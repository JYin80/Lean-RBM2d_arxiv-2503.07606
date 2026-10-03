/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Step1RegularityB
import RBM2D.Universality.Pins
import RBM2D.Universality.OU
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The GUE side of the regularity event of Step 1 under the weak statement `GUELocal`

Paper: arXiv:2503.07606, the proof of `Thm: B_Univ` (`(1infyuniv)` at `1infyuniv`, proved in the
paragraph after `univ-main` from `MR:locSC` and [32] Theorem 2.2); [32] Definition 2.1 and
Theorem 2.2 as stated in `Universality/Pins.lean` (`IsRegular32`, `IsFreeConv32`, `L32`).
`GUELocal` is not in the paper (`Pins.lean`); it is a hypothesis of `GUELocalEventHighProb` and
`GUEGoodHighProb`.  Namespace `RBM.Univ` (as `Universality/Pins.lean`).

Result.  `GUELocal` (precision `N^τ (N Im z)^{-1/2}`) suffices: `guelocalEventHighProb` (the
probabilistic half), `guedetHalf` (the deterministic half), `gueGoodHighProb`.  The single
exponent `τ` of `GUELocal` must lie in `(0, τs/8)`; no `τs ≤ 𝔠` is needed on the GUE side; every
rate `r > 0` of the density suffices for the translation (`GUETranslation.lean`).

Contents.
* vocabulary and statements: `vGUE`, `Step1LocalEventGUE`, `GUEGoodAt`; `GUELocalEventHighProb`
  (probabilistic half), `GUEDetHalf` (deterministic half), their composition `GUEGoodHighProb`.
* the exponent window `τ ∈ (0, τs/8)` of `GUELocal`, the counting scale, the `L32` exponents.
* the GUE entry tail and the union bound; `gue_err_pow`, where the weak precision enters the
  deterministic half.
* the deterministic half: that of `Step1RegularityB.lean` with `gue_err_pow`.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## Vocabulary and statements -/

/-- The shifted, rescaled GUE diagonal of the GUE side of Step 1:
`v_i = e^{-t*/2} λ_i(X) - E₀`, `X` under `gueP`, `t* = N^{-1+τs}` (`ouTStar`).  The GUE analogue
of `vOU` (`Step1RegularityB.lean`, carrier `seqP d`). -/
def vGUE (d : Sizes) (n : ℕ) (τs E₀ : ℝ) (ω : Ω (d.L n) (d.W n)) : Idx (d.L n) (d.W n) → ℝ :=
  fun i => Real.exp (-(ouTStar d τs n) / 2) *
    (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues i - E₀

/-- **The GUE-side local event** at the precision of the statement `GUELocal`: the averaged local
law
`|m_N(z) - m_sc(z)| ≤ N^τ (N Im z)^{-1/2}` for every `z` of the window
`|Re z| ≤ 2 - κ`, `N^{-1+τ} ≤ Im z ≤ 10`, and every entry of `X` has modulus at most `1`
(the Gaussian input of [32] (2.3), `CV = 2`, as in `Step1LocalEvent`).
The GUE counterpart of `Step1LocalEvent`, whose threshold is `2 W^{τ'} / Meta(z)`; there is no
grid and no interpolation, because `GUELocal` already has the union over `z` inside the
probability. -/
def Step1LocalEventGUE (d : Sizes) (n : ℕ) (κ τ : ℝ) (ω : Ω (d.L n) (d.W n)) : Prop :=
  (∀ z : ℂ, |z.re| ≤ 2 - κ → ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ z.im → z.im ≤ 10 →
      ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ / Real.sqrt (((d.size n : ℕ) : ℝ) * z.im)) ∧
  ∀ x y : Idx (d.L n) (d.W n), ‖Xmat (d.L n) (d.W n) ω x y‖ ≤ 1

/-- **The GUE-side good event** (the statement of `step1Good_highProb`, `Step1RegularityB.lean`,
with `vOU` replaced by `vGUE`): `vGUE` is `[32]`-regular with `g = N^{-1+τs/4}`,
`G = N^{-min(τs/4, (1-τs)/3)}`, `c = min κ 1 / 960`, `C = 2`, `CV = 2`, and the free-convolution
density at `t = 1 - e^{-t*}` exists and is within `N^{-3τs/8}` of `ρ_sc(E₀)`.  No `τs ≤ 𝔠`: the
GUE error `(N Im z)^{-1/2}` has no `W^{-2}` floor. -/
def GUEGoodAt (d : Sizes) (n : ℕ) (κ τs E₀ : ℝ) (ω : Ω (d.L n) (d.W n)) : Prop :=
  IsRegular32 (vGUE d n τs E₀ ω) (((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4))
      (((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 ∧
    ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST (vGUE d n τs E₀ ω)
        (1 - Real.exp (-(ouTStar d τs n))) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      |ρ - rhoSC E₀| ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))

/-- **Probabilistic half (proved as `guelocalEventHighProb`)**: from `GUELocal` (kept as
a hypothesis) and the Gaussian entry tail, the local event fails with probability `≤ N^{-D}`
eventually, for every exponent `τ > 0` of `GUELocal` (domain edge and precision exponent are the
same `τ`).  Proof:
`GUELocal` at `(κ, τ, D + 1)`, the union bound over the `2 N²` real coordinates of
`P(|coordinate| ≥ 1/2) ≤ 2 e^{-N/8}` (`gueVar ≤ 1/N`), `4 N² e^{-N/8} ≤ N^{-(D+1)}` for large `N`.
No grid is needed. -/
def GUELocalEventHighProb : Prop :=
  GUELocal → ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, gueP (d.L n) (d.W n) {ω | ¬ Step1LocalEventGUE d n κ τ ω} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **Deterministic half (proved as `guedetHalf`)**: for `0 < τ < τs/8`, `0 < τs < 1`,
eventually in `n`,
every `ω` in `Step1LocalEventGUE d n (κ/2) τ` has `GUEGoodAt`.  The window `τ < τs/8` is the
binding constraint (the error `N^{τ - τs/8}` at `Im z ≍ g = N^{-1+τs/4}`, and the strip error
`N^{τ - τs/2} ≤ N^{-3τs/8}`); the domain edge `N^{-1+τ} ≤ g` needs `τ ≤ τs/4`.  The template is
`Step1RegularityB_det`. -/
def GUEDetHalf : Prop :=
  ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
    ∀ κ τs E₀ : ℝ, 0 < κ → 0 < τs → τs < 1 → |E₀| ≤ 2 - κ →
      ∀ τ : ℝ, 0 < τ → τ < τs / 8 →
        ∀ᶠ n in atTop, ∀ ω : Ω (d.L n) (d.W n),
          Step1LocalEventGUE d n (κ / 2) τ ω → GUEGoodAt d n κ τs E₀ ω

/-- **The composition of the two halves**: the GUE-side good event has probability `≥ 1 - N^{-D}`
eventually, from `GUELocal`.  The GUE counterpart of `step1Good_highProb`. -/
def GUEGoodHighProb : Prop :=
  GUELocal → ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
    ∀ κ τs E₀ D : ℝ, 0 < κ → 0 < τs → τs < 1 → |E₀| ≤ 2 - κ → 0 < D →
      ∀ᶠ n in atTop, gueP (d.L n) (d.W n) {ω | ¬ GUEGoodAt d n κ τs E₀ ω} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- The composition of the two halves at `τ = τs/16`: `measure_mono` from
`{¬Good} ⊆ {¬Event}`. -/
theorem gueGoodHighProb_of (h1 : GUELocalEventHighProb) (h2 : GUEDetHalf) : GUEGoodHighProb := by
  intro hG d hd κ τs E₀ D hκ hτs0 hτs1 hE₀ hD
  have hev := h1 hG d hd (κ / 2) (τs / 16) D (by positivity) (by positivity) hD
  have hdet := h2 d hd κ τs E₀ hκ hτs0 hτs1 hE₀ (τs / 16) (by positivity) (by linarith)
  filter_upwards [hev, hdet] with n hn hdn
  refine le_trans (measure_mono ?_) hn
  intro ω hω hevω
  exact hω (hdn ω hevω)

/-! ## The exponent window of `GUELocal` (arithmetic)

`GUELocal` has one exponent `τ`: the domain edge `Im z ≥ N^{-1+τ}` and the precision
`N^τ (N Im z)^{-1/2}`.  The deterministic half S7b uses it at three scales (the regularity edge
`g = N^{-1+τs/4}`, the strip edge `Im w ≍ T = N^{-1+τs}`, and the rate `N^{-3τs/8}`); the count in
`GUETranslation.lean` uses its own `τ_G`. -/

/-! ## The probabilistic half: the GUE entry tail, the union bound and `GUELocal`

The only probabilistic input specific to the GUE side: every real coordinate of `gueP` is
sub-Gaussian with variance proxy `1/N` (`gueVar ≤ 1/N`), so some entry exceeds `1` with
probability `≤ 4 N² e^{-N/8}`; this is `Step1RegularityA_entry_bound`
with the band proxy `1/(5 W²)` replaced by `1/N`.  Since `N^{D+3} e^{-N/8} → 0` needs only
`N → ∞`, no `Admissible` is used. -/

private theorem Step1RegularityGUE_card_Idx (L W : ℕ) [NeZero L] [NeZero W] :
    Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp [Idx, Z2, Fintype.card_prod, ZMod.card, sq]

private theorem Step1RegularityGUE_card_Coord (L W : ℕ) [NeZero L] [NeZero W] :
    (Fintype.card (Coord L W) : ℝ) = 2 * ((((W * L) ^ 2 : ℕ)) : ℝ) ^ 2 := by
  have : Fintype.card (Coord L W) = 2 * ((W * L) ^ 2) ^ 2 := by
    change Fintype.card (Idx L W × Idx L W × Bool) = _
    rw [Fintype.card_prod (Idx L W) (Idx L W × Bool), Fintype.card_prod (Idx L W) Bool,
      Fintype.card_bool, Step1RegularityGUE_card_Idx]
    ring
  rw [this]; push_cast; ring

private theorem Step1RegularityGUE_gueVar_le (L W : ℕ) [NeZero L] [NeZero W] (c : Coord L W) :
    (gueVar L W c : ℝ) ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  unfold gueVar
  split_ifs
  · simp
  · have hpos : (0 : ℝ) ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by positivity
    push_cast at hpos ⊢
    rw [mul_inv]
    nlinarith [hpos]

/-- If every real coordinate is at most `1/2` in absolute value, every entry has modulus `≤ 1`. -/
private theorem Step1RegularityGUE_Xentry_le (L W : ℕ) [NeZero L] [NeZero W] (s : Ω L W)
    (hs : ∀ c, |s c| ≤ 1 / 2) (i j : Idx L W) : ‖Xentry L W s i j‖ ≤ 1 := by
  have hn : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  have hn' : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_sub_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  unfold Xentry
  split_ifs
  · exact hn _ _ (hs _) (hs _)
  · exact hn' _ _ (hs _) (hs _)
  · have := hs (i, j, true)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith

/-- Each real coordinate of the GUE is sub-Gaussian with variance proxy `1/N`
(`gueVar ≤ 1/N`, `N = (W L)²`). -/
private theorem Step1RegularityGUE_subgaussian (L W : ℕ) [NeZero L] [NeZero W] (c : Coord L W) :
    HasSubgaussianMGF (fun ω : Ω L W => ω c)
      (⟨((((W * L) ^ 2 : ℕ) : ℝ))⁻¹, by positivity⟩ : ℝ≥0) (gueP L W) := by
  set v : ℝ≥0 := ⟨((((W * L) ^ 2 : ℕ) : ℝ))⁻¹, by positivity⟩ with hv
  have hmap : (gueP L W).map (fun ω : Ω L W => ω c) = gaussianReal 0 (gueVar L W c) := by
    unfold gueP; exact Measure.infinitePi_map_eval _ c
  have hX : AEMeasurable (fun ω : Ω L W => ω c) (gueP L W) :=
    (measurable_pi_apply _).aemeasurable
  rw [← HasSubgaussianMGF.id_map_iff hX, hmap]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp only [zero_mul, zero_add]
  apply Real.exp_le_exp.2
  have h := Step1RegularityGUE_gueVar_le L W c
  have : (gueVar L W c : ℝ) ≤ (v : ℝ) := h
  nlinarith [sq_nonneg t]

/-- Chernoff bound for one coordinate: `P(|g| ≥ 1/2) ≤ 2 exp(-N/8)`. -/
private theorem Step1RegularityGUE_coord_tail (L W : ℕ) [NeZero L] [NeZero W] (c : Coord L W) :
    (gueP L W).real ({ω | 1 / 2 ≤ ω c} ∪ {ω | 1 / 2 ≤ -(ω c)}) ≤
      2 * Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8)) := by
  have hsg := Step1RegularityGUE_subgaussian L W c
  have h1 : (gueP L W).real {ω | 1 / 2 ≤ ω c} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹)) :=
    hsg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have h2 : (gueP L W).real {ω | 1 / 2 ≤ -(ω c)} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹)) :=
    hsg.neg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have hN : (0 : ℝ) < ((W * L) ^ 2 : ℕ) := by
    have h1 : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
    have h2 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hexp : Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹)) =
      Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8)) := by
    congr 1
    field_simp
    ring
  rw [hexp] at h1 h2
  calc (gueP L W).real ({ω | 1 / 2 ≤ ω c} ∪ {ω | 1 / 2 ≤ -(ω c)})
      ≤ (gueP L W).real {ω | 1 / 2 ≤ ω c} + (gueP L W).real {ω | 1 / 2 ≤ -(ω c)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8)) := by linarith

/-- The union bound over the `2 N²` real coordinates: some entry exceeds `1` with probability at
most `4 N² exp(-N/8)`. -/
private theorem Step1RegularityGUE_entry_bound (L W : ℕ) [NeZero L] [NeZero W] :
    gueP L W {ω | ¬ ∀ x y : Idx L W, ‖Xmat L W ω x y‖ ≤ 1} ≤
      ENNReal.ofReal (4 * ((((W * L) ^ 2 : ℕ)) : ℝ) ^ 2 *
        Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8))) := by
  classical
  have hsub : {ω : Ω L W | ¬ ∀ x y : Idx L W, ‖Xmat L W ω x y‖ ≤ 1} ⊆
      ⋃ c : Coord L W, ({ω : Ω L W | 1 / 2 ≤ ω c} ∪ {ω : Ω L W | 1 / 2 ≤ -(ω c)}) := by
    intro ω hω
    by_contra hcon
    apply hω
    intro x y
    have hs : ∀ c, |ω c| ≤ 1 / 2 := by
      intro c
      by_contra hc
      push Not at hc
      apply hcon
      refine Set.mem_iUnion.2 ⟨c, ?_⟩
      rcases lt_abs.1 hc with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    exact Step1RegularityGUE_Xentry_le L W ω hs x y
  have hterm : ∀ c : Coord L W,
      gueP L W ({ω : Ω L W | 1 / 2 ≤ ω c} ∪ {ω : Ω L W | 1 / 2 ≤ -(ω c)}) ≤
        ENNReal.ofReal (2 * Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8))) := by
    intro c
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
    exact Step1RegularityGUE_coord_tail L W c
  calc gueP L W {ω | ¬ ∀ x y : Idx L W, ‖Xmat L W ω x y‖ ≤ 1}
      ≤ gueP L W (⋃ c : Coord L W,
        ({ω : Ω L W | 1 / 2 ≤ ω c} ∪ {ω : Ω L W | 1 / 2 ≤ -(ω c)})) := measure_mono hsub
    _ ≤ ∑ c : Coord L W,
        gueP L W ({ω : Ω L W | 1 / 2 ≤ ω c} ∪ {ω : Ω L W | 1 / 2 ≤ -(ω c)}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : Coord L W, ENNReal.ofReal (2 * Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ENNReal.ofReal (4 * ((((W * L) ^ 2 : ℕ)) : ℝ) ^ 2 *
        Real.exp (-((((W * L) ^ 2 : ℕ) : ℝ) / 8))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Step1RegularityGUE_card_Coord]
        congr 1
        ring


/-- `4 N² e^{-N/8} ≤ N^{-(D+1)}` eventually, from `N → ∞` only (`x^s e^{-b x} → 0`). -/
private theorem Step1RegularityGUE_entry_eventually (D : ℝ) (d : Sizes)
    (hd : Tendsto (fun n => d.size n) atTop atTop) :
    ∀ᶠ n in atTop, 4 * ((d.size n : ℕ) : ℝ) ^ 2 * Real.exp (-(((d.size n : ℕ) : ℝ) / 8)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D + 3) (1 / 8) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (D + 3) * Real.exp (-(1 / 8) * x) ≤ 1 / 4 :=
    hdecay.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hNtend.eventually hsmall, hNtend.eventually_ge_atTop 1] with n hn hN1
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  have h3 : N ^ 2 * N ^ (D + 1) = N ^ (D + 3) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hpos : 0 < N ^ (D + 1) := Real.rpow_pos_of_pos hNpos _
  have hexp : Real.exp (-(N / 8)) = Real.exp (-(1 / 8) * N) := by
    congr 1; ring
  have h4 : 4 * N ^ 2 * Real.exp (-(N / 8)) * N ^ (D + 1) ≤ 1 := by
    calc 4 * N ^ 2 * Real.exp (-(N / 8)) * N ^ (D + 1)
        = 4 * (N ^ 2 * N ^ (D + 1)) * Real.exp (-(N / 8)) := by ring
      _ = 4 * (N ^ (D + 3) * Real.exp (-(1 / 8) * N)) := by rw [h3, hexp]; ring
      _ ≤ 4 * (1 / 4) := by gcongr
      _ = 1 := by norm_num
  rw [Real.rpow_neg hNpos.le, ← one_div]
  exact (le_div_iff₀ hpos).2 h4

/-- **The probabilistic half `GUELocalEventHighProb`, proved**: `GUELocal` at `(κ, τ, D + 1)`, the
entry bound at `D + 1`, and `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem guelocalEventHighProb : GUELocalEventHighProb := by
  intro hG d hd κ τ D hκ hτ hD
  have h1 := hG d hd κ τ (D + 1) hκ hτ (by linarith)
  have h2 := Step1RegularityGUE_entry_eventually D d hd
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  filter_upwards [h1, h2, hNtend.eventually_ge_atTop 2] with n hn1 hn2 hN2
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  have hentry := Step1RegularityGUE_entry_bound (d.L n) (d.W n)
  have hsub : {ω : Ω (d.L n) (d.W n) | ¬ Step1LocalEventGUE d n κ τ ω} ⊆
      {ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ N ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
          N ^ τ / Real.sqrt (N * z.im) <
            ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖} ∪
        {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖Xmat (d.L n) (d.W n) ω x y‖ ≤ 1} := by
    intro ω hω
    by_cases hent : ∀ x y : Idx (d.L n) (d.W n), ‖Xmat (d.L n) (d.W n) ω x y‖ ≤ 1
    · left
      by_contra hcon
      apply hω
      refine ⟨fun z hz1 hz2 hz3 => ?_, hent⟩
      by_contra hlt
      push Not at hlt
      exact hcon ⟨z, hz1, hz2, hz3, hlt⟩
    · exact Or.inr hent
  have hN2' : 2 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
    have : N ^ (-D) = N * N ^ (-(D + 1)) := by
      rw [← Real.rpow_one_add' hNpos.le (by linarith [hD])]
      congr 1; ring
    rw [this]
    have := Real.rpow_nonneg hNpos.le (-(D + 1))
    nlinarith
  have hentry' : gueP (d.L n) (d.W n)
      {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖Xmat (d.L n) (d.W n) ω x y‖ ≤ 1} ≤
        ENNReal.ofReal (N ^ (-(D + 1))) := by
    refine hentry.trans ?_
    exact ENNReal.ofReal_le_ofReal hn2
  calc gueP (d.L n) (d.W n) {ω | ¬ Step1LocalEventGUE d n κ τ ω}
      ≤ gueP (d.L n) (d.W n) ({ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ N ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
          N ^ τ / Real.sqrt (N * z.im) <
            ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖} ∪
        {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖Xmat (d.L n) (d.W n) ω x y‖ ≤ 1}) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) :=
        add_le_add hn1 hentry'
    _ = ENNReal.ofReal (2 * N ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hN2'

/-- **The place where the weak precision enters** (analogue of `Step1RegularityB_err_pow`,
`Step1RegularityB.lean`, whose bound `2 c⁻¹ N^{τ'/2 - σ}` needs `N^σ ≤ W²`, i.e. `τs ≤ 𝔠`):
on `Step1LocalEventGUE d n κ τ`, at every `z` of the window with `Im z ≥ c N^{-1+σ}`,
`‖m_N(z) - m_sc(z)‖ ≤ c^{-1/2} N^{τ - σ/2}`.  At `σ = τs/4` (the edge `g`) this is
`N^{τ - τs/8}`; at `σ = τs` (the strip edge) it is `N^{τ - τs/2}`. -/
theorem gue_err_pow (d : Sizes) (n : ℕ) {κ τ : ℝ} {ω : Ω (d.L n) (d.W n)}
    (hev : Step1LocalEventGUE d n κ τ ω) (hN : 1 ≤ d.size n) {z : ℂ}
    (hz1 : |z.re| ≤ 2 - κ) (hz2 : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ z.im) (hz3 : z.im ≤ 10)
    {c σ : ℝ} (hc : 0 < c) (hzc : c * ((d.size n : ℕ) : ℝ) ^ (-1 + σ) ≤ z.im) :
    ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖ ≤
      Real.sqrt c⁻¹ * ((d.size n : ℕ) : ℝ) ^ (τ - σ / 2) := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNr1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hNr0 : 0 < N := by linarith
  have h := hev.1 z hz1 hz2 hz3
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hz2
  have hNz : c * N ^ σ ≤ N * z.im := by
    calc c * N ^ σ = N * (c * N ^ (-1 + σ)) := by
          rw [Real.rpow_add hNr0, Real.rpow_neg_one]; field_simp
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left hzc hNr0.le
  have hsq : Real.sqrt c * N ^ (σ / 2) ≤ Real.sqrt (N * z.im) := by
    have : Real.sqrt (c * N ^ σ) = Real.sqrt c * N ^ (σ / 2) := by
      rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow (N ^ σ), ← Real.rpow_mul hNr0.le]
      congr 2; ring
    rw [← this]; exact Real.sqrt_le_sqrt hNz
  have hc0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hp : 0 < N ^ (σ / 2) := Real.rpow_pos_of_pos hNr0 _
  calc ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖ ≤ N ^ τ / Real.sqrt (N * z.im) := h
    _ ≤ N ^ τ / (Real.sqrt c * N ^ (σ / 2)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hNr0.le _) (by positivity) hsq
    _ = Real.sqrt c⁻¹ * N ^ (τ - σ / 2) := by
        rw [Real.sqrt_inv, Real.rpow_sub hNr0]; field_simp

/-! ## The deterministic half under the weak precision

The deterministic half of `Step1RegularityB.lean` with the single change that the event error
`2 W^{τ'}/Meta(z)` (which needs `N^σ ≤ W²`, i.e. `τs ≤ 𝔠`) is replaced by
`N^τ (N Im z)^{-1/2}` (`gue_err_pow`).  The generic private lemmas of `Step1RegularityB.lean` are
copied with the prefix `Step1RegularityGUE_` (elementary facts on `a = e^{-T/2}`, the eigenvalue
dictionary, the bulk lower bound of `Im m_sc`, the rescaled domain, `|λ_i| ≤ N` from the entry
bound); `bulk`, `regular`, `strip`, `det` are adapted. -/

private theorem Step1RegularityGUE_exp_le_one {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem Step1RegularityGUE_one_le_inv {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact Step1RegularityGUE_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityGUE_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem Step1RegularityGUE_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityGUE_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

private theorem Step1RegularityGUE_one_sub_exp_pos {T : ℝ} (hT : 0 < T) :
    0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem Step1RegularityGUE_sqrt_exp (T : ℝ) :
    Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem Step1RegularityGUE_inv_mul_re (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem Step1RegularityGUE_inv_mul_im (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

/-- `stieltjesN` is the finite-sum Stieltjes transform `mV` of the eigenvalues. -/
private theorem Step1RegularityGUE_stieltjesN_eq_mV {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjesN H z = mV hH.eigenvalues z := by
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold stieltjesN mV
  congr 1
  rw [green_eq_spectral hH hzne]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

/-- The affine dictionary:
`m_V(w) = a⁻¹ m_N(a⁻¹ (w + E₀))` for `v_i = a λ_i - E₀`, `a > 0`. -/
private theorem Step1RegularityGUE_mV_vOU {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {a : ℝ} (ha : 0 < a) (E₀ : ℝ) {w : ℂ}
    (hw : 0 < w.im) :
    mV (fun i => a * hH.eigenvalues i - E₀) w =
      ((a : ℝ) : ℂ)⁻¹ * stieltjesN H (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) := by
  have hz : 0 < (((a : ℝ) : ℂ)⁻¹ * (w + E₀)).im := by
    rw [Step1RegularityGUE_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
    positivity
  rw [Step1RegularityGUE_stieltjesN_eq_mV hH hz]
  unfold mV
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set lami : ℝ := hH.eigenvalues i with hlam_def
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hkey : ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w =
      (a : ℂ) * ((lami : ℂ) - (((a : ℝ) : ℂ)⁻¹ * (w + E₀))) := by
    rw [mul_sub]
    rw [show (a : ℂ) * (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) = w + E₀ by field_simp]
    ring
  rw [show ((a * lami - E₀ : ℝ) : ℂ) - w = ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w by push_cast; ring,
    hkey, mul_inv]

private theorem Step1RegularityGUE_im_le_norm_sub {a : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ ‖(a : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  rwa [abs_of_pos hz] at h

/-- Crude bound `‖m_V(z)‖ ≤ 1 / Im z`, valid for every `v`. -/
private theorem Step1RegularityGUE_mV_norm_le {ι : Type*} [Fintype ι] (v : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) : ‖mV v z‖ ≤ z.im⁻¹ := by
  have hterm : ∀ i : ι, ‖((v i : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := fun i => by
    rw [norm_inv]
    exact inv_anti₀ hz (Step1RegularityGUE_im_le_norm_sub hz)
  unfold mV
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
  · rw [hc0, Nat.cast_zero, _root_.inv_zero, zero_mul]
    exact inv_nonneg.2 hz.le
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcpos
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, ((v i : ℂ) - z)⁻¹‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖((v i : ℂ) - z)⁻¹‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, z.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
    _ = z.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

private theorem Step1RegularityGUE_norm_msc_pos {z : ℂ} (hz : 0 < z.im) : 0 < ‖msc z‖ :=
  norm_pos_iff.mpr fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

/-- `m_sc(z) + z = -m_sc(z)⁻¹` (private in `Defs/Semicircle.lean`). -/
private theorem Step1RegularityGUE_msc_add_eq_neg_inv {z : ℂ} (hz : 0 < z.im) :
    msc z + z = -(msc z)⁻¹ := by
  have hm0 : msc z ≠ 0 := norm_pos_iff.mp (Step1RegularityGUE_norm_msc_pos hz)
  field_simp
  linear_combination msc_mul z

/-- `|m_sc(z)|² ≥ (1 + |z|)⁻²` (private in `Defs/Semicircle.lean`). -/
private theorem Step1RegularityGUE_lemT_ge {z : ℂ} (hz : 0 < z.im) :
    ((1 + ‖z‖) ^ 2)⁻¹ ≤ lemT z := by
  have hr : 0 < ‖msc z‖ := Step1RegularityGUE_norm_msc_pos hz
  have hinv : ‖msc z‖⁻¹ ≤ ‖msc z‖ + ‖z‖ := by
    rw [← norm_inv, ← norm_neg, ← Step1RegularityGUE_msc_add_eq_neg_inv hz]
    exact norm_add_le _ _
  have h1 : 1 ≤ ‖msc z‖ * (1 + ‖z‖) := by
    have h := norm_msc_lt_one hz
    have := (inv_le_iff_one_le_mul₀' hr).1 (hinv.trans (by linarith : ‖msc z‖ + ‖z‖ ≤ 1 + ‖z‖))
    linarith
  rw [lemT, inv_le_iff_one_le_mul₀ (by positivity)]
  nlinarith [norm_nonneg z]

/-- **Bulk lower bound**:
`Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`, `0 < κ' ≤ 1`. -/
private theorem Step1RegularityGUE_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := Step1RegularityGUE_lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (Step1RegularityGUE_msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

/-- If `|E₀| ≤ 2 - κ`, `|Re w| ≤ R ≤ κ'/4`, `y ≤ Im w ≤ 1/2`, `N^{-1+τ} ≤ y` and
`0 ≤ T ≤ κ'/240` (`κ' = min κ 1`), then `z = a⁻¹ (w + E₀)`, `a = e^{-T/2}`, lies in
`locDomain N (κ/2) τ`, and `Im z ≥ Im w`. -/
private theorem Step1RegularityGUE_domain {N : ℕ} {κ τ E₀ T R y : ℝ} (hκ : 0 < κ)
    (hE₀ : |E₀| ≤ 2 - κ) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240) (hR : R ≤ min κ 1 / 4)
    (hy0 : 0 < y) (hy : (N : ℝ) ^ (-1 + τ) ≤ y) {w : ℂ} (hw : |w.re| ≤ R) (hwy : y ≤ w.im)
    (hw1 : w.im ≤ 1 / 2) :
    locDomain N (κ / 2) τ (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) ∧
      w.im ≤ ((((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))).im := by
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hκ' : min κ 1 ≤ κ := min_le_left _ _
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hT1 : T ≤ 1 := by linarith
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := Step1RegularityGUE_one_le_inv hT0
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := Step1RegularityGUE_inv_le hT0 hT1
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E₀]
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hw
  have hwim0 : 0 < w.im := lt_of_lt_of_le hy0 hwy
  have hre : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).re =
      (Real.exp (-T / 2))⁻¹ * (w.re + E₀) := by
    rw [Step1RegularityGUE_inv_mul_re, Complex.add_re, Complex.ofReal_re]
  have him : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).im =
      (Real.exp (-T / 2))⁻¹ * w.im := by
    rw [Step1RegularityGUE_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
  have hge : w.im ≤ (Real.exp (-T / 2))⁻¹ * w.im := by
    calc w.im = 1 * w.im := (one_mul _).symm
      _ ≤ (Real.exp (-T / 2))⁻¹ * w.im := mul_le_mul_of_nonneg_right hainv1 hwim0.le
  refine ⟨⟨?_, ?_, ?_⟩, by rw [him]; exact hge⟩
  · rw [hre, abs_mul, abs_of_pos (inv_pos.2 ha0)]
    have h1 : |w.re + E₀| ≤ R + (2 - κ) := (abs_add_le _ _).trans (add_le_add hw hE₀)
    have h2 : 0 ≤ R + (2 - κ) := by linarith
    have h3 : T * (R + (2 - κ)) ≤ min κ 1 / 240 * (R + (2 - κ)) :=
      mul_le_mul_of_nonneg_right hT h2
    calc (Real.exp (-T / 2))⁻¹ * |w.re + E₀| ≤ (1 + T) * (R + (2 - κ)) :=
          mul_le_mul hainv h1 (abs_nonneg _) (by linarith)
      _ ≤ 2 - κ / 2 := by nlinarith
  · rw [him]; exact hy.trans (hwy.trans hge)
  · rw [him]
    calc (Real.exp (-T / 2))⁻¹ * w.im ≤ (1 + T) * (1 / 2) :=
          mul_le_mul hainv hw1 hwim0.le (by linarith)
      _ ≤ 1 := by linarith

/-- The point of the event attached to `w = E + iη`. -/
private theorem Step1RegularityGUE_arg_eq (a E₀ E η : ℝ) :
    ((a : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) =
      ((a⁻¹ * (E + E₀) : ℝ) : ℂ) + ((a⁻¹ * η : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [Step1RegularityGUE_inv_mul_re]; simp
  · rw [Step1RegularityGUE_inv_mul_im]; simp

/-- `|λ_i| ≤ N` when every entry has modulus at most `1`: from `H ψ = λ ψ`,
`|λ| |ψ_x| ≤ Σ_y |ψ_y|`, summed over `x`. -/
private theorem Step1RegularityGUE_eigenvalue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hent : ∀ x y, ‖H x y‖ ≤ 1) (i : ι) :
    |hH.eigenvalues i| ≤ (Fintype.card ι : ℝ) := by
  set ψ : EuclideanSpace ℂ ι := hH.eigenvectorBasis i with hψ
  have hψn : ‖ψ‖ = 1 := hH.eigenvectorBasis.norm_eq_one i
  have hmv := hH.mulVec_eigenvectorBasis i
  have hsq : ∑ y, ‖ψ.ofLp y‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψn]; norm_num
  have hle1 : ∀ y, ‖ψ.ofLp y‖ ≤ 1 := by
    intro y
    have : ‖ψ.ofLp y‖ ^ 2 ≤ 1 := by
      rw [← hsq]
      exact Finset.single_le_sum (f := fun y => ‖ψ.ofLp y‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ y)
    nlinarith [norm_nonneg (ψ.ofLp y)]
  set S : ℝ := ∑ y, ‖ψ.ofLp y‖ with hS
  have hS1 : 1 ≤ S := by
    calc (1 : ℝ) = ∑ y, ‖ψ.ofLp y‖ ^ 2 := hsq.symm
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          nlinarith [norm_nonneg (ψ.ofLp y), hle1 y]
  have hrow : ∀ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ ≤ S := by
    intro x
    have h1 : (H.mulVec ψ.ofLp) x = (hH.eigenvalues i • ψ.ofLp) x := by rw [hmv]
    have h2 : ‖(hH.eigenvalues i • ψ.ofLp) x‖ = |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [← h2, ← h1]
    calc ‖(H.mulVec ψ.ofLp) x‖ = ‖∑ y, H x y * ψ.ofLp y‖ := rfl
      _ ≤ ∑ y, ‖H x y * ψ.ofLp y‖ := norm_sum_le _ _
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hent x y)
  have hsum : |hH.eigenvalues i| * S ≤ (Fintype.card ι : ℝ) * S := by
    calc |hH.eigenvalues i| * S = ∑ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
          rw [hS, Finset.mul_sum]
      _ ≤ ∑ _x : ι, S := Finset.sum_le_sum fun x _ => hrow x
      _ = (Fintype.card ι : ℝ) * S := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_mul_le_mul_right hsum (by linarith)

/-- The index set has `N = (W L)²` elements. -/
private theorem Step1RegularityGUE_card (d : Sizes) (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Sizes.size, Idx, Z2, Fintype.card_prod, ZMod.card, sq, mul_comm]

private theorem Step1RegularityGUE_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h


/-- Regime 1 of (2.2): for `|E| ≤ R`, `N^{-1+σ} ≤ η ≤ 1/2`, on the event, the imaginary part of
`m_N` at the rescaled point is in `[κ'/24, 1 + κ'/24]`, provided the event error
`N^{τ - σ/2} ≤ κ'/24`. -/
private theorem Step1RegularityGUE_bulk (d : Sizes) (n : ℕ) {κ τ E₀ T R σ : ℝ}
    {ω : Ω (d.L n) (d.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hev : Step1LocalEventGUE d n (κ / 2) τ ω)
    (hN : 1 ≤ d.size n) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240)
    (hR : R ≤ min κ 1 / 4) (hτσ : τ ≤ σ)
    (herr : ((d.size n : ℕ) : ℝ) ^ (τ - σ / 2) ≤ min κ 1 / 24)
    {E η : ℝ} (hE : |E| ≤ R) (hη : ((d.size n : ℕ) : ℝ) ^ (-1 + σ) ≤ η) (hη1 : η ≤ 1 / 2) :
    min κ 1 / 24 ≤ (stieltjesN (Xmat (d.L n) (d.W n) ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
      (stieltjesN (Xmat (d.L n) (d.W n) ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤ 1 + min κ 1 / 24 := by
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'κ : min κ 1 ≤ κ := min_le_left _ _
  have hy0 : 0 < ((d.size n : ℕ) : ℝ) ^ (-1 + σ) := Real.rpow_pos_of_pos hNr0 _
  have hyτ : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + σ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  obtain ⟨hdom, hdomim⟩ := Step1RegularityGUE_domain (N := d.size n) (τ := τ) (w := ⟨E, η⟩)
    hκ hE₀ hT0 hT hR hy0 hyτ hE hη hη1
  have herrz := gue_err_pow d n hev hN hdom.1 hdom.2.1 (hdom.2.2.trans (by norm_num))
    (c := 1) (σ := σ) one_pos (by rw [one_mul]; exact hη.trans hdomim)
  set z : ℂ := ((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀) with hz
  have hzim : 0 < z.im := lt_of_lt_of_le (lt_of_lt_of_le hy0 hη) hdomim
  have hnorm : ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖ ≤ min κ 1 / 24 := by
    refine herrz.trans ?_
    rw [inv_one, Real.sqrt_one, one_mul]; exact herr
  have hIm : |(stieltjesN (Xmat (d.L n) (d.W n) ω) z).im - (msc z).im| ≤ min κ 1 / 24 := by
    calc |(stieltjesN (Xmat (d.L n) (d.W n) ω) z).im - (msc z).im|
        = |(stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z).im| := by rw [Complex.sub_im]
      _ ≤ ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖ := Complex.abs_im_le_norm _
      _ ≤ min κ 1 / 24 := hnorm
  have hzre : |z.re| ≤ 2 - min κ 1 / 2 := by
    have := hdom.1; linarith
  have hmsc := Step1RegularityGUE_msc_im_ge hκ'0 hκ'1 hzre hzim (by linarith [hdom.2.2])
  have hmscn := norm_msc_lt_one (z := z) hzim
  have hmscim : (msc z).im < 1 :=
    lt_of_le_of_lt ((le_abs_self _).trans (Complex.abs_im_le_norm _)) hmscn
  obtain ⟨h1, h2⟩ := abs_le.mp hIm
  constructor <;> linarith


/-- **The regularity part**, deterministic on the event
(no grid): `[32]`-regularity of `vGUE` with `g = N^{-1+τs/4}`, `G = N^{-σ}`,
`c = min κ 1 / 960`, `C = 2`, `CV = 2`.  `hg`, `hG`, `hT`, `herr` are the size conditions
that hold for large `n`. -/
private theorem Step1RegularityGUE_regular (d : Sizes) (n : ℕ) {κ τ τs E₀ : ℝ}
    {ω : Ω (d.L n) (d.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hτ4 : τ ≤ τs / 4)
    (hev : Step1LocalEventGUE d n (κ / 2) τ ω) (hN : 2 ≤ d.size n)
    (hg : ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) ≤ 1 / 2)
    (hG : ((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3))) ≤ min κ 1 / 4)
    (hT : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240)
    (herr : ((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) ≤ min κ 1 / 24) :
    IsRegular32 (vGUE d n τs E₀ ω) (((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4))
      (((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 := by
  have hN1 : 1 ≤ d.size n := by omega
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hNr2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hT0 : 0 ≤ ouTStar d τs n := Real.rpow_nonneg hNr0.le _
  have hT' : ouTStar d τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar d τs n ≤ 1 := by linarith
  have ha0 : 0 < Real.exp (-(ouTStar d τs n) / 2) := Real.exp_pos _
  have hainv1 : 1 ≤ (Real.exp (-(ouTStar d τs n) / 2))⁻¹ := Step1RegularityGUE_one_le_inv hT0
  have hainv : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 1 + ouTStar d τs n :=
    Step1RegularityGUE_inv_le hT0 hT1
  have hH := Xmat_isHermitian (d.L n) (d.W n) ω
  have hgpos : 0 < ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hNr0 _
  have hbulk : ∀ E η : ℝ, |E| ≤ ((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3))) →
      ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      min κ 1 / 24 ≤ (stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
        (stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤
          1 + min κ 1 / 24 := fun E η hE hη hη1 =>
    Step1RegularityGUE_bulk d n hκ hE₀ hev hN1 hT0 hT hG (σ := τs / 4) hτ4
      (by rw [show τ - τs / 4 / 2 = τ - τs / 8 by ring]; exact herr) hE hη hη1
  refine ⟨?_, ?_⟩
  · intro E η hE hgη hη10
    have hηpos : 0 < η := lt_of_lt_of_le hgpos hgη
    have hdict : mV (vGUE d n τs E₀ ω) ⟨E, η⟩ =
        ((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) :=
      Step1RegularityGUE_mV_vOU hH ha0 E₀ (w := ⟨E, η⟩) hηpos
    have hdictIm : (mV (vGUE d n τs E₀ ω) ⟨E, η⟩).im =
        (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
      rw [hdict, Step1RegularityGUE_inv_mul_im]
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨hb1, hb2⟩ := hbulk E η hE hgη hη12
      rw [hdictIm]
      have hS0 : 0 ≤ (stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        linarith
      refine ⟨?_, ?_⟩
      · calc min κ 1 / 960 ≤ min κ 1 / 24 := by linarith
          _ ≤ _ := hb1
          _ = 1 * _ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS0
      · calc _ ≤ (1 + ouTStar d τs n) * (1 + min κ 1 / 24) :=
              mul_le_mul hainv hb2 hS0 (by linarith)
          _ ≤ 2 := by nlinarith
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      have hainv0 : 0 < (Real.exp (-(ouTStar d τs n) / 2))⁻¹ := inv_pos.2 ha0
      have hlb := (hbulk E (1 / 2) hE (by linarith) le_rfl).1
      have hmono : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2) *
            (stieltjesN (Xmat (d.L n) (d.W n) ω)
              (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ *
                ((⟨E, 1 / 2⟩ : ℂ) + E₀))).im ≤
          (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * η *
            (stieltjesN (Xmat (d.L n) (d.W n) ω)
              (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        rw [Step1RegularityGUE_arg_eq, Step1RegularityGUE_arg_eq]
        exact stieltjesN_eta_mul_im_mono (Xmat (d.L n) (d.W n) ω) hH _ _ _ (by positivity)
          (mul_le_mul_of_nonneg_left hη12'.le hainv0.le)
      set S₂ := (stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im with hS₂
      have h3 : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2) * (min κ 1 / 24) ≤
          (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (η * S₂) := by
        rw [← mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hlb (by positivity)) hmono
      have h4 : 1 / 2 * (min κ 1 / 24) ≤ η * S₂ := by
        have : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2 * (min κ 1 / 24)) ≤
            (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (η * S₂) := by
          rw [← mul_assoc]; exact h3
        exact le_of_mul_le_mul_left this hainv0
      have hS₂pos : 0 < S₂ := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hηpos.le (neg_nonneg.2 hneg)]
      have h5 : min κ 1 / 480 ≤ S₂ := by
        nlinarith [mul_le_mul_of_nonneg_right hη10 hS₂pos.le]
      refine ⟨?_, ?_⟩
      · rw [hdictIm]
        calc min κ 1 / 960 ≤ min κ 1 / 480 := by linarith
          _ ≤ S₂ := h5
          _ = 1 * S₂ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS₂pos.le
      · have hnb := Step1RegularityGUE_mV_norm_le (vGUE d n τs E₀ ω) (z := ⟨E, η⟩) hηpos
        calc (mV (vGUE d n τs E₀ ω) ⟨E, η⟩).im ≤ ‖mV (vGUE d n τs E₀ ω) ⟨E, η⟩‖ :=
              (le_abs_self _).trans (Complex.abs_im_le_norm _)
          _ ≤ (⟨E, η⟩ : ℂ).im⁻¹ := hnb
          _ ≤ 2 := by
              change η⁻¹ ≤ 2
              rw [inv_le_comm₀ hηpos (by norm_num)]
              linarith
  · intro i
    have hc : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
      rw [Step1RegularityGUE_card]
    have hlam := Step1RegularityGUE_eigenvalue_le hH hev.2 i
    rw [hc] at hlam
    rw [hc, Real.rpow_two]
    set a := Real.exp (-(ouTStar d τs n) / 2) with ha
    have ha1 : a ≤ 1 := Step1RegularityGUE_exp_le_one hT0
    have hE₀2 : |E₀| ≤ 2 := by linarith [abs_nonneg E₀]
    have h1 : |vGUE d n τs E₀ ω i| ≤ a * |hH.eigenvalues i| + |E₀| := by
      change |a * hH.eigenvalues i - E₀| ≤ _
      calc |a * hH.eigenvalues i - E₀| ≤ |a * hH.eigenvalues i| + |E₀| := abs_sub _ _
        _ = a * |hH.eigenvalues i| + |E₀| := by rw [abs_mul, abs_of_pos ha0]
    have h2 : a * |hH.eigenvalues i| ≤ ((d.size n : ℕ) : ℝ) :=
      (mul_le_of_le_one_left (abs_nonneg _) ha1).trans hlam
    nlinarith


/-- **The closeness hypothesis `hyp` of `FreeConvStability.freeConv_stable_local`**, on the event,
at every `w` of the
strip `|Re w| ≤ κ'/16`, `c₀ t/4 ≤ Im w ≤ 1/2`, `t = 1 - e^{-T}`: the lower edge of the strip is
above the domain edge `N^{-1+τ}` (`hedge`), so the strip stays inside the domain of the event. -/
private theorem Step1RegularityGUE_strip (d : Sizes) (n : ℕ) {κ τ τs E₀ c₀ C₀ : ℝ}
    {ω : Ω (d.L n) (d.W n)}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hev : Step1LocalEventGUE d n (κ / 2) τ ω) (hN : 1 ≤ d.size n)
    (hT : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240)
    (hedge : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤
      c₀ / 8 * ((d.size n : ℕ) : ℝ) ^ (-1 + τs))
    (hrate : ((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) ≤ Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀))
    {w : ℂ} (hw : |w.re| ≤ min κ 1 / 16)
    (hlow : c₀ * (1 - Real.exp (-(ouTStar d τs n))) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (vGUE d n τs E₀ ω) w - (Real.sqrt (Real.exp (-(ouTStar d τs n))) : ℂ)⁻¹ *
        msc ((Real.sqrt (Real.exp (-(ouTStar d τs n))) : ℂ)⁻¹ * (w + E₀))‖ ≤
      ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hTpos : 0 < ouTStar d τs n := Real.rpow_pos_of_pos hNr0 _
  have hT' : ouTStar d τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar d τs n ≤ 1 := by
    have : min κ 1 ≤ 1 := min_le_right _ _
    linarith
  have hH := Xmat_isHermitian (d.L n) (d.W n) ω
  rw [Step1RegularityGUE_sqrt_exp]
  have ha0 : 0 < Real.exp (-(ouTStar d τs n) / 2) := Real.exp_pos _
  have hainv : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 1 + ouTStar d τs n :=
    Step1RegularityGUE_inv_le hTpos.le hT1
  have hhalf := Step1RegularityGUE_half_le_one_sub_exp hTpos.le hT1
  have hy : c₀ / 8 * ouTStar d τs n ≤ w.im := by
    have : c₀ / 8 * ouTStar d τs n ≤ c₀ * (1 - Real.exp (-(ouTStar d τs n))) / 4 := by
      nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * ouTStar d τs n := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  obtain ⟨hdom, hdomim⟩ := Step1RegularityGUE_domain (N := d.size n) (τ := τ)
    (R := min κ 1 / 16) hκ hE₀ hTpos.le hT' (by linarith) hy0 hedge hw hy hw1
  set c₁ : ℝ := min 1 (c₀ / 8) with hc₁
  have hc₁0 : 0 < c₁ := lt_min one_pos (by positivity)
  have hc₁1 : c₁ ≤ 1 := min_le_left _ _
  have hc₁c : c₁ ≤ c₀ / 8 := min_le_right _ _
  have herrz := gue_err_pow d n hev hN hdom.1 hdom.2.1 (hdom.2.2.trans (by norm_num)) hc₁0
    (σ := τs)
    (by
      calc c₁ * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ c₀ / 8 * ouTStar d τs n :=
            mul_le_mul_of_nonneg_right hc₁c hTpos.le
        _ ≤ w.im := hy
        _ ≤ _ := hdomim)
  have hdict : mV (vGUE d n τs E₀ ω) w =
      ((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (Xmat (d.L n) (d.W n) ω)
        (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) :=
    Step1RegularityGUE_mV_vOU hH ha0 E₀ hw0
  rw [hdict, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg ha0.le]
  have ha2 : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 2 := by linarith [hT', min_le_right κ 1]
  have hsplit : ((d.size n : ℕ) : ℝ) ^ (τ - τs / 2) =
      ((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) * ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hNr0]; congr 1; ring
  have hY0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := Real.rpow_nonneg hNr0.le _
  have hsc : 0 < Real.sqrt c₁ := Real.sqrt_pos.2 hc₁0
  calc (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * ‖stieltjesN (Xmat (d.L n) (d.W n) ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) -
        msc (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))‖
      ≤ 2 * (Real.sqrt c₁⁻¹ * ((d.size n : ℕ) : ℝ) ^ (τ - τs / 2)) :=
        mul_le_mul ha2 herrz (norm_nonneg _) (by norm_num)
    _ = 2 * Real.sqrt c₁⁻¹ * (((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) *
          ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))) := by rw [hsplit]; ring
    _ ≤ 2 * Real.sqrt c₁⁻¹ * ((Real.sqrt c₁ / (2 * C₀)) *
          ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))) := by
        gcongr
    _ = ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by
        rw [Real.sqrt_inv]; field_simp


/-- **Deterministic part of the good event**: for `0 < τ < τs/8`, eventually in `n`, every
`ω` of the event `Step1LocalEventGUE d n (κ/2) τ` has `vGUE` `[32]`-regular and the
free-convolution density within `N^{-3τs/8}` of `ρ_sc(E₀)`.  All the size conditions are of the
form `N^{-e} ≤ c` with `e > 0` (so they hold for large `N`): `N^{τ - τs/8}` (the regularity error
at `g` and the strip error after the factor `N^{-3τs/8}`), `N^{τ - τs}` (the strip edge above the
domain edge `N^{-1+τ}`).  No `Admissible`, no `τs ≤ 𝔠`. -/
private theorem Step1RegularityGUE_det (d : Sizes) (hd : Tendsto (fun n => d.size n) atTop atTop)
    {κ τ τs E₀ : ℝ} (hκ : 0 < κ) (_hτs0 : 0 < τs) (hτs1 : τs < 1) (hE₀ : |E₀| ≤ 2 - κ)
    (hτ0 : 0 < τ) (hτ : τ < τs / 8) :
    ∀ᶠ n in atTop, ∀ ω : Ω (d.L n) (d.W n),
      Step1LocalEventGUE d n (κ / 2) τ ω → GUEGoodAt d n κ τs E₀ ω := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hFC⟩ := FreeConvStability.freeConv_stable_local hκ
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hc₁0 : 0 < min 1 (c₀ / 8) := lt_min one_pos (by positivity)
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  have eg := Step1RegularityGUE_rpow_ev (e := -1 + τs / 4) (c := 1 / 2) (by linarith)
    (by norm_num)
  have eG := Step1RegularityGUE_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3)))
    (c := min κ 1 / 4) (by linarith) (by positivity)
  have eT := Step1RegularityGUE_rpow_ev (e := -1 + τs) (c := min (min κ 1 / 240) c₀)
    (by linarith) (lt_min (by positivity) hc₀)
  have eerr := Step1RegularityGUE_rpow_ev (e := τ - τs / 8)
    (c := min (min κ 1 / 24) (Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀)))
    (by linarith) (lt_min (by positivity) (by positivity))
  have eedge := Step1RegularityGUE_rpow_ev (e := τ - τs) (c := c₀ / 8)
    (by linarith) (by positivity)
  have eeps := Step1RegularityGUE_rpow_ev (e := -(3 * τs / 8)) (c := c₀ * C₀)
    (by linarith) (by positivity)
  filter_upwards [hNtend.eventually eg, hNtend.eventually eG, hNtend.eventually eT,
    hNtend.eventually eerr, hNtend.eventually eedge, hNtend.eventually eeps,
    hNtend.eventually_ge_atTop 2] with n hg hG hT herr hedge heps hN2
  intro ω hev
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN2' : 2 ≤ d.size n := by exact_mod_cast hN2
  have hN1 : 1 ≤ d.size n := by omega
  have hT1 : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240 := hT.trans (min_le_left _ _)
  have hT2 : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ c₀ := hT.trans (min_le_right _ _)
  have herr1 : ((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) ≤ min κ 1 / 24 :=
    herr.trans (min_le_left _ _)
  have herr2 : ((d.size n : ℕ) : ℝ) ^ (τ - τs / 8) ≤ Real.sqrt (min 1 (c₀ / 8)) / (2 * C₀) :=
    herr.trans (min_le_right _ _)
  unfold GUEGoodAt
  refine ⟨Step1RegularityGUE_regular d n hκ hE₀ (by linarith) hev hN2' hg hG hT1 herr1, ?_⟩
  -- the free-convolution part
  have hTpos : 0 < ouTStar d τs n := Real.rpow_pos_of_pos hNr0 _
  have ht : 0 < 1 - Real.exp (-(ouTStar d τs n)) := Step1RegularityGUE_one_sub_exp_pos hTpos
  have htc : 1 - Real.exp (-(ouTStar d τs n)) ≤ c₀ :=
    (Step1RegularityGUE_one_sub_exp_le _).trans hT2
  have hε0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by positivity
  have hεc : ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ ≤ c₀ := by
    rw [div_le_iff₀ hC₀]; exact heps
  have hedge' : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤
      c₀ / 8 * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) := by
    have hsplit : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) =
        ((d.size n : ℕ) : ℝ) ^ (τ - τs) * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) := by
      rw [← Real.rpow_add hNr0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hedge (Real.rpow_nonneg hNr0.le _)
  obtain ⟨ρ, hρ1, hρ2, -⟩ := hFC (vGUE d n τs E₀ ω) (Real.exp (-(ouTStar d τs n)))
    (1 - Real.exp (-(ouTStar d τs n))) E₀ (((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀)
    ht htc (by ring) hE₀ hε0 hεc
    (fun w hw hlow hw1 => Step1RegularityGUE_strip d n hκ hE₀ hc₀ hC₀ hev hN1 hT1
      hedge' herr2 hw hlow hw1)
  refine ⟨ρ, hρ1, ?_⟩
  calc |ρ - rhoSC E₀| ≤ C₀ * (((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀) := hρ2
    _ = ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by field_simp

/-- **The deterministic half**: `GUEDetHalf`. -/
theorem guedetHalf : GUEDetHalf := by
  intro d hd κ τs E₀ hκ hτs0 hτs1 hE₀ τ hτ0 hτ
  exact Step1RegularityGUE_det d hd hκ hτs0 hτs1 hE₀ hτ0 hτ


/-- **The GUE-side good event** has probability `≥ 1 - N^{-D}` eventually, from `GUELocal` (the
two halves). -/
theorem gueGoodHighProb : GUEGoodHighProb :=
  gueGoodHighProb_of guelocalEventHighProb guedetHalf

end RBM.Univ
