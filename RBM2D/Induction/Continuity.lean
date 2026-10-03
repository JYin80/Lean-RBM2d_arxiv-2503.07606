/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Path.Step2Props
import RBM2D.Gauss.Domination
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.SpectralAlgebra
import Mathlib.Probability.Moments.SubGaussian

/-!
# Continuity of the Green function in time, and the net lift of the Step 1 families

* `GopboundPin` / `gopbound` (`Gopboundu`): the statement carries `0 < κ →` as its first
  hypothesis (the paper proves `Gopboundu` under `κ > 0`, which gives `Im m^{(E n)} > 0`).
* `Step1NetLift` / `step1NetLift`: the net lift from per time to uniform in `u ∈ [s,t]` of the
  Step 1 families `Step1LoopPT → Step1LoopUnif` and `Step1WeakLawPT → Step1WeakLawUnif`, under the
  hypothesis list of `Step2NetLift` (`RBM2D.Path.NetLift`); `Bandwidth` and `CondStInd` are kept
  but unused.

## Proof

The lemmas of `RBM2D.Path.NetLift` that this file needs are `private` there, so they are
re-proved here under `private` names `cont_*`.  Specific to this file: the entry modulus
`cont_entry_diff` of the resolvent along the flow, the `k`-fold telescoping `cont_word_diff` of a
resolvent-loop word (the closing trace is the crude `card(BlockIndex) · ‖·‖` of
`norm_matrix_trace_le_card_mul`), and the sharpened control ratios (`cont_scaleM_ratio`,
`cont_LP_zeta_ratio`), which replace the constant `11/10` of `Step2NetLift` by `1 + N^{-1}`, so that
`(1 + N^{-1})^{3(k-1)} ≤ 2`.

The high-probability bound `‖X‖ ≺ 1` is not available; it is replaced by the
coordinate event `Ξ_n = {every Gaussian coordinate of size n is at most N in absolute value}`,
on which `‖X‖ ≤ 2 N²`, and `P(Ξ_nᶜ) ≤ 4 N² e^{-N²/2}`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 0. The statement `GopboundPin` -/

section Pin

variable (d : Sizes)

/-- **`Gopboundu`**: for every `C > 0` there is `C' > 0` such that, for every
`D > 0`, eventually, outside an event of probability `≤ N^{-D}`,
`max_{0 ≤ u,u' ≤ 1 - N^{-1}, |u-u'| ≤ N^{-C'}} ‖G_u - G_{u'}‖_max ≤ N^{-C}`, at the energy `E n`.
The paper's range `u ≥ N^{-1}` is read as `1 - u ≥ N^{-1}` and "exponentially small" as
`≤ N^{-D}` for all `D`. -/
def GopboundPin (κ : ℝ) (E : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → SizeTendsto d →
  ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    Sizes.seqP d {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
        u ≤ 1 - ((d.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((d.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((d.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ i j : Idx (d.L n) (d.W n),
          ((d.size n : ℕ) : ℝ) ^ (-C) <
            ‖(Sizes.seqHflow d n u ω - spectralZ (E n) u • 1)⁻¹ i j -
              (Sizes.seqHflow d n u' ω - spectralZ (E n) u' • 1)⁻¹ i j‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

end Pin

/-! ## 1. The abstract net lift -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem cont_stochDomAt_of_subset {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U V : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (h : StochDomAt P size ξ' ζ') (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ∩ Ξ l ⊆ badSetAt size ξ' ζ' τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcover : badSetAt size ξ ζ τ l ⊆ (badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ l
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSetAt size ξ ζ τ l) ≤ P ((badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ) :=
        measure_mono hcover
    _ ≤ P (badSetAt size ξ ζ τ l ∩ Ξ l) + P (Ξ l)ᶜ := measure_union_le _ _
    _ ≤ P (badSetAt size ξ' ζ' τ' l) + P (Ξ l)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- The clamped net of `[s n, t n]` at scale `size^{-A-1}`. -/
private def contTime (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

private theorem contTime_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : contTime s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

private theorem cont_exists_close {s t : ℕ → ℝ} (hlen : ∀ n, t n - s n ≤ 1) (A : ℝ) (N n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s n) (t n)) :
    ∃ k, |u - contTime s t A N n k| ≤ 1 / (netSize A N : ℝ) := by
  have hmem : u - s n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen n]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s n + netPt 1 A N k)| ≤ 1 / (netSize A N : ℝ) := by
    have h : u - (s n + netPt 1 A N k) = u - s n - netPt 1 A N k := by ring
    rw [h]; exact hk
  unfold contTime
  rcases le_or_gt (s n + netPt 1 A N k) (t n) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- **The abstract net lift.**
A per-time domination on `TimeIcc s t n × V n`, a polynomial bound
on `#V n`, a good event `Ξ` of high probability on which `ξ` moves by at most `ε n` and `ζ`
by a factor `2` under a time change of size `size^{-A}`, and the lower bound `ε ≤ ζ`, give the
uniform domination. -/
private theorem cont_core {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop)
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1)
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    {ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ} {A Cv : ℝ} (hA : 0 ≤ A) (hCv : 0 ≤ Cv)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv)
    (hpt : PerTimeDomAt P size ξ ζ) {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hlow : ∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω)
    (hclose : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
        ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    StochDomAt P size ξ ζ := by
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  let θ : ∀ n, Fin (netSize (A + 1) (size n) + 1) → TimeIcc s t n := fun n k =>
    ⟨contTime s t (A + 1) (size n) n k, contTime_mem hst _ _ n k⟩
  let ξ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ξ n (θ n p.1, p.2) ω
  let ζ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ζ n (θ n p.1, p.2) ω
  have hpt' : PerTimeDomAt P size ξ' ζ' := by
    intro τ hτ D hD
    filter_upwards [hpt τ hτ D hD] with l hl p
    exact hl (θ l p.1, p.2)
  have hcard' : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Fin (netSize (A + 1) (size n) + 1) × V n) : ℝ) ≤
        (size n : ℝ) ^ (A + 1 + 1 + Cv) := by
    filter_upwards [hcard, hsize.eventually (card_net_le hA1),
      hsize.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
    have hpos : (0 : ℝ) < (size n : ℝ) := by exact_mod_cast h3
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hpos]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (Real.rpow_nonneg hpos.le _)
  have hnet : StochDomAt P size ξ' ζ' :=
    stochDomAt_of_perTimeDomAt P size (C := A + 1 + 1 + Cv) (by linarith) hcard' hpt'
  refine cont_stochDomAt_of_subset hsize hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hclose, hlow, hsize.eventually (eventually_ge_atTop 2),
    hsize.eventually (eventually_le_rpow 3 hτ2)] with n hcloseN hlowN hN2 hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hN2' : (2 : ℝ) ≤ (size n : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (size n : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (netSize (A + 1) (size n) : ℝ) := by
    exact_mod_cast netSize_pos (A + 1) (size n)
  have hmge : (size n : ℝ) ^ (A + 1) ≤ (netSize (A + 1) (size n) : ℝ) :=
    rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < (size n : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos _
  obtain ⟨k, hk⟩ := cont_exists_close hlen (A + 1) (size n) n u.2
  have hdist : |(u : ℝ) - ((θ n k : TimeIcc s t n) : ℝ)| ≤ (size n : ℝ) ^ (-A) := by
    refine hk.trans ?_
    have h1 : 1 / (netSize (A + 1) (size n) : ℝ) ≤ 1 / (size n : ℝ) ^ (A + 1) := by
      gcongr
    refine h1.trans ?_
    rw [div_le_iff₀ hNA1]
    have hmul : (size n : ℝ) ^ (-A) * (size n : ℝ) ^ (A + 1) = (size n : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    rw [hmul, Real.rpow_one]
    linarith
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ u (θ n k) hdist v
  have hzlow : ε n ≤ ζ n (u, v) ω := hlowN (u, v) ω
  have hε0 := hε n
  have hz0 : (0 : ℝ) ≤ ζ n (u, v) ω := le_trans hε0 hzlow
  have hhalf : (size n : ℝ) ^ (τ / 2) * (size n : ℝ) ^ (τ / 2) = (size n : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hbig : (0 : ℝ) ≤ (size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1 := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ ((size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1) * ζ n (u, v) ω :=
    mul_nonneg hbig hz0
  have hhalf0 : (0 : ℝ) ≤ (size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hz'le : (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω ≤
      (size n : ℝ) ^ (τ / 2) * (2 * ζ n (u, v) ω) :=
    mul_le_mul_of_nonneg_left hζ hhalf0
  refine ⟨(k, v), ?_⟩
  change (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω < ξ n (θ n k, v) ω
  nlinarith [hbad, hξ, hprod, hzlow, hz'le]

end Core

/-! ## 2. The good event: every Gaussian coordinate is at most `N` -/

section Good

/-- The good event at size index `n`: every real Gaussian coordinate of size `n` is at most
`size n` in absolute value. -/
private def contGood (d : Sizes) (n : ℕ) : Set (Sizes.SeqΩ d) :=
  {ω | ∀ c : Coord (d.L n) (d.W n), |ω ⟨n, c⟩| ≤ ((d.size n : ℕ) : ℝ)}

private theorem cont_seqGvar_le_one (d : Sizes) (c : Sizes.SeqCoord d) :
    (Sizes.seqGvar d c : ℝ) ≤ 1 := by
  obtain ⟨n, i, j, b⟩ := c
  have hW : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hs : svar (d.L n) (d.W n) i j ≤ 1 := by
    unfold svar
    split_ifs
    · have h1 : ((d.W n : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hW
      have h0 : 0 ≤ ((d.W n : ℝ)⁻¹) := by positivity
      nlinarith
    · norm_num
  have h0 := svar_nonneg (d.L n) (d.W n) i j
  change (if i = j then svar (d.L n) (d.W n) i j else svar (d.L n) (d.W n) i j / 2) ≤ 1
  split_ifs <;> linarith

/-- The Gaussian tail of one coordinate: `P(|Z| ≥ B) ≤ 2 exp(-B²/2)` (variance at most `1`). -/
private theorem cont_coord_tail (d : Sizes) (c : Sizes.SeqCoord d) {B : ℝ} (hB : 0 ≤ B) :
    Sizes.seqP d {ω | B < |ω c|} ≤ ENNReal.ofReal (2 * Real.exp (-B ^ 2 / 2)) := by
  have hmeas : Measurable (fun ω : Sizes.SeqΩ d => ω c) := measurable_pi_apply c
  have hsg : HasSubgaussianMGF (fun ω : Sizes.SeqΩ d => ω c) 1 (Sizes.seqP d) := by
    rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable, Sizes.seqP_map_eval]
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.2
    have h1 := cont_seqGvar_le_one d c
    have h2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    simp only [NNReal.coe_one, zero_mul, zero_add]
    nlinarith
  have h1 := hsg.measure_ge_le hB
  have h2 := hsg.neg.measure_ge_le hB
  simp only [NNReal.coe_one, mul_one] at h1 h2
  have hsub : {ω : Sizes.SeqΩ d | B < |ω c|} ⊆
      {ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Sizes.SeqΩ d => ω c)) ω} := by
    intro ω hω
    have hω' : B < |ω c| := hω
    rcases le_abs.1 (le_of_lt hω') with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hf1 : Sizes.seqP d {ω | B ≤ ω c} ≤ ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h1
  have hf2 : Sizes.seqP d {ω | B ≤ (-(fun ω : Sizes.SeqΩ d => ω c)) ω} ≤
      ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2
  have hp : (0 : ℝ) ≤ Real.exp (-B ^ 2 / 2) := (Real.exp_pos _).le
  calc Sizes.seqP d {ω | B < |ω c|}
      ≤ Sizes.seqP d ({ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Sizes.SeqΩ d => ω c)) ω}) :=
        measure_mono hsub
    _ ≤ Sizes.seqP d {ω | B ≤ ω c} + Sizes.seqP d {ω | B ≤ (-(fun ω : Sizes.SeqΩ d => ω c)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) :=
        add_le_add hf1 hf2
    _ = ENNReal.ofReal (2 * Real.exp (-B ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf

private theorem cont_card_Z2 (m : ℕ) [NeZero m] : (Fintype.card (Z2 m) : ℝ) = (m : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, pow_two]

private theorem cont_card_coord (d : Sizes) (n : ℕ) :
    (Fintype.card (Coord (d.L n) (d.W n)) : ℝ) = 2 * ((d.size n : ℕ) : ℝ) ^ 2 := by
  have h : Fintype.card (Coord (d.L n) (d.W n)) =
      Fintype.card (Idx (d.L n) (d.W n)) * (Fintype.card (Idx (d.L n) (d.W n)) * 2) := by
    simp [Coord, Fintype.card_prod, Fintype.card_bool]
  rw [h]
  push_cast
  have h2 : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
    change (Fintype.card (Z2 (d.W n * d.L n)) : ℝ) = _
    rw [cont_card_Z2]
    simp [Sizes.size]
  rw [h2]; ring

private theorem cont_good_compl (d : Sizes) (n : ℕ) :
    Sizes.seqP d (contGood d n)ᶜ ≤
      ENNReal.ofReal (2 * ((d.size n : ℕ) : ℝ) ^ 2 *
        (2 * Real.exp (-((d.size n : ℕ) : ℝ) ^ 2 / 2))) := by
  have hB : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub : (contGood d n)ᶜ ⊆
      ⋃ c : Coord (d.L n) (d.W n), {ω : Sizes.SeqΩ d | ((d.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|} := by
    intro ω hω
    simp only [contGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨c, hc⟩ := hω
    exact Set.mem_iUnion.2 ⟨c, hc⟩
  calc Sizes.seqP d (contGood d n)ᶜ
      ≤ Sizes.seqP d (⋃ c : Coord (d.L n) (d.W n),
          {ω : Sizes.SeqΩ d | ((d.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|}) := measure_mono hsub
    _ ≤ ∑ c : Coord (d.L n) (d.W n),
          Sizes.seqP d {ω : Sizes.SeqΩ d | ((d.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : Coord (d.L n) (d.W n),
          ENNReal.ofReal (2 * Real.exp (-((d.size n : ℕ) : ℝ) ^ 2 / 2)) :=
        Finset.sum_le_sum fun c _ => cont_coord_tail d ⟨n, c⟩ hB
    _ = ENNReal.ofReal (Fintype.card (Coord (d.L n) (d.W n)) *
          (2 * Real.exp (-((d.size n : ℕ) : ℝ) ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (2 * ((d.size n : ℕ) : ℝ) ^ 2 *
          (2 * Real.exp (-((d.size n : ℕ) : ℝ) ^ 2 / 2))) := by
        rw [cont_card_coord]

/-- `4 x² exp(-x²/2) ≤ x^{-D}` for large `x`. -/
private theorem cont_eventually_tail (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2 * x ^ 2 * (2 * Real.exp (-x ^ 2 / 2)) ≤ x ^ (-D) := by
  have h1 : Tendsto (fun x : ℝ => x ^ (D + 2) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D + 2) (1 / 2) (by norm_num)
  filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hexp : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-(1 / 2) * x) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hxD : 0 < x ^ (-D) := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (D + 2) * x ^ (-D) = x ^ 2 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have h2 : x ^ 2 * Real.exp (-(1 / 2) * x) < x ^ (-D) / 4 := by
    have := mul_lt_mul_of_pos_right hx hxD
    rw [← hsplit]
    nlinarith [this]
  calc 2 * x ^ 2 * (2 * Real.exp (-x ^ 2 / 2))
      = 4 * (x ^ 2 * Real.exp (-x ^ 2 / 2)) := by ring
    _ ≤ 4 * (x ^ 2 * Real.exp (-(1 / 2) * x)) := by
        gcongr
    _ ≤ x ^ (-D) := by linarith

private theorem cont_highProbAt_good (d : Sizes) (hsize : Tendsto d.size atTop atTop) :
    HighProbAt (Sizes.seqP d) d.size (contGood d) := by
  intro D hD
  have hcast : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  filter_upwards [hcast.eventually (cont_eventually_tail D)] with n hn
  exact (cont_good_compl d n).trans (ENNReal.ofReal_le_ofReal hn)

end Good

/-! ## 3. Deterministic estimates in the `L²` operator norm -/

section Resolvent

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖A‖² ≤ ∑ |A_ij|²`. -/
private theorem cont_opNorm_sq_le_frob (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  set F : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hbd : ‖A‖ ≤ Real.sqrt F := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hF, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg F, mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg F]

private theorem cont_norm_le_card_mul (A : Matrix n n ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A‖ ≤ (Fintype.card n : ℝ) * B := by
  have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, B ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  have h2 : ∑ _i : n, ∑ _j : n, B ^ 2 = ((Fintype.card n : ℝ) * B) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    ((cont_opNorm_sq_le_frob A).trans (h1.trans h2.le))

private theorem cont_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/-- The two-matrix resolvent estimate. -/
private theorem cont_green_diff {H H' : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) :
    ‖green H z - green H' z'‖ ≤ η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hzim' : z'.im ≠ 0 := fun h => absurd hz' (by rw [h]; simpa using hη)
  have hA := isUnit_sub_smul_one_of_im_ne_zero hH hzim
  have hB := isUnit_sub_smul_one_of_im_ne_zero hH' hzim'
  have hA' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hB' : (H' - z' • (1 : Matrix n n ℂ)) * green H' z' = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  have hid : green H z - green H' z' =
      green H z * ((H' - H) - (z' - z) • (1 : Matrix n n ℂ)) * green H' z' := by
    calc green H z - green H' z'
        = green H z * ((H' - z' • (1 : Matrix n n ℂ)) * green H' z') -
            (green H z * (H - z • (1 : Matrix n n ℂ))) * green H' z' := by
          rw [hA', hB']; simp
      _ = green H z * ((H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ))) *
            green H' z' := by noncomm_ring
      _ = _ := by
          congr 2
          module
  have hG := norm_green_le hH hη hz
  have hG' := norm_green_le hH' hη hz'
  have hmid : ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖ ≤ ‖H - H'‖ + ‖z - z'‖ := by
    calc ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖
        ≤ ‖H' - H‖ + ‖(z' - z) • (1 : Matrix n n ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖H - H'‖ + ‖z - z'‖ := by
          rw [norm_sub_rev H' H]
          refine add_le_add le_rfl ?_
          rw [norm_smul, norm_sub_rev z' z]
          exact mul_le_of_le_one_right (norm_nonneg _) cont_norm_one_le
  rw [hid]
  calc ‖green H z * ((H' - H) - (z' - z) • (1 : Matrix n n ℂ)) * green H' z'‖
      ≤ ‖green H z‖ * ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖ * ‖green H' z'‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ η⁻¹ * (‖H - H'‖ + ‖z - z'‖) * η⁻¹ := by
        gcongr
    _ = η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := by ring

end Resolvent

section Modulus

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|√x - √y| ≤ √|x - y|` for `x, y ≥ 0`. -/
private theorem cont_abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total y x with h | h
  · have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x - y := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt y * Real.sqrt y ≤ Real.sqrt x * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg y)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2
  · have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt h
    rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt y - Real.sqrt x) ^ 2 ≤ y - x := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt x * Real.sqrt x ≤ Real.sqrt y * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2

private theorem cont_norm_Xentry_le (ω : Ω L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B)
    (i j : Idx L W) : ‖Xentry L W ω i j‖ ≤ 2 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (i, j, true))
  unfold Xentry
  split_ifs
  · calc ‖((ω (i, j, true) : ℝ) : ℂ) + Complex.I * ((ω (i, j, false) : ℝ) : ℂ)‖
        ≤ ‖((ω (i, j, true) : ℝ) : ℂ)‖ + ‖Complex.I * ((ω (i, j, false) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 2 * B := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          linarith [h (i, j, true), h (i, j, false)]
  · calc ‖((ω (j, i, true) : ℝ) : ℂ) - Complex.I * ((ω (j, i, false) : ℝ) : ℂ)‖
        ≤ ‖((ω (j, i, true) : ℝ) : ℂ)‖ + ‖Complex.I * ((ω (j, i, false) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * B := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          linarith [h (j, i, true), h (j, i, false)]
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [h (i, j, true)]

private theorem cont_norm_Xmat_le (ω : Ω L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B) :
    ‖Xmat L W ω‖ ≤ (Fintype.card (Idx L W) : ℝ) * (2 * B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (0, 0, true))
  exact cont_norm_le_card_mul _ (by positivity) fun i j => cont_norm_Xentry_le ω h i j

private theorem cont_norm_blockMat_Xmat_le (ω : Ω L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B) :
    ‖blockMat (Xmat L W ω)‖ ≤ (Fintype.card (BlockIndex L W) : ℝ) * (2 * B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (0, 0, true))
  exact cont_norm_le_card_mul _ (by positivity) fun p q =>
    cont_norm_Xentry_le ω h _ _

private theorem cont_blockMat_sub (M M' : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (M - M') = blockMat M - blockMat M' := by
  ext p q; simp [blockMat]

private theorem cont_blockMat_smul (c : ℂ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (c • M) = c • blockMat M := by
  ext p q; simp [blockMat]

end Modulus

section GreenFlow

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent modulus along the flow: `H - H' = c X`, `|c| ≤ √Δ`, `‖X‖ ≤ Xb`, `‖z - z'‖ ≤ Δ`,
`Δ ≤ 1`, `η⁻¹ ≤ Q`. -/
private theorem cont_green_flow_diff {H H' X : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X) {Xb Δ : ℝ} (hX : ‖X‖ ≤ Xb)
    (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) {z z' : ℂ} {η Q : ℝ} (hη : 0 < η)
    (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) :
    ‖green H z - green H' z'‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
  have h1 := cont_green_diff hH hH' hη hz hz'
  have hQ0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hX0 : 0 ≤ Xb := (norm_nonneg _).trans hX
  have hΔs : Δ ≤ Real.sqrt Δ := by
    calc Δ = Real.sqrt Δ * Real.sqrt Δ := (Real.mul_self_sqrt hΔ0).symm
      _ ≤ Real.sqrt Δ * 1 := by
          gcongr
          rw [Real.sqrt_le_one]; exact hΔ1
      _ = Real.sqrt Δ := mul_one _
  have hHH : ‖H - H'‖ ≤ Real.sqrt Δ * Xb := by
    rw [hd, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hc hX (norm_nonneg _) (Real.sqrt_nonneg _)
  have h2 : η⁻¹ * η⁻¹ ≤ Q * Q := mul_le_mul hQ hQ hQ0 (hQ0.trans hQ)
  calc ‖green H z - green H' z'‖ ≤ η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := h1
    _ ≤ Q * Q * (Real.sqrt Δ * Xb + Real.sqrt Δ) := by
        refine mul_le_mul h2 ?_ (by positivity) (mul_self_nonneg _)
        linarith
    _ = Q * Q * (Xb + 1) * Real.sqrt Δ := by ring

end GreenFlow

section Spectral

/-- `‖m‖ = 1` and `Im m ≤ 1`. -/
private theorem cont_im_m_le_one {E : ℝ} (hE : |E| ≤ 2) : (spectralM E).im ≤ 1 := by
  have h := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE] at h
  exact (le_abs_self _).trans h

private theorem cont_eta_le_abs_im {E t u : ℝ} (hE : |E| < 2) (ht : t < 1) (hut : u ≤ t) :
    etaT E t ≤ |(spectralZ E u).im| := by
  have hm := spectralM_im_pos hE
  rw [spectralZ_im, abs_of_nonneg (mul_nonneg (by linarith) hm.le)]
  unfold etaT
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

private theorem cont_norm_spectralZ_sub {E : ℝ} (hE : |E| ≤ 2) (u u' : ℝ) :
    ‖spectralZ E u - spectralZ E u'‖ = |u - u'| := by
  have h : spectralZ E u - spectralZ E u' = ((u' - u : ℝ) : ℂ) * spectralM E := by
    unfold spectralZ; push_cast; ring
  rw [h, norm_mul, norm_spectralM hE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

end Spectral
section EblkNorm

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem cont_norm_Eblk_le_one (hW : 1 ≤ W) (c : Z2 L) : ‖Eblk L W c‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq L W c).trans ?_
  have h1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have h0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  nlinarith

end EblkNorm

/-! ## 4. Scalar estimates for the controls -/

section Scalars

/-- `|min a x - min a y| ≤ |x - y|`. -/
private theorem cont_abs_min_sub_min_le (a x y : ℝ) : |min a x - min a y| ≤ |x - y| := by
  refine (abs_min_sub_min_le_max a x a y).trans ?_
  simp


private theorem cont_spectralM_im_nonneg (E : ℝ) : 0 ≤ (spectralM E).im := by
  rw [spectralM_im]; positivity

/-- `|M_u - M_{u'}| ≤ Im m · N |u - u'|`. -/
private theorem cont_scaleM_diff {L W : ℕ} (hL : 1 ≤ L) {E u u' : ℝ} (hu : u < 1)
    (hu' : u' < 1) :
    |scaleM L W E u - scaleM L W E u'| ≤
      (spectralM E).im * ((((W * L) ^ 2 : ℕ) : ℝ) * |u - u'|) := by
  rw [scaleM_eq' hL hu, scaleM_eq' hL hu', ← mul_sub, abs_mul,
    abs_of_nonneg (cont_spectralM_im_nonneg E)]
  refine mul_le_mul_of_nonneg_left ?_ (cont_spectralM_im_nonneg E)
  refine (cont_abs_min_sub_min_le _ _ _).trans ?_
  have h : (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u) - (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u') =
      (((W * L) ^ 2 : ℕ) : ℝ) * (u' - u) := by ring
  rw [h, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_sub_comm]

/-- `Im m ≤ M_u` once `N (1 - u) ≥ 1`. -/
private theorem cont_im_le_scaleM {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hu : u < 1)
    (hN : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) : (spectralM E).im ≤ scaleM L W E u := by
  rw [scaleM_eq' hL hu]
  have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)
  have : (1 : ℝ) ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := le_min hW2 hN
  calc (spectralM E).im = (spectralM E).im * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left this (cont_spectralM_im_nonneg E)

/-- `M_u ≤ N` for `|E| ≤ 2`. -/
private theorem cont_scaleM_le {L W : ℕ} (hL : 1 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu : u < 1) :
    scaleM L W E u ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
  rw [scaleM_eq' hL hu]
  have hm := cont_im_m_le_one hE
  have hm0 := cont_spectralM_im_nonneg E
  have h1 : min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) ≤ (W : ℝ) ^ 2 := min_le_left _ _
  have h2 : (W : ℝ) ^ 2 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    push_cast
    rw [mul_pow]
    have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ this
    nlinarith [sq_nonneg (W : ℝ)]
  have h0 : 0 ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := by
    exact le_min (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  calc (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u))
      ≤ 1 * (W : ℝ) ^ 2 := mul_le_mul hm h1 h0 zero_le_one
    _ ≤ _ := by linarith

end Scalars

section Scalars2

private theorem cont_one_div_sqrt_diff {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) :
    |1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u')| ≤ (1 - t)⁻¹ * Real.sqrt |u - u'| := by
  have h1t : 0 < 1 - t := by linarith
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  have ha0 : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have hb0 : 0 < Real.sqrt (1 - u') := Real.sqrt_pos.2 hx'
  have hab : 1 - t ≤ Real.sqrt (1 - u) * Real.sqrt (1 - u') := by
    have hta : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt (by linarith)
    have htb : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u') := Real.sqrt_le_sqrt (by linarith)
    calc 1 - t = Real.sqrt (1 - t) * Real.sqrt (1 - t) := (Real.mul_self_sqrt h1t.le).symm
      _ ≤ _ := mul_le_mul hta htb (Real.sqrt_nonneg _) ha0.le
  have heq : 1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u') =
      (Real.sqrt (1 - u') - Real.sqrt (1 - u)) / (Real.sqrt (1 - u) * Real.sqrt (1 - u')) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0)]
  have hba : |Real.sqrt (1 - u') - Real.sqrt (1 - u)| ≤ Real.sqrt |u - u'| := by
    have h := cont_abs_sqrt_sub_sqrt_le hx'.le hx.le
    have h2 : |(1 - u') - (1 - u)| = |u - u'| := by
      rw [show (1 - u') - (1 - u) = -(u' - u) by ring, abs_neg, abs_sub_comm]
    rwa [h2] at h
  calc |Real.sqrt (1 - u') - Real.sqrt (1 - u)| / (Real.sqrt (1 - u) * Real.sqrt (1 - u'))
      ≤ Real.sqrt |u - u'| / (1 - t) := by gcongr
    _ = (1 - t)⁻¹ * Real.sqrt |u - u'| := by rw [div_eq_inv_mul]

private theorem cont_ellT_diff {L : ℕ} {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) :
    |ellT L u - ellT L u'| ≤ (1 - t)⁻¹ * Real.sqrt |u - u'| := by
  unfold ellT
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (cont_one_div_sqrt_diff ht hut hu't) (by positivity)

end Scalars2

section Ratio

/-- `b⁻¹ ≤ κ a⁻¹` from `a ≤ κ b` (positive `a, b`). -/
private theorem cont_inv_le_const_mul_inv {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ κ * b) : b⁻¹ ≤ κ * a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hb ha]
  nlinarith [h]

end Ratio

section Analytic

/-- `√(N^e) = N^{e/2}`. -/
private theorem cont_sqrt_rpow {N : ℝ} (hN : 0 ≤ N) (e : ℝ) :
    Real.sqrt (N ^ e) = N ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN]
  ring_nf

/-- `Δ ≤ N^{-A}` implies `√Δ ≤ N^{-A/2}`. -/
private theorem cont_sqrt_abs_le {N Δ A : ℝ} (hN : 0 ≤ N) (h : Δ ≤ N ^ (-A)) :
    Real.sqrt Δ ≤ N ^ (-A / 2) := by
  rw [← cont_sqrt_rpow hN]
  exact Real.sqrt_le_sqrt h

end Analytic

section Bulk

/-- The bulk constant: `|E| ≤ 2 - κ` gives `Im m ≥ √(2κ)/2 > 0`. -/
private theorem cont_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    |E| < 2 ∧ Real.sqrt (2 * κ) / 2 ≤ (spectralM E).im := by
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hκ2 : κ ≤ 2 := by linarith
  refine ⟨by linarith, ?_⟩
  rw [spectralM_im]
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ hE0 hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

end Bulk

section Assembly

/-- `C x^p ≤ κ x^q` eventually along `size → ∞`, for `p < q`. -/
private theorem cont_gap {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) (C : ℝ) {κ p q : ℝ}
    (hκ : 0 < κ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, C * ((size n : ℕ) : ℝ) ^ p ≤ κ * ((size n : ℕ) : ℝ) ^ q := by
  filter_upwards [hsize.eventually (eventually_le_rpow (C / κ) (sub_pos.2 hpq)),
    hsize.eventually (eventually_ge_atTop 1)] with n h1 h2
  have hx : (0 : ℝ) < ((size n : ℕ) : ℝ) := by exact_mod_cast h2
  have h3 : C / κ * ((size n : ℕ) : ℝ) ^ p ≤ ((size n : ℕ) : ℝ) ^ (q - p) * ((size n : ℕ) : ℝ) ^ p :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le _)
  rw [← Real.rpow_add hx, sub_add_cancel] at h3
  have h4 : C * ((size n : ℕ) : ℝ) ^ p = κ * (C / κ * ((size n : ℕ) : ℝ) ^ p) := by
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left h3 hκ.le

private theorem cont_pow_mul_rpow {x : ℝ} (hx : 0 < x) (k : ℕ) (e : ℝ) :
    x ^ k * x ^ e = x ^ ((k : ℝ) + e) := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

end Assembly

/-! ## 4. Deterministic estimates along the flow -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The entry modulus of the resolvent along the flow (`Gopboundu`): if
`‖X‖ ≤ Xb`, `u, u' ≤ t < 1`, `|u - u'| ≤ 1` and `(η_t)⁻¹ ≤ Q`, then
`‖G_u - G_{u'}‖_max ≤ Q² (Xb + 1) |u - u'|^{1/2}`. -/
private theorem cont_entry_diff (ω : Ω L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hΔ : |u - u'| ≤ 1)
    (hQ : (etaT E t)⁻¹ ≤ Q) (hX : ‖Xmat L W ω‖ ≤ Xb) (i j : Idx L W) :
    ‖(Hflow L W u ω - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
        (Hflow L W u' ω - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hG := cont_green_flow_diff (Hflow_isHermitian L W u ω) (Hflow_isHermitian L W u' ω)
    (Hflow_sub L W u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ hη hQ
    (cont_eta_le_abs_im hE ht hut) (cont_eta_le_abs_im hE ht hu't)
    (cont_norm_spectralZ_sub hE.le u u').le
  have hent := norm_matrix_entry_le_opNorm
    (green (Hflow L W u ω) (spectralZ E u) - green (Hflow L W u' ω) (spectralZ E u')) i j
  have h3 : (green (Hflow L W u ω) (spectralZ E u) -
        green (Hflow L W u' ω) (spectralZ E u')) i j =
      (Hflow L W u ω - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
        (Hflow L W u' ω - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j := by
    simp [green, Matrix.sub_apply]
  rw [h3] at hent
  exact hent.trans hG

/-- The same modulus for `|(G_u - m)_{ij}|` (`llErrMat`). -/
private theorem cont_llErr_diff (ω : Ω L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hΔ : |u - u'| ≤ 1)
    (hQ : (etaT E t)⁻¹ ≤ Q) (hX : ‖Xmat L W ω‖ ≤ Xb) (i j : Idx L W) :
    |llErrMat L W E u (Hflow L W u ω) i j - llErrMat L W E u' (Hflow L W u' ω) i j| ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
  refine le_trans ?_ (cont_entry_diff ω hE ht hu0 hut hu'0 hu't hΔ hQ hX i j)
  unfold llErrMat
  refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
  rw [sub_sub_sub_cancel_right]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (the `foldr` of `gloopProd`). -/
private noncomputable def contWord (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

omit [NeZero W] in
private theorem contWord_cons (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    contWord H z (p :: l) = Gsig H z p.1 * Eblk L W p.2 * contWord H z l := rfl

private theorem cont_word_norm (hW : 1 ≤ W) {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gsig H z σ‖ ≤ Q) (l : List (Bool × Z2 L)) :
    ‖contWord H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [contWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (L := L) hW p.2
    rw [contWord_cons, List.length_cons, pow_succ]
    calc ‖Gsig H z p.1 * Eblk L W p.2 * contWord H z l‖
        ≤ ‖Gsig H z p.1‖ * ‖Eblk L W p.2‖ * ‖contWord H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word, for the block matrices of `d = 2`. -/
private theorem cont_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gsig H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gsig H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gsig H z σ - Gsig H' z' σ‖ ≤ S) (l : List (Bool × Z2 L)) :
    ‖contWord H z l - contWord H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [contWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (L := L) hW p.2
    rw [contWord_cons, contWord_cons]
    have key : Gsig H z p.1 * Eblk L W p.2 * contWord H z l -
        Gsig H' z' p.1 * Eblk L W p.2 * contWord H' z' l =
        (Gsig H z p.1 - Gsig H' z' p.1) * Eblk L W p.2 * contWord H z l +
          Gsig H' z' p.1 * Eblk L W p.2 * (contWord H z l - contWord H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := cont_word_norm hW hQ l
    have t1 : ‖(Gsig H z p.1 - Gsig H' z' p.1) * Eblk L W p.2 * contWord H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gsig H' z' p.1 * Eblk L W p.2 * (contWord H z l - contWord H' z' l)‖ ≤
        Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hQ' _) hEa (norm_nonneg _) hQ0)) ih
        (norm_nonneg _) (by positivity)
    have hpos : 0 ≤ S * Q ^ l.length * (Q - 1) :=
      mul_nonneg (mul_nonneg hS0 (pow_nonneg hQ0 _)) (sub_nonneg.2 hQ1)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ S * 1 * Q ^ l.length + Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := add_le_add t1 t2
      _ ≤ (((p :: l).length : ℕ) : ℝ) * Q ^ (p :: l).length * S := by
        rw [List.length_cons, pow_succ]
        push_cast
        nlinarith [hpos]

/-- The modulus of a loop of length `k` along the flow, on `‖X‖ ≤ Xb` (`Gopboundu` and the net
argument after it, for the block matrices of `d = 2`; the trace is bounded by
`card(BlockIndex) · ‖·‖`). -/
private theorem cont_loopAbs_diff (hW : 1 ≤ W) (ω : Ω L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (hΔ : |u - u'| ≤ 1) (hQ1 : 1 ≤ Q) (hQ : (etaT E t)⁻¹ ≤ Q)
    (hXb : ‖blockMat (Xmat L W ω)‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    |loopAbs L W E u (Hflow L W u ω) σ a - loopAbs L W E u' (Hflow L W u' ω) σ a| ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((k : ℝ) * Q ^ k * (Q * Q * (Xb + 1) * Real.sqrt |u - u'|)) := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hHu : (blockMat (Hflow L W u ω)).IsHermitian := HflowBlock_isHermitian L W u ω
  have hHu' : (blockMat (Hflow L W u' ω)).IsHermitian := HflowBlock_isHermitian L W u' ω
  have hzu := cont_eta_le_abs_im hE ht hut
  have hzu' := cont_eta_le_abs_im hE ht hu't
  have hzz : ‖spectralZ E u - spectralZ E u'‖ ≤ |u - u'| :=
    (cont_norm_spectralZ_sub hE.le u u').le
  have hd : blockMat (Hflow L W u ω) - blockMat (Hflow L W u' ω) =
      ((Real.sqrt u - Real.sqrt u' : ℝ) : ℂ) • blockMat (Xmat L W ω) := by
    rw [← cont_blockMat_sub, Hflow_sub, cont_blockMat_smul]
  have hgt := cont_green_flow_diff hHu hHu' hd hXb (cont_abs_sqrt_sub_sqrt_le hu0 hu'0)
    (abs_nonneg _) hΔ hη hQ hzu hzu' hzz
  have hgf : ‖green (blockMat (Hflow L W u ω)) ((starRingEnd ℂ) (spectralZ E u)) -
      green (blockMat (Hflow L W u' ω)) ((starRingEnd ℂ) (spectralZ E u'))‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
    refine cont_green_flow_diff hHu hHu' hd hXb (cont_abs_sqrt_sub_sqrt_le hu0 hu'0)
      (abs_nonneg _) hΔ hη hQ ?_ ?_ ?_
    · rw [Complex.conj_im, abs_neg]; exact hzu
    · rw [Complex.conj_im, abs_neg]; exact hzu'
    · rw [← map_sub, Complex.norm_conj]; exact hzz
  have hS : ∀ σ : Bool, ‖Gsig (blockMat (Hflow L W u ω)) (spectralZ E u) σ -
      Gsig (blockMat (Hflow L W u' ω)) (spectralZ E u') σ‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
    intro σ
    cases σ
    · exact hgf
    · exact hgt
  have hGu : ∀ σ : Bool, ‖Gsig (blockMat (Hflow L W u ω)) (spectralZ E u) σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta L W hHu hη hzu σ).trans hQ
  have hGu' : ∀ σ : Bool, ‖Gsig (blockMat (Hflow L W u' ω)) (spectralZ E u') σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta L W hHu' hη hzu' σ).trans hQ
  have hw := cont_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  unfold loopAbs
  refine (abs_norm_sub_norm_le _ _).trans ?_
  unfold gloop
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Flow

/-! ## 5. Sharpened control ratios -/

section Ratio2

/-- `M_u ≤ (1 + x) M_{u'}` when `N |u - u'| ≤ x` (`netLift_scaleM_ratio` has
the fixed constant `11/10`; here it is `1 + x`). -/
private theorem cont_scaleM_ratio {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E t u u' x : ℝ}
    (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t)
    (hN1 : (1 - t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ))
    (hx : (((W * L) ^ 2 : ℕ) : ℝ) * |u - u'| ≤ x) :
    scaleM L W E u ≤ (1 + x) * scaleM L W E u' := by
  have h1t : 0 < 1 - t := by linarith
  have hN0 : 0 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := (mul_nonneg hN0 (abs_nonneg _)).trans hx
  have hNu' : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u') := by
    have h1 : 1 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (1 - t) := by
      have := mul_le_mul_of_nonneg_right hN1 h1t.le
      rwa [inv_mul_cancel₀ h1t.ne'] at this
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hN0)
  have hMu' := cont_im_le_scaleM (E := E) hL hW (by linarith : u' < 1) hNu'
  have hMd := (abs_le.1 (cont_scaleM_diff (W := W) (E := E) hL (by linarith : u < 1)
    (by linarith : u' < 1))).2
  have hm := cont_spectralM_im_nonneg E
  have h2 : (spectralM E).im * ((((W * L) ^ 2 : ℕ) : ℝ) * |u - u'|) ≤ (spectralM E).im * x :=
    mul_le_mul_of_nonneg_left hx hm
  have h3 : (spectralM E).im * x ≤ scaleM L W E u' * x := mul_le_mul_of_nonneg_right hMu' hx0
  nlinarith

/-- `(1 + x)^m ≤ 1 + 2 m x` when `m x ≤ 1/2`. -/
private theorem cont_one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 + 2 * m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hm ⊢
    have hm' : (m : ℝ) * x ≤ 1 / 2 := by nlinarith
    have h1 := ih hm'
    calc (1 + x) ^ (m + 1) = (1 + x) ^ m * (1 + x) := pow_succ _ _
      _ ≤ (1 + 2 * m * x) * (1 + x) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ 1 + 2 * ((m : ℝ) + 1) * x := by
          nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 1 - 2 * (m : ℝ) * x)]

/-- **The control of `Step1LoopUnif` moves by at most a factor `2` under a small time change.**
`ζ_u = (ℓ_u/ℓ_s)^{2(k-1)} M_u^{-(k-1)}`; `ℓ_{u'} ≤ (1 + x) ℓ_u` and `M_{u'}⁻¹ ≤ (1 + x) M_u⁻¹`,
so `ζ_{u'} ≤ (1 + x)^{3(k-1)} ζ_u`. -/
private theorem cont_LP_zeta_ratio {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W)
    {E s t u u' x : ℝ} (k : ℕ) (hE : |E| < 2) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t)
    (hsu' : s ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hN1 : (1 - t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ)) (hx0 : 0 ≤ x)
    (hx1 : (((W * L) ^ 2 : ℕ) : ℝ) * |u - u'| ≤ x)
    (hx2 : (1 - t)⁻¹ * Real.sqrt |u - u'| ≤ x)
    (hk : ((3 * (k - 1) : ℕ) : ℝ) * x ≤ 1 / 2) :
    (ellT L u' / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u')⁻¹ ^ (k - 1) ≤
      2 * ((ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu1 : u < 1 := by linarith
  have hu'1 : u' < 1 := by linarith
  have hℓu : 1 ≤ ellT L u := one_le_ellT hL hu0 hu1
  have hℓs : 0 < ellT L s := (ellT_pos_le hL (by linarith : s < 1)).1
  -- the `ℓ` factor
  have hℓ' : ellT L u' ≤ (1 + x) * ellT L u := by
    have h1 := (abs_le.1 (cont_ellT_diff (L := L) ht hut hu't)).1
    nlinarith
  have hr : ellT L u' / ellT L s ≤ (1 + x) * (ellT L u / ellT L s) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hℓ' hℓs.le
  have hr0 : 0 ≤ ellT L u' / ellT L s :=
    div_nonneg (by linarith [one_le_ellT hL hu'0 hu'1]) hℓs.le
  have hA : (ellT L u' / ellT L s) ^ (2 * (k - 1)) ≤
      (1 + x) ^ (2 * (k - 1)) * (ellT L u / ellT L s) ^ (2 * (k - 1)) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hr0 hr _
  -- the `M` factor
  have hMratio : scaleM L W E u ≤ (1 + x) * scaleM L W E u' :=
    cont_scaleM_ratio hL hW ht hut hu't hN1 hx1
  have hMu_pos : 0 < scaleM L W E u := scaleM_pos hL hW hE hu1
  have hMu'_pos : 0 < scaleM L W E u' := scaleM_pos hL hW hE hu'1
  have hMinv : (scaleM L W E u')⁻¹ ≤ (1 + x) * (scaleM L W E u)⁻¹ :=
    cont_inv_le_const_mul_inv hMu_pos hMu'_pos hMratio
  have hB : (scaleM L W E u')⁻¹ ^ (k - 1) ≤
      (1 + x) ^ (k - 1) * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hMu'_pos.le) hMinv _
  have hpow : (1 + x) ^ (3 * (k - 1)) ≤ 2 := by
    have := cont_one_add_pow_le hx0 (3 * (k - 1)) hk
    nlinarith
  have hζ0 : 0 ≤ (ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    have : 0 ≤ ellT L u / ellT L s := div_nonneg (by linarith) hℓs.le
    positivity
  calc (ellT L u' / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u')⁻¹ ^ (k - 1)
      ≤ ((1 + x) ^ (2 * (k - 1)) * (ellT L u / ellT L s) ^ (2 * (k - 1))) *
          ((1 + x) ^ (k - 1) * (scaleM L W E u)⁻¹ ^ (k - 1)) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = (1 + x) ^ (3 * (k - 1)) *
          ((ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) := by
        rw [show 3 * (k - 1) = 2 * (k - 1) + (k - 1) by ring, pow_add]; ring
    _ ≤ 2 * ((ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) :=
        mul_le_mul_of_nonneg_right hpow hζ0

end Ratio2


/-! ## 6. The closeness statements for the two families -/

section Close

open scoped Matrix.Norms.L2Operator

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N`. -/
private theorem cont_eta_inv_le {E t N c₁ : ℝ} (hE : |E| < 2) (hN0 : 0 < N) (hc₁ : 0 < c₁)
    (hc₁m : c₁ ≤ (spectralM E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N) :
    (etaT E t)⁻¹ ≤ N ^ 2 := by
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  have h1 : (etaT E t)⁻¹ = (1 - t)⁻¹ * ((spectralM E).im)⁻¹ := by
    unfold etaT; rw [mul_inv]
  have h2 : ((spectralM E).im)⁻¹ ≤ N := by
    refine le_trans ?_ hNc
    rw [one_div]; exact inv_anti₀ hc₁ hc₁m
  rw [h1, sq]
  exact mul_le_mul hN1 h2 (inv_nonneg.2 hm.le) hN0.le

/-- `ε ≤ ζ` for `Step1WeakLawUnif`: `M_u ≤ N` gives `N^{-1/4} ≤ M_u^{-1/4}`. -/
private theorem cont_WL_low {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu : u < 1) :
    ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := by
  have hM := scaleM_pos hL hW hE hu
  have hMN := cont_scaleM_le (W := W) hL hE.le hu
  exact Real.rpow_le_rpow (inv_nonneg.2 (Nat.cast_nonneg _)) (inv_anti₀ hM hMN) (by norm_num)

/-- The two conclusions of `hclose` for `Step1WeakLawUnif`, at one index `n`, deterministic. -/
private theorem cont_WL_close {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (hW : 1 ≤ W)
    (ω : Ω L W) {N E t u u' A c₁ : ℝ} (hN : N = (((W * L) ^ 2 : ℕ) : ℝ))
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (ht : t < 1) (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (spectralM E).im) (hNc : 1 / c₁ ≤ N)
    (hN1 : (1 - t)⁻¹ ≤ N) (hgood : ∀ c : Coord L W, |ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 3 * N ^ 6 * N ^ (-A / 2) ≤ (N⁻¹) ^ ((1 : ℝ) / 4)) (i j : Idx L W) :
    llErrMat L W E u (Hflow L W u ω) i j ≤
        llErrMat L W E u' (Hflow L W u' ω) i j + (N⁻¹) ^ ((1 : ℝ) / 4) ∧
      (scaleM L W E u')⁻¹ ^ ((1 : ℝ) / 4) ≤ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := by
  have hL1 : 1 ≤ L := by omega
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW hL1)
    exact_mod_cast this
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := cont_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hcardI : (Fintype.card (Idx L W) : ℝ) = N := by
    change (Fintype.card (Z2 (W * L)) : ℝ) = N
    rw [cont_card_Z2, hN]; push_cast; ring
  have hX : ‖Xmat L W ω‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le ω hgood
    rw [hcardI] at h
    linarith
  have hll := cont_llErr_diff ω (Q := N ^ 2) (Xb := 2 * N ^ 2) hE ht hu0 hut hu'0 hu't hΔ1 hQ
    hX i j
  have hs0' : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
  have hbound : |llErrMat L W E u (Hflow L W u ω) i j - llErrMat L W E u' (Hflow L W u' ω) i j| ≤
      3 * N ^ 6 * N ^ (-A / 2) := by
    refine hll.trans ?_
    have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| =
        (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| := by ring
    rw [e1]
    calc (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| ≤ 3 * N ^ 6 * Real.sqrt |u - u'| :=
          mul_le_mul_of_nonneg_right (by linarith) hs0'
      _ ≤ 3 * N ^ 6 * N ^ (-A / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
  refine ⟨?_, ?_⟩
  · have := (abs_le.1 hbound).2
    linarith [(abs_le.1 (hbound.trans g3)).2]
  · subst hN
    have hx : (((W * L) ^ 2 : ℕ) : ℝ) * |u - u'| ≤ 1 / 10 :=
      (mul_le_mul_of_nonneg_left hy hN0.le).trans g2
    have hMratio' := cont_scaleM_ratio (E := E) hL1 hW ht hut hu't hN1 hx
    have hMratio : scaleM L W E u ≤ (11 / 10) * scaleM L W E u' := by linarith
    have hMu_pos : 0 < scaleM L W E u := scaleM_pos hL1 hW hE (by linarith)
    have hMu'_pos : 0 < scaleM L W E u' := scaleM_pos hL1 hW hE (by linarith)
    have h1 := cont_inv_le_const_mul_inv hMu_pos hMu'_pos hMratio
    have h2 : (scaleM L W E u')⁻¹ ^ ((1 : ℝ) / 4) ≤
        ((11 / 10) * (scaleM L W E u)⁻¹) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (inv_nonneg.2 hMu'_pos.le) h1 (by norm_num)
    rw [Real.mul_rpow (by norm_num) (inv_nonneg.2 hMu_pos.le)] at h2
    have h3 : ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (11 / 10 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ 2 := by rw [Real.rpow_one]; norm_num
    calc (scaleM L W E u')⁻¹ ^ ((1 : ℝ) / 4)
        ≤ (11 / 10 : ℝ) ^ ((1 : ℝ) / 4) * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := h2
      _ ≤ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (inv_nonneg.2 hMu_pos.le) _)

/-- `ε ≤ ζ` for `Step1LoopUnif`: `ℓ_u ≥ ℓ_s` and `M_u ≤ N` give `N^{-k} ≤ ζ_u`. -/
private theorem cont_LP_low {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E s u : ℝ} (k : ℕ)
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1) :
    ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤
      (ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1) := by
  have hN1 : (1 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW (by omega))
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by linarith
  have hℓs : 0 < ellT L s := (ellT_pos_le hL (by linarith : s < 1)).1
  have hr : 1 ≤ ellT L u / ellT L s := (one_le_div hℓs).2 (ellT_mono_ratio hL hs0 hsu hu).1
  have h1 : 1 ≤ (ellT L u / ellT L s) ^ (2 * (k - 1)) := one_le_pow₀ hr
  have hM := scaleM_pos hL hW hE hu
  have hMN := cont_scaleM_le (W := W) hL hE.le hu
  have h2 : ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) ≤ (scaleM L W E u)⁻¹ ^ (k - 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 hN0.le) (inv_anti₀ hM hMN) _
  have h3 : ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤ ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) :=
    pow_le_pow_of_le_one (inv_nonneg.2 hN0.le) (inv_le_one_of_one_le₀ hN1) (Nat.sub_le k 1)
  calc ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ k ≤ ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹) ^ (k - 1) := h3
    _ ≤ (scaleM L W E u)⁻¹ ^ (k - 1) := h2
    _ = 1 * (scaleM L W E u)⁻¹ ^ (k - 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg (inv_nonneg.2 hM.le) _)

/-- The eventual numerical facts for a fixed loop length `k`, in `N` (exponent `A = 6k + 16`). -/
private theorem cont_LP_eventually (k : ℕ) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ 6 * (k : ℝ) ≤ N ∧ (2 : ℝ) ^ k ≤ N ∧
      N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹ ∧
      N * N ^ (-(6 * (k : ℝ) + 16) / 2) ≤ N⁻¹ ∧
      N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (6 * (k : ℝ)),
    eventually_ge_atTop ((2 : ℝ) ^ k)] with N h1 h2 h3
  have hN0 : 0 < N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hinv : N ^ (-1 : ℝ) = N⁻¹ := Real.rpow_neg_one N
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · have e : N * N ^ (-(6 * (k : ℝ) + 16)) = N ^ (1 + -(6 * (k : ℝ) + 16)) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [e, ← hinv]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have e : N * N ^ (-(6 * (k : ℝ) + 16) / 2) = N ^ (1 + -(6 * (k : ℝ) + 16) / 2) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [e, ← hinv]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have e : N ^ (-(6 * (k : ℝ) + 16) / 2) = (N ^ (3 * k + 8))⁻¹ := by
      rw [show -(6 * (k : ℝ) + 16) / 2 = -((3 * k + 8 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hN0.le, Real.rpow_natCast]
    have hpos : 0 < N ^ (3 * k + 8) := pow_pos hN0 _
    have hk1 : 0 < N ^ k := pow_pos hN0 k
    have e2 : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * (N ^ (3 * k + 8))⁻¹)) =
        (3 * k * N ^ (2 * k + 7)) / N ^ (3 * k + 8) := by
      field_simp
      ring
    rw [e, e2, inv_pow, ← one_div, div_le_div_iff₀ hpos hk1]
    have h5 : 3 * (k : ℝ) ≤ N := by linarith
    calc 3 * (k : ℝ) * N ^ (2 * k + 7) * N ^ k = 3 * (k : ℝ) * N ^ (3 * k + 7) := by ring
      _ ≤ N * N ^ (3 * k + 7) := mul_le_mul_of_nonneg_right h5 (pow_nonneg hN0.le _)
      _ = 1 * N ^ (3 * k + 8) := by ring

/-- The two conclusions of `hclose` for `Step1LoopUnif`, at one index `n`, deterministic. -/
private theorem cont_LP_close {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (hW : 1 ≤ W)
    (ω : Ω L W) {N E s t u u' c₁ : ℝ} {k : ℕ} (hN : N = (((W * L) ^ 2 : ℕ) : ℝ))
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u') (hu't : u' ≤ t)
    (ht : t < 1) (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (spectralM E).im) (hNc : 1 / c₁ ≤ N)
    (hN1 : (1 - t)⁻¹ ≤ N) (hgood : ∀ c : Coord L W, |ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16)))
    (g1 : 1 ≤ N) (g2 : 6 * (k : ℝ) ≤ N)
    (gA : N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹)
    (gB : N * N ^ (-(6 * (k : ℝ) + 16) / 2) ≤ N⁻¹)
    (gC : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k)
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    loopAbs L W E u (Hflow L W u ω) σ a ≤ loopAbs L W E u' (Hflow L W u' ω) σ a + (N⁻¹) ^ k ∧
      (ellT L u' / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u')⁻¹ ^ (k - 1) ≤
        2 * ((ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) := by
  have hL1 : 1 ≤ L := by omega
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16) / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := cont_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ g1
  have hcardB : (Fintype.card (BlockIndex L W) : ℝ) = N := by
    rw [card_BlockIndex, hN, mul_comm]
  have hXb : ‖blockMat (Xmat L W ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le ω hgood
    rw [hcardB] at h
    linarith
  have hloop := cont_loopAbs_diff hW ω hE ht hu0 hut hu'0 hu't hΔ1 hQ1 hQ hXb σ a
  rw [hcardB] at hloop
  refine ⟨?_, ?_⟩
  · have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ g1 (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hbound : |loopAbs L W E u (Hflow L W u ω) σ a - loopAbs L W E u' (Hflow L W u' ω) σ a| ≤
        N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) :=
      hloop.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le)
    have := (abs_le.1 (hbound.trans gC)).2
    linarith
  · have hx0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    have hx1 : N * |u - u'| ≤ N⁻¹ := (mul_le_mul_of_nonneg_left hy hN0.le).trans gA
    have hx2 : (1 - t)⁻¹ * Real.sqrt |u - u'| ≤ N⁻¹ :=
      (mul_le_mul hN1 hsq (Real.sqrt_nonneg _) hN0.le).trans gB
    have h3k : ((3 * (k - 1) : ℕ) : ℝ) ≤ 3 * k := by
      exact_mod_cast (by omega : 3 * (k - 1) ≤ 3 * k)
    have hk : ((3 * (k - 1) : ℕ) : ℝ) * N⁻¹ ≤ 1 / 2 := by
      calc ((3 * (k - 1) : ℕ) : ℝ) * N⁻¹ ≤ (3 * k) * N⁻¹ := mul_le_mul_of_nonneg_right h3k hx0
        _ ≤ (N / 2) * N⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hx0
        _ = 1 / 2 := by field_simp
    subst hN
    exact cont_LP_zeta_ratio hL1 hW k hE hs0 hsu hut hsu' hu't ht hN1 hx0 hx1 hx2 hk

end Close

/-! ## 7. The statements and their proofs -/

section Main

open scoped Matrix.Norms.L2Operator

variable (d : Sizes)

/-- **The net lift of the Step 1 families** (the net argument after `Gopboundu`): the
per-time statements `Step1LoopPT`, `Step1WeakLawPT` (`lRB1`, `Gtmwc`) give the u-uniform ones
`Step1LoopUnif`, `Step1WeakLawUnif`, under the hypothesis list of `Step2NetLift`
(`RBM2D.Path.NetLift`).  `Bandwidth` and `CondStInd` are unused by the proof. -/
def Step1NetLift (E : ℕ → ℝ) (κ c τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → SizeTendsto d → Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    (Step1LoopPT d E s t → Step1LoopUnif d E s t) ∧
      (Step1WeakLawPT d E s t → Step1WeakLawUnif d E s t)

/-- **Continuity of the Green function in time** (`Gopboundu`), the statement
`GopboundPin`. -/
theorem gopbound (κ : ℝ) (E : ℕ → ℝ) : GopboundPin d κ E := by
  intro hκ hE hsize C hC
  refine ⟨2 * C + 14, by linarith, fun D hD => ?_⟩
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (spectralM (E n)).im := fun n => cont_bulk hκ (hE n)
  have hcast : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ)) atTop atTop := hsize
  filter_upwards [hcast.eventually_ge_atTop (max 3 (1 / c₁)),
    hcast.eventually (cont_eventually_tail D)] with n hn htail
  have h3 : (3 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  have hc : 1 / c₁ ≤ ((d.size n : ℕ) : ℝ) := (le_max_right _ _).trans hn
  refine le_trans (measure_mono ?_) ((cont_good_compl d n).trans (ENNReal.ofReal_le_ofReal htail))
  rintro ω ⟨u, u', hu0, hu'0, hut, hu't, hΔ, i, j, hbad⟩
  by_contra hng
  have hgood : ∀ c : Coord (d.L n) (d.W n), |ω ⟨n, c⟩| ≤ ((d.size n : ℕ) : ℝ) := by
    simpa [contGood] using hng
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have ht1 : 1 - N⁻¹ < 1 := by have := inv_pos.2 hN0; linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith [inv_pos.2 hN0], by linarith [inv_pos.2 hN0]⟩
  have hN1 : (1 - (1 - N⁻¹))⁻¹ ≤ N := by
    rw [sub_sub_cancel, inv_inv]
  have hQ : (etaT (E n) (1 - N⁻¹))⁻¹ ≤ N ^ 2 :=
    cont_eta_inv_le (hbulk n).1 hN0 hc₁ (hbulk n).2 hc hN1
  have hcardI : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = N := by
    change (Fintype.card (Z2 (d.W n * d.L n)) : ℝ) = N
    rw [cont_card_Z2]; simp [hNdef, Sizes.size]
  have hX : ‖Xmat (d.L n) (d.W n) (Sizes.slice d n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (Sizes.slice d n ω) hgood
    rw [hcardI] at h
    linarith
  have key := cont_entry_diff (Sizes.slice d n ω) (Q := N ^ 2) (Xb := 2 * N ^ 2) (hbulk n).1 ht1
    hu0 hut hu'0 hu't hΔ1 hQ hX i j
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(2 * C + 14) / 2) := cont_sqrt_abs_le hN0.le hΔ
  have hN6 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
    have hN1' : (1 : ℝ) ≤ N := by linarith
    have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hN1' (by norm_num)
    nlinarith
  have hexp : 3 * N ^ 6 * N ^ (-(2 * C + 14) / 2) ≤ N ^ (-C) := by
    have e1 : N ^ 6 * N ^ (-(2 * C + 14) / 2) = N ^ (-C) * N⁻¹ := by
      rw [cont_pow_mul_rpow hN0 6 _, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hp : 0 ≤ N ^ (-C) := Real.rpow_nonneg hN0.le _
    calc 3 * N ^ 6 * N ^ (-(2 * C + 14) / 2) = 3 * (N ^ 6 * N ^ (-(2 * C + 14) / 2)) := by ring
      _ = (3 * N⁻¹) * N ^ (-C) := by rw [e1]; ring
      _ ≤ 1 * N ^ (-C) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          rw [← div_eq_mul_inv, div_le_one hN0]
          exact h3
      _ = N ^ (-C) := one_mul _
  have hfin : ‖(Sizes.seqHflow d n u ω - spectralZ (E n) u • 1)⁻¹ i j -
      (Sizes.seqHflow d n u' ω - spectralZ (E n) u' • 1)⁻¹ i j‖ ≤ N ^ (-C) :=
    key.trans ((mul_le_mul hN6 hsq (Real.sqrt_nonneg _) (by positivity)).trans hexp)
  exact absurd hbad (not_lt.2 hfin)

/-- **The net lift of the Step 1 families**: `Step1LoopPT → Step1LoopUnif` and
`Step1WeakLawPT → Step1WeakLawUnif`. -/
theorem step1NetLift : ∀ E κ c τ s t, Step1NetLift d E κ c τ s t := by
  intro E κ c τ s t hκ hE _hc hτ hs0 hst ht1 hsize _hBand _hCond hRange
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (spectralM (E n)).im := fun n => cont_bulk hκ (hE n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have evc : ∀ᶠ n : ℕ in atTop, 1 / c₁ ≤ ((d.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop _
  have evR : ∀ᶠ n : ℕ in atTop, (1 - t n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by
    filter_upwards [hRange, ev1] with n hn h1
    have hx0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hpos : 0 < ((d.size n : ℕ) : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hx0 _
    have h2 := inv_anti₀ hpos hn
    rw [← Real.rpow_neg hx0.le] at h2
    refine h2.trans ?_
    calc ((d.size n : ℕ) : ℝ) ^ (-(-1 + τ)) ≤ ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = _ := Real.rpow_one _
  refine ⟨fun hPT => ?_, fun hPT => ?_⟩
  · -- the loop family
    unfold Step1LoopUnif
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA0 : 0 ≤ 6 * (k : ℝ) + 16 := by linarith
    have hcard : ∀ᶠ n : ℕ in atTop,
        (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
          ((d.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) := by
      filter_upwards [hcast.eventually (cont_LP_eventually k)] with n hev
      obtain ⟨g1, _, g3, -⟩ := hev
      have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
      have e : ((d.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) =
          ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) := by
        rw [Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_one]
      have hcardV : (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) =
          (2 : ℝ) ^ k * ((d.L n : ℝ) ^ 2) ^ k := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
        push_cast
        rw [cont_card_Z2]
      have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
      have hL0 : (0 : ℝ) ≤ (d.L n : ℝ) := Nat.cast_nonneg _
      have hLW : (d.L n : ℝ) ≤ (d.W n : ℝ) * (d.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
      have eN : ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
        simp [Sizes.size]
      have hLN : (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
        rw [eN]; exact pow_le_pow_left₀ hL0 hLW 2
      rw [e, hcardV]
      calc (2 : ℝ) ^ k * ((d.L n : ℝ) ^ 2) ^ k
          ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ k :=
            mul_le_mul g3 (pow_le_pow_left₀ (by positivity) hLN k) (by positivity) hN0.le
        _ = ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) := by ring
    refine cont_core (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n))) hsizeN hst hlen
      (A := 6 * (k : ℝ) + 16) (Cv := (k : ℝ) + 1) hA0 (by linarith) hcard (hPT k hk)
      (cont_highProbAt_good d hsizeN)
      (ε := fun n => (((d.size n : ℕ) : ℝ)⁻¹) ^ k)
      (fun n => pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, σ, a⟩ := p
      have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
      exact cont_LP_low hL1 (d.W_pos n) k (hbulk n).1 (hs0 n) u.2.1
        (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [hcast.eventually (cont_LP_eventually k), evc, evR] with n hev hc hR
      obtain ⟨g1, g2, _, gA, gB, gC⟩ := hev
      intro ω hω u u' hΔ v
      obtain ⟨σ, a⟩ := v
      exact cont_LP_close (d.three_le_L n) (d.W_pos n) (Sizes.slice d n ω)
        (N := ((d.size n : ℕ) : ℝ)) (E := E n) (s := s n) (t := t n) (u := u) (u' := u')
        rfl (hbulk n).1 (hs0 n) u.2.1 u.2.2 u'.2.1 u'.2.2 (ht1 n) hc₁ (hbulk n).2 hc hR
        (fun c => hω c) hΔ g1 g2 gA gB gC σ a
  · -- the weak law
    unfold Step1WeakLawUnif
    have evg2 : ∀ᶠ n : ℕ in atTop,
        ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤ 1 / 10 := by
      filter_upwards [cont_gap hsizeN 1 (κ := 1 / 10) (p := 1 - 40) (q := 0) (by norm_num)
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
      have : ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) =
          ((d.size n : ℕ) : ℝ) ^ (1 - 40 : ℝ) := by
        rw [show (1 - 40 : ℝ) = 1 + -40 by ring, Real.rpow_add hx0, Real.rpow_one]
      rw [this]
      rw [Real.rpow_zero] at hn
      linarith
    have evg3 : ∀ᶠ n : ℕ in atTop,
        3 * ((d.size n : ℕ) : ℝ) ^ 6 * ((d.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) ≤
          (((d.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) := by
      filter_upwards [cont_gap hsizeN 3 (κ := 1) (p := 6 - 40 / 2) (q := -(1 / 4)) one_pos
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
      have e1 : 3 * ((d.size n : ℕ) : ℝ) ^ 6 * ((d.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) =
          3 * ((d.size n : ℕ) : ℝ) ^ (6 - 40 / 2 : ℝ) := by
        rw [mul_assoc, cont_pow_mul_rpow hx0]
        congr 2
        push_cast; ring
      have e2 : (((d.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) =
          ((d.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
      rw [e1, e2]
      linarith
    have hcard : ∀ n : ℕ, (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
      intro n
      rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_two]
      have h : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
        change (Fintype.card (Z2 (d.W n * d.L n)) : ℝ) = _
        rw [cont_card_Z2]
        simp [Sizes.size]
      rw [h]; ring_nf; exact le_rfl
    refine cont_core (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) hsizeN hst hlen
      (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
      (cont_highProbAt_good d hsizeN)
      (ε := fun n => (((d.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4))
      (fun n => Real.rpow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, i, j⟩ := p
      have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
      exact cont_WL_low hL1 (d.W_pos n) (hbulk n).1 (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [evc, evR, evg2, evg3] with n hc hR g2 g3
      intro ω hω u u' hΔ v
      obtain ⟨i, j⟩ := v
      exact cont_WL_close (d.three_le_L n) (d.W_pos n) (Sizes.slice d n ω)
        (N := ((d.size n : ℕ) : ℝ)) (E := E n) (t := t n) (u := u) (u' := u') (A := 40)
        (c₁ := c₁) rfl (hbulk n).1 ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2
        (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ g2 g3 i j

end Main

end RBM.Ind
