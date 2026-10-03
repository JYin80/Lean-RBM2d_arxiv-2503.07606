/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.CltSwap
import RBM2D.Evolution.CltGood
import RBM2D.Evolution.CltPath

/-!
# One real coordinate of the telescoping

Paper: Section 7, the proof of `clt-lemmafar`.  The definitions `cltXo`, `cltGamma` (section
`Step`) and the statement `CltStep` (section `Assembly`) are stated below.

* `cltStep : CltStep d κ 𝔠 δ`: one real coordinate `c = e⁻¹(k)` of the telescoping changes
  `∫ X_i Γ_i d(P⊗P)` by at most `N^{-D-3}`, eventually in `n`, uniformly in the labels `b`, the
  isolated index `i`, the enumeration `e` and the step `k`.

Proof.  If `gvar c = 0` the coordinate is `0`
almost surely under both factors and the step vanishes.  Otherwise the blocks of `c` are adjacent
(`cltCoord_adj`) and `cltFarGeomHalf` splits into case A (the block of `c` is far from `b_i`: the
path bound `cltPath_bound` at `(T_k, ω' c)`) and case B (it is far from every `b_m`, `m ≠ i`: the
exchange `cltSwap c` kills `∫ (X_i(T_k) - X_i(T_{k+1})) Γ_i(ω^{c→0})`, and `cltPath_bound` at
`(ω, 0)` bounds `Γ_i(ω) - Γ_i(ω^{c→0})`).  Outside the good event (E1 at `ω c`, `ω' c`; E2, E3 at
`ω` and at `T_k`, whose law is `P` by `measurePreserving_cltSplit`) the integrand is bounded by the
deterministic bound `cltEval_det_le`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## The statements -/

section Step

variable {L W K : ℕ} [NeZero L] [NeZero W]

/-- The centred factor `X_m`: `Y_{b_m} - 𝔼Y_{b_m}` for `m < p`, its conjugate for `m ≥ p`
(the integrand of `CltFar`, on the finite model). -/
def cltXo {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ) (b : Fin (2 * p) → Z2 L) (m : Fin (2 * p))
    (ω : Ω L W) : ℂ :=
  if (m : ℕ) < p then cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W)
  else (starRingEnd ℂ) (cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W))

/-- `Γ_i = ∏_{m ≠ i} X_m`. -/
def cltGamma {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ) (b : Fin (2 * p) → Z2 L) (i : Fin (2 * p))
    (ω : Ω L W) : ℂ :=
  ∏ m ∈ Finset.univ.erase i, cltXo F E u b m ω

end Step

section Helpers

variable {L W K : ℕ} [NeZero L] [NeZero W]

private theorem cltstep_zs_im {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool) :
    (if σ then spectralZ E u else (starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by
  cases σ <;> simpa using hz

/-- The entries of `G_u(σ)` at `Hflow u ω` are continuous in `ω`. -/
private theorem cltstep_gEntry_cont {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool)
    (x y : Idx L W) : Continuous fun ω : Ω L W => gEntry L W E u (Hflow L W u ω) σ x y :=
  (continuous_green_of_isHermitian (continuous_Hflow L W u) (Hflow_isHermitian L W u)
    (cltstep_zs_im hz σ)).matrix_elem x y

private theorem cltstep_Y_meas (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Z2 L) : Measurable fun ω : Ω L W => cltYo F E u ω b := by
  have hc : Continuous fun ω : Ω L W => cltYo F E u ω b := by
    unfold cltYo cltY LocalForm.eval
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun q _ => ?_
    exact continuous_const.mul
      (continuous_finsetProd _ fun i _ => cltstep_gEntry_cont hz _ _ _)
  exact hc.measurable

private theorem cltstep_Xo_meas {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Fin (2 * p) → Z2 L) (m : Fin (2 * p)) :
    Measurable (cltXo F E u b m) := by
  have h1 := (cltstep_Y_meas F hz (b m)).sub_const (∫ ω', cltYo F E u ω' (b m) ∂(P L W))
  by_cases hm : (m : ℕ) < p
  · have h : cltXo F E u b m =
        fun ω => cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W) := by
      funext ω; simp only [cltXo, hm, ↓reduceIte]
    rw [h]; exact h1
  · have h : cltXo F E u b m =
        fun ω => (starRingEnd ℂ) (cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W)) := by
      funext ω; simp only [cltXo, hm, ↓reduceIte]
    rw [h]; exact Complex.continuous_conj.measurable.comp h1

private theorem cltstep_Gamma_meas {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Fin (2 * p) → Z2 L) (i : Fin (2 * p)) :
    Measurable (cltGamma F E u b i) := by
  have h : cltGamma F E u b i = fun ω => ∏ m ∈ Finset.univ.erase i, cltXo F E u b m ω := rfl
  rw [h]
  exact Finset.measurable_prod _ fun m _ => cltstep_Xo_meas F hz b m

/-- The centring cancels in a difference, and conjugation is an isometry. -/
private theorem cltstep_Xo_sub {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ)
    (b : Fin (2 * p) → Z2 L) (m : Fin (2 * p)) (ω ω' : Ω L W) :
    ‖cltXo F E u b m ω - cltXo F E u b m ω'‖ =
      ‖cltYo F E u ω (b m) - cltYo F E u ω' (b m)‖ := by
  by_cases hm : (m : ℕ) < p
  · simp only [cltXo, hm, ↓reduceIte, sub_sub_sub_cancel_right]
  · simp only [cltXo, hm, ↓reduceIte]
    rw [← map_sub, Complex.norm_conj, sub_sub_sub_cancel_right]

private theorem cltstep_Xo_le {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ)
    (b : Fin (2 * p) → Z2 L) {BY : ℝ} (hY : ∀ ω b', ‖cltYo F E u ω b'‖ ≤ BY)
    (m : Fin (2 * p)) (ω : Ω L W) : ‖cltXo F E u b m ω‖ ≤ 2 * BY := by
  have hint : ‖∫ ω', cltYo F E u ω' (b m) ∂(P L W)‖ ≤ BY := by
    have h := norm_integral_le_of_norm_le_const (μ := P L W)
      (f := fun ω' => cltYo F E u ω' (b m)) (Filter.Eventually.of_forall fun ω' => hY ω' (b m))
    simpa using h
  have h1 : ‖cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W)‖ ≤ 2 * BY := by
    have := norm_sub_le (cltYo F E u ω (b m)) (∫ ω', cltYo F E u ω' (b m) ∂(P L W))
    linarith [hY ω (b m)]
  by_cases hm : (m : ℕ) < p
  · simpa only [cltXo, hm, ↓reduceIte] using h1
  · simpa only [cltXo, hm, ↓reduceIte, Complex.norm_conj] using h1

private theorem cltstep_Gamma_le {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ)
    (b : Fin (2 * p) → Z2 L) {X : ℝ} (hX1 : 1 ≤ X) (hX : ∀ m ω, ‖cltXo F E u b m ω‖ ≤ X)
    (i : Fin (2 * p)) (ω : Ω L W) : ‖cltGamma F E u b i ω‖ ≤ X ^ (2 * p) := by
  unfold cltGamma
  rw [norm_prod]
  calc ∏ m ∈ Finset.univ.erase i, ‖cltXo F E u b m ω‖ ≤ ∏ _m ∈ Finset.univ.erase i, X :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => hX m ω
    _ = X ^ (Finset.univ.erase i).card := Finset.prod_const X
    _ ≤ X ^ (2 * p) := pow_le_pow_right₀ hX1 (Finset.card_erase_le.trans (by simp))

private theorem cltstep_coefSum_nonneg (F : LocalForm L W 1 K) (b : Z2 L) :
    0 ≤ cltCoefSum F b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The coefficient weight in terms of the coefficient bound and `card Idx`. -/
private theorem cltstep_coefSum_le (F : LocalForm L W 1 K) {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C0) (b : Z2 L) :
    cltCoefSum F b ≤
      (K + 1) * ((2 * (Fintype.card (Idx L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K)) := by
  unfold cltCoefSum
  have h1 : 1 ≤ 2 * (Fintype.card (Idx L W) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ Fintype.card (Idx L W) := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hA : 0 ≤ C0 * K * 4 ^ K := by positivity
  calc ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
        ‖F.coef (fun _ => b) j q‖ * (j : ℝ) * 4 ^ (j : ℕ)
      ≤ ∑ j : Fin (K + 1), ∑ _q : Fin j → Idx L W × Idx L W × Bool, C0 * K * 4 ^ K := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun q _ => ?_
        have hj : (j : ℕ) ≤ K := Nat.lt_succ_iff.mp j.2
        have hj' : ((j : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
        have h4 : (4 : ℝ) ^ (j : ℕ) ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hj
        exact mul_le_mul (mul_le_mul (hC _ j q) hj' (Nat.cast_nonneg _) hC0) h4 (by positivity)
          (mul_nonneg hC0 (Nat.cast_nonneg _))
    _ = ∑ j : Fin (K + 1), (2 * (Fintype.card (Idx L W) : ℝ) ^ 2) ^ (j : ℕ) * (C0 * K * 4 ^ K) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Idx L W) (Idx L W × Bool),
          Fintype.card_prod (Idx L W) Bool, Fintype.card_bool]
        push_cast
        ring
    _ ≤ ∑ _j : Fin (K + 1), (2 * (Fintype.card (Idx L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.mp j.2)) hA
    _ = (K + 1) * ((2 * (Fintype.card (Idx L W) : ℝ) ^ 2) ^ K * (C0 * K * 4 ^ K)) := by
        simp

end Helpers

/-- The finite-product difference bound: `|∏ f - ∏ g| ≤ #s · X^{#s} · δ` when all factors are
`≤ X` (`X ≥ 1`) and differ by `≤ δ`. -/
private theorem cltstep_prod_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hf : ∀ j ∈ s, ‖f j‖ ≤ X) (hg : ∀ j ∈ s, ‖g j‖ ≤ X)
    (hfg : ∀ j ∈ s, ‖f j - g j‖ ≤ δ) :
    ‖∏ j ∈ s, f j - ∏ j ∈ s, g j‖ ≤ s.card * X ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have ih' := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    have hX0 : 0 ≤ X := by linarith
    have hfs : ‖∏ j ∈ s, f j‖ ≤ X ^ s.card := by
      rw [norm_prod]
      calc ∏ j ∈ s, ‖f j‖ ≤ ∏ _j ∈ s, X :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
              fun j hj => hf j (Finset.mem_insert_of_mem hj)
        _ = X ^ s.card := Finset.prod_const X
    have hga := hg a (Finset.mem_insert_self a s)
    have hfga := hfg a (Finset.mem_insert_self a s)
    have e : f a * ∏ j ∈ s, f j - g a * ∏ j ∈ s, g j =
        (f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j) := by ring
    have hpow : X ^ s.card ≤ X ^ s.card * X := le_mul_of_one_le_right (pow_nonneg hX0 _) hX
    have hp0 : 0 ≤ X ^ s.card := pow_nonneg hX0 _
    have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    rw [e]
    calc ‖(f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j)‖
        ≤ ‖f a - g a‖ * ‖∏ j ∈ s, f j‖ + ‖g a‖ * ‖∏ j ∈ s, f j - ∏ j ∈ s, g j‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul]
      _ ≤ δ * X ^ s.card + X * (s.card * X ^ s.card * δ) := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * X ^ (s.card + 1) * δ := by
          have h := mul_le_mul_of_nonneg_left hpow hδ
          rw [pow_succ]
          push_cast
          nlinarith [mul_nonneg (mul_nonneg hc0 hp0) hδ]

/-- `‖∫ H‖ ≤ g + M ε` when `‖H‖ ≤ M` everywhere, `‖H‖ ≤ g` off `B`, and `μ B ≤ ε` (no
measurability of `H` or `B` is needed). -/
private theorem cltstep_norm_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (H : α → ℂ) (B : Set α) {g M ε : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hB : μ B ≤ ENNReal.ofReal ε) (hall : ∀ x, ‖H x‖ ≤ M)
    (hgood : ∀ x, x ∉ B → ‖H x‖ ≤ g) : ‖∫ x, H x ∂μ‖ ≤ g + M * ε := by
  have hBm : MeasurableSet (toMeasurable μ B) := measurableSet_toMeasurable μ B
  have hdom : ∀ x, ‖H x‖ ≤ g + (toMeasurable μ B).indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ toMeasurable μ B
    · rw [Set.indicator_of_mem hx]; linarith [hall x]
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact hgood x fun h => hx (subset_toMeasurable μ B h)
  have hi1 : Integrable (fun _ : α => g) μ := integrable_const g
  have hi2 : Integrable (fun x => (toMeasurable μ B).indicator (fun _ => M) x) μ :=
    (integrable_const M).indicator hBm
  have hreal : μ.real (toMeasurable μ B) ≤ ε := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε hB
  calc ‖∫ x, H x ∂μ‖ ≤ ∫ x, (g + (toMeasurable μ B).indicator (fun _ => M) x) ∂μ :=
        norm_integral_le_of_norm_le (hi1.add hi2) (Filter.Eventually.of_forall hdom)
    _ = g + μ.real (toMeasurable μ B) * M := by
        rw [integral_add hi1 hi2, integral_const, integral_indicator hBm, setIntegral_const]
        simp [smul_eq_mul]
    _ ≤ g + M * ε := by nlinarith

/-- Pull-back of any set along a measure-preserving map. -/
private theorem cltstep_pull_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν) (S : Set β) :
    μ (f ⁻¹' S) ≤ ν S := by
  calc μ (f ⁻¹' S) ≤ μ.map f S := Measure.le_map_apply hf.measurable.aemeasurable S
    _ = ν S := by rw [hf.map_eq]

/-- A coordinate of variance `0` is `0` almost surely. -/
private theorem cltstep_ae_zero {L W : ℕ} [NeZero L] [NeZero W] (c : Coord L W)
    (hc : gvar L W c = 0) : ∀ᵐ ω ∂(P L W), ω c = 0 := by
  have hmap := P_map_eval L W c
  rw [hc, gaussianReal_zero_var] at hmap
  have h : ∀ᵐ x ∂((P L W).map (fun ω : Ω L W => ω c)), x = 0 := by
    rw [hmap]
    exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl
  exact ae_of_ae_map (measurable_pi_apply c).aemeasurable h

/-- **The step at one size** (deterministic inputs and probability bounds as hypotheses).  With
`‖X_m‖ ≤ X` (`X ≥ 1`), `4 · cltCoefSum ≤ Bc`, the events E1 (every coordinate), E2, E3 of
probability `≤ ε`, and the side conditions of `cltPath_bound`, one step of the telescoping is
bounded by `4p X^{2p+1} Bc W^{-D'} + 4 X^{2p+1} · 6ε`. -/
private theorem cltstep_core {L W K : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (F : LocalForm L W 1 K) (E u τ D' : ℝ) {p : ℕ} (hp : 1 ≤ p) (b : Fin (2 * p) → Z2 L)
    (i : Fin (2 * p)) (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ)
    (hk : k < Fintype.card (Coord L W))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hz : (spectralZ E u).im ≠ 0) (hloc : F.Local τ u)
    (hw : 6 ≤ (W : ℝ) ^ τ) (hℓ : 1 ≤ ellT L u) (hθ : 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1)
    (hiso : ∀ m, m ≠ i → (W : ℝ) ^ (2 * τ) * ellT L u ≤ (zdist2 L (b i - b m) : ℝ))
    {X Bc ε : ℝ} (hX1 : 1 ≤ X) (hX : ∀ m ω, ‖cltXo F E u b m ω‖ ≤ X)
    (hBc0 : 0 ≤ Bc) (hBc : ∀ b', 4 * cltCoefSum F b' ≤ Bc) (hε : 0 ≤ ε)
    (hE1 : ∀ c : Coord L W, P L W {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤ ENNReal.ofReal ε)
    (hE2 : P L W {ω | ∃ (σ : Bool) (x y : Idx L W),
      2 < ‖gEntry L W E u (Hflow L W u ω) σ x y‖} ≤ ENNReal.ofReal ε)
    (hE3 : P L W {ω | ∃ (σ : Bool) (x y : Idx L W),
      (W : ℝ) ^ τ * ellT L u ≤ (zdist2 L ((splitEquiv L W x).1 - (splitEquiv L W y).1) : ℝ) ∧
        (W : ℝ) ^ (-D') < ‖gEntry L W E u (Hflow L W u ω) σ x y‖} ≤ ENNReal.ofReal ε) :
    ‖∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W))‖ ≤
      4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) + 4 * (X * X ^ (2 * p)) * (6 * ε) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Coord L W, e.symm ⟨k, hk⟩ = c := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : 0 ≤ X ^ (2 * p) := pow_nonneg hX0 _
  have hγ0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hG0 : 0 ≤ Bc * (W : ℝ) ^ (-D') := mul_nonneg hBc0 hγ0
  have hv0 : 0 ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv1 : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hXQ0 : 0 ≤ X * X ^ (2 * p) := mul_nonneg hX0 hQ0
  have hg0 : 0 ≤ 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by positivity
  have hM0 : 0 ≤ 4 * (X * X ^ (2 * p)) := by positivity
  have h6ε : 0 ≤ 6 * ε := by linarith
  -- the hybrids at `c`
  have hTk : ∀ q : Ω L W × Ω L W, cltHyb L W e k q.1 q.2 c = q.1 c := by
    intro q
    have h := cltHyb_eq_update_succ L W e k hk q.1 q.2
    rw [hc] at h
    rw [h, Function.update_self]
  have hTk1 : ∀ q : Ω L W × Ω L W, cltHyb L W e (k + 1) q.1 q.2 =
      Function.update (cltHyb L W e k q.1 q.2) c (q.2 c) := by
    intro q
    have h := cltHyb_succ L W e k hk q.1 q.2
    rw [hc] at h
    exact h
  -- the bound of the difference factor
  have hdiff : ∀ q : Ω L W × Ω L W, ‖cltXo F E u b i (cltHyb L W e k q.1 q.2) -
      cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)‖ ≤ 2 * X := by
    intro q
    have h1 := hX i (cltHyb L W e k q.1 q.2)
    have h2 := hX i (cltHyb L W e (k + 1) q.1 q.2)
    exact (norm_sub_le _ _).trans (by linarith)
  -- Case 0: `gvar c = 0`
  by_cases hg : gvar L W c = 0
  · have h1 : ∀ᵐ q ∂((P L W).prod (P L W)), q.1 c = 0 := by
      have h := cltstep_ae_zero c hg
      rw [← (measurePreserving_fst (μ := P L W) (ν := P L W)).map_eq] at h
      exact ae_of_ae_map measurable_fst.aemeasurable h
    have h2 : ∀ᵐ q ∂((P L W).prod (P L W)), q.2 c = 0 := by
      have h := cltstep_ae_zero c hg
      rw [← (measurePreserving_snd (μ := P L W) (ν := P L W)).map_eq] at h
      exact ae_of_ae_map measurable_snd.aemeasurable h
    have h0 : ∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h1, h2] with q hq1 hq2
      have hq : cltHyb L W e (k + 1) q.1 q.2 = cltHyb L W e k q.1 q.2 := by
        rw [hTk1 q, hq2, Function.update_eq_self_iff, hTk q, hq1]
      simp only [Pi.zero_apply, hq, sub_self, zero_mul]
    rw [h0, norm_zero]
    positivity
  have hadj := (cltCoord_adj L W hL c).1 hg
  -- the bad sample set (E2 ∪ E3) and the good set `cltGoodAt`
  obtain ⟨Sb, hSb⟩ : ∃ S : Set (Ω L W), S =
      {ω | ∃ (σ : Bool) (x y : Idx L W), 2 < ‖gEntry L W E u (Hflow L W u ω) σ x y‖} ∪
      {ω | ∃ (σ : Bool) (x y : Idx L W),
        (W : ℝ) ^ τ * ellT L u ≤ (zdist2 L ((splitEquiv L W x).1 - (splitEquiv L W y).1) : ℝ) ∧
          (W : ℝ) ^ (-D') < ‖gEntry L W E u (Hflow L W u ω) σ x y‖} := ⟨_, rfl⟩
  have hSbP : P L W Sb ≤ ENNReal.ofReal (2 * ε) := by
    rw [hSb]
    calc P L W (_ ∪ _) ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hE2 hE3
      _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε hε]; ring_nf
  have hgoodOf : ∀ ω, ω ∉ Sb → cltGoodAt E u (ellT L u * (W : ℝ) ^ τ) D' ω := by
    intro ω hω
    rw [hSb] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hω
    exact ⟨fun σ x y => hω.1 σ x y, fun σ x y hρ => hω.2 σ x y (by rwa [mul_comm] at hρ)⟩
  -- the bad pair set
  obtain ⟨A1, hA1⟩ : ∃ A : Set (Ω L W × Ω L W),
      A = Prod.fst ⁻¹' {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : Set (Ω L W × Ω L W),
      A = Prod.snd ⁻¹' {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A : Set (Ω L W × Ω L W), A = Prod.fst ⁻¹' Sb := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A : Set (Ω L W × Ω L W),
      A = (fun q : Ω L W × Ω L W => cltHyb L W e k q.1 q.2) ⁻¹' Sb := ⟨_, rfl⟩
  have hmpT : MeasurePreserving (fun q : Ω L W × Ω L W => cltHyb L W e k q.1 q.2)
      ((P L W).prod (P L W)) (P L W) := measurePreserving_cltSplit L W (cltHybSet L W e k)
  have hmpT1 : MeasurePreserving (fun q : Ω L W × Ω L W => cltHyb L W e (k + 1) q.1 q.2)
      ((P L W).prod (P L W)) (P L W) := measurePreserving_cltSplit L W (cltHybSet L W e (k + 1))
  have hBq : ((P L W).prod (P L W)) (A1 ∪ A2 ∪ A3 ∪ A4) ≤ ENNReal.ofReal (6 * ε) := by
    have h1 : ((P L W).prod (P L W)) A1 ≤ ENNReal.ofReal ε := by
      rw [hA1]; exact (cltstep_pull_le measurePreserving_fst _).trans (hE1 c)
    have h2 : ((P L W).prod (P L W)) A2 ≤ ENNReal.ofReal ε := by
      rw [hA2]; exact (cltstep_pull_le measurePreserving_snd _).trans (hE1 c)
    have h3 : ((P L W).prod (P L W)) A3 ≤ ENNReal.ofReal (2 * ε) := by
      rw [hA3]; exact (cltstep_pull_le measurePreserving_fst _).trans hSbP
    have h4 : ((P L W).prod (P L W)) A4 ≤ ENNReal.ofReal (2 * ε) := by
      rw [hA4]; exact (cltstep_pull_le hmpT _).trans hSbP
    calc ((P L W).prod (P L W)) (A1 ∪ A2 ∪ A3 ∪ A4)
        ≤ ((P L W).prod (P L W)) (A1 ∪ A2 ∪ A3) + ((P L W).prod (P L W)) A4 :=
          measure_union_le _ _
      _ ≤ ((P L W).prod (P L W)) (A1 ∪ A2) + ((P L W).prod (P L W)) A3 +
            ((P L W).prod (P L W)) A4 := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ((P L W).prod (P L W)) A1 + ((P L W).prod (P L W)) A2 + ((P L W).prod (P L W)) A3 +
            ((P L W).prod (P L W)) A4 :=
          add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal (2 * ε) +
            ENNReal.ofReal (2 * ε) := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = ENNReal.ofReal (6 * ε) := by
          rw [← ENNReal.ofReal_add hε hε, ← ENNReal.ofReal_add (by linarith) (by linarith),
            ← ENNReal.ofReal_add (by linarith) (by linarith)]
          ring_nf
  have hgoodq : ∀ q : Ω L W × Ω L W, q ∉ A1 ∪ A2 ∪ A3 ∪ A4 →
      |q.1 c| ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) ∧ |q.2 c| ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) ∧
        q.1 ∉ Sb ∧ cltHyb L W e k q.1 q.2 ∉ Sb := by
    intro q hq
    rw [hA1, hA2, hA3, hA4] at hq
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_lt] at hq
    exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2, hq.2⟩
  -- the geometry
  have hsq : ((W : ℝ) ^ τ) ^ 2 = (W : ℝ) ^ (2 * τ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  rcases cltFarGeomHalf L (2 * p) b i ((W : ℝ) ^ (2 * τ) * ellT L u) (splitEquiv L W c.1).1
    hiso with hA | hB
  · -- Case A: the block of `c` is far from `b_i`
    have hfar : ((W : ℝ) ^ τ) ^ 2 * ellT L u / 2 ≤
        (zdist2 L ((splitEquiv L W c.1).1 - b i) : ℝ) := by
      rw [hsq]; exact hA
    refine cltstep_norm_integral_le ((P L W).prod (P L W)) _ (A1 ∪ A2 ∪ A3 ∪ A4) hg0 hM0 h6ε
      hBq (fun q => ?_) (fun q hq => ?_)
    · rw [norm_mul]
      calc _ ≤ (2 * X) * X ^ (2 * p) :=
            mul_le_mul (hdiff q) (cltstep_Gamma_le F E u b hX1 hX i q.1) (norm_nonneg _)
              (by linarith)
        _ ≤ 4 * (X * X ^ (2 * p)) := by nlinarith
    · obtain ⟨hq1, hq2, -, hq4⟩ := hgoodq q hq
      have hs : |q.2 c - cltHyb L W e k q.1 q.2 c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [hTk q]
        have a1 := abs_le.1 hq1
        have a2 := abs_le.1 hq2
        exact abs_le.2 ⟨by linarith, by linarith⟩
      have hpb := cltPath_bound L W K F E u τ D' (b i) c (cltHyb L W e k q.1 q.2) (q.2 c) hu0
        hu1 hz hloc hw hℓ hθ hadj hfar (hgoodOf _ hq4) hs
      have hcs := cltstep_coefSum_nonneg F (b i)
      have hY : ‖cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)‖ ≤ 2 * (Bc * (W : ℝ) ^ (-D')) := by
        rw [cltstep_Xo_sub, hTk1 q, norm_sub_rev]
        refine hpb.trans ?_
        have ha : |q.2 c - cltHyb L W e k q.1 q.2 c| ≤ 2 := by linarith
        have hb : |q.2 c - cltHyb L W e k q.1 q.2 c| * (4 * cltCoefSum F (b i)) ≤ 2 * Bc :=
          mul_le_mul ha (hBc (b i)) (by positivity) (by norm_num)
        calc |q.2 c - cltHyb L W e k q.1 q.2 c| * 4 * cltCoefSum F (b i) * (W : ℝ) ^ (-D')
            = (|q.2 c - cltHyb L W e k q.1 q.2 c| * (4 * cltCoefSum F (b i))) *
                (W : ℝ) ^ (-D') := by ring
          _ ≤ (2 * Bc) * (W : ℝ) ^ (-D') := mul_le_mul_of_nonneg_right hb hγ0
          _ = 2 * (Bc * (W : ℝ) ^ (-D')) := by ring
      rw [norm_mul]
      have hΓ := cltstep_Gamma_le F E u b hX1 hX i q.1
      calc _ ≤ (2 * (Bc * (W : ℝ) ^ (-D'))) * X ^ (2 * p) :=
            mul_le_mul hY hΓ (norm_nonneg _) (by positivity)
        _ ≤ 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by
            have h := mul_nonneg (mul_nonneg hG0 hQ0)
              (show (0 : ℝ) ≤ 4 * p * X - 2 by nlinarith)
            nlinarith
  · -- Case B: the block of `c` is far from every `b_m`, `m ≠ i`
    have hfarm : ∀ m, m ≠ i → ((W : ℝ) ^ τ) ^ 2 * ellT L u / 2 ≤
        (zdist2 L ((splitEquiv L W c.1).1 - b m) : ℝ) := by
      intro m hm; rw [hsq]; exact hB m hm
    obtain ⟨H0, hH0⟩ : ∃ H : Ω L W × Ω L W → ℂ, H = fun q =>
        (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) *
          cltGamma F E u b i (Function.update q.1 c 0) := ⟨_, rfl⟩
    have hanti : ∀ q, H0 (cltSwap L W c q) = -H0 q := by
      intro q
      have h1 := cltHyb_cltSwap L W e k hk q
      have h2 := cltHyb_succ_cltSwap L W e k hk q
      rw [hc] at h1 h2
      rw [hH0]
      simp only [h1, h2, update_cltSwap_fst]
      ring
    have hint0 : ∫ q, H0 q ∂((P L W).prod (P L W)) = 0 :=
      integral_eq_zero_of_cltSwap_neg L W c H0 hanti
    have hmU : Measurable fun q : Ω L W × Ω L W => Function.update q.1 c (0 : ℝ) :=
      measurable_update'.comp (measurable_fst.prodMk measurable_const)
    have hmD : Measurable fun q : Ω L W × Ω L W =>
        cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2) :=
      ((cltstep_Xo_meas F hz b i).comp hmpT.measurable).sub
        ((cltstep_Xo_meas F hz b i).comp hmpT1.measurable)
    have hiF : Integrable (fun q : Ω L W × Ω L W =>
        (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1)
        ((P L W).prod (P L W)) := by
      refine Integrable.of_bound
        (hmD.mul ((cltstep_Gamma_meas F hz b i).comp measurable_fst)).aestronglyMeasurable
        ((2 * X) * X ^ (2 * p)) (Filter.Eventually.of_forall fun q => ?_)
      rw [norm_mul]
      exact mul_le_mul (hdiff q) (cltstep_Gamma_le F E u b hX1 hX i q.1) (norm_nonneg _)
        (by linarith)
    have hiF0 : Integrable H0 ((P L W).prod (P L W)) := by
      rw [hH0]
      refine Integrable.of_bound
        (hmD.mul ((cltstep_Gamma_meas F hz b i).comp hmU)).aestronglyMeasurable
        ((2 * X) * X ^ (2 * p)) (Filter.Eventually.of_forall fun q => ?_)
      rw [norm_mul]
      exact mul_le_mul (hdiff q) (cltstep_Gamma_le F E u b hX1 hX i _) (norm_nonneg _)
        (by linarith)
    have hsplit : ∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W)) =
        ∫ q, ((cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1 - H0 q)
        ∂((P L W).prod (P L W)) := by
      rw [integral_sub hiF hiF0, hint0, sub_zero]
    rw [hsplit]
    have hH0q : ∀ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1 - H0 q =
        (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) *
          (cltGamma F E u b i q.1 - cltGamma F E u b i (Function.update q.1 c 0)) := by
      intro q; rw [hH0]; ring
    refine cltstep_norm_integral_le ((P L W).prod (P L W)) _ (A1 ∪ A2 ∪ A3 ∪ A4) hg0 hM0 h6ε
      hBq (fun q => ?_) (fun q hq => ?_)
    · rw [hH0q, norm_mul]
      have hΓ1 := cltstep_Gamma_le F E u b hX1 hX i q.1
      have hΓ2 := cltstep_Gamma_le F E u b hX1 hX i (Function.update q.1 c 0)
      have hΓ : ‖cltGamma F E u b i q.1 - cltGamma F E u b i (Function.update q.1 c 0)‖ ≤
          2 * X ^ (2 * p) := (norm_sub_le _ _).trans (by linarith)
      calc _ ≤ (2 * X) * (2 * X ^ (2 * p)) :=
            mul_le_mul (hdiff q) hΓ (norm_nonneg _) (by linarith)
        _ = 4 * (X * X ^ (2 * p)) := by ring
    · obtain ⟨hq1, -, hq3, -⟩ := hgoodq q hq
      have hs : |0 - q.1 c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [zero_sub, abs_neg]; linarith
      have hm : ∀ m ∈ Finset.univ.erase i,
          ‖cltXo F E u b m q.1 - cltXo F E u b m (Function.update q.1 c 0)‖ ≤
            Bc * (W : ℝ) ^ (-D') := by
        intro m hm
        have hmi : m ≠ i := Finset.ne_of_mem_erase hm
        have hpb := cltPath_bound L W K F E u τ D' (b m) c q.1 0 hu0 hu1 hz hloc hw hℓ hθ hadj
          (hfarm m hmi) (hgoodOf _ hq3) hs
        have hcs := cltstep_coefSum_nonneg F (b m)
        rw [cltstep_Xo_sub, norm_sub_rev]
        refine hpb.trans ?_
        have ha : |0 - q.1 c| ≤ 1 := by rw [zero_sub, abs_neg]; linarith
        have hb : |0 - q.1 c| * (4 * cltCoefSum F (b m)) ≤ 1 * Bc :=
          mul_le_mul ha (hBc (b m)) (by positivity) (by norm_num)
        calc |0 - q.1 c| * 4 * cltCoefSum F (b m) * (W : ℝ) ^ (-D')
            = (|0 - q.1 c| * (4 * cltCoefSum F (b m))) * (W : ℝ) ^ (-D') := by ring
          _ ≤ (1 * Bc) * (W : ℝ) ^ (-D') := mul_le_mul_of_nonneg_right hb hγ0
          _ = Bc * (W : ℝ) ^ (-D') := by ring
      have hprod := cltstep_prod_sub_le (Finset.univ.erase i) (fun m => cltXo F E u b m q.1)
        (fun m => cltXo F E u b m (Function.update q.1 c 0)) hX1 hG0
        (fun m _ => hX m q.1) (fun m _ => hX m _) hm
      have hcard : (Finset.univ.erase i).card ≤ 2 * p := Finset.card_erase_le.trans (by simp)
      have hcard' : (((Finset.univ.erase i).card : ℕ) : ℝ) ≤ 2 * p := by exact_mod_cast hcard
      have hpowc : X ^ (Finset.univ.erase i).card ≤ X ^ (2 * p) := pow_le_pow_right₀ hX1 hcard
      have hΓ : ‖cltGamma F E u b i q.1 - cltGamma F E u b i (Function.update q.1 c 0)‖ ≤
          2 * p * X ^ (2 * p) * (Bc * (W : ℝ) ^ (-D')) := by
        refine hprod.trans ?_
        have := mul_le_mul hcard' hpowc (pow_nonneg hX0 _) (by positivity)
        exact mul_le_mul_of_nonneg_right this hG0
      rw [hH0q, norm_mul]
      calc _ ≤ (2 * X) * (2 * p * X ^ (2 * p) * (Bc * (W : ℝ) ^ (-D'))) :=
            mul_le_mul (hdiff q) hΓ (norm_nonneg _) (by linarith)
        _ = 4 * p * (X * X ^ (2 * p)) * (Bc * (W : ℝ) ^ (-D')) := by ring

/-- `c_κ > 0` for `0 < κ`, `|E| ≤ 2 - κ` (a re-proof of the private `cltres_ck_pos` of
`RBM2D/Evolution/CltResolvent.lean`). -/
private theorem cltstep_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltCk κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltCk
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- Absorption of a constant `A ≤ N` into one power of `N`. -/
private theorem cltstep_absorb {N A x y : ℝ} (hN : 1 ≤ N) (hA : A ≤ N) (hxy : x + 1 ≤ y) :
    A * N ^ x ≤ N ^ y := by
  have hN0 : 0 < N := by linarith
  calc A * N ^ x ≤ N * N ^ x := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = N ^ (x + 1) := by rw [Real.rpow_add_one hN0.ne', mul_comm]
    _ ≤ N ^ y := Real.rpow_le_rpow_of_exponent_le hN hxy

section Assembly

variable (d : Sizes)

/-- **One real coordinate of the telescoping** (replaces `clt-taylor`,
`clt-remainder-bound`/`clt-remainder-bound-same`, `clt-ibp`, `clt-ibp-bound5`; the paper's
conclusion "`E[Δ_ij Y Γ] = O(W^{-D})`" before the proof of `clt-lemma`).  Under `H_clt` and the
coefficient and locality bounds: for all `p ≥ 1`, `D > 0`, eventually in `n`, for every `b` with an
isolated label `b_i` (separation `W^{2τ} ℓ_u`), every enumeration `e` of the coordinates and every
`k < card`, `‖∫ (X_i(T_k) - X_i(T_{k+1})) Γ_i(ω) d(P⊗P)‖ ≤ N^{-D-3}`.  It gives `CltFarThm`
(with `CltTelescope` and `2N²` steps). -/
def CltStep (κ 𝔠 δ : ℝ) : Prop :=
  ∀ (K : ℕ) (C' τ : ℝ) (E s₀ t₀ u t : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K),
    HClt d κ 𝔠 δ E s₀ t₀ u t → 0 ≤ C' → 0 < τ →
    (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
    (∀ n, (F n).Local τ (u n)) →
    ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop,
      ∀ (b : Fin (2 * p) → Z2 (d.L n)) (i : Fin (2 * p)),
        (∀ k, k ≠ i →
          (d.W n : ℝ) ^ (2 * τ) * ellT (d.L n) (u n) ≤ (zdist2 (d.L n) (b i - b k) : ℝ)) →
        ∀ (e : Coord (d.L n) (d.W n) ≃ Fin (Fintype.card (Coord (d.L n) (d.W n)))) (k : ℕ),
          k < Fintype.card (Coord (d.L n) (d.W n)) →
          ‖∫ q, (cltXo (F n) (E n) (u n) b i (cltHyb (d.L n) (d.W n) e k q.1 q.2) -
                cltXo (F n) (E n) (u n) b i (cltHyb (d.L n) (d.W n) e (k + 1) q.1 q.2)) *
              cltGamma (F n) (E n) (u n) b i q.1
            ∂((P (d.L n) (d.W n)).prod (P (d.L n) (d.W n)))‖ ≤
            ((d.size n : ℕ) : ℝ) ^ (-D - 3)

/-- **`CltStep`**: exponents: `a = C' + 3K + 2` (so that
`‖X_m‖ ≤ N^a` and `4 · cltCoefSum ≤ N^a`), `D'' = a(2p+2) + D + 4` (the events E1–E3), and
`D' = D''/𝔠` (the far scale, `W^{-D'} ≤ N^{-D''}` by `Bandwidth`); the step is then
`≤ (4p + 24) N^{-D-4} ≤ N^{-D-3}`. -/
theorem cltStep (κ 𝔠 δ : ℝ) : CltStep d κ 𝔠 δ := by
  intro K C' τ E s₀ t₀ u t F hH hC' hτ hcoef hloc p hp D hD
  obtain ⟨hκ, h𝔠, hδ, hE, hs0, hs0u, -, hut, ht1, hN, hBW, hRange, -, -, -⟩ := id hH
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = C' + 3 * K + 2 := ⟨_, rfl⟩
  obtain ⟨D'', hD''⟩ : ∃ x : ℝ, x = a * (2 * p + 2) + D + 4 := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ x : ℝ, x = D'' / 𝔠 := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ha0 : 0 < a := by rw [ha]; linarith
  have hD''0 : 0 < D'' := by
    have : 0 ≤ a * (2 * p + 2) := mul_nonneg ha0.le (by positivity)
    rw [hD'']; linarith
  have hD'0 : 0 < D' := by rw [hD']; exact div_pos hD''0 h𝔠
  have hck : 0 < cltCk κ := cltstep_ck_pos hκ (hE 0)
  obtain ⟨C1, hC1⟩ : ∃ C : ℝ, C = 2 * (K + 1) * (2 / cltCk κ) ^ K := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C : ℝ, C = 4 * (K + 1) * 2 ^ K * K * 4 ^ K := ⟨_, rfl⟩
  have hWt : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hBW ((tendsto_rpow_atTop h𝔠).comp hN)
  filter_upwards [hN.eventually_ge_atTop (max (max C1 C2) (max (4 * p + 24) 1)), hBW, hRange,
    ((tendsto_rpow_atTop hτ).comp hWt).eventually_ge_atTop 6,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hWt).eventually_ge_atTop 16,
    cltCoord_tail d 𝔠 h𝔠 hN hBW D'' hD''0, cltGmax_whp d κ 𝔠 δ E s₀ t₀ u t hH D'' hD''0,
    cltFarEntry_whp d κ 𝔠 δ E s₀ t₀ u t hH τ hτ D' hD'0 D'' hD''0]
    with n hNn hBWn hRn hWτ hW12 hE1 hE2 hE3
  intro b i hiso e k hk
  have hw : 6 ≤ (d.W n : ℝ) ^ τ := hWτ
  have hW12' : 16 ≤ (d.W n : ℝ) ^ (1 / 2 : ℝ) := hW12
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNn
  have hN0 : 0 < N := by linarith
  have hNC1 : C1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNn
  have hNC2 : C2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNn
  have hNC3 : 4 * p + 24 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNn
  have hL3 := d.three_le_L n
  have hu0 : 0 ≤ u n := (hs0 n).trans (hs0u n)
  have hu1 : u n < 1 := (hut n).trans_lt (ht1 n)
  have hR : N ^ (-1 + δ) ≤ 1 - u n := by have := hut n; linarith [hRn]
  have hηlow := cltEta_lower (d.L n) (d.W n) κ δ (E n) (u n) hκ hδ (hE n) hR
  have hz : (spectralZ (E n) (u n)).im ≠ 0 := by
    have h0 : 0 < cltCk κ / N := div_pos hck hN0
    exact (lt_of_lt_of_le h0 hηlow).ne'
  have hℓ : 1 ≤ ellT (d.L n) (u n) := one_le_ellT (by omega) hu0 hu1
  have hθ : 16 * (d.W n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have hpos : 0 < (d.W n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv, div_le_one hpos]
    exact hW12'
  -- `‖X_m‖ ≤ N^a`
  have hYn : ∀ (ω : Ω (d.L n) (d.W n)) (b' : Z2 (d.L n)),
      ‖cltYo (F n) (E n) (u n) ω b'‖ ≤ (K + 1) * N ^ C' * (2 * N ^ 3 / cltCk κ) ^ K :=
    fun ω b' => cltEval_det_le (d.L n) (d.W n) κ δ (E n) (u n) K (F n) C'
      (Hflow (d.L n) (d.W n) (u n) ω) b' hκ hδ (hE n) hR (hcoef n)
      (Hflow_isHermitian _ _ _ _)
  have hBY : 2 * ((K + 1) * N ^ C' * (2 * N ^ 3 / cltCk κ) ^ K) ≤ N ^ a := by
    have e1 : (2 * N ^ 3 / cltCk κ) ^ K = (2 / cltCk κ) ^ K * N ^ ((3 * K : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_mul, ← mul_pow]
      congr 1
      ring
    have e2 : 2 * ((K + 1) * N ^ C' * (2 * N ^ 3 / cltCk κ) ^ K) =
        C1 * N ^ (C' + ((3 * K : ℕ) : ℝ)) := by
      rw [e1, Real.rpow_add hN0, hC1]
      ring
    rw [e2]
    exact cltstep_absorb hN1 hNC1 (by rw [ha]; push_cast; linarith)
  have hX : ∀ m ω, ‖cltXo (F n) (E n) (u n) b m ω‖ ≤ N ^ a := fun m ω =>
    (cltstep_Xo_le (F n) (E n) (u n) b hYn m ω).trans hBY
  have hX1 : 1 ≤ N ^ a := Real.one_le_rpow hN1 ha0.le
  -- `4 · cltCoefSum ≤ N^a`
  have hcardN : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
    simp [Idx, Z2, ZMod.card, Sizes.size, sq]
  have hcard : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = N := by
    rw [hNdef, hcardN]
  have hBc : ∀ b', 4 * cltCoefSum (F n) b' ≤ N ^ a := by
    intro b'
    have h1 := cltstep_coefSum_le (F n) (Real.rpow_nonneg hN0.le C') (hcoef n) b'
    rw [hcard] at h1
    have e1 : 4 * ((K + 1) * ((2 * N ^ 2) ^ K * (N ^ C' * K * 4 ^ K))) =
        C2 * N ^ (C' + ((2 * K : ℕ) : ℝ)) := by
      rw [Real.rpow_add hN0, Real.rpow_natCast, hC2, mul_pow, pow_mul]
      ring
    calc 4 * cltCoefSum (F n) b' ≤ 4 * ((K + 1) * ((2 * N ^ 2) ^ K * (N ^ C' * K * 4 ^ K))) := by
          linarith
      _ = C2 * N ^ (C' + ((2 * K : ℕ) : ℝ)) := e1
      _ ≤ N ^ a := cltstep_absorb hN1 hNC2 (by rw [ha]; push_cast; linarith)
  -- the step at size `n`
  have hcore := cltstep_core hL3 (F n) (E n) (u n) τ D' hp b i e k hk hu0 hu1 hz (hloc n) hw hℓ
    hθ hiso (X := N ^ a) (Bc := N ^ a) (ε := N ^ (-D'')) hX1 hX (Real.rpow_nonneg hN0.le a) hBc
    (Real.rpow_nonneg hN0.le _) hE1 hE2 hE3
  refine hcore.trans ?_
  -- the exponent count
  have hγρ : (d.W n : ℝ) ^ (-D') ≤ N ^ (-D'') := by
    have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 𝔠
    calc (d.W n : ℝ) ^ (-D') ≤ (N ^ 𝔠) ^ (-D') :=
          Real.rpow_le_rpow_of_nonpos hNc hBWn (by linarith)
      _ = N ^ (-D'') := by
          rw [← Real.rpow_mul hN0.le]
          congr 1
          rw [hD']
          field_simp
  have hΛ : N ^ a * (N ^ a) ^ (2 * p) * N ^ a * N ^ (-D'') = N ^ (-D - 4) := by
    have e1 : N ^ a * (N ^ a) ^ (2 * p) * N ^ a = (N ^ a) ^ (2 * p + 2) := by ring
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    rw [hD'']
    push_cast
    ring
  have hZ0 : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le a
  have hQ0 : 0 ≤ (N ^ a) ^ (2 * p) := pow_nonneg hZ0 _
  have hρ0 : 0 ≤ N ^ (-D'') := Real.rpow_nonneg hN0.le _
  have hZQ : N ^ a * (N ^ a) ^ (2 * p) ≤ N ^ a * (N ^ a) ^ (2 * p) * N ^ a :=
    le_mul_of_one_le_right (mul_nonneg hZ0 hQ0) hX1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hT0 : 0 ≤ 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) := by
    have := mul_nonneg (mul_nonneg hZ0 hQ0) hZ0
    positivity
  calc 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p)) * (N ^ a * (d.W n : ℝ) ^ (-D')) +
        4 * (N ^ a * (N ^ a) ^ (2 * p)) * (6 * N ^ (-D''))
      = 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * (d.W n : ℝ) ^ (-D') +
          24 * (N ^ a * (N ^ a) ^ (2 * p)) * N ^ (-D'') := by ring
    _ ≤ 4 * (p : ℝ) * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * N ^ (-D'') +
          24 * (N ^ a * (N ^ a) ^ (2 * p) * N ^ a) * N ^ (-D'') :=
        add_le_add (mul_le_mul_of_nonneg_left hγρ hT0)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZQ (by norm_num)) hρ0)
    _ = (4 * p + 24) * N ^ (-D - 4) := by rw [← hΛ]; ring
    _ ≤ N ^ (-D - 3) := cltstep_absorb hN1 hNC3 (by linarith)

end Assembly

end RBM.Evol
