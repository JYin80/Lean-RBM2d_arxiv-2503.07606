/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.CltStep
import RBM2D.Evolution.CltMoments
import RBM2D.Evolution.CltResolvent
import RBM2D.Evolution.Case3Defs

/-!
# The far decorrelation `CltFar` and Cases 1, 2 of the CLT estimate

Paper: Section 7, `clt-lemmafar` and its closing sentence; `clt-lemma-final-result`;
`clt-lemma-final-result2`.  The statements `CltFarThm`, `cltCase1Prec_of_farThm`,
`cltCase2Prec_of_farThm` (section `Assembly`) are stated below.

* `cltFar : CltFarThm d κ 𝔠 δ`: `CltFar d F E u τ`.  Proof: the integral over `Sizes.seqP d`
  is the integral over the finite model `P L W` (`cltTransfer`); `∏_m X_m = X_i Γ_i`; `X_i` is
  centred, so `∫ X_i Γ_i dP = ∫ (X_i(ω) - X_i(ω')) Γ_i(ω) d(P⊗P)` (`integral_fun_fst`,
  `integral_prod_mul`); the telescoping `cltTelescope` over the `card Coord = 2 N²` real
  coordinates and the per-step bound `cltStep` (each step `≤ N^{-D-3}`) give
  `≤ 2 N^{-D-1} ≤ N^{-D} ≤ W^{-D}` for `N ≥ 2`, `W ≤ N`.
* `cltCase1Prec`, `cltCase2Prec`: Cases 1 and 2 at the constant `C = 4`.

The private helpers `cltdec_*` before the statements are re-proofs, for this file, of the private
measurability and bound lemmas `cltstep_*` of `RBM2D/Evolution/CltStep.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## Private helpers -/

section Helpers

variable {L W K : ℕ} [NeZero L] [NeZero W]

private theorem cltdec_zs_im {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool) :
    (if σ then spectralZ E u else (starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by
  cases σ <;> simpa using hz

/-- The entries of `G_u(σ)` at `Hflow u ω` are continuous in `ω`. -/
private theorem cltdec_gEntry_cont {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool)
    (x y : Idx L W) : Continuous fun ω : Ω L W => gEntry L W E u (Hflow L W u ω) σ x y :=
  (continuous_green_of_isHermitian (continuous_Hflow L W u) (Hflow_isHermitian L W u)
    (cltdec_zs_im hz σ)).matrix_elem x y

private theorem cltdec_Y_meas (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Z2 L) : Measurable fun ω : Ω L W => cltYo F E u ω b := by
  have hc : Continuous fun ω : Ω L W => cltYo F E u ω b := by
    unfold cltYo cltY LocalForm.eval
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun q _ => ?_
    exact continuous_const.mul
      (continuous_finsetProd _ fun i _ => cltdec_gEntry_cont hz _ _ _)
  exact hc.measurable

private theorem cltdec_Xo_meas {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Fin (2 * p) → Z2 L) (m : Fin (2 * p)) :
    Measurable (cltXo F E u b m) := by
  have h1 := (cltdec_Y_meas F hz (b m)).sub_const (∫ ω', cltYo F E u ω' (b m) ∂(P L W))
  by_cases hm : (m : ℕ) < p
  · have h : cltXo F E u b m =
        fun ω => cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W) := by
      funext ω; simp only [cltXo, hm, ↓reduceIte]
    rw [h]; exact h1
  · have h : cltXo F E u b m =
        fun ω => (starRingEnd ℂ) (cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W)) := by
      funext ω; simp only [cltXo, hm, ↓reduceIte]
    rw [h]; exact Complex.continuous_conj.measurable.comp h1

private theorem cltdec_Gamma_meas {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) (b : Fin (2 * p) → Z2 L) (i : Fin (2 * p)) :
    Measurable (cltGamma F E u b i) := by
  have h : cltGamma F E u b i = fun ω => ∏ m ∈ Finset.univ.erase i, cltXo F E u b m ω := rfl
  rw [h]
  exact Finset.measurable_prod _ fun m _ => cltdec_Xo_meas F hz b m

private theorem cltdec_Xo_le {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ)
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

private theorem cltdec_Gamma_le {p : ℕ} (F : LocalForm L W 1 K) (E u : ℝ)
    (b : Fin (2 * p) → Z2 L) {X : ℝ} (hX1 : 1 ≤ X) (hX : ∀ m ω, ‖cltXo F E u b m ω‖ ≤ X)
    (i : Fin (2 * p)) (ω : Ω L W) : ‖cltGamma F E u b i ω‖ ≤ X ^ (2 * p) := by
  unfold cltGamma
  rw [norm_prod]
  calc ∏ m ∈ Finset.univ.erase i, ‖cltXo F E u b m ω‖ ≤ ∏ _m ∈ Finset.univ.erase i, X :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => hX m ω
    _ = X ^ (Finset.univ.erase i).card := Finset.prod_const X
    _ ≤ X ^ (2 * p) := pow_le_pow_right₀ hX1 (Finset.card_erase_le.trans (by simp))

/-- `X_m` is centred under `P L W`: `∫ X_m dP = 0`. -/
private theorem cltdec_Xo_integral {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) {BY : ℝ} (hY : ∀ ω b', ‖cltYo F E u ω b'‖ ≤ BY)
    (b : Fin (2 * p) → Z2 L) (m : Fin (2 * p)) :
    ∫ ω, cltXo F E u b m ω ∂(P L W) = 0 := by
  have hint : Integrable (fun ω => cltYo F E u ω (b m)) (P L W) :=
    Integrable.of_bound (cltdec_Y_meas F hz (b m)).aestronglyMeasurable BY
      (Filter.Eventually.of_forall fun ω => hY ω (b m))
  have h0 : ∫ ω, (cltYo F E u ω (b m) - ∫ ω', cltYo F E u ω' (b m) ∂(P L W)) ∂(P L W) = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  by_cases hm : (m : ℕ) < p
  · simp only [cltXo, hm, ↓reduceIte]
    exact h0
  · simp only [cltXo, hm, ↓reduceIte]
    rw [integral_conj, h0]
    simp

/-- The finite-model core of the assembly: if every step of the telescoping has `‖·‖ ≤ η`, then
`‖∫ ∏_m X_m dP‖ ≤ card (Coord) · η`. -/
private theorem cltdec_core {p : ℕ} (F : LocalForm L W 1 K) {E u : ℝ}
    (hz : (spectralZ E u).im ≠ 0) {BY : ℝ} (hY : ∀ ω b', ‖cltYo F E u ω b'‖ ≤ BY)
    (b : Fin (2 * p) → Z2 L) (i : Fin (2 * p))
    (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) {η : ℝ}
    (hstep : ∀ k : ℕ, k < Fintype.card (Coord L W) →
      ‖∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W))‖ ≤ η) :
    ‖∫ ω, ∏ m : Fin (2 * p), cltXo F E u b m ω ∂(P L W)‖ ≤ Fintype.card (Coord L W) * η := by
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = max (2 * BY) 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX : ∀ m ω, ‖cltXo F E u b m ω‖ ≤ X := fun m ω => by
    rw [hXdef]; exact (cltdec_Xo_le F E u b hY m ω).trans (le_max_left _ _)
  have hG : ∀ ω, ‖cltGamma F E u b i ω‖ ≤ X ^ (2 * p) := cltdec_Gamma_le F E u b hX1 hX i
  have hXm : Measurable (cltXo F E u b i) := cltdec_Xo_meas F hz b i
  have hGm : Measurable (cltGamma F E u b i) := cltdec_Gamma_meas F hz b i
  have hX0 : 0 ≤ X := by linarith
  -- integrability of the difference integrands
  have hdiffInt : ∀ f g : Ω L W × Ω L W → Ω L W, Measurable f → Measurable g →
      Integrable (fun q : Ω L W × Ω L W =>
        (cltXo F E u b i (f q) - cltXo F E u b i (g q)) * cltGamma F E u b i q.1)
        ((P L W).prod (P L W)) := by
    intro f g hf hg
    refine Integrable.of_bound (C := (X + X) * X ^ (2 * p)) ?_ ?_
    · exact (((hXm.comp hf).sub (hXm.comp hg)).mul (hGm.comp measurable_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_mul]
      exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hX _ _) (hX _ _))) (hG _)
        (norm_nonneg _) (by linarith)
  have hTm : ∀ k : ℕ, Measurable fun q : Ω L W × Ω L W => cltHyb L W e k q.1 q.2 := fun k =>
    (measurePreserving_cltSplit L W (cltHybSet L W e k)).measurable
  have hi1 := hdiffInt Prod.fst Prod.snd measurable_fst measurable_snd
  have hi2 : Integrable (fun q : Ω L W × Ω L W =>
      cltGamma F E u b i q.1 * cltXo F E u b i q.2) ((P L W).prod (P L W)) := by
    refine Integrable.of_bound (C := X ^ (2 * p) * X) ?_ ?_
    · exact ((hGm.comp measurable_fst).mul (hXm.comp measurable_snd)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_mul]
      exact mul_le_mul (hG _) (hX _ _) (norm_nonneg _) (by positivity)
  -- factor `∏ X_m = X_i Γ_i`
  have hfac : ∀ ω, ∏ m : Fin (2 * p), cltXo F E u b m ω =
      cltXo F E u b i ω * cltGamma F E u b i ω := fun ω =>
    (Finset.mul_prod_erase Finset.univ (fun m => cltXo F E u b m ω) (Finset.mem_univ i)).symm
  -- transfer to the product space
  have h1 : ∫ ω, ∏ m : Fin (2 * p), cltXo F E u b m ω ∂(P L W) =
      ∫ q, cltXo F E u b i q.1 * cltGamma F E u b i q.1 ∂((P L W).prod (P L W)) := by
    have := integral_fun_fst (μ := P L W) (ν := P L W)
      (fun ω => cltXo F E u b i ω * cltGamma F E u b i ω)
    simp only [probReal_univ, one_smul] at this
    rw [this]
    exact integral_congr_ae (Filter.Eventually.of_forall hfac)
  -- the centred term vanishes
  have h0 : ∫ q, cltGamma F E u b i q.1 * cltXo F E u b i q.2 ∂((P L W).prod (P L W)) = 0 := by
    have := integral_prod_mul (μ := P L W) (ν := P L W) (cltGamma F E u b i) (cltXo F E u b i)
    rw [this, cltdec_Xo_integral F hz hY b i, mul_zero]
  have h2 : ∫ q, cltXo F E u b i q.1 * cltGamma F E u b i q.1 ∂((P L W).prod (P L W)) =
      ∫ q, (cltXo F E u b i q.1 - cltXo F E u b i q.2) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W)) := by
    have h3 : ∫ q, cltXo F E u b i q.1 * cltGamma F E u b i q.1 ∂((P L W).prod (P L W)) =
        ∫ q, (cltXo F E u b i q.1 - cltXo F E u b i q.2) * cltGamma F E u b i q.1
          ∂((P L W).prod (P L W)) +
        ∫ q, cltGamma F E u b i q.1 * cltXo F E u b i q.2 ∂((P L W).prod (P L W)) := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only
      ring
    rw [h3, h0, add_zero]
  -- telescoping
  have h4 : ∫ q, (cltXo F E u b i q.1 - cltXo F E u b i q.2) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W)) =
      ∑ k ∈ Finset.range (Fintype.card (Coord L W)),
        ∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W)) := by
    rw [← integral_finsetSum _ fun k _ => hdiffInt _ _ (hTm k) (hTm (k + 1))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only
    rw [← Finset.sum_mul, ← cltTelescope L W e (cltXo F E u b i) q.1 q.2]
  rw [h1, h2, h4]
  calc ‖∑ k ∈ Finset.range (Fintype.card (Coord L W)),
        ∫ q, (cltXo F E u b i (cltHyb L W e k q.1 q.2) -
          cltXo F E u b i (cltHyb L W e (k + 1) q.1 q.2)) * cltGamma F E u b i q.1
        ∂((P L W).prod (P L W))‖
      ≤ ∑ k ∈ Finset.range (Fintype.card (Coord L W)), η :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk =>
          hstep k (Finset.mem_range.mp hk))
    _ = Fintype.card (Coord L W) * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Helpers

/-- `c_κ > 0` for `0 < κ`, `|E| ≤ 2 - κ` (a re-proof of the private `cltres_ck_pos` of
`RBM2D/Evolution/CltResolvent.lean`). -/
private theorem cltdec_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltCk κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltCk
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- The exponent bound: `2 N² · N^{-D-3} ≤ W^{-D}` for `N ≥ 2`, `0 < W ≤ N`, `D > 0`. -/
private theorem cltdec_exponent {N Wn D : ℝ} (hN2 : 2 ≤ N) (hW : 0 < Wn) (hWN : Wn ≤ N)
    (hD : 0 < D) : 2 * N ^ 2 * N ^ (-D - 3) ≤ Wn ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have e1 : 2 * N ^ 2 * N ^ (-D - 3) = 2 * N ^ (-D - 1) := by
    have h : N ^ 2 = N ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast N 2).symm
    rw [h, mul_assoc, ← Real.rpow_add hN0]
    congr 2
    push_cast
    ring
  have e2 : N ^ (-D) = N ^ (-D - 1) * N := by
    rw [← Real.rpow_add_one hN0.ne']
    congr 1
    ring
  have hpos : 0 < N ^ (-D - 1) := Real.rpow_pos_of_pos hN0 _
  calc 2 * N ^ 2 * N ^ (-D - 3) = 2 * N ^ (-D - 1) := e1
    _ ≤ N ^ (-D - 1) * N := by nlinarith
    _ = N ^ (-D) := e2.symm
    _ ≤ Wn ^ (-D) := Real.rpow_le_rpow_of_nonpos hW hWN (by linarith)

/-! ## The statements -/

section Assembly

variable (d : Sizes)

/-- The number of real coordinates: `card (Coord (d.L n) (d.W n)) = 2 N²`
. -/
private theorem cltdec_card_coord (n : ℕ) :
    (Fintype.card (Coord (d.L n) (d.W n)) : ℝ) = 2 * ((d.size n : ℕ) : ℝ) ^ 2 := by
  have h : Fintype.card (Coord (d.L n) (d.W n)) =
      Fintype.card (Idx (d.L n) (d.W n)) * (Fintype.card (Idx (d.L n) (d.W n)) * 2) := by
    simp [Coord, Fintype.card_prod, Fintype.card_bool]
  rw [h]
  push_cast
  have h2 : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
    simp [Idx, Z2, ZMod.card, Sizes.size, sq]
  rw [h2]; ring

/-- **`CltFarThm`** (`clt-lemmafar`; the final assembly).  Under `H_clt` and the
coefficient and locality bounds, `CltFar d F E u τ` holds.  It gives `cltCase1_of_far`,
`cltCase2_of_far` (through `cltCase1Prec_of_farThm`, `cltCase2Prec_of_farThm` below). -/
def CltFarThm (κ 𝔠 δ : ℝ) : Prop :=
  ∀ (K : ℕ) (C' τ : ℝ) (E s₀ t₀ u t : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K),
    HClt d κ 𝔠 δ E s₀ t₀ u t → 0 ≤ C' → 0 < τ →
    (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
    (∀ n, (F n).Local τ (u n)) →
    CltFar d F E u τ

/-- **Case 1** (`clt-lemma-final-result`): `CltFarThm` and the
`cltCase1_of_far` at `C = 4` give `CltCase1Prec d κ 𝔠 δ 4`. -/
theorem cltCase1Prec_of_farThm (κ 𝔠 δ : ℝ) (h : CltFarThm d κ 𝔠 δ) :
    CltCase1Prec d κ 𝔠 δ 4 := by
  intro hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE hs₀ hsu hut₀ hut ht hN hW hR hLoc
    hDec hV3 hcoef hloc hΛ hZ
  exact cltCase1_of_far d κ 𝔠 δ 4 le_rfl hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE hs₀
    hsu hut₀ hut ht hN hW hR
    (h K C' τ E s₀ t₀ u t F
      ⟨hκ, h𝔠, hδ, hE, hs₀, hsu, hut₀, hut, ht, hN, hW, hR, hLoc, hDec, hV3⟩ hC' hτ hcoef hloc)
    hcoef hloc hΛ hZ

/-- **Case 2** (`clt-lemma-final-result2`): `CltFarThm` and the
`cltCase2_of_far` at `C = 4` give `CltCase2Prec d κ 𝔠 δ 4`. -/
theorem cltCase2Prec_of_farThm (κ 𝔠 δ : ℝ) (h : CltFarThm d κ 𝔠 δ) :
    CltCase2Prec d κ 𝔠 δ 4 := by
  intro hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE hs₀ hsu hut₀ hut ht hN hW hR hLoc
    hDec hV3 hcoef hloc hΛ hZ
  exact cltCase2_of_far d κ 𝔠 δ 4 (by norm_num) hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE
    hs₀ hsu hut₀ hut ht hN hW hR
    (h K C' τ E s₀ t₀ u t F
      ⟨hκ, h𝔠, hδ, hE, hs₀, hsu, hut₀, hut, ht, hN, hW, hR, hLoc, hDec, hV3⟩ hC' hτ hcoef hloc)
    hcoef hloc hΛ hZ

/-- **`CltFarThm`** (`clt-lemmafar`).  The step bound
`cltStep` is used at the same `p` and `D`; the `2 N²` steps give `2 N^{-D-1} ≤ N^{-D} ≤ W^{-D}`
for `N ≥ 2` and `W ≤ N`. -/
theorem cltFar (κ 𝔠 δ : ℝ) : CltFarThm d κ 𝔠 δ := by
  intro K C' τ E s₀ t₀ u t F hH hC' hτ hcoef hloc
  obtain ⟨hκ, h𝔠, hδ, hE, hs0, hs0u, -, hut, ht1, hN, hBW, hRange, -, -, -⟩ := id hH
  intro p hp D hD
  filter_upwards [cltStep d κ 𝔠 δ K C' τ E s₀ t₀ u t F hH hC' hτ hcoef hloc p hp D hD,
    hRange, hN.eventually_ge_atTop 2] with n hStep hRn hN2
  rintro b ⟨i, hiso⟩
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hu0 : 0 ≤ u n := (hs0 n).trans (hs0u n)
  have hR : N ^ (-1 + δ) ≤ 1 - u n := by have := hut n; linarith [hRn]
  have hηlow := cltEta_lower (d.L n) (d.W n) κ δ (E n) (u n) hκ hδ (hE n) hR
  have hz : (spectralZ (E n) (u n)).im ≠ 0 := by
    have hck : 0 < cltCk κ := cltdec_ck_pos hκ (hE 0)
    have h0 : 0 < cltCk κ / N := div_pos hck hN0
    exact (lt_of_lt_of_le h0 hηlow).ne'
  have hYn : ∀ (ω : Ω (d.L n) (d.W n)) (b' : Z2 (d.L n)),
      ‖cltYo (F n) (E n) (u n) ω b'‖ ≤ (K + 1) * N ^ C' * (2 * N ^ 3 / cltCk κ) ^ K := by
    intro ω b'
    have := cltEval_det_le (d.L n) (d.W n) κ δ (E n) (u n) K (F n) C'
      (Hflow (d.L n) (d.W n) (u n) ω) b' hκ hδ (hE n) hR (hcoef n)
      (Hflow_isHermitian _ _ _ _)
    exact this
  -- the transfer from `Sizes.seqP d` to the finite model
  have hprodm : Measurable fun η : Ω (d.L n) (d.W n) =>
      ∏ m : Fin (2 * p), cltXo (F n) (E n) (u n) b m η :=
    Finset.measurable_prod _ fun m _ => cltdec_Xo_meas (F n) hz b m
  have htr := cltTransfer d n (fun η => ∏ m : Fin (2 * p), cltXo (F n) (E n) (u n) b m η) hprodm
  have hinner : ∀ m : Fin (2 * p),
      ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') (b m) ∂(Sizes.seqP d) =
        ∫ η, cltYo (F n) (E n) (u n) η (b m) ∂(P (d.L n) (d.W n)) := fun m =>
    cltTransfer d n (fun η => cltYo (F n) (E n) (u n) η (b m)) (cltdec_Y_meas (F n) hz (b m))
  have hEq : ∫ ω, ∏ k : Fin (2 * p),
        (if (k : ℕ) < p
          then cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (b k) -
            ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') (b k) ∂(Sizes.seqP d)
          else (starRingEnd ℂ) (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (b k) -
            ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') (b k) ∂(Sizes.seqP d)))
        ∂(Sizes.seqP d) =
      ∫ η, ∏ m : Fin (2 * p), cltXo (F n) (E n) (u n) b m η ∂(P (d.L n) (d.W n)) := by
    rw [← htr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [cltXo, hinner m]
    rfl
  rw [hEq]
  have hcore := cltdec_core (F n) hz hYn b i (Fintype.equivFin (Coord (d.L n) (d.W n)))
    (η := N ^ (-D - 3)) (fun k hk => by
      have := hStep b i hiso (Fintype.equivFin (Coord (d.L n) (d.W n))) k hk
      exact this)
  refine hcore.trans ?_
  rw [cltdec_card_coord d n]
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have hWN : (d.W n : ℝ) ≤ N := by
    have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
    have h1 : d.W n ≤ d.size n := by
      unfold Sizes.size
      calc d.W n = d.W n * 1 := (mul_one _).symm
        _ ≤ d.W n * d.L n := Nat.mul_le_mul_left _ hL1
        _ ≤ (d.W n * d.L n) * (d.W n * d.L n) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (d.W_pos n) (by omega))
        _ = (d.W n * d.L n) ^ 2 := (sq _).symm
    exact (Nat.cast_le (α := ℝ)).mpr h1
  exact cltdec_exponent hN2 hW0 hWN hD

/-- **Case 1 of the CLT estimate** (`clt-lemma-final-result`) at the constant `C = 4`:
`CltCase1Prec d κ 𝔠 δ 4`, unconditionally. -/
theorem cltCase1Prec (κ 𝔠 δ : ℝ) : CltCase1Prec d κ 𝔠 δ 4 :=
  cltCase1Prec_of_farThm d κ 𝔠 δ (cltFar d κ 𝔠 δ)

/-- **Case 2 of the CLT estimate** (`clt-lemma-final-result2`) at the constant `C = 4`:
`CltCase2Prec d κ 𝔠 δ 4`, unconditionally. -/
theorem cltCase2Prec (κ 𝔠 δ : ℝ) : CltCase2Prec d κ 𝔠 δ 4 :=
  cltCase2Prec_of_farThm d κ 𝔠 δ (cltFar d κ 𝔠 δ)

end Assembly

end RBM.Evol
