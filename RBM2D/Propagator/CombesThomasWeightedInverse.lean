/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasExponentialWeight

/-!
# Inverse of the exponentially weighted block-walk denominator

The explicit smallness gate `‖ξ‖ exp t < 1` gives an inverse bound for the
conjugated denominator. No kernel decay estimate is asserted here.
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- The block walk conjugated by the exponential distance weight. -/
noncomputable def exponentialConjugatedSB (c : Z2 L) (t : ℝ) :
    Matrix (Z2 L) (Z2 L) ℂ :=
  blockWeightMatrix L (blockExponentialWeight L c t) * SB L *
    blockWeightInverse L (blockExponentialWeight L c t)

/-- The weighted walk's operator norm is at most `exp t`. -/
theorem norm_exponentialConjugatedSB_le (hL : 3 ≤ L) (c : Z2 L)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exponentialConjugatedSB L c t‖ ≤ Real.exp t := by
  have hδ : 0 ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hpert : ‖exponentialConjugatedSB L c t - SB L‖ ≤ Real.exp t - 1 := by
    have h := nnnorm_blockExponentialWeight_SB_sub_le L hL c ht
    apply (NNReal.coe_le_coe.mpr h).trans_eq ?_
    exact Real.coe_toNNReal _ hδ
  calc
    ‖exponentialConjugatedSB L c t‖ =
        ‖(exponentialConjugatedSB L c t - SB L) + SB L‖ := by congr 1; abel
    _ ≤ ‖exponentialConjugatedSB L c t - SB L‖ + ‖SB L‖ := norm_add_le _ _
    _ ≤ (Real.exp t - 1) + 1 := add_le_add hpert (le_of_eq (norm_SB L hL))
    _ = Real.exp t := by ring

/-- The norm of the weighted interaction obeys the same explicit gate. -/
theorem norm_smul_exponentialConjugatedSB_le (hL : 3 ≤ L) (c : Z2 L)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℂ) :
    ‖ξ • exponentialConjugatedSB L c t‖ ≤ ‖ξ‖ * Real.exp t := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_exponentialConjugatedSB_le L hL c ht) (norm_nonneg _)

/-- The explicitly weighted denominator is invertible when `‖ξ‖ exp t < 1`. -/
theorem isUnit_one_sub_smul_exponentialConjugatedSB (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) {ξ : ℂ}
    (hsmall : ‖ξ‖ * Real.exp t < 1) :
    IsUnit (1 - ξ • exponentialConjugatedSB L c t) := by
  have hnorm : ‖ξ • exponentialConjugatedSB L c t‖ < 1 :=
    lt_of_le_of_lt (norm_smul_exponentialConjugatedSB_le L hL c ht ξ) hsmall
  exact ⟨Units.oneSub _ hnorm, Units.val_oneSub _ _⟩

/-- Quantitative inverse bound under the explicit weighted smallness gate. -/
theorem norm_inverse_one_sub_smul_exponentialConjugatedSB_le (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) {ξ : ℂ}
    (hsmall : ‖ξ‖ * Real.exp t < 1) :
    ‖Ring.inverse (1 - ξ • exponentialConjugatedSB L c t)‖ ≤
      (1 - ‖ξ‖ * Real.exp t)⁻¹ := by
  let X := ξ • exponentialConjugatedSB L c t
  let B := Ring.inverse (1 - X)
  have hunit : IsUnit (1 - X) :=
    isUnit_one_sub_smul_exponentialConjugatedSB L hL c ht hsmall
  have hmul : B * (1 - X) = 1 := Ring.inverse_mul_cancel _ hunit
  have hB : B = 1 + B * X := by
    calc
      B = B * (1 - X) + B * X := by noncomm_ring
      _ = 1 + B * X := by rw [hmul]
  have hX : ‖X‖ ≤ ‖ξ‖ * Real.exp t :=
    norm_smul_exponentialConjugatedSB_le L hL c ht ξ
  have hbound : ‖B‖ ≤ 1 + ‖B‖ * ‖X‖ := by
    calc
      ‖B‖ = ‖1 + B * X‖ := congrArg norm hB
      _ ≤ ‖(1 : Matrix (Z2 L) (Z2 L) ℂ)‖ + ‖B * X‖ := norm_add_le _ _
      _ ≤ 1 + ‖B‖ * ‖X‖ := by
        rw [norm_one]
        simpa only [add_comm] using add_le_add_right (norm_mul_le B X) 1
  have hqpos : 0 < 1 - ‖ξ‖ * Real.exp t := by linarith
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hqpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hX (norm_nonneg B)]

/-- The weighted inverse is exactly the diagonal conjugate of the original propagator. -/
theorem exponentialConjugatedTheta_eq_inverse (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) {ξ : ℂ}
    (hsmall : ‖ξ‖ * Real.exp t < 1) :
    blockWeightMatrix L (blockExponentialWeight L c t) * Theta L ξ *
        blockWeightInverse L (blockExponentialWeight L c t) =
      Ring.inverse (1 - ξ • exponentialConjugatedSB L c t) := by
  let D := blockWeightMatrix L (blockExponentialWeight L c t)
  let Di := blockWeightInverse L (blockExponentialWeight L c t)
  let P := 1 - ξ • SB L
  let Q := 1 - ξ • exponentialConjugatedSB L c t
  have hw : ∀ a, blockExponentialWeight L c t a ≠ 0 :=
    blockExponentialWeight_ne_zero L c t
  have hDDi : D * Di = 1 := blockWeight_mul_inverse L _ hw
  have hDiD : Di * D = 1 := blockWeight_inverse_mul L _ hw
  have hξ : ‖ξ‖ < 1 := by
    have he : 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    nlinarith [mul_nonneg (norm_nonneg ξ) (sub_nonneg.mpr he)]
  have hTheta : Theta L ξ * P = 1 := Theta_mul L hL hξ
  have hQ : D * P * Di = Q := blockWeight_one_sub_smul_SB L _ hw ξ
  have hunit : IsUnit Q :=
    isUnit_one_sub_smul_exponentialConjugatedSB L hL c ht hsmall
  have hright : (D * Theta L ξ * Di) * Q = 1 := by
    rw [← hQ]
    calc
      (D * Theta L ξ * Di) * (D * P * Di) =
          D * Theta L ξ * (Di * D) * P * Di := by noncomm_ring
      _ = D * Theta L ξ * P * Di := by rw [hDiD]; simp
      _ = D * Di := by rw [mul_assoc D (Theta L ξ) P, hTheta, mul_one]
      _ = 1 := hDDi
  calc
    D * Theta L ξ * Di =
        (D * Theta L ξ * Di) * (Q * Ring.inverse Q) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
    _ = ((D * Theta L ξ * Di) * Q) * Ring.inverse Q := by simp only [mul_assoc]
    _ = Ring.inverse Q := by rw [hright, one_mul]

/-- The quantitative bound applies to the conjugated original propagator. -/
theorem norm_exponentialConjugatedTheta_le (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) {ξ : ℂ}
    (hsmall : ‖ξ‖ * Real.exp t < 1) :
    ‖blockWeightMatrix L (blockExponentialWeight L c t) * Theta L ξ *
      blockWeightInverse L (blockExponentialWeight L c t)‖ ≤
        (1 - ‖ξ‖ * Real.exp t)⁻¹ := by
  rw [exponentialConjugatedTheta_eq_inverse L hL c ht hsmall]
  exact norm_inverse_one_sub_smul_exponentialConjugatedSB_le L hL c ht hsmall

end RBM
