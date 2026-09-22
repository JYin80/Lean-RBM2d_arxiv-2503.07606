/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasWeightedInverse

/-!
# Entrywise decay from the weighted inverse

Centering the exponential weight at the column index turns the weighted
inverse norm into decay in the periodic graph distance. The spectral gate is
kept explicit.
-/

namespace RBM

open Matrix Finset
open scoped NNReal Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

private theorem matrix_entry_norm_le (M : Matrix (Z2 L) (Z2 L) ℂ)
    (a b : Z2 L) : ‖M a b‖ ≤ ‖M‖ := by
  have hrow : ‖M a b‖₊ ≤ ∑ j : Z2 L, ‖M a j‖₊ :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Z2 L => ‖M a j‖₊)
      (fun _ _ => by positivity) (Finset.mem_univ b)
  have hsup : (∑ j : Z2 L, ‖M a j‖₊) ≤
      (Finset.univ : Finset (Z2 L)).sup (fun i => ∑ j : Z2 L, ‖M i j‖₊) :=
    Finset.le_sup (s := Finset.univ) (f := fun i : Z2 L => ∑ j : Z2 L, ‖M i j‖₊)
      (Finset.mem_univ a)
  have hnn : ‖M a b‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact hrow.trans hsup
  exact NNReal.coe_le_coe.mpr hnn

/-- Combes–Thomas kernel estimate under the explicit weighted Neumann gate. -/
theorem norm_Theta_apply_le_exp_zdist2 (hL : 3 ≤ L)
    {ξ : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hsmall : ‖ξ‖ * Real.exp t < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      Real.exp (-(t * (zdist2 L (a - b) : ℝ))) *
        (1 - ‖ξ‖ * Real.exp t)⁻¹ := by
  let w := blockExponentialWeight L b t
  let M := blockWeightMatrix L w * Theta L ξ * blockWeightInverse L w
  let r : ℝ := t * (zdist2 L (a - b) : ℝ)
  have hM : ‖M‖ ≤ (1 - ‖ξ‖ * Real.exp t)⁻¹ :=
    norm_exponentialConjugatedTheta_le L hL b ht hsmall
  have hentry : M a b = (Real.exp r : ℂ) * Theta L ξ a b := by
    simp [M, blockWeightMatrix, blockWeightInverse, Matrix.diagonal_mul,
      Matrix.mul_diagonal, w, blockExponentialWeight, r, mul_assoc]
  have hbound : Real.exp r * ‖Theta L ξ a b‖ ≤
      (1 - ‖ξ‖ * Real.exp t)⁻¹ := by
    have h := (matrix_entry_norm_le L M a b).trans hM
    rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos r)] at h
    exact h
  have hdiv : ‖Theta L ξ a b‖ ≤
      (1 - ‖ξ‖ * Real.exp t)⁻¹ / Real.exp r := by
    apply (le_div_iff₀ (Real.exp_pos r)).mpr
    nlinarith [hbound]
  calc
    ‖Theta L ξ a b‖ ≤ (1 - ‖ξ‖ * Real.exp t)⁻¹ / Real.exp r := hdiv
    _ = Real.exp (-r) * (1 - ‖ξ‖ * Real.exp t)⁻¹ := by
      rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
    _ = Real.exp (-(t * (zdist2 L (a - b) : ℝ))) *
          (1 - ‖ξ‖ * Real.exp t)⁻¹ := rfl

/-- A nonzero spectral parameter and positive decay exponent on a finite torus. -/
example (a b : Z2 3) :
    ‖Theta 3 ((1 / 4 : ℝ) : ℂ) a b‖ ≤
      Real.exp (-(Real.log 2 * (zdist2 3 (a - b) : ℝ))) *
        (1 - ‖((1 / 4 : ℝ) : ℂ)‖ * Real.exp (Real.log 2))⁻¹ := by
  apply norm_Theta_apply_le_exp_zdist2 3 (by norm_num)
  · positivity
  · norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end RBM
