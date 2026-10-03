/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import RBM2D.Path.Step2Props
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Loop.Kcal

/-!
# Lipschitz dependence of the resolvent on the matrix

For Hermitian `M₁, M₂` on any finite index type and a fixed non-real spectral parameter `z`,
`norm_green_sub_le_of_herm` bounds the resolvent difference,
`‖G(M₁, z) - G(M₂, z)‖ ≤ |Im z|⁻² ‖M₁ - M₂‖`, by the resolvent identity and the whole-space
envelope `‖G‖ ≤ |Im z|⁻¹` (`norm_green_le`).
-/

namespace RBM.Path

open Finset Matrix RBM RBM.Gauss
open scoped Matrix.Norms.L2Operator

/-! ### The resolvent difference at a fixed spectral parameter -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent-difference bound.**  For Hermitian `M₁, M₂` and `z.im ≠ 0`,
`‖G(M₁, z) - G(M₂, z)‖ ≤ |z.im|⁻¹² ‖M₁ - M₂‖`. -/
theorem norm_green_sub_le_of_herm {M₁ M₂ : Matrix n n ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by
  have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hg1 : ‖green M₁ z‖ ≤ |z.im|⁻¹ := norm_green_le hM₁ hzpos le_rfl
  have hg2 : ‖green M₂ z‖ ≤ |z.im|⁻¹ := norm_green_le hM₂ hzpos le_rfl
  have hu1 := isUnit_sub_smul_one_of_im_ne_zero hM₁ hz
  have hu2 := isUnit_sub_smul_one_of_im_ne_zero hM₂ hz
  have hd1 : IsUnit (M₁ - z • (1 : Matrix n n ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu1
  have hd2 : IsUnit (M₂ - z • (1 : Matrix n n ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu2
  have hid : green M₁ z - green M₂ z = green M₁ z * (M₂ - M₁) * green M₂ z := by
    have hsub : M₂ - M₁ = (M₂ - z • (1 : Matrix n n ℂ)) - (M₁ - z • (1 : Matrix n n ℂ)) := by
      abel
    have h1 : green M₁ z * (M₂ - z • (1 : Matrix n n ℂ)) * green M₂ z = green M₁ z := by
      rw [green, green, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.mul_one]
    have h2 : green M₁ z * (M₁ - z • (1 : Matrix n n ℂ)) * green M₂ z = green M₂ z := by
      rw [green, green, Matrix.nonsing_inv_mul _ hd1, Matrix.one_mul]
    rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h1, h2]
  rw [hid]
  calc ‖green M₁ z * (M₂ - M₁) * green M₂ z‖
      ≤ ‖green M₁ z‖ * ‖M₂ - M₁‖ * ‖green M₂ z‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ |z.im|⁻¹ * ‖M₁ - M₂‖ * |z.im|⁻¹ := by
        rw [norm_sub_rev M₂ M₁]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)) hg2 (norm_nonneg _)
          (by positivity)
    _ = |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by ring


end Resolvent

end RBM.Path
