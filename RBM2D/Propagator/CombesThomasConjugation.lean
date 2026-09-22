/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Basic

/-!
# Diagonal-weight conjugation of the finite block walk

This is the algebraic setup for a Combes–Thomas estimate. It identifies the
weighted entries of the actual two-dimensional block walk `SB`; no decay
estimate is claimed here.
-/

namespace RBM

open Matrix

variable (L : ℕ) [NeZero L]

/-- Diagonal matrix of a complex weight on the block torus. -/
noncomputable def blockWeightMatrix (w : Z2 L → ℂ) : Matrix (Z2 L) (Z2 L) ℂ :=
  Matrix.diagonal w

/-- Diagonal matrix of reciprocal block weights. -/
noncomputable def blockWeightInverse (w : Z2 L → ℂ) : Matrix (Z2 L) (Z2 L) ℂ :=
  Matrix.diagonal fun a => (w a)⁻¹

/-- Exact entry formula for conjugating the actual two-dimensional block walk. -/
theorem blockWeight_SB_apply (w : Z2 L → ℂ) (a b : Z2 L) :
    (blockWeightMatrix L w * SB L * blockWeightInverse L w) a b =
      w a * SB L a b * (w b)⁻¹ := by
  simp [blockWeightMatrix, blockWeightInverse, Matrix.diagonal_mul,
    Matrix.mul_diagonal, mul_assoc]

/-- Nonvanishing weights make the reciprocal diagonal matrix a right inverse. -/
theorem blockWeight_mul_inverse (w : Z2 L → ℂ)
    (hw : ∀ a, w a ≠ 0) :
    blockWeightMatrix L w * blockWeightInverse L w = 1 := by
  rw [blockWeightMatrix, blockWeightInverse, Matrix.diagonal_mul_diagonal]
  simp [hw]

/-- The reciprocal diagonal matrix is also a left inverse. -/
theorem blockWeight_inverse_mul (w : Z2 L → ℂ)
    (hw : ∀ a, w a ≠ 0) :
    blockWeightInverse L w * blockWeightMatrix L w = 1 := by
  rw [blockWeightMatrix, blockWeightInverse, Matrix.diagonal_mul_diagonal]
  simp [hw]

/-- Conjugation transports the walk resolvent denominator exactly. -/
theorem blockWeight_one_sub_smul_SB (w : Z2 L → ℂ)
    (hw : ∀ a, w a ≠ 0) (ξ : ℂ) :
    blockWeightMatrix L w * (1 - ξ • SB L) * blockWeightInverse L w =
      1 - ξ • (blockWeightMatrix L w * SB L * blockWeightInverse L w) := by
  have hunit := blockWeight_mul_inverse L w hw
  simp only [mul_sub, sub_mul, mul_one, hunit]
  congr 1
  simp only [smul_mul_assoc, mul_smul_comm]

/-- A genuinely nonconstant, everywhere nonzero weight on `Z₃²`. -/
private def probeWeight (a : Z2 3) : ℂ :=
  if a = (0, 0) then 2 else 1

theorem probeWeight_nonconstant : probeWeight (0, 0) ≠ probeWeight (1, 0) := by
  norm_num [probeWeight]

theorem probeWeight_nonzero (a : Z2 3) : probeWeight a ≠ 0 := by
  unfold probeWeight
  split_ifs <;> norm_num

/-- The entry formula applies to the nonconstant concrete weight. -/
example (a b : Z2 3) :
    (blockWeightMatrix 3 probeWeight * SB 3 * blockWeightInverse 3 probeWeight) a b =
      probeWeight a * SB 3 a b * (probeWeight b)⁻¹ :=
  blockWeight_SB_apply 3 probeWeight a b

end RBM
