/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasConjugation

/-!
# Perturbation after diagonal-weight conjugation

The entrywise perturbation is an exact edge multiplier. A uniform ratio
bound on the support of the block walk controls every row sum and its
`ℓ∞` operator norm.
-/

namespace RBM

open Matrix Finset
open scoped NNReal Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- Exact entry formula for the perturbation of the two-dimensional walk. -/
theorem blockWeight_SB_sub_apply (w : Z2 L → ℂ) (a b : Z2 L) :
    (blockWeightMatrix L w * SB L * blockWeightInverse L w - SB L) a b =
      (w a * (w b)⁻¹ - 1) * SB L a b := by
  rw [Matrix.sub_apply, blockWeight_SB_apply]
  ring

/-- The edge ratio bound yields a row-sum perturbation bound. -/
theorem sum_nnnorm_blockWeight_SB_sub_le (hL : 3 ≤ L)
    (w : Z2 L → ℂ) (δ : ℝ≥0)
    (hδ : ∀ a b : Z2 L, SB L a b ≠ 0 →
      ‖w a * (w b)⁻¹ - 1‖₊ ≤ δ) (a : Z2 L) :
    ∑ b : Z2 L,
      ‖(blockWeightMatrix L w * SB L * blockWeightInverse L w - SB L) a b‖₊
        ≤ δ := by
  have hterm (b : Z2 L) :
      ‖(blockWeightMatrix L w * SB L * blockWeightInverse L w - SB L) a b‖₊
        ≤ δ * ‖SB L a b‖₊ := by
    rw [blockWeight_SB_sub_apply, nnnorm_mul]
    by_cases hb : SB L a b = 0
    · simp [hb]
    · exact mul_le_mul_of_nonneg_right (hδ a b hb) (by positivity)
  calc
    _ ≤ ∑ b : Z2 L, δ * ‖SB L a b‖₊ := Finset.sum_le_sum fun b _ => hterm b
    _ = δ * ∑ b : Z2 L, ‖SB L a b‖₊ := by rw [Finset.mul_sum]
    _ = δ := by rw [sum_nnnorm_SB_row L hL]; simp

/-- The same edge assumption controls the actual matrix `ℓ∞` operator norm. -/
theorem nnnorm_blockWeight_SB_sub_le (hL : 3 ≤ L)
    (w : Z2 L → ℂ) (δ : ℝ≥0)
    (hδ : ∀ a b : Z2 L, SB L a b ≠ 0 →
      ‖w a * (w b)⁻¹ - 1‖₊ ≤ δ) :
    ‖blockWeightMatrix L w * SB L * blockWeightInverse L w - SB L‖₊ ≤ δ := by
  rw [Matrix.linfty_opNNNorm_def]
  exact Finset.sup_le fun a _ => sum_nnnorm_blockWeight_SB_sub_le L hL w δ hδ a

/-- A nonconstant positive weight on a concrete three-by-three torus. -/
private def perturbationProbeWeight (a : Z2 3) : ℂ :=
  if a = (0, 0) then 2 else 1

private theorem perturbationProbeWeight_ratio (a b : Z2 3) :
    ‖perturbationProbeWeight a * (perturbationProbeWeight b)⁻¹ - 1‖₊ ≤ 1 := by
  by_cases ha : a = (0, 0) <;> by_cases hb : b = (0, 0) <;>
    simp [perturbationProbeWeight, ha, hb] <;> norm_num

example :
    ‖blockWeightMatrix 3 perturbationProbeWeight * SB 3 *
      blockWeightInverse 3 perturbationProbeWeight - SB 3‖₊ ≤ 1 := by
  exact nnnorm_blockWeight_SB_sub_le 3 (by norm_num) perturbationProbeWeight 1
    (fun a b _ => perturbationProbeWeight_ratio a b)

end RBM
