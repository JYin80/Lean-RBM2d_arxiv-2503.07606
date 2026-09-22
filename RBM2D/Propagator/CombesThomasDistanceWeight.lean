/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.CombesThomasPerturbation
import RBM2D.Defs.Dist

/-!
# A distance weight for the block walk

The positive linear distance weight has an edge ratio bounded by its slope.
This gives a concrete small perturbation of the two-dimensional block walk.
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- Distances to a fixed center change by at most one along an actual walk edge. -/
theorem zdist2_center_edge_le (hL : 3 ≤ L) (c a b : Z2 L)
    (hab : SB L a b ≠ 0) :
    zdist2 L (a - c) ≤ zdist2 L (b - c) + 1 ∧
    zdist2 L (b - c) ≤ zdist2 L (a - c) + 1 := by
  have hsym : SB L b a = SB L a b := by
    calc
      SB L b a = sbKernel L (b - a) := rfl
      _ = sbKernel L (-(a - b)) := by congr 1; abel
      _ = sbKernel L (a - b) := sbKernel_neg L _
      _ = SB L a b := rfl
  have hforward : zdist2 L (a - b) ≤ 1 := by
    by_contra h
    exact hab (SB_apply_eq_zero L hL (by omega))
  have hbackward : zdist2 L (b - a) ≤ 1 := by
    by_contra h
    exact hab (hsym ▸ SB_apply_eq_zero L hL (by omega))
  constructor
  · calc
      zdist2 L (a - c) = zdist2 L ((a - b) + (b - c)) := by congr 1; abel
      _ ≤ zdist2 L (a - b) + zdist2 L (b - c) := zdist2_add_le L _ _
      _ ≤ zdist2 L (b - c) + 1 := by omega
  · calc
      zdist2 L (b - c) = zdist2 L ((b - a) + (a - c)) := by congr 1; abel
      _ ≤ zdist2 L (b - a) + zdist2 L (a - c) := zdist2_add_le L _ _
      _ ≤ zdist2 L (a - c) + 1 := by omega

/-- A positive, distance-based diagonal weight. -/
noncomputable def blockDistanceWeight (c : Z2 L) (t : ℝ) (a : Z2 L) : ℂ :=
  ((1 + t * (zdist2 L (a - c) : ℝ) : ℝ) : ℂ)

omit [NeZero L] in
theorem blockDistanceWeight_ne_zero (c : Z2 L) {t : ℝ} (ht : 0 ≤ t)
    (a : Z2 L) : blockDistanceWeight L c t a ≠ 0 := by
  have hp : 0 < 1 + t * (zdist2 L (a - c) : ℝ) := by positivity
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hp)

private theorem linear_ratio_bound {t x y : ℝ} (ht : 0 ≤ t) (_hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : x ≤ y + 1) (hyx : y ≤ x + 1) :
    |(1 + t * x) / (1 + t * y) - 1| ≤ t := by
  have hden : 0 < 1 + t * y := by positivity
  have hdist : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hquot : (1 + t * x) / (1 + t * y) - 1 =
      (t * (x - y)) / (1 + t * y) := by
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc
    |t * (x - y)| = t * |x - y| := by rw [abs_mul, abs_of_nonneg ht]
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left hdist ht
    _ ≤ t * (1 + t * y) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg ht hy]) ht

/-- The ratio of linear distance weights changes by at most `t` on every edge. -/
theorem blockDistanceWeight_edge_ratio_le (hL : 3 ≤ L) (c a b : Z2 L)
    {t : ℝ} (ht : 0 ≤ t) (hab : SB L a b ≠ 0) :
    ‖blockDistanceWeight L c t a * (blockDistanceWeight L c t b)⁻¹ - 1‖₊
      ≤ Real.toNNReal t := by
  obtain ⟨habd, hbad⟩ := zdist2_center_edge_le L hL c a b hab
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, Real.coe_toNNReal t ht]
  change ‖((1 + t * (zdist2 L (a - c) : ℝ) : ℝ) : ℂ) *
    (((1 + t * (zdist2 L (b - c) : ℝ) : ℝ) : ℂ))⁻¹ - 1‖ ≤ t
  rw [← div_eq_mul_inv, ← Complex.ofReal_div]
  norm_cast
  apply linear_ratio_bound ht (by positivity) (by positivity)
  · exact_mod_cast habd
  · exact_mod_cast hbad

/-- The concrete weight perturbs the walk by at most its slope. -/
theorem nnnorm_blockDistanceWeight_SB_sub_le (hL : 3 ≤ L)
    (c : Z2 L) {t : ℝ} (ht : 0 ≤ t) :
    ‖blockWeightMatrix L (blockDistanceWeight L c t) * SB L *
      blockWeightInverse L (blockDistanceWeight L c t) - SB L‖₊
        ≤ Real.toNNReal t := by
  exact nnnorm_blockWeight_SB_sub_le L hL _ _
    (fun a b hab => blockDistanceWeight_edge_ratio_le L hL c a b ht hab)

end RBM
