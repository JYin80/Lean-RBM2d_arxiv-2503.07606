/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.LatticeCount

/-!
# The mixed lattice sum behind `eq-1sum`

The statement `ExpInvSum` (namespace `RBM.Evol`) and `expInvSum : ExpInvSum`.  Proof:
Cauchy–Schwarz, `RBM.KLoop.sum_exp_le` at `s = 2 / c` and `RBM.KLoop.sum_inv_sq_le`, with
`(z + 1)² ≥ z² + 1`.
-/

namespace RBM.Evol

open Finset

/-- **`ExpInvSum`** (the sum behind `eq-1sum`, against the decay of `Ξ₁`):
`Σ_b e^{-|b-x|_L/c} / (|b-y|_L + 1) ≤ (1 + c) √(5 + 4 log L)` (Cauchy–Schwarz with
`KLoop.sum_exp_le` at `s = 2/c` and `KLoop.sum_inv_sq_le`). -/
def ExpInvSum : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ c : ℝ, 0 < c → ∀ x y : Z2 L,
    ∑ b : Z2 L, Real.exp (-(zdist2 L (b - x) : ℝ) / c) / ((zdist2 L (b - y) : ℝ) + 1) ≤
      (1 + c) * Real.sqrt (5 + 4 * Real.log L)

private theorem latticeSums_zdist_neg {L : ℕ} [NeZero L] (u : ZMod L) :
    zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem latticeSums_zdist2_symm {L : ℕ} [NeZero L] (a b : Z2 L) :
    zdist2 L (a - b) = zdist2 L (b - a) := by
  have : b - a = -(a - b) := (neg_sub a b).symm
  rw [this]
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, latticeSums_zdist_neg]

/-- **`ExpInvSum` holds** (Cauchy–Schwarz with `RBM.KLoop.sum_exp_le` at `s = 2 / c` and
`RBM.KLoop.sum_inv_sq_le`). -/
theorem expInvSum : ExpInvSum := by
  intro L _ hL c hc x y
  have hs : 0 < 2 / c := by positivity
  have h1 := RBM.KLoop.sum_exp_le L (2 / c) hs x
  have h2 := RBM.KLoop.sum_inv_sq_le L hL y
  have hc2 : 2 / (2 / c) = c := by field_simp
  rw [hc2] at h1
  have hA : Real.sqrt (∑ b : Z2 L, (Real.exp (-(zdist2 L (b - x) : ℝ) / c)) ^ 2) ≤ 1 + c := by
    rw [Real.sqrt_le_left (by positivity)]
    refine le_trans (le_of_eq ?_) h1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Real.exp_nat_mul, latticeSums_zdist2_symm x b]
    congr 1
    ring
  have hB : Real.sqrt (∑ b : Z2 L, (((zdist2 L (b - y) : ℝ) + 1)⁻¹) ^ 2)
      ≤ Real.sqrt (5 + 4 * Real.log L) := by
    refine Real.sqrt_le_sqrt (le_trans ?_ h2)
    refine Finset.sum_le_sum fun b _ => ?_
    rw [latticeSums_zdist2_symm y b]
    set z : ℝ := (zdist2 L (b - y) : ℝ) with hz
    have hz0 : 0 ≤ z := by positivity
    have h3 : 0 < z ^ 2 + 1 := by positivity
    rw [inv_pow]
    exact inv_anti₀ h3 (by nlinarith)
  calc ∑ b : Z2 L, Real.exp (-(zdist2 L (b - x) : ℝ) / c) / ((zdist2 L (b - y) : ℝ) + 1)
      = ∑ b : Z2 L, Real.exp (-(zdist2 L (b - x) : ℝ) / c) * ((zdist2 L (b - y) : ℝ) + 1)⁻¹ := by
        simp only [div_eq_mul_inv]
    _ ≤ Real.sqrt (∑ b : Z2 L, (Real.exp (-(zdist2 L (b - x) : ℝ) / c)) ^ 2) *
          Real.sqrt (∑ b : Z2 L, (((zdist2 L (b - y) : ℝ) + 1)⁻¹) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ (1 + c) * Real.sqrt (5 + 4 * Real.log L) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity)

end RBM.Evol
