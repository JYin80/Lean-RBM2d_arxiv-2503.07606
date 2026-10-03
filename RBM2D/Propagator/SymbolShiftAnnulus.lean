/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Cutoff
import RBM2D.Propagator.Momentum

/-!
# Stability of momentum annuli under coordinate steps

The shift comparison is stated with its necessary lower-radius hypothesis.
It can be applied to each denominator of a second coordinate difference.
-/

namespace RBM

/-- Angular size of one lattice-frequency step. -/
noncomputable def symbolGridStep (L : ℕ) [NeZero L] : ℝ :=
  2 * Real.pi / (L : ℝ)

private theorem pstar_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    pstar L (u + v) ≤ pstar L u + pstar L v := by
  have hz := zdist_add_le L u v
  have hz' : (zdist L (u + v) : ℝ) ≤
      (zdist L u : ℝ) + (zdist L v : ℝ) := by exact_mod_cast hz
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (u + v) = symbolGridStep L * (zdist L (u + v) : ℝ) := by
      unfold pstar symbolGridStep
      ring
    _ ≤ symbolGridStep L * (zdist L u : ℝ) +
        symbolGridStep L * (zdist L v : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hz' hc]
    _ = pstar L u + pstar L v := by
      unfold pstar symbolGridStep
      ring

private theorem pstar_neg_one_le_grid (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) :
    pstar L (-1 : ZMod L) ≤ symbolGridStep L := by
  have hz : (zdist L (-1 : ZMod L) : ℝ) ≤ 1 := by
    exact_mod_cast zdist_neg_one_le L hL
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (-1 : ZMod L) =
        symbolGridStep L * (zdist L (-1 : ZMod L) : ℝ) := by
          unfold pstar symbolGridStep
          ring
    _ ≤ symbolGridStep L := by
      nlinarith [mul_le_mul_of_nonneg_left hz hc]

/-- A single coordinate step changes its angular distance by at most one grid step. -/
theorem pstar_le_shift_one (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (u : ZMod L) :
    pstar L u ≤ pstar L (u + 1) + symbolGridStep L := by
  calc
    pstar L u = pstar L ((u + 1) + (-1)) := by
      congr 1
      abel
    _ ≤ pstar L (u + 1) + pstar L (-1) := pstar_add_le L _ _
    _ ≤ pstar L (u + 1) + symbolGridStep L := by
      gcongr
      exact pstar_neg_one_le_grid L hL

end RBM
