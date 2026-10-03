/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondDerivativePositionSum

/-!
# Finite trace and Gaussian-coordinate sums of the second word derivative
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem sum_weighted_trace_list {α : Type*}
    (es : List α) (w : Coord L W → ℂ)
    (T : Coord L W → α → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ γ : Coord L W, w γ * Matrix.trace ((es.map (T γ)).sum) =
      (es.map (fun e => ∑ γ : Coord L W, w γ * Matrix.trace (T γ e))).sum := by
  induction es with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Matrix.trace_zero, mul_zero,
        Finset.sum_const_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, mul_add,
        Finset.sum_add_distrib, ih]

/-- Exact finite exchange of coordinate and edge-position sums in the
traced second product rule. No loop-cut or expectation identity is used. -/
theorem sum_coordinateSecondWordDeriv_trace_positions
    (u : ℝ) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l)) =
    ((edgeSplits l).map (fun e => ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm L W u ω γ z e)))).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p => ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm L W u ω γ z p)))).sum := by
  simp_rw [coordinateSecondWordDeriv_eq_position_sums L W]
  simp only [two_nsmul, Matrix.trace_add, mul_add, Finset.sum_add_distrib,
    coordinateSameEdgeSum, coordinatePairSum]
  rw [sum_weighted_trace_list L W (edgeSplits l),
    sum_weighted_trace_list L W (pairSplits l)]
  ring

end RBM.Gauss
