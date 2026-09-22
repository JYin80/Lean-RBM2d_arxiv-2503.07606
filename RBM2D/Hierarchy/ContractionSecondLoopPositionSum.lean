/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopSameEdgeCut

/-!
# Position decomposition of a three-edge second derivative

The finite three-edge case displays every same-edge term and every ordered
distinct-edge pair. The word order remains unchanged by differentiation.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- For three edges, the second coordinate derivative has three same-edge
terms and three distinct-edge pairs, each with multiplicity two. Every
factor is written in its actual prefix/middle/suffix position. -/
theorem coordinateSecondWordDeriv_three_edges
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (s t r : Bool) (a b c : Z2 L) :
    let H := HflowBlock L W u ω
    let A₁ := Gsig H z s * Eblk L W a
    let A₂ := Gsig H z t * Eblk L W b
    let A₃ := Gsig H z r * Eblk L W c
    let D₁ := gsigCoordinateDeriv L W u ω γ z s * Eblk L W a
    let D₂ := gsigCoordinateDeriv L W u ω γ z t * Eblk L W b
    let D₃ := gsigCoordinateDeriv L W u ω γ z r * Eblk L W c
    let S₁ := gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a
    let S₂ := gsigCoordinateSecondDeriv L W u ω γ z t * Eblk L W b
    let S₃ := gsigCoordinateSecondDeriv L W u ω γ z r * Eblk L W c
    coordinateSecondWordDeriv L W u ω γ z [(s, a), (t, b), (r, c)] =
      (S₁ * A₂ * A₃ + A₁ * S₂ * A₃ + A₁ * A₂ * S₃) +
      ((2 : ℕ) • (D₁ * D₂ * A₃) +
        (2 : ℕ) • (D₁ * A₂ * D₃) +
        (2 : ℕ) • (A₁ * D₂ * D₃)) := by
  simp only [coordinateSecondWordDeriv, coordinateWordDeriv,
    List.foldr_cons, List.foldr_nil, mul_one, mul_zero, add_zero,
    nsmul_eq_mul, Nat.cast_ofNat]
  simp only [Matrix.mul_assoc, mul_add, two_mul]
  abel

end RBM.Gauss
