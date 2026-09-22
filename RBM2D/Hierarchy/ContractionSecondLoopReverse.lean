/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoop

/-!
# The reverse ordered two-edge derivative term

The two mixed terms in the second product rule have the same matrix word:
the order of differentiation does not change the order of the Green factors.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- For a word of two Green edges, the two distinct-edge contributions to
`coordinateSecondWordDeriv` coincide. This is the actual recursive second
product rule, with its single-edge terms retained. -/
theorem coordinateSecondWordDeriv_two_edges
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (s t : Bool) (a c : Z2 L) :
    let H := HflowBlock L W u ω
    let Ds := gsigCoordinateDeriv L W u ω γ z s
    let Dt := gsigCoordinateDeriv L W u ω γ z t
    let Ss := gsigCoordinateSecondDeriv L W u ω γ z s
    let St := gsigCoordinateSecondDeriv L W u ω γ z t
    coordinateSecondWordDeriv L W u ω γ z [(s, a), (t, c)] =
      (Ss * Eblk L W a) * (Gsig H z t * Eblk L W c) +
      (2 : ℕ) • ((Ds * Eblk L W a) * (Dt * Eblk L W c)) +
      (Gsig H z s * Eblk L W a) * (St * Eblk L W c) := by
  simp only [coordinateSecondWordDeriv, coordinateWordDeriv, List.foldr_cons,
    List.foldr_nil, mul_one, mul_zero, add_zero,
    nsmul_eq_mul, Nat.cast_ofNat, add_assoc]
  rw [two_mul]
  abel

end RBM.Gauss
