/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionPairSplits

/-!
# The first coordinate derivative as a sum over edge positions
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The undifferentiated matrix word on a list of signed block edges. -/
noncomputable def coordinateWordProduct (u : ℝ) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p M => Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2 * M) 1

/-- Differentiate precisely the chosen edge of a split word. -/
noncomputable def coordinateEdgeTerm (u : ℝ) (ω : Ω L W)
    (γ : Coord L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  coordinateWordProduct L W u ω z e.before *
    (gsigCoordinateDeriv L W u ω γ z e.selected.1 * Eblk L W e.selected.2) *
    coordinateWordProduct L W u ω z e.after

omit [NeZero W] in
private theorem sum_map_mul_left
    (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (ms : List (Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :
    (ms.map (fun M => A * M)).sum = A * ms.sum := by
  induction ms with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons M ms ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The recursive first product rule is exactly the finite sum over all
selected edges. Prefix and suffix matrix factors remain in word order. -/
theorem coordinateWordDeriv_eq_edgeSplits_sum
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    coordinateWordDeriv L W u ω γ z l =
      ((edgeSplits l).map (coordinateEdgeTerm L W u ω γ z)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      let A := Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2
      let D := gsigCoordinateDeriv L W u ω γ z p.1 * Eblk L W p.2
      have hshift (e : EdgeSplit (Bool × Z2 L)) :
          coordinateEdgeTerm L W u ω γ z
              ⟨p :: e.before, e.selected, e.after⟩ =
            A * coordinateEdgeTerm L W u ω γ z e := by
        dsimp [A, coordinateEdgeTerm, coordinateWordProduct]
        simp only [Matrix.mul_assoc]
      have hhead : coordinateEdgeTerm L W u ω γ z
          ⟨[], p, l⟩ = D * coordinateWordProduct L W u ω z l := by
        dsimp [D, coordinateEdgeTerm, coordinateWordProduct]
        simp only [one_mul]
      simp only [coordinateWordDeriv, edgeSplits, List.map_cons, List.sum_cons]
      rw [ih]
      rw [hhead]
      rw [List.map_map]
      change D * coordinateWordProduct L W u ω z l +
          A * ((edgeSplits l).map (coordinateEdgeTerm L W u ω γ z)).sum =
        D * coordinateWordProduct L W u ω z l +
          ((edgeSplits l).map (fun e => coordinateEdgeTerm L W u ω γ z
            ⟨p :: e.before, e.selected, e.after⟩)).sum
      simp_rw [hshift]
      rw [← sum_map_mul_left L W A
        ((edgeSplits l).map (coordinateEdgeTerm L W u ω γ z)), List.map_map]
      rfl

end RBM.Gauss
