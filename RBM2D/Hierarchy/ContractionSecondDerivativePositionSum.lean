/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionFirstDerivativePositionSum

/-!
# The second coordinate derivative as finite position sums
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The second derivative applied twice to the selected Green edge. -/
noncomputable def coordinateSameEdgeTerm (u : ℝ) (ω : Ω L W)
    (γ : Coord L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  coordinateWordProduct L W u ω z e.before *
    (gsigCoordinateSecondDeriv L W u ω γ z e.selected.1 * Eblk L W e.selected.2) *
    coordinateWordProduct L W u ω z e.after

/-- First derivatives applied once to each of two ordered selected edges. -/
noncomputable def coordinatePairTerm (u : ℝ) (ω : Ω L W)
    (γ : Coord L W) (z : ℂ) (p : PairSplit (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  coordinateWordProduct L W u ω z p.before *
    (gsigCoordinateDeriv L W u ω γ z p.first.1 * Eblk L W p.first.2) *
    coordinateWordProduct L W u ω z p.middle *
    (gsigCoordinateDeriv L W u ω γ z p.second.1 * Eblk L W p.second.2) *
    coordinateWordProduct L W u ω z p.after

private theorem pairSplits_cons {α : Type*} (x : α) (xs : List α) :
    pairSplits (x :: xs) =
      (edgeSplits xs).map (fun e : EdgeSplit α =>
        (⟨[], x, e.before, e.selected, e.after⟩ : PairSplit α)) ++
      (pairSplits xs).map (fun p : PairSplit α =>
        ⟨x :: p.before, p.first, p.middle, p.second, p.after⟩) := by
  simp [pairSplits, edgeSplits, List.flatMap_cons, List.flatMap_map,
    List.map_flatMap, List.map_map]
  rfl

omit [NeZero W] in
private theorem sum_map_mul_left
    (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (ms : List (Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :
    (ms.map (fun M => A * M)).sum = A * ms.sum := by
  induction ms with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons M ms ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- Sum of all same-edge second-derivative terms. -/
noncomputable def coordinateSameEdgeSum (u : ℝ) (ω : Ω L W)
    (γ : Coord L W) (z : ℂ) (l : List (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  ((edgeSplits l).map (coordinateSameEdgeTerm L W u ω γ z)).sum

/-- Sum over each unordered pair of distinct positions, keeping the
original left-to-right matrix order. -/
noncomputable def coordinatePairSum (u : ℝ) (ω : Ω L W)
    (γ : Coord L W) (z : ℂ) (l : List (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  ((pairSplits l).map (coordinatePairTerm L W u ω γ z)).sum

private theorem coordinateSameEdgeSum_cons
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    coordinateSameEdgeSum L W u ω γ z (p :: l) =
      (gsigCoordinateSecondDeriv L W u ω γ z p.1 * Eblk L W p.2) *
        coordinateWordProduct L W u ω z l +
      (Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
        coordinateSameEdgeSum L W u ω γ z l := by
  let A := Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2
  let S := gsigCoordinateSecondDeriv L W u ω γ z p.1 * Eblk L W p.2
  have hhead : coordinateSameEdgeTerm L W u ω γ z ⟨[], p, l⟩ =
      S * coordinateWordProduct L W u ω z l := by
    dsimp [S, coordinateSameEdgeTerm, coordinateWordProduct]
    simp only [one_mul]
  have hshift (e : EdgeSplit (Bool × Z2 L)) :
      coordinateSameEdgeTerm L W u ω γ z ⟨p :: e.before, e.selected, e.after⟩ =
        A * coordinateSameEdgeTerm L W u ω γ z e := by
    dsimp [A, coordinateSameEdgeTerm, coordinateWordProduct]
    simp only [Matrix.mul_assoc]
  simp only [coordinateSameEdgeSum, edgeSplits, List.map_cons, List.sum_cons]
  rw [hhead, List.map_map]
  simp only [Function.comp_def]
  simp_rw [hshift]
  rw [← sum_map_mul_left L W A
    ((edgeSplits l).map (coordinateSameEdgeTerm L W u ω γ z)), List.map_map]
  rfl

private theorem coordinatePairSum_cons
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    coordinatePairSum L W u ω γ z (p :: l) =
      (gsigCoordinateDeriv L W u ω γ z p.1 * Eblk L W p.2) *
        ((edgeSplits l).map (coordinateEdgeTerm L W u ω γ z)).sum +
      (Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
        coordinatePairSum L W u ω γ z l := by
  let A := Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2
  let D := gsigCoordinateDeriv L W u ω γ z p.1 * Eblk L W p.2
  have hhead (e : EdgeSplit (Bool × Z2 L)) :
      coordinatePairTerm L W u ω γ z
          ⟨[], p, e.before, e.selected, e.after⟩ =
        D * coordinateEdgeTerm L W u ω γ z e := by
    dsimp [D, coordinatePairTerm, coordinateEdgeTerm, coordinateWordProduct]
    simp only [one_mul, Matrix.mul_assoc]
  have hshift (q : PairSplit (Bool × Z2 L)) :
      coordinatePairTerm L W u ω γ z
          ⟨p :: q.before, q.first, q.middle, q.second, q.after⟩ =
        A * coordinatePairTerm L W u ω γ z q := by
    dsimp [A, coordinatePairTerm, coordinateWordProduct]
    simp only [Matrix.mul_assoc]
  simp only [coordinatePairSum, pairSplits_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def]
  simp_rw [hhead, hshift]
  rw [← sum_map_mul_left L W D
    ((edgeSplits l).map (coordinateEdgeTerm L W u ω γ z)),
    ← sum_map_mul_left L W A
      ((pairSplits l).map (coordinatePairTerm L W u ω γ z))]
  simp only [List.map_map, Function.comp_def]

/-- For every finite signed word, the second coordinate derivative is the
sum over all same-edge insertions plus twice the sum over all pairs of
distinct edges. The `PairSplit` enumerator lists each pair only once. -/
theorem coordinateSecondWordDeriv_eq_position_sums
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    coordinateSecondWordDeriv L W u ω γ z l =
      coordinateSameEdgeSum L W u ω γ z l +
        (2 : ℕ) • coordinatePairSum L W u ω γ z l := by
  induction l with
  | nil =>
      simp only [coordinateSecondWordDeriv, coordinateSameEdgeSum,
        coordinatePairSum, edgeSplits, pairSplits, List.flatMap_nil,
        List.map_nil, List.sum_nil,
        smul_zero, add_zero]
  | cons p l ih =>
      rw [coordinateSecondWordDeriv,
        coordinateSameEdgeSum_cons L W u ω γ z p l,
        coordinatePairSum_cons L W u ω γ z p l,
        coordinateWordDeriv_eq_edgeSplits_sum L W u ω γ z l, ih]
      simp only [coordinateWordProduct, nsmul_eq_mul, Nat.cast_ofNat,
        two_mul, mul_add]
      abel

end RBM.Gauss
