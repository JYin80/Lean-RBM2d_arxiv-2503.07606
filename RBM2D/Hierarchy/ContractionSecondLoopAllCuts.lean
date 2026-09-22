/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionPairPositionCut

/-!
# All finite cut terms in the variance-weighted second loop derivative
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The cut-loop product attached to one same-edge position, without its
common coefficient `2uW²`. -/
noncomputable def sameEdgeCutValue (u : ℝ) (ω : Ω L W) (z : ℂ)
    (e : EdgeSplit (Bool × Z2 L)) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  ∑ p : Z2 L, ∑ q : Z2 L,
    gloop L W H z
      ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
        e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
      SB L p q * gloop L W H z ⟨[e.selected.1], [q]⟩

/-- The left/right cut-loop product attached to one pair of distinct edges,
without its common coefficient `2uW²` from the two derivative orders. -/
noncomputable def pairCutValue (u : ℝ) (ω : Ω L W) (z : ℂ)
    (p : PairSplit (Bool × Z2 L)) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  ∑ v : Z2 L, ∑ w : Z2 L,
    gloop L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueL
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
      SB L v w *
    gloop L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueR
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)

omit [NeZero L] [NeZero W] in
private theorem list_sum_map_mul_left {α : Type*} (c : ℂ)
    (es : List α) (f : α → ℂ) :
    (es.map (fun e => c * f e)).sum = c * (es.map f).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The full finite samplewise cut formula for any actual signed word.
Both same-edge and distinct-edge families have coefficient `2uW²`. -/
theorem sum_coordinateSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ((edgeSplits l).map (sameEdgeCutValue L W u ω z)).sum +
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ((pairSplits l).map (pairCutValue L W u ω z)).sum := by
  rw [sum_coordinateSecondWordDeriv_trace_positions L W u ω z l]
  simp_rw [sum_coordinateSameEdgeTerm_cutLoops L W u hu ω z]
  simp_rw [sum_coordinatePairTerm_cutLoops L W u hu ω z]
  change ((edgeSplits l).map (fun e =>
      ((2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2) * sameEdgeCutValue L W u ω z e)).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p =>
      ((u : ℂ) * (W : ℂ) ^ 2) * pairCutValue L W u ω z p)).sum = _
  rw [list_sum_map_mul_left, list_sum_map_mul_left]
  ring

omit [NeZero L] [NeZero W] in
/-- Zipping a well-formed loop and projecting it back preserves its literal
sign and block-label lists. -/
theorem segmentLoopIdx_zip_eq (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    segmentLoopIdx L (I.σ.zip I.a) = I := by
  cases I with
  | mk σ a =>
      change σ.length = a.length at hwf
      change (⟨(σ.zip a).map Prod.fst, (σ.zip a).map Prod.snd⟩ :
        LoopIdx (Z2 L)) = ⟨σ, a⟩
      rw [List.map_fst_zip hwf.le, List.map_snd_zip hwf.ge]

/-- The full samplewise cut formula for a well-formed finite loop. The first
conclusion certifies that the signed word used by the derivative is exactly
the supplied loop, without truncation by `List.zip`. -/
theorem sum_gloopSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    let l := I.σ.zip I.a
    segmentLoopIdx L l = I ∧
      (∑ γ : Coord L W,
        (((gvar L W γ : ℝ) : ℂ) *
          Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l)) =
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
         ((edgeSplits l).map (sameEdgeCutValue L W u ω z)).sum +
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
         ((pairSplits l).map (pairCutValue L W u ω z)).sum) := by
  exact ⟨segmentLoopIdx_zip_eq L I hwf,
    sum_coordinateSecondWordDeriv_allCuts L W u hu ω z (I.σ.zip I.a)⟩

end RBM.Gauss
