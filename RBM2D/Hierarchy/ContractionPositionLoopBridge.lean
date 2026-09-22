/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondDerivativeTraceSum

/-!
# Matching position-split word segments with loop products
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The sign and block-label projections of a signed word segment. -/
def segmentLoopIdx (l : List (Bool × Z2 L)) : LoopIdx (Z2 L) :=
  ⟨l.map Prod.fst, l.map Prod.snd⟩

omit [NeZero L] [NeZero W] in
/-- A projected word segment always has matching sign and block lengths. -/
theorem segmentLoopIdx_WF (l : List (Bool × Z2 L)) :
    (segmentLoopIdx L l).WF := by
  simp only [segmentLoopIdx, LoopIdx.WF, List.length_map]

omit [NeZero L] [NeZero W] in
private theorem zip_segment_projections (l : List (Bool × Z2 L)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      cases p
      simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The finite matrix word on a segment equals its loop-index product. -/
theorem coordinateWordProduct_eq_gloopProd
    (u : ℝ) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    coordinateWordProduct L W u ω z l =
      gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L l) := by
  unfold coordinateWordProduct gloopProd segmentLoopIdx
  rw [zip_segment_projections L l]

/-- Both segments of a one-edge split have genuine, well-formed loop words. -/
theorem edgeSplit_segment_products
    (u : ℝ) (ω : Ω L W) (z : ℂ)
    (e : EdgeSplit (Bool × Z2 L)) :
    (segmentLoopIdx L e.before).WF ∧
      (segmentLoopIdx L e.after).WF ∧
      coordinateWordProduct L W u ω z e.before =
        gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L e.before) ∧
      coordinateWordProduct L W u ω z e.after =
        gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L e.after) := by
  exact ⟨segmentLoopIdx_WF L e.before, segmentLoopIdx_WF L e.after,
    coordinateWordProduct_eq_gloopProd L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd L W u ω z e.after⟩

/-- All three segments of a two-edge split have genuine, well-formed loop
words, and their products agree with the coordinate-derivative convention. -/
theorem pairSplit_segment_products
    (u : ℝ) (ω : Ω L W) (z : ℂ)
    (p : PairSplit (Bool × Z2 L)) :
    (segmentLoopIdx L p.before).WF ∧
      (segmentLoopIdx L p.middle).WF ∧
      (segmentLoopIdx L p.after).WF ∧
      coordinateWordProduct L W u ω z p.before =
        gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L p.before) ∧
      coordinateWordProduct L W u ω z p.middle =
        gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L p.middle) ∧
      coordinateWordProduct L W u ω z p.after =
        gloopProd L W (HflowBlock L W u ω) z (segmentLoopIdx L p.after) := by
  exact ⟨segmentLoopIdx_WF L p.before, segmentLoopIdx_WF L p.middle,
    segmentLoopIdx_WF L p.after,
    coordinateWordProduct_eq_gloopProd L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd L W u ω z p.after⟩

end RBM.Gauss
