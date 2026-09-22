/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionPositionLoopBridge

/-!
# The same-edge cut formula at one enumerated loop position
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- At any chosen edge, the weighted second-coordinate insertion is the
same-edge cut-loop double sum. The two projected segments are well formed. -/
theorem sum_coordinateSameEdgeTerm_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (e : EdgeSplit (Bool × Z2 L)) :
    let H := HflowBlock L W u ω
    let I₁ := segmentLoopIdx L e.before
    let I₂ := segmentLoopIdx L e.after
    ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm L W u ω γ z e)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W H z
          ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
            e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
          SB L p q * gloop L W H z ⟨[e.selected.1], [q]⟩ := by
  have h₁ : (e.before.map Prod.fst).length =
      (e.before.map Prod.snd).length := segmentLoopIdx_WF L e.before
  have h₂ : (e.after.map Prod.fst).length =
      (e.after.map Prod.snd).length := segmentLoopIdx_WF L e.after
  dsimp only [coordinateSameEdgeTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd L W u ω z e.after]
  exact sum_sameEdge_cutLoops L W u hu ω z
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 h₁ h₂

/-- Membership in the position enumerator supplies the literal split of the
original word, together with its cut-loop contraction. -/
theorem sum_coordinateSameEdgeTerm_cutLoops_of_mem
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) (e : EdgeSplit (Bool × Z2 L))
    (he : e ∈ edgeSplits l) :
    e.before ++ e.selected :: e.after = l ∧
      (let H := HflowBlock L W u ω
       let I₁ := segmentLoopIdx L e.before
       let I₂ := segmentLoopIdx L e.after
       ∑ γ : Coord L W,
         (((gvar L W γ : ℝ) : ℂ) *
           Matrix.trace (coordinateSameEdgeTerm L W u ω γ z e)) =
       (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
         ∑ p : Z2 L, ∑ q : Z2 L,
           gloop L W H z
             ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
               e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
             SB L p q * gloop L W H z ⟨[e.selected.1], [q]⟩) := by
  exact ⟨edgeSplits_reconstruct l e he,
    sum_coordinateSameEdgeTerm_cutLoops L W u hu ω z e⟩

end RBM.Gauss
