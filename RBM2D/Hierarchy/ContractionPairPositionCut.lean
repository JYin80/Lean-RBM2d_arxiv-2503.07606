/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSameEdgePositionCut

/-!
# The two-edge cut formula at one enumerated pair of loop positions
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- At any chosen ordered pair of edges, the Gaussian variance contraction
is the corresponding left/right cut-loop double sum. -/
theorem sum_coordinatePairTerm_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (p : PairSplit (Bool × Z2 L)) :
    let H := HflowBlock L W u ω
    let I₁ := segmentLoopIdx L p.before
    let I₂ := segmentLoopIdx L p.middle
    let I₃ := segmentLoopIdx L p.after
    ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm L W u ω γ z p)) =
    (u : ℂ) * (W : ℂ) ^ 2 * ∑ v : Z2 L, ∑ w : Z2 L,
      gloop L W H z
        ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
            I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueL
          (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
        SB L v w *
      gloop L W H z
        ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
            I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueR
          (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w) := by
  have h₁ : (p.before.map Prod.fst).length =
      (p.before.map Prod.snd).length := segmentLoopIdx_WF L p.before
  have h₂ : (p.middle.map Prod.fst).length =
      (p.middle.map Prod.snd).length := segmentLoopIdx_WF L p.middle
  dsimp only [coordinatePairTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd L W u ω z p.after]
  exact RBM.sum_twoEdge_mixed_deriv L W u hu ω z
    (p.before.map Prod.fst) (p.middle.map Prod.fst) (p.after.map Prod.fst)
    (p.before.map Prod.snd) (p.middle.map Prod.snd) (p.after.map Prod.snd)
    p.first.1 p.second.1 p.first.2 p.second.2 h₁ h₂

/-- Pair membership supplies the literal five-part split of the original
word, alongside the fixed-position variance contraction. -/
theorem sum_coordinatePairTerm_cutLoops_of_mem
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (l : List (Bool × Z2 L)) (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits l) :
    p.before ++ p.first :: p.middle ++ p.second :: p.after = l ∧
      (let H := HflowBlock L W u ω
       let I₁ := segmentLoopIdx L p.before
       let I₂ := segmentLoopIdx L p.middle
       let I₃ := segmentLoopIdx L p.after
       ∑ γ : Coord L W,
         (((gvar L W γ : ℝ) : ℂ) *
           Matrix.trace (coordinatePairTerm L W u ω γ z p)) =
       (u : ℂ) * (W : ℂ) ^ 2 * ∑ v : Z2 L, ∑ w : Z2 L,
         gloop L W H z
           ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
               I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueL
             (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
           SB L v w *
         gloop L W H z
           ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
               I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueR
             (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)) := by
  exact ⟨pairSplits_reconstruct l p hp,
    sum_coordinatePairTerm_cutLoops L W u hu ω z p⟩

end RBM.Gauss
