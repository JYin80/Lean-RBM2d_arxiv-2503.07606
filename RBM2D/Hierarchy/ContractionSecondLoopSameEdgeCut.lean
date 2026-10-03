/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopSameEdgeWord

/-!
# A same-edge contraction at a specified edge of a finite loop
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The first block trace closes into the loop formed by the suffix,
prefix, and a repeated copy of the differentiated signed Green edge. -/
theorem trace_sameEdge_cutLoop
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a p : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let G := Gsig H z s
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let T := gloopProd L W H z ⟨σ₂, a₂⟩
    Matrix.trace (((G * Eblk L W a * T * P) * G) * Eblk L W p) =
      gloop L W H z
        ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ := by
  rw [gloop, gloopProd_cons, gloopProd_append h₂,
    gloopProd_append h₁]
  simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one, Matrix.mul_assoc]

omit [NeZero W] in
/-- The second block trace is the one-edge loop. -/
theorem trace_sameEdge_oneLoop
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (z : ℂ) (s : Bool) (q : Z2 L) :
    Matrix.trace (Gsig H z s * Eblk L W q) =
      gloop L W H z ⟨[s], [q]⟩ := by
  simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]

/-- The same-edge variance contraction at the specified split of a finite
loop word. No sum over edge positions or expectation is taken. -/
theorem sum_sameEdge_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := Gauss.HflowBlock L W u ω
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let T := gloopProd L W H z ⟨σ₂, a₂⟩
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gauss.gsigCoordinateSecondDeriv L W u ω γ z s *
          Eblk L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W H z
          ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ *
          SB L p q * gloop L W H z ⟨[s], [q]⟩ := by
  dsimp only
  rw [sum_gsigCoordinateSecondDeriv_word L W u hu ω z s a
    (gloopProd L W (Gauss.HflowBlock L W u ω) z ⟨σ₁, a₁⟩)
    (gloopProd L W (Gauss.HflowBlock L W u ω) z ⟨σ₂, a₂⟩)]
  simp_rw [trace_sameEdge_cutLoop L W (Gauss.HflowBlock L W u ω) z
    σ₁ σ₂ a₁ a₂ s a _ h₁ h₂,
    trace_sameEdge_oneLoop L W (Gauss.HflowBlock L W u ω) z s]

end RBM
