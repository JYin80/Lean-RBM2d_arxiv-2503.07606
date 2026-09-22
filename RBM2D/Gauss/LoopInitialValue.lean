/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopExpectationDerivative

/-!
# Initial value of a finite Gaussian resolvent loop

At time zero the matrix flow vanishes at every sample. The expected loop is
therefore the deterministic resolvent loop of the zero matrix.
-/

namespace RBM.Gauss

open Matrix MeasureTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

@[simp] theorem HflowBlock_zero (ω : Ω L W) :
    HflowBlock L W 0 ω = 0 := by
  simp [HflowBlock]

/-- The exact deterministic initial loop value, retaining the normalized
block insertions in `gloop`. -/
noncomputable def initialLoopValue (E : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  gloop L W 0 (E + spectralM E) I

omit [NeZero W] in
/-- Explicit finite matrix product for the initial value; every `Eblk`
already carries its `W⁻²` normalization. -/
theorem initialLoopValue_eq_trace_product (E : ℝ) (I : LoopIdx (Z2 L)) :
    initialLoopValue L W E I =
      Matrix.trace ((I.σ.zip I.a).foldr
        (fun p M => Gsig (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
          (E + spectralM E) p.1 * Eblk L W p.2 * M) 1) := rfl

/-- Each sample has the same initial loop value. -/
theorem gloop_HflowBlock_zero (ω : Ω L W) (E : ℝ)
    (I : LoopIdx (Z2 L)) :
    gloop L W (HflowBlock L W 0 ω) (spectralZ E 0) I =
      initialLoopValue L W E I := by
  simp [initialLoopValue, spectralZ]

/-- The expected finite loop starts at the deterministic zero-matrix value. -/
theorem integral_gloop_HflowBlock_zero (E : ℝ) (I : LoopIdx (Z2 L)) :
    ∫ ω : Ω L W,
      gloop L W (HflowBlock L W 0 ω) (spectralZ E 0) I ∂(P L W) =
        initialLoopValue L W E I := by
  simp only [gloop_HflowBlock_zero]
  simp

end RBM.Gauss
