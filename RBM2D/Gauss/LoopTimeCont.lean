/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.GreenTimeCont
import RBM2D.Hierarchy.Loops
import Mathlib.Topology.Instances.Matrix

/-!
# Samplewise time continuity of finite resolvent loops

At a fixed Gaussian sample, the two spectral signs, finite matrix product, and trace are
continuous along a continuous non-real spectral path. Well-formedness identifies a loop
with its intended list of edges; analytically, the finite zipped product is continuous even
for lists of unequal lengths.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The fine-lattice flow reindexed by the paper's block and within-block coordinates. -/
noncomputable def HflowBlock (u : ℝ) (ω : Ω L W) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  (Hflow L W u ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm

theorem continuous_HflowBlock_time (ω : Ω L W) :
    Continuous fun u : ℝ => HflowBlock L W u ω :=
  (continuous_Hflow_time L W ω).matrix_submatrix _ _

theorem HflowBlock_isHermitian (u : ℝ) (ω : Ω L W) :
    (HflowBlock L W u ω).IsHermitian :=
  (Hflow_isHermitian L W u ω).submatrix _

/-- The reindexed flow has a continuous Green matrix for a moving non-real parameter. -/
theorem continuous_green_HflowBlock_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => green (HflowBlock L W u ω) (z u) :=
  continuous_green_of_isHermitian_moving (continuous_HflowBlock_time L W ω)
    (fun u => HflowBlock_isHermitian L W u ω) hzcont hzim

/-- Either spectral sign gives a continuous Green matrix along the fixed-sample flow. -/
theorem continuous_Gsig_Hflow_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) (σ : Bool) :
    Continuous fun u : ℝ => Gsig (HflowBlock L W u ω) (z u) σ := by
  cases σ with
  | true =>
      exact continuous_green_HflowBlock_time L W ω hzcont hzim
  | false =>
      have hzconj : Continuous (fun u => (starRingEnd ℂ) (z u)) :=
        Complex.continuous_conj.comp hzcont
      have hzimconj : ∀ u, ((starRingEnd ℂ) (z u)).im ≠ 0 := by
        intro u
        simpa using hzim u
      exact continuous_green_HflowBlock_time L W ω hzconj hzimconj

/-- A finite list of signed Green factors and block insertions has a continuous product. -/
theorem continuous_foldr_Hflow_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (l : List (Bool × Z2 L)) :
    Continuous fun u : ℝ =>
      l.foldr (fun p M => Gsig (HflowBlock L W u ω) (z u) p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((continuous_Gsig_Hflow_time L W ω hzcont hzim p.1).mul
        continuous_const).mul ih

/-- Continuity of the full finite loop word. -/
theorem continuous_gloopProd_Hflow_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (I : LoopIdx (Z2 L)) :
    Continuous fun u : ℝ => gloopProd L W (HflowBlock L W u ω) (z u) I :=
  continuous_foldr_Hflow_time L W ω hzcont hzim (I.σ.zip I.a)

omit [NeZero W] in
/-- The trace of a finite complex matrix depends continuously on the matrix. -/
theorem continuous_matrixTrace :
    Continuous (Matrix.trace : Matrix (BlockIndex L W) (BlockIndex L W) ℂ → ℂ) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ)

/-- A well-formed finite resolvent loop is continuous in time at a fixed Gaussian sample. -/
theorem continuous_gloop_Hflow_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0)
    (I : LoopIdx (Z2 L)) (_hwf : I.WF) :
    Continuous fun u : ℝ => gloop L W (HflowBlock L W u ω) (z u) I :=
  (continuous_matrixTrace L W).comp
    (continuous_gloopProd_Hflow_time L W ω hzcont hzim I)

/-- A concrete one-edge loop at a nonzero block label. -/
theorem continuous_gloop_Hflow_one_edge_example (ω : Ω 3 1) :
    Continuous fun u : ℝ =>
      gloop 3 1 (HflowBlock 3 1 u ω) ((u : ℂ) + Complex.I)
        ⟨[true], [((1, 0) : Z2 3)]⟩ := by
  apply continuous_gloop_Hflow_time 3 1 ω
  · exact Complex.continuous_ofReal.add continuous_const
  · intro u
    norm_num
  · simp [LoopIdx.WF]

end RBM.Gauss
