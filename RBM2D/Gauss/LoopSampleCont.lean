/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopTimeCont

/-!
# Sample continuity and measurability of finite resolvent loops

At a fixed time and non-real spectral parameter, the reindexed Gaussian matrix flow is
continuous in the sample. The signed resolvents, finite product, and trace inherit this
continuity. This supplies time-slice measurability for a later moment integral.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Reindexing preserves continuity of the matrix flow as a function of the sample. -/
theorem continuous_HflowBlock_sample (u : ℝ) : Continuous (HflowBlock L W u) := by
  change Continuous fun ω : Ω L W =>
    (Hflow L W u ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm
  exact (continuous_Hflow L W u).matrix_submatrix _ _

/-- The fixed-parameter Green matrix is continuous in the Gaussian sample. -/
theorem continuous_green_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω L W => green (HflowBlock L W u ω) z :=
  continuous_green_of_isHermitian (continuous_HflowBlock_sample L W u)
    (fun ω => HflowBlock_isHermitian L W u ω) hz

/-- Both signed resolvents are continuous in the sample. -/
theorem continuous_Gsig_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) :
    Continuous fun ω : Ω L W => Gsig (HflowBlock L W u ω) z σ := by
  cases σ with
  | true => exact continuous_green_HflowBlock_sample L W u hz
  | false =>
      apply continuous_green_HflowBlock_sample L W u
      simpa using hz

/-- The finite loop word is continuous in the Gaussian sample. -/
theorem continuous_foldr_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Z2 L)) :
    Continuous fun ω : Ω L W =>
      l.foldr (fun p M => Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((continuous_Gsig_HflowBlock_sample L W u hz p.1).mul
        continuous_const).mul ih

/-- Sample continuity of the complete matrix product. -/
theorem continuous_gloopProd_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) :
    Continuous fun ω : Ω L W => gloopProd L W (HflowBlock L W u ω) z I :=
  continuous_foldr_HflowBlock_sample L W u hz (I.σ.zip I.a)

/-- A well-formed resolvent loop is continuous in the Gaussian sample at fixed time. -/
theorem continuous_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (_hwf : I.WF) :
    Continuous fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z I :=
  (continuous_matrixTrace L W).comp
    (continuous_gloopProd_HflowBlock_sample L W u hz I)

/-- The fixed-time loop is measurable under the Gaussian product law. -/
theorem measurable_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Measurable fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z I :=
  (continuous_gloop_HflowBlock_sample L W u hz I hwf).measurable

/-- A concrete nonempty one-edge loop at a nonzero block label. -/
theorem measurable_gloop_HflowBlock_one_edge_example (u : ℝ) :
    Measurable fun ω : Ω 3 1 =>
      gloop 3 1 (HflowBlock 3 1 u ω) Complex.I
        ⟨[true], [((1, 0) : Z2 3)]⟩ := by
  apply measurable_gloop_HflowBlock_sample 3 1 u
  · norm_num
  · simp [LoopIdx.WF]

end RBM.Gauss
