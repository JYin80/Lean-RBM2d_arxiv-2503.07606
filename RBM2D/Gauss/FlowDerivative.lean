/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.FlowTimeCont

/-!
# Samplewise derivative of the Gaussian matrix coupling

At positive time, the fixed-sample coupling `Hflow u ω = √u • Xmat ω` has derivative
`(2√u)⁻¹ • Xmat ω`. This is a deterministic path derivative, not a Brownian generator.
-/

namespace RBM.Gauss

open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The matrix-valued time derivative of a fixed Gaussian sample. -/
theorem hasDerivAt_Hflow_time (ω : Ω L W) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => Hflow L W v ω)
      ((1 / (2 * Real.sqrt u)) • Xmat L W ω) u := by
  have h := (Real.hasDerivAt_sqrt hu.ne').smul_const (Xmat L W ω)
  simpa only [Hflow_eq_realSmul] using h

/-- At time one, the derivative is half of the original matrix. -/
theorem hasDerivAt_Hflow_one (ω : Ω L W) :
    HasDerivAt (fun v : ℝ => Hflow L W v ω) ((1 / 2 : ℝ) • Xmat L W ω) 1 := by
  simpa using hasDerivAt_Hflow_time L W ω (by norm_num : (0 : ℝ) < 1)

/-- A deterministic Gaussian sample can have a genuinely nonzero time derivative. -/
example : ∃ ω : Ω 3 1,
    ((1 / 2 : ℝ) • Xmat 3 1 ω) ≠ 0 ∧
      HasDerivAt (fun v : ℝ => Hflow 3 1 v ω) ((1 / 2 : ℝ) • Xmat 3 1 ω) 1 := by
  let ω : Ω 3 1 :=
    fun c => if c = ((0 : Idx 3 1), (0 : Idx 3 1), true) then 1 else 0
  have hX : Xmat 3 1 ω (0 : Idx 3 1) 0 = 1 := by
    simp [Xmat, Xentry, ω]
  refine ⟨ω, ?_, hasDerivAt_Hflow_one 3 1 ω⟩
  intro h
  have h0 := congrArg (fun M : Matrix (Idx 3 1) (Idx 3 1) ℂ => M 0 0) h
  simp only [Matrix.smul_apply, Matrix.zero_apply, Complex.real_smul] at h0
  rw [hX] at h0
  norm_num at h0

end RBM.Gauss
