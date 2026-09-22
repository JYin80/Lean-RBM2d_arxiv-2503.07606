/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.FlowTimeCont

/-!
# Time continuity of a fixed-parameter resolvent

The inverse matrix is continuous along a continuous Hermitian path when the fixed spectral
parameter has nonzero imaginary part. The result applies to `Hflow` samplewise, including
at time zero. A moving spectral parameter and loop observables need separate proofs.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

section GreenCont

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent depends continuously on a continuously varying Hermitian matrix path,
for a fixed spectral parameter off the real axis. -/
theorem continuous_green_of_isHermitian {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : Continuous fun v => green (f v) z := by
  rw [continuous_iff_continuousAt]
  intro v
  have hU : IsUnit (f v - z • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (hherm v) hz
  have hspec : ((hU.unit : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = f v - z • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (f v - z • (1 : Matrix n n ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w => f w - z • (1 : Matrix n n ℂ)) v :=
    hf.continuousAt.sub continuousAt_const
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ))
    (f := fun w => f w - z • (1 : Matrix n n ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

/-- Joint path continuity of the resolvent when both the Hermitian matrix and the
non-real spectral parameter vary continuously. -/
theorem continuous_green_of_isHermitian_moving {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : V → ℂ} (hzcont : Continuous z) (hzim : ∀ v, (z v).im ≠ 0) :
    Continuous fun v => green (f v) (z v) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hU : IsUnit (f v - z v • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (hherm v) (hzim v)
  have hspec : ((hU.unit : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = f v - z v • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (f v - z v • (1 : Matrix n n ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w => f w - z w • (1 : Matrix n n ℂ)) v :=
    hf.continuousAt.sub (hzcont.continuousAt.smul continuousAt_const)
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ))
    (f := fun w => f w - z w • (1 : Matrix n n ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

end GreenCont

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Fixed-sample time continuity of the full resolvent for a fixed non-real `z`. -/
theorem continuous_green_Hflow_time (ω : Ω L W) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun u : ℝ => green (Hflow L W u ω) z :=
  continuous_green_of_isHermitian (continuous_Hflow_time L W ω)
    (fun u => Hflow_isHermitian L W u ω) hz

/-- The samplewise resolvent stays continuous when the spectral parameter follows any
continuous path in the upper or lower half-plane. -/
theorem continuous_green_Hflow_moving_time (ω : Ω L W) {z : ℝ → ℂ}
    (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) :
    Continuous fun u : ℝ => green (Hflow L W u ω) (z u) :=
  continuous_green_of_isHermitian_moving (continuous_Hflow_time L W ω)
    (fun u => Hflow_isHermitian L W u ω) hzcont hzim

/-- A concrete two-dimensional index and spectral parameter for the samplewise resolvent. -/
theorem continuous_green_Hflow_nonzero_index_example (ω : Ω 3 1) :
    Continuous fun u : ℝ =>
      green (Hflow 3 1 u ω) Complex.I ((1, 0) : Idx 3 1) (1, 0) := by
  have h := continuous_green_Hflow_time 3 1 ω (z := Complex.I) (by norm_num)
  exact (continuous_apply _).comp ((continuous_apply _).comp h)

end RBM.Gauss
