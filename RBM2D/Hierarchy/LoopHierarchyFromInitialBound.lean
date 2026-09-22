/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyIntegralBound
import RBM2D.Gauss.LoopInitialValueEmpty

/-!
# Bounds from the deterministic initial loop

At time zero the Gaussian matrix flow vanishes. The finite-time increment
bound therefore controls the expected loop relative to its explicit scalar
initial value, including the endpoint `u = 0`.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The finite expected loop differs from its exact deterministic initial
scalar by at most elapsed time times the uniform hierarchy envelope. -/
theorem norm_expected_gloop_sub_initial_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    ‖(∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)) -
      totalInitialLoopScalar L W E I‖ ≤
      loopHierarchyUniformEnvelope L W η E I * u := by
  by_cases hzero : u = 0
  · subst u
    rw [integral_gloop_HflowBlock_zero L W E I,
      initialLoopValue_eq_total L W hE I hwf]
    simp
  · have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
    have h := norm_expected_gloop_increment_le L W hL I hwf
      hE le_rfl hu hu1 hη hz
    rw [integral_gloop_HflowBlock_zero L W E I,
      initialLoopValue_eq_total L W hE I hwf] at h
    simpa using h

/-- The preceding deviation bound with the actual uniform spectral-path
gap `(1-u) Im m(E)`, positive for every `u<1`. -/
theorem norm_expected_gloop_sub_initial_le_pathGap
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ‖(∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)) -
      totalInitialLoopScalar L W E I‖ ≤
      loopHierarchyUniformEnvelope L W
        ((1 - u) * (spectralM E).im) E I * u := by
  have hη : 0 < (1 - u) * (spectralM E).im :=
    mul_pos (by linarith) (spectralM_im_pos hE)
  exact norm_expected_gloop_sub_initial_le L W hL I hwf hE hu0 hu1 hη
    (fun v hv => spectralZ_im_gap hE hu1 hv)

/-- A direct finite-time norm bound on the full expected loop. This remains
a crude finite-size estimate, without any moment closure. -/
theorem norm_expected_gloop_le_initial_add_envelope
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)‖ ≤
      ‖totalInitialLoopScalar L W E I‖ +
        loopHierarchyUniformEnvelope L W η E I * u := by
  have hdev := norm_expected_gloop_sub_initial_le L W hL I hwf
    hE hu0 hu1 hη hz
  calc
    ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)‖ =
      ‖((∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)) -
        totalInitialLoopScalar L W E I) + totalInitialLoopScalar L W E I‖ := by
          congr 1
          ring
    _ ≤ ‖(∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W)) -
        totalInitialLoopScalar L W E I‖ +
        ‖totalInitialLoopScalar L W E I‖ := norm_add_le _ _
    _ ≤ ‖totalInitialLoopScalar L W E I‖ +
          loopHierarchyUniformEnvelope L W η E I * u := by linarith

end RBM.Gauss
