/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopFlowDerivativeEnvelope
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating an expected finite Gaussian resolvent loop

The explicit integrable envelope on a closed neighborhood permits differentiation
under the product Gaussian integral. The finite coordinate Stein identity then
gives the exact second-coordinate and spectral terms.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The expected finite loop has the expected samplewise derivative at an interior time. -/
theorem hasDerivAt_integral_gloop_HflowBlock_spectralZ
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    HasDerivAt (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W))
      (∫ ω : Ω L W, deriv (fun v : ℝ =>
        gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u ∂(P L W))
      u := by
  let F : ℝ → Ω L W → ℂ := fun v ω =>
    gloop L W (HflowBlock L W v ω) (spectralZ E v) I
  let F' : ℝ → Ω L W → ℂ := fun v ω => deriv (F · ω) v
  let bound : Ω L W → ℝ := flowDerivativeEnvelope L W E u I
  have hstrict := flowWindow_strict u hu hu1
  have hOpen : Set.Ioo (u / 2) ((1 + u) / 2) ∈ 𝓝 u :=
    isOpen_Ioo.mem_nhds hstrict
  have hs : flowWindow u ∈ 𝓝 u := by
    apply Filter.mem_of_superset hOpen
    intro v hv
    exact ⟨hv.1.le, hv.2.le⟩
  have hF_meas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) (P L W) := by
    filter_upwards [hs] with v hv
    have hv' := flowWindow_subset_Ioo u hu hu1 hv
    have hz : (spectralZ E v).im ≠ 0 := by
      rw [spectralZ_im]
      exact ne_of_gt (mul_pos (by linarith [hv'.2]) (spectralM_im_pos hE))
    exact (measurable_gloop_HflowBlock_sample L W v hz I hwf).aestronglyMeasurable
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hη : 0 < |(spectralZ E u).im| := abs_pos.mpr hz
  have hF_int : Integrable (F u) (P L W) := by
    apply Integrable.of_bound
      (measurable_gloop_HflowBlock_sample L W u hz I hwf).aestronglyMeasurable
      ((((L * W) ^ 2 : ℕ) : ℝ) *
        (|(spectralZ E u).im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length)
    exact Filter.Eventually.of_forall fun ω =>
      norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
        hη le_rfl I hwf
  have hF'_meas : AEStronglyMeasurable (F' u) (P L W) :=
    (expected_samplewise_loop_flow_derivative L W hE hu hu1 I hwf).1.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂(P L W), ∀ v ∈ flowWindow u,
      ‖F' v ω‖ ≤ bound ω :=
    Filter.Eventually.of_forall fun ω v hv =>
      norm_samplewise_loop_flow_derivative_le_envelope L W hE hu hu1 I hwf hv ω
  have hbound_int : Integrable bound (P L W) :=
    integrable_flowDerivativeEnvelope L W E u I
  have hdiff : ∀ᵐ ω ∂(P L W), ∀ v ∈ flowWindow u,
      HasDerivAt (F · ω) (F' v ω) v := by
    apply Filter.Eventually.of_forall
    intro ω v hv
    have hv' := flowWindow_subset_Ioo u hu hu1 hv
    have h := hasDerivAt_gloop_HflowBlock_spectralZ L W ω hE hv'.1 hv'.2 I hwf
    have hval : F' v ω = Matrix.trace (loopWordDeriv L W ω E v (I.σ.zip I.a)) :=
      h.deriv
    rw [hval]
    exact h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) hs hF_meas hF_int
    hF'_meas hbound hbound_int hdiff
  exact h.2

/-- Derivative of the expected loop with its exact Gaussian second-coordinate sum. -/
theorem deriv_integral_gloop_HflowBlock_spectralZ
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)) u =
      (1 / (2 * u)) • ∫ ω : Ω L W,
        ∑ c : Coord L W, (gvar L W c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv L W u ω c
            (spectralZ E u) (I.σ.zip I.a)) ∂(P L W) +
      ∫ ω : Ω L W,
        Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))
          ∂(P L W) := by
  rw [(hasDerivAt_integral_gloop_HflowBlock_spectralZ L W hE hu hu1 I hwf).deriv]
  exact (expected_samplewise_loop_flow_derivative L W hE hu hu1 I hwf).2

end RBM.Gauss
