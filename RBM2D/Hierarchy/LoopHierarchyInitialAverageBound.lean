/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyFromInitialBound
import RBM2D.Gauss.LoopInitialValueGeneralLabelSum

/-!
# Summing the finite expected-loop bound over block labels

For a fixed signed word of positive length, every block-label assignment
defines a well-formed loop. The exact sum of initial norms leaves only the
`L²` constant assignments; the time-dependent error remains an explicit
finite sum of the honest hierarchy envelopes for those assignments.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Sum over all block labels of a fixed signed word: the initial part is
evaluated exactly, while each finite-time envelope retains its own labels
and pair cuts. -/
theorem sum_norm_expected_gloop_ofFn_le_initial_add_envelopes
    (hL : 3 ≤ L) {n : ℕ} (hn : 0 < n)
    (σ : List Bool) (hσ : σ.length = n)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    (∑ f : Fin n → Z2 L,
      ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          ⟨σ, List.ofFn f⟩ ∂(P L W)‖) ≤
      (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * (n - 1)) +
      (∑ f : Fin n → Z2 L,
        loopHierarchyUniformEnvelope L W η E ⟨σ, List.ofFn f⟩) * u := by
  have hwf (f : Fin n → Z2 L) :
      (⟨σ, List.ofFn f⟩ : LoopIdx (Z2 L)).WF := by
    simp [LoopIdx.WF, hσ]
  have hinit :
      (∑ f : Fin n → Z2 L,
        ‖totalInitialLoopScalar L W E ⟨σ, List.ofFn f⟩‖) =
      (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * (n - 1)) := by
    calc
      _ = ∑ f : Fin n → Z2 L,
          ‖initialLoopValue L W E ⟨σ, List.ofFn f⟩‖ := by
            apply Finset.sum_congr rfl
            intro f hf
            exact (congrArg norm (initialLoopValue_eq_total L W hE
              ⟨σ, List.ofFn f⟩ (hwf f))).symm
      _ = _ := sum_norm_initialLoopValue_fin L W hE hn σ hσ
  calc
    _ ≤ ∑ f : Fin n → Z2 L,
          (‖totalInitialLoopScalar L W E ⟨σ, List.ofFn f⟩‖ +
            loopHierarchyUniformEnvelope L W η E ⟨σ, List.ofFn f⟩ * u) := by
            apply Finset.sum_le_sum
            intro f hf
            exact norm_expected_gloop_le_initial_add_envelope L W hL
              ⟨σ, List.ofFn f⟩ (hwf f) hE hu0 hu1 hη hz
    _ = (∑ f : Fin n → Z2 L,
          ‖totalInitialLoopScalar L W E ⟨σ, List.ofFn f⟩‖) +
        (∑ f : Fin n → Z2 L,
          loopHierarchyUniformEnvelope L W η E ⟨σ, List.ofFn f⟩ * u) := by
            rw [Finset.sum_add_distrib]
    _ = _ := by rw [hinit, ← Finset.sum_mul]

/-- The same finite label average with the spectral path's uniform gap
`(1-u) Im m(E)` on `[0,u]`. -/
theorem sum_norm_expected_gloop_ofFn_le_pathGap
    (hL : 3 ≤ L) {n : ℕ} (hn : 0 < n)
    (σ : List Bool) (hσ : σ.length = n)
    {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑ f : Fin n → Z2 L,
      ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          ⟨σ, List.ofFn f⟩ ∂(P L W)‖) ≤
      (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * (n - 1)) +
      (∑ f : Fin n → Z2 L,
        loopHierarchyUniformEnvelope L W
          ((1 - u) * (spectralM E).im) E ⟨σ, List.ofFn f⟩) * u := by
  have hη : 0 < (1 - u) * (spectralM E).im :=
    mul_pos (by linarith) (spectralM_im_pos hE)
  exact sum_norm_expected_gloop_ofFn_le_initial_add_envelopes
    L W hL hn σ hσ hE hu0 hu1 hη
    (fun v hv => spectralZ_im_gap hE hu1 hv)

end RBM.Gauss
