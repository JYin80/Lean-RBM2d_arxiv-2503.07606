/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateDerivativeBounds
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Measurability and integrability of finite-loop coordinate derivatives

At fixed time and nonreal spectral parameter, both recursive coordinate
derivatives are continuous in the sample. Their deterministic norm bounds
make their traces integrable under the finite Gaussian product law.
-/

namespace RBM.Gauss

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The first signed-factor coordinate derivative is sample-continuous. -/
theorem continuous_gsigCoordinateDeriv_sample (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω : Ω L W => gsigCoordinateDeriv L W u ω c z σ := by
  have hG := continuous_Gsig_HflowBlock_sample L W u hz σ
  change Continuous fun ω : Ω L W =>
    -(Gsig (HflowBlock L W u ω) z σ *
      (Real.sqrt u • coordinateBlock L W c) *
        Gsig (HflowBlock L W u ω) z σ)
  exact ((hG.mul continuous_const).mul hG).neg

/-- The second signed-factor coordinate derivative is sample-continuous. -/
theorem continuous_gsigCoordinateSecondDeriv_sample (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω : Ω L W => gsigCoordinateSecondDeriv L W u ω c z σ := by
  have hG := continuous_Gsig_HflowBlock_sample L W u hz σ
  change Continuous fun ω : Ω L W =>
    (2 : ℝ) • (Gsig (HflowBlock L W u ω) z σ *
      (Real.sqrt u • coordinateBlock L W c) *
      Gsig (HflowBlock L W u ω) z σ *
      (Real.sqrt u • coordinateBlock L W c) *
      Gsig (HflowBlock L W u ω) z σ)
  exact (continuous_const : Continuous fun _ : Ω L W => (2 : ℝ)).smul
    ((((hG.mul continuous_const).mul hG).mul continuous_const).mul hG)

/-- The recursive first word derivative is sample-continuous. -/
theorem continuous_coordinateWordDeriv_sample (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L)) :
    Continuous fun ω : Ω L W => coordinateWordDeriv L W u ω c z l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact (((continuous_gsigCoordinateDeriv_sample L W u c hz p.1).mul
        continuous_const).mul (continuous_foldr_HflowBlock_sample L W u hz l)).add
        (((continuous_Gsig_HflowBlock_sample L W u hz p.1).mul
          continuous_const).mul ih)

/-- The recursive second word derivative is sample-continuous. -/
theorem continuous_coordinateSecondWordDeriv_sample (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L)) :
    Continuous fun ω : Ω L W => coordinateSecondWordDeriv L W u ω c z l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hD := continuous_coordinateWordDeriv_sample L W u c hz l
      have hG := continuous_Gsig_HflowBlock_sample L W u hz p.1
      have hDsig := continuous_gsigCoordinateDeriv_sample L W u c hz p.1
      have hSsig := continuous_gsigCoordinateSecondDeriv_sample L W u c hz p.1
      exact (((hSsig.mul continuous_const).mul
        (continuous_foldr_HflowBlock_sample L W u hz l)).add
        ((hDsig.mul continuous_const).mul hD)).add
        (((hDsig.mul continuous_const).mul hD).add
        ((hG.mul continuous_const).mul ih))

/-- Both traced coordinate-derivative observables are measurable. -/
theorem measurable_gloop_coordinate_derivatives_sample (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    Measurable (fun ω : Ω L W =>
      Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))) ∧
    Measurable (fun ω : Ω L W =>
      Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) := by
  constructor
  · exact ((continuous_matrixTrace L W).comp
      (continuous_coordinateWordDeriv_sample L W u c hz _)).measurable
  · exact ((continuous_matrixTrace L W).comp
      (continuous_coordinateSecondWordDeriv_sample L W u c hz _)).measurable

/-- Both traced derivatives are integrable under the Gaussian product law. -/
theorem integrable_gloop_coordinate_derivatives (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Integrable (fun ω : Ω L W =>
      Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))) (P L W) ∧
    Integrable (fun ω : Ω L W =>
      Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)))
      (P L W) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hm := measurable_gloop_coordinate_derivatives_sample L W u c hz I
  constructor
  · exact Integrable.of_bound hm.1.aestronglyMeasurable
      ((((L * W) ^ 2 : ℕ) : ℝ) *
        coordinateFirstWordBound L W u |z.im| c I.a.length)
      (Filter.Eventually.of_forall fun ω =>
        (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).1)
  · exact Integrable.of_bound hm.2.aestronglyMeasurable
      ((((L * W) ^ 2 : ℕ) : ℝ) *
        coordinateSecondWordBound L W u |z.im| c I.a.length)
      (Filter.Eventually.of_forall fun ω =>
        (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).2)

/-- The actual first coordinate derivative agrees with the recursive expression. -/
theorem deriv_gloop_coordinate_eq (u : ℝ) (ω : Ω L W) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun t : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c t)) z I) (ω c) =
      Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) :=
  (hasDerivAt_gloop_update L W u ω c hz I hwf).deriv

/-- The actual second coordinate derivative agrees with the recursive expression. -/
theorem deriv_deriv_gloop_coordinate_eq (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c s)) z I) t) (ω c) =
      Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)) :=
  (hasDerivAt_deriv_gloop_update L W u ω c hz I hwf).deriv

/-- Actual first and second coordinate derivatives are measurable and integrable. -/
theorem measurable_integrable_actual_gloop_coordinate_derivatives
    (u : ℝ) (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    let D₁ : Ω L W → ℂ := fun ω => deriv (fun t : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c t)) z I) (ω c)
    let D₂ : Ω L W → ℂ := fun ω => deriv (fun t : ℝ => deriv (fun s : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c s)) z I) t) (ω c)
    Measurable D₁ ∧ Integrable D₁ (P L W) ∧
      Measurable D₂ ∧ Integrable D₂ (P L W) := by
  have hD₁ : (fun ω : Ω L W => deriv (fun t : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c t)) z I) (ω c)) =
      (fun ω : Ω L W => Matrix.trace
        (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))) := by
    funext ω
    exact deriv_gloop_coordinate_eq L W u ω c hz I hwf
  have hD₂ : (fun ω : Ω L W => deriv (fun t : ℝ => deriv (fun s : ℝ =>
      gloop L W (HflowBlock L W u (Function.update ω c s)) z I) t) (ω c)) =
      (fun ω : Ω L W => Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) := by
    funext ω
    exact deriv_deriv_gloop_coordinate_eq L W u ω c hz I hwf
  dsimp
  rw [hD₁, hD₂]
  obtain ⟨hm₁, hm₂⟩ := measurable_gloop_coordinate_derivatives_sample L W u c hz I
  obtain ⟨hi₁, hi₂⟩ := integrable_gloop_coordinate_derivatives L W u c hz I hwf
  exact ⟨hm₁, hi₁, hm₂, hi₂⟩

end RBM.Gauss
