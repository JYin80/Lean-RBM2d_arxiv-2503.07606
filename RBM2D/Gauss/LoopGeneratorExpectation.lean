/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopExpectationDerivative
import RBM2D.Gauss.LoopGeneratorSamplewise

/-!
# Expected finite-loop cut expression

The derivative of the expected loop is the expectation of the finite
samplewise cut expression. The separate cut families remain inside one integral.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The samplewise finite cut expression is integrable under the product Gaussian law. -/
theorem integrable_samplewiseLoopGeneratorCuts
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hI : I.WF) :
    Integrable (fun ω : Ω L W => samplewiseLoopGeneratorCuts L W ω E u I)
      (P L W) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hcoord : Integrable (fun ω : Ω L W =>
      ∑ c : Coord L W, (gvar L W c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv L W u ω c
          (spectralZ E u) (I.σ.zip I.a))) (P L W) := by
    apply integrable_finsetSum univ
    intro c _
    exact ((integrable_gloop_coordinate_derivatives L W u c hz I hI).2).smul
      (gvar L W c : ℝ)
  have hspec : Integrable (fun ω : Ω L W =>
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))) (P L W) :=
    integrable_trace_spectralWordDeriv L W E u hE hu1 (I.σ.zip I.a)
  have hsum := (hcoord.smul (1 / (2 * u))).add hspec
  have hscale : ((1 / (2 * u) : ℝ) : ℂ) = 1 / (2 * (u : ℂ)) := by norm_cast
  have hfun : (fun ω : Ω L W => samplewiseLoopGeneratorCuts L W ω E u I) =
      (fun ω : Ω L W => (1 / (2 * u)) •
        (∑ c : Coord L W, (gvar L W c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv L W u ω c
            (spectralZ E u) (I.σ.zip I.a))) +
        Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))) := by
    funext ω
    have h := samplewise_loop_generator_eq_cuts L W ω (E := E) hu hu1 I hI
    simpa only [Complex.real_smul, hscale] using h.symm
  rw [hfun]
  exact hsum

/-- Derivative of the expected loop as one expectation of its finite cut expression. -/
theorem deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hI : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)) u =
      ∫ ω : Ω L W, samplewiseLoopGeneratorCuts L W ω E u I ∂(P L W) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hcoord : Integrable (fun ω : Ω L W =>
      ∑ c : Coord L W, (gvar L W c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv L W u ω c
          (spectralZ E u) (I.σ.zip I.a))) (P L W) := by
    apply integrable_finsetSum univ
    intro c _
    exact ((integrable_gloop_coordinate_derivatives L W u c hz I hI).2).smul
      (gvar L W c : ℝ)
  have hspec : Integrable (fun ω : Ω L W =>
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))) (P L W) :=
    integrable_trace_spectralWordDeriv L W E u hE hu1 (I.σ.zip I.a)
  have hscaled : Integrable (fun ω : Ω L W => (1 / (2 * u)) •
      ∑ c : Coord L W, (gvar L W c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv L W u ω c
          (spectralZ E u) (I.σ.zip I.a))) (P L W) :=
    hcoord.smul (1 / (2 * u))
  have hscale : ((1 / (2 * u) : ℝ) : ℂ) = 1 / (2 * (u : ℂ)) := by norm_cast
  calc
    _ = (1 / (2 * u)) • ∫ ω : Ω L W,
          ∑ c : Coord L W, (gvar L W c : ℝ) •
            Matrix.trace (coordinateSecondWordDeriv L W u ω c
              (spectralZ E u) (I.σ.zip I.a)) ∂(P L W) +
        ∫ ω : Ω L W,
          Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))
            ∂(P L W) :=
      deriv_integral_gloop_HflowBlock_spectralZ L W hE hu hu1 I hI
    _ = ∫ ω : Ω L W,
          (1 / (2 * u)) •
            (∑ c : Coord L W, (gvar L W c : ℝ) •
              Matrix.trace (coordinateSecondWordDeriv L W u ω c
                (spectralZ E u) (I.σ.zip I.a))) +
          Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))
            ∂(P L W) := by
      rw [integral_add hscaled hspec, integral_smul]
    _ = _ := by
      congr 1
      funext ω
      have h := samplewise_loop_generator_eq_cuts L W ω (E := E) hu hu1 I hI
      simpa only [Complex.real_smul, hscale] using h

end RBM.Gauss
