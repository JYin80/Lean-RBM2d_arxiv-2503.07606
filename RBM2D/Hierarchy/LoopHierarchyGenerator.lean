/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopExpectedCuts
import RBM2D.Gauss.LoopSpectralDriftExpectation
import RBM2D.Gauss.LoopGeneratorExpectation

/-!
# The finite expected loop hierarchy ODE

This is the complete finite-loop generator at nonreal spectral parameter.
The later convolution/tree estimates are separate.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Expected products from same-edge second-derivative cuts. -/
noncomputable def expectedSameEdgeCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  ((edgeSplits (I.σ.zip I.a)).map (fun e => ∑ p : Z2 L, ∑ q : Z2 L,
    ∫ ω : Ω L W,
      sameEdgeCutIntegrand L W u ω (spectralZ E u) e p q ∂(P L W))).sum

/-- Expected products from distinct-edge second-derivative cuts. -/
noncomputable def expectedPairCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  ((pairSplits (I.σ.zip I.a)).map (fun p => ∑ v : Z2 L, ∑ w : Z2 L,
    ∫ ω : Ω L W,
      pairCutIntegrand L W u ω (spectralZ E u) p v w ∂(P L W))).sum

/-- The signed, expected single-edge cuts from spectral motion. -/
noncomputable def expectedSpectralCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  ((spectralEdgeSplits (L := L) (I.σ.zip I.a)).map fun s =>
    -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
      ∑ b : Z2 L, ∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          (I.cutGlue (s.pre.length + 1) b) ∂(P L W)).sum

/-- Finite-loop hierarchy ODE: both Gaussian cut families have coefficient
`W²` after the Ornstein-Uhlenbeck factor `1/(2u)` cancels `2u`, while the
single-edge spectral cuts retain their signed coefficient. -/
theorem deriv_expected_gloop_eq_hierarchyCuts
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I ∂(P L W)) u =
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hHess := integral_coordinateSecondWordDeriv_allCuts L W u hu hz (I.σ.zip I.a)
  have hDrift := integral_trace_spectralWordDeriv_eq_sum_expected_cuts
    L W hE hu hu1 I hwf
  have hcoord :
      (fun ω : Ω L W => ∑ c : Coord L W, (gvar L W c : ℝ) •
        Matrix.trace (coordinateSecondWordDeriv L W u ω c
          (spectralZ E u) (I.σ.zip I.a))) =
      (fun ω : Ω L W => ∑ c : Coord L W, (((gvar L W c : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω c
          (spectralZ E u) (I.σ.zip I.a)))) := by
    funext ω
    apply Finset.sum_congr rfl
    intro c _
    exact Complex.real_smul
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hscale : ((1 / (2 * u) : ℝ) : ℂ) = 1 / (2 * (u : ℂ)) := by norm_cast
  calc
    _ = (1 / (2 * u)) • ∫ ω : Ω L W,
          ∑ c : Coord L W, (gvar L W c : ℝ) •
            Matrix.trace (coordinateSecondWordDeriv L W u ω c
              (spectralZ E u) (I.σ.zip I.a)) ∂(P L W) +
        ∫ ω : Ω L W,
          Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))
            ∂(P L W) :=
      deriv_integral_gloop_HflowBlock_spectralZ L W hE hu hu1 I hwf
    _ = (1 / (2 * (u : ℂ))) *
          ((2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
           (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 * expectedPairCuts L W E u I) +
        expectedSpectralCuts L W E u I := by
      rw [hcoord, hHess, hDrift]
      simp only [Complex.real_smul, expectedSameEdgeCuts,
        expectedPairCuts, expectedSpectralCuts]
      rw [hscale]
    _ = _ := by
      field_simp

end RBM.Gauss
