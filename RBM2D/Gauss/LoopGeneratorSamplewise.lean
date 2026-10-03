/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopAllCuts
import RBM2D.Gauss.LoopSpectralDriftCuts

/-!
# Samplewise finite-loop cut expression

The coordinate Hessian cuts and the spectral drift cuts are combined here only
as a finite algebraic identity at one Gaussian sample.
-/

namespace RBM.Gauss

open Matrix Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The finite cut-loop expression at one sample, with exact second-coordinate
and signed spectral-drift coefficients. -/
noncomputable def samplewiseLoopGeneratorCuts (ω : Ω L W) (E u : ℝ)
    (I : LoopIdx (Z2 L)) : ℂ :=
  let l := I.σ.zip I.a
  let z := spectralZ E u
  (W : ℂ) ^ 2 *
    (((edgeSplits l).map (sameEdgeCutValue L W u ω z)).sum +
      ((pairSplits l).map (pairCutValue L W u ω z)).sum) +
  ((spectralEdgeSplits L l).map fun s =>
    -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
      ∑ b : Z2 L,
        gloop L W (HflowBlock L W u ω) z
          (I.cutGlue (s.pre.length + 1) b)).sum

/-- The flow Hessian and spectral drift equal the corresponding finite cut sums.
This is a samplewise algebraic statement; it does not interchange expectation
and differentiation. -/
theorem samplewise_loop_generator_eq_cuts
    (ω : Ω L W) {E u : ℝ} (hu : 0 < u) (_hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hI : I.WF) :
    (1 / (2 * (u : ℂ))) *
        ∑ γ : Coord L W,
          (((gvar L W γ : ℝ) : ℂ) *
            Matrix.trace (coordinateSecondWordDeriv L W u ω γ
              (spectralZ E u) (I.σ.zip I.a))) +
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) =
        samplewiseLoopGeneratorCuts L W ω E u I := by
  have hsecond := sum_coordinateSecondWordDeriv_allCuts L W u hu.le ω
    (spectralZ E u) (I.σ.zip I.a)
  have hdrift := trace_spectralWordDeriv_eq_sum_original_cuts L W ω E u I hI
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  rw [hsecond, hdrift]
  unfold samplewiseLoopGeneratorCuts
  field_simp

end RBM.Gauss
