/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateStein

/-!
# Finite sum of Gaussian coordinate identities for a resolvent loop

The exact coordinate variances remain inside the finite weighted derivative sum.
This is a fixed-time identity; no time generator is asserted.
-/

namespace RBM.Gauss

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The coordinate weighted loop is integrable under the product Gaussian law. -/
theorem integrable_coord_smul_gloop (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Integrable (fun ω : Ω L W =>
      ω c • gloop L W (HflowBlock L W u ω) z I) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gvar L W c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (P L W) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hC : ∀ ω : Ω L W,
      ‖gloop L W (HflowBlock L W u ω) z I‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) *
          (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by
    intro ω
    exact norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
      hη le_rfl I hwf
  have h := hcoord.ofReal.bdd_mul
    (measurable_gloop_HflowBlock_sample L W u hz I hwf).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)
  simpa [Complex.real_smul, mul_comm] using h

/-- Summed Stein identity, with the finite weighted derivative sum inside expectation. -/
theorem stein_gloop_HflowBlock_sum (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∫ ω : Ω L W,
      ∑ c : Coord L W, ω c • gloop L W (HflowBlock L W u ω) z I
        ∂(P L W) =
    ∫ ω : Ω L W,
      ∑ c : Coord L W, (gvar L W c : ℝ) •
        Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
        ∂(P L W) := by
  classical
  have hleft (c : Coord L W) : Integrable (fun ω : Ω L W =>
      ω c • gloop L W (HflowBlock L W u ω) z I) (P L W) :=
    integrable_coord_smul_gloop L W u c hz I hwf
  have hright (c : Coord L W) : Integrable (fun ω : Ω L W =>
      (gvar L W c : ℝ) •
        Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)))
      (P L W) := by
    exact ((integrable_gloop_coordinate_derivatives L W u c hz I hwf).1).smul
      (gvar L W c : ℝ)
  calc
    ∫ ω : Ω L W,
        ∑ c : Coord L W, ω c • gloop L W (HflowBlock L W u ω) z I
          ∂(P L W) =
        ∑ c : Coord L W, ∫ ω : Ω L W,
          ω c • gloop L W (HflowBlock L W u ω) z I ∂(P L W) := by
            exact integral_finsetSum univ (fun c _ => hleft c)
    _ = ∑ c : Coord L W, (gvar L W c : ℝ) • ∫ ω : Ω L W,
          Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
            ∂(P L W) := by
          apply sum_congr rfl
          intro c _
          exact stein_gloop_HflowBlock L W u c hz I hwf
    _ = ∑ c : Coord L W, ∫ ω : Ω L W,
          (gvar L W c : ℝ) •
            Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
              ∂(P L W) := by simp only [integral_smul]
    _ = ∫ ω : Ω L W,
          ∑ c : Coord L W, (gvar L W c : ℝ) •
            Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
              ∂(P L W) := by
          exact (integral_finsetSum univ (fun c _ => hright c)).symm

end RBM.Gauss
