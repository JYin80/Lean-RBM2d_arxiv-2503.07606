/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.SteinConcrete
import RBM2D.Gauss.LoopCoordinateIntegrability

/-!
# One-coordinate Stein identity for a finite resolvent loop

The product Gaussian coordinate has its exact model variance, including zero
variance. The loop's derivative already contains the `√u` matrix direction.
-/

namespace RBM.Gauss

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Gaussian integration by parts in one coordinate of a finite loop. -/
theorem stein_gloop_HflowBlock (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∫ ω, ω c • gloop L W (HflowBlock L W u ω) z I ∂(P L W) =
      (gvar L W c : ℝ) • ∫ ω,
        Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
          ∂(P L W) := by
  let g : Ω L W → ℂ := fun ω => gloop L W (HflowBlock L W u ω) z I
  let g' : Ω L W → ℂ := fun ω =>
    Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
  have hgc : Continuous g := continuous_gloop_HflowBlock_sample L W u hz I hwf
  have hg'c : Continuous g' :=
    (continuous_matrixTrace L W).comp
      (continuous_coordinateWordDeriv_sample L W u c hz _)
  have hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    exact hasDerivAt_gloop_update L W u ω c hz I hwf
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω : Ω L W, ‖g ω‖ ≤ C := by
    refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
      (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length, ?_⟩
    intro ω
    exact norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
      hη le_rfl I hwf
  have hg'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖g' ω‖ ≤ C := by
    refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
      coordinateFirstWordBound L W u |z.im| c I.a.length, ?_⟩
    intro ω
    exact (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).1
  have h := GaussianProduct.stein (gvar L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [hlaw]
  exact h

end RBM.Gauss
