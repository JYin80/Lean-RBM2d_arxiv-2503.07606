/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Model
import RBM2D.Gauss.SteinMatrix

/-!
# Stein identity for the concrete Hermitian band matrix

The independent real coordinates have variances `gvar L W c`, including zero variance.
The fibre derivative below is the directional derivative along `coordinateMatrix L W c`.
The same statement applies to `Hflow u` with direction `√u • coordinateMatrix L W c`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- Resampling coordinate `c` from its own Gaussian law leaves the concrete matrix
sample law invariant, even when its variance is zero. -/
theorem P_map_update (c : Coord L W) :
    ((P L W).prod (gaussianReal 0 (gvar L W c))).map
        (GaussianProduct.update c) = P L W :=
  GaussianProduct.map_update (gvar L W) c

/-- A one-coordinate replacement changes the flow in its exact Hermitian direction. -/
theorem Hflow_update (u : ℝ) (ω : Ω L W) (c : Coord L W) (t : ℝ) :
    Hflow L W u (Function.update ω c t) =
      Hflow L W u ω + (t - ω c) • (Real.sqrt u • coordinateMatrix L W c) := by
  rw [Hflow_eq_realSmul, Xmat_update, smul_add,
    Hflow_eq_realSmul, smul_comm]

/-- Matrix-functional Stein identity at one fixed size. The hypotheses are global
continuity, boundedness, and the indicated directional derivative along the actual
matrix fibre. Zero-variance coordinates are included. -/
theorem stein_Xmat (c : Coord L W)
    (F F' : Matrix (Idx L W) (Idx L W) ℂ → ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ =>
        F (Xmat L W ω + (t - ω c) • coordinateMatrix L W c))
        (F' (Xmat L W ω)) (ω c))
    (hFb : ∃ C : ℝ, ∀ ω : Ω L W, ‖F (Xmat L W ω)‖ ≤ C)
    (hF'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖F' (Xmat L W ω)‖ ≤ C) :
    ∫ ω, ω c • F (Xmat L W ω) ∂(P L W) =
      (gvar L W c : ℝ) • ∫ ω, F' (Xmat L W ω) ∂(P L W) := by
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [hlaw]
  apply GaussianProduct.stein (gvar L W) c
    (fun ω => F (Xmat L W ω)) (fun ω => F' (Xmat L W ω))
    (hF.comp (continuous_Xmat L W)) (hF'.comp (continuous_Xmat L W))
  · intro ω
    simpa only [Xmat_update] using hderiv ω
  · exact hFb
  · exact hF'b

/-- The fixed-time version, with the exact `√u` coordinate direction. -/
theorem stein_Hflow (u : ℝ) (c : Coord L W)
    (F F' : Matrix (Idx L W) (Idx L W) ℂ → ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ =>
        F (Hflow L W u ω + (t - ω c) •
          (Real.sqrt u • coordinateMatrix L W c)))
        (F' (Hflow L W u ω)) (ω c))
    (hFb : ∃ C : ℝ, ∀ ω : Ω L W, ‖F (Hflow L W u ω)‖ ≤ C)
    (hF'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖F' (Hflow L W u ω)‖ ≤ C) :
    ∫ ω, ω c • F (Hflow L W u ω) ∂(P L W) =
      (gvar L W c : ℝ) • ∫ ω, F' (Hflow L W u ω) ∂(P L W) := by
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [hlaw]
  apply GaussianProduct.stein (gvar L W) c
    (fun ω => F (Hflow L W u ω)) (fun ω => F' (Hflow L W u ω))
    (hF.comp (continuous_Hflow L W u)) (hF'.comp (continuous_Hflow L W u))
  · intro ω
    simpa only [Hflow_update] using hderiv ω
  · exact hFb
  · exact hF'b

@[simp] theorem Xmat_diag (ω : Ω L W) (i : Idx L W) :
    Xmat L W ω i i = (ω (i, i, true) : ℂ) := by
  simp [Xmat_apply, Xentry]

/-- A nonconstant test of the actual diagonal matrix entry, with variance `1/5`.
This uses the positive-variance coordinate `(i,i,true)` of the model. -/
theorem stein_diagonal_sin_example :
    let i : Idx 3 1 := (0, 0)
    let c : Coord 3 1 := (i, i, true)
    (∫ ω, ω c • (↑(Real.sin (Complex.re (Xmat 3 1 ω i i))) : ℂ) ∂(P 3 1)) =
      (5 : ℝ)⁻¹ •
        ∫ ω, (↑(Real.cos (Complex.re (Xmat 3 1 ω i i))) : ℂ) ∂(P 3 1) := by
  let i : Idx 3 1 := (0, 0)
  let c : Coord 3 1 := (i, i, true)
  let F : Matrix (Idx 3 1) (Idx 3 1) ℂ → ℂ :=
    fun A => ↑(Real.sin (Complex.re (A i i)))
  let F' : Matrix (Idx 3 1) (Idx 3 1) ℂ → ℂ :=
    fun A => ↑(Real.cos (Complex.re (A i i)))
  have heval : Continuous (fun A : Matrix (Idx 3 1) (Idx 3 1) ℂ => A i i) :=
    (continuous_apply i).comp (continuous_apply i)
  have hre : Continuous (fun A : Matrix (Idx 3 1) (Idx 3 1) ℂ => (A i i).re) :=
    Complex.continuous_re.comp heval
  have hF : Continuous F :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hre)
  have hF' : Continuous F' :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hre)
  have hd : ∀ ω : Ω 3 1,
      HasDerivAt (fun t : ℝ =>
        F (Xmat 3 1 ω + (t - ω c) • coordinateMatrix 3 1 c))
        (F' (Xmat 3 1 ω)) (ω c) := by
    intro ω
    have hpath (t : ℝ) :
        F (Xmat 3 1 ω + (t - ω c) • coordinateMatrix 3 1 c) =
          (↑(Real.sin t) : ℂ) := by
      rw [← Xmat_update]
      simp only [F, Xmat_diag, Complex.ofReal_re]
      simp [c]
    have hpoint : F' (Xmat 3 1 ω) = (↑(Real.cos (ω c)) : ℂ) := by
      simp only [F', Xmat_diag, Complex.ofReal_re]
      rfl
    simpa only [hpath, hpoint] using (Real.hasDerivAt_sin (ω c)).ofReal_comp
  have hb : ∃ C : ℝ, ∀ ω : Ω 3 1, ‖F (Xmat 3 1 ω)‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [F, Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_sin_le_one (Complex.re (Xmat 3 1 ω i i))
  have hb' : ∃ C : ℝ, ∀ ω : Ω 3 1, ‖F' (Xmat 3 1 ω)‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [F', Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_cos_le_one (Complex.re (Xmat 3 1 ω i i))
  have hv : (gvar 3 1 c : ℝ) = (5 : ℝ)⁻¹ := by
    simp [c, gvar_diag, svar_diag]
  simpa only [i, c, F, F', hv] using stein_Xmat 3 1 c F F' hF hF' hd hb hb'

end RBM.Gauss
