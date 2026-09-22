/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.FlowDerivative
import RBM2D.Gauss.SpectralDerivative
import RBM2D.Gauss.LoopTimeCont

/-!
# Derivative of a resolvent along the samplewise spectral flow

This is a fixed-sample chain rule. The Gaussian coupling used here has the correct
one-time marginals but is not a matrix Brownian motion; no generator identity is claimed.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Chain rule for a non-real resolvent with both matrix and spectral parameter moving. -/
theorem hasDerivAt_green_moving {H : ℝ → Matrix n n ℂ} {z : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {u : ℝ}
    (hH : HasDerivAt H H' u) (hz : HasDerivAt z z' u)
    (hHerm : (H u).IsHermitian) (him : (z u).im ≠ 0) :
    HasDerivAt (fun v : ℝ => green (H v) (z v))
      (-(green (H u) (z u) * (H' - z' • (1 : Matrix n n ℂ)) *
        green (H u) (z u))) u := by
  have hU : IsUnit (H u - z u • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hHerm him
  set U : (Matrix n n ℂ)ˣ := hU.unit with hUdef
  have hus : (U : Matrix n n ℂ) = H u - z u • (1 : Matrix n n ℂ) :=
    IsUnit.unit_spec _
  have hinv : ((U⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = green (H u) (z u) := by
    rw [green, Matrix.nonsing_inv_eq_ringInverse, ← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      (H u - z u • (1 : Matrix n n ℂ)) := by
    rw [← hus]
    exact hasFDerivAt_ringInverse U
  have hpath : HasDerivAt (fun v : ℝ => H v - z v • (1 : Matrix n n ℂ))
      (H' - z' • (1 : Matrix n n ℂ)) u :=
    hH.sub (hz.smul_const (1 : Matrix n n ℂ))
  have hcomp := hF.comp_hasDerivAt u hpath
  have hval :
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
        (H' - z' • (1 : Matrix n n ℂ)) =
      -(green (H u) (z u) * (H' - z' • (1 : Matrix n n ℂ)) *
        green (H u) (z u)) := by
    simp [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinv]
  rw [hval] at hcomp
  have hfun : (fun v : ℝ => green (H v) (z v)) =
      (Ring.inverse (M₀ := Matrix n n ℂ)) ∘
        (fun v : ℝ => H v - z v • (1 : Matrix n n ℂ)) := by
    funext v
    simp [green, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  exact hcomp

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The reindexed Gaussian flow has the same square-root derivative. -/
theorem hasDerivAt_HflowBlock_time (ω : Ω L W) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => HflowBlock L W v ω)
      ((1 / (2 * Real.sqrt u)) •
        (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm) u := by
  have hfun : (fun v : ℝ => HflowBlock L W v ω) =
      fun v : ℝ => Real.sqrt v •
        (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm := by
    funext v
    ext i j
    simp only [HflowBlock, submatrix_apply, Hflow_apply, Matrix.smul_apply,
      Complex.real_smul, Xmat_apply]
  rw [hfun]
  exact (Real.hasDerivAt_sqrt hu.ne').smul_const _

/-- Fixed-sample Green derivative along `H_u=√u X` and `z_u=E+(1-u)m^(E)`.
The sign follows from differentiating `(H_u-z_u I)⁻¹`. -/
theorem hasDerivAt_green_HflowBlock_spectralZ (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt
      (fun v : ℝ => green (HflowBlock L W v ω) (spectralZ E v))
      (-(green (HflowBlock L W u ω) (spectralZ E u) *
        ((1 / (2 * Real.sqrt u)) •
          (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm +
          spectralM E • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
        green (HflowBlock L W u ω) (spectralZ E u))) u := by
  have him : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have h := hasDerivAt_green_moving
    (hasDerivAt_HflowBlock_time L W ω hu)
    (hasDerivAt_spectralZ E u)
    (HflowBlock_isHermitian L W u ω) him
  simpa only [neg_smul, sub_neg_eq_add] using h

/-- Even at the zero matrix sample, the moving spectral parameter gives a nonzero
resolvent derivative at the center of the bulk. -/
example : ∃ D : Matrix (BlockIndex 1 1) (BlockIndex 1 1) ℂ,
    D ≠ 0 ∧
      HasDerivAt
        (fun v : ℝ => green (HflowBlock 1 1 v (0 : Ω 1 1)) (spectralZ 0 v))
        D (1 / 2) := by
  let G : Matrix (BlockIndex 1 1) (BlockIndex 1 1) ℂ :=
    green (HflowBlock 1 1 (1 / 2) (0 : Ω 1 1)) (spectralZ 0 (1 / 2))
  let D : Matrix (BlockIndex 1 1) (BlockIndex 1 1) ℂ :=
    -(G * (spectralM 0 • (1 : Matrix (BlockIndex 1 1) (BlockIndex 1 1) ℂ)) * G)
  have hX : Xmat 1 1 (0 : Ω 1 1) = 0 := by
    ext i j
    simp [Xmat, Xentry]
  have hD : HasDerivAt
      (fun v : ℝ => green (HflowBlock 1 1 v (0 : Ω 1 1)) (spectralZ 0 v)) D
      (1 / 2) := by
    have h := hasDerivAt_green_HflowBlock_spectralZ 1 1 (0 : Ω 1 1)
      (by norm_num : |(0 : ℝ)| < 2)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [D, G, hX] using h
  have him : (spectralZ 0 (1 / 2)).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by norm_num) (spectralM_im_pos (by norm_num)))
  have hG : IsUnit G := by
    dsimp [G, green]
    rw [Matrix.isUnit_nonsing_inv_iff]
    exact isUnit_sub_smul_one_of_im_ne_zero
      (HflowBlock_isHermitian 1 1 (1 / 2) 0) him
  have hm : spectralM 0 ≠ 0 := by
    intro hm0
    have := spectralM_im_pos (by norm_num : |(0 : ℝ)| < 2)
    rw [hm0, Complex.zero_im] at this
    exact (lt_irrefl _ this)
  have hmid : IsUnit (spectralM 0 • (1 : Matrix (BlockIndex 1 1) (BlockIndex 1 1) ℂ)) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr hm
  have hD0 : D ≠ 0 := by
    exact ((hG.mul hmid).mul hG).neg.ne_zero
  exact ⟨D, hD0, hD⟩

end RBM.Gauss
