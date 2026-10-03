/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopDerivative

/-!
# One-coordinate derivative of a finite Gaussian resolvent loop

Changing one real Gaussian coordinate moves the Hermitian matrix in the
`coordinateMatrix` direction. The resolvent derivative is `-G B G`, with
`B = √u · coordinateMatrix`, and the loop derivative is a finite Leibniz sum.
No coordinate sum, integration by parts, or generator identity is asserted here.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- A Gaussian coordinate direction in block coordinates. -/
noncomputable def coordinateBlock (c : Coord L W) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  (coordinateMatrix L W c).submatrix (splitEquiv L W).symm (splitEquiv L W).symm

/-- Exact affine dependence of the reindexed matrix on one sample coordinate. -/
theorem HflowBlock_update (u : ℝ) (ω : Ω L W) (c : Coord L W) (t : ℝ) :
    HflowBlock L W u (Function.update ω c t) =
      HflowBlock L W u ω + (Real.sqrt u * (t - ω c)) • coordinateBlock L W c := by
  ext i j
  simp only [HflowBlock, submatrix_apply, Hflow_apply, Matrix.add_apply,
    Matrix.smul_apply, coordinateBlock]
  have h := congrArg (fun M : Matrix (Idx L W) (Idx L W) ℂ =>
    M ((splitEquiv L W).symm i) ((splitEquiv L W).symm j))
    (Xmat_update L W ω c t)
  simp only [Matrix.add_apply, Matrix.smul_apply, Xmat_apply] at h
  rw [h]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- The sample-coordinate derivative of the reindexed matrix. -/
theorem hasDerivAt_HflowBlock_update (u : ℝ) (ω : Ω L W) (c : Coord L W) :
    HasDerivAt (fun t : ℝ => HflowBlock L W u (Function.update ω c t))
      (Real.sqrt u • coordinateBlock L W c) (ω c) := by
  have hscalar : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c))
      (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have hline := (hscalar.smul_const (coordinateBlock L W c)).const_add
    (HflowBlock L W u ω)
  exact hline.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => HflowBlock_update L W u ω c t)

/-- The exact directional resolvent derivative for one real Gaussian coordinate. -/
theorem hasDerivAt_green_HflowBlock_update (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun t : ℝ => green (HflowBlock L W u (Function.update ω c t)) z)
      (let G := green (HflowBlock L W u ω) z;
       -(G * (Real.sqrt u • coordinateBlock L W c) * G)) (ω c) := by
  have h := hasDerivAt_green_moving
    (hasDerivAt_HflowBlock_update L W u ω c)
    (hasDerivAt_const (ω c) z)
    (by simpa only [Function.update_eq_self] using HflowBlock_isHermitian L W u ω)
    hz
  simpa only [Function.update_eq_self, zero_smul, sub_zero] using h

/-- The derivative of either signed Green factor in one coordinate. -/
noncomputable def gsigCoordinateDeriv (u : ℝ) (ω : Ω L W) (c : Coord L W)
    (z : ℂ) (σ : Bool) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  let G := Gsig (HflowBlock L W u ω) z σ;
  -(G * (Real.sqrt u • coordinateBlock L W c) * G)

theorem hasDerivAt_Gsig_HflowBlock_update (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    HasDerivAt
      (fun t : ℝ => Gsig (HflowBlock L W u (Function.update ω c t)) z σ)
      (gsigCoordinateDeriv L W u ω c z σ) (ω c) := by
  cases σ with
  | true =>
      simpa only [Gsig_true, gsigCoordinateDeriv] using
        hasDerivAt_green_HflowBlock_update L W u ω c hz
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      simpa only [Gsig_false, gsigCoordinateDeriv] using
        hasDerivAt_green_HflowBlock_update L W u ω c hz'

/-- Recursive product rule for the finite signed word. -/
noncomputable def coordinateWordDeriv (u : ℝ) (ω : Ω L W) (c : Coord L W)
    (z : ℂ) : List (Bool × Z2 L) →
      Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  | [] => 0
  | p :: l =>
      (gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
        l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1 +
      (Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
        coordinateWordDeriv u ω c z l

theorem hasDerivAt_coordinateWord (u : ℝ) (ω : Ω L W) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L)) :
    HasDerivAt
      (fun t : ℝ => l.foldr (fun p M =>
        Gsig (HflowBlock L W u (Function.update ω c t)) z p.1 * Eblk L W p.2 * M) 1)
      (coordinateWordDeriv L W u ω c z l) (ω c) := by
  induction l with
  | nil =>
      simpa only [List.foldr_nil, coordinateWordDeriv] using
        hasDerivAt_const (ω c) (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have hhead := (hasDerivAt_Gsig_HflowBlock_update L W u ω c hz p.1).mul_const
        (Eblk L W p.2)
      have h := hhead.mul ih
      have hfun :
          (fun t : ℝ => Gsig (HflowBlock L W u (Function.update ω c t)) z p.1 *
            Eblk L W p.2) *
            (fun t : ℝ => l.foldr (fun q M =>
              Gsig (HflowBlock L W u (Function.update ω c t)) z q.1 * Eblk L W q.2 * M) 1) =
          (fun t : ℝ => Gsig (HflowBlock L W u (Function.update ω c t)) z p.1 *
            Eblk L W p.2 * l.foldr (fun q M =>
              Gsig (HflowBlock L W u (Function.update ω c t)) z q.1 * Eblk L W q.2 * M) 1) := by
        funext t
        rfl
      rw [hfun] at h
      have hgoalFun :
          (fun t : ℝ => (p :: l).foldr (fun q M =>
            Gsig (HflowBlock L W u (Function.update ω c t)) z q.1 *
              Eblk L W q.2 * M) 1) =
          (fun t : ℝ => Gsig (HflowBlock L W u (Function.update ω c t)) z p.1 *
            Eblk L W p.2 * l.foldr (fun q M =>
              Gsig (HflowBlock L W u (Function.update ω c t)) z q.1 *
                Eblk L W q.2 * M) 1) := by
        funext t
        rfl
      rw [hgoalFun]
      rw [coordinateWordDeriv]
      simp only [Function.update_eq_self] at h
      exact h

/-- Coordinate derivative of the finite loop matrix product. -/
theorem hasDerivAt_gloopProd_update (u : ℝ) (ω : Ω L W) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (_hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => gloopProd L W (HflowBlock L W u (Function.update ω c t)) z I)
      (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) (ω c) :=
  hasDerivAt_coordinateWord L W u ω c hz (I.σ.zip I.a)

/-- Coordinate derivative of the complete finite loop. -/
theorem hasDerivAt_gloop_update (u : ℝ) (ω : Ω L W) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => gloop L W (HflowBlock L W u (Function.update ω c t)) z I)
      (Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))) (ω c) := by
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
    (hasDerivAt_gloopProd_update L W u ω c hz I hwf)
  simpa only [hT, Function.comp_def, gloop] using h

end RBM.Gauss
