/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.GreenCoordinateSecondDerivative

/-!
# Second coordinate derivative of a finite resolvent loop

The recursive formula is the finite second product rule. The coordinate and
spectral parameter are fixed; no expectation or generator identity is used.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Second derivative of one signed Green factor in a real Gaussian coordinate. -/
noncomputable def gsigCoordinateSecondDeriv (u : ℝ) (ω : Ω L W)
    (c : Coord L W) (z : ℂ) (σ : Bool) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  let G := Gsig (HflowBlock L W u ω) z σ
  let B := Real.sqrt u • coordinateBlock L W c
  (2 : ℝ) • (G * B * G * B * G)

theorem hasDerivAt_gsigCoordinateDeriv_update (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    HasDerivAt
      (fun t : ℝ => gsigCoordinateDeriv L W u (Function.update ω c t) c z σ)
      (gsigCoordinateSecondDeriv L W u ω c z σ) (ω c) := by
  cases σ with
  | true =>
      simpa only [gsigCoordinateDeriv, gsigCoordinateSecondDeriv, Gsig_true] using
        hasDerivAt_greenCoordinateDerivative L W u ω c hz
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      simpa only [gsigCoordinateDeriv, gsigCoordinateSecondDeriv, Gsig_false] using
        hasDerivAt_greenCoordinateDerivative L W u ω c hz'

/-- Recursive second product rule, including both mixed terms. -/
noncomputable def coordinateSecondWordDeriv (u : ℝ) (ω : Ω L W)
    (c : Coord L W) (z : ℂ) : List (Bool × Z2 L) →
      Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  | [] => 0
  | p :: l =>
      ((gsigCoordinateSecondDeriv L W u ω c z p.1 * Eblk L W p.2) *
          l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1 +
        (gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
          coordinateWordDeriv L W u ω c z l) +
      ((gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
          coordinateWordDeriv L W u ω c z l +
        (Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
          coordinateSecondWordDeriv u ω c z l)

theorem hasDerivAt_coordinateWordDeriv (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Z2 L)) :
    HasDerivAt
      (fun t : ℝ => coordinateWordDeriv L W u (Function.update ω c t) c z l)
      (coordinateSecondWordDeriv L W u ω c z l) (ω c) := by
  induction l with
  | nil =>
      simpa only [coordinateWordDeriv, coordinateSecondWordDeriv] using
        hasDerivAt_const (ω c) (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have hDhead :=
        (hasDerivAt_gsigCoordinateDeriv_update L W u ω c hz p.1).mul_const
          (Eblk L W p.2)
      have hHead :=
        (hasDerivAt_Gsig_HflowBlock_update L W u ω c hz p.1).mul_const
          (Eblk L W p.2)
      have hTail := hasDerivAt_coordinateWord L W u ω c hz l
      have h := (hDhead.mul hTail).add (hHead.mul ih)
      have hfun :
          (fun t : ℝ => gsigCoordinateDeriv L W u (Function.update ω c t) c z p.1 *
            Eblk L W p.2) *
              (fun t : ℝ => l.foldr (fun q M =>
                Gsig (HflowBlock L W u (Function.update ω c t)) z q.1 *
                  Eblk L W q.2 * M) 1) +
          (fun t : ℝ => Gsig (HflowBlock L W u (Function.update ω c t)) z p.1 *
            Eblk L W p.2) *
              (fun t : ℝ => coordinateWordDeriv L W u (Function.update ω c t) c z l) =
          (fun t : ℝ => coordinateWordDeriv L W u (Function.update ω c t) c z (p :: l)) := by
        funext t
        rfl
      rw [hfun] at h
      simp only [Function.update_eq_self] at h
      rw [coordinateSecondWordDeriv]
      exact h

/-- The second derivative of the actual finite word along one sample coordinate. -/
theorem hasDerivAt_deriv_coordinateWord (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Z2 L)) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => l.foldr (fun p M =>
        Gsig (HflowBlock L W u (Function.update ω c s)) z p.1 * Eblk L W p.2 * M) 1) t)
      (coordinateSecondWordDeriv L W u ω c z l) (ω c) := by
  let f : ℝ → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun s => l.foldr (fun p M =>
      Gsig (HflowBlock L W u (Function.update ω c s)) z p.1 * Eblk L W p.2 * M) 1
  have hfirst (t : ℝ) :
      HasDerivAt f (coordinateWordDeriv L W u (Function.update ω c t) c z l) t := by
    have h := hasDerivAt_coordinateWord L W u (Function.update ω c t) c hz l
    have hpoint : (Function.update ω c t) c = t := by simp
    rw [hpoint] at h
    have hpath : (fun s : ℝ => l.foldr (fun p M =>
        Gsig (HflowBlock L W u
          (Function.update (Function.update ω c t) c s)) z p.1 * Eblk L W p.2 * M) 1) =
        f := by
      funext s
      simp [f, Function.update_idem]
    rw [hpath] at h
    exact h
  have hderiv : (fun t : ℝ => deriv f t) =
      (fun t : ℝ => coordinateWordDeriv L W u (Function.update ω c t) c z l) := by
    funext t
    exact (hfirst t).deriv
  change HasDerivAt (fun t : ℝ => deriv f t) _ (ω c)
  rw [hderiv]
  exact hasDerivAt_coordinateWordDeriv L W u ω c hz l

/-- The second coordinate derivative of the finite loop matrix product. -/
theorem hasDerivAt_deriv_gloopProd_update (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (_hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        gloopProd L W (HflowBlock L W u (Function.update ω c s)) z I) t)
      (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)) (ω c) :=
  hasDerivAt_deriv_coordinateWord L W u ω c hz (I.σ.zip I.a)

/-- The second coordinate derivative of the traced finite loop. -/
theorem hasDerivAt_deriv_gloop_update (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        gloop L W (HflowBlock L W u (Function.update ω c s)) z I) t)
      (Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)))
      (ω c) := by
  let f : ℝ → ℂ := fun s =>
    gloop L W (HflowBlock L W u (Function.update ω c s)) z I
  have hfirst (t : ℝ) :
      HasDerivAt f
        (Matrix.trace (coordinateWordDeriv L W u (Function.update ω c t) c z
          (I.σ.zip I.a))) t := by
    have h := hasDerivAt_gloop_update L W u (Function.update ω c t) c hz I hwf
    have hpoint : (Function.update ω c t) c = t := by simp
    rw [hpoint] at h
    have hpath : (fun s : ℝ => gloop L W
        (HflowBlock L W u (Function.update (Function.update ω c t) c s)) z I) = f := by
      funext s
      simp [f, Function.update_idem]
    rw [hpath] at h
    exact h
  have hderiv : (fun t : ℝ => deriv f t) =
      (fun t : ℝ => Matrix.trace
        (coordinateWordDeriv L W u (Function.update ω c t) c z (I.σ.zip I.a))) := by
    funext t
    exact (hfirst t).deriv
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
    (hasDerivAt_coordinateWordDeriv L W u ω c hz (I.σ.zip I.a))
  change HasDerivAt (fun t : ℝ => deriv f t) _ (ω c)
  rw [hderiv]
  simpa only [hT, Function.comp_def] using h

end RBM.Gauss
