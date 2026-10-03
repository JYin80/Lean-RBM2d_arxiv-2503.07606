/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.GreenDerivative
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Fixed-sample derivative of finite resolvent loops

The derivative is a recursive Leibniz sum, with one differentiated Green factor
at each position. This is a deterministic path statement, not an expectation or
Gaussian generator identity.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The spectral drift for either Green sign. -/
noncomputable def spectralMSign (E : ℝ) (σ : Bool) : ℂ :=
  if σ then spectralM E else (starRingEnd ℂ) (spectralM E)

/-- The derivative of one signed Green factor along the samplewise flow. -/
noncomputable def gsigFlowDeriv (ω : Ω L W) (E u : ℝ) (σ : Bool) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  let G := Gsig (HflowBlock L W u ω) (spectralZ E u) σ;
  let X := (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm;
  -(G * ((1 / (2 * Real.sqrt u)) • X +
      spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) * G)

/-- Each signed resolvent has the stated fixed-sample derivative. -/
theorem hasDerivAt_Gsig_HflowBlock_spectralZ (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) (σ : Bool) :
    HasDerivAt
      (fun v : ℝ => Gsig (HflowBlock L W v ω) (spectralZ E v) σ)
      (gsigFlowDeriv L W ω E u σ) u := by
  cases σ with
  | true =>
      simpa only [Gsig_true, gsigFlowDeriv, spectralMSign, ite_true] using
        hasDerivAt_green_HflowBlock_spectralZ L W ω hE hu hu1
  | false =>
      have hz : HasDerivAt
          (fun v : ℝ => (starRingEnd ℂ) (spectralZ E v))
          (-((starRingEnd ℂ) (spectralM E))) u := by
        simpa using (hasDerivAt_spectralZ E u).star
      have him : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by
        have hpos : (spectralZ E u).im ≠ 0 := by
          rw [spectralZ_im]
          exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
        simpa using hpos
      have h := hasDerivAt_green_moving
        (hasDerivAt_HflowBlock_time L W ω hu) hz
        (HflowBlock_isHermitian L W u ω) him
      simpa only [Gsig_false, gsigFlowDeriv, spectralMSign, ite_false,
        Bool.false_eq_true, ↓reduceIte, neg_smul, sub_neg_eq_add] using h

/-- Recursive Leibniz derivative of the signed Green/block word. -/
noncomputable def loopWordDeriv (ω : Ω L W) (E u : ℝ) :
    List (Bool × Z2 L) → Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  | [] => 0
  | p :: l =>
      (gsigFlowDeriv L W ω E u p.1 * Eblk L W p.2) *
        l.foldr (fun q M => Gsig (HflowBlock L W u ω) (spectralZ E u) q.1 *
          Eblk L W q.2 * M) 1 +
      (Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2) *
        loopWordDeriv ω E u l

/-- List induction proves the product rule for every finite signed word. -/
theorem hasDerivAt_loopWord_HflowBlock_spectralZ (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (l : List (Bool × Z2 L)) :
    HasDerivAt
      (fun v : ℝ => l.foldr (fun p M =>
        Gsig (HflowBlock L W v ω) (spectralZ E v) p.1 * Eblk L W p.2 * M) 1)
      (loopWordDeriv L W ω E u l) u := by
  induction l with
  | nil =>
      simpa only [List.foldr_nil, loopWordDeriv] using
        hasDerivAt_const u (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have hhead :=
        (hasDerivAt_Gsig_HflowBlock_spectralZ L W ω hE hu hu1 p.1).mul_const
          (Eblk L W p.2)
      have h := hhead.mul ih
      have hfun :
          (fun v : ℝ => Gsig (HflowBlock L W v ω) (spectralZ E v) p.1 *
            Eblk L W p.2) *
            (fun v : ℝ => l.foldr (fun q M =>
              Gsig (HflowBlock L W v ω) (spectralZ E v) q.1 * Eblk L W q.2 * M) 1) =
          (fun v : ℝ => Gsig (HflowBlock L W v ω) (spectralZ E v) p.1 *
            Eblk L W p.2 *
            l.foldr (fun q M =>
              Gsig (HflowBlock L W v ω) (spectralZ E v) q.1 * Eblk L W q.2 * M) 1) := by
        funext v
        rfl
      rw [hfun] at h
      simpa only [List.foldr_cons, loopWordDeriv] using h

/-- The matrix-product form of the loop derivative. -/
theorem hasDerivAt_gloopProd_HflowBlock_spectralZ (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (_hwf : I.WF) :
    HasDerivAt
      (fun v : ℝ => gloopProd L W (HflowBlock L W v ω) (spectralZ E v) I)
      (loopWordDeriv L W ω E u (I.σ.zip I.a)) u :=
  hasDerivAt_loopWord_HflowBlock_spectralZ L W ω hE hu hu1 (I.σ.zip I.a)

/-- Taking the trace gives the fixed-sample derivative of the complete loop. -/
theorem hasDerivAt_gloop_HflowBlock_spectralZ (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    HasDerivAt
      (fun v : ℝ => gloop L W (HflowBlock L W v ω) (spectralZ E v) I)
      (Matrix.trace (loopWordDeriv L W ω E u (I.σ.zip I.a))) u := by
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_gloopProd_HflowBlock_spectralZ L W ω hE hu hu1 I hwf)
  simpa only [hT, Function.comp_def, gloop] using h

end RBM.Gauss
