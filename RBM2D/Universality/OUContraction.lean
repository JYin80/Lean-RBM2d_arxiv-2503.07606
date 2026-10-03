/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.OUHessian
import RBM2D.Universality.InjSum

/-!
# Centred contraction of the Wirtinger Hessian and its `L₁`, `L₂` bound

The deterministic pointwise contraction of the Wirtinger Hessian of `∏ Im m(z_i)` against
`S° = S - N⁻¹`, and its bound by the positive kernels `L₁`, `L₂` of `(EMCTE2)` (with the
definitions of `L_{1,t}`, `L_{2,t}`).  No OU path, expectation or time integral occurs.

Vocabulary (`Universality/OUHessian.lean`): the index set is `Idx L W`; `wirtSecond L W`;
`centeredVarianceEntry L W`; `stieltjesN`; `RBM.green`; `RBM.Green.Bmat L W`;
`paperL1Kernel L W`, `paperL2Kernel L W`.  Nothing here depends on the dimension beyond the index
type.
-/

noncomputable section

-- The style linters below only report unused simp arguments / section variables / `<;>` here.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal
open scoped Matrix.Norms.L2Operator
open scoped ComplexConjugate

section Defs

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The `K₁` contraction of (2.25). -/
def paperK1Contraction (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) (σ τ : Bool) : ℂ :=
  (Fintype.card (Idx L W) : ℂ)⁻¹ *
    ∑ a : Idx L W, ∑ b : Idx L W,
      ((RBM.Univ.signedGreen H z σ * RBM.Univ.signedGreen H z σ) a a) *
        (RBM.Univ.centeredVarianceEntry L W a b : ℂ) * (RBM.Univ.signedGreen H z τ) b b

/-- The `K₂` contraction of (2.25). -/
def paperK2Contraction (H : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ) (σ τ : Bool) : ℂ :=
  (Fintype.card (Idx L W) : ℂ)⁻¹ * (Fintype.card (Idx L W) : ℂ)⁻¹ *
    ∑ a : Idx L W, ∑ b : Idx L W,
      ((RBM.Univ.signedGreen H z₁ σ * RBM.Univ.signedGreen H z₁ σ) a b) *
        (RBM.Univ.centeredVarianceEntry L W a b : ℂ) *
          ((RBM.Univ.signedGreen H z₂ τ * RBM.Univ.signedGreen H z₂ τ) b a)

end Defs

theorem centeredVariance_single_contraction_eq (L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        wirtSecond L W (fun K => ((stieltjesN K z).im : ℂ)) H a b) =
      ((2 * (paperK1Contraction L W H z true true).im : ℝ) : ℂ) := by
  -- The second resolvent term agrees with the first after a simultaneous index swap.
  have hswap : (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ((RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) =
      ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [centeredVarianceEntry_symm]
  have hsum : (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
          (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) =
      2 * ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b) := by
    calc
      _ = ∑ a : Idx L W,
          ((∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b)) +
            ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
              ((RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ a : Idx L W, ∑ b : Idx L W,
            (centeredVarianceEntry L W a b : ℂ) *
              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b)) +
          ∑ a : Idx L W, ∑ b : Idx L W,
            (centeredVarianceEntry L W a b : ℂ) *
              ((RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a) := by
            rw [Finset.sum_add_distrib]
      _ = _ := by rw [hswap]; ring
  have hcomplex :
      ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          ((Fintype.card (Idx L W) : ℂ)⁻¹ *
            ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
              (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) =
      2 * paperK1Contraction L W H z true true := by
    dsimp [paperK1Contraction, signedGreen]
    have hXY : (∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b)) =
      ∑ a : Idx L W, ∑ b : Idx L W,
        (RBM.green H z * RBM.green H z) a a *
          (centeredVarianceEntry L W a b : ℂ) * (RBM.green H z) b b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    calc
      ∑ a : Idx L W, ∑ b : Idx L W,
          (centeredVarianceEntry L W a b : ℂ) *
            ((Fintype.card (Idx L W) : ℂ)⁻¹ *
              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a))
          = (Fintype.card (Idx L W) : ℂ)⁻¹ *
              ∑ a : Idx L W, ∑ b : Idx L W,
                (centeredVarianceEntry L W a b : ℂ) *
                  ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                    (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a) := by
              calc
                _ = ∑ a : Idx L W,
                    ((Fintype.card (Idx L W) : ℂ)⁻¹ *
                      ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
                        ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                          (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      calc
                        _ = ∑ b : Idx L W, (Fintype.card (Idx L W) : ℂ)⁻¹ *
                            ((centeredVarianceEntry L W a b : ℂ) *
                              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                                (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a)) := by
                              apply Finset.sum_congr rfl
                              intro b _
                              ring
                        _ = _ := (Finset.mul_sum _ _ _).symm
                _ = _ := (Finset.mul_sum _ _ _).symm
      _ = (Fintype.card (Idx L W) : ℂ)⁻¹ *
            (2 * ∑ a : Idx L W, ∑ b : Idx L W,
              (centeredVarianceEntry L W a b : ℂ) *
                ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b)) := by rw [hsum]
      _ = 2 * ((Fintype.card (Idx L W) : ℂ)⁻¹ *
            ∑ a : Idx L W, ∑ b : Idx L W,
              (RBM.green H z * RBM.green H z) a a *
                (centeredVarianceEntry L W a b : ℂ) * (RBM.green H z) b b) := by
              calc
                _ = 2 * ((Fintype.card (Idx L W) : ℂ)⁻¹ *
                      ∑ a : Idx L W, ∑ b : Idx L W,
                        (centeredVarianceEntry L W a b : ℂ) *
                          ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b)) := by ring
                _ = _ := congrArg
                  (fun w : ℂ => 2 * ((Fintype.card (Idx L W) : ℂ)⁻¹ * w)) hXY
  have him := congrArg Complex.im hcomplex
  have hpoint (a b : Idx L W) :
      (centeredVarianceEntry L W a b : ℂ) *
          wirtSecond L W (fun K => (stieltjesN K z).im) H a b =
        (((centeredVarianceEntry L W a b : ℂ) *
          ((Fintype.card (Idx L W) : ℂ)⁻¹ *
            ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
              (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a))).im : ℂ) := by
    rw [wirtSecond_stieltjesIm_entry_formula L W H hH z hz]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  calc
    _ = ∑ a : Idx L W, ∑ b : Idx L W,
          (((centeredVarianceEntry L W a b : ℂ) *
            ((Fintype.card (Idx L W) : ℂ)⁻¹ *
              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a))).im : ℂ) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            exact hpoint a b
    _ = ((∑ a : Idx L W, ∑ b : Idx L W,
          (centeredVarianceEntry L W a b : ℂ) *
            ((Fintype.card (Idx L W) : ℂ)⁻¹ *
              ((RBM.green H z * RBM.green H z) a a * (RBM.green H z) b b +
                (RBM.green H z * RBM.green H z) b b * (RBM.green H z) a a))).im : ℝ) := by
          simp [Complex.im_sum]
    _ = ((2 * (paperK1Contraction L W H z true true).im : ℝ) : ℂ) := by
          simpa [Complex.mul_im] using congrArg (fun x : ℝ => (x : ℂ)) him

theorem centeredVariance_wirtingerFirst_product_eq (L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        stieltjesImWirtingerFirst L W H z₁ a b * stieltjesImWirtingerFirst L W H z₂ b a) =
      -(1 / 4 : ℂ) *
        (paperK2Contraction L W H z₁ z₂ true true -
          paperK2Contraction L W H z₁ z₂ true false -
          paperK2Contraction L W H z₁ z₂ false true +
          paperK2Contraction L W H z₁ z₂ false false) := by
  let q : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
  let c : ℂ := Complex.I * q / 2
  let A : Idx L W → Idx L W → ℂ := fun a b =>
    (RBM.green H z₁ * RBM.green H z₁) b a -
      (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) b a
  let B : Idx L W → Idx L W → ℂ := fun a b =>
    (RBM.green H z₂ * RBM.green H z₂) a b -
      (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) a b
  have hswap : (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) * A a b * B a b) =
      ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) * A b a * B b a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [centeredVarianceEntry_symm]
  have hfour :
      (∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) * A b a * B b a) =
        (∑ a : Idx L W, ∑ b : Idx L W,
          (RBM.green H z₁ * RBM.green H z₁) a b *
            (centeredVarianceEntry L W a b : ℂ) *
              (RBM.green H z₂ * RBM.green H z₂) b a) -
        (∑ a : Idx L W, ∑ b : Idx L W,
          (RBM.green H z₁ * RBM.green H z₁) a b *
            (centeredVarianceEntry L W a b : ℂ) *
              (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a) -
        (∑ a : Idx L W, ∑ b : Idx L W,
          (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) a b *
            (centeredVarianceEntry L W a b : ℂ) *
              (RBM.green H z₂ * RBM.green H z₂) b a) +
        ∑ a : Idx L W, ∑ b : Idx L W,
          (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) a b *
            (centeredVarianceEntry L W a b : ℂ) *
              (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a := by
    have hsumEq (f : Idx L W → Idx L W → ℂ) :
        (∑ a : Idx L W, ∑ b : Idx L W, f a b) =
          ∑ p : Idx L W × Idx L W, f p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : Idx L W × Idx L W => f p.1 p.2)).symm
    calc
      _ = ∑ a : Idx L W, ∑ b : Idx L W,
          (centeredVarianceEntry L W a b : ℂ) *
            ((RBM.green H z₁ * RBM.green H z₁) a b -
              (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) a b) *
            ((RBM.green H z₂ * RBM.green H z₂) b a -
              (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            simp [A, B]
      _ = ∑ a : Idx L W, ∑ b : Idx L W,
          ((RBM.green H z₁ * RBM.green H z₁) a b *
              (centeredVarianceEntry L W a b : ℂ) *
                (RBM.green H z₂ * RBM.green H z₂) b a -
            (RBM.green H z₁ * RBM.green H z₁) a b *
              (centeredVarianceEntry L W a b : ℂ) *
                (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a -
            (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry L W a b : ℂ) *
                (RBM.green H z₂ * RBM.green H z₂) b a +
            (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry L W a b : ℂ) *
                (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ p : Idx L W × Idx L W,
          ((RBM.green H z₁ * RBM.green H z₁) p.1 p.2 *
              (centeredVarianceEntry L W p.1 p.2 : ℂ) *
                (RBM.green H z₂ * RBM.green H z₂) p.2 p.1 -
            (RBM.green H z₁ * RBM.green H z₁) p.1 p.2 *
              (centeredVarianceEntry L W p.1 p.2 : ℂ) *
                (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) p.2 p.1 -
            (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) p.1 p.2 *
              (centeredVarianceEntry L W p.1 p.2 : ℂ) *
                (RBM.green H z₂ * RBM.green H z₂) p.2 p.1 +
            (RBM.green H ((starRingEnd ℂ) z₁) * RBM.green H ((starRingEnd ℂ) z₁)) p.1 p.2 *
              (centeredVarianceEntry L W p.1 p.2 : ℂ) *
                (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) p.2 p.1) := by
            rw [hsumEq]
      _ = _ := by
        rw [hsumEq (fun a b => (RBM.green H z₁ * RBM.green H z₁) a b *
            (centeredVarianceEntry L W a b : ℂ) * (RBM.green H z₂ * RBM.green H z₂) b a),
          hsumEq (fun a b => (RBM.green H z₁ * RBM.green H z₁) a b *
            (centeredVarianceEntry L W a b : ℂ) *
              (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a),
          hsumEq (fun a b => (RBM.green H ((starRingEnd ℂ) z₁) *
            RBM.green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry L W a b : ℂ) * (RBM.green H z₂ * RBM.green H z₂) b a),
          hsumEq (fun a b => (RBM.green H ((starRingEnd ℂ) z₁) *
            RBM.green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry L W a b : ℂ) *
                (RBM.green H ((starRingEnd ℂ) z₂) * RBM.green H ((starRingEnd ℂ) z₂)) b a)]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfactor :
      (∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) * (c * A a b) * (c * B a b)) =
      (c * c) * ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) * A a b * B a b := by
    calc
      _ = ∑ a : Idx L W, ∑ b : Idx L W,
          (c * c) * ((centeredVarianceEntry L W a b : ℂ) * A a b * B a b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ a : Idx L W,
          ((c * c) * ∑ b : Idx L W,
            (centeredVarianceEntry L W a b : ℂ) * A a b * B a b) := by
            apply Finset.sum_congr rfl
            intro a _
            exact (Finset.mul_sum _ _ _).symm
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hc : c * c = -(q * q / 4) := by
    calc
      c * c = (Complex.I * Complex.I) * (q * q) / 4 := by dsimp [c]; ring
      _ = -(q * q / 4) := by rw [Complex.I_mul_I]; ring
  rw [show (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        stieltjesImWirtingerFirst L W H z₁ a b * stieltjesImWirtingerFirst L W H z₂ b a) =
      ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) * (c * A a b) * (c * B a b) from by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [stieltjesImWirtingerFirst_adjoint_formula L W H hH z₁ hz₁,
          stieltjesImWirtingerFirst_adjoint_formula L W H hH z₂ hz₂]
        ]
  rw [hfactor, hc, hswap, hfour]
  simp only [paperK2Contraction, signedGreen, ↓reduceIte]
  dsimp [q]
  ring

private def OUContraction_entryMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) : Matrix n n ℂ := Matrix.single i j 1

private theorem OUContraction_trace_green_single {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (a b : n) :
    (G * OUContraction_entryMatrix a b * G).trace = (G * G) b a := by
  calc
    (G * OUContraction_entryMatrix a b * G).trace =
        (G * (OUContraction_entryMatrix a b * G)).trace := by
          congr 1
          simp [Matrix.mul_assoc]
    _ = ((OUContraction_entryMatrix a b * G) * G).trace := Matrix.trace_mul_comm _ _
    _ = (OUContraction_entryMatrix a b * (G * G)).trace := by
          congr 1 <;> simp [Matrix.mul_assoc]
    _ = (G * G) b a := by
          simpa [OUContraction_entryMatrix] using Matrix.trace_single_mul a b (1 : ℂ) (G * G)

private theorem OUContraction_Bmat_real_eq_entryMatrices {L W : ℕ} [NeZero L] [NeZero W]
    {i j : Idx L W} (hij : i ≠ j) :
    RBM.Green.Bmat L W i j true =
      OUContraction_entryMatrix i j + OUContraction_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply,
        h1, h2, h1', h2', and_comm]

private theorem OUContraction_Bmat_imag_eq_entryMatrices {L W : ℕ} [NeZero L] [NeZero W]
    {i j : Idx L W} (hij : i ≠ j) :
    RBM.Green.Bmat L W i j false =
      Complex.I • OUContraction_entryMatrix i j - Complex.I • OUContraction_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply,
        h1, h2, h1', h2', and_comm]

private theorem OUContraction_Bmat_diag_eq_entryMatrix {L W : ℕ} [NeZero L] [NeZero W]
    (i : Idx L W) :
    RBM.Green.Bmat L W i i true = OUContraction_entryMatrix i i := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply]
  · have h' : ¬ (i = k ∧ i = l) := by
      rintro ⟨hik, hil⟩
      exact h ⟨hik.symm, hil.symm⟩
    simp [RBM.Green.Bmat, OUContraction_entryMatrix, Matrix.single_apply, h, h']

private theorem OUContraction_trace_green_Bmat_real {L W : ℕ} [NeZero L] [NeZero W]
    (G : Matrix (Idx L W) (Idx L W) ℂ) {i j : Idx L W} (hij : i ≠ j) :
    (G * RBM.Green.Bmat L W i j true * G).trace = (G * G) j i + (G * G) i j := by
  rw [OUContraction_Bmat_real_eq_entryMatrices hij, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, OUContraction_trace_green_single, OUContraction_trace_green_single]

private theorem OUContraction_trace_green_Bmat_imag {L W : ℕ} [NeZero L] [NeZero W]
    (G : Matrix (Idx L W) (Idx L W) ℂ) {i j : Idx L W} (hij : i ≠ j) :
    (G * RBM.Green.Bmat L W i j false * G).trace =
      Complex.I * ((G * G) j i - (G * G) i j) := by
  rw [OUContraction_Bmat_imag_eq_entryMatrices hij]
  have hmul :
      G * (Complex.I • OUContraction_entryMatrix i j -
          Complex.I • OUContraction_entryMatrix j i) * G =
        Complex.I • (G * OUContraction_entryMatrix i j * G) -
          Complex.I • (G * OUContraction_entryMatrix j i * G) := by
    calc
      _ = (Complex.I • (G * OUContraction_entryMatrix i j) -
          Complex.I • (G * OUContraction_entryMatrix j i)) * G := by
            simp [Matrix.mul_sub, Matrix.mul_smul]
      _ = _ := by rw [Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [hmul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    OUContraction_trace_green_single, OUContraction_trace_green_single]
  simp only [smul_eq_mul]
  ring

private theorem OUContraction_lineFirst_wirtinger {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : Idx L W) :
    stieltjesImWirtingerFirst L W H z a b =
      if a = b then
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) z 0 : ℂ)
      else
        (1 / 2 : ℂ) *
          ((stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) z 0 : ℂ) -
            Complex.I * (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) z 0 : ℂ)) := by
  by_cases hab : a = b
  · subst b
    rw [stieltjesImWirtingerFirst_entry_formula L W H hH z hz a a]
    let q : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
    have hline : stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) z 0 =
        (-q * (RBM.green H z * RBM.green H z) a a).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        OUContraction_Bmat_diag_eq_entryMatrix, OUContraction_trace_green_single]
    have hq : q.im = 0 := by simp [q]
    rw [ite_eq_left rfl, hline]
    apply Complex.ext <;>
      simp [q, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, hq] <;> ring_nf
  · rw [stieltjesImWirtingerFirst_entry_formula L W H hH z hz a b, ite_eq_right hab]
    let q : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
    have hreal : stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) z 0 =
        (-q * ((RBM.green H z * RBM.green H z) b a + (RBM.green H z * RBM.green H z) a b)).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        OUContraction_trace_green_Bmat_real (RBM.green H z) hab]
    have himag : stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) z 0 =
        (-q * (Complex.I * ((RBM.green H z * RBM.green H z) b a -
          (RBM.green H z * RBM.green H z) a b))).im := by
      simp [stieltjesImLineFirst, q, zero_smul, add_zero,
        OUContraction_trace_green_Bmat_imag (RBM.green H z) hab]
    have hq : q.im = 0 := by simp [q]
    rw [hreal, himag]
    apply Complex.ext <;>
      simp [q, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, hq] <;> ring_nf

private theorem OUContraction_lineFirst_neg {n : Type*} [Fintype n] [DecidableEq n]
    (H A : Matrix n n ℂ) (z : ℂ) :
    stieltjesImLineFirst H (-A) z 0 = -stieltjesImLineFirst H A z 0 := by
  simp [stieltjesImLineFirst, Matrix.mul_neg, Matrix.neg_mul]

private noncomputable def OUContraction_crossCoord {L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ)
    (a b : Idx L W) : ℂ :=
  if a = b then
    (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) z₂ 0 : ℂ) *
      (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) z₁ 0 : ℂ)
  else
    (1 / 4 : ℂ) *
      ((stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) z₂ 0 : ℂ) *
          (stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) z₁ 0 : ℂ) +
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) z₂ 0 : ℂ) *
          (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) z₁ 0 : ℂ))

private theorem OUContraction_crossCoord_eq_symmWirtinger {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (a b : Idx L W) :
    OUContraction_crossCoord H z₁ z₂ a b =
      (1 / 2 : ℂ) *
        (stieltjesImWirtingerFirst L W H z₁ a b * stieltjesImWirtingerFirst L W H z₂ b a +
          stieltjesImWirtingerFirst L W H z₁ b a * stieltjesImWirtingerFirst L W H z₂ a b) := by
  by_cases hab : a = b
  · subst b
    simp [OUContraction_crossCoord, OUContraction_lineFirst_wirtinger hH z₁ hz₁,
      OUContraction_lineFirst_wirtinger hH z₂ hz₂]
    ring
  · have h₁ := OUContraction_lineFirst_wirtinger hH z₁ hz₁ a b
    have h₂ := OUContraction_lineFirst_wirtinger hH z₂ hz₂ a b
    have h₁' := OUContraction_lineFirst_wirtinger hH z₁ hz₁ b a
    have h₂' := OUContraction_lineFirst_wirtinger hH z₂ hz₂ b a
    rw [ite_eq_right hab] at h₁ h₂
    rw [ite_eq_right (Ne.symm hab)] at h₁' h₂'
    have htrue : RBM.Green.Bmat L W b a true = RBM.Green.Bmat L W a b true :=
      Bmat_swap_true L W a b
    have hfalse : RBM.Green.Bmat L W b a false = -RBM.Green.Bmat L W a b false :=
      Bmat_swap_false L W hab
    rw [htrue, hfalse, OUContraction_lineFirst_neg] at h₁' h₂'
    simp only [Complex.ofReal_neg] at h₁' h₂'
    simp only [OUContraction_crossCoord, ite_eq_right hab, h₁, h₂, h₁', h₂']
    ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
    ring_nf

private theorem OUContraction_cross_contraction_eq {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) * OUContraction_crossCoord H z₁ z₂ a b) =
      ∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          stieltjesImWirtingerFirst L W H z₁ a b * stieltjesImWirtingerFirst L W H z₂ b a := by
  let F : Idx L W → Idx L W → ℂ := fun a b =>
    (centeredVarianceEntry L W a b : ℂ) *
      stieltjesImWirtingerFirst L W H z₁ a b * stieltjesImWirtingerFirst L W H z₂ b a
  let G : Idx L W → Idx L W → ℂ := fun a b =>
    (centeredVarianceEntry L W a b : ℂ) *
      stieltjesImWirtingerFirst L W H z₁ b a * stieltjesImWirtingerFirst L W H z₂ a b
  have hswap : (∑ a : Idx L W, ∑ b : Idx L W, G a b) =
      ∑ a : Idx L W, ∑ b : Idx L W, F a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [F, G]
    rw [centeredVarianceEntry_symm]
  have hadd : (∑ a : Idx L W, ∑ b : Idx L W, (F a b + G a b)) =
      (∑ a : Idx L W, ∑ b : Idx L W, F a b) +
        ∑ a : Idx L W, ∑ b : Idx L W, G a b := by
    simp only [Finset.sum_add_distrib]
  calc
    _ = ∑ a : Idx L W, ∑ b : Idx L W,
          (1 / 2 : ℂ) * (F a b + G a b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [OUContraction_crossCoord_eq_symmWirtinger hH z₁ z₂ hz₁ hz₂]
          dsimp [F, G]
          ring
    _ = (1 / 2 : ℂ) *
          (∑ a : Idx L W, ∑ b : Idx L W, (F a b + G a b)) := by
          calc
            _ = ∑ a : Idx L W,
                  ((1 / 2 : ℂ) * ∑ b : Idx L W, (F a b + G a b)) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
    _ = (1 / 2 : ℂ) *
          ((∑ a : Idx L W, ∑ b : Idx L W, F a b) +
            ∑ a : Idx L W, ∑ b : Idx L W, G a b) := by rw [hadd]
    _ = _ := by rw [hswap]; ring

private noncomputable def OUContraction_singleCoord {L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (a b : Idx L W) : ℂ :=
  if a = b then
    (stieltjesImLineSecond H (RBM.Green.Bmat L W a a true) z : ℂ)
  else
    (1 / 4 : ℂ) *
      ((stieltjesImLineSecond H (RBM.Green.Bmat L W a b true) z : ℂ) +
        (stieltjesImLineSecond H (RBM.Green.Bmat L W a b false) z : ℂ))

private theorem OUContraction_singleCoord_eq_wirtSecond {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (a b : Idx L W) :
    OUContraction_singleCoord H z a b =
      wirtSecond L W (fun K => (stieltjesN K z).im) H a b := by
  let u : Unit := ()
  have h := wirtSecond_stieltjesImProduct_expansion L W
    ({u} : Finset Unit) H hH
    (fun _ : Unit => z) (by intro i hi; simpa using hz) a b
  convert h.symm using 1 <;>
    simp [OUContraction_singleCoord, stieltjesImProductLineSecond] <;> ring_nf

private theorem OUContraction_lineSecond_rearrange {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (single : ι → ℝ) (cross : ι → ι → ℝ) (deriv : ι → ℝ) :
    s.sum (fun i => single i + (s.erase i).sum (fun j => cross i j) * deriv i) =
      s.sum single + s.sum (fun i =>
        (s.erase i).sum (fun j => cross i j * deriv i)) := by
  calc
    _ = s.sum single + s.sum (fun i => (s.erase i).sum (fun j => cross i j) * deriv i) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]

private theorem OUContraction_lineSecond_complex_split {L W : ℕ} [NeZero L] [NeZero W]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (H A : Matrix (Idx L W) (Idx L W) ℂ) (z : ι → ℂ) :
    (stieltjesImProductLineSecond s H A z : ℂ) =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0 : ℝ) : ℂ) *
          (stieltjesImLineSecond H A (z i) : ℂ) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0 : ℝ) : ℂ) *
          (stieltjesImLineFirst H A (z j) 0 : ℂ) *
          (stieltjesImLineFirst H A (z i) 0 : ℂ) := by
  classical
  exact_mod_cast OUContraction_lineSecond_rearrange s
    (fun i => (∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
      stieltjesImLineSecond H A (z i))
    (fun i j => (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
      stieltjesImLineFirst H A (z j) 0)
    (fun i => stieltjesImLineFirst H A (z i) 0)

private theorem OUContraction_sum_weighted_double {α β ι : Type*}
    [Fintype α] [Fintype β] [DecidableEq ι]
    (s : Finset ι) (V : α → β → ℂ) (w : ι → ℂ)
    (f : ι → α → β → ℂ) :
    (∑ a : α, ∑ b : β, V a b * (∑ i ∈ s, w i * f i a b)) =
      ∑ i ∈ s, w i * (∑ a : α, ∑ b : β, V a b * f i a b) := by
  classical
  calc
    _ = ∑ a : α, ∑ b : β, ∑ i ∈ s, w i * (V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ a : α, ∑ i ∈ s, ∑ b : β, w i * (V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ a : α, ∑ b : β, w i * (V a b * f i a b) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, w i * (∑ a : α, ∑ b : β, V a b * f i a b) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            _ = ∑ a : α, w i * ∑ b : β, V a b * f i a b := by
                  apply Finset.sum_congr rfl
                  intro a _
                  exact (Finset.mul_sum _ _ _).symm
            _ = _ := (Finset.mul_sum _ _ _).symm

private theorem OUContraction_wirtSecond_leibniz {L W : ℕ} [NeZero L] [NeZero W]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : Idx L W) :
    wirtSecond L W
      (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b =
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
          wirtSecond L W (fun K => (stieltjesN K (z i)).im) H a b) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
          OUContraction_crossCoord H (z i) (z j) a b := by
  classical
  have hsingle :
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
          wirtSecond L W (fun K => (stieltjesN K (z i)).im) H a b) =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
          OUContraction_singleCoord H (z i) a b := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← OUContraction_singleCoord_eq_wirtSecond hH (z i) (hz i hi) a b]
  rw [wirtSecond_stieltjesImProduct_expansion L W s H hH z hz a b]
  by_cases hab : a = b
  · subst b
    simp only [ite_eq_left rfl]
    rw [hsingle]
    have hline := OUContraction_lineSecond_complex_split s H (RBM.Green.Bmat L W a a true) z
    simp only [stieltjesImAlong, Complex.ofReal_zero, zero_smul, add_zero] at hline
    have hassoc :
        (∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
            (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z j) 0 : ℂ) *
            (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z i) 0 : ℂ)) =
        ∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
            ((stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z j) 0 : ℂ) *
              (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z i) 0 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hline' :
        (stieltjesImProductLineSecond s H (RBM.Green.Bmat L W a a true) z : ℂ) =
          (∑ i ∈ s,
            ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
              (stieltjesImLineSecond H (RBM.Green.Bmat L W a a true) (z i) : ℂ)) +
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
              ((stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z j) 0 : ℂ) *
                (stieltjesImLineFirst H (RBM.Green.Bmat L W a a true) (z i) 0 : ℂ)) := by
      calc
        _ = _ := hline
        _ = _ := congrArg (fun x : ℂ =>
          (∑ i ∈ s,
            ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
              (stieltjesImLineSecond H (RBM.Green.Bmat L W a a true) (z i) : ℂ)) + x) hassoc
    simpa only [OUContraction_singleCoord, OUContraction_crossCoord, ite_true] using hline'
  · simp only [ite_eq_right hab, smul_eq_mul]
    rw [hsingle]
    have htrue := OUContraction_lineSecond_complex_split s H (RBM.Green.Bmat L W a b true) z
    have hfalse := OUContraction_lineSecond_complex_split s H (RBM.Green.Bmat L W a b false) z
    simp only [stieltjesImAlong, Complex.ofReal_zero, zero_smul, add_zero] at htrue hfalse
    let c : ℂ := (1 / 4 : ℂ)
    let ST : ℂ := ∑ i ∈ s,
      ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
        (stieltjesImLineSecond H (RBM.Green.Bmat L W a b true) (z i) : ℂ)
    let SF : ℂ := ∑ i ∈ s,
      ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
        (stieltjesImLineSecond H (RBM.Green.Bmat L W a b false) (z i) : ℂ)
    let XT : ℂ := ∑ i ∈ s, ∑ j ∈ s.erase i,
      ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) (z j) 0 : ℂ) *
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) (z i) 0 : ℂ)
    let XF : ℂ := ∑ i ∈ s, ∑ j ∈ s.erase i,
      ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) (z j) 0 : ℂ) *
        (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) (z i) 0 : ℂ)
    have hsingleCoord :
        (∑ i ∈ s,
          ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
            OUContraction_singleCoord H (z i) a b) = c * (ST + SF) := by
      simp only [OUContraction_singleCoord, ite_eq_right hab]
      calc
        _ = ∑ i ∈ s,
              c * (((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
                (stieltjesImLineSecond H (RBM.Green.Bmat L W a b true) (z i) : ℂ) +
                ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
                (stieltjesImLineSecond H (RBM.Green.Bmat L W a b false) (z i) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = c * (ST + SF) := by
              simp only [mul_add, Finset.sum_add_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hcrossCoord :
        (∑ i ∈ s, ∑ j ∈ s.erase i,
          ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
            OUContraction_crossCoord H (z i) (z j) a b) = c * (XT + XF) := by
      simp only [OUContraction_crossCoord, ite_eq_right hab]
      calc
        _ = ∑ i ∈ s, ∑ j ∈ s.erase i,
              ((c * (((∏ k ∈ (s.erase i).erase j,
                  (stieltjesN H (z k)).im : ℝ) : ℂ) *
                    (stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) (z j) 0 : ℂ) *
                    (stieltjesImLineFirst H (RBM.Green.Bmat L W a b true) (z i) 0 : ℂ))) +
                c * (((∏ k ∈ (s.erase i).erase j,
                  (stieltjesN H (z k)).im : ℝ) : ℂ) *
                    (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) (z j) 0 : ℂ) *
                    (stieltjesImLineFirst H (RBM.Green.Bmat L W a b false) (z i) 0 : ℂ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = c * (XT + XF) := by
              simp only [Finset.sum_add_distrib]
              simp only [← Finset.mul_sum]
              change c * XT + c * XF = c * (XT + XF)
              ring
    rw [hsingleCoord, hcrossCoord, htrue, hfalse]
    simp only [Complex.real_smul]
    rw [show ((1 / 4 : ℝ) : ℂ) = c by norm_num [c]]
    ring

theorem centeredVariance_wirtProduct_contraction_eq (L W : ℕ) [NeZero L] [NeZero W]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        wirtSecond L W
          (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b) =
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
          ((2 * (paperK1Contraction L W H (z i) true true).im : ℝ) : ℂ)) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
          (-(1 / 4 : ℂ) *
            (paperK2Contraction L W H (z i) (z j) true true -
              paperK2Contraction L W H (z i) (z j) true false -
              paperK2Contraction L W H (z i) (z j) false true +
              paperK2Contraction L W H (z i) (z j) false false)) := by
  classical
  let V : Idx L W → Idx L W → ℂ := fun a b => centeredVarianceEntry L W a b
  let rem1 : ι → ℂ := fun i =>
    ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ)
  let rem2 : ι → ι → ℂ := fun i j =>
    ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ)
  let single : ι → Idx L W → Idx L W → ℂ := fun i a b =>
    wirtSecond L W (fun K => (stieltjesN K (z i)).im) H a b
  let cross : ι → ι → Idx L W → Idx L W → ℂ := fun i j a b =>
    OUContraction_crossCoord H (z i) (z j) a b
  have hpoint (a b : Idx L W) := OUContraction_wirtSecond_leibniz s hH z hz a b
  have hsplit :
      (∑ a : Idx L W, ∑ b : Idx L W,
        V a b * wirtSecond L W
          (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b) =
        (∑ a : Idx L W, ∑ b : Idx L W,
          V a b * (∑ i ∈ s, rem1 i * single i a b)) +
        ∑ a : Idx L W, ∑ b : Idx L W,
          V a b * (∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j * cross i j a b) := by
    simp_rw [hpoint]
    simp only [V, rem1, rem2, single, cross, mul_add, Finset.sum_add_distrib]
  have hfirst := OUContraction_sum_weighted_double s V rem1 single
  have hcross₁ := OUContraction_sum_weighted_double s V (fun _ => (1 : ℂ))
    (fun i a b => ∑ j ∈ s.erase i, rem2 i j * cross i j a b)
  have hcross₂ (i : ι) :
      (∑ a : Idx L W, ∑ b : Idx L W,
        V a b * (∑ j ∈ s.erase i, rem2 i j * cross i j a b)) =
        ∑ j ∈ s.erase i, rem2 i j *
          (∑ a : Idx L W, ∑ b : Idx L W, V a b * cross i j a b) :=
    OUContraction_sum_weighted_double (s.erase i) V (rem2 i) (cross i)
  have hcross :
      (∑ a : Idx L W, ∑ b : Idx L W,
        V a b * (∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j * cross i j a b)) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j *
        (∑ a : Idx L W, ∑ b : Idx L W, V a b * cross i j a b) := by
    simpa only [one_mul] using hcross₁.trans (by
      apply Finset.sum_congr rfl
      intro i hi
      rw [one_mul]
      exact hcross₂ i)
  calc
    _ = (∑ i ∈ s, rem1 i *
          (∑ a : Idx L W, ∑ b : Idx L W, V a b * single i a b)) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, rem2 i j *
          (∑ a : Idx L W, ∑ b : Idx L W, V a b * cross i j a b) := by
          rw [hsplit, hfirst, hcross]
    _ = _ := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i hi
            simpa [V, single, rem1] using congrArg (fun x : ℂ => rem1 i * x)
              (centeredVariance_single_contraction_eq L W H hH (z i) (hz i hi))
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            have hcrossContract := OUContraction_cross_contraction_eq hH (z i) (z j)
              (hz i hi) (hz j (Finset.mem_of_mem_erase hj))
            have hpair := centeredVariance_wirtingerFirst_product_eq L W H hH
              (z i) (z j) (hz i hi) (hz j (Finset.mem_of_mem_erase hj))
            simpa [V, cross, rem2] using congrArg (fun x : ℂ => rem2 i j * x)
              (hcrossContract.trans hpair)

private theorem OUContraction_stieltjesN_im_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjesN H z).im := by
  have h := stieltjesN_im_eq_normalized_specWeight H hH z.re z.im hz
  rw [Complex.re_add_im] at h
  rw [h]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  positivity

private theorem OUContraction_stieltjesN_im_prod_nonneg {ι : Type*}
    {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (z : ι → ℂ) (t : Finset ι)
    (hz : ∀ i ∈ t, 0 < (z i).im) :
    0 ≤ ∏ i ∈ t, (stieltjesN H (z i)).im := by
  exact Finset.prod_nonneg fun i hi => OUContraction_stieltjesN_im_nonneg hH (hz i hi)

private theorem OUContraction_K1_conj_eq_false_false {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (z : ℂ) :
    conj (paperK1Contraction L W H z true true) =
      paperK1Contraction L W H z false false := by
  have hG : signedGreen H z false = (signedGreen H z true)ᴴ := by
    simpa [signedGreen, RBM.Gsig] using (RBM.Gsig_conjTranspose hH z true).symm
  have hSq (a : Idx L W) :
      conj ((signedGreen H z true * signedGreen H z true) a a) =
        (signedGreen H z false * signedGreen H z false) a a := by
    calc
      _ = ((signedGreen H z true * signedGreen H z true)ᴴ) a a := by
        simp [Matrix.conjTranspose_apply]
      _ = ((signedGreen H z true)ᴴ * (signedGreen H z true)ᴴ) a a := by
        rw [Matrix.conjTranspose_mul]
      _ = _ := by rw [← hG]
  have hDiag (b : Idx L W) :
      conj (signedGreen H z true b b) = signedGreen H z false b b := by
    calc
      _ = ((signedGreen H z true)ᴴ) b b := by
        simp [Matrix.conjTranspose_apply]
      _ = _ := by rw [hG]
  simp only [paperK1Contraction, map_mul, map_sum, map_inv₀, map_natCast,
    Complex.conj_ofReal, hSq, hDiag]

private theorem OUContraction_K1_im_abs_le {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (z : ℂ) :
    ‖((2 * (paperK1Contraction L W H z true true).im : ℝ) : ℂ)‖ ≤
      paperL1Kernel L W H z := by
  let K := paperK1Contraction L W H z true true
  let Kbar := paperK1Contraction L W H z false false
  have hconj : conj K = Kbar := OUContraction_K1_conj_eq_false_false hH z
  have him : (K - conj K).im = 2 * K.im := by
    simp [Complex.sub_im, Complex.conj_im]
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, ← him, hconj]
  have htriangle : |(K - Kbar).im| ≤ |K.im| + |Kbar.im| := by
    simpa only [Complex.sub_im] using (abs_sub (K.im) (Kbar.im))
  have htoNorm : |K.im| + |Kbar.im| ≤ ‖K‖ + ‖Kbar‖ :=
    add_le_add (Complex.abs_im_le_norm K) (Complex.abs_im_le_norm Kbar)
  have hsum : ‖K‖ + ‖Kbar‖ ≤ paperL1Kernel L W H z := by
    change ‖paperK1Contraction L W H z true true‖ +
        ‖paperK1Contraction L W H z false false‖ ≤
      ∑ σ : Bool, ∑ τ : Bool, ‖paperK1Contraction L W H z σ τ‖
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    nlinarith [norm_nonneg (paperK1Contraction L W H z true false),
      norm_nonneg (paperK1Contraction L W H z false true)]
  exact htriangle.trans (htoNorm.trans hsum)

private theorem OUContraction_K2_abs_le {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (z₁ z₂ : ℂ) :
    ‖-(1 / 4 : ℂ) *
        (paperK2Contraction L W H z₁ z₂ true true -
          paperK2Contraction L W H z₁ z₂ true false -
          paperK2Contraction L W H z₁ z₂ false true +
          paperK2Contraction L W H z₁ z₂ false false)‖ ≤
      paperL2Kernel L W H z₁ z₂ := by
  let A := paperK2Contraction L W H z₁ z₂ true true
  let B := paperK2Contraction L W H z₁ z₂ true false
  let C := paperK2Contraction L W H z₁ z₂ false true
  let D := paperK2Contraction L W H z₁ z₂ false false
  have hcomb : ‖A - B - C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    calc
      ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (‖A - B‖ + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by gcongr; exact norm_sub_le _ _
  have hsum : ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤ paperL2Kernel L W H z₁ z₂ := by
    change ‖paperK2Contraction L W H z₁ z₂ true true‖ +
        ‖paperK2Contraction L W H z₁ z₂ true false‖ +
        ‖paperK2Contraction L W H z₁ z₂ false true‖ +
        ‖paperK2Contraction L W H z₁ z₂ false false‖ ≤
      ∑ σ : Bool, ∑ τ : Bool, ‖paperK2Contraction L W H z₁ z₂ σ τ‖
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    exact le_of_eq (by ring)
  rw [norm_mul]
  have hfour : 0 ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by positivity
  have hnormquarter : ‖-(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
  rw [hnormquarter]
  exact (mul_le_mul_of_nonneg_left hcomb (by norm_num)).trans <|
    by nlinarith [hsum]

/-- **Pointwise deterministic kernel bound behind `(EMCTE2)`.**  For a Hermitian
matrix and any finite family of spectral parameters in the upper half-plane, the norm of the
full signed centered double-sum contraction is bounded by the positive-weight `paperL1Kernel`
and ordered `paperL2Kernel` sums, which equal `L1t`, `L2t` at a Hermitian matrix
(`paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`). -/
theorem centeredVariance_wirtProduct_kernel_bound (L W : ℕ) [NeZero L] [NeZero W]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, 0 < (z i).im) :
    ‖∑ a : Idx L W, ∑ b : Idx L W,
        (centeredVarianceEntry L W a b : ℂ) *
          wirtSecond L W
            (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
      (∑ i ∈ s,
        (∏ j ∈ s.erase i, (stieltjesN H (z j)).im) * paperL1Kernel L W H (z i)) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im) *
          paperL2Kernel L W H (z i) (z j) := by
  have hz0 : ∀ i ∈ s, (z i).im ≠ 0 := fun i hi => (ne_of_gt (hz i hi))
  rw [centeredVariance_wirtProduct_contraction_eq L W s H hH z hz0]
  have hfirst :
      ‖∑ i ∈ s,
        ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
          ((2 * (paperK1Contraction L W H (z i) true true).im : ℝ) : ℂ)‖ ≤
      ∑ i ∈ s,
        (∏ j ∈ s.erase i, (stieltjesN H (z j)).im) * paperL1Kernel L W H (z i) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hprod := OUContraction_stieltjesN_im_prod_nonneg hH z (s.erase i)
      (fun j hj => hz j (Finset.mem_of_mem_erase hj))
    have hterm := OUContraction_K1_im_abs_le hH (z i)
    have hmul := mul_le_mul_of_nonneg_left hterm hprod
    calc
      _ = (∏ j ∈ s.erase i, (stieltjesN H (z j)).im) *
          ‖((2 * (paperK1Contraction L W H (z i) true true).im : ℝ) : ℂ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
      _ ≤ _ := hmul
  have hsecond :
      ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
          (-(1 / 4 : ℂ) *
            (paperK2Contraction L W H (z i) (z j) true true -
              paperK2Contraction L W H (z i) (z j) true false -
              paperK2Contraction L W H (z i) (z j) false true +
              paperK2Contraction L W H (z i) (z j) false false))‖ ≤
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im) *
          paperL2Kernel L W H (z i) (z j) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have hprod := OUContraction_stieltjesN_im_prod_nonneg hH z ((s.erase i).erase j)
      (fun k hk => hz k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
    have hterm := OUContraction_K2_abs_le (H := H) (z i) (z j)
    have hmul := mul_le_mul_of_nonneg_left hterm hprod
    calc
      _ = (∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im) *
          ‖-(1 / 4 : ℂ) *
            (paperK2Contraction L W H (z i) (z j) true true -
              paperK2Contraction L W H (z i) (z j) true false -
              paperK2Contraction L W H (z i) (z j) false true +
              paperK2Contraction L W H (z i) (z j) false false)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
      _ ≤ _ := hmul
  calc
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hfirst hsecond)

end RBM.Univ

end
