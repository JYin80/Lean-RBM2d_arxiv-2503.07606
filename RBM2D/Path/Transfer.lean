/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Walk
import RBM2D.Path.PerTime
import RBM2D.Path.Step2Props

/-!
# Measurability of the Step 2 matrix functionals

The matrix functionals `lkErrMat` and `jStarMat` are measurable in the matrix argument
(`measurable_lkErrMat`, `measurable_jStarMat`).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-! ## Measurability of the matrix functionals -/

section MeasurableMatrix

private theorem transfer_measurable_matrix_inv_apply {n : Type*} [Fintype n] [DecidableEq n]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix n n ℂ} (hM : Measurable M) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

set_option linter.unusedFintypeInType false in
private theorem transfer_measurable_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) : Measurable fun M : Matrix n n ℂ => M - z • (1 : Matrix n n ℂ) :=
  (continuous_id.sub continuous_const).measurable

private theorem transfer_measurable_green {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (i j : n) : Measurable fun M : Matrix n n ℂ => green M z i j :=
  transfer_measurable_matrix_inv_apply (transfer_measurable_sub_smul_one z) i j

private theorem transfer_measurable_Gsig {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (σ : Bool) (i j : n) : Measurable fun M : Matrix n n ℂ => Gsig M z σ i j := by
  cases σ
  · simpa [Gsig] using transfer_measurable_green ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using transfer_measurable_green z i j

private theorem transfer_measurable_mul {ι : Type*} [Fintype ι]
    {Θ : Type*} [MeasurableSpace Θ] {A C : Θ → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hC : ∀ i j, Measurable fun x => C x i j)
    (i j : ι) : Measurable fun x => (A x * C x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem transfer_measurable_gloopProd (z : ℂ) (I : LoopIdx (Z2 L)) (i j : BlockIndex L W) :
    Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloopProd L W H z I i j := by
  suffices h : ∀ l : List (Bool × Z2 L), ∀ i j : BlockIndex L W,
      Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => (l.foldr
        (fun (p : Bool × Z2 L) (Acc : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =>
          Gsig H z p.1 * Eblk L W p.2 * Acc)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) i j by
    simpa [gloopProd] using h (I.σ.zip I.a) i j
  intro l
  induction l with
  | nil => intro i j; simp
  | cons p l ih =>
      intro i j
      simp only [List.foldr_cons]
      refine transfer_measurable_mul ?_ (fun a b => ih a b) i j
      intro a b
      refine transfer_measurable_mul (fun c e => transfer_measurable_Gsig z p.1 c e)
        (C := fun _ => Eblk L W p.2) (fun _ _ => measurable_const) a b

omit [NeZero W] in
private theorem transfer_measurable_gloop (z : ℂ) (I : LoopIdx (Z2 L)) :
    Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloop L W H z I := by
  have h : ∀ H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ, gloop L W H z I
      = ∑ i : BlockIndex L W, gloopProd L W H z I i i := fun _ => rfl
  simp only [h]
  exact Finset.measurable_sum _ fun i _ => transfer_measurable_gloopProd L W z I i i

private theorem transfer_measurable_blockMat :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => blockMat M :=
  (continuous_id.matrix_submatrix _ _).measurable

/-- `lkErrMat` is measurable in the matrix, unconditionally. -/
theorem measurable_lkErrMat (E u : ℝ) (a b : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => lkErrMat L W E u M a b :=
  (((transfer_measurable_gloop L W (spectralZ E u) (pmLoop a b)).comp
    (transfer_measurable_blockMat L W)).sub measurable_const).norm

/-- `jStarMat` is measurable in the matrix. -/
theorem measurable_jStarMat (E D u : ℝ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => jStarMat L W E D u M := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ))) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ =>
      (measurable_lkErrMat L W E u p.1 p.2).div_const _
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => jStarMat L W E D u M) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ))) M + 1 := by
    funext M
    simp only [jStarMat, Finset.sup'_apply]
  rw [heq]
  exact hsup.add_const 1

end MeasurableMatrix

end RBM.Path
