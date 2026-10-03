/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.StepDecomp

/-!
# The quadratic-variation form of the linear part (`d = 2`)

The symmetric bilinear covariance form `vB` underlying `linTrVar` (`vB`, `vB_self`), and the
identity `v_gradMat_eq_quadVar`: the conditional-variance proxy `linTrVar n (gradMat Φ M)` is the
quadratic variation `Σ_c gvar_c ‖fderiv ℝ Φ M (coordinateMatrix c)‖²` over all coordinates
`c : Coord L W`.

The function `Φ` is only assumed to be differentiable at `M` (`DifferentiableAt ℝ Φ M`) and
real-valued on the Hermitian matrices.  The unused coordinates have `coordinateMatrix c = 0` and
contribute `0` on both sides.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {d : Sizes}

/-! ### The covariance form `vB` -/

/-- **`vB`**: the symmetric bilinear
covariance form underlying `linTrVar`. -/
noncomputable def vB (n : ℕ) (A A' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) : ℝ :=
  ∑ c ∈ coordFinset n, (Sizes.seqGvar d c : ℝ) * linTr n A (Sizes.seqXmat d n (Pi.single c 1))
      * linTr n A' (Sizes.seqXmat d n (Pi.single c 1))

/-- `linTrVar` as a real sum (a copy of the private `linTrVar_eq_sum` of `Path/Markov.lean`). -/
private theorem QVForm_linTrVar_eq_sum (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTrVar n A = ∑ c ∈ coordFinset n, (Sizes.seqGvar d c : ℝ)
      * (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) ^ 2 := by
  unfold linTrVar linVar
  push_cast [NNReal.coe_mk]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **`vB` on the diagonal is `linTrVar`.** -/
theorem vB_self (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    vB n A A = linTrVar n A := by
  rw [QVForm_linTrVar_eq_sum]
  unfold vB
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### `linTrVar n (gradMat Φ M)` is the quadratic variation -/

/-- A real-valued-on-Hermitian function has a real derivative along a Hermitian direction
(a copy of the private `StepDecomp_fderiv_im_eq_zero` of `Path/StepDecomp.lean`). -/
private theorem QVForm_fderiv_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M X : Matrix ι ι ℂ} (hd : DifferentiableAt ℝ Ψ M)
    (hReal : ∀ A, A.IsHermitian → (Ψ A).im = 0) (hM : M.IsHermitian) (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).im = 0 := by
  have hadd : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => M + t' • X) X t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const X).const_add M
  have hherm : ∀ t : ℝ, (M + t • X).IsHermitian := fun t => by
    have hcast : M + t • X = M + (t : ℂ) • X := by rw [Complex.coe_smul]
    rw [hcast]
    exact hM.add (hX.smul (Complex.conj_ofReal t))
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hadd 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  have hpath0 : ∀ t' : ℝ, (Ψ (M + t' • X)).im = 0 := fun t' => hReal _ (hherm t')
  have him0 : HasDerivAt (fun t' : ℝ => (Ψ (M + t' • X)).im) ((fderiv ℝ Ψ M X).im) 0 := by
    have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) Complex.imCLM.hasFDerivAt hp0
    simpa [Function.comp_def] using h1
  have hconst : (fun t' : ℝ => (Ψ (M + t' • X)).im) = fun _ : ℝ => (0 : ℝ) := funext hpath0
  rw [hconst] at him0
  exact him0.unique (hasDerivAt_const 0 0)

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem QVForm_seqXmat_single (n : ℕ) (c : Coord (d.L n) (d.W n)) :
    Sizes.seqXmat d n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) 1)
      = coordinateMatrix (d.L n) (d.W n) c := by
  have hs : Sizes.slice d n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) 1)
      = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) (1 : ℝ) : Sizes.SeqCoord d → ℝ) ⟨n, c'⟩
      = (Pi.single c (1 : ℝ) : Coord (d.L n) (d.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord d) ≠ ⟨n, c⟩ := fun he =>
        h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat coordinateMatrix
  rw [hs]

/-- **`v_gradMat_eq_quadVar`**: for `Φ` differentiable at `M`,
real-valued on the Hermitian matrices, and `M` Hermitian, the conditional-variance proxy
`linTrVar n (gradMat Φ M)` is the quadratic variation
`Σ_c gvar_c ‖fderiv ℝ Φ M (coordinateMatrix c)‖²` over all coordinates. -/
theorem v_gradMat_eq_quadVar (d : Sizes) (n : ℕ)
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hd : DifferentiableAt ℝ Φ M) (hReal : ∀ A, A.IsHermitian → (Φ A).im = 0)
    (hM : M.IsHermitian) :
    linTrVar n (gradMat Φ M)
      = ∑ c : Coord (d.L n) (d.W n), (gvar (d.L n) (d.W n) c : ℝ)
          * ‖fderiv ℝ Φ M (coordinateMatrix (d.L n) (d.W n) c)‖ ^ 2 := by
  classical
  rw [QVForm_linTrVar_eq_sum]
  unfold coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hX := coordinateMatrix_isHermitian (d.L n) (d.W n) c
  change (gvar (d.L n) (d.W n) c : ℝ) *
      (linTr n (gradMat Φ M) (Sizes.seqXmat d n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) 1))) ^ 2
    = _
  rw [QVForm_seqXmat_single, ← lin_eq_fderiv d n M hX]
  have him := QVForm_fderiv_im_eq_zero hd hReal hM hX
  have hz : fderiv ℝ Φ M (coordinateMatrix (d.L n) (d.W n) c)
      = ((fderiv ℝ Φ M (coordinateMatrix (d.L n) (d.W n) c)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hnormsq : ‖fderiv ℝ Φ M (coordinateMatrix (d.L n) (d.W n) c)‖ ^ 2
      = (fderiv ℝ Φ M (coordinateMatrix (d.L n) (d.W n) c)).re ^ 2 := by
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnormsq]

end RBM.Path

end
