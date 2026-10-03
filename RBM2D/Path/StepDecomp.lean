/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Markov
import RBM2D.Path.Stop
import RBM2D.Gauss.Stein
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Algebra.Order.Chebyshev

/-!
# The one-step decomposition of a loop observable (`d = 2`)

For the grid walk `pathH` of `Path/Walk.lean`: a family `Φ_a` of observables (real on Hermitian
matrices), two-loop labels `a ∈ Z2 L × Z2 L` and real weights `U(b,a)` give the propagated
martingale increment `ξ_b = Σ_a U(b,a) (Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j])`, split as
`ξ_b = Z_b + Y_b` into a conditionally sub-Gaussian linear part
`Z_b = √Δ · linTr (Ab) X_{j+1}` and a quadratic remainder.

Contents: `gradMat`, `fderiv_eq_trace_gradMat`, `lin_eq_fderiv`, `Ab`, `stepZ`, `stepXi`,
`stepY`, `stepDecomp`, `stepDecomp_Y_sq`, `stepDecomp_Z_subG`, `integrable_normSq_incr`,
`integrable_normPow4_incr`.  The notation is `linTr`, `linTrVar`, `gridStep`, `pathH`,
`Sizes.seqXmat d n`, `pathP`; the QV form is in `Path/QVForm.lean`.

* **The Hermitian class.**  A loop observable is not even bounded off the Hermitian set (the
  resolvent is unbounded), so a global `C²` bound is replaced by `HermTestFun`: (H1) `C²` at
  Hermitian points and (H2) a bound at Hermitian points; the second-derivative bound (H3) is the
  separate hypothesis `hC₂ : ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ ‖y‖²` for Hermitian `M`, `y`.
  Where a proof needs a globally smooth function (continuity of `gradMat` along the walk) it
  composes with the Hermitian projection `M ↦ ½ (M + Mᴴ)`; the Taylor bound uses only points of
  the Hermitian segment `M + t y`.
* **`gradMat`** is built from the real-linear derivative on the Hermitian basis `E_ii`,
  `E_ij + E_ji`, `I E_ij - I E_ji`.
* The moments of `X` (`integral_normSq_incr_le`, `integral_normPow4_incr_le`) are polynomials in
  `N = (W L)²` (`Coord L W` has `2 N²` elements).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. The gradient matrix -/

section GradMat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The gradient matrix** of `Φ` at `M`, built from the real-linear derivative
`φ = fderiv ℝ Φ M` on the Hermitian basis `E_ii`, `S_ij = E_ij + E_ji`, `T_ij = I E_ij - I E_ji`:
`G_ii = φ(E_ii)` and, for `i ≠ j`, `G_ij = ½ (φ(S_ij) + I φ(T_ij))`.  For every Hermitian `X`,
`fderiv ℝ Φ M X = tr (gradMat Φ M * X)` (`fderiv_eq_trace_gradMat`). -/
def gradMat (Φ : Matrix ι ι ℂ → ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    if i = j then fderiv ℝ Φ M (Matrix.single i i 1)
    else (1 / 2 : ℂ) * (fderiv ℝ Φ M (Matrix.single i j 1 + Matrix.single j i 1)
      + Complex.I * fderiv ℝ Φ M (Matrix.single i j Complex.I - Matrix.single j i Complex.I))

omit [Fintype ι] in
private theorem StepDecomp_single_pair {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {i j : ι}
    (hij : i ≠ j) :
    Matrix.single i j (X i j) + Matrix.single j i (X j i)
      = (X i j).re • (Matrix.single i j (1 : ℂ) + Matrix.single j i 1)
        + (X i j).im • (Matrix.single i j Complex.I - Matrix.single j i Complex.I) := by
  have hji : X j i = (starRingEnd ℂ) (X i j) := (hX.apply j i).symm
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
    Complex.real_smul]
  by_cases h1 : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬(j = i ∧ i = j) := fun h => hij h.2
    simp only [and_self, ite_true, h2, ite_false, add_zero, sub_zero]
    apply Complex.ext <;> simp
  · by_cases h2 : j = k ∧ i = l
    · obtain ⟨rfl, rfl⟩ := h2
      have h3 : ¬(i = j ∧ j = i) := fun h => hij h.1
      simp only [h3, ite_false, and_self, ite_true, zero_add, hji]
      apply Complex.ext <;> simp
    · simp [h1, h2]

omit [Fintype ι] in
private theorem StepDecomp_single_diag {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (i : ι) :
    Matrix.single i i (X i i) = (X i i).re • Matrix.single i i (1 : ℂ) := by
  have hre : X i i = ((X i i).re : ℂ) := (Complex.conj_eq_iff_re.mp (hX.apply i i)).symm
  ext k l
  simp only [Matrix.smul_apply, Matrix.single_apply, Complex.real_smul]
  by_cases h : i = k ∧ i = l
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one]
    exact hre
  · simp only [h, ite_false, mul_zero]

/-- **The trace identity.**  For Hermitian `X`, `fderiv ℝ Φ M X = tr (gradMat Φ M * X)`; no
hypothesis on `Φ`. -/
theorem fderiv_eq_trace_gradMat {Φ : Matrix ι ι ℂ → ℂ} (M : Matrix ι ι ℂ) {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) : fderiv ℝ Φ M X = Matrix.trace (gradMat Φ M * X) := by
  set φ : Matrix ι ι ℂ →L[ℝ] ℂ := fderiv ℝ Φ M with hφ
  have hpair : ∀ i j, φ (Matrix.single i j (X i j)) + φ (Matrix.single j i (X j i))
      = gradMat Φ M i j * X j i + gradMat Φ M j i * X i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hre : X i i = ((X i i).re : ℂ) := (Complex.conj_eq_iff_re.mp (hX.apply i i)).symm
      rw [StepDecomp_single_diag hX, map_smul]
      simp only [gradMat, Matrix.of_apply, ite_true, Complex.real_smul]
      rw [← hφ]
      linear_combination (-2 * φ (Matrix.single i i 1)) * hre
    · have hji : X j i = (starRingEnd ℂ) (X i j) := (hX.apply j i).symm
      rw [← map_add, StepDecomp_single_pair hX hij, map_add, map_smul, map_smul]
      simp only [gradMat, Matrix.of_apply, hij, Ne.symm hij, ite_false]
      have hS : Matrix.single j i (1 : ℂ) + Matrix.single i j 1
          = Matrix.single i j 1 + Matrix.single j i 1 := add_comm _ _
      have hT : Matrix.single j i Complex.I - Matrix.single i j Complex.I
          = -(Matrix.single i j Complex.I - Matrix.single j i Complex.I) := by abel
      rw [hS, hT, hji, ← hφ]
      simp only [map_add, map_sub, map_neg, Complex.real_smul]
      have hx : X i j = ((X i j).re : ℂ) + ((X i j).im : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      have hxc : (starRingEnd ℂ) (X i j) = ((X i j).re : ℂ) - ((X i j).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hxc]
      set a := (X i j).re
      set b := (X i j).im
      rw [hx]
      linear_combination (↑b * (φ (Matrix.single i j Complex.I) - φ (Matrix.single j i Complex.I)))
        * Complex.I_sq
  have hF : φ X = ∑ i, ∑ j, φ (Matrix.single i j (X i j)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
  have hT : Matrix.trace (gradMat Φ M * X) = ∑ i, ∑ j, gradMat Φ M i j * X j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have hsw : ∀ f : ι → ι → ℂ, ∑ i, ∑ j, f j i = ∑ i, ∑ j, f i j := fun f => Finset.sum_comm
  have h2 : 2 * φ X = 2 * Matrix.trace (gradMat Φ M * X) := by
    have e1 : ∑ i, ∑ j, φ (Matrix.single j i (X j i)) = φ X := by
      rw [hF]; exact hsw (fun i j => φ (Matrix.single i j (X i j)))
    have e2 : ∑ i, ∑ j, gradMat Φ M j i * X i j = Matrix.trace (gradMat Φ M * X) := by
      rw [hT]; exact hsw (fun i j => gradMat Φ M i j * X j i)
    calc 2 * φ X
        = ∑ i, ∑ j, φ (Matrix.single i j (X i j)) + ∑ i, ∑ j, φ (Matrix.single j i (X j i)) := by
          rw [e1, ← hF]; ring
      _ = ∑ i, ∑ j, (gradMat Φ M i j * X j i + gradMat Φ M j i * X i j) := by
          simp only [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpair i j
      _ = 2 * Matrix.trace (gradMat Φ M * X) := by
          simp only [Finset.sum_add_distrib]
          rw [e2, ← hT]; ring
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h2

end GradMat

/-! ### 2. The Hermitian class and the Hermitian projection -/

/-- **The Hermitian class.**  `HermTestFun d n Φ` asks only for (H1) `C²` smoothness at every
Hermitian point and (H2) a bound at Hermitian points; a global bound is not available for a loop
observable, which is unbounded off the Hermitian set (the resolvent is unbounded).  The
Hermitian-direction bound (H3) on the second derivative is the separate hypothesis `hC₂` of the
theorems below. -/
structure HermTestFun (d : Sizes) (n : ℕ)
    (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) : Prop where
  contDiffAt : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M
  bdd₀ : ∃ C₀ : ℝ, ∀ M, M.IsHermitian → ‖Φ M‖ ≤ C₀

section Herm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian projection `M ↦ ½ (M + Mᴴ)` as a continuous `ℝ`-linear map. -/
private def StepDecomp_hermCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

private theorem StepDecomp_hermCLM_apply (M : Matrix ι ι ℂ) :
    StepDecomp_hermCLM ι M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

private theorem StepDecomp_isHermitian_hermCLM (M : Matrix ι ι ℂ) :
    (StepDecomp_hermCLM ι M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

private theorem StepDecomp_hermCLM_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    StepDecomp_hermCLM ι M = M := by
  rw [StepDecomp_hermCLM_apply, hM]
  module

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_single_diag (i : ι) :
    (Matrix.single i i (1 : ℂ)).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_single]

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_S (i j : ι) :
    (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

omit [Fintype ι] in
private theorem StepDecomp_isHermitian_T (i j : ι) :
    (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
  simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
  abel

/-- `Φ ∘ P` is `C²` everywhere when `Φ` is `C²` at every Hermitian point. -/
private theorem StepDecomp_contDiff_comp {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) :
    ContDiff ℝ 2 (fun M => Φ (StepDecomp_hermCLM ι M)) :=
  contDiff_iff_contDiffAt.2 fun M =>
    (h _ (StepDecomp_isHermitian_hermCLM M)).comp M (StepDecomp_hermCLM ι).contDiff.contDiffAt

/-- The first derivative of `Φ ∘ P` at a Hermitian point, along a Hermitian direction, is that of
`Φ`. -/
private theorem StepDecomp_fderiv_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    fderiv ℝ (fun M' => Φ (StepDecomp_hermCLM ι M')) M B = fderiv ℝ Φ M B := by
  have hPM := StepDecomp_hermCLM_of_isHermitian hM
  have hf : DifferentiableAt ℝ Φ (StepDecomp_hermCLM ι M) := by rw [hPM]; exact hΦ
  have h : HasFDerivAt (fun M' => Φ (StepDecomp_hermCLM ι M'))
      ((fderiv ℝ Φ (StepDecomp_hermCLM ι M)).comp (StepDecomp_hermCLM ι)) M :=
    hf.hasFDerivAt.comp M (StepDecomp_hermCLM ι).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hPM, StepDecomp_hermCLM_of_isHermitian hB]

/-- The gradient matrix of `Φ ∘ P` at a Hermitian point is that of `Φ`: `gradMat` reads `Φ`
only along Hermitian directions. -/
private theorem StepDecomp_gradMat_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) :
    gradMat (fun M' => Φ (StepDecomp_hermCLM ι M')) M = gradMat Φ M := by
  ext i j
  simp only [gradMat, Matrix.of_apply]
  rw [StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_single_diag i),
    StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_S i j),
    StepDecomp_fderiv_comp hM hΦ (StepDecomp_isHermitian_T i j)]

private theorem StepDecomp_continuous_gradMat {Ψ : Matrix ι ι ℂ → ℂ} (h : ContDiff ℝ 2 Ψ) :
    Continuous (gradMat Ψ) := by
  have hc : ∀ B : Matrix ι ι ℂ, Continuous fun M => fderiv ℝ Ψ M B :=
    fun B => (h.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine continuous_matrix fun i j => ?_
  simp only [gradMat, Matrix.of_apply]
  split_ifs
  · exact hc _
  · exact continuous_const.mul ((hc _).add (continuous_const.mul (hc _)))

end Herm

/-! ### 3. The second-order Taylor remainder along a Hermitian line -/

section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The affine line `t ↦ M + t • y` has derivative `y`. -/
private theorem StepDecomp_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem StepDecomp_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

/-- The derivative of `M' ↦ fderiv ℝ f M' A` is `(fderiv ℝ (fderiv ℝ f) M).flip A`, when
`fderiv ℝ f` is differentiable at `M`. -/
private theorem StepDecomp_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line**.  Only (H1) at
Hermitian points and the Hermitian-direction bound (H3) are used; every point of the segment
`M + t y` is Hermitian. -/
private theorem StepDecomp_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := StepDecomp_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (StepDecomp_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (StepDecomp_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (StepDecomp_hasDerivAt_add_smul M y t)
    simp only [ContinuousLinearMap.flip_apply] at h1
    exact h1
  set k : ℝ → ℂ := fun t => fderiv ℝ Φ (M + t • y) y with hk_def
  have hkCont : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have hlevel1 : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖k t - k 0‖ ≤ C₂ * ‖y‖ ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hkCont.continuousOn (fun t _ => (hk t).hasDerivWithinAt)
      (fun t _ => by simpa using hC₂ (M + t • y) y (hH t) hy)
  have hg : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y)
      (k t - k 0) t := by
    intro t
    have h1 := (hp t).sub_const (Φ M)
    have h2 : HasDerivAt (fun t' : ℝ => t' • fderiv ℝ Φ M y) (fderiv ℝ Φ M y) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ Φ M y)
    have h3 := h1.sub h2
    have hk0 : k 0 = fderiv ℝ Φ M y := by simp [hk_def]
    rw [hk0]
    exact h3
  set g : ℝ → ℂ := fun t' => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y with hg_def
  have hgCont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set B : ℝ → ℝ := fun t => (C₂ / 2) * ‖y‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t : ℝ, HasDerivAt B (C₂ * ‖y‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.const_mul (C₂ / 2 * ‖y‖ ^ 2)
    have heq : C₂ / 2 * ‖y‖ ^ 2 * (2 * t) = C₂ * ‖y‖ ^ 2 * t := by ring
    rw [heq] at h2
    exact h2
  have ha0 : ‖g 0‖ ≤ B 0 := by simp [hg_def, hB_def]
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hgCont.continuousOn (fun t _ => (hg t).hasDerivWithinAt) ha0 hB
    (fun t ht => by simpa using hlevel1 t ⟨ht.1, ht.2.le⟩)
  have hgs := hfinal (Set.right_mem_Icc.2 hs)
  simp only [hg_def, hB_def] at hgs
  have heq : C₂ / 2 * ‖y‖ ^ 2 * s ^ 2 = C₂ / 2 * s ^ 2 * ‖y‖ ^ 2 := by ring
  linarith [hgs, heq]

end Taylor

/-! ### 4. Moments of one increment: `E ‖X‖² ≤ 16 N⁴` and `E ‖X‖⁴ ≤ 768 N⁸`, `N = (W L)²`

The counting lemmas are proved here (`d = 2`: `Coord L W` has `2 N²` elements,
`N = (W L)²`). -/

section Moments

private theorem StepDecomp_norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι)
    (a : ℂ) : ‖(Matrix.single i j a : Matrix ι ι ℂ)‖ ≤ ‖a‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => ?_
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.single i j a) v
      = EuclideanSpace.single i (a * v j) := by
    ext k
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.single_mulVec, Function.update_apply]
  rw [h, EuclideanSpace.single, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- The `ℓ²` operator norm is at most the sum of the moduli of the entries. -/
private theorem StepDecomp_norm_le_sum_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => StepDecomp_norm_single_le i j _))

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem StepDecomp_norm_Xentry_le (ω : Ω L W) (i j : Idx L W) :
    ‖Xentry L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

private theorem StepDecomp_sum_coord (f : Coord L W → ℝ) :
    ∑ c : Coord L W, f c = ∑ i : Idx L W, ∑ j : Idx L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|` (in `Idx` coordinates, as `OneStep_norm_blockMat_Xmat_le`). -/
private theorem StepDecomp_norm_Xmat_le (ω : Ω L W) :
    ‖Xmat L W ω‖ ≤ 2 * ∑ c : Coord L W, |ω c| := by
  refine (StepDecomp_norm_le_sum_entries _).trans ?_
  rw [StepDecomp_sum_coord]
  have hswap : ∑ i : Idx L W, ∑ j : Idx L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx L W, ∑ j : Idx L W, ‖Xmat L W ω i j‖
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => StepDecomp_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

private theorem StepDecomp_gvar_le_one (c : Coord L W) : (gvar L W c : ℝ) ≤ 1 := by
  have hW : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : (W : ℝ)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW)
  have hs : svar L W c.1 c.2.1 ≤ 1 := by
    unfold svar
    split_ifs
    · linarith
    · exact zero_le_one
  have h0 := svar_nonneg L W c.1 c.2.1
  change (if c.1 = c.2.1 then svar L W c.1 c.2.1 else svar L W c.1 c.2.1 / 2) ≤ 1
  split_ifs <;> linarith

private theorem StepDecomp_card_Coord :
    (Fintype.card (Coord L W) : ℝ) = 2 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by
  have : Fintype.card (Coord L W) = 2 * (Fintype.card (Idx L W)) ^ 2 := by
    simp [Coord, Fintype.card_prod, Fintype.card_bool]
    ring
  rw [this]
  push_cast
  have h2 : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
    simp [Idx, Z2, pow_two]
  rw [h2]
  push_cast
  ring

/-! #### The fourth moment of a centred Gaussian coordinate -/

private theorem StepDecomp_integrable_pow_mul_pdf {v : ℝ≥0} (hv : 0 < (v : ℝ)) (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * gaussianPDFReal 0 v x := by
  have hb : (0 : ℝ) < 1 / (2 * (v : ℝ)) := by positivity
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).const_mul
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_natCast, gaussianPDFReal]
  rw [show -(1 / (2 * (v : ℝ))) * x ^ 2 = -(x - 0) ^ 2 / (2 * (v : ℝ)) by ring]
  ring

/-- `E x⁴ = 3 v²` for `x ~ N(0, v)`, by Stein's identity `E[x f(x)] = v E[f'(x)]` with `f = x³`;
only `E x⁴ ≤ 3` for `v ≤ 1` is kept. -/
private theorem StepDecomp_integral_pow4_gaussian {v : ℝ≥0} (hv1 : (v : ℝ) ≤ 1) :
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) ≤ 3 := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [gaussianReal_zero_var, integral_dirac]
    norm_num
  · have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv0))
    have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := fun x => by
      simpa using hasDerivAt_pow 3 x
    have h1 : Integrable fun x : ℝ => x ^ 3 * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
      have := (StepDecomp_integrable_pow_mul_pdf hvpos 4).const_mul (-(1 / (v : ℝ)))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      field_simp
    have h2 : Integrable fun x : ℝ => (3 * x ^ 2) * gaussianPDFReal 0 v x := by
      have := (StepDecomp_integrable_pow_mul_pdf hvpos 2).const_mul 3
      exact this.congr (Filter.Eventually.of_forall fun x => by simp only; ring)
    have h3 := StepDecomp_integrable_pow_mul_pdf hvpos 3
    have hst := integral_mul_gaussianReal hv0 hf h1 h2 h3
    have hsq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
      have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
      rw [variance_eq_integral measurable_id'.aemeasurable] at h
      simpa using h
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
      (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    rw [integral_const_mul, hsq] at hst
    have hx : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) * (3 * (v : ℝ)) := by
      rw [← hst]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    rw [hx]
    nlinarith [hvpos, hv1]

end Moments

section MomentsBound

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem StepDecomp_integrable_pow4_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => (ω c) ^ 4) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 4) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    have h := (memLp_id_gaussianReal (μ := 0) (v := gvar L W c) 4).integrable_norm_pow
      (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [id, Real.norm_eq_abs]
    exact (Even.pow_abs (by decide) x)
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem StepDecomp_integral_pow4_coord_le (c : Coord L W) :
    ∫ ω : Ω L W, (ω c) ^ 4 ∂(P L W) ≤ 3 := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 4) ((P L W).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  exact StepDecomp_integral_pow4_gaussian (StepDecomp_gvar_le_one c)

private theorem StepDecomp_norm_sq_le (ω : Ω L W) :
    ‖Xmat L W ω‖ ^ 2 ≤ 4 * (Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 2 := by
  have h := StepDecomp_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat L W ω)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : Coord L W => |ω c|)
  simp only [sq_abs, Finset.card_univ] at hcs
  calc ‖Xmat L W ω‖ ^ 2 ≤ (2 * ∑ c : Coord L W, |ω c|) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 4 * (∑ c : Coord L W, |ω c|) ^ 2 := by ring
    _ ≤ 4 * ((Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 2) := by linarith
    _ = _ := by ring

private theorem StepDecomp_norm_pow4_le (ω : Ω L W) :
    ‖Xmat L W ω‖ ^ 4 ≤ 16 * (Fintype.card (Coord L W) : ℝ) ^ 3 * ∑ c : Coord L W, (ω c) ^ 4 := by
  have h := StepDecomp_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat L W ω)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : Coord L W => |ω c|)
  simp only [sq_abs, Finset.card_univ] at hcs
  have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : Coord L W => (ω c) ^ 2)
  simp only [← pow_mul, Finset.card_univ] at hcs2
  have hcard : (0 : ℝ) ≤ (Fintype.card (Coord L W) : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ ∑ c : Coord L W, |ω c| := Finset.sum_nonneg fun c _ => abs_nonneg _
  calc ‖Xmat L W ω‖ ^ 4 ≤ (2 * ∑ c : Coord L W, |ω c|) ^ 4 := pow_le_pow_left₀ h0 h 4
    _ = 16 * ((∑ c : Coord L W, |ω c|) ^ 2) ^ 2 := by ring
    _ ≤ 16 * ((Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 2) ^ 2 := by
        gcongr
    _ = 16 * (Fintype.card (Coord L W) : ℝ) ^ 2 * (∑ c : Coord L W, (ω c) ^ 2) ^ 2 := by ring
    _ ≤ 16 * (Fintype.card (Coord L W) : ℝ) ^ 2
          * ((Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 4) := by
        gcongr
    _ = _ := by ring

private theorem StepDecomp_integrable_normSq :
    Integrable (fun ω : Ω L W => ‖Xmat L W ω‖ ^ 2) (P L W) := by
  have hint : Integrable (fun ω : Ω L W =>
      4 * (Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 2) (P L W) :=
    (integrable_finsetSum _ fun c _ => integrable_sq_coord L W c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat L W)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact StepDecomp_norm_sq_le ω

private theorem StepDecomp_integrable_normPow4 :
    Integrable (fun ω : Ω L W => ‖Xmat L W ω‖ ^ 4) (P L W) := by
  have hint : Integrable (fun ω : Ω L W =>
      16 * (Fintype.card (Coord L W) : ℝ) ^ 3 * ∑ c : Coord L W, (ω c) ^ 4) (P L W) :=
    (integrable_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat L W)).pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact StepDecomp_norm_pow4_le ω

private theorem StepDecomp_integral_normSq_le :
    ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 2 ∂(P L W) ≤ 16 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 4 := by
  have hcard := StepDecomp_card_Coord (L := L) (W := W)
  calc ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 2 ∂(P L W)
      ≤ ∫ ω : Ω L W, 4 * (Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (ω c) ^ 2 ∂(P L W) :=
        integral_mono StepDecomp_integrable_normSq
          ((integrable_finsetSum _ fun c _ => integrable_sq_coord L W c).const_mul _)
          fun ω => StepDecomp_norm_sq_le ω
    _ = 4 * (Fintype.card (Coord L W) : ℝ) * ∑ c : Coord L W, (gvar L W c : ℝ) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => integrable_sq_coord L W c]
        simp only [integral_sq_coord]
    _ ≤ 4 * (Fintype.card (Coord L W) : ℝ) * ∑ _c : Coord L W, (1 : ℝ) := by
        gcongr with c
        exact StepDecomp_gvar_le_one c
    _ = 16 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
        ring

private theorem StepDecomp_integral_normPow4_le :
    ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 4 ∂(P L W) ≤ 768 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 8 := by
  have hcard := StepDecomp_card_Coord (L := L) (W := W)
  calc ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 4 ∂(P L W)
      ≤ ∫ ω : Ω L W, 16 * (Fintype.card (Coord L W) : ℝ) ^ 3 * ∑ c : Coord L W, (ω c) ^ 4
          ∂(P L W) :=
        integral_mono StepDecomp_integrable_normPow4
          ((integrable_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c).const_mul _)
          fun ω => StepDecomp_norm_pow4_le ω
    _ = 16 * (Fintype.card (Coord L W) : ℝ) ^ 3
          * ∑ c : Coord L W, ∫ ω : Ω L W, (ω c) ^ 4 ∂(P L W) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => StepDecomp_integrable_pow4_coord c]
    _ ≤ 16 * (Fintype.card (Coord L W) : ℝ) ^ 3 * ∑ _c : Coord L W, (3 : ℝ) := by
        gcongr with c
        exact StepDecomp_integral_pow4_coord_le c
    _ = 768 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 8 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

end MomentsBound

section MomentsPath

variable (d : Sizes)

private theorem StepDecomp_map_incr_slice (n j : ℕ) :
    (pathP d).map (fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) = P (d.L n) (d.W n) := by
  have h := Measure.map_map (μ := pathP d) (Sizes.measurable_slice d n)
    (measurable_pi_apply (j + 1) : Measurable fun ω : PathΩ d => ω (j + 1))
  rw [map_incr, Sizes.seqP_map_slice] at h
  exact h.symm

private theorem StepDecomp_measurable_incr (n j : ℕ) :
    Measurable fun ω : PathΩ d => Sizes.slice d n (ω (j + 1)) :=
  (Sizes.measurable_slice d n).comp (measurable_pi_apply (j + 1))

/-- Transfer of a fixed-size function along one increment, through `map_incr` and
`Sizes.seqP_map_slice`: integrability, and the value of the integral. -/
private theorem StepDecomp_transfer (n j : ℕ) {f : Ω (d.L n) (d.W n) → ℝ}
    (hf : Integrable f (P (d.L n) (d.W n))) :
    Integrable (fun ω : PathΩ d => f (Sizes.slice d n (ω (j + 1)))) (pathP d) ∧
      ∫ ω : PathΩ d, f (Sizes.slice d n (ω (j + 1))) ∂(pathP d)
        = ∫ x, f x ∂(P (d.L n) (d.W n)) := by
  have hmap := StepDecomp_map_incr_slice d n j
  have hgm : AEStronglyMeasurable f
      ((pathP d).map fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have hm : AEMeasurable (fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) (pathP d) :=
    (StepDecomp_measurable_incr d n j).aemeasurable
  refine ⟨(integrable_map_measure hgm hm).1 (by rw [hmap]; exact hf), ?_⟩
  have h := integral_map hm hgm
  rw [hmap] at h
  exact h.symm

/-- `‖X_{j+1}‖²` is integrable. -/
theorem integrable_normSq_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ d => ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2) (pathP d) :=
  (StepDecomp_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 2) StepDecomp_integrable_normSq).1

/-- `‖X_{j+1}‖⁴` is integrable. -/
theorem integrable_normPow4_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ d => ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4) (pathP d) :=
  (StepDecomp_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 4) StepDecomp_integrable_normPow4).1

/-- **The second moment of one increment**: `E ‖X_{j+1}‖² ≤ 16 N⁴`, `N = (W L)²`. -/
theorem integral_normSq_incr_le (n j : ℕ) :
    ∫ ω : PathΩ d, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 ∂(pathP d)
      ≤ 16 * (Sizes.size d n : ℝ) ^ 4 :=
  le_of_eq_of_le (StepDecomp_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 2) StepDecomp_integrable_normSq).2
    (StepDecomp_integral_normSq_le (L := d.L n) (W := d.W n))

/-- **The fourth moment of one increment**: `E ‖X_{j+1}‖⁴ ≤ 768 N⁸`, `N = (W L)²`. -/
theorem integral_normPow4_incr_le (n j : ℕ) :
    ∫ ω : PathΩ d, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d)
      ≤ 768 * (Sizes.size d n : ℝ) ^ 8 :=
  le_of_eq_of_le (StepDecomp_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 4) StepDecomp_integrable_normPow4).2
    (StepDecomp_integral_normPow4_le (L := d.L n) (W := d.W n))

end MomentsPath

/-! ### 5. The decomposition of one grid step -/

section StepDecomp

variable (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
  {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}

/-- **`Ab`**: the `filt d j`-measurable direction attached to a label-indexed family `Φ`, a real
backward kernel `U` and a target label `b`: `Ab ω = Σ_a U(b,a) • gradMat (Φ a) (H_j ω)`. -/
noncomputable def Ab (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) • gradMat (Φ a) (pathH d s t K n j ω)

/-- **`stepZ`**: the exactly linear part of one grid step, `Z b ω = √Δ · linTr n (Ab ω) X_{j+1}`. -/
noncomputable def stepZ (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n (Ab d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- **`stepXi`**: the propagated observable minus its `filt d j`-conditional mean,
`ξ_b = Σ_a U(b,a) Φ_a(H_{j+1}) - E[Σ_a U(b,a) Φ_a(H_{j+1}) | F_j]`. -/
noncomputable def stepXi (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) : ℂ :=
  (∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω))
    - (pathP d)[fun ω' => ∑ a : Z2 (d.L n) × Z2 (d.L n),
        (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω

/-- **`stepY`**: the quadratic remainder, `Y_b = ξ_b - Z_b`. -/
noncomputable def stepY (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) : ℂ :=
  stepXi d s t K n j Φ U b ω - (stepZ d s t K n j Φ U b ω : ℂ)

/-- **`lin_eq_fderiv`**: the real part of the derivative in a Hermitian direction is `linTr` of
the gradient matrix. -/
theorem lin_eq_fderiv {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    {X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).re = linTr n (gradMat Ψ M) X := by
  rw [fderiv_eq_trace_gradMat M hX]; rfl

/-- The grid walk is `filt d j`-measurable as a matrix-valued map, and measurable. -/
private theorem StepDecomp_measurable_pathH (k : ℕ) :
    Measurable fun ω : PathΩ d => pathH d s t K n k ω :=
  (pathH_measurable_filt d s t K n k).mono ((filt d).le k) le_rfl

private theorem StepDecomp_measurable_seqXmat (i : ℕ) :
    Measurable fun ω : PathΩ d => Sizes.seqXmat d n (ω i) :=
  ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).comp
    (measurable_pi_apply i)

/-- The grid recursion `H_{k+1} = H_k + √Δ X_{k+1}` with the real scalar (a private copy of
`pathH_succ` of `Path/LoopStep.lean`). -/
private theorem StepDecomp_pathH_succ (k : ℕ) (ω : PathΩ d) :
    pathH d s t K n (k + 1) ω
      = pathH d s t K n k ω + Real.sqrt (gridStep s t K n) • Sizes.seqXmat d n (ω (k + 1)) := by
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [← Complex.coe_smul]
  unfold pathH
  rw [hins, Finset.sum_insert (by simp), smul_add]
  abel


/-- `Ψ` along the walk is `filt d k`-measurable: `Ψ` agrees with the `C²` function `Ψ ∘ P` at
every Hermitian point, and the walk is Hermitian. -/
private theorem StepDecomp_measurable_phi_filt {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΨ : HermTestFun d n Ψ) (k : ℕ) :
    Measurable[filt d k] fun ω : PathΩ d => Ψ (pathH d s t K n k ω) := by
  have hcont := (StepDecomp_contDiff_comp hΨ.contDiffAt).continuous
  have heq : (fun ω : PathΩ d => Ψ (pathH d s t K n k ω))
      = fun ω => Ψ (StepDecomp_hermCLM _ (pathH d s t K n k ω)) := funext fun ω => by
    rw [StepDecomp_hermCLM_of_isHermitian (pathH_isHermitian d s t K n k ω)]
  rw [heq]
  exact hcont.measurable.comp (pathH_measurable_filt d s t K n k)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2). -/
private theorem StepDecomp_integrable_phi {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΨ : HermTestFun d n Ψ) (k : ℕ) :
    Integrable (fun ω : PathΩ d => Ψ (pathH d s t K n k ω)) (pathP d) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  have hm : Measurable fun ω : PathΩ d => Ψ (pathH d s t K n k ω) :=
    (StepDecomp_measurable_phi_filt d s t K n hΨ k).mono ((filt d).le k) le_rfl
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian d s t K n k ω))).integrable le_top

/-- A real-valued-on-Hermitian function has a real derivative along a Hermitian direction. -/
private theorem StepDecomp_fderiv_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M X : Matrix ι ι ℂ} (hd : DifferentiableAt ℝ Ψ M)
    (hReal : ∀ A, A.IsHermitian → (Ψ A).im = 0) (hM : M.IsHermitian) (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).im = 0 := by
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (StepDecomp_hasDerivAt_add_smul M X 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  have hpath0 : ∀ t' : ℝ, (Ψ (M + t' • X)).im = 0 := fun t' =>
    hReal _ (StepDecomp_isHermitian_add_smul hM hX t')
  have him0 : HasDerivAt (fun t' : ℝ => (Ψ (M + t' • X)).im) ((fderiv ℝ Ψ M X).im) 0 := by
    have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) Complex.imCLM.hasFDerivAt hp0
    simpa [Function.comp_def] using h1
  have hconst : (fun t' : ℝ => (Ψ (M + t' • X)).im) = fun _ : ℝ => (0 : ℝ) := funext hpath0
  rw [hconst] at him0
  exact him0.unique (hasDerivAt_const 0 0)

/-- `Ab` is `filt d j`-measurable: `gradMat`
of a member of the Hermitian class is a continuous function of the Hermitian walk, through the
Hermitian projection. -/
private theorem StepDecomp_measurable_Ab (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Measurable[filt d j] (fun ω : PathΩ d => Ab d s t K n j Φ U b ω) := by
  have hgrad : ∀ a, Measurable[filt d j] (fun ω : PathΩ d => gradMat (Φ a) (pathH d s t K n j ω)) := by
    intro a
    have hcont := StepDecomp_continuous_gradMat (StepDecomp_contDiff_comp (hΦ a).contDiffAt)
    have heq : (fun ω : PathΩ d => gradMat (Φ a) (pathH d s t K n j ω))
        = fun ω => gradMat (fun M' => Φ a (StepDecomp_hermCLM _ M')) (pathH d s t K n j ω) :=
      funext fun ω => (StepDecomp_gradMat_comp (pathH_isHermitian d s t K n j ω)
        (((hΦ a).contDiffAt _ (pathH_isHermitian d s t K n j ω)).differentiableAt
          (by norm_num))).symm
    rw [heq]
    exact hcont.measurable.comp (pathH_measurable_filt d s t K n j)
  exact Finset.measurable_sum _ fun a _ => (hgrad a).const_smul (U b a : ℂ)

/-- **`StepDecomp_Rlabel`**: the per-label Taylor remainder of one grid step,
`Φ(H_{j+1}) - Φ(H_j) - √Δ · fderiv ℝ Φ (H_j) X_{j+1}`. -/
private def StepDecomp_Rlabel
    (Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (ω : PathΩ d) : ℂ :=
  Ψ (pathH d s t K n (j + 1) ω) - Ψ (pathH d s t K n j ω)
    - Real.sqrt (gridStep s t K n) •
      fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- The pathwise Taylor remainder bound, from (H1) and the Hermitian-direction bound (H3). -/
private theorem StepDecomp_norm_Rlabel_le
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Ψ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (ω : PathΩ d) :
    ‖StepDecomp_Rlabel d s t K n j Ψ ω‖
      ≤ (C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
  unfold StepDecomp_Rlabel
  rw [StepDecomp_pathH_succ]
  have hkey := StepDecomp_taylor hΨ.contDiffAt hC₂ (pathH_isHermitian d s t K n j ω)
    (Sizes.seqXmat_isHermitian d n (ω (j + 1))) (Real.sqrt_nonneg (gridStep s t K n))
  rwa [Real.sq_sqrt hΔ] at hkey

private theorem StepDecomp_measurable_Rlabel
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ) :
    Measurable (StepDecomp_Rlabel d s t K n j Ψ) := by
  have h1 := (StepDecomp_measurable_phi_filt d s t K n hΨ (j + 1)).mono ((filt d).le (j + 1)) le_rfl
  have h2 := (StepDecomp_measurable_phi_filt d s t K n hΨ j).mono ((filt d).le j) le_rfl
  have hcont : Continuous fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ
      × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      fderiv ℝ (fun M' => Ψ (StepDecomp_hermCLM _ M')) p.1 p.2 :=
    (((StepDecomp_contDiff_comp hΨ.contDiffAt).continuous_fderiv (by norm_num)).comp
      continuous_fst).clm_apply continuous_snd
  have h3 : Measurable fun ω : PathΩ d =>
      fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))) := by
    have heq : (fun ω : PathΩ d => fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
        = fun ω => fderiv ℝ (fun M' => Ψ (StepDecomp_hermCLM _ M')) (pathH d s t K n j ω)
            (Sizes.seqXmat d n (ω (j + 1))) := funext fun ω =>
      (StepDecomp_fderiv_comp (pathH_isHermitian d s t K n j ω)
        ((hΨ.contDiffAt _ (pathH_isHermitian d s t K n j ω)).differentiableAt (by norm_num))
        (Sizes.seqXmat_isHermitian d n (ω (j + 1)))).symm
    rw [heq]
    exact hcont.measurable.comp
      ((StepDecomp_measurable_pathH d s t K n j).prodMk (StepDecomp_measurable_seqXmat d n (j + 1)))
  unfold StepDecomp_Rlabel
  simp only [Complex.real_smul]
  exact (h1.sub h2).sub (h3.const_mul _)

/-- **The pathwise bound on the `Ab`-weighted sum of Taylor remainders**: `O(Δ)` in `‖X_{j+1}‖²`
with the constant `(Σ_a |U(b,a)|)(C₂/2)`. -/
private theorem StepDecomp_norm_Rlabel_sum_le (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) :
    ‖∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω‖
      ≤ (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω‖
      ≤ ∑ a : Z2 (d.L n) × Z2 (d.L n),
          ‖(U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a| * ‖StepDecomp_Rlabel d s t K n j (Φ a) ω‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_mul, show ‖(U b a : ℂ)‖ = |U b a| from RCLike.norm_ofReal (U b a)]
    _ ≤ ∑ a : Z2 (d.L n) × Z2 (d.L n),
          |U b a| * ((C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          (StepDecomp_norm_Rlabel_le d s t K n j (hΦ a) (hC₂ a) hΔ ω) (abs_nonneg _)
    _ = (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- The `Ab`-weighted sum of Taylor remainders is integrable: measurable and dominated by a
multiple of the integrable `‖X_{j+1}‖²`. -/
private theorem StepDecomp_integrable_Rlabel_sum (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Integrable (fun ω : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω) (pathP d) := by
  have hmeas : Measurable fun ω : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω :=
    Finset.measurable_sum _ fun a _ => (StepDecomp_measurable_Rlabel d s t K n j (hΦ a)).const_mul _
  have hgint : Integrable (fun ω : PathΩ d =>
      (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2) (pathP d) :=
    (integrable_normSq_incr d n j).const_mul _
  exact hgint.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => StepDecomp_norm_Rlabel_sum_le d s t K n j hΦ hC₂ hΔ U b ω)

/-- `linTr` is real-linear in its direction argument, specialised to the `Ab` combination. -/
private theorem StepDecomp_lin_Ab_eq_sum
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n (Ab d s t K n j Φ U b ω) X
      = ∑ a : Z2 (d.L n) × Z2 (d.L n),
          U b a * linTr n (gradMat (Φ a) (pathH d s t K n j ω)) X := by
  unfold linTr Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : Z2 (d.L n) × Z2 (d.L n),
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (pathH d s t K n j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (pathH d s t K n j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **The key algebraic bridge**: the `Ab`-weighted
first-order term is exactly `stepZ`, because each `Φ a` is real on Hermitian matrices and `U` is
real. -/
private theorem StepDecomp_sum_fderiv_eq_stepZ (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) :
    (Real.sqrt (gridStep s t K n) : ℂ) *
      (∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) *
        fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
      = (stepZ d s t K n j Φ U b ω : ℂ) := by
  have hHherm := pathH_isHermitian d s t K n j ω
  have hXherm := Sizes.seqXmat_isHermitian d n (ω (j + 1))
  have hterm : ∀ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) *
      fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1)))
      = ((U b a * linTr n (gradMat (Φ a) (pathH d s t K n j ω))
          (Sizes.seqXmat d n (ω (j + 1))) : ℝ) : ℂ) := by
    intro a
    have h1 := StepDecomp_fderiv_im_eq_zero
      ((hΦ a).contDiffAt _ hHherm |>.differentiableAt (by norm_num)) (hReal a) hHherm hXherm
    have h2 := lin_eq_fderiv d n (Ψ := Φ a) (pathH d s t K n j ω) hXherm
    have h3 : fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1)))
        = ((linTr n (gradMat (Φ a) (pathH d s t K n j ω))
            (Sizes.seqXmat d n (ω (j + 1))) : ℝ) : ℂ) :=
      Complex.ext (by simpa using h2) (by simpa using h1)
    rw [h3]; push_cast; ring
  simp only [hterm]
  rw [← Complex.ofReal_sum, ← StepDecomp_lin_Ab_eq_sum d s t K n j U b ω
    (Sizes.seqXmat d n (ω (j + 1)))]
  unfold stepZ
  push_cast
  ring

/-- `Z`, as a complex function, has conditional mean zero: the real-valued
`condExp_linear_eq_zero`, lifted along `ℝ ↪ ℂ`. -/
private theorem StepDecomp_condExp_stepZ_eq_zero (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    (pathP d)[fun ω => (stepZ d s t K n j Φ U b ω : ℂ) | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℂ) := by
  have hreal : (pathP d)[stepZ d s t K n j Φ U b | filt d j] =ᵐ[pathP d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j (StepDecomp_measurable_Ab d s t K n j hΦ U b)
      Set.univ MeasurableSet.univ (show Integrable
        (fun ω => Real.sqrt (gridStep s t K n) *
          linTr n (Ab d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1)))) (pathP d) from hIntReal)
    rw [Set.indicator_univ] at h
    unfold stepZ
    exact h
  have hlift := ContinuousLinearMap.comp_condExp_comm (μ := pathP d) (m := filt d j)
    hIntReal Complex.ofRealCLM
  have hlift' : (fun ω => (((pathP d)[stepZ d s t K n j Φ U b | filt d j]) ω : ℂ))
      =ᵐ[pathP d] (pathP d)[fun ω => (stepZ d s t K n j Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hlift
  refine hlift'.symm.trans ?_
  filter_upwards [hreal] with ω hω
  simp [hω]

/-- **The pointwise identity**: `Σ_a U(b,a) Φ_a(H_{j+1})`
splits into the `F_j`-measurable term, `stepZ`, and the weighted Taylor remainder. -/
private theorem StepDecomp_g_eq_pointwise (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) :
    (∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω))
      = (∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n j ω))
        + (stepZ d s t K n j Φ U b ω : ℂ)
        + ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω := by
  have hZ := StepDecomp_sum_fderiv_eq_stepZ d s t K n j hΦ hReal U b ω
  have hexpand : ∀ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω)
        = (U b a : ℂ) * Φ a (pathH d s t K n j ω)
          + (Real.sqrt (gridStep s t K n) : ℂ) * ((U b a : ℂ) *
              fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
          + (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω := by
    intro a
    have hR : StepDecomp_Rlabel d s t K n j (Φ a) ω
        = Φ a (pathH d s t K n (j + 1) ω) - Φ a (pathH d s t K n j ω)
          - (Real.sqrt (gridStep s t K n) : ℂ) *
            fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))) := by
      unfold StepDecomp_Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0 := Σ_a U(b,a)·Φ_a(H_jω)` is `filt d j`-measurable. -/
private theorem StepDecomp_measurable_h0
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Measurable[filt d j]
      (fun ω : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n j ω)) := by
  exact Finset.measurable_sum _ fun a _ =>
    (StepDecomp_measurable_phi_filt d s t K n (hΦ a) j).const_mul (U b a : ℂ)

/-- `h0` is integrable: it is a finite sum of bounded functions. -/
private theorem StepDecomp_integrable_h0
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Integrable
      (fun ω : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n j ω)) (pathP d) :=
  integrable_finsetSum _ fun a _ =>
    (StepDecomp_integrable_phi d s t K n (hΦ a) j).const_mul (U b a : ℂ)

/-- `Z`, cast to `ℂ`, is integrable (the real cast of an integrable real function). -/
private theorem StepDecomp_integrable_stepZ_complex
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    Integrable (fun ω => (stepZ d s t K n j Φ U b ω : ℂ)) (pathP d) :=
  hIntReal.ofReal

/-- **The a.e. identity behind `stepDecomp`**.  `ξ b` agrees
a.e. with `Z b` plus the `Ab`-weighted Taylor-remainder martingale difference. -/
private theorem StepDecomp_stepXi_eq_ae
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    stepXi d s t K n j Φ U b
      =ᵐ[pathP d] fun ω => (stepZ d s t K n j Φ U b ω : ℂ)
        + ((∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω)
          - (pathP d)[fun ω' => ∑ a : Z2 (d.L n) × Z2 (d.L n),
              (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω' | filt d j] ω) := by
  set h0 : PathΩ d → ℂ :=
    fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n j ω) with hh0def
  set R : PathΩ d → ℂ :=
    fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω with hRdef
  set Zc : PathΩ d → ℂ := fun ω => (stepZ d s t K n j Φ U b ω : ℂ) with hZcdef
  set g : PathΩ d → ℂ :=
    fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R := funext fun ω => StepDecomp_g_eq_pointwise d s t K n j hΦ hReal U b ω
  have hh0meas := StepDecomp_measurable_h0 d s t K n j hΦ U b
  have hh0int := StepDecomp_integrable_h0 d s t K n j hΦ U b
  have hZcint := StepDecomp_integrable_stepZ_complex d s t K n j U b hIntReal
  have hRint := StepDecomp_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have hcondg : (pathP d)[g | filt d j]
      =ᵐ[pathP d] (pathP d)[h0 | filt d j] + (pathP d)[Zc | filt d j] + (pathP d)[R | filt d j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt d j)).trans
      ((condExp_add hh0int hZcint (filt d j)).add (EventuallyEq.refl _ _))
  have hh0cond : (pathP d)[h0 | filt d j] =ᵐ[pathP d] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt d).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (pathP d)[Zc | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) :=
    StepDecomp_condExp_stepZ_eq_zero d s t K n j hΦ U b hIntReal
  have hstepXi : stepXi d s t K n j Φ U b = fun ω => g ω - (pathP d)[g | filt d j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (pathP d)[g | filt d j] ω = h0 ω + (pathP d)[R | filt d j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`stepY` a.e. equals the `Ab`-weighted Taylor remainder minus its own conditional mean**.
Immediate from `StepDecomp_stepXi_eq_ae` and `stepY := stepXi - Z` (pointwise). -/
private theorem StepDecomp_stepY_eq_ae
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    stepY d s t K n j Φ U b
      =ᵐ[pathP d] fun ω => (∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω)
        - (pathP d)[fun ω' => ∑ a : Z2 (d.L n) × Z2 (d.L n),
            (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω' | filt d j] ω := by
  have hXi := StepDecomp_stepXi_eq_ae d s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  filter_upwards [hXi] with ω hω
  change stepXi d s t K n j Φ U b ω - (stepZ d s t K n j Φ U b ω : ℂ) = _
  rw [hω]; ring

/-- **The pathwise bound on `Y`, a.e.**.
`‖Y b ω‖ ≤ C₂'·Δ·‖X(ω(j+1))‖² + (its conditional
mean)`, with the explicit constant `C₂' := (Σ_a |U(b,a)|)·(C₂/2)`. -/
private theorem StepDecomp_stepY_norm_le_ae
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    ∀ᵐ ω ∂(pathP d), ‖stepY d s t K n j Φ U b ω‖
      ≤ (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2
        + (pathP d)[fun ω' => (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
            * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω := by
  have hY := StepDecomp_stepY_eq_ae d s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  set R : PathΩ d → ℂ :=
    fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω with hRdef
  set g : PathΩ d → ℝ := fun ω => (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω := fun ω => StepDecomp_norm_Rlabel_sum_le d s t K n j hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (pathP d) := (integrable_normSq_incr d n j).const_mul _
  have hRint : Integrable R (pathP d) := StepDecomp_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have hcondRmono : (pathP d)[fun ω => ‖R ω‖ | filt d j] ≤ᵐ[pathP d] (pathP d)[g | filt d j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(pathP d)[R | filt d j] x‖) ≤ᵐ[pathP d] (pathP d)[fun x => ‖R x‖ | filt d j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (pathP d)[R | filt d j] ω‖
      ≤ ‖R ω‖ + ‖(pathP d)[R | filt d j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (pathP d)[g | filt d j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

/-- **`stepDecomp`: the one-step decomposition of a loop observable** (for observables of the class
`HermTestFun`, with the Hermitian-direction bound `hC₂`).  (i) `ξ_b = Z_b + Y_b` pointwise; (ii)
`Ab` is
`filt d j`-measurable; (iii) a.e., `‖Y_b‖ ≤ g + E[g | F_j]` with
`g = (Σ_a |U(b,a)|) ((C₂/2) Δ) ‖X_{j+1}‖²`; (iv) `E[Y_b | F_j] = 0`. -/
theorem stepDecomp (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    (∀ ω, stepXi d s t K n j Φ U b ω
        = (stepZ d s t K n j Φ U b ω : ℂ) + stepY d s t K n j Φ U b ω)
      ∧ Measurable[filt d j] (fun ω => Ab d s t K n j Φ U b ω)
      ∧ (∀ᵐ ω ∂(pathP d), ‖stepY d s t K n j Φ U b ω‖
          ≤ (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
              * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2
            + (pathP d)[fun ω' => (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω)
      ∧ (pathP d)[stepY d s t K n j Φ U b | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) :=
  ⟨fun ω => by unfold stepY; ring, StepDecomp_measurable_Ab d s t K n j hΦ U b,
    StepDecomp_stepY_norm_le_ae d s t K n j hΦ hReal hC₂ hΔ U b hIntReal,
    by
      have hY := StepDecomp_stepY_eq_ae d s t K n j hΦ hReal hC₂ hΔ U b hIntReal
      have hRint := StepDecomp_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
      have hcond : (pathP d)[fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n),
          (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω
            - (pathP d)[fun ω' => ∑ a : Z2 (d.L n) × Z2 (d.L n),
                (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω' | filt d j] ω | filt d j]
          =ᵐ[pathP d] fun _ => (0 : ℂ) := by
        set R : PathΩ d → ℂ :=
          fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω with hRdef
        have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt d j)) (filt d j)
        have hidem : (pathP d)[(pathP d)[R | filt d j] | filt d j] =ᵐ[pathP d] (pathP d)[R | filt d j] :=
          condExp_condExp_of_le (le_refl (filt d j)) ((filt d).le j)
        have hfe : (fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * StepDecomp_Rlabel d s t K n j (Φ a) ω
            - (pathP d)[R | filt d j] ω) = R - (pathP d)[R | filt d j] := by
          funext ω
          change R ω - (pathP d)[R | filt d j] ω = (R - (pathP d)[R | filt d j]) ω
          rw [Pi.sub_apply]
        rw [hfe]
        filter_upwards [hsub, hidem] with ω hω1 hω2
        rw [hω1]
        simp only [Pi.sub_apply]
        rw [hω2]
        ring
      exact (condExp_congr_ae hY).trans hcond⟩

/-- **`stepDecomp_Y_sq`: the `L²` bound on `Y`**:
`∫ ‖Y_b‖² ≤ 4 ((Σ_a |U(b,a)|) C₂/2)² Δ² ∫ ‖X_{j+1}‖⁴`.  From (iii) of `stepDecomp`,
`(x+y)² ≤ 2x²+2y²`, conditional Jensen at `x ↦ x²` (`ConvexOn.map_condExp_le_univ`) and the
tower property (`integral_condExp`). -/
theorem stepDecomp_Y_sq (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (hIntReal : Integrable (stepZ d s t K n j Φ U b) (pathP d)) :
    ∫ ω, ‖stepY d s t K n j Φ U b ω‖ ^ 2 ∂(pathP d)
      ≤ 4 * ((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := by
  have hYbound := StepDecomp_stepY_norm_le_ae d s t K n j hΦ hReal hC₂ hΔ U b hIntReal
  set g : PathΩ d → ℝ := fun ω => (∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 with hgdef
  -- the key algebraic identity behind `g²`, in the exact grouping the target constant needs
  have heqg2 : (fun ω => (g ω) ^ 2)
      = fun ω => (((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
        * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 := by
    rw [hgdef]; funext ω; ring
  have hgint : Integrable g (pathP d) := by
    rw [hgdef]
    exact (integrable_normSq_incr d n j).const_mul
      ((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n))
  have hg2int : Integrable (fun ω => (g ω) ^ 2) (pathP d) := by
    rw [heqg2]
    exact (integrable_normPow4_incr d n j).const_mul
      (((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2)
  have hg2eq : ∫ ω, (g ω) ^ 2 ∂(pathP d)
      = ((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := by
    rw [heqg2, integral_const_mul]
  -- the conditional Jensen inequality at the convex map `x ↦ x²`
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow even_two
  have hcont : LowerSemicontinuous (fun x : ℝ => x ^ 2) := (continuous_pow 2).lowerSemicontinuous
  have hJensen : (fun ω => ((pathP d)[g | filt d j] ω) ^ 2)
      ≤ᵐ[pathP d] (pathP d)[fun ω => (g ω) ^ 2 | filt d j] :=
    hcvx.map_condExp_le_univ ((filt d).le j) hcont hgint hg2int
  -- combine the pathwise bound with `(x+y)² ≤ 2x²+2y²` and the Jensen bound
  have hcomb : ∀ᵐ ω ∂(pathP d), ‖stepY d s t K n j Φ U b ω‖ ^ 2
      ≤ 2 * (g ω) ^ 2 + 2 * (pathP d)[fun ω' => (g ω') ^ 2 | filt d j] ω := by
    filter_upwards [hYbound, hJensen] with ω h1 h2
    have hsq : ‖stepY d s t K n j Φ U b ω‖ ^ 2
        ≤ (g ω + (pathP d)[g | filt d j] ω) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hsq, h2, sq_nonneg (g ω - (pathP d)[g | filt d j] ω)]
  have hRHSint : Integrable (fun ω => 2 * (g ω) ^ 2
      + 2 * (pathP d)[fun ω' => (g ω') ^ 2 | filt d j] ω) (pathP d) :=
    (hg2int.const_mul 2).add (Integrable.const_mul integrable_condExp 2)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    hRHSint hcomb
  rw [integral_add (hg2int.const_mul 2) (Integrable.const_mul integrable_condExp 2),
    integral_const_mul, integral_const_mul, integral_condExp ((filt d).le j), hg2eq] at hmono
  have hgoal : (2 : ℝ) * (((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d))
      + 2 * (((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2
        * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d))
      = 4 * ((∑ a : Z2 (d.L n) × Z2 (d.L n), |U b a|) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
        * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := by ring
  linarith [hmono, hgoal]

/-- **`stepDecomp_Z_subG`: `Z_b` is conditionally sub-Gaussian**: on a `filt d j`-event `E` where
`Δ · linTrVar (Ab ω) ≤ c`, the
`hasCondSubgaussianMGF_linear` applied to `A := Ab`, since `stepZ` is exactly
`√Δ · linTr n (Ab ω) X_{j+1}`. -/
theorem stepDecomp_Z_subG (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (E : Set (PathΩ d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ E, gridStep s t K n * linTrVar n (Ab d s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZ d s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP d) := by
  have h := hasCondSubgaussianMGF_linear (d := d) s t K n j (StepDecomp_measurable_Ab d s t K n j hΦ U b) E hE c hc
    hbound
  simpa only [stepZ] using h

/-- **Integrability of `Z`:** `hIntReal` is a consequence of the other
hypotheses of `stepDecomp`: `Z` is `Σ_a U Φ_a(H_{j+1}) - Σ_a U Φ_a(H_j) - Σ_a U R_a`, a difference
of integrable functions (bounded and measurable by (H1)-(H2); `R` by (H3)). -/
theorem stepDecomp_integrable_stepZ (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun d n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Integrable (stepZ d s t K n j Φ U b) (pathP d) := by
  have hg : Integrable (fun ω : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω)) (pathP d) :=
    integrable_finsetSum _ fun a _ =>
      (StepDecomp_integrable_phi d s t K n (hΦ a) (j + 1)).const_mul (U b a : ℂ)
  have hZc : Integrable (fun ω : PathΩ d => (stepZ d s t K n j Φ U b ω : ℂ)) (pathP d) := by
    have h := (hg.sub (StepDecomp_integrable_h0 d s t K n j hΦ U b)).sub
      (StepDecomp_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    rw [StepDecomp_g_eq_pointwise d s t K n j hΦ hReal U b ω]
    ring
  have h := hZc.re
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp

end StepDecomp

end RBM.Path

end
