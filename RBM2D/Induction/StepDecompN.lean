/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.LoopC2N
import RBM2D.Path.LoopStep
import RBM2D.Path.StepDecomp

/-!
# The complex-valued one-step decomposition `ξ = Z + Y` of the grid walk (`d = 2`)

For a label-indexed family `Φ_a` of complex
observables in the Hermitian test class `HermTestFun` (module `RBM2D.Path.StepDecomp`) and a complex kernel
`U`, one grid step `H_j ↦ H_{j+1} = H_j + √Δ X_{j+1}` splits the propagated martingale increment
`ξ_b = Σ_a U(b,a) (Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j])` as `ξ_b = Z_b + Y_b`:
`Z_b = √Δ tr(A_b X_{j+1})` is exactly linear in the Gaussian increment (real part `stepZCN_re`,
imaginary part `stepZCN_im`, `A_b = Σ_a U(b,a) ∇Φ_a(H_j)` is `F_j`-measurable), and `Y_b` is a
Taylor remainder with `E[Y_b | F_j] = 0` and `‖Y_b‖ ≤ g + E[g | F_j]`,
`g = (Σ_a ‖U(b,a)‖) (C₂/2) Δ ‖X_{j+1}‖²`.  No reality hypothesis on `Φ` or `U` is needed: the
imaginary part of the first-order term is `stepZCN_im` (`√Δ · linTr ((-I) • A) X = √Δ Im tr(A X)`).

Paper: arXiv:2503.07606, Section 5: the martingale term of the stopped hierarchy
(`int_K-L_ST`, `alu9_STime`).  The split `ξ = Z + Y` is a device of the formalization (the paper
bounds the martingale term by BDG moments).

## Main declarations (namespace `RBM.Ind`)

* Definitions: `AbCN`, `stepZCN_re`, `stepZCN_im`, `stepZCN`, `stepXiCN`, `stepYCN`,
  `StepDecompCN_Stmt`, `loopFamN`.
* `stepDecompCN : StepDecompCN_Stmt d` -- (i) `ξ = Z + Y`, (ii) `AbCN` is `filt d j`-measurable,
  (iii) `‖Y‖ ≤ g + E[g | F_j]` a.e., (iv) `E[Y | F_j] = 0`.
* `stepDecompCN_Z_subG` -- `E.indicator stepZCN_re`, `E.indicator stepZCN_im` are conditionally
  sub-Gaussian with the same parameter `c` (`hasCondSubgaussianMGF_linear`).
* `integrable_stepZCN_re_of_hermTestFun`, `integrable_stepZCN_im_of_hermTestFun` -- the
  integrability hypotheses of `stepDecompCN` are dischargeable.
* Identification for the loop family `loopFamN`: `martIncN_eq_stepXiCN`,
  `YvecN_eq_stepYCN` (a.e., all labels at once), `ZvecN_eq_stepZCN` (pointwise), and with the
  `Ugen` kernel `Ugen_stepYCN`.  The test-class input of the
  loop family is proved directly from `hermTestFunLoopN`; no
  `HermTestFunLoopN` hypothesis appears in any statement (only `j + 1 ≤ K n`, `|E n| < 2`,
  `0 ≤ s n ≤ t n`, `t n < 1`, and `[NeZero k]` for the `Ugen` statement, as `Ugen` needs it).

## Relation to the real decomposition and the one-dimensional case

The argument follows the one-dimensional complex decomposition on the structure of the real
`stepDecomp` of `RBM2D.Path.StepDecomp` (`HermTestFun`, Hermitian bound `hC₂`), whose private
helpers (Hermitian projection, `C²` composition, Taylor bound along a Hermitian line, walk
measurability, integrability) are reproduced with the prefix `StepDecompN_`.  Changes with respect
to the one-dimensional case: the global `C²` bound (`TestFun`) becomes `HermTestFun` and the
bound `hC₂` at Hermitian `M, y` (the segment `[H_j, H_{j+1}]` is Hermitian); labels
`LoopArg (d.L N) n` become an arbitrary `Fintype ι` (`ι : Type` in `StepDecompCN_Stmt`); the
walk, step and trace notation becomes `PathΩ d`, `pathP d`, `pathH`, `Sizes.seqXmat d n`,
`gridStep`, `linTr`, `linTrVar`; `gradMat` is built from the real-linear derivative
on the Hermitian basis.  Every helper is `private` or carries the prefix `StepDecompN_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. Definitions -/

section StatementDefs

variable (d : Sizes)

/-- **`AbCN`**: the `filt d j`-measurable direction of a label-indexed complex family `Φ` with a
complex kernel `U` and target label `b`: `Σ_a U(b,a) • gradMat (Φ a) (H_j)` (the real version is
`Ab` of `RBM2D.Path.StepDecomp`). -/
def AbCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  ∑ a, U b a • gradMat (Φ a) (pathH d s t K n j ω)

/-- Real part of the linear term: `√Δ · linTr (AbCN) X_{j+1}`. -/
def stepZCN_re (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n (AbCN d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- Imaginary part of the linear term: `√Δ · linTr ((−I) • AbCN) X_{j+1}`. -/
def stepZCN_im (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : ℝ :=
  Real.sqrt (gridStep s t K n) *
    linTr n ((-Complex.I) • AbCN d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- **`stepZCN`**: the exactly linear part of one grid step, complex. -/
def stepZCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : ℂ :=
  (stepZCN_re d s t K n j Φ U b ω : ℂ) + Complex.I * (stepZCN_im d s t K n j Φ U b ω : ℂ)

/-- **`stepXiCN`**: the propagated observable minus its `filt d j`-conditional mean. -/
def stepXiCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : ℂ :=
  (∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω))
    - (pathP d)[fun ω' => ∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω

/-- **`stepYCN`**: the remainder `ξ − Z`. -/
def stepYCN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (U : ι → ι → ℂ) (b : ι)
    (ω : PathΩ d) : ℂ :=
  stepXiCN d s t K n j Φ U b ω - stepZCN d s t K n j Φ U b ω

/-- **Statement of `stepDecompCN`** (with the class `HermTestFun`
and the Hermitian-direction bound `hC₂` of the real `stepDecomp` of `RBM2D.Path.StepDecomp`;
no reality hypothesis): (i) `ξ = Z + Y` pointwise; (ii) `AbCN` is `filt d j`-measurable; (iii) a.e.
`‖Y‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖U(b,a)‖)(C₂/2)Δ‖X_{j+1}‖²`; (iv) `E[Y | F_j] = 0`. -/
def StepDecompCN_Stmt : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type} [Fintype ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ},
    (∀ a, HermTestFun d n (Φ a)) → ∀ {C₂ : ℝ},
    (∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2) →
    0 ≤ gridStep s t K n → ∀ (U : ι → ι → ℂ) (b : ι),
    Integrable (stepZCN_re d s t K n j Φ U b) (pathP d) →
    Integrable (stepZCN_im d s t K n j Φ U b) (pathP d) →
    (∀ ω, stepXiCN d s t K n j Φ U b ω
        = stepZCN d s t K n j Φ U b ω + stepYCN d s t K n j Φ U b ω)
      ∧ Measurable[filt d j] (fun ω => AbCN d s t K n j Φ U b ω)
      ∧ (∀ᵐ ω ∂(pathP d), ‖stepYCN d s t K n j Φ U b ω‖
          ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2
            + (pathP d)[fun ω' => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω)
      ∧ (pathP d)[stepYCN d s t K n j Φ U b | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ)

/-- **`loopFamN`**: the loop family `a ↦ (M ↦ 𝓛_{u_{j+1},σ,a}(M))` at the spectral time
of the step `j → j+1`; with the identity kernel it turns `stepXiCN`, `stepZCN`, `stepYCN` into
`martIncN`, `ZvecN`, `YvecN`. -/
def loopFamN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Z2 (d.L n)) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ :=
  fun a M => gloop (d.L n) (d.W n) (blockMat M) (spectralZ (E n) (gridTime s t K n (j + 1)))
    (loopOf σ a)

end StatementDefs

/-! ## 2. Helpers on the Hermitian class

The Hermitian projection, the `C²` composition, `gradMat` along the projection and the pathwise
second-order Taylor bound along a Hermitian line, with the prefix `StepDecompN_`
(the real counterparts are private in `RBM2D.Path.StepDecomp`). -/

section Herm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian projection `M ↦ ½ (M + Mᴴ)` as a continuous `ℝ`-linear map. -/
private def StepDecompN_hermCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
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

private theorem StepDecompN_hermCLM_apply (M : Matrix ι ι ℂ) :
    StepDecompN_hermCLM ι M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

private theorem StepDecompN_isHermitian_hermCLM (M : Matrix ι ι ℂ) :
    (StepDecompN_hermCLM ι M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

private theorem StepDecompN_hermCLM_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    StepDecompN_hermCLM ι M = M := by
  rw [StepDecompN_hermCLM_apply, hM]
  module

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_single_diag (i : ι) :
    (Matrix.single i i (1 : ℂ)).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_single]

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_S (i j : ι) :
    (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

omit [Fintype ι] in
private theorem StepDecompN_isHermitian_T (i j : ι) :
    (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
  simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
  abel

/-- `Φ ∘ P` is `C²` everywhere when `Φ` is `C²` at every Hermitian point. -/
private theorem StepDecompN_contDiff_comp {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) :
    ContDiff ℝ 2 (fun M => Φ (StepDecompN_hermCLM ι M)) :=
  contDiff_iff_contDiffAt.2 fun M =>
    (h _ (StepDecompN_isHermitian_hermCLM M)).comp M (StepDecompN_hermCLM ι).contDiff.contDiffAt

/-- The first derivative of `Φ ∘ P` at a Hermitian point, along a Hermitian direction, is that of
`Φ`. -/
private theorem StepDecompN_fderiv_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    fderiv ℝ (fun M' => Φ (StepDecompN_hermCLM ι M')) M B = fderiv ℝ Φ M B := by
  have hPM := StepDecompN_hermCLM_of_isHermitian hM
  have hf : DifferentiableAt ℝ Φ (StepDecompN_hermCLM ι M) := by rw [hPM]; exact hΦ
  have h : HasFDerivAt (fun M' => Φ (StepDecompN_hermCLM ι M'))
      ((fderiv ℝ Φ (StepDecompN_hermCLM ι M)).comp (StepDecompN_hermCLM ι)) M :=
    hf.hasFDerivAt.comp M (StepDecompN_hermCLM ι).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hPM, StepDecompN_hermCLM_of_isHermitian hB]

/-- The gradient matrix of `Φ ∘ P` at a Hermitian point is that of `Φ`: `gradMat` reads `Φ`
only along Hermitian directions. -/
private theorem StepDecompN_gradMat_comp {Φ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hΦ : DifferentiableAt ℝ Φ M) :
    gradMat (fun M' => Φ (StepDecompN_hermCLM ι M')) M = gradMat Φ M := by
  ext i j
  simp only [gradMat, Matrix.of_apply]
  rw [StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_single_diag i),
    StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_S i j),
    StepDecompN_fderiv_comp hM hΦ (StepDecompN_isHermitian_T i j)]

private theorem StepDecompN_continuous_gradMat {Ψ : Matrix ι ι ℂ → ℂ} (h : ContDiff ℝ 2 Ψ) :
    Continuous (gradMat Ψ) := by
  have hc : ∀ B : Matrix ι ι ℂ, Continuous fun M => fderiv ℝ Ψ M B :=
    fun B => (h.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine continuous_matrix fun i j => ?_
  simp only [gradMat, Matrix.of_apply]
  split_ifs
  · exact hc _
  · exact continuous_const.mul ((hc _).add (continuous_const.mul (hc _)))

end Herm

section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of `t' ↦ M + t' • y` at any point is `y`. -/
private theorem StepDecompN_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem StepDecompN_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

/-- The derivative of `M' ↦ fderiv ℝ f M' A` is the flipped second derivative applied to `A`. -/
private theorem StepDecompN_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line**.  Only (H1) at
Hermitian points and the Hermitian-direction bound (H3) are used; every point of the segment
`M + t y` is Hermitian. -/
private theorem StepDecompN_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := StepDecompN_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (StepDecompN_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (StepDecompN_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (StepDecompN_hasDerivAt_add_smul M y t)
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

/-! ## 3. The per-step lemmas (complex kernel, general label type) -/

section PerStep

variable (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}

/-- The grid walk is measurable as a matrix-valued map. -/
private theorem StepDecompN_measurable_pathH (k : ℕ) :
    Measurable fun ω : PathΩ d => pathH d s t K n k ω :=
  (pathH_measurable_filt d s t K n k).mono ((filt d).le k) le_rfl

private theorem StepDecompN_measurable_seqXmat (i : ℕ) :
    Measurable fun ω : PathΩ d => Sizes.seqXmat d n (ω i) :=
  ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).comp
    (measurable_pi_apply i)

/-- The grid recursion `H_{k+1} = H_k + √Δ X_{k+1}` with the real scalar (`pathH_succ` of
`RBM2D.Path.LoopStep` has the complex scalar). -/
private theorem StepDecompN_pathH_succ (k : ℕ) (ω : PathΩ d) :
    pathH d s t K n (k + 1) ω
      = pathH d s t K n k ω + Real.sqrt (gridStep s t K n) • Sizes.seqXmat d n (ω (k + 1)) := by
  rw [pathH_succ, Complex.coe_smul]

/-- `Ψ` along the walk is `filt d k`-measurable (cf. `StepDecomp_measurable_phi_filt`). -/
private theorem StepDecompN_measurable_phi_filt
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΨ : HermTestFun d n Ψ) (k : ℕ) :
    Measurable[filt d k] fun ω : PathΩ d => Ψ (pathH d s t K n k ω) := by
  have hcont := (StepDecompN_contDiff_comp hΨ.contDiffAt).continuous
  have heq : (fun ω : PathΩ d => Ψ (pathH d s t K n k ω))
      = fun ω => Ψ (StepDecompN_hermCLM _ (pathH d s t K n k ω)) := funext fun ω => by
    rw [StepDecompN_hermCLM_of_isHermitian (pathH_isHermitian d s t K n k ω)]
  rw [heq]
  exact hcont.measurable.comp (pathH_measurable_filt d s t K n k)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2) (cf.
`StepDecomp_integrable_phi`). -/
private theorem StepDecompN_integrable_phi
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΨ : HermTestFun d n Ψ) (k : ℕ) :
    Integrable (fun ω : PathΩ d => Ψ (pathH d s t K n k ω)) (pathP d) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  have hm : Measurable fun ω : PathΩ d => Ψ (pathH d s t K n k ω) :=
    (StepDecompN_measurable_phi_filt d s t K n hΨ k).mono ((filt d).le k) le_rfl
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian d s t K n k ω))).integrable le_top

/-- `AbCN` is `filt d j`-measurable (cf. `StepDecomp_measurable_Ab`): `gradMat` of a member of the Hermitian class is a continuous
function of the Hermitian walk, through the Hermitian projection. -/
private theorem StepDecompN_measurable_AbCN (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) : Measurable[filt d j] (fun ω : PathΩ d => AbCN d s t K n j Φ U b ω) := by
  have hgrad : ∀ a, Measurable[filt d j]
      (fun ω : PathΩ d => gradMat (Φ a) (pathH d s t K n j ω)) := by
    intro a
    have hcont := StepDecompN_continuous_gradMat (StepDecompN_contDiff_comp (hΦ a).contDiffAt)
    have heq : (fun ω : PathΩ d => gradMat (Φ a) (pathH d s t K n j ω))
        = fun ω => gradMat (fun M' => Φ a (StepDecompN_hermCLM _ M')) (pathH d s t K n j ω) :=
      funext fun ω => (StepDecompN_gradMat_comp (pathH_isHermitian d s t K n j ω)
        (((hΦ a).contDiffAt _ (pathH_isHermitian d s t K n j ω)).differentiableAt
          (by norm_num))).symm
    rw [heq]
    exact hcont.measurable.comp (pathH_measurable_filt d s t K n j)
  exact Finset.measurable_sum _ fun a _ => (hgrad a).const_smul (U b a)

/-- **`Rlabel`**: the per-label Taylor remainder of one grid step,
`Φ(H_{j+1}) - Φ(H_j) - √Δ · fderiv ℝ Φ (H_j) X_{j+1}` (cf. `StepDecomp_Rlabel`). -/
private def StepDecompN_Rlabel
    (Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (ω : PathΩ d) : ℂ :=
  Ψ (pathH d s t K n (j + 1) ω) - Ψ (pathH d s t K n j ω)
    - Real.sqrt (gridStep s t K n) •
      fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- The pathwise Taylor remainder bound, from (H1) and the Hermitian-direction bound (H3). -/
private theorem StepDecompN_norm_Rlabel_le
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Ψ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (ω : PathΩ d) :
    ‖StepDecompN_Rlabel d s t K n j Ψ ω‖
      ≤ (C₂ / 2) * gridStep s t K n * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
  unfold StepDecompN_Rlabel
  rw [StepDecompN_pathH_succ]
  have hkey := StepDecompN_taylor hΨ.contDiffAt hC₂ (pathH_isHermitian d s t K n j ω)
    (Sizes.seqXmat_isHermitian d n (ω (j + 1))) (Real.sqrt_nonneg (gridStep s t K n))
  rwa [Real.sq_sqrt hΔ] at hkey

private theorem StepDecompN_measurable_Rlabel
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ) :
    Measurable (StepDecompN_Rlabel d s t K n j Ψ) := by
  have h1 := (StepDecompN_measurable_phi_filt d s t K n hΨ (j + 1)).mono
    ((filt d).le (j + 1)) le_rfl
  have h2 := (StepDecompN_measurable_phi_filt d s t K n hΨ j).mono ((filt d).le j) le_rfl
  have hcont : Continuous fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ
      × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      fderiv ℝ (fun M' => Ψ (StepDecompN_hermCLM _ M')) p.1 p.2 :=
    (((StepDecompN_contDiff_comp hΨ.contDiffAt).continuous_fderiv (by norm_num)).comp
      continuous_fst).clm_apply continuous_snd
  have h3 : Measurable fun ω : PathΩ d =>
      fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))) := by
    have heq : (fun ω : PathΩ d =>
        fderiv ℝ Ψ (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
        = fun ω => fderiv ℝ (fun M' => Ψ (StepDecompN_hermCLM _ M')) (pathH d s t K n j ω)
            (Sizes.seqXmat d n (ω (j + 1))) := funext fun ω =>
      (StepDecompN_fderiv_comp (pathH_isHermitian d s t K n j ω)
        ((hΨ.contDiffAt _ (pathH_isHermitian d s t K n j ω)).differentiableAt (by norm_num))
        (Sizes.seqXmat_isHermitian d n (ω (j + 1)))).symm
    rw [heq]
    exact hcont.measurable.comp
      ((StepDecompN_measurable_pathH d s t K n j).prodMk
        (StepDecompN_measurable_seqXmat d n (j + 1)))
  unfold StepDecompN_Rlabel
  simp only [Complex.real_smul]
  exact (h1.sub h2).sub (h3.const_mul _)

/-- **The pathwise bound on the `U`-weighted sum of Taylor remainders**, complex `U`: `O(Δ)` in
`‖X_{j+1}‖²` with the constant `(Σ_a ‖U(b,a)‖)(C₂/2)`. -/
private theorem StepDecompN_norm_Rlabel_sum_le (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) (ω : PathΩ d) :
    ‖∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω‖
      ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω‖
      ≤ ∑ a, ‖U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a, ‖U b a‖ * ‖StepDecompN_Rlabel d s t K n j (Φ a) ω‖ :=
        Finset.sum_congr rfl fun a _ => norm_mul _ _
    _ ≤ ∑ a, ‖U b a‖ * ((C₂ / 2) * gridStep s t K n
          * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          (StepDecompN_norm_Rlabel_le d s t K n j (hΦ a) (hC₂ a) hΔ ω) (norm_nonneg _)
    _ = (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
          * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- The `U`-weighted sum of Taylor remainders is integrable: measurable and dominated by a multiple of the integrable `‖X_{j+1}‖²`. -/
private theorem StepDecompN_integrable_Rlabel_sum (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (fun ω : PathΩ d => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω)
      (pathP d) := by
  have hmeas : Measurable fun ω : PathΩ d =>
      ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω :=
    Finset.measurable_sum _ fun a _ =>
      (StepDecompN_measurable_Rlabel d s t K n j (hΦ a)).const_mul _
  have hgint : Integrable (fun ω : PathΩ d =>
      (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
        * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2) (pathP d) :=
    (integrable_normSq_incr d n j).const_mul _
  exact hgint.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω =>
      StepDecompN_norm_Rlabel_sum_le d s t K n j hΦ hC₂ hΔ U b ω)

end PerStep

/-! ## 4. The linear part `stepZCN`: the algebraic bridge and its conditional mean -/

section LinearPart

variable (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}

/-- **The key algebraic fact**: `linTr` at the direction `(-I) • A` reads the imaginary part of
`trace (A * X)`.  Together with
`linTr n A X = (trace (A * X)).re` (its definition) this is why `stepZCN` is the whole complex
first-order term, with no reality hypothesis. -/
private theorem StepDecompN_linTr_neg_I_smul
    (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- **The complex algebraic bridge**: the `U`-weighted sum
of directional derivatives is `stepZCN`, unconditionally (no reality of `Φ` or `U`). -/
private theorem StepDecompN_sum_fderiv_eq_stepZCN (U : ι → ι → ℂ) (b : ι) (ω : PathΩ d) :
    (Real.sqrt (gridStep s t K n) : ℂ) *
      (∑ a, U b a * fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
      = stepZCN d s t K n j Φ U b ω := by
  have hXherm := Sizes.seqXmat_isHermitian d n (ω (j + 1))
  have hcomb : (∑ a, U b a * fderiv ℝ (Φ a) (pathH d s t K n j ω)
        (Sizes.seqXmat d n (ω (j + 1))))
      = Matrix.trace (AbCN d s t K n j Φ U b ω * Sizes.seqXmat d n (ω (j + 1))) := by
    unfold AbCN
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, fderiv_eq_trace_gradMat _ hXherm]
  rw [hcomb]
  set w := Matrix.trace (AbCN d s t K n j Φ U b ω * Sizes.seqXmat d n (ω (j + 1))) with hw
  have hre : linTr n (AbCN d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1))) = w.re := rfl
  have him : linTr n ((-Complex.I) • AbCN d s t K n j Φ U b ω)
      (Sizes.seqXmat d n (ω (j + 1))) = w.im := StepDecompN_linTr_neg_I_smul d n _ _
  unfold stepZCN stepZCN_re stepZCN_im
  rw [hre, him]
  have hreim := Complex.re_add_im w
  push_cast
  linear_combination (Real.sqrt (gridStep s t K n) : ℂ) * hreim.symm

/-- **The pointwise identity**: `Σ_a U(b,a) Φ_a(H_{j+1})` splits
into the `F_j`-measurable term, `stepZCN`, and the `U`-weighted Taylor remainder. -/
private theorem StepDecompN_g_eq_pointwise (U : ι → ι → ℂ) (b : ι) (ω : PathΩ d) :
    (∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω))
      = (∑ a, U b a * Φ a (pathH d s t K n j ω))
        + stepZCN d s t K n j Φ U b ω
        + ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω := by
  have hZ := StepDecompN_sum_fderiv_eq_stepZCN d s t K n j (Φ := Φ) U b ω
  have hexpand : ∀ a,
      U b a * Φ a (pathH d s t K n (j + 1) ω)
        = U b a * Φ a (pathH d s t K n j ω)
          + (Real.sqrt (gridStep s t K n) : ℂ) *
              (U b a * fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))))
          + U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω := by
    intro a
    have hR : StepDecompN_Rlabel d s t K n j (Φ a) ω
        = Φ a (pathH d s t K n (j + 1) ω) - Φ a (pathH d s t K n j ω)
          - (Real.sqrt (gridStep s t K n) : ℂ) *
            fderiv ℝ (Φ a) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))) := by
      unfold StepDecompN_Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0 := Σ_a U(b,a)·Φ_a(H_j ω)` is `filt d j`-measurable. -/
private theorem StepDecompN_measurable_h0 (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) :
    Measurable[filt d j] (fun ω : PathΩ d => ∑ a, U b a * Φ a (pathH d s t K n j ω)) :=
  Finset.measurable_sum _ fun a _ =>
    (StepDecompN_measurable_phi_filt d s t K n (hΦ a) j).const_mul (U b a)

/-- `h0` is integrable: a finite sum of bounded functions. -/
private theorem StepDecompN_integrable_h0 (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ)
    (b : ι) :
    Integrable (fun ω : PathΩ d => ∑ a, U b a * Φ a (pathH d s t K n j ω)) (pathP d) :=
  integrable_finsetSum _ fun a _ =>
    (StepDecompN_integrable_phi d s t K n (hΦ a) j).const_mul (U b a)

/-- `stepZCN`, as a complex-valued function, is integrable given integrability of its real and
imaginary parts. -/
private theorem StepDecompN_integrable_stepZCN (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re d s t K n j Φ U b) (pathP d))
    (hIntIm : Integrable (stepZCN_im d s t K n j Φ U b) (pathP d)) :
    Integrable (stepZCN d s t K n j Φ U b) (pathP d) := by
  have h1 : Integrable (fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ)) (pathP d) := hIntRe.ofReal
  have h2 : Integrable (fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ)) (pathP d) := hIntIm.ofReal
  have h3 : Integrable (fun ω => Complex.I * (stepZCN_im d s t K n j Φ U b ω : ℂ)) (pathP d) :=
    h2.const_mul Complex.I
  have heq : stepZCN d s t K n j Φ U b
      = (fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ))
        + (fun ω => Complex.I * (stepZCN_im d s t K n j Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]; exact h1.add h3

/-- **`stepZCN` has conditional mean zero**: `condExp_linear_eq_zero` applied to the real direction `AbCN` and to `(-I) • AbCN`, recombined via
`condExp_add`/`condExp_smul`. -/
private theorem StepDecompN_condExp_stepZCN_eq_zero (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re d s t K n j Φ U b) (pathP d))
    (hIntIm : Integrable (stepZCN_im d s t K n j Φ U b) (pathP d)) :
    (pathP d)[stepZCN d s t K n j Φ U b | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) := by
  have hAmeas := StepDecompN_measurable_AbCN d s t K n j hΦ U b
  have hAmeas' : Measurable[filt d j]
      (fun ω => (-Complex.I) • AbCN d s t K n j Φ U b ω) := hAmeas.const_smul (-Complex.I)
  have hrealRe : (pathP d)[stepZCN_re d s t K n j Φ U b | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j hAmeas Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (gridStep s t K n)
        * linTr n (AbCN d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1)))) (pathP d)
        from hIntRe)
    rwa [Set.indicator_univ] at h
  have hrealIm : (pathP d)[stepZCN_im d s t K n j Φ U b | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K n j hAmeas' Set.univ MeasurableSet.univ
      (show Integrable (fun ω => Real.sqrt (gridStep s t K n)
        * linTr n ((-Complex.I) • AbCN d s t K n j Φ U b ω)
          (Sizes.seqXmat d n (ω (j + 1)))) (pathP d) from hIntIm)
    rwa [Set.indicator_univ] at h
  have hliftRe := ContinuousLinearMap.comp_condExp_comm (μ := pathP d) (m := filt d j)
    hIntRe Complex.ofRealCLM
  have hliftRe' : (fun ω => (((pathP d)[stepZCN_re d s t K n j Φ U b | filt d j] ω : ℝ) : ℂ))
      =ᵐ[pathP d] (pathP d)[fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hliftRe
  have hliftIm := ContinuousLinearMap.comp_condExp_comm (μ := pathP d) (m := filt d j)
    hIntIm Complex.ofRealCLM
  have hliftIm' : (fun ω => (((pathP d)[stepZCN_im d s t K n j Φ U b | filt d j] ω : ℝ) : ℂ))
      =ᵐ[pathP d] (pathP d)[fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hliftIm
  have hReC : (pathP d)[fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ) | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℂ) := by
    refine hliftRe'.symm.trans ?_
    filter_upwards [hrealRe] with ω hω
    simp [hω]
  have hImC : (pathP d)[fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ) | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℂ) := by
    refine hliftIm'.symm.trans ?_
    filter_upwards [hrealIm] with ω hω
    simp [hω]
  have heq : stepZCN d s t K n j Φ U b
      = (fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ))
        + Complex.I • (fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ)) := by
    funext ω; rfl
  rw [heq]
  have hIntImC : Integrable (fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ)) (pathP d) :=
    hIntIm.ofReal
  have hIntReC : Integrable (fun ω => (stepZCN_re d s t K n j Φ U b ω : ℂ)) (pathP d) :=
    hIntRe.ofReal
  have hIntSmul :
      Integrable (Complex.I • (fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ))) (pathP d) :=
    hIntImC.smul Complex.I
  have hAddCond := condExp_add hIntReC hIntSmul (filt d j)
  have hSmulCond := condExp_smul (μ := pathP d) Complex.I
    (fun ω => (stepZCN_im d s t K n j Φ U b ω : ℂ)) (filt d j)
  refine hAddCond.trans ?_
  filter_upwards [hReC, hSmulCond, hImC] with ω h1 h2 h3
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp [h3]

end LinearPart

/-! ## 5. The decomposition `ξ = Z + Y` of one grid step -/

section Decomposition

variable (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
  {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}

/-- **The a.e. identity behind `stepDecompCN`**: `ξ` agrees a.e. with
`Z` plus the `U`-weighted Taylor-remainder martingale difference. -/
private theorem StepDecompN_stepXiCN_eq_ae (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re d s t K n j Φ U b) (pathP d))
    (hIntIm : Integrable (stepZCN_im d s t K n j Φ U b) (pathP d)) :
    stepXiCN d s t K n j Φ U b
      =ᵐ[pathP d] fun ω => stepZCN d s t K n j Φ U b ω
        + ((∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω)
          - (pathP d)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω'
              | filt d j] ω) := by
  set h0 : PathΩ d → ℂ := fun ω => ∑ a, U b a * Φ a (pathH d s t K n j ω) with hh0def
  set R : PathΩ d → ℂ :=
    fun ω => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω with hRdef
  set Zc : PathΩ d → ℂ := stepZCN d s t K n j Φ U b with hZcdef
  set g : PathΩ d → ℂ := fun ω => ∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R :=
    funext fun ω => StepDecompN_g_eq_pointwise d s t K n j (Φ := Φ) U b ω
  have hh0meas := StepDecompN_measurable_h0 d s t K n j hΦ U b
  have hh0int := StepDecompN_integrable_h0 d s t K n j hΦ U b
  have hZcint := StepDecompN_integrable_stepZCN d s t K n j U b hIntRe hIntIm
  have hRint := StepDecompN_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have hcondg : (pathP d)[g | filt d j]
      =ᵐ[pathP d] (pathP d)[h0 | filt d j] + (pathP d)[Zc | filt d j]
        + (pathP d)[R | filt d j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt d j)).trans
      ((condExp_add hh0int hZcint (filt d j)).add (EventuallyEq.refl _ _))
  have hh0cond : (pathP d)[h0 | filt d j] =ᵐ[pathP d] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt d).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (pathP d)[Zc | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) :=
    StepDecompN_condExp_stepZCN_eq_zero d s t K n j hΦ U b hIntRe hIntIm
  have hstepXi : stepXiCN d s t K n j Φ U b = fun ω => g ω - (pathP d)[g | filt d j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (pathP d)[g | filt d j] ω = h0 ω + (pathP d)[R | filt d j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`stepYCN` a.e. equals the `U`-weighted Taylor remainder minus its own conditional mean**. -/
private theorem StepDecompN_stepYCN_eq_ae (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re d s t K n j Φ U b) (pathP d))
    (hIntIm : Integrable (stepZCN_im d s t K n j Φ U b) (pathP d)) :
    stepYCN d s t K n j Φ U b
      =ᵐ[pathP d] fun ω => (∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω)
        - (pathP d)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω'
            | filt d j] ω := by
  have hXi := StepDecompN_stepXiCN_eq_ae d s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  filter_upwards [hXi] with ω hω
  change stepXiCN d s t K n j Φ U b ω - stepZCN d s t K n j Φ U b ω = _
  rw [hω]; ring

/-- **The pathwise bound on `Y`, a.e.**:
`‖Y b ω‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖U(b,a)‖)(C₂/2)Δ‖X_{j+1}‖²`. -/
private theorem StepDecompN_stepYCN_norm_le_ae (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι)
    (hIntRe : Integrable (stepZCN_re d s t K n j Φ U b) (pathP d))
    (hIntIm : Integrable (stepZCN_im d s t K n j Φ U b) (pathP d)) :
    ∀ᵐ ω ∂(pathP d), ‖stepYCN d s t K n j Φ U b ω‖
      ≤ (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2
        + (pathP d)[fun ω' => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
            * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω := by
  have hY := StepDecompN_stepYCN_eq_ae d s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  set R : PathΩ d → ℂ :=
    fun ω => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω with hRdef
  set g : PathΩ d → ℝ := fun ω => (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n)
      * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω :=
    fun ω => StepDecompN_norm_Rlabel_sum_le d s t K n j hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (pathP d) := (integrable_normSq_incr d n j).const_mul _
  have hRint : Integrable R (pathP d) :=
    StepDecompN_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have hcondRmono : (pathP d)[fun ω => ‖R ω‖ | filt d j] ≤ᵐ[pathP d] (pathP d)[g | filt d j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(pathP d)[R | filt d j] x‖)
      ≤ᵐ[pathP d] (pathP d)[fun x => ‖R x‖ | filt d j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (pathP d)[R | filt d j] ω‖
      ≤ ‖R ω‖ + ‖(pathP d)[R | filt d j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (pathP d)[g | filt d j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

end Decomposition

/-- **`stepDecompCN`: the complex one-step decomposition of a loop observable** (with the class
`HermTestFun` and the Hermitian-direction bound `hC₂`, as in the real `stepDecomp` of
`RBM2D.Path.StepDecomp`).  (i) `ξ_b = Z_b + Y_b` pointwise; (ii) `AbCN` is
`filt d j`-measurable; (iii) a.e., `‖Y_b‖ ≤ g + E[g | F_j]` with
`g = (Σ_a ‖U(b,a)‖) ((C₂/2) Δ) ‖X_{j+1}‖²`; (iv) `E[Y_b | F_j] = 0`.  No reality hypothesis on
`Φ` or `U`: the imaginary part of the first-order term is `stepZCN_im`. -/
theorem stepDecompCN (d : Sizes) : StepDecompCN_Stmt d := by
  intro s t K n j ι _ Φ hΦ C₂ hC₂ hΔ U b hIntRe hIntIm
  refine ⟨fun ω => by unfold stepYCN; ring, StepDecompN_measurable_AbCN d s t K n j hΦ U b,
    StepDecompN_stepYCN_norm_le_ae d s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm, ?_⟩
  have hY := StepDecompN_stepYCN_eq_ae d s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  have hRint := StepDecompN_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have hcond : (pathP d)[fun ω => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω
        - (pathP d)[fun ω' => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω'
            | filt d j] ω | filt d j]
      =ᵐ[pathP d] fun _ => (0 : ℂ) := by
    set R : PathΩ d → ℂ :=
      fun ω => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω with hRdef
    have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt d j)) (filt d j)
    have hidem : (pathP d)[(pathP d)[R | filt d j] | filt d j]
        =ᵐ[pathP d] (pathP d)[R | filt d j] :=
      condExp_condExp_of_le (le_refl (filt d j)) ((filt d).le j)
    have hfe : (fun ω => ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω
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
  exact (condExp_congr_ae hY).trans hcond

/-! ## 6. Sub-Gaussianity of `Z`, integrability, and the `L²` bound on `Y` -/

/-- **`stepDecompCN_Z_subG`: the real and imaginary parts of `Z` are conditionally sub-Gaussian**
(cf. the real `stepDecomp_Z_subG` of `RBM2D.Path.StepDecomp`, with
`hasCondSubgaussianMGF_linear` and `linTrVar`): on a `filt d j`-measurable set `E` where
`Δ · linTrVar (AbCN ω) ≤ c` and `Δ · linTrVar ((-I) • AbCN ω) ≤ c`, both `E.indicator stepZCN_re`
and `E.indicator stepZCN_im` are conditionally sub-Gaussian with the same parameter `c`. -/
theorem stepDecompCN_Z_subG (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ) (b : ι)
    (E : Set (PathΩ d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω ∈ E, gridStep s t K n * linTrVar n (AbCN d s t K n j Φ U b ω) ≤ c)
    (hboundIm : ∀ ω ∈ E,
      gridStep s t K n * linTrVar n ((-Complex.I) • AbCN d s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZCN_re d s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP d)
    ∧ HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZCN_im d s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP d) := by
  refine ⟨?_, ?_⟩
  · have h := hasCondSubgaussianMGF_linear (d := d) s t K n j
      (StepDecompN_measurable_AbCN d s t K n j hΦ U b) E hE c hc hboundRe
    simpa only [stepZCN_re] using h
  · have hAmeas' : Measurable[filt d j] (fun ω => (-Complex.I) • AbCN d s t K n j Φ U b ω) :=
      (StepDecompN_measurable_AbCN d s t K n j hΦ U b).const_smul (-Complex.I)
    have h := hasCondSubgaussianMGF_linear (d := d) s t K n j hAmeas' E hE c hc hboundIm
    simpa only [stepZCN_im] using h

/-- **`stepZCN` is integrable, unconditionally**:
`stepZCN = Σ_a U Φ_a(H_{j+1}) - Σ_a U Φ_a(H_j) - Σ_a U R_a` (`StepDecompN_g_eq_pointwise`) with
all three terms integrable. -/
private theorem StepDecompN_integrable_stepZCN_of_hermTestFun (d : Sizes) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN d s t K n j Φ U b) (pathP d) := by
  have hg : Integrable (fun ω : PathΩ d => ∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω))
      (pathP d) :=
    integrable_finsetSum _ fun a _ =>
      (StepDecompN_integrable_phi d s t K n (hΦ a) (j + 1)).const_mul (U b a)
  have h0 := StepDecompN_integrable_h0 d s t K n j hΦ U b
  have hR := StepDecompN_integrable_Rlabel_sum d s t K n j hΦ hC₂ hΔ U b
  have heq : stepZCN d s t K n j Φ U b
      = fun ω => (∑ a, U b a * Φ a (pathH d s t K n (j + 1) ω))
        - (∑ a, U b a * Φ a (pathH d s t K n j ω))
        - ∑ a, U b a * StepDecompN_Rlabel d s t K n j (Φ a) ω := by
    funext ω
    rw [StepDecompN_g_eq_pointwise d s t K n j (Φ := Φ) U b ω]
    ring
  rw [heq]
  exact (hg.sub h0).sub hR

/-- **`stepZCN_re` is integrable, unconditionally**: discharges the hypothesis `hIntRe` of `stepDecompCN`. -/
theorem integrable_stepZCN_re_of_hermTestFun (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN_re d s t K n j Φ U b) (pathP d) := by
  have h := Complex.reCLM.integrable_comp
    (StepDecompN_integrable_stepZCN_of_hermTestFun d s t K n j hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZCN]

/-- **`stepZCN_im` is integrable, unconditionally**: discharges the hypothesis `hIntIm` of `stepDecompCN`. -/
theorem integrable_stepZCN_im_of_hermTestFun (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {ι : Type*} [Fintype ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    Integrable (stepZCN_im d s t K n j Φ U b) (pathP d) := by
  have h := Complex.imCLM.integrable_comp
    (StepDecompN_integrable_stepZCN_of_hermTestFun d s t K n j hΦ hC₂ hΔ U b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [stepZCN]

/-! ## 7. Identification with `martIncN`, `ZvecN`, `YvecN`, `Ugen`

The loop family `loopFamN` at the spectral time `u_{j+1}` is in the Hermitian test class for
`j + 1 ≤ K n`, `|E n| < 2`, `0 ≤ s n ≤ t n`, `t n < 1`: the argument of `hΦ_of_hermTestFunLoopN`,
stated per `n`, with the theorem `hermTestFunLoopN` in place of the hypothesis
`HermTestFunLoopN`, so no test-class hypothesis appears below. -/

section Identification

/-- The loop family is in the Hermitian test class at the spectral time `u_{j+1}` (the per-`n`
form of `hΦ_of_hermTestFunLoopN`, with the theorem `hermTestFunLoopN`).  For
`k = 0` the loop is empty and the observable is the constant `tr 1`. -/
private theorem StepDecompN_loopFam_hermTestFun (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n)) :
    HermTestFun d n (loopFamN d E s t K n j σ b) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hconst : loopFamN d E s t K n j σ b = fun _ => Matrix.trace
        (1 : Matrix (BlockIndex (d.L n) (d.W n)) (BlockIndex (d.L n) (d.W n)) ℂ) := by
      funext M
      simp [loopFamN, gloop, loopOf, gloopProd]
    rw [hconst]
    exact ⟨fun M _ => contDiffAt_const, _, fun M _ => le_rfl⟩
  · have : NeZero k := ⟨by omega⟩
    have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg hs0 hst (j + 1)
    have hu1 : gridTime s t K n (j + 1) < 1 :=
      (GoodEvent_gridTime_le (K := K) hst hj).trans_lt ht1
    exact (hermTestFunLoopN d k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ b).1

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M` (cf. `StepDecomp_fderiv_im_eq_zero`, first half). -/
private theorem StepDecompN_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ} (X : Matrix ι ι ℂ) (hd : DifferentiableAt ℝ Ψ M) :
    HasDerivAt (fun y : ℝ => Ψ (M + (y : ℂ) • X)) (fderiv ℝ Ψ M X) 0 := by
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (StepDecompN_hasDerivAt_add_smul M X 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  simpa only [Complex.coe_smul] using hp0

/-- `loopDerivN` is `fderiv ℝ` of the loop family, where the loop family is differentiable. -/
private theorem StepDecompN_loopDerivN_eq_fderiv (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n))
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (hd : DifferentiableAt ℝ (loopFamN d E s t K n j σ b) M) :
    loopDerivN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) M X σ b
      = fderiv ℝ (loopFamN d E s t K n j σ b) M X :=
  (StepDecompN_hasDerivAt_dir X hd).deriv

/-- The identity kernel collapses a sum over labels. -/
private theorem StepDecompN_sum_delta {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ)
    (a : ι) : ∑ c, (if a = c then (1 : ℂ) else 0) * f c = f a := by
  simp [ite_mul]

/-- **`stepZCN` is linear in the complex kernel `U`**, pointwise in `ω`: `Z^U_b = Σ_a U(b,a) Z^δ_a`. -/
private theorem StepDecompN_stepZCN_eq_sum_delta (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (U : ι → ι → ℂ) (b : ι) (ω : PathΩ d) :
    stepZCN d s t K n j Φ U b ω
      = ∑ a, U b a * stepZCN d s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  rw [← StepDecompN_sum_fderiv_eq_stepZCN d s t K n j (Φ := Φ) U b ω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← StepDecompN_sum_fderiv_eq_stepZCN d s t K n j (Φ := Φ)
    (fun a a' => if a = a' then 1 else 0) a ω]
  rw [StepDecompN_sum_delta (fun c => fderiv ℝ (Φ c) (pathH d s t K n j ω)
    (Sizes.seqXmat d n (ω (j + 1)))) a]
  ring

/-- `stepZCN` for the loop family and a general kernel is `Σ_a U(b,a) ZvecN_a`. -/
private theorem StepDecompN_stepZCN_eq_sum_zvecN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hj : j + 1 ≤ K n) {k : ℕ} (σ : Fin k → Bool)
    (U : (Fin k → Z2 (d.L n)) → (Fin k → Z2 (d.L n)) → ℂ) (b : Fin k → Z2 (d.L n))
    (ω : PathΩ d) :
    stepZCN d s t K n j (loopFamN d E s t K n j σ) U b ω
      = ∑ a, U b a * ZvecN d E s t K n j σ ω a := by
  rw [← StepDecompN_sum_fderiv_eq_stepZCN d s t K n j (Φ := loopFamN d E s t K n j σ) U b ω,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : DifferentiableAt ℝ (loopFamN d E s t K n j σ a) (pathH d s t K n j ω) :=
    ((StepDecompN_loopFam_hermTestFun d E s t K n j hE hs0 hst ht1 hj σ a).contDiffAt _
      (pathH_isHermitian d s t K n j ω)).differentiableAt (by norm_num)
  have h := StepDecompN_loopDerivN_eq_fderiv d E s t K n j σ a
    (M := pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1))) hd
  unfold ZvecN
  rw [h]
  ring

/-- **`ZvecN = stepZCN`** (identity kernel): the first-chaos
part `√Δ · ∂_{X_{j+1}} 𝓛_{u_{j+1},σ,b}(H_j)` is `stepZCN` of the loop family with the
identity kernel, at every sample point.  The derivative `loopDerivN` is `fderiv ℝ` because the loop
observable is differentiable at the Hermitian `H_j` (`HermTestFun.contDiffAt`), and `fderiv` along a
Hermitian direction is `trace (gradMat · X)` (`fderiv_eq_trace_gradMat`). -/
theorem ZvecN_eq_stepZCN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n)) (ω : PathΩ d) :
    ZvecN d E s t K n j σ ω b =
      stepZCN d s t K n j (loopFamN d E s t K n j σ) (fun a a' => if a = a' then 1 else 0) b ω := by
  rw [StepDecompN_stepZCN_eq_sum_zvecN d E s t K n j hE hs0 hst ht1 hj σ _ b ω,
    StepDecompN_sum_delta]

/-- **`stepXiCN` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`:
`ξ^U_b = Σ_a U(b,a) ξ^δ_a`. -/
private theorem StepDecompN_stepXiCN_eq_sum_delta_ae (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ) :
    ∀ᵐ ω ∂(pathP d), ∀ b : ι,
      stepXiCN d s t K n j Φ U b ω
        = ∑ a, U b a * stepXiCN d s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  have hfun : ∀ a : ι,
      (fun ω' => ∑ c, (if a = c then (1 : ℂ) else 0) * Φ c (pathH d s t K n (j + 1) ω'))
        = fun ω' => Φ a (pathH d s t K n (j + 1) ω') := by
    intro a; funext ω'
    exact StepDecompN_sum_delta (fun c => Φ c (pathH d s t K n (j + 1) ω')) a
  have hδ : ∀ a (ω : PathΩ d),
      stepXiCN d s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω
        = Φ a (pathH d s t K n (j + 1) ω)
          - (pathP d)[fun ω' => Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω := by
    intro a ω
    have h1 := congrFun (hfun a) ω
    unfold stepXiCN
    rw [h1, hfun a]
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset ι),
      Integrable (fun ω => U b a * Φ a (pathH d s t K n (j + 1) ω)) (pathP d) :=
    fun a _ => (StepDecompN_integrable_phi d s t K n (hΦ a) (j + 1)).const_mul (U b a)
  have hcondsum := condExp_finsetSum hint_a (filt d j)
  have hsmul_ae : ∀ᵐ ω ∂(pathP d), ∀ a : ι,
      (pathP d)[fun ω' => U b a * Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω
        = U b a * (pathP d)[fun ω' => Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω :=
    ae_all_iff.mpr fun a =>
      condExp_smul (U b a) (fun ω' => Φ a (pathH d s t K n (j + 1) ω')) (filt d j)
  have hsum_fn : (∑ a : ι, fun ω' => U b a * Φ a (pathH d s t K n (j + 1) ω'))
      = (fun ω' => ∑ a : ι, U b a * Φ a (pathH d s t K n (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [hδ]
  unfold stepXiCN
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepYCN` is linear in the complex kernel `U`**, a.e., simultaneously for all labels `b`. -/
private theorem StepDecompN_stepYCN_eq_sum_delta_ae (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a)) (U : ι → ι → ℂ) :
    ∀ᵐ ω ∂(pathP d), ∀ b : ι,
      stepYCN d s t K n j Φ U b ω
        = ∑ a, U b a * stepYCN d s t K n j Φ (fun a a' => if a = a' then 1 else 0) a ω := by
  filter_upwards [StepDecompN_stepXiCN_eq_sum_delta_ae d s t K n j hΦ U] with ω hω b
  unfold stepYCN
  rw [hω b, StepDecompN_stepZCN_eq_sum_delta d s t K n j (Φ := Φ) U b ω]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`martIncN = stepXiCN`** (identity kernel): a.e., simultaneously
for all labels `b`, the martingale increment `ξ_{j+1} = A_{j+1} - E[A_{j+1} | F_j]` is
`stepXiCN` of the loop family with the identity kernel.  The deterministic `𝒦` part of `AvecN`
(`A = 𝓛 - 𝒦`) cancels: `E[𝓛 - 𝒦 | F_j] = E[𝓛 | F_j] - 𝒦`, the loop observable being bounded and
measurable along the Hermitian walk (`HermTestFun`). -/
theorem martIncN_eq_stepXiCN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Fin k → Z2 (d.L n),
      martIncN d E s t K n j σ ω b =
        stepXiCN d s t K n j (loopFamN d E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
  have hΦ := StepDecompN_loopFam_hermTestFun d E s t K n j hE hs0 hst ht1 hj σ
  refine ae_all_iff.mpr fun b => ?_
  have hint : Integrable (fun ω' : PathΩ d => loopFamN d E s t K n j σ b (pathH d s t K n (j + 1) ω'))
      (pathP d) := StepDecompN_integrable_phi d s t K n (hΦ b) (j + 1)
  have hsub := condExp_sub hint
    (integrable_const (KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ b)))
    (filt d j)
  have hconst := condExp_const (μ := pathP d) ((filt d).le j)
    (KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ b))
  have hfun : (fun ω' : PathΩ d => ∑ a, (if b = a then (1 : ℂ) else 0) *
        loopFamN d E s t K n j σ a (pathH d s t K n (j + 1) ω'))
      = fun ω' => loopFamN d E s t K n j σ b (pathH d s t K n (j + 1) ω') := by
    funext ω'
    exact StepDecompN_sum_delta (fun c => loopFamN d E s t K n j σ c (pathH d s t K n (j + 1) ω')) b
  have hAvec : (fun ω' : PathΩ d => AvecN d E s t K n (j + 1) σ ω' b)
      = (fun ω' : PathΩ d => loopFamN d E s t K n j σ b (pathH d s t K n (j + 1) ω'))
        - fun _ => KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ b) := rfl
  filter_upwards [hsub] with ω hω
  unfold martIncN stepXiCN
  rw [hAvec, hω, hfun]
  simp only [Pi.sub_apply, hconst]
  have hb : (∑ a, (if b = a then (1 : ℂ) else 0) *
      loopFamN d E s t K n j σ a (pathH d s t K n (j + 1) ω))
      = loopFamN d E s t K n j σ b (pathH d s t K n (j + 1) ω) :=
    StepDecompN_sum_delta (fun c => loopFamN d E s t K n j σ c (pathH d s t K n (j + 1) ω)) b
  rw [hb]
  change (loopFamN d E s t K n j σ b (pathH d s t K n (j + 1) ω) - _) - _ = _
  ring

/-- **`YvecN = stepYCN`** (identity kernel): a.e., simultaneously for all labels `b`, the remainder
`martIncN - ZvecN` is `stepYCN` of the loop family with the identity kernel. -/
theorem YvecN_eq_stepYCN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Fin k → Z2 (d.L n),
      YvecN d E s t K n j σ ω b =
        stepYCN d s t K n j (loopFamN d E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
  filter_upwards [martIncN_eq_stepXiCN d E s t K n j hE hs0 hst ht1 hj σ] with ω hω b
  unfold YvecN stepYCN
  rw [hω b, ZvecN_eq_stepZCN d E s t K n j hE hs0 hst ht1 hj σ b ω]

/-- **`Ugen ∘ YvecN = stepYCN` with the propagator kernel**: a.e., for every label `a`, `(𝒰_{u_{j+1},u_m,σ} Y)_a` is `stepYCN` of the loop family with
the kernel of `Ugen`. -/
theorem Ugen_stepYCN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (m : ℕ) :
    ∀ᵐ ω ∂(pathP d), ∀ a : Fin k → Z2 (d.L n),
      Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (YvecN d E s t K n j σ ω) a =
        stepYCN d s t K n j (loopFamN d E s t K n j σ)
          (fun a b => ∏ i : Fin k, ukerMat (d.L n)
            (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
            (gridTime s t K n m) (a i) (b i)) a ω := by
  have hΦ := StepDecompN_loopFam_hermTestFun d E s t K n j hE hs0 hst ht1 hj σ
  filter_upwards [YvecN_eq_stepYCN d E s t K n j hE hs0 hst ht1 hj σ,
    StepDecompN_stepYCN_eq_sum_delta_ae d s t K n j hΦ
      (fun a b => ∏ i : Fin k, ukerMat (d.L n)
        (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
        (gridTime s t K n m) (a i) (b i))] with ω h1 h2 a
  rw [h2 a]
  unfold Ugen
  exact Finset.sum_congr rfl fun b _ => by rw [h1 b]

end Identification

end RBM.Ind

end
