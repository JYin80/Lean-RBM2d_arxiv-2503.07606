/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.StepDecompN
import RBM2D.Induction.GridGoodN
import RBM2D.Induction.LoopC2N
import RBM2D.Path.QVForm
import RBM2D.Gauss.Stein
import Mathlib.Probability.ConditionalExpectation

/-!
# The Azuma proxies and the `Y` moments of the grid walk (`d = 2`)

Proofs of the statement `AzumaSubGN` of `RBM2D.Induction.GridGoodN` and of the uniform `Y`
moments `YMomentsUnifN` (defined below) (namespace `RBM.Ind`, `variable (d : Sizes)`), with no
added hypothesis:

* `azumaSubGN d s t K : AzumaSubGN d s t K`: for a finite family
  `Φ` in the Hermitian test class, weights `κ`, a stopping family `{j < τ} ∈ F_j` on which the
  grid state lies in `G j`, and `Q` majorising `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the
  Hermitian matrices of `G j`, the stopped combination `1_{j<τ} Σ_b κ_b Z_b` of the first-chaos
  parts is conditionally sub-Gaussian with proxy `Q` (real and imaginary parts).
* `yMomentsUnifN d κ τ' E s t : YMomentsUnifN d κ τ' E s t`: the
  moment inputs of the assembled bound for `YvecN`, with `v_j = Δ² P`, `w_j = Δ⁴ P²`,
  `P ≤ N^{C_P}`, where `C_P` is chosen before the grid `K`.  **Explicit witness**:
  `C_P = 11 + (4 k + 4) · max 0 (1 - τ')`, and for `N = size n` with
  `N ≥ max 1 (2000 (2^k k (k + 1) c₀^{-(k+2)})²)` and the range condition,
  `P = 2000 (S C₂)² N⁸`, where `c₀ = √(κ (4 - κ)) / 2`, `Θ = N^{max 0 (1-τ')}`, `S = (2 Θ)^k`,
  `C₂ = k (k + 1) N (Θ / c₀)^{k+2}`.
* the eighth moment of one increment (`AzumaProxyN_integrable_normPow8_incr`,
  `AzumaProxyN_integral_normPow8_incr_le`).

## Proofs

`azumaSubGN`.  For a nonempty label set, `Σ_b κ_b Z_b` is `stepZCN` of the family `Φ`
with the kernel `(b, a) ↦ κ_a`.  `linTr (Σ_a κ_a gradMat Φ_a) X_c = Re Σ_a κ_a ∂_c Φ_a`, and
`linTr` at the `(-I)`-multiple reads the imaginary part, so `linTrVar` of both directions is at
most `Σ_c gvar_c ‖Σ_a κ_a ∂_c Φ_a‖²` (`AzumaProxyN_linTrVar_le`).  Then `Δ · linTrVar ≤ Q` follows
from the majorant hypothesis (for `Δ < 0` from `linTrVar ≥ 0`), and `stepDecompCN_Z_subG`
(`hasCondSubgaussianMGF_linear`) gives the two sub-Gaussian bounds; for an empty label set the
increment is `0`.

`yMomentsUnifN`.  `YvecN = stepYCN` a.e. (`Ugen_stepYCN`); `stepDecompCN` gives `E[Y | F_j] = 0` and
`‖Y‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖U(b,a)‖) (C₂/2) Δ ‖X_{j+1}‖²`; the independence of `X_{j+1}`
and `F_j` (`condExp_indep_eq`) turns this into `‖Y‖ ≤ ρ (‖X_{j+1}‖² + E ‖X‖²)` a.e.  Then
`E[W² | F_j] ≤ 2 ρ² (E ‖X‖⁴ + m²)` and `E W⁴ ≤ 8 ρ⁴ (E ‖X‖⁸ + m⁴)` for the real and imaginary
parts `W` of the stopped increment (`AzumaProxyN_moments_of_dom`), with `E ‖X‖² ≤ 16 N⁴`,
`E ‖X‖⁴ ≤ 768 N⁸` and `E ‖X‖⁸ ≤ 6881280 N¹⁶`.  The constants: `C₂ = k (k + 1) N
η^{-(k+2)}` (`hermTestFunLoopN`), `η_u^{-1} ≤ N^{1-τ'} / c₀` (from `RangeCond`, `u ≤ t`
and `|E| ≤ 2 - κ`), and the row sums `Σ_b ‖Π_i ukerMat‖ ≤ (1 + (1 - w)⁻¹)^k ≤ (2 Θ)^k`.

## The `d = 2` setting

The dominating function is squared with `(x + y)² ≤ 2 (x² + y²)`, `(x + y)⁴ ≤ 8 (x⁴ + y⁴)`, so only
`E ‖X‖⁴`, `E ‖X‖⁸` enter, and the conditional expectation of a function of the increment is
`condExp_indep_eq` for `indep_incr`.  The `TestFun` global `C²` bound is
the class `HermTestFun` and the Hermitian-direction bound `hC₂` of `stepDecompCN` (the segment
`[H_j, H_{j+1}]` is Hermitian); `Coord L W` has `2 N²` elements, `N = (W L)²` (the moments are
polynomials in `N`); the loop arguments are `Fin k → Z2 (d.L n)`.  The kernel row-sum
helpers, the Gaussian moment helpers and the norm bound `‖X‖ ≤ 2 Σ_c |ω_c|` are private lemmas
prefixed `AzumaProxyN_`.  The argument parallels the one-dimensional formalization.

Paper: arXiv:2503.07606, Section 5: the martingale term (`alu9_STime`) and the SDE `LK_SDE`.  The
Lean formulation differs from the paper in the `Z + Y` split (Azuma for `Z`, the second-order
remainder `Y`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. `azumaSubGN` -/

section Azuma

variable (d : Sizes)

/-- The directional derivative along the real line `y ↦ M + y X` at `0` is `fderiv ℝ Ψ M X`, for
`Ψ` differentiable at `M`. -/
private theorem AzumaProxyN_hasDerivAt_dir {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ} (X : Matrix ι ι ℂ) (hd : DifferentiableAt ℝ Ψ M) :
    HasDerivAt (fun y : ℝ => Ψ (M + (y : ℂ) • X)) (fderiv ℝ Ψ M X) 0 := by
  have hadd : HasDerivAt (fun t' : ℝ => M + t' • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add M
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 hadd
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  simpa only [Complex.coe_smul] using hp0

/-- `dirDerivN` is `fderiv ℝ` where the observable is differentiable. -/
private theorem AzumaProxyN_dirDerivN_eq {L W : ℕ} [NeZero L] [NeZero W]
    {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (X : Matrix (Idx L W) (Idx L W) ℂ) (hd : DifferentiableAt ℝ Φ M) :
    dirDerivN Φ M X = fderiv ℝ Φ M X :=
  (AzumaProxyN_hasDerivAt_dir X hd).deriv

/-- `linTr` at the direction `(-I) • A` reads the imaginary part of `trace (A * X)`. -/
private theorem AzumaProxyN_linTr_neg_I_smul (n : ℕ)
    (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n ((-Complex.I) • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem AzumaProxyN_seqXmat_single (n : ℕ) (c : Coord (d.L n) (d.W n)) :
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

/-- `linTrVar` as the sum over the coordinates of one size. -/
private theorem AzumaProxyN_linTrVar_eq (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTrVar n A = ∑ c : Coord (d.L n) (d.W n), (gvar (d.L n) (d.W n) c : ℝ) *
      (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2 := by
  classical
  rw [← vB_self (d := d)]
  unfold vB coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Function.Embedding.sigmaMk_apply, AzumaProxyN_seqXmat_single]
  change (gvar (d.L n) (d.W n) c : ℝ) * _ * _ = _
  ring

private theorem AzumaProxyN_sq_re_le (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

private theorem AzumaProxyN_sq_im_le (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2

/-- **The variance identity**: for `A` with `tr (A X_c) = D_c`, `linTrVar A` and
`linTrVar ((-I) • A)` are `Σ_c gvar_c (Re D_c)²` and `Σ_c gvar_c (Im D_c)²`, hence at most
`Σ_c gvar_c ‖D_c‖²`. -/
private theorem AzumaProxyN_linTrVar_le (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (D : Coord (d.L n) (d.W n) → ℂ)
    (hD : ∀ c, Matrix.trace (A * coordinateMatrix (d.L n) (d.W n) c) = D c) :
    linTrVar n A ≤ ∑ c : Coord (d.L n) (d.W n), (gvar (d.L n) (d.W n) c : ℝ) * ‖D c‖ ^ 2 ∧
    linTrVar n ((-Complex.I) • A) ≤
      ∑ c : Coord (d.L n) (d.W n), (gvar (d.L n) (d.W n) c : ℝ) * ‖D c‖ ^ 2 := by
  constructor
  · rw [AzumaProxyN_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (gvar (d.L n) (d.W n) c).2
    have : linTr n A (coordinateMatrix (d.L n) (d.W n) c) = (D c).re := by
      rw [← hD c]; rfl
    rw [this]
    exact AzumaProxyN_sq_re_le _
  · rw [AzumaProxyN_linTrVar_eq]
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (gvar (d.L n) (d.W n) c).2
    rw [AzumaProxyN_linTr_neg_I_smul, hD c]
    exact AzumaProxyN_sq_im_le _

/-- `tr (A X)` for `A = Σ_a κ_a gradMat Φ_a M` at a Hermitian direction `X` is the `κ`-weighted sum
of the directional derivatives. -/
private theorem AzumaProxyN_trace_eq {ι : Type*} [Fintype ι] {n : ℕ}
    {Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ b, HermTestFun d n (Φ b)) (κ : ι → ℂ)
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian)
    {X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hX : X.IsHermitian) :
    Matrix.trace ((∑ a, κ a • gradMat (Φ a) M) * X) = ∑ a, κ a * dirDerivN (Φ a) M X := by
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : DifferentiableAt ℝ (Φ a) M := ((hΦ a).contDiffAt M hM).differentiableAt (by norm_num)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← fderiv_eq_trace_gradMat M hX,
    AzumaProxyN_dirDerivN_eq X hd]


/-- The zero function is conditionally sub-Gaussian with every proxy. -/
private theorem AzumaProxyN_subG_zero (j : ℕ) (c : ℝ≥0) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j) (fun _ => (0 : ℝ)) c (pathP d) := by
  unfold HasCondSubgaussianMGF
  refine ⟨by simp, ?_⟩
  filter_upwards with ω t
  simp only [mgf, mul_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  have h1 : (condExpKernel (pathP d) (filt d j) ω).real Set.univ = 1 := by simp
  rw [h1]
  exact Real.one_le_exp (by positivity)

/-- **`azumaSubGN`** (the statement `AzumaSubGN`):
for a finite family `Φ` in the Hermitian test class, weights `κ`, a stopping family `{j < τ} ∈ F_j`
on which the grid state lies in `G j`, and `Q` majorising `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on
the Hermitian matrices of `G j`, the stopped combination `1_{j<τ} Σ_b κ_b Z_b` of the first-chaos
parts is conditionally sub-Gaussian with proxy `Q` (real and imaginary parts).  Proof: for a
nonempty label set `Σ_b κ_b Z_b = stepZCN` of the family `Φ` with the kernel `(b, a) ↦ κ_a`
(`stepZCN`), the variance identity `linTrVar (AbCN) ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²` (and the
same for `(-I) • AbCN`) and `stepDecompCN_Z_subG` (`hasCondSubgaussianMGF_linear`); for an
empty label set the increment is `0`. -/
theorem azumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN d s t K := by
  intro n ι _ Φ hΦ κ τ G hτ hG j Q hQ
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨b₀⟩⟩
  · -- empty label set: the combination is `0`
    have hz : ∀ ω : PathΩ d, ({ω' | j < τ ω'}.indicator
        (fun ω => ∑ b, κ b * ZfamN d s t K n j Φ ω b) ω) = 0 := by
      intro ω
      simp [Finset.univ_eq_empty]
    unfold SubGaussFormN
    simp only [hz, Complex.zero_re, Complex.zero_im]
    exact ⟨AzumaProxyN_subG_zero d j Q, AzumaProxyN_subG_zero d j Q⟩
  · set U : ι → ι → ℂ := fun _ a => κ a with hU
    -- the combination is `stepZCN`
    have hFeq : ∀ ω : PathΩ d,
        ∑ b, κ b * ZfamN d s t K n j Φ ω b = stepZCN d s t K n j Φ U b₀ ω := by
      intro ω
      have hH := pathH_isHermitian d s t K n j ω
      have hX := Sizes.seqXmat_isHermitian d n (ω (j + 1))
      have htr := AzumaProxyN_trace_eq d hΦ κ hH hX
      have hA : AbCN d s t K n j Φ U b₀ ω = ∑ a, κ a • gradMat (Φ a) (pathH d s t K n j ω) := rfl
      set w := Matrix.trace (AbCN d s t K n j Φ U b₀ ω * Sizes.seqXmat d n (ω (j + 1))) with hw
      have hre : linTr n (AbCN d s t K n j Φ U b₀ ω) (Sizes.seqXmat d n (ω (j + 1))) = w.re := rfl
      have him : linTr n ((-Complex.I) • AbCN d s t K n j Φ U b₀ ω)
          (Sizes.seqXmat d n (ω (j + 1))) = w.im := AzumaProxyN_linTr_neg_I_smul d n _ _
      have hw' : w = ∑ a, κ a * dirDerivN (Φ a) (pathH d s t K n j ω)
          (Sizes.seqXmat d n (ω (j + 1))) := by rw [hw, hA]; exact htr
      have hsum : ∑ b, κ b * ZfamN d s t K n j Φ ω b = (Real.sqrt (gridStep s t K n) : ℂ) * w := by
        rw [hw', Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold ZfamN; ring
      rw [hsum]
      unfold stepZCN stepZCN_re stepZCN_im
      rw [hre, him]
      have hreim := Complex.re_add_im w
      push_cast
      linear_combination (Real.sqrt (gridStep s t K n) : ℂ) * hreim.symm
    -- the variance bound on `{j < τ}`
    have hbound : ∀ ω ∈ {ω : PathΩ d | j < τ ω},
        (gridStep s t K n * linTrVar n (AbCN d s t K n j Φ U b₀ ω) ≤ (Q : ℝ)) ∧
        (gridStep s t K n * linTrVar n ((-Complex.I) • AbCN d s t K n j Φ U b₀ ω) ≤ (Q : ℝ)) := by
      intro ω hω
      have hmem : pathH d s t K n j ω ∈ G j := hG ω j hω
      have hH := pathH_isHermitian d s t K n j ω
      have hq := hQ _ hmem hH
      set D : Coord (d.L n) (d.W n) → ℂ := fun c => ∑ b, κ b * dirDerivN (Φ b)
        (pathH d s t K n j ω) (coordinateMatrix (d.L n) (d.W n) c) with hD
      have hDeq : ∀ c, Matrix.trace (AbCN d s t K n j Φ U b₀ ω *
          coordinateMatrix (d.L n) (d.W n) c) = D c :=
        fun c => AzumaProxyN_trace_eq d hΦ κ hH (coordinateMatrix_isHermitian _ _ c)
      obtain ⟨h1, h2⟩ := AzumaProxyN_linTrVar_le d n _ D hDeq
      have hv1 := linTrVar_nonneg n (AbCN d s t K n j Φ U b₀ ω)
      have hv2 := linTrVar_nonneg n ((-Complex.I) • AbCN d s t K n j Φ U b₀ ω)
      rcases le_or_gt 0 (gridStep s t K n) with hΔ | hΔ
      · exact ⟨(mul_le_mul_of_nonneg_left h1 hΔ).trans hq,
          (mul_le_mul_of_nonneg_left h2 hΔ).trans hq⟩
      · exact ⟨(mul_nonpos_of_nonpos_of_nonneg hΔ.le hv1).trans Q.2,
          (mul_nonpos_of_nonpos_of_nonneg hΔ.le hv2).trans Q.2⟩
    have hZ := stepDecompCN_Z_subG d s t K n j hΦ U b₀ {ω | j < τ ω} (hτ j) (Q : ℝ) Q.2
      (fun ω hω => (hbound ω hω).1) (fun ω hω => (hbound ω hω).2)
    have hFfun : (fun ω : PathΩ d => ∑ b, κ b * ZfamN d s t K n j Φ ω b)
        = stepZCN d s t K n j Φ U b₀ := funext hFeq
    have hre : (fun ω : PathΩ d => ({ω' | j < τ ω'}.indicator
          (stepZCN d s t K n j Φ U b₀) ω).re)
        = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_re d s t K n j Φ U b₀ ω') ω := by
      funext ω
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · simp only [Set.indicator_of_mem h]
        simp [stepZCN]
      · simp [Set.indicator_of_notMem h]
    have him : (fun ω : PathΩ d => ({ω' | j < τ ω'}.indicator
          (stepZCN d s t K n j Φ U b₀) ω).im)
        = fun ω => {ω' | j < τ ω'}.indicator (fun ω' => stepZCN_im d s t K n j Φ U b₀ ω') ω := by
      funext ω
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · simp only [Set.indicator_of_mem h]
        simp [stepZCN]
      · simp [Set.indicator_of_notMem h]
    unfold SubGaussFormN
    rw [hFfun]
    exact ⟨by rw [hre]; exact hZ.1, by rw [him]; exact hZ.2⟩

end Azuma

/-! ## 2. Gaussian moments up to order 8 -/

section GaussMoments

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem AzumaProxyN_integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
private theorem AzumaProxyN_integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- **The Stein recursion for the even moments**: `E[X^{2p+2}] = (2p+1) v E[X^{2p}]`. -/
private theorem AzumaProxyN_integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := AzumaProxyN_integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((AzumaProxyN_integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    AzumaProxyN_integrable_mul_gaussianPDFReal hv
      ((AzumaProxyN_integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    AzumaProxyN_integrable_mul_gaussianPDFReal hv
      (AzumaProxyN_integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- `E x⁸ = 105 v⁴` for `x ~ N(0, v)`, kept as the bound `≤ 105` for `v ≤ 1`. -/
private theorem AzumaProxyN_integral_pow8_gaussian_le {v : ℝ≥0} (hv1 : (v : ℝ) ≤ 1) :
    ∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 v) ≤ 105 := by
  have h0 : ∫ x : ℝ, x ^ (2 * 0) ∂(gaussianReal 0 v) = 1 := by simp
  have h1 := AzumaProxyN_integral_pow_gaussianReal_succ v 0
  have h2 := AzumaProxyN_integral_pow_gaussianReal_succ v 1
  have h3 := AzumaProxyN_integral_pow_gaussianReal_succ v 2
  have h4 := AzumaProxyN_integral_pow_gaussianReal_succ v 3
  norm_num at h1 h2 h3 h4
  rw [h4, h3, h2, h1]
  have hv0 : (0 : ℝ) ≤ v := v.2
  have : (v : ℝ) * (v : ℝ) ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hv0 hv0, pow_nonneg hv0 3, pow_nonneg hv0 4, pow_le_one₀ hv0 hv1 (n := 4)]


end GaussMoments

section MomentsBound8

private theorem AzumaProxyN_norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι)
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
private theorem AzumaProxyN_norm_le_sum_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => AzumaProxyN_norm_single_le i j _))

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem AzumaProxyN_norm_Xentry_le (ω : Ω L W) (i j : Idx L W) :
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

private theorem AzumaProxyN_sum_coord (f : Coord L W → ℝ) :
    ∑ c : Coord L W, f c = ∑ i : Idx L W, ∑ j : Idx L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|` (RBM2D `OneStep_norm_blockMat_Xmat_le`, here in `Idx` coordinates). -/
private theorem AzumaProxyN_norm_Xmat_le (ω : Ω L W) :
    ‖Xmat L W ω‖ ≤ 2 * ∑ c : Coord L W, |ω c| := by
  refine (AzumaProxyN_norm_le_sum_entries _).trans ?_
  rw [AzumaProxyN_sum_coord]
  have hswap : ∑ i : Idx L W, ∑ j : Idx L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx L W, ∑ j : Idx L W, ‖Xmat L W ω i j‖
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => AzumaProxyN_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

private theorem AzumaProxyN_gvar_le_one (c : Coord L W) : (gvar L W c : ℝ) ≤ 1 := by
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

private theorem AzumaProxyN_card_Coord :
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

/-! #### The eighth moment of `‖X‖` -/

private theorem AzumaProxyN_integrable_pow8_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => (ω c) ^ 8) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 8) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact AzumaProxyN_integrable_pow_gaussianReal _ 8
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem AzumaProxyN_integral_pow8_coord_le (c : Coord L W) :
    ∫ ω : Ω L W, (ω c) ^ 8 ∂(P L W) ≤ 105 := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 8) ((P L W).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  exact AzumaProxyN_integral_pow8_gaussian_le (AzumaProxyN_gvar_le_one c)

private theorem AzumaProxyN_norm_pow8_le (ω : Ω L W) :
    ‖Xmat L W ω‖ ^ 8 ≤ 256 * (Fintype.card (Coord L W) : ℝ) ^ 7 * ∑ c : Coord L W, (ω c) ^ 8 := by
  have h := AzumaProxyN_norm_Xmat_le ω
  have h0 := norm_nonneg (Xmat L W ω)
  have hS0 : ∀ c ∈ (Finset.univ : Finset (Coord L W)), 0 ≤ |ω c| := fun c _ => abs_nonneg _
  have hpm := pow_sum_le_card_mul_sum_pow hS0 7
  simp only [Finset.card_univ] at hpm
  have habs : ∀ c : Coord L W, |ω c| ^ (7 + 1) = (ω c) ^ 8 := fun c => Even.pow_abs (by decide) _
  simp only [habs] at hpm
  calc ‖Xmat L W ω‖ ^ 8 ≤ (2 * ∑ c : Coord L W, |ω c|) ^ 8 := pow_le_pow_left₀ h0 h 8
    _ = 256 * (∑ c : Coord L W, |ω c|) ^ 8 := by ring
    _ ≤ 256 * ((Fintype.card (Coord L W) : ℝ) ^ 7 * ∑ c : Coord L W, (ω c) ^ 8) := by
        gcongr
    _ = _ := by ring

private theorem AzumaProxyN_integrable_normPow8 :
    Integrable (fun ω : Ω L W => ‖Xmat L W ω‖ ^ 8) (P L W) := by
  have hint : Integrable (fun ω : Ω L W =>
      256 * (Fintype.card (Coord L W) : ℝ) ^ 7 * ∑ c : Coord L W, (ω c) ^ 8) (P L W) :=
    (integrable_finsetSum _ fun c _ => AzumaProxyN_integrable_pow8_coord c).const_mul _
  refine hint.mono' ((continuous_norm.comp (continuous_Xmat L W)).pow 8).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact AzumaProxyN_norm_pow8_le ω

private theorem AzumaProxyN_integral_normPow8_le :
    ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 8 ∂(P L W) ≤ 6881280 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 16 := by
  have hcard := AzumaProxyN_card_Coord (L := L) (W := W)
  calc ∫ ω : Ω L W, ‖Xmat L W ω‖ ^ 8 ∂(P L W)
      ≤ ∫ ω : Ω L W, 256 * (Fintype.card (Coord L W) : ℝ) ^ 7 * ∑ c : Coord L W, (ω c) ^ 8
          ∂(P L W) :=
        integral_mono AzumaProxyN_integrable_normPow8
          ((integrable_finsetSum _ fun c _ => AzumaProxyN_integrable_pow8_coord c).const_mul _)
          fun ω => AzumaProxyN_norm_pow8_le ω
    _ = 256 * (Fintype.card (Coord L W) : ℝ) ^ 7
          * ∑ c : Coord L W, ∫ ω : Ω L W, (ω c) ^ 8 ∂(P L W) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => AzumaProxyN_integrable_pow8_coord c]
    _ ≤ 256 * (Fintype.card (Coord L W) : ℝ) ^ 7 * ∑ _c : Coord L W, (105 : ℝ) := by
        gcongr with c
        exact AzumaProxyN_integral_pow8_coord_le c
    _ = 6881280 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 16 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

end MomentsBound8

section MomentsPath8

variable (d : Sizes)

private theorem AzumaProxyN_map_incr_slice (n j : ℕ) :
    (pathP d).map (fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) = P (d.L n) (d.W n) := by
  have h := Measure.map_map (μ := pathP d) (Sizes.measurable_slice d n)
    (measurable_pi_apply (j + 1) : Measurable fun ω : PathΩ d => ω (j + 1))
  rw [map_incr, Sizes.seqP_map_slice] at h
  exact h.symm

private theorem AzumaProxyN_transfer (n j : ℕ) {f : Ω (d.L n) (d.W n) → ℝ}
    (hf : Integrable f (P (d.L n) (d.W n))) :
    Integrable (fun ω : PathΩ d => f (Sizes.slice d n (ω (j + 1)))) (pathP d) ∧
      ∫ ω : PathΩ d, f (Sizes.slice d n (ω (j + 1))) ∂(pathP d)
        = ∫ x, f x ∂(P (d.L n) (d.W n)) := by
  have hmap := AzumaProxyN_map_incr_slice d n j
  have hgm : AEStronglyMeasurable f
      ((pathP d).map fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have hm : AEMeasurable (fun ω : PathΩ d => Sizes.slice d n (ω (j + 1))) (pathP d) :=
    ((Sizes.measurable_slice d n).comp (measurable_pi_apply (j + 1))).aemeasurable
  refine ⟨(integrable_map_measure hgm hm).1 (by rw [hmap]; exact hf), ?_⟩
  have h := integral_map hm hgm
  rw [hmap] at h
  exact h.symm

/-- **The eighth moment of one increment is integrable**: `‖X_{j+1}‖⁸`.  The eighth-moment
analogue of `integrable_normPow4_incr`. -/
theorem AzumaProxyN_integrable_normPow8_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ d => ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 8) (pathP d) :=
  (AzumaProxyN_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 8) AzumaProxyN_integrable_normPow8).1

/-- **The eighth moment of one increment**: `E ‖X_{j+1}‖⁸ ≤ 6881280 N¹⁶`, `N = (W L)²`
(`‖X‖ ≤ 2 Σ_c |ω_c|`, power mean over the `2 N²` coordinates, `E ω_c⁸ = 105 v⁴ ≤ 105`); the
eighth-moment analogue of `integral_normPow4_incr_le`. -/
theorem AzumaProxyN_integral_normPow8_incr_le (n j : ℕ) :
    ∫ ω : PathΩ d, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 8 ∂(pathP d)
      ≤ 6881280 * (Sizes.size d n : ℝ) ^ 16 :=
  le_of_eq_of_le (AzumaProxyN_transfer d n j
    (f := fun x => ‖Xmat (d.L n) (d.W n) x‖ ^ 8) AzumaProxyN_integrable_normPow8).2
    (AzumaProxyN_integral_normPow8_le (L := d.L n) (W := d.W n))

end MomentsPath8


/-! ## 3. The stopped `Y` increments: moments from domination by `ρ (‖X_{j+1}‖² + m)`

The conditional expectation of a function of the increment is `condExp_indep_eq` for `indep_incr`,
and the dominating function is squared and raised to the fourth power with the crude
`(x + y)^2 ≤ 2 (x² + y²)`, `(x + y)^4 ≤ 8 (x^4 + y^4)`, so that only `E ‖X‖⁴`, `E ‖X‖⁸` enter. -/

section YMoments

variable (d : Sizes)

private theorem AzumaProxyN_measurable_normX (n : ℕ) :
    Measurable fun x : Sizes.SeqΩ d => ‖Sizes.seqXmat d n x‖ :=
  ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).norm

/-- `E[φ(X_{j+1}) | F_j] = E φ(X_{j+1})` for a measurable `φ` of the increment: the increment
`ω (j + 1)` is independent of `filt d j` (`indep_incr`). -/
private theorem AzumaProxyN_condExp_incr (j : ℕ) {φ : Sizes.SeqΩ d → ℝ} (hφ : Measurable φ) :
    (pathP d)[fun ω => φ (ω (j + 1)) | filt d j] =ᵐ[pathP d]
      fun _ => ∫ ω, φ (ω (j + 1)) ∂(pathP d) := by
  have hle₁ : MeasurableSpace.comap (fun ω : PathΩ d => ω (j + 1)) inferInstance ≤
      (inferInstance : MeasurableSpace (PathΩ d)) := (measurable_pi_apply (j + 1)).comap_le
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω : PathΩ d => ω (j + 1)) inferInstance]
      (fun ω : PathΩ d => φ (ω (j + 1))) :=
    (hφ.comp (comap_measurable (fun ω : PathΩ d => ω (j + 1)))).stronglyMeasurable
  exact condExp_indep_eq hle₁ ((filt d).le j) hf (indep_incr d j)

private theorem AzumaProxyN_pow4_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h := mul_nonneg (sq_nonneg (x - y)) (show 0 ≤ 7 * x ^ 2 + 10 * x * y + 7 * y ^ 2 by positivity)
  nlinarith [h]

/-- **Moments of a real process dominated by `c (‖X_{j+1}‖² + m)`**: the fourth power is integrable, the conditional second moment is
at most `2 c² (B₄ + m²)` and the fourth moment at most `8 c⁴ (B₈ + m⁴)`, where `B₄`, `B₈` bound
`E ‖X‖⁴`, `E ‖X‖⁸`. -/
private theorem AzumaProxyN_moments_of_dom (n j : ℕ) {W : PathΩ d → ℝ} (hWm : Measurable W)
    {c m B4 B8 : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hB4 : ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) ≤ B4)
    (hB8 : ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 8 ∂(pathP d) ≤ B8)
    (hdom : ∀ᵐ ω ∂(pathP d), |W ω| ≤ c * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m)) :
    Integrable (fun ω => W ω ^ 4) (pathP d)
      ∧ (pathP d)[fun ω => W ω ^ 2 | filt d j] ≤ᵐ[pathP d] (fun _ => 2 * c ^ 2 * (B4 + m ^ 2))
      ∧ (∫ ω, W ω ^ 4 ∂(pathP d)) ≤ 8 * c ^ 4 * (B8 + m ^ 4) := by
  set f2 : Sizes.SeqΩ d → ℝ := fun x => 2 * c ^ 2 * (‖Sizes.seqXmat d n x‖ ^ 4 + m ^ 2) with hf2
  set f4 : Sizes.SeqΩ d → ℝ := fun x => 8 * c ^ 4 * (‖Sizes.seqXmat d n x‖ ^ 8 + m ^ 4) with hf4
  have hnX := AzumaProxyN_measurable_normX d n
  have hf2m : Measurable f2 := ((hnX.pow_const 4).add_const _).const_mul _
  have hf4m : Measurable f4 := ((hnX.pow_const 8).add_const _).const_mul _
  have hg2i : Integrable (fun ω : PathΩ d => f2 (ω (j + 1))) (pathP d) :=
    ((integrable_normPow4_incr d n j).add (integrable_const (m ^ 2))).const_mul _
  have hg4i : Integrable (fun ω : PathΩ d => f4 (ω (j + 1))) (pathP d) :=
    ((AzumaProxyN_integrable_normPow8_incr d n j).add (integrable_const (m ^ 4))).const_mul _
  have hW2 : ∀ᵐ ω ∂(pathP d), W ω ^ 2 ≤ f2 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    set a := ‖Sizes.seqXmat d n (ω (j + 1))‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hω 2
    rw [sq_abs] at h1
    have h2 := mul_nonneg (sq_nonneg c) (sq_nonneg (a ^ 2 - m))
    simp only [hf2]
    nlinarith [h1, h2]
  have hW4 : ∀ᵐ ω ∂(pathP d), W ω ^ 4 ≤ f4 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    set a := ‖Sizes.seqXmat d n (ω (j + 1))‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have h0 : 0 ≤ c * (a ^ 2 + m) := by positivity
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hω 4
    rw [show |W ω| ^ 4 = W ω ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at h1
    have h2 := AzumaProxyN_pow4_le (a ^ 2) m (by positivity) hm
    have h3 : (c * (a ^ 2 + m)) ^ 4 = c ^ 4 * (a ^ 2 + m) ^ 4 := by ring
    have h4 : 0 ≤ c ^ 4 := by positivity
    simp only [hf4]
    calc W ω ^ 4 ≤ (c * (a ^ 2 + m)) ^ 4 := h1
      _ = c ^ 4 * (a ^ 2 + m) ^ 4 := h3
      _ ≤ c ^ 4 * (8 * ((a ^ 2) ^ 4 + m ^ 4)) := mul_le_mul_of_nonneg_left h2 h4
      _ = 8 * c ^ 4 * (a ^ 8 + m ^ 4) := by ring
  have hW2i : Integrable (fun ω => W ω ^ 2) (pathP d) :=
    hg2i.mono' (hWm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hW2] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hω)
  have hW4i : Integrable (fun ω => W ω ^ 4) (pathP d) :=
    hg4i.mono' (hWm.pow_const 4).aestronglyMeasurable (by
      filter_upwards [hW4] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hω)
  refine ⟨hW4i, ?_, ?_⟩
  · have hmono := condExp_mono (m := filt d j) hW2i hg2i hW2
    have hfr := AzumaProxyN_condExp_incr d j hf2m
    filter_upwards [hmono, hfr] with ω h1 h2
    rw [h2] at h1
    refine h1.trans ?_
    have hI : ∫ ω, f2 (ω (j + 1)) ∂(pathP d)
        = 2 * c ^ 2 * (∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) + m ^ 2) := by
      simp only [hf2]
      rw [integral_const_mul, integral_add (integrable_normPow4_incr d n j)
        (integrable_const (m ^ 2))]
      simp
    rw [hI]
    have : 0 ≤ 2 * c ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  · have hmono := integral_mono_ae hW4i hg4i hW4
    refine hmono.trans ?_
    have hI : ∫ ω, f4 (ω (j + 1)) ∂(pathP d)
        = 8 * c ^ 4 * (∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 8 ∂(pathP d) + m ^ 4) := by
      simp only [hf4]
      rw [integral_const_mul, integral_add (AzumaProxyN_integrable_normPow8_incr d n j)
        (integrable_const (m ^ 4))]
      simp
    rw [hI]
    have : 0 ≤ 8 * c ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this

/-- Real and imaginary parts of a stopped process with conditional mean zero have conditional mean
zero (`S ∈ F_j`). -/
private theorem AzumaProxyN_condExp_stopped_reim (j : ℕ) {S : Set (PathΩ d)}
    (hS : MeasurableSet[filt d j] S) {Vf : PathΩ d → ℂ} (hVint : Integrable Vf (pathP d))
    (hmean : (pathP d)[Vf | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ)) :
    (pathP d)[fun ω => (S.indicator Vf ω).re | filt d j] =ᵐ[pathP d] 0 ∧
      (pathP d)[fun ω => (S.indicator Vf ω).im | filt d j] =ᵐ[pathP d] 0 := by
  constructor
  · have hfun : (fun ω => (S.indicator Vf ω).re) = S.indicator (fun ω => (Vf ω).re) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt d j) (f := fun ω => (Vf ω).re) hVint.re hS
    have h2 : (pathP d)[fun ω => (Vf ω).re | filt d j] =ᵐ[pathP d] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hVint
        Complex.reCLM).symm
      have hc' : (pathP d)[fun ω => (Vf ω).re | filt d j]
          =ᵐ[pathP d] fun ω => ((pathP d)[Vf | filt d j] ω).re := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1, h2]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl
  · have hfun : (fun ω => (S.indicator Vf ω).im) = S.indicator (fun ω => (Vf ω).im) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt d j) (f := fun ω => (Vf ω).im) hVint.im hS
    have h2 : (pathP d)[fun ω => (Vf ω).im | filt d j] =ᵐ[pathP d] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hVint
        Complex.imCLM).symm
      have hc' : (pathP d)[fun ω => (Vf ω).im | filt d j]
          =ᵐ[pathP d] fun ω => ((pathP d)[Vf | filt d j] ω).im := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1, h2]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl

end YMoments

/-! ## 4. The kernel row sums of `Ugen` -/

section KernelRows

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2`. -/
private theorem AzumaProxyN_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (b : Bool) :
    ‖KLoop.mSig E b‖ = 1 := by
  cases b <;> simp [KLoop.mSig, norm_spectralM hE]

/-- The slot parameter `m(σ) m(σ')` has modulus `1` for `|E| ≤ 2`. -/
private theorem AzumaProxyN_norm_slot {E : ℝ} (hE : |E| ≤ 2) (b b' : Bool) :
    ‖KLoop.mSig E b * KLoop.mSig E b'‖ ≤ 1 := by
  rw [norm_mul, AzumaProxyN_norm_mSig hE, AzumaProxyN_norm_mSig hE]
  simp

open scoped Matrix.Norms.Operator in
/-- The exact form of the kernel `(1 - vξS) Θ_{wξ} = 1 + (w - v) ξ SΘ_{wξ}`, from
`(1 - wξ S) Θ_{wξ} = 1` (`mul_Theta`). -/
private theorem AzumaProxyN_ukerMat_eq (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v w = 1 + ((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w := by
  have h := mul_Theta L hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat thetaGenMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

open scoped Matrix.Norms.Operator in
/-- The `ℓ^∞` operator norm of the one-slot kernel: `‖(1 - vξS) Θ_{wξ}‖ ≤ 1 + (1 - w)⁻¹` for
`0 ≤ v, w < 1`, `‖ξ‖ ≤ 1` (no order between `v` and `w`; via `|w - v| ≤ 1`). -/
private theorem AzumaProxyN_norm_ukerMat_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ‖ukerMat L ξ v w‖ ≤ 1 + (1 - w)⁻¹ := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hwξ : ‖(w : ℂ) * ξ‖ = w * ‖ξ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
  have hw' : ‖(w : ℂ) * ξ‖ < 1 := by
    rw [hwξ]
    calc w * ‖ξ‖ ≤ w * 1 := mul_le_mul_of_nonneg_left hξ hw0
      _ = w := mul_one w
      _ < 1 := hw1
  have hwv : ‖(w : ℂ) - (v : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hgen : ‖thetaGenMat L ξ w‖ ≤ ‖ξ‖ * (1 - w * ‖ξ‖)⁻¹ := by
    unfold thetaGenMat
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ hξ0
    calc ‖SB L * Theta L ((w : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((w : ℂ) * ξ)‖ := norm_mul_le _ _
      _ = ‖Theta L ((w : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
      _ ≤ (1 - ‖(w : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hw'
      _ = (1 - w * ‖ξ‖)⁻¹ := by rw [hwξ]
  have harith : ‖ξ‖ * (1 - w * ‖ξ‖)⁻¹ ≤ (1 - w)⁻¹ := by
    have hsr : w * ‖ξ‖ ≤ w := mul_le_of_le_one_right hw0 hξ
    have hd : 0 < 1 - w * ‖ξ‖ := by linarith
    have hd' : 0 < 1 - w := by linarith
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hd hd']
    nlinarith
  rw [AzumaProxyN_ukerMat_eq L hL hw']
  calc ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) + ((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w‖
      ≤ ‖(1 : Matrix (Z2 L) (Z2 L) ℂ)‖ + ‖((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w‖ :=
        norm_add_le _ _
    _ = 1 + ‖(w : ℂ) - (v : ℂ)‖ * ‖thetaGenMat L ξ w‖ := by rw [norm_one, norm_smul]
    _ ≤ 1 + 1 * ((1 - w)⁻¹) := by
        refine add_le_add le_rfl (mul_le_mul hwv (hgen.trans harith) (norm_nonneg _) zero_le_one)
    _ = 1 + (1 - w)⁻¹ := by rw [one_mul]

open scoped Matrix.Norms.Operator in
/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
private theorem AzumaProxyN_sum_norm_row_le_opNorm (L : ℕ) [NeZero L]
    (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) : ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- **The row sums of the `Ugen` kernel**: for `|E| ≤ 2`, `3 ≤ L`, `0 ≤ v, w < 1`, the kernel
`(a, b) ↦ Π_i ukerMat (m_i m_{i+1}) v w (a_i, b_i)` of `Ugen` has row sums
`Σ_b ‖κ(a, b)‖ ≤ (1 + (1 - w)⁻¹)^k` (each of the `k` slots has row sum at most `1 + (1 - w)⁻¹`,
`|m_i m_{i+1}| = 1`). -/
private theorem AzumaProxyN_rowsum_Ugen (L : ℕ) [NeZero L] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} [NeZero k] (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (a : Fin k → Z2 L) :
    ∑ b : Fin k → Z2 L, ‖∏ i : Fin k,
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k := by
  have hrow : ∀ (i : Fin k) (x : Z2 L),
      ∑ c : Z2 L, ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w x c‖ ≤
        1 + (1 - w)⁻¹ := fun i x =>
    (AzumaProxyN_sum_norm_row_le_opNorm L _ x).trans
      (AzumaProxyN_norm_ukerMat_le L hL (AzumaProxyN_norm_slot hE _ _) hv0 hv1 hw0 hw1)
  simp_rw [norm_prod]
  rw [← Fintype.prod_sum (fun (i : Fin k) (c : Z2 L) =>
    ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) c‖)]
  calc ∏ i : Fin k, ∑ c : Z2 L,
        ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) c‖
      ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
          (fun i _ => hrow i (a i))
    _ = (1 + (1 - w)⁻¹) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end KernelRows

/-! ## 5. One step: the eight moment fields of `YMomentBoundsN`

Fix `n`, the step `j < m ≤ K n` and the label `b`.  With the loop family `Φ = loopFamN` and the
kernel `Ukern (a, b') = Π_i ukerMat (a_i, b'_i)` of `Ugen`, the stopped propagated increment is
a.e. `1_{j<τ} stepYCN Φ Ukern b` (`Ugen_stepYCN`); `stepDecompCN` gives `E[Y | F_j] = 0` and
`‖Y‖ ≤ g + E[g | F_j]`, `g = (Σ_a ‖Ukern b a‖) (C₂/2) Δ ‖X_{j+1}‖²`; the independence of `X_{j+1}`
and `F_j` turns this into `‖Y‖ ≤ ρ (‖X_{j+1}‖² + E ‖X‖²)` a.e. -/

section YFields

variable (d : Sizes)

/-- **The eight moment fields of `YMomentBoundsN` for one step and one label**, with the loop
family, given the deterministic constants `S` (row sum of the `Ugen` kernel), `C₂` (Hermitian
second-derivative bound of the loops) and `P ≥ 2000 (S C₂)² N⁸`: the real and imaginary parts of the
stopped propagated increment `1_{j<τ} (𝒰_{u_{j+1},u_m} Y_j)_b` have conditional mean zero, integrable
fourth power, conditional second moment `≤ Δ² P` and fourth moment `≤ Δ⁴ P²`. -/
private theorem AzumaProxyN_Yfields (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j m : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hjm : j < m)
    (hm : m ≤ K n) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n))
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2)
    (hrow : ∑ b' : Fin k → Z2 (d.L n), ‖∏ i : Fin k, ukerMat (d.L n)
      (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (b i) (b' i)‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Z2 (d.L n))
      (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN d E s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (Sizes.size d n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ d → ℕ) (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) :
    (pathP d)[fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).re | filt d j] =ᵐ[pathP d] 0 ∧
    (pathP d)[fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).im | filt d j] =ᵐ[pathP d] 0 ∧
    Integrable (fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).re ^ 4) (pathP d) ∧
    Integrable (fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).im ^ 4) (pathP d) ∧
    (pathP d)[fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).re ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => gridStep s t K n ^ 2 * P) ∧
    (pathP d)[fun ω => (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).im ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).re ^ 4 ∂(pathP d)
      ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => YvecN d E s t K n j σ ω) b j ω).im ^ 4 ∂(pathP d)
      ≤ gridStep s t K n ^ 4 * P ^ 2 := by
  have hj : j + 1 ≤ K n := by omega
  have hΔ : 0 ≤ gridStep s t K n := GoodEvent_gridStep_nonneg hst
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (GoodEvent_gridTime_le (K := K) hst hj).trans_lt ht1
  set Δ := gridStep s t K n with hΔdef
  set N : ℝ := (Sizes.size d n : ℝ) with hNdef
  set Ukern : (Fin k → Z2 (d.L n)) → (Fin k → Z2 (d.L n)) → ℂ := fun a b' => ∏ i : Fin k,
    ukerMat (d.L n) (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1)))
      (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b' i) with hU
  have hΦ : ∀ a, HermTestFun d n (loopFamN d E s t K n j σ a) := fun a =>
    (hermTestFunLoopN d k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hIntRe := integrable_stepZCN_re_of_hermTestFun d s t K n j hΦ hC2 hΔ Ukern b
  have hIntIm := integrable_stepZCN_im_of_hermTestFun d s t K n j hΦ hC2 hΔ Ukern b
  obtain ⟨-, -, hbound, hmeanY⟩ :=
    stepDecompCN d s t K n j hΦ hC2 hΔ Ukern b hIntRe hIntIm
  -- the increment moments
  set m2 : ℝ := ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 ∂(pathP d) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2le : m2 ≤ 16 * N ^ 4 := integral_normSq_incr_le d n j
  set R0 : ℝ := (∑ a, ‖Ukern b a‖) * ((C2 / 2) * Δ) with hR0
  set ρ : ℝ := Smax * ((C2 / 2) * Δ) with hρ
  have hcΔ : 0 ≤ (C2 / 2) * Δ := by positivity
  have hR0ρ : R0 ≤ ρ := mul_le_mul_of_nonneg_right hrow hcΔ
  have hρ0 : 0 ≤ ρ := by positivity
  have hcond : (pathP d)[fun ω' => (∑ a, ‖Ukern b a‖) * ((C2 / 2) * Δ)
        * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j]
      =ᵐ[pathP d] fun _ => R0 * m2 := by
    have h := AzumaProxyN_condExp_incr d j (φ := fun x => R0 * ‖Sizes.seqXmat d n x‖ ^ 2)
      (((AzumaProxyN_measurable_normX d n).pow_const 2).const_mul _)
    have hint : ∫ ω, R0 * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 ∂(pathP d) = R0 * m2 :=
      integral_const_mul _ _
    rw [hint] at h
    exact h
  -- the loop-side representation of the stopped increment
  set Vfull : PathΩ d → ℂ := fun ω => Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1))
    (gridTime s t K n m) (YvecN d E s t K n j σ ω) b with hVfull
  have hVae : ∀ᵐ ω ∂(pathP d), Vfull ω = stepYCN d s t K n j (loopFamN d E s t K n j σ) Ukern b ω := by
    filter_upwards [Ugen_stepYCN d E s t K n j hE hs0 hst ht1 hj σ m] with ω hω
    exact hω b
  have hYm : Measurable fun ω : PathΩ d => YvecN d E s t K n j σ ω :=
    (stronglyMeasurable_YvecN d E s t K n j σ).measurable.mono ((filt d).le (j + 1)) le_rfl
  have hVm : Measurable Vfull := by
    change Measurable fun ω : PathΩ d => ∑ b' : Fin k → Z2 (d.L n), (∏ i : Fin k, ukerMat (d.L n)
      (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (b i) (b' i)) * YvecN d E s t K n j σ ω b'
    exact Finset.measurable_sum _ fun b' _ => ((measurable_pi_apply b').comp hYm).const_mul _
  have hdom : ∀ᵐ ω ∂(pathP d), ‖Vfull ω‖ ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hVae, hbound, hcond] with ω h1 h2 h3
    rw [h1]
    rw [h3] at h2
    have hX0 : 0 ≤ ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2 := by positivity
    calc ‖stepYCN d s t K n j (loopFamN d E s t K n j σ) Ukern b ω‖
        ≤ R0 * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + R0 * m2 := h2
      _ = R0 * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by ring
      _ ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := mul_le_mul_of_nonneg_right hR0ρ hX0
  have hmean : (pathP d)[Vfull | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) :=
    (condExp_congr_ae hVae).trans hmeanY
  have hS : MeasurableSet[filt d j] {ω | j < τ ω} := hτ j
  have hB4 := integral_normPow4_incr_le d n j
  have hB8 := AzumaProxyN_integral_normPow8_incr_le d n j
  -- the stopped moments
  have hVint : Integrable Vfull (pathP d) :=
    (((integrable_normSq_incr d n j).add (integrable_const m2)).const_mul ρ).mono'
      hVm.aestronglyMeasurable hdom
  have hSm : MeasurableSet {ω | j < τ ω} := (filt d).le j _ hS
  have hVind : Measurable ({ω | j < τ ω}.indicator Vfull) := hVm.indicator hSm
  have hdomS : ∀ᵐ ω ∂(pathP d), ‖{ω | j < τ ω}.indicator Vfull ω‖
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdom] with ω hω
    exact (norm_indicator_le_norm_self _ _).trans hω
  have hdomRe : ∀ᵐ ω ∂(pathP d), |({ω | j < τ ω}.indicator Vfull ω).re|
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(pathP d), |({ω | j < τ ω}.indicator Vfull ω).im|
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := AzumaProxyN_moments_of_dom d n j
    (Complex.measurable_re.comp hVind) hρ0 hm20 hB4 hB8 hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := AzumaProxyN_moments_of_dom d n j
    (Complex.measurable_im.comp hVind) hρ0 hm20 hB4 hB8 hdomIm
  obtain ⟨hmRe, hmIm⟩ := AzumaProxyN_condExp_stopped_reim d j hS hVint hmean
  -- the numerical bounds
  have hq0 : 0 ≤ Smax * C2 := mul_nonneg hS0 hC20
  have hN0 : 0 ≤ N := by positivity
  have hρq : ρ = (Smax * C2) * Δ / 2 := by simp only [hρ]; ring
  have hv : 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2) ≤ Δ ^ 2 * P := by
    have hm2sq : m2 ^ 2 ≤ 256 * N ^ 8 := by
      calc m2 ^ 2 ≤ (16 * N ^ 4) ^ 2 := pow_le_pow_left₀ hm20 hm2le 2
        _ = 256 * N ^ 8 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
    calc 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2)
        ≤ 2 * ρ ^ 2 * (768 * N ^ 8 + 256 * N ^ 8) := by gcongr
      _ = 512 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by rw [hρq]; ring
      _ ≤ 2000 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by nlinarith
      _ = Δ ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by ring
      _ ≤ Δ ^ 2 * P := by gcongr
  have hw : 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4) ≤ Δ ^ 4 * P ^ 2 := by
    have hm2q : m2 ^ 4 ≤ 65536 * N ^ 16 := by
      calc m2 ^ 4 ≤ (16 * N ^ 4) ^ 4 := pow_le_pow_left₀ hm20 hm2le 4
        _ = 65536 * N ^ 16 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16 := by positivity
    have hP0 : 0 ≤ 2000 * (Smax * C2) ^ 2 * N ^ 8 := by positivity
    calc 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4)
        ≤ 8 * ρ ^ 4 * (6881280 * N ^ 16 + 65536 * N ^ 16) := by gcongr
      _ = 3473408 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by rw [hρq]; ring
      _ ≤ 4000000 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by nlinarith
      _ = Δ ^ 4 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ^ 2 := by ring
      _ ≤ Δ ^ 4 * P ^ 2 := by gcongr
  refine ⟨hmRe, hmIm, hRe4, hIm4, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hRe2] with ω h
    exact h.trans hv
  · filter_upwards [hIm2] with ω h
    exact h.trans hv
  · exact hRe4'.trans hw
  · exact hIm4'.trans hw

end YFields

/-! ## 6. The explicit constants of `yMomentsUnifN`

The explicit witness: `C_P = 11 + (4 k + 4) · max 0 (1 - τ')`, with, for every `n` with `N = size n`
large and the range condition, `Θ = N^{max 0 (1-τ')}`, `c₀ = √(κ (4 - κ)) / 2`,
`S = (2 Θ)^k` (row sums of `Ugen`), `C₂ = k (k + 1) N (Θ / c₀)^{k+2}` (the second-derivative bound
of the loops) and `P = 2000 (S C₂)² N⁸`. -/

section YMomentsFinal

/-- `Im m^{(E)} ≥ √(κ (4 - κ)) / 2` in the bulk `|E| ≤ 2 - κ`. -/
private theorem AzumaProxyN_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private theorem AzumaProxyN_c0_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- `(1 - u)⁻¹ ≤ N^{1-τ'}` for `u ≤ t` and the range condition `N^{-1+τ'} ≤ 1 - t`. -/
private theorem AzumaProxyN_inv_one_sub_le {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
    (hR : N ^ (-1 + τ') ≤ 1 - t) : (1 - u)⁻¹ ≤ N ^ (1 - τ') := by
  have hpos : 0 < N ^ (-1 + τ') := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τ') ≤ 1 - u := by linarith
  calc (1 - u)⁻¹ ≤ (N ^ (-1 + τ'))⁻¹ := inv_anti₀ hpos h1
    _ = N ^ (1 - τ') := by
        rw [show (-1 + τ') = -(1 - τ') by ring, Real.rpow_neg hN0.le, inv_inv]

/-- `η_u⁻¹ ≤ N^{1-τ'} / c₀` for `u ≤ t`, in the bulk, under the range condition. -/
private theorem AzumaProxyN_etaT_inv_le {κ E u t τ' N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) := by
  have hc0 := AzumaProxyN_c0_pos hκ hE
  have hm := AzumaProxyN_im_ge hE
  have hpos : 0 < N ^ (-1 + τ') := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τ') ≤ 1 - u := by linarith
  have hη : N ^ (-1 + τ') * (Real.sqrt (κ * (4 - κ)) / 2) ≤ etaT E u := by
    unfold etaT
    exact mul_le_mul h1 hm hc0.le (by linarith)
  calc (etaT E u)⁻¹ ≤ (N ^ (-1 + τ') * (Real.sqrt (κ * (4 - κ)) / 2))⁻¹ :=
        inv_anti₀ (mul_pos hpos hc0) hη
    _ = N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) := by
        rw [mul_inv, show (-1 + τ') = -(1 - τ') by ring, Real.rpow_neg hN0.le, inv_inv]
        exact (div_eq_mul_inv _ _).symm

/-- The final size bound `P ≤ N^{C_P}`. -/
private theorem AzumaProxyN_P_le (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
    (hbig : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤ N) :
    2000 * ((2 * N ^ θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (N ^ θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      ≤ N ^ (11 + (4 * k + 4) * θ) := by
  have hN0 : 0 < N := by linarith
  set A : ℝ := 2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2) with hA
  set Θ : ℝ := N ^ θ with hΘ
  have hid : 2000 * ((2 * Θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (Θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      = (2000 * A ^ 2) * (Θ ^ (4 * k + 4) * N ^ 10) := by
    rw [hA, div_eq_mul_inv]
    ring
  have hΘpow : Θ ^ (4 * k + 4) = N ^ ((4 * k + 4 : ℝ) * θ) := by
    rw [hΘ, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    push_cast
    ring_nf
  have hN10 : N ^ 10 = N ^ (10 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hsplit : N ^ (11 + (4 * k + 4) * θ) = N * (N ^ ((4 * k + 4 : ℝ) * θ) * N ^ (10 : ℝ)) := by
    rw [show (11 + (4 * k + 4) * θ : ℝ) = 1 + (((4 * k + 4 : ℝ) * θ) + 10) by ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
  rw [hid, hΘpow, hN10, hsplit]
  have hpos : 0 ≤ N ^ ((4 * k + 4 : ℝ) * θ) * N ^ (10 : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right hbig hpos


end YMomentsFinal

end RBM.Ind

end

/-! ## 7. `YMomentsUnifN`: the uniform `Y` moments

The constant `C_P` is chosen before the grid `K`; `K` and `hK` are introduced after `C_P` (none of
`C_P`, the eventual threshold and `P` depends on `K`). -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section YMomentsUnif

variable (d : Sizes)


/-- **`YMomentsUnifN`**: the constant
`C_P` is taken **before** the grid `K`, so that a consumer can choose `C_K ≥ D₁ + 4D + k + 2C_P + 8`
after `C_P` (`AssembledN`); `C_P` must not depend on `K`, because `K = gridK … C_K` depends on
`C_P`.  This is true: `P` is a moment of the Gaussian increments and of `η_t⁻¹`, independent
of `K`. -/
def YMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  SizeTendsto d → RangeCond d τ' t →
  ∀ (k : ℕ) [NeZero k] (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
        YMomentBoundsN d (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => YvecN d E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **`yMomentsUnifN`**: the uniform `Y` moments.  **Explicit witness**
`C_P = 11 + (4 k + 4) · max 0 (1 - τ')`, chosen before the grid `K`; the eventual threshold
`N ≥ max 1 (2000 (2^k k (k + 1) c₀^{-(k+2)})²)` and `P = 2000 (S C₂)² N⁸` depend on `k, κ, τ'`
(and `d, t`) only.  `K` and `hK` are introduced after `C_P`. -/
theorem yMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsUnifN d κ τ' E s t := by
  intro hκ hE hs0 hst ht1 hsize hrange k _ σ
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := AzumaProxyN_c0_pos hκ (hE 0)
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0def
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  refine ⟨11 + (4 * k + 4) * θ, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max 1 (2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hΘ1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((d.size n : ℕ) : ℝ) ^ θ) ^ k with hSmax
  set C2 : ℝ := ((k * (k + 1) : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ)
    * (((d.size n : ℕ) : ℝ) ^ θ / c0) ^ (k + 2) with hC2def
  have hS0 : 0 ≤ Smax := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨2000 * (Smax * C2) ^ 2 * ((d.size n : ℕ) : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · exact AzumaProxyN_P_le k hc0 hθ0 hN1 ((le_max_right _ _).trans hN)
  · intro τ hτ
    refine ⟨fun j => stronglyMeasurable_YvecN d E s t K n j σ, ?_⟩
    intro m hm b j hjm
    have hj : j + 1 ≤ K n := by omega
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := GoodEvent_gridTime_le (K := K) (hst n) hj
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n m := GoodEvent_gridTime_nonneg (hs0 n) (hst n) m
    have hwt : gridTime s t K n m ≤ t n := GoodEvent_gridTime_le (K := K) (hst n) hm
    have hw1 : gridTime s t K n m < 1 := hwt.trans_lt (ht1 n)
    refine AzumaProxyN_Yfields d E s t K n j m hEn (hs0 n) (hst n) (ht1 n) hjm hm σ b hS0 hC20
      ?_ ?_ le_rfl τ hτ
    · refine (AzumaProxyN_rowsum_Ugen (d.L n) (d.three_le_L n) hEn.le σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n m)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τ') :=
        AzumaProxyN_inv_one_sub_le hwt hN0 hR
      have h2 : ((d.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((d.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    · intro a M y hM hy
      have hη := AzumaProxyN_etaT_inv_le (κ := κ) (E := E n) (u := gridTime s t K n (j + 1))
        (t := t n) (τ' := τ') (N := ((d.size n : ℕ) : ℝ)) hκ (hE n) hvt hN0 hR
      have hη' : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹
          ≤ ((d.size n : ℕ) : ℝ) ^ θ / c0 :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (hermTestFunLoopN d k n (E n) (gridTime s t K n (j + 1)) hEn hv0 hv1 σ a).2 M y hM hy
      refine h.trans ?_
      have hle : ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size d n : ℝ)
          * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ := by
          have := etaT_pos hEn hv1
          positivity
        have := pow_le_pow_left₀ hη0 hη' (k + 2)
        have hpos : 0 ≤ ((k * (k + 1) : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)


end YMomentsUnif

end RBM.Ind

end

/-! ## 8. The weighted `Y` fields

The eight moment fields of the private `AzumaProxyN_Yfields` for the stopped increment `1_{j<τ} Σ_c κ_c Y_c` of an
arbitrary weight vector `κ` with `Σ_c ‖κ_c‖ ≤ S` in place of the `Ugen` row; they are used in
`RBM2D.Induction.AltProxyQ` (`yMomentsQUnifN`), where `κ = Σ_b κ^{Ugen}_b Qmat_u(b, ·)` is the
transposed `𝒬`-weight vector.  Each `Y_c` has conditional mean zero and the pathwise domination
`‖Y_c‖ ≤ (C₂/2) Δ (‖X_{j+1}‖² + E‖X‖²)` (`stepDecompCN` at the identity kernel and
`YvecN_eq_stepYCN`), so the combination is dominated by `S (C₂/2) Δ (‖X_{j+1}‖² + E‖X‖²)`, and
the moment bounds of `AzumaProxyN_moments_of_dom` apply as in `AzumaProxyN_Yfields`.  The four
numerical helpers of section 6 and the row sums of the `Ugen` kernel (section 4) are re-exported as
the public theorems `AzumaProxyN_c0_pos_pub`, `AzumaProxyN_inv_one_sub_le_pub`,
`AzumaProxyN_etaT_inv_le_pub`, `AzumaProxyN_P_le_pub`, `AzumaProxyN_rowsum_Ugen_pub`. -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section YFieldsW

variable (d : Sizes)

/-- The stopped weighted increment `1_{j<τ} Σ_c κ_c Y_c` of the step `j → j+1`. -/
def AzumaProxyN_stopW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (κ : (Fin k → Z2 (d.L n)) → ℂ) (τ : PathΩ d → ℕ) (ω : PathΩ d) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * YvecN d E s t K n j σ ω' c) ω

/-- **The eight moment fields for an arbitrary weight vector** (the weighted analogue of the private
`AzumaProxyN_Yfields`): for `Σ_c ‖κ_c‖ ≤ S`, the Hermitian second-derivative bound `C₂` of the loop
family and `P ≥ 2000 (S C₂)² N⁸`, the real and imaginary parts of `1_{j<τ} Σ_c κ_c (Y_j)_c` have
conditional mean zero, integrable fourth power, conditional second moment `≤ Δ² P` and fourth moment
`≤ Δ⁴ P²`. -/
theorem AzumaProxyN_YfieldsW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (κ : (Fin k → Z2 (d.L n)) → ℂ)
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2) (hrow : ∑ c, ‖κ c‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Z2 (d.L n))
      (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN d E s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (Sizes.size d n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ d → ℕ) (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) :
    (pathP d)[fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).re | filt d j] =ᵐ[pathP d] 0 ∧
    (pathP d)[fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).im | filt d j] =ᵐ[pathP d] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).re ^ 4) (pathP d) ∧
    Integrable (fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).im ^ 4) (pathP d) ∧
    (pathP d)[fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).re ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => gridStep s t K n ^ 2 * P) ∧
    (pathP d)[fun ω => (AzumaProxyN_stopW d E s t K n j σ κ τ ω).im ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopW d E s t K n j σ κ τ ω).re ^ 4 ∂(pathP d)
      ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopW d E s t K n j σ κ τ ω).im ^ 4 ∂(pathP d)
      ≤ gridStep s t K n ^ 4 * P ^ 2 := by
  have hΔ : 0 ≤ gridStep s t K n := GoodEvent_gridStep_nonneg hst
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg hs0 hst (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 := (GoodEvent_gridTime_le (K := K) hst hj).trans_lt ht1
  set Δ := gridStep s t K n with hΔdef
  set N : ℝ := (Sizes.size d n : ℝ) with hNdef
  set δ : (Fin k → Z2 (d.L n)) → (Fin k → Z2 (d.L n)) → ℂ := fun a a' => if a = a' then 1 else 0
    with hδ
  have hΦ : ∀ a, HermTestFun d n (loopFamN d E s t K n j σ a) := fun a =>
    (hermTestFunLoopN d k n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a).1
  have hδrow : ∀ c : Fin k → Z2 (d.L n), ∑ a, ‖δ c a‖ = 1 := by
    intro c
    have h1 : ∀ x, ‖δ c x‖ = if c = x then (1 : ℝ) else 0 := by
      intro x
      by_cases h : c = x <;> simp [hδ, h]
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- the identity kernel, label by label
  have hDec : ∀ c : Fin k → Z2 (d.L n),
      (∀ᵐ ω ∂(pathP d), ‖stepYCN d s t K n j (loopFamN d E s t K n j σ) δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 +
            (pathP d)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω) ∧
      (pathP d)[stepYCN d s t K n j (loopFamN d E s t K n j σ) δ c | filt d j] =ᵐ[pathP d]
        fun _ => (0 : ℂ) := by
    intro c
    have hIntRe := integrable_stepZCN_re_of_hermTestFun d s t K n j hΦ hC2 hΔ δ c
    have hIntIm := integrable_stepZCN_im_of_hermTestFun d s t K n j hΦ hC2 hΔ δ c
    obtain ⟨-, -, hbound, hmeanY⟩ := stepDecompCN d s t K n j hΦ hC2 hΔ δ c hIntRe hIntIm
    exact ⟨hbound, hmeanY⟩
  -- the increment moments
  set m2 : ℝ := ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 ∂(pathP d) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2le : m2 ≤ 16 * N ^ 4 := integral_normSq_incr_le d n j
  set R1 : ℝ := (C2 / 2) * Δ with hR1
  set ρ : ℝ := Smax * R1 with hρ
  have hR10 : 0 ≤ R1 := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hcond : (pathP d)[fun ω' => R1 * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j]
      =ᵐ[pathP d] fun _ => R1 * m2 := by
    have h := AzumaProxyN_condExp_incr d j (φ := fun x => R1 * ‖Sizes.seqXmat d n x‖ ^ 2)
      (((AzumaProxyN_measurable_normX d n).pow_const 2).const_mul _)
    have hint : ∫ ω, R1 * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 ∂(pathP d) = R1 * m2 :=
      integral_const_mul _ _
    rw [hint] at h
    exact h
  -- `Y_c` a.e. equals `stepYCN` of the identity kernel
  have hYall := YvecN_eq_stepYCN d E s t K n j hE hs0 hst ht1 hj σ
  have hdomc : ∀ᵐ ω ∂(pathP d), ∀ c : Fin k → Z2 (d.L n),
      ‖YvecN d E s t K n j σ ω c‖ ≤ R1 * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    have h1 : ∀ᵐ ω ∂(pathP d), ∀ c : Fin k → Z2 (d.L n),
        ‖stepYCN d s t K n j (loopFamN d E s t K n j σ) δ c ω‖ ≤
          (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 +
            (pathP d)[fun ω' => (∑ a, ‖δ c a‖) * ((C2 / 2) * Δ) *
              ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω :=
      ae_all_iff.mpr fun c => (hDec c).1
    simp only [hδrow, one_mul] at h1
    filter_upwards [hYall, h1, hcond] with ω hY hb hcd c
    rw [hY c]
    refine (hb c).trans ?_
    rw [hcd]
    nlinarith
  have hYm : Measurable fun ω : PathΩ d => YvecN d E s t K n j σ ω :=
    (stronglyMeasurable_YvecN d E s t K n j σ).measurable.mono ((filt d).le (j + 1)) le_rfl
  have hYcm : ∀ c : Fin k → Z2 (d.L n), Measurable fun ω : PathΩ d => YvecN d E s t K n j σ ω c :=
    fun c => (measurable_pi_apply c).comp hYm
  have hYcint : ∀ c : Fin k → Z2 (d.L n),
      Integrable (fun ω : PathΩ d => YvecN d E s t K n j σ ω c) (pathP d) := fun c =>
    (((integrable_normSq_incr d n j).add (integrable_const m2)).const_mul R1).mono'
      (hYcm c).aestronglyMeasurable (by filter_upwards [hdomc] with ω h using h c)
  have hYcmean : ∀ c : Fin k → Z2 (d.L n),
      (pathP d)[fun ω => YvecN d E s t K n j σ ω c | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) :=
    fun c => by
      have hae : (fun ω => YvecN d E s t K n j σ ω c) =ᵐ[pathP d]
          stepYCN d s t K n j (loopFamN d E s t K n j σ) δ c := by
        filter_upwards [hYall] with ω h using h c
      exact (condExp_congr_ae hae).trans (hDec c).2
  -- the weighted combination
  set Vfull : PathΩ d → ℂ := fun ω => ∑ c, κ c * YvecN d E s t K n j σ ω c with hVfull
  have hVm : Measurable Vfull :=
    Finset.measurable_sum _ fun c _ => (hYcm c).const_mul _
  have hdom : ∀ᵐ ω ∂(pathP d), ‖Vfull ω‖ ≤
      ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomc] with ω h
    have hX0 : 0 ≤ ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2 := by positivity
    calc ‖Vfull ω‖ ≤ ∑ c, ‖κ c * YvecN d E s t K n j σ ω c‖ := norm_sum_le _ _
      _ = ∑ c, ‖κ c‖ * ‖YvecN d E s t K n j σ ω c‖ := by simp only [norm_mul]
      _ ≤ ∑ c, ‖κ c‖ * (R1 * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h c) (norm_nonneg _)
      _ = (∑ c, ‖κ c‖) * (R1 * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ Smax * (R1 * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2)) :=
          mul_le_mul_of_nonneg_right hrow (by positivity)
      _ = ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by rw [hρ]; ring
  have hmean : (pathP d)[Vfull | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) := by
    have hint : ∀ c ∈ (Finset.univ : Finset (Fin k → Z2 (d.L n))),
        Integrable (fun ω => κ c * YvecN d E s t K n j σ ω c) (pathP d) :=
      fun c _ => (hYcint c).const_mul (κ c)
    have hcs := condExp_finsetSum hint (filt d j)
    have hsm : ∀ᵐ ω ∂(pathP d), ∀ c : Fin k → Z2 (d.L n),
        (pathP d)[fun ω' => κ c * YvecN d E s t K n j σ ω' c | filt d j] ω =
          κ c * (pathP d)[fun ω' => YvecN d E s t K n j σ ω' c | filt d j] ω :=
      ae_all_iff.mpr fun c =>
        condExp_smul (κ c) (fun ω' => YvecN d E s t K n j σ ω' c) (filt d j)
    have hz : ∀ᵐ ω ∂(pathP d), ∀ c : Fin k → Z2 (d.L n),
        (pathP d)[fun ω' => YvecN d E s t K n j σ ω' c | filt d j] ω = 0 :=
      ae_all_iff.mpr fun c => hYcmean c
    have hsumfn : (∑ c : Fin k → Z2 (d.L n), fun ω' => κ c * YvecN d E s t K n j σ ω' c) =
        Vfull := by
      funext ω'
      simp only [hVfull, Finset.sum_apply]
    rw [hsumfn] at hcs
    filter_upwards [hcs, hsm, hz] with ω h1 h2 h3
    rw [h1]
    simp only [Finset.sum_apply, h2, h3, mul_zero, Finset.sum_const_zero]
  have hS : MeasurableSet[filt d j] {ω | j < τ ω} := hτ j
  have hB4 := integral_normPow4_incr_le d n j
  have hB8 := AzumaProxyN_integral_normPow8_incr_le d n j
  -- the stopped moments
  have hVint : Integrable Vfull (pathP d) :=
    (((integrable_normSq_incr d n j).add (integrable_const m2)).const_mul ρ).mono'
      hVm.aestronglyMeasurable hdom
  have hSm : MeasurableSet {ω | j < τ ω} := (filt d).le j _ hS
  have hVind : Measurable ({ω | j < τ ω}.indicator Vfull) := hVm.indicator hSm
  have hdomS : ∀ᵐ ω ∂(pathP d), ‖{ω | j < τ ω}.indicator Vfull ω‖
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdom] with ω hω
    exact (norm_indicator_le_norm_self _ _).trans hω
  have hdomRe : ∀ᵐ ω ∂(pathP d), |({ω | j < τ ω}.indicator Vfull ω).re|
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(pathP d), |({ω | j < τ ω}.indicator Vfull ω).im|
      ≤ ρ * (‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomS] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := AzumaProxyN_moments_of_dom d n j
    (Complex.measurable_re.comp hVind) hρ0 hm20 hB4 hB8 hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := AzumaProxyN_moments_of_dom d n j
    (Complex.measurable_im.comp hVind) hρ0 hm20 hB4 hB8 hdomIm
  obtain ⟨hmRe, hmIm⟩ := AzumaProxyN_condExp_stopped_reim d j hS hVint hmean
  -- the numerical bounds
  have hq0 : 0 ≤ Smax * C2 := mul_nonneg hS0 hC20
  have hN0 : 0 ≤ N := by positivity
  have hρq : ρ = (Smax * C2) * Δ / 2 := by simp only [hρ, hR1]; ring
  have hv : 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2) ≤ Δ ^ 2 * P := by
    have hm2sq : m2 ^ 2 ≤ 256 * N ^ 8 := by
      calc m2 ^ 2 ≤ (16 * N ^ 4) ^ 2 := pow_le_pow_left₀ hm20 hm2le 2
        _ = 256 * N ^ 8 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
    calc 2 * ρ ^ 2 * (768 * N ^ 8 + m2 ^ 2)
        ≤ 2 * ρ ^ 2 * (768 * N ^ 8 + 256 * N ^ 8) := by gcongr
      _ = 512 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by rw [hρq]; ring
      _ ≤ 2000 * ((Smax * C2) ^ 2 * Δ ^ 2 * N ^ 8) := by nlinarith
      _ = Δ ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by ring
      _ ≤ Δ ^ 2 * P := by gcongr
  have hw : 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4) ≤ Δ ^ 4 * P ^ 2 := by
    have hm2q : m2 ^ 4 ≤ 65536 * N ^ 16 := by
      calc m2 ^ 4 ≤ (16 * N ^ 4) ^ 4 := pow_le_pow_left₀ hm20 hm2le 4
        _ = 65536 * N ^ 16 := by ring
    have hpos : 0 ≤ (Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16 := by positivity
    have hP0 : 0 ≤ 2000 * (Smax * C2) ^ 2 * N ^ 8 := by positivity
    calc 8 * ρ ^ 4 * (6881280 * N ^ 16 + m2 ^ 4)
        ≤ 8 * ρ ^ 4 * (6881280 * N ^ 16 + 65536 * N ^ 16) := by gcongr
      _ = 3473408 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by rw [hρq]; ring
      _ ≤ 4000000 * ((Smax * C2) ^ 4 * Δ ^ 4 * N ^ 16) := by nlinarith
      _ = Δ ^ 4 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ^ 2 := by ring
      _ ≤ Δ ^ 4 * P ^ 2 := by gcongr
  have hEq : ∀ ω, AzumaProxyN_stopW d E s t K n j σ κ τ ω = {ω | j < τ ω}.indicator Vfull ω :=
    fun ω => rfl
  simp only [hEq]
  refine ⟨hmRe, hmIm, hRe4, hIm4, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hRe2] with ω h
    exact h.trans hv
  · filter_upwards [hIm2] with ω h
    exact h.trans hv
  · exact hRe4'.trans hw
  · exact hIm4'.trans hw

end YFieldsW

section PublicAliases

/-- Public re-export of the private `AzumaProxyN_c0_pos` (`c₀ = √(κ (4 - κ)) / 2 > 0`). -/
theorem AzumaProxyN_c0_pos_pub {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 :=
  AzumaProxyN_c0_pos hκ hE

/-- Public re-export of the private `AzumaProxyN_inv_one_sub_le`. -/
theorem AzumaProxyN_inv_one_sub_le_pub {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
    (hR : N ^ (-1 + τ') ≤ 1 - t) : (1 - u)⁻¹ ≤ N ^ (1 - τ') :=
  AzumaProxyN_inv_one_sub_le hut hN0 hR

/-- Public re-export of the private `AzumaProxyN_etaT_inv_le`. -/
theorem AzumaProxyN_etaT_inv_le_pub {κ E u t τ' N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τ') / (Real.sqrt (κ * (4 - κ)) / 2) :=
  AzumaProxyN_etaT_inv_le hκ hE hut hN0 hR

/-- Public re-export of the private `AzumaProxyN_P_le` (`P ≤ N^{C_P}`, `C_P = 11 + (4k+4)θ`). -/
theorem AzumaProxyN_P_le_pub (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
    (hbig : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤ N) :
    2000 * ((2 * N ^ θ) ^ k * (((k * (k + 1) : ℕ) : ℝ) * N * (N ^ θ / c0) ^ (k + 2))) ^ 2 * N ^ 8
      ≤ N ^ (11 + (4 * k + 4) * θ) :=
  AzumaProxyN_P_le k hc0 hθ hN1 hbig

/-- Public re-export of the private `AzumaProxyN_rowsum_Ugen` (row sums of the `Ugen` kernel). -/
theorem AzumaProxyN_rowsum_Ugen_pub (L : ℕ) [NeZero L] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} [NeZero k] (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (a : Fin k → Z2 L) :
    ∑ b : Fin k → Z2 L, ‖∏ i : Fin k,
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k :=
  AzumaProxyN_rowsum_Ugen L hL hE σ hv0 hv1 hw0 hw1 a

end PublicAliases

end RBM.Ind

end
