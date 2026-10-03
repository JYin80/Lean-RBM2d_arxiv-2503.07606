/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.JakKernel

/-!
# The deterministic pair kernel layer of `(uywy7723r3rf)`

Paper: arXiv:2503.07606, the display `(uywy7723r3rf)`.  For a Hermitian matrix `H` of size
`N = (WL)²`, per site `y`, this file bounds the weighted `y`-term of `L₂`,
`(∏_{j∈s} Im m(w_j)) |∑_x (G₁²)_{xy} S°_{xy} (G₂²)_{yx}|`
(the integrand of the statement `Uyw`), pointwise in the sample:

* `blockM2`, the pair moment `M_{y,α,β}` (the five-block average of the pair QUE quantities
  `N ψ_β^*(E_a - N⁻¹)ψ_α`); on the diagonal it is `blockM`, and
  `M_{y,α,β} = N ∑_x ψ_α(x) ψ_β(x)^* S°_{xy}` (`blockM2_eq`);
* the exact spectral expansion of the `y`-term (`green_spectral_identity_blockM2`);
* the union bound from the failure event `queBadMat` over the five blocks
  (`measure_bad2_le_of_queBadMat`);
* the bound on the single-scale grid event with the window bound `|M_{y,α,β}| ≤ θ` off the
  blocks flagged `Bad` (`uyw_pointwise_good`), and the crude bound valid for every matrix
  (`uyw_pointwise_crude`).

Conventions (as in `JakSpectral.lean` and `JakKernel.lean`, `d = 2`): the index set is `Idx L W`;
the matrix size is `(W L)²`; `S° = Scirc`; the QUE blocks are the five blocks `a₀ + sbSupport L`
with the factor `1/5`; the Stieltjes transform is `stieltjesN`; the grid event is `jakGridGood`;
the weights are `‖Spaper‖ + N⁻¹` with the row sum `sum_Spaper_row`
(`∑_x (|S_{xy}| + N⁻¹) = 2`); the statements are per site `y` and per `(σ₁, σ₂)`.

This file proves only deterministic implications; the only probability statement is the union
bound `measure_bad2_le_of_queBadMat` from a hypothesised `queBadMat` bound.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## Generic index type: eigenvector normalisations and Stieltjes helpers -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1`. -/
private theorem UywKernel_sum_sq_norm_row {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
    ∑ l, ‖hH.eigenvectorBasis l x‖ ^ 2 = 1 := by
  have hUU' : (hH.eigenvectorUnitary : Matrix n n ℂ) *
      star (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self _
  have h := congrArg (fun M : Matrix n n ℂ => M x x) hUU'
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    IsHermitian.eigenvectorUnitary_apply, RCLike.star_def] at h
  have h2 : ∑ l, ((‖hH.eigenvectorBasis l x‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

/-- Eigenvectors are normalised: `∑_p |ψ_k(p)|² = 1`. -/
private theorem UywKernel_sum_sq_norm_col {H : Matrix n n ℂ} (hH : H.IsHermitian) (k : n) :
    ∑ p, ‖hH.eigenvectorBasis k p‖ ^ 2 = 1 := by
  have h := hH.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- For a finite Hermitian matrix, `Im m(E + iη) = |n|⁻¹ ∑ₗ η / ((λₗ-E)²+η²)` for positive `η`. -/
private theorem UywKernel_stieltjesN_im_eq (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ)
    (hη : 0 < η) :
    (stieltjesN H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
  let U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  let d : n → ℂ := fun l => ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))⁻¹
  have hz (l : n) : (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro h
    have him := congrArg Complex.im h
    have : 0 = η := by simpa using him
    exact (ne_of_gt hη) this.symm
  have hgreen : RBM.green H (E + η * Complex.I) = U * diagonal d * star U := by
    exact RBM.green_eq_spectral hH hz
  have htrace : (RBM.green H (E + η * Complex.I)).trace = ∑ l : n, d l := by
    rw [hgreen]
    calc
      (U * diagonal d * star U).trace = (diagonal d * (star U * U)).trace := by
        calc
          (U * diagonal d * star U).trace = (U * (diagonal d * star U)).trace := by
            rw [Matrix.mul_assoc]
          _ = ((diagonal d * star U) * U).trace := by rw [Matrix.trace_mul_comm]
          _ = (diagonal d * (star U * U)).trace := by rw [Matrix.mul_assoc]
      _ = (diagonal d).trace := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]
      _ = ∑ l : n, d l := Matrix.trace_diagonal d
  have himag (l : n) : (d l).im = η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
    have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)) =
        (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp
      ring
    have hi : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
    simp only [d, Complex.inv_im, hi, hn]
    ring
  rw [stieltjesN, htrace]
  rw [Complex.mul_im]
  simp [Complex.im_sum, himag]

/-- Monotonicity used between (2.27) and (2.28): `η Im m(E+iη)` is nondecreasing in `η`. -/
private theorem UywKernel_stieltjesN_eta_mul_im_mono (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ηTilde : ℝ) (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjesN H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjesN H (E + ηTilde * Complex.I)).im := by
  have hformula := UywKernel_stieltjesN_im_eq H hH E η hη
  have hformulaT := UywKernel_stieltjesN_im_eq H hH E ηTilde (by linarith)
  rw [hformula, hformulaT]
  have hterm (l : n) :
      η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) ≤
        ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
    let x := (hH.eigenvalues l - E) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hy : 0 < x + η ^ 2 := by positivity
    have hηT : 0 < ηTilde := lt_of_lt_of_le hη hηTilde
    have hyt : 0 < x + ηTilde ^ 2 := by positivity
    have hsquares : η ^ 2 ≤ ηTilde ^ 2 := by nlinarith [sq_nonneg (ηTilde - η)]
    have hfrac : η ^ 2 / (x + η ^ 2) ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := by
      rw [div_le_div_iff₀ hy hyt]
      have hdiff : 0 ≤ ηTilde ^ 2 - η ^ 2 := by linarith
      nlinarith [mul_nonneg hx hdiff]
    calc
      η * (η / (x + η ^ 2)) = η ^ 2 / (x + η ^ 2) := by field_simp
      _ ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := hfrac
      _ = ηTilde * (ηTilde / (x + ηTilde ^ 2)) := by field_simp
  have hc : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  calc
    η * ((Fintype.card n : ℝ)⁻¹ * ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        = (Fintype.card n : ℝ)⁻¹ *
            ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
          calc
            η * ((Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
                = η * ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by rw [Finset.mul_sum]
            _ = ∑ l : n, η * ((Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by rw [Finset.mul_sum]
            _ = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = (Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
                      rw [Finset.mul_sum]
    _ ≤ (Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun l _ => hterm l) hc
    _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          calc
            (Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))
                = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      rw [Finset.mul_sum]
            _ = ∑ l : n, ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
                      rw [Finset.mul_sum, Finset.mul_sum]

/-- The zero-radius grid is the single energy `E₀`: a bound on every `Im G_xx(E₀ + iη)` bounds
`Im m(E₀ + iη)`. -/
private theorem UywKernel_gridGood_zero_stieltjes [Nonempty n] {H : Matrix n n ℂ} {η Cb E₀ : ℝ}
    (hG : jakGridGood H η Cb E₀ 0) :
    (stieltjesN H ((E₀ : ℂ) + η * Complex.I)).im ≤ Cb := by
  have hx : ∀ x : n, (RBM.green H ((E₀ : ℂ) + η * Complex.I) x x).im ≤ Cb := by
    intro x
    have := hG 0 (by simp) x
    simpa using this
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htr : (stieltjesN H ((E₀ : ℂ) + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ x : n, (RBM.green H ((E₀ : ℂ) + η * Complex.I) x x).im := by
    rw [stieltjesN, Matrix.trace, Complex.mul_im, Complex.im_sum, Complex.re_sum]
    have h1 : ((Fintype.card n : ℂ)⁻¹).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    have h2 : ((Fintype.card n : ℂ)⁻¹).re = (Fintype.card n : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [h1, h2]
    simp [Matrix.diag]
  rw [htr]
  calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _x : n, Cb := by
        gcongr with x; exact hx x
    _ = Cb := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-! ## Dyadic helpers -/

/-- Dyadic majorant: for `f` antitone and nonnegative on `(0,∞)`, `ρ < d ≤ 2^K ρ` gives
`f d ≤ ∑_{k<K} 1_{d ≤ 2^{k+1}ρ} f(2^k ρ)`. -/
private theorem UywKernel_dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
    (hf0 : ∀ a, 0 < a → 0 ≤ f a) {ρ d : ℝ} (hρ : 0 < ρ) :
    ∀ K : ℕ, ρ < d → d ≤ 2 ^ K * ρ →
      f d ≤ ∑ k ∈ Finset.range K, (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) := by
  intro K
  induction K with
  | zero => intro h1 h2; simp at h2; linarith
  | succ K ih =>
    intro h1 h2
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ ∑ k ∈ Finset.range K,
        (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) :=
      Finset.sum_nonneg fun k _ => by
        split_ifs <;> first | exact hf0 _ (by positivity) | exact le_rfl
    by_cases hd : d ≤ 2 ^ K * ρ
    · have := ih h1 hd
      have hlast : 0 ≤ (if d ≤ 2 ^ (K + 1) * ρ then f (2 ^ K * ρ) else 0) := by
        split_ifs; exact hf0 _ (by positivity)
      linarith
    · push Not at hd
      simp only [h2, ite_true]
      have := hf (2 ^ K * ρ) d (by positivity) hd.le
      linarith

private theorem UywKernel_geom_half_sum_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h
/-! ## Off-diagonal entries of `G²` in the eigenbasis -/

private theorem UywKernel_eigenvalues_ne_of_im_ne {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) : ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

private theorem UywKernel_im_gsig_ne {z : ℂ} (hη : 0 < z.im) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simp [hη.ne']

/-- General (off-diagonal) entries of the squared resolvent. -/
private theorem UywKernel_green_sq_apply {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x y : n) :
    (RBM.green H w ^ 2) x y =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hG : RBM.green H w = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using RBM.green_eq_spectral hH hw
  have hG2 : RBM.green H w ^ 2 = U * diagonal (fun α => d α * d α) * star U := by
    rw [hG]
    simp only [pow_two]
    calc
      (U * diagonal d * star U) * (U * diagonal d * star U) =
          U * diagonal d * (star U * U) * diagonal d * star U := by noncomm_ring
      _ = U * diagonal d * 1 * diagonal d * star U := by rw [hUU]
      _ = U * (diagonal d * diagonal d) * star U := by
        simp only [mul_one]
        rw [← Matrix.mul_assoc U (diagonal d) (diagonal d)]
      _ = U * diagonal (fun α => d α * d α) * star U := by
        rw [diagonal_mul_diagonal]
  rw [hG2, mul_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_diagonal, star_apply]
  change ((hH.eigenvectorUnitary : Matrix n n ℂ) x α * (d α * d α) *
      star ((hH.eigenvectorUnitary : Matrix n n ℂ) y α)) = _
  simp only [IsHermitian.eigenvectorUnitary_apply]
  ring

/-- General (off-diagonal) entries of `Gsig²` in the eigenbasis. -/
private theorem UywKernel_Gsig_sq_apply {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (x y : n) :
    (Gsig H z σ ^ 2) x y =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  have heig := UywKernel_eigenvalues_ne_of_im_ne hH (UywKernel_im_gsig_ne hη σ)
  simpa [Gsig, spectralGsigPole, spectralPole] using UywKernel_green_sq_apply hH heig x y

/-! ## Pole bounds (generic index type) -/

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem UywKernel_pole_norm_eq (u : ℂ) (α : n) :
    ‖spectralPole hH u α‖ = ‖(hH.eigenvalues α : ℂ) - u‖⁻¹ := by
  rw [spectralPole, norm_inv]

private theorem UywKernel_pole_norm_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ≤ u.im⁻¹ := by
  rw [UywKernel_pole_norm_eq]
  have h : u.im ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - u)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hη] at this
  exact inv_anti₀ hη h

private theorem UywKernel_pole_norm_le_inv_dist {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ≤ |hH.eigenvalues α - u.re|⁻¹ := by
  rw [UywKernel_pole_norm_eq]
  have h : |hH.eigenvalues α - u.re| ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_re_le_norm ((hH.eigenvalues α : ℂ) - u)
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  exact inv_anti₀ hd h

private theorem UywKernel_pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [UywKernel_pole_norm_eq, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem UywKernel_pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (UywKernel_pole_norm_le_inv_dist hH α hd) 2

include hH in
/-- Crude bound `Im m(w) ≤ 1/Im w`, and `Im m(w) ≥ 0`. -/
private theorem UywKernel_stieltjesN_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
    0 ≤ (stieltjesN H w).im ∧ (stieltjesN H w).im ≤ w.im⁻¹ := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hf := UywKernel_stieltjesN_im_eq H hH w.re w.im hη
  rw [← hw] at hf
  rw [hf]
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ l : n, w.im / ((hH.eigenvalues l - w.re) ^ 2 + w.im ^ 2) ≤ w.im⁻¹ := by
    intro l
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (hH.eigenvalues l - w.re)]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => by positivity)
  · calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _l : n, w.im⁻¹ := by
          gcongr with l; exact hterm l
      _ = w.im⁻¹ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

include hH in
/-- `Im m(w) ≤ (η̃/Im w) Cb` from the zero-radius grid at `Re w` (monotonicity in `η`). -/
private theorem UywKernel_stieltjesN_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im)
    {ηt Cb : ℝ} (hηη : w.im ≤ ηt) (hG : jakGridGood H ηt Cb w.re 0) :
    (stieltjesN H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := UywKernel_stieltjesN_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := UywKernel_gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)
private theorem UywKernel_pole_norm_sq_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (u.im⁻¹) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (UywKernel_pole_norm_le_inv_im hH hη α) 2

/-- **The `Q` factor.** `∑_α |p_α(u)|² |u_α(z)|² ≤ (η̃/η²) Cb` from the zero-radius grid at `Re u`.
-/
private theorem UywKernel_sum_pole_sq_mass_le_of_grid {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hG : jakGridGood H ηt Cb u.re 0) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ ηt / u.im ^ 2 * Cb := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hGz : (RBM.green H ((u.re : ℂ) + ηt * Complex.I) z z).im ≤ Cb := by
    have := hG 0 (by simp) z
    simpa using this
  rw [RBM.im_green_apply_self hH u.re hηt.ne' z] at hGz
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [UywKernel_pole_norm_sq_eq, Complex.normSq_eq_norm_sq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    set v := ‖hH.eigenvectorBasis α z‖ ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hv : 0 ≤ v := by positivity
    rw [show ηt / u.im ^ 2 * (ηt * v / (x + ηt ^ 2)) = ηt ^ 2 * v / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    have h3 : u.im ^ 2 * (x + ηt ^ 2) ≤ ηt ^ 2 * (x + u.im ^ 2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hv]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Crude `Q` factor: `∑_α |p_α(u)|² |u_α(z)|² ≤ (Im u)⁻²`. -/
private theorem UywKernel_sum_pole_sq_mass_le_crude {u : ℂ} (hη : 0 < u.im) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ (u.im⁻¹) ^ 2 := by
  calc _ ≤ ∑ α, (u.im⁻¹) ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 :=
        Finset.sum_le_sum fun α _ =>
          mul_le_mul_of_nonneg_right (UywKernel_pole_norm_sq_le_inv_im hH hη α) (by positivity)
    _ = (u.im⁻¹) ^ 2 := by rw [← Finset.mul_sum, UywKernel_sum_sq_norm_row hH z, mul_one]

/-- `∑_α |p_α|² = ∑_z ∑_α |p_α|² |u_α(z)|²` (completeness of each eigenvector). -/
private theorem UywKernel_sum_pole_sq_eq (u : ℂ) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 =
      ∑ z : n, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, UywKernel_sum_sq_norm_col hH α, mul_one]

/-- **The `Q^out` factor.** Out-of-window part (`|λ_α - Re u| > w'`) of `∑_α |p_α|² |u_α(z)|²`, from
the grids of radii `2^k w'`, `k ≤ K'` (dyadic shells and the covering lemma), and completeness
beyond `2^{K'} w'`. -/
private theorem UywKernel_sum_pole_sq_mass_out_le {u : ℂ} {ηt Cb w' : ℝ} (hηt : 0 < ηt)
    (hCb : 0 ≤ Cb)
    (hw' : 0 < w') (K' : ℕ) (hG : ∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w')) (z : n) :
    ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤
      Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ := by
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ z‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  have hpt : ∀ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) ≤
      ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ w'
    · simp only [h1, ite_true]; linarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false]
      have hdpos : 0 < dd γ := lt_trans hw' h1
      have hpd := mul_le_mul_of_nonneg_right
        (UywKernel_pole_norm_sq_le_inv_dist_sq hH γ hdpos) (hv0 γ)
      by_cases h2 : dd γ ≤ 2 ^ K' * w'
      · have hdy := UywKernel_dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have hdy' : (dd γ ^ 2)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) := by
          calc (dd γ ^ 2)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K',
                (if dd γ ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ ^ 2)⁻¹ * v γ ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right
            (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)) (hv0 γ)
        linarith
  have hmass : ∀ r : ℝ, 0 ≤ r → jakGridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact sum_mass_window_le_of_im_green_le hH hηt hr hCb u.re z fun j hj => hGr j hj z
  have hmk : ∀ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) ≤
        Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * w') (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ ((2 ^ k * w') ^ 2)⁻¹ * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ +
            4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ + 4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hsumv : ∑ γ, v γ = 1 := UywKernel_sum_sq_norm_row hH z
  calc ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2)
      = ∑ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) := rfl
    _ ≤ ∑ γ, (∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) +
          ((2 ^ K' * w') ^ 2)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range K', Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ * 1 := by
        rw [hsumv]
        have := Finset.sum_le_sum hmk
        linarith
    _ = Cb * (4 / w' + 4 * ηt / w' ^ 2) * ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ := by rw [Finset.mul_sum, mul_one]
    _ ≤ Cb * (4 / w' + 4 * ηt / w' ^ 2) * 2 + ((2 ^ K' * w') ^ 2)⁻¹ := by
        gcongr; exact UywKernel_geom_half_sum_le K'
    _ = _ := by ring

end Generic

/-! ## Pair combinatorics (abstract, index-free) -/

section Pair

variable {ι : Type*} [Fintype ι]

/-- AM–GM on a (restricted) one-index sum: `∑_{α∉W} P_α a_α(x) a_α(y) ≤ o` whenever
`∑_{α∉W} P_α a_α(z)² ≤ o` for every `z`. -/
private theorem UywKernel_amgm_sum (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop) [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) {o : ℝ}
    (ho : ∀ z, ∑ α, (if W α then 0 else P α * a α z ^ 2) ≤ o) (x y : ι) :
    ∑ α, (if W α then 0 else P α * (a α x * a α y)) ≤ o := by
  have hpt : ∀ α, (if W α then 0 else P α * (a α x * a α y)) ≤
      (1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2) := by
    intro α
    split_ifs
    · simp
    · have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α x) (a α y)) (hP α)
      nlinarith
  calc _ ≤ ∑ α, ((1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2)) := Finset.sum_le_sum fun α _ => hpt α
    _ = (1 / 2) * ∑ α, (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * ∑ α, (if W α then 0 else P α * a α y ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 / 2) * o + (1 / 2) * o := by gcongr <;> [exact ho x; exact ho y]
    _ = o := by ring

private theorem UywKernel_sum_ite_nonneg (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop)
    [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) (ha : ∀ α x, 0 ≤ a α x) (x y : ι) :
    0 ≤ ∑ α, (if W α then 0 else P α * (a α x * a α y)) :=
  Finset.sum_nonneg fun α _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hP α) (mul_nonneg (ha α x) (ha α y))

/-- The "rest" sum factorizes: `∑_{α∉W₁} ∑_β P₁P₂ (N∑_x s_x a_α(x)a_β(x)) a_α(y)a_β(y)
= N ∑_x s_x F₁^{out}(x) F₂(x)`. -/
private theorem UywKernel_rest_eq (P₁ P₂ : ι → ℝ) (a : ι → ι → ℝ) (s : ι → ℝ) (y : ι) (Nn : ℝ)
    (W₁ : ι → Prop) [DecidablePred W₁] :
    ∑ α, ∑ β, (if W₁ α then 0 else
        P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
        ∑ β, P₂ β * (a β x * a β y)) := by
  have hpt : ∀ α β, (if W₁ α then 0 else
      P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      ∑ x, Nn * (s x * ((if W₁ α then 0 else P₁ α * (a α x * a α y)) *
        (P₂ β * (a β x * a β y)))) := by
    intro α β
    split_ifs
    · simp
    · simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
  simp_rw [hpt]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]

/-- **Pair combinatorics.** Window pairs (`W₁ × W₂`, where `M ≤ θ`) plus the rest (where
`M ≤ N ∑_x s_x a_α(x) a_β(x)`), each reduced by AM–GM to the one-index bounds `q_i`, `o_i`
(out-of-window) and `S_i` (total weight). -/
private theorem UywKernel_pair_abstract (P₁ P₂ : ι → ℝ) (a M : ι → ι → ℝ) (s : ι → ℝ) (y : ι)
    {Nn θ q₁ q₂ o₁ o₂ S₁ S₂ : ℝ} (W₁ W₂ : ι → Prop) [DecidablePred W₁] [DecidablePred W₂]
    (hP₁ : ∀ α, 0 ≤ P₁ α) (hP₂ : ∀ α, 0 ≤ P₂ α) (ha : ∀ α x, 0 ≤ a α x)
    (hs : ∀ x, 0 ≤ s x) (hsum : ∑ x, s x ≤ 2) (hN : 0 ≤ Nn) (hθ : 0 ≤ θ)
    (hM : ∀ α β, M α β ≤ Nn * ∑ x, s x * (a α x * a β x))
    (hMw : ∀ α β, W₁ α → W₂ β → M α β ≤ θ)
    (hq₁ : ∀ z, ∑ α, P₁ α * a α z ^ 2 ≤ q₁) (hq₂ : ∀ z, ∑ α, P₂ α * a α z ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if W₁ α then 0 else P₁ α * a α z ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if W₂ α then 0 else P₂ α * a α z ^ 2) ≤ o₂)
    (hS₁ : ∑ α, P₁ α ≤ S₁) (hS₂ : ∑ α, P₂ α ≤ S₂) :
    ∑ α, ∑ β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) + 2 * Nn * (o₁ * q₂ + q₁ * o₂) := by
  classical
  set X : ι → ι → ℝ := fun α β =>
    P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y) with hX
  have hX0 : ∀ α β, 0 ≤ X α β := fun α β => by
    have : 0 ≤ ∑ x, s x * (a α x * a β x) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hs x) (mul_nonneg (ha α x) (ha β x))
    have := hP₁ α; have := hP₂ β; have := ha α y; have := ha β y
    simp only [X]; positivity
  have hpt : ∀ α β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β) := by
    intro α β
    have hc : 0 ≤ P₁ α * P₂ β * (a α y * a β y) :=
      mul_nonneg (mul_nonneg (hP₁ α) (hP₂ β)) (mul_nonneg (ha α y) (ha β y))
    have hθt : 0 ≤ θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) := by
      have := hP₁ α; have := hP₂ β; positivity
    have hrest : P₁ α * P₂ β * M α β * (a α y * a β y) ≤ X α β := by
      have := mul_le_mul_of_nonneg_left (hM α β) hc
      simp only [X]; nlinarith
    by_cases h1 : W₁ α <;> by_cases h2 : W₂ β
    · simp only [h1, h2, ite_true, add_zero]
      have hw := mul_le_mul_of_nonneg_left (hMw α β h1 h2) hc
      have hag := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α y) (a β y))
        (mul_nonneg (mul_nonneg hθ (hP₁ α)) (hP₂ β))
      nlinarith
    · simp only [h1, h2, ite_true, ite_false]; linarith
    · simp only [h1, h2, ite_true, ite_false, add_zero]; linarith
    · simp only [h1, h2, ite_false]; linarith [hX0 α β]
  -- the three sums
  have hq₁0 : 0 ≤ q₁ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₁ α; positivity) (hq₁ y)
  have hq₂0 : 0 ≤ q₂ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₂ α; positivity) (hq₂ y)
  have hG₁ : ∀ x, ∑ α, P₁ α * (a α x * a α y) ≤ q₁ := fun x => by
    simpa using UywKernel_amgm_sum P₁ a (fun _ => False) hP₁ (o := q₁) (by simpa using hq₁) x y
  have hG₂ : ∀ x, ∑ α, P₂ α * (a α x * a α y) ≤ q₂ := fun x => by
    simpa using UywKernel_amgm_sum P₂ a (fun _ => False) hP₂ (o := q₂) (by simpa using hq₂) x y
  have hG₁0 : ∀ x, 0 ≤ ∑ α, P₁ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₁ α) (mul_nonneg (ha α x) (ha α y))
  have hG₂0 : ∀ x, 0 ≤ ∑ α, P₂ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₂ α) (mul_nonneg (ha α x) (ha α y))
  have hS1 : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) := by
    have e : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) =
        θ / 2 * ((∑ α, P₁ α * a α y ^ 2) * (∑ β, P₂ β) +
          (∑ α, P₁ α) * ∑ β, P₂ β * a β y ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    rw [e]
    have hP₂s : 0 ≤ ∑ β, P₂ β := Finset.sum_nonneg fun β _ => hP₂ β
    have hP₁s : 0 ≤ ∑ α, P₁ α := Finset.sum_nonneg fun α _ => hP₁ α
    have hQ₂0 : 0 ≤ ∑ β, P₂ β * a β y ^ 2 := Finset.sum_nonneg fun β _ => by
      have := hP₂ β; positivity
    have hS₁0 : 0 ≤ S₁ := hP₁s.trans hS₁
    gcongr
    · exact hq₁ y
    · exact hq₂ y
  have hS2 : ∑ α, ∑ β, (if W₁ α then 0 else X α β) ≤ 2 * Nn * (o₁ * q₂) := by
    rw [UywKernel_rest_eq P₁ P₂ a s y Nn W₁]
    have hF : ∀ x, ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) ≤ o₁ :=
      fun x => UywKernel_amgm_sum P₁ a W₁ hP₁ ho₁ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) :=
      fun x => UywKernel_sum_ite_nonneg P₁ a W₁ hP₁ ha x y
    have ho₁0 : 0 ≤ o₁ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
          ∑ β, P₂ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₁ * q₂) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₂ x | exact hG₂0 x
      _ = Nn * (∑ x, s x) * (o₁ * q₂) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₁ * q₂) := by gcongr
      _ = _ := by ring
  have hS3 : ∑ α, ∑ β, (if W₂ β then 0 else X α β) ≤ 2 * Nn * (q₁ * o₂) := by
    have e : ∀ α β, (if W₂ β then 0 else X α β) = (if W₂ β then 0 else
        P₂ β * P₁ α * (Nn * ∑ x, s x * (a β x * a α x)) * (a β y * a α y)) := by
      intro α β
      simp only [X]
      rw [show ∑ x, s x * (a β x * a α x) = ∑ x, s x * (a α x * a β x) from
        Finset.sum_congr rfl fun x _ => by ring]
      split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_comm, UywKernel_rest_eq P₂ P₁ a s y Nn W₂]
    have hF : ∀ x, ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) ≤ o₂ :=
      fun x => UywKernel_amgm_sum P₂ a W₂ hP₂ ho₂ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) :=
      fun x => UywKernel_sum_ite_nonneg P₂ a W₂ hP₂ ha x y
    have ho₂0 : 0 ≤ o₂ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y))) *
          ∑ β, P₁ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₂ * q₁) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₁ x | exact hG₁0 x
      _ = Nn * (∑ x, s x) * (o₂ * q₁) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₂ * q₁) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ α, ∑ β, (θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β)) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hpt α β
    _ = ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        ∑ α, ∑ β, (if W₁ α then 0 else X α β) + ∑ α, ∑ β, (if W₂ β then 0 else X α β) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

end Pair
/-! ## The covariance profile (d = 2) -/

section Aux

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem UywKernel_card_idx : Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp only [Idx, Z2, Fintype.card_prod, ZMod.card]
  ring

private theorem UywKernel_N_pos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) 2

omit [NeZero L] [NeZero W] in
private theorem UywKernel_Spaper_eq_norm (x y : Idx L W) :
    Spaper L W x y = ((‖Spaper L W x y‖ : ℝ) : ℂ) := by
  rw [Spaper_indicator]
  split_ifs
  · rw [norm_mul, norm_inv, norm_pow, norm_inv]
    simp
  · simp

omit [NeZero L] in
private theorem UywKernel_Spaper_symm (x y : Idx L W) : Spaper L W x y = Spaper L W y x := by
  have := congrFun (congrFun (Spaper_transpose L W) y) x
  simpa using this

/-- Column sums of the covariance: `∑_x |S_{xy}| = 1`, for `L ≥ 3`. -/
private theorem UywKernel_sum_norm_Spaper (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, ‖Spaper L W x y‖ = 1 := by
  have h : ((∑ x : Idx L W, ‖Spaper L W x y‖ : ℝ) : ℂ) = 1 := by
    push_cast
    calc ∑ x : Idx L W, ((‖Spaper L W x y‖ : ℝ) : ℂ) = ∑ x : Idx L W, Spaper L W x y :=
          Finset.sum_congr rfl fun x _ => (UywKernel_Spaper_eq_norm x y).symm
      _ = ∑ x : Idx L W, Spaper L W y x :=
          Finset.sum_congr rfl fun x _ => UywKernel_Spaper_symm x y
      _ = 1 := sum_Spaper_row L W hL y
  exact_mod_cast h

omit [NeZero L] [NeZero W] in
private theorem UywKernel_Scirc_norm_le (x y : Idx L W) :
    ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ := by
  calc ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + ‖(((W * L) ^ 2 : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = _ := by rw [norm_inv, Complex.norm_natCast]

/-- The weight sum: `∑_x (|S_{xy}| + N⁻¹) = 2` (`sum_Spaper_row`). -/
private theorem UywKernel_profile_weight_sum (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, UywKernel_sum_norm_Spaper hL y]
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt UywKernel_N_pos
  have hconst : ∑ _x : Idx L W, (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, UywKernel_card_idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num
end Aux

/-! ## The pair moment `M_{y,α,β}` (d = 2) -/

section Block

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `M_{y,α,β}` for `y ∈ I_{a₀}`: the average
of the five pair QUE quantities `N ψ_β^*(E_a - N⁻¹)ψ_α` over the blocks `a ∈ a₀ + sbSupport L`.
At `α = β` it is `blockM`. -/
def blockM2 {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (a0 : Z2 L)
    (α β : Idx L W) : ℂ :=
  (((W * L) ^ 2 : ℕ) : ℂ) * ((1 / 5 : ℂ) * ∑ u ∈ sbSupport L,
    star (fun x => hH.eigenvectorBasis β x) ⬝ᵥ
      ((Epaper L W (a0 + u) -
          ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ
        (fun x => hH.eigenvectorBasis α x)))

/-- The pair overlap `ψ^*(E_a - c)φ` of a diagonal block matrix, entrywise. -/
private theorem UywKernel_overlap (a : Z2 L) (c : ℂ) (ψ φ : Idx L W → ℂ) :
    star ψ ⬝ᵥ ((Epaper L W a - c • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ φ) =
      ∑ x, (star (ψ x) * φ x) *
        ((W : ℂ)⁻¹ ^ 2 * (if x ∈ Iblk L W a then 1 else 0) - c) := by
  have hE : Epaper L W a - c • (1 : Matrix (Idx L W) (Idx L W) ℂ) =
      Matrix.diagonal (fun x => (W : ℂ)⁻¹ ^ 2 * (if x ∈ Iblk L W a then 1 else 0) - c) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Epaper]
    · simp [Epaper, h]
  rw [hE]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [NeZero L] in
/-- The covariance `S_{xy}` at a site `y` of block `a0`: the five-point indicator. -/
private theorem UywKernel_Spaper (x y : Idx L W) :
    Spaper L W x y =
      if (split L W x).1 - siteBlock L W y ∈ sbSupport L
      then (5 : ℂ)⁻¹ * (W : ℂ)⁻¹ ^ 2 else 0 :=
  Spaper_indicator L W x y

variable {L W}

/-- `M_{y,α,β} = N ∑_x ψ_α(x) ψ_β(x)^* S°_{xy}`; needs `L ≥ 3` for the count `|sbSupport L| = 5`. -/
theorem blockM2_eq (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (y α β : Idx L W) :
    blockM2 L W hH (siteBlock L W y) α β =
      (((W * L) ^ 2 : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) * Scirc L W x y := by
  set a0 : Z2 L := siteBlock L W y with ha0
  set c : ℂ := ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ with hc
  unfold blockM2
  simp only [UywKernel_overlap]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : ∑ u ∈ sbSupport L,
      (star (hH.eigenvectorBasis β x) * hH.eigenvectorBasis α x) *
        ((W : ℂ)⁻¹ ^ 2 * (if x ∈ Iblk L W (a0 + u) then 1 else 0) - c) =
      (star (hH.eigenvectorBasis β x) * hH.eigenvectorBasis α x) * (
        (W : ℂ)⁻¹ ^ 2 * (if (split L W x).1 - a0 ∈ sbSupport L then 1 else 0) - 5 * c) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      card_sbSupport L hL]
    have : ∀ u ∈ sbSupport L, (if x ∈ Iblk L W (a0 + u) then (1 : ℂ) else 0) =
        if u = (split L W x).1 - a0 then 1 else 0 := by
      intro u _
      have hiff : x ∈ Iblk L W (a0 + u) ↔ u = (split L W x).1 - a0 := by
        rw [mem_Iblk, eq_sub_iff_add_eq, add_comm u a0, eq_comm]
      simp only [hiff]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp
  rw [hx, Scirc, UywKernel_Spaper]
  split_ifs <;> ring

end Block

/-! ## The exact spectral expansion of the `y`-term of `L₂` -/

section BlockGreen

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Exact eigenbasis expansion of the `y`-term before substituting `blockM2_eq`. -/
private theorem UywKernel_sum_variance2 {Hm : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : Hm.IsHermitian) (y : Idx L W) (z₁ z₂ : ℂ) (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im)
    (σ₁ σ₂ : Bool) :
    (∑ x : Idx L W, (Gsig Hm z₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig Hm z₂ σ₂ ^ 2) y x) =
      ∑ α : Idx L W, ∑ β : Idx L W,
        (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
          (star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y) *
          ∑ x : Idx L W, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) *
            Scirc L W x y := by
  set S0 : Idx L W → ℂ := fun x => Scirc L W x y with hS0
  set A : Idx L W → Idx L W → ℂ := fun γ x => hH.eigenvectorBasis γ x with hA
  calc
    (∑ x : Idx L W, (Gsig Hm z₁ σ₁ ^ 2) x y * S0 x * (Gsig Hm z₂ σ₂ ^ 2) y x) =
        ∑ x : Idx L W, (∑ α : Idx L W, spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
            (A α x * star (A α y))) * S0 x *
          ∑ β : Idx L W, spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β *
            (A β y * star (A β x)) := by
          congr 1
          funext x
          rw [UywKernel_Gsig_sq_apply hH hη₁ σ₁ x y, UywKernel_Gsig_sq_apply hH hη₂ σ₂ y x]
    _ = ∑ α : Idx L W, ∑ β : Idx L W,
          (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
            (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            (star (A α y) * A β y) *
            ∑ x : Idx L W, (A α x * star (A β x)) * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- The exact spectral expansion of the `y`-term of `L₂` (the integrand of `Uyw`), with `M_{y,α,β}`
substituted from `blockM2_eq`. -/
theorem green_spectral_identity_blockM2 {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (y : Idx L W) (z₁ z₂ : ℂ)
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx L W, (Gsig H z₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H z₂ σ₂ ^ 2) y x) =
      ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ * ∑ α : Idx L W, ∑ β : Idx L W,
        spectralGsigPole hH z₁ σ₁ α ^ 2 * spectralGsigPole hH z₂ σ₂ β ^ 2 *
          blockM2 L W hH (siteBlock L W y) α β *
            star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y := by
  have hN : (((W * L) ^ 2 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero 2 (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  rw [UywKernel_sum_variance2 hH y z₁ z₂ hη₁ hη₂ σ₁ σ₂, eq_inv_mul_iff_mul_eq₀ hN,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [blockM2_eq hL hH y α β, pow_two, pow_two]
  ring

end BlockGreen

/-! ## The pair bad event is rare: the union bound from `queBadMat` -/

section Que

/-- **The pair bad event of `(uywy7723r3rf)` is rare, from QUE**: if the failure event `queBadMat`
of `(Meq:QUE)` at energy `E`
(window `N^{-1-τ} W^{2/3}`, threshold `N^{-τ/6}`) has probability `≤ ε'` for each block `a`, then
for `w` below the window and `N^{-τ/6} ≤ θ²`,
`P(∃ α β, |λ_α - E| ≤ w, |λ_β - E| ≤ w, |M_{a₀,α,β}| ≥ θ) ≤ 5ε'` (union over the at most five
blocks `a₀ + sbSupport L`; `queBadMat` already quantifies a pair `k, k'` of eigenvector indices;
no `3 ≤ L` is needed). -/
theorem measure_bad2_le_of_queBadMat {L W : ℕ} [NeZero L] [NeZero W] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (Hr : Ω → Matrix (Idx L W) (Idx L W) ℂ) (hH : ∀ ω, (Hr ω).IsHermitian)
    (E w τ θ ε' : ℝ)
    (hw : w ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3))
    (hθ : 0 ≤ θ) (hθτ : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-τ / 6) ≤ θ ^ 2) (a0 : Z2 L)
    (hque : ∀ a : Z2 L, P {ω | queBadMat L W ((W * L) ^ 2) τ E a (Hr ω)} ≤
      ENNReal.ofReal ε') :
    P {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ w ∧ |(hH ω).eigenvalues β - E| ≤ w ∧
        θ ≤ ‖blockM2 L W (hH ω) a0 α β‖} ≤ ENNReal.ofReal (5 * ε') := by
  have hcard : (sbSupport L).card ≤ 5 := Finset.card_le_five
  have hne : (sbSupport L).Nonempty := ⟨(0, 0), by simp [sbSupport]⟩
  have hsub : {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ w ∧ |(hH ω).eigenvalues β - E| ≤ w ∧
      θ ≤ ‖blockM2 L W (hH ω) a0 α β‖} ⊆
      ⋃ u ∈ sbSupport L, {ω | queBadMat L W ((W * L) ^ 2) τ E (a0 + u) (Hr ω)} := by
    rintro ω ⟨α, β, hα, hβ, hM⟩
    set q : Z2 L → ℂ := fun a => (((W * L) ^ 2 : ℕ) : ℂ) *
      (star (fun x => (hH ω).eigenvectorBasis β x) ⬝ᵥ
        ((Epaper L W a - ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ
          (fun x => (hH ω).eigenvectorBasis α x))) with hq
    have hMx : blockM2 L W (hH ω) a0 α β = (1 / 5 : ℂ) * ∑ u ∈ sbSupport L, q (a0 + u) := by
      simp only [blockM2, hq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    have hex : ∃ u ∈ sbSupport L, θ ≤ ‖q (a0 + u)‖ := by
      by_contra hno
      push Not at hno
      have h1 : ∑ u ∈ sbSupport L, ‖q (a0 + u)‖ < ∑ _u ∈ sbSupport L, θ :=
        Finset.sum_lt_sum_of_nonempty hne hno
      have h3 : ‖blockM2 L W (hH ω) a0 α β‖ ≤ (1 / 5) * ∑ u ∈ sbSupport L, ‖q (a0 + u)‖ := by
        rw [hMx, norm_mul]
        have : ‖(1 / 5 : ℂ)‖ = 1 / 5 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have h4 : ((sbSupport L).card : ℝ) * θ ≤ 5 * θ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hθ
      linarith
    obtain ⟨u, hu, hqu⟩ := hex
    refine Set.mem_biUnion hu ⟨_, _, isOrthoEigenbasis_eigenvectorBasis (hH ω), β, α,
      (hβ.trans hw), (hα.trans hw), ?_⟩
    exact hθτ.trans (pow_le_pow_left₀ hθ hqu 2)
  calc _ ≤ P (⋃ u ∈ sbSupport L, {ω | queBadMat L W ((W * L) ^ 2) τ E (a0 + u) (Hr ω)}) :=
        measure_mono hsub
    _ ≤ ∑ u ∈ sbSupport L, P {ω | queBadMat L W ((W * L) ^ 2) τ E (a0 + u) (Hr ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ sbSupport L, ENNReal.ofReal ε' := Finset.sum_le_sum fun u _ => hque (a0 + u)
    _ = (sbSupport L).card * ENNReal.ofReal ε' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 * ENNReal.ofReal ε' := by
        gcongr
        exact_mod_cast hcard
    _ = ENNReal.ofReal (5 * ε') := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

end Que

/-! ## The `A_y` factor and the pointwise bounds of the weighted `y`-term -/

section Pointwise

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|M_{y,α,β}| ≤ N ∑_x (|S_{xy}| + N⁻¹) |ψ_α(x)| |ψ_β(x)|`. -/
private theorem UywKernel_norm_blockM2_le (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (y α β : Idx L W) :
    ‖blockM2 L W hH (siteBlock L W y) α β‖ ≤ (((W * L) ^ 2 : ℕ) : ℝ) *
      ∑ x : Idx L W, (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) *
        (‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖) := by
  rw [blockM2_eq hL hH y α β, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, norm_mul, norm_star]
  calc ‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖ * ‖Scirc L W x y‖
      ≤ ‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖ *
          (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (UywKernel_Scirc_norm_le x y) (by positivity)
    _ = _ := by ring

private theorem UywKernel_ite_abs_neg_one (x t : ℝ) : (if |x| ≤ -1 then (0 : ℝ) else t) = t := by
  have h : ¬ |x| ≤ -1 := by linarith [abs_nonneg x]
  simp [h]

/-- **The `A_y` factor.** For a window radius `w'` (take `w' < 0` for no window), with window pairs
bounded by `θ`: `A_y ≤ (θ/2)(q₁ N q₂ + N q₁ q₂) + 2N(o₁q₂ + q₁o₂)`, with
`A_y = ∑_{α,β} |p₁α|²|p₂β|²|M_{y,α,β}||ψ_α(y)||ψ_β(y)|`. -/
private theorem UywKernel_A_le (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (u₁ u₂ : ℂ) (y : Idx L W) {θ q₁ q₂ o₁ o₂ w' : ℝ} (hθ : 0 ≤ θ)
    (hMw : ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' → |hH.eigenvalues β - u₂.re| ≤ w' →
      ‖blockM2 L W hH (siteBlock L W y) α β‖ ≤ θ)
    (hq₁ : ∀ z, ∑ α, ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₁)
    (hq₂ : ∀ z, ∑ α, ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₁.re| ≤ w' then 0 else
      ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₂.re| ≤ w' then 0 else
      ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₂) :
    ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
        ‖blockM2 L W hH (siteBlock L W y) α β‖ *
          (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
      θ / 2 * (q₁ * ((((W * L) ^ 2 : ℕ) : ℝ) * q₂) + ((((W * L) ^ 2 : ℕ) : ℝ) * q₁) * q₂) +
        2 * (((W * L) ^ 2 : ℕ) : ℝ) * (o₁ * q₂ + q₁ * o₂) := by
  have hS : ∀ (u : ℂ) (q : ℝ),
      (∀ z, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q) →
      ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ (((W * L) ^ 2 : ℕ) : ℝ) * q := by
    intro u q hq
    rw [UywKernel_sum_pole_sq_eq hH u]
    calc _ ≤ ∑ _z : Idx L W, q := Finset.sum_le_sum fun z _ => hq z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, UywKernel_card_idx]
  refine UywKernel_pair_abstract (fun α => ‖spectralPole hH u₁ α‖ ^ 2)
    (fun α => ‖spectralPole hH u₂ α‖ ^ 2) (fun γ x => ‖hH.eigenvectorBasis γ x‖)
    (fun α β => ‖blockM2 L W hH (siteBlock L W y) α β‖)
    (fun x => ‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) y
    (fun α => |hH.eigenvalues α - u₁.re| ≤ w') (fun β => |hH.eigenvalues β - u₂.re| ≤ w')
    (fun α => by positivity) (fun α => by positivity) (fun α x => norm_nonneg _)
    (fun x => add_nonneg (norm_nonneg _) (by have := UywKernel_N_pos (L := L) (W := W); positivity))
    (le_of_eq (UywKernel_profile_weight_sum hL y))
    (by have := UywKernel_N_pos (L := L) (W := W); positivity) hθ
    (fun α β => UywKernel_norm_blockM2_le hL hH y α β) (fun α β h1 h2 => hMw α β h1 h2)
    hq₁ hq₂ ho₁ ho₂ (hS u₁ q₁ hq₁) (hS u₂ q₂ hq₂)

/-- The triangle bound for the exact expansion: `‖y-term‖ ≤ N⁻¹ A_y` (the exact expansion together
with `spectralGsigPole_norm_eq_spectralPole`, per site `y` and per sign pair). -/
private theorem UywKernel_norm_yterm_le (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (y : Idx L W) {z₁ z₂ : ℂ} (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im)
    (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx L W, (Gsig H z₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H z₂ σ₂ ^ 2) y x‖ ≤
      (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ * ∑ α, ∑ β, ‖spectralPole hH z₁ α‖ ^ 2 *
        ‖spectralPole hH z₂ β‖ ^ 2 * ‖blockM2 L W hH (siteBlock L W y) α β‖ *
          (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) := by
  rw [green_spectral_identity_blockM2 hL hH y z₁ z₂ hη₁ hη₂ σ₁ σ₂, norm_mul, norm_inv,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_star,
    spectralGsigPole_norm_eq_spectralPole, spectralGsigPole_norm_eq_spectralPole]
  ring

/-- **Pointwise bound on the good event**.  On the single-scale grid event, with the
window bound `|M_{y,α,β}| ≤ θ` off the blocks flagged `Bad`, the weighted `y`-term of `L₂` (the
integrand of `Uyw`) is at most the product of the `Im m` factors times
`N⁻¹ (A_good + 1_{Bad} A_bad)`; `N = (W L)²`, and `σ₁, σ₂`, `y` are fixed. -/
theorem uyw_pointwise_good {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (ηt Cb w' θ Ag Ab : ℝ)
    (hη₁ : 0 < u₁.im) (hη₁' : u₁.im ≤ ηt) (hη₂ : 0 < u₂.im) (hη₂' : u₂.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K' : ℕ)
    (hG1 : ∀ k ≤ K', jakGridGood H ηt Cb u₁.re (2 ^ k * w'))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u₂.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u₁.re 0) (hG4 : jakGridGood H ηt Cb u₂.re 0)
    (hG5 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Z2 L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 L W hH a0 α β‖ ≤ θ)
    (hAg : θ / 2 * ((ηt / u₁.im ^ 2 * Cb) * ((((W * L) ^ 2 : ℕ) : ℝ) * (ηt / u₂.im ^ 2 * Cb)) +
        ((((W * L) ^ 2 : ℕ) : ℝ) * (ηt / u₁.im ^ 2 * Cb)) * (ηt / u₂.im ^ 2 * Cb)) +
      2 * (((W * L) ^ 2 : ℕ) : ℝ) *
        ((Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) * (ηt / u₂.im ^ 2 * Cb) +
          (ηt / u₁.im ^ 2 * Cb) * (Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹)) ≤
      Ag)
    (hAb : 4 * (((W * L) ^ 2 : ℕ) : ℝ) * ((ηt / u₁.im ^ 2 * Cb) * (ηt / u₂.im ^ 2 * Cb)) ≤ Ab)
    (y : Idx L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹ *
          (Ag + (if Bad (siteBlock L W y) then Ab else 0))) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη₁ hη₁'
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := UywKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀
      (fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => UywKernel_stieltjesN_im_le_of_grid hH (hηw j) (hηw' j) (hG5 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  have hq₁ := UywKernel_sum_pole_sq_mass_le_of_grid hH hη₁ hη₁' hG3
  have hq₂ := UywKernel_sum_pole_sq_mass_le_of_grid hH hη₂ hη₂' hG4
  have ho₁ := UywKernel_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG1
  have ho₂ := UywKernel_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG2
  have hq₁0 : 0 ≤ ηt / u₁.im ^ 2 * Cb := by positivity
  have hq₂0 : 0 ≤ ηt / u₂.im ^ 2 * Cb := by positivity
  have hAb0 : 0 ≤ Ab := le_trans (by positivity) hAb
  have hA : ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 L W hH (siteBlock L W y) α β‖ *
        (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        Ag + (if Bad (siteBlock L W y) then Ab else 0) := by
    by_cases hb : Bad (siteBlock L W y)
    · simp only [hb, ite_true]
      -- no window: `w' = -1`
      have h := UywKernel_A_le hL hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
        (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
        hq₁ hq₂ (o₁ := ηt / u₁.im ^ 2 * Cb) (o₂ := ηt / u₂.im ^ 2 * Cb)
        (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₁ z)
        (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₂ z)
      have hAg0 : 0 ≤ Ag := le_trans (by positivity) hAg
      nlinarith
    · simp only [hb, ite_false, add_zero]
      exact (UywKernel_A_le hL hH u₁ u₂ y hθ (hBad _ hb) hq₁ hq₂ ho₁ ho₂).trans hAg
  have hK := UywKernel_norm_yterm_le hL hH y hη₁ hη₂ σ₁ σ₂
  have hK' : ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ ≤
      (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ * (Ag + (if Bad (siteBlock L W y) then Ab else 0)) :=
    hK.trans (mul_le_mul_of_nonneg_left hA (by positivity))
  calc (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- **Crude pointwise bound**, valid for every Hermitian matrix:
`∏ Im m(w_j) · |y-term| ≤ ∏ (Im w_j)⁻¹ · 4 (Im u₁)⁻² (Im u₂)⁻²` (from
`A_y ≤ 4N (Im u₁)⁻²(Im u₂)⁻²`). -/
theorem uyw_pointwise_crude {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hη₁ : 0 < u₁.im) (hη₂ : 0 < u₂.im)
    (hηw : ∀ j, 0 < (w j).im) (y : Idx L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) := by
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := UywKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hq₁ := UywKernel_sum_pole_sq_mass_le_crude hH hη₁
  have hq₂ := UywKernel_sum_pole_sq_mass_le_crude hH hη₂
  have hA : ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 L W hH (siteBlock L W y) α β‖ *
        (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        4 * (((W * L) ^ 2 : ℕ) : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    have h := UywKernel_A_le hL hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
      (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
      hq₁ hq₂ (o₁ := (u₁.im⁻¹) ^ 2) (o₂ := (u₂.im⁻¹) ^ 2)
      (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₁ z)
      (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₂ z)
    nlinarith
  have hK : ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ ≤
      4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    refine (UywKernel_norm_yterm_le hL hH y hη₁ hη₂ σ₁ σ₂).trans ?_
    calc _ ≤ (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ *
          (4 * (((W * L) ^ 2 : ℕ) : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by field_simp
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) *
          ‖∑ x, (Gsig H u₁ σ₁ ^ 2) x y * Scirc L W x y * (Gsig H u₂ σ₂ ^ 2) y x‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK hP0

end Pointwise

end RBM.Univ
