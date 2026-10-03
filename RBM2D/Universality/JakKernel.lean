/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.JakSpectral

/-!
# The deterministic kernel layer of `(jaklsdufowe)`

Paper: arXiv:2503.07606, the display `(jaklsdufowe)`.  For a Hermitian matrix `H` of size
`N = (WL)²`, per site `y`, this file bounds the weighted `y`-term of `L₁`,
`(∏_{j∈s} Im m(w_j)) |∑_x (G²)_{xx} S°_{xy} G_{yy}|`
(the integrand of the statement `Jak`), pointwise in the sample:

* the covering lemma: a bound on `Im G_xx` at the single scale `η`, on the grid
  `E₀ - r + 2ηj`, `j ≤ ⌈r/η⌉₊`, controls the eigenvector mass at `x` of every window of radius
  `r` (`sum_mass_window_le_im_green`, `sum_mass_window_le_of_im_green_le`);
* the single-scale grid event `jakGridGood`;
* the bound on the grid event with `|M_{y,α}| ≤ θ` in the window off the `Bad` blocks
  (`jak_pointwise_good`), and the crude bound valid for every matrix (`jak_pointwise_crude`).

Conventions (`d = 2`): the Stieltjes transform is `stieltjesN`; the block of the site `y` is
`blockM L W hH (siteBlock L W y)`; the profile weights are `Scirc` and `Spaper + N⁻¹`, with the
row sum `sum_Spaper_row` (`∑_x (|S_{xy}| + N⁻¹) = 2`); the matrix size is `(W L)²`; the
statements are per site `y` and per `(σ₁, σ₂)`.

This file proves only deterministic implications; it states no probability estimate.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## The covering lemma (generic index type) -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real core of the covering: every `a` with `|a - E₀| ≤ r` is within `η` of one of the
`⌈r/η⌉₊ + 1` centres `E₀ - r + 2ηj`. -/
private theorem JakKernel_covering_exists_center {η r E₀ a : ℝ} (hη : 0 < η)
    (ha : |a - E₀| ≤ r) :
    ∃ j ∈ Finset.range (⌈r / η⌉₊ + 1), |a - (E₀ - r + 2 * η * j)| ≤ η := by
  have hr : 0 ≤ r := (abs_nonneg _).trans ha
  set x : ℝ := (a - E₀ + r) / (2 * η) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg _ (by positivity); linarith [(abs_le.1 ha).1]
  have hxr : x ≤ r / η := by
    rw [hx, div_le_div_iff₀ (by positivity) hη]
    nlinarith [(abs_le.1 ha).2]
  set j : ℕ := ⌊x + 1 / 2⌋₊ with hj
  have hj1 : (j : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
  have hj2 : x + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · rw [Finset.mem_range]
    have h1 : (j : ℝ) < r / η + 1 := by linarith [div_nonneg hr hη.le]
    have h2 : r / η ≤ (⌈r / η⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast (show (j : ℝ) < (⌈r / η⌉₊ : ℝ) + 1 by linarith)
  · have hax : a = E₀ - r + 2 * η * x := by rw [hx]; field_simp; ring
    rw [hax, abs_le]
    constructor <;> nlinarith

/-- **Covering lemma (one scale ⇒ every larger scale).**  The eigenvector mass at `x` of the
eigenvalues in `[E₀ - r, E₀ + r]` is bounded by `2η` times the sum of `Im G_xx` at the
`⌈r/η⌉₊ + 1` points `E₀ - r + 2ηj + iη` (all at the single scale `η`). -/
theorem sum_mass_window_le_im_green {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r : ℝ}
    (hη : 0 < η) (_hr : 0 ≤ r) (E₀ : ℝ) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤
      2 * η * ∑ j ∈ Finset.range (⌈r / η⌉₊ + 1),
        (RBM.green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im := by
  set K := ⌈r / η⌉₊ + 1
  set w : n → ℝ := fun l => ‖hH.eigenvectorBasis l x‖ ^ 2
  set k : ℕ → n → ℝ := fun j l =>
    w l * (η / ((hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2))
  have hk0 : ∀ j l, 0 ≤ k j l := fun j l => by
    simp only [k, w]; positivity
  have hG : ∀ j : ℕ, (RBM.green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im =
      ∑ l, k j l := by
    intro j
    rw [RBM.im_green_apply_self hH _ hη.ne']
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [k, w, Complex.normSq_eq_norm_sq]
    ring
  have hpt : ∀ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
      w l ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
    intro l hl
    obtain ⟨j, hjK, hjc⟩ := JakKernel_covering_exists_center hη (Finset.mem_filter.1 hl).2
    have hw : 0 ≤ w l := by simp only [w]; positivity
    set D := (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2
    have hD : 0 < D := by positivity
    have hDle : D ≤ 2 * η ^ 2 := by
      have : (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 ≤ η ^ 2 := by
        apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
      simp only [D]; linarith
    have hone : w l ≤ 2 * η * k j l := by
      simp only [k]
      rw [show 2 * η * (w l * (η / D)) = w l * (2 * η ^ 2 / D) by field_simp]
      have : 1 ≤ 2 * η ^ 2 / D := by rw [le_div_iff₀ hD]; linarith
      nlinarith
    calc w l ≤ 2 * η * k j l := hone
      _ ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hk0 j l) hjK
  calc ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r), w l
      ≤ ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
          2 * η * ∑ j ∈ Finset.range K, k j l := Finset.sum_le_sum hpt
    _ ≤ ∑ l, 2 * η * ∑ j ∈ Finset.range K, k j l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro l _ _
        have := fun j => hk0 j l
        positivity
    _ = 2 * η * ∑ j ∈ Finset.range K,
          (RBM.green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hG]

/-- Application form: a single-scale bound `Im G_xx ≤ Cb` at the grid points gives window mass
`≤ 2(r + 2η) Cb` at every scale `r ≥ 0`. -/
theorem sum_mass_window_le_of_im_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η r Cb : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb) (E₀ : ℝ) (x : n)
    (hG : ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1),
      (RBM.green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im ≤ Cb) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb := by
  refine (sum_mass_window_le_im_green hH hη hr E₀ x).trans ?_
  have hsum := Finset.sum_le_sum hG
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hK : ((⌈r / η⌉₊ + 1 : ℕ) : ℝ) ≤ r / η + 2 := by
    push_cast; linarith [Nat.ceil_lt_add_one (div_nonneg hr hη.le)]
  calc 2 * η * _ ≤ 2 * η * (((⌈r / η⌉₊ + 1 : ℕ) : ℝ) * Cb) := by gcongr
    _ ≤ 2 * η * ((r / η + 2) * Cb) := by gcongr
    _ = 2 * (r + 2 * η) * Cb := by field_simp

/-! ## The single-scale grid event and its deterministic consequences -/

/-- The single-scale grid event: `Im G_xx ≤ Cb` on the covering grid of centre `E₀`, radius
`r`, scale `η`, for every site `x`. -/
def jakGridGood (H : Matrix n n ℂ) (η Cb E₀ r : ℝ) : Prop :=
  ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1), ∀ x : n,
    (RBM.green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im ≤ Cb

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1`. -/
private theorem JakKernel_sum_sq_norm_row {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
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
private theorem JakKernel_sum_sq_norm_col {H : Matrix n n ℂ} (hH : H.IsHermitian) (k : n) :
    ∑ p, ‖hH.eigenvectorBasis k p‖ ^ 2 = 1 := by
  have h := hH.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

private theorem JakKernel_gridGood_mass {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : jakGridGood H η Cb E₀ r) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb :=
  sum_mass_window_le_of_im_green_le hH hη hr hCb E₀ x fun j hj => hG j hj x

/-- Eigenvalue counting from the site masses: `#{l : |λ_l - E₀| ≤ r} ≤ |n| · 2(r+2η)Cb`. -/
private theorem JakKernel_gridGood_count {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : jakGridGood H η Cb E₀ r) :
    ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) ≤
      (Fintype.card n : ℝ) * (2 * (r + 2 * η) * Cb) := by
  have h1 : ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) =
      ∑ x : n, ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [JakKernel_sum_sq_norm_col hH]
    simp
  rw [h1]
  calc _ ≤ ∑ _x : n, 2 * (r + 2 * η) * Cb :=
        Finset.sum_le_sum fun x _ => JakKernel_gridGood_mass hH hη hr hCb hG x
    _ = _ := by simp

/-- Bulk delocalization from the grid: `|λ_α - E₀| ≤ R` gives `|ψ_α(x)|² ≤ 2η Cb`. -/
private theorem JakKernel_gridGood_deloc {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ R : ℝ} (hη : 0 < η) (hG : jakGridGood H η Cb E₀ R) {α : n}
    (hα : |hH.eigenvalues α - E₀| ≤ R) (x : n) :
    ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ 2 * η * Cb := by
  obtain ⟨j, hj, hjc⟩ := JakKernel_covering_exists_center hη hα
  have hGj := hG j hj x
  rw [RBM.im_green_apply_self hH _ hη.ne'] at hGj
  set e : ℝ := E₀ - R + 2 * η * j
  have hterm : η * Complex.normSq (hH.eigenvectorBasis α x) /
      ((hH.eigenvalues α - e) ^ 2 + η ^ 2) ≤
      ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2) :=
    Finset.single_le_sum (f := fun l => η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2))
      (fun l _ => div_nonneg (mul_nonneg hη.le (Complex.normSq_nonneg _)) (by positivity))
      (Finset.mem_univ α)
  have hsq : (hH.eigenvalues α - e) ^ 2 ≤ η ^ 2 := by
    apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
  have hD : 0 < (hH.eigenvalues α - e) ^ 2 + η ^ 2 := by positivity
  have hv : 0 ≤ ‖hH.eigenvectorBasis α x‖ ^ 2 := by positivity
  rw [Complex.normSq_eq_norm_sq] at hterm
  have hle : ‖hH.eigenvectorBasis α x‖ ^ 2 ≤
      2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 / ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ hD]
    nlinarith
  calc _ ≤ 2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 /
        ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := hle
    _ ≤ 2 * η * Cb := by gcongr; exact hterm.trans hGj

/-- For a finite Hermitian matrix, `Im m(E + iη) = |n|⁻¹ ∑ₗ η / ((λₗ-E)²+η²)` for positive `η`. -/
private theorem JakKernel_stieltjesN_im_eq (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ)
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
private theorem JakKernel_stieltjesN_eta_mul_im_mono (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ηTilde : ℝ) (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjesN H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjesN H (E + ηTilde * Complex.I)).im := by
  have hformula := JakKernel_stieltjesN_im_eq H hH E η hη
  have hformulaT := JakKernel_stieltjesN_im_eq H hH E ηTilde (by linarith)
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
private theorem JakKernel_gridGood_zero_stieltjes [Nonempty n] {H : Matrix n n ℂ} {η Cb E₀ : ℝ}
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
private theorem JakKernel_dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
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

private theorem JakKernel_geom_half_sum_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h

/-! ## Pole bounds (generic index type) -/

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem JakKernel_pole_norm_eq (u : ℂ) (α : n) :
    ‖spectralPole hH u α‖ = ‖(hH.eigenvalues α : ℂ) - u‖⁻¹ := by
  rw [spectralPole, norm_inv]

private theorem JakKernel_pole_norm_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ≤ u.im⁻¹ := by
  rw [JakKernel_pole_norm_eq]
  have h : u.im ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - u)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hη] at this
  exact inv_anti₀ hη h

private theorem JakKernel_pole_norm_le_inv_dist {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ≤ |hH.eigenvalues α - u.re|⁻¹ := by
  rw [JakKernel_pole_norm_eq]
  have h : |hH.eigenvalues α - u.re| ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_re_le_norm ((hH.eigenvalues α : ℂ) - u)
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  exact inv_anti₀ hd h

private theorem JakKernel_pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [JakKernel_pole_norm_eq, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem JakKernel_pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (JakKernel_pole_norm_le_inv_dist hH α hd) 2

include hH in
/-- Crude bound `Im m(w) ≤ 1/Im w`, and `Im m(w) ≥ 0`. -/
private theorem JakKernel_stieltjesN_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
    0 ≤ (stieltjesN H w).im ∧ (stieltjesN H w).im ≤ w.im⁻¹ := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hf := JakKernel_stieltjesN_im_eq H hH w.re w.im hη
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
private theorem JakKernel_stieltjesN_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im)
    {ηt Cb : ℝ} (hηη : w.im ≤ ηt) (hG : jakGridGood H ηt Cb w.re 0) :
    (stieltjesN H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := JakKernel_stieltjesN_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := JakKernel_gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)

/-- `∑_α |p_α(u)|² ≤ (ηt/η²) |n| Cb` from the zero-radius grid at `Re u`. -/
private theorem JakKernel_sum_pole_sq_le_of_grid [Nonempty n] {u : ℂ} (hη : 0 < u.im)
    {ηt Cb : ℝ} (hηη : u.im ≤ ηt) (hG : jakGridGood H ηt Cb u.re 0) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ ηt / u.im ^ 2 * ((Fintype.card n : ℝ) * Cb) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hT := JakKernel_gridGood_zero_stieltjes (H := H) hG
  have hf := JakKernel_stieltjesN_im_eq H hH u.re ηt hηt
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ l : n, ηt / ((hH.eigenvalues l - u.re) ^ 2 + ηt ^ 2) ≤
      (Fintype.card n : ℝ) * Cb := by
    rw [hf] at hT
    rw [inv_mul_le_iff₀ hcard] at hT
    exact hT
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [JakKernel_pole_norm_sq_eq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    rw [show ηt / u.im ^ 2 * (ηt / (x + ηt ^ 2)) = ηt ^ 2 / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    nlinarith [mul_le_mul_of_nonneg_left h2 hx]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) :=
        Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

include hH in
/-- **The `Q_y` factor.** `∑_γ |p_γ(u)| |ψ_γ(y)|² ≤ 6(η̃/η)Cb + 8K Cb + (2^K η̃)⁻¹` from the grids
of
radii `2^k η̃`, `k ≤ K` (near part, `K` dyadic shells, completeness beyond `2^K η̃`). -/
private theorem JakKernel_sum_pole_mass_le {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hCb : 0 ≤ Cb) (K : ℕ)
    (hG : ∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt)) (y : n) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤
      6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ y‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  -- pointwise dyadic majorant
  have hpt : ∀ γ, ‖spectralPole hH u γ‖ * v γ ≤
      u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
        ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ (2 ^ K * ηt)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ ηt
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_im hH hη γ) (hv0 γ)
      linarith
    · push Not at h1
      have hdpos : 0 < dd γ := lt_trans hηt h1
      have hpd := mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_dist hH γ hdpos) (hv0 γ)
      simp only [not_le.2 h1, ite_false, mul_zero, zero_add]
      by_cases h2 : dd γ ≤ 2 ^ K * ηt
      · have hdy := JakKernel_dyadic_le_sum (f := fun x => x⁻¹)
          (fun a b ha hab => inv_anti₀ ha hab)
          (fun a ha => inv_nonneg.2 ha.le) hηt K h1 h2
        have hdy' : (dd γ)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) := by
          calc (dd γ)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K,
                (if dd γ ≤ 2 ^ (k + 1) * ηt then (2 ^ k * ηt)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ)⁻¹ * v γ ≤ (2 ^ K * ηt)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2.le) (hv0 γ)
        linarith
  -- mass bounds from the grids
  have hmass : ∀ r : ℝ, 0 ≤ r → jakGridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact JakKernel_gridGood_mass hH hηt hr hCb hGr y
  have hm0 : ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤ 2 * (ηt + 2 * ηt) * Cb :=
    hmass ηt hηt.le (by simpa using hG 0 (Nat.zero_le _))
  have hmk : ∀ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤ 8 * Cb := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * ηt) (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * ηt := by positivity
    have h1 : (2 ^ k * ηt)⁻¹ * ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤
        (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) =
        (4 + 4 * ((2 : ℝ) ^ k)⁻¹) * Cb := by
      field_simp; ring
    have h3 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hsumv : ∑ γ, v γ = 1 := JakKernel_sum_sq_norm_row hH y
  calc ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2
      = ∑ γ, ‖spectralPole hH u γ‖ * v γ := rfl
    _ ≤ ∑ γ, (u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) +
          (2 ^ K * ηt)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_comm]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) + ∑ _k ∈ Finset.range K, 8 * Cb +
          (2 ^ K * ηt)⁻¹ * 1 := by
        rw [hsumv]
        have hA : u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤
            u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left hm0 (by positivity)
        have hB := Finset.sum_le_sum hmk
        linarith
    _ = 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring

include hH in
/-- Crude `Q_y ≤ 1/η`. -/
private theorem JakKernel_sum_pole_mass_le_crude {u : ℂ} (hη : 0 < u.im) (y : n) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ u.im⁻¹ := by
  calc _ ≤ ∑ γ, u.im⁻¹ * ‖hH.eigenvectorBasis γ y‖ ^ 2 :=
        Finset.sum_le_sum fun γ _ =>
          mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_im hH hη γ) (by positivity)
    _ = u.im⁻¹ := by rw [← Finset.mul_sum, JakKernel_sum_sq_norm_row hH y, mul_one]

end Generic

/-! ## The block profile (d = 2): the `A_y` factor -/

section Block

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (Idx L W) (Idx L W) ℂ} (hH : Hm.IsHermitian)

private theorem JakKernel_card_idx : Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp only [Idx, Z2, Fintype.card_prod, ZMod.card]
  ring

private theorem JakKernel_N_pos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) 2

omit [NeZero L] [NeZero W] in
private theorem JakKernel_Spaper_eq_norm (x y : Idx L W) :
    Spaper L W x y = ((‖Spaper L W x y‖ : ℝ) : ℂ) := by
  rw [Spaper_indicator]
  split_ifs
  · rw [norm_mul, norm_inv, norm_pow, norm_inv]
    simp
  · simp

omit [NeZero L] in
private theorem JakKernel_Spaper_symm (x y : Idx L W) : Spaper L W x y = Spaper L W y x := by
  have := congrFun (congrFun (Spaper_transpose L W) y) x
  simpa using this

/-- Column sums of the covariance: `∑_x |S_{xy}| = 1`, for `L ≥ 3`. -/
private theorem JakKernel_sum_norm_Spaper (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, ‖Spaper L W x y‖ = 1 := by
  have h : ((∑ x : Idx L W, ‖Spaper L W x y‖ : ℝ) : ℂ) = 1 := by
    push_cast
    calc ∑ x : Idx L W, ((‖Spaper L W x y‖ : ℝ) : ℂ) = ∑ x : Idx L W, Spaper L W x y :=
          Finset.sum_congr rfl fun x _ => (JakKernel_Spaper_eq_norm x y).symm
      _ = ∑ x : Idx L W, Spaper L W y x :=
          Finset.sum_congr rfl fun x _ => JakKernel_Spaper_symm x y
      _ = 1 := sum_Spaper_row L W hL y
  exact_mod_cast h

omit [NeZero L] [NeZero W] in
private theorem JakKernel_Scirc_norm_le (x y : Idx L W) :
    ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ := by
  calc ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + ‖(((W * L) ^ 2 : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = _ := by rw [norm_inv, Complex.norm_natCast]

/-- The weight sum: `∑_x (|S_{xy}| + N⁻¹) = 2` (`sum_Spaper_row`). -/
private theorem JakKernel_profile_weight_sum (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, JakKernel_sum_norm_Spaper hL y]
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt JakKernel_N_pos
  have hconst : ∑ _x : Idx L W, (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, JakKernel_card_idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num

include hH in
/-- `|M_{y,α}| ≤ 2N · D` if `|ψ_α(x)|² ≤ D` for every `x`. -/
private theorem JakKernel_norm_blockM_le_of_mass (hL : 3 ≤ L) (y α : Idx L W) {D : ℝ}
    (hMass : ∀ x, ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ D) :
    ‖blockM L W hH (siteBlock L W y) α‖ ≤ 2 * (((W * L) ^ 2 : ℕ) : ℝ) * D := by
  rw [blockM_eq hL hH y α]
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := JakKernel_N_pos
  calc ‖(((W * L) ^ 2 : ℕ) : ℂ) *
        ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * Scirc L W x y‖
      ≤ (((W * L) ^ 2 : ℕ) : ℝ) * ∑ x, D * (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) := by
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hN.le
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul (hMass x) (JakKernel_Scirc_norm_le x y) (norm_nonneg _)
          ((sq_nonneg _).trans (hMass x))
    _ = 2 * (((W * L) ^ 2 : ℕ) : ℝ) * D := by
        rw [← Finset.mul_sum, JakKernel_profile_weight_sum hL y]; ring

include hH in
/-- Bulk bound `|M_{y,α}| ≤ 4Nη̃Cb` for `|λ_α - E₀| ≤ R`, from the grid of radius `R`. -/
private theorem JakKernel_norm_blockM_le_of_grid (hL : 3 ≤ L) (y : Idx L W)
    {ηt Cb E₀ R : ℝ} (hηt : 0 < ηt) (hG : jakGridGood Hm ηt Cb E₀ R) {α : Idx L W}
    (hα : |hH.eigenvalues α - E₀| ≤ R) :
    ‖blockM L W hH (siteBlock L W y) α‖ ≤ 4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb := by
  have := JakKernel_norm_blockM_le_of_mass hH hL y α (D := 2 * ηt * Cb)
    (fun x => JakKernel_gridGood_deloc hH hηt hG hα x)
  linarith

include hH in
/-- **The `A_y` factor.** Window part (`|λ_α - Re u| ≤ w'`, `|M| ≤ Mwin`), dyadic bulk part
(`w' < |λ_α - Re u| ≤ 2^{K'}w'`, delocalization and counting) and the part outside
`2^{K'}w'` (completeness `∑_α|M_{y,α}| ≤ 2N`, `sum_norm_blockM_le`). -/
private theorem JakKernel_sum_pole_sq_blockM_le (hL : 3 ≤ L) (y : Idx L W) {u : ℂ}
    (hη : 0 < u.im) {ηt Cb w' Rd Mwin : ℝ} (hηη : u.im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hMwin : 0 ≤ Mwin) (K' : ℕ) (hRd : 2 ^ K' * w' ≤ Rd)
    (hGd : jakGridGood Hm ηt Cb u.re Rd)
    (hGc : ∀ k ≤ K', jakGridGood Hm ηt Cb u.re (2 ^ k * w'))
    (hG0 : jakGridGood Hm ηt Cb u.re 0)
    (hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM L W hH (siteBlock L W y) α‖ ≤ Mwin) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
      Mwin * (ηt / u.im ^ 2 * ((((W * L) ^ 2 : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ 2 : ℕ) : ℝ)) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := JakKernel_N_pos
  have hcard : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
    rw [JakKernel_card_idx]
  set dd : Idx L W → ℝ := fun α => |hH.eigenvalues α - u.re| with hdd
  set Mb : ℝ := 4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hpt : ∀ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
      (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖ := by
    intro α
    have hS0 : 0 ≤ Mb * ∑ k ∈ Finset.range K',
        (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) :=
      mul_nonneg hMb0 (Finset.sum_nonneg fun k _ => by split_ifs <;> positivity)
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖ := by positivity
    by_cases h1 : dd α ≤ w'
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_left (hwin α h1) (sq_nonneg ‖spectralPole hH u α‖)
      nlinarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false, zero_add]
      have hdpos : 0 < dd α := lt_trans hw' h1
      have hp2 := JakKernel_pole_norm_sq_le_inv_dist_sq hH α hdpos
      by_cases h2 : dd α ≤ 2 ^ K' * w'
      · have hM := JakKernel_norm_blockM_le_of_grid hH hL y hηt hGd (h2.trans hRd)
        have hdy := JakKernel_dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
            (dd α ^ 2)⁻¹ * Mb :=
          mul_le_mul hp2 hM (norm_nonneg _) (by positivity)
        have h3 : (dd α ^ 2)⁻¹ * Mb ≤ Mb * ∑ k ∈ Finset.range K',
            (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hdy hMb0
        linarith
      · push Not at h2
        have h4 : (dd α ^ 2)⁻¹ ≤ ((2 ^ K' * w') ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
            ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖ :=
          mul_le_mul_of_nonneg_right (hp2.trans h4) (norm_nonneg _)
        linarith
  -- window part
  have hW1 : ∑ α, (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) ≤
      Mwin * (ηt / u.im ^ 2 * ((((W * L) ^ 2 : ℕ) : ℝ) * Cb)) := by
    calc _ ≤ ∑ α, Mwin * ‖spectralPole hH u α‖ ^ 2 :=
          Finset.sum_le_sum fun α _ => by split_ifs <;> [exact le_rfl; positivity]
      _ = Mwin * ∑ α, ‖spectralPole hH u α‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          have := JakKernel_sum_pole_sq_le_of_grid hH hη hηη hG0
          rwa [hcard] at this
  -- dyadic counting part
  have hcount : ∀ k ∈ Finset.range K',
      ∑ α, (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
        2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have hc := JakKernel_gridGood_count hH hηt (by positivity) hCb (hGc (k + 1) hkK)
    rw [hcard] at hc
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) *
            ((2 ^ k * w') ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ 2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hW2 : ∑ α, Mb * ∑ k ∈ Finset.range K',
      (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
      Mb * (2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left ?_ hMb0
    calc _ ≤ ∑ k ∈ Finset.range K',
          2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum hcount
      _ = 2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) *
            ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * 2 := by
          gcongr; exact JakKernel_geom_half_sum_le K'
      _ = _ := by ring
  -- outside part
  have hW3 : ∑ α, ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖ ≤
      ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ 2 : ℕ) : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_norm_blockM_le hL hH (siteBlock L W y))
      (by positivity)
  calc _ ≤ ∑ α, ((if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖) :=
        Finset.sum_le_sum fun α _ => hpt α
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

include hH in
/-- Crude `A_y ≤ 2N/η²`. -/
private theorem JakKernel_sum_pole_sq_blockM_le_crude (hL : 3 ≤ L) (y : Idx L W) {u : ℂ}
    (hη : 0 < u.im) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
      (u.im ^ 2)⁻¹ * (2 * (((W * L) ^ 2 : ℕ) : ℝ)) := by
  calc _ ≤ ∑ α, (u.im ^ 2)⁻¹ * ‖blockM L W hH (siteBlock L W y) α‖ := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← inv_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (JakKernel_pole_norm_le_inv_im hH hη α) 2
    _ = (u.im ^ 2)⁻¹ * ∑ α, ‖blockM L W hH (siteBlock L W y) α‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_blockM_le hL hH (siteBlock L W y))
        (by positivity)

end Block

/-! ## The pointwise bounds of the weighted `y`-term -/

section Pointwise

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Pointwise bound on the good event**.  On the single-scale grid event, with the window bound
`|M_{y,α}| ≤ θ` off the blocks
flagged `Bad`, the weighted `y`-term of `L₁` (the integrand of `Jak`) is at most the
product of the `Im m` factors times `N⁻¹ (α₁ + 1_{Bad} α₂) Q̄`; `N = (W L)²`. -/
theorem jak_pointwise_good (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {ηt Cb w' θ α₁ α₂ Qb : ℝ} (hηu : 0 < u.im) (hηu' : u.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K K' : ℕ)
    (hG1 : ∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u.re 0)
    (hG4 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Z2 L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM L W hH a0 α‖ ≤ θ)
    (hα₁ : θ * (ηt / u.im ^ 2 * ((((W * L) ^ 2 : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ 2 : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ 2 : ℕ) : ℝ)) ≤ α₁)
    (hα₂ : 4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb *
        (ηt / u.im ^ 2 * ((((W * L) ^ 2 : ℕ) : ℝ) * Cb)) ≤ α₂)
    (hQb : 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ ≤ Qb)
    (y : Idx L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹ *
          ((α₁ + (if Bad (siteBlock L W y) then α₂ else 0)) * Qb)) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hηu hηu'
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := JakKernel_N_pos
  -- the `Im m` factors
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀
      (fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => JakKernel_stieltjesN_im_le_of_grid hH (hηw j) (hηw' j) (hG4 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  -- the `A_y` factor
  have hA : ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖ ≤
      α₁ + (if Bad (siteBlock L W y) then α₂ else 0) := by
    have hRd : (2 : ℝ) ^ K' * w' ≤ 2 ^ K' * w' := le_rfl
    have hGd := hG2 K' le_rfl
    by_cases hb : Bad (siteBlock L W y)
    · simp only [hb, ite_true]
      have hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
          ‖blockM L W hH (siteBlock L W y) α‖ ≤
            4 * (((W * L) ^ 2 : ℕ) : ℝ) * ηt * Cb := by
        intro α hα
        have h1 : w' ≤ 2 ^ K' * w' := le_mul_of_one_le_left hw'.le (one_le_pow₀ (by norm_num))
        exact JakKernel_norm_blockM_le_of_grid hH hL y hηt hGd (hα.trans h1)
      have h := JakKernel_sum_pole_sq_blockM_le hH hL y hηu hηu' hCb hw' (by positivity) K' hRd
        hGd hG2 hG3 hwin
      have hX : 0 ≤ θ * (ηt / u.im ^ 2 * ((((W * L) ^ 2 : ℕ) : ℝ) * Cb)) := by positivity
      linarith
    · simp only [hb, ite_false, add_zero]
      have h := JakKernel_sum_pole_sq_blockM_le hH hL y hηu hηu' hCb hw' hθ K' hRd hGd hG2 hG3
        (hBad _ hb)
      linarith
  have hQ : ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ Qb :=
    (JakKernel_sum_pole_mass_le hH hηu hηu' hCb K hG1 y).trans hQb
  have hα₁0 : 0 ≤ α₁ := le_trans (by positivity) hα₁
  have hα₂0 : 0 ≤ α₂ := le_trans (by positivity) hα₂
  have hAy0 : 0 ≤ α₁ + (if Bad (siteBlock L W y) then α₂ else 0) :=
    add_nonneg hα₁0 (by split_ifs <;> linarith)
  -- the `y`-term
  have hK := norm_green_spectral_identity_blockM_le hL hH y hηu σ₁ σ₂
  simp only [spectralGsigPole_norm_eq_spectralPole, Complex.normSq_eq_norm_sq] at hK
  have hK' : ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ ≤
      (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ *
        ((α₁ + (if Bad (siteBlock L W y) then α₂ else 0)) * Qb) := by
    refine hK.trans ?_
    rw [mul_assoc]
    gcongr
  calc (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- **Crude pointwise bound**, valid
for every Hermitian matrix: `∏ Im m(w_j) · |y-term| ≤ ∏ (Im w_j)⁻¹ · 2 (Im u)⁻³`. -/
theorem jak_pointwise_crude (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hηu : 0 < u.im) (hηw : ∀ j, 0 < (w j).im)
    (y : Idx L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (2 * (u.im⁻¹) ^ 3) := by
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := JakKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hK := norm_green_spectral_identity_blockM_le hL hH y hηu σ₁ σ₂
  simp only [spectralGsigPole_norm_eq_spectralPole, Complex.normSq_eq_norm_sq] at hK
  have hA := JakKernel_sum_pole_sq_blockM_le_crude hH hL y hηu
  have hQ := JakKernel_sum_pole_mass_le_crude hH hηu y
  have hK' : ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ ≤
      2 * (u.im⁻¹) ^ 3 := by
    refine hK.trans ?_
    calc (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ *
          (∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM L W hH (siteBlock L W y) α‖) *
          (∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2)
        ≤ (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ * ((u.im ^ 2)⁻¹ * (2 * (((W * L) ^ 2 : ℕ) : ℝ))) *
            u.im⁻¹ := by
          gcongr
      _ = 2 * (u.im⁻¹) ^ 3 := by
          field_simp
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) *
          ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

end Pointwise

end RBM.Univ
