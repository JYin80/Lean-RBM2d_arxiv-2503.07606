/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins

/-!
# The deterministic spectral layer of `(jaklsdufowe)`

Paper: arXiv:2503.07606, the display `(jaklsdufowe)` and the definition of `M_{y,α}` after it
(`yw982823`).  For a Hermitian matrix `H` of size `N = (WL)²` with orthonormal eigenbasis `ψ_α`
(Mathlib's `eigenvectorBasis`), this file proves the deterministic finite-dimensional identities
behind the `y`-term `∑_x (G²)_{xx} S°_{xy} G_{yy}` of the statement `Jak`:

* the eigenbasis expansion of `G`, `G²` on the diagonal (`green_sq_apply_self`,
  `Gsig_apply_self_spectral`, `Gsig_sq_apply_self_spectral`,
  `spectralGsigPole_norm_eq_spectralPole`);
* `blockM`, the five-block average `M_{y,α}` of the QUE quantities, and its identification
  `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` for `L ≥ 3` (`blockM_eq`);
* the exact spectral expansion of the `y`-term and its triangle bound
  (`green_spectral_identity_blockM`, `norm_green_spectral_identity_blockM_le`);
* the mass bound `∑_α |M_{a₀,α}| ≤ 2N` (`sum_norm_blockM_le`);
* Mathlib's eigenbasis is an `IsOrthoEigenbasis` (`isOrthoEigenbasis_eigenvectorBasis`);
* the union bound from the failure event `queBadMat` over the five blocks `a₀ + sbSupport`
  (`measure_bad_le_of_queBadMat`).

Conventions (`d = 2`): the index set is `Idx L W`; the matrix size is `(W L)²`; `S° = Scirc`; the
QUE blocks are the five blocks `a₀ + sbSupport L`, with the factor `1/5`.

This file proves only deterministic implications.  It does not assert any probability estimate
other than the union bound `measure_bad_le_of_queBadMat`.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## Eigenbasis expansion of the resolvent (generic index type) -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue coefficient of the resolvent with spectral parameter `w`. -/
def spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (w : ℂ) (α : n) : ℂ :=
  ((hH.eigenvalues α : ℂ) - w)⁻¹

/-- The eigenvalue coefficient for `Gsig`: the minus sign uses the conjugate spectral parameter. -/
def spectralGsigPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (α : n) : ℂ :=
  spectralPole hH (if σ then z else (starRingEnd ℂ) z) α

private theorem JakSpectral_eigenvalues_ne_of_im_ne {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) : ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

private theorem JakSpectral_im_gsig_ne {z : ℂ} (hη : 0 < z.im) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simp [hη.ne']

/-- Diagonal entries of the squared resolvent, including the square on the spectral pole. -/
theorem green_sq_apply_self {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x : n) :
    (green H w ^ 2) x x =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hG : green H w = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using green_eq_spectral hH hw
  have hG2 : green H w ^ 2 = U * diagonal (fun α => d α * d α) * star U := by
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
      star ((hH.eigenvectorUnitary : Matrix n n ℂ) x α)) = _
  rw [IsHermitian.eigenvectorUnitary_apply, Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def, d]
  ring

/-- Diagonal entries of `Gsig` in the eigenbasis. -/
theorem Gsig_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (y : n) :
    Gsig H z σ y y =
      ∑ β, spectralGsigPole hH z σ β *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℂ) := by
  have heig := JakSpectral_eigenvalues_ne_of_im_ne hH (JakSpectral_im_gsig_ne hη σ)
  rw [Gsig, green_apply_self hH heig y]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [spectralGsigPole, spectralPole, div_eq_mul_inv]
  ring

/-- Diagonal entries of `Gsig²` in the eigenbasis. -/
theorem Gsig_sq_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (x : n) :
    (Gsig H z σ ^ 2) x x =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  have heig := JakSpectral_eigenvalues_ne_of_im_ne hH (JakSpectral_im_gsig_ne hη σ)
  simpa [Gsig, spectralGsigPole, spectralPole] using green_sq_apply_self hH heig x

/-- Both resolvent signs have the same pole norm for a Hermitian matrix. -/
theorem spectralGsigPole_norm_eq_spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (σ : Bool) (α : n) :
    ‖spectralGsigPole hH z σ α‖ = ‖spectralPole hH z α‖ := by
  cases σ
  · change ‖(((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z)⁻¹)‖ =
      ‖(((hH.eigenvalues α : ℂ) - z)⁻¹)‖
    rw [norm_inv, norm_inv]
    have hconj : ((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z) =
        star ((hH.eigenvalues α : ℂ) - z) := by simp
    rw [hconj, norm_star]
  · rfl

/-- Mathlib's eigenbasis is an orthonormal eigenbasis in the sense of `IsOrthoEigenbasis`. -/
theorem isOrthoEigenbasis_eigenvectorBasis {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    RBM.Endpoints.IsOrthoEigenbasis H hH.eigenvalues (fun k x => hH.eigenvectorBasis k x) := by
  refine ⟨fun k k' => ?_, fun k => ?_⟩
  · have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · rw [hH.mulVec_eigenvectorBasis k]
    ext x
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1`. -/
private theorem JakSpectral_sum_sq_norm {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
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

end Generic

/-! ## The block quantity `M_{y,α}` (d = 2) -/

section Block

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The block `a ∈ Z_L²` of a site `y` (the `a₀` with `y ∈ I_{a₀}`, `mem_Iblk`). -/
def siteBlock (y : Idx L W) : Z2 L := (split L W y).1

/-- `M_{y,α}` of `jaklsdufowe` for `y ∈ I_{a₀}` (d = 2): the average of the five QUE quantities
`N ψ_α^*(E_a - N⁻¹)ψ_α` over the blocks `a ∈ a₀ + {0, ±e₁, ±e₂}`. -/
def blockM {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (a0 : Z2 L)
    (α : Idx L W) : ℂ :=
  (((W * L) ^ 2 : ℕ) : ℂ) * ((1 / 5 : ℂ) * ∑ u ∈ sbSupport L,
    star (fun x => hH.eigenvectorBasis α x) ⬝ᵥ
      ((Epaper L W (a0 + u) -
          ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ
        (fun x => hH.eigenvectorBasis α x)))

/-- The overlap `ψ^*(E_a - c)ψ` of a diagonal block matrix, entrywise. -/
private theorem JakSpectral_overlap (a : Z2 L) (c : ℂ) (ψ : Idx L W → ℂ) :
    star ψ ⬝ᵥ ((Epaper L W a - c • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ ψ) =
      ∑ x, ((‖ψ x‖ ^ 2 : ℝ) : ℂ) *
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
  have : star (ψ x) * ψ x = ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← this]
  ring

omit [NeZero L] in
/-- The covariance `S_{xy}` at a site `y` of block `a0`: the five-point indicator in the block
of `x` against `a0`. -/
private theorem JakSpectral_Spaper (x y : Idx L W) :
    Spaper L W x y =
      if (split L W x).1 - siteBlock L W y ∈ sbSupport L
      then (5 : ℂ)⁻¹ * (W : ℂ)⁻¹ ^ 2 else 0 :=
  Spaper_indicator L W x y

variable {L W}

/-- `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` (the definition of `M_{y,α}` at `yw982823`); needs `L ≥ 3`
for the count `|sbSupport L| = 5`. -/
theorem blockM_eq (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (y α : Idx L W) :
    blockM L W hH (siteBlock L W y) α =
      (((W * L) ^ 2 : ℕ) : ℂ) *
        ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * Scirc L W x y := by
  set a0 : Z2 L := siteBlock L W y with ha0
  set c : ℂ := ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ with hc
  unfold blockM
  simp only [JakSpectral_overlap]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : ∑ u ∈ sbSupport L,
      ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
        ((W : ℂ)⁻¹ ^ 2 * (if x ∈ Iblk L W (a0 + u) then 1 else 0) - c) =
      ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * (
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
  rw [hx, Scirc, JakSpectral_Spaper]
  split_ifs <;> ring

end Block

/-! ## The exact spectral expansion of the `y`-term of `L₁` -/

section BlockGreen

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (Idx L W) (Idx L W) ℂ} (hH : Hm.IsHermitian)

/-- Exact eigenbasis expansion of the `y`-term before substituting `blockM_eq`. -/
private theorem JakSpectral_sum_variance (y : Idx L W) {z : ℂ} (hη : 0 < z.im)
    (σ₁ σ₂ : Bool) :
    (∑ x : Idx L W, (Gsig Hm z σ₁ ^ 2) x x * Scirc L W x y * Gsig Hm z σ₂ y y) =
      ∑ α : Idx L W, ∑ γ : Idx L W,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ *
          (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ) *
          ∑ x : Idx L W,
            (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) * Scirc L W x y := by
  let S0 : Idx L W → ℂ := fun x => Scirc L W x y
  let A : Idx L W → Idx L W → ℂ := fun α x =>
    (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)
  let P : Idx L W → ℂ := fun α =>
    spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α
  let B : Idx L W → ℂ := fun γ =>
    spectralGsigPole hH z σ₂ γ *
      (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ)
  calc
    (∑ x : Idx L W, (Gsig Hm z σ₁ ^ 2) x x * S0 x * Gsig Hm z σ₂ y y) =
        ∑ x : Idx L W, (∑ α : Idx L W, P α * A α x) * S0 x * ∑ γ : Idx L W, B γ := by
            congr 1
            funext x
            rw [Gsig_sq_apply_self_spectral hH hη σ₁, Gsig_apply_self_spectral hH hη σ₂]
    _ = ∑ α : Idx L W, ∑ γ : Idx L W, P α * B γ * ∑ x : Idx L W, A α x * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        calc
          _ = ∑ α : Idx L W, ∑ x : Idx L W, ∑ γ : Idx L W,
                P α * A α x * S0 x * B γ := by rw [Finset.sum_comm]
          _ = ∑ α : Idx L W, ∑ γ : Idx L W, ∑ x : Idx L W,
                P α * A α x * S0 x * B γ := by
                  congr 1
                  funext α
                  rw [Finset.sum_comm]
          _ = ∑ α : Idx L W, ∑ γ : Idx L W, ∑ x : Idx L W,
                P α * B γ * (A α x * S0 x) := by
                  refine Finset.sum_congr rfl fun α _ => ?_
                  refine Finset.sum_congr rfl fun γ _ => ?_
                  refine Finset.sum_congr rfl fun x _ => ?_
                  ring
          _ = _ := rfl
  simp [S0, A, P, B, mul_assoc]

/-- The averaged variance-profile factor in the spectral expansion is exactly `N⁻¹ M_{y,α}`. -/
private theorem JakSpectral_blockM_eq_variance_sum (hL : 3 ≤ L) (y α : Idx L W) :
    (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * blockM L W hH (siteBlock L W y) α =
      ∑ x : Idx L W, (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) * Scirc L W x y := by
  rw [blockM_eq hL hH y α]
  have hN : (((W * L) ^ 2 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero 2 (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  field_simp [hN]
  simp_rw [Complex.normSq_eq_norm_sq]

/-- Exact spectral expansion of the `y`-term of `L₁` (the integrand of `Jak`), with
`N⁻¹ M_{y,α}` substituted from `blockM_eq`. -/
theorem green_spectral_identity_blockM (hL : 3 ≤ L) (hH : Hm.IsHermitian) (y : Idx L W)
    {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx L W, (Gsig Hm z σ₁ ^ 2) x x * Scirc L W x y * Gsig Hm z σ₂ y y) =
      ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ * ∑ α : Idx L W, ∑ γ : Idx L W,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ * blockM L W hH (siteBlock L W y) α *
          (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ) := by
  rw [JakSpectral_sum_variance hH y hη σ₁ σ₂]
  simp_rw [← JakSpectral_blockM_eq_variance_sum hH hL y]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- Triangle bound for the exact expansion.  The `γ`-sum
remains weighted by the actual eigenvector masses at `y`; no uniform eigenvector bound is
assumed. -/
theorem norm_green_spectral_identity_blockM_le (hL : 3 ≤ L) (hH : Hm.IsHermitian)
    (y : Idx L W) {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx L W, (Gsig Hm z σ₁ ^ 2) x x * Scirc L W x y * Gsig Hm z σ₂ y y‖ ≤
      ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
        (∑ α : Idx L W, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 *
          ‖blockM L W hH (siteBlock L W y) α‖) *
        (∑ γ : Idx L W, ‖spectralGsigPole hH z σ₂ γ‖ *
          Complex.normSq (hH.eigenvectorBasis γ y)) := by
  rw [green_spectral_identity_blockM hL hH y hη σ₁ σ₂]
  let P : Idx L W → ℂ := fun α => spectralGsigPole hH z σ₁ α
  let Q : Idx L W → ℂ := fun γ => spectralGsigPole hH z σ₂ γ
  let M : Idx L W → ℂ := fun α => blockM L W hH (siteBlock L W y) α
  let w : Idx L W → ℝ := fun γ => Complex.normSq (hH.eigenvectorBasis γ y)
  have hw (γ : Idx L W) : 0 ≤ w γ := by
    simp only [w, Complex.normSq_eq_norm_sq]
    positivity
  have hnormw (γ : Idx L W) : ‖(w γ : ℂ)‖ = w γ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw γ)]
  have hterm (α γ : Idx L W) :
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    calc
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ =
          ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
            simp only [norm_mul, hnormw]
            ring
      _ ≤ _ := le_rfl
  have htriangle :
      ‖∑ α : Idx L W, ∑ γ : Idx L W,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx L W, ∑ γ : Idx L W,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
    calc
      ‖∑ α : Idx L W, ∑ γ : Idx L W,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
          ∑ α : Idx L W, ‖∑ γ : Idx L W,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ α : Idx L W, ∑ γ : Idx L W,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          exact Finset.sum_le_sum fun α _ => norm_sum_le _ _
  have htermSum :
      ∑ α : Idx L W, ∑ γ : Idx L W,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx L W, ∑ γ : Idx L W, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    exact Finset.sum_le_sum fun α _ =>
      Finset.sum_le_sum fun γ _ => hterm α γ
  have hfactor :
      ∑ α : Idx L W, ∑ γ : Idx L W, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) =
        (∑ α : Idx L W, ‖P α‖ ^ 2 * ‖M α‖) *
          (∑ γ : Idx L W, ‖Q γ‖ * w γ) := by
    calc
      _ = ∑ α : Idx L W, (‖P α‖ ^ 2 * ‖M α‖) *
            ∑ γ : Idx L W, ‖Q γ‖ * w γ := by
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    ‖(((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * ∑ α : Idx L W, ∑ γ : Idx L W,
        P α * P α * Q γ * M α * (w γ : ℂ)‖ =
        ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
          ‖∑ α : Idx L W, ∑ γ : Idx L W,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx L W, ∑ γ : Idx L W,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left htriangle (by positivity)
    _ ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx L W, ∑ γ : Idx L W,
            ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ)) := by
          exact mul_le_mul_of_nonneg_left htermSum (by positivity)
    _ = (((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx L W, ‖P α‖ ^ 2 * ‖M α‖)) *
            (∑ γ : Idx L W, ‖Q γ‖ * w γ) := by
          rw [hfactor]
          ring

end BlockGreen

/-! ## The mass bound `∑_α |M_{a₀,α}| ≤ 2N` -/

section Mass

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem JakSpectral_card_idx : Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp only [Idx, Z2, Fintype.card_prod, ZMod.card]
  ring

private theorem JakSpectral_N_pos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) 2

omit [NeZero L] in
/-- The covariance entry is a nonnegative real number. -/
private theorem JakSpectral_Spaper_eq_norm (x y : Idx L W) :
    Spaper L W x y = ((‖Spaper L W x y‖ : ℝ) : ℂ) := by
  rw [JakSpectral_Spaper]
  split_ifs
  · rw [norm_mul, norm_inv, norm_pow, norm_inv]
    simp
  · simp

omit [NeZero L] in
private theorem JakSpectral_Spaper_symm (x y : Idx L W) : Spaper L W x y = Spaper L W y x := by
  have := congrFun (congrFun (Spaper_transpose L W) y) x
  simpa using this

/-- Column sums of the covariance: `∑_x |S_{xy}| = 1`, for `L ≥ 3`. -/
private theorem JakSpectral_sum_norm_Spaper (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, ‖Spaper L W x y‖ = 1 := by
  have h : ((∑ x : Idx L W, ‖Spaper L W x y‖ : ℝ) : ℂ) = 1 := by
    push_cast
    calc ∑ x : Idx L W, ((‖Spaper L W x y‖ : ℝ) : ℂ) = ∑ x : Idx L W, Spaper L W x y :=
          Finset.sum_congr rfl fun x _ => (JakSpectral_Spaper_eq_norm x y).symm
      _ = ∑ x : Idx L W, Spaper L W y x :=
          Finset.sum_congr rfl fun x _ => JakSpectral_Spaper_symm x y
      _ = 1 := sum_Spaper_row L W hL y
  exact_mod_cast h

omit [NeZero L] [NeZero W] in
private theorem JakSpectral_Scirc_norm_le (x y : Idx L W) :
    ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ := by
  calc ‖Scirc L W x y‖ ≤ ‖Spaper L W x y‖ + ‖(((W * L) ^ 2 : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = _ := by rw [norm_inv, Complex.norm_natCast]

/-- `|M_{y,α}| ≤ N ∑_x |ψ_α(x)|² (|S_{xy}| + N⁻¹)`. -/
private theorem JakSpectral_norm_blockM_le (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (y α : Idx L W) :
    ‖blockM L W hH (siteBlock L W y) α‖ ≤ (((W * L) ^ 2 : ℕ) : ℝ) *
      ∑ x : Idx L W, ‖hH.eigenvectorBasis α x‖ ^ 2 *
        (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) := by
  rw [blockM_eq hL hH y α, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_))
    (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (JakSpectral_Scirc_norm_le x y) (sq_nonneg _)

private theorem JakSpectral_profile_weight_sum (hL : 3 ≤ L) (y : Idx L W) :
    ∑ x : Idx L W, (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, JakSpectral_sum_norm_Spaper hL y]
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt JakSpectral_N_pos
  have hconst : ∑ _x : Idx L W, (((W * L) ^ 2 : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, JakSpectral_card_idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num

/-- Full-spectrum aggregate of the block profile: `∑_α |M_{a₀,α}| ≤ 2N`.  Eigenbasis completeness
(`∑_α |ψ_α(x)|² = 1`) and the column sum `∑_x S_{xy} = 1` at a site `y` of the block `a₀`. -/
theorem sum_norm_blockM_le (hL : 3 ≤ L) {H : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : H.IsHermitian) (a0 : Z2 L) :
    ∑ α : Idx L W, ‖blockM L W hH a0 α‖ ≤ 2 * (((W * L) ^ 2 : ℕ) : ℝ) := by
  obtain ⟨y, hy⟩ : ∃ y : Idx L W, siteBlock L W y = a0 := by
    obtain ⟨y, hy⟩ := (split_bijective L W).2
      (a0, (⟨0, NeZero.pos W⟩, ⟨0, NeZero.pos W⟩))
    exact ⟨y, by simp [siteBlock, hy]⟩
  subst hy
  have hN : 0 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by positivity
  calc
    ∑ α : Idx L W, ‖blockM L W hH (siteBlock L W y) α‖ ≤
        ∑ α : Idx L W, (((W * L) ^ 2 : ℕ) : ℝ) *
          ∑ x : Idx L W, ‖hH.eigenvectorBasis α x‖ ^ 2 *
            (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum fun α _ => JakSpectral_norm_blockM_le hL hH y α
    _ = (((W * L) ^ 2 : ℕ) : ℝ) *
        ∑ x : Idx L W, (∑ α : Idx L W, ‖hH.eigenvectorBasis α x‖ ^ 2) *
          (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_mul]
    _ = (((W * L) ^ 2 : ℕ) : ℝ) *
        ∑ x : Idx L W, (‖Spaper L W x y‖ + (((W * L) ^ 2 : ℕ) : ℝ)⁻¹) := by
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [JakSpectral_sum_sq_norm hH x, one_mul]
    _ = 2 * (((W * L) ^ 2 : ℕ) : ℝ) := by
      rw [JakSpectral_profile_weight_sum hL y]
      ring

end Mass

/-! ## The bad event of `(jaklsdufowe)` is rare: the union bound from `queBadMat` -/

section Que

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The bad event `ℬ` of the proof of `(jaklsdufowe)` (the bad event ℬ in the proof of
`uywy7723r3rf`) is rare, from QUE**:
if the failure event `queBadMat` of `(Meq:QUE)` at energy `E` (window `N^{-1-τ} W^{2/3}`,
threshold `N^{-τ/6}`) has probability `≤ ε'` for each block `a`, then for `w` below the window
and `N^{-τ/6} ≤ θ²`,
`P(∃ α, |λ_α - E| ≤ w, |M_{a₀,α}| ≥ θ) ≤ 5ε'` (union over the at most five blocks
`a₀ + sbSupport L`; no `3 ≤ L` is needed). -/
theorem measure_bad_le_of_queBadMat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Hr : Ω → Matrix (Idx L W) (Idx L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian)
    {E w τ θ ε' : ℝ}
    (hw : w ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3))
    (hθ : 0 ≤ θ) (hθτ : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-τ / 6) ≤ θ ^ 2) (a0 : Z2 L)
    (hque : ∀ a : Z2 L, P {ω | queBadMat L W ((W * L) ^ 2) τ E a (Hr ω)} ≤
      ENNReal.ofReal ε') :
    P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ w ∧ θ ≤ ‖blockM L W (hH ω) a0 α‖} ≤
      ENNReal.ofReal (5 * ε') := by
  have hcard : (sbSupport L).card ≤ 5 := Finset.card_le_five
  have hne : (sbSupport L).Nonempty := ⟨(0, 0), by simp [sbSupport]⟩
  have hsub : {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ w ∧ θ ≤ ‖blockM L W (hH ω) a0 α‖} ⊆
      ⋃ u ∈ sbSupport L, {ω | queBadMat L W ((W * L) ^ 2) τ E (a0 + u) (Hr ω)} := by
    rintro ω ⟨α, hα, hM⟩
    set q : Z2 L → ℂ := fun a => (((W * L) ^ 2 : ℕ) : ℂ) *
      (star (fun x => (hH ω).eigenvectorBasis α x) ⬝ᵥ
        ((Epaper L W a - ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx L W) (Idx L W) ℂ)) *ᵥ
          (fun x => (hH ω).eigenvectorBasis α x))) with hq
    have hMx : blockM L W (hH ω) a0 α = (1 / 5 : ℂ) * ∑ u ∈ sbSupport L, q (a0 + u) := by
      simp only [blockM, hq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    have hex : ∃ u ∈ sbSupport L, θ ≤ ‖q (a0 + u)‖ := by
      by_contra hno
      push Not at hno
      have h1 : ∑ u ∈ sbSupport L, ‖q (a0 + u)‖ < ∑ _u ∈ sbSupport L, θ :=
        Finset.sum_lt_sum_of_nonempty hne hno
      have h3 : ‖blockM L W (hH ω) a0 α‖ ≤ (1 / 5) * ∑ u ∈ sbSupport L, ‖q (a0 + u)‖ := by
        rw [hMx, norm_mul]
        have : ‖(1 / 5 : ℂ)‖ = 1 / 5 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have h4 : ((sbSupport L).card : ℝ) * θ ≤ 5 * θ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hθ
      linarith
    obtain ⟨u, hu, hqu⟩ := hex
    refine Set.mem_biUnion hu ⟨_, _, isOrthoEigenbasis_eigenvectorBasis (hH ω), α, α,
      (hα.trans hw), (hα.trans hw), ?_⟩
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

end RBM.Univ
