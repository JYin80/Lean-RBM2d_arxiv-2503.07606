/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Green's function and its spectral decomposition

Formalization of the deterministic spectral input to the delocalization theorem
`MR:decol` of the two-dimensional random band matrix paper.

Nothing here depends on the dimension or on the band structure: it is the
standard eigenvector/resolvent identity that turns the diagonal of
the Green's function into information on the eigenvectors.

Let `H` be Hermitian with eigenvalues `λ_l` and orthonormal eigenvectors `ψ_l`, and
`G(z) = (H - z)⁻¹`.  For `η > 0`,
`|ψ_k(x)|² ≤ ∑_l η² |ψ_l(x)|² / ((λ_k - λ_l)² + η²) = η · Im G_xx(λ_k + iη)`.   (2.10)

Consequently a bound `|G_xx(λ_k + iη)| ≤ C` gives `|ψ_k(x)|² ≤ C η`.  In the paper the
bound on `G` comes from the local semicircle law `MR:locSC` with high probability
and `η = N^{-1+τ}`.  This file contains the spectral identities below; the eigenvector bound
itself is derived in `Main/DecolFromLocal.lean`.

## Main results

* `RBM.green_eq_spectral`       : `G(z) = U diag((λ - z)⁻¹) U*`
* `RBM.green_apply_self`        : `G_xx(z) = ∑_l |ψ_l(x)|² / (λ_l - z)`
* `RBM.im_green_apply_self`     : `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`
-/

namespace RBM

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- Spectral decomposition of the Green's function. -/
theorem green_eq_spectral {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- Diagonal entries of the Green's function: `G_xx(z) = ∑_l |ψ_l(x)|² / (λ_l - z)`. -/
theorem green_apply_self {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) (x : n) :
    green H z x x
      = ∑ l, (Complex.normSq (hH.eigenvectorBasis l x) : ℂ) / ((hH.eigenvalues l : ℂ) - z) := by
  rw [green_eq_spectral hH hz, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, star_apply, IsHermitian.eigenvectorUnitary_apply,
    Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

/-- `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`. -/
theorem im_green_apply_self (E : ℝ) {η : ℝ} (hη : η ≠ 0) (x : n) :
    (green H (E + η * Complex.I) x x).im
      = ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x)
          / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
  have hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hη this.symm
  rw [green_apply_self hH hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))
      = (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have him : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
  have hpos : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him]
  field_simp

end RBM
