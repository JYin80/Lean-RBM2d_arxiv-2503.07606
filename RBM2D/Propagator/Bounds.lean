/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Basic

/-!
# Norm bounds on the propagator

Formalization of the crude `ℓ^1` and `ℓ^∞` bounds on `Θ^(B)_ξ` used in Sections
3--4 of the two-dimensional random band matrix paper (the analogues of (3.35)
and (3.36) of [YY_25]).

The `ℓ^∞` operator norm of a matrix is the maximum of its `ℓ^1` row norms
(`Matrix.linfty_opNorm_def`), so `‖Θ_ξ‖` is exactly `max_a ∑_b |(Θ_ξ)_{ab}|`,
the `ℓ^1` row norm of `Θ_ξ`.  Summing the Neumann series gives the bound
`(1 - ‖ξ‖)⁻¹`; with `ξ = t|m|²` this is the `η_t^{-1}` bound and with `ξ = tm²`
it is the `O(1)` bound.

These bounds are **not** the sharp ones: the sharp statements are properties 5
and 6 of `lem_propTH`, proved by Fourier analysis in Section 8, where the decay
length is `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)` rather than `(1 - |ξ|)^{-1}`.  The two
differ enormously in the regime `ξ = t m²` that the paper cares about.
-/

namespace RBM

open Matrix
open scoped Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- Any entry of a matrix is bounded by its `ℓ^∞` operator norm. -/
theorem norm_entry_le_norm (M : Matrix (Z2 L) (Z2 L) ℂ) (a b : Z2 L) : ‖M a b‖ ≤ ‖M‖ := by
  have hrow : ∑ j : Z2 L, ‖M a j‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ a)
  have hb : ‖M a b‖₊ ≤ ∑ j : Z2 L, ‖M a j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M a j‖₊) (fun _ _ => by simp) (Finset.mem_univ b)
  exact_mod_cast hb.trans hrow

theorem norm_smul_SB (hL : 3 ≤ L) (ξ : ℂ) : ‖ξ • SB L‖ = ‖ξ‖ := by
  rw [norm_smul, norm_SB L hL, mul_one]

theorem summable_norm_pow (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Summable fun k : ℕ => ‖(ξ • SB L) ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_pow_le _ k) ?_
  rw [norm_smul_SB L hL]
  exact summable_geometric_of_lt_one (norm_nonneg _) hξ

/-- The `ℓ^1` bound on the rows of the propagator, the `ℓ^1` row bound:
`max_a ∑_b |(Θ_ξ)_{ab}| ≤ (1 - ‖ξ‖)⁻¹`. -/
theorem norm_Theta_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ‖Theta L ξ‖ ≤ (1 - ‖ξ‖)⁻¹ := by
  have hgeom : Summable fun k : ℕ => ‖ξ‖ ^ k := summable_geometric_of_lt_one (norm_nonneg _) hξ
  have hle : ∀ k : ℕ, ‖(ξ • SB L) ^ k‖ ≤ ‖ξ‖ ^ k := by
    intro k
    calc ‖(ξ • SB L) ^ k‖ ≤ ‖ξ • SB L‖ ^ k := norm_pow_le _ k
      _ = ‖ξ‖ ^ k := by rw [norm_smul_SB L hL]
  rw [Theta_eq_tsum L hL hξ]
  calc ‖∑' k : ℕ, (ξ • SB L) ^ k‖
      ≤ ∑' k : ℕ, ‖(ξ • SB L) ^ k‖ := norm_tsum_le_tsum_norm (summable_norm_pow L hL hξ)
    _ ≤ ∑' k : ℕ, ‖ξ‖ ^ k := Summable.tsum_le_tsum hle (summable_norm_pow L hL hξ) hgeom
    _ = (1 - ‖ξ‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg _) hξ

theorem sum_nnnorm_Theta_row_le (_hL : 3 ≤ L) {ξ : ℂ} (_hξ : ‖ξ‖ < 1) (a : Z2 L) :
    ∑ b : Z2 L, ‖Theta L ξ a b‖₊ ≤ ‖Theta L ξ‖₊ := by
  rw [Matrix.linfty_opNNNorm_def]
  exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖Theta L ξ i j‖₊) (Finset.mem_univ a)

/-- Entrywise `ℓ^1` form of `norm_Theta_le`, the literal row-sum form. -/
theorem sum_norm_Theta_row_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a : Z2 L) :
    ∑ b : Z2 L, ‖Theta L ξ a b‖ ≤ (1 - ‖ξ‖)⁻¹ := by
  refine le_trans ?_ (norm_Theta_le L hL hξ)
  have h : ((∑ b : Z2 L, ‖Theta L ξ a b‖₊ : NNReal) : ℝ) ≤ ((‖Theta L ξ‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (sum_nnnorm_Theta_row_le L hL hξ a)
  simpa using h

/-- The entries of the propagator are bounded. -/
theorem norm_Theta_apply_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤ (1 - ‖ξ‖)⁻¹ := by
  refine le_trans ?_ (sum_norm_Theta_row_le L hL hξ a)
  exact Finset.single_le_sum (fun c _ => norm_nonneg (Theta L ξ a c)) (Finset.mem_univ b)

end RBM
