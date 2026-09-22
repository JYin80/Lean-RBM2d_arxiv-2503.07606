/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolDiff

/-!
# First difference of the reciprocal Fourier multiplier

The reciprocal denominator inherits a first-difference bound from `Shat`.
This is the algebraic step in T21; annular comparison of the two denominator
norms is a separate scale estimate.
-/

namespace RBM

/-- The multiplier appearing in the Fourier representation of `Theta`. -/
noncomputable def invSymbolMultiplier (L : ℕ) [NeZero L]
    (ξ : ℂ) (p : Z2 L) : ℂ := (1 - ξ * Shat L p)⁻¹

/-- Exact reciprocal-difference quotient, valid for arbitrary momenta. -/
theorem invSymbolMultiplier_sub (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q : Z2 L) :
    invSymbolMultiplier L ξ q - invSymbolMultiplier L ξ p =
      ξ * (Shat L q - Shat L p) /
        ((1 - ξ * Shat L q) * (1 - ξ * Shat L p)) := by
  have hq : 1 - ξ * Shat L q ≠ 0 := one_sub_mul_Shat_ne_zero L hξ q
  have hp : 1 - ξ * Shat L p ≠ 0 := one_sub_mul_Shat_ne_zero L hξ p
  unfold invSymbolMultiplier
  field_simp [hq, hp]
  ring

/-- First-coordinate reciprocal difference with the exact denominator norms
retained for later annular ellipticity estimates. -/
theorem norm_invSymbolMultiplier_shift_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    ‖invSymbolMultiplier L ξ (p + (1, 0)) - invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * ((1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
        (2 * pstar L p.1 + 2 * Real.pi / (L : ℝ))) /
        (‖1 - ξ * Shat L (p + (1, 0))‖ * ‖1 - ξ * Shat L p‖) := by
  rw [invSymbolMultiplier_sub L hξ p (p + (1, 0)), norm_div, norm_mul, norm_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_Shat_shift_e1_le L hL p) (norm_nonneg ξ))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The corresponding second-coordinate estimate. -/
theorem norm_invSymbolMultiplier_shift_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    ‖invSymbolMultiplier L ξ (p + (0, 1)) - invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * ((1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
        (2 * pstar L p.2 + 2 * Real.pi / (L : ℝ))) /
        (‖1 - ξ * Shat L (p + (0, 1))‖ * ‖1 - ξ * Shat L p‖) := by
  rw [invSymbolMultiplier_sub L hξ p (p + (0, 1)), norm_div, norm_mul, norm_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_Shat_shift_e2_le L hL p) (norm_nonneg ξ))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A concrete nonzero reciprocal multiplier at `L=3`, `ξ=1/2`, `p=0`. -/
example : invSymbolMultiplier 3 (1 / 2) (0, 0) = 2 := by
  norm_num [invSymbolMultiplier, Shat]

/-- The exact difference formula applies at this nonzero parameter. -/
example : invSymbolMultiplier 3 (1 / 2) (1, 0) -
    invSymbolMultiplier 3 (1 / 2) (0, 0) =
      (1 / 2 : ℂ) * (Shat 3 (1, 0) - Shat 3 (0, 0)) /
        ((1 - (1 / 2 : ℂ) * Shat 3 (1, 0)) *
          (1 - (1 / 2 : ℂ) * Shat 3 (0, 0))) := by
  exact invSymbolMultiplier_sub 3 (by norm_num) (0, 0) (1, 0)

end RBM
