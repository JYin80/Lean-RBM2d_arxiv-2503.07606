/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolReciprocalDiff

/-!
# Exact second differences of the reciprocal Fourier multiplier

The three-point identity records both the second difference of `Shat` and
the product of first differences created by differentiating a reciprocal.
No annular denominator estimate is used here.
-/

namespace RBM

/-- A generic three-momentum exact second-difference identity. -/
theorem invSymbolMultiplier_second_diff (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q r : Z2 L) :
    invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p =
      ξ * (Shat L r - 2 * Shat L q + Shat L p) /
          ((1 - ξ * Shat L r) * (1 - ξ * Shat L q)) +
        ξ ^ 2 * (Shat L q - Shat L p) * (Shat L r - Shat L p) /
          ((1 - ξ * Shat L r) * (1 - ξ * Shat L q) *
            (1 - ξ * Shat L p)) := by
  have hr : 1 - ξ * Shat L r ≠ 0 := one_sub_mul_Shat_ne_zero L hξ r
  have hq : 1 - ξ * Shat L q ≠ 0 := one_sub_mul_Shat_ne_zero L hξ q
  have hp : 1 - ξ * Shat L p ≠ 0 := one_sub_mul_Shat_ne_zero L hξ p
  calc
    invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p =
      (invSymbolMultiplier L ξ r - invSymbolMultiplier L ξ q) -
        (invSymbolMultiplier L ξ q - invSymbolMultiplier L ξ p) := by ring
    _ = ξ * (Shat L r - Shat L q) /
          ((1 - ξ * Shat L r) * (1 - ξ * Shat L q)) -
        ξ * (Shat L q - Shat L p) /
          ((1 - ξ * Shat L q) * (1 - ξ * Shat L p)) := by
            rw [invSymbolMultiplier_sub L hξ q r,
              invSymbolMultiplier_sub L hξ p q]
    _ = _ := by
          field_simp [hr, hq, hp]
          ring

/-- Exact second forward difference in the first momentum coordinate. -/
theorem invSymbolMultiplier_second_diff_e1 (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    invSymbolMultiplier L ξ (p + (1, 0) + (1, 0)) -
        2 * invSymbolMultiplier L ξ (p + (1, 0)) +
        invSymbolMultiplier L ξ p =
      ξ * (Shat L (p + (1, 0) + (1, 0)) -
          2 * Shat L (p + (1, 0)) + Shat L p) /
          ((1 - ξ * Shat L (p + (1, 0) + (1, 0))) *
            (1 - ξ * Shat L (p + (1, 0)))) +
        ξ ^ 2 * (Shat L (p + (1, 0)) - Shat L p) *
            (Shat L (p + (1, 0) + (1, 0)) - Shat L p) /
          ((1 - ξ * Shat L (p + (1, 0) + (1, 0))) *
            (1 - ξ * Shat L (p + (1, 0))) *
            (1 - ξ * Shat L p)) :=
  invSymbolMultiplier_second_diff L hξ p (p + (1, 0)) (p + (1, 0) + (1, 0))

/-- Exact second forward difference in the second momentum coordinate. -/
theorem invSymbolMultiplier_second_diff_e2 (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    invSymbolMultiplier L ξ (p + (0, 1) + (0, 1)) -
        2 * invSymbolMultiplier L ξ (p + (0, 1)) +
        invSymbolMultiplier L ξ p =
      ξ * (Shat L (p + (0, 1) + (0, 1)) -
          2 * Shat L (p + (0, 1)) + Shat L p) /
          ((1 - ξ * Shat L (p + (0, 1) + (0, 1))) *
            (1 - ξ * Shat L (p + (0, 1)))) +
        ξ ^ 2 * (Shat L (p + (0, 1)) - Shat L p) *
            (Shat L (p + (0, 1) + (0, 1)) - Shat L p) /
          ((1 - ξ * Shat L (p + (0, 1) + (0, 1))) *
            (1 - ξ * Shat L (p + (0, 1))) *
            (1 - ξ * Shat L p)) :=
  invSymbolMultiplier_second_diff L hξ p (p + (0, 1)) (p + (0, 1) + (0, 1))

/-- Concrete nonzero-parameter instance on the three-by-three torus. -/
example :
    invSymbolMultiplier 3 (1 / 2) ((0, 0) + (1, 0) + (1, 0)) -
        2 * invSymbolMultiplier 3 (1 / 2) ((0, 0) + (1, 0)) +
        invSymbolMultiplier 3 (1 / 2) (0, 0) =
      (1 / 2 : ℂ) *
          (Shat 3 ((0, 0) + (1, 0) + (1, 0)) -
            2 * Shat 3 ((0, 0) + (1, 0)) + Shat 3 (0, 0)) /
          ((1 - (1 / 2 : ℂ) * Shat 3 ((0, 0) + (1, 0) + (1, 0))) *
            (1 - (1 / 2 : ℂ) * Shat 3 ((0, 0) + (1, 0)))) +
        (1 / 2 : ℂ) ^ 2 *
            (Shat 3 ((0, 0) + (1, 0)) - Shat 3 (0, 0)) *
            (Shat 3 ((0, 0) + (1, 0) + (1, 0)) - Shat 3 (0, 0)) /
          ((1 - (1 / 2 : ℂ) * Shat 3 ((0, 0) + (1, 0) + (1, 0))) *
            (1 - (1 / 2 : ℂ) * Shat 3 ((0, 0) + (1, 0))) *
            (1 - (1 / 2 : ℂ) * Shat 3 (0, 0))) :=
  invSymbolMultiplier_second_diff_e1 3 (by norm_num) (0, 0)

end RBM
