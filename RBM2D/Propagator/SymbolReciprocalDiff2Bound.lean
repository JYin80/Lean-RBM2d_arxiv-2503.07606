/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolReciprocalDiff2

/-!
# Second-difference bounds for the reciprocal Fourier multiplier

These estimates retain the three exact resolvent denominators. Their
annular lower bounds belong to a later step of Property 6.
-/

namespace RBM

/-- The one-step bound for a coordinate of the Fourier symbol. -/
noncomputable def reciprocalSymbolStepBound (L : ℕ) [NeZero L] (q : ZMod L) : ℝ :=
  (1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
    (2 * pstar L q + 2 * Real.pi / (L : ℝ))

/-- The uniform second-coordinate-difference bound for the Fourier symbol. -/
noncomputable def reciprocalSymbolSecondBound (L : ℕ) [NeZero L] : ℝ :=
  (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 2

/-- A three-point bound before specializing the coordinate shifts. -/
theorem norm_invSymbolMultiplier_second_diff_le (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q r : Z2 L)
    {A B C : ℝ}
    (hA : ‖Shat L r - 2 * Shat L q + Shat L p‖ ≤ A)
    (hB : ‖Shat L q - Shat L p‖ ≤ B)
    (hC : ‖Shat L r - Shat L p‖ ≤ C) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * A /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * B * C /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  rw [invSymbolMultiplier_second_diff L hξ p q r]
  calc
    _ ≤ ‖ξ * (Shat L r - 2 * Shat L q + Shat L p) /
          ((1 - ξ * Shat L r) * (1 - ξ * Shat L q))‖ +
        ‖ξ ^ 2 * (Shat L q - Shat L p) * (Shat L r - Shat L p) /
          ((1 - ξ * Shat L r) * (1 - ξ * Shat L q) *
            (1 - ξ * Shat L p))‖ := norm_add_le _ _
    _ = ‖ξ‖ * ‖Shat L r - 2 * Shat L q + Shat L p‖ /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * ‖Shat L q - Shat L p‖ * ‖Shat L r - Shat L p‖ /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := by
          simp only [norm_div, norm_mul, norm_pow]
    _ ≤ _ := by
      gcongr

/-- Explicit denominator-preserving second-difference bound in coordinate one. -/
theorem norm_invSymbolMultiplier_second_diff_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q r : Z2 L)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0)) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
            (reciprocalSymbolStepBound L p.1 +
              reciprocalSymbolStepBound L q.1) /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := by
  have hA : ‖Shat L r - 2 * Shat L q + Shat L p‖ ≤
      reciprocalSymbolSecondBound L := by
    rw [hr, hq]
    exact norm_Shat_second_diff_e1_le L hL p
  have hB : ‖Shat L q - Shat L p‖ ≤ reciprocalSymbolStepBound L p.1 := by
    rw [hq]
    exact norm_Shat_shift_e1_le L hL p
  have hC : ‖Shat L r - Shat L p‖ ≤
      reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1 := by
    calc
      _ = ‖(Shat L q - Shat L p) + (Shat L r - Shat L q)‖ := by
        congr 1; ring
      _ ≤ ‖Shat L q - Shat L p‖ + ‖Shat L r - Shat L q‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hB (by
        rw [hr]
        exact norm_Shat_shift_e1_le L hL q)
  exact norm_invSymbolMultiplier_second_diff_le L hξ p q r hA hB hC

/-- Explicit denominator-preserving second-difference bound in coordinate two. -/
theorem norm_invSymbolMultiplier_second_diff_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q r : Z2 L)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1)) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.2 *
            (reciprocalSymbolStepBound L p.2 +
              reciprocalSymbolStepBound L q.2) /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := by
  have hA : ‖Shat L r - 2 * Shat L q + Shat L p‖ ≤
      reciprocalSymbolSecondBound L := by
    rw [hr, hq]
    exact norm_Shat_second_diff_e2_le L hL p
  have hB : ‖Shat L q - Shat L p‖ ≤ reciprocalSymbolStepBound L p.2 := by
    rw [hq]
    exact norm_Shat_shift_e2_le L hL p
  have hC : ‖Shat L r - Shat L p‖ ≤
      reciprocalSymbolStepBound L p.2 + reciprocalSymbolStepBound L q.2 := by
    calc
      _ = ‖(Shat L q - Shat L p) + (Shat L r - Shat L q)‖ := by
        congr 1; ring
      _ ≤ ‖Shat L q - Shat L p‖ + ‖Shat L r - Shat L q‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hB (by
        rw [hr]
        exact norm_Shat_shift_e2_le L hL q)
  exact norm_invSymbolMultiplier_second_diff_le L hξ p q r hA hB hC

/-- The coordinate-one estimate has a concrete nonzero resolvent parameter. -/
example :
    let p : Z2 3 := (0, 0)
    let q := p + (1, 0)
    let r := q + (1, 0)
    ‖invSymbolMultiplier 3 (1 / 2) r -
        2 * invSymbolMultiplier 3 (1 / 2) q +
        invSymbolMultiplier 3 (1 / 2) p‖ ≤
      ‖(1 / 2 : ℂ)‖ * reciprocalSymbolSecondBound 3 /
          (‖1 - (1 / 2 : ℂ) * Shat 3 r‖ *
            ‖1 - (1 / 2 : ℂ) * Shat 3 q‖) +
        ‖(1 / 2 : ℂ)‖ ^ 2 * reciprocalSymbolStepBound 3 p.1 *
            (reciprocalSymbolStepBound 3 p.1 +
              reciprocalSymbolStepBound 3 q.1) /
          (‖1 - (1 / 2 : ℂ) * Shat 3 r‖ *
            ‖1 - (1 / 2 : ℂ) * Shat 3 q‖ *
            ‖1 - (1 / 2 : ℂ) * Shat 3 p‖) := by
  exact norm_invSymbolMultiplier_second_diff_e1_le 3 (by norm_num)
    (by norm_num) (0, 0) ((0, 0) + (1, 0))
    ((0, 0) + (1, 0) + (1, 0)) rfl rfl

end RBM
