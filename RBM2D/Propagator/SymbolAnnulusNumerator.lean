/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolReciprocalAnnulusBound

/-!
# Numerator bounds on a separated dyadic momentum annulus

The outer-radius hypothesis bounds each coordinate of the momentum. Combined
with the previous inner margin, it also forces the grid step below the shell
radius. These statements concern separated shells only.
-/

namespace RBM

private theorem pstar_shift_one_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (u : ZMod L) :
    pstar L (u + 1) ≤ pstar L u + symbolGridStep L := by
  have hz := zdist_add_le L u (1 : ZMod L)
  have h1 := zdist_one_le L hL
  have hz' : (zdist L (u + 1) : ℝ) ≤ (zdist L u : ℝ) + 1 := by
    exact_mod_cast (show zdist L (u + 1) ≤ zdist L u + 1 by omega)
  have hg : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (u + 1) = symbolGridStep L * (zdist L (u + 1) : ℝ) := by
      unfold pstar symbolGridStep
      ring
    _ ≤ symbolGridStep L * ((zdist L u : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hz' hg
    _ = pstar L u + symbolGridStep L := by
      unfold pstar symbolGridStep
      ring

private theorem pstar_coords_le_outer (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    pstar L p.1 ≤ 2 * dyad j ∧ pstar L p.2 ≤ 2 * dyad j := by
  have h₁ : 0 ≤ pstar L p.1 := pstar_nonneg L p.1
  have h₂ : 0 ≤ pstar L p.2 := pstar_nonneg L p.2
  have hr : 0 ≤ 2 * dyad j := by
    have := dyad_nonneg j
    positivity
  have hs₁ : (pstar L p.1) ^ 2 ≤ (2 * dyad j) ^ 2 := by
    dsimp [pstar2] at houter
    nlinarith [sq_nonneg (pstar L p.2)]
  have hs₂ : (pstar L p.2) ^ 2 ≤ (2 * dyad j) ^ 2 := by
    dsimp [pstar2] at houter
    nlinarith [sq_nonneg (pstar L p.1)]
  exact ⟨(sq_le_sq₀ h₁ hr).mp hs₁, (sq_le_sq₀ h₂ hr).mp hs₂⟩

/-- The strong inner margin and a dyadic outer radius force the frequency
grid step below half the shell radius. -/
theorem two_symbolGridStep_le_dyad (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    2 * symbolGridStep L ≤ dyad j := by
  have hg : 0 ≤ 2 * symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hr := dyad_nonneg j
  apply (sq_le_sq₀ hg hr).mp
  nlinarith

private theorem stepBound_le_shell (L : ℕ) [NeZero L]
    (u : ZMod L) (j : ℕ)
    (hu : pstar L u ≤ 2 * dyad j)
    (hg : 2 * symbolGridStep L ≤ dyad j) :
    reciprocalSymbolStepBound L u ≤ symbolGridStep L * dyad j := by
  have hgrid : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hnum : 2 * pstar L u + symbolGridStep L ≤ 5 * dyad j := by
    linarith
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L * (5 * dyad j) := by
      gcongr
    _ = _ := by ring

private theorem stepBound_shift_le_shell (L : ℕ) [NeZero L]
    (u : ZMod L) (j : ℕ)
    (hu : pstar L u ≤ 2 * dyad j + symbolGridStep L)
    (hg : 2 * symbolGridStep L ≤ dyad j) :
    reciprocalSymbolStepBound L u ≤
      (6 / 5 : ℝ) * symbolGridStep L * dyad j := by
  have hgrid : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hnum : 2 * pstar L u + symbolGridStep L ≤ 6 * dyad j := by
    linarith
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L * (6 * dyad j) := by
      gcongr
    _ = _ := by ring

/-- Numerator bounds for the first-coordinate second difference. -/
theorem reciprocalSymbolStepBound_e1_shell (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    reciprocalSymbolStepBound L p.1 ≤ symbolGridStep L * dyad j ∧
      reciprocalSymbolStepBound L q.1 ≤
        (6 / 5 : ℝ) * symbolGridStep L * dyad j := by
  have ⟨hp₁, _⟩ := pstar_coords_le_outer L p j houter
  have hg := two_symbolGridStep_le_dyad L p j hlarge houter
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  constructor
  · exact stepBound_le_shell L p.1 j hp₁ hg
  · apply stepBound_shift_le_shell L q.1 j
    · rw [hq₁]
      linarith [pstar_shift_one_le L hL p.1]
    · exact hg

/-- Numerator bounds for the second-coordinate second difference. -/
theorem reciprocalSymbolStepBound_e2_shell (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    reciprocalSymbolStepBound L p.2 ≤ symbolGridStep L * dyad j ∧
      reciprocalSymbolStepBound L q.2 ≤
        (6 / 5 : ℝ) * symbolGridStep L * dyad j := by
  have ⟨_, hp₂⟩ := pstar_coords_le_outer L p j houter
  have hg := two_symbolGridStep_le_dyad L p j hlarge houter
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  constructor
  · exact stepBound_le_shell L p.2 j hp₂ hg
  · apply stepBound_shift_le_shell L q.2 j
    · rw [hq₂]
      linarith [pstar_shift_one_le L hL p.2]
    · exact hg

private theorem shell_step_product_le {a b R : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hR : 0 ≤ R)
    (ha : a ≤ R) (hb : b ≤ (6 / 5 : ℝ) * R) :
    a * (a + b) ≤ (11 / 5 : ℝ) * R ^ 2 := by
  have hsum : a + b ≤ (11 / 5 : ℝ) * R := by linarith
  calc
    a * (a + b) ≤ R * ((11 / 5 : ℝ) * R) := by
      gcongr
    _ = (11 / 5 : ℝ) * R ^ 2 := by ring

/-- First-coordinate annular estimate with the numerator at grid-step times
shell-radius scale. -/
theorem norm_invSymbolMultiplier_second_diff_e1_shell_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
            (symbolGridStep L * dyad j) ^ 2) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := by
  have hpre := norm_invSymbolMultiplier_second_diff_e1_annulus_le
    L hL hξ p q r j hq hr hlarge hinner
  have ⟨hstepP, hstepQ⟩ :=
    reciprocalSymbolStepBound_e1_shell L hL p q j hq hlarge houter
  have hstepP0 : 0 ≤ reciprocalSymbolStepBound L p.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL p)
  have hstepQ0 : 0 ≤ reciprocalSymbolStepBound L q.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL q)
  have hR : 0 ≤ symbolGridStep L * dyad j := by
    have hg : 0 ≤ symbolGridStep L := by unfold symbolGridStep; positivity
    exact mul_nonneg hg (dyad_nonneg j)
  have hstepQ' : reciprocalSymbolStepBound L q.1 ≤
      (6 / 5 : ℝ) * (symbolGridStep L * dyad j) := by
    simpa only [mul_assoc] using hstepQ
  have hprod := shell_step_product_le hstepP0 hstepQ0 hR hstepP hstepQ'
  have hscaled : ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
      (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) ≤
      ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) * (symbolGridStep L * dyad j) ^ 2) := by
    calc
      _ = ‖ξ‖ ^ 2 * (reciprocalSymbolStepBound L p.1 *
          (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  calc
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
            (reciprocalSymbolStepBound L p.1 +
              reciprocalSymbolStepBound L q.1) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := hpre
    _ ≤ _ := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right hscaled
        (pow_nonneg (symbolAnnulusDenomScale_pos ξ j).le 3)

/-- Second-coordinate counterpart of the annular shell numerator estimate. -/
theorem norm_invSymbolMultiplier_second_diff_e2_shell_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * dyad j) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
            (symbolGridStep L * dyad j) ^ 2) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := by
  have hpre := norm_invSymbolMultiplier_second_diff_e2_annulus_le
    L hL hξ p q r j hq hr hlarge hinner
  have ⟨hstepP, hstepQ⟩ :=
    reciprocalSymbolStepBound_e2_shell L hL p q j hq hlarge houter
  have hstepP0 : 0 ≤ reciprocalSymbolStepBound L p.2 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e2_le L hL p)
  have hstepQ0 : 0 ≤ reciprocalSymbolStepBound L q.2 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e2_le L hL q)
  have hR : 0 ≤ symbolGridStep L * dyad j := by
    have hg : 0 ≤ symbolGridStep L := by unfold symbolGridStep; positivity
    exact mul_nonneg hg (dyad_nonneg j)
  have hstepQ' : reciprocalSymbolStepBound L q.2 ≤
      (6 / 5 : ℝ) * (symbolGridStep L * dyad j) := by
    simpa only [mul_assoc] using hstepQ
  have hprod := shell_step_product_le hstepP0 hstepQ0 hR hstepP hstepQ'
  have hscaled : ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.2 *
      (reciprocalSymbolStepBound L p.2 + reciprocalSymbolStepBound L q.2) ≤
      ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) * (symbolGridStep L * dyad j) ^ 2) := by
    calc
      _ = ‖ξ‖ ^ 2 * (reciprocalSymbolStepBound L p.2 *
          (reciprocalSymbolStepBound L p.2 + reciprocalSymbolStepBound L q.2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  calc
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.2 *
            (reciprocalSymbolStepBound L p.2 +
              reciprocalSymbolStepBound L q.2) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := hpre
    _ ≤ _ := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right hscaled
        (pow_nonneg (symbolAnnulusDenomScale_pos ξ j).le 3)

/-- The inner margin, outer radius, and grid separation hold simultaneously
at a concrete nonzero momentum. -/
example :
    16 * (symbolGridStep 100) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) ∧
    4 * (dyad (1 + 1)) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) ∧
    pstar2 100 ((10, 0) : Z2 100) ≤ (2 * dyad 1) ^ 2 := by
  have hz : zdist 100 (10 : ZMod 100) = 10 := by decide
  simp only [symbolGridStep, pstar2, pstar, dyad, hz, zdist_zero]
  constructor
  · norm_num
    nlinarith [sq_nonneg Real.pi]
  constructor
  · norm_num
    nlinarith [Real.pi_gt_three]
  · norm_num
    rw [abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_lt_four]

end RBM
