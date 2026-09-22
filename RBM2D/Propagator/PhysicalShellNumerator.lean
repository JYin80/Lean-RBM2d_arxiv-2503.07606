/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PhysicalShellDenominator

/-!
# Second reciprocal-symbol differences on physical dyadic shells

The shell radius is `R_j = (2π) dyad j`. The explicit grid, inner, and outer
margins suffice to control both numerator factors and all three resolvent
denominators. No dyadic summation is included here.
-/

namespace RBM

private theorem pstar_shift_one_le_physical (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
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

private theorem pstar_coords_le_physical_outer (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (houter : pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2) :
    pstar L p.1 ≤ 2 * physicalShellRadius j ∧
      pstar L p.2 ≤ 2 * physicalShellRadius j := by
  have hp₁ := pstar_nonneg L p.1
  have hp₂ := pstar_nonneg L p.2
  have hr : 0 ≤ 2 * physicalShellRadius j := by
    have := (physicalShellRadius_pos j).le
    positivity
  have hs₁ : (pstar L p.1) ^ 2 ≤ (2 * physicalShellRadius j) ^ 2 := by
    dsimp [pstar2] at houter
    nlinarith [sq_nonneg (pstar L p.2)]
  have hs₂ : (pstar L p.2) ^ 2 ≤ (2 * physicalShellRadius j) ^ 2 := by
    dsimp [pstar2] at houter
    nlinarith [sq_nonneg (pstar L p.1)]
  exact ⟨(sq_le_sq₀ hp₁ hr).mp hs₁, (sq_le_sq₀ hp₂ hr).mp hs₂⟩

/-- A separated physical shell is at least two grid steps wide. -/
theorem two_symbolGridStep_le_physicalShellRadius (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2) :
    2 * symbolGridStep L ≤ physicalShellRadius j := by
  have hg : 0 ≤ 2 * symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hr := (physicalShellRadius_pos j).le
  apply (sq_le_sq₀ hg hr).mp
  nlinarith

private theorem stepBound_le_physical (L : ℕ) [NeZero L]
    (u : ZMod L) (j : ℕ)
    (hu : pstar L u ≤ 2 * physicalShellRadius j)
    (hg : 2 * symbolGridStep L ≤ physicalShellRadius j) :
    reciprocalSymbolStepBound L u ≤
      symbolGridStep L * physicalShellRadius j := by
  have hgrid : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hnum : 2 * pstar L u + symbolGridStep L ≤
      5 * physicalShellRadius j := by linarith
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L *
        (5 * physicalShellRadius j) := by gcongr
    _ = _ := by ring

private theorem stepBound_shift_le_physical (L : ℕ) [NeZero L]
    (u : ZMod L) (j : ℕ)
    (hu : pstar L u ≤ 2 * physicalShellRadius j + symbolGridStep L)
    (hg : 2 * symbolGridStep L ≤ physicalShellRadius j) :
    reciprocalSymbolStepBound L u ≤
      (6 / 5 : ℝ) * symbolGridStep L * physicalShellRadius j := by
  have hgrid : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hnum : 2 * pstar L u + symbolGridStep L ≤
      6 * physicalShellRadius j := by linarith
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L *
        (6 * physicalShellRadius j) := by gcongr
    _ = _ := by ring

private theorem physical_step_product_le {a b R : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hR : 0 ≤ R)
    (ha : a ≤ R) (hb : b ≤ (6 / 5 : ℝ) * R) :
    a * (a + b) ≤ (11 / 5 : ℝ) * R ^ 2 := by
  have hsum : a + b ≤ (11 / 5 : ℝ) * R := by linarith
  calc
    a * (a + b) ≤ R * ((11 / 5 : ℝ) * R) := by gcongr
    _ = (11 / 5 : ℝ) * R ^ 2 := by ring

private theorem two_fraction_le_physical
    {A B d₁ d₂ d₃ D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 < D)
    (h₁ : D ≤ d₁) (h₂ : D ≤ d₂) (h₃ : D ≤ d₃) :
    A / (d₁ * d₂) + B / (d₁ * d₂ * d₃) ≤
      A / D ^ 2 + B / D ^ 3 := by
  have hden2 : D ^ 2 ≤ d₁ * d₂ := by
    calc
      D ^ 2 = D * D := by ring
      _ ≤ d₁ * d₂ := by gcongr; linarith
  have hden3 : D ^ 3 ≤ d₁ * d₂ * d₃ := by
    calc
      D ^ 3 = D ^ 2 * D := by ring
      _ ≤ (d₁ * d₂) * d₃ := by gcongr; nlinarith
  gcongr

private theorem second_diff_le_of_physical_bounds (L : ℕ) [NeZero L]
    {ξ : ℂ} (p q r : Z2 L) (j : ℕ) (a b : ℝ)
    (hraw : ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * a * (a + b) /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖))
    (hden : physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L q‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L r‖)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ symbolGridStep L * physicalShellRadius j)
    (hb : b ≤ (6 / 5 : ℝ) * symbolGridStep L * physicalShellRadius j) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (physicalShellDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
            (symbolGridStep L * physicalShellRadius j) ^ 2) /
          (physicalShellDenomScale ξ j) ^ 3 := by
  obtain ⟨hDp, hDq, hDr⟩ := hden
  have hD := physicalShellDenomScale_pos ξ j
  have hA : 0 ≤ ‖ξ‖ * reciprocalSymbolSecondBound L := by
    unfold reciprocalSymbolSecondBound
    positivity
  have hB : 0 ≤ ‖ξ‖ ^ 2 * a * (a + b) := by positivity
  have hfrac := two_fraction_le_physical hA hB hD hDr hDq hDp
  have hR : 0 ≤ symbolGridStep L * physicalShellRadius j := by
    have hg : 0 ≤ symbolGridStep L := by unfold symbolGridStep; positivity
    exact mul_nonneg hg (physicalShellRadius_pos j).le
  have hb' : b ≤ (6 / 5 : ℝ) *
      (symbolGridStep L * physicalShellRadius j) := by
    simpa only [mul_assoc] using hb
  have hprod := physical_step_product_le ha0 hb0 hR ha hb'
  have hscaled : ‖ξ‖ ^ 2 * a * (a + b) ≤
      ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
        (symbolGridStep L * physicalShellRadius j) ^ 2) := by
    calc
      _ = ‖ξ‖ ^ 2 * (a * (a + b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  calc
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * a * (a + b) /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := hraw
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (physicalShellDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * a * (a + b) /
          (physicalShellDenomScale ξ j) ^ 3 := hfrac
    _ ≤ _ := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right hscaled (pow_nonneg hD.le 3)

/-- First-coordinate second reciprocal difference on a physical shell. -/
theorem norm_invSymbolMultiplier_second_diff_e1_physical_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (physicalShellDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
            (symbolGridStep L * physicalShellRadius j) ^ 2) /
          (physicalShellDenomScale ξ j) ^ 3 := by
  have ⟨hp₁, _⟩ := pstar_coords_le_physical_outer L p j houter
  have hg := two_symbolGridStep_le_physicalShellRadius L p j hlarge houter
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hqangle : pstar L q.1 ≤
      2 * physicalShellRadius j + symbolGridStep L := by
    rw [hq₁]
    linarith [pstar_shift_one_le_physical L hL p.1]
  have ha := stepBound_le_physical L p.1 j hp₁ hg
  have hb := stepBound_shift_le_physical L q.1 j hqangle hg
  have ha0 : 0 ≤ reciprocalSymbolStepBound L p.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL p)
  have hb0 : 0 ≤ reciprocalSymbolStepBound L q.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL q)
  exact second_diff_le_of_physical_bounds L p q r j
    (reciprocalSymbolStepBound L p.1) (reciprocalSymbolStepBound L q.1)
    (norm_invSymbolMultiplier_second_diff_e1_le L hL hξ p q r hq hr)
    (physicalShellDenomScale_le_e1_triple L hL hξ p q r j hq hr hlarge hinner)
    ha0 hb0 ha hb

/-- Second-coordinate second reciprocal difference on a physical shell. -/
theorem norm_invSymbolMultiplier_second_diff_e2_physical_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p)
    (houter : pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (physicalShellDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
            (symbolGridStep L * physicalShellRadius j) ^ 2) /
          (physicalShellDenomScale ξ j) ^ 3 := by
  have ⟨_, hp₂⟩ := pstar_coords_le_physical_outer L p j houter
  have hg := two_symbolGridStep_le_physicalShellRadius L p j hlarge houter
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hqangle : pstar L q.2 ≤
      2 * physicalShellRadius j + symbolGridStep L := by
    rw [hq₂]
    linarith [pstar_shift_one_le_physical L hL p.2]
  have ha := stepBound_le_physical L p.2 j hp₂ hg
  have hb := stepBound_shift_le_physical L q.2 j hqangle hg
  have ha0 : 0 ≤ reciprocalSymbolStepBound L p.2 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e2_le L hL p)
  have hb0 : 0 ≤ reciprocalSymbolStepBound L q.2 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e2_le L hL q)
  exact second_diff_le_of_physical_bounds L p q r j
    (reciprocalSymbolStepBound L p.2) (reciprocalSymbolStepBound L q.2)
    (norm_invSymbolMultiplier_second_diff_e2_le L hL hξ p q r hq hr)
    (physicalShellDenomScale_le_e2_triple L hL hξ p q r j hq hr hlarge hinner)
    ha0 hb0 ha hb

/-- The inner, outer, and grid margins hold simultaneously for a nonzero mode. -/
example :
    16 * (symbolGridStep 100) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) ∧
      4 * (physicalShellRadius (4 + 1)) ^ 2 ≤
        pstar2 100 ((10, 0) : Z2 100) ∧
      pstar2 100 ((10, 0) : Z2 100) ≤
        (2 * physicalShellRadius 4) ^ 2 := by
  have hz : zdist 100 (10 : ZMod 100) = 10 := by decide
  simp only [symbolGridStep, physicalShellRadius, pstar2, pstar, dyad,
    hz, zdist_zero]
  constructor
  · norm_num
    nlinarith [sq_nonneg Real.pi]
  constructor
  · norm_num
    nlinarith [sq_nonneg Real.pi]
  · norm_num
    nlinarith [sq_nonneg Real.pi]

end RBM

#print axioms RBM.two_symbolGridStep_le_physicalShellRadius
#print axioms RBM.norm_invSymbolMultiplier_second_diff_e1_physical_le
#print axioms RBM.norm_invSymbolMultiplier_second_diff_e2_physical_le
