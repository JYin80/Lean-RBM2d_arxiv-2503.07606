/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolReciprocalDiff2Bound
import RBM2D.Propagator.SymbolShiftAnnulus

/-!
# A low-momentum reciprocal-symbol difference bound

This estimate applies when the strong grid margin of the separated-annulus
bound fails: `|p|_*² ≤ 16 (2π/L)²`. It uses only the positive mass
`κ(ξ)² = |1-ξ|` in the denominator, so its constant grows as `ξ → 1`.
-/

namespace RBM

/-- A uniform positive denominator scale for every momentum. -/
noncomputable def symbolLowDenomScale (ξ : ℂ) : ℝ :=
  (1 / 9 : ℝ) * (kappa ξ) ^ 2

theorem symbolLowDenomScale_pos {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    0 < symbolLowDenomScale ξ := by
  have hk := kappa_pos hξ
  unfold symbolLowDenomScale
  positivity

theorem symbolLowDenomScale_le (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    symbolLowDenomScale ξ ≤ ‖1 - ξ * Shat L p‖ := by
  have hq := qsym_nonneg L p
  have h := norm_one_sub_mul_Shat_ge_kappa L hξ p
  unfold symbolLowDenomScale
  linarith

private theorem pstar_shift_one_le_low (L : ℕ) [NeZero L] (hL : 3 ≤ L)
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

private theorem pstar_coord_le_four_grid (L : ℕ) [NeZero L]
    (p : Z2 L) {i : ZMod L}
    (hi : i = p.1 ∨ i = p.2)
    (hlow : pstar2 L p ≤ 16 * (symbolGridStep L) ^ 2) :
    pstar L i ≤ 4 * symbolGridStep L := by
  have hg : 0 ≤ 4 * symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hi0 : 0 ≤ pstar L i := pstar_nonneg L i
  have hsq : (pstar L i) ^ 2 ≤ (4 * symbolGridStep L) ^ 2 := by
    rcases hi with rfl | rfl
    · have hother := sq_nonneg (pstar L p.2)
      dsimp [pstar2] at hlow
      nlinarith
    · have hother := sq_nonneg (pstar L p.1)
      dsimp [pstar2] at hlow
      nlinarith
  exact (sq_le_sq₀ hi0 hg).mp hsq

private theorem stepBound_le_low (L : ℕ) [NeZero L]
    (u : ZMod L) (hu : pstar L u ≤ 4 * symbolGridStep L) :
    reciprocalSymbolStepBound L u ≤
      (9 / 5 : ℝ) * (symbolGridStep L) ^ 2 := by
  have hg : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  have hnum : 2 * pstar L u + symbolGridStep L ≤
      9 * symbolGridStep L := by linarith
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L *
        (9 * symbolGridStep L) := by gcongr
    _ = _ := by ring

private theorem stepBound_shift_le_low (L : ℕ) [NeZero L]
    (u : ZMod L) (hu : pstar L u ≤ 5 * symbolGridStep L) :
    reciprocalSymbolStepBound L u ≤
      (11 / 5 : ℝ) * (symbolGridStep L) ^ 2 := by
  have hg : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hdef : reciprocalSymbolStepBound L u =
      (1 / 5 : ℝ) * symbolGridStep L *
        (2 * pstar L u + symbolGridStep L) := by
    unfold reciprocalSymbolStepBound symbolGridStep
    ring
  rw [hdef]
  have hnum : 2 * pstar L u + symbolGridStep L ≤
      11 * symbolGridStep L := by linarith
  calc
    _ ≤ (1 / 5 : ℝ) * symbolGridStep L *
        (11 * symbolGridStep L) := by gcongr
    _ = _ := by ring

private theorem low_step_product_le {a b G : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ (9 / 5 : ℝ) * G ^ 2)
    (hb : b ≤ (11 / 5 : ℝ) * G ^ 2) :
    a * (a + b) ≤ (36 / 5 : ℝ) * G ^ 4 := by
  have hsum : a + b ≤ 4 * G ^ 2 := by linarith
  calc
    a * (a + b) ≤ ((9 / 5 : ℝ) * G ^ 2) * (4 * G ^ 2) := by
      gcongr
    _ = (36 / 5 : ℝ) * G ^ 4 := by ring

private theorem two_fraction_le_low
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

/-- A low-frequency bound for the second difference in coordinate one.
It applies even when the shifted momenta cross zero. -/
theorem norm_invSymbolMultiplier_second_diff_e1_low_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlow : pstar2 L p ≤ 16 * (symbolGridStep L) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * ((2 / 5 : ℝ) * (symbolGridStep L) ^ 2) /
          (symbolLowDenomScale ξ) ^ 2 +
        ‖ξ‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep L) ^ 4) /
          (symbolLowDenomScale ξ) ^ 3 := by
  have hpre := norm_invSymbolMultiplier_second_diff_e1_le L hL hξ p q r hq hr
  have hp := pstar_coord_le_four_grid L p (Or.inl rfl) hlow
  have hqangle : pstar L q.1 ≤ 5 * symbolGridStep L := by
    have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
    rw [hq₁]
    linarith [pstar_shift_one_le_low L hL p.1]
  have hstepP := stepBound_le_low L p.1 hp
  have hstepQ := stepBound_shift_le_low L q.1 hqangle
  have hstepP0 : 0 ≤ reciprocalSymbolStepBound L p.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL p)
  have hstepQ0 : 0 ≤ reciprocalSymbolStepBound L q.1 :=
    le_trans (norm_nonneg _) (norm_Shat_shift_e1_le L hL q)
  have hprod := low_step_product_le hstepP0 hstepQ0 hstepP hstepQ
  have hD : 0 < symbolLowDenomScale ξ := symbolLowDenomScale_pos hξ
  have hDp := symbolLowDenomScale_le L hξ p
  have hDq := symbolLowDenomScale_le L hξ q
  have hDr := symbolLowDenomScale_le L hξ r
  have hA : 0 ≤ ‖ξ‖ * reciprocalSymbolSecondBound L := by
    unfold reciprocalSymbolSecondBound
    positivity
  have hB : 0 ≤ ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
      (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) := by
    positivity
  have hfrac := two_fraction_le_low hA hB hD hDr hDq hDp
  have hsecond : reciprocalSymbolSecondBound L =
      (2 / 5 : ℝ) * (symbolGridStep L) ^ 2 := by
    unfold reciprocalSymbolSecondBound symbolGridStep
    ring
  have hscaled : ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
      (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) ≤
      ‖ξ‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep L) ^ 4) := by
    calc
      _ = ‖ξ‖ ^ 2 * (reciprocalSymbolStepBound L p.1 *
          (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  calc
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖) +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
          (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) /
          (‖1 - ξ * Shat L r‖ * ‖1 - ξ * Shat L q‖ *
            ‖1 - ξ * Shat L p‖) := hpre
    _ ≤ ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolLowDenomScale ξ) ^ 2 +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
          (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) /
          (symbolLowDenomScale ξ) ^ 3 := hfrac
    _ ≤ _ := by
      rw [hsecond]
      apply add_le_add_right
      exact div_le_div_of_nonneg_right hscaled (pow_nonneg hD.le 3)

/-- The zero momentum is a concrete low-frequency input at nonzero `ξ`. -/
example :
    let p : Z2 3 := (0, 0)
    let q := p + (1, 0)
    let r := q + (1, 0)
    ‖invSymbolMultiplier 3 (1 / 2) r -
        2 * invSymbolMultiplier 3 (1 / 2) q +
        invSymbolMultiplier 3 (1 / 2) p‖ ≤
      ‖(1 / 2 : ℂ)‖ * ((2 / 5 : ℝ) * (symbolGridStep 3) ^ 2) /
          (symbolLowDenomScale (1 / 2)) ^ 2 +
        ‖(1 / 2 : ℂ)‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep 3) ^ 4) /
          (symbolLowDenomScale (1 / 2)) ^ 3 := by
  apply norm_invSymbolMultiplier_second_diff_e1_low_le 3 (by norm_num)
    (by norm_num) (0, 0) ((0, 0) + (1, 0))
    ((0, 0) + (1, 0) + (1, 0)) rfl rfl
  simp only [pstar2, pstar, zdist_zero, Nat.cast_zero, mul_zero, zero_div]
  nlinarith [sq_nonneg (symbolGridStep 3)]

end RBM
