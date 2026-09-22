/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffShell

/-!
# Resolvent denominators on physical dyadic momentum shells

The physical radius is `(2π) dyad j`. The two shifted frequencies retain a
quarter of the original squared momentum under the explicit grid margin, so
all three resolvent denominators share one ellipticity scale.
-/

namespace RBM

/-- The exact ellipticity scale at a physical annulus. -/
noncomputable def physicalShellDenomScale (ξ : ℂ) (j : ℕ) : ℝ :=
  4 / (45 * Real.pi ^ 2) *
    ((kappa ξ) ^ 2 + (physicalShellRadius (j + 1)) ^ 2)

theorem physicalShellDenomScale_pos (ξ : ℂ) (j : ℕ) :
    0 < physicalShellDenomScale ξ j := by
  have hr := physicalShellRadius_pos (j + 1)
  unfold physicalShellDenomScale
  positivity

/-- One physical inner-radius condition gives a resolvent denominator bound. -/
theorem physicalShellDenomScale_le (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) (j : ℕ)
    (hinner : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p) :
    physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ := by
  calc
    physicalShellDenomScale ξ j ≤
        4 / (45 * Real.pi ^ 2) *
          ((kappa ξ) ^ 2 + pstar2 L p) := by
            unfold physicalShellDenomScale
            gcongr
    _ ≤ ‖1 - ξ * Shat L p‖ := norm_one_sub_mul_Shat_ge_pstar L hξ p

/-- All three first-coordinate second-difference denominators have the same
physical-shell lower bound. -/
theorem physicalShellDenomScale_le_e1_triple (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p) :
    physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L q‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L r‖ := by
  obtain ⟨hshiftq, hshiftr⟩ :=
    pstar2_shift_e1_ge_quarter L hL p q r hq hr hlarge
  have hp : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p := by
    nlinarith [sq_nonneg (physicalShellRadius (j + 1))]
  have hq' : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L q := by
    linarith
  have hr' : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L r := by
    linarith
  exact ⟨physicalShellDenomScale_le L hξ p j hp,
    physicalShellDenomScale_le L hξ q j hq',
    physicalShellDenomScale_le L hξ r j hr'⟩

/-- All three second-coordinate second-difference denominators have the same
physical-shell lower bound. -/
theorem physicalShellDenomScale_le_e2_triple (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p) :
    physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L q‖ ∧
      physicalShellDenomScale ξ j ≤ ‖1 - ξ * Shat L r‖ := by
  obtain ⟨hshiftq, hshiftr⟩ :=
    pstar2_shift_e2_ge_quarter L hL p q r hq hr hlarge
  have hp : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p := by
    nlinarith [sq_nonneg (physicalShellRadius (j + 1))]
  have hq' : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L q := by
    linarith
  have hr' : (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L r := by
    linarith
  exact ⟨physicalShellDenomScale_le L hξ p j hp,
    physicalShellDenomScale_le L hξ q j hq',
    physicalShellDenomScale_le L hξ r j hr'⟩

/-- A concrete physical shell satisfies both margin hypotheses. -/
example :
    16 * (symbolGridStep 100) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) ∧
      4 * (physicalShellRadius (4 + 1)) ^ 2 ≤
        pstar2 100 ((10, 0) : Z2 100) := by
  have hz : zdist 100 (10 : ZMod 100) = 10 := by decide
  simp only [symbolGridStep, physicalShellRadius, pstar2, pstar, dyad,
    hz, zdist_zero]
  constructor <;> norm_num <;> nlinarith [sq_nonneg Real.pi]

end RBM
