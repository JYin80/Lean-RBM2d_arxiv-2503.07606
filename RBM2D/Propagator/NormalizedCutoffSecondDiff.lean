/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PhysicalShellNumerator
import RBM2D.Propagator.SymbolLowShellE2

/-!
# Second reciprocal differences on a normalized cutoff shell

A nonzero cutoff weight gives one low-grid estimate or one of two adjacent
physical-shell estimates. Every physical radius retains the factor `2π`.
-/

namespace RBM

/-- The exact mass-dependent bound in the low-grid branch. -/
noncomputable def normalizedCutoffLowSecondBound (L : ℕ) [NeZero L]
    (ξ : ℂ) : ℝ :=
  ‖ξ‖ * ((2 / 5 : ℝ) * (symbolGridStep L) ^ 2) /
      (symbolLowDenomScale ξ) ^ 2 +
    ‖ξ‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep L) ^ 4) /
      (symbolLowDenomScale ξ) ^ 3

/-- The exact second-difference bound at physical shell index `k`. -/
noncomputable def normalizedCutoffPhysicalSecondBound (L : ℕ) [NeZero L]
    (ξ : ℂ) (k : ℕ) : ℝ :=
  ‖ξ‖ * reciprocalSymbolSecondBound L /
      (physicalShellDenomScale ξ k) ^ 2 +
    ‖ξ‖ ^ 2 * ((11 / 5 : ℝ) *
        (symbolGridStep L * physicalShellRadius k) ^ 2) /
      (physicalShellDenomScale ξ k) ^ 3

/-- First-coordinate cutoff support gives a low-grid bound or a separated
physical-shell bound at index `j` or `j+1`. -/
theorem normalizedDyadicCutoff_second_diff_e1_cases
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    (pstar2 L p < 16 * (symbolGridStep L) ^ 2 ∧
      physicalShellRadius (j + 1) < 4 * symbolGridStep L ∧
      ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤ normalizedCutoffLowSecondBound L ξ) ∨
    (16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p ∧
      ((4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2 ∧
          ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
            invSymbolMultiplier L ξ p‖ ≤
              normalizedCutoffPhysicalSecondBound L ξ j) ∨
        (4 * (physicalShellRadius (j + 2)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius (j + 1)) ^ 2 ∧
          ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
            invSymbolMultiplier L ξ p‖ ≤
              normalizedCutoffPhysicalSecondBound L ξ (j + 1)))) := by
  rcases normalizedDyadicCutoff_shell_cases L j p hcut with
    ⟨hlow, hgrid⟩ | ⟨hlarge, hphysical⟩
  · left
    refine ⟨hlow, hgrid, ?_⟩
    exact norm_invSymbolMultiplier_second_diff_e1_low_le L hL hξ p q r hq hr
      hlow.le
  · right
    refine ⟨hlarge, ?_⟩
    rcases hphysical with ⟨hinner, houter⟩ | ⟨hinner, houter⟩
    · left
      refine ⟨hinner, houter, ?_⟩
      exact norm_invSymbolMultiplier_second_diff_e1_physical_le L hL hξ
        p q r j hq hr hlarge hinner houter
    · right
      refine ⟨hinner, houter, ?_⟩
      exact norm_invSymbolMultiplier_second_diff_e1_physical_le L hL hξ
        p q r (j + 1) hq hr hlarge hinner houter

/-- Second-coordinate cutoff support has the same three branches and constants. -/
theorem normalizedDyadicCutoff_second_diff_e2_cases
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    (pstar2 L p < 16 * (symbolGridStep L) ^ 2 ∧
      physicalShellRadius (j + 1) < 4 * symbolGridStep L ∧
      ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤ normalizedCutoffLowSecondBound L ξ) ∨
    (16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p ∧
      ((4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2 ∧
          ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
            invSymbolMultiplier L ξ p‖ ≤
              normalizedCutoffPhysicalSecondBound L ξ j) ∨
        (4 * (physicalShellRadius (j + 2)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius (j + 1)) ^ 2 ∧
          ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
            invSymbolMultiplier L ξ p‖ ≤
              normalizedCutoffPhysicalSecondBound L ξ (j + 1)))) := by
  rcases normalizedDyadicCutoff_shell_cases L j p hcut with
    ⟨hlow, hgrid⟩ | ⟨hlarge, hphysical⟩
  · left
    refine ⟨hlow, hgrid, ?_⟩
    exact norm_invSymbolMultiplier_second_diff_e2_low_le L hL hξ p q r hq hr
      hlow.le
  · right
    refine ⟨hlarge, ?_⟩
    rcases hphysical with ⟨hinner, houter⟩ | ⟨hinner, houter⟩
    · left
      refine ⟨hinner, houter, ?_⟩
      exact norm_invSymbolMultiplier_second_diff_e2_physical_le L hL hξ
        p q r j hq hr hlarge hinner houter
    · right
      refine ⟨hinner, houter, ?_⟩
      exact norm_invSymbolMultiplier_second_diff_e2_physical_le L hL hξ
        p q r (j + 1) hq hr hlarge hinner houter

end RBM

#print axioms RBM.normalizedDyadicCutoff_second_diff_e1_cases
#print axioms RBM.normalizedDyadicCutoff_second_diff_e2_cases
