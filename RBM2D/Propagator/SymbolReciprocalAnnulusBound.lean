/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolReciprocalDiff2Bound
import RBM2D.Propagator.SymbolShiftAnnulus

/-!
# Reciprocal-symbol second differences on a separated dyadic annulus

The margin hypotheses ensure that all three reciprocal denominators have a
common positive lower scale. Low-frequency shells and cutoff normalization
are deliberately left to the later dyadic argument.
-/

namespace RBM

/-- Lower scale for each resolvent denominator on the annulus. -/
noncomputable def symbolAnnulusDenomScale (ξ : ℂ) (j : ℕ) : ℝ :=
  4 / (45 * Real.pi ^ 2) * ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2)

theorem symbolAnnulusDenomScale_pos (ξ : ℂ) (j : ℕ) :
    0 < symbolAnnulusDenomScale ξ j := by
  unfold symbolAnnulusDenomScale
  have hr := dyad_pos (j + 1)
  positivity

private theorem reciprocalSymbolStepBound_nonneg (L : ℕ) [NeZero L]
    (q : ZMod L) : 0 ≤ reciprocalSymbolStepBound L q := by
  unfold reciprocalSymbolStepBound
  have hq := pstar_nonneg L q
  positivity

private theorem reciprocalSymbolSecondBound_nonneg (L : ℕ) [NeZero L] :
    0 ≤ reciprocalSymbolSecondBound L := by
  unfold reciprocalSymbolSecondBound
  positivity

private theorem two_fraction_le_of_common_denom
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

/-- Second reciprocal difference in coordinate one at a separated dyadic scale. -/
theorem norm_invSymbolMultiplier_second_diff_e1_annulus_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
            (reciprocalSymbolStepBound L p.1 +
              reciprocalSymbolStepBound L q.1) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := by
  have hpre := norm_invSymbolMultiplier_second_diff_e1_le L hL hξ p q r hq hr
  have ⟨hDq, hDr⟩ :=
    norm_one_sub_mul_Shat_ge_e1_shifts L hL hξ p q r j hq hr hlarge hinner
  have hDp : symbolAnnulusDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ := by
    apply norm_one_sub_mul_Shat_ge_dyadic L hξ p j
    nlinarith [sq_nonneg (dyad (j + 1))]
  have hA : 0 ≤ ‖ξ‖ * reciprocalSymbolSecondBound L :=
    mul_nonneg (norm_nonneg _) (reciprocalSymbolSecondBound_nonneg L)
  have hB : 0 ≤ ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.1 *
      (reciprocalSymbolStepBound L p.1 + reciprocalSymbolStepBound L q.1) := by
    have hp := reciprocalSymbolStepBound_nonneg L p.1
    have hq := reciprocalSymbolStepBound_nonneg L q.1
    positivity
  exact hpre.trans (two_fraction_le_of_common_denom hA hB
    (symbolAnnulusDenomScale_pos ξ j) hDr hDq hDp)

/-- Second reciprocal difference in coordinate two at a separated dyadic scale. -/
theorem norm_invSymbolMultiplier_second_diff_e2_annulus_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * reciprocalSymbolSecondBound L /
          (symbolAnnulusDenomScale ξ j) ^ 2 +
        ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.2 *
            (reciprocalSymbolStepBound L p.2 +
              reciprocalSymbolStepBound L q.2) /
          (symbolAnnulusDenomScale ξ j) ^ 3 := by
  have hpre := norm_invSymbolMultiplier_second_diff_e2_le L hL hξ p q r hq hr
  have ⟨hDq, hDr⟩ :=
    norm_one_sub_mul_Shat_ge_e2_shifts L hL hξ p q r j hq hr hlarge hinner
  have hDp : symbolAnnulusDenomScale ξ j ≤ ‖1 - ξ * Shat L p‖ := by
    apply norm_one_sub_mul_Shat_ge_dyadic L hξ p j
    nlinarith [sq_nonneg (dyad (j + 1))]
  have hA : 0 ≤ ‖ξ‖ * reciprocalSymbolSecondBound L :=
    mul_nonneg (norm_nonneg _) (reciprocalSymbolSecondBound_nonneg L)
  have hB : 0 ≤ ‖ξ‖ ^ 2 * reciprocalSymbolStepBound L p.2 *
      (reciprocalSymbolStepBound L p.2 + reciprocalSymbolStepBound L q.2) := by
    have hp := reciprocalSymbolStepBound_nonneg L p.2
    have hq := reciprocalSymbolStepBound_nonneg L q.2
    positivity
  exact hpre.trans (two_fraction_le_of_common_denom hA hB
    (symbolAnnulusDenomScale_pos ξ j) hDr hDq hDp)

end RBM
