/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedRadiusNoFold

/-!
# The explicit fold defect in normalized-radius second differences

The square of the Euclidean radius has an exact three-point expansion. Its
departure from the affine-coordinate formula is one discrete second
difference of `pstar`. This file keeps that defect visible; it vanishes under
`noFoldTwo` and is first order in the grid step at a fold.
-/

namespace RBM

/-- The discrete angular-distance defect at two consecutive steps. -/
noncomputable def pstarFoldDefect (L : ℕ) [NeZero L] (u : ZMod L) : ℝ :=
  pstar L (u + 1 + 1) - 2 * pstar L (u + 1) + pstar L u

/-- The fold defect is supported outside the affine representative region. -/
theorem pstarFoldDefect_eq_zero_of_noFoldTwo (L : ℕ) [NeZero L]
    (u : ZMod L) (h : noFoldTwo L u) :
    pstarFoldDefect L u = 0 := by
  exact pstar_second_diff_eq_zero_of_noFoldTwo L u h

/-- A nonzero defect certifies that the two-step path crosses a fold. -/
theorem not_noFoldTwo_of_pstarFoldDefect_ne_zero (L : ℕ) [NeZero L]
    (u : ZMod L) (h : pstarFoldDefect L u ≠ 0) :
    ¬ noFoldTwo L u := by
  intro hnoFold
  exact h (pstarFoldDefect_eq_zero_of_noFoldTwo L u hnoFold)

private theorem abs_pstar_one_step_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
    |pstar L (u + 1) - pstar L u| ≤ symbolGridStep L := by
  have hforward : pstar L (u + 1) ≤
      pstar L u + symbolGridStep L := by
    have hz : zdist L (u + 1) ≤ zdist L u + 1 := by
      have h := zdist_add_le L u (1 : ZMod L)
      have h1 := zdist_one_le L hL
      omega
    have hz' : (zdist L (u + 1) : ℝ) ≤
        (zdist L u : ℝ) + 1 := by exact_mod_cast hz
    have hg : 0 ≤ symbolGridStep L := by unfold symbolGridStep; positivity
    calc
      pstar L (u + 1) = symbolGridStep L * (zdist L (u + 1) : ℝ) := by
        unfold pstar symbolGridStep
        ring
      _ ≤ symbolGridStep L * ((zdist L u : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hz' hg
      _ = pstar L u + symbolGridStep L := by
        unfold pstar symbolGridStep
        ring
  apply abs_le.mpr
  constructor
  · have := pstar_le_shift_one L hL u
    linarith
  · linarith

/-- The fold defect is at most two physical grid steps. -/
theorem abs_pstarFoldDefect_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
    |pstarFoldDefect L u| ≤ 2 * symbolGridStep L := by
  have h₁ := abs_pstar_one_step_le L hL u
  have h₂ := abs_pstar_one_step_le L hL (u + 1)
  have hrepr : pstarFoldDefect L u =
      (pstar L (u + 1 + 1) - pstar L (u + 1)) -
        (pstar L (u + 1) - pstar L u) := by
    unfold pstarFoldDefect
    ring
  rw [hrepr]
  calc
    |(pstar L (u + 1 + 1) - pstar L (u + 1)) -
        (pstar L (u + 1) - pstar L u)| ≤
      |pstar L (u + 1 + 1) - pstar L (u + 1)| +
        |pstar L (u + 1) - pstar L u| := abs_sub _ _
    _ ≤ 2 * symbolGridStep L := by linarith

/-- Exact squared-radius decomposition in the first coordinate. -/
theorem pstar2_second_diff_e1_fold_identity (L : ℕ) [NeZero L]
    (p q r : Z2 L) (hq : q = p + (1, 0))
    (hr : r = q + (1, 0)) :
    pstar2 L r - 2 * pstar2 L q + pstar2 L p =
      2 * (pstar L q.1 - pstar L p.1) ^ 2 +
        pstarFoldDefect L p.1 *
          (pstar L r.1 + 2 * pstar L q.1 - pstar L p.1) := by
  have hq₂ : q.2 = p.2 := by simp [hq]
  have hr₂ : r.2 = p.2 := by simp [hr, hq]
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hr₁ : r.1 = p.1 + 1 + 1 := by rw [hr, hq]; rfl
  simp only [pstar2, pstarFoldDefect, hq₂, hr₂, hq₁, hr₁]
  ring

/-- Exact squared-radius decomposition in the second coordinate. -/
theorem pstar2_second_diff_e2_fold_identity (L : ℕ) [NeZero L]
    (p q r : Z2 L) (hq : q = p + (0, 1))
    (hr : r = q + (0, 1)) :
    pstar2 L r - 2 * pstar2 L q + pstar2 L p =
      2 * (pstar L q.2 - pstar L p.2) ^ 2 +
        pstarFoldDefect L p.2 *
          (pstar L r.2 + 2 * pstar L q.2 - pstar L p.2) := by
  have hq₁ : q.1 = p.1 := by simp [hq]
  have hr₁ : r.1 = p.1 := by simp [hr, hq]
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hr₂ : r.2 = p.2 + 1 + 1 := by rw [hr, hq]; rfl
  simp only [pstar2, pstarFoldDefect, hq₁, hr₁, hq₂, hr₂]
  ring

private theorem normalized_second_square_of_physical_identity
    (L : ℕ) [NeZero L] (p q r : Z2 L) (A : ℝ)
    (h : pstar2 L r - 2 * pstar2 L q + pstar2 L p = A) :
    (normalizedFrequency L r) ^ 2 -
        2 * (normalizedFrequency L q) ^ 2 +
        (normalizedFrequency L p) ^ 2 =
      A / (2 * Real.pi) ^ 2 := by
  rw [normalizedFrequency_sq, normalizedFrequency_sq,
    normalizedFrequency_sq]
  calc
    pstar2 L r / (2 * Real.pi) ^ 2 -
        2 * (pstar2 L q / (2 * Real.pi) ^ 2) +
        pstar2 L p / (2 * Real.pi) ^ 2 =
      (pstar2 L r - 2 * pstar2 L q + pstar2 L p) /
        (2 * Real.pi) ^ 2 := by ring
    _ = A / (2 * Real.pi) ^ 2 := by rw [h]

/-- The normalized-radius second difference has one explicit fold term.
The identity avoids dividing by the middle radius and remains valid at zero. -/
theorem normalizedFrequency_second_diff_e1_fold_identity
    (L : ℕ) [NeZero L] (p q r : Z2 L)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0)) :
    2 * normalizedFrequency L q *
        (normalizedFrequency L r - 2 * normalizedFrequency L q +
          normalizedFrequency L p) =
      2 * ((pstar L q.1 - pstar L p.1) / (2 * Real.pi)) ^ 2 +
        pstarFoldDefect L p.1 *
          (pstar L r.1 + 2 * pstar L q.1 - pstar L p.1) /
          (2 * Real.pi) ^ 2 -
        (normalizedFrequency L r - normalizedFrequency L q) ^ 2 -
        (normalizedFrequency L p - normalizedFrequency L q) ^ 2 := by
  have hsq := normalized_second_square_of_physical_identity L p q r _
    (pstar2_second_diff_e1_fold_identity L p q r hq hr)
  have hden : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  rw [div_pow]
  field_simp [hden] at hsq ⊢
  nlinarith [hsq]

/-- The corresponding exact identity in the second coordinate. -/
theorem normalizedFrequency_second_diff_e2_fold_identity
    (L : ℕ) [NeZero L] (p q r : Z2 L)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1)) :
    2 * normalizedFrequency L q *
        (normalizedFrequency L r - 2 * normalizedFrequency L q +
          normalizedFrequency L p) =
      2 * ((pstar L q.2 - pstar L p.2) / (2 * Real.pi)) ^ 2 +
        pstarFoldDefect L p.2 *
          (pstar L r.2 + 2 * pstar L q.2 - pstar L p.2) /
          (2 * Real.pi) ^ 2 -
        (normalizedFrequency L r - normalizedFrequency L q) ^ 2 -
        (normalizedFrequency L p - normalizedFrequency L q) ^ 2 := by
  have hsq := normalized_second_square_of_physical_identity L p q r _
    (pstar2_second_diff_e2_fold_identity L p q r hq hr)
  have hden : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  rw [div_pow]
  field_simp [hden] at hsq ⊢
  nlinarith [hsq]

/-- A nonempty antipodal crossing: the fold defect is `-2` grid steps. -/
theorem pstarFoldDefect_antipodal_example :
    pstarFoldDefect 8 (3 : ZMod 8) =
      -2 * symbolGridStep 8 := by
  have hz₃ : zdist 8 (3 : ZMod 8) = 3 := by decide
  have hz₄ : zdist 8 (4 : ZMod 8) = 4 := by decide
  have hz₅ : zdist 8 (5 : ZMod 8) = 3 := by decide
  norm_num [pstarFoldDefect, pstar, symbolGridStep,
    hz₃, hz₄, hz₅]
  ring

end RBM

#print axioms RBM.pstarFoldDefect_eq_zero_of_noFoldTwo
#print axioms RBM.not_noFoldTwo_of_pstarFoldDefect_ne_zero
#print axioms RBM.abs_pstarFoldDefect_le
#print axioms RBM.pstar2_second_diff_e1_fold_identity
#print axioms RBM.pstar2_second_diff_e2_fold_identity
#print axioms RBM.normalizedFrequency_second_diff_e1_fold_identity
#print axioms RBM.normalizedFrequency_second_diff_e2_fold_identity
#print axioms RBM.pstarFoldDefect_antipodal_example
