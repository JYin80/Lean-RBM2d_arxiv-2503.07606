/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffFoldSupport

/-!
# Coarse separated-shell cutoff sums

The raw fold-defect sum and the full torus cardinality give an explicit
per-shell estimate. Its growth in the shell index is too large for the sharp
T22 Fourier estimate, so this is only a verified coarse baseline.
-/

namespace RBM

/-- The two-dimensional discrete torus has exactly `L²` frequency points. -/
theorem card_Z2_eq_sq (L : ℕ) [NeZero L] :
    Fintype.card (Z2 L) = L ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, pow_two]

private theorem separated_shell_remainder_le
    (L : ℕ) [NeZero L] (j : ℕ) (D : Z2 L → ℝ)
    (hD : (∑ p : Z2 L, |D p|) ≤ 24 * Real.pi) :
    (∑ p : Z2 L,
      (420 * (2 : ℝ) ^ j * (|D p| / (2 * Real.pi)) +
        (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
          2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2)) ≤
      5040 * (2 : ℝ) ^ j +
        (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
          2100 * ((2 : ℝ) ^ j) ^ 2) := by
  let A : ℝ := 420 * (2 : ℝ) ^ j / (2 * Real.pi)
  let Q : ℝ := 420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
    2100 * ((2 : ℝ) ^ j) ^ 2
  have hterm (p : Z2 L) :
      420 * (2 : ℝ) ^ j * (|D p| / (2 * Real.pi)) = A * |D p| := by
    dsimp [A]
    ring
  have hsum : (∑ p : Z2 L,
      (420 * (2 : ℝ) ^ j * (|D p| / (2 * Real.pi)) +
        Q * (1 / (L : ℝ)) ^ 2)) =
      A * (∑ p : Z2 L, |D p|) + Q := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const]
    have hcard : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
      exact_mod_cast card_Z2_eq_sq L
    simp only [Finset.card_univ, nsmul_eq_mul, hcard]
    have hL : (L : ℝ) ≠ 0 := ne_of_gt (cast_L_pos L)
    field_simp [hL]
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfold : A * (∑ p : Z2 L, |D p|) ≤
      5040 * (2 : ℝ) ^ j := by
    calc
      _ ≤ A * (24 * Real.pi) :=
        mul_le_mul_of_nonneg_left hD hA
      _ = 5040 * (2 : ℝ) ^ j := by
        dsimp [A]
        field_simp [Real.pi_ne_zero]
        ring
  change (∑ p : Z2 L,
      (420 * (2 : ℝ) ^ j * (|D p| / (2 * Real.pi)) +
        Q * (1 / (L : ℝ)) ^ 2)) ≤ 5040 * (2 : ℝ) ^ j + Q
  rw [hsum]
  linarith

/-- The first-coordinate separated-shell remainder has an explicit
`O(2^j+4^j)` bound independent of `L`. -/
theorem cutoffSecondDiffE1ShellRemainder_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) :
    cutoffSecondDiffE1ShellRemainder L j ≤
      5040 * (2 : ℝ) ^ j +
        (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
          2100 * ((2 : ℝ) ^ j) ^ 2) := by
  unfold cutoffSecondDiffE1ShellRemainder
  exact separated_shell_remainder_le L j
    (fun p => pstarFoldDefect L p.1)
    (sum_abs_pstarFoldDefect_e1_le L hL)

/-- The corresponding second-coordinate coarse shell bound. -/
theorem cutoffSecondDiffE2ShellRemainder_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) :
    cutoffSecondDiffE2ShellRemainder L j ≤
      5040 * (2 : ℝ) ^ j +
        (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
          2100 * ((2 : ℝ) ^ j) ^ 2) := by
  unfold cutoffSecondDiffE2ShellRemainder
  exact separated_shell_remainder_le L j
    (fun p => pstarFoldDefect L p.2)
    (sum_abs_pstarFoldDefect_e2_le L hL)

/-- Exact simplification of the affine coefficient in a separated shell. -/
theorem separated_shell_affine_coefficient_eq (j : ℕ) :
    420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
      2100 * ((2 : ℝ) ^ j) ^ 2 =
    3780 * ((2 : ℝ) ^ j) ^ 2 := by
  have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hden : dyad (j + 1) / 2 = 1 / (4 * (2 : ℝ) ^ j) := by
    simp only [dyad, pow_succ, inv_pow]
    field_simp [hp]
    ring
  rw [hden]
  field_simp [hp]
  ring

/-- Explicit numerical per-shell bound in the first coordinate. -/
theorem cutoffSecondDiffE1ShellRemainder_le_explicit
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) :
    cutoffSecondDiffE1ShellRemainder L j ≤
      5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2 := by
  simpa only [separated_shell_affine_coefficient_eq] using
    cutoffSecondDiffE1ShellRemainder_le L hL j

/-- Explicit numerical per-shell bound in the second coordinate. -/
theorem cutoffSecondDiffE2ShellRemainder_le_explicit
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) :
    cutoffSecondDiffE2ShellRemainder L j ≤
      5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2 := by
  simpa only [separated_shell_affine_coefficient_eq] using
    cutoffSecondDiffE2ShellRemainder_le L hL j

/-- A fully numerical finite-shell estimate in the first coordinate. The
increasing powers of two expose the weakness of the raw fold bound. -/
theorem sum_cutoffSecondDiffMass_e1_finite_shells_le_explicit
    (L N : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range N,
      cutoffSecondDiffMass L j ((1, 0) : Z2 L)) ≤
      4608 + ∑ j ∈ separatedShellIndices L N,
        (5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2) := by
  have hsplit := sum_cutoffSecondDiffMass_e1_finite_shells_le L N hL
  have hsum : (∑ j ∈ separatedShellIndices L N,
      cutoffSecondDiffE1ShellRemainder L j) ≤
      ∑ j ∈ separatedShellIndices L N,
        (5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    exact cutoffSecondDiffE1ShellRemainder_le_explicit L hL j
  linarith

/-- The corresponding numerical finite-shell estimate in coordinate 2. -/
theorem sum_cutoffSecondDiffMass_e2_finite_shells_le_explicit
    (L N : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range N,
      cutoffSecondDiffMass L j ((0, 1) : Z2 L)) ≤
      4608 + ∑ j ∈ separatedShellIndices L N,
        (5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2) := by
  have hsplit := sum_cutoffSecondDiffMass_e2_finite_shells_le L N hL
  have hsum : (∑ j ∈ separatedShellIndices L N,
      cutoffSecondDiffE2ShellRemainder L j) ≤
      ∑ j ∈ separatedShellIndices L N,
        (5040 * (2 : ℝ) ^ j + 3780 * ((2 : ℝ) ^ j) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    exact cutoffSecondDiffE2ShellRemainder_le_explicit L hL j
  linarith

example : cutoffSecondDiffE1ShellRemainder 8 1 ≤
    5040 * (2 : ℝ) ^ 1 + 3780 * ((2 : ℝ) ^ 1) ^ 2 :=
  cutoffSecondDiffE1ShellRemainder_le_explicit 8 (by norm_num) 1

end RBM

#print axioms RBM.card_Z2_eq_sq
#print axioms RBM.cutoffSecondDiffE1ShellRemainder_le
#print axioms RBM.cutoffSecondDiffE2ShellRemainder_le
#print axioms RBM.separated_shell_affine_coefficient_eq
#print axioms RBM.cutoffSecondDiffE1ShellRemainder_le_explicit
#print axioms RBM.cutoffSecondDiffE2ShellRemainder_le_explicit
#print axioms RBM.sum_cutoffSecondDiffMass_e1_finite_shells_le_explicit
#print axioms RBM.sum_cutoffSecondDiffMass_e2_finite_shells_le_explicit
