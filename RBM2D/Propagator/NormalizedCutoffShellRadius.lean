/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffSecondDiffSharp
import RBM2D.Propagator.NormalizedCutoffShell

/-!
# A shell-supported middle-radius bound

When the inner cutoff radius is at least two normalized grid steps, any
three-point cutoff contribution has a positive middle radius. The smaller
shells remain a separate low-grid branch.
-/

namespace RBM

private theorem cutoff_second_diff_nonzero_has_support
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    normalizedDyadicCutoff L j p ≠ 0 ∨
      normalizedDyadicCutoff L j q ≠ 0 ∨
      normalizedDyadicCutoff L j r ≠ 0 := by
  by_cases hp : normalizedDyadicCutoff L j p = 0
  · by_cases hq : normalizedDyadicCutoff L j q = 0
    · by_cases hr : normalizedDyadicCutoff L j r = 0
      · simp [hp, hq, hr] at hsecond
      · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hq)
  · exact Or.inl hp

private theorem middle_radius_of_triple_support
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hstep₁ : |normalizedFrequency L q - normalizedFrequency L p| ≤
      1 / (L : ℝ))
    (hstep₂ : |normalizedFrequency L r - normalizedFrequency L q| ≤
      1 / (L : ℝ))
    (hsep : 2 / (L : ℝ) ≤ dyad (j + 1))
    (hsupport : normalizedDyadicCutoff L j p ≠ 0 ∨
      normalizedDyadicCutoff L j q ≠ 0 ∨
      normalizedDyadicCutoff L j r ≠ 0) :
    dyad (j + 1) / 2 ≤ normalizedFrequency L q := by
  have hgrid : 0 ≤ 1 / (L : ℝ) := by positivity
  have hdyad : 0 ≤ dyad (j + 1) := (dyad_pos _).le
  have hsep' : 2 * (1 / (L : ℝ)) ≤ dyad (j + 1) := by
    calc
      _ = 2 / (L : ℝ) := by ring
      _ ≤ _ := hsep
  have hinner (x : Z2 L) (hx : normalizedDyadicCutoff L j x ≠ 0) :
      dyad (j + 1) ≤ normalizedFrequency L x :=
    (dyadicCutoff_support j (normalizedFrequency L x) hx).1
  rcases hsupport with hp | hq | hr
  · have hpx := hinner p hp
    have hstep := (abs_le.mp hstep₁).1
    linarith
  · have hqx := hinner q hq
    linarith
  · have hrx := hinner r hr
    have hstep := (abs_le.mp hstep₂).2
    linarith

/-- A nonzero first-coordinate cutoff second difference either belongs to
the low-grid range or has an explicit positive middle radius. -/
theorem cutoff_second_diff_e1_low_or_middle_radius
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    dyad (j + 1) < 2 / (L : ℝ) ∨
      dyad (j + 1) / 2 ≤ normalizedFrequency L q := by
  by_cases hsep : 2 / (L : ℝ) ≤ dyad (j + 1)
  · right
    apply middle_radius_of_triple_support L j p q r
    · rw [hq]
      simpa only [normalizedGridStep_eq_inv] using
        abs_normalizedFrequency_shift_e1_le L hL p
    · rw [hr]
      simpa only [normalizedGridStep_eq_inv] using
        abs_normalizedFrequency_shift_e1_le L hL q
    · exact hsep
    · exact cutoff_second_diff_nonzero_has_support L j p q r hsecond
  · left
    exact lt_of_not_ge hsep

/-- The same low-grid or positive-middle-radius alternative for coordinate 2. -/
theorem cutoff_second_diff_e2_low_or_middle_radius
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    dyad (j + 1) < 2 / (L : ℝ) ∨
      dyad (j + 1) / 2 ≤ normalizedFrequency L q := by
  by_cases hsep : 2 / (L : ℝ) ≤ dyad (j + 1)
  · right
    apply middle_radius_of_triple_support L j p q r
    · rw [hq]
      simpa only [normalizedGridStep_eq_inv] using
        abs_normalizedFrequency_shift_e2_le L hL p
    · rw [hr]
      simpa only [normalizedGridStep_eq_inv] using
        abs_normalizedFrequency_shift_e2_le L hL q
    · exact hsep
    · exact cutoff_second_diff_nonzero_has_support L j p q r hsecond
  · left
    exact lt_of_not_ge hsep

/-- On a separated first-coordinate shell the middle radius can be taken as
half the inner cutoff radius. The fold term remains explicit. -/
theorem abs_cutoff_second_diff_e1_shell_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hsep : 2 / (L : ℝ) ≤ dyad (j + 1)) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.1| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  by_cases hsecond : normalizedDyadicCutoff L j r -
      2 * normalizedDyadicCutoff L j q +
      normalizedDyadicCutoff L j p = 0
  · rw [hsecond, abs_zero]
    have hd : 0 < dyad (j + 1) := dyad_pos _
    positivity
  · have hmid : dyad (j + 1) / 2 ≤ normalizedFrequency L q := by
      rcases cutoff_second_diff_e1_low_or_middle_radius
          L hL p q r j hq hr hsecond with hlow | hmid
      · linarith
      · exact hmid
    exact abs_normalizedDyadicCutoff_second_diff_e1_sharp_le
      L hL p q r j (dyad (j + 1) / 2) hq hr
      (by have := dyad_pos (j + 1); positivity) hmid

/-- The analogous second-coordinate shell bound. -/
theorem abs_cutoff_second_diff_e2_shell_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hsep : 2 / (L : ℝ) ≤ dyad (j + 1)) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.2| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  by_cases hsecond : normalizedDyadicCutoff L j r -
      2 * normalizedDyadicCutoff L j q +
      normalizedDyadicCutoff L j p = 0
  · rw [hsecond, abs_zero]
    have hd : 0 < dyad (j + 1) := dyad_pos _
    positivity
  · have hmid : dyad (j + 1) / 2 ≤ normalizedFrequency L q := by
      rcases cutoff_second_diff_e2_low_or_middle_radius
          L hL p q r j hq hr hsecond with hlow | hmid
      · linarith
      · exact hmid
    exact abs_normalizedDyadicCutoff_second_diff_e2_sharp_le
      L hL p q r j (dyad (j + 1) / 2) hq hr
      (by have := dyad_pos (j + 1); positivity) hmid

/-- On a separated shell without a first-coordinate fold, the cutoff
second difference is purely quadratic in the mesh size. -/
theorem abs_cutoff_second_diff_e1_shell_noFold_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hsep : 2 / (L : ℝ) ≤ dyad (j + 1))
    (hnoFold : noFoldTwo L p.1) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have h := abs_cutoff_second_diff_e1_shell_le L hL p q r j hq hr hsep
  rw [pstarFoldDefect_eq_zero_of_noFoldTwo L p.1 hnoFold] at h
  simpa using h

/-- The same fold-free conclusion in the second coordinate. -/
theorem abs_cutoff_second_diff_e2_shell_noFold_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hsep : 2 / (L : ℝ) ≤ dyad (j + 1))
    (hnoFold : noFoldTwo L p.2) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have h := abs_cutoff_second_diff_e2_shell_le L hL p q r j hq hr hsep
  rw [pstarFoldDefect_eq_zero_of_noFoldTwo L p.2 hnoFold] at h
  simpa using h

/-- The separated shell can contain a genuinely nonzero middle cutoff. -/
example : normalizedDyadicCutoff 16 1 ((5, 0) : Z2 16) ≠ 0 := by
  have hz : zdist 16 (5 : ZMod 16) = 5 := by decide
  have hrad : pstar2 16 ((5, 0) : Z2 16) =
      (5 * Real.pi / 8) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
      Nat.cast_zero, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 16 ((5, 0) : Z2 16) = 5 / 16 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < 5 * Real.pi / 8)]
    field_simp [Real.pi_ne_zero]
    ring
  rw [normalizedDyadicCutoff, hν]
  norm_num [dyadicCutoff, dyad, lowPass, smoothstep3]

/-- A fold-free separated shell path with nonzero middle cutoff. -/
example :
    |normalizedDyadicCutoff 16 1 ((6, 0) : Z2 16) -
        2 * normalizedDyadicCutoff 16 1 ((5, 0) : Z2 16) +
        normalizedDyadicCutoff 16 1 ((4, 0) : Z2 16)| ≤
      (420 * (2 : ℝ) ^ 1 / (dyad 2 / 2) +
        2100 * ((2 : ℝ) ^ 1) ^ 2) * (1 / (16 : ℝ)) ^ 2 := by
  apply abs_cutoff_second_diff_e1_shell_noFold_le
    16 (by norm_num) ((4, 0) : Z2 16) ((5, 0) : Z2 16)
    ((6, 0) : Z2 16) 1
  · rfl
  · rfl
  · norm_num [dyad]
  · left
    decide

end RBM

#print axioms RBM.cutoff_second_diff_e1_low_or_middle_radius
#print axioms RBM.cutoff_second_diff_e2_low_or_middle_radius
#print axioms RBM.abs_cutoff_second_diff_e1_shell_le
#print axioms RBM.abs_cutoff_second_diff_e2_shell_le
#print axioms RBM.abs_cutoff_second_diff_e1_shell_noFold_le
#print axioms RBM.abs_cutoff_second_diff_e2_shell_noFold_le
