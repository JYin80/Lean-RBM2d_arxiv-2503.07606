/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolAnnulusNumerator
import RBM2D.Propagator.SymbolLowShellE2

/-!
# Direct support information for the existing dyadic cutoff

The existing cutoff takes an arbitrary real radius. Here it is evaluated at
the unnormalized momentum radius `sqrt (pstar2 L p)`. A cutoff composed with
the normalized frequency has not yet been defined in the project. The two
possible separated-shell indices below reflect the width of its support.
-/

namespace RBM

/-- Nonzero cutoff weight puts squared momentum between its exact squared
inner and outer radii. -/
theorem dyadicCutoff_sqrt_pstar2_support (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (hcut : dyadicCutoff j (Real.sqrt (pstar2 L p)) ≠ 0) :
    (dyad (j + 1)) ^ 2 ≤ pstar2 L p ∧
      pstar2 L p ≤ (2 * dyad j) ^ 2 := by
  have ⟨hinner, houter⟩ :=
    dyadicCutoff_support j (Real.sqrt (pstar2 L p)) hcut
  have hP := pstar2_nonneg L p
  constructor
  · have h := (sq_le_sq₀ (dyad_nonneg (j + 1))
        (Real.sqrt_nonneg _)).2 hinner
    simpa only [Real.sq_sqrt hP] using h
  · have h := (sq_le_sq₀ (Real.sqrt_nonneg _)
        (by have := dyad_nonneg j; positivity : 0 ≤ 2 * dyad j)).2 houter
    simpa only [Real.sq_sqrt hP] using h

/-- Each nonzero unnormalized cutoff weight lies either at low momentum,
where its inner radius is below four grid steps, or in one of the two
separated annuli required by the existing reciprocal-symbol shell bounds. -/
theorem dyadicCutoff_sqrt_pstar2_shell_cases (L : ℕ) [NeZero L]
    (p : Z2 L) (j : ℕ)
    (hcut : dyadicCutoff j (Real.sqrt (pstar2 L p)) ≠ 0) :
    (pstar2 L p < 16 * (symbolGridStep L) ^ 2 ∧
      dyad (j + 1) < 4 * symbolGridStep L) ∨
    (16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p ∧
      ((4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * dyad j) ^ 2) ∨
        (4 * (dyad (j + 2)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * dyad (j + 1)) ^ 2))) := by
  obtain ⟨hinner, houter⟩ := dyadicCutoff_sqrt_pstar2_support L p j hcut
  have hnext : dyad (j + 1) = dyad j / 2 := by
    simp [dyad, pow_succ]
    ring
  have hnext2 : dyad (j + 2) = dyad (j + 1) / 2 := by
    simp [dyad, pow_succ]
    ring
  have hinner_j : 4 * (dyad (j + 1)) ^ 2 = (dyad j) ^ 2 := by
    rw [hnext]
    ring
  have hinner_j1 : 4 * (dyad (j + 2)) ^ 2 = (dyad (j + 1)) ^ 2 := by
    rw [hnext2]
    ring
  have houter_j1 : (2 * dyad (j + 1)) ^ 2 = (dyad j) ^ 2 := by
    rw [hnext]
    ring
  by_cases hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p
  · right
    refine ⟨hlarge, ?_⟩
    by_cases hmid : (dyad j) ^ 2 ≤ pstar2 L p
    · left
      refine ⟨?_, houter⟩
      simpa only [hinner_j] using hmid
    · right
      refine ⟨?_, ?_⟩
      · simpa only [hinner_j1] using hinner
      · rw [houter_j1]
        exact le_of_not_ge hmid
  · left
    have hlow : pstar2 L p < 16 * (symbolGridStep L) ^ 2 := lt_of_not_ge hlarge
    refine ⟨hlow, ?_⟩
    have hr := dyad_nonneg (j + 1)
    have hg : 0 ≤ 4 * symbolGridStep L := by
      unfold symbolGridStep
      positivity
    by_contra hnot
    have hge : 4 * symbolGridStep L ≤ dyad (j + 1) := le_of_not_gt hnot
    have hsq := (sq_le_sq₀ hg hr).2 hge
    nlinarith

/-- The unnormalized cutoff genuinely meets a nonzero lattice momentum. -/
example : dyadicCutoff 0 (Real.sqrt (pstar2 6 ((1, 0) : Z2 6))) ≠ 0 := by
  have hz : zdist 6 (1 : ZMod 6) = 1 := by decide
  have hrad : pstar2 6 ((1, 0) : Z2 6) = (Real.pi / 3) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, zero_div]
    ring
  rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < Real.pi / 3)]
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have h1 : 1 < Real.pi / 3 := by linarith
  have h2 : Real.pi / 3 < 2 := by linarith
  have h2t : 2 ≤ 2 * (Real.pi / 3) := by linarith
  have hcut : dyadicCutoff 0 (Real.pi / 3) = lowPass (Real.pi / 3) := by
    rw [dyadicCutoff]
    norm_num [dyad]
    exact lowPass_eq_zero_of_two_le h2t
  rw [hcut]
  have hx0 : 0 ≤ Real.pi / 3 - 1 := by linarith
  have hx1 : Real.pi / 3 - 1 < 1 := by linarith
  have hpoly (x : ℝ) : 1 - smoothstep3 x =
      (1 - x) ^ 4 * (1 + 4 * x + 10 * x ^ 2 + 20 * x ^ 3) := by
    unfold smoothstep3
    ring
  rw [lowPass, ite_eq_right (not_le.mpr h1), ite_eq_left h2.le, hpoly]
  have hh : 0 < 1 - (Real.pi / 3 - 1) := by linarith
  positivity

end RBM
