/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedFrequency

/-!
# Physical shells of the normalized dyadic cutoff

The normalization factor `2π` is retained in every radius. A nonzero cutoff
weight either belongs to the low-grid regime or is covered by one of two
adjacent physical annuli. This is support geometry only.
-/

namespace RBM

/-- The physical momentum radius corresponding to normalized dyadic scale. -/
noncomputable def physicalShellRadius (j : ℕ) : ℝ :=
  (2 * Real.pi) * dyad j

theorem physicalShellRadius_pos (j : ℕ) : 0 < physicalShellRadius j := by
  unfold physicalShellRadius
  exact mul_pos (by positivity) (dyad_pos j)

theorem physicalShellRadius_succ (j : ℕ) :
    physicalShellRadius (j + 1) = physicalShellRadius j / 2 := by
  unfold physicalShellRadius
  simp [dyad, pow_succ]
  ring

/-- Exact squared physical-radius support, with no change to shell indexing. -/
theorem normalizedDyadicCutoff_physical_support_sq (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
      pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2 := by
  obtain ⟨hinner, houter⟩ := normalizedDyadicCutoff_support_sq L j p hcut
  constructor
  · exact hinner
  · convert houter using 1
    unfold physicalShellRadius
    ring

/-- A normalized cutoff shell splits into low-grid momentum or one of two
adjacent physical annuli satisfying the exact separated-shell margins. -/
theorem normalizedDyadicCutoff_shell_cases (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    (pstar2 L p < 16 * (symbolGridStep L) ^ 2 ∧
      physicalShellRadius (j + 1) < 4 * symbolGridStep L) ∨
    (16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p ∧
      ((4 * (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2) ∨
        (4 * (physicalShellRadius (j + 2)) ^ 2 ≤ pstar2 L p ∧
          pstar2 L p ≤ (2 * physicalShellRadius (j + 1)) ^ 2))) := by
  obtain ⟨hinner, houter⟩ :=
    normalizedDyadicCutoff_physical_support_sq L j p hcut
  have hnext := physicalShellRadius_succ j
  have hnext2 : physicalShellRadius (j + 2) =
      physicalShellRadius (j + 1) / 2 := by
    simpa only [Nat.add_assoc] using physicalShellRadius_succ (j + 1)
  have hinner_j : 4 * (physicalShellRadius (j + 1)) ^ 2 =
      (physicalShellRadius j) ^ 2 := by
    rw [hnext]
    ring
  have hinner_j1 : 4 * (physicalShellRadius (j + 2)) ^ 2 =
      (physicalShellRadius (j + 1)) ^ 2 := by
    rw [hnext2]
    ring
  have houter_j1 : (2 * physicalShellRadius (j + 1)) ^ 2 =
      (physicalShellRadius j) ^ 2 := by
    rw [hnext]
    ring
  by_cases hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p
  · right
    refine ⟨hlarge, ?_⟩
    by_cases hmid : (physicalShellRadius j) ^ 2 ≤ pstar2 L p
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
    have hr := (physicalShellRadius_pos (j + 1)).le
    have hg : 0 ≤ 4 * symbolGridStep L := by
      unfold symbolGridStep
      positivity
    by_contra hnot
    have hge : 4 * symbolGridStep L ≤ physicalShellRadius (j + 1) :=
      le_of_not_gt hnot
    have hsq := (sq_le_sq₀ hg hr).2 hge
    nlinarith

/-- The support classification has a concrete nonzero lattice input. -/
example : normalizedDyadicCutoff 6 2 ((1, 0) : Z2 6) ≠ 0 := by
  have hz : zdist 6 (1 : ZMod 6) = 1 := by decide
  have hrad : pstar2 6 ((1, 0) : Z2 6) = (Real.pi / 3) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 6 ((1, 0) : Z2 6) = 1 / 6 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi / 3)]
    field_simp [Real.pi_ne_zero]
    ring
  rw [normalizedDyadicCutoff, hν]
  norm_num [dyadicCutoff, dyad, lowPass, smoothstep3]

end RBM
