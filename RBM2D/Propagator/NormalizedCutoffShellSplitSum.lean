/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffLowGridScales

/-!
# Finite shell split for normalized cutoff second differences

The low-grid scales contribute at most `4608` in total. On the remaining
finite shells, the explicit fold defect and quadratic affine term are kept
without any claim that their sum is uniformly bounded.
-/

namespace RBM

/-- Separated dyadic shell indices among `0, ..., N-1`. -/
noncomputable def separatedShellIndices (L N : ℕ) [NeZero L] : Finset ℕ :=
  (Finset.range N).filter (fun j => 2 / (L : ℝ) ≤ dyad (j + 1))

private theorem finite_shell_split_sum
    (L N : ℕ) [NeZero L] (F G : ℕ → ℝ)
    (hF_nonneg : ∀ j, 0 ≤ F j)
    (hF_low_zero : ∀ j, dyad (j + 1) < 2 / (L : ℝ) →
      j ∉ lowGridActiveScales L → F j = 0)
    (hF_active : (∑ j ∈ lowGridActiveScales L, F j) ≤ 4608)
    (hF_sep : ∀ j, 2 / (L : ℝ) ≤ dyad (j + 1) → F j ≤ G j) :
    (∑ j ∈ Finset.range N, F j) ≤
      4608 + ∑ j ∈ separatedShellIndices L N, G j := by
  classical
  let Slo : Finset ℕ := (Finset.range N).filter
    (fun j => dyad (j + 1) < 2 / (L : ℝ))
  let Skeep : Finset ℕ := Slo.filter (fun j => j ∈ lowGridActiveScales L)
  have hkeep_subset : Skeep ⊆ Slo := Finset.filter_subset _ _
  have hkeep_active : Skeep ⊆ lowGridActiveScales L := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hlow_eq : (∑ j ∈ Slo, F j) = ∑ j ∈ Skeep, F j := by
    symm
    apply Finset.sum_subset hkeep_subset
    intro j hjlo hjnot
    have hlow : dyad (j + 1) < 2 / (L : ℝ) :=
      (Finset.mem_filter.mp hjlo).2
    have hnot : j ∉ lowGridActiveScales L := by
      intro hjA
      exact hjnot (Finset.mem_filter.mpr ⟨hjlo, hjA⟩)
    exact hF_low_zero j hlow hnot
  have hlow_le : (∑ j ∈ Slo, F j) ≤ 4608 := by
    rw [hlow_eq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hkeep_active
      (by intro j _ _; exact hF_nonneg j)).trans hF_active
  have hsep_le : (∑ j ∈ separatedShellIndices L N, F j) ≤
      ∑ j ∈ separatedShellIndices L N, G j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hF_sep j (Finset.mem_filter.mp hj).2
  have hsplit : (∑ j ∈ Finset.range N, F j) =
      (∑ j ∈ Slo, F j) +
        (∑ j ∈ separatedShellIndices L N, F j) := by
    simpa only [Slo, separatedShellIndices, not_lt] using
      (Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun j => dyad (j + 1) < 2 / (L : ℝ)) F).symm
  rw [hsplit]
  linarith

/-- Absolute cutoff second-difference mass on one shell along a lattice
displacement. -/
noncomputable def cutoffSecondDiffMass
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L) : ℝ :=
  ∑ p : Z2 L,
    |normalizedDyadicCutoff L j (p + e + e) -
      2 * normalizedDyadicCutoff L j (p + e) +
      normalizedDyadicCutoff L j p|

/-- The separated-shell first-coordinate remainder retains the exact fold
defect at every starting point. -/
noncomputable def cutoffSecondDiffE1ShellRemainder
    (L : ℕ) [NeZero L] (j : ℕ) : ℝ :=
  ∑ p : Z2 L,
    (420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.1| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2)

/-- Finite-shell first-coordinate split: low-grid contribution plus the
unreduced separated-shell fold and affine remainder. -/
theorem sum_cutoffSecondDiffMass_e1_finite_shells_le
    (L N : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range N,
      cutoffSecondDiffMass L j ((1, 0) : Z2 L)) ≤
      4608 + ∑ j ∈ separatedShellIndices L N,
        cutoffSecondDiffE1ShellRemainder L j := by
  apply finite_shell_split_sum L N
    (fun j => cutoffSecondDiffMass L j ((1, 0) : Z2 L))
    (fun j => cutoffSecondDiffE1ShellRemainder L j)
  · intro j
    unfold cutoffSecondDiffMass
    exact Finset.sum_nonneg (by intro p _; exact abs_nonneg _)
  · intro j hlow hnot
    unfold cutoffSecondDiffMass
    apply Finset.sum_eq_zero
    intro p _
    have hzero : normalizedDyadicCutoff L j (p + (1, 0) + (1, 0)) -
        2 * normalizedDyadicCutoff L j (p + (1, 0)) +
        normalizedDyadicCutoff L j p = 0 := by
      by_contra hne
      exact hnot (lowGridActiveScales_mem_of_second_diff_ne_zero
        L j p (p + (1, 0)) (p + (1, 0) + (1, 0)) hlow hne)
    simp [hzero]
  · simpa only [cutoffSecondDiffMass] using
      sum_abs_normalizedDyadicCutoff_second_diff_low_grid_scales_le
        L ((1, 0) : Z2 L)
  · intro j hsep
    unfold cutoffSecondDiffMass cutoffSecondDiffE1ShellRemainder
    apply Finset.sum_le_sum
    intro p _
    exact abs_cutoff_second_diff_e1_shell_le L hL p
      (p + (1, 0)) (p + (1, 0) + (1, 0)) j rfl rfl hsep

/-- The separated-shell second-coordinate remainder retains its fold
defect at every starting point. -/
noncomputable def cutoffSecondDiffE2ShellRemainder
    (L : ℕ) [NeZero L] (j : ℕ) : ℝ :=
  ∑ p : Z2 L,
    (420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.2| / (2 * Real.pi)) +
      (420 * (2 : ℝ) ^ j / (dyad (j + 1) / 2) +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2)

/-- The corresponding finite-shell split along the second coordinate. -/
theorem sum_cutoffSecondDiffMass_e2_finite_shells_le
    (L N : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range N,
      cutoffSecondDiffMass L j ((0, 1) : Z2 L)) ≤
      4608 + ∑ j ∈ separatedShellIndices L N,
        cutoffSecondDiffE2ShellRemainder L j := by
  apply finite_shell_split_sum L N
    (fun j => cutoffSecondDiffMass L j ((0, 1) : Z2 L))
    (fun j => cutoffSecondDiffE2ShellRemainder L j)
  · intro j
    unfold cutoffSecondDiffMass
    exact Finset.sum_nonneg (by intro p _; exact abs_nonneg _)
  · intro j hlow hnot
    unfold cutoffSecondDiffMass
    apply Finset.sum_eq_zero
    intro p _
    have hzero : normalizedDyadicCutoff L j (p + (0, 1) + (0, 1)) -
        2 * normalizedDyadicCutoff L j (p + (0, 1)) +
        normalizedDyadicCutoff L j p = 0 := by
      by_contra hne
      exact hnot (lowGridActiveScales_mem_of_second_diff_ne_zero
        L j p (p + (0, 1)) (p + (0, 1) + (0, 1)) hlow hne)
    simp [hzero]
  · simpa only [cutoffSecondDiffMass] using
      sum_abs_normalizedDyadicCutoff_second_diff_low_grid_scales_le
        L ((0, 1) : Z2 L)
  · intro j hsep
    unfold cutoffSecondDiffMass cutoffSecondDiffE2ShellRemainder
    apply Finset.sum_le_sum
    intro p _
    exact abs_cutoff_second_diff_e2_shell_le L hL p
      (p + (0, 1)) (p + (0, 1) + (0, 1)) j rfl rfl hsep

/-- At `L=16`, both the separated and low-grid index ranges are present. -/
example : 2 ∈ separatedShellIndices 16 5 ∧
    3 ∈ lowGridActiveScales 16 ∧
    (∑ j ∈ Finset.range 5,
      cutoffSecondDiffMass 16 j ((1, 0) : Z2 16)) ≤
      4608 + ∑ j ∈ separatedShellIndices 16 5,
        cutoffSecondDiffE1ShellRemainder 16 j := by
  refine ⟨?_, ?_, sum_cutoffSecondDiffMass_e1_finite_shells_le
    16 5 (by norm_num)⟩
  · norm_num [separatedShellIndices, dyad]
  · rw [mem_lowGridActiveScales_iff]
    norm_num [dyad]

end RBM

#print axioms RBM.sum_cutoffSecondDiffMass_e1_finite_shells_le
#print axioms RBM.sum_cutoffSecondDiffMass_e2_finite_shells_le
