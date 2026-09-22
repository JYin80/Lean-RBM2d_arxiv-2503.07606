/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffLowGridCount

/-!
# One-shell low-grid cutoff sum

Each cutoff weight lies in `[0,1]`, so each two-step difference has absolute
value at most two. The uniform support count then bounds its `ℓ¹` mass on
each low-grid shell. Summation over shell indices is not included here.
-/

namespace RBM

/-- The normalized annular cutoff takes values in `[0,1]`. -/
theorem normalizedDyadicCutoff_mem_unit_interval
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) :
    0 ≤ normalizedDyadicCutoff L j p ∧
      normalizedDyadicCutoff L j p ≤ 1 := by
  exact ⟨dyadicCutoff_nonneg j (normalizedFrequency L p),
    dyadicCutoff_le_one j (normalizedFrequency L p)⟩

/-- The absolute second difference of any three annular cutoff weights is
at most two, independent of folds and grid size. -/
theorem abs_normalizedDyadicCutoff_second_diff_le_two
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤ 2 := by
  obtain ⟨hp₀, hp₁⟩ := normalizedDyadicCutoff_mem_unit_interval L j p
  obtain ⟨hq₀, hq₁⟩ := normalizedDyadicCutoff_mem_unit_interval L j q
  obtain ⟨hr₀, hr₁⟩ := normalizedDyadicCutoff_mem_unit_interval L j r
  apply abs_le.mpr
  constructor <;> linarith

/-- The total absolute second difference on one low-grid shell is at most
`2·768=1536`, uniformly in lattice side length, shell, and displacement. -/
theorem sum_abs_normalizedDyadicCutoff_second_diff_low_grid_le
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L)
    (hlow : dyad (j + 1) < 2 / (L : ℝ)) :
    (∑ p : Z2 L, |normalizedDyadicCutoff L j (p + e + e) -
        2 * normalizedDyadicCutoff L j (p + e) +
        normalizedDyadicCutoff L j p|) ≤ (1536 : ℝ) := by
  classical
  let F : Z2 L → ℝ := fun p =>
    normalizedDyadicCutoff L j (p + e + e) -
      2 * normalizedDyadicCutoff L j (p + e) +
      normalizedDyadicCutoff L j p
  let S := lowGridTwoStepStarts L j e
  have hmem (p : Z2 L) : p ∈ S ↔ F p ≠ 0 := by
    simp [S, F, lowGridTwoStepStarts]
  have hsum : (∑ p : Z2 L, |F p|) = ∑ p ∈ S, |F p| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    have hF : F p = 0 := by
      by_contra hn
      exact hp ((hmem p).2 hn)
    simp [hF]
  have hpoint (p : Z2 L) : |F p| ≤ 2 :=
    abs_normalizedDyadicCutoff_second_diff_le_two L j p (p + e) (p + e + e)
  have hbound : (∑ p ∈ S, |F p|) ≤ ∑ _p ∈ S, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro p _
    exact hpoint p
  have hcard : S.card ≤ 768 := card_lowGridTwoStepStarts_le L j e hlow
  have hcardR : (S.card : ℝ) ≤ 768 := by exact_mod_cast hcard
  change (∑ p : Z2 L, |F p|) ≤ (1536 : ℝ)
  rw [hsum]
  calc
    (∑ p ∈ S, |F p|) ≤ ∑ _p ∈ S, (2 : ℝ) := hbound
    _ = (S.card : ℝ) * 2 := by simp
    _ ≤ 1536 := by linarith

/-- A concrete low-grid shell (the middle cutoff at `(2,0)` is nonzero). -/
example :
    (∑ p : Z2 16,
      |normalizedDyadicCutoff 16 3 (p + (1, 0) + (1, 0)) -
        2 * normalizedDyadicCutoff 16 3 (p + (1, 0)) +
        normalizedDyadicCutoff 16 3 p|) ≤ (1536 : ℝ) := by
  apply sum_abs_normalizedDyadicCutoff_second_diff_low_grid_le
  norm_num [dyad]

end RBM

#print axioms RBM.normalizedDyadicCutoff_mem_unit_interval
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_le_two
#print axioms RBM.sum_abs_normalizedDyadicCutoff_second_diff_low_grid_le
