/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffLowGridSum

/-!
# Counting active low-grid dyadic scales

The scale window imposed by low-grid support has ratio eight. Since dyadic
scales halve at each step, it contains at most three indices. The candidate
set is explicitly finite for each lattice side length.
-/

namespace RBM

private theorem dyadic_index_lt_four_mul_L
    (L j : ℕ) [NeZero L]
    (hscale : 1 / (L : ℝ) ≤ 4 * dyad (j + 1)) :
    j < 4 * L := by
  have hL : 0 < (L : ℝ) := cast_L_pos L
  have hpow : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hscale' : 1 / (L : ℝ) ≤ 4 / (2 : ℝ) ^ (j + 1) := by
    simpa only [dyad, inv_pow, div_eq_mul_inv] using hscale
  have hpowR : (2 : ℝ) ^ (j + 1) ≤ 4 * (L : ℝ) := by
    have h := (div_le_div_iff₀ hL hpow).mp hscale'
    nlinarith
  have hpowN : (2 : ℕ) ^ (j + 1) ≤ 4 * L := by exact_mod_cast hpowR
  have hj : j + 1 < (2 : ℕ) ^ (j + 1) :=
    Nat.lt_pow_self (by norm_num)
  omega

/-- Explicit finite set of dyadic indices in the possible low-grid support
window `1/L ≤ 4·dyad(j+1) < 8/L`. -/
noncomputable def lowGridActiveScales (L : ℕ) [NeZero L] : Finset ℕ :=
  (Finset.range (4 * L)).filter (fun j =>
    dyad (j + 1) < 2 / (L : ℝ) ∧
      1 / (L : ℝ) ≤ 4 * dyad (j + 1))

theorem mem_lowGridActiveScales_iff (L : ℕ) [NeZero L] (j : ℕ) :
    j ∈ lowGridActiveScales L ↔
      dyad (j + 1) < 2 / (L : ℝ) ∧
        1 / (L : ℝ) ≤ 4 * dyad (j + 1) := by
  classical
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (dyadic_index_lt_four_mul_L L j hj.2), hj⟩

/-- A nonzero cutoff second difference on a low-grid shell has an index in
the finite active-scale set. -/
theorem lowGridActiveScales_mem_of_second_diff_ne_zero
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hlow : dyad (j + 1) < 2 / (L : ℝ))
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    j ∈ lowGridActiveScales L := by
  apply (mem_lowGridActiveScales_iff L j).2
  exact ⟨hlow, cutoff_second_diff_support_grid_lower_scale L j p q r hsecond⟩

private theorem dyad_add_three (j : ℕ) :
    dyad (j + 3) = dyad j / 8 := by
  unfold dyad
  rw [pow_add]
  norm_num
  ring

/-- Two indices in the active window differ by fewer than three. -/
theorem lowGridActiveScales_gap_lt_three
    (L : ℕ) [NeZero L] (i j : ℕ)
    (hi : i ∈ lowGridActiveScales L)
    (hj : j ∈ lowGridActiveScales L) :
    j < i + 3 := by
  obtain ⟨hiLow, _⟩ := (mem_lowGridActiveScales_iff L i).1 hi
  obtain ⟨_, hjHigh⟩ := (mem_lowGridActiveScales_iff L j).1 hj
  by_contra hnot
  have hgap : i + 4 ≤ j + 1 := by omega
  have hmono : dyad (j + 1) ≤ dyad (i + 4) :=
    dyad_le_dyad_of_le hgap
  have hrel : dyad (i + 4) = dyad (i + 1) / 8 := by
    simpa [Nat.add_assoc] using dyad_add_three (i + 1)
  have hL : 0 < (L : ℝ) := cast_L_pos L
  have hiLow' : dyad (i + 1) < 2 * (1 / (L : ℝ)) := by
    calc
      _ < 2 / (L : ℝ) := hiLow
      _ = 2 * (1 / (L : ℝ)) := by ring
  rw [hrel] at hmono
  linarith

/-- The low-grid support window contains at most three dyadic indices. -/
theorem card_lowGridActiveScales_le_three
    (L : ℕ) [NeZero L] :
    (lowGridActiveScales L).card ≤ 3 := by
  classical
  let S := lowGridActiveScales L
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := Finset.min'_mem S hS
    have hsubset : S ⊆ Finset.Icc m (m + 2) := by
      intro j hj
      have hmin : m ≤ j := Finset.min'_le S j hj
      have hmax : j ≤ m + 2 := by
        have hgap := lowGridActiveScales_gap_lt_three L m j hm hj
        omega
      simp only [Finset.mem_Icc]
      exact ⟨hmin, hmax⟩
    have h := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at h
    dsimp [S] at h
    omega
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hzero]

/-- The total absolute second difference over all possible low-grid shells
is at most `3·1536=4608`, for any fixed lattice displacement. -/
theorem sum_abs_normalizedDyadicCutoff_second_diff_low_grid_scales_le
    (L : ℕ) [NeZero L] (e : Z2 L) :
    (∑ j ∈ lowGridActiveScales L,
      ∑ p : Z2 L,
        |normalizedDyadicCutoff L j (p + e + e) -
          2 * normalizedDyadicCutoff L j (p + e) +
          normalizedDyadicCutoff L j p|) ≤ (4608 : ℝ) := by
  have hsum : (∑ j ∈ lowGridActiveScales L,
      ∑ p : Z2 L,
        |normalizedDyadicCutoff L j (p + e + e) -
          2 * normalizedDyadicCutoff L j (p + e) +
          normalizedDyadicCutoff L j p|) ≤
      ∑ _j ∈ lowGridActiveScales L, (1536 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact sum_abs_normalizedDyadicCutoff_second_diff_low_grid_le
      L j e ((mem_lowGridActiveScales_iff L j).1 hj).1
  have hcard := card_lowGridActiveScales_le_three L
  have hcardR : ((lowGridActiveScales L).card : ℝ) ≤ 3 := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ _j ∈ lowGridActiveScales L, (1536 : ℝ) := hsum
    _ = ((lowGridActiveScales L).card : ℝ) * 1536 := by simp
    _ ≤ 4608 := by linarith

/-- The active low-grid index set is nonempty for a concrete side length. -/
example : 3 ∈ lowGridActiveScales 16 := by
  rw [mem_lowGridActiveScales_iff]
  norm_num [dyad]

end RBM

#print axioms RBM.mem_lowGridActiveScales_iff
#print axioms RBM.lowGridActiveScales_mem_of_second_diff_ne_zero
#print axioms RBM.lowGridActiveScales_gap_lt_three
#print axioms RBM.card_lowGridActiveScales_le_three
#print axioms RBM.sum_abs_normalizedDyadicCutoff_second_diff_low_grid_scales_le
