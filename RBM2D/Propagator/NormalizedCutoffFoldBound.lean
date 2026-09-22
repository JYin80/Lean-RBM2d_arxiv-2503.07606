/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedRadiusFoldCorrection

/-!
# Cutoff second differences with an explicit fold defect

The last radius is compared with the radius of the affine continuation of
the first coordinate step. The comparison costs exactly the angular fold
defect times the cutoff's Lipschitz scale. The remaining affine-path term is
kept visible for a later second-derivative estimate.
-/

namespace RBM

/-- The hypothetical normalized radius after one more affine coordinate step. -/
noncomputable def affineFrequencyE1 (L : ℕ) [NeZero L]
    (p q : Z2 L) : ℝ :=
  Real.sqrt ((2 * pstar L q.1 - pstar L p.1) ^ 2 +
    (pstar L p.2) ^ 2) / (2 * Real.pi)

/-- The analogous affine continuation in the second coordinate. -/
noncomputable def affineFrequencyE2 (L : ℕ) [NeZero L]
    (p q : Z2 L) : ℝ :=
  Real.sqrt ((pstar L p.1) ^ 2 +
    (2 * pstar L q.2 - pstar L p.2) ^ 2) / (2 * Real.pi)

private theorem abs_radial_sqrt_sub_le (x y t : ℝ) :
    |Real.sqrt (x ^ 2 + t ^ 2) - Real.sqrt (y ^ 2 + t ^ 2)| ≤
      |x - y| := by
  let zx : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  let zy : ℂ := (y : ℂ) + (t : ℂ) * Complex.I
  have hx : ‖zx‖ = Real.sqrt (x ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [zx, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  have hy : ‖zy‖ = Real.sqrt (y ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [zy, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  have hdiff : zx - zy = ((x - y : ℝ) : ℂ) := by
    dsimp [zx, zy]
    push_cast
    ring
  have h := abs_norm_sub_norm_le zx zy
  rw [hx, hy, hdiff, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

private theorem abs_normalized_radial_sub_le (x y t : ℝ) :
    |Real.sqrt (x ^ 2 + t ^ 2) / (2 * Real.pi) -
        Real.sqrt (y ^ 2 + t ^ 2) / (2 * Real.pi)| ≤
      |x - y| / (2 * Real.pi) := by
  have h := abs_radial_sqrt_sub_le x y t
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact (div_le_div_iff_of_pos_right
    (by positivity : 0 < 2 * Real.pi)).2 h

/-- The actual first-coordinate radius differs from its affine continuation
by at most the normalized fold defect. No lower-radius premise is needed. -/
theorem abs_normalizedFrequency_sub_affineFrequencyE1_le
    (L : ℕ) [NeZero L] (p q r : Z2 L)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0)) :
    |normalizedFrequency L r - affineFrequencyE1 L p q| ≤
      |pstarFoldDefect L p.1| / (2 * Real.pi) := by
  have hr₂ : r.2 = p.2 := by simp [hr, hq]
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hr₁ : r.1 = p.1 + 1 + 1 := by rw [hr, hq]; rfl
  have h := abs_normalized_radial_sub_le
    (pstar L r.1) (2 * pstar L q.1 - pstar L p.1) (pstar L p.2)
  have hdef : pstar L r.1 - (2 * pstar L q.1 - pstar L p.1) =
      pstarFoldDefect L p.1 := by
    rw [hr₁, hq₁]
    unfold pstarFoldDefect
    ring
  simpa only [normalizedFrequency, pstar2, affineFrequencyE1,
    hr₂, hdef] using h

/-- The same fold-defect comparison in the second coordinate. -/
theorem abs_normalizedFrequency_sub_affineFrequencyE2_le
    (L : ℕ) [NeZero L] (p q r : Z2 L)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1)) :
    |normalizedFrequency L r - affineFrequencyE2 L p q| ≤
      |pstarFoldDefect L p.2| / (2 * Real.pi) := by
  have hr₁ : r.1 = p.1 := by simp [hr, hq]
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hr₂ : r.2 = p.2 + 1 + 1 := by rw [hr, hq]; rfl
  have h := abs_normalized_radial_sub_le
    (pstar L r.2) (2 * pstar L q.2 - pstar L p.2) (pstar L p.1)
  have hdef : pstar L r.2 - (2 * pstar L q.2 - pstar L p.2) =
      pstarFoldDefect L p.2 := by
    rw [hr₂, hq₂]
    unfold pstarFoldDefect
    ring
  have hrad : (pstar L p.1) ^ 2 + (pstar L r.2) ^ 2 =
      (pstar L r.2) ^ 2 + (pstar L p.1) ^ 2 := by ring
  have haff : (pstar L p.1) ^ 2 +
      (2 * pstar L q.2 - pstar L p.2) ^ 2 =
      (2 * pstar L q.2 - pstar L p.2) ^ 2 +
        (pstar L p.1) ^ 2 := by ring
  simpa only [normalizedFrequency, pstar2, affineFrequencyE2,
    hr₁, hrad, haff, hdef] using h

/-- First-coordinate cutoff second difference, split into an affine-path
curvature term and an explicit fold-defect term. -/
theorem abs_normalizedDyadicCutoff_second_diff_e1_fold_le
    (L : ℕ) [NeZero L] (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0)) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.1| / (2 * Real.pi)) +
      |dyadicCutoff j (affineFrequencyE1 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| := by
  have hcut := abs_dyadicCutoff_sub_le j
    (affineFrequencyE1 L p q) (normalizedFrequency L r)
  have hrad := abs_normalizedFrequency_sub_affineFrequencyE1_le L p q r hq hr
  have hfold : |normalizedDyadicCutoff L j r -
      dyadicCutoff j (affineFrequencyE1 L p q)| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.1| / (2 * Real.pi)) := by
    exact hcut.trans (by gcongr)
  have hrepr : normalizedDyadicCutoff L j r -
      2 * normalizedDyadicCutoff L j q +
      normalizedDyadicCutoff L j p =
    (normalizedDyadicCutoff L j r -
      dyadicCutoff j (affineFrequencyE1 L p q)) +
      (dyadicCutoff j (affineFrequencyE1 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p) := by ring
  rw [hrepr]
  exact (abs_add_le _ _).trans (add_le_add_left hfold _)

/-- Second-coordinate cutoff second difference with the same fold term. -/
theorem abs_normalizedDyadicCutoff_second_diff_e2_fold_le
    (L : ℕ) [NeZero L] (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1)) :
    |normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.2| / (2 * Real.pi)) +
      |dyadicCutoff j (affineFrequencyE2 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| := by
  have hcut := abs_dyadicCutoff_sub_le j
    (affineFrequencyE2 L p q) (normalizedFrequency L r)
  have hrad := abs_normalizedFrequency_sub_affineFrequencyE2_le L p q r hq hr
  have hfold : |normalizedDyadicCutoff L j r -
      dyadicCutoff j (affineFrequencyE2 L p q)| ≤
      420 * (2 : ℝ) ^ j *
        (|pstarFoldDefect L p.2| / (2 * Real.pi)) := by
    exact hcut.trans (by gcongr)
  have hrepr : normalizedDyadicCutoff L j r -
      2 * normalizedDyadicCutoff L j q +
      normalizedDyadicCutoff L j p =
    (normalizedDyadicCutoff L j r -
      dyadicCutoff j (affineFrequencyE2 L p q)) +
      (dyadicCutoff j (affineFrequencyE2 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p) := by ring
  rw [hrepr]
  exact (abs_add_le _ _).trans (add_le_add_left hfold _)

/-- The first-coordinate cutoff second difference is exactly zero in either
previously established two-step flat region. -/
theorem normalizedDyadicCutoff_second_diff_e1_eq_zero_of_flat
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hflat :
      normalizedFrequency L p + 2 / (L : ℝ) ≤ dyad (j + 1) ∨
        2 * dyad j ≤ normalizedFrequency L p - 2 / (L : ℝ)) :
    normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p = 0 := by
  rcases hflat with hinner | houter
  · obtain ⟨hp, hq', hr'⟩ :=
      normalizedDyadicCutoff_eq_zero_e1_triple L hL j p q r hq hr hinner
    simp [hp, hq', hr']
  · obtain ⟨hp, hq', hr'⟩ :=
      normalizedDyadicCutoff_eq_zero_e1_outer_triple L hL j p q r hq hr houter
    simp [hp, hq', hr']

/-- The second-coordinate cutoff second difference also vanishes in both
two-step flat regions. -/
theorem normalizedDyadicCutoff_second_diff_e2_eq_zero_of_flat
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hflat :
      normalizedFrequency L p + 2 / (L : ℝ) ≤ dyad (j + 1) ∨
        2 * dyad j ≤ normalizedFrequency L p - 2 / (L : ℝ)) :
    normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p = 0 := by
  rcases hflat with hinner | houter
  · obtain ⟨hp, hq', hr'⟩ :=
      normalizedDyadicCutoff_eq_zero_e2_triple L hL j p q r hq hr hinner
    simp [hp, hq', hr']
  · obtain ⟨hp, hq', hr'⟩ :=
      normalizedDyadicCutoff_eq_zero_e2_outer_triple L hL j p q r hq hr houter
    simp [hp, hq', hr']

/-- The antipodal three-point path has a genuine, nonzero fold defect. -/
theorem pstarFoldDefect_antipodal_nonzero :
    pstarFoldDefect 8 (3 : ZMod 8) ≠ 0 := by
  rw [pstarFoldDefect_antipodal_example]
  have hg : 0 < symbolGridStep 8 := by
    unfold symbolGridStep
    positivity
  linarith

end RBM

#print axioms RBM.abs_normalizedFrequency_sub_affineFrequencyE1_le
#print axioms RBM.abs_normalizedFrequency_sub_affineFrequencyE2_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e1_fold_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e2_fold_le
#print axioms RBM.normalizedDyadicCutoff_second_diff_e1_eq_zero_of_flat
#print axioms RBM.normalizedDyadicCutoff_second_diff_e2_eq_zero_of_flat
#print axioms RBM.pstarFoldDefect_antipodal_nonzero
