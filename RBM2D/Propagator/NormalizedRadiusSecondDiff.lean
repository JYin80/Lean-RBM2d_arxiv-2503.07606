/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffOuterFlat

/-!
# Second differences of normalized radius away from folds

The angular distance on `ZMod L` has a fold at the antipodal point. A
quadratic second-difference estimate therefore requires an explicit affine
condition on the angular coordinate across the three sampled frequencies.
The positive middle radius controls the Euclidean norm's curvature.
-/

namespace RBM

private theorem abs_second_le_of_sq_diff
    {a b c ε ρ : ℝ} (hρ : 0 < ρ) (hb : ρ ≤ b)
    (hε : 0 ≤ ε)
    (h₁ : |b - a| ≤ ε) (h₂ : |c - b| ≤ ε)
    (hsq₀ : 0 ≤ c ^ 2 - 2 * b ^ 2 + a ^ 2)
    (hsq₁ : c ^ 2 - 2 * b ^ 2 + a ^ 2 ≤ 2 * ε ^ 2) :
    |c - 2 * b + a| ≤ ε ^ 2 / ρ := by
  have h₁sq : (b - a) ^ 2 ≤ ε ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 h₁
    simpa only [sq_abs] using h
  have h₂sq : (c - b) ^ 2 ≤ ε ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 h₂
    simpa only [sq_abs] using h
  have hident : 2 * b * (c - 2 * b + a) =
      (c ^ 2 - 2 * b ^ 2 + a ^ 2) -
        (c - b) ^ 2 - (a - b) ^ 2 := by ring
  have hlow : -(2 * ε ^ 2) ≤ 2 * b * (c - 2 * b + a) := by
    rw [hident]
    nlinarith [sq_nonneg (a - b)]
  have hupp : 2 * b * (c - 2 * b + a) ≤ 2 * ε ^ 2 := by
    rw [hident]
    nlinarith [sq_nonneg (c - b), sq_nonneg (a - b)]
  have hbpos : 0 < b := lt_of_lt_of_le hρ hb
  have habs : |2 * b * (c - 2 * b + a)| ≤ 2 * ε ^ 2 :=
    abs_le.mpr ⟨hlow, hupp⟩
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * b)] at habs
  have hbabs : b * |c - 2 * b + a| ≤ ε ^ 2 := by nlinarith
  have hρabs : ρ * |c - 2 * b + a| ≤ ε ^ 2 :=
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans hbabs
  exact (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hρabs)

/-- The squared normalized radius is the squared physical radius divided by
the square of the normalization factor `2π`. -/
theorem normalizedFrequency_sq (L : ℕ) [NeZero L] (p : Z2 L) :
    (normalizedFrequency L p) ^ 2 =
      pstar2 L p / (2 * Real.pi) ^ 2 := by
  unfold normalizedFrequency
  rw [div_pow, Real.sq_sqrt (pstar2_nonneg L p)]

private theorem second_sq_of_affine_e1 (L : ℕ) [NeZero L]
    (p q r : Z2 L) (hq : q = p + (1, 0))
    (hr : r = q + (1, 0))
    (haffine : pstar L r.1 - 2 * pstar L q.1 + pstar L p.1 = 0) :
    pstar2 L r - 2 * pstar2 L q + pstar2 L p =
      2 * (pstar L q.1 - pstar L p.1) ^ 2 := by
  have hq₂ : q.2 = p.2 := by simp [hq]
  have hr₂ : r.2 = p.2 := by simp [hr, hq]
  have hr₁ : pstar L r.1 = 2 * pstar L q.1 - pstar L p.1 := by
    linarith
  simp only [pstar2, hq₂, hr₂, hr₁]
  ring

private theorem second_sq_of_affine_e2 (L : ℕ) [NeZero L]
    (p q r : Z2 L) (hq : q = p + (0, 1))
    (hr : r = q + (0, 1))
    (haffine : pstar L r.2 - 2 * pstar L q.2 + pstar L p.2 = 0) :
    pstar2 L r - 2 * pstar2 L q + pstar2 L p =
      2 * (pstar L q.2 - pstar L p.2) ^ 2 := by
  have hq₁ : q.1 = p.1 := by simp [hq]
  have hr₁ : r.1 = p.1 := by simp [hr, hq]
  have hr₂ : pstar L r.2 = 2 * pstar L q.2 - pstar L p.2 := by
    linarith
  simp only [pstar2, hq₁, hr₁, hr₂]
  ring

private theorem normalized_second_sq_of_physical_sq (L : ℕ) [NeZero L]
    (p q r : Z2 L) (d : ℝ)
    (hsq : pstar2 L r - 2 * pstar2 L q + pstar2 L p = 2 * d ^ 2) :
    (normalizedFrequency L r) ^ 2 -
        2 * (normalizedFrequency L q) ^ 2 +
        (normalizedFrequency L p) ^ 2 =
      2 * (d / (2 * Real.pi)) ^ 2 := by
  rw [normalizedFrequency_sq, normalizedFrequency_sq,
    normalizedFrequency_sq]
  rw [div_pow]
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp [hpi]
  nlinarith [hsq]

private theorem abs_pstar_shift_one_le_grid (L : ℕ) [NeZero L]
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

private theorem abs_normalizedFrequency_second_diff_of_affine (L : ℕ)
    [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (ρ d : ℝ)
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (hstep₁ : |normalizedFrequency L q - normalizedFrequency L p| ≤
      symbolGridStep L / (2 * Real.pi))
    (hstep₂ : |normalizedFrequency L r - normalizedFrequency L q| ≤
      symbolGridStep L / (2 * Real.pi))
    (hd : |d| ≤ symbolGridStep L)
    (hsq : pstar2 L r - 2 * pstar2 L q + pstar2 L p = 2 * d ^ 2) :
    |normalizedFrequency L r - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤
      (1 / (L : ℝ)) ^ 2 / ρ := by
  have hε : 0 ≤ symbolGridStep L / (2 * Real.pi) := by
    unfold symbolGridStep
    positivity
  have hratio : |d / (2 * Real.pi)| ≤
      symbolGridStep L / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (div_le_div_iff_of_pos_right
      (by positivity : 0 < 2 * Real.pi)).2 hd
  have hratioSq : (d / (2 * Real.pi)) ^ 2 ≤
      (symbolGridStep L / (2 * Real.pi)) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 hratio
    simpa only [sq_abs] using h
  have hsq' := normalized_second_sq_of_physical_sq L p q r d hsq
  have hsq₀ : 0 ≤ (normalizedFrequency L r) ^ 2 -
      2 * (normalizedFrequency L q) ^ 2 +
      (normalizedFrequency L p) ^ 2 := by
    rw [hsq']
    positivity
  have hsq₁ : (normalizedFrequency L r) ^ 2 -
      2 * (normalizedFrequency L q) ^ 2 +
      (normalizedFrequency L p) ^ 2 ≤
      2 * (symbolGridStep L / (2 * Real.pi)) ^ 2 := by
    rw [hsq']
    linarith
  have h := abs_second_le_of_sq_diff hρ hmiddle hε
    hstep₁ hstep₂ hsq₀ hsq₁
  simpa only [normalizedGridStep_eq_inv] using h

/-- Away from an antipodal fold, the first-coordinate radius difference is
quadratic in `1/L`. A positive lower bound at the middle point suffices. -/
theorem abs_normalizedFrequency_second_diff_e1_le_of_affine
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (ρ : ℝ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (haffine : pstar L r.1 - 2 * pstar L q.1 + pstar L p.1 = 0) :
    |normalizedFrequency L r - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  have hstep₁ : |normalizedFrequency L q - normalizedFrequency L p| ≤
      symbolGridStep L / (2 * Real.pi) := by
    rw [hq]
    exact abs_normalizedFrequency_shift_e1_le L hL p
  have hstep₂ : |normalizedFrequency L r - normalizedFrequency L q| ≤
      symbolGridStep L / (2 * Real.pi) := by
    rw [hr]
    exact abs_normalizedFrequency_shift_e1_le L hL q
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hd : |pstar L q.1 - pstar L p.1| ≤ symbolGridStep L := by
    rw [hq₁]
    exact abs_pstar_shift_one_le_grid L hL p.1
  exact abs_normalizedFrequency_second_diff_of_affine L hL p q r ρ
    (pstar L q.1 - pstar L p.1) hρ hmiddle hstep₁ hstep₂ hd
    (second_sq_of_affine_e1 L p q r hq hr haffine)

/-- The same quadratic radius estimate in the second coordinate. -/
theorem abs_normalizedFrequency_second_diff_e2_le_of_affine
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (ρ : ℝ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (haffine : pstar L r.2 - 2 * pstar L q.2 + pstar L p.2 = 0) :
    |normalizedFrequency L r - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  have hstep₁ : |normalizedFrequency L q - normalizedFrequency L p| ≤
      symbolGridStep L / (2 * Real.pi) := by
    rw [hq]
    exact abs_normalizedFrequency_shift_e2_le L hL p
  have hstep₂ : |normalizedFrequency L r - normalizedFrequency L q| ≤
      symbolGridStep L / (2 * Real.pi) := by
    rw [hr]
    exact abs_normalizedFrequency_shift_e2_le L hL q
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hd : |pstar L q.2 - pstar L p.2| ≤ symbolGridStep L := by
    rw [hq₂]
    exact abs_pstar_shift_one_le_grid L hL p.2
  exact abs_normalizedFrequency_second_diff_of_affine L hL p q r ρ
    (pstar L q.2 - pstar L p.2) hρ hmiddle hstep₁ hstep₂ hd
    (second_sq_of_affine_e2 L p q r hq hr haffine)

/-- A nonzero, nonfolded example with positive middle radius. -/
example :
    |normalizedFrequency 8 ((3, 0) : Z2 8) -
        2 * normalizedFrequency 8 ((2, 0) : Z2 8) +
        normalizedFrequency 8 ((1, 0) : Z2 8)| ≤
      (1 / (8 : ℝ)) ^ 2 / (1 / 4 : ℝ) := by
  apply abs_normalizedFrequency_second_diff_e1_le_of_affine 8
    (by norm_num) (1, 0) (2, 0) (3, 0) (1 / 4)
    (by decide) (by decide) (by norm_num)
  · have hz : zdist 8 (2 : ZMod 8) = 2 := by decide
    have hrad : pstar2 8 ((2, 0) : Z2 8) = (Real.pi / 2) ^ 2 := by
      simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
        Nat.cast_zero, mul_zero, zero_div]
      ring
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi / 2)]
    field_simp [Real.pi_ne_zero]
    norm_num
  · have hz₁ : zdist 8 (1 : ZMod 8) = 1 := by decide
    have hz₂ : zdist 8 (2 : ZMod 8) = 2 := by decide
    have hz₃ : zdist 8 (3 : ZMod 8) = 3 := by decide
    norm_num [pstar, hz₁, hz₂, hz₃]
    ring

/-- Concrete antipodal fold: the radius is far from zero, while its second
difference has the first-order size `2/L = 1/4` for `L=8`. -/
theorem normalizedFrequency_antipodal_fold_example :
    |normalizedFrequency 8 ((5, 0) : Z2 8) -
        2 * normalizedFrequency 8 ((4, 0) : Z2 8) +
        normalizedFrequency 8 ((3, 0) : Z2 8)| = 1 / 4 := by
  have hν₃ : normalizedFrequency 8 ((3, 0) : Z2 8) = 3 / 8 := by
    have hz : zdist 8 (3 : ZMod 8) = 3 := by decide
    have hrad : pstar2 8 ((3, 0) : Z2 8) = (3 * Real.pi / 4) ^ 2 := by
      simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
        Nat.cast_zero, mul_zero, zero_div]
      ring
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < 3 * Real.pi / 4)]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hν₄ : normalizedFrequency 8 ((4, 0) : Z2 8) = 1 / 2 := by
    have hz : zdist 8 (4 : ZMod 8) = 4 := by decide
    have hrad : pstar2 8 ((4, 0) : Z2 8) = Real.pi ^ 2 := by
      simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
        Nat.cast_zero, mul_zero, zero_div]
      ring
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  have hν₅ : normalizedFrequency 8 ((5, 0) : Z2 8) = 3 / 8 := by
    have hz : zdist 8 (5 : ZMod 8) = 3 := by decide
    have hrad : pstar2 8 ((5, 0) : Z2 8) = (3 * Real.pi / 4) ^ 2 := by
      simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
        Nat.cast_zero, mul_zero, zero_div]
      ring
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < 3 * Real.pi / 4)]
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hν₃, hν₄, hν₅]
  norm_num

end RBM

#print axioms RBM.normalizedFrequency_sq
#print axioms RBM.abs_normalizedFrequency_second_diff_e1_le_of_affine
#print axioms RBM.abs_normalizedFrequency_second_diff_e2_le_of_affine
#print axioms RBM.normalizedFrequency_antipodal_fold_example
