/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedFrequency
import RBM2D.Propagator.SymbolShiftAnnulus

/-!
# Finite differences of the normalized dyadic cutoff

The normalized Euclidean frequency is Lipschitz under a coordinate step,
including at zero momentum. This gives a global first-difference bound.
-/

namespace RBM

private theorem pstar_shift_one_le_grid (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
    pstar L (u + 1) ≤ pstar L u + symbolGridStep L := by
  have hz : zdist L (u + 1) ≤ zdist L u + 1 := by
    have h := zdist_add_le L u (1 : ZMod L)
    have h1 := zdist_one_le L hL
    omega
  have hz' : (zdist L (u + 1) : ℝ) ≤ (zdist L u : ℝ) + 1 := by
    exact_mod_cast hz
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

private theorem abs_pstar_shift_one_le_grid (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
    |pstar L (u + 1) - pstar L u| ≤ symbolGridStep L := by
  apply abs_le.mpr
  constructor
  · have h := pstar_le_shift_one L hL u
    linarith
  · have h := pstar_shift_one_le_grid L hL u
    linarith

private noncomputable def momentumComplex (L : ℕ) [NeZero L]
    (p : Z2 L) : ℂ :=
  (pstar L p.1 : ℂ) + (pstar L p.2 : ℂ) * Complex.I

private theorem norm_momentumComplex (L : ℕ) [NeZero L] (p : Z2 L) :
    ‖momentumComplex L p‖ = Real.sqrt (pstar2 L p) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [momentumComplex, pstar2, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring_nf

private theorem abs_sqrt_pstar2_shift_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    |Real.sqrt (pstar2 L (p + (1, 0))) - Real.sqrt (pstar2 L p)| ≤
      symbolGridStep L := by
  have hnorm := abs_norm_sub_norm_le
    (momentumComplex L (p + (1, 0))) (momentumComplex L p)
  rw [norm_momentumComplex, norm_momentumComplex] at hnorm
  have hdiff : momentumComplex L (p + (1, 0)) - momentumComplex L p =
      ((pstar L (p.1 + 1) - pstar L p.1 : ℝ) : ℂ) := by
    unfold momentumComplex
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm.trans (abs_pstar_shift_one_le_grid L hL p.1)

private theorem abs_sqrt_pstar2_shift_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    |Real.sqrt (pstar2 L (p + (0, 1))) - Real.sqrt (pstar2 L p)| ≤
      symbolGridStep L := by
  have hnorm := abs_norm_sub_norm_le
    (momentumComplex L (p + (0, 1))) (momentumComplex L p)
  rw [norm_momentumComplex, norm_momentumComplex] at hnorm
  have hdiff : momentumComplex L (p + (0, 1)) - momentumComplex L p =
      ((pstar L (p.2 + 1) - pstar L p.2 : ℝ) : ℂ) * Complex.I := by
    unfold momentumComplex
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    push_cast
    ring_nf
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one] at hnorm
  exact hnorm.trans (abs_pstar_shift_one_le_grid L hL p.2)

/-- A coordinate step changes normalized frequency by at most `1/L`. -/
theorem abs_normalizedFrequency_shift_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    |normalizedFrequency L (p + (1, 0)) - normalizedFrequency L p| ≤
      symbolGridStep L / (2 * Real.pi) := by
  have h := abs_sqrt_pstar2_shift_e1_le L hL p
  unfold normalizedFrequency
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).2 h

/-- The same normalized-frequency bound for a second-coordinate step. -/
theorem abs_normalizedFrequency_shift_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    |normalizedFrequency L (p + (0, 1)) - normalizedFrequency L p| ≤
      symbolGridStep L / (2 * Real.pi) := by
  have h := abs_sqrt_pstar2_shift_e2_le L hL p
  unfold normalizedFrequency
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).2 h

private theorem abs_lowPassD1_le (t : ℝ) : |lowPassD1 t| ≤ 140 := by
  by_cases h₁ : t ≤ 1
  · simp [lowPassD1, h₁]
  by_cases h₂ : t ≤ 2
  · have hx₀ : 0 ≤ t - 1 := by linarith
    have hx₁ : t - 1 ≤ 1 := by linarith
    have hy₀ : 0 ≤ 1 - (t - 1) := by linarith
    have hy₁ : 1 - (t - 1) ≤ 1 := by linarith
    have hpoly : 0 ≤ smoothstep3D1 (t - 1) := by
      rw [smoothstep3D1_factor]
      positivity
    have hbound : smoothstep3D1 (t - 1) ≤ 140 := by
      rw [smoothstep3D1_factor]
      calc
        140 * (t - 1) ^ 3 * (1 - (t - 1)) ^ 3 ≤
            140 * 1 ^ 3 * 1 ^ 3 := by gcongr
        _ = 140 := by norm_num
    simp only [lowPassD1, ite_eq_right h₁, ite_eq_left h₂, abs_neg,
      abs_of_nonneg hpoly]
    exact hbound
  · simp [lowPassD1, h₁, h₂]

private theorem abs_lowPass_sub_le (u v : ℝ) :
    |lowPass v - lowPass u| ≤ 140 * |v - u| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := lowPass) (x := u) (y := v) (C := (140 : ℝ))
    (fun z _ => (hasDerivAt_lowPass z).differentiableAt)
    (fun z _ => by
      rw [(hasDerivAt_lowPass z).deriv]
      simpa only [Real.norm_eq_abs] using abs_lowPassD1_le z)
    (by simp) (by simp)
  simpa only [Real.norm_eq_abs] using h

/-- The real annular cutoff is globally Lipschitz with explicit dyadic scale. -/
theorem abs_dyadicCutoff_sub_le (j : ℕ) (u v : ℝ) :
    |dyadicCutoff j v - dyadicCutoff j u| ≤
      420 * (2 : ℝ) ^ j * |v - u| := by
  let a : ℝ := (2 : ℝ) ^ j
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h₁ := abs_lowPass_sub_le (a * u) (a * v)
  have h₂ := abs_lowPass_sub_le ((2 * a) * u) ((2 * a) * v)
  have hrepr : dyadicCutoff j v - dyadicCutoff j u =
      (lowPass (a * v) - lowPass (a * u)) -
        (lowPass ((2 * a) * v) - lowPass ((2 * a) * u)) := by
    unfold dyadicCutoff
    rw [inv_dyad j, inv_dyad (j + 1)]
    dsimp [a]
    rw [pow_succ]
    ring_nf
  rw [hrepr]
  calc
    |(lowPass (a * v) - lowPass (a * u)) -
        (lowPass ((2 * a) * v) - lowPass ((2 * a) * u))| ≤
      |lowPass (a * v) - lowPass (a * u)| +
        |lowPass ((2 * a) * v) - lowPass ((2 * a) * u)| := abs_sub _ _
    _ ≤ 140 * |a * v - a * u| + 140 * |(2 * a) * v - (2 * a) * u| :=
      add_le_add h₁ h₂
    _ = 420 * (2 : ℝ) ^ j * |v - u| := by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg (by positivity : 0 ≤ 2 * a)]
      dsimp [a]
      ring

/-- First-coordinate cutoff difference, valid even when a step crosses zero. -/
theorem abs_normalizedDyadicCutoff_shift_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (j : ℕ) (p : Z2 L) :
    |normalizedDyadicCutoff L j (p + (1, 0)) -
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
  have hcut := abs_dyadicCutoff_sub_le j
    (normalizedFrequency L p) (normalizedFrequency L (p + (1, 0)))
  have hν := abs_normalizedFrequency_shift_e1_le L hL p
  dsimp only [normalizedDyadicCutoff]
  exact hcut.trans (by gcongr)

/-- Second-coordinate cutoff difference with the same dyadic factor. -/
theorem abs_normalizedDyadicCutoff_shift_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (j : ℕ) (p : Z2 L) :
    |normalizedDyadicCutoff L j (p + (0, 1)) -
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
  have hcut := abs_dyadicCutoff_sub_le j
    (normalizedFrequency L p) (normalizedFrequency L (p + (0, 1)))
  have hν := abs_normalizedFrequency_shift_e2_le L hL p
  dsimp only [normalizedDyadicCutoff]
  exact hcut.trans (by gcongr)

/-- A global second first-coordinate difference bound from two Lipschitz steps.
It is linear in the grid step, including at zero momentum. -/
theorem abs_normalizedDyadicCutoff_second_diff_e1_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ)
    (p q r : Z2 L) (hq : q = p + (1, 0)) (hr : r = q + (1, 0)) :
    |normalizedDyadicCutoff L j r - 2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      840 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
  have hpq : |normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
    rw [hq]
    exact abs_normalizedDyadicCutoff_shift_e1_le L hL j p
  have hqr : |normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
    rw [hr]
    exact abs_normalizedDyadicCutoff_shift_e1_le L hL j q
  calc
    |normalizedDyadicCutoff L j r - 2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| =
      |(normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q) -
        (normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p)| := by ring_nf
    _ ≤ |normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q| +
        |normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The same global linear second-difference estimate in coordinate two. -/
theorem abs_normalizedDyadicCutoff_second_diff_e2_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ)
    (p q r : Z2 L) (hq : q = p + (0, 1)) (hr : r = q + (0, 1)) :
    |normalizedDyadicCutoff L j r - 2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      840 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
  have hpq : |normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
    rw [hq]
    exact abs_normalizedDyadicCutoff_shift_e2_le L hL j p
  have hqr : |normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q| ≤
      420 * (2 : ℝ) ^ j * (symbolGridStep L / (2 * Real.pi)) := by
    rw [hr]
    exact abs_normalizedDyadicCutoff_shift_e2_le L hL j q
  calc
    |normalizedDyadicCutoff L j r - 2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| =
      |(normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q) -
        (normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p)| := by ring_nf
    _ ≤ |normalizedDyadicCutoff L j r - normalizedDyadicCutoff L j q| +
        |normalizedDyadicCutoff L j q - normalizedDyadicCutoff L j p| := abs_sub _ _
    _ ≤ _ := by linarith

end RBM

#print axioms RBM.abs_normalizedFrequency_shift_e1_le
#print axioms RBM.abs_normalizedFrequency_shift_e2_le
#print axioms RBM.abs_normalizedDyadicCutoff_shift_e1_le
#print axioms RBM.abs_normalizedDyadicCutoff_shift_e2_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e1_le
#print axioms RBM.abs_normalizedDyadicCutoff_second_diff_e2_le
