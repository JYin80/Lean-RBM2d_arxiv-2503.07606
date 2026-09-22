/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ZeroMode
import RBM2D.Propagator.LatticeSum

/-!
# Large-step finite differences of the two-dimensional propagator

Section 8.3, Case 2 of the paper. When `2 * |s|_L > |u|_L`, the zero Fourier
mode cancels and a crude bound on every remaining plane-wave difference is
enough. The punctured two-dimensional lattice sum is logarithmic. The ratio
`|s|_L / (|u|_L + 1)` is bounded below in this regime, so the logarithm is
absorbed by the deterministic-domination prefactor in Property 6.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

/-- A nonzero Fourier term of a first difference is bounded by twice the
inverse-square momentum weight. The constant comes from `eq_elliptic`. -/
theorem norm_chr_sub_div_le_pstar (hξ : ‖ξ‖ < 1)
    (p u v : Z2 L) (hp : p ≠ 0) :
    ‖(chr L p u - chr L p v) / (1 - ξ * Shat L p)‖
      ≤ (45 * Real.pi ^ 2 / 2) * (pstar2 L p)⁻¹ := by
  have hp0 : 0 < pstar2 L p := pstar2_pos_of_ne_zero L hp
  have hc : 0 < 4 / (45 * Real.pi ^ 2) := by positivity
  have hden : 4 / (45 * Real.pi ^ 2) * pstar2 L p
      ≤ ‖1 - ξ * Shat L p‖ := by
    have h := norm_one_sub_mul_Shat_ge_pstar L hξ p
    nlinarith [sq_nonneg (kappa ξ)]
  have hdenpos : 0 < ‖1 - ξ * Shat L p‖ :=
    lt_of_lt_of_le (mul_pos hc hp0) hden
  have hinv : ‖1 - ξ * Shat L p‖⁻¹
      ≤ (45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹ := by
    calc
      ‖1 - ξ * Shat L p‖⁻¹
          ≤ (4 / (45 * Real.pi ^ 2) * pstar2 L p)⁻¹ :=
            (inv_le_inv₀ hdenpos (mul_pos hc hp0)).2 hden
      _ = (45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹ := by
            have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
            have hpne : pstar2 L p ≠ 0 := ne_of_gt hp0
            field_simp
  rw [norm_div]
  have hnum := norm_chr_sub_le L p u v
  have hright : 0 ≤ ‖1 - ξ * Shat L p‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  calc
    ‖chr L p u - chr L p v‖ / ‖1 - ξ * Shat L p‖
        = ‖chr L p u - chr L p v‖ * ‖1 - ξ * Shat L p‖⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ 2 * ‖1 - ξ * Shat L p‖⁻¹ :=
      mul_le_mul_of_nonneg_right hnum hright
    _ ≤ 2 * ((45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

/-- First difference after T14's zero-mode cancellation, in terms of T3's
normalized punctured sum. This estimate holds for every displacement. -/
theorem norm_Theta_sub_le_normalized (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u v : Z2 L) :
    ‖Theta L ξ u 0 - Theta L ξ v 0‖
      ≤ (45 * Real.pi ^ 2 / 2) * normalizedPuncturedSum L := by
  classical
  have hsum :
      ‖∑ p ∈ Finset.univ.erase (0 : Z2 L),
          (chr L p u - chr L p v) / (1 - ξ * Shat L p)‖
        ≤ (45 * Real.pi ^ 2 / 2) *
            ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹ := by
    calc
      _ ≤ ∑ p ∈ Finset.univ.erase (0 : Z2 L),
            ‖(chr L p u - chr L p v) / (1 - ξ * Shat L p)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.univ.erase (0 : Z2 L),
            (45 * Real.pi ^ 2 / 2) * (pstar2 L p)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact norm_chr_sub_div_le_pstar L hξ p u v (Finset.mem_erase.mp hp).1
      _ = _ := by rw [Finset.mul_sum]
  have hfactor : 0 ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
  rw [Theta_apply_sub_eq_erase_sum L hL hξ u v, norm_mul]
  have hcast : ‖((L : ℂ) ^ 2)⁻¹‖ = ((L : ℝ) ^ 2)⁻¹ := by simp [norm_inv, norm_pow]
  rw [hcast]
  calc
    ((L : ℝ) ^ 2)⁻¹ *
        ‖∑ p ∈ Finset.univ.erase (0 : Z2 L),
          (chr L p u - chr L p v) / (1 - ξ * Shat L p)‖
      ≤ ((L : ℝ) ^ 2)⁻¹ *
          ((45 * Real.pi ^ 2 / 2) *
            ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hfactor
    _ = (45 * Real.pi ^ 2 / 2) * normalizedPuncturedSum L := by
      rw [normalizedPuncturedSum_eq L hL]
      ring

/-- The logarithmic Fourier estimate for the first difference, with an
explicit universal constant. -/
theorem norm_Theta_sub_le_log (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u v : Z2 L) :
    ‖Theta L ξ u 0 - Theta L ξ v 0‖ ≤ 90 * (1 + Real.log L) := by
  have hsum := normalized_sum_inv_pstar2_le_log L hL
  have hmul := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ 45 * Real.pi ^ 2 / 2)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    ‖Theta L ξ u 0 - Theta L ξ v 0‖
        ≤ (45 * Real.pi ^ 2 / 2) * normalizedPuncturedSum L :=
          norm_Theta_sub_le_normalized L hL hξ u v
    _ ≤ (45 * Real.pi ^ 2 / 2) *
          ((4 / Real.pi ^ 2) * (1 + Real.log L)) := by
            rw [normalizedPuncturedSum_eq L hL]
            exact hmul
    _ = 90 * (1 + Real.log L) := by field_simp; ring

/-- The second finite difference is the sum of two first differences. -/
theorem norm_Theta_second_sub_le_log (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u s : Z2 L) :
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ 180 * (1 + Real.log L) := by
  have hident :
      2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0
        = (Theta L ξ u 0 - Theta L ξ (u - s) 0) +
            (Theta L ξ u 0 - Theta L ξ (u + s) 0) := by ring
  rw [hident]
  calc
    ‖(Theta L ξ u 0 - Theta L ξ (u - s) 0) +
        (Theta L ξ u 0 - Theta L ξ (u + s) 0)‖
        ≤ ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖ +
            ‖Theta L ξ u 0 - Theta L ξ (u + s) 0‖ := norm_add_le _ _
    _ ≤ 90 * (1 + Real.log L) + 90 * (1 + Real.log L) :=
      add_le_add (norm_Theta_sub_le_log L hL hξ u (u - s))
        (norm_Theta_sub_le_log L hL hξ u (u + s))
    _ = 180 * (1 + Real.log L) := by ring

omit [NeZero L] in
/-- The first paper-scale ratio is bounded below in Case 2. The strict
`d < 2|s|_L` hypothesis also forces `s ≠ 0`. -/
theorem case2_half_le_distance_ratio (u s : Z2 L)
    (hs : zdist2 L u < 2 * zdist2 L s) :
    (1 / 2 : ℝ) ≤ (zdist2 L s : ℝ) / ((zdist2 L u : ℝ) + 1) := by
  have hnat : zdist2 L u + 1 ≤ 2 * zdist2 L s := by omega
  have hreal : (zdist2 L u : ℝ) + 1 ≤ 2 * (zdist2 L s : ℝ) := by
    exact_mod_cast hnat
  have hpos : 0 < (zdist2 L u : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hpos).2
  nlinarith

omit [NeZero L] in
/-- The squared paper-scale ratio is bounded below in Case 2. -/
theorem case2_quarter_le_distance_sq_ratio (u s : Z2 L)
    (hs : zdist2 L u < 2 * zdist2 L s) :
    (1 / 4 : ℝ) ≤ (zdist2 L s : ℝ) ^ 2 /
      ((zdist2 L u : ℝ) ^ 2 + 1) := by
  have hnat : zdist2 L u + 1 ≤ 2 * zdist2 L s := by omega
  have hreal : (zdist2 L u : ℝ) + 1 ≤ 2 * (zdist2 L s : ℝ) := by
    exact_mod_cast hnat
  have hupos : 0 ≤ (zdist2 L u : ℝ) := Nat.cast_nonneg _
  have hspos : 0 ≤ (zdist2 L s : ℝ) := Nat.cast_nonneg _
  have hsq : ((zdist2 L u : ℝ) + 1) ^ 2 ≤
      (2 * (zdist2 L s : ℝ)) ^ 2 := by nlinarith
  have hpos : 0 < (zdist2 L u : ℝ) ^ 2 + 1 := by positivity
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- `(prop:BD1)`, Case 2, with the logarithm as the deterministic-domination
prefactor. The positive second term in the paper may be added downstream. -/
theorem norm_Theta_fd1_case2_le (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u s : Z2 L)
    (hs : zdist2 L u < 2 * zdist2 L s) :
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
      ≤ 180 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) / ((zdist2 L u : ℝ) + 1)) := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  have hratio := case2_half_le_distance_ratio L u s hs
  calc
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
        ≤ 90 * (1 + Real.log L) := norm_Theta_sub_le_log L hL hξ u (u - s)
    _ ≤ 180 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) / ((zdist2 L u : ℝ) + 1)) := by
      nlinarith

/-- `(prop:BD2)`, Case 2, with an explicit logarithmic prefactor. -/
theorem norm_Theta_fd2_case2_le (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u s : Z2 L)
    (hs : zdist2 L u < 2 * zdist2 L s) :
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ 720 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) ^ 2 /
            ((zdist2 L u : ℝ) ^ 2 + 1)) := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  have hratio := case2_quarter_le_distance_sq_ratio L u s hs
  calc
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
        ≤ 180 * (1 + Real.log L) :=
          norm_Theta_second_sub_le_log L hL hξ u s
    _ ≤ 720 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) ^ 2 /
            ((zdist2 L u : ℝ) ^ 2 + 1)) := by
      nlinarith

/-- Both Case 2 inequalities in the exact two-term scale of `(prop:BD1)` and
`(prop:BD2)`, with a common explicit logarithmic prefactor. -/
theorem norm_Theta_fd_case2_le_paper (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (u s : Z2 L)
    (hs : zdist2 L u < 2 * zdist2 L s) :
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
        ≤ 720 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) * ((zdist2 L u : ℝ) + 1)⁻¹ +
            (zdist2 L s : ℝ) * (kappa ξ * (ellhat L ξ) ^ 2)⁻¹)
      ∧
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
        ≤ 720 * (1 + Real.log L) *
          ((zdist2 L s : ℝ) ^ 2 * ((zdist2 L u : ℝ) ^ 2 + 1)⁻¹ +
            (zdist2 L s : ℝ) ^ 2 * ((ellhat L ξ) ^ 2)⁻¹) := by
  have hlog : 0 ≤ 1 + Real.log L := one_add_log_nonneg L
  have hfirstExtra : 0 ≤ (zdist2 L s : ℝ) *
      (kappa ξ * (ellhat L ξ) ^ 2)⁻¹ := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (mul_nonneg (kappa_pos hξ).le (sq_nonneg _)))
  have hsecondExtra : 0 ≤ (zdist2 L s : ℝ) ^ 2 *
      ((ellhat L ξ) ^ 2)⁻¹ := by positivity
  constructor
  · have h := norm_Theta_fd1_case2_le L hL hξ u s hs
    have hr : 0 ≤ (zdist2 L s : ℝ) /
        ((zdist2 L u : ℝ) + 1) := by positivity
    rw [div_eq_mul_inv] at h
    rw [div_eq_mul_inv] at hr
    nlinarith [mul_nonneg hlog hr, mul_nonneg hlog hfirstExtra]
  · have h := norm_Theta_fd2_case2_le L hL hξ u s hs
    rw [div_eq_mul_inv] at h
    nlinarith [mul_nonneg hlog hsecondExtra]

/-- The common Case 2 prefactor is subpolynomial in the block side length. -/
theorem case2_log_prefactor_detDom_one :
    (fun L : ℕ => 720 * (1 + Real.log L)) ≺ (fun _ => (1 : ℝ)) :=
  DetDom.const_mul_left (by norm_num) (fun _ => by norm_num)
    one_add_log_detDom_one

/-- Nonvacuous example of the strict Case 2 geometry on `Z_3²`. -/
example : zdist2 3 (0 : Z2 3) < 2 * zdist2 3 ((1, 0) : Z2 3) := by decide

/-- The full analytic assumptions can simultaneously hold at that example. -/
example : ‖(0 : ℂ)‖ < 1 ∧
    zdist2 3 (0 : Z2 3) < 2 * zdist2 3 ((1, 0) : Z2 3) := by
  constructor
  · norm_num
  · decide

end RBM
