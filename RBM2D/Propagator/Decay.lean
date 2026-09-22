/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ZeroMode
import RBM2D.Propagator.LatticeSum

/-!
# Small-scale decay of the two-dimensional propagator

The `κ L < 1` part of Section 8.2, Property 5 (`prop:ThfadC`).
-/

namespace RBM

variable (L : ℕ) [NeZero L]

/-- The first inequality in the small-`κL` paragraph of §8.2: after separating
the zero mode, the remaining terms are bounded by inverse momentum squares. -/
theorem norm_Theta_apply_le_zero_mode_add_pstar (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
      ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
        ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹ := by
  classical
  let s : Finset (Z2 L) := Finset.univ.erase 0
  have hterm (p : Z2 L) (hp : p ∈ s) :
      ‖chr L p (a - b) / (1 - ξ * Shat L p)‖
        ≤ (45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹ := by
    have hp0 : 0 < pstar2 L p :=
      pstar2_pos_of_ne_zero L (Finset.mem_erase.mp hp).1
    have hc : 0 < 4 / (45 * Real.pi ^ 2) := by positivity
    have hden : 4 / (45 * Real.pi ^ 2) * pstar2 L p
        ≤ ‖1 - ξ * Shat L p‖ := by
      have h := norm_one_sub_mul_Shat_ge_pstar L hξ p
      nlinarith [sq_nonneg (kappa ξ)]
    have hdenpos : 0 < ‖1 - ξ * Shat L p‖ :=
      lt_of_lt_of_le (mul_pos hc hp0) hden
    rw [norm_chr_div_one_sub_mul_Shat]
    calc
      ‖1 - ξ * Shat L p‖⁻¹
          ≤ (4 / (45 * Real.pi ^ 2) * pstar2 L p)⁻¹ :=
            (inv_le_inv₀ hdenpos (mul_pos hc hp0)).2 hden
      _ = (45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹ := by
            have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
            have hpne : pstar2 L p ≠ 0 := ne_of_gt hp0
            field_simp
  have hsum :
      ‖∑ p ∈ s, chr L p (a - b) / (1 - ξ * Shat L p)‖
        ≤ (45 * Real.pi ^ 2 / 4) *
          ∑ p ∈ s, (pstar2 L p)⁻¹ := by
    calc
      _ ≤ ∑ p ∈ s, ‖chr L p (a - b) / (1 - ξ * Shat L p)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ s, (45 * Real.pi ^ 2 / 4) * (pstar2 L p)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p hp
      _ = _ := by rw [Finset.mul_sum]
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  rw [Theta_apply_eq_zero_mode_add L hL hξ a b]
  calc
    _ ≤ ‖((L : ℂ) ^ 2)⁻¹ * (1 - ξ)⁻¹‖ +
        ‖((L : ℂ) ^ 2)⁻¹ * ∑ p ∈ s, chr L p (a - b) / (1 - ξ * Shat L p)‖ :=
          norm_add_le _ _
    _ = ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
        ((L : ℝ) ^ 2)⁻¹ *
          ‖∑ p ∈ s, chr L p (a - b) / (1 - ξ * Shat L p)‖ := by
          simp [norm_inv, norm_pow]
    _ ≤ _ := by
          dsimp [s] at hsum
          have hnonneg : 0 ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
          have h := mul_le_mul_of_nonneg_left hsum hnonneg
          nlinarith

/-- The paper's explicit zero-mode bound followed by the two-dimensional
harmonic sum. The constant `45` comes from `eq_elliptic` and T3's shell count. -/
theorem norm_Theta_apply_le_inv_kappa_sq_add_harmonic (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ +
        45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by
  have hsum := sum_inv_pstar2_le L hL
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  have hfactor : 0 ≤ ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hpunctured :
      ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
          ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹
        ≤ 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by
    calc
      _ ≤ (((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4)) *
          ((4 / Real.pi ^ 2) * (L : ℝ) ^ 2 *
            ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) := hmul
      _ = _ := by field_simp
  calc
    ‖Theta L ξ a b‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
          ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
            ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹ :=
        norm_Theta_apply_le_zero_mode_add_pstar L hL hξ a b
    _ ≤ ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
          45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ :=
        by simpa [add_comm] using
          (add_le_add_left hpunctured (((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹))
    _ = _ := by rw [← kappa_sq ξ, mul_inv_rev]

/-- The second displayed inequality in the small-`κL` paragraph of §8.2,
using T3's normalized logarithmic estimate directly. -/
theorem norm_Theta_apply_le_inv_kappa_sq_add_log (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ + 45 * (1 + Real.log L) := by
  have hsum := normalized_sum_inv_pstar2_le_log L hL
  have hfactor : 0 ≤ 45 * Real.pi ^ 2 / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpunctured :
      ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
          ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹
        ≤ 45 * (1 + Real.log L) := by
    calc
      _ = (45 * Real.pi ^ 2 / 4) *
          ((∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) /
            (L : ℝ) ^ 2) := by ring
      _ ≤ (45 * Real.pi ^ 2 / 4) *
          ((4 / Real.pi ^ 2) * (1 + Real.log L)) := hmul
      _ = _ := by field_simp
  calc
    ‖Theta L ξ a b‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
          ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
            ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹ :=
        norm_Theta_apply_le_zero_mode_add_pstar L hL hξ a b
    _ ≤ ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
          45 * (1 + Real.log L) := by
        simpa [add_comm] using
          (add_le_add_left hpunctured (((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹))
    _ = _ := by rw [← kappa_sq ξ, mul_inv_rev]

/-- The same explicit entrywise bound with T3's normalized punctured sum as
the prefactor. This is the form whose prefactor is directly `≺ 1`. -/
theorem norm_Theta_apply_le_inv_kappa_sq_add_normalized (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ +
        (45 * Real.pi ^ 2 / 4) * normalizedPuncturedSum L := by
  calc
    ‖Theta L ξ a b‖ ≤
        ((L : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - ξ‖⁻¹ +
          ((L : ℝ) ^ 2)⁻¹ * (45 * Real.pi ^ 2 / 4) *
            ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹ :=
      norm_Theta_apply_le_zero_mode_add_pstar L hL hξ a b
    _ = _ := by
      rw [normalizedPuncturedSum_eq L hL, ← kappa_sq ξ, mul_inv_rev]
      ring

omit [NeZero L] in
/-- In the small-`κL` regime the effective length is the torus side length. -/
theorem ellhat_eq_L_of_kappa_mul_L_lt_one (_hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (hsmall : kappa ξ * (L : ℝ) < 1) :
    ellhat L ξ = (L : ℝ) := by
  have hk : 0 < kappa ξ := kappa_pos hξ
  have hLI : (L : ℝ) ≤ (kappa ξ)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hk).2 (by nlinarith)
  exact min_eq_right hLI

/-- The periodic `L¹` distance never exceeds the side length, as in §8.2. -/
theorem zdist2_le_L (u : Z2 L) : zdist2 L u ≤ L := by
  have h1 := two_mul_zdist_le L u.1
  have h2 := two_mul_zdist_le L u.2
  simp only [zdist2]
  omega

/-- Property 5 in the `κL < 1` regime, with the exponential factor restored.
This is the small-regime theorem that T24 can combine with its large-regime
contour input; no contour assumption is used here. -/
theorem norm_Theta_apply_le_small_kappa_harmonic (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (hsmall : kappa ξ * (L : ℝ) < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      Real.exp 1 *
        (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
        ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) := by
  have hk : 0 < kappa ξ := kappa_pos hξ
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  have hscalePos : 0 < (kappa ξ) ^ 2 * (L : ℝ) ^ 2 := by positivity
  have hscaleLt : (kappa ξ) ^ 2 * (L : ℝ) ^ 2 < 1 := by
    have hxpos : 0 < kappa ξ * (L : ℝ) := mul_pos hk hLpos
    have haux : 0 < (kappa ξ * (L : ℝ)) * (1 - kappa ξ * (L : ℝ)) :=
      mul_pos hxpos (by linarith)
    nlinarith
  have hinv : 1 ≤ ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ :=
    (one_le_inv₀ hscalePos).2 hscaleLt.le
  have hHnonneg : 0 ≤ 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (sum_inv_Icc_nonneg L)
  have hbase : ‖Theta L ξ a b‖ ≤
      (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
        ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ := by
    have h := norm_Theta_apply_le_inv_kappa_sq_add_harmonic L hL hξ a b
    have hm := mul_nonneg hHnonneg (sub_nonneg.mpr hinv)
    nlinarith
  have hell : ellhat L ξ = (L : ℝ) :=
    ellhat_eq_L_of_kappa_mul_L_lt_one L hL hξ hsmall
  have hdist : (zdist2 L (a - b) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast zdist2_le_L L (a - b)
  have hratio : (zdist2 L (a - b) : ℝ) / (L : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith
  have hexp : 1 ≤ Real.exp 1 *
      Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) := by
    rw [hell]
    calc
      (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (1 + -(zdist2 L (a - b) : ℝ) / (L : ℝ)) :=
        Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
      _ = Real.exp 1 * Real.exp (-(zdist2 L (a - b) : ℝ) / (L : ℝ)) :=
        Real.exp_add _ _
  rw [hell] at hexp
  rw [hell]
  have hfactor : 0 ≤
      (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
        ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ := by positivity
  calc
    ‖Theta L ξ a b‖ ≤
        (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
          ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ := hbase
    _ = (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
          ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ * 1 := by ring
    _ ≤ (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
          ((kappa ξ) ^ 2 * (L : ℝ) ^ 2)⁻¹ *
          (Real.exp 1 * Real.exp (-(zdist2 L (a - b) : ℝ) / (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hfactor
    _ = _ := by ring

/-- The logarithmic explicit form expected by T24. The prefactor is allowed
to grow only logarithmically, hence is `≺ 1` by `one_add_log_detDom_one`. -/
theorem norm_Theta_apply_le_small_kappa_log (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (hsmall : kappa ξ * (L : ℝ) < 1) (a b : Z2 L) :
    ‖Theta L ξ a b‖ ≤
      46 * Real.exp 1 * (1 + Real.log L) *
        ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) := by
  have hH := sum_inv_Icc_le_one_add_log L
  have hlog : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  have hpref :
      1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹
        ≤ 46 * (1 + Real.log L) := by nlinarith
  have hfactor : 0 ≤ Real.exp 1 *
      ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) := by positivity
  calc
    ‖Theta L ξ a b‖ ≤ Real.exp 1 *
        (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
        ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ) :=
      norm_Theta_apply_le_small_kappa_harmonic L hL hξ hsmall a b
    _ = (1 + 45 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
          (Real.exp 1 * ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
            Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ)) := by ring
    _ ≤ 46 * (1 + Real.log L) *
          (Real.exp 1 * ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ *
            Real.exp (-(zdist2 L (a - b) : ℝ) / ellhat L ξ)) :=
      mul_le_mul_of_nonneg_right hpref hfactor
    _ = _ := by ring

/-- T3's `≺ 1` punctured-sum theorem makes the exact small-regime prefactor
subpolynomial, as required when T24 packages Property 5. -/
theorem small_kappa_prefactor_detDom_one :
    (fun L : ℕ => 1 + (45 * Real.pi ^ 2 / 4) * normalizedPuncturedSum L) ≺
      (fun _ => (1 : ℝ)) := by
  have hone : (fun _ : ℕ => (1 : ℝ)) ≺ (fun _ => (1 : ℝ)) :=
    DetDom.refl (fun _ => by norm_num)
  have hsum : (fun L : ℕ => (45 * Real.pi ^ 2 / 4) * normalizedPuncturedSum L) ≺
      (fun _ => (1 : ℝ)) :=
    DetDom.const_mul_left (by positivity) (fun _ => by norm_num)
      normalizedPuncturedSum_detDom_one
  have h := DetDom.add_left (fun _ => by norm_num) hone hsum
  change (fun L : ℕ => 1 + (45 * Real.pi ^ 2 / 4) * normalizedPuncturedSum L) ≺
    (fun _ => (1 : ℝ)) at h
  exact h

/-- A nondegenerate small-regime instance: `L = 3`, `ξ = 35/36`, `κL = 1/2`. -/
example : ‖(35 / 36 : ℂ)‖ < 1 ∧
    kappa (35 / 36 : ℂ) * (3 : ℝ) < 1 := by
  constructor
  · norm_num
  · have hn : ‖(1 : ℂ) - (35 / 36 : ℂ)‖ = (1 / 36 : ℝ) := by norm_num
    rw [kappa, hn]
    have hs : Real.sqrt (1 / 36 : ℝ) = 1 / 6 := by
      have hs36 : Real.sqrt (36 : ℝ) = 6 :=
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
      norm_num [hs36]
    rw [hs]
    norm_num

-- The complementary `κL ≥ 1` contour/periodization regime belongs to T27/T28.

end RBM
