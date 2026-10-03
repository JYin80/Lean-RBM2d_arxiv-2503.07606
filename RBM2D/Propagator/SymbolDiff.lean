/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.AbelSum

/-!
# One-step differences of the two-dimensional Fourier symbol

The cancellation between the positive and negative character contributions
gives one power of the momentum, in addition to the size of a grid step.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

private theorem char_one_mul_char_neg_one :
    (ZMod.stdAddChar (1 : ZMod L) : ℂ) * ZMod.stdAddChar (-1 : ZMod L) = 1 := by
  rw [← AddChar.map_add_eq_mul]
  simp

private theorem symbol_diff_algebra (a b c d : ℂ) (hcd : c * d = 1) :
    (a * c + b * d - a - b) / 5 =
      ((a - b) * (c - 1) - b * (c - 1) * (d - 1)) / 5 := by
  calc
    (a * c + b * d - a - b) / 5 =
        ((a - b) * (c - 1) - b * (c - 1) * (d - 1)) / 5 +
          b * (c * d - 1) / 5 := by ring
    _ = _ := by rw [hcd]; ring

private theorem Shat_shift_e1_exact (p : Z2 L) :
    Shat L (p + (1, 0)) - Shat L p =
      (((ZMod.stdAddChar p.1 : ℂ) - ZMod.stdAddChar (-p.1)) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) -
        (ZMod.stdAddChar (-p.1) : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1)) / 5 := by
  have hpos : (ZMod.stdAddChar (p.1 + 1) : ℂ) =
      ZMod.stdAddChar p.1 * ZMod.stdAddChar (1 : ZMod L) :=
    AddChar.map_add_eq_mul _ _ _
  have hneg : (ZMod.stdAddChar (-(p.1 + 1)) : ℂ) =
      ZMod.stdAddChar (-p.1) * ZMod.stdAddChar (-1 : ZMod L) := by
    rw [show -(p.1 + 1) = -p.1 + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul]
  simp only [Shat, Prod.fst_add, Prod.snd_add, add_zero]
  rw [hpos, hneg]
  convert symbol_diff_algebra _ _ _ _ (char_one_mul_char_neg_one L) using 1; ring_nf

private theorem Shat_shift_e2_exact (p : Z2 L) :
    Shat L (p + (0, 1)) - Shat L p =
      (((ZMod.stdAddChar p.2 : ℂ) - ZMod.stdAddChar (-p.2)) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) -
        (ZMod.stdAddChar (-p.2) : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1)) / 5 := by
  have hpos : (ZMod.stdAddChar (p.2 + 1) : ℂ) =
      ZMod.stdAddChar p.2 * ZMod.stdAddChar (1 : ZMod L) :=
    AddChar.map_add_eq_mul _ _ _
  have hneg : (ZMod.stdAddChar (-(p.2 + 1)) : ℂ) =
      ZMod.stdAddChar (-p.2) * ZMod.stdAddChar (-1 : ZMod L) := by
    rw [show -(p.2 + 1) = -p.2 + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul]
  simp only [Shat, Prod.fst_add, Prod.snd_add]
  rw [hpos, hneg]
  convert symbol_diff_algebra _ _ _ _ (char_one_mul_char_neg_one L) using 1; ring_nf

private theorem norm_char_neg_sub_one (q : ZMod L) :
    ‖(ZMod.stdAddChar (-q) : ℂ) - 1‖ =
      ‖(ZMod.stdAddChar q : ℂ) - 1‖ := by
  rw [AddChar.map_neg_eq_inv,
    Complex.inv_eq_conj (AddChar.norm_apply _ q)]
  have h : ((starRingEnd ℂ) ((ZMod.stdAddChar q : ℂ) - 1)) =
      (starRingEnd ℂ) (ZMod.stdAddChar q : ℂ) - 1 := by simp
  rw [← h, Complex.norm_conj]

private theorem norm_char_sub_char_neg_le (q : ZMod L) :
    ‖(ZMod.stdAddChar q : ℂ) - ZMod.stdAddChar (-q)‖ ≤
      2 * pstar L q := by
  calc
    ‖(ZMod.stdAddChar q : ℂ) - ZMod.stdAddChar (-q)‖ =
        ‖((ZMod.stdAddChar q : ℂ) - 1) -
          ((ZMod.stdAddChar (-q) : ℂ) - 1)‖ := by congr 1; ring
    _ ≤ ‖(ZMod.stdAddChar q : ℂ) - 1‖ +
          ‖(ZMod.stdAddChar (-q) : ℂ) - 1‖ := norm_sub_le _ _
    _ = 2 * ‖(ZMod.stdAddChar q : ℂ) - 1‖ := by
      rw [norm_char_neg_sub_one]; ring
    _ ≤ 2 * pstar L q := by
      gcongr
      exact norm_stdAddChar_sub_one_le_pstar L q

private theorem norm_char_one_sub_one_le_grid (hL : 3 ≤ L) :
    ‖(ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1‖ ≤
      2 * Real.pi / (L : ℝ) := by
  calc
    _ ≤ pstar L (1 : ZMod L) := norm_stdAddChar_sub_one_le_pstar L _
    _ = 2 * Real.pi * (zdist L (1 : ZMod L) : ℝ) / (L : ℝ) := rfl
    _ ≤ 2 * Real.pi / (L : ℝ) := by
      have hz : (zdist L (1 : ZMod L) : ℝ) ≤ 1 := by
        exact_mod_cast zdist_one_le L hL
      have hδ : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
      calc
        _ = (2 * Real.pi / (L : ℝ)) * (zdist L (1 : ZMod L) : ℝ) := by ring
        _ ≤ (2 * Real.pi / (L : ℝ)) * 1 := mul_le_mul_of_nonneg_left hz hδ
        _ = _ := by ring

private theorem norm_char_neg_one_sub_one_le_grid (hL : 3 ≤ L) :
    ‖(ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1‖ ≤
      2 * Real.pi / (L : ℝ) := by
  calc
    _ ≤ pstar L (-1 : ZMod L) := norm_stdAddChar_sub_one_le_pstar L _
    _ = 2 * Real.pi * (zdist L (-1 : ZMod L) : ℝ) / (L : ℝ) := rfl
    _ ≤ 2 * Real.pi / (L : ℝ) := by
      have hz : (zdist L (-1 : ZMod L) : ℝ) ≤ 1 := by
        exact_mod_cast zdist_neg_one_le L hL
      have hδ : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
      calc
        _ = (2 * Real.pi / (L : ℝ)) * (zdist L (-1 : ZMod L) : ℝ) := by ring
        _ ≤ (2 * Real.pi / (L : ℝ)) * 1 := mul_le_mul_of_nonneg_left hz hδ
        _ = _ := by ring

private theorem norm_symbol_diff_of_exact (hL : 3 ≤ L) (q : ZMod L)
    (v : ℂ)
    (hv : v =
      (((ZMod.stdAddChar q : ℂ) - ZMod.stdAddChar (-q)) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) -
        (ZMod.stdAddChar (-q) : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1)) / 5) :
    ‖v‖ ≤ (1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
      (2 * pstar L q + 2 * Real.pi / (L : ℝ)) := by
  let A : ℂ := (ZMod.stdAddChar q : ℂ) - ZMod.stdAddChar (-q)
  let B : ℂ := (ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1
  let C : ℂ := (ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1
  let D : ℂ := ZMod.stdAddChar (-q)
  let δ : ℝ := 2 * Real.pi / (L : ℝ)
  have hA : ‖A‖ ≤ 2 * pstar L q := norm_char_sub_char_neg_le L q
  have hB : ‖B‖ ≤ δ := norm_char_one_sub_one_le_grid L hL
  have hC : ‖C‖ ≤ δ := norm_char_neg_one_sub_one_le_grid L hL
  have hD : ‖D‖ = 1 := AddChar.norm_apply _ _
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hp : 0 ≤ pstar L q := pstar_nonneg L q
  have hAB : ‖A‖ * ‖B‖ ≤ (2 * pstar L q) * δ :=
    mul_le_mul hA hB (norm_nonneg _) (by positivity)
  have hBC : ‖B‖ * ‖C‖ ≤ δ * δ :=
    mul_le_mul hB hC (norm_nonneg _) hδ
  have hnum : ‖A * B - D * B * C‖ ≤
      (2 * pstar L q) * δ + δ * δ := by
    calc
      _ ≤ ‖A * B‖ + ‖D * B * C‖ := norm_sub_le _ _
      _ = ‖A‖ * ‖B‖ + ‖B‖ * ‖C‖ := by rw [norm_mul, norm_mul, norm_mul, hD, one_mul]
      _ ≤ _ := by linarith
  rw [hv]
  change ‖(A * B - D * B * C) / 5‖ ≤ _
  rw [norm_div]
  rw [show ‖(5 : ℂ)‖ = (5 : ℝ) by norm_num]
  change ‖A * B - D * B * C‖ / 5 ≤ (1 / 5 : ℝ) * δ * (2 * pstar L q + δ)
  nlinarith

/-- A one-step first-coordinate difference of the Fourier multiplier has
the sharp `|p|_*/L + L⁻²` scale. -/
theorem norm_Shat_shift_e1_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (1, 0)) - Shat L p‖ ≤
      (1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
        (2 * pstar L p.1 + 2 * Real.pi / (L : ℝ)) := by
  exact norm_symbol_diff_of_exact L hL p.1 _ (Shat_shift_e1_exact L p)

/-- The analogous one-step difference in the second momentum coordinate. -/
theorem norm_Shat_shift_e2_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (0, 1)) - Shat L p‖ ≤
      (1 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) *
        (2 * pstar L p.2 + 2 * Real.pi / (L : ℝ)) := by
  exact norm_symbol_diff_of_exact L hL p.2 _ (Shat_shift_e2_exact L p)

private theorem char_pair_second_diff (q : ZMod L) :
    (ZMod.stdAddChar (q + 1 + 1) : ℂ) +
        ZMod.stdAddChar (-(q + 1 + 1)) -
      2 * ((ZMod.stdAddChar (q + 1) : ℂ) + ZMod.stdAddChar (-(q + 1))) +
      ((ZMod.stdAddChar q : ℂ) + ZMod.stdAddChar (-q)) =
    (ZMod.stdAddChar q : ℂ) *
        ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 2 +
      (ZMod.stdAddChar (-q) : ℂ) *
        ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 2 := by
  have hp1 : (ZMod.stdAddChar (q + 1) : ℂ) =
      ZMod.stdAddChar q * ZMod.stdAddChar (1 : ZMod L) :=
    AddChar.map_add_eq_mul _ _ _
  have hm1 : (ZMod.stdAddChar (-(q + 1)) : ℂ) =
      ZMod.stdAddChar (-q) * ZMod.stdAddChar (-1 : ZMod L) := by
    rw [show -(q + 1) = -q + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul]
  have hp2 : (ZMod.stdAddChar (q + 1 + 1) : ℂ) =
      ZMod.stdAddChar q * ZMod.stdAddChar (1 : ZMod L) ^ 2 := by
    rw [AddChar.map_add_eq_mul, hp1]
    ring
  have hm2 : (ZMod.stdAddChar (-(q + 1 + 1)) : ℂ) =
      ZMod.stdAddChar (-q) * ZMod.stdAddChar (-1 : ZMod L) ^ 2 := by
    rw [show -(q + 1 + 1) = -(q + 1) + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul, hm1]
    ring
  rw [hp1, hm1, hp2, hm2]
  ring

private theorem Shat_second_diff_e1_exact (p : Z2 L) :
    Shat L (p + (1, 0) + (1, 0)) - 2 * Shat L (p + (1, 0)) + Shat L p =
      ((ZMod.stdAddChar p.1 : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 2 +
        (ZMod.stdAddChar (-p.1) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 2) / 5 := by
  have h := char_pair_second_diff L p.1
  simp only [Shat, Prod.fst_add, Prod.snd_add, add_zero] at ⊢
  convert congrArg (fun z : ℂ => z / 5) h using 1; ring_nf

private theorem Shat_second_diff_e2_exact (p : Z2 L) :
    Shat L (p + (0, 1) + (0, 1)) - 2 * Shat L (p + (0, 1)) + Shat L p =
      ((ZMod.stdAddChar p.2 : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 2 +
        (ZMod.stdAddChar (-p.2) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 2) / 5 := by
  have h := char_pair_second_diff L p.2
  simp only [Shat, Prod.fst_add, Prod.snd_add] at ⊢
  convert congrArg (fun z : ℂ => z / 5) h using 1; ring_nf

private theorem norm_second_diff_of_exact (hL : 3 ≤ L) (q : ZMod L) (v : ℂ)
    (hv : v =
      ((ZMod.stdAddChar q : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 2 +
        (ZMod.stdAddChar (-q) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 2) / 5) :
    ‖v‖ ≤ (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 2 := by
  let A : ℂ := (ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1
  let B : ℂ := (ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1
  let δ : ℝ := 2 * Real.pi / (L : ℝ)
  have hA : ‖A‖ ≤ δ := norm_char_one_sub_one_le_grid L hL
  have hB : ‖B‖ ≤ δ := norm_char_neg_one_sub_one_le_grid L hL
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hAsq : ‖A‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA _
  have hBsq : ‖B‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB _
  rw [hv]
  change ‖((ZMod.stdAddChar q : ℂ) * A ^ 2 +
    (ZMod.stdAddChar (-q) : ℂ) * B ^ 2) / 5‖ ≤ _
  rw [norm_div, show ‖(5 : ℂ)‖ = (5 : ℝ) by norm_num]
  have hnum : ‖(ZMod.stdAddChar q : ℂ) * A ^ 2 +
      (ZMod.stdAddChar (-q) : ℂ) * B ^ 2‖ ≤ 2 * δ ^ 2 := by
    calc
      _ ≤ ‖(ZMod.stdAddChar q : ℂ) * A ^ 2‖ +
          ‖(ZMod.stdAddChar (-q) : ℂ) * B ^ 2‖ := norm_add_le _ _
      _ = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
        simp only [norm_mul, norm_pow, AddChar.norm_apply, one_mul]
      _ ≤ 2 * δ ^ 2 := by linarith
  change ‖(ZMod.stdAddChar q : ℂ) * A ^ 2 +
    (ZMod.stdAddChar (-q) : ℂ) * B ^ 2‖ / 5 ≤ (2 / 5 : ℝ) * δ ^ 2
  linarith

/-- A second forward difference in the first momentum coordinate costs
two grid steps and is uniformly `O(L⁻²)`. -/
theorem norm_Shat_second_diff_e1_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (1, 0) + (1, 0)) -
      2 * Shat L (p + (1, 0)) + Shat L p‖ ≤
      (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 2 := by
  exact norm_second_diff_of_exact L hL p.1 _ (Shat_second_diff_e1_exact L p)

/-- The analogous second difference in the second momentum coordinate. -/
theorem norm_Shat_second_diff_e2_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (0, 1) + (0, 1)) -
      2 * Shat L (p + (0, 1)) + Shat L p‖ ≤
      (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 2 := by
  exact norm_second_diff_of_exact L hL p.2 _ (Shat_second_diff_e2_exact L p)

private theorem char_pair_third_diff (q : ZMod L) :
    ((ZMod.stdAddChar (q + 1 + 1 + 1) : ℂ) +
        ZMod.stdAddChar (-(q + 1 + 1 + 1))) -
      3 * ((ZMod.stdAddChar (q + 1 + 1) : ℂ) +
        ZMod.stdAddChar (-(q + 1 + 1))) +
      3 * ((ZMod.stdAddChar (q + 1) : ℂ) + ZMod.stdAddChar (-(q + 1))) -
      ((ZMod.stdAddChar q : ℂ) + ZMod.stdAddChar (-q)) =
    (ZMod.stdAddChar q : ℂ) *
        ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 3 +
      (ZMod.stdAddChar (-q) : ℂ) *
        ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 3 := by
  have hp1 : (ZMod.stdAddChar (q + 1) : ℂ) =
      ZMod.stdAddChar q * ZMod.stdAddChar (1 : ZMod L) :=
    AddChar.map_add_eq_mul _ _ _
  have hm1 : (ZMod.stdAddChar (-(q + 1)) : ℂ) =
      ZMod.stdAddChar (-q) * ZMod.stdAddChar (-1 : ZMod L) := by
    rw [show -(q + 1) = -q + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul]
  have hp2 : (ZMod.stdAddChar (q + 1 + 1) : ℂ) =
      ZMod.stdAddChar q * ZMod.stdAddChar (1 : ZMod L) ^ 2 := by
    rw [AddChar.map_add_eq_mul, hp1]
    ring
  have hm2 : (ZMod.stdAddChar (-(q + 1 + 1)) : ℂ) =
      ZMod.stdAddChar (-q) * ZMod.stdAddChar (-1 : ZMod L) ^ 2 := by
    rw [show -(q + 1 + 1) = -(q + 1) + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul, hm1]
    ring
  have hp3 : (ZMod.stdAddChar (q + 1 + 1 + 1) : ℂ) =
      ZMod.stdAddChar q * ZMod.stdAddChar (1 : ZMod L) ^ 3 := by
    rw [AddChar.map_add_eq_mul, hp2]
    ring
  have hm3 : (ZMod.stdAddChar (-(q + 1 + 1 + 1)) : ℂ) =
      ZMod.stdAddChar (-q) * ZMod.stdAddChar (-1 : ZMod L) ^ 3 := by
    rw [show -(q + 1 + 1 + 1) = -(q + 1 + 1) + (-1 : ZMod L) by ring,
      AddChar.map_add_eq_mul, hm2]
    ring
  rw [hp1, hm1, hp2, hm2, hp3, hm3]
  ring

private theorem Shat_third_diff_e1_exact (p : Z2 L) :
    Shat L (p + (1, 0) + (1, 0) + (1, 0)) -
      3 * Shat L (p + (1, 0) + (1, 0)) +
      3 * Shat L (p + (1, 0)) - Shat L p =
      ((ZMod.stdAddChar p.1 : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 3 +
        (ZMod.stdAddChar (-p.1) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 3) / 5 := by
  have h := char_pair_third_diff L p.1
  simp only [Shat, Prod.fst_add, Prod.snd_add, add_zero] at ⊢
  convert congrArg (fun z : ℂ => z / 5) h using 1; ring_nf

private theorem Shat_third_diff_e2_exact (p : Z2 L) :
    Shat L (p + (0, 1) + (0, 1) + (0, 1)) -
      3 * Shat L (p + (0, 1) + (0, 1)) +
      3 * Shat L (p + (0, 1)) - Shat L p =
      ((ZMod.stdAddChar p.2 : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 3 +
        (ZMod.stdAddChar (-p.2) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 3) / 5 := by
  have h := char_pair_third_diff L p.2
  simp only [Shat, Prod.fst_add, Prod.snd_add] at ⊢
  convert congrArg (fun z : ℂ => z / 5) h using 1; ring_nf

private theorem norm_third_diff_of_exact (hL : 3 ≤ L) (q : ZMod L) (v : ℂ)
    (hv : v =
      ((ZMod.stdAddChar q : ℂ) *
          ((ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1) ^ 3 +
        (ZMod.stdAddChar (-q) : ℂ) *
          ((ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1) ^ 3) / 5) :
    ‖v‖ ≤ (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 3 := by
  let A : ℂ := (ZMod.stdAddChar (1 : ZMod L) : ℂ) - 1
  let B : ℂ := (ZMod.stdAddChar (-1 : ZMod L) : ℂ) - 1
  let δ : ℝ := 2 * Real.pi / (L : ℝ)
  have hA : ‖A‖ ≤ δ := norm_char_one_sub_one_le_grid L hL
  have hB : ‖B‖ ≤ δ := norm_char_neg_one_sub_one_le_grid L hL
  have hAsq : ‖A‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hA _
  have hBsq : ‖B‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hB _
  rw [hv]
  change ‖((ZMod.stdAddChar q : ℂ) * A ^ 3 +
    (ZMod.stdAddChar (-q) : ℂ) * B ^ 3) / 5‖ ≤ _
  rw [norm_div, show ‖(5 : ℂ)‖ = (5 : ℝ) by norm_num]
  have hnum : ‖(ZMod.stdAddChar q : ℂ) * A ^ 3 +
      (ZMod.stdAddChar (-q) : ℂ) * B ^ 3‖ ≤ 2 * δ ^ 3 := by
    calc
      _ ≤ ‖(ZMod.stdAddChar q : ℂ) * A ^ 3‖ +
          ‖(ZMod.stdAddChar (-q) : ℂ) * B ^ 3‖ := norm_add_le _ _
      _ = ‖A‖ ^ 3 + ‖B‖ ^ 3 := by
        simp only [norm_mul, norm_pow, AddChar.norm_apply, one_mul]
      _ ≤ 2 * δ ^ 3 := by linarith
  change ‖(ZMod.stdAddChar q : ℂ) * A ^ 3 +
    (ZMod.stdAddChar (-q) : ℂ) * B ^ 3‖ / 5 ≤ (2 / 5 : ℝ) * δ ^ 3
  linarith

/-- A third forward difference in the first momentum coordinate is
uniformly `O(L⁻³)`. -/
theorem norm_Shat_third_diff_e1_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (1, 0) + (1, 0) + (1, 0)) -
      3 * Shat L (p + (1, 0) + (1, 0)) +
      3 * Shat L (p + (1, 0)) - Shat L p‖ ≤
      (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 3 := by
  exact norm_third_diff_of_exact L hL p.1 _ (Shat_third_diff_e1_exact L p)

/-- A third forward difference in the second momentum coordinate. -/
theorem norm_Shat_third_diff_e2_le (hL : 3 ≤ L) (p : Z2 L) :
    ‖Shat L (p + (0, 1) + (0, 1) + (0, 1)) -
      3 * Shat L (p + (0, 1) + (0, 1)) +
      3 * Shat L (p + (0, 1)) - Shat L p‖ ≤
      (2 / 5 : ℝ) * (2 * Real.pi / (L : ℝ)) ^ 3 := by
  exact norm_third_diff_of_exact L hL p.2 _ (Shat_third_diff_e2_exact L p)

end RBM
