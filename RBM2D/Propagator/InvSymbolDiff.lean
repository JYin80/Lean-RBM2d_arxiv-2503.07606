/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Algebra.Group.ForwardDiff
import RBM2D.Propagator.SymbolShiftAnnulus
import RBM2D.Propagator.SymbolReciprocalDiff
import RBM2D.Propagator.GeomSum

/-!
# Forward differences of the reciprocal symbol up to order three

The shell decomposition of Section 8.3 needs the forward differences `Δ^k m` of the multiplier
`m = (1 - ξ Ŝ)⁻¹` up to `k = 3`, on the region `|p|_* ≥ r` with explicit constants.
-/

namespace RBM

private theorem invSymbolDiff_norm_div_le {a b : ℂ} {N P : ℝ} (hP : 0 < P)
    (ha : ‖a‖ ≤ N) (hb : P ≤ ‖b‖) : ‖a / b‖ ≤ N / P := by
  rw [norm_div]
  exact div_le_div₀ (le_trans (norm_nonneg _) ha) ha hP hb

private theorem invSymbolDiff_pn2 {b c : ℂ} {P Q : ℝ} (hQ : 0 ≤ Q)
    (hb : P ≤ ‖b‖) (hc : Q ≤ ‖c‖) : P * Q ≤ ‖b * c‖ := by
  rw [norm_mul]
  exact mul_le_mul hb hc hQ (norm_nonneg _)

private theorem invSymbolDiff_pn3 {b c d : ℂ} {P Q R : ℝ} (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hb : P ≤ ‖b‖) (hc : Q ≤ ‖c‖) (hd : R ≤ ‖d‖) :
    P * Q * R ≤ ‖b * c * d‖ := by
  rw [norm_mul]
  exact mul_le_mul (invSymbolDiff_pn2 hQ hb hc) hd hR (norm_nonneg _)

private theorem invSymbolDiff_pn4 {b c d e : ℂ} {P Q R S : ℝ} (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hb : P ≤ ‖b‖) (hc : Q ≤ ‖c‖) (hd : R ≤ ‖d‖)
    (he : S ≤ ‖e‖) : P * Q * R * S ≤ ‖b * c * d * e‖ := by
  rw [norm_mul]
  exact mul_le_mul (invSymbolDiff_pn3 hQ hR hb hc hd) he hS (norm_nonneg _)

private theorem invSymbolDiff_ne_zero {D : ℂ} {P : ℝ} (hP : 0 < P) (h : P ≤ ‖D‖) : D ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- Order zero. -/
private theorem invSymbolDiff_core0 {D0 : ℂ} {ρ2 : ℝ} (hρ2 : 0 < ρ2) {r h : ℝ}
    (n0 : ρ2 / 112 ≤ ‖D0‖) :
    ‖D0⁻¹‖ ≤ 112 * (h / r) ^ 0 / ρ2 := by
  have hP : 0 < ρ2 / 112 := by positivity
  calc ‖D0⁻¹‖ = ‖(1 : ℂ) / D0‖ := by rw [one_div]
    _ ≤ 1 / (ρ2 / 112) := invSymbolDiff_norm_div_le hP (by simp) n0
    _ = 112 * (h / r) ^ 0 / ρ2 := by
      field_simp

/-- Order one. -/
private theorem invSymbolDiff_core1 {D0 D1 : ℂ} {ρ2 Y r h : ℝ} (hρ2 : 0 < ρ2)
    (hr : 0 < r) (hrY : r ≤ Y) (hh : 0 ≤ h)
    (n0 : ρ2 / 112 ≤ ‖D0‖) (n1 : Y ^ 2 / 112 ≤ ‖D1‖)
    (d1 : ‖D1 - D0‖ ≤ 27 / 50 * h * Y) :
    ‖D1⁻¹ - D0⁻¹‖ ≤ 10 ^ 4 * (h / r) ^ 1 / ρ2 := by
  have hY : 0 < Y := hr.trans_le hrY
  have hP0 : 0 < ρ2 / 112 := by positivity
  have hP1 : 0 < Y ^ 2 / 112 := by positivity
  have h0 := invSymbolDiff_ne_zero hP0 n0
  have h1 := invSymbolDiff_ne_zero hP1 n1
  have hid : D1⁻¹ - D0⁻¹ = -(D1 - D0) / (D0 * D1) := by field_simp; ring
  rw [hid]
  have hden := invSymbolDiff_pn2 hP1.le n0 n1
  have hb := invSymbolDiff_norm_div_le (a := -(D1 - D0)) (N := 27 / 50 * h * Y)
    (mul_pos hP0 hP1) (by rwa [norm_neg]) hden
  refine hb.trans ?_
  have hu : h / Y ≤ h / r := div_le_div_of_nonneg_left hh hr hrY
  have hteq : (27 / 50 * h * Y) / (ρ2 / 112 * (Y ^ 2 / 112)) =
      (27 / 50 * 112 ^ 2) * (h / Y) / ρ2 := by
    field_simp
  rw [hteq, pow_one, div_le_div_iff_of_pos_right hρ2]
  nlinarith [hu, div_nonneg hh hr.le]

/-- Order two. -/
private theorem invSymbolDiff_core2 {D0 D1 D2 : ℂ} {ρ2 Y r h : ℝ} (hρ2 : 0 < ρ2)
    (hr : 0 < r) (hrY : r ≤ Y) (hh : 0 ≤ h)
    (n0 : ρ2 / 112 ≤ ‖D0‖) (n1 : Y ^ 2 / 112 ≤ ‖D1‖) (n1' : ρ2 / 112 ≤ ‖D1‖)
    (n2 : Y ^ 2 / 112 ≤ ‖D2‖)
    (d1 : ‖D1 - D0‖ ≤ 27 / 50 * h * Y) (d2 : ‖D2 - D1‖ ≤ 27 / 50 * h * Y)
    (s2 : ‖D2 - 2 * D1 + D0‖ ≤ 2 / 5 * h ^ 2) :
    ‖D2⁻¹ - 2 * D1⁻¹ + D0⁻¹‖ ≤ 10 ^ 6 * (h / r) ^ 2 / ρ2 := by
  have hY : 0 < Y := hr.trans_le hrY
  have hP0 : 0 < ρ2 / 112 := by positivity
  have hP1 : 0 < Y ^ 2 / 112 := by positivity
  have h0 := invSymbolDiff_ne_zero hP0 n0
  have h1 := invSymbolDiff_ne_zero hP1 n1
  have h2 := invSymbolDiff_ne_zero hP1 n2
  have hid : D2⁻¹ - 2 * D1⁻¹ + D0⁻¹ =
      -(D2 - 2 * D1 + D0) / (D1 * D2) +
        (D1 - D0) * ((D1 - D0) + (D2 - D1)) / (D0 * D1 * D2) := by
    field_simp
    ring
  rw [hid]
  have e1 : ‖-(D2 - 2 * D1 + D0) / (D1 * D2)‖ ≤
      (2 / 5 * h ^ 2) / (ρ2 / 112 * (Y ^ 2 / 112)) :=
    invSymbolDiff_norm_div_le (mul_pos hP0 hP1) (by rwa [norm_neg])
      (invSymbolDiff_pn2 hP1.le n1' n2)
  have hnum : ‖(D1 - D0) * ((D1 - D0) + (D2 - D1))‖ ≤
      27 / 50 * h * Y * (2 * (27 / 50 * h * Y)) := by
    rw [norm_mul]
    refine mul_le_mul d1 ?_ (norm_nonneg _) (by positivity)
    calc ‖(D1 - D0) + (D2 - D1)‖ ≤ ‖D1 - D0‖ + ‖D2 - D1‖ := norm_add_le _ _
      _ ≤ 2 * (27 / 50 * h * Y) := by linarith
  have e2 : ‖(D1 - D0) * ((D1 - D0) + (D2 - D1)) / (D0 * D1 * D2)‖ ≤
      (27 / 50 * h * Y * (2 * (27 / 50 * h * Y))) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112)) :=
    invSymbolDiff_norm_div_le (by positivity) hnum
      (invSymbolDiff_pn3 hP1.le hP1.le n0 n1 n2)
  have hu : h / Y ≤ h / r := div_le_div_of_nonneg_left hh hr hrY
  have hu0 : 0 ≤ h / Y := div_nonneg hh hY.le
  have hu2 : (h / Y) ^ 2 ≤ (h / r) ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have E1 : (2 / 5 * h ^ 2) / (ρ2 / 112 * (Y ^ 2 / 112)) =
      (2 / 5 * 112 ^ 2) * (h / Y) ^ 2 / ρ2 := by
    field_simp
  have E2 : (27 / 50 * h * Y * (2 * (27 / 50 * h * Y))) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112)) =
      (27 / 50 * (2 * (27 / 50)) * 112 ^ 3) * (h / Y) ^ 2 / ρ2 := by
    field_simp
  refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
  rw [E1, E2, ← add_div, div_le_div_iff_of_pos_right hρ2]
  nlinarith [hu2, sq_nonneg (h / r)]

/-- Order three. -/
private theorem invSymbolDiff_core3 {D0 D1 D2 D3 : ℂ} {ρ2 Y r h : ℝ} (hρ2 : 0 < ρ2)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrY : r ≤ Y) (hh : 0 ≤ h)
    (n0 : ρ2 / 112 ≤ ‖D0‖) (n1 : Y ^ 2 / 112 ≤ ‖D1‖) (n1' : ρ2 / 112 ≤ ‖D1‖)
    (n2 : Y ^ 2 / 112 ≤ ‖D2‖) (n2' : ρ2 / 112 ≤ ‖D2‖) (n3 : Y ^ 2 / 112 ≤ ‖D3‖)
    (d1 : ‖D1 - D0‖ ≤ 27 / 50 * h * Y) (d2 : ‖D2 - D1‖ ≤ 27 / 50 * h * Y)
    (d3 : ‖D3 - D2‖ ≤ 27 / 50 * h * Y)
    (s2a : ‖D2 - 2 * D1 + D0‖ ≤ 2 / 5 * h ^ 2)
    (s2b : ‖D3 - 2 * D2 + D1‖ ≤ 2 / 5 * h ^ 2)
    (s3 : ‖D3 - 3 * D2 + 3 * D1 - D0‖ ≤ 2 / 5 * h ^ 3) :
    ‖D3⁻¹ - 3 * D2⁻¹ + 3 * D1⁻¹ - D0⁻¹‖ ≤ 2 * 10 ^ 8 * (h / r) ^ 3 / ρ2 := by
  have hY : 0 < Y := hr.trans_le hrY
  have hP0 : 0 < ρ2 / 112 := by positivity
  have hP1 : 0 < Y ^ 2 / 112 := by positivity
  have hPr : 0 < r ^ 2 / 112 := by positivity
  have hrY2 : r ^ 2 / 112 ≤ Y ^ 2 / 112 := by
    have := pow_le_pow_left₀ hr.le hrY 2
    linarith
  have n3r : r ^ 2 / 112 ≤ ‖D3‖ := hrY2.trans n3
  have h0 := invSymbolDiff_ne_zero hP0 n0
  have h1 := invSymbolDiff_ne_zero hP1 n1
  have h2 := invSymbolDiff_ne_zero hP1 n2
  have h3 := invSymbolDiff_ne_zero hP1 n3
  have hid : D3⁻¹ - 3 * D2⁻¹ + 3 * D1⁻¹ - D0⁻¹ =
      -(D3 - 3 * D2 + 3 * D1 - D0) / (D2 * D3) +
        (((D1 - D0) + 3 * (D2 - D1) + (D3 - D2)) * (D2 - 2 * D1 + D0) +
          (D2 - D1) * (D3 - 2 * D2 + D1)) / (D1 * D2 * D3) -
        (D1 - D0) * ((D1 - D0) + (D2 - D1)) *
          ((D1 - D0) + (D2 - D1) + (D3 - D2)) / (D0 * D1 * D2 * D3) := by
    field_simp
    ring
  rw [hid]
  -- first term
  have e1 : ‖-(D3 - 3 * D2 + 3 * D1 - D0) / (D2 * D3)‖ ≤
      (2 / 5 * h ^ 3) / (ρ2 / 112 * (r ^ 2 / 112)) :=
    invSymbolDiff_norm_div_le (mul_pos hP0 hPr) (by rwa [norm_neg])
      (invSymbolDiff_pn2 hPr.le n2' n3r)
  -- second term
  have hsum : ‖(D1 - D0) + 3 * (D2 - D1) + (D3 - D2)‖ ≤ 5 * (27 / 50 * h * Y) := by
    have h3' : ‖(3 : ℂ) * (D2 - D1)‖ = 3 * ‖D2 - D1‖ := by
      rw [norm_mul]; norm_num
    calc ‖(D1 - D0) + 3 * (D2 - D1) + (D3 - D2)‖
        ≤ ‖(D1 - D0) + 3 * (D2 - D1)‖ + ‖D3 - D2‖ := norm_add_le _ _
      _ ≤ ‖D1 - D0‖ + ‖(3 : ℂ) * (D2 - D1)‖ + ‖D3 - D2‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 5 * (27 / 50 * h * Y) := by rw [h3']; linarith
  have hnum2 : ‖((D1 - D0) + 3 * (D2 - D1) + (D3 - D2)) * (D2 - 2 * D1 + D0) +
      (D2 - D1) * (D3 - 2 * D2 + D1)‖ ≤
      5 * (27 / 50 * h * Y) * (2 / 5 * h ^ 2) + 27 / 50 * h * Y * (2 / 5 * h ^ 2) := by
    calc _ ≤ ‖((D1 - D0) + 3 * (D2 - D1) + (D3 - D2)) * (D2 - 2 * D1 + D0)‖ +
          ‖(D2 - D1) * (D3 - 2 * D2 + D1)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, norm_mul]
        gcongr
  have e2 : ‖(((D1 - D0) + 3 * (D2 - D1) + (D3 - D2)) * (D2 - 2 * D1 + D0) +
          (D2 - D1) * (D3 - 2 * D2 + D1)) / (D1 * D2 * D3)‖ ≤
      (5 * (27 / 50 * h * Y) * (2 / 5 * h ^ 2) + 27 / 50 * h * Y * (2 / 5 * h ^ 2)) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112)) :=
    invSymbolDiff_norm_div_le (by positivity) hnum2
      (invSymbolDiff_pn3 hP1.le hP1.le n1' n2 n3)
  -- third term
  have hab : ‖(D1 - D0) + (D2 - D1)‖ ≤ 2 * (27 / 50 * h * Y) := by
    calc ‖(D1 - D0) + (D2 - D1)‖ ≤ ‖D1 - D0‖ + ‖D2 - D1‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have habc : ‖(D1 - D0) + (D2 - D1) + (D3 - D2)‖ ≤ 3 * (27 / 50 * h * Y) := by
    calc ‖(D1 - D0) + (D2 - D1) + (D3 - D2)‖ ≤
          ‖(D1 - D0) + (D2 - D1)‖ + ‖D3 - D2‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hnum3 : ‖(D1 - D0) * ((D1 - D0) + (D2 - D1)) *
      ((D1 - D0) + (D2 - D1) + (D3 - D2))‖ ≤
      27 / 50 * h * Y * (2 * (27 / 50 * h * Y)) * (3 * (27 / 50 * h * Y)) := by
    rw [norm_mul, norm_mul]
    gcongr
  have e3 : ‖(D1 - D0) * ((D1 - D0) + (D2 - D1)) *
        ((D1 - D0) + (D2 - D1) + (D3 - D2)) / (D0 * D1 * D2 * D3)‖ ≤
      (27 / 50 * h * Y * (2 * (27 / 50 * h * Y)) * (3 * (27 / 50 * h * Y))) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112) * (Y ^ 2 / 112)) :=
    invSymbolDiff_norm_div_le (by positivity) hnum3
      (invSymbolDiff_pn4 hP1.le hP1.le hP1.le n0 n1 n2 n3)
  -- real arithmetic
  have hu : h / Y ≤ h / r := div_le_div_of_nonneg_left hh hr hrY
  have hu0 : 0 ≤ h / Y := div_nonneg hh hY.le
  have ht0 : 0 ≤ h / r := div_nonneg hh hr.le
  have hu3 : (h / Y) ^ 3 ≤ (h / r) ^ 3 := pow_le_pow_left₀ hu0 hu 3
  have hrt : (h / r) ^ 3 * r ≤ (h / r) ^ 3 :=
    mul_le_of_le_one_right (pow_nonneg ht0 3) hr1
  have E1 : (2 / 5 * h ^ 3) / (ρ2 / 112 * (r ^ 2 / 112)) =
      (2 / 5 * 112 ^ 2) * ((h / r) ^ 3 * r) / ρ2 := by
    field_simp
  have E2 : (5 * (27 / 50 * h * Y) * (2 / 5 * h ^ 2) + 27 / 50 * h * Y * (2 / 5 * h ^ 2)) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112)) =
      ((5 * (27 / 50) * (2 / 5) + 27 / 50 * (2 / 5)) * 112 ^ 3) * (h / Y) ^ 3 / ρ2 := by
    field_simp
  have E3 : (27 / 50 * h * Y * (2 * (27 / 50 * h * Y)) * (3 * (27 / 50 * h * Y))) /
        (ρ2 / 112 * (Y ^ 2 / 112) * (Y ^ 2 / 112) * (Y ^ 2 / 112)) =
      (27 / 50 * (2 * (27 / 50)) * (3 * (27 / 50)) * 112 ^ 4) * (h / Y) ^ 3 / ρ2 := by
    field_simp
  refine (norm_sub_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add e1 e2)) e3).trans ?_)
  rw [E1, E2, E3, ← add_div, ← add_div, div_le_div_iff_of_pos_right hρ2]
  nlinarith [hu3, hrt, pow_nonneg ht0 3]

/-! ## Stencil data -/

private theorem invSymbolDiff_pstar_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    pstar L (u + v) ≤ pstar L u + pstar L v := by
  have hz := zdist_add_le L u v
  have hz' : (zdist L (u + v) : ℝ) ≤ (zdist L u : ℝ) + (zdist L v : ℝ) := by
    exact_mod_cast hz
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (u + v) = symbolGridStep L * (zdist L (u + v) : ℝ) := by
      unfold pstar symbolGridStep
      ring
    _ ≤ symbolGridStep L * (zdist L u : ℝ) + symbolGridStep L * (zdist L v : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hz' hc]
    _ = pstar L u + pstar L v := by
      unfold pstar symbolGridStep
      ring

private theorem invSymbolDiff_pstar_one_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    pstar L (1 : ZMod L) ≤ symbolGridStep L := by
  have hz : (zdist L (1 : ZMod L) : ℝ) ≤ 1 := by
    exact_mod_cast zdist_one_le L hL
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (1 : ZMod L) = symbolGridStep L * (zdist L (1 : ZMod L) : ℝ) := by
      unfold pstar symbolGridStep
      ring
    _ ≤ symbolGridStep L := by nlinarith [mul_le_mul_of_nonneg_left hz hc]

private theorem invSymbolDiff_pstar_step_up (L : ℕ) [NeZero L] (hL : 3 ≤ L) (u : ZMod L) :
    pstar L (u + 1) ≤ pstar L u + symbolGridStep L :=
  (invSymbolDiff_pstar_add_le L u 1).trans
    (by linarith [invSymbolDiff_pstar_one_le L hL])

/-- Along a stencil in one coordinate, `|u + l|_*` changes by at most `3 h` between any two
of the first four points. -/
private theorem invSymbolDiff_pstar_step (L : ℕ) [NeZero L] (hL : 3 ≤ L) (u : ZMod L)
    {k : ℕ} (hk : k ≤ 3) :
    ∀ l l' : ℕ, l ≤ k → l' ≤ k →
      pstar L (u + (l : ZMod L)) ≤ pstar L (u + (l' : ZMod L)) + 3 * symbolGridStep L := by
  have hh : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  set c : ℕ → ℝ := fun l => pstar L (u + (l : ZMod L)) with hc
  have h1 : ∀ l : ℕ, c (l + 1) ≤ c l + symbolGridStep L := by
    intro l
    have : u + ((l + 1 : ℕ) : ZMod L) = (u + (l : ZMod L)) + 1 := by
      push_cast
      ring
    simp only [hc]
    rw [this]
    exact invSymbolDiff_pstar_step_up L hL _
  have h2 : ∀ l : ℕ, c l ≤ c (l + 1) + symbolGridStep L := by
    intro l
    have : u + ((l + 1 : ℕ) : ZMod L) = (u + (l : ZMod L)) + 1 := by
      push_cast
      ring
    simp only [hc]
    rw [this]
    exact pstar_le_shift_one L hL _
  have hup : ∀ n l : ℕ, c (l + n) ≤ c l + n * symbolGridStep L := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
      intro l
      have := h1 (l + n)
      have := ih l
      push_cast
      rw [← add_assoc]
      nlinarith
  have hdown : ∀ n l : ℕ, c l ≤ c (l + n) + n * symbolGridStep L := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
      intro l
      have := h2 (l + n)
      have := ih l
      push_cast
      rw [← add_assoc]
      nlinarith
  intro l l' hl hl'
  change c l ≤ c l' + 3 * symbolGridStep L
  rcases le_total l l' with hle | hle
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hn : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    have := hdown n l
    nlinarith
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hn : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    have := hup n l'
    nlinarith

/-- The data of a stencil `p, p + e, …, p + k e` in one coordinate, in the form used by the
reciprocal-difference cores: `S l = Ŝ(p + l e)`, `c l` the moving coordinate of `|p + l e|_*`,
`d` the fixed one. -/
private structure InvSymbolDiffStencil (κ2 r h : ℝ) (ξ : ℂ) (k : ℕ) (S : ℕ → ℂ)
    (c : ℕ → ℝ) (d : ℝ) : Prop where
  c_nonneg : ∀ l, 0 ≤ c l
  d_nonneg : 0 ≤ d
  step : ∀ l l' : ℕ, l ≤ k → l' ≤ k → c l ≤ c l' + 3 * h
  outside : ∀ l : ℕ, l ≤ k → r ^ 2 ≤ c l ^ 2 + d ^ 2
  low : ∀ l : ℕ, l ≤ k → 1 / 112 * (κ2 + (c l ^ 2 + d ^ 2)) ≤ ‖1 - ξ * S l‖
  diff1 : ∀ l : ℕ, l + 1 ≤ k → ‖S (l + 1) - S l‖ ≤ 1 / 5 * h * (2 * c l + h)
  diff2 : ∀ l : ℕ, l + 2 ≤ k → ‖S (l + 2) - 2 * S (l + 1) + S l‖ ≤ 2 / 5 * h ^ 2
  diff3 : ∀ l : ℕ, l + 3 ≤ k →
    ‖S (l + 3) - 3 * S (l + 2) + 3 * S (l + 1) - S l‖ ≤ 2 / 5 * h ^ 3

private theorem invSymbolDiff_one_div_112_le : (1 : ℝ) / 112 ≤ 4 / (45 * Real.pi ^ 2) := by
  have hpi := Real.pi_pos
  have hlt := Real.pi_lt_d2
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

private theorem invSymbolDiff_stencil_mk (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (e : Z2 L) (mv fx : Z2 L → ZMod L)
    (hmv : ∀ q, mv (q + e) = mv q + 1) (hfx : ∀ q, fx (q + e) = fx q)
    (hp2 : ∀ q, pstar2 L q = pstar L (mv q) ^ 2 + pstar L (fx q) ^ 2)
    (hd1 : ∀ q, ‖Shat L (q + e) - Shat L q‖ ≤
      1 / 5 * symbolGridStep L * (2 * pstar L (mv q) + symbolGridStep L))
    (hd2 : ∀ q, ‖Shat L (q + e + e) - 2 * Shat L (q + e) + Shat L q‖ ≤
      2 / 5 * symbolGridStep L ^ 2)
    (hd3 : ∀ q, ‖Shat L (q + e + e + e) - 3 * Shat L (q + e + e) + 3 * Shat L (q + e) -
      Shat L q‖ ≤ 2 / 5 * symbolGridStep L ^ 3)
    (p : Z2 L) (k : ℕ) (hk : k ≤ 3) (r : ℝ)
    (hst : ∀ l : ℕ, l ≤ k → r ^ 2 ≤ pstar2 L (p + l • e)) :
    InvSymbolDiffStencil (kappa ξ ^ 2) r (symbolGridStep L) ξ k
      (fun l => Shat L (p + l • e)) (fun l => pstar L (mv p + (l : ZMod L)))
      (pstar L (fx p)) := by
  have hsh : ∀ l : ℕ, p + (l + 1) • e = p + l • e + e := by
    intro l
    rw [succ_nsmul, add_assoc]
  have hmvl : ∀ l : ℕ, mv (p + l • e) = mv p + (l : ZMod L) := by
    intro l
    induction l with
    | zero => simp
    | succ n ih =>
      rw [hsh, hmv, ih]
      push_cast
      ring
  have hfxl : ∀ l : ℕ, fx (p + l • e) = fx p := by
    intro l
    induction l with
    | zero => simp
    | succ n ih => rw [hsh, hfx, ih]
  have hp2l : ∀ l : ℕ, pstar2 L (p + l • e) = pstar L (mv p + (l : ZMod L)) ^ 2 +
      pstar L (fx p) ^ 2 := by
    intro l
    rw [hp2, hmvl, hfxl]
  refine ⟨fun l => pstar_nonneg L _, pstar_nonneg L _,
    invSymbolDiff_pstar_step L hL (mv p) hk, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    have := hst l hl
    rwa [hp2l] at this
  · intro l hl
    have h1 := norm_one_sub_mul_Shat_ge_pstar L hξ (p + l • e)
    rw [hp2l] at h1
    have hnn : 0 ≤ kappa ξ ^ 2 + (pstar L (mv p + (l : ZMod L)) ^ 2 + pstar L (fx p) ^ 2) := by
      positivity
    exact (mul_le_mul_of_nonneg_right invSymbolDiff_one_div_112_le hnn).trans h1
  · intro l hl
    have := hd1 (p + l • e)
    rw [hmvl, ← hsh] at this
    exact this
  · intro l hl
    have := hd2 (p + l • e)
    rw [← hsh, ← hsh] at this
    exact this
  · intro l hl
    have := hd3 (p + l • e)
    rw [← hsh, ← hsh, ← hsh] at this
    exact this

private theorem invSymbolDiff_exists_Y {c : ℕ → ℝ} {d r h : ℝ} {k : ℕ}
    (hc : ∀ l, 0 ≤ c l)
    (hstep : ∀ l l' : ℕ, l ≤ k → l' ≤ k → c l ≤ c l' + 3 * h)
    (hout : ∀ l : ℕ, l ≤ k → r ^ 2 ≤ c l ^ 2 + d ^ 2) :
    ∃ Y : ℝ, r ≤ Y ∧ (∀ l : ℕ, l ≤ k → Y ^ 2 ≤ c l ^ 2 + d ^ 2) ∧
      (∀ l : ℕ, l ≤ k → c l ≤ Y + 3 * h) := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range (k + 1)) c ⟨0, by simp⟩
  have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
  have hmin' : ∀ l : ℕ, l ≤ k → c i ≤ c l := fun l hl =>
    hmin l (by simpa [Nat.lt_succ_iff] using hl)
  have hY2 : Real.sqrt (c i ^ 2 + d ^ 2) ^ 2 = c i ^ 2 + d ^ 2 :=
    Real.sq_sqrt (by positivity)
  refine ⟨Real.sqrt (c i ^ 2 + d ^ 2), Real.le_sqrt_of_sq_le (hout i hik), ?_, ?_⟩
  · intro l hl
    rw [hY2]
    have := pow_le_pow_left₀ (hc i) (hmin' l hl) 2
    linarith
  · intro l hl
    have h1 := hstep l i hl hik
    have h2 : c i ≤ Real.sqrt (c i ^ 2 + d ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg d])
    linarith

private theorem invSymbolDiff_facts {κ2 r h : ℝ} {ξ : ℂ} {k : ℕ} {S : ℕ → ℂ}
    {c : ℕ → ℝ} {d : ℝ} (hξ : ‖ξ‖ < 1) (hκ : 0 ≤ κ2) (hr : 0 < r)
    (hh : 10 * h ≤ r) (h0 : 0 ≤ h) (H : InvSymbolDiffStencil κ2 r h ξ k S c d) :
    ∃ Y : ℝ, r ≤ Y ∧
      (∀ l : ℕ, l ≤ k → (κ2 + r ^ 2) / 112 ≤ ‖1 - ξ * S l‖) ∧
      (∀ l : ℕ, l ≤ k → Y ^ 2 / 112 ≤ ‖1 - ξ * S l‖) ∧
      (∀ l : ℕ, l + 1 ≤ k →
        ‖(1 - ξ * S (l + 1)) - (1 - ξ * S l)‖ ≤ 27 / 50 * h * Y) ∧
      (∀ l : ℕ, l + 2 ≤ k →
        ‖(1 - ξ * S (l + 2)) - 2 * (1 - ξ * S (l + 1)) + (1 - ξ * S l)‖ ≤ 2 / 5 * h ^ 2) ∧
      (∀ l : ℕ, l + 3 ≤ k →
        ‖(1 - ξ * S (l + 3)) - 3 * (1 - ξ * S (l + 2)) + 3 * (1 - ξ * S (l + 1)) -
          (1 - ξ * S l)‖ ≤ 2 / 5 * h ^ 3) := by
  obtain ⟨Y, hrY, hY2, hcY⟩ :=
    invSymbolDiff_exists_Y H.c_nonneg H.step H.outside
  have hξ1 : ‖ξ‖ ≤ 1 := hξ.le
  have hY : 0 < Y := hr.trans_le hrY
  refine ⟨Y, hrY, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    have h1 := H.low l hl
    have h2 := hY2 l hl
    have h3 : r ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hr.le hrY 2
    linarith
  · intro l hl
    have h1 := H.low l hl
    have h2 := hY2 l hl
    linarith
  · intro l hl
    have e : (1 - ξ * S (l + 1)) - (1 - ξ * S l) = -(ξ * (S (l + 1) - S l)) := by ring
    rw [e, norm_neg, norm_mul]
    have h1 := H.diff1 l hl
    have h2 := hcY l (by omega)
    have h3 : ‖ξ‖ * ‖S (l + 1) - S l‖ ≤ ‖S (l + 1) - S l‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hξ1
    have h4 : 1 / 5 * h * (2 * c l + h) ≤ 27 / 50 * h * Y := by
      nlinarith [mul_nonneg h0 (sub_nonneg.2 (hh.trans hrY))]
    linarith
  · intro l hl
    have e : (1 - ξ * S (l + 2)) - 2 * (1 - ξ * S (l + 1)) + (1 - ξ * S l) =
        -(ξ * (S (l + 2) - 2 * S (l + 1) + S l)) := by ring
    rw [e, norm_neg, norm_mul]
    have h1 := H.diff2 l hl
    have h3 : ‖ξ‖ * ‖S (l + 2) - 2 * S (l + 1) + S l‖ ≤
        ‖S (l + 2) - 2 * S (l + 1) + S l‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hξ1
    linarith
  · intro l hl
    have e : (1 - ξ * S (l + 3)) - 3 * (1 - ξ * S (l + 2)) + 3 * (1 - ξ * S (l + 1)) -
        (1 - ξ * S l) =
        -(ξ * (S (l + 3) - 3 * S (l + 2) + 3 * S (l + 1) - S l)) := by ring
    rw [e, norm_neg, norm_mul]
    have h1 := H.diff3 l hl
    have h3 : ‖ξ‖ * ‖S (l + 3) - 3 * S (l + 2) + 3 * S (l + 1) - S l‖ ≤
        ‖S (l + 3) - 3 * S (l + 2) + 3 * S (l + 1) - S l‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hξ1
    linarith

private theorem invSymbolDiff_stencil0 {κ2 r h : ℝ} {ξ : ℂ} {S : ℕ → ℂ} {c : ℕ → ℝ}
    {d : ℝ} (hξ : ‖ξ‖ < 1) (hκ : 0 < κ2) (hr : 0 < r) (hh : 10 * h ≤ r) (h0 : 0 ≤ h)
    (H : InvSymbolDiffStencil κ2 r h ξ 0 S c d) :
    ‖(1 - ξ * S 0)⁻¹‖ ≤ 112 * (h / r) ^ 0 / (κ2 + r ^ 2) := by
  obtain ⟨Y, hrY, hρ, hYn, -, -, -⟩ := invSymbolDiff_facts hξ hκ.le hr hh h0 H
  exact invSymbolDiff_core0 (by positivity) (hρ 0 le_rfl)

private theorem invSymbolDiff_stencil1 {κ2 r h : ℝ} {ξ : ℂ} {S : ℕ → ℂ} {c : ℕ → ℝ}
    {d : ℝ} (hξ : ‖ξ‖ < 1) (hκ : 0 < κ2) (hr : 0 < r) (hh : 10 * h ≤ r) (h0 : 0 ≤ h)
    (H : InvSymbolDiffStencil κ2 r h ξ 1 S c d) :
    ‖(1 - ξ * S 1)⁻¹ - (1 - ξ * S 0)⁻¹‖ ≤ 10 ^ 4 * (h / r) ^ 1 / (κ2 + r ^ 2) := by
  obtain ⟨Y, hrY, hρ, hYn, hd1, -, -⟩ := invSymbolDiff_facts hξ hκ.le hr hh h0 H
  exact invSymbolDiff_core1 (by positivity) hr hrY h0 (hρ 0 (by omega))
    (hYn 1 le_rfl) (hd1 0 le_rfl)

private theorem invSymbolDiff_stencil2 {κ2 r h : ℝ} {ξ : ℂ} {S : ℕ → ℂ} {c : ℕ → ℝ}
    {d : ℝ} (hξ : ‖ξ‖ < 1) (hκ : 0 < κ2) (hr : 0 < r) (hh : 10 * h ≤ r) (h0 : 0 ≤ h)
    (H : InvSymbolDiffStencil κ2 r h ξ 2 S c d) :
    ‖(1 - ξ * S 2)⁻¹ - 2 * (1 - ξ * S 1)⁻¹ + (1 - ξ * S 0)⁻¹‖ ≤
      10 ^ 6 * (h / r) ^ 2 / (κ2 + r ^ 2) := by
  obtain ⟨Y, hrY, hρ, hYn, hd1, hd2, -⟩ := invSymbolDiff_facts hξ hκ.le hr hh h0 H
  exact invSymbolDiff_core2 (by positivity) hr hrY h0 (hρ 0 (by omega))
    (hYn 1 (by omega)) (hρ 1 (by omega)) (hYn 2 le_rfl) (hd1 0 (by omega))
    (hd1 1 (by omega)) (hd2 0 le_rfl)

private theorem invSymbolDiff_stencil3 {κ2 r h : ℝ} {ξ : ℂ} {S : ℕ → ℂ} {c : ℕ → ℝ}
    {d : ℝ} (hξ : ‖ξ‖ < 1) (hκ : 0 < κ2) (hr : 0 < r) (hr1 : r ≤ 1)
    (hh : 10 * h ≤ r) (h0 : 0 ≤ h)
    (H : InvSymbolDiffStencil κ2 r h ξ 3 S c d) :
    ‖(1 - ξ * S 3)⁻¹ - 3 * (1 - ξ * S 2)⁻¹ + 3 * (1 - ξ * S 1)⁻¹ - (1 - ξ * S 0)⁻¹‖ ≤
      2 * 10 ^ 8 * (h / r) ^ 3 / (κ2 + r ^ 2) := by
  obtain ⟨Y, hrY, hρ, hYn, hd1, hd2, hd3⟩ := invSymbolDiff_facts hξ hκ.le hr hh h0 H
  exact invSymbolDiff_core3 (by positivity) hr hr1 hrY h0 (hρ 0 (by omega))
    (hYn 1 (by omega)) (hρ 1 (by omega)) (hYn 2 (by omega)) (hρ 2 (by omega))
    (hYn 3 le_rfl) (hd1 0 (by omega)) (hd1 1 (by omega)) (hd1 2 (by omega))
    (hd2 0 (by omega)) (hd2 1 (by omega)) (hd3 0 le_rfl)

private theorem invSymbolDiff_iter2 {L : ℕ} [NeZero L] (f : Z2 L → ℂ) (e p : Z2 L) :
    (fwdDiff e)^[2] f p = f (p + e + e) - 2 * f (p + e) + f p := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id, fwdDiff]
  ring

private theorem invSymbolDiff_iter3 {L : ℕ} [NeZero L] (f : Z2 L → ℂ) (e p : Z2 L) :
    (fwdDiff e)^[3] f p =
      f (p + e + e + e) - 3 * f (p + e + e) + 3 * f (p + e) - f p := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id, fwdDiff]
  ring

/-- Forward differences of the reciprocal symbol `(1 - ξŜ)⁻¹` up to order three, on a stencil
in one coordinate direction whose points all satisfy `r ≤ |·|_*`, with `10 h ≤ r`
(`h = 2π/L`, `r = 2⁻ʲ`).  This is a discrete quantitative form of the forward-difference
estimate, not a statement of the paper. -/
theorem invSymbolMultiplier_fwdDiff_le :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 →
    ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) →
    ∀ (j : ℕ) (p : Z2 L) (k : Fin 4),
      10 * symbolGridStep L ≤ dyad j →
      (∀ l : ℕ, l ≤ (k : ℕ) → dyad j ^ 2 ≤ pstar2 L (p + l • e)) →
      ‖(fwdDiff e)^[k] (invSymbolMultiplier L ξ) p‖
        ≤ (![112, 10 ^ 4, 10 ^ 6, 2 * 10 ^ 8] k : ℝ) *
            (symbolGridStep L / dyad j) ^ (k : ℕ) / (kappa ξ ^ 2 + dyad j ^ 2) := by
  intro L _ hL ξ hξ e he j p k hh hst
  have hκ : 0 < kappa ξ ^ 2 := by
    have := kappa_pos hξ
    positivity
  have hr : 0 < dyad j := dyad_pos j
  have hr1 : dyad j ≤ 1 := dyad_le_one j
  have h0 : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hk3 : (k : ℕ) ≤ 3 := by omega
  obtain ⟨c, d, H⟩ : ∃ (c : ℕ → ℝ) (d : ℝ), InvSymbolDiffStencil (kappa ξ ^ 2) (dyad j)
      (symbolGridStep L) ξ (k : ℕ) (fun l => Shat L (p + l • e)) c d := by
    rcases he with rfl | rfl
    · exact ⟨_, _, invSymbolDiff_stencil_mk L hL hξ (1, 0) Prod.fst Prod.snd
        (by intro q; simp) (by intro q; simp) (fun q => rfl)
        (fun q => norm_Shat_shift_e1_le L hL q)
        (fun q => norm_Shat_second_diff_e1_le L hL q)
        (fun q => norm_Shat_third_diff_e1_le L hL q) p (k : ℕ) hk3 (dyad j) hst⟩
    · exact ⟨_, _, invSymbolDiff_stencil_mk L hL hξ (0, 1) Prod.snd Prod.fst
        (by intro q; simp) (by intro q; simp) (fun q => by simp only [pstar2]; ring)
        (fun q => norm_Shat_shift_e2_le L hL q)
        (fun q => norm_Shat_second_diff_e2_le L hL q)
        (fun q => norm_Shat_third_diff_e2_le L hL q) p (k : ℕ) hk3 (dyad j) hst⟩
  have hS0 : p + (0 : ℕ) • e = p := by simp
  have hS1 : p + (1 : ℕ) • e = p + e := by simp
  have hS2 : p + (2 : ℕ) • e = p + e + e := by
    rw [two_nsmul, add_assoc]
  have hS3 : p + (3 : ℕ) • e = p + e + e + e := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, add_assoc, add_assoc, add_assoc]
  fin_cases k
  · have key := invSymbolDiff_stencil0 hξ hκ hr hh h0 H
    simp only [hS0] at key
    change ‖(fwdDiff e)^[0] (invSymbolMultiplier L ξ) p‖ ≤
      (112 : ℝ) * (symbolGridStep L / dyad j) ^ 0 / (kappa ξ ^ 2 + dyad j ^ 2)
    exact key
  · have key := invSymbolDiff_stencil1 hξ hκ hr hh h0 H
    simp only [hS0, hS1] at key
    change ‖(fwdDiff e)^[1] (invSymbolMultiplier L ξ) p‖ ≤
      (10 ^ 4 : ℝ) * (symbolGridStep L / dyad j) ^ 1 / (kappa ξ ^ 2 + dyad j ^ 2)
    exact key
  · have key := invSymbolDiff_stencil2 hξ hκ hr hh h0 H
    simp only [hS0, hS1, hS2] at key
    change ‖(fwdDiff e)^[2] (invSymbolMultiplier L ξ) p‖ ≤
      (10 ^ 6 : ℝ) * (symbolGridStep L / dyad j) ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)
    rw [invSymbolDiff_iter2]
    exact key
  · have key := invSymbolDiff_stencil3 hξ hκ hr hr1 hh h0 H
    simp only [hS0, hS1, hS2, hS3] at key
    change ‖(fwdDiff e)^[3] (invSymbolMultiplier L ξ) p‖ ≤
      (2 * 10 ^ 8 : ℝ) * (symbolGridStep L / dyad j) ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
    rw [invSymbolDiff_iter3]
    exact key

end RBM
