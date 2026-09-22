/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolDenomAnnulus

/-!
# Stability of momentum annuli under coordinate steps

The shift comparison is stated with its necessary lower-radius hypothesis.
It can be applied to each denominator of a second coordinate difference.
-/

namespace RBM

/-- Angular size of one lattice-frequency step. -/
noncomputable def symbolGridStep (L : ℕ) [NeZero L] : ℝ :=
  2 * Real.pi / (L : ℝ)

private theorem pstar_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    pstar L (u + v) ≤ pstar L u + pstar L v := by
  have hz := zdist_add_le L u v
  have hz' : (zdist L (u + v) : ℝ) ≤
      (zdist L u : ℝ) + (zdist L v : ℝ) := by exact_mod_cast hz
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (u + v) = symbolGridStep L * (zdist L (u + v) : ℝ) := by
      unfold pstar symbolGridStep
      ring
    _ ≤ symbolGridStep L * (zdist L u : ℝ) +
        symbolGridStep L * (zdist L v : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hz' hc]
    _ = pstar L u + pstar L v := by
      unfold pstar symbolGridStep
      ring

private theorem pstar_neg_one_le_grid (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) :
    pstar L (-1 : ZMod L) ≤ symbolGridStep L := by
  have hz : (zdist L (-1 : ZMod L) : ℝ) ≤ 1 := by
    exact_mod_cast zdist_neg_one_le L hL
  have hc : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  calc
    pstar L (-1 : ZMod L) =
        symbolGridStep L * (zdist L (-1 : ZMod L) : ℝ) := by
          unfold pstar symbolGridStep
          ring
    _ ≤ symbolGridStep L := by
      nlinarith [mul_le_mul_of_nonneg_left hz hc]

/-- A single coordinate step changes its angular distance by at most one grid step. -/
theorem pstar_le_shift_one (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (u : ZMod L) :
    pstar L u ≤ pstar L (u + 1) + symbolGridStep L := by
  calc
    pstar L u = pstar L ((u + 1) + (-1)) := by
      congr 1
      abel
    _ ≤ pstar L (u + 1) + pstar L (-1) := pstar_add_le L _ _
    _ ≤ pstar L (u + 1) + symbolGridStep L := by
      gcongr
      exact pstar_neg_one_le_grid L hL

/-- Two coordinate steps change angular distance by at most two grid steps. -/
theorem pstar_le_shift_two (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (u : ZMod L) :
    pstar L u ≤ pstar L (u + 1 + 1) + 2 * symbolGridStep L := by
  calc
    pstar L u ≤ pstar L (u + 1) + symbolGridStep L :=
      pstar_le_shift_one L hL u
    _ ≤ (pstar L (u + 1 + 1) + symbolGridStep L) +
        symbolGridStep L := by
          gcongr
          exact pstar_le_shift_one L hL (u + 1)
    _ = _ := by ring

private theorem pstar2_le_two_mul_shift (L : ℕ) [NeZero L]
    (p q : Z2 L) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : pstar L p.1 ≤ pstar L q.1 + ε₁)
    (h₂ : pstar L p.2 ≤ pstar L q.2 + ε₂) :
    pstar2 L p ≤ 2 * pstar2 L q + 2 * (ε₁ ^ 2 + ε₂ ^ 2) := by
  have hq₁ : 0 ≤ pstar L q.1 := pstar_nonneg L q.1
  have hq₂ : 0 ≤ pstar L q.2 := pstar_nonneg L q.2
  have hp₁ : 0 ≤ pstar L p.1 := pstar_nonneg L p.1
  have hp₂ : 0 ≤ pstar L p.2 := pstar_nonneg L p.2
  have hs₁ : (pstar L p.1) ^ 2 ≤ (pstar L q.1 + ε₁) ^ 2 :=
    (sq_le_sq₀ hp₁ (by positivity)).2 h₁
  have hs₂ : (pstar L p.2) ^ 2 ≤ (pstar L q.2 + ε₂) ^ 2 :=
    (sq_le_sq₀ hp₂ (by positivity)).2 h₂
  simp only [pstar2]
  nlinarith [sq_nonneg (pstar L q.1 - ε₁),
    sq_nonneg (pstar L q.2 - ε₂)]

/-- If the original momentum is larger than four shift energies, a shift
preserves at least one quarter of its squared radius. -/
theorem pstar2_shift_ge_quarter (L : ℕ) [NeZero L]
    (p q : Z2 L) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : pstar L p.1 ≤ pstar L q.1 + ε₁)
    (h₂ : pstar L p.2 ≤ pstar L q.2 + ε₂)
    (hlarge : 4 * (ε₁ ^ 2 + ε₂ ^ 2) ≤ pstar2 L p) :
    pstar2 L p / 4 ≤ pstar2 L q := by
  have h := pstar2_le_two_mul_shift L p q hε₁ hε₂ h₁ h₂
  linarith

/-- Both first- and second-coordinate-one shifts retain a quarter of the
original squared momentum when its radius exceeds the two-step grid cost. -/
theorem pstar2_shift_e1_ge_quarter (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (p q r : Z2 L) (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p) :
    pstar2 L p / 4 ≤ pstar2 L q ∧
      pstar2 L p / 4 ≤ pstar2 L r := by
  have hδ : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hq₂ : q.2 = p.2 := by simp [hq]
  have hr₁ : r.1 = p.1 + 1 + 1 := by rw [hr, hq]; rfl
  have hr₂ : r.2 = p.2 := by simp [hr, hq]
  constructor
  · apply pstar2_shift_ge_quarter L p q (ε₁ := 2 * symbolGridStep L)
      (ε₂ := 0) (by positivity) (by norm_num)
    · rw [hq₁]
      have h := pstar_le_shift_one L hL p.1
      linarith
    · rw [hq₂]
      simp
    · nlinarith
  · apply pstar2_shift_ge_quarter L p r (ε₁ := 2 * symbolGridStep L)
      (ε₂ := 0) (by positivity) (by norm_num)
    · rw [hr₁]
      exact pstar_le_shift_two L hL p.1
    · rw [hr₂]
      simp
    · nlinarith

/-- The same two-step radius comparison in coordinate two. -/
theorem pstar2_shift_e2_ge_quarter (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (p q r : Z2 L) (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p) :
    pstar2 L p / 4 ≤ pstar2 L q ∧
      pstar2 L p / 4 ≤ pstar2 L r := by
  have hδ : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hq₁ : q.1 = p.1 := by simp [hq]
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hr₁ : r.1 = p.1 := by simp [hr, hq]
  have hr₂ : r.2 = p.2 + 1 + 1 := by rw [hr, hq]; rfl
  constructor
  · apply pstar2_shift_ge_quarter L p q (ε₁ := 0)
      (ε₂ := 2 * symbolGridStep L) (by norm_num) (by positivity)
    · rw [hq₁]
      simp
    · rw [hq₂]
      have h := pstar_le_shift_one L hL p.2
      linarith
    · nlinarith
  · apply pstar2_shift_ge_quarter L p r (ε₁ := 0)
      (ε₂ := 2 * symbolGridStep L) (by norm_num) (by positivity)
    · rw [hr₁]
      simp
    · rw [hr₂]
      exact pstar_le_shift_two L hL p.2
    · nlinarith

/-- Any shifted momentum retaining a quarter of the squared radius obeys
the same dyadic denominator bound under a fourfold inner-radius margin. -/
theorem norm_one_sub_mul_Shat_ge_shifted_dyadic (L : ℕ) [NeZero L]
    {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p q : Z2 L) (j : ℕ)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p)
    (hshift : pstar2 L p / 4 ≤ pstar2 L q) :
    4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L q‖ := by
  apply norm_one_sub_mul_Shat_ge_dyadic L hξ q j
  linarith

/-- The two shifted denominators in the first-coordinate second difference. -/
theorem norm_one_sub_mul_Shat_ge_e1_shifts (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ) (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p) :
    (4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L q‖) ∧
    (4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L r‖) := by
  obtain ⟨hshiftq, hshiftr⟩ :=
    pstar2_shift_e1_ge_quarter L hL p q r hq hr hlarge
  exact ⟨norm_one_sub_mul_Shat_ge_shifted_dyadic L hξ p q j hinner hshiftq,
    norm_one_sub_mul_Shat_ge_shifted_dyadic L hξ p r j hinner hshiftr⟩

/-- The two shifted denominators in the second-coordinate second difference. -/
theorem norm_one_sub_mul_Shat_ge_e2_shifts (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (j : ℕ) (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlarge : 16 * (symbolGridStep L) ^ 2 ≤ pstar2 L p)
    (hinner : 4 * (dyad (j + 1)) ^ 2 ≤ pstar2 L p) :
    (4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L q‖) ∧
    (4 / (45 * Real.pi ^ 2) *
        ((kappa ξ) ^ 2 + (dyad (j + 1)) ^ 2) ≤
      ‖1 - ξ * Shat L r‖) := by
  obtain ⟨hshiftq, hshiftr⟩ :=
    pstar2_shift_e2_ge_quarter L hL p q r hq hr hlarge
  exact ⟨norm_one_sub_mul_Shat_ge_shifted_dyadic L hξ p q j hinner hshiftq,
    norm_one_sub_mul_Shat_ge_shifted_dyadic L hξ p r j hinner hshiftr⟩

/-- The radius and annulus-margin hypotheses hold at a concrete nonzero momentum. -/
example :
    16 * (symbolGridStep 100) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) ∧
    4 * (dyad (1 + 1)) ^ 2 ≤ pstar2 100 ((10, 0) : Z2 100) := by
  have hz : zdist 100 (10 : ZMod 100) = 10 := by decide
  simp only [symbolGridStep, pstar2, pstar, dyad, hz, zdist_zero]
  constructor <;> norm_num <;> nlinarith [Real.pi_gt_three]

end RBM
