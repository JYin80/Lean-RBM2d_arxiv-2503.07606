/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffFlat

/-!
# A zero buffer beyond the normalized dyadic cutoff

The cutoff vanishes above its outer radius. An extra `2/L` of normalized
frequency keeps it zero after either of two coordinate steps.
-/

namespace RBM

/-- The normalized cutoff vanishes at and above its outer support radius. -/
theorem normalizedDyadicCutoff_eq_zero_of_outer_le (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hp : 2 * dyad j ≤ normalizedFrequency L p) :
    normalizedDyadicCutoff L j p = 0 := by
  exact dyadicCutoff_eq_zero_of_outer_le j (normalizedFrequency L p) hp

/-- A first-coordinate step can reduce normalized frequency by at most `1/L`. -/
private theorem normalizedFrequency_le_shift_e1 (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    normalizedFrequency L p ≤
      normalizedFrequency L (p + (1, 0)) + 1 / (L : ℝ) := by
  have h := abs_normalizedFrequency_shift_e1_le L hL p
  rw [normalizedGridStep_eq_inv] at h
  have ⟨hleft, _⟩ := abs_le.mp h
  linarith

/-- The matching lower shift bound in the second coordinate. -/
private theorem normalizedFrequency_le_shift_e2 (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    normalizedFrequency L p ≤
      normalizedFrequency L (p + (0, 1)) + 1 / (L : ℝ) := by
  have h := abs_normalizedFrequency_shift_e2_le L hL p
  rw [normalizedGridStep_eq_inv] at h
  have ⟨hleft, _⟩ := abs_le.mp h
  linarith

/-- First-coordinate three-point vanishing beyond the buffered outer radius. -/
theorem normalizedDyadicCutoff_eq_zero_e1_outer_triple
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) (p q r : Z2 L)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hbuffer : 2 * dyad j ≤ normalizedFrequency L p - 2 / (L : ℝ)) :
    normalizedDyadicCutoff L j p = 0 ∧
      normalizedDyadicCutoff L j q = 0 ∧
      normalizedDyadicCutoff L j r = 0 := by
  have hinv : 0 ≤ 1 / (L : ℝ) := by positivity
  have htwo : 2 / (L : ℝ) = 2 * (1 / (L : ℝ)) := by ring
  rw [htwo] at hbuffer
  have hqν : normalizedFrequency L p ≤
      normalizedFrequency L q + 1 / (L : ℝ) := by
    rw [hq]
    exact normalizedFrequency_le_shift_e1 L hL p
  have hrν : normalizedFrequency L q ≤
      normalizedFrequency L r + 1 / (L : ℝ) := by
    rw [hr]
    exact normalizedFrequency_le_shift_e1 L hL q
  exact ⟨normalizedDyadicCutoff_eq_zero_of_outer_le L j p (by linarith),
    normalizedDyadicCutoff_eq_zero_of_outer_le L j q (by linarith),
    normalizedDyadicCutoff_eq_zero_of_outer_le L j r (by linarith)⟩

/-- Second-coordinate three-point vanishing with the same outer buffer. -/
theorem normalizedDyadicCutoff_eq_zero_e2_outer_triple
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (j : ℕ) (p q r : Z2 L)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hbuffer : 2 * dyad j ≤ normalizedFrequency L p - 2 / (L : ℝ)) :
    normalizedDyadicCutoff L j p = 0 ∧
      normalizedDyadicCutoff L j q = 0 ∧
      normalizedDyadicCutoff L j r = 0 := by
  have hinv : 0 ≤ 1 / (L : ℝ) := by positivity
  have htwo : 2 / (L : ℝ) = 2 * (1 / (L : ℝ)) := by ring
  rw [htwo] at hbuffer
  have hqν : normalizedFrequency L p ≤
      normalizedFrequency L q + 1 / (L : ℝ) := by
    rw [hq]
    exact normalizedFrequency_le_shift_e2 L hL p
  have hrν : normalizedFrequency L q ≤
      normalizedFrequency L r + 1 / (L : ℝ) := by
    rw [hr]
    exact normalizedFrequency_le_shift_e2 L hL q
  exact ⟨normalizedDyadicCutoff_eq_zero_of_outer_le L j p (by linarith),
    normalizedDyadicCutoff_eq_zero_of_outer_le L j q (by linarith),
    normalizedDyadicCutoff_eq_zero_of_outer_le L j r (by linarith)⟩

/-- A nonempty outer buffer: all three points lie at or above radius `1/4`. -/
example :
    normalizedDyadicCutoff 8 3 ((4, 0) : Z2 8) = 0 ∧
      normalizedDyadicCutoff 8 3 ((5, 0) : Z2 8) = 0 ∧
      normalizedDyadicCutoff 8 3 ((6, 0) : Z2 8) = 0 := by
  apply normalizedDyadicCutoff_eq_zero_e1_outer_triple 8 (by norm_num) 3
    (4, 0) ((4, 0) + (1, 0)) (((4, 0) + (1, 0)) + (1, 0)) rfl rfl
  have hz : zdist 8 (4 : ZMod 8) = 4 := by decide
  have hrad : pstar2 8 ((4, 0) : Z2 8) = Real.pi ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
      Nat.cast_zero, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 8 ((4, 0) : Z2 8) = 1 / 2 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hν]
  norm_num [dyad]

end RBM

#print axioms RBM.normalizedDyadicCutoff_eq_zero_of_outer_le
#print axioms RBM.normalizedDyadicCutoff_eq_zero_e1_outer_triple
#print axioms RBM.normalizedDyadicCutoff_eq_zero_e2_outer_triple
