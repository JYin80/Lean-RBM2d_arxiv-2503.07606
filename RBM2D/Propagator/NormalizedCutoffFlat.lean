/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffDiff

/-!
# A zero buffer for the normalized dyadic cutoff

The cutoff is exactly zero below its inner radius. A two-step buffer in
normalized frequency keeps the cutoff zero at both coordinate shifts.
-/

namespace RBM

/-- One normalized frequency step is exactly the reciprocal side length. -/
theorem normalizedGridStep_eq_inv (L : ℕ) [NeZero L] :
    symbolGridStep L / (2 * Real.pi) = 1 / (L : ℝ) := by
  have hL : (L : ℝ) ≠ 0 := ne_of_gt (cast_L_pos L)
  unfold symbolGridStep
  field_simp [hL, Real.pi_ne_zero]

/-- The normalized cutoff vanishes at and below its inner support radius. -/
theorem normalizedDyadicCutoff_eq_zero_of_le_inner (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hp : normalizedFrequency L p ≤ dyad (j + 1)) :
    normalizedDyadicCutoff L j p = 0 := by
  exact dyadicCutoff_eq_zero_of_le_inner j (normalizedFrequency L p) hp

/-- A step in the first coordinate increases normalized frequency by at most
one grid increment, also when the original frequency is zero. -/
private theorem normalizedFrequency_shift_e1_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    normalizedFrequency L (p + (1, 0)) ≤
      normalizedFrequency L p + symbolGridStep L / (2 * Real.pi) := by
  have h := abs_normalizedFrequency_shift_e1_le L hL p
  linarith [le_abs_self
    (normalizedFrequency L (p + (1, 0)) - normalizedFrequency L p)]

/-- The analogous second-coordinate frequency increment. -/
private theorem normalizedFrequency_shift_e2_le (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (p : Z2 L) :
    normalizedFrequency L (p + (0, 1)) ≤
      normalizedFrequency L p + symbolGridStep L / (2 * Real.pi) := by
  have h := abs_normalizedFrequency_shift_e2_le L hL p
  linarith [le_abs_self
    (normalizedFrequency L (p + (0, 1)) - normalizedFrequency L p)]

/-- First-coordinate two-step flatness below the buffered inner radius. -/
theorem normalizedDyadicCutoff_eq_zero_e1_triple (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (j : ℕ) (p q r : Z2 L)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hbuffer : normalizedFrequency L p +
        2 / (L : ℝ) ≤ dyad (j + 1)) :
    normalizedDyadicCutoff L j p = 0 ∧
      normalizedDyadicCutoff L j q = 0 ∧
      normalizedDyadicCutoff L j r = 0 := by
  have hstep : 0 ≤ symbolGridStep L / (2 * Real.pi) := by
    unfold symbolGridStep
    positivity
  have hbuffer' : normalizedFrequency L p +
      2 * (symbolGridStep L / (2 * Real.pi)) ≤ dyad (j + 1) := by
    rw [normalizedGridStep_eq_inv]
    convert hbuffer using 1; ring
  have hqν : normalizedFrequency L q ≤
      normalizedFrequency L p + symbolGridStep L / (2 * Real.pi) := by
    rw [hq]
    exact normalizedFrequency_shift_e1_le L hL p
  have hrν : normalizedFrequency L r ≤
      normalizedFrequency L q + symbolGridStep L / (2 * Real.pi) := by
    rw [hr]
    exact normalizedFrequency_shift_e1_le L hL q
  exact ⟨normalizedDyadicCutoff_eq_zero_of_le_inner L j p (by linarith),
    normalizedDyadicCutoff_eq_zero_of_le_inner L j q (by linarith),
    normalizedDyadicCutoff_eq_zero_of_le_inner L j r (by linarith)⟩

/-- Second-coordinate two-step flatness with the same buffer. -/
theorem normalizedDyadicCutoff_eq_zero_e2_triple (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (j : ℕ) (p q r : Z2 L)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hbuffer : normalizedFrequency L p +
        2 / (L : ℝ) ≤ dyad (j + 1)) :
    normalizedDyadicCutoff L j p = 0 ∧
      normalizedDyadicCutoff L j q = 0 ∧
      normalizedDyadicCutoff L j r = 0 := by
  have hstep : 0 ≤ symbolGridStep L / (2 * Real.pi) := by
    unfold symbolGridStep
    positivity
  have hbuffer' : normalizedFrequency L p +
      2 * (symbolGridStep L / (2 * Real.pi)) ≤ dyad (j + 1) := by
    rw [normalizedGridStep_eq_inv]
    convert hbuffer using 1; ring
  have hqν : normalizedFrequency L q ≤
      normalizedFrequency L p + symbolGridStep L / (2 * Real.pi) := by
    rw [hq]
    exact normalizedFrequency_shift_e2_le L hL p
  have hrν : normalizedFrequency L r ≤
      normalizedFrequency L q + symbolGridStep L / (2 * Real.pi) := by
    rw [hr]
    exact normalizedFrequency_shift_e2_le L hL q
  exact ⟨normalizedDyadicCutoff_eq_zero_of_le_inner L j p (by linarith),
    normalizedDyadicCutoff_eq_zero_of_le_inner L j q (by linarith),
    normalizedDyadicCutoff_eq_zero_of_le_inner L j r (by linarith)⟩

/-- A nonempty two-step zero buffer at the origin. -/
example :
    normalizedDyadicCutoff 16 2 ((0, 0) : Z2 16) = 0 ∧
      normalizedDyadicCutoff 16 2 ((1, 0) : Z2 16) = 0 ∧
      normalizedDyadicCutoff 16 2 ((2, 0) : Z2 16) = 0 := by
  apply normalizedDyadicCutoff_eq_zero_e1_triple 16 (by norm_num) 2
    (0, 0) ((0, 0) + (1, 0)) (((0, 0) + (1, 0)) + (1, 0)) rfl rfl
  have hν : normalizedFrequency 16 ((0, 0) : Z2 16) = 0 := by
    simp [normalizedFrequency, pstar2, pstar, zdist_zero]
  rw [hν]
  norm_num [dyad]

end RBM

#print axioms RBM.normalizedDyadicCutoff_eq_zero_of_le_inner
#print axioms RBM.normalizedGridStep_eq_inv
#print axioms RBM.normalizedDyadicCutoff_eq_zero_e1_triple
#print axioms RBM.normalizedDyadicCutoff_eq_zero_e2_triple
