/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedRadiusSecondDiff

/-!
# A checkable no-fold condition for two momentum shifts

The three integer representatives stay in one affine branch of the cycle
distance if they are all on the lower half, or all on the upper half without
wrapping through zero. This condition excludes the antipodal and zero folds.
-/

namespace RBM

/-- A representative and its next two successors lie on a single affine
branch of the cycle distance. -/
def noFoldTwo (L : ℕ) [NeZero L] (u : ZMod L) : Prop :=
  2 * (u.val + 2) ≤ L ∨
    (L ≤ 2 * u.val ∧ u.val + 2 < L)

private theorem zdist_two_step_affine (L : ℕ) [NeZero L]
    (u : ZMod L) (h : noFoldTwo L u) :
    zdist L (u + 1 + 1) + zdist L u =
      2 * zdist L (u + 1) := by
  have hval : u.val < L := ZMod.val_lt u
  have hnoWrap : u.val + 2 < L := by
    rcases h with hlow | ⟨_, hhigh⟩
    · omega
    · exact hhigh
  have hone : (1 : ZMod L).val = 1 := by
    have h : ((1 : ℕ) : ZMod L).val = 1 :=
      ZMod.val_cast_of_lt (by omega)
    simpa using h
  have hq : (u + 1).val = u.val + 1 := by
    rw [ZMod.val_add, hone, Nat.mod_eq_of_lt (by omega)]
  have hr : (u + 1 + 1).val = u.val + 2 := by
    rw [ZMod.val_add, hone, hq, Nat.mod_eq_of_lt (by omega)]
  simp only [zdist, hq, hr]
  rcases h with hlow | ⟨hupper, _⟩
  · have hu : u.val ≤ L - u.val := by omega
    have hq' : u.val + 1 ≤ L - (u.val + 1) := by omega
    have hr' : u.val + 2 ≤ L - (u.val + 2) := by omega
    rw [min_eq_left hu, min_eq_left hq', min_eq_left hr']
    omega
  · have hu : L - u.val ≤ u.val := by omega
    have hq' : L - (u.val + 1) ≤ u.val + 1 := by omega
    have hr' : L - (u.val + 2) ≤ u.val + 2 := by omega
    rw [min_eq_right hu, min_eq_right hq', min_eq_right hr']
    omega

/-- The physical angular radius has zero second difference under `noFoldTwo`. -/
theorem pstar_second_diff_eq_zero_of_noFoldTwo (L : ℕ) [NeZero L]
    (u : ZMod L) (h : noFoldTwo L u) :
    pstar L (u + 1 + 1) - 2 * pstar L (u + 1) + pstar L u = 0 := by
  have hz := zdist_two_step_affine L u h
  have hzR : (zdist L (u + 1 + 1) : ℝ) + (zdist L u : ℝ) =
      2 * (zdist L (u + 1) : ℝ) := by exact_mod_cast hz
  have hp (v : ZMod L) : pstar L v =
      symbolGridStep L * (zdist L v : ℝ) := by
    unfold pstar symbolGridStep
    ring
  rw [hp, hp, hp]
  linear_combination (symbolGridStep L) * hzR

/-- An integer representative condition supplies the no-fold hypothesis in
the first-coordinate quadratic radius estimate. -/
theorem abs_normalizedFrequency_second_diff_e1_le_of_noFoldTwo
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (ρ : ℝ)
    (hq : q = p + (1, 0)) (hr : r = q + (1, 0))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (hnoFold : noFoldTwo L p.1) :
    |normalizedFrequency L r - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  apply abs_normalizedFrequency_second_diff_e1_le_of_affine L hL p q r ρ
    hq hr hρ hmiddle
  simpa [hq, hr] using pstar_second_diff_eq_zero_of_noFoldTwo L p.1 hnoFold

/-- The same representative criterion for the second coordinate. -/
theorem abs_normalizedFrequency_second_diff_e2_le_of_noFoldTwo
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q r : Z2 L) (ρ : ℝ)
    (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hρ : 0 < ρ) (hmiddle : ρ ≤ normalizedFrequency L q)
    (hnoFold : noFoldTwo L p.2) :
    |normalizedFrequency L r - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  apply abs_normalizedFrequency_second_diff_e2_le_of_affine L hL p q r ρ
    hq hr hρ hmiddle
  simpa [hq, hr] using pstar_second_diff_eq_zero_of_noFoldTwo L p.2 hnoFold

/-- The criterion holds for a nonzero coordinate away from both folds. -/
example : noFoldTwo 8 (1 : ZMod 8) := by
  left
  decide

end RBM

#print axioms RBM.pstar_second_diff_eq_zero_of_noFoldTwo
#print axioms RBM.abs_normalizedFrequency_second_diff_e1_le_of_noFoldTwo
#print axioms RBM.abs_normalizedFrequency_second_diff_e2_le_of_noFoldTwo
