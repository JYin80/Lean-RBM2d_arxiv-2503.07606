/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Tactic

/-!
# Finite boxes and max-norm shells in `ℤ²`

These finite counting statements supply the lattice multiplicity needed to
sum exponentially decaying tails in the two-dimensional periodization step.
They contain no analytic claim about the infinite-volume kernel.
-/

namespace RBM

/-- The closed integer square `[-r,r] × [-r,r]`. -/
def periodizationBox (r : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(r : ℤ)) (r : ℤ)).product
    (Finset.Icc (-(r : ℤ)) (r : ℤ))

/-- The max-norm shell of radius `r`; Mathlib's `Finset.box` is exactly the
difference of successive closed integer squares. -/
def periodizationShell (r : ℕ) : Finset (ℤ × ℤ) := Finset.box r

theorem mem_periodizationBox (r : ℕ) (p : ℤ × ℤ) :
    p ∈ periodizationBox r ↔
      -(r : ℤ) ≤ p.1 ∧ p.1 ≤ r ∧ -(r : ℤ) ≤ p.2 ∧ p.2 ≤ r := by
  simp [periodizationBox, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- There are exactly `(2r+1)²` lattice points in the square. -/
theorem card_periodizationBox (r : ℕ) :
    (periodizationBox r).card = (2 * r + 1) ^ 2 := by
  have hcard : ((Finset.Icc (-(r : ℤ)) (r : ℤ)).card : ℤ) =
      2 * (r : ℤ) + 1 := by
    simpa [sub_neg_eq_add, two_mul, add_assoc, add_comm, add_left_comm] using
      (Int.card_Icc_of_le (a := -(r : ℤ)) (b := (r : ℤ)) (by omega))
  have hnat : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
    exact_mod_cast hcard
  simp [periodizationBox, Finset.card_product, hnat, pow_two]

/-- The shell really is the set of points with max-norm exactly `r`. -/
theorem mem_periodizationShell (r : ℕ) (p : ℤ × ℤ) :
    p ∈ periodizationShell r ↔
      max p.1.natAbs p.2.natAbs = r := by
  exact Int.mem_box

/-- Each lattice point belongs to exactly one max-norm shell. -/
theorem existsUnique_mem_periodizationShell (p : ℤ × ℤ) :
    ∃! r : ℕ, p ∈ periodizationShell r :=
  Int.existsUnique_mem_box p

/-- Exact shell count, including the singleton at radius zero. -/
theorem card_periodizationShell_zero : (periodizationShell 0).card = 1 := by
  simp [periodizationShell]

theorem card_periodizationShell_pos (r : ℕ) (hr : r ≠ 0) :
    (periodizationShell r).card = 8 * r := by
  exact Int.card_box hr

/-- A polynomial shell bound sufficient for exponentially decaying tails. -/
theorem card_periodizationShell_le (r : ℕ) :
    (periodizationShell r).card ≤ 8 * (r + 1) ^ 2 := by
  by_cases hr : r = 0
  · subst r
    simp [card_periodizationShell_zero]
  · rw [card_periodizationShell_pos r hr]
    have h : r ≤ (r + 1) ^ 2 := by nlinarith
    exact Nat.mul_le_mul_left 8 h

/-- The first nonzero shell contains a concrete point. -/
example : (1, 0) ∈ periodizationShell 1 := by
  simp [mem_periodizationShell]

end RBM
