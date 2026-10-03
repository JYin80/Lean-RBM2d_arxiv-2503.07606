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

/-- The max-norm shell of radius `r`; Mathlib's `Finset.box` is exactly the
difference of successive closed integer squares. -/
def periodizationShell (r : ℕ) : Finset (ℤ × ℤ) := Finset.box r

/-- The shell really is the set of points with max-norm exactly `r`. -/
theorem mem_periodizationShell (r : ℕ) (p : ℤ × ℤ) :
    p ∈ periodizationShell r ↔
      max p.1.natAbs p.2.natAbs = r := by
  exact Int.mem_box

/-- Each lattice point belongs to exactly one max-norm shell. -/
theorem existsUnique_mem_periodizationShell (p : ℤ × ℤ) :
    ∃! r : ℕ, p ∈ periodizationShell r :=
  Int.existsUnique_mem_box p

theorem card_periodizationShell_pos (r : ℕ) (hr : r ≠ 0) :
    (periodizationShell r).card = 8 * r := by
  exact Int.card_box hr

end RBM
