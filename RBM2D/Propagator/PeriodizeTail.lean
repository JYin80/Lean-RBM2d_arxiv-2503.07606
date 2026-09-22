/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeShells
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summable geometric tails on `ℤ²`

The max-norm shell at radius `r > 0` has exactly `8r` points. Thus geometric
decay in that radius is summable. This is the counting and convergence input
for periodization, before any statement about the infinite-volume kernel.
-/

namespace RBM

/-- The max norm of an integer lattice point, as a natural number. -/
def latticeMaxRadius (n : ℤ × ℤ) : ℕ := max n.1.natAbs n.2.natAbs

theorem latticeMaxRadius_eq_shell (r : ℕ) (n : ℤ × ℤ) :
    n ∈ periodizationShell r ↔ latticeMaxRadius n = r :=
  mem_periodizationShell r n

/-- The sum over a single shell is its cardinality times the radial value. -/
theorem sum_periodizationShell_pow (ρ : ℝ) (r : ℕ) :
    ∑ n ∈ periodizationShell r, ρ ^ latticeMaxRadius n =
      (periodizationShell r).card * ρ ^ r := by
  have hval : ∀ n ∈ periodizationShell r, ρ ^ latticeMaxRadius n = ρ ^ r := by
    intro n hn
    rw [(latticeMaxRadius_eq_shell r n).mp hn]
  simp_rw [Finset.sum_congr rfl hval]
  simp

/-- The radial shell weights form a summable sequence when `0 ≤ ρ < 1`. -/
theorem summable_shell_weights {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun r : ℕ => ((periodizationShell r).card : ℝ) * ρ ^ r) := by
  have hnorm : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρ1
  have hgeom : Summable (fun r : ℕ => (8 : ℝ) * r * ρ ^ r) := by
    simpa [pow_one, mul_assoc] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (8 : ℝ)
  apply (summable_nat_add_iff 1).mp
  have htail := (summable_nat_add_iff 1).mpr hgeom
  convert htail using 1
  funext r
  rw [card_periodizationShell_pos (r + 1) (by omega)]
  norm_cast

/-- The geometric max-norm weight is summable over the full integer lattice. -/
theorem summable_latticeMaxRadius_pow {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℤ × ℤ => ρ ^ latticeMaxRadius n) := by
  rw [summable_partition (f := fun n : ℤ × ℤ => ρ ^ latticeMaxRadius n)
    (s := fun r : ℕ => {n | n ∈ periodizationShell r})
    (fun n => pow_nonneg hρ _) (fun n => existsUnique_mem_periodizationShell n)]
  refine ⟨fun r => (hasSum_fintype (β := {n : ℤ × ℤ | n ∈ periodizationShell r}) _).summable, ?_⟩
  have hweights := summable_shell_weights hρ hρ1
  convert hweights using 1
  funext r
  simp only [tsum_fintype]
  have hval : ∀ n : {n : ℤ × ℤ | n ∈ periodizationShell r},
      ρ ^ latticeMaxRadius n = ρ ^ r := by
    intro n
    rw [(latticeMaxRadius_eq_shell r n).mp n.property]
  simp_rw [hval]
  simp

/-- A concrete nonzero decay parameter in the admissible range. -/
example : Summable (fun n : ℤ × ℤ => (1 / 2 : ℝ) ^ latticeMaxRadius n) :=
  summable_latticeMaxRadius_pow (by norm_num) (by norm_num)

end RBM
