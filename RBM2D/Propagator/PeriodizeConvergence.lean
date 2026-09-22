/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeTail

/-!
# Comparison criterion for complex lattice kernels

An explicit geometric bound in max-norm implies absolute summability of a
complex kernel on `ℤ²`. The hypothesis is a numerical norm inequality; it does
not supply the missing estimate for the paper's actual `Kinf` kernel.
-/

namespace RBM

/-- A complex kernel with an explicit geometric max-norm majorant is summable. -/
theorem summable_complex_lattice_of_geometric_bound
    (K : ℤ × ℤ → ℂ) (C ρ : ℝ) (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ n, ‖K n‖ ≤ C * ρ ^ latticeMaxRadius n) : Summable K := by
  have hmajor : Summable (fun n : ℤ × ℤ => C * ρ ^ latticeMaxRadius n) :=
    (summable_latticeMaxRadius_pow hρ hρ1).mul_left C
  exact hmajor.of_norm_bounded hK

/-- The same criterion for a kernel sampled on a translated lattice. The
bound is stated at the translated arguments, as required for periodization. -/
theorem summable_complex_lattice_translate_of_geometric_bound
    (K : ℤ × ℤ → ℂ) (x : ℤ × ℤ) (C ρ : ℝ)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ n, ‖K (x + n)‖ ≤ C * ρ ^ latticeMaxRadius n) :
    Summable (fun n : ℤ × ℤ => K (x + n)) :=
  summable_complex_lattice_of_geometric_bound
    (fun n => K (x + n)) C ρ hC hρ hρ1 hK

/-- A nonzero geometric kernel, with `ρ = 1/2`, satisfies the criterion. -/
theorem summable_complex_geometric_half :
    Summable (fun n : ℤ × ℤ => ((1 / 2 : ℝ) ^ latticeMaxRadius n : ℂ)) := by
  apply summable_complex_lattice_of_geometric_bound
    (fun n : ℤ × ℤ => ((1 / 2 : ℝ) ^ latticeMaxRadius n : ℂ))
    1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  intro n
  simp

example : ((1 / 2 : ℝ) ^ latticeMaxRadius (0, 0) : ℂ) = 1 := by
  norm_num [latticeMaxRadius]

end RBM
