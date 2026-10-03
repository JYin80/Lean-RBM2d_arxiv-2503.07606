/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeTail

/-!
# Comparison criterion for complex lattice kernels

An explicit geometric bound in max-norm implies absolute summability of a
complex kernel on `ℤ²`. The hypothesis is a numerical norm inequality; for the
paper's `Kinf` kernel the estimate is `norm_Kinf_le` (`Propagator/KinfBound.lean`).
-/

namespace RBM

/-- A complex kernel with an explicit geometric max-norm majorant is summable. -/
theorem summable_complex_lattice_of_geometric_bound
    (K : ℤ × ℤ → ℂ) (C ρ : ℝ) (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ n, ‖K n‖ ≤ C * ρ ^ latticeMaxRadius n) : Summable K := by
  have hmajor : Summable (fun n : ℤ × ℤ => C * ρ ^ latticeMaxRadius n) :=
    (summable_latticeMaxRadius_pow hρ hρ1).mul_left C
  exact hmajor.of_norm_bounded hK

end RBM
