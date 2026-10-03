/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueProjectionWords
import RBM2D.Hierarchy.LoopHierarchyCutContinuity
import RBM2D.Propagator.Basic

/-!
# Block-label sums of finite cut-loop bounds

For `L ≥ 3`, each row of the actual five-point block covariance has total
absolute mass one. Thus a double block-label sum contributes one factor
`card (Z2 L)`, not its square, to the crude cut-loop envelope.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Real norm row sum of the actual block covariance, for `L ≥ 3`. -/
theorem sum_norm_SB_row (hL : 3 ≤ L) (p : Z2 L) :
    ∑ q : Z2 L, ‖SB L p q‖ = (1 : ℝ) := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    (RBM.sum_nnnorm_SB_row L hL p)
  simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using h

end RBM.Gauss
