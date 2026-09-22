/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.ODE.Gronwall

/-!
# A dimension-independent Grönwall bridge

The derivative inequality for a real moment function is converted into an interval bound.
The hypothesis is a one-sided derivative along `Ici x`, matching Mathlib's slope formulation.
-/

namespace RBM.Gauss

/-- If `φ' ≤ K φ + ε` on `[a,b)` and `φ a ≤ δ`, then `φ` is bounded by the
Grönwall comparison function on `[a,b]`. No sign condition on the constants is needed. -/
theorem le_gronwallBound_of_hasDerivWithinAt_le {φ φ' : ℝ → ℝ} {δ K ε a b : ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt φ (φ' x) (Set.Ici x) x)
    (hδ : φ a ≤ δ) (hbound : ∀ x ∈ Set.Ico a b, φ' x ≤ K * φ x + ε) :
    ∀ x ∈ Set.Icc a b, φ x ≤ gronwallBound δ K ε (x - a) := by
  refine le_gronwallBound_of_liminf_deriv_right_le hcont (fun x hx r hr => ?_) hδ hbound
  have h := (hderiv x hx).liminf_right_slope_le hr
  simpa [slope_def_field, div_eq_inv_mul] using h

/-- A nonconstant witness: `φ(x)=x` satisfies the comparison with `φ'=1`, `K=0`, `ε=1`. -/
theorem gronwall_linear_example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ≤ gronwallBound 0 0 1 (x - 0) := by
  apply le_gronwallBound_of_hasDerivWithinAt_le
    (φ := fun x : ℝ => x) (φ' := fun _ => 1)
  · exact continuous_id.continuousOn
  · intro x hx
    exact (hasDerivAt_id x).hasDerivWithinAt
  · norm_num
  · intro x hx
    norm_num

end RBM.Gauss
