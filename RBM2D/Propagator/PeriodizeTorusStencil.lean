/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeDelta
import RBM2D.Propagator.Symbol

/-!
# The periodized five-point stencil is `S^(B)`

The integer-lattice five-point average descends to exactly the paper's torus
transition matrix. The support is symmetric, so the signs in the circulant
convention `SB L a b = sbKernel L (a-b)` agree with the lattice stencil.
-/

namespace RBM

open Matrix

/-- Write the integer five-point average as the five explicit terms. -/
theorem latticeFiveAverage_apply (K : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    latticeFiveAverage K x =
      (K x + K (x + (1, 0)) + K (x + (-1, 0)) +
        K (x + (0, 1)) + K (x + (0, -1))) / 5 := by
  simp [latticeFiveAverage, latticeFivePoint, Prod.mk.injEq]
  simp only [Prod.mk_zero_zero, add_zero]
  ring

/-- The canonical integer lift reduces to the original torus point. -/
theorem torusLatticeLift_cast (L : ℕ) [NeZero L] (u : Z2 L) :
    (((torusLatticeLift u).1 : ZMod L),
      ((torusLatticeLift u).2 : ZMod L)) = u := by
  apply Prod.ext
  · simp [torusLatticeLift]
  · simp [torusLatticeLift]

/-- Shifted representatives evaluate the descended kernel at the
correspondingly shifted torus point. -/
theorem periodizeKernel_lift_add (L : ℕ) [NeZero L]
    (K : ℤ × ℤ → ℂ) (u : Z2 L) (δ : ℤ × ℤ) :
    periodizeKernel L K (torusLatticeLift u + δ) =
      periodizedTorusKernel L K
        (u + ((δ.1 : ZMod L), (δ.2 : ZMod L))) := by
  symm
  apply periodizedTorusKernel_eq_of_cast
  apply Prod.ext
  · simp [torusLatticeLift]
  · simp [torusLatticeLift]

/-- Periodizing the integer five-point average gives the action of `S^(B)`
on the descended periodized kernel. -/
theorem periodizedTorusKernel_latticeFiveAverage (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (K : ℤ × ℤ → ℂ) (u : Z2 L)
    (hs : ∀ δ ∈ latticeFivePoint,
      Summable (fun n : ℤ × ℤ => K (torusLatticeLift u + δ + L • n))) :
    periodizedTorusKernel L (latticeFiveAverage K) u =
      (SB L *ᵥ periodizedTorusKernel L K) u := by
  rw [periodizedTorusKernel,
    periodizeKernel_latticeFiveAverage L K (torusLatticeLift u) hs,
    latticeFiveAverage_apply, SB_mulVec_apply L hL]
  rw [show periodizeKernel L K (torusLatticeLift u) =
      periodizedTorusKernel L K u from rfl,
    periodizeKernel_lift_add L K u (1, 0),
    periodizeKernel_lift_add L K u (-1, 0),
    periodizeKernel_lift_add L K u (0, 1),
    periodizeKernel_lift_add L K u (0, -1)]
  simp only [Int.cast_one, Int.cast_zero,
    Int.cast_neg, sub_eq_add_neg, Prod.neg_mk, neg_zero]
  ring

/-- Every periodized sample of the lattice point mass has finite support when
`L` is positive. This verifies the analytic hypothesis for a nonzero kernel. -/
theorem summable_latticePointMass_periodized (L : ℕ) (hL : L ≠ 0)
    (x : ℤ × ℤ) :
    Summable (fun n : ℤ × ℤ => latticePointMass (x + L • n)) := by
  have hpoint : Summable latticePointMass := by
    apply summable_of_ne_finset_zero (s := {0})
    intro y hy
    simp only [Finset.mem_singleton] at hy
    simp [latticePointMass, hy]
  have hinj : Function.Injective (fun n : ℤ × ℤ => x + L • n) := by
    intro a b hab
    exact (nsmul_right_injective hL) (add_left_cancel hab)
  exact hpoint.comp_injective hinj

/-- A nonzero three-by-three example that exercises the summability
hypothesis and the stencil identity. -/
example : periodizedTorusKernel 3 (latticeFiveAverage latticePointMass)
    ((0, 0) : Z2 3) = 1 / 5 := by
  rw [periodizedTorusKernel_latticeFiveAverage 3 (by norm_num) latticePointMass
    ((0, 0) : Z2 3) (by
      intro δ hδ
      exact summable_latticePointMass_periodized 3 (by norm_num) _)]
  rw [SB_mulVec_apply 3 (by norm_num)]
  simp [periodizedTorusKernel_latticePointMass]

end RBM
