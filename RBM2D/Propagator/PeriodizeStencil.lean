/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeDescend

/-!
# Finite-stencil commutation with periodization

The five-point averaging operator on `ℤ²` commutes with an absolutely
convergent periodization. This is the summation step in the periodized
resolvent equation, independent of the equation for `Kinf`.
-/

namespace RBM

/-- The origin and four nearest neighbours in `ℤ²`. -/
def latticeFivePoint : Finset (ℤ × ℤ) :=
  {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The paper's lazy five-point averaging operator on the integer lattice. -/
noncomputable def latticeFiveAverage (K : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  (1 / 5 : ℂ) * ∑ δ ∈ latticeFivePoint, K (x + δ)

/-- Finite-stencil averaging commutes with periodization when each of its five
shifted lattice families is summable. -/
theorem periodizeKernel_latticeFiveAverage (L : ℕ) (K : ℤ × ℤ → ℂ)
    (x : ℤ × ℤ)
    (hs : ∀ δ ∈ latticeFivePoint,
      Summable (fun n : ℤ × ℤ => K (x + δ + L • n))) :
    periodizeKernel L (latticeFiveAverage K) x =
      latticeFiveAverage (periodizeKernel L K) x := by
  calc
    periodizeKernel L (latticeFiveAverage K) x
        = ∑' n : ℤ × ℤ, (1 / 5 : ℂ) *
            ∑ δ ∈ latticeFivePoint, K (x + δ + L • n) := by
              unfold periodizeKernel latticeFiveAverage
              congr 1
              funext n
              congr 1
              apply Finset.sum_congr rfl
              intro δ hδ
              congr 1
              abel
    _ = (1 / 5 : ℂ) * ∑' n : ℤ × ℤ,
          ∑ δ ∈ latticeFivePoint, K (x + δ + L • n) := tsum_mul_left
    _ = (1 / 5 : ℂ) * ∑ δ ∈ latticeFivePoint,
          ∑' n : ℤ × ℤ, K (x + δ + L • n) := by
            rw [Summable.tsum_finsetSum hs]
    _ = latticeFiveAverage (periodizeKernel L K) x := by
          simp only [latticeFiveAverage, periodizeKernel]

/-- A point mass on the integer lattice. -/
def latticePointMass (x : ℤ × ℤ) : ℂ := if x = 0 then 1 else 0

end RBM
