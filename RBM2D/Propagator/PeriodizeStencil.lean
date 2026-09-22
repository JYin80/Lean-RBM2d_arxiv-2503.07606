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
resolvent equation, independent of the still-needed equation for `Kinf`.
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

/-- At unit spacing, every translated sample of the point mass has finite support. -/
theorem summable_latticePointMass_unit (x : ℤ × ℤ) :
    Summable (fun n : ℤ × ℤ => latticePointMass (x + (1 : ℕ) • n)) := by
  apply summable_of_ne_finset_zero (s := {-x})
  intro n hn
  have hne : x + n ≠ 0 := by
    intro hz
    apply hn
    have heq : n = -x := by
      calc n = -x + (x + n) := by abel
        _ = -x := by rw [hz]; simp
    simpa using heq
  simp [latticePointMass, hne]

theorem periodizeKernel_latticePointMass_unit (x : ℤ × ℤ) :
    periodizeKernel 1 latticePointMass x = 1 := by
  simp only [periodizeKernel, latticePointMass, one_smul]
  have heq : (fun n : ℤ × ℤ => if x + n = 0 then (1 : ℂ) else 0) =
      (fun n : ℤ × ℤ => if n = -x then (1 : ℂ) else 0) := by
    funext n
    congr 1
    apply propext
    constructor
    · intro hz
      calc n = -x + (x + n) := by abel
        _ = -x := by rw [hz]; simp
    · intro hn
      rw [hn]
      simp
  rw [heq]
  exact tsum_ite_eq (-x) (fun _ => (1 : ℂ))

/-- The commutation theorem applies to a nonzero, finitely supported kernel. -/
example : periodizeKernel 1 (latticeFiveAverage latticePointMass) (0, 0) = 1 := by
  rw [periodizeKernel_latticeFiveAverage 1 latticePointMass (0, 0) (by
    intro δ hδ
    simpa only [Prod.mk_zero_zero, zero_add] using summable_latticePointMass_unit δ)]
  simp [latticeFiveAverage, latticeFivePoint, periodizeKernel_latticePointMass_unit]

end RBM
