/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeTorusStencil

/-!
# Conditional bridge from the lattice resolvent to the torus resolvent

If a complex lattice kernel solves the five-point resolvent equation and its
five shifted periodization families are summable, its periodization is the
finite-torus propagator. The analytic estimate and lattice equation for the
paper's actual `Kinf` remain separate obligations.
-/

namespace RBM

open Matrix

/-- The periodized lattice resolvent equation on the torus. -/
theorem periodizedTorusKernel_sub_SB_mulVec (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (ξ : ℂ) (K : ℤ × ℤ → ℂ)
    (hs : ∀ u : Z2 L, ∀ δ ∈ latticeFivePoint,
      Summable (fun n : ℤ × ℤ => K (torusLatticeLift u + δ + L • n)))
    (hK : ∀ x : ℤ × ℤ,
      K x - ξ * latticeFiveAverage K x = latticePointMass x)
    (u : Z2 L) :
    periodizedTorusKernel L K u -
      ξ * (SB L *ᵥ periodizedTorusKernel L K) u =
        if u = 0 then 1 else 0 := by
  have hzero : (0 : ℤ × ℤ) ∈ latticeFivePoint := by
    change (0, 0) ∈ latticeFivePoint
    simp [latticeFivePoint]
  have hs0 : Summable (fun n : ℤ × ℤ => K (torusLatticeLift u + L • n)) := by
    simpa only [zero_add, add_zero] using hs u 0 hzero
  have hsavg : Summable
      (fun n : ℤ × ℤ => latticeFiveAverage K (torusLatticeLift u + L • n)) := by
    have hsum : Summable (fun n : ℤ × ℤ =>
        ∑ δ ∈ latticeFivePoint, K (torusLatticeLift u + δ + L • n)) :=
      summable_sum (hs u)
    have hscaled := hsum.mul_left (1 / 5 : ℂ)
    convert hscaled using 1
    funext n
    unfold latticeFiveAverage
    congr 1
    apply Finset.sum_congr rfl
    intro δ hδ
    congr 1
    abel
  have hpoint : ∀ n : ℤ × ℤ,
      K (torusLatticeLift u + L • n) -
        ξ * latticeFiveAverage K (torusLatticeLift u + L • n) =
          latticePointMass (torusLatticeLift u + L • n) := by
    intro n
    exact hK _
  have htsum :
      (∑' n : ℤ × ℤ,
        (K (torusLatticeLift u + L • n) -
          ξ * latticeFiveAverage K (torusLatticeLift u + L • n))) =
        ∑' n : ℤ × ℤ, latticePointMass (torusLatticeLift u + L • n) := by
    exact tsum_congr hpoint
  rw [Summable.tsum_sub hs0 (hsavg.mul_left ξ), tsum_mul_left] at htsum
  change periodizedTorusKernel L K u -
      ξ * periodizedTorusKernel L (latticeFiveAverage K) u =
        periodizedTorusKernel L latticePointMass u at htsum
  rw [periodizedTorusKernel_latticeFiveAverage L hL K u (hs u),
    periodizedTorusKernel_latticePointMass L u] at htsum
  exact htsum

/-- Inverse uniqueness identifies the circulant matrix of the periodized
kernel with the paper's finite-torus propagator. -/
theorem Theta_eq_circulant_periodized (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (K : ℤ × ℤ → ℂ)
    (hs : ∀ u : Z2 L, ∀ δ ∈ latticeFivePoint,
      Summable (fun n : ℤ × ℤ => K (torusLatticeLift u + δ + L • n)))
    (hK : ∀ x : ℤ × ℤ,
      K x - ξ * latticeFiveAverage K x = latticePointMass x) :
    Theta L ξ = circulant (periodizedTorusKernel L K) := by
  refine (eq_Theta_of_mul L hL hξ ?_).symm
  have hmul : circulant (periodizedTorusKernel L K) * SB L =
      circulant (SB L *ᵥ periodizedTorusKernel L K) := by
    rw [SB, circulant_mul_comm, circulant_mul]
  rw [mul_sub, mul_one, Matrix.mul_smul, hmul, ← circulant_smul,
    ← circulant_sub, ← circulant_single_one ℂ (Z2 L), circulant_inj]
  funext u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  exact periodizedTorusKernel_sub_SB_mulVec L hL ξ K hs hK u

/-- Entrywise form: evaluate the periodization at the torus difference. -/
theorem Theta_apply_periodized (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (K : ℤ × ℤ → ℂ)
    (hs : ∀ u : Z2 L, ∀ δ ∈ latticeFivePoint,
      Summable (fun n : ℤ × ℤ => K (torusLatticeLift u + δ + L • n)))
    (hK : ∀ x : ℤ × ℤ,
      K x - ξ * latticeFiveAverage K x = latticePointMass x)
    (a b : Z2 L) :
    Theta L ξ a b = periodizedTorusKernel L K (a - b) := by
  rw [Theta_eq_circulant_periodized L hL hξ K hs hK, circulant_apply]

/-- The bridge has a concrete solution at `ξ = 0` on the three-by-three torus. -/
example : Theta 3 0 = circulant (periodizedTorusKernel 3 latticePointMass) := by
  apply Theta_eq_circulant_periodized 3 (by norm_num) (by norm_num) latticePointMass
  · intro u δ hδ
    exact summable_latticePointMass_periodized 3 (by norm_num) _
  · intro x
    simp

end RBM
