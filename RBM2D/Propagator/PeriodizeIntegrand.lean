/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeFourierDelta
import RBM2D.Propagator.PeriodizeTorusStencil

/-!
# The five-point resolvent equation at the Fourier integrand level

The continuous Fourier numerator is an eigenfunction of the five-point
integer-lattice average with eigenvalue `Scont`. Division by `Dcont` then gives
the pointwise identity needed for the infinite-volume lattice equation.
-/

namespace RBM

open Real intervalIntegral MeasureTheory

/-- Fourier characters multiply under addition of lattice points. -/
theorem continuumNumerator_add (x y : ℤ × ℤ) (p : ℝ × ℝ) :
    continuumNumerator (x + y) p =
      continuumNumerator x p * continuumNumerator y p := by
  unfold continuumNumerator continuumPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- The two opposite coordinate characters give twice the cosine. -/
theorem exp_pair_eq_two_cos (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) +
      Complex.exp (-(Complex.I * (t : ℂ))) =
        ((2 * Real.cos t : ℝ) : ℂ) := by
  calc
    Complex.exp (Complex.I * (t : ℂ)) +
        Complex.exp (-(Complex.I * (t : ℂ))) =
          Complex.exp ((t : ℂ) * Complex.I) +
            Complex.exp (-(t : ℂ) * Complex.I) := by congr 1 <;> ring_nf
    _ = 2 * Complex.cos (t : ℂ) := (Complex.two_cos _).symm
    _ = ((2 * Real.cos t : ℝ) : ℂ) := by
          rw [← Complex.ofReal_cos]
          push_cast
          ring

/-- The lattice stencil has the continuous symbol as its eigenvalue. -/
theorem latticeFiveAverage_continuumNumerator (x : ℤ × ℤ) (p : ℝ × ℝ) :
    latticeFiveAverage (fun y => continuumNumerator y p) x =
      Scont p * continuumNumerator x p := by
  rw [latticeFiveAverage_apply]
  simp_rw [continuumNumerator_add]
  have e0 : continuumNumerator (1, 0) p =
      Complex.exp (Complex.I * (p.1 : ℂ)) := by
    simp [continuumNumerator, continuumPhase]
  have em0 : continuumNumerator (-1, 0) p =
      Complex.exp (-(Complex.I * (p.1 : ℂ))) := by
    simp [continuumNumerator, continuumPhase]
  have e1 : continuumNumerator (0, 1) p =
      Complex.exp (Complex.I * (p.2 : ℂ)) := by
    simp [continuumNumerator, continuumPhase]
  have em1 : continuumNumerator (0, -1) p =
      Complex.exp (-(Complex.I * (p.2 : ℂ))) := by
    simp [continuumNumerator, continuumPhase]
  rw [e0, em0, e1, em1]
  have hcos0 : Complex.exp (Complex.I * (p.1 : ℂ)) +
      Complex.exp (-(Complex.I * (p.1 : ℂ))) =
        (2 : ℂ) * (Real.cos p.1 : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using exp_pair_eq_two_cos p.1
  have hcos1 : Complex.exp (Complex.I * (p.2 : ℂ)) +
      Complex.exp (-(Complex.I * (p.2 : ℂ))) =
        (2 : ℂ) * (Real.cos p.2 : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using exp_pair_eq_two_cos p.2
  unfold Scont ScontReal
  push_cast
  simp only [← Complex.ofReal_cos]
  linear_combination (continuumNumerator x p / 5) * hcos0 +
    (continuumNumerator x p / 5) * hcos1

/-- Pointwise `(1-ξ S∞)` cancellation of the actual Fourier integrand. -/
theorem KinfIntegrand_sub_latticeFiveAverage (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) (p : ℝ × ℝ) :
    KinfIntegrand ξ x p -
      ξ * latticeFiveAverage (fun y => KinfIntegrand ξ y p) x =
        continuumNumerator x p := by
  have hD : Dcont ξ p ≠ 0 := Dcont_ne_zero ξ hξ p
  have hAvg : latticeFiveAverage (fun y => KinfIntegrand ξ y p) x =
      latticeFiveAverage (fun y => continuumNumerator y p) x / Dcont ξ p := by
    rw [latticeFiveAverage_apply, latticeFiveAverage_apply]
    simp only [KinfIntegrand]
    ring
  rw [hAvg, latticeFiveAverage_continuumNumerator]
  unfold KinfIntegrand
  field_simp [hD]
  unfold Dcont
  ring

/-- The finite stencil passes through the two interval integrals defining
`Kinf`; all five integrands already have the required inner and outer
integrability. -/
theorem integral_latticeFiveAverage_KinfIntegrand (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) :
    (∫ p₁ : ℝ in -Real.pi..Real.pi,
      ∫ p₂ : ℝ in -Real.pi..Real.pi,
        latticeFiveAverage (fun y => KinfIntegrand ξ y (p₁, p₂)) x) =
      latticeFiveAverage
        (fun y => ∫ p₁ : ℝ in -Real.pi..Real.pi,
          ∫ p₂ : ℝ in -Real.pi..Real.pi, KinfIntegrand ξ y (p₁, p₂)) x := by
  have hinner (p₁ : ℝ) :
      (∫ p₂ : ℝ in -Real.pi..Real.pi,
        latticeFiveAverage (fun y => KinfIntegrand ξ y (p₁, p₂)) x) =
        (1 / 5 : ℂ) * ∑ δ ∈ latticeFivePoint,
          ∫ p₂ : ℝ in -Real.pi..Real.pi,
            KinfIntegrand ξ (x + δ) (p₁, p₂) := by
    simp only [latticeFiveAverage]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun δ hδ =>
        Kinf_inner_intervalIntegrable ξ hξ (x + δ) p₁)]
  calc
    (∫ p₁ : ℝ in -Real.pi..Real.pi,
      ∫ p₂ : ℝ in -Real.pi..Real.pi,
        latticeFiveAverage (fun y => KinfIntegrand ξ y (p₁, p₂)) x)
        = ∫ p₁ : ℝ in -Real.pi..Real.pi,
            (1 / 5 : ℂ) * ∑ δ ∈ latticeFivePoint,
              ∫ p₂ : ℝ in -Real.pi..Real.pi,
                KinfIntegrand ξ (x + δ) (p₁, p₂) := by
                  apply intervalIntegral.integral_congr
                  intro p₁ hp₁
                  exact hinner p₁
    _ = latticeFiveAverage
        (fun y => ∫ p₁ : ℝ in -Real.pi..Real.pi,
          ∫ p₂ : ℝ in -Real.pi..Real.pi, KinfIntegrand ξ y (p₁, p₂)) x := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_finsetSum (fun δ hδ =>
              Kinf_outer_intervalIntegrable ξ hξ (x + δ))]
          rfl

/-- The same finite-sum interchange after the normalization defining `Kinf`. -/
theorem latticeFiveAverage_Kinf_eq_integral (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) :
    latticeFiveAverage (Kinf ξ) x =
      ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
        (∫ p₁ : ℝ in -Real.pi..Real.pi,
          ∫ p₂ : ℝ in -Real.pi..Real.pi,
            latticeFiveAverage (fun y => KinfIntegrand ξ y (p₁, p₂)) x) := by
  rw [integral_latticeFiveAverage_KinfIntegrand ξ hξ x]
  simp only [latticeFiveAverage, Kinf]
  rw [← Finset.mul_sum]
  ring

/-- The actual infinite-volume Fourier kernel solves the five-point lattice
resolvent equation. -/
theorem Kinf_sub_latticeFiveAverage (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) :
    Kinf ξ x - ξ * latticeFiveAverage (Kinf ξ) x = latticePointMass x := by
  have hinnerAvg (p₁ : ℝ) : IntervalIntegrable
      (fun p₂ : ℝ => latticeFiveAverage
        (fun y => KinfIntegrand ξ y (p₁, p₂)) x)
      volume (-Real.pi) Real.pi := by
    have hsum : IntervalIntegrable
        (fun p₂ : ℝ => ∑ δ ∈ latticeFivePoint,
          KinfIntegrand ξ (x + δ) (p₁, p₂))
        volume (-Real.pi) Real.pi :=
      IntervalIntegrable.sum latticeFivePoint
        (fun δ hδ => Kinf_inner_intervalIntegrable ξ hξ (x + δ) p₁)
    simpa only [latticeFiveAverage] using hsum.const_mul (1 / 5 : ℂ)
  have houterAvg : IntervalIntegrable
      (fun p₁ : ℝ => ∫ p₂ : ℝ in -Real.pi..Real.pi,
        latticeFiveAverage (fun y => KinfIntegrand ξ y (p₁, p₂)) x)
      volume (-Real.pi) Real.pi := by
    have hsum : IntervalIntegrable
        (fun p₁ : ℝ => ∑ δ ∈ latticeFivePoint,
          ∫ p₂ : ℝ in -Real.pi..Real.pi,
            KinfIntegrand ξ (x + δ) (p₁, p₂))
        volume (-Real.pi) Real.pi :=
      IntervalIntegrable.sum latticeFivePoint
        (fun δ hδ => Kinf_outer_intervalIntegrable ξ hξ (x + δ))
    have hscaled := hsum.const_mul (1 / 5 : ℂ)
    convert hscaled using 1
    funext p₁
    simp only [latticeFiveAverage]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun δ hδ =>
        Kinf_inner_intervalIntegrable ξ hξ (x + δ) p₁)]
  have hinnerResidual (p₁ : ℝ) :
      (∫ p₂ : ℝ in -Real.pi..Real.pi,
        (KinfIntegrand ξ x (p₁, p₂) -
          ξ * latticeFiveAverage
            (fun y => KinfIntegrand ξ y (p₁, p₂)) x)) =
        (∫ p₂ : ℝ in -Real.pi..Real.pi,
          KinfIntegrand ξ x (p₁, p₂)) -
          ξ * (∫ p₂ : ℝ in -Real.pi..Real.pi,
            latticeFiveAverage
              (fun y => KinfIntegrand ξ y (p₁, p₂)) x) := by
    rw [intervalIntegral.integral_sub
      (Kinf_inner_intervalIntegrable ξ hξ x p₁)
      ((hinnerAvg p₁).const_mul ξ), intervalIntegral.integral_const_mul]
  have houterResidual :
      (∫ p₁ : ℝ in -Real.pi..Real.pi,
        ∫ p₂ : ℝ in -Real.pi..Real.pi,
          (KinfIntegrand ξ x (p₁, p₂) -
            ξ * latticeFiveAverage
              (fun y => KinfIntegrand ξ y (p₁, p₂)) x)) =
        (∫ p₁ : ℝ in -Real.pi..Real.pi,
          ∫ p₂ : ℝ in -Real.pi..Real.pi,
            KinfIntegrand ξ x (p₁, p₂)) -
          ξ * (∫ p₁ : ℝ in -Real.pi..Real.pi,
            ∫ p₂ : ℝ in -Real.pi..Real.pi,
              latticeFiveAverage
                (fun y => KinfIntegrand ξ y (p₁, p₂)) x) := by
    simp_rw [hinnerResidual]
    rw [intervalIntegral.integral_sub
      (Kinf_outer_intervalIntegrable ξ hξ x)
      (houterAvg.const_mul ξ), intervalIntegral.integral_const_mul]
  calc
    Kinf ξ x - ξ * latticeFiveAverage (Kinf ξ) x =
        ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
          ((∫ p₁ : ℝ in -Real.pi..Real.pi,
            ∫ p₂ : ℝ in -Real.pi..Real.pi,
              KinfIntegrand ξ x (p₁, p₂)) -
            ξ * (∫ p₁ : ℝ in -Real.pi..Real.pi,
              ∫ p₂ : ℝ in -Real.pi..Real.pi,
                latticeFiveAverage
                  (fun y => KinfIntegrand ξ y (p₁, p₂)) x)) := by
          rw [Kinf, latticeFiveAverage_Kinf_eq_integral ξ hξ x]
          ring
    _ = ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
          (∫ p₁ : ℝ in -Real.pi..Real.pi,
            ∫ p₂ : ℝ in -Real.pi..Real.pi,
              (KinfIntegrand ξ x (p₁, p₂) -
                ξ * latticeFiveAverage
                  (fun y => KinfIntegrand ξ y (p₁, p₂)) x)) := by
          rw [houterResidual]
    _ = ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
          (∫ p₁ : ℝ in -Real.pi..Real.pi,
            ∫ p₂ : ℝ in -Real.pi..Real.pi,
              continuumNumerator x (p₁, p₂)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro p₁ hp₁
          apply intervalIntegral.integral_congr
          intro p₂ hp₂
          exact KinfIntegrand_sub_latticeFiveAverage ξ hξ x (p₁, p₂)
    _ = latticePointMass x := normalized_integral_continuumNumerator x

/-- A nonzero pointwise probe at `ξ=0`, `x=0`, `p=0`. -/
example : KinfIntegrand 0 (0, 0) (0, 0) -
    0 * latticeFiveAverage (fun y => KinfIntegrand 0 y (0, 0)) (0, 0) = 1 := by
  simpa [continuumNumerator, continuumPhase] using
    KinfIntegrand_sub_latticeFiveAverage 0 (by norm_num) (0, 0) (0, 0)

/-- The actual kernel has unit lattice resolvent mass at the origin. -/
example : Kinf 0 (0, 0) -
    0 * latticeFiveAverage (Kinf 0) (0, 0) = 1 := by
  simpa [latticePointMass] using Kinf_sub_latticeFiveAverage 0 (by norm_num) (0, 0)

example : Kinf 0 (1, 0) -
    0 * latticeFiveAverage (Kinf 0) (1, 0) = 0 := by
  simpa [latticePointMass] using Kinf_sub_latticeFiveAverage 0 (by norm_num) (1, 0)

end RBM
