/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ContinuumSymbol
import RBM2D.Propagator.PeriodizeStencil

/-!
# Fourier inversion of the integer-lattice point mass

The normalized integral of the bare Fourier numerator over `[-π,π]²` is the
point mass at the origin. This is the Fourier-inversion endpoint of the
infinite-volume lattice resolvent equation, before the denominator and
five-point stencil are handled.
-/

namespace RBM

open Real intervalIntegral

/-- One-dimensional orthogonality of integer Fourier characters. -/
theorem integral_exp_int_periodize (w : ℤ) :
    ∫ p : ℝ in (-π)..π, Complex.exp (Complex.I * p * w)
      = if w = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hw
  · subst hw
    have h1 : ∀ p : ℝ, Complex.exp (Complex.I * p * ((0 : ℤ) : ℂ)) = 1 := by
      intro p
      simp
    simp_rw [h1]
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  · have hc : Complex.I * (w : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 hw)
    have e : ∀ p : ℝ,
        Complex.exp (Complex.I * p * w) = Complex.exp (Complex.I * w * p) := by
      intro p
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (Complex.I * w * (π : ℝ)) =
        Complex.exp (Complex.I * w * ((-π : ℝ) : ℂ)) := by
      have : Complex.I * w * (π : ℝ) =
          Complex.I * w * ((-π : ℝ) : ℂ) + w * (2 * π * Complex.I) := by
        push_cast
        ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

/-- The numerator factors into the two coordinate characters. -/
theorem continuumNumerator_factor (x : ℤ × ℤ) (p : ℝ × ℝ) :
    continuumNumerator x p =
      Complex.exp (Complex.I * p.1 * x.1) *
        Complex.exp (Complex.I * p.2 * x.2) := by
  unfold continuumNumerator continuumPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Two-dimensional orthogonality in the iterated-integral convention of
`Kinf`. -/
theorem integral_continuumNumerator (x : ℤ × ℤ) :
    (∫ p₁ : ℝ in -π..π,
      ∫ p₂ : ℝ in -π..π, continuumNumerator x (p₁, p₂)) =
        (if x.1 = 0 then ((2 * π : ℝ) : ℂ) else 0) *
          (if x.2 = 0 then ((2 * π : ℝ) : ℂ) else 0) := by
  simp_rw [continuumNumerator_factor]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [integral_exp_int_periodize]
  rw [intervalIntegral.integral_mul_const, integral_exp_int_periodize]

/-- Normalized two-dimensional Fourier inversion gives the lattice point mass. -/
theorem normalized_integral_continuumNumerator (x : ℤ × ℤ) :
    ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
      (∫ p₁ : ℝ in -Real.pi..Real.pi,
        ∫ p₂ : ℝ in -Real.pi..Real.pi, continuumNumerator x (p₁, p₂)) =
          latticePointMass x := by
  rw [integral_continuumNumerator]
  by_cases h₁ : x.1 = 0 <;> by_cases h₂ : x.2 = 0
  · have hx : x = 0 := Prod.ext_iff.mpr ⟨h₁, h₂⟩
    simp [latticePointMass, hx]
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  · have hx : x ≠ 0 := fun h => h₂ (by rw [h]; rfl)
    simp [h₁, h₂, latticePointMass, hx]
  · have hx : x ≠ 0 := fun h => h₁ (by rw [h]; rfl)
    simp [h₁, h₂, latticePointMass, hx]
  · have hx : x ≠ 0 := fun h => h₁ (by rw [h]; rfl)
    simp [h₁, h₂, latticePointMass, hx]

/-- The inversion theorem is nonzero at the origin. -/
example : ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
    (∫ p₁ : ℝ in -Real.pi..Real.pi,
      ∫ p₂ : ℝ in -Real.pi..Real.pi, continuumNumerator (0, 0) (p₁, p₂)) = 1 := by
  simpa [latticePointMass] using normalized_integral_continuumNumerator (0, 0)

example : ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
    (∫ p₁ : ℝ in -Real.pi..Real.pi,
      ∫ p₂ : ℝ in -Real.pi..Real.pi, continuumNumerator (1, 0) (p₁, p₂)) = 0 := by
  simpa [latticePointMass] using normalized_integral_continuumNumerator (1, 0)

end RBM
