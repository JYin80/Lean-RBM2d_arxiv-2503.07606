/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Momentum
import RBM2D.Propagator.LogIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuous Fourier symbol and infinite-volume kernel

This is the continuous counterpart of the finite-torus symbol in Section 8.2.
On the fundamental square `[-π,π]²`, the paper's periodic norm `|p|_*²`
equals `p.1² + p.2²`.
-/

namespace RBM

open Real MeasureTheory intervalIntegral

/-- The real Fourier symbol `(1+2 cos p₁+2 cos p₂)/5`, equation `(eq_symbol)`. -/
noncomputable def ScontReal (p : ℝ × ℝ) : ℝ :=
  (1 + 2 * Real.cos p.1 + 2 * Real.cos p.2) / 5

/-- The symbol embedded in `ℂ`, to match the torus multiplier's type. -/
noncomputable def Scont (p : ℝ × ℝ) : ℂ := (ScontReal p : ℂ)

/-- `q(p)=1-Ŝ(p)`, equation `(eq_qdef)`. -/
noncomputable def qcont (p : ℝ × ℝ) : ℝ :=
  (2 / 5 : ℝ) * ((1 - Real.cos p.1) + (1 - Real.cos p.2))

/-- Squared Euclidean momentum on the fundamental square. -/
def pnorm2 (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

theorem one_sub_ScontReal_eq_qcont (p : ℝ × ℝ) :
    1 - ScontReal p = qcont p := by
  unfold ScontReal qcont
  ring

theorem ScontReal_bounds (p : ℝ × ℝ) :
    -(3 / 5 : ℝ) ≤ ScontReal p ∧ ScontReal p ≤ 1 := by
  have h₁ := Real.neg_one_le_cos p.1
  have h₂ := Real.neg_one_le_cos p.2
  have h₃ := Real.cos_le_one p.1
  have h₄ := Real.cos_le_one p.2
  unfold ScontReal
  constructor <;> linarith

theorem qcont_nonneg (p : ℝ × ℝ) : 0 ≤ qcont p := by
  rw [← one_sub_ScontReal_eq_qcont]
  exact sub_nonneg.mpr (ScontReal_bounds p).2

theorem qcont_le (p : ℝ × ℝ) : qcont p ≤ 8 / 5 := by
  rw [← one_sub_ScontReal_eq_qcont]
  linarith [(ScontReal_bounds p).1]

/-- The upper half of `q(p) ≍ |p|_*²`, globally on `ℝ²`. -/
theorem qcont_le_pnorm2 (p : ℝ × ℝ) :
    qcont p ≤ (1 / 5 : ℝ) * pnorm2 p := by
  have h₁ := one_sub_cos_le_sq p.1
  have h₂ := one_sub_cos_le_sq p.2
  unfold qcont pnorm2
  nlinarith

/-- The lower half of `q(p) ≍ |p|_*²` on the fundamental square. -/
theorem pnorm2_le_qcont (p : ℝ × ℝ)
    (h₁ : |p.1| ≤ Real.pi) (h₂ : |p.2| ≤ Real.pi) :
    (4 / (5 * Real.pi ^ 2)) * pnorm2 p ≤ qcont p := by
  have hp₁ := sq_le_one_sub_cos h₁
  have hp₂ := sq_le_one_sub_cos h₂
  have hsum : (2 / Real.pi ^ 2) * (p.1 ^ 2 + p.2 ^ 2) ≤
      (1 - Real.cos p.1) + (1 - Real.cos p.2) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2 / 5)
  unfold qcont pnorm2
  convert hscale using 1; ring

/-- The continuous denominator `1-ξŜ(p)`. -/
noncomputable def Dcont (ξ : ℂ) (p : ℝ × ℝ) : ℂ := 1 - ξ * Scont p

/-- Upper ellipticity bound, valid without a restriction on `ξ`. -/
theorem norm_Dcont_le (ξ : ℂ) (p : ℝ × ℝ) :
    ‖Dcont ξ p‖ ≤ (kappa ξ) ^ 2 + qcont p := by
  have h := norm_one_sub_mul_real_le (ξ := ξ) (lam := ScontReal p)
    (ScontReal_bounds p).1 (ScontReal_bounds p).2
  rw [← one_sub_ScontReal_eq_qcont, kappa_sq]
  simpa only [Dcont, Scont, add_comm] using h

/-- Lower ellipticity bound in terms of the continuous symbol. -/
theorem norm_Dcont_ge (ξ : ℂ) (hξ : ‖ξ‖ < 1) (p : ℝ × ℝ) :
    (1 / 9 : ℝ) * ((kappa ξ) ^ 2 + qcont p) ≤ ‖Dcont ξ p‖ := by
  have h := norm_one_sub_mul_real_ge (ξ := ξ) (lam := ScontReal p) hξ
    (ScontReal_bounds p).1 (ScontReal_bounds p).2
  rw [← one_sub_ScontReal_eq_qcont, kappa_sq]
  simpa only [Dcont, Scont, add_comm] using h

/-- The upper half of `(eq_elliptic)` on `[-π,π]²`. -/
theorem norm_Dcont_le_pnorm2 (ξ : ℂ) (p : ℝ × ℝ) :
    ‖Dcont ξ p‖ ≤ (kappa ξ) ^ 2 + pnorm2 p := by
  have hq := qcont_le_pnorm2 p
  have hp : 0 ≤ pnorm2 p := by unfold pnorm2; positivity
  calc
    ‖Dcont ξ p‖ ≤ (kappa ξ) ^ 2 + qcont p := norm_Dcont_le ξ p
    _ ≤ (kappa ξ) ^ 2 + (1 / 5 : ℝ) * pnorm2 p := by
      simpa only [add_comm] using add_le_add_left hq ((kappa ξ) ^ 2)
    _ ≤ (kappa ξ) ^ 2 + pnorm2 p := by nlinarith

/-- The lower half of `(eq_elliptic)` on the fundamental square. -/
theorem norm_Dcont_ge_pnorm2 (ξ : ℂ) (hξ : ‖ξ‖ < 1) (p : ℝ × ℝ)
    (h₁ : |p.1| ≤ Real.pi) (h₂ : |p.2| ≤ Real.pi) :
    (4 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + pnorm2 p) ≤
      ‖Dcont ξ p‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : (4 / (5 * Real.pi ^ 2) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi ^ 2)).2
    nlinarith [Real.pi_gt_three]
  have hq := pnorm2_le_qcont p h₁ h₂
  have hk : 0 ≤ (kappa ξ) ^ 2 := sq_nonneg _
  have hsum : (4 / (5 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + pnorm2 p) ≤
      (kappa ξ) ^ 2 + qcont p := by
    nlinarith [mul_le_mul_of_nonneg_right hc hk]
  calc
    (4 / (45 * Real.pi ^ 2)) * ((kappa ξ) ^ 2 + pnorm2 p)
        = (1 / 9 : ℝ) * ((4 / (5 * Real.pi ^ 2)) *
          ((kappa ξ) ^ 2 + pnorm2 p)) := by ring
    _ ≤ (1 / 9 : ℝ) * ((kappa ξ) ^ 2 + qcont p) := by gcongr
    _ ≤ ‖Dcont ξ p‖ := norm_Dcont_ge ξ hξ p

theorem Dcont_ne_zero (ξ : ℂ) (hξ : ‖ξ‖ < 1) (p : ℝ × ℝ) :
    Dcont ξ p ≠ 0 := by
  have hk : 0 < kappa ξ := kappa_pos hξ
  have hq : 0 ≤ qcont p := qcont_nonneg p
  have hge := norm_Dcont_ge ξ hξ p
  intro hz
  rw [hz, norm_zero] at hge
  have hpos : (0 : ℝ) < (1 / 9) * ((kappa ξ) ^ 2 + qcont p) := by positivity
  linarith

theorem continuous_ScontReal : Continuous ScontReal := by
  unfold ScontReal
  fun_prop

theorem continuous_Scont : Continuous Scont := by
  exact Complex.continuous_ofReal.comp continuous_ScontReal

theorem continuous_Dcont (ξ : ℂ) : Continuous (Dcont ξ) := by
  unfold Dcont
  exact continuous_const.sub (continuous_const.mul continuous_Scont)

/-- The real phase `p·x` for `x∈ℤ²`. -/
def continuumPhase (x : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (x.1 : ℝ) + p.2 * (x.2 : ℝ)

/-- The numerator `exp(i p·x)` of `(eq_Kinf)`. -/
noncomputable def continuumNumerator (x : ℤ × ℤ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * (continuumPhase x p : ℂ))

theorem continuous_continuumNumerator (x : ℤ × ℤ) :
    Continuous (continuumNumerator x) := by
  unfold continuumNumerator continuumPhase
  fun_prop

theorem norm_continuumNumerator (x : ℤ × ℤ) (p : ℝ × ℝ) :
    ‖continuumNumerator x p‖ = 1 := by
  simp [continuumNumerator, Complex.norm_exp, Complex.mul_re]

/-- The integrand of the infinite-volume Fourier kernel. -/
noncomputable def KinfIntegrand (ξ : ℂ) (x : ℤ × ℤ) (p : ℝ × ℝ) : ℂ :=
  continuumNumerator x p / Dcont ξ p

theorem continuous_KinfIntegrand (ξ : ℂ) (hξ : ‖ξ‖ < 1) (x : ℤ × ℤ) :
    Continuous (KinfIntegrand ξ x) := by
  unfold KinfIntegrand
  exact (continuous_continuumNumerator x).div (continuous_Dcont ξ)
    (Dcont_ne_zero ξ hξ)

/-- Genuine Lebesgue integrability of the Fourier integrand on the compact square. -/
theorem KinfIntegrand_integrableOn (ξ : ℂ) (hξ : ‖ξ‖ < 1) (x : ℤ × ℤ) :
    IntegrableOn (KinfIntegrand ξ x)
      (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi)
      (volume.prod volume) :=
  ((continuous_KinfIntegrand ξ hξ x).continuousOn).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

theorem Kinf_inner_intervalIntegrable (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) (p₁ : ℝ) :
    IntervalIntegrable (fun p₂ : ℝ => KinfIntegrand ξ x (p₁, p₂))
      volume (-Real.pi) Real.pi := by
  have hc : Continuous fun p₂ : ℝ => KinfIntegrand ξ x (p₁, p₂) :=
    (continuous_KinfIntegrand ξ hξ x).comp (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable _ _

/-- Fubini's theorem makes the outer integral in `Kinf` a genuine Bochner integral. -/
theorem Kinf_outer_intervalIntegrable (ξ : ℂ) (hξ : ‖ξ‖ < 1)
    (x : ℤ × ℤ) :
    IntervalIntegrable
      (fun p₁ : ℝ => ∫ p₂ : ℝ in -Real.pi..Real.pi,
        KinfIntegrand ξ x (p₁, p₂)) volume (-Real.pi) Real.pi := by
  let A : Set ℝ := Set.Icc (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℂ := KinfIntegrand ξ x
  have hProd : Integrable f ((volume.restrict A).prod (volume.restrict A)) := by
    rw [Measure.prod_restrict]
    exact KinfIntegrand_integrableOn ξ hξ x
  have hOuter := hProd.integral_prod_left
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have heq (p₁ : ℝ) :
      (∫ p₂ : ℝ, f (p₁, p₂) ∂(volume.restrict A)) =
        ∫ p₂ : ℝ in -Real.pi..Real.pi, f (p₁, p₂) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ]
  have hOuter' : Integrable
      (fun p₁ : ℝ => ∫ p₂ : ℝ in -Real.pi..Real.pi, f (p₁, p₂))
      (volume.restrict A) := by
    convert hOuter using 1
    funext p₁
    exact (heq p₁).symm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hπ).2 hOuter'

/-- `K_{ξ,∞}(x)` from `(eq_Kinf)`, written as an iterated integral as in §8.2. -/
noncomputable def Kinf (ξ : ℂ) (x : ℤ × ℤ) : ℂ :=
  ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
    ∫ p₁ : ℝ in -Real.pi..Real.pi,
      ∫ p₂ : ℝ in -Real.pi..Real.pi,
        KinfIntegrand ξ x (p₁, p₂)

/-- The iterated definition agrees with the genuine two-dimensional Lebesgue integral. -/
theorem Kinf_eq_square_integral (ξ : ℂ) (hξ : ‖ξ‖ < 1) (x : ℤ × ℤ) :
    Kinf ξ x = ((2 * (Real.pi : ℂ)) ^ 2)⁻¹ *
      ∫ p : ℝ × ℝ in Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi,
        KinfIntegrand ξ x p ∂(volume.prod volume) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [setIntegral_prod (KinfIntegrand ξ x) (KinfIntegrand_integrableOn ξ hξ x)]
  simp_rw [integral_Icc_eq_integral_Ioc]
  simp_rw [← intervalIntegral.integral_of_le hπ]
  rfl

/-- At `ξ=0` and `x=0`, the Fourier integrand is the nonzero constant `1`. -/
theorem KinfIntegrand_zero_zero (p : ℝ × ℝ) :
    KinfIntegrand 0 (0, 0) p = 1 := by
  simp [KinfIntegrand, continuumNumerator, continuumPhase, Dcont]

/-- The normalization in `(eq_Kinf)` gives `K_{0,∞}(0)=1`. -/
theorem Kinf_zero_zero : Kinf 0 (0, 0) = 1 := by
  simp [Kinf, KinfIntegrand_zero_zero]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end RBM
