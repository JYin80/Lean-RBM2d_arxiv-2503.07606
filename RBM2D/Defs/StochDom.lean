/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Domination
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Stochastic domination `≺` along admissible sequences

Formalization of the two-dimensional random band matrix paper, Definition 2.1 (i).

**Convention.**  The probability space `(Ω, P)` is fixed, and the dependence on the size is
carried by the random variables: a family is `ξ : ∀ l, U l → Ω → ℝ`, with `U l` the (possibly
`l`-dependent) parameter set.  The paper assumes the compared variables are non-negative; the
predicate below is defined on real-valued families so that it can be used directly for the
moment and matrix statements.  The intended `P` is a probability measure; the definition allows
any measure.

Here the matrix dimension is `size l`, an admissible sequence of dimensions such as
`size l = W(l)² l²`; nothing is asserted about natural numbers that are not of this form.
The deterministic `UnifDetDom` in `Defs/Domination.lean` uses the block side length `L`
instead.

## Main definitions

* `badSetAt size ξ ζ τ l` : the failure event `∃ u, ξ l u > (size l)^τ ζ l u`.
* `StochDomAt size ξ ζ` : Definition 2.1(i) along the dimensions `size l`: for all `τ > 0` and
  `D > 0`, eventually in `l`, `P(badSetAt size ξ ζ τ l) ≤ (size l)^{-D}`.  The union over
  `u : U l` sits inside the probability, as in the paper.

## Auxiliary facts

* `eventually_two_mul_rpow_le` : `2 N^{-(D+1)} ≤ N^{-D}` eventually.
* `rpow_mul_rpow_neg_add` : `N^C N^{-(D+C)} = N^{-D}`.
-/

namespace RBM

open Filter MeasureTheory

section Arith

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem eventually_two_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 2 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (2 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN2
    _ = _ := mul_one _

/-- `N^C N^{-(D+C)} = N^{-D}`. -/
theorem rpow_mul_rpow_neg_add {N : ℕ} (hN : 1 ≤ N) (C D : ℝ) :
    (N : ℝ) ^ C * (N : ℝ) ^ (-(D + C)) = (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add hN0]; congr 1; ring

end Arith

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

section Defs

variable {U : ℕ → Type*}

/-- The failure event for a sequence indexed by `l` whose matrix dimension is `size l`.
This permits the paper's admissible dimensions `size l = W(l)² l²` without
pretending that all natural numbers are admissible dimensions. -/
def badSetAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) (τ : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∃ u, (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}

/-- Definition 2.1(i) along an admissible sequence of matrix dimensions `size l`.
The cutoff is uniform in `u : U l` and both the threshold and failure rate use `size l`. -/
def StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
    P (badSetAt size ξ ζ τ l) ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

end Defs

end RBM
