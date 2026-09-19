/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM2D.Defs.Domination

/-!
# The harmonic sum is `≺ 1`

Work order T16.  The lattice sum of Section 8.2 (`Propagator/LatticeSum.lean`,
work order T3) ends at

  `Σ_{p ≠ 0} |p|_*^{-2} ≤ (3/π²) L² Σ_{k=1}^{L} 1/k`,

and the paper then discards the last factor with the remark that "powers of
`log L` are harmless", i.e. `Σ_{k ≤ L} 1/k ≺ 1` in the sense of
Definition `stoch_domination` (ii).  This file proves exactly that statement and
nothing else: it mentions neither the lattice nor the propagator, which is why it
can be, and is, formalized independently of T2, T3 and T15.

## The two inputs

Mathlib already has the harmonic sum and its logarithmic bound
(`Mathlib/NumberTheory/Harmonic/Bounds.lean`), stated over `ℚ`:

  `harmonic n = ∑ i ∈ Finset.Icc 1 n, (i : ℚ)⁻¹`   (`harmonic_eq_sum_Icc`)
  `(harmonic n : ℝ) ≤ 1 + Real.log n`              (`harmonic_le_one_add_log`)

so the first step is only a cast, and we push it with the same three lemmas
Mathlib's own proof uses (`Rat.cast_sum`, `Rat.cast_inv`, `Rat.cast_natCast`).

The second input is that `log` is beaten by every positive power.  Rather than
hunting for a packaged version, we derive it in two lines from
`Real.log_le_sub_one_of_pos` applied to `x ^ τ`, combined with
`Real.log_rpow : log (x ^ y) = y * log x`.  Note the statement is kept
*multiplicative* — `τ * log x ≤ x ^ τ` rather than `log x ≤ x ^ τ / τ` — so that
no division lemma is needed anywhere downstream.

## Main results

* `RBM.mul_log_le_rpow`             : `τ * log x ≤ x ^ τ` for `x > 0`
* `RBM.sum_inv_Icc_le_one_add_log`  : `Σ_{k ∈ [1,n]} 1/k ≤ 1 + log n`, over `ℝ`
* `RBM.one_add_log_detDom_one`      : `1 + log L ≺ 1`
* `RBM.harmonic_detDom_one`         : `Σ_{k ∈ [1,L]} 1/k ≺ 1`  ← what T3 consumes
-/

namespace RBM

open Filter

/-! ### The logarithm is beaten by every positive power -/

/-- For `x > 0` and any real `τ`, `τ · log x ≤ x ^ τ`.

This is `log y ≤ y - 1` at `y = x ^ τ`, rewritten with `Real.log_rpow`.  Keeping
the `τ` on the left rather than dividing by it is deliberate: every use below is
a `calc` step in which the factor `τ` is carried along, so no field lemma and no
hypothesis `τ ≠ 0` is ever needed here. -/
theorem mul_log_le_rpow {x : ℝ} (hx : 0 < x) (τ : ℝ) : τ * Real.log x ≤ x ^ τ := by
  have hpos : (0 : ℝ) < x ^ τ := Real.rpow_pos_of_pos hx τ
  have h1 : Real.log (x ^ τ) ≤ x ^ τ - 1 := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_rpow hx] at h1
  linarith

/-! ### The harmonic sum over `ℝ` -/

/-- Mathlib's `harmonic_le_one_add_log`, transported from `ℚ` to `ℝ`.

The `simp` set is copied verbatim from the `simp_rw` line inside Mathlib's own
proof of `harmonic_le_one_add_log`, which is the cast route that is known to
work for this exact expression. -/
theorem sum_inv_Icc_le_one_add_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

/-- The harmonic sum is non-negative.  Needed because `DetDom`'s closure lemmas
take non-negativity of the dominating quantity as an explicit hypothesis. -/
theorem sum_inv_Icc_nonneg (n : ℕ) : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ :=
  Finset.sum_nonneg fun k _ => by positivity

/-- `1 + log n ≥ 0` for a natural `n`, including `n = 0` where `Real.log 0 = 0`. -/
theorem one_add_log_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 + Real.log n := by
  have := Real.log_natCast_nonneg n
  linarith

/-! ### The bridge to `≺` -/

/-- `1 + log L ≺ 1`.

Unwinding `DetDom`, given `τ > 0` we must eventually have
`1 + log L ≤ L^τ`.  Write `A = L^{τ/2}`, so that `A · A = L^τ`.  Two facts
suffice: `(τ/2) · log L ≤ A` (that is `mul_log_le_rpow`), and `A ≥ 1 + (τ/2)⁻¹`
eventually (that is `eventually_le_rpow`, the constant being allowed to depend on
`τ`).  Multiplying the goal by `τ/2 > 0` turns it into `τ/2 + A ≤ (τ/2)·A·A`,
which follows from `(τ/2)·A ≥ τ/2 + 1` multiplied by `A`. -/
theorem one_add_log_detDom_one : (fun L : ℕ => 1 + Real.log L) ≺ (fun _ => (1 : ℝ)) := by
  rw [detDom_iff]
  intro τ hτ
  have ht : 0 < τ / 2 := half_pos hτ
  filter_upwards [eventually_le_rpow (1 + (τ / 2)⁻¹) ht, eventually_ge_atTop 1]
    with L hC hL1
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hL1'
  have hA : (0 : ℝ) < (L : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hLpos (τ / 2)
  have hinv : (0 : ℝ) < (τ / 2)⁻¹ := inv_pos.mpr ht
  have hA1 : (1 : ℝ) ≤ (L : ℝ) ^ (τ / 2) := by linarith
  have hlog : (τ / 2) * Real.log L ≤ (L : ℝ) ^ (τ / 2) := mul_log_le_rpow hLpos (τ / 2)
  have hkey : (τ / 2) * (1 + (τ / 2)⁻¹) = τ / 2 + 1 := by
    rw [mul_add, mul_one, mul_inv_cancel₀ (ne_of_gt ht)]
  have hstep : τ / 2 + 1 ≤ (τ / 2) * (L : ℝ) ^ (τ / 2) := by
    calc τ / 2 + 1 = (τ / 2) * (1 + (τ / 2)⁻¹) := hkey.symm
      _ ≤ (τ / 2) * (L : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_left hC ht.le
  have hmain :
      (τ / 2) * (1 + Real.log L)
        ≤ (τ / 2) * ((L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2)) := by
    calc (τ / 2) * (1 + Real.log L) = τ / 2 + (τ / 2) * Real.log L := by ring
      _ ≤ τ / 2 + (L : ℝ) ^ (τ / 2) := by linarith
      _ ≤ (τ / 2) * (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) := by
          nlinarith [mul_le_mul_of_nonneg_right hstep hA.le]
      _ = (τ / 2) * ((L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2)) := by ring
  have hfinal : 1 + Real.log L ≤ (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) :=
    le_of_mul_le_mul_left hmain ht
  calc (1 : ℝ) + Real.log L
      ≤ (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) := hfinal
    _ = (L : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half L hτ
    _ = (L : ℝ) ^ τ * 1 := (mul_one _).symm

/-- `Σ_{k=1}^{L} 1/k ≺ 1`: the statement work order T3 consumes at the very end
of the lattice-sum estimate.  This is the Lean form of the paper's remark that
"powers of `log L` are harmless". -/
theorem harmonic_detDom_one :
    (fun L : ℕ => ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) ≺ (fun _ => (1 : ℝ)) := by
  rw [detDom_iff]
  intro τ hτ
  filter_upwards [detDom_iff.mp one_add_log_detDom_one τ hτ] with L hL
  calc ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹
      ≤ 1 + Real.log L := sum_inv_Icc_le_one_add_log L
    _ ≤ (L : ℝ) ^ τ * 1 := hL

end RBM
