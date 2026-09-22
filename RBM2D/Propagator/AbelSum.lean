/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Momentum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Periodic summation by parts on the two-dimensional torus

The reindexing identities have no boundary terms because `Z2 L` is a finite
additive group. The character estimates relate the phase loss under a unit
translation to graph distance in the dual coordinate.
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- Periodic summation by parts in an arbitrary direction on `Z_L²`. -/
theorem sum_fwdDiff_mul (f g : Z2 L → ℂ) (e : Z2 L) :
    ∑ p : Z2 L, (f (p + e) - f p) * g p =
      -(∑ p : Z2 L, f p * (g p - g (p - e))) := by
  have hreindex : (∑ p : Z2 L, f (p + e) * g p) =
      ∑ p : Z2 L, f p * g (p - e) := by
    exact Fintype.sum_equiv (Equiv.addRight e) _ _ (fun p => by simp)
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hreindex]
  abel

/-- The exact squared phase loss for one Fourier coordinate. -/
theorem norm_stdAddChar_sub_one_sq (p : ZMod L) :
    ‖(ZMod.stdAddChar p : ℂ) - 1‖ ^ 2 =
      2 * (1 - Real.cos (pstar L p)) := by
  let θ : ℝ := 2 * Real.pi * (p.val : ℝ) / (L : ℝ)
  have hchar : (ZMod.stdAddChar p : ℂ) = Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    simp only [θ]
    push_cast
    ring
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hnorm : ‖(2 * Real.sin (θ / 2) : ℝ)‖ ^ 2 =
      4 * Real.sin (θ / 2) ^ 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (2 * Real.sin (θ / 2))]
  rw [hnorm]
  have hcos := Real.cos_two_mul' (θ / 2)
  have htrig := Real.sin_sq_add_cos_sq (θ / 2)
  have hθ : 2 * (θ / 2) = θ := by ring
  rw [hθ] at hcos
  rw [← cos_eq_cos_pstar L p]
  change 4 * Real.sin (θ / 2) ^ 2 = 2 * (1 - Real.cos θ)
  nlinarith

/-- The phase loss is bounded above by the periodic angular distance. -/
theorem norm_stdAddChar_sub_one_le_pstar (p : ZMod L) :
    ‖(ZMod.stdAddChar p : ℂ) - 1‖ ≤ pstar L p := by
  have hs := norm_stdAddChar_sub_one_sq L p
  have hc := one_sub_cos_le_sq (pstar L p)
  have hp := pstar_nonneg L p
  nlinarith [norm_nonneg ((ZMod.stdAddChar p : ℂ) - 1)]

/-- Jordan's lower bound on the half-angle, expressed as phase loss. -/
theorem two_div_pi_mul_pstar_le_norm_stdAddChar_sub_one (p : ZMod L) :
    2 / Real.pi * pstar L p ≤ ‖(ZMod.stdAddChar p : ℂ) - 1‖ := by
  have hs := norm_stdAddChar_sub_one_sq L p
  have hc := sq_le_one_sub_cos (abs_pstar_le_pi L p)
  have hp := pstar_nonneg L p
  have hpi := Real.pi_pos
  have hpisq : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hpi)
  have htarget : (2 / Real.pi * pstar L p) ^ 2 ≤
      ‖(ZMod.stdAddChar p : ℂ) - 1‖ ^ 2 := by
    rw [hs]
    calc
      (2 / Real.pi * pstar L p) ^ 2 =
          2 * (2 / Real.pi ^ 2 * pstar L p ^ 2) := by field_simp
      _ ≤ 2 * (1 - Real.cos (pstar L p)) := by linarith
  nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpi.le,
    norm_nonneg ((ZMod.stdAddChar p : ℂ) - 1)]

/-- Quantitative upper bound in units of graph distance on the frequency cycle. -/
theorem norm_stdAddChar_sub_one_le_zdist (p : ZMod L) :
    ‖(ZMod.stdAddChar p : ℂ) - 1‖ ≤
      2 * Real.pi * (zdist L p : ℝ) / (L : ℝ) := by
  simpa only [pstar] using norm_stdAddChar_sub_one_le_pstar L p

/-- Quantitative lower bound in units of graph distance on the frequency cycle. -/
theorem zdist_le_norm_stdAddChar_sub_one (p : ZMod L) :
    4 * (zdist L p : ℝ) / (L : ℝ) ≤
      ‖(ZMod.stdAddChar p : ℂ) - 1‖ := by
  convert two_div_pi_mul_pstar_le_norm_stdAddChar_sub_one L p using 1
  simp only [pstar]
  field_simp
  ring

theorem chr_e1 (p : Z2 L) :
    chr L p (1, 0) = ZMod.stdAddChar p.1 := by
  simp [chr]

theorem chr_e2 (p : Z2 L) :
    chr L p (0, 1) = ZMod.stdAddChar p.2 := by
  simp [chr]

/-- Character loss in the first coordinate, with explicit graph-distance constants. -/
theorem chr_e1_distance_bounds (p : Z2 L) :
    4 * (zdist L p.1 : ℝ) / (L : ℝ) ≤ ‖chr L p (1, 0) - 1‖ ∧
      ‖chr L p (1, 0) - 1‖ ≤
        2 * Real.pi * (zdist L p.1 : ℝ) / (L : ℝ) := by
  rw [chr_e1]
  exact ⟨zdist_le_norm_stdAddChar_sub_one L p.1,
    norm_stdAddChar_sub_one_le_zdist L p.1⟩

/-- Character loss in the second coordinate, with explicit graph-distance constants. -/
theorem chr_e2_distance_bounds (p : Z2 L) :
    4 * (zdist L p.2 : ℝ) / (L : ℝ) ≤ ‖chr L p (0, 1) - 1‖ ∧
      ‖chr L p (0, 1) - 1‖ ≤
        2 * Real.pi * (zdist L p.2 : ℝ) / (L : ℝ) := by
  rw [chr_e2]
  exact ⟨zdist_le_norm_stdAddChar_sub_one L p.2,
    norm_stdAddChar_sub_one_le_zdist L p.2⟩

end RBM
