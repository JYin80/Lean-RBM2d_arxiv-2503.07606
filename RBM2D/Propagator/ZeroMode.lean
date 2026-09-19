/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Symbol
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Separating the zero mode from `(eq_Fourier_rep)`

Sections 8.2 and 8.3 of the paper both open with the same manoeuvre: in

`K_{ξ,L}(u) = (1/L²) ∑_{p ∈ T_L²} exp(i p·u) / (1 - ξ Ŝ(p))`

the frequency `p = 0` contributes `L^{-2}(1-ξ)^{-1}`, because `Ŝ(0) = 1` and the
plane wave `e_0` is constant.  That term carries all of the `ξ → 1` singularity
and none of the `p`-dependence, so §8.2 pulls it out and estimates it separately,
while §8.3 works with a difference of two kernels, in which it cancels outright.

Proving it once here is what makes work orders T4 (`Propagator/Decay.lean`) and
T5 (`Propagator/FiniteDiff.lean`) file-disjoint: both consume this file and
neither re-derives it.

## Main results

* `RBM.Shat_zero`                    : `Ŝ(0) = 1`
* `RBM.chr_zero_left`                : `e_0(u) = 1`
* `RBM.Theta_apply_eq_zero_mode_add` : the split used by §8.2 (Property 5)
* `RBM.Theta_apply_sub_eq_erase_sum` : the cancellation used by §8.3 (Property 6)
* `RBM.norm_chr`                     : `‖e_p(u)‖ = 1`, the companion needed downstream

## Implementation notes

`Theta_apply_sub_eq_erase_sum` fixes the second index at `0`.  That is no loss:
translation invariance (`Theta_apply_add_right`, Property 2) already reduces the
general case to it, and pinning the index keeps the statement readable.
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section ZeroFrequency

/-- The symbol at the zero frequency: all five terms of `(eq_symbol)` are `1`,
so `Ŝ(0) = 5/5 = 1`. -/
@[simp]
theorem Shat_zero : Shat L (0 : Z2 L) = 1 := by
  rw [Shat]
  simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, AddChar.map_zero_eq_one]
  norm_num

/-- The zero frequency plane wave is constant: `e_0(u) = 1`. -/
@[simp]
theorem chr_zero_left (u : Z2 L) : chr L (0 : Z2 L) u = 1 := by
  rw [chr]
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, AddChar.map_zero_eq_one]

/-- The Fourier multiplier at the zero frequency is `1 - ξ`.  This is the factor
that blows up as `ξ → 1`, i.e. as `κ → 0`. -/
theorem one_sub_mul_Shat_zero (ξ : ℂ) :
    1 - ξ * Shat L (0 : Z2 L) = 1 - ξ := by
  rw [Shat_zero, mul_one]

end ZeroFrequency

section Norms

/-- Plane waves have modulus one.  `ZMod.stdAddChar` is `Circle.coeHom` composed
with `ZMod.toCircle`, so its values lie on the unit circle by construction. -/
@[simp]
theorem norm_chr (p u : Z2 L) : ‖chr L p u‖ = 1 := by
  rw [chr, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- A single Fourier term has modulus `‖1 - ξ Ŝ(p)‖⁻¹`: the numerator never
contributes.  This is what turns `(eq_elliptic)` into a bound on `K_{ξ,L}`. -/
theorem norm_chr_div_one_sub_mul_Shat (p u : Z2 L) (ξ : ℂ) :
    ‖chr L p u / (1 - ξ * Shat L p)‖ = ‖1 - ξ * Shat L p‖⁻¹ := by
  rw [norm_div, norm_chr, one_div]

/-- The crude bound used in §8.3: a difference of two plane waves at the same
frequency has modulus at most `2`.  No cancellation is claimed — Case 2 of
Property 6 is exactly the regime in which none is needed. -/
theorem norm_chr_sub_le (p u v : Z2 L) : ‖chr L p u - chr L p v‖ ≤ 2 := by
  calc ‖chr L p u - chr L p v‖ ≤ ‖chr L p u‖ + ‖chr L p v‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_chr, norm_chr]; norm_num

end Norms

section Split

/-- **Zero-mode separation**, the first step of §8.2.  In `(eq_Fourier_rep)` the
frequency `p = 0` contributes `L^{-2}(1-ξ)^{-1}`:

`(Θ_ξ)_{ab} = L^{-2}(1-ξ)^{-1} + L^{-2} ∑_{p ≠ 0} e_p(a-b)/(1 - ξ Ŝ(p))`.

The point of the split is that the first summand is the only place where the
singularity at `ξ = 1` lives; the remaining sum is controlled by ellipticity
alone, uniformly in `ξ`. -/
theorem Theta_apply_eq_zero_mode_add (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L ξ a b
      = ((L : ℂ) ^ 2)⁻¹ * (1 - ξ)⁻¹
        + ((L : ℂ) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.erase (0 : Z2 L),
            chr L p (a - b) / (1 - ξ * Shat L p) := by
  have hsplit :
      ∑ p : Z2 L, chr L p (a - b) / (1 - ξ * Shat L p)
        = chr L (0 : Z2 L) (a - b) / (1 - ξ * Shat L (0 : Z2 L))
          + ∑ p ∈ Finset.univ.erase (0 : Z2 L),
              chr L p (a - b) / (1 - ξ * Shat L p) :=
    (Finset.add_sum_erase _ (fun p => chr L p (a - b) / (1 - ξ * Shat L p))
      (Finset.mem_univ (0 : Z2 L))).symm
  rw [Theta_apply_fourier L hL hξ, hsplit, chr_zero_left, one_sub_mul_Shat_zero,
    one_div, mul_add]

/-- **Zero-mode cancellation**, the first step of §8.3.  In a difference of two
kernel values the constant term drops out, leaving a sum over `p ≠ 0` only:

`(Θ_ξ)_{u0} - (Θ_ξ)_{v0} = L^{-2} ∑_{p ≠ 0} (e_p(u) - e_p(v))/(1 - ξ Ŝ(p))`.

This is why Property 6 needs no information at all about the behaviour of
`(1-ξ)^{-1}`, and why Case 2 is elementary while Property 5 is not. -/
theorem Theta_apply_sub_eq_erase_sum (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (u v : Z2 L) :
    Theta L ξ u 0 - Theta L ξ v 0
      = ((L : ℂ) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.erase (0 : Z2 L),
          (chr L p u - chr L p v) / (1 - ξ * Shat L p) := by
  have hu := Theta_apply_eq_zero_mode_add L hL hξ u 0
  have hv := Theta_apply_eq_zero_mode_add L hL hξ v 0
  simp only [sub_zero] at hu hv
  rw [hu, hv]
  simp only [sub_div, Finset.sum_sub_distrib]
  ring

end Split

end RBM
