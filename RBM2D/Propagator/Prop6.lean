/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.DerivBounds
import RBM2D.Propagator.ZeroMode
import RBM2D.Propagator.ShellCutoff
import RBM2D.Propagator.ShellKernelFD

/-!
# Property 6 of `lem_propTH`: `(prop:BD1)` and `(prop:BD2)`

The shell kernels `shellKernel L ξ j`,
`j = 0, …, shellCount L`, together with the zero mode `L⁻² (1 - ξ)⁻¹`, decompose
`Θ_ξ` (first sentence of §8.3, with the smooth partition of unity
`shellCutoff_partition`).  This gives a `DyadicDecomp L ξ` witness with constant
`C₀ = 10 ^ 14` (`exists_dyadicDecomp`), and `norm_Theta_fd_all_le_paper`
turns it into property 6, in explicit form (`norm_Theta_fd_prop6`).

Both statements hold for every `‖ξ‖ < 1`, not only for the three spectral
parameters `t m², t m̄², t |m|²` of the paper; the dyadic cutoff is a function of
the smooth periodic variable `t(p) = (5/8) q(p)` rather than of `|p|_*`.
-/

namespace RBM

open Finset Filter

/-- The `theta_eq` field of `DyadicDecomp` for the shell kernels: the zero mode
plus the sum of the `shellCount L + 1` shell kernels is `Θ_ξ`. -/
theorem Theta_eq_zeroMode_add_shellKernel :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ u : Z2 L,
    Theta L ξ u 0 = ((L : ℂ) ^ 2)⁻¹ * (1 - ξ)⁻¹ +
      ∑ j ∈ Finset.range (shellCount L + 1), shellKernel L ξ j u := by
  intro L _ hL ξ hξ u
  obtain ⟨hzero, hpart⟩ := shellCutoff_partition L hL
  rw [Theta_apply_eq_zero_mode_add L hL hξ u 0, sub_zero]
  congr 1
  simp only [shellKernel]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  have hfull :
      ∑ p : Z2 L, ∑ j ∈ Finset.range (shellCount L + 1),
          (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * chr L p u
        = ∑ p ∈ Finset.univ.erase (0 : Z2 L), ∑ j ∈ Finset.range (shellCount L + 1),
          (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * chr L p u := by
    refine (Finset.sum_erase _ ?_).symm
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hzero j]
  rw [hfull]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, hpart p hp0,
    Complex.ofReal_one, one_mul, invSymbolMultiplier, div_eq_mul_inv, mul_comm]

/-- The witness: a `DyadicDecomp L ξ` built from the shell kernels, with
the numeral constant `C₀ = 10 ^ 14`. -/
theorem exists_dyadicDecomp :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 →
    ∃ H : DyadicDecomp L ξ,
      H.J = shellCount L ∧ H.Kr = shellKernel L ξ ∧ H.C = 10 ^ 14 := by
  intro L _ hL ξ hξ
  exact ⟨{ J := shellCount L, Kr := shellKernel L ξ, C := 10 ^ 14,
            C_nonneg := by positivity,
            theta_eq := Theta_eq_zeroMode_add_shellKernel L hL ξ hξ,
            fd1 := fun u s hs j _ => shellKernel_fd1 L hL ξ hξ u s hs j,
            fd2 := fun u s hs j _ => shellKernel_fd2 L hL ξ hξ u s hs j }, rfl, rfl, rfl⟩

/-- **Property 6** (`(prop:BD1)`, `(prop:BD2)`), explicit form: every `3 ≤ L`,
every `‖ξ‖ < 1`, every `a, b, s`, with prefactor
`derivativePrefactor (10 ^ 14) L = 8 · 10 ^ 14 + 720 (1 + log L)`. -/
theorem norm_Theta_fd_prop6 :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ a b s : Z2 L,
    ‖Theta L ξ a b - Theta L ξ a (b + s)‖
        ≤ derivativePrefactor (10 ^ 14) L *
          ((zdist2 L s : ℝ) * ((zdist2 L (a - b) : ℝ) + 1)⁻¹ +
            (zdist2 L s : ℝ) * (kappa ξ * (ellhat L ξ) ^ 2)⁻¹)
      ∧
    ‖2 * Theta L ξ a b - Theta L ξ a (b + s) - Theta L ξ a (b - s)‖
        ≤ derivativePrefactor (10 ^ 14) L *
          ((zdist2 L s : ℝ) ^ 2 * ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹ +
            (zdist2 L s : ℝ) ^ 2 * ((ellhat L ξ) ^ 2)⁻¹) := by
  intro L _ hL ξ hξ a b s
  obtain ⟨H, -, -, hC⟩ := exists_dyadicDecomp L hL ξ hξ
  exact norm_Theta_fd_all_le_paper H (10 ^ 14) hC.le hL hξ a b s

end RBM
