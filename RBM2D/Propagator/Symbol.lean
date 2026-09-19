/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The Fourier representation of `Θ^(B)_ξ` on `Z_L^2`

Formalization of Section 8.1 of the paper ("Fourier setup"), equations
`(eq_symbol)` and `(eq_Fourier_rep)`.

The paper indexes frequencies by `p ∈ T_L^2 = ((2π/L) Z_L)^2` and writes the
Fourier symbol of `S^(B)` as `Ŝ(p) = (1 + 2 cos p₁ + 2 cos p₂)/5`.  Here a
frequency is `p : Z_L^2`, standing for `(2π p₁/L, 2π p₂/L)`, and the plane wave
`x ↦ exp(i p · x)` is `RBM.chr p x`.

## Main definitions

* `RBM.Shat`          : the symbol `Ŝ(p)`, equation `(eq_symbol)`
* `RBM.chr`           : the plane wave `e_p(x) = exp(i p · x)`
* `RBM.fourierKernel` : `K_{ξ,L}(x) = (1/L²) ∑_p exp(i p·x) / (1 - ξ Ŝ(p))`

## Main results

* `RBM.Shat_eq_cos`              : `Ŝ(p) = (1 + 2 cos p₁ + 2 cos p₂)/5`, the paper's form
* `RBM.SB_mulVec_char`           : plane waves are eigenvectors of `S^(B)` with eigenvalue `Ŝ(p)`
* `RBM.one_sub_mul_Shat_ne_zero` : `1 - ξ Ŝ(p) ≠ 0` for `‖ξ‖ < 1`
* `RBM.Theta_apply_fourier`      : `(eq_Fourier_rep)`
-/

namespace RBM

open Matrix Finset

variable (L : ℕ) [NeZero L]

section Symbol

/-- The Fourier symbol of `S^(B)` at frequency `(2πp₁/L, 2πp₂/L)`, equation
`(eq_symbol)`: `Ŝ(p) = (1 + e^{ip₁} + e^{-ip₁} + e^{ip₂} + e^{-ip₂})/5`. -/
noncomputable def Shat (p : Z2 L) : ℂ :=
  (1 + (ZMod.stdAddChar p.1 + ZMod.stdAddChar (-p.1))
     + (ZMod.stdAddChar p.2 + ZMod.stdAddChar (-p.2))) / 5

/-- `e^{ip} + e^{-ip} = 2 cos p`, the one-dimensional ingredient of
`Shat_eq_cos`. -/
theorem stdAddChar_add_neg (p : ZMod L) :
    (ZMod.stdAddChar p : ℂ) + (ZMod.stdAddChar (-p) : ℂ)
      = ((2 * Real.cos (2 * Real.pi * p.val / L) : ℝ) : ℂ) := by
  have h := Complex.two_cos (2 * Real.pi * p.val / L)
  have e₁ : 2 * (Real.pi : ℂ) * Complex.I * (p.val : ℂ) / (L : ℂ)
      = 2 * Real.pi * p.val / L * Complex.I := by ring
  have e₂ : -(2 * (Real.pi : ℂ) * p.val / L * Complex.I)
      = -(2 * Real.pi * p.val / L) * Complex.I := by ring
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ZMod.toCircle_apply,
    ← Complex.exp_neg, e₁, e₂]
  push_cast
  rw [h]
  ring

/-- The symbol in the form written in `(eq_symbol)`:
`Ŝ(p) = (1 + 2 cos p₁ + 2 cos p₂)/5`.  In particular `Ŝ(p)` is real. -/
theorem Shat_eq_cos (p : Z2 L) :
    Shat L p = (((1 + 2 * Real.cos (2 * Real.pi * p.1.val / L)
        + 2 * Real.cos (2 * Real.pi * p.2.val / L)) / 5 : ℝ) : ℂ) := by
  rw [Shat, stdAddChar_add_neg L p.1, stdAddChar_add_neg L p.2]
  push_cast
  ring

theorem Shat_neg (p : Z2 L) : Shat L (-p) = Shat L p := by
  rw [Shat, Shat]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_neg]
  ring

theorem norm_Shat_le_one (p : Z2 L) : ‖Shat L p‖ ≤ 1 := by
  rw [Shat, norm_div]
  have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
  rw [h5, div_le_one (by norm_num)]
  have hb : ∀ q : ZMod L,
      ‖(ZMod.stdAddChar q : ℂ) + (ZMod.stdAddChar (-q) : ℂ)‖ ≤ 2 := by
    intro q
    calc ‖(ZMod.stdAddChar q : ℂ) + (ZMod.stdAddChar (-q) : ℂ)‖
        ≤ ‖(ZMod.stdAddChar q : ℂ)‖ + ‖(ZMod.stdAddChar (-q) : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [AddChar.norm_apply, AddChar.norm_apply]; norm_num
  calc ‖1 + (ZMod.stdAddChar p.1 + ZMod.stdAddChar (-p.1))
          + (ZMod.stdAddChar p.2 + ZMod.stdAddChar (-p.2))‖
      ≤ ‖(1 : ℂ)‖ + ‖(ZMod.stdAddChar p.1 : ℂ) + (ZMod.stdAddChar (-p.1) : ℂ)‖
        + ‖(ZMod.stdAddChar p.2 : ℂ) + (ZMod.stdAddChar (-p.2) : ℂ)‖ := norm_add₃_le
    _ ≤ 1 + 2 + 2 := by
        have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
        have h2 := hb p.1
        have h3 := hb p.2
        linarith
    _ = 5 := by norm_num

/-- For `‖ξ‖ < 1` the Fourier multiplier `1 - ξ Ŝ(p)` never vanishes. -/
theorem one_sub_mul_Shat_ne_zero {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    1 - ξ * Shat L p ≠ 0 := by
  intro h
  have h1 : ξ * Shat L p = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖ξ * Shat L p‖ < 1 := by
    rw [norm_mul]
    calc ‖ξ‖ * ‖Shat L p‖ ≤ ‖ξ‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_Shat_le_one L p) (norm_nonneg ξ)
      _ < 1 := by rwa [mul_one]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

end Symbol

section Plane

/-- The plane wave `e_p(x) = exp(i p · x)` on `Z_L^2`. -/
noncomputable def chr (p u : Z2 L) : ℂ := ZMod.stdAddChar (p.1 * u.1 + p.2 * u.2)

theorem chr_add_e1 (p x : Z2 L) :
    chr L p (x + (1, 0)) = chr L p x * ZMod.stdAddChar p.1 := by
  simp only [chr, Prod.fst_add, Prod.snd_add]
  rw [show p.1 * (x.1 + 1) + p.2 * (x.2 + 0) = (p.1 * x.1 + p.2 * x.2) + p.1 by ring,
    AddChar.map_add_eq_mul]

theorem chr_sub_e1 (p x : Z2 L) :
    chr L p (x - (1, 0)) = chr L p x * ZMod.stdAddChar (-p.1) := by
  simp only [chr, Prod.fst_sub, Prod.snd_sub]
  rw [show p.1 * (x.1 - 1) + p.2 * (x.2 - 0) = (p.1 * x.1 + p.2 * x.2) + -p.1 by ring,
    AddChar.map_add_eq_mul]

theorem chr_add_e2 (p x : Z2 L) :
    chr L p (x + (0, 1)) = chr L p x * ZMod.stdAddChar p.2 := by
  simp only [chr, Prod.fst_add, Prod.snd_add]
  rw [show p.1 * (x.1 + 0) + p.2 * (x.2 + 1) = (p.1 * x.1 + p.2 * x.2) + p.2 by ring,
    AddChar.map_add_eq_mul]

theorem chr_sub_e2 (p x : Z2 L) :
    chr L p (x - (0, 1)) = chr L p x * ZMod.stdAddChar (-p.2) := by
  simp only [chr, Prod.fst_sub, Prod.snd_sub]
  rw [show p.1 * (x.1 - 0) + p.2 * (x.2 - 1) = (p.1 * x.1 + p.2 * x.2) + -p.2 by ring,
    AddChar.map_add_eq_mul]

/-- Orthogonality of characters in one dimension: `(1/L) ∑_p exp(ipu) = δ_{u,0}`. -/
theorem inv_mul_sum_stdAddChar (u : ZMod L) :
    (L : ℂ)⁻¹ * ∑ p : ZMod L, ZMod.stdAddChar (p * u) = if u = 0 then 1 else 0 := by
  rw [AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar L), ZMod.card]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  split_ifs <;> simp [hL]

/-- Orthogonality of characters on `Z_L^2`: `(1/L²) ∑_p exp(i p·u) = δ_{u,0}`. -/
theorem inv_mul_sum_chr (u : Z2 L) :
    ((L : ℂ) ^ 2)⁻¹ * ∑ p : Z2 L, chr L p u = if u = 0 then 1 else 0 := by
  have hsum : ∑ p : Z2 L, chr L p u
      = (∑ p₁ : ZMod L, (ZMod.stdAddChar (p₁ * u.1) : ℂ))
        * (∑ p₂ : ZMod L, (ZMod.stdAddChar (p₂ * u.2) : ℂ)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
    rw [chr, AddChar.map_add_eq_mul]
  rw [hsum, show ((L : ℂ) ^ 2)⁻¹ = (L : ℂ)⁻¹ * (L : ℂ)⁻¹ by rw [sq, mul_inv],
    mul_mul_mul_comm, inv_mul_sum_stdAddChar L u.1, inv_mul_sum_stdAddChar L u.2]
  by_cases h1 : u.1 = 0 <;> by_cases h2 : u.2 = 0
  · have hu : u = 0 := Prod.ext_iff.mpr ⟨h1, h2⟩
    simp [h1, h2, hu]
  · have hu : u ≠ 0 := fun h => h2 (by rw [h]; rfl)
    simp [h1, h2, hu]
  · have hu : u ≠ 0 := fun h => h1 (by rw [h]; rfl)
    simp [h1, h2, hu]
  · have hu : u ≠ 0 := fun h => h1 (by rw [h]; rfl)
    simp [h1, h2, hu]

end Plane

section Eigen

/-- `S^(B)` averages over the five lattice points of the nearest-neighbour
support. -/
theorem SB_mulVec_apply (hL : 3 ≤ L) (v : Z2 L → ℂ) (x : Z2 L) :
    (SB L *ᵥ v) x
      = (v x + v (x - (1, 0)) + v (x + (1, 0)) + v (x - (0, 1)) + v (x + (0, 1))) / 5 := by
  have e0 : x - ((0 : ZMod L), (0 : ZMod L)) = x := by
    rw [show ((0 : ZMod L), (0 : ZMod L)) = (0 : Z2 L) from rfl, sub_zero]
  have e1 : x - ((-1 : ZMod L), (0 : ZMod L)) = x + ((1 : ZMod L), (0 : ZMod L)) := by
    rw [show ((-1 : ZMod L), (0 : ZMod L)) = -((1 : ZMod L), (0 : ZMod L)) from by
      rw [Prod.neg_mk, neg_zero], sub_neg_eq_add]
  have e2 : x - ((0 : ZMod L), (-1 : ZMod L)) = x + ((0 : ZMod L), (1 : ZMod L)) := by
    rw [show ((0 : ZMod L), (-1 : ZMod L)) = -((0 : ZMod L), (1 : ZMod L)) from by
      rw [Prod.neg_mk, neg_zero], sub_neg_eq_add]
  have hsplit : ∀ u : Z2 L, sbKernel L u * v (x - u)
      = if u ∈ sbSupport L then (5 : ℂ)⁻¹ * v (x - u) else 0 := by
    intro u
    rw [sbKernel]
    split_ifs <;> ring
  simp only [mulVec, dotProduct, SB_apply]
  rw [← Equiv.sum_comp (Equiv.subLeft x)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, hsplit]
  rw [Finset.sum_ite_mem, Finset.univ_inter, sum_over_sbSupport L hL, e0, e1, e2]
  ring

/-- The plane wave `e_p` is an eigenvector of `S^(B)` with eigenvalue `Ŝ(p)`. -/
theorem SB_mulVec_char (hL : 3 ≤ L) (p : Z2 L) :
    SB L *ᵥ (fun x => chr L p x) = Shat L p • fun x => chr L p x := by
  funext x
  rw [SB_mulVec_apply L hL, chr_sub_e1, chr_add_e1, chr_sub_e2, chr_add_e2, Pi.smul_apply,
    smul_eq_mul, Shat]
  ring

end Eigen

section Fourier

/-- The kernel of `(eq_Fourier_rep)`:
`K_{ξ,L}(u) = (1/L²) ∑_p exp(i p·u) / (1 - ξ Ŝ(p))`. -/
noncomputable def fourierKernel (ξ : ℂ) (u : Z2 L) : ℂ :=
  ((L : ℂ) ^ 2)⁻¹ * ∑ p : Z2 L, chr L p u / (1 - ξ * Shat L p)

/-- The Fourier kernel solves `K - ξ S^(B) K = δ_0`. -/
theorem fourierKernel_sub_SB_mulVec (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (u : Z2 L) :
    fourierKernel L ξ u - ξ * (SB L *ᵥ fourierKernel L ξ) u = if u = 0 then 1 else 0 := by
  rw [SB_mulVec_apply L hL, ← inv_mul_sum_chr L u]
  simp only [fourierKernel, chr_sub_e1, chr_add_e1, chr_sub_e2, chr_add_e2]
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hD := one_sub_mul_Shat_ne_zero L hξ p
  set C := chr L p u with hC
  set D := 1 - ξ * Shat L p with hDdef
  have key : C / D
      - ξ * ((C / D + C * ZMod.stdAddChar (-p.1) / D + C * ZMod.stdAddChar p.1 / D
              + C * ZMod.stdAddChar (-p.2) / D + C * ZMod.stdAddChar p.2 / D) / 5)
      = C / D * D := by
    rw [hDdef, Shat]
    ring
  calc _ = ((L : ℂ) ^ 2)⁻¹ * (C / D
        - ξ * ((C / D + C * ZMod.stdAddChar (-p.1) / D + C * ZMod.stdAddChar p.1 / D
              + C * ZMod.stdAddChar (-p.2) / D + C * ZMod.stdAddChar p.2 / D) / 5)) := by
        ring
    _ = _ := by rw [key, div_mul_cancel₀ _ hD]

/-- `(eq_Fourier_rep)`, matrix form: `Θ^(B)_ξ` is the circulant matrix on `Z_L^2`
generated by the Fourier kernel `K_{ξ,L}`. -/
theorem Theta_eq_circulant_fourierKernel (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta L ξ = circulant (fourierKernel L ξ) := by
  refine (eq_Theta_of_mul L hL hξ ?_).symm
  have hmul : circulant (fourierKernel L ξ) * SB L
      = circulant (SB L *ᵥ fourierKernel L ξ) := by
    rw [SB, circulant_mul_comm, circulant_mul]
  rw [mul_sub, mul_one, Matrix.mul_smul, hmul, ← circulant_smul, ← circulant_sub,
    ← circulant_single_one ℂ (Z2 L), circulant_inj]
  funext u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  exact fourierKernel_sub_SB_mulVec L hL hξ u

/-- **(eq_Fourier_rep)**:
`(Θ^(B)_ξ)_{ab} = (1/L²) ∑_p exp(i p·(a-b)) / (1 - ξ Ŝ(p))`. -/
theorem Theta_apply_fourier (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L ξ a b
      = ((L : ℂ) ^ 2)⁻¹ * ∑ p : Z2 L, chr L p (a - b) / (1 - ξ * Shat L p) := by
  rw [Theta_eq_circulant_fourierKernel L hL hξ, circulant_apply, fourierKernel]

end Fourier

end RBM
