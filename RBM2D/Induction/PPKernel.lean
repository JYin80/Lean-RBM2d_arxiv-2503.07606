/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.PPVocab
import RBM2D.Propagator.Prop5
import RBM2D.Loop.LatticeCount
import RBM2D.Path.Kernel
import RBM2D.Gauss.SpectralAlgebra

/-!
# The `(+,+)` slot-kernel row bound `ppKernelN`

The result is the statement `PPKernelN` (`RBM2D.Induction.PPVocab`), proved verbatim, with no
hypothesis added:

`theorem ppKernelN (κ : ℝ) : PPKernelN κ`.

Paper: arXiv:2503.07606, Section 5: `def_Ustz`; Section 3: `prop:ThfadC` (property 5, as
`norm_Theta_apply_le_prop5`, `RBM2D.Propagator.Prop5`).  The argument parallels the
one-dimensional formalization: the row-sum identity `𝒰 = 1 + (w - v) m² S Θ_{w m²}` and the
lattice sum of the exponential of property 5 over `Z_L²` (for `d = 2` this replaces the `d = 1`
short-edge bound).  The row-sum bound of `Θ_ξ` is the `hΘ` of `Green.stable_svar_bulk`
(`RBM2D.Green.Stability`), whose private gap lemmas (`gapK_le_norm`) are re-proved here under the
prefix `ppk_`.

Layout: 1. the bulk gap `gapK κ ≤ ‖1 - t m²‖`; 2. the row sums of `Θ_{t m²}`; 3. the row-sum
identity of `𝒰` and its `ℓ¹` bound; 4. the theorem `ppKernelN`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open Matrix RBM

/-! ## 1. The bulk gap `gapK κ ≤ ‖1 - t m²‖` (re-proved; the other copies are `private`) -/

section Gap

private theorem ppk_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < KLoop.gapK κ := by
  unfold KLoop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem ppk_gapK_le_one (κ : ℝ) : KLoop.gapK κ ≤ 1 := min_le_left _ _

private theorem ppk_gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    KLoop.gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ KLoop.gapK κ := (ppk_gapK_pos hκ hκ2).le
  have h1 : KLoop.gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem ppk_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * Gauss.spectralM E ^ 2‖ ^ 2 = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him := Gauss.spectralM_im E
  have hs := Gauss.spectralM_sqrt_sq hE
  rw [pow_two (Gauss.spectralM E), Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- The bulk gap: `gapK κ ≤ |1 - t m²|` for `t ≥ 0` and `|E| ≤ 2 - κ`. -/
private theorem ppk_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) :
    KLoop.gapK κ ≤ ‖1 - (t : ℂ) * Gauss.spectralM E ^ 2‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : KLoop.gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * Gauss.spectralM E ^ 2‖ ^ 2 := by
    rw [ppk_norm_one_sub_sq hE2]
    have hg1 : KLoop.gapK κ ^ 2 ≤ 1 := by
      have := ppk_gapK_le_one κ
      have := (ppk_gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := ppk_gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have := (ppk_gapK_pos hκ hκ2).le
  have := norm_nonneg (1 - (t : ℂ) * Gauss.spectralM E ^ 2)
  nlinarith

end Gap

/-! ## 2. The row sums of `Θ_{t m²}` -/

section ThetaRow

/-- The constant `A0(κ) = cΘ / gapK κ · (1 + 40000 / √(gapK κ))²`, `cΘ = 180·40002²`
(property 5). -/
private def ppkA0 (κ : ℝ) : ℝ :=
  180 * 40002 ^ 2 / KLoop.gapK κ * (1 + 40000 / Real.sqrt (KLoop.gapK κ)) ^ 2

private theorem ppkA0_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < ppkA0 κ := by
  have hc0 : 0 < KLoop.gapK κ := ppk_gapK_pos hκ hκ2
  unfold ppkA0
  positivity

/-- **Row sums of `Θ_{t m²}`**: `∑_b |Θ_{t m²}(a,b)| ≤ A0(κ) (1 + log L)`, uniformly in
`t ∈ [0, 1)`, `|E| ≤ 2 - κ`, `L ≥ 3`; property 5 (`norm_Theta_apply_le_prop5`), the gap
`gapK κ ≤ |1 - t m²|` and the exponential sum `KLoop.sum_exp_le`
(the `hΘ` of `Green.stable_svar_bulk`). -/
private theorem ppk_theta_row_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {κ E t : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Z2 L) :
    ∑ b : Z2 L, ‖Theta L ((t : ℂ) * Gauss.spectralM E ^ 2) a b‖ ≤
      ppkA0 κ * (1 + Real.log (L : ℝ)) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  set c := KLoop.gapK κ with hc
  have hc0 : 0 < c := ppk_gapK_pos hκ hκ2
  have hc1 : c ≤ 1 := ppk_gapK_le_one κ
  set ξ : ℂ := (t : ℂ) * Gauss.spectralM E ^ 2 with hξdef
  have hξ : ‖ξ‖ < 1 := by
    rw [hξdef, norm_mul, norm_pow, Gauss.norm_spectralM hE2, Complex.norm_real,
      Real.norm_of_nonneg ht0, one_pow, mul_one]
    exact ht1
  have hgap : c ≤ ‖(1 : ℂ) - ξ‖ := ppk_gapK_le_norm hκ hE ht0
  have hk2 : c ≤ kappa ξ ^ 2 := by rw [kappa_sq]; exact hgap
  have hkpos : 0 < kappa ξ := kappa_pos hξ
  have hℓpos : 0 < ellhat L ξ := ellhat_pos L hL hξ
  have hkl : c ≤ kappa ξ ^ 2 * ellhat L ξ ^ 2 := by
    unfold ellhat
    rcases le_total (kappa ξ)⁻¹ (L : ℝ) with h | h
    · rw [min_eq_left h]
      have : kappa ξ ^ 2 * ((kappa ξ)⁻¹) ^ 2 = 1 := by field_simp
      rw [this]; exact hc1
    · rw [min_eq_right h]
      have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
      have h1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      calc c = c * 1 := by ring
        _ ≤ kappa ξ ^ 2 * (L : ℝ) ^ 2 := mul_le_mul hk2 h1 zero_le_one (by positivity)
  have hℓ_le : ellhat L ξ ≤ (Real.sqrt c)⁻¹ := by
    have h1 : ellhat L ξ ≤ (kappa ξ)⁻¹ := min_le_left _ _
    have h2 : Real.sqrt c ≤ kappa ξ := by
      unfold kappa
      exact Real.sqrt_le_sqrt hgap
    exact h1.trans (inv_anti₀ (Real.sqrt_pos.2 hc0) h2)
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have h1log : 0 ≤ 1 + Real.log (L : ℝ) := by linarith
  set s : ℝ := (20000 * ellhat L ξ)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 (by positivity)
  have hexp := KLoop.sum_exp_le L s hs0 a
  have h2s : 1 + 2 / s = 1 + 40000 * ellhat L ξ := by
    rw [hs]; field_simp; ring
  have hinv : (kappa ξ ^ 2 * ellhat L ξ ^ 2)⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hkl
  have hℓ40 : 1 + 40000 * ellhat L ξ ≤ 1 + 40000 / Real.sqrt c := by
    have := mul_le_mul_of_nonneg_left hℓ_le (by norm_num : (0 : ℝ) ≤ 40000)
    rw [div_eq_mul_inv]; linarith
  have hsq : (1 + 40000 * ellhat L ξ) ^ 2 ≤ (1 + 40000 / Real.sqrt c) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hℓ40 2
  have hX : 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * (kappa ξ ^ 2 * ellhat L ξ ^ 2)⁻¹ *
      (1 + 40000 * ellhat L ξ) ^ 2 ≤
      180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hsq (by positivity)
      (by positivity)
  have hK : ppkA0 κ * (1 + Real.log (L : ℝ)) =
      180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 := by
    unfold ppkA0
    rw [← hc]
    ring
  calc ∑ b : Z2 L, ‖Theta L ξ a b‖
      ≤ ∑ b : Z2 L, (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) *
          (kappa ξ ^ 2 * ellhat L ξ ^ 2)⁻¹) * Real.exp (-(s * (zdist2 L (a - b) : ℝ))) :=
        Finset.sum_le_sum fun b _ => by
          have h := norm_Theta_apply_le_prop5 L hL ξ hξ a b
          have hh : -(zdist2 L (a - b) : ℝ) / (20000 * ellhat L ξ) =
              -(s * (zdist2 L (a - b) : ℝ)) := by
            rw [hs]; ring
          rw [hh] at h
          exact h
    _ = (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * (kappa ξ ^ 2 * ellhat L ξ ^ 2)⁻¹) *
          ∑ b : Z2 L, Real.exp (-(s * (zdist2 L (a - b) : ℝ))) := by
        rw [← Finset.mul_sum]
    _ ≤ (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * (kappa ξ ^ 2 * ellhat L ξ ^ 2)⁻¹) *
          (1 + 2 / s) ^ 2 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ ppkA0 κ * (1 + Real.log (L : ℝ)) := by
        rw [h2s, hK]
        exact hX

end ThetaRow

/-! ## 3. The row-sum identity `𝒰 = 1 + (w - v) ξ S Θ_{wξ}` and its `ℓ¹` bound -/

section RowIdentity

/-- **The row-sum identity**: `(1 - vξ S) Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}` for `‖wξ‖ < 1`
(`1 - vξ S = (1 - wξ S) + (w - v) ξ S` and `(1 - wξ S) Θ_{wξ} = 1`). -/
private theorem ppk_ukerMat_eq {L : ℕ} [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    Path.ukerMat L ξ v w =
      1 + (((w : ℂ) - (v : ℂ)) * ξ) • (SB L * Theta L ((w : ℂ) * ξ)) := by
  have h1 := mul_Theta L hL hw
  unfold Path.ukerMat
  have h2 : (1 : Matrix (Z2 L) (Z2 L) ℂ) - ((v : ℂ) * ξ) • SB L =
      (1 - ((w : ℂ) * ξ) • SB L) + (((w : ℂ) - (v : ℂ)) * ξ) • SB L := by
    rw [sub_mul, sub_smul]; abel
  rw [h2, add_mul, h1, smul_mul_assoc]

/-- **The `ℓ¹` row bound**: if every row of `Θ_{wξ}` has `ℓ¹` norm `≤ R`, then every row of
`𝒰_{v,w} = (1 - vξ S) Θ_{wξ}` has `ℓ¹` norm `≤ 1 + R` (`|w - v| ≤ 1`, `|ξ| ≤ 1`, `S` stochastic). -/
private theorem ppk_row_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} {v w R : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) (hξ : ‖ξ‖ ≤ 1)
    (hR : ∀ a : Z2 L, ∑ b : Z2 L, ‖Theta L ((w : ℂ) * ξ) a b‖ ≤ R) (x : Z2 L) :
    ∑ y : Z2 L, ‖Path.ukerMat L ξ v w x y‖ ≤ 1 + R := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hwξ : ‖(w : ℂ) * ξ‖ < 1 := by
    rw [norm_mul, Complex.norm_of_nonneg hw0]
    calc w * ‖ξ‖ ≤ w * 1 := mul_le_mul_of_nonneg_left hξ hw0
      _ = w := mul_one w
      _ < 1 := hw1
  have hid := ppk_ukerMat_eq (L := L) hL (ξ := ξ) (v := v) (w := w) hwξ
  set c : ℝ := ‖((w : ℂ) - (v : ℂ)) * ξ‖ with hcdef
  have hc1 : c ≤ 1 := by
    rw [hcdef, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc (w - v) * ‖ξ‖ ≤ (w - v) * 1 := mul_le_mul_of_nonneg_left hξ (by linarith)
      _ ≤ 1 := by linarith
  have hc0 : 0 ≤ c := norm_nonneg _
  have hS1 : ∑ z : Z2 L, ‖SB L x z‖ = 1 := by
    have := congrArg (fun r : NNReal => (r : ℝ)) (sum_nnnorm_SB_row L hL x)
    simpa [NNReal.coe_sum] using this
  have hentry : ∀ y : Z2 L, ‖Path.ukerMat L ξ v w x y‖ ≤
      ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ +
        c * ∑ z : Z2 L, ‖SB L x z‖ * ‖Theta L ((w : ℂ) * ξ) z y‖ := by
    intro y
    rw [hid, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add le_rfl ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    refine (norm_sum_le _ _).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun z _ => ?_)
    rw [norm_mul]
  have h1 : ∑ y : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ = 1 := by
    simp [Matrix.one_apply, apply_ite]
  have h2 : ∑ y : Z2 L, ∑ z : Z2 L, ‖SB L x z‖ * ‖Theta L ((w : ℂ) * ξ) z y‖ ≤ R := by
    rw [Finset.sum_comm]
    calc ∑ z : Z2 L, ∑ y : Z2 L, ‖SB L x z‖ * ‖Theta L ((w : ℂ) * ξ) z y‖
        = ∑ z : Z2 L, ‖SB L x z‖ * ∑ y : Z2 L, ‖Theta L ((w : ℂ) * ξ) z y‖ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ z : Z2 L, ‖SB L x z‖ * R :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hR z) (norm_nonneg _)
      _ = R := by rw [← Finset.sum_mul, hS1, one_mul]
  have hR0 : 0 ≤ R := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hR x)
  calc ∑ y : Z2 L, ‖Path.ukerMat L ξ v w x y‖
      ≤ ∑ y : Z2 L, (‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ +
          c * ∑ z : Z2 L, ‖SB L x z‖ * ‖Theta L ((w : ℂ) * ξ) z y‖) :=
        Finset.sum_le_sum fun y _ => hentry y
    _ = ∑ y : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ +
          c * ∑ y : Z2 L, ∑ z : Z2 L, ‖SB L x z‖ * ‖Theta L ((w : ℂ) * ξ) z y‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 1 + 1 * R := by
        rw [h1]
        exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left h2 hc0).trans
          (mul_le_mul_of_nonneg_right hc1 hR0))
    _ = 1 + R := by rw [one_mul]

end RowIdentity

/-! ## 4. The theorem `ppKernelN` -/

section Main

/-- `m(true) m(true) = m²` where `m = spectralM E`. -/
private theorem ppk_mSig_sq (E : ℝ) :
    KLoop.mSig E true * KLoop.mSig E true = Gauss.spectralM E ^ 2 := by
  simp [KLoop.mSig, sq]

/-- **`ppKernelN`** (the statement `PPKernelN`, proved verbatim): every row of the `(+,+)` slot kernel `𝒰 = (1 - v m² S) Θ_{w m²}` has `ℓ¹` norm
`≤ 1 + A0 (1 + log L)`, uniformly in `L ≥ 3`, `0 ≤ v ≤ w < 1` and `|E| ≤ 2 - κ`, with
`A0 = A0(κ) = 180·40002² gapK⁻¹ (1 + 40000/√gapK)²` (`gapK = gapK κ`; `A0 = 1` for `κ > 2`, where
the energy hypothesis is void). -/
theorem ppKernelN (κ : ℝ) : PPKernelN κ := by
  intro hκ
  by_cases hκ2 : κ ≤ 2
  · refine ⟨ppkA0 κ, ppkA0_pos hκ hκ2, ?_⟩
    intro L _ hL E hE v w hv0 hvw hw1 x
    have hw0 : 0 ≤ w := hv0.trans hvw
    have hE2 : |E| ≤ 2 := by linarith
    rw [ppk_mSig_sq]
    have hξ : ‖Gauss.spectralM E ^ 2‖ ≤ 1 := by
      rw [norm_pow, Gauss.norm_spectralM hE2]; norm_num
    have hrow := ppk_row_le (L := L) hL (ξ := Gauss.spectralM E ^ 2) (v := v) (w := w)
      (R := ppkA0 κ * (1 + Real.log (L : ℝ))) hv0 hvw hw1 hξ
      (fun a => ppk_theta_row_le hL hκ hE hw0 hw1 a) x
    unfold CUN
    exact hrow
  · refine ⟨1, one_pos, ?_⟩
    intro L _ hL E hE
    exfalso
    push Not at hκ2
    linarith [abs_nonneg E]

end Main

end RBM.Ind
