/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.EntryCore
import RBM2D.Propagator.Prop5
import RBM2D.Loop.LatticeCount
import RBM2D.Loop.Kcal
import RBM2D.Induction.Defs
import RBM2D.Gauss.Model
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Gauss.SpectralWindow

/-!
# Stability of `1 - t m² S` for the `d = 2` variance profile

The `d = 2` analogue of the one-dimensional stability bound for the variance profile `svar` on
`Idx L W = Z_{WL}²`, together with the `d = 2` stability constant `Kstab2 κ L = O_κ(1 + log L)`.

* `RBM.Green.Kstab2`                       : the `d = 2` stability constant;
* `RBM.Green.stable_svar`                  : `Stable (svar L W) ξ (1 + KΘ)` from a row-sum
  bound `KΘ` on `Θ_ξ` (`S = S^{(B)} ⊗ S_W`, block size `W²`, `S_W = W⁻²`);
* `RBM.Green.stable_svar_bulk`             : `Stable (svar L W) (t m²) (Kstab2 κ L)` uniformly
  in `t ∈ [0, 1)`, `|E| ≤ 2 - κ` (via property 5, `norm_Theta_apply_le_prop5`, and
  the exponential sum `RBM.KLoop.sum_exp_le`);
* `RBM.Green.eventually_Kstab2_mul_rpow_le` : the absorption condition
  `Kstab2 κ L · W^{-c} ≤ 1/2`, eventually, under `SizeTendsto` and `Bandwidth`.
-/

namespace RBM.Green

open Matrix Finset Filter

/-- The d = 2 stability constant:
`1 + 2·cΘ/c_κ·(1 + 40000/√c_κ)²·(1 + log L)`, `cΘ = 180·40002²` (property 5),
`c_κ = gapK κ`.  In contrast with the one-dimensional `Kstab κ = O_κ(1)`, which rests on the
one-dimensional short-edge bound, it grows like `1 + log L`. -/
noncomputable def Kstab2 (κ : ℝ) (L : ℕ) : ℝ :=
  1 + 2 * (180 * 40002 ^ 2) / RBM.KLoop.gapK κ *
    (1 + 40000 / Real.sqrt (RBM.KLoop.gapK κ)) ^ 2 * (1 + Real.log L)

section StableSvar

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **`‖(1 - ξ S)⁻¹‖_{max→max} ≤ 1 + max_a ∑_b |(Θ_ξ)_{ab}|`** for the `d = 2` variance profile
`svar` on `Idx L W = Z_{WL}²`.  `S = S^(B) ⊗ S_W` acts on block averages only (blocks of `W²`
sites, `S_W = W⁻²`), so a solution of `v - ξ S v = r` has block averages `Θ_ξ r̃` and is
recovered from them up to `r` itself. -/
theorem stable_svar (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {KΘ : ℝ}
    (hΘ : ∀ a : Z2 L, ∑ b : Z2 L, ‖Theta L ξ a b‖ ≤ KΘ) :
    Stable (RBM.Gauss.svar L W) ξ (1 + KΘ) := by
  intro v B hB
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne W
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set e := splitEquiv L W with he
  obtain ⟨β, hβ⟩ : ∃ β : RBM.Gauss.Idx L W → Z2 L,
      ∀ i, β i = (blk L W i.1, blk L W i.2) := ⟨_, fun _ => rfl⟩
  have hb : ∀ x : BlockIndex L W, β (e.symm x) = x.1 := fun x => by
    rw [hβ]
    exact congrArg Prod.fst (e.apply_symm_apply x)
  have hsvar : ∀ i j : RBM.Gauss.Idx L W,
      (RBM.Gauss.svar L W i j : ℂ) = SB L (β i) (β j) * (W : ℂ)⁻¹ ^ 2 := by
    intro i j
    rw [hβ, hβ]
    exact RBM.Gauss.svar_cast_eq_Spaper L W i j
  set vt : Z2 L → ℂ :=
    fun a => (W : ℂ)⁻¹ ^ 2 * ∑ γ : Fin W × Fin W, v (e.symm (a, γ)) with hvt
  have hSv : ∀ i : RBM.Gauss.Idx L W,
      ∑ k, (RBM.Gauss.svar L W i k : ℂ) * v k = ∑ b, SB L (β i) b * vt b := by
    intro i
    refine (Equiv.sum_comp e.symm _).symm.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hvt]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [hsvar, hb (b, γ)]
    ring
  set r : RBM.Gauss.Idx L W → ℂ :=
    fun i => v i - ξ * ∑ k, (RBM.Gauss.svar L W i k : ℂ) * v k with hr
  set rt : Z2 L → ℂ := fun a => (W : ℂ)⁻¹ ^ 2 * ∑ γ : Fin W × Fin W, r (e.symm (a, γ)) with hrt
  have hcard : (∑ _γ : Fin W × Fin W, B) = (W : ℝ) ^ 2 * B := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hrt_le : ∀ a, ‖rt a‖ ≤ B := by
    intro a
    rw [hrt]
    simp only
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    calc (W : ℝ)⁻¹ ^ 2 * ‖∑ γ : Fin W × Fin W, r (e.symm (a, γ))‖
        ≤ (W : ℝ)⁻¹ ^ 2 * ∑ γ : Fin W × Fin W, ‖r (e.symm (a, γ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (W : ℝ)⁻¹ ^ 2 * ∑ _γ : Fin W × Fin W, B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => hB _) (by positivity)
      _ = B := by
          rw [hcard]
          field_simp
  have hmv : (1 - ξ • SB L) *ᵥ vt = rt := by
    funext a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 : (SB L *ᵥ vt) a = ∑ b, SB L a b * vt b := rfl
    rw [h1, hrt]
    simp only [hr]
    have h2 : ∀ γ : Fin W × Fin W, ∑ k, (RBM.Gauss.svar L W (e.symm (a, γ)) k : ℂ) * v k =
        ∑ b, SB L a b * vt b := fun γ => by
      rw [hSv, hb (a, γ)]
    simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    have h3 : vt a = (W : ℂ)⁻¹ ^ 2 * ∑ γ : Fin W × Fin W, v (e.symm (a, γ)) := rfl
    rw [h3]
    push_cast
    field_simp
  have hvt_eq : vt = Theta L ξ *ᵥ rt := by
    rw [← hmv, Matrix.mulVec_mulVec, Theta_mul L hL hξ, Matrix.one_mulVec]
  have hvt_le : ∀ b, ‖vt b‖ ≤ KΘ * B := by
    intro b
    rw [hvt_eq]
    calc ‖(Theta L ξ *ᵥ rt) b‖ = ‖∑ c, Theta L ξ b c * rt c‖ := rfl
      _ ≤ ∑ c, ‖Theta L ξ b c * rt c‖ := norm_sum_le _ _
      _ ≤ ∑ c, ‖Theta L ξ b c‖ * B := Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hrt_le c) (norm_nonneg _)
      _ = (∑ c, ‖Theta L ξ b c‖) * B := by rw [Finset.sum_mul]
      _ ≤ KΘ * B := mul_le_mul_of_nonneg_right (hΘ b) hB0
  have hrow : ∀ a : Z2 L, ∑ b : Z2 L, ‖SB L a b‖ = 1 := by
    intro a
    have := congrArg (fun x : NNReal => (x : ℝ)) (sum_nnnorm_SB_row L hL a)
    simpa [NNReal.coe_sum] using this
  intro i
  have hvi : v i = r i + ξ * ∑ b, SB L (β i) b * vt b := by
    rw [hr]; simp only; rw [hSv i]; ring
  rw [hvi]
  have hsum : ‖∑ b, SB L (β i) b * vt b‖ ≤ KΘ * B := by
    calc ‖∑ b, SB L (β i) b * vt b‖ ≤ ∑ b, ‖SB L (β i) b * vt b‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖SB L (β i) b‖ * (KΘ * B) := Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hvt_le b) (norm_nonneg _)
      _ = KΘ * B := by rw [← Finset.sum_mul, hrow, one_mul]
  calc ‖r i + ξ * ∑ b, SB L (β i) b * vt b‖ ≤ ‖r i‖ + ‖ξ‖ * ‖∑ b, SB L (β i) b * vt b‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B + 1 * (KΘ * B) := by
        have := mul_le_mul hξ.le hsum (norm_nonneg _) zero_le_one
        linarith [hB i]
    _ = (1 + KΘ) * B := by ring

end StableSvar

section Bulk

/-! ### The bulk gap `c_κ ≤ |1 - t m²|` -/

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < RBM.KLoop.gapK κ := by
  unfold RBM.KLoop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem gapK_le_one (κ : ℝ) : RBM.KLoop.gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    RBM.KLoop.gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ RBM.KLoop.gapK κ := (gapK_pos hκ hκ2).le
  have h1 : RBM.KLoop.gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * RBM.Gauss.spectralM E ^ 2‖ ^ 2 = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (RBM.Gauss.spectralM E).re = -E / 2 := by simp [RBM.Gauss.spectralM]
  have him := RBM.Gauss.spectralM_im E
  have hs := RBM.Gauss.spectralM_sqrt_sq hE
  rw [pow_two (RBM.Gauss.spectralM E), Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- The bulk gap: `c_κ ≤ |1 - t m²|` for `t ≥ 0` and `|E| ≤ 2 - κ`. -/
private theorem gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) :
    RBM.KLoop.gapK κ ≤ ‖1 - (t : ℂ) * RBM.Gauss.spectralM E ^ 2‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : RBM.KLoop.gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * RBM.Gauss.spectralM E ^ 2‖ ^ 2 := by
    rw [norm_one_sub_sq hE2]
    have hg1 : RBM.KLoop.gapK κ ^ 2 ≤ 1 := by
      have := gapK_le_one κ
      have := (gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have := (gapK_pos hκ hκ2).le
  have := norm_nonneg (1 - (t : ℂ) * RBM.Gauss.spectralM E ^ 2)
  nlinarith

/-- **`‖(1 - t m² S)⁻¹‖_{max→max} = O_κ(1 + log L)`**, uniformly in `t ∈ [0, 1)` and
`|E| ≤ 2 - κ`.  The row sums of `Θ_{t m²}` are bounded through property 5
(`norm_Theta_apply_le_prop5`), the gap `c_κ ≤ |1 - t m²|` and the exponential sum
`RBM.KLoop.sum_exp_le`; the resulting bound is `(Kstab2 κ L - 1) / 2`. -/
theorem stable_svar_bulk {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {κ E t : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (RBM.Gauss.svar L W) ((t : ℂ) * RBM.Gauss.spectralM E ^ 2) (Kstab2 κ L) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  set c := RBM.KLoop.gapK κ with hc
  have hc0 : 0 < c := gapK_pos hκ hκ2
  have hc1 : c ≤ 1 := gapK_le_one κ
  set ξ : ℂ := (t : ℂ) * RBM.Gauss.spectralM E ^ 2 with hξdef
  have hξ : ‖ξ‖ < 1 := by
    rw [hξdef, norm_mul, norm_pow, RBM.Gauss.norm_spectralM hE2, Complex.norm_real,
      Real.norm_of_nonneg ht0, one_pow, mul_one]
    exact ht1
  have hgap : c ≤ ‖(1 : ℂ) - ξ‖ := gapK_le_norm hκ hE ht0
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
  have hΘ : ∀ a : Z2 L, ∑ b : Z2 L, ‖Theta L ξ a b‖ ≤ Kstab2 κ L - 1 := by
    intro a
    set s : ℝ := (20000 * ellhat L ξ)⁻¹ with hs
    have hs0 : 0 < s := inv_pos.2 (by positivity)
    have hexp := RBM.KLoop.sum_exp_le L s hs0 a
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
    have hK : Kstab2 κ L - 1 =
        2 * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2) := by
      unfold Kstab2
      rw [← hc]
      ring
    have hXnn : 0 ≤
        180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 := by
      positivity
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
      _ ≤ Kstab2 κ L - 1 := by
          rw [h2s]
          linarith
  have h := stable_svar (W := W) hL hξ hΘ
  have e : 1 + (Kstab2 κ L - 1) = Kstab2 κ L := by ring
  rwa [e] at h

end Bulk

section Absorption

/-- **The absorption condition** `hKδ : K δ ≤ 1/2` of `norm_sq_green_diag_sub_le` for the
`d = 2` constant: with `δ = W^{-c}`, `K = Kstab2 κ L` and `W ≥ N^𝔠` (`Bandwidth`), the factor
`1 + log L ≤ 1 + 𝔠⁻¹ log W` is beaten by any power of `W`.  `SizeTendsto` makes `W → ∞`. -/
theorem eventually_Kstab2_mul_rpow_le (d : RBM.Gauss.Sizes) {κ 𝔠 c : ℝ}
    (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (hc : 0 < c)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : RBM.Path.Bandwidth d 𝔠) :
    ∀ᶠ n in Filter.atTop, Kstab2 κ (d.L n) * (d.W n : ℝ) ^ (-c) ≤ 1 / 2 := by
  have _ := hκ
  set A : ℝ := 2 * (180 * 40002 ^ 2) / RBM.KLoop.gapK κ *
    (1 + 40000 / Real.sqrt (RBM.KLoop.gapK κ)) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ RBM.KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    positivity
  have hlim : Tendsto (fun x : ℝ => (1 + A) * x ^ (-c) + (A / 𝔠) * (Real.log x / x ^ c))
      atTop (nhds 0) := by
    have h1 := (tendsto_rpow_neg_atTop hc).const_mul (1 + A)
    have h2 := ((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).const_mul (A / 𝔠)
    simpa using h1.add h2
  have hW : Tendsto (fun n => (d.W n : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hsz
    exact tendsto_atTop_mono' _ hbw h1
  have hev : ∀ᶠ n in atTop,
      (1 + A) * (d.W n : ℝ) ^ (-c) + (A / 𝔠) * (Real.log (d.W n : ℝ) / (d.W n : ℝ) ^ c) <
        1 / 2 :=
    (hlim.comp hW).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hbw, hev] with n hn hn2
  have hWn : 0 < d.W n := d.W_pos n
  have hLn : 3 ≤ d.L n := d.three_le_L n
  have hWpos : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast hWn
  have hLpos : (0 : ℝ) < (d.L n : ℝ) := by exact_mod_cast (by omega : 0 < d.L n)
  have hLN : ((d.L n : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : d.L n ≤ d.size n := by
      unfold RBM.Gauss.Sizes.size
      calc d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ hWn
        _ ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le hLpos hLN
  have hlogLN : Real.log (d.L n : ℝ) ≤ Real.log ((d.size n : ℕ) : ℝ) :=
    Real.log_le_log hLpos hLN
  have hlogN : 𝔠 * Real.log ((d.size n : ℕ) : ℝ) ≤ Real.log (d.W n : ℝ) := by
    rw [← Real.log_rpow hNpos]
    exact Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hn
  have hlogL : Real.log (d.L n : ℝ) ≤ Real.log (d.W n : ℝ) / 𝔠 := by
    rw [le_div_iff₀ h𝔠]
    nlinarith
  have hneg : (d.W n : ℝ) ^ (-c) = ((d.W n : ℝ) ^ c)⁻¹ := Real.rpow_neg hWpos.le c
  have hWc : 0 < (d.W n : ℝ) ^ c := Real.rpow_pos_of_pos hWpos c
  calc Kstab2 κ (d.L n) * (d.W n : ℝ) ^ (-c)
      = (1 + A * (1 + Real.log (d.L n : ℝ))) * (d.W n : ℝ) ^ (-c) := by
        rw [hA]; unfold Kstab2; ring
    _ ≤ (1 + A * (1 + Real.log (d.W n : ℝ) / 𝔠)) * (d.W n : ℝ) ^ (-c) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = (1 + A) * (d.W n : ℝ) ^ (-c) + (A / 𝔠) * (Real.log (d.W n : ℝ) / (d.W n : ℝ) ^ c) := by
        rw [hneg]
        field_simp
        ring
    _ ≤ 1 / 2 := hn2.le

end Absorption

end RBM.Green
