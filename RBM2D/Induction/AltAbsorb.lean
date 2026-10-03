/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEnd

/-!
# The absorption hypothesis `AltAbsorb` of the alternating endpoint

Namespace `RBM.Ind`.  Proves `AltAbsorb d` of `RBM2D.Induction.AltEnd` for every size sequence
`d`: at the exponents `altDelta`, `altTau`, `altDb`, `altDq`, `altCK`, eventually in `n`, the
thirteen fields of `AltBudgetHyp` (`ha1`-`ha5`, `he1`-`he8`) and the absorption of the last-step
level `altLastLevel`.

Structure: each field is one eventual inequality `poly(N, W, log N) ≤ N^{ε₀}/c`, proved as one
lemma `AltAbsorb_ev_*` from `SizeTendsto`, `Bandwidth` and the exponent choice, by the pattern of
`NonAltEnd_ev_ha1`-`NonAltEnd_ev_he5` (`RBM2D.Induction.NonAltEnd`); the argument parallels the
one-dimensional formalization.  The pointwise inputs are `W² ≤ N` (`AltAbsorb_Wpow_le`),
`W^{-D} ≤ N^{-cD}`, `ℓ_v ≥ 1`, `η_v ≤ 1`, `ℓ_v ≤ L`, `1 + log L ≤ 1 + log N`, `L² ≤ N`,
`Im m ≥ √(κ(4-κ))/2`.

* Section 1: pointwise bounds of the constants `C₄`, `C₄e`, `A`, `B`;
* Section 2: fields `ha1`-`ha5` (`ha5` through the square template `AltAbsorb_ev_of_sq_le`);
* Section 3: fields `he1`-`he8` (`he3` by `(1+x)^k - 1 ≤ 2^k x`, `he6` with the factor `Λ ≥ 1`
  pulled out of the square root);
* Section 4: the last step (`altLastLevel` splits into the `Ξ_{k-1}` part and the `W^{-D'}` part;
  the powers of `ℓ_v` cancel through `(W² η)⁻¹ M = ℓ²`);
* Section 5: the theorem `altAbsorb`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Pointwise bounds -/

/-- `W^x ≤ N^{x/2}` for `x ≥ 0` (from `W² ≤ N`). -/
theorem AltAbsorb_Wpow_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (d.W n : ℝ) ^ x ≤ ((d.size n : ℕ) : ℝ) ^ (x / 2) := by
  have hW0 : (0 : ℝ) ≤ d.W n := Nat.cast_nonneg _
  have h := Real.rpow_le_rpow (by positivity) (NonAltEnd_W_sq_le_size d n) (by positivity : 0 ≤ x / 2)
  have e : ((d.W n : ℝ) ^ 2) ^ (x / 2) = (d.W n : ℝ) ^ x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; congr 1; push_cast; ring
  rwa [e] at h

/-- the eventual template: `f ≤ C (1 + log N)^j N^a` pointwise and `a < b` give `f ≤ N^b/m` eventually. -/
theorem AltAbsorb_ev_of_le (hsize : SizeTendsto d) {a b C m : ℝ} (j : ℕ) (hab : a < b)
    (hm : 0 < m) {f : ℕ → ℝ}
    (hf : ∀ n, 1 ≤ ((d.size n : ℕ) : ℝ) →
      f n ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a) :
    ∀ᶠ n : ℕ in atTop, f n ≤ ((d.size n : ℕ) : ℝ) ^ b / m := by
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le j hab (C * m)),
    hsize.eventually_ge_atTop 1] with n h h1
  rw [le_div_iff₀ hm]
  calc f n * m ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a * m :=
        mul_le_mul_of_nonneg_right (hf n h1) hm.le
    _ = C * m * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a := by ring
    _ ≤ _ := h


/-- the eventual template with an eventual side condition `Q`. -/
theorem AltAbsorb_ev_of_leQ (hsize : SizeTendsto d) {a b C m : ℝ} (j : ℕ) (hab : a < b)
    (hm : 0 < m) {Q : ℕ → Prop} (hQ : ∀ᶠ n : ℕ in atTop, Q n) {f : ℕ → ℝ}
    (hf : ∀ n, Q n → 1 ≤ ((d.size n : ℕ) : ℝ) →
      f n ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a) :
    ∀ᶠ n : ℕ in atTop, f n ≤ ((d.size n : ℕ) : ℝ) ^ b / m := by
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le j hab (C * m)),
    hsize.eventually_ge_atTop 1, hQ] with n h h1 hq
  rw [le_div_iff₀ hm]
  calc f n * m ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a * m :=
        mul_le_mul_of_nonneg_right (hf n hq h1) hm.le
    _ = C * m * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a := by ring
    _ ≤ _ := h

/-- the eventual template for a square: `f² ≤ C (1 + log N)^j N^a`, `a < 2b`, `f ≥ 0`. -/
theorem AltAbsorb_ev_of_sq_le (hsize : SizeTendsto d) {a b C m : ℝ} (j : ℕ) (hab : a < 2 * b)
    (hm : 0 < m) {f : ℕ → ℝ}
    (hf : ∀ n, 1 ≤ ((d.size n : ℕ) : ℝ) → 0 ≤ f n ∧
      (f n) ^ 2 ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a) :
    ∀ᶠ n : ℕ in atTop, f n ≤ ((d.size n : ℕ) : ℝ) ^ b / m := by
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le j hab (C * m ^ 2)),
    hsize.eventually_ge_atTop 1] with n h h1
  obtain ⟨hf0, hf2⟩ := hf n h1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN2 : ((d.size n : ℕ) : ℝ) ^ (2 * b) = (((d.size n : ℕ) : ℝ) ^ b) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hb0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ b / m := by positivity
  refine (sq_le_sq₀ hf0 hb0).1 ?_
  rw [div_pow, ← hN2, le_div_iff₀ (by positivity)]
  calc (f n) ^ 2 * m ^ 2 ≤ C * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a * m ^ 2 :=
        mul_le_mul_of_nonneg_right hf2 (by positivity)
    _ = C * m ^ 2 * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j * ((d.size n : ℕ) : ℝ) ^ a := by ring
    _ ≤ _ := h


/-- `0 ≤ cCase4 k`. -/
theorem AltAbsorb_cCase4_nonneg (k : ℕ) : 0 ≤ cCase4 k := by unfold cCase4 cProp5; positivity
/-- `0 ≤ cCase5 k`. -/
theorem AltAbsorb_cCase5_nonneg (k : ℕ) : 0 ≤ cCase5 k := by unfold cCase5 cProp5; positivity

/-- `1 ≤ 1 + log N`. -/
theorem AltAbsorb_one_le_P (n : ℕ) : 1 ≤ 1 + Real.log ((d.size n : ℕ) : ℝ) := by
  have := Real.log_nonneg (NonAltEnd_one_le_size d n)
  linarith

/-- `0 ≤ 1 + log L`. -/
theorem AltAbsorb_P_L_nonneg (n : ℕ) : 0 ≤ 1 + Real.log (d.L n : ℝ) := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ d.L n by linarith [NonAltEnd_three_le_L d n])
  linarith

/-- `L² ≤ N` (from `N = W² L²`, `W ≥ 1`). -/
theorem AltAbsorb_L_sq_le (n : ℕ) : (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  rw [NonAltEnd_size_eq]
  have h := NonAltEnd_one_le_W d n
  nlinarith [sq_nonneg (d.L n : ℝ), mul_nonneg (sq_nonneg (d.L n : ℝ)) (sq_nonneg ((d.W n : ℝ) - 1)),
    mul_nonneg (sq_nonneg (d.L n : ℝ)) (sub_nonneg.2 h)]

/-- `1 + log L ≤ 1 + log N`. -/
theorem AltAbsorb_logL_le (n : ℕ) : 1 + Real.log (d.L n : ℝ) ≤ 1 + Real.log ((d.size n : ℕ) : ℝ) := by
  have h3 := NonAltEnd_three_le_L d n
  have := Real.log_le_log (by linarith) (NonAltEnd_L_le_size d n)
  linarith

/-- `C₄ = altC4 ≤ c₄ (1 + log N)^{k+1} N^{τ' k}` (from `W² ≤ N`). -/
theorem AltAbsorb_C4_le (n k : ℕ) {τ' : ℝ} (hτ : 0 ≤ τ') :
    altC4 (d.L n) (d.W n) k τ' ≤ cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) *
      ((d.size n : ℕ) : ℝ) ^ (τ' * (k : ℝ)) := by
  unfold altC4
  have h1 := NonAltEnd_log_pow_le d n (k + 1)
  have h2 := NonAltEnd_Wpow_le d n (2 * k) hτ
  have e : τ' * ((2 * k : ℕ) : ℝ) / 2 = τ' * (k : ℝ) := by push_cast; ring
  rw [e] at h2
  have hc := AltAbsorb_cCase4_nonneg k
  have h4 : 0 ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (by positivity) (by positivity)

/-- `C₄e = altC4e ≤ c₄ (1 + log N)^k N^k` (from `L² ≤ N`). -/
theorem AltAbsorb_C4e_le (n k : ℕ) :
    altC4e (d.L n) k ≤ cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
      ((d.size n : ℕ) : ℝ) ^ (k : ℝ) := by
  unfold altC4e
  have hc := AltAbsorb_cCase4_nonneg k
  have h1 := AltAbsorb_logL_le d n
  have h2 := AltAbsorb_L_sq_le d n
  have hP := AltAbsorb_P_L_nonneg d n
  rw [Real.rpow_natCast, mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
    (mul_le_mul h1 h2 (by positivity) (by linarith [AltAbsorb_one_le_P d n])) k) hc

/-- `A = altQvA ≤ c₅ 3^{4k} (1 + log N)^{2k+1} N^{(2k + C_k(𝔠)) τ'}` (`W^{(4k + 2C_k)τ'} ≤ N^{(2k + C_k)τ'}`). -/
theorem AltAbsorb_A_le (n k : ℕ) {c τ' : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ') :
    altQvA (d.L n) (d.W n) k c τ' ≤ cCase5 k * 3 ^ (4 * k) *
      (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
      ((d.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + cPrec c k) * τ') := by
  unfold altQvA
  have hc5 := AltAbsorb_cCase5_nonneg k
  have h1 := NonAltEnd_log_pow_le d n (2 * k + 1)
  have h2 := NonAltEnd_Wpow_le d n (4 * k) hτ
  have e : τ' * ((4 * k : ℕ) : ℝ) / 2 = 2 * (k : ℝ) * τ' := by push_cast; ring
  rw [e] at h2
  have hcp : 0 ≤ cPrec c k := by unfold cPrec; positivity
  have h3 := AltAbsorb_Wpow_le d n (x := 2 * (cPrec c k * τ')) (by positivity)
  have e3 : 2 * (cPrec c k * τ') / 2 = cPrec c k * τ' := by ring
  rw [e3] at h3
  have hW0 : 0 ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith [NonAltEnd_one_le_size d n]
  have e4 : ((d.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + cPrec c k) * τ') =
      ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) * τ') * ((d.size n : ℕ) : ℝ) ^ (cPrec c k * τ') := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  rw [e4, mul_pow]
  have hP := AltAbsorb_P_L_nonneg d n
  calc cCase5 k * (1 + Real.log (d.L n : ℝ)) ^ (2 * k + 1) * (3 ^ (4 * k) * ((d.W n : ℝ) ^ τ') ^ (4 * k)) *
        (d.W n : ℝ) ^ (2 * (cPrec c k * τ'))
      ≤ cCase5 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) * (3 ^ (4 * k) *
          ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) * τ')) * ((d.size n : ℕ) : ℝ) ^ (cPrec c k * τ') := by
        gcongr
    _ = _ := by ring


/-- `B = altQvB ≤ c₅ (1 + log N)^{2k} N^{2k} (2 + M_max)`. -/
theorem AltAbsorb_B_le (n k : ℕ) {M : ℝ} (hM : 0 ≤ 2 + M) :
    altQvB (d.L n) k M ≤ cCase5 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k) *
      ((d.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) * (2 + M) := by
  unfold altQvB
  have hc := AltAbsorb_cCase5_nonneg k
  have h1 := AltAbsorb_logL_le d n
  have h2 := AltAbsorb_L_sq_le d n
  have hP := AltAbsorb_P_L_nonneg d n
  have h3 : ((1 + Real.log (d.L n : ℝ)) * (d.L n : ℝ) ^ 2) ^ (2 * k) ≤
      (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (2 * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul h1 h2 (by positivity)
      (by linarith [AltAbsorb_one_le_P d n])) _
  rw [Real.rpow_natCast]
  calc cCase5 k * ((1 + Real.log (d.L n : ℝ)) * (d.L n : ℝ) ^ 2) ^ (2 * k) * (2 + M)
      ≤ cCase5 k * ((1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (2 * k)) *
        (2 + M) := by gcongr
    _ = _ := by ring

/-- `Im m` bounds in the bulk. -/
theorem AltAbsorb_Ls_le {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {N : ℝ} (hN1 : 1 ≤ N) :
    (spectralM E).im⁻¹ * Real.log N ≤ (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * (1 + Real.log N) := by
  have hc0 := AzumaProxyN_c0_pos_pub hκ hE
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  calc _ ≤ (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * Real.log N :=
        mul_le_mul_of_nonneg_right (NonAltEnd_im_inv_le hκ hE) hlog0
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hc0.le)

theorem AltAbsorb_Ls1_le {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {N : ℝ} (hN1 : 1 ≤ N) :
    (spectralM E).im⁻¹ * Real.log N + 1 ≤ ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ + 1) * (1 + Real.log N) := by
  have hc0 := AzumaProxyN_c0_pos_pub hκ hE
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h := AltAbsorb_Ls_le hκ hE hN1
  nlinarith [inv_nonneg.2 hc0.le]

theorem AltAbsorb_Ls_nonneg {E : ℝ} (hE : |E| < 2) {N : ℝ} (hN1 : 1 ≤ N) :
    0 ≤ (spectralM E).im⁻¹ * Real.log N := by
  have := inv_nonneg.2 (spectralM_im_pos hE).le
  have := Real.log_nonneg hN1
  positivity


/-! ## 2. Fields `ha1`-`ha5` -/

/-- `N^{ε_q} W^{2(k-1)τ'} ≤ N^{ε_q + τ'(k-1)}`, the common factor of `ha1`-`ha4`. -/
theorem AltAbsorb_X_le (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {τ' εq : ℝ} (hτ : 0 ≤ τ') :
    ((d.size n : ℕ) : ℝ) ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') ≤
      ((d.size n : ℕ) : ℝ) ^ (εq + τ' * ((k : ℝ) - 1)) := by
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith [NonAltEnd_one_le_size d n]
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := AltAbsorb_Wpow_le d n (x := 2 * ((k : ℝ) - 1) * τ') (by positivity)
  rw [Real.rpow_add hN0]
  have e : 2 * ((k : ℝ) - 1) * τ' / 2 = τ' * ((k : ℝ) - 1) := by ring
  rw [e] at h
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hN0.le _)

/-- Field `ha1`: `N^{ε_q} W^{2(k-1)τ'} ≤ N^{ε₀}/10` when `ε_q + τ'(k-1) < ε₀`. -/
theorem AltAbsorb_ev_ha1 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {τ' εq ε₀ : ℝ}
    (hτ : 0 ≤ τ') (hε : εq + τ' * ((k : ℝ) - 1) < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 10 := by
  refine AltAbsorb_ev_of_le d hsize (C := 1) 0 hε (by norm_num) (fun n h1 => ?_)
  rw [pow_zero, one_mul, one_mul]
  exact AltAbsorb_X_le d n hk hτ

/-- Field `ha2`: the same with the factor `5 (Im m)^{-1} log N`. -/
theorem AltAbsorb_ev_ha2 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ)
    {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) {τ' εq ε₀ : ℝ}
    (hτ : 0 ≤ τ') (hε : εq + τ' * ((k : ℝ) - 1) < ε₀) :
    ∀ᶠ n : ℕ in atTop, 5 * (((d.size n : ℕ) : ℝ) ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 10 := by
  refine AltAbsorb_ev_of_le d hsize (C := 5 * (Real.sqrt (κ * (4 - κ)) / 2)⁻¹) 1 hε (by norm_num)
    (fun n h1 => ?_)
  have hX := AltAbsorb_X_le d n hk (εq := εq) hτ
  have hL := AltAbsorb_Ls_le hκ (hE n) h1
  have hL0 := AltAbsorb_Ls_nonneg (by linarith [hE n, abs_nonneg (E n)] : |E n| < 2) h1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  calc _ ≤ 5 * ((d.size n : ℕ) : ℝ) ^ (εq + τ' * ((k : ℝ) - 1)) *
        ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * (1 + Real.log ((d.size n : ℕ) : ℝ))) := by
        refine mul_le_mul (by linarith) hL hL0 (by positivity)
    _ = _ := by ring

/-- Field `ha3`: the same with the factor `C₄`. -/
theorem AltAbsorb_ev_ha3 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {τ' εE ε₀ : ℝ}
    (hτ : 0 ≤ τ') (hε : τ' * (k : ℝ) + (εE + τ' * ((k : ℝ) - 1)) < ε₀) :
    ∀ᶠ n : ℕ in atTop, altC4 (d.L n) (d.W n) k τ' *
      (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 10 := by
  refine AltAbsorb_ev_of_le d hsize (C := cCase4 k) (k + 1) hε (by norm_num) (fun n h1 => ?_)
  have hX := AltAbsorb_X_le d n hk (εq := εE) hτ
  have hC := AltAbsorb_C4_le d n k hτ
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hc := AltAbsorb_cCase4_nonneg k
  have hP := AltAbsorb_one_le_P d n
  have hXn : 0 ≤ ((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') := by positivity
  calc _ ≤ (cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) *
        ((d.size n : ℕ) : ℝ) ^ (τ' * (k : ℝ))) * ((d.size n : ℕ) : ℝ) ^ (εE + τ' * ((k : ℝ) - 1)) :=
        mul_le_mul hC hX hXn (by positivity)
    _ = _ := by rw [Real.rpow_add hN0 (τ' * (k : ℝ)) (εE + τ' * ((k : ℝ) - 1))]; ring


/-- Field `ha4`: the same with the factor `5 C₄ (Im m)^{-1} log N`. -/
theorem AltAbsorb_ev_ha4 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ)
    {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) {τ' εE ε₀ : ℝ}
    (hτ : 0 ≤ τ') (hε : τ' * (k : ℝ) + (εE + τ' * ((k : ℝ) - 1)) < ε₀) :
    ∀ᶠ n : ℕ in atTop, 5 * altC4 (d.L n) (d.W n) k τ' *
      (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 10 := by
  refine AltAbsorb_ev_of_le d hsize (C := 5 * cCase4 k * (Real.sqrt (κ * (4 - κ)) / 2)⁻¹) (k + 2) hε
    (by norm_num) (fun n h1 => ?_)
  have hX := AltAbsorb_X_le d n hk (εq := εE) hτ
  have hC := AltAbsorb_C4_le d n k hτ
  have hL := AltAbsorb_Ls_le hκ (hE n) h1
  have hL0 := AltAbsorb_Ls_nonneg (by linarith [hE n, abs_nonneg (E n)] : |E n| < 2) h1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hc := AltAbsorb_cCase4_nonneg k
  have hP := AltAbsorb_one_le_P d n
  have hXn : 0 ≤ ((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') := by positivity
  have hC0 : 0 ≤ altC4 (d.L n) (d.W n) k τ' := by
    unfold altC4
    have := AltAbsorb_P_L_nonneg d n
    positivity
  calc _ ≤ (5 * (cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) *
        ((d.size n : ℕ) : ℝ) ^ (τ' * (k : ℝ)))) * ((d.size n : ℕ) : ℝ) ^ (εE + τ' * ((k : ℝ) - 1)) *
        ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * (1 + Real.log ((d.size n : ℕ) : ℝ))) := by
        refine mul_le_mul (mul_le_mul (by linarith) hX hXn (by positivity)) hL hL0 (by positivity)
    _ = _ := by rw [Real.rpow_add hN0 (τ' * (k : ℝ)) (εE + τ' * ((k : ℝ) - 1))]; ring

theorem AltAbsorb_rpow_sq {N : ℝ} (hN0 : 0 < N) (x : ℝ) : (N ^ x) ^ 2 = N ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring

theorem AltAbsorb_A_nonneg (n k : ℕ) (c τ' : ℝ) : 0 ≤ altQvA (d.L n) (d.W n) k c τ' := by
  unfold altQvA
  have := AltAbsorb_P_L_nonneg d n
  have := AltAbsorb_cCase5_nonneg k
  positivity

/-- Field `ha5`: the Azuma main term `N^{ε} N^{ε_Γ} √(2kA (L_s + 1)) ≤ N^{ε₀}/10` when `2(ε + ε_Γ) + (2k + C_k(𝔠))τ' < 2ε₀`. -/
theorem AltAbsorb_ev_ha5 (hsize : SizeTendsto d) {k : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) {c τ' ε εΓ ε₀ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ')
    (hε : 2 * (ε + εΓ) + (2 * (k : ℝ) + cPrec c k) * τ' < 2 * ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ εΓ *
      Real.sqrt (2 * (k : ℝ) * altQvA (d.L n) (d.W n) k c τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 10 := by
  refine AltAbsorb_ev_of_sq_le d hsize
    (C := 2 * (k : ℝ) * (cCase5 k * 3 ^ (4 * k)) * ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ + 1)) (2 * k + 2)
    (a := 2 * (ε + εΓ) + (2 * (k : ℝ) + cPrec c k) * τ') hε (by norm_num) (fun n h1 => ?_)
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hA := AltAbsorb_A_le d n k hc hτ
  have hA0 := AltAbsorb_A_nonneg d n k c τ'
  have hL := AltAbsorb_Ls1_le hκ (hE n) h1
  have hL0 : 0 ≤ (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1 := by
    have := AltAbsorb_Ls_nonneg (by linarith [hE n, abs_nonneg (E n)] : |E n| < 2) h1
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hZ0 : 0 ≤ 2 * (k : ℝ) * altQvA (d.L n) (d.W n) k c τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1) := by positivity
  have hc5 := AltAbsorb_cCase5_nonneg k
  have hP := AltAbsorb_one_le_P d n
  refine ⟨by positivity, ?_⟩
  have e1 : (((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ εΓ *
      Real.sqrt (2 * (k : ℝ) * altQvA (d.L n) (d.W n) k c τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1)))) ^ 2 =
      ((d.size n : ℕ) : ℝ) ^ (2 * (ε + εΓ)) * (2 * (k : ℝ) * altQvA (d.L n) (d.W n) k c τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1)) := by
    rw [← mul_assoc, mul_pow, Real.sq_sqrt hZ0, ← Real.rpow_add hN0, AltAbsorb_rpow_sq hN0]
  rw [e1]
  have hZ : 2 * (k : ℝ) * altQvA (d.L n) (d.W n) k c τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1) ≤
      2 * (k : ℝ) * (cCase5 k * 3 ^ (4 * k) * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        ((d.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + cPrec c k) * τ')) *
      (((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ + 1) * (1 + Real.log ((d.size n : ℕ) : ℝ))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hL hL0 (by positivity)
  calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * (ε + εΓ)) * (2 * (k : ℝ) * (cCase5 k * 3 ^ (4 * k) *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        ((d.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + cPrec c k) * τ')) *
      (((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ + 1) * (1 + Real.log ((d.size n : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by
        rw [Real.rpow_add hN0 (2 * (ε + εΓ)) ((2 * (k : ℝ) + cPrec c k) * τ')]; ring


/-! ## 3. Fields `he1`, `he2`, `he4`-`he8` -/

theorem AltAbsorb_pow4 {N : ℝ} (hN0 : 0 < N) (a b c e : ℝ) :
    N ^ a * N ^ b * N ^ c * N ^ e = N ^ (a + b + c + e) := by
  rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]

theorem AltAbsorb_pow5 {N : ℝ} (hN0 : 0 < N) (a b c e f : ℝ) :
    N ^ a * N ^ b * N ^ c * N ^ e * N ^ f = N ^ (a + b + c + e + f) := by
  rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]

theorem AltAbsorb_Wneg_le {c Db : ℝ} (n : ℕ) (hband : ((d.size n : ℕ) : ℝ) ^ c ≤ (d.W n : ℝ))
    (hD : 0 ≤ Db) : (d.W n : ℝ) ^ (-Db) ≤ ((d.size n : ℕ) : ℝ) ^ (-(c * Db)) :=
  NonAltEnd_Wneg_le (by linarith [NonAltEnd_one_le_size d n]) hband hD

/-- Field `he1`: `N^k (N^{ε_q} N^k + 1) W^{-D_b} ≤ N^{ε₀}/20` when `2k + ε_q - c D_b < ε₀`. -/
theorem AltAbsorb_ev_he1 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    {Db εq ε₀ : ℝ} (hD : 0 ≤ Db) (hq : 0 ≤ εq) (hε : 2 * (k : ℝ) + εq - c * Db < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((((d.size n : ℕ) : ℝ) ^ εq *
      ((d.size n : ℕ) : ℝ) ^ k + 1) * (d.W n : ℝ) ^ (-Db)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
  refine AltAbsorb_ev_of_leQ d hsize (C := 2) 0 hε (by norm_num) hband (fun n hb h1 => ?_)
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW := AltAbsorb_Wneg_le d n hb hD
  have hx : 1 ≤ ((d.size n : ℕ) : ℝ) ^ εq * ((d.size n : ℕ) : ℝ) ^ k :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 hq) (one_le_pow₀ h1)
  have hW0 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [pow_zero, mul_one, NonAltEnd_npow_eq]
  calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((2 * (((d.size n : ℕ) : ℝ) ^ εq *
      ((d.size n : ℕ) : ℝ) ^ (k : ℝ))) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by
        rw [← NonAltEnd_npow_eq]
        gcongr
        linarith
    _ = _ := by
        have e : ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * (2 * (((d.size n : ℕ) : ℝ) ^ εq *
            ((d.size n : ℕ) : ℝ) ^ (k : ℝ)) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) =
            2 * (((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ εq *
            ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by ring
        rw [e, AltAbsorb_pow4 hN0]
        rw [show (k : ℝ) + εq + (k : ℝ) + -(c * Db) = 2 * (k : ℝ) + εq - c * Db by ring]

/-- Field `he2`: the same with the factor `5 N^{ε_q} N^k + 1`. -/
theorem AltAbsorb_ev_he2 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    {Db εq ε₀ : ℝ} (hD : 0 ≤ Db) (hq : 0 ≤ εq) (hε : 2 * (k : ℝ) + εq - c * Db < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((5 * (((d.size n : ℕ) : ℝ) ^ εq *
      ((d.size n : ℕ) : ℝ) ^ k) + 1) * (d.W n : ℝ) ^ (-Db)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
  refine AltAbsorb_ev_of_leQ d hsize (C := 6) 0 hε (by norm_num) hband (fun n hb h1 => ?_)
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW := AltAbsorb_Wneg_le d n hb hD
  have hx : 1 ≤ ((d.size n : ℕ) : ℝ) ^ εq * ((d.size n : ℕ) : ℝ) ^ k :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 hq) (one_le_pow₀ h1)
  have hW0 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [pow_zero, mul_one, NonAltEnd_npow_eq]
  calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((6 * (((d.size n : ℕ) : ℝ) ^ εq *
      ((d.size n : ℕ) : ℝ) ^ (k : ℝ))) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by
        rw [← NonAltEnd_npow_eq]
        gcongr
        linarith
    _ = _ := by
        have e : ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * (6 * (((d.size n : ℕ) : ℝ) ^ εq *
            ((d.size n : ℕ) : ℝ) ^ (k : ℝ)) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) =
            6 * (((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ εq *
            ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by ring
        rw [e, AltAbsorb_pow4 hN0]
        rw [show (k : ℝ) + εq + (k : ℝ) + -(c * Db) = 2 * (k : ℝ) + εq - c * Db by ring]

/-- (`he7`, `he8`) `N^k N^{-D} ≤ N^{ε₀}/20`. -/
theorem AltAbsorb_ev_he7 (hsize : SizeTendsto d) (k : ℕ) {D ε₀ : ℝ} (hε : (k : ℝ) - D < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
  refine AltAbsorb_ev_of_le d hsize (C := 1) 0 hε (by norm_num) (fun n h1 => ?_)
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  rw [pow_zero, one_mul, one_mul, NonAltEnd_npow_eq, ← Real.rpow_add hN0, ← sub_eq_add_neg]

/-- the product `N^k (a₅ C₄ + C₄e) N^k N^{ε_E} W^{-D_b}` of `he4`, `he5`. -/
theorem AltAbsorb_ev_he45 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    {Db εE ε₀ τ' a5 : ℝ} (hD : 0 ≤ Db) (hτ : 0 ≤ τ') (ha5 : 0 ≤ a5)
    (hε1 : 2 * (k : ℝ) + τ' * (k : ℝ) + εE - c * Db < ε₀) (hε2 : 3 * (k : ℝ) + εE - c * Db < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((a5 * altC4 (d.L n) (d.W n) k τ' +
      altC4e (d.L n) k) * ((d.size n : ℕ) : ℝ) ^ k *
      (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
  have h1 : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((a5 * altC4 (d.L n) (d.W n) k τ') *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 40 := by
    refine AltAbsorb_ev_of_leQ d hsize (C := a5 * cCase4 k) (k + 1) hε1 (by norm_num) hband
      (fun n hb h1 => ?_)
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hW := AltAbsorb_Wneg_le d n hb hD
    have hC := AltAbsorb_C4_le d n k hτ
    have hc := AltAbsorb_cCase4_nonneg k
    have hP := AltAbsorb_one_le_P d n
    have hW0 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC0 : 0 ≤ altC4 (d.L n) (d.W n) k τ' := by
      unfold altC4
      have := AltAbsorb_P_L_nonneg d n
      positivity
    rw [NonAltEnd_npow_eq]
    calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((a5 * (cCase4 k *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) * ((d.size n : ℕ) : ℝ) ^ (τ' * (k : ℝ)))) *
        ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * (((d.size n : ℕ) : ℝ) ^ εE *
        ((d.size n : ℕ) : ℝ) ^ (-(c * Db)))) := by
          rw [← NonAltEnd_npow_eq]
          gcongr
      _ = a5 * cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) *
          (((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ (τ' * (k : ℝ)) *
          ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ εE *
          ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by ring
      _ = _ := by
          rw [AltAbsorb_pow5 hN0]
          rw [show (k : ℝ) + τ' * (k : ℝ) + (k : ℝ) + εE + -(c * Db) =
            2 * (k : ℝ) + τ' * (k : ℝ) + εE - c * Db by ring]
  have h2 : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * (altC4e (d.L n) k *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 40 := by
    refine AltAbsorb_ev_of_leQ d hsize (C := cCase4 k) k hε2 (by norm_num) hband
      (fun n hb h1 => ?_)
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hW := AltAbsorb_Wneg_le d n hb hD
    have hC := AltAbsorb_C4e_le d n k
    have hc := AltAbsorb_cCase4_nonneg k
    have hP := AltAbsorb_one_le_P d n
    have hW0 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC0 : 0 ≤ altC4e (d.L n) k := by
      unfold altC4e
      have := AltAbsorb_P_L_nonneg d n
      positivity
    rw [NonAltEnd_npow_eq]
    calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((cCase4 k *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k * ((d.size n : ℕ) : ℝ) ^ (k : ℝ)) *
        ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * (((d.size n : ℕ) : ℝ) ^ εE *
        ((d.size n : ℕ) : ℝ) ^ (-(c * Db)))) := by
          rw [← NonAltEnd_npow_eq]
          gcongr
          simpa [Real.rpow_natCast] using hC
      _ = cCase4 k * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
          (((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ (k : ℝ) *
          ((d.size n : ℕ) : ℝ) ^ (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ εE *
          ((d.size n : ℕ) : ℝ) ^ (-(c * Db))) := by ring
      _ = _ := by
          rw [AltAbsorb_pow5 hN0]
          rw [show (k : ℝ) + (k : ℝ) + (k : ℝ) + εE + -(c * Db) = 3 * (k : ℝ) + εE - c * Db by ring]
  filter_upwards [h1, h2] with n hn1 hn2
  have e : ((d.size n : ℕ) : ℝ) ^ k * ((a5 * altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) =
      ((d.size n : ℕ) : ℝ) ^ k * ((a5 * altC4 (d.L n) (d.W n) k τ') *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) +
      ((d.size n : ℕ) : ℝ) ^ k * (altC4e (d.L n) k *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) := by ring
  rw [e]
  linarith


theorem AltAbsorb_one_add_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k ≤ 1 + ((2 : ℝ) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    calc (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := pow_succ _ _
      _ ≤ (1 + ((2 : ℝ) ^ k - 1) * x) * (1 + x) := by gcongr
      _ ≤ 1 + ((2 : ℝ) ^ (k + 1) - 1) * x := by
          rw [pow_succ (2 : ℝ)]
          nlinarith [mul_nonneg (sub_nonneg.2 h2) (mul_nonneg hx0 (sub_nonneg.2 hx1))]

/-- Field `he3`: `N^k · altShiftTerm ≤ N^{ε₀}/20` when `6k + 8 - C_K < ε₀`, `N^{C_K} ≤ K`, `C_K ≥ 1`. -/
theorem AltAbsorb_ev_he3 (hsize : SizeTendsto d) {s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) {C_K ε₀ : ℝ}
    (hC : 1 ≤ C_K) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hε : 6 * (k : ℝ) + 8 - C_K < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k *
      altShiftTerm s v K n k ((d.size n : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
  refine AltAbsorb_ev_of_leQ d hsize (C := 10 * 2 ^ k) 0 hε (by norm_num) hKN (fun n hK h1 => ?_)
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ := NonAltEnd_step_le d hK hvs
  have hKΔ := NonAltEnd_K_mul_step (s := s) (v := v) (K := K) (hK0 n) hvs
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hΔN := NonAltEnd_hΔN d hC hK hvs
  have hK00 : (0 : ℝ) ≤ (K n : ℝ) * gridStep s v K n := mul_nonneg (Nat.cast_nonneg _) hΔ0
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  have hx0 : 0 ≤ gridStep s v K n * Nn := mul_nonneg hΔ0 hN0.le
  have hpow := AltAbsorb_one_add_pow_le hx0 hΔN k
  have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hm : (1 + gridStep s v K n * Nn) ^ k - 1 ≤ 2 ^ k * (Nn ^ (-C_K) * Nn) := by
    calc (1 + gridStep s v K n * Nn) ^ k - 1 ≤ ((2 : ℝ) ^ k - 1) * (gridStep s v K n * Nn) := by linarith
      _ ≤ 2 ^ k * (gridStep s v K n * Nn) := by nlinarith
      _ ≤ 2 ^ k * (Nn ^ (-C_K) * Nn) := by gcongr
  have hm0 : 0 ≤ (1 + gridStep s v K n * Nn) ^ k - 1 := by
    have : (1 : ℝ) ≤ (1 + gridStep s v K n * Nn) ^ k := one_le_pow₀ (by linarith)
    linarith
  rw [pow_zero, mul_one]
  calc Nn ^ k * altShiftTerm s v K n k Nn
      = Nn ^ k * ((K n : ℝ) * gridStep s v K n * (Nn ^ k * ((1 + gridStep s v K n * Nn) ^ k - 1) *
        (10 * Nn ^ (4 * k + 7)))) := rfl
    _ ≤ Nn ^ k * (1 * (Nn ^ k * (2 ^ k * (Nn ^ (-C_K) * Nn)) * (10 * Nn ^ (4 * k + 7)))) := by
        gcongr
    _ = 10 * 2 ^ k * (Nn ^ (k : ℝ) * Nn ^ (k : ℝ) * Nn ^ (-C_K) * Nn ^ (1 : ℝ) *
          Nn ^ (((4 * k + 7 : ℕ)) : ℝ)) := by
        rw [NonAltEnd_npow_eq Nn k, NonAltEnd_npow_eq Nn (4 * k + 7), Real.rpow_one]; ring
    _ = _ := by
        rw [AltAbsorb_pow5 hN0]
        rw [show (k : ℝ) + (k : ℝ) + -C_K + 1 + ((4 * k + 7 : ℕ) : ℝ) = 6 * (k : ℝ) + 8 - C_K by
          push_cast; ring]


/-- Field `he6`: the far part of the quadratic variation, `N^{ε} N^k √(k (A + B) N^{2k} W^{-D_q + C'}) ≤ (N^{ε₀}/20) Λ^{1/2}`, with `Λ ≥ 1` pulled out of the square root. -/
theorem AltAbsorb_ev_he6 (hsize : SizeTendsto d) {k : ℕ} {c : ℝ} (hc : 0 < c)
    (hband : Bandwidth d c) {τ' ε εΓ ε₀ Dq C' : ℝ} (hτ : 0 ≤ τ') (hD : 0 ≤ Dq - C') (hεΓ : 0 ≤ εΓ)
    (hA : (2 * (k : ℝ) + cPrec c k) * τ' ≤ 2 * (k : ℝ) + 2 * εΓ + 1)
    (hε : 2 * ε + 2 * εΓ + 6 * (k : ℝ) + 1 - c * (Dq - C') < 2 * ε₀)
    {Λ : ℕ → ℝ} (hΛ : ∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ k *
      Real.sqrt ((k : ℝ) * ((altQvA (d.L n) (d.W n) k c τ' +
        altQvB (d.L n) k (((d.size n : ℕ) : ℝ) ^ εΓ * (((d.size n : ℕ) : ℝ) ^ εΓ * Λ n) *
          ((d.size n : ℕ) : ℝ) + 1)) *
        ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-Dq + C')))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 * Λ n ^ ((1 : ℝ) / 2) := by
  have hg : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ k *
      Real.sqrt ((k : ℝ) * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2 * εΓ + 1)) *
        ((d.size n : ℕ) : ℝ) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (-(c * (Dq - C')))))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 := by
    refine AltAbsorb_ev_of_sq_le d hsize (C := (k : ℝ) * (cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k))
      (2 * k + 1) (a := 2 * ε + 2 * εΓ + 6 * (k : ℝ) + 1 - c * (Dq - C')) hε (by norm_num)
      (fun n h1 => ?_)
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hc5 := AltAbsorb_cCase5_nonneg k
    have hP := AltAbsorb_one_le_P d n
    have hZ0 : 0 ≤ (k : ℝ) * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2 * εΓ + 1)) *
        ((d.size n : ℕ) : ℝ) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (-(c * (Dq - C')))) := by positivity
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hZ0, AltAbsorb_rpow_sq hN0,
      NonAltEnd_npow_eq ((d.size n : ℕ) : ℝ) k, AltAbsorb_rpow_sq hN0,
      NonAltEnd_npow_eq ((d.size n : ℕ) : ℝ) (2 * k)]
    have e : ((d.size n : ℕ) : ℝ) ^ (2 * ε) * (((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ)) *
        ((k : ℝ) * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2 * εΓ + 1)) *
        ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ)) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(c * (Dq - C')))))) =
        (k : ℝ) * (cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k + 1) *
        (((d.size n : ℕ) : ℝ) ^ (2 * ε) * ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ)) *
        ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2 * εΓ + 1) * ((d.size n : ℕ) : ℝ) ^ (2 * (k : ℝ)) *
        ((d.size n : ℕ) : ℝ) ^ (-(c * (Dq - C')))) := by
      push_cast; ring
    rw [e, AltAbsorb_pow5 hN0]
    refine le_of_eq ?_
    rw [show 2 * ε + 2 * (k : ℝ) + (2 * (k : ℝ) + 2 * εΓ + 1) + 2 * (k : ℝ) + -(c * (Dq - C')) =
      2 * ε + 2 * εΓ + 6 * (k : ℝ) + 1 - c * (Dq - C') by ring]
  filter_upwards [hg, hΛ, hband, hsize.eventually_ge_atTop 1] with n hgn hΛn hb h1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hlam0 : 0 ≤ Λ n := by linarith
  have hW := AltAbsorb_Wneg_le d n hb hD
  have hP := AltAbsorb_one_le_P d n
  have hc5 := AltAbsorb_cCase5_nonneg k
  have hW0 : 0 ≤ (d.W n : ℝ) ^ (-(Dq - C')) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [show -Dq + C' = -(Dq - C') by ring]
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  set Pn : ℝ := 1 + Real.log Nn with hPn
  have hQ1 : 1 ≤ Nn ^ (2 * εΓ + 1) := Real.one_le_rpow h1 (by linarith)
  have hQ0 : 0 ≤ Nn ^ (2 * εΓ + 1) := by positivity
  have hA1 := AltAbsorb_A_le d n k hc hτ
  have hA2 : Nn ^ ((2 * (k : ℝ) + cPrec c k) * τ') ≤ Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1) :=
    Real.rpow_le_rpow_of_exponent_le h1 hA
  have hA3 : altQvA (d.L n) (d.W n) k c τ' ≤ Λ n * ((cCase5 k * 3 ^ (4 * k)) * Pn ^ (2 * k + 1) *
      Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) := by
    calc altQvA (d.L n) (d.W n) k c τ' ≤ (cCase5 k * 3 ^ (4 * k)) * Pn ^ (2 * k + 1) *
          Nn ^ ((2 * (k : ℝ) + cPrec c k) * τ') := hA1
      _ ≤ (cCase5 k * 3 ^ (4 * k)) * Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1) := by
          gcongr
      _ ≤ Λ n * ((cCase5 k * 3 ^ (4 * k)) * Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) :=
          le_mul_of_one_le_left (by positivity) hΛn
  have hM : 0 ≤ 2 + (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1) := by positivity
  have hB1 := AltAbsorb_B_le d n k hM
  have e1 : Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn = Λ n * Nn ^ (2 * εΓ + 1) := by
    rw [show 2 * εΓ + 1 = εΓ + εΓ + 1 by ring, Real.rpow_add hN0 (εΓ + εΓ) 1,
      Real.rpow_add hN0 εΓ εΓ, Real.rpow_one]; ring
  have hM2 : 2 + (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1) ≤ 4 * Λ n * Nn ^ (2 * εΓ + 1) := by
    rw [e1]; nlinarith [mul_nonneg hlam0 (sub_nonneg.2 hQ1), sub_nonneg.2 hΛn]
  have e2 : Nn ^ (((2 * k : ℕ)) : ℝ) * Nn ^ (2 * εΓ + 1) = Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1) := by
    rw [← Real.rpow_add hN0]; push_cast; ring_nf
  have hB3 : altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1) ≤
      Λ n * ((4 * cCase5 k) * Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) := by
    calc altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1)
        ≤ cCase5 k * Pn ^ (2 * k) * Nn ^ (((2 * k : ℕ)) : ℝ) *
          (2 + (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1)) := hB1
      _ ≤ cCase5 k * Pn ^ (2 * k) * Nn ^ (((2 * k : ℕ)) : ℝ) * (4 * Λ n * Nn ^ (2 * εΓ + 1)) := by
          gcongr
      _ = Λ n * ((4 * cCase5 k) * Pn ^ (2 * k) * (Nn ^ (((2 * k : ℕ)) : ℝ) * Nn ^ (2 * εΓ + 1))) := by
          ring
      _ = Λ n * ((4 * cCase5 k) * Pn ^ (2 * k) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) := by rw [e2]
      _ ≤ _ := by
          gcongr
          omega
  have hAB : altQvA (d.L n) (d.W n) k c τ' +
      altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1) ≤
      Λ n * ((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) * Pn ^ (2 * k + 1) *
        Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) := by
    have := add_le_add hA3 hB3
    refine this.trans (le_of_eq ?_)
    ring
  have hN2k : 0 ≤ Nn ^ (2 * k) := by positivity
  have hmain : (k : ℝ) * ((altQvA (d.L n) (d.W n) k c τ' +
      altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1)) * Nn ^ (2 * k) *
      (d.W n : ℝ) ^ (-(Dq - C'))) ≤ Λ n * ((k : ℝ) * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) * Nn ^ (2 * k) *
        Nn ^ (-(c * (Dq - C'))))) := by
    have h3 : (altQvA (d.L n) (d.W n) k c τ' +
        altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1)) * Nn ^ (2 * k) *
        (d.W n : ℝ) ^ (-(Dq - C')) ≤ Λ n * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) * Nn ^ (2 * k) *
        Nn ^ (-(c * (Dq - C')))) := by
      calc _ ≤ (Λ n * ((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) * Pn ^ (2 * k + 1) *
            Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1))) * Nn ^ (2 * k) * Nn ^ (-(c * (Dq - C'))) := by
            gcongr
        _ = _ := by ring
    calc _ ≤ (k : ℝ) * (Λ n * (((cCase5 k * 3 ^ (4 * k) + 4 * cCase5 k) *
        Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) * Nn ^ (2 * k) *
        Nn ^ (-(c * (Dq - C'))))) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg k)
      _ = _ := by ring
  have hsq := Real.sqrt_le_sqrt hmain
  rw [Real.sqrt_mul hlam0] at hsq
  have hsqr : Λ n ^ ((1 : ℝ) / 2) = Real.sqrt (Λ n) := (Real.sqrt_eq_rpow _).symm
  rw [hsqr]
  have hNk0 : 0 ≤ Nn ^ k := by positivity
  have hNe0 : 0 ≤ Nn ^ ε := by positivity
  calc Nn ^ ε * (Nn ^ k * Real.sqrt ((k : ℝ) * ((altQvA (d.L n) (d.W n) k c τ' +
        altQvB (d.L n) k (Nn ^ εΓ * (Nn ^ εΓ * Λ n) * Nn + 1)) * Nn ^ (2 * k) *
        (d.W n : ℝ) ^ (-(Dq - C')))))
      ≤ Nn ^ ε * (Nn ^ k * (Real.sqrt (Λ n) * Real.sqrt ((k : ℝ) * (((cCase5 k * 3 ^ (4 * k) +
        4 * cCase5 k) * Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) * Nn ^ (2 * k) *
        Nn ^ (-(c * (Dq - C'))))))) := by gcongr
    _ = Real.sqrt (Λ n) * (Nn ^ ε * (Nn ^ k * Real.sqrt ((k : ℝ) * (((cCase5 k * 3 ^ (4 * k) +
        4 * cCase5 k) * Pn ^ (2 * k + 1) * Nn ^ (2 * (k : ℝ) + 2 * εΓ + 1)) * Nn ^ (2 * k) *
        Nn ^ (-(c * (Dq - C'))))))) := by ring
    _ ≤ Real.sqrt (Λ n) * (Nn ^ ε₀ / 20) := mul_le_mul_of_nonneg_left hgn (Real.sqrt_nonneg _)
    _ = _ := by ring


/-! ## 4. The last step -/

/-- `η_u ≤ 1` for `|E| < 2`, `0 ≤ u`. -/
theorem AltAbsorb_etaT_le_one {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) : etaT E u ≤ 1 := by
  unfold etaT
  have h1 : (spectralM E).im ≤ 1 := by
    rw [spectralM_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
    linarith
  have h2 := spectralM_im_pos hE
  nlinarith

theorem AltAbsorb_T2_id (a q Y Cc : ℝ) (ha : a ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    a⁻¹ * Y * (Cc * q⁻¹) ^ (m + 1) = (a⁻¹ * q⁻¹) ^ (m + 2) * (Y * Cc ^ (m + 1) * a ^ (m + 1) * q) := by
  have hw : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have hr : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
  have h1 : a⁻¹ ^ (m + 2) * a ^ (m + 1) = a⁻¹ := by
    calc a⁻¹ ^ (m + 2) * a ^ (m + 1) = a⁻¹ * (a⁻¹ * a) ^ (m + 1) := by ring
      _ = a⁻¹ := by rw [hw, one_pow, mul_one]
  have h2 : q⁻¹ ^ (m + 2) * q = q⁻¹ ^ (m + 1) := by
    calc q⁻¹ ^ (m + 2) * q = q⁻¹ ^ (m + 1) * (q⁻¹ * q) := by ring
      _ = q⁻¹ ^ (m + 1) := by rw [hr, mul_one]
  refine Eq.symm ?_
  calc (a⁻¹ * q⁻¹) ^ (m + 2) * (Y * Cc ^ (m + 1) * a ^ (m + 1) * q)
      = (a⁻¹ ^ (m + 2) * a ^ (m + 1)) * (q⁻¹ ^ (m + 2) * q) * Y * Cc ^ (m + 1) := by ring
    _ = a⁻¹ * q⁻¹ ^ (m + 1) * Y * Cc ^ (m + 1) := by rw [h1, h2]
    _ = _ := by ring

theorem AltAbsorb_T1_id (w r S Γ Φ Cc : ℝ) (m : ℕ) :
    w * (S ^ m * (Γ * Φ * (w * r) ^ (m + 1))) * (Cc * r) ^ (m + 1) =
      Φ * (w * r) ^ (m + 2) * Γ * ((S * r) ^ m * Cc ^ (m + 1)) := by ring

/-- The last-step level `altLastLevel` at `k = m + 2`, bounded pointwise by two terms (the `Ξ_{k-1}` part and the `W^{-D'}` part), both of the form `M_v^{-k} · (...)`. -/
theorem AltAbsorb_last_pt {L W : ℕ} (m : ℕ) {E u : ℝ} (hL : 3 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {Γ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (hτ : 0 ≤ τ') :
    altLastLevel L W E u (m + 2) Γ Φ τ' D' ≤
      Φ * (scaleM L W E u)⁻¹ ^ (m + 2) * Γ * ((9 * ((W : ℝ) ^ τ') ^ 2) ^ m *
        ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1)) +
      (scaleM L W E u)⁻¹ ^ (m + 2) * (((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1) *
        (((W : ℝ) ^ 2 * (L : ℝ) ^ 2) ^ (m + 1) * (W : ℝ) ^ (-D'))) := by
  have hL1 : 1 ≤ L := by omega
  have hℓ1 := one_le_ellT hL1 hu0 hu1
  have hℓL := (ellT_pos_le hL1 hu1).2
  have hη0 := etaT_pos hE hu1
  have hη1 := AltAbsorb_etaT_le_one hE hu0
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith)
  have hKw : (1 : ℝ) ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hWr hτ
  have hMd : scaleM L W E u = (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u := rfl
  unfold altLastLevel
  rw [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 from rfl, hMd]
  set ℓ := ellT L u with hℓ
  set η := etaT E u with hη
  set X : ℝ := (W : ℝ) ^ τ' with hX
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlam : 0 ≤ (180 * 40002 ^ 2) * (1 + Real.log (L : ℝ)) := by positivity
  -- the two parts
  have hS : (2 * (ℓ * X) + 1) ^ 2 * (ℓ ^ 2)⁻¹ ≤ 9 * X ^ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have h1 : 2 * (ℓ * X) + 1 ≤ 3 * (ℓ * X) := by nlinarith
    calc (2 * (ℓ * X) + 1) ^ 2 ≤ (3 * (ℓ * X)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = 9 * X ^ 2 * ℓ ^ 2 := by ring
  have hT1 : (W ^ 2 * η)⁻¹ * (((2 * (ℓ * X) + 1) ^ 2) ^ m *
      (Γ * Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 1))) *
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 2) * Γ * ((9 * X ^ 2) ^ m *
        ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1)) := by
    have e : (W ^ 2 * η)⁻¹ * (((2 * (ℓ * X) + 1) ^ 2) ^ m *
        (Γ * Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 1))) *
        ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) =
        Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 2) * Γ * (((2 * (ℓ * X) + 1) ^ 2 * (ℓ ^ 2)⁻¹) ^ m *
        ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1)) := by
      rw [show (W : ℝ) ^ 2 * ℓ ^ 2 * η = ((W : ℝ) ^ 2 * η) * ℓ ^ 2 by ring,
        mul_inv ((W : ℝ) ^ 2 * η) (ℓ ^ 2)]
      exact AltAbsorb_T1_id _ _ _ _ _ _ m
    rw [e]
    have hM0 : 0 ≤ (W ^ 2 * ℓ ^ 2 * η)⁻¹ := by positivity
    gcongr
  have hT2 : (W ^ 2 * η)⁻¹ * (((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D')) *
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 2) * (((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1) *
        (((W : ℝ) ^ 2 * (L : ℝ) ^ 2) ^ (m + 1) * (W : ℝ) ^ (-D'))) := by
    have e : (W ^ 2 * η)⁻¹ * (((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D')) *
        ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) =
        (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 2) * (((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D') *
        ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1) * ((W : ℝ) ^ 2 * η) ^ (m + 1) * ℓ ^ 2) := by
      rw [show (W : ℝ) ^ 2 * ℓ ^ 2 * η = ((W : ℝ) ^ 2 * η) * ℓ ^ 2 by ring]
      have := AltAbsorb_T2_id ((W : ℝ) ^ 2 * η) (ℓ ^ 2) (((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D'))
        ((180 * 40002 ^ 2) * (1 + Real.log L)) (by positivity) (by positivity) m
      rw [this]; ring
    rw [e]
    have hM0 : 0 ≤ (W ^ 2 * ℓ ^ 2 * η)⁻¹ := by positivity
    have hWD : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
    have h1 : ((W : ℝ) ^ 2 * η) ^ (m + 1) ≤ ((W : ℝ) ^ 2) ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (W : ℝ)]) _
    have h2 : ℓ ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓL 2
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D') * ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1) *
          ((W : ℝ) ^ 2 * η) ^ (m + 1) * ℓ ^ 2
        ≤ ((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D') * ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1) *
          ((W : ℝ) ^ 2) ^ (m + 1) * (L : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hsplit : (W ^ 2 * η)⁻¹ * (((2 * (ℓ * X) + 1) ^ 2) ^ m *
      (Γ * Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 1)) + ((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D')) *
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) =
      (W ^ 2 * η)⁻¹ * (((2 * (ℓ * X) + 1) ^ 2) ^ m *
      (Γ * Φ * (W ^ 2 * ℓ ^ 2 * η)⁻¹ ^ (m + 1))) *
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) +
      (W ^ 2 * η)⁻¹ * (((L : ℝ) ^ 2) ^ m * (W : ℝ) ^ (-D')) *
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (ℓ ^ 2)⁻¹) ^ (m + 1) := by ring
  rw [hsplit]
  exact add_le_add hT1 hT2


/-- The last step: `altLastLevel ≤ (N^ε/10)(Λ^{1/2} + Φ) M_v^{-k}` at `Γ = N^{ε_Γ}` when `ε_Γ + τ'(k-2) < ε` and `k - 1 - c D' < ε`. -/
theorem AltAbsorb_ev_last (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    (hk : 2 ≤ k) {E v : ℕ → ℝ} (hE : ∀ n, |E n| < 2) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1)
    {τ' εΓ ε D' : ℝ} (hτ : 0 ≤ τ') (hD' : 0 ≤ D') (hεΓ : 0 ≤ εΓ)
    (hε1 : εΓ + τ' * ((k : ℝ) - 2) < ε) (hε2 : (k : ℝ) - 1 - c * D' < ε)
    {Λ Φ : ℕ → ℝ} (hΦ : ∀ n, 0 ≤ Φ n) (hΛ : ∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) :
    ∀ᶠ n : ℕ in atTop, altLastLevel (d.L n) (d.W n) (E n) (v n) k
      (((d.size n : ℕ) : ℝ) ^ εΓ) (Φ n) τ' D' ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 10 * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
        (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  push_cast at hε1 hε2
  have hT1 : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ εΓ * ((9 * ((d.W n : ℝ) ^ τ') ^ 2) ^ m *
      ((180 * 40002 ^ 2) * (1 + Real.log (d.L n : ℝ))) ^ (m + 1)) ≤ ((d.size n : ℕ) : ℝ) ^ ε / 20 := by
    refine AltAbsorb_ev_of_le d hsize (C := 9 ^ m * (180 * 40002 ^ 2) ^ (m + 1)) (m + 1)
      (a := εΓ + τ' * (m : ℝ)) (by linarith) (by norm_num) (fun n h1 => ?_)
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have h2 := NonAltEnd_Wpow_le d n (2 * m) hτ
    have e : τ' * ((2 * m : ℕ) : ℝ) / 2 = τ' * (m : ℝ) := by push_cast; ring
    rw [e] at h2
    have h3 := NonAltEnd_log_pow_le d n (m + 1)
    have hP := AltAbsorb_P_L_nonneg d n
    have hW0 : 0 ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have e2 : (9 * ((d.W n : ℝ) ^ τ') ^ 2) ^ m = 9 ^ m * ((d.W n : ℝ) ^ τ') ^ (2 * m) := by
      rw [mul_pow, ← pow_mul]
    rw [e2]
    calc ((d.size n : ℕ) : ℝ) ^ εΓ * (9 ^ m * ((d.W n : ℝ) ^ τ') ^ (2 * m) *
          ((180 * 40002 ^ 2) * (1 + Real.log (d.L n : ℝ))) ^ (m + 1))
        ≤ ((d.size n : ℕ) : ℝ) ^ εΓ * (9 ^ m * ((d.size n : ℕ) : ℝ) ^ (τ' * (m : ℝ)) *
          ((180 * 40002 ^ 2) ^ (m + 1) * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (m + 1))) := by
          rw [mul_pow]
          gcongr
      _ = _ := by
          rw [Real.rpow_add hN0 εΓ (τ' * (m : ℝ))]; ring
  have hT2 : ∀ᶠ n : ℕ in atTop, (((180 * 40002 ^ 2) * (1 + Real.log (d.L n : ℝ))) ^ (m + 1) *
      (((d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2) ^ (m + 1) * (d.W n : ℝ) ^ (-D'))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 20 := by
    refine AltAbsorb_ev_of_leQ d hsize (C := (180 * 40002 ^ 2) ^ (m + 1)) (m + 1)
      (a := ((m : ℝ) + 1) - c * D') (by linarith) (by norm_num) hband (fun n hb h1 => ?_)
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hW := AltAbsorb_Wneg_le d n hb hD'
    have h3 := NonAltEnd_log_pow_le d n (m + 1)
    have hP := AltAbsorb_P_L_nonneg d n
    have hsz := NonAltEnd_size_eq d n
    have hW0 : 0 ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [← hsz]
    calc ((180 * 40002 ^ 2) * (1 + Real.log (d.L n : ℝ))) ^ (m + 1) *
          (((d.size n : ℕ) : ℝ) ^ (m + 1) * (d.W n : ℝ) ^ (-D'))
        ≤ ((180 * 40002 ^ 2) ^ (m + 1) * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (m + 1)) *
          (((d.size n : ℕ) : ℝ) ^ (m + 1) * ((d.size n : ℕ) : ℝ) ^ (-(c * D'))) := by
          rw [mul_pow]
          gcongr
      _ = _ := by
          rw [NonAltEnd_npow_eq ((d.size n : ℕ) : ℝ) (m + 1)]
          have : ((d.size n : ℕ) : ℝ) ^ (((m + 1 : ℕ)) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(c * D')) =
              ((d.size n : ℕ) : ℝ) ^ (((m : ℝ) + 1) - c * D') := by
            rw [← Real.rpow_add hN0]; push_cast; ring_nf
          rw [this]
  filter_upwards [hT1, hT2, hΛ] with n h1 h2 hΛn
  have hlast := AltAbsorb_last_pt (L := d.L n) (W := d.W n) m (d.three_le_L n) (d.W_pos n) (hE n)
    (hv0 n) (hv1 n) (Γ := ((d.size n : ℕ) : ℝ) ^ εΓ) (Φ := Φ n) (τ' := τ') (D' := D')
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hΦ n) hτ
  have hMi : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ (m + 2) :=
    pow_nonneg (inv_nonneg.2 (scaleM_pos (by have := d.three_le_L n; omega) (d.W_pos n) (hE n) (hv1 n)).le) _
  have hNe : 0 ≤ ((d.size n : ℕ) : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hR : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛn (by norm_num)
  refine hlast.trans ?_
  have hΦn := hΦ n
  calc _ ≤ Φ n * (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ (m + 2) * (((d.size n : ℕ) : ℝ) ^ ε / 20) +
      (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ (m + 2) * (((d.size n : ℕ) : ℝ) ^ ε / 20) := by
        rw [mul_assoc (Φ n * _)]
        gcongr
    _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hNe hMi) (by linarith : 0 ≤ 2 * Λ n ^ ((1 : ℝ) / 2) + Φ n - 1)]


/-! ## 5. The theorem `altAbsorb` -/

/-- **The absorption hypothesis `AltAbsorb`** holds for every size sequence (the analogue of
`NonAltEnd_ev_ha1`-`ha3`, `NonAltEnd_ev_he1`-`he5`). -/
theorem altAbsorb : AltAbsorb d := by
  intro κ c τR E s v K k hNZ hk hκ hc hτR hE hs0 hsv hv1 hK0 hsize hband hrange Λ Φ hΦ hΛ ε D₁ C_P C'
    hε hD₁ hCP hC' hKN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  have hcP0 : 0 ≤ cPrec c k := by unfold cPrec; positivity
  have hden : 0 < 4 * (k : ℝ) + cPrec c k + 1 := by linarith
  have hδ : altDelta ε = ε / 100 := rfl
  have hδ0 : 0 < altDelta ε := by rw [hδ]; positivity
  have hτ0 : 0 ≤ altTau c k ε := by unfold altTau; positivity
  have hτd : altTau c k ε * (4 * (k : ℝ) + cPrec c k + 1) = altDelta ε := by
    unfold altTau; field_simp
  have hkτ : (k : ℝ) * altTau c k ε ≤ altDelta ε / 4 := by
    nlinarith [mul_nonneg hτ0 hcP0, hτ0]
  have hcPτ : (2 * (k : ℝ) + cPrec c k) * altTau c k ε ≤ altDelta ε := by
    nlinarith [mul_nonneg hτ0 hcP0, hτ0]
  have hcDb : c * altDb c k = 4 * (k : ℝ) + 8 := by unfold altDb; field_simp
  have hDb0 : 0 ≤ altDb c k := by unfold altDb; positivity
  have hcDq : c * (altDq c k C' - C') = 8 * (k : ℝ) + 10 := by unfold altDq; field_simp; ring
  have hDq0 : 0 ≤ altDq c k C' - C' := by unfold altDq; ring_nf; positivity
  have hCK : 10 * (k : ℝ) + 40 ≤ altCK c k D₁ C_P C' := by
    unfold altCK
    have : 0 ≤ (4 * (k : ℝ) + 5) / c := by positivity
    linarith
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hv0 : ∀ n, 0 ≤ v n := fun n => (hs0 n).trans (hsv n)
  have hDq1 : 0 ≤ altDq c k C' + 1 := by
    have := hDq0; linarith
  have h1 := AltAbsorb_ev_ha1 d hsize hk1 (τ' := altTau c k ε) (εq := altDelta ε) (ε₀ := ε) hτ0
    (by nlinarith)
  have h2 := AltAbsorb_ev_ha2 d hsize hk1 hκ hE (τ' := altTau c k ε) (εq := altDelta ε) (ε₀ := ε) hτ0
    (by nlinarith)
  have h3 := AltAbsorb_ev_ha3 d hsize hk1 (τ' := altTau c k ε) (εE := altDelta ε) (ε₀ := ε) hτ0
    (by nlinarith)
  have h4 := AltAbsorb_ev_ha4 d hsize hk1 hκ hE (τ' := altTau c k ε) (εE := altDelta ε) (ε₀ := ε) hτ0
    (by nlinarith)
  have h5 := AltAbsorb_ev_ha5 d hsize hκ hE (c := c) (τ' := altTau c k ε) (ε := altDelta ε)
    (εΓ := altDelta ε) (ε₀ := ε) hc hτ0 (by nlinarith)
  have h6 := AltAbsorb_ev_he1 d hsize hband (k := k) (Db := altDb c k) (εq := altDelta ε) (ε₀ := ε)
    hDb0 hδ0.le (by nlinarith)
  have h7 := AltAbsorb_ev_he2 d hsize hband (k := k) (Db := altDb c k) (εq := altDelta ε) (ε₀ := ε)
    hDb0 hδ0.le (by nlinarith)
  have h8 := AltAbsorb_ev_he3 d hsize (s := s) (v := v) (K := K) k (C_K := altCK c k D₁ C_P C')
    (ε₀ := ε) (by linarith) hs0 hsv hv1 hK0 hKN (by linarith)
  have h9 := AltAbsorb_ev_he45 d hsize hband (k := k) (Db := altDb c k) (εE := altDelta ε)
    (ε₀ := ε) (τ' := altTau c k ε) (a5 := 1) hDb0 hτ0 zero_le_one (by nlinarith) (by nlinarith)
  have h10 := AltAbsorb_ev_he45 d hsize hband (k := k) (Db := altDb c k) (εE := altDelta ε)
    (ε₀ := ε) (τ' := altTau c k ε) (a5 := 5) hDb0 hτ0 (by norm_num) (by nlinarith) (by nlinarith)
  have h11 := AltAbsorb_ev_he6 d hsize hc hband (k := k) (τ' := altTau c k ε) (ε := altDelta ε)
    (εΓ := altDelta ε) (ε₀ := ε) (Dq := altDq c k C') (C' := C') hτ0 hDq0 hδ0.le
    (by nlinarith) (by nlinarith) hΛ
  have h12 := AltAbsorb_ev_he7 d hsize k (D := (k : ℝ) + 1) (ε₀ := ε) (by linarith)
  have h13 := AltAbsorb_ev_last d hsize hband hk hE2 hv0 hv1 (τ' := altTau c k ε)
    (εΓ := altDelta ε) (ε := ε) (D' := altDq c k C' + 1) hτ0 hDq1 hδ0.le (by nlinarith)
    (by nlinarith [mul_nonneg hc.le hC']) hΦ hΛ
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] with n a1 a2 a3 a4 a5 a6 a7
    a8 a9 a10 a11 a12 a13
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, ?_, a10, a11, a12, a12⟩, a13⟩
  simpa using a9

end RBM.Ind
