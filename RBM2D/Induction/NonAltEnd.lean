/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.NonAltBudget
import RBM2D.Induction.GridAssemblyN

/-!
# The non-alternating grid endpoint `nonAltGridEnd`

Namespace `RBM.Ind`.  The argument parallels the one-dimensional formalization (the asymptotic
helpers, the absorption lemmas, the assembly at the exit time, and the endpoint), with the `d = 2`
data of `RBM2D.Induction.NonAltGood` and `RBM2D.Induction.NonAltBudget`.  Paper:
arXiv:2503.07606, Section 5, `lem:STOeq_NQ` and its proof.

## The statement and the choice of the exponents

`nonAltGridEnd : NonAltGridEnd d κ c τ C E s t` (`RBM2D.Induction.StoppedEndDefs`).  For fixed
`k ≥ 2`, `Λ, Φ`, `v`, `ε > 0`, `D₁ > 0` the exponents of `GridEndConcl` are `ε₁ = ε/8`,
`τ' = ε/(8k)`, `D'' = 4k/c`, `D' = D'' + 1` (so `D'' < D'`, the shift hypothesis) and
`C_K = D₁ + 2 C_P + 6k + 20 + 2k/c`, with `C_P ≥ 0` the maximum over the `2^k` sign vectors of the
constants of `yMomentsUnifN` (`NonAltEnd_yMomentsMax`: chosen before the grid).  Inside the budget:
`ε_q = ε/8`, `D_Y = D_t = k + 1`, `τ_K = 1`, final exponent `ε`.  The range exponent of the end
time is `τ_R = min τ 1` (`RangeCond` is monotone in the exponent, so `τ ≤ 1` need not be derived).

## Sections

0. asymptotic helpers (`C (1 + log x)^j x^a ≤ x^b` eventually for `a < b`); 1. facts on the sizes
and the constants `C_κ`, `A`; 2. the absorption lemmas `NonAltEnd_ev_ha1` to
`NonAltEnd_ev_he5` (the eight numerical hypotheses of `budgetNonAlt`), the regime facts `hM1`,
`hη`, `hΔN` and the shift hypothesis `hδ` (`NonAltEnd_ev_hδ`); 3. the assembly at the exit
time, per sign vector (`NonAltEnd_assembly`: `assembledN` at `goodExitTauN`); 4. the
collapsed window `v_n = s_n` (`NonAltEnd_collapse`); 5. the endpoint `nonAltGridEnd` (union bound
over the signs with `D₁ + 1`, `budgetNonAlt`, the initial supremum from `InitLK`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 0. Asymptotic helpers -/

section Asymp

/-- `C · x^a ≤ x^b` for all large real `x` when `a < b`. -/
theorem NonAltEnd_ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  have ht : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop 0] with x hx hx0
  have h1 : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

/-- `C · x^a (log x + 1) ≤ x^b` for all large real `x` when `a < b`. -/
theorem NonAltEnd_ev_rpow_log_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * (Real.log x + 1) ≤ x ^ b := by
  set δ := (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [NonAltEnd_ev_rpow_le (a := a + δ) (b := b) (by rw [hδ]; linarith)
    (max C 0 * (1 / δ + 1)), eventually_ge_atTop 1] with x hN hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hNδ : 1 ≤ x ^ δ := Real.one_le_rpow hx1 hδ0.le
  have hl : Real.log x + 1 ≤ (1 / δ + 1) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  have hCa : C * x ^ a ≤ max C 0 * x ^ a :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  have hM0 : 0 ≤ max C 0 * x ^ a := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
  calc C * x ^ a * (Real.log x + 1)
      ≤ max C 0 * x ^ a * (Real.log x + 1) := mul_le_mul_of_nonneg_right hCa (by linarith)
    _ ≤ max C 0 * x ^ a * ((1 / δ + 1) * x ^ δ) := mul_le_mul_of_nonneg_left hl hM0
    _ = max C 0 * (1 / δ + 1) * x ^ (a + δ) := by
        rw [Real.rpow_add hx0]; ring
    _ ≤ x ^ b := hN

/-- **Polylog absorption**: `C (1 + log x)^j x^a ≤ x^b` for all large real `x` when `a < b`. -/
theorem NonAltEnd_ev_polylog_le (j : ℕ) :
    ∀ {a b : ℝ}, a < b → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ^ j * x ^ a ≤ x ^ b := by
  induction j with
  | zero =>
    intro a b hab C
    filter_upwards [NonAltEnd_ev_rpow_le hab C] with x hx
    simpa using hx
  | succ j ih =>
    intro a b hab C
    set m := (a + b) / 2 with hm
    have ham : a < m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    filter_upwards [NonAltEnd_ev_rpow_log_le ham (max C 0), ih hmb 1, eventually_ge_atTop 1] with
      x h1 h2 hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hL : 0 ≤ (1 + Real.log x) ^ j := by positivity
    have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
    calc C * (1 + Real.log x) ^ (j + 1) * x ^ a
        ≤ max C 0 * (1 + Real.log x) ^ (j + 1) * x ^ a := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by positivity)) hxa
      _ = (1 + Real.log x) ^ j * (max C 0 * x ^ a * (Real.log x + 1)) := by ring
      _ ≤ (1 + Real.log x) ^ j * x ^ m := mul_le_mul_of_nonneg_left h1 hL
      _ = 1 * (1 + Real.log x) ^ j * x ^ m := by ring
      _ ≤ x ^ b := h2

end Asymp

/-! ## 1. Elementary facts on the sizes and the constants -/

section Facts

variable (d : Sizes)

theorem NonAltEnd_size_eq (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
  rw [Sizes.size_eq]; push_cast; ring

theorem NonAltEnd_one_le_W (n : ℕ) : (1 : ℝ) ≤ (d.W n : ℝ) := by
  exact_mod_cast d.W_pos n

theorem NonAltEnd_three_le_L (n : ℕ) : (3 : ℝ) ≤ (d.L n : ℝ) := by
  exact_mod_cast d.three_le_L n

theorem NonAltEnd_W_sq_le_size (n : ℕ) : (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  rw [NonAltEnd_size_eq]
  have h := NonAltEnd_three_le_L d n
  nlinarith [sq_nonneg (d.W n : ℝ), sq_nonneg ((d.L n : ℝ) - 3)]

theorem NonAltEnd_L_le_size (n : ℕ) : (d.L n : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  rw [NonAltEnd_size_eq]
  have h := NonAltEnd_three_le_L d n
  have hW := NonAltEnd_one_le_W d n
  nlinarith [mul_nonneg (sq_nonneg ((d.W n : ℝ) - 1)) (sq_nonneg (d.L n : ℝ)), sq_nonneg (d.W n : ℝ)]

theorem NonAltEnd_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) :=
  GoodEvent_one_le_size n

theorem NonAltEnd_W_le_sqrt (n : ℕ) :
    (d.W n : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h := NonAltEnd_W_sq_le_size d n
  calc (d.W n : ℝ) = ((d.W n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (Nat.cast_nonneg _)]
    _ ≤ ((d.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h (by norm_num)

theorem NonAltEnd_cCase1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cCase1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cCase1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

theorem NonAltEnd_cPair1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cPair1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cPair1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

/-- `(1 + log L)^j ≤ (1 + log N)^j`. -/
theorem NonAltEnd_log_pow_le (n j : ℕ) :
    (1 + Real.log (d.L n : ℝ)) ^ j ≤ (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ j := by
  have h3 := NonAltEnd_three_le_L d n
  have hlog : Real.log (d.L n : ℝ) ≤ Real.log ((d.size n : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (NonAltEnd_L_le_size d n)
  have hlog0 : 0 ≤ Real.log (d.L n : ℝ) := Real.log_nonneg (by linarith)
  exact pow_le_pow_left₀ (by linarith) (by linarith) j

/-- `(W^{τ})^m ≤ N^{τ m / 2}` for `τ ≥ 0` (from `W² ≤ N`). -/
theorem NonAltEnd_Wpow_le (n m : ℕ) {τw : ℝ} (hτw : 0 ≤ τw) :
    ((d.W n : ℝ) ^ τw) ^ m ≤ ((d.size n : ℕ) : ℝ) ^ (τw * (m : ℝ) / 2) := by
  have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) := Nat.cast_nonneg _
  have hsq : ((d.W n : ℝ) ^ 2) ^ (τw * (m : ℝ) / 2) ≤ ((d.size n : ℕ) : ℝ) ^ (τw * (m : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (NonAltEnd_W_sq_le_size d n) (by positivity)
  have e : ((d.W n : ℝ) ^ τw) ^ m = ((d.W n : ℝ) ^ 2) ^ (τw * (m : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0, ← Real.rpow_natCast ((d.W n : ℝ)) 2,
      ← Real.rpow_mul hW0]
    congr 1
    push_cast
    ring
  rw [e]
  exact hsq

/-- `C_κ ≤ c_1 (1 + log N)^k N^{τ' (k-1)}` (the constant of `kappaNonAlt` at `K_w = W^{τ'}`). -/
theorem NonAltEnd_cKap_le (n k : ℕ) (hk : 1 ≤ k) (κ : ℝ) {τw : ℝ} (hτw : 0 ≤ τw) :
    NonAltBudget_cKap d n k κ τw ≤
      cCase1 k κ * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
        ((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1)) := by
  unfold NonAltBudget_cKap
  have hc := NonAltEnd_cCase1_nonneg k κ
  have h1 := NonAltEnd_log_pow_le d n k
  have h2 := NonAltEnd_Wpow_le d n (2 * (k - 1)) hτw
  have e : τw * ((2 * (k - 1) : ℕ) : ℝ) / 2 = τw * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hk]; push_cast; ring
  rw [e] at h2
  have h3 : 0 ≤ (1 + Real.log (d.L n : ℝ)) ^ k := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ d.L n by linarith [NonAltEnd_three_le_L d n])
    positivity
  have h4 : 0 ≤ (d.W n : ℝ) ^ τw := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (by positivity) (by positivity)

/-- `A ≤ c_pair (1 + log N)^{2k} N^{τ' (2k-1)}` (the constant of `qvBdNonAlt`). -/
theorem NonAltEnd_aQv_le (n k : ℕ) (hk : 1 ≤ k) (κ : ℝ) {τw : ℝ} (hτw : 0 ≤ τw) :
    NonAltBudget_aQv d n k κ τw ≤
      cPair1 k κ * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (2 * k) *
        ((d.size n : ℕ) : ℝ) ^ (τw * ((2 * k : ℝ) - 1)) := by
  unfold NonAltBudget_aQv
  have hc := NonAltEnd_cPair1_nonneg k κ
  have h1 := NonAltEnd_log_pow_le d n (2 * k)
  have h2 := NonAltEnd_Wpow_le d n (2 * (2 * k - 1)) hτw
  have e : τw * ((2 * (2 * k - 1) : ℕ) : ℝ) / 2 = τw * ((2 * k : ℝ) - 1) := by
    have : 1 ≤ 2 * k := by omega
    rw [Nat.cast_mul, Nat.cast_sub this]; push_cast; ring
  rw [e] at h2
  have h3 : 0 ≤ (1 + Real.log (d.L n : ℝ)) ^ (2 * k) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ d.L n by linarith [NonAltEnd_three_le_L d n])
    positivity
  have h4 : 0 ≤ (d.W n : ℝ) ^ τw := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (by positivity) (by positivity)

/-- `Im m_E ≥ √(κ(4-κ))/2` in the bulk `|E| ≤ 2 - κ`. -/
theorem NonAltEnd_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- `(Im m_E)⁻¹ ≤ c₀⁻¹`. -/
theorem NonAltEnd_im_inv_le {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    ((spectralM E).im)⁻¹ ≤ (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ :=
  inv_anti₀ (AzumaProxyN_c0_pos_pub hκ hE) (NonAltEnd_im_ge hE)

end Facts

/-! ## 2. The absorption lemmas -/

section Absorb

variable (d : Sizes)

/-- `W^{-D} ≤ N^{-cD}` from `N^c ≤ W`, `D ≥ 0`. -/
theorem NonAltEnd_Wneg_le {W N c D : ℝ} (hN0 : 0 < N) (hcW : N ^ c ≤ W) (hD : 0 ≤ D) :
    W ^ (-D) ≤ N ^ (-(c * D)) := by
  have h1 : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hcW (by linarith : -D ≤ 0)
  rw [← Real.rpow_mul hN0.le] at h
  convert h using 2; ring

/-- (ha1) the initial-datum main term: `C_κ N^{ε₁} ≤ N^{ε}/6` when `ε₁ + τ'(k-1) < ε` (`d = 2`: `K_w = W^{τ'}` without the factor 4 and
`W² ≤ N` gives `N^{τ'(k-1)}`). -/
theorem NonAltEnd_ev_ha1 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) {τw ε₁ ε : ℝ}
    (hτw : 0 ≤ τw) (hε : τw * ((k : ℝ) - 1) + ε₁ < ε) :
    ∀ᶠ n : ℕ in atTop, NonAltBudget_cKap d n k κ τw * ((d.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 6 := by
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le k hε (6 * cCase1 k κ)),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have h1 := NonAltEnd_cKap_le d n k hk κ hτw
  have hE1 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  rw [Real.rpow_add hN0] at h
  calc _ ≤ cCase1 k κ * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
        ((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1)) * ((d.size n : ℕ) : ℝ) ^ ε₁ :=
        mul_le_mul_of_nonneg_right h1 hE1
    _ = (6 * cCase1 k κ * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
        (((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1)) * ((d.size n : ℕ) : ℝ) ^ ε₁)) / 6 := by ring
    _ ≤ _ := by linarith

/-- (ha2) the drift main term with the `log N` of `Σ Δ/η`: `((k-1)²+1) C_κ N^{2ε₁} (Im m)⁻¹ log N
≤ N^ε/12` when `2ε₁ + τ'(k-1) < ε`. -/
theorem NonAltEnd_ev_ha2 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ)
    {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) {τw ε₁ ε : ℝ} (hτw : 0 ≤ τw)
    (hε : τw * ((k : ℝ) - 1) + 2 * ε₁ < ε) :
    ∀ᶠ n : ℕ in atTop, (((k : ℝ) - 1) ^ 2 + 1) * NonAltBudget_cKap d n k κ τw *
        (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 12 := by
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc00 : 0 < c0 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  set a2 : ℝ := ((k : ℝ) - 1) ^ 2 + 1 with ha2
  have ha20 : 0 ≤ a2 := by rw [ha2]; positivity
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le (k + 1) hε
    (12 * (a2 * cCase1 k κ * c0⁻¹))), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have h1 := NonAltEnd_cKap_le d n k hk κ hτw
  have hc1 := NonAltEnd_cCase1_nonneg k κ
  have hlog0 : 0 ≤ Real.log ((d.size n : ℕ) : ℝ) := Real.log_nonneg hN1
  have hIm := NonAltEnd_im_inv_le hκ (hE n)
  have hIm0 : 0 ≤ ((spectralM (E n)).im)⁻¹ := inv_nonneg.2 (spectralM_im_pos (by
    have := hE n; linarith [abs_nonneg (E n)])).le
  have hLs : ((spectralM (E n)).im)⁻¹ * Real.log ((d.size n : ℕ) : ℝ) ≤
      c0⁻¹ * (1 + Real.log ((d.size n : ℕ) : ℝ)) := by
    calc _ ≤ c0⁻¹ * Real.log ((d.size n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hIm hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hc00.le)
  have hsq : (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 = ((d.size n : ℕ) : ℝ) ^ (2 * ε₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hpow0 : 0 ≤ (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 := by positivity
  have hLs0 : 0 ≤ ((spectralM (E n)).im)⁻¹ * Real.log ((d.size n : ℕ) : ℝ) := by positivity
  have hrp : ((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1) + 2 * ε₁) =
      ((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1)) * ((d.size n : ℕ) : ℝ) ^ (2 * ε₁) :=
    Real.rpow_add hN0 _ _
  rw [hrp] at h
  calc a2 * NonAltBudget_cKap d n k κ τw * (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        (((spectralM (E n)).im)⁻¹ * Real.log ((d.size n : ℕ) : ℝ))
      ≤ a2 * (cCase1 k κ * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ k *
          ((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1))) *
          (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          (c0⁻¹ * (1 + Real.log ((d.size n : ℕ) : ℝ))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ha20) hpow0)
          hLs hLs0 (by positivity)
    _ = (12 * (a2 * cCase1 k κ * c0⁻¹) * (1 + Real.log ((d.size n : ℕ) : ℝ)) ^ (k + 1) *
          (((d.size n : ℕ) : ℝ) ^ (τw * ((k : ℝ) - 1)) * ((d.size n : ℕ) : ℝ) ^ (2 * ε₁))) / 12 := by
        rw [hsq]; ring
    _ ≤ _ := by linarith

/-- (ha3) the quadratic-variation main term: `N^{ε_q + ε₁} √(k A (Ls + 1)) ≤ N^ε/12` when
`ε_q + ε₁ + τ'(2k-1)/2 < ε`. -/
theorem NonAltEnd_ev_ha3 (hsize : SizeTendsto d) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ)
    {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) {τw ε₁ εq ε : ℝ} (hτw : 0 ≤ τw)
    (hε : 2 * (εq + ε₁) + τw * ((2 * k : ℝ) - 1) < 2 * ε) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ εq * (((d.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * NonAltBudget_aQv d n k κ τw *
          ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 12 := by
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc00 : 0 < c0 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le (2 * k + 1) hε
    (144 * ((k : ℝ) * cPair1 k κ * (c0⁻¹ + 1)))), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have h1 := NonAltEnd_aQv_le d n k hk κ hτw
  have hc1 := NonAltEnd_cPair1_nonneg k κ
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hIm := NonAltEnd_im_inv_le hκ (hE n)
  have hLs : ((spectralM (E n)).im)⁻¹ * Real.log N + 1 ≤ (c0⁻¹ + 1) * (1 + Real.log N) := by
    have : ((spectralM (E n)).im)⁻¹ * Real.log N ≤ c0⁻¹ * Real.log N :=
      mul_le_mul_of_nonneg_right hIm hlog0
    nlinarith [inv_nonneg.2 hc00.le]
  have hA0 : 0 ≤ NonAltBudget_aQv d n k κ τw := by
    unfold NonAltBudget_aQv
    have : 0 ≤ (1 + Real.log (d.L n : ℝ)) ^ (2 * k) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ d.L n by linarith [NonAltEnd_three_le_L d n])
      positivity
    have : 0 ≤ (d.W n : ℝ) ^ τw := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  set Z' : ℝ := (k : ℝ) * (cPair1 k κ * (1 + Real.log N) ^ (2 * k) * N ^ (τw * ((2 * k : ℝ) - 1))) *
    ((c0⁻¹ + 1) * (1 + Real.log N)) with hZ'
  have hZ'0 : 0 ≤ Z' := by rw [hZ']; positivity
  have hZ : (k : ℝ) * NonAltBudget_aQv d n k κ τw *
      (((spectralM (E n)).im)⁻¹ * Real.log N + 1) ≤ Z' := by
    rw [hZ']
    have hLs0 : 0 ≤ ((spectralM (E n)).im)⁻¹ * Real.log N + 1 := by
      have := inv_nonneg.2 (spectralM_im_pos (by
        have := hE n; linarith [abs_nonneg (E n)] : |E n| < 2)).le
      positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hk0) hLs hLs0 (by positivity)
  have hX0 : 0 ≤ N ^ (εq + ε₁) := Real.rpow_nonneg hN0.le _
  have hX : N ^ εq * (N ^ ε₁ * Real.sqrt ((k : ℝ) * NonAltBudget_aQv d n k κ τw *
      (((spectralM (E n)).im)⁻¹ * Real.log N + 1))) ≤ N ^ (εq + ε₁) * Real.sqrt Z' := by
    rw [Real.rpow_add hN0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hZ) (by positivity)
  refine hX.trans ?_
  have e1 : Real.sqrt ((N ^ (εq + ε₁)) ^ 2 * Z') = N ^ (εq + ε₁) * Real.sqrt Z' := by
    rw [Real.sqrt_mul (sq_nonneg (N ^ (εq + ε₁))) Z', Real.sqrt_sq hX0]
  have e2 : (N ^ (εq + ε₁)) ^ 2 = N ^ (2 * (εq + ε₁)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hrp : N ^ (2 * (εq + ε₁) + τw * ((2 * k : ℝ) - 1)) =
      N ^ (2 * (εq + ε₁)) * N ^ (τw * ((2 * k : ℝ) - 1)) := Real.rpow_add hN0 _ _
  rw [hrp] at h
  have hN2 : N ^ (2 * ε) = (N ^ ε) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hbd : (N ^ (εq + ε₁)) ^ 2 * Z' ≤ (N ^ ε / 12) ^ 2 := by
    rw [e2, div_pow, ← hN2]
    have : (N ^ (2 * (εq + ε₁))) * Z' = (144 * ((k : ℝ) * cPair1 k κ * (c0⁻¹ + 1)) *
        (1 + Real.log N) ^ (2 * k + 1) *
        (N ^ (2 * (εq + ε₁)) * N ^ (τw * ((2 * k : ℝ) - 1)))) / 144 := by
      rw [hZ']; ring
    rw [this]
    have h144 : (12 : ℝ) ^ 2 = 144 := by norm_num
    rw [h144]
    linarith
  rw [← e1]
  calc Real.sqrt ((N ^ (εq + ε₁)) ^ 2 * Z') ≤ Real.sqrt ((N ^ ε / 12) ^ 2) := Real.sqrt_le_sqrt hbd
    _ = N ^ ε / 12 := Real.sqrt_sq (by positivity)

/-- Helper: `N^k` (natural power) and the real power `N^{(k:ℝ)}` agree. -/
theorem NonAltEnd_npow_eq (N : ℝ) (m : ℕ) : N ^ m = N ^ (m : ℝ) := (Real.rpow_natCast N m).symm

/-- (he1) the `W^{-D'}` tail of the initial datum: `N^{2k} W^{-D'} ≤ N^ε/6` when `2k - cD' < ε`. -/
theorem NonAltEnd_ev_he1 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    {D' ε : ℝ} (hD' : 0 ≤ D') (hε : (2 * k : ℝ) - c * D' < ε) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-D') ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 6 := by
  have h0 := fun x : ℝ => (NonAltEnd_ev_polylog_le 0 hε 6)
  filter_upwards [hband, hsize.eventually (NonAltEnd_ev_polylog_le 0 hε 6),
    hsize.eventually_ge_atTop 1] with n hW h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hWn := NonAltEnd_Wneg_le hN0 hW hD'
  simp only [pow_zero, mul_one] at h
  rw [NonAltEnd_npow_eq]
  have e : ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) * ((d.size n : ℕ) : ℝ) ^ (-(c * D')) =
      ((d.size n : ℕ) : ℝ) ^ ((2 * k : ℝ) - c * D') := by
    rw [← Real.rpow_add hN0]; push_cast; ring_nf
  calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) * ((d.size n : ℕ) : ℝ) ^ (-(c * D')) :=
        mul_le_mul_of_nonneg_left hWn (Real.rpow_nonneg hN0.le _)
    _ = ((d.size n : ℕ) : ℝ) ^ ((2 * k : ℝ) - c * D') := e
    _ ≤ _ := by linarith

/-- (he2) the far part of the drift kernel: `(2 C_κ + 1) N^{2k} W^{-D'} ≤ N^ε/12` when
`2k + τ'(k-1) - cD' < ε`. -/
theorem NonAltEnd_ev_he2 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    (hk : 1 ≤ k) (κ : ℝ) {τw D' ε : ℝ} (hτw : 0 ≤ τw) (hD' : 0 ≤ D')
    (hε : (2 * k : ℝ) - c * D' + τw * ((k : ℝ) - 1) < ε) :
    ∀ᶠ n : ℕ in atTop, (2 * NonAltBudget_cKap d n k κ τw + 1) * ((d.size n : ℕ) : ℝ) ^ (2 * k) *
        (d.W n : ℝ) ^ (-D') ≤ ((d.size n : ℕ) : ℝ) ^ ε / 12 := by
  filter_upwards [hband, hsize.eventually (NonAltEnd_ev_polylog_le k hε
    (12 * (2 * cCase1 k κ + 1))), hsize.eventually_ge_atTop 1] with n hW h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hWn := NonAltEnd_Wneg_le hN0 hW hD'
  have hc1 := NonAltEnd_cCase1_nonneg k κ
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h1 := NonAltEnd_cKap_le d n k hk κ hτw
  set Q : ℝ := (1 + Real.log N) ^ k * N ^ (τw * ((k : ℝ) - 1)) with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    have h1' : 1 ≤ (1 + Real.log N) ^ k := one_le_pow₀ (by linarith)
    have h2' : 1 ≤ N ^ (τw * ((k : ℝ) - 1)) := by
      refine Real.one_le_rpow hN1 (mul_nonneg hτw ?_)
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    nlinarith
  have hcK : NonAltBudget_cKap d n k κ τw ≤ cCase1 k κ * Q := by
    rw [hQ]; calc _ ≤ _ := h1
      _ = _ := by ring
  have hQ0 : 0 ≤ Q := by linarith
  have h2 : 2 * NonAltBudget_cKap d n k κ τw + 1 ≤ (2 * cCase1 k κ + 1) * Q := by nlinarith
  rw [NonAltEnd_npow_eq]
  set R : ℝ := N ^ (((2 * k : ℕ) : ℝ)) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg hN0.le _
  have hW0 : 0 ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hRW : R * (d.W n : ℝ) ^ (-D') ≤ R * N ^ (-(c * D')) := mul_le_mul_of_nonneg_left hWn hR0
  have e : R * N ^ (-(c * D')) = N ^ ((2 * k : ℝ) - c * D') := by
    rw [hR, ← Real.rpow_add hN0]; push_cast; ring_nf
  have e2 : N ^ ((2 * k : ℝ) - c * D' + τw * ((k : ℝ) - 1)) =
      N ^ ((2 * k : ℝ) - c * D') * N ^ (τw * ((k : ℝ) - 1)) := Real.rpow_add hN0 _ _
  rw [e2] at h
  calc (2 * NonAltBudget_cKap d n k κ τw + 1) * R * (d.W n : ℝ) ^ (-D')
      = (2 * NonAltBudget_cKap d n k κ τw + 1) * (R * (d.W n : ℝ) ^ (-D')) := by ring
    _ ≤ ((2 * cCase1 k κ + 1) * Q) * (N ^ ((2 * k : ℝ) - c * D')) := by
        refine mul_le_mul h2 (hRW.trans (le_of_eq e)) (mul_nonneg hR0 hW0) (by positivity)
    _ = (12 * (2 * cCase1 k κ + 1) * (1 + Real.log N) ^ k *
          (N ^ ((2 * k : ℝ) - c * D') * N ^ (τw * ((k : ℝ) - 1)))) / 12 := by rw [hQ]; ring
    _ ≤ _ := by linarith

/-- (he3) the far part of the quadratic variation: `N^{ε_q + k} √(k (A + 1) N^{2k} W^{-D''}) ≤ N^ε/12`
when `2(ε_q + k) + τ'(2k-1) + 2k - cD'' < 2ε`. -/
theorem NonAltEnd_ev_he3 (hsize : SizeTendsto d) {c : ℝ} (hband : Bandwidth d c) {k : ℕ}
    (hk : 1 ≤ k) (κ : ℝ) {τw D'' εq ε : ℝ} (hτw : 0 ≤ τw) (hD'' : 0 ≤ D'')
    (hε : 2 * (εq + k) + τw * ((2 * k : ℝ) - 1) + (2 * k : ℝ) - c * D'' < 2 * ε) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ εq * (((d.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * ((NonAltBudget_aQv d n k κ τw + 1) * ((d.size n : ℕ) : ℝ) ^ (2 * k) *
          (d.W n : ℝ) ^ (-D'')))) ≤ ((d.size n : ℕ) : ℝ) ^ ε / 12 := by
  filter_upwards [hband, hsize.eventually (NonAltEnd_ev_polylog_le (2 * k) hε
    (144 * ((k : ℝ) * (cPair1 k κ + 1)))), hsize.eventually_ge_atTop 1] with n hW h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hWn := NonAltEnd_Wneg_le hN0 hW hD''
  have hc1 := NonAltEnd_cPair1_nonneg k κ
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := NonAltEnd_aQv_le d n k hk κ hτw
  set Q : ℝ := (1 + Real.log N) ^ (2 * k) * N ^ (τw * ((2 * k : ℝ) - 1)) with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    have h1' : 1 ≤ (1 + Real.log N) ^ (2 * k) := one_le_pow₀ (by linarith)
    have h2' : 1 ≤ N ^ (τw * ((2 * k : ℝ) - 1)) := by
      refine Real.one_le_rpow hN1 (mul_nonneg hτw ?_)
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    nlinarith
  have hA : NonAltBudget_aQv d n k κ τw + 1 ≤ (cPair1 k κ + 1) * Q := by
    have : NonAltBudget_aQv d n k κ τw ≤ cPair1 k κ * Q := by
      rw [hQ]; calc _ ≤ _ := h1
        _ = _ := by ring
    nlinarith
  have hA0 : 0 ≤ NonAltBudget_aQv d n k κ τw + 1 := by
    have : 0 ≤ NonAltBudget_aQv d n k κ τw := by
      unfold NonAltBudget_aQv
      have : 0 ≤ (1 + Real.log (d.L n : ℝ)) ^ (2 * k) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ d.L n by linarith [NonAltEnd_three_le_L d n])
        positivity
      have : 0 ≤ (d.W n : ℝ) ^ τw := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  rw [NonAltEnd_npow_eq N (2 * k)]
  set R : ℝ := N ^ (((2 * k : ℕ) : ℝ)) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg hN0.le _
  have hW0 : 0 ≤ (d.W n : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hRW : R * (d.W n : ℝ) ^ (-D'') ≤ R * N ^ (-(c * D'')) := mul_le_mul_of_nonneg_left hWn hR0
  have e : R * N ^ (-(c * D'')) = N ^ ((2 * k : ℝ) - c * D'') := by
    rw [hR, ← Real.rpow_add hN0]; push_cast; ring_nf
  set Z' : ℝ := (k : ℝ) * ((cPair1 k κ + 1) * Q * N ^ ((2 * k : ℝ) - c * D'')) with hZ'
  have hZ'0 : 0 ≤ Z' := by rw [hZ']; positivity
  have hZ : (k : ℝ) * ((NonAltBudget_aQv d n k κ τw + 1) * R * (d.W n : ℝ) ^ (-D'')) ≤ Z' := by
    rw [hZ']
    refine mul_le_mul_of_nonneg_left ?_ hk0
    calc (NonAltBudget_aQv d n k κ τw + 1) * R * (d.W n : ℝ) ^ (-D'')
        = (NonAltBudget_aQv d n k κ τw + 1) * (R * (d.W n : ℝ) ^ (-D'')) := by ring
      _ ≤ ((cPair1 k κ + 1) * Q) * N ^ ((2 * k : ℝ) - c * D'') :=
          mul_le_mul hA (hRW.trans (le_of_eq e)) (mul_nonneg hR0 hW0) (by positivity)
      _ = _ := by ring
  have hX0 : 0 ≤ N ^ (εq + (k : ℝ)) := Real.rpow_nonneg hN0.le _
  have hX : N ^ εq * (N ^ k * Real.sqrt ((k : ℝ) * ((NonAltBudget_aQv d n k κ τw + 1) * R *
      (d.W n : ℝ) ^ (-D'')))) ≤ N ^ (εq + (k : ℝ)) * Real.sqrt Z' := by
    rw [Real.rpow_add hN0, ← mul_assoc, NonAltEnd_npow_eq N k]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hZ) (by positivity)
  refine hX.trans ?_
  have e1 : Real.sqrt ((N ^ (εq + (k : ℝ))) ^ 2 * Z') = N ^ (εq + (k : ℝ)) * Real.sqrt Z' := by
    rw [Real.sqrt_mul (sq_nonneg (N ^ (εq + (k : ℝ)))) Z', Real.sqrt_sq hX0]
  have e2 : (N ^ (εq + (k : ℝ))) ^ 2 = N ^ (2 * (εq + (k : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hN2 : N ^ (2 * ε) = (N ^ ε) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have hrp : N ^ (2 * (εq + k) + τw * ((2 * k : ℝ) - 1) + (2 * k : ℝ) - c * D'') =
      N ^ (2 * (εq + (k : ℝ))) * (N ^ (τw * ((2 * k : ℝ) - 1)) * N ^ ((2 * k : ℝ) - c * D'')) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  rw [hrp] at h
  have hbd : (N ^ (εq + (k : ℝ))) ^ 2 * Z' ≤ (N ^ ε / 12) ^ 2 := by
    rw [e2, div_pow, ← hN2]
    have : (N ^ (2 * (εq + (k : ℝ)))) * Z' = (144 * ((k : ℝ) * (cPair1 k κ + 1)) *
        (1 + Real.log N) ^ (2 * k) *
        (N ^ (2 * (εq + (k : ℝ))) * (N ^ (τw * ((2 * k : ℝ) - 1)) * N ^ ((2 * k : ℝ) - c * D'')))) /
          144 := by rw [hZ', hQ]; ring
    rw [this]
    have h144 : (12 : ℝ) ^ 2 = 144 := by norm_num
    rw [h144]
    linarith
  rw [← e1]
  calc Real.sqrt ((N ^ (εq + (k : ℝ))) ^ 2 * Z') ≤ Real.sqrt ((N ^ ε / 12) ^ 2) :=
        Real.sqrt_le_sqrt hbd
    _ = N ^ ε / 12 := Real.sqrt_sq (by positivity)

/-- (he4, he5) the `Y` and step-error thresholds: `N^k N^{-D} ≤ N^ε/6` when `k - D < ε` (used with
`D = D_Y` and `D = D_t`). -/
theorem NonAltEnd_ev_he4 (hsize : SizeTendsto d) (k : ℕ) {D ε : ℝ} (hε : (k : ℝ) - D < ε) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D) ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 6 := by
  filter_upwards [hsize.eventually (NonAltEnd_ev_polylog_le 0 hε 6),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  simp only [pow_zero, mul_one] at h
  rw [NonAltEnd_npow_eq, ← Real.rpow_add hN0]
  have e : (k : ℝ) + -D = (k : ℝ) - D := by ring
  rw [e]
  linarith

theorem NonAltEnd_ev_he5 (hsize : SizeTendsto d) (k : ℕ) {D ε : ℝ} (hε : (k : ℝ) - D < ε) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D) ≤
      ((d.size n : ℕ) : ℝ) ^ ε / 6 :=
  NonAltEnd_ev_he4 d hsize k hε

/-! ### The regime hypotheses `hM1`, `hη`, `hΔN` and the shift hypothesis `hδ` -/

/-- `η_u⁻¹ ≤ N^{1-τ}/c₀` for `u ≤ t`, in the bulk, under the range condition `N^{-1+τ} ≤ 1 - t`. -/
theorem NonAltEnd_etaT_inv_le {κ E u t τR N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hut : u ≤ t) (hN0 : 0 < N) (hR : N ^ (-1 + τR) ≤ 1 - t) :
    (etaT E u)⁻¹ ≤ N ^ (1 - τR) / (Real.sqrt (κ * (4 - κ)) / 2) := by
  have hc0 := AzumaProxyN_c0_pos_pub hκ hE
  have hm := NonAltEnd_im_ge hE
  have hpos : 0 < N ^ (-1 + τR) := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (-1 + τR) ≤ 1 - u := by linarith
  have hη : N ^ (-1 + τR) * (Real.sqrt (κ * (4 - κ)) / 2) ≤ etaT E u := by
    unfold etaT
    exact mul_le_mul h1 hm hc0.le (by linarith)
  calc (etaT E u)⁻¹ ≤ (N ^ (-1 + τR) * (Real.sqrt (κ * (4 - κ)) / 2))⁻¹ :=
        inv_anti₀ (mul_pos hpos hc0) hη
    _ = N ^ (1 - τR) / (Real.sqrt (κ * (4 - κ)) / 2) := by
        rw [mul_inv, show (-1 + τR) = -(1 - τR) by ring, Real.rpow_neg hN0.le, inv_inv]
        exact (div_eq_mul_inv _ _).symm

/-- (`hM1`) `1 ≤ M_v` eventually, from `Im m N^{min(2c, τ)} ≤ M_v` (`scaleM_etaT_of_range`). -/
theorem NonAltEnd_ev_hM1 (hsize : SizeTendsto d) {κ c τR : ℝ} (hκ : 0 < κ) {E v : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (hc : 0 < c) (hτR : 0 < τR) (hv1 : ∀ n, v n < 1)
    (hband : Bandwidth d c) (hrange : RangeCond d τR v) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n) := by
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc00 : 0 < c0 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  have hmin : 0 < min (2 * c) τR := lt_min (by linarith) hτR
  filter_upwards [hband, hrange, hsize.eventually (NonAltEnd_ev_rpow_le (a := 0) hmin c0⁻¹),
    hsize.eventually_ge_atTop 1] with n hW hR hbig hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hE2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have h := (scaleM_etaT_of_range (L := d.L n) (W := d.W n) (E := E n) (c := c) (τ := τR)
    (t := v n) (by have := d.three_le_L n; omega) (d.W_pos n) hE2 hc hτR (hv1 n) hW hR).1
  have hIm := NonAltEnd_im_ge (hE n)
  rw [Real.rpow_zero, mul_one] at hbig
  have hP : 1 ≤ c0 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τR) := by
    have := mul_le_mul_of_nonneg_left hbig hc00.le
    rwa [mul_inv_cancel₀ hc00.ne'] at this
  calc (1 : ℝ) ≤ c0 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τR) := hP
    _ ≤ (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τR) :=
        mul_le_mul_of_nonneg_right hIm (Real.rpow_nonneg hN0.le _)
    _ ≤ _ := h

/-- (`hη`) `η_v⁻¹ ≤ N` eventually, from `η_v⁻¹ ≤ N^{1-τ}/c₀` and `N^τ ≥ c₀⁻¹`. -/
theorem NonAltEnd_ev_hη (hsize : SizeTendsto d) {κ τR : ℝ} (hκ : 0 < κ) {E v : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (hτR : 0 < τR) (hrange : RangeCond d τR v) :
    ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc00 : 0 < c0 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  filter_upwards [hrange, hsize.eventually (NonAltEnd_ev_rpow_le (a := 0) hτR c0⁻¹),
    hsize.eventually_ge_atTop 1] with n hR hbig hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have h := NonAltEnd_etaT_inv_le hκ (hE n) le_rfl hN0 hR
  rw [Real.rpow_zero, mul_one] at hbig
  calc (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τR) / c0 := h
    _ = ((d.size n : ℕ) : ℝ) ^ (1 - τR) * c0⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τR) * ((d.size n : ℕ) : ℝ) ^ τR :=
        mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hN0.le _)
    _ = ((d.size n : ℕ) : ℝ) := by
        rw [← Real.rpow_add hN0]; simp

/-- `Δ ≤ N^{-C_K}` on a grid with `N^{C_K} ≤ K n` and `v - s ≤ 1`. -/
theorem NonAltEnd_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (GoodEvent_one_le_size n)
  have hpos : 0 < ((d.size n : ℕ) : ℝ) ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hK0 : (0 : ℝ) < K n := lt_of_lt_of_le hpos hK
  unfold gridStep
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc v n - s n ≤ 1 := hvs
    _ = (((d.size n : ℕ) : ℝ) ^ C_K)⁻¹ * ((d.size n : ℕ) : ℝ) ^ C_K :=
        (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (((d.size n : ℕ) : ℝ) ^ C_K)⁻¹ * (K n : ℝ) :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- (`hΔN`) `Δ N ≤ 1` for `C_K ≥ 1`. -/
theorem NonAltEnd_hΔN {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ} (hC : 1 ≤ C_K)
    (hK : ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n * ((d.size n : ℕ) : ℝ) ≤ 1 := by
  have hN1 := GoodEvent_one_le_size (d := d) n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  have h := NonAltEnd_step_le d hK hvs
  calc gridStep s v K n * ((d.size n : ℕ) : ℝ)
      ≤ ((d.size n : ℕ) : ℝ) ^ (-C_K) * ((d.size n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h hN0.le
    _ = ((d.size n : ℕ) : ℝ) ^ (1 - C_K) := by
        rw [show (1 - C_K) = 1 + (-C_K) by ring, Real.rpow_add hN0, Real.rpow_one]; ring
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

/-- `K Δ = v - s ≤ 1`. -/
theorem NonAltEnd_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0)
    (hvs : v n - s n ≤ 1) : (K n : ℝ) * gridStep s v K n ≤ 1 := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']
  exact hvs

/-- The one-step increment of the grid times is `Δ`. -/
theorem NonAltEnd_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- The shift error, with `η_{u'}⁻¹ ≤ B`: `eeShiftErr ≤ (W² L²) k (2k+2) B^{2k+3} (u' - u)`. -/
theorem NonAltEnd_eeShiftErr_le {L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
    (hη0 : 0 ≤ (etaT E u')⁻¹) (hB : (etaT E u')⁻¹ ≤ B) (hΔ : 0 ≤ u' - u) :
    eeShiftErr L W E k u u' ≤
      (W : ℝ) ^ 2 * ((k : ℝ) * ((L : ℝ) ^ 2 * (((2 * k + 2 : ℕ) : ℝ) *
        (B ^ (2 * k + 2 + 1) * (u' - u))))) := by
  unfold eeShiftErr loopShiftErr
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWi : ((W : ℝ)⁻¹ ^ 2) ^ (2 * k + 2 - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hW1))
  have hWi0 : 0 ≤ ((W : ℝ)⁻¹ ^ 2) ^ (2 * k + 2 - 1) := by positivity
  have h1 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) ≤ B ^ (2 * k + 2 + 1) := pow_le_pow_left₀ hη0 hB _
  have h2 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * ((W : ℝ)⁻¹ ^ 2) ^ (2 * k + 2 - 1) * (u' - u) ≤
      B ^ (2 * k + 2 + 1) * (u' - u) := by
    calc _ ≤ (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * 1 * (u' - u) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWi (by positivity)) hΔ
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right h1 hΔ
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  gcongr

/-- (`hδ`, the shift hypothesis of `subGaussStop_nonAlt`) `W^{-D'} + eeShiftErr(u_j, u_{j+1}) ≤
W^{-D''}` for `D' = D'' + 1`, every `j < K n`, eventually: `Δ ≤ N^{-C_K}`, `η⁻¹ ≤ N^{1-τ}/c₀`
(`RangeCond`), `W ≥ 2`, `W ≤ N^{1/2}` and `1 + (2k+3)(1-τ) + D''/2 < C_K`. -/
theorem NonAltEnd_ev_hδ (hsize : SizeTendsto d) {κ c τR C_K D'' : ℝ} (k : ℕ) (hκ : 0 < κ)
    {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| ≤ 2 - κ) (hc : 0 < c)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hband : Bandwidth d c) (hrange : RangeCond d τR v) (hD'' : 0 ≤ D'')
    (hCK : 1 + (2 * (k : ℝ) + 3) * (1 - τR) + D'' / 2 < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ j < K n,
      (d.W n : ℝ) ^ (-(D'' + 1)) + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
        (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-D'') := by
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc00 : 0 < c0 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  set C1 : ℝ := (k : ℝ) * ((2 * k + 2 : ℕ) : ℝ) * (c0⁻¹) ^ (2 * k + 3) with hC1
  have hexp : 1 + (1 - τR) * (2 * (k : ℝ) + 3) + D'' / 2 - C_K < 0 := by linarith
  filter_upwards [hband, hrange, hKN, hsize.eventually (NonAltEnd_ev_rpow_le hexp (2 * C1)),
    hsize.eventually (NonAltEnd_ev_rpow_le (a := 0) hc 2), hsize.eventually_ge_atTop 1] with
    n hW hR hK hbig hW2 hN1
  intro j hj
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  rw [Real.rpow_zero, mul_one] at hW2
  have hW2' : (2 : ℝ) ≤ (d.W n : ℝ) := hW2.trans hW
  have hWpos : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ N ^ (-C_K) := NonAltEnd_step_le d hK hvs
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n :=
    (GoodEvent_gridTime_le (K := K) (hsv n) (show j + 1 ≤ K n by omega))
  have hdiff := NonAltEnd_gridTime_succ_sub s v K n j
  have hηB := NonAltEnd_etaT_inv_le hκ (hE n) hu'v hN0 hR
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := by
    have := etaT_pos (by have := hE n; linarith [abs_nonneg (E n)] : |E n| < 2)
      (hu'v.trans_lt (hv1 n))
    positivity
  have hee := NonAltEnd_eeShiftErr_le (L := d.L n) (W := d.W n) (d.W_pos n) (E := E n) k
    (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηB (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  -- the bound `eeShiftErr ≤ C1 N^{1 + θ(2k+3) - C_K}`
  set B : ℝ := N ^ (1 - τR) / c0 with hB
  have hBpow : B ^ (2 * k + 2 + 1) = N ^ ((1 - τR) * (2 * (k : ℝ) + 3)) * (c0⁻¹) ^ (2 * k + 3) := by
    rw [hB, div_eq_mul_inv, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 2
    · push_cast; ring_nf
  have hsz : (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2) = N := (NonAltEnd_size_eq d n).symm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hBp0 : 0 ≤ B ^ (2 * k + 2 + 1) := by positivity
  have hmain : eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
      C1 * N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) := by
    refine hee.trans ?_
    have e : (d.W n : ℝ) ^ 2 * ((k : ℝ) * ((d.L n : ℝ) ^ 2 * (((2 * k + 2 : ℕ) : ℝ) *
        (B ^ (2 * k + 2 + 1) * gridStep s v K n)))) =
        ((d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2) * ((k : ℝ) * (((2 * k + 2 : ℕ) : ℝ) *
          (B ^ (2 * k + 2 + 1) * gridStep s v K n))) := by ring
    rw [e, hsz]
    calc N * ((k : ℝ) * (((2 * k + 2 : ℕ) : ℝ) * (B ^ (2 * k + 2 + 1) * gridStep s v K n)))
        ≤ N * ((k : ℝ) * (((2 * k + 2 : ℕ) : ℝ) * (B ^ (2 * k + 2 + 1) * N ^ (-C_K)))) := by
          gcongr
      _ = C1 * N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) := by
          rw [hBpow, hC1]
          have : N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) =
              N * (N ^ ((1 - τR) * (2 * (k : ℝ) + 3)) * N ^ (-C_K)) := by
            rw [← Real.rpow_add hN0, show (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) =
              1 + ((1 - τR) * (2 * (k : ℝ) + 3) + -C_K) by ring, Real.rpow_add hN0, Real.rpow_one]
          rw [this]; ring
  -- the comparison with `W^{-D''}`
  have hWD : N ^ (-(D'' / 2)) ≤ (d.W n : ℝ) ^ (-D'') := by
    have h1 := Real.rpow_le_rpow_of_nonpos hWpos (NonAltEnd_W_le_sqrt d n) (by linarith : -D'' ≤ 0)
    rw [← Real.rpow_mul hN0.le] at h1
    convert h1 using 2; ring
  have hbig' : C1 * N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) ≤ N ^ (-(D'' / 2)) / 2 := by
    have h1 : N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) + D'' / 2 - C_K) =
        N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) * N ^ (D'' / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [h1, Real.rpow_zero] at hbig
    have hpD : 0 < N ^ (D'' / 2) := Real.rpow_pos_of_pos hN0 _
    have h2 : N ^ (-(D'' / 2)) = 1 / N ^ (D'' / 2) := by rw [Real.rpow_neg hN0.le, one_div]
    rw [h2, div_div, le_div_iff₀ (by positivity)]
    calc C1 * N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) * (N ^ (D'' / 2) * 2)
        = 2 * C1 * (N ^ (1 + (1 - τR) * (2 * (k : ℝ) + 3) - C_K) * N ^ (D'' / 2)) := by ring
      _ ≤ 1 := hbig
  have hWm1 : (d.W n : ℝ) ^ (-(D'' + 1)) ≤ (d.W n : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hpos : 0 ≤ (d.W n : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
    have : ((d.W n : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hW2'
    calc (d.W n : ℝ) ^ (-D'') * ((d.W n : ℝ))⁻¹ ≤ (d.W n : ℝ) ^ (-D'') * (1 / 2) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  linarith

end Absorb

/-! ## 3. The assembly at the exit time -/

section Assembly

/-- The step error of `gridDriftN` is nonnegative (the proof of `stepErrN_nonneg'`). -/
theorem NonAltEnd_stepErrN_nonneg {L W : ℕ} {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2) (hu1 : u < 1)
    (hv1 : v < 1) (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) : 0 ≤ stepErrN L W E k u v Δ Bk := by
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hv : 0 < 1 - v := by linarith
  have h1 : 0 ≤ envConst L W E k v * Δ ^ ((3 : ℝ) / 2) := by
    unfold envConst
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hΔ _)
  have h2 : 0 ≤ kStepC L W k Bk * Δ ^ 2 := by
    unfold kStepC; positivity
  have h3 : 0 ≤ uStepC k Δ v := by
    unfold uStepC
    have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
    have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
      have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
      simpa using this
    have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
    nlinarith
  have h4 : 0 ≤ (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk := by
    have : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  unfold stepErrN
  have := mul_nonneg h3 h4
  linarith

variable (d : Sizes)

/-- **The assembly at the exit time, for one sign vector.**  With `τ =
goodExitTauN` at the levels `(Γ, Λ, Φ)`, `assembledN` (with `D₁`, `D = D_Y`, `ε = ε_q`,
`C_P`, `C_K`) applied to the stopped Duhamel process of `AvecN`, with the data of `NonAltGood`
(`nonAltCls`, `kappaNonAlt`, `epsNonAlt`, `dDriftNonAlt`, `cQVNonAlt`, the sub-Gaussian proxy
`subGaussStop_nonAlt`), the `Y` moments (`hY`: `yMomentsUnifN`) and the envelope of the step error
(`gridDriftN_envelope`), gives, eventually in `n` and for every non-alternating `σ` on a strict
window `s_n < v_n`, an event `G` of probability `≥ 1 - N^{-D₁}` on which the terminal bound
`‖A_K(a)‖ ≤ assembledRHSNonAlt` holds as soon as the grid walk stays in `GoodSetN`.  The shift
hypothesis `hδ` is an explicit premise at the size index `n` (supplied by `NonAltEnd_ev_hδ`). -/
theorem NonAltEnd_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) [NeZero k]
    (hk : 2 ≤ k) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hsize : SizeTendsto d)
    (Γ Λ Φ : ℕ → ℝ) (hΓ : ∀ n, 0 ≤ Γ n) (hΛ : ∀ n, 0 ≤ Λ n) (hΦ : ∀ n, 0 ≤ Φ n)
    {τw D' D'' D_Y τK εq D₁ C_P C_K : ℝ} (hτw : 0 ≤ τw) (hτK : 0 < τK) (hεq : 0 < εq)
    (hCK0 : 0 ≤ C_K) (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
        YMomentBoundsN d (E n) σ (gridTime s v K n) τ (K n)
          (fun j ω => YvecN d E s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2)) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, (∃ i : Fin k, σ i = σ (i + 1)) → s n < v n →
      (∀ j < K n, (d.W n : ℝ) ^ (-D') + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
        (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-D'')) →
      ∃ G : Set (PathΩ d), (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
            (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τw D') →
          ∀ a : Fin k → Z2 (d.L n),
            ‖AvecN d E s v K n (K n) σ ω a‖ ≤
              assembledRHSNonAlt d E s v K n k κ τw Γ Λ Φ D' D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN d E s v K n 0 σ ω b‖) a := by
  have hA := assembledN d hsize k εq hεq D_Y D₁ C_P C_K hCK0 hCK
  have hEnv : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP d), ∀ j, j < K n →
      ∀ a : Fin k → Z2 (d.L n),
      ‖predIncN d E s v K n j σ ω a - (gridStep s v K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s v K n j)
              (pathH d s v K n j ω) l (loopOf σ a) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω)
              (loopOf σ a) +
            egtN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω)
              (loopOf σ a))‖ ≤
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) :=
    fun σ => gridDriftN_envelope κ hκ k hk τK hτK hsize hE hs0 hsv hv1 hK0 σ
  filter_upwards [hA, hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv] with
    n hAn hKNn hKUn hYn hEnvn
  intro σ hσ hsvn hδn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  have hEn2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-C_K) := NonAltEnd_step_le d hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := NonAltEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ =>
    GoodEvent_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) (hsv n) hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m :=
    fun i m him _ => GoodEvent_gridTime_mono (hsv n) him
  have hWτ0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ τw := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKw : (1 : ℝ) ≤ (d.W n : ℝ) ^ τw := Real.one_le_rpow (NonAltEnd_one_le_W d n) hτw
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := NonAltEnd_one_le_size d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hτmeas : ∀ j, MeasurableSet[filt d j]
      {ω | j < goodExitTauN d E s v K k Γ Λ Φ τw D' n ω} :=
    goodExitMeasN d E s v K n k Γ Λ Φ τw D'
  have hmem : ∀ (ω : PathΩ d) (j : ℕ), j < goodExitTauN d E s v K k Γ Λ Φ τw D' n ω →
      pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n)
        (Φ n) τw D' := fun ω j hj => mem_of_lt_gridExitTauN hj
  -- the data of the assembly
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ d → ℕ := goodExitTauN d E s v K k Γ Λ Φ τw D' n with hτdef
  set A0 : PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun ω => AvecN d E s v K n 0 σ ω with hA0
  set Dr : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω =>
    driftTensor (d.L n) (d.W n) (E n) (u j) (pathH d s v K n j ω) σ with hDr
  set Z : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω => ZvecN d E s v K n j σ ω with hZ
  set Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω => YvecN d E s v K n j σ ω with hY'
  set R : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω =>
    predIncN d E s v K n j σ ω - ((Δ : ℝ) : ℂ) • Dr j ω with hR
  set Af : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun m ω =>
    Ugen (d.L n) (E n) σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) (E n) σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) with hAf
  set stepE : ℕ → ℝ := fun j => stepErrN (d.L n) (d.W n) (E n) k (u j) (u (j + 1)) Δ
    (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) with hstepE
  have hZmeas : ∀ j, StronglyMeasurable[filt d (j + 1)] (Z j) := fun j =>
    stronglyMeasurable_ZvecN d E s v K n j σ
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Z2 (d.L n)) (j : ℕ), j < m →
      SubGaussStopN d (E n) σ u τ Z m a j (cQVNonAlt d E s v K n k κ Γ Λ τw D'' m a j) :=
    fun m hm a j hj => subGaussStop_nonAlt hκ hE hs0 hsv hv1 n k hk hσ Γ Λ Φ (hΓ n) (hΛ n) τw D'
      D'' hτw m hm a j hj (hδn j (lt_of_lt_of_le hj hm))
  have hbundle : GridAssemblyHypN d (n := n) (k := k) (E n) σ u τ Δ (K n)
      (nonAltCls (d.L n) ((d.W n : ℝ) ^ τw) u) A0 Af Dr Z Y R
      (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τw) u) (epsNonAlt k u) ((d.W n : ℝ) ^ (-D'))
      (fun j _ => dDriftNonAlt (d.L n) (d.W n) (E n) (u j) k (Γ n) (Φ n) D')
      (fun _ _ => (d.W n : ℝ) ^ (-D'))
      (fun m a j => cQVNonAlt d E s v K n k κ Γ Λ τw D'' m a j)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE := {
    hE := hEn2.le
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Eventually.of_forall fun ω => rfl
    hκ0 := nonAlt_hκ0 k κ _ hWτ0 hu1
    hε0 := nonAlt_hε0 k hu1
    hker := nonAlt_hker hk (d.three_le_L n) hκ (hE n) hσ hu0 hmono hu1 hKw
    hδ0 := Real.rpow_nonneg (Nat.cast_nonneg _) _
    hA0cls := nonAlt_hA0cls (n := n) (by omega) σ Γ Λ Φ τw D' τ hmem
    hdDrift0 := fun ω j hj => nonAlt_hdDrift0 (E := E) (s := s) (v := v) (K := K) (n := n) (k := k)
      hEn2 (hsv n) (hv1 n) Γ Φ (hΓ n) (hΦ n) D' ω j hj
    hδD0 := fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    hdrift := nonAlt_hdrift (n := n) σ Γ Λ Φ τw D' τ hmem
    hDcls := nonAlt_hDcls (n := n) (hs0 n) (hsv n) (hv1 n) σ Γ Λ Φ τw D' τ hmem
    hc_pos := cQVNonAlt_sum_pos n k hEn2 (by omega) hsvn (hv1 n) hKn Γ Λ (hΓ n) (hΛ n) τw D''
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => NonAltEnd_stepErrN_nonneg hEn2 (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
      (by
        have := etaT_pos hEn2 (hu1 (j + 1) hj)
        positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => by
      have h := hω j hj b
      simp only [hR, hDr, hstepE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, driftTensor]
      exact h }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) (E n) σ u τ Δ (nonAltCls (d.L n) ((d.W n : ℝ) ^ τw) u) A0 Af
    Dr Z Y R (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τw) u) (epsNonAlt k u)
    ((d.W n : ℝ) ^ (-D')) (fun j _ => dDriftNonAlt (d.L n) (d.W n) (E n) (u j) k (Γ n) (Φ n) D')
    (fun _ _ => (d.W n : ℝ) ^ (-D'))
    (fun m a j => cQVNonAlt d E s v K n k κ Γ Λ τw D'' m a j)
    (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE P hK1 hKUn hΔ hKΔ hP0 hPle
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauN_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hex := hexp_at_goodExit (d := d) (fun n => by have := hE n; linarith [abs_nonneg (E n)]) hs0
    hsv hv1 hK0 n k σ Γ Λ Φ τw D' ω
  have hAeq : Af (K n) ω = AvecN d E s v K n (K n) σ ω := by
    have hex' : AvecN d E s v K n (τ ω) σ ω =
        Ugen (d.L n) (E n) σ (u 0) (u (τ ω)) (AvecN d E s v K n 0 σ ω) +
          ∑ j ∈ Finset.range (τ ω), Ugen (d.L n) (E n) σ (u (j + 1)) (u (τ ω))
            (predIncN d E s v K n j σ ω + martIncN d E s v K n j σ ω) := hex
    rw [hτeq] at hex'
    have hinner : ∀ j, ((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω =
        predIncN d E s v K n j σ ω + martIncN d E s v K n j σ ω := by
      intro j; funext b
      simp only [hR, hZ, hY', hDr, YvecN, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hex']
    simp only [hAf, hτeq, min_self, hinner, hA0]
  rw [hAeq] at hb
  exact hb

end Assembly

/-! ## 4. The collapsed window `v_n = s_n` -/

section Collapse

variable (d : Sizes)

/-- If `v_n = s_n` the grid walk does not move: `Δ = 0`, every `H_j = H_0` and `u_j = s_n`. -/
theorem NonAltEnd_pathH_collapse {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n = v n) (j : ℕ)
    (ω : PathΩ d) : pathH d s v K n j ω = pathH d s v K n 0 ω := by
  have hΔ : gridStep s v K n = 0 := by unfold gridStep; rw [← hsv]; simp
  unfold pathH
  rw [hΔ]
  simp

/-- **The collapsed window** (the case `v_n = s_n` of the endpoint, where `hc_pos` of the assembly
fails): `H_K = H_0` and `u_K = s`, so the initial bound `(𝓛-𝒦)_s ≤ N^{ε₁} M_s^{-k}` (`InitLK`)
with `ε₁ ≤ ε`, `N ≥ 1`, `Λ ≥ 1` and `Φ ≥ 0` is the conclusion `(𝓛-𝒦)_v ≤ N^ε (Λ^{1/2} + Φ)
M_v^{-k}` directly. -/
theorem NonAltEnd_collapse {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hE : |E n| < 2)
    (hv1 : v n < 1) (hsv : s n = v n) {k : ℕ}
    {ε₁ ε Λ Φ : ℝ} (hε : ε₁ ≤ ε) (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ) (ω : PathΩ d) (σ : Fin k → Bool)
    (a : Fin k → Z2 (d.L n))
    (hinit : lkGen (d.L n) (d.W n) (E n) (s n) (pathH d s v K n 0 ω) σ a ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k) :
    lkGen (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) σ a ≤
      ((d.size n : ℕ) : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) *
        (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k := by
  rw [NonAltEnd_pathH_collapse d hsv, ← hsv]
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hM : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k := by
    have hpos := scaleM_pos (L := d.L n) (W := d.W n) (E := E n) (u := s n)
      (by have := d.three_le_L n; omega) (d.W_pos n) hE (by linarith)
    have h1 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ := inv_nonneg.2 hpos.le
    positivity
  have h1 : ((d.size n : ℕ) : ℝ) ^ ε₁ ≤ ((d.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 hε
  have h2 : 1 ≤ Λ ^ ((1 : ℝ) / 2) + Φ := by
    have := Real.one_le_rpow hΛ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have h3 : ((d.size n : ℕ) : ℝ) ^ ε ≤ ((d.size n : ℕ) : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) :=
    le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h2
  exact hinit.trans (mul_le_mul_of_nonneg_right (h1.trans h3) hM)

end Collapse

/-! ## 5. The endpoint theorem `NonAltGridEnd` -/

section Main

variable (d : Sizes)

/-- The range condition passes to a smaller exponent and an earlier time. -/
theorem NonAltEnd_rangeCond_mono {τ τR : ℝ} {t v : ℕ → ℝ} (hτ : τR ≤ τ) (hvt : ∀ n, v n ≤ t n)
    (h : RangeCond d τ t) : RangeCond d τR v := by
  filter_upwards [h] with n hn
  calc ((d.size n : ℕ) : ℝ) ^ (-1 + τR) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ) :=
        Real.rpow_le_rpow_of_exponent_le (GoodEvent_one_le_size n) (by linarith)
    _ ≤ 1 - t n := hn
    _ ≤ 1 - v n := by linarith [hvt n]

/-- The union bound over the sign vectors: `2^k N^{-(D+1)} ≤ N^{-D}` eventually. -/
theorem NonAltEnd_ev_union (hsize : SizeTendsto d) (k : ℕ) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [hsize.eventually_ge_atTop ((2 : ℝ) ^ k), hsize.eventually_ge_atTop 1] with n hn hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  rw [show (-(D + 1)) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc (2 : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ (-D) * ((d.size n : ℕ) : ℝ)⁻¹)
      = ((d.size n : ℕ) : ℝ) ^ (-D) * ((2 : ℝ) ^ k / ((d.size n : ℕ) : ℝ)) := by ring
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ h
        rw [div_le_one hN0]; exact hn
    _ = _ := mul_one _

/-- **The uniform `Y` moments for all signs with one `C_P`** (before the grid `K`): the maximum over
the `2^k` sign vectors of the constants of `yMomentsUnifN` serves every sign (`N ≥ 1`). -/
theorem NonAltEnd_yMomentsMax {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : SizeTendsto d) (hrange : RangeCond d τR v) (k : ℕ) [NeZero k] :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin k → Bool,
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
          YMomentBoundsN d (E n) σ (gridTime s v K n) τ (K n)
            (fun j ω => YvecN d E s v K n j σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  choose CP hCP0 hCPev using fun σ : Fin k → Bool =>
    yMomentsUnifN d κ τR E s v hκ hE hs0 hsv hv1 hsize hrange k σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (GoodEvent_one_le_size n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

/-- **The grid endpoint for non-alternating `σ`** (`lem:STOeq_NQ` and its proof; the
statement `NonAltGridEnd`, `RBM2D.Induction.StoppedEndDefs`).  The exponents are explicit functions of `(k, c, ε, D₁)`
and of the constant `C_P` of the `Y` moments: `ε₁ = ε/8`, `τ' = ε/(8k)`, `D'' = 4k/c`, `D' = D'' + 1`,
`C_K = D₁ + 2 C_P^* + 6k + 20 + 2k/c` (`C_P^*` the maximum over the signs of the `C_P` of
`yMomentsUnifN`), with `ε_q = ε/8`, `D_Y = D_t = k + 1`, `τ_K = 1` inside the budget. -/
theorem nonAltGridEnd (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : NonAltGridEnd d κ c τ C E s t := by
  intro hU hmain hloc hdec hG4 k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt ε hε D₁ hD₁
  classical
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, hinit, -, -⟩ := hmain
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : RangeCond d (min τ 1) v := NonAltEnd_rangeCond_mono d (min_le_left _ _) hvt hrange
  -- the `Y`-moment constant (one for all sign vectors, chosen before the grid)
  obtain ⟨Cmax, hCmax0, hYmax⟩ := NonAltEnd_yMomentsMax d hκ hE hs0 hsv hv1 hsize hrangeV k
  -- the numerical constants
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := by linarith
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = ε / 8 := ⟨_, rfl⟩
  obtain ⟨τw, hτw⟩ : ∃ τw : ℝ, τw = ε / (8 * k) := ⟨_, rfl⟩
  obtain ⟨D'', hD''⟩ : ∃ D'' : ℝ, D'' = 4 * k / c := ⟨_, rfl⟩
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * Cmax + 6 * k + 20 + 2 * k / c := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; linarith
  have hτw0 : 0 < τw := by rw [hτw]; positivity
  have hτwk : τw * (k : ℝ) = ε / 8 := by rw [hτw]; field_simp
  have hD''0 : 0 ≤ D'' := by rw [hD'']; positivity
  have hD''c : c * D'' = 4 * k := by rw [hD'']; field_simp
  have hkc : 0 ≤ 2 * (k : ℝ) / c := by positivity
  have hCK0 : 0 ≤ C_K := by rw [hCKdef]; positivity
  refine ⟨ε₁, τw, D'' + 1, C_K, hε₁0, hτw0, by linarith, hCK0, ?_⟩
  intro K hK0 hKN hKU
  -- the exponent constraints
  obtain ⟨εq, hεq⟩ : ∃ εq : ℝ, εq = ε / 8 := ⟨_, rfl⟩
  have hεq0 : 0 < εq := by rw [hεq]; linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - min τ 1 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hθk1 : (4 * (k : ℝ) + 8) * θ ≤ 4 * k + 8 := mul_le_of_le_one_right (by positivity) hθ1
  have hθk2 : 5 * (k : ℝ) * θ ≤ 5 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk3 : 2 * (k : ℝ) * θ ≤ 2 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk4 : (2 * (k : ℝ) + 3) * θ ≤ 2 * k + 3 := mul_le_of_le_one_right (by positivity) hθ1
  have hτk1 : τw * ((k : ℝ) - 1) = ε / 8 - τw := by rw [mul_sub, hτwk]; ring
  have hτk2 : τw * ((2 * k : ℝ) - 1) = ε / 4 - τw := by
    have : τw * ((2 * k : ℝ) - 1) = 2 * (τw * k) - τw := by ring
    rw [this, hτwk]; ring
  have E1 : τw * ((k : ℝ) - 1) + ε₁ < ε := by rw [hτk1, hε₁]; linarith
  have E2 : τw * ((k : ℝ) - 1) + 2 * ε₁ < ε := by rw [hτk1, hε₁]; linarith
  have E3 : 2 * (εq + ε₁) + τw * ((2 * k : ℝ) - 1) < 2 * ε := by
    rw [hτk2, hεq, hε₁]; linarith
  have E4 : (2 * k : ℝ) - c * (D'' + 1) < ε := by rw [mul_add, hD''c]; linarith
  have E5 : (2 * k : ℝ) - c * (D'' + 1) + τw * ((k : ℝ) - 1) < ε := by
    rw [mul_add, hD''c, hτk1]; linarith
  have E6 : 2 * (εq + (k : ℝ)) + τw * ((2 * k : ℝ) - 1) + (2 * k : ℝ) - c * D'' < 2 * ε := by
    rw [hτk2, hD''c, hεq]; linarith
  have E7 : (k : ℝ) - ((k : ℝ) + 1) < ε := by linarith
  have hC1 : (D₁ + 1) + 4 * ((k : ℝ) + 1) + (k : ℝ) + 2 * Cmax + 8 ≤ C_K := by
    rw [hCKdef]; linarith
  have hC2 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * ((k : ℝ) + 1) < C_K := by
    rw [← hθdef, hCKdef]; linarith
  have hC3 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [← hθdef, hCKdef]; linarith
  have hC4 : 2 * (1 - min τ 1) + 1 + 2 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [← hθdef, hCKdef]; linarith
  have hC5 : 1 - min τ 1 < C_K := by rw [← hθdef, hCKdef]; linarith
  have hC6 : 1 + (2 * (k : ℝ) + 3) * (1 - min τ 1) + D'' / 2 < C_K := by
    have : D'' / 2 = 2 * (k : ℝ) / c := by rw [hD'']; ring
    rw [← hθdef, this, hCKdef]; linarith
  have hC7 : 1 ≤ C_K := by rw [hCKdef]; linarith
  -- the data of the levels and the `Y` moments
  have hΓ0 : ∀ n, 0 ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hYev := hYmax K hK0
  have hAsm := NonAltEnd_assembly d (κ := κ) (E := E) (s := s) (v := v) (K := K)
    k hk hκ hE hs0 hsv hv1 hK0 hsize (fun n => ((d.size n : ℕ) : ℝ) ^ ε₁) Λ Φ hΓ0 hΛ0 hΦ0
    (τw := τw) (D' := D'' + 1) (D'' := D'') (D_Y := (k : ℝ) + 1) (τK := 1) (εq := εq)
    (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K) hτw0.le one_pos hεq0 hCK0 hC1 hKN hKU hYev
  have hδ := NonAltEnd_ev_hδ d hsize (c := c) (τR := min τ 1) (C_K := C_K) (D'' := D'') k hκ
    (E := E) (s := s) (v := v) (K := K) hE hc hs0 hsv hv1 hband hrangeV hD''0 hC6 hKN
  have hM1 := NonAltEnd_ev_hM1 d hsize hκ hE hc hτR hv1 hband hrangeV
  have hη := NonAltEnd_ev_hη d hsize hκ hE hτR hrangeV
  have hlogR := NonAltBudget_merged_inputs d (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := (k : ℝ) + 1) (E := E) (s := s) (v := v) (K := K) k hκ hτR hτR1 one_pos
    (by linarith) hk hsize hE hs0 hsv hv1 hK0 hrangeV hC2 hC3 hC4 hC5 hKN
  have ha1 := NonAltEnd_ev_ha1 d hsize (k := k) (by omega) κ (τw := τw) (ε₁ := ε₁) (ε := ε)
    hτw0.le E1
  have ha2 := NonAltEnd_ev_ha2 d hsize (k := k) (by omega) hκ hE (τw := τw) (ε₁ := ε₁) (ε := ε)
    hτw0.le E2
  have ha3 := NonAltEnd_ev_ha3 d hsize (k := k) (by omega) hκ hE (τw := τw) (ε₁ := ε₁)
    (εq := εq) (ε := ε) hτw0.le E3
  have he1 := NonAltEnd_ev_he1 d hsize hband (k := k) (D' := D'' + 1) (ε := ε) (by linarith) E4
  have he2 := NonAltEnd_ev_he2 d hsize hband (k := k) (by omega) κ (τw := τw) (D' := D'' + 1)
    (ε := ε) hτw0.le (by linarith) E5
  have he3 := NonAltEnd_ev_he3 d hsize hband (k := k) (by omega) κ (τw := τw) (D'' := D'')
    (εq := εq) (ε := ε) hτw0.le hD''0 E6
  have he4 := NonAltEnd_ev_he4 d hsize k (D := (k : ℝ) + 1) (ε := ε) E7
  have he5 := NonAltEnd_ev_he5 d hsize k (D := (k : ℝ) + 1) (ε := ε) E7
  have hun := NonAltEnd_ev_union d hsize k D₁
  filter_upwards [hAsm, hδ, hM1, hη, hlogR, ha1, ha2, ha3, he1, he2, he3, he4, he5, hΛ1, hun,
    hKN] with n hAsmn hδn hM1n hηn hlogRn ha1n ha2n ha3n he1n he2n he3n he4n he5n hΛ1n hunn
    hKNn
  have hEn2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact NonAltEnd_collapse d hEn2 (hv1 n) hsvn (by rw [hε₁]; linarith) hΛ1n (hΦ0 n) ω σ a
        (hinit' σ hσ a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
    have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
    have hΔN := NonAltEnd_hΔN d hC7 hKNn hvs
    -- the events, one per non-alternating sign vector
    have hAsmσ : ∀ σ : {σ : Fin k → Bool // ¬ Alternating σ}, ∃ G : Set (PathΩ d),
        (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) ∧
        ∀ ω ∈ G, (∀ j ≤ K n, pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
            (gridTime s v K n j) k (((d.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φ n) τw (D'' + 1)) →
          ∀ a : Fin k → Z2 (d.L n),
            ‖AvecN d E s v K n (K n) σ.1 ω a‖ ≤
              assembledRHSNonAlt d E s v K n k κ τw (fun n => ((d.size n : ℕ) : ℝ) ^ ε₁) Λ Φ
                (D'' + 1) D'' ((k : ℝ) + 1) 1 εq
                (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN d E s v K n 0 σ.1 ω b‖) a :=
      fun σ => hAsmn σ.1 ((not_alternating_iff σ.1).1 σ.2) hlt hδn
    choose Gs hGsP hGsb using hAsmσ
    refine ⟨⋂ σ, Gs σ, ?_, ?_⟩
    · -- the union bound over the `≤ 2^k` sign vectors
      have hcompl : (⋂ σ, Gs σ)ᶜ = ⋃ σ, (Gs σ)ᶜ := by rw [Set.compl_iInter]
      rw [hcompl]
      calc (pathP d).real (⋃ σ, (Gs σ)ᶜ) ≤ ∑ σ, (pathP d).real (Gs σ)ᶜ :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ _σ : {σ : Fin k → Bool // ¬ Alternating σ},
              ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun σ _ => hGsP σ
        _ = (Fintype.card {σ : Fin k → Bool // ¬ Alternating σ} : ℝ) *
              ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
        _ ≤ (2 : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
            have h1 := Fintype.card_subtype_le (fun σ : Fin k → Bool => ¬ Alternating σ)
            have h2 : Fintype.card (Fin k → Bool) = 2 ^ k := by simp
            rw [h2] at h1
            exact_mod_cast h1
        _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ hσ a
      have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω ⟨σ, hσ⟩
      have hb := hGsb ⟨σ, hσ⟩ ω hωσ hgood a
      have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN d E s v K n 0 σ ω b‖) ≤
          ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹ := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have h := hinit' σ hσ b
        have e : ‖AvecN d E s v K n 0 σ ω b‖ =
            lkGen (d.L n) (d.W n) (E n) (s n) (pathH d s v K n 0 ω) σ b := by
          simp only [AvecN, lkGen, GoodEvent_gridTime_zero]
        rw [e, ← inv_pow]
        exact h
      have hbud := budgetNonAlt d E s v K n k hk κ τw (fun n => ((d.size n : ℕ) : ℝ) ^ ε₁) Λ Φ
        (D'' + 1) D'' ((k : ℝ) + 1) ((k : ℝ) + 1) 1 ε εq ε₁
        (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecN d E s v K n 0 σ ω b‖) a hEn2
        (hs0 n) (hsv n) (hv1 n) hK1 hM1n hηn hΔN rfl hΛ1n (hΦ0 n) hlogRn.1 hX0 hlogRn.2 ha1n
        ha2n ha3n he1n he2n he3n he4n he5n
      have hlk : lkGen (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) σ a =
          ‖AvecN d E s v K n (K n) σ ω a‖ := by
        simp only [AvecN, lkGen, gridTime_last s v K n (hK0 n)]
      rw [hlk]
      exact hb.trans hbud

end Main

end RBM.Ind

end
