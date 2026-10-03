/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

import RBM2D.Induction.Defs
import RBM2D.Induction.PerTimeCalc
import RBM2D.Induction.ScaleFacts
import RBM2D.Induction.Split
import RBM2D.Loop.Cyclic
import RBM2D.Path.ScalesBridge

/-!
# Step 3 of Theorem `lem:main_ind`: the deterministic `≺`-calculus giving (`Eq:LGxb`)

Paper: arXiv:2503.07606, Section 5, "Proof of Theorem `lem:main_ind`, Step 3"; the conclusion is
(`Eq:LGxb`).

Main declarations (namespace `RBM.Ind`): the `Prop` `Step3Target` and
`theorem step3 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step3Target d κ c τ E s t`.

## What is used

Of the premises of `Step3Target`, the proof uses `KboundConcl κ`; from `MainIndHyp` the
conjuncts `0 < κ`, `|E n| ≤ 2 - κ`, `0 < c`, `0 ≤ s`, `s ≤ t`, `t < 1`, `SizeTendsto`,
`Bandwidth`, `CondStInd`; `Step1LoopPT`; `Step2LocalPT`; `Step2DecayPT`; `PPTwoLoopPT` (the
`(+,+)` two-loop); and `STOeqPT k` for `k ≥ 3`.  It does not use `τ`, `RangeCond`,
`InitLK`, `InitDecay`, `InitLocal`, `Step1WeakLawPT`, nor `STOeqPT 2`.

## Proof

The double induction is that of the one-dimensional formalization, restated for `PerTimeDomAt`
(`≺` per time, `hsize : size → ∞` in place of `N → ∞`):

* real inequalities `step3_rpow_quarter`, ..., `step3_ineq_long` (Section 1);
* `step3_Psi`, `step3_psi` and their lemmas (Section 2);
* the abstract induction `Step3Scales`, `Step3Hyp`, `step3_S_of_S`, `step3_S_all`,
  `step3_xiLK_le`, `step3_xiL_le_one_of` (Section 3);
* the flow wiring `step3_scales`, `step3_xiL_le`, `step3_hyp`, and `step3`;
* the four-charge decomposition `step3_lkGen_two_le`, `step3_lkGen_mm`, `step3_pm_two`,
  `step3_xiLK_two`.

All auxiliary names are private with the prefix `step3`.

## The `d = 2` changes

* `R = (ℓ_t/ℓ_s)²` (in the one-dimensional case `ℓ_t/ℓ_s`), so `Ψ` carries
  `R^{n-1} = (ℓ_t/ℓ_s)^{2n-2}` and the real lemmas apply verbatim.  Scale inequalities:
  `R² M_s^{3/4} ≤ M_u` from
  `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)² ≤ M_s^{1/15}` (`scaleFacts_ellT_pow_four`, `CondStInd`) and
  `M_s^{29/30} ≤ M_u` (`scaleFacts_R2_pt`); the exponents are `1/15 + 3/4 = 49/60 ≤ 29/30`.
* The final choice is `k = n + 1` (`Psi_succ_le`, needs `R ≤ M_s^{1/4}`, which `scale_facts`
  gives from `R² M_s^{3/4} ≤ M_u ≤ M_s`); the requirement `k ≥ 4 + 4(n-1)/15` is not used.
* (5.118) is `loopXi_le` (module `RBM2D.Induction.Split`, block weight `W⁻²`); (5.107) is `KboundConcl` at every
  length `k ≥ 1` (`KLoop.Par κ N` filled with `(L n, W n, E n, u)`, `kloop_Mt_eq`).
* The label maximum `step3_label_max` (union bound with `D + C`; the label sets have at most
  `N^{2k}` elements) turns the per-label inputs `Step1LoopPT`, `Step2LocalPT`, `Step2DecayPT`
  into statements about the maxima `Ξ`.
* The base cases are proved here: `S(m,0)` (`step3_S_zero`), `m = 1` (`step3_xiLK_one`), `m = 2`
  over the four charges (`step3_xiLK_two`: `(+,+)` is `PPTwoLoopPT`, `(+,-)` is `Step2DecayPT`
  at `D = 3/c`, `(-,+)` is its rotation and `(-,-)` the conjugate of `(+,+)`).

## Differences from the paper

* The paper cites (`Gt_bound+IND`) and (`Eq:Gdecay_w`) for the base cases `m ≤ 2`; the induction
  runs over `u ∈ [s,t]`, so the formalization uses `Step2LocalPT` (`Gt_bound_flow`) for `m = 1`
  and `Step2DecayPT` (`Eq:Gdecay_w`) at `D = 3/c` for `(+,-)`.
* The paper's base-case sentence is silent on `S(m,0)` and on the charges `(-,+)`, `(-,-)` of
  `m = 2`; the formalization takes `S(m,0)` from `Step1LoopPT` and `KboundConcl`, and the two
  charges from rotation (`gloop_rotate`, `Kcal_rotate`) and complex conjugation.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The statement of Step 3**: deterministic `≺`-calculus given the random layer
(`STOeqPT`, all `k ≥ 2`), the `(+,+)` base case, Steps 1–2 per time, and the `𝒦` bound. -/
def Step3Target (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  KboundConcl κ → MainIndHyp d κ c τ E s t →
    Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    Step2LocalPT d E s t → Step2DecayPT d E s t → PPTwoLoopPT d E s t →
    (∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k) → Step3PT d E s t

/-! ## 1. Real inequalities between the scales -/

section Real

/-- The scale kit: `b = a^{1/4}` with `a^{1/2} = b²`, `a^{3/4} = b³`, `a = b⁴`. -/
private theorem step3_rpow_quarter {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    a ^ ((j : ℝ) / 4) = (a ^ ((1 : ℝ) / 4)) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  ring_nf

private theorem step3_rpow_half_eq {a : ℝ} (ha : 0 ≤ a) :
    a ^ ((1 : ℝ) / 2) = (a ^ ((1 : ℝ) / 4)) ^ 2 := by
  rw [← step3_rpow_quarter ha]; norm_num

private theorem step3_rpow_three_quarter_eq {a : ℝ} (ha : 0 ≤ a) :
    a ^ ((3 : ℝ) / 4) = (a ^ ((1 : ℝ) / 4)) ^ 3 := by
  rw [← step3_rpow_quarter ha]; norm_num

private theorem step3_self_eq_rpow_quarter_pow {a : ℝ} (ha : 0 ≤ a) :
    a = (a ^ ((1 : ℝ) / 4)) ^ 4 := by
  rw [← step3_rpow_quarter ha]; norm_num

/-- `a^{1-(k-1)/4} = a^{1/4} a^{1-k/4}` for `k ≥ 1`. -/
private theorem step3_rpow_pred_eq {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    a ^ (1 - ((k - 1 : ℕ) : ℝ) / 4) = a ^ ((1 : ℝ) / 4) * a ^ (1 - (k : ℝ) / 4) := by
  rw [← Real.rpow_add ha]
  congr 1
  rw [Nat.cast_sub hk]
  ring

/-- `a^{1-k/4} ≤ a^{3/4}` for `k ≥ 1`, `a ≥ 1`. -/
private theorem step3_rpow_one_sub_le {a : ℝ} (ha : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    a ^ (1 - (k : ℝ) / 4) ≤ (a ^ ((1 : ℝ) / 4)) ^ 3 := by
  rw [← step3_rpow_three_quarter_eq (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le ha
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-! The polynomial inequalities.  Throughout, `b = (W ℓ_s η_s)^{1/4} ≥ 1`, `R = ℓ_t/ℓ_s ≥ 1`,
`v = W ℓ_u η_u` with `R² b³ ≤ v ≤ b⁴`, and `e = (W ℓ_s η_s)^{1-k/4} ≤ b³` (`k ≥ 1`). -/

variable {b R v e : ℝ}

private theorem step3_scale_facts (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4)
    (hRv : R ^ 2 * b ^ 3 ≤ v) :
    0 < v ∧ R ^ 2 ≤ b ∧ b ^ 2 ≤ v ∧ b ^ 3 ≤ v ∧ R * b ≤ v ∧ R ≤ b := by
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hb3v : b ^ 3 ≤ v := by nlinarith
  have hR2b : R ^ 2 ≤ b := by
    have h : R ^ 2 * b ^ 3 ≤ b * b ^ 3 := by nlinarith
    exact le_of_mul_le_mul_right h (by positivity)
  have hRb : R ≤ b := by nlinarith
  refine ⟨by linarith, hR2b, by nlinarith, hb3v, ?_, hRb⟩
  have : R * b ≤ R ^ 2 * b ^ 3 :=
    mul_le_mul (by nlinarith) (by simpa using pow_le_pow_right₀ hb (show 1 ≤ 3 by norm_num))
      (by linarith) (by positivity)
  linarith

/-- The deterministic part of **(5.119) ⟹ (5.120)**. -/
private theorem step3_ineq_5120 (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) {n α β : ℕ} (hn : 1 ≤ n) (hαβ : α + β = 2 * n) (hα : α ≤ n + 1)
    (hβ : β ≤ n + 1) {p₁ p₂ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₂0 : 0 ≤ p₂)
    (hp₁ : p₁ ≤ b ^ 2 + R ^ α * (b * e)) (hp₂ : p₂ ≤ b ^ 2 + R ^ β * (b * e)) :
    (1 + v⁻¹ * p₁) * (1 + v⁻¹ * p₂) * v ≤ 4 * (b ^ 2 + R ^ (n - 1) * e) ^ 2 := by
  obtain ⟨hv0, hR2b, hb2v, hb3v, -, -⟩ := step3_scale_facts hb hR hv hRv
  set r := R ^ (n - 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hb0 : 0 ≤ b := by linarith
  have hsplit : R ^ (n + 1) = r * R ^ 2 := by rw [hr, ← pow_add]; congr 1; omega
  have hRα : R ^ α ≤ r * b :=
    (pow_le_pow_right₀ hR hα).trans (by rw [hsplit]; exact mul_le_mul_of_nonneg_left hR2b hr0)
  have hRβ : R ^ β ≤ r * b :=
    (pow_le_pow_right₀ hR hβ).trans (by rw [hsplit]; exact mul_le_mul_of_nonneg_left hR2b hr0)
  have hRαβ : R ^ α * R ^ β = r ^ 2 * R ^ 2 := by
    rw [← pow_add, hαβ, hr, ← pow_mul, ← pow_add]; congr 1; omega
  set x := R ^ α * (b * e) with hx
  set y := R ^ β * (b * e) with hy
  have hbe : 0 ≤ b * e := mul_nonneg hb0 he
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hxle : x ≤ r * b ^ 2 * e := by
    calc x ≤ r * b * (b * e) := mul_le_mul_of_nonneg_right hRα hbe
      _ = r * b ^ 2 * e := by ring
  have hyle : y ≤ r * b ^ 2 * e := by
    calc y ≤ r * b * (b * e) := mul_le_mul_of_nonneg_right hRβ hbe
      _ = r * b ^ 2 * e := by ring
  have hR2b2 : R ^ 2 * b ^ 2 ≤ v := by
    have : R ^ 2 * b ^ 2 ≤ R ^ 2 * b ^ 3 := by
      have : b ^ 2 ≤ b ^ 3 := pow_le_pow_right₀ hb (by norm_num)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hxy : x * y ≤ r ^ 2 * e ^ 2 * v := by
    have : x * y = r ^ 2 * e ^ 2 * (R ^ 2 * b ^ 2) := by
      rw [hx, hy]
      calc R ^ α * (b * e) * (R ^ β * (b * e)) = (R ^ α * R ^ β) * (b ^ 2 * e ^ 2) := by ring
        _ = _ := by rw [hRαβ]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hR2b2 (by positivity)
  -- the numerator
  have hnum : (v + p₁) * (v + p₂) ≤ 4 * v * (b ^ 2 + r * e) ^ 2 := by
    have h1 : v + p₁ ≤ v + b ^ 2 + x := by linarith
    have h2 : v + p₂ ≤ v + b ^ 2 + y := by linarith
    have h12 : (v + p₁) * (v + p₂) ≤ (v + b ^ 2 + x) * (v + b ^ 2 + y) :=
      mul_le_mul h1 h2 (by linarith) (by positivity)
    have h3 : (v + b ^ 2) * (x + y) ≤ (2 * v) * (2 * (r * b ^ 2 * e)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have h4 : (v + b ^ 2) ^ 2 ≤ 4 * v * b ^ 4 := by
      have : (v + b ^ 2) ^ 2 ≤ (2 * v) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith
    have hre : 0 ≤ r * b ^ 2 * e := by positivity
    have h5 : 0 ≤ v * (r ^ 2 * e ^ 2) := by positivity
    nlinarith
  have hlhs : (1 + v⁻¹ * p₁) * (1 + v⁻¹ * p₂) * v = (v + p₁) * (v + p₂) * v⁻¹ := by
    field_simp
  rw [hlhs, mul_inv_le_iff₀ hv0]
  nlinarith

/-- The quadratic term of (5.112) for `3 ≤ p, q ≤ n - 1` (both factors at level `k`). -/
private theorem step3_ineq_quad (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) (he3 : e ≤ b ^ 3) {n p q : ℕ} (hpq : p + q = n + 2) (hp : p ≤ n) (hq : q ≤ n) :
    (b ^ 2 + R ^ (p - 1) * e) * (b ^ 2 + R ^ (q - 1) * e) * v⁻¹
      ≤ 4 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, hb3v, -, -⟩ := step3_scale_facts hb hR hv hRv
  set r := R ^ (n - 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hRp : R ^ (p - 1) ≤ r := pow_le_pow_right₀ hR (by omega)
  have hRq : R ^ (q - 1) ≤ r := pow_le_pow_right₀ hR (by omega)
  have hRpq : R ^ (p - 1) * R ^ (q - 1) = r * R := by
    rw [← pow_add, hr, ← pow_succ]; congr 1; omega
  have hRe : R * e ≤ v := by
    have : R * e ≤ R ^ 2 * b ^ 3 := by
      have : R ≤ R ^ 2 := by nlinarith
      calc R * e ≤ R * b ^ 3 := mul_le_mul_of_nonneg_left he3 (by linarith)
        _ ≤ R ^ 2 * b ^ 3 := mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  rw [mul_inv_le_iff₀ hv0]
  have hexp : (b ^ 2 + R ^ (p - 1) * e) * (b ^ 2 + R ^ (q - 1) * e)
      = b ^ 2 * b ^ 2 + b ^ 2 * (R ^ (p - 1) * e + R ^ (q - 1) * e) + r * e * (R * e) := by
    rw [show r * e * (R * e) = (R ^ (p - 1) * R ^ (q - 1)) * e ^ 2 by rw [hRpq]; ring]
    ring
  rw [hexp]
  have h1 : b ^ 2 * b ^ 2 ≤ b ^ 2 * v := mul_le_mul_of_nonneg_left hb2v (by positivity)
  have h2 : b ^ 2 * (R ^ (p - 1) * e + R ^ (q - 1) * e) ≤ v * (2 * (r * e)) :=
    mul_le_mul hb2v (by nlinarith) (by positivity) (by linarith)
  have h3 : r * e * (R * e) ≤ r * e * v := mul_le_mul_of_nonneg_left hRe (by positivity)
  have h4 : 0 ≤ r * e * v := by positivity
  nlinarith

/-- The quadratic term of (5.112) with a `2`-loop factor: `Ξ_2 ≺ b²`, `Ξ_n ≺ b² + R^{n-1} b e`. -/
private theorem step3_ineq_quad_two (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4)
    (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) (n : ℕ) :
    b ^ 2 * (b ^ 2 + R ^ (n - 1) * (b * e)) * v⁻¹ ≤ 2 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, hb3v, -, -⟩ := step3_scale_facts hb hR hv hRv
  have hr0 : 0 ≤ R ^ (n - 1) := by positivity
  rw [mul_inv_le_iff₀ hv0]
  have h1 : b ^ 2 * b ^ 2 ≤ b ^ 2 * v := mul_le_mul_of_nonneg_left hb2v (by positivity)
  have h2 : b ^ 3 * (R ^ (n - 1) * e) ≤ v * (R ^ (n - 1) * e) :=
    mul_le_mul_of_nonneg_right hb3v (by positivity)
  have h3 : b ^ 2 * (b ^ 2 + R ^ (n - 1) * (b * e))
      = b ^ 2 * b ^ 2 + b ^ 3 * (R ^ (n - 1) * e) := by ring
  rw [h3]
  have h4 : 0 ≤ R ^ (n - 1) * e * v := by positivity
  nlinarith

/-- The long-loop term of (5.112): `Ξ^{(L)}_{n+1} ≺ 1 + v⁻¹ (b² + R^n b e)`. -/
private theorem step3_ineq_long (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) :
    1 + v⁻¹ * (b ^ 2 + R ^ n * (b * e)) ≤ 3 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, -, hRbv, -⟩ := step3_scale_facts hb hR hv hRv
  have hr0 : 0 ≤ R ^ (n - 1) := by positivity
  have hRn : R ^ n = R ^ (n - 1) * R := by rw [← pow_succ]; congr 1; omega
  have h1 : (1 : ℝ) ≤ b ^ 2 := one_le_pow₀ hb
  have h2 : v⁻¹ * b ^ 2 ≤ 1 := by rw [inv_mul_le_iff₀ hv0]; linarith
  have h3 : v⁻¹ * (R ^ n * (b * e)) ≤ R ^ (n - 1) * e := by
    rw [inv_mul_le_iff₀ hv0, hRn]
    have : R ^ (n - 1) * e * (R * b) ≤ R ^ (n - 1) * e * v :=
      mul_le_mul_of_nonneg_left hRbv (by positivity)
    nlinarith
  have h4 : 0 ≤ R ^ (n - 1) * e := by positivity
  nlinarith

end Real

/-! ## 2. The control parameter `Ψ` (5.108) -/

section PsiDefs

/-- **(5.108)** for `k ≥ 1`:
`Ψ(n,k,s,u,t) = M_s^{1/2} + R^{n-1} M_s^{1-k/4}`, with `As = M_s` and `R = (ℓ_t/ℓ_s)²`.  It
does not depend on `u`. -/
private noncomputable def step3_Psi (As R : ℝ) (n k : ℕ) : ℝ :=
  As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4)

/-- **(5.108)** `Ψ(n,k,s,u,t)`, with `Au = W ℓ_u η_u`: for `k = 0` the last factor is
`W ℓ_u η_u`, for `k ≥ 1` it is `(W ℓ_s η_s)^{1-k/4}`. -/
private noncomputable def step3_psi (As R Au : ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * Au else step3_Psi As R n k

variable {As R Au : ℝ} {n k : ℕ}

private theorem step3_psi_of_ne_zero (hk : k ≠ 0) :
    step3_psi As R Au n k = step3_Psi As R n k := by simp [step3_psi, hk]

private theorem step3_psi_zero :
    step3_psi As R Au n 0 = As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * Au := by simp [step3_psi]

private theorem step3_Psi_nonneg (hAs : 0 ≤ As) (hR : 0 ≤ R) : 0 ≤ step3_Psi As R n k := by
  unfold step3_Psi; positivity

private theorem step3_psi_nonneg (hAs : 0 ≤ As) (hR : 0 ≤ R) (hAu : 0 ≤ Au) :
    0 ≤ step3_psi As R Au n k := by
  unfold step3_psi; split_ifs
  · positivity
  · exact step3_Psi_nonneg hAs hR

/-- `Ψ(n,k)` in the variables `b = As^{1/4}`, `e = As^{1-k/4}`. -/
private theorem step3_Psi_eq (hAs : 0 ≤ As) :
    step3_Psi As R n k = (As ^ ((1 : ℝ) / 4)) ^ 2 + R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4) := by
  rw [step3_Psi, step3_rpow_half_eq hAs]

/-- The level-`(k-1)` bound in the level-`k` variables: `Ψ(m,k-1,u) ≤ b² + R^{m-1} b e`
(for `k = 1` this uses `W ℓ_u η_u ≤ W ℓ_s η_s`). -/
private theorem step3_psi_pred_le (hAs : 0 < As) (hR : 0 ≤ R) (hAu : Au ≤ As) (hk : 1 ≤ k) (m : ℕ) :
    step3_psi As R Au m (k - 1) ≤ (As ^ ((1 : ℝ) / 4)) ^ 2
      + R ^ (m - 1) * (As ^ ((1 : ℝ) / 4) * As ^ (1 - (k : ℝ) / 4)) := by
  rw [← step3_rpow_pred_eq hAs hk, ← step3_rpow_half_eq hAs.le]
  unfold step3_psi
  split_ifs with h0
  · have hk1 : k - 1 = 0 := h0
    rw [hk1]
    simp only [CharP.cast_eq_zero, zero_div, sub_zero, Real.rpow_one]
    gcongr
  · exact le_of_eq (by rw [step3_Psi])

/-- `Ψ(n,k)` is non-decreasing in `n` (for `R ≥ 1`). -/
private theorem step3_Psi_mono (hAs : 0 ≤ As) (hR : 1 ≤ R) {m : ℕ} (hmn : m ≤ n) :
    step3_Psi As R m k ≤ step3_Psi As R n k := by
  unfold step3_Psi
  gcongr

end PsiDefs


/-! ## 3. The abstract double induction

`≺` is `PerTimeDomAt P size` (per time, `u ∈ U l`); `size → ∞` is the field `hsize` of `Step3Hyp`
(the hypothesis of `PerTimeCalc`). -/

section Abstract

open PerTimeCalc.PerTime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Transitivity of `≺` through a random middle quantity. -/
private theorem step3_trans (hsize : Tendsto size atTop atTop) {ξ ζ χ : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ ζ) (h₂ : PerTimeDomAt P size ζ χ) :
    PerTimeDomAt P size ξ χ := by
  refine perTimeCalc_of_imp_union hsize h₁ h₂ ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  by_contra hno
  simp only [not_or, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h3 : ξ l u ω ≤ (size l : ℝ) ^ τ * χ l u ω :=
    calc ξ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := hno.1
      _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * χ l u ω) :=
          mul_le_mul_of_nonneg_left hno.2 hpos
      _ = (size l : ℝ) ^ τ * χ l u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  linarith

/-- `ξ ≺ ζ` gives `1 + A⁻¹ ξ ≺ 1 + A⁻¹ ζ` for a deterministic `A > 0`. -/
private theorem step3_one_add_inv_mul (hsize : Tendsto size atTop atTop)
    {A : ∀ N, U N → ℝ} (hA : ∀ N u, 0 < A N u)
    {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun N u ω => 1 + (A N u)⁻¹ * ξ N u ω)
      (fun N u ω => 1 + (A N u)⁻¹ * ζ N u ω) := by
  have h1 : PerTimeDomAt P size (fun N (_ : U N) (_ : Ω) => (1 : ℝ)) (fun _ _ _ => 1) :=
    perTimeCalc_refl hsize fun _ _ _ => zero_le_one
  have hA' : ∀ N u (_ : Ω), 0 ≤ (A N u)⁻¹ := fun N u _ => (inv_pos.2 (hA N u)).le
  have h2 : PerTimeDomAt P size (fun N u (_ : Ω) => (A N u)⁻¹) (fun N u _ => (A N u)⁻¹) :=
    perTimeCalc_refl hsize hA'
  exact perTimeCalc_add hsize h1 (perTimeCalc_mul hsize hξ hA' h2 h)

/-- **The scales of Step 3**: `As N = M_s`,
`R N = (ℓ_t/ℓ_s)²`, `A N u = M_u`. -/
private structure Step3Scales (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) : Prop where
  As_pos : ∀ N, 0 < As N
  R_nonneg : ∀ N, 0 ≤ R N
  A_pos : ∀ N u, 0 < A N u
  one_le_As : ∀ᶠ N : ℕ in atTop, 1 ≤ As N
  one_le_R : ∀ᶠ N : ℕ in atTop, 1 ≤ R N
  A_le_As : ∀ᶠ N : ℕ in atTop, ∀ u, A N u ≤ As N
  le_A : ∀ᶠ N : ℕ in atTop, ∀ u, R N ^ 2 * As N ^ ((3 : ℝ) / 4) ≤ A N u

/-- The scale facts in the variable `b = As^{1/4}`. -/
private theorem Step3Scales.kit {As R : ℕ → ℝ} {A : ∀ N, U N → ℝ} (h : Step3Scales As R A) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ As N ∧ 1 ≤ As N ^ ((1 : ℝ) / 4) ∧ 1 ≤ R N ∧
      ∀ u, A N u ≤ As N ∧ A N u ≤ (As N ^ ((1 : ℝ) / 4)) ^ 4 ∧
        R N ^ 2 * (As N ^ ((1 : ℝ) / 4)) ^ 3 ≤ A N u := by
  filter_upwards [h.one_le_As, h.one_le_R, h.A_le_As, h.le_A] with N h1 h2 h3 h4
  have ha : 0 ≤ As N := by linarith
  refine ⟨h1, Real.one_le_rpow h1 (by norm_num), h2, fun u => ⟨h3 u, ?_, ?_⟩⟩
  · rw [← step3_self_eq_rpow_quarter_pow ha]; exact h3 u
  · rw [← step3_rpow_three_quarter_eq ha]; exact h4 u

variable (P size) in
/-- **The estimate `S(n,k,s,u,t)`**:`Ξ^{(𝓛-𝒦)}_{u,n} ≺ Ψ(n,k,s,u,t)`. -/
private def step3S (X : ℕ → ∀ N, U N → Ω → ℝ) (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) (n k : ℕ) :
    Prop :=
  PerTimeDomAt P size (X n) fun N u _ => step3_psi (As N) (R N) (A N u) n k

variable (P size) in
/-- **Lemma 5.14 (5.92)** in the form used in (5.112);
for `X = Ξ^{(𝓛-𝒦)}`, `Y = Ξ^{(𝓛)}`, `A = M_u` it is `STOeqPT` (module `RBM2D.Induction.Defs`). -/
private def step3Lemma514 (X Y : ℕ → ∀ N, U N → Ω → ℝ) (A : ∀ N, U N → ℝ) (n : ℕ) : Prop :=
  ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
    PerTimeDomAt P size (Y (2 * n + 2)) (fun N _ _ => Λ N) →
    (∀ m, 1 ≤ m → m < n → PerTimeDomAt P size (X m) fun N _ _ => Φ N) →
    (∀ m, 2 ≤ m → m ≤ n → PerTimeDomAt P size
      (fun N u ω => X m N u ω * X (n - m + 2) N u ω * (A N u)⁻¹) fun N _ _ => Φ N) →
    PerTimeDomAt P size (Y (n + 1)) (fun N _ _ => Φ N) →
    PerTimeDomAt P size (X n) fun N _ _ => Λ N ^ ((1 : ℝ) / 2) + Φ N

variable (P size) in
/-- **The inputs of Step 3**, with `size → ∞` added. -/
private structure Step3Hyp (X Y : ℕ → ∀ N, U N → Ω → ℝ) (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) :
    Prop where
  hsize : Tendsto size atTop atTop
  scales : Step3Scales As R A
  X_nonneg : ∀ n N u ω, 0 ≤ X n N u ω
  Y_nonneg : ∀ n N u ω, 0 ≤ Y n N u ω
  /-- **(5.107)**, first half: `Ξ^{(𝓛)}_{u,n} ≺ 1 + M_u^{-1} Ξ^{(𝓛-𝒦)}_{u,n}` (`n ≥ 3`). -/
  xiL_le : ∀ n, 3 ≤ n → PerTimeDomAt P size (Y n) fun N u ω => 1 + (A N u)⁻¹ * X n N u ω
  /-- **(5.118)**: `Ξ^{(𝓛)}_{u,2n+2} ≤ Ξ^{(𝓛)}_{u,2l₁} Ξ^{(𝓛)}_{u,2l₂} M_u`, `l₁ + l₂ = n + 1`. -/
  xiL_split : ∀ n l₁ l₂, 1 ≤ l₁ → 1 ≤ l₂ → l₁ + l₂ = n + 1 → ∀ N u ω,
    Y (2 * n + 2) N u ω ≤ Y (2 * l₁) N u ω * Y (2 * l₂) N u ω * A N u
  /-- **Lemma 5.14 (5.92)** for `n ≥ 3`. -/
  lemma514 : ∀ n, 3 ≤ n → step3Lemma514 P size X Y A n

variable {X Y : ℕ → ∀ N, U N → Ω → ℝ} {As R : ℕ → ℝ} {A : ∀ N, U N → ℝ}

/-- The right side of (5.119). -/
private noncomputable def step3rhs5119 (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) (n k : ℕ) (N : ℕ)
    (u : U N) : ℝ :=
  (1 + (A N u)⁻¹ * step3_psi (As N) (R N) (A N u) (2 * ((n + 1) / 2)) (k - 1)) *
    (1 + (A N u)⁻¹ * step3_psi (As N) (R N) (A N u) (2 * (n + 1 - (n + 1) / 2)) (k - 1)) * A N u

/-- **(5.119)**. -/
private theorem step3_xiL_5119 (h : Step3Hyp P size X Y As R A) {n k : ℕ} (hn : 3 ≤ n)
    (hS : ∀ m, 1 ≤ m → m ≤ n + 2 → step3S P size X As R A m (k - 1)) :
    PerTimeDomAt P size (Y (2 * n + 2)) fun N u _ => step3rhs5119 As R A n k N u := by
  have hsize := h.hsize
  have sc := h.scales
  set l₁ := (n + 1) / 2 with hl₁def
  set l₂ := n + 1 - l₁ with hl₂def
  have hl₁ : 2 ≤ l₁ := by omega
  have hl₂ : 2 ≤ l₂ := by omega
  have hbd0 : ∀ l N (u : U N) (_ : Ω),
      0 ≤ 1 + (A N u)⁻¹ * step3_psi (As N) (R N) (A N u) (2 * l) (k - 1) := fun l N u _ => by
    have := step3_psi_nonneg (sc.As_pos N).le (sc.R_nonneg N) (sc.A_pos N u).le
      (n := 2 * l) (k := k - 1)
    have := (inv_pos.2 (sc.A_pos N u)).le
    positivity
  have hY : ∀ l, 2 ≤ l → 2 * l ≤ n + 2 → PerTimeDomAt P size (Y (2 * l))
      (fun N u _ => 1 + (A N u)⁻¹ * step3_psi (As N) (R N) (A N u) (2 * l) (k - 1)) :=
    fun l hl hl' => step3_trans hsize (h.xiL_le (2 * l) (by omega))
      (step3_one_add_inv_mul hsize sc.A_pos (h.X_nonneg _) (hS (2 * l) (by omega) hl'))
  have h12 := perTimeCalc_mul hsize (h.Y_nonneg _) (hbd0 l₁) (hY l₁ hl₁ (by omega))
    (hY l₂ hl₂ (by omega))
  have hA : PerTimeDomAt P size (fun N u (_ : Ω) => A N u) (fun N u _ => A N u) :=
    perTimeCalc_refl hsize fun N u _ => (sc.A_pos N u).le
  have h3 := perTimeCalc_mul hsize (fun N u _ => (sc.A_pos N u).le)
    (fun N u ω => mul_nonneg (hbd0 l₁ N u ω) (hbd0 l₂ N u ω)) h12 hA
  exact stochDom_of_le_left_eventually (Eventually.of_forall fun N u ω =>
    h.xiL_split n l₁ l₂ (by omega) (by omega) (by omega) N u ω) h3

/-- **(5.120)** (deterministic). -/
private theorem step3_rhs5119_le (sc : Step3Scales As R A) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∀ᶠ N : ℕ in atTop, ∀ u, step3rhs5119 As R A n k N u ≤ 4 * step3_Psi (As N) (R N) n k ^ 2 := by
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u
  obtain ⟨hAs, hv, hRv⟩ := hu u
  have ha0 : 0 < As N := sc.As_pos N
  rw [step3_Psi_eq ha0.le, step3rhs5119]
  refine step3_ineq_5120 (α := 2 * ((n + 1) / 2) - 1) (β := 2 * (n + 1 - (n + 1) / 2) - 1) hb hR hv
    hRv (Real.rpow_nonneg ha0.le _) hn (by omega) (by omega) (by omega)
    (step3_psi_nonneg ha0.le (sc.R_nonneg N) (sc.A_pos N u).le)
    (step3_psi_nonneg ha0.le (sc.R_nonneg N) (sc.A_pos N u).le) ?_ ?_
  · exact step3_psi_pred_le ha0 (sc.R_nonneg N) hAs hk _
  · exact step3_psi_pred_le ha0 (sc.R_nonneg N) hAs hk _

/-- **(5.111)**. -/
private theorem step3_xiL_two_mul_add_two (h : Step3Hyp P size X Y As R A) {n k : ℕ}
    (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hS : ∀ m, 1 ≤ m → m ≤ n + 2 → step3S P size X As R A m (k - 1)) :
    PerTimeDomAt P size (Y (2 * n + 2)) fun N _ _ => step3_Psi (As N) (R N) n k ^ 2 :=
  perTimeCalc_mono h.hsize (fun N _ _ => sq_nonneg _) 4
    ((step3_rhs5119_le h.scales (by omega) hk).mono fun _ hN u _ => hN u) (step3_xiL_5119 h hn hS)

/-- `S(2,3)` gives `Ξ^{(𝓛-𝒦)}_{u,2} ≺ M_s^{1/2}`. -/
private theorem step3_xiLK_two_le (h : Step3Hyp P size X Y As R A)
    (hS2 : step3S P size X As R A 2 3) :
    PerTimeDomAt P size (X 2) fun N _ _ => As N ^ ((1 : ℝ) / 2) := by
  have sc := h.scales
  refine perTimeCalc_mono h.hsize (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 2 ?_ hS2
  filter_upwards [sc.kit] with N ⟨h1, hb, hR, hu⟩ u ω
  obtain ⟨-, hv, hRv⟩ := hu u
  obtain ⟨-, -, -, -, -, hRb⟩ := step3_scale_facts hb hR hv hRv
  have ha0 := (sc.As_pos N).le
  rw [step3_psi_of_ne_zero (by norm_num), step3_Psi, step3_rpow_half_eq ha0,
    show (1 : ℝ) - ((3 : ℕ) : ℝ) / 4 = 1 / 4 by norm_num]
  have hb0 : 0 ≤ As N ^ ((1 : ℝ) / 4) := by linarith
  simp only [show 2 - 1 = 1 from rfl, pow_one]
  nlinarith

/-- A product bound for the quadratic term of (5.92). -/
private theorem step3_quad_of {p q : ℕ} {ζp ζq : ∀ N, U N → ℝ} {Φ : ℕ → ℝ}
    (h : Step3Hyp P size X Y As R A)
    (hζp : ∀ N u, 0 ≤ ζp N u) (hζq : ∀ N u, 0 ≤ ζq N u) (hΦ : ∀ N, 0 ≤ Φ N)
    (hp : PerTimeDomAt P size (X p) fun N u _ => ζp N u)
    (hq : PerTimeDomAt P size (X q) fun N u _ => ζq N u)
    (C : ℝ) (hle : ∀ᶠ N : ℕ in atTop, ∀ u, ζp N u * ζq N u * (A N u)⁻¹ ≤ C * Φ N) :
    PerTimeDomAt P size (fun N u ω => X p N u ω * X q N u ω * (A N u)⁻¹) fun N _ _ => Φ N := by
  have hsize := h.hsize
  have hA' : ∀ N u (_ : Ω), 0 ≤ (A N u)⁻¹ := fun N u _ => (inv_pos.2 (h.scales.A_pos N u)).le
  have h12 := perTimeCalc_mul hsize (h.X_nonneg q) (fun N u _ => hζp N u) hp hq
  have h3 := perTimeCalc_mul hsize hA' (fun N u _ => mul_nonneg (hζp N u) (hζq N u)) h12
    (perTimeCalc_refl hsize hA')
  exact perTimeCalc_mono hsize (fun N _ _ => hΦ N) C (hle.mono fun N hN u _ => hN u) h3


/-- **(5.109), the induction step**.  For `n ≥ 3`, `k ≥ 1`: if
`S(m,k)` holds for `m ≤ n - 1` and `S(m,k-1)` for `m ≤ n + 2`, then `S(n,k)` holds (also uses
`S(2,3)`). -/
private theorem step3_S_of_S (h : Step3Hyp P size X Y As R A) {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hSk : ∀ m, 1 ≤ m → m ≤ n - 1 → step3S P size X As R A m k)
    (hSk1 : ∀ m, 1 ≤ m → m ≤ n + 2 → step3S P size X As R A m (k - 1))
    (hS2 : step3S P size X As R A 2 3) : step3S P size X As R A n k := by
  have hsize := h.hsize
  have sc := h.scales
  have hk0 : k ≠ 0 := by omega
  have ha0 : ∀ N, 0 < As N := sc.As_pos
  set Ψ : ℕ → ℝ := fun N => step3_Psi (As N) (R N) n k with hΨdef
  have hΨ0 : ∀ N, 0 ≤ Ψ N := fun N => step3_Psi_nonneg (ha0 N).le (sc.R_nonneg N)
  have hS' : ∀ m, step3S P size X As R A m k ↔
      PerTimeDomAt P size (X m) fun N _ _ => step3_Psi (As N) (R N) m k := fun m => by
    unfold step3S; simp only [step3_psi_of_ne_zero hk0]
  -- the long loop `Ξ^{(L)}_{2n+2}`: (5.111)
  have hlongloop := step3_xiL_two_mul_add_two h hn hk hSk1
  -- the short loops `m < n`
  have hsmall : ∀ m, 1 ≤ m → m < n → PerTimeDomAt P size (X m) fun N _ _ => Ψ N := by
    intro m hm1 hmn
    refine perTimeCalc_mono hsize (fun N _ _ => hΨ0 N) 1 ?_ ((hS' m).1 (hSk m hm1 (by omega)))
    filter_upwards [sc.one_le_R] with N hR u ω
    rw [one_mul]
    exact step3_Psi_mono (ha0 N).le hR hmn.le
  -- `Ξ^{(L-K)}_2 ≺ b²` and `Ξ^{(L-K)}_n ≺ Ψ(n, k-1)`
  have hX2 := step3_xiLK_two_le h hS2
  have hXn := hSk1 n (by omega) (by omega)
  have hpsi0 : ∀ m N (u : U N), 0 ≤ step3_psi (As N) (R N) (A N u) m (k - 1) := fun m N u =>
    step3_psi_nonneg (ha0 N).le (sc.R_nonneg N) (sc.A_pos N u).le
  have hquad2 : ∀ᶠ N : ℕ in atTop, ∀ u, As N ^ ((1 : ℝ) / 2) *
      step3_psi (As N) (R N) (A N u) n (k - 1) * (A N u)⁻¹ ≤ 2 * Ψ N := by
    filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u
    obtain ⟨hAs, hv, hRv⟩ := hu u
    obtain ⟨hv0, -⟩ := step3_scale_facts hb hR hv hRv
    change _ ≤ 2 * step3_Psi (As N) (R N) n k
    rw [step3_Psi_eq (ha0 N).le, step3_rpow_half_eq (ha0 N).le]
    refine le_trans ?_ (step3_ineq_quad_two hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _) n)
    gcongr
    exact step3_psi_pred_le (ha0 N) (sc.R_nonneg N) hAs hk n
  have hquad : ∀ m, 2 ≤ m → m ≤ n → PerTimeDomAt P size
      (fun N u ω => X m N u ω * X (n - m + 2) N u ω * (A N u)⁻¹) fun N _ _ => Ψ N := by
    intro m hm2 hmn
    rcases (show m = 2 ∨ m = n ∨ (3 ≤ m ∧ m ≤ n - 1) by omega) with rfl | rfl | ⟨hm3, hm⟩
    · rw [show n - 2 + 2 = n by omega]
      exact step3_quad_of h (fun N _ => Real.rpow_nonneg (ha0 N).le _) (hpsi0 n) hΨ0 hX2 hXn 2
        hquad2
    · rw [show m - m + 2 = 2 by omega]
      refine step3_quad_of h (hpsi0 m) (fun N _ => Real.rpow_nonneg (ha0 N).le _) hΨ0 hXn hX2 2 ?_
      filter_upwards [hquad2] with N hN u
      rw [mul_comm (step3_psi _ _ _ _ _)]
      exact hN u
    · refine step3_quad_of h (fun N _ => step3_Psi_nonneg (ha0 N).le (sc.R_nonneg N))
        (fun N _ => step3_Psi_nonneg (ha0 N).le (sc.R_nonneg N)) hΨ0
        ((hS' m).1 (hSk m (by omega) hm)) ((hS' (n - m + 2)).1 (hSk _ (by omega) (by omega)))
        4 ?_
      filter_upwards [sc.kit] with N ⟨h1, hb, hR, hu⟩ u
      obtain ⟨_, hv, hRv⟩ := hu u
      change _ ≤ 4 * step3_Psi (As N) (R N) n k
      simp only [step3_Psi_eq (ha0 N).le]
      exact step3_ineq_quad hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _)
        (step3_rpow_one_sub_le h1 hk) (by omega) (by omega) (by omega)
  -- the `(n+1)`-loop `Ξ^{(L)}_{n+1}`, via (5.107)
  have hlong : PerTimeDomAt P size (Y (n + 1)) fun N _ _ => Ψ N := by
    have h1 := step3_trans hsize (h.xiL_le (n + 1) (by omega))
      (step3_one_add_inv_mul hsize sc.A_pos (h.X_nonneg _) (hSk1 (n + 1) (by omega) (by omega)))
    refine perTimeCalc_mono hsize (fun N _ _ => hΨ0 N) 3 ?_ h1
    filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
    obtain ⟨hAs, hv, hRv⟩ := hu u
    obtain ⟨hv0, -⟩ := step3_scale_facts hb hR hv hRv
    change _ ≤ 3 * step3_Psi (As N) (R N) n k
    rw [step3_Psi_eq (ha0 N).le]
    refine le_trans ?_ (step3_ineq_long hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _)
      (by omega : 1 ≤ n))
    gcongr
    have := step3_psi_pred_le (ha0 N) (sc.R_nonneg N) hAs hk (n + 1)
    simpa using this
  -- (5.112) ⟹ (5.113)
  have hΛ : ∀ᶠ N : ℕ in atTop, 1 ≤ Ψ N ^ 2 := by
    filter_upwards [sc.one_le_As] with N h1
    have : 1 ≤ Ψ N := by
      have h2 : 1 ≤ As N ^ ((1 : ℝ) / 2) := Real.one_le_rpow h1 (by norm_num)
      have h3 : 0 ≤ R N ^ (n - 1) * As N ^ (1 - (k : ℝ) / 4) := by
        have := sc.R_nonneg N; have := ha0 N; positivity
      simp only [hΨdef, step3_Psi]; linarith
    nlinarith
  have key := h.lemma514 n hn (fun N => Ψ N ^ 2) Ψ (fun N => sq_nonneg _) hΨ0 hΛ hlongloop
    hsmall hquad hlong
  rw [hS']
  refine perTimeCalc_mono hsize (fun N _ _ => hΨ0 N) 2 (Eventually.of_forall fun N u ω => ?_) key
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hΨ0 N)]
  norm_num
  change Ψ N + Ψ N ≤ 2 * Ψ N
  linarith

/-- **The double induction**. -/
private theorem step3_S_all (h : Step3Hyp P size X Y As R A)
    (h0 : ∀ m, 1 ≤ m → step3S P size X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → step3S P size X As R A m l) :
    ∀ k n, 1 ≤ n → step3S P size X As R A n k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn
      rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with hn2 | hn3
      · exact h12 n (k + 1) hn hn2
      · exact step3_S_of_S h hn3 (by omega) (fun m hm1 hm => ihn m (by omega) hm1)
          (fun m hm1 _ => by simpa using ih m hm1) (h12 2 3 (by norm_num) le_rfl)

/-- `Ψ(n, n+1) ≤ 2 M_s^{1/2}` for `R ≤ M_s^{1/4}`. -/
private theorem step3_Psi_succ_le {a r : ℝ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hr : r ≤ a ^ ((1 : ℝ) / 4)) {n : ℕ} (hn : 1 ≤ n) :
    step3_Psi a r n (n + 1) ≤ 2 * a ^ ((1 : ℝ) / 2) := by
  have h1 : r ^ (n - 1) ≤ a ^ (((n - 1 : ℕ) : ℝ) / 4) := by
    rw [step3_rpow_quarter ha.le]; exact pow_le_pow_left₀ hr0 hr _
  have h2 : a ^ (((n - 1 : ℕ) : ℝ) / 4) * a ^ (1 - ((n + 1 : ℕ) : ℝ) / 4) = a ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add ha]; congr 1; rw [Nat.cast_sub hn]; push_cast; ring
  unfold step3_Psi
  have h3 : r ^ (n - 1) * a ^ (1 - ((n + 1 : ℕ) : ℝ) / 4) ≤ a ^ ((1 : ℝ) / 2) := by
    rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ha.le _)
  linarith

/-- **The conclusion of the induction**:
`Ξ^{(𝓛-𝒦)}_{u,n} ≺ M_s^{1/2}` for every `n ≥ 1`. -/
private theorem step3_xiLK_le (h : Step3Hyp P size X Y As R A)
    (h0 : ∀ m, 1 ≤ m → step3S P size X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → step3S P size X As R A m l) {n : ℕ} (hn : 1 ≤ n) :
    PerTimeDomAt P size (X n) fun N _ _ => As N ^ ((1 : ℝ) / 2) := by
  have sc := h.scales
  refine perTimeCalc_mono h.hsize (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 2 ?_
    (step3_S_all h h0 h12 (n + 1) n hn)
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
  obtain ⟨_, hv, hRv⟩ := hu u
  obtain ⟨-, -, -, -, -, hRb⟩ := step3_scale_facts hb hR hv hRv
  rw [step3_psi_of_ne_zero (by omega)]
  exact step3_Psi_succ_le (sc.As_pos N) (sc.R_nonneg N) hRb hn

/-- **(2.77) from (5.107)** at a given length `n`. -/
private theorem step3_xiL_le_one_of (h : Step3Hyp P size X Y As R A)
    (h0 : ∀ m, 1 ≤ m → step3S P size X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → step3S P size X As R A m l) {n : ℕ} (hn : 1 ≤ n)
    (h107 : PerTimeDomAt P size (Y n) fun N u ω => 1 + (A N u)⁻¹ * X n N u ω) :
    PerTimeDomAt P size (Y n) fun _ _ _ => 1 := by
  have sc := h.scales
  refine perTimeCalc_mono h.hsize (fun _ _ _ => zero_le_one) 2 ?_ (step3_trans h.hsize h107
    (step3_one_add_inv_mul h.hsize sc.A_pos (h.X_nonneg n) (step3_xiLK_le h h0 h12 hn)))
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
  obtain ⟨_, hv, hRv⟩ := hu u
  obtain ⟨hv0, -, hb2v, -⟩ := step3_scale_facts hb hR hv hRv
  rw [step3_rpow_half_eq (sc.As_pos N).le, mul_one]
  have : (A N u)⁻¹ * (As N ^ ((1 : ℝ) / 4)) ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ hv0]; linarith
  linarith

end Abstract

/-! ## 4. Generic `≺` lemmas for the deterministic argument -/

section Generic

open PerTimeCalc.PerTime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- `x^C · x^{-(D+C)} = x^{-D}` for `x ≥ 0`, `D ≠ 0`. -/
private theorem step3_rpow_mul_rpow_neg_add {x : ℝ} (hx : 0 ≤ x) (C D : ℝ) (hD : D ≠ 0) :
    x ^ C * x ^ (-(D + C)) = x ^ (-D) := by
  rw [← Real.rpow_add' hx (by rw [show C + -(D + C) = -D by ring]; exact neg_ne_zero.mpr hD)]
  congr 1; ring

/-- If `ξ ≤ (size l)^δ ζ` eventually, for every `δ > 0`, then `ξ ≺ ζ` (`ξ, ζ ≥ 0`). -/
private theorem step3_of_forall_le_rpow_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : ∀ δ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ δ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  refine of_forall_rpow_mul fun δ hδ => ?_
  refine perTimeCalc_mono hsize
    (fun l u ω => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ l u ω)) 1 ?_
    (perTimeCalc_refl hsize hξ)
  filter_upwards [h δ hδ] with l hl u ω
  rw [one_mul]; exact hl u ω

/-- Multiplication of both sides of `≺` by a non-negative deterministic factor. -/
private theorem step3_mul_det (hsize : Tendsto size atTop atTop) {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) {c : ∀ l, U l → ℝ} (hc : ∀ l u, 0 ≤ c l u)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l u ω * c l u) (fun l u ω => ζ l u ω * c l u) :=
  perTimeCalc_mul hsize (fun l u _ => hc l u) hζ h (perTimeCalc_refl hsize fun l u _ => hc l u)

/-- Pull-back of a time-only statement to the index `(u, v)`. -/
private theorem step3_pullback {V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (U := fun l => U l × V l) (fun l p ω => ξ l p.1 ω)
      (fun l p ω => ζ l p.1 ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl p
  exact hl p.1

/-- **The label maximum**: if `ξ(u,v) ≺ ζ(u)` at every `(u, v)` and the label set has at most
`(size l)^C` elements, then `max_v ξ(u,v) ≺ ζ(u)` (union bound with `D` replaced by `D + C`;
the pattern of `stochDomAt_of_perTimeDomAt`, with the time kept outside the probability). -/
private theorem step3_label_max {V : ℕ → Type*} [∀ l, Fintype (V l)] [∀ l, Nonempty (V l)]
    {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ l : ℕ in atTop, (Fintype.card (V l) : ℝ) ≤ (size l : ℝ) ^ C)
    {ξ : ∀ l, U l → V l → Ω → ℝ} {ζ : ∀ l, U l → Ω → ℝ}
    (h : PerTimeDomAt P size (U := fun l => U l × V l) (fun l p ω => ξ l p.1 p.2 ω)
      (fun l p ω => ζ l p.1 ω)) :
    PerTimeDomAt P size
      (fun l u ω => Finset.univ.sup' Finset.univ_nonempty (fun v => ξ l u v ω)) ζ := by
  intro τ hτ D hD
  filter_upwards [hcard, h τ hτ (D + C) (by linarith)] with l hcard hl u
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  have hset : {ω | (size l : ℝ) ^ τ * ζ l u ω <
      Finset.univ.sup' Finset.univ_nonempty (fun v => ξ l u v ω)} ⊆
      ⋃ v, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u v ω} := by
    intro ω hω
    have hω' : (size l : ℝ) ^ τ * ζ l u ω <
        Finset.univ.sup' Finset.univ_nonempty (fun v => ξ l u v ω) := hω
    obtain ⟨v, -, hv⟩ := (Finset.lt_sup'_iff _).1 hω'
    exact Set.mem_iUnion.2 ⟨v, hv⟩
  calc P {ω | (size l : ℝ) ^ τ * ζ l u ω <
        Finset.univ.sup' Finset.univ_nonempty (fun v => ξ l u v ω)}
      ≤ P (⋃ v, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u v ω}) := measure_mono hset
    _ ≤ ∑ v, P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u v ω} := measure_iUnion_fintype_le P _
    _ ≤ ∑ _v : V l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun v _ => hl (u, v)
    _ = ENNReal.ofReal (Fintype.card (V l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [step3_rpow_mul_rpow_neg_add hs C D hD.ne']

end Generic

/-! ## 5. Matrix-level identities: charges of the two-loop, and the one-loop -/

section MatrixLevel

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The entries of the block resolvent are those of the fine resolvent. -/
private theorem step3_green_blockMat (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (p q : BlockIndex L W) :
    green (blockMat M) z p q =
      (M - z • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ ((splitEquiv L W).symm p)
        ((splitEquiv L W).symm q) := by
  have h : blockMat M - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - z • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix (splitEquiv L W).symm
        (splitEquiv L W).symm := by
    ext i j
    simp [blockMat, Matrix.one_apply]
  unfold green
  rw [h, Matrix.inv_submatrix_equiv]
  rfl

/-- `|G(σ)_{pp} - m(σ)| ≤ max_{ij} |(G - m)_{ij}|` for the block resolvent of a Hermitian `M`. -/
private theorem step3_Gsig_diag_le (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (σ : Bool) (p : BlockIndex L W) :
    ‖Gsig (blockMat M) (spectralZ E u) σ p p - KLoop.mSig E σ‖ ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hle : llErrMat L W E u M ((splitEquiv L W).symm p) ((splitEquiv L W).symm p) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2) :=
    Finset.le_sup' (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2)
      (Finset.mem_univ (((splitEquiv L W).symm p), ((splitEquiv L W).symm p)))
  refine le_trans (le_of_eq ?_) hle
  cases σ
  · have hG : Gsig (blockMat M) (spectralZ E u) false =
        (Gsig (blockMat M) (spectralZ E u) true)ᴴ := by
      have := Gsig_conjTranspose hH (spectralZ E u) true
      simpa using this.symm
    rw [hG, Matrix.conjTranspose_apply]
    simp only [KLoop.mSig, Bool.false_eq_true, ↓reduceIte, Gsig_true, llErrMat,
      step3_green_blockMat, Complex.star_def]
    rw [← map_sub, Complex.norm_conj]
  · simp only [KLoop.mSig, ↓reduceIte, Gsig_true, llErrMat, step3_green_blockMat]


/-- **One-loop**: `|(𝓛-𝒦)_{u,σ,a}| ≤ max_{ij} |(G_u - m)_{ij}|` (`𝒦 = m(σ)` by `Kgen` at length
one, `𝓛 = Σ_p bw_a(p) G(σ)_{pp}` and `Σ_p bw_a(p) = 1`). -/
private theorem step3_lkGen_one_le (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    lkGen L W E u M σ a ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2) := by
  set Lm := Finset.univ.sup' Finset.univ_nonempty
      (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2) with hLm
  have hloop : loopOf σ a = ⟨[σ 0], [a 0]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have hK : KLoop.Kcal L W E u ⟨[σ 0], [a 0]⟩ = KLoop.mSig E (σ 0) := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  have hg : gloop L W (blockMat M) (spectralZ E u) ⟨[σ 0], [a 0]⟩ =
      ∑ p : BlockIndex L W,
        Gsig (blockMat M) (spectralZ E u) (σ 0) p p * ((bw (a 0) p : ℝ) : ℂ) := by
    simp [gloop, gloopProd_cons, gloopProd_nil, Eblk_eq_diagonal_bw, Matrix.trace,
      Matrix.mul_diagonal]
  have hsum : ∑ p : BlockIndex L W, KLoop.mSig E (σ 0) * ((bw (a 0) p : ℝ) : ℂ) =
      KLoop.mSig E (σ 0) := by
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_bw]; simp
  unfold lkGen
  rw [hloop, hK, hg]
  calc ‖∑ p : BlockIndex L W,
          Gsig (blockMat M) (spectralZ E u) (σ 0) p p * ((bw (a 0) p : ℝ) : ℂ) -
        KLoop.mSig E (σ 0)‖
      = ‖∑ p : BlockIndex L W, (Gsig (blockMat M) (spectralZ E u) (σ 0) p p -
          KLoop.mSig E (σ 0)) * ((bw (a 0) p : ℝ) : ℂ)‖ := by
        congr 1
        conv_lhs => rw [← hsum]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ ≤ ∑ p : BlockIndex L W, ‖(Gsig (blockMat M) (spectralZ E u) (σ 0) p p -
          KLoop.mSig E (σ 0)) * ((bw (a 0) p : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ p : BlockIndex L W, Lm * bw (a 0) p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bw_nonneg _ _)]
        exact mul_le_mul_of_nonneg_right (step3_Gsig_diag_le E u M hM (σ 0) p) (bw_nonneg _ _)
    _ = Lm := by rw [← Finset.mul_sum, sum_bw, mul_one]

end MatrixLevel

section Charges

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `𝒦` at `σ = (+,-)` is `Kpm` (`Kcal_two_cases`), so `lkGen` at `(+,-)` is `lkErrMat`. -/
private theorem step3_lkGen_pm (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    lkGen L W E u M ![true, false] ![a, b] = lkErrMat L W E u M a b := by
  have hloop : loopOf ![true, false] ![a, b] = pmLoop a b := by
    simp [loopOf, pmLoop, List.ofFn_succ]
  have hK := (KLoop.Kcal_two_cases L W E u a b).1
  unfold lkGen lkErrMat
  rw [hloop]
  congr 2
  rw [pmLoop, hK]
  unfold Kpm
  simp [Theta, inv_pow]

/-- **Rotation** `(-,+),(a,b) ↦ (+,-),(b,a)` (`gloop_rotate`, `Kcal_rotate`). -/
private theorem step3_lkGen_mp (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    lkGen L W E u M ![false, true] ![a, b] = lkGen L W E u M ![true, false] ![b, a] := by
  have h1 : loopOf ![false, true] ![a, b] = ⟨false :: [true], a :: [b]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have h2 : loopOf ![true, false] ![b, a] = ⟨[true] ++ [false], [b] ++ [a]⟩ := by
    simp [loopOf, List.ofFn_succ]
  unfold lkGen
  rw [h1, h2, gloop_rotate false a (by simp),
    KLoop.Kcal_rotate L W hL hW E hE u hu false a [true] [b] (by simp)]

omit [NeZero L] in
private theorem step3_SB_conjTranspose : (SB L)ᴴ = SB L := by
  ext a b
  rw [Matrix.conjTranspose_apply, SB_apply, SB_apply, ← neg_sub b a, sbKernel_neg L (b - a)]
  unfold sbKernel
  split_ifs <;> simp

/-- `(Θ_ξ)ᴴ = Θ_{ξ̄}` (`SB` is real symmetric). -/
private theorem step3_Theta_conjTranspose (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta L ξ)ᴴ = Theta L (starRingEnd ℂ ξ) := by
  have hξ' : ‖starRingEnd ℂ ξ‖ < 1 := by rwa [Complex.norm_conj]
  refine eq_Theta_of_mul L hL hξ' ?_
  calc (Theta L ξ)ᴴ * (1 - starRingEnd ℂ ξ • SB L)
      = (Theta L ξ)ᴴ * (1 - ξ • SB L)ᴴ := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
          step3_SB_conjTranspose]
        rfl
    _ = ((1 - ξ • SB L) * Theta L ξ)ᴴ := (Matrix.conjTranspose_mul _ _).symm
    _ = 1 := by rw [mul_Theta L hL hξ, Matrix.conjTranspose_one]

omit [NeZero W] in
/-- The `(-,-)` value of `𝒦` is the conjugate of the `(+,+)` value at the swapped labels. -/
private theorem step3_Kcal_mm (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (a b : Z2 L) :
    KLoop.Kcal L W E u ⟨[false, false], [a, b]⟩ =
      starRingEnd ℂ (KLoop.Kcal L W E u ⟨[true, true], [b, a]⟩) := by
  have hm : KLoop.mSig E false = starRingEnd ℂ (KLoop.mSig E true) := by simp [KLoop.mSig]
  have hnorm : ‖(u : ℂ) * (KLoop.mSig E true * KLoop.mSig E true)‖ < 1 := by
    have h1 : ‖KLoop.mSig E true‖ = 1 := by simpa [KLoop.mSig] using Gauss.norm_spectralM hE
    rw [norm_mul, norm_mul, h1, Complex.norm_real, Real.norm_of_nonneg hu.1]
    simpa using hu.2
  have hΘ : starRingEnd ℂ (Theta L ((u : ℂ) * (KLoop.mSig E true * KLoop.mSig E true)) b a) =
      Theta L (starRingEnd ℂ ((u : ℂ) * (KLoop.mSig E true * KLoop.mSig E true))) a b := by
    have := congrArg (fun X => X a b) (step3_Theta_conjTranspose hL hnorm)
    simpa [Matrix.conjTranspose_apply] using this
  rw [KLoop.Kcal_two, KLoop.Kcal_two, map_mul, hΘ]
  simp [hm, map_mul, Complex.conj_ofReal]

/-- The `(-,-)` two-loop is the conjugate of the `(+,+)` two-loop at swapped labels. -/
private theorem step3_gloop_mm (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (a b : Z2 L) :
    gloop L W (blockMat M) (spectralZ E u) ⟨[false, false], [a, b]⟩ =
      starRingEnd ℂ (gloop L W (blockMat M) (spectralZ E u) ⟨[true, true], [b, a]⟩) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hGm : Gsig (blockMat M) (spectralZ E u) false =
      (Gsig (blockMat M) (spectralZ E u) true)ᴴ := by
    have := Gsig_conjTranspose hH (spectralZ E u) true
    simpa using this.symm
  rw [gloop_two, gloop_two, hGm, starRingEnd_apply, ← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Eblk_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Gsig (blockMat M) (spectralZ E u) true)ᴴ]
  simp only [Matrix.mul_assoc]

/-- `(-,-)` two-loop error = the `(+,+)` one at swapped labels. -/
private theorem step3_lkGen_mm (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (a b : Z2 L) :
    lkGen L W E u M ![false, false] ![a, b] = lkGen L W E u M ![true, true] ![b, a] := by
  have h1 : loopOf ![false, false] ![a, b] = ⟨[false, false], [a, b]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have h2 : loopOf ![true, true] ![b, a] = ⟨[true, true], [b, a]⟩ := by
    simp [loopOf, List.ofFn_succ]
  unfold lkGen
  rw [h1, h2, step3_gloop_mm E u M hM a b, step3_Kcal_mm hL hE hu a b, ← map_sub,
    Complex.norm_conj]

/-- **The four charges of the two-loop**: every `|(𝓛-𝒦)_{u,σ,a}|` at `k = 2` is bounded by the
`(+,+)` maximum or by the `(+,-)` maximum. -/
private theorem step3_lkGen_two_le (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    lkGen L W E u M σ a ≤
      max (Finset.univ.sup' Finset.univ_nonempty
            (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]))
        (Finset.univ.sup' Finset.univ_nonempty
            (fun p : Z2 L × Z2 L => lkErrMat L W E u M p.1 p.2)) := by
  have hσ : ∃ s0 s1 : Bool, σ = ![s0, s1] := ⟨σ 0, σ 1, by funext i; fin_cases i <;> rfl⟩
  have ha : ∃ a0 a1 : Z2 L, a = ![a0, a1] := ⟨a 0, a 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨s0, s1, rfl⟩ := hσ
  obtain ⟨a0, a1, rfl⟩ := ha
  have hPP : ∀ p : Z2 L × Z2 L, lkGen L W E u M ![true, true] ![p.1, p.2] ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]) :=
    fun p => Finset.le_sup' (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2])
      (Finset.mem_univ p)
  have hPM : ∀ p : Z2 L × Z2 L, lkErrMat L W E u M p.1 p.2 ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 L × Z2 L => lkErrMat L W E u M p.1 p.2) :=
    fun p => Finset.le_sup' (fun p : Z2 L × Z2 L => lkErrMat L W E u M p.1 p.2)
      (Finset.mem_univ p)
  cases s0 <;> cases s1
  · rw [step3_lkGen_mm hL hE.le hu M hM]
    exact le_max_of_le_left (hPP (a1, a0))
  · rw [step3_lkGen_mp hL hW hE hu, step3_lkGen_pm]
    exact le_max_of_le_right (hPM (a1, a0))
  · rw [step3_lkGen_pm]
    exact le_max_of_le_right (hPM (a0, a1))
  · exact le_max_of_le_left (hPP (a0, a1))

end Charges

/-! ## 6. The flow families, the context, and the scale conditions -/

section Flow

variable {d : Sizes}

/-- The hypotheses of `MainIndHyp` that Step 3 uses. -/
private structure Step3Ctx (d : Sizes) (κ c : ℝ) (E s t : ℕ → ℝ) : Prop where
  hκ : 0 < κ
  hE : ∀ n, |E n| ≤ 2 - κ
  hc : 0 < c
  hs0 : ∀ n, 0 ≤ s n
  hst : ∀ n, s n ≤ t n
  ht1 : ∀ n, t n < 1
  hsize : SizeTendsto d
  hband : Bandwidth d c
  hcond : CondStInd d E s t

private theorem step3_ctx_of {κ c τ : ℝ} {E s t : ℕ → ℝ} (h : MainIndHyp d κ c τ E s t) :
    Step3Ctx d κ c E s t := by
  obtain ⟨hκ, hE, hc, -, hs0, hst, ht1, hsize, hband, hcond, -, -, -⟩ := h
  exact ⟨hκ, hE, hc, hs0, hst, ht1, hsize, hband, hcond⟩

/-- `Ξ^{(𝓛-𝒦)}_{u,k}` as the family `k ↦ (n, u, ω) ↦ …` on `u ∈ [s,t]`. -/
private abbrev step3X (d : Sizes) (E s t : ℕ → ℝ) :
    ℕ → ∀ n, TimeIcc s t n → Sizes.SeqΩ d → ℝ :=
  fun k n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k

/-- `Ξ^{(𝓛)}_{u,k}` on `u ∈ [s,t]`. -/
private abbrev step3Y (d : Sizes) (E s t : ℕ → ℝ) :
    ℕ → ∀ n, TimeIcc s t n → Sizes.SeqΩ d → ℝ :=
  fun k n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k

/-- `M_u` for `u ∈ [s,t]`. -/
private abbrev step3A (d : Sizes) (E s t : ℕ → ℝ) : ∀ n, TimeIcc s t n → ℝ :=
  fun n u => scaleM (d.L n) (d.W n) (E n) u

/-- `M_s`. -/
private abbrev step3As (d : Sizes) (E s : ℕ → ℝ) : ℕ → ℝ :=
  fun n => scaleM (d.L n) (d.W n) (E n) (s n)

/-- `R = (ℓ_t/ℓ_s)²` (the `d = 2` change with respect to the one-dimensional case: `Ψ` carries
`(ℓ_t/ℓ_s)^{2n-2}`). -/
private abbrev step3R (d : Sizes) (_E s t : ℕ → ℝ) : ℕ → ℝ :=
  fun n => (ellT (d.L n) (t n) / ellT (d.L n) (s n)) ^ 2

private theorem step3_one_le_L (d : Sizes) (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem step3_one_le_W (d : Sizes) (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem step3_one_le_size (d : Sizes) (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h : 1 ≤ d.size n :=
    Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))
  exact_mod_cast h

variable {κ c : ℝ} {E s t : ℕ → ℝ}

private theorem Step3Ctx.E2 (h : Step3Ctx d κ c E s t) (n : ℕ) : |E n| < 2 := by
  linarith [h.hE n, h.hκ]

private theorem Step3Ctx.u0 (h : Step3Ctx d κ c E s t) (n : ℕ) (u : TimeIcc s t n) :
    0 ≤ (u : ℝ) := (h.hs0 n).trans u.2.1

private theorem Step3Ctx.u1 (h : Step3Ctx d κ c E s t) (n : ℕ) (u : TimeIcc s t n) :
    (u : ℝ) < 1 := u.2.2.trans_lt (h.ht1 n)

private theorem Step3Ctx.s1 (h : Step3Ctx d κ c E s t) (n : ℕ) : s n < 1 :=
  (h.hst n).trans_lt (h.ht1 n)

private theorem Step3Ctx.tendsto (h : Step3Ctx d κ c E s t) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h.hsize

private theorem Step3Ctx.A_pos (h : Step3Ctx d κ c E s t) (n : ℕ) (u : TimeIcc s t n) :
    0 < scaleM (d.L n) (d.W n) (E n) u :=
  scaleM_pos (step3_one_le_L d n) (step3_one_le_W d n) (h.E2 n) (h.u1 n u)

private theorem Step3Ctx.As_pos (h : Step3Ctx d κ c E s t) (n : ℕ) :
    0 < scaleM (d.L n) (d.W n) (E n) (s n) :=
  scaleM_pos (step3_one_le_L d n) (step3_one_le_W d n) (h.E2 n) (h.s1 n)

/-- `xiL` and `xiLK` are non-negative when the scale is. -/
private theorem step3_xiL_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ}
    (hM : 0 ≤ scaleM L W E u) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) :
    0 ≤ xiL L W E u M k := by
  unfold xiL
  refine mul_nonneg ?_ (pow_nonneg hM _)
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Z2 L) =>
    loopAbs L W E u M p.1 p.2) (Finset.mem_univ (fun _ => true, fun _ => 0)))

private theorem step3_xiLK_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ}
    (hM : 0 ≤ scaleM L W E u) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) :
    0 ≤ xiLK L W E u M k := by
  unfold xiLK
  refine mul_nonneg ?_ (pow_nonneg hM _)
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Z2 L) =>
    lkGen L W E u M p.1 p.2) (Finset.mem_univ (fun _ => true, fun _ => 0)))

/-! ### The scale conditions along the window -/

/-- `ρ^30 ≤ M` from the step condition `M⁻¹ ≤ ((1-t)/(1-s))^30`, `ρ = (1-s)/(1-t)`. -/
private theorem step3_pow30 {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) (h : M⁻¹ ≤ ρ⁻¹ ^ 30) :
    ρ ^ 30 ≤ M := by
  rw [inv_pow] at h
  exact (inv_le_inv₀ hM (pow_pos hρ 30)).1 h

/-- The pure-real core of `le_A`: `(ℓ_t/ℓ_s)^4 ≤ ρ²`, `ρ^30 ≤ M_s`, `M_s^{29/30} ≤ M_u` give
`R² M_s^{3/4} ≤ M_u` with `R = (ℓ_t/ℓ_s)²` (exponents `1/15 + 3/4 = 49/60 ≤ 29/30`). -/
private theorem step3_le_A_pt {M ρ x Au : ℝ} (hM1 : 1 ≤ M) (hρ0 : 0 ≤ ρ) (hρ30 : ρ ^ 30 ≤ M)
    (hx : x ^ 4 ≤ ρ ^ 2) (hAu : M ^ ((29 : ℝ) / 30) ≤ Au) :
    (x ^ 2) ^ 2 * M ^ ((3 : ℝ) / 4) ≤ Au := by
  have hM0 : 0 < M := by linarith
  have h1 : ρ ^ 2 ≤ M ^ ((1 : ℝ) / 15) := by
    have h2 : ρ ^ 2 = (ρ ^ 30) ^ ((1 : ℝ) / 15) := by
      rw [← Real.rpow_natCast ρ 30, ← Real.rpow_mul hρ0]; norm_num
    rw [h2]; exact Real.rpow_le_rpow (by positivity) hρ30 (by norm_num)
  calc (x ^ 2) ^ 2 * M ^ ((3 : ℝ) / 4) ≤ M ^ ((1 : ℝ) / 15) * M ^ ((3 : ℝ) / 4) := by
        refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
        calc (x ^ 2) ^ 2 = x ^ 4 := by ring
          _ ≤ ρ ^ 2 := hx
          _ ≤ _ := h1
    _ = M ^ ((49 : ℝ) / 60) := by rw [← Real.rpow_add hM0]; norm_num
    _ ≤ M ^ ((29 : ℝ) / 30) := Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
    _ ≤ Au := hAu

/-- `1 ≤ M_s` and `ρ^30 ≤ M_s` from `CondStInd` at one index. -/
private theorem step3_cond_pt {Ms s t : ℝ} (hMs : 0 < Ms) (hst : s ≤ t) (ht : t < 1)
    (h : Ms⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    1 ≤ Ms ∧ ((1 - s) / (1 - t)) ^ 30 ≤ Ms := by
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hρ : 0 < (1 - s) / (1 - t) := div_pos hxs hxt
  have hq : ((1 - t) / (1 - s)) = ((1 - s) / (1 - t))⁻¹ := by rw [inv_div]
  rw [hq] at h
  refine ⟨?_, step3_pow30 hMs hρ h⟩
  have hρ1 : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ hxt]; linarith
  exact le_trans (one_le_pow₀ hρ1) (step3_pow30 hMs hρ h)

/-- **The scale conditions of Step 3** (from the scale facts
`scaleFacts_R2_pt`, `scaleFacts_ellT_pow_four`, `scaleM_anti_ratio`, `ellT_mono_ratio`). -/
private theorem step3_scales (h : Step3Ctx d κ c E s t) :
    Step3Scales (U := fun n => TimeIcc s t n) (step3As d E s) (step3R d E s t)
      (step3A d E s t) where
  As_pos n := h.As_pos n
  R_nonneg n := sq_nonneg _
  A_pos := h.A_pos
  one_le_As := by
    filter_upwards [h.hcond] with n hn
    exact (step3_cond_pt (h.As_pos n) (h.hst n) (h.ht1 n) hn).1
  one_le_R := Eventually.of_forall fun n => by
    have hL := step3_one_le_L d n
    have hle := (ellT_mono_ratio hL (h.hs0 n) (h.hst n) (h.ht1 n)).1
    have hpos := (ellT_pos_le hL (h.s1 n)).1
    exact one_le_pow₀ ((one_le_div hpos).2 hle)
  A_le_As := Eventually.of_forall fun n u =>
    (scaleM_anti_ratio (W := d.W n) (step3_one_le_L d n) (h.E2 n) u.2.1 (h.u1 n u)).1
  le_A := by
    filter_upwards [h.hcond] with n hn u
    have hL := step3_one_le_L d n
    have hW := step3_one_le_W d n
    obtain ⟨hM1, hρ30⟩ := step3_cond_pt (h.As_pos n) (h.hst n) (h.ht1 n) hn
    have hx : (ellT (d.L n) (t n) / ellT (d.L n) (s n)) ^ 4 ≤
        (((1 - s n) / (1 - t n))) ^ 2 := by
      have := scaleFacts_ellT_pow_four hL (h.E2 n) (h.hs0 n) (h.hst n) (h.ht1 n)
      rwa [etaT_div_etaT (h.E2 n) (h.s1 n) (h.ht1 n)] at this
    have hxt : 0 < 1 - t n := by linarith [h.ht1 n]
    have hxs : 0 < 1 - s n := by linarith [h.s1 n]
    exact step3_le_A_pt hM1 (div_pos hxs hxt).le hρ30 hx
      (scaleFacts_R2_pt hL hW (h.E2 n) u.2.1 u.2.2 (h.ht1 n) hn)

end Flow

/-! ## 7. Deterministic bounds between `xiL`, `xiLK` and the primitive loops -/

section Determ

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `max_{σ,a} |𝒦_{u,σ,a}|` over the loops of length `k`. -/
private noncomputable def step3Kmax (L W : ℕ) [NeZero L] (E u : ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : (Fin k → Bool) × (Fin k → Z2 L) => ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖)

omit [NeZero W] in
private theorem step3_Kmax_nonneg (E u : ℝ) (k : ℕ) : 0 ≤ step3Kmax L W E u k :=
  le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Z2 L) =>
    ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖) (Finset.mem_univ (fun _ => true, fun _ => 0)))

omit [NeZero W] in
/-- The supremum of a pointwise bound. -/
private theorem step3_Kmax_le (E u : ℝ) (k : ℕ) {B : ℝ}
    (h : ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L), ‖KLoop.Kcal L W E u (loopOf σ a)‖ ≤ B) :
    step3Kmax L W E u k ≤ B :=
  Finset.sup'_le _ _ fun p _ => h p.1 p.2

/-- **(5.107), first half, pointwise**:
`Ξ^{(𝓛)}_{u,k} ≤ M_u⁻¹ Ξ^{(𝓛-𝒦)}_{u,k} + max|𝒦| M_u^{k-1}`. -/
private theorem step3_xiL_le_pt (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hMs : 0 < scaleM L W E u) {k : ℕ} (hk : 1 ≤ k) :
    xiL L W E u M k ≤ (scaleM L W E u)⁻¹ * xiLK L W E u M k +
      step3Kmax L W E u k * scaleM L W E u ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hT : Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => loopAbs L W E u M p.1 p.2) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => lkGen L W E u M p.1 p.2) +
        step3Kmax L W E u (j + 1) := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : loopAbs L W E u M p.1 p.2 ≤ lkGen L W E u M p.1 p.2 +
        ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖ := by
      unfold loopAbs lkGen
      calc ‖gloop L W (blockMat M) (spectralZ E u) (loopOf p.1 p.2)‖
          = ‖(gloop L W (blockMat M) (spectralZ E u) (loopOf p.1 p.2) -
              KLoop.Kcal L W E u (loopOf p.1 p.2)) + KLoop.Kcal L W E u (loopOf p.1 p.2)‖ := by
            rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    refine h1.trans (add_le_add
      (Finset.le_sup' (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) =>
        lkGen L W E u M p.1 p.2) (Finset.mem_univ p))
      (Finset.le_sup' (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) =>
        ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖) (Finset.mem_univ p)))
  have hpow : 0 ≤ scaleM L W E u ^ (j + 1 - 1) := pow_nonneg hMs.le _
  unfold xiL xiLK
  calc _ ≤ (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => lkGen L W E u M p.1 p.2) +
        step3Kmax L W E u (j + 1)) * scaleM L W E u ^ (j + 1 - 1) :=
        mul_le_mul_of_nonneg_right hT hpow
    _ = _ := by
        rw [Nat.add_sub_cancel, pow_succ]
        field_simp

/-- **(5.107), second half, pointwise**:
`Ξ^{(𝓛-𝒦)}_{u,k} ≤ (Ξ^{(𝓛)}_{u,k} + max|𝒦| M_u^{k-1}) M_u`. -/
private theorem step3_xiLK_le_pt (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hMs : 0 < scaleM L W E u) {k : ℕ} (hk : 1 ≤ k) :
    xiLK L W E u M k ≤ (xiL L W E u M k + step3Kmax L W E u k * scaleM L W E u ^ (k - 1)) *
      scaleM L W E u := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hS : Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => lkGen L W E u M p.1 p.2) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => loopAbs L W E u M p.1 p.2) +
        step3Kmax L W E u (j + 1) := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : lkGen L W E u M p.1 p.2 ≤ loopAbs L W E u M p.1 p.2 +
        ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖ := by
      unfold loopAbs lkGen
      exact norm_sub_le _ _
    refine h1.trans (add_le_add
      (Finset.le_sup' (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) =>
        loopAbs L W E u M p.1 p.2) (Finset.mem_univ p))
      (Finset.le_sup' (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) =>
        ‖KLoop.Kcal L W E u (loopOf p.1 p.2)‖) (Finset.mem_univ p)))
  have hpow : 0 ≤ scaleM L W E u ^ (j + 1) := pow_nonneg hMs.le _
  unfold xiL xiLK
  calc _ ≤ (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 L) => loopAbs L W E u M p.1 p.2) +
        step3Kmax L W E u (j + 1)) * scaleM L W E u ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hS hpow
    _ = _ := by
        rw [Nat.add_sub_cancel, pow_succ]
        ring

/-- `Ξ^{(𝓛)}_{u,m}` is `loopXi` of the block matrix at `z_u` with the scale `M_u`. -/
private theorem step3_xiL_eq_loopXi (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (m : ℕ) :
    xiL L W E u M m =
      loopXi L W (blockMat M) (spectralZ E u) (scaleM L W E u) m := by
  unfold xiL loopXi loopMax loopAbs loopOf
  rw [Finset.sup'_univ_eq_ciSup]

/-- **(5.118)** for `xiL` (from `loopXi_le`). -/
private theorem step3_xiL_split (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (hA : 0 ≤ scaleM L W E u) {n l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁) (h₂ : 1 ≤ l₂) (hl : l₁ + l₂ = n + 1) :
    xiL L W E u M (2 * n + 2) ≤
      xiL L W E u M (2 * l₁) * xiL L W E u M (2 * l₂) * scaleM L W E u := by
  simp only [step3_xiL_eq_loopXi]
  exact loopXi_le (hM.submatrix _) hA h₁ h₂ hl

end Determ

/-! ## 8. Label counts, and real-variable lemmas for the base cases -/

section Counts

variable (d : Sizes)

private theorem step3_size_ge_LL (n : ℕ) : d.L n * d.L n ≤ d.size n := by
  have hW : 1 ≤ d.W n := d.W_pos n
  rw [Sizes.size_eq]
  calc d.L n * d.L n = 1 * (d.L n * d.L n) := by ring
    _ ≤ d.W n ^ 2 * d.L n ^ 2 := by
        rw [← pow_two]
        exact Nat.mul_le_mul (Nat.one_le_pow _ _ hW) le_rfl

private theorem step3_two_le_size (n : ℕ) : 2 ≤ d.size n := by
  have h1 := step3_size_ge_LL d n
  have h2 := d.three_le_L n
  nlinarith

/-- The loop labels: `2^k (L²)^k ≤ (size)^{2k}`. -/
private theorem step3_card_loops (k n : ℕ) :
    (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ)) : ℝ) := by
  have hc : Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) =
      (2 * (d.L n * d.L n)) ^ k := by
    simp [Fintype.card_prod, ZMod.card, mul_pow]
  have h1 := step3_size_ge_LL d n
  have h2 := step3_two_le_size d n
  have h3 : 2 * (d.L n * d.L n) ≤ d.size n ^ 2 := by nlinarith
  have h4 : (2 * (d.L n * d.L n)) ^ k ≤ (d.size n ^ 2) ^ k := Nat.pow_le_pow_left h3 k
  rw [hc, Real.rpow_natCast]
  have : ((2 * (d.L n * d.L n)) ^ k : ℕ) ≤ (d.size n ^ (2 * k) : ℕ) := by
    rw [pow_mul]; exact h4
  exact_mod_cast this

/-- Pairs of fine indices: `(size)²`. -/
private theorem step3_card_idx (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((2 : ℕ)) : ℝ) := by
  have hc : Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) = d.size n ^ 2 := by
    simp [Fintype.card_prod, ZMod.card, Sizes.size, mul_pow]
    ring
  rw [hc, Real.rpow_natCast]
  exact_mod_cast le_rfl

/-- Pairs of block labels: `L⁴ ≤ (size)²`. -/
private theorem step3_card_pairs (n : ℕ) :
    (Fintype.card (Z2 (d.L n) × Z2 (d.L n)) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (((2 : ℕ)) : ℝ) := by
  have hc : Fintype.card (Z2 (d.L n) × Z2 (d.L n)) = (d.L n * d.L n) * (d.L n * d.L n) := by
    simp [Fintype.card_prod, ZMod.card]
  have h1 := step3_size_ge_LL d n
  rw [hc, Real.rpow_natCast]
  have : (d.L n * d.L n) * (d.L n * d.L n) ≤ d.size n ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul h1 h1
  exact_mod_cast this

end Counts

/-! ## 9. Real-variable lemmas for the base cases -/

section RealLemmas

private theorem step3_ellT_nonneg (L : ℕ) (u : ℝ) : 0 ≤ ellT L u :=
  le_min (by positivity) (Nat.cast_nonneg _)

/-- `M_u ≤ (W L)² = N` (`ℓ_u ≤ L`, `η_u ≤ 1`). -/
private theorem step3_scaleM_le {L W : ℕ} {E u : ℝ} (hL : 1 ≤ L) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    scaleM L W E u ≤ ((W : ℝ) * L) ^ 2 := by
  have hl := ellT_pos_le hL hu1
  have him0 : 0 ≤ (spectralM E).im := by rw [spectralM_im]; positivity
  have him : (spectralM E).im ≤ 1 := by
    rw [spectralM_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have heta : etaT E u ≤ 1 := by
    unfold etaT
    calc (1 - u) * (spectralM E).im ≤ 1 * 1 :=
          mul_le_mul (by linarith) him him0 zero_le_one
      _ = 1 := one_mul 1
  have heta0 : 0 ≤ etaT E u := mul_nonneg (by linarith) him0
  unfold scaleM
  calc (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.1.le hl.2 2) (sq_nonneg _))
          heta heta0 (by positivity)
    _ = ((W : ℝ) * L) ^ 2 := by ring

/-- `W^{-D} M² ≤ 1` for `D = 3/c`, `N^c ≤ W`, `M ≤ N`, `N ≥ 1`. -/
private theorem step3_Wneg_le {W M N c D : ℝ} (hc : 0 < c) (hD : D = 3 / c) (hN1 : 1 ≤ N)
    (hW0 : 0 < W) (hband : N ^ c ≤ W) (hM0 : 0 ≤ M) (hMN : M ≤ N) :
    W ^ (-D) * M ^ 2 ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have h1 : N ^ (3 : ℝ) ≤ W ^ D := by
    calc N ^ (3 : ℝ) = (N ^ c) ^ D := by
          rw [← Real.rpow_mul hN0.le, hD]; congr 1; field_simp
      _ ≤ W ^ D := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hband hD0
  have h2 : M ^ 2 ≤ N ^ (3 : ℝ) := by
    calc M ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hM0 hMN 2
      _ ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
      _ = N ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  rw [Real.rpow_neg hW0.le]
  have hWD : 0 < W ^ D := Real.rpow_pos_of_pos hW0 _
  rw [inv_mul_le_iff₀ hWD, mul_one]
  exact h2.trans h1

/-- `(η_s/η_u)^4 ≤ M_s^{1/2}` for `s ≤ u ≤ t`, from `ρ^30 ≤ M_s`, `1 ≤ M_s`
(`ρ = (1-s)/(1-t)`; exponent `4/30 = 2/15 ≤ 1/2`). -/
private theorem step3_eta4_le {E s u t Ms : ℝ} (hE : |E| < 2) (hsu : s ≤ u) (hut : u ≤ t)
    (ht : t < 1) (hM1 : 1 ≤ Ms) (hρ30 : ((1 - s) / (1 - t)) ^ 30 ≤ Ms) :
    (etaT E s / etaT E u) ^ 4 ≤ Ms ^ ((1 : ℝ) / 2) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hxt : 0 < 1 - t := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hρ0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg hxs.le hxt.le
  rw [etaT_div_etaT hE hs1 hu1]
  have h1 : (1 - s) / (1 - u) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_left hxs.le hxt (by linarith)
  have h2 : ((1 - s) / (1 - u)) ^ 4 ≤ ((1 - s) / (1 - t)) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg hxs.le hxu.le) h1 4
  have h3 : ((1 - s) / (1 - t)) ^ 4 = (((1 - s) / (1 - t)) ^ 30) ^ ((2 : ℝ) / 15) := by
    rw [← Real.rpow_natCast _ 30, ← Real.rpow_mul hρ0, ← Real.rpow_natCast _ 4]; norm_num
  have hM0 : 0 < Ms := by linarith
  calc ((1 - s) / (1 - u)) ^ 4 ≤ ((1 - s) / (1 - t)) ^ 4 := h2
    _ = (((1 - s) / (1 - t)) ^ 30) ^ ((2 : ℝ) / 15) := h3
    _ ≤ Ms ^ ((2 : ℝ) / 15) := Real.rpow_le_rpow (by positivity) hρ30 (by norm_num)
    _ ≤ Ms ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)

/-- The `(+,-)` decay threshold times `M_u²` is `≤ 2 M_s^{1/2}`. -/
private theorem step3_thr_le {Eta Mu Wneg Ms : ℝ} (hMu : 0 < Mu) (hM1 : 1 ≤ Ms)
    (hEta : Eta ≤ Ms ^ ((1 : ℝ) / 2)) (hW : Wneg * Mu ^ 2 ≤ 1) :
    (Eta * (Mu ^ 2)⁻¹ + Wneg) * Mu ^ 2 ≤ 2 * Ms ^ ((1 : ℝ) / 2) := by
  have h1 : 1 ≤ Ms ^ ((1 : ℝ) / 2) := Real.one_le_rpow hM1 (by norm_num)
  have h2 : (Eta * (Mu ^ 2)⁻¹ + Wneg) * Mu ^ 2 = Eta + Wneg * Mu ^ 2 := by
    rw [add_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hMu.ne'), mul_one]
  rw [h2]
  linarith

/-- `(ℓ_u/ℓ_s)^{2(m-1)} ≤ R^{m-1}` with `R = (ℓ_t/ℓ_s)²`, for `s ≤ u ≤ t`. -/
private theorem step3_rho_le {L : ℕ} {s u t : ℝ} (hL : 1 ≤ L) (hs0 : 0 ≤ s) (hsu : s ≤ u)
    (hut : u ≤ t) (ht : t < 1) (m : ℕ) :
    (ellT L u / ellT L s) ^ (2 * (m - 1)) ≤ ((ellT L t / ellT L s) ^ 2) ^ (m - 1) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hpos := (ellT_pos_le hL hs1).1
  have hle : ellT L u ≤ ellT L t :=
    (ellT_mono_ratio hL (hs0.trans hsu) hut ht).1
  have h1 : ellT L u / ellT L s ≤ ellT L t / ellT L s :=
    div_le_div_of_nonneg_right hle hpos.le
  rw [pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _)
    (pow_le_pow_left₀ (div_nonneg (step3_ellT_nonneg _ _) hpos.le) h1 2) _

/-- `M⁻¹^{1/2} · M = M^{1/2}`. -/
private theorem step3_inv_sqrt_mul {M : ℝ} (hM : 0 < M) :
    (M⁻¹) ^ ((1 : ℝ) / 2) * M = M ^ ((1 : ℝ) / 2) := by
  rw [Real.inv_rpow hM.le]
  have hp : 0 < M ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
  have h : M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) = M := by
    rw [← Real.rpow_add hM]; norm_num
  field_simp
  linarith

/-- `Ψ ≥ M_s^{1/2}`. -/
private theorem step3_psi_ge {As R Au : ℝ} (hAs : 0 ≤ As) (hR : 0 ≤ R) (hAu : 0 ≤ Au) (n k : ℕ) :
    As ^ ((1 : ℝ) / 2) ≤ step3_psi As R Au n k := by
  unfold step3_psi
  split_ifs
  · have : 0 ≤ R ^ (n - 1) * Au := by positivity
    linarith
  · unfold step3_Psi
    have : 0 ≤ R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4) := by positivity
    linarith

end RealLemmas

/-! ## 10. The random layer through `KboundConcl`, Step 1 and Step 2 -/

section Random

open PerTimeCalc.PerTime

variable {d : Sizes} {κ c : ℝ} {E s t : ℕ → ℝ}

private theorem step3_Kd_le {Kmax M Nδ : ℝ} {k : ℕ} (hM : 0 < M)
    (h : Kmax ≤ Nδ * M⁻¹ ^ (k - 1)) : Kmax * M ^ (k - 1) ≤ Nδ := by
  calc Kmax * M ^ (k - 1) ≤ Nδ * M⁻¹ ^ (k - 1) * M ^ (k - 1) :=
        mul_le_mul_of_nonneg_right h (pow_nonneg hM.le _)
    _ = Nδ := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hM.ne', one_pow, mul_one]

/-- **The `𝒦` bound** (Lemma `ML:Kbound+pi`, (`eq:bcal_k_2`), `KboundConcl`) for the flow: for
every `δ > 0`, eventually in `n`, for every `u ∈ [s n, t n]`,
`max_{σ,a}|𝒦_{u,σ,a}| ≤ N^δ M_u^{-(k-1)}` (`KLoop.Par κ N` is filled with
`(L n, W n, E n, u)`; `KLoop.Mt = scaleM` by `kloop_Mt_eq`). -/
private theorem step3_Kmax_bound (hK : KboundConcl κ) (h : Step3Ctx d κ c E s t) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      step3Kmax (d.L n) (d.W n) (E n) u k ≤
        ((d.size n : ℕ) : ℝ) ^ δ * ((scaleM (d.L n) (d.W n) (E n) u)⁻¹) ^ (k - 1) := by
  filter_upwards [h.tendsto.eventually (hK k hk δ hδ)] with n hn u
  refine step3_Kmax_le _ _ _ fun σ a => ?_
  have h1 := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n,
    h.hE n, u, h.u0 n u, h.u1 n u⟩, σ, a⟩
  dsimp only at h1
  rwa [kloop_Mt_eq (le_of_lt (h.u1 n u))] at h1

/-- `max|𝒦| M_u^{k-1} ≺ 1`. -/
private theorem step3_Kd_pt (hK : KboundConcl κ) (h : Step3Ctx d κ c E s t) {k : ℕ}
    (hk : 1 ≤ k) :
    PT d s t (fun n u _ => step3Kmax (d.L n) (d.W n) (E n) u k *
      scaleM (d.L n) (d.W n) (E n) u ^ (k - 1)) (fun _ _ _ => 1) := by
  refine step3_of_forall_le_rpow_mul h.tendsto (fun n u _ => mul_nonneg
    (step3_Kmax_nonneg _ _ _) (pow_nonneg (h.A_pos n u).le _)) (fun _ _ _ => zero_le_one) ?_
  intro δ hδ
  filter_upwards [step3_Kmax_bound hK h hk hδ] with n hn u ω
  rw [mul_one]
  exact step3_Kd_le (h.A_pos n u) (hn u)

/-- **(5.107)**, first half: `Ξ^{(𝓛)}_{u,k} ≺ 1 + M_u⁻¹ Ξ^{(𝓛-𝒦)}_{u,k}` for every `k ≥ 1`
(from `KboundConcl` and the triangle inequality). -/
private theorem step3_xiL_le (hK : KboundConcl κ) (h : Step3Ctx d κ c E s t) {k : ℕ}
    (hk : 1 ≤ k) :
    PT d s t (step3Y d E s t k)
      (fun n u ω => 1 + (scaleM (d.L n) (d.W n) (E n) u)⁻¹ * step3X d E s t k n u ω) := by
  have hnn : ∀ n (u : TimeIcc s t n) (ω : Sizes.SeqΩ d),
      0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ * step3X d E s t k n u ω := fun n u ω =>
    mul_nonneg (inv_nonneg.2 (h.A_pos n u).le)
      (step3_xiLK_nonneg (h.A_pos n u).le (Sizes.seqHflow d n u ω) k)
  refine step3_of_forall_le_rpow_mul h.tendsto
    (fun n u ω => step3_xiL_nonneg (h.A_pos n u).le _ k)
    (fun n u ω => by have := hnn n u ω; positivity) ?_
  intro δ hδ
  filter_upwards [step3_Kmax_bound hK h hk hδ] with n hn u ω
  have h1 := step3_xiL_le_pt (E n) u (Sizes.seqHflow d n u ω) (h.A_pos n u) hk
  have hKd := step3_Kd_le (h.A_pos n u) (hn u)
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ δ := Real.one_le_rpow (step3_one_le_size d n) hδ.le
  have hx0 := hnn n u ω
  change xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k ≤ _
  nlinarith [mul_nonneg (sub_nonneg.2 hN1) hx0]

/-- **Step 1 as a statement about `Ξ^{(𝓛)}`**: `Ξ^{(𝓛)}_{u,m} ≺ (ℓ_u/ℓ_s)^{2(m-1)}` (label
maximum of `Step1LoopPT`, times `M_u^{m-1}`). -/
private theorem step3_xiL_step1 (h : Step3Ctx d κ c E s t) (hL1 : Step1LoopPT d E s t)
    {m : ℕ} (hm : 1 ≤ m) :
    PT d s t (step3Y d E s t m)
      (fun n u _ => (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (m - 1))) := by
  have hsize := h.tendsto
  have h1 := step3_label_max (P := Sizes.seqP d) (size := d.size)
    (U := fun n => TimeIcc s t n) (V := fun n => (Fin m → Bool) × (Fin m → Z2 (d.L n)))
    (C := ((2 * m : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (Eventually.of_forall (step3_card_loops d m))
    (ξ := fun n u v ω => loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2)
    (ζ := fun n u _ => (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (m - 1)) *
      (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1)) (hL1 m hm)
  have hζ : ∀ n (u : TimeIcc s t n) (_ : Sizes.SeqΩ d),
      0 ≤ (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (m - 1)) *
        (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := fun n u _ =>
    mul_nonneg (pow_nonneg (div_nonneg (step3_ellT_nonneg _ _) (step3_ellT_nonneg _ _)) _)
      (pow_nonneg (inv_nonneg.2 (h.A_pos n u).le) _)
  have h2 := step3_mul_det hsize hζ
    (c := fun n (u : TimeIcc s t n) => scaleM (d.L n) (d.W n) (E n) u ^ (m - 1))
    (fun n u => pow_nonneg (h.A_pos n u).le _) h1
  refine perTimeCalc_mono hsize (fun n u _ => pow_nonneg (div_nonneg (step3_ellT_nonneg _ _)
    (step3_ellT_nonneg _ _)) _) 1 (Eventually.of_forall fun n u ω => ?_) h2
  show _ * _ * _ ≤ 1 * _
  rw [one_mul, mul_assoc, ← mul_pow, inv_mul_cancel₀ (h.A_pos n u).ne', one_pow, mul_one]

end Random

/-! ## 11. The base cases `S(m,0)`, `m ≥ 1`, and `S(m,l)`, `m ≤ 2` -/

section BaseCases

open PerTimeCalc.PerTime

variable {d : Sizes} {κ c : ℝ} {E s t : ℕ → ℝ}

/-- **The base case `S(m,0)`** (from Step 1 (`lRB1`) and `𝒦`):
`Ξ^{(𝓛-𝒦)}_{u,m} ≺ M_s^{1/2} + R^{m-1} M_u`. -/
private theorem step3_S_zero (hK : KboundConcl κ) (h : Step3Ctx d κ c E s t)
    (hL1 : Step1LoopPT d E s t) {m : ℕ} (hm : 1 ≤ m) :
    step3S (Sizes.seqP d) d.size (step3X d E s t) (step3As d E s) (step3R d E s t)
      (step3A d E s t) m 0 := by
  have hsize := h.tendsto
  have sc := step3_scales h
  have hY := step3_xiL_step1 h hL1 hm
  have hKd := step3_Kd_pt hK h hm
  have hadd := perTimeCalc_add hsize hY hKd
  have hρ0 : ∀ n (u : TimeIcc s t n) (_ : Sizes.SeqΩ d),
      0 ≤ (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (m - 1)) + 1 := fun n u _ =>
    add_nonneg (pow_nonneg (div_nonneg (step3_ellT_nonneg _ _) (step3_ellT_nonneg _ _)) _)
      zero_le_one
  have hmul := step3_mul_det hsize hρ0
    (c := fun n (u : TimeIcc s t n) => scaleM (d.L n) (d.W n) (E n) u)
    (fun n u => (h.A_pos n u).le) hadd
  have hle := stochDom_of_le_left_eventually (Eventually.of_forall fun n u ω => by
    exact step3_xiLK_le_pt (E n) u (Sizes.seqHflow d n u ω) (h.A_pos n u) hm) hmul
  refine perTimeCalc_mono hsize (fun n u _ => step3_psi_nonneg (h.As_pos n).le
    (sq_nonneg _) (h.A_pos n u).le) 2 ?_ hle
  filter_upwards [sc.one_le_R] with n hR u ω
  show _ ≤ 2 * step3_psi _ _ _ m 0
  rw [step3_psi_zero]
  have hρ := step3_rho_le (step3_one_le_L d n) (h.hs0 n) u.2.1 u.2.2 (h.ht1 n) m
  have hR1 : 1 ≤ ((ellT (d.L n) (t n) / ellT (d.L n) (s n)) ^ 2) ^ (m - 1) :=
    one_le_pow₀ hR
  have hMu := h.A_pos n u
  have hs2 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (s n)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (h.As_pos n).le _
  change (_ + 1) * _ ≤ 2 * (_ + _ * _)
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add hρ hR1) hMu.le]

/-- **The one-loop base case** (`m = 1`): `Ξ^{(𝓛-𝒦)}_{u,1} ≺ M_s^{1/2}` from `Step2LocalPT`
(`‖G_u - m‖_max ≺ M_u^{-1/2}`). -/
private theorem step3_xiLK_one (h : Step3Ctx d κ c E s t) (hL2 : Step2LocalPT d E s t) :
    PT d s t (step3X d E s t 1)
      (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)) := by
  have hsize := h.tendsto
  have sc := step3_scales h
  have h1 := step3_label_max (P := Sizes.seqP d) (size := d.size)
    (U := fun n => TimeIcc s t n) (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (C := ((2 : ℕ) : ℝ)) (Nat.cast_nonneg _) (Eventually.of_forall (step3_card_idx d))
    (ξ := fun n u v ω => llErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2)
    (ζ := fun n u _ => (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ ((1 : ℝ) / 2)) hL2
  have hζ : ∀ n (u : TimeIcc s t n) (_ : Sizes.SeqΩ d),
      0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ ((1 : ℝ) / 2) := fun n u _ =>
    Real.rpow_nonneg (inv_nonneg.2 (h.A_pos n u).le) _
  have h2 := step3_mul_det hsize hζ
    (c := fun n (u : TimeIcc s t n) => scaleM (d.L n) (d.W n) (E n) u)
    (fun n u => (h.A_pos n u).le) h1
  have hpt : ∀ n (u : TimeIcc s t n) (ω : Sizes.SeqΩ d),
      xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 1 ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun v : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) =>
            llErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2) *
          scaleM (d.L n) (d.W n) (E n) u := fun n u ω => by
    unfold xiLK
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (Finset.sup'_le _ _ fun p _ =>
      step3_lkGen_one_le (E n) u _ (Sizes.seqHflow_isHermitian d n u ω) p.1 p.2)
      (h.A_pos n u).le
  have h3 := stochDom_of_le_left_eventually (Eventually.of_forall hpt) h2
  refine perTimeCalc_mono hsize (fun n _ _ => Real.rpow_nonneg (h.As_pos n).le _) 1 ?_ h3
  filter_upwards [sc.A_le_As] with n hle u ω
  show _ * _ ≤ 1 * _
  rw [one_mul, step3_inv_sqrt_mul (h.A_pos n u)]
  exact Real.rpow_le_rpow (h.A_pos n u).le (hle u) (by norm_num)

/-- **The `(+,-)` part of the two-loop**: `max_{a,b}|(𝓛-𝒦)_{u,(+,-),(a,b)}| M_u² ≺ M_s^{1/2}`
from `Step2DecayPT` at `D = 3/c`. -/
private theorem step3_pm_two (h : Step3Ctx d κ c E s t) (hD : Step2DecayPT d E s t) :
    PT d s t (fun n u ω => Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 (d.L n) × Z2 (d.L n) =>
          lkErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) p.1 p.2) *
        scaleM (d.L n) (d.W n) (E n) u ^ 2)
      (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)) := by
  have hsize := h.tendsto
  have hc := h.hc
  have hD' : (0 : ℝ) < 3 / c := by positivity
  have h1 := hD (3 / c) hD'
  have h2 := mono_right_eventually
    (ζ' := fun n (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) (_ : Sizes.SeqΩ d) =>
      (etaT (E n) (s n) / etaT (E n) p.1) ^ 4 * (scaleM (d.L n) (d.W n) (E n) p.1 ^ 2)⁻¹ +
        (d.W n : ℝ) ^ (-(3 / c))) h1
    (Eventually.of_forall fun n p ω => by
      show _ * _ * Real.exp _ + _ ≤ _ * _ + _
      have hnn : 0 ≤ (etaT (E n) (s n) / etaT (E n) p.1) ^ 4 *
          (scaleM (d.L n) (d.W n) (E n) p.1 ^ 2)⁻¹ := by
        have := (h.A_pos n p.1)
        positivity
      have hexp : Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) /
          ellT (d.L n) p.1)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_left hexp hnn])
  have h3 := step3_label_max (P := Sizes.seqP d) (size := d.size)
    (U := fun n => TimeIcc s t n) (V := fun n => Z2 (d.L n) × Z2 (d.L n))
    (C := ((2 : ℕ) : ℝ)) (Nat.cast_nonneg _) (Eventually.of_forall (step3_card_pairs d))
    (ξ := fun n u v ω => lkErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2)
    (ζ := fun n u _ => (etaT (E n) (s n) / etaT (E n) u) ^ 4 *
        (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ + (d.W n : ℝ) ^ (-(3 / c))) h2
  have hζ : ∀ n (u : TimeIcc s t n) (_ : Sizes.SeqΩ d),
      0 ≤ (etaT (E n) (s n) / etaT (E n) u) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ +
        (d.W n : ℝ) ^ (-(3 / c)) := fun n u _ => by
    have := h.A_pos n u
    have hW : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
    positivity
  have h4 := step3_mul_det hsize hζ
    (c := fun n (u : TimeIcc s t n) => scaleM (d.L n) (d.W n) (E n) u ^ 2)
    (fun n u => sq_nonneg _) h3
  refine perTimeCalc_mono hsize (fun n _ _ => Real.rpow_nonneg (h.As_pos n).le _) 2 ?_ h4
  filter_upwards [h.hband, h.hcond] with n hband hcond u ω
  obtain ⟨hM1, hρ30⟩ := step3_cond_pt (h.As_pos n) (h.hst n) (h.ht1 n) hcond
  have hMu := h.A_pos n u
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have hMN : scaleM (d.L n) (d.W n) (E n) u ≤ ((d.size n : ℕ) : ℝ) := by
    have := step3_scaleM_le (E := E n) (W := d.W n) (step3_one_le_L d n) (h.u0 n u) (h.u1 n u)
    simpa [Sizes.size] using this
  change _ ≤ 2 * _
  exact step3_thr_le hMu hM1 (step3_eta4_le (h.E2 n) u.2.1 u.2.2 (h.ht1 n) hM1 hρ30)
    (step3_Wneg_le hc rfl (step3_one_le_size d n) hW0 hband hMu.le hMN)

/-- **The two-loop base case** (`m = 2`): `Ξ^{(𝓛-𝒦)}_{u,2} ≺ M_s^{1/2}`, over the four charges:
`(+,+)` is the hypothesis `PPTwoLoopPT`, `(+,-)` is `step3_pm_two`,
`(-,+)` is its rotation and `(-,-)` the conjugate of `(+,+)`. -/
private theorem step3_xiLK_two (h : Step3Ctx d κ c E s t) (hD : Step2DecayPT d E s t)
    (hPP : PPTwoLoopPT d E s t) :
    PT d s t (step3X d E s t 2)
      (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)) := by
  have hsize := h.tendsto
  refine stochDom_of_forall_or hsize hPP (step3_pm_two h hD) ?_
  intro n u ω
  have hM2 : 0 ≤ scaleM (d.L n) (d.W n) (E n) u ^ 2 := sq_nonneg _
  have hle : xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 2 ≤
      max (Finset.univ.sup' Finset.univ_nonempty
          (fun p : Z2 (d.L n) × Z2 (d.L n) => lkGen (d.L n) (d.W n) (E n) u
            (Sizes.seqHflow d n u ω) ![true, true] ![p.1, p.2]) *
          scaleM (d.L n) (d.W n) (E n) u ^ 2)
        (Finset.univ.sup' Finset.univ_nonempty
          (fun p : Z2 (d.L n) × Z2 (d.L n) => lkErrMat (d.L n) (d.W n) (E n) u
            (Sizes.seqHflow d n u ω) p.1 p.2) * scaleM (d.L n) (d.W n) (E n) u ^ 2) := by
    unfold xiLK
    rw [← max_mul_of_nonneg _ _ hM2]
    exact mul_le_mul_of_nonneg_right (Finset.sup'_le _ _ fun p _ =>
      step3_lkGen_two_le (d.three_le_L n) (step3_one_le_W d n) (h.E2 n) ⟨h.u0 n u, h.u1 n u⟩
        _ (Sizes.seqHflow_isHermitian d n u ω) p.1 p.2) hM2
  rcases le_max_iff.1 hle with h1 | h1
  · exact Or.inl ⟨h1, le_rfl⟩
  · exact Or.inr ⟨h1, le_rfl⟩

/-- `S(m,l)` for `m ≤ 2` from `Ξ^{(𝓛-𝒦)}_{u,m} ≺ M_s^{1/2}`: `Ψ(m,l) ≥ M_s^{1/2}`. -/
private theorem step3_S_low (h : Step3Ctx d κ c E s t)
    (hm12 : ∀ m, 1 ≤ m → m ≤ 2 → PT d s t (step3X d E s t m)
      (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)))
    (m l : ℕ) (hm : 1 ≤ m) (hm2 : m ≤ 2) :
    step3S (Sizes.seqP d) d.size (step3X d E s t) (step3As d E s) (step3R d E s t)
      (step3A d E s t) m l := by
  refine perTimeCalc_mono h.tendsto (fun n u _ => step3_psi_nonneg (h.As_pos n).le
    (sq_nonneg _) (h.A_pos n u).le) 1 (Eventually.of_forall fun n u ω => ?_) (hm12 m hm hm2)
  show _ ≤ 1 * step3_psi _ _ _ m l
  rw [one_mul]
  exact step3_psi_ge (h.As_pos n).le (sq_nonneg _) (h.A_pos n u).le m l

end BaseCases

/-! ## 12. The bundle `Step3Hyp` and the theorem -/

section Assembly

open PerTimeCalc.PerTime

variable {d : Sizes} {κ c : ℝ} {E s t : ℕ → ℝ}

/-- The inputs of the abstract Step 3, with (5.107) from
`KboundConcl`, (5.118) from `loopXi_le`, the scales from `step3_scales`, and Lemma 5.14 from
`STOeqPT`. -/
private theorem step3_hyp (hK : KboundConcl κ) (h : Step3Ctx d κ c E s t)
    (hSTO : ∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k) :
    Step3Hyp (U := fun n => TimeIcc s t n) (Sizes.seqP d) d.size (step3X d E s t)
      (step3Y d E s t) (step3As d E s) (step3R d E s t) (step3A d E s t) where
  hsize := h.tendsto
  scales := step3_scales h
  X_nonneg := fun k n u ω => step3_xiLK_nonneg (h.A_pos n u).le _ k
  Y_nonneg := fun k n u ω => step3_xiL_nonneg (h.A_pos n u).le _ k
  xiL_le := fun k hk => step3_xiL_le hK h (by omega)
  xiL_split := fun n l₁ l₂ h₁ h₂ hl N u ω =>
    step3_xiL_split (E N) u _ (Sizes.seqHflow_isHermitian d N u ω) (h.A_pos N u).le h₁ h₂ hl
  lemma514 := fun n hn => hSTO n (by omega)

/-- From `Ξ^{(𝓛)}_{u,k} ≺ 1` to `max|𝓛_{u,σ,a}| ≺ M_u^{-k+1}` (`Step3PT`). -/
private theorem step3_final (h : Step3Ctx d κ c E s t) {k : ℕ}
    (hY : PT d s t (step3Y d E s t k) (fun _ _ _ => 1)) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1)) := by
  have hpb := step3_pullback (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n))) hY
  refine perTimeCalc_of_imp hpb ?_
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun n p ω hp => ?_⟩
  have hMu := h.A_pos n p.1
  have hle : loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun q : (Fin k → Bool) × (Fin k → Z2 (d.L n)) =>
          loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) q.1 q.2) :=
    Finset.le_sup' (fun q : (Fin k → Bool) × (Fin k → Z2 (d.L n)) =>
      loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) q.1 q.2) (Finset.mem_univ _)
  have hp' : ((d.size n : ℕ) : ℝ) ^ τ * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1) <
      loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 := hp
  have h1 := mul_lt_mul_of_pos_right (lt_of_lt_of_le hp' hle) (pow_pos hMu (k - 1))
  change ((d.size n : ℕ) : ℝ) ^ τ * 1 < _
  calc ((d.size n : ℕ) : ℝ) ^ τ * 1
      = ((d.size n : ℕ) : ℝ) ^ τ * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1) *
          scaleM (d.L n) (d.W n) (E n) p.1 ^ (k - 1) := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hMu.ne', one_pow]
    _ < _ := h1

end Assembly

/-- **Step 3** of `lem:main_ind`: the deterministic `≺`-calculus that gives
(`Eq:LGxb`) from the random layer `STOeqPT`, the `(+,+)` base case `PPTwoLoopPT`, Steps 1–2 per
time, and the `𝒦` bound.  The double induction is that of the one-dimensional formalization
with `R = (ℓ_t/ℓ_s)²`. -/
theorem step3 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step3Target d κ c τ E s t := by
  intro hK hmain hL1 _hweak hL2 hD hPP hSTO
  have h := step3_ctx_of hmain
  have hyp := step3_hyp hK h hSTO
  have h0 : ∀ m, 1 ≤ m → step3S (Sizes.seqP d) d.size (step3X d E s t) (step3As d E s)
      (step3R d E s t) (step3A d E s t) m 0 := fun m hm => step3_S_zero hK h hL1 hm
  have hm12 : ∀ m, 1 ≤ m → m ≤ 2 → PT d s t (step3X d E s t m)
      (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)) := by
    intro m hm hm2
    rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
    · exact step3_xiLK_one h hL2
    · exact step3_xiLK_two h hD hPP
  have h12 : ∀ m l, 1 ≤ m → m ≤ 2 → step3S (Sizes.seqP d) d.size (step3X d E s t)
      (step3As d E s) (step3R d E s t) (step3A d E s t) m l :=
    fun m l hm hm2 => step3_S_low h hm12 m l hm hm2
  intro k hk
  exact step3_final h (step3_xiL_le_one_of hyp h0 h12 hk (step3_xiL_le hK h hk))


end RBM.Ind

end
