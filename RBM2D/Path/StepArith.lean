/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# The exponent arithmetic of the Step 2 closing argument

Real-number inequalities only (Mathlib `Real.rpow`, `Real.sqrt`):

* `StepEExponentsD`: from `1 ≤ rv ≤ r`, `1 ≤ Mt ≤ Mv`, `r^29 ≤ Mt`, the four absolute exponents
  `-21/29`, `-11/58`, `-5/58`, `-17/58`;
* `ThrImproveD`: `J ≤ C N^ε (1 + r^3) + 2` and `4C < N^{δ-ε}` give `J < N^δ r⁴`.
-/

namespace RBM.Path

/-- **The absolute exponents**: from `r^{29} ≤ M_t ≤ M_v`, `1 ≤ r_v ≤ r`, the four terms
(drift `LK×LK`, far drift, and the two martingale terms) have exponents `-21/29`, `-11/58`,
`-5/58`, `-17/58`. -/
def StepEExponentsD : Prop :=
  ∀ r rv Mv Mt : ℝ, 1 ≤ rv → rv ≤ r → 1 ≤ Mt → Mt ≤ Mv → r ^ 29 ≤ Mt →
    rv ^ 8 * Mv⁻¹ ≤ Mt ^ (-(21 : ℝ) / 29) ∧
    rv ^ 9 * Mv ^ (-(1 : ℝ) / 2) ≤ Mt ^ (-(11 : ℝ) / 58) ∧
    Real.sqrt (rv ^ ((19 : ℝ) / 2) * Mv ^ (-(1 : ℝ) / 2)) ≤ Mt ^ (-(5 : ℝ) / 58) ∧
    Real.sqrt (rv ^ 12 * Mv⁻¹) ≤ Mt ^ (-(17 : ℝ) / 58)

/-- **Threshold improvement**: if `J ≤ C N^ε (1 + r^3) + 2` and
`4C < N^{δ-ε}` then `J < N^δ r⁴ = Θ(u)`. -/
def ThrImproveD : Prop :=
  ∀ N r C ε δ J : ℝ, 1 ≤ N → 1 ≤ r → 1 ≤ C → 0 ≤ ε → 4 * C < N ^ (δ - ε) →
    J ≤ C * N ^ ε * (1 + r ^ 3) + 2 → J < N ^ δ * r ^ 4

/-- `r_v ≤ M_t^{1/29}` from `r_v ≤ r`, `r^29 ≤ M_t`. -/
private theorem stepArith_rv_le {r rv Mt : ℝ} (hrv1 : 1 ≤ rv) (hrv : rv ≤ r)
    (hMt : r ^ 29 ≤ Mt) : rv ≤ Mt ^ ((1 : ℝ) / 29) := by
  have hr0 : 0 ≤ r := by linarith
  have h1 : (r ^ 29) ^ ((29 : ℕ)⁻¹ : ℝ) = r := Real.pow_rpow_inv_natCast hr0 (by norm_num)
  have h2 : (r ^ 29) ^ ((29 : ℕ)⁻¹ : ℝ) ≤ Mt ^ ((29 : ℕ)⁻¹ : ℝ) :=
    Real.rpow_le_rpow (by positivity) hMt (by positivity)
  have h3 : ((29 : ℕ)⁻¹ : ℝ) = (1 : ℝ) / 29 := by norm_num
  rw [h1, h3] at h2
  exact hrv.trans h2

/-- Core estimate: `rv^a Mv^{-b} ≤ Mt^{a/29 - b}` for `a, b ≥ 0`. -/
private theorem stepArith_core {r rv Mv Mt : ℝ} (hrv1 : 1 ≤ rv) (hrv : rv ≤ r) (hMt1 : 1 ≤ Mt)
    (hMv : Mt ≤ Mv) (hr : r ^ 29 ≤ Mt) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rv ^ a * Mv ^ (-b) ≤ Mt ^ (a / 29 - b) := by
  have hMt0 : 0 < Mt := by linarith
  have hrv0 : 0 ≤ rv := by linarith
  have h1 : rv ^ a ≤ Mt ^ (a / 29) := by
    calc rv ^ a ≤ (Mt ^ ((1 : ℝ) / 29)) ^ a :=
          Real.rpow_le_rpow hrv0 (stepArith_rv_le hrv1 hrv hr) ha
      _ = Mt ^ (a / 29) := by
          rw [← Real.rpow_mul hMt0.le]; congr 1; ring
  have h2 : Mv ^ (-b) ≤ Mt ^ (-b) := Real.rpow_le_rpow_of_nonpos hMt0 hMv (by linarith)
  calc rv ^ a * Mv ^ (-b) ≤ Mt ^ (a / 29) * Mt ^ (-b) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hMt0.le _)
    _ = Mt ^ (a / 29 - b) := by
        rw [← Real.rpow_add hMt0]; congr 1

/-- `√X ≤ Mt^p` from `X ≤ Mt^{2p}`. -/
private theorem stepArith_sqrt {X Mt p : ℝ} (hMt : 0 < Mt) (h : X ≤ Mt ^ (2 * p)) :
    Real.sqrt X ≤ Mt ^ p := by
  rw [Real.sqrt_le_left (Real.rpow_nonneg hMt.le _)]
  have : (Mt ^ p) ^ 2 = Mt ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMt.le]; congr 1; push_cast; ring
  rw [this]; exact h

/-- **`stepEExponentsD`**: the four absolute exponents. -/
theorem stepEExponentsD : StepEExponentsD := by
  intro r rv Mv Mt hrv1 hrv hMt1 hMv hr
  have hMt0 : 0 < Mt := by linarith
  have core := fun {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) =>
    stepArith_core hrv1 hrv hMt1 hMv hr ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := core (a := 8) (b := 1) (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    convert this using 2; norm_num
  · have := core (a := 9) (b := 1 / 2) (by norm_num) (by norm_num)
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    convert this using 2 <;> norm_num
  · apply stepArith_sqrt hMt0
    have := core (a := 19 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    convert this using 2 <;> norm_num
  · apply stepArith_sqrt hMt0
    have := core (a := 12) (b := 1) (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    convert this using 2; norm_num

/-- **`thrImproveD`**: the threshold improvement. -/
theorem thrImproveD : ThrImproveD := by
  intro N r C ε δ J hN hr hC hε h4 hJ
  have hN0 : 0 < N := by linarith
  have hP : 1 ≤ N ^ ε := Real.one_le_rpow hN hε
  have hQ : 1 ≤ r ^ 4 := one_le_pow₀ hr
  have hr3 : r ^ 3 ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have hNδ : N ^ δ = N ^ (δ - ε) * N ^ ε := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  set P := N ^ ε with hPdef
  set Q := r ^ 4 with hQdef
  have hCP : 1 ≤ C * P := by nlinarith
  have hCPQ : 1 ≤ C * P * Q := by nlinarith
  have hCP0 : 0 ≤ C * P := by linarith
  have h5 : C * P * (1 + r ^ 3) ≤ C * P * (2 * Q) :=
    mul_le_mul_of_nonneg_left (by linarith) hCP0
  have h6 : J ≤ 4 * C * P * Q := by nlinarith
  have h7 : 4 * C * P < N ^ δ := by
    rw [hNδ]; exact mul_lt_mul_of_pos_right h4 (by linarith)
  have h8 : 4 * C * P * Q < N ^ δ * Q := mul_lt_mul_of_pos_right h7 (by linarith)
  linarith

end RBM.Path
