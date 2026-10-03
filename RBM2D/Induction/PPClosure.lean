/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.PPVocab

/-!
# The `(+,+)` two-loop base case: the drift sum, the Azuma sum and the arithmetic inequalities

Proofs of the three deterministic statements `PPDriftSumN`, `PPQVSumN`, `PPArithN` of
`RBM2D.Induction.PPVocab`.  Namespace `RBM.Ind`.  The argument parallels the one-dimensional
formalization (the drift sum, the Azuma sum, the forbidden zone), recounted for `d = 2` with the
constants of `PPVocab`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Elementary facts on `N`, `Im m`, `Lg` -/

section Basic

private theorem ppc_nPPN_eq (L W : ℕ) : nPPN L W = ((W : ℝ) * L) ^ 2 := by
  unfold nPPN; push_cast; ring

private theorem ppc_one_le_N {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) : (1 : ℝ) ≤ nPPN L W := by
  rw [ppc_nPPN_eq]
  have h1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h2 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : (1 : ℝ) ≤ (W : ℝ) * L := one_le_mul_of_one_le_of_one_le h1 h2
  exact one_le_pow₀ this

private theorem ppc_W2_le_N {L W : ℕ} (hL : 1 ≤ L) : (W : ℝ) ^ 2 ≤ nPPN L W := by
  rw [ppc_nPPN_eq, mul_pow]
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hL)
  have h3 : 0 ≤ (W : ℝ) ^ 2 := sq_nonneg _
  nlinarith

private theorem ppc_L_le_N {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) : (L : ℝ) ≤ nPPN L W := by
  rw [ppc_nPPN_eq, mul_pow]
  have h1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)
  have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  nlinarith

private theorem ppc_nine_le_N {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) : (9 : ℝ) ≤ nPPN L W := by
  rw [ppc_nPPN_eq, mul_pow]
  have h1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)
  have h2 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  nlinarith

private theorem ppc_one_le_log {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) :
    (1 : ℝ) ≤ Real.log (nPPN L W) := by
  have h9 := ppc_nine_le_N hL hW
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

private theorem ppc_im_le_one (E : ℝ) : (spectralM E).im ≤ 1 := MLExpVocab_im_le_one E

private theorem ppc_Lg_ge_one {E : ℝ} {N : ℝ} (hE : |E| < 2) (hN : 1 ≤ N) : 1 ≤ LgPPN E N := by
  unfold LgPPN
  have h1 : 0 ≤ Real.log N := Real.log_nonneg hN
  have h2 : 0 ≤ (spectralM E).im⁻¹ := inv_nonneg.2 (spectralM_im_pos hE).le
  nlinarith [mul_nonneg h2 h1]

/-- `A (1 + log x)^p ≤ x^δ` eventually (polylogarithm against a power). -/
private theorem ppc_polylog_le (A δ : ℝ) (p : ℕ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, A * (1 + Real.log x) ^ p ≤ x ^ δ := by
  have hlo := isLittleO_log_rpow_rpow_atTop (p : ℝ) hδ
  have hc : (0 : ℝ) < 1 / (|A| * 2 ^ p + 1) := by positivity
  filter_upwards [hlo.def hc, eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hxδ : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg hxδ, Real.rpow_natCast] at hx
  have h1 : (1 + Real.log x) ^ p ≤ 2 ^ p * Real.log x ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) p
  have h2 : A * (1 + Real.log x) ^ p ≤ |A| * (2 ^ p * Real.log x ^ p) := by
    calc A * (1 + Real.log x) ^ p ≤ |A| * (1 + Real.log x) ^ p :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
      _ ≤ |A| * (2 ^ p * Real.log x ^ p) := mul_le_mul_of_nonneg_left h1 (abs_nonneg A)
  have h3 : |A| * (2 ^ p * Real.log x ^ p) ≤ x ^ δ := by
    have h4 : |A| * 2 ^ p * Real.log x ^ p ≤ |A| * 2 ^ p * (1 / (|A| * 2 ^ p + 1) * x ^ δ) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have h5 : |A| * 2 ^ p * (1 / (|A| * 2 ^ p + 1) * x ^ δ) ≤ x ^ δ := by
      have hq : |A| * 2 ^ p / (|A| * 2 ^ p + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      calc |A| * 2 ^ p * (1 / (|A| * 2 ^ p + 1) * x ^ δ)
          = (|A| * 2 ^ p / (|A| * 2 ^ p + 1)) * x ^ δ := by ring
        _ ≤ 1 * x ^ δ := mul_le_mul_of_nonneg_right hq hxδ
        _ = x ^ δ := one_mul _
    calc |A| * (2 ^ p * Real.log x ^ p) = |A| * 2 ^ p * Real.log x ^ p := by ring
      _ ≤ _ := h4
      _ ≤ x ^ δ := h5
  exact h2.trans h3

end Basic

/-! ## 2. The drift sum -/

section Drift

/-- One term of the drift sum, multiplied by `M_k²`: `M_k ≤ M_j`, `M_v ≤ M_k` for
`u_j ≤ u_k ≤ v` (`scaleM_anti_ratio`), so `M_k² M_j^{-3} ≤ M_v^{-1}` and `M_k² M_j^{-2} ≤ 1`. -/
private theorem ppc_drift_term {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E ε D' : ℝ} (hE : |E| < 2)
    {uj uk v : ℝ} (hjk : uj ≤ uk) (hkv : uk ≤ v) (hv1 : v < 1)
    {Γ Φ J m : ℝ} (hJ0 : 0 ≤ J) (hJm : J ≤ m) (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) :
    scaleM L W E uk ^ 2 * dBoundPPN L W E uj Γ Φ ε D' J ≤
      1000 * ((W : ℝ) ^ (2 * ε) * m ^ 2 * (scaleM L W E v)⁻¹ * (etaT E uj)⁻¹ +
        (W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * (etaT E uj)⁻¹ +
        scaleM L W E uk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (m + Γ))) := by
  have hkj1 : uk < 1 := hkv.trans_lt hv1
  have hj1 : uj < 1 := hjk.trans_lt hkj1
  have hMk_j : scaleM L W E uk ≤ scaleM L W E uj := (scaleM_anti_ratio hL hE hjk hkj1).1
  have hMv_k : scaleM L W E v ≤ scaleM L W E uk := (scaleM_anti_ratio hL hE hkv hv1).1
  have hMv : 0 < scaleM L W E v := scaleM_pos hL hW hE hv1
  have hMk : 0 < scaleM L W E uk := scaleM_pos hL hW hE hkj1
  have hMj : 0 < scaleM L W E uj := scaleM_pos hL hW hE hj1
  have hη : 0 < etaT E uj := etaT_pos hE hj1
  set Mv := scaleM L W E v
  set Mk := scaleM L W E uk
  set Mj := scaleM L W E uj
  set η := etaT E uj
  have hw : 0 ≤ (W : ℝ) ^ (2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  have hn2 : 0 ≤ nPPN L W ^ 2 * (W : ℝ) ^ (-D') :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg W) _)
  have h1 : Mk ^ 2 * Mj⁻¹ ^ 3 ≤ Mv⁻¹ := by
    calc Mk ^ 2 * Mj⁻¹ ^ 3 ≤ Mj ^ 2 * Mj⁻¹ ^ 3 := by gcongr
      _ = Mj⁻¹ := by field_simp
      _ ≤ Mv⁻¹ := inv_anti₀ hMv (hMv_k.trans hMk_j)
  have h2 : Mk ^ 2 * Mj⁻¹ ^ 2 ≤ 1 := by
    calc Mk ^ 2 * Mj⁻¹ ^ 2 ≤ Mj ^ 2 * Mj⁻¹ ^ 2 := by gcongr
      _ = 1 := by field_simp
  unfold dBoundPPN
  have hJ2 : J ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hJ0 hJm 2
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have t1 : Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * J ^ 2 * Mj⁻¹ ^ 3 * η⁻¹) ≤
      (W : ℝ) ^ (2 * ε) * m ^ 2 * Mv⁻¹ * η⁻¹ := by
    have e : Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * J ^ 2 * Mj⁻¹ ^ 3 * η⁻¹) =
        ((W : ℝ) ^ (2 * ε) * η⁻¹ * J ^ 2) * (Mk ^ 2 * Mj⁻¹ ^ 3) := by ring
    rw [e]
    calc ((W : ℝ) ^ (2 * ε) * η⁻¹ * J ^ 2) * (Mk ^ 2 * Mj⁻¹ ^ 3)
        ≤ ((W : ℝ) ^ (2 * ε) * η⁻¹ * m ^ 2) * Mv⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hJ2 (mul_nonneg hw hηi)) h1 (by positivity)
            (by positivity)
      _ = _ := by ring
  have t2 : Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * Mj⁻¹ ^ 2 * η⁻¹) ≤
      (W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * η⁻¹ := by
    have e : Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * Mj⁻¹ ^ 2 * η⁻¹) =
        ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * η⁻¹) * (Mk ^ 2 * Mj⁻¹ ^ 2) := by ring
    rw [e]
    calc ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * η⁻¹) * (Mk ^ 2 * Mj⁻¹ ^ 2)
        ≤ ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * η⁻¹) * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := mul_one _
  have t3 : Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (J + Γ)) ≤
      Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (m + Γ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hn2) (sq_nonneg _)
  calc Mk ^ 2 * (1000 * ((W : ℝ) ^ (2 * ε) * J ^ 2 * Mj⁻¹ ^ 3 * η⁻¹ +
        (W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * Mj⁻¹ ^ 2 * η⁻¹ +
        nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (J + Γ)))
      = 1000 * (Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * J ^ 2 * Mj⁻¹ ^ 3 * η⁻¹) +
        Mk ^ 2 * ((W : ℝ) ^ (2 * ε) * Γ ^ 2 * Φ * Mj⁻¹ ^ 2 * η⁻¹) +
        Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (J + Γ))) := by ring
    _ ≤ _ := by linarith

/-- The algebra of the drift sum: with `f = N^{-2}` (`f M_v ≤ 1`) and `F_k ≤ f` the far factor,
`CU² (1000 (w m² M_v⁻¹ + w Γ² R⁴) Lg + 1000 F_k (m + Γ)) ≤ c'/4 + C_q m² Lg / M_v`
(`w = W^{2ε} ≤ Γ`, `C_q = 2000 CU² w`, `c' = 10⁴ (CU² + 1) Γ³ (1 + R⁴ + R⁵) Lg`). -/
private theorem ppc_drift_alg {CU2 w Γ R Lg Mv m f Fk : ℝ} (hCU : 0 ≤ CU2) (hw1 : 1 ≤ w)
    (hwΓ : w ≤ Γ) (hR : 0 ≤ R) (hLg : 1 ≤ Lg) (hMv : 0 < Mv) (hm : 0 ≤ m) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) (hfM : f * Mv ≤ 1) (hFk0 : 0 ≤ Fk) (hFk : Fk ≤ f) :
    CU2 * ((1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) * Lg + 1000 * (Fk * (m + Γ))) ≤
      10000 * (CU2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg / 4 +
        2000 * CU2 * w * m ^ 2 * Lg / Mv := by
  have hΓ1 : 1 ≤ Γ := hw1.trans hwΓ
  have hΓ0 : 0 ≤ Γ := by linarith
  set X := m ^ 2 * Lg / Mv with hXdef
  have hX : 0 ≤ X := by positivity
  have hfle : f ≤ 2 * w * Lg / Mv := by
    rw [le_div_iff₀ hMv]; nlinarith
  have hfm2 : f * m ^ 2 ≤ 2 * w * X := by
    calc f * m ^ 2 ≤ (2 * w * Lg / Mv) * m ^ 2 := mul_le_mul_of_nonneg_right hfle (sq_nonneg m)
      _ = 2 * w * X := by rw [hXdef]; ring
  have hfm : Fk * m ≤ (f + f * m ^ 2) / 2 := by
    have h1 : Fk * m ≤ f * m := mul_le_mul_of_nonneg_right hFk hm
    nlinarith [mul_nonneg hf0 (sq_nonneg (m - 1))]
  set Z := Γ ^ 3 * Lg with hZdef
  have hZ : 0 ≤ Z := by positivity
  have hZ1 : 1 ≤ Z := by
    have : 1 ≤ Γ ^ 3 := one_le_pow₀ hΓ1
    nlinarith
  have hΓZ : Γ ≤ Z := by
    have : Γ ≤ Γ ^ 3 := by nlinarith [sq_nonneg Γ]
    nlinarith
  have hwΓ2 : w * Γ ^ 2 ≤ Γ ^ 3 := by nlinarith [sq_nonneg Γ]
  have e1 : CU2 * ((1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) * Lg + 1000 * (Fk * (m + Γ))) =
      1000 * CU2 * w * X + 1000 * R ^ 4 * (CU2 * (w * Γ ^ 2) * Lg) + 1000 * CU2 * (Fk * m) +
        1000 * CU2 * (Fk * Γ) := by
    rw [hXdef]; field_simp; ring
  have h_a : CU2 * (w * Γ ^ 2) * Lg ≤ CU2 * Z := by
    rw [hZdef]
    have := mul_le_mul_of_nonneg_left hwΓ2 hCU
    nlinarith
  have h_c : Fk * Γ ≤ Z := by
    have : Fk * Γ ≤ 1 * Γ := mul_le_mul_of_nonneg_right (hFk.trans hf1) hΓ0
    linarith
  have h_b : CU2 * (Fk * m) ≤ CU2 * ((f + f * m ^ 2) / 2) := mul_le_mul_of_nonneg_left hfm hCU
  have h_f : CU2 * (f + f * m ^ 2) ≤ CU2 * (Z + 2 * w * X) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hCU
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hR5 : 0 ≤ R ^ 5 := by positivity
  have e2 : 10000 * (CU2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg / 4 =
      2500 * (CU2 * Z) * (1 + R ^ 4 + R ^ 5) + 2500 * Z * (1 + R ^ 4 + R ^ 5) := by
    rw [hZdef]; ring
  have hCZ : 0 ≤ CU2 * Z := by positivity
  have h_r1 : 0 ≤ (CU2 * Z) * R ^ 5 := by positivity
  have h_r2 : 0 ≤ Z * (1 + R ^ 4 + R ^ 5) := by positivity
  have h_r3 : 0 ≤ CU2 * (2 * w * X) := by positivity
  have hRZ : 1000 * R ^ 4 * (CU2 * (w * Γ ^ 2) * Lg) ≤ 1000 * R ^ 4 * (CU2 * Z) :=
    mul_le_mul_of_nonneg_left h_a (by positivity)
  have hC : 1000 * CU2 * (Fk * Γ) ≤ 1000 * CU2 * Z :=
    mul_le_mul_of_nonneg_left h_c (by positivity)
  rw [e1, e2]
  have e3 : 2000 * CU2 * w * m ^ 2 * Lg / Mv = 2000 * CU2 * w * X := by rw [hXdef]; ring
  rw [e3]
  nlinarith [mul_nonneg hCZ hR4, h_r1, h_r2, h_r3, h_b, h_f, hRZ, hC]

private theorem ppc_scaleM_le_N {L W : ℕ} (hL : 1 ≤ L) {E u : ℝ} (hu : u < 1) :
    scaleM L W E u ≤ nPPN L W :=
  (MLExpVocab_scaleM_le_W2 hL hu).trans (ppc_W2_le_N hL)

/-- The far factor: `M_u² N² W^{-6/c} ≤ N^{-2}` from `W ≥ N^c` and `M_u ≤ W² ≤ N`. -/
private theorem ppc_far {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E c : ℝ} (hE : |E| < 2)
    (hc : 0 < c) (hbw : (nPPN L W) ^ c ≤ (W : ℝ)) {u : ℝ} (hu1 : u < 1) :
    scaleM L W E u ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))) ≤ ((nPPN L W) ^ 2)⁻¹ := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hN0 : 0 < nPPN L W := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hMk0 : 0 < scaleM L W E u := scaleM_pos hL1 hW hE hu1
  have hMkN : scaleM L W E u ≤ nPPN L W := ppc_scaleM_le_N hL1 hu1
  have h6c : 0 < 6 / c := by positivity
  have hWneg : (W : ℝ) ^ (-(6 / c)) ≤ (nPPN L W) ^ (-(6 : ℝ)) := by
    have h1 : 0 < (nPPN L W) ^ c := Real.rpow_pos_of_pos hN0 c
    have h2 := Real.rpow_le_rpow_of_nonpos h1 hbw (show -(6 / c) ≤ 0 by linarith)
    calc (W : ℝ) ^ (-(6 / c)) ≤ ((nPPN L W) ^ c) ^ (-(6 / c)) := h2
      _ = (nPPN L W) ^ (-(6 : ℝ)) := by
        rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  have hN6 : (nPPN L W) ^ (-(6 : ℝ)) = ((nPPN L W) ^ 6)⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    congr 1
    exact_mod_cast Real.rpow_natCast (nPPN L W) 6
  have hMk2 : scaleM L W E u ^ 2 ≤ nPPN L W ^ 2 := pow_le_pow_left₀ hMk0.le hMkN 2
  have hpos : 0 ≤ (W : ℝ) ^ (-(6 / c)) := Real.rpow_nonneg hW0.le _
  calc scaleM L W E u ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c)))
      ≤ nPPN L W ^ 2 * (nPPN L W ^ 2 * ((nPPN L W) ^ 6)⁻¹) := by
        rw [← hN6]
        exact mul_le_mul hMk2 (mul_le_mul_of_nonneg_left hWneg (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) hpos) (sq_nonneg _)
    _ = ((nPPN L W) ^ 2)⁻¹ := by field_simp

/-- **The drift sum at one size** (recounted for `d = 2`): for the grid
`u_j`, `0 ≤ Δ`, `k ≤ K`, `J_j ≤ m`, `Σ_{j<K} Δ/η_{u_j} ≤ (Im m)⁻¹ log N`, `W ≥ N^c`,
`M_k² Δ Σ_{j<k} CU² d_j ≤ c'/4 + C_q m² Lg / M_v`. -/
private theorem ppc_drift_sum {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E c ε : ℝ} (hE : |E| < 2)
    (hc : 0 < c) (hε : 0 < ε) (hbw : (nPPN L W) ^ c ≤ (W : ℝ)) {CU R : ℝ} (hR0 : 0 ≤ R)
    {u : ℕ → ℝ} {Δ v : ℝ} {K k : ℕ} (hk : k ≤ K) (hΔ : 0 ≤ Δ)
    (hmono : ∀ i j, i ≤ j → u i ≤ u j) (hle : ∀ j ≤ K, u j ≤ v) (hv1 : v < 1)
    (hkΔ : (k : ℝ) * Δ ≤ 1)
    (hsum : ∑ j ∈ Finset.range K, Δ / etaT E (u j) ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W))
    {J : ℕ → ℝ} (hJ0 : ∀ j, 0 ≤ J j) {m : ℝ} (hm0 : 0 ≤ m) (hJm : ∀ j < k, J j ≤ m) :
    scaleM L W E (u k) ^ 2 * (Δ * ∑ j ∈ Finset.range k, CU ^ 2 *
        dBoundPPN L W E (u j) ((nPPN L W) ^ ε) (R ^ 4) ε (6 / c) (J j)) ≤
      cPrimePPN CU ((nPPN L W) ^ ε) R (LgPPN E (nPPN L W)) / 4 +
        CqPPN CU (W : ℝ) ε * m ^ 2 * LgPPN E (nPPN L W) / scaleM L W E v := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hN0 : 0 < nPPN L W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hΓ1 : 1 ≤ (nPPN L W) ^ ε := Real.one_le_rpow hN1 hε.le
  have hw1 : 1 ≤ (W : ℝ) ^ (2 * ε) := Real.one_le_rpow hW1 (by linarith)
  have hwΓ : (W : ℝ) ^ (2 * ε) ≤ (nPPN L W) ^ ε := by
    have e : (W : ℝ) ^ (2 * ε) = ((W : ℝ) ^ 2) ^ ε := by
      rw [Real.rpow_mul (by positivity), Real.rpow_two]
    rw [e]
    exact Real.rpow_le_rpow (sq_nonneg _) (ppc_W2_le_N hL1) hε.le
  have hLg : 1 ≤ LgPPN E (nPPN L W) := ppc_Lg_ge_one hE hN1
  have hv0 : 0 < scaleM L W E v := scaleM_pos hL1 hW hE hv1
  have hvN : scaleM L W E v ≤ nPPN L W := ppc_scaleM_le_N hL1 hv1
  have hf0 : 0 ≤ ((nPPN L W) ^ 2)⁻¹ := by positivity
  have hf1 : ((nPPN L W) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN1)
  have hfM : ((nPPN L W) ^ 2)⁻¹ * scaleM L W E v ≤ 1 := by
    calc ((nPPN L W) ^ 2)⁻¹ * scaleM L W E v ≤ ((nPPN L W) ^ 2)⁻¹ * nPPN L W :=
          mul_le_mul_of_nonneg_left hvN hf0
      _ = (nPPN L W)⁻¹ := by field_simp
      _ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hkv : u k ≤ v := hle k hk
  have hk1 : u k < 1 := hkv.trans_lt hv1
  have hFk := ppc_far hL hW hE hc hbw hk1
  have hFk0 : 0 ≤ scaleM L W E (u k) ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg W) _))
  have hS : ∑ j ∈ Finset.range k, Δ / etaT E (u j) ≤ LgPPN E (nPPN L W) := by
    calc ∑ j ∈ Finset.range k, Δ / etaT E (u j)
        ≤ ∑ j ∈ Finset.range K, Δ / etaT E (u j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun j hj _ =>
            div_nonneg hΔ (etaT_pos hE ((hle j (Finset.mem_range.1 hj).le).trans_lt hv1)).le)
      _ ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W) := hsum
      _ ≤ LgPPN E (nPPN L W) := by unfold LgPPN; linarith
  set Mk := scaleM L W E (u k) with hMkdef
  set Mv := scaleM L W E v with hMvdef
  set Γ := (nPPN L W) ^ ε with hΓdef
  set w := (W : ℝ) ^ (2 * ε) with hwdef
  set Lg := LgPPN E (nPPN L W) with hLgdef
  set Fk := Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))) with hFkdef
  have hterm : ∀ j ∈ Finset.range k, Mk ^ 2 * (CU ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) ≤
      CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) * (etaT E (u j))⁻¹ +
        1000 * (Fk * (m + Γ))) := by
    intro j hj
    have hjk : u j ≤ u k := hmono j k (Finset.mem_range.1 hj).le
    have h := ppc_drift_term (E := E) (ε := ε) (D' := 6 / c) hL1 hW hE hjk hkv hv1
      (Γ := Γ) (Φ := R ^ 4) (hJ0 j) (hJm j (Finset.mem_range.1 hj)) (by linarith) (by positivity)
    rw [← hMkdef, ← hMvdef, ← hwdef] at h
    have hF : Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c)) * (m + Γ)) = Fk * (m + Γ) := by
      rw [hFkdef]; ring
    rw [hF] at h
    have e : Mk ^ 2 * (CU ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) =
        CU ^ 2 * (Mk ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) := by ring
    rw [e]
    calc CU ^ 2 * (Mk ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j))
        ≤ CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ * (etaT E (u j))⁻¹ +
          w * Γ ^ 2 * R ^ 4 * (etaT E (u j))⁻¹ + Fk * (m + Γ))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by ring
  have hsumle : ∑ j ∈ Finset.range k, Mk ^ 2 *
        (CU ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) ≤
      ∑ j ∈ Finset.range k, CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) *
          (etaT E (u j))⁻¹ + 1000 * (Fk * (m + Γ))) := Finset.sum_le_sum hterm
  have hsumeq : ∑ j ∈ Finset.range k, Δ * (CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) *
          (etaT E (u j))⁻¹ + 1000 * (Fk * (m + Γ)))) =
      CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) *
          (∑ j ∈ Finset.range k, Δ / etaT E (u j)) +
        CU ^ 2 * (1000 * (Fk * (m + Γ))) * ((k : ℝ) * Δ) := by
    have : ∀ j ∈ Finset.range k, Δ * (CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) *
          (etaT E (u j))⁻¹ + 1000 * (Fk * (m + Γ)))) =
        CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) * (Δ / etaT E (u j)) +
          CU ^ 2 * (1000 * (Fk * (m + Γ))) * Δ := by
      intro j _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  have hlhs : Mk ^ 2 * (Δ * ∑ j ∈ Finset.range k, CU ^ 2 *
        dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) =
      Δ * ∑ j ∈ Finset.range k, Mk ^ 2 * (CU ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : 0 ≤ CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) := by positivity
  have hcoef2 : 0 ≤ CU ^ 2 * (1000 * (Fk * (m + Γ))) := by
    have : 0 ≤ m + Γ := by linarith
    positivity
  have hbound : Mk ^ 2 * (Δ * ∑ j ∈ Finset.range k, CU ^ 2 *
        dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) ≤
      CU ^ 2 * ((1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) * Lg + 1000 * (Fk * (m + Γ))) := by
    calc Mk ^ 2 * (Δ * ∑ j ∈ Finset.range k, CU ^ 2 *
        dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j))
        = Δ * ∑ j ∈ Finset.range k, Mk ^ 2 *
          (CU ^ 2 * dBoundPPN L W E (u j) Γ (R ^ 4) ε (6 / c) (J j)) := hlhs
      _ ≤ Δ * ∑ j ∈ Finset.range k, CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) *
          (etaT E (u j))⁻¹ + 1000 * (Fk * (m + Γ))) := mul_le_mul_of_nonneg_left hsumle hΔ
      _ = ∑ j ∈ Finset.range k, Δ * (CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4) *
          (etaT E (u j))⁻¹ + 1000 * (Fk * (m + Γ)))) := Finset.mul_sum _ _ _
      _ = _ := hsumeq
      _ ≤ CU ^ 2 * (1000 * (w * m ^ 2 * Mv⁻¹ + w * Γ ^ 2 * R ^ 4)) * Lg +
          CU ^ 2 * (1000 * (Fk * (m + Γ))) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hS hcoef) (mul_le_mul_of_nonneg_left hkΔ hcoef2)
      _ = _ := by ring
  have halg := ppc_drift_alg (CU2 := CU ^ 2) (w := w) (Γ := Γ) (R := R) (Lg := Lg) (Mv := Mv)
    (m := m) (f := ((nPPN L W) ^ 2)⁻¹) (Fk := Fk) (sq_nonneg CU) hw1 hwΓ hR0 hLg hv0 hm0 hf0 hf1
    hfM hFk0 hFk
  refine hbound.trans (halg.trans_eq ?_)
  unfold cPrimePPN C0PPN CqPPN
  rfl

private theorem ppc_R_ge_one {L : ℕ} (hL : 1 ≤ L) {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v)
    (hv1 : v < 1) : 1 ≤ ellT L v / ellT L s := by
  have h := (ellT_mono_ratio hL hs0 hsv hv1).1
  have hpos := (ellT_pos_le hL (hsv.trans_lt hv1)).1
  exact (one_le_div hpos).2 h

end Drift

/-! ## 3. The Azuma sum -/

section QV

private theorem ppc_sum_shift (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) (k : ℕ) :
    ∑ j ∈ Finset.range k, f (j + 1) ≤ ∑ j ∈ Finset.range k, f j + f k := by
  have h1 := Finset.sum_range_succ' f k
  have h2 := Finset.sum_range_succ f k
  linarith

/-- The last grid step: `Δ ≤ K⁻¹ ≤ N^{-C_K} ≤ N^{-1+τ} ≤ 1 - u` gives `Δ/η_u ≤ (Im m)⁻¹`. -/
private theorem ppc_last {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E τ CK Δ u : ℝ} {K : ℕ}
    (hE : |E| < 2) (hτ : 0 < τ) (hCK : 1 ≤ CK) (hKN : (nPPN L W) ^ CK ≤ K) (hΔ0 : 0 ≤ Δ)
    (hΔK : Δ ≤ (K : ℝ)⁻¹) (hu1 : u < 1) (hrange : (nPPN L W) ^ (-1 + τ) ≤ 1 - u) :
    Δ / etaT E u ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W) := by
  have hN1 := ppc_one_le_N (L := L) (W := W) (by omega) hW
  have hN0 : 0 < nPPN L W := by linarith
  have him := spectralM_im_pos hE
  set a := (nPPN L W) ^ (-1 + τ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hNCK : 0 < (nPPN L W) ^ CK := Real.rpow_pos_of_pos hN0 _
  have hKa : (K : ℝ)⁻¹ ≤ a := by
    calc (K : ℝ)⁻¹ ≤ ((nPPN L W) ^ CK)⁻¹ := inv_anti₀ hNCK hKN
      _ = (nPPN L W) ^ (-CK) := (Real.rpow_neg hN0.le _).symm
      _ ≤ a := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hη : a * (spectralM E).im ≤ etaT E u := by
    unfold etaT; exact mul_le_mul_of_nonneg_right hrange him.le
  have h1 : Δ / etaT E u ≤ a / (a * (spectralM E).im) :=
    div_le_div₀ ha0.le (hΔK.trans hKa) (mul_pos ha0 him) hη
  have h2 : a / (a * (spectralM E).im) = (spectralM E).im⁻¹ := by field_simp
  have hlog := ppc_one_le_log hL hW
  calc Δ / etaT E u ≤ (spectralM E).im⁻¹ := h1.trans_eq h2
    _ ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W) :=
        le_mul_of_one_le_right (inv_nonneg.2 him.le) hlog

/-- The algebra of the Azuma sum: `Γ² (C₁ · 2Lg + 1000 CU⁴ + 1) ≤ (c'/4)²`. -/
private theorem ppc_qv_alg {CU w Γ R Lg : ℝ} (hw1 : 1 ≤ w) (hwΓ : w ≤ Γ) (hR : 0 ≤ R)
    (hLg : 1 ≤ Lg) :
    Γ ^ 2 * (1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) + 1000 * CU ^ 4 * 1 + 1) ≤
      (10000 * (CU ^ 2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg / 4) ^ 2 := by
  have hΓ1 : 1 ≤ Γ := hw1.trans hwΓ
  have hΓ0 : 0 ≤ Γ := by linarith
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hR5 : 0 ≤ R ^ 5 := by positivity
  set T := 1 + R ^ 4 + R ^ 5 with hT
  have hT1 : 1 ≤ T := by linarith
  have hR10 : R ^ 10 ≤ T ^ 2 := by
    have : R ^ 5 ≤ T := by linarith
    calc R ^ 10 = (R ^ 5) ^ 2 := by ring
      _ ≤ T ^ 2 := pow_le_pow_left₀ hR5 this 2
  have hA0 : 0 ≤ CU ^ 4 := by positivity
  have hAB : CU ^ 4 ≤ (CU ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg CU, sq_nonneg (CU ^ 2)]
  have hB1 : 1 ≤ (CU ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg CU]
  set B := (CU ^ 2 + 1) ^ 2 with hB
  have hΓ2 : 0 ≤ Γ ^ 2 := by positivity
  have hwΓ' : w * Γ ≤ Γ ^ 2 := by nlinarith
  have hQ : 1 ≤ Γ ^ 2 * T ^ 2 * Lg := by
    have h1 : 1 ≤ Γ ^ 2 := one_le_pow₀ hΓ1
    have h2 : 1 ≤ T ^ 2 := one_le_pow₀ hT1
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ Γ ^ 2 * T ^ 2 * Lg := by gcongr
  have h1 : 1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) ≤ 2000 * CU ^ 4 * (Γ ^ 2 * T ^ 2 * Lg) := by
    have e : 1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) = 2000 * CU ^ 4 * ((w * Γ) * R ^ 10 * Lg) := by
      ring
    rw [e]
    have : (w * Γ) * R ^ 10 * Lg ≤ Γ ^ 2 * T ^ 2 * Lg := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul hwΓ' hR10 (by positivity) hΓ2
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : 1000 * CU ^ 4 * 1 + 1 ≤ 1001 * B * (Γ ^ 2 * T ^ 2 * Lg) := by
    have : 1000 * CU ^ 4 * 1 + 1 ≤ 1001 * B := by nlinarith
    calc 1000 * CU ^ 4 * 1 + 1 ≤ 1001 * B := this
      _ = 1001 * B * 1 := (mul_one _).symm
      _ ≤ 1001 * B * (Γ ^ 2 * T ^ 2 * Lg) := mul_le_mul_of_nonneg_left hQ (by positivity)
  have h3 : 2000 * CU ^ 4 * (Γ ^ 2 * T ^ 2 * Lg) ≤ 2000 * B * (Γ ^ 2 * T ^ 2 * Lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hin : 1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) + 1000 * CU ^ 4 * 1 + 1 ≤
      3001 * B * (Γ ^ 2 * T ^ 2 * Lg) := by linarith
  have hY : 0 ≤ B * T ^ 2 * Γ ^ 4 * Lg := by positivity
  have hΓ2Lg : 1 ≤ Γ ^ 2 * Lg := by
    have h1 : 1 ≤ Γ ^ 2 := one_le_pow₀ hΓ1
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ Γ ^ 2 * Lg := by gcongr
  have hY2 : B * T ^ 2 * Γ ^ 4 * Lg ≤ B * T ^ 2 * Γ ^ 4 * Lg * (Γ ^ 2 * Lg) :=
    le_mul_of_one_le_right hY hΓ2Lg
  calc Γ ^ 2 * (1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) + 1000 * CU ^ 4 * 1 + 1)
      ≤ Γ ^ 2 * (3001 * B * (Γ ^ 2 * T ^ 2 * Lg)) := mul_le_mul_of_nonneg_left hin hΓ2
    _ = 3001 * (B * T ^ 2 * Γ ^ 4 * Lg) := by ring
    _ ≤ 6250000 * (B * T ^ 2 * Γ ^ 4 * Lg * (Γ ^ 2 * Lg)) := by linarith
    _ = (10000 * (CU ^ 2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg / 4) ^ 2 := by
      rw [hB, hT]; ring

/-- `1 ≤ W^{2ε} ≤ N^ε` (as `W² ≤ N`). -/
private theorem ppc_w_facts {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ (W : ℝ) ^ (2 * ε) ∧ (W : ℝ) ^ (2 * ε) ≤ (nPPN L W) ^ ε ∧ 1 ≤ (nPPN L W) ^ ε := by
  have hN1 := ppc_one_le_N hL hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  refine ⟨Real.one_le_rpow hW1 (by linarith), ?_, Real.one_le_rpow hN1 hε.le⟩
  have e : (W : ℝ) ^ (2 * ε) = ((W : ℝ) ^ 2) ^ ε := by
    rw [Real.rpow_mul (by positivity), Real.rpow_two]
  rw [e]
  exact Real.rpow_le_rpow (sq_nonneg _) (ppc_W2_le_N hL) hε.le

/-- **The Azuma sum at one size** (recounted for `d = 2`):
`M_k² N^ε (Σ_{j<k} c_j)^{1/2} ≤ c'/4`. -/
private theorem ppc_qv_sum {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E c ε : ℝ} (hE : |E| < 2)
    (hc : 0 < c) (hε : 0 < ε) (hbw : (nPPN L W) ^ c ≤ (W : ℝ)) {CU R : ℝ} (hR0 : 0 ≤ R)
    {u : ℕ → ℝ} {Δ v : ℝ} {K k : ℕ} (hK : K ≠ 0) (hk : k ≤ K) (hΔ : 0 ≤ Δ)
    (hmono : ∀ i j, i ≤ j → u i ≤ u j) (hle : ∀ j ≤ K, u j ≤ v) (hv1 : v < 1)
    (hkΔ : (k : ℝ) * Δ ≤ 1)
    (hsum : ∑ j ∈ Finset.range K, Δ / etaT E (u j) ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W))
    (hlast : Δ / etaT E (u k) ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W)) :
    scaleM L W E (u k) ^ 2 * ((nPPN L W) ^ ε * Real.sqrt (∑ j ∈ Finset.range k,
        (Real.toNNReal (cQPPN L W E (u (j + 1)) ((nPPN L W) ^ ε) (R ^ 10) ε (6 / c) Δ CU K) : ℝ))) ≤
      cPrimePPN CU ((nPPN L W) ^ ε) R (LgPPN E (nPPN L W)) / 4 := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hN0 : 0 < nPPN L W := by linarith
  obtain ⟨hw1, hwΓ, hΓ1⟩ := ppc_w_facts hL1 hW hε
  have hLg : 1 ≤ LgPPN E (nPPN L W) := ppc_Lg_ge_one hE hN1
  have hkv : u k ≤ v := hle k hk
  have hk1 : u k < 1 := hkv.trans_lt hv1
  have hMk0 : 0 < scaleM L W E (u k) := scaleM_pos hL1 hW hE hk1
  have hMkN : scaleM L W E (u k) ≤ nPPN L W := ppc_scaleM_le_N hL1 hk1
  have hFk := ppc_far hL hW hE hc hbw hk1
  have hFk0 : 0 ≤ scaleM L W E (u k) ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg W) _))
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hK
  have hN10 : (nPPN L W) ^ (-(10 : ℝ)) = ((nPPN L W) ^ 10)⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    congr 1
    exact_mod_cast Real.rpow_natCast (nPPN L W) 10
  have hN10n : 0 ≤ (nPPN L W) ^ (-(10 : ℝ)) := Real.rpow_nonneg hN0.le _
  set Mk := scaleM L W E (u k) with hMkdef
  set Γ := (nPPN L W) ^ ε with hΓdef
  set w := (W : ℝ) ^ (2 * ε) with hwdef
  set Lg := LgPPN E (nPPN L W) with hLgdef
  have hG : Mk ^ 4 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))) ≤ 1 := by
    calc Mk ^ 4 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c)))
        = Mk ^ 2 * (Mk ^ 2 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c)))) := by ring
      _ ≤ nPPN L W ^ 2 * ((nPPN L W) ^ 2)⁻¹ :=
          mul_le_mul (pow_le_pow_left₀ hMk0.le hMkN 2) hFk hFk0 (sq_nonneg _)
      _ = 1 := by field_simp
  have hKN : Mk ^ 4 * (nPPN L W) ^ (-(10 : ℝ)) ≤ 1 := by
    have h1 : Mk ^ 4 ≤ (nPPN L W) ^ 4 := pow_le_pow_left₀ hMk0.le hMkN 4
    calc Mk ^ 4 * (nPPN L W) ^ (-(10 : ℝ)) ≤ (nPPN L W) ^ 4 * (nPPN L W) ^ (-(10 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hN10n
      _ = ((nPPN L W) ^ 6)⁻¹ := by rw [hN10]; field_simp
      _ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN1)
  have hterm : ∀ j ∈ Finset.range k, Mk ^ 4 *
        cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K ≤
      (Δ / etaT E (u (j + 1))) * (1000 * CU ^ 4 * w * Γ * R ^ 10) + Δ * (1000 * CU ^ 4) +
        (K : ℝ)⁻¹ := by
    intro j hj
    have hj1 : j + 1 ≤ k := Finset.mem_range.1 hj
    have hu1 : u (j + 1) ≤ u k := hmono _ _ hj1
    have hu1v : u (j + 1) < 1 := hu1.trans_lt hk1
    have hM1 : 0 < scaleM L W E (u (j + 1)) := scaleM_pos hL1 hW hE hu1v
    have hMM : Mk ≤ scaleM L W E (u (j + 1)) := (scaleM_anti_ratio hL1 hE hu1 hk1).1
    have hη : 0 < etaT E (u (j + 1)) := etaT_pos hE hu1v
    have hMM4 : Mk ^ 4 * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 ≤ 1 := by
      calc Mk ^ 4 * (scaleM L W E (u (j + 1)))⁻¹ ^ 4
          ≤ (scaleM L W E (u (j + 1))) ^ 4 * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 := by gcongr
        _ = 1 := by field_simp
    unfold cQPPN eeBdPPN
    have hηi : 0 ≤ (etaT E (u (j + 1)))⁻¹ := inv_nonneg.2 hη.le
    have hwn : 0 ≤ w := by linarith
    have hKi : 0 ≤ (K : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
    have ha : Mk ^ 4 * (w * (Γ * R ^ 10) * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 *
        (etaT E (u (j + 1)))⁻¹) ≤ w * (Γ * R ^ 10) * (etaT E (u (j + 1)))⁻¹ := by
      have e : Mk ^ 4 * (w * (Γ * R ^ 10) * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 *
          (etaT E (u (j + 1)))⁻¹) = (w * (Γ * R ^ 10) * (etaT E (u (j + 1)))⁻¹) *
            (Mk ^ 4 * (scaleM L W E (u (j + 1)))⁻¹ ^ 4) := by ring
      rw [e]
      calc _ ≤ (w * (Γ * R ^ 10) * (etaT E (u (j + 1)))⁻¹) * 1 :=
            mul_le_mul_of_nonneg_left hMM4 (by positivity)
        _ = _ := mul_one _
    have hKt : Mk ^ 4 * ((K : ℝ)⁻¹ * (nPPN L W) ^ (-(10 : ℝ))) ≤ (K : ℝ)⁻¹ := by
      calc Mk ^ 4 * ((K : ℝ)⁻¹ * (nPPN L W) ^ (-(10 : ℝ)))
          = (K : ℝ)⁻¹ * (Mk ^ 4 * (nPPN L W) ^ (-(10 : ℝ))) := by ring
        _ ≤ (K : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hKN hKi
        _ = _ := mul_one _
    have hc4 : 0 ≤ Δ * (CU ^ 4 * 1000) := by positivity
    calc Mk ^ 4 * (Δ * (CU ^ 4 * (1000 * (w * (Γ * R ^ 10) * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 *
          (etaT E (u (j + 1)))⁻¹ + nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c))))) +
          (K : ℝ)⁻¹ * (nPPN L W) ^ (-(10 : ℝ)))
        = (Δ * (CU ^ 4 * 1000)) * (Mk ^ 4 * (w * (Γ * R ^ 10) * (scaleM L W E (u (j + 1)))⁻¹ ^ 4 *
          (etaT E (u (j + 1)))⁻¹)) + (Δ * (CU ^ 4 * 1000)) *
          (Mk ^ 4 * (nPPN L W ^ 2 * (W : ℝ) ^ (-(6 / c)))) +
          Mk ^ 4 * ((K : ℝ)⁻¹ * (nPPN L W) ^ (-(10 : ℝ))) := by ring
      _ ≤ (Δ * (CU ^ 4 * 1000)) * (w * (Γ * R ^ 10) * (etaT E (u (j + 1)))⁻¹) +
          (Δ * (CU ^ 4 * 1000)) * 1 + (K : ℝ)⁻¹ :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha hc4)
            (mul_le_mul_of_nonneg_left hG hc4)) hKt
      _ = _ := by ring
  have hcq0 : ∀ j ∈ Finset.range k, 0 ≤ cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K := by
    intro j hj
    have hj1 : j + 1 ≤ k := Finset.mem_range.1 hj
    have hu1v : u (j + 1) < 1 := (hmono _ _ hj1).trans_lt hk1
    have hη : 0 < etaT E (u (j + 1)) := etaT_pos hE hu1v
    have hwn : 0 ≤ w := by linarith
    have hKi : 0 ≤ (K : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
    unfold cQPPN eeBdPPN
    have : 0 ≤ (Γ * R ^ 10) := by positivity
    positivity
  have hcoe : ∑ j ∈ Finset.range k,
      (Real.toNNReal (cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K) : ℝ) =
      ∑ j ∈ Finset.range k, cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K :=
    Finset.sum_congr rfl fun j hj => Real.coe_toNNReal _ (hcq0 j hj)
  rw [hcoe]
  set S := ∑ j ∈ Finset.range k, cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg hcq0
  -- the shifted sum of `Δ/η`
  have hsh : ∑ j ∈ Finset.range k, Δ / etaT E (u (j + 1)) ≤ 2 * Lg := by
    have h0 : 0 ≤ Δ / etaT E (u 0) :=
      div_nonneg hΔ (etaT_pos hE ((hmono 0 k (Nat.zero_le _)).trans_lt hk1)).le
    have h1 := ppc_sum_shift (fun j => Δ / etaT E (u j)) h0 k
    have h2 : ∑ j ∈ Finset.range k, Δ / etaT E (u j) ≤ (spectralM E).im⁻¹ * Real.log (nPPN L W) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun j hj _ =>
        div_nonneg hΔ (etaT_pos hE ((hle j (Finset.mem_range.1 hj).le).trans_lt hv1)).le)).trans hsum
    have h3 : (spectralM E).im⁻¹ * Real.log (nPPN L W) ≤ Lg := by
      rw [hLgdef]; unfold LgPPN; linarith
    linarith
  have hkK : (k : ℝ) * (K : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    exact_mod_cast hk
  have hsumS : Mk ^ 4 * S ≤ 1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) + 1000 * CU ^ 4 * 1 + 1 := by
    have hsumle : ∑ j ∈ Finset.range k, Mk ^ 4 *
        cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K ≤
        ∑ j ∈ Finset.range k, ((Δ / etaT E (u (j + 1))) * (1000 * CU ^ 4 * w * Γ * R ^ 10) +
          Δ * (1000 * CU ^ 4) + (K : ℝ)⁻¹) := Finset.sum_le_sum hterm
    have hsumeq : ∑ j ∈ Finset.range k, ((Δ / etaT E (u (j + 1))) *
        (1000 * CU ^ 4 * w * Γ * R ^ 10) + Δ * (1000 * CU ^ 4) + (K : ℝ)⁻¹) =
        (∑ j ∈ Finset.range k, Δ / etaT E (u (j + 1))) * (1000 * CU ^ 4 * w * Γ * R ^ 10) +
          (k : ℝ) * (Δ * (1000 * CU ^ 4)) + (k : ℝ) * (K : ℝ)⁻¹ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
    have hC1 : 0 ≤ 1000 * CU ^ 4 * w * Γ * R ^ 10 := by
      have : 0 ≤ w := by linarith
      positivity
    have hC2 : 0 ≤ 1000 * CU ^ 4 := by positivity
    rw [hSdef, Finset.mul_sum]
    calc ∑ j ∈ Finset.range k, Mk ^ 4 * cQPPN L W E (u (j + 1)) Γ (R ^ 10) ε (6 / c) Δ CU K
        ≤ _ := hsumle
      _ = _ := hsumeq
      _ ≤ (2 * Lg) * (1000 * CU ^ 4 * w * Γ * R ^ 10) + 1000 * CU ^ 4 * 1 + 1 := by
        have e2 : (k : ℝ) * (Δ * (1000 * CU ^ 4)) = ((k : ℝ) * Δ) * (1000 * CU ^ 4) := by ring
        have h2 : ((k : ℝ) * Δ) * (1000 * CU ^ 4) ≤ 1 * (1000 * CU ^ 4) :=
          mul_le_mul_of_nonneg_right hkΔ hC2
        have h1 := mul_le_mul_of_nonneg_right hsh hC1
        linarith
      _ = _ := by ring
  have hX0 : 0 ≤ cPrimePPN CU Γ R Lg / 4 := by
    unfold cPrimePPN C0PPN
    have : 0 ≤ Lg := by linarith
    have : 0 ≤ Γ := by linarith
    positivity
  have halg := ppc_qv_alg (CU := CU) hw1 hwΓ hR0 hLg
  have hsq : (Mk ^ 2 * (Γ * Real.sqrt S)) ^ 2 ≤ (cPrimePPN CU Γ R Lg / 4) ^ 2 := by
    have e : (Mk ^ 2 * (Γ * Real.sqrt S)) ^ 2 = Γ ^ 2 * (Mk ^ 4 * S) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hS0]; ring
    rw [e]
    calc Γ ^ 2 * (Mk ^ 4 * S) ≤ Γ ^ 2 * (1000 * CU ^ 4 * w * Γ * R ^ 10 * (2 * Lg) +
        1000 * CU ^ 4 * 1 + 1) := mul_le_mul_of_nonneg_left hsumS (sq_nonneg _)
      _ ≤ _ := halg.trans_eq (by unfold cPrimePPN C0PPN; rfl)
  exact (pow_le_pow_iff_left₀ (by positivity) hX0 two_ne_zero).1 hsq


end QV

/-! ## 4. The arithmetic inequalities -/

section Arith

/-- `R ≤ ρ^{1/2}` and `ρ^p ≤ Y` give `R⁵ ≤ Y^{5/(2p)}`. -/
private theorem ppc_R5_le {R ρ Y : ℝ} {p : ℕ} (hp0 : 0 < p) (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hRρ : R ≤ ρ ^ ((1 : ℝ) / 2)) (hp : ρ ^ p ≤ Y) : R ^ 5 ≤ Y ^ ((5 : ℝ) / (2 * p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have h1 : R ^ 5 ≤ (ρ ^ ((1 : ℝ) / 2)) ^ 5 := pow_le_pow_left₀ hR hRρ 5
  have h2 : (ρ ^ ((1 : ℝ) / 2)) ^ 5 = (ρ ^ p) ^ ((5 : ℝ) / (2 * p)) := by
    rw [← Real.rpow_natCast (ρ ^ ((1 : ℝ) / 2)) 5, ← Real.rpow_mul hρ,
      ← Real.rpow_natCast ρ p, ← Real.rpow_mul hρ]
    congr 1
    push_cast
    field_simp
  have h3 : (ρ ^ p) ^ ((5 : ℝ) / (2 * p)) ≤ Y ^ ((5 : ℝ) / (2 * p)) :=
    Real.rpow_le_rpow (by positivity) hp (by positivity)
  exact h1.trans (h2.le.trans h3)

/-- The `R` facts of the closure at one size: `1 ≤ R`, `R⁵ ≤ M_v^{5/58}`, `R⁵ ≤ M_s^{1/12}`,
`1 ≤ M_s`, from `ℓ_v/ℓ_s ≤ ((1-s)/(1-v))^{1/2}` (`ellT_mono_ratio`), `r^{29} ≤ M_v`
(`scaleM_ge_pow29`) and `r_t^{30} ≤ M_s` (`CondStInd`). -/
private theorem ppc_R_facts {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E s v t : ℝ} (hE : |E| < 2)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t) (ht : t < 1)
    (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    1 ≤ ellT L v / ellT L s ∧
      (ellT L v / ellT L s) ^ 5 ≤ (scaleM L W E v) ^ ((5 : ℝ) / 58) ∧
      (ellT L v / ellT L s) ^ 5 ≤ (scaleM L W E s) ^ ((1 : ℝ) / 12) ∧ 1 ≤ scaleM L W E s := by
  have hv1 : v < 1 := hvt.trans_lt ht
  have hxt : 0 < 1 - t := by linarith
  have hxv : 0 < 1 - v := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hR1 := ppc_R_ge_one hL hs0 hsv hv1
  have hR0 : 0 ≤ ellT L v / ellT L s := by linarith
  have hRρ := (ellT_mono_ratio hL hs0 hsv hv1).2
  have hρ0 : 0 ≤ (1 - s) / (1 - v) := div_nonneg hxs.le hxv.le
  have hp29 := scaleM_ge_pow29 (W := W) hL hW hE hs0 hsv hvt ht hstep
  have hMs : 0 < scaleM L W E s := scaleM_pos hL hW hE (by linarith)
  have hq : 0 < ((1 - t) / (1 - s)) ^ 30 := pow_pos (div_pos hxt hxs) 30
  have hr : ((1 - s) / (1 - t)) ^ 30 ≤ scaleM L W E s := by
    have := (inv_le_comm₀ hMs hq).1 hstep
    rwa [← inv_pow, inv_div] at this
  have hrv : (1 - s) / (1 - v) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_left hxs.le hxt (by linarith)
  have h30 : ((1 - s) / (1 - v)) ^ 30 ≤ scaleM L W E s :=
    (pow_le_pow_left₀ hρ0 hrv 30).trans hr
  have h5 := ppc_R5_le (p := 29) (by norm_num) hR0 hρ0 hRρ hp29
  have h6 := ppc_R5_le (p := 30) (by norm_num) hR0 hρ0 hRρ h30
  refine ⟨hR1, ?_, ?_, ?_⟩
  · have e : (5 : ℝ) / (2 * ((29 : ℕ) : ℝ)) = 5 / 58 := by norm_num
    rwa [e] at h5
  · have e : (5 : ℝ) / (2 * ((30 : ℕ) : ℝ)) = 1 / 12 := by norm_num
    rwa [e] at h6
  · have h1 : 1 ≤ ((1 - s) / (1 - t)) ^ 30 :=
      one_le_pow₀ ((one_le_div hxt).2 (by linarith))
    exact h1.trans hr

/-- The exponent bookkeeping of the forbidden zone: `Q P⁶ N^{m₀/2} R⁵ ≤ X` from
`μ N^{m₀} ≤ X`, `R⁵ ≤ X^{5/58}` and `Q P⁶ ≤ μ^{1/2+12/29} N^{(12/29) m₀}`
(`1/2 + 5/58 + 12/29 = 1`). -/
private theorem ppc_zone_core {X N μ m0 R P Q : ℝ} (hμ : 0 < μ) (hN : 1 ≤ N)
    (hX : μ * N ^ m0 ≤ X) (hR5 : R ^ 5 ≤ X ^ ((5 : ℝ) / 58)) (hR0 : 0 ≤ R)
    (hQP : 0 ≤ Q * P ^ 6)
    (hpoly : Q * P ^ 6 ≤ μ ^ ((1 : ℝ) / 2 + 12 / 29) * N ^ ((12 / 29) * m0)) :
    Q * P ^ 6 * N ^ (m0 / 2) * R ^ 5 ≤ X := by
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N ^ m0 := Real.rpow_pos_of_pos hN0 _
  have hX0 : 0 < X := lt_of_lt_of_le (mul_pos hμ hNm) hX
  have hμh : 0 < μ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hμ _
  have h1 : N ^ (m0 / 2) ≤ X ^ ((1 : ℝ) / 2) / μ ^ ((1 : ℝ) / 2) := by
    have h : N ^ m0 ≤ X / μ := by rw [le_div_iff₀ hμ]; linarith
    calc N ^ (m0 / 2) = (N ^ m0) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ (X / μ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hNm.le h (by norm_num)
      _ = X ^ ((1 : ℝ) / 2) / μ ^ ((1 : ℝ) / 2) := Real.div_rpow hX0.le hμ.le _
  have h2 : Q * P ^ 6 ≤ μ ^ ((1 : ℝ) / 2) * X ^ ((12 : ℝ) / 29) := by
    calc Q * P ^ 6 ≤ μ ^ ((1 : ℝ) / 2 + 12 / 29) * N ^ ((12 / 29) * m0) := hpoly
      _ = μ ^ ((1 : ℝ) / 2) * (μ ^ ((12 : ℝ) / 29) * (N ^ m0) ^ ((12 : ℝ) / 29)) := by
          rw [Real.rpow_add hμ, ← Real.rpow_mul hN0.le, mul_comm m0]
          have : (12 / 29 : ℝ) = (12 : ℝ) / 29 := rfl
          ring_nf
      _ = μ ^ ((1 : ℝ) / 2) * (μ * N ^ m0) ^ ((12 : ℝ) / 29) := by
          rw [Real.mul_rpow hμ.le hNm.le]
      _ ≤ μ ^ ((1 : ℝ) / 2) * X ^ ((12 : ℝ) / 29) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hX (by norm_num)) hμh.le
  have hNh : 0 ≤ N ^ (m0 / 2) := Real.rpow_nonneg hN0.le _
  have hXh : 0 ≤ X ^ ((5 : ℝ) / 58) := Real.rpow_nonneg hX0.le _
  calc Q * P ^ 6 * N ^ (m0 / 2) * R ^ 5
      ≤ (μ ^ ((1 : ℝ) / 2) * X ^ ((12 : ℝ) / 29)) * (X ^ ((1 : ℝ) / 2) / μ ^ ((1 : ℝ) / 2)) *
        X ^ ((5 : ℝ) / 58) :=
        mul_le_mul (mul_le_mul h2 h1 hNh (by positivity)) hR5 (by positivity) (by positivity)
    _ = X ^ ((12 : ℝ) / 29) * X ^ ((1 : ℝ) / 2) * X ^ ((5 : ℝ) / 58) := by field_simp
    _ = X ^ ((12 : ℝ) / 29 + 1 / 2 + 5 / 58) := by rw [Real.rpow_add hX0, Real.rpow_add hX0]
    _ = X := by norm_num

/-- The size-dependent constants at one size: `CU ≤ (1 + A0)(1 + log N)`, `Lg ≤ μ⁻¹ (1 + log N)`,
`CU² (CU² + 1) ≤ 2 Λ⁴` with `Λ = (1 + A0)(1 + log N)`. -/
private theorem ppc_const_facts {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E A0 μ : ℝ} (hE : |E| < 2)
    (hA0 : 0 < A0) (hμ : 0 < μ) (hμE : μ ≤ (spectralM E).im) :
    0 ≤ CUN A0 L ∧ CUN A0 L ^ 2 * (CUN A0 L ^ 2 + 1) ≤ 2 * ((1 + A0) * (1 + Real.log (nPPN L W))) ^ 4 ∧
      CUN A0 L ^ 2 + 1 ≤ 2 * ((1 + A0) * (1 + Real.log (nPPN L W))) ^ 2 ∧
      1 ≤ LgPPN E (nPPN L W) ∧ LgPPN E (nPPN L W) ≤ μ⁻¹ * (1 + Real.log (nPPN L W)) := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hμ1 : μ ≤ 1 := hμE.trans (ppc_im_le_one E)
  have hlog0 : 0 ≤ Real.log (nPPN L W) := Real.log_nonneg hN1
  have hlogL : Real.log (L : ℝ) ≤ Real.log (nPPN L W) :=
    Real.log_le_log (by positivity) (ppc_L_le_N hL1 hW)
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  set P := 1 + Real.log (nPPN L W) with hPdef
  have hP1 : 1 ≤ P := by linarith
  have hCU0 : 0 ≤ CUN A0 L := by unfold CUN; nlinarith
  have hCUle : CUN A0 L ≤ (1 + A0) * P := by unfold CUN; nlinarith
  have hΛ1 : 1 ≤ (1 + A0) * P := by nlinarith
  have hCU2 : CUN A0 L ^ 2 ≤ ((1 + A0) * P) ^ 2 := pow_le_pow_left₀ hCU0 hCUle 2
  have hΛ2 : 1 ≤ ((1 + A0) * P) ^ 2 := one_le_pow₀ hΛ1
  refine ⟨hCU0, ?_, ?_, ppc_Lg_ge_one hE hN1, ?_⟩
  · have h1 : CUN A0 L ^ 2 + 1 ≤ ((1 + A0) * P) ^ 2 + 1 := by linarith
    calc CUN A0 L ^ 2 * (CUN A0 L ^ 2 + 1)
        ≤ ((1 + A0) * P) ^ 2 * (((1 + A0) * P) ^ 2 + 1) :=
          mul_le_mul hCU2 h1 (by positivity) (by positivity)
      _ ≤ ((1 + A0) * P) ^ 2 * (2 * ((1 + A0) * P) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * ((1 + A0) * P) ^ 4 := by ring
  · linarith
  · unfold LgPPN
    have him := spectralM_im_pos hE
    have h1 : (spectralM E).im⁻¹ ≤ μ⁻¹ := inv_anti₀ hμ hμE
    have h2 : 1 ≤ μ⁻¹ := (one_le_inv₀ hμ).2 hμ1
    calc (spectralM E).im⁻¹ * Real.log (nPPN L W) + 1
        ≤ μ⁻¹ * Real.log (nPPN L W) + μ⁻¹ := by
          have := mul_le_mul_of_nonneg_right h1 hlog0
          linarith
      _ = μ⁻¹ * P := by rw [hPdef]; ring

/-- `A (1 + log x)^p ≤ a x^δ` eventually, for `a > 0`. -/
private theorem ppc_polylog_le' (A a δ : ℝ) (p : ℕ) (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, A * (1 + Real.log x) ^ p ≤ a * x ^ δ := by
  filter_upwards [ppc_polylog_le (A / a) δ p hδ] with x hx
  have : A * (1 + Real.log x) ^ p = a * (A / a * (1 + Real.log x) ^ p) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hx ha.le

/-- **The forbidden zone at one size**: `4 C_q c' Lg ≤ M_v` from `μ N^{m₀} ≤ M_v`,
`R⁵ ≤ M_v^{5/58}`, `4ε ≤ m₀/2`, and the polylogarithmic premise. -/
private theorem ppc_zone_n {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E ε m0 A0 μ : ℝ} (hE : |E| < 2)
    (hε : 0 < ε) (hεm : 4 * ε ≤ m0 / 2) (hA0 : 0 < A0) (hμ : 0 < μ)
    (hμE : μ ≤ (spectralM E).im) {R X : ℝ} (hR1 : 1 ≤ R) (hR5 : R ^ 5 ≤ X ^ ((5 : ℝ) / 58))
    (hX : μ * (nPPN L W) ^ m0 ≤ X)
    (hpoly : (480000000 * (1 + A0) ^ 4 / μ ^ 2) * (1 + Real.log (nPPN L W)) ^ 6 ≤
        μ ^ ((1 : ℝ) / 2 + 12 / 29) * (nPPN L W) ^ ((12 / 29) * m0)) :
    4 * CqPPN (CUN A0 L) (W : ℝ) ε * cPrimePPN (CUN A0 L) ((nPPN L W) ^ ε) R
        (LgPPN E (nPPN L W)) * LgPPN E (nPPN L W) ≤ X := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hN0 : 0 < nPPN L W := by linarith
  obtain ⟨hw1, hwΓ, hΓ1⟩ := ppc_w_facts hL1 hW hε
  obtain ⟨hCU0, hc1, -, hLg1, hLgle⟩ := ppc_const_facts hL hW hE hA0 hμ hμE
  have hlog0 : 0 ≤ Real.log (nPPN L W) := Real.log_nonneg hN1
  set N := nPPN L W with hNdef
  set P := 1 + Real.log N with hPdef
  have hP1 : 1 ≤ P := by linarith
  set Γ := N ^ ε with hΓdef
  set w := (W : ℝ) ^ (2 * ε) with hwdef
  set Lg := LgPPN E N with hLgdef
  have hΓ0 : 0 ≤ Γ := by linarith
  have hΓ4 : Γ ^ 4 ≤ N ^ (m0 / 2) := by
    have e : Γ ^ 4 = N ^ (ε * 4) := by
      rw [hΓdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hR5' : 0 ≤ R ^ 5 := by positivity
  have hLg0 : 0 ≤ Lg := by linarith
  have hLL : Lg * Lg ≤ (μ⁻¹ * P) ^ 2 := by
    rw [← sq]; exact pow_le_pow_left₀ hLg0 hLgle 2
  have hwΓ3 : w * Γ ^ 3 ≤ Γ ^ 4 := by
    have := mul_le_mul_of_nonneg_right hwΓ (pow_nonneg hΓ0 3)
    calc w * Γ ^ 3 ≤ Γ * Γ ^ 3 := this
      _ = Γ ^ 4 := by ring
  have hC : 1 + R ^ 4 + R ^ 5 ≤ 3 * R ^ 5 := by
    have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
    have h0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
    linarith
  have hQP : 0 ≤ (480000000 * (1 + A0) ^ 4 / μ ^ 2) * P ^ 6 := by positivity
  have hstep : 4 * CqPPN (CUN A0 L) (W : ℝ) ε * cPrimePPN (CUN A0 L) Γ R Lg * Lg ≤
      (480000000 * (1 + A0) ^ 4 / μ ^ 2) * P ^ 6 * N ^ (m0 / 2) * R ^ 5 := by
    have e1 : 4 * CqPPN (CUN A0 L) (W : ℝ) ε * cPrimePPN (CUN A0 L) Γ R Lg * Lg =
        80000000 * (CUN A0 L ^ 2 * (CUN A0 L ^ 2 + 1)) * (w * Γ ^ 3) * (1 + R ^ 4 + R ^ 5) *
          (Lg * Lg) := by
      unfold CqPPN cPrimePPN C0PPN; ring
    have e2 : 80000000 * (2 * ((1 + A0) * P) ^ 4) * Γ ^ 4 * (3 * R ^ 5) * (μ⁻¹ * P) ^ 2 =
        (480000000 * (1 + A0) ^ 4 / μ ^ 2) * P ^ 6 * Γ ^ 4 * R ^ 5 := by
      field_simp; ring
    rw [e1]
    calc 80000000 * (CUN A0 L ^ 2 * (CUN A0 L ^ 2 + 1)) * (w * Γ ^ 3) * (1 + R ^ 4 + R ^ 5) *
          (Lg * Lg)
        ≤ 80000000 * (2 * ((1 + A0) * P) ^ 4) * Γ ^ 4 * (3 * R ^ 5) * (μ⁻¹ * P) ^ 2 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul
            (mul_le_mul_of_nonneg_left hc1 (by norm_num)) hwΓ3 (by positivity) (by positivity)) hC
            (by positivity) (by positivity)) hLL (by positivity) (by positivity)
      _ = (480000000 * (1 + A0) ^ 4 / μ ^ 2) * P ^ 6 * Γ ^ 4 * R ^ 5 := e2
      _ ≤ (480000000 * (1 + A0) ^ 4 / μ ^ 2) * P ^ 6 * N ^ (m0 / 2) * R ^ 5 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ4 hQP) hR5'
  exact hstep.trans (ppc_zone_core hμ hN1 hX hR5 hR0 hQP hpoly)

/-- **The output inequality at one size**: `2 c' ≤ N^{τ'} M_s^{1/2}` from `R⁵ ≤ M_s^{1/12}`,
`1 ≤ M_s`, `8ε ≤ τ'` and the polylogarithmic premise. -/
private theorem ppc_out_n {L W : ℕ} (hL : 3 ≤ L) (hW : 1 ≤ W) {E ε τ' A0 μ : ℝ} (hE : |E| < 2)
    (hε : 0 < ε) (hτ' : 8 * ε ≤ τ') (hA0 : 0 < A0) (hμ : 0 < μ)
    (hμE : μ ≤ (spectralM E).im) {R Ms : ℝ} (hR1 : 1 ≤ R)
    (hR5 : R ^ 5 ≤ Ms ^ ((1 : ℝ) / 12)) (hMs : 1 ≤ Ms)
    (hpoly : (120000 * (1 + A0) ^ 2 / μ) * (1 + Real.log (nPPN L W)) ^ 3 ≤
      (nPPN L W) ^ (5 * ε)) :
    2 * cPrimePPN (CUN A0 L) ((nPPN L W) ^ ε) R (LgPPN E (nPPN L W)) ≤
      (nPPN L W) ^ τ' * Ms ^ ((1 : ℝ) / 2) := by
  have hL1 : 1 ≤ L := by omega
  have hN1 := ppc_one_le_N hL1 hW
  have hN0 : 0 < nPPN L W := by linarith
  obtain ⟨hw1, hwΓ, hΓ1⟩ := ppc_w_facts hL1 hW hε
  obtain ⟨hCU0, -, hc2, hLg1, hLgle⟩ := ppc_const_facts hL hW hE hA0 hμ hμE
  have hlog0 : 0 ≤ Real.log (nPPN L W) := Real.log_nonneg hN1
  set N := nPPN L W with hNdef
  set P := 1 + Real.log N with hPdef
  have hP1 : 1 ≤ P := by linarith
  set Γ := N ^ ε with hΓdef
  set Lg := LgPPN E N with hLgdef
  have hΓ0 : 0 ≤ Γ := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hR5' : 0 ≤ R ^ 5 := by positivity
  have hLg0 : 0 ≤ Lg := by linarith
  have hC : 1 + R ^ 4 + R ^ 5 ≤ 3 * R ^ 5 := by
    have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
    have h0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
    linarith
  have hΓ3 : Γ ^ 3 * N ^ (5 * ε) ≤ N ^ τ' := by
    have e : Γ ^ 3 * N ^ (5 * ε) = N ^ (8 * ε) := by
      rw [hΓdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hτ'
  have hMh : Ms ^ ((1 : ℝ) / 12) ≤ Ms ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hMs (by norm_num)
  have hQ0 : 0 ≤ (120000 * (1 + A0) ^ 2 / μ) * P ^ 3 := by positivity
  have hstep : 2 * cPrimePPN (CUN A0 L) Γ R Lg ≤
      ((120000 * (1 + A0) ^ 2 / μ) * P ^ 3) * Γ ^ 3 * R ^ 5 := by
    have e1 : 2 * cPrimePPN (CUN A0 L) Γ R Lg =
        20000 * (CUN A0 L ^ 2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg := by
      unfold cPrimePPN C0PPN; ring
    have e2 : 20000 * (2 * ((1 + A0) * P) ^ 2) * Γ ^ 3 * (3 * R ^ 5) * (μ⁻¹ * P) =
        ((120000 * (1 + A0) ^ 2 / μ) * P ^ 3) * Γ ^ 3 * R ^ 5 := by
      field_simp; ring
    rw [e1]
    calc 20000 * (CUN A0 L ^ 2 + 1) * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg
        ≤ 20000 * (2 * ((1 + A0) * P) ^ 2) * Γ ^ 3 * (3 * R ^ 5) * (μ⁻¹ * P) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hc2 (by norm_num))
            le_rfl (by positivity) (by positivity)) hC (by positivity) (by positivity)
            |> fun h => mul_le_mul h hLgle hLg0 (by positivity)
      _ = _ := e2
  calc 2 * cPrimePPN (CUN A0 L) Γ R Lg
      ≤ ((120000 * (1 + A0) ^ 2 / μ) * P ^ 3) * Γ ^ 3 * R ^ 5 := hstep
    _ ≤ N ^ (5 * ε) * Γ ^ 3 * R ^ 5 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hΓ0 3)) hR5'
    _ = (Γ ^ 3 * N ^ (5 * ε)) * R ^ 5 := by ring
    _ ≤ N ^ τ' * Ms ^ ((1 : ℝ) / 2) :=
        mul_le_mul hΓ3 (hR5.trans hMh) hR5' (Real.rpow_nonneg hN0.le _)

end Arith

/-! ## 5. The three statements -/

section Pins

variable (d : Sizes)

/-- **`PPDriftSumN`**: the drift sum
`M_k² Δ Σ_{j<k} CU² d_j ≤ c'/4 + C_q m² Lg / M_v` along the grid `[s,v]`. -/
theorem ppDriftSumN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) :
    PPDriftSumN d κ c τ E s v t K := by
  intro hM hsv hvt hK0 ε hε C_K hCK hKN A0 hA0
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hbw, hcond, hrange, -, -, -⟩ := hM
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hrangeV : RangeCond d τ v := hrange.mono fun n hn => hn.trans (by linarith [hvt n])
  filter_upwards [sum_gridStep_div_etaT_le hτ hE2 hs0 hsv hv1 hK0 hrangeV, hbw] with n hsum hbwn
  intro J hJ0 k hk m hm0 hJm
  have hΔ := GoodEvent_gridStep_nonneg (K := K) (hsv n)
  have hkΔ : (k : ℝ) * gridStep s v K n ≤ 1 := by
    have h1 := GoodEvent_gridTime_le (K := K) (hsv n) hk
    have h2 : gridTime s v K n k = s n + k * gridStep s v K n := rfl
    linarith [hs0 n, hv1 n]
  exact ppc_drift_sum (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n) (hE2 n) hc hε hbwn
    (CU := CUN A0 (d.L n)) (R := RPPN d s v n)
    (le_trans zero_le_one (ppc_R_ge_one (d.three_le_L n |> fun h => by omega) (hs0 n) (hsv n) (hv1 n)))
    hk hΔ (fun i j h => GoodEvent_gridTime_mono (K := K) (hsv n) h)
    (fun j hj => GoodEvent_gridTime_le (K := K) (hsv n) hj) (hv1 n) hkΔ hsum hJ0 hm0 hJm

/-- **`PPQVSumN`**: the Azuma term
`M_k² N^ε (Σ_{j<k} c_j)^{1/2} ≤ c'/4`. -/
theorem ppQVSumN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) :
    PPQVSumN d κ c τ E s v t K := by
  intro hM hsv hvt hK0 ε hε C_K hCK hKN A0 hA0
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hbw, hcond, hrange, -, -, -⟩ := hM
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hrangeV : RangeCond d τ v := hrange.mono fun n hn => hn.trans (by linarith [hvt n])
  filter_upwards [sum_gridStep_div_etaT_le hτ hE2 hs0 hsv hv1 hK0 hrangeV, hbw, hrange, hKN]
    with n hsum hbwn hrn hKn
  intro k hk
  have hΔ := GoodEvent_gridStep_nonneg (K := K) (hsv n)
  have hkΔ : (k : ℝ) * gridStep s v K n ≤ 1 := by
    have h1 := GoodEvent_gridTime_le (K := K) (hsv n) hk
    have h2 : gridTime s v K n k = s n + k * gridStep s v K n := rfl
    linarith [hs0 n, hv1 n]
  have hΔK : gridStep s v K n ≤ (K n : ℝ)⁻¹ := by
    unfold gridStep
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 (Nat.cast_nonneg _)) (by linarith [hs0 n, hv1 n])
  have hku : gridTime s v K n k ≤ v n := GoodEvent_gridTime_le (K := K) (hsv n) hk
  have hlast : gridStep s v K n / etaT (E n) (gridTime s v K n k) ≤
      (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) :=
    ppc_last (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n) (hE2 n) hτ (by linarith)
      hKn hΔ hΔK (hku.trans_lt (hv1 n)) (hrn.trans (by linarith [hvt n]))
  exact ppc_qv_sum (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n) (hE2 n) hc hε hbwn
    (CU := CUN A0 (d.L n)) (R := RPPN d s v n)
    (le_trans zero_le_one (ppc_R_ge_one (by have := d.three_le_L n; omega) (hs0 n) (hsv n) (hv1 n)))
    (hK0 n) hk hΔ (fun i j h => GoodEvent_gridTime_mono (K := K) (hsv n) h)
    (fun j hj => GoodEvent_gridTime_le (K := K) (hsv n) hj) (hv1 n) hkΔ hsum hlast

/-- **`PPArithN`**: (i) `1 ≤ M_v`; (ii) the forbidden zone
`4 C_q c' Lg ≤ M_v` for `ε ≤ min(2c, τ)/8`; (iii) the output `2 c' ≤ N^{τ'} M_s^{1/2}` for
`8ε ≤ τ'`. -/
theorem ppArithN (κ c τ : ℝ) (E s t : ℕ → ℝ) : PPArithN d κ c τ E s t := by
  intro hM v hsv hvt A0 hA0
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hbw, hcond, hrange, -, -, -⟩ := hM
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hL1 : ∀ n, 1 ≤ d.L n := fun n => by have := d.three_le_L n; omega
  have hm0 : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  have hμ : 0 < Real.sqrt (2 * κ) / 2 := by
    have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
    linarith
  have hμE : ∀ n, Real.sqrt (2 * κ) / 2 ≤ (spectralM (E n)).im :=
    fun n => MLExpVocab_im_ge hκ (hE n)
  -- `μ N^{m₀} ≤ M_v`
  have hMt : ∀ᶠ n : ℕ in atTop, Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤
      scaleM (d.L n) (d.W n) (E n) (v n) := by
    filter_upwards [hbw, hrange] with n hbwn hrn
    have h1 := (scaleM_etaT_of_range (hL1 n) (d.W_pos n) (hE2 n) hc hτ (ht1 n) hbwn hrn).1
    have h2 : scaleM (d.L n) (d.W n) (E n) (t n) ≤ scaleM (d.L n) (d.W n) (E n) (v n) :=
      (scaleM_anti_ratio (hL1 n) (hE2 n) (hvt n) (ht1 n)).1
    have h3 : Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤
        (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) :=
      mul_le_mul_of_nonneg_right (hμE n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact h3.trans (h1.trans h2)
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    have hlim : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ)) atTop atTop :=
      (tendsto_rpow_atTop hm0).comp hsize
    filter_upwards [hMt, hlim.eventually_ge_atTop (Real.sqrt (2 * κ) / 2)⁻¹] with n hn hn2
    have : 1 ≤ Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) := by
      calc (1 : ℝ) = Real.sqrt (2 * κ) / 2 * (Real.sqrt (2 * κ) / 2)⁻¹ := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hn2 hμ.le
    exact this.trans hn
  · -- (ii)
    intro ε hε hεm
    have hδ : 0 < (12 / 29 : ℝ) * min (2 * c) τ := by positivity
    filter_upwards [hMt, hcond, hsize.eventually (ppc_polylog_le'
      (480000000 * (1 + A0) ^ 4 / (Real.sqrt (2 * κ) / 2) ^ 2)
      ((Real.sqrt (2 * κ) / 2) ^ ((1 : ℝ) / 2 + 12 / 29)) ((12 / 29 : ℝ) * min (2 * c) τ) 6
      (Real.rpow_pos_of_pos hμ _) hδ)] with n hn hcn hpn
    obtain ⟨hR1, hR5v, -, -⟩ := ppc_R_facts (hL1 n) (d.W_pos n) (hE2 n) (hs0 n) (hsv n) (hvt n)
      (ht1 n) hcn
    exact ppc_zone_n (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n) (hE2 n) hε
      (by linarith) hA0 hμ (hμE n) hR1 hR5v hn hpn
  · -- (iii)
    intro ε hε τ' hτ'
    have hδ : 0 < 5 * ε := by linarith
    filter_upwards [hcond, hsize.eventually (ppc_polylog_le'
      (120000 * (1 + A0) ^ 2 / (Real.sqrt (2 * κ) / 2)) 1 (5 * ε) 3 one_pos hδ)] with n hcn hpn
    obtain ⟨hR1, -, hR5s, hMs⟩ := ppc_R_facts (hL1 n) (d.W_pos n) (hE2 n) (hs0 n) (hsv n) (hvt n)
      (ht1 n) hcn
    exact ppc_out_n (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n) (hE2 n) hε hτ' hA0 hμ
      (hμE n) hR1 hR5s hMs (by rw [one_mul] at hpn; exact hpn)

end Pins

end RBM.Ind

end
