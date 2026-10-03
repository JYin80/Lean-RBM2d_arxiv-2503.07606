/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEnd

/-!
# The budget hypothesis `BudgetAlt` of the alternating endpoint

This file proves `BudgetAlt` of `RBM2D.Induction.AltEnd` (`theorem budgetAlt : BudgetAlt d`): at a
fixed size index `n`, `assembledRHSAlt ≤ (9/10) N^{ε₀} (Λ^{1/2} + Φ) M_v^{-k}` from the regime
facts, the two inputs `hlog`, `hR` and the absorptions `AltBudgetHyp`.

Method: the eight terms of `assembledRHSAlt` are bounded against the thirteen fields of
`AltBudgetHyp`, as `budgetNonAlt` (`RBM2D.Induction.NonAltBudget`) does for `assembledRHSNonAlt`,
using the term bounds `tbInitQPart`, `tbDriftQPart` (`RBM2D.Induction.AltBudgetTerms`) and `tbQv`
(`RBM2D.Induction.NonAltBudget`) and a private drift budget `AltBudget_tbDriftEPart` without the
unused premise `1 ≤ K_w`.  Five main terms are absorbed into `N^{ε₀}/10` and eight far terms into
`N^{ε₀}/20` (`5/10 + 8/20 = 9/10`, after `M_v^{-k} ≤ Λ^{1/2} M_v^{-k}`); the argument parallels the
one-dimensional formalization.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Elementary facts (private copies of the private helpers of `NonAltBudget`, `AltBudgetTerms`) -/

section Basic

private theorem AltBudget_im_le_one {E : ℝ} (hE : |E| < 2) : (spectralM E).im ≤ 1 := by
  have := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE.le] at this
  exact (le_abs_self _).trans this

private theorem AltBudget_etaT_le_one {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) :
    etaT E u ≤ 1 := by
  unfold etaT
  have hm := AltBudget_im_le_one hE
  have hm0 := (spectralM_im_pos hE).le
  nlinarith

private theorem AltBudget_scaleM_le {L W : ℕ} [NeZero L] {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : scaleM L W E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl := ellT_pos_le hLp hu1
  have hη0 := etaT_pos hE hu1
  have hη1 := AltBudget_etaT_le_one hE hu0
  unfold scaleM
  have h1 : ellT L u ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hl.1.le hl.2 2
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := sq_nonneg _
  calc (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hW2) hη1 hη0.le (by positivity)
    _ = _ := mul_one _

private theorem AltBudget_size_eq (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
  rw [Sizes.size_eq]; push_cast; ring

private theorem AltBudget_scaleM_le_size {E u : ℝ} (n : ℕ) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    scaleM (d.L n) (d.W n) E u ≤ ((d.size n : ℕ) : ℝ) := by
  rw [AltBudget_size_eq d n]; exact AltBudget_scaleM_le hE hu0 hu1

private theorem AltBudget_inv_one_sub_le {E v Nn : ℝ} (hE : |E| < 2) (hv1 : v < 1)
    (hη : (etaT E v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn := by
  have hm := AltBudget_im_le_one hE
  have hm0 := spectralM_im_pos hE
  have h1 : 0 < 1 - v := by linarith
  have heq : (1 - v)⁻¹ = (spectralM E).im * (etaT E v)⁻¹ := by
    unfold etaT
    field_simp
  rw [heq]
  have h0 : 0 ≤ (etaT E v)⁻¹ := by
    have := etaT_pos hE hv1
    positivity
  nlinarith

private theorem AltBudget_sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) :
    ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K := by
  have h := Finset.sum_range_succ' f K
  have h2 := Finset.sum_range_succ f K
  linarith

private theorem AltBudget_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The absorption step of a far part: `y N_p ≤ B`, `N_p^{-1} ≤ X`, `B ≥ 0` give `y ≤ B X`. -/
private theorem AltBudget_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

private theorem AltBudget_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK1 : 1 ≤ K n) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

private theorem AltBudget_cCase4_nonneg (k : ℕ) : 0 ≤ cCase4 k := by
  unfold cCase4 cProp5
  positivity

private theorem AltBudget_cCase5_nonneg (k : ℕ) : 0 ≤ cCase5 k := by
  unfold cCase5
  exact (even_two_mul k).pow_nonneg _

private theorem AltBudget_ratioR_eq_rhoR {L : ℕ} {E s t : ℝ} (hE : |E| < 2) :
    ratioR L E s t = rhoR L s t := by
  have hI : (RBM.Gauss.spectralM E).im ≠ 0 := (RBM.Gauss.spectralM_im_pos hE).ne'
  unfold ratioR rhoR etaT
  rw [← mul_assoc, ← mul_assoc]
  exact mul_div_mul_right _ _ hI

private theorem AltBudget_ratioR_eq_div {L W : ℕ} [NeZero W] (E s t : ℝ) :
    ratioR L E s t = scaleM L W E s / scaleM L W E t :=
  MLExpVocab_ratioR_eq (Nat.pos_of_ne_zero (NeZero.ne W)) E s t

private theorem AltBudget_scaleM_pos {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) : 0 < scaleM L W E u :=
  scaleM_pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (Nat.one_le_iff_ne_zero.2 (NeZero.ne W)) hE hu

private theorem AltBudget_ratioR_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E s t : ℝ}
    (hE : |E| < 2) (hs : s < 1) (ht : t < 1) : 0 ≤ ratioR L E s t := by
  rw [AltBudget_ratioR_eq_div (W := W)]
  exact div_nonneg (AltBudget_scaleM_pos hE hs).le (AltBudget_scaleM_pos hE ht).le

private theorem AltBudget_ratioR_le {L W : ℕ} [NeZero L] [NeZero W] {E s t Nn : ℝ}
    (hE : |E| < 2) (hs : s < 1) (hMs : scaleM L W E s ≤ Nn) (hMt : 1 ≤ scaleM L W E t) :
    ratioR L E s t ≤ Nn := by
  rw [AltBudget_ratioR_eq_div (W := W)]
  exact (div_le_self (AltBudget_scaleM_pos hE hs).le hMt).trans hMs

private theorem AltBudget_C4_nonneg (L k : ℕ) [NeZero L] (Kw : ℝ) :
    0 ≤ cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) := by
  have h1 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have h2 : 0 ≤ Kw ^ (2 * k) := by rw [pow_mul]; positivity
  have := AltBudget_cCase4_nonneg k
  positivity

end Basic

/-! ## 2. The `𝔼`-part drift budget without the premise `1 ≤ K_w` -/

/-- The `𝔼`-part drift budget (the generic `tbDrift` with the weights `kapQ4`, `epsQ4`), without a
premise `1 ≤ Kw`, which the proof never uses: `K_w = W^{τ'}` may be `< 1`. -/
private theorem AltBudget_tbDriftEPart (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ) (E : ℝ)
    (hE : |E| < 2) (u : ℕ → ℝ) (K : ℕ) (Kw Δ a b δmax Nn : ℝ) (hu0 : ∀ i ≤ K, 0 ≤ u i)
    (hu1 : ∀ i ≤ K, u i < 1) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m)
    (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδmax : 0 ≤ δmax)
    (hM1 : ∀ i ≤ K, 1 ≤ scaleM L W E (u i)) (hMN : ∀ i ≤ K, scaleM L W E (u i) ≤ Nn)
    (hNn : (1 - u K)⁻¹ ≤ Nn) (X δ : ℕ → ℝ)
    (hX : ∀ j < K, X j ≤ a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b)
    (hδ0 : ∀ j < K, 0 ≤ δ j) (hδ : ∀ j < K, δ j ≤ δmax) :
    Δ * ∑ j ∈ Finset.range K, (kapQ4 L k Kw (u j) (u K) * X j + epsQ4 L k (u j) (u K) * δ j) ≤
      cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * a * (scaleM L W E (u K) ^ k)⁻¹ *
          ∑ j ∈ Finset.range K, Δ / etaT E (u j) +
        ((K : ℝ) * Δ) * (cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * Nn ^ k * b +
          cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * Nn ^ k * δmax) := by
  have hC4 := AltBudget_C4_nonneg L k Kw
  have h1L : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hc4 := AltBudget_cCase4_nonneg k
  have h :=
    tbDrift (L := L) (W := W) (E := E) (k := k) (K := K) (Δ := Δ)
      (Cκ := cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k))
      (Cε := cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * Nn ^ k)
      (Cfar := cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * Nn ^ k)
      (a := a) (b := b) (δmax := δmax) u
      (fun i m => kapQ4 L k Kw (u (i - 1)) (u m)) (fun i m => epsQ4 L k (u (i - 1)) (u m))
      X δ hΔ ha hb
      (fun j hj => by
        simp only [Nat.add_sub_cancel]
        unfold kapQ4
        exact mul_nonneg hC4 (pow_nonneg (by
          rw [← AltBudget_ratioR_eq_rhoR hE]
          exact AltBudget_ratioR_nonneg (L := L) (W := W) hE (hu1 j hj.le) (hu1 K le_rfl)) k))
      (fun j hj => by
        simp only [Nat.add_sub_cancel]
        unfold epsQ4
        have h1j : 0 < 1 - u j := by linarith [hu1 j hj.le]
        have h1K : 0 < 1 - u K := by linarith [hu1 K le_rfl]
        positivity)
      (fun j hj => by
        simp only [Nat.add_sub_cancel]
        exact (kapQ4_mul_scale_pow_eq L W k Kw E (u j) (u K) hE (hu1 j hj.le)
          (hu1 K le_rfl)).le)
      (fun j hj => by
        simp only [Nat.add_sub_cancel]
        unfold kapQ4
        have hR0 := AltBudget_ratioR_nonneg (L := L) (W := W) hE (hu1 j hj.le) (hu1 K le_rfl)
        have hRN := AltBudget_ratioR_le (L := L) (W := W) hE (hu1 j hj.le) (hMN j hj.le)
          (hM1 K le_rfl)
        rw [← AltBudget_ratioR_eq_rhoR hE]
        have := pow_le_pow_left₀ hR0 hRN k
        exact mul_le_mul_of_nonneg_left this hC4)
      (fun j hj => by
        simp only [Nat.add_sub_cancel]
        unfold epsQ4
        have h1j : 0 < 1 - u j := by linarith [hu1 j hj.le]
        have h1K : 0 < 1 - u K := by linarith [hu1 K le_rfl]
        have hle : (1 - u j) / (1 - u K) ≤ Nn := by
          calc (1 - u j) / (1 - u K) ≤ 1 / (1 - u K) :=
                div_le_div_of_nonneg_right (by linarith [hu0 j hj.le]) h1K.le
            _ = (1 - u K)⁻¹ := one_div _
            _ ≤ Nn := hNn
        have hq0 : 0 ≤ (1 - u j) / (1 - u K) := by positivity
        have := pow_le_pow_left₀ hq0 hle k
        have e : cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - u j) / (1 - u K)) ^ k ≤
            cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * Nn ^ k :=
          mul_le_mul_of_nonneg_left this (by positivity)
        exact e)
      hX hδ0 hδ
      (fun j hj => etaT_pos hE (hu1 j hj.le))
  simp only [Nat.add_sub_cancel] at h
  exact h

/-! ## 3. Bounds of the Case 4 weights, nonnegativity of the variance shape, the proxy as a real -/

section Weights

private theorem AltBudget_kapQ4_bounds {L W : ℕ} [NeZero L] [NeZero W] {E s t Nn : ℝ} (k : ℕ)
    (τ' : ℝ) (hE : |E| < 2) (hs : s < 1) (ht : t < 1) (hMs : scaleM L W E s ≤ Nn)
    (hMt : 1 ≤ scaleM L W E t) :
    0 ≤ kapQ4 L k ((W : ℝ) ^ τ') s t ∧ kapQ4 L k ((W : ℝ) ^ τ') s t ≤ altC4 L W k τ' * Nn ^ k := by
  have hC4 : 0 ≤ altC4 L W k τ' := AltBudget_C4_nonneg L k ((W : ℝ) ^ τ')
  have hR0 := AltBudget_ratioR_nonneg (L := L) (W := W) hE hs ht
  have hRN := AltBudget_ratioR_le (L := L) (W := W) hE hs hMs hMt
  rw [AltBudget_ratioR_eq_rhoR hE] at hR0 hRN
  have hpow := pow_le_pow_left₀ hR0 hRN k
  unfold kapQ4
  exact ⟨mul_nonneg hC4 (pow_nonneg hR0 k), mul_le_mul_of_nonneg_left hpow hC4⟩

private theorem AltBudget_epsQ4_bounds {L : ℕ} [NeZero L] {s t Nn : ℝ} (k : ℕ) (hs0 : 0 ≤ s)
    (hs : s < 1) (ht : t < 1) (hN : (1 - t)⁻¹ ≤ Nn) :
    0 ≤ epsQ4 L k s t ∧ epsQ4 L k s t ≤ altC4e L k * Nn ^ k := by
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  have h1L : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hc4 := AltBudget_cCase4_nonneg k
  have hle : (1 - s) / (1 - t) ≤ Nn := by
    calc (1 - s) / (1 - t) ≤ 1 / (1 - t) :=
          div_le_div_of_nonneg_right (by linarith) h1t.le
      _ = (1 - t)⁻¹ := one_div _
      _ ≤ Nn := hN
  have hq0 : 0 ≤ (1 - s) / (1 - t) := by positivity
  have hpow := pow_le_pow_left₀ hq0 hle k
  unfold epsQ4 altC4e
  exact ⟨by positivity, mul_le_mul_of_nonneg_left hpow (by positivity)⟩

private theorem AltBudget_qvShape_nonneg {L W : ℕ} {E : ℝ} (k : ℕ) {A B G Wd u w : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hWd : 0 ≤ Wd) (hη : 0 ≤ etaT E u) :
    0 ≤ NonAltBudget_qvShape L W E k A B G Wd u w := by
  unfold NonAltBudget_qvShape
  have h1 : 0 ≤ rhoR L u w ^ (2 * k) := (even_two_mul k).pow_nonneg _
  have h2 : 0 ≤ ((1 - u) / (1 - w)) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  have h3 : 0 ≤ (scaleM L W E u ^ (2 * k))⁻¹ := inv_nonneg.2 ((even_two_mul k).pow_nonneg _)
  have h4 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη
  positivity

/-- The proxy `cQVAlt` as a real number: `Δ k NonAltBudget_qvShape(u_{j+1}, u_m)` (it is `≥ 0`). -/
private theorem AltBudget_cQVAlt_coe {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ)
    (𝔠 τ' Dq C' G Mmax : ℝ) (m : ℕ) (a : Fin k → Z2 (d.L n)) (j : ℕ)
    (hnn : 0 ≤ gridStep s v K n * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
      (altQvA (d.L n) (d.W n) k 𝔠 τ') (altQvB (d.L n) k Mmax) G ((d.W n : ℝ) ^ (-Dq + C'))
      (gridTime s v K n (j + 1)) (gridTime s v K n m))) :
    (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax m a j : ℝ) =
      gridStep s v K n * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
        (altQvA (d.L n) (d.W n) k 𝔠 τ') (altQvB (d.L n) k Mmax) G ((d.W n : ℝ) ^ (-Dq + C'))
        (gridTime s v K n (j + 1)) (gridTime s v K n m)) := by
  unfold cQVAlt
  exact Real.coe_toNNReal _ hnn

end Weights

/-! ## 4. The budget `budgetAlt` -/

section Budget

/-- **The budget hypothesis `BudgetAlt`** holds (the analogue of `budgetNonAlt`): at a fixed size
index `n`, `assembledRHSAlt ≤ (9/10) N^{ε₀} (Λ^{1/2} + Φ) M_v^{-k}` under the regime facts, the two
inputs `hlog`, `hR` and the absorptions `AltBudgetHyp`.  Terms: 1 `tbInitQPart`; 2 `tbDriftQPart`;
3 `altShiftTerm` (`he3`); 4 `kapQ4_mul_scale_pow_eq`; 5 `AltBudget_tbDriftEPart`; 6 `tbQv` and the
`sqrt` split; 7 `he7`; 8 `hR` and `he8`.  Five main terms `≤ N^{ε₀}/10`, eight far terms
`≤ N^{ε₀}/20`; `5/10 + 8/20 = 9/10`. -/
theorem budgetAlt : BudgetAlt d := by
  intro E s v K n k _ hk 𝔠 τ' Dq C' Db εq εE ε ε₀ D_Y D_t τK Γ Λ Φ a hE hs0 hsv hv1 hK1 hM1 hη hΔN
    hΛ hΦ hΓ hlog hR hhyp
  obtain ⟨ha1, ha2, ha3, ha4, ha5, he1, he2, he3, he4, he5, he6, he7, he8⟩ := hhyp
  have hLp : 1 ≤ d.L n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hWp : 1 ≤ d.W n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size (d := d) n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hs1 : s n < 1 := hsv.trans_lt hv1
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => GoodEvent_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) hsv hi).trans_lt hv1
  have huK : gridTime s v K n (K n) = v n := gridTime_last s v K n (by omega)
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    GoodEvent_gridTime_mono hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    rw [AltBudget_K_mul_step hK1]; linarith
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hMv0 := scaleM_pos hLp hWp hE hv1
  have hMvN := AltBudget_scaleM_le_size d n hE (hs0.trans hsv) hv1
  have hN1' : (1 - v n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := AltBudget_inv_one_sub_le hE hv1 hη
  have hMN : ∀ i ≤ K n, scaleM (d.L n) (d.W n) (E n) (gridTime s v K n i) ≤
      ((d.size n : ℕ) : ℝ) := fun i hi => AltBudget_scaleM_le_size d n hE (hu0 i) (hu1 i hi)
  have hMi1 : ∀ i ≤ K n, 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n i) := by
    intro i hi
    have h := (scaleM_anti_ratio (L := d.L n) (W := d.W n) hLp hE (hmono i (K n) hi)
      (hu1 (K n) le_rfl)).1
    rw [huK] at h
    linarith
  have hMKv : 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) := by rw [huK]; exact hM1
  have hu1K : (1 - gridTime s v K n (K n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by rw [huK]; exact hN1'
  have hWb0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWq0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWd0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-Dq + C') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hNq : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
  have hNE : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ εE := Real.rpow_nonneg hN0.le _
  have hNe : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ ε := Real.rpow_nonneg hN0.le _
  have hC4 : 0 ≤ altC4 (d.L n) (d.W n) k τ' := AltBudget_C4_nonneg (d.L n) k _
  have hlogL : 0 ≤ Real.log (d.L n : ℝ) := Real.log_natCast_nonneg _
  have hC4e : 0 ≤ altC4e (d.L n) k := by
    have := AltBudget_cCase4_nonneg k
    unfold altC4e
    positivity
  have hLs0 : 0 ≤ (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (spectralM_im_pos hE).le) (Real.log_nonneg hN1)
  have hηv0 := etaT_pos hE hv1
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Δ := gridStep s v K n with hΔdef
  set X := (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k with hXdef
  set Ls := (spectralM (E n)).im⁻¹ * Real.log N with hLsdef
  have hNk : (0 : ℝ) < N ^ k := pow_pos hN0 k
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ := inv_nonneg.2 hMv0.le
    positivity
  have hXk : (scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹ = X := by rw [hXdef, inv_pow]
  have hXK : (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) ^ k)⁻¹ = X := by
    rw [huK]; exact hXk
  have hXN : (N ^ k)⁻¹ ≤ X := by
    rw [hXdef, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) (inv_anti₀ hMv0 hMvN) k
  have hX1 : X ≤ 1 := by
    rw [hXdef]
    exact pow_le_one₀ (inv_nonneg.2 hMv0.le) (inv_le_one_of_one_le₀ hM1)
  set P0 := N ^ ε₀ with hP0def
  set Λr := Λ n ^ ((1 : ℝ) / 2) with hΛrdef
  have hΛr1 : 1 ≤ Λr := Real.one_le_rpow hΛ (by norm_num)
  have hP20 : 0 ≤ P0 / 20 := by positivity
  -- T1: the `ℚ` initial term
  have T1 : N ^ εq * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db *
        ratioR (d.L n) (E n) (s n) (gridTime s v K n (K n)) ^ k + (d.W n : ℝ) ^ (-Db) ≤
      P0 / 10 * X + P0 / 20 * X := by
    have hMs0 := scaleM_pos hLp hWp hE hs1
    have hMsN := AltBudget_scaleM_le_size d n hE hs0 hs1
    have hMk : 0 < scaleM (d.L n) (d.W n) (E n) (s n) ^ k := pow_pos hMs0 k
    have hpow : scaleM (d.L n) (d.W n) (E n) (s n) ^ k ≤ N ^ k :=
      pow_le_pow_left₀ hMs0.le hMsN k
    have hfar : (d.W n : ℝ) ^ (-Db) ≤
        N ^ k * (d.W n : ℝ) ^ (-Db) * (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hMk]
      linarith [mul_le_mul_of_nonneg_right hpow hWb0]
    have hΛ0' : altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db ≤
        ((d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') + N ^ k * (d.W n : ℝ) ^ (-Db)) *
          (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹ := by
      unfold altQ0Level
      linarith [hfar]
    have h := tbInitQPart (d.L n) (d.W n) k (E n) (s n) (gridTime s v K n (K n)) hE hs1
      (hu1 _ le_rfl) (N ^ εq) ((d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') + N ^ k * (d.W n : ℝ) ^ (-Db))
      (altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db) ((d.W n : ℝ) ^ (-Db)) hNq hΛ0'
    rw [hXK] at h
    refine h.trans ?_
    have m1 : N ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * X ≤ P0 / 10 * X :=
      mul_le_mul_of_nonneg_right ha1 hX0
    have m2 : N ^ εq * N ^ k * (d.W n : ℝ) ^ (-Db) * X ≤ N ^ εq * N ^ k * (d.W n : ℝ) ^ (-Db) :=
      mul_le_of_le_one_right (by positivity) hX1
    have m3 : (N ^ εq * N ^ k + 1) * (d.W n : ℝ) ^ (-Db) ≤ P0 / 20 * X := by
      refine AltBudget_absorb hNk hP20 ?_ hXN
      exact (mul_comm _ _).le.trans he1
    linarith [m1, m2, m3]
  -- T2: the `ℚ` drift
  have T2 : Δ * ∑ j ∈ Finset.range (K n),
      (N ^ εq * (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (gridTime s v K n j)) *
        ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
        (d.W n : ℝ) ^ (-Db)) ≤ P0 / 10 * (Φ n * X) + P0 / 20 * X := by
    have h := tbDriftQPart (d.L n) (d.W n) k (E n) hE (gridTime s v K n) (K n) Δ (N ^ εq)
      (5 * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) (5 * (d.W n : ℝ) ^ (-Db))
      ((d.W n : ℝ) ^ (-Db)) N hu1 hΔ0 hNq (by positivity) (by positivity) hWb0 hMi1 hMN
      (fun j => 5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (gridTime s v K n j))
      (fun j hj => by
        have h1 := scaleM_pos hLp hWp hE (hu1 j hj.le)
        have h2 := etaT_pos hE (hu1 j hj.le)
        unfold altQLevel
        positivity)
      (fun j hj => le_of_eq (by unfold altQLevel; ring))
    rw [hXK] at h
    refine h.trans ?_
    have hcoef : 0 ≤ N ^ εq * (5 * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X := by
      positivity
    have m1 : N ^ εq * (5 * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X *
        ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n j) ≤
        N ^ εq * (5 * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X * Ls :=
      mul_le_mul_of_nonneg_left hlog hcoef
    have m2 : N ^ εq * (5 * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X * Ls =
        (5 * (N ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * Ls) * (Φ n * X) := by ring
    have m3 : (5 * (N ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * Ls) * (Φ n * X) ≤
        P0 / 10 * (Φ n * X) := mul_le_mul_of_nonneg_right ha2 (mul_nonneg hΦ hX0)
    have hq : 0 ≤ N ^ εq * N ^ k * (5 * (d.W n : ℝ) ^ (-Db)) + (d.W n : ℝ) ^ (-Db) := by positivity
    have f1 : ((K n : ℝ) * Δ) * (N ^ εq * N ^ k * (5 * (d.W n : ℝ) ^ (-Db)) +
        (d.W n : ℝ) ^ (-Db)) ≤ (5 * (N ^ εq * N ^ k) + 1) * (d.W n : ℝ) ^ (-Db) := by
      have := mul_le_mul_of_nonneg_right hKΔ1 hq
      linarith
    have f2 : (5 * (N ^ εq * N ^ k) + 1) * (d.W n : ℝ) ^ (-Db) ≤ P0 / 20 * X := by
      refine AltBudget_absorb hNk hP20 ?_ hXN
      exact (mul_comm _ _).le.trans he2
    linarith
  -- T3: the kernel-start shift
  have T3 : altShiftTerm s v K n k N ≤ P0 / 20 * X := by
    refine AltBudget_absorb hNk hP20 ?_ hXN
    exact (mul_comm _ _).le.trans he3
  -- T4: the `𝔼` initial term
  have T4 : kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n 0) (gridTime s v K n (K n)) *
        altE0Level d n E s k τ' Db εE +
      epsQ4 (d.L n) k (gridTime s v K n 0) (gridTime s v K n (K n)) * altEDecay d n Db εE ≤
      P0 / 10 * X + P0 / 20 * X := by
    rw [GoodEvent_gridTime_zero]
    have hMsN := AltBudget_scaleM_le_size d n hE hs0 hs1
    have hid : kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (s n) (gridTime s v K n (K n)) *
        (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹ =
        altC4 (d.L n) (d.W n) k τ' * (scaleM (d.L n) (d.W n) (E n)
          (gridTime s v K n (K n)) ^ k)⁻¹ :=
      kapQ4_mul_scale_pow_eq (d.L n) (d.W n) k ((d.W n : ℝ) ^ τ') (E n) (s n)
        (gridTime s v K n (K n)) hE hs1 (hu1 _ le_rfl)
    rw [hXK] at hid
    obtain ⟨hk0, hk1⟩ := AltBudget_kapQ4_bounds (L := d.L n) (W := d.W n) (E := E n) k τ' hE hs1
      (hu1 _ le_rfl) hMsN hMKv
    obtain ⟨hε0, hε1⟩ := AltBudget_epsQ4_bounds (L := d.L n) (Nn := N) k hs0 hs1 (hu1 _ le_rfl) hu1K
    have e1 : kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (s n) (gridTime s v K n (K n)) *
        altE0Level d n E s k τ' Db εE +
        epsQ4 (d.L n) k (s n) (gridTime s v K n (K n)) * altEDecay d n Db εE =
        (altC4 (d.L n) (d.W n) k τ' * (N ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ'))) * X +
          (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (s n) (gridTime s v K n (K n)) *
              (N ^ εE * (d.W n : ℝ) ^ (-Db)) +
            epsQ4 (d.L n) k (s n) (gridTime s v K n (K n)) * (N ^ εE * (d.W n : ℝ) ^ (-Db))) := by
      unfold altE0Level altQ0Level altEDecay
      linear_combination (N ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * hid
    rw [e1]
    have m1 : (altC4 (d.L n) (d.W n) k τ' * (N ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ'))) * X ≤
        P0 / 10 * X := mul_le_mul_of_nonneg_right ha3 hX0
    have hδ0 : 0 ≤ N ^ εE * (d.W n : ℝ) ^ (-Db) := by positivity
    have m2 : kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (s n) (gridTime s v K n (K n)) *
          (N ^ εE * (d.W n : ℝ) ^ (-Db)) +
        epsQ4 (d.L n) k (s n) (gridTime s v K n (K n)) * (N ^ εE * (d.W n : ℝ) ^ (-Db)) ≤
        (altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) * N ^ k * (N ^ εE * (d.W n : ℝ) ^ (-Db)) := by
      have := mul_le_mul_of_nonneg_right hk1 hδ0
      have := mul_le_mul_of_nonneg_right hε1 hδ0
      linarith
    have m3 : (altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) * N ^ k *
        (N ^ εE * (d.W n : ℝ) ^ (-Db)) ≤ P0 / 20 * X := by
      refine AltBudget_absorb hNk hP20 ?_ hXN
      exact (mul_comm _ _).le.trans he4
    linarith
  -- T5: the `𝔼` drift
  have T5 : Δ * ∑ j ∈ Finset.range (K n),
      (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n j) (gridTime s v K n (K n)) *
          altELevel d n E k τ' Db εE (Φ n) (gridTime s v K n j) +
        epsQ4 (d.L n) k (gridTime s v K n j) (gridTime s v K n (K n)) *
          altEDecay d n Db εE) ≤ P0 / 10 * (Φ n * X) + P0 / 20 * X := by
    have h : Δ * ∑ j ∈ Finset.range (K n),
        (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n j) (gridTime s v K n (K n)) *
            altELevel d n E k τ' Db εE (Φ n) (gridTime s v K n j) +
          epsQ4 (d.L n) k (gridTime s v K n j) (gridTime s v K n (K n)) *
            altEDecay d n Db εE) ≤
        altC4 (d.L n) (d.W n) k τ' * (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) *
            (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) ^ k)⁻¹ *
            ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n j) +
          ((K n : ℝ) * Δ) * (altC4 (d.L n) (d.W n) k τ' * N ^ k *
              (5 * N ^ εE * (d.W n : ℝ) ^ (-Db)) +
            altC4e (d.L n) k * N ^ k * (N ^ εE * (d.W n : ℝ) ^ (-Db))) :=
      AltBudget_tbDriftEPart (d.L n) (d.W n) k (E n) hE (gridTime s v K n) (K n)
        ((d.W n : ℝ) ^ τ') Δ (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ'))
        (5 * N ^ εE * (d.W n : ℝ) ^ (-Db)) (N ^ εE * (d.W n : ℝ) ^ (-Db)) N
        (fun i _ => hu0 i) hu1 (fun i m him _ => hmono i m him) hΔ0 (by positivity)
        (by positivity) (by positivity) hMi1 hMN hu1K
        (fun j => altELevel d n E k τ' Db εE (Φ n) (gridTime s v K n j))
        (fun _ => altEDecay d n Db εE)
        (fun j hj => le_of_eq (by unfold altELevel altQLevel; ring))
        (fun _ _ => by unfold altEDecay; positivity) (fun _ _ => le_rfl)
    rw [hXK] at h
    refine h.trans ?_
    have hcoef : 0 ≤ altC4 (d.L n) (d.W n) k τ' *
        (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X := by positivity
    have m1 : altC4 (d.L n) (d.W n) k τ' *
        (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X *
        ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n j) ≤
        altC4 (d.L n) (d.W n) k τ' *
        (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X * Ls :=
      mul_le_mul_of_nonneg_left hlog hcoef
    have m2 : altC4 (d.L n) (d.W n) k τ' *
        (5 * N ^ εE * Φ n * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * X * Ls =
        (5 * altC4 (d.L n) (d.W n) k τ' * (N ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * Ls) *
          (Φ n * X) := by ring
    have m3 : (5 * altC4 (d.L n) (d.W n) k τ' *
          (N ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) * Ls) * (Φ n * X) ≤
        P0 / 10 * (Φ n * X) := mul_le_mul_of_nonneg_right ha4 (mul_nonneg hΦ hX0)
    have hq : 0 ≤ altC4 (d.L n) (d.W n) k τ' * N ^ k * (5 * N ^ εE * (d.W n : ℝ) ^ (-Db)) +
        altC4e (d.L n) k * N ^ k * (N ^ εE * (d.W n : ℝ) ^ (-Db)) := by positivity
    have f1 : ((K n : ℝ) * Δ) * (altC4 (d.L n) (d.W n) k τ' * N ^ k *
          (5 * N ^ εE * (d.W n : ℝ) ^ (-Db)) +
        altC4e (d.L n) k * N ^ k * (N ^ εE * (d.W n : ℝ) ^ (-Db))) ≤
        (5 * altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) * N ^ k *
          (N ^ εE * (d.W n : ℝ) ^ (-Db)) := by
      have := mul_le_mul_of_nonneg_right hKΔ1 hq
      linarith
    have f2 : (5 * altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) * N ^ k *
        (N ^ εE * (d.W n : ℝ) ^ (-Db)) ≤ P0 / 20 * X := by
      refine AltBudget_absorb hNk hP20 ?_ hXN
      exact (mul_comm _ _).le.trans he5
    linarith
  -- T6: the martingale term
  have T6 : N ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAlt d E s v K n k 𝔠 τ' Dq C' (2 * (Γ n * (Γ n * Λ n)))
        (Γ n * (Γ n * Λ n) * N + 1) (K n) a j : ℝ)) ≤ P0 / 10 * (Λr * X) + P0 / 20 * (Λr * X) := by
    have hA0 : 0 ≤ altQvA (d.L n) (d.W n) k 𝔠 τ' := by
      unfold altQvA
      have := AltBudget_cCase5_nonneg k
      have : 0 ≤ 1 + Real.log (d.L n : ℝ) := by linarith
      positivity
    have hG0 : 0 ≤ 2 * (Γ n * (Γ n * Λ n)) := by positivity
    have hMmax0 : 0 ≤ Γ n * (Γ n * Λ n) * N + 1 := by positivity
    have hB0 : 0 ≤ altQvB (d.L n) k (Γ n * (Γ n * Λ n) * N + 1) := by
      unfold altQvB
      have := AltBudget_cCase5_nonneg k
      exact mul_nonneg (mul_nonneg this ((even_two_mul k).pow_nonneg _)) (by linarith)
    have hnn : ∀ j, j < K n → 0 ≤ Δ * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
        (altQvA (d.L n) (d.W n) k 𝔠 τ') (altQvB (d.L n) k (Γ n * (Γ n * Λ n) * N + 1))
        (2 * (Γ n * (Γ n * Λ n))) ((d.W n : ℝ) ^ (-Dq + C'))
        (gridTime s v K n (j + 1)) (gridTime s v K n (K n))) := by
      intro j hj
      refine mul_nonneg hΔ0 (mul_nonneg (Nat.cast_nonneg k) ?_)
      refine AltBudget_qvShape_nonneg k hA0 hB0 hG0 hWd0 ?_
      exact (etaT_pos hE (hu1 (j + 1) (by omega))).le
    have hcoe : ∀ j ∈ Finset.range (K n),
        (cQVAlt d E s v K n k 𝔠 τ' Dq C' (2 * (Γ n * (Γ n * Λ n)))
          (Γ n * (Γ n * Λ n) * N + 1) (K n) a j : ℝ) =
        Δ * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
          (altQvA (d.L n) (d.W n) k 𝔠 τ') (altQvB (d.L n) k (Γ n * (Γ n * Λ n) * N + 1))
          (2 * (Γ n * (Γ n * Λ n))) ((d.W n : ℝ) ^ (-Dq + C'))
          (gridTime s v K n (j + 1)) (gridTime s v K n (K n))) := fun j hj =>
      AltBudget_cQVAlt_coe d n k 𝔠 τ' Dq C' _ _ (K n) a j (hnn j (Finset.mem_range.1 hj))
    rw [Finset.sum_congr rfl hcoe]
    have h := tbQv (L := d.L n) (W := d.W n) (E := E n) hE k (K n)
      (A := altQvA (d.L n) (d.W n) k 𝔠 τ') (B := altQvB (d.L n) k (Γ n * (Γ n * Λ n) * N + 1))
      (G := 2 * (Γ n * (Γ n * Λ n))) (Wd := (d.W n : ℝ) ^ (-Dq + C')) (Δ := Δ) (Nn := N)
      (gridTime s v K n) hA0 hB0 hG0 hWd0 hΔ0 (fun i _ => hu0 i) hu1
      (fun j hj => hmono (j + 1) (K n) (by omega)) hMKv hMN hu1K
    rw [hXK] at h
    have hSv : ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n (j + 1)) ≤ Ls + 1 := by
      have hsucc := AltBudget_sum_succ_le (K := K n)
        (fun j => Δ / etaT (E n) (gridTime s v K n j))
        (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : Δ / etaT (E n) (v n) ≤ 1 := by
        rw [div_eq_mul_inv]
        have h1 : Δ * (etaT (E n) (v n))⁻¹ ≤ Δ * N := mul_le_mul_of_nonneg_left hη hΔ0
        linarith
      linarith
    generalize altQvA (d.L n) (d.W n) k 𝔠 τ' = A at hA0 h ha5 he6 ⊢
    generalize altQvB (d.L n) k (Γ n * (Γ n * Λ n) * N + 1) = B at hB0 h he6 ⊢
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set Pq : ℝ := 2 * (k : ℝ) * A * (Ls + 1) with hPq
    set Qe : ℝ := (k : ℝ) * ((A + B) * N ^ (2 * k) * (d.W n : ℝ) ^ (-Dq + C')) with hQe
    have hLs0' : 0 ≤ Ls := hLs0
    have hPq0 : 0 ≤ Pq := by rw [hPq]; positivity
    have hQe0 : 0 ≤ Qe := by rw [hQe]; positivity
    have hΓX : 0 ≤ Γ n * X := mul_nonneg hΓ hX0
    have hsum : ∑ j ∈ Finset.range (K n), Δ * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
          A B (2 * (Γ n * (Γ n * Λ n))) ((d.W n : ℝ) ^ (-Dq + C'))
          (gridTime s v K n (j + 1)) (gridTime s v K n (K n))) ≤
        Pq * (Γ n * X) ^ 2 * Λ n + Qe := by
      refine h.trans ?_
      have hc0 : 0 ≤ (k : ℝ) * A * (2 * (Γ n * (Γ n * Λ n))) * X ^ 2 := by positivity
      have m1 := mul_le_mul_of_nonneg_left hSv hc0
      have m2 : ((K n : ℝ) * Δ) * Qe ≤ Qe := by
        have := mul_le_mul_of_nonneg_right hKΔ1 hQe0
        linarith
      have e : (k : ℝ) * A * (2 * (Γ n * (Γ n * Λ n))) * X ^ 2 * (Ls + 1) =
          Pq * (Γ n * X) ^ 2 * Λ n := by rw [hPq]; ring
      linarith
    have hs1' := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt (Pq * (Γ n * X) ^ 2 * Λ n + Qe) ≤
        Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n) + Real.sqrt Qe := by
      have hZ : 0 ≤ Pq * (Γ n * X) ^ 2 * Λ n := by positivity
      refine (AltBudget_sqrt_add_le hZ hQe0).trans ?_
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Pq * (Γ n * X) ^ 2),
        Real.sqrt_mul hPq0, Real.sqrt_sq hΓX]
    have hsΛ : Real.sqrt (Λ n) = Λr := Real.sqrt_eq_rpow (Λ n)
    have k1 : N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n)) ≤ P0 / 10 * (Λr * X) := by
      have e : N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n)) =
          (N ^ ε * (Γ n * Real.sqrt Pq)) * (Λr * X) := by rw [hsΛ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha5 (by positivity)
    have k2 : N ^ ε * Real.sqrt Qe ≤ P0 / 20 * (Λr * X) := by
      have hB' : 0 ≤ P0 / 20 * Λr := by positivity
      have h2 := AltBudget_absorb (y := N ^ ε * Real.sqrt Qe) hNk hB' (by
        have e : N ^ ε * Real.sqrt Qe * N ^ k = N ^ ε * (N ^ k * Real.sqrt Qe) := by ring
        rw [e]; exact he6) hXN
      calc N ^ ε * Real.sqrt Qe ≤ P0 / 20 * Λr * X := h2
        _ = P0 / 20 * (Λr * X) := by ring
    have h3 := mul_le_mul_of_nonneg_left (hs1'.trans hs2) hNe
    linarith [k1, k2]
  -- T7, T8: the `Y` term and the remainder
  have T7 : N ^ (-D_Y) ≤ P0 / 20 * X := by
    refine AltBudget_absorb hNk hP20 ?_ hXN
    rw [mul_comm]; exact he7
  have T8 : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      qErrQN d E s v K n k (N ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) j ≤
      P0 / 20 * X := by
    refine hR.trans (AltBudget_absorb hNk hP20 ?_ hXN)
    rw [mul_comm]; exact he8
  -- total
  unfold assembledRHSAlt
  have hPX : P0 * X ≤ P0 * (Λr * X) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX0 hΛr1) hP0
  have e : P0 * (Λr + Φ n) * X = P0 * (Λr * X) + P0 * (Φ n * X) := by ring
  rw [e]
  have hΦX : 0 ≤ P0 * (Φ n * X) := mul_nonneg hP0 (mul_nonneg hΦ hX0)
  have hPX0 : 0 ≤ P0 * X := mul_nonneg hP0 hX0
  simp only [hNdef, hΔdef] at T1 T2 T3 T4 T5 T6 T7 T8 ⊢
  linarith [T1, T2, T3, T4, T5, T6, T7, T8, hPX, hΦX, hPX0]

end Budget

end RBM.Ind

end
