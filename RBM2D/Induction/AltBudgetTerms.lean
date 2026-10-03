/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.NonAltBudget
import RBM2D.Induction.AltDriftQ

/-!
# Deterministic term budgets of the alternating (`𝒬`-process) assembled bound

Namespace `RBM.Ind`.  The shapes parallel the one-dimensional formalization, with the `d = 2` data
of `RBM2D.Induction.NonAltBudget` (`tbInit`, `tbDrift`), `RBM2D.Induction.AltDriftQ` (`kapQ4`,
`epsQ4`, `altQ_hker`) and per-time levels.

1. **Sharp-kernel identities**: `ratioR_pow_mul_scale_eq` (`R_{s,t}^k M_s^{-k} = M_t^{-k}`) and
   `kapQ4_mul_scale_pow_eq` (the same for the Case 4 weight `kapQ4`).
2. **The `ℚ`-part budgets with per-time levels**: `tbDriftQPart` (drift) and `tbInitQPart`
   (initial term).  The level `Λ_j` at the grid time `u_j` is an abstract real with
   `Λ_j ≤ a M_{u_j}^{-k} η_{u_j}^{-1} + b` (the shape of the second conclusion of `AltQPartGridT`);
   the budgets do not use `AltQPartGridT`.
3. **The quadratic-variation budget** `qvFormQN_bound_le_qvShape`: the Case 5 bound for
   `(𝒬 ⊗ 𝒬̄)(𝓔 ⊗ 𝓔)` is at most `NonAltBudget_qvShape` (see the last section).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Elementary facts (private) -/

section Basic

private theorem AltBudgetTerms_one_le {n : ℕ} [NeZero n] : 1 ≤ n :=
  Nat.one_le_iff_ne_zero.2 (NeZero.ne n)

/-- `ratioR = ρ`: the factor `Im m` cancels (`|E| < 2`). -/
private theorem AltBudgetTerms_ratioR_eq_rhoR {L : ℕ} {E s t : ℝ} (hE : |E| < 2) :
    ratioR L E s t = rhoR L s t := by
  have hI : (RBM.Gauss.spectralM E).im ≠ 0 := (RBM.Gauss.spectralM_im_pos hE).ne'
  unfold ratioR rhoR etaT
  rw [← mul_assoc, ← mul_assoc]
  exact mul_div_mul_right _ _ hI

/-- `0 < M_u`. -/
private theorem AltBudgetTerms_scaleM_pos {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) : 0 < scaleM L W E u :=
  scaleM_pos AltBudgetTerms_one_le AltBudgetTerms_one_le hE hu

/-- `R_{s,t} = M_s / M_t`. -/
private theorem AltBudgetTerms_ratioR_eq_div {L W : ℕ} [NeZero W] (E s t : ℝ) :
    ratioR L E s t = scaleM L W E s / scaleM L W E t :=
  MLExpVocab_ratioR_eq (Nat.pos_of_ne_zero (NeZero.ne W)) E s t

/-- `0 ≤ R_{s,t}`. -/
private theorem AltBudgetTerms_ratioR_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E s t : ℝ}
    (hE : |E| < 2) (hs : s < 1) (ht : t < 1) : 0 ≤ ratioR L E s t := by
  rw [AltBudgetTerms_ratioR_eq_div (W := W)]
  exact div_nonneg (AltBudgetTerms_scaleM_pos hE hs).le (AltBudgetTerms_scaleM_pos hE ht).le

/-- `R_{s,t} ≤ N_n` from `M_s ≤ N_n` and `1 ≤ M_t`. -/
private theorem AltBudgetTerms_ratioR_le {L W : ℕ} [NeZero L] [NeZero W] {E s t Nn : ℝ}
    (hE : |E| < 2) (hs : s < 1) (hMs : scaleM L W E s ≤ Nn) (hMt : 1 ≤ scaleM L W E t) :
    ratioR L E s t ≤ Nn := by
  rw [AltBudgetTerms_ratioR_eq_div (W := W)]
  exact (div_le_self (AltBudgetTerms_scaleM_pos hE hs).le hMt).trans hMs

end Basic

/-! ## 2. The sharp-kernel identities -/

/-- **The sharp-kernel identity** `R_{s,t}^k M_s^{-k} = M_t^{-k}` (`R_{s,t} = M_s/M_t`;
the factor `W²` cancels). -/
theorem ratioR_pow_mul_scale_eq (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ) (E s t : ℝ)
    (hE : |E| < 2) (hs : s < 1) (ht : t < 1) :
    ratioR L E s t ^ k * (scaleM L W E s ^ k)⁻¹ = (scaleM L W E t ^ k)⁻¹ := by
  have hMs := AltBudgetTerms_scaleM_pos (L := L) (W := W) hE hs
  have hMt := AltBudgetTerms_scaleM_pos (L := L) (W := W) hE ht
  rw [AltBudgetTerms_ratioR_eq_div (W := W), div_pow]
  field_simp

/-- **The sharp-kernel identity for the Case 4 weight** `kapQ4`:
`kapQ4 (s, t) M_s^{-k} = c_4(k) (1 + log L)^{k+1} K_w^{2k} M_t^{-k}` (no `η_s/η_t` prefactor). -/
theorem kapQ4_mul_scale_pow_eq (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ) (Kw E s t : ℝ)
    (hE : |E| < 2) (hs : s < 1) (ht : t < 1) :
    kapQ4 L k Kw s t * (scaleM L W E s ^ k)⁻¹ =
      cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * (scaleM L W E t ^ k)⁻¹ := by
  have h := ratioR_pow_mul_scale_eq L W k E s t hE hs ht
  rw [AltBudgetTerms_ratioR_eq_rhoR hE] at h
  unfold kapQ4
  calc cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * rhoR L s t ^ k *
        (scaleM L W E s ^ k)⁻¹
      = cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) *
          (rhoR L s t ^ k * (scaleM L W E s ^ k)⁻¹) := by ring
    _ = _ := by rw [h]

/-! ## 3. The `ℚ`-part budgets with per-time levels -/

/-- **The `ℚ`-part drift budget with per-time levels.**  For levels
`Λ_j ≤ a M_{u_j}^{-k} η_{u_j}^{-1} + b` at the grid times `u_j` (the second conclusion of
`AltQPartGridT` at the endpoint `m = K`):
`Δ Σ_{j<K} (N^ε Λ_j R_{u_j,u_K}^k + W^{-D}) ≤ N^ε a M_{u_K}^{-k} Σ_j Δ/η_{u_j} +
(K Δ)(N^ε N^k b + W^{-D})` (`R_{u_j,u_K} = M_{u_j}/M_{u_K} ≤ N_n`). -/
theorem tbDriftQPart (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ) (E : ℝ) (hE : |E| < 2)
    (u : ℕ → ℝ) (K : ℕ) (Δ Nε a b WD Nn : ℝ) (hu1 : ∀ i ≤ K, u i < 1) (hΔ : 0 ≤ Δ)
    (hNε : 0 ≤ Nε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hWD : 0 ≤ WD)
    (hM1 : ∀ i ≤ K, 1 ≤ scaleM L W E (u i)) (hMN : ∀ i ≤ K, scaleM L W E (u i) ≤ Nn)
    (Λ : ℕ → ℝ) (hΛ0 : ∀ j < K, 0 ≤ Λ j)
    (hΛ : ∀ j < K, Λ j ≤ a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b) :
    Δ * ∑ j ∈ Finset.range K, (Nε * Λ j * ratioR L E (u j) (u K) ^ k + WD) ≤
      Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * ∑ j ∈ Finset.range K, Δ / etaT E (u j) +
        ((K : ℝ) * Δ) * (Nε * Nn ^ k * b + WD) := by
  have hstep : ∀ j ∈ Finset.range K,
      Δ * (Nε * Λ j * ratioR L E (u j) (u K) ^ k + WD) ≤
        Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * (Δ / etaT E (u j)) +
          Δ * (Nε * Nn ^ k * b + WD) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.1 hj
    have huj := hu1 j hjK.le
    have huK := hu1 K le_rfl
    set R := ratioR L E (u j) (u K) with hR
    have hR0 : 0 ≤ R := AltBudgetTerms_ratioR_nonneg (L := L) (W := W) hE huj huK
    have hRN : R ≤ Nn :=
      AltBudgetTerms_ratioR_le (L := L) (W := W) hE huj (hMN j hjK.le) (hM1 K le_rfl)
    have hRk : R ^ k ≤ Nn ^ k := pow_le_pow_left₀ hR0 hRN k
    have hid : R ^ k * (scaleM L W E (u j) ^ k)⁻¹ = (scaleM L W E (u K) ^ k)⁻¹ :=
      ratioR_pow_mul_scale_eq L W k E (u j) (u K) hE huj huK
    have hNR : 0 ≤ Nε * R ^ k := mul_nonneg hNε (pow_nonneg hR0 k)
    have h1 : Nε * Λ j * R ^ k ≤
        Nε * R ^ k * (a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b) := by
      have := mul_le_mul_of_nonneg_left (hΛ j hjK) hNR
      linarith
    have h2 : Nε * R ^ k * (a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b) =
        Nε * a * (etaT E (u j))⁻¹ * (R ^ k * (scaleM L W E (u j) ^ k)⁻¹) + Nε * b * R ^ k := by
      ring
    rw [hid] at h2
    have h3 : Nε * b * R ^ k ≤ Nε * Nn ^ k * b := by
      have := mul_le_mul_of_nonneg_left hRk (mul_nonneg hNε hb)
      linarith
    have h4 : Nε * Λ j * R ^ k + WD ≤
        Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * (etaT E (u j))⁻¹ + (Nε * Nn ^ k * b + WD) := by
      have e : Nε * a * (etaT E (u j))⁻¹ * (scaleM L W E (u K) ^ k)⁻¹ =
          Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * (etaT E (u j))⁻¹ := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hΔ
    have e : Δ * (Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * (etaT E (u j))⁻¹ +
        (Nε * Nn ^ k * b + WD)) =
        Nε * a * (scaleM L W E (u K) ^ k)⁻¹ * (Δ / etaT E (u j)) +
          Δ * (Nε * Nn ^ k * b + WD) := by
      rw [div_eq_mul_inv]; ring
    rw [e] at h5
    exact h5
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- **The `ℚ`-part initial term** (first conclusion of `AltQPartGridT`, level at `s`
only): `N^ε Λ₀ R_{s,t}^k + W^{-D} ≤ N^ε G M_t^{-k} + W^{-D}` for `Λ₀ ≤ G M_s^{-k}`. -/
theorem tbInitQPart (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ) (E s t : ℝ) (hE : |E| < 2)
    (hs : s < 1) (ht : t < 1) (Nε G Λ0 WD : ℝ) (hNε : 0 ≤ Nε)
    (hΛ0 : Λ0 ≤ G * (scaleM L W E s ^ k)⁻¹) :
    Nε * Λ0 * ratioR L E s t ^ k + WD ≤ Nε * G * (scaleM L W E t ^ k)⁻¹ + WD := by
  have hR0 : 0 ≤ ratioR L E s t := AltBudgetTerms_ratioR_nonneg (L := L) (W := W) hE hs ht
  have hid := ratioR_pow_mul_scale_eq L W k E s t hE hs ht
  have hNR : 0 ≤ Nε * ratioR L E s t ^ k := mul_nonneg hNε (pow_nonneg hR0 k)
  have h1 := mul_le_mul_of_nonneg_left hΛ0 hNR
  have e : Nε * ratioR L E s t ^ k * (G * (scaleM L W E s ^ k)⁻¹) =
      Nε * G * (ratioR L E s t ^ k * (scaleM L W E s ^ k)⁻¹) := by ring
  rw [e, hid] at h1
  have e2 : Nε * Λ0 * ratioR L E s t ^ k = Nε * ratioR L E s t ^ k * Λ0 := by ring
  rw [e2]
  linarith

end RBM.Ind

end

/-! ## 4. The quadratic-variation budget of the `𝒬` process

The Case 5 right side for `(𝒬 ⊗ 𝒬̄)(𝓔 ⊗ 𝓔)` at a level `Mee ≤ G M_u^{-2k} η_u^{-1}`,
`Mee ≤ Mmax` is at most a `NonAltBudget_qvShape` with
`A = cCase5 k (1+log L)^{2k+1} (3 W^{τ'})^{4k} W^{2 cPrec(𝔠,k) τ'}`,
`B = cCase5 k ((1+log L) L²)^{2k} (2 + Mmax)` (`qvFormQN_bound_le_qvShape`); together with the
generic `tbQv` this gives the quadratic-variation budget with per-time levels. -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

section QvBudgetQ

private theorem AltBudgetTerms_cCase5_nonneg (k : ℕ) : 0 ≤ cCase5 k := by
  unfold cCase5
  exact (even_two_mul k).pow_nonneg _

/-- The Case 5 right side for `(𝒬 ⊗ 𝒬̄)(𝓔 ⊗ 𝓔)` at a
level `0 ≤ Mee ≤ G M_u^{-2k} η_u^{-1}`, `Mee ≤ Mmax`, is at most `NonAltBudget_qvShape` with
`A = cCase5 k (1+log L)^{2k+1} (3 W^{τ'})^{4k} W^{2 cPrec(𝔠,k) τ'}`,
`B = cCase5 k ((1+log L) L²)^{2k} (2 + Mmax)`, `Wd = W^{-D'+C'}`. -/
theorem qvFormQN_bound_le_qvShape (L W : ℕ) [NeZero L] [NeZero W] (k : ℕ)
    (𝔠 τ' D' C' E u w G Mee Mmax : ℝ)
    (h𝔠 : 0 < 𝔠) (hτ' : 0 ≤ τ') (hG : 0 ≤ G) (hMee0 : 0 ≤ Mee)
    (hMee : Mee ≤ G * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹)) (hMmax : Mee ≤ Mmax)
    (hu0 : 0 ≤ u) (huw : u ≤ w) (hw1 : w < 1) :
    cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) *
        rhoR L u w ^ (2 * k) *
        ((W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) * Mee + (W : ℝ) ^ (-D' + C')) +
      cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * ((1 - u) / (1 - w)) ^ (2 * k) *
        ((W : ℝ) ^ (-D' + C') * (2 + Mee)) ≤
    NonAltBudget_qvShape L W E k
      (cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) *
        (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')))
      (cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * (2 + Mmax))
      G ((W : ℝ) ^ (-D' + C')) u w := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hlog : 0 ≤ 1 + Real.log L := by have := Real.log_nonneg hL1; linarith
  have hcp : 0 ≤ cPrec 𝔠 k := by unfold cPrec; positivity
  have hX : 1 ≤ (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) :=
    Real.one_le_rpow hW1 (by positivity)
  have hWd : 0 ≤ (W : ℝ) ^ (-D' + C') := Real.rpow_nonneg (by positivity) _
  have hKw : 0 ≤ (W : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have hc5 := AltBudgetTerms_cCase5_nonneg k
  have hc1 : 0 ≤ cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) := by
    positivity
  have hc2 : 0 ≤ cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) :=
    mul_nonneg hc5 ((even_two_mul k).pow_nonneg _)
  have hρ : 0 ≤ rhoR L u w ^ (2 * k) := (even_two_mul k).pow_nonneg _
  have hq : 0 ≤ ((1 - u) / (1 - w)) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  unfold NonAltBudget_qvShape
  generalize cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) = c1
    at hc1 ⊢
  generalize cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) = c2 at hc2 ⊢
  generalize (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) = X at hX ⊢
  generalize (W : ℝ) ^ (-D' + C') = Wd at hWd ⊢
  generalize rhoR L u w ^ (2 * k) = ρ at hρ ⊢
  generalize ((1 - u) / (1 - w)) ^ (2 * k) = q at hq ⊢
  generalize (scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹ = lvl at hMee ⊢
  have hX0 : 0 ≤ X := by linarith
  have h1 : X * Mee + Wd ≤ X * (G * lvl + Wd) := by
    nlinarith [mul_le_mul_of_nonneg_left hMee hX0, mul_nonneg hWd (sub_nonneg.2 hX)]
  have h2 : c1 * ρ * (X * Mee + Wd) ≤ c1 * ρ * (X * (G * lvl + Wd)) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hc1 hρ)
  have h3 : c2 * q * (Wd * (2 + Mee)) ≤ c2 * q * (Wd * (2 + Mmax)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hWd) (mul_nonneg hc2 hq)
  have e1 : c1 * ρ * (X * (G * lvl + Wd)) = c1 * X * ρ * (G * lvl + Wd) := by ring
  have e2 : c2 * q * (Wd * (2 + Mmax)) = c2 * (2 + Mmax) * q * Wd := by ring
  linarith

end QvBudgetQ

end RBM.Ind

end
