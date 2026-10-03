/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.LemDecCalE
import RBM2D.Path.LemDecCalEwG
import RBM2D.Path.UTransport
import RBM2D.Propagator.Decay

/-!
# The pointwise drift transported to the endpoint

`DriftPoint` states the bound of (`res_deccalE_1`) and (`res_deccalE_2`) at the endpoint `v`:
the bracket is the sum of the bound for the `𝓔^{LK×LK}` term and the bound for the `𝓔^{(G̃)}`
term, with the near-diagonal exponents of the proof.

Result (namespace `RBM.Path`): `driftPoint : DriftPoint`, with the explicit constant
`2 e^{2 (log W)^{3/4}}`.

Proof outline.
* `‖𝓔^{LK×LK}‖ + ‖𝓔^{(G̃)}‖` is bounded pointwise by `lemDecCalE_lk` and `lemDecCalE_wG`;
* the transport by `𝒰_{u,v}` is `uopLocalMax` at the radius `R = ℓ*_v`, with the global bound
  `α` (from `𝒯_v ≤ 2`) and the local bound `β` (`tailT` is non-increasing and `tellStar` at
  `C = 2` move the tail from `|b₁ - b₂|` to `|a₁ - a₂|`; a near `b` has
  `|a₁ - a₂| < 2ℓ*_v + |b₁ - b₂|`);
* the far cost `2 L² W^{-D'} (η_u/η_v) α` is absorbed by the hypothesis
  `16 L⁶ W⁶ W^{-D'} ≤ W^{-D}` and `𝒯_v ≥ W^{-D}`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-- **The pointwise drift, transported to the endpoint**, (`res_deccalE_1`) and
(`res_deccalE_2`) with the proof exponents: on `E2Hyp` and the far-kernel condition at
`ℓ*_v`, `‖𝒰_{u,v}(𝓔^{LK×LK} + 𝓔^{(G̃)})_a‖ ≤ 2 e^{2(log W)^{3/4}} loss (η_u/η_v)² η_u^{-1}
[M_u^{-1}(J*)² + ρ⁶ 1(|a₁-a₂| ≤ 3ℓ*_v) + ρ² M_u^{-1/2}(J*)²] 𝒯_v`, `ρ = ℓ_u/ℓ_s`. -/
def DriftPoint : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E s u v D D' Λ K₀ : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ),
    E2Hyp L W E s u v D Λ K₀ M → UkerFar L W u v (ellStar L W v) D' →
    16 * (L : ℝ) ^ 6 * (W : ℝ) ^ 6 * (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) →
    ∀ a : Z2 L × Z2 L,
      ‖Uop L 1 u v (fun b => ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2) a‖ ≤
        2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ *
          (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
            (ellT L u / ellT L s) ^ 6 *
              (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) *
          tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ)

/-! ## 1. Distances -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem dp_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

/-- `|a₁ - a₂| ≤ |a₁ - b₁| + |b₁ - b₂| + |a₂ - b₂|` (two uses of the triangle inequality, and
`|b₂ - a₂| = |a₂ - b₂|`). -/
private theorem dp_zdist2_three (a₁ a₂ b₁ b₂ : Z2 L) :
    (zdist2 L (a₁ - a₂) : ℝ) ≤
      (zdist2 L (a₁ - b₁) : ℝ) + (zdist2 L (b₁ - b₂) : ℝ) + (zdist2 L (a₂ - b₂) : ℝ) := by
  have h1 : a₁ - a₂ = (a₁ - b₁ + (b₁ - b₂)) + (-(a₂ - b₂)) := by abel
  have hneg : zdist2 L (-(a₂ - b₂)) = zdist2 L (a₂ - b₂) := by
    simp only [zdist2, Prod.fst_neg, Prod.snd_neg, dp_zdist_neg]
  have h2 := zdist2_add_le L (a₁ - b₁ + (b₁ - b₂)) (-(a₂ - b₂))
  have h3 := zdist2_add_le L (a₁ - b₁) (b₁ - b₂)
  rw [← h1, hneg] at h2
  have h4 : zdist2 L (a₁ - a₂) ≤ zdist2 L (a₁ - b₁) + zdist2 L (b₁ - b₂) + zdist2 L (a₂ - b₂) := by
    omega
  exact_mod_cast h4

end Dist

/-! ## 2. Real-number bookkeeping -/

section Real

/-- The bracket at the global bound: `B₀ + ρ⁶ ≤ 2 L⁴ W B₀` with
`B₀ = M⁻¹ J² + ρ² q J²`, using `J ≥ 1`, `q ≥ W⁻¹` (`q = M_u^{-1/2}`, `M_u ≤ W²`), `1 ≤ ρ ≤ L`. -/
private theorem dp_bracket_alpha {Lr Wr ρ q J Mi : ℝ} (hL1 : 1 ≤ Lr) (hW1 : 1 ≤ Wr)
    (hρ1 : 1 ≤ ρ) (hρL : ρ ≤ Lr) (hq : Wr⁻¹ ≤ q) (hJ : 1 ≤ J) (hMi : 0 ≤ Mi) :
    Mi * J ^ 2 + ρ ^ 6 + ρ ^ 2 * q * J ^ 2 ≤
      2 * Lr ^ 4 * Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) := by
  have hW0 : 0 < Wr := by linarith
  have hJ2 : 1 ≤ J ^ 2 := by nlinarith
  have hq0 : 0 ≤ q := (inv_nonneg.2 hW0.le).trans hq
  have hρ0 : 0 ≤ ρ := by linarith
  have hB0 : 0 ≤ Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2 := by positivity
  have hWq : 1 ≤ Wr * q := by
    have := mul_le_mul_of_nonneg_left hq hW0.le
    rwa [mul_inv_cancel₀ hW0.ne'] at this
  have h1 : ρ ^ 2 ≤ Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) := by
    have h2 : ρ ^ 2 ≤ Wr * (ρ ^ 2 * q * J ^ 2) := by
      calc ρ ^ 2 = ρ ^ 2 * 1 * 1 := by ring
        _ ≤ ρ ^ 2 * (Wr * q) * J ^ 2 := by gcongr
        _ = Wr * (ρ ^ 2 * q * J ^ 2) := by ring
    have h3 : 0 ≤ Wr * (Mi * J ^ 2) := by positivity
    nlinarith
  have h4 : ρ ^ 6 ≤ Lr ^ 4 * ρ ^ 2 := by
    have h5 : ρ ^ 4 ≤ Lr ^ 4 := pow_le_pow_left₀ hρ0 hρL 4
    calc ρ ^ 6 = ρ ^ 4 * ρ ^ 2 := by ring
      _ ≤ Lr ^ 4 * ρ ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
  have hL4 : 1 ≤ Lr ^ 4 := one_le_pow₀ hL1
  have hL4W : 1 ≤ Lr ^ 4 * Wr := by nlinarith
  have h6 : ρ ^ 6 ≤ Lr ^ 4 * Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) := by
    calc ρ ^ 6 ≤ Lr ^ 4 * ρ ^ 2 := h4
      _ ≤ Lr ^ 4 * (Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Lr ^ 4 * Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) := by ring
  have h7 : Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2 ≤
      Lr ^ 4 * Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) := le_mul_of_one_le_left hB0 hL4W
  nlinarith

/-- The closing inequality: the near part `r² β` with
`β = e₁ X Br T`, plus the far part `2 L² F r α` with `α ≤ 4 X B₀ L⁴ W` and `16 L⁶ W⁶ F ≤ W^{-D} ≤ T`,
is at most `2 e₂ r² X Br T` for `e₁ ≤ e₂`, `1 ≤ e₂`, `1 ≤ r`, `B₀ ≤ Br`. -/
private theorem dp_final {r X Br B0 T e1 e2 F Lr Wr Dd α : ℝ} (hr : 1 ≤ r) (hX : 0 ≤ X)
    (hB0 : 0 ≤ B0) (hBr : B0 ≤ Br) (hT : 0 ≤ T) (he1 : e1 ≤ e2) (he2 : 1 ≤ e2) (hF : 0 ≤ F)
    (hL1 : 1 ≤ Lr) (hW1 : 1 ≤ Wr) (hDd : Dd ≤ T) (hhyp : 16 * Lr ^ 6 * Wr ^ 6 * F ≤ Dd)
    (hα : α ≤ 4 * X * B0 * Lr ^ 4 * Wr) :
    r ^ 2 * (e1 * (X * Br * T)) + 2 * Lr ^ 2 * F * r * α ≤ 2 * e2 * r ^ 2 * X * Br * T := by
  have hL0 : 0 ≤ Lr := by linarith
  have hW0 : 0 ≤ Wr := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hBr0 : 0 ≤ Br := hB0.trans hBr
  have hS0 : 0 ≤ Lr ^ 6 * F * Wr := by positivity
  have hW5 : 1 ≤ Wr ^ 5 := one_le_pow₀ hW1
  have hS : 16 * (Lr ^ 6 * F * Wr) ≤ T := by
    have h1 : 16 * (Lr ^ 6 * F * Wr) * 1 ≤ 16 * (Lr ^ 6 * F * Wr) * Wr ^ 5 :=
      mul_le_mul_of_nonneg_left hW5 (by positivity)
    have h2 : 16 * (Lr ^ 6 * F * Wr) * Wr ^ 5 = 16 * Lr ^ 6 * Wr ^ 6 * F := by ring
    linarith
  have hfar1 : 2 * Lr ^ 2 * F * r * α ≤ 2 * Lr ^ 2 * F * r * (4 * X * B0 * Lr ^ 4 * Wr) :=
    mul_le_mul_of_nonneg_left hα (by positivity)
  have hfar2 : 2 * Lr ^ 2 * F * r * (4 * X * B0 * Lr ^ 4 * Wr) =
      8 * (Lr ^ 6 * F * Wr) * (r * X * B0) := by ring
  have hrXB : 0 ≤ r * X * B0 := by positivity
  have hfar3 : 8 * (Lr ^ 6 * F * Wr) * (r * X * B0) ≤ T / 2 * (r * X * B0) :=
    mul_le_mul_of_nonneg_right (by linarith) hrXB
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hfar4 : T / 2 * (r * X * B0) ≤ T / 2 * (r ^ 2 * X * Br) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : r * X * B0 ≤ r * X * Br := mul_le_mul_of_nonneg_left hBr (by positivity)
    have h2 : r * X * Br ≤ r ^ 2 * X * Br :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrr hX) hBr0
    linarith
  have hP : 0 ≤ r ^ 2 * X * Br * T := by positivity
  have hnear : r ^ 2 * (e1 * (X * Br * T)) = e1 * (r ^ 2 * X * Br * T) := by ring
  have hgoal : 2 * e2 * r ^ 2 * X * Br * T = 2 * e2 * (r ^ 2 * X * Br * T) := by ring
  have hhalf : T / 2 * (r ^ 2 * X * Br) = 1 / 2 * (r ^ 2 * X * Br * T) := by ring
  rw [hnear, hgoal]
  have h5 : e1 * (r ^ 2 * X * Br * T) ≤ e2 * (r ^ 2 * X * Br * T) :=
    mul_le_mul_of_nonneg_right he1 hP
  have h6 : 1 / 2 * (r ^ 2 * X * Br * T) ≤ e2 * (r ^ 2 * X * Br * T) :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  linarith

/-- The whole closing step with the bracket unfolded: `r² β + 2 L² F r α ≤ 2 e₂ loss r² η⁻¹ Br T`
for `β = e₁ (X Br T)`, `α = 2 X (M⁻¹ J² + ρ⁶ + ρ² q J²)`, `X = loss η⁻¹`,
`Br = M⁻¹ J² + ρ⁶ Ia + ρ² q J²` (`Ia ≥ 0` is the indicator). -/
private theorem dp_close {Lr Wr r loss ηi Mi J ρ q Ia T Dd F e1 e2 : ℝ}
    (hr : 1 ≤ r) (hloss : 0 ≤ loss) (hηi : 0 ≤ ηi) (hMi : 0 ≤ Mi) (hJ : 1 ≤ J) (hρ1 : 1 ≤ ρ)
    (hρL : ρ ≤ Lr) (hq : Wr⁻¹ ≤ q) (hIa : 0 ≤ Ia) (hT : 0 ≤ T) (he1 : e1 ≤ e2) (he2 : 1 ≤ e2)
    (hF : 0 ≤ F) (hL1 : 1 ≤ Lr) (hW1 : 1 ≤ Wr) (hDd : Dd ≤ T)
    (hhyp : 16 * Lr ^ 6 * Wr ^ 6 * F ≤ Dd) :
    r ^ 2 * (e1 * (loss * ηi * (Mi * J ^ 2 + ρ ^ 6 * Ia + ρ ^ 2 * q * J ^ 2) * T)) +
        2 * Lr ^ 2 * F * r * (2 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 6 + ρ ^ 2 * q * J ^ 2)) ≤
      2 * e2 * loss * r ^ 2 * ηi * (Mi * J ^ 2 + ρ ^ 6 * Ia + ρ ^ 2 * q * J ^ 2) * T := by
  have hW0 : 0 < Wr := by linarith
  have hq0 : 0 ≤ q := (inv_nonneg.2 hW0.le).trans hq
  have hρ0 : 0 ≤ ρ := by linarith
  have hX : 0 ≤ loss * ηi := mul_nonneg hloss hηi
  have hB0 : 0 ≤ Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2 := by positivity
  have hα0 := dp_bracket_alpha hL1 hW1 hρ1 hρL hq hJ hMi
  have hα : 2 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 6 + ρ ^ 2 * q * J ^ 2) ≤
      4 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) * Lr ^ 4 * Wr := by
    calc 2 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 6 + ρ ^ 2 * q * J ^ 2)
        ≤ 2 * (loss * ηi) * (2 * Lr ^ 4 * Wr * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2)) :=
          mul_le_mul_of_nonneg_left hα0 (by positivity)
      _ = 4 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) * Lr ^ 4 * Wr := by ring
  have hBrB : Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2 ≤ Mi * J ^ 2 + ρ ^ 6 * Ia + ρ ^ 2 * q * J ^ 2 := by
    have := mul_nonneg (pow_nonneg hρ0 6) hIa
    linarith
  have h := dp_final (r := r) (X := loss * ηi) (Br := Mi * J ^ 2 + ρ ^ 6 * Ia + ρ ^ 2 * q * J ^ 2)
    (B0 := Mi * J ^ 2 + ρ ^ 2 * q * J ^ 2) (T := T) (e1 := e1) (e2 := e2) (F := F) (Lr := Lr)
    (Wr := Wr) (Dd := Dd) (α := 2 * (loss * ηi) * (Mi * J ^ 2 + ρ ^ 6 + ρ ^ 2 * q * J ^ 2))
    hr hX hB0 hBrB hT he1 he2 hF hL1 hW1 hDd hhyp hα
  refine h.trans (le_of_eq ?_)
  ring

end Real

/-! ## 3. The tail at the endpoint -/

section Tail

variable {L W : ℕ}

/-- `𝒯_{v,D}(x) ≤ 2` for `1 ≤ M_v`, `1 < W`, `0 ≤ D`. -/
private theorem dp_tailT_le_two {E D v : ℝ} (hW : (1 : ℝ) < W) (hD : 0 ≤ D)
    (hMv : 1 ≤ scaleM L W E v) (x : ℝ) : tailT L W E D v x ≤ 2 := by
  unfold tailT
  have h1 : (scaleM L W E v ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    nlinarith
  have h2 : Real.exp (-Real.sqrt (x / ellT L v)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith [Real.sqrt_nonneg (x / ellT L v)])
  have h3 : (W : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW.le (by linarith)
  have h4 : (scaleM L W E v ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L v)) ≤ 1 := by
    have h5 : 0 ≤ Real.exp (-Real.sqrt (x / ellT L v)) := (Real.exp_pos _).le
    calc (scaleM L W E v ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L v))
        ≤ 1 * 1 := mul_le_mul h1 h2 h5 zero_le_one
      _ = 1 := one_mul 1
  linarith

/-- `W^{-D} ≤ 𝒯_{v,D}(x)`. -/
private theorem dp_tailT_ge {E D v : ℝ} (x : ℝ) :
    (W : ℝ) ^ (-D) ≤ tailT L W E D v x := by
  unfold tailT
  have : 0 ≤ (scaleM L W E v ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L v)) :=
    mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le
  linarith

end Tail

/-! ## 4. The theorem -/

theorem driftPoint : DriftPoint := by
  intro L W _ _ E s u v D D' Λ K₀ M hyp hFar hD' a
  obtain ⟨hW1r, hD24, -, -⟩ := LemDecCalE_floor hyp
  obtain ⟨hMv1, hMvu, hMuW⟩ := LemDecCalE_e2 hyp
  have hlk := lemDecCalE_lk L W E s u v D Λ K₀ M hyp
  have hwG := lemDecCalE_wG L W E s u v D Λ K₀ M hyp
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := hyp
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : 0 ≤ Real.log W := by linarith
  -- scales
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hηv : 0 < etaT E v := etaT_pos hE hv1
  have hr : etaT E u / etaT E v = (1 - u) / (1 - v) := etaT_div_etaT hE hu1 hv1
  have hr1 : 1 ≤ (1 - u) / (1 - v) := (one_le_div (by linarith)).2 (by linarith)
  have hJ1 : 1 ≤ jStarMat L W E D u M := one_le_jStarMat L W hW1 E D u M
  have hMu : 0 < scaleM L W E u := by linarith
  have hℓs := ellT_pos_le hL1 hs1
  have hℓs1 : 1 ≤ ellT L s := one_le_ellT hL1 hs0 hs1
  have hℓu := ellT_pos_le hL1 hu1
  have hℓsu : ellT L s ≤ ellT L u := (ellT_mono_ratio hL1 hs0 hsu hu1).1
  have hℓuv : ellT L u ≤ ellT L v := (ellT_mono_ratio hL1 hu0 huv hv1).1
  have hρ1 : 1 ≤ ellT L u / ellT L s := (one_le_div hℓs.1).2 hℓsu
  have hρL : ellT L u / ellT L s ≤ L := by
    rw [div_le_iff₀ hℓs.1]
    calc ellT L u ≤ (L : ℝ) := hℓu.2
      _ = (L : ℝ) * 1 := (mul_one _).symm
      _ ≤ (L : ℝ) * ellT L s := mul_le_mul_of_nonneg_left hℓs1 (by linarith)
  have hq : (W : ℝ)⁻¹ ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc (W : ℝ)⁻¹ = Real.sqrt (((W : ℝ)⁻¹) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((scaleM L W E u)⁻¹) := by
        apply Real.sqrt_le_sqrt
        rw [inv_pow]
        exact inv_anti₀ hMu hMuW
  have hq0 : 0 ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (inv_nonneg.2 hMu.le) _
  have hstar : ellStar L W u ≤ ellStar L W v := by
    unfold ellStar
    exact mul_le_mul_of_nonneg_left hℓuv (Real.rpow_nonneg hlogW _)
  have hloss : 0 ≤ lossE2 L W Λ K₀ := by
    have h1 : 0 ≤ 1 + Real.log W := by linarith
    have h2 : 0 ≤ 1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) := by
      have : (1 : ℝ) ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ 12 := by
        have h3 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1r
        have h4 : (1 : ℝ) ≤ (W : ℝ) ^ 12 := one_le_pow₀ hW1r.le
        nlinarith
      have := Real.log_nonneg this
      linarith
    have hΛ0 : 0 ≤ Λ := by linarith
    unfold lossE2
    positivity
  have hX : 0 ≤ lossE2 L W Λ K₀ * (etaT E u)⁻¹ := mul_nonneg hloss (inv_nonneg.2 hηu.le)
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hMu.le
  -- pointwise bound for `A = ELKLK + EGt`
  have hpt : ∀ b : Z2 L × Z2 L,
      ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖ ≤
        lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
            (ellT L u / ellT L s) ^ 6 *
              (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then 1 else 0) +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) *
          tailT L W E D v (zdist2 L (b.1 - b.2) : ℝ) := by
    intro b
    calc ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖
        ≤ ‖ELKLK L W E u M b.1 b.2‖ + ‖EGt L W E u M b.1 b.2‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hlk b.1 b.2) (hwG b.1 b.2)
      _ = _ := by ring
  -- global bound `α`
  have hglob : ∀ b : Z2 L × Z2 L,
      ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖ ≤
        2 * (lossE2 L W Λ K₀ * (etaT E u)⁻¹) *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 + (ellT L u / ellT L s) ^ 6 +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) := by
    intro b
    refine (hpt b).trans ?_
    have hI : (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hI0 : (0 : ℝ) ≤ (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have hT := dp_tailT_le_two (E := E) (D := D) (v := v) (L := L) hW1r (by linarith) hMv1
      (zdist2 L (b.1 - b.2) : ℝ)
    have hTp := tailT_pos hW1 L E D v (zdist2 L (b.1 - b.2) : ℝ)
    have hJ0 : 0 ≤ jStarMat L W E D u M := by linarith
    have hρ0 : 0 ≤ ellT L u / ellT L s := by linarith
    have hBr : (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 ≤
        (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 + (ellT L u / ellT L s) ^ 6 +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 := by
      have := mul_le_mul_of_nonneg_left hI (pow_nonneg hρ0 6)
      linarith
    have hBr0 : 0 ≤ (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 := by positivity
    calc _ ≤ lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 + (ellT L u / ellT L s) ^ 6 +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBr hX) hT hTp.le
            (mul_nonneg hX (hBr0.trans hBr))
      _ = _ := by ring
  -- local bound `β` near `a` (radius `R = ℓ*_v`)
  have hloc : ∀ b : Z2 L × Z2 L, (zdist2 L (a.1 - b.1) : ℝ) < ellStar L W v →
      (zdist2 L (a.2 - b.2) : ℝ) < ellStar L W v →
      ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖ ≤
        Real.exp (Real.sqrt 2 * Real.log W ^ ((3 : ℝ) / 4)) *
          (lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
            ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
              (ellT L u / ellT L s) ^ 6 *
                (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
              (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
                jStarMat L W E D u M ^ 2) *
            tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ)) := by
    intro b hb1 hb2
    have h3 := dp_zdist2_three a.1 a.2 b.1 b.2
    have hx : (zdist2 L (a.1 - a.2) : ℝ) - 2 * ellStar L W v ≤ (zdist2 L (b.1 - b.2) : ℝ) := by
      linarith
    have hT1 : tailT L W E D v (zdist2 L (b.1 - b.2) : ℝ) ≤
        tailT L W E D v ((zdist2 L (a.1 - a.2) : ℝ) - 2 * ellStar L W v) :=
      LemDecCalE_tailT_anti hL1 hv1 hx
    have hT2 : tailT L W E D v ((zdist2 L (a.1 - a.2) : ℝ) - 2 * ellStar L W v) ≤
        Real.exp (Real.sqrt 2 * Real.log W ^ ((3 : ℝ) / 4)) *
          tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) :=
      tellStar L W E D v 2 (zdist2 L (a.1 - a.2) : ℝ) hv1 (by norm_num)
    have hI : (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) ≤
        (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) := by
      by_cases hc : (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u
      · have hc' : (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v := by linarith
        simp [hc, hc']
      · simp only [hc, ite_false]
        split_ifs <;> norm_num
    have hTp := tailT_pos hW1 L E D v (zdist2 L (b.1 - b.2) : ℝ)
    have hJ0 : 0 ≤ jStarMat L W E D u M := by linarith
    have hρ0 : 0 ≤ ellT L u / ellT L s := by linarith
    have hI0 : (0 : ℝ) ≤ (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have hBrb : (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 ≤
        (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 := by
      have := mul_le_mul_of_nonneg_left hI (pow_nonneg hρ0 6)
      linarith
    have hBrb0 : 0 ≤ (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then (1 : ℝ) else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 := by positivity
    calc ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖
        ≤ lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
            (ellT L u / ellT L s) ^ 6 *
              (if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then 1 else 0) +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) *
          tailT L W E D v (zdist2 L (b.1 - b.2) : ℝ) := hpt b
      _ ≤ lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
            (ellT L u / ellT L s) ^ 6 *
              (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
              jStarMat L W E D u M ^ 2) *
          (Real.exp (Real.sqrt 2 * Real.log W ^ ((3 : ℝ) / 4)) *
            tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBrb hX) (hT1.trans hT2) hTp.le
            (mul_nonneg hX (hBrb0.trans hBrb))
      _ = _ := by ring
  -- transport by `𝒰_{u,v}`
  have hTa := tailT_pos hW1 L E D v (zdist2 L (a.1 - a.2) : ℝ)
  have hIa0 : (0 : ℝ) ≤ (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hJ0 : 0 ≤ jStarMat L W E D u M := by linarith
  have hρ0 : 0 ≤ ellT L u / ellT L s := by linarith
  have hBr0 : 0 ≤ (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
        (ellT L u / ellT L s) ^ 6 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then (1 : ℝ) else 0) +
        (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
          jStarMat L W E D u M ^ 2 := by positivity
  have hβ : 0 ≤ Real.exp (Real.sqrt 2 * Real.log W ^ ((3 : ℝ) / 4)) *
      (lossE2 L W Λ K₀ * (etaT E u)⁻¹ *
        ((scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2 +
          (ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2) *
        tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hX hBr0) hTa.le)
  have hU := uopLocalMax L W hL3 u v (ellStar L W v) D' hu0 huv hv1 hFar
    (fun b => ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2) _ _ a hβ hglob hloc
  rw [hr]
  refine hU.trans ?_
  -- closing inequality
  have hDd := dp_tailT_ge (L := L) (W := W) (E := E) (D := D) (v := v)
    (zdist2 L (a.1 - a.2) : ℝ)
  have he1 : Real.exp (Real.sqrt 2 * Real.log W ^ ((3 : ℝ) / 4)) ≤
      Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) := by
    apply Real.exp_le_exp.2
    have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have hY : 0 ≤ Real.log W ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hlogW _
    exact mul_le_mul_of_nonneg_right h2 hY
  have he2 : 1 ≤ Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) := by
    apply Real.one_le_exp
    have hY : 0 ≤ Real.log W ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hlogW _
    linarith
  have key := dp_close hr1 hloss (inv_nonneg.2 hηu.le) hMi hJ1 hρ1 hρL hq hIa0 hTa.le he1 he2
    (Real.rpow_nonneg hW0.le (-D')) hL1r hW1r.le hDd hD'
  exact key

end RBM.Path
