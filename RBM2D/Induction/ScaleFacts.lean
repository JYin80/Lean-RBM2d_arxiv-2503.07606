/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

import RBM2D.Induction.Defs

/-!
# The scale facts of Steps 1--5 and the chain step condition

Deterministic scale inequalities (`scaleFacts_R1`, `scaleFacts_R2`, the ratio facts, the near case
of Step 5) among the scales `etaT`, `ellT`, `scaleM` (`RBM2D.Path.Scales`) and the step-2
properties `Bandwidth`, `CondStInd`, `RangeCond` (`RBM2D.Path.Step2Props`), and the statement
`ChainStepCond` with its proof `chainStepCond`.  The argument parallels the one-dimensional
formalization; the `d = 2` forms of some of the ratio facts are in `RBM2D.Path.Scales`.

Paper: arXiv:2503.07606, Section 2 (`con_st_ind`, the chain times) and Section 5 (Steps 1, 3, 5).
-/

noncomputable section

namespace RBM.Ind

open Filter RBM RBM.Gauss RBM.Path

variable (d : Sizes)

/-! ## 1. The statement -/

/-- The step condition of the chain: `CondStInd` and `RangeCond` at `(s_k, s_{k+1})`. -/
def ChainStepCond (κ c τ : ℝ) : Prop :=
  ∀ (E t : ℕ → ℝ) (n₀ : ℕ), (∀ n, |E n| ≤ 2 - κ) → 0 < κ → 0 < c → 0 < τ →
    30 / min (2 * c) τ < n₀ → (∀ n, 0 ≤ t n) → SizeTendsto d → Bandwidth d c →
    RangeCond d τ t → ∀ k : ℕ, k < n₀ →
      CondStInd d E (chainTime t n₀ k) (chainTime t n₀ (k + 1)) ∧
        RangeCond d τ (chainTime t n₀ (k + 1))


/-! ## 2. Elementary facts on the sizes -/

private theorem sf_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem sf_one_le_W (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem sf_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h : 1 ≤ d.size n :=
    Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))
  exact_mod_cast h

/-- The range condition at one index forces `t < 1`. -/
private theorem sf_lt_one_of_range {τ t : ℝ} {n : ℕ}
    (h : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t) : t < 1 := by
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (sf_one_le_size d n)
  have := Real.rpow_pos_of_pos hN0 (-1 + τ)
  linarith

/-! ## 3. `M_u ≥ Im m · N^{c₀}` for `u ≤ t` -/

/-- **`scaleFacts_R1`**: under `Bandwidth d c` and `RangeCond d τ t`, eventually, for every
`u ≤ t n`, `Im m^{(E n)} · N^{min(2c, τ)} ≤ M_u`, with `N = d.size n = (W L)²`.  The hypotheses
`0 < κ` (for `|E n| < 2`), `0 < c`, `0 < τ` are those of `scaleM_etaT_of_range`. -/
theorem scaleFacts_R1 (κ c τ : ℝ) (E t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ)
    (hc : 0 < c) (hτ : 0 < τ) (hB : Bandwidth d c) (hR : RangeCond d τ t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤
        scaleM (d.L n) (d.W n) (E n) u := by
  filter_upwards [hB, hR] with n hBn hRn u hu
  have htlt : t n < 1 := sf_lt_one_of_range d hRn
  have hE' : |E n| < 2 := by linarith [hE n]
  exact (scaleM_etaT_of_range (sf_one_le_L d n) (sf_one_le_W d n) hE' hc hτ
    (lt_of_le_of_lt hu htlt) hBn (le_trans hRn (by linarith))).1

/-! ## 4. `M_u ≥ M_s^{29/30}` for `u ∈ [s, t]` -/

/-- **`scaleFacts_R2_pt`**, pointwise: from the step condition `M_s⁻¹ ≤ ((1 - t)/(1 - s))^30`
(`con_st_ind`), for `s ≤ u ≤ t < 1`, `M_s^{29/30} ≤ M_u`. -/
theorem scaleFacts_R2_pt {L W : ℕ} {E s u t : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1)
    (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    scaleM L W E s ^ ((29 : ℝ) / 30) ≤ scaleM L W E u := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hM : 0 < scaleM L W E s := scaleM_pos hL hW hE hs1
  set M := scaleM L W E s with hMdef
  set q := (1 - t) / (1 - s) with hqdef
  have hq : 0 < q := div_pos hxt hxs
  set a : ℝ := M ^ ((1 : ℝ) / 30) with hadef
  have ha : 0 < a := Real.rpow_pos_of_pos hM _
  have ha30 : a ^ 30 = M := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
  have h29 : M ^ ((29 : ℝ) / 30) = a ^ 29 := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
  have hainv : a⁻¹ ≤ q := by
    have h1 : (a⁻¹) ^ 30 ≤ q ^ 30 := by rw [inv_pow, ha30]; exact hstep
    exact (pow_le_pow_iff_left₀ (inv_nonneg.2 ha.le) hq.le (by norm_num)).1 h1
  have hanti := (scaleM_anti_ratio (W := W) hL hE hsu hu1).2
  have hxu : 1 - t ≤ 1 - u := by linarith
  have hq' : q ≤ (1 - u) / (1 - s) := div_le_div_of_nonneg_right hxu hxs.le
  calc M ^ ((29 : ℝ) / 30) = M * a⁻¹ := by
        rw [h29]; rw [← ha30]; field_simp
    _ ≤ M * q := mul_le_mul_of_nonneg_left hainv hM.le
    _ ≤ M * ((1 - u) / (1 - s)) := mul_le_mul_of_nonneg_left hq' hM.le
    _ = M * (1 - u) / (1 - s) := by ring
    _ ≤ scaleM L W E u := hanti

/-- **`scaleFacts_R2`**, sequence form: `CondStInd d E s t` and `RangeCond d τ t` give, eventually, for every
`u ∈ [s n, t n]`, `M_{s n}^{29/30} ≤ M_u`.  `RangeCond` (or an equivalent `t < 1`) is needed
because `CondStInd` is vacuous at `s ≥ 1` (Lean `ℓ = 1/√0 = 0`). -/
theorem scaleFacts_R2 (κ τ : ℝ) (E s t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ)
    (hC : CondStInd d E s t) (hR : RangeCond d τ t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      scaleM (d.L n) (d.W n) (E n) (s n) ^ ((29 : ℝ) / 30) ≤
        scaleM (d.L n) (d.W n) (E n) u := by
  filter_upwards [hC, hR] with n hCn hRn u hsu hut
  exact scaleFacts_R2_pt (sf_one_le_L d n) (sf_one_le_W d n) (by linarith [hE n]) hsu hut
    (sf_lt_one_of_range d hRn) hCn

/-! ## 5. The ratio facts for Steps 1 and 3 -/

/-- Ratio fact for Step 1 (`ℓ_u ℓ_s^{-1} ≤ M_s^{1/60}`):
`ℓ_u/ℓ_s ≤ ((1 - s)/(1 - t))^{1/2}` for
`0 ≤ s ≤ u ≤ t < 1`.  The hypothesis `0 ≤ s` is that of `ellT_mono_ratio`. -/
theorem scaleFacts_ellT_ratio {L : ℕ} {s u t : ℝ} (hL : 1 ≤ L) (hs0 : 0 ≤ s) (hsu : s ≤ u)
    (hut : u ≤ t) (ht : t < 1) :
    ellT L u / ellT L s ≤ ((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  refine le_trans (ellT_mono_ratio hL hs0 hsu hu1).2 ?_
  refine Real.rpow_le_rpow (div_nonneg hxs.le (by linarith)) ?_ (by norm_num)
  exact div_le_div_of_nonneg_left hxs.le hxt (by linarith)

/-- Ratio fact for Step 3: `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)^2` for `|E| < 2`,
`0 ≤ s ≤ t < 1`. -/
theorem scaleFacts_ellT_pow_four {L : ℕ} {E s t : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) :
    (ellT L t / ellT L s) ^ 4 ≤ (etaT E s / etaT E t) ^ 2 := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hC := scaleFacts_ellT_ratio hL hs0 hst le_rfl ht
  have hpos : 0 < ellT L t / ellT L s :=
    div_pos (ellT_pos_le hL ht).1 (ellT_pos_le hL hs1).1
  have hr0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg hxs.le hxt.le
  have h4 : (ellT L t / ellT L s) ^ 4 ≤ (((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)) ^ 4 :=
    pow_le_pow_left₀ hpos.le hC 4
  have h5 : (((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2)) ^ 4 = ((1 - s) / (1 - t)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, ← Real.rpow_natCast]; norm_num
  rw [etaT_div_etaT hE hs1 ht]
  exact h4.trans_eq h5

/-! ## 6. The chain step condition -/

/-- **`chainStepCond`** (the chain times with a fixed `n₀`): `ChainStepCond`
holds for all `κ c τ`.  Proof: eventually `M_{s_k} ≥ M_t ≥ Im m N^{c₀} ≥ N^{30/n₀}` (facts of
`RBM2D.Path.Scales`, and `N^{c₀ - 30/n₀} → ∞`), while
`((1 - s_{k+1})/(1 - s_k))^30 = (1 - t)^{30/n₀} ≥ N^{-30/n₀}`. -/
theorem chainStepCond (κ c τ : ℝ) : ChainStepCond d κ c τ := by
  intro E t n₀ hE hκ hc hτ hn₀ ht0 hSize hB hR k hk
  have hc₀ : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  have hn₀0 : (0 : ℝ) < n₀ := lt_trans (div_pos (by norm_num) hc₀) hn₀
  have hp : 30 / (n₀ : ℝ) < min (2 * c) τ := by
    rw [div_lt_iff₀ hn₀0]; rw [div_lt_iff₀ hc₀] at hn₀; linarith
  set c₀ : ℝ := min (2 * c) τ with hc₀def
  set p : ℝ := 30 / (n₀ : ℝ) with hpdef
  have hp0 : 0 ≤ p := by positivity
  -- uniform lower bound on `Im m^{(E n)}`
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  set μ : ℝ := Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hμdef
  have hμ : 0 < μ := by
    have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  have hmμ : ∀ n, μ ≤ (spectralM (E n)).im := fun n => by
    rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith
  -- the exponent gap: `N^{c₀ - p} → ∞`
  have hS : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop := hSize
  have hF3 : ∀ᶠ n : ℕ in atTop, μ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ - p) :=
    ((tendsto_rpow_atTop (sub_pos.2 hp)).comp hS).eventually_ge_atTop _
  have hk1 : ((k : ℝ) + 1) / n₀ ≤ 1 := by
    rw [div_le_one hn₀0]; exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / n₀ := by positivity
  have hk10 : (k : ℝ) / n₀ ≤ ((k : ℝ) + 1) / n₀ :=
    div_le_div_of_nonneg_right (by linarith) hn₀0.le
  have key : ∀ᶠ n : ℕ in atTop,
      (((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - chainTime t n₀ (k + 1) n) ∧
      (scaleM (d.L n) (d.W n) (E n) (chainTime t n₀ k n))⁻¹ ≤
        ((1 - chainTime t n₀ (k + 1) n) / (1 - chainTime t n₀ k n)) ^ 30 := by
    filter_upwards [hB, hR, hF3] with n hBn hRn hF3n
    have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := sf_one_le_size d n
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
    have htlt : t n < 1 := sf_lt_one_of_range d hRn
    have hE' : |E n| < 2 := by linarith [hE n]
    have hxpos : 0 < 1 - t n := by linarith
    have hx1 : 1 - t n ≤ 1 := by have := ht0 n; linarith
    have hcs : chainTime t n₀ k n = 1 - (1 - t n) ^ ((k : ℝ) / n₀) := rfl
    have hcs1 : chainTime t n₀ (k + 1) n = 1 - (1 - t n) ^ (((k : ℝ) + 1) / n₀) := by
      unfold chainTime; push_cast; rfl
    have hxe2 : 1 - t n ≤ (1 - t n) ^ (((k : ℝ) + 1) / n₀) :=
      Real.self_le_rpow_of_le_one hxpos.le hx1 hk1
    have hxe1 : 1 - t n ≤ (1 - t n) ^ ((k : ℝ) / n₀) :=
      Real.self_le_rpow_of_le_one hxpos.le hx1 (hk10.trans hk1)
    have hxe1pos : 0 < (1 - t n) ^ ((k : ℝ) / n₀) := Real.rpow_pos_of_pos hxpos _
    have hR2 : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - chainTime t n₀ (k + 1) n := by
      rw [hcs1]; linarith
    refine ⟨hR2, ?_⟩
    have hsk1 : chainTime t n₀ k n < 1 := by rw [hcs]; linarith
    have hskt : chainTime t n₀ k n ≤ t n := by rw [hcs]; linarith
    -- `M_{s_k} ≥ M_t ≥ Im m N^{c₀}`
    have hM1 : scaleM (d.L n) (d.W n) (E n) (t n) ≤
        scaleM (d.L n) (d.W n) (E n) (chainTime t n₀ k n) :=
      (scaleM_anti_ratio (W := d.W n) (sf_one_le_L d n) hE' hskt htlt).1
    have hM2 : (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ c₀ ≤
        scaleM (d.L n) (d.W n) (E n) (t n) :=
      (scaleM_etaT_of_range (sf_one_le_L d n) (sf_one_le_W d n) hE' hc hτ htlt hBn hRn).1
    -- `N^p ≤ μ N^{c₀}`
    have hNp : 0 < ((d.size n : ℕ) : ℝ) ^ p := Real.rpow_pos_of_pos hN0 _
    have hsplit : ((d.size n : ℕ) : ℝ) ^ c₀ =
        ((d.size n : ℕ) : ℝ) ^ p * ((d.size n : ℕ) : ℝ) ^ (c₀ - p) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hNpμ : ((d.size n : ℕ) : ℝ) ^ p ≤ μ * ((d.size n : ℕ) : ℝ) ^ c₀ := by
      have h1 : ((d.size n : ℕ) : ℝ) ^ p * μ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ c₀ := by
        rw [hsplit]; exact mul_le_mul_of_nonneg_left hF3n hNp.le
      calc ((d.size n : ℕ) : ℝ) ^ p
          = ((d.size n : ℕ) : ℝ) ^ p * μ⁻¹ * μ := by field_simp
        _ ≤ ((d.size n : ℕ) : ℝ) ^ c₀ * μ := mul_le_mul_of_nonneg_right h1 hμ.le
        _ = μ * ((d.size n : ℕ) : ℝ) ^ c₀ := mul_comm _ _
    have hNc0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ c₀ := Real.rpow_nonneg hN0.le _
    have hNpM : ((d.size n : ℕ) : ℝ) ^ p ≤
        scaleM (d.L n) (d.W n) (E n) (chainTime t n₀ k n) :=
      hNpμ.trans ((mul_le_mul_of_nonneg_right (hmμ n) hNc0).trans (hM2.trans hM1))
    have hinv := inv_anti₀ hNp hNpM
    -- `((1 - s_{k+1})/(1 - s_k))^30 = (1 - t)^p ≥ N^{-p}`
    have hratio : ((1 - chainTime t n₀ (k + 1) n) / (1 - chainTime t n₀ k n)) ^ 30 =
        (1 - t n) ^ p := by
      rw [hcs, hcs1]
      have e1 : 1 - (1 - (1 - t n) ^ (((k : ℝ) + 1) / n₀)) = (1 - t n) ^ (((k : ℝ) + 1) / n₀) := by
        ring
      have e2 : 1 - (1 - (1 - t n) ^ ((k : ℝ) / n₀)) = (1 - t n) ^ ((k : ℝ) / n₀) := by ring
      rw [e1, e2, ← Real.rpow_sub hxpos, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      congr 1
      rw [hpdef]; push_cast; field_simp; ring
    have hxN : ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ 1 - t n :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hRn
    have hxp : (((d.size n : ℕ) : ℝ) ^ (-1 : ℝ)) ^ p ≤ (1 - t n) ^ p :=
      Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hxN hp0
    have hNneg : (((d.size n : ℕ) : ℝ) ^ (-1 : ℝ)) ^ p = (((d.size n : ℕ) : ℝ) ^ p)⁻¹ := by
      rw [← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]; ring_nf
    rw [hratio]
    calc _ ≤ (((d.size n : ℕ) : ℝ) ^ p)⁻¹ := hinv
      _ = (((d.size n : ℕ) : ℝ) ^ (-1 : ℝ)) ^ p := hNneg.symm
      _ ≤ (1 - t n) ^ p := hxp
  exact ⟨key.mono fun n h => h.2, key.mono fun n h => h.1⟩

/-! ## 7. Step 5, near case: `M_u^{-2} ≤ exp(√6 (log W)^{3/4}) 𝒯_{u,D}(ℓ)` for `ℓ ≤ 6 ℓ*_u` -/

/-- The near region of Step 5 (`|a₁ - a₂|_L ≤ 6 ℓ*`): for `ℓ ≤ 6 ℓ*_u`,
`(M_u²)⁻¹ ≤ exp(√6 (log W)^{3/4}) · 𝒯_{u,D}(ℓ)`.  The constants `6` and `3/4` are those of the
one-dimensional argument; no hypothesis beyond
`1 ≤ L`, `1 ≤ W`, `u < 1`. -/
theorem scaleFacts_inv_sq_le_tailT {L W : ℕ} {E D u ℓ : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hu : u < 1)
    (hℓ : ℓ ≤ 6 * ellStar L W u) :
    (scaleM L W E u ^ 2)⁻¹ ≤
      Real.exp (Real.sqrt 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) * tailT L W E D u ℓ := by
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hlog : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg hW'
  have hℓu : 0 < ellT L u := (ellT_pos_le hL hu).1
  have hdiv : ℓ / ellT L u ≤ 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [div_le_iff₀ hℓu]
    calc ℓ ≤ 6 * ellStar L W u := hℓ
      _ = 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) * ellT L u := by unfold ellStar; ring
  have hS : Real.sqrt (ℓ / ellT L u) ≤ Real.sqrt 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4) := by
    calc Real.sqrt (ℓ / ellT L u) ≤ Real.sqrt (6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 2)) :=
          Real.sqrt_le_sqrt hdiv
      _ = Real.sqrt 6 * Real.sqrt (Real.log (W : ℝ) ^ ((3 : ℝ) / 2)) :=
          Real.sqrt_mul (by norm_num) _
      _ = Real.sqrt 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [Real.sqrt_eq_rpow (Real.log (W : ℝ) ^ ((3 : ℝ) / 2)), ← Real.rpow_mul hlog]; norm_num
  set A : ℝ := (scaleM L W E u ^ 2)⁻¹ with hA
  have hA0 : 0 ≤ A := inv_nonneg.2 (sq_nonneg _)
  set a : ℝ := Real.sqrt 6 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4) with ha
  set S : ℝ := Real.sqrt (ℓ / ellT L u) with hSdef
  have hexp : 1 ≤ Real.exp a * Real.exp (-S) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
  unfold tailT
  calc A = A * 1 := (mul_one A).symm
    _ ≤ A * (Real.exp a * Real.exp (-S)) := mul_le_mul_of_nonneg_left hexp hA0
    _ = Real.exp a * (A * Real.exp (-S)) := by ring
    _ ≤ Real.exp a * (A * Real.exp (-S) + (W : ℝ) ^ (-D)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le

end RBM.Ind
