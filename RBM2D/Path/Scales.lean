/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.SpectralWindow

/-!
# The Step 2 scales `η_u`, `ℓ_u`, `M_u`, `𝒯_{u,D}`, `ℓ*_u`

The five definitions `etaT`, `ellT`, `scaleM`, `tailT`, `ellStar`.  They live in `RBM.Path`, not
in `RBM`, because `RBM.KLoop` has its own `etaT`, `ellT`.

Paper: arXiv:2503.07606, `eta`, `eq:bcal_k`, `con_st_ind`.
The paper writes `|1 - u|`; the definitions use `1 - u`, and every theorem assumes `u < 1`.

Results (notation `x_u = 1 - u`, `m' = Im m^{(E)}`, `N = (W L)²`):
1. positivity and range: `etaT_pos`, `ellT_pos_le`, `one_le_ellT`, `scaleM_pos`, `tailT_pos`;
2. `etaT_div_etaT`: `η_s / η_u = x_s / x_u`;
3. `scaleM_eq`, `scaleM_eq'`: `M_u = W² m' min(1, L² x_u) = m' min(W², N x_u)`;
4. `ellT_mono_ratio`: `ℓ_s ≤ ℓ_u` and `ℓ_u / ℓ_s ≤ (x_s / x_u)^{1/2}`;
5. `scaleM_anti_ratio`: `M_v ≤ M_s` and `M_s x_v / x_s ≤ M_v`;
6. `scaleM_ge_pow29`: from `M_s⁻¹ ≤ (x_t / x_s)^30`, `(x_s / x_v)^29 ≤ M_v`;
7. `scaleM_etaT_of_range`: `m' N^{min(2c, τ)} ≤ M_t` and `η_t⁻¹ ≤ N^{1-τ} / m'`.
-/

noncomputable section

namespace RBM.Path

open RBM RBM.Gauss

/-! ## Definitions -/

/-- `η_u = (1 - u) Im m^{(E)}` (`eta`). -/
def etaT (E u : ℝ) : ℝ := (1 - u) * (spectralM E).im

/-- `ℓ_u = min((1-u)^{-1/2}, L)` (`eq:bcal_k`). -/
def ellT (L : ℕ) (u : ℝ) : ℝ := min (1 / Real.sqrt (1 - u)) (L : ℝ)

/-- `M_u = W² ℓ_u² η_u` (`eq:bcal_k`; `def_meta`). -/
def scaleM (L W : ℕ) (E u : ℝ) : ℝ := (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u

/-- `𝒯_{u,D}(ℓ) = M_u^{-2} exp(-(ℓ/ℓ_u)_+^{1/2}) + W^{-D}` (`def_WTuD`).
`Real.sqrt` of a negative number is `0`, which is the positive part. -/
def tailT (L W : ℕ) (E D u ℓ : ℝ) : ℝ :=
  (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (ℓ / ellT L u)) + (W : ℝ) ^ (-D)

/-- `ℓ*_u = (log W)^{3/2} ℓ_u` (the definition before Lemma `lem_dec_calE_0`). -/
def ellStar (L W : ℕ) (u : ℝ) : ℝ := Real.log (W : ℝ) ^ ((3 : ℝ) / 2) * ellT L u

/-! ## 1. Positivity and range -/

/-- `0 < η_u` for `|E| < 2`, `u < 1`. -/
theorem etaT_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (spectralM_im_pos hE)

/-- `0 < ℓ_u ≤ L` for `1 ≤ L`, `u < 1`. -/
theorem ellT_pos_le {L : ℕ} {u : ℝ} (hL : 1 ≤ L) (hu : u < 1) :
    0 < ellT L u ∧ ellT L u ≤ L := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 (by linarith)
  refine ⟨lt_min (by positivity) (by linarith), min_le_right _ _⟩

/-- `1 ≤ ℓ_u` for `1 ≤ L`, `0 ≤ u < 1`. -/
theorem one_le_ellT {L : ℕ} {u : ℝ} (hL : 1 ≤ L) (hu0 : 0 ≤ u) (hu : u < 1) :
    1 ≤ ellT L u := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 (by linarith)
  have hsq1 : Real.sqrt (1 - u) ≤ 1 := by
    calc Real.sqrt (1 - u) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  exact le_min (one_le_one_div hsq hsq1) hL'

/-- `0 < M_u` for `1 ≤ L`, `1 ≤ W`, `|E| < 2`, `u < 1`. -/
theorem scaleM_pos {L W : ℕ} {E u : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2) (hu : u < 1) :
    0 < scaleM L W E u := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  exact mul_pos (mul_pos (pow_pos hW' 2) (pow_pos (ellT_pos_le hL hu).1 2)) (etaT_pos hE hu)

/-- `0 < 𝒯_{u,D}(ℓ)` for `1 ≤ W`, for all `L, E, D, u, ℓ`. -/
theorem tailT_pos {W : ℕ} (hW : 1 ≤ W) (L : ℕ) (E D u ℓ : ℝ) : 0 < tailT L W E D u ℓ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le) (Real.rpow_pos_of_pos hW' _)

/-! ## 2. Ratio -/

/-- `η_s / η_u = (1 - s) / (1 - u)` for `|E| < 2`, `s, u < 1`. -/
theorem etaT_div_etaT {E s u : ℝ} (hE : |E| < 2) (_hs : s < 1) (_hu : u < 1) :
    etaT E s / etaT E u = (1 - s) / (1 - u) :=
  mul_div_mul_right _ _ (spectralM_im_pos hE).ne'

/-! ## 3. Closed form of `M` -/

/-- `ℓ_u² = min(1/(1-u), L²)` for `u < 1`. -/
private theorem ellT_sq {L : ℕ} {u : ℝ} (hu : u < 1) :
    ellT L u ^ 2 = min (1 / (1 - u)) ((L : ℝ) ^ 2) := by
  have hx : 0 < 1 - u := by linarith
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have ha : (1 / Real.sqrt (1 - u)) ^ 2 = 1 / (1 - u) := by
    rw [div_pow, one_pow, Real.sq_sqrt hx.le]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  unfold ellT
  rcases le_total (1 / Real.sqrt (1 - u)) (L : ℝ) with h | h
  · rw [min_eq_left h, ha, min_eq_left]
    rw [← ha]; exact pow_le_pow_left₀ (by positivity) h 2
  · rw [min_eq_right h, min_eq_right]
    rw [← ha]; exact pow_le_pow_left₀ hL0 h 2

/-- `M_u = W² Im m · min(1, L² (1 - u))` for `1 ≤ L`, `u < 1`. -/
theorem scaleM_eq {L W : ℕ} {E u : ℝ} (_hL : 1 ≤ L) (hu : u < 1) :
    scaleM L W E u = (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u)) := by
  have hx : 0 < 1 - u := by linarith
  calc scaleM L W E u
      = (W : ℝ) ^ 2 * (spectralM E).im * (min (1 / (1 - u)) ((L : ℝ) ^ 2) * (1 - u)) := by
        unfold scaleM etaT; rw [ellT_sq hu]; ring
    _ = (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u)) := by
        rw [min_mul_of_nonneg _ _ hx.le, one_div_mul_cancel hx.ne']

/-- `M_u = Im m · min(W², N (1 - u))` with `N = (W L)²`, for `1 ≤ L`, `u < 1`. -/
theorem scaleM_eq' {L W : ℕ} {E u : ℝ} (hL : 1 ≤ L) (hu : u < 1) :
    scaleM L W E u =
      (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) := by
  have h : (((W * L) ^ 2 : ℕ) : ℝ) * (1 - u) = (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (1 - u)) := by
    push_cast; ring
  rw [scaleM_eq hL hu, h, mul_comm ((W : ℝ) ^ 2) _, mul_assoc,
    mul_min_of_nonneg _ _ (sq_nonneg (W : ℝ)), mul_one]

/-! ## 4. Monotonicity of `ℓ` -/

/-- `ℓ_s ≤ ℓ_u` and `ℓ_u / ℓ_s ≤ ((1 - s)/(1 - u))^{1/2}` for `1 ≤ L`, `0 ≤ s ≤ u < 1`. -/
theorem ellT_mono_ratio {L : ℕ} {s u : ℝ} (hL : 1 ≤ L) (_hs0 : 0 ≤ s) (hsu : s ≤ u)
    (hu : u < 1) :
    ellT L s ≤ ellT L u ∧ ellT L u / ellT L s ≤ ((1 - s) / (1 - u)) ^ ((1 : ℝ) / 2) := by
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hsqu : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hxu
  have hsqs : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 hxs
  have hmono : 1 / Real.sqrt (1 - s) ≤ 1 / Real.sqrt (1 - u) :=
    one_div_le_one_div_of_le hsqu (Real.sqrt_le_sqrt (by linarith))
  refine ⟨min_le_min hmono le_rfl, ?_⟩
  have hℓs : 0 < ellT L s := (ellT_pos_le hL (by linarith)).1
  rw [← Real.sqrt_eq_rpow, div_le_iff₀ hℓs, Real.sqrt_div hxs.le]
  unfold ellT
  rcases le_total (1 / Real.sqrt (1 - s)) (L : ℝ) with h | h
  · rw [min_eq_left h]
    calc min (1 / Real.sqrt (1 - u)) (L : ℝ) ≤ 1 / Real.sqrt (1 - u) := min_le_left _ _
      _ = Real.sqrt (1 - s) / Real.sqrt (1 - u) * (1 / Real.sqrt (1 - s)) := by
        field_simp
  · rw [min_eq_right h]
    have h1 : 1 ≤ Real.sqrt (1 - s) / Real.sqrt (1 - u) :=
      (one_le_div hsqu).2 (Real.sqrt_le_sqrt (by linarith))
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    calc min (1 / Real.sqrt (1 - u)) (L : ℝ) ≤ L := min_le_right _ _
      _ ≤ Real.sqrt (1 - s) / Real.sqrt (1 - u) * L := le_mul_of_one_le_left hL0 h1

/-! ## 5. Monotonicity of `M` -/

/-- `M_v ≤ M_s` and `M_s (1 - v)/(1 - s) ≤ M_v` for `1 ≤ L`, `|E| < 2`, `s ≤ v < 1`. -/
theorem scaleM_anti_ratio {L W : ℕ} {E s v : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hsv : s ≤ v)
    (hv : v < 1) :
    scaleM L W E v ≤ scaleM L W E s ∧ scaleM L W E s * (1 - v) / (1 - s) ≤ scaleM L W E v := by
  have hxv : 0 < 1 - v := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hC : 0 ≤ (W : ℝ) ^ 2 * (spectralM E).im :=
    mul_nonneg (sq_nonneg _) (spectralM_im_pos hE).le
  rw [scaleM_eq hL hv, scaleM_eq hL (by linarith)]
  refine ⟨mul_le_mul_of_nonneg_left
    (min_le_min le_rfl (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))) hC, ?_⟩
  have hρ0 : 0 ≤ (1 - v) / (1 - s) := div_nonneg hxv.le hxs.le
  have hρ1 : (1 - v) / (1 - s) ≤ 1 := (div_le_one hxs).2 (by linarith)
  have hmin : min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s)) ≤
      min 1 ((L : ℝ) ^ 2 * (1 - v)) := by
    refine le_min ?_ ?_
    · calc min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s)) ≤ 1 * 1 :=
            mul_le_mul (min_le_left _ _) hρ1 hρ0 zero_le_one
        _ = 1 := one_mul 1
    · calc min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s))
          ≤ (L : ℝ) ^ 2 * (1 - s) * ((1 - v) / (1 - s)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hρ0
        _ = (L : ℝ) ^ 2 * (1 - v) := by field_simp
  calc (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - s)) * (1 - v) / (1 - s)
      = (W : ℝ) ^ 2 * (spectralM E).im *
          (min 1 ((L : ℝ) ^ 2 * (1 - s)) * ((1 - v) / (1 - s))) := by ring
    _ ≤ (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - v)) :=
        mul_le_mul_of_nonneg_left hmin hC

/-! ## 6. Lower bound of `M` under the step condition -/

/-- Under the step condition `M_s⁻¹ ≤ ((1 - t)/(1 - s))^30` (`con_st_ind`),
`((1 - s)/(1 - v))^29 ≤ M_v` for `0 ≤ s ≤ v ≤ t < 1`. -/
theorem scaleM_ge_pow29 {L W : ℕ} {E s v t : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (_hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t) (ht : t < 1)
    (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    ((1 - s) / (1 - v)) ^ 29 ≤ scaleM L W E v := by
  have hxt : 0 < 1 - t := by linarith
  have hxv : 0 < 1 - v := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hMs : 0 < scaleM L W E s := scaleM_pos hL hW hE (by linarith)
  have hq : 0 < ((1 - t) / (1 - s)) ^ 30 := pow_pos (div_pos hxt hxs) 30
  -- `r^30 ≤ M_s` with `r = x_s / x_t`
  have hr : ((1 - s) / (1 - t)) ^ 30 ≤ scaleM L W E s := by
    have := (inv_le_comm₀ hMs hq).1 hstep
    rwa [← inv_pow, inv_div] at this
  -- `r_v ≤ r`
  have hrv : (1 - s) / (1 - v) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_left hxs.le hxt (by linarith)
  have hrv0 : 0 ≤ (1 - s) / (1 - v) := div_nonneg hxs.le hxv.le
  have h30 : ((1 - s) / (1 - v)) ^ 30 ≤ scaleM L W E s :=
    (pow_le_pow_left₀ hrv0 hrv 30).trans hr
  have hF2 := (scaleM_anti_ratio (W := W) hL hE hsv (by linarith)).2
  calc ((1 - s) / (1 - v)) ^ 29 = ((1 - s) / (1 - v)) ^ 30 * ((1 - v) / (1 - s)) := by
        field_simp
    _ ≤ scaleM L W E s * ((1 - v) / (1 - s)) :=
        mul_le_mul_of_nonneg_right h30 (div_nonneg hxv.le hxs.le)
    _ = scaleM L W E s * (1 - v) / (1 - s) := by ring
    _ ≤ scaleM L W E v := hF2

/-! ## 7. Scales on the application range -/

/-- With `N = (W L)²`, the bandwidth condition `N^c ≤ W` and the range condition
`N^{-1+τ} ≤ 1 - t` give `Im m · N^{min(2c, τ)} ≤ M_t` and `η_t⁻¹ ≤ N^{1-τ} / Im m`. -/
theorem scaleM_etaT_of_range {L W : ℕ} {E c τ t : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (_hc : 0 < c) (_hτ : 0 < τ) (ht : t < 1)
    (hcW : (((W * L) ^ 2 : ℕ) : ℝ) ^ c ≤ W)
    (hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t) :
    (spectralM E).im * (((W * L) ^ 2 : ℕ) : ℝ) ^ (min (2 * c) τ) ≤ scaleM L W E t ∧
      (etaT E t)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ (1 - τ) / (spectralM E).im := by
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW hL)
    rw [hNdef]; exact_mod_cast this
  have hN0 : 0 < N := by linarith
  refine ⟨?_, ?_⟩
  · rw [scaleM_eq' hL ht, ← hNdef]
    refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) hm.le
    · calc N ^ (min (2 * c) τ) ≤ N ^ (2 * c) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)
        _ = (N ^ c) ^ 2 := by rw [mul_comm, Real.rpow_mul hN0.le, Real.rpow_two]
        _ ≤ (W : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hcW 2
    · calc N ^ (min (2 * c) τ) ≤ N ^ τ :=
            Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)
        _ = N ^ ((1 : ℝ) + (-1 + τ)) := by ring_nf
        _ = N * N ^ (-1 + τ) := by rw [Real.rpow_add hN0, Real.rpow_one]
        _ ≤ N * (1 - t) := mul_le_mul_of_nonneg_left hrange hN0.le
  · have hpos : 0 < N ^ (-1 + τ) * (spectralM E).im :=
      mul_pos (Real.rpow_pos_of_pos hN0 _) hm
    have hle : N ^ (-1 + τ) * (spectralM E).im ≤ etaT E t :=
      mul_le_mul_of_nonneg_right hrange hm.le
    calc (etaT E t)⁻¹ ≤ (N ^ (-1 + τ) * (spectralM E).im)⁻¹ := inv_anti₀ hpos hle
      _ = N ^ (1 - τ) / (spectralM E).im := by
          rw [show (-1 + τ) = -(1 - τ) by ring, Real.rpow_neg hN0.le, mul_inv, inv_inv,
            div_eq_mul_inv]

end RBM.Path
