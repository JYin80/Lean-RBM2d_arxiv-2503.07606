/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Induction.ConArg
import RBM2D.Induction.Continuity
import RBM2D.Induction.ScaleFacts
import RBM2D.Induction.PerTimeCalc
import RBM2D.Induction.Split
import RBM2D.Green.Pins
import RBM2D.Path.ScalesBridge
import RBM2D.Gauss.GreenTimeCont

/-!
# Step 1 of `lem:main_ind`: (`lRB1`) and (`Gtmwc`) uniformly in `u ∈ [s,t]`

The statement `Step1TargetV3` (with `GbEXPHypV3` written `Green.GbEXPHypV3`); `step1` proves it
for every size sequence `d`, every `κ, c, τ` and every `E, s, t`.

Paper: arXiv:2503.07606, Section 5, Step 1 of the proof of Theorem `lem:main_ind`; (`lRB1`),
(`Gtmwc`) are in Section 2.

## Proof

The proof is that of the one-dimensional formalization, rewired to the `d = 2` inputs.  The net
lift, Lemma 4.1 along the flow and the time continuity are hypotheses of the one-dimensional
version; here the net is rebuilt and the other two inputs are `GbEXPHypV3` (`lem_GbEXP`, one time
per size sequence) and the samplewise continuity of the resolvent.

* `s1T1` is the start time; `s1_loop_det` is (`Lboundfor1/2`) at `u ≤ 1/2`
  (`norm_gloop_le_of_le_abs_im`, weight `W⁻²` instead of `W⁻¹`); `s1_Kbound_seq`, `s1_h55`: (55) at
  `t₁ = max(s, 1/2)`.
* `s1_LI`: (`jsajufua`) along a time sequence, the three-case split done pointwise; the input of
  Lemma 5.1 is `conArg`.
* `s1_ratio_pt`, `s1_F3`--`s1_F8`: the arithmetic of the forbidden region and of the initial
  datum, with the scale facts `M_u ≥ M_s^{29/30}`, `(ℓ_u/ℓ_s)² ≤ M_s^{1/30}`,
  `M_s ≥ Im m · N^{min(2c,τ)}`.
* `s1_wl_seq`, `s1_forb`, `s1_boot`: the per-time forbidden region (`lem_GbEXP` with `n = 2` and
  (5.8)), the union bound over a polynomial net of `[s,t]` with
  `PerTimeCalc.Unif.forbidden_region` and `gopbound` (`Gopboundu`), and `stepOneBootstrap` (the net
  is the one of the private `contTime` of `Continuity`).
* `s1_weakPT`, `s1_loopPT`, `step1`, with the net lift `step1NetLift`.

The indicator that appears is `1(‖G_u - m‖_max ≤ 2 M_s^{-1/4}) ⊆ {‖G_u‖_max ≤ 2}`, so the
threshold `2` of `conArg` suffices.

## Differences from the one-dimensional argument (`d = 2`, and the per-time hypotheses)

* The forbidden region is `[M_s^{-1/4}/2, 2 M_s^{-1/4}]` (constant in `u`, at the points of the
  net) and the bound is `6 M_s^{-7/15}` (constant in `u`); this gives `‖G_u - m‖_max < M_s^{-1/4}
  ≤ M_u^{-1/4}` for all `u ∈ [s,t]` (`M_u ≤ M_s`), which is what (`Gtmwc`) needs, and no ratio of
  scales at nearby times is needed.  The exponents are those of the paper with
  `d = 2` scales `M = W² ℓ² η`: `(ℓ_u/ℓ_s)² M_u⁻¹ ≤ M_s^{-14/15}` (from `con_st_ind`,
  exponent `30`).
* Case 1 (`t ≤ 1/2`) of the paper is not treated separately: (`Lboundfor1/2`) gives
  (`jsajufua`) for `u < 1/2` and the same forbidden-region argument covers all `u ∈ [s,t]`; the
  intermediate bound (`Gtmt12`) is not derived.
* `InitDecay` is not used; `InitLK` (for `s ≥ 1/2`), `KboundConcl` (at `κ`), `InitLocal` are.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The statement of Step 1**, with
`GbEXPHyp d (κ/2)` replaced by `GbEXPHypV3 d (κ/2) c τ` (the `c` and `τ` of `MainIndHyp`).
Paper: Step 1 of `lem:main_ind` (uses of `lem_GbEXP`). -/
def Step1TargetV3 (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  KboundConcl κ → Green.GbEXPHypV3 d (κ / 2) c τ → MainIndHyp d κ c τ E s t →
    Step1LoopUnif d E s t ∧ Step1WeakLawUnif d E s t

/-! ## 1. Elementary facts -/

section Elementary

/-- Bulk energy: `|E| < 2` and `√(2κ)/2 ≤ Im m` for `|E| ≤ 2 - κ`. -/
private theorem s1_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    |E| < 2 ∧ Real.sqrt (2 * κ) / 2 ≤ (spectralM E).im := by
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hκ2 : κ ≤ 2 := by linarith
  refine ⟨by linarith, ?_⟩
  rw [spectralM_im]
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ hE0 hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

private theorem s1_im_le_one {E : ℝ} (hE : |E| ≤ 2) : (spectralM E).im ≤ 1 := by
  have h := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE] at h
  exact (le_abs_self _).trans h

private theorem s1_inv_rpow {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : x⁻¹ ^ p = x ^ (-p) := by
  rw [Real.rpow_neg hx, Real.inv_rpow hx]

/-- `K x^p ≤ x^q` from `K ≤ x^{q-p}`. -/
private theorem s1_mul_rpow_le {x K p q : ℝ} (hx : 0 < x) (h : K ≤ x ^ (q - p)) :
    K * x ^ p ≤ x ^ q := by
  have e : x ^ q = x ^ (q - p) * x ^ p := by rw [← Real.rpow_add hx]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le _)

private theorem s1_size_eq (n : ℕ) : ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
  simp [Sizes.size]

private theorem s1_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem s1_one_le_W (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem s1_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h : 1 ≤ d.size n :=
    Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))
  exact_mod_cast h

private theorem s1_W_sq_le_size (n : ℕ) : (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  rw [s1_size_eq, mul_pow]
  have h1 : (1 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast s1_one_le_L d n
  have h2 : (1 : ℝ) ≤ (d.L n : ℝ) ^ 2 := one_le_pow₀ h1
  nlinarith [sq_nonneg (d.W n : ℝ)]

private theorem s1_hsize (h : SizeTendsto d) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

/-- `M_u ≤ W²` (`Im m ≤ 1`). -/
private theorem s1_scaleM_le_W2 {L W : ℕ} (hL : 1 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu : u < 1) :
    scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  rw [scaleM_eq' hL hu]
  have hm := s1_im_le_one hE
  have hm0 : 0 ≤ (spectralM E).im := by rw [spectralM_im]; positivity
  have h1 : min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) ≤ (W : ℝ) ^ 2 := min_le_left _ _
  have h0 : 0 ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) :=
    le_min (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  calc (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u))
      ≤ 1 * (W : ℝ) ^ 2 := mul_le_mul hm h1 h0 zero_le_one
    _ = _ := one_mul _

/-- The deterministic ratio fact behind Step 1 (`ℓ_u ℓ_s^{-1} ≤ M_s^{1/60}`):
`(ℓ_u/ℓ_s)² M_u⁻¹ ≤ M_s^{-14/15}` for `0 ≤ s ≤ u ≤ t < 1` under `con_st_ind` at `(s,t)`. -/
private theorem s1_ratio_pt {L W : ℕ} {E s u t : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1)
    (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ≤ scaleM L W E s ^ (-((14 : ℝ) / 15)) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hMs : 0 < scaleM L W E s := scaleM_pos hL hW hE hs1
  have hMu : 0 < scaleM L W E u := scaleM_pos hL hW hE hu1
  set Ms := scaleM L W E s with hMsdef
  set ρ : ℝ := (1 - s) / (1 - t) with hρdef
  have hρ0 : 0 < ρ := div_pos hxs hxt
  -- `ρ^30 ≤ Ms`
  have hρ30 : ρ ^ 30 ≤ Ms := by
    have h1 : ((1 - t) / (1 - s)) ^ 30 = (ρ ^ 30)⁻¹ := by
      rw [hρdef, ← inv_pow, inv_div]
    rw [h1] at hstep
    have h2 : 0 < ρ ^ 30 := pow_pos hρ0 30
    exact (inv_le_inv₀ hMs h2).1 hstep |>.trans_eq' rfl
  -- `ρ ≤ Ms^{1/30}`
  have hρle : ρ ≤ Ms ^ ((1 : ℝ) / 30) := by
    have h1 : ρ = (ρ ^ 30) ^ ((1 : ℝ) / 30) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]; norm_num
    calc ρ = (ρ ^ 30) ^ ((1 : ℝ) / 30) := h1
      _ ≤ Ms ^ ((1 : ℝ) / 30) :=
          Real.rpow_le_rpow (pow_nonneg hρ0.le 30) hρ30 (by norm_num)
  -- `(ℓ_u/ℓ_s)² ≤ ρ`
  have hr : (ellT L u / ellT L s) ^ 2 ≤ ρ := by
    have hpos : 0 < ellT L u / ellT L s :=
      div_pos (ellT_pos_le hL hu1).1 (ellT_pos_le hL hs1).1
    have h := scaleFacts_ellT_ratio hL hs0 hsu hut ht
    have h2 : (ellT L u / ellT L s) ^ 2 ≤ (ρ ^ ((1 : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ hpos.le h 2
    have h3 : (ρ ^ ((1 : ℝ) / 2)) ^ 2 = ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]; norm_num
    exact h2.trans_eq h3
  -- `M_u ≥ Ms^{29/30}`
  have hMu29 := scaleFacts_R2_pt hL hW hE hsu hut ht hstep
  have hinv : (scaleM L W E u)⁻¹ ≤ Ms ^ (-((29 : ℝ) / 30)) := by
    rw [Real.rpow_neg hMs.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hMs _) hMu29
  calc (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹
      ≤ Ms ^ ((1 : ℝ) / 30) * Ms ^ (-((29 : ℝ) / 30)) :=
        mul_le_mul (hr.trans hρle) hinv (inv_nonneg.2 hMu.le) (Real.rpow_nonneg hMs.le _)
    _ = Ms ^ (-((14 : ℝ) / 15)) := by
        rw [← Real.rpow_add hMs]; congr 1; norm_num

end Elementary

/-! ## 2. The standing hypotheses and the scale facts along the window -/

section Scales

/-- The deterministic hypotheses of `MainIndHyp` (all but the three initial-data clauses). -/
private structure S1Std (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop where
  hκ : 0 < κ
  hE : ∀ n, |E n| ≤ 2 - κ
  hc : 0 < c
  hτ : 0 < τ
  hs0 : ∀ n, 0 ≤ s n
  hst : ∀ n, s n ≤ t n
  ht1 : ∀ n, t n < 1
  hN : SizeTendsto d
  hB : Bandwidth d c
  hCond : CondStInd d E s t
  hR : RangeCond d τ t

variable {d} {κ c τ : ℝ} {E s t : ℕ → ℝ}

private theorem s1_std_of_mainIndHyp (h : MainIndHyp d κ c τ E s t) : S1Std d κ c τ E s t := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hCond, hR, -, -, -⟩ := h
  exact ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hCond, hR⟩

private theorem s1_Ms_ge (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤
        scaleM (d.L n) (d.W n) (E n) u := by
  filter_upwards [scaleFacts_R1 d κ c τ E t h.hE h.hκ h.hc h.hτ h.hB h.hR] with n hn u hu
  refine le_trans ?_ (hn u hu)
  exact mul_le_mul_of_nonneg_right (s1_bulk h.hκ (h.hE n)).2
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem s1_Ms_tendsto (h : S1Std d κ c τ E s t) :
    Tendsto (fun n => scaleM (d.L n) (d.W n) (E n) (s n)) atTop atTop := by
  have hc0 : 0 < min (2 * c) τ := lt_min (by linarith [h.hc]) h.hτ
  have hc1 : 0 < Real.sqrt (2 * κ) / 2 := by
    have := Real.sqrt_pos.2 (by linarith [h.hκ] : 0 < 2 * κ); linarith
  have hS : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop := h.hN
  have h1 : Tendsto (fun n => Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ))
      atTop atTop := ((tendsto_rpow_atTop hc0).comp hS).const_mul_atTop hc1
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [s1_Ms_ge h] with n hn
  exact hn (s n) (h.hst n)

private theorem s1_Ms_pos (h : S1Std d κ c τ E s t) (n : ℕ) :
    0 < scaleM (d.L n) (d.W n) (E n) (s n) :=
  scaleM_pos (s1_one_le_L d n) (s1_one_le_W d n) (s1_bulk h.hκ (h.hE n)).1
    (lt_of_le_of_lt (h.hst n) (h.ht1 n))

private theorem s1_Mu_pos (h : S1Std d κ c τ E s t) (n : ℕ) {u : ℝ} (hu : u ≤ t n) :
    0 < scaleM (d.L n) (d.W n) (E n) u :=
  scaleM_pos (s1_one_le_L d n) (s1_one_le_W d n) (s1_bulk h.hκ (h.hE n)).1
    (lt_of_le_of_lt hu (h.ht1 n))

private theorem s1_Ms_ev_pow (h : S1Std d κ c τ E s t) {p : ℝ} (hp : 0 < p) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ scaleM (d.L n) (d.W n) (E n) (s n) ^ p :=
  ((tendsto_rpow_atTop hp).comp (s1_Ms_tendsto h)).eventually_ge_atTop K

private theorem s1_one_le_Ms (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scaleM (d.L n) (d.W n) (E n) (s n) :=
  (s1_Ms_tendsto h).eventually_ge_atTop 1

/-- (`con_st_ind`) `(ℓ_u/ℓ_s)² M_u⁻¹ ≤ M_s^{-14/15}`, uniformly in `u ∈ [s,t]`, eventually. -/
private theorem s1_ratio_ev (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      (ellT (d.L n) u / ellT (d.L n) (s n)) ^ 2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤
        scaleM (d.L n) (d.W n) (E n) (s n) ^ (-((14 : ℝ) / 15)) := by
  filter_upwards [h.hCond] with n hn u hsu hut
  exact s1_ratio_pt (s1_one_le_L d n) (s1_one_le_W d n) (s1_bulk h.hκ (h.hE n)).1 (h.hs0 n)
    hsu hut (h.ht1 n) hn

/-- `M_{s_n}` at the energy `E n`. -/
private abbrev s1Ms (d : Sizes) (E s : ℕ → ℝ) (n : ℕ) : ℝ := scaleM (d.L n) (d.W n) (E n) (s n)

/-- From `c₁ N^{c₀} ≤ M` : `N^{c₀ q} ≤ (c₁⁻¹)^q M^q` for `q ≥ 0`. -/
private theorem s1_Npow_le {N Ms c₁ c₀ : ℝ} (hN : 0 ≤ N) (hc₁ : 0 < c₁) (hM : c₁ * N ^ c₀ ≤ Ms)
    {q : ℝ} (hq : 0 ≤ q) : N ^ (c₀ * q) ≤ (c₁⁻¹) ^ q * Ms ^ q := by
  have h1 : N ^ c₀ ≤ c₁⁻¹ * Ms := by
    rw [← div_eq_inv_mul, le_div_iff₀ hc₁]; linarith
  rw [Real.rpow_mul hN, ← Real.mul_rpow (inv_nonneg.2 hc₁.le) (le_trans (mul_nonneg hc₁.le
    (Real.rpow_nonneg hN _)) hM)]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hN _) h1 hq

private theorem s1_c1_pos (h : S1Std d κ c τ E s t) : 0 < Real.sqrt (2 * κ) / 2 := by
  have := Real.sqrt_pos.2 (by linarith [h.hκ] : 0 < 2 * κ); linarith

private theorem s1_c0_pos (h : S1Std d κ c τ E s t) : 0 < min (2 * c) τ :=
  lt_min (by linarith [h.hc]) h.hτ

/-- The exponent `τ₀` of the initial-data step: `N^{τ₀} M_s^{-1/2} < M_s^{-1/4}`, eventually. -/
private theorem s1_F3 (h : S1Std d κ c τ E s t) :
    ∃ τ₀ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ τ₀ * (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 2) <
        (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) := by
  have hc0 := s1_c0_pos h
  have hc1 := s1_c1_pos h
  refine ⟨min (2 * c) τ * (1 / 8), by positivity, ?_⟩
  filter_upwards [s1_Ms_ge h, s1_Ms_ev_pow h (p := (1 : ℝ) / 8) (by norm_num)
    ((Real.sqrt (2 * κ) / 2)⁻¹ ^ ((1 : ℝ) / 8) + 1)] with n hn1 hn2
  have hMs : 0 < s1Ms d E s n := s1_Ms_pos h n
  have h1 := s1_Npow_le (Nat.cast_nonneg (d.size n)) hc1 (hn1 (s n) (h.hst n))
    (q := (1 : ℝ) / 8) (by norm_num)
  have h8 : 0 < s1Ms d E s n ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hMs _
  have h2 : ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ * (1 / 8)) < s1Ms d E s n ^ ((1 : ℝ) / 4) := by
    have h3 : s1Ms d E s n ^ ((1 : ℝ) / 4) = s1Ms d E s n ^ ((1 : ℝ) / 8) * s1Ms d E s n ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hMs]; norm_num
    rw [h3]
    calc _ ≤ _ := h1
      _ < s1Ms d E s n ^ ((1 : ℝ) / 8) * s1Ms d E s n ^ ((1 : ℝ) / 8) := by
        rw [mul_comm]
        exact mul_lt_mul_of_pos_left (by linarith) h8
  rw [s1_inv_rpow hMs.le, s1_inv_rpow hMs.le]
  have h4 : s1Ms d E s n ^ (-((1 : ℝ) / 4)) =
      s1Ms d E s n ^ ((1 : ℝ) / 4) * s1Ms d E s n ^ (-((1 : ℝ) / 2)) := by
    rw [← Real.rpow_add hMs]; congr 1; norm_num
  rw [h4]
  exact mul_lt_mul_of_pos_right h2 (Real.rpow_pos_of_pos hMs _)

/-- The exponent `ε` of the gap `f ≪ a` at the net: `6 M_s^{-7/15} ≤ N^{-ε} (M_s^{-1/4}/2)`. -/
private theorem s1_F4 (h : S1Std d κ c τ E s t) :
    ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      6 * (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15) ≤
        ((d.size n : ℕ) : ℝ) ^ (-ε) * ((s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) / 2) := by
  have hc0 := s1_c0_pos h
  have hc1 := s1_c1_pos h
  refine ⟨min (2 * c) τ * (1 / 8), by positivity, ?_⟩
  filter_upwards [s1_Ms_ge h, s1_Ms_ev_pow h (p := (11 : ℝ) / 120) (by norm_num)
    (12 * (Real.sqrt (2 * κ) / 2)⁻¹ ^ ((1 : ℝ) / 8)), Eventually.of_forall (s1_one_le_size d)] with n hn1 hn2 hn3
  have hMs : 0 < s1Ms d E s n := s1_Ms_pos h n
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn3
  have h1 := s1_Npow_le hN0.le hc1 (hn1 (s n) (h.hst n)) (q := (1 : ℝ) / 8) (by norm_num)
  set ε := min (2 * c) τ * (1 / 8) with hε
  set X := ((d.size n : ℕ) : ℝ) ^ ε with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hXinv : ((d.size n : ℕ) : ℝ) ^ (-ε) = X⁻¹ := by rw [Real.rpow_neg hN0.le]
  -- `12 X ≤ M^{13/60}`
  have h2 : 12 * X ≤ s1Ms d E s n ^ ((13 : ℝ) / 60) := by
    have h3 : 12 * ((Real.sqrt (2 * κ) / 2)⁻¹ ^ ((1 : ℝ) / 8) * s1Ms d E s n ^ ((1 : ℝ) / 8)) ≤
        s1Ms d E s n ^ ((13 : ℝ) / 60) := by
      rw [← mul_assoc]
      refine s1_mul_rpow_le hMs (p := (1 : ℝ) / 8) ?_
      have : (13 : ℝ) / 60 - 1 / 8 = 11 / 120 := by norm_num
      rw [this]; exact hn2
    linarith [h1]
  -- rewrite the goal
  rw [s1_inv_rpow hMs.le, s1_inv_rpow hMs.le, hXinv]
  have h5 : s1Ms d E s n ^ (-((7 : ℝ) / 15)) =
      s1Ms d E s n ^ (-((1 : ℝ) / 4)) * s1Ms d E s n ^ (-((13 : ℝ) / 60)) := by
    rw [← Real.rpow_add hMs]; congr 1; norm_num
  have h6 : s1Ms d E s n ^ ((13 : ℝ) / 60) * s1Ms d E s n ^ (-((13 : ℝ) / 60)) = 1 := by
    rw [← Real.rpow_add hMs]; simp
  have hA : 0 < s1Ms d E s n ^ (-((1 : ℝ) / 4)) := Real.rpow_pos_of_pos hMs _
  have hB : 0 < s1Ms d E s n ^ (-((13 : ℝ) / 60)) := Real.rpow_pos_of_pos hMs _
  rw [h5]
  -- `12 X B ≤ 1`
  have h7 : 12 * X * s1Ms d E s n ^ (-((13 : ℝ) / 60)) ≤ 1 := by
    calc 12 * X * s1Ms d E s n ^ (-((13 : ℝ) / 60))
        ≤ s1Ms d E s n ^ ((13 : ℝ) / 60) * s1Ms d E s n ^ (-((13 : ℝ) / 60)) :=
          mul_le_mul_of_nonneg_right h2 hB.le
      _ = 1 := h6
  rw [← sub_nonneg]
  have : X⁻¹ * (s1Ms d E s n ^ (-((1 : ℝ) / 4)) / 2) -
      6 * (s1Ms d E s n ^ (-((1 : ℝ) / 4)) * s1Ms d E s n ^ (-((13 : ℝ) / 60))) =
      (X⁻¹ / 2) * s1Ms d E s n ^ (-((1 : ℝ) / 4)) *
        (1 - 12 * X * s1Ms d E s n ^ (-((13 : ℝ) / 60))) := by
    have hXne : X ≠ 0 := hX0.ne'
    field_simp
    ring
  rw [this]
  exact mul_nonneg (by positivity) (by linarith)

/-- The exponent `c'` of `Ω(u,c')`: `2 M_s^{-1/4} ≤ W^{-c'}`, eventually. -/
private theorem s1_F5 (h : S1Std d κ c τ E s t) :
    ∃ c' > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      2 * (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) ≤ (d.W n : ℝ) ^ (-c') := by
  have hc0 := s1_c0_pos h
  have hc1 := s1_c1_pos h
  refine ⟨min (2 * c) τ * (1 / 4), by positivity, ?_⟩
  filter_upwards [s1_Ms_ge h, s1_Ms_ev_pow h (p := (1 : ℝ) / 8) (by norm_num)
    (2 * (Real.sqrt (2 * κ) / 2)⁻¹ ^ ((1 : ℝ) / 8))] with n hn1 hn2
  have hMs : 0 < s1Ms d E s n := s1_Ms_pos h n
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast s1_one_le_W d n
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := s1_Npow_le hN0 hc1 (hn1 (s n) (h.hst n)) (q := (1 : ℝ) / 8) (by norm_num)
  -- `W^{c'} ≤ N^{c₀/8}`
  have h2 : (d.W n : ℝ) ^ (min (2 * c) τ * (1 / 4)) ≤ ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ * (1 / 8)) := by
    have e : (d.W n : ℝ) ^ (min (2 * c) τ * (1 / 4)) =
        ((d.W n : ℝ) ^ 2) ^ (min (2 * c) τ * (1 / 8)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    rw [e]
    exact Real.rpow_le_rpow (sq_nonneg _) (s1_W_sq_le_size d n) (by positivity)
  set w := (d.W n : ℝ) ^ (min (2 * c) τ * (1 / 4)) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hW0 _
  have hm0 : 0 < s1Ms d E s n ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hMs _
  have h3 : 2 * w ≤ s1Ms d E s n ^ ((1 : ℝ) / 4) := by
    have h4 : 2 * ((Real.sqrt (2 * κ) / 2)⁻¹ ^ ((1 : ℝ) / 8) * s1Ms d E s n ^ ((1 : ℝ) / 8)) ≤
        s1Ms d E s n ^ ((1 : ℝ) / 4) := by
      rw [← mul_assoc]
      refine s1_mul_rpow_le hMs (p := (1 : ℝ) / 8) ?_
      have : (1 : ℝ) / 4 - 1 / 8 = 1 / 8 := by norm_num
      rw [this]; exact hn2
    linarith [h1, h2]
  rw [s1_inv_rpow hMs.le, Real.rpow_neg hW0.le, ← hw, Real.rpow_neg hMs.le]
  rw [show 2 * (s1Ms d E s n ^ ((1 : ℝ) / 4))⁻¹ = 2 / s1Ms d E s n ^ ((1 : ℝ) / 4) by ring,
    show w⁻¹ = 1 / w by ring, div_le_div_iff₀ hm0 hw0]
  linarith

/-- `N⁻¹ ≤ M_s^{-1/4}/2`, eventually (the mesh of the net is finer than `a/2`). -/
private theorem s1_F6 (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ)⁻¹ ≤ (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) / 2 := by
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp h.hN).eventually_ge_atTop 2]
    with n hn
  have hMs : 0 < s1Ms d E s n := s1_Ms_pos h n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (s1_one_le_size d n)
  have hle : s1Ms d E s n ≤ ((d.size n : ℕ) : ℝ) :=
    (s1_scaleM_le_W2 (s1_one_le_L d n) (by linarith [h.hE n, h.hκ])
      (lt_of_le_of_lt (h.hst n) (h.ht1 n))).trans (s1_W_sq_le_size d n)
  have h1 : ((d.size n : ℕ) : ℝ)⁻¹ ^ ((1 : ℝ) / 4) ≤ (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (inv_nonneg.2 hN0.le) (inv_anti₀ hMs hle) (by norm_num)
  have h2 : 2 * ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-((1 : ℝ) / 4)) := by
    refine s1_mul_rpow_le hN0 ?_
    have : -((1 : ℝ) / 4) - -1 = 3 / 4 := by norm_num
    rw [this]; exact hn
  rw [s1_inv_rpow hN0.le] at h1
  rw [Real.rpow_neg_one] at h2
  linarith

/-- `M_s^{-1/4} ≤ 1`, eventually. -/
private theorem s1_F7 (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop, (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) ≤ 1 := by
  filter_upwards [s1_one_le_Ms h] with n hn
  exact Real.rpow_le_one (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hn) (by norm_num)

/-- `W⁻² ≤ M_s^{-14/15}`, eventually. -/
private theorem s1_F8 (h : S1Std d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ) ^ 2)⁻¹ ≤ s1Ms d E s n ^ (-((14 : ℝ) / 15)) := by
  filter_upwards [s1_one_le_Ms h] with n hn
  have hMs : 0 < s1Ms d E s n := s1_Ms_pos h n
  have hle : s1Ms d E s n ≤ (d.W n : ℝ) ^ 2 :=
    s1_scaleM_le_W2 (s1_one_le_L d n) (by linarith [h.hE n, h.hκ])
      (lt_of_le_of_lt (h.hst n) (h.ht1 n))
  have h1 : ((d.W n : ℝ) ^ 2)⁻¹ ≤ (s1Ms d E s n)⁻¹ := inv_anti₀ hMs hle
  have h2 : s1Ms d E s n ^ (-(1 : ℝ)) ≤ s1Ms d E s n ^ (-((14 : ℝ) / 15)) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  rw [Real.rpow_neg_one] at h2
  exact h1.trans h2

end Scales

/-! ## 3. Generic `PerTimeDomAt` helpers -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- A deterministic bound `ξ ≤ N^τ ζ` (eventually, for every `τ > 0`) gives `ξ ≺ ζ`. -/
private theorem s1_pt_of_le {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ] with l hl u
  have : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [this, measure_empty]
  exact zero_le

/-- The union bound in event form: `ξ ≺ ζ` per time, with polynomially many parameters, gives that
`ξ ≤ N^τ ζ` for all parameters simultaneously with high probability. -/
private theorem s1_highProb_of_pt [∀ l, Fintype (U l)] {ξ ζ : ∀ l, U l → Ω → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : PerTimeDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω}) :=
  PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt (stochDomAt_of_perTimeDomAt P size hC0 hC h) hτ

/-- Conversely, a high-probability event for every `τ > 0` gives `ξ ≺ ζ` per time. -/
private theorem s1_pt_of_highProb {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), HighProbAt P size
      (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω})) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine (measure_mono ?_).trans hl
  intro ω hω hω'
  exact absurd (hω' u) (not_le.2 hω)

/-- Per time along a `Unit`-indexed family is the uniform statement. -/
private theorem s1_stochDom_unit {ξ ζ : ∀ _ : ℕ, Unit → Ω → ℝ} (h : PerTimeDomAt P size ξ ζ) :
    StochDomAt P size ξ ζ :=
  stochDomAt_of_perTimeDomAt P size (C := 0) le_rfl
    (Eventually.of_forall fun _ => by simp) h

end Generic

/-! ## 4. The loop family: (55) at `t₁ = max(s, 1/2)`, and (`lRB1`) with the indicator -/

section Loops

variable {d} {κ c τ : ℝ} {E s t : ℕ → ℝ}

/-- The start time `t₁ = max(s, 1/2)` of the continuity argument. -/
private abbrev s1T1 (s : ℕ → ℝ) (n : ℕ) : ℝ := max (s n) (1 / 2)

private theorem s1_blockMat_herm {L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) : (blockMat M).IsHermitian :=
  hM.submatrix _

private theorem s1_ellT_nonneg (L : ℕ) (u : ℝ) : 0 ≤ ellT L u :=
  le_min (by positivity) (Nat.cast_nonneg L)

/-- (`Lboundfor1/2`) at a time `u ≤ 1/2` (deterministic): `|𝓛_{u,σ,a}| ≤ (2/c₁)^k
M_u^{-(k-1)}` when `Im m ≥ c₁` (`d = 2`: weight `W⁻²`, `M = W² ℓ² η`). -/
private theorem s1_loop_det {L W : ℕ} [NeZero L] [NeZero W] {E u c₁ : ℝ} (hL : 1 ≤ L)
    (hE : |E| < 2) (hc₁ : 0 < c₁) (hm : c₁ ≤ (spectralM E).im) (hu : u ≤ 1 / 2)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    loopAbs L W E u M σ a ≤ (2 / c₁) ^ k * (scaleM L W E u)⁻¹ ^ (k - 1) := by
  have hu1 : u < 1 := by linarith
  have hMpos : 0 < scaleM L W E u := scaleM_pos hL (NeZero.pos W) hE hu1
  have hη : c₁ / 2 ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
    calc c₁ / 2 ≤ (1 / 2) * (spectralM E).im := by linarith
      _ ≤ (1 - u) * (spectralM E).im := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h1 := norm_gloop_le_of_le_abs_im (L := L) (W := W) (s1_blockMat_herm hM)
    (by positivity : 0 < c₁ / 2) hη (loopOf σ a) (by simp [loopOf]) (by simpa [loopOf] using hk)
  simp only [loopOf, List.length_ofFn] at h1
  unfold loopAbs
  refine h1.trans ?_
  have h2 : ((W : ℝ)⁻¹ ^ 2) ≤ (scaleM L W E u)⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ hMpos (s1_scaleM_le_W2 hL hE.le hu1)
  have h3 : (c₁ / 2)⁻¹ = 2 / c₁ := by rw [inv_div]
  rw [h3]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 _) (by positivity)

/-- `KboundConcl κ` along the sequence `(L n, W n, E n, s n)`: `|𝒦_{s,σ,a}| ≺ M_s^{-(k-1)}`
(`ML:Kbound`, via `kloop_Mt_eq`). -/
private theorem s1_Kbound_seq (h : S1Std d κ c τ E s t) (hK : KboundConcl κ) {k : ℕ}
    (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p _ => ‖KLoop.Kcal (d.L n) (d.W n) (E n) (s n) (loopOf p.2.1 p.2.2)‖)
      (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ (k - 1)) := by
  refine s1_pt_of_le fun τ' hτ' => ?_
  filter_upwards [(s1_hsize d h.hN).eventually (hK k hk τ' hτ')] with n hn p ω
  have hs1 : s n < 1 := lt_of_le_of_lt (h.hst n) (h.ht1 n)
  let par : KLoop.Par κ (d.size n) :=
    { L := d.L n, W := d.W n, hL := d.three_le_L n, hW := d.W_pos n,
      hN := (Sizes.size_eq d n).symm, E := E n, hE := h.hE n, t := s n,
      ht0 := h.hs0 n, ht1 := hs1 }
  have h1 := hn ⟨par, p.2.1, p.2.2⟩
  simp only [] at h1
  rw [kloop_Mt_eq hs1.le] at h1
  exact h1

/-- Hypothesis (55) of `lem_ConArg` at `t₁ = max(s, 1/2)`:
`max_{σ,a} |𝓛_{t₁,σ,a}| ≺ M_{t₁}^{-(k-1)}` for every `k ≥ 1`. -/
private def S1H55 (d : Sizes) (E s : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => loopAbs (d.L n) (d.W n) (E n) (s1T1 s n)
        (Sizes.seqHflow d n (s1T1 s n) ω) p.2.1 p.2.2)
      (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1))

/-- **(55) at `t₁ = max(s, 1/2)`** (Cases 2 and 3 of the paper): for `s ≥ 1/2`,
`𝓛 = (𝓛-𝒦) + 𝒦` with `InitLK` and `KboundConcl` (`Lboundfors`); for `s < 1/2` the deterministic
bound (`Lboundfor1/2`). -/
private theorem s1_h55 (h : S1Std d κ c τ E s t) (hIK : InitLK d E s) (hK : KboundConcl κ) :
    S1H55 d E s := by
  intro k hk
  have hsize := s1_hsize d h.hN
  have hc1 := s1_c1_pos h
  have hsum := PerTimeCalc.PerTime.perTimeCalc_add hsize (hIK k hk) (s1_Kbound_seq h hK hk)
  have hMt1 : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (s1T1 s n) := fun n =>
    scaleM_pos (s1_one_le_L d n) (s1_one_le_W d n) (s1_bulk h.hκ (h.hE n)).1
      (max_lt (lt_of_le_of_lt (h.hst n) (h.ht1 n)) (by norm_num))
  have h₁ := PerTimeCalc.PerTime.perTimeCalc_mono hsize (P := Sizes.seqP d) (size := d.size)
    (ζ' := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1))
    (fun n _ _ => pow_nonneg (inv_nonneg.2 (hMt1 n).le) _) 2 ?_ hsum
  swap
  · filter_upwards [s1_one_le_Ms h] with n hn p ω
    have hMs := s1_Ms_pos h n
    have hs1 : s n < 1 := lt_of_le_of_lt (h.hst n) (h.ht1 n)
    have h1 : (s1Ms d E s n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
    have h2 : (s1Ms d E s n)⁻¹ ^ k ≤ (s1Ms d E s n)⁻¹ ^ (k - 1) :=
      pow_le_pow_of_le_one (inv_nonneg.2 hMs.le) h1 (Nat.sub_le k 1)
    have h3 : scaleM (d.L n) (d.W n) (E n) (s1T1 s n) ≤ s1Ms d E s n :=
      (scaleM_anti_ratio (W := d.W n) (s1_one_le_L d n) (s1_bulk h.hκ (h.hE n)).1
        (le_max_left _ _) (max_lt hs1 (by norm_num))).1
    have h4 : (s1Ms d E s n)⁻¹ ^ (k - 1) ≤
        (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1) :=
      pow_le_pow_left₀ (inv_nonneg.2 hMs.le) (inv_anti₀ (hMt1 n) h3) _
    change (s1Ms d E s n)⁻¹ ^ k + (s1Ms d E s n)⁻¹ ^ (k - 1) ≤
      2 * (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1)
    linarith
  have h₂ := PerTimeCalc.PerTime.stochDom_of_le_const_mul hsize (P := Sizes.seqP d)
    (size := d.size)
    (ξ := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (2 / (Real.sqrt (2 * κ) / 2)) ^ k *
        (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1))
    (ζ := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (scaleM (d.L n) (d.W n) (E n) (s1T1 s n))⁻¹ ^ (k - 1))
    (fun n _ _ => mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg (inv_nonneg.2 (hMt1 n).le) _))
    (fun n _ _ => pow_nonneg (inv_nonneg.2 (hMt1 n).le) _)
    ((2 / (Real.sqrt (2 * κ) / 2)) ^ k) (fun _ _ _ => le_rfl)
  refine PerTimeCalc.PerTime.stochDom_of_forall_or hsize h₁ h₂ ?_
  intro n p ω
  by_cases hs : 1 / 2 ≤ s n
  · left
    have ht : s1T1 s n = s n := max_eq_left hs
    refine ⟨?_, le_rfl⟩
    rw [ht]
    unfold loopAbs lkGen
    exact norm_le_norm_sub_add _ _
  · right
    have hs' : s n < 1 / 2 := not_le.1 hs
    have ht : s1T1 s n = 1 / 2 := max_eq_right hs'.le
    refine ⟨?_, le_rfl⟩
    exact s1_loop_det (s1_one_le_L d n) (s1_bulk h.hκ (h.hE n)).1 hc1 (s1_bulk h.hκ (h.hE n)).2
      (by rw [ht]) _ (Sizes.seqHflow_isHermitian d n _ ω) hk _ _

/-- **`(lRB1)` with the indicator, per sequence** (`jsajufua`, from `lem_ConArg`
and (`Lboundfor1/2`) for `u < 1/2`): for every time sequence `u n ∈ [s n, t n]` and `k ≥ 1`,
`1(‖G_u‖_max ≤ 2) |𝓛_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{2(k-1)} M_u^{-(k-1)}`. -/
private theorem s1_LI (h : S1Std d κ c τ E s t) (h55 : S1H55 d E s) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) {k : ℕ} (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => (if gMax (E n) (u n) (Sizes.seqHflow d n (u n) ω) ≤ 2 then 1 else 0) *
        loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n _ _ => (ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1)) := by
  have hsize := s1_hsize d h.hN
  have hc1 := s1_c1_pos h
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (h.hst n) (h.ht1 n)
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hu n).2 (h.ht1 n)
  have hcon := conArg d κ (1 / 4) E (s1T1 s) (fun n => max (u n) (s1T1 s n)) h.hκ h.hE
    (by norm_num) (fun n => lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    (fun n => le_max_right _ _)
    (fun n => max_lt (hu1 n) (max_lt (hs1 n) (by norm_num))) h.hN h55 k hk
  have hMu : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (u n) := fun n =>
    scaleM_pos (s1_one_le_L d n) (s1_one_le_W d n) (s1_bulk h.hκ (h.hE n)).1 (hu1 n)
  have hζ0 : ∀ n, 0 ≤ (ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
      (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1) := fun n =>
    mul_nonneg (pow_nonneg (div_nonneg (s1_ellT_nonneg _ _) (s1_ellT_nonneg _ _)) _)
      (pow_nonneg (inv_nonneg.2 (hMu n).le) _)
  have h₂ := PerTimeCalc.PerTime.stochDom_of_le_const_mul hsize (P := Sizes.seqP d)
    (size := d.size)
    (ξ := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (2 / (Real.sqrt (2 * κ) / 2)) ^ k *
        ((ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
          (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1)))
    (ζ := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1))
    (fun n _ _ => mul_nonneg (pow_nonneg (by positivity) _) (hζ0 n)) (fun n _ _ => hζ0 n)
    ((2 / (Real.sqrt (2 * κ) / 2)) ^ k) (fun _ _ _ => le_rfl)
  refine PerTimeCalc.PerTime.stochDom_of_forall_or hsize hcon h₂ ?_
  intro n p ω
  by_cases hu12 : 1 / 2 ≤ u n
  · left
    have ht2 : max (u n) (s1T1 s n) = u n := max_eq_left (max_le (hu n).1 hu12)
    have hs1' : s n ≤ s1T1 s n := le_max_left _ _
    have hs1'' : s1T1 s n < 1 := max_lt (hs1 n) (by norm_num)
    have hmono := (ellT_mono_ratio (s1_one_le_L d n) (h.hs0 n) hs1' hs1'').1
    change _ ≤ (if gMax (E n) (max (u n) (s1T1 s n))
        (Sizes.seqHflow d n (max (u n) (s1T1 s n)) ω) ≤ 2 then 1 else 0) *
      loopAbs (d.L n) (d.W n) (E n) (max (u n) (s1T1 s n))
        (Sizes.seqHflow d n (max (u n) (s1T1 s n)) ω) p.2.1 p.2.2 ∧
      (ellT (d.L n) (max (u n) (s1T1 s n)) / ellT (d.L n) (s1T1 s n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) (max (u n) (s1T1 s n)))⁻¹ ^ (k - 1) ≤ _
    rw [ht2]
    refine ⟨le_rfl, ?_⟩
    have hℓs : 0 < ellT (d.L n) (s n) := (ellT_pos_le (s1_one_le_L d n) (hs1 n)).1
    have hdiv : ellT (d.L n) (u n) / ellT (d.L n) (s1T1 s n) ≤
        ellT (d.L n) (u n) / ellT (d.L n) (s n) :=
      div_le_div_of_nonneg_left (s1_ellT_nonneg _ _) hℓs hmono
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg (s1_ellT_nonneg _ _) (s1_ellT_nonneg _ _)) hdiv _)
      (pow_nonneg (inv_nonneg.2 (hMu n).le) _)
  · right
    have hu' : u n < 1 / 2 := not_le.1 hu12
    refine ⟨?_, le_rfl⟩
    have hℓs : 0 < ellT (d.L n) (s n) := (ellT_pos_le (s1_one_le_L d n) (hs1 n)).1
    have hratio : 1 ≤ ellT (d.L n) (u n) / ellT (d.L n) (s n) := by
      rw [one_le_div hℓs]
      exact (ellT_mono_ratio (s1_one_le_L d n) (h.hs0 n) (hu n).1 (hu1 n)).1
    have h1 : 1 ≤ (ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) :=
      one_le_pow₀ hratio
    have hdet := s1_loop_det (s1_one_le_L d n) (s1_bulk h.hκ (h.hE n)).1 hc1
      (s1_bulk h.hκ (h.hE n)).2 hu'.le _ (Sizes.seqHflow_isHermitian d n (u n) ω) hk
      p.2.1 p.2.2
    have hind : (if gMax (E n) (u n) (Sizes.seqHflow d n (u n) ω) ≤ 2 then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hnn : 0 ≤ loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2 :=
      loopAbs_nonneg _ _ _ _ _ _ _
    calc (if gMax (E n) (u n) (Sizes.seqHflow d n (u n) ω) ≤ 2 then (1 : ℝ) else 0) *
          loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2
        ≤ loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2 :=
          mul_le_of_le_one_left hnn hind
      _ ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k * (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1) :=
          hdet
      _ ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k *
          ((ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
            (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ (k - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
          exact le_mul_of_one_le_left (pow_nonneg (inv_nonneg.2 (hMu n).le) _) h1

end Loops

/-! ## 5. Matrix-level bridges: block indices versus `Idx`, loops, and `gexRHS` -/

section Bridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `green (blockMat M) z` is the resolvent of `M`, relabelled by `splitEquiv` (cf. the private
`conArg_green_blockMat_diag_le` of `RBM2D.Induction.ConArg`). -/
private theorem s1_green_blockMat (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) :
    green (blockMat M) z = (M - z • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹.submatrix
      (splitEquiv L W).symm (splitEquiv L W).symm := by
  have hs : blockMat M - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      = (M - z • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
          (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext p q
    simp [blockMat, Matrix.one_apply]
  unfold green
  rw [hs, Matrix.inv_submatrix_equiv]

private theorem s1_greenBlk_apply (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    greenBlk L W E u M true (splitEquiv L W i) (splitEquiv L W j) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j := by
  rw [greenBlk, Gsig_true, s1_green_blockMat, Matrix.submatrix_apply]
  simp

private theorem s1_diagSq_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i : Idx L W) :
    Green.diagSq L W E u M (splitEquiv L W i) = llErrMat L W E u M i i ^ 2 := by
  unfold Green.diagSq llErrMat
  rw [s1_greenBlk_apply]
  simp

private theorem s1_offSq_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {i j : Idx L W}
    (hij : i ≠ j) :
    Green.offSq L W E u M (splitEquiv L W i) (splitEquiv L W j) = llErrMat L W E u M i j ^ 2 := by
  unfold Green.offSq llErrMat
  have h1 : ¬ (splitEquiv L W i = splitEquiv L W j) := by simpa using hij
  rw [s1_greenBlk_apply]
  simp [hij, h1]

private theorem s1_norm_loopPM (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    ‖loopPM L W E u M a b‖ = loopAbs L W E u M ![true, false] ![a, b] := by
  unfold loopPM loopAbs
  have : loopOf (![true, false] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) = pmLoop a b := by
    simp [loopOf, pmLoop]
  rw [this]

omit [NeZero W] in
private theorem s1_zdist_le_one (hL : 3 ≤ L) {x : ZMod L} (h : zdist L x ≤ 1) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hx : x.val < L := ZMod.val_lt x
  simp only [zdist] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  have hneg : (-1 : ZMod L).val = L - 1 := by
    rw [ZMod.neg_val, ite_eq_right h1, hval]
  by_cases hs : x.val ≤ 1
  · rcases (by omega : x.val = 0 ∨ x.val = 1) with h0 | h0
    · left
      exact (ZMod.val_eq_zero x).1 h0
    · right; left
      exact ZMod.val_injective L (by rw [h0, hval])
  · right; right
    exact ZMod.val_injective L (by rw [hneg]; omega)

omit [NeZero W] in
private theorem s1_mem_sbSupport (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    v ∈ sbSupport L := by
  obtain ⟨x, y⟩ := v
  simp only [zdist2] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hz1 : zdist L (1 : ZMod L) ≠ 0 := fun h0 => h1 ((zdist_eq_zero_iff L).1 h0)
  have hzm : zdist L (-1 : ZMod L) ≠ 0 := fun h0 => neg_ne_zero.2 h1 ((zdist_eq_zero_iff L).1 h0)
  have hx : zdist L x ≤ 1 := by omega
  have hy : zdist L y ≤ 1 := by omega
  rcases s1_zdist_le_one hL hx with rfl | rfl | rfl <;>
    rcases s1_zdist_le_one hL hy with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | simp [sbSupport]

omit [NeZero W] in
private theorem s1_near_card (hL : 3 ≤ L) (a : Z2 L) :
    ((Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1)).card : ℝ) ≤ 5 := by
  have hsub : Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1) ⊆
      (sbSupport L).image (fun v => v + a) := by
    intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    exact Finset.mem_image.2 ⟨a' - a, s1_mem_sbSupport hL ha', by simp⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_sbSupport L hL] at this
  exact_mod_cast this

/-- The right side of (`GijGEX`) is at most `25 B + W⁻²` if every `|𝓛_{(+,-),(a,b)}| ≤ B`
(the number of `(a',b')` with `|a'-a|_L, |b'-b|_L ≤ 1` is at most `25`). -/
private theorem s1_gexRHS_le (hL : 3 ≤ L) (E u B : ℝ) (hB : 0 ≤ B)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : ∀ a b, ‖loopPM L W E u M a b‖ ≤ B) (a b : Z2 L) :
    gexRHS L W E u M a b ≤ 25 * B + ((W : ℝ) ^ 2)⁻¹ := by
  unfold gexRHS
  have hp : ∀ a' : Z2 L, ((if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0)) ≥ 0 := fun a' => by
    split_ifs <;> norm_num
  have h1 : (∑ a' : Z2 L, ∑ b' : Z2 L,
      if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0) ≤
      25 * B := by
    calc (∑ a' : Z2 L, ∑ b' : Z2 L,
        if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0)
        ≤ ∑ a' : Z2 L, ∑ b' : Z2 L, (if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          by_cases h1 : zdist2 L (a' - a) ≤ 1 <;> by_cases h2 : zdist2 L (b' - b) ≤ 1 <;>
            simp [h1, h2, hM]
      _ = (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 5 * (5 * B) := by
          have e1 : (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact s1_near_card hL a
          have e2 : (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact s1_near_card hL b
          have e0 : 0 ≤ (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) := by
            exact Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
          exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hB) (mul_nonneg e0 hB) (by norm_num)
      _ = 25 * B := by ring
  have h2 : (if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    split_ifs
    · exact le_rfl
    · positivity
  linarith

/-- `‖G_u - m‖_max = max_{i,j} |(G_u - m)_{ij}|` at the matrix `M`. -/
private def s1xM (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2)

private theorem s1xM_ge (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    llErrMat L W E u M i j ≤ s1xM L W E u M :=
  Finset.le_sup' (fun q : Idx L W × Idx L W => llErrMat L W E u M q.1 q.2)
    (Finset.mem_univ (i, j))

private theorem s1xM_le {E u B : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (h : ∀ i j, llErrMat L W E u M i j ≤ B) : s1xM L W E u M ≤ B :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

/-- `‖G_u‖_max ≤ 1 + ‖G_u - m‖_max` (`|m| = 1`). -/
private theorem s1_gMax_le {E u : ℝ} (hE : |E| ≤ 2) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    gMax E u M ≤ 1 + s1xM L W E u M := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  have h1 := norm_le_norm_sub_add
    ((M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ q.1 q.2)
    (if q.1 = q.2 then spectralM E else 0)
  have h2 : ‖(if q.1 = q.2 then spectralM E else 0)‖ ≤ 1 := by
    split_ifs
    · rw [norm_spectralM hE]
    · simp
  have h3 := s1xM_ge E u M q.1 q.2
  unfold llErrMat at h3
  linarith

/-- One-sided Lipschitz bound of `‖G_u - m‖_max` in the resolvent entries. -/
private theorem s1xM_le_add {E u u' δ : ℝ} {M M' : Matrix (Idx L W) (Idx L W) ℂ}
    (h : ∀ i j, ‖(M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (M' - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j‖ ≤ δ) :
    s1xM L W E u M ≤ s1xM L W E u' M' + δ := by
  refine s1xM_le fun i j => ?_
  have h1 := s1xM_ge E u' M' i j
  have h6 := norm_le_norm_sub_add
    ((M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (if i = j then spectralM E else 0))
    ((M' - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (if i = j then spectralM E else 0))
  have h4 : ((M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (if i = j then spectralM E else 0)) -
      ((M' - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (if i = j then spectralM E else 0)) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (M' - spectralZ E u' • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j := by ring
  rw [h4] at h6
  have h7 := h i j
  unfold llErrMat at h1 ⊢
  linarith

/-- **The deterministic core of the weak-law step**: on `{‖G_u - m‖_max ≤ 2a}`, with
`2a ≤ W^{-c'}` (so `Ω(u,c')` holds and `‖G_u‖_max ≤ 2`), the three per-time bounds
`1_Ω |G_{pq}|² ≤ N^τ 𝓛-terms`, `1_Ω |G_{pp}-m|² ≤ N^τ max 𝓛`, `1_Ω |𝓛| ≤ N^τ g` give
`|(G_u - m)_{ij}|² ≤ 26 N^{2τ} g`. -/
private theorem s1_wl_det (hL : 3 ≤ L) (hW : 1 ≤ W) {E u a c' g Nτ : ℝ} (hE : |E| ≤ 2)
    (hc' : 0 < c') (M : Matrix (Idx L W) (Idx L W) ℂ) (hx : s1xM L W E u M ≤ 2 * a)
    (hΩ : 2 * a ≤ (W : ℝ) ^ (-c')) (hNτ : 1 ≤ Nτ) (hg : 0 ≤ g)
    (hWg : ((W : ℝ) ^ 2)⁻¹ ≤ g)
    (hLoop : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Z2 L),
      (if gMax E u M ≤ 2 then (1 : ℝ) else 0) * loopAbs L W E u M σ b ≤ Nτ * g)
    (hii : ∀ P : BlockIndex L W,
      Green.omegaInd L W E u c' M * Green.diagSq L W E u M P ≤ Nτ * maxLoopPM L W E u M)
    (hij : ∀ P Q : BlockIndex L W,
      Green.omegaInd L W E u c' M * Green.offSq L W E u M P Q ≤ Nτ * gexRHS L W E u M Q.1 P.1) :
    ∀ i j, llErrMat L W E u M i j ^ 2 ≤ 26 * Nτ ^ 2 * g := by
  have hΩ' : ∀ i j, llErrMat L W E u M i j ≤ (W : ℝ) ^ (-c') := fun i j =>
    (s1xM_ge E u M i j).trans (hx.trans hΩ)
  have hom : Green.omegaInd L W E u c' M = 1 := by
    unfold Green.omegaInd
    simp [hΩ']
  have hWc : (W : ℝ) ^ (-c') ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  have hgm : gMax E u M ≤ 2 := by
    have := s1_gMax_le (L := L) (W := W) (u := u) hE M
    linarith
  have hLoop' : ∀ b b' : Z2 L, ‖loopPM L W E u M b b'‖ ≤ Nτ * g := fun b b' => by
    rw [s1_norm_loopPM]
    have := hLoop ![true, false] ![b, b']
    simpa [hgm] using this
  have hB : 0 ≤ Nτ * g := mul_nonneg (by linarith) hg
  have hmax : maxLoopPM L W E u M ≤ Nτ * g :=
    Finset.sup'_le _ _ fun p _ => hLoop' p.1 p.2
  have hgle : g ≤ Nτ * g := by nlinarith
  intro i j
  by_cases hij' : i = j
  · subst hij'
    have h1 := hii (splitEquiv L W i)
    rw [hom, one_mul, s1_diagSq_eq] at h1
    have h2 : Nτ * maxLoopPM L W E u M ≤ Nτ * (Nτ * g) :=
      mul_le_mul_of_nonneg_left hmax (by linarith)
    have h3 : 0 ≤ Nτ ^ 2 * g := mul_nonneg (sq_nonneg _) hg
    nlinarith
  · have h1 := hij (splitEquiv L W i) (splitEquiv L W j)
    rw [hom, one_mul, s1_offSq_eq _ _ _ hij'] at h1
    have h2 := s1_gexRHS_le hL E u (Nτ * g) hB M hLoop'
      (splitEquiv L W j).1 (splitEquiv L W i).1
    have h3 : Nτ * gexRHS L W E u M (splitEquiv L W j).1 (splitEquiv L W i).1 ≤
        Nτ * (25 * (Nτ * g) + Nτ * g) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by linarith)
    nlinarith

end Bridge

/-! ## 6. The weak-law step at one time sequence -/

section WeakLawSeq

variable {d} {κ c τ : ℝ} {E s t : ℕ → ℝ}

/-- `‖G_v - m‖_max` at the size index `n`, time `v`. -/
private abbrev s1x (d : Sizes) (E : ℕ → ℝ) (n : ℕ) (v : ℝ) (ω : Sizes.SeqΩ d) : ℝ :=
  s1xM (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω)

/-- The threshold `a = M_s^{-1/4}` (constant in `u`). -/
private abbrev s1a (d : Sizes) (E s : ℕ → ℝ) (n : ℕ) : ℝ := (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4)

/-- The bound `f = 6 M_s^{-7/15}` (constant in `u`). -/
private abbrev s1f (d : Sizes) (E s : ℕ → ℝ) (n : ℕ) : ℝ := 6 * (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15)

private theorem s1_card_block (n : ℕ) :
    (Fintype.card (BlockIndex (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  rw [card_BlockIndex]
  simp [Sizes.size, mul_comm]

private theorem s1_card_block1 (n : ℕ) :
    (Fintype.card (Unit × BlockIndex (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  rw [Fintype.card_prod Unit (BlockIndex (d.L n) (d.W n)), Fintype.card_unit]
  push_cast
  rw [s1_card_block]; ring

private theorem s1_card_block2 (n : ℕ) :
    (Fintype.card (Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) : ℝ) =
      ((d.size n : ℕ) : ℝ) ^ 2 := by
  rw [Fintype.card_prod Unit (BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)),
    Fintype.card_prod (BlockIndex (d.L n) (d.W n)) (BlockIndex (d.L n) (d.W n)), Fintype.card_unit]
  push_cast
  rw [s1_card_block]; ring

/-- `#(Unit × (Fin k → Bool) × (Fin k → Z2 L)) ≤ size^{2k}` (as in the private
`conArg_card_le`). -/
private theorem s1_card_loops (n k : ℕ) :
    (Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ)
      ≤ ((d.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hc : Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      = 2 ^ k * (d.L n * d.L n) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have hL := d.three_le_L n
  have hW := d.W_pos n
  have h1 : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ hW
    nlinarith
  have h2 : 2 ≤ d.size n := le_trans (by nlinarith) h1
  have key : 2 ^ k * (d.L n * d.L n) ^ k ≤ d.size n ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left h2 k) (Nat.pow_le_pow_left h1 k)
  rw [hc]
  exact_mod_cast key

/-- **The weak-law step at one time sequence** (`lem_GbEXP` with `n = 2` and
`lem_ConArg`): for every time sequence `u n ∈ [s n, t n]`,
`1(‖G_u - m‖_max ≤ 2 M_s^{-1/4}) ‖G_u - m‖_max ≺ 6 M_s^{-7/15}`. -/
private theorem s1_wl_seq (h : S1Std d κ c τ E s t) (hG : Green.GbEXPHypV3 d (κ / 2) c τ)
    (h55 : S1H55 d E s) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun _ => Unit)
      (fun n _ ω => {ω | s1x d E n (u n) ω ≤ 2 * s1a d E s n}.indicator
        (fun ω => s1x d E n (u n) ω) ω)
      (fun n _ _ => s1f d E s n) := by
  have hsize := s1_hsize d h.hN
  obtain ⟨c', hc', hF5⟩ := s1_F5 h
  have hu0 : ∀ n, 0 ≤ u n := fun n => (h.hs0 n).trans (hu n).1
  have hu1 : ∀ n, u n < 1 := fun n => (hu n).2.trans_lt (h.ht1 n)
  have hRu : RangeCond d τ u := Green.rangeCond_mono d h.hR (fun n => (hu n).2)
  have hE' : ∀ n, |E n| < 2 - κ / 2 := fun n => by linarith [h.hE n, h.hκ]
  obtain ⟨hGij, hGii, -⟩ := hG h.hN h.hB E u hE' hu0 hu1 hRu c' hc'
  have hLI := s1_LI h h55 u hu (k := 2) (by norm_num)
  have hLI' : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p ω => (if gMax (E n) (u n) (Sizes.seqHflow d n (u n) ω) ≤ 2 then 1 else 0) *
        loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n _ _ => s1Ms d E s n ^ (-((14 : ℝ) / 15))) := by
    refine PerTimeCalc.PerTime.mono_right_eventually hLI ?_
    filter_upwards [s1_ratio_ev h] with n hn p ω
    simpa using hn (u n) (hu n).1 (hu n).2
  refine s1_pt_of_highProb fun τ' hτ' => ?_
  have hC1 : ∀ᶠ l : ℕ in atTop,
      (Fintype.card (Unit × BlockIndex (d.L l) (d.W l) × BlockIndex (d.L l) (d.W l)) : ℝ) ≤
        ((d.size l : ℕ) : ℝ) ^ (2 : ℝ) := Eventually.of_forall fun l => by
    rw [Real.rpow_two, s1_card_block2]
  have hC2 : ∀ᶠ l : ℕ in atTop,
      (Fintype.card (Unit × BlockIndex (d.L l) (d.W l)) : ℝ) ≤ ((d.size l : ℕ) : ℝ) ^ (1 : ℝ) :=
    Eventually.of_forall fun l => by
      rw [Real.rpow_one, s1_card_block1]
  have hC3 : ∀ᶠ l : ℕ in atTop,
      (Fintype.card (Unit × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L l))) : ℝ) ≤
        ((d.size l : ℕ) : ℝ) ^ ((2 * 2 : ℕ) : ℝ) := Eventually.of_forall fun l => s1_card_loops l 2
  have Ev1 := s1_highProb_of_pt (P := Sizes.seqP d) (size := d.size) (C := 2) (by norm_num) hC1 hGij hτ'
  have Ev2 := s1_highProb_of_pt (P := Sizes.seqP d) (size := d.size) (C := 1) (by norm_num) hC2 hGii hτ'
  have Ev3 := s1_highProb_of_pt (P := Sizes.seqP d) (size := d.size) (C := ((2 * 2 : ℕ) : ℝ))
    (by positivity) hC3 hLI' hτ'
  have EvAll := PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize Ev1 Ev2) Ev3
  refine PerTimeCalc.perTimeCalc_highProbAt_mono EvAll ?_
  filter_upwards [hF5, s1_F8 h] with n hn5 hn8
  rintro ω ⟨⟨h1, h2⟩, h3⟩ ⟨⟩
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) := s1_one_le_size d n
  have hNτ : 1 ≤ ((d.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
  have hMs := s1_Ms_pos h n
  have hr0 : 0 ≤ (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15) := Real.rpow_nonneg (inv_nonneg.2 hMs.le) _
  have hgr : s1Ms d E s n ^ (-((14 : ℝ) / 15)) = ((s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [s1_inv_rpow hMs.le, ← Real.rpow_natCast, ← Real.rpow_mul hMs.le]; norm_num
  change {ω | s1x d E n (u n) ω ≤ 2 * s1a d E s n}.indicator (fun ω => s1x d E n (u n) ω) ω ≤
    ((d.size n : ℕ) : ℝ) ^ τ' * s1f d E s n
  by_cases hx : s1x d E n (u n) ω ≤ 2 * s1a d E s n
  · rw [Set.indicator_of_mem (show ω ∈ {ω | s1x d E n (u n) ω ≤ 2 * s1a d E s n} from hx)]
    have hent := s1_wl_det (L := d.L n) (W := d.W n) (d.three_le_L n) (d.W_pos n)
      (E := E n) (u := u n) (a := s1a d E s n) (c' := c')
      (g := s1Ms d E s n ^ (-((14 : ℝ) / 15))) (Nτ := ((d.size n : ℕ) : ℝ) ^ τ')
      (s1_bulk h.hκ (h.hE n)).1.le hc' _ hx hn5 hNτ (Real.rpow_nonneg hMs.le _) hn8
      (fun σ b => h3 ((), σ, b)) (fun P => h2 ((), P)) (fun P Q => h1 ((), P, Q))
    refine s1xM_le fun i j => ?_
    have hij := hent i j
    rw [hgr] at hij
    have hB0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (6 * (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15)) :=
      mul_nonneg (by linarith) (by positivity)
    refine (pow_le_pow_iff_left₀ (llErrMat_nonneg _ _ _ _ _ _ _) hB0 two_ne_zero).1 ?_
    have h4 : 0 ≤ (((d.size n : ℕ) : ℝ) ^ τ' * (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15)) ^ 2 :=
      sq_nonneg _
    nlinarith
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | s1x d E n (u n) ω ≤ 2 * s1a d E s n} from hx)]
    exact mul_nonneg (by linarith) (by positivity)

end WeakLawSeq

/-! ## 7. The net and the forbidden region for all `u ∈ [s,t]` -/

section Net

variable {d} {κ c τ : ℝ} {E s t : ℕ → ℝ}

/-- The clamped net of `[s n, t n]` at scale `1/netSize A N` (as the private `contTime` of
`RBM2D.Induction.Continuity`). -/
private def s1Net (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

private theorem s1Net_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : s1Net s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

private theorem s1_exists_close {s t : ℕ → ℝ} (hlen : ∀ n, t n - s n ≤ 1) (A : ℝ) (N n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s n) (t n)) :
    ∃ k, |u - s1Net s t A N n k| ≤ 1 / (netSize A N : ℝ) := by
  have hmem : u - s n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen n]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s n + netPt 1 A N k)| ≤ 1 / (netSize A N : ℝ) := by
    have h : u - (s n + netPt 1 A N k) = u - s n - netPt 1 A N k := by ring
    rw [h]; exact hk
  unfold s1Net
  rcases le_or_gt (s n + netPt 1 A N k) (t n) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- **The forbidden region for all `u ∈ [s,t]` simultaneously** (`Gopboundu` and the continuity
argument): with high probability, `‖G_u - m‖_max ∉ [M_s^{-1/4}, M_s^{-1/4}]` for every `u ∈ [s,t]`.  The
per-sequence bound `s1_wl_seq` is used at the points of a polynomial net, the union bound over
the net is `Unif.forbidden_region` and the passage to all `u` is `gopbound` (`C = 1`). -/
private theorem s1_forb (h : S1Std d κ c τ E s t) (hG : Green.GbEXPHypV3 d (κ / 2) c τ)
    (h55 : S1H55 d E s) :
    HighProbAt (Sizes.seqP d) d.size (fun n => {ω | ∀ u : TimeIcc s t n,
      s1x d E n u ω < s1a d E s n ∨ s1a d E s n < s1x d E n u ω}) := by
  have hsize := s1_hsize d h.hN
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [h.hs0 n, h.ht1 n]
  obtain ⟨C', hC', hgop⟩ := gopbound d κ E h.hκ h.hE h.hN 1 one_pos
  obtain ⟨ε, hε, hF4⟩ := s1_F4 h
  -- the net-level forbidden region
  have hpt : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun l => Fin (netSize C' (d.size l) + 1))
      (fun l k ω => {ω | s1x d E l (s1Net s t C' (d.size l) l k) ω ≤ 2 * s1a d E s l}.indicator
        (fun ω => s1x d E l (s1Net s t C' (d.size l) l k) ω) ω)
      (fun l _ _ => s1f d E s l) := by
    rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size (fun l => ⟨0⟩)]
    intro sec
    exact s1_stochDom_unit (s1_wl_seq h hG h55 (fun n => s1Net s t C' (d.size n) n (sec n))
      (fun n => s1Net_mem h.hst C' (d.size n) n (sec n)))
  have hnetSD := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := C' + 1) (by linarith)
    (hsize.eventually (card_net_le hC'.le)) hpt
  have hnet := PerTimeCalc.Unif.forbidden_region hsize
    (x := fun l (k : Fin (netSize C' (d.size l) + 1)) ω =>
      s1x d E l (s1Net s t C' (d.size l) l k) ω)
    (f := fun l _ => s1f d E s l) (a := fun l _ => s1a d E s l / 2)
    (b := fun l _ => 2 * s1a d E s l)
    (fun l _ => by
      have := Real.rpow_pos_of_pos (inv_pos.2 (s1_Ms_pos h l)) ((1 : ℝ) / 4)
      simp only [s1a]; positivity) hε
    (by filter_upwards [hF4] with l hl _; exact hl) hnetSD
  -- the good event of `gopbound`
  have hgood : HighProbAt (Sizes.seqP d) d.size (fun n => {ω : Sizes.SeqΩ d | ¬ (∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
        u ≤ 1 - ((d.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((d.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((d.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ i j : Idx (d.L n) (d.W n),
          ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) <
            ‖(Sizes.seqHflow d n u ω - spectralZ (E n) u • 1)⁻¹ i j -
              (Sizes.seqHflow d n u' ω - spectralZ (E n) u' • 1)⁻¹ i j‖)}) := by
    intro D hD
    filter_upwards [hgop D hD] with n hn
    convert hn using 2
    ext ω; simp
  refine PerTimeCalc.perTimeCalc_highProbAt_mono
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize hnet hgood) ?_
  filter_upwards [h.hR, s1_F6 h] with n hR hF6
  rintro ω ⟨hω1, hω2⟩ u
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) := s1_one_le_size d n
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk⟩ := s1_exists_close hlen C' (d.size n) n u.2
  have hθ := s1Net_mem h.hst C' (d.size n) n k
  have hdist : |(u : ℝ) - s1Net s t C' (d.size n) n k| ≤ ((d.size n : ℕ) : ℝ) ^ (-C') := by
    refine hk.trans ?_
    have h1 : ((d.size n : ℕ) : ℝ) ^ C' ≤ (netSize C' (d.size n) : ℝ) :=
      rpow_le_netSize C' (d.size n)
    calc 1 / (netSize C' (d.size n) : ℝ) ≤ 1 / ((d.size n : ℕ) : ℝ) ^ C' :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) h1
      _ = ((d.size n : ℕ) : ℝ) ^ (-C') := by rw [Real.rpow_neg hN0.le, one_div]
  have hrange : ∀ v ∈ Set.Icc (s n) (t n), v ≤ 1 - ((d.size n : ℕ) : ℝ)⁻¹ := by
    intro v hv
    have h1 : ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.hτ])
    rw [Real.rpow_neg_one] at h1
    linarith [hv.2]
  have hgop : ∀ i j, ‖(Sizes.seqHflow d n u ω - spectralZ (E n) u •
        (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ i j -
      (Sizes.seqHflow d n (s1Net s t C' (d.size n) n k) ω -
        spectralZ (E n) (s1Net s t C' (d.size n) n k) •
        (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ i j‖ ≤
      ((d.size n : ℕ) : ℝ)⁻¹ := by
    intro i j
    by_contra hlt
    push Not at hlt
    refine hω2 ⟨u, s1Net s t C' (d.size n) n k, (h.hs0 n).trans u.2.1, (h.hs0 n).trans hθ.1,
      hrange u u.2, hrange _ hθ, hdist, i, j, ?_⟩
    rwa [Real.rpow_neg_one]
  have hgop' : ∀ i j, ‖(Sizes.seqHflow d n (s1Net s t C' (d.size n) n k) ω -
        spectralZ (E n) (s1Net s t C' (d.size n) n k) •
        (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ i j -
      (Sizes.seqHflow d n u ω - spectralZ (E n) u •
        (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ i j‖ ≤
      ((d.size n : ℕ) : ℝ)⁻¹ := fun i j => by rw [norm_sub_rev]; exact hgop i j
  have hup := s1xM_le_add hgop
  have hdown := s1xM_le_add hgop'
  have hapos : 0 < s1a d E s n := by
    have := Real.rpow_pos_of_pos (inv_pos.2 (s1_Ms_pos h n)) ((1 : ℝ) / 4)
    exact this
  rcases hω1 k with h1 | h1
  · left
    change s1xM (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) < s1a d E s n
    change s1xM (d.L n) (d.W n) (E n) (s1Net s t C' (d.size n) n k)
      (Sizes.seqHflow d n (s1Net s t C' (d.size n) n k) ω) < s1a d E s n / 2 at h1
    linarith
  · right
    change s1a d E s n < s1xM (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)
    change 2 * s1a d E s n < s1xM (d.L n) (d.W n) (E n) (s1Net s t C' (d.size n) n k)
      (Sizes.seqHflow d n (s1Net s t C' (d.size n) n k) ω) at h1
    linarith

end Net

/-! ## 8. The continuity argument, and the two per-time conclusions -/

section Bootstrap

variable {d} {κ c τ : ℝ} {E s t : ℕ → ℝ}

/-- `u ↦ ‖G_u - m‖_max` is continuous on `[a, b]`, `b < 1`, for every sample point
(`continuous_green_Hflow_moving_time` applied to the clamped path `z(min(u, b))`). -/
private theorem s1x_continuousOn (d : Sizes) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| < 2) {a b : ℝ}
    (hb : b < 1) (ω : Sizes.SeqΩ d) :
    ContinuousOn (fun v => s1x d E n v ω) (Set.Icc a b) := by
  set z : ℝ → ℂ := fun v => spectralZ (E n) (min v b) with hz
  have hzc : Continuous z :=
    (continuous_spectralZ (E n)).comp (continuous_id.min continuous_const)
  have hzi : ∀ v, (z v).im ≠ 0 := by
    intro v
    simp only [hz, spectralZ_im]
    have : 0 < 1 - min v b := by have := min_le_right v b; linarith
    exact (mul_pos this (spectralM_im_pos hE)).ne'
  have hcont := continuous_green_Hflow_moving_time (d.L n) (d.W n) (Sizes.slice d n ω) hzc hzi
  have hfun : Continuous fun v => Finset.univ.sup' Finset.univ_nonempty
      (fun q : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) =>
        ‖green (Hflow (d.L n) (d.W n) v (Sizes.slice d n ω)) (z v) q.1 q.2 -
          (if q.1 = q.2 then spectralM (E n) else 0)‖) := by
    refine Continuous.finset_sup'_apply _ fun q _ => ?_
    exact ((hcont.matrix_elem q.1 q.2).sub continuous_const).norm
  refine hfun.continuousOn.congr fun v hv => ?_
  simp only [s1x, s1xM, llErrMat, hz, min_eq_left hv.2, green, Sizes.seqHflow]

private theorem s1_card_idx (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  change (Fintype.card (Z2 (d.W n * d.L n)) : ℝ) = _
  simp [Z2, Fintype.card_prod, ZMod.card, Sizes.size, pow_two]

/-- **The continuity argument**: with high probability, `‖G_u - m‖_max < M_s^{-1/4}`
for every `u ∈ [s,t]`. -/
private theorem s1_boot (h : S1Std d κ c τ E s t) (hG : Green.GbEXPHypV3 d (κ / 2) c τ)
    (h55 : S1H55 d E s) (hIL : InitLocal d E s) :
    HighProbAt (Sizes.seqP d) d.size (fun n => {ω | ∀ u : TimeIcc s t n,
      s1x d E n u ω < s1a d E s n}) := by
  have hsize := s1_hsize d h.hN
  -- the initial condition
  have hinit : HighProbAt (Sizes.seqP d) d.size
      (fun n => {ω | s1x d E n (s n) ω < s1a d E s n}) := by
    obtain ⟨τ₀, hτ₀, hF3⟩ := s1_F3 h
    have hC : ∀ᶠ l : ℕ in atTop,
        (Fintype.card (Unit × Idx (d.L l) (d.W l) × Idx (d.L l) (d.W l)) : ℝ) ≤
          ((d.size l : ℕ) : ℝ) ^ (2 : ℝ) := Eventually.of_forall fun l => by
      rw [Real.rpow_two]
      rw [Fintype.card_prod Unit (Idx (d.L l) (d.W l) × Idx (d.L l) (d.W l)),
        Fintype.card_prod (Idx (d.L l) (d.W l)) (Idx (d.L l) (d.W l)), Fintype.card_unit]
      push_cast
      rw [s1_card_idx]; ring_nf; exact le_rfl
    have hev := s1_highProb_of_pt (P := Sizes.seqP d) (size := d.size) (C := 2) (by norm_num) hC
      hIL hτ₀
    refine PerTimeCalc.perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hF3] with n hn ω hω
    have hb : s1xM (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) ≤
        ((d.size n : ℕ) : ℝ) ^ τ₀ * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ ((1 : ℝ) / 2) :=
      s1xM_le fun i j => hω ((), i, j)
    exact lt_of_le_of_lt hb hn
  have hcont : HighProbAt (Sizes.seqP d) d.size (fun l => {ω | ContinuousOn
      (fun u => s1x d E l u ω) (Set.Icc (s l) (t l))}) :=
    PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun l ω _ =>
        s1x_continuousOn d E l (s1_bulk h.hκ (h.hE l)).1 (h.ht1 l) ω)
  exact PerTimeCalc.stepOneBootstrap hsize (M := fun l v ω => s1x d E l v ω)
    (a := fun l _ => s1a d E s l) (b := fun l _ => s1a d E s l) (s := s) (t := t)
    hcont (fun l => continuousOn_const) (Eventually.of_forall fun l u => le_rfl)
    (s1_forb h hG h55) hinit

/-- **(`Gtmwc`) per time**: `‖G_u - m‖_max ≺ M_u^{-1/4}` uniformly in `u ∈ [s,t]`. -/
private theorem s1_weakPT (h : S1Std d κ c τ E s t) (hG : Green.GbEXPHypV3 d (κ / 2) c τ)
    (h55 : S1H55 d E s) (hIL : InitLocal d E s) : Step1WeakLawPT d E s t := by
  have hsize := s1_hsize d h.hN
  have hboot := s1_boot h hG h55 hIL
  unfold Step1WeakLawPT
  refine PerTimeCalc.PerTime.stochDom_of_highProb hsize (fun n p ω =>
    Real.rpow_nonneg (inv_nonneg.2 (s1_Mu_pos h n p.1.2.2).le) _) ?_
  refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot (Eventually.of_forall fun n ω hω p => ?_)
  obtain ⟨u, i, j⟩ := p
  have h1 : llErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i j ≤ s1x d E n u ω :=
    s1xM_ge _ _ _ i j
  have h2 := hω u
  have hMu := s1_Mu_pos h n u.2.2
  have h3 : scaleM (d.L n) (d.W n) (E n) u ≤ s1Ms d E s n :=
    (scaleM_anti_ratio (W := d.W n) (s1_one_le_L d n) (s1_bulk h.hκ (h.hE n)).1 u.2.1
      (lt_of_le_of_lt u.2.2 (h.ht1 n))).1
  have h4 : s1a d E s n ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (inv_nonneg.2 (s1_Ms_pos h n).le) (inv_anti₀ hMu h3) (by norm_num)
  exact (h1.trans h2.le).trans h4

/-- **(`lRB1`) per time**: `|𝓛_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{2(k-1)} M_u^{-(k-1)}` uniformly in `u ∈ [s,t]`: the
indicator of `{‖G_u‖_max ≤ 2}` is removed by the continuity argument. -/
private theorem s1_loopPT (h : S1Std d κ c τ E s t) (hG : Green.GbEXPHypV3 d (κ / 2) c τ)
    (h55 : S1H55 d E s) (hIL : InitLocal d E s) : Step1LoopPT d E s t := by
  intro k hk
  have hsize := s1_hsize d h.hN
  have hboot := s1_boot h hG h55 hIL
  refine PerTimeCalc.PerTime.stochDom_of_indicator hsize
    (Ωs := fun n p => {ω | gMax (E n) (p.1 : ℝ) (Sizes.seqHflow d n p.1 ω) ≤ 2}) ?_ ?_
  · refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot ?_
    filter_upwards [s1_F7 h] with n hF7 ω hω p
    have h1 := s1_gMax_le (L := d.L n) (W := d.W n) (u := (p.1 : ℝ))
      (s1_bulk h.hκ (h.hE n)).1.le (Sizes.seqHflow d n p.1 ω)
    have h2 := hω p.1
    change gMax (E n) (p.1 : ℝ) (Sizes.seqHflow d n p.1 ω) ≤ 2
    change s1xM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) < s1a d E s n at h2
    linarith
  · have key := Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size h.hst
      (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
      (fun n v q ω => (if gMax (E n) v (Sizes.seqHflow d n v ω) ≤ 2 then 1 else 0) *
        loopAbs (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (ellT (d.L n) v / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ (k - 1))
      (fun u hu => s1_LI h h55 u hu hk)
    have hfun : (fun (n : ℕ) (p : TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
        (ω : Sizes.SeqΩ d) =>
          ({ω | gMax (E n) (p.1 : ℝ) (Sizes.seqHflow d n p.1 ω) ≤ 2}).indicator
            (fun ω => loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
            ω) =
        fun n p ω => (if gMax (E n) (p.1 : ℝ) (Sizes.seqHflow d n p.1 ω) ≤ 2 then 1 else 0) *
          loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 := by
      funext n p ω
      by_cases hg : gMax (E n) (p.1 : ℝ) (Sizes.seqHflow d n p.1 ω) ≤ 2 <;>
        simp [Set.indicator, hg]
    rw [hfun]
    exact key

end Bootstrap

/-! ## 9. The theorem -/

/-- **Step 1 of `lem:main_ind`**: (`lRB1`) and (`Gtmwc`) uniformly in `u ∈ [s,t]`,
in the form `Step1TargetV3`.  Proof: the per-time statements `s1_loopPT`, `s1_weakPT`
(continuity argument from `conArg`, `GbEXPHypV3`, `gopbound`, `stepOneBootstrap`) and the net lift
`step1NetLift`. -/
theorem step1 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step1TargetV3 d κ c τ E s t := by
  intro hK hG hM
  have h := s1_std_of_mainIndHyp hM
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hIK, -, hIL⟩ := hM
  have h55 := s1_h55 h hIK hK
  have hnet := step1NetLift d E κ c τ s t h.hκ h.hE h.hc h.hτ h.hs0 h.hst h.ht1 h.hN h.hB
    h.hCond h.hR
  exact ⟨hnet.1 (s1_loopPT h hG h55 hIL), hnet.2 (s1_weakPT h hG h55 hIL)⟩

end RBM.Ind
