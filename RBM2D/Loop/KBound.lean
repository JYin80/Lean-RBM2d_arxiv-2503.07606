/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.KBoundCut
import RBM2D.Loop.KBoundInner

/-!
# `(eq:bcal_k_pi)` for all `π` and `ML:Kbound` = `(eq:bcal_k_2)`

Paper: Lemma `ML:Kbound+pi`, `(eq:bcal_k_2)`, `(eq:bcal_k_pi)`; and `ML:Kbound` of the
introduction.

Declarations (namespace `RBM.KLoop`):

* the definitions `KpiBoundAt`, `KpiEmptyAt`, `InnerSumAt`;
* `Kpi_step` : the induction step, from `Kpi_cut`;
* `Kpi_bound_prec` : `(eq:bcal_k_pi)` (strong induction using `Kpi_step`, `Kpi_empty_prec`,
  `innerId_sum_prec`);
* `Kbound_prec` : `ML:Kbound` (`(Kn2sol)` with `Prop5Hyp` and the bulk gap for `n = 2`,
  `(KKpi)` for `n ≥ 3`, `𝒦 = m(σ₁)` for `n = 1`);
* `Kbound_prec_uncond` : `Kbound_prec` with `c = 1/20000` and the hypotheses discharged by
  `prop5Hyp_holds`, `prop6Hyp_holds`.

The skeleton of the `n ≥ 3` case of `Kbound_prec` follows the one-dimensional argument, with
the `d = 2` prefactor `W^{-2(n-1)}` and `≺` at fixed `n` in place of a constant `C`
uniform in `n ≤ N_max`.  Every helper is `private`.
-/

namespace RBM.KLoop

open Finset

/-! ## 1. The induction statements -/

/-- `(eq:bcal_k_pi)` at a fixed length `n` (the induction statement): uniformly in `σ, π, a`. -/
def KpiBoundAt (n : ℕ) [NeZero n] (κ : ℝ) : Prop :=
  UnifDetDom
    (U := fun N => (p : Par κ N) × (Fin n → Bool) × Finset (Fin n × Fin n) × (Fin n → Z2 p.L))
    (fun _ u => ‖Kpi u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2.2 u.2.2.1‖)
    (fun _ u => Xt u.1.L u.1.E u.1.t ^ (n - 1))

/-- `(eq:bcal_k_pi)` at a fixed length `n` for `π = ∅` (every `σ`). -/
def KpiEmptyAt (n : ℕ) [NeZero n] (κ : ℝ) : Prop :=
  UnifDetDom
    (U := fun N => (p : Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
    (fun _ u => ‖Kpi u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2 ∅‖)
    (fun _ u => Xt u.1.L u.1.E u.1.t ^ (n - 1))

/-- `innerSum_pin` at a fixed size `k`. -/
def InnerSumAt (k : ℕ) [NeZero k] (κ : ℝ) : Prop :=
  UnifDetDom
    (U := fun N => (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
      (Fin k → Z2 p.L))
    (fun _ u => ∑ x : Z2 u.1.L,
      ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2 u.2.1.1.2 x‖)
    (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 2))

/-! ## 2. Private helpers -/

section Helpers

private theorem kb_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖t m(s) m(s')‖ = t` for `t ≥ 0`. -/
private theorem kb_norm_xi {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (mSig E s * mSig E s')‖ = t := by
  rw [norm_mul, norm_mul, kb_norm_mSig hE, kb_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg ht, mul_one, mul_one]

/-- The `τ`-level of `KpiBoundAt` at a fixed `N`. -/
private def KpiBoundN (n : ℕ) [NeZero n] (κ τ : ℝ) (N : ℕ) : Prop :=
  ∀ u : (p : Par κ N) × (Fin n → Bool) × Finset (Fin n × Fin n) × (Fin n → Z2 p.L),
    ‖Kpi u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2.2 u.2.2.1‖
      ≤ (N : ℝ) ^ τ * Xt u.1.L u.1.E u.1.t ^ (n - 1)

/-- The `τ`-level of `InnerSumAt` at a fixed `N`. -/
private def InnerSumN (k : ℕ) [NeZero k] (κ τ : ℝ) (N : ℕ) : Prop :=
  ∀ u : (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
      (Fin k → Z2 p.L),
    ∑ x : Z2 u.1.L, ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2 u.2.1.1.2 x‖
      ≤ (N : ℝ) ^ τ * Xt u.1.L u.1.E u.1.t ^ (k - 2)

variable (L : ℕ) [NeZero L]

private theorem kb_norm_one_sub_ofReal {t : ℝ} (ht1 : t < 1) :
    ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

private theorem kb_ellT_eq {t : ℝ} (ht1 : t < 1) :
    ellT L t = min (Real.sqrt (1 - t))⁻¹ (L : ℝ) := by
  rw [ellT, ellhat, kappa, kb_norm_one_sub_ofReal ht1]

/-- `ℓ_t ≥ 1`. -/
private theorem kb_one_le_ellT (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ ellT L t := by
  rw [kb_ellT_eq L ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine le_min ((one_le_inv₀ hs0).2 hs1) ?_
  have : (3 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

private theorem kb_etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem kb_spectralM_im_le_one (E : ℝ) : (Gauss.spectralM E).im ≤ 1 := by
  rw [Gauss.spectralM_im]
  have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
  linarith

/-- `M_t⁻¹ = W⁻² X_t` (the `W`-power identity at one edge). -/
private theorem kb_Mt_inv (W : ℕ) (E t : ℝ) :
    (Mt L W E t)⁻¹ = ((W : ℝ) ^ 2)⁻¹ * Xt L E t := by
  rw [Mt, Xt, mul_assoc, mul_inv]

/-- The right side of `Prop5Hyp` at `ξ = t` is at most `X_t`. -/
private theorem kb_rhs_t_le (hL : 3 ≤ L) {E t c d : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hc : 0 < c) (hd : 0 ≤ d) :
    Real.exp (-(c * d) / ellhat L (t : ℂ)) / (‖(1 : ℂ) - (t : ℂ)‖ * ellhat L (t : ℂ) ^ 2)
      ≤ Xt L E t := by
  have hℓ := kb_one_le_ellT L hL ht0 ht1
  have hℓ' : ellhat L (t : ℂ) = ellT L t := rfl
  rw [hℓ', kb_norm_one_sub_ofReal ht1, Xt, kb_etaT_eq]
  have him0 := Gauss.spectralM_im_pos hE
  have him1 := kb_spectralM_im_le_one E
  have h1t : 0 < 1 - t := by linarith
  have hℓ0 : 0 < ellT L t := by linarith
  have hexp : Real.exp (-(c * d) / ellT L t) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (mul_nonneg hc.le hd) hℓ0.le)
  have hden : 0 < (1 - t) * ellT L t ^ 2 := by positivity
  calc Real.exp (-(c * d) / ellT L t) / ((1 - t) * ellT L t ^ 2)
      ≤ 1 / ((1 - t) * ellT L t ^ 2) := div_le_div_of_nonneg_right hexp hden.le
    _ ≤ (ellT L t ^ 2 * ((1 - t) * (Gauss.spectralM E).im))⁻¹ := by
        rw [one_div]
        refine inv_anti₀ (by positivity) ?_
        calc ellT L t ^ 2 * ((1 - t) * (Gauss.spectralM E).im)
            = ((1 - t) * ellT L t ^ 2) * (Gauss.spectralM E).im := by ring
          _ ≤ ((1 - t) * ellT L t ^ 2) * 1 := mul_le_mul_of_nonneg_left him1 hden.le
          _ = (1 - t) * ellT L t ^ 2 := mul_one _

end Helpers

/-! ## 3. The bulk gap -/

section Gap

private theorem kb_gapK_nonneg (κ : ℝ) : 0 ≤ gapK κ :=
  le_min zero_le_one (Real.sqrt_nonneg _)

private theorem kb_gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem kb_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ :=
  lt_min one_pos (Real.sqrt_pos.2 (by nlinarith))

private theorem kb_gapK_sq_le {κ : ℝ} (hκ2 : κ ≤ 2) (hκ : 0 < κ) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ κ * (4 - κ) / 2 := by nlinarith
  calc gapK κ ^ 2 ≤ (Real.sqrt (κ * (4 - κ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (kb_gapK_nonneg κ) (min_le_right _ _) 2
    _ = κ * (4 - κ) / 2 := Real.sq_sqrt h0

/-- The bulk gap: `c_κ ≤ |1 - t m²|` for `t ≥ 0`, `|E| ≤ 2 - κ` (`m = m^{(E)}`). -/
private theorem kb_gap_le_norm {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ)
    (ht : 0 ≤ t) : gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ := by
  have hE2 : |E| ≤ 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set s := Real.sqrt (4 - E ^ 2) with hs_def
  have hs : s ^ 2 = 4 - E ^ 2 := Gauss.spectralM_sqrt_sq hE2
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him : (Gauss.spectralM E).im = s / 2 := Gauss.spectralM_im E
  have hzre : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).re
      = 1 - t * ((-E / 2) ^ 2 - (s / 2) ^ 2) := by
    simp [pow_two, Complex.mul_re, hre, him]
  have hzim : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).im
      = -(t * (2 * (-E / 2) * (s / 2))) := by
    simp only [pow_two, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub, hre, him]
    ring
  have hsq : ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ ^ 2
      = 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    linear_combination (t / 2 + t ^ 2 * (8 + (s ^ 2 - (4 - E ^ 2))) / 16) * hs
  have hg0 := kb_gapK_nonneg κ
  have hg1 : gapK κ ^ 2 ≤ 1 := pow_le_one₀ hg0 (kb_gapK_le_one κ)
  have hg2 := kb_gapK_sq_le hκ2 hκ
  have hmain : gapK κ ^ 2 ≤ 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    by_cases hc : E ^ 2 ≤ 2
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hc), sq_nonneg t]
    · have hc := not_le.1 hc
      have hy : E ^ 2 ≤ (2 - κ) ^ 2 := by
        rw [← sq_abs E]
        exact pow_le_pow_left₀ (abs_nonneg E) hE 2
      have hk4 : 0 ≤ 4 - (2 - κ) ^ 2 := by nlinarith
      have h1 : κ * (4 - κ) / 2 ≤ E ^ 2 * (4 - E ^ 2) / 4 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hy) (show 0 ≤ E ^ 2 + (2 - κ) ^ 2 - 4 by nlinarith),
          mul_nonneg hk4 (show 0 ≤ (2 - κ) ^ 2 - 2 by nlinarith)]
      nlinarith [sq_nonneg (t - (E ^ 2 / 2 - 1))]
  by_contra hlt
  have hlt := not_le.1 hlt
  have := norm_nonneg ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2)
  nlinarith

private theorem kb_gap_le_norm_mSig {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ)
    (ht : 0 ≤ t) (s : Bool) : gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * mSig E s ^ 2‖ := by
  cases s
  · have h := kb_gap_le_norm hκ hE ht
    have : (1 : ℂ) - (t : ℂ) * mSig E false ^ 2
        = (starRingEnd ℂ) ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2) := by
      simp [mSig]
    rw [this, Complex.norm_conj]
    exact h
  · simpa [mSig] using kb_gap_le_norm hκ hE ht

/-- The right side of `Prop5Hyp` is at most `c_κ⁻¹` when `c_κ ≤ |1 - ξ|`
(`ℓ̂(ξ)² |1 - ξ| ≥ min(1, L² |1 - ξ|) ≥ c_κ`). -/
private theorem kb_rhs_gap_le {L : ℕ} [NeZero L] {ξ : ℂ} {g c d : ℝ} (hg : 0 < g)
    (hg1 : g ≤ 1) (hgξ : g ≤ ‖(1 : ℂ) - ξ‖) (hc : 0 < c) (hd : 0 ≤ d) (hL : 3 ≤ L) :
    Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2) ≤ g⁻¹ := by
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hκξ : Real.sqrt g ≤ kappa ξ := Real.sqrt_le_sqrt hgξ
  have hκpos : 0 < kappa ξ := lt_of_lt_of_le hsg hκξ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hℓpos : 0 < ellhat L ξ := lt_min (inv_pos.2 hκpos) (by linarith)
  have hkl : Real.sqrt g ≤ kappa ξ * ellhat L ξ := by
    rcases le_total (kappa ξ)⁻¹ (L : ℝ) with h | h
    · have : ellhat L ξ = (kappa ξ)⁻¹ := min_eq_left h
      rw [this, mul_inv_cancel₀ hκpos.ne']
      exact Real.sqrt_le_one.2 hg1 |>.trans_eq rfl
    · have : ellhat L ξ = L := min_eq_right h
      rw [this]
      nlinarith
  have hden : g ≤ ‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2 := by
    rw [← kappa_sq, ← mul_pow]
    calc g = Real.sqrt g ^ 2 := (Real.sq_sqrt hg.le).symm
      _ ≤ _ := pow_le_pow_left₀ hsg.le hkl 2
  have hexp : Real.exp (-(c * d) / ellhat L ξ) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (mul_nonneg hc.le hd) hℓpos.le)
  calc Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2)
      ≤ 1 / g := div_le_div₀ zero_le_one hexp hg hden
    _ = g⁻¹ := one_div g

/-- **The `n = 2` edge bound from `Prop5Hyp`**: for every `τ > 0`, eventually in `N`, every
entry of `Θ_{t m(s₁) m(s₂)}` is at most `N^τ c_κ⁻¹ X_t`. -/
private theorem kb_theta_two_le {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (h5 : Prop5Hyp κ c)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p : Par κ N) (s₁ s₂ : Bool) (x y : Z2 p.L),
      ‖Theta p.L ((p.t : ℂ) * (mSig p.E s₁ * mSig p.E s₂)) x y‖ ≤
        (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Xt p.L p.E p.t) := by
  filter_upwards [h5 τ hτ] with N hN p s₁ s₂ x y
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg p.E, p.hE]
  have hE : |p.E| < 2 := by linarith [p.hE]
  have hg := kb_gapK_pos hκ hκ2
  have hg1 := kb_gapK_le_one κ
  have hX1 : 1 ≤ Xt p.L p.E p.t := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hg1' : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hg).2 hg1
  have hNτ : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
  have hd : (0 : ℝ) ≤ (zdist2 p.L (x - y) : ℝ) := Nat.cast_nonneg _
  -- the same-sign case `ξ = t m(s)²`
  have hsame : ∀ s : Bool,
      ‖Theta p.L ((p.t : ℂ) * (mSig p.E s * mSig p.E s)) x y‖ ≤
        (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Xt p.L p.E p.t) := by
    intro s
    have h := hN ⟨p, if s then 0 else 1, x, y⟩
    have hξ : xiSet p.E p.t (if s then 0 else 1) = (p.t : ℂ) * (mSig p.E s * mSig p.E s) := by
      cases s <;> simp [xiSet, sq]
    simp only [hξ] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hNτ)
    have hgξ := kb_gap_le_norm_mSig hκ p.hE p.ht0 s
    rw [sq] at hgξ
    refine (kb_rhs_gap_le hg hg1 hgξ hc hd p.hL).trans ?_
    calc (gapK κ)⁻¹ = (gapK κ)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (gapK κ)⁻¹ * Xt p.L p.E p.t :=
          mul_le_mul_of_nonneg_left hX1 (by positivity)
  -- the opposite-sign case `ξ = t`
  have hmm : mSig p.E true * mSig p.E false = 1 := by
    have h1 : Complex.normSq (Gauss.spectralM p.E) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Gauss.norm_spectralM (by linarith), one_pow]
    simp [mSig, Complex.mul_conj, h1]
  have hopp : ‖Theta p.L (p.t : ℂ) x y‖ ≤ (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Xt p.L p.E p.t) := by
    have h := hN ⟨p, 2, x, y⟩
    have hξ : xiSet p.E p.t 2 = (p.t : ℂ) := by simp [xiSet]
    simp only [hξ] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hNτ)
    refine (kb_rhs_t_le p.L p.hL hE p.ht0 p.ht1 hc hd).trans ?_
    calc Xt p.L p.E p.t = 1 * Xt p.L p.E p.t := (one_mul _).symm
      _ ≤ (gapK κ)⁻¹ * Xt p.L p.E p.t :=
          mul_le_mul_of_nonneg_right hg1' (by linarith)
  cases s₁ <;> cases s₂
  · exact hsame false
  · rw [mul_comm (mSig p.E false), hmm, mul_one]; exact hopp
  · rw [hmm, mul_one]; exact hopp
  · exact hsame true

end Gap

/-! ## 4. The induction step and `(eq:bcal_k_pi)` for all `π` -/

/-- **The induction step** (strong induction on the number `n` of polygon vertices): the bound
at `n` follows from the `π = ∅` bound at `n`, the bound at every `3 ≤ n'' < n` (outer
polygons, `n'' = n - wIn J + 1`), and the inner sums at every `3 ≤ k < n` (inner polygons,
`k = wIn J + 1`).  No hypothesis on `Θ` enters the step itself.  The proof uses `Kpi_cut`. -/
theorem Kpi_step :
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ κ : ℝ, 0 < κ →
    KpiEmptyAt n κ →
    (∀ (n'' : ℕ) [NeZero n''], 3 ≤ n'' → n'' < n → KpiBoundAt n'' κ) →
    (∀ (k : ℕ) [NeZero k], 3 ≤ k → k < n → InnerSumAt k κ) →
    KpiBoundAt n κ := by
  intro n _ hn κ hκ hempty hout hin τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hO : ∀ᶠ N : ℕ in Filter.atTop, ∀ n'' ∈ Finset.range n, ∀ h3 : 3 ≤ n'',
      @KpiBoundN n'' ⟨by omega⟩ κ (τ / 2) N := by
    refine (Filter.eventually_all_finset _).2 fun n'' hn'' => ?_
    by_cases h3 : 3 ≤ n''
    · have : NeZero n'' := ⟨by omega⟩
      filter_upwards [hout n'' h3 (Finset.mem_range.1 hn'') (τ / 2) hτ2] with N hN _
      exact hN
    · exact Filter.Eventually.of_forall fun N h3' => absurd h3' h3
  have hI : ∀ᶠ N : ℕ in Filter.atTop, ∀ k ∈ Finset.range n, ∀ h3 : 3 ≤ k,
      @InnerSumN k ⟨by omega⟩ κ (τ / 2) N := by
    refine (Filter.eventually_all_finset _).2 fun k hk => ?_
    by_cases h3 : 3 ≤ k
    · have : NeZero k := ⟨by omega⟩
      filter_upwards [hin k h3 (Finset.mem_range.1 hk) (τ / 2) hτ2] with N hN _
      exact hN
    · exact Filter.Eventually.of_forall fun N h3' => absurd h3' h3
  filter_upwards [hempty τ hτ, hO, hI] with N hNE hNO hNI
  rintro ⟨p, σ, π, a⟩
  have hE2 : |p.E| ≤ 2 := by have := p.hE; linarith
  have hX0 : 0 ≤ Xt p.L p.E p.t := Xt_nonneg p.L p.ht1
  have hN0 : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hRHS : 0 ≤ (N : ℝ) ^ τ * Xt p.L p.E p.t ^ (n - 1) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N) τ
    positivity
  by_cases hπ0 : π = ∅
  · subst hπ0
    exact hNE ⟨p, σ, a⟩
  rcases (TSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · simp only [Kpi, hemp, Finset.sum_empty, norm_zero]
    exact hRHS
  obtain ⟨hF₀T, hπ⟩ := Finset.mem_filter.1 hF₀
  have hsub : π ⊆ diagonals n := by rw [← hπ]; exact Flong_subset_diagonals hF₀T σ
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hsub (Finset.nonempty_iff_ne_empty.2 hπ0)
  have hJd : IsDiag n J.1 J.2 := (Finset.mem_filter.1 (hsub hJ)).2
  have hJlong : σ J.1 ≠ σ J.2 := by
    have hJ' : J ∈ Flong F₀ σ := by rw [hπ]; exact hJ
    exact (Finset.mem_filter.1 hJ').2
  obtain ⟨hJ12, hJadj, hJwhole⟩ := hJd
  rw [Fin.lt_def] at hJ12
  have hJ2n := J.2.isLt
  have hw2 : 2 ≤ wIn J := by simp only [wIn]; omega
  have hwn : wIn J + 2 ≤ n := by
    simp only [wIn]
    by_cases h0 : J.1.val = 0
    · have : J.2.val ≠ n - 1 := fun h => hJwhole ⟨h0, h⟩
      omega
    · omega
  have hm : ∀ s s' : Bool, ‖(p.t : ℂ) * (mSig p.E s * mSig p.E s')‖ < 1 := fun s s' => by
    rw [kb_norm_xi hE2 p.ht0]; exact p.ht1
  rw [Kpi_cut p.L p.hL n hn (mSig p.E) p.t hm σ F₀ hF₀T π J hπ hJ hinner a]
  have hB : ∀ w, ‖Kpi p.L (mSig p.E) p.t (sigmaOut σ J) (aOut J a w)
      ((π.erase J).image (shiftOut J))‖
        ≤ (N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1) := fun w =>
    hNO (n - wIn J + 1) (Finset.mem_range.2 (by omega)) (by omega)
      ⟨p, sigmaOut σ J, (π.erase J).image (shiftOut J), aOut J a w⟩
  have hroot : sigmaIn σ J (Fin.last (wIn J)) ≠ sigmaIn σ J (Fin.last (wIn J) + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last (wIn J)) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last]
      congr 1
      ext
      simp only [wIn]
      omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]
      congr 1
      ext
      simp only
      omega
    rw [e1, e2]
    exact Ne.symm hJlong
  have hA := hNI (wIn J + 1) (Finset.mem_range.2 (by omega)) (by omega)
    ⟨p, ⟨(sigmaIn σ J, Fin.last (wIn J)), hroot⟩, aIn J a⟩
  have hξ : ‖(p.t : ℂ) * (mSig p.E (σ J.1) * mSig p.E (σ J.2))‖ ≤ 1 := by
    rw [kb_norm_xi hE2 p.ht0]; exact p.ht1.le
  refine (norm_cut_le p.L p.hL _ _ _ hB).trans ?_
  have hM0 : 0 ≤ (N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1) := by positivity
  have hsum0 : 0 ≤ ∑ u : Z2 p.L,
      ‖innerId p.L (mSig p.E) p.t (sigmaIn σ J) (aIn J a) (Fin.last (wIn J)) u‖ :=
    Finset.sum_nonneg fun u _ => norm_nonneg _
  have hpow : Xt p.L p.E p.t ^ (wIn J + 1 - 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1)
      = Xt p.L p.E p.t ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  calc ‖(p.t : ℂ) * (mSig p.E (σ J.1) * mSig p.E (σ J.2))‖ *
        (∑ u : Z2 p.L,
          ‖innerId p.L (mSig p.E) p.t (sigmaIn σ J) (aIn J a) (Fin.last (wIn J)) u‖) *
        ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1))
      ≤ 1 * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (wIn J + 1 - 2)) *
          ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hξ hA hsum0 zero_le_one) hM0
    _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) *
          (Xt p.L p.E p.t ^ (wIn J + 1 - 2) * Xt p.L p.E p.t ^ (n - wIn J + 1 - 1)) := by ring
    _ = (N : ℝ) ^ τ * Xt p.L p.E p.t ^ (n - 1) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half N hτ, hpow]

/-- **`(eq:bcal_k_pi)`**: `K^{(π)}_{t,σ,a} ≺ (ℓ_t² η_t)^{-n+1}`,
for `n ≥ 3`, every `σ`, `π`, `a`.  Conditional on `Prop5Hyp κ c` and `Prop6Hyp κ`.  Proof:
strong induction on `n` with `Kpi_step`, `Kpi_empty_prec` and `innerId_sum_prec`. -/
theorem Kpi_bound_prec :
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × (Fin n → Bool) × Finset (Fin n × Fin n) × (Fin n → Z2 p.L))
      (fun _ u => ‖Kpi u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2.2 u.2.2.1‖)
      (fun _ u => (ellT u.1.L u.1.t ^ 2 * etaT u.1.E u.1.t)⁻¹ ^ (n - 1)) := by
  intro n _ hn κ c hκ hc h5 h6
  have key : ∀ n : ℕ, ∀ [NeZero n], 3 ≤ n → KpiBoundAt n κ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro _ hn
      exact Kpi_step n hn κ hκ (Kpi_empty_prec n hn κ c hκ hc h5 h6)
        (fun n'' _ h3 hlt => ih n'' hlt h3)
        (fun k _ h3 _ => innerId_sum_prec k h3 κ c hκ hc h5 h6)
  exact key n hn

/-! ## 5. `ML:Kbound` = `(eq:bcal_k_2)` -/

section Kbound

private theorem kb_loopOf_one (L : ℕ) [NeZero L] (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    loopOf L σ a = ⟨[σ 0], [a 0]⟩ := by
  simp [loopOf, List.ofFn_succ]

private theorem kb_loopOf_two (L : ℕ) [NeZero L] (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    loopOf L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  simp [loopOf, List.ofFn_succ]

private theorem kb_Kcal_one (L W : ℕ) [NeZero L] (E t : ℝ) (s : Bool) (a : Z2 L) :
    Kcal L W E t ⟨[s], [a]⟩ = mSig E s := by
  simp [Kcal, Kgen, LoopIdx.length]

private theorem kb_norm_W (W : ℕ) (j : ℕ) :
    ‖((W : ℂ) ^ 2)⁻¹ ^ j‖ = (((W : ℝ) ^ 2)⁻¹) ^ j := by
  rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]

/-- **`ML:Kbound+pi`, `(eq:bcal_k_2)`** (= `ML:Kbound`, `(eq:bcal_k)`):
`𝒦_{t,σ,a} ≺ M_t^{-n+1}`, with `n`, `κ` fixed before `∀ τ, ∀ᶠ N`, uniformly in
`W² L² = N`, `|E| ≤ 2 - κ`, `t ∈ [0,1)`, `σ`, `a`.  Conditional on `Prop5Hyp κ c` and
`Prop6Hyp κ`; the unconditional form is `Kbound_prec_uncond`. -/
theorem Kbound_prec :
  ∀ (n : ℕ), 1 ≤ n → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom (U := fun N => (p : Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
      (fun _ u => ‖Kcal u.1.L u.1.W u.1.E u.1.t (loopOf u.1.L u.2.1 u.2.2)‖)
      (fun _ u => (Mt u.1.L u.1.W u.1.E u.1.t)⁻¹ ^ (n - 1)) := by
  intro n hn κ c hκ hc h5 h6 τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  obtain rfl | rfl | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
  · -- `n = 1`: `𝒦 = m(σ₁)`
    filter_upwards [eventually_le_rpow 1 hτ] with N hN
    rintro ⟨p, σ, a⟩
    have hE2 : |p.E| ≤ 2 := by have := p.hE; linarith
    change ‖Kcal p.L p.W p.E p.t (loopOf p.L σ a)‖ ≤ (N : ℝ) ^ τ * (Mt p.L p.W p.E p.t)⁻¹ ^ (1 - 1)
    rw [kb_loopOf_one, kb_Kcal_one, kb_norm_mSig hE2, Nat.sub_self, pow_zero, mul_one]
    exact hN
  · -- `n = 2`: `(Kn2sol)`, `Prop5Hyp` and the bulk gap
    filter_upwards [kb_theta_two_le hκ hc h5 hτ2, eventually_le_rpow (gapK κ)⁻¹ hτ2]
      with N hN hC
    rintro ⟨p, σ, a⟩
    have hE2 : |p.E| ≤ 2 := by have := p.hE; linarith
    change ‖Kcal p.L p.W p.E p.t (loopOf p.L σ a)‖ ≤ (N : ℝ) ^ τ * (Mt p.L p.W p.E p.t)⁻¹ ^ (2 - 1)
    rw [kb_loopOf_two, Kcal_two, norm_mul, norm_mul, norm_mul, kb_norm_mSig hE2,
      kb_norm_mSig hE2, mul_one, mul_one, show (2 - 1 : ℕ) = 1 from rfl, pow_one,
      kb_Mt_inv]
    have hW : ‖((p.W : ℂ) ^ 2)⁻¹‖ = ((p.W : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]
    rw [hW]
    have hX0 : 0 ≤ Xt p.L p.E p.t := Xt_nonneg p.L p.ht1
    have hN0 : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hW0 : 0 ≤ ((p.W : ℝ) ^ 2)⁻¹ := by positivity
    have hΘ := hN p (σ 0) (σ 1) (a 0) (a 1)
    calc ((p.W : ℝ) ^ 2)⁻¹ * ‖Theta p.L ((p.t : ℂ) * (mSig p.E (σ 0) * mSig p.E (σ 1)))
            (a 0) (a 1)‖
        ≤ ((p.W : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ (τ / 2) * ((gapK κ)⁻¹ * Xt p.L p.E p.t)) :=
          mul_le_mul_of_nonneg_left hΘ hW0
      _ ≤ ((p.W : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t)) := by
          gcongr
      _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) * (((p.W : ℝ) ^ 2)⁻¹ * Xt p.L p.E p.t) := by
          ring
      _ = (N : ℝ) ^ τ * (((p.W : ℝ) ^ 2)⁻¹ * Xt p.L p.E p.t) := by
          rw [UnifDetDom.rpow_half_mul_rpow_half N hτ]
  · -- `n ≥ 3`: `(KKpi)`, `(eq:bcal_k_pi)` and `W^{-2(n-1)} X_t^{n-1} = M_t^{-(n-1)}`
    have : NeZero n := ⟨by omega⟩
    filter_upwards [Kpi_bound_prec n h3 κ c hκ hc h5 h6 (τ / 2) hτ2,
      eventually_le_rpow ((2 : ℝ) ^ (diagonals n).card) hτ2] with N hN hC
    rintro ⟨p, σ, a⟩
    have hE2 : |p.E| ≤ 2 := by have := p.hE; linarith
    change ‖Kcal p.L p.W p.E p.t (loopOf p.L σ a)‖ ≤ (N : ℝ) ^ τ * (Mt p.L p.W p.E p.t)⁻¹ ^ (n - 1)
    rw [Kcal_eq_sum_Kpi p.L p.W p.E p.t n h3 σ a, norm_mul, norm_mul, kb_norm_W, norm_prod,
      Finset.prod_eq_one (fun i _ => kb_norm_mSig hE2 (σ i)), mul_one, kb_Mt_inv, mul_pow]
    have hX0 : 0 ≤ Xt p.L p.E p.t := Xt_nonneg p.L p.ht1
    have hN0 : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hW0 : 0 ≤ ((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) := by positivity
    have hsum : ‖∑ π ∈ (diagonals n).powerset, Kpi p.L (mSig p.E) p.t σ a π‖
        ≤ (2 : ℝ) ^ (diagonals n).card * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - 1)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ π ∈ (diagonals n).powerset, ‖Kpi p.L (mSig p.E) p.t σ a π‖
          ≤ ∑ π ∈ (diagonals n).powerset, (N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - 1) :=
            Finset.sum_le_sum fun π _ => hN ⟨p, σ, π, a⟩
        _ = (2 : ℝ) ^ (diagonals n).card * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - 1)) := by
            rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
            push_cast
            ring
    calc ((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) *
          ‖∑ π ∈ (diagonals n).powerset, Kpi p.L (mSig p.E) p.t σ a π‖
        ≤ ((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) *
            ((2 : ℝ) ^ (diagonals n).card * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - 1))) :=
          mul_le_mul_of_nonneg_left hsum hW0
      _ ≤ ((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) *
            ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * Xt p.L p.E p.t ^ (n - 1))) := by
          gcongr
      _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) *
            (((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) * Xt p.L p.E p.t ^ (n - 1)) := by ring
      _ = (N : ℝ) ^ τ * (((p.W : ℝ) ^ 2)⁻¹ ^ (n - 1) * Xt p.L p.E p.t ^ (n - 1)) := by
          rw [UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-- **`ML:Kbound` = `(eq:bcal_k_2)`, unconditional** (`c = 1/20000`): for every `n ≥ 1` and
`κ > 0`, `𝒦_{t,σ,a} ≺ M_t^{-n+1}` uniformly over `Par κ N`, `σ`, `a`.  `Kbound_prec` with
`Prop5Hyp κ (1/20000)` and `Prop6Hyp κ` discharged by `prop5Hyp_holds`, `prop6Hyp_holds`. -/
theorem Kbound_prec_uncond :
  ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    UnifDetDom (U := fun N => (p : Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
      (fun _ u => ‖Kcal u.1.L u.1.W u.1.E u.1.t (loopOf u.1.L u.2.1 u.2.2)‖)
      (fun _ u => (Mt u.1.L u.1.W u.1.E u.1.t)⁻¹ ^ (n - 1)) := by
  intro n hn κ hκ
  exact Kbound_prec n hn κ (1 / 20000) hκ (by norm_num) (prop5Hyp_holds κ hκ)
    (prop6Hyp_holds κ hκ)

end Kbound

end RBM.KLoop
