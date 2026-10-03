/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Grid
import RBM2D.Universality.GUEPhase.Eq729B
import RBM2D.Path.GoodEvent
import RBM2D.Induction.Split
import RBM2D.Defs.Semicircle
import RBM2D.Path.Scales

/-!
# The §7.2 random layer, first part: Lemma 2.8, the size-level conditions, the one-time law
(`d = 2`)

Lemma 2.8 at `z = e + iη` gives `E' = lemE z`, `t₀ = lemT z`, `t₁ = (1 - ζ(t)) t₀`; the
size-level conditions of `RandomLayer_rows` give, in exactly the form of the hypotheses of
`gueGrid_eq729` (`Eq729B.lean`), `|E' n| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1`, `h730`, `hscale`, `hell`,
and the time-range condition of `P7Out`/`P7ExpOut` at `t₁`.  The carrier crossing is the one-time
law `map_gueH_last`.

## Public declarations

* `RandomLayer_lem28`, `RandomLayer_rows`, `RandomLayer_eventually_size`,
  `RandomLayer_eventually_rpow_ge`, `RandomLayer_rowsLL`, `RandomLayer_rowsQ`.
* `RandomLayer_etaLL_pos`, `RandomLayer_etaLL_le_one`, `RandomLayer_etaQ_pos`,
  `RandomLayer_etaQ_le_one`: `0 < η ≤ 1` at the two scales `ouEtaLL`, `ouEtaQ` (the hypotheses
  `hη0`, `hη1` of `RandomLayer_rows` at those scales).

Conventions (`d = 2`): the scale of the local law is `ouEtaLL d τU n = N^{-1+2τU}` and the scale of
(7.47) is `ouEtaQ d n = W^{2/3}/N`; there is one size `d.size n = (W L)²`; the hypotheses are
`τU ≤ ouTauMax 𝔠` and `Admissible 𝔠 d`; the range exponent of the Q scale is `τ = 𝔠/3`.

Helpers are `private` and carry the prefix `RandomLayer_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### Measurability of the resolvent in the matrix -/

/-! ### The one-time law, integrated (the only carrier crossing of this layer) -/

/-! ### Lemma 2.8 at `z = e + iη` -/

private theorem RandomLayer_lemT_pos {z : ℂ} (hz : 0 < z.im) : 0 < lemT z := by
  have h1 : msc z ≠ 0 := fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this
  unfold lemT
  exact pow_pos (norm_pos_iff.2 h1) 2

/-- `eq:zztE` read on imaginary parts: `Im z_t = t^{1/2} Im z` (as `semicircle_spectralZ_im_lemT`
of `Defs/Semicircle.lean`). -/
private theorem RandomLayer_spectralZ_im_lemT {z : ℂ} (hz : 0 < z.im) :
    (spectralZ (lemE z) (lemT z)).im = Real.sqrt (lemT z) * z.im := by
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RandomLayer_lemT_pos hz)).ne'
  have h := eq_inv_sqrt_mul_spectralZ hz
  have e : spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z :=
    calc spectralZ (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) *
            ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = _ := by rw [← h]
  rw [e]
  simp [Complex.mul_im]

/-- **Lemma 2.8 at `z = e + iη`**, `|e| ≤ 2 - k`, `0 < η ≤ 1` (with the bounds on
`η_{t₀} = etaT E' t₀ = √t₀ η` and `1 - t₀`).  The
last two items are `η/4 ≤ 1 - t₀ ≤ η/c_k`, `c_k = √(2k)/2`. -/
theorem RandomLayer_lem28 {k e η : ℝ} (hk : 0 < k) (he : |e| ≤ 2 - k) (hη0 : 0 < η)
    (hη1 : η ≤ 1) {z : ℂ} (hz : z = (e : ℂ) + (η : ℂ) * Complex.I) :
    0 < z.im ∧ |lemE z| ≤ 2 - k ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧
      η / 4 ≤ etaT (lemE z) (lemT z) ∧ etaT (lemE z) (lemT z) ≤ η ∧
      η / 4 ≤ 1 - lemT z ∧ 1 - lemT z ≤ η / (Real.sqrt (2 * k) / 2) := by
  have hre : z.re = e := by simp [hz]
  have him : z.im = η := by simp [hz]
  have hzim : 0 < z.im := him ▸ hη0
  obtain ⟨hE', ht16, -, -⟩ := zztE_quant hk hzim (him ▸ hη1) (hre ▸ he)
  have ht1 : lemT z < 1 := by
    have h := norm_msc_lt_one hzim
    have h0 := norm_nonneg (msc z)
    unfold lemT
    nlinarith
  have heta' : etaT (lemE z) (lemT z) = (1 - lemT z) * (spectralM (lemE z)).im := rfl
  have heta : etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η := by
    rw [← him, ← RandomLayer_spectralZ_im_lemT hzim]
    exact (spectralZ_im _ _).symm
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht16
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  have hk2 : k ≤ 2 := by linarith [abs_nonneg e]
  have hE'abs := abs_le.1 hE'
  have hm : Real.sqrt (2 * k) / 2 ≤ (spectralM (lemE z)).im := by
    rw [spectralM_im]
    have h2 : 2 * k ≤ 4 - (lemE z) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hE'abs.2) (by linarith [hE'abs.1] : (0 : ℝ) ≤ 2 - k + lemE z),
        mul_nonneg hk.le (sub_nonneg.2 hk2)]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h2) (by norm_num)
  have hm1 : (spectralM (lemE z)).im ≤ 1 := by
    rw [spectralM_im]
    have : Real.sqrt (4 - (lemE z) ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg (lemE z)]⟩
    linarith
  have hc : 0 < Real.sqrt (2 * k) / 2 := by positivity
  have hA : η / 4 ≤ etaT (lemE z) (lemT z) := by rw [heta]; nlinarith
  have hB : etaT (lemE z) (lemT z) ≤ η := by rw [heta]; nlinarith
  refine ⟨hzim, hE', ht16, ht1, hA, hB, ?_, ?_⟩
  · have h1t : 0 < 1 - lemT z := by linarith
    rw [heta'] at hA
    nlinarith
  · rw [le_div_iff₀ hc]
    rw [heta'] at hB
    have h1t : 0 < 1 - lemT z := by linarith
    nlinarith

/-! ### The size-level conditions at an arbitrary scale -/

/-- **Size-level conditions at an arbitrary scale** for the sequence `z_n = e_n + iη_n`,
`t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`, from the conditions `r1`, `r2`, `r3`, `r5`.  The
conclusions are, in this order, exactly the hypotheses `|E n| ≤ 2 - κ`, `0 ≤ t1 n`,
`t1 n ≤ t0 n`, `t0 n < 1`, `h730`, `hscale`, `hell` of `gueGrid_eq729` (`Eq729B.lean`) at
`E n = lemE (z n)`, `t0 n = lemT (z n)`, `t1 n = (1 - ouZeta (t n)) * lemT (z n)` and the exponent
`τD`, and the range condition `N^{-1+τ} ≤ 1 - t1 n` of `P7Out`/`P7ExpOut` at `t₁`. -/
theorem RandomLayer_rows {k τD τ : ℝ} (hk : 0 < k) (_hτD : 0 < τD)
    {e η t : ℕ → ℝ} (z : ℕ → ℂ) (hz : ∀ n, z n = (e n : ℂ) + (η n : ℂ) * Complex.I)
    (he : ∀ n, |e n| ≤ 2 - k) (hη0 : ∀ n, 0 < η n) (hη1 : ∀ n, η n ≤ 1) (ht : ∀ n, 0 ≤ t n)
    (r1 : ∀ᶠ n in atTop, t n ≤ ((d.size n : ℕ) : ℝ) ^ (-τD) * (η n / 4))
    (r2 : ∀ᶠ n in atTop, 4 * (((d.size n : ℕ) : ℝ) * η n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τD))
    (r3 : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (η n / (Real.sqrt (2 * k) / 2) + t n) ≤ 1)
    (r5 : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ η n / 4) :
    (∀ n, |lemE (z n)| ≤ 2 - k) ∧ (∀ n, 0 ≤ (1 - ouZeta (t n)) * lemT (z n)) ∧
      (∀ n, (1 - ouZeta (t n)) * lemT (z n) ≤ lemT (z n)) ∧ (∀ n, lemT (z n) < 1) ∧
      (∀ᶠ n in atTop, lemT (z n) - (1 - ouZeta (t n)) * lemT (z n) ≤
        ((d.size n : ℕ) : ℝ) ^ (-τD) * etaT (lemE (z n)) (lemT (z n))) ∧
      (∀ᶠ n in atTop, (gueScale d (fun n => lemE (z n)) n (lemT (z n)))⁻¹ ≤
        ((d.size n : ℕ) : ℝ) ^ (-τD)) ∧
      (∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - (1 - ouZeta (t n)) * lemT (z n)) ≤ 1) ∧
      (∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤
        1 - (1 - ouZeta (t n)) * lemT (z n)) := by
  have L28 := fun n => RandomLayer_lem28 hk (he n) (hη0 n) (hη1 n) (hz n)
  have hSpos : ∀ n, (0 : ℝ) < ((d.size n : ℕ) : ℝ) := fun n => by
    have h1 : 0 < d.W n := d.W_pos n
    have h2 : 0 < d.L n := by have := d.three_le_L n; omega
    have : 0 < d.size n := pow_pos (Nat.mul_pos h1 h2) 2
    exact_mod_cast this
  have hζ0 : ∀ n, 0 ≤ ouZeta (t n) := fun n => ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 : ∀ n, ouZeta (t n) ≤ 1 := fun n => ZeroModeProfile_ouZeta_le_one (t n)
  have hζt : ∀ n, ouZeta (t n) ≤ t n := fun n => ZeroModeProfile_ouZeta_le (t n)
  have ht0pos : ∀ n, 0 ≤ lemT (z n) := fun n => by linarith [(L28 n).2.2.1]
  have hdiff : ∀ n, lemT (z n) - (1 - ouZeta (t n)) * lemT (z n) ≤ t n := fun n => by
    have h1 := (L28 n).2.2.2.1
    nlinarith [hζ0 n, hζt n, ht0pos n]
  refine ⟨fun n => (L28 n).2.1, fun n => mul_nonneg (by linarith [hζ1 n]) (ht0pos n),
    fun n => by nlinarith [hζ0 n, ht0pos n], fun n => (L28 n).2.2.2.1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [r1] with n hN
    calc _ ≤ t n := hdiff n
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τD) * (η n / 4) := hN
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τD) * etaT (lemE (z n)) (lemT (z n)) :=
          mul_le_mul_of_nonneg_left (L28 n).2.2.2.2.1 (by positivity)
  · filter_upwards [r2] with n hN
    refine le_trans ?_ hN
    unfold gueScale
    have hη4 := (L28 n).2.2.2.2.1
    have hSη : 0 < ((d.size n : ℕ) : ℝ) * (η n / 4) := mul_pos (hSpos n) (by linarith [hη0 n])
    calc (((d.size n : ℕ) : ℝ) * etaT (lemE (z n)) (lemT (z n)))⁻¹
        ≤ (((d.size n : ℕ) : ℝ) * (η n / 4))⁻¹ :=
          inv_anti₀ hSη (mul_le_mul_of_nonneg_left hη4 (hSpos n).le)
      _ = 4 * (((d.size n : ℕ) : ℝ) * η n)⁻¹ := by
          have := hη0 n; have := hSpos n; field_simp
  · filter_upwards [r3] with n hN
    refine le_trans ?_ hN
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := (L28 n).2.2.2.2.2.2.2
    have h2 : ouZeta (t n) * lemT (z n) ≤ ouZeta (t n) * 1 :=
      mul_le_mul_of_nonneg_left (L28 n).2.2.2.1.le (hζ0 n)
    nlinarith [hζt n]
  · filter_upwards [r5] with n hN
    have h2 := (L28 n).2.2.2.2.2.2.1
    have h3 : (1 - ouZeta (t n)) * lemT (z n) ≤ lemT (z n) := by nlinarith [hζ0 n, ht0pos n]
    linarith


/-! ### Size-level facts -/

/-- Lift a property holding for all large reals to the matrix size `N = d.size n = (W L)²`. -/
theorem RandomLayer_eventually_size (hsize : Tendsto (fun n => d.size n) atTop atTop)
    {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P x) :
    ∀ᶠ n : ℕ in atTop, P ((d.size n : ℕ) : ℝ) :=
  (tendsto_natCast_atTop_atTop.comp hsize).eventually h

/-- Eventually `C ≤ x ^ a` as `x → ∞`, for `a > 0`. -/
theorem RandomLayer_eventually_rpow_ge (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop C

private theorem RandomLayer_rpow_mul_eq {x a b c e : ℝ} (hx : 0 < x) (h : a + b = c + e) :
    x ^ a * x ^ b = x ^ c * x ^ e := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, h]

private theorem RandomLayer_size_pos (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.W n := d.W_pos n
  have h2 : 0 < d.L n := by have := d.three_le_L n; omega
  have : 0 < d.size n := pow_pos (Nat.mul_pos h1 h2) 2
  exact_mod_cast this

private theorem RandomLayer_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : 1 ≤ d.W n := d.W_pos n
  have h2 : 3 ≤ d.L n := d.three_le_L n
  have h3 : 1 ≤ d.W n * d.L n := by nlinarith
  have : 1 ≤ d.size n := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast this

private theorem RandomLayer_size_eq (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2 := by
  rw [Sizes.size_eq]; push_cast; ring

/-- `L² ≤ N^{1-2𝔠}` from `W ≥ N^𝔠` and `N = W² L²`. -/
private theorem RandomLayer_L_sq_le {𝔠 : ℝ} (n : ℕ)
    (hW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)) :
    (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (1 - 2 * 𝔠) := by
  have hSLW := RandomLayer_size_eq d n
  have hS0 := RandomLayer_size_pos d n
  set S : ℝ := ((d.size n : ℕ) : ℝ) with hS
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have e : S ^ (1 - 2 * 𝔠) * S ^ (2 * 𝔠) = S := by
    rw [← Real.rpow_add hS0]; norm_num
  have h2 : S ^ (2 * 𝔠) ≤ (d.W n : ℝ) ^ 2 := by
    have : S ^ (2 * 𝔠) = (S ^ 𝔠) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hS0.le _) hW 2
  have h1 : (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2 ≤ S ^ (1 - 2 * 𝔠) * (d.W n : ℝ) ^ 2 := by
    calc (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2 = S := hSLW.symm
      _ = S ^ (1 - 2 * 𝔠) * S ^ (2 * 𝔠) := e.symm
      _ ≤ S ^ (1 - 2 * 𝔠) * (d.W n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  exact le_of_mul_le_mul_right h1 (by positivity)

/-! ### The two scales: `η_LL = N^{-1+2τU}` and `η_Q = W^{2/3}/N` -/

/-- `0 < η_LL` (the hypothesis `hη0` of `RandomLayer_rows` at the local-law scale). -/
theorem RandomLayer_etaLL_pos (τU : ℝ) (n : ℕ) : 0 < ouEtaLL d τU n :=
  Real.rpow_pos_of_pos (RandomLayer_size_pos d n) _

/-- `η_LL ≤ 1` for `τU ≤ 1/2` (the hypothesis `hη1` of `RandomLayer_rows` at the local-law scale). -/
theorem RandomLayer_etaLL_le_one {τU : ℝ} (hτU : τU ≤ 1 / 2) (n : ℕ) : ouEtaLL d τU n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (RandomLayer_one_le_size d n) (by linarith)

/-- `0 < η_Q` (the hypothesis `hη0` of `RandomLayer_rows` at the QUE scale). -/
theorem RandomLayer_etaQ_pos (n : ℕ) : 0 < ouEtaQ d n := by
  have hS := RandomLayer_size_pos d n
  have hW : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  unfold ouEtaQ
  positivity

/-- `η_Q ≤ 1` (the hypothesis `hη1` of `RandomLayer_rows` at the QUE scale): `W^{2/3} ≤ W ≤ W² ≤ N`. -/
theorem RandomLayer_etaQ_le_one (n : ℕ) : ouEtaQ d n ≤ 1 := by
  have hS := RandomLayer_size_pos d n
  have hSe := RandomLayer_size_eq d n
  have hW1 : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
  have hL3 : (3 : ℝ) ≤ d.L n := by exact_mod_cast d.three_le_L n
  unfold ouEtaQ
  rw [div_le_one hS]
  calc (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ (d.W n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    _ = d.W n := Real.rpow_one _
    _ ≤ (d.W n : ℝ) ^ 2 := by nlinarith
    _ ≤ (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2 := by
        have hL2 : (1 : ℝ) ≤ (d.L n : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hL2 (sq_nonneg (d.W n : ℝ))]
    _ = _ := hSe.symm

/-- `N η_Q = W^{2/3}`. -/
private theorem RandomLayer_size_mul_etaQ (n : ℕ) :
    ((d.size n : ℕ) : ℝ) * ouEtaQ d n = (d.W n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hS := RandomLayer_size_pos d n
  unfold ouEtaQ
  field_simp

/-- `W ≥ N^𝔠` gives `N^{2𝔠/3} ≤ W^{2/3}`. -/
private theorem RandomLayer_rpow_le_W {𝔠 : ℝ} (n : ℕ)
    (hW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)) :
    ((d.size n : ℕ) : ℝ) ^ (2 * 𝔠 / 3) ≤ (d.W n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hS := RandomLayer_size_pos d n
  have e : ((d.size n : ℕ) : ℝ) ^ (2 * 𝔠 / 3) = (((d.size n : ℕ) : ℝ) ^ 𝔠) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_mul hS.le]; ring_nf
  rw [e]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hS.le _) hW (by norm_num)

/-- `η_Q ≥ N^{-1+2𝔠/3}` from `W ≥ N^𝔠`. -/
private theorem RandomLayer_etaQ_ge {𝔠 : ℝ} (n : ℕ)
    (hW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)) :
    ((d.size n : ℕ) : ℝ) ^ (-1 + 2 * 𝔠 / 3) ≤ ouEtaQ d n := by
  have hS := RandomLayer_size_pos d n
  have hu := RandomLayer_rpow_le_W d n hW
  have e2 : ((d.size n : ℕ) : ℝ) ^ (-1 + 2 * 𝔠 / 3) =
      ((d.size n : ℕ) : ℝ) ^ (2 * 𝔠 / 3) / ((d.size n : ℕ) : ℝ) := by
    rw [show (-1 + 2 * 𝔠 / 3 : ℝ) = 2 * 𝔠 / 3 - 1 by ring, Real.rpow_sub_one hS.ne']
  rw [e2]
  unfold ouEtaQ
  exact div_le_div_of_nonneg_right hu hS.le

/-- `L² η_Q W^{4/3} = 1`, i.e. `L² η_Q = W^{-4/3}`: `L² η_Q v² = 1`, `v = W^{2/3}`, `v³ = W²`,
`N = W² L²`. -/
private theorem RandomLayer_L_sq_etaQ_mul (n : ℕ) :
    (d.L n : ℝ) ^ 2 * ouEtaQ d n * ((d.W n : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 = 1 := by
  have hS := RandomLayer_size_pos d n
  have hSe := RandomLayer_size_eq d n
  have hW : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have hL : (0 : ℝ) < d.L n := by have := d.three_le_L n; positivity
  have hv3 : ((d.W n : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = (d.W n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; norm_num
  have hη : ouEtaQ d n = (d.W n : ℝ) ^ ((2 : ℝ) / 3) / ((d.size n : ℕ) : ℝ) := rfl
  rw [hη, hSe]
  set v : ℝ := (d.W n : ℝ) ^ ((2 : ℝ) / 3)
  field_simp
  nlinarith [hv3]

/-! ### The size-level conditions at the two scales -/

/-- **Size-level conditions at `η = η_LL = N^{-1+2τU}`** (the scale of the local law (2.26)),
`τD = τU/2`, `τ = τU`, for any `0 ≤ t_n ≤ t*_n = N^{-1+τU}`: the hypotheses `r1`, `r2`, `r3`, `r5`
of `RandomLayer_rows` with `k = κ`.  Here `τU ≤ ouTauMax 𝔠` and `Admissible 𝔠 d` (the binding
inequality is `τU < 𝔠`, `ouTauMax_slack`); there is one size, so no factor `2^{τD}` appears. -/
theorem RandomLayer_rowsLL {𝔠 κ τU : ℝ} (h𝔠 : 0 < 𝔠) (hd : RBM.Endpoints.Admissible 𝔠 d)
    (hκ : 0 < κ) (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (ht : ∀ n, t n ≤ ouTStar d τU n) :
    (∀ᶠ n in atTop, t n ≤ ((d.size n : ℕ) : ℝ) ^ (-(τU / 2)) * (ouEtaLL d τU n / 4)) ∧
      (∀ᶠ n in atTop, 4 * (((d.size n : ℕ) : ℝ) * ouEtaLL d τU n)⁻¹ ≤
        ((d.size n : ℕ) : ℝ) ^ (-(τU / 2))) ∧
      (∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 *
        (ouEtaLL d τU n / (Real.sqrt (2 * κ) / 2) + t n) ≤ 1) ∧
      (∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τU) ≤ ouEtaLL d τU n / 4) := by
  obtain ⟨-, hτc, -⟩ := ouTauMax_slack h𝔠 hτUc
  have hck : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  set C : ℝ := 1 / (Real.sqrt (2 * κ) / 2) + 1 with hC
  have hE1 := RandomLayer_eventually_size d hd.1 (eventually_ge_atTop (1 : ℝ))
  have hE2 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 4 (by positivity : 0 < τU / 2))
  have hE3 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 4 (by positivity : 0 < 3 * τU / 2))
  have hE4 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge C (by linarith : 0 < 2 * 𝔠 - 2 * τU))
  have hE5 := RandomLayer_eventually_size d hd.1 (RandomLayer_eventually_rpow_ge 4 hτU)
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hE1, hE2] with n hS1 h1
    unfold ouEtaLL
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have e := RandomLayer_rpow_mul_eq (a := -(τU / 2)) (b := -1 + 2 * τU) (c := -1 + τU)
      (e := τU / 2) hS0 (by ring)
    have hp : 0 < S ^ (-1 + τU) := Real.rpow_pos_of_pos hS0 _
    calc t n ≤ S ^ (-1 + τU) := ht n
      _ ≤ S ^ (-1 + τU) * S ^ (τU / 2) / 4 := by nlinarith
      _ = S ^ (-(τU / 2)) * (S ^ (-1 + 2 * τU) / 4) := by rw [← e]; ring
  · filter_upwards [hE1, hE3] with n hS1 h1
    unfold ouEtaLL
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have e1 : S * S ^ (-1 + 2 * τU) = S ^ (2 * τU) := by
      rw [mul_comm, ← Real.rpow_add_one hS0.ne']; ring_nf
    have e2 : S ^ (-(τU / 2)) = (S ^ (2 * τU))⁻¹ * S ^ (3 * τU / 2) := by
      rw [← Real.rpow_neg hS0.le, ← Real.rpow_add hS0]; ring_nf
    rw [e1, e2]
    have hp : 0 < (S ^ (2 * τU))⁻¹ := by positivity
    nlinarith
  · filter_upwards [hE1, hE4, hd.2] with n hS1 h1 hWn
    unfold ouEtaLL
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hL := RandomLayer_L_sq_le d n hWn
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have htt : t n ≤ S ^ (-1 + 2 * τU) :=
      (ht n).trans (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith))
    have hX : S ^ (-1 + 2 * τU) / (Real.sqrt (2 * κ) / 2) + t n ≤ C * S ^ (-1 + 2 * τU) := by
      rw [hC, add_mul, one_mul, div_eq_mul_one_div, mul_comm]; linarith
    have e : S ^ (1 - 2 * 𝔠) * S ^ (-1 + 2 * τU) = (S ^ (2 * 𝔠 - 2 * τU))⁻¹ := by
      rw [← Real.rpow_add hS0, ← Real.rpow_neg hS0.le]; ring_nf
    have hX0 : 0 ≤ S ^ (-1 + 2 * τU) / (Real.sqrt (2 * κ) / 2) + t n := by
      have := ht0 n; positivity
    calc (d.L n : ℝ) ^ 2 * (S ^ (-1 + 2 * τU) / (Real.sqrt (2 * κ) / 2) + t n)
        ≤ S ^ (1 - 2 * 𝔠) * (C * S ^ (-1 + 2 * τU)) :=
          mul_le_mul hL hX hX0 (by positivity)
      _ = C * (S ^ (2 * 𝔠 - 2 * τU))⁻¹ := by rw [← e]; ring
      _ ≤ 1 := by
          have hp : 0 < S ^ (2 * 𝔠 - 2 * τU) := by positivity
          rw [← div_eq_mul_inv, div_le_one hp]; exact h1
  · filter_upwards [hE1, hE5] with n hS1 h1
    unfold ouEtaLL
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have e : S ^ (-1 + 2 * τU) = S ^ (-1 + τU) * S ^ τU := by
      rw [← Real.rpow_add hS0]; ring_nf
    have hp : 0 < S ^ (-1 + τU) := by positivity
    rw [e]; nlinarith

/-- **Size-level conditions at `η = η_Q = W^{2/3}/N`** (the scale of (7.47)), `τD = τU/2`,
`τ = 𝔠/3`, for any `0 ≤ t_n ≤ t*_n = N^{-1+τU}`: the hypotheses `r1`, `r2`, `r3`, `r5` of
`RandomLayer_rows` with `k = κ`.  The exponents of `W ≥ N^𝔠` and `L² η_Q = W^{-4/3}` give
`r1`: `3τU/2 < 2𝔠/3`; `r3a`: `L² η_Q ≤ N^{-4𝔠/3}`; the range exponent is `τ = 𝔠/3 < 2𝔠/3`. -/
theorem RandomLayer_rowsQ {𝔠 κ τU : ℝ} (h𝔠 : 0 < 𝔠) (hd : RBM.Endpoints.Admissible 𝔠 d)
    (hκ : 0 < κ) (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (ht : ∀ n, t n ≤ ouTStar d τU n) :
    (∀ᶠ n in atTop, t n ≤ ((d.size n : ℕ) : ℝ) ^ (-(τU / 2)) * (ouEtaQ d n / 4)) ∧
      (∀ᶠ n in atTop, 4 * (((d.size n : ℕ) : ℝ) * ouEtaQ d n)⁻¹ ≤
        ((d.size n : ℕ) : ℝ) ^ (-(τU / 2))) ∧
      (∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 *
        (ouEtaQ d n / (Real.sqrt (2 * κ) / 2) + t n) ≤ 1) ∧
      (∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + 𝔠 / 3) ≤ ouEtaQ d n / 4) := by
  obtain ⟨-, hτc, hτ3⟩ := ouTauMax_slack h𝔠 hτUc
  set ck : ℝ := Real.sqrt (2 * κ) / 2 with hck
  have hck0 : 0 < ck := by positivity
  have hE1 := RandomLayer_eventually_size d hd.1 (eventually_ge_atTop (1 : ℝ))
  have hE2 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 4 (by linarith : 0 < 2 * 𝔠 / 3 - 3 * τU / 2))
  have hE3 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 4 (by linarith : 0 < 2 * 𝔠 / 3 - τU / 2))
  have hE4 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 2 (by linarith : 0 < 2 * 𝔠 - τU))
  have hE5 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge (2 / ck) (by linarith : 0 < 4 * 𝔠 / 3))
  have hE6 := RandomLayer_eventually_size d hd.1
    (RandomLayer_eventually_rpow_ge 4 (by linarith : 0 < 𝔠 / 3))
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hE1, hE2, hd.2] with n hS1 h1 hWn
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hη := RandomLayer_etaQ_ge d n hWn
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have e := RandomLayer_rpow_mul_eq (a := -(τU / 2)) (b := -1 + 2 * 𝔠 / 3) (c := -1 + τU)
      (e := 2 * 𝔠 / 3 - 3 * τU / 2) hS0 (by ring)
    have hp : 0 < S ^ (-1 + τU) := Real.rpow_pos_of_pos hS0 _
    calc t n ≤ S ^ (-1 + τU) := ht n
      _ ≤ S ^ (-1 + τU) * S ^ (2 * 𝔠 / 3 - 3 * τU / 2) / 4 := by nlinarith
      _ = S ^ (-(τU / 2)) * (S ^ (-1 + 2 * 𝔠 / 3) / 4) := by rw [← e]; ring
      _ ≤ S ^ (-(τU / 2)) * (ouEtaQ d n / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · filter_upwards [hE1, hE3, hd.2] with n hS1 h1 hWn
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hu := RandomLayer_rpow_le_W d n hWn
    have hNη := RandomLayer_size_mul_etaQ d n
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have hpu : 0 < S ^ (2 * 𝔠 / 3) := Real.rpow_pos_of_pos hS0 _
    have hinv : (S * ouEtaQ d n)⁻¹ ≤ S ^ (-(2 * 𝔠 / 3)) := by
      rw [hNη, Real.rpow_neg hS0.le]
      exact inv_anti₀ hpu hu
    have e2 : S ^ (-(τU / 2)) = S ^ (-(2 * 𝔠 / 3)) * S ^ (2 * 𝔠 / 3 - τU / 2) := by
      rw [← Real.rpow_add hS0]; ring_nf
    rw [e2]
    have hp : 0 < S ^ (-(2 * 𝔠 / 3)) := Real.rpow_pos_of_pos hS0 _
    have hq : 0 ≤ (S * ouEtaQ d n)⁻¹ := by
      have := RandomLayer_etaQ_pos d n
      positivity
    calc 4 * (S * ouEtaQ d n)⁻¹ ≤ S ^ (2 * 𝔠 / 3 - τU / 2) * S ^ (-(2 * 𝔠 / 3)) :=
          mul_le_mul h1 hinv hq (by positivity)
      _ = _ := by ring
  · filter_upwards [hE1, hE4, hE5, hd.2] with n hS1 h4 h5 hWn
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hL := RandomLayer_L_sq_le d n hWn
    have hu := RandomLayer_rpow_le_W d n hWn
    have hmul := RandomLayer_L_sq_etaQ_mul d n
    have hη0 := RandomLayer_etaQ_pos d n
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    set η : ℝ := ouEtaQ d n with hηdef
    have hu0 : 0 ≤ S ^ (2 * 𝔠 / 3) := Real.rpow_nonneg hS0.le _
    have hu2 : (S ^ (2 * 𝔠 / 3)) ^ 2 = S ^ (4 * 𝔠 / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num; ring_nf
    have hA0 : 0 ≤ (d.L n : ℝ) ^ 2 * η := by positivity
    -- `L² η ≤ ck / 2`
    have hAu : (d.L n : ℝ) ^ 2 * η * (S ^ (2 * 𝔠 / 3)) ^ 2 ≤ 1 := by
      calc (d.L n : ℝ) ^ 2 * η * (S ^ (2 * 𝔠 / 3)) ^ 2
          ≤ (d.L n : ℝ) ^ 2 * η * ((d.W n : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu 2) hA0
        _ = 1 := hmul
    have hA : (d.L n : ℝ) ^ 2 * η ≤ ck / 2 := by
      rw [hu2] at hAu
      have h5' : 2 ≤ S ^ (4 * 𝔠 / 3) * ck := (div_le_iff₀ hck0).1 h5
      nlinarith [mul_le_mul_of_nonneg_left h5' hA0]
    -- `L² t ≤ 1/2`
    have hB : (d.L n : ℝ) ^ 2 * t n ≤ 1 / 2 := by
      have e : S ^ (1 - 2 * 𝔠) * S ^ (-1 + τU) = (S ^ (2 * 𝔠 - τU))⁻¹ := by
        rw [← Real.rpow_add hS0, ← Real.rpow_neg hS0.le]; ring_nf
      calc (d.L n : ℝ) ^ 2 * t n ≤ S ^ (1 - 2 * 𝔠) * S ^ (-1 + τU) :=
            mul_le_mul hL (ht n) (ht0 n) (by positivity)
        _ = (S ^ (2 * 𝔠 - τU))⁻¹ := e
        _ ≤ 1 / 2 := by
            rw [one_div]; exact inv_anti₀ (by norm_num) h4
    have e : (d.L n : ℝ) ^ 2 * (η / ck + t n) =
        (d.L n : ℝ) ^ 2 * η / ck + (d.L n : ℝ) ^ 2 * t n := by
      ring
    rw [e]
    have : (d.L n : ℝ) ^ 2 * η / ck ≤ 1 / 2 := by
      rw [div_le_iff₀ hck0]; linarith
    linarith
  · filter_upwards [hE1, hE6, hd.2] with n hS1 h1 hWn
    have hS0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hη := RandomLayer_etaQ_ge d n hWn
    set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
    have e : S ^ (-1 + 2 * 𝔠 / 3) = S ^ (-1 + 𝔠 / 3) * S ^ (𝔠 / 3) := by
      rw [← Real.rpow_add hS0]; ring_nf
    have hp : 0 < S ^ (-1 + 𝔠 / 3) := by positivity
    rw [e] at hη
    nlinarith

/-! ### Integrability of the loops of `H_{t_n}` -/

end RBM.Univ.GUEPhase

end
