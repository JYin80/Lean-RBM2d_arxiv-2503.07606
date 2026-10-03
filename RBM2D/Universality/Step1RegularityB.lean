/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Step1RegularityA
import RBM2D.Universality.FreeConvStability
import RBM2D.Universality.InjSum

/-!
# The good event of Step 1

Deterministic half of the regularity event of Step 1 of `Thm: B_Univ`: on the event
`Step1LocalEvent d n (κ/2) (τs/8) (τs/8)` of `Step1RegularityA.lean`, the diagonal
`v_i = e^{-t*/2} λ_i(H) - E₀` (`vOU`, `t* = N^{-1+τs}`) is `[32]`-regular (`IsRegular32`, [32]
Definition 2.1) and the free-convolution density at `t = 1 - e^{-t*}` exists and is within
`N^{-3τs/8}` of `ρ_sc(E₀)`.  Hence it fails with probability `≤ N^{-D}` eventually
(`step1Good_highProb`), from `locSC` (kept as a hypothesis).

Proof.
* Dictionary `m_V(w) = a⁻¹ m_N(a⁻¹ (w + E₀))`, `a = e^{-t*/2} = √(1 - t)`, through the spectral
  formula for `stieltjesN` (`Step1RegularityB_mV_vOU`).
* Regularity (2.2): for `|E| ≤ G`, `g ≤ η ≤ 1/2` the event bound `2 W^{τ'} / Meta(z)`, with
  `Meta(z) ≥ min (W², N Im z)` (`Step1RegularityB_Meta_ge`), `W² ≤ N` and `N^{τs/4} ≤ W²`, is
  `≤ κ'/24`, and `Im m_sc ≥ κ'/12` in the bulk (`Step1RegularityB_msc_im_ge`) gives
  `Im m_V ∈ [κ'/24, 2]`; for `1/2 < η ≤ 10` the monotonicity of `η ↦ η Im m_N(E + iη)`
  (`stieltjesN_eta_mul_im_mono`) gives `≥ κ'/480` and `‖m_V‖ ≤ 1/η` gives `≤ 2`.
* Regularity (2.3): `|λ_i| ≤ N` from the entry bound (`Step1RegularityB_eigenvalue_le`), so
  `|v_i| ≤ N + 2 ≤ N²`.
* Free convolution: `FreeConvStability.freeConv_stable_local` with `t = 1 - e^{-t*}` and
  `ε = N^{-3τs/8} / C₀`; its hypothesis `hyp` on the strip `c₀ t/4 ≤ Im w ≤ 1/2` is discharged
  from the event (`Step1RegularityB_strip`): the strip stays above `N^{-1+τs/8}` because
  `τs/8 < τs`, and the error is `≤ 4 c₁⁻¹ N^{-15τs/16}`.
* All size conditions have the form `N^{-e} ≤ c`, `e > 0`, hence hold for large `n`.

Lemmas: `vOU`; `Step1RegularityB_stieltjesN_eq_mV`; `Step1RegularityB_msc_im_ge`;
`Step1RegularityB_mV_norm_le`; `Step1RegularityB_inv_le`; `Step1RegularityB_mV_vOU`;
`Step1RegularityB_domain`; `Step1RegularityB_bulk`, `Step1RegularityB_regular`;
`Step1RegularityB_strip`, `Step1RegularityB_det`; `step1Good_highProb`.  The parameters of the
statement (rate, exponents, bulk constant) are written out.  No grid or interpolation is needed
here (`Step1RegularityA.lean` covers all `z` of the domain at once); the eigenvalue bound is
`Step1RegularityB_eigenvalue_le` and the monotonicity of `η Im m` is `stieltjesN_eta_mul_im_mono`
of `InjSum.lean`.

Conventions (`d = 2`).
* `CV = 2`: the event only bounds the entries, `|h_xy| ≤ 1`, which gives
  `|λ_i| ≤ N` through an eigenvector, hence `|v_i| ≤ N + 2 ≤ N²`; no operator-norm bound.
* The hypothesis `τs ≤ 𝔠` is used for `N^{τs} ≤ N^𝔠 ≤ W ≤ W²`: the band local-law error
  `W^{τ'} / Meta` then decays like `N^{-(τs - τ'/2)}` on the strip.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ### 0. The shifted, rescaled diagonal -/

/-- The shifted, rescaled diagonal of Step 1: `v_i = e^{-t*/2} λ_i(H) - E₀`, `t* = N^{-1+τs}`. -/
def vOU (d : Sizes) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ d) : Idx (d.L n) (d.W n) → ℝ :=
  fun i => Real.exp (-(RBM.Univ.ouTStar d τs n) / 2) *
    (Sizes.seqXmat_isHermitian d n ω).eigenvalues i - E₀

/-! ### 1. Elementary facts about `a = e^{-T/2}` and `t = 1 - e^{-T}` -/

private theorem Step1RegularityB_exp_le_one {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem Step1RegularityB_one_le_inv {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact Step1RegularityB_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityB_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem Step1RegularityB_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem Step1RegularityB_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

private theorem Step1RegularityB_one_sub_exp_pos {T : ℝ} (hT : 0 < T) :
    0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem Step1RegularityB_sqrt_exp (T : ℝ) :
    Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem Step1RegularityB_inv_mul_re (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem Step1RegularityB_inv_mul_im (a : ℝ) (X : ℂ) :
    (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

/-! ### 2. The eigenvalue dictionary and elementary bounds on `mV` -/

/-- `stieltjesN` is the finite-sum Stieltjes transform `mV` of the eigenvalues. -/
private theorem Step1RegularityB_stieltjesN_eq_mV {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjesN H z = mV hH.eigenvalues z := by
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold stieltjesN mV
  congr 1
  rw [green_eq_spectral hH hzne]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

/-- The affine dictionary:
`m_V(w) = a⁻¹ m_N(a⁻¹ (w + E₀))` for `v_i = a λ_i - E₀`, `a > 0`. -/
private theorem Step1RegularityB_mV_vOU {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {a : ℝ} (ha : 0 < a) (E₀ : ℝ) {w : ℂ}
    (hw : 0 < w.im) :
    mV (fun i => a * hH.eigenvalues i - E₀) w =
      ((a : ℝ) : ℂ)⁻¹ * stieltjesN H (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) := by
  have hz : 0 < (((a : ℝ) : ℂ)⁻¹ * (w + E₀)).im := by
    rw [Step1RegularityB_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
    positivity
  rw [Step1RegularityB_stieltjesN_eq_mV hH hz]
  unfold mV
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set lami : ℝ := hH.eigenvalues i with hlam_def
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hkey : ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w =
      (a : ℂ) * ((lami : ℂ) - (((a : ℝ) : ℂ)⁻¹ * (w + E₀))) := by
    rw [mul_sub]
    rw [show (a : ℂ) * (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) = w + E₀ by field_simp]
    ring
  rw [show ((a * lami - E₀ : ℝ) : ℂ) - w = ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w by push_cast; ring,
    hkey, mul_inv]

private theorem Step1RegularityB_im_le_norm_sub {a : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ ‖(a : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  rwa [abs_of_pos hz] at h

/-- Crude bound `‖m_V(z)‖ ≤ 1 / Im z`, valid for every `v`. -/
private theorem Step1RegularityB_mV_norm_le {ι : Type*} [Fintype ι] (v : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) : ‖mV v z‖ ≤ z.im⁻¹ := by
  have hterm : ∀ i : ι, ‖((v i : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := fun i => by
    rw [norm_inv]
    exact inv_anti₀ hz (Step1RegularityB_im_le_norm_sub hz)
  unfold mV
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
  · rw [hc0, Nat.cast_zero, _root_.inv_zero, zero_mul]
    exact inv_nonneg.2 hz.le
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcpos
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, ((v i : ℂ) - z)⁻¹‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖((v i : ℂ) - z)⁻¹‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, z.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
    _ = z.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-! ### 3. The bulk lower bound of `Im m_sc` -/

private theorem Step1RegularityB_norm_msc_pos {z : ℂ} (hz : 0 < z.im) : 0 < ‖msc z‖ :=
  norm_pos_iff.mpr fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

/-- `m_sc(z) + z = -m_sc(z)⁻¹` (private in `Defs/Semicircle.lean`). -/
private theorem Step1RegularityB_msc_add_eq_neg_inv {z : ℂ} (hz : 0 < z.im) :
    msc z + z = -(msc z)⁻¹ := by
  have hm0 : msc z ≠ 0 := norm_pos_iff.mp (Step1RegularityB_norm_msc_pos hz)
  field_simp
  linear_combination msc_mul z

/-- `|m_sc(z)|² ≥ (1 + |z|)⁻²` (private in `Defs/Semicircle.lean`). -/
private theorem Step1RegularityB_lemT_ge {z : ℂ} (hz : 0 < z.im) :
    ((1 + ‖z‖) ^ 2)⁻¹ ≤ lemT z := by
  have hr : 0 < ‖msc z‖ := Step1RegularityB_norm_msc_pos hz
  have hinv : ‖msc z‖⁻¹ ≤ ‖msc z‖ + ‖z‖ := by
    rw [← norm_inv, ← norm_neg, ← Step1RegularityB_msc_add_eq_neg_inv hz]
    exact norm_add_le _ _
  have h1 : 1 ≤ ‖msc z‖ * (1 + ‖z‖) := by
    have h := norm_msc_lt_one hz
    have := (inv_le_iff_one_le_mul₀' hr).1 (hinv.trans (by linarith : ‖msc z‖ + ‖z‖ ≤ 1 + ‖z‖))
    linarith
  rw [lemT, inv_le_iff_one_le_mul₀ (by positivity)]
  nlinarith [norm_nonneg z]

/-- **Bulk lower bound**:
`Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`, `0 < κ' ≤ 1`. -/
private theorem Step1RegularityB_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := Step1RegularityB_lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (Step1RegularityB_msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

/-! ### 4. The control parameter `Meta` and the error bound on the event -/

/-- `min (1, L² η) ≤ ℓ(z)² η`, `η = Im z`. -/
private theorem Step1RegularityB_ellz_sq_mul_ge (L : ℕ) {z : ℂ} (hz : 0 < z.im) :
    min 1 ((L : ℝ) ^ 2 * z.im) ≤ ellz L z ^ 2 * z.im := by
  unfold ellz
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hp : 0 < z.im ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hz _
  rcases le_total (z.im ^ (-(1 / 2 : ℝ))) (L : ℝ) with h | h
  · rw [min_eq_left h]
    have h1 : (z.im ^ (-(1 / 2 : ℝ))) ^ 2 * z.im = 1 := by
      have : z.im ^ (-(1 / 2 : ℝ)) * z.im ^ (-(1 / 2 : ℝ)) = z.im⁻¹ := by
        rw [← Real.rpow_add hz]; norm_num [Real.rpow_neg_one]
      rw [sq, this]; field_simp
    calc min 1 ((L : ℝ) ^ 2 * z.im) ≤ 1 := min_le_left _ _
      _ = (z.im ^ (-(1 / 2 : ℝ))) ^ 2 * z.im := h1.symm
      _ ≤ (z.im ^ (-(1 / 2 : ℝ)) + 1) ^ 2 * z.im := by
          apply mul_le_mul_of_nonneg_right _ hz.le
          nlinarith
  · rw [min_eq_right h]
    calc min 1 ((L : ℝ) ^ 2 * z.im) ≤ (L : ℝ) ^ 2 * z.im := min_le_right _ _
      _ ≤ ((L : ℝ) + 1) ^ 2 * z.im := by
          apply mul_le_mul_of_nonneg_right _ hz.le
          nlinarith

/-- `Meta(z) ≥ min (W², W² L² Im z)`. -/
private theorem Step1RegularityB_Meta_ge (L W : ℕ) {z : ℂ} (hz : 0 < z.im) :
    min ((W : ℝ) ^ 2) ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * z.im) ≤ RBM.Meta L W z := by
  have h := Step1RegularityB_ellz_sq_mul_ge L hz
  have hW : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  unfold RBM.Meta
  calc min ((W : ℝ) ^ 2) ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * z.im)
      = (W : ℝ) ^ 2 * min 1 ((L : ℝ) ^ 2 * z.im) := by
        rw [mul_min_of_nonneg _ _ hW, mul_one, mul_assoc]
    _ ≤ (W : ℝ) ^ 2 * (ellz L z ^ 2 * z.im) := mul_le_mul_of_nonneg_left h hW
    _ = (W : ℝ) ^ 2 * ellz L z ^ 2 * z.im := by ring

/-- `W² ≤ N`. -/
private theorem Step1RegularityB_W_sq_le (d : Sizes) (n : ℕ) :
    (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : d.size n = d.W n ^ 2 * d.L n ^ 2 := Sizes.size_eq d n
  have hL1 : 1 ≤ d.L n ^ 2 := Nat.one_le_pow _ _ (by have := d.three_le_L n; omega)
  have : d.W n ^ 2 ≤ d.size n := by
    calc d.W n ^ 2 = d.W n ^ 2 * 1 := (mul_one _).symm
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul_left _ hL1
      _ = d.size n := h1.symm
  exact_mod_cast this

/-- On the event, the tracial error is at most `2 c⁻¹ N^{τ'/2 - σ}` at every point of the domain
with `Im z ≥ c N^{-1+σ}`, provided `N^σ ≤ W²` (`Meta ≥ min (W², N Im z)`, `W² ≤ N`). -/
private theorem Step1RegularityB_err_pow (d : Sizes) (n : ℕ) {κ τ τ' : ℝ} {ω : SeqΩ d}
    (hev : Step1LocalEvent d n κ τ τ' ω) (hτ' : 0 ≤ τ') (hN : 1 ≤ d.size n)
    {z : ℂ} (hz : locDomain (d.size n) κ τ z) {c σ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hWσ : ((d.size n : ℕ) : ℝ) ^ σ ≤ (d.W n : ℝ) ^ 2)
    (hzc : c * ((d.size n : ℕ) : ℝ) ^ (-1 + σ) ≤ z.im) :
    ‖stieltjesN (seqXmat d n ω) z - msc z‖ ≤
      2 * c⁻¹ * ((d.size n : ℕ) : ℝ) ^ (τ' / 2 - σ) := by
  set Nr : ℝ := ((d.size n : ℕ) : ℝ) with hNr
  have hNr1 : (1 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hN
  have hNr0 : 0 < Nr := by linarith
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hz.2.1
  have h1 := hev.1 z hz
  rw [mSC_eq_msc hzim] at h1
  have hMeta : c * Nr ^ σ ≤ RBM.Meta (d.L n) (d.W n) z := by
    refine le_trans ?_ (Step1RegularityB_Meta_ge (d.L n) (d.W n) hzim)
    refine le_min ?_ ?_
    · exact le_trans (mul_le_of_le_one_left (Real.rpow_nonneg hNr0.le _) hc1) hWσ
    · have hsz : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = Nr := by
        rw [hNr]; exact_mod_cast (Sizes.size_eq d n).symm
      rw [hsz]
      calc c * Nr ^ σ = Nr * (c * Nr ^ (-1 + σ)) := by
            rw [Real.rpow_add hNr0, Real.rpow_neg_one]; field_simp
        _ ≤ Nr * z.im := mul_le_mul_of_nonneg_left hzc hNr0.le
  have hW2 : (d.W n : ℝ) ^ 2 ≤ Nr := Step1RegularityB_W_sq_le d n
  have hWτ : (d.W n : ℝ) ^ τ' ≤ Nr ^ (τ' / 2) := by
    have hW0 : (0 : ℝ) ≤ d.W n := Nat.cast_nonneg _
    calc (d.W n : ℝ) ^ τ' = ((d.W n : ℝ) ^ (2 : ℝ)) ^ (τ' / 2) := by
          rw [← Real.rpow_mul hW0]; congr 1; ring
      _ = ((d.W n : ℝ) ^ 2) ^ (τ' / 2) := by rw [Real.rpow_two]
      _ ≤ Nr ^ (τ' / 2) := Real.rpow_le_rpow (by positivity) hW2 (by linarith)
  have hcpos : 0 < c * Nr ^ σ := mul_pos hc (Real.rpow_pos_of_pos hNr0 _)
  calc ‖stieltjesN (seqXmat d n ω) z - msc z‖
      ≤ 2 * (d.W n : ℝ) ^ τ' / RBM.Meta (d.L n) (d.W n) z := h1
    _ ≤ 2 * Nr ^ (τ' / 2) / (c * Nr ^ σ) :=
        div_le_div₀ (by positivity) (by linarith) hcpos hMeta
    _ = 2 * c⁻¹ * Nr ^ (τ' / 2 - σ) := by
        rw [Real.rpow_sub hNr0]; field_simp

/-! ### 5. The rescaled point lies in the domain of the event -/

/-- If `|E₀| ≤ 2 - κ`, `|Re w| ≤ R ≤ κ'/4`, `y ≤ Im w ≤ 1/2`, `N^{-1+τ} ≤ y` and
`0 ≤ T ≤ κ'/240` (`κ' = min κ 1`), then `z = a⁻¹ (w + E₀)`, `a = e^{-T/2}`, lies in
`locDomain N (κ/2) τ`, and `Im z ≥ Im w`. -/
private theorem Step1RegularityB_domain {N : ℕ} {κ τ E₀ T R y : ℝ} (hκ : 0 < κ)
    (hE₀ : |E₀| ≤ 2 - κ) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240) (hR : R ≤ min κ 1 / 4)
    (hy0 : 0 < y) (hy : (N : ℝ) ^ (-1 + τ) ≤ y) {w : ℂ} (hw : |w.re| ≤ R) (hwy : y ≤ w.im)
    (hw1 : w.im ≤ 1 / 2) :
    locDomain N (κ / 2) τ (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) ∧
      w.im ≤ ((((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))).im := by
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hκ' : min κ 1 ≤ κ := min_le_left _ _
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hT1 : T ≤ 1 := by linarith
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := Step1RegularityB_one_le_inv hT0
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := Step1RegularityB_inv_le hT0 hT1
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E₀]
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hw
  have hwim0 : 0 < w.im := lt_of_lt_of_le hy0 hwy
  have hre : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).re =
      (Real.exp (-T / 2))⁻¹ * (w.re + E₀) := by
    rw [Step1RegularityB_inv_mul_re, Complex.add_re, Complex.ofReal_re]
  have him : (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)).im =
      (Real.exp (-T / 2))⁻¹ * w.im := by
    rw [Step1RegularityB_inv_mul_im, Complex.add_im, Complex.ofReal_im, add_zero]
  have hge : w.im ≤ (Real.exp (-T / 2))⁻¹ * w.im := by
    calc w.im = 1 * w.im := (one_mul _).symm
      _ ≤ (Real.exp (-T / 2))⁻¹ * w.im := mul_le_mul_of_nonneg_right hainv1 hwim0.le
  refine ⟨⟨?_, ?_, ?_⟩, by rw [him]; exact hge⟩
  · rw [hre, abs_mul, abs_of_pos (inv_pos.2 ha0)]
    have h1 : |w.re + E₀| ≤ R + (2 - κ) := (abs_add_le _ _).trans (add_le_add hw hE₀)
    have h2 : 0 ≤ R + (2 - κ) := by linarith
    have h3 : T * (R + (2 - κ)) ≤ min κ 1 / 240 * (R + (2 - κ)) :=
      mul_le_mul_of_nonneg_right hT h2
    calc (Real.exp (-T / 2))⁻¹ * |w.re + E₀| ≤ (1 + T) * (R + (2 - κ)) :=
          mul_le_mul hainv h1 (abs_nonneg _) (by linarith)
      _ ≤ 2 - κ / 2 := by nlinarith
  · rw [him]; exact hy.trans (hwy.trans hge)
  · rw [him]
    calc (Real.exp (-T / 2))⁻¹ * w.im ≤ (1 + T) * (1 / 2) :=
          mul_le_mul hainv hw1 hwim0.le (by linarith)
      _ ≤ 1 := by linarith

/-! ### 6. Regime 1: the tracial bulk bound for `Im z ≥ N^{-1+σ}` -/

/-- The point of the event attached to `w = E + iη`. -/
private theorem Step1RegularityB_arg_eq (a E₀ E η : ℝ) :
    ((a : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) =
      ((a⁻¹ * (E + E₀) : ℝ) : ℂ) + ((a⁻¹ * η : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [Step1RegularityB_inv_mul_re]; simp
  · rw [Step1RegularityB_inv_mul_im]; simp

/-- Regime 1 of (2.2): for `|E| ≤ R`, `N^{-1+σ} ≤ η ≤ 1/2`, on the event, the imaginary part of
`m_N` at the rescaled point is in `[κ'/24, 1 + κ'/24]`, provided the event error
`2 N^{τ'/2 - σ} ≤ κ'/24` and `N^σ ≤ W²`. -/
private theorem Step1RegularityB_bulk (d : Sizes) (n : ℕ) {κ τ τ' E₀ T R σ : ℝ} {ω : SeqΩ d}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hev : Step1LocalEvent d n (κ / 2) τ τ' ω)
    (hτ' : 0 ≤ τ') (hN : 1 ≤ d.size n) (hT0 : 0 ≤ T) (hT : T ≤ min κ 1 / 240)
    (hR : R ≤ min κ 1 / 4) (hτσ : τ ≤ σ)
    (hWσ : ((d.size n : ℕ) : ℝ) ^ σ ≤ (d.W n : ℝ) ^ 2)
    (herr : 2 * ((d.size n : ℕ) : ℝ) ^ (τ' / 2 - σ) ≤ min κ 1 / 24)
    {E η : ℝ} (hE : |E| ≤ R) (hη : ((d.size n : ℕ) : ℝ) ^ (-1 + σ) ≤ η) (hη1 : η ≤ 1 / 2) :
    min κ 1 / 24 ≤ (stieltjesN (seqXmat d n ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
      (stieltjesN (seqXmat d n ω)
        (((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤ 1 + min κ 1 / 24 := by
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκ'κ : min κ 1 ≤ κ := min_le_left _ _
  have hy0 : 0 < ((d.size n : ℕ) : ℝ) ^ (-1 + σ) := Real.rpow_pos_of_pos hNr0 _
  have hyτ : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + σ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  obtain ⟨hdom, hdomim⟩ := Step1RegularityB_domain (N := d.size n) (τ := τ) (w := ⟨E, η⟩)
    hκ hE₀ hT0 hT hR hy0 hyτ hE hη hη1
  have herrz := Step1RegularityB_err_pow d n hev hτ' hN hdom (c := 1) (σ := σ) one_pos le_rfl
    hWσ (by rw [one_mul]; exact hη.trans hdomim)
  set z : ℂ := ((Real.exp (-T / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀) with hz
  have hzim : 0 < z.im := lt_of_lt_of_le (lt_of_lt_of_le hy0 hη) hdomim
  have hnorm : ‖stieltjesN (seqXmat d n ω) z - msc z‖ ≤ min κ 1 / 24 := by
    refine herrz.trans ?_
    rw [inv_one, mul_one]; exact herr
  have hIm : |(stieltjesN (seqXmat d n ω) z).im - (msc z).im| ≤ min κ 1 / 24 := by
    calc |(stieltjesN (seqXmat d n ω) z).im - (msc z).im|
        = |(stieltjesN (seqXmat d n ω) z - msc z).im| := by rw [Complex.sub_im]
      _ ≤ ‖stieltjesN (seqXmat d n ω) z - msc z‖ := Complex.abs_im_le_norm _
      _ ≤ min κ 1 / 24 := hnorm
  have hzre : |z.re| ≤ 2 - min κ 1 / 2 := by
    have := hdom.1; linarith
  have hmsc := Step1RegularityB_msc_im_ge hκ'0 hκ'1 hzre hzim (by linarith [hdom.2.2])
  have hmscn := norm_msc_lt_one (z := z) hzim
  have hmscim : (msc z).im < 1 :=
    lt_of_le_of_lt ((le_abs_self _).trans (Complex.abs_im_le_norm _)) hmscn
  obtain ⟨h1, h2⟩ := abs_le.mp hIm
  constructor <;> linarith

/-! ### 7. The eigenvalue bound from the entry bound (`CV = 2`) -/

/-- `|λ_i| ≤ N` when every entry has modulus at most `1`: from `H ψ = λ ψ`,
`|λ| |ψ_x| ≤ Σ_y |ψ_y|`, summed over `x`. -/
private theorem Step1RegularityB_eigenvalue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hent : ∀ x y, ‖H x y‖ ≤ 1) (i : ι) :
    |hH.eigenvalues i| ≤ (Fintype.card ι : ℝ) := by
  set ψ : EuclideanSpace ℂ ι := hH.eigenvectorBasis i with hψ
  have hψn : ‖ψ‖ = 1 := hH.eigenvectorBasis.norm_eq_one i
  have hmv := hH.mulVec_eigenvectorBasis i
  have hsq : ∑ y, ‖ψ.ofLp y‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψn]; norm_num
  have hle1 : ∀ y, ‖ψ.ofLp y‖ ≤ 1 := by
    intro y
    have : ‖ψ.ofLp y‖ ^ 2 ≤ 1 := by
      rw [← hsq]
      exact Finset.single_le_sum (f := fun y => ‖ψ.ofLp y‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ y)
    nlinarith [norm_nonneg (ψ.ofLp y)]
  set S : ℝ := ∑ y, ‖ψ.ofLp y‖ with hS
  have hS1 : 1 ≤ S := by
    calc (1 : ℝ) = ∑ y, ‖ψ.ofLp y‖ ^ 2 := hsq.symm
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          nlinarith [norm_nonneg (ψ.ofLp y), hle1 y]
  have hrow : ∀ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ ≤ S := by
    intro x
    have h1 : (H.mulVec ψ.ofLp) x = (hH.eigenvalues i • ψ.ofLp) x := by rw [hmv]
    have h2 : ‖(hH.eigenvalues i • ψ.ofLp) x‖ = |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [← h2, ← h1]
    calc ‖(H.mulVec ψ.ofLp) x‖ = ‖∑ y, H x y * ψ.ofLp y‖ := rfl
      _ ≤ ∑ y, ‖H x y * ψ.ofLp y‖ := norm_sum_le _ _
      _ ≤ ∑ y, ‖ψ.ofLp y‖ := Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hent x y)
  have hsum : |hH.eigenvalues i| * S ≤ (Fintype.card ι : ℝ) * S := by
    calc |hH.eigenvalues i| * S = ∑ x, |hH.eigenvalues i| * ‖ψ.ofLp x‖ := by
          rw [hS, Finset.mul_sum]
      _ ≤ ∑ _x : ι, S := Finset.sum_le_sum fun x _ => hrow x
      _ = (Fintype.card ι : ℝ) * S := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_mul_le_mul_right hsum (by linarith)

/-- The index set has `N = (W L)²` elements. -/
private theorem Step1RegularityB_card (d : Sizes) (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Sizes.size, Idx, Z2, Fintype.card_prod, ZMod.card, sq, mul_comm]

/-! ### 8. Regularity (2.2), (2.3) of `[32]` for `vOU` on the event -/

/-- **The regularity part**, deterministic on the event
(no grid): `[32]`-regularity of `vOU` with `g = N^{-1+τs/4}`, `G = N^{-σ}`,
`c = min κ 1 / 960`, `C = 2`, `CV = 2`.  `hg`, `hG`, `hT`, `hWσ`, `herr` are the size conditions
that hold for large `n`. -/
private theorem Step1RegularityB_regular (d : Sizes) (n : ℕ) {κ τs E₀ : ℝ} {ω : SeqΩ d}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hτs0 : 0 < τs)
    (hev : Step1LocalEvent d n (κ / 2) (τs / 8) (τs / 8) ω) (hN : 2 ≤ d.size n)
    (hg : ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) ≤ 1 / 2)
    (hG : ((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3))) ≤ min κ 1 / 4)
    (hT : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240)
    (hWσ : ((d.size n : ℕ) : ℝ) ^ (τs / 4) ≤ (d.W n : ℝ) ^ 2)
    (herr : 2 * ((d.size n : ℕ) : ℝ) ^ (τs / 8 / 2 - τs / 4) ≤ min κ 1 / 24) :
    IsRegular32 (vOU d n τs E₀ ω) (((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4))
      (((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 := by
  have hN1 : 1 ≤ d.size n := by omega
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hNr2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hT0 : 0 ≤ ouTStar d τs n := Real.rpow_nonneg hNr0.le _
  have hT' : ouTStar d τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar d τs n ≤ 1 := by linarith
  have ha0 : 0 < Real.exp (-(ouTStar d τs n) / 2) := Real.exp_pos _
  have hainv1 : 1 ≤ (Real.exp (-(ouTStar d τs n) / 2))⁻¹ := Step1RegularityB_one_le_inv hT0
  have hainv : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 1 + ouTStar d τs n :=
    Step1RegularityB_inv_le hT0 hT1
  have hH := seqXmat_isHermitian d n ω
  have hgpos : 0 < ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hNr0 _
  have hbulk : ∀ E η : ℝ, |E| ≤ ((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3))) →
      ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      min κ 1 / 24 ≤ (stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ∧
        (stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im ≤
          1 + min κ 1 / 24 := fun E η hE hη hη1 =>
    Step1RegularityB_bulk d n hκ hE₀ hev (by positivity) hN1 hT0 hT hG (by linarith) hWσ herr
      hE hη hη1
  refine ⟨?_, ?_⟩
  · intro E η hE hgη hη10
    have hηpos : 0 < η := lt_of_lt_of_le hgpos hgη
    have hdict : mV (vOU d n τs E₀ ω) ⟨E, η⟩ =
        ((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀)) :=
      Step1RegularityB_mV_vOU hH ha0 E₀ (w := ⟨E, η⟩) hηpos
    have hdictIm : (mV (vOU d n τs E₀ ω) ⟨E, η⟩).im =
        (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
      rw [hdict, Step1RegularityB_inv_mul_im]
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨hb1, hb2⟩ := hbulk E η hE hgη hη12
      rw [hdictIm]
      have hS0 : 0 ≤ (stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        linarith
      refine ⟨?_, ?_⟩
      · calc min κ 1 / 960 ≤ min κ 1 / 24 := by linarith
          _ ≤ _ := hb1
          _ = 1 * _ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS0
      · calc _ ≤ (1 + ouTStar d τs n) * (1 + min κ 1 / 24) :=
              mul_le_mul hainv hb2 hS0 (by linarith)
          _ ≤ 2 := by nlinarith
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      have hainv0 : 0 < (Real.exp (-(ouTStar d τs n) / 2))⁻¹ := inv_pos.2 ha0
      have hlb := (hbulk E (1 / 2) hE (by linarith) le_rfl).1
      have hmono : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2) *
            (stieltjesN (seqXmat d n ω)
              (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ *
                ((⟨E, 1 / 2⟩ : ℂ) + E₀))).im ≤
          (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * η *
            (stieltjesN (seqXmat d n ω)
              (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im := by
        rw [Step1RegularityB_arg_eq, Step1RegularityB_arg_eq]
        exact stieltjesN_eta_mul_im_mono (seqXmat d n ω) hH _ _ _ (by positivity)
          (mul_le_mul_of_nonneg_left hη12'.le hainv0.le)
      set S₂ := (stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * ((⟨E, η⟩ : ℂ) + E₀))).im with hS₂
      have h3 : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2) * (min κ 1 / 24) ≤
          (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (η * S₂) := by
        rw [← mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hlb (by positivity)) hmono
      have h4 : 1 / 2 * (min κ 1 / 24) ≤ η * S₂ := by
        have : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (1 / 2 * (min κ 1 / 24)) ≤
            (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * (η * S₂) := by
          rw [← mul_assoc]; exact h3
        exact le_of_mul_le_mul_left this hainv0
      have hS₂pos : 0 < S₂ := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hηpos.le (neg_nonneg.2 hneg)]
      have h5 : min κ 1 / 480 ≤ S₂ := by
        nlinarith [mul_le_mul_of_nonneg_right hη10 hS₂pos.le]
      refine ⟨?_, ?_⟩
      · rw [hdictIm]
        calc min κ 1 / 960 ≤ min κ 1 / 480 := by linarith
          _ ≤ S₂ := h5
          _ = 1 * S₂ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hainv1 hS₂pos.le
      · have hnb := Step1RegularityB_mV_norm_le (vOU d n τs E₀ ω) (z := ⟨E, η⟩) hηpos
        calc (mV (vOU d n τs E₀ ω) ⟨E, η⟩).im ≤ ‖mV (vOU d n τs E₀ ω) ⟨E, η⟩‖ :=
              (le_abs_self _).trans (Complex.abs_im_le_norm _)
          _ ≤ (⟨E, η⟩ : ℂ).im⁻¹ := hnb
          _ ≤ 2 := by
              change η⁻¹ ≤ 2
              rw [inv_le_comm₀ hηpos (by norm_num)]
              linarith
  · intro i
    have hc : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
      rw [Step1RegularityB_card]
    have hlam := Step1RegularityB_eigenvalue_le hH hev.2 i
    rw [hc] at hlam
    rw [hc, Real.rpow_two]
    set a := Real.exp (-(ouTStar d τs n) / 2) with ha
    have ha1 : a ≤ 1 := Step1RegularityB_exp_le_one hT0
    have hE₀2 : |E₀| ≤ 2 := by linarith [abs_nonneg E₀]
    have h1 : |vOU d n τs E₀ ω i| ≤ a * |hH.eigenvalues i| + |E₀| := by
      change |a * hH.eigenvalues i - E₀| ≤ _
      calc |a * hH.eigenvalues i - E₀| ≤ |a * hH.eigenvalues i| + |E₀| := abs_sub _ _
        _ = a * |hH.eigenvalues i| + |E₀| := by rw [abs_mul, abs_of_pos ha0]
    have h2 : a * |hH.eigenvalues i| ≤ ((d.size n : ℕ) : ℝ) :=
      (mul_le_of_le_one_left (abs_nonneg _) ha1).trans hlam
    nlinarith

/-! ### 9. The free-convolution strip: closeness of `m_V` to the rescaled `m_sc` -/

/-- **The closeness hypothesis `hyp` of `FreeConvStability.freeConv_stable_local`**, on the event,
at every `w` of the
strip `|Re w| ≤ κ'/16`, `c₀ t/4 ≤ Im w ≤ 1/2`, `t = 1 - e^{-T}`: the lower edge of the strip is
above `N^{-1+τs/8}` (`hedge`), so the strip stays inside the domain of the event. -/
private theorem Step1RegularityB_strip (d : Sizes) (n : ℕ) {κ τs E₀ c₀ C₀ : ℝ} {ω : SeqΩ d}
    (hκ : 0 < κ) (hE₀ : |E₀| ≤ 2 - κ) (hτs0 : 0 < τs) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hev : Step1LocalEvent d n (κ / 2) (τs / 8) (τs / 8) ω) (hN : 1 ≤ d.size n)
    (hT : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240)
    (hWσ : ((d.size n : ℕ) : ℝ) ^ τs ≤ (d.W n : ℝ) ^ 2)
    (hedge : ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 8) ≤
      c₀ / 8 * ((d.size n : ℕ) : ℝ) ^ (-1 + τs))
    (hrate : ((d.size n : ℕ) : ℝ) ^ (-(9 * τs / 16)) ≤ min 1 (c₀ / 8) / (4 * C₀))
    {w : ℂ} (hw : |w.re| ≤ min κ 1 / 16)
    (hlow : c₀ * (1 - Real.exp (-(ouTStar d τs n))) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (vOU d n τs E₀ ω) w - (Real.sqrt (Real.exp (-(ouTStar d τs n))) : ℂ)⁻¹ *
        msc ((Real.sqrt (Real.exp (-(ouTStar d τs n))) : ℂ)⁻¹ * (w + E₀))‖ ≤
      ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hTpos : 0 < ouTStar d τs n := Real.rpow_pos_of_pos hNr0 _
  have hT' : ouTStar d τs n ≤ min κ 1 / 240 := hT
  have hT1 : ouTStar d τs n ≤ 1 := by
    have : min κ 1 ≤ 1 := min_le_right _ _
    linarith
  have hH := seqXmat_isHermitian d n ω
  rw [Step1RegularityB_sqrt_exp]
  have ha0 : 0 < Real.exp (-(ouTStar d τs n) / 2) := Real.exp_pos _
  have hainv : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 1 + ouTStar d τs n :=
    Step1RegularityB_inv_le hTpos.le hT1
  have hhalf := Step1RegularityB_half_le_one_sub_exp hTpos.le hT1
  have hy : c₀ / 8 * ouTStar d τs n ≤ w.im := by
    have : c₀ / 8 * ouTStar d τs n ≤ c₀ * (1 - Real.exp (-(ouTStar d τs n))) / 4 := by
      nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * ouTStar d τs n := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  obtain ⟨hdom, hdomim⟩ := Step1RegularityB_domain (N := d.size n) (τ := τs / 8)
    (R := min κ 1 / 16) hκ hE₀ hTpos.le hT' (by linarith) hy0 hedge hw hy hw1
  set c₁ : ℝ := min 1 (c₀ / 8) with hc₁
  have hc₁0 : 0 < c₁ := lt_min one_pos (by positivity)
  have hc₁1 : c₁ ≤ 1 := min_le_left _ _
  have hc₁c : c₁ ≤ c₀ / 8 := min_le_right _ _
  have herrz := Step1RegularityB_err_pow d n hev (by positivity : (0 : ℝ) ≤ τs / 8) hN hdom
    hc₁0 hc₁1 (σ := τs) hWσ
    (by
      calc c₁ * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ c₀ / 8 * ouTStar d τs n :=
            mul_le_mul_of_nonneg_right hc₁c hTpos.le
        _ ≤ w.im := hy
        _ ≤ _ := hdomim)
  have hdict : mV (vOU d n τs E₀ ω) w =
      ((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (seqXmat d n ω)
        (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) :=
    Step1RegularityB_mV_vOU hH ha0 E₀ hw0
  rw [hdict, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg ha0.le]
  have ha2 : (Real.exp (-(ouTStar d τs n) / 2))⁻¹ ≤ 2 := by linarith [hT', min_le_right κ 1]
  have hsplit : ((d.size n : ℕ) : ℝ) ^ (τs / 8 / 2 - τs) =
      ((d.size n : ℕ) : ℝ) ^ (-(9 * τs / 16)) * ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hNr0]; congr 1; ring
  have hY0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := Real.rpow_nonneg hNr0.le _
  calc (Real.exp (-(ouTStar d τs n) / 2))⁻¹ * ‖stieltjesN (seqXmat d n ω)
          (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀)) -
        msc (((Real.exp (-(ouTStar d τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E₀))‖
      ≤ 2 * (2 * c₁⁻¹ * ((d.size n : ℕ) : ℝ) ^ (τs / 8 / 2 - τs)) :=
        mul_le_mul ha2 herrz (norm_nonneg _) (by norm_num)
    _ = 4 * c₁⁻¹ * (((d.size n : ℕ) : ℝ) ^ (-(9 * τs / 16)) *
          ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))) := by rw [hsplit]; ring
    _ ≤ 4 * c₁⁻¹ * ((c₁ / (4 * C₀)) * ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))) := by
        gcongr
    _ = ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by
        field_simp

/-! ### 10. Assembly: the good event holds on `Step1LocalEvent`, eventually in `n` -/

private theorem Step1RegularityB_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h

/-- **Deterministic part of the good event**: eventually in `n`, every `ω` of the event
`Step1LocalEvent d n (κ/2) (τs/8) (τs/8)` has `vOU` `[32]`-regular and the free-convolution
density within `N^{-3τs/8}` of `ρ_sc(E₀)`.  All the size conditions are of the form
`N^{-e} ≤ c` with `e > 0` (so they hold for large `N`), and `N^{τs} ≤ W²` from `τs ≤ 𝔠`. -/
private theorem Step1RegularityB_det (𝔠 : ℝ) (d : Sizes) (hd : Admissible 𝔠 d) {κ τs E₀ : ℝ}
    (hκ : 0 < κ) (hτs0 : 0 < τs) (hτs1 : τs < 1) (hτs𝔠 : τs ≤ 𝔠) (hE₀ : |E₀| ≤ 2 - κ) :
    ∀ᶠ n in atTop, ∀ ω : SeqΩ d, Step1LocalEvent d n (κ / 2) (τs / 8) (τs / 8) ω →
      (IsRegular32 (vOU d n τs E₀ ω) (((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4))
          (((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3)))) (min κ 1 / 960) 2 2 ∧
        ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST (vOU d n τs E₀ ω)
            (1 - Real.exp (-(ouTStar d τs n))) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - rhoSC E₀| ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hFC⟩ := FreeConvStability.freeConv_stable_local hκ
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd.1
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  have eg := Step1RegularityB_rpow_ev (e := -1 + τs / 4) (c := 1 / 2) (by linarith)
    (by norm_num)
  have eG := Step1RegularityB_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3)))
    (c := min κ 1 / 4) (by linarith) (by positivity)
  have eT := Step1RegularityB_rpow_ev (e := -1 + τs) (c := min (min κ 1 / 240) c₀)
    (by linarith) (lt_min (by positivity) hc₀)
  have eerr := Step1RegularityB_rpow_ev (e := τs / 8 / 2 - τs / 4) (c := min κ 1 / 48)
    (by linarith) (by positivity)
  have eedge := Step1RegularityB_rpow_ev (e := -(7 * τs / 8)) (c := c₀ / 8)
    (by linarith) (by positivity)
  have erate := Step1RegularityB_rpow_ev (e := -(9 * τs / 16))
    (c := min 1 (c₀ / 8) / (4 * C₀)) (by linarith) (by positivity)
  have eeps := Step1RegularityB_rpow_ev (e := -(3 * τs / 8)) (c := c₀ * C₀)
    (by linarith) (by positivity)
  filter_upwards [hd.2, hNtend.eventually eg, hNtend.eventually eG, hNtend.eventually eT,
    hNtend.eventually eerr, hNtend.eventually eedge, hNtend.eventually erate,
    hNtend.eventually eeps, hNtend.eventually_ge_atTop 2] with n hW hg hG hT herr hedge hrate
    heps hN2
  intro ω hev
  have hNr1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN2' : 2 ≤ d.size n := by exact_mod_cast hN2
  have hN1 : 1 ≤ d.size n := by omega
  have hT1 : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ min κ 1 / 240 := hT.trans (min_le_left _ _)
  have hT2 : ((d.size n : ℕ) : ℝ) ^ (-1 + τs) ≤ c₀ := hT.trans (min_le_right _ _)
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWτ : ((d.size n : ℕ) : ℝ) ^ τs ≤ (d.W n : ℝ) ^ 2 :=
    calc ((d.size n : ℕ) : ℝ) ^ τs ≤ ((d.size n : ℕ) : ℝ) ^ 𝔠 :=
          Real.rpow_le_rpow_of_exponent_le hNr1 hτs𝔠
      _ ≤ (d.W n : ℝ) := hW
      _ ≤ (d.W n : ℝ) ^ 2 := by nlinarith
  have hWτ4 : ((d.size n : ℕ) : ℝ) ^ (τs / 4) ≤ (d.W n : ℝ) ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)).trans hWτ
  refine ⟨Step1RegularityB_regular d n hκ hE₀ hτs0 hev hN2' hg hG hT1 hWτ4 (by linarith), ?_⟩
  -- the free-convolution part
  have hTpos : 0 < ouTStar d τs n := Real.rpow_pos_of_pos hNr0 _
  have ht : 0 < 1 - Real.exp (-(ouTStar d τs n)) := Step1RegularityB_one_sub_exp_pos hTpos
  have htc : 1 - Real.exp (-(ouTStar d τs n)) ≤ c₀ :=
    (Step1RegularityB_one_sub_exp_le _).trans hT2
  have hε0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ := by positivity
  have hεc : ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀ ≤ c₀ := by
    rw [div_le_iff₀ hC₀]; exact heps
  have hedge' : ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 8) ≤
      c₀ / 8 * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) := by
    have hsplit : ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 8) =
        ((d.size n : ℕ) : ℝ) ^ (-(7 * τs / 8)) * ((d.size n : ℕ) : ℝ) ^ (-1 + τs) := by
      rw [← Real.rpow_add hNr0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hedge (Real.rpow_nonneg hNr0.le _)
  obtain ⟨ρ, hρ1, hρ2, -⟩ := hFC (vOU d n τs E₀ ω) (Real.exp (-(ouTStar d τs n)))
    (1 - Real.exp (-(ouTStar d τs n))) E₀ (((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀)
    ht htc (by ring) hE₀ hε0 hεc
    (fun w hw hlow hw1 => Step1RegularityB_strip d n hκ hE₀ hτs0 hc₀ hC₀ hev hN1 hT1 hWτ
      hedge' hrate hw hlow hw1)
  refine ⟨ρ, hρ1, ?_⟩
  calc |ρ - rhoSC E₀| ≤ C₀ * (((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) / C₀) := hρ2
    _ = ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by field_simp

/-! ### 11. The statement -/

/-- **The good event of Step 1**: with
probability `≥ 1 - N^{-D}`, eventually, `vOU` is `[32]`-regular with `g = N^{-1+τs/4}`,
`G = N^{-min(τs/4, (1-τs)/3)}`, `c = min κ 1 / 960`, `C = 2`, `CV = 2`, and the
free-convolution density at `t = 1 - e^{-t*}` exists and is within `N^{-3τs/8}` of `ρ_sc(E₀)`;
`τs ≤ 𝔠` (the band local-law error `W^{-2}` must not dominate the rate).  The hypothesis is
`locSC`; the probabilistic input is `step1LocalEvent_highProb` at `(κ/2, τs/8, τs/8, D)`. -/
theorem step1Good_highProb :
    RBM.Endpoints.locSC → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, RBM.Endpoints.Admissible 𝔠 d →
    ∀ κ τs E₀ D : ℝ, 0 < κ → 0 < τs → τs < 1 → τs ≤ 𝔠 → |E₀| ≤ 2 - κ → 0 < D →
      ∀ᶠ n in atTop, Sizes.seqP d {ω | ¬ (RBM.Univ.IsRegular32 (vOU d n τs E₀ ω)
          (((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4))
          (((d.size n : ℕ) : ℝ) ^ (-(min (τs / 4) ((1 - τs) / 3))))
          (min κ 1 / 960) 2 2 ∧
        ∃ ρ : ℝ, Tendsto (fun η : ℝ => (RBM.Univ.freeConvST (vOU d n τs E₀ ω)
            (1 - Real.exp (-(RBM.Univ.ouTStar d τs n))) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - RBM.Univ.rhoSC E₀| ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)))} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  intro hloc 𝔠 h𝔠 d hd κ τs E₀ D hκ hτs0 hτs1 hτs𝔠 hE₀ hD
  have hev := step1LocalEvent_highProb hloc 𝔠 h𝔠 d hd (κ / 2) (τs / 8) (τs / 8) D
    (by positivity) (by positivity) (by positivity) hD
  have hdet := Step1RegularityB_det 𝔠 d hd hκ hτs0 hτs1 hτs𝔠 hE₀
  filter_upwards [hev, hdet] with n hn hdn
  refine le_trans (measure_mono ?_) hn
  intro ω hω hevω
  exact hω (hdn ω hevω)

end RBM.Univ

/-! ## Compiled instance -/
