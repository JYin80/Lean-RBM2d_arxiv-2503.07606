/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins
import RBM2D.Green.FlucAvg
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The high-probability event of Step 1: tracial local law uniformly in `z`, and an entry bound

From `locSC` (kept as the hypothesis of the theorem) we prove that, with
probability `≥ 1 - N^{-D}` eventually, simultaneously

* for every `z` in the spectral domain `locDomain N κ τ`:
  `‖N⁻¹ Tr G(z) - m_sc(z)‖ ≤ 2 W^{τ'} / Meta(z)`, and
* every entry satisfies `|h_xy| ≤ 1`.

Proof.
* `locSC` is applied with `τ'' = min τ τ'` and `D + 10` on a polynomial grid of the domain
  (`(5 N⁴ + 1)²` points, mesh `≤ N⁻⁴`, all points in the domain).  Its `(G_bound_ave)` half
  bounds every block average `W⁻² Σ_{x ∈ Iblk a} G_xx - m_sc`, hence
  (`N⁻¹ Tr G = L⁻² Σ_a (block average)`, `Step1RegularityA_tracial_le`) the normalized trace.
  The union bound is `measure_iUnion_fintype_le`; `(5 N⁴ + 1)² ≤ N⁹` for `N ≥ 36`.
* Deterministic interpolation from the grid to the continuum (`Step1RegularityA_compare`):
  `m_N` through the spectral formula (`|m_N(z) - m_N(z')| ≤ |z - z'| / (Im z Im z')`), `m_sc`
  through `m (m + z) = -1` and `Im m_sc ≥ |m_sc|² Im z ≥ Im z / 16` (`zztE_quant`), and the
  ratio `Meta(z') / Meta(z) ≥ 2/3` (`Meta = W² (min 1 (L √η) + √η)²`).  Only `Im z ≥ N⁻¹` is
  used, so no condition on `τ` enters the thresholds.
* Entries: every coordinate of the Gaussian slice is sub-Gaussian with variance proxy
  `1 / (5 W²)` (`gvar ≤ svar ≤ 1 / (5 W²)`); a Chernoff bound and a union over the `2 N²`
  coordinates give `P(some |h_xy| > 1) ≤ 4 N² exp(-5 W² / 8)`, which is `≤ N^{-(D+1)}`
  eventually since `W ≥ N^𝔠`.
* No measurability of the event is needed: the bounds are subadditivity of the measure.

Only the `(G_bound_ave)` half of `locSC` is used.

Lemmas: `Step1RegularityA_stieltjesN_eq_mV`; `Step1RegularityA_im_le_norm_sub`,
`Step1RegularityA_sub_ne_zero`; `Step1RegularityA_mV_lip` (for `mV`);
`Step1RegularityA_grid_exists` (degenerate interval allowed); `Step1RegularityA_zpt`,
`Step1RegularityA_zpt_cover` and the union bound in the theorem (a grid of the whole domain);
`Step1RegularityA_compare`; `Step1RegularityA_msc_lip` (from `msc_mul`).
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ### 1. The control parameter `Meta` -/

private theorem Step1RegularityA_ellz_ge_one (L : ℕ) {z : ℂ} (hz : 0 < z.im) : 1 ≤ ellz L z := by
  unfold ellz
  have h1 : 0 < z.im ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hz _
  have h2 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have : 0 ≤ min (z.im ^ (-(1 / 2 : ℝ))) (L : ℝ) := le_min h1.le h2
  linarith

/-- `Meta = W² (min 1 (L √η) + √η)²`: this form is monotone in `η`. -/
private theorem Step1RegularityA_Meta_eq (L W : ℕ) {z : ℂ} (hz : 0 < z.im) :
    RBM.Meta L W z =
      (W : ℝ) ^ 2 * (min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im) ^ 2 := by
  have hs : 0 < Real.sqrt z.im := Real.sqrt_pos.2 hz
  have h1 : z.im ^ (-(1 / 2 : ℝ)) = (Real.sqrt z.im)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hz.le]
  have h2 : ellz L z * Real.sqrt z.im =
      min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im := by
    unfold ellz
    rw [h1, add_mul, min_mul_of_nonneg _ _ hs.le, inv_mul_cancel₀ hs.ne', one_mul]
  calc RBM.Meta L W z = (W : ℝ) ^ 2 * ellz L z ^ 2 * z.im := rfl
    _ = (W : ℝ) ^ 2 * (ellz L z * Real.sqrt z.im) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hz.le]; ring
    _ = _ := by rw [h2]

private theorem Step1RegularityA_Meta_pos (L W : ℕ) (hW : 1 ≤ W) {z : ℂ} (hz : 0 < z.im) :
    0 < RBM.Meta L W z := by
  have h1 := Step1RegularityA_ellz_ge_one L hz
  have hW' : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  unfold RBM.Meta
  have : 0 < ellz L z := by linarith
  positivity

/-- `Meta` is nondecreasing in `Im z`. -/
private theorem Step1RegularityA_Meta_mono (L W : ℕ) {z z' : ℂ} (hz : 0 < z.im)
    (hzz : z.im ≤ z'.im) : RBM.Meta L W z ≤ RBM.Meta L W z' := by
  have hz' : 0 < z'.im := lt_of_lt_of_le hz hzz
  rw [Step1RegularityA_Meta_eq L W hz, Step1RegularityA_Meta_eq L W hz']
  have hs : Real.sqrt z.im ≤ Real.sqrt z'.im := Real.sqrt_le_sqrt hzz
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmin : min 1 ((L : ℝ) * Real.sqrt z.im) ≤ min 1 ((L : ℝ) * Real.sqrt z'.im) :=
    min_le_min le_rfl (mul_le_mul_of_nonneg_left hs hL)
  have h0 : 0 ≤ min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im :=
    add_nonneg (le_min zero_le_one (mul_nonneg hL (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  have h1 : min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im ≤
      min 1 ((L : ℝ) * Real.sqrt z'.im) + Real.sqrt z'.im := add_le_add hmin hs
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (by positivity)

/-- `Meta / Im z = W² ℓ²` is nonincreasing in `Im z`: for `Im z' ≤ Im z`,
`Meta(z) Im z' ≤ Meta(z') Im z`. -/
private theorem Step1RegularityA_Meta_ratio (L W : ℕ) {z z' : ℂ} (hz' : 0 < z'.im)
    (hzz : z'.im ≤ z.im) : RBM.Meta L W z * z'.im ≤ RBM.Meta L W z' * z.im := by
  have hz : 0 < z.im := lt_of_lt_of_le hz' hzz
  have hℓ : ellz L z ≤ ellz L z' := by
    unfold ellz
    have h : z.im ^ (-(1 / 2 : ℝ)) ≤ z'.im ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hz' hzz (by norm_num)
    have := min_le_min h (le_refl (L : ℝ))
    linarith
  have hℓ0 : 0 ≤ ellz L z := by
    have := Step1RegularityA_ellz_ge_one L hz
    linarith
  have h2 : ellz L z ^ 2 ≤ ellz L z' ^ 2 := pow_le_pow_left₀ hℓ0 hℓ 2
  unfold RBM.Meta
  have hc : 0 ≤ (W : ℝ) ^ 2 * z.im * z'.im := by positivity
  calc (W : ℝ) ^ 2 * ellz L z ^ 2 * z.im * z'.im
      = ((W : ℝ) ^ 2 * z.im * z'.im) * ellz L z ^ 2 := by ring
    _ ≤ ((W : ℝ) ^ 2 * z.im * z'.im) * ellz L z' ^ 2 := mul_le_mul_of_nonneg_left h2 hc
    _ = (W : ℝ) ^ 2 * ellz L z' ^ 2 * z'.im * z.im := by ring

/-- `Meta ≤ 4 W²` for `Im z ≤ 1`. -/
private theorem Step1RegularityA_Meta_le (L W : ℕ) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    RBM.Meta L W z ≤ 4 * (W : ℝ) ^ 2 := by
  rw [Step1RegularityA_Meta_eq L W hz]
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hs1 : Real.sqrt z.im ≤ 1 := Real.sqrt_le_one.mpr hz1
  have hmin : min 1 ((L : ℝ) * Real.sqrt z.im) ≤ 1 := min_le_left _ _
  have h0 : 0 ≤ min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im :=
    add_nonneg (le_min zero_le_one (mul_nonneg hL (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  have h2 : min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im ≤ 2 := by linarith
  have h3 : (min 1 ((L : ℝ) * Real.sqrt z.im) + Real.sqrt z.im) ^ 2 ≤ 2 ^ 2 :=
    pow_le_pow_left₀ h0 h2 2
  nlinarith [sq_nonneg (W : ℝ)]

/-! ### 2. The semicircle transform: lower bound of `Im m_sc` and Lipschitz continuity -/

/-- `Im m_sc(z) ≥ |m_sc(z)|² Im z`, from `m (m + z) = -1`. -/
private theorem Step1RegularityA_msc_im_ge {z : ℂ} (hz : 0 < z.im) :
    ‖msc z‖ ^ 2 * z.im ≤ (msc z).im := by
  have hm := msc_mul z
  have hpos := msc_im_pos hz
  have hre := congrArg Complex.re hm
  have him := congrArg Complex.im hm
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at hre him
  have key : ((msc z).re ^ 2 + (msc z).im ^ 2) * ((msc z).im + z.im) = (msc z).im := by
    linear_combination (msc z).re * him - (msc z).im * hre
  have hn : ‖msc z‖ ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn]
  have h0 : 0 ≤ ((msc z).re ^ 2 + (msc z).im ^ 2) * (msc z).im :=
    mul_nonneg (by positivity) hpos.le
  nlinarith

/-- Lipschitz bound for `m_sc`:
`|m_sc(z') - m_sc(z)| Im m_sc(z) ≤ |z' - z|`. -/
private theorem Step1RegularityA_msc_lip {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖msc z' - msc z‖ * (msc z).im ≤ ‖z' - z‖ := by
  set a := msc z with ha
  set m' := msc z' with hm'
  have hquad : (m' - a) * (a + m' + z') = -((z' - z) * a) := by
    have h1 := msc_mul z'
    have h2 := msc_mul z
    linear_combination h1 - h2
  have him' := msc_im_pos hz'
  have hden : a.im ≤ ‖a + m' + z'‖ := by
    have h1 : (a + m' + z').im = a.im + m'.im + z'.im := by simp [Complex.add_im]
    calc a.im ≤ (a + m' + z').im := by rw [h1]; linarith
      _ ≤ |(a + m' + z').im| := le_abs_self _
      _ ≤ ‖a + m' + z'‖ := Complex.abs_im_le_norm _
  have ha1 : ‖a‖ ≤ 1 := (norm_msc_lt_one hz).le
  calc ‖m' - a‖ * a.im ≤ ‖m' - a‖ * ‖a + m' + z'‖ :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖z' - z‖ * ‖a‖ := by rw [← norm_mul, hquad, norm_neg, norm_mul]
    _ ≤ ‖z' - z‖ := mul_le_of_le_one_right (norm_nonneg _) ha1

/-- On the domain, `Im m_sc(z) ≥ Im z / 16` (`zztE_quant`: `|m_sc|² ≥ 1/16`). -/
private theorem Step1RegularityA_msc_im_ge_sixteenth {z : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) :
    z.im / 16 ≤ (msc z).im := by
  have h16 : (1 / 16 : ℝ) ≤ lemT z := (zztE_quant hκ hz hz1 hre).2.1
  have h := Step1RegularityA_msc_im_ge hz
  have : (1 / 16 : ℝ) ≤ ‖msc z‖ ^ 2 := h16
  nlinarith

/-- The Lipschitz constant `16 / Im z` of `m_sc` on the domain. -/
private theorem Step1RegularityA_msc_lip_domain {z z' : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) (hz' : 0 < z'.im) :
    ‖msc z' - msc z‖ ≤ 16 * ‖z' - z‖ / z.im := by
  have h1 := Step1RegularityA_msc_lip hz hz'
  have h2 := Step1RegularityA_msc_im_ge_sixteenth hκ hz hz1 hre
  rw [le_div_iff₀ hz]
  have h3 : ‖msc z' - msc z‖ * (z.im / 16) ≤ ‖msc z' - msc z‖ * (msc z).im :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  nlinarith

/-! ### 3. The normalized trace `m_N`: spectral formula and Lipschitz bound -/

private theorem Step1RegularityA_im_le_norm_sub {a : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ ‖(a : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  rwa [abs_of_pos hz] at h

private theorem Step1RegularityA_sub_ne_zero {a : ℝ} {z : ℂ} (hz : 0 < z.im) :
    (a : ℂ) - z ≠ 0 := fun h => by
  have := Step1RegularityA_im_le_norm_sub (a := a) hz
  rw [h] at this
  simp at this
  linarith

/-- `stieltjesN` is the finite-sum Stieltjes transform `mV` of the eigenvalues. -/
private theorem Step1RegularityA_stieltjesN_eq_mV {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- Elementary Lipschitz bound for `mV`: a term-by-term bound,
no local law. -/
private theorem Step1RegularityA_mV_lip {ι : Type*} [Fintype ι] (v : ι → ℝ) {z z' : ℂ}
    (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖mV v z - mV v z'‖ ≤ ‖z - z'‖ / (z.im * z'.im) := by
  have hdiff : mV v z - mV v z' =
      ((Fintype.card ι : ℕ) : ℂ)⁻¹ *
        ∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹) := by
    unfold mV
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := Step1RegularityA_sub_ne_zero (a := v i) hz
    have h2 := Step1RegularityA_sub_ne_zero (a := v i) hz'
    field_simp
    ring
  have hterm : ∀ i : ι, ‖(z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖ ≤
      ‖z - z'‖ * (z.im * z'.im)⁻¹ := by
    intro i
    rw [norm_mul, norm_mul, norm_inv, norm_inv]
    have h1 := Step1RegularityA_im_le_norm_sub (a := v i) hz
    have h2 := Step1RegularityA_im_le_norm_sub (a := v i) hz'
    have hz0 : (0 : ℝ) < ‖(v i : ℂ) - z‖ := lt_of_lt_of_le hz h1
    have hz0' : (0 : ℝ) < ‖(v i : ℂ) - z'‖ := lt_of_lt_of_le hz' h2
    rw [mul_inv]
    gcongr
  have hsum : ‖∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖ ≤
      (Fintype.card ι : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖
        ≤ ∑ _i : ι, ‖z - z'‖ * (z.im * z'.im)⁻¹ := Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card ι : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
  · rw [hc0, Nat.cast_zero, _root_.inv_zero, zero_mul]
    positivity
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcpos
  rw [div_eq_inv_mul]
  calc (Fintype.card ι : ℝ)⁻¹ *
      ‖∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (z.im * z'.im)⁻¹ * ‖z - z'‖ := by field_simp

/-- Lipschitz bound for the normalized trace of a Hermitian matrix. -/
private theorem Step1RegularityA_stieltjesN_lip {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖stieltjesN H z - stieltjesN H z'‖ ≤ ‖z - z'‖ / (z.im * z'.im) := by
  rw [Step1RegularityA_stieltjesN_eq_mV hH hz, Step1RegularityA_stieltjesN_eq_mV hH hz']
  exact Step1RegularityA_mV_lip _ hz hz'

/-! ### 4. The normalized trace from the block averages -/

/-- The block `Iblk a` is the fiber of `i ↦ (split i).1` over `a`. -/
private theorem Step1RegularityA_Iblk_eq_filter (L W : ℕ) [NeZero L] [NeZero W] (a : Z2 L) :
    Iblk L W a = Finset.univ.filter (fun i : Idx L W => (split L W i).1 = a) := by
  ext i
  simp [mem_Iblk]

/-- `N⁻¹ Tr G` is the average over the `L²` blocks of the block averages, so it is within `B`
of `m` when every block average is. -/
private theorem Step1RegularityA_tracial_le (L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (Idx L W) (Idx L W) ℂ) (z m : ℂ) {B : ℝ}
    (h : ∀ a : Z2 L, ‖((W : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W a, green H z x x - m‖ ≤ B) :
    ‖stieltjesN H z - m‖ ≤ B := by
  classical
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hcardI : (Fintype.card (Idx L W) : ℂ) = (W : ℂ) ^ 2 * (L : ℂ) ^ 2 := by
    have : Fintype.card (Idx L W) = (W * L) ^ 2 := by
      simp [Idx, Z2, Fintype.card_prod, ZMod.card, sq]
    rw [this]; push_cast; ring
  have hcardZ : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
    simp [Z2, Fintype.card_prod, ZMod.card, sq]
  have hcardZc : (Fintype.card (Z2 L) : ℂ) = (L : ℂ) ^ 2 := by
    have : Fintype.card (Z2 L) = L ^ 2 := by simp [Z2, Fintype.card_prod, ZMod.card, sq]
    rw [this]; push_cast; ring
  have hpart : ∑ a : Z2 L, ∑ x ∈ Iblk L W a, green H z x x = ∑ x : Idx L W, green H z x x := by
    simp_rw [Step1RegularityA_Iblk_eq_filter]
    exact Finset.sum_fiberwise Finset.univ (fun i : Idx L W => (split L W i).1)
      (fun x => green H z x x)
  have hsum : ∑ a : Z2 L, (((W : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W a, green H z x x - m) =
      ((W : ℂ) ^ 2)⁻¹ * ∑ x : Idx L W, green H z x x - (L : ℂ) ^ 2 * m := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hpart, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardZc]
  have key : stieltjesN H z - m =
      ((L : ℂ) ^ 2)⁻¹ * ∑ a : Z2 L, (((W : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W a, green H z x x - m) := by
    rw [hsum]
    unfold stieltjesN
    rw [hcardI]
    have htr : (green H z).trace = ∑ x : Idx L W, green H z x x := rfl
    rw [htr]
    field_simp
  rw [key, norm_mul, norm_inv]
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hnorm : ‖((L : ℂ) ^ 2)‖ = (L : ℝ) ^ 2 := by simp
  rw [hnorm]
  calc ((L : ℝ) ^ 2)⁻¹ * ‖∑ a : Z2 L, (((W : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W a, green H z x x - m)‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ∑ _a : Z2 L, B :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => h a))
          (by positivity)
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardZ]
        field_simp

/-! ### 5. The grid -/

/-- The `Δ + 1` equally spaced points of `[a, b]`. -/
private def Step1RegularityA_gridPt (a b : ℝ) (Δ : ℕ) (k : Fin (Δ + 1)) : ℝ :=
  a + (k : ℝ) * ((b - a) / Δ)

private theorem Step1RegularityA_gridPt_mem {a b : ℝ} (hab : a ≤ b) {Δ : ℕ} (hΔ : 0 < Δ)
    (k : Fin (Δ + 1)) :
    a ≤ Step1RegularityA_gridPt a b Δ k ∧ Step1RegularityA_gridPt a b Δ k ≤ b := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hk1 : (k : ℝ) ≤ Δ := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  have hd : 0 ≤ (b - a) / Δ := div_nonneg (by linarith) hΔ'.le
  unfold Step1RegularityA_gridPt
  constructor
  · nlinarith [mul_nonneg hk0 hd]
  · have h1 : (k : ℝ) * ((b - a) / Δ) ≤ Δ * ((b - a) / Δ) :=
      mul_le_mul_of_nonneg_right hk1 hd
    have h2 : (Δ : ℝ) * ((b - a) / Δ) = b - a := by field_simp
    linarith

/-- Nearest grid point. -/
private theorem Step1RegularityA_grid_exists {a b : ℝ} (hab : a ≤ b) {Δ : ℕ} (hΔ : 0 < Δ)
    {x : ℝ} (hxa : a ≤ x) (hxb : x ≤ b) :
    ∃ k : Fin (Δ + 1), |x - Step1RegularityA_gridPt a b Δ k| ≤ (b - a) / Δ := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  rcases eq_or_lt_of_le hab with h | h
  · refine ⟨0, ?_⟩
    have hx : x = a := by linarith
    subst h
    simp [Step1RegularityA_gridPt, hx]
  · have hh : 0 < (b - a) / Δ := div_pos (by linarith) hΔ'
    set h : ℝ := (b - a) / Δ with hh_def
    set r : ℝ := (x - a) / h with hr_def
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hh.le
    have hΔh : (Δ : ℝ) * h = b - a := by rw [hh_def]; field_simp
    have hrΔ : r ≤ Δ := by
      rw [hr_def, div_le_iff₀ hh]
      linarith
    have hk0Δ : ⌊r⌋₊ ≤ Δ := Nat.floor_le_of_le hrΔ
    refine ⟨⟨⌊r⌋₊, by omega⟩, ?_⟩
    have hfl_le : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
    have hfl_lt : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
    have hxr : x - a = r * h := by rw [hr_def]; field_simp
    unfold Step1RegularityA_gridPt
    have hdiff : x - (a + (⌊r⌋₊ : ℝ) * ((b - a) / Δ)) = (r - ⌊r⌋₊) * h := by
      rw [← hh_def]; linarith
    rw [hdiff, abs_of_nonneg (mul_nonneg (by linarith) hh.le)]
    nlinarith

/-- The two-dimensional grid of the domain `locDomain N κ τ`: `Re ∈ [-(2-κ), 2-κ]`,
`Im ∈ [N^{-1+τ}, 1]`. -/
private def Step1RegularityA_zpt (N : ℕ) (κ τ : ℝ) (Δ : ℕ)
    (k : Fin (Δ + 1) × Fin (Δ + 1)) : ℂ :=
  ⟨Step1RegularityA_gridPt (-(2 - κ)) (2 - κ) Δ k.1,
    Step1RegularityA_gridPt ((N : ℝ) ^ (-1 + τ)) 1 Δ k.2⟩

/-- Every point of the domain has a grid point in the domain within `5 / Δ`. -/
private theorem Step1RegularityA_zpt_cover {N : ℕ} {κ τ : ℝ} (hκ : 0 < κ) {Δ : ℕ} (hΔ : 0 < Δ)
    {z : ℂ} (hz : locDomain N κ τ z) :
    ∃ k : Fin (Δ + 1) × Fin (Δ + 1), locDomain N κ τ (Step1RegularityA_zpt N κ τ Δ k) ∧
      ‖z - Step1RegularityA_zpt N κ τ Δ k‖ ≤ 5 / Δ := by
  obtain ⟨hre, hg, h1⟩ := hz
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hR : 0 ≤ 2 - κ := (abs_nonneg _).trans hre
  have hre' := abs_le.1 hre
  have hg1 : (N : ℝ) ^ (-1 + τ) ≤ 1 := hg.trans h1
  have hg0 : 0 ≤ (N : ℝ) ^ (-1 + τ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨k₁, hk₁⟩ := Step1RegularityA_grid_exists (a := -(2 - κ)) (b := 2 - κ) (by linarith) hΔ
    hre'.1 hre'.2
  obtain ⟨k₂, hk₂⟩ := Step1RegularityA_grid_exists (a := (N : ℝ) ^ (-1 + τ)) (b := 1) hg1 hΔ hg h1
  have hm₁ := Step1RegularityA_gridPt_mem (a := -(2 - κ)) (b := 2 - κ) (by linarith) hΔ k₁
  have hm₂ := Step1RegularityA_gridPt_mem (a := (N : ℝ) ^ (-1 + τ)) (b := 1) hg1 hΔ k₂
  refine ⟨(k₁, k₂), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact abs_le.2 ⟨hm₁.1, hm₁.2⟩
  · exact hm₂.1
  · exact hm₂.2
  · have e1 : (2 - κ - -(2 - κ)) / (Δ : ℝ) ≤ 4 / Δ :=
      div_le_div_of_nonneg_right (by linarith) hΔ'.le
    have e2 : (1 - (N : ℝ) ^ (-1 + τ)) / (Δ : ℝ) ≤ 1 / Δ :=
      div_le_div_of_nonneg_right (by linarith) hΔ'.le
    have hre_d : |(z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).re| ≤ 4 / Δ := by
      have : (z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).re =
          z.re - Step1RegularityA_gridPt (-(2 - κ)) (2 - κ) Δ k₁ := rfl
      rw [this]; exact hk₁.trans e1
    have him_d : |(z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).im| ≤ 1 / Δ := by
      have : (z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).im =
          z.im - Step1RegularityA_gridPt ((N : ℝ) ^ (-1 + τ)) 1 Δ k₂ := rfl
      rw [this]; exact hk₂.trans e2
    calc ‖z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)‖
        ≤ |(z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).re| +
          |(z - Step1RegularityA_zpt N κ τ Δ (k₁, k₂)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 4 / Δ + 1 / Δ := add_le_add hre_d him_d
      _ = 5 / Δ := by ring

/-! ### 6. Deterministic interpolation from the grid to the continuum -/

/-- Interpolation from a grid point: if the normalized trace of a Hermitian
matrix is within `W^{τ''} / Meta` of `m_sc` at a point `z'` of the domain, and `τ'' ≤ τ'`, then
it is within `2 W^{τ'} / Meta` of `m_sc` at every point `z` of the domain with
`|z - z'| ≤ N⁻⁴` (`N ≥ 32`, `W² ≤ N`, `Im z, Im z' ≥ N⁻¹`). -/
private theorem Step1RegularityA_compare {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {L W N : ℕ} (hW : 1 ≤ W) (hWN : W ^ 2 ≤ N)
    (hN : 32 ≤ N) {κ τ' τ'' : ℝ} (hκ : 0 < κ) (hτ'' : τ'' ≤ τ') (hτ' : 0 ≤ τ')
    {z z' : ℂ} (hz : (N : ℝ)⁻¹ ≤ z.im) (hz1 : z.im ≤ 1) (hzre : |z.re| ≤ 2 - κ)
    (hz' : (N : ℝ)⁻¹ ≤ z'.im) (hdist : ‖z - z'‖ ≤ ((N : ℝ) ^ 4)⁻¹)
    (hloc : ‖stieltjesN H z' - msc z'‖ ≤ (W : ℝ) ^ τ'' / RBM.Meta L W z') :
    ‖stieltjesN H z - msc z‖ ≤ 2 * (W : ℝ) ^ τ' / RBM.Meta L W z := by
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set ε : ℝ := (N : ℝ)⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.2 hNpos
  have hε32 : ε ≤ 1 / 32 := by
    have : (N : ℝ)⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hN32
    rw [hε]; linarith [this, show ((32 : ℝ)⁻¹) = 1 / 32 by norm_num]
  have hdist' : ‖z - z'‖ ≤ ε ^ 4 := by rw [hε, inv_pow]; exact hdist
  have hη : 0 < z.im := lt_of_lt_of_le hε0 hz
  have hη' : 0 < z'.im := lt_of_lt_of_le hε0 hz'
  -- (i) Lipschitz bound of the normalized trace
  have h1 : ‖stieltjesN H z - stieltjesN H z'‖ ≤ ε ^ 2 := by
    refine (Step1RegularityA_stieltjesN_lip hH hη hη').trans ?_
    rw [div_le_iff₀ (mul_pos hη hη')]
    have h12 : ε * ε ≤ z.im * z'.im := mul_le_mul hz hz' hε0.le hη.le
    calc ‖z - z'‖ ≤ ε ^ 4 := hdist'
      _ = ε ^ 2 * (ε * ε) := by ring
      _ ≤ ε ^ 2 * (z.im * z'.im) := mul_le_mul_of_nonneg_left h12 (by positivity)
  -- (ii) Lipschitz bound of `m_sc`
  have h2 : ‖msc z' - msc z‖ ≤ 16 * ε ^ 3 := by
    refine (Step1RegularityA_msc_lip_domain hκ hη hz1 hzre hη').trans ?_
    rw [div_le_iff₀ hη, norm_sub_rev]
    calc 16 * ‖z - z'‖ ≤ 16 * ε ^ 4 := by linarith
      _ = 16 * ε ^ 3 * ε := by ring
      _ ≤ 16 * ε ^ 3 * z.im := mul_le_mul_of_nonneg_left hz (by positivity)
  -- (iii) the ratio of the control parameters
  set M := RBM.Meta L W z with hM
  set M' := RBM.Meta L W z' with hM'
  have hMpos : 0 < M := Step1RegularityA_Meta_pos L W hW hη
  have hM'pos : 0 < M' := Step1RegularityA_Meta_pos L W hW hη'
  have h3 : 2 * M ≤ 3 * M' := by
    rcases le_or_gt z.im z'.im with hle | hlt
    · have := Step1RegularityA_Meta_mono L W hη hle
      linarith
    · have hr := Step1RegularityA_Meta_ratio L W (z := z) (z' := z') hη' hlt.le
      have hδ : z.im - z'.im ≤ ‖z - z'‖ := by
        have := Complex.abs_im_le_norm (z - z')
        rw [Complex.sub_im] at this
        exact (le_abs_self _).trans this
      have hε3 : ε ^ 3 ≤ (1 / 32) ^ 3 := pow_le_pow_left₀ hε0.le hε32 3
      have hδ' : ‖z - z'‖ ≤ z.im / 3 := by
        calc ‖z - z'‖ ≤ ε ^ 4 := hdist'
          _ = ε * ε ^ 3 := by ring
          _ ≤ ε * (1 / 3) := mul_le_mul_of_nonneg_left (by nlinarith) hε0.le
          _ ≤ z.im / 3 := by linarith
      have h23 : 2 * z.im ≤ 3 * z'.im := by linarith
      have hfin : (2 * M) * z.im ≤ (3 * M') * z.im := by
        nlinarith [mul_le_mul_of_nonneg_left h23 hMpos.le]
      exact le_of_mul_le_mul_right hfin hη
  -- (iv) the size of the threshold
  set P : ℝ := (W : ℝ) ^ τ' with hP
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hP1 : 1 ≤ P := Real.one_le_rpow hW1 hτ'
  have hMle : M ≤ 4 * N := by
    have := Step1RegularityA_Meta_le L W hη hz1
    have h2 : (W : ℝ) ^ 2 ≤ N := by exact_mod_cast hWN
    linarith
  have hPM : ε / 4 ≤ P / M := by
    rw [le_div_iff₀ hMpos]
    calc ε / 4 * M ≤ ε / 4 * (4 * N) := mul_le_mul_of_nonneg_left hMle (by positivity)
      _ = 1 := by rw [hε]; field_simp
      _ ≤ P := hP1
  have hWτ : (W : ℝ) ^ τ'' ≤ P := Real.rpow_le_rpow_of_exponent_le hW1 hτ''
  have h4 : (W : ℝ) ^ τ'' / M' ≤ 3 / 2 * (P / M) := by
    rw [div_le_iff₀ hM'pos]
    have h5 : P / M * M = P := div_mul_cancel₀ P hMpos.ne'
    have h6 : 3 / 2 * (P / M) * ((2 / 3) * M) = P := by
      calc 3 / 2 * (P / M) * ((2 / 3) * M) = P / M * M := by ring
        _ = P := h5
    calc (W : ℝ) ^ τ'' ≤ P := hWτ
      _ = 3 / 2 * (P / M) * ((2 / 3) * M) := h6.symm
      _ ≤ 3 / 2 * (P / M) * M' := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have hsmall : ε ^ 2 + 16 * ε ^ 3 ≤ 1 / 2 * (P / M) := by
    have a1 : ε ^ 2 ≤ ε * (1 / 32) := by
      calc ε ^ 2 = ε * ε := by ring
        _ ≤ ε * (1 / 32) := mul_le_mul_of_nonneg_left hε32 hε0.le
    have a2 : ε ^ 3 ≤ ε * (1 / 32) ^ 2 := by
      calc ε ^ 3 = ε * ε ^ 2 := by ring
        _ ≤ ε * (1 / 32) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε0.le hε32 2) hε0.le
    nlinarith
  calc ‖stieltjesN H z - msc z‖
      = ‖(stieltjesN H z - stieltjesN H z') + (stieltjesN H z' - msc z') +
          (msc z' - msc z)‖ := by congr 1; ring
    _ ≤ ‖stieltjesN H z - stieltjesN H z'‖ + ‖stieltjesN H z' - msc z'‖ +
          ‖msc z' - msc z‖ := norm_add₃_le
    _ ≤ ε ^ 2 + (W : ℝ) ^ τ'' / M' + 16 * ε ^ 3 := by linarith
    _ ≤ 2 * P / M := by
        have : 2 * P / M = 2 * (P / M) := by ring
        rw [this]
        linarith

/-! ### 7. The entry bound -/

/-- If every real coordinate is at most `1/2` in absolute value, every entry has modulus `≤ 1`. -/
private theorem Step1RegularityA_Xentry_le (L W : ℕ) [NeZero L] [NeZero W] (s : Ω L W)
    (hs : ∀ c, |s c| ≤ 1 / 2) (i j : Idx L W) : ‖Xentry L W s i j‖ ≤ 1 := by
  have hn : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  have hn' : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ 1 := by
    intro a b ha hb
    calc ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_sub_le _ _
      _ = |a| + |b| := by simp
      _ ≤ 1 := by linarith
  unfold Xentry
  split_ifs
  · exact hn _ _ (hs _) (hs _)
  · exact hn' _ _ (hs _) (hs _)
  · have := hs (i, j, true)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith

/-- Each real coordinate of the size-`n` slice is sub-Gaussian with variance proxy
`1 / (5 W²)` (`gvar ≤ svar ≤ 1 / (5 W²)`). -/
private theorem Step1RegularityA_subgaussian (d : Sizes) (n : ℕ)
    (c : Coord (d.L n) (d.W n)) :
    HasSubgaussianMGF (fun ω : SeqΩ d => ω ⟨n, c⟩)
      (⟨(5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2, by positivity⟩ : ℝ≥0) (seqP d) := by
  set v : ℝ≥0 := ⟨(5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2, by positivity⟩ with hv
  have hgv : (seqGvar d ⟨n, c⟩ : ℝ) ≤ (5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2 := by
    have h1 : (gvar (d.L n) (d.W n) c : ℝ) ≤ svar (d.L n) (d.W n) c.1 c.2.1 := by
      change (if c.1 = c.2.1 then svar (d.L n) (d.W n) c.1 c.2.1
        else svar (d.L n) (d.W n) c.1 c.2.1 / 2) ≤ _
      split_ifs
      · exact le_rfl
      · linarith [svar_nonneg (d.L n) (d.W n) c.1 c.2.1]
    have h2 : svar (d.L n) (d.W n) c.1 c.2.1 ≤ (5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2 := by
      unfold svar
      split_ifs
      · exact le_rfl
      · positivity
    exact h1.trans h2
  have hmap : (seqP d).map (fun ω : SeqΩ d => ω ⟨n, c⟩) = gaussianReal 0 (seqGvar d ⟨n, c⟩) :=
    seqP_map_eval d ⟨n, c⟩
  have hX : AEMeasurable (fun ω : SeqΩ d => ω ⟨n, c⟩) (seqP d) :=
    (measurable_pi_apply _).aemeasurable
  rw [← HasSubgaussianMGF.id_map_iff hX, hmap]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp only [zero_mul, zero_add]
  apply Real.exp_le_exp.2
  have : (seqGvar d ⟨n, c⟩ : ℝ) ≤ (v : ℝ) := hgv
  nlinarith [sq_nonneg t]

/-- Chernoff bound for one coordinate: `P(|g| ≥ 1/2) ≤ 2 exp(-5 W² / 8)`. -/
private theorem Step1RegularityA_coord_tail (d : Sizes) (n : ℕ) (c : Coord (d.L n) (d.W n)) :
    (seqP d).real ({ω | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω | 1 / 2 ≤ -(ω ⟨n, c⟩)}) ≤
      2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) := by
  have hsg := Step1RegularityA_subgaussian d n c
  have h1 : (seqP d).real {ω | 1 / 2 ≤ ω ⟨n, c⟩} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2))) :=
    hsg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have h2 : (seqP d).real {ω | 1 / 2 ≤ -(ω ⟨n, c⟩)} ≤
      Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2))) :=
    hsg.neg.measure_ge_le (ε := 1 / 2) (by norm_num)
  have hW : (0 : ℝ) < (d.W n : ℝ) := Nat.cast_pos.2 (d.W_pos n)
  have hexp : Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * ((5 : ℝ)⁻¹ * ((d.W n : ℝ)⁻¹) ^ 2))) =
      Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) := by
    congr 1
    field_simp
    ring
  have h1' : (seqP d).real {ω | 1 / 2 ≤ ω ⟨n, c⟩} ≤ Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) := by
    rw [← hexp]; exact h1
  have h2' : (seqP d).real {ω | 1 / 2 ≤ -(ω ⟨n, c⟩)} ≤ Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) := by
    rw [← hexp]; exact h2
  calc (seqP d).real ({ω | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω | 1 / 2 ≤ -(ω ⟨n, c⟩)})
      ≤ (seqP d).real {ω | 1 / 2 ≤ ω ⟨n, c⟩} + (seqP d).real {ω | 1 / 2 ≤ -(ω ⟨n, c⟩)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) := by linarith

/-- The union bound over the `2 N²` real coordinates: some entry exceeds `1` with probability at
most `4 N² exp(-5 W² / 8)`. -/
private theorem Step1RegularityA_entry_bound (d : Sizes) (n : ℕ) :
    seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖seqXmat d n ω x y‖ ≤ 1} ≤
      ENNReal.ofReal (4 * ((d.size n : ℕ) : ℝ) ^ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) := by
  classical
  have hsub : {ω : SeqΩ d | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖seqXmat d n ω x y‖ ≤ 1} ⊆
      ⋃ c : Coord (d.L n) (d.W n),
        ({ω : SeqΩ d | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ d | 1 / 2 ≤ -(ω ⟨n, c⟩)}) := by
    intro ω hω
    by_contra hcon
    apply hω
    intro x y
    have hs : ∀ c, |slice d n ω c| ≤ 1 / 2 := by
      intro c
      by_contra hc
      push Not at hc
      apply hcon
      refine Set.mem_iUnion.2 ⟨c, ?_⟩
      rcases lt_abs.1 hc with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    exact Step1RegularityA_Xentry_le (d.L n) (d.W n) (slice d n ω) hs x y
  have hterm : ∀ c : Coord (d.L n) (d.W n),
      seqP d ({ω : SeqΩ d | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ d | 1 / 2 ≤ -(ω ⟨n, c⟩)}) ≤
        ENNReal.ofReal (2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) := by
    intro c
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
    exact Step1RegularityA_coord_tail d n c
  have hcard : (Fintype.card (Coord (d.L n) (d.W n)) : ℝ) = 2 * ((d.size n : ℕ) : ℝ) ^ 2 := by
    have : Fintype.card (Coord (d.L n) (d.W n)) = 2 * d.size n ^ 2 := by
      have h := RBM.Green.flucAvg_card_Idx_eq_size d n
      change Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) × Bool) = _
      rw [Fintype.card_prod (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n) × Bool),
        Fintype.card_prod (Idx (d.L n) (d.W n)) Bool, Fintype.card_bool, h]
      ring
    rw [this]; push_cast; ring
  calc seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖seqXmat d n ω x y‖ ≤ 1}
      ≤ seqP d (⋃ c : Coord (d.L n) (d.W n),
        ({ω : SeqΩ d | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ d | 1 / 2 ≤ -(ω ⟨n, c⟩)})) :=
        measure_mono hsub
    _ ≤ ∑ c : Coord (d.L n) (d.W n),
        seqP d ({ω : SeqΩ d | 1 / 2 ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ d | 1 / 2 ≤ -(ω ⟨n, c⟩)}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : Coord (d.L n) (d.W n),
        ENNReal.ofReal (2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ENNReal.ofReal (4 * ((d.size n : ℕ) : ℝ) ^ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
        congr 1
        ring

/-! ### 8. The entry bound is eventually polynomially small -/

/-- `4 N² exp(-5 W²/8) ≤ N^{-(D+1)}` eventually, from `W ≥ N^𝔠` and `N → ∞`
(`x^s e^{-b x} → 0`). -/
private theorem Step1RegularityA_entry_eventually {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (d : Sizes)
    (hd : Admissible 𝔠 d) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n in atTop, 4 * ((d.size n : ℕ) : ℝ) ^ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
  obtain ⟨hNt, hbw⟩ := hd
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNt
  have hWt : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hbw ((tendsto_rpow_atTop h𝔠).comp hNtend)
  have hxt : Tendsto (fun n => (d.W n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hWt
  set s : ℝ := (D + 3) / (2 * 𝔠) with hs
  have hs0 : 0 ≤ s := by positivity
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (5 / 8) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ s * Real.exp (-(5 / 8) * x) ≤ 1 / 4 :=
    hdecay.eventually (ge_mem_nhds (by norm_num))
  have hsmall' := hxt.eventually hsmall
  filter_upwards [hsmall', hbw, hNtend.eventually_ge_atTop 1] with n hn hbwn hN1
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := (d.W n : ℝ) with hWdef
  have hNpos : 0 < N := by linarith
  have hN0 : 0 ≤ N := hNpos.le
  -- `N^{2𝔠} ≤ W²`
  have h1 : N ^ (2 * 𝔠) ≤ W ^ 2 := by
    have : N ^ (2 * 𝔠) = (N ^ 𝔠) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hN0, Real.rpow_two]
    rw [this]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hN0 _) hbwn 2
  -- `N^{D+3} ≤ (W²)^s`
  have h2 : N ^ (D + 3) ≤ (W ^ 2) ^ s := by
    have : N ^ (D + 3) = (N ^ (2 * 𝔠)) ^ s := by
      rw [← Real.rpow_mul hN0, hs]
      congr 1
      field_simp
    rw [this]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h1 hs0
  have hexp : Real.exp (-(5 * W ^ 2 / 8)) = Real.exp (-(5 / 8) * W ^ 2) := by
    congr 1; ring
  have h3 : N ^ 2 * N ^ (D + 1) = N ^ (D + 3) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hpos : 0 < N ^ (D + 1) := Real.rpow_pos_of_pos hNpos _
  have h4 : 4 * N ^ 2 * Real.exp (-(5 * W ^ 2 / 8)) * N ^ (D + 1) ≤ 1 := by
    have hE : 0 ≤ Real.exp (-(5 * W ^ 2 / 8)) := (Real.exp_pos _).le
    calc 4 * N ^ 2 * Real.exp (-(5 * W ^ 2 / 8)) * N ^ (D + 1)
        = 4 * (N ^ 2 * N ^ (D + 1)) * Real.exp (-(5 * W ^ 2 / 8)) := by ring
      _ = 4 * N ^ (D + 3) * Real.exp (-(5 * W ^ 2 / 8)) := by rw [h3]
      _ ≤ 4 * (W ^ 2) ^ s * Real.exp (-(5 * W ^ 2 / 8)) := by gcongr
      _ = 4 * ((W ^ 2) ^ s * Real.exp (-(5 / 8) * W ^ 2)) := by rw [hexp]; ring
      _ ≤ 4 * (1 / 4) := by gcongr
      _ = 1 := by norm_num
  rw [Real.rpow_neg hN0, ← one_div]
  exact (le_div_iff₀ hpos).2 h4

/-! ### 9. The event and the theorem -/

/-- **The event of Step 1**: the tracial local law with factor `2` simultaneously for
every `z` in the spectral domain of `locSC`, and every entry at most `1`. -/
def Step1LocalEvent (d : Sizes) (n : ℕ) (κ τ τ' : ℝ) (ω : Sizes.SeqΩ d) : Prop :=
  (∀ z : ℂ, RBM.Endpoints.locDomain (d.size n) κ τ z →
    ‖RBM.Univ.stieltjesN (Sizes.seqXmat d n ω) z - RBM.Endpoints.mSC z‖ ≤
      2 * (d.W n : ℝ) ^ τ' / RBM.Meta (d.L n) (d.W n) z) ∧
  ∀ x y : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n ω x y‖ ≤ 1

private theorem Step1RegularityA_locDomain_mono {N : ℕ} (hN : 1 ≤ N) {κ τ τ'' : ℝ}
    (h : τ'' ≤ τ) {z : ℂ} (hz : locDomain N κ τ z) : locDomain N κ τ'' z :=
  ⟨hz.1, le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith))
    hz.2.1, hz.2.2⟩

private theorem Step1RegularityA_im_ge_inv {N : ℕ} (hN : 1 ≤ N) {κ τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ}
    (hz : locDomain N κ τ z) : (N : ℝ)⁻¹ ≤ z.im := by
  have h : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  rw [Real.rpow_neg_one] at h
  exact h.trans hz.2.1

/-- The deterministic half: on the good grid event and the entry event, `Step1LocalEvent`
holds. -/
private theorem Step1RegularityA_event_of_grid (d : Sizes) (n : ℕ) {κ τ τ' : ℝ} (hκ : 0 < κ)
    (hτ : 0 < τ) (hτ' : 0 < τ') (hN : 72 ≤ d.size n) (ω : SeqΩ d)
    (hent : ∀ x y : Idx (d.L n) (d.W n), ‖seqXmat d n ω x y‖ ≤ 1)
    (hgrid : ∀ k : Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1),
      locDomain (d.size n) κ (min τ τ')
          (Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k) →
        ∀ a : Z2 (d.L n),
          ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a,
              Gn d n ω (Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k) x x -
            mSC (Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k)‖ ≤
            (d.W n : ℝ) ^ (min τ τ') / RBM.Meta (d.L n) (d.W n)
              (Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k)) :
    Step1LocalEvent d n κ τ τ' ω := by
  refine ⟨fun z hz => ?_, hent⟩
  have hN1 : 1 ≤ d.size n := by omega
  have hΔ : 0 < 5 * d.size n ^ 4 := by positivity
  obtain ⟨k, hk, hkd⟩ := Step1RegularityA_zpt_cover (N := d.size n) (κ := κ) (τ := τ)
    hκ hΔ hz
  have hkτ : locDomain (d.size n) κ (min τ τ')
      (Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k) :=
    Step1RegularityA_locDomain_mono hN1 (min_le_left _ _) hk
  have hgk := hgrid k hkτ
  set zk := Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4) k with hzk
  have hNpos : (0 : ℝ) < (d.size n : ℝ) := by exact_mod_cast hN1
  have hzk_im : ((d.size n : ℕ) : ℝ)⁻¹ ≤ zk.im := Step1RegularityA_im_ge_inv hN1 hτ.le hk
  have hz_im : ((d.size n : ℕ) : ℝ)⁻¹ ≤ z.im := Step1RegularityA_im_ge_inv hN1 hτ.le hz
  have hzk0 : 0 < zk.im := lt_of_lt_of_le (inv_pos.2 hNpos) hzk_im
  have hz0 : 0 < z.im := lt_of_lt_of_le (inv_pos.2 hNpos) hz_im
  have hWN : d.W n ^ 2 ≤ d.size n := by
    have h1 : d.size n = d.W n ^ 2 * d.L n ^ 2 := Sizes.size_eq d n
    have hL1 : 1 ≤ d.L n ^ 2 := Nat.one_le_pow _ _ (by have := d.three_le_L n; omega)
    calc d.W n ^ 2 = d.W n ^ 2 * 1 := (mul_one _).symm
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul_left _ hL1
      _ = d.size n := h1.symm
  have hdist : ‖z - zk‖ ≤ (((d.size n : ℕ) : ℝ) ^ 4)⁻¹ := by
    refine hkd.trans (le_of_eq ?_)
    push_cast
    field_simp
  have htr : ‖stieltjesN (seqXmat d n ω) zk - msc zk‖ ≤
      (d.W n : ℝ) ^ (min τ τ') / RBM.Meta (d.L n) (d.W n) zk := by
    rw [← mSC_eq_msc hzk0]
    exact Step1RegularityA_tracial_le (d.L n) (d.W n) (seqXmat d n ω) zk (mSC zk) hgk
  have hcmp := Step1RegularityA_compare (seqXmat_isHermitian d n ω) (L := d.L n) (W := d.W n)
    (N := d.size n) (d.W_pos n) hWN (by omega) hκ (min_le_right τ τ') hτ'.le hz_im hz.2.2 hz.1
    hzk_im hdist htr
  rw [mSC_eq_msc hz0]
  exact hcmp

/-- **The event of Step 1.**  From `locSC`: with probability `≥ 1 - N^{-D}`, eventually, the
tracial local law with factor `2` holds for every `z` in `locDomain N κ τ` and every entry has
modulus at most `1`. -/
theorem step1LocalEvent_highProb :
    RBM.Endpoints.locSC → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, RBM.Endpoints.Admissible 𝔠 d →
      ∀ κ τ τ' D : ℝ, 0 < κ → 0 < τ → 0 < τ' → 0 < D →
        ∀ᶠ n in atTop, Sizes.seqP d {ω | ¬ Step1LocalEvent d n κ τ τ' ω} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  intro hloc 𝔠 h𝔠 d hd κ τ τ' D hκ hτ hτ' hD
  classical
  have hev := hloc 𝔠 h𝔠 d hd κ (min τ τ') (D + 10) hκ (lt_min hτ hτ') (by linarith)
  have hent := Step1RegularityA_entry_eventually h𝔠 d hd hD
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd.1
  filter_upwards [hev, hent, hNtend.eventually_ge_atTop 72] with n hn hentn hN72
  have hNnat : 72 ≤ d.size n := by exact_mod_cast hN72
  have hN1 : 1 ≤ d.size n := by omega
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  -- the grid events
  let zk : Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1) → ℂ :=
    Step1RegularityA_zpt (d.size n) κ τ (5 * d.size n ^ 4)
  let Bad : Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1) → Set (SeqΩ d) := fun k =>
    {ω | locDomain (d.size n) κ (min τ τ') (zk k) ∧ ¬ ∀ a : Z2 (d.L n),
      ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω (zk k) x x - mSC (zk k)‖ ≤
        (d.W n : ℝ) ^ (min τ τ') / RBM.Meta (d.L n) (d.W n) (zk k)}
  let Ent : Set (SeqΩ d) := {ω | ¬ ∀ x y : Idx (d.L n) (d.W n), ‖seqXmat d n ω x y‖ ≤ 1}
  have hsub : {ω : SeqΩ d | ¬ Step1LocalEvent d n κ τ τ' ω} ⊆ (⋃ k, Bad k) ∪ Ent := by
    intro ω hω
    by_contra hcon
    apply hω
    refine Step1RegularityA_event_of_grid d n hκ hτ hτ' hNnat ω ?_ ?_
    · by_contra h
      exact hcon (Or.inr h)
    · intro k hk
      by_contra h
      exact hcon (Or.inl (Set.mem_iUnion.2 ⟨k, hk, h⟩))
  have hBad : ∀ k, seqP d (Bad k) ≤ ENNReal.ofReal (N ^ (-(D + 10))) := by
    intro k
    by_cases hk : locDomain (d.size n) κ (min τ τ') (zk k)
    · refine le_trans (measure_mono ?_) (hn (zk k) hk).2
      intro ω hω
      exact hω.2
    · have h0 : Bad k = ∅ := by
        ext ω
        simp only [Bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hk h.1
      rw [h0, measure_empty]
      exact zero_le
  -- the real numbers
  have hΔR : ((5 * d.size n ^ 4 : ℕ) : ℝ) = 5 * N ^ 4 := by
    rw [hNdef]; push_cast; ring
  have hN4 : (1 : ℝ) ≤ N ^ 4 := one_le_pow₀ (by linarith)
  have hcardR : ((Fintype.card (Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1)) : ℕ) :
      ℝ) = (5 * N ^ 4 + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    rw [hNdef]; ring
  have hc2 : (5 * N ^ 4 + 1) ^ 2 ≤ N ^ 9 := by
    have h1 : 5 * N ^ 4 + 1 ≤ 6 * N ^ 4 := by linarith
    have h2 : (5 * N ^ 4 + 1) ^ 2 ≤ (6 * N ^ 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (6 * N ^ 4) ^ 2 = 36 * N ^ 8 := by ring
    have h4 : 36 * N ^ 8 ≤ N * N ^ 8 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h5 : N * N ^ 8 = N ^ 9 := by ring
    linarith
  have hA : ((Fintype.card (Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1)) : ℕ) : ℝ) *
      N ^ (-(D + 10)) ≤ N ^ (-(D + 1)) := by
    rw [hcardR]
    calc (5 * N ^ 4 + 1) ^ 2 * N ^ (-(D + 10)) ≤ N ^ 9 * N ^ (-(D + 10)) :=
          mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (-(D + 1)) := by
          rw [← Real.rpow_natCast N 9, ← Real.rpow_add hNpos]
          congr 1
          push_cast
          ring
  have hhalf : 2 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
    have h1 : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [h1]
    have hinv : N⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hp : 0 ≤ N ^ (-D) := Real.rpow_nonneg hNpos.le _
    nlinarith
  have hunion : seqP d (⋃ k, Bad k) ≤ ENNReal.ofReal
      (((Fintype.card (Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1)) : ℕ) : ℝ) *
        N ^ (-(D + 10))) := by
    calc seqP d (⋃ k, Bad k) ≤ ∑ k, seqP d (Bad k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Fin (5 * d.size n ^ 4 + 1) × Fin (5 * d.size n ^ 4 + 1),
            ENNReal.ofReal (N ^ (-(D + 10))) := Finset.sum_le_sum fun k _ => hBad k
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hEnt := Step1RegularityA_entry_bound d n
  calc seqP d {ω | ¬ Step1LocalEvent d n κ τ τ' ω}
      ≤ seqP d ((⋃ k, Bad k) ∪ Ent) := measure_mono hsub
    _ ≤ seqP d (⋃ k, Bad k) + seqP d Ent := measure_union_le _ _
    _ ≤ ENNReal.ofReal (((Fintype.card (Fin (5 * d.size n ^ 4 + 1) ×
            Fin (5 * d.size n ^ 4 + 1)) : ℕ) : ℝ) * N ^ (-(D + 10))) +
        ENNReal.ofReal (4 * N ^ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) :=
        add_le_add hunion hEnt
    _ = ENNReal.ofReal (((Fintype.card (Fin (5 * d.size n ^ 4 + 1) ×
            Fin (5 * d.size n ^ 4 + 1)) : ℕ) : ℝ) * N ^ (-(D + 10)) +
        4 * N ^ 2 * Real.exp (-(5 * (d.W n : ℝ) ^ 2 / 8))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal (by linarith)

end RBM.Univ

/-! ## Compiled instance -/
