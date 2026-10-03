/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM2D.Gauss.SpectralAlgebra

/-!
# The semicircle Stieltjes transform and the reparametrisation `zztE`

`msc z` is the root of `m² + z m + 1 = 0` with positive imaginary part (for `Im z > 0`);
the paper defines `m_sc(z)` by an integral (Section 2.1), and the agreement of the two
definitions is proved in `Defs/SemicircleIntegral.lean`.  `lemE`, `lemT` are the energy `E` and
time `t` of the reparametrisation `zztE`, and `ellz`, `Meta` are `ℓ(z)` (`def_ellz`) and
`M_η = W²ℓ²η` (`def_meta`).  The uniqueness lemma for the root of `m(m + E) = -1` with positive
imaginary part is `semicircle_eq_spectralM`.
-/

namespace RBM

open Complex RBM.Gauss

/-- A square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

private theorem semicircle_mscDisc_sq (z : ℂ) : mscDisc z ^ 2 = z ^ 2 - 4 :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

/-- The two roots of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform of the semicircle law: the root of `m² + z m + 1 = 0` with
positive imaginary part (for `Im z > 0`). -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z

theorem msc_mul (z : ℂ) : msc z * (msc z + z) = -1 := by
  have hd := semicircle_mscDisc_sq z
  unfold msc mscRoot₁ mscRoot₂
  split_ifs <;> linear_combination (1 / 4 : ℂ) * hd

theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  have hd := semicircle_mscDisc_sq z
  unfold msc
  split_ifs with h
  · exact h
  · push Not at h
    set r₁ := mscRoot₁ z
    set r₂ := mscRoot₂ z
    have hmul : r₁ * r₂ = 1 := by
      simp only [r₁, r₂, mscRoot₁, mscRoot₂]
      linear_combination (-1 / 4 : ℂ) * hd
    have hsum : r₁.im + r₂.im = -z.im := by
      have : r₁ + r₂ = -z := by simp only [r₁, r₂, mscRoot₁, mscRoot₂]; ring
      simpa using congrArg Complex.im this
    have hr₁ : r₁ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hr₂ : r₂ = r₁⁻¹ := eq_inv_of_mul_eq_one_right hmul
    have hN : 0 < Complex.normSq r₁ := Complex.normSq_pos.mpr hr₁
    have him : r₂.im * Complex.normSq r₁ = -r₁.im := by
      rw [hr₂, Complex.inv_im]
      field_simp
    by_contra hneg
    push Not at hneg
    have h1 : r₂.im * Complex.normSq r₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hN.le
    have h2 : r₁.im = 0 := by linarith
    have h3 : r₂.im < 0 := by linarith
    have h4 : r₂.im * Complex.normSq r₁ < 0 := mul_neg_of_neg_of_pos h3 hN
    linarith

/-- `|m_sc(z)| < 1` for `Im z > 0`. -/
theorem norm_msc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ < 1 := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  set m := msc z
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  have hinv : m + z = -m⁻¹ := by
    field_simp
    linear_combination hm
  have hN : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm0
  have key : (m.im + z.im) * Complex.normSq m = m.im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  have hN1 : Complex.normSq m < 1 := by nlinarith
  have h2 : ‖m‖ ^ 2 < 1 := by rwa [Complex.sq_norm]
  have := norm_nonneg m
  nlinarith

/-- The energy of `zztE`: `E = -2 Re m_sc(z) / |m_sc(z)|`. -/
noncomputable def lemE (z : ℂ) : ℝ := -2 * (msc z).re / ‖msc z‖

/-- The time of `zztE`: `t = |m_sc(z)|²`. -/
noncomputable def lemT (z : ℂ) : ℝ := ‖msc z‖ ^ 2

/-- Uniqueness: `spectralM E` is the only root of `m(m + E) = -1` with `Im m > 0`. -/
private theorem semicircle_eq_spectralM {E : ℝ} (hE : |E| < 2) {m : ℂ}
    (hm : m * (m + E) = -1) (him : 0 < m.im) : m = spectralM E := by
  have h0 := spectralM_mul hE.le
  have h : (m - spectralM E) * (m + spectralM E + E) = 0 := by linear_combination hm - h0
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have him' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him'
    have := spectralM_im_pos hE
    linarith

private theorem semicircle_norm_msc_pos {z : ℂ} (hz : 0 < z.im) : 0 < ‖msc z‖ :=
  norm_pos_iff.mpr fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

private theorem semicircle_lemT_pos {z : ℂ} (hz : 0 < z.im) : 0 < lemT z := by
  have := semicircle_norm_msc_pos hz
  unfold lemT
  positivity

private theorem semicircle_lemT_lt_one {z : ℂ} (hz : 0 < z.im) : lemT z < 1 := by
  have := norm_msc_lt_one hz
  have := norm_nonneg (msc z)
  unfold lemT
  nlinarith

/-- Real and imaginary parts of `u = m_sc(z)/|m_sc(z)|`, and `|u| = 1`. -/
private theorem semicircle_msc_div_norm_facts {z : ℂ} (hz : 0 < z.im) :
    let r := ‖msc z‖
    ((msc z / r).re ^ 2 + (msc z / r).im ^ 2 = 1) ∧ 0 < (msc z / r).im := by
  intro r
  have hr : 0 < r := semicircle_norm_msc_pos hz
  have hr2 : r ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    simp only [r, Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im]
  refine ⟨?_, div_pos (msc_im_pos hz) hr⟩
  field_simp
  linarith

private theorem semicircle_abs_lemE_lt_two {z : ℂ} (hz : 0 < z.im) : |lemE z| < 2 := by
  obtain ⟨h1, h2⟩ := semicircle_msc_div_norm_facts hz
  have hre : lemE z = -2 * (msc z / (‖msc z‖ : ℂ)).re := by
    rw [lemE, Complex.div_ofReal_re]
    ring
  rw [hre, abs_lt]
  constructor <;> nlinarith

/-- The key step of `zztE`: `spectralM E = m_sc(z) / |m_sc(z)|`. -/
private theorem semicircle_spectralM_lemE {z : ℂ} (hz : 0 < z.im) :
    spectralM (lemE z) = msc z / (‖msc z‖ : ℂ) := by
  obtain ⟨h1, h2⟩ := semicircle_msc_div_norm_facts hz
  symm
  refine semicircle_eq_spectralM (semicircle_abs_lemE_lt_two hz) ?_ h2
  set u := msc z / (‖msc z‖ : ℂ) with hu
  have hre : lemE z = -2 * u.re := by
    rw [lemE, hu, Complex.div_ofReal_re]
    ring
  rw [hre]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_re, Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_im, Complex.one_im]
    ring

/-- `mtEmz`: `m_sc(z) = t^{1/2} m^{(E)}`. -/
theorem msc_eq_sqrt_mul_spectralM {z : ℂ} (hz : 0 < z.im) :
    msc z = (Real.sqrt (lemT z) : ℂ) * spectralM (lemE z) := by
  have hr : (‖msc z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (semicircle_norm_msc_pos hz).ne'
  rw [semicircle_spectralM_lemE hz, lemT, Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- `eq:zztE`: `z = t^{-1/2} z_t^{(E)}`. -/
theorem eq_inv_sqrt_mul_spectralZ {z : ℂ} (hz : 0 < z.im) :
    z = (Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z) := by
  set r := ‖msc z‖ with hr_def
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (semicircle_norm_msc_pos hz).ne'
  set u := spectralM (lemE z) with hu_def
  set E := lemE z
  have hu : u * (u + E) = -1 := spectralM_mul (semicircle_abs_lemE_lt_two hz).le
  have hmu : msc z = r * u := by
    rw [hu_def, semicircle_spectralM_lemE hz, ← hr_def]
    field_simp
  have hm := msc_mul z
  rw [hmu] at hm
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hsqrt : Real.sqrt (lemT z) = r := by rw [lemT, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, spectralZ, lemT, ← hr_def]
  push_cast
  have key : (z * r - (E + (1 - r ^ 2) * u)) * u = 0 := by
    linear_combination hm - hu
  have h2 : z * r = E + (1 - r ^ 2) * u := by
    have := (mul_eq_zero.mp key).resolve_right hu0
    linear_combination this
  field_simp
  linear_combination h2

/-- `m_sc(z) + z = -m_sc(z)⁻¹`. -/
private theorem semicircle_msc_add_eq_neg_inv {z : ℂ} (hz : 0 < z.im) :
    msc z + z = -(msc z)⁻¹ := by
  have hm0 : msc z ≠ 0 := norm_pos_iff.mp (semicircle_norm_msc_pos hz)
  field_simp
  linear_combination msc_mul z

/-- `|E| ≤ |Re z|`: the energy of `zztE` is no closer to the edge than `Re z`. -/
private theorem semicircle_abs_lemE_le {z : ℂ} (hz : 0 < z.im) : |lemE z| ≤ |z.re| := by
  set m := msc z
  set r := ‖m‖ with hr_def
  have hr : 0 < r := semicircle_norm_msc_pos hz
  have hN : Complex.normSq m = r ^ 2 := by rw [hr_def, Complex.sq_norm]
  have hre : m.re + z.re = -(m.re / r ^ 2) := by
    have := congrArg Complex.re (semicircle_msc_add_eq_neg_inv hz)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at this
    have h' : m.re + z.re = -(m.re / Complex.normSq m) := this
    rwa [hN] at h'
  have hzre : z.re = -m.re * (r ^ 2 + 1) / r ^ 2 := by
    have hc : m.re / r ^ 2 * r ^ 2 = m.re := div_mul_cancel₀ _ (by positivity)
    rw [eq_div_iff (by positivity)]
    linear_combination r ^ 2 * hre - hc
  have e : lemE z = -2 * m.re / r := rfl
  rw [e, hzre, abs_div, abs_div, abs_mul, abs_mul, abs_neg, abs_neg, abs_of_pos hr,
    abs_of_pos (by positivity : (0 : ℝ) < r ^ 2 + 1), abs_of_pos (by positivity : (0 : ℝ) < r ^ 2),
    abs_two, div_le_div_iff₀ hr (by positivity)]
  have := abs_nonneg m.re
  nlinarith [mul_nonneg this (sq_nonneg (r - 1))]

/-- `t ≥ (1 + |z|)⁻²`. -/
private theorem semicircle_lemT_ge {z : ℂ} (hz : 0 < z.im) : ((1 + ‖z‖) ^ 2)⁻¹ ≤ lemT z := by
  have hr : 0 < ‖msc z‖ := semicircle_norm_msc_pos hz
  have hinv : ‖msc z‖⁻¹ ≤ ‖msc z‖ + ‖z‖ := by
    rw [← norm_inv, ← norm_neg, ← semicircle_msc_add_eq_neg_inv hz]
    exact norm_add_le _ _
  have h1 : 1 ≤ ‖msc z‖ * (1 + ‖z‖) := by
    have h := norm_msc_lt_one hz
    have := (inv_le_iff_one_le_mul₀' hr).1 (hinv.trans (by linarith : ‖msc z‖ + ‖z‖ ≤ 1 + ‖z‖))
    linarith
  rw [lemT, inv_le_iff_one_le_mul₀ (by positivity)]
  nlinarith [norm_nonneg z]

/-- `eq:zztE` read on imaginary parts: `Im z_t = t^{1/2} Im z`. -/
private theorem semicircle_spectralZ_im_lemT {z : ℂ} (hz : 0 < z.im) :
    (spectralZ (lemE z) (lemT z)).im = Real.sqrt (lemT z) * z.im := by
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (semicircle_lemT_pos hz)).ne'
  have h := eq_inv_sqrt_mul_spectralZ hz
  have e : spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z :=
    calc spectralZ (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) *
            ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = _ := by rw [← h]
  rw [e]
  simp [Complex.mul_im]

/-- `eq:zztE2`: for `0 < Im z ≤ 1` and `|Re z| ≤ 2 - κ`, `|E| ≤ 2 - κ` and, with
`c_κ = 1/16`, `t ≥ c_κ` and `c_κ Im z ≤ Im z_t ≤ c_κ⁻¹ Im z`. -/
theorem zztE_quant {z : ℂ} {κ : ℝ} (hκ0 : 0 < κ) (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hκ : |z.re| ≤ 2 - κ) :
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧
      (1 / 16 : ℝ) * z.im ≤ (spectralZ (lemE z) (lemT z)).im ∧
      (spectralZ (lemE z) (lemT z)).im ≤ (1 / 16 : ℝ)⁻¹ * z.im := by
  have hnorm : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz0] at this
    linarith
  have ht : (1 / 16 : ℝ) ≤ lemT z := by
    refine le_trans ?_ (semicircle_lemT_ge hz0)
    rw [one_div]
    exact inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.mpr (semicircle_lemT_lt_one hz0).le
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  refine ⟨(semicircle_abs_lemE_le hz0).trans hκ, ht, ?_, ?_⟩ <;>
    rw [semicircle_spectralZ_im_lemT hz0] <;> nlinarith

/-- `ℓ(z) = min(η^{-1/2}, L) + 1`, `η = Im z` (`def_ellz`). -/
noncomputable def ellz (L : ℕ) (z : ℂ) : ℝ :=
  min (z.im ^ (-(1 / 2 : ℝ))) (L : ℝ) + 1

/-- `M_η = W² ℓ(z)² η` (`def_meta`, `d = 2`). -/
noncomputable def Meta (L W : ℕ) (z : ℂ) : ℝ :=
  (W : ℝ) ^ 2 * ellz L z ^ 2 * z.im

end RBM
