/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodSet
import RBM2D.Path.TailSums
import RBM2D.Loop.KBoundCut
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `lem_dec_calE`, first part: the loss, the hypothesis bundle, the `LK×LK` bound

The three declarations `lossE2`, `E2Hyp`, `LemDecCalE_lk`; `E2Hyp` refers to the good set
`goodSet`.

Results (namespace `RBM.Path`):
* `lemDecCalE_lk : LemDecCalE_lk`, the `𝓔^{LK×LK}` bound `res_deccalE_lk` with the explicit
  constant `6800 ≤ lossE2`;
* the shared facts (e1)–(e10), public with the prefix `LemDecCalE_`, that the other bounds of
  `lem_dec_calE` reuse (the constants of (e7), (e8) are computed for the `5 × 5 = 25` neighbour
  pairs of `Z_L²`; (e9) uses the deterministic control `ρ² M_u^{-1}` of the good set).

Paper: arXiv:2503.07606, `res_deccalE_lk` and its proof, `mmxiaoxi`, `def_ELKLK`, `def_WTuD`,
(`GijGEX`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-! ## 0. The statements -/

section LemDecCalE

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The explicit loss of the deterministic bounds of `lem_dec_calE` (it replaces the `≺` of the
paper):
`10¹² K₀² Λ⁶ (1 + log(L²W¹²))⁴ (1 + log W)³ exp(8 (log W)^{3/4})`. -/
def lossE2 (Λ K₀ : ℝ) : ℝ :=
  10 ^ 12 * K₀ ^ 2 * Λ ^ 6 * (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 *
    (1 + Real.log W) ^ 3 * Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4))

/-- The hypotheses of the deterministic bounds of `lem_dec_calE` at `s ≤ u ≤ v` (as numeric
conditions): `M ∈ G(u)` at level `Λ`; `J*_{u,D} ≤ W`; the `𝒦` bound with constant `K₀`
(`KpmBoundProp5`); (`Kell*`) for `𝒦` beyond `ℓ*_u/8` (`KellStarEv`); the floor condition
`L² W¹² ≤ W^{D/2}`; `W ≥ e⁴`; `M_v ≥ 1`. -/
def E2Hyp (E s u v D Λ K₀ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  3 ≤ L ∧ |E| < 2 ∧ 0 ≤ s ∧ s ≤ u ∧ u ≤ v ∧ v < 1 ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧ 4 ≤ Real.log W ∧
    (L : ℝ) ^ 2 * (W : ℝ) ^ 12 ≤ (W : ℝ) ^ (D / 2) ∧ 1 ≤ scaleM L W E v ∧
    M ∈ goodSet L W E s u Λ ∧ jStarMat L W E D u M ≤ W ∧
    (∀ a b : Z2 L, ‖Kpm L W E u a b‖ ≤ K₀ * (scaleM L W E u)⁻¹) ∧
    (∀ a b : Z2 L, ellStar L W u / 8 ≤ (zdist2 L (a - b) : ℝ) → ‖Kpm L W E u a b‖ ≤ (W : ℝ) ^ (-D))

end LemDecCalE

/-- **The `𝓔^{LK×LK}` bound (`res_deccalE_lk`)** at a general endpoint `v`:
`‖𝓔^{LK×LK}_{u,a}‖ ≤ loss · η_u^{-1} M_u^{-1} (J*)² · 𝒯_{v,D}(|a₁-a₂|)`. -/
def LemDecCalE_lk : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E s u v D Λ K₀ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ),
    E2Hyp L W E s u v D Λ K₀ M → ∀ a₁ a₂ : Z2 L,
      ‖ELKLK L W E u M a₁ a₂‖ ≤ lossE2 L W Λ K₀ *
        ((etaT E u)⁻¹ * (scaleM L W E u)⁻¹ * jStarMat L W E D u M ^ 2) *
          tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ)


/-! ## 1. Unpacking `E2Hyp` and the scale facts (e1)–(e3) -/

section Scales

/-- (e1): `W² ℓ_u² = M_u / η_u` (`M_u = W² ℓ_u² η_u`, `scaleM`, and `η_u > 0`). -/
theorem LemDecCalE_e1 {L W : ℕ} {E u : ℝ} (hE : |E| < 2) (hu : u < 1) :
    (W : ℝ) ^ 2 * ellT L u ^ 2 = scaleM L W E u / etaT E u := by
  have h := (etaT_pos hE hu).ne'
  unfold scaleM
  field_simp

/-- `M_u ≤ W²` for `1 ≤ L`, `|E| < 2`, `u < 1` (`M_u = W² Im m min(1, L²(1-u))`, `Im m ≤ 1`);
public copy of the `private` `scaleM_le_sq` of `RBM2D/Path/TailSums.lean`. -/
theorem LemDecCalE_scaleM_le_sq {L W : ℕ} {E u : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hu : u < 1) :
    scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  have him0 := spectralM_im_pos hE
  have him : (spectralM E).im ≤ 1 := by
    rw [spectralM_im, div_le_one (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have hx : 0 < 1 - u := by linarith
  have hmin0 : 0 ≤ min 1 ((L : ℝ) ^ 2 * (1 - u)) := le_min zero_le_one (by positivity)
  have hmin : min 1 ((L : ℝ) ^ 2 * (1 - u)) ≤ 1 := min_le_left _ _
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  rw [scaleM_eq hL hu]
  calc (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u))
      ≤ (W : ℝ) ^ 2 * 1 * 1 := by gcongr
    _ = (W : ℝ) ^ 2 := by ring

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem one_le_L : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)

private theorem one_le_W : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)

/-- (e2): under `E2Hyp`, `1 ≤ M_v ≤ M_u ≤ W²`. -/
theorem LemDecCalE_e2 (h : E2Hyp L W E s u v D Λ K₀ M) :
    1 ≤ scaleM L W E v ∧ scaleM L W E v ≤ scaleM L W E u ∧ scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  exact ⟨hMv, (scaleM_anti_ratio (W := W) one_le_L hE huv hv1).1,
    LemDecCalE_scaleM_le_sq one_le_L hE (huv.trans_lt hv1)⟩

/-- (e3) (i), and the floor conditions of `ConvTailT`, `ConvSqrtTailT`: under `E2Hyp`,
`D > 24`, `L² ≤ W^{D-4}` and `L² ≤ W^{D/2-2}`; also `1 < W`. -/
theorem LemDecCalE_floor (h : E2Hyp L W E s u v D Λ K₀ M) :
    (1 : ℝ) < W ∧ 24 < D ∧ (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (D - 4) ∧
      (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (D / 2 - 2) := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hW1 : (1 : ℝ) < W := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_lt.1 hcon)
    linarith
  have hL9 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL3
    nlinarith
  have h12 : (0 : ℝ) < (W : ℝ) ^ 12 := by positivity
  have hD : 24 < D := by
    have h1 : (W : ℝ) ^ (12 : ℝ) < (W : ℝ) ^ (D / 2) := by
      have : (W : ℝ) ^ (12 : ℝ) = (W : ℝ) ^ 12 := by
        rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [this]
      nlinarith
    have := (Real.rpow_lt_rpow_left_iff hW1).1 h1
    linarith
  have hsub : (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (D / 2 - 12) := by
    have h12' : (W : ℝ) ^ (D / 2 - 12) = (W : ℝ) ^ (D / 2) / (W : ℝ) ^ 12 := by
      rw [Real.rpow_sub hW0, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h12', le_div_iff₀ h12]
    exact hfloor
  refine ⟨hW1, hD, hsub.trans (Real.rpow_le_rpow_of_exponent_le hW1.le (by linarith)),
    hsub.trans (Real.rpow_le_rpow_of_exponent_le hW1.le (by linarith))⟩

end Scales

/-! ## 2. The tail `𝒯_{u,D}`: (e3) (ii)–(iii), (e4) -/

section Tails

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0` (a copy of the `private` `sqrt_add_le_add_sqrt'` in
`RBM2D/Path/TailSums.lean`). -/
private theorem sqrt_add_le_add_sqrt'' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

/-- (e4) (a): `𝒯_{u,D}` is non-increasing in its argument (`1 ≤ L`, `u < 1`). -/
theorem LemDecCalE_tailT_anti {L W : ℕ} {E D u : ℝ} (hL : 1 ≤ L) (hu : u < 1) {x y : ℝ}
    (hxy : x ≤ y) : tailT L W E D u y ≤ tailT L W E D u x := by
  unfold tailT
  have hℓ := (ellT_pos_le hL hu).1
  have h1 : Real.sqrt (x / ellT L u) ≤ Real.sqrt (y / ellT L u) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hxy hℓ.le)
  have h2 : Real.exp (-Real.sqrt (y / ellT L u)) ≤ Real.exp (-Real.sqrt (x / ellT L u)) :=
    Real.exp_le_exp.2 (by linarith)
  have hA : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left h2 hA
  linarith

/-- (e4) (b): `𝒯_{u,D}(x - c) ≤ exp(√c) 𝒯_{u,D}(x)` for `c ≥ 0` and every real `x`
(`0 ≤ u < 1`, `1 ≤ L`; `√(c/ℓ_u) ≤ √c` as `ℓ_u ≥ 1`).  With `c = 1` the factor is `e`.
The proof is adapted from that of `tellStar` in `RBM2D/Path/TailSums.lean`. -/
theorem LemDecCalE_tailT_shift {L W : ℕ} {E D u : ℝ} (hL : 1 ≤ L) (hu0 : 0 ≤ u) (hu : u < 1)
    {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    tailT L W E D u (x - c) ≤ Real.exp (Real.sqrt c) * tailT L W E D u x := by
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hL hu0 hu
  have hℓ : 0 < ellT L u := by linarith
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  have hsplit : x / ellT L u = (x - c) / ellT L u + c / ellT L u := by
    field_simp; ring
  have hc' : 0 ≤ c / ellT L u := div_nonneg hc hℓ.le
  have hkey : Real.sqrt (x / ellT L u) ≤ Real.sqrt ((x - c) / ellT L u) + Real.sqrt c := by
    have h := sqrt_add_le_add_sqrt'' (x := max ((x - c) / ellT L u) 0) (y := c / ellT L u)
      (le_max_right _ _) hc'
    have h1 : Real.sqrt (x / ellT L u) ≤
        Real.sqrt (max ((x - c) / ellT L u) 0 + c / ellT L u) := by
      apply Real.sqrt_le_sqrt
      rw [hsplit]
      linarith [le_max_left ((x - c) / ellT L u) 0]
    have h2 : Real.sqrt (max ((x - c) / ellT L u) 0) = Real.sqrt ((x - c) / ellT L u) := by
      rcases le_total ((x - c) / ellT L u) 0 with h | h
      · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
      · rw [max_eq_left h]
    have h3 : Real.sqrt (c / ellT L u) ≤ Real.sqrt c :=
      Real.sqrt_le_sqrt (div_le_self hc hℓ1)
    linarith
  have hexp : Real.exp (-Real.sqrt ((x - c) / ellT L u)) ≤
      Real.exp (Real.sqrt c) * Real.exp (-Real.sqrt (x / ellT L u)) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have h1 : 1 ≤ Real.exp (Real.sqrt c) := Real.one_le_exp (Real.sqrt_nonneg _)
  have hA : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := by positivity
  unfold tailT
  have := mul_le_mul_of_nonneg_left hexp hA
  nlinarith

/-- (e4) (c): `Tell*` at the scale `v`, used unchanged: for `C ≥ 0`,
`𝒯_{v,D}(x - C ℓ*_v) ≤ exp(√C (log W)^{3/4}) 𝒯_{v,D}(x)` (this is `tellStar`). -/
theorem LemDecCalE_e4c {L W : ℕ} [NeZero L] [NeZero W] {E D v C : ℝ} (hv : v < 1) (hC : 0 ≤ C)
    (x : ℝ) : tailT L W E D v (x - C * ellStar L W v) ≤
      Real.exp (Real.sqrt C * Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D v x :=
  tellStar L W E D v C x hv hC

/-- (e3) (ii): `𝒯_{u,D}(x) ≤ 𝒯_{v,D}(x)` for `x ≥ 0`, `0 ≤ u ≤ v < 1`
(`M_v ≤ M_u`, `scaleM_anti_ratio`; `ℓ_u ≤ ℓ_v`, `ellT_mono_ratio`; `M_v > 0`). -/
theorem LemDecCalE_tailT_mono_scale {L W : ℕ} {E D u v : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) {x : ℝ} (hx : 0 ≤ x) :
    tailT L W E D u x ≤ tailT L W E D v x := by
  have hu : u < 1 := huv.trans_lt hv
  have hMv : 0 < scaleM L W E v := scaleM_pos hL hW hE hv
  have hMle : scaleM L W E v ≤ scaleM L W E u := (scaleM_anti_ratio (W := W) hL hE huv hv).1
  have hℓ := (ellT_mono_ratio hL hu0 huv hv).1
  have hℓu := (ellT_pos_le hL hu).1
  have hA : (scaleM L W E u ^ 2)⁻¹ ≤ (scaleM L W E v ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hMv.le hMle 2)
  have hs : Real.sqrt (x / ellT L v) ≤ Real.sqrt (x / ellT L u) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hx hℓu hℓ)
  have he : Real.exp (-Real.sqrt (x / ellT L u)) ≤ Real.exp (-Real.sqrt (x / ellT L v)) :=
    Real.exp_le_exp.2 (by linarith)
  unfold tailT
  have h1 : (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L u)) ≤
      (scaleM L W E v ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L v)) :=
    mul_le_mul hA he (Real.exp_pos _).le (by positivity)
  linarith

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- (e3) (iii): under `E2Hyp`, `𝒯_{u,D}(x) ≤ 2 M_u⁻²` for every real `x`
(`W^{-D} ≤ W^{-4} ≤ M_u⁻²` by (e2) and `D > 24`). -/
theorem LemDecCalE_tailT_le_two_inv_sq (h : E2Hyp L W E s u v D Λ K₀ M) (x : ℝ) :
    tailT L W E D u x ≤ 2 * (scaleM L W E u ^ 2)⁻¹ := by
  obtain ⟨hW1, hD, -, -⟩ := LemDecCalE_floor h
  have h2 := LemDecCalE_e2 h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hW0 : (0 : ℝ) < W := by linarith
  have hM : 0 < scaleM L W E u := by linarith [h2.1, h2.2.1]
  have hWD : (W : ℝ) ^ (-D) ≤ (scaleM L W E u ^ 2)⁻¹ := by
    have h1 : (W : ℝ) ^ (-D) ≤ (W : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hW1.le (by linarith)
    have h2' : (W : ℝ) ^ (-(4 : ℝ)) = (((W : ℝ) ^ 2) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hW0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      congr 1; ring
    have h3 : (((W : ℝ) ^ 2) ^ 2)⁻¹ ≤ (scaleM L W E u ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hM.le h2.2.2 2)
    rw [h2'] at h1
    exact h1.trans h3
  unfold tailT
  have hexp : Real.exp (-Real.sqrt (x / ellT L u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simp
  have hA : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hexp hA
  linarith

end Tails

/-! ## 3. (e5) and `lemDecCalE_lk` -/

section LK

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- (e5), first part: `|(𝓛 - 𝒦)_{ab}| = ‖lkMat a b‖ ≤ J*_{u,D} 𝒯_{u,D}(|a - b|_L)` for `1 ≤ W`
(`lkErrMat_le_jStarMat_mul_tailT`). -/
theorem LemDecCalE_lkMat_le (E D u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    ‖lkMat L W E u M a b‖ ≤
      jStarMat L W E D u M * tailT L W E D u (zdist2 L (a - b) : ℝ) :=
  lkErrMat_le_jStarMat_mul_tailT L W one_le_W E D u M a b

/-- (e5), second part: under `E2Hyp`, `|𝓛_{(+,-),(a,b)}| ≤ K₀ M_u⁻¹ + 2 J M_u⁻²`
(`𝓛 = (𝓛 - 𝒦) + 𝒦`, conjunct 14, and (e3) (iii)). -/
theorem LemDecCalE_loopPM_le (h : E2Hyp L W E s u v D Λ K₀ M) (a b : Z2 L) :
    ‖loopPM L W E u M a b‖ ≤
      K₀ * (scaleM L W E u)⁻¹ + 2 * jStarMat L W E D u M * (scaleM L W E u ^ 2)⁻¹ := by
  have hT := LemDecCalE_tailT_le_two_inv_sq h (zdist2 L (a - b) : ℝ)
  have hJ0 : 0 ≤ jStarMat L W E D u M := by
    linarith [one_le_jStarMat L W one_le_W E D u M]
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have h1 := LemDecCalE_lkMat_le E D u M a b
  have h2 := hK14 a b
  have h3 : loopPM L W E u M a b = lkMat L W E u M a b + Kpm L W E u a b := by
    unfold lkMat; ring
  rw [h3]
  have h4 := norm_add_le (lkMat L W E u M a b) (Kpm L W E u a b)
  have h5 := mul_le_mul_of_nonneg_left hT hJ0
  linarith

/-- The loss absorbs the constant of `lemDecCalE_lk`: `6800 ≤ lossE2 L W Λ K₀` under `E2Hyp`
(`lossE2 ≥ 10¹² · 5³ = 1.25 · 10¹⁴`, using `K₀, Λ ≥ 1`, `log(L²W¹²) ≥ 0`, `log W ≥ 4`). -/
theorem LemDecCalE_six_thousand_le_lossE2 (h : E2Hyp L W E s u v D Λ K₀ M) :
    (6800 : ℝ) ≤ lossE2 L W Λ K₀ := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast one_le_L
  have hW1 : (1 : ℝ) ≤ W := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_le.1 hcon).le
    linarith
  have hbase : (1 : ℝ) ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ 12 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL0) (one_le_pow₀ hW1)
  have hA : (1 : ℝ) ≤ (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_nonneg hbase])
  have hB : (125 : ℝ) ≤ (1 + Real.log W) ^ 3 := by
    have : (5 : ℝ) ≤ 1 + Real.log W := by linarith
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (1 + Real.log W) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have hX : (1 : ℝ) ≤ Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log W) ((3 : ℝ) / 4)
      linarith)
  have hP : (1 : ℝ) ≤ K₀ ^ 2 * Λ ^ 6 * (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 *
      Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) (one_le_pow₀ hΛ)) hA) hX
  unfold lossE2
  have hrw : (10 : ℝ) ^ 12 * K₀ ^ 2 * Λ ^ 6 *
      (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 * (1 + Real.log W) ^ 3 *
        Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) =
      10 ^ 12 * (1 + Real.log W) ^ 3 * (K₀ ^ 2 * Λ ^ 6 *
        (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 *
          Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4))) := by ring
  rw [hrw]
  have h1 : (10 : ℝ) ^ 12 * 125 ≤ 10 ^ 12 * (1 + Real.log W) ^ 3 :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  have h2 : (10 : ℝ) ^ 12 * 125 * 1 ≤ 10 ^ 12 * (1 + Real.log W) ^ 3 * (K₀ ^ 2 * Λ ^ 6 *
        (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 *
          Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4))) :=
    mul_le_mul h1 hP (by norm_num) (by nlinarith)
  linarith

/-- **`lemDecCalE_lk`** (`res_deccalE_lk`).
Proof: `‖𝓔^{LK×LK}(a₁,a₂)‖ ≤ W² Σ_{b₁,b₂} J² 𝒯_u(|a₁-b₁|) |S_{b₁b₂}| 𝒯_u(|b₂-a₂|)`
by (e5); `S` is supported on `|b₁-b₂|_L ≤ 1` with `Σ_{b₂} |S_{b₁b₂}| = 1`, so the shift (e4) with
`c = 1` gives the factor `e`; `convTailT` gives `2500 ℓ_u² M_u⁻²`; (e1), (e3) turn this into
`2500 e · η_u⁻¹ M_u⁻¹ J² 𝒯_v ≤ 6800 · η_u⁻¹ M_u⁻¹ J² 𝒯_v ≤ lossE2 · …`. -/
theorem lemDecCalE_lk : LemDecCalE_lk := by
  intro L W _ _ E s u v D Λ K₀ M h a₁ a₂
  obtain ⟨hW1, hD, hfloorC, -⟩ := LemDecCalE_floor h
  have hloss := LemDecCalE_six_thousand_le_lossE2 h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hJ1 : 1 ≤ jStarMat L W E D u M := one_le_jStarMat L W one_le_W E D u M
  set J := jStarMat L W E D u M with hJdef
  have hJ0 : 0 ≤ J := by linarith
  have hMpos : 0 < scaleM L W E u := scaleM_pos one_le_L one_le_W hE hu1
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hexp : Real.exp 1 * 2500 ≤ 6800 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  -- the norm of `ELKLK`
  have hS1 : ‖ELKLK L W E u M a₁ a₂‖ ≤ (W : ℝ) ^ 2 * ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
      ‖lkMat L W E u M a₁ b₁‖ * ‖SB L b₁ b₂‖ * ‖lkMat L W E u M b₂ a₂‖ := by
    unfold ELKLK
    rw [norm_mul]
    have hw : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
    rw [hw]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => ?_)
    rw [norm_mul, norm_mul]
  -- pointwise bound with the shift
  have hpt : ∀ b₁ b₂ : Z2 L,
      ‖lkMat L W E u M a₁ b₁‖ * ‖SB L b₁ b₂‖ * ‖lkMat L W E u M b₂ a₂‖ ≤
        (J ^ 2 * Real.exp 1) * (tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
          tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ)) * ‖SB L b₁ b₂‖ := by
    intro b₁ b₂
    by_cases hS : SB L b₁ b₂ = 0
    · simp [hS]
    have hd : zdist2 L (b₁ - b₂) ≤ 1 := by
      by_contra hcon
      exact hS (SB_apply_eq_zero L hL3 (not_le.1 hcon))
    have htri : (zdist2 L (b₁ - a₂) : ℝ) ≤ (zdist2 L (b₁ - b₂) : ℝ) +
        (zdist2 L (b₂ - a₂) : ℝ) := by
      have := zdist2_add_le L (b₁ - b₂) (b₂ - a₂)
      rw [sub_add_sub_cancel] at this
      exact_mod_cast this
    have hd' : (zdist2 L (b₁ - b₂) : ℝ) ≤ 1 := by exact_mod_cast hd
    have hshift : tailT L W E D u (zdist2 L (b₂ - a₂) : ℝ) ≤
        Real.exp 1 * tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ) := by
      have h1 : tailT L W E D u (zdist2 L (b₂ - a₂) : ℝ) ≤
          tailT L W E D u ((zdist2 L (b₁ - a₂) : ℝ) - 1) :=
        LemDecCalE_tailT_anti one_le_L hu1 (by linarith)
      have h2 := LemDecCalE_tailT_shift (L := L) (W := W) (E := E) (D := D) one_le_L hu0 hu1
        (c := 1) zero_le_one (zdist2 L (b₁ - a₂) : ℝ)
      rw [Real.sqrt_one] at h2
      exact h1.trans h2
    have hl1 := LemDecCalE_lkMat_le (L := L) (W := W) E D u M a₁ b₁
    have hl2 := LemDecCalE_lkMat_le (L := L) (W := W) E D u M b₂ a₂
    have hT1 : 0 ≤ tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) := (tailT_pos one_le_W L E D u _).le
    have hT2 : 0 ≤ tailT L W E D u (zdist2 L (b₂ - a₂) : ℝ) := (tailT_pos one_le_W L E D u _).le
    have hSn : 0 ≤ ‖SB L b₁ b₂‖ := norm_nonneg _
    calc ‖lkMat L W E u M a₁ b₁‖ * ‖SB L b₁ b₂‖ * ‖lkMat L W E u M b₂ a₂‖
        ≤ (J * tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ)) * ‖SB L b₁ b₂‖ *
            (J * tailT L W E D u (zdist2 L (b₂ - a₂) : ℝ)) := by
          gcongr
      _ ≤ (J * tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ)) * ‖SB L b₁ b₂‖ *
            (J * (Real.exp 1 * tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ))) := by
          gcongr
      _ = (J ^ 2 * Real.exp 1) * (tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
          tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ)) * ‖SB L b₁ b₂‖ := by ring
  have hS2 : ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
      ‖lkMat L W E u M a₁ b₁‖ * ‖SB L b₁ b₂‖ * ‖lkMat L W E u M b₂ a₂‖ ≤
      (J ^ 2 * Real.exp 1) * ∑ b₁ : Z2 L, tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
          tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ) := by
    calc ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
        ‖lkMat L W E u M a₁ b₁‖ * ‖SB L b₁ b₂‖ * ‖lkMat L W E u M b₂ a₂‖
        ≤ ∑ b₁ : Z2 L, ∑ b₂ : Z2 L, (J ^ 2 * Real.exp 1) *
            (tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
              tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ)) * ‖SB L b₁ b₂‖ :=
          Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hpt b₁ b₂
      _ = ∑ b₁ : Z2 L, (J ^ 2 * Real.exp 1) * (tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
              tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ)) := by
          refine Finset.sum_congr rfl fun b₁ _ => ?_
          rw [← Finset.mul_sum, KLoop.sum_norm_SB_row L hL3 b₁, mul_one]
      _ = (J ^ 2 * Real.exp 1) * ∑ b₁ : Z2 L, tailT L W E D u (zdist2 L (a₁ - b₁) : ℝ) *
              tailT L W E D u (zdist2 L (b₁ - a₂) : ℝ) := by rw [Finset.mul_sum]
  have hconv := convTailT L W E D u hE hu0 hu1 hfloorC a₁ a₂
  -- (e1): `W² ℓ² (M²)⁻¹ = η⁻¹ M⁻¹`
  have hcoef : (W : ℝ) ^ 2 * ellT L u ^ 2 * (scaleM L W E u ^ 2)⁻¹ =
      (etaT E u)⁻¹ * (scaleM L W E u)⁻¹ := by
    rw [LemDecCalE_e1 (L := L) (W := W) hE hu1]
    field_simp
  have hTu : 0 ≤ tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) := (tailT_pos one_le_W L E D u _).le
  have hTuv : tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) ≤
      tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ) :=
    LemDecCalE_tailT_mono_scale one_le_L one_le_W hE hu0 huv hv1 (Nat.cast_nonneg _)
  set X : ℝ := (etaT E u)⁻¹ * (scaleM L W E u)⁻¹ * J ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hmain : ‖ELKLK L W E u M a₁ a₂‖ ≤
      (2500 * Real.exp 1) * (X * tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ)) := by
    calc ‖ELKLK L W E u M a₁ a₂‖
        ≤ (W : ℝ) ^ 2 * ((J ^ 2 * Real.exp 1) * (2500 * ellT L u ^ 2 * (scaleM L W E u ^ 2)⁻¹ *
            tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ))) := by
          refine hS1.trans ?_
          gcongr
          refine hS2.trans ?_
          gcongr
      _ = (2500 * Real.exp 1) * ((W : ℝ) ^ 2 * ellT L u ^ 2 * (scaleM L W E u ^ 2)⁻¹ * J ^ 2 *
            tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ)) := by ring
      _ = (2500 * Real.exp 1) * (X * tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ)) := by
          rw [hcoef, hX]
  calc ‖ELKLK L W E u M a₁ a₂‖
      ≤ (2500 * Real.exp 1) * (X * tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ)) := hmain
    _ ≤ 6800 * (X * tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ)) := by
        have h0 : 0 ≤ X * tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) := mul_nonneg hX0 hTu
        have h1 : X * tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) ≤
            X * tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ) := mul_le_mul_of_nonneg_left hTuv hX0
        have h2 : (2500 * Real.exp 1) ≤ 6800 := by linarith
        exact mul_le_mul h2 h1 h0 (by norm_num)
    _ ≤ lossE2 L W Λ K₀ * X * tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ) := by
        have hTv : 0 ≤ tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ) := (tailT_pos one_le_W L E D v _).le
        have := mul_le_mul_of_nonneg_right hloss (mul_nonneg hX0 hTv)
        linarith

end LK

/-! ## 4. Ball counts (e10) and the neighbour sums of `gexRHS` -/

section Near

variable {L : ℕ} [NeZero L]

/-- (e10) (a): the ball count `RBM.KLoop.card_ball_le`, `#{u : |a - u|_L ≤ R} ≤ (2R+1)²`. -/
theorem LemDecCalE_e10a (a : Z2 L) (R : ℝ) (hR : 0 ≤ R) :
    (((Finset.univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ) ≤
      (2 * R + 1) ^ 2 :=
  KLoop.card_ball_le L a R hR

private theorem zdist_le_one_cases (hL : 3 ≤ L) {x : ZMod L} (h : zdist L x ≤ 1) :
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

private theorem mem_sbSupport_of_zdist2_le_one (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    v ∈ sbSupport L := by
  obtain ⟨x, y⟩ := v
  simp only [zdist2] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hz1 : zdist L (1 : ZMod L) ≠ 0 := fun h0 => h1 ((zdist_eq_zero_iff L).1 h0)
  have hzm : zdist L (-1 : ZMod L) ≠ 0 := fun h0 => neg_ne_zero.2 h1 ((zdist_eq_zero_iff L).1 h0)
  have hx : zdist L x ≤ 1 := by omega
  have hy : zdist L y ≤ 1 := by omega
  rcases zdist_le_one_cases hL hx with rfl | rfl | rfl <;>
    rcases zdist_le_one_cases hL hy with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | simp [sbSupport]

/-- (e10) (b): sharp ball count, `#{a' : |a' - a|_L ≤ 1} ≤ 5` for `L ≥ 3` (the five blocks of the
nearest-neighbour support; `card_ball_le` only gives `9`).  It is what makes the pair count `25`. -/
theorem LemDecCalE_e10b (hL : 3 ≤ L) (a : Z2 L) :
    ((Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1)).card : ℝ) ≤ 5 := by
  have hsub : Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1) ⊆
      (sbSupport L).image (fun v => v + a) := by
    intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    exact Finset.mem_image.2 ⟨a' - a, mem_sbSupport_of_zdist2_le_one hL ha', by simp⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_sbSupport L hL] at this
  exact_mod_cast this

private theorem zdist_neg_eq (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem zdist2_neg_eq (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, zdist_neg_eq]

/-- `|q - p|_L ≤ |q - a'|_L + |a' - b'|_L + |b' - p|_L` with the two outer terms flipped
to `|a' - q|_L`, `|b' - p|_L`. -/
private theorem zdist2_tri3 (q p a' b' : Z2 L) :
    zdist2 L (q - p) ≤ zdist2 L (a' - q) + zdist2 L (a' - b') + zdist2 L (b' - p) := by
  have e : q - p = ((q - a') + (a' - b')) + (b' - p) := by abel
  have h1 := zdist2_add_le L (q - a' + (a' - b')) (b' - p)
  have h2 := zdist2_add_le L (q - a') (a' - b')
  have h3 : zdist2 L (q - a') = zdist2 L (a' - q) := by
    rw [← neg_sub a' q, zdist2_neg_eq]
  rw [e]
  omega

variable {W : ℕ} [NeZero W]

/-- The right side of (`GijGEX`) at `(a, b)` is at most `25 B + [|a - b|_L ≤ 1] W⁻²` if
`|𝓛_{(+,-),(a',b')}| ≤ B` for the pairs with `|a' - a|_L ≤ 1`, `|b' - b|_L ≤ 1` (the ball
`|·|_L ≤ 1` has `5` points, so `5 · 5 = 25` pairs).  The proof is that of the `private`
`s1_gexRHS_le` of `RBM2D/Induction/Step1.lean`, with the bound on `‖loopPM‖` assumed only on
the neighbour pairs. -/
private theorem gexRHS_le_near (hL : 3 ≤ L) (E u B : ℝ) (hB : 0 ≤ B)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L)
    (hM : ∀ a' b' : Z2 L, zdist2 L (a' - a) ≤ 1 → zdist2 L (b' - b) ≤ 1 →
      ‖loopPM L W E u M a' b'‖ ≤ B) :
    gexRHS L W E u M a b ≤
      25 * B + (if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) := by
  unfold gexRHS
  have h1 : (∑ a' : Z2 L, ∑ b' : Z2 L,
      if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0) ≤
      25 * B := by
    calc (∑ a' : Z2 L, ∑ b' : Z2 L,
        if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0)
        ≤ ∑ a' : Z2 L, ∑ b' : Z2 L, (if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          by_cases h1 : zdist2 L (a' - a) ≤ 1 <;> by_cases h2 : zdist2 L (b' - b) ≤ 1
          · simpa [h1, h2] using hM a' b' h1 h2
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
      _ = (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 5 * (5 * B) := by
          have e1 : (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact LemDecCalE_e10b hL a
          have e2 : (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact LemDecCalE_e10b hL b
          have e0 : 0 ≤ (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) :=
            Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
          exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hB) (mul_nonneg e0 hB) (by norm_num)
      _ = 25 * B := by ring
  linarith

end Near

/-! ## 5. The Green function entries: (e6)–(e9) -/

section Green

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- The entries of `G_u(+)` at blocks are the entries of the fine-lattice resolvent at the
`splitEquiv` coordinates (`Matrix.inv_submatrix_equiv`). -/
private theorem greenBlk_true_apply (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (p q : BlockIndex L W) :
    greenBlk L W E u M true p q =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹
        ((splitEquiv L W).symm p) ((splitEquiv L W).symm q) := by
  unfold greenBlk blockMat
  rw [Gsig_true, green]
  have h : M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm -
      spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
        (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [h, Matrix.inv_submatrix_equiv]
  rfl

/-- (e6), the resolvent entries minus `δ_{pq} m^{(σ)}`: for `M ∈ goodSet L W E s u Λ`, both
signs `σ` and all blocks `p q`, `|G_{pq}(σ) - δ_{pq} m(σ)| ≤ Λ M_u^{-1/4}` (clause 3 of `goodSet`
at the fine indices `splitEquiv.symm p`, `splitEquiv.symm q`; for `σ = −` the adjoint `G(−) = G(+)ᴴ`,
`Gsig_conjTranspose`, with `M` Hermitian, clause 1). -/
theorem LemDecCalE_e6_err (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (p q : BlockIndex L W) :
    ‖greenBlk L W E u M σ p q - (if p = q then KLoop.mSig E σ else 0)‖ ≤
      Λ * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := by
  obtain ⟨hH, -, hll, -⟩ := hM
  have hpq : ∀ p q : BlockIndex L W, ‖greenBlk L W E u M true p q -
      (if p = q then spectralM E else 0)‖ ≤ Λ * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) := by
    intro p q
    have h := hll ((splitEquiv L W).symm p) ((splitEquiv L W).symm q)
    unfold llErrMat at h
    rw [greenBlk_true_apply]
    have hiff : ((splitEquiv L W).symm p = (splitEquiv L W).symm q) ↔ p = q :=
      (splitEquiv L W).symm.injective.eq_iff
    simpa only [hiff] using h
  cases σ
  · have hHb : (blockMat M).IsHermitian := hH.submatrix _
    have hG := Gsig_conjTranspose hHb (spectralZ E u) true
    have hfalse : greenBlk L W E u M false p q =
        star (greenBlk L W E u M true q p) := by
      have := congrFun (congrFun hG p) q
      simpa [Matrix.conjTranspose_apply, greenBlk] using this.symm
    have h := hpq q p
    have hs : greenBlk L W E u M false p q - (if p = q then KLoop.mSig E false else 0) =
        star (greenBlk L W E u M true q p - (if q = p then spectralM E else 0)) := by
      rw [hfalse, star_sub]
      congr 1
      by_cases hpq' : p = q
      · subst hpq'
        simp [KLoop.mSig]
      · have : ¬ q = p := fun h => hpq' h.symm
        simp [hpq', this]
    rw [hs, norm_star]
    exact h
  · simpa [KLoop.mSig] using hpq p q

/-- (e6): for `M ∈ goodSet L W E s u Λ`, `|E| ≤ 2`, `Λ ≥ 1`, `M_u ≥ 1`, every entry satisfies
`|G_{pq}(σ)| ≤ |m| + Λ M_u^{-1/4} ≤ 2Λ` (`|m| = 1`, `norm_spectralM`). -/
theorem LemDecCalE_e6 (hE : |E| ≤ 2) (hΛ : 1 ≤ Λ) (hM1 : 1 ≤ scaleM L W E u)
    (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (p q : BlockIndex L W) :
    ‖greenBlk L W E u M σ p q‖ ≤ 2 * Λ := by
  have herr := LemDecCalE_e6_err hM σ p q
  have hinv : (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one (by positivity) (inv_le_one_of_one_le₀ hM1) (by norm_num)
  have hm : ‖KLoop.mSig E σ‖ = 1 := by
    cases σ
    · simp [KLoop.mSig, norm_spectralM hE]
    · simp [KLoop.mSig, norm_spectralM hE]
  have hdiag : ‖(if p = q then KLoop.mSig E σ else 0 : ℂ)‖ ≤ 1 := by
    split_ifs
    · exact hm.le
    · simp
  have h1 := norm_le_norm_sub_add (greenBlk L W E u M σ p q)
    (if p = q then KLoop.mSig E σ else 0)
  have hΛ0 : 0 ≤ Λ := by linarith
  have : Λ * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4) ≤ Λ * 1 := mul_le_mul_of_nonneg_left hinv hΛ0
  linarith

/-- (e6) under `E2Hyp` (`|E| < 2`, `Λ ≥ 1`, `M_u ≥ M_v ≥ 1` by (e2), `M ∈ goodSet`). -/
theorem LemDecCalE_e6_of_hyp (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Bool) (p q : BlockIndex L W) :
    ‖greenBlk L W E u M σ p q‖ ≤ 2 * Λ := by
  have h2 := LemDecCalE_e2 h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  exact LemDecCalE_e6 hE.le hΛ (hMv.trans h2.2.1) hgood σ p q

/-- (e7) [25 neighbour pairs]: under `E2Hyp`, for blocks `p q` with
`|q.1 - p.1|_L ≥ ℓ*_u/8 + 2`,
`‖G_{pq}‖² ≤ 25 Λ (W^{-D} + J 𝒯_u(|q.1 - p.1|_L - 2))`, `G = greenBlk … true`.
From the swapped (`GijGEX`) clause of `goodSet` (`gexRHS … q.1 p.1`): `gexRHS` is a sum
over the `5 · 5` pairs `(a', b')` with `|a' - q.1|_L ≤ 1`, `|b' - p.1|_L ≤ 1` (and no `W⁻²` term as
`|q.1 - p.1|_L > 1`); each has `|a' - b'|_L ≥ |q.1 - p.1|_L - 2 ≥ ℓ*_u/8`, hence
`‖𝒦(a',b')‖ ≤ W^{-D}` (conjunct 15) and `‖𝓛 - 𝒦‖ ≤ J 𝒯_u(|q.1 - p.1|_L - 2)` ((e4) (a), (e5)). -/
theorem LemDecCalE_e7 (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W)
    (hd : ellStar L W u / 8 + 2 ≤ (zdist2 L (q.1 - p.1) : ℝ)) :
    ‖greenBlk L W E u M true p q‖ ^ 2 ≤
      25 * Λ * ((W : ℝ) ^ (-D) + jStarMat L W E D u M *
        tailT L W E D u ((zdist2 L (q.1 - p.1) : ℝ) - 2)) := by
  have hJ1 := one_le_jStarMat L W one_le_W E D u M
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu1 : u < 1 := huv.trans_lt hv1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hℓ := (ellT_pos_le (L := L) one_le_L hu1).1
  have hlogW : 0 ≤ Real.log (W : ℝ) := by linarith
  have hstar : 0 ≤ ellStar L W u :=
    mul_nonneg (Real.rpow_nonneg hlogW _) hℓ.le
  set d : ℝ := (zdist2 L (q.1 - p.1) : ℝ) with hddef
  have hd2 : 2 ≤ d := by linarith
  have hpq : p ≠ q := by
    intro hpq
    subst hpq
    norm_num [hddef] at hd2
  have hgex := hgood.2.2.2.1 p q hpq
  set J := jStarMat L W E D u M with hJdef
  have hJ0 : 0 ≤ J := by linarith
  have hB0 : 0 ≤ (W : ℝ) ^ (-D) + J * tailT L W E D u (d - 2) :=
    add_nonneg (Real.rpow_nonneg hW0.le _) (mul_nonneg hJ0 (tailT_pos one_le_W L E D u _).le)
  have hloc : ∀ a' b' : Z2 L, zdist2 L (a' - q.1) ≤ 1 → zdist2 L (b' - p.1) ≤ 1 →
      ‖loopPM L W E u M a' b'‖ ≤ (W : ℝ) ^ (-D) + J * tailT L W E D u (d - 2) := by
    intro a' b' h1 h2
    have htri := zdist2_tri3 q.1 p.1 a' b'
    have h1' : (zdist2 L (a' - q.1) : ℝ) ≤ 1 := by exact_mod_cast h1
    have h2' : (zdist2 L (b' - p.1) : ℝ) ≤ 1 := by exact_mod_cast h2
    have htri' : d ≤ (zdist2 L (a' - q.1) : ℝ) + (zdist2 L (a' - b') : ℝ) +
        (zdist2 L (b' - p.1) : ℝ) := by
      rw [hddef]; exact_mod_cast htri
    have hfar : d - 2 ≤ (zdist2 L (a' - b') : ℝ) := by linarith
    have hfar' : ellStar L W u / 8 ≤ (zdist2 L (a' - b') : ℝ) := by linarith
    have hKp := hK15 a' b' hfar'
    have hlk := LemDecCalE_lkMat_le (L := L) (W := W) E D u M a' b'
    have hT := LemDecCalE_tailT_anti (L := L) (W := W) (E := E) (D := D) one_le_L hu1 hfar
    have hsum : loopPM L W E u M a' b' = lkMat L W E u M a' b' + Kpm L W E u a' b' := by
      unfold lkMat; ring
    have hn := norm_add_le (lkMat L W E u M a' b') (Kpm L W E u a' b')
    have hJT := mul_le_mul_of_nonneg_left hT hJ0
    rw [hsum]
    linarith
  have hgex' := gexRHS_le_near (W := W) hL3 E u _ hB0 M q.1 p.1 hloc
  have hnear : ¬ zdist2 L (q.1 - p.1) ≤ 1 := by
    intro hle
    have : (zdist2 L (q.1 - p.1) : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith
  simp only [hnear, ite_false, add_zero] at hgex'
  have hΛ0 : 0 ≤ Λ := by linarith
  calc ‖greenBlk L W E u M true p q‖ ^ 2 ≤ Λ * gexRHS L W E u M q.1 p.1 := hgex
    _ ≤ Λ * (25 * ((W : ℝ) ^ (-D) + J * tailT L W E D u (d - 2))) :=
        mul_le_mul_of_nonneg_left hgex' hΛ0
    _ = 25 * Λ * ((W : ℝ) ^ (-D) + J * tailT L W E D u (d - 2)) := by ring

/-- (e8) [25 neighbour pairs]: under `E2Hyp`, for blocks `p ≠ q`,
`‖G_{pq}‖² ≤ Λ (25 (K₀ M_u⁻¹ + 2 J M_u⁻²) + W⁻²)` (clause 4 of `goodSet`, `gexRHS_le_near` with
the bound of (e5)), and this is `≤ 50 Λ K₀ M_u⁻¹ (1 + J/M_u)` (`W⁻² ≤ M_u⁻¹` as `M_u ≤ W²`,
`K₀ ≥ 1`). -/
theorem LemDecCalE_e8 (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) (hpq : p ≠ q) :
    ‖greenBlk L W E u M true p q‖ ^ 2 ≤
        Λ * (25 * (K₀ * (scaleM L W E u)⁻¹ + 2 * jStarMat L W E D u M * (scaleM L W E u ^ 2)⁻¹) +
          ((W : ℝ) ^ 2)⁻¹) ∧
      ‖greenBlk L W E u M true p q‖ ^ 2 ≤
        50 * Λ * K₀ * (scaleM L W E u)⁻¹ * (1 + jStarMat L W E D u M / scaleM L W E u) := by
  have hloop := LemDecCalE_loopPM_le h
  have h2 := LemDecCalE_e2 h
  have hJ1 := one_le_jStarMat L W one_le_W E D u M
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu1 : u < 1 := huv.trans_lt hv1
  have hMpos : 0 < scaleM L W E u := by linarith [h2.1, h2.2.1]
  set J := jStarMat L W E D u M with hJdef
  have hJ0 : 0 ≤ J := by linarith
  have hgex := hgood.2.2.2.1 p q hpq
  have hB0 : 0 ≤ K₀ * (scaleM L W E u)⁻¹ + 2 * J * (scaleM L W E u ^ 2)⁻¹ := by positivity
  have hgex' := gexRHS_le_near (W := W) hL3 E u _ hB0 M q.1 p.1 (fun a' b' _ _ => hloop a' b')
  have hif : (if zdist2 L (q.1 - p.1) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    split_ifs
    · exact le_rfl
    · positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hfirst : ‖greenBlk L W E u M true p q‖ ^ 2 ≤
      Λ * (25 * (K₀ * (scaleM L W E u)⁻¹ + 2 * J * (scaleM L W E u ^ 2)⁻¹) +
        ((W : ℝ) ^ 2)⁻¹) :=
    hgex.trans (mul_le_mul_of_nonneg_left (hgex'.trans (by linarith)) hΛ0)
  refine ⟨hfirst, hfirst.trans ?_⟩
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.2 hMpos
  have hWm : ((W : ℝ) ^ 2)⁻¹ ≤ m := inv_anti₀ hMpos h2.2.2
  have hm2 : (scaleM L W E u ^ 2)⁻¹ = m ^ 2 := by rw [hm, inv_pow]
  have hJM : J / scaleM L W E u = J * m := by rw [hm, div_eq_mul_inv]
  rw [hm2, hJM]
  have h1 : 25 * (K₀ * m + 2 * J * m ^ 2) + ((W : ℝ) ^ 2)⁻¹ ≤ 50 * K₀ * m * (1 + J * m) := by
    have e1 : 0 ≤ (K₀ - 1) * m := mul_nonneg (by linarith) hm0.le
    have e2 : 0 ≤ (K₀ - 1) * (J * m ^ 2) := mul_nonneg (by linarith) (by positivity)
    have e3 : 0 ≤ K₀ * m := by positivity
    nlinarith
  calc Λ * (25 * (K₀ * m + 2 * J * m ^ 2) + ((W : ℝ) ^ 2)⁻¹)
      ≤ Λ * (50 * K₀ * m * (1 + J * m)) := mul_le_mul_of_nonneg_left h1 hΛ0
    _ = 50 * Λ * K₀ * m * (1 + J * m) := by ring

/-- (e9): for `M ∈ goodSet L W E s u Λ`, both signs `σ` and every block `a`,
`|⟨G̃_u(σ) E_a⟩| ≤ Λ (ℓ_u/ℓ_s)² M_u⁻¹` (clause 6 of `goodSet`).  For `σ = −` the conjugation
step: `M` Hermitian (clause 1), `G(−) = G(+)ᴴ` (`Gsig_conjTranspose`), `E_a` Hermitian, so
`avgErr … false a = conj (avgErr … true a)` (`Matrix.trace_conjTranspose`, `Matrix.trace_mul_comm`). -/
theorem LemDecCalE_e9 (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (a : Z2 L) :
    ‖avgErr L W E u M σ a‖ ≤ Λ * (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ := by
  obtain ⟨hH, -, -, -, -, hav⟩ := hM
  cases σ
  · have hHb : (blockMat M).IsHermitian := hH.submatrix _
    have hG := Gsig_conjTranspose hHb (spectralZ E u) true
    have hEh : (Eblk L W a)ᴴ = Eblk L W a := by
      ext p q
      simp only [Matrix.conjTranspose_apply, Eblk_apply]
      by_cases hpq : q = p
      · subst hpq
        split_ifs <;> simp
      · have : ¬ p = q := fun h => hpq h.symm
        simp [hpq, this]
    set X : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
      greenBlk L W E u M true - KLoop.mSig E true • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      with hX
    have hXh : greenBlk L W E u M false - KLoop.mSig E false •
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) = Xᴴ := by
      rw [hX, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      have hgt : (greenBlk L W E u M true)ᴴ = greenBlk L W E u M false := by
        simpa [greenBlk] using hG
      rw [hgt]
      congr 2
    have hav' : avgErr L W E u M false a = star (avgErr L W E u M true a) := by
      unfold avgErr
      rw [hXh, ← hX, ← Matrix.trace_conjTranspose]
      rw [Matrix.conjTranspose_mul, hEh, Matrix.trace_mul_comm]
    rw [hav', norm_star]
    exact hav a
  · exact hav a

end Green

end RBM.Path
