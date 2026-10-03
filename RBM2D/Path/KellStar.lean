/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Props
import RBM2D.Path.UBounds
import RBM2D.Propagator.Prop5

/-!
# The `𝒦` bound at `n = 2` and the far field `Kell*`

Paper: arXiv:2503.07606, (`Kell*`) in Lemma `lem_dec_calE_0`.

* `KpmBoundProp5`, `KellStarEv` : the two statements.
* `kpmBoundProp5` : `|𝒦_{u,(+,-),(a,b)}| ≤ 180·40002² (1 + log L) M_u⁻¹`.
* `kellStarEv` : eventually, beyond `δ ℓ*_u`, `Θ_u` and `𝒰`-kernel entries are `≤ W^{-D}`.

The single analytic input is property 5 in its explicit-constant form `norm_Theta_apply_le_prop5`
at `ξ = u` real; the far-field estimate closes by the growth of `(log W)^{3/2}` against
`log W`.  No d = 1 closed form is used.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-! ## Definitions -/

/-- **The `𝒦` bound at `n = 2` from property 5**:
`|𝒦_{u,(+,-),(a,b)}| ≤ 180·40002² (1 + log L) M_u^{-1}`. -/
def KpmBoundProp5 : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ a b : Z2 L, ‖Kpm L W E u a b‖ ≤
      180 * 40002 ^ 2 * (1 + Real.log L) * (scaleM L W E u)⁻¹

/-- **The far field (`Kell*`)** in `∀ᶠ` form: beyond `δ ℓ*_u`, both `Θ_u` and
`Θ_s^{-1} Θ_u = ukerMat 1 s u` are `≤ W^{-D}`, uniformly in `0 ≤ s ≤ u ≤ t_n`. -/
def KellStarEv : Prop :=
  ∀ (d : Sizes) (c τ δ D : ℝ) (t : ℕ → ℝ), 0 < c → 0 < τ → 0 < δ →
    Tendsto d.size atTop atTop → Bandwidth d c → RangeCond d τ t → (∀ n, t n < 1) →
    ∀ᶠ n : ℕ in atTop, ∀ s u : ℝ, 0 ≤ s → s ≤ u → u ≤ t n →
      ∀ a b : Z2 (d.L n), δ * ellStar (d.L n) (d.W n) u ≤ (zdist2 (d.L n) (a - b) : ℝ) →
        ‖Theta (d.L n) (u : ℂ) a b‖ ≤ (d.W n : ℝ) ^ (-D) ∧
          ‖ukerMat (d.L n) 1 s u a b‖ ≤ (d.W n : ℝ) ^ (-D)

/-! ## Private helpers -/

/-- Property 5 at the real point `ξ = u ∈ [0,1)`, written in the scale `ℓ_u = ellT L u`:
`κ² = 1 - u` and `ℓ̂(u) = ℓ_u`. -/
private theorem kellStar_theta_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (a b : Z2 L) :
    ‖Theta L (u : ℂ) a b‖ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) *
      ((1 - u) * ellT L u ^ 2)⁻¹ *
      Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L u)) := by
  have hξ : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have h := norm_Theta_apply_le_prop5 L hL (u : ℂ) hξ a b
  have hk : kappa (u : ℂ) = Real.sqrt (1 - u) := by
    unfold kappa
    congr 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hkk : kappa (u : ℂ) ^ 2 = 1 - u := by rw [hk, Real.sq_sqrt (by linarith)]
  have hℓ : ellhat L (u : ℂ) = ellT L u := by
    unfold ellhat ellT; rw [hk, one_div]
  rw [hkk, hℓ] at h
  exact h

/-- `min(1, L² (1-u)) ≤ (1-u) ℓ_u²` for `u < 1`. -/
private theorem kellStar_min_le (L : ℕ) {u : ℝ} (hu : u < 1) :
    min 1 ((L : ℝ) ^ 2 * (1 - u)) ≤ (1 - u) * ellT L u ^ 2 := by
  have hx : 0 < 1 - u := by linarith
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have ha : (1 / Real.sqrt (1 - u)) ^ 2 * (1 - u) = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hx.le]; field_simp
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  unfold ellT
  rcases le_total (1 / Real.sqrt (1 - u)) (L : ℝ) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (le_of_eq (mul_comm _ _))

/-- `Kpm` at `|E| < 2` is `W⁻² Θ_u`, since `|m|² = 1`. -/
private theorem kellStar_Kpm_eq (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2) (u : ℝ)
    (a b : Z2 L) : Kpm L W E u a b = ((W : ℂ)⁻¹) ^ 2 * Theta L (u : ℂ) a b := by
  have h1 : Complex.normSq (spectralM E) = 1 := normSqSpectralMOne E hE.le
  unfold Kpm
  rw [h1]
  simp

/-- The closing inequality of the far field, for `x = log W ≥ 1` with
`20000 A ≤ δ √x`, `A = 180·40002² + 1/(2c) + 2 + |D|`. -/
private theorem kellStar_arith {c δ D x : ℝ} (hc : 0 < c) (hx1 : 1 ≤ x)
    (hsq : 20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) ≤ δ * Real.sqrt x) :
    180 * 40002 ^ 2 * (1 + x / (2 * c)) * Real.exp (2 * x) *
        Real.exp (-δ * x ^ ((3 : ℝ) / 2) / 20000) ≤ Real.exp (x * (-D)) := by
  have hx0 : 0 < x := by linarith
  have hy : 0 ≤ x / (2 * c) := by positivity
  have h32 : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h, Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h1 : 180 * 40002 ^ 2 * (1 + x / (2 * c)) ≤
      Real.exp (180 * 40002 ^ 2) * Real.exp (x / (2 * c)) := by
    apply mul_le_mul _ _ (by linarith) (Real.exp_pos _).le
    · have := Real.add_one_le_exp (180 * 40002 ^ 2 : ℝ); linarith
    · have := Real.add_one_le_exp (x / (2 * c)); linarith
  have h2 : 180 * 40002 ^ 2 + x / (2 * c) + 2 * x + -δ * x ^ ((3 : ℝ) / 2) / 20000 ≤
      x * (-D) := by
    rw [h32]
    have e1 : x / (2 * c) = 1 / (2 * c) * x := by ring
    have hDx : D * x ≤ |D| * x := mul_le_mul_of_nonneg_right (le_abs_self D) hx0.le
    have hCx : (180 * 40002 ^ 2 : ℝ) ≤ 180 * 40002 ^ 2 * x := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hx0.le
    rw [e1]
    nlinarith
  calc 180 * 40002 ^ 2 * (1 + x / (2 * c)) * Real.exp (2 * x) *
        Real.exp (-δ * x ^ ((3 : ℝ) / 2) / 20000)
      ≤ Real.exp (180 * 40002 ^ 2) * Real.exp (x / (2 * c)) * Real.exp (2 * x) *
        Real.exp (-δ * x ^ ((3 : ℝ) / 2) / 20000) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (180 * 40002 ^ 2 + x / (2 * c) + 2 * x + -δ * x ^ ((3 : ℝ) / 2) / 20000) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (x * (-D)) := Real.exp_le_exp.mpr h2

/-- The far field of `Θ_u` at one size, from property 5 (`ℓ_u`-scale). -/
private theorem kellStar_theta_far (L W : ℕ) [NeZero L] (hL : 3 ≤ L) (hW : 1 ≤ W)
    {c δ D u : ℝ} (hc : 0 < c)
    (hBW : ((((W * L) ^ 2 : ℕ) : ℝ)) ^ c ≤ (W : ℝ))
    (hx1 : 1 ≤ Real.log (W : ℝ))
    (hsq : 20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) ≤
      δ * Real.sqrt (Real.log (W : ℝ)))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hN : 1 ≤ (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (1 - u)))
    (a b : Z2 L) (hfar : δ * ellStar L W u ≤ (zdist2 L (a - b) : ℝ)) :
    ‖Theta L (u : ℂ) a b‖ ≤ (W : ℝ) ^ (-D) := by
  have hWn : 0 < W := hW
  have hLn : 0 < L := by omega
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hx0 : 0 < Real.log (W : ℝ) := by linarith
  have hu1' : 0 < 1 - u := by linarith
  have hℓ := (ellT_pos_le (by omega : 1 ≤ L) hu1).1
  -- `log L ≤ log W / (2c)` from the bandwidth condition
  have hlogL : Real.log (L : ℝ) ≤ Real.log (W : ℝ) / (2 * c) := by
    have hNn : 0 < (W * L) ^ 2 := by positivity
    have hNpos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNn
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hNpos c) hBW
    rw [Real.log_rpow hNpos] at h1
    have h2 : Real.log ((((W * L) ^ 2 : ℕ) : ℝ)) =
        2 * Real.log (W : ℝ) + 2 * Real.log (L : ℝ) := by
      push_cast
      rw [Real.log_pow, Real.log_mul hWpos.ne' hLpos.ne']
      push_cast; ring
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hc hx0]
  have h5 := kellStar_theta_le L hL hu0 hu1 a b
  -- the prefactor `((1-u) ℓ_u²)⁻¹ ≤ W²`
  have hQ : ((1 - u) * ellT L u ^ 2)⁻¹ ≤ (W : ℝ) ^ 2 := by
    have hmin := kellStar_min_le L hu1
    have hle : ((W : ℝ) ^ 2)⁻¹ ≤ min 1 ((L : ℝ) ^ 2 * (1 - u)) := by
      apply le_min
      · exact inv_le_one_of_one_le₀ (one_le_pow₀ hW')
      · calc ((W : ℝ) ^ 2)⁻¹ = ((W : ℝ) ^ 2)⁻¹ * 1 := (mul_one _).symm
          _ ≤ ((W : ℝ) ^ 2)⁻¹ * ((W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (1 - u))) :=
              mul_le_mul_of_nonneg_left hN (by positivity)
          _ = (L : ℝ) ^ 2 * (1 - u) := inv_mul_cancel_left₀ (by positivity) _
    have hP : ((W : ℝ) ^ 2)⁻¹ ≤ (1 - u) * ellT L u ^ 2 := hle.trans hmin
    have := inv_anti₀ (by positivity) hP
    rwa [inv_inv] at this
  -- the exponential
  have hexp : Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L u)) ≤
      Real.exp (-δ * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) / 20000) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold ellStar at hfar
    nlinarith
  have hxW : (W : ℝ) ^ 2 = Real.exp (2 * Real.log (W : ℝ)) := by
    rw [show (2 : ℝ) * Real.log (W : ℝ) = ((2 : ℕ) : ℝ) * Real.log (W : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hWpos]
  have hC : (0 : ℝ) ≤ 180 * 40002 ^ 2 := by norm_num
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  calc ‖Theta L (u : ℂ) a b‖
      ≤ 180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - u) * ellT L u ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L u)) := h5
    _ ≤ 180 * 40002 ^ 2 * (1 + Real.log (W : ℝ) / (2 * c)) * (W : ℝ) ^ 2 *
        Real.exp (-δ * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) / 20000) := by
        have hy : (0 : ℝ) ≤ 1 + Real.log (L : ℝ) := by linarith
        have hQ0 : (0 : ℝ) ≤ ((1 - u) * ellT L u ^ 2)⁻¹ := by positivity
        have hlogL' : 1 + Real.log (L : ℝ) ≤ 1 + Real.log (W : ℝ) / (2 * c) := by linarith
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hlogL' hC) hQ
          hQ0 (by positivity)) hexp (Real.exp_pos _).le (by positivity)
    _ = 180 * 40002 ^ 2 * (1 + Real.log (W : ℝ) / (2 * c)) *
        Real.exp (2 * Real.log (W : ℝ)) *
        Real.exp (-δ * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) / 20000) := by rw [hxW]
    _ ≤ Real.exp (Real.log (W : ℝ) * (-D)) := kellStar_arith hc hx1 hsq
    _ = (W : ℝ) ^ (-D) := (Real.rpow_def_of_pos hWpos _).symm

/-- Off-diagonal entries of the `𝒰`-kernel: `u 𝒰_{s,u}(a,b) = (u - s) Θ_u(a,b)` for `a ≠ b`
(from `(1 - uS) Θ_u = 1`). -/
private theorem kellStar_uker_offdiag (L : ℕ) [NeZero L] (hL : 3 ≤ L) {s u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) {a b : Z2 L} (hab : a ≠ b) :
    (u : ℂ) * ukerMat L 1 s u a b = ((u : ℂ) - (s : ℂ)) * Theta L (u : ℂ) a b := by
  have hξ : ‖(u : ℂ) * 1‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have h := mul_Theta L hL hξ
  have h' : (u : ℂ) • ukerMat L 1 s u =
      ((u : ℂ) - (s : ℂ)) • Theta L ((u : ℂ) * 1) + (s : ℂ) • (1 : Matrix (Z2 L) (Z2 L) ℂ) := by
    have hs : (s : ℂ) • (1 : Matrix (Z2 L) (Z2 L) ℂ) =
        (s : ℂ) • ((1 - ((u : ℂ) * 1) • SB L) * Theta L ((u : ℂ) * 1)) := by rw [h]
    rw [hs]
    unfold ukerMat
    simp only [sub_mul, one_mul, smul_mul_assoc]
    module
  have h'' := congrFun (congrFun h' a) b
  simpa [Matrix.one_apply_ne hab] using h''

/-! ## Theorems -/

/-- **`kpmBoundProp5`**: `|𝒦_{u,(+,-),(a,b)}| ≤ 180·40002² (1 + log L) M_u⁻¹`, from property 5 at
`ξ = u |m|² = u` (`|m|² = 1`), with `W⁻² ((1-u) ℓ_u²)⁻¹ = Im m M_u⁻¹ ≤ M_u⁻¹`. -/
theorem kpmBoundProp5 : KpmBoundProp5 := by
  intro L W _ _ E u hL hE hu0 hu1 a b
  have hx : 0 < 1 - u := by linarith
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  have hm1 : (spectralM E).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_spectralM hE.le).le
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hℓ := (ellT_pos_le (by omega : 1 ≤ L) hu1).1
  have h5 := kellStar_theta_le L hL hu0 hu1 a b
  have hexp : Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ (zdist2 L (a - b) : ℝ) := Nat.cast_nonneg _
    have h20 : 0 < 20000 * ellT L u := by positivity
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg this h20.le)
  have hC : (0 : ℝ) ≤ 180 * 40002 ^ 2 * (1 + Real.log L) := by
    have := Real.log_natCast_nonneg L
    positivity
  have hP : 0 < (1 - u) * ellT L u ^ 2 := by positivity
  have hkey : ((W : ℝ)⁻¹) ^ 2 * ((1 - u) * ellT L u ^ 2)⁻¹ ≤ (scaleM L W E u)⁻¹ := by
    have e1 : ((W : ℝ)⁻¹) ^ 2 * ((1 - u) * ellT L u ^ 2)⁻¹ =
        ((W : ℝ) ^ 2 * ((1 - u) * ellT L u ^ 2))⁻¹ := by
      rw [inv_pow, ← mul_inv]
    have e2 : scaleM L W E u = ((W : ℝ) ^ 2 * ((1 - u) * ellT L u ^ 2)) * (spectralM E).im := by
      unfold scaleM etaT; ring
    rw [e1, e2]
    exact inv_anti₀ (by positivity) (mul_le_of_le_one_right (by positivity) hm1)
  calc ‖Kpm L W E u a b‖
      = ((W : ℝ)⁻¹) ^ 2 * ‖Theta L (u : ℂ) a b‖ := by
        rw [kellStar_Kpm_eq L W hE, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    _ ≤ ((W : ℝ)⁻¹) ^ 2 * (180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - u) * ellT L u ^ 2)⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left (h5.trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
          (by positivity)
    _ = 180 * 40002 ^ 2 * (1 + Real.log L) *
          (((W : ℝ)⁻¹) ^ 2 * ((1 - u) * ellT L u ^ 2)⁻¹) := by ring
    _ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) * (scaleM L W E u)⁻¹ :=
        mul_le_mul_of_nonneg_left hkey hC

/-- **`kellStarEv`** (`Kell*`): eventually, beyond `δ ℓ*_u`, `Θ_u` and `Θ_s⁻¹ Θ_u = ukerMat 1 s u`
are `≤ W^{-D}`, uniformly in `0 ≤ s ≤ u ≤ t_n`.  Property 5 at `ξ = u` bounds `Θ_u`; the
`ℓ_u`-scale prefactor is `≤ W²` on the range `1 - t ≥ N^{-1+τ}`, `log L ≤ log W / (2c)` from
`Bandwidth`, and `(log W)^{3/2}` beats `log W` since `W → ∞`. -/
theorem kellStarEv : KellStarEv := by
  intro d c τ δ D t hc hτ hδ hT hBW hRC ht
  have hNtop : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hT
  have hNc : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp hNtop
  have hWtop : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ hBW hNc
  have hxtop : Tendsto (fun n => Real.log (d.W n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hWtop
  have hX := (tendsto_atTop.1 hxtop)
    (max 1 ((20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) / δ) ^ 2))
  filter_upwards [hBW, hRC, hX] with n hBn hRn hXn
  intro s u hs0 hsu hut a b hfar
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht n)
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hWpos : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have hLpos : (0 : ℝ) < d.L n := by exact_mod_cast (by omega : 0 < d.L n)
  have hx1 : 1 ≤ Real.log (d.W n : ℝ) := (le_max_left _ _).trans hXn
  have hsq : 20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) ≤
      δ * Real.sqrt (Real.log (d.W n : ℝ)) := by
    have hA : 0 ≤ 20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) / δ := by positivity
    have h1 : (20000 * (180 * 40002 ^ 2 + 1 / (2 * c) + 2 + |D|) / δ) ^ 2 ≤
        Real.log (d.W n : ℝ) := (le_max_right _ _).trans hXn
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hA, div_le_iff₀ hδ] at h2
    linarith
  -- `N (1 - u) ≥ 1` on the application range
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    rw [hNeq]
    have h1 : (1 : ℝ) ≤ d.W n := by exact_mod_cast hW1
    have h2 : (1 : ℝ) ≤ d.L n := by exact_mod_cast (by omega : 1 ≤ d.L n)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN : 1 ≤ (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * (1 - u)) := by
    have h1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    have h2 := Real.rpow_add hNpos 1 (-1 + τ)
    rw [Real.rpow_one, show (1 : ℝ) + (-1 + τ) = τ by ring] at h2
    calc (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ := h1
      _ = ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-1 + τ) := h2
      _ ≤ ((d.size n : ℕ) : ℝ) * (1 - u) :=
          mul_le_mul_of_nonneg_left (hRn.trans (by linarith)) hNpos.le
      _ = (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * (1 - u)) := by rw [hNeq]; ring
  have hΘ := kellStar_theta_far (d.L n) (d.W n) hL3 hW1 hc hBn hx1 hsq hu0 hu1 hN a b hfar
  refine ⟨hΘ, ?_⟩
  -- the pair is off the diagonal: `δ ℓ*_u > 0`
  have hab : a ≠ b := by
    intro hab
    have hz : (zdist2 (d.L n) (a - b) : ℝ) = 0 := by
      rw [hab, sub_self]; simp
    have hℓ := (ellT_pos_le (by omega : 1 ≤ d.L n) hu1).1
    have hpos : 0 < δ * ellStar (d.L n) (d.W n) u := by
      unfold ellStar
      have : 0 < Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_pos_of_pos (by linarith) _
      positivity
    linarith
  by_cases hu : u = 0
  · have hs : s = 0 := le_antisymm (hu ▸ hsu) hs0
    subst hu; subst hs
    have e : ukerMat (d.L n) 1 ((0 : ℝ)) ((0 : ℝ)) = Theta (d.L n) (((0 : ℝ)) : ℂ) := by
      simp [ukerMat]
    rw [e]
    exact hΘ
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have key := kellStar_uker_offdiag (d.L n) hL3 (s := s) hu0 hu1 hab
    have hn := congrArg norm key
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hn
    have hle : u * ‖ukerMat (d.L n) 1 s u a b‖ ≤ u * ‖Theta (d.L n) (u : ℂ) a b‖ := by
      rw [hn]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact (le_of_mul_le_mul_left hle hupos).trans hΘ

end RBM.Path
