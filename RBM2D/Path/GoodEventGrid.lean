/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodEvent
import RBM2D.Path.LemDecCalEdif
import RBM2D.Path.UTransport
import RBM2D.Path.KellStar
import RBM2D.Path.QVIdentity
import RBM2D.Path.QVForm
import RBM2D.Path.StepDecompLoop

/-!
# The linear part of the Step 2 good event on the grid

The deterministic Azuma proxy `cZ` and its variance bound `cZ_hbound`, the stopped conditional
sub-Gaussian input `hsubG_gridTauFull`, the threshold bound `thr_le_W`, the Azuma threshold `xZ`
and the Azuma event `highProb_azuma_grid'`.

For `d = 2` the proxy `cZ` is built on `lemDecCalE_dif` (inside `ℓ*`), `uopPairLocalMax` (the
double sum), `qvPropagated` (the QV identity) and `eeShift` (the one-step shift); the threshold
bound is `Θ ≤ W` (`thr_le_W`); labels are `Z2 L × Z2 L` (`L⁴` labels); `Uop` is taken at
`ξ = |m(E_n)|²`; the energy is a sequence `E`.

## Main declarations

* `cZ`, `cZ_nonneg`, `floor_le_cZ`, `cZ_hbound`: the proxy, its nonnegativity, its floor and its
  variance property.
* `hsubG_gridTauFull`: the stopped conditional sub-Gaussian input.
* `thr_le_W`: the threshold bound `Θ ≤ W`.
* `xZ`, `xZ_pos`, `xZ_sq`, `highProb_azuma_grid'`: the Azuma threshold and the Azuma event.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## The proxy `cZ` -/

/-- **The deterministic Azuma proxy `cZ`**.  With
`Δ = gridStep`, `u_i = gridTime … i`, `R = (1 - u_{j+1})/(1 - u_k)`, `ρ = ℓ_{u_j}/ℓ_{s_n}`,
`N = size n`, `Λ = N^ε`, `K₀ = 180·40002²(1 + log L)`, `Θ = thr(u_j)`:
`cZ = 2Δ[R⁴ B + 8 L⁴ W^{2-D'} N^ε ρ^{10} M_{u_j}^{-5} R³ + 16 R⁴ N² η_{u_{j+1}}^{-7} Δ]
  + Δ N^{-C_c}`,
`B = lossE2(Λ, K₀) e^{2 (log W)^{3/4}} [η_{u_j}^{-1} ρ^{10} 1(|a| ≤ 5ℓ*_{u_k})
  + η_{u_j}^{-1} ρ³ (M_{u_j}^{-1})^{1/2} Θ² + η_{u_k}^{-1} M_{u_k}^{-1} Θ³] 𝒯_{u_k}(|a|)²`. -/
def cZ (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (δ D ε D' Cc : ℝ) (n k : ℕ)
    (a : Z2 (d.L n) × Z2 (d.L n)) (j : ℕ) : ℝ :=
  2 * gridStep s v K n *
      (((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)) ^ 4 *
          (lossE2 (d.L n) (d.W n) (((d.size n : ℕ) : ℝ) ^ ε)
              (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) *
            Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4)) *
            ((etaT (E n) (gridTime s v K n j))⁻¹ *
                (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 10 *
                (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
                    5 * ellStar (d.L n) (d.W n) (gridTime s v K n k) then 1 else 0) +
              (etaT (E n) (gridTime s v K n j))⁻¹ *
                (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 3 *
                (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ ((1 : ℝ) / 2) *
                thr d E s δ n (gridTime s v K n j) ^ 2 +
              (etaT (E n) (gridTime s v K n k))⁻¹ *
                (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ *
                thr d E s δ n (gridTime s v K n j) ^ 3) *
            tailT (d.L n) (d.W n) (E n) D (gridTime s v K n k)
              (zdist2 (d.L n) (a.1 - a.2) : ℝ) ^ 2) +
        8 * (d.L n : ℝ) ^ 4 * (d.W n : ℝ) ^ (2 - D') * ((d.size n : ℕ) : ℝ) ^ ε *
          (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 10 *
          (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ 5 *
          ((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)) ^ 3 +
        16 * ((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)) ^ 4 *
          ((d.size n : ℕ) : ℝ) ^ 2 * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 7 *
          gridStep s v K n) +
    gridStep s v K n * ((d.size n : ℕ) : ℝ) ^ (-Cc)

variable {d}

/-- `u_{j+1} = u_j + Δ`. -/
private theorem GoodEventGrid_gridTime_succ (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) = gridTime s v K n j + gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- `s_n ≤ u_i`. -/
private theorem GoodEventGrid_le_gridTime {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (i : ℕ) : s n ≤ gridTime s v K n i := by
  have h := GoodEvent_gridTime_mono (K := K) hsv (Nat.zero_le i)
  rwa [GoodEvent_gridTime_zero] at h

/-- `0 ≤ lossE2` for `W ≥ 1`. -/
private theorem GoodEventGrid_lossE2_nonneg {L W : ℕ} (hW : 1 ≤ W) (Λ K₀ : ℝ) :
    0 ≤ lossE2 L W Λ K₀ := by
  have hlog : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
  unfold lossE2
  positivity

/-- **The floor of `cZ`**: `Δ N^{-C_c} ≤ cZ`. -/
theorem floor_le_cZ {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {δ D ε D' Cc : ℝ} {n k j : ℕ}
    (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1) (hk : k ≤ K n) (hj : j < k)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    gridStep s v K n * ((d.size n : ℕ) : ℝ) ^ (-Cc) ≤ cZ d E s v K δ D ε D' Cc n k a j := by
  have hΔ : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hlt : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le hsv hi).trans_lt hv1
  have hj1 : gridTime s v K n (j + 1) < 1 := hlt _ (by omega)
  have hjj : gridTime s v K n j < 1 := hlt _ (by omega)
  have hkk : gridTime s v K n k < 1 := hlt _ hk
  have hs1 : s n < 1 := (hsv).trans_lt hv1
  have h1 : 0 ≤ 1 - gridTime s v K n (j + 1) := by linarith
  have h2 : 0 < 1 - gridTime s v K n k := by linarith
  have e1 : 0 < etaT (E n) (gridTime s v K n j) := etaT_pos hE hjj
  have e2 : 0 < etaT (E n) (gridTime s v K n k) := etaT_pos hE hkk
  have e3 : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hE hj1
  have l1 : 0 < ellT (d.L n) (gridTime s v K n j) := (ellT_pos_le hL1 hjj).1
  have l2 : 0 < ellT (d.L n) (s n) := (ellT_pos_le hL1 hs1).1
  have m1 : 0 < scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) := scaleM_pos hL1 hW1 hE hjj
  have m2 : 0 < scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) := scaleM_pos hL1 hW1 hE hkk
  have hloss := GoodEventGrid_lossE2_nonneg (L := d.L n) hW1 (((d.size n : ℕ) : ℝ) ^ ε)
    (180 * 40002 ^ 2 * (1 + Real.log (d.L n)))
  unfold cZ
  refine le_add_of_nonneg_left ?_
  unfold thr
  positivity

/-- **`cZ ≥ 0`**. -/
theorem cZ_nonneg {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {δ D ε D' Cc : ℝ} {n k j : ℕ}
    (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1) (hk : k ≤ K n) (hj : j < k)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    0 ≤ cZ d E s v K δ D ε D' Cc n k a j := by
  have hΔ : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have h0 : 0 ≤ gridStep s v K n * ((d.size n : ℕ) : ℝ) ^ (-Cc) := by positivity
  exact h0.trans (floor_le_cZ hE hsv hv1 hk hj a)

/-! ## The threshold bound `Θ ≤ W` -/

/-- **`Θ(u) ≤ W`** on the window: `Θ(u) ≤ W^{1/200 + 8/30} ≤ W`, from
`CondStInd` (`r^{30} ≤ M_{s_n} ≤ W²`, `r = (1 - s_n)/(1 - t_n)`) and `Bandwidth`
(`N^δ ≤ W^{δ/c} ≤ W^{1/200}`). -/
theorem thr_le_W {E : ℕ → ℝ} {s t : ℕ → ℝ} {c δ : ℝ} (hE : ∀ n, |E n| < 2)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hc : 0 < c) (hband : Bandwidth d c)
    (hstep : CondStInd d E s t) (hδc : δ ≤ c / 200) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → thr d E s δ n u ≤ (d.W n : ℝ) := by
  filter_upwards [hband, hstep] with n hB hS u hsu hut
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hW1' : 1 ≤ d.W n := d.W_pos n
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hs1 : s n < 1 := (hst n).trans_lt (ht1 n)
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hxt : 0 < 1 - t n := by linarith [ht1 n]
  have hxs : 0 < 1 - s n := by linarith
  have hxu : 0 < 1 - u := by linarith
  -- the ratio `x = η_s/η_u = (1 - s)/(1 - u) ≤ r`
  set x : ℝ := etaT (E n) (s n) / etaT (E n) u with hxdef
  have hx : x = (1 - s n) / (1 - u) := etaT_div_etaT (hE n) hs1 hu1
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  set r : ℝ := (1 - s n) / (1 - t n) with hrdef
  have hxr : x ≤ r := by
    rw [hx, hrdef]
    exact div_le_div_of_nonneg_left hxs.le hxt (by linarith)
  have hr0 : 0 < r := by positivity
  -- `r^30 ≤ M_s ≤ W²`
  have hMs : 0 < scaleM (d.L n) (d.W n) (E n) (s n) := scaleM_pos hL1 hW1' (hE n) hs1
  have hr30 : r ^ 30 ≤ scaleM (d.L n) (d.W n) (E n) (s n) := by
    have e : ((1 - t n) / (1 - s n)) ^ 30 = (r ^ 30)⁻¹ := by
      rw [hrdef, ← inv_pow, inv_div]
    rw [e] at hS
    exact (inv_le_inv₀ hMs (by positivity)).1 hS
  have hMW : scaleM (d.L n) (d.W n) (E n) (s n) ≤ (d.W n : ℝ) ^ 2 :=
    LemDecCalE_scaleM_le_sq hL1 (hE n) hs1
  have hx30 : x ^ 30 ≤ (d.W n : ℝ) ^ 2 :=
    ((pow_le_pow_left₀ hx0 hxr 30).trans hr30).trans hMW
  -- `x⁴ ≤ W^{8/30}`
  have hx4 : x ^ 4 ≤ (d.W n : ℝ) ^ ((8 : ℝ) / 30) := by
    have h1 : (x ^ 30) ^ ((4 : ℝ) / 30) ≤ ((d.W n : ℝ) ^ 2) ^ ((4 : ℝ) / 30) :=
      Real.rpow_le_rpow (by positivity) hx30 (by norm_num)
    have e1 : (x ^ 30) ^ ((4 : ℝ) / 30) = x ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
      norm_num
    have e2 : ((d.W n : ℝ) ^ 2) ^ ((4 : ℝ) / 30) = (d.W n : ℝ) ^ ((8 : ℝ) / 30) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      norm_num
    rw [e1, e2] at h1
    exact h1
  -- `N^δ ≤ W^{1/200}`
  have hNδ : ((d.size n : ℕ) : ℝ) ^ δ ≤ (d.W n : ℝ) ^ ((1 : ℝ) / 200) := by
    rcases le_or_gt 0 δ with hδ0 | hδ0
    · have h1 : (((d.size n : ℕ) : ℝ) ^ c) ^ (δ / c) ≤ (d.W n : ℝ) ^ (δ / c) :=
        Real.rpow_le_rpow (by positivity) hB (div_nonneg hδ0 hc.le)
      have e1 : (((d.size n : ℕ) : ℝ) ^ c) ^ (δ / c) = ((d.size n : ℕ) : ℝ) ^ δ := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        field_simp
      rw [e1] at h1
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le hW1 ?_)
      rw [div_le_iff₀ hc]
      linarith
    · calc ((d.size n : ℕ) : ℝ) ^ δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 hδ0.le
        _ ≤ (d.W n : ℝ) ^ ((1 : ℝ) / 200) := Real.one_le_rpow hW1 (by norm_num)
  unfold thr
  rw [← hxdef]
  calc ((d.size n : ℕ) : ℝ) ^ δ * x ^ 4
      ≤ (d.W n : ℝ) ^ ((1 : ℝ) / 200) * (d.W n : ℝ) ^ ((8 : ℝ) / 30) :=
        mul_le_mul hNδ hx4 (by positivity) (by positivity)
    _ = (d.W n : ℝ) ^ ((1 : ℝ) / 200 + 8 / 30) := (Real.rpow_add hW0 _ _).symm
    _ ≤ (d.W n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    _ = (d.W n : ℝ) := Real.rpow_one _

/-! ## Helpers of the variance chain -/

section Helpers

open scoped Matrix.Norms.L2Operator

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The derivative of a real-weighted sum of differentiable observables (the `Fintype`/
`DecidableEq` instances are those of the `L2Operator` norm used by `gradMat`'s callers). -/
private theorem GoodEventGrid_hasFDerivAt_sum {ι κι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κι] {Φ : κι → Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hd : ∀ c, DifferentiableAt ℝ (Φ c) M) (κ : κι → ℝ) :
    HasFDerivAt (fun M' => ∑ c, (κ c : ℂ) * Φ c M')
      (∑ c, (κ c : ℂ) • fderiv ℝ (Φ c) M) M :=
  HasFDerivAt.fun_sum (u := Finset.univ) (A := fun c M' => (κ c : ℂ) * Φ c M')
    (A' := fun c => (κ c : ℂ) • fderiv ℝ (Φ c) M) fun c _ =>
      (hd c).hasFDerivAt.const_mul (κ c : ℂ)

set_option linter.unusedFintypeInType false in
/-- `gradMat` is linear under real weights: `gradMat (Σ_c κ_c Φ_c) M = Σ_c κ_c gradMat Φ_c M`. -/
private theorem GoodEventGrid_gradMat_sum {ι κι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κι] {Φ : κι → Matrix ι ι ℂ → ℂ} {M : Matrix ι ι ℂ}
    (hd : ∀ c, DifferentiableAt ℝ (Φ c) M) (κ : κι → ℝ) :
    gradMat (fun M' => ∑ c, (κ c : ℂ) * Φ c M') M = ∑ c, (κ c : ℂ) • gradMat (Φ c) M := by
  have hf := (GoodEventGrid_hasFDerivAt_sum hd κ).fderiv
  ext i j
  simp only [gradMat, hf, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · rw [Finset.mul_sum _ _ Complex.I, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

/-- `fderiv Φ_c M X = loopDeriv(M, X, c)` for the two-loop observable at a Hermitian `M`. -/
private theorem GoodEventGrid_fderiv_loop (n : ℕ) {E u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hE : |E| < 2) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hM : M.IsHermitian) (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (c : Z2 (d.L n) × Z2 (d.L n)) :
    fderiv ℝ (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        gloop (d.L n) (d.W n) (blockMat M') (spectralZ E u) (pmLoop c.1 c.2)) M X
      = loopDeriv (d.L n) (d.W n) E u M X c := by
  have hd := ((hermTestFun_loopPM d n E u hu0 hu1 hE c).1.contDiffAt M hM).differentiableAt
    (by norm_num)
  have hF' : HasFDerivAt (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        gloop (d.L n) (d.W n) (blockMat M') (spectralZ E u) (pmLoop c.1 c.2))
      (fderiv ℝ (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        gloop (d.L n) (d.W n) (blockMat M') (spectralZ E u) (pmLoop c.1 c.2)) M)
      ((fun y : ℝ => M + (y : ℂ) • X) 0) := by
    simpa using hd.hasFDerivAt
  have h := hF'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line M X 0)
  unfold loopDeriv loopPM
  exact h.deriv.symm

/-- **The variance chain**: for real weights `κ`, at a Hermitian `M` and `0 ≤ u < 1`,
`linTrVar(Σ_c κ_c gradMat Φ_c M) ≤ 2 Re Σ_{b,b'} κ_b κ_{b'} (𝓔⊗𝓔)_u(M)_{b,b'}`
(`v_gradMat_eq_quadVar`, `qvPropagated`). -/
private theorem GoodEventGrid_linTrVar_le (n : ℕ) {E u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hE : |E| < 2) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hM : M.IsHermitian) (κ : Z2 (d.L n) × Z2 (d.L n) → ℝ) :
    linTrVar n (∑ c : Z2 (d.L n) × Z2 (d.L n), (κ c : ℂ) • gradMat
        (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          gloop (d.L n) (d.W n) (blockMat M') (spectralZ E u) (pmLoop c.1 c.2)) M)
      ≤ 2 * (∑ b : Z2 (d.L n) × Z2 (d.L n), ∑ b' : Z2 (d.L n) × Z2 (d.L n),
          (κ b : ℂ) * (starRingEnd ℂ) (κ b' : ℂ) * EE (d.L n) (d.W n) E u M b b').re := by
  set Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ :=
    fun c M' => gloop (d.L n) (d.W n) (blockMat M') (spectralZ E u) (pmLoop c.1 c.2) with hΦ
  have hd : ∀ c, DifferentiableAt ℝ (Φ c) M := fun c =>
    ((hermTestFun_loopPM d n E u hu0 hu1 hE c).1.contDiffAt M hM).differentiableAt (by norm_num)
  have hsum := GoodEventGrid_hasFDerivAt_sum hd κ
  rw [← GoodEventGrid_gradMat_sum hd κ]
  have hReal : ∀ A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ, A.IsHermitian →
      (∑ c, (κ c : ℂ) * Φ c A).im = 0 := by
    intro A hA
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Complex.im_ofReal_mul, hΦ]
    simp only
    rw [loopPM_real_of_herm d n E u c hA, mul_zero]
  rw [v_gradMat_eq_quadVar d n hsum.differentiableAt hReal hM, hsum.fderiv]
  have hfd : ∀ X, (∑ c, (κ c : ℂ) • fderiv ℝ (Φ c) M) X
      = ∑ c, (κ c : ℂ) * loopDeriv (d.L n) (d.W n) E u M X c := by
    intro X
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΦ,
      GoodEventGrid_fderiv_loop n hu0 hu1 hE hM X c]
  simp_rw [hfd]
  exact qvPropagated (d.L n) (d.W n) E u (d.three_le_L n) hE hu0 hu1 M hM (fun c => (κ c : ℂ))

end Helpers

/-- On the good set, `‖(𝓔⊗𝓔)_u(M)_{b,b'}‖ ≤ 2 W² L² Λ ρ^{10} M_u^{-5}` for all labels
(`goodSet` at `k = 6`, `sum_norm_SB_row`). -/
private theorem GoodEventGrid_norm_EE_le {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {E s u Λ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ goodSet L W E s u Λ)
    (b b' : Z2 L × Z2 L) :
    ‖EE L W E u M b b'‖ ≤
      2 * (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * Λ * (ellT L u / ellT L s) ^ 10 *
        (scaleM L W E u)⁻¹ ^ 5 := by
  obtain ⟨-, hloop, -⟩ := hM
  set B : ℝ := Λ * (ellT L u / ellT L s) ^ 10 * (scaleM L W E u)⁻¹ ^ 5 with hB
  have h6 : ∀ (σ : Fin 6 → Bool) (x : Fin 6 → Z2 L), ‖loop6 L W E u M σ x‖ ≤ B := by
    intro σ x
    exact hloop 6 (by simp) σ x
  unfold EE
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ x : Z2 L, ∑ y : Z2 L, SB L x y *
      (loop6 L W E u M ![true, false, true, false, true, false] ![b.1, b.2, y, b'.2, b'.1, x] +
        loop6 L W E u M ![false, true, false, true, false, true] ![b.2, b.1, y, b'.1, b'.2, x])‖
      ≤ ∑ x : Z2 L, ∑ y : Z2 L, ‖SB L x y‖ * (2 * B) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => ?_))
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    linarith [h6 ![true, false, true, false, true, false] ![b.1, b.2, y, b'.2, b'.1, x],
      h6 ![false, true, false, true, false, true] ![b.2, b.1, y, b'.1, b'.2, x]]
  have hrow : ∑ x : Z2 L, ∑ y : Z2 L, ‖SB L x y‖ * (2 * B) = (L : ℝ) ^ 2 * (2 * B) := by
    simp_rw [← Finset.sum_mul, KLoop.sum_norm_SB_row L hL]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
    push_cast
    ring
  rw [hrow] at hsum
  calc (W : ℝ) ^ 2 * ‖_‖ ≤ (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * B)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [hB]; ring

/-- The kernel at `ξ = 1` is real and `≥ 0`, so is the product of two of its entries. -/
private theorem GoodEventGrid_P_real {L : ℕ} [NeZero L] (hL : 3 ≤ L) {u w : ℝ} (hu0 : 0 ≤ u)
    (huw : u ≤ w) (hw1 : w < 1) (a b : Z2 L × Z2 L) :
    (ukerMat L 1 u w a.1 b.1 * ukerMat L 1 u w a.2 b.2).im = 0 ∧
      0 ≤ (ukerMat L 1 u w a.1 b.1 * ukerMat L 1 u w a.2 b.2).re := by
  have h := ukerNonneg L hL 1 u w zero_le_one hu0 huw (by linarith)
  simp only [Complex.ofReal_one] at h
  obtain ⟨h1i, h1r⟩ := h a.1 b.1
  obtain ⟨h2i, h2r⟩ := h a.2 b.2
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_im, h1i, h2i]; ring
  · rw [Complex.mul_re, h1i, h2i]; simpa using mul_nonneg h1r h2r

/-- The row sum of the product kernel at `ξ = 1`: `Σ_b Re(𝒰(a₁,b₁)𝒰(a₂,b₂)) = ((1-u)/(1-w))²`
(`ukerRowSum`). -/
private theorem GoodEventGrid_weight_sum {L : ℕ} [NeZero L] (hL : 3 ≤ L) {u w : ℝ} (hu0 : 0 ≤ u)
    (huw : u ≤ w) (hw1 : w < 1) (a : Z2 L × Z2 L) :
    ∑ b : Z2 L × Z2 L, (ukerMat L 1 u w a.1 b.1 * ukerMat L 1 u w a.2 b.2).re
      = ((1 - u) / (1 - w)) ^ 2 := by
  have hr : ∀ c : Z2 L, ∑ b : Z2 L, ukerMat L 1 u w c b = (((1 - u) / (1 - w) : ℝ) : ℂ) := by
    intro c
    have h := ukerRowSum L hL 1 u w zero_le_one (hu0.trans huw) (by linarith) c
    rw [Complex.ofReal_one] at h
    simpa only [mul_one] using h
  rw [← Complex.re_sum, Fintype.sum_prod_type]
  simp only
  rw [← Finset.sum_mul_sum, hr, hr]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The one-step shift of the propagated QV: for a real nonnegative weight `P`,
`Re Σ P_b P_{b'} A_{bb'} ≤ ‖Σ P_b P_{b'} B_{bb'}‖ + (Σ_b P_b)² C` when `‖A - B‖ ≤ C`
entrywise. -/
private theorem GoodEventGrid_shift_le {ι : Type*} [Fintype ι] (P : ι → ℂ)
    (hP : ∀ b, (P b).im = 0 ∧ 0 ≤ (P b).re) (A B : ι → ι → ℂ) {C : ℝ}
    (hAB : ∀ b b', ‖A b b' - B b b'‖ ≤ C) :
    (∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * A b b').re ≤
      ‖∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * B b b'‖ + (∑ b, (P b).re) ^ 2 * C := by
  have hnorm : ∀ b, ‖P b‖ = (P b).re := by
    intro b
    have e : P b = ((P b).re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im, (hP b).1])
    rw [e, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (hP b).2]
  have hsplit : (∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * A b b') =
      (∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * B b b') +
        ∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * (A b b' - B b b') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have hdiff : ‖∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * (A b b' - B b b')‖ ≤
      ∑ b, ∑ b', (P b).re * (P b').re * C := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj, hnorm, hnorm]
    exact mul_le_mul_of_nonneg_left (hAB b b') (mul_nonneg (hP b).2 (hP b').2)
  have hsq : ∑ b, ∑ b', (P b).re * (P b').re * C = (∑ b, (P b).re) ^ 2 * C := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  rw [hsplit, Complex.add_re]
  have h1 := Complex.re_le_norm (∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * B b b')
  have h2 := Complex.re_le_norm (∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * (A b b' - B b b'))
  linarith

/-! ### Periodic distance helpers -/

private theorem GoodEventGrid_zdist_neg {L : ℕ} [NeZero L] (u : ZMod L) :
    zdist L (-u) = zdist L u := by
  have hu : u.val < L := ZMod.val_lt u
  by_cases h : u = 0
  · subst h; simp
  · have hneg : (-u).val = L - u.val := by rw [ZMod.neg_val]; simp [h]
    simp only [zdist, hneg]
    omega

private theorem GoodEventGrid_zdist2_neg {L : ℕ} [NeZero L] (u : Z2 L) :
    zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, GoodEventGrid_zdist_neg]

/-- `|y - z| ≤ |x - y| + |x - z|`. -/
private theorem GoodEventGrid_zdist2_sub_le {L : ℕ} [NeZero L] (x y z : Z2 L) :
    zdist2 L (y - z) ≤ zdist2 L (x - y) + zdist2 L (x - z) := by
  have h : y - z = -(x - y) + (x - z) := by abel
  rw [h]
  refine (zdist2_add_le L _ _).trans ?_
  rw [GoodEventGrid_zdist2_neg]

/-- `|a₁ - a₂| ≤ |a₁ - b₁| + |b₁ - b₂| + |a₂ - b₂|`. -/
private theorem GoodEventGrid_zdist2_tri {L : ℕ} [NeZero L] (a₁ a₂ b₁ b₂ : Z2 L) :
    zdist2 L (a₁ - a₂) ≤ zdist2 L (a₁ - b₁) + zdist2 L (b₁ - b₂) + zdist2 L (a₂ - b₂) := by
  have h : a₁ - a₂ = (a₁ - b₁) + (b₁ - b₂) + -(a₂ - b₂) := by abel
  rw [h]
  refine (zdist2_add_le L _ _).trans ?_
  have := zdist2_add_le L (a₁ - b₁) (b₁ - b₂)
  rw [GoodEventGrid_zdist2_neg]
  omega

/-- **The near bound**: when the four distances `|a_i - b_i|`, `|a_i - b'_i|` are `< ℓ*_w/2`,
`lemDecCalE_dif` at `(b, b')` and `J* ≤ Θ` give `‖(𝓔⊗𝓔)_u(M)_{b,b'}‖ ≤ B(a)`, the `B` of `cZ`. -/
private theorem GoodEventGrid_near {L W : ℕ} [NeZero L] [NeZero W] {E s u w D Λ K₀ Θ : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hE2 : E2Hyp L W E s u w D Λ K₀ M)
    (hJ : jStarMat L W E D u M ≤ Θ) (a b b' : Z2 L × Z2 L)
    (h1 : (zdist2 L (a.1 - b.1) : ℝ) < ellStar L W w / 2)
    (h2 : (zdist2 L (a.2 - b.2) : ℝ) < ellStar L W w / 2)
    (h3 : (zdist2 L (a.1 - b'.1) : ℝ) < ellStar L W w / 2)
    (h4 : (zdist2 L (a.2 - b'.2) : ℝ) < ellStar L W w / 2) :
    ‖EE L W E u M b b'‖ ≤ lossE2 L W Λ K₀ * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
      ((etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 5 * ellStar L W w then 1 else 0) +
        (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * Θ ^ 2 +
        (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ * Θ ^ 3) *
      tailT L W E D w (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := by
  have hW1 : 1 ≤ W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨-, hE, -, hsu, huw, hw1, -⟩ := id hE2
  have hu1 : u < 1 := huw.trans_lt hw1
  have hs1 : s < 1 := hsu.trans_lt hu1
  -- the distance facts
  have hb1 : (zdist2 L (b.1 - b'.1) : ℝ) ≤ ellStar L W w := by
    have := GoodEventGrid_zdist2_sub_le a.1 b.1 b'.1
    have h : (zdist2 L (b.1 - b'.1) : ℝ) ≤ (zdist2 L (a.1 - b.1) : ℝ) + zdist2 L (a.1 - b'.1) := by
      exact_mod_cast this
    linarith
  have hb2 : (zdist2 L (b.2 - b'.2) : ℝ) ≤ ellStar L W w := by
    have := GoodEventGrid_zdist2_sub_le a.2 b.2 b'.2
    have h : (zdist2 L (b.2 - b'.2) : ℝ) ≤ (zdist2 L (a.2 - b.2) : ℝ) + zdist2 L (a.2 - b'.2) := by
      exact_mod_cast this
    linarith
  have hab : (zdist2 L (a.1 - a.2) : ℝ) < zdist2 L (b.1 - b.2) + ellStar L W w := by
    have := GoodEventGrid_zdist2_tri a.1 a.2 b.1 b.2
    have h : (zdist2 L (a.1 - a.2) : ℝ) ≤
        (zdist2 L (a.1 - b.1) : ℝ) + zdist2 L (b.1 - b.2) + zdist2 L (a.2 - b.2) := by
      exact_mod_cast this
    linarith
  have hdif := lemDecCalE_dif L W E s u w D Λ K₀ M hE2 b b' hb1 hb2
  -- nonnegativity
  have hloss : 0 ≤ lossE2 L W Λ K₀ := GoodEventGrid_lossE2_nonneg hW1 Λ K₀
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hηw : 0 < etaT E w := etaT_pos hE hw1
  have hℓu : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have hℓs : 0 < ellT L s := (ellT_pos_le hL1 hs1).1
  have hMu : 0 < scaleM L W E u := scaleM_pos hL1 hW1 hE hu1
  have hMw : 0 < scaleM L W E w := scaleM_pos hL1 hW1 hE hw1
  have hJ1 : 1 ≤ jStarMat L W E D u M := one_le_jStarMat L W hW1 E D u M
  have hJ0 : 0 ≤ jStarMat L W E D u M := by linarith
  have hJ2 : jStarMat L W E D u M ^ 2 ≤ Θ ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
  have hJ3 : jStarMat L W E D u M ^ 3 ≤ Θ ^ 3 := pow_le_pow_left₀ hJ0 hJ 3
  have hind : (if (zdist2 L (b.1 - b.2) : ℝ) ≤ 4 * ellStar L W w then (1 : ℝ) else 0) ≤
      (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 5 * ellStar L W w then 1 else 0) := by
    split_ifs with hb ha
    · exact le_rfl
    · exfalso; exact ha (by linarith)
    · exact zero_le_one
    · exact le_rfl
  have hX : (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
          (if (zdist2 L (b.1 - b.2) : ℝ) ≤ 4 * ellStar L W w then 1 else 0) +
        (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
          jStarMat L W E D u M ^ 2 +
        (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ * jStarMat L W E D u M ^ 3 ≤
      (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 5 * ellStar L W w then 1 else 0) +
        (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * Θ ^ 2 +
        (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ * Θ ^ 3 := by
    have c1 : 0 ≤ (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 := by positivity
    have c2 : 0 ≤ (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 *
        (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := by
      positivity
    have c3 : 0 ≤ (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ := by positivity
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hind c1)
      (mul_le_mul_of_nonneg_left hJ2 c2)) (mul_le_mul_of_nonneg_left hJ3 c3)
  have hX0 : 0 ≤ (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
          (if (zdist2 L (b.1 - b.2) : ℝ) ≤ 4 * ellStar L W w then 1 else 0) +
        (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
          jStarMat L W E D u M ^ 2 +
        (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ * jStarMat L W E D u M ^ 3 := by positivity
  -- the tail comparison
  have hT1 : tailT L W E D w (zdist2 L (b.1 - b.2) : ℝ) ≤
      tailT L W E D w ((zdist2 L (a.1 - a.2) : ℝ) - ellStar L W w) :=
    LemDecCalE_tailT_anti hL1 hw1 (by linarith)
  have hT2 := LemDecCalE_e4c (L := L) (W := W) (E := E) (D := D) hw1 zero_le_one
    (zdist2 L (a.1 - a.2) : ℝ)
  simp only [Real.sqrt_one, one_mul] at hT2
  have hTb0 : 0 ≤ tailT L W E D w (zdist2 L (b.1 - b.2) : ℝ) := (tailT_pos hW1 _ _ _ _ _).le
  have hT : tailT L W E D w (zdist2 L (b.1 - b.2) : ℝ) ^ 2 ≤
      Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
        tailT L W E D w (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hTb0 (hT1.trans hT2) 2
    have e : (Real.exp (Real.log W ^ ((3 : ℝ) / 4)) *
        tailT L W E D w (zdist2 L (a.1 - a.2) : ℝ)) ^ 2 =
        Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
          tailT L W E D w (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    rw [e] at h
    exact h
  refine hdif.trans ?_
  calc lossE2 L W Λ K₀ * _ * tailT L W E D w (zdist2 L (b.1 - b.2) : ℝ) ^ 2
      ≤ lossE2 L W Λ K₀ * ((etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 5 * ellStar L W w then 1 else 0) +
        (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * Θ ^ 2 +
        (etaT E w)⁻¹ * (scaleM L W E w)⁻¹ * Θ ^ 3) *
          (Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
            tailT L W E D w (zdist2 L (a.1 - a.2) : ℝ) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hloss) hT (sq_nonneg _)
          (mul_nonneg hloss (hX0.trans hX))
    _ = _ := by ring

/-! ### The eventual environment of the standing hypotheses -/

/-- Eventually in `n`: `4 ≤ log W`, the `E2Hyp` floor `L² W¹² ≤ W^{D/2}`, `Θ ≤ W` on the window,
the step condition at `n`, and the two `kellStarEv` instances (`δ = 1/8` at `D`, for `Kpm`;
`δ = 1/2` at `D'`, for `UkerFar`). -/
private theorem GoodEventGrid_env {E : ℕ → ℝ} {s t : ℕ → ℝ} {c τ' δ D : ℝ}
    (hE : ∀ n, |E n| < 2) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hc : 0 < c)
    (hband : Bandwidth d c) (hτ' : 0 < τ') (hrange : RangeCond d τ' t)
    (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d) (hδc : δ ≤ c / 200)
    (hD : 20 + 2 / c ≤ D) (D' : ℝ) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log (d.W n : ℝ) ∧
      (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12 ≤ (d.W n : ℝ) ^ (D / 2) ∧
      (∀ u : ℝ, s n ≤ u → u ≤ t n → thr d E s δ n u ≤ (d.W n : ℝ)) ∧
      (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ ((1 - t n) / (1 - s n)) ^ 30 ∧
      (∀ s' u : ℝ, 0 ≤ s' → s' ≤ u → u ≤ t n → ∀ a b : Z2 (d.L n),
        1 / 8 * ellStar (d.L n) (d.W n) u ≤ (zdist2 (d.L n) (a - b) : ℝ) →
          ‖Theta (d.L n) (u : ℂ) a b‖ ≤ (d.W n : ℝ) ^ (-D)) ∧
      (∀ s' u : ℝ, 0 ≤ s' → s' ≤ u → u ≤ t n → ∀ a b : Z2 (d.L n),
        1 / 2 * ellStar (d.L n) (d.W n) u ≤ (zdist2 (d.L n) (a - b) : ℝ) →
          ‖ukerMat (d.L n) 1 s' u a b‖ ≤ (d.W n : ℝ) ^ (-D')) := by
  have hT : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.1 hsize
  have hK1 := kellStarEv d c τ' (1 / 8) D t hc hτ' (by norm_num) hT hband hrange ht1
  have hK2 := kellStarEv d c τ' (1 / 2) D' t hc hτ' (by norm_num) hT hband hrange ht1
  have hNc : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp hsize
  have hWtop : Tendsto (fun n => (d.W n : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNc
  have hlog : ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log (d.W n : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtop).eventually_ge_atTop 4
  filter_upwards [hlog, hband, thr_le_W hE hst ht1 hc hband hstep hδc, hstep, hK1, hK2]
    with n hlogn hB hthr hS hk1 hk2
  refine ⟨hlogn, ?_, hthr, hS, fun s' u h0 h1 h2 a b hab => (hk1 s' u h0 h1 h2 a b hab).1,
    fun s' u h0 h1 h2 a b hab => (hk2 s' u h0 h1 h2 a b hab).2⟩
  -- the `E2Hyp` floor
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hNW : ((d.size n : ℕ) : ℝ) ≤ (d.W n : ℝ) ^ (1 / c) := by
    have h1 : (((d.size n : ℕ) : ℝ) ^ c) ^ (1 / c) ≤ (d.W n : ℝ) ^ (1 / c) :=
      Real.rpow_le_rpow (by positivity) hB (by positivity)
    rwa [← Real.rpow_mul hN0, mul_one_div_cancel hc.ne', Real.rpow_one] at h1
  have hexp : 1 / c + 10 ≤ D / 2 := by
    have : 2 / c = 2 * (1 / c) := by ring
    linarith
  calc (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12 = ((d.size n : ℕ) : ℝ) * (d.W n : ℝ) ^ (10 : ℝ) := by
        rw [hNeq, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    _ ≤ (d.W n : ℝ) ^ (1 / c) * (d.W n : ℝ) ^ (10 : ℝ) :=
        mul_le_mul_of_nonneg_right hNW (by positivity)
    _ = (d.W n : ℝ) ^ (1 / c + 10) := (Real.rpow_add hW0 _ _).symm
    _ ≤ (d.W n : ℝ) ^ (D / 2) := Real.rpow_le_rpow_of_exponent_le hW1 hexp

/-! ### The variance bound `cZ_hbound` -/

/-- **The `hbound` property of `cZ`** (the variance input of
`stepDecomp_Z_subG_loopPM` with `E := E n`, `u := v := u_{j+1}`, `w := u_k`, `b := a`,
`S := {j < gridTauFull}`, `c := cZ`).  Eventually in `n`, for all `k ≤ K_n`, labels `a`, `j < k`
and `ω` with `j < gridTauFull(ω)`: `Δ · linTrVar(Ab) ≤ cZ`.  Proof: `lt_gridTauFull_imp`; the
variance chain (`v_gradMat_eq_quadVar`, `qvPropagated`); the
shift `eeShift` from `u_{j+1}` to `u_j`; `uopPairLocalMax` with `UkerFar` from `kellStarEv`,
the far bound from `goodSet` and the near bound from `lemDecCalE_dif` (`E2Hyp` assembled from
the standing hypotheses) and `J* < Θ(u_j)`. -/
theorem cZ_hbound {E : ℕ → ℝ} {s v t : ℕ → ℝ} {c τ' δ D ε : ℝ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hc : 0 < c) (hband : Bandwidth d c) (hτ' : 0 < τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    (hδc : δ ≤ c / 200) (hD : 20 + 2 / c ≤ D) (hε : 0 ≤ ε) (D' Cc : ℝ) (K : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n), ∀ j < k,
      ∀ ω ∈ {ω : PathΩ d | j < gridTauFull d E s v K δ D ε n ω},
        gridStep s v K n * linTrVar n (Ab d s v K n j
          (fun (b : Z2 (d.L n) × Z2 (d.L n))
              (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ (E n) (gridTime s v K n (j + 1)))
              (pmLoop b.1 b.2))
          (fun b b' => (ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.1 b'.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.2 b'.2).re) a ω)
          ≤ cZ d E s v K δ D ε D' Cc n k a j := by
  have hst : ∀ n, s n ≤ t n := fun n => (hsv n).trans (hvt n)
  filter_upwards [GoodEventGrid_env hE hst ht1 hc hband hτ' hrange hstep hsize hδc hD D']
    with n ⟨hlogW, hLW, hthr, hS, hK1, hK2⟩ k hk a j hj ω hω
  obtain ⟨hJ, hG⟩ := lt_gridTauFull_imp (show j < gridTauFull d E s v K δ D ε n ω from hω)
  have hEn := hE n
  have hL3 := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hW1' : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hξ : ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) = 1 := by
    rw [normSqSpectralMOne _ hEn.le, Complex.ofReal_one]
  simp only [hξ]
  unfold cZ
  -- the grid times
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hsucc := GoodEventGrid_gridTime_succ s v K n j
  have hsuj : s n ≤ gridTime s v K n j := GoodEventGrid_le_gridTime (hsv n) j
  have huj0 : 0 ≤ gridTime s v K n j := (hs0 n).trans hsuj
  have hujU : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    GoodEvent_gridTime_mono (hsv n) (Nat.le_succ j)
  have huw : gridTime s v K n (j + 1) ≤ gridTime s v K n k := GoodEvent_gridTime_mono (hsv n) hj
  have hwv : gridTime s v K n k ≤ v n := GoodEvent_gridTime_le (hsv n) hk
  have hwt : gridTime s v K n k ≤ t n := hwv.trans (hvt n)
  have hw1 : gridTime s v K n k < 1 := hwt.trans_lt (ht1 n)
  have hu1 : gridTime s v K n (j + 1) < 1 := huw.trans_lt hw1
  have hu0 : 0 ≤ gridTime s v K n (j + 1) := huj0.trans hujU
  have huj1 : gridTime s v K n j < 1 := hujU.trans_lt hu1
  have hujt : gridTime s v K n j ≤ t n := (hujU.trans huw).trans hwt
  have hujw : gridTime s v K n j ≤ gridTime s v K n k := hujU.trans huw
  have hsw : s n ≤ gridTime s v K n k := hsuj.trans hujw
  have hM : (pathH d s v K n j ω).IsHermitian := pathH_isHermitian d s v K n j ω
  -- abbreviations
  set Δ := gridStep s v K n with hΔdef
  set uj := gridTime s v K n j with hujdef
  set u := gridTime s v K n (j + 1) with hudef
  set w := gridTime s v K n k with hwdef
  set M := pathH d s v K n j ω with hMdef
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Λ : ℝ := N ^ ε with hΛdef
  set K₀ : ℝ := 180 * 40002 ^ 2 * (1 + Real.log (d.L n)) with hK₀def
  set Θ := thr d E s δ n uj with hΘdef
  set R : ℝ := (1 - u) / (1 - w) with hRdef
  set ρ : ℝ := ellT (d.L n) uj / ellT (d.L n) (s n) with hρdef
  set P : Z2 (d.L n) × Z2 (d.L n) → ℂ :=
    fun b => ukerMat (d.L n) 1 u w a.1 b.1 * ukerMat (d.L n) 1 u w a.2 b.2 with hPdef
  have hP : ∀ b, (P b).im = 0 ∧ 0 ≤ (P b).re := fun b =>
    GoodEventGrid_P_real hL3 hu0 huw hw1 a b
  have hPre : ∀ b, ((P b).re : ℂ) = P b := fun b =>
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, (hP b).1])
  have hPsum : ∑ b, (P b).re = R ^ 2 := GoodEventGrid_weight_sum hL3 hu0 huw hw1 a
  -- the variance chain
  have hA := GoodEventGrid_linTrVar_le n hu0 hu1 hEn hM (fun b => (P b).re)
  have hsumeq : (∑ b : Z2 (d.L n) × Z2 (d.L n), ∑ b' : Z2 (d.L n) × Z2 (d.L n),
      ((P b).re : ℂ) * (starRingEnd ℂ) ((P b').re : ℂ) * EE (d.L n) (d.W n) (E n) u M b b') =
      ∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * EE (d.L n) (d.W n) (E n) u M b b' := by
    simp only [hPre]
  rw [hsumeq] at hA
  -- the shift from `u = u_j + Δ` to `u_j`
  have hshift : ∀ b b', ‖EE (d.L n) (d.W n) (E n) u M b b' - EE (d.L n) (d.W n) (E n) uj M b b'‖
      ≤ 16 * N ^ 2 * (etaT (E n) u)⁻¹ ^ 7 * Δ := by
    intro b b'
    have h := eeShift (d.L n) (d.W n) (E n) uj Δ hL3 hEn huj0 hΔ0 (by rw [← hsucc]; exact hu1)
      M hM b b'
    rw [← hsucc] at h
    exact h
  have hB := GoodEventGrid_shift_le P hP (EE (d.L n) (d.W n) (E n) u M)
    (EE (d.L n) (d.W n) (E n) uj M) hshift
  -- `E2Hyp` at `(s_n, u_j, u_k)`
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hN1 hε
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ Real.log (d.L n : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
    rw [hK₀def]; nlinarith
  have hMw : 1 ≤ scaleM (d.L n) (d.W n) (E n) w := by
    have h29 := scaleM_ge_pow29 hL1 hW1 hEn (hs0 n) hsw hwt (ht1 n) hS
    have hr : 1 ≤ (1 - s n) / (1 - w) := by
      rw [one_le_div (by linarith)]; linarith
    exact (one_le_pow₀ hr).trans h29
  have hJW : jStarMat (d.L n) (d.W n) (E n) D uj M ≤ (d.W n : ℝ) :=
    hJ.le.trans (hthr uj hsuj hujt)
  have hKfar : ∀ x y : Z2 (d.L n), ellStar (d.L n) (d.W n) uj / 8 ≤ (zdist2 (d.L n) (x - y) : ℝ) →
      ‖Kpm (d.L n) (d.W n) (E n) uj x y‖ ≤ (d.W n : ℝ) ^ (-D) := by
    intro x y hxy
    have hth := hK1 uj uj huj0 le_rfl hujt x y (by linarith)
    have hξ' : (Complex.normSq (spectralM (E n)) : ℂ) = 1 := by
      rw [normSqSpectralMOne _ hEn.le, Complex.ofReal_one]
    unfold Kpm
    rw [hξ', mul_one, mul_one, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    have hWi : ((d.W n : ℝ)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1')
    calc ((d.W n : ℝ)⁻¹) ^ 2 * ‖Theta (d.L n) (uj : ℂ) x y‖ ≤ 1 * ‖Theta (d.L n) (uj : ℂ) x y‖ :=
          mul_le_mul_of_nonneg_right hWi (norm_nonneg _)
      _ ≤ (d.W n : ℝ) ^ (-D) := by rw [one_mul]; exact hth
  have hE2 : E2Hyp (d.L n) (d.W n) (E n) (s n) uj w D Λ K₀ M :=
    ⟨hL3, hEn, hs0 n, hsuj, hujw, hw1, hΛ1, hK₀1, hlogW, hLW, hMw, hG, hJW,
      kpmBoundProp5 (d.L n) (d.W n) (E n) uj hL3 hEn huj0 huj1, hKfar⟩
  -- `uopPairLocalMax`
  have hFar : UkerFar (d.L n) (d.W n) u w (ellStar (d.L n) (d.W n) w / 2) D' := by
    intro x y hxy
    exact hK2 u w hu0 huw hwt x y (by linarith)
  set α : ℝ := 2 * (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 * Λ * ρ ^ 10 *
    (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ 5 with hαdef
  set β : ℝ := lossE2 (d.L n) (d.W n) Λ K₀ * Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4)) *
      ((etaT (E n) uj)⁻¹ * ρ ^ 10 *
          (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 5 * ellStar (d.L n) (d.W n) w then 1 else 0) +
        (etaT (E n) uj)⁻¹ * ρ ^ 3 * (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ ((1 : ℝ) / 2) *
          Θ ^ 2 +
        (etaT (E n) w)⁻¹ * (scaleM (d.L n) (d.W n) (E n) w)⁻¹ * Θ ^ 3) *
      tailT (d.L n) (d.W n) (E n) D w (zdist2 (d.L n) (a.1 - a.2) : ℝ) ^ 2 with hβdef
  have hβ0 : 0 ≤ β := by
    have hloss := GoodEventGrid_lossE2_nonneg (L := d.L n) hW1 Λ K₀
    have e1 : 0 < etaT (E n) uj := etaT_pos hEn huj1
    have e2 : 0 < etaT (E n) w := etaT_pos hEn hw1
    have l1 : 0 < ellT (d.L n) uj := (ellT_pos_le hL1 huj1).1
    have l2 : 0 < ellT (d.L n) (s n) := (ellT_pos_le hL1 ((hsuj).trans_lt huj1)).1
    have m1 : 0 < scaleM (d.L n) (d.W n) (E n) uj := scaleM_pos hL1 hW1 hEn huj1
    have m2 : 0 < scaleM (d.L n) (d.W n) (E n) w := scaleM_pos hL1 hW1 hEn hw1
    have hΘ0 : 0 ≤ Θ := by rw [hΘdef]; unfold thr; positivity
    rw [hβdef]
    positivity
  have hα : ∀ b b', ‖EE (d.L n) (d.W n) (E n) uj M b b'‖ ≤ α := fun b b' =>
    GoodEventGrid_norm_EE_le hL3 hG b b'
  have hnear : ∀ b b' : Z2 (d.L n) × Z2 (d.L n),
      (zdist2 (d.L n) (a.1 - b.1) : ℝ) < ellStar (d.L n) (d.W n) w / 2 →
      (zdist2 (d.L n) (a.2 - b.2) : ℝ) < ellStar (d.L n) (d.W n) w / 2 →
      (zdist2 (d.L n) (a.1 - b'.1) : ℝ) < ellStar (d.L n) (d.W n) w / 2 →
      (zdist2 (d.L n) (a.2 - b'.2) : ℝ) < ellStar (d.L n) (d.W n) w / 2 →
      ‖EE (d.L n) (d.W n) (E n) uj M b b'‖ ≤ β := fun b b' h1 h2 h3 h4 =>
    GoodEventGrid_near hE2 hJ.le a b b' h1 h2 h3 h4
  have hC := uopPairLocalMax (d.L n) (d.W n) hL3 u w (ellStar (d.L n) (d.W n) w / 2) D' hu0 huw
    hw1 hFar (EE (d.L n) (d.W n) (E n) uj M) α β a hβ0 hα hnear
  have hC' : ‖∑ b, ∑ b', P b * (starRingEnd ℂ) (P b') * EE (d.L n) (d.W n) (E n) uj M b b'‖ ≤
      R ^ 4 * β + 4 * (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ (-D') * R ^ 3 * α := hC
  -- assembly
  have hAb : Ab d s v K n j
      (fun (b : Z2 (d.L n) × Z2 (d.L n))
          (M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
        gloop (d.L n) (d.W n) (blockMat M') (spectralZ (E n) u) (pmLoop b.1 b.2))
      (fun b b' => (ukerMat (d.L n) 1 u w b.1 b'.1 * ukerMat (d.L n) 1 u w b.2 b'.2).re) a ω
      = ∑ c : Z2 (d.L n) × Z2 (d.L n), ((P c).re : ℂ) • gradMat
          (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            gloop (d.L n) (d.W n) (blockMat M') (spectralZ (E n) u) (pmLoop c.1 c.2)) M := rfl
  rw [hAb]
  have hWD : (d.W n : ℝ) ^ (2 - D') = (d.W n : ℝ) ^ 2 * (d.W n : ℝ) ^ (-D') := by
    rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_two]
  have hfar : 4 * (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ (-D') * R ^ 3 * α =
      8 * (d.L n : ℝ) ^ 4 * (d.W n : ℝ) ^ (2 - D') * N ^ ε * ρ ^ 10 *
        (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ 5 * R ^ 3 := by
    rw [hWD, hαdef, hΛdef]; ring
  have hNsq : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = N := rfl
  have hvar : linTrVar n (∑ c : Z2 (d.L n) × Z2 (d.L n), ((P c).re : ℂ) • gradMat
      (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        gloop (d.L n) (d.W n) (blockMat M') (spectralZ (E n) u) (pmLoop c.1 c.2)) M) ≤
      2 * (R ^ 4 * β + 8 * (d.L n : ℝ) ^ 4 * (d.W n : ℝ) ^ (2 - D') * N ^ ε * ρ ^ 10 *
          (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ 5 * R ^ 3 +
        16 * R ^ 4 * N ^ 2 * (etaT (E n) u)⁻¹ ^ 7 * Δ) := by
    rw [← hfar]
    rw [hPsum] at hB
    have e : (R ^ 2) ^ 2 * (16 * N ^ 2 * (etaT (E n) u)⁻¹ ^ 7 * Δ) =
        16 * R ^ 4 * N ^ 2 * (etaT (E n) u)⁻¹ ^ 7 * Δ := by ring
    rw [e] at hB
    linarith
  have hfl : 0 ≤ Δ * N ^ (-Cc) := mul_nonneg hΔ0 (Real.rpow_nonneg (by linarith) _)
  have hmain := mul_le_mul_of_nonneg_left hvar hΔ0
  rw [hβdef] at hmain
  linarith

/-! ## The stopped conditional sub-Gaussian input -/

/-- **`hsubG_gridTauFull`**: the `hsubG` argument of
`stopped_duhamel_azuma_union` at `ℱ = filt d`, `μ = pathP d`, `ξ = |m(E_n)|²`,
`u = gridTime s v K n`, `τ = gridTauFull`, `Z = ZvecCut`, `c k a j = (cZ … n k a j)₊`, eventually in
`n`.  Real part: `ZvecCut_succ`, `stepZ_ukerMat_eq_Uker`, `stepDecomp_Z_subG_loopPM` with the
variance bound `cZ_hbound`; imaginary part: identically zero, `stepDecomp_Z_subG` at the zero
kernel. -/
theorem hsubG_gridTauFull {E : ℕ → ℝ} {s v t : ℕ → ℝ} {c τ' δ D ε : ℝ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hc : 0 < c) (hband : Bandwidth d c) (hτ' : 0 < τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    (hδc : δ ≤ c / 200) (hD : 20 + 2 / c ≤ D) (hε : 0 ≤ ε) (D' Cc : ℝ) (K : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n), ∀ j < k,
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTauFull d E s v K δ D ε n ω'}.indicator
          (fun ω' => Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
            (gridTime s v K n (j + 1)) (gridTime s v K n k)
            (ZvecCut d (E n) s v K n (j + 1) ω') a) ω).re)
        (cZ d E s v K δ D ε D' Cc n k a j).toNNReal (pathP d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTauFull d E s v K δ D ε n ω'}.indicator
          (fun ω' => Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
            (gridTime s v K n (j + 1)) (gridTime s v K n k)
            (ZvecCut d (E n) s v K n (j + 1) ω') a) ω).im)
        (cZ d E s v K δ D ε D' Cc n k a j).toNNReal (pathP d) := by
  filter_upwards [cZ_hbound hE hs0 hsv hvt ht1 hc hband hτ' hrange hstep hsize hδc hD hε D' Cc K]
    with n hbd k hk a j hj
  have hEn := hE n
  have hv1 : v n < 1 := (hvt n).trans_lt (ht1 n)
  set S : Set (PathΩ d) := {ω' | j < gridTauFull d E s v K δ D ε n ω'} with hSdef
  have hS : MeasurableSet[filt d j] S := lt_gridTauFull_measurableSet hEn (hsv n) hv1 K δ D ε j
  have hjK : j < K n := lt_of_lt_of_le hj hk
  have hsuj : s n ≤ gridTime s v K n j := GoodEventGrid_le_gridTime (hsv n) j
  have hujU : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    GoodEvent_gridTime_mono (hsv n) (Nat.le_succ j)
  have hu0 : 0 ≤ gridTime s v K n (j + 1) := ((hs0 n).trans hsuj).trans hujU
  have huw : gridTime s v K n (j + 1) ≤ gridTime s v K n k := GoodEvent_gridTime_mono (hsv n) hj
  have hw1 : gridTime s v K n k < 1 := (GoodEvent_gridTime_le (hsv n) hk).trans_lt hv1
  have hu1 : gridTime s v K n (j + 1) < 1 := huw.trans_lt hw1
  have hc0 := cZ_nonneg (δ := δ) (D := D) (ε := ε) (D' := D') (Cc := Cc) hEn (hsv n) hv1 hk hj a
  have hcnn : (cZ d E s v K δ D ε D' Cc n k a j).toNNReal
      = ⟨cZ d E s v K δ D ε D' Cc n k a j, hc0⟩ := Real.toNNReal_of_nonneg hc0
  set Φ := Expansion_loopObs d n (E n) (gridTime s v K n (j + 1)) with hΦdef
  have hΦ : ∀ b, HermTestFun d n (Φ b) := fun b =>
    (hermTestFun_loopPM d n (E n) (gridTime s v K n (j + 1)) hu0 hu1 hEn b).1
  have hkey : ∀ ω', Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
      (gridTime s v K n (j + 1)) (gridTime s v K n k) (ZvecCut d (E n) s v K n (j + 1) ω') a
      = (stepZ d s v K n j Φ
          (fun b b' => (ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.1 b'.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.2 b'.2).re) a ω' : ℂ) := by
    intro ω'
    rw [ZvecCut_succ hjK]
    have hZ : Zvec d (E n) s v K n (j + 1) ω'
        = fun b => (stepZ d s v K n j Φ (gridDelta (d.L n)) b ω' : ℂ) :=
      funext fun b => Zvec_succ d (E n) s v K n j ω' b
    rw [hZ]
    exact (stepZ_ukerMat_eq_Uker d s v K n j Φ (E n) hEn.le hu0 huw hw1 a ω').symm
  constructor
  · -- the real part
    have hfun : (fun ω => (S.indicator (fun ω' => Uop (d.L n)
          ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
          (gridTime s v K n k) (ZvecCut d (E n) s v K n (j + 1) ω') a) ω).re)
        = fun ω => S.indicator (fun ω => stepZ d s v K n j Φ
          (fun b b' => (ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.1 b'.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
              (gridTime s v K n (j + 1)) (gridTime s v K n k) b.2 b'.2).re) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hkey ω, Complex.ofReal_re]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_re]
    rw [hfun, hcnn]
    exact stepDecomp_Z_subG_loopPM d s v K n j (E n) (gridTime s v K n (j + 1)) hu0 hu1 hEn
      (gridTime s v K n (j + 1)) (gridTime s v K n k) a S hS _ hc0 (hbd k hk a j hj)
  · -- the imaginary part: identically zero
    have hz0 : ∀ ω, stepZ d s v K n j Φ (fun _ _ => (0 : ℝ)) a ω = 0 := by
      intro ω; simp [stepZ, Ab, linTr]
    have hfun : (fun ω => (S.indicator (fun ω' => Uop (d.L n)
          ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
          (gridTime s v K n k) (ZvecCut d (E n) s v K n (j + 1) ω') a) ω).im)
        = fun ω => S.indicator (fun ω => stepZ d s v K n j Φ (fun _ _ => (0 : ℝ)) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hz0, hkey ω, Complex.ofReal_im]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_im]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s v K n j hΦ _ a S hS _ hc0 ?_
    intro ω _
    have hAb : Ab d s v K n j Φ (fun _ _ => (0 : ℝ)) a ω = 0 := by simp [Ab]
    have hv0 : linTrVar n (0 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) = 0 := by
      simp [linTrVar, LinearForm.linVar, linTr]
    rw [hAb, hv0, mul_zero]
    exact hc0

/-! ## The threshold `xZ` and the Azuma event -/

variable (d) in
/-- **The Azuma threshold**:
`xZ(n, k, a) = N^{δ/16} √(4 Σ_{j<k} cZ(n, k, a, j) + N^{-C_x})`. -/
def xZ (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (δ D ε D' Cc Cx : ℝ) (n k : ℕ)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℝ :=
  ((d.size n : ℕ) : ℝ) ^ (δ / 16) *
    Real.sqrt (4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j +
      ((d.size n : ℕ) : ℝ) ^ (-Cx))

/-- `Σ_{j<k} cZ ≥ 0`. -/
private theorem GoodEventGrid_sum_cZ_nonneg {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ}
    {δ D ε D' Cc : ℝ} {n k : ℕ} (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hk : k ≤ K n) (a : Z2 (d.L n) × Z2 (d.L n)) :
    0 ≤ ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j :=
  Finset.sum_nonneg fun _ hj => cZ_nonneg hE hsv hv1 hk (Finset.mem_range.1 hj) a

/-- **`xZ > 0`**. -/
theorem xZ_pos {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {δ D ε D' Cc Cx : ℝ} {n k : ℕ}
    (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1) (hk : k ≤ K n)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    0 < xZ d E s v K δ D ε D' Cc Cx n k a := by
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith [GoodEvent_one_le_size (d := d) n]
  have hS := GoodEventGrid_sum_cZ_nonneg (δ := δ) (D := D) (ε := ε) (D' := D') (Cc := Cc)
    hE hsv hv1 hk a
  unfold xZ
  have : 0 < 4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j +
      ((d.size n : ℕ) : ℝ) ^ (-Cx) := by
    have := Real.rpow_pos_of_pos hN0 (-Cx); linarith
  exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 this)

/-- **`xZ² = N^{δ/8}(4 Σ_{j<k} cZ + N^{-C_x})`**. -/
theorem xZ_sq {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {δ D ε D' Cc Cx : ℝ} {n k : ℕ}
    (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1) (hk : k ≤ K n)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    xZ d E s v K δ D ε D' Cc Cx n k a ^ 2 = ((d.size n : ℕ) : ℝ) ^ (δ / 8) *
      (4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j +
        ((d.size n : ℕ) : ℝ) ^ (-Cx)) := by
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS := GoodEventGrid_sum_cZ_nonneg (δ := δ) (D := D) (ε := ε) (D' := D') (Cc := Cc)
    hE hsv hv1 hk a
  have hX : 0 ≤ 4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j +
      ((d.size n : ℕ) : ℝ) ^ (-Cx) := by
    have := Real.rpow_nonneg hN0 (-Cx); linarith
  unfold xZ
  rw [mul_pow, Real.sq_sqrt hX]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
  congr 1
  push_cast; ring

/-- `C x^b e^{-x^a} ≤ x^{-D}` for large real `x`. -/
private theorem GoodEventGrid_eventually_mul_exp_neg_rpow_le (C b : ℝ) {a : ℝ} (ha : 0 < a)
    (D : ℝ) : ∀ᶠ x : ℝ in atTop, C * x ^ b * Real.exp (-x ^ a) ≤ x ^ (-D) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((b + D) / a) 1 one_pos
  have h2 := h.comp (tendsto_rpow_atTop ha)
  have hpos : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hpos), eventually_gt_atTop 0] with x hx hx0
  simp only [Function.comp_apply] at hx
  have e : (x ^ a) ^ ((b + D) / a) = x ^ (b + D) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; field_simp
  rw [e, neg_one_mul] at hx
  have hy0 : 0 ≤ x ^ (b + D) * Real.exp (-x ^ a) := by positivity
  have hCy : C * (x ^ (b + D) * Real.exp (-x ^ a)) ≤ 1 := by
    calc C * (x ^ (b + D) * Real.exp (-x ^ a))
        ≤ (|C| + 1) * (x ^ (b + D) * Real.exp (-x ^ a)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hy0
      _ ≤ (|C| + 1) * (|C| + 1)⁻¹ := mul_le_mul_of_nonneg_left hx.le (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have key : C * x ^ b * Real.exp (-x ^ a) =
      (C * (x ^ (b + D) * Real.exp (-x ^ a))) * x ^ (-D) := by
    rw [Real.rpow_add hx0]
    have h1 : x ^ D * x ^ (-D) = 1 := by rw [← Real.rpow_add hx0]; simp
    calc C * x ^ b * Real.exp (-x ^ a)
        = C * x ^ b * Real.exp (-x ^ a) * (x ^ D * x ^ (-D)) := by rw [h1, mul_one]
      _ = _ := by ring
  rw [key]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) hCy

/-- `Zvec (j+1) ≡ 0` when the grid step is `0`. -/
private theorem GoodEventGrid_Zvec_eq_zero_of_step {E : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (h0 : gridStep s v K n = 0) (j : ℕ) (ω : PathΩ d) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Zvec d E s v K n (j + 1) ω b = 0 := by
  rw [Zvec_succ]
  simp [stepZ, h0]

/-- **`highProb_azuma_grid'`**: with high probability, for every `k ≤ K_n` and
label `a`, `‖(Σ_{j < min(k, τ)} 𝒰_{u_{j+1}, u_k} Zvec_{j+1})(a)‖ < xZ(n, k, a)`, where
`τ = gridTauFull`, `𝒰` at `ξ_n = |m(E_n)|²`.  Proof: `stopped_duhamel_azuma_union` with
`hsubG_gridTauFull`; each summand is `≤ 4 e^{-N^{δ/8}}` (`xZ_sq`, `floor_le_cZ`); there are
`K_n · L⁴ ≤ N^{C+2}` summands (`L⁴ ≤ N²`).  If `Δ = 0` the event is the whole space. -/
theorem highProb_azuma_grid' {E : ℕ → ℝ} {s v t : ℕ → ℝ} {c τ' δ D ε : ℝ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hc : 0 < c) (hband : Bandwidth d c) (hτ' : 0 < τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    (hδ0 : 0 < δ) (hδc : δ ≤ c / 200) (hD : 20 + 2 / c ≤ D) (hε : 0 ≤ ε) (D' Cc Cx : ℝ)
    (K : ℕ → ℕ) {C : ℝ}
    (hKcard : ∀ᶠ n : ℕ in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ C) :
    HighProbAt (pathP d) d.size (fun n => {ω | ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(∑ j ∈ Finset.range (min k (gridTauFull d E s v K δ D ε n ω)),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n k) (Zvec d (E n) s v K n (j + 1) ω)) a‖
        < xZ d E s v K δ D ε D' Cc Cx n k a}) := by
  intro D'' _
  have hδ8 : 0 < δ / 8 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, 4 * ((d.size n : ℕ) : ℝ) ^ (C + 2) *
      Real.exp (-((d.size n : ℕ) : ℝ) ^ (δ / 8)) ≤ ((d.size n : ℕ) : ℝ) ^ (-D'') :=
    hsize.eventually (GoodEventGrid_eventually_mul_exp_neg_rpow_le 4 (C + 2) hδ8 D'')
  filter_upwards [hsubG_gridTauFull hE hs0 hsv hvt ht1 hc hband hτ' hrange hstep hsize hδc hD hε
      D' Cc K, hKcard, hsmall] with n hsub hKN hsm
  have hEn := hE n
  have hv1 : v n < 1 := (hvt n).trans_lt (ht1 n)
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set ξ : ℂ := ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) with hξdef
  set τN : PathΩ d → ℕ := fun ω => gridTauFull d E s v K δ D ε n ω with hτN
  set Ev : Set (PathΩ d) := {ω | ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(∑ j ∈ Finset.range (min k (τN ω)),
          Uop (d.L n) ξ (gridTime s v K n (j + 1)) (gridTime s v K n k)
            (Zvec d (E n) s v K n (j + 1) ω)) a‖
        < xZ d E s v K δ D ε D' Cc Cx n k a} with hEv
  change (pathP d) Evᶜ ≤ _
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  rcases hΔ0.eq_or_lt with hΔ | hΔ
  · -- `Δ = 0`: every sum vanishes, the event is everything
    have hall : Evᶜ = ∅ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not, hEv,
        Set.mem_ofPred_eq]
      intro k hk a
      have h0 : (∑ j ∈ Finset.range (min k (τN ω)),
          Uop (d.L n) ξ (gridTime s v K n (j + 1)) (gridTime s v K n k)
            (Zvec d (E n) s v K n (j + 1) ω)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        funext b
        simp [Uop, GoodEventGrid_Zvec_eq_zero_of_step hΔ.symm j ω]
      rw [h0, Pi.zero_apply, norm_zero]
      exact xZ_pos hEn (hsv n) hv1 hk a
    rw [hall, measure_empty]; exact bot_le
  · -- `Δ > 0`
    have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
      lt_gridTauFull_measurableSet hEn (hsv n) hv1 K δ D ε j
    have hZ : ∀ i ≤ K n, StronglyMeasurable[filt d i] (ZvecCut d (E n) s v K n i) :=
      fun i _ => stronglyMeasurable_ZvecCut hEn (hs0 n) (hsv n) hv1 i
    have hx : ∀ k ≤ K n, ∀ a, 0 ≤ xZ d E s v K δ D ε D' Cc Cx n k a :=
      fun k hk a => (xZ_pos hEn (hsv n) hv1 hk a).le
    have hx0 : ∀ a, 0 < xZ d E s v K δ D ε D' Cc Cx n 0 a :=
      fun a => xZ_pos hEn (hsv n) hv1 (Nat.zero_le _) a
    have hU := stopped_duhamel_azuma_union (μ := pathP d) (ℱ := filt d) (d.L n) (ξ := ξ)
      (u := gridTime s v K n) (τ := τN) hτmeas (Z := ZvecCut d (E n) s v K n) (K n) hZ
      (c := fun k a j => (cZ d E s v K δ D ε D' Cc n k a j).toNNReal) hsub hx hx0
    set Sbad : Set (PathΩ d) := {ω | ∃ k ≤ K n, ∃ a, xZ d E s v K δ D ε D' Cc Cx n k a ≤
        ‖(∑ j ∈ Finset.range (min k (τN ω)), Uop (d.L n) ξ (gridTime s v K n (j + 1))
          (gridTime s v K n k) (ZvecCut d (E n) s v K n (j + 1) ω)) a‖} with hSbad
    have hsubset : Evᶜ ⊆ Sbad := by
      intro ω hω
      simp only [hEv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
      obtain ⟨k, hk, a, ha⟩ := hω
      refine ⟨k, hk, a, ?_⟩
      have hsum : (∑ j ∈ Finset.range (min k (τN ω)), Uop (d.L n) ξ (gridTime s v K n (j + 1))
          (gridTime s v K n k) (ZvecCut d (E n) s v K n (j + 1) ω))
          = ∑ j ∈ Finset.range (min k (τN ω)), Uop (d.L n) ξ (gridTime s v K n (j + 1))
            (gridTime s v K n k) (Zvec d (E n) s v K n (j + 1) ω) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < min k (τN ω) := Finset.mem_range.1 hj
        rw [ZvecCut_succ (by omega)]
      rw [hsum]; exact ha
    -- the per-summand bound
    have hterm : ∀ k ∈ Finset.Icc 1 (K n), ∀ a : Z2 (d.L n) × Z2 (d.L n),
        4 * Real.exp (-(xZ d E s v K δ D ε D' Cc Cx n k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d E s v K δ D ε D' Cc n k a j).toNNReal : ℝ)))
          ≤ 4 * Real.exp (-N ^ (δ / 8)) := by
      intro k hk a
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hkK : k ≤ K n := (Finset.mem_Icc.1 hk).2
      have hcoe : ∑ j ∈ Finset.range k, ((cZ d E s v K δ D ε D' Cc n k a j).toNNReal : ℝ)
          = ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j :=
        Finset.sum_congr rfl fun j hj => Real.coe_toNNReal _
          (cZ_nonneg hEn (hsv n) hv1 hkK (Finset.mem_range.1 hj) a)
      rw [hcoe]
      set Sk := ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j with hSk
      have hSk0 : 0 < Sk := by
        have h1 : gridStep s v K n * N ^ (-Cc) ≤ Sk := by
          have := Finset.single_le_sum (f := fun j => cZ d E s v K δ D ε D' Cc n k a j)
            (fun j hj => cZ_nonneg hEn (hsv n) hv1 hkK (Finset.mem_range.1 hj) a)
            (Finset.mem_range.2 hk1)
          exact (floor_le_cZ hEn (hsv n) hv1 hkK hk1 a).trans this
        exact lt_of_lt_of_le (mul_pos hΔ (Real.rpow_pos_of_pos hN0 _)) h1
      have hsq := xZ_sq (δ := δ) (D := D) (ε := ε) (D' := D') (Cc := Cc) (Cx := Cx)
        hEn (hsv n) hv1 hkK a
      rw [← hSk] at hsq
      have hle : N ^ (δ / 8) * (4 * Sk) ≤ xZ d E s v K δ D ε D' Cc Cx n k a ^ 2 := by
        rw [hsq]
        have := Real.rpow_nonneg hN0.le (-Cx)
        have := Real.rpow_nonneg hN0.le (δ / 8)
        nlinarith
      have h4S : 0 < 4 * Sk := by linarith
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ h4S]
      exact hle
    have hL4 : (d.L n : ℝ) ^ 4 ≤ N ^ (2 : ℝ) := by
      have hW : 1 ≤ d.W n := d.W_pos n
      have h : (d.L n) ^ 4 ≤ (d.size n) ^ 2 := by
        unfold Sizes.size
        calc (d.L n) ^ 4 ≤ (d.W n * d.L n) ^ 4 :=
              Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) 4
          _ = ((d.W n * d.L n) ^ 2) ^ 2 := by ring
      rw [Real.rpow_two, hNdef]; exact_mod_cast h
    have hcard : Fintype.card (Z2 (d.L n) × Z2 (d.L n)) = d.L n ^ 4 := by
      rw [Fintype.card_prod, Fintype.card_prod, ZMod.card]; ring
    have hsum_le : ∑ k ∈ Finset.Icc 1 (K n), ∑ a : Z2 (d.L n) × Z2 (d.L n),
        4 * Real.exp (-(xZ d E s v K δ D ε D' Cc Cx n k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d E s v K δ D ε D' Cc n k a j).toNNReal : ℝ)))
        ≤ N ^ (-D'') := by
      calc _ ≤ ∑ _k ∈ Finset.Icc 1 (K n), ∑ _a : Z2 (d.L n) × Z2 (d.L n),
            4 * Real.exp (-N ^ (δ / 8)) :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hterm k hk a
        _ = (K n : ℝ) * ((d.L n : ℝ) ^ 4 * (4 * Real.exp (-N ^ (δ / 8)))) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, hcard,
              Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
            push_cast; ring
        _ ≤ N ^ C * (N ^ (2 : ℝ) * (4 * Real.exp (-N ^ (δ / 8)))) := by
            have hK : (K n : ℝ) ≤ N ^ C := by
              have : (K n : ℝ) ≤ ((K n + 1 : ℕ) : ℝ) := by push_cast; linarith
              exact this.trans hKN
            have he : 0 ≤ 4 * Real.exp (-N ^ (δ / 8)) := by positivity
            have hL0 : 0 ≤ (d.L n : ℝ) ^ 4 := by positivity
            gcongr
        _ = 4 * N ^ (C + 2) * Real.exp (-N ^ (δ / 8)) := by
            rw [Real.rpow_add hN0]; ring
        _ ≤ N ^ (-D'') := hsm
    calc (pathP d) Evᶜ ≤ (pathP d) Sbad := measure_mono hsubset
      _ = ENNReal.ofReal ((pathP d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (N ^ (-D'')) := ENNReal.ofReal_le_ofReal (hU.trans hsum_le)

end RBM.Path

end
