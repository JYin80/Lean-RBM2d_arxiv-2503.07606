/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridGoodN
import RBM2D.Induction.GridDriftN

/-!
# The envelope bookkeeping of the grid drift

Namespace `RBM.Ind`.
* `gridDriftN_envelope`: `exists_norm_Kcal_le_win` supplies `B_k = N^{τ_K} η_{u_{j+1}}^{-k}` in
  `GridDriftN`, so `gridDriftN` holds a.e. with `stepErr_j = stepErrN … B_k` for every grid step
  `j < K n` at once;
* `sum_gridStep_div_etaT_le`: `Σ_j Δ/η_{u_j} ≤ (Im m(E))^{-1} log N` on the grid under `RangeCond`.

Also: `sum_weighted_stepErrN_le` (statement `SumWeightedStepErrN_Stmt`): on the grid `u_j = gridTime s t K n j` with
`K n ≥ N^{C_K}`, the step errors of `gridDriftN_envelope`, weighted by the coarse row bound
`(1 + (1 - u_m)^{-1})^k`, sum to at most `N^{-D_t}` for every `m ≤ K n`, eventually.  Proof: the
uniform per-step bound (`GridEnvelopeN_stepErr_le`), `K Δ = t - s ≤ 1`,
`Δ ≤ N^{-C_K}`, `η_u^{-1} ≤ N^θ / Im m` and `(1 - u)^{-1} ≤ N^θ` on `u ≤ t` (`RangeCond`,
`θ = 1 - τ'`), and the strict inequalities of the statement, which absorb every `k`-, `κ`-dependent
constant.

Paper: arXiv:2503.07606, Section 5 (`int_K-L_ST`, `LK_SDE`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

section Ported

variable {d : Sizes}

/-- **The envelope of the grid drift**: `exists_norm_Kcal_le_win` (eventually `‖𝒦‖ ≤ N^{τ_K} η_v^{-m}`)
supplies `B_k = N^{τ_K} η_{u_{j+1}}^{-k}` in `GridDriftN` for every grid step `j < K n` at once,
so `gridDriftN` holds with `stepErr_j = stepErrN … (N^{τ_K} η_{u_{j+1}}^{-k})`, a.e. in `ω`
simultaneously for all `j < K n` and all labels. -/
theorem gridDriftN_envelope (κ : ℝ) (hκ : 0 < κ) (k : ℕ) [NeZero k] (hk : 2 ≤ k) (τK : ℝ)
    (hτK : 0 < τK) {E s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : SizeTendsto d)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP d), ∀ j, j < K n → ∀ a : Fin k → Z2 (d.L n),
      ‖predIncN d E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
              (pathH d s t K n j ω) l (loopOf σ a) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
              (loopOf σ a) +
            egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
              (loopOf σ a))‖ ≤
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n)
          (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  filter_upwards [hsizeN.eventually (exists_norm_Kcal_le_win κ hκ k τK hτK)] with n hn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hK1 : gridTime s t K n (j + 1) ≤ t n := by
      have h := GoodEvent_gridTime_mono (K := K) (hst n) (show j + 1 ≤ K n by omega)
      rwa [gridTime_last s t K n (hK0 n)] at h
    have hv1 : gridTime s t K n (j + 1) < 1 := hK1.trans_lt (ht1 n)
    have hη : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos (hE2 n) hv1
    have hBk : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _)
    have hN : d.W n ^ 2 * d.L n ^ 2 = d.size n := by
      rw [Sizes.size_eq]
    have h := gridDriftN d E s t K hE2 hs0 hst ht1 hK0 n j hj k hk σ _ hBk (by
      intro w hw J hJ h2 hJk
      exact hn (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) hN (E n) (hE n) w
        (gridTime s t K n (j + 1)) hw.1 hw.2 hv1 J hJ h2 hJk)
    exact h.mono fun ω hω _ => hω
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- **`Σ_j Δ/η_{u_j} ≤ (Im m(E))^{-1} log N`** on the grid
`u_j = s + jΔ` under `RangeCond` (`1 - t ≥ N^{-(1-τ')}`, `τ' > 0`): each term is
`≤ (Im m)^{-1}(log(1-u_j) - log(1-u_{j+1}))` (`Real.one_sub_inv_le_log_of_pos`), the sum telescopes
to `-log(1-t) ≤ (1-τ') log N`.  Used for the factor `exp(C Σ_j Δ/η_{u_j}) ≤ N^{C/Im m}`. -/
theorem sum_gridStep_div_etaT_le {τ' : ℝ} (hτ' : 0 < τ') {E s t : ℕ → ℝ}
    {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0) (hrange : RangeCond d τ' t) :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range (K n),
        gridStep s t K n / etaT (E n) (gridTime s t K n j) ≤
      (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) := by
  filter_upwards [hrange] with n hn
  have hu1 : ∀ j ≤ K n, gridTime s t K n j < 1 := fun j hj =>
    (GoodEvent_gridTime_le (K := K) (hst n) hj).trans_lt (ht1 n)
  have hpos : ∀ j ≤ K n, 0 < 1 - gridTime s t K n j := fun j hj => by linarith [hu1 j hj]
  have him : 0 < (spectralM (E n)).im := spectralM_im_pos (hE n)
  have hstep : ∀ j < K n, gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n j) - Real.log (1 - gridTime s t K n (j + 1)) := by
    intro j hj
    have h1 := hpos j hj.le
    have h2 := hpos (j + 1) hj
    have hx : 0 < (1 - gridTime s t K n j) / (1 - gridTime s t K n (j + 1)) := div_pos h1 h2
    have h3 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div h1.ne' h2.ne', inv_div] at h3
    have hΔj : gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
      unfold gridTime; push_cast; ring
    have e : 1 - (1 - gridTime s t K n (j + 1)) / (1 - gridTime s t K n j) =
        gridStep s t K n / (1 - gridTime s t K n j) := by
      rw [hΔj]; field_simp; ring
    rwa [e] at h3
  have hsum : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log (1 - gridTime s t K n 0) - Real.log (1 - gridTime s t K n (K n)) := by
    rw [← Finset.sum_range_sub' (fun j => Real.log (1 - gridTime s t K n j)) (K n)]
    exact Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.1 hj)
  have hs' : gridTime s t K n 0 = s n := by unfold gridTime; simp
  have hlast : gridTime s t K n (K n) = t n := gridTime_last s t K n (hK0 n)
  rw [hs', hlast] at hsum
  have hlog0 : Real.log (1 - s n) ≤ 0 :=
    Real.log_nonpos (by linarith [hst n, ht1 n]) (by linarith [hs0 n])
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : 1 ≤ d.size n := by
      rw [Sizes.size_eq]
      exact Nat.one_le_iff_ne_zero.2 (by have := d.W_pos n; have := d.three_le_L n; positivity)
    exact_mod_cast this
  have hlogN : 0 ≤ Real.log ((d.size n : ℕ) : ℝ) := Real.log_nonneg hN1
  have ht0 : 0 < 1 - t n := by linarith [ht1 n]
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hlogt : -Real.log (1 - t n) ≤ Real.log ((d.size n : ℕ) : ℝ) := by
    have h4 := Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hn
    rw [Real.log_rpow hNpos] at h4
    nlinarith
  have hfin : ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) ≤
      Real.log ((d.size n : ℕ) : ℝ) := by linarith
  calc ∑ j ∈ Finset.range (K n), gridStep s t K n / etaT (E n) (gridTime s t K n j)
      = (spectralM (E n)).im⁻¹ *
          ∑ j ∈ Finset.range (K n), gridStep s t K n / (1 - gridTime s t K n j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold etaT
        field_simp
    _ ≤ (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.2 him.le)

end Ported

/-! ## Deterministic bookkeeping of the weighted step errors -/

section Envelope

/-- `(1 + x)^k - 1 - k x ≤ k 2^k x²` for `0 ≤ x ≤ 1` (induction: `f_{k+1} = (1+x) f_k + k x²`). -/
private theorem GridEnvelopeN_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : ℝ) * x ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (1 + x) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * x =
        (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2 := by
      push_cast; ring
    rw [e]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
    have h1 : (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) ≤
        (1 + x) * ((k : ℝ) * 2 ^ k * x ^ 2) := mul_le_mul_of_nonneg_left ih (by linarith)
    have hb : 0 ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_right hx1 hb
    have h3 := mul_le_mul_of_nonneg_right hk2 hx2
    have h4 := mul_nonneg hpk hx2
    push_cast
    rw [pow_succ (2 : ℝ) k]
    nlinarith [h1, h2, h3, h4]

/-- **The uniform one-step bound**: with `N = W² L²`, `H ≥ 1` a bound of
`(1 - v)^{-1}`, `H / c` a bound of `η_u^{-1}, η_v^{-1}`, `Y ≥ 1` (`= N^{τ_K}`) and `Δ H ≤ 1`, the
step error at `B_k = Y η_v^{-k}` is at most `Z₁ Δ^{3/2} + Z₂₃ Δ²`. -/
private theorem GridEnvelopeN_stepErr_le (L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ N H Y c : ℝ)
    (hN1 : 1 ≤ N) (hWL : (W : ℝ) ^ 2 * (L : ℝ) ^ 2 = N) (hW : (1 : ℝ) ≤ W)
    (hH : 1 ≤ H) (hY : 1 ≤ Y) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E v)
    (hηu : (etaT E u)⁻¹ ≤ H / c) (hηv : (etaT E v)⁻¹ ≤ H / c)
    (hv1 : 0 < 1 - v) (hv : (1 - v)⁻¹ ≤ H) :
    stepErrN L W E k u v Δ (Y * (etaT E v)⁻¹ ^ k) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) +
        ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
          2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * Δ ^ 2 := by
  unfold stepErrN
  set B := Y * (H / c) ^ k with hB
  have hHc : 1 ≤ H / c := by rw [le_div_iff₀ hc0]; linarith
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hY (one_le_pow₀ hHc)
  have hηu' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηv' : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hηv0.le
  have hBk0 : 0 ≤ Y * (etaT E v)⁻¹ ^ k := mul_nonneg (by linarith) (pow_nonneg hηv' _)
  have hBk : Y * (etaT E v)⁻¹ ^ k ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηv' hηv k)
    (by linarith)
  set Bk := Y * (etaT E v)⁻¹ ^ k with hBkdef
  -- term A
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcast : ((((W * L) ^ 2 : ℕ)) : ℝ) = N := by
    push_cast; rw [← hWL]; ring
  have hone : 1 + (etaT E v)⁻¹ ≤ (1 + 1 / c) * H := by
    have : (etaT E v)⁻¹ ≤ H / c := hηv
    have h2 : H / c = (1 / c) * H := by ring
    linarith
  have hA : envConst L W E k v ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) := by
    unfold envConst
    rw [hcast]
    have hbase : 0 ≤ 1 + (etaT E v)⁻¹ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hone _) (by positivity)
  have hA' : envConst L W E k v * Δ ^ ((3 : ℝ) / 2) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hΔ0 _)
  -- term B
  have hk : kStepC L W k Bk = 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 + (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 := by
    unfold kStepC
    rw [← hWL]; ring
  have hN23 : N ^ 2 ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
  have hB3 : Bk ^ 3 ≤ B ^ 4 :=
    (pow_le_pow_left₀ hBk0 hBk 3).trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hB4 : Bk ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hBk0 hBk 4
  have hkB : kStepC L W k Bk ≤ (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 := by
    rw [hk]
    have hk4 : (0 : ℝ) ≤ (k : ℝ) ^ 4 := by positivity
    have hk6 : (0 : ℝ) ≤ (k : ℝ) ^ 6 := by positivity
    have e1 : 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 ≤ 2 * (k : ℝ) ^ 4 * N ^ 3 * B ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN23 (by positivity)) hB3 (by positivity)
        (by positivity)
    have e2 : (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 ≤ (k : ℝ) ^ 6 * N ^ 3 * B ^ 4 :=
      mul_le_mul_of_nonneg_left hB4 (by positivity)
    linarith [e1, e2]
  have hB' : kStepC L W k Bk * Δ ^ 2 ≤
      (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 * Δ ^ 2 :=
    mul_le_mul_of_nonneg_right hkB (sq_nonneg Δ)
  -- term C
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := GridEnvelopeN_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  have hU : uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
    unfold uStepC
    have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
      mul_le_mul_of_nonneg_left hiv2 (by positivity)
    have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
      mul_le_mul_of_nonneg_left hx2 (by positivity)
    linarith [hrem, e1, e2]
  have hbr0 : 0 ≤ (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk :=
    add_nonneg (mul_nonneg (pow_nonneg hηu' _) (pow_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) _) _))
      hBk0
  have hW1 : ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (pow_nonneg (inv_nonneg.2 (by linarith)) _)
      (pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hW))
  have hbr : (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk ≤ 2 * B := by
    have e1 : (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) ≤ B := by
      calc (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) ≤ (etaT E u)⁻¹ ^ k * 1 :=
            mul_le_mul_of_nonneg_left hW1 (pow_nonneg hηu' _)
        _ = (etaT E u)⁻¹ ^ k := mul_one _
        _ ≤ (H / c) ^ k := pow_le_pow_left₀ hηu' hηu k
        _ ≤ Y * (H / c) ^ k := by
          exact le_mul_of_one_le_left (by positivity) hY
    linarith
  have hC : uStepC k Δ v * ((etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk) ≤
      2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by
    calc uStepC k Δ v * ((etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk)
        ≤ (((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2) * (2 * B) :=
          mul_le_mul hU hbr hbr0 (by positivity)
      _ = 2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by ring
  linarith [hA', hB', hC]

/-- The three `k`-, `c`-dependent coefficients of the weighted sum. -/
private def GridEnvelopeN_a1 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * (16 * ((k : ℝ) + 3) ^ 4 * (1 + 1 / c) ^ (k + 4))

private def GridEnvelopeN_a2 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * (c⁻¹) ^ (4 * k))

private def GridEnvelopeN_a3 (k : ℕ) (c : ℝ) : ℝ :=
  2 ^ k * (2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (c⁻¹) ^ k)

/-- The algebra of the three monomials (`X₁ = N^{-C_K/2}`, `X₂ = N^{-C_K}`). -/
private theorem GridEnvelopeN_alg (k : ℕ) (c H Y N X₁ X₂ : ℝ) :
    (2 * H) ^ k * ((16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4)) * X₁ +
        ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
          2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * X₂) =
      2 ^ k * (16 * ((k : ℝ) + 3) ^ 4 * (1 + 1 / c) ^ (k + 4)) *
          (N ^ 4 * H ^ (2 * k + 4) * Y ^ 0 * X₁) +
        2 ^ k * ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * (c⁻¹) ^ (4 * k)) *
          (N ^ 3 * H ^ (5 * k) * Y ^ 4 * X₂) +
        2 ^ k * (2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (c⁻¹) ^ k) *
          (N ^ 0 * H ^ (2 * k + 2) * Y ^ 1 * X₂) := by
  have e1 : ((1 + 1 / c) * H) ^ (k + 4) = (1 + 1 / c) ^ (k + 4) * H ^ (k + 4) := mul_pow _ _ _
  have e2 : (H / c) ^ k = H ^ k * (c⁻¹) ^ k := by rw [div_eq_mul_inv, mul_pow]
  rw [e1, e2]
  generalize (1 + 1 / c) ^ (k + 4) = P
  ring

/-- **The weighted sum at a fixed size index**, as a sum of three `N`-monomials: for `m ≤ K n`,
`Σ_{j<m} (1 + (1-u_m)^{-1})^k stepErrN … ≤ a₁ N⁴ H^{2k+4} N^{-C_K/2} + a₂ N³ Y⁴ H^{5k} N^{-C_K}
+ a₃ Y H^{2k+2} N^{-C_K}`, `N = size n`, `H = N^{1-τ'}`, `Y = N^{τ_K}`, `c ≤ Im m(E n)`. -/
private theorem GridEnvelopeN_sum_le (d : Sizes) {τ' τK C_K : ℝ} {E s t : ℕ → ℝ} {K : ℕ → ℕ}
    (k : ℕ) (c : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcE : c ≤ (spectralM (E n)).im)
    (hτK : 0 < τK) (hτ'1 : τ' ≤ 1) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + τ') ≤ 1 - t n)
    (hKn : ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (h4 : 1 - τ' ≤ C_K) (m : ℕ) (hm : m ≤ K n) :
    ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n)
          (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
      GridEnvelopeN_a1 k c *
          (((d.size n : ℕ) : ℝ) ^ 4 * (((d.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (2 * k + 4) *
            (((d.size n : ℕ) : ℝ) ^ τK) ^ 0 * ((d.size n : ℕ) : ℝ) ^ (-C_K / 2)) +
        GridEnvelopeN_a2 k c *
          (((d.size n : ℕ) : ℝ) ^ 3 * (((d.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (5 * k) *
            (((d.size n : ℕ) : ℝ) ^ τK) ^ 4 * ((d.size n : ℕ) : ℝ) ^ (-C_K)) +
        GridEnvelopeN_a3 k c *
          (((d.size n : ℕ) : ℝ) ^ 0 * (((d.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (2 * k + 2) *
            (((d.size n : ℕ) : ℝ) ^ τK) ^ 1 * ((d.size n : ℕ) : ℝ) ^ (-C_K)) := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  set θ : ℝ := 1 - τ' with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set H : ℝ := N ^ θ with hHdef
  set Y : ℝ := N ^ τK with hYdef
  have hH1 : 1 ≤ H := Real.one_le_rpow hN1 hθ0
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 hτK.le
  have hH0 : 0 < H := by linarith
  have hHinv : H⁻¹ ≤ 1 - t n := by
    rw [hHdef, ← Real.rpow_neg hN0.le]
    have e : -θ = -1 + τ' := by rw [hθ]; ring
    rw [e]; exact hR
  have hinv : ∀ x, x ≤ t n → 0 < 1 - x ∧ (1 - x)⁻¹ ≤ H := fun x hx => by
    have h1 : H⁻¹ ≤ 1 - x := hHinv.trans (by linarith)
    have h1x : 0 < 1 - x := lt_of_lt_of_le (inv_pos.2 hH0) h1
    exact ⟨h1x, (inv_le_comm₀ h1x hH0).2 h1⟩
  have hη : ∀ x, x ≤ t n → 0 < etaT (E n) x ∧ (etaT (E n) x)⁻¹ ≤ H / c := fun x hx => by
    obtain ⟨h1x, hxH⟩ := hinv x hx
    have hpos : 0 < etaT (E n) x := etaT_pos hE (by linarith [ht1])
    refine ⟨hpos, ?_⟩
    have hle : (1 - x) * c ≤ etaT (E n) x := by
      unfold etaT; exact mul_le_mul_of_nonneg_left hcE h1x.le
    calc (etaT (E n) x)⁻¹ ≤ ((1 - x) * c)⁻¹ := inv_anti₀ (mul_pos h1x hc0) hle
      _ = (1 - x)⁻¹ * c⁻¹ := mul_inv _ _
      _ ≤ H * c⁻¹ := mul_le_mul_of_nonneg_right hxH (inv_nonneg.2 hc0.le)
      _ = H / c := (div_eq_mul_inv H c).symm
  -- the grid
  set Δ : ℝ := gridStep s t K n with hΔdef
  have hKpos : (0 : ℝ) < (K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK0)
  have hΔ0 : 0 ≤ Δ := GoodEvent_gridStep_nonneg (K := K) hst
  have hKΔ : (K n : ℝ) * Δ = t n - s n := by
    rw [hΔdef]; unfold gridStep; field_simp
  have hKΔ1 : (K n : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hNC : 0 < N ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hΔD : Δ ≤ N ^ (-C_K) := by
    have h1 : Δ ≤ 1 / (K n : ℝ) := by
      rw [hΔdef]; unfold gridStep
      exact div_le_div_of_nonneg_right (by linarith) hKpos.le
    calc Δ ≤ 1 / (K n : ℝ) := h1
      _ ≤ 1 / N ^ C_K := one_div_le_one_div_of_le hNC hKn
      _ = N ^ (-C_K) := by rw [Real.rpow_neg hN0.le, one_div]
  have hΔH : Δ * H ≤ 1 := by
    calc Δ * H ≤ N ^ (-C_K) * N ^ θ := mul_le_mul hΔD le_rfl hH0.le (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-C_K + θ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  -- per-step bound
  have hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N := by
    rw [hNdef]; exact_mod_cast (Sizes.size_eq d n).symm
  have hW : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
  have hstep : ∀ j < K n,
      stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
          (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
        16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) +
          ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
            2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * Δ ^ 2 := by
    intro j hj
    have hu : gridTime s t K n j ≤ t n := GoodEvent_gridTime_le (K := K) hst hj.le
    have hv : gridTime s t K n (j + 1) ≤ t n := GoodEvent_gridTime_le (K := K) hst hj
    obtain ⟨hu1, _⟩ := hinv _ hu
    obtain ⟨hv1, hvH⟩ := hinv _ hv
    obtain ⟨hηu0, hηu⟩ := hη _ hu
    obtain ⟨hηv0, hηv⟩ := hη _ hv
    exact GridEnvelopeN_stepErr_le (d.L n) (d.W n) (E n) k _ _ Δ N H Y c hN1 hWL hW hH1 hY1 hc0
      hc1 hΔ0 hΔH hηu0 hηv0 hηu hηv hv1 hvH
  -- the weight
  have hum : gridTime s t K n m ≤ t n := GoodEvent_gridTime_le (K := K) hst hm
  obtain ⟨_, hwH⟩ := hinv _ hum
  have hw0 : 0 ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k := by
    have := inv_nonneg.2 (hinv _ hum).1.le
    positivity
  have hw : (1 + (1 - gridTime s t K n m)⁻¹) ^ k ≤ (2 * H) ^ k :=
    pow_le_pow_left₀ (by have := inv_nonneg.2 (hinv _ hum).1.le; linarith) (by linarith) k
  -- the sum
  set Z1 : ℝ := 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) with hZ1
  set Z2 : ℝ := (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
            2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k) with hZ2
  have hZ1' : 0 ≤ Z1 := by rw [hZ1]; positivity
  have hZ2' : 0 ≤ Z2 := by rw [hZ2]; positivity
  have hT : 0 ≤ Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2 := by
    have := Real.rpow_nonneg hΔ0 ((3 : ℝ) / 2)
    positivity
  have hsumle : ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
          (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
      (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) := by
    calc _ ≤ ∑ j ∈ Finset.range m, (2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 := hstep j (lt_of_lt_of_le (Finset.mem_range.1 hj) hm)
          calc (1 + (1 - gridTime s t K n m)⁻¹) ^ k * stepErrN (d.L n) (d.W n) (E n) k
                (gridTime s t K n j) (gridTime s t K n (j + 1)) Δ
                (Y * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)
              ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) :=
                mul_le_mul_of_nonneg_left h1 hw0
            _ ≤ (2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2) :=
                mul_le_mul_of_nonneg_right hw hT
      _ = (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmK : (m : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hm
  have h2H : 0 ≤ (2 * H) ^ k := by positivity
  -- `K Δ^{3/2} ≤ N^{-C_K/2}` and `K Δ² ≤ N^{-C_K}`
  have hhalf : (K n : ℝ) * Δ ^ ((3 : ℝ) / 2) ≤ N ^ (-C_K / 2) := by
    have e : Δ ^ ((3 : ℝ) / 2) = Δ * Δ ^ ((1 : ℝ) / 2) := by
      rw [show ((3 : ℝ) / 2) = 1 + (1 : ℝ) / 2 by norm_num, Real.rpow_add' hΔ0 (by norm_num),
        Real.rpow_one]
    have h1 : Δ ^ ((1 : ℝ) / 2) ≤ N ^ (-C_K / 2) := by
      calc Δ ^ ((1 : ℝ) / 2) ≤ (N ^ (-C_K)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow hΔ0 hΔD (by norm_num)
        _ = N ^ (-C_K / 2) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
    calc (K n : ℝ) * Δ ^ ((3 : ℝ) / 2) = ((K n : ℝ) * Δ) * Δ ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ 1 * N ^ (-C_K / 2) :=
          mul_le_mul hKΔ1 h1 (Real.rpow_nonneg hΔ0 _) zero_le_one
      _ = N ^ (-C_K / 2) := one_mul _
  have hfull : (K n : ℝ) * Δ ^ 2 ≤ N ^ (-C_K) := by
    calc (K n : ℝ) * Δ ^ 2 = ((K n : ℝ) * Δ) * Δ := by ring
      _ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hKΔ1 hΔ0
      _ ≤ N ^ (-C_K) := by rw [one_mul]; exact hΔD
  have hmain : (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) ≤
      (2 * H) ^ k * (Z1 * N ^ (-C_K / 2) + Z2 * N ^ (-C_K)) := by
    calc (m : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2))
        ≤ (K n : ℝ) * ((2 * H) ^ k * (Z1 * Δ ^ ((3 : ℝ) / 2) + Z2 * Δ ^ 2)) :=
          mul_le_mul_of_nonneg_right hmK (mul_nonneg h2H hT)
      _ = (2 * H) ^ k * (Z1 * ((K n : ℝ) * Δ ^ ((3 : ℝ) / 2)) + Z2 * ((K n : ℝ) * Δ ^ 2)) := by
          ring
      _ ≤ (2 * H) ^ k * (Z1 * N ^ (-C_K / 2) + Z2 * N ^ (-C_K)) := by
          refine mul_le_mul_of_nonneg_left ?_ h2H
          exact add_le_add (mul_le_mul_of_nonneg_left hhalf hZ1')
            (mul_le_mul_of_nonneg_left hfull hZ2')
  refine hsumle.trans (hmain.trans (le_of_eq ?_))
  rw [hZ1, hZ2]
  unfold GridEnvelopeN_a1 GridEnvelopeN_a2 GridEnvelopeN_a3
  exact GridEnvelopeN_alg k c H Y N _ _

end Envelope

section Main

/-- `N^a (N^θ)^p (N^τ)^q N^b = N^{a + θ p + τ q + b}`. -/
private theorem GridEnvelopeN_mono (N : ℝ) (hN : 0 < N) (a : ℕ) (θ : ℝ) (p : ℕ) (τ : ℝ) (q : ℕ)
    (b : ℝ) :
    N ^ a * (N ^ θ) ^ p * (N ^ τ) ^ q * N ^ b = N ^ ((a : ℝ) + θ * p + τ * q + b) := by
  rw [← Real.rpow_natCast N a, ← Real.rpow_natCast (N ^ θ) p, ← Real.rpow_natCast (N ^ τ) q,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN,
    ← Real.rpow_add hN]

/-- `A N^e ≤ N^f` eventually, for `e < f` (`N → ∞`). -/
private theorem GridEnvelopeN_eventually_le (d : Sizes) (hsize : SizeTendsto d) (A e f : ℝ)
    (hef : e < f) :
    ∀ᶠ n : ℕ in atTop, A * ((d.size n : ℕ) : ℝ) ^ e ≤ ((d.size n : ℕ) : ℝ) ^ f := by
  have hT : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ) ^ (f - e)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hef)).comp hsize
  filter_upwards [hT.eventually_ge_atTop A, hsize.eventually_ge_atTop 1] with n hA hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  calc A * ((d.size n : ℕ) : ℝ) ^ e ≤ ((d.size n : ℕ) : ℝ) ^ (f - e) * ((d.size n : ℕ) : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = ((d.size n : ℕ) : ℝ) ^ f := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A uniform lower bound `0 < c ≤ 1`, `c ≤ Im m(E n)` in the bulk `|E n| ≤ 2 - κ`. -/
private theorem GridEnvelopeN_exists_c {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c ≤ (spectralM (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨min (Real.sqrt (2 * κ) / 2) 1, lt_min (by have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith) one_pos, min_le_right _ _, fun n => ?_⟩
  rw [spectralM_im]
  refine (min_le_left _ _).trans ?_
  have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.1 (hE n)
    nlinarith
  have h2 : 2 * κ ≤ 4 - E n ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

/-- **`SumWeightedStepErrN_Stmt`** (used for the `stepErr` part of `AssembledN`): on the grid
`u_j = gridTime s t K n j` with `K n ≥ N^{C_K}`, the step errors of
`gridDriftN_envelope` (`B_k = N^{τ_K} η_{u_{j+1}}^{-k}`), weighted by the coarse row bound
`(1 + (1 − u_m)^{-1})^k` of `Ugen`, sum to at most `N^{-D_t}` for every `m ≤ K n`, eventually, as
soon as `C_K` exceeds the four lower bounds of the hypotheses (`θ = 1 − τ'`,
`RangeCond d τ' t`: `1 − t ≥ N^{-θ}`).  Strict inequalities absorb the `k`-dependent
constants. -/
def SumWeightedStepErrN_Stmt : Prop :=
  ∀ (d : Sizes) {κ τ' τK C_K D_t : ℝ} {E s t : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) [NeZero k],
    0 < κ → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k → SizeTendsto d →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) → RangeCond d τ' t →
    8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K →
    3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K →
    2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K →
    1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ K n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
        ((d.size n : ℕ) : ℝ) ^ (-D_t)

/-- **`sum_weighted_stepErrN_le`**: the statement `SumWeightedStepErrN_Stmt`. -/
theorem sum_weighted_stepErrN_le : SumWeightedStepErrN_Stmt := by
  intro d κ τ' τK C_K D_t E s t K k _ hκ hτ' hτ'1 hτK hDt hk hsize hE hs0 hst ht1 hK0 hrange
    h1 h2 h3 h4 hKN
  obtain ⟨c, hc0, hc1, hcE⟩ := GridEnvelopeN_exists_c hκ hE
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hev1 := GridEnvelopeN_eventually_le d hsize (3 * GridEnvelopeN_a1 k c)
    (((4 : ℕ) : ℝ) + (1 - τ') * ((2 * k + 4 : ℕ) : ℝ) + τK * ((0 : ℕ) : ℝ) + (-C_K / 2)) (-D_t)
    (by push_cast; linarith [h1])
  have hev2 := GridEnvelopeN_eventually_le d hsize (3 * GridEnvelopeN_a2 k c)
    (((3 : ℕ) : ℝ) + (1 - τ') * ((5 * k : ℕ) : ℝ) + τK * ((4 : ℕ) : ℝ) + (-C_K)) (-D_t)
    (by push_cast; linarith [h2])
  have hev3 := GridEnvelopeN_eventually_le d hsize (3 * GridEnvelopeN_a3 k c)
    (((0 : ℕ) : ℝ) + (1 - τ') * ((2 * k + 2 : ℕ) : ℝ) + τK * ((1 : ℕ) : ℝ) + (-C_K)) (-D_t)
    (by push_cast; linarith [h3])
  filter_upwards [hrange, hKN, hev1, hev2, hev3, hsize.eventually_ge_atTop 1] with n hR hKn hA1 hA2 hA3 hN1
  intro m hm
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hsum := GridEnvelopeN_sum_le d k c n hc0 hc1 (hcE n) hτK hτ'1 (hE2 n) (hs0 n) (hst n)
    (ht1 n) (hK0 n) hR hKn h4.le m hm
  have m1 := GridEnvelopeN_mono ((d.size n : ℕ) : ℝ) hN0 4 (1 - τ') (2 * k + 4) τK 0 (-C_K / 2)
  have m2 := GridEnvelopeN_mono ((d.size n : ℕ) : ℝ) hN0 3 (1 - τ') (5 * k) τK 4 (-C_K)
  have m3 := GridEnvelopeN_mono ((d.size n : ℕ) : ℝ) hN0 0 (1 - τ') (2 * k + 2) τK 1 (-C_K)
  rw [m1, m2, m3] at hsum
  calc _ ≤ _ := hsum
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D_t) / 3 + ((d.size n : ℕ) : ℝ) ^ (-D_t) / 3 +
          ((d.size n : ℕ) : ℝ) ^ (-D_t) / 3 :=
        add_le_add (add_le_add ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA1))
          ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA2)))
          ((le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).2 (by rw [← mul_assoc]; exact hA3))
    _ = _ := by ring

end Main

end RBM.Ind

end
