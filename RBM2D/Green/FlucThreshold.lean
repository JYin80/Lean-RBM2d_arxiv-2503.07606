/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.Eq45Small
import RBM2D.Green.AvgPins
import RBM2D.Green.MinorDiffCond

/-!
# A movable deterministic threshold, and the fluctuation gain from the local law

The threshold `detFlucDelta`, the control `detFlucControl`, the exponent `detFlucTheta` and
their bounds, the `η` input (`flucThreshold_etaInv_le_rpow_of_lower`,
`flucThreshold_etaPolyHi_of_lower`), the theorem
`highProbAt_detFlucDelta_of_localLaw`, and the fluctuation gain `flucGain_of_localLaw`.

The argument for the endpoint `flucGain_of_localLaw` (the input `FlucGainUpTo'` of the `2p`-th
moment
expansion `integral_norm_flucAvg_pow_le_iter_budget`, used for `fixedTimeFAThm`):

  `LocalLawDetSeq d E t Ψ`  ⟶  good event at `δ = detFlucDelta d Ψ θ` has high probability
  ⟶  `hsmall` (`hsmall_of_highProb`, `RBM2D/Green/Eq45Small.lean`)  ⟶  `FlucGainUpTo'`
  (`flucGainUpTo'_goodEvent`, `RBM2D/Green/MinorDiffCond.lean`).

## d = 2

* The level `N` is the size `d.size n = (W L)²`; `(N + 4)` becomes `d.size n + 4`.  The
  divergence of the sizes is `hsz : SizeTendsto d`, present in the
  lemmas that need `4 ≤ size n` or `1 ≤ size n` eventually.
* The good event is per time and `LocalLawDetSeq` is a `PerTimeDomAt` over the pairs `(i, j)` of
  the fine lattice, so `highProbAt_detFlucDelta_of_localLaw` is the margin
  `size^{θ/2} · detFlucControl ≤ detFlucDelta` (`detFlucDelta_margin`), the monotonicity
  `Ψ ≤ detFlucControl`, `PerTimeDomAt` at `τ = θ/2`, and the union bound over the `size²` pairs
  (`highProbAt_iInter`, which spends `D + 2` on `D`).
* **The weight condition.**  The condition `(W⁻¹)² ≤ (2 (2δ))²` follows from the floor `W⁻¹ ≤ Ψ`
  (the floor of `FixedTimeFAThm`; in the one-dimensional argument `W^{-1/2} ≤ Ψ` gives
  `W⁻¹ ≤ (4δ)²`): in d = 2 the `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` is at
  `c = W⁻²` (`uniformWeight_blockAvg2`).  It follows from `W⁻¹ ≤ Ψ ≤ 4δ`
  (`detFlucDelta_quarter_psi_le`, `Ψ ≤ 1`).
* The budgets `M` (letters) and `K` (slots) are arbitrary (the one-dimensional argument takes
  `M = K = 2p`).
* The `η` input `size^{-K_η} ≤ etaT (E n) (t n)` is a hypothesis (`fixedTimeFAThm` obtains it from
  `eta_lower_of_rangeCond` with `K_η = 1`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter RBM RBM.Gauss RBM.Path RBM.Ind

open scoped ENNReal

/-! ### The threshold -/

/-- Positive threshold, capped at `1/4`, with a polynomial floor (the level `N` replaced by the
size `d.size n`). -/
def detFlucDelta (d : Sizes) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  min (1 / 4 : ℝ)
    ((((d.size n : ℕ) : ℝ) + 4) ^ θ * max (Ψ n) ((((d.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ))))

/-- The regularized entry control. -/
def detFlucControl (d : Sizes) (Ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (Ψ n) ((((d.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)))

/-- A threshold exponent chosen after the domination tolerance `τ`. -/
def detFlucTheta (a τ : ℝ) : ℝ :=
  min (a / 8) (min (τ / 32) (1 / 8))

theorem detFlucTheta_specs {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    0 < detFlucTheta a τ ∧ detFlucTheta a τ < a / 4 ∧
      detFlucTheta a τ < τ / 16 ∧ detFlucTheta a τ ≤ 1 / 4 := by
  unfold detFlucTheta
  have hpos : 0 < min (a / 8) (min (τ / 32) (1 / 8)) :=
    lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have ha8 := min_le_left (a / 8) (min (τ / 32) (1 / 8))
  have hτ32 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_left (τ / 32) (1 / 8))
  have h8 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_right (τ / 32) (1 / 8))
  refine ⟨hpos, ?_, ?_, ?_⟩ <;> linarith

theorem detFlucControl_ge_psi (d : Sizes) (Ψ : ℕ → ℝ) (n : ℕ) : Ψ n ≤ detFlucControl d Ψ n :=
  le_max_left _ _

/-! #### Real-variable cores (`x` stands for the size `d.size n`) -/

private theorem detFlucCtrl_le_rpow_core {x ψ a : ℝ} (hx : 1 ≤ x) (hψ : ψ ≤ x ^ (-a)) :
    max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1)) := by
  have hβa : min a 1 ≤ a := min_le_left _ _
  have hβ1 : min a 1 ≤ 1 := min_le_right _ _
  have hnp : (0 : ℝ) < x := by linarith
  have hxx : x ≤ x + 4 := by linarith
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnp hxx (by norm_num)
  apply max_le
  · exact hψ.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))

private theorem detFlucDelta_floor_le_core {x ψ θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) :
    (x + 4) ^ (-(2 : ℝ)) ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  have hx4 : (4 : ℝ) ≤ x + 4 := by linarith
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ 1 / 4 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) hx4
      (by norm_num : -(2 : ℝ) ≤ 0)
    norm_num at h ⊢
    linarith
  have hpow : 1 ≤ (x + 4) ^ θ := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ x + 4) hθ
  apply le_min
  · exact hfloor
  · have hmax : (x + 4) ^ (-(2 : ℝ)) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) := le_max_right _ _
    have hpos : 0 ≤ (x + 4) ^ (-(2 : ℝ)) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hpos,
      mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x + 4) θ) (sub_nonneg.mpr hmax)]

private theorem detFlucPow_neg_four_le_core {x : ℝ} (hx : 4 ≤ x) :
    x ^ (-(4 : ℝ)) ≤ (x + 4) ^ (-(2 : ℝ)) := by
  have hnp : (0 : ℝ) < x := by linarith
  have hsq : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hlow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < x + 4) hsq
    (by norm_num : -(2 : ℝ) ≤ 0)
  have hr : (x ^ (2 : ℕ)) ^ (-(2 : ℝ)) = x ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnp.le]
    norm_num
  rw [hr] at hlow
  exact hlow

private theorem detFlucDelta_le_rpow_core {x ψ a θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4) (hx : 4 ≤ x) (hψ : ψ ≤ x ^ (-a)) :
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) ≤ x ^ (-(min (a / 2) 1)) := by
  have hβa : min (a / 2) 1 ≤ a / 2 := min_le_left _ _
  have hβ1 : min (a / 2) 1 ≤ 1 := min_le_right _ _
  have hn : (1 : ℝ) ≤ x := by linarith
  have hnpos : (0 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) ≤ x + 4 := by positivity
  have hxN : x ≤ x + 4 := by linarith
  have hxN2 : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hpow : (x + 4) ^ θ ≤ x ^ (2 * θ) := by
    calc
      (x + 4) ^ θ ≤ (x ^ (2 : ℕ)) ^ θ := Real.rpow_le_rpow hx0 hxN2 hθ0
      _ = x ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        ring_nf
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnpos hxN (by norm_num)
  have hΨcap : ψ ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    hψ.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hfloorcap : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    hfloor.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hmax : max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    max_le hΨcap hfloorcap
  have hmax0 : (0 : ℝ) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) :=
    le_trans (by positivity) (le_max_right _ _)
  have hraw : (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) := by
    calc
      _ ≤ x ^ (2 * θ) * max ψ ((x + 4) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hpow hmax0
      _ ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
  calc
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))))
        ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) := hraw
    _ = x ^ (-(min (a / 2) 1)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

private theorem detFlucDelta_margin_core {x ψ a θ : ℝ} (hθ0 : 0 < θ) (hx : 1 ≤ x)
    (hctrl : max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1)))
    (hpow : 4 ≤ x ^ (min a 1 - θ / 2)) :
    x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  have hnp : (0 : ℝ) < x := by linarith
  have hpowp : (0 : ℝ) < x ^ (min a 1 - θ / 2) := Real.rpow_pos_of_pos hnp _
  have hctrl0 : (0 : ℝ) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) :=
    le_trans (by positivity) (le_max_right _ _)
  have hcap : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ 1 / 4 := by
    have hh : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1 - θ / 2)) := by
      calc
        _ ≤ x ^ (θ / 2) * x ^ (-(min a 1)) :=
          mul_le_mul_of_nonneg_left hctrl (by positivity)
        _ = x ^ (-(min a 1 - θ / 2)) := by
          rw [← Real.rpow_add hnp]
          congr 1
          ring
    have hquarter : x ^ (-(min a 1 - θ / 2)) ≤ 1 / 4 := by
      rw [Real.rpow_neg hnp.le]
      rw [inv_le_iff_one_le_mul₀ hpowp]
      linarith
    exact hh.trans hquarter
  have hraw : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := by
    have hbase : x ^ (θ / 2) ≤ (x + 4) ^ θ := by
      calc
        x ^ (θ / 2) ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
        _ ≤ (x + 4) ^ θ := Real.rpow_le_rpow hnp.le (by linarith) hθ0.le
    exact mul_le_mul_of_nonneg_right hbase hctrl0
  exact le_min hcap hraw

private theorem detFlucDelta_quarter_psi_le_core {x ψ θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ)
    (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1) :
    ψ / 4 ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  apply le_min
  · linarith
  · have hn : (1 : ℝ) ≤ x + 4 := by linarith
    have hp : 1 ≤ (x + 4) ^ θ := Real.one_le_rpow hn hθ
    have hmax : ψ ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hψ0,
      mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x + 4) θ) (sub_nonneg.mpr hmax)]

/-! #### The threshold and its bounds -/

/-- The positive floor does not change the eventual polynomial upper scale. -/
theorem detFlucControl_le_rpow (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {a : ℝ}
    (_ha : 0 < a) (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, detFlucControl d Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(min a 1)) := by
  filter_upwards [hΨ, hsz.eventually_ge_atTop 1] with n hΨn hn
  exact detFlucCtrl_le_rpow_core hn hΨn

theorem detFlucDelta_pos (d : Sizes) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : 0 < detFlucDelta d Ψ θ n := by
  unfold detFlucDelta
  have hn : (0 : ℝ) < ((d.size n : ℕ) : ℝ) + 4 := by positivity
  exact lt_min (by norm_num) (mul_pos (Real.rpow_pos_of_pos hn θ)
    (lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_right _ _)))

theorem detFlucDelta_le_quarter (d : Sizes) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    detFlucDelta d Ψ θ n ≤ 1 / 4 := min_le_left _ _

theorem detFlucDelta_floor_le (d : Sizes) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    (((d.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ detFlucDelta d Ψ θ n :=
  detFlucDelta_floor_le_core (Nat.cast_nonneg _) hθ

theorem detFlucDelta_polyLo (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) :
    PolyLo d.size (detFlucDelta d Ψ θ) := by
  refine ⟨1, one_pos, 4, ?_⟩
  filter_upwards [hsz.eventually_ge_atTop 4] with n hn
  rw [one_mul]
  exact (detFlucPow_neg_four_le_core hn).trans (detFlucDelta_floor_le d hθ n)

/-- Both the entry-control branch and the positive floor decay at a common power. -/
theorem detFlucDelta_le_rpow (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (_ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop,
      detFlucDelta d Ψ θ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(min (a / 2) 1)) := by
  filter_upwards [hΨ, hsz.eventually_ge_atTop 4] with n hΨn hn
  exact detFlucDelta_le_rpow_core hθ0 hθa hθ1 hn hΨn

/-- The required good-event margin `size^{θ/2} · control ≤ threshold`, including the global positive
control floor. -/
theorem detFlucDelta_margin (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ (θ / 2) * detFlucControl d Ψ n ≤ detFlucDelta d Ψ θ n := by
  have hβθ : 0 < min a 1 - θ / 2 := by
    have hβpos : 0 < min a 1 := lt_min ha (by norm_num)
    rcases le_total a 1 with ha1 | ha1
    · rw [min_eq_left ha1]; linarith
    · rw [min_eq_right ha1]; linarith
  filter_upwards [detFlucControl_le_rpow d hsz ha hΨ,
    ((tendsto_rpow_atTop hβθ).comp hsz).eventually_ge_atTop 4,
    hsz.eventually_ge_atTop 1] with n hctrl hpow hn
  exact detFlucDelta_margin_core (a := a) hθ0 hn hctrl hpow

/-- For each fixed coefficient, the threshold is eventually small. -/
theorem detFlucDelta_eventually_mul_le_one (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ}
    {a θ C : ℝ} (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * detFlucDelta d Ψ θ n ≤ 1 := by
  have hβ : 0 < min (a / 2) 1 := lt_min (by linarith) (by norm_num)
  filter_upwards [detFlucDelta_le_rpow d hsz ha hθ0 hθa hθ1 hΨ,
    ((tendsto_rpow_atTop hβ).comp hsz).eventually_ge_atTop C, hsz.eventually_ge_atTop 1]
    with n hδ hCn hn
  have hnp : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hp : (0 : ℝ) < ((d.size n : ℕ) : ℝ) ^ (min (a / 2) 1) := Real.rpow_pos_of_pos hnp _
  have hbound : C * ((d.size n : ℕ) : ℝ) ^ (-(min (a / 2) 1)) ≤ 1 := by
    rw [Real.rpow_neg hnp.le]
    rw [mul_inv_le_iff₀ hp]
    simpa using hCn
  exact (mul_le_mul_of_nonneg_left hδ hC).trans hbound

/-- The two smallness conditions of `flucGainUpTo'_goodEvent` at the threshold, for every budget
`M`: `8 M δ ≤ 1` and `2 C_M (2 δ) + 2 δ ≤ 1` (`hB1` at `condCost = 2 δ`), eventually. -/
theorem detFlucDelta_moment_small (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) (M : ℕ) :
    (∀ᶠ n : ℕ in atTop, 8 * (M : ℝ) * detFlucDelta d Ψ θ n ≤ 1) ∧
    (∀ᶠ n : ℕ in atTop,
      2 * minorDiffC M * (2 * detFlucDelta d Ψ θ n) + 2 * detFlucDelta d Ψ θ n ≤ 1) := by
  have hC : 0 ≤ 4 * minorDiffC M + 2 := by
    have := minorDiffC_nonneg M
    linarith
  constructor
  · filter_upwards [detFlucDelta_eventually_mul_le_one d hsz ha hθ0 hθa hθ1 hΨ
      (C := 8 * (M : ℝ)) (by positivity)] with n hn
    exact hn
  · filter_upwards [detFlucDelta_eventually_mul_le_one d hsz ha hθ0 hθa hθ1 hΨ
      (C := 4 * minorDiffC M + 2) hC] with n hn
    nlinarith

/-- The cap never reduces the threshold below a quarter of a small entry control. -/
theorem detFlucDelta_quarter_psi_le (d : Sizes) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    {n : ℕ} (hΨ0 : 0 ≤ Ψ n) (hΨ1 : Ψ n ≤ 1) :
    Ψ n / 4 ≤ detFlucDelta d Ψ θ n :=
  detFlucDelta_quarter_psi_le_core (Nat.cast_nonneg _) hθ hΨ0 hΨ1

/-- **The d = 2 weight condition.**  The floor `W⁻¹ ≤ Ψ` and `Ψ ≤ size^{-a}` give
`(W⁻¹)² ≤ (2 (2 δ))²` eventually: the `c ≤ ρ²` of
`integral_norm_flucAvg_pow_le_iter_budget` at `c = W⁻²` (`uniformWeight_blockAvg2`) and
`ρ = 2 (2 δ)`. -/
private theorem flucThreshold_W_inv_sq_le_detFlucDelta_sq (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ}
    {a θ : ℝ} (ha : 0 < a) (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ^ 2 ≤ (2 * (2 * detFlucDelta d Ψ θ n)) ^ 2 := by
  filter_upwards [hΨlo, hΨhi, hsz.eventually_ge_atTop 1] with n hlow hhigh hn
  have hw : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  have hW0 : (0 : ℝ) ≤ ((d.W n : ℝ))⁻¹ := inv_nonneg.2 hw.le
  have hΨ0 : 0 ≤ Ψ n := hW0.trans hlow
  have hΨ1 : Ψ n ≤ 1 :=
    hhigh.trans (by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith : -a ≤ (0 : ℝ))))
  have hquarter := detFlucDelta_quarter_psi_le d hθ hΨ0 hΨ1
  have hΨδ : Ψ n ≤ 2 * (2 * detFlucDelta d Ψ θ n) := by linarith
  exact (pow_le_pow_left₀ hW0 hlow 2).trans (pow_le_pow_left₀ hΨ0 hΨδ 2)

/-! #### The `η` input -/

/-- `size^{-K} ≤ η_t` gives `η_t⁻¹ ≤ size^K`. -/
theorem flucThreshold_etaInv_le_rpow_of_lower (d : Sizes) {E t : ℕ → ℝ} {K : ℝ}
    (hη : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-K) ≤ RBM.Path.etaT (E n) (t n)) :
    ∀ᶠ n : ℕ in atTop, (RBM.Path.etaT (E n) (t n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ K := by
  filter_upwards [hη] with n hηn
  have hn : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
    have := AvgPins_one_le_size d n
    linarith
  have hpow : 0 < ((d.size n : ℕ) : ℝ) ^ (-K) := Real.rpow_pos_of_pos hn _
  have h := inv_anti₀ hpow hηn
  rw [Real.rpow_neg hn.le, inv_inv] at h
  exact h

/-- `size^{-K} ≤ η_t` (with `K ≥ 0`) makes `η_t⁻¹ + 1` a `PolyHi` function. -/
theorem flucThreshold_etaPolyHi_of_lower (d : Sizes) {E t : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-K) ≤ RBM.Path.etaT (E n) (t n)) :
    PolyHi d.size (fun n => (RBM.Path.etaT (E n) (t n))⁻¹ + 1) := by
  refine ⟨2, by norm_num, K, ?_⟩
  filter_upwards [flucThreshold_etaInv_le_rpow_of_lower d hη] with n hInv
  have hn : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := AvgPins_one_le_size d n
  have hOne : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ K := Real.one_le_rpow hn hK
  linarith

/-! ### The good event at the threshold, from the local law -/

/-- **Statement of `highProbAt_detFlucDelta_of_localLaw`**: the per-time good event (4.1) at the
threshold `detFlucDelta` has high probability.  Proof: the margin
`size^{θ/2} · detFlucControl ≤ detFlucDelta` (eventually),
`Ψ ≤ detFlucControl`, `PerTimeDomAt` at `τ = θ/2`, `D + 2`, and the union over the `size²` pairs. -/
theorem highProbAt_detFlucDelta_of_localLaw :
  ∀ (d : Sizes) {E t Ψ : ℕ → ℝ} {a θ : ℝ}, SizeTendsto d →
    0 < a → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq d E t Ψ →
    HighProbAt (Sizes.seqP d) d.size (fun n => {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
      llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤
        detFlucDelta d Ψ θ n}) := by
  intro d E t Ψ a θ hsz ha hθ0 hθa hθ1 hΨhi hll
  have hmargin := detFlucDelta_margin d hsz ha hθ0 hθa hθ1 hΨhi
  -- `#(Idx × Idx) = size²` pairs
  have hcard : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ)
        ≤ ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun n => by
      rw [Fintype.card_prod, flucAvg_card_Idx_eq_size, Real.rpow_two]
      push_cast
      rw [sq]
  -- one pair at a time: `PerTimeDomAt` at `τ = θ/2`, with the margin
  have hpair : ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ p : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n),
        (Sizes.seqP d) ({ω : Sizes.SeqΩ d |
            llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.1 p.2
              ≤ detFlucDelta d Ψ θ n})ᶜ
          ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
    intro D hD
    filter_upwards [hll (θ / 2) (half_pos hθ0) D hD, hmargin] with n hn hm p
    refine le_trans (measure_mono ?_) (hn ((), p.1, p.2))
    intro ω hω
    have hω' : detFlucDelta d Ψ θ n
        < llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.1 p.2 :=
      not_le.1 hω
    have hle : ((d.size n : ℕ) : ℝ) ^ (θ / 2) * Ψ n ≤ detFlucDelta d Ψ θ n :=
      le_trans (mul_le_mul_of_nonneg_left (detFlucControl_ge_psi d Ψ n)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hm
    exact lt_of_le_of_lt hle hω'
  have hpairs := highProbAt_iInter (Sizes.seqP d) d.size
    (K := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (Ξ := fun n p => {ω : Sizes.SeqΩ d |
      llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.1 p.2
        ≤ detFlucDelta d Ψ θ n})
    (C := 2) (by norm_num) hcard hpair
  exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hpairs
    (Filter.Eventually.of_forall fun n ω hω i j => Set.mem_iInter.1 hω (i, j))

/-! ### The endpoint: the gain from the local law -/

/-- **Statement of `flucGain_of_localLaw`**: from the local law at the deterministic scale `Ψ`,
the gain `FlucGainUpTo'` at the time `t n` with `δ = detFlucDelta d Ψ θ`,
`B = 2 (2 C_M (2δ) + 2δ)`, `ρ = 2 (2δ)`, for every pair of budgets `M, K`; and the d = 2 weight
condition `(W⁻¹)² ≤ ρ²` (the `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` at
`c = W⁻²`, `uniformWeight_blockAvg2`).  It is used for `fixedTimeFAThm`. -/
theorem flucGain_of_localLaw :
  ∀ (d : Sizes) {E t Ψ : ℕ → ℝ} {a Kη θ : ℝ}, SizeTendsto d →
    (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    0 < a → 0 ≤ Kη → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-Kη) ≤ RBM.Path.etaT (E n) (t n)) →
    (∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq d E t Ψ → ∀ M K : ℕ,
    (∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
        (2 * (2 * minorDiffC M * (2 * detFlucDelta d Ψ θ n) + 2 * detFlucDelta d Ψ θ n))
        (2 * (2 * detFlucDelta d Ψ θ n)) M K) ∧
    (∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ^ 2 ≤ (2 * (2 * detFlucDelta d Ψ θ n)) ^ 2) := by
  intro d E t Ψ a Kη θ hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll M K
  have hΩ := highProbAt_detFlucDelta_of_localLaw d hsz ha hθ0 hθa hθ1 hΨhi hll
  have hsmall := hsmall_of_highProb d hsz hE ht1 (detFlucDelta_pos d Ψ θ)
    (detFlucDelta_polyLo d hsz hθ0.le) (flucThreshold_etaPolyHi_of_lower d hKη hη) hΩ M K
  obtain ⟨hMδ, hδC⟩ := detFlucDelta_moment_small d hsz ha hθ0.le hθa hθ1 hΨhi M
  refine ⟨?_, flucThreshold_W_inv_sq_le_detFlucDelta_sq d hsz ha hθ0.le hΨlo hΨhi⟩
  filter_upwards [hMδ, hδC, hsmall] with n hMδn hδCn hsmalln
  have hΨ : (0 : ℝ) < 2 * detFlucDelta d Ψ θ n := by linarith [detFlucDelta_pos d Ψ θ n]
  have hcc : condCost (E n) (t n) M (2 * detFlucDelta d Ψ θ n)
      (condEps (E n) (t n) M (2 * detFlucDelta d Ψ θ n)) = 2 * detFlucDelta d Ψ θ n :=
    condCost_condEps (hE n) (ht1 n) M hΨ
  have h := flucGainUpTo'_goodEvent (d := d) (E := E) (t := t) (δ := detFlucDelta d Ψ θ)
    (n := n) (hE n) (ht1 n) (condEps_nonneg (hE n) (ht1 n) M hΨ.le)
    (detFlucDelta_pos d Ψ θ n) (detFlucDelta_le_quarter d Ψ θ n) hMδn
    (by rw [hcc]; exact hδCn) hsmalln
  rwa [hcc] at h

end RBM.Green
