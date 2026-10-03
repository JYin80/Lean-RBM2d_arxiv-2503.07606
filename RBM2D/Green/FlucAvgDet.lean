/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucThreshold
import RBM2D.Green.EntryBlock
import RBM2D.Green.LocalLaw

/-!
# The fixed-time fluctuation averaging at a deterministic entry scale: `fixedTimeFAThm`

The statement `FixedTimeFAThm` of `Green/AvgPins.lean`, proved outright.  The proof follows the
one-dimensional formalization (the fixed-time statement, the `2p`-th moment bound for the budget
family, the iterated bound, the threshold lemmas).  The paper (arXiv:2503.07606)
does not state fluctuation averaging as a lemma: the (`GavLGEX`) clause of `lem_GbEXP` is proved
"as Lemma 4.2 in [YY_25]", and the fluctuation averaging is the display `jasdu` there.

## Method

  `LocalLawDetSeq d E t Ψ`  ⟶  `flucGain_of_localLaw` (`FlucThreshold.lean`): the gain
  `FlucGainUpTo'` with `ρ = 4 δ`, `B = (8 C_M + 4) δ`, `δ = detFlucDelta d Ψ θ`, and the d = 2
  weight condition `(W⁻¹)² ≤ ρ²`  ⟶  the moment bound `integral_norm_flucAvg_pow_le_iter_budget`
  for the two weight families (row `svar`, `c = (5 W²)⁻¹`; block `uniformWeight_blockAvg2`,
  `c = W⁻²`), at the
  budgets `M = K = 2p`  ⟶  Markov (`perTimeDomAt_of_moment`): `‖flucAvg‖ ≺ 4 δ²`  ⟶  the choice of
  `θ` after `τ` (`detFlucTheta`, `θ < τ/16`): `‖flucAvg‖ ≺ Ψ²`  ⟶  the bridge to `BlockIndex`.

## d = 2

* The `≺` statements are `PerTimeDomAt (Sizes.seqP d) d.size ξ ζ` at the time `t n`; `N` is
  `size n = (W L)²`; `N → ∞` is `hsz : SizeTendsto d`.
* The floor is `W⁻¹ ≤ Ψ` (the entry scale in d = 2 is `S ≤ W⁻²/5`), against `W^{-1/2} ≤ Ψ` in the
  one-dimensional argument.  `(size + 4)^{-2} ≤ W⁻¹` follows from `W ≤ size`.
* The weight families have `#A = 5 W²` (row) and `W²` (block), against `3 W` and `W` in
  `d = 1`; the weights are `(5 W²)⁻¹ ≤ W⁻²` and `W⁻²`; the condition `c ≤ ρ²` is
  `W⁻² ≤ (4 δ)²`, the second conjunct of `flucGain_of_localLaw`.  `2 p ≤ #A` holds eventually
  since `W → ∞` (`eventually_le_W`, from `Bandwidth`).
* The premise `η ≥ N^{-K}` is derived from `RangeCond` (`eta_lower_of_rangeCond`, `K_η = 1`).
* **The bridge.**  `FARowDet` / `FABlkDet` live on `BlockIndex` with `Sblk2`,
  `blkCoef2`, `greenBlk`, `condDiagBlk`; `flucAvg`, `condExpDiag`, `condRow` live on
  `Idx = Z2 (W L)`.  They are transported by `splitEquiv` and `Sblk2_eq_svar`
  (`Green/EntryBlock.lean`); the index `i` (row) or `a` (block) stays outside
  the probability (`PerTimeDomAt` is `∀ u` inside the eventually).

## Statement

`fixedTimeFAThm : FixedTimeFAThm` is the statement of `AvgPins.lean`, with no added
hypothesis.  The `Bandwidth` input is used only for `2 p ≤ #A`; `RangeCond` only for the `η` input.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Green
open scoped NNReal ENNReal

/-! ## 1. The threshold against `Ψ` -/

/-- `Tendsto d.size` from `SizeTendsto d` (copy of the `private` `tendsto_size_of'`,
`Green/AvgPins.lean`). -/
private theorem FlucAvgDet_tendsto_size {d : Sizes} (hsz : SizeTendsto d) :
    Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

/-- Real-variable core of `FlucAvgDet_detFlucDelta_le_rpow_mul_psi` (`x` is the size): once the
floor
`w⁻¹ ≤ ψ` with `w ≤ x` holds, the floor `(x + 4)^{-2}` of the threshold is below `ψ`, and the
remaining loss is at most `x^{2θ}` (`x + 4 ≤ x²` for `x ≥ 4`). -/
private theorem FlucAvgDet_delta_le_core {x w ψ θ : ℝ} (hθ : 0 ≤ θ) (hx : 4 ≤ x) (hw : 0 < w)
    (hwx : w ≤ x) (hψ : w⁻¹ ≤ ψ) :
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) ≤ x ^ (2 * θ) * ψ := by
  have hn1 : (1 : ℝ) ≤ x := by linarith
  have hn0 : (0 : ℝ) < x := by linarith
  have hfloorN : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num)
  have hNhalf : x ^ (-(2 : ℝ)) ≤ x ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hWhalf : x ^ (-(1 : ℝ)) ≤ w⁻¹ := by
    rw [Real.rpow_neg_one]
    exact inv_anti₀ hw hwx
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ ψ := (hfloorN.trans hNhalf).trans (hWhalf.trans hψ)
  have hmax : max ψ ((x + 4) ^ (-(2 : ℝ))) = ψ := max_eq_left hfloor
  have hψ0 : 0 ≤ ψ := le_trans (inv_nonneg.2 hw.le) hψ
  have hN2 : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hpow : (x + 4) ^ θ ≤ x ^ (2 * θ) := by
    calc (x + 4) ^ θ ≤ (x ^ (2 : ℕ)) ^ θ := Real.rpow_le_rpow (by positivity) hN2 hθ
      _ = x ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        ring_nf
  calc min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))))
      ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ = (x + 4) ^ θ * ψ := by rw [hmax]
    _ ≤ x ^ (2 * θ) * ψ := mul_le_mul_of_nonneg_right hpow hψ0

/-- Once the bandwidth scale is reached, the floor in the threshold is below `Ψ`; the remaining
loss is at most `size^{2θ}` (with the floor `W⁻¹ ≤ Ψ`). -/
private theorem FlucAvgDet_detFlucDelta_le_rpow_mul_psi (d : Sizes) (hsz : SizeTendsto d)
    {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop, detFlucDelta d Ψ θ n ≤ ((d.size n : ℕ) : ℝ) ^ (2 * θ) * Ψ n := by
  filter_upwards [hΨlo, hsz.eventually_ge_atTop 4] with n hΨn hn4
  exact FlucAvgDet_delta_le_core hθ hn4 (by exact_mod_cast d.W_pos n)
    (by exact_mod_cast W_le_self d n) hΨn

/-- Real-variable core of the absorption of the movable threshold. -/
private theorem FlucAvgDet_scale_absorb_core {x ψ δ τ θ : ℝ} (hθτ : θ ≤ τ / 16)
    (hx1 : 1 ≤ x) (h4 : 4 ≤ x ^ (τ / 4)) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x ^ (2 * θ) * ψ) :
    x ^ (τ / 2) * (4 * δ ^ 2) ≤ x ^ τ * ψ ^ 2 := by
  have hn0 : (0 : ℝ) < x := by linarith
  have hsq : δ ^ 2 ≤ (x ^ (2 * θ) * ψ) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hPowExp : x ^ (4 * θ) ≤ x ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpow2 : (x ^ (2 * θ)) ^ 2 = x ^ (4 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring_nf
  have hΨsq : 0 ≤ ψ ^ 2 := sq_nonneg _
  calc x ^ (τ / 2) * (4 * δ ^ 2)
      = 4 * x ^ (τ / 2) * δ ^ 2 := by ring
    _ ≤ 4 * x ^ (τ / 2) * ((x ^ (2 * θ) * ψ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * x ^ (τ / 2) * x ^ (4 * θ) * ψ ^ 2 := by rw [mul_pow, hpow2]; ring
    _ ≤ 4 * x ^ (τ / 2) * x ^ (τ / 4) * ψ ^ 2 := by gcongr
    _ ≤ x ^ (τ / 4) * x ^ (τ / 2) * x ^ (τ / 4) * ψ ^ 2 := by gcongr
    _ = x ^ τ * ψ ^ 2 := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, show τ / 4 + τ / 2 + τ / 4 = τ by ring]

/-- Absorb the movable threshold's polynomial loss with half of the requested
stochastic-domination tolerance. -/
private theorem FlucAvgDet_detFlucDelta_scale_absorb (d : Sizes) (hsz : SizeTendsto d)
    {Ψ : ℕ → ℝ} {τ θ : ℝ} (hτ : 0 < τ) (hθ0 : 0 ≤ θ) (hθτ : θ ≤ τ / 16)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ (τ / 2) * (4 * detFlucDelta d Ψ θ n ^ 2) ≤
        ((d.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 := by
  filter_upwards [FlucAvgDet_detFlucDelta_le_rpow_mul_psi d hsz hθ0 hΨlo,
    (FlucAvgDet_tendsto_size hsz).eventually (eventually_le_rpow 4 (by linarith : 0 < τ / 4))]
    with n hδ h4
  exact FlucAvgDet_scale_absorb_core hθτ (AvgPins_one_le_size d n) h4
    (detFlucDelta_pos d Ψ θ n).le hδ

/-! ## 2. The moment bound gives `≺` -/

/-- **The `2p`-th moment of the fluctuation average gives `‖flucAvg‖ ≺ ρ B`, per time**: the gain
`FlucGainUpTo'` at the budgets `M = K = 2p` with `B_p ≤ K_p B_m` and `ρ = ep`, a uniform weight
`c ≤ ρ²` on a set with `2 p ≤ #A` eventually, and Markov (`perTimeDomAt_of_moment`, where the
size-index `n` carries `size n` in every power). -/
theorem FlucAvgDet_iter_budget_eventually {d : Sizes} (hsz : SizeTendsto d) {E t : ℕ → ℝ}
    {V : ℕ → Type*} (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1)
    {Tw : ∀ n, V n → Idx (d.L n) (d.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx (d.L n) (d.W n))}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) (Bp p n) (ep n)
        (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ n, 0 ≤ Bm n)
    (hBK : ∀ p n, Bp p n ≤ Kp p * Bm n)
    (hpos : ∀ n, 0 < ep n * Bm n) (hρ1 : ∀ n, ep n ≤ 1)
    (hcρ : ∀ᶠ n : ℕ in atTop, cw n ≤ ep n ^ 2)
    (hw : ∀ n (a : V n), UniformWeight (Tw n a) (cw n) (Aw n a))
    (hcardA : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ a : V n, 2 * p ≤ (Aw n a).card) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (a : V n) ω =>
        ‖flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) (Tw n a) ω‖)
      (fun n _ _ => ep n * Bm n) := by
  refine perTimeDomAt_of_moment (FlucAvgDet_tendsto_size hsz) (fun n _ => hpos n)
    (fun p n a => ?_) ?_
  · exact integrable_norm_flucAvg_pow (flucBound_env (hE n) (ht1 n) d n (t n)).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, hg p, hcρ] with n h2 hgn hcρn a
    have hmain := integral_norm_flucAvg_pow_le_iter_budget (p := p) (hE n) (ht1 n) (u := t n)
      hgn le_rfl le_rfl (hρ1 n) hcρn (hw n a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep n := hgn.rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p n := hgn.B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep n * Bm n) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep n * (Kp p * Bm n) :=
            mul_le_mul_of_nonneg_left (hBK p n) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep n * Bm n) := by ring
    have hmain2 : ∫ ω, ‖flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) (Tw n a) ω‖
          ^ (2 * p) ∂(Sizes.seqP d)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep n * Bm n) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep n * Bm n) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (AvgPins_one_le_size d n) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep n * Bm n) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm n)) _
    simp only [abs_norm]
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-! ## 3. The family at the threshold `δ = detFlucDelta` -/

/-- **The fluctuation average is `≺ 4 δ²` at the movable threshold**.  The gain
comes from the local law (`flucGain_of_localLaw`) with the budgets `M = K = 2p`,
`B_p = (8 C_{2p} + 4) δ`, `ρ = 4 δ`; the weight condition `c ≤ ρ²` is its second conjunct,
`(W⁻¹)² ≤ (2 (2 δ))²`, with `c ≤ (W⁻¹)²` (row: `(5 W²)⁻¹`, block: `W⁻²`). -/
theorem FlucAvgDet_family (d : Sizes) (hsz : SizeTendsto d) {E t Ψ : ℕ → ℝ} {a Kη θ : ℝ}
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (ha : 0 < a) (hKη : 0 ≤ Kη)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n))
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a))
    (hll : LocalLawDetSeq d E t Ψ) {V : ℕ → Type*}
    {Tw : ∀ n, V n → Idx (d.L n) (d.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx (d.L n) (d.W n))}
    (hw : ∀ n (b : V n), UniformWeight (Tw n b) (cw n) (Aw n b))
    (hcW : ∀ n, cw n ≤ ((d.W n : ℝ))⁻¹ ^ 2)
    (hcard : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ b : V n, 2 * p ≤ (Aw n b).card) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (b : V n) ω =>
        ‖flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) (Tw n b) ω‖)
      (fun n _ _ => 4 * detFlucDelta d Ψ θ n ^ 2) := by
  have hgain := flucGain_of_localLaw d hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll
  have hg : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
        ((8 * minorDiffC (2 * p) + 4) * detFlucDelta d Ψ θ n) (4 * detFlucDelta d Ψ θ n)
        (2 * p) (2 * p) := by
    intro p
    filter_upwards [(hgain (2 * p) (2 * p)).1] with n hn
    have e1 : 2 * (2 * minorDiffC (2 * p) * (2 * detFlucDelta d Ψ θ n) + 2 * detFlucDelta d Ψ θ n)
        = (8 * minorDiffC (2 * p) + 4) * detFlucDelta d Ψ θ n := by ring
    have e2 : 2 * (2 * detFlucDelta d Ψ θ n) = 4 * detFlucDelta d Ψ θ n := by ring
    rw [e1, e2] at hn
    exact hn
  have hcρ : ∀ᶠ n : ℕ in atTop, cw n ≤ (4 * detFlucDelta d Ψ θ n) ^ 2 := by
    filter_upwards [(hgain 0 0).2] with n hn
    calc cw n ≤ ((d.W n : ℝ))⁻¹ ^ 2 := hcW n
      _ ≤ (2 * (2 * detFlucDelta d Ψ θ n)) ^ 2 := hn
      _ = (4 * detFlucDelta d Ψ θ n) ^ 2 := by ring
  have hKp : ∀ p : ℕ, (0 : ℝ) ≤ 8 * minorDiffC (2 * p) + 4 := fun p => by
    have := minorDiffC_nonneg (2 * p)
    linarith
  have h := FlucAvgDet_iter_budget_eventually hsz hE ht1 (Tw := Tw) (cw := cw) (Aw := Aw)
    (Bp := fun p n => (8 * minorDiffC (2 * p) + 4) * detFlucDelta d Ψ θ n)
    (Bm := detFlucDelta d Ψ θ) (Kp := fun p => 8 * minorDiffC (2 * p) + 4)
    (ep := fun n => 4 * detFlucDelta d Ψ θ n) hg hKp
    (fun n => (detFlucDelta_pos d Ψ θ n).le) (fun p n => le_refl _)
    (fun n => mul_pos (by linarith [detFlucDelta_pos d Ψ θ n]) (detFlucDelta_pos d Ψ θ n))
    (fun n => by linarith [detFlucDelta_le_quarter d Ψ θ n]) hcρ hw hcard
  convert h using 1
  funext n b ω
  ring

/-! ## 4. Choosing the threshold after the tolerance -/

/-- A family of positive thresholds gives domination at the original squared entry control, because
the threshold exponent can be chosen after the requested tolerance.  For `τ, D`, take
`θ = detFlucTheta a τ` (`θ < τ / 16`), the family at `(τ/2, D)`, and
`size^{τ/2} · 4 δ² ≤ size^τ Ψ²` eventually. -/
theorem FlucAvgDet_budgetFamily_absorb (d : Sizes) (hsz : SizeTendsto d) {Ψ : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a) (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n)
    {V : ℕ → Type*} {ξ : ∀ n, V n → Sizes.SeqΩ d → ℝ}
    (hfamily : ∀ θ : ℝ, 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
      PerTimeDomAt (Sizes.seqP d) d.size ξ (fun n _ _ => 4 * detFlucDelta d Ψ θ n ^ 2)) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ (fun n _ _ => Ψ n ^ 2) := by
  intro τ hτ D hD
  obtain ⟨hθ0, hθa, hθτ, hθ1⟩ := detFlucTheta_specs ha hτ
  have hsource := hfamily (detFlucTheta a τ) hθ0 hθa.le hθ1 (τ / 2) (by linarith) D hD
  filter_upwards [hsource,
    FlucAvgDet_detFlucDelta_scale_absorb d hsz hτ hθ0.le hθτ.le hΨlo] with n hn hscale v
  refine (measure_mono ?_).trans (hn v)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hscale hω

/-- **The weighted fluctuation average is `≺ Ψ²`, per time** (the fine-lattice form):
the local law, the floor `W⁻¹ ≤ Ψ`, the ceiling `Ψ ≤ size^{-a}` and `size^{-K_η} ≤ η_t` give
`‖flucAvg‖ ≺ Ψ²` for any uniform weight family with `c ≤ (W⁻¹)²` and `2 p ≤ #A` eventually. -/
theorem FlucAvgDet_weighted (d : Sizes) (hsz : SizeTendsto d) {E t Ψ : ℕ → ℝ} {a Kη : ℝ}
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (ha : 0 < a) (hKη : 0 ≤ Kη)
    (hη : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n))
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a))
    (hll : LocalLawDetSeq d E t Ψ) {V : ℕ → Type*}
    {Tw : ∀ n, V n → Idx (d.L n) (d.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx (d.L n) (d.W n))}
    (hw : ∀ n (b : V n), UniformWeight (Tw n b) (cw n) (Aw n b))
    (hcW : ∀ n, cw n ≤ ((d.W n : ℝ))⁻¹ ^ 2)
    (hcard : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ b : V n, 2 * p ≤ (Aw n b).card) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (b : V n) ω =>
        ‖flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) (Tw n b) ω‖)
      (fun n _ _ => Ψ n ^ 2) :=
  FlucAvgDet_budgetFamily_absorb d hsz ha hΨlo fun _ hθ0 hθa hθ1 =>
    FlucAvgDet_family d hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll hw hcW hcard

/-! ## 5. The bridge from `BlockIndex` to the fine lattice `Idx`

`FARowDet` / `FABlkDet` / `IBPDet` are stated on `BlockIndex` (`Sblk2`, `blkCoef2`, `greenBlk`,
`condDiagBlk`); `flucAvg`, `condExpDiag`, `condRow` live on `Idx = Z2 (W L)`.  The transport is the
equivalence `splitEquiv` (`Idx ≃ BlockIndex`), the identity `Sblk2_eq_svar`, and
`Matrix.inv_submatrix_equiv`. -/

section Bridge

/-- `greenBlk` at block indices is the fine-lattice resolvent at the `splitEquiv` coordinates
(`Matrix.inv_submatrix_equiv`). -/
theorem FlucAvgDet_greenBlk_true_apply {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (p q : BlockIndex L W) :
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

/-- `G_kk - m` at a block index `k` is `greenDiagCentered` at the fine index `splitEquiv.symm k`. -/
theorem FlucAvgDet_greenBlk_sub_eq (d : Sizes) (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (k : BlockIndex (d.L n) (d.W n)) :
    greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k
        - spectralM (E n)
      = greenDiagCentered d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
          ((splitEquiv (d.L n) (d.W n)).symm k) ω := by
  rw [FlucAvgDet_greenBlk_true_apply]
  rfl

/-- `condDiagBlk` at a block index is `condExpDiag` at the fine index `splitEquiv.symm k`. -/
theorem FlucAvgDet_condDiagBlk_eq (d : Sizes) (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (k : BlockIndex (d.L n) (d.W n)) :
    condDiagBlk d E t n ω k
      = condExpDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
          ((splitEquiv (d.L n) (d.W n)).symm k) ω := by
  unfold condDiagBlk condExpDiag
  congr 1
  funext ω'
  exact FlucAvgDet_greenBlk_sub_eq d E t n ω' k

/-- **The row family on `BlockIndex` is `flucAvg` with the weight `svar` on `Idx`**:
`∑_k S_{ik} ((G_kk - m) - E_k(G_kk - m)) = ∑_j S_{ij} Z_j` (`Sblk2_eq_svar`, `splitEquiv`). -/
theorem FlucAvgDet_row_sum_eq (d : Sizes) (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (i : BlockIndex (d.L n) (d.W n)) :
    ∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
        ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k
          - spectralM (E n)) - condDiagBlk d E t n ω k)
      = flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
          (fun j => svar (d.L n) (d.W n) ((splitEquiv (d.L n) (d.W n)).symm i) j) ω := by
  unfold flucAvg
  rw [← Equiv.sum_comp (splitEquiv (d.L n) (d.W n)).symm
    (fun j : Idx (d.L n) (d.W n) => (svar (d.L n) (d.W n)
      ((splitEquiv (d.L n) (d.W n)).symm i) j : ℂ) *
        flucDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) j ω)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sblk2_eq_svar, FlucAvgDet_greenBlk_sub_eq, FlucAvgDet_condDiagBlk_eq]
  rfl

/-- **The block family on `BlockIndex` is `flucAvg` with the weight `W⁻² 1(k ∈ 𝓘_a)` on `Idx`**:
`blkCoef2` is that weight read through `splitEquiv` (`flucVanish_blockAvg2_eq_blkCoef2`). -/
theorem FlucAvgDet_blk_sum_eq (d : Sizes) (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (a : Z2 (d.L n)) :
    ∑ k, (blkCoef2 (d.L n) (d.W n) a k : ℂ) *
        ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k
          - spectralM (E n)) - condDiagBlk d E t n ω k)
      = flucAvg d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
          (fun j : Idx (d.L n) (d.W n) =>
            if (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) = a
            then ((d.W n : ℝ))⁻¹ ^ 2 else 0) ω := by
  unfold flucAvg
  rw [← Equiv.sum_comp (splitEquiv (d.L n) (d.W n)).symm
    (fun j : Idx (d.L n) (d.W n) => ((if (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) = a
            then ((d.W n : ℝ))⁻¹ ^ 2 else 0 : ℝ) : ℂ) *
        flucDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) j ω)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hb : blkCoef2 (d.L n) (d.W n) a k =
      (if (blk (d.L n) (d.W n) ((splitEquiv (d.L n) (d.W n)).symm k).1,
        blk (d.L n) (d.W n) ((splitEquiv (d.L n) (d.W n)).symm k).2) = a
        then ((d.W n : ℝ))⁻¹ ^ 2 else 0) := by
    rw [flucVanish_blockAvg2_eq_blkCoef2, Equiv.apply_symm_apply]
  rw [hb, FlucAvgDet_greenBlk_sub_eq, FlucAvgDet_condDiagBlk_eq]
  rfl

/-- **The IBP sum on `BlockIndex` is the fine-lattice sum with `svar`**:
`∑_k S_{ik} (G_kk - m)` (`Sblk2_eq_svar`, `splitEquiv`). -/
theorem FlucAvgDet_ibp_sum_eq (d : Sizes) (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (i : BlockIndex (d.L n) (d.W n)) :
    ∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k
          - spectralM (E n))
      = ∑ j, (svar (d.L n) (d.W n) ((splitEquiv (d.L n) (d.W n)).symm i) j : ℂ) *
          (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)) j j
            - spectralM (E n)) := by
  rw [← Equiv.sum_comp (splitEquiv (d.L n) (d.W n)).symm
    (fun j : Idx (d.L n) (d.W n) => (svar (d.L n) (d.W n)
      ((splitEquiv (d.L n) (d.W n)).symm i) j : ℂ) *
        (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)) j j - spectralM (E n)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sblk2_eq_svar, FlucAvgDet_greenBlk_sub_eq]
  rfl

/-- Reindexing and pointwise rewriting of a per-time domination: if `ξ' n v = ξ n (g n v)` and
`ζ' n v = ζ n (g n v)` pointwise, the domination of `(ξ, ζ)` gives that of `(ξ', ζ')`. -/
theorem FlucAvgDet_perTime_reindex {d : Sizes} {U V : ℕ → Type*}
    {ξ ζ : ∀ n, U n → Sizes.SeqΩ d → ℝ} {ξ' ζ' : ∀ n, V n → Sizes.SeqΩ d → ℝ}
    (g : ∀ n, V n → U n) (hξ : ∀ n v ω, ξ' n v ω = ξ n (g n v) ω)
    (hζ : ∀ n v ω, ζ' n v ω = ζ n (g n v) ω)
    (h : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn v
  have hset : {ω | ((d.size n : ℕ) : ℝ) ^ τ * ζ' n v ω < ξ' n v ω}
      = {ω | ((d.size n : ℕ) : ℝ) ^ τ * ζ n (g n v) ω < ξ n (g n v) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, hζ]
  rw [hset]
  exact hn (g n v)

end Bridge

/-! ## 6. The endpoint: `fixedTimeFAThm` -/

section Endpoint

/-- **The endpoint `fixedTimeFAThm`.**  Both families of `jasdu` at `x = condDiagBlk`, with the
control `Ψ²`: the row family `t_k = S_{ik}` (`uniformWeight_svar`, `c = (5 W²)⁻¹ ≤ W⁻²`,
`#A = 5 W²`) and the block family `t_k = W⁻² 1(k ∈ 𝓘_a)` (`uniformWeight_blockAvg2`,
`c = W⁻²`, `#A = W²`), on the fine lattice (`FlucAvgDet_weighted`, with the `η` input
`size^{-1} ≤ η_t` from `eta_lower_of_rangeCond`), then transported to `BlockIndex` by the bridge.
The statement is `FixedTimeFAThm` (`AvgPins.lean`), with no added hypothesis. -/
theorem fixedTimeFAThm : FixedTimeFAThm := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE _ h1 hR Ψ a ha _ hΨ hll
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hη : ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n) :=
    (eta_lower_of_rangeCond d hκ hδ hsz hE hR).mono fun n h => by
      rw [spectralZ_im] at h
      exact h
  have hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n := hΨ.mono fun n hn => hn.1
  have hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a) := hΨ.mono fun n hn => hn.2
  have hW1 : ∀ n, (1 : ℝ) ≤ (d.W n : ℝ) := fun n => by exact_mod_cast d.W_pos n
  have hW2 : ∀ n, ((d.W n : ℝ))⁻¹ ^ 2 ≥ 0 := fun n => by positivity
  refine ⟨?_, ?_⟩
  · -- the row family `t_k = S_{ik}`
    have hrow := FlucAvgDet_weighted d hsz hE2 h1 ha (zero_le_one' ℝ) hη hΨlo hΨhi hll
      (V := fun n => Idx (d.L n) (d.W n))
      (Tw := fun n i j => svar (d.L n) (d.W n) i j)
      (cw := fun n => (5 : ℝ)⁻¹ * ((d.W n : ℝ))⁻¹ ^ 2)
      (Aw := fun n i => (Finset.univ : Finset (Idx (d.L n) (d.W n))).filter fun j =>
        (blk (d.L n) (d.W n) i.1, blk (d.L n) (d.W n) i.2)
          - (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) ∈ sbSupport (d.L n))
      (fun n i => uniformWeight_svar (d.L n) (d.W n) i)
      (fun n => by
        have := hW2 n
        nlinarith)
      (fun p => by
        filter_upwards [eventually_le_W d h𝔠 hsz hbw (2 * p)] with n hn i
        rw [card_Sblk_support]
        have h2 : d.W n ≤ d.W n ^ 2 := Nat.le_self_pow (by norm_num) _
        omega)
    exact FlucAvgDet_perTime_reindex (fun n i => (splitEquiv (d.L n) (d.W n)).symm i)
      (fun n i ω => by rw [FlucAvgDet_row_sum_eq]) (fun _ _ _ => rfl) hrow
  · -- the block family `t_k = W⁻² 1(k ∈ 𝓘_a)`
    have hblk := FlucAvgDet_weighted d hsz hE2 h1 ha (zero_le_one' ℝ) hη hΨlo hΨhi hll
      (V := fun n => Z2 (d.L n))
      (Tw := fun n a j => if (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) = a
        then ((d.W n : ℝ))⁻¹ ^ 2 else 0)
      (cw := fun n => ((d.W n : ℝ))⁻¹ ^ 2)
      (Aw := fun n a => (Finset.univ : Finset (Idx (d.L n) (d.W n))).filter fun j =>
        (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) = a)
      (fun n a => uniformWeight_blockAvg2 (d.L n) (d.W n) a)
      (fun n => le_rfl)
      (fun p => by
        filter_upwards [eventually_le_W d h𝔠 hsz hbw (2 * p)] with n hn a
        rw [card_blockAvg_support]
        have h2 : d.W n ≤ d.W n ^ 2 := Nat.le_self_pow (by norm_num) _
        omega)
    exact FlucAvgDet_perTime_reindex (fun n a => a)
      (fun n a ω => by rw [FlucAvgDet_blk_sum_eq]) (fun _ _ _ => rfl) hblk

end Endpoint

end RBM.Green
