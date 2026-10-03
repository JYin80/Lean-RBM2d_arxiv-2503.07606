/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.MinorDiffCond
import RBM2D.Green.AvgPins

/-!
# The smallness of the bad-event tower, from the high probability of the per-time good event

The endpoint `RBM.Green.flucGainUpTo'_goodEvent` (`RBM2D/Green/MinorDiffCond.lean`)
takes the numeric premise `hsmall`: the tower `badTower … (badBase d E t δ n) (M + 1)` has measure
at most `B₀^K (2 · 2δ)^{K M} / condEnv^K`.  This file **derives** it from the high probability of
the per-time good event `{ω | ∀ i j, llErrMat … i j ≤ δ n}` (the event `Ω(t, c)` of `def_asGMc`,
i.e. (4.1) of [YY_25], at the time `t n`) and nothing else probabilistic.

## The accounting

`minorDiffCond_meas_badTower_le_size` costs one factor `(ε + size n)/ε` per letter (`#Idx = size n`,
`flucAvg_card_Idx_eq_size`), so `P(badTower ε Bad₀ (M+1)) ≤ ((ε + size n)/ε)^{M+1} · P(Ω(t,c)ᶜ)`.
For fixed budgets `M`, `K` every factor is polynomially bounded in `size n` (`PolyHi`) and the
right side `B₀^K (2 · 2δ)^{KM}` is polynomially bounded below (`PolyLo`); `HighProbAt`
quantifies over every `D`, so one `D` beats the ratio (`measureReal_compl_le_of_polyLo`).

## d = 2

* The level `N` of the one-dimensional argument is the size sequence `size : ℕ → ℕ`
  (`size n = (W L)²` for `d : Sizes`).  The divergence of the sizes is the hypothesis
  `hs : Tendsto (fun n => (size n : ℝ)) atTop atTop` (`SizeTendsto d` for `d.size`), present in
  exactly the lemmas that need `1 ≤ size n` eventually.
* The row count is `#Idx = size n` exactly.
* The flow time is the single time `t n` (the good event is per time), and the two budgets are
  separate: `M` bounds the length of the words (letters) and `K` the number of slots
  (`FlucGainUpTo' … M K`; the one-dimensional argument takes `M = K = 2p`).
* `hsmall_of_highProb` is stated with `condCost … (condEps …)` on the right, the exact `hsmall`
  premise of `flucGainUpTo'_goodEvent` at `ε = condEps (E n) (t n) M (2 δ n)`; `condCost_condEps`
  turns it into `2 δ n` inside the proof.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter RBM RBM.Gauss RBM.Path RBM.Ind

open scoped ENNReal

/-! ### Polynomial envelopes -/

/-- `f` is eventually at least a fixed negative power of the size `size n` (`PolyLo`). -/
def PolyLo (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, C * ((size n : ℕ) : ℝ) ^ (-D) ≤ f n

/-- `f` is eventually at most a fixed power of the size `size n` (`PolyHi`). -/
def PolyHi (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, f n ≤ C * ((size n : ℕ) : ℝ) ^ D

theorem polyLo_const {size : ℕ → ℕ} {c : ℝ} (hc : 0 < c) : PolyLo size (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun n => by rw [neg_zero, Real.rpow_zero, mul_one]⟩

theorem polyHi_const {size : ℕ → ℕ} {c : ℝ} (hc : 0 < c) : PolyHi size (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun n => by rw [Real.rpow_zero, mul_one]⟩

theorem PolyLo.mono {size : ℕ → ℕ} {f g : ℕ → ℝ} (hf : PolyLo size f)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PolyLo size g := by
  obtain ⟨C, hC, D, hD⟩ := hf
  exact ⟨C, hC, D, by filter_upwards [hD, h] with n h1 h2 using h1.trans h2⟩

theorem PolyHi.mono {size : ℕ → ℕ} {f g : ℕ → ℝ} (hg : PolyHi size g)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PolyHi size f := by
  obtain ⟨C, hC, D, hD⟩ := hg
  exact ⟨C, hC, D, by filter_upwards [hD, h] with n h1 h2 using h2.trans h1⟩

theorem PolyLo.mul {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyLo size f) (hg : PolyLo size g) :
    PolyLo size (fun n => f n * g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hsplit : ((size n : ℕ) : ℝ) ^ (-(D + D'))
      = ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-D') := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h1' : (0 : ℝ) ≤ C * ((size n : ℕ) : ℝ) ^ (-D) := by positivity
  have h2' : (0 : ℝ) ≤ C' * ((size n : ℕ) : ℝ) ^ (-D') := by positivity
  calc C * C' * ((size n : ℕ) : ℝ) ^ (-(D + D'))
      = (C * ((size n : ℕ) : ℝ) ^ (-D)) * (C' * ((size n : ℕ) : ℝ) ^ (-D')) := by
        rw [hsplit]; ring
    _ ≤ f n * g n := mul_le_mul h1 h2 h2' (h1'.trans h1)

theorem PolyHi.mul {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyHi size f) (hg : PolyHi size g)
    (hf0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n) (hg0 : ∀ᶠ n : ℕ in atTop, 0 ≤ g n) :
    PolyHi size (fun n => f n * g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', hf0, hg0, hs.eventually_ge_atTop 1] with n h1 h2 h3 h4 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hsplit : ((size n : ℕ) : ℝ) ^ (D + D')
      = ((size n : ℕ) : ℝ) ^ D * ((size n : ℕ) : ℝ) ^ D' := Real.rpow_add hN0 _ _
  calc f n * g n ≤ (C * ((size n : ℕ) : ℝ) ^ D) * (C' * ((size n : ℕ) : ℝ) ^ D') :=
        mul_le_mul h1 h2 h4 (h3.trans h1)
    _ = C * C' * ((size n : ℕ) : ℝ) ^ (D + D') := by rw [hsplit]; ring

theorem PolyHi.add {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyHi size f) (hg : PolyHi size g) :
    PolyHi size (fun n => f n + g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C + C', by positivity, max D D', ?_⟩
  filter_upwards [hD, hD', hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hle : ((size n : ℕ) : ℝ) ^ D ≤ ((size n : ℕ) : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hle' : ((size n : ℕ) : ℝ) ^ D' ≤ ((size n : ℕ) : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
  calc f n + g n ≤ C * ((size n : ℕ) : ℝ) ^ D + C' * ((size n : ℕ) : ℝ) ^ D' := by linarith
    _ ≤ C * ((size n : ℕ) : ℝ) ^ (max D D') + C' * ((size n : ℕ) : ℝ) ^ (max D D') := by
        have a1 : C * ((size n : ℕ) : ℝ) ^ D ≤ C * ((size n : ℕ) : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle hC.le
        have a2 : C' * ((size n : ℕ) : ℝ) ^ D' ≤ C' * ((size n : ℕ) : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle' hC'.le
        linarith
    _ = (C + C') * ((size n : ℕ) : ℝ) ^ (max D D') := by ring

theorem PolyLo.pow {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyLo size f) (k : ℕ) : PolyLo size (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using polyLo_const (size := size) (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have := PolyLo.mul hs ih hf
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun n => le_of_eq (by rw [pow_succ])

theorem PolyHi.pow {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyHi size f) (hf0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n) (k : ℕ) :
    PolyHi size (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using polyHi_const (size := size) (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have hpow0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ^ k := by
        filter_upwards [hf0] with n h using pow_nonneg h k
      have := PolyHi.mul hs ih hf hpow0 hf0
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun n => le_of_eq (by rw [pow_succ])

/-- The reciprocal of a `PolyHi` function is `PolyLo`. -/
theorem PolyLo.inv {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyHi size f) (hf0 : ∀ᶠ n : ℕ in atTop, 0 < f n) :
    PolyLo size (fun n => (f n)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, hf0, hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hrp : (0 : ℝ) < ((size n : ℕ) : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * ((size n : ℕ) : ℝ) ^ D := by positivity
  have : (C * ((size n : ℕ) : ℝ) ^ D)⁻¹ ≤ (f n)⁻¹ := inv_anti₀ h2 h1
  refine le_trans (le_of_eq ?_) this
  rw [mul_inv, ← Real.rpow_neg hN0.le]

/-- The reciprocal of a `PolyLo` function is `PolyHi`. -/
theorem PolyHi.inv {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyLo size f) : PolyHi size (fun n => (f n)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, hs.eventually_ge_atTop 1] with n h1 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hrp : (0 : ℝ) < ((size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * ((size n : ℕ) : ℝ) ^ (-D) := by positivity
  have : (f n)⁻¹ ≤ (C * ((size n : ℕ) : ℝ) ^ (-D))⁻¹ := inv_anti₀ hCN h1
  refine this.trans (le_of_eq ?_)
  rw [mul_inv, ← Real.rpow_neg hN0.le, neg_neg]

/-- A `PolyLo` numerator over a `PolyHi` denominator is `PolyLo`. -/
theorem PolyLo.div {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyLo size f) (hg : PolyHi size g)
    (hg0 : ∀ᶠ n : ℕ in atTop, 0 < g n) : PolyLo size (fun n => f n / g n) := by
  have := PolyLo.mul hs hf (PolyLo.inv hs hg hg0)
  refine this.mono (Filter.Eventually.of_forall fun n => ?_)
  rw [div_eq_mul_inv]

/-! ### The only use of `HighProbAt` -/

/-- **Statement of `measureReal_compl_le_of_polyLo`**: the
complement of a `HighProbAt` event is eventually below any `PolyLo` function, once the sizes
diverge.  This is where the `∀ D` of `HighProbAt` is spent. -/
theorem measureReal_compl_le_of_polyLo :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
    Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop →
    ∀ {Ξ : ℕ → Set Ω}, HighProbAt P size Ξ → ∀ {f : ℕ → ℝ}, PolyLo size f →
      ∀ᶠ n : ℕ in atTop, P.real (Ξ n)ᶜ ≤ f n := by
  intro Ω _ P size hs Ξ hΞ f hf
  obtain ⟨C, hC, D, hD⟩ := hf
  have hD'pos : (0 : ℝ) < max (D + 1) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hΞ (max (D + 1) 1) hD'pos, hD, hs.eventually_ge_atTop 1,
    hs.eventually_ge_atTop C⁻¹] with n h1 h2 hN1 hNC
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  set D' : ℝ := max (D + 1) 1 with hD'
  -- the measure bound, transported to `ℝ`
  have hstep1 : P.real (Ξ n)ᶜ ≤ ((size n : ℕ) : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P (Ξ n)ᶜ).toReal ≤ (ENNReal.ofReal (((size n : ℕ) : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = ((size n : ℕ) : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)
  -- and the arithmetic `size^{-D'} ≤ C size^{-D}`
  have hCN : ((size n : ℕ) : ℝ)⁻¹ ≤ C := (inv_le_comm₀ hC hN0).1 hNC
  have hDD : (1 : ℝ) ≤ D' - D := by
    have : D + 1 ≤ D' := le_max_left _ _
    linarith
  have hsmallexp : ((size n : ℕ) : ℝ) ^ (-(D' - D)) ≤ C := by
    calc ((size n : ℕ) : ℝ) ^ (-(D' - D)) ≤ ((size n : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = ((size n : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ C := hCN
  have hstep2 : ((size n : ℕ) : ℝ) ^ (-D') ≤ C * ((size n : ℕ) : ℝ) ^ (-D) := by
    have hsplit : ((size n : ℕ) : ℝ) ^ (-D')
        = ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-(D' - D)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ ((size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    calc ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-(D' - D))
        ≤ ((size n : ℕ) : ℝ) ^ (-D) * C := mul_le_mul_of_nonneg_left hsmallexp hnn
      _ = C * ((size n : ℕ) : ℝ) ^ (-D) := by ring
  exact hstep1.trans (hstep2.trans h2)

/-! ### `hsmall`, derived -/

/-- **Statement of `hsmall_of_highProb`** (per time): the `hsmall`
premise of `flucGainUpTo'_goodEvent` at `ε = condEps (E n) (t n) M (2 δ n)`, for every
pair of budgets `M, K`, from the high probability of the per-time good event (4.1).  The price
`condEnv^K ((ε + size)/ε)^{M+1}` is `PolyHi`, the target is `PolyLo`, and one `D` of
`HighProbAt` beats their ratio. -/
theorem hsmall_of_highProb :
  ∀ (d : Sizes) {E t δ : ℕ → ℝ}, SizeTendsto d → (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    (∀ n, 0 < δ n) → PolyLo d.size δ →
    PolyHi d.size (fun n => (RBM.Path.etaT (E n) (t n))⁻¹ + 1) →
    HighProbAt (Sizes.seqP d) d.size (fun n => {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
      llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n}) →
    ∀ M K : ℕ, ∀ᶠ n : ℕ in atTop,
      condEnv (E n) (t n) M ^ K
          * (Sizes.seqP d).real (badTower d n (condEps (E n) (t n) M (2 * δ n))
              (badBase d E t δ n) (M + 1))
        ≤ (2 * minorDiffC M * (2 * δ n)
            + condCost (E n) (t n) M (2 * δ n) (condEps (E n) (t n) M (2 * δ n))) ^ K
          * (2 * (2 * δ n)) ^ (K * M) := by
  intro d E t δ hsz hE ht1 hδpos hδlo hηhi hΩ M K
  classical
  have hΨpos : ∀ n, (0 : ℝ) < 2 * δ n := fun n => by linarith [hδpos n]
  have hηt : ∀ n, 0 < RBM.Path.etaT (E n) (t n) := fun n => etaT_pos (hE n) (ht1 n)
  have hEnv0 : ∀ n, (0 : ℝ) < condEnv (E n) (t n) M := fun n =>
    lt_of_lt_of_le zero_lt_one (one_le_condEnv (hE n) (ht1 n) M)
  have hMEnv0 : ∀ n, (0 : ℝ) < ((M : ℝ) + 1) * condEnv (E n) (t n) M := fun n => by
    have := hEnv0 n; positivity
  have heps0 : ∀ n, (0 : ℝ) < condEps (E n) (t n) M (2 * δ n) := by
    intro n
    change (0 : ℝ) < (2 * δ n) * (2 * (2 * δ n)) ^ M
      * (((M : ℝ) + 1) * condEnv (E n) (t n) M)⁻¹
    have h1 := hΨpos n
    have h3 : (0 : ℝ) < (2 * (2 * δ n)) ^ M := by positivity
    exact mul_pos (mul_pos h1 h3) (inv_pos.2 (hMEnv0 n))
  have hR0 : ∀ n, (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := fun n => Nat.cast_nonneg _
  have hq0 : ∀ n, (0 : ℝ) < (condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
      / condEps (E n) (t n) M (2 * δ n) := fun n =>
    div_pos (add_pos_of_pos_of_nonneg (heps0 n) (hR0 n)) (heps0 n)
  have hG0 : ∀ n, (0 : ℝ) < condEnv (E n) (t n) M ^ K
      * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) := fun n =>
    mul_pos (pow_pos (hEnv0 n) K) (pow_pos (hq0 n) (M + 1))
  -- the target is bounded below by a fixed negative power of the size
  have hΨlo : PolyLo d.size fun n => 2 * δ n :=
    hδlo.mono (Filter.Eventually.of_forall fun n => by linarith [(hδpos n).le])
  have hB0lo : PolyLo d.size fun n => 2 * minorDiffC M * (2 * δ n) + 2 * δ n :=
    hΨlo.mono (Filter.Eventually.of_forall fun n => by
      have h1 := minorDiffC_nonneg M
      have h2 := (hδpos n).le
      nlinarith)
  have h2Ψlo : PolyLo d.size fun n => 2 * (2 * δ n) :=
    hΨlo.mono (Filter.Eventually.of_forall fun n => by linarith [(hδpos n).le])
  have hSlo : PolyLo d.size fun n =>
      (2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M) :=
    (hB0lo.pow hsz K).mul hsz (h2Ψlo.pow hsz (K * M))
  -- the price is bounded above by a fixed power of the size
  have hEnvhi : PolyHi d.size fun n => condEnv (E n) (t n) M := by
    have hc : PolyHi d.size fun _ : ℕ => (2 : ℝ) ^ (2 * M + 1) := polyHi_const (by positivity)
    have hnn : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (RBM.Path.etaT (E n) (t n))⁻¹ + 1 :=
      Filter.Eventually.of_forall fun n => by
        have : (0 : ℝ) ≤ (RBM.Path.etaT (E n) (t n))⁻¹ := inv_nonneg.2 (hηt n).le
        linarith
    have h := hc.mul hsz hηhi (Filter.Eventually.of_forall fun _ => by positivity) hnn
    exact h.mono (Filter.Eventually.of_forall fun n => le_of_eq rfl)
  have hMEnvhi : PolyHi d.size fun n => ((M : ℝ) + 1) * condEnv (E n) (t n) M :=
    (polyHi_const (c := (M : ℝ) + 1) (by positivity)).mul hsz hEnvhi
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun n => (hEnv0 n).le)
  have hepslo : PolyLo d.size fun n => condEps (E n) (t n) M (2 * δ n) := by
    have h := (hΨlo.mul hsz (h2Ψlo.pow hsz M)).mul hsz
      (PolyLo.inv hsz hMEnvhi (Filter.Eventually.of_forall hMEnv0))
    exact h.mono (Filter.Eventually.of_forall fun n => le_of_eq rfl)
  have hRhi : PolyHi d.size fun n => ((d.size n : ℕ) : ℝ) :=
    ⟨1, one_pos, 1, Filter.Eventually.of_forall fun n => by rw [Real.rpow_one, one_mul]⟩
  have hquothi : PolyHi d.size fun n =>
      (condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
        / condEps (E n) (t n) M (2 * δ n) := by
    have hprod : PolyHi d.size fun n =>
        ((d.size n : ℕ) : ℝ) * (condEps (E n) (t n) M (2 * δ n))⁻¹ :=
      hRhi.mul hsz (PolyHi.inv hsz hepslo) (Filter.Eventually.of_forall hR0)
        (Filter.Eventually.of_forall fun n => (inv_pos.2 (heps0 n)).le)
    refine ((polyHi_const (c := (1 : ℝ)) one_pos).add hsz hprod).mono
      (Filter.Eventually.of_forall fun n => le_of_eq ?_)
    rw [add_div, div_self (heps0 n).ne', div_eq_mul_inv]
  have hGhi : PolyHi d.size fun n => condEnv (E n) (t n) M ^ K
      * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) :=
    (hEnvhi.pow hsz (Filter.Eventually.of_forall fun n => (hEnv0 n).le) K).mul hsz
      (hquothi.pow hsz (Filter.Eventually.of_forall fun n => (hq0 n).le) (M + 1))
      (Filter.Eventually.of_forall fun n => pow_nonneg (hEnv0 n).le K)
      (Filter.Eventually.of_forall fun n => pow_nonneg (hq0 n).le (M + 1))
  -- and (4.1) beats the quotient
  have hkey := measureReal_compl_le_of_polyLo (Sizes.seqP d) d.size hsz hΩ
    (hSlo.div hsz hGhi (Filter.Eventually.of_forall hG0))
  filter_upwards [hkey] with n hn
  -- the tower's measure
  have hε0 : (0 : ℝ) ≤ condEps (E n) (t n) M (2 * δ n) := (heps0 n).le
  have htow := minorDiffCond_meas_badTower_le_size d n
    (ε := condEps (E n) (t n) M (2 * δ n)) (measurableSet_badBase d E t δ n) (M + 1)
  have hfin : ((ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n))
      + ((d.size n : ℕ) : ℝ≥0∞)) ^ (M + 1) * (Sizes.seqP d) (badBase d E t δ n)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)) (measure_ne_top _ _)
  have hL : (ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
        * (Sizes.seqP d) (badTower d n (condEps (E n) (t n) M (2 * δ n))
            (badBase d E t δ n) (M + 1))).toReal
      = condEps (E n) (t n) M (2 * δ n) ^ (M + 1)
        * (Sizes.seqP d).real (badTower d n (condEps (E n) (t n) M (2 * δ n))
            (badBase d E t δ n) (M + 1)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε0, measureReal_def]
  have hRr : ((ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n))
        + ((d.size n : ℕ) : ℝ≥0∞)) ^ (M + 1) * (Sizes.seqP d) (badBase d E t δ n)).toReal
      = (condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ)) ^ (M + 1)
        * (Sizes.seqP d).real (badBase d E t δ n) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
      ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast, measureReal_def]
  have hreal := ENNReal.toReal_mono hfin htow
  rw [hL, hRr] at hreal
  have hp0 : (Sizes.seqP d).real (badBase d E t δ n)
      = (Sizes.seqP d).real {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
          llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n}ᶜ := by
    rw [measureReal_def, measureReal_def, meas_badBase]
  have hp0nn : (0 : ℝ) ≤ (Sizes.seqP d).real (badBase d E t δ n) := measureReal_nonneg
  -- divide by `ε^{M+1}`
  have hA : (Sizes.seqP d).real
        (badTower d n (condEps (E n) (t n) M (2 * δ n)) (badBase d E t δ n) (M + 1))
      ≤ ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
        * (Sizes.seqP d).real (badBase d E t δ n) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos (heps0 n) (M + 1)), mul_comm]
    exact hreal
  -- the price of conditionalizing is exactly `2 δ n` at `ε = condEps`
  have hcc : condCost (E n) (t n) M (2 * δ n) (condEps (E n) (t n) M (2 * δ n)) = 2 * δ n :=
    condCost_condEps (hE n) (ht1 n) M (hΨpos n)
  rw [hcc]
  calc condEnv (E n) (t n) M ^ K
        * (Sizes.seqP d).real
          (badTower d n (condEps (E n) (t n) M (2 * δ n)) (badBase d E t δ n) (M + 1))
      ≤ condEnv (E n) (t n) M ^ K
          * (((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
            * (Sizes.seqP d).real (badBase d E t δ n)) :=
        mul_le_mul_of_nonneg_left hA (pow_nonneg (hEnv0 n).le K)
    _ = (condEnv (E n) (t n) M ^ K
          * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))
        * (Sizes.seqP d).real (badBase d E t δ n) := by ring
    _ ≤ (condEnv (E n) (t n) M ^ K
          * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))
        * (((2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M))
          / (condEnv (E n) (t n) M ^ K
            * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
                / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG0 n).le
        rw [hp0]; exact hn
    _ = (2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M) := by
        have hGne : condEnv (E n) (t n) M ^ K
            * ((condEps (E n) (t n) M (2 * δ n) + ((d.size n : ℕ) : ℝ))
                / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) ≠ 0 := (hG0 n).ne'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hGne]

end RBM.Green
