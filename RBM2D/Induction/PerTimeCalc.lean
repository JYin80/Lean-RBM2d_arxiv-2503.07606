/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.PerTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `≺`-calculus for the per-time predicate `PerTimeDomAt`

Generic manipulations of the domination relation `ξ ≺ ζ` along the admissible dimensions
`size l`, parallel to the one-dimensional formalization and stated

* for the per-time predicate `RBM.Path.PerTimeDomAt` (namespace `PerTime`), and
* for the uniform predicate `RBM.StochDomAt` (namespace `Unif`).

The index change is `N ↦ size l` (thresholds `N^τ ↦ (size l)^τ`, rates `N^{-D} ↦ (size l)^{-D}`,
`∀ᶠ N ↦ ∀ᶠ l`).  In `d = 1`, `N → ∞` comes from the filter `atTop` on `N`; here it becomes the
explicit hypothesis `hsize : Tendsto size atTop atTop`, which is present exactly in the lemmas
that need it.

The base layer is public with the file-stem prefix `perTimeCalc_` (the `N`-indexed lemmas
`RBM.StochDom.*` do not apply to `StochDomAt`).

## The hypothesis `hsize`

`hsize : Tendsto size atTop atTop` is present in `PerTime`/`Unif` `perTimeCalc_of_imp_union`,
`perTimeCalc_refl`, `perTimeCalc_add`, `perTimeCalc_mul`, `perTimeCalc_mono`,
`of_le_add_sqrt_mul`, `finset_sum_of`, `stochDom_of_indicator`, `stochDom_of_forall_or`,
`stochDom_of_le_const_mul`, `stochDom_of_highProb`, in `Unif.forbidden_region`, in
`perTimeCalc_highProbAt_inter` and in `stepOneBootstrap`.  It is used for `∀ᶠ l, 2 ≤ size l`
(two-term union bound `2 x^{-(D+1)} ≤ x^{-D}`), `∀ᶠ l, 1 ≤ size l` or `∀ᶠ l, C ≤ (size l)^{τ'}`;
the per-time lemmas `stochDom_of_highProb`, `stochDom_of_le_const_mul`, `of_le_add_sqrt_mul` and
`finset_sum_of` are false without it.

## Not stated

The per-time variant of `forbidden_region` is not stated: its conclusion is a `HighProbAt` event
with the union over `u` inside `P`, which the per-time hypothesis does not control.  Only the
uniform variant `Unif.forbidden_region` is provided.
-/

namespace RBM.Ind.PerTimeCalc

open MeasureTheory Filter RBM RBM.Gauss RBM.Path
open scoped ENNReal

/-! ### Pure real facts -/

/-- The elementary inequality behind the last step of §6: for `s ≥ 0`, `T ≥ 1`,
`s² ≤ T(r² + r s)` implies `s² ≤ 4T²r²`. -/
theorem sq_le_four_mul_of_le_add_mul {s r T : ℝ} (hs : 0 ≤ s) (hT : 1 ≤ T)
    (h : s ^ 2 ≤ T * (r ^ 2 + r * s)) : s ^ 2 ≤ 4 * T ^ 2 * r ^ 2 := by
  rcases le_or_gt s (2 * T * r) with h1 | h1
  · have : s ^ 2 ≤ (2 * T * r) ^ 2 := pow_le_pow_left₀ hs h1 2
    nlinarith
  · have hTr : T * r * s ≤ s ^ 2 / 2 := by nlinarith
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith

/-- `N^{τ} N^{-ε} < 1` for `τ < ε`, `N ≥ 2` (here `N` is a value `size l`). -/
theorem rpow_mul_rpow_neg_lt_one {N : ℕ} (hN : 2 ≤ N) {τ ε : ℝ} (hτε : τ < ε) :
    (N : ℝ) ^ τ * (N : ℝ) ^ (-ε) < 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)

/-- **The continuity argument, deterministic core.**  If `g` and `a` are continuous on
`[s, t]`, `g(s) < a(s)`, and `g(u) ≠ a(u)` for all `u ∈ [s, t]`, then `g < a` on `[s, t]`
(intermediate value theorem). -/
theorem lt_of_forall_ne_of_continuousOn {g a : ℝ → ℝ} {s t : ℝ}
    (hg : ContinuousOn g (Set.Icc s t)) (ha : ContinuousOn a (Set.Icc s t)) (h0 : g s < a s)
    (hne : ∀ u ∈ Set.Icc s t, g u ≠ a u) : ∀ u ∈ Set.Icc s t, g u < a u := by
  intro u hu
  by_contra hno
  push Not at hno
  have hsub : Set.Icc s u ⊆ Set.Icc s t := Set.Icc_subset_Icc_right hu.2
  have hc : ContinuousOn (fun v => a v - g v) (Set.Icc s u) := (ha.sub hg).mono hsub
  have h0' : (0 : ℝ) ∈ Set.Icc (a u - g u) (a s - g s) := ⟨by linarith, by linarith⟩
  obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hu.1 hc h0'
  exact hne v (hsub hv) (by simp only at hv0; linarith)

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Two events with `P ≤ x^{-(D+1)}` give `P (A ∪ B) ≤ x^{-D}` once `2 x^{-(D+1)} ≤ x^{-D}`. -/
private theorem measure_union_le_of_two {A B : Set Ω} {x D : ℝ} (hx : 0 ≤ x)
    (hA : P A ≤ ENNReal.ofReal (x ^ (-(D + 1)))) (hB : P B ≤ ENNReal.ofReal (x ^ (-(D + 1))))
    (h : 2 * x ^ (-(D + 1)) ≤ x ^ (-D)) : P (A ∪ B) ≤ ENNReal.ofReal (x ^ (-D)) := by
  have hp : (0 : ℝ) ≤ x ^ (-(D + 1)) := Real.rpow_nonneg hx _
  calc P (A ∪ B) ≤ P A + P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (x ^ (-(D + 1))) + ENNReal.ofReal (x ^ (-(D + 1))) := add_le_add hA hB
    _ = ENNReal.ofReal (2 * x ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (x ^ (-D)) := ENNReal.ofReal_le_ofReal h

/-! ### `HighProbAt`: monotonicity and finite intersections

The `size`-indexed analogues of the monotonicity and intersection lemmas for events of high
probability. -/

/-- Monotonicity of `HighProbAt`. -/
theorem perTimeCalc_highProbAt_mono {Ξ Ξ' : ℕ → Set Ω} (h : HighProbAt P size Ξ)
    (hsub : ∀ᶠ l : ℕ in atTop, Ξ l ⊆ Ξ' l) : HighProbAt P size Ξ' := by
  intro D hD
  filter_upwards [h D hD, hsub] with l hN hs
  exact (measure_mono (Set.compl_subset_compl.2 hs)).trans hN

/-- Two `HighProbAt` events hold simultaneously with high probability (needs `size → ∞`). -/
theorem perTimeCalc_highProbAt_inter (hsize : Tendsto size atTop atTop) {Ξ₁ Ξ₂ : ℕ → Set Ω}
    (h₁ : HighProbAt P size Ξ₁) (h₂ : HighProbAt P size Ξ₂) :
    HighProbAt P size (fun l => Ξ₁ l ∩ Ξ₂ l) := by
  intro D hD
  filter_upwards [h₁ (D + 1) (by linarith), h₂ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l hN1 hN2 h3
  rw [Set.compl_inter]
  exact measure_union_le_of_two (Nat.cast_nonneg _) hN1 hN2 h3

/-- **`StochDomAt` gives a high-probability event**: `{∀ u, ξ ≤ (size l)^τ ζ}` holds with high
probability. -/
theorem perTimeCalc_highProbAt_of_stochDomAt {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with l hN
  convert hN using 2
  ext ω; simp [badSetAt]

end Generic

/-! ### Pointwise cores

The pointwise implications behind each domination lemma.  They do not mention `P`, so the same
core serves the per-time variant (`PerTime`) and the uniform variant (`Unif`). -/

section Cores

variable {Ω : Type*} {size : ℕ → ℕ} {U : ℕ → Type*}

private theorem imp_mono_right {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ ζ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ' l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with l hl u ω hu
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hl u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) τ)) hu

private theorem imp_rpow_of_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ l u ω) ^ r < (ξ l u ω) ^ r →
        (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  rcases Nat.eq_zero_or_pos (size l) with h0 | h1
  · rw [h0] at hu ⊢
    simp only [Nat.cast_zero, Real.zero_rpow hτ.ne', zero_mul] at hu ⊢
    rcases (hξ l u ω).eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hr0.ne'] at hu
      exact absurd hu (lt_irrefl _)
    · exact h
  · refine lt_of_not_ge fun hle => ?_
    have hN : (1 : ℝ) ≤ (size l : ℝ) ^ τ :=
      Real.one_le_rpow (by exact_mod_cast h1) hτ.le
    have h1' : (ξ l u ω) ^ r ≤ ((size l : ℝ) ^ τ * ζ l u ω) ^ r :=
      Real.rpow_le_rpow (hξ l u ω) hle hr0.le
    rw [Real.mul_rpow (by linarith) (hζ l u ω)] at h1'
    have h2 : ((size l : ℝ) ^ τ) ^ r ≤ (size l : ℝ) ^ τ := Real.rpow_le_self_of_one_le hN hr1
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (hζ l u ω) r)
    exact absurd hu (not_lt.2 (h1'.trans h3))

private theorem imp_of_le_add_sqrt_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * (ζ l u ω + Real.sqrt (ζ l u ω * ξ l u ω)) < ξ l u ω := by
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  filter_upwards [hsize.eventually
    (eventually_le_rpow 4 (by positivity : (0 : ℝ) < τ / 3))] with l h4 u ω hu
  refine lt_of_not_ge fun hle => ?_
  set T := (size l : ℝ) ^ (τ / 3)
  have hT1 : 1 ≤ T := by linarith
  have hT3 : T ^ 3 = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; push_cast; ring
  set x := ξ l u ω
  set a := ζ l u ω
  have hx := hξ l u ω
  have ha := hζ l u ω
  have hs := Real.sq_sqrt hx
  have hr := Real.sq_sqrt ha
  have key : Real.sqrt x ^ 2 ≤ T * (Real.sqrt a ^ 2 + Real.sqrt a * Real.sqrt x) := by
    rw [hs, hr, ← Real.sqrt_mul ha]; exact hle
  have h4' := sq_le_four_mul_of_le_add_mul (Real.sqrt_nonneg _) hT1 key
  rw [hs, hr] at h4'
  have : 4 * T ^ 2 * a ≤ T ^ 3 * a := by
    have : 4 * T ^ 2 ≤ T ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this ha
  rw [hT3] at this
  exact absurd hu (not_lt.2 (h4'.trans this))

private theorem imp_add {ξ₁ ξ₂ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ₁ l u ω + ζ₂ l u ω) < ξ₁ l u ω + ξ₂ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  by_contra hno
  simp only [not_or, not_lt] at hno
  simp only [mul_add] at hu
  linarith [hno.1, hno.2]

private theorem imp_mul {ξ₁ ξ₂ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω)
    (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * (ζ₁ l u ω * ζ₂ l u ω) < ξ₁ l u ω * ξ₂ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  by_contra hno
  simp only [not_or, not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := calc ξ₁ l u ω * ξ₂ l u ω
        ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ξ₂ l u ω :=
          mul_le_mul_of_nonneg_right hno.1 (hξ₂ l u ω)
    _ ≤ ((size l : ℝ) ^ (τ / 2) * ζ₁ l u ω) * ((size l : ℝ) ^ (τ / 2) * ζ₂ l u ω) :=
        mul_le_mul_of_nonneg_left hno.2 (mul_nonneg hpos (hζ₁ l u ω))
    _ = ((size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2)) * (ζ₁ l u ω * ζ₂ l u ω) := by ring
    _ = (size l : ℝ) ^ τ * (ζ₁ l u ω * ζ₂ l u ω) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  linarith

private theorem imp_mono (hsize : Tendsto size atTop atTop) {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hζ' : ∀ l u ω, 0 ≤ ζ' l u ω) (C : ℝ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ C * ζ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ' l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ l u ω := by
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow C (half_pos hτ))] with l hN hC u ω hu
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ (τ / 2) * ζ l u ω
      ≤ (size l : ℝ) ^ (τ / 2) * (C * ζ' l u ω) := mul_le_mul_of_nonneg_left (hN u ω) hpos
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ' l u ω) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (hζ' l u ω)) hpos
    _ = (size l : ℝ) ^ τ * ζ' l u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
    _ < ξ l u ω := hu

private theorem imp_forall_or {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (hor : ∀ l u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall fun l u ω hu => ?_⟩
  have hpos : 0 ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases hor l u ω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])
  · exact Or.inr (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])

private theorem imp_left_eventually {ξ ξ' ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ ξ' l u ω) :
    ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ l u ω < ξ' l u ω := by
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with l hl u ω hu
  exact lt_of_lt_of_le hu (hl u ω)

end Cores

/-! ### The per-time variants (`PerTimeDomAt`) -/

section PerTimeSection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

namespace PerTime

variable {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}

/-! #### Base layer (per time) -/

/-- A failure event eventually contained in the failure event of a single domination
(pointwise form). -/
theorem perTimeCalc_of_imp (h : PerTimeDomAt P size ξ₁ ζ₁)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2 u
  exact (measure_mono fun ω hω => h1 u ω hω).trans (h2 u)

/-- A failure event eventually contained in the union of two failure events (pointwise form). -/
theorem perTimeCalc_of_imp_union (hsize : Tendsto size atTop atTop)
    (h₁ : PerTimeDomAt P size ξ₁ ζ₁) (h₂ : PerTimeDomAt P size ξ₂ ζ₂)
    (himp : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω,
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (size l : ℝ) ^ τ' * ζ₁ l u ω < ξ₁ l u ω ∨ (size l : ℝ) ^ τ' * ζ₂ l u ω < ξ₂ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3 u
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) (h1 u) (h2 u) h3)
  intro ω hω
  rcases h0 u ω hω with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- `ζ ≺ ζ` for a non-negative family (needs `1 ≤ size l` eventually). -/
theorem perTimeCalc_refl (hsize : Tendsto size atTop atTop) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    PerTimeDomAt P size ζ ζ := by
  intro τ hτ D hD
  filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with l hl u
  have hN : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl) hτ.le
  have hE : {ω | (size l : ℝ) ^ τ * ζ l u ω < ζ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hζ l u ω]
  rw [hE, measure_empty]
  exact zero_le

/-- `≺` is closed under addition. -/
theorem perTimeCalc_add (hsize : Tendsto size atTop atTop) (h₁ : PerTimeDomAt P size ξ₁ ζ₁)
    (h₂ : PerTimeDomAt P size ξ₂ ζ₂) :
    PerTimeDomAt P size (fun l u ω => ξ₁ l u ω + ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω + ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ imp_add

/-- `≺` is closed under multiplication of non-negative quantities. -/
theorem perTimeCalc_mul (hsize : Tendsto size atTop atTop) (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω)
    (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) (h₁ : PerTimeDomAt P size ξ₁ ζ₁)
    (h₂ : PerTimeDomAt P size ξ₂ ζ₂) :
    PerTimeDomAt P size (fun l u ω => ξ₁ l u ω * ξ₂ l u ω)
      (fun l u ω => ζ₁ l u ω * ζ₂ l u ω) :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_mul hξ₂ hζ₁)

/-- `ξ ≺ ζ` and `ζ ≤ C ζ'` (eventually, pointwise) give `ξ ≺ ζ'`. -/
theorem perTimeCalc_mono (hsize : Tendsto size atTop atTop) {ζ' : ∀ l, U l → Ω → ℝ}
    (hζ' : ∀ l u ω, 0 ≤ ζ' l u ω) (C : ℝ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ C * ζ' l u ω) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono hsize hζ' C hle)

/-! #### Powers, square roots and sums -/

/-- Enlarging the right side of `≺` (for large `l`). -/
theorem mono_right_eventually {ζ' : ∀ l, U l → Ω → ℝ} (h : PerTimeDomAt P size ξ ζ)
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l u ω ≤ ζ' l u ω) : PerTimeDomAt P size ξ ζ' :=
  perTimeCalc_of_imp h (imp_mono_right hle)

/-- Powers `0 < r ≤ 1` preserve `≺`: `ξ ≺ ζ` implies `ξ^r ≺ ζ^r`; no growth hypothesis on `size`
(the case `size l = 0` is treated separately). -/
theorem rpow_of_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l u ω ^ r) (fun l u ω => ζ l u ω ^ r) :=
  perTimeCalc_of_imp h (imp_rpow_of_le_one hr0 hr1 hξ hζ)

/-- Square roots preserve `≺`. -/
theorem sqrt_of (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => Real.sqrt (ξ l u ω)) (fun l u ω => Real.sqrt (ζ l u ω)) := by
  simp only [Real.sqrt_eq_rpow]
  exact rpow_of_le_one (by norm_num) (by norm_num) hξ hζ h

/-- **Absorbing `(size l)^δ`**: if `ξ ≺ (size l)^δ ζ` for every `δ > 0`, then `ξ ≺ ζ`. -/
theorem of_forall_rpow_mul
    (h : ∀ δ > (0 : ℝ), PerTimeDomAt P size ξ (fun l u ω => (size l : ℝ) ^ δ * ζ l u ω)) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) (τ / 2) (half_pos hτ) D hD] with l hl u
  refine (measure_mono ?_).trans (hl u)
  intro ω hω
  change (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) < ξ l u ω
  rwa [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]

/-- **The last step of Section 6**: `X ≺ A + A^{1/2} X^{1/2}` implies `X ≺ A` (for `X, A ≥ 0`). -/
theorem of_le_add_sqrt_mul (hsize : Tendsto size atTop atTop)
    (hξ : ∀ l u ω, 0 ≤ ξ l u ω) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : PerTimeDomAt P size ξ (fun l u ω => ζ l u ω + Real.sqrt (ζ l u ω * ξ l u ω))) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_of_le_add_sqrt_mul hsize hξ hζ)

/-- `≺` is closed under finite sums. -/
theorem finset_sum_of (hsize : Tendsto size atTop atTop) {ι : Type*} (s : Finset ι)
    {ξ ζ : ι → ∀ l, U l → Ω → ℝ} (h : ∀ i ∈ s, PerTimeDomAt P size (ξ i) (ζ i)) :
    PerTimeDomAt P size (fun l u ω => ∑ i ∈ s, ξ i l u ω) (fun l u ω => ∑ i ∈ s, ζ i l u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := perTimeCalc_refl (P := P) (size := size) hsize
      (ζ := fun (l : ℕ) (_ : U l) (_ : Ω) => (0 : ℝ)) (fun _ _ _ => le_rfl)
    simpa using h0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact perTimeCalc_add hsize (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! #### Indicators, case splits and high probability -/

/-- **Removing a parameter-dependent indicator.**  If `1_{Ω(l,u)} ξ ≺ ζ` and the events
`Ω(l,u)` hold for all `u` simultaneously with high probability, then `ξ ≺ ζ`. -/
theorem stochDom_of_indicator (hsize : Tendsto size atTop atTop)
    {Ωs : ∀ l, U l → Set Ω} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hΩ : HighProbAt P size (fun l => {ω | ∀ u, ω ∈ Ωs l u}))
    (h : PerTimeDomAt P size (fun l u ω => (Ωs l u).indicator (fun ω => ξ l u ω) ω) ζ) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ (D + 1) (by linarith), hΩ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h1 h2 h3 u
  refine (measure_mono ?_).trans (measure_union_le_of_two (Nat.cast_nonneg _) (h1 u) h2 h3)
  intro ω hu
  by_cases hω : ∀ u, ω ∈ Ωs l u
  · refine Or.inl ?_
    change (size l : ℝ) ^ τ * ζ l u ω < (Ωs l u).indicator (fun ω => ξ l u ω) ω
    rw [Set.indicator_of_mem (hω u)]
    exact hu
  · exact Or.inr hω

/-- **Case splitting under `≺`**: if at every `(l, u, ω)` the pair `(ξ, ζ)` is dominated by
`(ξ₁, ζ₁)` or by `(ξ₂, ζ₂)` (`ξ ≤ ξᵢ`, `ζᵢ ≤ ζ`), then `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` give `ξ ≺ ζ`. -/
theorem stochDom_of_forall_or (hsize : Tendsto size atTop atTop)
    {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ₁ ζ₁) (h₂ : PerTimeDomAt P size ξ₂ ζ₂)
    (hor : ∀ l u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) : PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp_union hsize h₁ h₂ (imp_forall_or hor)

/-- A pointwise bound `ξ ≤ C ζ` (`ξ, ζ ≥ 0`) gives `ξ ≺ ζ`. -/
theorem stochDom_of_le_const_mul (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, 0 ≤ ξ l u ω)
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) (C : ℝ) (h : ∀ l u ω, ξ l u ω ≤ C * ζ l u ω) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_mono hsize hζ C (Eventually.of_forall h) (perTimeCalc_refl hsize hξ)

/-- A left side that is eventually pointwise smaller. -/
theorem stochDom_of_le_left_eventually {ξ ξ' ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ ξ' l u ω) (h : PerTimeDomAt P size ξ' ζ) :
    PerTimeDomAt P size ξ ζ :=
  perTimeCalc_of_imp h (imp_left_eventually hle)

/-- **High probability gives `≺`**: if `ξ ≤ ζ` for all `u` w.h.p. (`ζ ≥ 0`), then `ξ ≺ ζ`. -/
theorem stochDom_of_highProb (hsize : Tendsto size atTop atTop)
    {ξ ζ : ∀ l, U l → Ω → ℝ} (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (h : HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ ζ l u ω})) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h D hD, hsize.eventually (eventually_ge_atTop 1)] with l hl hl1 u
  refine (measure_mono ?_).trans hl
  intro ω hω hω'
  have h1 : (1 : ℝ) ≤ (size l : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hl1) hτ.le
  have := hω' u
  have hω'' : (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω := hω
  nlinarith [hζ l u ω]

end PerTime

end PerTimeSection

/-! ### The uniform variants (`StochDomAt`) -/

section UnifSection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

namespace Unif

/-- **The forbidden region (5.9).**  Let `x ≥ 0` be random and `f, a, b` deterministic with
`a > 0`.  If `1(x ≤ b) x ≺ f` and `f ≪ a` (i.e. `f ≤ (size l)^{-ε} a` for some `ε > 0`), then
with high probability `x` avoids `[a, b]`, simultaneously for all parameters `u`.  Only the uniform
variant is stated (the per-time variant is false, see the module docstring). -/
theorem forbidden_region (hsize : Tendsto size atTop atTop) {x : ∀ l, U l → Ω → ℝ}
    {f a b : ∀ l, U l → ℝ}
    (ha : ∀ l u, 0 < a l u) {ε : ℝ} (hε : 0 < ε)
    (hfa : ∀ᶠ l : ℕ in atTop, ∀ u, f l u ≤ (size l : ℝ) ^ (-ε) * a l u)
    (h : StochDomAt P size (fun l u ω => {ω | x l u ω ≤ b l u}.indicator (fun ω => x l u ω) ω)
      (fun l u _ => f l u)) :
    HighProbAt P size (fun l => {ω | ∀ u, x l u ω < a l u ∨ b l u < x l u ω}) := by
  refine perTimeCalc_highProbAt_mono (perTimeCalc_highProbAt_of_stochDomAt h (half_pos hε)) ?_
  filter_upwards [hfa, hsize.eventually (eventually_ge_atTop 2)] with l hN hN2
  intro ω hω u
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hno
  push Not at hno
  obtain ⟨hax, hxb⟩ := hno
  have h1 := hω u
  have hmem : x l u ω ≤ b l u := hxb
  rw [Set.indicator_of_mem (show ω ∈ {ω | x l u ω ≤ b l u} from hmem)] at h1
  have hpos : 0 ≤ (size l : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : (size l : ℝ) ^ (ε / 2) * f l u ≤
      (size l : ℝ) ^ (ε / 2) * (size l : ℝ) ^ (-ε) * a l u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hN u) hpos
  have h3 := rpow_mul_rpow_neg_lt_one hN2 (half_lt_self hε)
  have h4 : (size l : ℝ) ^ (ε / 2) * (size l : ℝ) ^ (-ε) * a l u < a l u := by
    have := ha l u
    nlinarith
  linarith

end Unif

end UnifSection

/-! ### The continuity argument (bootstrap) -/

section Bootstrap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- **The continuity argument (bootstrap).**  Let `M(u)` be random, continuous in `u ∈ [s,t]`
with high probability, and `a ≤ b` deterministic, `a` continuous.  If the forbidden region
`[a(u), b(u)]` is avoided for all `u` simultaneously (w.h.p.) and `M(s) < a(s)` (w.h.p.), then
`M(u) < a(u)` for all `u ∈ [s,t]` (w.h.p.).  It is a statement about events only, so there
is no per-time / uniform split. -/
theorem stepOneBootstrap (hsize : Tendsto size atTop atTop)
    {M : ∀ _ : ℕ, ℝ → Ω → ℝ} {a b : ∀ _ : ℕ, ℝ → ℝ} {s t : ℕ → ℝ}
    (hcont : HighProbAt P size
      (fun l => {ω | ContinuousOn (fun u => M l u ω) (Set.Icc (s l) (t l))}))
    (ha : ∀ l, ContinuousOn (a l) (Set.Icc (s l) (t l)))
    (hab : ∀ᶠ l : ℕ in atTop, ∀ u : TimeIcc s t l, a l u ≤ b l u)
    (hforb : HighProbAt P size
      (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u ∨ b l u < M l u ω}))
    (hinit : HighProbAt P size (fun l => {ω | M l (s l) ω < a l (s l)})) :
    HighProbAt P size (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u}) := by
  refine perTimeCalc_highProbAt_mono
    (perTimeCalc_highProbAt_inter hsize (perTimeCalc_highProbAt_inter hsize hcont hforb) hinit) ?_
  filter_upwards [hab] with l hab
  rintro ω ⟨⟨hc, hf⟩, hi⟩
  simp only [Set.mem_ofPred_eq] at hc hf hi ⊢
  intro u
  refine lt_of_forall_ne_of_continuousOn hc (ha l) hi (fun v hv => ?_) u u.2
  rcases hf ⟨v, hv⟩ with h | h
  · exact h.ne
  · have := hab ⟨v, hv⟩
    simp only at h this
    exact (lt_of_le_of_lt this h).ne'

end Bootstrap

end RBM.Ind.PerTimeCalc
