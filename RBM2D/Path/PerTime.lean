/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Domination

/-!
# The per-time domination interface `PerTimeDomAt`

The definitions `TimeIcc`, `PerTimeDomAt` and `PerTimeOfStochDomAt`.

`PerTimeDomAt` is Definition 2.1(i) of arXiv:2503.07606 (`stoch_domination`) along the admissible
dimensions `size l`, with the union over the parameter `u` taken **outside** the probability
(in the paper's statement the union is inside).

Results:
1. `perTimeOfStochDomAt`: the uniform form `RBM.StochDomAt` implies the per-time form;
2. `perTimeDomAt_iff_forall_section`: the per-time form is equivalent to `StochDomAt` along
   every section `u : ∀ l, U l` (for nonempty `U l`);
3. `stochDomAt_of_perTimeDomAt`: grid union bound, uniform form (`#U l ≤ size(l)^C`);
4. `highProbAt_iInter`: grid union bound, event form.

None of these needs `1 ≤ size l`: the exponent identity `x^C x^{-(D+C)} = x^{-D}` holds for
every `x ≥ 0` when `D ≠ 0` (`Real.rpow_add'`).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-- The times `u ∈ [s_n, t_n]`. -/
abbrev TimeIcc (s t : ℕ → ℝ) (n : ℕ) : Type := ↥(Set.Icc (s n) (t n))

/-- **Per-time stochastic domination** along the admissible dimensions `size l`: for every
`τ, D > 0`, eventually in `l`, **for every** parameter `u`, the failure probability at `u` is at
most `size(l)^{-D}`.  The union over `u` is *outside* the probability, so the statement depends
only on the one-parameter marginals and transfers between couplings with the same marginals
(`Hflow` and the grid walk).  Compare `RBM.StochDomAt`, where the
union is inside. -/
def PerTimeDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ)
    {U : ℕ → Type*} (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u : U l,
    P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

/-- **Uniform ⇒ per time**: `StochDomAt` implies `PerTimeDomAt` (each event is contained
in the union). -/
def PerTimeOfStochDomAt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type}
    (ξ ζ : ∀ l, U l → Ω → ℝ), StochDomAt P size ξ ζ → PerTimeDomAt P size ξ ζ

/-- Each per-time event is contained in `badSetAt`. -/
theorem perTimeOfStochDomAt : PerTimeOfStochDomAt := by
  intro Ω _ P size U ξ ζ h τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) hl
  intro ω hω
  exact ⟨u, hω⟩

/-- `x^C · x^{-(D+C)} = x^{-D}` for every `x ≥ 0` and `D ≠ 0` (no `1 ≤ x` needed). -/
private theorem rpow_mul_rpow_neg_add_of_nonneg {x : ℝ} (hx : 0 ≤ x) (C D : ℝ) (hD : D ≠ 0) :
    x ^ C * x ^ (-(D + C)) = x ^ (-D) := by
  rw [← Real.rpow_add' hx (by rw [show C + -(D + C) = -D by ring]; exact neg_ne_zero.mpr hD)]
  congr 1; ring

/-- **Per-sequence equivalence.** For nonempty parameter sets, the per-time bound
holds iff `StochDomAt` holds along every section `u : ∀ l, U l` (one-parameter `Unit` family).
The "⇐" direction picks, at each `l`, a bad parameter when one exists (classical choice); no
measurability is used. -/
theorem perTimeDomAt_iff_forall_section {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} (hU : ∀ l, Nonempty (U l)) (ξ ζ : ∀ l, U l → Ω → ℝ) :
    PerTimeDomAt P size ξ ζ ↔
      ∀ u : ∀ l, U l,
        StochDomAt P size (fun l (_ : Unit) ω => ξ l (u l) ω)
          (fun l (_ : Unit) ω => ζ l (u l) ω) := by
  constructor
  · intro h u τ hτ D hD
    filter_upwards [h τ hτ D hD] with l hl
    refine le_trans (measure_mono ?_) (hl (u l))
    rintro ω ⟨_, hω⟩
    exact hω
  · intro h τ hτ D hD
    by_contra hne
    rw [Filter.not_eventually] at hne
    classical
    let bad : ∀ l, U l → Prop := fun l v =>
      ENNReal.ofReal ((size l : ℝ) ^ (-D)) < P {ω | (size l : ℝ) ^ τ * ζ l v ω < ξ l v ω}
    let u : ∀ l, U l := fun l =>
      if hb : ∃ v, bad l v then hb.choose else Classical.choice (hU l)
    have hfreq : ∃ᶠ l in atTop, ∃ v, bad l v := by
      refine hne.mono fun l hl => ?_
      push Not at hl
      exact hl
    obtain ⟨l, ⟨v, hv⟩, hl⟩ := (hfreq.and_eventually (h u τ hτ D hD)).exists
    have hb : ∃ v, bad l v := ⟨v, hv⟩
    have hul : bad l (u l) := by
      simp only [u, hb, dite_true]
      exact hb.choose_spec
    refine absurd hl (not_le.mpr (lt_of_lt_of_le hul (measure_mono ?_)))
    intro ω hω
    exact ⟨(), hω⟩

/-- **Grid union bound, uniform form.** If `#U(l) ≤ size(l)^C` eventually, the
per-time bound implies the uniform bound `StochDomAt` (the union moves inside `P`). -/
theorem stochDomAt_of_perTimeDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} [∀ l, Fintype (U l)] {ξ ζ : ∀ l, U l → Ω → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : PerTimeDomAt P size ξ ζ) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hC, h τ hτ (D + C) (by linarith)] with l hcard hl
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  have hset : badSetAt size ξ ζ τ l =
      ⋃ u, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} := by
    ext ω; simp [badSetAt]
  calc P (badSetAt size ξ ζ τ l)
      = P (⋃ u, {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}) := by rw [hset]
    _ ≤ ∑ u, P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} := measure_iUnion_fintype_le P _
    _ ≤ ∑ _u : U l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun u _ => hl u
    _ = ENNReal.ofReal (Fintype.card (U l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [rpow_mul_rpow_neg_add_of_nonneg hs C D hD.ne']

/-- **Grid union bound, event form.**  Polynomially many (in `size l`) events that each hold
with high probability, uniformly in `k`, hold simultaneously with high probability. -/
theorem highProbAt_iInter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ)
    {K : ℕ → Type*} [∀ l, Fintype (K l)] {Ξ : ∀ l, K l → Set Ω} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (K l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ k,
      P (Ξ l k)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))) :
    HighProbAt P size (fun l => ⋂ k, Ξ l k) := by
  intro D hD
  filter_upwards [hC, h (D + C) (by linarith)] with l hcard hl
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  calc P (⋂ k, Ξ l k)ᶜ = P (⋃ k, (Ξ l k)ᶜ) := by rw [Set.compl_iInter]
    _ ≤ ∑ k, P (Ξ l k)ᶜ := measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : K l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun k _ => hl k
    _ = ENNReal.ofReal (Fintype.card (K l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [rpow_mul_rpow_neg_add_of_nonneg hs C D hD.ne']

end RBM.Path
