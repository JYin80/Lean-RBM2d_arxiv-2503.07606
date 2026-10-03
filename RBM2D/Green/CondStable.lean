/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.CondDom
import RBM2D.Induction.PerTimeCalc

/-!
# `≺` under `E_k` and the minor replacement (4.9), at a fixed time

The paper (arXiv:2503.07606) does not state these as lemmas: it says that the estimates on `G_t`
"follow that of Lemma 4.2 in [YY_25], which is dimension-independent"
(Section "Estimates for entries of `G`").
The minor formula `G^{(i)}_{kl} = G_{kl} - G_{ki} G_{il} / G_{ii}` is the (4.9) of [YY_25], cited as
(4.9) in `RBM2D/Green/EntryCore.lean` (where `greenMinor` is its right-hand side) and identified
with the minor resolvent `greenMinorMat` by `greenMinorMat_eq_minorGreen`
(`RBM2D/Green/CondRow.lean`); the word "minor" does not occur in the TeX of the paper.

## Contents

* `perTimeDomAt_condRow_of_envelope` -- **`≺` under `E_k`**: `‖X‖ ≺ ζ`, a deterministic envelope
  of polynomial growth (`Env n ≤ size^{Kenv}`), `E_k[ζ] ≺ χ` and `size^{-B} ≺ χ` give
  `‖E_k[X]‖ ≺ χ`.  The exceptional set of `‖X‖ ≺ ζ` at `(τ/3, D₁)`, `D₁ = Kenv + B + D + 2`, is
  turned into a small set of fixed configurations by the row-slice Markov inequality
  (`meas_measure_rowSlice_ge`), and the bad part of the row integral is at most the envelope times
  the probability of the slice (`norm_condRow_le_split`).
* `perTimeDomAt_condRow_sub_self` -- `‖E_k[X] - X‖ ≺ χ` from a row-`k`-independent surrogate `X'`
  with `‖X - X'‖ ≺ ζ`: the shape of the minor replacement.
* `norm_greenDiagCentered_sub_minor_le` -- (4.9) pointwise on the good event `Ω(t,c)`:
  `|(G_{kk} - m) - (G^{(i)}_{kk} - m)| ≤ 2 |G_{ki}| |G_{ik}|`, since `|G_{ii}| ≥ 1/2` there.
* `perTimeDomAt_const`, `perTimeDomAt_of_le_left_on`, `perTimeDomAt_of_highProb` -- three
  combinators for `PerTimeDomAt` (a deterministic inequality as a `≺`; monotonicity of the left
  side on a high-probability event; a deterministic bound on a high-probability event).

## The per-time form

The statements are `PerTimeDomAt (Sizes.seqP d) d.size ξ ζ` at the time `t n`: every power of `N`
is the same power of `size n`.  The divergence of the sizes is the hypothesis
`hsize : Tendsto d.size atTop atTop` in the two `condRow` statements (as for the
`perTimeCalc_*` lemmas); the combinators `perTimeDomAt_const`, `perTimeDomAt_of_le_left_on` need
only `size ≥ 2`, which holds for every `Sizes` (`size = (W L)² ≥ 9`), so they carry no `hsize`;
`perTimeDomAt_of_highProb` needs no property of `size` and is stated for a general `P` and `size`.

This file uses `PerTime.stochDom_of_le_left_eventually`, `perTimeCalc_add` with
`perTimeCalc_mono`, `perTimeCalc_of_imp_union`.  A transitivity lemma for the per-time `≺` is a
private lemma here.

## d = 2

The index is the fine lattice `Idx (d.L n) (d.W n) = Z2 (W L)` on which `condRow`, `Hflow` and
`greenMinorMat` live; the minor `κ`-entry index is the subtype `{a // a ≠ κ}`.  The spectral
quantities are `spectralZ`, `spectralM`; the flow is `Sizes.seqHflow d n u ω`.
`norm_greenDiagCentered_sub_minor_le` is stated for a pair of distinct fine indices
`i k : Idx (d.L n) (d.W n)` with `hik : i ≠ k` (the `OffPair` of `RBM2D/Green/EntryDom.lean`
is a pair of *block* indices).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path RBM.Ind.PerTimeCalc.PerTime
open scoped ENNReal

/-! ### Elementary facts on `size` -/

private theorem CondStable_nine_le_size (d : Sizes) (n : ℕ) : 9 ≤ d.size n := by
  have hL := d.three_le_L n
  have hW := d.W_pos n
  have h3 : 3 ≤ d.W n * d.L n := by nlinarith
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ (d.W n * d.L n) ^ 2 := Nat.pow_le_pow_left h3 2

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `2 ≤ N` (the pointwise form of `eventually_two_mul_rpow_le`). -/
private theorem CondStable_two_mul_rpow_le {N : ℕ} (hN : 2 ≤ N) (D : ℝ) :
    2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 2 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (2 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN2
    _ = _ := mul_one _

/-! ### Combinators for `PerTimeDomAt` -/

/-- **A deterministic eventual inequality is a `≺`.**  `size ≥ 1` holds for every `Sizes`, so
there is no `hsize`. -/
theorem perTimeDomAt_const (d : Sizes) {V : ℕ → Type*} {f g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ d) => f n) (fun n _ _ => g n) := by
  intro τ hτ D hD
  filter_upwards [hfg] with n hn a
  have hs : (1 : ℝ) ≤ (d.size n : ℝ) := by
    have := CondStable_nine_le_size d n
    exact_mod_cast (by omega : 1 ≤ d.size n)
  have h1 : (1 : ℝ) ≤ (d.size n : ℝ) ^ τ := Real.one_le_rpow hs hτ.le
  have hsub : {ω : Sizes.SeqΩ d | (d.size n : ℝ) ^ τ * g n < f n} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hg n]
  rw [hsub, measure_empty]
  exact zero_le

/-- **Monotonicity in the dominated quantity, on a high-probability event** (with `HighProbAt`
and the one time).  The event costs one more `size^{-(D+1)}`, and
`2 size^{-(D+1)} ≤ size^{-D}` holds since `size ≥ 2`. -/
theorem perTimeDomAt_of_le_left_on {d : Sizes} {V : ℕ → Type*}
    {ξ ξ' ζ : ∀ n, V n → Sizes.SeqΩ d → ℝ} {Ξ : ℕ → Set (Sizes.SeqΩ d)}
    (hΞ : HighProbAt (Sizes.seqP d) d.size Ξ)
    (hle : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ a : V n, ξ' n a ω ≤ ξ n a ω)
    (h : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ' ζ := by
  intro τ hτ D hD
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h τ hτ (D + 1) hD1, hΞ (D + 1) hD1, hle] with n hN hΞN hleN a
  have hp : (0 : ℝ) ≤ (d.size n : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : {ω | (d.size n : ℝ) ^ τ * ζ n a ω < ξ' n a ω}
      ⊆ {ω | (d.size n : ℝ) ^ τ * ζ n a ω < ξ n a ω} ∪ (Ξ n)ᶜ := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hmem : ω ∈ Ξ n
    · exact Or.inl (lt_of_lt_of_le hω (hleN ω hmem a))
    · exact Or.inr hmem
  calc (Sizes.seqP d) {ω | (d.size n : ℝ) ^ τ * ζ n a ω < ξ' n a ω}
      ≤ (Sizes.seqP d) ({ω | (d.size n : ℝ) ^ τ * ζ n a ω < ξ n a ω} ∪ (Ξ n)ᶜ) :=
        measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 1)))
          + ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 1))) :=
        add_le_add (hN a) hΞN
    _ = ENNReal.ofReal (2 * (d.size n : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal
          (CondStable_two_mul_rpow_le (by have := CondStable_nine_le_size d n; omega) D)

/-- **A deterministic bound on a high-probability event gives a `≺`** (with `HighProbAt`).  No
condition on `size` is needed. -/
theorem perTimeDomAt_of_highProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (hΞ : HighProbAt P size Ξ)
    (hle : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ ω ∈ Ξ l, ∀ a : U l,
      ξ l a ω ≤ (size l : ℝ) ^ τ * ζ l a ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hΞ D hD, hle τ hτ] with l hΞl hlel a
  refine le_trans (measure_mono ?_) hΞl
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  exact fun hmem => absurd (hlel ω hmem a) (not_le.2 hω)

/-- **`≺` is transitive**, from `perTimeCalc_of_imp_union` with the `τ/2` split.  Private: it is
used only by `perTimeDomAt_condRow_sub_self`. -/
private theorem CondStable_trans {d : Sizes} (hsize : Tendsto d.size atTop atTop)
    {V : ℕ → Type*} {ξ ζ χ : ∀ n, V n → Sizes.SeqΩ d → ℝ}
    (h₁ : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) (h₂ : PerTimeDomAt (Sizes.seqP d) d.size ζ χ) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ χ := by
  refine perTimeCalc_of_imp_union hsize h₁ h₂ (fun τ hτ => ⟨τ / 2, half_pos hτ,
    Eventually.of_forall fun n u ω hω => ?_⟩)
  by_contra hno
  simp only [not_or, not_lt] at hno
  have hpos : (0 : ℝ) ≤ (d.size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcalc : ξ n u ω ≤ (d.size n : ℝ) ^ τ * χ n u ω :=
    calc ξ n u ω ≤ (d.size n : ℝ) ^ (τ / 2) * ζ n u ω := hno.1
      _ ≤ (d.size n : ℝ) ^ (τ / 2) * ((d.size n : ℝ) ^ (τ / 2) * χ n u ω) :=
          mul_le_mul_of_nonneg_left hno.2 hpos
      _ = (d.size n : ℝ) ^ τ * χ n u ω := by
          rw [← mul_assoc, RBM.UnifDetDom.rpow_half_mul_rpow_half (d.size n) hτ]
  exact absurd hω (not_lt.2 hcalc)

/-! ### `≺` under `E_k`, at a fixed time -/

/-- **`≺` under `E_k`, per time**, with no cardinality hypothesis on the index family `V`.

The exceptional set of `hdom` at `(τ/3, D₁)` with `D₁ = Kenv + B + D + 2` is `S`; the row-slice
Markov inequality makes `{ω : P(slice_ω) ≥ size^{-(Kenv+B)}}` have probability at most
`size^{-(D+2)}`.  Off this set and off the exceptional sets (at `(τ/3, D+2)`) of `hstab` and
`hlow`, `norm_condRow_le_split` gives
`‖E_k[X]‖ ≤ size^{τ/3} E_k[ζ] + Env · P(slice) ≤ size^{2τ/3} χ + size^{-B}`, and
`size^{-B} ≤ size^{τ/3} χ ≤ size^{2τ/3} χ`, so `‖E_k[X]‖ ≤ 2 size^{2τ/3} χ ≤ size^τ χ` when
`2 ≤ size^{τ/3}` (eventually, by `hsize`).  The three exceptional probabilities are at most
`size^{-(D+2)}` each, and `3 size^{-(D+2)} ≤ size^{-D}` eventually.

The deterministic envelope `Env n` may grow polynomially: `Kenv` is free and is absorbed into
the exponent `D₁`.  `hsize` is the divergence of the sizes. -/
theorem perTimeDomAt_condRow_of_envelope {d : Sizes} (hsize : Tendsto d.size atTop atTop)
    {V : ℕ → Type*} {X : ∀ n, V n → Sizes.SeqΩ d → ℂ}
    {ζ χ : ∀ n, V n → Sizes.SeqΩ d → ℝ} {k : ∀ n, V n → Idx (d.L n) (d.W n)}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (n : ℕ) (a : V n), Measurable (X n a))
    (hζmeas : ∀ (n : ℕ) (a : V n), Measurable (ζ n a))
    (hζ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), 0 ≤ ζ n a ω)
    (hχ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), 0 ≤ χ n a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), ‖X n a ω‖ ≤ Env n)
    (hEnvpoly : ∀ᶠ n : ℕ in atTop, Env n ≤ (d.size n : ℝ) ^ Kenv)
    (hrowint : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d),
      Integrable (fun ω' => ζ n a (rowSplit d n (k n a) ω ω')) (Sizes.seqP d))
    (hlow : PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ d) => (d.size n : ℝ) ^ (-B)) χ)
    (hstab : PerTimeDomAt (Sizes.seqP d) d.size
      (fun n a ω => condRowReal d n (k n a) (ζ n a) ω) χ)
    (hdom : PerTimeDomAt (Sizes.seqP d) d.size (fun n a ω => ‖X n a ω‖) ζ) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n a ω => ‖condRow d n (k n a) (X n a) ω‖) χ := by
  intro τ hτ D hD
  have hτ3 : 0 < τ / 3 := by linarith
  set M : ℝ := Kenv + B with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  set D₁ : ℝ := M + D + 2 with hD₁def
  have hD₁0 : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hEnvpoly, hdom (τ / 3) hτ3 D₁ hD₁0, hstab (τ / 3) hτ3 (D + 2) (by linarith),
    hlow (τ / 3) hτ3 (D + 2) (by linarith), hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow 2 hτ3),
    hsize.eventually (eventually_two_mul_rpow_le (D + 1)),
    hsize.eventually (eventually_two_mul_rpow_le D)] with
    n hEnvN hbadN hstabN hlowN hN1 h2N hdbl1 hdbl2 a
  have hNpos : (0 : ℝ) < d.size n := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (d.size n : ℝ) := by exact_mod_cast hN1
  set S : Set (Sizes.SeqΩ d) := {σ | (d.size n : ℝ) ^ (τ / 3) * ζ n a σ < ‖X n a σ‖} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt (measurable_const.mul (hζmeas n a)) ((hXmeas n a).norm)
  have hSsmall : (Sizes.seqP d) S ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-D₁)) := hbadN a
  set ε : ℝ≥0∞ := ENNReal.ofReal ((d.size n : ℝ) ^ (-M)) with hεdef
  have hεpos : (0 : ℝ) < (d.size n : ℝ) ^ (-M) := Real.rpow_pos_of_pos hNpos _
  have hε0 : ε ≠ 0 := by
    rw [hεdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hεpos
  set A1 : Set (Sizes.SeqΩ d) := {ω | ε ≤ (Sizes.seqP d) (rowSlice d n (k n a) S ω)} with hA1def
  set A2 : Set (Sizes.SeqΩ d) :=
    {ω | (d.size n : ℝ) ^ (τ / 3) * χ n a ω < condRowReal d n (k n a) (ζ n a) ω} with hA2def
  set A3 : Set (Sizes.SeqΩ d) := {ω | (d.size n : ℝ) ^ (τ / 3) * χ n a ω < (d.size n : ℝ) ^ (-B)} with hA3def
  have hA1small : (Sizes.seqP d) A1 ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 2))) := by
    have h2 : ε * (Sizes.seqP d) A1 ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-D₁)) :=
      (meas_measure_rowSlice_ge d n (k n a) hSmeas ε).trans hSsmall
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.ofReal_ne_top)] at h2
    refine h2.trans (le_of_eq ?_)
    have hexp : -D₁ - -M = -(D + 2) := by rw [hD₁def, hMdef]; ring
    rw [hεdef, ← ENNReal.ofReal_div_of_pos hεpos, ← Real.rpow_sub hNpos, hexp]
  have hsub : {ω | (d.size n : ℝ) ^ τ * χ n a ω < ‖condRow d n (k n a) (X n a) ω‖}
      ⊆ A1 ∪ A2 ∪ A3 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [hA1def] at h1
    simp only [Set.mem_ofPred_eq, not_le] at h1
    rw [hA2def] at h2
    simp only [Set.mem_ofPred_eq, not_lt] at h2
    rw [hA3def] at h3
    simp only [Set.mem_ofPred_eq, not_lt] at h3
    have hgood : ∀ σ : Sizes.SeqΩ d, σ ∉ S → ‖X n a σ‖ ≤ (d.size n : ℝ) ^ (τ / 3) * ζ n a σ := by
      intro σ hσ
      rw [hSdef] at hσ
      simpa only [Set.mem_ofPred_eq, not_lt] using hσ
    have hsplit := norm_condRow_le_split (hXmeas n a) (hζ0 n a) (hrowint n a)
      (henv n a) (Real.rpow_nonneg hNpos.le _) hSmeas hgood ω
    have hr1 : (Sizes.seqP d).real (rowSlice d n (k n a) S ω) ≤ (d.size n : ℝ) ^ (-M) :=
      ENNReal.toReal_le_of_le_ofReal hεpos.le h1.le
    have hr0 : (0 : ℝ) ≤ (Sizes.seqP d).real (rowSlice d n (k n a) S ω) := measureReal_nonneg
    have hEnvterm : Env n * (Sizes.seqP d).real (rowSlice d n (k n a) S ω) ≤ (d.size n : ℝ) ^ (-B) := by
      have hstep : Env n * (Sizes.seqP d).real (rowSlice d n (k n a) S ω)
          ≤ (d.size n : ℝ) ^ Kenv * (d.size n : ℝ) ^ (-M) :=
        mul_le_mul hEnvN hr1 hr0 (Real.rpow_nonneg hNpos.le _)
      refine hstep.trans (le_of_eq ?_)
      rw [← Real.rpow_add hNpos, hMdef]
      congr 1
      ring
    have hχu := hχ0 n a ω
    have hr3 : (0 : ℝ) ≤ (d.size n : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
    have hmono : (d.size n : ℝ) ^ (τ / 3) ≤ (d.size n : ℝ) ^ (2 * τ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hprod : (d.size n : ℝ) ^ (τ / 3) * (d.size n : ℝ) ^ (τ / 3) = (d.size n : ℝ) ^ (2 * τ / 3) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hfin : (d.size n : ℝ) ^ (τ / 3) * (d.size n : ℝ) ^ (2 * τ / 3) = (d.size n : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hchain : ‖condRow d n (k n a) (X n a) ω‖ ≤ (d.size n : ℝ) ^ τ * χ n a ω := by
      have e1 : (d.size n : ℝ) ^ (τ / 3) * condRowReal d n (k n a) (ζ n a) ω
          ≤ (d.size n : ℝ) ^ (τ / 3) * ((d.size n : ℝ) ^ (τ / 3) * χ n a ω) :=
        mul_le_mul_of_nonneg_left h2 hr3
      have e3 : (d.size n : ℝ) ^ (τ / 3) * χ n a ω ≤ (d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω :=
        mul_le_mul_of_nonneg_right hmono hχu
      have e4 : (d.size n : ℝ) ^ (τ / 3) * ((d.size n : ℝ) ^ (τ / 3) * χ n a ω)
          = (d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω := by rw [← mul_assoc, hprod]
      have e5 : (2 : ℝ) * ((d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω) ≤ (d.size n : ℝ) ^ τ * χ n a ω := by
        have hnn : (0 : ℝ) ≤ (d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω :=
          mul_nonneg (Real.rpow_nonneg hNpos.le _) hχu
        calc (2 : ℝ) * ((d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω)
            ≤ (d.size n : ℝ) ^ (τ / 3) * ((d.size n : ℝ) ^ (2 * τ / 3) * χ n a ω) :=
              mul_le_mul_of_nonneg_right h2N hnn
          _ = ((d.size n : ℝ) ^ (τ / 3) * (d.size n : ℝ) ^ (2 * τ / 3)) * χ n a ω := (mul_assoc _ _ _).symm
          _ = (d.size n : ℝ) ^ τ * χ n a ω := by rw [hfin]
      linarith
    exact absurd hchain (not_le.2 hω)
  have hnn : (0 : ℝ) ≤ (d.size n : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
  refine (measure_mono hsub).trans ?_
  calc (Sizes.seqP d) (A1 ∪ A2 ∪ A3) ≤ (Sizes.seqP d) (A1 ∪ A2) + (Sizes.seqP d) A3 := measure_union_le _ _
    _ ≤ ((Sizes.seqP d) A1 + (Sizes.seqP d) A2) + (Sizes.seqP d) A3 := by gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 2))))
        + ENNReal.ofReal ((d.size n : ℝ) ^ (-(D + 2))) :=
          add_le_add (add_le_add hA1small (hstabN a)) (hlowN a)
    _ = ENNReal.ofReal (3 * (d.size n : ℝ) ^ (-(D + 2))) := by
        rw [show (3 : ℝ) * (d.size n : ℝ) ^ (-(D + 2))
            = (d.size n : ℝ) ^ (-(D + 2)) + (d.size n : ℝ) ^ (-(D + 2)) + (d.size n : ℝ) ^ (-(D + 2)) by ring,
          ENNReal.ofReal_add (by positivity) hnn, ENNReal.ofReal_add hnn hnn]
    _ ≤ ENNReal.ofReal ((d.size n : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : 2 * (d.size n : ℝ) ^ (-(D + 1 + 1)) ≤ (d.size n : ℝ) ^ (-(D + 1)) := hdbl1
        have e2 : 2 * (d.size n : ℝ) ^ (-(D + 1)) ≤ (d.size n : ℝ) ^ (-D) := hdbl2
        have e3 : (d.size n : ℝ) ^ (-(D + 1 + 1)) = (d.size n : ℝ) ^ (-(D + 2)) := by congr 1; ring
        rw [e3] at e1
        linarith

/-! ### `E_k[X] - X` through a row-free surrogate, at a fixed time -/

/-- The `PerTimeDomAt` form of `E_k[X] - X ≺ χ` through a row-free surrogate.  The
calculus gives `perTimeCalc_add` then `perTimeCalc_mono` (with `χ + χ ≤ 2 χ`) for the
sum, and `PerTime.stochDom_of_le_left_eventually` for monotonicity; transitivity is the private
`CondStable_trans`. -/
theorem perTimeDomAt_condRow_sub_self {d : Sizes} (hsize : Tendsto d.size atTop atTop)
    {V : ℕ → Type*} {X X' : ∀ n, V n → Sizes.SeqΩ d → ℂ}
    {ζ χ : ∀ n, V n → Sizes.SeqΩ d → ℝ} {k : ∀ n, V n → Idx (d.L n) (d.W n)}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (n : ℕ) (a : V n), Measurable (X n a))
    (hX'meas : ∀ (n : ℕ) (a : V n), Measurable (X' n a))
    (hζmeas : ∀ (n : ℕ) (a : V n), Measurable (ζ n a))
    (hζ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), 0 ≤ ζ n a ω)
    (hχ0 : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), 0 ≤ χ n a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d), ‖X n a ω - X' n a ω‖ ≤ Env n)
    (hEnvpoly : ∀ᶠ n : ℕ in atTop, Env n ≤ (d.size n : ℝ) ^ Kenv)
    (hrowint : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d),
      Integrable (fun ω' => ζ n a (rowSplit d n (k n a) ω ω')) (Sizes.seqP d))
    (hlow : PerTimeDomAt (Sizes.seqP d) d.size
      (fun n (_ : V n) (_ : Sizes.SeqΩ d) => (d.size n : ℝ) ^ (-B)) χ)
    (hstab : PerTimeDomAt (Sizes.seqP d) d.size
      (fun n a ω => condRowReal d n (k n a) (ζ n a) ω) χ)
    (hζχ : PerTimeDomAt (Sizes.seqP d) d.size ζ χ)
    (hfd : ∀ (n : ℕ) (a : V n), FinDepOffRow d n (k n a) (X' n a))
    (hXint : ∀ (n : ℕ) (a : V n), RowIntegrable d n (k n a) (X n a))
    (hdiff : PerTimeDomAt (Sizes.seqP d) d.size (fun n a ω => ‖X n a ω - X' n a ω‖) ζ) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (fun n a ω => ‖condRow d n (k n a) (X n a) ω - X n a ω‖) χ := by
  have hX'int : ∀ (n : ℕ) (a : V n), RowIntegrable d n (k n a) (X' n a) := by
    intro n a ω
    have h : (fun ω' => X' n a (rowSplit d n (k n a) ω ω')) = fun _ => X' n a ω := by
      funext ω'; exact (hfd n a).rowSplit_eq ω ω'
    rw [h]; exact integrable_const _
  have hbound : ∀ (n : ℕ) (a : V n) (ω : Sizes.SeqΩ d),
      ‖condRow d n (k n a) (X n a) ω - X n a ω‖
        ≤ ‖condRow d n (k n a) (fun η => X n a η - X' n a η) ω‖
          + ‖X n a ω - X' n a ω‖ := by
    intro n a ω
    have e1 := congrFun (condRow_sub (k n a) (hXint n a) (hX'int n a)) ω
    have e2 := congrFun (condRow_of_finDepOffRow (hfd n a)) ω
    have hid : condRow d n (k n a) (X n a) ω - X n a ω
        = condRow d n (k n a) (fun η => X n a η - X' n a η) ω
          - (X n a ω - X' n a ω) := by
      rw [e1, e2]; ring
    rw [hid]
    exact norm_sub_le _ _
  have htool : PerTimeDomAt (Sizes.seqP d) d.size
      (fun n a ω => ‖condRow d n (k n a) (fun η => X n a η - X' n a η) ω‖) χ :=
    perTimeDomAt_condRow_of_envelope hsize
      (fun n a => (hXmeas n a).sub (hX'meas n a)) hζmeas hζ0 hχ0 hKenv hB henv hEnvpoly
      hrowint hlow hstab hdiff
  have hsum := perTimeCalc_add hsize htool (CondStable_trans hsize hdiff hζχ)
  have hsum2 := perTimeCalc_mono hsize hχ0 2
    (Eventually.of_forall fun n a ω => by linarith) hsum
  exact stochDom_of_le_left_eventually (Eventually.of_forall fun n a ω => hbound n a ω) hsum2

/-! ### The minor replacement (4.9) on the good event -/

/-- **(4.9) pointwise, on the good event**.  The replacement error is
`|G_{kk} - G^{(i)}_{kk}| = |G_{ki} G_{ik} / G_{ii}| ≤ 2 |G_{ki}| |G_{ik}|`, since `|G_{ii}| ≥ 1/2`
on the good event (`δ' ≤ 1/2`).  The identification of `greenMinorMat` with the explicit formula
needs no event: `H_u` is Hermitian and `Im z_u ≠ 0`.  The pair of distinct indices is passed as
`i k : Idx (d.L n) (d.W n)` with `hik : i ≠ k`; see the module docstring. -/
theorem norm_greenDiagCentered_sub_minor_le (d : Sizes) (n : ℕ) {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) {δ' : ℝ} (hδ' : δ' ≤ 1 / 2) {ω : Sizes.SeqΩ d}
    (hω : GoodEvent (green (Sizes.seqHflow d n u ω) (spectralZ E u)) (spectralM E) δ')
    (i k : Idx (d.L n) (d.W n)) (hik : i ≠ k) :
    ‖greenDiagCentered d n u (spectralZ E u) (spectralM E) k ω
        - greenMinorDiagCentered d n u (spectralZ E u) (spectralM E) i ⟨k, Ne.symm hik⟩ ω‖
      ≤ 2 * (‖green (Sizes.seqHflow d n u ω) (spectralZ E u) k i‖
          * ‖green (Sizes.seqHflow d n u ω) (spectralZ E u) i k‖) := by
  have hzt : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (etaT_pos hE hu1).ne'
  have hid : greenDiagCentered d n u (spectralZ E u) (spectralM E) k ω
      - greenMinorDiagCentered d n u (spectralZ E u) (spectralM E) i ⟨k, Ne.symm hik⟩ ω
      = -(greenMinor (green (Sizes.seqHflow d n u ω) (spectralZ E u)) i k k
          - green (Sizes.seqHflow d n u ω) (spectralZ E u) k k) := by
    simp only [greenDiagCentered, greenMinorDiagCentered]
    rw [greenMinorMat_eq_minorGreen d n u (spectralZ E u) i ω
      (isUnit_det_Hflow_sub d n u ω hzt) (green_Hflow_diag_ne_zero d n u ω hzt i),
      minorGreen_eq_greenMinor]
    ring
  rw [hid, norm_neg]
  exact hω.norm_greenMinor_sub_le (norm_spectralM hE.le) hδ' i k k

end RBM.Green
