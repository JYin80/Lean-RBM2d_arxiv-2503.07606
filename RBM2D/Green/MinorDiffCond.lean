/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.MinorDiff
import RBM2D.Green.CondDom
import RBM2D.Path.Step2Props

/-!
# Conditionalizing the minor-difference gain on the good event

The paper (arXiv:2503.07606) has the event `Ω(t, c) = {‖G_t - m‖_max ≤ W^{-c}}` (`def_asGMc`, in
`lem_GbEXP`) and states the entry estimates on it with
the indicator `1_Ω` and the relation `≺`; the proofs are deferred to Lemma 4.2 of [YY_25], "which is
dimension-independent".  The equation
numbers `(4.1)`-`(4.3)`, `(4.9)`, `(4.12)` in this file are those of [YY_25], as in
`RBM2D/Green/MinorGoodLe.lean` (`(4.1)` is the event `Ω`).  This file passes
from the event `Ω` to the moment bound that the `2p`-th moment expansion
consumes; it has no counterpart in the TeX.

## Why an indicator does not work, and what does

`flucDiagSet` **is** `qRow k (…)`, i.e. a conditional expectation, and `applyOps` stacks further
`E_κ` on top of it.  Multiplying the integrand by `1_Ω` therefore does not commute past the
operators and splitting the integral naively is illegitimate.  The legitimate tool is
`RBM.Green.norm_condRow_le_split` (`RBM2D/Green/CondDom.lean`): off the exceptional set the
integrand obeys the sharp bound, on the whole space the deterministic envelope, and `E_κ` splits
into the two contributions, the second weighted by the probability of the **row section** of the
exceptional set.

## The tower, and why a single exceptional set is not enough

A hypothesis `∀ κ ω, P(rowSlice κ Bad ω) ≤ ε` for a single `Bad` is a `∀ ω` statement, and for
the good event it is
**false**: conditionally on a catastrophic configuration of the rows other than `κ`, the good event
fails with probability one, so its row section is the whole space (this remark is not used in any
proof below).  What *is* true is the statement one level at a time: `badStep` enlarges a set by the
fixed configurations whose sections are not `ε`-small and `badTower` iterates it.
`BadFamily` is the resulting interface (monotone, measurable, `ε`-small sections of the `j`-th
member off the `(j+1)`-st) and `badFamily_badTower` **produces** it for any measurable base.
`meas_badTower_le` is the price: one factor `(ε + #rows)/ε` per letter, which is a power of
`size n` against a super-polynomially small base.

## The estimates

* `norm_applyOps_le_badFamily` -- a word of `n` letters applied to a function that is sharp off
  `Bad 0` and enveloped everywhere is sharp off `Bad n`, up to `n · Env · ε`.
* `norm_minorDiff_qList_greenSetDiagCentered_le` -- the sharp size of the word's minor difference at
  **one** sample point (empty word: (4.3); non-empty word: the `Δ_κ` calculus of `MinorDiff.lean`).
* `norm_applyOps_minorDiff_flucDiagSet_le_badFamily` -- the two combined.
* `integral_prod_applyOps_minorDiff_le_on` -- the moment bound, with no `∀ ω` hypothesis: the price
  is `condCost` on the constant and the additive remainder `condEnv ^ #ι · P(Bad_{M+1})`.
* `minorDiffGainUpTo'_of_le_on` -- the remainder is absorbed by the budget `#ι ≤ K`, which gives the
  interface `MinorDiffGainUpTo'` again.
* `minorDiffGainUpTo'_goodEvent`, `flucGainUpTo'_goodEvent` -- the endpoints, from the per-time
  good event `{ω | ∀ i j, llErrMat … i j ≤ δ n}` at the time `t n` alone.

## d = 2

* The objects are `Idx (d.L n) (d.W n)`, `Sizes.SeqΩ d`, `Sizes.seqP d`, `Sizes.seqHflow`,
  `spectralZ`, `spectralM`, `Sizes`, and `n` is the slice; `η_t` is `RBM.Path.etaT`
  (`(spectralZ E t).im = etaT E t` is `spectralZ_im`).  The budget of `MinorDiffGainUpTo'` is
  `K`, the level is `n`.
* **The row count.**  `meas_badStep_le` and `meas_badTower_le` count the rows `κ` of the lattice
  `Idx (d.L n) (d.W n)`, of cardinality `size n = (W L)²` (`flucAvg_card_Idx_eq_size`); the form
  `minorDiffCond_meas_badTower_le_size` is stated with `size n`.  Everything else is dimension-free.
* **The per-time good event**: the event is
  `{ω | ∀ i j, llErrMat … (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n}` at the time `t n`
  (the form of the `hΩ` of `RBM2D/Green/IBPRem.lean`).  `badBase` is the measurable hull of its
  complement.  The bridge to `MinorGoodLe` is `minorGoodLe_of_goodEvent_flow` after the definitional
  identity `llErrMat … i j = ‖G_{ij} - m 1_{i=j}‖` of `GoodEvent (green H z) m δ`.
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Finset RBM.Gauss RBM.Path

open scoped ENNReal

variable {d : Sizes} {n : ℕ}

/-! ### The tower of exceptional sets -/

/-- One step of the tower: enlarge `S` by the fixed configurations whose row-`κ` section of `S` is
not `ε`-small, for some row `κ`. -/
def badStep (d : Sizes) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ d)) : Set (Sizes.SeqΩ d) :=
  S ∪ ⋃ κ : Idx (d.L n) (d.W n), {ω | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)}

theorem subset_badStep (d : Sizes) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ d)) :
    S ⊆ badStep d n ε S :=
  Set.subset_union_left

theorem measurable_measureReal_rowSlice (d : Sizes) (n : ℕ) (κ : Idx (d.L n) (d.W n))
    {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S) :
    Measurable fun ω => (Sizes.seqP d).real (rowSlice d n κ S ω) :=
  (measurable_measure_rowSlice d n κ hS).ennreal_toReal

theorem measurableSet_badStep {ε : ℝ} {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S) :
    MeasurableSet (badStep d n ε S) :=
  hS.union (MeasurableSet.iUnion fun κ =>
    measurableSet_lt measurable_const (measurable_measureReal_rowSlice d n κ hS))

/-- Off `badStep`, every row section of `S` is `ε`-small. -/
theorem measureReal_rowSlice_le_of_notMem_badStep {ε : ℝ} {S : Set (Sizes.SeqΩ d)}
    (κ : Idx (d.L n) (d.W n)) {ω : Sizes.SeqΩ d} (hω : ω ∉ badStep d n ε S) :
    (Sizes.seqP d).real (rowSlice d n κ S ω) ≤ ε := by
  by_contra h
  exact hω (Or.inr (Set.mem_iUnion.2 ⟨κ, not_le.1 h⟩))

/-- **The tower.**  `badTower d n ε S j` is `S` enlarged `j` times. -/
def badTower (d : Sizes) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ d)) : ℕ → Set (Sizes.SeqΩ d)
  | 0 => S
  | j + 1 => badStep d n ε (badTower d n ε S j)

@[simp] theorem badTower_succ (d : Sizes) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ d)) (j : ℕ) :
    badTower d n ε S (j + 1) = badStep d n ε (badTower d n ε S j) := rfl

/-- **The interface the word estimate consumes.**  A monotone measurable family whose `j`-th member
has `ε`-small row sections off the `(j+1)`-st.

This replaces a hypothesis `∀ κ ω, P(rowSlice κ Bad ω) ≤ ε` with a single set `Bad`, which is a
`∀ ω` statement (and false for the good event: see the module docstring).
`badStep` enlarges the set by the fixed configurations where the section is not `ε`-small, once
per letter of the word. -/
structure BadFamily (d : Sizes) (n : ℕ) (ε : ℝ) (Bad : ℕ → Set (Sizes.SeqΩ d)) : Prop where
  /-- Every member is measurable. -/
  meas : ∀ j, MeasurableSet (Bad j)
  /-- The family increases. -/
  mono : ∀ j, Bad j ⊆ Bad (j + 1)
  /-- Off the next member, the row sections of the current one are `ε`-small. -/
  slice : ∀ (j : ℕ) (κ : Idx (d.L n) (d.W n)) {ω : Sizes.SeqΩ d}, ω ∉ Bad (j + 1) →
    (Sizes.seqP d).real (rowSlice d n κ (Bad j) ω) ≤ ε

theorem BadFamily.mono_le {ε : ℝ} {Bad : ℕ → Set (Sizes.SeqΩ d)} (h : BadFamily d n ε Bad) :
    ∀ {j j' : ℕ}, j ≤ j' → Bad j ⊆ Bad j' := by
  intro j j' hjj'
  induction j' with
  | zero => rw [Nat.le_zero.1 hjj']
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (h.mono k)
      · rw [le_antisymm hjj' hge]

/-- **The tower is a `BadFamily`.**  Nothing is assumed about `S` beyond measurability, so the
hypothesis of the word estimate is *produced*, not postulated. -/
theorem badFamily_badTower (d : Sizes) (n : ℕ) (ε : ℝ) {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) : BadFamily d n ε (badTower d n ε S) where
  meas := by
    intro j
    induction j with
    | zero => exact hS
    | succ k ih => exact measurableSet_badStep ih
  mono := fun j => subset_badStep d n ε _
  slice := fun j κ _ hω => measureReal_rowSlice_le_of_notMem_badStep κ hω

/-! ### The measure of the tower -/

/-- **One step costs a factor `1 + #rows / ε`**, by Fubini and Markov for the row section
(`meas_measure_rowSlice_ge`).  Stated multiplicatively to avoid division in `ℝ≥0∞`.  The rows are
the `size n = (W L)²` sites of the lattice (`flucAvg_card_Idx_eq_size`). -/
theorem meas_badStep_le (d : Sizes) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) :
    ENNReal.ofReal ε * (Sizes.seqP d) (badStep d n ε S)
      ≤ (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞)) * (Sizes.seqP d) S := by
  classical
  have hsub : ∀ κ : Idx (d.L n) (d.W n),
      {ω : Sizes.SeqΩ d | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)}
        ⊆ {ω : Sizes.SeqΩ d | ENNReal.ofReal ε ≤ (Sizes.seqP d) (rowSlice d n κ S ω)} := by
    intro κ ω hω
    exact ENNReal.ofReal_le_of_le_toReal hω.le
  have hstep : ∀ κ : Idx (d.L n) (d.W n),
      ENNReal.ofReal ε * (Sizes.seqP d)
        {ω : Sizes.SeqΩ d | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)}
        ≤ (Sizes.seqP d) S := by
    intro κ
    refine le_trans (mul_le_mul_right (measure_mono (hsub κ)) _) ?_
    exact meas_measure_rowSlice_ge d n κ hS (ENNReal.ofReal ε)
  have hunion : (Sizes.seqP d) (badStep d n ε S)
      ≤ (Sizes.seqP d) S + ∑ κ : Idx (d.L n) (d.W n), (Sizes.seqP d)
          {ω : Sizes.SeqΩ d | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)} := by
    refine le_trans (measure_union_le _ _) (add_le_add_right ?_ _)
    exact measure_iUnion_fintype_le _ _
  calc ENNReal.ofReal ε * (Sizes.seqP d) (badStep d n ε S)
      ≤ ENNReal.ofReal ε * ((Sizes.seqP d) S
          + ∑ κ : Idx (d.L n) (d.W n), (Sizes.seqP d)
              {ω : Sizes.SeqΩ d | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)}) :=
        mul_le_mul_right hunion _
    _ = ENNReal.ofReal ε * (Sizes.seqP d) S
          + ∑ κ : Idx (d.L n) (d.W n), ENNReal.ofReal ε * (Sizes.seqP d)
              {ω : Sizes.SeqΩ d | ε < (Sizes.seqP d).real (rowSlice d n κ S ω)} := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ ENNReal.ofReal ε * (Sizes.seqP d) S
          + ∑ _κ : Idx (d.L n) (d.W n), (Sizes.seqP d) S :=
        add_le_add_right (Finset.sum_le_sum fun κ _ => hstep κ) _
    _ = (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞)) * (Sizes.seqP d) S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul]

/-- **The tower's measure**: `ε^j P(Bad_j) ≤ (ε + #rows)^j P(Bad_0)`, with `#rows = size n`.  Since
`P(Bad_0)` is super-polynomially small (it is the complement of (4.1)) while `#rows = size n` and
`ε` is a fixed negative power of `size n`, the whole tower is still super-polynomially small for
every fixed number `j` of letters. -/
theorem meas_badTower_le (d : Sizes) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) (j : ℕ) :
    ENNReal.ofReal ε ^ j * (Sizes.seqP d) (badTower d n ε S j)
      ≤ (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞)) ^ j
          * (Sizes.seqP d) S := by
  induction j with
  | zero => simp [badTower]
  | succ k ih =>
      have hmeas : MeasurableSet (badTower d n ε S k) :=
        (badFamily_badTower d n ε hS).meas k
      calc ENNReal.ofReal ε ^ (k + 1) * (Sizes.seqP d) (badTower d n ε S (k + 1))
          = ENNReal.ofReal ε ^ k * (ENNReal.ofReal ε
              * (Sizes.seqP d) (badStep d n ε (badTower d n ε S k))) := by
            rw [badTower_succ, pow_succ]; ring
        _ ≤ ENNReal.ofReal ε ^ k
              * ((ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞))
                  * (Sizes.seqP d) (badTower d n ε S k)) :=
            mul_le_mul_right (meas_badStep_le d n hmeas) _
        _ = (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞))
              * (ENNReal.ofReal ε ^ k * (Sizes.seqP d) (badTower d n ε S k)) := by ring
        _ ≤ (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞))
              * ((ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞)) ^ k
                  * (Sizes.seqP d) S) :=
            mul_le_mul_right ih _
        _ = (ENNReal.ofReal ε + (Fintype.card (Idx (d.L n) (d.W n)) : ℝ≥0∞)) ^ (k + 1)
              * (Sizes.seqP d) S := by
            rw [pow_succ]; ring

/-- `meas_badTower_le` with the row count written as `size n`. -/
theorem minorDiffCond_meas_badTower_le_size (d : Sizes) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) (j : ℕ) :
    ENNReal.ofReal ε ^ j * (Sizes.seqP d) (badTower d n ε S j)
      ≤ (ENNReal.ofReal ε + (d.size n : ℝ≥0∞)) ^ j * (Sizes.seqP d) S := by
  have h := meas_badTower_le d n (ε := ε) hS j
  rwa [flucAvg_card_Idx_eq_size] at h

/-! ### A word applied to a function that is good off the tower -/

/-- Words concatenate. -/
theorem applyOps_append (d : Sizes) (n : ℕ) (l₁ l₂ : List (Bool × Idx (d.L n) (d.W n)))
    (X : Sizes.SeqΩ d → ℂ) :
    applyOps d n (l₁ ++ l₂) X = applyOps d n l₁ (applyOps d n l₂ X) := by
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [List.cons_append, applyOps_cons_false, ih]
      · simp only [List.cons_append, applyOps_cons_true, ih]

/-- **The conditionalized word estimate.**

If `X` obeys the sharp bound `c` off `Bad 0` and the deterministic envelope `Env` everywhere, then a
word of `l.length` letters obeys the sharp bound off `Bad l.length`, up to the additive loss
`l.length · Env · ε` from the row sections that the conditional expectations integrate over.

Multiplying the integrand by an indicator is *not* available: `flucDiagSet` is itself a `qRow`, and
`applyOps` stacks further `E_κ` on top of it, so an indicator does not commute past the conditional
expectations.  What does pass is `norm_condRow_le_split`: on the good set the integrand obeys the
sharp bound, on the whole space the envelope, and `E_κ` splits accordingly, at the price of one
further enlargement of the exceptional set per letter. -/
theorem norm_applyOps_le_badFamily {X : Sizes.SeqΩ d → ℂ} (hX : BddMeas d X)
    {Bad : ℕ → Set (Sizes.SeqΩ d)} {ε Env c : ℝ} (hfam : BadFamily d n ε Bad)
    (hEnv : ∀ ω, ‖X ω‖ ≤ Env) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hgood : ∀ ω ∉ Bad 0, ‖X ω‖ ≤ c) :
    ∀ (l : List (Bool × Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d), ω ∉ Bad l.length →
      ‖applyOps d n l X ω‖ ≤ 2 ^ numQ l * (c + l.length * Env * ε) := by
  have hEnv0 : 0 ≤ Env := le_trans (norm_nonneg _) (hEnv 0)
  intro l
  induction l with
  | nil => intro ω hω; simpa [applyOps, numQ] using hgood ω hω
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      intro ω hω
      have hωl : ω ∉ Bad l.length := fun h => hω (hfam.mono l.length h)
      set A : ℝ := 2 ^ numQ l * (c + l.length * Env * ε) with hA
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hinner : ∀ σ ∉ Bad l.length, ‖applyOps d n l X σ‖ ≤ A * (1 : ℝ) := by
        intro σ hσ; rw [mul_one]; exact ih σ hσ
      have hEnvl : ∀ σ, ‖applyOps d n l X σ‖ ≤ 2 ^ numQ l * Env := fun σ =>
        norm_applyOps_le l hEnv σ
      have hsplit := norm_condRow_le_split (k := κ) (X := applyOps d n l X)
        (hX.applyOps l).meas (f := fun _ : Sizes.SeqΩ d => (1 : ℝ)) (fun _ => zero_le_one)
        (fun _ => integrable_const 1) hEnvl hA0 (hfam.meas l.length) hinner ω
      have hcr : condRowReal d n κ (fun _ : Sizes.SeqΩ d => (1 : ℝ)) ω = 1 := by
        rw [condRowReal_const]
      rw [hcr, mul_one] at hsplit
      have hsl := hfam.slice l.length κ hω
      have hEnvpos : (0 : ℝ) ≤ 2 ^ numQ l * Env := by positivity
      have hterm : 2 ^ numQ l * Env * (Sizes.seqP d).real (rowSlice d n κ (Bad l.length) ω)
          ≤ 2 ^ numQ l * Env * ε := mul_le_mul_of_nonneg_left hsl hEnvpos
      have hcond : ‖condRow d n κ (applyOps d n l X) ω‖ ≤ A + 2 ^ numQ l * Env * ε := by
        linarith
      have hEe : (0 : ℝ) ≤ 2 ^ numQ l * Env * ε := by positivity
      cases b
      · rw [applyOps_cons_false, numQ_cons_false]
        refine hcond.trans (le_of_eq ?_)
        rw [hA, List.length_cons]
        push_cast
        ring
      · rw [applyOps_cons_true, numQ_cons_true]
        have htri : ‖qRow d n κ (applyOps d n l X) ω‖
            ≤ ‖applyOps d n l X ω‖ + ‖condRow d n κ (applyOps d n l X) ω‖ := by
          rw [qRow_apply]; exact norm_sub_le _ _
        have hgoal : 2 ^ (numQ l + 1) * (c + ((l.length : ℝ) + 1) * Env * ε)
            = 2 * A + 2 * (2 ^ numQ l * Env * ε) := by
          rw [hA]; ring
        have h1 := ih ω hωl
        rw [List.length_cons]
        push_cast
        rw [hgoal]
        linarith

/-! ### The sharp size of the word's minor difference, at one sample point -/

section Words

variable {u : ℝ} {z m : ℂ} {Ψ : ℝ} {M : ℕ}

theorem numQ_append_true (L : List (Bool × Idx (d.L n) (d.W n))) (k : Idx (d.L n) (d.W n)) :
    numQ (L ++ [(true, k)]) = numQ L + 1 := by
  simp [numQ, List.countP_append]

/-- **Both grades of the gain in one statement**, at a *single* sample point: the word's minor
difference of `G^{(·)}_{kk} - m` is at most `C_M Ψ^{#Q + 1}`.

The empty word is (4.3) itself (`norm_greenSetDiagCentered_le`) and a non-empty word is the `Δ_κ`
calculus (`norm_minorDiff_greenSetDiagCentered_le`).  `ω` appears only as the point at which the
hypothesis and the conclusion are read: no `∀ ω`. -/
theorem norm_minorDiff_qList_greenSetDiagCentered_le {ω : Sizes.SeqΩ d}
    (hg : MinorGoodLe d n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (k : Idx (d.L n) (d.W n))
    (L : List (Bool × Idx (d.L n) (d.W n))) (h1 : ((L.map Prod.snd)).Nodup)
    (h2 : ∀ x ∈ L, x.2 ≠ k) (hM : L.length ≤ M) :
    ‖minorDiff d n (qList L) (greenSetDiagCentered d n u z m k) ω‖
      ≤ minorDiffC M * Ψ ^ (numQ L + 1) := by
  classical
  have hlenq : (qList L).length = numQ L := length_qList L
  have hnodup : (qList L).Nodup := qList_nodup h1
  have hne : ∀ y ∈ qList L, y ≠ k := fun y hy => mem_qList_ne h2 hy
  have hCM := one_le_minorDiffC M
  cases hqs : qList L with
  | nil =>
      have hzero : numQ L = 0 := by rw [← hlenq, hqs]; rfl
      rw [hzero, pow_one]
      have hb := norm_greenSetDiagCentered_le hg hΨ0 k ∅ (by simp)
      simp only [minorDiff]
      nlinarith
  | cons κ l' =>
      have hκmem : κ ∈ qList L := by rw [hqs]; exact List.mem_cons_self
      have hkκ : k ≠ κ := Ne.symm (hne κ hκmem)
      have hnd' : (κ :: l').Nodup := by rw [← hqs]; exact hnodup
      have hkl : ∀ x ∈ l', x ≠ k := by
        intro x hx
        exact hne x (by rw [hqs]; exact List.mem_cons_of_mem _ hx)
      have hm : numQ L = l'.length + 1 := by rw [← hlenq, hqs]; simp [List.length_cons]
      have hq : numQ L ≤ L.length := List.countP_le_length
      have hlM1 : l'.length + 1 ≤ M := by omega
      have hlM : l'.length ≤ M := by omega
      rw [hm]
      refine le_trans (norm_minorDiff_greenSetDiagCentered_le hg hΨ0 hΨ1 k κ l'
        hkκ hnd' hkl hlM1) ?_
      have hmono := minorDiffC_mono hlM
      have hpow : (0 : ℝ) ≤ Ψ ^ (l'.length + 2) := pow_nonneg hΨ0 _
      have : l'.length + 1 + 1 = l'.length + 2 := by omega
      rw [this]
      exact mul_le_mul_of_nonneg_right hmono hpow

end Words

/-! ### The conditionalized estimate for one factor -/

section Factor

variable {E t : ℝ}

/-- **One factor of the `2p`-th moment, conditionalized.**

The object is `applyOps L (Δ_{qList L} Z^{(·)}_k)`.  Since `Z^{(S)}_k = Q_k (G^{(S)}_{kk} - m)` and
`Δ` commutes with `Q_k` (`minorDiff_flucDiagSet_eq`), the whole object is the *single* word
`L ++ [(true, k)]` applied to the **deterministic** family `Δ_{qList L} (G^{(·)}_{kk} - m)`, which
is where the good event enters pointwise.  `norm_applyOps_le_badFamily` then carries it through the
`#L + 1` conditional expectations. -/
theorem norm_applyOps_minorDiff_flucDiagSet_le_badFamily
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hε : 0 ≤ ε)
    {M : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ d)} (hfam : BadFamily d n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d n u (spectralZ E t) (spectralM E) ω Ψ M)
    (k : Idx (d.L n) (d.W n)) (L : List (Bool × Idx (d.L n) (d.W n)))
    (h1 : ((L.map Prod.snd)).Nodup) (h2 : ∀ x ∈ L, x.2 ≠ k) (hM : L.length ≤ M)
    (ω : Sizes.SeqΩ d) (hω : ω ∉ Bad (L.length + 1)) :
    ‖applyOps d n L
        (minorDiff d n (qList L) (flucDiagSet d n u (spectralZ E t) (spectralM E) k)) ω‖
      ≤ 2 ^ (numQ L + 1)
        * (minorDiffC M * Ψ ^ (numQ L + 1)
            + ((L.length : ℝ) + 1) * (2 ^ numQ L * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε) := by
  classical
  set Y : Sizes.SeqΩ d → ℂ :=
    minorDiff d n (qList L) (greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k) with hY
  have hrw : applyOps d n L
        (minorDiff d n (qList L) (flucDiagSet d n u (spectralZ E t) (spectralM E) k))
      = applyOps d n (L ++ [(true, k)]) Y := by
    rw [minorDiff_flucDiagSet_eq hE ht u k (qList L), applyOps_append, hY]
    rfl
  have hYbdd : BddMeas d Y :=
    bddMeas_minorDiff _ _ fun S => bddMeas_greenSetDiagCentered hE ht u k S
  have hYenv : ∀ ω', ‖Y ω'‖ ≤ 2 ^ numQ L * ((RBM.Path.etaT E t)⁻¹ + 1) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L)
      (greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k)
      (fun S ω'' => norm_greenSetDiagCentered_le_env hE ht u k S ω'') ω'
    rwa [length_qList, spectralZ_im] at hb
  have hYgood : ∀ ω' ∉ Bad 0, ‖Y ω'‖ ≤ minorDiffC M * Ψ ^ (numQ L + 1) := fun ω' hω' =>
    norm_minorDiff_qList_greenSetDiagCentered_le (hgood ω' hω') hΨ0 hΨ1 k L h1 h2 hM
  have hc0 : 0 ≤ minorDiffC M * Ψ ^ (numQ L + 1) :=
    mul_nonneg (minorDiffC_nonneg M) (pow_nonneg hΨ0 _)
  have hlen : (L ++ [(true, k)]).length = L.length + 1 := by simp
  have hωa : ω ∉ Bad ((L ++ [(true, k)]).length) := by rwa [hlen]
  have hkey := norm_applyOps_le_badFamily hYbdd hfam hYenv hc0 hε hYgood
    (L ++ [(true, k)]) ω hωa
  rw [numQ_append_true, hlen] at hkey
  rw [hrw]
  refine hkey.trans (le_of_eq ?_)
  push_cast
  ring

end Factor

/-! ### The conditionalized moment bound -/

section Moment

variable {E t : ℝ}

/-- A pointwise family of bounds **valid only off a measurable set** gives the expectation bound,
with the set's probability charged at the deterministic envelope. -/
theorem integral_prod_norm_le_of_bounds_on {ι : Type*} [Fintype ι] {F : ι → Sizes.SeqΩ d → ℂ}
    (hF : ∀ i, BddMeas d (F i)) {b : ι → ℝ} {Genv : ℝ} {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ ω ∉ S, ∀ i, ‖F i ω‖ ≤ b i) (hG : ∀ ω, ∏ i, ‖F i ω‖ ≤ Genv) :
    ∫ ω, ∏ i, ‖F i ω‖ ∂(Sizes.seqP d) ≤ (∏ i, b i) + Genv * (Sizes.seqP d).real S := by
  classical
  have hnorm : (fun ω : Sizes.SeqΩ d => ∏ i, ‖F i ω‖) = fun ω => ‖∏ i, F i ω‖ :=
    funext fun ω => (norm_prod _ _).symm
  have hint : Integrable (fun ω : Sizes.SeqΩ d => ∏ i, ‖F i ω‖) (Sizes.seqP d) := by
    rw [hnorm]; exact (bddMeas_prod Finset.univ fun i _ => hF i).integrable.norm
  have hindint : Integrable (S.indicator fun _ : Sizes.SeqΩ d => Genv) (Sizes.seqP d) :=
    (integrable_const Genv).indicator hS
  have hb0' : (0 : ℝ) ≤ ∏ i, b i := Finset.prod_nonneg fun i _ => hb0 i
  have hpt : ∀ ω : Sizes.SeqΩ d, ∏ i, ‖F i ω‖ ≤ (∏ i, b i) + S.indicator (fun _ => Genv) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      linarith [hG ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hb ω hω i
  calc ∫ ω, ∏ i, ‖F i ω‖ ∂(Sizes.seqP d)
      ≤ ∫ ω, ((∏ i, b i) + S.indicator (fun _ => Genv) ω) ∂(Sizes.seqP d) :=
        integral_mono hint ((integrable_const _).add hindint) hpt
    _ = (∏ i, b i) + Genv * (Sizes.seqP d).real S := by
        rw [integral_add (integrable_const _) hindint, integral_indicator_const _ hS,
          smul_eq_mul, mul_comm ((Sizes.seqP d).real S) Genv]
        simp

/-- The deterministic envelope of one factor, for words of length at most `M`:
`2^{2M+1}(η_t⁻¹ + 1)`, with `η_t = RBM.Path.etaT`. -/
noncomputable def condEnv (E t : ℝ) (M : ℕ) : ℝ :=
  2 ^ (2 * M + 1) * ((RBM.Path.etaT E t)⁻¹ + 1)

theorem condEnv_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 0 ≤ condEnv E t M := by
  have hη : 0 < RBM.Path.etaT E t := etaT_pos hE ht
  unfold condEnv
  positivity

/-- **The price of conditionalizing**, per factor: the `#L + 1` conditional expectations each
integrate over a row section of the exceptional set, and each such section is only `ε`-small.
Dividing by `(2Ψ)^M` is what puts the loss into the *constant* `B` of the graded interface rather
than into the gain `ρ`. -/
noncomputable def condCost (E t : ℝ) (M : ℕ) (Ψ ε : ℝ) : ℝ :=
  ((M : ℝ) + 1) * condEnv E t M * ε * ((2 * Ψ) ^ M)⁻¹

theorem condCost_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hε : 0 ≤ ε) : 0 ≤ condCost E t M Ψ ε := by
  have := condEnv_nonneg hE ht (E := E) (t := t) M
  unfold condCost
  have h2 : (0 : ℝ) ≤ ((2 * Ψ) ^ M)⁻¹ := by positivity
  have h3 : (0 : ℝ) ≤ ((M : ℝ) + 1) := by positivity
  positivity

theorem norm_applyOps_minorDiff_flucDiagSet_le_condEnv (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {M : ℕ} (k : Idx (d.L n) (d.W n)) (L : List (Bool × Idx (d.L n) (d.W n)))
    (hM : (L).length ≤ M) (ω : Sizes.SeqΩ d) :
    ‖applyOps d n L
        (minorDiff d n (qList L) (flucDiagSet d n u (spectralZ E t) (spectralM E) k)) ω‖
      ≤ condEnv E t M := by
  have hη : 0 < RBM.Path.etaT E t := etaT_pos hE ht
  have hq : numQ L ≤ M := le_trans List.countP_le_length hM
  have hdiff : ∀ ω', ‖minorDiff d n (qList L)
      (flucDiagSet d n u (spectralZ E t) (spectralM E) k) ω'‖
        ≤ 2 ^ numQ L * (2 * ((RBM.Path.etaT E t)⁻¹ + 1)) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L) (flucDiagSet d n u (spectralZ E t) (spectralM E) k)
      (fun S ω'' => norm_flucDiagSet_le_env hE ht u k S ω'') ω'
    rwa [length_qList, spectralZ_im] at hb
  refine le_trans (norm_applyOps_le L hdiff ω) ?_
  have hpow : (2 : ℝ) ^ numQ L * (2 ^ numQ L * (2 * ((RBM.Path.etaT E t)⁻¹ + 1)))
      = 2 ^ (2 * numQ L + 1) * ((RBM.Path.etaT E t)⁻¹ + 1) := by
    rw [show 2 * numQ L + 1 = numQ L + numQ L + 1 by omega, pow_succ, pow_add]
    ring
  rw [hpow]
  unfold condEnv
  have hmono : (2 : ℝ) ^ (2 * numQ L + 1) ≤ 2 ^ (2 * M + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnn : (0 : ℝ) ≤ (RBM.Path.etaT E t)⁻¹ + 1 := by positivity
  exact mul_le_mul_of_nonneg_right hmono hnn

/-- **(4.12)'s last input, conditionalized on the good event.**

`hgood` is read at one sample point at a time and only *off* `Bad 0`; there is no hypothesis
quantified over all `ω`.  The price is the two explicit terms:

* the per-factor constant grows from `2 C_M Ψ` to `2 C_M Ψ + condCost`, i.e. by
  `(M+1) 2^{2M+1}(η_t⁻¹+1) ε (2Ψ)^{-M}`, where `ε` is the row-section threshold of the
  `BadFamily`;
* an additive remainder `(2^{2M+1}(η_t⁻¹+1))^{#slots} P(Bad_{M+1})`.

The additive remainder is *not* removable inside an interface whose index type `ι` is
unrestricted; it is absorbed by the budget `#ι ≤ K` in `minorDiffGainUpTo'_of_le_on`. -/
theorem integral_prod_applyOps_minorDiff_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ d)} (hfam : BadFamily d n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d n u (spectralZ E t) (spectralM E) ω Ψ M)
    (ι : Type) [Fintype ι] (k : ι → Idx (d.L n) (d.W n))
    (L : ι → List (Bool × Idx (d.L n) (d.W n)))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps d n (L i)
        (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i))) ω‖
        ∂(Sizes.seqP d)
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ Fintype.card ι
          * (2 * Ψ) ^ ∑ i, numQ (L i)
        + condEnv E t M ^ Fintype.card ι * (Sizes.seqP d).real (Bad (M + 1)) := by
  classical
  have hη : 0 < RBM.Path.etaT E t := etaT_pos hE ht
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have hΨ1 : Ψ ≤ 1 := by linarith
  have hEnv0 : 0 ≤ condEnv E t M := condEnv_nonneg hE ht M
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  set B : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB
  have hB0 : 0 ≤ B := by
    have := minorDiffC_nonneg M
    rw [hB]
    have : (0:ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    linarith
  -- the per-factor bound off the exceptional set
  have hb : ∀ ω ∉ Bad (M + 1), ∀ i : ι,
      ‖applyOps d n (L i)
        (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i))) ω‖
        ≤ B * (2 * Ψ) ^ numQ (L i) := by
    intro ω hω i
    have hωi : ω ∉ Bad ((L i).length + 1) := by
      intro hmem
      exact hω (hfam.mono_le (by have := hM i; omega) hmem)
    have hkey := norm_applyOps_minorDiff_flucDiagSet_le_badFamily hE ht u hΨ0' hΨ1 hε hfam
      hgood (k i) (L i) (h1 i) (h2 i) (hM i) ω hωi
    refine hkey.trans ?_
    set q : ℕ := numQ (L i) with hq
    have hqM : q ≤ M := le_trans List.countP_le_length (hM i)
    -- the gain term is exact
    have hgain : (2 : ℝ) ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
        = (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    -- the exceptional term is charged to `condCost`
    have hpowle : ((2 * Ψ) ^ M : ℝ) ≤ (2 * Ψ) ^ q :=
      pow_le_pow_of_le_one h2Ψ0.le hΨhalf hqM
    have hexact : (2 * Ψ) ^ M * condCost E t M Ψ ε = ((M : ℝ) + 1) * condEnv E t M * ε := by
      unfold condCost
      field_simp
    have hlen : ((L i).length : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have : ((L i).length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM i
      linarith
    have h2q : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) ≤ condEnv E t M := by
      unfold condEnv
      have hrw : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1))
          = 2 ^ (2 * q + 1) * ((RBM.Path.etaT E t)⁻¹ + 1) := by
        rw [show 2 * q + 1 = q + q + 1 by omega, pow_succ, pow_add]
        ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    have hexc : (2 : ℝ) ^ (q + 1)
        * (((L i).length + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * condCost E t M Ψ ε := by
      have hstep : (2 : ℝ) ^ (q + 1)
          * (((L i).length + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε)
          = (((L i).length : ℝ) + 1)
              * (2 ^ (q + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1))) * ε := by
        ring
      rw [hstep]
      have hA : (((L i).length : ℝ) + 1)
            * (2 ^ (q + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1))) * ε
          ≤ ((M : ℝ) + 1) * condEnv E t M * ε := by
        have hnn1 : (0 : ℝ) ≤ ((L i).length : ℝ) + 1 := by positivity
        have hnn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (q + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) := by
          positivity
        have := mul_le_mul hlen h2q hnn2 (by positivity)
        exact mul_le_mul_of_nonneg_right this hε
      refine hA.trans ?_
      rw [← hexact]
      exact mul_le_mul_of_nonneg_right hpowle hcost0
    have hsplit : (2 : ℝ) ^ (q + 1)
        * (minorDiffC M * Ψ ^ (q + 1)
            + ((L i).length + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε)
        = 2 ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε) := by
      ring
    rw [hsplit, hgain, hB]
    calc (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ)
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((RBM.Path.etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) + (2 * Ψ) ^ q * condCost E t M Ψ ε := by
          linarith
      _ = (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) * (2 * Ψ) ^ q := by ring
  -- the global envelope
  have hG : ∀ ω : Sizes.SeqΩ d, ∏ i, ‖applyOps d n (L i)
      (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i))) ω‖
      ≤ condEnv E t M ^ Fintype.card ι := by
    intro ω
    calc ∏ i, ‖applyOps d n (L i)
          (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i)))
            ω‖
        ≤ ∏ _i : ι, condEnv E t M :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
            norm_applyOps_minorDiff_flucDiagSet_le_condEnv hE ht u (k i) (L i) (hM i) ω
      _ = condEnv E t M ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]
  have hbm : ∀ i : ι, BddMeas d (applyOps d n (L i)
      (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  have hb0 : ∀ i : ι, 0 ≤ B * (2 * Ψ) ^ numQ (L i) := fun i => by positivity
  refine le_trans (integral_prod_norm_le_of_bounds_on hbm (hfam.meas (M + 1)) hb0 hb hG) ?_
  have heq : (∏ i : ι, B * (2 * Ψ) ^ numQ (L i))
      = B ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      Finset.card_univ]
  rw [heq]

end Moment

/-! ### The hypothesis is produced from the good event, not postulated -/

section Bridge

variable {E t δ : ℕ → ℝ}

/-- The base of the tower: a **measurable** hull of the complement of the per-time good event
`{ω | ∀ i j, llErrMat … i j ≤ δ n}` at the time `t n` (`‖G_{t n} - m‖_max ≤ δ n`, the paper's
`Ω(t,c)` of (4.1)).  Measures
in Mathlib are outer measures, so the hull has exactly the same measure as the complement itself
(`meas_badBase`), and a high-probability statement about the event bounds that. -/
noncomputable def badBase (d : Sizes) (E t δ : ℕ → ℝ) (n : ℕ) : Set (Sizes.SeqΩ d) :=
  toMeasurable (Sizes.seqP d)
    {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
      llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n}ᶜ

theorem measurableSet_badBase (d : Sizes) (E t δ : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (badBase d E t δ n) := measurableSet_toMeasurable _ _

theorem meas_badBase (d : Sizes) (E t δ : ℕ → ℝ) (n : ℕ) :
    (Sizes.seqP d) (badBase d E t δ n)
      = (Sizes.seqP d) {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
          llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n}ᶜ :=
  measure_toMeasurable _

/-- **`hgood` is a theorem.**  Off the hull of the complement of the per-time good event, the
level-budgeted good event holds at threshold `2 δ n`.  This is `minorGoodLe_of_goodEvent_flow`
composed with the definitional identity of `llErrMat … i j ≤ δ` and `GoodEvent (green H z) m δ`
(the entry `‖G_{ij} - m 1_{i=j}‖`). -/
theorem minorGoodLe_of_notMem_badBase (hE : |E n| ≤ 2)
    (hz : (spectralZ (E n) (t n)).im ≠ 0) {M : ℕ}
    (hδ0 : 0 ≤ δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    {ω : Sizes.SeqΩ d} (hω : ω ∉ badBase d E t δ n) :
    MinorGoodLe d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) ω (2 * δ n) M := by
  have hmem : ω ∈ {ω : Sizes.SeqΩ d | ∀ i j : Idx (d.L n) (d.W n),
      llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ δ n} := by
    by_contra h
    exact hω (subset_toMeasurable (Sizes.seqP d) _ h)
  exact minorGoodLe_of_goodEvent_flow hE hz hδ0 hδ4 hMδ hmem

end Bridge

/-! ### The conditionalized estimate, packaged as a budgeted interface

With the cardinality budget `#ι ≤ K` the additive remainder of `integral_prod_applyOps_minorDiff_le_on`
**is** absorbable, and the conditionalized (4.12) input becomes an interface again rather than an
inequality with a tail.  The arithmetic is the one the budget is for:

  `condEnv^{#ι} P(Bad) ≤ condEnv^K P(Bad) ≤ B₀^K (2Ψ)^{KM} ≤ B₀^{#ι} (2Ψ)^{∑ q}`,

using `1 ≤ condEnv`, `#ι ≤ K`, `B₀ ≤ 1`, `2Ψ ≤ 1` and `∑ q ≤ #ι M ≤ K M`; the middle step is the
one genuine hypothesis, a smallness condition on the measure of the tower.  Adding the remainder to
the main term then costs a factor `2 ≤ 2^{#ι}`, i.e. `B = 2 B₀`, and the gain `ρ = 2Ψ` is
untouched.

At `#ι = 0` the bound `1 + P(Bad) ≤ 1` would be false, so that case is not routed through the
remainder at all: the integrand is an empty product, the integral of `1` against a probability
measure, and the conclusion is `1 ≤ 1`. -/

section Budget

variable {E t : ℝ}

theorem one_le_condEnv (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 1 ≤ condEnv E t M := by
  have hη : 0 < RBM.Path.etaT E t := etaT_pos hE ht
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * M + 1) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (RBM.Path.etaT E t)⁻¹ + 1 := by
    have := inv_nonneg.2 hη.le
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 2 ^ (2 * M + 1) * ((RBM.Path.etaT E t)⁻¹ + 1) := by
        exact mul_le_mul h1 h2 zero_le_one (by positivity)
    _ = condEnv E t M := rfl

/-- **The row-section threshold that makes the conditionalization cost exactly `Ψ`.**

`condCost` is linear in `ε`, so there is one choice of the `BadFamily` threshold for which the
price of conditionalizing is the same `Ψ` as the gain itself; with it the constant of the budgeted
interface is `2(2 minorDiffC M + 1) Ψ`, i.e. `≍ Ψ`, which is the paper's size. -/
noncomputable def condEps (E t : ℝ) (M : ℕ) (Ψ : ℝ) : ℝ :=
  Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹

theorem condEps_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    0 ≤ condEps E t M Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  unfold condEps
  positivity

theorem condCost_condEps (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 < Ψ) :
    condCost E t M Ψ (condEps E t M Ψ) = Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  have hMEnv : (0 : ℝ) < ((M : ℝ) + 1) * condEnv E t M := by positivity
  have h1 : ((2 * Ψ) ^ M : ℝ) ≠ 0 := by positivity
  have h2 : (((M : ℝ) + 1) * condEnv E t M) ≠ 0 := ne_of_gt hMEnv
  unfold condCost condEps
  calc ((M : ℝ) + 1) * condEnv E t M
          * (Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹) * ((2 * Ψ) ^ M)⁻¹
      = (((M : ℝ) + 1) * condEnv E t M * (((M : ℝ) + 1) * condEnv E t M)⁻¹)
          * ((2 * Ψ) ^ M * ((2 * Ψ) ^ M)⁻¹) * Ψ := by ring
    _ = Ψ := by rw [mul_inv_cancel₀ h2, mul_inv_cancel₀ h1, mul_one, one_mul]

/-- **The conditionalized (4.12) input, as a budgeted interface.**

The hypotheses are those of `integral_prod_applyOps_minorDiff_le_on` plus the two that the
absorption needs: `hB1`, that the per-factor constant is at most `1` (automatic at
`B₀ ≍ Ψ → 0`), and `hsmall`, that the tower is small enough at the two budgets.  Neither is a
`∀ ω` hypothesis, and neither involves the index type.

The constant doubles, `B = 2 B₀`; the gain is exactly the `ρ = 2Ψ` of
`integral_prod_applyOps_minorDiff_le_on`, unchanged. -/
theorem minorDiffGainUpTo'_of_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M K : ℕ} {Bad : ℕ → Set (Sizes.SeqΩ d)} (hfam : BadFamily d n ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d n u (spectralZ E t) (spectralM E) ω Ψ M)
    (hB1 : 2 * minorDiffC M * Ψ + condCost E t M Ψ ε ≤ 1)
    (hsmall : condEnv E t M ^ K * (Sizes.seqP d).real (Bad (M + 1))
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ K * (2 * Ψ) ^ (K * M)) :
    MinorDiffGainUpTo' d n u (spectralZ E t) (spectralM E)
      (2 * (2 * minorDiffC M * Ψ + condCost E t M Ψ ε)) (2 * Ψ) M K := by
  classical
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have hC := minorDiffC_nonneg M
  set B₀ : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB₀def
  have hB₀0 : 0 ≤ B₀ := by
    have : (0 : ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    rw [hB₀def]; linarith
  refine ⟨by positivity, by positivity, fun ι _ k L h1 h2 hlen hcard => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hemp : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
    simp [Finset.univ_eq_empty]
  · have hmain := integral_prod_applyOps_minorDiff_le_on hE ht u hΨ0 hΨhalf hε hfam hgood
      ι k L h1 h2 hlen
    refine hmain.trans ?_
    -- the sum of the gain exponents is at most `K * M`
    have hq : (∑ i, numQ (L i)) ≤ K * M := by
      have hstep : (∑ i, numQ (L i)) ≤ ∑ _i : ι, M :=
        Finset.sum_le_sum fun i _ => le_trans List.countP_le_length (hlen i)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstep
      exact le_trans hstep (Nat.mul_le_mul_right M hcard)
    have hEnv1 : 1 ≤ condEnv E t M := one_le_condEnv hE ht M
    have hPnn : 0 ≤ (Sizes.seqP d).real (Bad (M + 1)) := measureReal_nonneg
    have hmainnn : 0 ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by positivity
    -- the remainder is dominated by the main term
    have hrem : condEnv E t M ^ Fintype.card ι * (Sizes.seqP d).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
      calc condEnv E t M ^ Fintype.card ι * (Sizes.seqP d).real (Bad (M + 1))
          ≤ condEnv E t M ^ K * (Sizes.seqP d).real (Bad (M + 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hEnv1 hcard) hPnn
        _ ≤ B₀ ^ K * (2 * Ψ) ^ (K * M) := hsmall
        _ ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
            refine mul_le_mul (pow_le_pow_of_le_one hB₀0 hB1 hcard)
              (pow_le_pow_of_le_one h2Ψ0.le hΨhalf hq) (by positivity) (by positivity)
    -- and the doubling is paid by `2 ≤ 2 ^ #ι`
    have hdouble : (2 : ℝ) ≤ 2 ^ Fintype.card ι := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ one_le_two hpos
    calc B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + condEnv E t M ^ Fintype.card ι * (Sizes.seqP d).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by linarith
      _ = 2 * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) := by ring
      _ ≤ 2 ^ Fintype.card ι * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) :=
          mul_le_mul_of_nonneg_right hdouble hmainnn
      _ = (2 * B₀) ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
          rw [mul_pow (2 : ℝ) B₀ (Fintype.card ι)]; ring

end Budget

/-! ### The budgeted interface, produced from the per-time good event

The composition of `minorDiffGainUpTo'_of_le_on` with the bridge of the previous section: the
*only* probabilistic input is the per-time good event `{ω | ∀ i j, llErrMat … i j ≤ δ n}` (the
paper's `Ω(t,c)` of (4.1) at the time `t n`), there is **no** hypothesis quantified over all sample
points, and the exceptional set charged is the explicit tower `badTower` over the measurable hull
of its complement.  The residual hypothesis `hsmall` is a statement about the *measure* of that
tower, which `meas_badTower_le` bounds by `((ε + size n)/ε)^{M+1} P(Ω(t,c)ᶜ)`: super-polynomially
small for each fixed pair of budgets (the high-probability input of the event is a separate
statement, `highProbAt_detFlucDelta_of_localLaw`). -/

section Endpoints

variable {E t δ : ℕ → ℝ}

/-- **`MinorDiffGainUpTo'` from the per-time good event (4.1)**, at the time `t n`. -/
theorem minorDiffGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε)
    {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1)
    (hsmall : condEnv (E n) (t n) M ^ K
        * (Sizes.seqP d).real (badTower d n ε (badBase d E t δ n) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K
          * (2 * (2 * δ n)) ^ (K * M)) :
    MinorDiffGainUpTo' d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
      (2 * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε))
      (2 * (2 * δ n)) M K := by
  have hz : (spectralZ (E n) (t n)).im ≠ 0 := by
    rw [spectralZ_im]; exact ne_of_gt (etaT_pos hE ht1)
  exact minorDiffGainUpTo'_of_le_on (E := E n) (t := t n) hE ht1 (t n) (Ψ := 2 * δ n)
    (by linarith) (by linarith) hε
    (badFamily_badTower d n ε (measurableSet_badBase d E t δ n))
    (fun ω hω => minorGoodLe_of_notMem_badBase hE.le hz hδ0.le hδ4 hMδ hω) hB1 hsmall

/-- **`FlucGainUpTo'` from the per-time good event (4.1)**: the interface consumed by the
`2p`-th moment expansion, with every hypothesis produced from (4.1) at the time
`t n` and explicit numeric side conditions. -/
theorem flucGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε)
    {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1)
    (hsmall : condEnv (E n) (t n) M ^ K
        * (Sizes.seqP d).real (badTower d n ε (badBase d E t δ n) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K
          * (2 * (2 * δ n)) ^ (K * M)) :
    FlucGainUpTo' d n (t n) (spectralZ (E n) (t n)) (spectralM (E n))
      (2 * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε))
      (2 * (2 * δ n)) M K :=
  flucGainUpTo'_of_minorDiffGainUpTo' (E := E n) (t := t n) hE ht1 (t n)
    (minorDiffGainUpTo'_goodEvent hE ht1 hε hδ0 hδ4 hMδ hB1 hsmall)

end Endpoints

end RBM.Green
