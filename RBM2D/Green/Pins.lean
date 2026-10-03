/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Vocab
import RBM2D.Induction.Defs

/-!
# The `lem_GbEXP` statements and their bridges

The statements `GbEXPHypV3`, `GbEXPV3Theorem` (the per-sequence form of
`lem_GbEXP`), the per-time shapes, and the bridges between them.

Paper: arXiv:2503.07606, Section "Estimates for entries of `G`": `lem_GbEXP`, (`def_asGMc`),
(`GijGEX`), (`GiiGEX`), (`asGMc`), (`GavLGEX`).

Contents:
1. matrix-level pieces (`omegaInd`, `offSq`, `diagSq`);
2. per-sequence components of `lem_GbEXP` (one time `t n` per size index `n`);
3. the statements `GbEXPHypV3`, `GbEXPV3Theorem`;
4. per-time shapes `GijGEXPTSwap`, `GiiGEXPT`, `AsGMcPT` and the bridges;
5. elementary facts: a per-time domination with left side `≤ 0` and right side `≥ 0` holds,
   nonnegativity of `gexRHS` and `maxLoopPM`, and the norm of `𝓛_{(+,-)}`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. Matrix-level pieces -/

section MatrixLevel

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The indicator of `Ω(u,c) = {‖G_u - m‖_max ≤ W^{-c}}` (`def_asGMc`) at the matrix
`M`, spectral parameter `z_u^{(E)}`. -/
def omegaInd (E u c : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  if ∀ i j : Idx L W, llErrMat L W E u M i j ≤ (W : ℝ) ^ (-c) then 1 else 0

/-- `|G_{pq}|²` off the diagonal, `0` on it (left side of (`GijGEX`), with the
restriction `p ≠ q`). -/
def offSq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p q : BlockIndex L W) : ℝ :=
  if p = q then 0 else ‖greenBlk L W E u M true p q‖ ^ 2

/-- `|G_{pp} - m|²` (left side of (`GiiGEX`)). -/
def diagSq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p : BlockIndex L W) : ℝ :=
  ‖greenBlk L W E u M true p p - spectralM E‖ ^ 2

end MatrixLevel

/-! ## 2. Per-sequence components (time `t n`, energy `E n` at size index `n`) -/

section Components

variable (d : Sizes)

/-- (`GijGEX`), on `Ω(t,c)` (`def_asGMc`), off the diagonal,
right side with the swapped pair.  Component of `GbEXPHypV3`. -/
def GijOmegaSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
    (fun n p ω => omegaInd (d.L n) (d.W n) (E n) (t n) c (Sizes.seqHflow d n (t n) ω) *
      offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
    (fun n p ω => gexRHS (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.2.1 p.2.1.1)

/-- (`GiiGEX`), on `Ω(t,c)`.  Component of `GbEXPHypV3`. -/
def GiiOmegaSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × BlockIndex (d.L n) (d.W n))
    (fun n p ω => omegaInd (d.L n) (d.W n) (E n) (t n) c (Sizes.seqHflow d n (t n) ω) *
      diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2)
    (fun n _ ω => maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω))

/-- (`asGMc`): `‖G_t - m‖_max ≺ W^{-c}`.  Hypothesis inside `GbEXPHypV3`. -/
def AsGMcSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
    (fun n _ _ => (d.W n : ℝ) ^ (-c))

/-- (`GijGEX`), without the indicator under (`asGMc`), off the diagonal,
swapped right side.  Component of `GbEXPHypV3`. -/
def GijSeq (E t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
    (fun n p ω => offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
    (fun n p ω => gexRHS (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.2.1 p.2.1.1)

/-- (`GiiGEX`), without the indicator under (`asGMc`).  Component of
`GbEXPHypV3`. -/
def GiiSeq (E t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × BlockIndex (d.L n) (d.W n))
    (fun n p ω => diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2)
    (fun n _ ω => maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω))

/-- `max_{a,b} |𝓛_{t,(+,-),(a,b)}| ≺ Ψ²` for a deterministic `Ψ` (the right side of (`GavLGEX`),
bounded deterministically).  Hypothesis of the (`GavLGEX`) clause of `GbEXPHypV3`. -/
def LoopDetSeq (E t : ℕ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => ‖loopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2‖)
    (fun n _ _ => Ψ n ^ 2)

/-- (`GavLGEX`), with a deterministic control `Ψ²`:
`max_a |⟨(G_t - m) E_a⟩| ≺ Ψ²`.  Component of `GbEXPHypV3`. -/
def GavLDetSeq (E t : ℕ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
    (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true p.2‖)
    (fun n _ _ => Ψ n ^ 2)

end Components

/-! ## 3. The statements -/

section Pins

variable (d : Sizes)

/-- **`GbEXPHypV3`** (`lem_GbEXP`).  Fixed `κ` (bulk), `𝔠` (bandwidth,
`Main_DEL_COND`), `δ` (range `1 - t ≥ N^{-1+δ}`), then the size divergence, the
bandwidth, every energy and time sequence in the bulk with the range condition, and every `c > 0`:
* (`GijGEX`) on `Ω(t,c)`, off the diagonal, right side `Σ_{a'∼a} Σ_{b'∼b} 𝓛_{(+,-),(b',a')} +
  W^{-2} 1(|a-b|_L ≤ 1)` (swapped pair);
* (`GiiGEX`) on `Ω(t,c)`;
* under (`asGMc`) at `c`: (`GijGEX`), (`GiiGEX`) without the indicator, and (`GavLGEX`) in the
  deterministic-control form: `max 𝓛 ≺ Ψ²` with `0 ≤ Ψ ≤ N^{-a}` gives
  `max_a |⟨(G-m)E_a⟩| ≺ Ψ²`. -/
def GbEXPHypV3 (κ 𝔠 δ : ℝ) : Prop :=
  SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ c > (0 : ℝ),
    GijOmegaSeq d E t c ∧ GiiOmegaSeq d E t c ∧
    (AsGMcSeq d E t c →
      GijSeq d E t ∧ GiiSeq d E t ∧
      ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
        (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
        LoopDetSeq d E t Ψ → GavLDetSeq d E t Ψ)

/-- **`GbEXPV3Theorem`** (`lem_GbEXP`): `GbEXPHypV3` for
every size sequence and every `κ, 𝔠, δ > 0`.  Every use of `GbEXPHypV3` as a hypothesis is
discharged by this theorem. -/
def GbEXPV3Theorem : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → GbEXPHypV3 d κ 𝔠 δ

end Pins

/-! ## 4. Per-time shapes and bridges -/

section Bridges

/-- **Bridge: per sequence ⇒ per time over `[s,t]`.**  If a bound holds per sequence at
every time sequence `u n ∈ [s n, t n]`, it holds per time over `TimeIcc s t` (from
`RBM.Path.perTimeDomAt_iff_forall_section`, used twice). -/
theorem perTime_timeIcc_of_forall_seq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {V : ℕ → Type*}
    (hV : ∀ n, Nonempty (V n)) (ξ ζ : ∀ n, ℝ → V n → Ω → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt P size (U := fun n => Unit × V n)
        (fun n p ω => ξ n (u n) p.2 ω) (fun n p ω => ζ n (u n) p.2 ω)) :
    PerTimeDomAt P size (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => ξ n p.1 p.2 ω) (fun n p ω => ζ n p.1 p.2 ω) := by
  have hne : ∀ n, Nonempty (TimeIcc s t n × V n) :=
    fun n => ⟨(⟨s n, le_rfl, hst n⟩, (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne]
  intro sec
  have h1 := h (fun n => ((sec n).1 : ℝ)) (fun n => (sec n).1.2)
  have hne' : ∀ n, Nonempty (Unit × V n) := fun n => ⟨((), (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne'] at h1
  exact h1 (fun n => ((), (sec n).2))

/-- **Bridge (proved): per time over `[s,t]` ⇒ per sequence at any section time sequence.** -/
theorem perSeq_of_perTime_timeIcc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {s t : ℕ → ℝ} {V : ℕ → Type*} (hV : ∀ n, Nonempty (V n))
    (ξ ζ : ∀ n, ℝ → V n → Ω → ℝ)
    (h : PerTimeDomAt P size (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => ξ n p.1 p.2 ω) (fun n p ω => ζ n p.1 p.2 ω))
    (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) :
    PerTimeDomAt P size (U := fun n => Unit × V n)
      (fun n p ω => ξ n (u n) p.2 ω) (fun n p ω => ζ n (u n) p.2 ω) := by
  have hne : ∀ n, Nonempty (TimeIcc s t n × V n) :=
    fun n => ⟨(⟨u n, hu n⟩, (hV n).some)⟩
  have hne' : ∀ n, Nonempty (Unit × V n) := fun n => ⟨((), (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne] at h
  rw [perTimeDomAt_iff_forall_section P size hne']
  intro sec
  exact h (fun n => (⟨u n, hu n⟩, (sec n).2))

variable (d : Sizes)

/-- (`GijGEX`) per time, off the diagonal, with the `gexRHS` arguments
swapped (`p.2.2.1 p.2.1.1` in place of `p.2.1.1 p.2.2.1`). -/
def GijGEXPTSwap (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
    (fun n p ω => if p.2.1 = p.2.2 then 0 else
      ‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2.1 p.2.2‖ ^ 2)
    (fun n p ω => gexRHS (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.2.1 p.2.1.1)

/-- (`GiiGEX`), per time over `[s,t]`. -/
def GiiGEXPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × BlockIndex (d.L n) (d.W n))
    (fun n p ω =>
      ‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2 p.2 -
        spectralM (E n)‖ ^ 2)
    (fun n p ω => maxLoopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω))

/-- (`asGMc`), per time over `[s,t]`, at exponent `c`.  Used as a hypothesis of
`gijGEXPTSwap_giiGEXPT_of_V3`. -/
def AsGMcPT (E : ℕ → ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n _ _ => (d.W n : ℝ) ^ (-c))

/-- `RangeCond` passes to any time sequence below `t`. -/
theorem rangeCond_mono {δ : ℝ} {t u : ℕ → ℝ} (h : RangeCond d δ t) (hut : ∀ n, u n ≤ t n) :
    RangeCond d δ u :=
  h.mono fun n hn => hn.trans (by linarith [hut n])

/-- **Bridge: `GbEXPHypV3` ⇒ the per-time (`GijGEX`) (swapped) and (`GiiGEX`)**,
given (`asGMc`) per time over `[s,t]`. -/
theorem gijGEXPTSwap_giiGEXPT_of_V3 {κ 𝔠 δ c : ℝ} {E s t : ℕ → ℝ}
    (hV3 : GbEXPHypV3 d κ 𝔠 δ) (hN : SizeTendsto d) (hW : Bandwidth d 𝔠)
    (hE : ∀ n, |E n| < 2 - κ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hR : RangeCond d δ t) (hc : 0 < c) (hAs : AsGMcPT d E s t c) :
    GijGEXPTSwap d E s t ∧ GiiGEXPT d E s t := by
  have hseq : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      GijSeq d E u ∧ GiiSeq d E u := by
    intro u hu
    have hRu : RangeCond d δ u := rangeCond_mono d hR fun n => (hu n).2
    have hAsu : AsGMcSeq d E u c :=
      perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
        (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
        (fun n => ⟨(0, 0)⟩)
        (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
        (fun n _ _ _ => (d.W n : ℝ) ^ (-c)) hAs u hu
    have h := (hV3 hN hW E u hE (fun n => (hs n).trans (hu n).1)
      (fun n => (hu n).2.trans_lt (ht n)) hRu c hc).2.2 hAsu
    exact ⟨h.1, h.2.1⟩
  refine ⟨?_, ?_⟩
  · exact perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst
      (V := fun n => BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
      (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => offSq (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v q ω => gexRHS (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.2.1 q.1.1)
      fun u hu => (hseq u hu).1
  · exact perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst
      (V := fun n => BlockIndex (d.L n) (d.W n)) (fun n => ⟨0⟩)
      (fun n v q ω => diagSq (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q)
      (fun n v _ ω => maxLoopPM (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω))
      fun u hu => (hseq u hu).2

/-- **Bridge: the premises of `GbEXPHypV3 d (κ/2) c τ` at every time sequence in
`[s,t]` follow from `MainIndHyp d κ c τ E s t`.** -/
theorem v3_premises_of_mainIndHyp {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (h : MainIndHyp d κ c τ E s t) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) :
    SizeTendsto d ∧ Bandwidth d c ∧ (∀ n, |E n| < 2 - κ / 2) ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < 1) ∧ RangeCond d τ u := by
  obtain ⟨hκ, hE, _, _, hs, _, ht, hN, hW, _, hR, _⟩ := h
  refine ⟨hN, hW, fun n => by linarith [hE n], fun n => (hs n).trans (hu n).1,
    fun n => (hu n).2.trans_lt (ht n), rangeCond_mono d hR fun n => (hu n).2⟩

end Bridges

/-! ## 5. Elementary facts -/

section Extreme

/-- A per-time domination whose left side is `≤ 0` and right side `≥ 0` holds. -/
theorem perTimeDomAt_of_nonpos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} (ξ ζ : ∀ l, U l → Ω → ℝ)
    (hξ : ∀ l u ω, ξ l u ω ≤ 0) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ _ D _
  refine Eventually.of_forall fun l u => ?_
  have hempty : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hξ l u ω).trans
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) τ) (hζ l u ω))
  rw [hempty, measure_empty]
  exact bot_le

variable {L W : ℕ} [NeZero L] [NeZero W]

theorem gexRHS_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    0 ≤ gexRHS L W E u M a b := by
  unfold gexRHS
  refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_) ?_
  · split_ifs <;> simp
  · split_ifs <;> positivity

theorem maxLoopPM_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    0 ≤ maxLoopPM L W E u M :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : Z2 L × Z2 L => ‖loopPM L W E u M p.1 p.2‖)
    (Finset.mem_univ ((0 : Z2 L), (0 : Z2 L))))

/-- `‖𝓛_{u,(+,-),(a,b)}‖ = W⁻⁴ Σ_{β,α} |G_{(b,β),(a,α)}|²` for Hermitian `M` (from
`RBM.gloop_two_plus_minus_blocks`): rows in block `b`, columns in block `a`. -/
theorem norm_loopPM_eq {E u : ℝ} (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (a b : Z2 L) :
    ‖loopPM L W E u M a b‖ = ((W : ℝ)⁻¹ ^ 2) ^ 2 *
      ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W, ‖greenBlk L W E u M true (b, β) (a, α)‖ ^ 2 := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  unfold loopPM pmLoop
  rw [gloop_two_plus_minus_blocks hH]
  have hcast : ((W : ℂ)⁻¹ ^ 2) ^ 2 * ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,
      (Complex.normSq (green (blockMat M) (spectralZ E u) (b, β) (a, α)) : ℂ) =
      ((((W : ℝ)⁻¹ ^ 2) ^ 2 * ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,
        Complex.normSq (green (blockMat M) (spectralZ E u) (b, β) (a, α)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_of_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))]
  simp only [greenBlk, Gsig_true, Complex.normSq_eq_norm_sq]

end Extreme

end RBM.Green
