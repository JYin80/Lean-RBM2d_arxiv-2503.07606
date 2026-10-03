/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.Pins
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# The Step 2 good set `G(u)`

The definitions `goodSet` (six clauses; the (`GijGEX`) clause takes the swapped pair and the
(`GavLGEX`) clause the deterministic control `ρ² M_u^{-1}`), `GoodSetPT` (the good set holds per
time) and `MeasurableGoodSet`.

Results: `goodSetPT : GoodSetPT` (from `GbEXPHypV3`, `Step1LoopPT`, `Step1WeakLawPT`) and
`measurableGoodSet : MeasurableGoodSet`.

Paper: arXiv:2503.07606, `lem_dec_calE`, (`lRB1`), (`Gtmwc`), (`con_st_ind`), `lem_GbEXP`,
(`GijGEX`), (`GiiGEX`), (`asGMc`), (`GavLGEX`).

For `d = 2` the index sets are `Z2 L`, `Idx L W`, `BlockIndex L W`, and the union bound runs over
at most `N⁹` labels per time, `N = (W L)²`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

section GoodSet

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The good set `G(u)` at level `Λ`** (the single-time inputs of `lem_dec_calE`): Hermitian;
(`lRB1`) at `k = 3, 4, 6`; (`Gtmwc`); (`GijGEX`) off the diagonal, swapped pair; (`GiiGEX`);
(`GavLGEX`) with the deterministic control `ρ² M_u^{-1}`, `ρ = ℓ_u/ℓ_s` (`lRB1` at `k = 2`).
The set is used with `Λ = N^ε`. -/
def goodSet (E s u Λ : ℝ) : Set (Matrix (Idx L W) (Idx L W) ℂ) :=
  {M | M.IsHermitian ∧
    (∀ k ∈ ({3, 4, 6} : Finset ℕ), ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      loopAbs L W E u M σ a ≤
        Λ * (ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) ∧
    (∀ i j : Idx L W, llErrMat L W E u M i j ≤ Λ * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4)) ∧
    (∀ p q : BlockIndex L W, p ≠ q →
      ‖greenBlk L W E u M true p q‖ ^ 2 ≤ Λ * gexRHS L W E u M q.1 p.1) ∧
    (∀ p : BlockIndex L W,
      ‖greenBlk L W E u M true p p - spectralM E‖ ^ 2 ≤ Λ * maxLoopPM L W E u M) ∧
    (∀ a : Z2 L, ‖avgErr L W E u M true a‖ ≤
      Λ * (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹)}

end GoodSet

/-- **The good set holds per time at level `N^ε`**: from (`lRB1`) and (`Gtmwc`) per time over
`[s,t]` (Step 1) and `lem_GbEXP` as `GbEXPHypV3`, under the bulk, bandwidth, range and
(`con_st_ind`) conditions of `lem:main_ind`. -/
def GoodSetPT : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ), 0 < κ → 0 < 𝔠 → 0 < δ →
    RBM.Green.GbEXPHypV3 d κ 𝔠 δ → RBM.Ind.SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
    CondStInd d E s t → (∀ n, |E n| < 2 - κ) →
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    ∀ ε > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
          goodSet (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε)} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **Measurability of `G(u)`.** -/
def MeasurableGoodSet : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E s u Λ : ℝ), |E| < 2 → u < 1 →
    MeasurableSet (goodSet L W E s u Λ)

/-! ## Measurability of `goodSet` -/

section MeasurableHelpers

private theorem goodSet_measurable_matrix_inv_apply {n : Type*} [Fintype n] [DecidableEq n]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix n n ℂ} (hM : Measurable M) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

set_option linter.unusedFintypeInType false in
private theorem goodSet_measurable_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) : Measurable fun M : Matrix n n ℂ => M - z • (1 : Matrix n n ℂ) :=
  (continuous_id.sub continuous_const).measurable

private theorem goodSet_measurable_green {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (i j : n) : Measurable fun M : Matrix n n ℂ => green M z i j :=
  goodSet_measurable_matrix_inv_apply (goodSet_measurable_sub_smul_one z) i j

private theorem goodSet_measurable_Gsig {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (σ : Bool) (i j : n) : Measurable fun M : Matrix n n ℂ => Gsig M z σ i j := by
  cases σ
  · simpa [Gsig] using goodSet_measurable_green ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using goodSet_measurable_green z i j

private theorem goodSet_measurable_mul {ι : Type*} [Fintype ι]
    {Θ : Type*} [MeasurableSpace Θ] {A C : Θ → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hC : ∀ i j, Measurable fun x => C x i j)
    (i j : ι) : Measurable fun x => (A x * C x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem goodSet_measurable_gloopProd (z : ℂ) (I : LoopIdx (Z2 L)) (i j : BlockIndex L W) :
    Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloopProd L W H z I i j := by
  suffices h : ∀ l : List (Bool × Z2 L), ∀ i j : BlockIndex L W,
      Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => (l.foldr
        (fun (p : Bool × Z2 L) (Acc : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =>
          Gsig H z p.1 * Eblk L W p.2 * Acc)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) i j by
    simpa [gloopProd] using h (I.σ.zip I.a) i j
  intro l
  induction l with
  | nil => intro i j; simp
  | cons p l ih =>
      intro i j
      simp only [List.foldr_cons]
      refine goodSet_measurable_mul ?_ (fun a b => ih a b) i j
      intro a b
      refine goodSet_measurable_mul (fun c e => goodSet_measurable_Gsig z p.1 c e)
        (C := fun _ => Eblk L W p.2) (fun _ _ => measurable_const) a b

omit [NeZero W] in
private theorem goodSet_measurable_gloop (z : ℂ) (I : LoopIdx (Z2 L)) :
    Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloop L W H z I := by
  have h : ∀ H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ, gloop L W H z I
      = ∑ i : BlockIndex L W, gloopProd L W H z I i i := fun _ => rfl
  simp only [h]
  exact Finset.measurable_sum _ fun i _ => goodSet_measurable_gloopProd L W z I i i

private theorem goodSet_measurable_blockMat :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => blockMat M :=
  (continuous_id.matrix_submatrix _ _).measurable

private theorem goodSet_measurable_loopPM (E u : ℝ) (a b : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => loopPM L W E u M a b :=
  (goodSet_measurable_gloop L W (spectralZ E u) (pmLoop a b)).comp
    (goodSet_measurable_blockMat L W)

private theorem goodSet_measurable_loopAbs (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => loopAbs L W E u M σ a :=
  ((goodSet_measurable_gloop L W (spectralZ E u) (loopOf σ a)).comp
    (goodSet_measurable_blockMat L W)).norm

private theorem goodSet_measurable_llErrMat (E u : ℝ) (i j : Idx L W) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => llErrMat L W E u M i j :=
  ((goodSet_measurable_matrix_inv_apply
    (goodSet_measurable_sub_smul_one (spectralZ E u)) i j).sub measurable_const).norm

private theorem goodSet_measurable_greenBlk (E u : ℝ) (σ : Bool) (p q : BlockIndex L W) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => greenBlk L W E u M σ p q :=
  (goodSet_measurable_Gsig (spectralZ E u) σ p q).comp (goodSet_measurable_blockMat L W)

private theorem goodSet_measurable_avgErr (E u : ℝ) (σ : Bool) (a : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => avgErr L W E u M σ a := by
  simp only [avgErr, Matrix.trace, Matrix.diag_apply]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine goodSet_measurable_mul (A := fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      greenBlk L W E u M σ - KLoop.mSig E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ))
    (C := fun _ => Eblk L W a) ?_ (fun _ _ => measurable_const) i i
  intro p q
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (goodSet_measurable_greenBlk L W E u σ p q).sub measurable_const

private theorem goodSet_measurable_maxLoopPM (E u : ℝ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => maxLoopPM L W E u M := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) => ‖loopPM L W E u M p.1 p.2‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ =>
      (goodSet_measurable_loopPM L W E u p.1 p.2).norm
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => maxLoopPM L W E u M) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) => ‖loopPM L W E u M p.1 p.2‖) := by
    funext M
    simp only [maxLoopPM, Finset.sup'_apply]
  rw [heq]
  exact hsup

private theorem goodSet_measurable_gexRHS (E u : ℝ) (a b : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => gexRHS L W E u M a b := by
  unfold gexRHS
  refine Measurable.add ?_ measurable_const
  refine Finset.measurable_sum _ fun a' _ => Finset.measurable_sum _ fun b' _ => ?_
  exact Measurable.ite (MeasurableSet.const _) (goodSet_measurable_loopPM L W E u a' b').norm
    measurable_const

end MeasurableHelpers

private theorem goodSet_measurableSet_ball {α : Type*} [MeasurableSpace α] (S : Finset ℕ)
    {p : ℕ → α → Prop} (h : ∀ k ∈ S, MeasurableSet {x | p k x}) :
    MeasurableSet {x | ∀ k ∈ S, p k x} := by
  have e : {x | ∀ k ∈ S, p k x} = ⋂ k ∈ (S : Set ℕ), {x | p k x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.biInter S.countable_toSet fun k hk => h k hk

private theorem goodSet_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

/-- **`measurableGoodSet`**: `G(u)` is a measurable set of matrices (a finite intersection of the
closed Hermitian set and sets `{M | f M ≤ g}` with `f` measurable in `M`). -/
theorem measurableGoodSet : MeasurableGoodSet := by
  intro L W _ _ E s u Λ _ _
  have hH : MeasurableSet {M : Matrix (Idx L W) (Idx L W) ℂ | M.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  unfold goodSet
  simp only [Set.ofPred_and]
  refine hH.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ ?_))))
  · refine goodSet_measurableSet_ball _ fun k _ => goodSet_measurableSet_forall fun σ =>
      goodSet_measurableSet_forall fun a => ?_
    exact measurableSet_le (goodSet_measurable_loopAbs L W E u σ a) measurable_const
  · refine goodSet_measurableSet_forall fun i => goodSet_measurableSet_forall fun j => ?_
    exact measurableSet_le (goodSet_measurable_llErrMat L W E u i j) measurable_const
  · refine goodSet_measurableSet_forall fun p => goodSet_measurableSet_forall fun q => ?_
    by_cases hpq : p = q
    · simp [hpq]
    · simp only [ne_eq, hpq, not_false_eq_true, forall_true_left]
      exact measurableSet_le ((goodSet_measurable_greenBlk L W E u true p q).norm.pow_const 2)
        (measurable_const.mul (goodSet_measurable_gexRHS L W E u q.1 p.1))
  · refine goodSet_measurableSet_forall fun p => ?_
    exact measurableSet_le
      (((goodSet_measurable_greenBlk L W E u true p p).sub_const (spectralM E)).norm.pow_const 2)
      (measurable_const.mul (goodSet_measurable_maxLoopPM L W E u))
  · refine goodSet_measurableSet_forall fun a => ?_
    exact measurableSet_le (goodSet_measurable_avgErr L W E u true a).norm measurable_const


/-! ## The good set holds per time -/

section HoldsPerTime

open RBM.Green

/-- The failure set of a matrix property `c` at the time `u` and size index `n`. -/
private def goodSetFail (d : Sizes) (n : ℕ) (u : ℝ)
    (c : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Prop) : Set (Sizes.SeqΩ d) :=
  {ω | ¬ c (Sizes.seqHflow d n u ω)}

section Clauses

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Clause 2 of `goodSet` at the loop length `k`. -/
private def goodSetLoopK (E s u Λ : ℝ) (k : ℕ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
    loopAbs L W E u M σ a ≤
      Λ * (ellT L u / ellT L s) ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)

/-- Clause 3 of `goodSet`. -/
private def goodSetWeak (E u Λ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∀ i j : Idx L W, llErrMat L W E u M i j ≤ Λ * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 4)

/-- Clause 4 of `goodSet`. -/
private def goodSetGij (E u Λ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∀ p q : BlockIndex L W, p ≠ q →
    ‖greenBlk L W E u M true p q‖ ^ 2 ≤ Λ * gexRHS L W E u M q.1 p.1

/-- Clause 5 of `goodSet`. -/
private def goodSetGii (E u Λ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∀ p : BlockIndex L W,
    ‖greenBlk L W E u M true p p - spectralM E‖ ^ 2 ≤ Λ * maxLoopPM L W E u M

/-- Clause 6 of `goodSet`. -/
private def goodSetGav (E s u Λ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∀ a : Z2 L, ‖avgErr L W E u M true a‖ ≤
    Λ * (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹

private theorem goodSet_mem_iff (E s u Λ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    M ∈ goodSet L W E s u Λ ↔ M.IsHermitian ∧
      (∀ k ∈ ({3, 4, 6} : Finset ℕ), goodSetLoopK L W E s u Λ k M) ∧ goodSetWeak L W E u Λ M ∧
      goodSetGij L W E u Λ M ∧ goodSetGii L W E u Λ M ∧ goodSetGav L W E s u Λ M :=
  Iff.rfl

end Clauses

/-! ### Generic measure and per-time lemmas -/

/-- A per-time domination transfers along a map of labels, to a smaller left side and a larger
control (the control comparison may hold only eventually). -/
private theorem goodSet_perTimeDomAt_of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, U' l → Ω → ℝ}
    (f : ∀ l, U' l → U l) (h : PerTimeDomAt P size ξ ζ)
    (hξ : ∀ l u ω, ξ' l u ω ≤ ξ l (f l u) ω)
    (hζ : ∀ᶠ l : ℕ in atTop, ∀ u ω, ζ l (f l u) ω ≤ ζ' l u ω) :
    PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hζ] with l hl hζl u
  refine le_trans (measure_mono ?_) (hl (f l u))
  intro ω hω
  have hω' : (size l : ℝ) ^ τ * ζ' l u ω < ξ' l u ω := hω
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hζl u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) τ)) (lt_of_lt_of_le hω' (hξ l u ω))

private theorem goodSet_measure_iUnion_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (S : ι → Set Ω) (x : ℝ≥0∞) (h : ∀ i, P (S i) ≤ x) :
    P (⋃ i, S i) ≤ (Fintype.card ι : ℝ≥0∞) * x :=
  calc P (⋃ i, S i) ≤ ∑ i, P (S i) := measure_iUnion_fintype_le P S
    _ ≤ ∑ _i : ι, x := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : ℝ≥0∞) * x := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- From a per-time domination at labels `(t, v)` with `v` in a finite set: an event `F l t` all of
whose points violate the domination at some `v` has probability at most `#V · size^{-(D+9)}`. -/
private theorem goodSet_fail_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {T V : ℕ → Type*} [∀ l, Fintype (V l)] {ξ ζ : ∀ l, T l × V l → Ω → ℝ}
    (h : PerTimeDomAt P size ξ ζ) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) (F : ∀ l, T l → Set Ω)
    (hF : ∀ l t ω, ω ∈ F l t → ∃ v : V l, (size l : ℝ) ^ ε * ζ l (t, v) ω < ξ l (t, v) ω) :
    ∀ᶠ l : ℕ in atTop, ∀ t : T l, P (F l t) ≤
      (Fintype.card (V l) : ℝ≥0∞) * ENNReal.ofReal ((size l : ℝ) ^ (-(D + 9))) := by
  filter_upwards [h ε hε (D + 9) (by linarith)] with l hl t
  calc P (F l t) ≤ P (⋃ v : V l, {ω | (size l : ℝ) ^ ε * ζ l (t, v) ω < ξ l (t, v) ω}) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨v, hv⟩ := hF l t ω hω
        exact Set.mem_iUnion.2 ⟨v, hv⟩
    _ ≤ _ := goodSet_measure_iUnion_le P _ _ fun v => hl (t, v)

private theorem goodSet_final {x : ℝ} (hx : 0 < x) (D : ℝ) (C : ℕ) (hC : (C : ℝ) ≤ x ^ 9) :
    (C : ℝ≥0∞) * ENNReal.ofReal (x ^ (-(D + 9))) ≤ ENNReal.ofReal (x ^ (-D)) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (C : ℝ) * x ^ (-(D + 9)) ≤ x ^ 9 * x ^ (-(D + 9)) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx.le _)
    _ = x ^ (-D) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hx]
        congr 1; push_cast; ring

private theorem goodSet_rpow_pow {x : ℝ} (hx : 0 ≤ x) (e : ℝ) (k : ℕ) :
    (x ^ e) ^ k = x ^ (e * k) := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

/-! ### Cardinalities and size facts -/

private theorem goodSet_size_facts (d : Sizes) (n : ℕ) :
    (9 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ ((d.L n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧
      ((d.W n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have hL : (3 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast d.three_le_L n
  have hW : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hs : ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
    simp [Sizes.size]
  rw [hs, mul_pow]
  have hw2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW
  have ha2 : (9 : ℝ) ≤ (d.L n : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith


/-! ### The scale bounds (exponent chain of (`asGMc`) and of `Ψ`) -/

/-- `Im m^{(E)} ≥ √(κ(4-κ))/2` for `|E| < 2 - κ`. -/
private theorem goodSet_im_lower {κ E : ℝ} (hE : |E| < 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have h2 : 0 < 2 - κ := lt_of_le_of_lt (abs_nonneg _) hE
  have h3 := abs_le.1 hE.le
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by nlinarith [h3.1, h3.2]
  have := Real.sqrt_le_sqrt (show κ * (4 - κ) ≤ 4 - E ^ 2 by nlinarith [hE2])
  linarith

/-- Eventually, for every `u ≤ t n`: `W^q ≤ M_u`, `q = min(2𝔠, δ)` (`M_u ≥ M_t ≥ Im m · N^q`
by `scaleM_etaT_of_range` and `scaleM_anti_ratio`, `Im m ≥ √(κ(4-κ))/2`, `W² ≤ N`). -/
private theorem goodSet_scale_lower {d : Sizes} {κ 𝔠 δ : ℝ} {E t : ℕ → ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (hδ : 0 < δ) (hE : ∀ n, |E n| < 2 - κ) (ht : ∀ n, t n < 1)
    (hN : RBM.Ind.SizeTendsto d) (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      (d.W n : ℝ) ^ (min (2 * 𝔠) δ) ≤ scaleM (d.L n) (d.W n) (E n) u := by
  set q := min (2 * 𝔠) δ with hq
  have hq0 : 0 < q := lt_min (by linarith) hδ
  set m₀ := Real.sqrt (κ * (4 - κ)) / 2 with hm₀
  have hκ2 : κ < 2 := by
    have := lt_of_le_of_lt (abs_nonneg (E 0)) (hE 0); linarith
  have hm₀0 : 0 < m₀ := by
    rw [hm₀]
    exact half_pos (Real.sqrt_pos.2 (mul_pos hκ (by linarith)))
  have hlim : ∀ᶠ n : ℕ in atTop, 1 ≤ m₀ * ((d.size n : ℕ) : ℝ) ^ (q / 2) :=
    (((tendsto_rpow_atTop (half_pos hq0)).comp hN).const_mul_atTop hm₀0).eventually_ge_atTop 1
  filter_upwards [hW, hR, hlim] with n hWn hRn hlimn u hu
  obtain ⟨hN9, hLN, hWN⟩ := goodSet_size_facts d n
  have hx0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWpos : 1 ≤ d.W n := d.W_pos n
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hMt : (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ q ≤
      scaleM (d.L n) (d.W n) (E n) (t n) :=
    (scaleM_etaT_of_range hLpos hWpos hE2 h𝔠 hδ (ht n) hWn hRn).1
  have hMu : scaleM (d.L n) (d.W n) (E n) (t n) ≤ scaleM (d.L n) (d.W n) (E n) u :=
    (scaleM_anti_ratio hLpos hE2 hu (ht n)).1
  have him : m₀ ≤ (spectralM (E n)).im := goodSet_im_lower (hE n)
  have hWq : (d.W n : ℝ) ^ q ≤ ((d.size n : ℕ) : ℝ) ^ (q / 2) := by
    have h1 : ((d.W n : ℝ) ^ 2) ^ (q / 2) ≤ ((d.size n : ℕ) : ℝ) ^ (q / 2) :=
      Real.rpow_le_rpow (by positivity) hWN (by linarith)
    have h2 : ((d.W n : ℝ) ^ 2) ^ (q / 2) = (d.W n : ℝ) ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    rwa [h2] at h1
  have hxq : ((d.size n : ℕ) : ℝ) ^ q =
      ((d.size n : ℕ) : ℝ) ^ (q / 2) * ((d.size n : ℕ) : ℝ) ^ (q / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hpos : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (q / 2) := Real.rpow_nonneg hx0.le _
  calc (d.W n : ℝ) ^ q ≤ ((d.size n : ℕ) : ℝ) ^ (q / 2) := hWq
    _ ≤ m₀ * ((d.size n : ℕ) : ℝ) ^ (q / 2) * ((d.size n : ℕ) : ℝ) ^ (q / 2) := by
        nlinarith
    _ = m₀ * ((d.size n : ℕ) : ℝ) ^ q := by rw [hxq]; ring
    _ ≤ (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ q :=
        mul_le_mul_of_nonneg_right him (Real.rpow_nonneg hx0.le q)
    _ ≤ _ := hMt.trans hMu

/-- (`asGMc`) per time over `[s,t]` at the exponent `q/4`, `q = min(2𝔠, δ)`:
`M_u^{-1/4} ≤ W^{-q/4}` for `u ≤ t`, from (`Gtmwc`). -/
private theorem goodSet_asGMc {d : Sizes} {κ 𝔠 δ : ℝ} {E s t : ℕ → ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (hδ : 0 < δ) (hE : ∀ n, |E n| < 2 - κ) (ht : ∀ n, t n < 1)
    (hN : RBM.Ind.SizeTendsto d) (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t)
    (hWeak : Step1WeakLawPT d E s t) : AsGMcPT d E s t (min (2 * 𝔠) δ / 4) := by
  refine goodSet_perTimeDomAt_of_le (fun n p => p) hWeak (fun _ _ _ => le_rfl) ?_
  filter_upwards [goodSet_scale_lower hκ h𝔠 hδ hE ht hN hW hR] with n hn p ω
  set q := min (2 * 𝔠) δ with hq
  have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWpos : 1 ≤ d.W n := d.W_pos n
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht n)
  have hM := scaleM_pos hLpos hWpos hE2 hu1
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast hWpos
  have hle := hn p.1 p.1.2.2
  have hinv : (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ≤ (d.W n : ℝ) ^ (-q) := by
    rw [Real.rpow_neg hW0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hW0 q) hle
  calc (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ ((1 : ℝ) / 4)
      ≤ ((d.W n : ℝ) ^ (-q)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (inv_nonneg.2 hM.le) hinv (by norm_num)
    _ = (d.W n : ℝ) ^ (-(q / 4)) := by
        rw [← Real.rpow_mul hW0.le]; congr 1; ring

/-- The identity `ρ² M_u^{-1} = ((1-s)/(1-u)) M_s^{-1}` (`ρ = ℓ_u/ℓ_s`). -/
private theorem goodSet_rho_identity {L W : ℕ} {E s u : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : |E| < 2) (hs : s < 1) (hu : u < 1) :
    (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ = ((1 - s) / (1 - u)) * (scaleM L W E s)⁻¹ := by
  have hlu := (ellT_pos_le hL hu).1
  have hls := (ellT_pos_le hL hs).1
  have hm := spectralM_im_pos hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < 1 - u := by linarith
  unfold scaleM etaT
  field_simp

/-- Eventually, for `s n ≤ u ≤ t n`: `ρ² M_u^{-1} ≤ (N^{-a})²` with `a = 𝔠 q / 4`, `q = min(2𝔠, δ)`
(chain `ρ²M_u^{-1} = ((1-s)/(1-u)) M_s^{-1} ≤ M_s^{-29/30}` by (`con_st_ind`), `M_s ≥ W^q ≥ N^{𝔠 q}`;
written with 30th powers). -/
private theorem goodSet_psi_bound {d : Sizes} {κ 𝔠 δ : ℝ} {E s t : ℕ → ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (hδ : 0 < δ) (hE : ∀ n, |E n| < 2 - κ) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1) (hN : RBM.Ind.SizeTendsto d)
    (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t) (hCond : CondStInd d E s t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      (ellT (d.L n) u / ellT (d.L n) (s n)) ^ 2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤
        (((d.size n : ℕ) : ℝ) ^ (-(𝔠 * min (2 * 𝔠) δ / 4))) ^ 2 := by
  set q := min (2 * 𝔠) δ with hq
  have hq0 : 0 < q := lt_min (by linarith) hδ
  filter_upwards [goodSet_scale_lower hκ h𝔠 hδ hE ht hN hW hR, hW, hCond] with n hn hWn hCn u hsu hut
  obtain ⟨hN9, hLN, hWN⟩ := goodSet_size_facts d n
  set x : ℝ := ((d.size n : ℕ) : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWpos : 1 ≤ d.W n := d.W_pos n
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast hWpos
  have hs1 : s n < 1 := (hst n).trans_lt (ht n)
  have hu1 : u < 1 := hut.trans_lt (ht n)
  have hxs : 0 < 1 - s n := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hxt : 0 < 1 - t n := by linarith [ht n]
  have hMs := scaleM_pos hLpos hWpos hE2 hs1
  -- `y = M_s⁻¹ ≤ x^(-𝔠 q)`
  set y : ℝ := (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ with hydef
  have hy0 : 0 < y := inv_pos.2 hMs
  have hWq := hn (s n) (hst n)
  have hcq : (x ^ 𝔠) ^ q ≤ (d.W n : ℝ) ^ q :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hWn hq0.le
  have hy1 : y ≤ x ^ (-(𝔠 * q)) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_mul hx0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx0 _) _) (hcq.trans hWq)
  -- `w = ρ² M_u⁻¹`
  rw [goodSet_rho_identity hLpos hWpos hE2 hs1 hu1]
  set w : ℝ := (1 - s n) / (1 - u) * y with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hr : y ≤ ((1 - t n) / (1 - s n)) ^ 30 := hCn
  have hw1 : (1 - s n) / (1 - u) ≤ (1 - s n) / (1 - t n) :=
    div_le_div_of_nonneg_left hxs.le hxt (by linarith)
  have hw2 : w ≤ (1 - s n) / (1 - t n) * y := mul_le_mul_of_nonneg_right hw1 hy0.le
  have hr' : ((1 - s n) / (1 - t n)) ^ 30 ≤ y⁻¹ := by
    have : ((1 - s n) / (1 - t n)) ^ 30 = (((1 - t n) / (1 - s n)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [this]
    exact inv_anti₀ hy0 hr
  have hw30 : w ^ 30 ≤ y ^ 29 := by
    calc w ^ 30 ≤ ((1 - s n) / (1 - t n) * y) ^ 30 := pow_le_pow_left₀ hw0 hw2 30
      _ = ((1 - s n) / (1 - t n)) ^ 30 * y ^ 30 := mul_pow _ _ _
      _ ≤ y⁻¹ * y ^ 30 := mul_le_mul_of_nonneg_right hr' (by positivity)
      _ = y ^ 29 := by field_simp
  have hy29 : y ^ 29 ≤ (x ^ (-(𝔠 * q))) ^ 29 := pow_le_pow_left₀ hy0.le hy1 29
  have hexp : (x ^ (-(𝔠 * q))) ^ 29 ≤ ((x ^ (-(𝔠 * q / 4))) ^ 2) ^ 30 := by
    rw [goodSet_rpow_pow hx0.le, ← pow_mul, goodSet_rpow_pow hx0.le]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    have : 0 < 𝔠 * q := mul_pos h𝔠 hq0
    push_cast
    nlinarith
  have hz0 : 0 ≤ (x ^ (-(𝔠 * q / 4))) ^ 2 := by positivity
  exact (pow_le_pow_iff_left₀ hw0 hz0 (by norm_num : (30 : ℕ) ≠ 0)).1
    (hw30.trans (hy29.trans hexp))


/-! ### The five clause failures at level `N^ε`, per time -/

private theorem goodSet_loopK_fail {d : Sizes} {E s t : ℕ → ℝ} (hLoop : Step1LoopPT d E s t)
    (k : ℕ) (hk : 1 ≤ k) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d (goodSetFail d n u
          (goodSetLoopK (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε) k)) ≤
        (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 9))) :=
  goodSet_fail_le (T := fun n => TimeIcc s t n)
    (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n))) (hLoop k hk) hε hD
    (fun n u => goodSetFail d n u
      (goodSetLoopK (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε) k))
    (by
      intro n u ω hω
      simp only [goodSetFail, goodSetLoopK, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨σ, a, h⟩ := hω
      exact ⟨(σ, a), by rw [← mul_assoc]; exact h⟩)

private theorem goodSet_weak_fail {d : Sizes} {E s t : ℕ → ℝ} (hWeak : Step1WeakLawPT d E s t)
    {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d (goodSetFail d n u
          (goodSetWeak (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε))) ≤
        (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 9))) :=
  goodSet_fail_le (T := fun n => TimeIcc s t n)
    (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) hWeak hε hD
    (fun n u => goodSetFail d n u
      (goodSetWeak (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)))
    (by
      intro n u ω hω
      simp only [goodSetFail, goodSetWeak, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨i, j, h⟩ := hω
      exact ⟨(i, j), h⟩)

private theorem goodSet_gij_fail {d : Sizes} {E s t : ℕ → ℝ} (hGij : GijGEXPTSwap d E s t)
    {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d (goodSetFail d n u
          (goodSetGij (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε))) ≤
        (Fintype.card (BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 9))) :=
  goodSet_fail_le (T := fun n => TimeIcc s t n)
    (V := fun n => BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) hGij hε hD
    (fun n u => goodSetFail d n u
      (goodSetGij (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)))
    (by
      intro n u ω hω
      simp only [goodSetFail, goodSetGij, Set.mem_ofPred_eq] at hω
      push Not at hω
      obtain ⟨p, q, hpq, h⟩ := hω
      refine ⟨(p, q), ?_⟩
      change _ < (if p = q then 0 else _)
      simp only [hpq, ↓reduceIte]
      exact h)

private theorem goodSet_gii_fail {d : Sizes} {E s t : ℕ → ℝ} (hGii : GiiGEXPT d E s t)
    {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d (goodSetFail d n u
          (goodSetGii (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε))) ≤
        (Fintype.card (BlockIndex (d.L n) (d.W n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 9))) :=
  goodSet_fail_le (T := fun n => TimeIcc s t n)
    (V := fun n => BlockIndex (d.L n) (d.W n)) hGii hε hD
    (fun n u => goodSetFail d n u
      (goodSetGii (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)))
    (by
      intro n u ω hω
      simp only [goodSetFail, goodSetGii, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨p, h⟩ := hω
      exact ⟨p, h⟩)

private theorem goodSet_gav_fail {d : Sizes} {E s t : ℕ → ℝ}
    (hGav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (ellT (d.L n) p.1 / ellT (d.L n) (s n)) ^ 2 *
        (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹))
    {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d (goodSetFail d n u
          (goodSetGav (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε))) ≤
        (Fintype.card (Z2 (d.L n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 9))) :=
  goodSet_fail_le (T := fun n => TimeIcc s t n) (V := fun n => Z2 (d.L n)) hGav hε hD
    (fun n u => goodSetFail d n u
      (goodSetGav (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε)))
    (by
      intro n u ω hω
      simp only [goodSetFail, goodSetGav, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨a, h⟩ := hω
      exact ⟨a, by rw [← mul_assoc]; exact h⟩)


/-! ### The (`GavLGEX`) clause per time -/

/-- **Clause 6 per time over `[s,t]`.**  For each time sequence `u n ∈ [s n, t n]`: `Ψ n =
√(ρ² M_u^{-1})`, `Ψ ≤ N^{-a}` eventually (`goodSet_psi_bound`), `LoopDetSeq d E u Ψ` from
`Step1LoopPT` at `k = 2` (`perSeq_of_perTime_timeIcc`, `loopOf ![true, false] ![a, b] = pmLoop a b`),
`AsGMcSeq` from (`Gtmwc`); third component of `GbEXPHypV3` at `u`; then lift with
`perTime_timeIcc_of_forall_seq`. -/
private theorem goodSet_avgErr {d : Sizes} {κ 𝔠 δ : ℝ} {E s t : ℕ → ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (hδ : 0 < δ) (hV3 : GbEXPHypV3 d κ 𝔠 δ) (hN : RBM.Ind.SizeTendsto d)
    (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t) (hCond : CondStInd d E s t)
    (hE : ∀ n, |E n| < 2 - κ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hLoop : Step1LoopPT d E s t) (hWeak : Step1WeakLawPT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (ellT (d.L n) p.1 / ellT (d.L n) (s n)) ^ 2 *
        (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  set q := min (2 * 𝔠) δ with hq
  have hq0 : 0 < q := lt_min (by linarith) hδ
  have hAs := goodSet_asGMc hκ h𝔠 hδ hE ht hN hW hR hWeak
  refine perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst (V := fun n => Z2 (d.L n))
    (fun n => ⟨0⟩)
    (fun n v a ω => ‖avgErr (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) true a‖)
    (fun n v a ω => (ellT (d.L n) v / ellT (d.L n) (s n)) ^ 2 *
      (scaleM (d.L n) (d.W n) (E n) v)⁻¹) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hu1 : ∀ n, u n < 1 := fun n => (hu n).2.trans_lt (ht n)
  have hRu : RangeCond d δ u := rangeCond_mono d hR fun n => (hu n).2
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n = Real.sqrt ((ellT (d.L n) (u n) /
      ellT (d.L n) (s n)) ^ 2 * (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹) := ⟨_, fun _ => rfl⟩
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => by rw [hΨ]; exact Real.sqrt_nonneg _
  have hΨsq : ∀ n, Ψ n ^ 2 = (ellT (d.L n) (u n) / ellT (d.L n) (s n)) ^ 2 *
      (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := by
    intro n
    have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
    have hE2 : |E n| < 2 := by linarith [hE n]
    rw [hΨ]
    exact Real.sq_sqrt (mul_nonneg (sq_nonneg _)
      (inv_nonneg.2 (scaleM_pos hLpos (d.W_pos n) hE2 (hu1 n)).le))
  have ha : 0 < 𝔠 * q / 4 := by positivity
  have hΨN : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(𝔠 * q / 4)) := by
    filter_upwards [goodSet_psi_bound hκ h𝔠 hδ hE hst ht hN hW hR hCond] with n hn
    rw [hΨ]
    exact Real.sqrt_le_iff.2 ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, hn (u n) (hu n).1 (hu n).2⟩
  have hLoopDet : LoopDetSeq d E u Ψ := by
    have h2 := perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
      (fun n v q ω => loopAbs (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (ellT (d.L n) v / ellT (d.L n) (s n)) ^ (2 * (2 - 1)) *
        (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ (2 - 1))
      (hLoop 2 (by norm_num)) u hu
    refine goodSet_perTimeDomAt_of_le
      (fun n (p : Unit × Z2 (d.L n) × Z2 (d.L n)) =>
        (p.1, ((![true, false] : Fin 2 → Bool), (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))))
      h2 (fun n p ω => le_rfl) (Filter.Eventually.of_forall fun n p ω => ?_)
    rw [hΨsq n]
    norm_num
  have hAsu : AsGMcSeq d E u (min (2 * 𝔠) δ / 4) :=
    perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n _ _ _ => (d.W n : ℝ) ^ (-(min (2 * 𝔠) δ / 4))) hAs u hu
  have h3 := ((hV3 hN hW E u hE hu0 hu1 hRu (min (2 * 𝔠) δ / 4) (by positivity)).2.2 hAsu).2.2
    Ψ (𝔠 * q / 4) ha hΨ0 hΨN hLoopDet
  exact goodSet_perTimeDomAt_of_le (fun n p => p) h3 (fun _ _ _ => le_rfl)
    (Filter.Eventually.of_forall fun n p ω => (hΨsq n).le)

/-! ### Assembly -/

private theorem goodSet_card_loop (L k : ℕ) [NeZero L] :
    Fintype.card ((Fin k → Bool) × (Fin k → Z2 L)) = 2 ^ k * (L * L) ^ k := by
  simp [Fintype.card_prod, ZMod.card]

private theorem goodSet_card_idx (L W : ℕ) [NeZero L] [NeZero W] :
    Fintype.card (Idx L W) = W * L * (W * L) := by
  simp [Idx, Fintype.card_prod, ZMod.card]

private theorem goodSet_card_block (L W : ℕ) [NeZero L] [NeZero W] :
    Fintype.card (BlockIndex L W) = L * L * (W * W) := by
  simp [BlockIndex, Fintype.card_prod, ZMod.card]

private theorem goodSet_card_z2 (L : ℕ) [NeZero L] : Fintype.card (Z2 L) = L * L := by
  simp [Fintype.card_prod, ZMod.card]


private theorem goodSet_size_cast (d : Sizes) (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
  simp [Sizes.size]

/-- The label count: `Σ ≤ N⁹` for `N ≥ 9` and `A = L² ≤ N` (`192 N⁶ + 2N² + 2N ≤ N⁹`). -/
private theorem goodSet_count_le {x A : ℝ} (hx : 9 ≤ x) (hA0 : 0 ≤ A) (hA : A ≤ x) :
    8 * A ^ 3 + 16 * A ^ 4 + 64 * A ^ 6 + x * x + x * x + x + A ≤ x ^ 9 := by
  have hx1 : 1 ≤ x := by linarith
  have h3 : A ^ 3 ≤ x ^ 6 :=
    (pow_le_pow_left₀ hA0 hA 3).trans (pow_le_pow_right₀ hx1 (by norm_num))
  have h4 : A ^ 4 ≤ x ^ 6 :=
    (pow_le_pow_left₀ hA0 hA 4).trans (pow_le_pow_right₀ hx1 (by norm_num))
  have h6 : A ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ hA0 hA 6
  have h2 : x * x ≤ x ^ 6 := by
    rw [← pow_two]; exact pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : x ≤ x ^ 6 := by
    simpa using pow_le_pow_right₀ hx1 (show 1 ≤ 6 by norm_num)
  have hA6 : A ≤ x ^ 6 := hA.trans h1
  have h9 : 92 * x ^ 6 ≤ x ^ 9 := by
    have h92 : (92 : ℝ) ≤ x ^ 3 :=
      calc (92 : ℝ) ≤ 9 ^ 3 := by norm_num
        _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
    calc 92 * x ^ 6 ≤ x ^ 3 * x ^ 6 :=
          mul_le_mul_of_nonneg_right h92 (by positivity)
      _ = x ^ 9 := by ring
  linarith

private theorem goodSet_union7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B C D E F G : Set Ω) :
    P (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ≤ P A + P B + P C + P D + P E + P F + P G := by
  calc P (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ≤ P (A ∪ B ∪ C ∪ D ∪ E ∪ F) + P G := measure_union_le _ _
    _ ≤ P (A ∪ B ∪ C ∪ D ∪ E) + P F + P G := by
        gcongr; exact measure_union_le _ _
    _ ≤ P (A ∪ B ∪ C ∪ D) + P E + P F + P G := by
        gcongr; exact measure_union_le _ _
    _ ≤ P (A ∪ B ∪ C) + P D + P E + P F + P G := by
        gcongr; exact measure_union_le _ _
    _ ≤ P (A ∪ B) + P C + P D + P E + P F + P G := by
        gcongr; exact measure_union_le _ _
    _ ≤ P A + P B + P C + P D + P E + P F + P G := by
        gcongr; exact measure_union_le _ _

/-- **`goodSetPT`**: the good set `G(u)` holds per time over `[s,t]` at level `N^ε`.
Clauses 2–3 from `Step1LoopPT`, `Step1WeakLawPT`; clauses 4–5 from
`gijGEXPTSwap_giiGEXPT_of_V3` (via (`asGMc`) from (`Gtmwc`)); clause 6 from the third component of
`GbEXPHypV3` (`goodSet_avgErr`); union over at most `N⁹` labels with `D + 9` each. -/
theorem goodSetPT : GoodSetPT := by
  intro d κ 𝔠 δ E s t hκ h𝔠 hδ hV3 hN hW hR hCond hE hs hst ht hLoop hWeak ε hε D hD
  have hq0 : 0 < min (2 * 𝔠) δ := lt_min (by linarith) hδ
  have hAs := goodSet_asGMc hκ h𝔠 hδ hE ht hN hW hR hWeak
  obtain ⟨hGij, hGii⟩ := gijGEXPTSwap_giiGEXPT_of_V3 d hV3 hN hW hE hs hst ht hR
    (by positivity : 0 < min (2 * 𝔠) δ / 4) hAs
  have hGav := goodSet_avgErr hκ h𝔠 hδ hV3 hN hW hR hCond hE hs hst ht hLoop hWeak
  filter_upwards [goodSet_loopK_fail hLoop 3 (by norm_num) hε hD,
    goodSet_loopK_fail hLoop 4 (by norm_num) hε hD,
    goodSet_loopK_fail hLoop 6 (by norm_num) hε hD, goodSet_weak_fail hWeak hε hD,
    goodSet_gij_fail hGij hε hD, goodSet_gii_fail hGii hε hD, goodSet_gav_fail hGav hε hD]
    with n h3 h4 h6 hw hij hii hav u
  obtain ⟨hN9, hLN, hWN⟩ := goodSet_size_facts d n
  have hx0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hsub : {ω | Sizes.seqHflow d n u ω ∉
        goodSet (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε)} ⊆
      goodSetFail d n u (goodSetLoopK (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε) 3) ∪
      goodSetFail d n u (goodSetLoopK (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε) 4) ∪
      goodSetFail d n u (goodSetLoopK (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε) 6) ∪
      goodSetFail d n u (goodSetWeak (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)) ∪
      goodSetFail d n u (goodSetGij (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)) ∪
      goodSetFail d n u (goodSetGii (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)) ∪
      goodSetFail d n u (goodSetGav (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε)) := by
    intro ω hω
    by_contra hcon
    simp only [goodSetFail, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨⟨⟨⟨⟨c3, c4⟩, c6⟩, cw⟩, cij⟩, cii⟩, cav⟩ := hcon
    apply hω
    refine (goodSet_mem_iff _ _ _ _ _ _ _).2
      ⟨Sizes.seqHflow_isHermitian d n u ω, ?_, cw, cij, cii, cav⟩
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    exacts [c3, c4, c6]
  have hc3 := goodSet_card_loop (d.L n) 3
  have hc4 := goodSet_card_loop (d.L n) 4
  have hc6 := goodSet_card_loop (d.L n) 6
  have hcw : Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) =
      d.W n * d.L n * (d.W n * d.L n) * (d.W n * d.L n * (d.W n * d.L n)) := by
    rw [Fintype.card_prod, goodSet_card_idx]
  have hcij : Fintype.card (BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) =
      d.L n * d.L n * (d.W n * d.W n) * (d.L n * d.L n * (d.W n * d.W n)) := by
    rw [Fintype.card_prod, goodSet_card_block]
  have hcii := goodSet_card_block (d.L n) (d.W n)
  have hcav := goodSet_card_z2 (d.L n)
  have hC : ((Fintype.card ((Fin 3 → Bool) × (Fin 3 → Z2 (d.L n))) +
      Fintype.card ((Fin 4 → Bool) × (Fin 4 → Z2 (d.L n))) +
      Fintype.card ((Fin 6 → Bool) × (Fin 6 → Z2 (d.L n))) +
      Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) +
      Fintype.card (BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) +
      Fintype.card (BlockIndex (d.L n) (d.W n)) + Fintype.card (Z2 (d.L n)) : ℕ) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ 9 := by
    rw [hc3, hc4, hc6, hcw, hcij, hcii, hcav]
    push_cast
    have hxe := goodSet_size_cast d n
    have e1 : (d.W n : ℝ) * d.L n * ((d.W n : ℝ) * d.L n) = ((d.size n : ℕ) : ℝ) := by
      rw [hxe]; ring
    have e2 : (d.L n : ℝ) * d.L n * ((d.W n : ℝ) * d.W n) = ((d.size n : ℕ) : ℝ) := by
      rw [hxe]; ring
    have hA : (d.L n : ℝ) * d.L n ≤ ((d.size n : ℕ) : ℝ) := by
      rw [← pow_two]; exact hLN
    rw [e1, e2]
    exact goodSet_count_le hN9 (by positivity) hA
  refine (measure_mono hsub).trans ((goodSet_union7 _ _ _ _ _ _ _ _).trans ?_)
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (h3 u) (h4 u)) (h6 u)) (hw u)) (hij u)) (hii u)) (hav u)) ?_
  have hsum : ∀ (a b c d e f g : ℕ) (X : ℝ≥0∞), (a : ℝ≥0∞) * X + b * X + c * X + d * X + e * X +
      f * X + g * X = ((a + b + c + d + e + f + g : ℕ) : ℝ≥0∞) * X := by
    intros; push_cast; ring
  rw [hsum]
  exact goodSet_final hx0 D _ hC

end HoldsPerTime

end RBM.Path

end
