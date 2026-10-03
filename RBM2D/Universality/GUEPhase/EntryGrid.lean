/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.EntryTail
import RBM2D.Universality.GUEPhase.Proc
import RBM2D.Path.GoodEvent

/-!
# The grid form of Lemma 4.1: the one-time law of the GUE-phase grid path and `gueGrid_entry_bound`

* `map_gueH_eq_mixMat`: under `Pgue d` the grid path at step `k` has the law of the mixture
  `mixMat (t₁) (u_k - t₁)` under `ouP`, `u_k = gridTime k`.
* `gueGrid_entry_bound`: Lemma 4.1 (4.2)+(4.3) on the grid, from `gueEntryMix`
  (`EntryTail.lean`) after the transfer of the one-time law.

Notation: `PathΩ d`, `Sizes.SeqΩ d` (all sizes at once; the size-`n` slice `Sizes.slice`,
`Sizes.seqXmat`), `Sizes.SeqCoord d`, `Sizes.seqGvar d`; the step laws are `gueStepMeasure d`; the
matrix size is `d.size n = (W L)^2`; the grid is given by `gridTime/gridStep`.  The mixed-grid law
lemmas of `Grid.lean` are `private` there, so they are copied here with the prefix `EntryGrid_`
(`EntryGrid_slice_add` … `EntryGrid_measurable_Xmat`).

Layout: the copied private machinery of `Grid.lean`; the one-time law (`EntryGrid_var`,
`EntryGrid_map_gueH`, `map_gueH_eq_mixMat`) and its preimage form `EntryGrid_pgue_preimage`; the
bad set in matrix space and its measurability; deterministic facts (`maxLoopPM ≤ gueLmax`, the
entry of `green - m • 1` is `llErrMat`, the zero-time case, the grid times, the exponent
arithmetic); the main bound `gueGrid_entry_bound`.

Helpers are `private` or carry the prefix `EntryGrid_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Endpoints
open scoped NNReal ENNReal

variable (d : Sizes)

section Algebra

variable {d}

private lemma EntryGrid_slice_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.slice d n (ω + ν) = Sizes.slice d n ω + Sizes.slice d n ν := rfl

private lemma EntryGrid_slice_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.slice d n (a • ω) = a • Sizes.slice d n ω := rfl

private lemma EntryGrid_slice_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ d) :
    Sizes.slice d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.slice d n (ω l) := by
  funext c
  simp [Sizes.slice, Finset.sum_apply]

private lemma EntryGrid_seqXmat_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (ω + ν) = Sizes.seqXmat d n ω + Sizes.seqXmat d n ν := by
  unfold Sizes.seqXmat
  rw [EntryGrid_slice_add, Xmat_add]

private lemma EntryGrid_seqXmat_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (a • ω) = a • Sizes.seqXmat d n ω := by
  unfold Sizes.seqXmat
  rw [EntryGrid_slice_smul, Xmat_smul]

private lemma EntryGrid_seqXmat_sum {ι : Type*} (n : ℕ) (S : Finset ι)
    (ω : ι → Sizes.SeqΩ d) :
    Sizes.seqXmat d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.seqXmat d n (ω l) := by
  unfold Sizes.seqXmat
  rw [EntryGrid_slice_sum]
  exact map_sum (Xlinear (d.L n) (d.W n)) (fun l => Sizes.slice d n (ω l)) S

private lemma EntryGrid_real_smul_matrix {m : Type*} (r : ℝ) (M : Matrix m m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

end Algebra

/-! ### A mixed-step grid carrier

`mixedStepMeasure v0 v1` has the same shape as `gueStepMeasure`: the coordinate variance family
`v0` at step `0`, `v1` at steps `≥ 1`.  With `(v0, v1) = (seqGvar d, gueUnitVar d)` it is
`gueStepMeasure`.  The "swap" computation of `Path/Walk.lean` (private `pathP'`, `swapEquiv`,
`pathP_swap_eq`, `map_combined_eq`), generalised from a constant step law to this mixed law. -/

section MixedGrid

variable {d}

private def EntryGrid_mixedStepMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    ℕ → Measure (Sizes.SeqΩ d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def EntryGrid_mixedRawStep (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (c : Sizes.SeqCoord d)
    (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance EntryGrid_mixedRawStep_isProbabilityMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (i : ℕ) : IsProbabilityMeasure (EntryGrid_mixedRawStep v0 v1 c i) := by
  unfold EntryGrid_mixedRawStep; split_ifs <;> infer_instance

private lemma EntryGrid_mixedStepMeasure_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (i : ℕ) :
    EntryGrid_mixedStepMeasure v0 v1 i
      = Measure.infinitePi (fun c => EntryGrid_mixedRawStep v0 v1 c i) := by
  cases i <;> simp [EntryGrid_mixedStepMeasure, EntryGrid_mixedRawStep]

/-- Same nesting as `Path/Walk.lean`'s private `pathP'`: coordinates first, then the grid index. -/
private def EntryGrid_mixedRaw (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    Measure (Sizes.SeqCoord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Sizes.SeqCoord d =>
    Measure.infinitePi (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i))

private def EntryGrid_swapEquiv : (Sizes.SeqCoord d → ℕ → ℝ) → PathΩ d :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
    (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm

private lemma EntryGrid_measurable_swapEquiv :
    Measurable (EntryGrid_swapEquiv (d := d)) :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm.measurable)

private lemma EntryGrid_swapEquiv_apply (X : Sizes.SeqCoord d → ℕ → ℝ) (i : ℕ)
    (c : Sizes.SeqCoord d) : EntryGrid_swapEquiv X i c = X c i := by
  change (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ)
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
          (Equiv.prodComm (Sizes.SeqCoord d) ℕ))
        ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm X)) i c = X c i
  rw [MeasurableEquiv.coe_curry]
  change (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ))
      ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm X) (i, c) = X c i
  have key := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.prodComm (Sizes.SeqCoord d) ℕ)
    (β := fun _ : ℕ × Sizes.SeqCoord d => ℝ)
    ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm X) (c, i)
  rw [show Equiv.prodComm (Sizes.SeqCoord d) ℕ (c, i) = (i, c) from rfl] at key
  rw [key, MeasurableEquiv.coe_curry_symm]
  rfl

private lemma EntryGrid_mixedRaw_swap_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    (EntryGrid_mixedRaw v0 v1).map EntryGrid_swapEquiv
      = Measure.infinitePi (EntryGrid_mixedStepMeasure v0 v1) := by
  have ha : (EntryGrid_mixedRaw v0 v1).map ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Sizes.SeqCoord d × ℕ => EntryGrid_mixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm
      (μ := fun (c : Sizes.SeqCoord d) (i : ℕ) => EntryGrid_mixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi
        (fun p : Sizes.SeqCoord d × ℕ => EntryGrid_mixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Sizes.SeqCoord d => EntryGrid_mixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Sizes.SeqCoord d => EntryGrid_mixedRawStep v0 v1 p.2 p.1)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)
  have hc : (Measure.infinitePi
        (fun p : ℕ × Sizes.SeqCoord d => EntryGrid_mixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ)
      = Measure.infinitePi (EntryGrid_mixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry
      (μ := fun (i : ℕ) (c : Sizes.SeqCoord d) => EntryGrid_mixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (EntryGrid_mixedStepMeasure_eq v0 v1 i).symm)
  change (EntryGrid_mixedRaw v0 v1).map ((MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (EntryGrid_mixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma**: the law is uniform `w` only from index `1`
on. -/
private lemma EntryGrid_sumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w) (k : ℕ) :
    μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w) := by
  induction k with
  | zero =>
      have hEmpty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      simp only [hEmpty, Finset.sum_empty]
      rw [Measure.map_const, measure_univ, one_smul, zero_smul, gaussianReal_zero_var]
  | succ k ih =>
      have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
      have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hfun : (fun ω => ∑ i ∈ Finset.Icc 1 (k + 1), Y i ω)
          = (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) + Y (k + 1) := by
        funext ω
        rw [hins, Finset.sum_insert hnotmem, add_comm]
        rfl
      rw [hfun]
      have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
        Finset.measurable_sum _ fun i _ => hYm i
      have hlaw1 : HasLaw (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (gaussianReal 0 (k • w)) μ' :=
        ⟨hsummeas.aemeasurable, ih⟩
      have hlaw2 : HasLaw (Y (k + 1)) (gaussianReal 0 w) μ' :=
        ⟨(hYm (k + 1)).aemeasurable, hYd (k + 1) (by omega)⟩
      have hindep : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y (k + 1)) μ' := by
        have h := hY.indepFun_finsetSum_of_notMem hYm hnotmem
        have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
          funext ω; simp [Finset.sum_apply]
        rwa [heq] at h
      have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw1 hlaw2
      rw [hres, add_zero, ← succ_nsmul]

/-- **The two-scale mixed weighted sum lemma**: `Y 0` has variance `w0`, `Y 1, Y 2, …` the common
variance `w1`. -/
private lemma EntryGrid_weightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w0 w1 : ℝ≥0} (hY0 : μ'.map (Y 0) = gaussianReal 0 w0)
    (hY1 : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w1) (a b : ℝ) (k : ℕ) :
    μ'.map (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * w1)) := by
  classical
  have hindep : IndepFun (fun ω => a * Y 0 ω) (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω) μ' := by
    have h0 : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y 0) μ' := by
      have h := hY.indepFun_finsetSum_of_notMem hYm (s := Finset.Icc 1 k) (i := 0) (by simp)
      have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [heq] at h
    exact h0.symm.comp (φ := (a * ·)) (ψ := (b * ·)) (by fun_prop) (by fun_prop)
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hY0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w1) :=
    EntryGrid_sumIcc_map_gaussianReal_mixed hYm hY hY1 k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w1))) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have heq : (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
        = (b * ·) ∘ (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) hsummeas, hlawsum, gaussianReal_map_const_mul,
      mul_zero]
  have hgoal_eq : (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = (fun ω => a * Y 0 ω) + fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω := rfl
  rw [hgoal_eq]
  have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw0 hlaw1
  rw [hres, add_zero]
  congr 1
  rw [nsmul_eq_mul, nsmul_eq_mul]
  apply NNReal.coe_injective
  push_cast
  ring

private lemma EntryGrid_map_column_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [EntryGrid_mixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi
      (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i)).map (fun y : ℕ → ℝ => y i)
        = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    have hi0 : i ≠ 0 := by omega
    simp [EntryGrid_mixedRawStep, hi0]
  exact EntryGrid_weightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law**. -/
private lemma EntryGrid_map_combined_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (a b : ℝ)
    (k : ℕ) :
    (Measure.infinitePi (EntryGrid_mixedStepMeasure v0 v1)).map
        (fun ω : PathΩ d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Sizes.SeqCoord d => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
            + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c))) := by
  have hmeasComb : Measurable (fun ω : PathΩ d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : PathΩ d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hcomp : (fun ω : PathΩ d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
        ∘ EntryGrid_swapEquiv
      = (fun X : Sizes.SeqCoord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      EntryGrid_swapEquiv_apply]
  rw [← EntryGrid_mixedRaw_swap_eq v0 v1,
    Measure.map_map hmeasComb EntryGrid_measurable_swapEquiv, hcomp]
  have hfmeas : ∀ c : Sizes.SeqCoord d,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) := fun c => by
    have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
    have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Sizes.SeqCoord d =>
        Measure.infinitePi (fun i : ℕ => EntryGrid_mixedRawStep v0 v1 c i))
      (f := fun c : Sizes.SeqCoord d => fun y : ℕ → ℝ =>
        a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [EntryGrid_mixedRaw]
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => EntryGrid_map_column_eq_mixed v0 v1 c a b k))

end MixedGrid

/-! ### Identification of `Pgue d` as the mixed-grid carrier, and the size slice -/

section Identification

variable {d}

private lemma EntryGrid_Pgue_eq_mixed :
    Pgue d = Measure.infinitePi
      (EntryGrid_mixedStepMeasure (Sizes.seqGvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord d` (generalising
`Sizes.seqP_map_slice` from `seqGvar d` to any variance family). -/
private lemma EntryGrid_map_slice_infinitePi (w : Sizes.SeqCoord d → ℝ≥0) (n : ℕ) :
    (Measure.infinitePi fun c => gaussianReal 0 (w c)).map (Sizes.slice d n)
      = Measure.infinitePi fun c : Coord (d.L n) (d.W n) => gaussianReal 0 (w ⟨n, c⟩) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : Coord (d.L n) (d.W n) → Sizes.SeqCoord d := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : Sizes.SeqCoord d → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : Sizes.slice d n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, Sizes.slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, Sizes.slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (Sizes.measurable_slice d n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e]

private lemma EntryGrid_measurable_Xmat (L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j

end Identification

/-! ### The one-time law of the grid path at step `k` (T2) -/

section OneTimeLaw

/-- `gueUnitVar / N = gueVar` (`N = d.size n`): `1/N` on the diagonal, `1/(2N)` off it. -/
private lemma EntryGrid_gueUnitVar_div (n : ℕ) (c : Coord (d.L n) (d.W n)) :
    ((gueUnitVar d ⟨n, c⟩ : ℝ≥0) : ℝ) / ((d.size n : ℕ) : ℝ)
      = (RBM.Endpoints.gueVar (d.L n) (d.W n) c : ℝ) := by
  have hsz : ((d.size n : ℕ) : ℝ) = (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) := rfl
  unfold gueUnitVar RBM.Endpoints.gueVar
  by_cases hc : c.1 = c.2.1
  · simp only [hc, ite_true, hsz]
    push_cast
    simp
  · simp only [hc, ite_false, hsz]
    push_cast
    field_simp

/-- The coordinate variances of the grid path at step `k`:
`t₁ gvar_c + k (Δ/N) gueUnitVar_c`. -/
def EntryGrid_var (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (c : Coord (d.L n) (d.W n)) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (t1 n) ^ 2) (sq_nonneg _) * Sizes.seqGvar d ⟨n, c⟩
    + k • (NNReal.mk (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) ^ 2) (sq_nonneg _)
        * gueUnitVar d ⟨n, c⟩)

/-- **The one-time law of the grid path at step `k`**: `Xmat` of independent centred Gaussian
coordinates with variances `EntryGrid_var`. -/
theorem EntryGrid_map_gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    (Pgue d).map (gueH d t1 t0 K n k) =
      (Measure.infinitePi
        (fun c : Coord (d.L n) (d.W n) => gaussianReal 0 (EntryGrid_var d t1 t0 K n k c))).map
        (Xmat (d.L n) (d.W n)) := by
  set a : ℝ := Real.sqrt (t1 n) with hadef
  set b : ℝ := Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) with hbdef
  have hHeq : gueH d t1 t0 K n k
      = fun ω => Sizes.seqXmat d n (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    funext ω
    rw [EntryGrid_seqXmat_add, EntryGrid_seqXmat_smul, EntryGrid_seqXmat_smul,
      EntryGrid_seqXmat_sum, EntryGrid_real_smul_matrix, EntryGrid_real_smul_matrix]
    rfl
  have hLHSmeas : Measurable (fun ω : PathΩ d =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : PathΩ d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hfun : (fun ω : PathΩ d => Sizes.seqXmat d n
        (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i))
      = Xmat (d.L n) (d.W n) ∘ Sizes.slice d n ∘
          (fun ω : PathΩ d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := rfl
  rw [hHeq, hfun, ← Measure.map_map (EntryGrid_measurable_Xmat _ _)
      ((Sizes.measurable_slice d n).comp hLHSmeas),
    ← Measure.map_map (Sizes.measurable_slice d n) hLHSmeas,
    EntryGrid_Pgue_eq_mixed,
    EntryGrid_map_combined_eq_mixed (Sizes.seqGvar d) (gueUnitVar d) a b k]
  congr 1
  exact EntryGrid_map_slice_infinitePi _ n

/-- **T2: the law of the grid path at step `k` is the law of the mixture** `√t₁ X_band +
√(u_k - t₁) X_GUE` under `ouP`: the variance at step `k` is
`t₁ gvar + k Δ gueUnitVar / N`, which is `mixVar t₁ (k Δ)` because `gueVar = gueUnitVar / N` and
`gridTime k - t₁ = k Δ`. -/
theorem map_gueH_eq_mixMat (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) :
    (Pgue d).map (gueH d t1 t0 K n k) =
      (ouP (d.L n) (d.W n)).map
        (mixMat (d.L n) (d.W n) (t1 n) (gridTime t1 t0 K n k - t1 n)) := by
  have hΔ : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hkΔ : 0 ≤ (k : ℝ) * gridStep t1 t0 K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  have hbk : gridTime t1 t0 K n k - t1 n = (k : ℝ) * gridStep t1 t0 K n := by
    unfold gridTime; ring
  have hb : 0 ≤ gridTime t1 t0 K n k - t1 n := by rw [hbk]; exact hkΔ
  have hMpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
    have h1 : 0 < d.W n := d.W_pos n
    have h2 : 0 < d.L n := by have := d.three_le_L n; omega
    have : 0 < d.size n := by rw [Sizes.size_eq]; positivity
    exact_mod_cast this
  -- the `ouP` side: `mixMat = Xmat ∘ mixSample`, and `mixSample_law`
  have hcomp : mixMat (d.L n) (d.W n) (t1 n) (gridTime t1 t0 K n k - t1 n)
      = Xmat (d.L n) (d.W n) ∘
          mixSample (d.L n) (d.W n) (t1 n) (gridTime t1 t0 K n k - t1 n) :=
    funext (mixMat_eq_Xmat_mixSample _ _ _ _)
  rw [EntryGrid_map_gueH, hcomp,
    ← Measure.map_map (EntryGrid_measurable_Xmat _ _) (measurable_mixSample _ _ _ _),
    mixSample_law _ _ ht1 hb]
  congr 1
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  apply NNReal.coe_injective
  have ha2 : Real.sqrt (t1 n) ^ 2 = t1 n := Real.sq_sqrt ht1
  have hb2 : Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) ^ 2
      = gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ) := Real.sq_sqrt (div_nonneg hΔ hMpos.le)
  have hunit := EntryGrid_gueUnitVar_div d n c
  have hseq : ((Sizes.seqGvar d ⟨n, c⟩ : ℝ≥0) : ℝ) = (gvar (d.L n) (d.W n) c : ℝ) := rfl
  have hmix := mixEntry_mixVar_coe (d.L n) (d.W n) ht1 hb c
  rw [hmix, ← hunit, hbk]
  unfold EntryGrid_var
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, NNReal.coe_natCast]
  rw [ha2, hb2, hseq]
  ring

end OneTimeLaw

/-- The preimage form of T2: for a measurable set `B` of matrices, `Pgue` of the event
`{gueH_k ∈ B}` is the `ouP`-probability of `{mixMat ∈ B}`. -/
theorem EntryGrid_pgue_preimage (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n)
    {B : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)} (hB : MeasurableSet B) :
    Pgue d (gueH d t1 t0 K n k ⁻¹' B) =
      ouP (d.L n) (d.W n)
        (mixMat (d.L n) (d.W n) (t1 n) (gridTime t1 t0 K n k - t1 n) ⁻¹' B) := by
  rw [← Measure.map_apply (gueH_measurable d t1 t0 K n k) hB,
    map_gueH_eq_mixMat d t1 t0 K n k ht1 ht10,
    Measure.map_apply (measurable_mixMat _ _ _ _) hB]

/-! ### The bad set in matrix space and its measurability -/

section MatrixSpace

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem EntryGrid_measurable_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix ι ι ℂ} (hM : Measurable M) (i j : ι) :
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

private theorem EntryGrid_measurable_llErrMat (E u : ℝ) (i j : Idx L W) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => llErrMat L W E u M i j := by
  have hM : Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ) :=
    (continuous_id.sub continuous_const).measurable
  exact ((EntryGrid_measurable_inv_apply hM i j).sub measurable_const).norm

private theorem EntryGrid_measurable_maxLoopPM (E u : ℝ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => maxLoopPM L W E u M := by
  have hloop : ∀ a b : Z2 L,
      Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => loopPM L W E u M a b :=
    fun a b => GoodEvent_measurable_gloop L W (spectralZ E u) (pmLoop a b)
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) => ‖loopPM L W E u M p.1 p.2‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => (hloop p.1 p.2).norm
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => maxLoopPM L W E u M) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) => ‖loopPM L W E u M p.1 p.2‖) := by
    funext M
    simp only [maxLoopPM, Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The single-`k` bad set of `GUEEntryMix` in matrix space (`s = N^τ`, `δ`, energy `E`, time `u`):
the matrices `M` with `s (maxLoopPM M + W⁻²) < ` the squared error entry on the event
`{all entries ≤ δ}`, for some entry `(i, j)`. -/
private def EntryGrid_badMat (E u δ s : ℝ) : Set (Matrix (Idx L W) (Idx L W) ℂ) :=
  {M | ∃ i j : Idx L W, s * (maxLoopPM L W E u M + (((W : ℕ) : ℝ) ^ 2)⁻¹) <
    (if ∀ x y, llErrMat L W E u M x y ≤ δ then llErrMat L W E u M i j ^ 2 else 0)}

private theorem EntryGrid_measurableSet_badMat (E u δ s : ℝ) :
    MeasurableSet (EntryGrid_badMat L W E u δ s) := by
  have hll : ∀ x y : Idx L W,
      Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => llErrMat L W E u M x y :=
    fun x y => EntryGrid_measurable_llErrMat L W E u x y
  have hcond : MeasurableSet {M : Matrix (Idx L W) (Idx L W) ℂ |
      ∀ x y, llErrMat L W E u M x y ≤ δ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      measurableSet_le (hll x y) measurable_const
  have hrhs : ∀ i j : Idx L W, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      (if ∀ x y, llErrMat L W E u M x y ≤ δ then llErrMat L W E u M i j ^ 2 else 0) :=
    fun i j => Measurable.ite hcond ((hll i j).pow_const 2) measurable_const
  have hlhs : Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      s * (maxLoopPM L W E u M + (((W : ℕ) : ℝ) ^ 2)⁻¹) :=
    measurable_const.mul ((EntryGrid_measurable_maxLoopPM L W E u).add measurable_const)
  have heq : EntryGrid_badMat L W E u δ s = ⋃ i : Idx L W, ⋃ j : Idx L W,
      {M : Matrix (Idx L W) (Idx L W) ℂ | s * (maxLoopPM L W E u M + (((W : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat L W E u M x y ≤ δ then llErrMat L W E u M i j ^ 2 else 0)} := by
    ext M
    simp [EntryGrid_badMat]
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    measurableSet_lt hlhs (hrhs i j)

end MatrixSpace

/-! ### Deterministic facts -/

section Deterministic

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `(green M z - m • 1)_{ij}` as the entry of `(M - z)⁻¹` minus `m δ_{ij}`. -/
private theorem EntryGrid_norm_green_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z m : ℂ) (i j : ι) :
    ‖(green M z - m • (1 : Matrix ι ι ℂ)) i j‖
      = ‖(M - z • (1 : Matrix ι ι ℂ))⁻¹ i j - (if i = j then m else 0)‖ := by
  congr 1
  simp only [green, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

/-- `llErrMat` is the entry of `green M z - m • 1` at `z = spectralZ E u`, `m = spectralM E`. -/
private theorem EntryGrid_norm_green_sub_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (i j : Idx L W) :
    ‖(green M (spectralZ E u) - spectralM E • (1 : Matrix (Idx L W) (Idx L W) ℂ)) i j‖
      = llErrMat L W E u M i j :=
  EntryGrid_norm_green_sub M _ _ i j

/-- `maxLoopPM ≤ loopMax _ 2`: the `(+,-)` two-loops `pmLoop a b` have two signs and two labels. -/
private theorem EntryGrid_maxLoopPM_le (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    maxLoopPM L W E u M ≤ RBM.Ind.loopMax L W (blockMat M) (spectralZ E u) 2 := by
  unfold maxLoopPM
  refine Finset.sup'_le _ _ fun p _ => ?_
  exact RBM.Ind.norm_gloop_le_loopMax (pmLoop p.1 p.2) rfl rfl

end Deterministic

/-- `green 0 z = m • 1` when `m z = -1`. -/
private theorem EntryGrid_green_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {z m : ℂ}
    (hmz : m * z = -1) : green (0 : Matrix ι ι ℂ) z = m • (1 : Matrix ι ι ℂ) := by
  unfold green
  refine Matrix.inv_eq_left_inv ?_
  rw [zero_sub, Matrix.mul_neg, smul_mul_smul_comm, Matrix.one_mul, ← neg_smul, hmz, neg_neg,
    one_smul]

/-- At the spectral time `0`: `m z_0 = -1` (`z_0 = E + m`, `m² + E m + 1 = 0`). -/
private theorem EntryGrid_spectral_zero {E : ℝ} (hE : |E| ≤ 2) :
    spectralM E * spectralZ E 0 = -1 := by
  have hm := spectralM_mul hE
  have hz : spectralZ E 0 = (E : ℂ) + spectralM E := by simp [spectralZ]
  rw [hz]
  linear_combination hm

/-- Zero time: every entry of `green 0 z_0 - m • 1` vanishes, so `0 ∉` the bad set of time `0`. -/
private theorem EntryGrid_zero_not_mem_badMat (L W : ℕ) [NeZero L] [NeZero W] {E : ℝ}
    (hE : |E| ≤ 2) (δ s : ℝ) (hs : 0 ≤ s) :
    (0 : Matrix (Idx L W) (Idx L W) ℂ) ∉ EntryGrid_badMat L W E 0 δ s := by
  rintro ⟨i, j, h⟩
  have hg := EntryGrid_green_zero (ι := Idx L W) (EntryGrid_spectral_zero hE)
  have hll : ∀ x y : Idx L W, llErrMat L W E 0 0 x y = 0 := by
    intro x y
    rw [← EntryGrid_norm_green_sub_eq, hg, sub_self]
    simp
  have hrhs : (if ∀ x y, llErrMat L W E 0 0 x y ≤ δ then llErrMat L W E 0 0 i j ^ 2 else 0)
      = 0 := by
    split_ifs
    · rw [hll i j]; norm_num
    · rfl
  rw [hrhs] at h
  have h0 : 0 ≤ s * (maxLoopPM L W E 0 0 + (((W : ℕ) : ℝ) ^ 2)⁻¹) :=
    mul_nonneg hs (add_nonneg (RBM.Green.maxLoopPM_nonneg E 0 _) (by positivity))
  exact absurd h (not_lt.2 h0)

/-! ### The grid times -/

/-- `Δ ≥ 0`. -/
private theorem EntryGrid_gridStep_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (h : t1 n ≤ t0 n) : 0 ≤ gridStep t1 t0 K n :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem EntryGrid_gridTime_sub (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    gridTime t1 t0 K n k - t1 n = (k : ℝ) * gridStep t1 t0 K n := by
  unfold gridTime; ring

/-- `t₁ ≤ u_k`. -/
private theorem EntryGrid_gridTime_ge {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (k : ℕ)
    (ht10 : t1 n ≤ t0 n) : t1 n ≤ gridTime t1 t0 K n k := by
  have h := EntryGrid_gridTime_sub t1 t0 K n k
  have h2 : 0 ≤ (k : ℝ) * gridStep t1 t0 K n :=
    mul_nonneg (Nat.cast_nonneg _) (EntryGrid_gridStep_nonneg ht10)
  linarith

/-- `u_k ≤ t₀` for `k ≤ K`. -/
private theorem EntryGrid_gridTime_le {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (hK : K n ≠ 0)
    (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) : gridTime t1 t0 K n k ≤ t0 n := by
  rw [← gridTime_last t1 t0 K n hK]
  unfold gridTime
  have hΔ := EntryGrid_gridStep_nonneg (K := K) ht10
  have hk' : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hk
  nlinarith

/-- At grid time `0`: `t₁ = 0` and `k Δ = 0`, so the path vanishes. -/
private theorem EntryGrid_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) (hu : gridTime t1 t0 K n k = 0) (ω : PathΩ d) :
    gueH d t1 t0 K n k ω = 0 := by
  have hΔ := EntryGrid_gridStep_nonneg (K := K) ht10
  have hkΔ : 0 ≤ (k : ℝ) * gridStep t1 t0 K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  have h := EntryGrid_gridTime_sub t1 t0 K n k
  have ht : t1 n = 0 := by rw [hu] at h; linarith [ht1]
  have hk : (k : ℝ) * gridStep t1 t0 K n = 0 := by rw [hu] at h; linarith [ht1]
  unfold gueH
  rw [ht, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_add]
  rcases mul_eq_zero.1 hk with h | h
  · have hk0 : k = 0 := by exact_mod_cast h
    subst hk0
    simp
  · rw [h, zero_div, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

/-! ### The parameters fed to `gueEntryMix` -/

/-- `a_k = t₁` at positive grid time (`1/2` at grid time `0`, where `0 < a + b` would fail). -/
private def EntryGrid_a (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) : ℝ :=
  if 0 < gridTime t1 t0 K n k then t1 n else 1 / 2

/-- `b_k = u_k - t₁` at positive grid time (`0` at grid time `0`). -/
private def EntryGrid_b (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) : ℝ :=
  if 0 < gridTime t1 t0 K n k then gridTime t1 t0 K n k - t1 n else 0

private theorem EntryGrid_params (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : K n ≠ 0) (hk : k ≤ K n) :
    0 ≤ EntryGrid_a t1 t0 K n k ∧ 0 ≤ EntryGrid_b t1 t0 K n k ∧
      0 < EntryGrid_a t1 t0 K n k + EntryGrid_b t1 t0 K n k ∧
      EntryGrid_a t1 t0 K n k + EntryGrid_b t1 t0 K n k < 1 := by
  by_cases hpos : 0 < gridTime t1 t0 K n k
  · have hge := EntryGrid_gridTime_ge (K := K) k ht10
    have hle := EntryGrid_gridTime_le hK ht10 hk
    simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]
    refine ⟨ht1, by linarith, by linarith, by linarith⟩
  · simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]
    norm_num

/-! ### The size bounds and the union arithmetic -/

private theorem EntryGrid_two_le_size (n : ℕ) : 2 ≤ d.size n := by
  have h1 : 1 ≤ d.W n := d.W_pos n
  have h3 : 3 ≤ d.L n := d.three_le_L n
  have : 3 ≤ d.W n * d.L n := by nlinarith
  unfold Sizes.size
  nlinarith

private theorem EntryGrid_gridK_le (n0 n : ℕ) :
    gueGridK d n0 n ≤ (d.size n) ^ (64 * n0 + 128) := by
  unfold gueGridK
  have h2 := EntryGrid_two_le_size d n
  calc (d.size n + 1) ^ (32 * n0 + 64) ≤ (d.size n ^ 2) ^ (32 * n0 + 64) :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ = (d.size n) ^ (64 * n0 + 128) := by rw [← pow_mul]; ring_nf

/-- `(K + 1) N^{-(D + 1 + m)} ≤ N^{-D}` for `K ≤ N^m`, `N ≥ 2`. -/
private theorem EntryGrid_union_arith (Nn Kn m : ℕ) (hN : 2 ≤ Nn) (hK : Kn ≤ Nn ^ m) (D : ℝ) :
    ((Kn + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((Nn : ℝ) ^ (-(D + 1 + (m : ℝ))))
      ≤ ENNReal.ofReal ((Nn : ℝ) ^ (-D)) := by
  have hN2 : (2 : ℝ) ≤ Nn := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < Nn := by linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hKr : (Kn : ℝ) ≤ (Nn : ℝ) ^ m := by exact_mod_cast hK
  have h1 : (1 : ℝ) ≤ (Nn : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hp : (0 : ℝ) ≤ (Nn : ℝ) ^ (-(D + 1 + (m : ℝ))) := Real.rpow_nonneg hN0.le _
  have hmul : (Nn : ℝ) ^ (m : ℝ) * (Nn : ℝ) ^ (-((D + 1) + (m : ℝ))) = (Nn : ℝ) ^ (-(D + 1)) :=
    rpow_mul_rpow_neg_add (by omega) (m : ℝ) (D + 1)
  have hnat : (Nn : ℝ) ^ (m : ℝ) = (Nn : ℝ) ^ m := Real.rpow_natCast _ _
  have hD1 : (2 : ℝ) * (Nn : ℝ) ^ (-(D + 1)) ≤ (Nn : ℝ) ^ (-D) := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
    have h := Real.rpow_nonneg hN0.le (-D)
    calc 2 * ((Nn : ℝ) ^ (-D) * (Nn : ℝ)⁻¹) = (Nn : ℝ) ^ (-D) * (2 / Nn) := by ring
      _ ≤ (Nn : ℝ) ^ (-D) * 1 := by
          gcongr; rw [div_le_one hN0]; exact hN2
      _ = _ := mul_one _
  calc ((Kn + 1 : ℕ) : ℝ) * (Nn : ℝ) ^ (-(D + 1 + (m : ℝ)))
      ≤ (2 * (Nn : ℝ) ^ m) * (Nn : ℝ) ^ (-(D + 1 + (m : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ hp
        push_cast; linarith
    _ = 2 * ((Nn : ℝ) ^ (m : ℝ) * (Nn : ℝ) ^ (-((D + 1) + (m : ℝ)))) := by rw [hnat]; ring
    _ = 2 * (Nn : ℝ) ^ (-(D + 1)) := by rw [hmul]
    _ ≤ (Nn : ℝ) ^ (-D) := hD1

/-! ### T1: Lemma 4.1 on the GUE-phase grid -/

/-- The pointwise step of `gueGrid_entry_bound`: if `ω` is in the bad event of the entry `(i, j)`
at grid step `k` (the bound `s (gueLmax + W⁻²) < ` the indicator of the a priori event times the
squared entry of `green - m • 1`), then `gueH_k ω` lies in the bad set of matrix space
(`maxLoopPM ≤ gueLmax`, `‖(green M z - m • 1)_{ij}‖ = llErrMat M i j`). -/
private theorem EntryGrid_pointwise (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n k : ℕ)
    (ω : PathΩ d) (i j : Idx (d.L n) (d.W n)) (s : ℝ) (hs : 0 ≤ s)
    (hlt : s * (gueLmax d E t1 t0 K n 2 k ω + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) <
      {ω' : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
          ‖(green (gueH d t1 t0 K n k ω') (spectralZ (E n) (gridTime t1 t0 K n k)) -
            spectralM (E n) •
              (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤ δ n}.indicator
        (fun ω' => ‖(green (gueH d t1 t0 K n k ω') (spectralZ (E n) (gridTime t1 t0 K n k)) -
            spectralM (E n) •
              (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ^ 2) ω) :
    gueH d t1 t0 K n k ω ∈
      EntryGrid_badMat (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k) (δ n) s := by
  have hnorm : ∀ (M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (x y : Idx (d.L n) (d.W n)),
      ‖(green M' (spectralZ (E n) (gridTime t1 t0 K n k)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) x y‖
        = llErrMat (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k) M' x y :=
    fun M' x y => EntryGrid_norm_green_sub_eq _ _ _ _ M' x y
  have hle : s * (maxLoopPM (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k) (gueH d t1 t0 K n k ω) +
        (((d.W n : ℕ) : ℝ) ^ 2)⁻¹)
      ≤ s * (gueLmax d E t1 t0 K n 2 k ω + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left (EntryGrid_maxLoopPM_le (d.L n) (d.W n) (E n) _ _) _) hs
  by_cases hall : ∀ x y, llErrMat (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k)
      (gueH d t1 t0 K n k ω) x y ≤ δ n
  · have hmem : ω ∈ {ω' : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
        ‖(green (gueH d t1 t0 K n k ω') (spectralZ (E n) (gridTime t1 t0 K n k)) -
          spectralM (E n) •
            (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤ δ n} := by
      intro x y
      rw [hnorm]
      exact hall x y
    rw [Set.indicator_of_mem hmem] at hlt
    refine ⟨i, j, ?_⟩
    simp only [hall, implies_true, ↓reduceIte]
    refine lt_of_le_of_lt hle (lt_of_lt_of_eq hlt ?_)
    simp only [hnorm]
  · have hnot : ω ∉ {ω' : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
        ‖(green (gueH d t1 t0 K n k ω') (spectralZ (E n) (gridTime t1 t0 K n k)) -
          spectralM (E n) •
            (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤ δ n} := by
      intro h
      apply hall
      intro x y
      rw [← hnorm]
      exact h x y
    rw [Set.indicator_of_notMem hnot] at hlt
    have h0 : 0 ≤ s * (gueLmax d E t1 t0 K n 2 k ω + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) :=
      mul_nonneg hs (add_nonneg (RBM.Ind.loopMax_nonneg 2) (by positivity))
    exact absurd hlt (not_lt.2 h0)

/-- **Lemma 4.1 (4.2)+(4.3) on the GUE-phase grid**, on the size scale.  On the a priori event
`{all entries of G - m ≤ δ_n}`,
`δ_n ≤ N^{-c₀}`, the squared entry `|(G_k - m)_{ij}|²` of the grid resolvent at the grid time
`u_k` is `≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W⁻²` (`gueLmax _ 2`, the 2-loop maximum),
uniformly in `k ≤ K_n`, `i`, `j`.  Proof: per grid point `k` the bad event on `Pgue` has the
`ouP`-probability of the bad event of the mixture `mixMat t₁ (u_k - t₁)` (`map_gueH_eq_mixMat`),
a subset of the event of `gueEntryMix` (`a = t₁`, `b = u_k - t₁`); the union over the `K_n + 1`
grid points costs a power of `N` (`K_n ≤ N^{64 n₀ + 128}`, `D ↦ D + 1 + 64 n₀ + 128`); at grid time
`0` (`t₁ = 0`, `k = 0` or `Δ = 0`) `gueH = 0` and the bad event is empty. -/
theorem gueGrid_entry_bound {𝔠 κ : ℝ} (h𝔠 : 0 < 𝔠) (hadm : Admissible 𝔠 d) (hκ : 0 < κ)
    (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 ≤ δ n)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ n in atTop, δ n ≤ ((d.size n : ℕ) : ℝ) ^ (-c₀)) :
    StochDomAt (Pgue d) d.size
      (fun n (p : Fin (gueGridK d n0 n + 1) ×
          (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))) ω =>
        {ω' : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
            ‖(green (gueH d t1 t0 (gueGridK d n0) n p.1 ω')
                (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) -
              spectralM (E n) •
                (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
            δ n}.indicator
          (fun ω' => ‖(green (gueH d t1 t0 (gueGridK d n0) n p.1 ω')
                (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) -
              spectralM (E n) •
                (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax d E t1 t0 (gueGridK d n0) n 2 p.1 ω +
          (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) := by
  intro τ hτ D hD
  have hD' : 0 < D + 1 + ((64 * n0 + 128 : ℕ) : ℝ) := by positivity
  have hmix := gueEntryMix 𝔠 h𝔠 d hadm κ hκ E hE (64 * n0 + 128) (gueGridK d n0)
    (EntryGrid_gridK_le d n0) (fun n k => EntryGrid_a t1 t0 (gueGridK d n0) n k)
    (fun n k => EntryGrid_b t1 t0 (gueGridK d n0) n k)
    (fun n k => EntryGrid_params t1 t0 (gueGridK d n0) n k (ht1 n) (ht10 n) (ht0 n)
      (gueGridK_ne_zero d n0 n) (Nat.lt_succ_iff.1 k.2))
    c₀ δ hc₀ hδ0 hδ τ (D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)) hτ hD'
  filter_upwards [hmix] with n hn
  have hN2 := EntryGrid_two_le_size d n
  have hs0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- Step 1: the bad event is inside the union over the grid of the preimages of the matrix bad sets
  refine le_trans (measure_mono (t := ⋃ k : Fin (gueGridK d n0 n + 1),
    gueH d t1 t0 (gueGridK d n0) n k ⁻¹' EntryGrid_badMat (d.L n) (d.W n) (E n)
      (gridTime t1 t0 (gueGridK d n0) n k) (δ n) (((d.size n : ℕ) : ℝ) ^ τ)) ?_) ?_
  · rintro ω ⟨⟨k, i, j⟩, hlt⟩
    exact Set.mem_iUnion.2 ⟨k, EntryGrid_pointwise d E t1 t0 (gueGridK d n0) δ n k ω i j _ hs0 hlt⟩
  -- Step 2: each grid point costs at most the `ouP`-probability of the event of `gueEntryMix`
  have hk : ∀ k : Fin (gueGridK d n0 n + 1),
      Pgue d (gueH d t1 t0 (gueGridK d n0) n k ⁻¹' EntryGrid_badMat (d.L n) (d.W n) (E n)
        (gridTime t1 t0 (gueGridK d n0) n k) (δ n) (((d.size n : ℕ) : ℝ) ^ τ))
      ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
    intro k
    by_cases hpos : 0 < gridTime t1 t0 (gueGridK d n0) n k
    · rw [EntryGrid_pgue_preimage d t1 t0 _ n k (ht1 n) (ht10 n)
        (EntryGrid_measurableSet_badMat (d.L n) (d.W n) _ _ _ _)]
      refine le_trans (measure_mono ?_) hn
      intro ω hω
      obtain ⟨i, j, hij⟩ := hω
      refine ⟨k, i, j, ?_⟩
      have hab : EntryGrid_a t1 t0 (gueGridK d n0) n k + EntryGrid_b t1 t0 (gueGridK d n0) n k
          = gridTime t1 t0 (gueGridK d n0) n k := by
        simp only [EntryGrid_a, EntryGrid_b, hpos, ↓reduceIte]; ring
      have ha : EntryGrid_a t1 t0 (gueGridK d n0) n k = t1 n := by
        simp only [EntryGrid_a, hpos, ↓reduceIte]
      have hb : EntryGrid_b t1 t0 (gueGridK d n0) n k
          = gridTime t1 t0 (gueGridK d n0) n k - t1 n := by
        simp only [EntryGrid_b, hpos, ↓reduceIte]
      rw [hab, ha, hb]
      exact hij
    · have h0 : gridTime t1 t0 (gueGridK d n0) n k = 0 :=
        le_antisymm (not_lt.1 hpos) (le_trans (ht1 n) (EntryGrid_gridTime_ge k (ht10 n)))
      have hempty : gueH d t1 t0 (gueGridK d n0) n k ⁻¹' EntryGrid_badMat (d.L n) (d.W n) (E n)
          (gridTime t1 t0 (gueGridK d n0) n k) (δ n) (((d.size n : ℕ) : ℝ) ^ τ) = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rw [EntryGrid_gueH_zero d t1 t0 _ n k (ht1 n) (ht10 n) h0 ω, h0]
        exact EntryGrid_zero_not_mem_badMat (d.L n) (d.W n)
          (by linarith [hE n, hκ, abs_nonneg (E n)]) (δ n) _ hs0
      rw [hempty, measure_empty]
      exact zero_le
  -- Step 3: the union bound over the `K_n + 1` grid points and the arithmetic
  calc Pgue d (⋃ k : Fin (gueGridK d n0 n + 1),
        gueH d t1 t0 (gueGridK d n0) n k ⁻¹' EntryGrid_badMat (d.L n) (d.W n) (E n)
          (gridTime t1 t0 (gueGridK d n0) n k) (δ n) (((d.size n : ℕ) : ℝ) ^ τ))
      ≤ ∑ k : Fin (gueGridK d n0 n + 1),
          Pgue d (gueH d t1 t0 (gueGridK d n0) n k ⁻¹' EntryGrid_badMat (d.L n) (d.W n) (E n)
            (gridTime t1 t0 (gueGridK d n0) n k) (δ n) (((d.size n : ℕ) : ℝ) ^ τ)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (gueGridK d n0 n + 1),
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ((gueGridK d n0 n + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1 + ((64 * n0 + 128 : ℕ) : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) :=
        EntryGrid_union_arith _ _ _ hN2 (EntryGrid_gridK_le d n0 n) D

end RBM.Univ.GUEPhase

end
