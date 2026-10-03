/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Grid
import RBM2D.Evolution.XiBounds
import RBM2D.Hierarchy.ContractionSecondLoopSameEdge
import RBM2D.Gauss.LoopFlowCoordinateChain
import RBM2D.Gauss.LoopCoordinateDerivativeBounds
import RBM2D.Gauss.SteinMatrix
import RBM2D.Gauss.LoopInitialValueScalar

/-!
# Lemma 5.15 for the GUE-phase grid: the `1`-loop expectation bound, `d = 2`

Lemma `lemma:step6-1` for the GUE-phase grid path `gueH` of `Universality/GUEPhase/Grid.lean`, on
the size scale (the argument parallels arXiv:2501.01718 §5.8, Lemma 5.15, (5.126)–(5.128)).  The
band analogue is `Evolution/Step61.lean`.

**Result.**  `gueGrid_expect_oneLoop`: the pathwise `1`-loop bound
`‖⟨(G - m)E_a⟩‖ ≺ (N η_u)^{-1}` (`StochDomAt (Pgue d) d.size`, uniformly in the grid time and the
block label) implies `‖𝔼⟨(G - m)E_a⟩‖ ≤ N^ε (N η_u)^{-2}` eventually, for every `ε > 0`.

**Proof.**
* The one-time law of grid step `k`.  The step-`k` matrix is `Xmat` of
  the size-`n` slice of `√t₁ ω₀ + √(Δ/N) ∑_{i=1}^k ω_i`, which has the product Gaussian law with
  variances `t₁ seqGvar_c + k (Δ/N) gueUnitVar_c` (`ol_map_comb_slice`, `ol_gueH_eq`).  The
  mixed-grid computation reproduces the private one of `Grid.lean` (`OneLoop_*` copies).
* Stein's identity for that product Gaussian (`GaussianProduct.stein`, applied to
  `tr(B_c G E_a)` as in `step61_stein`), with the
  contraction of the mixed variances: the `t₁` part is `sum_coordinateBlock_trace_pair`,
  the unit-GUE part is `OneLoop_sum_gue_block`, `∑_c w_c tr(A B_c C B_c) = tr A tr C` (the
  `S ≡ 1` analogue of `sum_usedCoords_trace`).  Result: `𝔼 tr(H G E_a) = -∑_p Ŝ_{pa} 𝔼[g_p g_a]`,
  `Ŝ = t₁ S^{(B)} + ((u - t₁)/L²) J` (row sums `u`), and with `m z_u + u m² = -1`
  (`spectralM_quadratic`) the block identity (5.127)/(5.128), `OneLoop_selfcons`.
* Stability of `1 - m² Ŝ` in `max → max` (`OneLoop_stable`): the zero
  mode through `|1 - u m²| ≥ gapK κ` (`OneLoop_gapK_le_norm`), the rest through `Θ_{t₁ m²}` with the
  d = 2 row sum `1 + cShortRow κ (1 + log L)` (`OneLoop_theta_row_sum`, `xiRowBoundShort`).
* The bound at one grid time from the pathwise input on its good
  event and the envelope `‖G‖ ≤ η⁻¹` on the bad event (`OneLoop_expect_core`,
  `OneLoop_expect_bound`), and `gueGrid_expect_oneLoop`; the `log L` is absorbed by the
  `(d.size n)^ε` factor (`OneLoop_log_absorb`, as `step61_log_absorb`).

Conventions (`d = 2`): the path is `PathΩ d` with `gridTime` and a general grid `K` with
`K n ≠ 0`; `spectralZ`, `spectralM`; `gloop (d.L n) (d.W n) (blockMat M) z ⟨[true], [a]⟩`,
`a : Z2 (d.L n)`; the domination is `StochDomAt (Pgue d) d.size` and the explicit
`∀ ε > 0, ∀ᶠ n, ... ≤ (d.size n)^ε · Λ²`; `Tendsto d.size atTop atTop` is a
hypothesis; the block profile `Ŝ` lives on `Z2 L` with `σ = (u - t₁)/L²`; the stability constant is
`(1 + cShortRow κ (1 + log L))(1 + 1/gapK κ)`; the envelope of a `1`-loop is
`‖gloop‖ ≤ L² η⁻¹ ≤ N² Λ`, so the failure exponent is `D = 5` and the second
moments come from the good event directly (`momentDomAt_of_stochDomAt` needs a polynomial
envelope in the grid time, which `t₀ n < 1` alone does not give).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### Copies of the private algebra of `Grid.lean` -/

section Algebra

variable {d}

private lemma OneLoop_slice_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.slice d n (ω + ν) = Sizes.slice d n ω + Sizes.slice d n ν := rfl

private lemma OneLoop_slice_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.slice d n (a • ω) = a • Sizes.slice d n ω := rfl

private lemma OneLoop_slice_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ d) :
    Sizes.slice d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.slice d n (ω l) := by
  funext c
  simp [Sizes.slice, Finset.sum_apply]

private lemma OneLoop_seqXmat_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (ω + ν) = Sizes.seqXmat d n ω + Sizes.seqXmat d n ν := by
  unfold Sizes.seqXmat
  rw [OneLoop_slice_add, Xmat_add]

private lemma OneLoop_seqXmat_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (a • ω) = a • Sizes.seqXmat d n ω := by
  unfold Sizes.seqXmat
  rw [OneLoop_slice_smul, Xmat_smul]

private lemma OneLoop_seqXmat_sum {ι : Type*} (n : ℕ) (S : Finset ι)
    (ω : ι → Sizes.SeqΩ d) :
    Sizes.seqXmat d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.seqXmat d n (ω l) := by
  unfold Sizes.seqXmat
  rw [OneLoop_slice_sum]
  exact map_sum (Xlinear (d.L n) (d.W n)) (fun l => Sizes.slice d n (ω l)) S

private lemma OneLoop_real_smul_matrix {m : Type*} (r : ℝ) (M : Matrix m m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

end Algebra

/-! ### The mixed-step grid carrier -/

section MixedGrid

variable {d}

private def OneLoop_mixedStepMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    ℕ → Measure (Sizes.SeqΩ d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def OneLoop_mixedRawStep (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (c : Sizes.SeqCoord d)
    (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance OneLoop_mixedRawStep_isProbabilityMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (i : ℕ) : IsProbabilityMeasure (OneLoop_mixedRawStep v0 v1 c i) := by
  unfold OneLoop_mixedRawStep; split_ifs <;> infer_instance

private lemma OneLoop_mixedStepMeasure_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (i : ℕ) :
    OneLoop_mixedStepMeasure v0 v1 i
      = Measure.infinitePi (fun c => OneLoop_mixedRawStep v0 v1 c i) := by
  cases i <;> simp [OneLoop_mixedStepMeasure, OneLoop_mixedRawStep]

/-- Same nesting as `Path/Walk.lean`'s private `pathP'`: coordinates first, then the grid index. -/
private def OneLoop_mixedRaw (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    Measure (Sizes.SeqCoord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Sizes.SeqCoord d =>
    Measure.infinitePi (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i))

private def OneLoop_swapEquiv : (Sizes.SeqCoord d → ℕ → ℝ) → PathΩ d :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
    (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm

private lemma OneLoop_measurable_swapEquiv :
    Measurable (OneLoop_swapEquiv (d := d)) :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm.measurable)

private lemma OneLoop_swapEquiv_apply (X : Sizes.SeqCoord d → ℕ → ℝ) (i : ℕ)
    (c : Sizes.SeqCoord d) : OneLoop_swapEquiv X i c = X c i := by
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

private lemma OneLoop_mixedRaw_swap_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    (OneLoop_mixedRaw v0 v1).map OneLoop_swapEquiv
      = Measure.infinitePi (OneLoop_mixedStepMeasure v0 v1) := by
  have ha : (OneLoop_mixedRaw v0 v1).map ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Sizes.SeqCoord d × ℕ => OneLoop_mixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm
      (μ := fun (c : Sizes.SeqCoord d) (i : ℕ) => OneLoop_mixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi
        (fun p : Sizes.SeqCoord d × ℕ => OneLoop_mixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Sizes.SeqCoord d => OneLoop_mixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Sizes.SeqCoord d => OneLoop_mixedRawStep v0 v1 p.2 p.1)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)
  have hc : (Measure.infinitePi
        (fun p : ℕ × Sizes.SeqCoord d => OneLoop_mixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ)
      = Measure.infinitePi (OneLoop_mixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry
      (μ := fun (i : ℕ) (c : Sizes.SeqCoord d) => OneLoop_mixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (OneLoop_mixedStepMeasure_eq v0 v1 i).symm)
  change (OneLoop_mixedRaw v0 v1).map ((MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (OneLoop_mixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma**: the law is uniform `w` only from index `1`
on. -/
private lemma OneLoop_sumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
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
private lemma OneLoop_weightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
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
    OneLoop_sumIcc_map_gaussianReal_mixed hYm hY hY1 k
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

private lemma OneLoop_map_column_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [OneLoop_mixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi
      (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i)).map (fun y : ℕ → ℝ => y i)
        = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    have hi0 : i ≠ 0 := by omega
    simp [OneLoop_mixedRawStep, hi0]
  exact OneLoop_weightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law**. -/
private lemma OneLoop_map_combined_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (a b : ℝ)
    (k : ℕ) :
    (Measure.infinitePi (OneLoop_mixedStepMeasure v0 v1)).map
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
        ∘ OneLoop_swapEquiv
      = (fun X : Sizes.SeqCoord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      OneLoop_swapEquiv_apply]
  rw [← OneLoop_mixedRaw_swap_eq v0 v1,
    Measure.map_map hmeasComb OneLoop_measurable_swapEquiv, hcomp]
  have hfmeas : ∀ c : Sizes.SeqCoord d,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) := fun c => by
    have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
    have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Sizes.SeqCoord d =>
        Measure.infinitePi (fun i : ℕ => OneLoop_mixedRawStep v0 v1 c i))
      (f := fun c : Sizes.SeqCoord d => fun y : ℕ → ℝ =>
        a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [OneLoop_mixedRaw]
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => OneLoop_map_column_eq_mixed v0 v1 c a b k))

end MixedGrid

/-! ### Identification of `Pgue d` as the mixed-grid carrier, and the size slice -/

section Identification

variable {d}

private lemma OneLoop_Pgue_eq_mixed :
    Pgue d = Measure.infinitePi
      (OneLoop_mixedStepMeasure (Sizes.seqGvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord d` (generalising
`Sizes.seqP_map_slice` from `seqGvar d` to any variance family). -/
private lemma OneLoop_map_slice_infinitePi (w : Sizes.SeqCoord d → ℝ≥0) (n : ℕ) :
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

end Identification

/-! ### The one-time law of grid step `k` -/

/-- The real-coordinate combination read by grid step `k`: `a ω₀ + b ∑_{i=1}^k ω_i`. -/
def olComb (a b : ℝ) (k : ℕ) (ω : PathΩ d) : Sizes.SeqΩ d :=
  a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i

theorem olComb_measurable (a b : ℝ) (k : ℕ) : Measurable (olComb d a b k) := by
  have h1 : Measurable (fun ω : PathΩ d => ω 0) := measurable_pi_apply 0
  have h2 : Measurable (fun ω : PathΩ d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (h1.const_smul a).add (h2.const_smul b)

/-- The coordinate variances of step `k`: `a² seqGvar_c + k b² gueUnitVar_c`. -/
def olVar (a b : ℝ) (k : ℕ) : Sizes.SeqCoord d → ℝ≥0 := fun c =>
  NNReal.mk (a ^ 2) (sq_nonneg a) * Sizes.seqGvar d c
    + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar d c)

/-- **The one-time law of step `k`** (the D1 coordinate description): the combination has the
product Gaussian law with variances `olVar`. -/
theorem ol_map_comb (a b : ℝ) (k : ℕ) :
    (Pgue d).map (olComb d a b k)
      = Measure.infinitePi (fun c : Sizes.SeqCoord d => gaussianReal 0 (olVar d a b k c)) := by
  rw [OneLoop_Pgue_eq_mixed]
  exact OneLoop_map_combined_eq_mixed (Sizes.seqGvar d) (gueUnitVar d) a b k

/-- The size-`n` slice of the combination has the product Gaussian law `GaussianProduct.law`. -/
theorem ol_map_comb_slice (a b : ℝ) (k n : ℕ) :
    (Pgue d).map (fun ω => Sizes.slice d n (olComb d a b k ω))
      = GaussianProduct.law (fun c : Coord (d.L n) (d.W n) => olVar d a b k ⟨n, c⟩) := by
  have hm : Measurable (Sizes.slice d n) := Sizes.measurable_slice d n
  rw [show (fun ω => Sizes.slice d n (olComb d a b k ω)) = Sizes.slice d n ∘ olComb d a b k from rfl,
    ← Measure.map_map hm (olComb_measurable d a b k), ol_map_comb]
  exact OneLoop_map_slice_infinitePi (d := d) (olVar d a b k) n

/-- `gueH` at step `k` is `Xmat` of the size-`n` slice of the combination. -/
theorem ol_gueH_eq (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    gueH d t1 t0 K n k ω
      = Xmat (d.L n) (d.W n) (Sizes.slice d n (olComb d (Real.sqrt (t1 n))
          (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ))) k ω)) := by
  change _ = Sizes.seqXmat d n _
  unfold gueH olComb
  rw [OneLoop_seqXmat_add, OneLoop_seqXmat_smul, OneLoop_seqXmat_smul, OneLoop_seqXmat_sum,
    OneLoop_real_smul_matrix, OneLoop_real_smul_matrix]

/-! ## Fixed size: contraction of the step-`k` coordinate variances

`OneLoop_sum_orderedPairs_from_upper` is a copy of the private `sum_orderedPairs_from_upper`
(of `Hierarchy/ContractionSum.lean`). -/

section OrderedPairs

open Finset in
/-- An upper-triangular sum, with its transposed term, plus the diagonal is
the full ordered-pair sum. The key is injective, so its order chooses exactly
one orientation of every distinct pair. -/
private theorem OneLoop_sum_orderedPairs_from_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℕ) (hkey : Function.Injective key)
    (S : ι → ι → ℂ) (hS : ∀ i j, S i j = S j i)
    (f : ι → ι → ℂ) :
    ∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0) =
      ∑ i : ι, ∑ j : ι, S i j * f i j := by
  classical
  have point (i j : ι) : S i j * f i j =
      (if key i < key j then S i j * f i j else 0) +
      (if i = j then S i i * f i i else 0) +
      (if key j < key i then S i j * f i j else 0) := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
    · have hij : i = j := hkey h
      subst j
      simp
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
  have hswap :
      (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) =
      (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hS]
  calc
    (∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0)) =
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : key i < key j
          · have hne : i ≠ j := by
              intro he
              subst j
              exact (lt_irrefl _) hij
            simp [hij, hne, mul_add]
          · simp [hij]
    _ = (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
          rw [hswap]
    _ = ∑ i : ι, ∑ j : ι, S i j * f i j := by
          symm
          calc
            (∑ i : ι, ∑ j : ι, S i j * f i j) =
                ∑ i : ι, ∑ j : ι,
                  ((if key i < key j then S i j * f i j else 0) +
                   (if i = j then S i i * f i i else 0) +
                   (if key j < key i then S i j * f i j else 0)) := by
                    refine Finset.sum_congr rfl fun i _ =>
                      Finset.sum_congr rfl fun j _ => point i j
            _ = _ := by simp only [Finset.sum_add_distrib]

end OrderedPairs

section GUEContraction

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The unit-GUE coordinate contraction** on the physical lattice:
`∑_c w_c tr(A X_c C X_c) = tr A · tr C`, `w_c = 1` on the diagonal and `1/2` off it
(the `S ≡ 1` analogue of `Hierarchy/ContractionSum.lean`'s `sum_usedCoords_trace`). -/
private theorem OneLoop_sum_gue_fine (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c : Coord L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c) =
      Matrix.trace A * Matrix.trace C := by
  classical
  have splitCoord (f : Coord L W → ℂ) :
      ∑ c : Coord L W, f c = ∑ i : Idx L W, ∑ j : Idx L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx L W × Bool => f (i, jb))
  rw [splitCoord]
  have hpair : ∀ i j : Idx L W, ∑ b : Bool,
      (if (i, j, b).1 = (i, j, b).2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateMatrix L W (i, j, b) * C * coordinateMatrix L W (i, j, b)) =
      (if idxKey L W i < idxKey L W j then (fun _ _ : Idx L W => (1 : ℂ)) i j *
          ((fun i j : Idx L W => A i i * C j j) i j + (fun i j : Idx L W => A i i * C j j) j i)
        else if i = j then (fun _ _ : Idx L W => (1 : ℂ)) i i *
          (fun i j : Idx L W => A i i * C j j) i i else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
    · have hne : i ≠ j := fun he => by subst he; exact lt_irrefl _ h
      simp only [h, ite_true, Fintype.sum_bool, hne, ite_false]
      rw [trace_coordinate_real L W A C h, trace_coordinate_imag L W A C h]
      ring
    · subst h
      simp only [lt_irrefl, ite_false, ite_true, Fintype.sum_bool]
      rw [coordinateMatrix_diag_imag_zero]
      simp [trace_coordinate_diag L W A C i]
    · have hne : i ≠ j := fun he => by subst he; exact lt_irrefl _ h
      have hrev : ¬ idxKey L W i < idxKey L W j := not_lt_of_ge (le_of_lt h)
      simp [hrev, hne, coordinateMatrix_lower_zero L W h]
  simp_rw [hpair]
  rw [OneLoop_sum_orderedPairs_from_upper (idxKey L W) (idxKey_injective L W)
    (fun _ _ => (1 : ℂ)) (fun _ _ => rfl) (fun i j => A i i * C j j)]
  simp only [one_mul, Matrix.trace, Matrix.diag, Finset.sum_mul_sum]

private theorem OneLoop_trace_blockRelabel (M : Matrix (Idx L W) (Idx L W) ℂ) :
    Matrix.trace (Gauss.blockRelabel L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, Gauss.blockRelabel]
  exact (Equiv.sum_comp (splitEquiv L W).symm (fun i => M i i))

private theorem OneLoop_blockRelabel_mul (M N : Matrix (Idx L W) (Idx L W) ℂ) :
    Gauss.blockRelabel L W (M * N) = Gauss.blockRelabel L W M * Gauss.blockRelabel L W N :=
  (Matrix.submatrix_mul_equiv M N (splitEquiv L W).symm (splitEquiv L W).symm
    (splitEquiv L W).symm).symm

private theorem OneLoop_trace_coordinateBlock_pair
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (γ : Coord L W) :
    Matrix.trace (A * coordinateBlock L W γ * C * coordinateBlock L W γ) =
    Matrix.trace (A.submatrix (split L W) (split L W) * coordinateMatrix L W γ *
      C.submatrix (split L W) (split L W) * coordinateMatrix L W γ) := by
  let P := A.submatrix (split L W) (split L W)
  let Q := C.submatrix (split L W) (split L W)
  have hA : Gauss.blockRelabel L W P = A := blockRelabel_submatrix_split L W A
  have hC : Gauss.blockRelabel L W Q = C := blockRelabel_submatrix_split L W C
  change Matrix.trace (A * Gauss.blockRelabel L W (coordinateMatrix L W γ) *
    C * Gauss.blockRelabel L W (coordinateMatrix L W γ)) =
    Matrix.trace (P * coordinateMatrix L W γ * Q * coordinateMatrix L W γ)
  rw [← hA, ← hC, ← OneLoop_blockRelabel_mul L W, ← OneLoop_blockRelabel_mul L W,
    ← OneLoop_blockRelabel_mul L W]
  exact OneLoop_trace_blockRelabel L W _

/-- The unit-GUE coordinate contraction in block coordinates. -/
private theorem OneLoop_sum_gue_block (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ c : Coord L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateBlock L W c * C * coordinateBlock L W c) =
      Matrix.trace A * Matrix.trace C := by
  simp_rw [OneLoop_trace_coordinateBlock_pair L W]
  rw [OneLoop_sum_gue_fine L W]
  have h1 : Matrix.trace (A.submatrix (split L W) (split L W)) = Matrix.trace A := by
    rw [← OneLoop_trace_blockRelabel L W, blockRelabel_submatrix_split L W A]
  have h2 : Matrix.trace (C.submatrix (split L W) (split L W)) = Matrix.trace C := by
    rw [← OneLoop_trace_blockRelabel L W, blockRelabel_submatrix_split L W C]
  rw [h1, h2]

end GUEContraction

section FixedSize

open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem OneLoop_sub_mul_green {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) * green H z = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_sub_smul_one_of_im_ne_zero hH hz)
  exact Matrix.mul_nonsing_inv _ hdet

private theorem OneLoop_gloop_one (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (b : Z2 L) :
    gloop L W H z ⟨[true], [b]⟩ = Matrix.trace (green H z * Eblk L W b) :=
  by simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true]

/-- Resolvent identity at a single sample: `tr(H G E_a) = 1 + z tr(G E_a)`
(`Evolution/Step61.lean`, `step61_trace_HGE`). -/
private theorem OneLoop_trace_HGE (u : ℝ) (ω : Ω L W) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) :
    Matrix.trace (HflowBlock L W u ω * green (HflowBlock L W u ω) z * Eblk L W a) =
      1 + z * gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩ := by
  have h := OneLoop_sub_mul_green L W (HflowBlock_isHermitian L W u ω) hz
  have hHG : HflowBlock L W u ω * green (HflowBlock L W u ω) z =
      1 + z • green (HflowBlock L W u ω) z := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [hHG, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.one_mul, trace_Eblk_eq_one, OneLoop_gloop_one, smul_eq_mul]

private theorem OneLoop_norm_trace_mul3_le
    (A M C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ‖Matrix.trace (A * M * C)‖ ≤ (((L * W) ^ 2 : ℕ) : ℝ) * (‖A‖ * ‖M‖ * ‖C‖) := by
  have h := norm_matrix_trace_le_card_mul (A * M * C)
  rw [card_BlockIndex] at h
  refine h.trans ?_
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- A Gaussian coordinate times a bounded measurable complex observable is integrable under any
product Gaussian law. -/
private theorem OneLoop_integrable_coord_smul (v : Coord L W → ℝ≥0) (c : Coord L W)
    (g : Ω L W → ℂ) (hgm : Measurable g) {C : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω L W => ω c • g ω) (GaussianProduct.law v) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (GaussianProduct.law v) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((GaussianProduct.law v).map fun ω => ω c) := by
    have hmap : (GaussianProduct.law v).map (fun ω : Ω L W => ω c) = gaussianReal 0 (v c) :=
      Measure.infinitePi_map_eval _ c
    rw [hmap]
    exact RBM.integrable_id_gaussianReal (var := v c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (GaussianProduct.law v) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have h := hcoord.ofReal.bdd_mul hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  simpa [Complex.real_smul, mul_comm] using h

private theorem OneLoop_integrable_of_cont_bdd (v : Coord L W → ℝ≥0) {f : Ω L W → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (GaussianProduct.law v) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem OneLoop_green_norm_le (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω L W) :
    ‖green (HflowBlock L W u ω) z‖ ≤ (|z.im|)⁻¹ :=
  norm_green_le (HflowBlock_isHermitian L W u ω) (abs_pos.mpr hz) le_rfl

private theorem OneLoop_g_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    Continuous fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a) :=
  (continuous_matrixTrace L W).comp
    ((continuous_const.mul (continuous_green_HflowBlock_sample L W u hz)).mul continuous_const)

private theorem OneLoop_g'_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    Continuous fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a) := by
  have hGc := continuous_green_HflowBlock_sample L W u hz
  exact (continuous_matrixTrace L W).comp
    ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const)

private theorem OneLoop_g_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    ∃ C : ℝ, ∀ ω : Ω L W, ‖Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
    (‖coordinateBlock L W c‖ * (|z.im|)⁻¹ * ‖Eblk L W a‖), fun ω => ?_⟩
  refine (OneLoop_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  exact OneLoop_green_norm_le L W u hz ω

private theorem OneLoop_g'_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    ∃ C : ℝ, ∀ ω : Ω L W, ‖Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
    (‖coordinateBlock L W c‖ * ((|z.im|)⁻¹ * ‖Real.sqrt u • coordinateBlock L W c‖ *
      (|z.im|)⁻¹) * ‖Eblk L W a‖), fun ω => ?_⟩
  refine (OneLoop_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  rw [norm_neg]
  refine (norm_mul_le _ _).trans ?_
  gcongr
  · exact (norm_mul_le _ _).trans (by gcongr; exact OneLoop_green_norm_le L W u hz ω)
  · exact OneLoop_green_norm_le L W u hz ω

/-- One-coordinate Stein identity for `tr(B_c G E_a)` under an arbitrary product Gaussian law. -/
private theorem OneLoop_stein_coord (v : Coord L W → ℝ≥0) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (a : Z2 L) (c : Coord L W) :
    ∫ ω : Ω L W, ω c • Matrix.trace
        (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)
        ∂(GaussianProduct.law v) =
      (v c : ℝ) • ∫ ω : Ω L W, Matrix.trace
        (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
          (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
          Eblk L W a) ∂(GaussianProduct.law v) := by
  set B := coordinateBlock L W c with hB
  set E := Eblk L W a with hE
  let g : Ω L W → ℂ := fun ω => Matrix.trace (B * green (HflowBlock L W u ω) z * E)
  let g' : Ω L W → ℂ := fun ω => Matrix.trace (B * (-(green (HflowBlock L W u ω) z *
    (Real.sqrt u • B) * green (HflowBlock L W u ω) z)) * E)
  have hgc : Continuous g := OneLoop_g_cont L W u hz a c
  have hg'c : Continuous g' := OneLoop_g'_cont L W u hz a c
  have hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_HflowBlock_update L W u ω c hz
    have h2 := ((hasDerivAt_const (ω c) B).mul h1).mul_const E
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, g', zero_mul, zero_add, hB]
  have hgb : ∃ C : ℝ, ∀ ω : Ω L W, ‖g ω‖ ≤ C := OneLoop_g_bdd L W u hz a c
  have hg'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖g' ω‖ ≤ C := OneLoop_g'_bdd L W u hz a c
  exact GaussianProduct.stein v c g g' hgc hg'c hderiv hgb hg'b

private theorem OneLoop_HflowBlock_eq (u : ℝ) (ω : Ω L W) :
    HflowBlock L W u ω =
      (Real.sqrt u : ℂ) • ∑ c : Coord L W, ω c • coordinateBlock L W c := by
  rw [← Xblock_eq_sum_coordinates]
  ext i j
  simp [HflowBlock, Hflow]

end FixedSize

section FixedSize2

open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The mixed-profile contraction**: with coordinate variances `v_c = t₁ gvar_c + c₀ w_c`
(`w_c = 1` on the diagonal, `1/2` off it), the Stein sum collapses to the block profile
`Ŝ_{pa} = t₁ S^{(B)}_{pa} + c₀ W²`:
`∑_c (√u v_c) tr(B_c (-(G √u B_c G)) E_a) = -u ∑_p Ŝ_{pa} tr(G E_p) tr(G E_a)`.
The `t₁` part is `sum_coordinateBlock_trace_pair`; the `c₀` part is the unit-GUE
contraction `OneLoop_sum_gue_block` (`tr A tr C`, with `tr G = W² ∑_p tr(G E_p)`). -/
private theorem OneLoop_contraction (v : Coord L W → ℝ≥0) {t1 c0 : ℝ}
    (hv : ∀ c : Coord L W, (v c : ℝ) =
      t1 * (gvar L W c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (u : ℝ) (hu : 0 ≤ u) (G : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (a : Z2 L) :
    ∑ c : Coord L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c *
        (-(G * (Real.sqrt u • coordinateBlock L W c) * G)) * Eblk L W a) =
    -(u : ℂ) * ∑ p : Z2 L, ((t1 : ℂ) * SB L p a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
      (Matrix.trace (G * Eblk L W p) * Matrix.trace (G * Eblk L W a)) := by
  have hterm : ∀ c : Coord L W,
      ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c *
        (-(G * (Real.sqrt u • coordinateBlock L W c) * G)) * Eblk L W a) =
      -(u : ℂ) * (((v c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock L W c * (G * Eblk L W a) *
          coordinateBlock L W c)) := by
    intro c
    set B := coordinateBlock L W c
    have h1 : B * (-(G * (Real.sqrt u • B) * G)) * Eblk L W a =
        -(Real.sqrt u • (B * (G * B * (G * Eblk L W a)))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    have h2 : Matrix.trace (B * (G * B * (G * Eblk L W a))) =
        Matrix.trace (G * B * (G * Eblk L W a) * B) :=
      Matrix.trace_mul_comm _ _
    rw [h1, Matrix.trace_neg, Matrix.trace_smul, h2, Complex.real_smul]
    have h3 : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    linear_combination
      (-(((v c : ℝ) : ℂ) * Matrix.trace (G * B * (G * Eblk L W a) * B))) * h3
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hvC : ∀ c : Coord L W, ((v c : ℝ) : ℂ) =
      (t1 : ℂ) * ((gvar L W c : ℝ) : ℂ) + (c0 : ℂ) * (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) := by
    intro c
    rw [hv c]
    split_ifs <;> push_cast <;> ring
  have hsplit : ∑ c : Coord L W, ((v c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock L W c * (G * Eblk L W a) * coordinateBlock L W c) =
      (t1 : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock L W c * (G * Eblk L W a) * coordinateBlock L W c) +
      (c0 : ℂ) * ∑ c : Coord L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (G * coordinateBlock L W c * (G * Eblk L W a) * coordinateBlock L W c) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hvC c]
    ring
  rw [hsplit, sum_coordinateBlock_trace_pair L W G (G * Eblk L W a),
    OneLoop_sum_gue_block L W G (G * Eblk L W a)]
  have hq : ∀ q : Z2 L, Matrix.trace (G * Eblk L W a * Eblk L W q) =
      if a = q then (W : ℂ)⁻¹ ^ 2 * Matrix.trace (G * Eblk L W a) else 0 := by
    intro q
    rw [Matrix.mul_assoc, Eblk_mul_Eblk]
    split_ifs
    · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    · simp
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have htr : Matrix.trace G = (W : ℂ) ^ 2 * ∑ p : Z2 L, Matrix.trace (G * Eblk L W p) := by
    have h := congrArg (fun M => Matrix.trace (G * M)) (sum_Eblk L W)
    simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.mul_one, smul_eq_mul] at h
    rw [h]
    field_simp
  simp_rw [hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [htr]
  have e1 : (t1 : ℂ) * ((W : ℂ) ^ 2 * ∑ x : Z2 L, Matrix.trace (G * Eblk L W x) * SB L x a *
      ((W : ℂ)⁻¹ ^ 2 * Matrix.trace (G * Eblk L W a))) =
      ∑ x : Z2 L, (t1 : ℂ) * ((W : ℂ) ^ 2 * (Matrix.trace (G * Eblk L W x) * SB L x a *
        ((W : ℂ)⁻¹ ^ 2 * Matrix.trace (G * Eblk L W a)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  have e2 : (c0 : ℂ) * (((W : ℂ) ^ 2 * ∑ p : Z2 L, Matrix.trace (G * Eblk L W p)) *
      Matrix.trace (G * Eblk L W a)) =
      ∑ p : Z2 L, (c0 : ℂ) * ((W : ℂ) ^ 2 * Matrix.trace (G * Eblk L W p) *
        Matrix.trace (G * Eblk L W a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  have hlhs : ∀ p : Z2 L, (t1 : ℂ) * ((W : ℂ) ^ 2 * (Matrix.trace (G * Eblk L W p) * SB L p a *
      ((W : ℂ)⁻¹ ^ 2 * Matrix.trace (G * Eblk L W a)))) +
      (c0 : ℂ) * ((W : ℂ) ^ 2 * Matrix.trace (G * Eblk L W p) *
        Matrix.trace (G * Eblk L W a)) =
      ((t1 : ℂ) * SB L p a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
        (Matrix.trace (G * Eblk L W p) * Matrix.trace (G * Eblk L W a)) := by
    intro p
    push_cast
    field_simp
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => hlhs p

end FixedSize2

section FixedSize3

open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem OneLoop_gloop_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Z2 L) (ω : Ω L W) :
    ‖gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2)) := by
  have h := norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
    (abs_pos.mpr hz) le_rfl ⟨[true], [b]⟩ (by simp [LoopIdx.WF])
  simpa using h

private theorem OneLoop_gloop_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Z2 L) :
    Continuous fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ :=
  continuous_gloop_HflowBlock_sample L W u hz _ (by simp [LoopIdx.WF])

private theorem OneLoop_integrable_gloop (v : Coord L W → ℝ≥0) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (b : Z2 L) :
    Integrable (fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩)
      (GaussianProduct.law v) :=
  OneLoop_integrable_of_cont_bdd L W v (OneLoop_gloop_cont L W u hz b)
    (OneLoop_gloop_bdd L W u hz b)

private theorem OneLoop_integrable_gloop_mul (v : Coord L W → ℝ≥0) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (b a : Z2 L) :
    Integrable (fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ *
      gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩) (GaussianProduct.law v) := by
  refine OneLoop_integrable_of_cont_bdd L W v
    ((OneLoop_gloop_cont L W u hz b).mul (OneLoop_gloop_cont L W u hz a))
    (C := ((((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2))) *
      ((((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2)))) (fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (OneLoop_gloop_bdd L W u hz b ω) (OneLoop_gloop_bdd L W u hz a ω)
    (norm_nonneg _) ((norm_nonneg _).trans (OneLoop_gloop_bdd L W u hz b ω))

/-- **Stein step** under the product Gaussian `law v` of the step-`k` coordinate variances:
`𝔼 tr(H G E_a) = -u ∑_p Ŝ_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`, `Ŝ = t₁ S^{(B)} + c₀ W²`. -/
private theorem OneLoop_stein (v : Coord L W → ℝ≥0) {t1 c0 : ℝ}
    (hv : ∀ c : Coord L W, (v c : ℝ) =
      t1 * (gvar L W c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (u : ℝ) (hu : 0 ≤ u) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) :
    ∫ ω : Ω L W, Matrix.trace (HflowBlock L W u ω * green (HflowBlock L W u ω) z *
        Eblk L W a) ∂(GaussianProduct.law v) =
      -(u : ℂ) * ∑ p : Z2 L, ((t1 : ℂ) * SB L p a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∫ ω : Ω L W, gloop L W (HflowBlock L W u ω) z ⟨[true], [p]⟩ *
          gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩ ∂(GaussianProduct.law v) := by
  classical
  have hI1 : ∀ c : Coord L W, Integrable (fun ω : Ω L W => ω c • Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a))
      (GaussianProduct.law v) := by
    intro c
    obtain ⟨C, hC⟩ := OneLoop_g_bdd L W u hz a c
    exact OneLoop_integrable_coord_smul L W v c _ (OneLoop_g_cont L W u hz a c).measurable hC
  have hI2 : ∀ c : Coord L W, Integrable (fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a)) (GaussianProduct.law v) := by
    intro c
    obtain ⟨C, hC⟩ := OneLoop_g'_bdd L W u hz a c
    exact OneLoop_integrable_of_cont_bdd L W v (OneLoop_g'_cont L W u hz a c) hC
  have hexp : ∀ ω : Ω L W, Matrix.trace (HflowBlock L W u ω *
      green (HflowBlock L W u ω) z * Eblk L W a) =
      ∑ c : Coord L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
        (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)) := by
    intro ω
    generalize green (HflowBlock L W u ω) z = G
    rw [OneLoop_HflowBlock_eq L W u ω]
    simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      Complex.real_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun c _ => (hI1 c).const_mul _)]
  have hstein : ∀ c : Coord L W, ∫ ω : Ω L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a))
        ∂(GaussianProduct.law v) =
      ∫ ω : Ω L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) * Matrix.trace
        (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
          (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
          Eblk L W a) ∂(GaussianProduct.law v) := by
    intro c
    rw [integral_const_mul, OneLoop_stein_coord L W v u hz a c, integral_const_mul,
      Complex.real_smul, mul_assoc]
  simp_rw [hstein]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  have hpt : ∀ ω : Ω L W, ∑ c : Coord L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a) =
      -(u : ℂ) * ∑ p : Z2 L, ((t1 : ℂ) * SB L p a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
        (gloop L W (HflowBlock L W u ω) z ⟨[true], [p]⟩ *
        gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩) := by
    intro ω
    rw [OneLoop_contraction L W v hv u hu]
    simp only [OneLoop_gloop_one]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _
    (fun p _ => (OneLoop_integrable_gloop_mul L W v u hz p a).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

private theorem OneLoop_SB_symm (a b : Z2 L) : SB L b a = SB L a b :=
  congrFun (congrFun (SB_transpose L) a) b

private theorem OneLoop_sum_SB_col (hL : 3 ≤ L) (a : Z2 L) : ∑ b : Z2 L, SB L b a = 1 := by
  simp_rw [OneLoop_SB_symm L a]
  exact sum_SB_row L hL a

/-- **(5.127)/(5.128) before inversion** for the step-`k` law: with `x_b = 𝔼 g_b - m`,
`Z_b = g_b - m`, `Ŝ = t₁ S^{(B)} + c₀ W²`
(row sums `u = t₁ + L² c₀ W²`), `x_a = m² ∑_b Ŝ_{ba} x_b + m ∑_b Ŝ_{ba} 𝔼[Z_b Z_a]`. -/
private theorem OneLoop_selfcons (hL : 3 ≤ L) (v : Coord L W → ℝ≥0) {t1 c0 E u : ℝ}
    (hv : ∀ c : Coord L W, (v c : ℝ) =
      t1 * (gvar L W c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (hsum : t1 + (L : ℝ) ^ 2 * (c0 * (W : ℝ) ^ 2) = u) (hE : |E| < 2) (hu1 : u < 1)
    (a : Z2 L) :
    (∫ ω : Ω L W, gloop L W (HflowBlock L W 1 ω) (spectralZ E u) ⟨[true], [a]⟩
        ∂(GaussianProduct.law v)) - spectralM E =
      spectralM E ^ 2 * ∑ b : Z2 L, ((t1 : ℂ) * SB L b a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
        ((∫ ω : Ω L W, gloop L W (HflowBlock L W 1 ω) (spectralZ E u) ⟨[true], [b]⟩
          ∂(GaussianProduct.law v)) - spectralM E) +
      spectralM E * ∑ b : Z2 L, ((t1 : ℂ) * SB L b a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∫ ω : Ω L W,
        (gloop L W (HflowBlock L W 1 ω) (spectralZ E u) ⟨[true], [b]⟩ - spectralM E) *
          (gloop L W (HflowBlock L W 1 ω) (spectralZ E u) ⟨[true], [a]⟩ - spectralM E)
          ∂(GaussianProduct.law v) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  set z := spectralZ E u with hzdef
  set m := spectralM E with hm
  set Q := GaussianProduct.law v with hQ
  set Sh : Z2 L → ℂ := fun b => (t1 : ℂ) * SB L b a + ((c0 * (W : ℝ) ^ 2 : ℝ) : ℂ) with hSh
  set g : Z2 L → Ω L W → ℂ := fun b ω => gloop L W (HflowBlock L W 1 ω) z ⟨[true], [b]⟩ with hg
  have hgI : ∀ b, Integrable (g b) Q := fun b => OneLoop_integrable_gloop L W v 1 hz b
  have hgg : ∀ b, Integrable (fun ω => g b ω * g a ω) Q :=
    fun b => OneLoop_integrable_gloop_mul L W v 1 hz b a
  -- the Stein identity, integrated resolvent identity
  have hres : ∫ ω : Ω L W, Matrix.trace (HflowBlock L W 1 ω * green (HflowBlock L W 1 ω) z *
      Eblk L W a) ∂Q = 1 + z * ∫ ω, g a ω ∂Q := by
    simp_rw [OneLoop_trace_HGE L W 1 _ hz a]
    rw [integral_add (integrable_const _) ((hgI a).const_mul z), integral_const_mul,
      integral_const]
    simp
  have hst : 1 + z * ∫ ω, g a ω ∂Q = -∑ p : Z2 L, Sh p * ∫ ω, g p ω * g a ω ∂Q := by
    have h := OneLoop_stein L W v hv 1 zero_le_one hz a
    rw [hres] at h
    rw [h]
    simp only [Complex.ofReal_one, neg_mul, one_mul]
    rfl
  -- `m z + u m² = -1`
  have hmz : m * z + (u : ℂ) * m ^ 2 = -1 := by
    have hq := spectralM_quadratic (E := E) hE.le
    simp only [hzdef, spectralZ]
    linear_combination hq
  have hSum1 : ∑ b : Z2 L, Sh b = (u : ℂ) := by
    simp only [hSh, Finset.sum_add_distrib, ← Finset.mul_sum, OneLoop_sum_SB_col L hL a,
      Finset.sum_const, Finset.card_univ]
    have hc : (Fintype.card (Z2 L) : ℕ) = L ^ 2 := by
      simp [Z2, Fintype.card_prod, ZMod.card, pow_two]
    rw [hc, nsmul_eq_mul]
    rw [← hsum]
    push_cast
    ring
  change (∫ ω, g a ω ∂Q) - m =
    m ^ 2 * ∑ b : Z2 L, Sh b * ((∫ ω, g b ω ∂Q) - m) +
      m * ∑ b : Z2 L, Sh b * ∫ ω, (g b ω - m) * (g a ω - m) ∂Q
  -- centred product integrals
  have hZ : ∀ b, ∫ ω : Ω L W, (g b ω - m) * (g a ω - m) ∂Q =
      (∫ ω, g b ω * g a ω ∂Q) - m * (∫ ω, g b ω ∂Q) -
        m * (∫ ω, g a ω ∂Q) + m ^ 2 := by
    intro b
    have i1 : Integrable (fun ω : Ω L W => g b ω * g a ω) Q := hgg b
    have i2 : Integrable (fun ω : Ω L W => m * g b ω) Q := (hgI b).const_mul m
    have i3 : Integrable (fun ω : Ω L W => m * g a ω) Q := (hgI a).const_mul m
    have hfun : (fun ω : Ω L W => (g b ω - m) * (g a ω - m)) =
        fun ω => g b ω * g a ω - m * g b ω - m * g a ω + m ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω : Ω L W => g b ω * g a ω - m * g b ω) Q := i1.sub i2
    have i123 : Integrable (fun ω : Ω L W => g b ω * g a ω - m * g b ω - m * g a ω) Q :=
      i12.sub i3
    rw [hfun, integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  simp_rw [hZ]
  set Ia := ∫ ω, g a ω ∂Q with hIa
  have e1 : ∑ b : Z2 L, Sh b * ((∫ ω, g b ω ∂Q) - m) =
      (∑ b : Z2 L, Sh b * ∫ ω, g b ω ∂Q) - (u : ℂ) * m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum1]
  have e2 : ∑ b : Z2 L, Sh b * ((∫ ω, g b ω * g a ω ∂Q) -
      m * (∫ ω, g b ω ∂Q) - m * Ia + m ^ 2) =
      (∑ b : Z2 L, Sh b * ∫ ω, g b ω * g a ω ∂Q) -
        m * (∑ b : Z2 L, Sh b * ∫ ω, g b ω ∂Q) - (u : ℂ) * (m * Ia - m ^ 2) := by
    have hb : ∀ b : Z2 L, Sh b * ((∫ ω, g b ω * g a ω ∂Q) -
        m * (∫ ω, g b ω ∂Q) - m * Ia + m ^ 2) =
        Sh b * (∫ ω, g b ω * g a ω ∂Q) -
          m * (Sh b * ∫ ω, g b ω ∂Q) + Sh b * (m ^ 2 - m * Ia) :=
      fun b => by ring
    simp_rw [hb]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hSum1]
    ring
  rw [e1, e2]
  set T1 := ∑ b : Z2 L, Sh b * ∫ ω, g b ω ∂Q
  set T2 := ∑ b : Z2 L, Sh b * ∫ ω, g b ω * g a ω ∂Q
  linear_combination (-m) * hst + Ia * hmz

end FixedSize3

/-! ## Deterministic inversion of `x = m² Ŝ x + y` in `max → max` -/

section Stability

open RBM.Evol

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem OneLoop_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * spectralM E ^ 2‖ ^ 2 = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (spectralM E).re = -E / 2 := by simp [spectralM]
  have him := spectralM_im E
  have hs := spectralM_sqrt_sq hE
  rw [pow_two (spectralM E), Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

private theorem OneLoop_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < KLoop.gapK κ := by
  unfold KLoop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

/-- The bulk gap `c_κ ≤ |1 - t m²|` for `t ≥ 0`, `|E| ≤ 2 - κ`. -/
private theorem OneLoop_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) : KLoop.gapK κ ≤ ‖1 - (t : ℂ) * spectralM E ^ 2‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : KLoop.gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * spectralM E ^ 2‖ ^ 2 := by
    rw [OneLoop_norm_one_sub_sq hE2]
    have hg0 := (OneLoop_gapK_pos hκ hκ2).le
    have hg1 : KLoop.gapK κ ^ 2 ≤ 1 := by
      have := min_le_left 1 (Real.sqrt (κ * (4 - κ) / 2))
      have h1 : KLoop.gapK κ ≤ 1 := this
      nlinarith
    have hg2 : KLoop.gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
      have h1 : KLoop.gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
      have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
        Real.sq_sqrt (by nlinarith)
      nlinarith
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have := (OneLoop_gapK_pos hκ hκ2).le
  have := norm_nonneg (1 - (t : ℂ) * spectralM E ^ 2)
  nlinarith

variable (L : ℕ) [NeZero L]

/-- As `step61_theta_solve` (`Evolution/Step61.lean`): `x = ξ S x + y` is solved by
`x = Θ_ξ y`. -/
private theorem OneLoop_theta_solve (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {x y : Z2 L → ℂ}
    (h : ∀ a, x a = ξ * ∑ b, SB L b a * x b + y a) (a : Z2 L) :
    x a = ∑ a', Theta L ξ a a' * y a' := by
  have hy : y = (1 - ξ • SB L) *ᵥ x := by
    funext c
    have hc := h c
    have hm : ((1 - ξ • SB L) *ᵥ x) c = x c - ξ * ∑ b, SB L c b * x b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    rw [hm]
    have e : ∑ b, SB L b c * x b = ∑ b, SB L c b * x b :=
      Finset.sum_congr rfl fun b _ => by rw [OneLoop_SB_symm L c b]
    rw [e] at hc
    linear_combination -hc
  have hx : Theta L ξ *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Theta_mul L hL hξ, Matrix.one_mulVec]
  rw [← hx]
  rfl

/-- Row sum of `Θ_{t m²}` on `Z_L²`: `1 + cShortRow κ (1 + log L)` (as `step61_theta_row_sum` of
`Evolution/Step61.lean`; `xiRowBoundShort` at `s = 0`, `σ = +`). -/
private theorem OneLoop_theta_row_sum (hL : 3 ≤ L) {κ E t : ℝ} (hκ : 0 < κ)
    (hEκ : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Z2 L) :
    ∑ a' : Z2 L, ‖Theta L ((t : ℂ) * spectralM E ^ 2) a a'‖ ≤
      1 + cShortRow κ * (1 + Real.log L) := by
  have h := xiRowBoundShort L hL κ E hκ hEκ true 0 t le_rfl ht0 ht1 a
  have hxi : ∀ a' : Z2 L,
      xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 t a a' =
        Theta L ((t : ℂ) * spectralM E ^ 2) a a' - (1 : Matrix (Z2 L) (Z2 L) ℂ) a a' := by
    intro a'
    simp only [xiMat, ukerMat, KLoop.mSig, ite_true, Complex.ofReal_zero, zero_mul, zero_smul,
      sub_zero, Matrix.one_mul, Matrix.sub_apply]
    rw [sq]
  have hone : ∑ a' : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖ = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  calc ∑ a' : Z2 L, ‖Theta L ((t : ℂ) * spectralM E ^ 2) a a'‖
      ≤ ∑ a' : Z2 L, (‖xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 t a a'‖ +
          ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖) := by
        refine Finset.sum_le_sum fun a' _ => ?_
        have : Theta L ((t : ℂ) * spectralM E ^ 2) a a' =
            xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 t a a' +
              (1 : Matrix (Z2 L) (Z2 L) ℂ) a a' := by
          rw [hxi a']; ring
        rw [this]
        exact norm_add_le _ _
    _ = ∑ a' : Z2 L, ‖xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 t a a'‖ +
          ∑ a' : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖ := Finset.sum_add_distrib
    _ ≤ cShortRow κ * (1 + Real.log L) + 1 := add_le_add h hone.le
    _ = 1 + cShortRow κ * (1 + Real.log L) := by ring

/-- **Stability of `1 - m² Ŝ` in `max → max`**: `Ŝ = t₁ S^{(B)} + σ J` on `Z_L²` with row sums
`u = t₁ + L² σ < 1`.  The average is
recovered through `1 - u m²`, `|1 - u m²| ≥ c_κ = gapK κ`; the rest is `Θ_{t₁ m²}`, whose row sum
is `1 + cShortRow κ (1 + log L)` (d = 2: the `log L`, not the d = 1 constant). -/
private theorem OneLoop_stable (hL : 3 ≤ L) {κ E t1 σ u : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht1 : 0 ≤ t1) (ht1' : t1 < 1) (hσ : 0 ≤ σ)
    (hu : t1 + (L : ℝ) ^ 2 * σ = u) (hu1 : u < 1) {x y : Z2 L → ℂ}
    (h : ∀ a, x a = spectralM E ^ 2 * ∑ b, ((t1 : ℂ) * SB L b a + (σ : ℂ)) * x b + y a)
    {B : ℝ} (hB : ∀ a, ‖y a‖ ≤ B) (a : Z2 L) :
    ‖x a‖ ≤ (1 + cShortRow κ * (1 + Real.log L)) * (1 + 1 / KLoop.gapK κ) * B := by
  classical
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  set m := spectralM E with hm
  have hm1 : ‖m‖ = 1 := norm_spectralM hE2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a)
  have hgpos : 0 < KLoop.gapK κ := OneLoop_gapK_pos hκ hκ2
  set g := KLoop.gapK κ with hg
  have hLσ : (L : ℝ) ^ 2 * σ ≤ 1 := by linarith
  have hu0 : 0 ≤ u := by rw [← hu]; positivity
  have hc : (Fintype.card (Z2 L) : ℕ) = L ^ 2 := by
    simp [Z2, Fintype.card_prod, ZMod.card, pow_two]
  set S := ∑ b, x b with hS
  -- the row sums of the profile
  have hrow : ∀ b : Z2 L, ∑ a : Z2 L, ((t1 : ℂ) * SB L b a + (σ : ℂ)) = (u : ℂ) := by
    intro b
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_SB_row L hL b, Finset.sum_const,
      Finset.card_univ, hc, nsmul_eq_mul]
    rw [← hu]
    push_cast
    ring
  -- the average: `(1 - u m²) ∑ x = ∑ y`
  have hsum : (1 - (u : ℂ) * m ^ 2) * S = ∑ a, y a := by
    have e1 : ∑ a : Z2 L, ∑ b : Z2 L, ((t1 : ℂ) * SB L b a + (σ : ℂ)) * x b = (u : ℂ) * S := by
      rw [Finset.sum_comm, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, hrow b]
    have h1 : S = m ^ 2 * ((u : ℂ) * S) + ∑ a, y a := by
      conv_lhs => rw [hS, Finset.sum_congr rfl fun a _ => h a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1]
    linear_combination h1
  have hden : g ≤ ‖1 - (u : ℂ) * m ^ 2‖ := OneLoop_gapK_le_norm hκ hE hu0
  have hY : ‖∑ a, y a‖ ≤ (L : ℝ) ^ 2 * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖y a‖ ≤ ∑ _a : Z2 L, B := Finset.sum_le_sum fun a _ => hB a
      _ = (L : ℝ) ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]; push_cast; ring
  have hSle : ‖S‖ ≤ (L : ℝ) ^ 2 * B / g := by
    rw [le_div_iff₀ hgpos]
    calc ‖S‖ * g ≤ ‖S‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖∑ a, y a‖ := by rw [← hsum, norm_mul, mul_comm]
      _ ≤ (L : ℝ) ^ 2 * B := hY
  -- the remainder `r = y + m² σ ∑ x`
  set r : Z2 L → ℂ := fun a => y a + m ^ 2 * (σ : ℂ) * S with hr
  have hrle : ∀ a, ‖r a‖ ≤ (1 + 1 / g) * B := by
    intro a
    calc ‖r a‖ ≤ ‖y a‖ + ‖m ^ 2 * (σ : ℂ) * S‖ := norm_add_le _ _
      _ ≤ B + σ * ((L : ℝ) ^ 2 * B / g) := by
          gcongr
          · exact hB a
          · rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hσ]
            exact mul_le_mul_of_nonneg_left hSle hσ
      _ = B + ((L : ℝ) ^ 2 * σ) * B / g := by ring
      _ ≤ B + 1 * B / g := by gcongr
      _ = (1 + 1 / g) * B := by ring
  -- `x = ξ S^{(B)} x + r`, `ξ = t₁ m²`
  have hξ : ‖(t1 : ℂ) * m ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, hm1, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht1]
    exact ht1'
  have hxr : ∀ a, x a = ((t1 : ℂ) * m ^ 2) * ∑ b, SB L b a * x b + r a := by
    intro a
    have h2 : ∑ b : Z2 L, ((t1 : ℂ) * SB L b a + (σ : ℂ)) * x b =
        (t1 : ℂ) * ∑ b : Z2 L, SB L b a * x b + (σ : ℂ) * S := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hS]
    rw [h a, h2]
    simp only [hr]
    ring
  rw [OneLoop_theta_solve L hL hξ hxr a]
  have hrow_sum := OneLoop_theta_row_sum L hL hκ hE ht1 ht1' a
  calc ‖∑ a', Theta L ((t1 : ℂ) * m ^ 2) a a' * r a'‖
      ≤ ∑ a', ‖Theta L ((t1 : ℂ) * m ^ 2) a a'‖ * ((1 + 1 / g) * B) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hrle a') (norm_nonneg _)
    _ = (∑ a', ‖Theta L ((t1 : ℂ) * m ^ 2) a a'‖) * ((1 + 1 / g) * B) := by
        rw [Finset.sum_mul]
    _ ≤ (1 + cShortRow κ * (1 + Real.log L)) * ((1 + 1 / g) * B) :=
        mul_le_mul_of_nonneg_right hrow_sum (by positivity)
    _ = (1 + cShortRow κ * (1 + Real.log L)) * (1 + 1 / g) * B := by ring

end Stability

/-! ## From the pathwise input to the expectation bound at one grid time -/

section Core

open scoped Matrix.Norms.L2Operator
open RBM.Evol

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The core of the bound at one grid time**: given a measurable exceptional set
`T`, `μ.real T ≤ δ`, off which every `1`-loop is `≤ ρ Λ`, and a global envelope `Env` with
`δ Env² ≤ 4 Λ²`, then `‖𝔼 g_a - m‖ ≤ (1 + cShortRow κ (1 + log L))(1 + 1/c_κ)(ρ² + 4) Λ²`. -/
private theorem OneLoop_expect_core (hL : 3 ≤ L) {κ E t1 c0 u : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht1 : 0 ≤ t1) (hc0 : 0 ≤ c0)
    (hsum : t1 + (L : ℝ) ^ 2 * (c0 * (W : ℝ) ^ 2) = u) (hu1 : u < 1)
    (v : Coord L W → ℝ≥0)
    (hv : ∀ c : Coord L W, (v c : ℝ) =
      t1 * (gvar L W c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
    (φ : Ω' → Ω L W) (hφ : Measurable φ) (hmap : μ.map φ = GaussianProduct.law v)
    {Λ ρ Env δ : ℝ} (T : Set Ω') (hT : MeasurableSet T)
    (hEnv : ∀ (b : Z2 L) (ω' : Ω L W),
      ‖gloop L W (HflowBlock L W 1 ω') (spectralZ E u) ⟨[true], [b]⟩ - spectralM E‖ ≤ Env)
    (hTδ : μ.real T ≤ δ) (hbad : δ * Env ^ 2 ≤ 4 * Λ ^ 2)
    (hgood : ∀ ω ∉ T, ∀ b : Z2 L,
      ‖gloop L W (HflowBlock L W 1 (φ ω)) (spectralZ E u) ⟨[true], [b]⟩ - spectralM E‖ ≤ ρ * Λ)
    (a : Z2 L) :
    ‖(∫ ω, gloop L W (HflowBlock L W 1 (φ ω)) (spectralZ E u) ⟨[true], [a]⟩ ∂μ) - spectralM E‖ ≤
      (1 + cShortRow κ * (1 + Real.log L)) * (1 + 1 / KLoop.gapK κ) *
        ((ρ ^ 2 + 4) * Λ ^ 2) := by
  classical
  have hE2 : |E| < 2 := by linarith
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE2))
  set z := spectralZ E u with hzdef
  set m := spectralM E with hm
  have hm1 : ‖m‖ = 1 := norm_spectralM hE2.le
  set Q := GaussianProduct.law v with hQ
  set σ : ℝ := c0 * (W : ℝ) ^ 2 with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  have hLσ0 : 0 ≤ (L : ℝ) ^ 2 * σ := by positivity
  have hu0 : 0 ≤ u := by rw [← hsum]; positivity
  have ht1' : t1 < 1 := by linarith
  have hc : (Fintype.card (Z2 L) : ℕ) = L ^ 2 := by
    simp [Z2, Fintype.card_prod, ZMod.card, pow_two]
  set Φ : Z2 L → Ω L W → ℂ := fun b ω' => gloop L W (HflowBlock L W 1 ω') z ⟨[true], [b]⟩ - m
    with hΦ
  have hΦc : ∀ b, Continuous (Φ b) := fun b => (OneLoop_gloop_cont L W 1 hz b).sub continuous_const
  have hΦm : ∀ b, Measurable (Φ b) := fun b => (hΦc b).measurable
  have hΦb : ∀ b ω', ‖Φ b ω'‖ ≤ Env := fun b ω' => hEnv b ω'
  have hEnv0 : 0 ≤ Env := (norm_nonneg _).trans (hΦb 0 0)
  -- transfer of integrals along `φ`
  have hint : ∀ {F : Ω L W → ℂ}, Continuous F →
      ∫ ω, F (φ ω) ∂μ = ∫ ω', F ω' ∂Q := by
    intro F hF
    have h := integral_map hφ.aemeasurable (hF.aestronglyMeasurable (μ := μ.map φ))
    rw [hmap] at h
    exact h.symm
  -- the first moments and the self-consistent equation
  have hgI : ∀ b, Integrable (fun ω' => gloop L W (HflowBlock L W 1 ω') z ⟨[true], [b]⟩) Q :=
    fun b => OneLoop_integrable_gloop L W v 1 hz b
  have hxg : ∀ b, ∫ ω', Φ b ω' ∂Q = (∫ ω', gloop L W (HflowBlock L W 1 ω') z ⟨[true], [b]⟩ ∂Q) - m := by
    intro b
    simp only [hΦ]
    rw [integral_sub (hgI b) (integrable_const _), integral_const]
    simp
  set Y : Z2 L → Z2 L → ℂ := fun b a' => ∫ ω', Φ b ω' * Φ a' ω' ∂Q with hY
  set x : Z2 L → ℂ := fun b => ∫ ω', Φ b ω' ∂Q with hx
  set y : Z2 L → ℂ := fun a' => m * ∑ b : Z2 L, ((t1 : ℂ) * SB L b a' + (σ : ℂ)) * Y b a' with hy
  have hxy : ∀ a', x a' = m ^ 2 * ∑ b : Z2 L, ((t1 : ℂ) * SB L b a' + (σ : ℂ)) * x b + y a' := by
    intro a'
    have h := OneLoop_selfcons L W hL v hv hsum hE2 hu1 a'
    simp only [hx, hy, hY, hxg] at h ⊢
    exact h
  -- the pair bound from the pathwise input
  have hpair : ∀ b a', ‖Y b a'‖ ≤ (ρ * Λ) ^ 2 + 4 * Λ ^ 2 := by
    intro b a'
    have hYeq : Y b a' = ∫ ω, Φ b (φ ω) * Φ a' (φ ω) ∂μ := (hint ((hΦc b).mul (hΦc a'))).symm
    have hpt : ∀ ω, ‖Φ b (φ ω) * Φ a' (φ ω)‖ ≤
        (ρ * Λ) ^ 2 + T.indicator (fun _ => Env ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω, norm_mul]
        calc ‖Φ b (φ ω)‖ * ‖Φ a' (φ ω)‖ ≤ Env * Env :=
              mul_le_mul (hΦb b (φ ω)) (hΦb a' (φ ω)) (norm_nonneg _) hEnv0
          _ = Env ^ 2 := (sq Env).symm
          _ ≤ (ρ * Λ) ^ 2 + Env ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
      · rw [Set.indicator_of_notMem hω, add_zero, norm_mul]
        have h1 := hgood ω hω b
        have h2 := hgood ω hω a'
        calc ‖Φ b (φ ω)‖ * ‖Φ a' (φ ω)‖ ≤ (ρ * Λ) * (ρ * Λ) :=
              mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
          _ = (ρ * Λ) ^ 2 := (sq _).symm
    have hmeas : Measurable (fun ω => Φ b (φ ω) * Φ a' (φ ω)) :=
      ((hΦm b).comp hφ).mul ((hΦm a').comp hφ)
    have hint1 : Integrable (fun ω => ‖Φ b (φ ω) * Φ a' (φ ω)‖) μ := by
      refine Integrable.of_bound (C := Env * Env) hmeas.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [norm_norm, norm_mul]
      exact mul_le_mul (hΦb b (φ ω)) (hΦb a' (φ ω)) (norm_nonneg _) hEnv0
    have hint2 : Integrable (fun ω => (ρ * Λ) ^ 2 + T.indicator (fun _ => Env ^ 2) ω) μ :=
      (integrable_const _).add ((integrable_const _).indicator hT)
    rw [hYeq]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono hint1 hint2 hpt).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hT), integral_const,
      integral_indicator_const _ hT]
    simp only [probReal_univ, smul_eq_mul]
    have : μ.real T * Env ^ 2 ≤ 4 * Λ ^ 2 := (mul_le_mul_of_nonneg_right hTδ (sq_nonneg _)).trans hbad
    linarith
  -- the row norm of the profile
  have hrowS : ∀ a' : Z2 L, ∑ b : Z2 L, ‖(t1 : ℂ) * SB L b a' + (σ : ℂ)‖ ≤ u := by
    intro a'
    have hsb : ∑ b : Z2 L, ‖SB L b a'‖ = 1 := by
      simp_rw [OneLoop_SB_symm L a']
      have h := congrArg (fun r : NNReal => (r : ℝ)) (sum_nnnorm_SB_row L hL a')
      simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using h
    calc ∑ b : Z2 L, ‖(t1 : ℂ) * SB L b a' + (σ : ℂ)‖
        ≤ ∑ b : Z2 L, (t1 * ‖SB L b a'‖ + σ) := Finset.sum_le_sum fun b _ => by
          calc ‖(t1 : ℂ) * SB L b a' + (σ : ℂ)‖ ≤ ‖(t1 : ℂ) * SB L b a'‖ + ‖(σ : ℂ)‖ :=
                norm_add_le _ _
            _ = t1 * ‖SB L b a'‖ + σ := by
                rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                  Real.norm_eq_abs, abs_of_nonneg ht1, abs_of_nonneg hσ0]
      _ = t1 + (L : ℝ) ^ 2 * σ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsb, Finset.sum_const, Finset.card_univ,
            hc, nsmul_eq_mul]
          push_cast
          ring
      _ = u := by rw [hσdef]; exact hsum
  have hyle : ∀ a', ‖y a'‖ ≤ (ρ * Λ) ^ 2 + 4 * Λ ^ 2 := by
    intro a'
    have hK0 : 0 ≤ (ρ * Λ) ^ 2 + 4 * Λ ^ 2 := by positivity
    calc ‖y a'‖ = ‖m‖ * ‖∑ b : Z2 L, ((t1 : ℂ) * SB L b a' + (σ : ℂ)) * Y b a'‖ := by
          rw [hy]; exact norm_mul _ _
      _ ≤ 1 * (∑ b : Z2 L, ‖(t1 : ℂ) * SB L b a' + (σ : ℂ)‖ * ((ρ * Λ) ^ 2 + 4 * Λ ^ 2)) := by
          rw [hm1]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b _ => ?_)) zero_le_one
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpair b a') (norm_nonneg _)
      _ = (∑ b : Z2 L, ‖(t1 : ℂ) * SB L b a' + (σ : ℂ)‖) * ((ρ * Λ) ^ 2 + 4 * Λ ^ 2) := by
          rw [one_mul, Finset.sum_mul]
      _ ≤ u * ((ρ * Λ) ^ 2 + 4 * Λ ^ 2) := mul_le_mul_of_nonneg_right (hrowS a') hK0
      _ ≤ 1 * ((ρ * Λ) ^ 2 + 4 * Λ ^ 2) := mul_le_mul_of_nonneg_right hu1.le hK0
      _ = (ρ * Λ) ^ 2 + 4 * Λ ^ 2 := one_mul _
  -- stability
  have hxa := OneLoop_stable L hL hκ hE ht1 ht1' hσ0 hsum hu1 (x := x) (y := y)
    (fun a' => hxy a') hyle a
  have hconc : (∫ ω, gloop L W (HflowBlock L W 1 (φ ω)) z ⟨[true], [a]⟩ ∂μ) - m = x a := by
    rw [hint (OneLoop_gloop_cont L W 1 hz a), hx]
    simp only
    rw [hxg a]
  rw [hconc]
  calc ‖x a‖ ≤ (1 + cShortRow κ * (1 + Real.log L)) * (1 + 1 / KLoop.gapK κ) *
        ((ρ * Λ) ^ 2 + 4 * Λ ^ 2) := hxa
    _ = (1 + cShortRow κ * (1 + Real.log L)) * (1 + 1 / KLoop.gapK κ) *
        ((ρ ^ 2 + 4) * Λ ^ 2) := by ring

end Core

section Wrapper

open scoped Matrix.Norms.L2Operator
open RBM.Evol

/-- `blockMat (Xmat ω) = HflowBlock 1 ω`. -/
private theorem OneLoop_blockMat_Xmat (L W : ℕ) [NeZero L] [NeZero W] (ω : Ω L W) :
    blockMat (Xmat L W ω) = HflowBlock L W 1 ω := by
  unfold HflowBlock Hflow blockMat
  simp

/-- **The bound at one grid time**:
for a set `Bset` of probability `≤ N^{-5}` off which every `1`-loop of step `k` is
`≤ ρ Λ`, `Λ = (N η_u)^{-1}`: `‖𝔼⟨(G-m)E_a⟩‖ ≤ C_κ(L) (ρ² + 4) Λ²`, with the d = 2 constant
`C_κ(L) = (1 + cShortRow κ (1 + log L))(1 + 1/c_κ)`.  (`D = 5`: the envelope of a `1`-loop is
`L² η⁻¹ ≤ N² Λ`.) -/
private theorem OneLoop_expect_bound {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : |E n| ≤ 2 - κ) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n)
    (ht0 : t0 n < 1) (K : ℕ → ℕ) (hK : K n ≠ 0) (k : ℕ) (hkK : k ≤ K n)
    {ρ : ℝ} (Bset : Set (PathΩ d))
    (hPB : Pgue d Bset ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(5 : ℝ))))
    (hgood : ∀ ω ∉ Bset, ∀ b : Z2 (d.L n),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
          (spectralZ (E n) (gridTime t1 t0 K n k)) ⟨[true], [b]⟩ - spectralM (E n)‖
        ≤ ρ * (gueScale d E n (gridTime t1 t0 K n k))⁻¹)
    (a : Z2 (d.L n)) :
    ‖(∫ ω, gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
          (spectralZ (E n) (gridTime t1 t0 K n k)) ⟨[true], [a]⟩ ∂(Pgue d)) - spectralM (E n)‖
      ≤ (1 + cShortRow κ * (1 + Real.log (d.L n : ℝ))) * (1 + 1 / KLoop.gapK κ) *
        ((ρ ^ 2 + 4) * (gueScale d E n (gridTime t1 t0 K n k))⁻¹ ^ 2) := by
  classical
  have hL3 := d.three_le_L n
  have hW0 := d.W_pos n
  have hLpos : (0 : ℝ) < d.L n := by exact_mod_cast (show 0 < d.L n by omega)
  have hWpos : (0 : ℝ) < d.W n := by exact_mod_cast hW0
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNeq]; positivity
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ d.size n := Nat.succ_le_of_lt (by rw [Sizes.size_eq]; positivity)
    rw [hNdef]
    exact_mod_cast h1
  -- the grid time
  set Δ := gridStep t1 t0 K n with hΔdef
  set u := gridTime t1 t0 K n k with hudef
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hKpos.le
  have hkK' : (k : ℝ) ≤ K n := by exact_mod_cast hkK
  have hkΔ : (k : ℝ) * Δ ≤ t0 n - t1 n := by
    calc (k : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hkK' hΔ0
      _ = t0 n - t1 n := by rw [hΔdef, gridStep]; field_simp
  have hu_eq : u = t1 n + (k : ℝ) * Δ := rfl
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  have hu0 : 0 ≤ u := by rw [hu_eq]; linarith
  have hu1 : u < 1 := by rw [hu_eq]; linarith
  have hE2 : |E n| < 2 := by linarith
  have hm1 : ‖spectralM (E n)‖ = 1 := norm_spectralM hE2.le
  set η := etaT (E n) u with hηdef
  have hηpos : 0 < η := etaT_pos hE2 hu1
  have hηle : η ≤ 1 := by
    have him : (spectralM (E n)).im ≤ 1 := by
      have h := Complex.abs_im_le_norm (spectralM (E n))
      rw [hm1] at h
      exact (le_abs_self _).trans h
    have him0 := spectralM_im_pos hE2
    rw [hηdef, etaT]
    nlinarith
  set Λ := (gueScale d E n u)⁻¹ with hΛdef
  have hscale : gueScale d E n u = N * η := rfl
  have hΛ : Λ = (N * η)⁻¹ := by rw [hΛdef, hscale]
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hηinv : η⁻¹ = N * Λ := by rw [hΛ]; field_simp
  -- the one-time law of step `k`
  set aa := Real.sqrt (t1 n) with haa
  set bb := Real.sqrt (Δ / N) with hbb
  have haa2 : aa ^ 2 = t1 n := Real.sq_sqrt ht1
  have hbb2 : bb ^ 2 = Δ / N := Real.sq_sqrt (div_nonneg hΔ0 hNpos.le)
  set c0 : ℝ := (k : ℝ) * bb ^ 2 with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  have hsum : t1 n + (d.L n : ℝ) ^ 2 * (c0 * (d.W n : ℝ) ^ 2) = u := by
    rw [hc0, hbb2, hu_eq, hNeq]
    field_simp
  have hv : ∀ c : Coord (d.L n) (d.W n), (olVar d aa bb k ⟨n, c⟩ : ℝ) =
      t1 n * (gvar (d.L n) (d.W n) c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2) := by
    intro c
    have hg : ((Sizes.seqGvar d ⟨n, c⟩ : ℝ≥0) : ℝ) = (gvar (d.L n) (d.W n) c : ℝ) := rfl
    simp only [olVar, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, hg, haa2]
    by_cases hc : c.1 = c.2.1
    · simp [gueUnitVar, hc, hc0]
    · simp [gueUnitVar, hc, hc0]
      ring
  have hmap := ol_map_comb_slice d aa bb k n
  have hφ : Measurable (fun ω : PathΩ d => Sizes.slice d n (olComb d aa bb k ω)) :=
    (Sizes.measurable_slice d n).comp (olComb_measurable d aa bb k)
  have hblock : ∀ ω : PathΩ d, blockMat (gueH d t1 t0 K n k ω) =
      HflowBlock (d.L n) (d.W n) 1 (Sizes.slice d n (olComb d aa bb k ω)) := by
    intro ω
    rw [ol_gueH_eq]
    exact OneLoop_blockMat_Xmat _ _ _
  -- the measurable exceptional set
  set T := toMeasurable (Pgue d) Bset with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hBT : Bset ⊆ T := subset_toMeasurable _ _
  have hTδ : (Pgue d).real T ≤ N ^ (-(5 : ℝ)) := by
    rw [measureReal_def, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPB
  -- the global envelope
  have hz : (spectralZ (E n) u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE2))
  have hzη : η ≤ |(spectralZ (E n) u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE2))]
    exact le_rfl
  have hgl : ∀ (b : Z2 (d.L n)) (ω' : Ω (d.L n) (d.W n)),
      ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) 1 ω') (spectralZ (E n) u)
        ⟨[true], [b]⟩‖ ≤ (d.L n : ℝ) ^ 2 * η⁻¹ := by
    intro b ω'
    have h := norm_gloop_le_crude (d.L n) (d.W n) (HflowBlock_isHermitian (d.L n) (d.W n) 1 ω')
      hηpos hzη ⟨[true], [b]⟩ (by simp [LoopIdx.WF])
    refine h.trans (le_of_eq ?_)
    have hW : (d.W n : ℝ) ≠ 0 := hWpos.ne'
    simp only [List.length_singleton, pow_one]
    push_cast
    field_simp
  have hL2N : (d.L n : ℝ) ^ 2 ≤ N := by
    rw [hNeq]
    have hW2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW0)
    nlinarith [sq_nonneg (d.L n : ℝ)]
  have hEnv : ∀ (b : Z2 (d.L n)) (ω' : Ω (d.L n) (d.W n)),
      ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) 1 ω') (spectralZ (E n) u)
        ⟨[true], [b]⟩ - spectralM (E n)‖ ≤ 2 * N ^ 2 * Λ := by
    intro b ω'
    have h1 : 1 ≤ η⁻¹ := by rw [le_inv_comm₀ one_pos hηpos, inv_one]; exact hηle
    have hη0 : 0 ≤ η⁻¹ := (inv_pos.2 hηpos).le
    calc ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) 1 ω') (spectralZ (E n) u)
          ⟨[true], [b]⟩ - spectralM (E n)‖
        ≤ ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) 1 ω') (spectralZ (E n) u)
          ⟨[true], [b]⟩‖ + ‖spectralM (E n)‖ := norm_sub_le _ _
      _ ≤ (d.L n : ℝ) ^ 2 * η⁻¹ + (d.L n : ℝ) ^ 2 * η⁻¹ := by
          rw [hm1]
          refine add_le_add (hgl b ω') ?_
          have hL1 : (1 : ℝ) ≤ (d.L n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ d.L n))
          nlinarith
      _ ≤ N * η⁻¹ + N * η⁻¹ := by gcongr
      _ = 2 * N ^ 2 * Λ := by rw [hηinv]; ring
  have hbad : N ^ (-(5 : ℝ)) * (2 * N ^ 2 * Λ) ^ 2 ≤ 4 * Λ ^ 2 := by
    have h5 : N ^ (-(5 : ℝ)) = (N ^ 5)⁻¹ := by
      rw [Real.rpow_neg hNpos.le]; norm_cast
    calc N ^ (-(5 : ℝ)) * (2 * N ^ 2 * Λ) ^ 2 = 4 * Λ ^ 2 / N := by
          rw [h5]; field_simp; ring
      _ ≤ 4 * Λ ^ 2 := by
          rw [div_le_iff₀ hNpos]
          have h4 : 0 ≤ 4 * Λ ^ 2 := by positivity
          calc 4 * Λ ^ 2 = 4 * Λ ^ 2 * 1 := (mul_one _).symm
            _ ≤ 4 * Λ ^ 2 * N := mul_le_mul_of_nonneg_left hN1 h4
  have hgood' : ∀ ω ∉ T, ∀ b : Z2 (d.L n),
      ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) 1
          (Sizes.slice d n (olComb d aa bb k ω))) (spectralZ (E n) u) ⟨[true], [b]⟩ -
        spectralM (E n)‖ ≤ ρ * Λ := by
    intro ω hω b
    have h := hgood ω (fun h => hω (hBT h)) b
    rwa [hblock ω] at h
  have key := OneLoop_expect_core (d.L n) (d.W n) hL3 hκ hE ht1 hc00 hsum hu1
    (fun c => olVar d aa bb k ⟨n, c⟩) hv (Pgue d)
    (fun ω : PathΩ d => Sizes.slice d n (olComb d aa bb k ω)) hφ hmap T hTm hEnv hTδ hbad
    hgood' a
  have hfun : (fun ω : PathΩ d => gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
      (spectralZ (E n) u) ⟨[true], [a]⟩) = fun ω : PathΩ d => gloop (d.L n) (d.W n)
        (HflowBlock (d.L n) (d.W n) 1 (Sizes.slice d n (olComb d aa bb k ω)))
        (spectralZ (E n) u) ⟨[true], [a]⟩ := funext fun ω => by rw [hblock ω]
  rw [hfun]
  exact key

end Wrapper

section Main

open scoped Matrix.Norms.L2Operator
open RBM.Evol

/-- A fixed constant times `1 + a (1 + log x)` is eventually `≤ x^δ`. -/
private theorem OneLoop_log_absorb (a C δ : ℝ) (ha : 0 ≤ a) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, (1 + a * (1 + Real.log x)) * C ≤ x ^ δ := by
  set B : ℝ := (1 + a) * C + a * C * (2 / δ) + 1 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (1 + a) * C := by positivity
    have : 0 ≤ a * C * (2 / δ) := by positivity
    linarith
  have ht : Tendsto (fun x : ℝ => x ^ (δ / 2)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [ht.eventually (eventually_ge_atTop B), eventually_gt_atTop 0] with x hxB hx0
  set t : ℝ := x ^ (δ / 2) with htdef
  have ht1 : 1 ≤ t := hB1.trans hxB
  have hlog : Real.log x ≤ t / (δ / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hxδ : x ^ δ = t * t := by
    rw [htdef, ← Real.rpow_add hx0]; congr 1; ring
  rw [hxδ]
  have h1 : (1 + a * (1 + Real.log x)) * C ≤ (1 + a) * C + a * C * (t / (δ / 2)) := by
    have : a * C * Real.log x ≤ a * C * (t / (δ / 2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith
  have h2 : a * C * (t / (δ / 2)) = a * C * (2 / δ) * t := by field_simp
  have h3 : (1 + a) * C ≤ (1 + a) * C * t := by
    have : 0 ≤ (1 + a) * C := by positivity
    nlinarith
  have h4 : (1 + a) * C * t + a * C * (2 / δ) * t ≤ B * t := by
    rw [hB]; nlinarith
  nlinarith

/-- **Lemma 5.15 for the GUE-phase grid**: given the pathwise
`1`-loop bound `‖⟨(G - m)E_a⟩‖ ≺ (N η_u)^{-1}` at every grid time of the GUE-phase path, the
`1`-loop expectation satisfies `‖𝔼⟨(G - m)E_a⟩‖ ≤ N^ε (N η_u)^{-2}` eventually, for every `ε > 0`,
uniformly in the grid time and the block label.  Proof: the one-time law of grid step `k`
(`ol_map_comb_slice`), Stein's identity for that product Gaussian with the mixed block profile
`Ŝ = t₁ S^{(B)} + ((u - t₁)/L²) J` (`OneLoop_selfcons`), stability of `1 - m² Ŝ` through
`|1 - u m²| ≥ gapK κ` and `Θ_{t₁ m²}` (`OneLoop_stable`), and the pathwise input on its good event
with the envelope `‖G‖ ≤ η⁻¹` on the bad event (`OneLoop_expect_bound`, `D = 5`). -/
theorem gueGrid_expect_oneLoop {κ : ℝ} (hκ : 0 < κ) {E t1 t0 : ℕ → ℝ} {K : ℕ → ℕ}
    (hsize : Tendsto (fun n => d.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hK : ∀ n, K n ≠ 0)
    (h1 : StochDomAt (Pgue d) d.size
      (fun n (p : Fin (K n + 1) × Z2 (d.L n)) ω =>
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n p.1 ω))
            (spectralZ (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - spectralM (E n)‖)
      (fun n p _ => (gueScale d E n (gridTime t1 t0 K n p.1))⁻¹)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Z2 (d.L n),
      ‖(∫ ω, gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n p.1 ω))
          (spectralZ (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue d)) -
        spectralM (E n)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε * (gueScale d E n (gridTime t1 t0 K n p.1))⁻¹ ^ 2 := by
  intro ε hε
  have hsz : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hsize
  have hκ2 : κ ≤ 2 := by
    have := hE 0
    linarith [abs_nonneg (E 0)]
  have hgpos : 0 < KLoop.gapK κ := OneLoop_gapK_pos hκ hκ2
  set g := KLoop.gapK κ with hg
  have hcs : 0 ≤ cShortRow κ := by
    have hg0 : 0 ≤ g := hgpos.le
    unfold cShortRow
    have : 0 ≤ 2 * cProp5 := by unfold cProp5; positivity
    positivity
  set C : ℝ := 8 * (1 + 1 / g) + 1 with hC
  have hCpos : 0 < C := by positivity
  have hbad := h1 (ε / 4) (by positivity) 5 (by norm_num)
  have habs := hsz.eventually (OneLoop_log_absorb (cShortRow κ) C (ε / 2) hcs hCpos
    (half_pos hε))
  filter_upwards [hbad, habs, hsz.eventually (eventually_ge_atTop 1)] with n hPn hn hN1r
  rintro ⟨k, a⟩
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hL3 := d.three_le_L n
  have hL1r : (1 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast (by omega : 1 ≤ d.L n)
  have hL2N : (d.L n : ℝ) ^ 2 ≤ N := by
    rw [hNdef, Sizes.size_eq]
    push_cast
    have hW2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast d.W_pos n)
    nlinarith [sq_nonneg (d.L n : ℝ)]
  have hLN : (d.L n : ℝ) ≤ N := (le_self_pow₀ hL1r two_ne_zero).trans hL2N
  have hbound := OneLoop_expect_bound d hκ n (hE n) (ht1 n) (ht10 n) (ht0 n) K (hK n) k
    (Nat.lt_succ_iff.1 k.isLt) (ρ := N ^ (ε / 4)) _ hPn
    (fun ω hω b => by
      by_contra hc
      exact hω ⟨(k, b), lt_of_not_ge hc⟩) a
  -- the constants
  set Λ2 := (gueScale d E n (gridTime t1 t0 K n k))⁻¹ ^ 2 with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by rw [hΛ2]; exact sq_nonneg _
  set X := N ^ (ε / 2) with hX
  have hρ : (N ^ (ε / 4)) ^ 2 = X := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hNε : N ^ ε = X * X := by
    rw [hX, ← Real.rpow_add hN0]; ring_nf
  set Rl := 1 + cShortRow κ * (1 + Real.log (d.L n : ℝ)) with hRl
  have hlogL : 0 ≤ Real.log (d.L n : ℝ) := Real.log_nonneg hL1r
  have hRl1 : 1 ≤ Rl := by
    have : 0 ≤ cShortRow κ * (1 + Real.log (d.L n : ℝ)) := by positivity
    linarith
  have hRlN : Rl ≤ 1 + cShortRow κ * (1 + Real.log N) := by
    have hlog : Real.log (d.L n : ℝ) ≤ Real.log N := Real.log_le_log (by positivity) hLN
    rw [hRl]
    gcongr
  have hg1 : 0 ≤ 1 + 1 / g := by positivity
  have hCs : 8 * (Rl * (1 + 1 / g)) + 1 ≤ X := by
    calc 8 * (Rl * (1 + 1 / g)) + 1 ≤ Rl * (8 * (1 + 1 / g) + 1) := by nlinarith
      _ ≤ (1 + cShortRow κ * (1 + Real.log N)) * (8 * (1 + 1 / g) + 1) := by gcongr
      _ ≤ X := hn
  have hCs0 : 0 ≤ Rl * (1 + 1 / g) := by positivity
  have hX1 : 1 ≤ X := by nlinarith
  have hXC : Rl * (1 + 1 / g) * (X + 4) ≤ X * X := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by linarith : (0 : ℝ) ≤ X - 8 * (Rl * (1 + 1 / g)) - 1),
      mul_nonneg hCs0 (by linarith : (0 : ℝ) ≤ X - 1)]
  rw [hρ] at hbound
  calc _ ≤ Rl * (1 + 1 / g) * ((X + 4) * Λ2) := hbound
    _ = (Rl * (1 + 1 / g) * (X + 4)) * Λ2 := by ring
    _ ≤ (X * X) * Λ2 := mul_le_mul_of_nonneg_right hXC hΛ20
    _ = N ^ ε * Λ2 := by rw [hNε]

end Main


end RBM.Univ.GUEPhase

end
