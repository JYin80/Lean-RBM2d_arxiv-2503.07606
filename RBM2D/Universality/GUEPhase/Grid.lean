/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Walk
import RBM2D.Path.Step2Props
import RBM2D.Universality.OU
import RBM2D.Universality.ZeroModeProfile
import RBM2D.Green.Pins
import RBM2D.Main.ZRescale
import RBM2D.Defs.StochDom

/-!
# The GUE-phase grid carrier, path and one-time laws (7.25)/(7.26), `d = 2`

The carrier `Pgue`, the path `gueH`, its algebra, the mixed-grid identification, the laws
`map_gueH_zero`, `map_gueH_last`, `gueGridK`, `gueScale`, `GUEPathBounds`, and the homogeneity
lemmas.

The GUE-phase flow of §7.2, `H̃_u = √t₁ X + √(u - t₁) Y`, is realised as a discrete grid walk: the
band field `Sizes.seqP d` at grid step `0` and independent unit GUE fields `gueUnit d` at every
later step, on the path carrier `PathΩ d`.  Only the one-time laws at step `0` and at the last
step `K n` are proved (against `Sizes.seqHflow` and against `ouMat`, (7.25)/(7.26)).

Notation (`d = 2`): the sizes are `Sizes`, the sample space is `Sizes.SeqΩ d` with coordinates
`Sizes.SeqCoord d`, the index set is `Idx (d.L n) (d.W n)`, the path space is `PathΩ d` with
`gridTime/gridStep` and the filtration `filt d`; the band law is `Sizes.seqP d`, the matrix is
`Sizes.seqXmat d n`, the flow is `Sizes.seqHflow`, and the matrix size is `d.size n = (W L)²`;
the OU marginal is `ouMat (d.L n) (d.W n) τ` on `ouP (d.L n) (d.W n)`; loops are
`gloop (d.L n) (d.W n) (blockMat M) z (loopOf σ a)` (as `ZTrace`, `Main/ZRescale.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### The GUE-phase grid measure -/

/-- Unit GUE coordinate variance: `1` on the diagonal, `1/2` per real component off it. -/
def gueUnitVar (c : Sizes.SeqCoord d) : ℝ≥0 := if c.2.1 = c.2.2.1 then 1 else 1 / 2

/-- One unit GUE coordinate field, all sizes at once. -/
def gueUnit : Measure (Sizes.SeqΩ d) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueUnitVar d c)

/-- Step laws: the band field at step `0`, unit GUE fields at steps `k ≥ 1`. -/
def gueStepMeasure : ℕ → Measure (Sizes.SeqΩ d)
  | 0 => Sizes.seqP d
  | _ + 1 => gueUnit d

/-- The GUE-phase grid measure on the path carrier `PathΩ d`. -/
def Pgue : Measure (PathΩ d) := Measure.infinitePi (gueStepMeasure d)

instance gueUnit_isProbabilityMeasure : IsProbabilityMeasure (gueUnit d) := by
  unfold gueUnit; infer_instance

instance gueStepMeasure_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (gueStepMeasure d k) := by
  cases k <;> simp only [gueStepMeasure] <;> infer_instance

instance Pgue_isProbabilityMeasure : IsProbabilityMeasure (Pgue d) := by
  unfold Pgue; infer_instance

/-! ### The GUE-phase grid path -/

/-- The GUE-phase grid path `H_k = √t₁ X + √(Δ/N) ∑_{i=1}^k Y_i`, `Δ = (t₀ - t₁)/K`,
`N = d.size n = (W L)²`. -/
def gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  (Real.sqrt (t1 n) : ℂ) • Sizes.seqXmat d n (ω 0) +
    (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ) •
      ∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω i)

/-- `N η_u` of the GUE phase, `N = (W L)²`. -/
def gueScale (E : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ := ((d.size n : ℕ) : ℝ) * etaT (E n) u

/-- **The output of the §7.2 random layer** at the grid times `k ≤ K n`: (7.28) for loops of
length `1 ≤ m ≤ n₀` against a primitive family `Kt`, and `‖G̃ - m‖_max ≺ (N η_u)^{-1/2}`.
Loops are indexed by `(Fin m → Bool) × (Fin m → Z2 L)` with `idx = loopOf σ a` and evaluated on
`blockMat` (as `ZTrace`, `Main/ZRescale.lean`). -/
structure GUEPathBounds (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) : Prop where
  lk : ∀ m : ℕ, 1 ≤ m → m ≤ n0 → StochDomAt (Pgue d) d.size
    (fun n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Z2 (d.L n))) ω =>
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n p.1 ω))
          (spectralZ (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 K n p.1) (loopOf p.2.1 p.2.2)‖)
    (fun n p _ => (gueScale d E n (gridTime t1 t0 K n p.1))⁻¹ ^ m)
  localLaw : StochDomAt (Pgue d) d.size
    (fun n (p : Fin (K n + 1) × (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))) ω =>
      ‖(green (gueH d t1 t0 K n p.1 ω) (spectralZ (E n) (gridTime t1 t0 K n p.1)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
        p.2.1 p.2.2‖)
    (fun n p _ => (gueScale d E n (gridTime t1 t0 K n p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-- The grid size: `K n = (d.size n + 1)^(32 n₀ + 64)`. -/
def gueGridK (n0 n : ℕ) : ℕ := (d.size n + 1) ^ (32 * n0 + 64)

theorem gueGridK_ne_zero (n0 n : ℕ) : gueGridK d n0 n ≠ 0 := by
  unfold gueGridK; positivity

/-! ### Pointwise algebraic identities -/

section Algebra

variable {d}

private lemma GUEPhaseGrid_slice_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.slice d n (ω + ν) = Sizes.slice d n ω + Sizes.slice d n ν := rfl

private lemma GUEPhaseGrid_slice_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.slice d n (a • ω) = a • Sizes.slice d n ω := rfl

private lemma GUEPhaseGrid_slice_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ d) :
    Sizes.slice d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.slice d n (ω l) := by
  funext c
  simp [Sizes.slice, Finset.sum_apply]

private lemma GUEPhaseGrid_seqXmat_add (n : ℕ) (ω ν : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (ω + ν) = Sizes.seqXmat d n ω + Sizes.seqXmat d n ν := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_add, Xmat_add]

private lemma GUEPhaseGrid_seqXmat_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (a • ω) = a • Sizes.seqXmat d n ω := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_smul, Xmat_smul]

private lemma GUEPhaseGrid_seqXmat_sum {ι : Type*} (n : ℕ) (S : Finset ι)
    (ω : ι → Sizes.SeqΩ d) :
    Sizes.seqXmat d n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.seqXmat d n (ω l) := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_sum]
  exact map_sum (Xlinear (d.L n) (d.W n)) (fun l => Sizes.slice d n (ω l)) S

private lemma GUEPhaseGrid_real_smul_matrix {m : Type*} (r : ℝ) (M : Matrix m m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

private lemma GUEPhaseGrid_measurable_seqXentry (n : ℕ) (i j : Idx (d.L n) (d.W n)) :
    Measurable fun ω : Sizes.SeqΩ d => Sizes.seqXmat d n ω i j :=
  (measurable_Xentry (d.L n) (d.W n) i j).comp (Sizes.measurable_slice d n)

private lemma GUEPhaseGrid_gueH_apply (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (i j : Idx (d.L n) (d.W n)) (ω : PathΩ d) :
    gueH d t1 t0 K n k ω i j
      = (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat d n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω l) i j := by
  simp [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Finset.mul_sum]

end Algebra

theorem gueH_isHermitian (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    (gueH d t1 t0 K n k ω).IsHermitian := by
  have h0 : (Sizes.seqXmat d n (ω 0))ᴴ = Sizes.seqXmat d n (ω 0) :=
    Sizes.seqXmat_isHermitian d n (ω 0)
  have hsum : (∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω i))ᴴ
      = ∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω i) := by
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => Sizes.seqXmat_isHermitian d n (ω i)
  change (gueH d t1 t0 K n k ω)ᴴ = gueH d t1 t0 K n k ω
  unfold gueH
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    show star (Real.sqrt (t1 n) : ℂ) = (Real.sqrt (t1 n) : ℂ) from Complex.conj_ofReal _,
    show star (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ)
        = (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ)
      from Complex.conj_ofReal _,
    h0, hsum]

theorem gueH_adapted (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (i j : Idx (d.L n) (d.W n)) :
    StronglyMeasurable[filt d k] (fun ω : PathΩ d => gueH d t1 t0 K n k ω i j) := by
  rw [stronglyMeasurable_iff_measurable]
  have heq : (fun ω : PathΩ d => gueH d t1 t0 K n k ω i j) =
      fun ω => (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat d n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω l) i j :=
    funext fun ω => GUEPhaseGrid_gueH_apply t1 t0 K n k i j ω
  rw [heq]
  have hmeas : ∀ l : ℕ, l ≤ k → Measurable[filt d k] (fun ω : PathΩ d => ω l) := by
    intro l hl
    have : (fun ω : PathΩ d => ω l)
        = (fun g : Set.Iic k → Sizes.SeqΩ d => g ⟨l, hl⟩)
          ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k) := rfl
    rw [this]
    exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k))
  apply Measurable.add
  · exact ((GUEPhaseGrid_measurable_seqXentry n i j).comp (hmeas 0 (by omega))).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l hl =>
      (GUEPhaseGrid_measurable_seqXentry n i j).comp
        (hmeas l (by simp only [Finset.mem_Icc] at hl; omega))

theorem gueH_measurable (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueH d t1 t0 K n k) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have heq : (fun ω : PathΩ d => gueH d t1 t0 K n k ω i j) =
      fun ω => (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat d n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat d n (ω l) i j :=
    funext fun ω => GUEPhaseGrid_gueH_apply t1 t0 K n k i j ω
  rw [heq]
  apply Measurable.add
  · exact ((GUEPhaseGrid_measurable_seqXentry n i j).comp (measurable_pi_apply 0)).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l _ =>
      (GUEPhaseGrid_measurable_seqXentry n i j).comp (measurable_pi_apply l)

/-! ### A mixed-step grid carrier

`mixedStepMeasure v0 v1` has the same shape as `gueStepMeasure`: the coordinate variance family
`v0` at step `0`, `v1` at steps `≥ 1`.  With `(v0, v1) = (seqGvar d, gueUnitVar d)` it is
`gueStepMeasure`.  The "swap" computation of `Path/Walk.lean` (private `pathP'`, `swapEquiv`,
`pathP_swap_eq`, `map_combined_eq`), generalised from a constant step law to this mixed law. -/

section MixedGrid

variable {d}

private def GUEPhaseGrid_mixedStepMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    ℕ → Measure (Sizes.SeqΩ d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def GUEPhaseGrid_mixedRawStep (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (c : Sizes.SeqCoord d)
    (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance GUEPhaseGrid_mixedRawStep_isProbabilityMeasure (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (i : ℕ) : IsProbabilityMeasure (GUEPhaseGrid_mixedRawStep v0 v1 c i) := by
  unfold GUEPhaseGrid_mixedRawStep; split_ifs <;> infer_instance

private lemma GUEPhaseGrid_mixedStepMeasure_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (i : ℕ) :
    GUEPhaseGrid_mixedStepMeasure v0 v1 i
      = Measure.infinitePi (fun c => GUEPhaseGrid_mixedRawStep v0 v1 c i) := by
  cases i <;> simp [GUEPhaseGrid_mixedStepMeasure, GUEPhaseGrid_mixedRawStep]

/-- Same nesting as `Path/Walk.lean`'s private `pathP'`: coordinates first, then the grid index. -/
private def GUEPhaseGrid_mixedRaw (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    Measure (Sizes.SeqCoord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Sizes.SeqCoord d =>
    Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i))

private def GUEPhaseGrid_swapEquiv : (Sizes.SeqCoord d → ℕ → ℝ) → PathΩ d :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
    (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm

private lemma GUEPhaseGrid_measurable_swapEquiv :
    Measurable (GUEPhaseGrid_swapEquiv (d := d)) :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm.measurable)

private lemma GUEPhaseGrid_swapEquiv_apply (X : Sizes.SeqCoord d → ℕ → ℝ) (i : ℕ)
    (c : Sizes.SeqCoord d) : GUEPhaseGrid_swapEquiv X i c = X c i := by
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

private lemma GUEPhaseGrid_mixedRaw_swap_eq (v0 v1 : Sizes.SeqCoord d → ℝ≥0) :
    (GUEPhaseGrid_mixedRaw v0 v1).map GUEPhaseGrid_swapEquiv
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1) := by
  have ha : (GUEPhaseGrid_mixedRaw v0 v1).map ((MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Sizes.SeqCoord d × ℕ => GUEPhaseGrid_mixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm
      (μ := fun (c : Sizes.SeqCoord d) (i : ℕ) => GUEPhaseGrid_mixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi
        (fun p : Sizes.SeqCoord d × ℕ => GUEPhaseGrid_mixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Sizes.SeqCoord d => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Sizes.SeqCoord d => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1)
      (Equiv.prodComm (Sizes.SeqCoord d) ℕ)
  have hc : (Measure.infinitePi
        (fun p : ℕ × Sizes.SeqCoord d => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ)
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry
      (μ := fun (i : ℕ) (c : Sizes.SeqCoord d) => GUEPhaseGrid_mixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (GUEPhaseGrid_mixedStepMeasure_eq v0 v1 i).symm)
  change (GUEPhaseGrid_mixedRaw v0 v1).map ((MeasurableEquiv.curry ℕ (Sizes.SeqCoord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord d => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord d) ℕ)) ∘
      (MeasurableEquiv.curry (Sizes.SeqCoord d) ℕ ℝ).symm)
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma**: the law is uniform `w` only from index `1`
on. -/
private lemma GUEPhaseGrid_sumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
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
private lemma GUEPhaseGrid_weightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
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
    GUEPhaseGrid_sumIcc_map_gaussianReal_mixed hYm hY hY1 k
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

private lemma GUEPhaseGrid_map_column_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0)
    (c : Sizes.SeqCoord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [GUEPhaseGrid_mixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi
      (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map (fun y : ℕ → ℝ => y i)
        = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    have hi0 : i ≠ 0 := by omega
    simp [GUEPhaseGrid_mixedRawStep, hi0]
  exact GUEPhaseGrid_weightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law**. -/
private lemma GUEPhaseGrid_map_combined_eq_mixed (v0 v1 : Sizes.SeqCoord d → ℝ≥0) (a b : ℝ)
    (k : ℕ) :
    (Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1)).map
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
        ∘ GUEPhaseGrid_swapEquiv
      = (fun X : Sizes.SeqCoord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      GUEPhaseGrid_swapEquiv_apply]
  rw [← GUEPhaseGrid_mixedRaw_swap_eq v0 v1,
    Measure.map_map hmeasComb GUEPhaseGrid_measurable_swapEquiv, hcomp]
  have hfmeas : ∀ c : Sizes.SeqCoord d,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) := fun c => by
    have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
    have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Sizes.SeqCoord d =>
        Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i))
      (f := fun c : Sizes.SeqCoord d => fun y : ℕ → ℝ =>
        a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [GUEPhaseGrid_mixedRaw]
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => GUEPhaseGrid_map_column_eq_mixed v0 v1 c a b k))

end MixedGrid

/-! ### Identification of `Pgue d` as the mixed-grid carrier, and the size slice -/

section Identification

variable {d}

private lemma GUEPhaseGrid_Pgue_eq_mixed :
    Pgue d = Measure.infinitePi
      (GUEPhaseGrid_mixedStepMeasure (Sizes.seqGvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord d` (generalising
`Sizes.seqP_map_slice` from `seqGvar d` to any variance family). -/
private lemma GUEPhaseGrid_map_slice_infinitePi (w : Sizes.SeqCoord d → ℝ≥0) (n : ℕ) :
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

private lemma GUEPhaseGrid_measurable_Xmat (L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j

/-- Scaling every coordinate of an independent centred Gaussian family by `s` multiplies the
variances by `s²`. -/
private lemma GUEPhaseGrid_map_smul_infinitePi {ι : Type*} (s : ℝ) (v : ι → ℝ≥0) :
    (Measure.infinitePi fun c => gaussianReal 0 (v c)).map (fun x : ι → ℝ => s • x)
      = Measure.infinitePi (fun c => gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s) * v c)) := by
  have hfmeas : ∀ c : ι, Measurable (s * ·) := fun c => by fun_prop
  have h1 : (Measure.infinitePi fun c => gaussianReal 0 (v c)).map
        (fun x : ι → ℝ => fun c => s * x c)
      = Measure.infinitePi (fun c => (gaussianReal 0 (v c)).map (s * ·)) :=
    Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (v c)) (f := fun _ => (s * ·)) hfmeas
  have heq : (fun x : ι → ℝ => s • x) = (fun x : ι → ℝ => fun c => s * x c) := by
    funext x c; simp [smul_eq_mul]
  rw [heq, h1]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]

end Identification

/-! ### The one-time laws (7.25)/(7.26) -/

/-- Step `0` has the law of the band flow at `t₁`. -/
theorem map_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (_ht1 : 0 ≤ t1 n) :
    (Pgue d).map (gueH d t1 t0 K n 0) = (Sizes.seqP d).map (Sizes.seqHflow d n (t1 n)) := by
  have heq : gueH d t1 t0 K n 0 = (Sizes.seqHflow d n (t1 n)) ∘ (fun ω : PathΩ d => ω 0) := by
    funext ω
    change gueH d t1 t0 K n 0 ω = Sizes.seqHflow d n (t1 n) (ω 0)
    unfold gueH
    simp [Sizes.seqHflow_eq_smul]
  have hmeasHflow : Measurable (Sizes.seqHflow d n (t1 n)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      Sizes.measurable_seqHflow_entry d n (t1 n) i j
  rw [heq, ← Measure.map_map hmeasHflow (measurable_pi_apply (0 : ℕ))]
  congr 1
  unfold Pgue
  rw [Measure.infinitePi_map_eval]
  rfl

/-- Step `K` with `t₁ = (1 - ζ(τ)) t₀` has the law of `√t₀ · H_τ` ((7.25), (7.26)). -/
theorem map_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ n)
    (hK : K n ≠ 0) :
    (Pgue d).map (gueH d (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n)) =
      (ouP (d.L n) (d.W n)).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (τ n) ω) := by
  set t1fn : ℕ → ℝ := fun n => (1 - ouZeta (τ n)) * t0 n with ht1fndef
  have hζ0 : 0 ≤ ouZeta (τ n) := by
    unfold ouZeta
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hζ1 : ouZeta (τ n) ≤ 1 := by
    unfold ouZeta
    have := (Real.exp_pos (-(τ n))).le
    linarith
  have ht1n : t1fn n = (1 - ouZeta (τ n)) * t0 n := rfl
  have ht1n0 : 0 ≤ t1fn n := by rw [ht1n]; exact mul_nonneg (by linarith) ht0
  have ht1nt0 : t1fn n ≤ t0 n := by rw [ht1n]; nlinarith
  have hΔ : 0 ≤ gridStep t1fn t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  set M : ℝ := ((d.size n : ℕ) : ℝ) with hMdef
  have hMpos : (0 : ℝ) < M := by
    rw [hMdef]
    have h1 : 0 < d.W n := d.W_pos n
    have h2 : 0 < d.L n := by have := d.three_le_L n; omega
    have : 0 < d.size n := by
      rw [Sizes.size_eq]; positivity
    exact_mod_cast this
  set a : ℝ := Real.sqrt (t1fn n) with hadef
  set b : ℝ := Real.sqrt (gridStep t1fn t0 K n / M) with hbdef
  -- Step 1: the left side is `seqXmat d n` of a real-linear combination of the raw draws.
  have hHeq : gueH d t1fn t0 K n (K n)
      = fun ω => Sizes.seqXmat d n (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := by
    funext ω
    rw [GUEPhaseGrid_seqXmat_add, GUEPhaseGrid_seqXmat_smul, GUEPhaseGrid_seqXmat_smul,
      GUEPhaseGrid_seqXmat_sum, GUEPhaseGrid_real_smul_matrix, GUEPhaseGrid_real_smul_matrix]
    rfl
  have hLHSmeas : Measurable (fun ω : PathΩ d =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := by
    have h1 : Measurable (fun ω : PathΩ d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ d => ∑ i ∈ Finset.Icc 1 (K n), ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  -- The left side as the `Xmat` image of the size-`n` slice of the combined draw.
  have hseqX : Sizes.seqXmat d n = Xmat (d.L n) (d.W n) ∘ Sizes.slice d n := rfl
  have hLHS : (Pgue d).map (gueH d t1fn t0 K n (K n))
      = (Measure.infinitePi fun c : Coord (d.L n) (d.W n) => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * Sizes.seqGvar d ⟨n, c⟩
            + (K n) • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar d ⟨n, c⟩))).map
          (Xmat (d.L n) (d.W n)) := by
    rw [hHeq]
    have hfun : (fun ω : PathΩ d => Sizes.seqXmat d n
          (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i))
        = Xmat (d.L n) (d.W n) ∘ Sizes.slice d n ∘
            (fun ω : PathΩ d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := rfl
    rw [hfun, ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _)
        ((Sizes.measurable_slice d n).comp hLHSmeas),
      ← Measure.map_map (Sizes.measurable_slice d n) hLHSmeas,
      GUEPhaseGrid_Pgue_eq_mixed,
      GUEPhaseGrid_map_combined_eq_mixed (Sizes.seqGvar d) (gueUnitVar d) a b (K n)]
    congr 1
    exact GUEPhaseGrid_map_slice_infinitePi _ n
  -- The right side as the `Xmat` image of `√t₀ • ouSample`.
  have hRHSeq : (fun ω : Ω (d.L n) (d.W n) × Ω (d.L n) (d.W n) =>
        ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (τ n) ω)
      = Xmat (d.L n) (d.W n) ∘ (fun x => Real.sqrt (t0 n) • x) ∘
          ouSample (d.L n) (d.W n) (τ n) := by
    funext ω
    simp only [Function.comp_apply]
    rw [ouMat_eq_Xmat_ouSample, Xmat_smul, GUEPhaseGrid_real_smul_matrix]
  have hRHS : (ouP (d.L n) (d.W n)).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (τ n) ω)
      = (Measure.infinitePi fun c : Coord (d.L n) (d.W n) => gaussianReal 0
          (NNReal.mk (Real.sqrt (t0 n) ^ 2) (sq_nonneg _) * ouVar (d.L n) (d.W n) (τ n) c)).map
          (Xmat (d.L n) (d.W n)) := by
    have hsm : Measurable (fun x : Ω (d.L n) (d.W n) => Real.sqrt (t0 n) • x) :=
      by fun_prop
    rw [hRHSeq, ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _)
        (hsm.comp (measurable_ouSample (d.L n) (d.W n) (τ n))),
      ← Measure.map_map hsm (measurable_ouSample (d.L n) (d.W n) (τ n)),
      ouSample_law _ _ hτ, GUEPhaseGrid_map_smul_infinitePi]
  rw [hLHS, hRHS]
  congr 1
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  -- Step 2: the coordinate variances agree.
  apply NNReal.coe_injective
  have ha2 : a ^ 2 = t1fn n := by rw [hadef, Real.sq_sqrt ht1n0]
  have hb2 : b ^ 2 = gridStep t1fn t0 K n / M := by
    rw [hbdef, Real.sq_sqrt (div_nonneg hΔ hMpos.le)]
  have ht02 : Real.sqrt (t0 n) ^ 2 = t0 n := Real.sq_sqrt ht0
  have hstepval : gridStep t1fn t0 K n = (t0 n - t1fn n) / (K n : ℝ) := rfl
  have hKcast : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  have hex : Real.exp (-τ n) = 1 - ouZeta (τ n) := by unfold ouZeta; ring
  have hexle : Real.exp (-τ n) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hsz : ((d.size n : ℕ) : ℝ) = (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) := rfl
  have hunit : ((gueUnitVar d ⟨n, c⟩ : ℝ≥0) : ℝ) / M
      = (RBM.Endpoints.gueVar (d.L n) (d.W n) c : ℝ) := by
    unfold gueUnitVar RBM.Endpoints.gueVar
    by_cases hc : c.1 = c.2.1
    · simp only [hc, ite_true, hMdef, hsz]
      push_cast
      simp
    · simp only [hc, ite_false, hMdef, hsz]
      push_cast
      field_simp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul,
    ouVar, Real.coe_toNNReal _ (Real.exp_pos _).le, Real.coe_toNNReal _ (sub_nonneg.2 hexle)]
  have hseq : ((Sizes.seqGvar d ⟨n, c⟩ : ℝ≥0) : ℝ) = (gvar (d.L n) (d.W n) c : ℝ) := rfl
  have hkey : (K n : ℝ) * (gridStep t1fn t0 K n / M * ((gueUnitVar d ⟨n, c⟩ : ℝ≥0) : ℝ))
      = (t0 n - t1fn n) * ((gueUnitVar d ⟨n, c⟩ : ℝ≥0) / M : ℝ) := by
    rw [hstepval]
    field_simp
  push_cast
  rw [ha2, hb2, hseq, ht02, mul_assoc, hkey, hunit, ht1n, ← hex]
  ring

/-! ### Homogeneity of `gloop` under `z ↦ (E, u) = (lemE z, lemT z)`

Used by the law (7.26) (`Eq729B.lean`).  The d = 2 form is on `H : Matrix (BlockIndex L W) …`
(callers pass `blockMat M`); the scaling lemmas of `ConArg.lean` are private, so the three steps
are reproduced here. -/

section Homogeneity

private lemma GUEPhaseGrid_Gsig_smul_mul {m : Type*} [Fintype m] [DecidableEq m] {r : ℝ}
    (hr : (r : ℂ) ≠ 0) (H : Matrix m m ℂ) (z : ℂ) (σ : Bool) :
    Gsig ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • Gsig H z σ := by
  cases σ with
  | true => simpa only [Gsig_true] using RBM.Endpoints.ZRescale_green_smul_mul hr H z
  | false =>
    rw [Gsig_false, Gsig_false, map_mul, Complex.conj_ofReal]
    exact RBM.Endpoints.ZRescale_green_smul_mul hr H _

variable {L W : ℕ} [NeZero L]

private lemma GUEPhaseGrid_gloopProd_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) :
    gloopProd L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = (((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length) • gloopProd L W H z I := by
  obtain ⟨σ, a⟩ := I
  induction σ generalizing a with
  | nil => simp [gloopProd]
  | cons s σ ih =>
    cases a with
    | nil => simp [gloopProd]
    | cons b a =>
      rw [gloopProd_cons, gloopProd_cons, GUEPhaseGrid_Gsig_smul_mul hr, ih, smul_mul_assoc,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      simp only [List.zip_cons_cons, List.length_cons]
      congr 1
      ring

private lemma GUEPhaseGrid_gloop_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) :
    gloop L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * gloop L W H z I := by
  unfold gloop
  rw [GUEPhaseGrid_gloopProd_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

/-- `z_u^{(E)} = √u z` for `(E, u) = (lemE z, lemT z)` (`eq:zztE`). -/
private lemma GUEPhaseGrid_spectralZ_eq {z : ℂ} (hz : 0 < z.im) :
    spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
  have hu := RBM.Endpoints.ZRescale_lemT_pos hz
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have h := eq_inv_sqrt_mul_spectralZ hz
  calc spectralZ (lemE z) (lemT z)
      = (Real.sqrt (lemT z) : ℂ) *
          ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]

/-- **General homogeneity of `gloop`** for `0 < z.im`:
`L(H, z) = (√t₀)^n · L(√t₀ H, z_{t₀}^{(E)})`, `(E, t₀) = (lemE z, lemT z)`, `n` the loop length. -/
theorem GUEPhaseGrid_gloop_smul_lemT_eq
    (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ : List Bool) (a : List (Z2 L)) :
    gloop L W M z ⟨σ, a⟩
      = ((Real.sqrt (lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        gloop L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (spectralZ (lemE z) (lemT z)) ⟨σ, a⟩ := by
  have hs : ((Real.sqrt (lemT z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.Endpoints.ZRescale_lemT_pos hz)).ne'
  rw [GUEPhaseGrid_spectralZ_eq hz, GUEPhaseGrid_gloop_smul_mul hs]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- **General homogeneity of the 2-loop `gloop`**: for `0 < z.im`,
`L(H, z) = t₀ · L(√t₀ H, z_{t₀}^{(E)})` on the loop `loopOf ![true, σ₂] ![a, b]`, `t₀ = lemT z`. -/
theorem GUEPhaseGrid_gloop_two_smul_lemT_eq
    (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ₂ : Bool) (a b : Z2 L) :
    gloop L W M z (loopOf ![true, σ₂] ![a, b])
      = ((lemT z : ℝ) : ℂ) *
        gloop L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (spectralZ (lemE z) (lemT z)) (loopOf ![true, σ₂] ![a, b]) := by
  have hl : (loopOf ![true, σ₂] ![a, b] : LoopIdx (Z2 L)) = ⟨[true, σ₂], [a, b]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have hlen : (([true, σ₂] : List Bool).zip [a, b]).length = 2 := rfl
  rw [hl, GUEPhaseGrid_gloop_smul_lemT_eq M hz [true, σ₂] [a, b], hlen, ← Complex.ofReal_pow,
    Real.sq_sqrt (RBM.Endpoints.ZRescale_lemT_pos hz).le]

end Homogeneity

end RBM.Univ.GUEPhase

end
