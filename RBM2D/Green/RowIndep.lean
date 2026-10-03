/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Instances.Matrix
import RBM2D.Delocalization
import RBM2D.Gauss.Domination
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.LinearForm
import RBM2D.Gauss.Model
import RBM2D.Gauss.Stein
import RBM2D.Green.EntryCore
import RBM2D.Green.Minor

/-!
# The minor resolvent does not read row `x`

The paper (arXiv:2503.07606) does not state this file as a lemma: it says that the
entry estimates "follow that of Lemma 4.2 in [YY_25], which is dimension-independent"
(Section "Estimates for entries of `G`"), and the mathematics is that of [YY_25]: `G^(x)`, the
resolvent with row and column `x` removed, is a function of the coordinates outside row `x`,
hence independent of the Gaussian entries `H_{xk}`, `k ≠ x`, that multiply it.

The model interface is that of `RBM2D/Gauss/Model.lean`: everything is stated on the common
sample space `Sizes.SeqΩ d` with the product measure `Sizes.seqP d`, at slice `n` (the lattice
index type is `Idx (d.L n) (d.W n)`; the flow is `Sizes.seqHflow d n u`; the variances are the
block profile `svar`).

* `AgreeOffRow`, `Xentry_congr_of_ne`, `Hflow_submatrix_congr` : the minor reads only off-row
  coordinates.
* `rowSet`, `indepFun_rowSet`, `rowCoord`, `Xentry_eq_rowCoord`, `offRowCoord`,
  `Hflow_submatrix_congr_offRowCoord`, `row_sum_congr` : the row block is independent of the
  off-row block, and the row sum reads only the two.
* `integral_norm_row_sum_pow_le` : fixed coefficients, `E‖∑_{k≠x} H_{xk} c_k‖^{2p}
  ≤ 2 (2p-1)!! (u ∑_{k≠x} svar(x,k) ‖c_k‖²)^p`.
* `integral_norm_rowSum_pow_le`, `integral_norm_rowSum_norm_pow_le'` : coefficients that read
  only the off-row block (conditionally Gaussian row sum).
* `minorCol`, `minorRowConj`, `ldeRowLHS_eq`, `rowVarSum_eq` : the minor resolvent columns and
  the alignment with `ldeRowLHS`, `ldeRowRHS` of `Green/EntryCore.lean`.
* `stochDom_rowSum_generalTime` : the row LDE as stochastic domination (`PerTimeDomAt`) along an
  admissible size sequence.

`relCoord` is the set of all slice-`n` coordinates; the double
factorial is `RowIndep_dfac` and the Gaussian-moment helpers are private; the `At` forms carry
the hypothesis `Filter.Tendsto d.size Filter.atTop Filter.atTop`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory RBM.Gauss RBM.Gauss.LinearForm
open scoped NNReal ENNReal

/-! ### Gaussian moments (private) -/

section Moments

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
private theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- **The Stein recursion for the even moments**: `E[X^{2p+2}] = (2p+1) v E[X^{2p}]`. -/
private theorem integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv
      ((integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv (integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`, with the
double factorial written as `∏_{i<p} (2i+1)`. -/
private theorem integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v)
      = (∏ i ∈ Finset.range p, (2 * (i : ℝ) + 1)) * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, integral_pow_gaussianReal_succ, ih,
      Finset.prod_range_succ]
    ring

/-- The double factorial `(2p-1)!! = ∏_{i<p} (2i+1)`, the `2p`-th moment of a standard
Gaussian.  (Public because it occurs in the statements of the moment bounds below.) -/
noncomputable def RowIndep_dfac (p : ℕ) : ℝ := ∏ i ∈ Finset.range p, (2 * (i : ℝ) + 1)

@[simp] theorem RowIndep_dfac_zero : RowIndep_dfac 0 = 1 := by simp [RowIndep_dfac]

theorem RowIndep_dfac_succ (p : ℕ) :
    RowIndep_dfac (p + 1) = (2 * (p : ℝ) + 1) * RowIndep_dfac p := by
  rw [RowIndep_dfac, RowIndep_dfac, Finset.prod_range_succ, mul_comm]

private theorem integral_pow_gaussianReal' (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = RowIndep_dfac p * (v : ℝ) ^ p :=
  integral_pow_gaussianReal v p

section MomentBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- All even moments of a linear form exist. -/
private theorem integrable_pow_lin (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    Integrable (fun ω => (∑ i ∈ s, a i * X i ω) ^ (2 * p)) P := by
  classical
  have hm := measurable_lin hmeas a s
  have h := integrable_pow_gaussianReal (linVar v a s) (2 * p)
  rw [← map_lin hmeas hlaw hindep a s] at h
  exact (integrable_map_measure ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
    hm.aemeasurable).1 h

/-- **The even moments of a linear form**: `E[(∑ a_i X_i)^{2p}] = (2p-1)!! (∑ a_i² v_i)^p`. -/
private theorem integral_pow_lin (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, (∑ i ∈ s, a i * X i ω) ^ (2 * p) ∂P = RowIndep_dfac p * (linVar v a s : ℝ) ^ p := by
  classical
  have hm := measurable_lin hmeas a s
  have h := integral_map (μ := P) (φ := fun ω => ∑ i ∈ s, a i * X i ω)
    (f := fun y : ℝ => y ^ (2 * p)) hm.aemeasurable
    ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
  rw [map_lin hmeas hlaw hindep a s] at h
  rw [← h, integral_pow_gaussianReal']

/-- **The moment bound for the modulus of a complex linear form.**  If `Y = ∑ a_i X_i` and
`Y' = ∑ b_i X_i` are the real and imaginary parts, then
`E[(Y² + Y'²)^p] ≤ 2^p (2p-1)!! (V_a^p + V_b^p)`; in the circular case `V_a = V_b = σ²/2` this
is `E‖Z‖^{2p} ≤ (2p-1)!! σ^{2p}`. -/
private theorem integral_sq_add_sq_pow_le (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a b : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ 2 ^ p * (RowIndep_dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
  classical
  have hia := integrable_pow_lin hmeas hlaw hindep a s p
  have hib := integrable_pow_lin hmeas hlaw hindep b s p
  have hpt : ∀ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p
      ≤ 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p) + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) := by
    intro ω
    set x := (∑ i ∈ s, a i * X i ω) ^ 2 with hx
    set y := (∑ i ∈ s, b i * X i ω) ^ 2 with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hmax : x + y ≤ 2 * max x y := by
      rcases le_total x y with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h1 : (x + y) ^ p ≤ (2 * max x y) ^ p :=
      pow_le_pow_left₀ (by positivity) hmax p
    have h2 : (2 * max x y) ^ p = 2 ^ p * max x y ^ p := by rw [mul_pow]
    have h3 : max x y ^ p ≤ x ^ p + y ^ p := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ x ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ y ^ p := by positivity
        linarith
    have hxp : x ^ p = (∑ i ∈ s, a i * X i ω) ^ (2 * p) := by
      rw [hx, ← pow_mul]
    have hyp : y ^ p = (∑ i ∈ s, b i * X i ω) ^ (2 * p) := by
      rw [hy, ← pow_mul]
    calc (x + y) ^ p ≤ 2 ^ p * max x y ^ p := by rw [← h2]; exact h1
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h3 this
      _ = _ := by rw [hxp, hyp]
  have hint : Integrable (fun ω => 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
      + (∑ i ∈ s, b i * X i ω) ^ (2 * p))) P := (hia.add hib).const_mul _
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hint
    (Filter.Eventually.of_forall hpt)
  calc ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ ∫ ω, 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
          + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) ∂P := hle
    _ = 2 ^ p * (RowIndep_dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
        rw [integral_const_mul, integral_add hia hib, integral_pow_lin hmeas hlaw hindep,
          integral_pow_lin hmeas hlaw hindep]
        ring


end MomentBound

end Moments

/-! ### Measurability of the matrix inverse (private) -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
    (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- The entrywise form: from measurability of every entry of `A`, every entry of `A⁻¹` is
measurable. -/
private theorem measurable_inv_entries {A : Θ → Matrix ν ν ℂ}
    (hA : ∀ k l, Measurable fun ω => A ω k l) (k l : ν) :
    Measurable fun ω => (A ω)⁻¹ k l :=
  measurable_matrix_inv_apply (Measurable.of_eval fun a => Measurable.of_eval fun b => hA a b) k l

end MatrixMeasurable

variable {d : Sizes} {n : ℕ}

/-- The entries of the common-space flow. -/
private theorem seqHflow_apply (u : ℝ) (ω : Sizes.SeqΩ d) (i j : Idx (d.L n) (d.W n)) :
    Sizes.seqHflow d n u ω i j
      = (Real.sqrt u : ℂ) * Xentry (d.L n) (d.W n) (Sizes.slice d n ω) i j := rfl


/-- Two sample points **agree off row `i`** when every coordinate at size `n` whose index pair
avoids `i` carries the same value. -/
def AgreeOffRow (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) (ω ω' : Sizes.SeqΩ d) : Prop :=
  ∀ (k l : Idx (d.L n) (d.W n)) (b : Bool), k ≠ i → l ≠ i → ω ⟨n, k, l, b⟩ = ω' ⟨n, k, l, b⟩

/-- The entries of `X` away from row and column `i` only read coordinates that avoid `i`. -/
theorem Xentry_congr_of_ne {i : Idx (d.L n) (d.W n)} {ω ω' : Sizes.SeqΩ d}
    (h : AgreeOffRow d n i ω ω')
    {k l : Idx (d.L n) (d.W n)} (hk : k ≠ i) (hl : l ≠ i) :
    Xentry (d.L n) (d.W n) (Sizes.slice d n ω) k l
      = Xentry (d.L n) (d.W n) (Sizes.slice d n ω') k l := by
  unfold Xentry
  simp only [Sizes.slice]
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` at `i` only reads coordinates that avoid `i`. -/
theorem Hflow_submatrix_congr (u : ℝ) {i : Idx (d.L n) (d.W n)} {ω ω' : Sizes.SeqΩ d}
    (h : AgreeOffRow d n i ω ω') :
    (Sizes.seqHflow d n u ω).submatrix (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
      = (Sizes.seqHflow d n u ω').submatrix (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _) := by
  ext k l
  simp only [Matrix.submatrix_apply, seqHflow_apply]
  rw [Xentry_congr_of_ne h k.2 l.2]

/-! ### The coordinates of row `i` -/

open Finset

/-- The coordinates of row `i` at size `n`: those whose index pair contains `i`. -/
def rowSet (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) : Finset (Sizes.SeqCoord d) :=
  (univ : Finset (Idx (d.L n) (d.W n) × Bool)).image
      (fun p => (⟨n, i, p.1, p.2⟩ : Sizes.SeqCoord d)) ∪
    (univ : Finset (Idx (d.L n) (d.W n) × Bool)).image
      (fun p => (⟨n, p.1, i, p.2⟩ : Sizes.SeqCoord d))

@[simp] theorem mem_rowSet {i k l : Idx (d.L n) (d.W n)} {b : Bool} :
    (⟨n, k, l, b⟩ : Sizes.SeqCoord d) ∈ rowSet d n i ↔ (k = i ∨ l = i) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inl h2.1.symm
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inr h2.2.1.symm
  · rintro (rfl | rfl)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(l, b), Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(k, b), Finset.mem_univ _, rfl⟩)

/-- **The row block is independent of any disjoint block of coordinates.** -/
theorem indepFun_rowSet (i : Idx (d.L n) (d.W n)) (T : Finset (Sizes.SeqCoord d))
    (hT : Disjoint (rowSet d n i) T) :
    IndepFun (fun (ω : Sizes.SeqΩ d) (c : rowSet d n i) => ω c)
      (fun (ω : Sizes.SeqΩ d) (c : T) => ω c) (Sizes.seqP d) :=
  (iIndepFun_coord d).indepFun_finset _ _ hT fun c => measurable_pi_apply c

/-! ### The row as a family indexed by `(column, real/imaginary)` -/

/-- The coordinate carrying the real (`b = true`) or imaginary (`b = false`) part of the entry
`X_{ik}`, for `k ≠ i`. -/
noncomputable def rowCoord (d : Sizes) (n : ℕ) (i k : Idx (d.L n) (d.W n)) (b : Bool) :
    Sizes.SeqCoord d :=
  if idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k then ⟨n, i, k, b⟩ else ⟨n, k, i, b⟩

/-- The sign with which the imaginary coordinate enters `X_{ik}`. -/
noncomputable def rowSign (d : Sizes) (n : ℕ) (i k : Idx (d.L n) (d.W n)) : ℝ :=
  if idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k then 1 else -1

theorem rowCoord_mem_rowSet (i k : Idx (d.L n) (d.W n)) (b : Bool) :
    rowCoord d n i k b ∈ rowSet d n i := by
  unfold rowCoord
  split_ifs with h
  · exact mem_rowSet.2 (Or.inl rfl)
  · exact mem_rowSet.2 (Or.inr rfl)

/-- **The entry `X_{ik}` in terms of the two row coordinates.**  For `k ≠ i` it is
`ω(real) + ε i ω(imag)` with `ε = ±1`. -/
theorem Xentry_eq_rowCoord {i k : Idx (d.L n) (d.W n)} (hik : i ≠ k) (ω : Sizes.SeqΩ d) :
    Xentry (d.L n) (d.W n) (Sizes.slice d n ω) i k = (ω (rowCoord d n i k true) : ℂ)
      + (rowSign d n i k : ℂ) * Complex.I * (ω (rowCoord d n i k false) : ℂ) := by
  have hkey : idxKey (d.L n) (d.W n) i ≠ idxKey (d.L n) (d.W n) k := fun h =>
    hik (idxKey_injective (d.L n) (d.W n) h)
  unfold Xentry rowCoord rowSign
  simp only [Sizes.slice]
  rcases lt_or_gt_of_ne hkey with h | h
  · simp only [h, ↓reduceIte]
    push_cast
    ring
  · have h' : ¬ idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k := by omega
    simp only [h', ↓reduceIte, h]
    push_cast
    ring

/-- The row coordinates are distinct: `(k, b) ↦ rowCoord i k b` is injective away from `i`. -/
theorem rowCoord_injOn {i : Idx (d.L n) (d.W n)} {k l : Idx (d.L n) (d.W n)} {b c : Bool}
    (hk : k ≠ i) (hl : l ≠ i)
    (h : rowCoord d n i k b = rowCoord d n i l c) : k = l ∧ b = c := by
  unfold rowCoord at h
  have hk' := hk
  have hl' := hl
  split_ifs at h with h1 h2 h2 <;> injection h with h3 h4 <;>
    simp only [Prod.mk.injEq] at h4 <;>
    first
      | exact ⟨h4.2.1, h4.2.2⟩
      | exact ⟨h4.1, h4.2.2⟩
      | (exfalso; simp_all)

/-! ### The row sum as a pair of real linear forms -/

/-- The index set of the row: a column `k ≠ i` together with a real/imaginary flag. -/
abbrev RowIdx (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) : Type :=
    {k : Idx (d.L n) (d.W n) // k ≠ i} × Bool

/-- The Gaussian coordinates of the row, indexed by `RowIdx`. -/
noncomputable def rowVar (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) (q : RowIdx d n i)
    (ω : Sizes.SeqΩ d) : ℝ :=
  ω (rowCoord d n i q.1.1 q.2)

/-- The coefficients of the real part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowRe (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (c : Idx (d.L n) (d.W n) → ℂ)
    (q : RowIdx d n i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).re
  else -(Real.sqrt u * rowSign d n i q.1.1 * (c q.1.1).im)

/-- The coefficients of the imaginary part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowIm (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (c : Idx (d.L n) (d.W n) → ℂ)
    (q : RowIdx d n i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).im
  else Real.sqrt u * rowSign d n i q.1.1 * (c q.1.1).re

/-- **The row sum, real part**: a real linear form in the row coordinates. -/
theorem re_row_sum (u : ℝ) (i : Idx (d.L n) (d.W n)) (c : Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) :
    (∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * c k.1).re
      = ∑ q : RowIdx d n i, rowRe d n u i c q * rowVar d n i q ω := by
  rw [Complex.re_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seqHflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowRe, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k.1 <;>
    simp [h, Complex.add_re, Complex.mul_re] <;> ring

/-- **The row sum, imaginary part**. -/
theorem im_row_sum (u : ℝ) (i : Idx (d.L n) (d.W n)) (c : Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) :
    (∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * c k.1).im
      = ∑ q : RowIdx d n i, rowIm d n u i c q * rowVar d n i q ω := by
  rw [Complex.im_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seqHflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowIm, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k.1 <;>
    simp [h, Complex.add_im, Complex.mul_im] <;> ring

/-! ### The moment bound for a row sum with fixed coefficients -/

theorem rowCoord_inj (i : Idx (d.L n) (d.W n)) :
    Function.Injective fun q : RowIdx d n i => rowCoord d n i q.1.1 q.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
  obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
  subst h1
  subst h2
  rfl

/-- The row coordinates form an independent family. -/
theorem iIndepFun_rowVar (i : Idx (d.L n) (d.W n)) :
    ProbabilityTheory.iIndepFun (rowVar d n i) (Sizes.seqP d) :=
  ProbabilityTheory.iIndepFun.precomp
    (g := fun q : RowIdx d n i => rowCoord d n i q.1.1 q.2) (rowCoord_inj i) (iIndepFun_coord d)

theorem measurable_rowVar (i : Idx (d.L n) (d.W n)) (q : RowIdx d n i) :
    Measurable (rowVar d n i q) := measurable_pi_apply _

theorem map_rowVar (i : Idx (d.L n) (d.W n)) (q : RowIdx d n i) :
    (Sizes.seqP d).map (rowVar d n i q)
      = gaussianReal 0 (Sizes.seqGvar d (rowCoord d n i q.1.1 q.2)) :=
  Sizes.seqP_map_eval d _

/-- Off the diagonal the coordinate variance is `svar(i,k)/2`, in either order of the index pair. -/
theorem gvar_rowCoord {i k : Idx (d.L n) (d.W n)} (hk : k ≠ i) (b : Bool) :
    (Sizes.seqGvar d (rowCoord d n i k b) : ℝ) = svar (d.L n) (d.W n) i k / 2 := by
  have key : ∀ a c : Idx (d.L n) (d.W n), a ≠ c →
      (Sizes.seqGvar d ⟨n, a, c, b⟩ : ℝ) = svar (d.L n) (d.W n) a c / 2 := fun a c hac =>
    gvar_offDiag (d.L n) (d.W n) a c b hac
  unfold rowCoord
  split_ifs with h
  · exact key i k (Ne.symm hk)
  · rw [key k i hk, svar_comm]

/-- The variance of the real part of the row sum: `(u/2) ∑_k svar(i,k) |c_k|²`. -/
theorem linVar_rowRe {u : ℝ} (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (c : Idx (d.L n) (d.W n) → ℂ) :
    ((linVar (fun q : RowIdx d n i => Sizes.seqGvar d (rowCoord d n i q.1.1 q.2))
        (rowRe d n u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
          svar (d.L n) (d.W n) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowRe, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k.1 <;>
    simp [h, hnorm, mul_pow, hsq] <;> ring

/-- The variance of the imaginary part is the same. -/
theorem linVar_rowIm {u : ℝ} (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (c : Idx (d.L n) (d.W n) → ℂ) :
    ((linVar (fun q : RowIdx d n i => Sizes.seqGvar d (rowCoord d n i q.1.1 q.2))
        (rowIm d n u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
          svar (d.L n) (d.W n) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowIm, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey (d.L n) (d.W n) i < idxKey (d.L n) (d.W n) k.1 <;>
    simp [h, hnorm, mul_pow, hsq] <;> ring

/-- **The moment bound for a row sum with fixed coefficients**:
`E‖∑_{k ≠ i} H_{ik} c_k‖^{2p} ≤ 2 (2p-1)!! (u ∑_k svar(i,k) |c_k|²)^p`. -/
theorem integral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    (c : Idx (d.L n) (d.W n) → ℂ) (p : ℕ) :
    ∫ ω, ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
        Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p) ∂(Sizes.seqP d)
      ≤ 2 * (RowIndep_dfac p *
        (u * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
          svar (d.L n) (d.W n) i k.1 * ‖c k.1‖ ^ 2) ^ p) := by
  set V : ℝ := u / 2 * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
    svar (d.L n) (d.W n) i k.1 * ‖c k.1‖ ^ 2 with hV
  have hpt : ∀ ω : Sizes.SeqΩ d, ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
        Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p)
      = ((∑ q : RowIdx d n i, rowRe d n u i c q * rowVar d n i q ω) ^ 2
        + (∑ q : RowIdx d n i, rowIm d n u i c q * rowVar d n i q ω) ^ 2) ^ p := by
    intro ω
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← re_row_sum, ← im_row_sum]
    ring_nf
  simp_rw [hpt]
  have hbound := integral_sq_add_sq_pow_le (P := Sizes.seqP d)
    (measurable_rowVar (d := d) (n := n) i)
    (map_rowVar (d := d) (n := n) i) (iIndepFun_rowVar (d := d) (n := n) i)
    (rowRe d n u i c) (rowIm d n u i c) Finset.univ p
  rw [linVar_rowRe hu, linVar_rowIm hu] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [mul_pow, div_pow]
  field_simp
  ring

/-! ### The two concrete finite blocks -/

/-- The coordinates of slice `n` (all of them: RBM2D has no unused-coordinate bookkeeping, and the
finite block only has to contain the coordinates that `H` at size `n` reads and to be disjoint
from `rowSet`). -/
def relCoord (d : Sizes) (n : ℕ) : Finset (Sizes.SeqCoord d) :=
  (Finset.univ : Finset (Coord (d.L n) (d.W n))).image (fun c => (⟨n, c⟩ : Sizes.SeqCoord d))

/-- The relevant coordinates outside row `i`. -/
def offRowCoord (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) : Finset (Sizes.SeqCoord d) :=
  relCoord d n \ rowSet d n i

theorem disjoint_rowSet_offRowCoord (i : Idx (d.L n) (d.W n)) :
    Disjoint (rowSet d n i) (offRowCoord d n i) := by
  rw [Finset.disjoint_right]
  intro c hc
  exact (Finset.mem_sdiff.1 hc).2

/-- A coordinate of slice `n` whose index pair avoids `i` lies in the off-row block. -/
private theorem mem_offRowCoord {i k l : Idx (d.L n) (d.W n)} (b : Bool) (hk : k ≠ i)
    (hl : l ≠ i) : (⟨n, k, l, b⟩ : Sizes.SeqCoord d) ∈ offRowCoord d n i := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact Finset.mem_image.2 ⟨(k, l, b), Finset.mem_univ _, rfl⟩
  · rw [mem_rowSet]
    rintro (h | h)
    · exact hk h
    · exact hl h

/-- **The minor matrix reads only the off-row block.**  Two sample points agreeing on
`offRowCoord` have the same `H^{(i)}`. -/
theorem Hflow_submatrix_congr_offRowCoord (u : ℝ) {i : Idx (d.L n) (d.W n)}
    {ω ω' : Sizes.SeqΩ d} (h : ∀ c ∈ offRowCoord d n i, ω c = ω' c) :
    (Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
      = (Sizes.seqHflow d n u ω').submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _) :=
  Hflow_submatrix_congr u fun _ _ b hk hl => h _ (mem_offRowCoord b hk hl)

/-- The row entries `H_{ik}`, `k ≠ i`, read only the row block. -/
theorem Hflow_row_congr (u : ℝ) {i : Idx (d.L n) (d.W n)} {ω ω' : Sizes.SeqΩ d}
    (h : ∀ c ∈ rowSet d n i, ω c = ω' c) {k : Idx (d.L n) (d.W n)} (hk : k ≠ i) :
    Sizes.seqHflow d n u ω i k = Sizes.seqHflow d n u ω' i k := by
  rw [seqHflow_apply, seqHflow_apply, Xentry_eq_rowCoord (Ne.symm hk) ω,
    Xentry_eq_rowCoord (Ne.symm hk) ω', h _ (rowCoord_mem_rowSet i k true),
    h _ (rowCoord_mem_rowSet i k false)]

/-- The row sum with coefficients reading only the off-row block, as a function of the two
blocks. -/
theorem row_sum_congr (u : ℝ) {i : Idx (d.L n) (d.W n)} (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω')
    {ω ω' : Sizes.SeqΩ d} (h : ∀ c ∈ rowSet d n i ∪ offRowCoord d n i, ω c = ω' c) :
    (∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * C ω k.1)
      = ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω' i k.1 * C ω' k.1 := by
  have hrow : ∀ c ∈ rowSet d n i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_left _ hc)
  have hoff : ∀ c ∈ offRowCoord d n i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_right _ hc)
  rw [hC ω ω' hoff]
  exact Finset.sum_congr rfl fun k _ => by rw [Hflow_row_congr u hrow k.2]

/-! ### The conditional moment bound: random coefficients -/

variable {u : ℝ} {i : Idx (d.L n) (d.W n)} {p : ℕ}

/-- Abbreviation for the row sum with coefficients `C`. -/
noncomputable def rowSum (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) : ℂ :=
  ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * C ω k.1

/-- The (random) variance of the row sum. -/
noncomputable def rowVarSum (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) : ℝ :=
  u * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, svar (d.L n) (d.W n) i k.1 * ‖C ω k.1‖ ^ 2

/-- **The row LDE moment bound.**  If the coefficients read only the off-row block, then
`E‖∑_{k ≠ i} H_{ik} C_k‖^{2p} ≤ 2 (2p-1)!! · E[(u ∑_k svar(i,k) |C_k|²)^p]`: conditionally on the
off-row block the row sum is a centred complex Gaussian of variance `u ∑_k svar(i,k)|C_k|²`, so the
fixed-coefficient bound `integral_norm_row_sum_pow_le` applies fibrewise. -/
theorem integral_norm_rowSum_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable (fun ω => ‖rowSum d n u i C ω‖ ^ (2 * p)) (Sizes.seqP d))
    (hint' : Integrable (fun ω => rowVarSum d n u i C ω ^ p) (Sizes.seqP d)) :
    ∫ ω, ‖rowSum d n u i C ω‖ ^ (2 * p) ∂(Sizes.seqP d)
      ≤ 2 * (RowIndep_dfac p * ∫ ω, rowVarSum d n u i C ω ^ p ∂(Sizes.seqP d)) := by
  classical
  set S := rowSet d n i with hS
  set T := offRowCoord d n i with hT
  set U : Sizes.SeqΩ d → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Sizes.SeqΩ d → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (Sizes.seqP d) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (d := d) (n := n) i
  -- the coefficients read only the second block, so they may be read off `V` alone
  have hCy : ∀ ω : Sizes.SeqΩ d, C ω = C (glue S T (0, V ω)) := by
    intro ω
    refine hC _ _ fun c hc => ?_
    have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
    simp [glue, hcS, hc, hV]
  -- the row sum is a function of the two blocks
  have hrow : ∀ ω : Sizes.SeqΩ d, rowSum d n u i C ω = rowSum d n u i C (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u C hC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ :=
    fun q => ‖rowSum d n u i C (glue S T q)‖ ^ (2 * p) with hF
  set G : ({c // c ∈ T} → ℝ) → ℝ :=
    fun y => 2 * (RowIndep_dfac p * rowVarSum d n u i C (glue S T (0, y)) ^ p) with hG
  -- measurability of the glued quantities
  have hglue := measurable_glue (ι := Sizes.SeqCoord d) S T
  have hFmeas : Measurable F := by
    refine (Measurable.pow_const ?_ _)
    refine Measurable.norm ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((Sizes.measurable_seqHflow_entry d n u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hCmeas).comp hglue)
  have hGmeas : Measurable G := by
    refine (measurable_const.mul ((measurable_const.mul (Measurable.pow_const ?_ _))))
    refine (measurable_const.mul ?_)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_const.mul
      ((((measurable_pi_apply k.1).comp hCmeas).comp (hglue.comp (measurable_const.prodMk
        measurable_id))).norm.pow_const _)
  -- transport the two integrability hypotheses
  have hpair : (Sizes.seqP d).map (fun ω => (U ω, V ω))
      = ((Sizes.seqP d).map U).prod ((Sizes.seqP d).map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable).1 hindep
  have hFint : Integrable F (((Sizes.seqP d).map U).prod ((Sizes.seqP d).map V)) := by
    rw [← hpair]
    refine (integrable_map_measure hFmeas.aestronglyMeasurable
      (hUmeas.prodMk hVmeas).aemeasurable).2 ?_
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF, Function.comp]
    rw [← hrow]
  have hGint : Integrable G ((Sizes.seqP d).map V) := by
    refine (integrable_map_measure hGmeas.aestronglyMeasurable hVmeas.aemeasurable).2 ?_
    refine ((hint'.const_mul (RowIndep_dfac p)).const_mul 2).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hG, Function.comp, rowVarSum]
    rw [← hCy]
  -- the fibrewise (conditional) bound
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫ x, F (x, y) ∂((Sizes.seqP d).map U)) ≤ G y := by
    intro y
    have hmap := integral_map (μ := Sizes.seqP d) (φ := U) (f := fun x => F (x, y))
      hUmeas.aemeasurable (hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [hmap]
    have hval : ∀ ω : Sizes.SeqΩ d, F (U ω, y)
        = ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 *
            C (glue S T (0, y)) k.1‖ ^ (2 * p) := by
      intro ω
      simp only [hF, rowSum]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Sizes.seqHflow d n u (glue S T (U ω, y)) i k.1 = Sizes.seqHflow d n u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hCe : C (glue S T (U ω, y)) k.1 = C (glue S T (0, y)) k.1 := by
        have : C (glue S T (U ω, y)) = C (glue S T (0, y)) := by
          refine hC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hCe]
    simp only [hval]
    exact (integral_norm_row_sum_pow_le hu i (C (glue S T (0, y))) p).trans (le_of_eq (by
      simp only [hG, rowVarSum]))
  -- assemble
  have hmain := integral_indep_pair_le hUmeas hVmeas hindep hFint hGint
    (Filter.Eventually.of_forall hinner)
  have hL : ∫ ω, ‖rowSum d n u i C ω‖ ^ (2 * p) ∂(Sizes.seqP d)
      = ∫ ω, F (U ω, V ω) ∂(Sizes.seqP d) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF]
    rw [← hrow]
  have hR : ∫ y, G y ∂((Sizes.seqP d).map V)
      = 2 * (RowIndep_dfac p * ∫ ω, rowVarSum d n u i C ω ^ p ∂(Sizes.seqP d)) := by
    rw [integral_map hVmeas.aemeasurable hGmeas.aestronglyMeasurable]
    simp only [hG, rowVarSum]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [← hCy]
  rw [hL, ← hR]
  exact hmain

/-- The coefficients normalised by the (random) standard deviation of the row sum. -/
noncomputable def rowCoeffNorm (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) (k : Idx (d.L n) (d.W n)) : ℂ :=
  if 0 < rowVarSum d n u i C ω then C ω k / (Real.sqrt (rowVarSum d n u i C ω) : ℂ) else 0

theorem rowVarSum_nonneg (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) :
    0 ≤ rowVarSum d n u i C ω := by
  refine mul_nonneg hu (Finset.sum_nonneg fun k _ => ?_)
  exact mul_nonneg (svar_nonneg _ _ _ _) (by positivity)

/-- **The normalised row sum has variance `1`** wherever the variance is positive. -/
theorem rowVarSum_rowCoeffNorm (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) :
    rowVarSum d n u i (rowCoeffNorm d n u i C) ω
      = if 0 < rowVarSum d n u i C ω then 1 else 0 := by
  have hV0 := rowVarSum_nonneg (i := i) hu C ω
  by_cases h : 0 < rowVarSum d n u i C ω
  · have hs : (0 : ℝ) < Real.sqrt (rowVarSum d n u i C ω) := Real.sqrt_pos.2 h
    have hsq : Real.sqrt (rowVarSum d n u i C ω) ^ 2 = rowVarSum d n u i C ω := Real.sq_sqrt hV0
    have hcoef : ∀ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, ‖rowCoeffNorm d n u i C ω k.1‖ ^ 2
        = ‖C ω k.1‖ ^ 2 / rowVarSum d n u i C ω := by
      intro k
      simp only [rowCoeffNorm, h, ↓reduceIte, norm_div, div_pow, Complex.norm_real,
        Real.norm_of_nonneg hs.le, hsq]
    simp only [h, ↓reduceIte]
    have hne : rowVarSum d n u i C ω ≠ 0 := ne_of_gt h
    have hcalc : rowVarSum d n u i (rowCoeffNorm d n u i C) ω
        = rowVarSum d n u i C ω / rowVarSum d n u i C ω := by
      conv_lhs => unfold rowVarSum
      simp only [hcoef]
      rw [Finset.sum_congr rfl fun k _ => (mul_div_assoc (svar (d.L n) (d.W n) i k.1)
        (‖C ω k.1‖ ^ 2) (rowVarSum d n u i C ω)).symm, ← Finset.sum_div, ← mul_div_assoc]
      rfl
    rw [hcalc, div_self hne]
  · simp only [h, ↓reduceIte]
    have hzero : ∀ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, rowCoeffNorm d n u i C ω k.1 = 0 := by
      intro k
      simp [rowCoeffNorm, h]
    unfold rowVarSum
    simp [hzero]

/-- The normalised coefficients still read only the off-row block. -/
theorem rowCoeffNorm_congr (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω')
    (ω ω' : Sizes.SeqΩ d) (h : ∀ c ∈ offRowCoord d n i, ω c = ω' c) :
    rowCoeffNorm d n u i C ω = rowCoeffNorm d n u i C ω' := by
  have hCe := hC ω ω' h
  funext k
  simp only [rowCoeffNorm, rowVarSum, hCe]
  rfl

theorem measurable_rowVarSum (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ) (hCmeas : Measurable C) :
    Measurable (rowVarSum d n u i C) := by
  unfold rowVarSum
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
  exact measurable_const.mul ((((measurable_pi_apply k.1).comp hCmeas).norm).pow_const 2)

theorem measurable_rowCoeffNorm (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C) :
    Measurable (rowCoeffNorm d n u i C) := by
  refine Measurable.of_eval fun k => ?_
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_rowVarSum C hCmeas)) ?_
    measurable_const
  refine ((measurable_pi_apply k).comp hCmeas).div ?_
  exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (measurable_rowVarSum C hCmeas))

/-- **The row LDE, ratio form.**  Normalising by the conditional standard deviation gives a
*constant* moment bound: `E[(‖∑_{k≠i} H_{ik} C_k‖² / (u ∑_k svar(i,k)|C_k|²))^p] ≤ 2 (2p-1)!!`.
This is the `MomentDomAt` input (with `Φ = 1`) that `stochDomAt_of_momentDomAt` turns into `≺`. -/
theorem integral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable
      (fun ω => ‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p)) (Sizes.seqP d)) :
    ∫ ω, ‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p) ∂(Sizes.seqP d)
      ≤ 2 * RowIndep_dfac p := by
  have hvar := rowVarSum_rowCoeffNorm (d := d) (n := n) (u := u) (i := i) hu C
  have hmeas' : Measurable (fun ω => rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p) :=
    (measurable_rowVarSum _ (measurable_rowCoeffNorm C hCmeas)).pow_const p
  have hbdd : ∀ ω : Sizes.SeqΩ d, ‖rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p‖ ≤ 1 := by
    intro ω
    rw [hvar ω]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · by_cases h : 0 < rowVarSum d n u i C ω <;> simp [h]
    · by_cases h : 0 < rowVarSum d n u i C ω <;> simp [h, zero_pow hp.ne']
  have hint' : Integrable (fun ω => rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p)
      (Sizes.seqP d) :=
    (integrable_const (1 : ℝ)).mono' hmeas'.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hmain := integral_norm_rowSum_pow_le (d := d) (n := n) (u := u) (i := i) (p := p) hu
    (rowCoeffNorm d n u i C) (measurable_rowCoeffNorm C hCmeas)
    (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h) hint hint'
  refine hmain.trans ?_
  have hle : ∫ ω, rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p ∂(Sizes.seqP d) ≤ 1 := by
    calc ∫ ω, rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p ∂(Sizes.seqP d)
        ≤ ∫ _ω : Sizes.SeqΩ d, (1 : ℝ) ∂(Sizes.seqP d) := by
          refine integral_mono hint' (integrable_const 1) fun ω => ?_
          have := hbdd ω
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = 1 := by simp
  have hd : 0 ≤ RowIndep_dfac p := by
    unfold RowIndep_dfac
    positivity
  nlinarith [hle, hd]

/-! ### Measurability of the minor resolvent -/

/-- The `j`-th column of the minor resolvent `(H^{(i)} - z)^{-1}`, as coefficients indexed by
all of `Idx (d.L n) (d.W n)` (zero at `i`). -/
noncomputable def minorCol (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (i : Idx (d.L n) (d.W n))
    (j : {a : Idx (d.L n) (d.W n) // a ≠ i}) (ω : Sizes.SeqΩ d) (k : Idx (d.L n) (d.W n)) : ℂ :=
  if h : k ≠ i then
    (((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ i}
        {a : Idx (d.L n) (d.W n) // a ≠ i} ℂ))⁻¹) ⟨k, h⟩ j
  else 0

/-- **The minor resolvent column reads only the off-row block.** -/
theorem minorCol_congr (u : ℝ) (z : ℂ) {i : Idx (d.L n) (d.W n)}
    (j : {a : Idx (d.L n) (d.W n) // a ≠ i})
    {ω ω' : Sizes.SeqΩ d} (h : ∀ c ∈ offRowCoord d n i, ω c = ω' c) :
    minorCol d n u z i j ω = minorCol d n u z i j ω' := by
  funext k
  unfold minorCol
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorCol (u : ℝ) (z : ℂ) (i : Idx (d.L n) (d.W n))
    (j : {a : Idx (d.L n) (d.W n) // a ≠ i}) :
    Measurable (minorCol d n u z i j) := by
  refine Measurable.of_eval fun k => ?_
  unfold minorCol
  split
  · exact measurable_inv_entries
      (A := fun ω : Sizes.SeqΩ d => (Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → _)
        - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ i} {a : Idx (d.L n) (d.W n) // a ≠ i} ℂ))
      (fun a b => (Sizes.measurable_seqHflow_entry d n u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-! ### Alignment with the LDE of `Green/EntryCore.lean` -/

variable {z : ℂ}

/-- Where the resolvent exists, the coefficients `minorCol` are the entries of `G^{(i)}`. -/
theorem minorCol_eq_greenMinor (u : ℝ) {i : Idx (d.L n) (d.W n)}
    (j : {a : Idx (d.L n) (d.W n) // a ≠ i}) {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow d n u ω) z i i ≠ 0) {k : Idx (d.L n) (d.W n)} (hk : k ≠ i) :
    minorCol d n u z i j ω k = greenMinor (green (Sizes.seqHflow d n u ω) z) i k j.1 := by
  unfold minorCol
  simp only [ne_eq, hk, not_false_eq_true, ↓reduceDIte]
  rw [inv_minor_resolvent hdet i hGii]
  rfl

/-- **The left-hand side of the row LDE** is the row sum with the minor resolvent column. -/
theorem ldeRowLHS_eq (u : ℝ) {i : Idx (d.L n) (d.W n)} (j : {a : Idx (d.L n) (d.W n) // a ≠ i})
    {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow d n u ω) z i i ≠ 0) :
    ldeRowLHS (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z) i j.1
      = ‖rowSum d n u i (minorCol d n u z i j) ω‖ ^ 2 := by
  unfold ldeRowLHS rowSum
  congr 2
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-- **The right-hand side of the row LDE** is the variance of that row sum, up to the factor
`u`. -/
theorem rowVarSum_eq (u : ℝ) {i : Idx (d.L n) (d.W n)} (j : {a : Idx (d.L n) (d.W n) // a ≠ i})
    {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow d n u ω) z i i ≠ 0) :
    rowVarSum d n u i (minorCol d n u z i j) ω
      = u * ldeRowRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i j.1 := by
  unfold rowVarSum ldeRowRHS
  congr 1
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-! ### The fixed-coefficient bound in `ℝ≥0∞` form -/

theorem measurable_row_sum (u : ℝ) (i : Idx (d.L n) (d.W n)) (c : Idx (d.L n) (d.W n) → ℂ) :
    Measurable fun ω : Sizes.SeqΩ d =>
      ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * c k.1 :=
  Finset.measurable_sum _ fun k _ =>
    (Sizes.measurable_seqHflow_entry d n u i k.1).mul measurable_const

/-- All even moments of a row sum with fixed coefficients exist. -/
theorem integrable_norm_row_sum_pow (u : ℝ) (i : Idx (d.L n) (d.W n))
    (c : Idx (d.L n) (d.W n) → ℂ) (p : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ d =>
      ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p))
        (Sizes.seqP d) := by
  have hre := integrable_pow_lin (P := Sizes.seqP d) (measurable_rowVar (d := d) (n := n) i)
    (map_rowVar (d := d) (n := n) i) (iIndepFun_rowVar (d := d) (n := n) i)
    (rowRe d n u i c) Finset.univ p
  have him := integrable_pow_lin (P := Sizes.seqP d) (measurable_rowVar (d := d) (n := n) i)
    (map_rowVar (d := d) (n := n) i) (iIndepFun_rowVar (d := d) (n := n) i)
    (rowIm d n u i c) Finset.univ p
  refine ((hre.add him).const_mul ((2 : ℝ) ^ p)).mono'
    (((measurable_row_sum u i c).norm).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  set x := (∑ q : RowIdx d n i, rowRe d n u i c q * rowVar d n i q ω) with hx
  set y := (∑ q : RowIdx d n i, rowIm d n u i c q * rowVar d n i q ω) with hy
  have hz : ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
        Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p)
      = (x ^ 2 + y ^ 2) ^ p := by
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hx, hy, ← re_row_sum,
      ← im_row_sum]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hz]
  have hxy : (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
    have hx0 : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hy0 : (0 : ℝ) ≤ y ^ 2 := by positivity
    have h1 : (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h2 : max (x ^ 2) (y ^ 2) ^ p ≤ x ^ (2 * p) + y ^ (2 * p) := by
      rw [pow_mul, pow_mul]
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ (x ^ 2) ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ (y ^ 2) ^ p := by positivity
        linarith
    calc (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := h1
      _ = 2 ^ p * max (x ^ 2) (y ^ 2) ^ p := by rw [mul_pow]
      _ ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h2 this
  calc (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := hxy
    _ = _ := by simp only [Pi.add_apply, hx, hy]

/-- The fixed-coefficient bound, in `ℝ≥0∞` form. -/
theorem lintegral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    (c : Idx (d.L n) (d.W n) → ℂ) (p : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
        Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p)) ∂(Sizes.seqP d)
      ≤ ENNReal.ofReal (2 * (RowIndep_dfac p *
        (u * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
          svar (d.L n) (d.W n) i k.1 * ‖c k.1‖ ^ 2) ^ p)) := by
  have hint := integrable_norm_row_sum_pow u i c p
  have hnn : 0 ≤ᵐ[Sizes.seqP d] fun ω : Sizes.SeqΩ d =>
      ‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, Sizes.seqHflow d n u ω i k.1 * c k.1‖ ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal (integral_norm_row_sum_pow_le hu i c p)

/-! ### The row LDE without integrability hypotheses -/

/-- **Tonelli assembly, constant-bound form.**  If the coefficients `D` read only the off-row
block and their (random) variance obeys a uniform bound after the fixed-coefficient estimate, then
`∫⁻ ‖Z‖^{2p}` obeys that bound — with no integrability hypothesis. -/
theorem lintegral_norm_rowSum_pow_le_of_const (hu : 0 ≤ u)
    (D : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ) (hDmeas : Measurable D)
    (hDC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → D ω = D ω') {c : ℝ≥0∞}
    (hb : ∀ ω : Sizes.SeqΩ d,
      ENNReal.ofReal (2 * (RowIndep_dfac p * rowVarSum d n u i D ω ^ p)) ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum d n u i D ω‖ ^ (2 * p)) ∂(Sizes.seqP d) ≤ c := by
  classical
  set S := rowSet d n i with hS
  set T := offRowCoord d n i with hT
  set U : Sizes.SeqΩ d → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Sizes.SeqΩ d → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (Sizes.seqP d) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (d := d) (n := n) i
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (‖rowSum d n u i D (glue S T q)‖ ^ (2 * p)) with hF
  have hglue := measurable_glue (ι := Sizes.SeqCoord d) S T
  have hFmeas : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) _)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((Sizes.measurable_seqHflow_entry d n u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hDmeas).comp hglue)
  have hrow : ∀ ω : Sizes.SeqΩ d, rowSum d n u i D ω = rowSum d n u i D (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u D hDC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫⁻ x, F (x, y) ∂((Sizes.seqP d).map U)) ≤ c := by
    intro y
    have hFy : Measurable fun x : {c // c ∈ S} → ℝ => F (x, y) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_map hFy hUmeas]
    have hval : ∀ ω : Sizes.SeqΩ d, F (U ω, y)
        = ENNReal.ofReal (‖∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i},
            Sizes.seqHflow d n u ω i k.1 * D (glue S T (0, y)) k.1‖ ^ (2 * p)) := by
      intro ω
      simp only [hF, rowSum]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Sizes.seqHflow d n u (glue S T (U ω, y)) i k.1 = Sizes.seqHflow d n u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hDe : D (glue S T (U ω, y)) k.1 = D (glue S T (0, y)) k.1 := by
        have : D (glue S T (U ω, y)) = D (glue S T (0, y)) := by
          refine hDC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hDe]
    simp only [hval]
    exact (lintegral_norm_row_sum_pow_le hu i (D (glue S T (0, y))) p).trans
      (hb (glue S T (0, y)))
  have hmain := lintegral_indep_pair_le hUmeas hVmeas hindep hFmeas hinner
  calc ∫⁻ ω, ENNReal.ofReal (‖rowSum d n u i D ω‖ ^ (2 * p)) ∂(Sizes.seqP d)
      = ∫⁻ ω, F (U ω, V ω) ∂(Sizes.seqP d) := by
        refine lintegral_congr fun ω => ?_
        simp only [hF]
        rw [← hrow]
    _ ≤ c := hmain

/-- **The row LDE, `ℝ≥0∞` form, no side conditions.**  Conditionally on the off-row block the
normalised row sum is a centred complex Gaussian of variance `≤ 1`. -/
theorem lintegral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω') :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p)) ∂(Sizes.seqP d)
      ≤ ENNReal.ofReal (2 * RowIndep_dfac p) := by
  refine lintegral_norm_rowSum_pow_le_of_const hu (rowCoeffNorm d n u i C)
    (measurable_rowCoeffNorm C hCmeas) (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h)
    (fun ω => ENNReal.ofReal_le_ofReal ?_)
  have hvar := rowVarSum_rowCoeffNorm (d := d) (n := n) (u := u) (i := i) hu C ω
  have hd0 : (0 : ℝ) ≤ RowIndep_dfac p := by unfold RowIndep_dfac; positivity
  have hle : rowVarSum d n u i (rowCoeffNorm d n u i C) ω ^ p ≤ 1 := by
    rw [hvar]
    by_cases h : 0 < rowVarSum d n u i C ω
    · simp [h]
    · rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [h]
      · simp [h, zero_pow hp.ne']
  nlinarith [hle, hd0]

/-- Integrability of the normalised row sum, from the finiteness of the `ℝ≥0∞` bound. -/
theorem integrable_norm_rowSum_norm_pow (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω') :
    Integrable (fun ω => ‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p)) (Sizes.seqP d) := by
  have hmeas : Measurable fun ω : Sizes.SeqΩ d =>
      ‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p) := by
    unfold rowSum
    refine (Measurable.norm ?_).pow_const _
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (Sizes.measurable_seqHflow_entry d n u i k.1).mul
      ((measurable_pi_apply k.1).comp (measurable_rowCoeffNorm C hCmeas))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnn : ∀ ω : Sizes.SeqΩ d, ‖‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p)‖ₑ
      = ENNReal.ofReal (‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p)) :=
    fun ω => Real.enorm_eq_ofReal (by positivity)
  simp only [hnn]
  exact lt_of_le_of_lt (lintegral_norm_rowSum_norm_pow_le hu C hCmeas hC) ENNReal.ofReal_lt_top

/-- **The row LDE, Bochner form, no side conditions**: `E‖Z/√V‖^{2p} ≤ 2 (2p-1)!!`. -/
theorem integral_norm_rowSum_norm_pow_le' (hu : 0 ≤ u) (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω') :
    ∫ ω, ‖rowSum d n u i (rowCoeffNorm d n u i C) ω‖ ^ (2 * p) ∂(Sizes.seqP d)
      ≤ 2 * RowIndep_dfac p :=
  integral_norm_rowSum_norm_pow_le hu C hCmeas hC
    (integrable_norm_rowSum_norm_pow hu C hCmeas hC)

/-! ### The row LDE as stochastic domination -/

/-- The index set of the row LDE: a row `i` and a column `j ≠ i`. -/
abbrev LdeIdx (d : Sizes) (n : ℕ) : Type := Σ i : Idx (d.L n) (d.W n),
    {a : Idx (d.L n) (d.W n) // a ≠ i}

/-- The physical dimension `d.size n` is positive. -/
private theorem one_le_size (d : Sizes) (n : ℕ) : 1 ≤ d.size n :=
  Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))

/-- The index set of the row LDE has at most `(size n)²` elements, for every `n`
(here `Fintype.card (Idx L W) = size n`). -/
theorem card_LdeIdx_le (n : ℕ) :
    (Fintype.card (LdeIdx d n) : ℝ) ≤ (d.size n : ℝ) * (d.size n : ℝ) := by
  have hcard : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
    simp [Idx, Z2, Sizes.size, ZMod.card, sq]
  have : Fintype.card (LdeIdx d n)
      ≤ Fintype.card (Idx (d.L n) (d.W n)) * Fintype.card (Idx (d.L n) (d.W n)) := by
    calc Fintype.card (LdeIdx d n)
        = ∑ i : Idx (d.L n) (d.W n), Fintype.card {a : Idx (d.L n) (d.W n) // a ≠ i} :=
          Fintype.card_sigma
      _ ≤ ∑ _i : Idx (d.L n) (d.W n), Fintype.card (Idx (d.L n) (d.W n)) :=
          Finset.sum_le_sum fun i _ => Fintype.card_subtype_le _
      _ = Fintype.card (Idx (d.L n) (d.W n)) * Fintype.card (Idx (d.L n) (d.W n)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hcard] at this
  exact_mod_cast this

/-- The index set of the row LDE is polynomially large: `#LdeIdx ≤ (size n)²`. -/
theorem eventually_card_LdeIdx_le (d : Sizes) :
    ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (LdeIdx d n) : ℝ) ≤ (d.size n : ℝ) ^ (2 : ℝ) := by
  refine Filter.Eventually.of_forall fun n => ?_
  refine (card_LdeIdx_le n).trans (le_of_eq ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- **Stochastic domination for any row sum with off-row coefficients, with the time in the
index set.**  Given a family of times `tim n q ≥ 0`, rows `row n q` and coefficients `C n q`
that read only the corresponding off-row block, the normalised row sums are `≺ 1` along the
admissible size sequence `d.size`, uniformly over a polynomially large index set.

The hypothesis `hsize` is needed (and is not automatic for `Sizes`): for the constant sizes
`L n = 3`, `W n = 1` the domination would ask for probabilities `≤ 9^{-D}` for every `D`. -/
theorem stochDom_rowSum_generalTime (hsize : Filter.Tendsto d.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (d.size n : ℝ) ^ Ccard)
    (tim : ∀ n, U n → ℝ) (htim : ∀ n q, 0 ≤ tim n q)
    (row : ∀ n, U n → Idx (d.L n) (d.W n))
    (C : ∀ n, U n → Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ d),
      (∀ c ∈ offRowCoord d n (row n q), ω c = ω' c) → C n q ω = C n q ω') :
    StochDomAt (Sizes.seqP d) d.size
      (fun n q ω =>
        ‖rowSum d n (tim n q) (row n q)
          (rowCoeffNorm d n (tim n q) (row n q) (C n q)) ω‖)
      (fun _ _ _ => 1) := by
  refine stochDomAt_of_momentDomAt d.size hsize hcard (Φ := fun _ _ => (1 : ℝ))
    (fun _ _ => zero_lt_one) ?_ ?_
  · intro p n q
    have := integrable_norm_rowSum_norm_pow (d := d) (n := n) (u := tim n q) (i := row n q)
      (p := p) (htim n q) (C n q) (hCmeas n q) (fun ω ω' h => hC n q ω ω' h)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  · intro ε hε p
    have hd0 : (0 : ℝ) ≤ RowIndep_dfac p := by unfold RowIndep_dfac; positivity
    refine ⟨2 * RowIndep_dfac p + 1, by linarith, ?_⟩
    refine Filter.Eventually.of_forall fun n q => ?_
    have hn1 : (1 : ℝ) ≤ (d.size n : ℝ) := by exact_mod_cast one_le_size d n
    have hbound := integral_norm_rowSum_norm_pow_le' (d := d) (n := n) (u := tim n q)
      (i := row n q) (p := p) (htim n q) (C n q) (hCmeas n q) (fun ω ω' h => hC n q ω ω' h)
    have habs : ∫ ω, |‖rowSum d n (tim n q) (row n q)
          (rowCoeffNorm d n (tim n q) (row n q) (C n q)) ω‖| ^ (2 * p) ∂(Sizes.seqP d)
        = ∫ ω, ‖rowSum d n (tim n q) (row n q)
            (rowCoeffNorm d n (tim n q) (row n q) (C n q)) ω‖ ^ (2 * p) ∂(Sizes.seqP d) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [abs_norm]
    rw [habs]
    have hpow : (1 : ℝ) ≤ (d.size n : ℝ) ^ (ε * p) := Real.one_le_rpow hn1 (by positivity)
    have : (2 * RowIndep_dfac p)
        ≤ (2 * RowIndep_dfac p + 1) * ((d.size n : ℝ) ^ (ε * p) * 1 ^ (2 * p)) := by
      rw [one_pow, mul_one]
      nlinarith [hpow, hd0]
    linarith [hbound, this]

/-! ### The column LDE, by Hermitian symmetry -/

/-- The conjugate of the `k`-th row of the minor resolvent `(H^{(j)} - z)^{-1}`, as coefficients
indexed by all of `Idx (d.L n) (d.W n)` (zero at `j`).  By Hermitian symmetry the column sum of
the paper is the conjugate of the row sum with these coefficients. -/
noncomputable def minorRowConj (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (j : Idx (d.L n) (d.W n))
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j}) (ω : Sizes.SeqΩ d) (l : Idx (d.L n) (d.W n)) : ℂ :=
  if h : l ≠ j then
    (starRingEnd ℂ) ((((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ j} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ j} → _)
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ j}
        {a : Idx (d.L n) (d.W n) // a ≠ j} ℂ))⁻¹) k ⟨l, h⟩)
  else 0

theorem minorRowConj_congr (u : ℝ) (z : ℂ) {j : Idx (d.L n) (d.W n)}
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j})
    {ω ω' : Sizes.SeqΩ d} (h : ∀ c ∈ offRowCoord d n j, ω c = ω' c) :
    minorRowConj d n u z j k ω = minorRowConj d n u z j k ω' := by
  funext l
  unfold minorRowConj
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorRowConj (u : ℝ) (z : ℂ) (j : Idx (d.L n) (d.W n))
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j}) : Measurable (minorRowConj d n u z j k) := by
  refine Measurable.of_eval fun l => ?_
  unfold minorRowConj
  split
  · refine Complex.continuous_conj.measurable.comp ?_
    exact measurable_inv_entries
      (A := fun ω : Sizes.SeqΩ d => (Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ j} → _)
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ j} → _)
        - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ j} {a : Idx (d.L n) (d.W n) // a ≠ j} ℂ))
      (fun a b => (Sizes.measurable_seqHflow_entry d n u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-- **The degenerate case.**  Where the conditional variance vanishes, so does the row sum,
almost surely: freezing the coefficients to `0` off that event gives a family whose variance is
identically `0`, hence whose second moment vanishes. -/
theorem rowSum_ae_eq_zero_of_varSum_eq_zero (hu : 0 ≤ u)
    (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ) (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → C ω = C ω') :
    ∀ᵐ ω ∂(Sizes.seqP d), rowVarSum d n u i C ω = 0 → rowSum d n u i C ω = 0 := by
  classical
  set D : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ :=
    fun ω k => if rowVarSum d n u i C ω = 0 then C ω k else 0 with hD
  have hVmeas : Measurable (rowVarSum d n u i C) := measurable_rowVarSum C hCmeas
  have hDmeas : Measurable D := by
    refine Measurable.of_eval fun k => ?_
    exact Measurable.ite (measurableSet_eq_fun hVmeas measurable_const)
      ((measurable_pi_apply k).comp hCmeas) measurable_const
  have hDC : ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ offRowCoord d n i, ω c = ω' c) → D ω = D ω' := by
    intro ω ω' h
    have hCe := hC ω ω' h
    funext k
    simp only [hD, rowVarSum, hCe]
    rfl
  have hDvar : ∀ ω : Sizes.SeqΩ d, rowVarSum d n u i D ω = 0 := by
    intro ω
    by_cases h : rowVarSum d n u i C ω = 0
    · have : D ω = C ω := by funext k; simp [hD, h]
      simp only [rowVarSum] at h ⊢
      rw [this]
      exact h
    · have : D ω = fun _ => (0 : ℂ) := by funext k; simp [hD, h]
      simp [rowVarSum, this]
  -- the second moment of the family of fixed coefficients vanishes
  have hzero : ∫⁻ ω, ENNReal.ofReal (‖rowSum d n u i D ω‖ ^ (2 * 1)) ∂(Sizes.seqP d) = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine lintegral_norm_rowSum_pow_le_of_const hu D hDmeas hDC fun ω => ?_
    simp [hDvar ω]
  have hae : ∀ᵐ ω ∂(Sizes.seqP d), ENNReal.ofReal (‖rowSum d n u i D ω‖ ^ (2 * 1)) = 0 := by
    rw [lintegral_eq_zero_iff'] at hzero
    · exact hzero
    · refine (ENNReal.measurable_ofReal.comp
        (Measurable.pow_const (Measurable.norm ?_) _)).aemeasurable
      unfold rowSum
      exact Finset.measurable_sum _ fun k _ =>
        (Sizes.measurable_seqHflow_entry d n u i k.1).mul ((measurable_pi_apply k.1).comp hDmeas)
  filter_upwards [hae] with ω hω hV
  have hDC' : D ω = C ω := by funext k; simp [hD, hV]
  have : ‖rowSum d n u i D ω‖ ^ (2 * 1) = 0 := by
    have := ENNReal.ofReal_eq_zero.1 hω
    have hnn : (0 : ℝ) ≤ ‖rowSum d n u i D ω‖ ^ (2 * 1) := by positivity
    linarith
  have hnorm : ‖rowSum d n u i D ω‖ = 0 := by
    have hp : ‖rowSum d n u i D ω‖ ^ (2 * 1) = ‖rowSum d n u i D ω‖ ^ 2 := by norm_num
    rw [hp, pow_eq_zero_iff (by norm_num)] at this
    exact this
  have : rowSum d n u i D ω = 0 := by simpa using hnorm
  rwa [show rowSum d n u i D ω = rowSum d n u i C ω by
    unfold rowSum; simp only [hDC']] at this

/-- Normalising the coefficients divides the row sum by the conditional standard deviation. -/
theorem rowSum_rowCoeffNorm (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ) {ω : Sizes.SeqΩ d}
    (hV : 0 < rowVarSum d n u i C ω) :
    rowSum d n u i (rowCoeffNorm d n u i C) ω
      = ((Real.sqrt (rowVarSum d n u i C ω) : ℂ))⁻¹ * rowSum d n u i C ω := by
  unfold rowSum rowCoeffNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hV, ↓reduceIte]
  field_simp

end RBM.Green
