/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Model
import RBM2D.Defs.StochDom
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The one-time Gaussian matrix model

The paper's indices are `ZMod (W * L) × ZMod (W * L)`, and its entry variance is
`Spaper L W i j`.  We use a finite product of independent real Gaussians.  An off-diagonal
entry uses two real coordinates, each of variance `S_ij / 2`; a diagonal entry uses one real
coordinate of variance `S_ii`.  The paper's phrase “complex Gaussian” on the diagonal must
be read with this standard Hermitian convention: a non-real diagonal entry would contradict
`X_ii = conj X_ii`.

`Hflow u = √u • Xmat` has the required one-time marginal law.  It is a deterministic
coupling across times, not a matrix Brownian motion.

`Sizes.seqP` takes the countable product over all size parameters.  Its size projection
has law `P L W` (`Sizes.seqP_map_slice`), so the same probability measure can be used in
`StochDomAt` for the whole admissible sequence.  Both the fixed-size and sequence-level
matrices have proved covariance identities and exact coordinate update formulas.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The exact fine-lattice index set of Section 2.1. -/
abbrev Idx := Z2 (W * L)

/-- The real form of the paper's variance profile. -/
noncomputable def svar (i j : Idx L W) : ℝ :=
  if (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L
  then (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 else 0

omit [NeZero L] [NeZero W] in
theorem svar_nonneg (i j : Idx L W) : 0 ≤ svar L W i j := by
  unfold svar
  split_ifs <;> positivity

omit [NeZero L] [NeZero W] in
theorem svar_comm (i j : Idx L W) : svar L W i j = svar L W j i := by
  unfold svar
  have h : (blk L W j.1, blk L W j.2) - (blk L W i.1, blk L W i.2) =
      -((blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2)) := by
    abel
  simp only [h, neg_mem_sbSupport]

omit [NeZero L] [NeZero W] in
/-- Agreement with the covariance already formalized in `Defs/Model.lean`. -/
theorem svar_cast_eq_Spaper (i j : Idx L W) :
    (svar L W i j : ℂ) = Spaper L W i j := by
  rw [svar, Spaper_indicator]
  split_ifs
  · push_cast
    rfl
  · simp

omit [NeZero L] [NeZero W] in
/-- The diagonal entry variance. -/
theorem svar_diag (i : Idx L W) :
    svar L W i i = (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 := by
  have h : (0 : Z2 L) ∈ sbSupport L := by
    change ((0 : ZMod L), (0 : ZMod L)) ∈ sbSupport L
    simp [sbSupport]
  simp only [svar, sub_self, ite_eq_left_iff]
  intro hn
  exact False.elim (hn h)

omit [NeZero L] in
/-- Nondegeneracy of every diagonal Gaussian coordinate. -/
theorem svar_diag_pos (i : Idx L W) : 0 < svar L W i i := by
  rw [svar_diag]
  have hW : (0 : ℝ) < W := by exact_mod_cast NeZero.pos W
  positivity

/-- A finite injective key, used only to orient independent off-diagonal entries. -/
noncomputable def idxKey (i : Idx L W) : ℕ := (Fintype.equivFin (Idx L W) i).val

theorem idxKey_injective : Function.Injective (idxKey L W) := fun _ _ h =>
  (Fintype.equivFin (Idx L W)).injective (Fin.val_injective h)

theorem idxKey_lt_or_eq_or_lt (i j : Idx L W) :
    idxKey L W i < idxKey L W j ∨ i = j ∨ idxKey L W j < idxKey L W i := by
  rcases lt_trichotomy (idxKey L W i) (idxKey L W j) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (idxKey_injective L W h))
  · exact Or.inr (Or.inr h)

/-- Two real coordinates per oriented pair.  The lower-triangular and imaginary diagonal
coordinates are unused independent noise; this choice makes the product index simple. -/
abbrev Coord := Idx L W × Idx L W × Bool

/-- The finite product sample space. -/
abbrev Ω := Coord L W → ℝ

/-- Diagonal coordinate variance `S_ii`; off-diagonal coordinate variance `S_ij/2`. -/
noncomputable def gvar (c : Coord L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svar L W c.1 c.2.1 else svar L W c.1 c.2.1 / 2, by
    split_ifs
    · exact svar_nonneg L W _ _
    · exact div_nonneg (svar_nonneg L W _ _) (by norm_num)⟩

omit [NeZero L] [NeZero W] in
@[simp] theorem gvar_diag (i : Idx L W) (b : Bool) :
    (gvar L W (i, i, b) : ℝ) = svar L W i i := by
  change (if i = i then svar L W i i else svar L W i i / 2) = _
  simp

omit [NeZero L] [NeZero W] in
theorem gvar_offDiag (i j : Idx L W) (b : Bool) (hij : i ≠ j) :
    (gvar L W (i, j, b) : ℝ) = svar L W i j / 2 := by
  change (if i = j then svar L W i j else svar L W i j / 2) = _
  simp [hij]

/-- The finite product of independent centered real Gaussian laws. -/
noncomputable def P : Measure (Ω L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gvar L W c)

instance isProbabilityMeasure_P : IsProbabilityMeasure (P L W) := by
  unfold P
  infer_instance

omit [NeZero L] [NeZero W] in
/-- Marginal law of one independent real coordinate. -/
theorem P_map_eval (c : Coord L W) :
    (P L W).map (fun ω => ω c) = gaussianReal 0 (gvar L W c) :=
  Measure.infinitePi_map_eval _ c

omit [NeZero L] [NeZero W] in
/-- Every finite collection of coordinates has its independent product law. -/
theorem P_map_restrict (I : Finset (Coord L W)) :
    (P L W).map I.restrict = Measure.pi fun c : I => gaussianReal 0 (gvar L W c) :=
  Measure.infinitePi_map_restrict _

/-- An entry of the Hermitian matrix, oriented by `idxKey`. -/
noncomputable def Xentry (ω : Ω L W) (i j : Idx L W) : ℂ :=
  if idxKey L W i < idxKey L W j then
    (ω (i, j, true) : ℂ) + Complex.I * (ω (i, j, false) : ℂ)
  else if idxKey L W j < idxKey L W i then
    (ω (j, i, true) : ℂ) - Complex.I * (ω (j, i, false) : ℂ)
  else (ω (i, j, true) : ℂ)

/-- The fixed one-time Gaussian matrix. -/
noncomputable def Xmat (ω : Ω L W) : Matrix (Idx L W) (Idx L W) ℂ :=
  Matrix.of fun i j => Xentry L W ω i j

@[simp] theorem Xmat_apply (ω : Ω L W) (i j : Idx L W) :
    Xmat L W ω i j = Xentry L W ω i j := rfl

theorem Xentry_swap (ω : Ω L W) (i j : Idx L W) :
    Xentry L W ω j i = (starRingEnd ℂ) (Xentry L W ω i j) := by
  unfold Xentry
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · rw [ite_eq_right (asymm h), ite_eq_left h, ite_eq_left h]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    simp only [Complex.conj_ofReal]
  · rw [ite_eq_left h, ite_eq_right (asymm h), ite_eq_left h]
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- Hermitian symmetry holds at every sample point. -/
theorem Xmat_isHermitian (ω : Ω L W) : (Xmat L W ω).IsHermitian := by
  ext i j
  exact (Xentry_swap L W ω j i).symm

theorem measurable_Xentry (i j : Idx L W) :
    Measurable fun ω : Ω L W => Xentry L W ω i j := by
  unfold Xentry
  split_ifs <;> exact by fun_prop

/-! ### The defining entry covariance -/

omit [NeZero L] [NeZero W] in
theorem integrable_sq_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => (ω c) ^ 2) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gvar L W c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

omit [NeZero L] [NeZero W] in
theorem integral_sq_coord (c : Coord L W) :
    ∫ ω, (ω c) ^ 2 ∂(P L W) = (gvar L W c : ℝ) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((P L W).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := gvar L W c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- `E |X_ij|² = S_ij`, including the real diagonal convention. -/
theorem integral_normSq_Xentry (i j : Idx L W) :
    ∫ ω, ‖Xentry L W ω i j‖ ^ 2 ∂(P L W) = svar L W i j := by
  have key : ∀ (p q : Coord L W) (S : ℝ), (gvar L W p : ℝ) = S / 2 →
      (gvar L W q : ℝ) = S / 2 →
      (∫ ω, ((ω p) ^ 2 + (ω q) ^ 2) ∂(P L W)) = S := by
    intro p q S hp hq
    rw [integral_add (integrable_sq_coord L W p) (integrable_sq_coord L W q),
      integral_sq_coord, integral_sq_coord, hp, hq]
    ring
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω L W, ‖Xentry L W ω i j‖ ^ 2 =
        (ω (i, j, true)) ^ 2 + (ω (i, j, false)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    exact key _ _ _ (gvar_offDiag L W i j true hij) (gvar_offDiag L W i j false hij)
  · subst h
    have hX : ∀ ω : Ω L W, ‖Xentry L W ω i i‖ ^ 2 = (ω (i, i, true)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    simp only [hX]
    rw [integral_sq_coord, gvar_diag]
  · have hij : j ≠ i := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω L W, ‖Xentry L W ω i j‖ ^ 2 =
        (ω (j, i, true)) ^ 2 + (ω (j, i, false)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    rw [key _ _ (svar L W j i) (gvar_offDiag L W j i true hij)
      (gvar_offDiag L W j i false hij)]
    exact (svar_comm L W i j).symm

/-! ### Linear decomposition into independent real coordinates -/

/-- The matrix depends additively on its real Gaussian coordinates. -/
theorem Xmat_add (ω ν : Ω L W) :
    Xmat L W (ω + ν) = Xmat L W ω + Xmat L W ν := by
  ext i j
  simp only [Xmat_apply, Matrix.add_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.add_apply, Complex.ofReal_add] <;> ring

/-- Real scaling of every coordinate scales the entire matrix. -/
theorem Xmat_smul (t : ℝ) (ω : Ω L W) :
    Xmat L W (t • ω) = t • Xmat L W ω := by
  ext i j
  simp only [Xmat_apply, Matrix.smul_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Algebra.smul_def, Complex.coe_algebraMap] <;> ring

/-- The real-linear map from independent coordinates to the Hermitian matrix. -/
noncomputable def Xlinear : Ω L W →ₗ[ℝ] Matrix (Idx L W) (Idx L W) ℂ where
  toFun := Xmat L W
  map_add' := Xmat_add L W
  map_smul' := Xmat_smul L W

/-- The matrix direction attached to one independent real coordinate.  Unused coordinates
give the zero matrix. -/
noncomputable def coordinateMatrix (c : Coord L W) :
    Matrix (Idx L W) (Idx L W) ℂ := Xmat L W (Pi.single c 1)

@[simp] theorem coordinateMatrix_apply (c : Coord L W) (i j : Idx L W) :
    coordinateMatrix L W c i j = Xentry L W (Pi.single c 1) i j := rfl

theorem coordinateMatrix_isHermitian (c : Coord L W) :
    (coordinateMatrix L W c).IsHermitian := Xmat_isHermitian L W _

/-- Replacing one real coordinate moves the matrix in its coordinate direction. -/
theorem Xmat_update (ω : Ω L W) (c : Coord L W) (t : ℝ) :
    Xmat L W (Function.update ω c t) =
      Xmat L W ω + (t - ω c) • coordinateMatrix L W c := by
  have hupdate : Function.update ω c t = ω + (t - ω c) • Pi.single c (1 : ℝ) := by
    funext d
    by_cases h : d = c
    · subst h
      simp [Function.update_self, Pi.single_eq_same, Pi.add_apply, Pi.smul_apply]
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h, Pi.add_apply, Pi.smul_apply]
  rw [hupdate, Xmat_add, Xmat_smul]
  rfl

/-- Exact finite coordinate decomposition of the one-time Gaussian matrix. -/
theorem Xmat_eq_sum_coordinates (ω : Ω L W) :
    Xmat L W ω = ∑ c : Coord L W, (ω c) • coordinateMatrix L W c := by
  calc
    Xmat L W ω = Xlinear L W ω := rfl
    _ = Xlinear L W (∑ c : Coord L W, Pi.single c (ω c)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ c : Coord L W, (ω c) • coordinateMatrix L W c := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro c _
      have hsingle : Pi.single c (ω c) = (ω c) • (Pi.single c (1 : ℝ)) := by
        ext d
        by_cases h : d = c
        · subst h; simp
        · simp [h, Pi.smul_apply]
      rw [hsingle, map_smul]
      rfl

/-- The matrix is continuous as a function of the Gaussian coordinate vector. -/
theorem continuous_Xmat : Continuous (Xmat L W) := by
  have h : Xmat L W = fun ω : Ω L W =>
      ∑ c : Coord L W, (ω c) • coordinateMatrix L W c :=
    funext (Xmat_eq_sum_coordinates L W)
  rw [h]
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).smul continuous_const

/-- The one-time replacement for the paper's matrix Brownian flow. -/
noncomputable def Hflow (u : ℝ) (ω : Ω L W) : Matrix (Idx L W) (Idx L W) ℂ :=
  (Real.sqrt u : ℂ) • Xmat L W ω

@[simp] theorem Hflow_apply (u : ℝ) (ω : Ω L W) (i j : Idx L W) :
    Hflow L W u ω i j = (Real.sqrt u : ℂ) * Xentry L W ω i j := rfl

@[simp] theorem Hflow_zero (ω : Ω L W) : Hflow L W 0 ω = 0 := by
  simp [Hflow]

/-- The same flow written with the real scalar action used by differentiation. -/
theorem Hflow_eq_realSmul (u : ℝ) (ω : Ω L W) :
    Hflow L W u ω = Real.sqrt u • Xmat L W ω := by
  ext i j
  change (Real.sqrt u : ℂ) * Xentry L W ω i j =
    Real.sqrt u • Xentry L W ω i j
  rw [Complex.real_smul]

theorem continuous_Hflow (u : ℝ) : Continuous (Hflow L W u) := by
  have h : Hflow L W u = fun ω : Ω L W => Real.sqrt u • Xmat L W ω :=
    funext (Hflow_eq_realSmul L W u)
  rw [h]
  exact (continuous_Xmat L W).const_smul (Real.sqrt u)

theorem Hflow_isHermitian (u : ℝ) (ω : Ω L W) :
    (Hflow L W u ω).IsHermitian := by
  ext i j
  change (starRingEnd ℂ) ((Real.sqrt u : ℂ) * Xentry L W ω j i) =
    (Real.sqrt u : ℂ) * Xentry L W ω i j
  rw [map_mul, Complex.conj_ofReal, ← Xentry_swap]

theorem measurable_Hflow (u : ℝ) (i j : Idx L W) :
    Measurable fun ω : Ω L W => Hflow L W u ω i j := by
  simp only [Hflow_apply]
  exact (measurable_Xentry L W i j).const_mul _

/-- The entire time dependence is one scalar. -/
theorem Hflow_sub (u v : ℝ) (ω : Ω L W) :
    Hflow L W u ω - Hflow L W v ω =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) • Xmat L W ω := by
  simp only [Hflow, Complex.ofReal_sub, sub_smul]

/-- Entrywise coordinate decomposition of the time increment. -/
theorem Hflow_sub_apply (u v : ℝ) (ω : Ω L W) (i j : Idx L W) :
    (Hflow L W u ω - Hflow L W v ω) i j =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) * Xentry L W ω i j := by
  rw [Hflow_sub]
  rfl

/-- The flow's entry variance is `u S_ij` for nonnegative time. -/
theorem integral_normSq_Hflow (u : ℝ) (hu : 0 ≤ u) (i j : Idx L W) :
    ∫ ω, ‖Hflow L W u ω i j‖ ^ 2 ∂(P L W) = u * svar L W i j := by
  simp only [Hflow_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), mul_pow]
  rw [integral_const_mul, integral_normSq_Xentry, Real.sq_sqrt hu]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- Exact deterministic modulus for the operator norm along the one-time coupling. -/
theorem norm_Hflow_sub (u v : ℝ) (ω : Ω L W) :
    ‖Hflow L W u ω - Hflow L W v ω‖ =
      |Real.sqrt u - Real.sqrt v| * ‖Xmat L W ω‖ := by
  rw [Hflow_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]

end OperatorNorm

/-- Concrete nonzero instance: a diagonal entry at `L = 3`, `W = 1` has variance `1/5`. -/
theorem nontrivial_diagonal_example :
    ∫ ω, ‖Xentry 3 1 ω ((0, 0) : Idx 3 1) (0, 0)‖ ^ 2 ∂(P 3 1) =
    (5 : ℝ)⁻¹ := by
  rw [integral_normSq_Xentry, svar_diag]
  norm_num

/-! ### A common probability space for an admissible size sequence -/

/-- Only the size data needed by the Gaussian construction.  Quantitative bandwidth
hypotheses belong to the later asymptotic estimates. -/
structure Sizes where
  L : ℕ → ℕ
  W : ℕ → ℕ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n

namespace Sizes

variable (d : Sizes)

instance neZeroL (n : ℕ) : NeZero (d.L n) := ⟨by have := d.three_le_L n; omega⟩
instance neZeroW (n : ℕ) : NeZero (d.W n) := ⟨(d.W_pos n).ne'⟩

/-- The full matrix dimension along this admissible sequence. -/
def size (n : ℕ) : ℕ := (d.W n * d.L n) ^ 2

theorem size_eq (n : ℕ) : size d n = d.W n ^ 2 * d.L n ^ 2 := by
  simp [size, mul_pow]

/-- A coordinate records its size parameter as well as the entry and real/imaginary tag. -/
abbrev SeqCoord := Σ n : ℕ, Coord (d.L n) (d.W n)

/-- One common sample space for all sizes. -/
abbrev SeqΩ := SeqCoord d → ℝ

noncomputable def seqGvar (c : SeqCoord d) : ℝ≥0 :=
  gvar (d.L c.1) (d.W c.1) c.2

/-- Independent Gaussian coordinates for every size in one countable product. -/
noncomputable def seqP : Measure (SeqΩ d) :=
  Measure.infinitePi fun c => gaussianReal 0 (seqGvar d c)

instance isProbabilityMeasure_seqP : IsProbabilityMeasure (seqP d) := by
  unfold seqP
  infer_instance

/-- The coordinate vector at one size, extracted from the common product. -/
def slice (n : ℕ) (ω : SeqΩ d) : Ω (d.L n) (d.W n) := fun c => ω ⟨n, c⟩

theorem measurable_slice (n : ℕ) : Measurable (slice d n) := by
  exact Measurable.of_eval fun (c : Coord (d.L n) (d.W n)) =>
    measurable_pi_apply (⟨n, c⟩ : SeqCoord d)

theorem seqP_map_eval (c : SeqCoord d) :
    (seqP d).map (fun ω => ω c) = gaussianReal 0 (seqGvar d c) :=
  Measure.infinitePi_map_eval _ c

theorem seqP_map_restrict (I : Finset (SeqCoord d)) :
    (seqP d).map I.restrict = Measure.pi fun c : I => gaussianReal 0 (seqGvar d c) :=
  Measure.infinitePi_map_restrict _

/-- Every size projection of the common product has exactly the fixed-size Gaussian law. -/
theorem seqP_map_slice (n : ℕ) :
    (seqP d).map (slice d n) = P (d.L n) (d.W n) := by
  classical
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : Coord (d.L n) (d.W n) → SeqCoord d := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : SeqCoord d → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : slice d n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (measurable_slice d n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, seqP, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e, seqGvar]

/-- The size-`n` matrix on the common probability space. -/
noncomputable def seqXmat (n : ℕ) (ω : SeqΩ d) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  Xmat (d.L n) (d.W n) (slice d n ω)

/-- The one-time flow on the common probability space. -/
noncomputable def seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ d) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  Hflow (d.L n) (d.W n) u (slice d n ω)

theorem seqHflow_eq_smul (n : ℕ) (u : ℝ) (ω : SeqΩ d) :
    seqHflow d n u ω = (Real.sqrt u : ℂ) • seqXmat d n ω := rfl

@[simp] theorem seqHflow_zero (n : ℕ) (ω : SeqΩ d) : seqHflow d n 0 ω = 0 :=
  Hflow_zero _ _ _

theorem seqXmat_isHermitian (n : ℕ) (ω : SeqΩ d) :
    (seqXmat d n ω).IsHermitian := Xmat_isHermitian _ _ _

theorem seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ d) :
    (seqHflow d n u ω).IsHermitian := Hflow_isHermitian _ _ _ _

theorem measurable_seqHflow_entry (n : ℕ) (u : ℝ)
    (i j : Idx (d.L n) (d.W n)) :
    Measurable fun ω : SeqΩ d => seqHflow d n u ω i j :=
  (measurable_Hflow _ _ u i j).comp (measurable_slice d n)

/-- The size-`n` matrix has the paper's covariance under the common probability measure. -/
theorem integral_normSq_seqXmat (n : ℕ) (i j : Idx (d.L n) (d.W n)) :
    ∫ ω, ‖seqXmat d n ω i j‖ ^ 2 ∂(seqP d) =
      svar (d.L n) (d.W n) i j := by
  change ∫ ω, ‖Xentry (d.L n) (d.W n) (slice d n ω) i j‖ ^ 2 ∂(seqP d) = _
  have hf : AEMeasurable (slice d n) (seqP d) := (measurable_slice d n).aemeasurable
  have hg : AEStronglyMeasurable
      (fun v : Ω (d.L n) (d.W n) => ‖Xentry (d.L n) (d.W n) v i j‖ ^ 2)
      ((seqP d).map (slice d n)) := by
    exact ((measurable_Xentry (d.L n) (d.W n) i j).norm.pow_const 2).aestronglyMeasurable
  rw [← integral_map hf hg, seqP_map_slice]
  exact integral_normSq_Xentry _ _ _ _

/-- The common-space flow has entry variance `u S_ij` at nonnegative time. -/
theorem integral_normSq_seqHflow (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (i j : Idx (d.L n) (d.W n)) :
    ∫ ω, ‖seqHflow d n u ω i j‖ ^ 2 ∂(seqP d) =
      u * svar (d.L n) (d.W n) i j := by
  change ∫ ω, ‖Hflow (d.L n) (d.W n) u (slice d n ω) i j‖ ^ 2 ∂(seqP d) = _
  have hf : AEMeasurable (slice d n) (seqP d) := (measurable_slice d n).aemeasurable
  have hg : AEStronglyMeasurable
      (fun v : Ω (d.L n) (d.W n) => ‖Hflow (d.L n) (d.W n) u v i j‖ ^ 2)
      ((seqP d).map (slice d n)) := by
    exact ((measurable_Hflow (d.L n) (d.W n) u i j).norm.pow_const 2).aestronglyMeasurable
  rw [← integral_map hf hg, seqP_map_slice]
  exact integral_normSq_Hflow _ _ _ hu _ _

/-- Exact coordinate decomposition at every size on the common space. -/
theorem seqXmat_eq_sum_coordinates (n : ℕ) (ω : SeqΩ d) :
    seqXmat d n ω = ∑ c : Coord (d.L n) (d.W n),
      (ω ⟨n, c⟩) • coordinateMatrix (d.L n) (d.W n) c :=
  Xmat_eq_sum_coordinates _ _ _

/-- Updating one common-space coordinate updates only its matrix direction at this size. -/
theorem seqXmat_update (n : ℕ) (ω : SeqΩ d)
    (c : Coord (d.L n) (d.W n)) (t : ℝ) :
    seqXmat d n (Function.update ω ⟨n, c⟩ t) =
      seqXmat d n ω + (t - ω ⟨n, c⟩) • coordinateMatrix (d.L n) (d.W n) c := by
  have hslice : slice d n (Function.update ω ⟨n, c⟩ t) =
      Function.update (slice d n ω) c t := by
    funext a
    by_cases h : a = c
    · subst h; simp [slice]
    · have hne : (⟨n, a⟩ : SeqCoord d) ≠ ⟨n, c⟩ := fun he => h (by cases he; rfl)
      simp [slice, Function.update_of_ne h, Function.update_of_ne hne]
  change Xmat (d.L n) (d.W n) (slice d n (Function.update ω ⟨n, c⟩ t)) = _
  rw [hslice, Xmat_update]
  rfl

/-- A concrete inhabitant proves that the size-sequence interface is satisfiable. -/
def constantSizes : Sizes where
  L := fun _ => 3
  W := fun _ => 1
  three_le_L := fun _ => by norm_num
  W_pos := fun _ => by norm_num

end Sizes

end RBM.Gauss
