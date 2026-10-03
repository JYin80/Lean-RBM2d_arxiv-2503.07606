/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.OU
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Courant-Fischer, Weyl, and measurability of the `k`-point functional

Weyl's inequality in Frobenius form (`eigenvalues₀_abs_sub_le`, via Courant-Fischer) and
measurability of the correlation sums (`measurable_corrSum`).

* `eigenvalues₀_abs_sub_le` -- Weyl: `|λ_i(A) - λ_i(B)| ≤ √(∑_{ab} |(A - B)_{ab}|²)`.
* `measurable_corrSum` -- measurability of `∑_f O(c (λ_{f j} - E))` for measurable Hermitian `H`.
* `measurable_kPoint_eigenvalues` -- measurability of `ω ↦ kPoint k O E (λ(H ω))`.
* `integral_kPoint_eq_of_map_eq` -- equal laws give equal `kPoint` expectations.

The Frobenius bound on the operator norm is `EigenMeasurable.opNorm_sq_le_frob`.
-/

noncomputable section

namespace RBM.Univ

section EigenWeyl

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The operator norm is bounded by the Frobenius norm: `‖A‖² ≤ ∑ |A_ij|²`. -/
private theorem EigenMeasurable.opNorm_sq_le_frob {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  set F : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hbd : ‖A‖ ≤ Real.sqrt F := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hF, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg F, mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg F]

/-! ### Abstract Courant–Fischer inequalities for a symmetric operator -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-- The real part of `⟪T v, v⟫` decomposes over the eigenbasis of a symmetric operator. -/
private lemma EigenWeyl.reInner_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    RCLike.re (inner ℂ (T v) v) =
      ∑ j : Fin m, hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  have hb := (hT.eigenvectorBasis hn).repr.inner_map_map (T v) v
  rw [← hb, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn v j, RCLike.inner_apply', map_mul (starRingEnd ℂ),
    RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul, RCLike.re_ofReal_mul, RCLike.re_ofReal_pow]

/-- Parseval: `‖v‖²` decomposes over the eigenbasis of a symmetric operator. -/
private lemma EigenWeyl.norm_sq_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    ‖v‖ ^ 2 = ∑ j : Fin m, ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_sq_eq]

/-- A vector in the span of a finite sub-family of the eigenbasis has zero coordinates outside
that sub-family. -/
private lemma EigenWeyl.repr_eq_zero_of_not_mem {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) {s : Finset (Fin m)} {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
    {j : Fin m} (hj : j ∉ s) :
    (hT.eigenvectorBasis hn).repr x j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℂ)).mp hx
  rw [← hc, map_sum]
  simp only [map_smul]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : j ≠ k := fun h => hj (h ▸ hk)
  rw [(hT.eigenvectorBasis hn).repr_self k]
  simp [hkj]

/-- The dimension of the span of the eigenvectors indexed by a finite set of indices. -/
private lemma EigenWeyl.finrank_span_eigenvectorBasis {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (s : Finset (Fin m)) :
    Module.finrank ℂ (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
      = s.card := by
  classical
  have hli : LinearIndependent ℂ ((hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m)) :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp
      ((↑) : s → Fin m) Subtype.val_injective
  have hrange : Set.range ((hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m))
      = (hT.eigenvectorBasis hn) '' (s : Set (Fin m)) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨(k : Fin m), k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
  have hfr := finrank_span_eq_card hli
  rw [hrange] at hfr
  rw [hfr, Fintype.card_coe]

/-- On the span of the top `i + 1` eigenvectors, the Rayleigh quotient of a symmetric operator
is at least the `i`-th eigenvalue. -/
private lemma EigenWeyl.rayleigh_ge_of_mem_Iic {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))) :
    hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  rw [EigenWeyl.reInner_eq_sum hT hn x, EigenWeyl.norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Iic i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj))
      (sq_nonneg _)
  · rw [EigenWeyl.repr_eq_zero_of_not_mem hT hn hx hj]; simp

/-- On the span of the bottom `m - i` eigenvectors, the Rayleigh quotient of a symmetric operator
is at most the `i`-th eigenvalue. -/
private lemma EigenWeyl.rayleigh_le_of_mem_Ici {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Ici i : Set (Fin m)))) :
    RCLike.re (inner ℂ (T x) x) ≤ hT.eigenvalues hn i * ‖x‖ ^ 2 := by
  rw [EigenWeyl.reInner_eq_sum hT hn x, EigenWeyl.norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Ici i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj))
      (sq_nonneg _)
  · rw [EigenWeyl.repr_eq_zero_of_not_mem hT hn hx hj]; simp

/-- The Courant–Fischer half we need: any subspace of dimension `≥ m - i` contains a nonzero
vector on which the Rayleigh quotient of `T` is `≥` the `i`-th eigenvalue. -/
private lemma EigenWeyl.exists_ge_rayleigh_of_finrank_ge {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {W : Submodule ℂ E}
    (hW : m - i.1 ≤ Module.finrank ℂ W) :
    ∃ x ∈ W, x ≠ 0 ∧ hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  classical
  have hUfr : Module.finrank ℂ
      (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))) = i.1 + 1 := by
    rw [EigenWeyl.finrank_span_eigenvectorBasis hT hn (Finset.Iic i), Fin.card_Iic]
  have him : i.1 < m := i.2
  have hcard : m - i.1 + (i.1 + 1) = m + 1 := by omega
  have hne : W ⊓ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))
      ≠ ⊥ := by
    intro hbot
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq W
      (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m))))
    rw [hbot, finrank_bot, add_zero] at hfin
    have hsup_le : Module.finrank ℂ
        (↥(W ⊔ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))))
        ≤ Module.finrank ℂ E := Submodule.finrank_le _
    rw [hn] at hsup_le
    omega
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxW : x ∈ W := (Submodule.mem_inf.mp hxmem).1
  have hxU : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m))) :=
    (Submodule.mem_inf.mp hxmem).2
  exact ⟨x, hxW, hx0, EigenWeyl.rayleigh_ge_of_mem_Iic hT hn i hxU⟩

end Abstract

/-! ### Specialization to Hermitian matrices -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric linear map underlying a Hermitian matrix. -/
private theorem EigenWeyl.sym {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr hA

/-- `eigenvalues₀` is literally the abstract `LinearMap.IsSymmetric.eigenvalues` of
`toEuclideanLin A`; this is the bridge between the abstract inequalities above and Mathlib's
`Matrix.IsHermitian.eigenvalues₀`. -/
private lemma EigenWeyl.eigenvalues₀_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ = (EigenWeyl.sym hA).eigenvalues finrank_euclideanSpace := rfl

/-- The operator norm bounds the norm of `toEuclideanLin C` applied to a unit-normalized
vector. -/
private lemma EigenWeyl.norm_toEuclideanLin_apply_le (C : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) : ‖Matrix.toEuclideanLin C x‖ ≤ ‖C‖ * ‖x‖ := by
  have hx : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C) x = Matrix.toEuclideanLin C x := by
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) x = Matrix.toEuclideanLin C x
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C).le_opNorm x
  rw [hx, Matrix.l2_opNorm_toEuclideanCLM] at h
  exact h

/-- One side of Weyl's inequality: `λ_i(A) ≤ λ_i(B) + ‖A - B‖`. -/
private lemma EigenWeyl.eigenvalues₀_le_add_opNorm {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ := by
  classical
  have hWdim : Fintype.card n - i.1 ≤ Module.finrank ℂ
      (Submodule.span ℂ (((EigenWeyl.sym hB).eigenvectorBasis finrank_euclideanSpace) ''
        (Finset.Ici i : Set (Fin (Fintype.card n))))) := by
    rw [EigenWeyl.finrank_span_eigenvectorBasis (EigenWeyl.sym hB) finrank_euclideanSpace
      (Finset.Ici i), Fin.card_Ici]
  obtain ⟨x, hxW, hx0, hxrayleigh⟩ :=
    EigenWeyl.exists_ge_rayleigh_of_finrank_ge (EigenWeyl.sym hA) finrank_euclideanSpace i hWdim
  have hBle := EigenWeyl.rayleigh_le_of_mem_Ici (EigenWeyl.sym hB) finrank_euclideanSpace i hxW
  have hsplit : (inner ℂ (Matrix.toEuclideanLin A x) x : ℂ) =
      inner ℂ (Matrix.toEuclideanLin B x) x
        + inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x := by
    have hEq : Matrix.toEuclideanLin A x
        = Matrix.toEuclideanLin B x + (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) := by
      abel
    nth_rewrite 1 [hEq]
    rw [inner_add_left]
  have hCterm : RCLike.re
      (inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x)
      ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
    have hAB : Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x
        = Matrix.toEuclideanLin (A - B) x := by
      rw [map_sub, LinearMap.sub_apply]
    calc RCLike.re (inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x)
        ≤ ‖(inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x : ℂ)‖ :=
          RCLike.re_le_norm _
      _ = ‖(inner ℂ (Matrix.toEuclideanLin (A - B) x) x : ℂ)‖ := by rw [hAB]
      _ ≤ ‖Matrix.toEuclideanLin (A - B) x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖A - B‖ * ‖x‖) * ‖x‖ := by
          gcongr
          exact EigenWeyl.norm_toEuclideanLin_apply_le (A - B) x
      _ = ‖A - B‖ * ‖x‖ ^ 2 := by ring
  have hCbound : RCLike.re (inner ℂ (Matrix.toEuclideanLin A x) x)
      ≤ RCLike.re (inner ℂ (Matrix.toEuclideanLin B x) x) + ‖A - B‖ * ‖x‖ ^ 2 := by
    rw [hsplit, map_add]
    linarith [hCterm]
  have hxpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have hchain : (EigenWeyl.sym hA).eigenvalues finrank_euclideanSpace i * ‖x‖ ^ 2 ≤
      ((EigenWeyl.sym hB).eigenvalues finrank_euclideanSpace i + ‖A - B‖) * ‖x‖ ^ 2 := by
    rw [add_mul]
    linarith [hxrayleigh, hBle, hCbound]
  rw [EigenWeyl.eigenvalues₀_eq hA, EigenWeyl.eigenvalues₀_eq hB]
  exact le_of_mul_le_mul_right hchain hxpos

/-- **Weyl's perturbation inequality** for `Matrix.IsHermitian.eigenvalues₀`, together with the
Frobenius-norm bound on the operator norm (`EigenMeasurable.opNorm_sq_le_frob`). -/
theorem eigenvalues₀_abs_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) := by
  have h1 : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ :=
    EigenWeyl.eigenvalues₀_le_add_opNorm hA hB i
  have h2 : hB.eigenvalues₀ i ≤ hA.eigenvalues₀ i + ‖B - A‖ :=
    EigenWeyl.eigenvalues₀_le_add_opNorm hB hA i
  have hnormBA : ‖B - A‖ = ‖A - B‖ := by rw [← neg_sub]; exact norm_neg _
  rw [hnormBA] at h2
  have habs : |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hfrob : ‖A - B‖ ^ 2 ≤ ∑ a, ∑ b, ‖(A - B) a b‖ ^ 2 :=
    EigenMeasurable.opNorm_sq_le_frob (A - B)
  have hle : ‖A - B‖ ≤ Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) :=
    Real.le_sqrt_of_sq_le hfrob
  calc |hA.eigenvalues₀ i - hB.eigenvalues₀ i|
      ≤ ‖A - B‖ := habs
    _ ≤ Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) := hle

end Matrices

end EigenWeyl

section EigenMeasurable

open MeasureTheory Filter Matrix Polynomial Topology
open scoped ComplexConjugate
open RBM.Endpoints

/-! ### Measurability of the eigenvalue functions -/

section Measurability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian matrices form a closed (hence measurable) subset of `Matrix n n ℂ`, for any
index type `n` (generalizing `Gauss/GridGoodSet.lean`'s `measurableSet_isHermitian`, which is
specific to one concrete index type). File-stem-prefixed helper. -/
private theorem EigenMeasurable.measurableSet_isHermitian :
    MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} := by
  have hcont : Continuous (fun A : Matrix n n ℂ => Aᴴ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.conjTranspose_apply]
    exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
  have heq : {A : Matrix n n ℂ | A.IsHermitian} = {A | Aᴴ = A} := rfl
  rw [heq]
  exact (isClosed_eq hcont continuous_id).measurableSet

/-- Continuity of `A.eigenvalues₀ i` on the Hermitian subtype (subspace topology), via the Weyl
bound `eigenvalues₀_abs_sub_le`. File-stem-prefixed helper. -/
private theorem EigenMeasurable.continuous_eigenvalues₀_subtype (i : Fin (Fintype.card n)) :
    Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues₀ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ i)
    (𝓝 x) (𝓝 (x.2.eigenvalues₀ i))
  rw [tendsto_iff_dist_tendsto_zero]
  have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
  have hcont : Continuous (fun A : Matrix n n ℂ =>
      Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
    Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun b _ =>
        (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
  have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
      (𝓝 x.1) (𝓝 0) := by
    have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
    have := hcont.continuousAt (x := x.1)
    rwa [ContinuousAt, hval] at this
  have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
      Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
    h0.comp (continuous_subtype_val.continuousAt (x := x))
  refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
  rw [Real.dist_eq]
  exact eigenvalues₀_abs_sub_le y.2 x.2 i

/-- Measurability of `A.eigenvalues₀ i` on the Hermitian subtype. -/
private theorem EigenMeasurable.measurable_eigenvalues₀_subtype (i : Fin (Fintype.card n)) :
    Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues₀ i) :=
  (EigenMeasurable.continuous_eigenvalues₀_subtype i).measurable

/-- Measurability of `A.eigenvalues i` on the Hermitian subtype, `n`-indexed. -/
private theorem EigenMeasurable.measurable_eigenvalues_subtype (i : n) :
    Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) := by
  have := EigenMeasurable.measurable_eigenvalues₀_subtype
    (n := n) ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)
  simpa [Matrix.IsHermitian.eigenvalues] using this

/-- **Measurability of the correlation-sum integrand**, for a measurable and
everywhere-Hermitian matrix-valued map. -/
theorem measurable_corrSum {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*} [Fintype n]
    [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : Continuous O)
    (c E : ℝ) :
    Measurable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) := by
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have heig : ∀ i : n, Measurable (fun ω => (hH ω).eigenvalues i) := by
    intro i
    have h : Measurable ((fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) ∘
        (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian}))) :=
      (EigenMeasurable.measurable_eigenvalues_subtype i).comp hφ
    exact h
  have heigPi : Measurable (fun ω i => (hH ω).eigenvalues i) := measurable_pi_iff.mpr heig
  refine Finset.measurable_sum _ (fun f _ => ?_)
  refine hO.measurable.comp ?_
  refine measurable_pi_iff.mpr (fun j => ?_)
  have h1 : Measurable (fun ω => (hH ω).eigenvalues (f j)) := (measurable_pi_apply (f j)).comp heigPi
  have h2 : Measurable (fun ω => (hH ω).eigenvalues (f j) - E) := h1.sub_const E
  exact h2.const_mul c

end Measurability

/-! ### Global extension of the correlation sum (for the law congruence) -/

section CongrLaw

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The correlation-sum function, extended to all of `Matrix n n ℂ` by the junk value `0` off
the Hermitian locus (needed to push the integral through `Measure.map`). File-stem-prefixed
helper. -/
private noncomputable def EigenMeasurable.corrSumVal (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ)
    (A : Matrix n n ℂ) : ℝ :=
  if hA : A.IsHermitian then
    ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (hA.eigenvalues (f j) - E))
  else 0

private theorem EigenMeasurable.measurable_corrSumVal (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) (E : ℝ) :
    Measurable (EigenMeasurable.corrSumVal (n := n) k O E) := by
  have hf : Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (x.2.eigenvalues (f j) - E))) :=
    measurable_corrSum measurable_subtype_coe (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2)
      k hO (Fintype.card n : ℝ) E
  have hg : Measurable (fun _ : {A : Matrix n n ℂ // ¬ A.IsHermitian} => (0 : ℝ)) :=
    measurable_const
  have hdite := Measurable.dite (s := {A : Matrix n n ℂ | A.IsHermitian}) hf hg
    EigenMeasurable.measurableSet_isHermitian
  have heq : EigenMeasurable.corrSumVal (n := n) k O E = fun A =>
      if hA : A ∈ {A : Matrix n n ℂ | A.IsHermitian} then
        ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (hA.eigenvalues (f j) - E))
      else 0 := rfl
  rw [heq]
  exact hdite

end CongrLaw

/-! ### Measurability and law congruence of the `k`-point functional -/

section KPoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `kPoint` of the spectrum, extended by `0` off the Hermitian matrices. -/
private def EigenMeasurable.kPointVal (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ)
    (A : Matrix ι ι ℂ) : ℝ :=
  if hA : A.IsHermitian then kPoint k O E hA.eigenvalues else 0

private theorem EigenMeasurable.kPointVal_eq (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ)
    (A : Matrix ι ι ℂ) :
    EigenMeasurable.kPointVal k O E A =
      ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
        EigenMeasurable.corrSumVal k O E A := by
  unfold EigenMeasurable.kPointVal EigenMeasurable.corrSumVal kPoint
  split_ifs <;> simp

private theorem EigenMeasurable.measurable_kPointVal (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) (E : ℝ) :
    Measurable (EigenMeasurable.kPointVal (ι := ι) k O E) := by
  have h : EigenMeasurable.kPointVal (ι := ι) k O E = fun A =>
      ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
        EigenMeasurable.corrSumVal k O E A := funext (EigenMeasurable.kPointVal_eq k O E)
  rw [h]
  exact (EigenMeasurable.measurable_corrSumVal k hO E).const_mul _

private theorem EigenMeasurable.kPointVal_apply {Ω : Type*} {H : Ω → Matrix ι ι ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) (ω : Ω) :
    EigenMeasurable.kPointVal k O E (H ω) = kPoint k O E (hH ω).eigenvalues := by
  simp only [EigenMeasurable.kPointVal, dif_pos (hH ω)]

/-- **Measurability of the `k`-point functional** of the spectrum of a
measurable, everywhere Hermitian matrix-valued map. -/
theorem measurable_kPoint_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (H : Ω → Matrix ι ι ℂ) (hH : ∀ ω, (H ω).IsHermitian)
    (hmeas : Measurable H) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (E : ℝ) :
    Measurable (fun ω => kPoint k O E (hH ω).eigenvalues) := by
  have h : (fun ω => kPoint k O E (hH ω).eigenvalues) =
      EigenMeasurable.kPointVal k O E ∘ H :=
    funext fun ω => (EigenMeasurable.kPointVal_apply hH k O E ω).symm
  rw [h]
  exact (EigenMeasurable.measurable_kPointVal k hO E).comp hmeas

/-- **Equal laws**: equal laws of two measurable Hermitian-valued maps give equal expected
`k`-point functionals of the spectrum. -/
theorem integral_kPoint_eq_of_map_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁)
    (P₂ : Measure Ω₂) (H₁ : Ω₁ → Matrix ι ι ℂ) (H₂ : Ω₂ → Matrix ι ι ℂ)
    (hH₁ : ∀ ω, (H₁ ω).IsHermitian) (hH₂ : ∀ ω, (H₂ ω).IsHermitian)
    (hmeas₁ : Measurable H₁) (hmeas₂ : Measurable H₂) (hlaw : P₁.map H₁ = P₂.map H₂)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (E : ℝ) :
    ∫ ω, kPoint k O E (hH₁ ω).eigenvalues ∂P₁ = ∫ ω, kPoint k O E (hH₂ ω).eigenvalues ∂P₂ := by
  have hmeas : Measurable (EigenMeasurable.kPointVal (ι := ι) k O E) :=
    EigenMeasurable.measurable_kPointVal k hO E
  have h1 : ∫ ω, kPoint k O E (hH₁ ω).eigenvalues ∂P₁ =
      ∫ A, EigenMeasurable.kPointVal k O E A ∂(P₁.map H₁) := by
    rw [MeasureTheory.integral_map hmeas₁.aemeasurable hmeas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun ω => (EigenMeasurable.kPointVal_apply hH₁ k O E ω).symm))
  have h2 : ∫ ω, kPoint k O E (hH₂ ω).eigenvalues ∂P₂ =
      ∫ A, EigenMeasurable.kPointVal k O E A ∂(P₂.map H₂) := by
    rw [MeasureTheory.integral_map hmeas₂.aemeasurable hmeas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun ω => (EigenMeasurable.kPointVal_apply hH₂ k O E ω).symm))
  rw [h1, h2, hlaw]

end KPoint

end EigenMeasurable

end RBM.Univ
