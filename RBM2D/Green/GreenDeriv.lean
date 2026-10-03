/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSum
import RBM2D.Green.LDEQuad
import RBM2D.Gauss.GreenTimeCont
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The resolvent as a differentiable function of the Gaussian coordinates

The coordinate calculus (`crd`, `Bmat`, `Xmat_eq_sum`, `finDep_of_Hflow`, `hermCLM`), the
differentiability of the resolvent in the coordinates (`resH`, `hasFDerivAt_resH`) and
`continuous_green_comp`, for the two-dimensional model of `RBM2D/Gauss/Model.lean`; the
argument parallels the one-dimensional formalization.

## The model

* The coordinates are the one-size coordinates `(i, j, b) : Coord L W` on the lattice
  `Idx L W = Z2 (W * L)`, and on the common sample space the sequence coordinates
  `⟨n, c⟩ : Sizes.SeqCoord d` (`crd d n c`).
* The used coordinates are `RBM.Gauss.usedCoords L W` (with the abstract injective key
  `idxKey L W`).
* The flow `Hflow` on the common space is `Sizes.seqHflow d n u`; `FinDep` is
  `RBM.Green.FinDep` over `Sizes.SeqΩ d`.
* `continuous_green_comp` is stated over a generic finite index type and proved by
  `RBM.Gauss.continuous_green_of_isHermitian`.

The paper (arXiv:2503.07606) differentiates in the complex entries `H_ij`, `H̄_ij`
(Section 7, `∂_{H_ij} G_xy = -G_xi G_jy`).  Here the resolvent is
differentiated along the independent real coordinates, with fixed Hermitian directions `Bmat`;
the dictionary is `∂_{H_ij} = ½ (∂_{(i,j,T)} - i ∂_{(i,j,F)})` for `idxKey i < idxKey j`.
-/

namespace RBM.Green

open Matrix RBM.Gauss
open scoped Matrix.Norms.L2Operator

/-! ### Coordinate enumeration -/

/-- The coordinate of the common sample space attached to a coordinate `c` at size `n`. -/
abbrev crd (d : Sizes) (n : ℕ) (c : Coord (d.L n) (d.W n)) : Sizes.SeqCoord d := ⟨n, c⟩

/-! ### The coordinate directions -/

section Directions

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The Hermitian matrix direction attached to the coordinate `(i, j, b)`:
`E_ij + E_ji` for the real tag `b = true` and `I·E_ij - I·E_ji` for the imaginary tag
`b = false`; on the diagonal `i = j` the real tag gives `E_ii`. -/
noncomputable def Bmat (i j : Idx L W) (b : Bool) : Matrix (Idx L W) (Idx L W) ℂ :=
  Matrix.of fun k l =>
    if k = i ∧ l = j then (if b then 1 else Complex.I)
    else if k = j ∧ l = i then (if b then 1 else -Complex.I)
    else 0

omit [NeZero L] [NeZero W] in
theorem GreenDeriv_Bmat_apply (i j : Idx L W) (b : Bool) (k l : Idx L W) :
    Bmat L W i j b k l =
      if k = i ∧ l = j then (if b then 1 else Complex.I)
      else if k = j ∧ l = i then (if b then 1 else -Complex.I)
      else 0 := rfl

variable {L W} in
theorem GreenDeriv_mem_usedCoords {c : Coord L W} :
    c ∈ usedCoords L W ↔
      idxKey L W c.1 < idxKey L W c.2.1 ∨ (c.1 = c.2.1 ∧ c.2.2 = true) := by
  simp [usedCoords]

/-- **The coordinate decomposition of `X`.**  `X` is the `ℝ`-linear combination of the fixed
Hermitian directions `Bmat` with the used Gaussian coordinates as coefficients. -/
theorem Xmat_eq_sum (ω : Ω L W) :
    Xmat L W ω = ∑ c ∈ usedCoords L W, ω c • Bmat L W c.1 c.2.1 c.2.2 := by
  ext k l
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Complex.real_smul]
  rcases idxKey_lt_or_eq_or_lt L W k l with h | h | h
  · -- `idxKey k < idxKey l`
    have hkl : k ≠ l := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(k, l, true), (k, l, false)} : Finset (Coord L W)) ⊆ usedCoords L W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact GreenDeriv_mem_usedCoords.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · change Xentry L W ω k l = _
      rw [Xentry, ite_eq_left h]
      simp [GreenDeriv_Bmat_apply]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      simp [GreenDeriv_Bmat_apply, hne1, hne2]
  · -- `k = l`
    subst h
    have hsub : ({(k, k, true)} : Finset (Coord L W)) ⊆ usedCoords L W := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact GreenDeriv_mem_usedCoords.2 (Or.inr ⟨rfl, rfl⟩)
    rw [← Finset.sum_subset hsub, Finset.sum_singleton]
    · change Xentry L W ω k k = _
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
      simp [GreenDeriv_Bmat_apply]
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_singleton] at hnx
      have hne : ¬ (k = i ∧ k = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (lt_irrefl _)
        · have hb : b = true := hu.2
          subst hb
          exact hnx rfl
      have hne' : ¬ (k = j ∧ k = i) := fun h' => hne ⟨h'.2, h'.1⟩
      rw [GreenDeriv_Bmat_apply, ite_eq_right hne, ite_eq_right hne', mul_zero]
  · -- `idxKey l < idxKey k`
    have hkl : l ≠ k := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(l, k, true), (l, k, false)} : Finset (Coord L W)) ⊆ usedCoords L W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact GreenDeriv_mem_usedCoords.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · change Xentry L W ω k l = _
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h]
      simp [GreenDeriv_Bmat_apply, hkl, Ne.symm hkl]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      simp [GreenDeriv_Bmat_apply, hne1, hne2]

variable {L W} in
/-- Every direction attached to a **used** coordinate is Hermitian (the redundant coordinate
`(i, i, false)` is the one exception, and it is never read). -/
theorem GreenDeriv_Bmat_isHermitian {c : Coord L W} (hc : c ∈ usedCoords L W) :
    (Bmat L W c.1 c.2.1 c.2.2).IsHermitian := by
  obtain ⟨i, j, b⟩ := c
  have hij : i ≠ j ∨ b = true := by
    rcases GreenDeriv_mem_usedCoords.1 hc with h | h
    · exact Or.inl fun he => absurd (he ▸ h) (lt_irrefl _)
    · exact Or.inr h.2
  ext k l
  change (starRingEnd ℂ) (Bmat L W i j b l k) = Bmat L W i j b k l
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  rcases hij with hij | hb
  · by_cases hA : k = i ∧ l = j
    · have hB : ¬ (l = i ∧ k = j) := fun hB => hij (by rw [← hA.1]; exact hB.2)
      rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i), ite_eq_left hA]
      cases b <;> simp
    · by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_right hA, ite_eq_left hB]
        cases b <;> simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hA, ite_eq_right hB]
        simp
  · subst hb
    by_cases hA : k = i ∧ l = j
    · rw [ite_eq_left hA]
      by_cases hB : l = i ∧ k = j
      · rw [ite_eq_left hB]; simp
      · rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i)]; simp
    · rw [ite_eq_right hA]
      by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_left hB]; simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hB]
        simp

variable {L W} in
/-- On a used coordinate the direction `coordinateMatrix` is `Bmat`.  (Off the used
coordinates `coordinateMatrix` is `0`, `coordinateMatrix_zero_of_not_mem_usedCoords`.) -/
theorem GreenDeriv_coordinateMatrix_eq_Bmat {c : Coord L W} (hc : c ∈ usedCoords L W) :
    coordinateMatrix L W c = Bmat L W c.1 c.2.1 c.2.2 := by
  classical
  rw [coordinateMatrix, Xmat_eq_sum, Finset.sum_eq_single_of_mem c hc]
  · simp
  · intro c' _ hne
    rw [Pi.single_eq_of_ne hne, zero_smul]

variable {L W} in
/-- **`X` is affine in each used coordinate**, with slope the direction `Bmat`. -/
theorem GreenDeriv_Xmat_update (ω : Ω L W) {c : Coord L W} (hc : c ∈ usedCoords L W)
    (t : ℝ) :
    Xmat L W (Function.update ω c t) = Xmat L W ω + (t - ω c) • Bmat L W c.1 c.2.1 c.2.2 := by
  rw [Xmat_update, GreenDeriv_coordinateMatrix_eq_Bmat hc]

end Directions

/-! ### The sequence model -/

section Sequence

variable (d : Sizes)

/-- The coordinate decomposition of the size-`n` matrix on the common sample space. -/
theorem GreenDeriv_seqXmat_eq_sum (n : ℕ) (ω : Sizes.SeqΩ d) :
    Sizes.seqXmat d n ω =
      ∑ c ∈ usedCoords (d.L n) (d.W n), ω (crd d n c) • Bmat (d.L n) (d.W n) c.1 c.2.1 c.2.2 :=
  Xmat_eq_sum _ _ _

/-- Moving the common-space coordinate `crd d n c` of a used `c` moves `seqXmat d n` along
`Bmat c`. -/
theorem GreenDeriv_seqXmat_update (n : ℕ) (ω : Sizes.SeqΩ d) {c : Coord (d.L n) (d.W n)}
    (hc : c ∈ usedCoords (d.L n) (d.W n)) (t : ℝ) :
    Sizes.seqXmat d n (Function.update ω (crd d n c) t) =
      Sizes.seqXmat d n ω + (t - ω (crd d n c)) • Bmat (d.L n) (d.W n) c.1 c.2.1 c.2.2 := by
  rw [Sizes.seqXmat_update, GreenDeriv_coordinateMatrix_eq_Bmat hc]

/-- The flow on the common space, with the real scalar action. -/
theorem GreenDeriv_seqHflow_eq_realSmul (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d) :
    Sizes.seqHflow d n u ω = Real.sqrt u • Sizes.seqXmat d n ω :=
  Hflow_eq_realSmul _ _ _ _

/-- The flow at size `n` is continuous in the common-space coordinates. -/
theorem GreenDeriv_continuous_seqHflow (n : ℕ) (u : ℝ) :
    Continuous (Sizes.seqHflow d n u) := by
  have hs : Continuous (Sizes.slice d n) :=
    continuous_pi fun c => continuous_apply (crd d n c)
  exact (continuous_Hflow (d.L n) (d.W n) u).comp hs

/-- `seqHflow d n u` reads only the coordinates `crd d n c`, `c ∈ usedCoords`. -/
theorem GreenDeriv_seqHflow_congr_of_agree (n : ℕ) (u : ℝ) (ω ω' : Sizes.SeqΩ d)
    (h : ∀ e ∈ (usedCoords (d.L n) (d.W n)).image (crd d n), ω e = ω' e) :
    Sizes.seqHflow d n u ω = Sizes.seqHflow d n u ω' := by
  rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqHflow_eq_realSmul,
    GreenDeriv_seqXmat_eq_sum, GreenDeriv_seqXmat_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [h (crd d n c) (Finset.mem_image_of_mem _ hc)]

/-- Anything read off `seqHflow d n u` reads only finitely many coordinates. -/
theorem finDep_of_Hflow (n : ℕ) (u : ℝ) {V : Type*}
    (F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → V) :
    FinDep d fun ω => F (Sizes.seqHflow d n u ω) :=
  ⟨(usedCoords (d.L n) (d.W n)).image (crd d n), fun ω ω' h => by
    change F (Sizes.seqHflow d n u ω) = F (Sizes.seqHflow d n u ω')
    rw [GreenDeriv_seqHflow_congr_of_agree d n u ω ω' h]⟩

end Sequence

/-! ### The Hermitian projection and the extended resolvent -/

section HermProj

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `ℝ`-linear projection onto the Hermitian matrices, `M ↦ (M + Mᴴ)/2`, as a continuous
linear map (hence `C^∞`). -/
noncomputable def hermCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

theorem GreenDeriv_hermCLM_apply (M : Matrix n n ℂ) :
    hermCLM n M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

/-- The projection lands in the Hermitian matrices. -/
theorem GreenDeriv_isHermitian_hermCLM (M : Matrix n n ℂ) : (hermCLM n M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

/-- The projection is the identity on Hermitian matrices. -/
theorem GreenDeriv_hermCLM_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermCLM n M = M := by
  rw [GreenDeriv_hermCLM_apply, hM]
  module

/-- **`G_z` pre-composed with the Hermitian projection**: defined on the whole matrix space,
and equal to the Green function at every Hermitian matrix
(`GreenDeriv_resH_of_isHermitian`). -/
noncomputable def resH (z : ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))

theorem GreenDeriv_resH_eq_green (z : ℂ) (M : Matrix n n ℂ) :
    resH z M = green (hermCLM n M) z := by
  change Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))
    = (hermCLM n M - z • (1 : Matrix n n ℂ))⁻¹
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem GreenDeriv_resH_of_isHermitian {z : ℂ} {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    resH z M = green M z := by
  rw [GreenDeriv_resH_eq_green, GreenDeriv_hermCLM_of_isHermitian hM]

theorem GreenDeriv_isUnit_resH_arg {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    IsUnit (hermCLM n M - z • (1 : Matrix n n ℂ)) :=
  RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero (GreenDeriv_isHermitian_hermCLM M) hz

/-- **The real Fréchet derivative of the extended resolvent**:
`D resH_z(M)[A] = -resH_z(M) · herm(A) · resH_z(M)`, for every `M` and `Im z ≠ 0`. -/
theorem hasFDerivAt_resH {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    HasFDerivAt (resH z)
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (resH z M) (resH z M)).comp
        (hermCLM n))) M := by
  obtain ⟨u, hus⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = hermCLM n M - z • (1 : Matrix n n ℂ) :=
    ⟨(GreenDeriv_isUnit_resH_arg hz M).unit, IsUnit.unit_spec _⟩
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = resH z M := by
    rw [resH, ← hus, Ring.inverse_unit]
  have hT : HasFDerivAt (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ))
      (hermCLM n) M := (hermCLM n).hasFDerivAt.sub_const _
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹))
      ((fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) M) := by
    change HasFDerivAt _ _ (hermCLM n M - z • (1 : Matrix n n ℂ))
    rw [← hus]
    exact hasFDerivAt_ringInverse u
  have key := hF.comp M hT
  rw [hinv] at key
  have hcomp : (Ring.inverse (M₀ := Matrix n n ℂ))
      ∘ (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) = resH z := rfl
  rw [hcomp, ContinuousLinearMap.neg_comp] at key
  exact key

/-- The resolvent depends continuously on a continuously varying Hermitian matrix. -/
theorem continuous_green_comp {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f)
    (hherm : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun v => green (f v) z :=
  RBM.Gauss.continuous_green_of_isHermitian hf hherm hz

end HermProj

end RBM.Green
