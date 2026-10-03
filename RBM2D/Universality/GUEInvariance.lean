/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi

/-!
# GUE unitary invariance

The statement is about the coordinate space `Ω L W = Coord L W → ℝ`,
`Coord L W = Idx L W × Idx L W × Bool`, and `gueVar`, `gueP`, `Xmat` (`N = (W L)²`).

## Proof outline

Only the real coordinates `(i, j, b)` with `idxKey i < idxKey j` (both booleans) or `i = j`
(`b = true`) are read by `Xmat L W`; they form the finite slot type `GUESlot L W`.  The real-linear
reconstruction `GUEReconSlot` and its left inverse `GUEExtractSlot` identify `Xmat L W` with
`GUEReconSlot` composed with the restriction of `ω` to the slots.  The key identity
(`GUEMainIdentity`) is `∑ (extr K)² / wt = N · Tr(K²)` for Hermitian `K` (`wt` the slot's Gaussian
variance `gueVar`, `N = (W L)²` the matrix size); its right side is invariant under unitary
conjugation.  Standardizing each slot by `√wt` gives a linear isometry of
`EuclideanSpace ℝ (GUESlot L W)`, to which `ProbabilityTheory.stdGaussian_map` applies; the slot
law of `gueP` is identified with a standardized `stdGaussian` by `map_pi_eq_stdGaussian`,
`Measure.pi_map_pi` and `gaussianReal_map_const_mul`.  The unused coordinates of `Coord L W` (the
pairs with `idxKey j < idxKey i` and `(i, i, false)`) drop out through
`Measure.map_infinitePi_infinitePi_of_inj`.

The invariance is first proved for `Uᴴ * X * U` (`GUE_map_conj`); the main statement
`gueP_map_unitary_conj` is for `U * X * star U`, the instance of `GUE_map_conj` at `star U`.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory WithLp
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped ComplexConjugate NNReal ENNReal

set_option linter.unusedSectionVars false

variable (L W : ℕ) [NeZero L] [NeZero W]

/-! ### The real-coordinate slot type at fixed matrix size `N` -/

/-- Which triples `(i, j, b)` carry a real coordinate read by `Xmat L W`: either
`idxKey i < idxKey j` (either boolean), or `i = j` (only `b = true`). -/
private def GUESlotPred (q : Idx L W × Idx L W × Bool) : Prop :=
  idxKey L W q.1 < idxKey L W q.2.1 ∨ (q.1 = q.2.1 ∧ q.2.2 = true)

private instance instDecidablePredGUESlotPred :
    DecidablePred (GUESlotPred L W) := fun q => by unfold GUESlotPred; infer_instance

/-- The finite index set of real coordinates read by `Xmat L W`. -/
private def GUESlot : Type :=
  {q : Idx L W × Idx L W × Bool // GUESlotPred L W q}

private instance instFintypeGUESlot : Fintype (GUESlot L W) :=
  Subtype.fintype _

/-! ### The Gaussian variance of a slot (total function, matches `gueVar`) -/

private theorem GUE_card_idx :
    Fintype.card (Idx L W) = (W * L) ^ 2 := by
  change Fintype.card (ZMod (W * L) × ZMod (W * L)) = (W * L) ^ 2
  rw [Fintype.card_prod, ZMod.card, sq]

private noncomputable def GUEWt (q : Idx L W × Idx L W × Bool) : ℝ :=
  (gueVar L W q : ℝ)

private theorem GUEWt_diag (i : Idx L W) (b : Bool) :
    GUEWt L W (i, i, b) = 1 / (Fintype.card (Idx L W) : ℝ) := by
  rw [GUE_card_idx]
  unfold GUEWt gueVar
  simp

private theorem GUEWt_offDiag (i j : Idx L W) (b : Bool) (hij : i ≠ j) :
    GUEWt L W (i, j, b) = 1 / (2 * (Fintype.card (Idx L W) : ℝ)) := by
  rw [GUE_card_idx]
  unfold GUEWt gueVar
  simp [hij]

private theorem GUEWt_pos (q : Idx L W × Idx L W × Bool) :
    0 < GUEWt L W q := by
  have hc : (0 : ℝ) < (Fintype.card (Idx L W) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rcases q with ⟨i, j, b⟩
  by_cases h : i = j
  · subst h
    rw [GUEWt_diag]
    positivity
  · rw [GUEWt_offDiag L W i j b h]
    positivity

/-! ### Reconstruction and extraction (total functions on all triples) -/

/-- Rebuild a Hermitian matrix from a total assignment of real values to triples
`(i, j, b)`, using only the values at slots (mirrors `RBM.Gauss.Xentry`). -/
private noncomputable def GUERe (x : Idx L W × Idx L W × Bool → ℝ) :
    Matrix (Idx L W) (Idx L W) ℂ :=
  Matrix.of fun i j =>
    if idxKey L W i < idxKey L W j then
      (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ)
    else if idxKey L W j < idxKey L W i then
      (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ)
    else
      (x (i, i, true) : ℂ)

/-- Extract the real value of a matrix entry at a triple `(i, j, b)` (mirrors the inverse of
`Xentry`; well-behaved only at slots, but total). -/
private noncomputable def GUEEx (K : Matrix (Idx L W) (Idx L W) ℂ) :
    Idx L W × Idx L W × Bool → ℝ :=
  fun q => if q.1 = q.2.1 ∨ q.2.2 = true then (K q.1 q.2.1).re else (K q.1 q.2.1).im

private theorem GUERe_apply_lt (x : Idx L W × Idx L W × Bool → ℝ)
    {i j : Idx L W} (h : idxKey L W i < idxKey L W j) :
    GUERe L W x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, ite_eq_left h]

private theorem GUERe_apply_gt (x : Idx L W × Idx L W × Bool → ℝ)
    {i j : Idx L W} (h : idxKey L W j < idxKey L W i) :
    GUERe L W x i j = (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ) := by
  have hne : ¬ idxKey L W i < idxKey L W j := asymm h
  simp only [GUERe, Matrix.of_apply, ite_eq_right hne, ite_eq_left h]

private theorem GUERe_apply_diag (x : Idx L W × Idx L W × Bool → ℝ)
    (i : Idx L W) :
    GUERe L W x i i = (x (i, i, true) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, ite_eq_right (lt_irrefl (idxKey L W i))]

/-- **Hermitian-ness of `GUERe`**, for any real coordinate assignment. -/
private theorem GUERe_isHermitian (x : Idx L W × Idx L W × Bool → ℝ) :
    (GUERe L W x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · rw [GUERe_apply_lt L W x h, GUERe_apply_gt L W x h, hstar]
    apply Complex.ext <;> simp
  · subst h
    rw [GUERe_apply_diag L W x i, hstar]
    apply Complex.ext <;> simp
  · rw [GUERe_apply_gt L W x h, GUERe_apply_lt L W x h, hstar]
    apply Complex.ext <;> simp

/-- **Extraction after reconstruction recovers a slot's value.** -/
private theorem GUEEx_GUERe (x : Idx L W × Idx L W × Bool → ℝ)
    {q : Idx L W × Idx L W × Bool} (hq : GUESlotPred L W q) :
    GUEEx L W (GUERe L W x) q = x q := by
  rcases q with ⟨i, j, b⟩
  rcases hq with h | ⟨hij, hb⟩
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    have hval : GUERe L W x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) :=
      GUERe_apply_lt L W x h
    cases b
    · have e : GUEEx L W (GUERe L W x) (i, j, false) = (GUERe L W x i j).im := by
        simp [GUEEx, hne]
      rw [e, hval]
      simp
    · have e : GUEEx L W (GUERe L W x) (i, j, true) = (GUERe L W x i j).re := by
        simp [GUEEx]
      rw [e, hval]
      simp
  · dsimp only at hij hb
    subst hij
    subst hb
    have e : GUEEx L W (GUERe L W x) (i, i, true) = (GUERe L W x i i).re := by
      simp [GUEEx]
    rw [e, GUERe_apply_diag L W x i]
    simp

/-- **Reconstruction after extraction recovers a Hermitian matrix.** -/
private theorem GUERe_GUEEx {K : Matrix (Idx L W) (Idx L W) ℂ}
    (hK : K.IsHermitian) : GUERe L W (GUEEx L W K) = K := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_lt L W (GUEEx L W K) h]
    have e1 : GUEEx L W K (i, j, true) = (K i j).re := by simp [GUEEx]
    have e2 : GUEEx L W K (i, j, false) = (K i j).im := by simp [GUEEx, hne]
    rw [e1, e2, mul_comm]
    exact Complex.re_add_im (K i j)
  · subst h
    rw [GUERe_apply_diag L W (GUEEx L W K) i]
    have e : GUEEx L W K (i, i, true) = (K i i).re := by simp [GUEEx]
    rw [e]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    apply Complex.ext
    · simp
    · simp [him]
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_gt L W (GUEEx L W K) h]
    have e1 : GUEEx L W K (j, i, true) = (K j i).re := by simp [GUEEx]
    have e2 : GUEEx L W K (j, i, false) = (K j i).im := by simp [GUEEx, Ne.symm hne]
    rw [e1, e2]
    have hKij : star (K i j) = K j i := hK.apply j i
    have hcong : K i j = star (K j i) := by rw [← hKij, star_star]
    rw [hcong]
    apply Complex.ext <;> simp

/-! ### `GUERe`, `GUEEx` are real-linear -/

private theorem GUERe_add (x y : Idx L W × Idx L W × Bool → ℝ) :
    GUERe L W (x + y) = GUERe L W x + GUERe L W y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · rw [Matrix.add_apply, GUERe_apply_lt L W x h, GUERe_apply_lt L W y h,
      GUERe_apply_lt L W (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  · subst h
    rw [Matrix.add_apply, GUERe_apply_diag L W x i, GUERe_apply_diag L W y i,
      GUERe_apply_diag L W (x + y) i]
    simp only [Pi.add_apply, Complex.ofReal_add]
  · rw [Matrix.add_apply, GUERe_apply_gt L W x h, GUERe_apply_gt L W y h,
      GUERe_apply_gt L W (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

private theorem GUERe_smul (c : ℝ) (x : Idx L W × Idx L W × Bool → ℝ) :
    GUERe L W (c • x) = c • GUERe L W x := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · rw [Matrix.smul_apply, GUERe_apply_lt L W x h, GUERe_apply_lt L W (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  · subst h
    rw [Matrix.smul_apply, GUERe_apply_diag L W x i, GUERe_apply_diag L W (c • x) i]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  · rw [Matrix.smul_apply, GUERe_apply_gt L W x h, GUERe_apply_gt L W (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring

private theorem GUEEx_add (K K' : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEEx L W (K + K') = GUEEx L W K + GUEEx L W K' := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp [hc]
  · simp [hc]

private theorem GUEEx_smul (c : ℝ) (K : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEEx L W (c • K) = c • GUEEx L W K := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp only [hc, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, Pi.smul_apply,
      ite_eq_left]
  · simp only [hc, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, Pi.smul_apply,
      ite_eq_right, not_false_eq_true]

/-! ### The fixed conjugation `H ↦ Uᴴ H U`, and its interaction with `GUERe`/`GUEEx` -/

private noncomputable def GUEConj (U : Matrix (Idx L W) (Idx L W) ℂ)
    (H : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (Idx L W) (Idx L W) ℂ :=
  Uᴴ * H * U

private theorem GUEConj_isHermitian (U : Matrix (Idx L W) (Idx L W) ℂ)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) :
    (GUEConj L W U H).IsHermitian := by
  change (Uᴴ * H * U)ᴴ = Uᴴ * H * U
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
    Matrix.mul_assoc]

private theorem GUEConj_add (U : Matrix (Idx L W) (Idx L W) ℂ)
    (H1 H2 : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEConj L W U (H1 + H2) = GUEConj L W U H1 + GUEConj L W U H2 := by
  change Uᴴ * (H1 + H2) * U = Uᴴ * H1 * U + Uᴴ * H2 * U
  rw [Matrix.mul_add, Matrix.add_mul]

private theorem GUEConj_smul (U : Matrix (Idx L W) (Idx L W) ℂ) (c : ℝ)
    (H : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEConj L W U (c • H) = c • GUEConj L W U H := by
  change Uᴴ * (c • H) * U = c • (Uᴴ * H * U)
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `Uᴴ * (Uᴴ H U) * U`-type cancellation: conjugating by `U` then by `Uᴴ` is the identity, for
any unitary `U`. -/
private theorem GUEConj_conj_left {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (H : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEConj L W Uᴴ (GUEConj L W U H) = H := by
  change Uᴴᴴ * (Uᴴ * H * U) * Uᴴ = H
  rw [Matrix.conjTranspose_conjTranspose]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc U * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc U Uᴴ H, ← Matrix.mul_assoc U,
          Matrix.mul_assoc]
    _ = H := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem GUEConj_conj_right {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (H : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEConj L W U (GUEConj L W Uᴴ H) = H := by
  have hU' : Uᴴ ∈ Matrix.unitaryGroup (Idx L W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have := GUEConj_conj_left L W hU' H
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-! ### The algebraic core: `∑ (extraction)²/(variance) = M · Tr(K²)` and unitary invariance -/

private theorem GUE_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, Complex.add_re, ih]

private theorem GUE_normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.normSq_conj]

/-- **Step 1 of the main identity**: `Tr(K²).re` as a double sum of `normSq`, using only that
`K` is Hermitian. -/
private theorem GUE_trace_sq_re {K : Matrix (Idx L W) (Idx L W) ℂ}
    (hK : K.IsHermitian) :
    (Matrix.trace (K * K)).re = ∑ i, ∑ j, Complex.normSq (K i j) := by
  have htr : Matrix.trace (K * K) = ∑ i, ∑ j, K i j * K j i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htr, GUE_re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [GUE_re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hji : K j i = star (K i j) := (hK.apply j i).symm
  have heq : K i j * K j i = ((Complex.normSq (K i j) : ℝ) : ℂ) := by
    rw [hji, show star (K i j) = (starRingEnd ℂ) (K i j) from rfl, Complex.mul_conj]
  rw [heq]
  simp

/-- **Step 2 of the main identity**: the sum of the two boolean slots at a fixed `(i, j)`. -/
private theorem GUE_bool_sum {K : Matrix (Idx L W) (Idx L W) ℂ}
    (hK : K.IsHermitian) (i j : Idx L W) :
    (∑ b : Bool, if GUESlotPred L W (i, j, b) then
        (GUEEx L W K (i, j, b)) ^ 2 / GUEWt L W (i, j, b) else 0) =
      if i = j then (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j)
      else if idxKey L W i < idxKey L W j then
        2 * (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j)
      else 0 := by
  rw [Fintype.sum_bool]
  by_cases hij : i = j
  · subst hij
    have hSPt : GUESlotPred L W (i, i, true) := Or.inr ⟨rfl, rfl⟩
    have hSPf : ¬ GUESlotPred L W (i, i, false) := by
      simp [GUESlotPred]
    rw [ite_eq_left rfl, ite_eq_left hSPt, ite_eq_right hSPf]
    have e : GUEEx L W K (i, i, true) = (K i i).re := by simp [GUEEx]
    have hw : GUEWt L W (i, i, true) = 1 / (Fintype.card (Idx L W) : ℝ) :=
      GUEWt_diag L W i true
    rw [e, add_zero, hw]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    rw [Complex.normSq_apply, him]
    field_simp
    ring
  · rw [ite_eq_right hij]
    by_cases hlt : idxKey L W i < idxKey L W j
    · have hSPt : GUESlotPred L W (i, j, true) := Or.inl hlt
      have hSPf : GUESlotPred L W (i, j, false) := Or.inl hlt
      rw [ite_eq_left hlt, ite_eq_left hSPt, ite_eq_left hSPf]
      have e1 : GUEEx L W K (i, j, true) = (K i j).re := by simp [GUEEx]
      have e2 : GUEEx L W K (i, j, false) = (K i j).im := by simp [GUEEx, hij]
      have hw1 : GUEWt L W (i, j, true) = 1 / (2 * (Fintype.card (Idx L W) : ℝ)) :=
        GUEWt_offDiag L W i j true hij
      have hw2 : GUEWt L W (i, j, false) = 1 / (2 * (Fintype.card (Idx L W) : ℝ)) :=
        GUEWt_offDiag L W i j false hij
      rw [e1, e2, hw1, hw2, Complex.normSq_apply]
      field_simp
    · have hSPt : ¬ GUESlotPred L W (i, j, true) := by
        simp [GUESlotPred, hlt, hij]
      have hSPf : ¬ GUESlotPred L W (i, j, false) := by
        simp [GUESlotPred, hlt, hij]
      rw [ite_eq_right hlt, ite_eq_right hSPt, ite_eq_right hSPf]
      ring

/-- **Step 3 of the main identity**: the off-diagonal contribution is symmetric under swapping
`i` and `j` (uses `K`'s Hermitian symmetry). -/
private theorem GUE_swap_sum {K : Matrix (Idx L W) (Idx L W) ℂ}
    (hK : K.IsHermitian) (c : ℝ) :
    ∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W j < idxKey L W i then c * Complex.normSq (K i j) else 0) =
      ∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W i < idxKey L W j then c * Complex.normSq (K i j) else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hab : idxKey L W a < idxKey L W b
  · rw [ite_eq_left hab, ite_eq_left hab]
    have hsymm : Complex.normSq (K b a) = Complex.normSq (K a b) := by
      have hba : K b a = star (K a b) := (hK.apply b a).symm
      rw [hba, GUE_normSq_star]
    rw [hsymm]
  · rw [ite_eq_right hab, ite_eq_right hab]

/-- **Main identity**: the weighted sum of squared slot values equals `M · Tr(K²).re`, for
Hermitian `K`. -/
private theorem GUEMainIdentity {K : Matrix (Idx L W) (Idx L W) ℂ}
    (hK : K.IsHermitian) :
    ∑ q : GUESlot L W, (GUEEx L W K q.1) ^ 2 / GUEWt L W q.1 =
      (Fintype.card (Idx L W) : ℝ) * (Matrix.trace (K * K)).re := by
  have hconv : (∑ q ∈ (Finset.univ : Finset (Idx L W × Idx L W × Bool)).filter (GUESlotPred L W),
      (GUEEx L W K q) ^ 2 / GUEWt L W q) =
      ∑ q : GUESlot L W, (GUEEx L W K q.1) ^ 2 / GUEWt L W q.1 :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [← hconv, Finset.sum_filter]
  have hsplit : (∑ q : Idx L W × Idx L W × Bool,
      if GUESlotPred L W q then (GUEEx L W K q) ^ 2 / GUEWt L W q else 0) =
      ∑ i : Idx L W, ∑ j : Idx L W, ∑ b : Bool,
        if GUESlotPred L W (i, j, b) then (GUEEx L W K (i, j, b)) ^ 2 / GUEWt L W (i, j, b)
        else 0 := by
    rw [Fintype.sum_prod_type (α₁ := Idx L W) (α₂ := Idx L W × Bool)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Fintype.sum_prod_type (α₁ := Idx L W) (α₂ := Bool)
      (f := fun y => if GUESlotPred L W (i, y) then
        (GUEEx L W K (i, y)) ^ 2 / GUEWt L W (i, y) else 0)
  rw [hsplit]
  simp_rw [GUE_bool_sum L W hK]
  rw [GUE_trace_sq_re L W hK]
  have hsep : ∀ i j : Idx L W,
      (if i = j then (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j)
        else if idxKey L W i < idxKey L W j then
          2 * (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j) else 0) =
      (if i = j then (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j) else 0) +
        (if idxKey L W i < idxKey L W j then
          2 * (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j) else 0) := by
    intro i j
    by_cases hij : i = j
    · have hnlt : ¬ idxKey L W i < idxKey L W j := by rw [hij]; exact lt_irrefl _
      rw [ite_eq_left hij, ite_eq_left hij, ite_eq_right hnlt, add_zero]
    · rw [ite_eq_right hij, ite_eq_right hij, zero_add]
  simp_rw [hsep, Finset.sum_add_distrib]
  have hA : ∑ i : Idx L W, ∑ j : Idx L W,
      (if i = j then (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j) else 0) =
      (Fintype.card (Idx L W) : ℝ) * ∑ i : Idx L W, Complex.normSq (K i i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hB : ∑ i : Idx L W, ∑ j : Idx L W,
      (if idxKey L W i < idxKey L W j then
        2 * (Fintype.card (Idx L W) : ℝ) * Complex.normSq (K i j) else 0) =
      2 * (Fintype.card (Idx L W) : ℝ) * ∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W i < idxKey L W j then Complex.normSq (K i j) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [hA, hB]
  have hC : ∑ i : Idx L W, ∑ j : Idx L W, Complex.normSq (K i j) =
      (∑ i : Idx L W, Complex.normSq (K i i)) +
      2 * (∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W i < idxKey L W j then Complex.normSq (K i j) else 0)) := by
    have hdecomp : ∀ i j : Idx L W, Complex.normSq (K i j) =
        (if i = j then Complex.normSq (K i j) else 0) +
        ((if idxKey L W i < idxKey L W j then Complex.normSq (K i j) else 0) +
          (if idxKey L W j < idxKey L W i then Complex.normSq (K i j) else 0)) := by
      intro i j
      rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
      · rw [ite_eq_right (fun he : i = j => absurd h (he ▸ lt_irrefl _)), ite_eq_left h,
          ite_eq_right (asymm h)]
        ring
      · subst h
        rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _)]
        ring
      · rw [ite_eq_right (fun he : i = j => absurd h (he ▸ lt_irrefl _)), ite_eq_right (asymm h),
          ite_eq_left h]
        ring
    rw [show (∑ i : Idx L W, ∑ j : Idx L W, Complex.normSq (K i j)) =
        ∑ i : Idx L W, ∑ j : Idx L W, ((if i = j then Complex.normSq (K i j) else 0) +
          ((if idxKey L W i < idxKey L W j then Complex.normSq (K i j) else 0) +
            (if idxKey L W j < idxKey L W i then Complex.normSq (K i j) else 0))) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hdecomp i j))]
    simp_rw [Finset.sum_add_distrib]
    have hdiagsum : (∑ i : Idx L W, ∑ j : Idx L W,
        (if i = j then Complex.normSq (K i j) else 0)) =
        ∑ i : Idx L W, Complex.normSq (K i i) :=
      Finset.sum_congr rfl (fun i _ => by simp)
    have hswap1 : (∑ i : Idx L W, ∑ j : Idx L W,
        (if idxKey L W j < idxKey L W i then Complex.normSq (K i j) else 0)) =
        ∑ i : Idx L W, ∑ j : Idx L W,
          (if idxKey L W i < idxKey L W j then Complex.normSq (K i j) else 0) := by
      simpa using GUE_swap_sum L W hK 1
    rw [hdiagsum, hswap1]
    ring
  rw [hC]
  ring

/-! ### The subtype-indexed reconstruction/extraction, and the conjugation action on slots -/

private noncomputable def GUEExtend (x : GUESlot L W → ℝ) :
    Idx L W × Idx L W × Bool → ℝ :=
  fun q => if h : GUESlotPred L W q then x ⟨q, h⟩ else 0

private theorem GUEExtend_add (x y : GUESlot L W → ℝ) :
    GUEExtend L W (x + y) = GUEExtend L W x + GUEExtend L W y := by
  funext q
  change GUEExtend L W (x + y) q = GUEExtend L W x q + GUEExtend L W y q
  unfold GUEExtend
  by_cases h : GUESlotPred L W q
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h, add_zero]

private theorem GUEExtend_smul (c : ℝ) (x : GUESlot L W → ℝ) :
    GUEExtend L W (c • x) = c • GUEExtend L W x := by
  funext q
  change GUEExtend L W (c • x) q = c • GUEExtend L W x q
  unfold GUEExtend
  by_cases h : GUESlotPred L W q
  · rw [dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, smul_zero]

private noncomputable def GUEReconSlot (x : GUESlot L W → ℝ) :
    Matrix (Idx L W) (Idx L W) ℂ :=
  GUERe L W (GUEExtend L W x)

private noncomputable def GUEExtractSlot (K : Matrix (Idx L W) (Idx L W) ℂ) :
    GUESlot L W → ℝ :=
  fun p => GUEEx L W K p.1

private theorem GUEReconSlot_add (x y : GUESlot L W → ℝ) :
    GUEReconSlot L W (x + y) = GUEReconSlot L W x + GUEReconSlot L W y := by
  unfold GUEReconSlot
  rw [GUEExtend_add, GUERe_add]

private theorem GUEReconSlot_smul (c : ℝ) (x : GUESlot L W → ℝ) :
    GUEReconSlot L W (c • x) = c • GUEReconSlot L W x := by
  unfold GUEReconSlot
  rw [GUEExtend_smul, GUERe_smul]

private theorem GUEReconSlot_isHermitian (x : GUESlot L W → ℝ) :
    (GUEReconSlot L W x).IsHermitian :=
  GUERe_isHermitian L W (GUEExtend L W x)

private theorem GUEExtractSlot_add (K K' : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEExtractSlot L W (K + K') = GUEExtractSlot L W K + GUEExtractSlot L W K' := by
  funext p
  exact congrFun (GUEEx_add L W K K') p.1

private theorem GUEExtractSlot_smul (c : ℝ)
    (K : Matrix (Idx L W) (Idx L W) ℂ) :
    GUEExtractSlot L W (c • K) = c • GUEExtractSlot L W K := by
  funext p
  exact congrFun (GUEEx_smul L W c K) p.1

private theorem GUEExtractSlot_GUEReconSlot (x : GUESlot L W → ℝ) :
    GUEExtractSlot L W (GUEReconSlot L W x) = x := by
  funext p
  change GUEEx L W (GUERe L W (GUEExtend L W x)) p.1 = x p
  rw [GUEEx_GUERe L W (GUEExtend L W x) p.2]
  unfold GUEExtend
  rw [dite_eq_left p.2]
  rfl

private theorem GUERe_congr_slots {x y : Idx L W × Idx L W × Bool → ℝ}
    (h : ∀ q, GUESlotPred L W q → x q = y q) : GUERe L W x = GUERe L W y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt L W i j with hlt | heq | hgt
  · rw [GUERe_apply_lt L W x hlt, GUERe_apply_lt L W y hlt, h _ (Or.inl hlt), h _ (Or.inl hlt)]
  · subst heq
    rw [GUERe_apply_diag L W x i, GUERe_apply_diag L W y i, h _ (Or.inr ⟨rfl, rfl⟩)]
  · rw [GUERe_apply_gt L W x hgt, GUERe_apply_gt L W y hgt, h _ (Or.inl hgt), h _ (Or.inl hgt)]

private theorem GUEReconSlot_GUEExtractSlot
    {K : Matrix (Idx L W) (Idx L W) ℂ} (hK : K.IsHermitian) :
    GUEReconSlot L W (GUEExtractSlot L W K) = K := by
  change GUERe L W (GUEExtend L W (GUEExtractSlot L W K)) = K
  rw [GUERe_congr_slots L W (x := GUEExtend L W (GUEExtractSlot L W K)) (y := GUEEx L W K)
    (fun q hq => by unfold GUEExtend GUEExtractSlot; rw [dite_eq_left hq])]
  exact GUERe_GUEEx L W hK

/-- The conjugation action on real slot values, `x ↦ extract (Uᴴ · reconstruct(x) · U)`. -/
private noncomputable def GUE_T (U : Matrix (Idx L W) (Idx L W) ℂ)
    (x : GUESlot L W → ℝ) : GUESlot L W → ℝ :=
  GUEExtractSlot L W (GUEConj L W U (GUEReconSlot L W x))

private theorem GUE_T_add (U : Matrix (Idx L W) (Idx L W) ℂ)
    (x y : GUESlot L W → ℝ) : GUE_T L W U (x + y) = GUE_T L W U x + GUE_T L W U y := by
  unfold GUE_T
  rw [GUEReconSlot_add, GUEConj_add, GUEExtractSlot_add]

private theorem GUE_T_smul (U : Matrix (Idx L W) (Idx L W) ℂ) (c : ℝ)
    (x : GUESlot L W → ℝ) : GUE_T L W U (c • x) = c • GUE_T L W U x := by
  unfold GUE_T
  rw [GUEReconSlot_smul, GUEConj_smul, GUEExtractSlot_smul]

private theorem GUE_T_left_inv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    GUE_T L W Uᴴ (GUE_T L W U x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot L W
    (GUEConj_isHermitian L W U (GUEReconSlot_isHermitian L W x)),
    GUEConj_conj_left L W hU, GUEExtractSlot_GUEReconSlot]

private theorem GUE_T_right_inv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    GUE_T L W U (GUE_T L W Uᴴ x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot L W
    (GUEConj_isHermitian L W Uᴴ (GUEReconSlot_isHermitian L W x)),
    GUEConj_conj_right L W hU, GUEExtractSlot_GUEReconSlot]

/-- **Conjugation-invariance of `Tr(K²)`**, the algebraic core of unitary invariance. -/
private theorem GUE_trace_conj_inv {U K : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    Matrix.trace ((Uᴴ * K * U) * (Uᴴ * K * U)) = Matrix.trace (K * K) := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have heq : Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * (K * K) * U := by
    rw [show Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * K * (U * Uᴴ) * K * U by
      simp only [Matrix.mul_assoc], h1]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **The `Q`-invariance of `GUE_T`**: the weighted sum of squares is preserved by conjugation. -/
private theorem GUE_T_Q_inv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    ∑ p : GUESlot L W, (GUE_T L W U x p) ^ 2 / GUEWt L W p.1 =
      ∑ p : GUESlot L W, (x p) ^ 2 / GUEWt L W p.1 := by
  have hK : (GUEReconSlot L W x).IsHermitian := GUEReconSlot_isHermitian L W x
  have hK' : (GUEConj L W U (GUEReconSlot L W x)).IsHermitian := GUEConj_isHermitian L W U hK
  have e1 : (∑ p : GUESlot L W, (GUE_T L W U x p) ^ 2 / GUEWt L W p.1) =
      (Fintype.card (Idx L W) : ℝ) * (Matrix.trace (GUEConj L W U (GUEReconSlot L W x) *
        GUEConj L W U (GUEReconSlot L W x))).re :=
    GUEMainIdentity L W hK'
  have e2 : (∑ p : GUESlot L W, (x p) ^ 2 / GUEWt L W p.1) =
      (Fintype.card (Idx L W) : ℝ) *
        (Matrix.trace (GUEReconSlot L W x * GUEReconSlot L W x)).re := by
    rw [← GUEMainIdentity L W hK]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [show GUEEx L W (GUEReconSlot L W x) p.1 =
        GUEExtractSlot L W (GUEReconSlot L W x) p from rfl,
      GUEExtractSlot_GUEReconSlot]
  rw [e1, e2, show GUEConj L W U (GUEReconSlot L W x) = Uᴴ * GUEReconSlot L W x * U from rfl,
    GUE_trace_conj_inv L W hU]

/-! ### Standardization by the square root of the variance, and the resulting isometry -/

private noncomputable def GUEDv (x : GUESlot L W → ℝ) : GUESlot L W → ℝ :=
  fun p => Real.sqrt (GUEWt L W p.1) * x p

private noncomputable def GUEDvInv (x : GUESlot L W → ℝ) : GUESlot L W → ℝ :=
  fun p => x p / Real.sqrt (GUEWt L W p.1)

private theorem GUEDv_add (x y : GUESlot L W → ℝ) :
    GUEDv L W (x + y) = GUEDv L W x + GUEDv L W y := by
  funext p
  change GUEDv L W (x + y) p = GUEDv L W x p + GUEDv L W y p
  unfold GUEDv
  change Real.sqrt (GUEWt L W p.1) * (x p + y p) = _
  ring

private theorem GUEDv_smul (c : ℝ) (x : GUESlot L W → ℝ) :
    GUEDv L W (c • x) = c • GUEDv L W x := by
  funext p
  change GUEDv L W (c • x) p = c • GUEDv L W x p
  unfold GUEDv
  change Real.sqrt (GUEWt L W p.1) * (c * x p) = c * (Real.sqrt (GUEWt L W p.1) * x p)
  ring

private theorem GUEDvInv_add (x y : GUESlot L W → ℝ) :
    GUEDvInv L W (x + y) = GUEDvInv L W x + GUEDvInv L W y := by
  funext p
  change GUEDvInv L W (x + y) p = GUEDvInv L W x p + GUEDvInv L W y p
  unfold GUEDvInv
  change (x p + y p) / Real.sqrt (GUEWt L W p.1) = _
  ring

private theorem GUEDvInv_smul (c : ℝ) (x : GUESlot L W → ℝ) :
    GUEDvInv L W (c • x) = c • GUEDvInv L W x := by
  funext p
  change GUEDvInv L W (c • x) p = c • GUEDvInv L W x p
  unfold GUEDvInv
  change (c * x p) / Real.sqrt (GUEWt L W p.1) = c * (x p / Real.sqrt (GUEWt L W p.1))
  ring

private theorem GUE_sqrt_ne_zero (q : Idx L W × Idx L W × Bool) :
    Real.sqrt (GUEWt L W q) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (GUEWt_pos L W q))

private theorem GUEDv_GUEDvInv (x : GUESlot L W → ℝ) :
    GUEDv L W (GUEDvInv L W x) = x := by
  funext p
  change Real.sqrt (GUEWt L W p.1) * (x p / Real.sqrt (GUEWt L W p.1)) = x p
  field_simp [GUE_sqrt_ne_zero L W p.1]

private theorem GUEDvInv_GUEDv (x : GUESlot L W → ℝ) :
    GUEDvInv L W (GUEDv L W x) = x := by
  funext p
  change Real.sqrt (GUEWt L W p.1) * x p / Real.sqrt (GUEWt L W p.1) = x p
  field_simp [GUE_sqrt_ne_zero L W p.1]

/-- The composite `extract ∘ (Uᴴ · ·  · U) ∘ reconstruct`, standardized by the square root of the
slot's variance: the map whose invariance under the pointwise Euclidean quadratic form is
established by `GUE_Tpp_Q`. -/
private noncomputable def GUE_Tpp (U : Matrix (Idx L W) (Idx L W) ℂ)
    (x : GUESlot L W → ℝ) : GUESlot L W → ℝ :=
  GUEDvInv L W (GUE_T L W U (GUEDv L W x))

private theorem GUE_Tpp_add (U : Matrix (Idx L W) (Idx L W) ℂ)
    (x y : GUESlot L W → ℝ) : GUE_Tpp L W U (x + y) = GUE_Tpp L W U x + GUE_Tpp L W U y := by
  unfold GUE_Tpp
  rw [GUEDv_add, GUE_T_add, GUEDvInv_add]

private theorem GUE_Tpp_smul (U : Matrix (Idx L W) (Idx L W) ℂ) (c : ℝ)
    (x : GUESlot L W → ℝ) : GUE_Tpp L W U (c • x) = c • GUE_Tpp L W U x := by
  unfold GUE_Tpp
  rw [GUEDv_smul, GUE_T_smul, GUEDvInv_smul]

private theorem GUE_Tpp_left_inv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    GUE_Tpp L W Uᴴ (GUE_Tpp L W U x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_left_inv L W hU, GUEDvInv_GUEDv]

private theorem GUE_Tpp_right_inv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    GUE_Tpp L W U (GUE_Tpp L W Uᴴ x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_right_inv L W hU, GUEDvInv_GUEDv]

/-- **The pointwise sum of squares is preserved by `GUE_Tpp`.** -/
private theorem GUE_Tpp_Q {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (x : GUESlot L W → ℝ) :
    ∑ p : GUESlot L W, (GUE_Tpp L W U x p) ^ 2 = ∑ p : GUESlot L W, (x p) ^ 2 := by
  have key := GUE_T_Q_inv L W hU (GUEDv L W x)
  have hlhs : ∀ p : GUESlot L W, (GUE_Tpp L W U x p) ^ 2 =
      (GUE_T L W U (GUEDv L W x) p) ^ 2 / GUEWt L W p.1 := by
    intro p
    change (GUE_T L W U (GUEDv L W x) p / Real.sqrt (GUEWt L W p.1)) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (GUEWt_pos L W p.1).le]
  have hrhs : ∀ p : GUESlot L W, (GUEDv L W x p) ^ 2 / GUEWt L W p.1 = (x p) ^ 2 := by
    intro p
    change (Real.sqrt (GUEWt L W p.1) * x p) ^ 2 / GUEWt L W p.1 = (x p) ^ 2
    rw [mul_pow, Real.sq_sqrt (GUEWt_pos L W p.1).le]
    field_simp [ne_of_gt (GUEWt_pos L W p.1)]
  simp_rw [hlhs]
  rw [key]
  simp_rw [hrhs]

/-! ### The `EuclideanSpace` isometry, and its relation to `GUE_T` -/

private noncomputable def GUE_Tpp_lin (U : Matrix (Idx L W) (Idx L W) ℂ) :
    (GUESlot L W → ℝ) →ₗ[ℝ] (GUESlot L W → ℝ) where
  toFun := GUE_Tpp L W U
  map_add' := GUE_Tpp_add L W U
  map_smul' := GUE_Tpp_smul L W U

private noncomputable def GUE_Tpp_linEquiv {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    (GUESlot L W → ℝ) ≃ₗ[ℝ] (GUESlot L W → ℝ) :=
  LinearEquiv.ofLinearMap (GUE_Tpp_lin L W U) (GUE_Tpp_lin L W Uᴴ)
    (LinearMap.ext (fun x => GUE_Tpp_right_inv L W hU x))
    (LinearMap.ext (fun x => GUE_Tpp_left_inv L W hU x))

private noncomputable def GUE_Tpp_eucl {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    EuclideanSpace ℝ (GUESlot L W) ≃ₗ[ℝ] EuclideanSpace ℝ (GUESlot L W) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)).trans
    ((GUE_Tpp_linEquiv L W hU).trans (WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)).symm)

private theorem GUE_Tpp_eucl_norm_sq {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (z : EuclideanSpace ℝ (GUESlot L W)) :
    ‖GUE_Tpp_eucl L W hU z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact GUE_Tpp_Q L W hU (fun q => z q)

private theorem GUE_Tpp_eucl_norm {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) (z : EuclideanSpace ℝ (GUESlot L W)) :
    ‖GUE_Tpp_eucl L W hU z‖ = ‖z‖ := by
  have h := congrArg Real.sqrt (GUE_Tpp_eucl_norm_sq L W hU z)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

private noncomputable def GUE_Tpp_isometry {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    EuclideanSpace ℝ (GUESlot L W) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (GUESlot L W) :=
  { GUE_Tpp_eucl L W hU with norm_map' := GUE_Tpp_eucl_norm L W hU }

/-- **`GUE_T` factors through `GUE_Tpp` via the standardizing scale.** -/
private theorem GUE_T_eq_Tpp (U : Matrix (Idx L W) (Idx L W) ℂ)
    (y : GUESlot L W → ℝ) :
    GUE_T L W U y = GUEDv L W (GUE_Tpp L W U (GUEDvInv L W y)) := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUEDv_GUEDvInv]

/-- **The intertwining identity**: reconstructing after `GUE_T` matches conjugating after
reconstructing, for *any* slot values (no Hermitian hypothesis needed: `GUEReconSlot`'s output is
always Hermitian). -/
private theorem GUE_T_intertwine (U : Matrix (Idx L W) (Idx L W) ℂ)
    (x : GUESlot L W → ℝ) :
    GUEReconSlot L W (GUE_T L W U x) = GUEConj L W U (GUEReconSlot L W x) := by
  unfold GUE_T
  exact GUEReconSlot_GUEExtractSlot L W
    (GUEConj_isHermitian L W U (GUEReconSlot_isHermitian L W x))

/-! ### The coordinate-restriction map and its law under `gueP` -/

private theorem GUE_f_injective :
    Function.Injective (fun p : GUESlot L W => p.1) := by
  intro p q h
  exact Subtype.ext h

private theorem Xmat_eq_GUERe_raw (ω : Ω L W) :
    Xmat L W ω = GUERe L W (fun q => ω q) := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · rw [GUERe_apply_lt L W _ h]
    simp [Xmat_apply, Xentry, h]
  · subst h
    rw [GUERe_apply_diag L W _ i]
    simp [Xmat_apply, Xentry]
  · rw [GUERe_apply_gt L W _ h]
    simp [Xmat_apply, Xentry, h, asymm h]

private theorem Xmat_eq_GUEReconSlot (ω : Ω L W) :
    Xmat L W ω =
      GUEReconSlot L W (fun p : GUESlot L W => ω p.1) := by
  rw [Xmat_eq_GUERe_raw]
  refine GUERe_congr_slots L W (fun q hq => ?_)
  unfold GUEExtend
  rw [dite_eq_left hq]

/-! ### Measurability of the finite-dimensional maps -/

private theorem measurable_GUERe :
    Measurable (GUERe L W) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  simp only [GUERe, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem measurable_GUEExtend :
    Measurable (GUEExtend L W) := by
  apply measurable_pi_iff.mpr; intro q
  unfold GUEExtend
  split_ifs <;> fun_prop

private theorem measurable_GUEReconSlot :
    Measurable (GUEReconSlot L W) :=
  (measurable_GUERe L W).comp (measurable_GUEExtend L W)

private theorem measurable_GUEConj (U : Matrix (Idx L W) (Idx L W) ℂ) :
    Measurable (GUEConj L W U) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  unfold GUEConj
  fun_prop

private theorem measurable_GUEExtractSlot :
    Measurable (GUEExtractSlot L W) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEExtractSlot GUEEx
  split_ifs <;> fun_prop

private theorem measurable_GUE_T (U : Matrix (Idx L W) (Idx L W) ℂ) :
    Measurable (GUE_T L W U) :=
  (measurable_GUEExtractSlot L W).comp
    ((measurable_GUEConj L W U).comp (measurable_GUEReconSlot L W))

/-! ### The law of the coordinate-restriction map, identified with a standardized `stdGaussian` -/

private theorem measurable_GUEDv : Measurable (GUEDv L W) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEDv
  fun_prop

private theorem continuous_WithLp_linearEquiv :
    Continuous (⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)).toLinearMap.continuous_of_finiteDimensional

private theorem continuous_WithLp_toLp :
    Continuous (WithLp.toLp 2 : (GUESlot L W → ℝ) → EuclideanSpace ℝ (GUESlot L W)) := by
  rw [← WithLp.coe_symm_linearEquiv (K := ℝ)]
  exact (WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)).symm.toLinearMap.continuous_of_finiteDimensional

private theorem GUE_gaussianReal_eq (p : GUESlot L W) :
    (gaussianReal 0 1).map (fun t => Real.sqrt (GUEWt L W p.1) * t) =
      gaussianReal 0 (gueVar L W p.1) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    change (Real.sqrt (GUEWt L W p.1)) ^ 2 * 1 = (gueVar L W p.1 : ℝ)
    rw [Real.sq_sqrt (GUEWt_pos L W p.1).le, mul_one]
    rfl

private theorem GUE_muI_eq :
    (gueP L W).map (fun ω => fun p : GUESlot L W => ω p.1) =
      Measure.pi (fun p : GUESlot L W => gaussianReal 0 (gueVar L W p.1)) := by
  unfold gueP
  rw [Measure.map_infinitePi_infinitePi_of_inj (GUE_f_injective L W), Measure.infinitePi_eq_pi]

private theorem GUE_muI_eq_stdGaussian_map :
    Measure.pi (fun p : GUESlot L W => gaussianReal 0 (gueVar L W p.1)) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot L W))).map
        (GUEDv L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) := by
  have hpi : (Measure.pi fun _ : GUESlot L W => gaussianReal 0 1).map (GUEDv L W) =
      Measure.pi (fun p : GUESlot L W => gaussianReal 0 (gueVar L W p.1)) := by
    rw [show (GUEDv L W) = (fun x p => Real.sqrt (GUEWt L W p.1) * x p) from rfl,
      Measure.pi_map_pi (fun p => Measurable.aemeasurable (by fun_prop))]
    exact congrArg Measure.pi (funext fun p => GUE_gaussianReal_eq L W p)
  have hstd : (Measure.pi fun _ : GUESlot L W => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot L W))).map
        (⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_WithLp_linearEquiv L W).measurable
      (continuous_WithLp_toLp L W).measurable]
    have hid : (⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)) ∘ WithLp.toLp 2) =
        (id : (GUESlot L W → ℝ) → GUESlot L W → ℝ) := by
      funext x
      change WithLp.ofLp (WithLp.toLp 2 x) = x
      rfl
    rw [hid, Measure.map_id]
  rw [← hpi, hstd, Measure.map_map (measurable_GUEDv L W)
    (continuous_WithLp_linearEquiv L W).measurable]

private theorem GUE_muI_eq_final :
    (gueP L W).map (fun ω => fun p : GUESlot L W => ω p.1) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot L W))).map
        (GUEDv L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) := by
  rw [GUE_muI_eq, GUE_muI_eq_stdGaussian_map]

/-- **Invariance of the coordinate law under `GUE_T`.** -/
private theorem GUE_muI_invariant {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    ((gueP L W).map (fun ω => fun p : GUESlot L W => ω p.1)).map
        (GUE_T L W U) =
      (gueP L W).map (fun ω => fun p : GUESlot L W => ω p.1) := by
  rw [GUE_muI_eq_final]
  rw [Measure.map_map (measurable_GUE_T L W U)
    ((measurable_GUEDv L W).comp (continuous_WithLp_linearEquiv L W).measurable)]
  have hfun : GUE_T L W U ∘ (GUEDv L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) =
      (GUEDv L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ))) ∘ (GUE_Tpp_isometry L W hU) := by
    funext z
    change GUE_T L W U (GUEDv L W ((WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)) z)) =
      GUEDv L W ((WithLp.linearEquiv 2 ℝ (GUESlot L W → ℝ)) (GUE_Tpp_isometry L W hU z))
    rw [GUE_T_eq_Tpp]
    congr 1
    show GUE_Tpp L W U (GUEDvInv L W (GUEDv L W ((WithLp.linearEquiv 2 ℝ _) z))) = _
    rw [GUEDvInv_GUEDv]
    rfl
  rw [hfun, ← Measure.map_map
    ((measurable_GUEDv L W).comp (continuous_WithLp_linearEquiv L W).measurable)
    (LinearIsometryEquiv.continuous _).measurable, stdGaussian_map (GUE_Tpp_isometry L W hU)]

/-! ### The invariance statements -/

/-- The invariance of the GUE law in the form `Uᴴ * X * U`. -/
private theorem GUE_map_conj {U : Matrix (Idx L W) (Idx L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    (gueP L W).map (fun ω => Uᴴ * Xmat L W ω * U) = (gueP L W).map (Xmat L W) := by
  have hr_meas : Measurable (fun ω : Ω L W => fun p : GUESlot L W => ω p.1) := by
    apply measurable_pi_iff.mpr; intro p; exact measurable_pi_apply _
  have key1 : (fun ω => Uᴴ * Xmat L W ω * U) =
      (GUEConj L W U ∘ GUEReconSlot L W) ∘
        (fun ω : Ω L W => fun p : GUESlot L W => ω p.1) := by
    funext ω
    change Uᴴ * Xmat L W ω * U =
      GUEConj L W U (GUEReconSlot L W (fun p : GUESlot L W => ω p.1))
    rw [Xmat_eq_GUEReconSlot L W ω]
    rfl
  have key2 : Xmat L W =
      GUEReconSlot L W ∘ (fun ω : Ω L W => fun p : GUESlot L W => ω p.1) :=
    funext (Xmat_eq_GUEReconSlot L W)
  rw [key1, key2,
    ← Measure.map_map ((measurable_GUEConj L W U).comp (measurable_GUEReconSlot L W)) hr_meas,
    ← Measure.map_map (measurable_GUEReconSlot L W) hr_meas,
    show GUEConj L W U ∘ GUEReconSlot L W = GUEReconSlot L W ∘ GUE_T L W U from
      funext (fun x => (GUE_T_intertwine L W U x).symm),
    ← Measure.map_map (measurable_GUEReconSlot L W) (measurable_GUE_T L W U)]
  congr 1
  exact GUE_muI_invariant L W hU

/-- **Unitary invariance of the GUE law**: the law of the GUE matrix `Xmat L W` under `gueP L W`
is invariant under conjugation by any fixed unitary matrix. -/
theorem gueP_map_unitary_conj (U : Matrix (Idx L W) (Idx L W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Idx L W) ℂ) :
    (gueP L W).map (fun ω => U * Xmat L W ω * star U) = (gueP L W).map (Xmat L W) := by
  have hV : star U ∈ Matrix.unitaryGroup (Idx L W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h := GUE_map_conj L W hV
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

end RBM.Univ

end
