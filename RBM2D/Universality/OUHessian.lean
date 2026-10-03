/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins
import RBM2D.Green.GreenDeriv
import RBM2D.Gauss.Envelope
import RBM2D.Hierarchy.Loops

/-!
# Pointwise Hessian structure for the centered-variance Green comparison

The deterministic, finite-dimensional second-variation calculation behind the `L₁` and `L₂`
kernels of `(EMCTE2)` (with the definitions of `L_{1,t}`, `L_{2,t}`).  No OU path, expectation or
time integral occurs.

Vocabulary (`d = 2`):

* the index set is `Idx L W = Z2 (W * L)`; the matrices are `RBM.Green.Bmat L W`; the used
  coordinates are `RBM.Gauss.usedCoords`; the Stieltjes transform is `stieltjesN`; the band
  variance is `RBM.Gauss.svar L W`;
* the coordinate-derivative vocabulary `coordD1`, `coordD2`, `wirtSecond`;
* the bridges `card_Idx_eq`, `centeredVarianceEntry_cast`, `signedGreen_eq_gSel`,
  `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t` to the definitions `Scirc`, `gSel`, `L1t`, `L2t`
  of `Universality/Pins.lean`.

On the diagonal the imaginary direction `Bmat i i false` is not Hermitian and is never used.
-/

noncomputable section

-- The style linters below only report unused simp arguments / section variables / `<;>` here.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal
open scoped Matrix.Norms.L2Operator

/-! ### The coordinate directions -/

section Directions

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- The real direction is symmetric in the pair: `Bmat j i true = Bmat i j true`. -/
theorem Bmat_swap_true (i j : Idx L W) :
    RBM.Green.Bmat L W j i true = RBM.Green.Bmat L W i j true := by
  ext k l
  rw [RBM.Green.GreenDeriv_Bmat_apply, RBM.Green.GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_left h1]
    · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

omit [NeZero L] [NeZero W] in
/-- The imaginary direction is antisymmetric in the pair (off the diagonal):
`Bmat j i false = -Bmat i j false`. -/
theorem Bmat_swap_false {i j : Idx L W} (hij : i ≠ j) :
    RBM.Green.Bmat L W j i false = -RBM.Green.Bmat L W i j false := by
  ext k l
  change RBM.Green.Bmat L W j i false k l = -(RBM.Green.Bmat L W i j false k l)
  rw [RBM.Green.GreenDeriv_Bmat_apply, RBM.Green.GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := by
      rintro ⟨hkj, _⟩
      refine hij ?_
      rw [← h1.1]
      exact hkj
    rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, neg_zero]

/-- Every direction `Bmat i j b` with `i ≠ j` or `b = true` is Hermitian (the redundant
`Bmat i i false = I • E_ii` is the one exception and is never read). -/
theorem Bmat_isHermitian_of_ne_or {i j : Idx L W} {b : Bool} (h : i ≠ j ∨ b = true) :
    (RBM.Green.Bmat L W i j b).IsHermitian := by
  by_cases hij : i = j
  · subst hij
    have hb : b = true := h.resolve_left (fun hne => hne rfl)
    subst hb
    exact RBM.Green.GreenDeriv_Bmat_isHermitian (c := (i, i, true))
      (RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inr ⟨rfl, rfl⟩))
  · rcases RBM.Gauss.idxKey_lt_or_eq_or_lt L W i j with hlt | heq | hgt
    · exact RBM.Green.GreenDeriv_Bmat_isHermitian (c := (i, j, b))
        (RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inl hlt))
    · exact (hij heq).elim
    · have hmem : (j, i, b) ∈ usedCoords L W :=
        RBM.Green.GreenDeriv_mem_usedCoords.2 (Or.inl hgt)
      have hji := RBM.Green.GreenDeriv_Bmat_isHermitian (c := (j, i, b)) hmem
      cases b
      · have hswap := Bmat_swap_false L W hij
        have hneg : -RBM.Green.Bmat L W j i false = RBM.Green.Bmat L W i j false := by
          rw [hswap]
          simp
        rw [← hneg]
        exact hji.neg
      · rw [← Bmat_swap_true L W i j]
        exact hji

end Directions

/-! ### Coordinate derivatives -/

section CoordDeriv

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `∂_c Φ (M)`: the first directional derivative of `Φ` at `M` along the direction `Bmat c` of
the coordinate `c`. -/
def coordD1 (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (c : Coord L W) : ℂ :=
  fderiv ℝ Φ M (RBM.Green.Bmat L W c.1 c.2.1 c.2.2)

/-- `∂_c ∂_c Φ (M)`: the second directional derivative of `Φ` at `M`, twice along `Bmat c`. -/
def coordD2 (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (c : Coord L W) : ℂ :=
  fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W c.1 c.2.1 c.2.2)
    (RBM.Green.Bmat L W c.1 c.2.1 c.2.2)

/-- `∂_ij ∂_ji Φ` in the Wirtinger convention of the paper: for `i ≠ j`,
`∂_ij ∂_ji = (∂_a² + ∂_b²)/4` with `∂_a² ↔ (i, j, true)` and `∂_b² ↔ (i, j, false)`; on the
diagonal `∂_ii ∂_ii = ∂_a²`. -/
def wirtSecond (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (i j : Idx L W) : ℂ :=
  if i = j then coordD2 L W Φ M (i, i, true)
  else (1 / 4 : ℝ) • (coordD2 L W Φ M (i, j, true) + coordD2 L W Φ M (i, j, false))

end CoordDeriv

/-! ### The Hessian along a Hermitian line -/

section ResolventVariation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordinary second derivative of a finite product separates into the single-factor Hessians
and the ordered cross-factor products. -/
theorem hasDerivAt_deriv_finset_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f fp : ι → ℝ → ℝ) (fpp : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t)
    (hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t)
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j 0) * fpp i +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)) 0 := by
  have hfirst (t : ℝ) :
      HasDerivAt (fun u : ℝ => ∏ i ∈ s, f i u)
        (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [smul_eq_mul] using h
  have hderiv :
      (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t) =
        fun t => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := by
    funext t
    exact (hfirst t).deriv
  let p : ι → ℝ := fun i => ∏ j ∈ s.erase i, f j 0
  let dp : ι → ℝ := fun i =>
    ∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0
  have hprod (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => ∏ j ∈ s.erase i, f j t) (dp i) 0 := by
    have h := HasDerivAt.fun_finsetProd (u := s.erase i) (f := fun j t => f j t)
      (f' := fun j => fp j 0) (fun j hj => hf j (Finset.mem_of_mem_erase hj) 0)
    simpa [dp, smul_eq_mul] using h
  have hterm (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t)
        (dp i * fp i 0 + p i * fpp i) 0 := by
    have h := (hprod i hi).mul (hfp i hi)
    refine h.congr_deriv ?_
    simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]
  have hsum₀ : HasDerivAt
      (fun t : ℝ => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t)
      (∑ i ∈ s, (dp i * fp i 0 + p i * fpp i)) 0 := by
    have h := HasDerivAt.sum (u := s)
      (A := fun i t => (∏ j ∈ s.erase i, f j t) * fp i t)
      (A' := fun i => dp i * fp i 0 + p i * fpp i)
      (fun i hi => hterm i hi)
    have heq : (fun t : ℝ => ∑ i ∈ s,
        (∏ j ∈ s.erase i, f j t) * fp i t) =
        ∑ i ∈ s, fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t := by
      funext t
      simp
    rw [heq]
    exact h
  rw [hderiv]
  refine hsum₀.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro i hi
  simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]

private theorem OUHessian_fderiv_fderiv_eq_lineSecond {H A : Matrix n n ℂ}
    {f : Matrix n n ℂ → ℂ} (hf : ContDiffAt ℝ 2 f H)
    (hline : ∀ t : ℝ, DifferentiableAt ℝ f (H + (t : ℂ) • A)) :
    fderiv ℝ (fderiv ℝ f) H A A =
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hf.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline0 := Gauss.hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline0
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    exact (hline t).hasFDerivAt.comp_hasDerivAt t (Gauss.hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

private theorem OUHessian_deriv_deriv_ofRealCLM {g dg : ℝ → ℝ} {d2g : ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (dg t) t)
    (hdg : HasDerivAt dg d2g 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) 0 = (d2g : ℂ) := by
  have hfirst (t : ℝ) : HasDerivAt (fun s : ℝ => (g s : ℂ)) (dg t : ℂ) t := by
    have h := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hg t)
    simpa [Function.comp_def] using h
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) =
      fun t => (dg t : ℂ) := by
    funext t
    exact (hfirst t).deriv
  have hsecond := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hdg
  rw [hderiv]
  exact hsecond.deriv

private noncomputable def OUHessian_traceCLM : Matrix n n ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap

private def OUHessian_entryMatrix (i j : n) : Matrix n n ℂ := Matrix.single i j 1

private theorem OUHessian_matrix_mul_entryMatrix_apply (X : Matrix n n ℂ) (i j a b : n) :
    (X * OUHessian_entryMatrix i j) a b = if b = j then X a i else 0 := by
  by_cases hb : b = j
  · subst b
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [OUHessian_entryMatrix]
    · intro x hx hxi
      simp [OUHessian_entryMatrix, hxi.symm]
    · simp
  · simp [OUHessian_entryMatrix, Matrix.mul_apply, Matrix.single_apply, hb, Ne.symm hb]

private theorem OUHessian_matrix_mul_entryMatrix_mul_apply (X Y : Matrix n n ℂ)
    (i j a b : n) :
    (X * OUHessian_entryMatrix i j * Y) a b = X a i * Y j b := by
  rw [Matrix.mul_apply]
  simp_rw [OUHessian_matrix_mul_entryMatrix_apply]
  simp

private theorem OUHessian_trace_green_entryCross (G : Matrix n n ℂ) (i j : n) :
    (G * OUHessian_entryMatrix i j * G * OUHessian_entryMatrix j i * G).trace =
      (G * G) i i * G j j := by
  calc
    (G * OUHessian_entryMatrix i j * G * OUHessian_entryMatrix j i * G).trace =
        ((G * OUHessian_entryMatrix i j * G) * (OUHessian_entryMatrix j i * G)).trace := by
      simp [mul_assoc]
    _ = ((OUHessian_entryMatrix j i * G) * (G * OUHessian_entryMatrix i j * G)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (OUHessian_entryMatrix j i * (G * G * OUHessian_entryMatrix i j * G)).trace := by
      simp [mul_assoc]
    _ = (G * G * OUHessian_entryMatrix i j * G) i j := by
      simpa [OUHessian_entryMatrix] using
        (Matrix.trace_single_mul j i (1 : ℂ) (G * G * OUHessian_entryMatrix i j * G))
    _ = (G * G) i i * G j j :=
      OUHessian_matrix_mul_entryMatrix_mul_apply (G * G) G i j i j

private theorem OUHessian_trace_green_singleEntry (G : Matrix n n ℂ) (a b : n) :
    (G * OUHessian_entryMatrix a b * G).trace = (G * G) b a := by
  calc
    (G * OUHessian_entryMatrix a b * G).trace =
        (G * (OUHessian_entryMatrix a b * G)).trace := by
      congr 1
      simp [Matrix.mul_assoc]
    _ = ((OUHessian_entryMatrix a b * G) * G).trace := Matrix.trace_mul_comm _ _
    _ = (OUHessian_entryMatrix a b * (G * G)).trace := by
      congr 1 <;> simp [Matrix.mul_assoc]
    _ = (G * G) b a := by
      simpa [OUHessian_entryMatrix] using Matrix.trace_single_mul a b (1 : ℂ) (G * G)

private theorem OUHessian_trace_green_entryPair (G : Matrix n n ℂ) (i j : n) :
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace =
      (G * G) j i + (G * G) i j := by
  calc
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace =
        (G * OUHessian_entryMatrix i j * G + G * OUHessian_entryMatrix j i * G).trace := by
      congr 1 <;> simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = (G * OUHessian_entryMatrix i j * G).trace +
        (G * OUHessian_entryMatrix j i * G).trace :=
      Matrix.trace_add _ _
    _ = (G * G) j i + (G * G) i j := by
      rw [OUHessian_trace_green_singleEntry G i j, OUHessian_trace_green_singleEntry G j i]

private theorem OUHessian_trace_green_entryImagPair (G : Matrix n n ℂ) (i j : n) :
    (G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) *
        G).trace =
      Complex.I * ((G * G) j i - (G * G) i j) := by
  have hmul : G * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) * G =
      Complex.I • (G * OUHessian_entryMatrix i j * G) -
        Complex.I • (G * OUHessian_entryMatrix j i * G) := by
    calc
      G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) * G =
          (Complex.I • (G * OUHessian_entryMatrix i j) -
            Complex.I • (G * OUHessian_entryMatrix j i)) * G := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      _ = Complex.I • (G * OUHessian_entryMatrix i j * G) -
          Complex.I • (G * OUHessian_entryMatrix j i * G) := by
        rw [Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [hmul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    OUHessian_trace_green_singleEntry, OUHessian_trace_green_singleEntry]
  simp only [smul_eq_mul]
  ring

end ResolventVariation

section BmatEntry

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OUHessian_Bmat_real_eq_entryMatrices {i j : Idx L W} (hij : i ≠ j) :
    RBM.Green.Bmat L W i j true = OUHessian_entryMatrix i j + OUHessian_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h1, h2, h1', h2',
        and_comm]

private theorem OUHessian_Bmat_imag_eq_entryMatrices {i j : Idx L W} (hij : i ≠ j) :
    RBM.Green.Bmat L W i j false =
      Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h1, h2, h1', h2',
        and_comm]

private theorem OUHessian_Bmat_diag_true_eq_entryMatrix (i : Idx L W) :
    RBM.Green.Bmat L W i i true = OUHessian_entryMatrix i i := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply]
  · have h' : ¬ (i = k ∧ i = l) := by
      rintro ⟨hik, hil⟩
      exact h ⟨hik.symm, hil.symm⟩
    simp [RBM.Green.Bmat, OUHessian_entryMatrix, Matrix.single_apply, h, h']

end BmatEntry

section ResolventVariation2

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem OUHessian_trace_green_Bmat_pair_sum {G : Matrix n n ℂ} {i j : n}
    (hij : i ≠ j) :
    (G * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G *
        (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) * G).trace +
      (G * (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) * G *
        (Complex.I • OUHessian_entryMatrix i j - Complex.I • OUHessian_entryMatrix j i) *
          G).trace =
      2 * ((G * G) i i * G j j + (G * G) j j * G i i) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp_rw [OUHessian_trace_green_entryCross]
  simp only [smul_eq_mul, Complex.I_mul_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem OUHessian_analyticAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => RBM.green K z) H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : AnalyticAt ℝ q H := by
    exact analyticAt_id.sub analyticAt_const
  have hU : IsUnit (q H) := Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv : AnalyticAt ℝ Ring.inverse (q H) := by
    rw [← hu]
    exact analyticAt_inverse u
  have hc := hinv.comp hq
  convert hc using 1
  funext K
  simp [q, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

private theorem OUHessian_hasFDerivAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => RBM.green K z)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z) (RBM.green H z))
      H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : HasFDerivAt q (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) H := by
    simpa [q] using (hasFDerivAt_id H).sub_const (z • (1 : Matrix n n ℂ))
  have hU : IsUnit (q H) := Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv := (hasFDerivAt_ringInverse u).comp H hq
  have hinvval : (↑u⁻¹ : Matrix n n ℂ) = RBM.green H z := by
    calc
      (↑u⁻¹ : Matrix n n ℂ) = Ring.inverse (↑u : Matrix n n ℂ) :=
        (Ring.inverse_unit u).symm
      _ = Ring.inverse (q H) := by rw [hu]
      _ = RBM.green H z := by simp [q, RBM.green, Matrix.nonsing_inv_eq_ringInverse]
  convert hinv using 1
  · funext K
    simp [q, Function.comp_def, RBM.green, Matrix.nonsing_inv_eq_ringInverse]
  · rw [← hinvval]
    simp

private theorem OUHessian_analyticAt_stieltjes_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => stieltjesN K z) H := by
  have hg := OUHessian_analyticAt_green_matrix hH z hz
  have ht : AnalyticAt ℝ
      (fun K : Matrix n n ℂ => OUHessian_traceCLM (n := n) (RBM.green K z)) H := by
    have ht0 : AnalyticAt ℝ (fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A)
        (RBM.green H z) :=
      (OUHessian_traceCLM (n := n)).analyticAt (RBM.green H z)
    have hcomp : AnalyticAt ℝ
        ((fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A) ∘
          (fun K : Matrix n n ℂ => RBM.green K z)) H :=
      AnalyticAt.comp (g := fun A : Matrix n n ℂ => OUHessian_traceCLM (n := n) A)
        (f := fun K : Matrix n n ℂ => RBM.green K z) (x := H) ht0 hg
    simpa [Function.comp_def] using hcomp
  have hc : AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      (Fintype.card n : ℂ)⁻¹ * OUHessian_traceCLM (n := n) (RBM.green K z)) H := by
    exact (analyticAt_const (x := H)).mul ht
  convert hc using 1
  funext K
  rfl

private theorem OUHessian_hasFDerivAt_stieltjes_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => stieltjesN K z)
      (((Fintype.card n : ℂ)⁻¹) •
        (OUHessian_traceCLM (n := n) ∘L
          (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z)
            (RBM.green H z)))) H := by
  have hgreen := OUHessian_hasFDerivAt_green_matrix hH z hz
  have htrace := (OUHessian_traceCLM (n := n)).hasFDerivAt.comp H hgreen
  have hst := htrace.const_mul ((Fintype.card n : ℂ)⁻¹)
  have hEq : (fun K : Matrix n n ℂ => stieltjesN K z)
      = fun K => (Fintype.card n : ℂ)⁻¹ * OUHessian_traceCLM (n := n) (RBM.green K z) := by
    rfl
  rw [hEq]
  simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using hst

private theorem OUHessian_fderiv_stieltjesIm_apply_matrix {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H A =
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green H z * A * RBM.green H z).trace).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp H
    (OUHessian_hasFDerivAt_stieltjes_matrix hH z hz)).fderiv
  have hA := congrArg (fun L : Matrix n n ℂ →L[ℝ] ℝ => L A) h
  calc
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H A =
        (fderiv ℝ (⇑Complex.imCLM ∘ fun K : Matrix n n ℂ => stieltjesN K z) H) A := rfl
    _ = (Complex.imCLM ∘SL
        ((Fintype.card n : ℂ)⁻¹ •
          OUHessian_traceCLM (n := n) ∘L
            (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (RBM.green H z)
              (RBM.green H z)))) A := hA
    _ = (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green H z * A * RBM.green H z).trace).im := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
        OUHessian_traceCLM, Matrix.traceLinearMap_apply, Complex.mul_im, mul_assoc]

private theorem OUHessian_analyticAt_stieltjesIm_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => (stieltjesN K z).im) H := by
  have hm := OUHessian_analyticAt_stieltjes_matrix hH z hz
  have hi0 : AnalyticAt ℝ (fun w : ℂ => Complex.imCLM w) (stieltjesN H z) :=
    Complex.imCLM.analyticAt (stieltjesN H z)
  have hi : AnalyticAt ℝ
      ((fun w : ℂ => Complex.imCLM w) ∘ (fun K : Matrix n n ℂ => stieltjesN K z)) H :=
    AnalyticAt.comp (g := fun w : ℂ => Complex.imCLM w)
      (f := fun K : Matrix n n ℂ => stieltjesN K z) (x := H) hi0 hm
  simpa [Function.comp_def] using hi

private theorem OUHessian_analyticAt_stieltjesImComplex_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ)) H := by
  have hm := OUHessian_analyticAt_stieltjesIm_matrix hH z hz
  have ho : AnalyticAt ℝ (fun x : ℝ => Complex.ofRealCLM x)
      ((stieltjesN H z).im) := Complex.ofRealCLM.analyticAt _
  have hc : AnalyticAt ℝ
      ((fun x : ℝ => Complex.ofRealCLM x) ∘
        (fun K : Matrix n n ℂ => (stieltjesN K z).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => Complex.ofRealCLM x)
      (f := fun K : Matrix n n ℂ => (stieltjesN K z).im) (x := H) ho hm
  simpa [Function.comp_def] using hc

private theorem OUHessian_analyticAt_stieltjesImProduct_complex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H := by
  have hR : AnalyticAt ℝ
      (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im) H := by
    exact s.analyticAt_fun_prod
      (fun i hi => OUHessian_analyticAt_stieltjesIm_matrix hH (z i) (hz i hi))
  have hcast : AnalyticAt ℝ (fun x : ℝ => (x : ℂ))
      (∏ i ∈ s, (stieltjesN H (z i)).im) := Complex.ofRealCLM.analyticAt _
  have hcomp : AnalyticAt ℝ
      ((fun x : ℝ => (x : ℂ)) ∘
        (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => (x : ℂ))
      (f := fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjesN K (z i)).im)
      (x := H) hcast hR
  simpa [Function.comp_def] using hcomp

private theorem OUHessian_fderiv_fderiv_stieltjesImComplex_eq_lineSecond
    {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ))) H A A =
      deriv (fun t : ℝ => deriv
        (fun s : ℝ => ((stieltjesN (H + (s : ℂ) • A) z).im : ℂ)) t) 0 := by
  let f : Matrix n n ℂ → ℂ := fun K => ((stieltjesN K z).im : ℂ)
  have hc : ContDiffAt ℝ 2 f H :=
    (OUHessian_analyticAt_stieltjesImComplex_matrix hH z hz).contDiffAt
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hc.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline := Gauss.hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    have hHt := Gauss.isHermitian_add_realSmul hH hA t
    exact (OUHessian_analyticAt_stieltjesImComplex_matrix hHt z hz).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt t (Gauss.hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  change fderiv ℝ (fderiv ℝ f) H A A = _
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv
        (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

/-- The resolvent along a Hermitian real line has the usual first variation. -/
theorem hasDerivAt_green_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      (-(RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z)) t := by
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    intro s
    have hsum : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (H + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [hsum]
    exact Gauss.isUnit_sub_smul_one_of_im_ne_zero (Gauss.isHermitian_add_realSmul hH hA s) hz
  have hEq : (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    change (H + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hEq_t := congrFun hEq t
  have hline := Gauss.hasDerivAt_lineInverse hU t
  rw [← hEq_t] at hline
  rw [hEq]
  exact hline

/-- The first derivative of the paper-normalized Stieltjes transform along a Hermitian line. -/
theorem hasDerivAt_stieltjesN_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stieltjesN (H + (s : ℂ) • A) z)
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  have htrace := HasFDerivAt.comp_hasDerivAt t
    (OUHessian_traceCLM (n := n)).hasFDerivAt hG
  have hmul := (htrace.const_mul ((Fintype.card n : ℂ)⁻¹))
  have hst : (fun s : ℝ => stieltjesN (H + (s : ℂ) • A) z)
      = fun s : ℝ => (Fintype.card n : ℂ)⁻¹ *
          OUHessian_traceCLM (n := n) (RBM.green (H + (s : ℂ) • A) z) := by
    rfl
  rw [hst]
  simpa [OUHessian_traceCLM, Matrix.traceLinearMap_apply] using hmul

/-- Along a Hermitian line, the derivative of the first Stieltjes variation is the usual
resolvent second variation. -/
theorem hasDerivAt_stieltjesFirstVariation {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => -((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z * A *
          RBM.green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  set R := RBM.green (H + (t : ℂ) • A) z
  have hRA := hG.mul_const A
  have hRARA := hRA.mul hG
  have hfun : ((fun s : ℝ => RBM.green (H + (s : ℂ) • A) z * A) *
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)) =
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z *
        (A * RBM.green (H + (s : ℂ) • A) z)) := by
    funext s
    simp [Pi.mul_apply, Matrix.mul_assoc]
  have hprod : HasDerivAt
      (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z *
        (A * RBM.green (H + (s : ℂ) • A) z))
      ((-(R * A * R) * A) * R + (R * A) * (-(R * A * R))) t := by
    rw [← hfun]
    simpa [R, Matrix.mul_assoc] using hRARA
  have htr := HasFDerivAt.comp_hasDerivAt t
    (OUHessian_traceCLM (n := n)).hasFDerivAt hprod
  have hconst := htr.const_mul (-((Fintype.card n : ℂ)⁻¹))
  convert hconst using 1 <;>
    simp [OUHessian_traceCLM, Matrix.traceLinearMap_apply, Matrix.mul_assoc] <;> ring

/-- The real Stieltjes factor along a Hermitian matrix line. -/
def stieltjesImAlong (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (RBM.Univ.stieltjesN (H + (t : ℂ) • A) z).im

/-- Its first derivative, written as the imaginary part of the resolvent first variation. -/
def stieltjesImLineFirst (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (-((Fintype.card n : ℂ)⁻¹) *
    (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace).im

/-- Its second derivative at the base point, written as the resolvent second variation. -/
def stieltjesImLineSecond (H A : Matrix n n ℂ) (z : ℂ) : ℝ :=
  (2 * (Fintype.card n : ℂ)⁻¹ *
    (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im

/-- The finite-product second line variation, including all single and ordered cross terms. -/
def stieltjesImProductLineSecond {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (z : ι → ℂ) : ℝ :=
  ∑ i ∈ s,
    ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
        stieltjesImLineSecond H A (z i) +
      (∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
          stieltjesImLineFirst H A (z j) 0) *
        stieltjesImLineFirst H A (z i) 0)

/-- The Fréchet Hessian of a finite product of real Stieltjes factors along any Hermitian
direction has the single-factor and ordered cross-factor expansion. -/
theorem fderiv_fderiv_stieltjesImProduct_hermitianLine {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H A A =
      ((stieltjesImProductLineSecond s H A z : ℝ) : ℂ) := by
  let F : Matrix n n ℂ → ℂ := fun K =>
    ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)
  let f : ι → ℝ → ℝ := fun i t => stieltjesImAlong H A (z i) t
  let fp : ι → ℝ → ℝ := fun i t => stieltjesImLineFirst H A (z i) t
  let fpp : ι → ℝ := fun i => stieltjesImLineSecond H A (z i)
  let g : ℝ → ℝ := fun t => ∏ i ∈ s, f i t
  let d2g : ℝ := ∑ i ∈ s,
    ((∏ j ∈ s.erase i, f j 0) * fpp i +
      (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)
  have hC2 : ContDiffAt ℝ 2 F H :=
    (OUHessian_analyticAt_stieltjesImProduct_complex s hH z hz).contDiffAt
  have hline : ∀ t : ℝ, DifferentiableAt ℝ F (H + (t : ℂ) • A) := by
    intro t
    have htH := Gauss.isHermitian_add_realSmul hH hA t
    exact (OUHessian_analyticAt_stieltjesImProduct_complex s htH z hz).differentiableAt
  have hbridge := OUHessian_fderiv_fderiv_eq_lineSecond hC2 hline
  have hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t := by
    intro i hi t
    have hst := hasDerivAt_stieltjesN_hermitianLine hH hA (z i) (hz i hi) t
    have him := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hst
    simpa [f, fp, stieltjesImAlong, stieltjesImLineFirst, Function.comp_def] using him
  have hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0 := by
    intro i hi
    have hst := hasDerivAt_stieltjesFirstVariation hH hA (z i) (hz i hi) 0
    have him := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hst
    simpa [fp, fpp, stieltjesImLineFirst, stieltjesImLineSecond,
      Function.comp_def] using him
  have hfirst (t : ℝ) : HasDerivAt g
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [g, smul_eq_mul] using h
  have hg : ∀ t : ℝ, HasDerivAt g (deriv g t) t := by
    intro t
    have heq : deriv g t =
        ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := (hfirst t).deriv
    exact (hfirst t).congr_deriv heq.symm
  have hsecond := hasDerivAt_deriv_finset_product_expansion s f fp fpp hf hfp
  have hsecond' : HasDerivAt (fun t => deriv g t) d2g 0 := by
    simpa [g, d2g, f, fp, fpp] using hsecond
  have hcast := OUHessian_deriv_deriv_ofRealCLM hg hsecond'
  have hlineEq : (fun t : ℝ => F (H + (t : ℂ) • A)) = fun t => (g t : ℂ) := by
    funext t
    rfl
  rw [hlineEq] at hbridge
  rw [hbridge]
  simpa [stieltjesImProductLineSecond, d2g, f, fp, fpp] using hcast

/-! ### The Wirtinger Hessian of a product of `Im m` factors -/

end ResolventVariation2

section WirtingerHessian

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The Wirtinger Hessian of a finite product is the real-coordinate combination of the single
and cross resolvent variations. -/
theorem wirtSecond_stieltjesImProduct_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx L W) (Idx L W) ℂ)
    (hH : H.IsHermitian) (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : Idx L W) :
    wirtSecond L W
        (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b =
      if a = b then
        (stieltjesImProductLineSecond s H (RBM.Green.Bmat L W a a true) z : ℂ)
      else
        (1 / 4 : ℝ) •
          ((stieltjesImProductLineSecond s H (RBM.Green.Bmat L W a b true) z : ℂ) +
            (stieltjesImProductLineSecond s H (RBM.Green.Bmat L W a b false) z : ℂ)) := by
  by_cases hab : a = b
  · subst b
    simp only [wirtSecond, ↓reduceIte]
    have hA : (RBM.Green.Bmat L W a a true).IsHermitian :=
      Bmat_isHermitian_of_ne_or L W (Or.inr rfl)
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
        (RBM.Green.Bmat L W a a true) (RBM.Green.Bmat L W a a true) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
      (RBM.Green.Bmat L W a a true) hH hA z hz]
  · simp only [wirtSecond, ite_eq_right hab]
    have hT : (RBM.Green.Bmat L W a b true).IsHermitian :=
      Bmat_isHermitian_of_ne_or L W (Or.inl hab)
    have hF : (RBM.Green.Bmat L W a b false).IsHermitian :=
      Bmat_isHermitian_of_ne_or L W (Or.inl hab)
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
        ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
          (RBM.Green.Bmat L W a b true) (RBM.Green.Bmat L W a b true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
        ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H
          (RBM.Green.Bmat L W a b false) (RBM.Green.Bmat L W a b false)) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (RBM.Green.Bmat L W a b true) hH hT z hz,
        fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (RBM.Green.Bmat L W a b false) hH hF z hz]

end WirtingerHessian

section FirstWirtinger

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem OUHessian_deriv_deriv_stieltjes_im_complex_hermitianLine
    {n : Type*} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (fun t : ℝ => deriv
      (fun s : ℝ => ((stieltjesN (H + (s : ℂ) • A) z).im : ℂ)) t) 0 =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) := by
  let fR : ℝ → ℝ := fun s => (stieltjesN (H + (s : ℂ) • A) z).im
  let fC : ℝ → ℂ := fun s => (fR s : ℂ)
  let dR : ℝ → ℝ := fun s => Complex.imCLM
    (-((Fintype.card n : ℂ)⁻¹) *
      (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
  have hfirstR (t : ℝ) : HasDerivAt fR (dR t) t := by
    have hs := hasDerivAt_stieltjesN_hermitianLine hH hA z hz t
    have hi := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hs
    simpa [Function.comp_def, fR, dR] using hi
  have hfirstC (t : ℝ) : HasDerivAt fC ((dR t : ℂ)) t := by
    have hc := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hfirstR t)
    simpa [Function.comp_def, fC] using hc
  have hderiv : (fun t : ℝ => deriv fC t) = fun t => (dR t : ℂ) := by
    funext t
    exact (hfirstC t).deriv
  have hsecond := hasDerivAt_stieltjesFirstVariation hH hA z hz 0
  have hsecondR : HasDerivAt dR
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im 0 := by
    have hi := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hsecond
    simpa [Function.comp_def, dR] using hi
  have hsecondC : HasDerivAt (fun s : ℝ => (dR s : ℂ))
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) 0 := by
    have hc := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hsecondR
    simpa [Function.comp_def] using hc
  change deriv (fun t : ℝ => deriv fC t) 0 = _
  calc
    deriv (fun t : ℝ => deriv fC t) 0 = deriv (fun t : ℝ => (dR t : ℂ)) 0 := by
      rw [hderiv]
    _ = _ := hsecondC.deriv

private theorem OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine
    {n : Type*} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjesN K z).im : ℂ))) H A A =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im : ℂ) := by
  rw [OUHessian_fderiv_fderiv_stieltjesImComplex_eq_lineSecond hH hA z hz]
  exact OUHessian_deriv_deriv_stieltjes_im_complex_hermitianLine hH hA z hz

/-- The first Wirtinger derivative of the real-valued observable `Im m`, expressed through the
real-coordinate derivatives along `Bmat`. -/
def stieltjesImWirtingerFirst (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) (i j : Idx L W) : ℂ :=
  if i = j then
    (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
      (RBM.Green.Bmat L W i i true) : ℝ)
  else
    (2⁻¹ : ℂ) *
      ((fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
          (RBM.Green.Bmat L W i j true) : ℝ) -
        Complex.I *
          (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
            (RBM.Green.Bmat L W i j false) : ℝ))

/-- The first Wirtinger derivative of `Im m` is the difference of two resolvent-square entries;
the conjugated entry is the corresponding entry of `G*²` for Hermitian `H`. -/
theorem stieltjesImWirtingerFirst_entry_formula
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx L W) :
    stieltjesImWirtingerFirst L W H z i j =
      (Complex.I * (Fintype.card (Idx L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j)) := by
  by_cases hij : i = j
  · subst j
    rw [stieltjesImWirtingerFirst, ite_eq_left rfl, OUHessian_Bmat_diag_true_eq_entryMatrix]
    rw [OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz]
    rw [OUHessian_trace_green_singleEntry]
    let c : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
    have hc : c.im = 0 := by simp [c]
    change ((-c * (RBM.green H z * RBM.green H z) i i).im : ℂ) =
      (Complex.I * c / 2) * ((RBM.green H z * RBM.green H z) i i -
        (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i i))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring
  · rw [stieltjesImWirtingerFirst, ite_eq_right hij,
      OUHessian_Bmat_real_eq_entryMatrices hij, OUHessian_Bmat_imag_eq_entryMatrices hij]
    rw [OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz,
      OUHessian_fderiv_stieltjesIm_apply_matrix hH z hz,
      OUHessian_trace_green_entryPair, OUHessian_trace_green_entryImagPair]
    let c : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
    have hc : c.im = 0 := by simp [c]
    change (2⁻¹ : ℂ) *
      (((-c * ((RBM.green H z * RBM.green H z) j i +
          (RBM.green H z * RBM.green H z) i j)).im : ℂ) -
        Complex.I * ((-c * (Complex.I * ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H z * RBM.green H z) i j))).im : ℂ)) =
      (Complex.I * c / 2) * ((RBM.green H z * RBM.green H z) j i -
        (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring

private theorem OUHessian_green_square_conj_entry
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (i j : Idx L W) :
    (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j) =
      (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i := by
  have hG : RBM.green H ((starRingEnd ℂ) z) = (RBM.green H z)ᴴ := by
    simpa [RBM.Gsig] using (RBM.Gsig_conjTranspose hH z true).symm
  calc
    (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j) =
        ((RBM.green H z * RBM.green H z)ᴴ) j i := by
      simp [Matrix.conjTranspose_apply, Complex.star_def]
    _ = ((RBM.green H z)ᴴ * (RBM.green H z)ᴴ) j i := by rw [Matrix.conjTranspose_mul]
    _ = (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i := by
      rw [← hG]

/-- The first derivative formula in the notation of (2.25), with the conjugate entry written as
the corresponding entry of the adjoint resolvent square. -/
theorem stieltjesImWirtingerFirst_adjoint_formula
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx L W) :
    stieltjesImWirtingerFirst L W H z i j =
      (Complex.I * (Fintype.card (Idx L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i) := by
  rw [stieltjesImWirtingerFirst_entry_formula L W H hH z hz i j,
    OUHessian_green_square_conj_entry L W hH z i j]

/-- The Wirtinger Hessian of one real Stieltjes factor has the exact entry formula that
underlies the paper's `L₁` contraction. -/
theorem wirtSecond_stieltjesIm_entry_formula
    (H : Matrix (Idx L W) (Idx L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx L W) :
    wirtSecond L W (fun K => ((stieltjesN K z).im : ℂ)) H i j =
      ((((Fintype.card (Idx L W) : ℂ)⁻¹) *
        ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
          (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i)).im : ℂ) := by
  by_cases hij : i = j
  · subst j
    have hdiag : (RBM.Green.Bmat L W i i true).IsHermitian :=
      Bmat_isHermitian_of_ne_or L W (Or.inr rfl)
    rw [wirtSecond, ite_eq_left rfl]
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
      ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat L W i i true)
        (RBM.Green.Bmat L W i i true) = _
    rw [OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH hdiag z hz]
    rw [OUHessian_Bmat_diag_true_eq_entryMatrix, OUHessian_trace_green_entryCross]
    simp [Complex.mul_im, mul_assoc]
    ring
  · rw [wirtSecond, ite_eq_right hij]
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
        ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat L W i j true)
          (RBM.Green.Bmat L W i j true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (Idx L W) (Idx L W) ℂ =>
        ((stieltjesN K z).im : ℂ))) H (RBM.Green.Bmat L W i j false)
          (RBM.Green.Bmat L W i j false)) = _
    rw [OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_isHermitian_of_ne_or L W (Or.inl hij)) z hz,
        OUHessian_fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_isHermitian_of_ne_or L W (Or.inl hij)) z hz,
        OUHessian_Bmat_real_eq_entryMatrices hij, OUHessian_Bmat_imag_eq_entryMatrices hij]
    let c : ℂ := (Fintype.card (Idx L W) : ℂ)⁻¹
    let T₁ := (RBM.green H z * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) *
      RBM.green H z * (OUHessian_entryMatrix i j + OUHessian_entryMatrix j i) *
      RBM.green H z).trace
    let T₂ := (RBM.green H z * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) *
      RBM.green H z * (Complex.I • OUHessian_entryMatrix i j -
        Complex.I • OUHessian_entryMatrix j i) *
      RBM.green H z).trace
    have hcIm : c.im = 0 := by simp [c]
    have hIm : (2 * c * T₁).im + (2 * c * T₂).im = (2 * c * (T₁ + T₂)).im := by
      simp [Complex.mul_im, hcIm]
      ring
    have hImC : ((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ) =
        ((2 * c * (T₁ + T₂)).im : ℂ) := by
      exact_mod_cast hIm
    change (1 / 4 : ℝ) •
      (((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ)) = _
    rw [hImC]
    have hT : T₁ + T₂ = 2 * ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
        (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i) := by
      dsimp [T₁, T₂]
      exact OUHessian_trace_green_Bmat_pair_sum hij
    rw [hT]
    simp [Complex.mul_im, hcIm, c]
    ring

end FirstWirtinger

/-! ### The signed resolvent family and the `L₁`, `L₂` kernels -/

section Kernels

section SignedGreen

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signed resolvent family `{G, G*}` at a Hermitian matrix. -/
def signedGreen (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  if σ then RBM.green H z else RBM.green H ((starRingEnd ℂ) z)

end SignedGreen

section KernelDefs

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The centered covariance entry `S°_{ab} = S_{ab} - N⁻¹`, with the matrix dimension
`N = card (Idx L W)`. -/
def centeredVarianceEntry (a b : Idx L W) : ℝ :=
  svar L W a b - (Fintype.card (Idx L W) : ℝ)⁻¹

/-- The deterministic pointwise `L₁` kernel in (2.25). -/
def paperL1Kernel (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx L W) : ℂ)⁻¹ *
      ∑ a : Idx L W, ∑ b : Idx L W,
        ((signedGreen H z σ * signedGreen H z σ) a a) *
          (centeredVarianceEntry L W a b : ℂ) * (signedGreen H z τ) b b‖

/-- The deterministic pointwise `L₂` kernel in (2.25), for two spectral parameters. -/
def paperL2Kernel (H : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx L W) : ℂ)⁻¹ *
      (Fintype.card (Idx L W) : ℂ)⁻¹ *
      ∑ a : Idx L W, ∑ b : Idx L W,
        ((signedGreen H z₁ σ * signedGreen H z₁ σ) a b) *
          (centeredVarianceEntry L W a b : ℂ) *
          ((signedGreen H z₂ τ * signedGreen H z₂ τ) b a)‖

/-- The matrix size is `(W L)²`. -/
theorem card_Idx_eq : Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp [Idx, Z2, ZMod.card, sq]

/-- `S°` is symmetric. -/
theorem centeredVarianceEntry_symm (a b : Idx L W) :
    centeredVarianceEntry L W a b = centeredVarianceEntry L W b a := by
  simp [centeredVarianceEntry, svar_comm L W a b]

/-- `S°` of this file is `Scirc` of `Universality/Pins.lean` after the cast to `ℂ`. -/
theorem centeredVarianceEntry_cast (a b : Idx L W) :
    ((centeredVarianceEntry L W a b : ℝ) : ℂ) = Scirc L W a b := by
  rw [centeredVarianceEntry, Scirc, ← svar_cast_eq_Spaper, card_Idx_eq]
  push_cast
  rfl

/-- `G(z̄) = G(z)^*` for Hermitian `H` and every `z` (the nonsingular-inverse convention needs
no invertibility): `signedGreen` is `gSel`. -/
theorem signedGreen_eq_gSel {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (σ : Bool) : signedGreen H z σ = gSel L W H z σ := by
  cases σ
  · have h := RBM.Gsig_conjTranspose hH z true
    simp only [RBM.Gsig_true, Bool.not_true, RBM.Gsig_false] at h
    simp only [signedGreen, gSel, Bool.false_eq_true, ite_false]
    exact h.symm
  · rfl

/-- `paperL1Kernel` is `L1t` at a Hermitian matrix. -/
theorem paperL1Kernel_eq_L1t {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) : paperL1Kernel L W H z = L1t L W H z := by
  simp only [paperL1Kernel, L1t, signedGreen_eq_gSel L W hH, centeredVarianceEntry_cast,
    card_Idx_eq, Nat.cast_pow]

/-- `paperL2Kernel` is `L2t` at a Hermitian matrix. -/
theorem paperL2Kernel_eq_L2t {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) : paperL2Kernel L W H z₁ z₂ = L2t L W H z₁ z₂ := by
  simp only [paperL2Kernel, L2t, signedGreen_eq_gSel L W hH, centeredVarianceEntry_cast,
    card_Idx_eq, sq]

end KernelDefs

end Kernels

end RBM.Univ

end
