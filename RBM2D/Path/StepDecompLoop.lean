/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import RBM2D.Path.StepDecomp
import RBM2D.Path.Step2Props
import RBM2D.Path.Kernel
import RBM2D.Path.UBounds
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.SpectralWindow
import RBM2D.Hierarchy.Loops

/-!
# The two-loop family is in the Hermitian test class of `StepDecomp.lean` (`d = 2`)

For `0 ≤ u < 1`, `|E| < 2` and a label `a = (p, q) ∈ Z_L² × Z_L²`, the observable

  `Φ_a(M) = gloop L W (blockMat M) (spectralZ E u) (pmLoop p q) = tr (G(z) E_p G(z̄) E_q)`,
  `z = spectralZ E u`,

is a member of the Hermitian test class `HermTestFun` of `Path/StepDecomp.lean`, is real on
Hermitian matrices, and satisfies the (H3) bound of `stepDecomp` with the explicit constant
`C₂ = 6 N η_u⁻⁴`, `N = (W L)²`, `η_u = (1 - u) Im m`.  Then `stepDecomp` and `stepDecomp_Z_subG`
are specialized to this family with the weights
`U b a = (𝒰_{v,w} (b₁,a₁) 𝒰_{v,w} (b₂,a₂)).re`, `ξ = |m|²`, of `Path/Kernel.lean`.

## Main results (namespace `RBM.Path`)

* `hermTestFun_loopPM` : `HermTestFun` for `Φ_a` and the (H3) bound with `C₂ = 6 N η_u⁻⁴`.
* `loopPM_real_of_herm` : `Φ_a` is real on Hermitian matrices.
* `stepDecomp_loopPM` : the decomposition `ξ_b = Z_b + Y_b` and the bounds on `Y_b`, for the
  family `Φ_a` and the weights `U`, whose sign is `ukerNonneg`.
* `stepDecomp_Z_subG_loopPM` : the conditional sub-Gaussian bound of `Z_b` for the family.

## Proof outline

Along a Hermitian line `s ↦ M + s y`, `R' = -R D R` (`hasDerivAt_lineInverse`), so the first jet of
`tr (R₁ E_p R₂ E_q)` is a sum of two words and the second is a sum of three words (each twice), with
four resolvents, two `D` and two `E`.  Each word has norm `≤ η⁻⁴ W⁻⁴ ‖D‖²` and `|tr| ≤ N ‖·‖`.
The derivative of the trace along the line is transported to `fderiv ℝ (fderiv ℝ Φ)` by the
chain rule at Hermitian points, which is why the class is only claimed there.

The block structure is `Z2 L × Fin W × Fin W`, the weights are the `W⁻²` of `Eblk`, and
`N = (LW)²`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### 1. Block coordinates -/

section BlockCoordinates

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem StepDecompLoop_blockMat_add_smul (A C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (A + y • C) = blockMat A + y • blockMat C := by
  ext p q
  simp [blockMat]

/-- `blockMat` as a continuous real-linear map. -/
private def StepDecompLoop_blockCLM (L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx L W) (Idx L W) ℂ →L[ℝ] Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

/-- Reindexing by an equivalence is a star algebra homomorphism of matrix algebras. -/
private def StepDecompLoop_reindexHom {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (e : k ≃ m) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix k k ℂ where
  toFun A := A.submatrix e e
  map_smul' c A := rfl
  map_zero' := rfl
  map_add' A B := rfl
  map_mul' A B := by
    exact (Matrix.submatrix_mul_equiv A B e e e).symm
  map_star' A := by
    exact (Matrix.conjTranspose_submatrix A e e).symm

/-- `blockMat` preserves the operator norm. -/
private theorem StepDecompLoop_norm_blockMat (A : Matrix (Idx L W) (Idx L W) ℂ) :
    ‖blockMat A‖ = ‖A‖ := by
  have hinj : Function.Injective (StepDecompLoop_reindexHom (splitEquiv L W).symm) := by
    intro A B h
    ext i j
    have := congrFun (congrFun h ((splitEquiv L W) i)) ((splitEquiv L W) j)
    change A ((splitEquiv L W).symm ((splitEquiv L W) i))
      ((splitEquiv L W).symm ((splitEquiv L W) j)) =
        B ((splitEquiv L W).symm ((splitEquiv L W) i))
          ((splitEquiv L W).symm ((splitEquiv L W) j)) at this
    simpa using this
  exact NonUnitalStarAlgHom.norm_map _ hinj A

private theorem StepDecompLoop_isHermitian_blockMat {A : Matrix (Idx L W) (Idx L W) ℂ}
    (hA : A.IsHermitian) : (blockMat A).IsHermitian :=
  hA.submatrix _

/-- The `(+,-)` two-loop as the trace of a word of two resolvents and two block insertions. -/
private theorem StepDecompLoop_gloop_eq (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (p q : Z2 L) :
    gloop L W H z (pmLoop p q)
      = Matrix.trace (green H z * Eblk L W p * (green H ((starRingEnd ℂ) z) * Eblk L W q)) :=
  gloop_two (L := L) (W := W) (H := H) (z := z) true false p q

end BlockCoordinates

/-! ### 2. Jets of a word of two resolvents along a line -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace as a continuous real-linear map. -/
private def StepDecompLoop_trCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

private theorem StepDecompLoop_trace_hasDerivAt {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ}
    {t : ℝ} (h : HasDerivAt P P' t) :
    HasDerivAt (fun s => Matrix.trace (P s)) (Matrix.trace P') t := by
  exact (StepDecompLoop_trCLM n).hasFDerivAt.comp_hasDerivAt t h

private theorem StepDecompLoop_word_jet1 {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) (t : ℝ) :
    HasDerivAt (fun s => R₁ s * Ep * (R₂ s * Eq))
      (-(R₁ t * D * R₁ t) * Ep * (R₂ t * Eq) - R₁ t * Ep * (R₂ t * D * R₂ t * Eq)) t := by
  have h := ((h₁ t).mul_const Ep).mul ((h₂ t).mul_const Eq)
  refine h.congr_deriv ?_
  noncomm_ring

private theorem StepDecompLoop_word_jet2 {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) (t : ℝ) :
    HasDerivAt
      (fun s => -(R₁ s * D * R₁ s) * Ep * (R₂ s * Eq) - R₁ s * Ep * (R₂ s * D * R₂ s * Eq))
      ((R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq)
          + R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq))
        + (R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq)
          + R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq))
        + (R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq)
          + R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq))) t := by
  have hQ1 := ((h₁ t).mul_const D).mul (h₁ t)
  have hQ2 := ((h₂ t).mul_const D).mul (h₂ t)
  have hA := (hQ1.neg.mul_const Ep).mul ((h₂ t).mul_const Eq)
  have hB := ((h₁ t).mul_const Ep).mul (hQ2.mul_const Eq)
  have h := hA.sub hB
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.neg_apply]
  noncomm_ring

private theorem StepDecompLoop_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem StepDecompLoop_nadd {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A + B‖ ≤ a + b :=
  (norm_add_le _ _).trans (add_le_add hA hB)

/-- The first and second derivative of `s ↦ tr (R₁ E_p R₂ E_q)` along a line, where
`R_i' = -R_i D R_i` and `‖R_i‖ ≤ K`, `‖E_p‖, ‖E_q‖ ≤ e`: the second one is bounded by
`|n| · 6 K⁴ e² ‖D‖²`. -/
private theorem StepDecompLoop_word_jets {R₁ R₂ : ℝ → Matrix n n ℂ} {D Ep Eq : Matrix n n ℂ}
    (h₁ : ∀ t, HasDerivAt R₁ (-(R₁ t * D * R₁ t)) t)
    (h₂ : ∀ t, HasDerivAt R₂ (-(R₂ t * D * R₂ t)) t) {K e : ℝ}
    (hK₁ : ∀ t, ‖R₁ t‖ ≤ K) (hK₂ : ∀ t, ‖R₂ t‖ ≤ K) (hEp : ‖Ep‖ ≤ e) (hEq : ‖Eq‖ ≤ e) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t, HasDerivAt (fun s => Matrix.trace (R₁ s * Ep * (R₂ s * Eq))) (φ₁ t) t) ∧
      (∀ t, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t, ‖φ₁ t‖ ≤ (Fintype.card n : ℝ) * (2 * K ^ 3 * e ^ 2 * ‖D‖)) ∧
      ∀ t, ‖φ₂ t‖ ≤ (Fintype.card n : ℝ) * (6 * K ^ 4 * e ^ 2 * ‖D‖ ^ 2) := by
  refine ⟨fun t => Matrix.trace (-(R₁ t * D * R₁ t) * Ep * (R₂ t * Eq)
      - R₁ t * Ep * (R₂ t * D * R₂ t * Eq)),
    fun t => Matrix.trace ((R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq)
          + R₁ t * D * R₁ t * D * R₁ t * Ep * (R₂ t * Eq))
        + (R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq)
          + R₁ t * D * R₁ t * Ep * (R₂ t * D * R₂ t * Eq))
        + (R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq)
          + R₁ t * Ep * (R₂ t * D * R₂ t * D * R₂ t * Eq))), ?_, ?_, ?_, ?_⟩
  · intro t
    exact StepDecompLoop_trace_hasDerivAt (StepDecompLoop_word_jet1 h₁ h₂ t)
  · intro t
    exact StepDecompLoop_trace_hasDerivAt (StepDecompLoop_word_jet2 h₁ h₂ t)
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hR1 := hK₁ t
    have hR2 := hK₂ t
    have hD : ‖D‖ ≤ ‖D‖ := le_rfl
    have hQ : ‖-(R₁ t * D * R₁ t)‖ ≤ K * ‖D‖ * K := by
      rw [norm_neg]
      exact StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hD) hR1
    have w1 := StepDecompLoop_nmul (StepDecompLoop_nmul hQ hEp) (StepDecompLoop_nmul hR2 hEq)
    have w2 := StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hEq)
    have h := (norm_sub_le _ _).trans (add_le_add w1 w2)
    refine h.trans (le_of_eq ?_)
    ring
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hR1 := hK₁ t
    have hR2 := hK₂ t
    have hD : ‖D‖ ≤ ‖D‖ := le_rfl
    have w1 := StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hD) hR1) hD) hR1) hEp)
      (StepDecompLoop_nmul hR2 hEq)
    have w2 := StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
      (StepDecompLoop_nmul hR1 hD) hR1) hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hEq)
    have w3 := StepDecompLoop_nmul (StepDecompLoop_nmul hR1 hEp)
      (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul
        (StepDecompLoop_nmul (StepDecompLoop_nmul hR2 hD) hR2) hD) hR2) hEq)
    have h := StepDecompLoop_nadd
      (StepDecompLoop_nadd (StepDecompLoop_nadd w1 w1) (StepDecompLoop_nadd w2 w2))
      (StepDecompLoop_nadd w3 w3)
    refine h.trans (le_of_eq ?_)
    ring

end Words

/-! ### 3. Lines through Hermitian points -/

section Lines

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent along a Hermitian line has derivative `-G D G`. -/
private theorem StepDecompLoop_hasDerivAt_green {H D : Matrix n n ℂ} (hH : H.IsHermitian)
    (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (H + (s : ℂ) • D) z)
      (-(green (H + (t : ℂ) • D) z * D * green (H + (t : ℂ) • D) z)) t := by
  have hgr : ∀ s : ℝ, green (H + (s : ℂ) • D) z
      = Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    change (H + (s : ℂ) • D - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    have he : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D
        = (H + (s : ℂ) • D) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hH hD s) hz
  have h := hasDerivAt_lineInverse hU t
  simp only [← hgr] at h
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `Φ` is `C²` at Hermitian points and its derivative along a Hermitian line
`s ↦ M + s y` is `φ₁`, then `fderiv ℝ Φ (M + t y) y = φ₁ t`. -/
private theorem StepDecompLoop_fderiv_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t) (t : ℝ) :
    φ₁ t = fderiv ℝ Φ (M + (t : ℂ) • y) y := by
  have hdiff : DifferentiableAt ℝ Φ (M + (t : ℂ) • y) :=
    ((hΦ _ (isHermitian_add_realSmul hM hy t)).differentiableAt (by norm_num))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line M y t)
  exact (h₀ t).unique h

/-- If `Φ` is `C²` at Hermitian points and its first two derivatives along a Hermitian line
`s ↦ M + s y` are `φ₁`, `φ₂`, then `fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0`. -/
private theorem StepDecompLoop_fderiv2_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ φ₂ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t)
    (h₁ : ∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) :
    fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M + (s : ℂ) • y) y t := fun t =>
    hasDerivAt_line M y t
  have hφ₁ := StepDecompLoop_fderiv_of_line hΦ hM hy h₀
  have hfd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) M) M :=
    (((hΦ M hM).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hpt : M + ((0 : ℝ) : ℂ) • y = M := by simp
  have hΘ : HasFDerivAt (fun N : Matrix ι ι ℂ => fderiv ℝ Φ N y)
      ((ContinuousLinearMap.apply ℝ ℂ y).comp (fderiv ℝ (fderiv ℝ Φ) M)) M :=
    (ContinuousLinearMap.apply ℝ ℂ y).hasFDerivAt.comp M hfd
  have hev := hΘ.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hpt.symm
  have hfun : (fun t : ℝ => fderiv ℝ Φ (M + (t : ℂ) • y) y) = φ₁ := by
    funext t; exact (hφ₁ t).symm
  have hev' : HasDerivAt φ₁ (fderiv ℝ (fderiv ℝ Φ) M y y) 0 := by
    rw [← hfun]
    exact hev
  exact hev'.unique (h₁ 0)

end Lines

/-! ### 4. The observable: smoothness, bound, reality, second derivative -/

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible. -/
private theorem StepDecompLoop_contDiffAt_green {w : ℂ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hu : IsUnit (blockMat M - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => green (blockMat M') w) M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
      blockMat M' - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :=
    ((StepDecompLoop_blockCLM L W).contDiff).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (BlockIndex L W) (BlockIndex L W) ℂ))
      (blockMat M - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx L W) (Idx L W) ℂ => green (blockMat M') w)
      = Ring.inverse ∘ (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
        blockMat M' - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    funext M'
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  exact h

/-- (H1) for the two-loop observable: `C²` at every Hermitian point. -/
private theorem StepDecompLoop_contDiffAt_loopPM {z : ℂ} (hz : z.im ≠ 0) (p q : Z2 L)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2
      (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z (pmLoop p q)) M := by
  have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
  have hMb : (blockMat M).IsHermitian := StepDecompLoop_isHermitian_blockMat hM
  have hG₁ := StepDecompLoop_contDiffAt_green (L := L) (W := W)
    (isUnit_sub_smul_one_of_im_ne_zero hMb hz)
  have hG₂ := StepDecompLoop_contDiffAt_green (L := L) (W := W)
    (isUnit_sub_smul_one_of_im_ne_zero hMb hz')
  have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx L W) (Idx L W) ℂ => Eblk L W p) M :=
    contDiffAt_const
  have hEq : ContDiffAt ℝ 2 (fun _ : Matrix (Idx L W) (Idx L W) ℂ => Eblk L W q) M :=
    contDiffAt_const
  have hprod := (hG₁.mul hEp).mul (hG₂.mul hEq)
  have h := (StepDecompLoop_trCLM (BlockIndex L W)).contDiff.contDiffAt.comp M hprod
  have hfun : (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z (pmLoop p q))
      = (StepDecompLoop_trCLM (BlockIndex L W)) ∘ (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
        green (blockMat M') z * Eblk L W p * (green (blockMat M') ((starRingEnd ℂ) z) * Eblk L W q))
      := by
    funext M'
    exact StepDecompLoop_gloop_eq _ _ p q
  rw [hfun]
  exact h

/-- The first two derivatives of the two-loop observable along a Hermitian line, with their
bounds `|φ₁| ≤ N · 2 η⁻³ (W⁻²)² ‖y‖` and `|φ₂| ≤ N · 6 η⁻⁴ (W⁻²)² ‖y‖²`. -/
private theorem StepDecompLoop_line_jets {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (p q : Z2 L) {M y : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun s : ℝ =>
        gloop L W (blockMat (M + (s : ℂ) • y)) z (pmLoop p q)) (φ₁ t) t) ∧
      (∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t : ℝ, ‖φ₁ t‖ ≤ (((L * W) ^ 2 : ℕ) : ℝ) * (2 * η⁻¹ ^ 3 * ((W : ℝ)⁻¹ ^ 2) ^ 2 * ‖y‖)) ∧
      (∀ t : ℝ, ‖φ₂ t‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) * (6 * η⁻¹ ^ 4 * ((W : ℝ)⁻¹ ^ 2) ^ 2 * ‖y‖ ^ 2)) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz0
  have hzc : η ≤ |((starRingEnd ℂ) z).im| := by simpa using hz
  have hMb : (blockMat M).IsHermitian := StepDecompLoop_isHermitian_blockMat hM
  have hyb : (blockMat y).IsHermitian := StepDecompLoop_isHermitian_blockMat hy
  obtain ⟨φ₁, φ₂, hd1, hd2, hb1, hb2⟩ := StepDecompLoop_word_jets
    (R₁ := fun s : ℝ => green (blockMat M + (s : ℂ) • blockMat y) z)
    (R₂ := fun s : ℝ => green (blockMat M + (s : ℂ) • blockMat y) ((starRingEnd ℂ) z))
    (D := blockMat y) (Ep := Eblk L W p) (Eq := Eblk L W q) (K := η⁻¹) (e := (W : ℝ)⁻¹ ^ 2)
    (StepDecompLoop_hasDerivAt_green hMb hyb hz0) (StepDecompLoop_hasDerivAt_green hMb hyb hz')
    (fun t => norm_green_le (isHermitian_add_realSmul hMb hyb t) hη hz)
    (fun t => norm_green_le (isHermitian_add_realSmul hMb hyb t) hη hzc)
    (norm_Eblk_le_inv_W_sq L W p) (norm_Eblk_le_inv_W_sq L W q)
  have hDn : ‖blockMat y‖ ≤ ‖y‖ := le_of_eq (StepDecompLoop_norm_blockMat y)
  have hD2 : ‖blockMat y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [StepDecompLoop_norm_blockMat]
  refine ⟨φ₁, φ₂, ?_, hd2, ?_, ?_⟩
  · intro t
    have hfun : (fun s : ℝ => gloop L W (blockMat (M + (s : ℂ) • y)) z (pmLoop p q))
        = fun s : ℝ => Matrix.trace
          (green (blockMat M + (s : ℂ) • blockMat y) z * Eblk L W p
            * (green (blockMat M + (s : ℂ) • blockMat y) ((starRingEnd ℂ) z) * Eblk L W q)) := by
      funext s
      rw [StepDecompLoop_blockMat_add_smul, StepDecompLoop_gloop_eq]
    rw [hfun]
    exact hd1 t
  · intro t
    rw [card_BlockIndex] at hb1
    refine (hb1 t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hK : (0 : ℝ) ≤ 2 * η⁻¹ ^ 3 * ((W : ℝ)⁻¹ ^ 2) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hDn hK
  · intro t
    rw [card_BlockIndex] at hb2
    refine (hb2 t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hK : (0 : ℝ) ≤ 6 * η⁻¹ ^ 4 * ((W : ℝ)⁻¹ ^ 2) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hD2 hK

/-- (H3), before the constant is simplified: the second derivative along a Hermitian line. -/
private theorem StepDecompLoop_second_deriv_bound {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (p q : Z2 L) {M y : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ
        (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z (pmLoop p q))) M y y‖
      ≤ (((L * W) ^ 2 : ℕ) : ℝ) * (6 * η⁻¹ ^ 4 * ((W : ℝ)⁻¹ ^ 2) ^ 2 * ‖y‖ ^ 2) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  obtain ⟨φ₁, φ₂, h₀, hd2, -, hb⟩ := StepDecompLoop_line_jets (L := L) (W := W) hη hz p q hM hy
  rw [StepDecompLoop_fderiv2_of_line
    (fun M' hM' => StepDecompLoop_contDiffAt_loopPM (L := L) (W := W) hz0 p q hM') hM hy h₀ hd2]
  exact hb 0

end Observable

/-! ### 5. The four targets -/

section Targets

/-- **The two-loop family is in the Hermitian test class, with `C₂ = 6 N η_u⁻⁴`.**  For
`0 ≤ u < 1`, `|E| < 2` and a label `a = (p, q)`,
`M ↦ gloop (blockMat M) (spectralZ E u) (pmLoop p q)` satisfies `HermTestFun` (`C²` and bounded at
Hermitian points) and the (H3) bound of `stepDecomp` (`hC₂`) with `C₂ = 6 N η_u⁻⁴`,
`N = (W L)²`, `η_u = (1 - u) Im m`.  (`HermTestFun` has no `C₂` field.  The proof gives the sharper
constant
`6 N η_u⁻⁴ W⁻⁴`.) -/
theorem hermTestFun_loopPM (d : Sizes) (n : ℕ) (E u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hE : |E| < 2) (a : Z2 (d.L n) × Z2 (d.L n)) :
    HermTestFun d n
        (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
      ∧ ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
          M.IsHermitian → y.IsHermitian →
          ‖fderiv ℝ (fderiv ℝ
              (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
                gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))) M y y‖
            ≤ 6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2 := by
  have _ := hu0
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (spectralM E).im := mul_pos (by linarith) (spectralM_im_pos hE)
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hz0 : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]; exact hpos.ne'
  have hwf : (pmLoop a.1 a.2).WF := rfl
  refine ⟨⟨fun M hM => StepDecompLoop_contDiffAt_loopPM hz0 a.1 a.2 hM,
    ⟨_, fun M hM => norm_gloop_le_crude (d.L n) (d.W n)
      (StepDecompLoop_isHermitian_blockMat hM) hη hz (pmLoop a.1 a.2) hwf⟩⟩, ?_⟩
  intro M y hM hy
  have h := StepDecompLoop_second_deriv_bound (L := d.L n) (W := d.W n) hη hz a.1 a.2 hM hy
  refine h.trans ?_
  have hN : (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) = (Sizes.size d n : ℝ) := by
    rw [Sizes.size, mul_comm]
  rw [hN]
  have hW : ((d.W n : ℝ)⁻¹ ^ 2) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (d.W n : ℝ) := Nat.one_le_cast.2 (d.W_pos n)
    have h2 : ((d.W n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : (0 : ℝ) ≤ ((d.W n : ℝ))⁻¹ := by positivity
    exact pow_le_one₀ (by positivity) (pow_le_one₀ h3 h2)
  have hNn : (0 : ℝ) ≤ (Sizes.size d n : ℝ) := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ (etaT E u)⁻¹ ^ 4 := by positivity
  calc (Sizes.size d n : ℝ) * (6 * (etaT E u)⁻¹ ^ 4 * ((d.W n : ℝ)⁻¹ ^ 2) ^ 2 * ‖y‖ ^ 2)
      = (6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2) * ((d.W n : ℝ)⁻¹ ^ 2) ^ 2 := by
        ring
    _ ≤ (6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = 6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2 := mul_one _

/-- **`hReal` for the two-loop family.**  The `(+,-)` two-loop `tr (G E_p G̅ E_q)` of a Hermitian
matrix is real, with no hypothesis on `E` or `u`.  Proof: `gloop_two_plus_minus_nonneg`, which
uses the sign pattern `(+,-)` of `pmLoop`. -/
theorem loopPM_real_of_herm (d : Sizes) (n : ℕ) (E u : ℝ) (a : Z2 (d.L n) × Z2 (d.L n))
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian) :
    (gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2)).im = 0 := by
  obtain ⟨r, -, hr⟩ := gloop_two_plus_minus_nonneg (L := d.L n) (W := d.W n)
    (H := blockMat M) (z := spectralZ E u) (StepDecompLoop_isHermitian_blockMat hM) a.1 a.2
  change (gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u)
    ⟨[true, false], [a.1, a.2]⟩).im = 0
  rw [hr]
  exact Complex.ofReal_im r

/-- The weights `U b a = (𝒰_{v,w} (b₁,a₁) 𝒰_{v,w} (b₂,a₂)).re`, `ξ = |m|²`, are nonnegative. -/
private theorem StepDecompLoop_weight_nonneg (d : Sizes) (n : ℕ) (E : ℝ) (hE : |E| < 2)
    (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) (b a : Z2 (d.L n) × Z2 (d.L n)) :
    0 ≤ (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re := by
  have hξ : Complex.normSq (spectralM E) = 1 := normSqSpectralMOne E hE.le
  have h1 := ukerNonneg (d.L n) (d.three_le_L n) (Complex.normSq (spectralM E)) v w
    (Complex.normSq_nonneg _) hv hvw (by rw [hξ]; linarith) b.1 a.1
  have h2 := ukerNonneg (d.L n) (d.three_le_L n) (Complex.normSq (spectralM E)) v w
    (Complex.normSq_nonneg _) hv hvw (by rw [hξ]; linarith) b.2 a.2
  rw [Complex.mul_re, h1.1, h2.1]
  nlinarith [h1.2, h2.2]

/-- **`stepDecomp` and `stepDecomp_Y_sq` for the two-loop family.**  With `Φ_a` the two-loop
observable, `C₂ = 6 N η_u⁻⁴` and the weights `U b a = (𝒰_{v,w} 𝒰_{v,w}).re`, `ξ = |m|²`: the
decomposition `ξ_b = Z_b + Y_b`, the measurability of `Ab`, the pathwise bound and the vanishing
conditional mean of `Y_b`, and the `L²` bound of `Y_b`.  The signs `0 ≤ v ≤ w < 1` of the
propagator times are what `ukerNonneg` needs to replace `∑ |U b a|` by `∑ U b a`; the fifth
conjunct is `stepDecomp_Y_sq`. -/
theorem stepDecomp_loopPM (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    (hΔ : 0 ≤ gridStep s t K n) (b : Z2 (d.L n) × Z2 (d.L n)) :
    (∀ ω, stepXi d s t K n j
          (fun (a : Z2 (d.L n) × Z2 (d.L n))
              (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
          (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω
        = (stepZ d s t K n j
            (fun (a : Z2 (d.L n) × Z2 (d.L n))
                (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
              gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
            (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)
            b ω : ℂ)
          + stepY d s t K n j
            (fun (a : Z2 (d.L n) × Z2 (d.L n))
                (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
              gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
            (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)
            b ω)
      ∧ Measurable[filt d j] (fun ω => Ab d s t K n j
          (fun (a : Z2 (d.L n) × Z2 (d.L n))
              (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
          (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω)
      ∧ (∀ᵐ ω ∂(pathP d), ‖stepY d s t K n j
            (fun (a : Z2 (d.L n) × Z2 (d.L n))
                (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
              gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
            (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω‖
          ≤ (∑ a : Z2 (d.L n) × Z2 (d.L n),
                (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)
              * ((6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2) * gridStep s t K n)
              * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2
            + (pathP d)[fun ω' => (∑ a : Z2 (d.L n) × Z2 (d.L n),
                (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)
                * ((6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat d n (ω' (j + 1))‖ ^ 2 | filt d j] ω)
      ∧ ((pathP d)[stepY d s t K n j
            (fun (a : Z2 (d.L n) × Z2 (d.L n))
                (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
              gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
            (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b
          | filt d j] =ᵐ[pathP d] (fun _ => (0 : ℂ)))
      ∧ ∫ ω, ‖stepY d s t K n j
            (fun (a : Z2 (d.L n) × Z2 (d.L n))
                (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
              gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
            (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω‖ ^ 2
            ∂(pathP d)
          ≤ 4 * ((∑ a : Z2 (d.L n) × Z2 (d.L n),
                (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
                  * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)
              * (6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2)) ^ 2
            * (gridStep s t K n) ^ 2 * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := by
  have hΦ := fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).1
  have hC := fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).2
  have hReal : ∀ (a : Z2 (d.L n) × Z2 (d.L n))
      (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), A.IsHermitian →
      ((fun (a : Z2 (d.L n) × Z2 (d.L n))
          (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
        gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2)) a A).im = 0 :=
    fun a A hA => loopPM_real_of_herm d n E u a hA
  have hIntReal := stepDecomp_integrable_stepZ d s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b
  obtain ⟨h1, h2, h3, h4⟩ := stepDecomp d s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b hIntReal
  have h5 := stepDecomp_Y_sq d s t K n j hΦ hReal hC hΔ
    (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b hIntReal
  have hsum : (∑ a : Z2 (d.L n) × Z2 (d.L n),
      |(ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re|)
      = ∑ a : Z2 (d.L n) × Z2 (d.L n),
        (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
          * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re :=
    Finset.sum_congr rfl fun a _ =>
      abs_of_nonneg (StepDecompLoop_weight_nonneg d n E hE v w hv hvw hw b a)
  simp only [hsum] at h3 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`stepDecomp_Z_subG` for the two-loop family**: for `S ∈ F_j` on which
`Δ · linTrVar n (Ab ω) ≤ c`, the indicator of `S` times `Z_b` is conditionally sub-Gaussian with
variance proxy `c`.  `v`, `w` are unconstrained: `stepDecomp_Z_subG` uses no property of the
weights. -/
theorem stepDecomp_Z_subG_loopPM (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (S : Set (PathΩ d)) (hS : MeasurableSet[filt d j] S) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ S, gridStep s t K n * linTrVar n (Ab d s t K n j
          (fun (a : Z2 (d.L n) × Z2 (d.L n))
              (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
          (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => S.indicator (fun ω => stepZ d s t K n j
          (fun (a : Z2 (d.L n) × Z2 (d.L n))
              (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2))
          (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω) ω)
      ⟨c, hc⟩ (pathP d) :=
  stepDecomp_Z_subG d s t K n j (fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).1)
    (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b S hS c hc hbound

end Targets

end RBM.Path
