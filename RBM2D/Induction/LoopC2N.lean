/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import RBM2D.Induction.GridGoodN
import RBM2D.Path.StepDecomp
import RBM2D.Path.Step2Props
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.SpectralWindow
import RBM2D.Hierarchy.Loops

/-!
# The general-length `C²` bound of the loop observables (`d = 2`)

The statement `HermTestFunLoopN` of `RBM2D.Induction.GridGoodN` (section `TestClass`) says: for every loop length `k ≥ 1`, every `n`,
`|E| < 2`, `0 ≤ u < 1`, every sign vector `σ : Fin k → Bool` and label vector
`b : Fin k → Z_L²`, the observable

  `Φ(M) = gloop L W (blockMat M) (spectralZ E u) (loopOf σ b) = tr ∏_{i=1}^k (G_{σ_i}(z_u) E_{b_i})`

is in the Hermitian test class `HermTestFun` of `RBM2D.Path.StepDecomp`, and at Hermitian `M, y`

  `‖∂²Φ(M)[y, y]‖ ≤ k (k + 1) · N · η_u^{-(k+2)} · ‖y‖²`,   `N = (W L)²`, `η_u = (1 - u) Im m`.

## Main result (namespace `RBM.Ind`)

* `hermTestFunLoopN (d : Sizes) : HermTestFunLoopN d` — the statement, with no added
  hypothesis.

## Proof

Generalisation of the proof `hermTestFun_loopPM` of the case `k = 2`, `σ = (+,-)`
(`RBM2D.Path.StepDecompLoop`), whose private jets (`blockCLM`, `norm_blockMat`,
`trCLM`, `hasDerivAt_green`, `fderiv(2)_of_line`, `contDiffAt_green`, `line_jets`) are re-proved here
as private `LoopC2N_` helpers; the two-resolvent `word_jets` is replaced by an
induction on the word (`LoopC2N_word_jets`).  Along the Hermitian line `s ↦ M + s y`, with
`H = blockMat M`, `D = blockMat y`, `R_i(s) = G_{σ_i}(H + s D)`, `R_i' = -R_i D R_i`:

  `P_l = ∏_{i ∈ l} (R_i E_i)`,   `‖R_i‖ ≤ K = η⁻¹`,   `‖E_b‖ ≤ 1`,
  `‖P_l‖ ≤ K^m`,  `‖P_l'‖ ≤ m K^{m+1} ‖D‖`,  `‖P_l''‖ ≤ m (m + 1) K^{m+2} ‖D‖²`  (`m = |l|`),

by the Leibniz rule `(R E Q)'' = R'' E Q + 2 R' E Q' + R E Q''`, `R'' = 2 R D R D R`, which gives
the step `C₂(m+1) = K C₂(m) + 2 K² C₁(m) + 2 K³ C₀(m)`, `m (m + 1) + 2 m + 2 = (m + 1) (m + 2)`.
The trace costs `‖tr A‖ ≤ card · ‖A‖` with `card (BlockIndex L W) = (L W)² = size n`
(`Sizes.size`); `‖blockMat y‖ = ‖y‖`; `‖E_b‖ ≤ W⁻² ≤ 1`.  The `HermTestFun` fields come from
`ContDiffAt` of the resolvent product at `Im z_u ≠ 0` (`spectralZ_im`, `etaT_pos`) and the crude
envelope `norm_gloop_le_crude`.

The induction over the `List.foldr` word parallels the one-dimensional formalization, whose
constants `B^n, n B^n, n² B^n` with `B = 2 (1 + η⁻¹)³` are not the `k (k + 1)` of the statement.

Every helper is `private` and carries the prefix `LoopC2N_`.
-/

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Gauss RBM.Path
open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### 1. Block coordinates -/

section BlockCoordinates

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem LoopC2N_blockMat_add_smul (A C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (A + y • C) = blockMat A + y • blockMat C := by
  ext p q
  simp [blockMat]

/-- `blockMat` as a continuous real-linear map. -/
private def LoopC2N_blockCLM (L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx L W) (Idx L W) ℂ →L[ℝ] Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

/-- Reindexing by an equivalence is a star algebra homomorphism of matrix algebras. -/
private def LoopC2N_reindexHom {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
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
private theorem LoopC2N_norm_blockMat (A : Matrix (Idx L W) (Idx L W) ℂ) :
    ‖blockMat A‖ = ‖A‖ := by
  have hinj : Function.Injective (LoopC2N_reindexHom (splitEquiv L W).symm) := by
    intro A B h
    ext i j
    have := congrFun (congrFun h ((splitEquiv L W) i)) ((splitEquiv L W) j)
    change A ((splitEquiv L W).symm ((splitEquiv L W) i))
      ((splitEquiv L W).symm ((splitEquiv L W) j)) =
        B ((splitEquiv L W).symm ((splitEquiv L W) i))
          ((splitEquiv L W).symm ((splitEquiv L W) j)) at this
    simpa using this
  exact NonUnitalStarAlgHom.norm_map _ hinj A

private theorem LoopC2N_isHermitian_blockMat {A : Matrix (Idx L W) (Idx L W) ℂ}
    (hA : A.IsHermitian) : (blockMat A).IsHermitian :=
  hA.submatrix _

end BlockCoordinates

/-! ### 2. Jets of a word of resolvents and block insertions along a line -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem LoopC2N_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem LoopC2N_nadd {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a)
    (hB : ‖B‖ ≤ b) : ‖A + B‖ ≤ a + b :=
  (norm_add_le _ _).trans (add_le_add hA hB)

/-- The word `∏_{a ∈ l} (R a s * E a)` as a function of the line parameter `s`. -/
private def LoopC2N_word {α : Type*} (R : α → ℝ → Matrix n n ℂ) (E : α → Matrix n n ℂ)
    (l : List α) (s : ℝ) : Matrix n n ℂ :=
  l.foldr (fun a M => R a s * E a * M) 1

/-- **The Leibniz induction over the word.**  Let `R a s` be resolvent-type matrices with
`(R a)' = -R a D R a` and `‖R a s‖ ≤ K`, and `E a` matrices with `‖E a‖ ≤ 1`.  Then the word
`P_l(s) = ∏_{a ∈ l} (R a s * E a)` has two derivatives along `s`, with
`‖P_l‖ ≤ K^m`, `‖P_l'‖ ≤ m K^{m+1} ‖D‖`, `‖P_l''‖ ≤ m (m + 1) K^{m+2} ‖D‖²`, `m = l.length`. -/
private theorem LoopC2N_word_jets [Nonempty n] {α : Type*}
    {R : α → ℝ → Matrix n n ℂ} {E : α → Matrix n n ℂ} {D : Matrix n n ℂ}
    (hR : ∀ a t, HasDerivAt (R a) (-(R a t * D * R a t)) t) {K : ℝ}
    (hK : ∀ a t, ‖R a t‖ ≤ K) (hE : ∀ a, ‖E a‖ ≤ 1) (l : List α) :
    ∃ P1 P2 : ℝ → Matrix n n ℂ,
      (∀ t, HasDerivAt (LoopC2N_word R E l) (P1 t) t) ∧
      (∀ t, HasDerivAt P1 (P2 t) t) ∧
      (∀ t, ‖LoopC2N_word R E l t‖ ≤ K ^ l.length) ∧
      (∀ t, ‖P1 t‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * ‖D‖) ∧
      (∀ t, ‖P2 t‖ ≤
        (l.length : ℝ) * ((l.length : ℝ) + 1) * K ^ (l.length + 2) * ‖D‖ ^ 2) := by
  induction l with
  | nil =>
    refine ⟨fun _ => 0, fun _ => 0, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
      fun t => ?_⟩
    · exact hasDerivAt_const t (1 : Matrix n n ℂ)
    · exact hasDerivAt_const t (0 : Matrix n n ℂ)
    · simp [LoopC2N_word]
    · simp
    · simp
  | cons a l ih =>
    obtain ⟨Q1, Q2, hQ1, hQ2, hb0, hb1, hb2⟩ := ih
    have hRDR : ∀ t, HasDerivAt (fun s => R a s * D * R a s)
        (-(R a t * D * R a t) * D * R a t + R a t * D * (-(R a t * D * R a t))) t := fun t =>
      ((hR a t).mul_const D).mul (hR a t)
    refine ⟨fun t => -(R a t * D * R a t) * E a * LoopC2N_word R E l t + R a t * E a * Q1 t,
      fun t => ((R a t * D * R a t) * D * R a t + R a t * D * (R a t * D * R a t))
          * E a * LoopC2N_word R E l t
        + (-(R a t * D * R a t) * E a * Q1 t
          + (-(R a t * D * R a t) * E a * Q1 t + R a t * E a * Q2 t)),
      fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact ((hR a t).mul_const (E a)).mul (hQ1 t)
    · have hT1 := (((hRDR t).neg).mul_const (E a)).mul (hQ1 t)
      have hT2 := ((hR a t).mul_const (E a)).mul (hQ2 t)
      have h := hT1.add hT2
      refine h.congr_deriv ?_
      simp only [Pi.neg_apply]
      noncomm_ring
    · have hr := hK a t
      have h := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb0 t)
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      ring
    · have hr := hK a t
      have hX : ‖R a t * D * R a t‖ ≤ K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hr
      have hXn : ‖-(R a t * D * R a t)‖ ≤ K * ‖D‖ * K := by rwa [norm_neg]
      have w1 := LoopC2N_nmul (LoopC2N_nmul hXn (hE a)) (hb0 t)
      have w2 := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb1 t)
      have h := LoopC2N_nadd w1 w2
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      push_cast
      ring
    · have hr := hK a t
      have hX : ‖R a t * D * R a t‖ ≤ K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hr
      have hXn : ‖-(R a t * D * R a t)‖ ≤ K * ‖D‖ * K := by rwa [norm_neg]
      have hXDR : ‖(R a t * D * R a t) * D * R a t‖ ≤ K * ‖D‖ * K * ‖D‖ * K :=
        LoopC2N_nmul (LoopC2N_nmul hX le_rfl) hr
      have hRDX : ‖R a t * D * (R a t * D * R a t)‖ ≤ K * ‖D‖ * (K * ‖D‖ * K) :=
        LoopC2N_nmul (LoopC2N_nmul hr le_rfl) hX
      have w1 := LoopC2N_nmul (LoopC2N_nmul (LoopC2N_nadd hXDR hRDX) (hE a)) (hb0 t)
      have w2 := LoopC2N_nmul (LoopC2N_nmul hXn (hE a)) (hb1 t)
      have w4 := LoopC2N_nmul (LoopC2N_nmul hr (hE a)) (hb2 t)
      have h := LoopC2N_nadd w1 (LoopC2N_nadd w2 (LoopC2N_nadd w2 w4))
      refine h.trans (le_of_eq ?_)
      simp only [List.length_cons]
      push_cast
      ring

end Words

/-! ### 3. Lines through Hermitian points -/

section Lines

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace as a continuous real-linear map. -/
private def LoopC2N_trCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

private theorem LoopC2N_trace_hasDerivAt {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ}
    {t : ℝ} (h : HasDerivAt P P' t) :
    HasDerivAt (fun s => Matrix.trace (P s)) (Matrix.trace P') t := by
  exact (LoopC2N_trCLM n).hasFDerivAt.comp_hasDerivAt t h

/-- The resolvent along a Hermitian line has derivative `-G D G`. -/
private theorem LoopC2N_hasDerivAt_green {H D : Matrix n n ℂ} (hH : H.IsHermitian)
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
    exact RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hH hD s) hz
  have h := hasDerivAt_lineInverse hU t
  simp only [← hgr] at h
  exact h

/-- The signed resolvent `G_σ = G(z)` or `G(z̄)` along a Hermitian line has derivative
`-G_σ D G_σ`. -/
private theorem LoopC2N_hasDerivAt_Gsig {H D : Matrix n n ℂ} (hH : H.IsHermitian)
    (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gsig (H + (s : ℂ) • D) z σ)
      (-(Gsig (H + (t : ℂ) • D) z σ * D * Gsig (H + (t : ℂ) • D) z σ)) t := by
  cases σ
  · exact LoopC2N_hasDerivAt_green hH hD (by simpa using hz) t
  · exact LoopC2N_hasDerivAt_green hH hD hz t

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `Φ` is `C²` at Hermitian points and its derivative along a Hermitian line
`s ↦ M + s y` is `φ₁`, then `fderiv ℝ Φ (M + t y) y = φ₁ t`. -/
private theorem LoopC2N_fderiv_of_line {Φ : Matrix ι ι ℂ → ℂ}
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
private theorem LoopC2N_fderiv2_of_line {Φ : Matrix ι ι ℂ → ℂ}
    (hΦ : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {M y : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) {φ₁ φ₂ : ℝ → ℂ}
    (h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • y)) (φ₁ t) t)
    (h₁ : ∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) :
    fderiv ℝ (fderiv ℝ Φ) M y y = φ₂ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M + (s : ℂ) • y) y t := fun t =>
    hasDerivAt_line M y t
  have hφ₁ := LoopC2N_fderiv_of_line hΦ hM hy h₀
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

/-! ### 4. The observable: smoothness, second derivative along a line -/

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible. -/
private theorem LoopC2N_contDiffAt_green {w : ℂ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hu : IsUnit (blockMat M - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => green (blockMat M') w) M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
      blockMat M' - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :=
    ((LoopC2N_blockCLM L W).contDiff).sub contDiff_const
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

/-- The signed resolvent factor `G_σ(blockMat M')` is `C²` at Hermitian `M`. -/
private theorem LoopC2N_contDiffAt_Gsig {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => Gsig (blockMat M') z σ) M := by
  have hMb : (blockMat M).IsHermitian := LoopC2N_isHermitian_blockMat hM
  cases σ
  · exact LoopC2N_contDiffAt_green (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hMb
      (by simpa using hz))
  · exact LoopC2N_contDiffAt_green (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hMb hz)

/-- The resolvent word is `C²` at every Hermitian point (as a function of `M`). -/
private theorem LoopC2N_contDiffAt_word {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L))
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
      l.foldr (fun p X => Gsig (blockMat M') z p.1 * Eblk L W p.2 * X) 1) M := by
  induction l with
  | nil => exact contDiffAt_const
  | cons p l ih =>
    have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx L W) (Idx L W) ℂ => Eblk L W p.2) M :=
      contDiffAt_const
    exact ((LoopC2N_contDiffAt_Gsig hz p.1 hM).mul hEp).mul ih

/-- (H1) for the `k`-loop observable: `C²` at every Hermitian point. -/
private theorem LoopC2N_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Z2 L) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2
      (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z (loopOf σ b)) M := by
  have h := (LoopC2N_trCLM (BlockIndex L W)).contDiff.contDiffAt.comp M
    (LoopC2N_contDiffAt_word hz ((List.ofFn σ).zip (List.ofFn b)) hM)
  exact h

/-- The first two derivatives of the `k`-loop observable along a Hermitian line, with the bound
`|φ₂| ≤ N · k (k + 1) η⁻⁽ᵏ⁺²⁾ ‖y‖²`, `N = (L W)²`. -/
private theorem LoopC2N_line_jets {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Z2 L) {M y : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ∃ φ₁ φ₂ : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun s : ℝ =>
        gloop L W (blockMat (M + (s : ℂ) • y)) z (loopOf σ b)) (φ₁ t) t) ∧
      (∀ t : ℝ, HasDerivAt φ₁ (φ₂ t) t) ∧
      (∀ t : ℝ, ‖φ₂ t‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) + 1) * η⁻¹ ^ (k + 2) * ‖y‖ ^ 2)) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hMb : (blockMat M).IsHermitian := LoopC2N_isHermitian_blockMat hM
  have hyb : (blockMat y).IsHermitian := LoopC2N_isHermitian_blockMat hy
  have hE1 : ∀ p : Bool × Z2 L, ‖Eblk L W p.2‖ ≤ 1 := fun p => by
    refine (norm_Eblk_le_inv_W_sq L W p.2).trans ?_
    have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    have hW2 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
    have hW3 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    exact pow_le_one₀ hW3 hW2
  obtain ⟨P1, P2, hd1, hd2, -, -, hb2⟩ := LoopC2N_word_jets
    (R := fun (p : Bool × Z2 L) (s : ℝ) => Gsig (blockMat M + (s : ℂ) • blockMat y) z p.1)
    (E := fun p : Bool × Z2 L => Eblk L W p.2) (D := blockMat y) (K := η⁻¹)
    (fun p t => LoopC2N_hasDerivAt_Gsig hMb hyb hz0 p.1 t)
    (fun p t => norm_Gsig_le_inv_eta L W (isHermitian_add_realSmul hMb hyb t) hη hz p.1)
    hE1 ((List.ofFn σ).zip (List.ofFn b))
  refine ⟨fun t => Matrix.trace (P1 t), fun t => Matrix.trace (P2 t), ?_, ?_, ?_⟩
  · intro t
    have hfun : (fun s : ℝ => gloop L W (blockMat (M + (s : ℂ) • y)) z (loopOf σ b))
        = fun s : ℝ => Matrix.trace (LoopC2N_word
          (fun (p : Bool × Z2 L) (s : ℝ) => Gsig (blockMat M + (s : ℂ) • blockMat y) z p.1)
          (fun p : Bool × Z2 L => Eblk L W p.2) ((List.ofFn σ).zip (List.ofFn b)) s) := by
      funext s
      rw [LoopC2N_blockMat_add_smul]
      rfl
    rw [hfun]
    exact LoopC2N_trace_hasDerivAt (hd1 t)
  · intro t
    exact LoopC2N_trace_hasDerivAt (hd2 t)
  · intro t
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    rw [card_BlockIndex]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hlen : ((List.ofFn σ).zip (List.ofFn b)).length = k := by simp
    have h2 := hb2 t
    rw [hlen, LoopC2N_norm_blockMat] at h2
    exact h2

/-- (H3): the second derivative of the `k`-loop observable in a Hermitian direction. -/
private theorem LoopC2N_second_deriv_bound {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 L) {M y : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ
        (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z (loopOf σ b))) M y y‖
      ≤ (((L * W) ^ 2 : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) + 1) * η⁻¹ ^ (k + 2) * ‖y‖ ^ 2) := by
  have hz0 : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  obtain ⟨φ₁, φ₂, h₀, hd2, hb⟩ := LoopC2N_line_jets (L := L) (W := W) hη hz σ b hM hy
  rw [LoopC2N_fderiv2_of_line
    (fun M' hM' => LoopC2N_contDiffAt_loop (L := L) (W := W) hz0 σ b hM') hM hy h₀ hd2]
  exact hb 0

end Observable

/-! ### 5. The target -/

section Target

variable (d : Sizes)

/-- **`HermTestFunLoopN`, the general-length `C²` bound of the loop observables.**  For every
`k`, `n`, `|E| < 2`, `0 ≤ u < 1`, `σ : Fin k → Bool`, `b : Fin k → Z_L²`, the observable
`M ↦ gloop (blockMat M) (spectralZ E u) (loopOf σ b)` is in the Hermitian test class
(`HermTestFun`) and `‖∂²(…)(M)[y, y]‖ ≤ k (k + 1) N η_u^{-(k+2)} ‖y‖²` at Hermitian `M, y`,
`N = (W L)²`, `η_u = (1 - u) Im m`.  This is the statement `HermTestFunLoopN` of `GridGoodN`
(section `TestClass`), with no added hypothesis; `0 ≤ u` is not used (as in the case `k = 2`).
The proof uses `‖E_b‖ ≤ W⁻² ≤ 1` (dropping the factor `W^{-2k}`), so the constant is the count
`k (k + 1)` of the Leibniz terms. -/
theorem hermTestFunLoopN : HermTestFunLoopN d := by
  intro k _ n E u hE _hu0 hu1 σ b
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hpos : 0 < (1 - u) * (spectralM E).im := mul_pos (by linarith) (spectralM_im_pos hE)
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hz0 : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]; exact hpos.ne'
  have hwf : (loopOf σ b).WF := by
    simp [LoopIdx.WF, loopOf]
  refine ⟨⟨fun M hM => LoopC2N_contDiffAt_loop hz0 σ b hM,
    ⟨_, fun M hM => norm_gloop_le_crude (d.L n) (d.W n)
      (LoopC2N_isHermitian_blockMat hM) hη hz (loopOf σ b) hwf⟩⟩, ?_⟩
  intro M y hM hy
  have h := LoopC2N_second_deriv_bound (L := d.L n) (W := d.W n) hη hz σ b hM hy
  refine h.trans (le_of_eq ?_)
  have hN : (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) = (Sizes.size d n : ℝ) := by
    rw [Sizes.size, mul_comm]
  rw [hN]
  push_cast
  ring

end Target

end RBM.Ind

end
