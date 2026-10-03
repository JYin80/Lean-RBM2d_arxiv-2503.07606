/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Vocab
import RBM2D.Path.OneStep
import RBM2D.Path.UBounds
import RBM2D.Hierarchy.ContractionCutWords
import RBM2D.Gauss.LoopInitialValueScalar
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.GreenDerivative

/-!
# The `n = 2` loop hierarchy at matrix level

The three `Prop` definitions `KpmODE`, `LoopGenN2`, `HierarchyN2` state the `n = 2` loop
hierarchy at matrix level; they are proved here as `kpmODE`, `loopGenN2`, `hierarchyN2`.

Paper: arXiv:2503.07606, (`pro_dyncalK`) and (`Kn2sol`), (`eq:mainStoflow`) and
(`def_EwtG`), (`eq_L-Keee`), (`def_ELKLK`), (`DefTHUST`), (`LK_SDE`).

Proof outline.
* `kpmODE`: `|m|² = 1` (`normSqSpectralMOne`), so `Kpm = W⁻² Θ_u`; then `hasDerivAt_Theta_apply`
  composed with `ℝ → ℂ`.
* `loopGenN2`: the space part of `genMat` is computed directly at `n = 2`: the second derivative of
  `tr(G₊ E_{a₁} G₋ E_{a₂})` along `M + y C_c` is `2 Σ` of three traces (two same-edge cuts, one
  pair cut); the coordinate sum is contracted by `Gauss.sum_allCoords_trace_blocks`.  The
  spectral part is `-m tr(G₊² E G₋ E) - m̄ tr(G₊ E G₋² E)`; with `Σ_b E_b = W⁻²` and
  `Σ_a S_{ab} = 1` it combines with the same-edge cuts into `𝓔^{(G̃)}` (`EGt`).
* `hierarchyN2`: `loopGenN2 - kpmODE`, rearranged with `Theta_commute_SB`, `Theta_transpose`,
  `SB_transpose`, as in the one-dimensional argument.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-! ## The statements -/

/-- **The `𝒦` ODE at `n = 2`**, (`pro_dyncalK`) with (`Kn2sol`):
`∂_u 𝒦_{(a,b)} = W² Σ_{c,e} 𝒦_{(a,c)} S_{ce} 𝒦_{(e,b)}`. -/
def KpmODE : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ a b : Z2 L, HasDerivAt (fun v : ℝ => Kpm L W E v a b)
      ((W : ℂ) ^ 2 * ∑ c : Z2 L, ∑ e : Z2 L, Kpm L W E u a c * SB L c e * Kpm L W E u e b) u

/-- **The loop generator at `n = 2`**, drift part of (`eq:mainStoflow`) at
`σ = (+,-)`: `genMat(𝓛_{(a₁,a₂)}) = W² Σ 𝓛 S 𝓛 + 𝓔^{(G̃)}`, for Hermitian `M`. -/
def LoopGenN2 : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ a₁ a₂ : Z2 L,
      genMat E u M (pmLoop a₁ a₂) = LLpair L W E u M a₁ a₂ + EGt L W E u M a₁ a₂

/-- **The `(𝓛 - 𝒦)` hierarchy at `n = 2`**, drift part of (`LK_SDE`) with the
generator `ξ S Θ` in each slot: `genMat(𝓛) - ∂_u 𝒦 = Θ∘(𝓛-𝒦) + 𝓔^{LK×LK} + 𝓔^{(G̃)}`. -/
def HierarchyN2 : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ a₁ a₂ : Z2 L,
      genMat E u M (pmLoop a₁ a₂) - deriv (fun v : ℝ => Kpm L W E v a₁ a₂) u =
        thetaGen L (Complex.normSq (spectralM E) : ℂ) u
            (fun b : Z2 L × Z2 L => lkMat L W E u M b.1 b.2) (a₁, a₂) +
          ELKLK L W E u M a₁ a₂ + EGt L W E u M a₁ a₂

/-! ## 1. The `𝒦` ODE at `n = 2` -/

section KODE

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|m|² = 1` as a complex number, for `|E| < 2`. -/
private theorem DriftAlgebra_normSq_one {E : ℝ} (hE : |E| < 2) :
    ((Complex.normSq (spectralM E) : ℝ) : ℂ) = 1 := by
  rw [normSqSpectralMOne E hE.le, Complex.ofReal_one]

/-- `Kpm = W⁻² Θ_u` for `|E| < 2`. -/
private theorem DriftAlgebra_Kpm_eq {E : ℝ} (hE : |E| < 2) (v : ℝ) (a b : Z2 L) :
    Kpm L W E v a b = ((W : ℂ)⁻¹) ^ 2 * Theta L (v : ℂ) a b := by
  rw [Kpm, DriftAlgebra_normSq_one hE, mul_one, mul_one]

/-- The `(a, b)` entry of `Θ S Θ` as a double sum. -/
private theorem DriftAlgebra_TST_apply (A S B : Matrix (Z2 L) (Z2 L) ℂ) (a b : Z2 L) :
    (A * S * B) a b = ∑ c : Z2 L, ∑ e : Z2 L, A a c * S c e * B e b := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end KODE

/-- **`kpmODE`**: the `𝒦` ODE at `n = 2`. -/
theorem kpmODE : KpmODE := by
  intro L W _ _ E hL hE u hu0 hu1 a b
  have hu : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  have hfun : (fun v : ℝ => Kpm L W E v a b) =
      fun v : ℝ => ((W : ℂ)⁻¹) ^ 2 * Theta L (v : ℂ) a b := by
    funext v
    exact DriftAlgebra_Kpm_eq hE v a b
  rw [hfun]
  have hT := ((hasDerivAt_Theta_apply L hL hu a b).comp_ofReal).const_mul (((W : ℂ)⁻¹) ^ 2)
  refine hT.congr_deriv ?_
  simp only [DriftAlgebra_Kpm_eq hE u]
  rw [DriftAlgebra_TST_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  field_simp

/-! ## 2. Derivatives of the two-loop word -/

section Word

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace commutes with the derivative (as `OneStep_hasDerivAt_trace`, which is private). -/
private theorem DriftAlgebra_hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- A signed resolvent along a moving Hermitian matrix and spectral parameter
(as `OneStep_hasDerivAt_Gsig`, which is private). -/
private theorem DriftAlgebra_hasDerivAt_Gsig {H : ℝ → Matrix n n ℂ} {zf : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {t : ℝ}
    (hH : HasDerivAt H H' t) (hz : HasDerivAt zf z' t) (hherm : (H t).IsHermitian)
    (him : (zf t).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s => Gsig (H s) (zf s) σ)
      (-(Gsig (H t) (zf t) σ *
        (H' - (if σ then z' else (starRingEnd ℂ) z') • (1 : Matrix n n ℂ)) *
        Gsig (H t) (zf t) σ)) t := by
  cases σ with
  | true => exact hasDerivAt_green_moving hH hz hherm him
  | false =>
      have hz' : HasDerivAt (fun s => (starRingEnd ℂ) (zf s)) ((starRingEnd ℂ) z') t := hz.star
      have him' : ((starRingEnd ℂ) (zf t)).im ≠ 0 := by simpa using him
      exact hasDerivAt_green_moving hH hz' hherm him'

variable {R : ℝ → Bool → Matrix n n ℂ} {D : Bool → Matrix n n ℂ} {t : ℝ}

/-- First derivative of `R₊ A R₋ B` when `R_σ' = -R_σ D_σ R_σ`. -/
private theorem DriftAlgebra_hasDerivAt_word1
    (hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R t σ * D σ * R t σ)) t) (A B : Matrix n n ℂ) :
    HasDerivAt (fun s => R s true * A * R s false * B)
      (-(R t true * D true * R t true * A * R t false * B) -
        R t true * A * R t false * D false * R t false * B) t := by
  have h := (((hR true).mul_const A).mul (hR false)).mul_const B
  refine h.congr_deriv ?_
  noncomm_ring

/-- Second derivative of `R₊ A R₋ B` when `R_σ' = -R_σ D_σ R_σ`. -/
private theorem DriftAlgebra_hasDerivAt_word2
    (hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R t σ * D σ * R t σ)) t) (A B : Matrix n n ℂ) :
    HasDerivAt (fun s => -(R s true * D true * R s true * A * R s false * B) -
        R s true * A * R s false * D false * R s false * B)
      (R t true * D true * R t true * D true * R t true * A * R t false * B +
        R t true * D true * R t true * D true * R t true * A * R t false * B +
        (R t true * D true * R t true * A * R t false * D false * R t false * B +
          R t true * D true * R t true * A * R t false * D false * R t false * B) +
        (R t true * A * R t false * D false * R t false * D false * R t false * B +
          R t true * A * R t false * D false * R t false * D false * R t false * B)) t := by
  have h1 := (((((hR true).mul_const (D true)).mul (hR true)).mul_const A).mul
    (hR false)).mul_const B
  have h2 := (((((hR true).mul_const A).mul (hR false)).mul_const (D false)).mul
    (hR false)).mul_const B
  refine (h1.neg.sub h2).congr_deriv ?_
  simp only [Pi.mul_apply]
  noncomm_ring

end Word

/-! ## 3. The two-loop at a block matrix: space and spectral derivatives -/

section Loop

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The `(+,-)` two-loop as one trace. -/
private theorem DriftAlgebra_gloop_pm (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (a b : Z2 L) :
    gloop L W H z (pmLoop a b) =
      Matrix.trace (Gsig H z true * Eblk L W a * Gsig H z false * Eblk L W b) := by
  simp [gloop, gloopProd, pmLoop, Matrix.mul_assoc]

/-- A three-loop as one trace. -/
private theorem DriftAlgebra_gloop_three (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (z : ℂ) (s₁ s₂ s₃ : Bool) (x y w : Z2 L) :
    gloop L W H z (loopOf ![s₁, s₂, s₃] ![x, y, w]) =
      Matrix.trace (Gsig H z s₁ * Eblk L W x * Gsig H z s₂ * Eblk L W y * Gsig H z s₃ *
        Eblk L W w) := by
  simp [gloop, gloopProd, loopOf, List.ofFn_succ, Matrix.mul_assoc]

/-- `blockMat` is real-affine along a line. -/
private theorem DriftAlgebra_blockMat_add_smul (M C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (M + y • C) = blockMat M + y • blockMat C := by
  ext i j
  simp [blockMat]

/-- The second derivative of the two-loop along a Hermitian line, at `0`: two same-edge cuts and
one pair cut, each counted twice. -/
private theorem DriftAlgebra_deriv2_line {H B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : Z2 L) :
    deriv (deriv (fun y : ℝ => gloop L W (H + (y : ℂ) • B) z (pmLoop a b))) 0 =
      2 * (Matrix.trace (Gsig H z true * B * Gsig H z true * B * Gsig H z true * Eblk L W a *
            Gsig H z false * Eblk L W b) +
          Matrix.trace (Gsig H z true * B * Gsig H z true * Eblk L W a * Gsig H z false * B *
            Gsig H z false * Eblk L W b) +
          Matrix.trace (Gsig H z true * Eblk L W a * Gsig H z false * B * Gsig H z false * B *
            Gsig H z false * Eblk L W b)) := by
  set R : ℝ → Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun s σ => Gsig (H + (s : ℂ) • B) z σ with hRdef
  have hR : ∀ y : ℝ, ∀ σ, HasDerivAt (fun s => R s σ) (-(R y σ * (fun _ => B) σ * R y σ)) y := by
    intro y σ
    have := DriftAlgebra_hasDerivAt_Gsig (hasDerivAt_line H B y) (hasDerivAt_const y z)
      (isHermitian_add_realSmul hH hB y) hz σ
    simpa [hRdef] using this
  have h1 : deriv (fun y : ℝ => gloop L W (H + (y : ℂ) • B) z (pmLoop a b)) =
      fun y => Matrix.trace (-(R y true * B * R y true * Eblk L W a * R y false * Eblk L W b) -
        R y true * Eblk L W a * R y false * B * R y false * Eblk L W b) := by
    funext y
    simp only [DriftAlgebra_gloop_pm]
    exact (DriftAlgebra_hasDerivAt_trace
      (DriftAlgebra_hasDerivAt_word1 (hR y) (Eblk L W a) (Eblk L W b))).deriv
  rw [h1]
  have h2 := (DriftAlgebra_hasDerivAt_trace
    (DriftAlgebra_hasDerivAt_word2 (D := fun _ => B) (hR 0) (Eblk L W a) (Eblk L W b))).deriv
  rw [h2]
  simp only [hRdef, Complex.ofReal_zero, zero_smul, add_zero, Matrix.trace_add]
  ring

/-- The spectral derivative of the two-loop at a Hermitian block matrix. -/
private theorem DriftAlgebra_deriv_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (a b : Z2 L) :
    deriv (fun v : ℝ => gloop L W H (spectralZ E v) (pmLoop a b)) u =
      -(spectralM E * Matrix.trace (Gsig H (spectralZ E u) true * Gsig H (spectralZ E u) true *
          Eblk L W a * Gsig H (spectralZ E u) false * Eblk L W b)) -
        (starRingEnd ℂ) (spectralM E) * Matrix.trace (Gsig H (spectralZ E u) true * Eblk L W a *
          Gsig H (spectralZ E u) false * Gsig H (spectralZ E u) false * Eblk L W b) := by
  have him : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  set R : ℝ → Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun s σ => Gsig H (spectralZ E s) σ with hRdef
  set D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun σ => (if σ then spectralM E else (starRingEnd ℂ) (spectralM E)) •
      (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) with hDdef
  have hR : ∀ σ, HasDerivAt (fun s => R s σ) (-(R u σ * D σ * R u σ)) u := by
    intro σ
    have := DriftAlgebra_hasDerivAt_Gsig (hasDerivAt_const u H) (hasDerivAt_spectralZ E u) hH
      him σ
    refine this.congr_deriv ?_
    cases σ <;> simp [hDdef, hRdef]
  have h := (DriftAlgebra_hasDerivAt_trace
    (DriftAlgebra_hasDerivAt_word1 hR (Eblk L W a) (Eblk L W b))).deriv
  simp only [DriftAlgebra_gloop_pm]
  rw [h]
  simp only [hRdef, hDdef, ite_true, Bool.false_eq_true, ite_false, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul]

/-- The coordinate contraction at block level (`Gauss.sum_allCoords_trace_blocks`). -/
private theorem DriftAlgebra_cov (X Y : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        Matrix.trace (X * blockMat (coordinateMatrix L W c) * Y *
          blockMat (coordinateMatrix L W c)) =
      (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
        Matrix.trace (X * Eblk L W p) * SB L p q * Matrix.trace (Y * Eblk L W q) := by
  have key := Gauss.sum_allCoords_trace_blocks L W (X.submatrix (split L W) (split L W))
    (Y.submatrix (split L W) (split L W))
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hX := blockRelabel_submatrix_split L W X
  have hY := blockRelabel_submatrix_split L W Y
  have hmul : ∀ P Q : Matrix (Idx L W) (Idx L W) ℂ,
      Gauss.blockRelabel L W (P * Q) = Gauss.blockRelabel L W P * Gauss.blockRelabel L W Q :=
    fun P Q => (Matrix.submatrix_mul_equiv P Q
      (splitEquiv L W).symm (splitEquiv L W).symm (splitEquiv L W).symm).symm
  have htr : ∀ P : Matrix (Idx L W) (Idx L W) ℂ,
      Matrix.trace (Gauss.blockRelabel L W P) = Matrix.trace P := by
    intro P
    simp only [Matrix.trace, Matrix.diag, Gauss.blockRelabel]
    exact Equiv.sum_comp (splitEquiv L W).symm (fun i => P i i)
  have hC : blockMat (coordinateMatrix L W c) =
      Gauss.blockRelabel L W (coordinateMatrix L W c) := rfl
  conv_lhs => rw [← hX, ← hY, hC, ← hmul, ← hmul, ← hmul, htr]

end Loop

/-! ## 4. The loop generator at `n = 2` -/

section Gen

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Inserting `1 = W² Σ_p E_p` in a trace. -/
private theorem DriftAlgebra_trace_insert (X Y : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (X * Y) = (W : ℂ) ^ 2 * ∑ p : Z2 L, Matrix.trace (X * Eblk L W p * Y) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have h : ∑ p : Z2 L, Matrix.trace (X * Eblk L W p * Y) =
      Matrix.trace (X * (∑ p : Z2 L, Eblk L W p) * Y) := by
    rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  rw [h, sum_Eblk, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_one,
    smul_eq_mul, ← mul_assoc]
  field_simp

/-- Column sums of `S^{(B)}` are `1`. -/
private theorem DriftAlgebra_sum_SB_col (hL : 3 ≤ L) (b : Z2 L) : ∑ a : Z2 L, SB L a b = 1 := by
  rw [← sum_SB_row L hL b]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrFun (congrFun (SB_transpose L) b) a

/-- The final finite-sum algebra of `loopGenN2`. -/
private theorem DriftAlgebra_sum_algebra (hL : 3 ≤ L) (w m m' : ℂ)
    (f₁ f₂ g₁ g₂ : Z2 L → ℂ) (P : Z2 L → Z2 L → ℂ) (a b : Z2 L) :
    w * ∑ p : Z2 L, ∑ q : Z2 L, f₁ p * SB L p q * g₁ q +
        w * ∑ p : Z2 L, ∑ q : Z2 L, P p b * SB L p q * P a q +
        w * ∑ p : Z2 L, ∑ q : Z2 L, f₂ p * SB L p q * g₂ q +
      (-(m * (w * ∑ p : Z2 L, f₁ p)) - m' * (w * ∑ p : Z2 L, f₂ p)) =
    w * ∑ b₁ : Z2 L, ∑ b₂ : Z2 L, P a b₁ * SB L b₁ b₂ * P b₂ b +
      w * ∑ a' : Z2 L, ∑ b' : Z2 L,
        ((g₁ a' - m) * SB L a' b' * f₁ b' + (g₂ a' - m') * SB L a' b' * f₂ b') := by
  have hS : ∀ p q : Z2 L, SB L p q = SB L q p := fun p q =>
    congrFun (congrFun (SB_transpose L) q) p
  have hP : ∑ p : Z2 L, ∑ q : Z2 L, P p b * SB L p q * P a q =
      ∑ b₁ : Z2 L, ∑ b₂ : Z2 L, P a b₁ * SB L b₁ b₂ * P b₂ b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [hS p q]
    ring
  have hG : ∀ (f g : Z2 L → ℂ) (m : ℂ),
      ∑ a' : Z2 L, ∑ b' : Z2 L, (g a' - m) * SB L a' b' * f b' =
        ∑ p : Z2 L, ∑ q : Z2 L, f p * SB L p q * g q - m * ∑ p : Z2 L, f p := by
    intro f g m
    have h1 : ∑ a' : Z2 L, ∑ b' : Z2 L, g a' * SB L a' b' * f b' =
        ∑ p : Z2 L, ∑ q : Z2 L, f p * SB L p q * g q := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [hS q p]
      ring
    have h2 : ∑ a' : Z2 L, ∑ b' : Z2 L, m * SB L a' b' * f b' = m * ∑ p : Z2 L, f p := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, DriftAlgebra_sum_SB_col hL, mul_one]
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a' _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hG, hG, hP]
  ring

end Gen

section GenMain

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)`. -/
private theorem DriftAlgebra_avgErr (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (a : Z2 L) :
    avgErr L W E u M σ a =
      Matrix.trace (Gsig (blockMat M) (spectralZ E u) σ * Eblk L W a) - KLoop.mSig E σ := by
  rw [avgErr, greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, trace_Eblk_eq_one, smul_eq_mul, mul_one]

/-- Rotation of a trace, written with right-nested products on both sides. -/
private theorem DriftAlgebra_rot {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : Matrix.trace (X * Y) = Matrix.trace (Y * X) :=
  Matrix.trace_mul_comm X Y

end GenMain

/-- **`loopGenN2`**: the loop generator at `n = 2`. -/
theorem loopGenN2 : LoopGenN2 := by
  intro L W _ _ E hL hE u hu0 hu1 M hM a₁ a₂
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  set H := blockMat M with hHdef
  set z := spectralZ E u with hzdef
  set Rp := Gsig H z true with hRp
  set Rm := Gsig H z false with hRm
  set Ea := Eblk L W a₁ with hEa
  set Eb := Eblk L W a₂ with hEb
  set Cb : Coord L W → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun c => blockMat (coordinateMatrix L W c) with hCb
  -- the space part, coordinate by coordinate
  have hspace : ∀ c : Coord L W, deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) z (pmLoop a₁ a₂))) 0 =
      2 * (Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
        Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
        Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c)) := by
    intro c
    simp only [DriftAlgebra_blockMat_add_smul]
    rw [← hHdef, DriftAlgebra_deriv2_line (B := blockMat (coordinateMatrix L W c)) hH ((coordinateMatrix_isHermitian L W c).submatrix _) hz]
    have h1 := DriftAlgebra_rot (Rp * Cb c * Rp * Cb c) (Rp * Ea * Rm * Eb)
    have h2 := DriftAlgebra_rot (Rp * Cb c * Rp * Ea * Rm * Cb c) (Rm * Eb)
    have h3 := DriftAlgebra_rot (Rp * Ea * Rm * Cb c * Rm * Cb c) (Rm * Eb)
    simp only [Matrix.mul_assoc] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  -- the spectral part
  have hspec := DriftAlgebra_deriv_spec (L := L) (W := W) hH hE hu1 a₁ a₂
  -- the six trace identifications
  have e1 : ∀ p : Z2 L, Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Eblk L W p) =
      loop3 L W E u M ![true, true, false] ![p, a₁, a₂] := by
    intro p
    rw [loop3, DriftAlgebra_gloop_three]
    have h := DriftAlgebra_rot (Rp * Ea * Rm * Eb) (Rp * Eblk L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e2 : ∀ p : Z2 L, Matrix.trace ((Rm * Eb * Rp) * Eblk L W p) = loopPM L W E u M p a₂ := by
    intro p
    rw [loopPM, DriftAlgebra_gloop_pm]
    have h := DriftAlgebra_rot (Rm * Eb) (Rp * Eblk L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e3 : ∀ q : Z2 L, Matrix.trace ((Rp * Ea * Rm) * Eblk L W q) = loopPM L W E u M a₁ q := by
    intro q
    rw [loopPM, DriftAlgebra_gloop_pm]
  have e4 : ∀ p : Z2 L, Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Eblk L W p) =
      loop3 L W E u M ![true, false, false] ![a₁, p, a₂] := by
    intro p
    rw [loop3, DriftAlgebra_gloop_three]
    have h := DriftAlgebra_rot (Rm * Eb) (Rp * Ea * Rm * Eblk L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e5 : Matrix.trace (Rp * Rp * Ea * Rm * Eb) =
      (W : ℂ) ^ 2 * ∑ p : Z2 L, loop3 L W E u M ![true, true, false] ![p, a₁, a₂] := by
    rw [show Rp * Rp * Ea * Rm * Eb = Rp * (Rp * Ea * Rm * Eb) by simp only [Matrix.mul_assoc],
      DriftAlgebra_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    rw [loop3, DriftAlgebra_gloop_three]
    simp only [Matrix.mul_assoc]
    rfl
  have e6 : Matrix.trace (Rp * Ea * Rm * Rm * Eb) =
      (W : ℂ) ^ 2 * ∑ p : Z2 L, loop3 L W E u M ![true, false, false] ![a₁, p, a₂] := by
    rw [show Rp * Ea * Rm * Rm * Eb = (Rp * Ea * Rm) * (Rm * Eb) by simp only [Matrix.mul_assoc],
      DriftAlgebra_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    rw [loop3, DriftAlgebra_gloop_three]
    simp only [Matrix.mul_assoc]
    rfl
  -- the left side
  have hlhs : genMat E u M (pmLoop a₁ a₂) =
      (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
          loop3 L W E u M ![true, true, false] ![p, a₁, a₂] * SB L p q *
            Matrix.trace (Rp * Eblk L W q) +
        (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
          loopPM L W E u M p a₂ * SB L p q * loopPM L W E u M a₁ q +
        (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
          loop3 L W E u M ![true, false, false] ![a₁, p, a₂] * SB L p q *
            Matrix.trace (Rm * Eblk L W q) +
      (-(spectralM E * ((W : ℂ) ^ 2 * ∑ p : Z2 L,
          loop3 L W E u M ![true, true, false] ![p, a₁, a₂])) -
        (starRingEnd ℂ) (spectralM E) * ((W : ℂ) ^ 2 * ∑ p : Z2 L,
          loop3 L W E u M ![true, false, false] ![a₁, p, a₂])) := by
    rw [genMat, Finset.sum_congr rfl fun c _ => by rw [hspace c], hspec, ← e5, ← e6]
    have hsplit : (1 / 2 : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (2 * (Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
          Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
          Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c))) =
        ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
            Matrix.trace ((Rp * Ea * Rm * Eb * Rp) * Cb c * Rp * Cb c) +
          ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
            Matrix.trace ((Rm * Eb * Rp) * Cb c * (Rp * Ea * Rm) * Cb c) +
          ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
            Matrix.trace ((Rm * Eb * Rp * Ea * Rm) * Cb c * Rm * Cb c) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hsplit]
    simp only [hCb]
    rw [DriftAlgebra_cov, DriftAlgebra_cov, DriftAlgebra_cov]
    simp only [e1, e2, e3, e4]
    rfl
  -- the right side
  have hrhs : LLpair L W E u M a₁ a₂ + EGt L W E u M a₁ a₂ =
      (W : ℂ) ^ 2 * ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
          loopPM L W E u M a₁ b₁ * SB L b₁ b₂ * loopPM L W E u M b₂ a₂ +
        (W : ℂ) ^ 2 * ∑ a' : Z2 L, ∑ b' : Z2 L,
          ((Matrix.trace (Rp * Eblk L W a') - spectralM E) * SB L a' b' *
              loop3 L W E u M ![true, true, false] ![b', a₁, a₂] +
            (Matrix.trace (Rm * Eblk L W a') - (starRingEnd ℂ) (spectralM E)) * SB L a' b' *
              loop3 L W E u M ![true, false, false] ![a₁, b', a₂]) := by
    rw [LLpair, EGt]
    simp only [DriftAlgebra_avgErr]
    rfl
  rw [hlhs, hrhs]
  exact DriftAlgebra_sum_algebra hL ((W : ℂ) ^ 2) (spectralM E) ((starRingEnd ℂ) (spectralM E))
    (fun p => loop3 L W E u M ![true, true, false] ![p, a₁, a₂])
    (fun p => loop3 L W E u M ![true, false, false] ![a₁, p, a₂])
    (fun q => Matrix.trace (Rp * Eblk L W q)) (fun q => Matrix.trace (Rm * Eblk L W q))
    (fun x y => loopPM L W E u M x y) a₁ a₂

/-! ## 5. The `(𝓛 - 𝒦)` hierarchy at `n = 2` -/

section Hier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix form of `𝓛S𝓛 - 𝒦S𝒦 = STD + DST + DSD` with `𝓛 = D + 𝒦`, `𝒦 = c T`, `wc = 1`,
`TS = ST`. -/
private theorem DriftAlgebra_matrix_identity (S T D : Matrix n n ℂ) (w c : ℂ) (hwc : w * c = 1)
    (hTS : T * S = S * T) :
    w • ((D + c • T) * S * (D + c • T)) - w • ((c • T) * S * (c • T)) =
      S * T * D + D * (S * T) + w • (D * S * D) := by
  have e1 : w • ((D + c • T) * S * (D + c • T)) =
      w • (D * S * D) + (w * c) • (D * S * T) + (w * c) • (T * S * D) +
        (w * c * c) • (T * S * T) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    rw [mul_comm c c, ← mul_assoc]
    abel
  have e2 : w • ((c • T) * S * (c • T)) = (w * c * c) • (T * S * T) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm c c, ← mul_assoc]
  rw [e1, e2, hwc, one_smul, one_smul, hTS, Matrix.mul_assoc D S T]
  abel

end Hier

/-- **`hierarchyN2`**: the `(𝓛 - 𝒦)` hierarchy at `n = 2`. -/
theorem hierarchyN2 : HierarchyN2 := by
  intro L W _ _ E hL hE u hu0 hu1 M hM a₁ a₂
  have hu : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  rw [loopGenN2 L W E hL hE u hu0 hu1 M hM a₁ a₂, (kpmODE L W E hL hE u hu0 hu1 a₁ a₂).deriv,
    DriftAlgebra_normSq_one hE]
  set T := Theta L (u : ℂ) with hT
  set S := SB L with hS
  set c : ℂ := ((W : ℂ)⁻¹) ^ 2 with hc
  set w : ℂ := (W : ℂ) ^ 2 with hw
  have hwc : w * c = 1 := by
    have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
    rw [hw, hc]
    field_simp
  set D : Matrix (Z2 L) (Z2 L) ℂ := Matrix.of fun x y => lkMat L W E u M x y with hD
  have hK : ∀ x y : Z2 L, Kpm L W E u x y = (c • T) x y := by
    intro x y
    rw [DriftAlgebra_Kpm_eq hE, Matrix.smul_apply, smul_eq_mul]
  have hL' : ∀ x y : Z2 L, loopPM L W E u M x y = (D + c • T) x y := by
    intro x y
    rw [Matrix.add_apply, ← hK, hD, Matrix.of_apply, lkMat, sub_add_cancel]
  have hTS : T * S = S * T := Theta_commute_SB L hL hu
  have hsym : ∀ x y : Z2 L, (S * T) x y = (S * T) y x := by
    intro x y
    have h : (S * T)ᵀ = S * T := by
      rw [Matrix.transpose_mul, Theta_transpose L hL hu, hS, SB_transpose, ← hS, hTS]
    rw [← h, Matrix.transpose_apply, h]
  have hLL : LLpair L W E u M a₁ a₂ = w * ((D + c • T) * S * (D + c • T)) a₁ a₂ := by
    rw [LLpair, DriftAlgebra_TST_apply]
    simp only [hL']
    rfl
  have hKK : w * ∑ c' : Z2 L, ∑ e : Z2 L, Kpm L W E u a₁ c' * S c' e * Kpm L W E u e a₂ =
      w * ((c • T) * S * (c • T)) a₁ a₂ := by
    rw [DriftAlgebra_TST_apply]
    simp only [hK]
  have hLK : ELKLK L W E u M a₁ a₂ = w * (D * S * D) a₁ a₂ := by
    rw [ELKLK, DriftAlgebra_TST_apply]
    rfl
  have hTh : thetaGen L 1 u (fun b : Z2 L × Z2 L => lkMat L W E u M b.1 b.2) (a₁, a₂) =
      (S * T * D) a₁ a₂ + (D * (S * T)) a₁ a₂ := by
    simp only [thetaGen, thetaGenMat, one_smul, mul_one, Finset.sum_add_distrib]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsym a₂ b, mul_comm]
    rfl
  have key := congrFun (congrFun (DriftAlgebra_matrix_identity S T D w c hwc hTS) a₁) a₂
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at key
  rw [hLL, hKK, hLK, hTh]
  linear_combination key

end RBM.Path

end
