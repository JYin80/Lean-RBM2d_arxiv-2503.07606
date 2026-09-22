/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateSecondDerivative
import RBM2D.Hierarchy.ContractionCutWords

/-!
# A two-edge cross term in the second loop derivative
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem trace_blockRelabel (M : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Matrix.trace (Gauss.blockRelabel L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, Gauss.blockRelabel]
  exact (Equiv.sum_comp (splitEquiv L W).symm (fun i => M i i))

private theorem blockRelabel_mul
    (M N : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Gauss.blockRelabel L W (M * N) =
      Gauss.blockRelabel L W M * Gauss.blockRelabel L W N := by
  exact (Matrix.submatrix_mul_equiv M N
    (splitEquiv L W).symm (splitEquiv L W).symm (splitEquiv L W).symm).symm

private theorem trace_coordinateBlock_pair
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (γ : Gauss.Coord L W) :
    Matrix.trace (A * Gauss.coordinateBlock L W γ * C *
      Gauss.coordinateBlock L W γ) =
    Matrix.trace (A.submatrix (split L W) (split L W) *
      Gauss.coordinateMatrix L W γ * C.submatrix (split L W) (split L W) *
      Gauss.coordinateMatrix L W γ) := by
  let P := A.submatrix (split L W) (split L W)
  let Q := C.submatrix (split L W) (split L W)
  have hA : Gauss.blockRelabel L W P = A := blockRelabel_submatrix_split L W A
  have hC : Gauss.blockRelabel L W Q = C := blockRelabel_submatrix_split L W C
  change Matrix.trace (A * Gauss.blockRelabel L W (Gauss.coordinateMatrix L W γ) *
    C * Gauss.blockRelabel L W (Gauss.coordinateMatrix L W γ)) =
    Matrix.trace (P * Gauss.coordinateMatrix L W γ * Q * Gauss.coordinateMatrix L W γ)
  rw [← hA, ← hC, ← blockRelabel_mul L W,
    ← blockRelabel_mul L W, ← blockRelabel_mul L W]
  exact trace_blockRelabel L W _

omit [NeZero W] in
/-- The ordered mixed term obtained by differentiating two distinct Green
factors once is the cut-chain trace, before covariance summation. -/
theorem trace_twoEdge_mixed_eq_cutChains
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    let Gs := Gsig H z s
    let Gt := Gsig H z t
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let M := gloopProd L W H z ⟨σ₂, a₂⟩
    let T := gloopProd L W H z ⟨σ₃, a₃⟩
    Matrix.trace (P * (Gs * B * Gs * Eblk L W a) * M *
      (Gt * B * Gt * Eblk L W c) * T) =
    Matrix.trace (cutLeftChain L W H z σ₁ σ₃ a₁ a₃ s t c * B *
      cutRightChain L W H z σ₂ a₂ s t a * B) := by
  let P := gloopProd L W H z ⟨σ₁, a₁⟩
  let M := gloopProd L W H z ⟨σ₂, a₂⟩
  let T := gloopProd L W H z ⟨σ₃, a₃⟩
  let Gs := Gsig H z s
  let Gt := Gsig H z t
  let Ea := Eblk L W a
  let Ec := Eblk L W c
  simpa only [cutLeftChain, cutRightChain, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (P * Gs * B * Gs * Ea * M * Gt * B) (Gt * Ec * T))

/-- Covariance summation of one ordered, unscaled two-edge cross term. -/
theorem sum_twoEdge_mixed_cutChains
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (cutLeftChain L W H z σ₁ σ₃ a₁ a₃ s t c *
          Gauss.coordinateBlock L W γ *
          cutRightChain L W H z σ₂ a₂ s t a *
          Gauss.coordinateBlock L W γ)) =
    (W : ℂ) ^ 2 * ∑ u : Z2 L, ∑ v : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
        SB L u v *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  simp_rw [trace_coordinateBlock_pair L W]
  exact sum_coordinate_cutChains L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

omit [NeZero W] in
private theorem trace_two_smul (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

private theorem trace_twoEdge_deriv_signs
    (u : ℝ) (ω : Gauss.Ω L W) (γ : Gauss.Coord L W) (z : ℂ)
    (P M T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (s t : Bool) (a c : Z2 L) :
    let H := Gauss.HflowBlock L W u ω
    let B := Real.sqrt u • Gauss.coordinateBlock L W γ
    Matrix.trace (P * (Gauss.gsigCoordinateDeriv L W u ω γ z s * Eblk L W a) * M *
      (Gauss.gsigCoordinateDeriv L W u ω γ z t * Eblk L W c) * T) =
    Matrix.trace (P * (Gsig H z s * B * Gsig H z s * Eblk L W a) * M *
      (Gsig H z t * B * Gsig H z t * Eblk L W c) * T) := by
  simp only [Gauss.gsigCoordinateDeriv, neg_mul, mul_neg, neg_neg]

/-- One ordered cross term in the finite second product rule, after the
Gaussian coordinate weights are summed. The other ordering and terms where
both derivatives hit one edge are separate. -/
theorem sum_twoEdge_mixed_coordinate
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := Gauss.HflowBlock L W u ω
    let Gs := Gsig H z s
    let Gt := Gsig H z t
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let M := gloopProd L W H z ⟨σ₂, a₂⟩
    let T := gloopProd L W H z ⟨σ₃, a₃⟩
    (∑ γ : Gauss.Coord L W,
      let B := Real.sqrt u • Gauss.coordinateBlock L W γ
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gs * B * Gs * Eblk L W a) * M *
          (Gt * B * Gt * Eblk L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SB L p q *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_mixed_eq_cutChains L W]
  simp_rw [trace_two_smul L W u hu]
  calc
    _ = (u : ℂ) * ∑ γ : Gauss.Coord L W,
          (((Gauss.gvar L W γ : ℝ) : ℂ) *
            Matrix.trace (cutLeftChain L W (Gauss.HflowBlock L W u ω) z
              σ₁ σ₃ a₁ a₃ s t c * Gauss.coordinateBlock L W γ *
              cutRightChain L W (Gauss.HflowBlock L W u ω) z
                σ₂ a₂ s t a * Gauss.coordinateBlock L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [sum_twoEdge_mixed_cutChains L W (Gauss.HflowBlock L W u ω) z
        σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂]
      ring

/-- The same contraction written with the two actual first derivatives of
the signed Green factors in `coordinateSecondWordDeriv`. -/
theorem sum_twoEdge_mixed_deriv
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := Gauss.HflowBlock L W u ω
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let M := gloopProd L W H z ⟨σ₂, a₂⟩
    let T := gloopProd L W H z ⟨σ₃, a₃⟩
    (∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (P *
          (Gauss.gsigCoordinateDeriv L W u ω γ z s * Eblk L W a) * M *
          (Gauss.gsigCoordinateDeriv L W u ω γ z t * Eblk L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SB L p q *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_deriv_signs L W u ω]
  exact sum_twoEdge_mixed_coordinate L W u hu ω z
    σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

end RBM
