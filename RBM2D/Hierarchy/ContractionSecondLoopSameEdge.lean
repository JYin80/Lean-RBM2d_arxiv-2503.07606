/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopReverse

/-!
# A single-edge term of the second loop derivative
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem trace_blockRelabel_sameEdge
    (M : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Matrix.trace (Gauss.blockRelabel L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, Gauss.blockRelabel]
  exact (Equiv.sum_comp (splitEquiv L W).symm (fun i => M i i))

private theorem blockRelabel_mul_sameEdge
    (M N : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) :
    Gauss.blockRelabel L W (M * N) =
      Gauss.blockRelabel L W M * Gauss.blockRelabel L W N := by
  exact (Matrix.submatrix_mul_equiv M N
    (splitEquiv L W).symm (splitEquiv L W).symm (splitEquiv L W).symm).symm

private theorem trace_coordinateBlock_pair_sameEdge
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
  rw [← hA, ← hC, ← blockRelabel_mul_sameEdge L W,
    ← blockRelabel_mul_sameEdge L W, ← blockRelabel_mul_sameEdge L W]
  exact trace_blockRelabel_sameEdge L W _

/-- Coordinate contraction in block notation, with the physical-site
Gaussian covariance and its exact `W²` normalization. -/
theorem sum_coordinateBlock_trace_pair
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (A * Gauss.coordinateBlock L W γ * C *
          Gauss.coordinateBlock L W γ)) =
    (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      Matrix.trace (A * Eblk L W p) * SB L p q *
        Matrix.trace (C * Eblk L W q) := by
  simp_rw [trace_coordinateBlock_pair_sameEdge L W]
  rw [Gauss.sum_allCoords_trace_blocks]
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split]

omit [NeZero W] in
private theorem trace_two_smul_sameEdge (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

/-- One actual second Green derivative produces a twice-weighted same-edge
`A B C B` contraction. The trace rotation puts the fixed block projector
inside `A = G Eₐ G`. -/
theorem trace_gsigCoordinateSecondDeriv_Eblk
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W)
    (γ : Gauss.Coord L W) (z : ℂ) (s : Bool) (a : Z2 L) :
    let G := Gsig (Gauss.HflowBlock L W u ω) z s
    Matrix.trace (Gauss.gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a) =
      (2 : ℂ) * (u : ℂ) *
        Matrix.trace ((G * Eblk L W a * G) * Gauss.coordinateBlock L W γ * G *
          Gauss.coordinateBlock L W γ) := by
  let G := Gsig (Gauss.HflowBlock L W u ω) z s
  let E := Eblk L W a
  let D := Gauss.coordinateBlock L W γ
  let B := Real.sqrt u • D
  have hcyc : Matrix.trace (G * B * G * B * G * E) =
      Matrix.trace ((G * E * G) * B * G * B) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (G * B * G * B) (G * E)
  change Matrix.trace (((2 : ℝ) • (G * B * G * B * G)) * E) =
    (2 : ℂ) * (u : ℂ) * Matrix.trace ((G * E * G) * D * G * D)
  rw [smul_mul_assoc, Matrix.trace_smul, hcyc, trace_two_smul_sameEdge L W u hu]
  simp only [two_smul, two_mul]
  ring

/-- Gaussian variance contraction of the actual second derivative at one
Green edge. The first trace contains the two-edge loop `G Eₐ G Eₚ`, and the
second trace is the one-edge loop `G E_q`. -/
theorem sum_gsigCoordinateSecondDeriv_Eblk
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W)
    (z : ℂ) (s : Bool) (a : Z2 L) :
    let G := Gsig (Gauss.HflowBlock L W u ω) z s
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (Gauss.gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ∑ p : Z2 L, ∑ q : Z2 L,
        Matrix.trace ((G * Eblk L W a * G) * Eblk L W p) * SB L p q *
          Matrix.trace (G * Eblk L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_Eblk L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : Gauss.Coord L W,
          (((Gauss.gvar L W γ : ℝ) : ℂ) *
            Matrix.trace ((Gsig (Gauss.HflowBlock L W u ω) z s * Eblk L W a *
              Gsig (Gauss.HflowBlock L W u ω) z s) *
              Gauss.coordinateBlock L W γ *
              Gsig (Gauss.HflowBlock L W u ω) z s *
              Gauss.coordinateBlock L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [sum_coordinateBlock_trace_pair L W]
      ring

end RBM
