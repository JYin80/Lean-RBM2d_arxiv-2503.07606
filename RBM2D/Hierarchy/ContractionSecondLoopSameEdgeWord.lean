/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopSameEdge

/-!
# A same-edge second derivative inside a finite matrix word
-/

namespace RBM

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem trace_two_smul_word (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

/-- A single second Green derivative at an arbitrary edge of a matrix word.
The surrounding prefix and suffix remain explicit matrices. -/
theorem trace_gsigCoordinateSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W)
    (γ : Gauss.Coord L W) (z : ℂ) (s : Bool) (a : Z2 L)
    (P T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    let G := Gsig (Gauss.HflowBlock L W u ω) z s
    Matrix.trace (P * (Gauss.gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a) * T) =
      (2 : ℂ) * (u : ℂ) *
        Matrix.trace (((G * Eblk L W a * T * P) * G) *
          Gauss.coordinateBlock L W γ * G * Gauss.coordinateBlock L W γ) := by
  let G := Gsig (Gauss.HflowBlock L W u ω) z s
  let E := Eblk L W a
  let D := Gauss.coordinateBlock L W γ
  let B := Real.sqrt u • D
  have hcyc : Matrix.trace (P * ((G * B * G * B * G) * E) * T) =
      Matrix.trace (((G * E * T * P) * G) * B * G * B) := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (P * G * B * G * B) (G * E * T)
  change Matrix.trace (P * (((2 : ℝ) • (G * B * G * B * G)) * E) * T) =
    (2 : ℂ) * (u : ℂ) * Matrix.trace (((G * E * T * P) * G) * D * G * D)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, hcyc,
    trace_two_smul_word L W u hu]
  simp only [two_smul, two_mul]
  ring

/-- The weighted same-edge term at one chosen position of a finite word.
The covariance is exactly `SB L p q`, with the surrounding word absorbed
into the first block trace. -/
theorem sum_gsigCoordinateSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Gauss.Ω L W)
    (z : ℂ) (s : Bool) (a : Z2 L)
    (P T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    let G := Gsig (Gauss.HflowBlock L W u ω) z s
    ∑ γ : Gauss.Coord L W,
      (((Gauss.gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gauss.gsigCoordinateSecondDeriv L W u ω γ z s *
          Eblk L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ∑ p : Z2 L, ∑ q : Z2 L,
        Matrix.trace ((((G * Eblk L W a * T * P) * G) * Eblk L W p)) *
          SB L p q * Matrix.trace (G * Eblk L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_word L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : Gauss.Coord L W,
          (((Gauss.gvar L W γ : ℝ) : ℂ) *
            Matrix.trace (((Gsig (Gauss.HflowBlock L W u ω) z s * Eblk L W a *
              T * P) * Gsig (Gauss.HflowBlock L W u ω) z s) *
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
