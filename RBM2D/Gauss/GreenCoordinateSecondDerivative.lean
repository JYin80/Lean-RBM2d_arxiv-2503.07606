/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateDerivative

/-!
# Second derivative of a Green matrix in one Gaussian coordinate

For the affine coordinate direction `B = √u • coordinateBlock c`, differentiating
`-G B G` once more gives `2 G B G B G`. The spectral parameter stays fixed.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The derivative of the first-coordinate derivative `-G B G`. -/
theorem hasDerivAt_greenCoordinateDerivative (u : ℝ) (ω : Ω L W)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        let G := green (HflowBlock L W u (Function.update ω c t)) z;
        let B := Real.sqrt u • coordinateBlock L W c;
        -(G * B * G))
      (let G := green (HflowBlock L W u ω) z;
       let B := Real.sqrt u • coordinateBlock L W c;
       (2 : ℝ) • (G * B * G * B * G)) (ω c) := by
  let B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    Real.sqrt u • coordinateBlock L W c
  let G : ℝ → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun t => green (HflowBlock L W u (Function.update ω c t)) z
  have hbase : G (ω c) = green (HflowBlock L W u ω) z := by
    simp [G]
  have hG : HasDerivAt G (-(G (ω c) * B * G (ω c))) (ω c) := by
    simpa only [G, B, hbase] using
      hasDerivAt_green_HflowBlock_update L W u ω c hz
  have hprod := ((hG.mul_const B).mul hG).neg
  have hval :
      -((-(G (ω c) * B * G (ω c)) * B) * G (ω c) +
        (G (ω c) * B) * (-(G (ω c) * B * G (ω c)))) =
      (2 : ℝ) • (G (ω c) * B * G (ω c) * B * G (ω c)) := by
    rw [two_smul]
    noncomm_ring
  rw [hval] at hprod
  have hfun :
      -((fun t : ℝ => G t * B) * G) =
        (fun t : ℝ => -(G t * B * G t)) := by
    funext t
    rfl
  rw [hfun] at hprod
  simpa only [G, B, hbase] using hprod

end RBM.Gauss
