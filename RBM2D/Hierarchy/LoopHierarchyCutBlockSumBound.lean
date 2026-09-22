/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyCutNormBounds
import RBM2D.Propagator.Basic

/-!
# Block-label sums of finite cut-loop bounds

For `L ≥ 3`, each row of the actual five-point block covariance has total
absolute mass one. Thus a double block-label sum contributes one factor
`card (Z2 L)`, not its square, to the crude cut-loop envelope.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The exact crude resolvent-loop envelope: one dimension factor and one
normalized projector factor per Green edge. -/
noncomputable def cutResolventEnvelope (η : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (BlockIndex L W) : ℝ) *
    (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ n

/-- Real norm row sum of the actual block covariance, for `L ≥ 3`. -/
theorem sum_norm_SB_row (hL : 3 ≤ L) (p : Z2 L) :
    ∑ q : Z2 L, ‖SB L p q‖ = (1 : ℝ) := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    (RBM.sum_nnnorm_SB_row L hL p)
  simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using h

/-- A fixed same-edge split, summed over both block labels, has exactly one
free block-cardinality factor after the covariance row sum. -/
theorem sum_norm_integral_sameEdgeCutIntegrand_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (e : EdgeSplit (Bool × Z2 L))
    (he : e ∈ edgeSplits (I.σ.zip I.a))
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    (∑ p : Z2 L, ∑ q : Z2 L,
      ‖∫ ω : Ω L W,
        sameEdgeCutIntegrand L W u ω z e p q ∂(P L W)‖) ≤
      (Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η (I.length + 1) *
          cutResolventEnvelope L W η 1) := by
  let A := cutResolventEnvelope L W η (I.length + 1)
  let B := cutResolventEnvelope L W η 1
  have hpoint (p q : Z2 L) :
      ‖∫ ω : Ω L W,
        sameEdgeCutIntegrand L W u ω z e p q ∂(P L W)‖ ≤
        A * ‖SB L p q‖ * B := by
    simpa [A, B, cutResolventEnvelope] using
      norm_integral_sameEdgeCutIntegrand_le L W I hwf e he p q u hη hz
  calc
    _ ≤ ∑ p : Z2 L, ∑ q : Z2 L, A * ‖SB L p q‖ * B := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint p q
    _ = ∑ p : Z2 L, (A * B) * (∑ q : Z2 L, ‖SB L p q‖) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (Fintype.card (Z2 L) : ℝ) * (A * B) := by
      simp [sum_norm_SB_row L hL, Finset.sum_const, nsmul_eq_mul]
    _ = _ := rfl

/-- The analogous fixed ordered pair split has the same single free block
factor, with the two exact pair-cut loop lengths. -/
theorem sum_norm_integral_pairCutIntegrand_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a))
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    (∑ v : Z2 L, ∑ w : Z2 L,
      ‖∫ ω : Ω L W,
        pairCutIntegrand L W u ω z p v w ∂(P L W)‖) ≤
      (Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η
          (p.before.length + p.after.length + 2) *
          cutResolventEnvelope L W η (p.middle.length + 2)) := by
  let A := cutResolventEnvelope L W η
    (p.before.length + p.after.length + 2)
  let B := cutResolventEnvelope L W η (p.middle.length + 2)
  have hpoint (v w : Z2 L) :
      ‖∫ ω : Ω L W,
        pairCutIntegrand L W u ω z p v w ∂(P L W)‖ ≤
        A * ‖SB L v w‖ * B := by
    simpa [A, B, cutResolventEnvelope] using
      norm_integral_pairCutIntegrand_le L W I hwf p hp v w u hη hz
  calc
    _ ≤ ∑ v : Z2 L, ∑ w : Z2 L, A * ‖SB L v w‖ * B := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact hpoint v w
    _ = ∑ v : Z2 L, (A * B) * (∑ w : Z2 L, ‖SB L v w‖) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = (Fintype.card (Z2 L) : ℝ) * (A * B) := by
      simp [sum_norm_SB_row L hL, Finset.sum_const, nsmul_eq_mul]
    _ = _ := rfl

end RBM.Gauss
