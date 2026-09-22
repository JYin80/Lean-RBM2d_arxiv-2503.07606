/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyCutLengths
import RBM2D.Hierarchy.LoopHierarchyCutContinuity

/-!
# Deterministic bounds for finite cut-loop summands

The factors below retain the exact block covariance entry `‖SB L p q‖` and
the exact normalized projector factor `(W⁻¹)²` per Green edge. No row-sum
estimate or Gaussian expectation factorization is used.
-/

namespace RBM.Gauss

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The uniform single-loop resolvent envelope at a fixed nonreal spectral
point, expressed by its well-formed edge count. -/
theorem norm_gloop_fixed_le (u : ℝ) (ω : Ω L W) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|)
    (K : LoopIdx (Z2 L)) (hK : K.WF) :
    ‖gloop L W (HflowBlock L W u ω) z K‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ K.length := by
  have hlow : ∀ v ∈ Set.Icc u u, η ≤ |((fun _ : ℝ => z) v).im| := by
    intro v hv
    exact hz
  have h := norm_gloop_any_window_le L W hη hlow K
    (show u ∈ Set.Icc u u from ⟨le_rfl, le_rfl⟩) ω
  have hlen : (K.σ.zip K.a).length = K.length := by
    simp [LoopIdx.WF, LoopIdx.length] at hK ⊢
    omega
  simpa only [hlen] using h

/-- One same-edge cut summand is bounded by an outer `(n+1)`-edge loop,
its covariance entry, and a one-edge loop. -/
theorem norm_sameEdgeCutIntegrand_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (e : EdgeSplit (Bool × Z2 L))
    (he : e ∈ edgeSplits (I.σ.zip I.a)) (p q : Z2 L)
    (u : ℝ) (ω : Ω L W) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖sameEdgeCutIntegrand L W u ω z e p q‖ ≤
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.length + 1)) *
      ‖SB L p q‖ *
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2))) := by
  have hWF := sameEdge_cut_WF L e p q
  have hlen := sameEdge_cut_lengths L I hwf e he p q
  have hout := norm_gloop_fixed_le L W u ω hη hz
    (sameEdgeOuterIdx L e p) hWF.1
  have hin := norm_gloop_fixed_le L W u ω hη hz
    (sameEdgeInnerIdx L e q) hWF.2
  rw [hlen.1] at hout
  rw [hlen.2, pow_one] at hin
  change ‖gloop L W (HflowBlock L W u ω) z (sameEdgeOuterIdx L e p) *
    SB L p q *
    gloop L W (HflowBlock L W u ω) z (sameEdgeInnerIdx L e q)‖ ≤ _
  calc
    _ ≤ ‖gloop L W (HflowBlock L W u ω) z (sameEdgeOuterIdx L e p)‖ *
        ‖SB L p q‖ *
        ‖gloop L W (HflowBlock L W u ω) z (sameEdgeInnerIdx L e q)‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ _ := by gcongr

/-- One ordered pair-cut summand has the exact left and right edge powers
from its three intervening list segments. -/
theorem norm_pairCutIntegrand_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a)) (v w : Z2 L)
    (u : ℝ) (ω : Ω L W) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖pairCutIntegrand L W u ω z p v w‖ ≤
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^
          (p.before.length + p.after.length + 2)) *
      ‖SB L v w‖ *
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (p.middle.length + 2)) := by
  have hcut := pair_cut_lengths_WF L I hwf p hp v w
  have hout := norm_gloop_fixed_le L W u ω hη hz
    ((pairBaseIdx L p).cutGlueL (p.before.length + 1)
      (p.before.length + p.middle.length + 2) v) hcut.2.2.1
  have hin := norm_gloop_fixed_le L W u ω hη hz
    ((pairBaseIdx L p).cutGlueR (p.before.length + 1)
      (p.before.length + p.middle.length + 2) w) hcut.2.2.2
  rw [hcut.1] at hout
  rw [hcut.2.1] at hin
  have hterm : pairCutIntegrand L W u ω z p v w =
      gloop L W (HflowBlock L W u ω) z
        ((pairBaseIdx L p).cutGlueL (p.before.length + 1)
          (p.before.length + p.middle.length + 2) v) * SB L v w *
      gloop L W (HflowBlock L W u ω) z
        ((pairBaseIdx L p).cutGlueR (p.before.length + 1)
          (p.before.length + p.middle.length + 2) w) := by
    simp [pairCutIntegrand, pairBaseIdx, segmentLoopIdx]
  rw [hterm]
  change ‖gloop L W (HflowBlock L W u ω) z
    ((pairBaseIdx L p).cutGlueL (p.before.length + 1)
      (p.before.length + p.middle.length + 2) v) * SB L v w *
    gloop L W (HflowBlock L W u ω) z
      ((pairBaseIdx L p).cutGlueR (p.before.length + 1)
        (p.before.length + p.middle.length + 2) w)‖ ≤ _
  calc
    _ ≤ ‖gloop L W (HflowBlock L W u ω) z
          ((pairBaseIdx L p).cutGlueL (p.before.length + 1)
            (p.before.length + p.middle.length + 2) v)‖ *
        ‖SB L v w‖ *
        ‖gloop L W (HflowBlock L W u ω) z
          ((pairBaseIdx L p).cutGlueR (p.before.length + 1)
            (p.before.length + p.middle.length + 2) w)‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ _ := by gcongr

/-- The Gaussian expectation of one same-edge cut summand obeys the same
deterministic envelope because `P L W` is a probability measure. -/
theorem norm_integral_sameEdgeCutIntegrand_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (e : EdgeSplit (Bool × Z2 L))
    (he : e ∈ edgeSplits (I.σ.zip I.a)) (p q : Z2 L)
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖∫ ω : Ω L W, sameEdgeCutIntegrand L W u ω z e p q ∂(P L W)‖ ≤
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.length + 1)) *
      ‖SB L p q‖ *
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2))) := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P L W) (f := fun ω : Ω L W =>
      sameEdgeCutIntegrand L W u ω z e p q)
    (Filter.Eventually.of_forall fun ω =>
      norm_sameEdgeCutIntegrand_le L W I hwf e he p q u ω hη hz)
  simpa using h

/-- The Gaussian expectation of one distinct-edge pair summand obeys its
exact two-loop deterministic envelope. -/
theorem norm_integral_pairCutIntegrand_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a)) (v w : Z2 L)
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖∫ ω : Ω L W, pairCutIntegrand L W u ω z p v w ∂(P L W)‖ ≤
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^
          (p.before.length + p.after.length + 2)) *
      ‖SB L v w‖ *
      ((Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (p.middle.length + 2)) := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P L W) (f := fun ω : Ω L W =>
      pairCutIntegrand L W u ω z p v w)
    (Filter.Eventually.of_forall fun ω =>
      norm_pairCutIntegrand_le L W I hwf p hp v w u ω hη hz)
  simpa using h

end RBM.Gauss
