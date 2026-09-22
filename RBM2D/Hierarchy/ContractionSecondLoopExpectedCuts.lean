/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopAllCuts
import RBM2D.Gauss.LoopCoordinateIntegrability
import RBM2D.Gauss.LoopEnvelope

/-!
# Expected finite cut sums of the second loop derivative
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Two finite Green-loop traces have an integrable product at a nonreal
spectral point, even before a list-level well-formedness simplification. -/
theorem integrable_gloop_product (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I J : LoopIdx (Z2 L)) :
    Integrable (fun ω : Ω L W =>
      gloop L W (HflowBlock L W u ω) z I *
        gloop L W (HflowBlock L W u ω) z J) (P L W) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  let C (K : LoopIdx (Z2 L)) : ℝ :=
    (Fintype.card (BlockIndex L W) : ℝ) *
      (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (K.σ.zip K.a).length
  have hbound (K : LoopIdx (Z2 L)) (ω : Ω L W) :
      ‖gloop L W (HflowBlock L W u ω) z K‖ ≤ C K := by
    have ht := norm_matrix_trace_le_card_mul
      (gloopProd L W (HflowBlock L W u ω) z K)
    have hw := norm_foldr_Gsig_Eblk_le L W
      (HflowBlock_isHermitian L W u ω) hη le_rfl (K.σ.zip K.a)
    calc
      ‖gloop L W (HflowBlock L W u ω) z K‖ ≤
          (Fintype.card (BlockIndex L W) : ℝ) *
            ‖gloopProd L W (HflowBlock L W u ω) z K‖ := ht
      _ ≤ C K := by
        exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
  have hcont (K : LoopIdx (Z2 L)) :
      Continuous (fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z K) :=
    (continuous_matrixTrace L W).comp
      (continuous_gloopProd_HflowBlock_sample L W u hz K)
  apply Integrable.of_bound ((hcont I).mul (hcont J)).measurable.aestronglyMeasurable
    (C I * C J)
  exact Filter.Eventually.of_forall fun ω => by
    calc
      ‖gloop L W (HflowBlock L W u ω) z I *
          gloop L W (HflowBlock L W u ω) z J‖ ≤
          ‖gloop L W (HflowBlock L W u ω) z I‖ *
            ‖gloop L W (HflowBlock L W u ω) z J‖ := norm_mul_le _ _
      _ ≤ C I * C J := by
        apply mul_le_mul (hbound I ω) (hbound J ω) (norm_nonneg _)
        dsimp [C]
        positivity

private theorem integrable_gloop_term (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I J : LoopIdx (Z2 L)) (k : ℂ) :
    Integrable (fun ω : Ω L W =>
      gloop L W (HflowBlock L W u ω) z I * k *
        gloop L W (HflowBlock L W u ω) z J) (P L W) := by
  have h := (integrable_gloop_product L W u hz I J).const_mul k
  convert h using 1
  funext ω
  ring

private theorem integrable_gloop_double_sum (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (A B : Z2 L → LoopIdx (Z2 L)) (K : Z2 L → Z2 L → ℂ) :
    Integrable (fun ω : Ω L W =>
      ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W (HflowBlock L W u ω) z (A p) * K p q *
          gloop L W (HflowBlock L W u ω) z (B q)) (P L W) := by
  refine integrable_finsetSum Finset.univ fun p _ =>
    integrable_finsetSum Finset.univ fun q _ => ?_
  exact integrable_gloop_term L W u hz (A p) (B q) (K p q)

private theorem integral_gloop_double_sum (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (A B : Z2 L → LoopIdx (Z2 L)) (K : Z2 L → Z2 L → ℂ) :
    ∫ ω : Ω L W, (∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W (HflowBlock L W u ω) z (A p) * K p q *
        gloop L W (HflowBlock L W u ω) z (B q)) ∂(P L W) =
      ∑ p : Z2 L, ∑ q : Z2 L, ∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) z (A p) * K p q *
          gloop L W (HflowBlock L W u ω) z (B q) ∂(P L W) := by
  rw [integral_finsetSum Finset.univ (fun p _ =>
    integrable_finsetSum Finset.univ (fun q _ =>
      integrable_gloop_term L W u hz (A p) (B q) (K p q)))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum Finset.univ (fun q _ =>
    integrable_gloop_term L W u hz (A p) (B q) (K p q))]

/-- Each fixed same-edge cut sum has a Gaussian expectation. -/
theorem integrable_sameEdgeCutValue (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (e : EdgeSplit (Bool × Z2 L)) :
    Integrable (fun ω : Ω L W => sameEdgeCutValue L W u ω z e) (P L W) := by
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  let A (p : Z2 L) : LoopIdx (Z2 L) :=
    ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
      e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩
  let B (q : Z2 L) : LoopIdx (Z2 L) := ⟨[e.selected.1], [q]⟩
  change Integrable (fun ω : Ω L W =>
    ∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W (HflowBlock L W u ω) z (A p) * SB L p q *
        gloop L W (HflowBlock L W u ω) z (B q)) (P L W)
  exact integrable_gloop_double_sum L W u hz A B (SB L)

/-- Each fixed two-edge cut sum has a Gaussian expectation. -/
theorem integrable_pairCutValue (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (p : PairSplit (Bool × Z2 L)) :
    Integrable (fun ω : Ω L W => pairCutValue L W u ω z p) (P L W) := by
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  let I : LoopIdx (Z2 L) :=
    ⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
      I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩
  let A (v : Z2 L) : LoopIdx (Z2 L) :=
    I.cutGlueL (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v
  let B (w : Z2 L) : LoopIdx (Z2 L) :=
    I.cutGlueR (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w
  change Integrable (fun ω : Ω L W =>
    ∑ v : Z2 L, ∑ w : Z2 L,
      gloop L W (HflowBlock L W u ω) z (A v) * SB L v w *
        gloop L W (HflowBlock L W u ω) z (B w)) (P L W)
  exact integrable_gloop_double_sum L W u hz A B (SB L)

/-- One same-edge block summand before expectation. -/
noncomputable def sameEdgeCutIntegrand (u : ℝ) (ω : Ω L W) (z : ℂ)
    (e : EdgeSplit (Bool × Z2 L)) (p q : Z2 L) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  gloop L W H z
    ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
      e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
    SB L p q * gloop L W H z ⟨[e.selected.1], [q]⟩

/-- One distinct-edge left/right block summand before expectation. -/
noncomputable def pairCutIntegrand (u : ℝ) (ω : Ω L W) (z : ℂ)
    (p : PairSplit (Bool × Z2 L)) (v w : Z2 L) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  gloop L W H z
    ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
        I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueL
      (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
    SB L v w *
  gloop L W H z
    ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
        I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueR
      (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)

/-- Expectation commutes with the finite block sum of a same-edge cut. -/
theorem integral_sameEdgeCutValue (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (e : EdgeSplit (Bool × Z2 L)) :
    ∫ ω : Ω L W, sameEdgeCutValue L W u ω z e ∂(P L W) =
      ∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W, sameEdgeCutIntegrand L W u ω z e p q ∂(P L W) := by
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  let A (p : Z2 L) : LoopIdx (Z2 L) :=
    ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
      e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩
  let B (q : Z2 L) : LoopIdx (Z2 L) := ⟨[e.selected.1], [q]⟩
  change (∫ ω : Ω L W, (∑ p : Z2 L, ∑ q : Z2 L,
    gloop L W (HflowBlock L W u ω) z (A p) * SB L p q *
      gloop L W (HflowBlock L W u ω) z (B q)) ∂(P L W)) =
    ∑ p : Z2 L, ∑ q : Z2 L, ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) z (A p) * SB L p q *
        gloop L W (HflowBlock L W u ω) z (B q) ∂(P L W)
  exact integral_gloop_double_sum L W u hz A B (SB L)

/-- Expectation commutes with the finite block sum of a two-edge cut. -/
theorem integral_pairCutValue (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (p : PairSplit (Bool × Z2 L)) :
    ∫ ω : Ω L W, pairCutValue L W u ω z p ∂(P L W) =
      ∑ v : Z2 L, ∑ w : Z2 L,
        ∫ ω : Ω L W, pairCutIntegrand L W u ω z p v w ∂(P L W) := by
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  let I : LoopIdx (Z2 L) :=
    ⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
      I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩
  let A (v : Z2 L) : LoopIdx (Z2 L) :=
    I.cutGlueL (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v
  let B (w : Z2 L) : LoopIdx (Z2 L) :=
    I.cutGlueR (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w
  change (∫ ω : Ω L W, (∑ v : Z2 L, ∑ w : Z2 L,
    gloop L W (HflowBlock L W u ω) z (A v) * SB L v w *
      gloop L W (HflowBlock L W u ω) z (B w)) ∂(P L W)) =
    ∑ v : Z2 L, ∑ w : Z2 L, ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) z (A v) * SB L v w *
        gloop L W (HflowBlock L W u ω) z (B w) ∂(P L W)
  exact integral_gloop_double_sum L W u hz A B (SB L)

omit [NeZero L] [NeZero W] in
private theorem integrable_list_sum {α : Type*} (μ : Measure (Ω L W))
    (es : List α) (f : α → Ω L W → ℂ)
    (hf : ∀ e ∈ es, Integrable (f e) μ) :
    Integrable (fun ω => (es.map fun e => f e ω).sum) μ := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil]; exact integrable_zero _ _ _
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hf e (by simp)).add (ih (by
        intro d hd
        exact hf d (by simp [hd])))

omit [NeZero L] [NeZero W] in
private theorem integral_list_sum {α : Type*} (μ : Measure (Ω L W))
    (es : List α) (f : α → Ω L W → ℂ)
    (hf : ∀ e ∈ es, Integrable (f e) μ) :
    ∫ ω, (es.map fun e => f e ω).sum ∂μ =
      (es.map fun e => ∫ ω, f e ω ∂μ).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil, integral_zero]
  | cons e es ih =>
      have he : Integrable (f e) μ := hf e (by simp)
      have hes : ∀ d ∈ es, Integrable (f d) μ := by
        intro d hd
        exact hf d (by simp [hd])
      simp only [List.map_cons, List.sum_cons]
      rw [integral_add he (integrable_list_sum L W μ es f hes), ih hes]

/-- The variance-weighted second coordinate derivative is integrable under
the actual finite Gaussian product law. -/
theorem integrable_weightedSecondWordDeriv
    (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Integrable (fun ω : Ω L W => ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z (I.σ.zip I.a))))
      (P L W) := by
  apply integrable_finsetSum Finset.univ
  intro γ _
  exact ((integrable_gloop_coordinate_derivatives L W u γ hz I hwf).2).const_mul
    (((gvar L W γ : ℝ) : ℂ))

/-- The expected Hessian cut formula. All exchanges are finite, and each
individual cut product is integrable under the actual Gaussian law. -/
theorem integral_coordinateSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 < u) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × Z2 L)) :
    ∫ ω : Ω L W, (∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l))) ∂(P L W) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ((edgeSplits l).map (fun e => ∑ p : Z2 L, ∑ q : Z2 L,
        ∫ ω : Ω L W, sameEdgeCutIntegrand L W u ω z e p q ∂(P L W))).sum +
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ((pairSplits l).map (fun p => ∑ v : Z2 L, ∑ w : Z2 L,
        ∫ ω : Ω L W, pairCutIntegrand L W u ω z p v w ∂(P L W))).sum := by
  let C : ℂ := (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2
  let S (ω : Ω L W) : ℂ :=
    ((edgeSplits l).map (sameEdgeCutValue L W u ω z)).sum
  let T (ω : Ω L W) : ℂ :=
    ((pairSplits l).map (pairCutValue L W u ω z)).sum
  have hS : Integrable S (P L W) :=
    integrable_list_sum L W (P L W) (edgeSplits l)
      (fun e ω => sameEdgeCutValue L W u ω z e)
      (fun e _ => integrable_sameEdgeCutValue L W u hz e)
  have hT : Integrable T (P L W) :=
    integrable_list_sum L W (P L W) (pairSplits l)
      (fun p ω => pairCutValue L W u ω z p)
      (fun p _ => integrable_pairCutValue L W u hz p)
  have hpoint (ω : Ω L W) :
      (∑ γ : Coord L W,
        (((gvar L W γ : ℝ) : ℂ) *
          Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l))) =
        C * S ω + C * T ω :=
    sum_coordinateSecondWordDeriv_allCuts L W u hu.le ω z l
  calc
    _ = ∫ ω : Ω L W, (C * S ω + C * T ω) ∂(P L W) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = C * (∫ ω : Ω L W, S ω ∂(P L W)) +
        C * (∫ ω : Ω L W, T ω ∂(P L W)) := by
      rw [integral_add (hS.const_mul C) (hT.const_mul C)]
      simp only [integral_const_mul]
    _ = C * ((edgeSplits l).map (fun e =>
          ∫ ω : Ω L W, sameEdgeCutValue L W u ω z e ∂(P L W))).sum +
        C * ((pairSplits l).map (fun p =>
          ∫ ω : Ω L W, pairCutValue L W u ω z p ∂(P L W))).sum := by
      rw [integral_list_sum L W (P L W) (edgeSplits l)
        (fun e ω => sameEdgeCutValue L W u ω z e)
        (fun e _ => integrable_sameEdgeCutValue L W u hz e),
        integral_list_sum L W (P L W) (pairSplits l)
          (fun p ω => pairCutValue L W u ω z p)
          (fun p _ => integrable_pairCutValue L W u hz p)]
    _ = _ := by
      simp_rw [integral_sameEdgeCutValue L W u hz,
        integral_pairCutValue L W u hz]
      rfl

/-- For a well-formed loop, the genuine weighted Hessian observable is
integrable and has the expected cut formula above. -/
theorem integrable_and_integral_gloopSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 < u) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Integrable (fun ω : Ω L W => ∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z (I.σ.zip I.a))))
      (P L W) ∧
    (∫ ω : Ω L W, (∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z (I.σ.zip I.a))))
        ∂(P L W) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((edgeSplits (I.σ.zip I.a)).map (fun e => ∑ p : Z2 L, ∑ q : Z2 L,
          ∫ ω : Ω L W, sameEdgeCutIntegrand L W u ω z e p q ∂(P L W))).sum +
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((pairSplits (I.σ.zip I.a)).map (fun p => ∑ v : Z2 L, ∑ w : Z2 L,
          ∫ ω : Ω L W, pairCutIntegrand L W u ω z p v w ∂(P L W))).sum) := by
  exact ⟨integrable_weightedSecondWordDeriv L W u hz I hwf,
    integral_coordinateSecondWordDeriv_allCuts L W u hu hz (I.σ.zip I.a)⟩

/-- The same expectation formula for the actual second coordinate derivative
of the finite Gaussian resolvent loop. -/
theorem integral_actual_gloopSecondCoordinate_allCuts
    (u : ℝ) (hu : 0 < u) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∫ ω : Ω L W, (∑ γ : Coord L W,
      (((gvar L W γ : ℝ) : ℂ) *
        deriv (fun t : ℝ => deriv (fun s : ℝ =>
          gloop L W (HflowBlock L W u (Function.update ω γ s)) z I) t) (ω γ)))
        ∂(P L W) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((edgeSplits (I.σ.zip I.a)).map (fun e => ∑ p : Z2 L, ∑ q : Z2 L,
          ∫ ω : Ω L W, sameEdgeCutIntegrand L W u ω z e p q ∂(P L W))).sum +
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((pairSplits (I.σ.zip I.a)).map (fun p => ∑ v : Z2 L, ∑ w : Z2 L,
          ∫ ω : Ω L W, pairCutIntegrand L W u ω z p v w ∂(P L W))).sum := by
  have hfun :
      (fun ω : Ω L W => ∑ γ : Coord L W,
        (((gvar L W γ : ℝ) : ℂ) *
          deriv (fun t : ℝ => deriv (fun s : ℝ =>
            gloop L W (HflowBlock L W u (Function.update ω γ s)) z I) t) (ω γ))) =
      (fun ω : Ω L W => ∑ γ : Coord L W,
        (((gvar L W γ : ℝ) : ℂ) *
          Matrix.trace (coordinateSecondWordDeriv L W u ω γ z (I.σ.zip I.a)))) := by
    funext ω
    apply Finset.sum_congr rfl
    intro γ _
    rw [deriv_deriv_gloop_coordinate_eq L W u ω γ hz I hwf]
  rw [hfun]
  exact (integrable_and_integral_gloopSecondWordDeriv_allCuts L W u hu hz I hwf).2

end RBM.Gauss
