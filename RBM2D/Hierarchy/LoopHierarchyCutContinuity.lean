/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyIntegral
import RBM2D.Gauss.LoopMomentCont

/-!
# Time continuity of finite expected cut terms

Each cut integrand is a product of two finite resolvent loops. On a compact
time window inside `(0,1)` the spectral gap gives a constant envelope, so
dominated convergence applies to its Gaussian expectation.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Time continuity of any finite loop, including a loop index not separately
certified well formed. Its product uses the paired list `σ.zip a`. -/
theorem continuousOn_gloop_any_window {s t : ℝ} (hst : s ≤ t)
    (ω : Ω L W) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => gloop L W (HflowBlock L W u ω) (z u) I)
      (Set.Icc s t) := by
  let clamp : ℝ → ℝ := fun u => max s (min t u)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ u, clamp u ∈ Set.Icc s t := by
    intro u
    exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
  have hclamp_eq : ∀ u ∈ Set.Icc s t, clamp u = u := by
    intro u hu
    simp [clamp, min_eq_right hu.2, max_eq_right hu.1]
  have hglobal : Continuous (fun u : ℝ =>
      gloop L W (HflowBlock L W u ω) (z (clamp u)) I) :=
    (continuous_matrixTrace L W).comp
      (continuous_gloopProd_Hflow_time L W ω
        (hzcont.comp hclamp_cont)
        (fun u => hzim (clamp u) (hclamp_mem u)) I)
  exact hglobal.continuousOn.congr (fun u hu => by
    change gloop L W (HflowBlock L W u ω) (z u) I =
      gloop L W (HflowBlock L W u ω) (z (clamp u)) I
    rw [hclamp_eq u hu])

/-- A uniform deterministic bound for any finite loop on a spectral window. -/
theorem norm_gloop_any_window_le {s t η : ℝ} (hη : 0 < η)
    {z : ℝ → ℂ} (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : LoopIdx (Z2 L)) {u : ℝ} (hu : u ∈ Set.Icc s t)
    (ω : Ω L W) :
    ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.σ.zip I.a).length := by
  have ht := norm_matrix_trace_le_card_mul
    (gloopProd L W (HflowBlock L W u ω) (z u) I)
  have hw := norm_foldr_Gsig_Eblk_le L W
    (HflowBlock_isHermitian L W u ω) hη (hzlow u hu) (I.σ.zip I.a)
  calc
    ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤
        (Fintype.card (BlockIndex L W) : ℝ) *
          ‖gloopProd L W (HflowBlock L W u ω) (z u) I‖ := ht
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

/-- Dominated continuity for the expectation of a product of two finite loops. -/
theorem continuousOn_integral_gloop_product_window {s t η : ℝ}
    (hst : s ≤ t) (hη : 0 < η) {z : ℝ → ℂ}
    (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I J : LoopIdx (Z2 L)) (k : ℂ) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (z u) I * k *
        gloop L W (HflowBlock L W u ω) (z u) J ∂(P L W))
      (Set.Icc s t) := by
  let C (K : LoopIdx (Z2 L)) : ℝ :=
    (Fintype.card (BlockIndex L W) : ℝ) *
      (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (K.σ.zip K.a).length
  let B : ℝ := C I * ‖k‖ * C J
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable (fun ω : Ω L W =>
        gloop L W (HflowBlock L W u ω) (z u) I * k *
          gloop L W (HflowBlock L W u ω) (z u) J) (P L W) := by
    intro u hu
    have hK (K : LoopIdx (Z2 L)) :
        Continuous (fun ω : Ω L W =>
          gloop L W (HflowBlock L W u ω) (z u) K) :=
      (continuous_matrixTrace L W).comp
        (continuous_gloopProd_HflowBlock_sample L W u (hzim u hu) K)
    exact (((hK I).mul continuous_const).mul (hK J)).measurable.aestronglyMeasurable
  have hbound : ∀ u ∈ Set.Icc s t, ∀ᵐ ω ∂(P L W),
      ‖gloop L W (HflowBlock L W u ω) (z u) I * k *
        gloop L W (HflowBlock L W u ω) (z u) J‖ ≤ B := by
    intro u hu
    exact Filter.Eventually.of_forall fun ω => by
      have hI := norm_gloop_any_window_le L W hη hzlow I hu ω
      have hJ := norm_gloop_any_window_le L W hη hzlow J hu ω
      calc
        ‖gloop L W (HflowBlock L W u ω) (z u) I * k *
            gloop L W (HflowBlock L W u ω) (z u) J‖ ≤
            ‖gloop L W (HflowBlock L W u ω) (z u) I‖ * ‖k‖ *
              ‖gloop L W (HflowBlock L W u ω) (z u) J‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ B := by
          dsimp [B]
          gcongr
  have hcont : ∀ᵐ ω ∂(P L W), ContinuousOn (fun u : ℝ =>
      gloop L W (HflowBlock L W u ω) (z u) I * k *
        gloop L W (HflowBlock L W u ω) (z u) J) (Set.Icc s t) :=
    Filter.Eventually.of_forall fun ω =>
      ((continuousOn_gloop_any_window L W hst ω hzcont hzim I).mul
        continuousOn_const).mul
        (continuousOn_gloop_any_window L W hst ω hzcont hzim J)
  exact MeasureTheory.continuousOn_of_dominated hmeas hbound
    (integrable_const B) hcont

/-- Specialization to the spectral path on a compact interior time window. -/
theorem continuousOn_integral_gloop_product_spectralZ
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I J : LoopIdx (Z2 L)) (k : ℂ) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (spectralZ E u) I * k *
        gloop L W (HflowBlock L W u ω) (spectralZ E u) J ∂(P L W))
      (Set.Icc a b) := by
  let η : ℝ := (1 - b) * (spectralM E).im
  have hη : 0 < η := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc a b, η ≤ |(spectralZ E u).im| := by
    intro u hu
    exact spectralZ_im_gap hE hb hu
  exact continuousOn_integral_gloop_product_window L W hab hη
    (continuous_spectralZ E) hlow I J k

/-- Continuity of each expected summand in a same-edge cut. -/
theorem continuousOn_integral_sameEdgeCutIntegrand
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (e : EdgeSplit (Bool × Z2 L)) (p q : Z2 L) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      sameEdgeCutIntegrand L W u ω (spectralZ E u) e p q ∂(P L W))
      (Set.Icc a b) := by
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  let A : LoopIdx (Z2 L) :=
    ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
      e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩
  let B : LoopIdx (Z2 L) := ⟨[e.selected.1], [q]⟩
  change ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
    gloop L W (HflowBlock L W u ω) (spectralZ E u) A * SB L p q *
      gloop L W (HflowBlock L W u ω) (spectralZ E u) B ∂(P L W))
      (Set.Icc a b)
  exact continuousOn_integral_gloop_product_spectralZ L W hE hab hb A B (SB L p q)

/-- Continuity of each expected summand in a distinct-edge cut. -/
theorem continuousOn_integral_pairCutIntegrand
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (p : PairSplit (Bool × Z2 L)) (v w : Z2 L) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      pairCutIntegrand L W u ω (spectralZ E u) p v w ∂(P L W))
      (Set.Icc a b) := by
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  let I : LoopIdx (Z2 L) :=
    ⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
      I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩
  let A : LoopIdx (Z2 L) :=
    I.cutGlueL (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v
  let B : LoopIdx (Z2 L) :=
    I.cutGlueR (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w
  change ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
    gloop L W (HflowBlock L W u ω) (spectralZ E u) A * SB L v w *
      gloop L W (HflowBlock L W u ω) (spectralZ E u) B ∂(P L W))
      (Set.Icc a b)
  exact continuousOn_integral_gloop_product_spectralZ L W hE hab hb A B (SB L v w)

private theorem continuousOn_list_map_sum {α : Type*} {s : Set ℝ}
    (l : List α) (f : α → ℝ → ℂ)
    (hf : ∀ x ∈ l, ContinuousOn (f x) s) :
    ContinuousOn (fun u => (l.map fun x => f x u).sum) s := by
  induction l with
  | nil => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) s)
  | cons x xs ih =>
      change ContinuousOn
        (fun u => f x u + (xs.map fun y => f y u).sum) s
      exact (hf x (by simp)).add (ih (by
        intro y hy
        exact hf y (by simp [hy])))

/-- The full expected same-edge cut family is continuous on every compact
time window strictly below `1`. -/
theorem continuousOn_expectedSameEdgeCuts
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => expectedSameEdgeCuts L W E u I)
      (Set.Icc a b) := by
  unfold expectedSameEdgeCuts
  apply continuousOn_list_map_sum
  intro e he
  apply continuousOn_finsetSum
  intro p hp
  apply continuousOn_finsetSum
  intro q hq
  exact continuousOn_integral_sameEdgeCutIntegrand L W hE hab hb e p q

/-- The full expected distinct-edge cut family is continuous on every compact
time window strictly below `1`. -/
theorem continuousOn_expectedPairCuts
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => expectedPairCuts L W E u I)
      (Set.Icc a b) := by
  unfold expectedPairCuts
  apply continuousOn_list_map_sum
  intro p hp
  apply continuousOn_finsetSum
  intro v hv
  apply continuousOn_finsetSum
  intro w hw
  exact continuousOn_integral_pairCutIntegrand L W hE hab hb p v w

/-- Dominated continuity for a single expected finite loop. -/
theorem continuousOn_integral_gloop_window {s t η : ℝ}
    (hst : s ≤ t) (hη : 0 < η) {z : ℝ → ℂ}
    (hzcont : Continuous z)
    (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (z u) I ∂(P L W))
      (Set.Icc s t) := by
  let B : ℝ := (Fintype.card (BlockIndex L W) : ℝ) *
    (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.σ.zip I.a).length
  have hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0 := by
    intro u hu
    exact abs_pos.mp (hη.trans_le (hzlow u hu))
  have hmeas : ∀ u ∈ Set.Icc s t,
      AEStronglyMeasurable (fun ω : Ω L W =>
        gloop L W (HflowBlock L W u ω) (z u) I) (P L W) := by
    intro u hu
    exact ((continuous_matrixTrace L W).comp
      (continuous_gloopProd_HflowBlock_sample L W u (hzim u hu) I)).measurable.aestronglyMeasurable
  have hbound : ∀ u ∈ Set.Icc s t, ∀ᵐ ω ∂(P L W),
      ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤ B := by
    intro u hu
    exact Filter.Eventually.of_forall fun ω =>
      norm_gloop_any_window_le L W hη hzlow I hu ω
  have hcont : ∀ᵐ ω ∂(P L W), ContinuousOn (fun u : ℝ =>
      gloop L W (HflowBlock L W u ω) (z u) I) (Set.Icc s t) :=
    Filter.Eventually.of_forall fun ω =>
      continuousOn_gloop_any_window L W hst ω hzcont hzim I
  exact MeasureTheory.continuousOn_of_dominated hmeas hbound
    (integrable_const B) hcont

/-- Continuity of the expectation of any fixed cut loop along the spectral path. -/
theorem continuousOn_integral_gloop_spectralZ
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (spectralZ E u) I ∂(P L W))
      (Set.Icc a b) := by
  let η : ℝ := (1 - b) * (spectralM E).im
  have hη : 0 < η := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc a b, η ≤ |(spectralZ E u).im| := by
    intro u hu
    exact spectralZ_im_gap hE hb hu
  exact continuousOn_integral_gloop_window L W hab hη
    (continuous_spectralZ E) hlow I

/-- The signed expected spectral-drift cut family is continuous on every
compact time window strictly below `1`. -/
theorem continuousOn_expectedSpectralCuts
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => expectedSpectralCuts L W E u I)
      (Set.Icc a b) := by
  unfold expectedSpectralCuts
  apply continuousOn_list_map_sum
  intro s hs
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro q hq
  exact continuousOn_integral_gloop_spectralZ L W hE hab hb
    (I.cutGlue (s.pre.length + 1) q)

/-- All three expected cut families, with their generator coefficients, are
continuous on compact intervals below the singular endpoint `u = 1`. -/
theorem continuousOn_expectedLoopCutRHS
    {E a b : ℝ} (hE : |E| < 2) (hab : a ≤ b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => expectedLoopCutRHS L W E u I)
      (Set.Icc a b) := by
  unfold expectedLoopCutRHS
  exact (((continuousOn_const.mul
    (continuousOn_expectedSameEdgeCuts L W hE hab hb I)).add
    (continuousOn_const.mul
      (continuousOn_expectedPairCuts L W hE hab hb I))).add
    (continuousOn_expectedSpectralCuts L W hE hab hb I))

/-- Unconditional finite-time Duhamel form of the finite expected loop
hierarchy on an interior time interval. -/
theorem expected_gloop_hierarchy_integral_unconditional
    {E a b : ℝ} (hE : |E| < 2) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W b ω) (spectralZ E b) I ∂(P L W)) -
    (∫ ω : Ω L W,
      gloop L W (HflowBlock L W a ω) (spectralZ E a) I ∂(P L W)) =
    ∫ u in a..b,
      (W : ℂ) ^ 2 * expectedSameEdgeCuts L W E u I +
      (W : ℂ) ^ 2 * expectedPairCuts L W E u I +
      expectedSpectralCuts L W E u I := by
  exact expected_gloop_hierarchy_integral_of_continuousOn L W hE ha hab hb I hwf
    (continuousOn_expectedLoopCutRHS L W hE hab.le hb I)

end RBM.Gauss
