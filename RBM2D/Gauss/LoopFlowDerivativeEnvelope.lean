/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopFlowSteinExpectation

/-!
# An integrable time-neighborhood envelope for samplewise loop derivatives

For fixed `0 < u < 1`, the interval `[u/2, (1+u)/2]` contains `u` in its
interior and stays inside `(0,1)`. The derivative bound is a constant plus a
finite weighted sum of absolute Gaussian coordinates.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The closed neighborhood of a positive time before the singular endpoint. -/
def flowWindow (u : ℝ) : Set ℝ := Set.Icc (u / 2) ((1 + u) / 2)

theorem flowWindow_mem (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    u ∈ flowWindow u := by
  simp only [flowWindow, Set.mem_Icc]
  constructor <;> linarith

theorem flowWindow_strict (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    u / 2 < u ∧ u < (1 + u) / 2 := by
  constructor <;> linarith

theorem flowWindow_subset_Ioo (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    {v : ℝ} (hv : v ∈ flowWindow u) : v ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [flowWindow, Set.mem_Icc] at hv
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- The first-coordinate word bound grows with `√v` on `[0,1]`. -/
theorem coordinateFirstWordBound_le_one (c : Coord L W) {v η : ℝ}
    (hv1 : v ≤ 1) (hη : 0 < η) (n : ℕ) :
    coordinateFirstWordBound L W v η c n ≤
      coordinateFirstWordBound L W 1 η c n := by
  have hsqrt : Real.sqrt v ≤ 1 := by
    have h := Real.sqrt_le_sqrt hv1
    simpa using h
  have hB : ‖Real.sqrt v • coordinateBlock L W c‖ ≤
      ‖Real.sqrt (1 : ℝ) • coordinateBlock L W c‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_one, abs_one]
    exact mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coordinateFirstWordBound]
      have hA : 0 ≤ η⁻¹ * ((W : ℝ)⁻¹ ^ 2) := by positivity
      have hD :
          (η⁻¹ * ‖Real.sqrt v • coordinateBlock L W c‖ * η⁻¹) *
              ((W : ℝ)⁻¹ ^ 2) ≤
          (η⁻¹ * ‖Real.sqrt (1 : ℝ) • coordinateBlock L W c‖ * η⁻¹) *
              ((W : ℝ)⁻¹ ^ 2) := by
        gcongr
      change _ ≤ _
      gcongr
      exact hD

/-- A fixed integrable majorant: one constant plus finitely many absolute coordinates. -/
noncomputable def flowDerivativeEnvelope (E u : ℝ) (I : LoopIdx (Z2 L))
    (ω : Ω L W) : ℝ :=
  let η := (1 - (1 + u) / 2) * (spectralM E).im
  (1 / u) * ∑ c : Coord L W,
    ((((L * W) ^ 2 : ℕ) : ℝ) *
      coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| +
    (((L * W) ^ 2 : ℕ) : ℝ) * spectralWordBound W E η I.a.length

/-- The majorant is integrable by the first absolute moments of the coordinates. -/
theorem integrable_flowDerivativeEnvelope (E u : ℝ)
    (I : LoopIdx (Z2 L)) :
    Integrable (flowDerivativeEnvelope L W E u I) (P L W) := by
  let η := (1 - (1 + u) / 2) * (spectralM E).im
  have hcoord (c : Coord L W) :
      Integrable (fun ω : Ω L W => ω c) (P L W) := by
    have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
      (measurable_pi_apply c).aemeasurable
    have hg : Integrable (fun x : ℝ => x) ((P L W).map fun ω => ω c) := by
      rw [P_map_eval]
      exact RBM.integrable_id_gaussianReal (var := gvar L W c)
    exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  change Integrable (fun ω : Ω L W =>
    (1 / u) * ∑ c : Coord L W,
      ((((L * W) ^ 2 : ℕ) : ℝ) *
        coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| +
      (((L * W) ^ 2 : ℕ) : ℝ) * spectralWordBound W E η I.a.length)
    (P L W)
  apply Integrable.add
  · apply Integrable.const_mul
    apply integrable_finsetSum univ
    intro c _
    exact (hcoord c).abs.const_mul _
  · exact integrable_const _

/-- The explicit majorant bounds the actual samplewise time derivative throughout
the closed neighborhood `[u/2,(1+u)/2]`. -/
theorem norm_samplewise_loop_flow_derivative_le_envelope
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    {v : ℝ} (hv : v ∈ flowWindow u) (ω : Ω L W) :
    ‖deriv (fun t : ℝ =>
      gloop L W (HflowBlock L W t ω) (spectralZ E t) I) v‖ ≤
      flowDerivativeEnvelope L W E u I ω := by
  let η := (1 - (1 + u) / 2) * (spectralM E).im
  have hv' : v ∈ Set.Icc (u / 2) ((1 + u) / 2) := hv
  have hmid : v ∈ Set.Ioo (0 : ℝ) 1 :=
    flowWindow_subset_Ioo u hu hu1 hv
  have ht : (1 + u) / 2 < (1 : ℝ) := by linarith
  have hη : 0 < η := mul_pos (by linarith)
    (spectralM_im_pos hE)
  have hgap : η ≤ |(spectralZ E v).im| :=
    spectralZ_im_gap hE ht hv'
  have hcoef : |1 / (2 * v)| ≤ 1 / u := by
    have hvpos : 0 < 2 * v := by linarith [hmid.1]
    have hcoef' : 1 / (2 * v) ≤ 1 / u := by
      apply (div_le_div_iff₀ hvpos hu).2
      linarith [hv'.1]
    have hcoefpos : 0 < (1 : ℝ) / (2 * v) :=
      div_pos (by norm_num) hvpos
    rwa [abs_of_pos hcoefpos]
  have hD (c : Coord L W) :
      ‖Matrix.trace (coordinateWordDeriv L W v ω c (spectralZ E v)
        (I.σ.zip I.a))‖ ≤
        ((((L * W) ^ 2 : ℕ) : ℝ) *
          coordinateFirstWordBound L W 1 η c I.a.length) := by
    have hb := (norm_gloop_coordinate_derivatives_le L W
      (u := v) hη c hgap I hwf ω).1
    exact hb.trans (mul_le_mul_of_nonneg_left
      (coordinateFirstWordBound_le_one L W c hmid.2.le hη I.a.length)
      (Nat.cast_nonneg _))
  have hsum :
      ‖∑ c : Coord L W, (ω c) • Matrix.trace
          (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a))‖ ≤
        ∑ c : Coord L W,
          ((((L * W) ^ 2 : ℕ) : ℝ) *
            coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| := by
    calc
      ‖∑ c : Coord L W, (ω c) • Matrix.trace
          (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a))‖ ≤
        ∑ c : Coord L W, ‖(ω c) • Matrix.trace
          (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ c : Coord L W,
          ((((L * W) ^ 2 : ℕ) : ℝ) *
            coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| := by
        apply sum_le_sum
        intro c _
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hD c) (abs_nonneg _)
  have hspec :
      ‖Matrix.trace (spectralWordDeriv L W ω E v (I.σ.zip I.a))‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) * spectralWordBound W E η I.a.length := by
    have hb := norm_spectralWordDeriv_le L W hη hgap (I.σ.zip I.a) ω
    have hlen : (I.σ.zip I.a).length = I.a.length := by
      rw [List.length_zip]
      simp only [LoopIdx.WF] at hwf
      rw [hwf, min_self]
    calc
      _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          ‖spectralWordDeriv L W ω E v (I.σ.zip I.a)‖ :=
            norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          spectralWordBound W E η (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]
  rw [(hasDerivAt_gloop_HflowBlock_spectralZ L W ω hE hmid.1 hmid.2 I hwf).deriv]
  rw [loopWordDeriv_split, Matrix.trace_add]
  rw [trace_wordDirectionMap_time_eq_coordinate_sum L W ω hmid.1]
  change ‖(1 / (2 * v)) • (∑ c : Coord L W, (ω c) • Matrix.trace
      (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a))) +
      Matrix.trace (spectralWordDeriv L W ω E v (I.σ.zip I.a))‖ ≤
    (1 / u) * ∑ c : Coord L W,
      ((((L * W) ^ 2 : ℕ) : ℝ) *
        coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| +
      (((L * W) ^ 2 : ℕ) : ℝ) * spectralWordBound W E η I.a.length
  calc
    ‖_ + _‖ ≤ ‖(1 / (2 * v)) • (∑ c : Coord L W, (ω c) • Matrix.trace
        (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a)))‖ +
      ‖Matrix.trace (spectralWordDeriv L W ω E v (I.σ.zip I.a))‖ :=
        norm_add_le _ _
    _ = |1 / (2 * v)| * ‖∑ c : Coord L W, (ω c) • Matrix.trace
        (coordinateWordDeriv L W v ω c (spectralZ E v) (I.σ.zip I.a))‖ +
      ‖Matrix.trace (spectralWordDeriv L W ω E v (I.σ.zip I.a))‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / u) * ∑ c : Coord L W,
        ((((L * W) ^ 2 : ℕ) : ℝ) *
          coordinateFirstWordBound L W 1 η c I.a.length) * |ω c| +
        (((L * W) ^ 2 : ℕ) : ℝ) * spectralWordBound W E η I.a.length := by
      apply add_le_add _ hspec
      exact mul_le_mul hcoef hsum (norm_nonneg _) (by positivity)

end RBM.Gauss
