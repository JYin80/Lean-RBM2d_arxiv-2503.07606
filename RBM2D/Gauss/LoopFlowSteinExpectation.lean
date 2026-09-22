/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopFlowCoordinateChain
import RBM2D.Gauss.LoopCoordinateSteinSum

/-!
# Expected samplewise loop-flow derivative

The matrix-flow term is replaced using finite-coordinate Gaussian Stein. The
left side is an expectation of a samplewise derivative, not a derivative of
expectation.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

private noncomputable def driftA (η : ℝ) : ℝ :=
  η⁻¹ * ((W : ℝ)⁻¹ ^ 2)

private noncomputable def driftD (E η : ℝ) : ℝ :=
  (η⁻¹ * ‖spectralM E‖ * η⁻¹) * ((W : ℝ)⁻¹ ^ 2)

/-- A deterministic recursive bound for the spectral drift of a word. -/
noncomputable def spectralWordBound (E η : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => driftD W E η * (driftA W η) ^ n +
      driftA W η * spectralWordBound E η n

omit [NeZero W] in
private theorem driftA_nonneg {η : ℝ} (hη : 0 < η) :
    0 ≤ driftA W η := by unfold driftA; positivity

omit [NeZero W] in
private theorem driftD_nonneg {E η : ℝ} (hη : 0 < η) :
    0 ≤ driftD W E η := by unfold driftD; positivity

omit [NeZero W] in
private theorem spectralWordBound_nonneg {E η : ℝ} (hη : 0 < η)
    (n : ℕ) : 0 ≤ spectralWordBound W E η n := by
  induction n with
  | zero => simp [spectralWordBound]
  | succ n ih =>
      rw [spectralWordBound]
      exact add_nonneg
        (mul_nonneg (driftD_nonneg W hη) (pow_nonneg (driftA_nonneg W hη) _))
        (mul_nonneg (driftA_nonneg W hη) ih)

/-- The spectral drift of one signed factor is continuous in the sample. -/
theorem continuous_gsigSpectralFlowDeriv_sample (E u : ℝ)
    (hE : |E| < 2) (hu1 : u < 1) (σ : Bool) :
    Continuous fun ω : Ω L W => gsigSpectralFlowDeriv L W ω E u σ := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hG := continuous_Gsig_HflowBlock_sample L W u hz σ
  change Continuous fun ω : Ω L W =>
    -(Gsig (HflowBlock L W u ω) (spectralZ E u) σ *
      (spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
      Gsig (HflowBlock L W u ω) (spectralZ E u) σ)
  exact ((hG.mul continuous_const).mul hG).neg

/-- The finite spectral drift word is continuous in the sample. -/
theorem continuous_spectralWordDeriv_sample (E u : ℝ)
    (hE : |E| < 2) (hu1 : u < 1) (l : List (Bool × Z2 L)) :
    Continuous fun ω : Ω L W => spectralWordDeriv L W ω E u l := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact (((continuous_gsigSpectralFlowDeriv_sample L W E u hE hu1 p.1).mul
        continuous_const).mul (continuous_foldr_HflowBlock_sample L W u hz l)).add
        (((continuous_Gsig_HflowBlock_sample L W u hz p.1).mul
          continuous_const).mul ih)

private theorem norm_spectral_head_le {E u η : ℝ} (hη : 0 < η)
    (ω : Ω L W) (hz : η ≤ |(spectralZ E u).im|)
    (p : Bool × Z2 L) :
    ‖gsigSpectralFlowDeriv L W ω E u p.1 * Eblk L W p.2‖ ≤
      driftD W E η := by
  let G := Gsig (HflowBlock L W u ω) (spectralZ E u) p.1
  let M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    spectralMSign E p.1 • 1
  let B := Eblk L W p.2
  have hG : ‖G‖ ≤ η⁻¹ :=
    norm_Gsig_le_inv_eta L W (HflowBlock_isHermitian L W u ω) hη hz p.1
  have hM : ‖M‖ = ‖spectralM E‖ := by
    have hm : ‖spectralMSign E p.1‖ = ‖spectralM E‖ := by
      cases p.1 <;> simp [spectralMSign]
    simp [M, norm_smul, hm]
  have hB : ‖B‖ ≤ (W : ℝ)⁻¹ ^ 2 := norm_Eblk_le_inv_W_sq L W p.2
  change ‖-(G * M * G) * B‖ ≤ driftD W E η
  calc
    ‖-(G * M * G) * B‖ ≤ ‖-(G * M * G)‖ * ‖B‖ := norm_mul_le _ _
    _ = ‖G * M * G‖ * ‖B‖ := by rw [norm_neg]
    _ ≤ (‖G‖ * ‖M‖ * ‖G‖) * ‖B‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (η⁻¹ * ‖M‖ * η⁻¹) * ‖B‖ := by
      have hq : 0 ≤ η⁻¹ := by positivity
      have hgm : ‖G‖ * ‖M‖ ≤ η⁻¹ * ‖M‖ :=
        mul_le_mul_of_nonneg_right hG (norm_nonneg M)
      have hggm : ‖G‖ * ‖M‖ * ‖G‖ ≤ η⁻¹ * ‖M‖ * η⁻¹ :=
        mul_le_mul hgm hG (norm_nonneg G) (mul_nonneg hq (norm_nonneg M))
      exact mul_le_mul_of_nonneg_right hggm (norm_nonneg B)
    _ ≤ (η⁻¹ * ‖M‖ * η⁻¹) * ((W : ℝ)⁻¹ ^ 2) := by
      have hq : 0 ≤ η⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hB
        (mul_nonneg (mul_nonneg hq (norm_nonneg M)) hq)
    _ = (η⁻¹ * ‖spectralM E‖ * η⁻¹) * ((W : ℝ)⁻¹ ^ 2) := by rw [hM]
    _ = driftD W E η := rfl

/-- Deterministic sample-uniform bound for the finite spectral drift word. -/
theorem norm_spectralWordDeriv_le {E u η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) (l : List (Bool × Z2 L))
    (ω : Ω L W) :
    ‖spectralWordDeriv L W ω E u l‖ ≤ spectralWordBound W E η l.length := by
  induction l with
  | nil => simp [spectralWordDeriv, spectralWordBound]
  | cons p l ih =>
      have hD := norm_spectral_head_le L W hη ω hz p
      have hA := norm_Gsig_le_inv_eta L W
        (HflowBlock_isHermitian L W u ω) hη hz p.1
      have hE := norm_Eblk_le_inv_W_sq L W p.2
      have htail := norm_foldr_Gsig_Eblk_le L W
        (HflowBlock_isHermitian L W u ω) hη hz l
      have htail' :
          ‖l.foldr (fun q M => Gsig (HflowBlock L W u ω) (spectralZ E u) q.1 *
              Eblk L W q.2 * M) 1‖ ≤ driftA W η ^ l.length := by
        simpa only [driftA] using htail
      have hhead :
          ‖Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2‖ ≤
            driftA W η := by
        calc
          _ ≤ ‖Gsig (HflowBlock L W u ω) (spectralZ E u) p.1‖ *
              ‖Eblk L W p.2‖ := norm_mul_le _ _
          _ ≤ _ := by
            unfold driftA
            gcongr
      have hD0 : 0 ≤ driftD W E η := driftD_nonneg W hη
      have hA0 : 0 ≤ driftA W η := driftA_nonneg W hη
      rw [spectralWordDeriv, List.length_cons, spectralWordBound]
      calc
        ‖_ + _‖ ≤
            ‖gsigSpectralFlowDeriv L W ω E u p.1 * Eblk L W p.2 *
              l.foldr (fun q M => Gsig (HflowBlock L W u ω) (spectralZ E u) q.1 *
                Eblk L W q.2 * M) 1‖ +
            ‖(Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2) *
              spectralWordDeriv L W ω E u l‖ := norm_add_le _ _
        _ ≤ ‖gsigSpectralFlowDeriv L W ω E u p.1 * Eblk L W p.2‖ *
              ‖l.foldr (fun q M => Gsig (HflowBlock L W u ω) (spectralZ E u) q.1 *
                Eblk L W q.2 * M) 1‖ +
            ‖Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2‖ *
              ‖spectralWordDeriv L W ω E u l‖ :=
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ driftD W E η * driftA W η ^ l.length +
              driftA W η * spectralWordBound W E η l.length := by gcongr

/-- The traced spectral drift is integrable under the Gaussian product law. -/
theorem integrable_trace_spectralWordDeriv (E u : ℝ) (hE : |E| < 2)
    (hu1 : u < 1) (l : List (Bool × Z2 L)) :
    Integrable (fun ω : Ω L W => Matrix.trace (spectralWordDeriv L W ω E u l))
      (P L W) := by
  have hη : 0 < |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE))]
    exact mul_pos (by linarith) (spectralM_im_pos hE)
  have hm := ((continuous_matrixTrace L W).comp
    (continuous_spectralWordDeriv_sample L W E u hE hu1 l)).measurable
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((Fintype.card (BlockIndex L W) : ℝ) *
      spectralWordBound W E |(spectralZ E u).im| l.length)
  exact Filter.Eventually.of_forall fun ω => by
    calc
      ‖Matrix.trace (spectralWordDeriv L W ω E u l)‖ ≤
          (Fintype.card (BlockIndex L W) : ℝ) *
            ‖spectralWordDeriv L W ω E u l‖ := norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          spectralWordBound W E |(spectralZ E u).im| l.length := by
            exact mul_le_mul_of_nonneg_left
              (norm_spectralWordDeriv_le L W hη le_rfl l ω) (Nat.cast_nonneg _)

omit [NeZero L] [NeZero W] in
-- A Gaussian coordinate times a bounded measurable complex observable is integrable.
private theorem integrable_coord_smul_of_bounded (c : Coord L W)
    (g : Ω L W → ℂ) (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω L W => ω c • g ω) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gvar L W c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (P L W) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have h := hcoord.ofReal.bdd_mul hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  simpa [Complex.real_smul, mul_comm] using h

/-- Stein applied to the first coordinate derivative yields the second derivative. -/
theorem stein_gloop_first_coordinate_derivative (u : ℝ) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∫ ω : Ω L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) ∂(P L W) =
      (gvar L W c : ℝ) • ∫ ω : Ω L W, Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)) ∂(P L W) := by
  let g : Ω L W → ℂ := fun ω =>
    Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))
  let g' : Ω L W → ℂ := fun ω =>
    Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))
  have hgc : Continuous g := (continuous_matrixTrace L W).comp
    (continuous_coordinateWordDeriv_sample L W u c hz _)
  have hg'c : Continuous g' := (continuous_matrixTrace L W).comp
    (continuous_coordinateSecondWordDeriv_sample L W u c hz _)
  have hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h := T.hasFDerivAt.comp_hasDerivAt (ω c)
      (hasDerivAt_coordinateWordDeriv L W u ω c hz (I.σ.zip I.a))
    simpa only [g, g', hT, Function.comp_def] using h
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω : Ω L W, ‖g ω‖ ≤ C := by
    refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
      coordinateFirstWordBound L W u |z.im| c I.a.length, ?_⟩
    intro ω
    exact (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).1
  have hg'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖g' ω‖ ≤ C := by
    refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
      coordinateSecondWordBound L W u |z.im| c I.a.length, ?_⟩
    intro ω
    exact (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).2
  have h := GaussianProduct.stein (gvar L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [hlaw]
  exact h

/-- Finite sum of the second-level Stein identities. -/
theorem stein_gloop_first_coordinate_derivative_sum (u : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∫ ω : Ω L W, ∑ c : Coord L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) ∂(P L W) =
    ∫ ω : Ω L W, ∑ c : Coord L W, (gvar L W c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))
          ∂(P L W) := by
  classical
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hleft (c : Coord L W) : Integrable (fun ω : Ω L W =>
      ω c • Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)))
      (P L W) := by
    have hgb (ω : Ω L W) :
        ‖Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))‖ ≤
          (((L * W) ^ 2 : ℕ) : ℝ) *
            coordinateFirstWordBound L W u |z.im| c I.a.length :=
      (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).1
    exact integrable_coord_smul_of_bounded L W c _
      ((continuous_matrixTrace L W).comp
        (continuous_coordinateWordDeriv_sample L W u c hz _)).measurable hgb
  have hright (c : Coord L W) : Integrable (fun ω : Ω L W =>
      (gvar L W c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) (P L W) := by
    exact ((integrable_gloop_coordinate_derivatives L W u c hz I hwf).2).smul
      (gvar L W c : ℝ)
  calc
    ∫ ω : Ω L W, ∑ c : Coord L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) ∂(P L W) =
      ∑ c : Coord L W, ∫ ω : Ω L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) ∂(P L W) := by
          exact integral_finsetSum univ (fun c _ => hleft c)
    _ = ∑ c : Coord L W, (gvar L W c : ℝ) • ∫ ω : Ω L W,
        Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))
          ∂(P L W) := by
          apply sum_congr rfl
          intro c _
          exact stein_gloop_first_coordinate_derivative L W u c hz I hwf
    _ = ∑ c : Coord L W, ∫ ω : Ω L W, (gvar L W c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))
          ∂(P L W) := by simp only [integral_smul]
    _ = ∫ ω : Ω L W, ∑ c : Coord L W, (gvar L W c : ℝ) • Matrix.trace
        (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))
          ∂(P L W) := by
          exact (integral_finsetSum univ (fun c _ => hright c)).symm

/-- Expected samplewise derivative after second-level Stein; the spectral drift remains. -/
theorem expected_samplewise_loop_flow_derivative
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    Integrable (fun ω : Ω L W => deriv (fun v : ℝ =>
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u) (P L W) ∧
    (∫ ω : Ω L W, deriv (fun v : ℝ =>
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u ∂(P L W)) =
      (1 / (2 * u)) • ∫ ω : Ω L W,
        ∑ c : Coord L W, (gvar L W c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv L W u ω c
            (spectralZ E u) (I.σ.zip I.a)) ∂(P L W) +
      ∫ ω : Ω L W,
        Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))
          ∂(P L W) := by
  classical
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hleft : Integrable (fun ω : Ω L W =>
      ∑ c : Coord L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c (spectralZ E u) (I.σ.zip I.a)))
      (P L W) := by
    have hη : 0 < |(spectralZ E u).im| := abs_pos.mpr hz
    apply integrable_finsetSum univ
    intro c _
    have hgb (ω : Ω L W) :
        ‖Matrix.trace (coordinateWordDeriv L W u ω c (spectralZ E u)
            (I.σ.zip I.a))‖ ≤
          (((L * W) ^ 2 : ℕ) : ℝ) *
            coordinateFirstWordBound L W u |(spectralZ E u).im| c I.a.length :=
      (norm_gloop_coordinate_derivatives_le L W hη c le_rfl I hwf ω).1
    exact integrable_coord_smul_of_bounded L W c _
      ((continuous_matrixTrace L W).comp
        (continuous_coordinateWordDeriv_sample L W u c hz _)).measurable hgb
  have hspec : Integrable (fun ω : Ω L W =>
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))) (P L W) :=
    integrable_trace_spectralWordDeriv L W E u hE hu1 (I.σ.zip I.a)
  have hfun : (fun ω : Ω L W => deriv (fun v : ℝ =>
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u) =
      (fun ω : Ω L W => (1 / (2 * u)) •
        (∑ c : Coord L W, ω c • Matrix.trace
          (coordinateWordDeriv L W u ω c (spectralZ E u) (I.σ.zip I.a))) +
        Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a))) := by
    funext ω
    exact loop_flow_derivative_coordinate_chain L W ω hE hu hu1 I hwf
  have hscaled : Integrable (fun ω : Ω L W => (1 / (2 * u)) •
      (∑ c : Coord L W, ω c • Matrix.trace
        (coordinateWordDeriv L W u ω c (spectralZ E u) (I.σ.zip I.a))))
      (P L W) := by
    exact hleft.smul (1 / (2 * u))
  constructor
  · rw [hfun]
    exact hscaled.add hspec
  · rw [hfun, integral_add hscaled hspec, integral_smul]
    rw [stein_gloop_first_coordinate_derivative_sum L W u hz I hwf]

end RBM.Gauss
