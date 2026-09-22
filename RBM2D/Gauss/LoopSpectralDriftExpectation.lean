/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopSpectralDriftCuts
import RBM2D.Gauss.LoopEnvelope

/-!
# Expected spectral drift as a finite sum of expected cut loops

The whole-space resolvent envelope justifies moving both finite sums through
the Gaussian expectation. No generator identity is asserted here.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
private theorem integrable_list_sum {α : Type*} (μ : Measure (Ω L W))
    (l : List α) (f : α → Ω L W → ℂ)
    (hf : ∀ a ∈ l, Integrable (f a) μ) :
    Integrable (fun ω => (l.map fun a => f a ω).sum) μ := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hf a (by simp)).add (ih (by
        intro b hb
        exact hf b (by simp [hb])))

omit [NeZero L] [NeZero W] in
private theorem integral_list_sum {α : Type*} (μ : Measure (Ω L W))
    (l : List α) (f : α → Ω L W → ℂ)
    (hf : ∀ a ∈ l, Integrable (f a) μ) :
    ∫ ω, (l.map fun a => f a ω).sum ∂μ =
      (l.map fun a => ∫ ω, f a ω ∂μ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : Integrable (f a) μ := hf a (by simp)
      have hl : ∀ b ∈ l, Integrable (f b) μ := by
        intro b hb
        exact hf b (by simp [hb])
      have hlsum := integrable_list_sum L W μ l f hl
      simp only [List.map_cons, List.sum_cons]
      rw [integral_add ha hlsum, ih hl]

omit [NeZero L] in
private theorem spectral_split_position_le (I : LoopIdx (Z2 L)) (hI : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a)) :
    s.pre.length + 1 ≤ I.length := by
  have hrec := spectralEdgeSplits_reconstruct L (I.σ.zip I.a) s hs
  have hlen := congrArg List.length hrec
  simp only [List.length_append, List.length_cons, List.length_zip, LoopIdx.WF] at hlen hI
  rw [hI, min_self] at hlen
  simp only [LoopIdx.length]
  omega

/-- Every valid one-edge cut loop is integrable at a nonreal spectral point. -/
theorem integrable_spectral_cut_loop {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a)) (b : Z2 L) :
    Integrable (fun ω : Ω L W =>
      gloop L W (HflowBlock L W u ω) (spectralZ E u)
        (I.cutGlue (s.pre.length + 1) b)) (P L W) := by
  have hpos : 1 ≤ s.pre.length + 1 := by omega
  have hle := spectral_split_position_le L I hI s hs
  have hcut := hI.cutGlue b hpos hle
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hη : 0 < |(spectralZ E u).im| := abs_pos.mpr hz
  apply Integrable.of_bound
    (measurable_gloop_HflowBlock_sample L W u hz
      (I.cutGlue (s.pre.length + 1) b) hcut).aestronglyMeasurable
    ((((L * W) ^ 2 : ℕ) : ℝ) *
      (|(spectralZ E u).im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^
        (I.cutGlue (s.pre.length + 1) b).a.length)
  exact Filter.Eventually.of_forall fun ω =>
    norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
      hη le_rfl (I.cutGlue (s.pre.length + 1) b) hcut

/-- Gaussian expectation of spectral drift, with its exact signed-edge coefficients. -/
theorem integral_trace_spectralWordDeriv_eq_sum_expected_cuts
    {E u : ℝ} (hE : |E| < 2) (_hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hI : I.WF) :
    ∫ ω : Ω L W,
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) ∂(P L W) =
      ((spectralEdgeSplits L (I.σ.zip I.a)).map fun s =>
        -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
          ∑ b : Z2 L, ∫ ω : Ω L W,
            gloop L W (HflowBlock L W u ω) (spectralZ E u)
              (I.cutGlue (s.pre.length + 1) b) ∂(P L W)).sum := by
  let splits := spectralEdgeSplits L (I.σ.zip I.a)
  let C : SpectralEdgeSplit L → ℂ := fun s =>
    -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2)
  let F : SpectralEdgeSplit L → Ω L W → ℂ := fun s ω =>
    C s * ∑ b : Z2 L,
      gloop L W (HflowBlock L W u ω) (spectralZ E u)
        (I.cutGlue (s.pre.length + 1) b)
  have hcut : ∀ s ∈ splits, ∀ b : Z2 L,
      Integrable (fun ω : Ω L W =>
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          (I.cutGlue (s.pre.length + 1) b)) (P L W) := by
    intro s hs b
    exact integrable_spectral_cut_loop L W hE hu1 I hI s hs b
  have hF : ∀ s ∈ splits, Integrable (F s) (P L W) := by
    intro s hs
    exact (integrable_finsetSum Finset.univ (fun b _ => hcut s hs b)).const_mul (C s)
  have hinner : ∀ s ∈ splits,
      ∫ ω : Ω L W, F s ω ∂(P L W) =
        C s * ∑ b : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            (I.cutGlue (s.pre.length + 1) b) ∂(P L W) := by
    intro s hs
    simp only [F, integral_const_mul]
    congr 1
    exact integral_finsetSum Finset.univ (fun b _ => hcut s hs b)
  calc
    _ = ∫ ω : Ω L W, (splits.map fun s => F s ω).sum ∂(P L W) := by
      simp_rw [trace_spectralWordDeriv_eq_sum_original_cuts L W _ E u I hI]
      rfl
    _ = (splits.map fun s => ∫ ω : Ω L W, F s ω ∂(P L W)).sum :=
      integral_list_sum L W (P L W) splits F hF
    _ = _ := by
      simp only [List.map_congr_left hinner]
      rfl

end RBM.Gauss
