/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyCutTotalBound

/-!
# Bounds for the spectral-drift cut family

One spectral cut has `n+1` Green edges. Its block sum contributes the exact
cardinality of the block torus, and the drift coefficient contributes
`‖spectralM E‖ W²`. There are exactly `n` spectral edge positions.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Both signs of the spectral derivative have the same modulus. -/
theorem norm_spectralMSign (E : ℝ) (σ : Bool) :
    ‖spectralMSign E σ‖ = ‖spectralM E‖ := by
  cases σ <;> simp [spectralMSign]

/-- Each expected loop produced by an enumerated spectral cut has the
`n+1`-edge resolvent envelope. -/
theorem norm_integral_spectralCut_gloop_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a)) (q : Z2 L)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (spectralZ E u)
        (I.cutGlue (s.pre.length + 1) q) ∂(P L W)‖ ≤
      cutResolventEnvelope L W η (I.length + 1) := by
  have hcut := spectral_cut_length_WF L I hwf s hs q
  have hbound (ω : Ω L W) := norm_gloop_fixed_le L W u ω hη hz
    (I.cutGlue (s.pre.length + 1) q) hcut.2
  rw [hcut.1] at hbound
  have h := norm_integral_le_of_norm_le_const
    (μ := P L W) (f := fun ω : Ω L W =>
      gloop L W (HflowBlock L W u ω) (spectralZ E u)
        (I.cutGlue (s.pre.length + 1) q))
    (Filter.Eventually.of_forall hbound)
  simpa [cutResolventEnvelope] using h

/-- One spectral edge's signed block sum, with the exact `W²` drift factor. -/
theorem norm_spectralEdgeCut_sum_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a))
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖-(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
      (∑ q : Z2 L, ∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          (I.cutGlue (s.pre.length + 1) q) ∂(P L W))‖ ≤
      ‖spectralM E‖ * (W : ℝ) ^ 2 *
        ((Fintype.card (Z2 L) : ℝ) *
          cutResolventEnvelope L W η (I.length + 1)) := by
  have hcoef : ‖-(spectralMSign E s.edge.1 * (W : ℂ) ^ 2)‖ =
      ‖spectralM E‖ * (W : ℝ) ^ 2 := by
    simp [norm_pow, norm_spectralMSign]
  have hsum : ‖∑ q : Z2 L, ∫ ω : Ω L W,
      gloop L W (HflowBlock L W u ω) (spectralZ E u)
        (I.cutGlue (s.pre.length + 1) q) ∂(P L W)‖ ≤
      (Fintype.card (Z2 L) : ℝ) *
        cutResolventEnvelope L W η (I.length + 1) := by
    calc
      _ ≤ ∑ q : Z2 L, ‖∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            (I.cutGlue (s.pre.length + 1) q) ∂(P L W)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _q : Z2 L, cutResolventEnvelope L W η (I.length + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        exact norm_integral_spectralCut_gloop_le L W I hwf s hs q E u hη hz
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ‖-(spectralMSign E s.edge.1 * (W : ℂ) ^ 2)‖ *
        ‖∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            (I.cutGlue (s.pre.length + 1) q) ∂(P L W)‖ := norm_mul_le _ _
    _ ≤ _ := by rw [hcoef]; gcongr

private theorem list_sum_map_le_card_mul {α : Type*} (l : List α)
    (f : α → ℝ) (C : ℝ) (h : ∀ x ∈ l, f x ≤ C) :
    (l.map f).sum ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        f x + (xs.map f).sum ≤ C + (xs.length : ℝ) * C := add_le_add hx hxs
        _ = ((xs.length : ℝ) + 1) * C := by ring

/-- Sum of norms over every spectral edge position, counted exactly once. -/
theorem sum_all_spectralEdgeCut_norm_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ((spectralEdgeSplits L (I.σ.zip I.a)).map fun s =>
      ‖-(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
        (∑ q : Z2 L, ∫ ω : Ω L W,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            (I.cutGlue (s.pre.length + 1) q) ∂(P L W))‖).sum ≤
      (I.length : ℝ) *
        (‖spectralM E‖ * (W : ℝ) ^ 2 *
          ((Fintype.card (Z2 L) : ℝ) *
            cutResolventEnvelope L W η (I.length + 1))) := by
  have hsum := list_sum_map_le_card_mul
    (spectralEdgeSplits L (I.σ.zip I.a))
    (fun s => ‖-(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
      (∑ q : Z2 L, ∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          (I.cutGlue (s.pre.length + 1) q) ∂(P L W))‖)
    (‖spectralM E‖ * (W : ℝ) ^ 2 *
      ((Fintype.card (Z2 L) : ℝ) *
        cutResolventEnvelope L W η (I.length + 1)))
    (by
      intro s hs
      exact norm_spectralEdgeCut_sum_le L W I hwf s hs E u hη hz)
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.WF, LoopIdx.length] at hwf ⊢
    omega
  simpa only [length_spectralEdgeSplits, hzip] using hsum

private theorem norm_list_map_sum_le {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map fun x => ‖f x‖).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The complete signed spectral-drift cut family obeys the same exact
`n`-position envelope. -/
theorem norm_expectedSpectralCuts_le
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (E u : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E u).im|) :
    ‖expectedSpectralCuts L W E u I‖ ≤
      (I.length : ℝ) *
        (‖spectralM E‖ * (W : ℝ) ^ 2 *
          ((Fintype.card (Z2 L) : ℝ) *
            cutResolventEnvelope L W η (I.length + 1))) := by
  unfold expectedSpectralCuts
  exact (norm_list_map_sum_le _ _).trans
    (sum_all_spectralEdgeCut_norm_le L W I hwf E u hη hz)

end RBM.Gauss
