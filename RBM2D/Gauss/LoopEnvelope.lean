/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopSampleCont

/-!
# A whole-space envelope for finite resolvent loops

This elementary finite-dimensional bound keeps the block insertion's `W⁻²` factor. It uses
the ordinary trace bound by the full matrix dimension, so it costs a factor `L²` compared
with the sharper paper-scale estimate. The bound is deterministic for every Gaussian sample.
-/

namespace RBM.Gauss

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix entry is bounded by the `ℓ² → ℓ²` operator norm. -/
theorem norm_matrix_entry_le_opNorm (M : Matrix n n ℂ) (p q : n) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

/-- Crude trace bound, with the full dimension as constant. -/
theorem norm_matrix_trace_le_card_mul (M : Matrix n n ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc
    ‖∑ p, M p p‖ ≤ ∑ p, ‖M p p‖ := norm_sum_le _ _
    _ ≤ ∑ _p : n, ‖M‖ := sum_le_sum fun p _ => norm_matrix_entry_le_opNorm M p p
    _ = (Fintype.card n : ℝ) * ‖M‖ := by simp

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- Each normalized block insertion has operator norm at most `W⁻²`. -/
theorem norm_Eblk_le_inv_W_sq (a : Z2 L) :
    ‖Eblk L W a‖ ≤ (W : ℝ)⁻¹ ^ 2 := by
  rw [Eblk, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs with h
  · simp
  · simp

omit [NeZero W] in
/-- Both spectral signs have the same whole-space resolvent bound. -/
theorem norm_Gsig_le_inv_eta {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (σ : Bool) : ‖Gsig H z σ‖ ≤ η⁻¹ := by
  cases σ with
  | true => exact norm_green_le hH hη hz
  | false =>
      apply norm_green_le hH hη
      simpa using hz

/-- Operator norm of a finite signed Green and block-insertion word. -/
theorem norm_foldr_Gsig_Eblk_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (l : List (Bool × Z2 L)) :
    ‖l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)‖
      ≤ (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc
        ‖Gsig H z p.1 * Eblk L W p.2 *
            l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1‖
          ≤ ‖Gsig H z p.1‖ * ‖Eblk L W p.2‖ *
              ‖l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ η⁻¹ * ((W : ℝ)⁻¹ ^ 2) *
              (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length := by
                gcongr
                · exact norm_Gsig_le_inv_eta L W hH hη hz p.1
                · exact norm_Eblk_le_inv_W_sq L W p.2
        _ = (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ l.length *
              (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) := by ring

omit [NeZero W] in
/-- The block-index matrix dimension is `(LW)²`. -/
theorem card_BlockIndex : Fintype.card (BlockIndex L W) = (L * W) ^ 2 := by
  simp [BlockIndex, Z2, pow_two]
  ring

/-- A crude but global finite-loop envelope; no exceptional event is removed. -/
theorem norm_gloop_le_crude {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ‖gloop L W H z I‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by
  have htrace := norm_matrix_trace_le_card_mul (gloopProd L W H z I)
  have hword := norm_foldr_Gsig_Eblk_le L W hH hη hz (I.σ.zip I.a)
  calc
    ‖gloop L W H z I‖
      ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          ‖(I.σ.zip I.a).foldr
            (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1‖ := htrace
    _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hword (Nat.cast_nonneg _)
    _ = (((L * W) ^ 2 : ℕ) : ℝ) *
          (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by
            rw [card_BlockIndex, List.length_zip]
            simp only [LoopIdx.WF] at hwf
            rw [hwf, min_self]

/-- A deterministic loop envelope uniform in time and over every Gaussian sample. -/
theorem norm_gloop_HflowBlock_le_crude_on_Icc {s t η : ℝ} (hη : 0 < η)
    {z : ℝ → ℂ} (hz : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    ∀ u ∈ Set.Icc s t, ∀ ω : Ω L W,
      ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) *
          (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length := by
  intro u hu ω
  exact norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
    hη (hz u hu) I hwf

end RBM.Gauss
