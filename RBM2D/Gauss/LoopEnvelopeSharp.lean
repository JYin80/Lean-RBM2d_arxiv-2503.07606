/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopEnvelope

/-!
# A block-normalized trace bound for resolvent loops

The final `Eblk` in a nonempty loop has trace mass one. Retaining it in the trace
removes the full-volume factor from the crude finite-dimensional envelope.
-/

namespace RBM.Gauss

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Real diagonal weight of a normalized two-dimensional block insertion. -/
noncomputable def blockWeight (b : Z2 L) (p : BlockIndex L W) : ℝ :=
  if p.1 = b then (W : ℝ)⁻¹ ^ 2 else 0

omit [NeZero L] [NeZero W] in
theorem blockWeight_nonneg (b : Z2 L) (p : BlockIndex L W) :
    0 ≤ blockWeight L W b p := by
  unfold blockWeight
  split_ifs <;> positivity

omit [NeZero L] [NeZero W] in
theorem Eblk_eq_diagonal_blockWeight (b : Z2 L) :
    Eblk L W b = diagonal (fun p => ((blockWeight L W b p : ℝ) : ℂ)) := by
  have hcast : (((W : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) = (W : ℂ)⁻¹ ^ 2 := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv]
    simp only [Complex.ofReal_natCast]
  ext p q
  simp only [Eblk, blockWeight, diagonal_apply]
  split_ifs <;> simp only [Complex.ofReal_zero, hcast]

/-- The `W²` physical sites in a block cancel its `W⁻²` normalization. -/
theorem sum_blockWeight (b : Z2 L) :
    ∑ p : BlockIndex L W, blockWeight L W b p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [blockWeight]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  field_simp
  norm_num [Nat.cast_mul, pow_two]

/-- Trace against one normalized block insertion costs no volume factor. -/
theorem norm_trace_mul_Eblk_le (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (b : Z2 L) :
    ‖trace (M * Eblk L W b)‖ ≤ ‖M‖ := by
  rw [Eblk_eq_diagonal_blockWeight, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ p, ‖M p p * ((blockWeight L W b p : ℝ) : ℂ)‖
        ≤ ∑ p, ‖M‖ * blockWeight L W b p := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (blockWeight_nonneg L W b p)]
          exact mul_le_mul_of_nonneg_right
            (norm_matrix_entry_le_opNorm M p p) (blockWeight_nonneg L W b p)
    _ = ‖M‖ := by rw [← Finset.mul_sum, sum_blockWeight L W b, mul_one]

/-- A nonempty loop has the paper-scale deterministic envelope. The final block
insertion is kept inside the trace, so no factor involving the number of blocks occurs. -/
theorem norm_gloop_le_sharp {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (hn : 1 ≤ I.a.length) :
    ‖gloop L W H z I‖ ≤
      η⁻¹ ^ I.a.length * ((W : ℝ)⁻¹ ^ 2) ^ (I.a.length - 1) := by
  obtain ⟨σ, a⟩ := I
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hn
  rcases List.eq_nil_or_concat' σ with rfl | ⟨σ', s, rfl⟩
  · simp [LoopIdx.WF] at hwf
  have hpre : σ'.length = a'.length := by simpa [LoopIdx.WF] using hwf
  have hfactor :
      gloop L W H z ⟨σ' ++ [s], a' ++ [b]⟩ =
        trace ((gloopProd L W H z ⟨σ', a'⟩ * Gsig H z s) * Eblk L W b) := by
    rw [gloop, gloopProd_append hpre [s] [b]]
    simp only [gloopProd_cons, gloopProd_nil, mul_one]
    rw [mul_assoc]
  rw [hfactor]
  have hword := norm_foldr_Gsig_Eblk_le L W hH hη hz (σ'.zip a')
  have hG := norm_Gsig_le_inv_eta L W hH hη hz s
  have hlen : (σ'.zip a').length = a'.length := by simp [hpre]
  rw [hlen] at hword
  calc
    ‖trace ((gloopProd L W H z ⟨σ', a'⟩ * Gsig H z s) * Eblk L W b)‖
        ≤ ‖gloopProd L W H z ⟨σ', a'⟩ * Gsig H z s‖ :=
          norm_trace_mul_Eblk_le L W _ b
    _ ≤ ‖gloopProd L W H z ⟨σ', a'⟩‖ * ‖Gsig H z s‖ := norm_mul_le _ _
    _ ≤ (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ a'.length * η⁻¹ := by
          exact mul_le_mul hword hG (norm_nonneg _) (pow_nonneg (by positivity) _)
    _ = η⁻¹ ^ (a' ++ [b]).length * ((W : ℝ)⁻¹ ^ 2) ^
          ((a' ++ [b]).length - 1) := by
          simp [pow_succ, mul_pow]
          ring

/-- The one-edge loop is already bounded independently of `L` and `W`. -/
example {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (b : Z2 L) :
    ‖gloop L W H z ⟨[true], [b]⟩‖ ≤ η⁻¹ := by
  simpa using norm_gloop_le_sharp L W hH hη hz ⟨[true], [b]⟩
    (by simp [LoopIdx.WF]) (by simp)

end RBM.Gauss
