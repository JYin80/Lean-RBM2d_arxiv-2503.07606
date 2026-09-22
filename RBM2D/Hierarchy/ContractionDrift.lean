/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.Operations

/-!
# Scalar drift insertions and single-edge cut-and-glue loops

At a fixed matrix and spectral parameter, summing the inserted block label
replaces `E_b` by `W⁻² I`. Thus a scalar identity inserted between the two
copies of a Green edge is `W²` times the cut-and-glue loop sum. Both the
positive insertion and the negative sign from resolvent differentiation are
recorded here; no generator or expectation is asserted.
-/

namespace RBM

open Matrix Finset

variable (L W : ℕ) [NeZero L]
variable (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)

/-- Sum over the inserted block at a general one-based Green edge. -/
theorem sum_gloop_cutGlue_split
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a : Z2 L) (h₁ : σ₁.length = a₁.length) :
    ∑ b : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx (Z2 L)).cutGlue
          (σ₁.length + 1) b) =
      ((W : ℂ)⁻¹ ^ 2) *
        Matrix.trace (gloopProd L W H z ⟨σ₁, a₁⟩ *
          (Gsig H z s * (Gsig H z s * Eblk L W a *
            gloopProd L W H z ⟨σ₂, a₂⟩))) := by
  simp_rw [gloop, gloopProd_cutGlue_split L W H z σ₁ σ₂ a₁ a₂ s a _ h₁]
  rw [← Matrix.trace_sum]
  simp only [Matrix.mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_Eblk L W]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul]

/-- A positive scalar insertion `G_s (m I) G_s` has coefficient `m W²`
relative to the sum of single-edge cut-and-glue loops. -/
theorem trace_scalarDrift_cutGlue_split [NeZero W]
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a : Z2 L) (m : ℂ)
    (h₁ : σ₁.length = a₁.length) :
    Matrix.trace (gloopProd L W H z ⟨σ₁, a₁⟩ *
      (Gsig H z s * (m • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
        (Gsig H z s * Eblk L W a * gloopProd L W H z ⟨σ₂, a₂⟩))) =
      (m * (W : ℂ) ^ 2) *
        ∑ b : Z2 L,
          gloop L W H z
            ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx (Z2 L)).cutGlue
              (σ₁.length + 1) b) := by
  rw [sum_gloop_cutGlue_split L W H z σ₁ σ₂ a₁ a₂ s a h₁]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  field_simp

/-- The same identity with the negative sign contributed by differentiating
an inverse matrix. The sign is explicit; this theorem does not formalize the
derivative itself. -/
theorem neg_trace_scalarDrift_cutGlue_split [NeZero W]
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a : Z2 L) (m : ℂ)
    (h₁ : σ₁.length = a₁.length) :
    -Matrix.trace (gloopProd L W H z ⟨σ₁, a₁⟩ *
      (Gsig H z s * (m • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
        (Gsig H z s * Eblk L W a * gloopProd L W H z ⟨σ₂, a₂⟩))) =
      -(m * (W : ℂ) ^ 2) *
        ∑ b : Z2 L,
          gloop L W H z
            ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx (Z2 L)).cutGlue
              (σ₁.length + 1) b) := by
  rw [trace_scalarDrift_cutGlue_split L W H z σ₁ σ₂ a₁ a₂ s a m h₁]
  ring

end RBM
