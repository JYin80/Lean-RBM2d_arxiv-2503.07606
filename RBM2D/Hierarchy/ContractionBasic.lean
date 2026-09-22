/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.OperationsPairWord

/-!
# Elementary contraction identities for two-dimensional loop dynamics

The first identity is the finite-matrix contraction used in the one-dimensional
`LoopIto` proof. It is independent of the spatial geometry. The second identity
turns a diagonal contraction into a trace with the paper's normalized block
projector `E_a`, whose coefficient is `W⁻²` in two dimensions.
-/

namespace RBM

open Matrix Finset

/-- Contract two elementary matrix directions in a cyclic trace. -/
theorem trace_mul_single_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℂ) (p q r s : ι) (c e : ℂ) :
    Matrix.trace (A * Matrix.single p q c * C * Matrix.single r s e) =
      c * e * (A s p * C q r) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq]
  ring

/-- A block projector trace is the normalized sum of diagonal entries in
that block. The fiber has `W²` sites, indexed by `Fin W × Fin W`. -/
theorem trace_mul_Eblk (L W : ℕ) [NeZero L]
    (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (a : Z2 L) :
    Matrix.trace (A * Eblk L W a) =
      ((W : ℂ)⁻¹ ^ 2) * ∑ α : Fin W × Fin W, A (a, α) (a, α) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Eblk, Matrix.mul_diagonal]
  rw [Fintype.sum_prod_type]
  simp only [inv_pow, mul_ite, mul_zero, sum_ite_irrel, sum_const_zero,
    sum_ite_eq', mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]
  simp only [mul_comm]

/-- Collapse the site variance contraction to block traces. The `W²`
coefficient cancels one of the two `W⁻²` normalizations from the block
projectors, leaving the `W⁻²` variance at site level. -/
theorem sum_Svar_diag_mul (L W : ℕ) [NeZero L] [NeZero W]
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ i : BlockIndex L W, ∑ j : BlockIndex L W,
        Svar L W i j * (A i i * C j j) =
      (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        Matrix.trace (A * Eblk L W a) * SB L a b *
          Matrix.trace (C * Eblk L W b) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have expand : ∀ (c : ℂ) (f g : Fin W × Fin W → ℂ),
      ∑ α, ∑ β, c * (f α * g β) = c * ((∑ α, f α) * (∑ β, g β)) := by
    intro c f g
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  have split (f : BlockIndex L W → ℂ) :
      ∑ i : BlockIndex L W, f i =
        ∑ a : Z2 L, ∑ α : Fin W × Fin W, f (a, α) := Fintype.sum_prod_type f
  simp only [split, trace_mul_Eblk, Svar_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [expand]
  field_simp

end RBM
