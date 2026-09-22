/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.Loops

/-!
# Algebraic resolvent Ward identity for two-dimensional loops

The resolvent difference is `2iη` times the product of the two Green
functions. Summing the second block label of a `(+,-)` two-loop removes its
`E_b` with the dimension-correct factor `W⁻²`.
-/

namespace RBM

open Matrix Finset

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent identity for two spectral parameters. -/
theorem green_sub_green {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z - green H w =
      (z - w) • (green H z * green H w) := by
  have hz' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hz)
  have hw' : (H - w • (1 : Matrix n n ℂ)) * green H w = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hw)
  calc
    green H z - green H w =
        green H z * ((H - w • (1 : Matrix n n ℂ)) * green H w) -
          (green H z * (H - z • (1 : Matrix n n ℂ))) * green H w := by
        rw [hz', hw', Matrix.one_mul, Matrix.mul_one]
    _ = green H z * ((H - w • (1 : Matrix n n ℂ)) -
          (H - z • (1 : Matrix n n ℂ))) * green H w := by noncomm_ring
    _ = green H z * ((z - w) • (1 : Matrix n n ℂ)) * green H w := by
        congr 2
        module
    _ = (z - w) • (green H z * green H w) := by
        simp

/-- The conjugate resolvent identity in the order `G(z̄)G(z)`. -/
theorem green_sub_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z) =
      (2 * Complex.I * (z.im : ℂ)) •
        (green H ((starRingEnd ℂ) z) * green H z) := by
  have h := green_sub_green hz' hz
  have hc : (2 * Complex.I * (z.im : ℂ)) =
      -((starRingEnd ℂ) z - z) := by
    have h0 := Complex.sub_conj z
    push_cast at h0
    linear_combination -h0
  rw [hc, neg_smul, ← h]
  abel

/-- The traced Ward identity against any matrix observable. -/
theorem trace_green_sub_trace_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ)))
    (A : Matrix n n ℂ) :
    Matrix.trace (green H z * A) -
      Matrix.trace (green H ((starRingEnd ℂ) z) * A) =
      (2 * Complex.I * (z.im : ℂ)) *
        Matrix.trace (green H ((starRingEnd ℂ) z) * green H z * A) := by
  have h := congrArg (fun M : Matrix n n ℂ => Matrix.trace (M * A))
    (green_sub_green_conj' hz hz')
  simpa [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc] using h

end Resolvent

section TwoLoop

variable (L W : ℕ) [NeZero L]

/-- The summed `(+,-)` two-loop Ward identity. The factor `2iη` is essential:
`z - conj z = 2iη`; summing the final block insertion contributes `W⁻²`. -/
theorem sum_gloop_two_ward
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (a : Z2 L) :
    (2 * Complex.I * (z.im : ℂ)) *
      ∑ b : Z2 L, gloop L W H z ⟨[true, false], [a, b]⟩ =
      ((W : ℂ)⁻¹ ^ 2) *
        (Matrix.trace (green H z * Eblk L W a) -
          Matrix.trace (green H ((starRingEnd ℂ) z) * Eblk L W a)) := by
  have hrot : ∀ b : Z2 L,
      gloop L W H z ⟨[true, false], [a, b]⟩ =
        gloop L W H z ⟨[false, true], [b, a]⟩ :=
    fun b => gloop_rotate true a rfl
  simp_rw [hrot]
  rw [sum_gloop_head,
    trace_green_sub_trace_green_conj' hz hz' (Eblk L W a)]
  have hprod : gloopProd L W H z ⟨[true], [a]⟩ =
      green H z * Eblk L W a := by
    simp [gloopProd_cons, gloopProd_nil]
  rw [hprod]
  change (2 * Complex.I * (z.im : ℂ)) *
      (((W : ℂ)⁻¹ ^ 2) *
        Matrix.trace (green H ((starRingEnd ℂ) z) *
          (green H z * Eblk L W a))) = _
  rw [← Matrix.mul_assoc]
  ring

/-- The corrected `G`-loop Ward identity at arbitrary length with first
sign `+` and last sign `−`. The middle signs and labels have equal lengths,
so both sides are well-formed loops. -/
theorem sum_gloop_ward_last
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (μ : List Bool) (x : Z2 L) (a' : List (Z2 L))
    (hμ : μ.length = a'.length) :
    (2 * Complex.I * (z.im : ℂ)) *
      ∑ b : Z2 L,
        gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩ =
      ((W : ℂ)⁻¹ ^ 2) *
        (gloop L W H z ⟨true :: μ, x :: a'⟩ -
          gloop L W H z ⟨false :: μ, x :: a'⟩) := by
  let P := gloopProd L W H z ⟨μ, a'⟩
  have hlen : (true :: μ).length = (x :: a').length := by simp [hμ]
  have hrot : ∀ b : Z2 L,
      gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩ =
        gloop L W H z ⟨false :: true :: μ, b :: x :: a'⟩ := by
    intro b
    exact (gloop_rotate (L := L) (W := W) (H := H) (z := z)
      false b hlen).symm
  simp_rw [hrot]
  rw [sum_gloop_head]
  have hprod : gloopProd L W H z ⟨true :: μ, x :: a'⟩ =
      green H z * Eblk L W x * P := by
    simp [P, gloopProd_cons]
  rw [hprod]
  have hplus : gloop L W H z ⟨true :: μ, x :: a'⟩ =
      Matrix.trace (green H z * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons, Gsig_true]
  have hminus : gloop L W H z ⟨false :: μ, x :: a'⟩ =
      Matrix.trace (green H ((starRingEnd ℂ) z) * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons, Gsig_false]
  rw [hplus, hminus]
  have htrace := trace_green_sub_trace_green_conj' hz hz' (Eblk L W x * P)
  simp only [Matrix.mul_assoc] at htrace ⊢
  simp only [Gsig_false]
  rw [htrace]
  ring

/-- The literal divided form of the corrected `(WI_calL)` for nonreal `z`
and positive block width `W`. -/
theorem sum_gloop_ward_last_div [NeZero W]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hη : z.im ≠ 0)
    (μ : List Bool) (x : Z2 L) (a' : List (Z2 L))
    (hμ : μ.length = a'.length) :
    (∑ b : Z2 L,
      gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) =
      (gloop L W H z ⟨true :: μ, x :: a'⟩ -
        gloop L W H z ⟨false :: μ, x :: a'⟩) /
        (2 * Complex.I * (W : ℂ) ^ 2 * (z.im : ℂ)) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hηC : (z.im : ℂ) ≠ 0 := by exact_mod_cast hη
  have hD : 2 * Complex.I * (W : ℂ) ^ 2 * (z.im : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, hW, hηC]
  apply (eq_div_iff hD).2
  have hbase := sum_gloop_ward_last L W hz hz' μ x a' hμ
  calc
    (∑ b : Z2 L,
      gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) *
        (2 * Complex.I * (W : ℂ) ^ 2 * (z.im : ℂ)) =
          (W : ℂ) ^ 2 * ((2 * Complex.I * (z.im : ℂ)) *
            ∑ b : Z2 L,
              gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) := by ring
    _ = (W : ℂ) ^ 2 * (((W : ℂ)⁻¹ ^ 2) *
          (gloop L W H z ⟨true :: μ, x :: a'⟩ -
            gloop L W H z ⟨false :: μ, x :: a'⟩)) := by rw [hbase]
    _ = gloop L W H z ⟨true :: μ, x :: a'⟩ -
          gloop L W H z ⟨false :: μ, x :: a'⟩ := by field_simp

end TwoLoop

end RBM
