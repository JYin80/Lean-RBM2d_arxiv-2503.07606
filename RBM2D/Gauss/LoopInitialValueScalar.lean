/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValue
import RBM2D.Hierarchy.ContractionBasic

/-!
# Scalar initial values for short finite loops

At the zero matrix each signed Green factor is scalar. The first two loop
lengths show the exact powers of the block normalization and the equality
indicator for block labels.
-/

namespace RBM.Gauss

open Matrix Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The zero-matrix Green function is a scalar matrix when `z ≠ 0`. -/
theorem green_zero_eq_scalar (z : ℂ) (hz : z ≠ 0) :
    green (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) z =
      (-z)⁻¹ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
  simp only [green, zero_sub, ← neg_smul]
  have hmul := @Matrix.inv_smul (BlockIndex L W) ℂ _ _ _
    (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (-z)
    (invertibleOfNonzero (neg_ne_zero.mpr hz)) (by simp)
  rw [hmul]
  simp

omit [NeZero W] in
/-- The signed version of the zero-matrix Green identity. -/
theorem Gsig_zero_eq_scalar (z : ℂ) (hz : z ≠ 0) (σ : Bool) :
    Gsig (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) z σ =
      (-(if σ then z else (starRingEnd ℂ) z))⁻¹ •
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
  apply green_zero_eq_scalar L W
  cases σ with
  | true => simpa using hz
  | false =>
      intro hc
      have hc' := congrArg (starRingEnd ℂ) hc
      exact hz (by simpa using hc')

/-- Each normalized block projector has trace one. -/
theorem trace_Eblk_eq_one (a : Z2 L) :
    Matrix.trace (Eblk L W a) = 1 := by
  have h := RBM.trace_mul_Eblk L W
    (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) a
  simp only [one_mul] at h
  rw [h]
  simp only [one_apply, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  field_simp
  simp [Nat.cast_mul, pow_two]

/-- Scalar contributed by a signed Green factor at the initial spectral point. -/
noncomputable def initialGreenScalar (E : ℝ) (σ : Bool) : ℂ :=
  (-(if σ then (E : ℂ) + spectralM E
      else (starRingEnd ℂ) ((E : ℂ) + spectralM E)))⁻¹

private theorem initial_spectral_ne_zero {E : ℝ} (hE : |E| < 2) :
    (E : ℂ) + spectralM E ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  have hp := spectralM_im_pos hE
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at hi
  exact (ne_of_gt hp) hi

/-- Exact one-edge initial value, including the `W⁻²` block normalization. -/
theorem initialLoopValue_one_edge {E : ℝ} (hE : |E| < 2)
    (σ : Bool) (a : Z2 L) :
    initialLoopValue L W E ⟨[σ], [a]⟩ = initialGreenScalar E σ := by
  rw [initialLoopValue_eq_trace_product]
  change Matrix.trace
    (Gsig (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      (E + spectralM E) σ * Eblk L W a * 1) = _
  rw [mul_one]
  rw [Gsig_zero_eq_scalar L W _ (initial_spectral_ne_zero hE) σ]
  simp [initialGreenScalar, trace_Eblk_eq_one]

/-- Two block projectors have nonzero trace exactly when their labels agree. -/
theorem trace_Eblk_mul_Eblk (a b : Z2 L) :
    Matrix.trace (Eblk L W a * Eblk L W b) =
      if a = b then (W : ℂ)⁻¹ ^ 2 else 0 := by
  rw [RBM.Eblk_mul_Eblk L W a b]
  split_ifs <;> simp [trace_Eblk_eq_one]

/-- Exact two-edge initial value, with the block-label equality indicator. -/
theorem initialLoopValue_two_edges {E : ℝ} (hE : |E| < 2)
    (σ₁ σ₂ : Bool) (a b : Z2 L) :
    initialLoopValue L W E ⟨[σ₁, σ₂], [a, b]⟩ =
      initialGreenScalar E σ₁ * initialGreenScalar E σ₂ *
        (if a = b then (W : ℂ)⁻¹ ^ 2 else 0) := by
  rw [initialLoopValue_eq_trace_product]
  change Matrix.trace
    (Gsig (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      (E + spectralM E) σ₁ * Eblk L W a *
      (Gsig 0 (E + spectralM E) σ₂ * Eblk L W b * 1)) = _
  rw [mul_one, Gsig_zero_eq_scalar L W _ (initial_spectral_ne_zero hE) σ₁,
    Gsig_zero_eq_scalar L W _ (initial_spectral_ne_zero hE) σ₂]
  simp [initialGreenScalar, trace_Eblk_mul_Eblk, mul_assoc]
  split_ifs <;> ring

/-- A nonempty initial loop has a nonzero value at a bulk spectral point. -/
example : initialLoopValue 1 1 0
    ⟨[true], [((0, 0) : Z2 1)]⟩ ≠ 0 := by
  rw [initialLoopValue_one_edge 1 1 (by norm_num : |(0 : ℝ)| < 2)]
  unfold initialGreenScalar
  simp only [ite_true]
  exact inv_ne_zero (neg_ne_zero.mpr
    (initial_spectral_ne_zero (by norm_num : |(0 : ℝ)| < 2)))

end RBM.Gauss
