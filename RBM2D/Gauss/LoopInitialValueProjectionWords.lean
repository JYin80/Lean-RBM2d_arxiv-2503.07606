/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueScalar

/-!
# Arbitrary products of normalized block projectors

Each adjacent pair contributes its block-label equality indicator and one
factor `W⁻²`. A nonempty projector word has trace equal to their product.
-/

namespace RBM.Gauss

open Matrix Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Product of the normalized block projectors in a list. -/
noncomputable def blockProjectorWord (as : List (Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  as.foldr (fun a M => Eblk L W a * M) 1

/-- The explicit product of adjacent equality indicators and `W⁻²` factors.
The empty and singleton lists have coefficient one. -/
noncomputable def adjacentBlockWeight : List (Z2 L) → ℂ
  | [] => 1
  | [_] => 1
  | a :: b :: as =>
      (if a = b then (W : ℂ)⁻¹ ^ 2 else 0) *
        adjacentBlockWeight (b :: as)

omit [NeZero W] in
/-- A nonempty block projector word is a scalar multiple of its first projector. -/
theorem blockProjectorWord_cons (a : Z2 L) (as : List (Z2 L)) :
    blockProjectorWord L W (a :: as) =
      adjacentBlockWeight L W (a :: as) • Eblk L W a := by
  induction as generalizing a with
  | nil => simp [blockProjectorWord, adjacentBlockWeight]
  | cons b bs ih =>
      change Eblk L W a * blockProjectorWord L W (b :: bs) = _
      rw [ih b, mul_smul_comm, RBM.Eblk_mul_Eblk L W a b]
      by_cases hab : a = b
      · simp [adjacentBlockWeight, hab, smul_smul, mul_comm]
      · simp [adjacentBlockWeight, hab]

/-- Trace of an arbitrary nonempty projector word, with all normalization
and equality-indicator factors explicit in `adjacentBlockWeight`. -/
theorem trace_blockProjectorWord_cons (a : Z2 L) (as : List (Z2 L)) :
    Matrix.trace (blockProjectorWord L W (a :: as)) =
      adjacentBlockWeight L W (a :: as) := by
  rw [blockProjectorWord_cons, Matrix.trace_smul, trace_Eblk_eq_one]
  simp

private theorem initial_spectral_ne_zero_here {E : ℝ} (hE : |E| < 2) :
    (E : ℂ) + spectralM E ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  have hp := spectralM_im_pos hE
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at hi
  exact (ne_of_gt hp) hi

omit [NeZero W] in
/-- At time zero, every signed Green factor can be pulled out of the matrix word. -/
theorem initial_green_word_eq_scalar_projectors {E : ℝ} (hE : |E| < 2)
    (l : List (Bool × Z2 L)) :
    l.foldr (fun p M =>
      Gsig (0 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
        (E + spectralM E) p.1 * Eblk L W p.2 * M) 1 =
      (l.map fun p => initialGreenScalar E p.1).prod •
        blockProjectorWord L W (l.map Prod.snd) := by
  induction l with
  | nil => simp [blockProjectorWord]
  | cons p l ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [Gsig_zero_eq_scalar L W _ (initial_spectral_ne_zero_here hE) p.1, ih]
      change ((initialGreenScalar E p.1 •
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) * Eblk L W p.2) *
          ((l.map fun p => initialGreenScalar E p.1).prod •
            blockProjectorWord L W (l.map Prod.snd)) =
        (initialGreenScalar E p.1 *
          (l.map fun p => initialGreenScalar E p.1).prod) •
            (Eblk L W p.2 * blockProjectorWord L W (l.map Prod.snd))
      simp only [smul_mul_assoc, one_mul, mul_smul_comm, smul_smul]
      rw [mul_comm]

/-- General nonempty initial-loop formula: the signed Green scalars multiply,
and each adjacent block-label match contributes exactly one `W⁻²` factor. -/
theorem initialLoopValue_nonempty {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (a : Z2 L) (as : List (Z2 L)) (ha : I.a = a :: as) :
    initialLoopValue L W E I =
      ((I.σ.zip I.a).map fun p => initialGreenScalar E p.1).prod *
        adjacentBlockWeight L W (a :: as) := by
  rw [initialLoopValue_eq_trace_product,
    initial_green_word_eq_scalar_projectors L W hE,
    Matrix.trace_smul]
  have hlabels : (I.σ.zip I.a).map Prod.snd = I.a :=
    List.map_snd_zip hI.ge
  rw [hlabels, ha, trace_blockProjectorWord_cons]
  rfl

omit [NeZero L] [NeZero W] in
/-- Three edges give the equality indicator for all three labels and `W⁻⁴`. -/
theorem adjacentBlockWeight_three (a b c : Z2 L) :
    adjacentBlockWeight L W [a, b, c] =
      if a = b ∧ b = c then ((W : ℂ)⁻¹ ^ 2) ^ 2 else 0 := by
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp [adjacentBlockWeight, hab, hbc, pow_two]

end RBM.Gauss
