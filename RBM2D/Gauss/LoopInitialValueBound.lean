/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueSupport
import RBM2D.Gauss.SpectralAlgebra

/-!
# Magnitude of the finite initial-loop value

The explicit bulk spectral root has unit modulus. Consequently every signed
zero-matrix Green scalar has unit modulus, and the initial loop is controlled
only by its normalized block-projector word. A looser spectral-gap bound is
also recorded for estimates that use `Im m` uniformly.
-/

namespace RBM.Gauss

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Each signed initial Green scalar lies on the unit circle in the bulk. -/
theorem norm_initialGreenScalar {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    ‖initialGreenScalar E σ‖ = 1 := by
  have hm : ‖spectralM E‖ = 1 := norm_spectralM hE.le
  have hmul := congrArg norm (spectralM_mul hE.le)
  simp only [norm_mul, hm, one_mul, norm_neg, norm_one] at hmul
  have hz : ‖(E : ℂ) + spectralM E‖ = 1 := by simpa [add_comm] using hmul
  cases σ with
  | true =>
      change ‖(-((E : ℂ) + spectralM E))⁻¹‖ = 1
      rw [norm_inv, norm_neg, hz]
      norm_num
  | false =>
      change ‖(-(starRingEnd ℂ) ((E : ℂ) + spectralM E))⁻¹‖ = 1
      rw [norm_inv, norm_neg]
      have hc : ‖(starRingEnd ℂ) ((E : ℂ) + spectralM E)‖ =
          ‖(E : ℂ) + spectralM E‖ :=
        Complex.norm_conj ((E : ℂ) + spectralM E)
      rw [hc, hz]
      norm_num

omit [NeZero L] in
private theorem norm_initialGreenScalar_prod {E : ℝ} (hE : |E| < 2)
    (l : List (Bool × Z2 L)) :
    ‖(l.map fun p => initialGreenScalar E p.1).prod‖ = 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp [norm_initialGreenScalar hE, ih]

/-- Exact sharp magnitude on a constant-label nonempty loop. -/
theorem norm_initialLoopValue_all_same {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (a : Z2 L) (as : List (Z2 L)) (ha : I.a = a :: as)
    (hsame : ∀ b ∈ as, b = a) :
    ‖initialLoopValue L W E I‖ =
      ((W : ℝ)⁻¹) ^ (2 * as.length) := by
  rw [initialLoopValue_all_same L W hE I hI a as ha hsame, norm_mul,
    norm_initialGreenScalar_prod L hE, one_mul, norm_pow, norm_inv]
  simp

omit [NeZero L] [NeZero W] in
private theorem all_same_of_no_adjacentMismatch
    (a : Z2 L) (as : List (Z2 L))
    (hm : ¬AdjacentMismatch L (a :: as)) :
    ∀ b ∈ as, b = a := by
  induction as generalizing a with
  | nil => simp
  | cons c cs ih =>
      have hac : a = c := by
        by_contra h
        exact hm (Or.inl h)
      have htail : ¬AdjacentMismatch L (c :: cs) := by
        intro h
        exact hm (Or.inr h)
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact hac.symm
      · exact (ih c htail b hmem).trans hac.symm

/-- Sharp whole-space initial-value bound for every nonempty well-formed loop. -/
theorem norm_initialLoopValue_le {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (a : Z2 L) (as : List (Z2 L)) (ha : I.a = a :: as) :
    ‖initialLoopValue L W E I‖ ≤
      ((W : ℝ)⁻¹) ^ (2 * as.length) := by
  by_cases hm : AdjacentMismatch L (a :: as)
  · rw [initialLoopValue_zero_of_adjacentMismatch L W hE I hI a as ha hm,
      norm_zero]
    positivity
  · exact (norm_initialLoopValue_all_same L W hE I hI a as ha
      (all_same_of_no_adjacentMismatch L a as hm)).le

/-- A spectral-gap version of the initial-value bound, useful when all
resolvent estimates are expressed in terms of `Im m`. -/
theorem norm_initialLoopValue_le_gap {E : ℝ} (hE : |E| < 2)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (a : Z2 L) (as : List (Z2 L)) (ha : I.a = a :: as) :
    ‖initialLoopValue L W E I‖ ≤
      ((spectralM E).im)⁻¹ ^ (as.length + 1) *
        ((W : ℝ)⁻¹) ^ (2 * as.length) := by
  have hηpos : 0 < (spectralM E).im := spectralM_im_pos hE
  have hηle : (spectralM E).im ≤ 1 := by
    simpa [norm_spectralM hE.le] using Complex.im_le_norm (spectralM E)
  have hinv : 1 ≤ ((spectralM E).im)⁻¹ := by
    simpa [one_div] using (one_le_div hηpos).2 hηle
  have hpow : 1 ≤ ((spectralM E).im)⁻¹ ^ (as.length + 1) :=
    one_le_pow₀ hinv
  calc
    ‖initialLoopValue L W E I‖ ≤ ((W : ℝ)⁻¹) ^ (2 * as.length) :=
      norm_initialLoopValue_le L W hE I hI a as ha
    _ = 1 * ((W : ℝ)⁻¹) ^ (2 * as.length) := by ring
    _ ≤ ((spectralM E).im)⁻¹ ^ (as.length + 1) *
          ((W : ℝ)⁻¹) ^ (2 * as.length) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)

/-- A one-edge loop at a genuine bulk point has nonzero unit magnitude. -/
example : ‖initialLoopValue 2 2 0
    ⟨[true], [((0, 0) : Z2 2)]⟩‖ = 1 := by
  simpa using norm_initialLoopValue_all_same 2 2
    (by norm_num : |(0 : ℝ)| < 2)
    ⟨[true], [((0, 0) : Z2 2)]⟩ (by rfl)
    ((0, 0) : Z2 2) [] rfl (by simp)

end RBM.Gauss
