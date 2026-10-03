/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RBM2D.Delocalization

/-!
# Minor formulas for the Green's function (Schur complement, (4.7) and (4.9))

The formulas (4.7) and (4.9) of Lemma 4.2 of Horng-Tzer Yau and Jun Yin, *Delocalization of
One-Dimensional Random Band Matrices* [YY_25].  The 2D paper (arXiv:2503.07606) does not
restate these formulas; it uses them through "the proof of these estimates follows that of
Lemma 4.2 in [YY_25], which is dimension-independent" (Section "Estimates for entries of `G`").

Everything here is deterministic linear algebra over an arbitrary finite index type and
field, with no dimension dependence.  Let `M` be invertible with inverse `G`, fix an index
`i`, and let `M^(i)` be the minor of `M` obtained by deleting row and column `i`.

* (4.9)  `G^(i) j k = G j k - G j i * G i k / G i i`                 for `j, k /= i`
* (4.7)  `G i i = (M i i - sum_{k,l /= i} M i k * G^(i) k l * M l i)` inverse

The right-hand side of (4.9) is taken as the definition `RBM.Green.minorGreen` and shown to
be a left inverse of the minor.

## Main results

* `minorGreen_mul_minorMat`, `inv_minorMat`  : (4.9)
* `sum_minorGreen_col`, `green_diag_eq`      : (4.7)
* `minorMat_sub_smul_one`, `inv_minor_resolvent`, `green_diag_paper` : the resolvent versions for
  `M = H - z`
-/

namespace RBM.Green

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]

/-- Summing over every index different from `i` is summing over everything and
subtracting the `i`-th term. -/
theorem sum_subtype_ne (i : n) (f : n → R) :
    ∑ k : {a : n // a ≠ i}, f k.1 = (∑ k, f k) - f i := by
  have h1 : ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {a : n // a ≠ i}, f k.1 :=
    Finset.sum_subtype _ (fun x => by simp) f
  rw [← h1, Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- The minor `M^(i)`: delete row `i` and column `i`. -/
def minorMat (M : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  M.submatrix Subtype.val Subtype.val

/-- The right-hand side of (4.9), taken as a definition.  It is proved below to be the
inverse of `minorMat M i`. -/
def minorGreen (G : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  Matrix.of fun j k => G j.1 k.1 - G j.1 i * G i k.1 / G i i

section Abstract

variable {M G : Matrix n n R}

/-- Row identity coming from `G * M = 1`, with the `i`-th term split off. -/
theorem sum_ne_green_mul (hGM : G * M = 1) (i : n) (a l : n) :
    ∑ k : {b : n // b ≠ i}, G a k.1 * M k.1 l = (if a = l then (1 : R) else 0) - G a i * M i l := by
  rw [sum_subtype_ne i (fun k => G a k * M k l)]
  have h : ∑ k, G a k * M k l = (if a = l then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a l) hGM
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- Row identity coming from `M * G = 1`, with the `i`-th term split off. -/
theorem sum_ne_mul_green (hMG : M * G = 1) (i : n) (a b : n) :
    ∑ k : {c : n // c ≠ i}, M a k.1 * G k.1 b = (if a = b then (1 : R) else 0) - M a i * G i b := by
  rw [sum_subtype_ne i (fun k => M a k * G k b)]
  have h : ∑ k, M a k * G k b = (if a = b then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a b) hMG
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- **(4.9)**, in the form "the candidate is a left inverse of the minor".
Only `G i i /= 0` is needed; invertibility of the minor is a *conclusion*. -/
theorem minorGreen_mul_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    minorGreen G i * minorMat M i = 1 := by
  ext j l
  have hil : (i : n) ≠ l.1 := fun h => l.2 h.symm
  have hjl : ((1 : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R) j l)
      = (if j.1 = l.1 then (1 : R) else 0) := by
    by_cases h : j = l
    · subst h
      simp [Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h, ite_eq_right (fun hh => h (Subtype.ext hh))]
  rw [hjl, Matrix.mul_apply]
  have hsplit : ∑ k : {a : n // a ≠ i}, minorGreen G i j k * minorMat M i k l
      = (∑ k : {a : n // a ≠ i}, G j.1 k.1 * M k.1 l.1)
        - (G j.1 i / G i i) * ∑ k : {a : n // a ≠ i}, G i k.1 * M k.1 l.1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [minorGreen, minorMat, Matrix.of_apply, Matrix.submatrix_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i j.1 l.1, sum_ne_green_mul hGM i i l.1, ite_eq_right hil]
  have hcancel : G j.1 i / G i i * ((0 : R) - G i i * M i l.1) = -(G j.1 i * M i l.1) := by
    rw [zero_sub, mul_neg, neg_inj]
    field_simp
  rw [hcancel]
  ring

/-- **(4.9)**: the inverse of the minor is given by the explicit formula. -/
theorem inv_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    (minorMat M i)⁻¹ = minorGreen G i :=
  Matrix.inv_eq_left_inv (minorGreen_mul_minorMat hGM i hGii)

/-- The column sum `∑_l G^(i)_{kl} M_{li} = -G_{ki}/G_{ii}`, used for (4.7). -/
theorem sum_minorGreen_col (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0)
    (k : {a : n // a ≠ i}) :
    ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i = -(G k.1 i / G i i) := by
  have hsplit : ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i
      = (∑ l : {a : n // a ≠ i}, G k.1 l.1 * M l.1 i)
        - (G k.1 i / G i i) * ∑ l : {a : n // a ≠ i}, G i l.1 * M l.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [minorGreen, Matrix.of_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i k.1 i, sum_ne_green_mul hGM i i i,
    ite_eq_right k.2, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.7)**. -/
theorem green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0) :
    G i i = (M i i - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        M i k.1 * minorGreen G i k l * M l.1 i)⁻¹ := by
  have hinner : ∀ k : {a : n // a ≠ i},
      (∑ l : {a : n // a ≠ i}, M i k.1 * minorGreen G i k l * M l.1 i)
        = M i k.1 * -(G k.1 i / G i i) := by
    intro k
    rw [← sum_minorGreen_col hGM i hGii k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have hstep : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
      M i k.1 * minorGreen G i k l * M l.1 i)
      = ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i) :=
    Finset.sum_congr rfl fun k _ => hinner k
  have hcol : ∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 i = 1 - M i i * G i i := by
    rw [sum_ne_mul_green hMG i i i, ite_eq_left rfl]
  have houter : ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hval : M i i - -(1 / G i i) * (1 - M i i * G i i) = (G i i)⁻¹ := by
    field_simp
    ring
  rw [hstep, houter, hval, inv_inv]

end Abstract

section Resolvent

variable {H : Matrix n n ℂ} {z : ℂ}

omit [Fintype n] in
theorem sub_smul_one_apply_self (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    (H - z • (1 : Matrix n n ℂ)) i i = H i i - z := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]

omit [Fintype n] in
theorem sub_smul_one_apply_ne (H : Matrix n n ℂ) (z : ℂ) {i k : n} (h : i ≠ k) :
    (H - z • (1 : Matrix n n ℂ)) i k = H i k := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h]

omit [Fintype n] in
/-- The minor of `H - z` is `H^(i) - z`: so `minorGreen (green H z) i` really is the
Green's function of the submatrix `H^(i)`, which is what the paper calls `G^(i)`. -/
theorem minorMat_sub_smul_one (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    minorMat (H - z • (1 : Matrix n n ℂ)) i
      = H.submatrix Subtype.val Subtype.val - z • 1 := by
  ext j k
  by_cases h : j = k
  · subst h
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · have h' : j.1 ≠ k.1 := fun hh => h (Subtype.ext hh)
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
      Matrix.one_apply_ne h']

theorem green_mul_self (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ h

theorem self_mul_green (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  Matrix.mul_nonsing_inv _ h

/-- **(4.9)** for the resolvent: `G^(i) = (H^(i) - z)` inverse is given by the explicit
formula in terms of `G`. -/
theorem inv_minor_resolvent (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) :
    (H.submatrix Subtype.val Subtype.val - z • (1 : Matrix {a : n // a ≠ i} _ ℂ))⁻¹
      = minorGreen (green H z) i := by
  rw [← minorMat_sub_smul_one H z i]
  exact inv_minorMat (green_mul_self h) i hGii

/-- **(4.7)** in the paper's notation. -/
theorem green_diag_paper (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) :
    green H z i i = (H i i - z - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i)⁻¹ := by
  have hsum : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        (H - z • (1 : Matrix n n ℂ)) i k.1 * minorGreen (green H z) i k l
          * (H - z • (1 : Matrix n n ℂ)) l.1 i)
      = ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hik : (i : n) ≠ k.1 := fun hh => k.2 hh.symm
    have hli : l.1 ≠ (i : n) := l.2
    rw [sub_smul_one_apply_ne H z hik, sub_smul_one_apply_ne H z hli]
  rw [green_diag_eq (green_mul_self h) (self_mul_green h) i hGii,
    sub_smul_one_apply_self H z i, hsum]

end Resolvent

end RBM.Green
