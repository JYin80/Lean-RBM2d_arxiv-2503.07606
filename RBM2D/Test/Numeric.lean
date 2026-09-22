/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Basic

/-!
# Exact nine-site regression for the block propagator

At `L = 3`, each distinct point on a coordinate circle is adjacent. Thus the
five-point stencil consists exactly of pairs sharing one coordinate. The
rational matrix below is defined independently of `RBM.SB`. An inverse at
`ξ = 1/2` was obtained by exact rational Gaussian elimination. Lean checks
the nine origin-row entries and uses simultaneous translation to prove the
full matrix identity. The rational inverse is then matched to `RBM.Theta`.
-/

namespace RBM.Numeric

open Matrix

/-- Independent paper stencil on `Z_3²`: the center and four axial neighbors. -/
def SBq : Matrix (Z2 3) (Z2 3) ℚ :=
  Matrix.of fun a b => if a.1 = b.1 ∨ a.2 = b.2 then 1 / 5 else 0

/-- Exact inverse of `I - S/2`. The diagonal, axial and diagonal-displacement
entries are respectively `13/11`, `7/44`, and `1/22`. -/
def Thetaq : Matrix (Z2 3) (Z2 3) ℚ :=
  Matrix.of fun a b =>
    if a = b then 13 / 11 else
    if a.1 = b.1 ∨ a.2 = b.2 then 7 / 44 else 1 / 22

theorem SBq_add_right (a b c : Z2 3) :
    SBq (a + c) (b + c) = SBq a b := by
  simp only [SBq, Matrix.of_apply, Prod.fst_add, Prod.snd_add,
    add_right_cancel_iff]

theorem Thetaq_add_right (a b c : Z2 3) :
    Thetaq (a + c) (b + c) = Thetaq a b := by
  simp only [Thetaq, Matrix.of_apply, add_right_cancel_iff,
    Prod.fst_add, Prod.snd_add]

/-- Simultaneous translation preserves the rational resolvent product. -/
theorem half_SBq_mul_Thetaq_add_right (a b c : Z2 3) :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (a + c) (b + c) =
      ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) a b := by
  let A : Matrix (Z2 3) (Z2 3) ℚ := 1 - (1 / 2 : ℚ) • SBq
  let e : Z2 3 ≃ Z2 3 := Equiv.addRight c
  have hA : A.submatrix e e = A := by
    ext i j
    change A (i + c) (j + c) = A i j
    simp only [A, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, SBq_add_right]
    simp only [add_right_cancel_iff]
  have hT : Thetaq.submatrix e e = Thetaq := by
    ext i j
    exact Thetaq_add_right i j c
  change (A * Thetaq) (a + c) (b + c) = (A * Thetaq) a b
  calc
    (A * Thetaq) (a + c) (b + c) =
        (A.submatrix e e * Thetaq.submatrix e e) a b := by
      rw [Matrix.submatrix_mul_equiv]
      rfl
    _ = (A * Thetaq) a b := by rw [hA, hT]

private theorem sum_ZMod3 (f : ZMod 3 → ℚ) :
    ∑ x : ZMod 3, f x = f 0 + f 1 + f 2 := by
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide]
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  simp [h01, h02, h12]
  ring

/-- The independent stencil agrees entrywise with the repository's `S^(B)`. -/
theorem SB_three_apply (a b : Z2 3) : SB 3 a b = ((SBq a b : ℚ) : ℂ) := by
  rw [SB_apply, sbKernel]
  have h : (a - b ∈ sbSupport 3) ↔ (a.1 = b.1 ∨ a.2 = b.2) := by
    revert a b
    decide
  change _ = (((if a.1 = b.1 ∨ a.2 = b.2 then 1 / 5 else 0 : ℚ)) : ℂ)
  rw [if_congr h rfl rfl]
  split_ifs <;> norm_num

private theorem zmod3_zero_ne_one : (0 : ZMod 3) ≠ 1 := by decide
private theorem zmod3_zero_ne_two : (0 : ZMod 3) ≠ 2 := by decide
private theorem zmod3_one_ne_two : (1 : ZMod 3) ≠ 2 := by decide
private theorem zmod3_one_ne_zero : (1 : ZMod 3) ≠ 0 := zmod3_zero_ne_one.symm
private theorem zmod3_two_ne_zero : (2 : ZMod 3) ≠ 0 := zmod3_zero_ne_two.symm
private theorem zmod3_two_ne_one : (2 : ZMod 3) ≠ 1 := zmod3_one_ne_two.symm

private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have h : x ∈ ({0, 1, 2} : Finset (ZMod 3)) := by
    rw [← (show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide)]
    simp
  simpa [Finset.mem_insert, Finset.mem_singleton] using h

/-- Exact left-resolvent check at the origin, testing all nine summands. -/
theorem half_SBq_mul_Thetaq_origin :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (0, 0) = 1 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, sum_ZMod3]
  norm_num [SBq, Thetaq, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.mk.injEq, Prod.fst, Prod.snd,
    zmod3_zero_ne_one, zmod3_zero_ne_two, zmod3_one_ne_two,
    zmod3_one_ne_zero, zmod3_two_ne_zero, zmod3_two_ne_one]

/-- An axial off-diagonal resolvent entry vanishes. -/
theorem half_SBq_mul_Thetaq_axis :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (1, 0) = 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, sum_ZMod3]
  norm_num [SBq, Thetaq, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.mk.injEq, Prod.fst, Prod.snd,
    zmod3_zero_ne_one, zmod3_zero_ne_two, zmod3_one_ne_two,
    zmod3_one_ne_zero, zmod3_two_ne_zero, zmod3_two_ne_one]

/-- A two-coordinate off-diagonal resolvent entry vanishes. -/
theorem half_SBq_mul_Thetaq_corner :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (1, 1) = 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, sum_ZMod3]
  norm_num [SBq, Thetaq, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.mk.injEq, Prod.fst, Prod.snd,
    zmod3_zero_ne_one, zmod3_zero_ne_two, zmod3_one_ne_two,
    zmod3_one_ne_zero, zmod3_two_ne_zero, zmod3_two_ne_one]

macro "check_origin_entry" : tactic =>
  `(tactic| (simp only [Matrix.mul_apply, Fintype.sum_prod_type, sum_ZMod3]
             norm_num [SBq, Thetaq, Matrix.sub_apply, Matrix.smul_apply,
               Matrix.one_apply, Prod.mk.injEq, Prod.fst, Prod.snd,
               zmod3_zero_ne_one, zmod3_zero_ne_two, zmod3_one_ne_two,
               zmod3_one_ne_zero, zmod3_two_ne_zero, zmod3_two_ne_one]))

private theorem origin_01 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (0, 1) = 0 := by
  check_origin_entry

private theorem origin_02 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (0, 2) = 0 := by
  check_origin_entry

private theorem origin_12 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (1, 2) = 0 := by
  check_origin_entry

private theorem origin_20 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (2, 0) = 0 := by
  check_origin_entry

private theorem origin_21 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (2, 1) = 0 := by
  check_origin_entry

private theorem origin_22 :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) (2, 2) = 0 := by
  check_origin_entry

/-- The entire origin row of the resolvent product, nine rational entries. -/
theorem half_SBq_mul_Thetaq_zero_row (b : Z2 3) :
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0, 0) b =
      (1 : Matrix (Z2 3) (Z2 3) ℚ) (0, 0) b := by
  rcases b with ⟨b₁, b₂⟩
  rcases zmod3_cases b₁ with h₁ | h₁ | h₁ <;>
    rcases zmod3_cases b₂ with h₂ | h₂ | h₂ <;>
    subst b₁ <;> subst b₂
  · simpa [Matrix.one_apply] using half_SBq_mul_Thetaq_origin
  · simpa [Matrix.one_apply, zmod3_zero_ne_one] using origin_01
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_two] using origin_02
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_one] using half_SBq_mul_Thetaq_axis
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_one] using half_SBq_mul_Thetaq_corner
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_one] using origin_12
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_two] using origin_20
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_two] using origin_21
  · simpa [Matrix.one_apply, Prod.mk.injEq, zmod3_zero_ne_two] using origin_22

/-- Exact rational left inverse at all nine sites, reduced to one row by
simultaneous translation. -/
theorem half_SBq_mul_Thetaq :
    (1 - (1 / 2 : ℚ) • SBq) * Thetaq = 1 := by
  ext a b
  have hshift := half_SBq_mul_Thetaq_add_right a b (-a)
  have hshift' :
      ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0 : Z2 3) (b - a) =
        ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) a b := by
    simpa [sub_eq_add_neg] using hshift
  calc
    ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) a b =
        ((1 - (1 / 2 : ℚ) • SBq) * Thetaq) (0 : Z2 3) (b - a) := hshift'.symm
    _ = (1 : Matrix (Z2 3) (Z2 3) ℚ) (0 : Z2 3) (b - a) := by
      exact half_SBq_mul_Thetaq_zero_row (b - a)
    _ = (1 : Matrix (Z2 3) (Z2 3) ℚ) a b := by
      simp [Matrix.one_apply, sub_eq_zero, eq_comm]

theorem Thetaq_mul_half_SBq :
    Thetaq * (1 - (1 / 2 : ℚ) • SBq) = 1 :=
  mul_eq_one_comm.mp half_SBq_mul_Thetaq

/-- The explicit rational inverse is exactly the paper's complex propagator
at `L = 3` and `ξ = 1/2`. -/
theorem Theta_three_half (a b : Z2 3) :
    Theta 3 (1 / 2) a b = ((Thetaq a b : ℚ) : ℂ) := by
  let B : Matrix (Z2 3) (Z2 3) ℂ := fun x y => ((Thetaq x y : ℚ) : ℂ)
  have h' : ∀ x y : Z2 3, ∑ k, ((Thetaq x k : ℚ) : ℂ)
      * ((if k = y then 1 else 0) - 1 / 2 * ((SBq k y : ℚ) : ℂ)) =
        if x = y then 1 else 0 := by
    intro x y
    have h := congrArg (fun q : ℚ => (q : ℂ))
      (congrFun (congrFun Thetaq_mul_half_SBq x) y)
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at h
    simpa only [apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_one, Rat.cast_zero,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
      Rat.cast_ofNat] using h
  have hmul : B * (1 - (1 / 2 : ℂ) • SB 3) = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, SB_three_apply]
    exact h' x y
  have h := eq_Theta_of_mul 3 (by norm_num) (ξ := 1 / 2)
    (by norm_num) hmul
  rw [← h]

/-- The origin row of the proposed inverse has mass `(1 - 1/2)⁻¹ = 2`. -/
theorem sum_Thetaq_origin : ∑ b : Z2 3, Thetaq (0, 0) b = 2 := by
  simp only [Fintype.sum_prod_type, sum_ZMod3]
  norm_num [Thetaq, Prod.mk.injEq, Prod.fst, Prod.snd,
    zmod3_zero_ne_one, zmod3_zero_ne_two, zmod3_one_ne_two,
    zmod3_one_ne_zero, zmod3_two_ne_zero, zmod3_two_ne_one]

/-- Every rational row sum matches `(1 - 1/2)⁻¹ = 2`. -/
theorem sum_Thetaq_row (a : Z2 3) : ∑ b : Z2 3, Thetaq a b = 2 := by
  have hpaper : ∑ b : Z2 3, Theta 3 (1 / 2) a b = (2 : ℂ) := by
    have h := sum_Theta_row 3 (by norm_num) (ξ := 1 / 2) (by norm_num) a
    norm_num at h
    exact h
  have hcast : ∑ b : Z2 3, ((Thetaq a b : ℚ) : ℂ) = (2 : ℂ) := by
    simpa only [Theta_three_half] using hpaper
  have hcast' : ((∑ b : Z2 3, Thetaq a b : ℚ) : ℂ) = (2 : ℂ) := by
    simpa only [Rat.cast_sum] using hcast
  exact_mod_cast hcast'

end RBM.Numeric
