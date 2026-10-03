/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Drift
import RBM2D.Path.StepDecomp
import RBM2D.Induction.Split
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Hierarchy.WardResolvent
import RBM2D.Induction.LoopC2N

/-!
# The loop Duhamel tail of the GUE phase, part I (`d = 2`)

The unit-GUE variance of a linear functional, the Ward bound of the quadratic variation
(7.38)/(7.43) with `S_GUE = 1/N`, the conditional variance of the linear part of one step, crude
and Lipschitz bounds on `loopMax`, the one-step decomposition (linear part, Taylor remainder,
truncation), the truncation bias, and the grid facts with the drift remainder.  Parts II and III
(`GUEPhase/DuhamelB.lean`, `GUEPhase/DuhamelC.lean`) are written against the public declarations
below.

## Contents

* `Duhamel_vGue_le` (`vGue A ≤ 8 ‖A‖_F²`); `Duhamel_frobSq_loopCut_le` with the cut block
  `DuhamelLoopCut`; `Duhamel_vGue_gradMat_le`.
* `Duhamel_loopMax_le_crude`, `Duhamel_loopMax_shift_le`: crude and shift bounds on `loopMax`.
* `DuhamelGood`, `DuhamelZ`, `DuhamelR`, `DuhamelT`, `DuhamelB`: the truncation set, the linear
  part, the Taylor remainder, its truncation and the truncation bias of one step;
  `Duhamel_measurableSet_good`, `Duhamel_Z_re_im`, `Duhamel_measurable_R`,
  `Duhamel_integral_step`, `Duhamel_norm_T_le`, `Duhamel_norm_B_le`.
* `Duhamel_measurable_coord`, `Duhamel_gueH_measurable_filt`, `Duhamel_gueH_succ`,
  `Duhamel_drift_remainder_ae`: the grid facts and the drift remainder.
* `Duhamel_measurable_loop`: measurability of the loop observable on all matrices (the hypothesis
  `Measurable Φ` of `Duhamel_measurable_R`).

## Conventions (`d = 2`)

* The sizes are `Sizes`, the sample space is `Sizes.SeqΩ d`, with `Sizes.seqXmat d n`, the
  increment flow `Sizes.seqHflow d n v y` (`= √v • seqXmat`), the grid `PathΩ d`, `filt d`,
  `gridTime/gridStep`, `linTr`, and `d.size n = (W L)²`; `frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2`.
* Loops: `gloop (d.L n) (d.W n) (blockMat M) z I` on `BlockIndex L W` with the blocks
  `E_a = W⁻² 1_{block a}`; `loopMax` is `RBM.Ind.loopMax`.
* The observable is a `HermTestFun d n Φ` with a second-derivative bound `hC₂` at Hermitian
  points, and `hM : M.IsHermitian` (a loop observable is not even bounded off the Hermitian set).
* Size scale: the truncation threshold is `d.size n` (the event of `gue_highProb_incr_le`),
  `card (Idx) = d.size n`, `card (Coord) = 2 (d.size n)²`; the crude bound is
  `(L W)² |Im z|^{-m}` (`card (BlockIndex L W) = (L W)²`); the drift remainder is
  `envConst L W e m (u_{k+1}) Δ^{3/2}` (`condExp_loop_drift_gue`).

The cut identity `gradMat = -∑_k R_k` is proved from `fderiv_eq_trace_gradMat`, the Leibniz rule
and the fact that a matrix is determined by its trace pairing with the Hermitian matrices.
The private helpers carry the prefix `Duhamel_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### 1. The unit-GUE variance of a linear functional is bounded by the Frobenius norm -/

section VGue

variable {d : Sizes}

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem Duhamel_seqXmat_single (n : ℕ) (c : Coord (d.L n) (d.W n)) :
    Sizes.seqXmat d n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) 1)
      = coordinateMatrix (d.L n) (d.W n) c := by
  have hs : Sizes.slice d n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) 1)
      = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord d) (1 : ℝ) : Sizes.SeqCoord d → ℝ) ⟨n, c'⟩
      = (Pi.single c (1 : ℝ) : Coord (d.L n) (d.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord d) ≠ ⟨n, c⟩ := fun he =>
        h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat
  rw [hs]
  rfl

private theorem Duhamel_cm_lt {L W : ℕ} [NeZero L] [NeZero W] {i j : Idx L W}
    (h : idxKey L W i < idxKey L W j) (b : Bool) :
    coordinateMatrix L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_diag_true {L W : ℕ} [NeZero L] [NeZero W] (i : Idx L W) :
    coordinateMatrix L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_diag_false {L W : ℕ} [NeZero L] [NeZero W] (i : Idx L W) :
    coordinateMatrix L W (i, i, false) = 0 := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem Duhamel_cm_gt {L W : ℕ} [NeZero L] [NeZero W] {i j : Idx L W}
    (h : idxKey L W j < idxKey L W i) (b : Bool) :
    coordinateMatrix L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The squared coefficient of one coordinate in `linTr n A ∘ seqXmat d n`. -/
private theorem Duhamel_lin_coord_sq_le (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (c : Coord (d.L n) (d.W n)) :
    (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2
      ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
  obtain ⟨i, j, b⟩ := c
  simp only
  have hnn : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    intro x y _ _; nlinarith [sq_nonneg (x - y)]
  rcases idxKey_lt_or_eq_or_lt (d.L n) (d.W n) i j with h | h | h
  · rw [Duhamel_cm_lt h]
    have hx : ‖(if b then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
    have hy : ‖(if b then (1 : ℂ) else -Complex.I)‖ = 1 := by split_ifs <;> simp
    have htr : Matrix.trace (A * (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I)))
        = A j i * (if b then (1 : ℂ) else Complex.I) + A i j * (if b then (1 : ℂ) else -Complex.I) := by
      rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single, Matrix.trace_mul_single]
      simp [mul_comm]
    have hlin : |linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))| ≤ ‖A j i‖ + ‖A i j‖ := by
      unfold linTr
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [htr]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hx, hy, mul_one, mul_one]
    calc (linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))) ^ 2
        = |linTr n A (Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I))| ^ 2 := (sq_abs _).symm
      _ ≤ (‖A j i‖ + ‖A i j‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlin 2
      _ ≤ 2 * (‖A j i‖ ^ 2 + ‖A i j‖ ^ 2) := hnn _ _ (norm_nonneg _) (norm_nonneg _)
      _ = 2 * (‖A i j‖ ^ 2 + ‖A j i‖ ^ 2) := by ring
  · subst h
    cases b
    · rw [Duhamel_cm_diag_false]
      have h0 : linTr n A (0 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) = 0 := by
        simp [linTr]
      rw [h0]
      nlinarith [sq_nonneg ‖A i i‖]
    · rw [Duhamel_cm_diag_true]
      have hlin : |linTr n A (Matrix.single i i (1 : ℂ))| ≤ ‖A i i‖ := by
        unfold linTr
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [Matrix.trace_mul_single]
        simp
      calc (linTr n A (Matrix.single i i (1 : ℂ))) ^ 2
          = |linTr n A (Matrix.single i i (1 : ℂ))| ^ 2 := (sq_abs _).symm
        _ ≤ ‖A i i‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlin 2
        _ ≤ 2 * (‖A i i‖ ^ 2 + ‖A i i‖ ^ 2) := by nlinarith [sq_nonneg ‖A i i‖]
  · rw [Duhamel_cm_gt h]
    have h0 : linTr n A (0 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) = 0 := by
      simp [linTr]
    rw [h0]
    nlinarith [sq_nonneg ‖A i j‖, sq_nonneg ‖A j i‖]

/-- `vGue` as the sum over the coordinates of the squared coefficient times the variance. -/
private theorem Duhamel_vGue_eq_sum (d : Sizes) (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    (vGue d n A : ℝ) = ∑ c : Coord (d.L n) (d.W n),
      (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2
        * (gueUnitVar d ⟨n, c⟩ : ℝ) := by
  classical
  unfold vGue linVar coordFinset
  push_cast [NNReal.coe_mk]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Function.Embedding.sigmaMk_apply, Duhamel_seqXmat_single]

/-- **`vGue A ≤ 8 ‖A‖_F²`**:
the unit-GUE variance of the linear functional `y ↦ Re tr (A · seqXmat d n y)` is at most
`8 ∑_{ij} |A_{ij}|²`. -/
theorem Duhamel_vGue_le (d : Sizes) (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    (vGue d n A : ℝ) ≤ 8 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  classical
  have hvar : ∀ c : Sizes.SeqCoord d, (gueUnitVar d c : ℝ) ≤ 1 := by
    intro c; unfold gueUnitVar; split_ifs <;> norm_num
  rw [Duhamel_vGue_eq_sum]
  have hterm : ∀ c : Coord (d.L n) (d.W n),
      (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2 * (gueUnitVar d ⟨n, c⟩ : ℝ)
        ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
    intro c
    calc (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2 * (gueUnitVar d ⟨n, c⟩ : ℝ)
        ≤ (linTr n A (coordinateMatrix (d.L n) (d.W n) c)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hvar _) (sq_nonneg _)
      _ ≤ 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2) := by
          rw [mul_one]; exact Duhamel_lin_coord_sq_le n A c
  refine (Finset.sum_le_sum fun c _ => hterm c).trans (le_of_eq ?_)
  have hsplit : ∑ c : Coord (d.L n) (d.W n), 2 * (‖A c.1 c.2.1‖ ^ 2 + ‖A c.2.1 c.1‖ ^ 2)
      = ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
          (4 * ‖A i j‖ ^ 2 + 4 * ‖A j i‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hsplit]
  have hswap : ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n), ‖A j i‖ ^ 2
      = ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n), ‖A i j‖ ^ 2 :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

end VGue


/-! ### 2. The Ward bound of the quadratic variation ((7.43) with `S_GUE = 1/N`) -/

section Ward

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The word `∏_{p ∈ l} G_{p.1} E_{p.2}` of a list of `(sign, label)` pairs. -/
private def Duhamel_wd (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p X => Gsig M z p.1 * Eblk L W p.2 * X) 1

private theorem Duhamel_wd_cons (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    Duhamel_wd M z (p :: l) = Gsig M z p.1 * Eblk L W p.2 * Duhamel_wd M z l := rfl

private theorem Duhamel_wd_append (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l₁ l₂ : List (Bool × Z2 L)) :
    Duhamel_wd M z (l₁ ++ l₂) = Duhamel_wd M z l₁ * Duhamel_wd M z l₂ := by
  have Duhamel_wd_nil (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Z2 L)) = 1 := rfl
  induction l₁ with
  | nil => simp [Duhamel_wd_nil]
  | cons p l ih => simp [Duhamel_wd_cons, ih, Matrix.mul_assoc]

private theorem Duhamel_gloopProd_eq (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) : gloopProd L W M z I = Duhamel_wd M z (I.σ.zip I.a) := rfl

/-- A list of `(sign, label)` pairs read as a loop index. -/
private def Duhamel_ofPairs (l : List (Bool × Z2 L)) : LoopIdx (Z2 L) :=
  ⟨l.map Prod.fst, l.map Prod.snd⟩

private theorem Duhamel_ofPairs_zip (l : List (Bool × Z2 L)) :
    (Duhamel_ofPairs l).σ.zip (Duhamel_ofPairs l).a = l := by
  change (l.map Prod.fst).zip (l.map Prod.snd) = l
  rw [List.zip_map']
  simp

/-- Reverse a chain and flip its charges. -/
private def Duhamel_rflip (t : Bool) : List (Bool × Z2 L) → Z2 L → List (Bool × Z2 L)
  | [], c => [(t, c)]
  | p :: l, c => Duhamel_rflip t l p.2 ++ [(!p.1, c)]

private theorem Duhamel_rflip_length (t : Bool) (l : List (Bool × Z2 L)) (c : Z2 L) :
    (Duhamel_rflip t l c).length = l.length + 1 := by
  induction l generalizing c with
  | nil => simp [Duhamel_rflip]
  | cons p l ih => simp [Duhamel_rflip, ih]

/-- `G(t) · (∏ G E)ᴴ · E_c` is the word of `rflip t l c`, for Hermitian `M`. -/
private theorem Duhamel_wd_rflip {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (t : Bool) (l : List (Bool × Z2 L)) (c : Z2 L) :
    Gsig M z t * (Duhamel_wd M z l)ᴴ * Eblk L W c = Duhamel_wd M z (Duhamel_rflip t l c) := by
  have Duhamel_wd_nil (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Z2 L)) = 1 := rfl
  induction l generalizing c with
  | nil => simp [Duhamel_rflip, Duhamel_wd_nil, Duhamel_wd_cons]
  | cons p l ih =>
    rw [Duhamel_rflip, Duhamel_wd_append, ← ih p.2, Duhamel_wd_cons, Duhamel_wd_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Eblk_conjTranspose,
      Gsig_conjTranspose hM]
    simp [Matrix.mul_assoc, Duhamel_wd_nil]

/-- The two Ward products `G Gᴴ` and `Gᴴ G` are both `(2iη)⁻¹ (G(z) - G(z̄))`. -/
private theorem Duhamel_Gsig_mul_conj {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) :
    Gsig M z s * (Gsig M z s)ᴴ
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) ∧
      (Gsig M z s)ᴴ * Gsig M z s
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
  have hu : IsUnit (M - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM hz
  have hu' : IsUnit (M - ((starRingEnd ℂ) z) • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM (by simpa using hz)
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) this
  have hzc : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
    rw [Complex.sub_conj]; push_cast; ring
  have h1 : green M z * green M ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green hu hu', hzc, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : green M ((starRingEnd ℂ) z) * green M z
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green_conj' hu hu', smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Gsig_conjTranspose hM]
  cases s
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

/-- A glued trace `tr(E P G_x Pᴴ E G_y)` is a `2m`-loop. -/
private theorem Duhamel_trace_glue_eq {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × Z2 L)) (a : Z2 L) (x y : Bool) :
    Matrix.trace (Eblk L W a * Duhamel_wd M z rest * Gsig M z x
        * (Duhamel_wd M z rest)ᴴ * Eblk L W a * Gsig M z y)
      = gloop L W M z (Duhamel_ofPairs ((y, a) :: rest ++ Duhamel_rflip x rest a)) := by
  rw [gloop, Duhamel_gloopProd_eq, Duhamel_ofPairs_zip, Duhamel_wd_append, Duhamel_wd_cons,
    ← Duhamel_wd_rflip hM z x rest a]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private theorem Duhamel_norm_glue_le {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × Z2 L)) (a : Z2 L) (x y : Bool)
    {m : ℕ} (hm : rest.length + 1 = m) :
    ‖Matrix.trace (Eblk L W a * Duhamel_wd M z rest * Gsig M z x
        * (Duhamel_wd M z rest)ᴴ * Eblk L W a * Gsig M z y)‖ ≤ RBM.Ind.loopMax L W M z (2 * m) := by
  rw [Duhamel_trace_glue_eq hM]
  refine RBM.Ind.norm_gloop_le_loopMax _ ?_ ?_
  · simp [Duhamel_ofPairs, Duhamel_rflip_length]; omega
  · simp [Duhamel_ofPairs, Duhamel_rflip_length]; omega

/-- **The cut block `R_k` of the `k`-th edge** (`k` counted from `0`):
`R_k = G(σ_k) E_{a_k} · (∏_{i > k} ∏_{i < k} G(σ_i) E_{a_i}) · G(σ_k)`. -/
def DuhamelLoopCut (L W : ℕ) [NeZero L] (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) (k : ℕ) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  Gsig M z (I.σ.getD k true) * Eblk L W (I.a.getD k 0) *
    gloopProd L W M z ⟨I.σ.drop (k + 1) ++ I.σ.take k, I.a.drop (k + 1) ++ I.a.take k⟩ *
    Gsig M z (I.σ.getD k true)

/-- **Ward, for one cut block**: `‖R_k‖_F² ≤ |Im z|⁻² L^{(2n)}`. -/
theorem Duhamel_frobSq_loopCut_le {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hI : I.WF) {k : ℕ}
    (hk : k < I.length) :
    ∑ p, ∑ q, ‖DuhamelLoopCut L W M z I k p q‖ ^ 2
      ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax L W M z (2 * I.length) := by
  set s := I.σ.getD k true with hs
  set a := I.a.getD k 0 with ha
  set σ' := I.σ.drop (k + 1) ++ I.σ.take k with hσ'
  set a' := I.a.drop (k + 1) ++ I.a.take k with ha'
  have hσlen : I.σ.length = I.a.length := hI
  have hlen' : σ'.length = a'.length := by
    simp only [hσ', ha', List.length_append, List.length_drop, List.length_take, hσlen]
  set rest : List (Bool × Z2 L) := σ'.zip a' with hrest
  set P := Duhamel_wd M z rest with hP
  set G := Gsig M z s with hG
  set Dl := green M z - green M ((starRingEnd ℂ) z) with hDl
  set c := (2 * Complex.I * (z.im : ℂ))⁻¹ with hcdef
  have hlen : rest.length + 1 = I.length := by
    have hk' : k < I.a.length := hk
    have : rest.length = σ'.length := by
      rw [hrest, List.length_zip, hlen', min_self]
    rw [this]
    simp only [hσ', List.length_append, List.length_drop, List.length_take, hσlen]
    change _ = I.a.length
    omega
  have hR : DuhamelLoopCut L W M z I k = G * Eblk L W a * P * G := by
    rw [DuhamelLoopCut]
    rfl
  obtain ⟨hGG, hGG'⟩ := Duhamel_Gsig_mul_conj hM hz s
  -- the Frobenius norm is the trace of `R Rᴴ`
  have hfrob : ∀ R : Matrix (BlockIndex L W) (BlockIndex L W) ℂ,
      ((∑ p, ∑ q, ‖R p q‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (R * Rᴴ) := by
    intro R
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have htr : Matrix.trace (DuhamelLoopCut L W M z I k * (DuhamelLoopCut L W M z I k)ᴴ)
      = c * c * Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl) := by
    rw [hR]
    simp only [Matrix.conjTranspose_mul, Eblk_conjTranspose]
    have e1 : G * Eblk L W a * P * G * (Gᴴ * (Pᴴ * (Eblk L W a * Gᴴ)))
        = G * (Eblk L W a * P * (G * Gᴴ) * Pᴴ * Eblk L W a * Gᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm, hGG]
    have e2 : Eblk L W a * P * (c • Dl) * Pᴴ * Eblk L W a * Gᴴ * G
        = Eblk L W a * P * (c • Dl) * Pᴴ * Eblk L W a * (Gᴴ * G) := by
      simp only [Matrix.mul_assoc]
    rw [e2, hGG']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  -- expand `Dl = G₊ - G₋` in both slots
  have hexp : Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)
      = Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z true)
        - Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z false)
        - Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z true)
        + Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z false) := by
    rw [hDl, Gsig_true, Gsig_false]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    ring
  have hb : ∀ x y : Bool,
      ‖Matrix.trace (Eblk L W a * P * Gsig M z x * Pᴴ * Eblk L W a * Gsig M z y)‖
        ≤ RBM.Ind.loopMax L W M z (2 * I.length) :=
    fun x y => Duhamel_norm_glue_le hM z rest a x y hlen
  have hsum : ‖Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)‖
      ≤ 4 * RBM.Ind.loopMax L W M z (2 * I.length) := by
    rw [hexp]
    have := hb true true; have := hb true false; have := hb false true; have := hb false false
    calc _ ≤ ‖Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z true)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z false)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z true)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a
              * Gsig M z false)‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add_left ?_ _
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add_left ?_ _
          exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hcnorm : ‖c * c‖ = (|z.im|⁻¹) ^ 2 / 4 := by
    rw [hcdef, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    field_simp
    rw [sq_abs]; ring
  have hre : (∑ p, ∑ q, ‖DuhamelLoopCut L W M z I k p q‖ ^ 2 : ℝ)
      = (Matrix.trace (DuhamelLoopCut L W M z I k * (DuhamelLoopCut L W M z I k)ᴴ)).re := by
    rw [← hfrob, Complex.ofReal_re]
  rw [hre]
  refine (Complex.re_le_norm _).trans ?_
  rw [htr, norm_mul, hcnorm]
  have h0 : 0 ≤ (|z.im|⁻¹) ^ 2 / 4 := by positivity
  calc (|z.im|⁻¹) ^ 2 / 4 * ‖Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)‖
      ≤ (|z.im|⁻¹) ^ 2 / 4 * (4 * RBM.Ind.loopMax L W M z (2 * I.length)) :=
        mul_le_mul_of_nonneg_left hsum h0
    _ = _ := by ring

end Ward


/-! ### 3. The conditional variance of the linear part of one step -/

section QV

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Reindex a block matrix back to the fine lattice (the inverse of `blockMat`). -/
private def Duhamel_unblock (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix (Idx L W) (Idx L W) ℂ :=
  A.submatrix (splitEquiv L W) (splitEquiv L W)

private theorem Duhamel_blockMat_unblock (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    blockMat (Duhamel_unblock A) = A := by
  ext p q
  simp [blockMat, Duhamel_unblock]

private theorem Duhamel_blockMat_mul (A B : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (A * B) = blockMat A * blockMat B :=
  (Matrix.submatrix_mul_equiv A B _ (splitEquiv L W).symm _).symm

private theorem Duhamel_trace_blockMat (A : Matrix (Idx L W) (Idx L W) ℂ) :
    Matrix.trace (blockMat A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, blockMat, Matrix.submatrix_apply]
  exact (splitEquiv L W).symm.sum_comp (fun i => A i i)

private theorem Duhamel_trace_blockMat_mul (X : Matrix (Idx L W) (Idx L W) ℂ)
    (C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (blockMat X * C) = Matrix.trace (X * Duhamel_unblock C) := by
  have h : blockMat X * C = blockMat (X * Duhamel_unblock C) := by
    rw [Duhamel_blockMat_mul, Duhamel_blockMat_unblock]
  rw [h, Duhamel_trace_blockMat]

private theorem Duhamel_frobSq_unblock (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ i, ∑ j, ‖Duhamel_unblock A i j‖ ^ 2 = ∑ p, ∑ q, ‖A p q‖ ^ 2 := by
  simp only [Duhamel_unblock, Matrix.submatrix_apply]
  rw [← (splitEquiv L W).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (splitEquiv L W).sum_comp (fun q => ‖A (splitEquiv L W p) q‖ ^ 2)

/-- A matrix is determined by its trace pairing with the Hermitian matrices. -/
private theorem Duhamel_eq_of_trace_herm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (h : ∀ X : Matrix ι ι ℂ, X.IsHermitian → Matrix.trace (A * X) = Matrix.trace (B * X)) :
    A = B := by
  ext i j
  have hmul : ∀ (C : Matrix ι ι ℂ) (a b : ι) (x : ℂ),
      Matrix.trace (C * Matrix.single a b x) = C b a * x := by
    intro C a b x
    rw [Matrix.trace_mul_single]
    simp [mul_comm]
  by_cases hij : i = j
  · subst hij
    have h0 := h (Matrix.single i i (1 : ℂ))
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_single])
    rw [hmul, hmul] at h0
    simpa using h0
  · have hS : (Matrix.single i j (1 : ℂ) + Matrix.single j i 1).IsHermitian := by
      simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]
    have hT : (Matrix.single i j Complex.I - Matrix.single j i Complex.I).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
      simp only [Complex.star_def, Complex.conj_I, ← Matrix.single_neg]
      abel
    have h1 := h _ hS
    have h2 := h _ hT
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, hmul] at h1 h2
    have h2' : A j i - A i j = B j i - B i j := by
      refine mul_right_cancel₀ Complex.I_ne_zero ?_
      linear_combination h2
    linear_combination (h1 - h2') / 2

private theorem Duhamel_frobSq_sum_le {ι : Type*} [Fintype ι] (s : Finset ℕ)
    (R : ℕ → Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(∑ k ∈ s, R k) i j‖ ^ 2
      ≤ (s.card : ℝ) * ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := by
  have key : ∀ i j : ι, ‖(∑ k ∈ s, R k) i j‖ ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 := by
    intro i j
    rw [Matrix.sum_apply]
    have h1 : ‖∑ k ∈ s, R k i j‖ ≤ ∑ k ∈ s, ‖R k i j‖ := norm_sum_le _ _
    have h2 : (∑ k ∈ s, ‖R k i j‖) ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  calc ∑ i, ∑ j, ‖(∑ k ∈ s, R k) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (s.card : ℝ) * ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 := by simp only [Finset.mul_sum]
    _ = (s.card : ℝ) * ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := by
        congr 1
        calc ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 = ∑ i, ∑ k ∈ s, ∑ j, ‖R k i j‖ ^ 2 :=
              Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := Finset.sum_comm


/-! #### The Leibniz rule for the loop observable at a Hermitian point

(Jets of the loop observable for a general spectral parameter `z`, `Im z ≠ 0`, and a general loop
index.) -/

/-- `blockMat` as a continuous real-linear map. -/
private def Duhamel_blockCLM (L W : ℕ) [NeZero L] [NeZero W] :
    Matrix (Idx L W) (Idx L W) ℂ →L[ℝ] Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockMat
      map_add' := fun A C => by ext p q; simp [blockMat]
      map_smul' := fun r A => by ext p q; simp [blockMat] }

private theorem Duhamel_blockMat_add_smul (A C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (A + y • C) = blockMat A + y • blockMat C := by
  ext p q
  simp [blockMat]

/-- The trace as a continuous real-linear map. -/
private def Duhamel_trCLM (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)

/-- The resolvent along a Hermitian line has derivative `-G D G`. -/
private theorem Duhamel_hasDerivAt_green {n : Type*} [Fintype n] [DecidableEq n] {H D : Matrix n n ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (H + (s : ℂ) • D) z)
      (-(green (H + (t : ℂ) • D) z * D * green (H + (t : ℂ) • D) z)) t := by
  have hgr : ∀ s : ℝ, green (H + (s : ℂ) • D) z
      = Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    change (H + (s : ℂ) • D - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D) := by
    intro s
    have he : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • D
        = (H + (s : ℂ) • D) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hH hD s) hz
  have h := hasDerivAt_lineInverse hU t
  simp only [← hgr] at h
  exact h

private theorem Duhamel_hasDerivAt_Gsig {n : Type*} [Fintype n] [DecidableEq n] {H D : Matrix n n ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gsig (H + (s : ℂ) • D) z σ)
      (-(Gsig (H + (t : ℂ) • D) z σ * D * Gsig (H + (t : ℂ) • D) z σ)) t := by
  cases σ
  · exact Duhamel_hasDerivAt_green hH hD (by simpa using hz) t
  · exact Duhamel_hasDerivAt_green hH hD hz t

/-- Differentiate the first factor of the word `m`: `head (p :: m') = (-(G D G) E_p) · wd m'`. -/
private def Duhamel_head (H D : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
    List (Bool × Z2 L) → Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  | [] => 0
  | p :: m => (-(Gsig H z p.1 * D * Gsig H z p.1) * Eblk L W p.2) * Duhamel_wd H z m

/-- The Leibniz sum of a word: differentiate the `q`-th factor, `q < |l|`. -/
private def Duhamel_wordDeriv (H D : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  ∑ q ∈ Finset.range l.length, Duhamel_wd H z (l.take q) * Duhamel_head H D z (l.drop q)

private theorem Duhamel_wordDeriv_cons (H D : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    Duhamel_wordDeriv H D z (p :: l) = Duhamel_head H D z (p :: l) +
      Gsig H z p.1 * Eblk L W p.2 * Duhamel_wordDeriv H D z l := by
  have Duhamel_wd_nil (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Z2 L)) = 1 := rfl
  unfold Duhamel_wordDeriv
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, Duhamel_wd_cons, List.take_zero,
    List.drop_zero, Duhamel_wd_nil, Matrix.one_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [add_comm]

/-- **Leibniz rule for a word** along a Hermitian line. -/
private theorem Duhamel_hasDerivAt_wd {H D : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L)) :
    HasDerivAt (fun y : ℝ => Duhamel_wd (H + (y : ℂ) • D) z l) (Duhamel_wordDeriv H D z l) 0 := by
  have Duhamel_wd_nil (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
      Duhamel_wd M z ([] : List (Bool × Z2 L)) = 1 := rfl
  induction l with
  | nil =>
      have h0 : Duhamel_wordDeriv H D z ([] : List (Bool × Z2 L)) = 0 := by
        simp [Duhamel_wordDeriv]
      rw [h0]
      simpa only [Duhamel_wd_nil] using
        hasDerivAt_const (0 : ℝ) (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have hG := Duhamel_hasDerivAt_Gsig hH hD hz p.1 0
      have h00 : H + ((0 : ℝ) : ℂ) • D = H := by simp
      rw [h00] at hG
      have hhead := hG.mul_const (Eblk L W p.2)
      have h := hhead.mul ih
      rw [Duhamel_wordDeriv_cons]
      have hfun : (fun y : ℝ => Duhamel_wd (H + (y : ℂ) • D) z (p :: l)) =
          fun y : ℝ => Gsig (H + (y : ℂ) • D) z p.1 * Eblk L W p.2 *
            Duhamel_wd (H + (y : ℂ) • D) z l := rfl
      rw [hfun]
      convert h using 1
      simp [Duhamel_head]

/-- The `q`-th Leibniz term as a pairing against the cut chain:
`tr(wd(l[:q]) · ∂_q) = -tr(D · wd(l[q:] ++ l[:q]) · G^{l_q})` (cyclicity of the trace). -/
private theorem Duhamel_trace_term (H D : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) {q : ℕ} (hq : q < l.length) :
    Matrix.trace (Duhamel_wd H z (l.take q) * Duhamel_head H D z (l.drop q)) =
      -Matrix.trace (D * (Duhamel_wd H z (l.drop q ++ l.take q) *
        Gsig H z (l.getD q (true, 0)).1)) := by
  rw [List.getD_eq_getElem _ _ hq, List.drop_eq_getElem_cons hq, Duhamel_head,
    Duhamel_wd_append, Duhamel_wd_cons]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [show Duhamel_wd H z (l.take q) * (Gsig H z l[q].1 * D * Gsig H z l[q].1 * Eblk L W l[q].2 *
        Duhamel_wd H z (l.drop (q + 1))) =
      (Duhamel_wd H z (l.take q) * Gsig H z l[q].1) *
        (D * (Gsig H z l[q].1 * Eblk L W l[q].2 * Duhamel_wd H z (l.drop (q + 1)))) by
    simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The resolvent of `blockMat M` is `C²` at every `M` for which `blockMat M - w` is invertible. -/
private theorem Duhamel_contDiffAt_green {w : ℂ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hu : IsUnit (blockMat M - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ))) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => green (blockMat M') w) M := by
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
      blockMat M' - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) :=
    ((Duhamel_blockCLM L W).contDiff).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (BlockIndex L W) (BlockIndex L W) ℂ))
      (blockMat M - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx L W) (Idx L W) ℂ => green (blockMat M') w)
      = Ring.inverse ∘ (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
        blockMat M' - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    funext M'
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  exact h

private theorem Duhamel_contDiffAt_Gsig {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => Gsig (blockMat M') z σ) M := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  cases σ
  · exact Duhamel_contDiffAt_green (isUnit_sub_smul_one_of_im_ne_zero hMb (by simpa using hz))
  · exact Duhamel_contDiffAt_green (isUnit_sub_smul_one_of_im_ne_zero hMb hz)

private theorem Duhamel_contDiffAt_word {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Z2 L))
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
      l.foldr (fun p X => Gsig (blockMat M') z p.1 * Eblk L W p.2 * X) 1) M := by
  induction l with
  | nil => exact contDiffAt_const
  | cons p l ih =>
    have hEp : ContDiffAt ℝ 2 (fun _ : Matrix (Idx L W) (Idx L W) ℂ => Eblk L W p.2) M :=
      contDiffAt_const
    exact ((Duhamel_contDiffAt_Gsig hz p.1 hM).mul hEp).mul ih

/-- The loop observable `M ↦ 𝓛(blockMat M, z, I)` is `C²` at every Hermitian point. -/
private theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L))
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z I) M :=
  (Duhamel_trCLM (BlockIndex L W)).contDiff.contDiffAt.comp M
    (Duhamel_contDiffAt_word hz (I.σ.zip I.a) hM)

/-- **Leibniz decomposition of the loop derivative**: for Hermitian `M, X`,
`D𝓛(M)[X] = -∑_q tr(X̂ · A_q)`. -/
private theorem Duhamel_fderiv_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L))
    {M X : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    fderiv ℝ (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z I) M X
      = -∑ q ∈ Finset.range (I.σ.zip I.a).length,
          Matrix.trace (blockMat X * (Duhamel_wd (blockMat M) z
            ((I.σ.zip I.a).drop q ++ (I.σ.zip I.a).take q) *
              Gsig (blockMat M) z ((I.σ.zip I.a).getD q (true, 0)).1)) := by
  set Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ := fun M' => gloop L W (blockMat M') z I with hΦ
  set l : List (Bool × Z2 L) := I.σ.zip I.a with hl
  have hdiff : DifferentiableAt ℝ Φ M :=
    (Duhamel_contDiffAt_loop hz I hM).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • X)) (fderiv ℝ Φ M X) 0 := by
    have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line M X 0)
      (by simp)
    simpa [Function.comp_def] using h
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hXb : (blockMat X).IsHermitian := hX.submatrix _
  have hfun : (fun s : ℝ => Φ (M + (s : ℂ) • X))
      = fun s : ℝ => Matrix.trace (Duhamel_wd (blockMat M + (s : ℂ) • blockMat X) z l) := by
    funext s
    simp only [hΦ]
    rw [Duhamel_blockMat_add_smul]
    rfl
  have h2 : HasDerivAt (fun s : ℝ => Φ (M + (s : ℂ) • X))
      (Matrix.trace (Duhamel_wordDeriv (blockMat M) (blockMat X) z l)) 0 := by
    rw [hfun]
    exact (Duhamel_trCLM (BlockIndex L W)).hasFDerivAt.comp_hasDerivAt 0
      (Duhamel_hasDerivAt_wd hMb hXb hz l)
  rw [h1.unique h2, Duhamel_wordDeriv, Matrix.trace_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  exact Duhamel_trace_term (blockMat M) (blockMat X) z l (Finset.mem_range.1 hq)


private theorem Duhamel_gloopProd_mk (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ : List Bool) (a : List (Z2 L)) :
    gloopProd L W M z ⟨σ, a⟩ = Duhamel_wd M z (σ.zip a) := rfl

/-- The zip of a rotated pair of lists is the rotation of the zip. -/
private theorem Duhamel_zip_drop_take {α β : Type*} (σ : List α) (a : List β)
    (h : σ.length = a.length) (p q : ℕ) :
    (σ.drop p ++ σ.take q).zip (a.drop p ++ a.take q) = (σ.zip a).drop p ++ (σ.zip a).take q := by
  rw [List.zip_append (by simp [h])]
  simp only [List.zip_eq_zipWith, List.drop_zipWith, List.take_zipWith]

/-- `DuhamelLoopCut` is the cut chain `wd(rot_k) · G^{σ_k}` of the Leibniz decomposition. -/
private theorem Duhamel_loopCut_eq (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    {I : LoopIdx (Z2 L)} (hI : I.WF) {k : ℕ} (hk : k < (I.σ.zip I.a).length) :
    DuhamelLoopCut L W H z I k
      = Duhamel_wd H z ((I.σ.zip I.a).drop k ++ (I.σ.zip I.a).take k) *
          Gsig H z ((I.σ.zip I.a).getD k (true, 0)).1 := by
  have hσlen : I.σ.length = I.a.length := hI
  have hσk : k < I.σ.length := lt_of_lt_of_le hk (by simp [List.length_zip])
  have hak : k < I.a.length := lt_of_lt_of_le hk (by simp [List.length_zip])
  have hgetD : (I.σ.zip I.a).getD k (true, 0) = (I.σ[k], I.a[k]) := by
    rw [List.getD_eq_getElem _ _ hk, List.getElem_zip]
  unfold DuhamelLoopCut
  rw [Duhamel_gloopProd_mk, Duhamel_zip_drop_take I.σ I.a hσlen (k + 1) k,
    List.drop_eq_getElem_cons hk, List.cons_append, Duhamel_wd_cons, hgetD,
    List.getD_eq_getElem _ _ hσk, List.getD_eq_getElem _ _ hak, List.getElem_zip]

/-- **`gradMat` of a loop observable is minus the sum of its cut blocks** at a Hermitian matrix. -/
private theorem Duhamel_gradMat_loop {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hI : I.WF)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    gradMat (fun M' : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M') z I) M
      = -∑ k ∈ Finset.range I.a.length,
          Duhamel_unblock (DuhamelLoopCut L W (blockMat M) z I k) := by
  have hσlen : I.σ.length = I.a.length := hI
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip, hσlen, min_self]
  apply Duhamel_eq_of_trace_herm
  intro X hX
  rw [← fderiv_eq_trace_gradMat M hX, Duhamel_fderiv_loop hz I hM hX, Matrix.neg_mul,
    Matrix.sum_mul, Matrix.trace_neg, Matrix.trace_sum, hlen]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < (I.σ.zip I.a).length := by rw [hlen]; exact Finset.mem_range.1 hq
  rw [← Duhamel_loopCut_eq (blockMat M) z hI hq', Duhamel_trace_blockMat_mul,
    Matrix.trace_mul_comm]

private theorem Duhamel_frobSq_neg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(-A) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp

private theorem Duhamel_frobSq_negI {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖(-Complex.I • A) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp

/-- **(7.43) for the constant profile**: the unit-GUE Frobenius norm of the gradient of an
`n`-loop is at most `n² |Im z|⁻² L^{(2n)}`. -/
private theorem Duhamel_frobSq_gradMat_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)}
    (hI : I.WF) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ∑ i, ∑ j, ‖gradMat (fun M' : Matrix (Idx L W) (Idx L W) ℂ =>
        gloop L W (blockMat M') z I) M i j‖ ^ 2
      ≤ (I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax L W (blockMat M) z (2 * I.length) := by
  rw [Duhamel_gradMat_loop hz hI hM, Duhamel_frobSq_neg]
  refine (Duhamel_frobSq_sum_le _ _).trans ?_
  rw [Finset.card_range]
  have hk : ∀ k ∈ Finset.range I.a.length,
      ∑ i, ∑ j, ‖Duhamel_unblock (DuhamelLoopCut L W (blockMat M) z I k) i j‖ ^ 2
      ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax L W (blockMat M) z (2 * I.length) := by
    intro k hk
    rw [Duhamel_frobSq_unblock]
    exact Duhamel_frobSq_loopCut_le (hM.submatrix _) hz hI (Finset.mem_range.1 hk)
  have h1 := Finset.sum_le_sum hk
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hlen : (I.length : ℝ) = (I.a.length : ℝ) := rfl
  rw [hlen]
  have h0 : (0 : ℝ) ≤ (I.a.length : ℝ) := Nat.cast_nonneg _
  calc (I.a.length : ℝ) * ∑ k ∈ Finset.range I.a.length,
        ∑ i, ∑ j, ‖Duhamel_unblock (DuhamelLoopCut L W (blockMat M) z I k) i j‖ ^ 2
      ≤ (I.a.length : ℝ) * ((I.a.length : ℝ) * ((|z.im|⁻¹) ^ 2
          * RBM.Ind.loopMax L W (blockMat M) z (2 * I.length))) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

end QV

/-- **The variance proxy of the linear part**: for a Hermitian `M`, a well-formed loop `I` and
`Im z ≠ 0`, with
`Φ M = 𝓛(blockMat M, z, I)`,
`max(vGue(∇Φ), vGue(-i ∇Φ)) ≤ 8 · n² |Im z|⁻² L^{(2n)}(blockMat M, z)`, `n = |I|`. -/
theorem Duhamel_vGue_gradMat_le {d : Sizes} {n : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF)
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian) :
    max (vGue d n (gradMat (fun M' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          gloop (d.L n) (d.W n) (blockMat M') z I) M) : ℝ)
        (vGue d n (-Complex.I • gradMat (fun M' : Matrix (Idx (d.L n) (d.W n))
          (Idx (d.L n) (d.W n)) ℂ => gloop (d.L n) (d.W n) (blockMat M') z I) M) : ℝ)
      ≤ 8 * ((I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2
          * RBM.Ind.loopMax (d.L n) (d.W n) (blockMat M) z (2 * I.length)) := by
  have h := Duhamel_frobSq_gradMat_le hz hwf hM
  refine max_le ?_ ?_
  · exact (Duhamel_vGue_le d n _).trans (by linarith)
  · refine (Duhamel_vGue_le d n _).trans ?_
    rw [Duhamel_frobSq_negI]
    linarith

/-! ### 4. Crude and Lipschitz bounds on `loopMax` -/

section LoopMaxBounds

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Duhamel_norm_Eblk_le_one (a : Z2 L) : ‖Eblk L W a‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq L W a).trans ?_
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hW2 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hW3 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  exact pow_le_one₀ hW3 hW2

/-- `|L_{σ,a}| ≤ (LW)² |Im z|^{-m}`, hence `L^{(m)} ≤ (LW)² |Im z|^{-m}`
(`card (BlockIndex L W) = (L W)²`). -/
theorem Duhamel_loopMax_le_crude {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    RBM.Ind.loopMax L W M z m ≤ ((L : ℝ) * (W : ℝ)) ^ 2 * (|z.im|⁻¹) ^ m := by
  refine RBM.Ind.loopMax_le fun I hσ ha => ?_
  have hwf : I.WF := by unfold LoopIdx.WF; rw [hσ, ha]
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have h := norm_gloop_le_crude L W hM hη le_rfl I hwf
  refine h.trans ?_
  rw [ha]
  have hLW : ((L * W) ^ 2 : ℕ) = ((L : ℝ) * (W : ℝ)) ^ 2 := by push_cast; ring
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hW2 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have hpow : (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ m ≤ (|z.im|⁻¹) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    calc |z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2) ≤ |z.im|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = |z.im|⁻¹ := mul_one _
  have h0 : (0 : ℝ) ≤ ((L : ℝ) * (W : ℝ)) ^ 2 := by positivity
  rw [hLW]
  exact mul_le_mul_of_nonneg_left hpow h0

/-- The telescoping bound for two signed words. -/
private theorem Duhamel_word_le (G : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hG : ∀ s, ‖G s‖ ≤ K) (l : List (Bool × Z2 L)) :
    ‖l.foldr (fun p X => G p.1 * Eblk L W p.2 * X)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)‖ ≤ K ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc ‖G p.1 * Eblk L W p.2 *
            l.foldr (fun p X => G p.1 * Eblk L W p.2 * X) 1‖
          ≤ ‖G p.1‖ * ‖Eblk L W p.2‖ *
              ‖l.foldr (fun p X => G p.1 * Eblk L W p.2 * X) 1‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ K * 1 * K ^ l.length :=
            mul_le_mul (mul_le_mul (hG p.1) (Duhamel_norm_Eblk_le_one p.2) (norm_nonneg _) hK)
              ih (norm_nonneg _) (by positivity)
        _ = K ^ l.length * K := by ring

private theorem Duhamel_word_sub_le (G₁ G₂ : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    {K Δg : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δg) (hG₁ : ∀ s, ‖G₁ s‖ ≤ K) (hG₂ : ∀ s, ‖G₂ s‖ ≤ K)
    (hGd : ∀ s, ‖G₁ s - G₂ s‖ ≤ Δg) (l : List (Bool × Z2 L)) :
    ‖l.foldr (fun p X => G₁ p.1 * Eblk L W p.2 * X)
          (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      - l.foldr (fun p X => G₂ p.1 * Eblk L W p.2 * X) 1‖
      ≤ (l.length : ℝ) * K ^ l.length * Δg := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons]
      set w₁ := l.foldr (fun p X => G₁ p.1 * Eblk L W p.2 * X)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) with hw₁
      set w₂ := l.foldr (fun p X => G₂ p.1 * Eblk L W p.2 * X)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) with hw₂
      have hsplit : G₁ p.1 * Eblk L W p.2 * w₁ - G₂ p.1 * Eblk L W p.2 * w₂
          = (G₁ p.1 - G₂ p.1) * Eblk L W p.2 * w₁
            + G₂ p.1 * Eblk L W p.2 * (w₁ - w₂) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub]
        abel
      have hw1 : ‖w₁‖ ≤ K ^ l.length := Duhamel_word_le G₁ hK0 hG₁ l
      have hE := Duhamel_norm_Eblk_le_one (L := L) (W := W) p.2
      have hA : ‖(G₁ p.1 - G₂ p.1) * Eblk L W p.2 * w₁‖ ≤ Δg * K ^ l.length := by
        calc ‖(G₁ p.1 - G₂ p.1) * Eblk L W p.2 * w₁‖
            ≤ ‖G₁ p.1 - G₂ p.1‖ * ‖Eblk L W p.2‖ * ‖w₁‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ Δg * 1 * K ^ l.length :=
              mul_le_mul (mul_le_mul (hGd p.1) hE (norm_nonneg _) hΔ) hw1 (norm_nonneg _)
                (by positivity)
          _ = Δg * K ^ l.length := by ring
      have hB : ‖G₂ p.1 * Eblk L W p.2 * (w₁ - w₂)‖
          ≤ K * ((l.length : ℝ) * K ^ l.length * Δg) := by
        calc ‖G₂ p.1 * Eblk L W p.2 * (w₁ - w₂)‖
            ≤ ‖G₂ p.1‖ * ‖Eblk L W p.2‖ * ‖w₁ - w₂‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ K * 1 * ((l.length : ℝ) * K ^ l.length * Δg) :=
              mul_le_mul (mul_le_mul (hG₂ p.1) hE (norm_nonneg _) hK0) ih (norm_nonneg _)
                (by positivity)
          _ = K * ((l.length : ℝ) * K ^ l.length * Δg) := by ring
      have hpow : K ^ l.length ≤ K ^ (l.length + 1) := pow_le_pow_right₀ hK (Nat.le_succ _)
      rw [hsplit]
      calc ‖(G₁ p.1 - G₂ p.1) * Eblk L W p.2 * w₁
            + G₂ p.1 * Eblk L W p.2 * (w₁ - w₂)‖
          ≤ Δg * K ^ l.length + K * ((l.length : ℝ) * K ^ l.length * Δg) :=
            (norm_add_le _ _).trans (add_le_add hA hB)
        _ ≤ Δg * K ^ (l.length + 1) + K * ((l.length : ℝ) * K ^ l.length * Δg) := by
            have := mul_le_mul_of_nonneg_left hpow hΔ
            linarith
        _ = ((l.length + 1 : ℕ) : ℝ) * K ^ (l.length + 1) * Δg := by
            push_cast
            ring

/-- The Lipschitz bound of `loopMax` in the spectral parameter. -/
theorem Duhamel_loopMax_shift_le {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
    (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
    RBM.Ind.loopMax L W M z' m
      ≤ RBM.Ind.loopMax L W M z m
          + ((L : ℝ) * (W : ℝ)) ^ 2 * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hsub : ‖green M z' - green M z‖ ≤ ‖z' - z‖ * K ^ 2 := by
    rw [green_sub_green (isUnit_sub_smul_one_of_im_ne_zero hM hz')
      (isUnit_sub_smul_one_of_im_ne_zero hM hz), norm_smul]
    have h1 : ‖green M z' * green M z‖ ≤ K ^ 2 := by
      refine (norm_mul_le _ _).trans ?_
      rw [sq]
      exact mul_le_mul hGz' hGz (norm_nonneg _) hK0
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hΔ : 0 ≤ ‖z' - z‖ * K ^ 2 := by positivity
  have hGd : ∀ s : Bool, ‖Gsig M z' s - Gsig M z s‖ ≤ ‖z' - z‖ * K ^ 2 := by
    intro s
    cases s
    · have h := Gsig_conjTranspose hM z' true
      have h' := Gsig_conjTranspose hM z true
      have e : Gsig M z' false - Gsig M z false = (green M z' - green M z)ᴴ := by
        rw [Matrix.conjTranspose_sub]
        change _ = (Gsig M z' true)ᴴ - (Gsig M z true)ᴴ
        rw [h, h']
        rfl
      rw [e, Matrix.l2_opNorm_conjTranspose]
      exact hsub
    · exact hsub
  have hGn : ∀ w : ℂ, w.im ≠ 0 → ‖green M w‖ ≤ K → ∀ s : Bool, ‖Gsig M w s‖ ≤ K := by
    intro w hw hGw s
    cases s
    · have h := Gsig_conjTranspose hM w true
      change ‖Gsig M w false‖ ≤ K
      have e : Gsig M w false = (green M w)ᴴ := by
        change Gsig M w false = (Gsig M w true)ᴴ
        rw [h]; rfl
      rw [e, Matrix.l2_opNorm_conjTranspose]
      exact hGw
    · exact hGw
  refine RBM.Ind.loopMax_le fun I hσ ha => ?_
  have hwf : I.WF := by unfold LoopIdx.WF; rw [hσ, ha]
  have hlen : (I.σ.zip I.a).length = m := by
    rw [List.length_zip, hσ, ha, min_self]
  have hword := Duhamel_word_sub_le (Gsig M z') (Gsig M z) hK hΔ (hGn z' hz' hGz')
    (hGn z hz hGz) hGd (I.σ.zip I.a)
  rw [hlen] at hword
  have htrace := norm_matrix_trace_le_card_mul
    (gloopProd L W M z' I - gloopProd L W M z I)
  rw [Matrix.trace_sub] at htrace
  have hle : ‖gloop L W M z I‖ ≤ RBM.Ind.loopMax L W M z m :=
    RBM.Ind.norm_gloop_le_loopMax I hσ ha
  have hdiff : ‖gloop L W M z' I - gloop L W M z I‖
      ≤ ((L : ℝ) * (W : ℝ)) ^ 2 * (m * K ^ m * (‖z' - z‖ * K ^ 2)) := by
    refine htrace.trans ?_
    have hcard : (Fintype.card (BlockIndex L W) : ℝ) = ((L : ℝ) * (W : ℝ)) ^ 2 := by
      rw [card_BlockIndex]; push_cast; ring
    rw [hcard]
    exact mul_le_mul_of_nonneg_left hword (by positivity)
  calc ‖gloop L W M z' I‖ ≤ ‖gloop L W M z I‖ + ‖gloop L W M z' I - gloop L W M z I‖ := by
        have := norm_add_le (gloop L W M z I) (gloop L W M z' I - gloop L W M z I)
        simpa using this
    _ ≤ _ := by
        have := add_le_add hle hdiff
        linarith

end LoopMaxBounds




/-! ### 5. One step: the linear part, the Taylor remainder, its truncation -/

section Step

/-- `‖A‖² ≤ ∑ |A_ij|²`. -/
private theorem Duhamel_opNorm_sq_le_frob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  set F : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hbd : ‖A‖ ≤ Real.sqrt F := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hF, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg F, mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg F]

variable (d : Sizes) (n : ℕ)

/-- The truncation set `{‖X_{il}‖ ≤ N}` of one increment, `N = d.size n = (W L)²` (the event of
`gue_highProb_incr_le`). -/
def DuhamelGood : Set (Sizes.SeqΩ d) :=
  {y | ∀ i l : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n y i l‖ ≤ ((d.size n : ℕ) : ℝ)}

/-- The linear part `DΦ(M)[h(y)]` of one step. -/
def DuhamelZ (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (y : Sizes.SeqΩ d) : ℂ :=
  fderiv ℝ Φ M (Sizes.seqHflow d n v y)

/-- The Taylor remainder of one step. -/
def DuhamelR (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (y : Sizes.SeqΩ d) : ℂ :=
  Φ (M + Sizes.seqHflow d n v y) - Φ M - DuhamelZ d n Φ v M y

/-- The truncated remainder. -/
def DuhamelT (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (y : Sizes.SeqΩ d) : ℂ :=
  (DuhamelGood d n).indicator (DuhamelR d n Φ v M) y

/-- The truncation bias. -/
def DuhamelB (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) : ℂ :=
  ∫ y, (DuhamelGood d n)ᶜ.indicator (DuhamelR d n Φ v M) y ∂(gueUnit d)

variable {d n}

private theorem Duhamel_measurable_seqXentry (i j : Idx (d.L n) (d.W n)) :
    Measurable fun y : Sizes.SeqΩ d => Sizes.seqXmat d n y i j :=
  (measurable_Xentry (d.L n) (d.W n) i j).comp (Sizes.measurable_slice d n)

private theorem Duhamel_measurable_seqXmat : Measurable (Sizes.seqXmat d n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => Duhamel_measurable_seqXentry i j

private theorem Duhamel_measurable_seqHflow (v : ℝ) : Measurable (Sizes.seqHflow d n v) :=
  (Duhamel_measurable_seqXmat (d := d) (n := n)).const_smul (Real.sqrt v : ℂ)

theorem Duhamel_measurableSet_good : MeasurableSet (DuhamelGood d n) := by
  have h : DuhamelGood d n = ⋂ i : Idx (d.L n) (d.W n), ⋂ l : Idx (d.L n) (d.W n),
      {y | ‖Sizes.seqXmat d n y i l‖ ≤ ((d.size n : ℕ) : ℝ)} := by
    ext y; simp [DuhamelGood]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun l => ?_
  exact measurableSet_le (Duhamel_measurable_seqXentry i l).norm measurable_const

private theorem Duhamel_lin_eq_im (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n (-Complex.I • A) X = (Matrix.trace (A * X)).im := by
  unfold linTr
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- `Re Z = √v lin(A, X)`, `Im Z = √v lin(-iA, X)`, `A = gradMat Φ M`. -/
theorem Duhamel_Z_re_im (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) {v : ℝ}
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (y : Sizes.SeqΩ d) :
    (DuhamelZ d n Φ v M y).re = Real.sqrt v * linTr n (gradMat Φ M) (Sizes.seqXmat d n y) ∧
      (DuhamelZ d n Φ v M y).im
        = Real.sqrt v * linTr n (-Complex.I • gradMat Φ M) (Sizes.seqXmat d n y) := by
  have h : DuhamelZ d n Φ v M y
      = (Real.sqrt v : ℂ) * Matrix.trace (gradMat Φ M * Sizes.seqXmat d n y) := by
    have hX : Sizes.seqXmat d n y = Xmat (d.L n) (d.W n) (Sizes.slice d n y) := rfl
    unfold DuhamelZ
    rw [Sizes.seqHflow, Hflow_eq_realSmul, map_smul, hX,
      fderiv_eq_trace_gradMat M (Xmat_isHermitian _ _ _), Complex.real_smul]
  rw [h, Duhamel_lin_eq_im]
  constructor
  · rw [Complex.re_ofReal_mul]; rfl
  · rw [Complex.im_ofReal_mul]

private theorem Duhamel_integrable_lin
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Integrable (fun y => linTr n A (Sizes.seqXmat d n y)) (gueUnit d) ∧
      ∫ y, linTr n A (Sizes.seqXmat d n y) ∂(gueUnit d) = 0 := by
  have hmeas : Measurable (fun y : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n y)) := by
    unfold linTr
    exact Complex.measurable_re.comp
      ((Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).measurable.comp
        (Duhamel_measurable_seqXmat (d := d) (n := n)))
  have hmap := gueMap_lin_Xmat d n A
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 (vGue d n A)) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hid
    exact (integrable_map_measure hid.aestronglyMeasurable hmeas.aemeasurable).1 hid
  · have h := integral_map (μ := gueUnit d) hmeas.aemeasurable
      (f := fun x : ℝ => x) (measurable_id.aestronglyMeasurable)
    rw [hmap, integral_id_gaussianReal] at h
    exact h.symm

private theorem Duhamel_integrable_Z
    (Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Integrable (DuhamelZ d n Φ v M) (gueUnit d) ∧ ∫ y, DuhamelZ d n Φ v M y ∂(gueUnit d) = 0 := by
  obtain ⟨h1, h1'⟩ := Duhamel_integrable_lin (d := d) (n := n) (gradMat Φ M)
  obtain ⟨h2, h2'⟩ := Duhamel_integrable_lin (d := d) (n := n) (-Complex.I • gradMat Φ M)
  have hre : (fun y => RCLike.re (DuhamelZ d n Φ v M y))
      = fun y => Real.sqrt v * linTr n (gradMat Φ M) (Sizes.seqXmat d n y) :=
    funext fun y => (Duhamel_Z_re_im Φ M y).1
  have him : (fun y => RCLike.im (DuhamelZ d n Φ v M y))
      = fun y => Real.sqrt v * linTr n (-Complex.I • gradMat Φ M) (Sizes.seqXmat d n y) :=
    funext fun y => (Duhamel_Z_re_im Φ M y).2
  have hint : Integrable (DuhamelZ d n Φ v M) (gueUnit d) := by
    rw [← Integrable.re_im_iff, hre, him]
    exact ⟨h1.const_mul _, h2.const_mul _⟩
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have := integral_re hint
    rw [hre, integral_const_mul, h1', mul_zero] at this
    simpa using this.symm
  · have := integral_im hint
    rw [him, integral_const_mul, h2', mul_zero] at this
    simpa using this.symm

end Step


section Taylor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem Duhamel_hasDerivAt_add_smul (M y : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

private theorem Duhamel_isHermitian_add_smul {M y : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hy : y.IsHermitian) (t : ℝ) : (M + t • y).IsHermitian := by
  have hcast : M + t • y = M + (t : ℂ) • y := by rw [Complex.coe_smul]
  rw [hcast]
  exact hM.add (hy.smul (Complex.conj_ofReal t))

private theorem Duhamel_hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {M : E} (h : DifferentiableAt ℝ (fderiv ℝ f) M) (A : E) :
    HasFDerivAt (fun M' => fderiv ℝ f M' A) ((fderiv ℝ (fderiv ℝ f) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- **The pathwise second-order Taylor remainder bound along a Hermitian line**.  Only (H1) at
Hermitian points and the Hermitian-direction
bound (H3) are used. -/
private theorem Duhamel_taylor {Φ : Matrix ι ι ℂ → ℂ}
    (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M) {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix ι ι ℂ, M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {M y : Matrix ι ι ℂ} (hM : M.IsHermitian) (hy : y.IsHermitian) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  have hH := Duhamel_isHermitian_add_smul hM hy
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ Φ (M + t • y) :=
    fun t => (h _ (hH t)).differentiableAt (by norm_num)
  have hdiff2 : ∀ t : ℝ, DifferentiableAt ℝ (fderiv ℝ Φ) (M + t • y) := fun t =>
    ((h _ (hH t)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((hdiff t).hasFDerivAt).comp_hasDerivAt t (Duhamel_hasDerivAt_add_smul M y t)
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (Duhamel_hasFDerivAt_fderiv_apply (hdiff2 t) y).comp_hasDerivAt t
      (Duhamel_hasDerivAt_add_smul M y t)
    simp only [ContinuousLinearMap.flip_apply] at h1
    exact h1
  set k : ℝ → ℂ := fun t => fderiv ℝ Φ (M + t • y) y with hk_def
  have hkCont : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have hlevel1 : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖k t - k 0‖ ≤ C₂ * ‖y‖ ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hkCont.continuousOn (fun t _ => (hk t).hasDerivWithinAt)
      (fun t _ => by simpa using hC₂ (M + t • y) y (hH t) hy)
  have hg : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y)
      (k t - k 0) t := by
    intro t
    have h1 := (hp t).sub_const (Φ M)
    have h2 : HasDerivAt (fun t' : ℝ => t' • fderiv ℝ Φ M y) (fderiv ℝ Φ M y) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ Φ M y)
    have h3 := h1.sub h2
    have hk0 : k 0 = fderiv ℝ Φ M y := by simp [hk_def]
    rw [hk0]
    exact h3
  set g : ℝ → ℂ := fun t' => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y with hg_def
  have hgCont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set B : ℝ → ℝ := fun t => (C₂ / 2) * ‖y‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t : ℝ, HasDerivAt B (C₂ * ‖y‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.const_mul (C₂ / 2 * ‖y‖ ^ 2)
    have heq : C₂ / 2 * ‖y‖ ^ 2 * (2 * t) = C₂ * ‖y‖ ^ 2 * t := by ring
    rw [heq] at h2
    exact h2
  have ha0 : ‖g 0‖ ≤ B 0 := by simp [hg_def, hB_def]
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hgCont.continuousOn (fun t _ => (hg t).hasDerivWithinAt) ha0 hB
    (fun t ht => by simpa using hlevel1 t ⟨ht.1, ht.2.le⟩)
  have hgs := hfinal (Set.right_mem_Icc.2 hs)
  simp only [hg_def, hB_def] at hgs
  have heq : C₂ / 2 * ‖y‖ ^ 2 * s ^ 2 = C₂ / 2 * s ^ 2 * ‖y‖ ^ 2 := by ring
  linarith [hgs, heq]

end Taylor

section Step2

variable {d : Sizes} {n : ℕ}

/-- The pathwise Taylor remainder bound: `‖R‖ ≤ (C₂/2) v ‖X‖²`. -/
private theorem Duhamel_norm_R_le
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hM : M.IsHermitian) (y : Sizes.SeqΩ d) :
    ‖DuhamelR d n Φ v M y‖ ≤ C₂ / 2 * v * ‖Sizes.seqXmat d n y‖ ^ 2 := by
  have h := Duhamel_taylor hΦ.contDiffAt hC₂ hM (Sizes.seqXmat_isHermitian d n y)
    (Real.sqrt_nonneg v)
  have e : DuhamelR d n Φ v M y = Φ (M + Real.sqrt v • Sizes.seqXmat d n y) - Φ M
      - Real.sqrt v • fderiv ℝ Φ M (Sizes.seqXmat d n y) := by
    unfold DuhamelR DuhamelZ
    rw [Sizes.seqHflow, Hflow_eq_realSmul, map_smul]
    rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.sq_sqrt hv]

/-- `Φ(M + h(y))` is measurable in `y` for Hermitian `M`: `Φ` is continuous on the (closed)
Hermitian set and the increment is Hermitian. -/
private theorem Duhamel_measurable_Phi_line
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian) (v : ℝ) :
    Measurable (fun y : Sizes.SeqΩ d => Φ (M + Sizes.seqHflow d n v y)) := by
  set S : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) := {A | A.IsHermitian}
    with hS
  have hcont : ContinuousOn Φ S := fun A hA =>
    (hΦ.contDiffAt A hA).continuousAt.continuousWithinAt
  have hherm : ∀ y : Sizes.SeqΩ d, M + Sizes.seqHflow d n v y ∈ S := fun y =>
    hM.add (Sizes.seqHflow_isHermitian d n v y)
  have h1 : Measurable (S.domRestrict Φ) := hcont.domRestrict.measurable
  have h2 : Measurable (fun y : Sizes.SeqΩ d =>
      (⟨M + Sizes.seqHflow d n v y, hherm y⟩ : S)) :=
    Measurable.subtype_mk
      ((measurable_const (a := M)).add (Duhamel_measurable_seqHflow (d := d) (n := n) v))
  exact h1.comp h2

/-- Jointly measurable: for a measurable `Φ`, the remainder is measurable in `(M, y)`. -/
theorem Duhamel_measurable_R
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    (v : ℝ) :
    Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
      DuhamelR d n Φ v p.1 p.2) := by
  have hZ : Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
      Sizes.SeqΩ d => DuhamelZ d n Φ v p.1 p.2) := by
    have hrep : ∀ y : Sizes.SeqΩ d, Sizes.seqHflow d n v y
        = ∑ c : Coord (d.L n) (d.W n), (Real.sqrt v * y ⟨n, c⟩) • coordinateMatrix (d.L n) (d.W n) c := by
      intro y
      rw [Sizes.seqHflow_eq_smul, Complex.coe_smul]
      change Real.sqrt v • Sizes.seqXmat d n y = _
      rw [Sizes.seqXmat_eq_sum_coordinates, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_smul]
    have : (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        DuhamelZ d n Φ v p.1 p.2)
        = fun p => ∑ c : Coord (d.L n) (d.W n), (Real.sqrt v * p.2 ⟨n, c⟩) •
            fderiv ℝ Φ p.1 (coordinateMatrix (d.L n) (d.W n) c) := by
      funext p
      unfold DuhamelZ
      rw [hrep, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]
    rw [this]
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (measurable_const.mul ((measurable_pi_apply (⟨n, c⟩ : Sizes.SeqCoord d)).comp
      measurable_snd)).smul ((measurable_fderiv_apply_const ℝ Φ _).comp measurable_fst)
  have h1 : Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
      Sizes.SeqΩ d => Φ (p.1 + Sizes.seqHflow d n v p.2)) :=
    hΦm.comp (measurable_fst.add ((Duhamel_measurable_seqHflow (d := d) (n := n) v).comp measurable_snd))
  exact (h1.sub (hΦm.comp measurable_fst)).sub hZ

private theorem Duhamel_integrable_R
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    (v : ℝ) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian) :
    Integrable (DuhamelR d n Φ v M) (gueUnit d) ∧
      Integrable (fun y => Φ (M + Sizes.seqHflow d n v y)) (gueUnit d) := by
  obtain ⟨C₀, hC₀⟩ := hΦ.bdd₀
  have hΦint : Integrable (fun y => Φ (M + Sizes.seqHflow d n v y)) (gueUnit d) :=
    (memLp_top_of_bound (Duhamel_measurable_Phi_line hΦ hM v).aestronglyMeasurable C₀
      (Eventually.of_forall fun y =>
        hC₀ _ (hM.add (Sizes.seqHflow_isHermitian d n v y)))).integrable le_top
  refine ⟨?_, hΦint⟩
  have e : DuhamelR d n Φ v M
      = fun y => Φ (M + Sizes.seqHflow d n v y) - Φ M - DuhamelZ d n Φ v M y := rfl
  rw [e]
  exact (hΦint.sub (integrable_const _)).sub (Duhamel_integrable_Z Φ v M).1

/-- **The mean of one step**: `∫ Φ(M + h) = Φ(M) + ∫ T + B`.  The bound `hC₂` on the second
derivative is part of the statement but not used. -/
theorem Duhamel_integral_step
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    {C₂ : ℝ} (_hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (v : ℝ) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian) :
    ∫ y, Φ (M + Sizes.seqHflow d n v y) ∂(gueUnit d)
      = Φ M + ∫ y, DuhamelT d n Φ v M y ∂(gueUnit d) + DuhamelB d n Φ v M := by
  obtain ⟨hR, hΦint⟩ := Duhamel_integrable_R hΦ v hM
  obtain ⟨hZ, hZ0⟩ := Duhamel_integrable_Z Φ v M
  have hpt : (fun y => Φ (M + Sizes.seqHflow d n v y))
      = fun y => Φ M + (DuhamelZ d n Φ v M y + DuhamelR d n Φ v M y) := by
    funext y; unfold DuhamelR; ring
  have hZR : Integrable (fun y => DuhamelZ d n Φ v M y + DuhamelR d n Φ v M y) (gueUnit d) :=
    hZ.add hR
  rw [hpt, integral_add (integrable_const _) hZR, integral_add hZ hR, hZ0,
    integral_const, probReal_univ, one_smul, zero_add]
  have hsplit : DuhamelR d n Φ v M
      = fun y => DuhamelT d n Φ v M y + (DuhamelGood d n)ᶜ.indicator (DuhamelR d n Φ v M) y := by
    funext y; unfold DuhamelT; rw [Set.indicator_self_add_compl_apply]
  have hT : Integrable (DuhamelT d n Φ v M) (gueUnit d) := hR.indicator Duhamel_measurableSet_good
  have hB : Integrable ((DuhamelGood d n)ᶜ.indicator (DuhamelR d n Φ v M)) (gueUnit d) :=
    hR.indicator Duhamel_measurableSet_good.compl
  conv_lhs => rw [hsplit]
  rw [integral_add hT hB]
  unfold DuhamelB
  ring

end Step2


section LoopMeasurable

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Duhamel_measurable_mul {α : Type*} [MeasurableSpace α] {B : Type*} [Fintype B]
    {F G : α → Matrix B B ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun a => F a * G a) := by
  refine measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun q => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_pi_iff.1 (measurable_pi_iff.1 hF p) k).mul
      (measurable_pi_iff.1 (measurable_pi_iff.1 hG k) q)

private theorem Duhamel_measurable_nonsing_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable (fun A : Matrix m m ℂ => A⁻¹) := by
  have h : (fun A : Matrix m m ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [h]
  have h1 : Measurable (fun A : Matrix m m ℂ => Ring.inverse A.det) := by
    rw [Ring.inverse_eq_inv']
    exact (Continuous.matrix_det continuous_id).measurable.inv
  have h2 : Measurable (fun A : Matrix m m ℂ => A.adjugate) :=
    (Continuous.matrix_adjugate continuous_id).measurable
  exact h1.smul h2

/-- **The loop observable is measurable on all matrices** (`Measurable Φ` is the hypothesis of
`Duhamel_measurable_R`; `Φ` is only `C²` at Hermitian points, but it is a Borel function of the
matrix: the resolvent is the Borel map `A ↦ A⁻¹ = det⁻¹ · adj A`). -/
theorem Duhamel_measurable_loop (z : ℂ) (I : LoopIdx (Z2 L)) :
    Measurable (fun M : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M) z I) := by
  have hb : Continuous (fun M : Matrix (Idx L W) (Idx L W) ℂ => blockMat M) := by
    unfold blockMat
    exact continuous_id.matrix_submatrix _ _
  have hG : ∀ s : Bool,
      Measurable (fun M : Matrix (Idx L W) (Idx L W) ℂ => Gsig (blockMat M) z s) := by
    intro s
    unfold Gsig green
    exact Duhamel_measurable_nonsing_inv.comp (hb.sub continuous_const).measurable
  have hw : ∀ l : List (Bool × Z2 L), Measurable (fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      l.foldr (fun p X => Gsig (blockMat M) z p.1 * Eblk L W p.2 * X) 1) := by
    intro l
    induction l with
    | nil => exact measurable_const
    | cons p l ih =>
      simp only [List.foldr_cons]
      exact Duhamel_measurable_mul (Duhamel_measurable_mul (hG p.1) measurable_const) ih
  unfold gloop gloopProd
  exact (Continuous.matrix_trace continuous_id).measurable.comp (hw _)

end LoopMeasurable

section Bounds

variable {d : Sizes} {n : ℕ}

private theorem Duhamel_card_Idx : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Idx, Z2, ZMod.card, Sizes.size, pow_two]

private theorem Duhamel_norm_le_card_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A‖ ≤ (Fintype.card ι : ℝ) * B := by
  have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : ι, ∑ _j : ι, B ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  have h2 : ∑ _i : ι, ∑ _j : ι, B ^ 2 = ((Fintype.card ι : ℝ) * B) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    ((Duhamel_opNorm_sq_le_frob A).trans (h1.trans h2.le))

/-- The second-derivative bound forces `0 ≤ C₂` (the d = 2 replacement of the field `nonneg₂` of
`BddC2C`): evaluate it at `M = 0`, `y = E_{00}`. -/
private theorem Duhamel_nonneg_C2
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} {C₂ : ℝ}
    (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2) :
    0 ≤ C₂ := by
  set i : Idx (d.L n) (d.W n) := 0 with hi
  have hy : (Matrix.single i i (1 : ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  have h := hC₂ 0 (Matrix.single i i 1) Matrix.isHermitian_zero hy
  have hne : (Matrix.single i i (1 : ℂ) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
      ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 i) i
    simp at this
  have hpos : 0 < ‖(Matrix.single i i (1 : ℂ) : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)‖ ^ 2 := by
    have := norm_pos_iff.2 hne
    positivity
  by_contra hneg
  have hneg' : C₂ < 0 := not_le.mp hneg
  nlinarith [mul_neg_of_neg_of_pos hneg' hpos, norm_nonneg
    (fderiv ℝ (fderiv ℝ Φ) 0 (Matrix.single i i (1 : ℂ)) (Matrix.single i i (1 : ℂ)))]

/-- On the truncation set, `‖T‖ ≤ (C₂/2) v N⁴`, `N = d.size n` (`card (Idx) = N` and the truncation
threshold is `N`). -/
theorem Duhamel_norm_T_le
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hM : M.IsHermitian) (y : Sizes.SeqΩ d) :
    ‖DuhamelT d n Φ v M y‖ ≤ C₂ / 2 * v * ((d.size n : ℕ) : ℝ) ^ 4 := by
  have hC2 : 0 ≤ C₂ := Duhamel_nonneg_C2 hC₂
  unfold DuhamelT
  by_cases hy : y ∈ DuhamelGood d n
  · rw [Set.indicator_of_mem hy]
    refine (Duhamel_norm_R_le hΦ hC₂ hv hM y).trans ?_
    have hX : ‖Sizes.seqXmat d n y‖ ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ 4 := by
      have h1 := Duhamel_norm_le_card_mul (Sizes.seqXmat d n y)
        (B := ((d.size n : ℕ) : ℝ)) (by positivity) (fun i l => hy i l)
      rw [Duhamel_card_Idx] at h1
      calc ‖Sizes.seqXmat d n y‖ ^ 2
          ≤ (((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = ((d.size n : ℕ) : ℝ) ^ 4 := by ring
    have h0 : 0 ≤ C₂ / 2 * v := by positivity
    exact mul_le_mul_of_nonneg_left hX h0
  · rw [Set.indicator_of_notMem hy, norm_zero]
    positivity

end Bounds


/-! ### 6. The truncation bias -/

section Tail

/-- An entry of `Xmat` is bounded by its (at most four) raw coordinates. -/
private theorem Duhamel_norm_Xentry_le {L W : ℕ} [NeZero L] [NeZero W] (ω : Ω L W)
    (i j : Idx L W) :
    ‖Xentry L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

/-- `∑_{ij} |X_ij|² ≤ 2 ∑_c ω_c²`: every raw
coordinate enters at most two entries. -/
private theorem Duhamel_sumSq_Xentry_le {L W : ℕ} [NeZero L] [NeZero W] (ω : Ω L W) :
    ∑ i, ∑ l, ‖Xentry L W ω i l‖ ^ 2 ≤ 2 * ∑ c : Coord L W, (ω c) ^ 2 := by
  set q : Idx L W → Idx L W → ℝ := fun i j => (ω (i, j, true)) ^ 2 + (ω (i, j, false)) ^ 2
    with hq
  have hq0 : ∀ i j, 0 ≤ q i j := fun i j => by simp only [hq]; positivity
  have hpt : ∀ i j : Idx L W, ‖Xentry L W ω i j‖ ^ 2 ≤ q i j + q j i := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
    · have hX : ‖Xentry L W ω i j‖ ^ 2 = q i j := by
        rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
        simp only [hq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      rw [hX]; linarith [hq0 j i]
    · subst h
      have hX : ‖Xentry L W ω i i‖ ^ 2 = (ω (i, i, true)) ^ 2 := by
        rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
      rw [hX]
      have : 0 ≤ (ω (i, i, false)) ^ 2 := sq_nonneg _
      simp only [hq]
      nlinarith
    · have hX : ‖Xentry L W ω i j‖ ^ 2 = q j i := by
        rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
        simp only [hq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      rw [hX]; linarith [hq0 i j]
  have hsplit : ∑ c : Coord L W, (ω c) ^ 2 = ∑ i : Idx L W, ∑ j : Idx L W, q i j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
  have hswap : ∑ i : Idx L W, ∑ j : Idx L W, q j i = ∑ i : Idx L W, ∑ j : Idx L W, q i j :=
    Finset.sum_comm
  calc ∑ i, ∑ l, ‖Xentry L W ω i l‖ ^ 2 ≤ ∑ i : Idx L W, ∑ j : Idx L W, (q i j + q j i) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, q i j := by
        simp only [Finset.sum_add_distrib]
        rw [hswap]; ring
    _ = 2 * ∑ c : Coord L W, (ω c) ^ 2 := by rw [hsplit]

variable {d : Sizes} {n : ℕ}

private theorem Duhamel_exp_coord (c : ℝ) (t : Coord (d.L n) (d.W n)) :
    Integrable (fun y : Sizes.SeqΩ d => Real.exp (c * y ⟨n, t⟩)) (gueUnit d) ∧
      ∫ y, Real.exp (c * y ⟨n, t⟩) ∂(gueUnit d) ≤ Real.exp (c ^ 2 / 2) := by
  have hmeas : Measurable (fun y : Sizes.SeqΩ d => y ⟨n, t⟩) := measurable_pi_apply _
  have hmap : (gueUnit d).map (fun y : Sizes.SeqΩ d => y ⟨n, t⟩)
      = gaussianReal 0 (gueUnitVar d ⟨n, t⟩) := Measure.infinitePi_map_eval _ _
  have hlaw : HasLaw (fun y : Sizes.SeqΩ d => y ⟨n, t⟩) (gaussianReal 0 (gueUnitVar d ⟨n, t⟩))
      (gueUnit d) := ⟨hmeas.aemeasurable, hmap⟩
  have hv : (gueUnitVar d ⟨n, t⟩ : ℝ) ≤ 1 := by unfold gueUnitVar; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · have h := integrable_exp_mul_gaussianReal (μ := 0) (v := gueUnitVar d ⟨n, t⟩) c
    rw [← hmap] at h
    exact (integrable_map_measure h.aestronglyMeasurable hmeas.aemeasurable).1 h
  · have h := mgf_gaussianReal hlaw c
    have e : ∫ y, Real.exp (c * y ⟨n, t⟩) ∂(gueUnit d)
        = mgf (fun y : Sizes.SeqΩ d => y ⟨n, t⟩) (gueUnit d) c :=
      rfl
    rw [e, h]
    apply Real.exp_le_exp.2
    have : (gueUnitVar d ⟨n, t⟩ : ℝ) * c ^ 2 ≤ c ^ 2 := by
      nlinarith [sq_nonneg c, NNReal.coe_nonneg (gueUnitVar d ⟨n, t⟩)]
    linarith

/-- `ψ(t,t') = e^{2y_t} + e^{-2y_t} + e^{2y_{t'}} + e^{-2y_{t'}}`. -/
private def Duhamel_psi (n : ℕ) (y : Sizes.SeqΩ d) (t t' : Coord (d.L n) (d.W n)) : ℝ :=
  Real.exp (2 * y ⟨n, t⟩) + Real.exp (-2 * y ⟨n, t⟩)
    + Real.exp (2 * y ⟨n, t'⟩) + Real.exp (-2 * y ⟨n, t'⟩)

private theorem Duhamel_psi_nonneg (y : Sizes.SeqΩ d) (t t' : Coord (d.L n) (d.W n)) :
    0 ≤ Duhamel_psi n y t t' := by unfold Duhamel_psi; positivity

private theorem Duhamel_exp_two_abs_le (x : ℝ) :
    Real.exp (2 * |x|) ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-2 * x)]
  · rw [abs_of_nonpos h, show 2 * -x = -2 * x by ring]; linarith [Real.exp_pos (2 * x)]

/-- `x² ≤ 2 e^{|x|}`. -/
private theorem Duhamel_sq_le_two_exp (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  rw [sq_abs] at h
  nlinarith [abs_nonneg x]

/-- Off the truncation set, `∑_t y_t² ≤ e^{-N/4} ∑_{t,t'} ψ(t,t')`, `N = d.size n`. -/
private theorem Duhamel_coordSq_le_of_not_good {y : Sizes.SeqΩ d} (hy : y ∉ DuhamelGood d n) :
    ∑ t : Coord (d.L n) (d.W n), (y ⟨n, t⟩) ^ 2
      ≤ Real.exp (-((d.size n : ℕ) : ℝ) / 4) * ∑ t, ∑ t', Duhamel_psi n y t t' := by
  simp only [DuhamelGood, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨i, l, hil⟩ := hy
  have hent : ‖Sizes.seqXmat d n y i l‖ ≤ (|y ⟨n, (i, l, true)⟩| + |y ⟨n, (i, l, false)⟩|)
      + (|y ⟨n, (l, i, true)⟩| + |y ⟨n, (l, i, false)⟩|) :=
    Duhamel_norm_Xentry_le (Sizes.slice d n y) i l
  -- one of the four coordinates exceeds `N/4`
  obtain ⟨t', ht'⟩ : ∃ t' : Coord (d.L n) (d.W n),
      ((d.size n : ℕ) : ℝ) / 4 < |y ⟨n, t'⟩| := by
    by_contra hno
    push Not at hno
    have := hno (i, l, true); have := hno (i, l, false); have := hno (l, i, true)
    have := hno (l, i, false)
    linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hone : 1 ≤ Real.exp (|y ⟨n, t'⟩| - N / 4) := Real.one_le_exp (by linarith)
  have hterm : ∀ t : Coord (d.L n) (d.W n),
      (y ⟨n, t⟩) ^ 2 ≤ Real.exp (-N / 4) * Duhamel_psi n y t t' := by
    intro t
    have h1 := Duhamel_sq_le_two_exp (y ⟨n, t⟩)
    have h2 : 2 * Real.exp |y ⟨n, t⟩| ≤ 2 * Real.exp |y ⟨n, t⟩|
        * Real.exp (|y ⟨n, t'⟩| - N / 4) := by
      have : 0 ≤ 2 * Real.exp |y ⟨n, t⟩| := by positivity
      nlinarith
    have h3 : 2 * Real.exp |y ⟨n, t⟩| * Real.exp (|y ⟨n, t'⟩| - N / 4)
        = Real.exp (-N / 4) * (2 * (Real.exp |y ⟨n, t⟩| * Real.exp |y ⟨n, t'⟩|)) := by
      rw [Real.exp_sub]
      have : Real.exp (N / 4) ≠ 0 := (Real.exp_pos _).ne'
      rw [show -N / 4 = -(N / 4) by ring, Real.exp_neg]
      field_simp
    have h4 : 2 * (Real.exp |y ⟨n, t⟩| * Real.exp |y ⟨n, t'⟩|)
        ≤ Real.exp (2 * |y ⟨n, t⟩|) + Real.exp (2 * |y ⟨n, t'⟩|) := by
      have e1 : Real.exp (2 * |y ⟨n, t⟩|) = Real.exp |y ⟨n, t⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have e2 : Real.exp (2 * |y ⟨n, t'⟩|) = Real.exp |y ⟨n, t'⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg (Real.exp |y ⟨n, t⟩| - Real.exp |y ⟨n, t'⟩|)]
    have h5 : Real.exp (2 * |y ⟨n, t⟩|) + Real.exp (2 * |y ⟨n, t'⟩|) ≤ Duhamel_psi n y t t' := by
      unfold Duhamel_psi
      have := Duhamel_exp_two_abs_le (y ⟨n, t⟩)
      have := Duhamel_exp_two_abs_le (y ⟨n, t'⟩)
      linarith
    have hE : 0 ≤ Real.exp (-N / 4) := (Real.exp_pos _).le
    calc (y ⟨n, t⟩) ^ 2 ≤ 2 * Real.exp |y ⟨n, t⟩| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ Real.exp (-N / 4) * Duhamel_psi n y t t' :=
          mul_le_mul_of_nonneg_left (h4.trans h5) hE
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => (hterm t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Finset.single_le_sum (f := fun t'' => Duhamel_psi n y t t'')
    (fun _ _ => Duhamel_psi_nonneg y t _) (Finset.mem_univ t')

private theorem Duhamel_integrable_psi (t t' : Coord (d.L n) (d.W n)) :
    Integrable (fun y : Sizes.SeqΩ d => Duhamel_psi n y t t') (gueUnit d) ∧
      ∫ y, Duhamel_psi n y t t' ∂(gueUnit d) ≤ 4 * Real.exp 2 := by
  obtain ⟨i1, j1⟩ := Duhamel_exp_coord (d := d) (n := n) 2 t
  obtain ⟨i2, j2⟩ := Duhamel_exp_coord (d := d) (n := n) (-2) t
  obtain ⟨i3, j3⟩ := Duhamel_exp_coord (d := d) (n := n) 2 t'
  obtain ⟨i4, j4⟩ := Duhamel_exp_coord (d := d) (n := n) (-2) t'
  have hint : Integrable (fun y : Sizes.SeqΩ d => Duhamel_psi n y t t') (gueUnit d) :=
    ((i1.add i2).add i3).add i4
  refine ⟨hint, ?_⟩
  unfold Duhamel_psi
  have i12 : Integrable (fun y : Sizes.SeqΩ d => Real.exp (2 * y ⟨n, t⟩)
      + Real.exp (-2 * y ⟨n, t⟩)) (gueUnit d) := i1.add i2
  have i123 : Integrable (fun y : Sizes.SeqΩ d => Real.exp (2 * y ⟨n, t⟩)
      + Real.exp (-2 * y ⟨n, t⟩) + Real.exp (2 * y ⟨n, t'⟩)) (gueUnit d) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  have e : Real.exp ((2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  have e' : Real.exp ((-2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  rw [e] at j1 j3; rw [e'] at j2 j4
  linarith

/-- **The truncation bias**: `‖B‖ ≤ 16 e² C₂ v N⁴ e^{-N/4}`, `N = d.size n`. -/
theorem Duhamel_norm_B_le
    {Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΦ : HermTestFun d n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hM : M.IsHermitian) :
    ‖DuhamelB d n Φ v M‖ ≤ 16 * Real.exp 2 * C₂ * v * ((d.size n : ℕ) : ℝ) ^ 4
      * Real.exp (-((d.size n : ℕ) : ℝ) / 4) := by
  have hC2 : 0 ≤ C₂ := Duhamel_nonneg_C2 hC₂
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set g : Sizes.SeqΩ d → ℝ := fun y => C₂ / 2 * v * (2 * (Real.exp (-N / 4)
      * ∑ t, ∑ t', Duhamel_psi n y t t')) with hg
  have hgint : Integrable g (gueUnit d) := by
    refine ((integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (Duhamel_integrable_psi t t').1).const_mul _).const_mul _ |>.const_mul _
  have hpt : ∀ y, ‖(DuhamelGood d n)ᶜ.indicator (DuhamelR d n Φ v M) y‖ ≤ g y := by
    intro y
    have hg0 : 0 ≤ g y := by
      simp only [hg]
      have : 0 ≤ ∑ t, ∑ t', Duhamel_psi n y t t' :=
        Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun t' _ => Duhamel_psi_nonneg y t t'
      positivity
    by_cases hy : y ∈ DuhamelGood d n
    · rw [Set.indicator_of_notMem (by simpa using hy), norm_zero]; exact hg0
    · rw [Set.indicator_of_mem (by simpa using hy)]
      refine (Duhamel_norm_R_le hΦ hC₂ hv hM y).trans ?_
      have hX : ‖Sizes.seqXmat d n y‖ ^ 2 ≤ 2 * ∑ t : Coord (d.L n) (d.W n), (y ⟨n, t⟩) ^ 2 :=
        (Duhamel_opNorm_sq_le_frob _).trans (Duhamel_sumSq_Xentry_le (Sizes.slice d n y))
      have hc := Duhamel_coordSq_le_of_not_good hy
      have h0 : 0 ≤ C₂ / 2 * v := by positivity
      simp only [hg]
      exact mul_le_mul_of_nonneg_left (by linarith) h0
  refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)).trans ?_
  have hsum : ∫ y, ∑ t, ∑ t', Duhamel_psi n y t t' ∂(gueUnit d)
      ≤ ((Fintype.card (Coord (d.L n) (d.W n)) : ℝ)) ^ 2 * (4 * Real.exp 2) := by
    rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (Duhamel_integrable_psi t t').1]
    calc ∑ t, ∫ y, ∑ t', Duhamel_psi n y t t' ∂(gueUnit d)
        = ∑ t : Coord (d.L n) (d.W n), ∑ t' : Coord (d.L n) (d.W n),
            ∫ y, Duhamel_psi n y t t' ∂(gueUnit d) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_finsetSum _ fun t' _ => (Duhamel_integrable_psi t t').1
      _ ≤ ∑ _t : Coord (d.L n) (d.W n), ∑ _t' : Coord (d.L n) (d.W n), 4 * Real.exp 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ => (Duhamel_integrable_psi t t').2
      _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hcard : ((Fintype.card (Coord (d.L n) (d.W n)) : ℕ) : ℝ) = 2 * N ^ 2 := by
    rw [show Fintype.card (Coord (d.L n) (d.W n))
        = Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) × Bool) from rfl,
      Fintype.card_prod (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n) × Bool),
      Fintype.card_prod (Idx (d.L n) (d.W n)) Bool, Fintype.card_bool, Duhamel_card_Idx]
    push_cast; ring
  rw [hcard] at hsum
  simp only [hg]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hE : 0 ≤ Real.exp (-N / 4) := (Real.exp_pos _).le
  have h0 : 0 ≤ C₂ / 2 * v := by positivity
  calc C₂ / 2 * v * (2 * (Real.exp (-N / 4)
        * ∫ y, ∑ t, ∑ t', Duhamel_psi n y t t' ∂(gueUnit d)))
      ≤ C₂ / 2 * v * (2 * (Real.exp (-N / 4)
        * ((2 * N ^ 2) ^ 2 * (4 * Real.exp 2)))) := by
        gcongr
    _ = _ := by ring

end Tail


/-! ### 7. The grid: measurability, freezing, and the D3 remainder -/

section Grid

variable (d : Sizes)

/-- `ω ↦ ω i` is `filt d k`-measurable for `i ≤ k`. -/
theorem Duhamel_measurable_coord {i k : ℕ} (h : i ≤ k) :
    Measurable[filt d k] (fun ω : PathΩ d => ω i) := by
  have : (fun ω : PathΩ d => ω i)
      = (fun g : Set.Iic k → Sizes.SeqΩ d => g ⟨i, h⟩)
        ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨i, h⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k))

/-- A private copy of the (private) `StandardBorelSpace` instance of `Drift.lean`. -/
private instance Duhamel_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ))

/-- The grid path is `filt d k`-measurable as a matrix-valued map. -/
theorem Duhamel_gueH_measurable_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt d k] (gueH d t1 t0 K n k) :=
  @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun j =>
      (gueH_adapted d t1 t0 K n k i j).measurable

/-- The one-step recursion `H_{k+1} = H_k + h_v(X_{k+1})`, `v = Δ/N`, in the form of the
increment flow `Sizes.seqHflow`. -/
theorem Duhamel_gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    gueH d t1 t0 K n (k + 1) ω = gueH d t1 t0 K n k ω
      + Sizes.seqHflow d n (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) (ω (k + 1)) := by
  rw [gueH_succ]
  rfl

variable {d}

/-- Complex freezing under `Pgue` (real and imaginary parts of `gueCondExp_freeze`). -/
private theorem Duhamel_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℂ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (gueUnit d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set f : PathΩ d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Sizes.SeqΩ d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Sizes.SeqΩ d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pgue d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pgue d) := hInt.im
  have hfreezeRe := gueCondExp_freeze d k hY hFre hIntRe
  have hfreezeIm := gueCondExp_freeze d k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fre (Y ω) x ∂(gueUnit d) := by
    have hRe' : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fre (Y ω) (ω (k + 1)) | filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fim (Y ω) x ∂(gueUnit d) := by
    have hIm' : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fim (Y ω) (ω (k + 1)) | filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(gueUnit d) = RCLike.re (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(gueUnit d) = RCLike.im (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pgue d)[f | filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωre, hreEq]
  · change RCLike.im ((Pgue d)[f | filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωim, himEq]

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)`. -/
private def Duhamel_herm (A : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (Idx L W) (Idx L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem Duhamel_herm_isHermitian (A : Matrix (Idx L W) (Idx L W) ℂ) :
    (Duhamel_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem Duhamel_herm_of_isHermitian {A : Matrix (Idx L W) (Idx L W) ℂ}
    (hA : A.IsHermitian) : Duhamel_herm A = A := by
  unfold Duhamel_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem Duhamel_continuous_herm :
    Continuous (Duhamel_herm : Matrix (Idx L W) (Idx L W) ℂ → _) := by
  unfold Duhamel_herm
  have h1 : Continuous fun A : Matrix (Idx L W) (Idx L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix. -/
private def Duhamel_Phi (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : LoopIdx (Z2 L))
    (A : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  gloop L W (blockMat (Duhamel_herm A)) z I

private theorem Duhamel_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    Continuous (Duhamel_Phi L W z I) := by
  refine continuous_iff_continuousAt.2 fun A => ?_
  exact (Duhamel_contDiffAt_loop hz I (Duhamel_herm_isHermitian A)).continuousAt.comp
    Duhamel_continuous_herm.continuousAt

private theorem Duhamel_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hwf : I.WF)
    (A : Matrix (Idx L W) (Idx L W) ℂ) :
    ‖Duhamel_Phi L W z I A‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) * (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
  norm_gloop_le_crude L W ((Duhamel_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl I hwf

end Observable

/-- **The drift remainder**: the conditional mean of the next loop minus the loop and its
drift is bounded by the remainder `envConst · Δ^{3/2}` of `condExp_loop_drift_gue`, almost
surely. -/
theorem Duhamel_drift_remainder_ae (d : Sizes) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (e : ℝ)
    (he : |e| < 2) {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) :
    ∀ᵐ ω ∂(Pgue d),
      ‖(∫ y, gloop (d.L n) (d.W n)
            (blockMat (gueH d t1 t0 K n k ω
              + Sizes.seqHflow d n (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) y))
            (spectralZ e (gridTime t1 t0 K n (k + 1))) I ∂(gueUnit d))
          - gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
              (spectralZ e (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) *
              genMatGUE (d.L n) (d.W n) e (gridTime t1 t0 K n k) (gueH d t1 t0 K n k ω) I‖
        ≤ envConst (d.L n) (d.W n) e I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  set z1 := spectralZ e (gridTime t1 t0 K n (k + 1)) with hz1
  set v := gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ) with hv
  have hu1lt : gridTime t1 t0 K n (k + 1) < 1 := by
    have hKpos : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
    have hk1 : (k : ℝ) + 1 ≤ (K n : ℝ) := by exact_mod_cast hk
    have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
      unfold gridStep; exact div_nonneg (by linarith) hKpos.le
    have hKΔ : (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n := by unfold gridStep; field_simp
    have h : gridTime t1 t0 K n (k + 1) = t1 n + ((k : ℝ) + 1) * gridStep t1 t0 K n := by
      unfold gridTime; push_cast; ring
    rw [h]; nlinarith
  have hz1ne : z1.im ≠ 0 := by
    rw [hz1, spectralZ_im]
    exact (mul_pos (sub_pos.2 hu1lt) (spectralM_im_pos he)).ne'
  set F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℂ :=
    fun p y => Duhamel_Phi (d.L n) (d.W n) z1 I (p + Sizes.seqHflow d n v y) with hF
  have hΦcont := Duhamel_continuous_Phi (L := d.L n) (W := d.W n) hz1ne I
  have hFmeas : Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
      Sizes.SeqΩ d => F p.1 p.2) :=
    hΦcont.measurable.comp (measurable_fst.add
      ((Duhamel_measurable_seqHflow (d := d) (n := n) v).comp measurable_snd))
  have hFbdd : ∀ p y, ‖F p y‖ ≤ (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) *
      (|z1.im|⁻¹ * (((d.W n : ℕ) : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
    fun p y => Duhamel_norm_Phi_le hz1ne hwf _
  have hFInt : ∀ p, Integrable (F p) (gueUnit d) := by
    intro p
    have hm : Measurable (fun y : Sizes.SeqΩ d => F p y) := by
      have h := hFmeas.comp (measurable_const.prodMk measurable_id : Measurable fun y : Sizes.SeqΩ d => (p, y))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun y => hFbdd p y)).integrable le_top
  have hYmeas := Duhamel_gueH_measurable_filt d t1 t0 K n k
  have hYmeas' : Measurable (gueH d t1 t0 K n k) := hYmeas.mono ((filt d).le k) le_rfl
  have hIntTarget : Integrable (fun ω : PathΩ d => F (gueH d t1 t0 K n k ω) (ω (k + 1)))
      (Pgue d) := by
    have hm : Measurable (fun ω : PathΩ d => F (gueH d t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hfreeze := Duhamel_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget
  have hEq : (fun ω' : PathΩ d =>
        gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n (k + 1) ω')) z1 I)
      = fun ω => F (gueH d t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (gueH d t1 t0 K n (k + 1) ω).IsHermitian := gueH_isHermitian d t1 t0 K n (k + 1) ω
    simp only [hF, Duhamel_Phi]
    rw [← Duhamel_gueH_succ d t1 t0 K n k ω, Duhamel_herm_of_isHermitian hH]
  have hD3 := condExp_loop_drift_gue d t1 t0 K n k e he hwf ht1 hst (by omega) hk hu1lt
  rw [hEq] at hD3
  filter_upwards [hD3, hfreeze] with ω h1 h2
  rw [h2] at h1
  have hFeq : ∀ y, F (gueH d t1 t0 K n k ω) y = gloop (d.L n) (d.W n)
      (blockMat (gueH d t1 t0 K n k ω + Sizes.seqHflow d n v y)) z1 I := by
    intro y
    have hh : (gueH d t1 t0 K n k ω + Sizes.seqHflow d n v y).IsHermitian :=
      (gueH_isHermitian d t1 t0 K n k ω).add (Sizes.seqHflow_isHermitian d n v y)
    simp only [hF, Duhamel_Phi]
    rw [Duhamel_herm_of_isHermitian hh]
  simp only [hFeq] at h1
  exact h1

end Grid


end RBM.Univ.GUEPhase

end
