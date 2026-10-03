/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab

/-!
# The general-`n` variance proxy `QVPropagatedN`

One public theorem,
`qvPropagatedN : QVPropagatedN` (the statement of `RBM2D.Induction.HierVocab`): for a
Hermitian `M`, a loop of length `k ≥ 2`, every sign vector `σ` and every coefficient family `κ`,
`Σ_c gvar_c |Σ_b κ_b ∂_c 𝓛_{σ,b}|² ≤ k · Re Σ_{b,b'} κ_b conj κ_{b'} (𝓔⊗𝓔)_{σ,b,b'}`.
At `k = 2`, `σ = (+,-)` this is `qvPropagated` (`RBM2D.Path.QVIdentity`).

Paper: arXiv:2503.07606, Section 5: `def:CALE` (`defEOTE`, `def_diffakn_k`); the paper describes
`𝓔⊗𝓔` combinatorially and never writes the per-cut identity explicitly, so it is proved here.

Proof, in the order of the file:
* (section 1) the coordinate algebra `Σ_c gvar_c ⟨X̂_c, F⟩ conj ⟨X̂_c, G⟩ = W² Σ S^B tr(F E G* E)`,
  repeating private lemmas of `RBM2D.Path.QVIdentity`;
* (sections 2-3) words `∏ G^{σ_i} E_{a_i}` of pair lists; Leibniz `∂_X 𝓛_{σ,b} = -Σ_j tr(X̂ A_j(b))`
  with the cut chain `A_j(b) = ∏_{i ≥ j} · ∏_{i < j} · G^{σ_j}` (`dG = -G X̂ G`, cyclicity); the
  glued loop `eeLoop σ b b' (j+1) β β' = tr(A_j(b) E_{β'} A_j(b')ᴴ E_β)` (`G(σ)ᴴ = G(σ̄)` for
  Hermitian `M`, and the reverse-and-flip chain `QVN_rflip`);
* (section 4) the per-cut identity, `𝓔⊗𝓔 = Σ_j (cut j)`, and Cauchy–Schwarz over the `k` cuts.

The argument parallels the one-dimensional formalization, with `ZMod L → Z2 L`, block size
`W → W²` and the Wirtinger gradient replaced by the directional derivative along
`coordinateMatrix c`: `QVN_rflip`, `QVN_wd_append`, `QVN_wd_rflip`, `QVN_eeLoop_zip`,
`QVN_eeLoop_gloop`, `QVN_cut`, `QVN_loopDerivN_eq`, `QVN_eeN_eq`, `QVN_sum_Icc_fin`,
`QVN_norm_sum_sq_le`.

Every helper is `private` and carries the prefix `QVN_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Gauss RBM.Path

/-! ## 1. Coordinate algebra -/

section CoordAlgebra

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem QVN_cm_lt {i j : Idx L W} (h : idxKey L W i < idxKey L W j) (b : Bool) :
    coordinateMatrix L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind


private theorem QVN_cm_diag_true (i : Idx L W) :
    coordinateMatrix L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVN_cm_diag_false (i : Idx L W) :
    coordinateMatrix L W (i, i, false) = 0 := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVN_cm_gt {i j : Idx L W} (h : idxKey L W j < idxKey L W i) (b : Bool) :
    coordinateMatrix L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The pairing `Σ_{k,l} X_{kl} f_{lk}` (the trace `tr(X F)` with `F_{lk} = f l k`). -/
private def QVN_pair (X : Matrix (Idx L W) (Idx L W) ℂ) (f : Idx L W → Idx L W → ℂ) : ℂ :=
  ∑ k, ∑ l, X k l * f l k

private theorem QVN_pair_single (i j : Idx L W) (x : ℂ) (f : Idx L W → Idx L W → ℂ) :
    QVN_pair (Matrix.single i j x) f = x * f j i := by
  simp only [QVN_pair, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem QVN_pair_add (X Y : Matrix (Idx L W) (Idx L W) ℂ)
    (f : Idx L W → Idx L W → ℂ) :
    QVN_pair (X + Y) f = QVN_pair X f + QVN_pair Y f := by
  simp only [QVN_pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem QVN_pair_zero (f : Idx L W → Idx L W → ℂ) :
    QVN_pair (0 : Matrix (Idx L W) (Idx L W) ℂ) f = 0 := by
  simp [QVN_pair]

/-- Sum of an ordered-pair function over the three cases of `idxKey`. -/
private theorem QVN_sum_tri (T : Idx L W → Idx L W → ℂ) :
    (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T i j + T j i
      else if i = j then T i i else 0) = ∑ i, ∑ j, T i j := by
  have hpt : ∀ i j, (if idxKey L W i < idxKey L W j then T i j + T j i
      else if i = j then T i i else 0) =
      ((if idxKey L W i < idxKey L W j then T i j else 0) +
        (if idxKey L W i < idxKey L W j then T j i else 0)) +
        (if i = j then T i j else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [h, hij]
    · subst h; simp
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [not_lt.mpr h.le, hij]
  have hswap : (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T j i else 0) =
      ∑ i, ∑ j, if idxKey L W j < idxKey L W i then T i j else 0 := Finset.sum_comm
  calc (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T i j + T j i
        else if i = j then T i i else 0)
      = (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T j i else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by
        simp only [hpt, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if idxKey L W i < idxKey L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey L W j < idxKey L W i then T i j else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by rw [hswap]
    _ = ∑ i, ∑ j, (((if idxKey L W i < idxKey L W j then T i j else 0) +
          (if idxKey L W j < idxKey L W i then T i j else 0)) +
          (if i = j then T i j else 0)) := by simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, T i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]
        · subst h; simp
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]

/-- **Coordinate sum of a sesquilinear pairing.**  For every pair of kernels `f, g`,
`Σ_c gvar_c ⟨X_c, f⟩ conj ⟨X_c, g⟩ = Σ_{k,l} svar_{kl} f_{lk} conj g_{lk}`. -/
private theorem QVN_coord_sum (f g : Idx L W → Idx L W → ℂ) :
    ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (QVN_pair (coordinateMatrix L W c) f *
          (starRingEnd ℂ) (QVN_pair (coordinateMatrix L W c) g)) =
      ∑ k, ∑ l, (svar L W k l : ℂ) * (f l k * (starRingEnd ℂ) (g l k)) := by
  have hc : ∀ F : Coord L W → ℂ,
      ∑ c : Coord L W, F c = ∑ i : Idx L W, ∑ j : Idx L W, (F (i, j, true) + F (i, j, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Fintype.sum_bool _
  rw [← QVN_sum_tri, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_left h, QVN_cm_lt h, QVN_cm_lt h, gvar_offDiag L W i j true hij,
      gvar_offDiag L W i j false hij, svar_comm L W j i]
    simp only [QVN_pair_add, QVN_pair_single, ite_true, Bool.false_eq_true,
      ite_false, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, QVN_cm_diag_true,
      QVN_cm_diag_false,
      gvar_diag, gvar_diag]
    simp [QVN_pair_single, QVN_pair_zero]
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right hij, QVN_cm_gt h, QVN_cm_gt h]
    simp [QVN_pair_zero]

/-- `tr(blockMat X · A) = Σ_{k,l} X_{kl} A_{e l, e k}` with `e = splitEquiv`. -/
private theorem QVN_trace_blockMat_mul (X : Matrix (Idx L W) (Idx L W) ℂ)
    (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (blockMat X * A) =
      QVN_pair X (fun l k => A (splitEquiv L W l) (splitEquiv L W k)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, blockMat, Matrix.submatrix_apply,
    QVN_pair]
  rw [← (splitEquiv L W).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (splitEquiv L W).sum_comp]
  simp

/-- Reordering four finite sums. -/
private theorem QVN_sum_swap4 {α β : Type*} [Fintype α] [Fintype β]
    (F : α → α → β → β → ℂ) :
    ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
  calc ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ b, ∑ q, ∑ p, ∑ b', F b b' q p := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- **From the fine variance to block insertions.**
`Σ_{k,l} svar_{kl} A_{e l,e k} conj B_{e l,e k} = W² Σ_{b,b'} S^{(B)}_{bb'} tr(A E_b Bᴴ E_{b'})`. -/
private theorem QVN_svar_sum (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ k, ∑ l, (svar L W k l : ℂ) *
        (A (splitEquiv L W l) (splitEquiv L W k) *
          (starRingEnd ℂ) (B (splitEquiv L W l) (splitEquiv L W k))) =
      (W : ℂ) ^ 2 * ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        Matrix.trace (A * Eblk L W b * Bᴴ * Eblk L W b') := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  -- the left side over block indices
  have hL : ∑ k, ∑ l, (svar L W k l : ℂ) *
        (A (splitEquiv L W l) (splitEquiv L W k) *
          (starRingEnd ℂ) (B (splitEquiv L W l) (splitEquiv L W k))) =
      ∑ p : BlockIndex L W, ∑ q : BlockIndex L W,
        SB L p.1 q.1 * (W : ℂ)⁻¹ ^ 2 * (A q p * (starRingEnd ℂ) (B q p)) := by
    rw [← (splitEquiv L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (splitEquiv L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [svar_cast_eq_Spaper, Spaper_eq]
    simp only [Equiv.apply_symm_apply]
    change Svar L W (splitEquiv L W ((splitEquiv L W).symm p))
        (splitEquiv L W ((splitEquiv L W).symm q)) * _ = _
    simp only [Equiv.apply_symm_apply]
    obtain ⟨a, α⟩ := p
    obtain ⟨b, β⟩ := q
    rw [Svar_apply]
  have htr : ∀ b b' : Z2 L, Matrix.trace (A * Eblk L W b * Bᴴ * Eblk L W b') =
      ∑ q : BlockIndex L W, ∑ p : BlockIndex L W,
        (if p.1 = b then (W : ℂ)⁻¹ ^ 2 else 0) * (if q.1 = b' then (W : ℂ)⁻¹ ^ 2 else 0) *
          (A q p * (starRingEnd ℂ) (B q p)) := by
    intro b b'
    simp only [Matrix.trace, Matrix.diag, Eblk, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 = b'
    · simp only [hq, ite_true]
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.1 = b
      · simp only [hp, ite_true, RCLike.star_def]; ring
      · simp [hp]
    · simp [hq]
  have hcollapse : ∀ (x y : BlockIndex L W) (C : ℂ),
      ∑ b : Z2 L, ∑ b' : Z2 L, (W : ℂ) ^ 2 * (SB L b b' *
        ((if x.1 = b then (W : ℂ)⁻¹ ^ 2 else 0) * (if y.1 = b' then (W : ℂ)⁻¹ ^ 2 else 0) *
          C)) = (W : ℂ) ^ 2 * (SB L x.1 y.1 * ((W : ℂ)⁻¹ ^ 2 * (W : ℂ)⁻¹ ^ 2 * C)) := by
    intro x y C
    rw [Finset.sum_eq_single x.1]
    · rw [Finset.sum_eq_single y.1]
      · simp
      · intro b' _ hb'; simp [Ne.symm hb']
      · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hL]
  simp only [htr, Finset.mul_sum]
  rw [QVN_sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hcollapse]
  field_simp

end CoordAlgebra

/-! ## 2. Words, reversal and the glued loop -/

section Words

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The word `∏_{p ∈ l} G_{p.1} E_{p.2}` of a list of `(sign, label)` pairs at `(E, u, M)`. -/
private def QVN_wd (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : List (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p Z => greenBlk L W E u M p.1 * Eblk L W p.2 * Z) 1

private theorem QVN_wd_cons (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p : Bool × Z2 L)
    (l : List (Bool × Z2 L)) :
    QVN_wd E u M (p :: l) = greenBlk L W E u M p.1 * Eblk L W p.2 * QVN_wd E u M l := rfl

private theorem QVN_wd_append (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (l₁ l₂ : List (Bool × Z2 L)) :
    QVN_wd E u M (l₁ ++ l₂) = QVN_wd E u M l₁ * QVN_wd E u M l₂ := by
  have QVN_wd_nil (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
      QVN_wd E u M ([] : List (Bool × Z2 L)) =
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := rfl
  induction l₁ with
  | nil => simp [QVN_wd_nil]
  | cons p l ih => simp [QVN_wd_cons, ih, Matrix.mul_assoc]

private theorem QVN_greenBlk_conjTranspose (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (σ : Bool) :
    (greenBlk L W E u M σ)ᴴ = greenBlk L W E u M (!σ) :=
  Gsig_conjTranspose (hM.submatrix _) _ σ

/-- **Reverse a chain and flip its charges**:
`QVN_rflip t l c` reads `l` backwards with every charge flipped, prefixed by the charge `t` and
closed by the label `c`. -/
private def QVN_rflip (t : Bool) : List (Bool × Z2 L) → Z2 L → List (Bool × Z2 L)
  | [], c => [(t, c)]
  | p :: l, c => QVN_rflip t l p.2 ++ [(!p.1, c)]

/-- **The conjugate-transposed chain is a chain again**:
`G(t) · (∏ G E)ᴴ · E_c` is the word of `QVN_rflip t l c`, for Hermitian `M`. -/
private theorem QVN_wd_rflip (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (t : Bool) (l : List (Bool × Z2 L)) (c : Z2 L) :
    greenBlk L W E u M t * (QVN_wd E u M l)ᴴ * Eblk L W c = QVN_wd E u M (QVN_rflip t l c) := by
  have QVN_wd_nil (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
      QVN_wd E u M ([] : List (Bool × Z2 L)) =
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := rfl
  induction l generalizing c with
  | nil => simp [QVN_rflip, QVN_wd_nil, QVN_wd_cons]
  | cons p l ih =>
    rw [QVN_rflip, QVN_wd_append, ← ih p.2, QVN_wd_cons, QVN_wd_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Eblk_conjTranspose,
      QVN_greenBlk_conjTranspose E u hM]
    simp [Matrix.mul_assoc, QVN_wd_nil]

/-- `QVN_rflip` in closed form: the zip of the flipped reversed charges (led by `t`) with the
reversed labels (closed by `c`). -/
private theorem QVN_rflip_eq_zip (t : Bool) (l : List (Bool × Z2 L)) (c : Z2 L) :
    QVN_rflip t l c =
      (t :: l.reverse.map (fun p => !p.1)).zip (l.reverse.map Prod.snd ++ [c]) := by
  induction l generalizing c with
  | nil => simp [QVN_rflip]
  | cons p l ih =>
    rw [QVN_rflip, ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [← List.cons_append, List.zip_append (by simp)]
    rfl

/-- Rotation of a zipped chain is the zip of the rotations. -/
private theorem QVN_rot_zip {α β : Type*} (σ : List α) (a : List β) (h : σ.length = a.length)
    (q : ℕ) :
    (σ.zip a).drop q ++ (σ.zip a).take q = (σ.drop q ++ σ.take q).zip (a.drop q ++ a.take q) := by
  rw [List.zip_append (by simp [h]), List.zip_eq_zipWith, List.drop_zipWith, List.take_zipWith]
  simp [List.zip_eq_zipWith]

/-- The charges and labels of a zipped chain, reversed (and flipped). -/
private theorem QVN_flip_zip (σ : List Bool) (a : List (Z2 L)) (h : σ.length = a.length) :
    ((σ.zip a).reverse.map (fun p => !p.1)) = σ.reverse.map not ∧
      ((σ.zip a).reverse.map Prod.snd) = a.reverse := by
  have h1 : (σ.zip a).map Prod.fst = σ := List.map_fst_zip h.le
  have h2 : (σ.zip a).map Prod.snd = a := List.map_snd_zip h.ge
  have e : (σ.zip a).map (fun p => !p.1) = σ.map not := by
    have := congrArg (List.map not) h1
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨?_, ?_⟩
  · rw [List.map_reverse, e, ← List.map_reverse]
  · rw [List.map_reverse, h2]

/-- **The glued `(2n+2)`-loop as a chain** (the layout `eeLoop` of `Induction/HierVocab.lean` at
cut `q + 1`, read as pairs): the cut chain `rot_q(σ,a) · (σ_q, b')`, then the reversed and
flipped rotated chain of `a'` closed by `b`. -/
private theorem QVN_eeLoop_zip (σ : List Bool) (a a' : List (Z2 L)) (h1 : σ.length = a.length)
    (h2 : σ.length = a'.length) {q : ℕ} (hq : q < σ.length) (b b' : Z2 L) :
    (eeLoop L σ a a' (q + 1) b b').σ.zip (eeLoop L σ a a' (q + 1) b b').a =
      (((σ.zip a).drop q ++ (σ.zip a).take q) ++ [(σ[q], b')]) ++
        QVN_rflip (!σ[q]) ((σ.zip a').drop q ++ (σ.zip a').take q) b := by
  rw [QVN_rot_zip σ a h1, QVN_rot_zip σ a' h2, QVN_rflip_eq_zip]
  have hlen : (σ.drop q ++ σ.take q).length = (a'.drop q ++ a'.take q).length := by simp [h2]
  have hlen1 : (σ.drop q ++ σ.take q).length = (a.drop q ++ a.take q).length := by simp [h1]
  obtain ⟨f1, f2⟩ := QVN_flip_zip (σ.drop q ++ σ.take q) (a'.drop q ++ a'.take q) hlen
  rw [f1, f2, show [(σ[q], b')] = [σ[q]].zip [b'] from rfl, ← List.zip_append hlen1,
    ← List.zip_append (by simp only [List.length_append, List.length_singleton, hlen1])]
  simp only [eeLoop, Nat.add_sub_cancel]
  congr 1
  · rw [List.take_succ_eq_append_getElem hq]
    simp only [List.reverse_append, List.map_append, List.map_cons, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]
  · simp [List.reverse_append, List.append_assoc]

end Words

/-! ## 3. The Leibniz rule and the cut decomposition -/

section Deriv

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

set_option linter.unusedDecidableInType false in
/-- The trace of a differentiable matrix path. -/
private theorem QVN_hasDerivAt_trace {n : Type*} [Fintype n] [DecidableEq n]
    {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- `∂_y G^σ(M + yX)|_{y=0} = -G^σ X̂ G^σ` (the resolvent derivative, for either sign). -/
private theorem QVN_hasDerivAt_greenBlk {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (X : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) :
    HasDerivAt (fun y : ℝ => greenBlk L W E u (M + (y : ℂ) • X) σ)
      (-(greenBlk L W E u M σ * blockMat X * greenBlk L W E u M σ)) 0 := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  set Hy : ℝ → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun y => blockMat M + (y : ℂ) • blockMat X with hHy
  have hH0 : Hy 0 = blockMat M := by simp [hHy]
  have hline : HasDerivAt Hy (blockMat X) 0 := hasDerivAt_line _ _ 0
  have hfun : (fun y : ℝ => greenBlk L W E u (M + (y : ℂ) • X) σ) =
      fun y => Gsig (Hy y) (spectralZ E u) σ := by
    funext y
    simp only [greenBlk, hHy]
    rfl
  rw [hfun]
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving hline (hasDerivAt_const (0 : ℝ) (spectralZ E u))
        (by rw [hH0]; exact hH) hz
      simpa [hH0, greenBlk] using h
  | false =>
      have hz' : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by simpa using hz
      have h := hasDerivAt_green_moving hline
        (hasDerivAt_const (0 : ℝ) ((starRingEnd ℂ) (spectralZ E u))) (by rw [hH0]; exact hH) hz'
      simpa [hH0, greenBlk] using h

/-- Differentiate the first factor of the word `m`: `head (p :: m') = (-(G X̂ G) E_p) · wd m'`. -/
private def QVN_head (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ) :
    List (Bool × Z2 L) → Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  | [] => 0
  | p :: m => (-(greenBlk L W E u M p.1 * blockMat X * greenBlk L W E u M p.1) *
      Eblk L W p.2) * QVN_wd E u M m

/-- The Leibniz sum of a word: differentiate the `q`-th factor, `q < |l|`. -/
private def QVN_wordDeriv (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  ∑ q ∈ Finset.range l.length, QVN_wd E u M (l.take q) * QVN_head E u M X (l.drop q)

private theorem QVN_wordDeriv_cons (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    QVN_wordDeriv E u M X (p :: l) = QVN_head E u M X (p :: l) +
      greenBlk L W E u M p.1 * Eblk L W p.2 * QVN_wordDeriv E u M X l := by
  have QVN_wd_nil (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
      QVN_wd E u M ([] : List (Bool × Z2 L)) =
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := rfl
  unfold QVN_wordDeriv
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, QVN_wd_cons, List.take_zero,
    List.drop_zero, QVN_wd_nil, Matrix.one_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [add_comm]

/-- **Leibniz rule for a word** in the direction `X`. -/
private theorem QVN_hasDerivAt_wd {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx L W) (Idx L W) ℂ)
    (l : List (Bool × Z2 L)) :
    HasDerivAt (fun y : ℝ => QVN_wd E u (M + (y : ℂ) • X) l) (QVN_wordDeriv E u M X l) 0 := by
  have QVN_wd_nil (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
      QVN_wd E u M ([] : List (Bool × Z2 L)) =
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := rfl
  induction l with
  | nil =>
      have h0 : QVN_wordDeriv E u M X ([] : List (Bool × Z2 L)) = 0 := by
        simp [QVN_wordDeriv]
      rw [h0]
      simpa only [QVN_wd_nil] using
        hasDerivAt_const (0 : ℝ) (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have hhead := (QVN_hasDerivAt_greenBlk hE hu hM X p.1).mul_const (Eblk L W p.2)
      have h := hhead.mul ih
      rw [QVN_wordDeriv_cons]
      have hfun : (fun y : ℝ => QVN_wd E u (M + (y : ℂ) • X) (p :: l)) =
          fun y : ℝ => greenBlk L W E u (M + (y : ℂ) • X) p.1 * Eblk L W p.2 *
            QVN_wd E u (M + (y : ℂ) • X) l := rfl
      rw [hfun]
      convert h using 1
      simp [QVN_head]

/-- The `q`-th Leibniz term as a pairing against the cut chain:
`tr(wd(l[:q]) · ∂_q) = -tr(X̂ · wd(l[q:] ++ l[:q]) · G^{l_q})` (cyclicity of the trace). -/
private theorem QVN_trace_term (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    (l : List (Bool × Z2 L)) {q : ℕ} (hq : q < l.length) :
    Matrix.trace (QVN_wd E u M (l.take q) * QVN_head E u M X (l.drop q)) =
      -Matrix.trace (blockMat X * (QVN_wd E u M (l.drop q ++ l.take q) *
        greenBlk L W E u M l[q].1)) := by
  rw [List.drop_eq_getElem_cons hq, QVN_head, QVN_wd_append, QVN_wd_cons]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [show QVN_wd E u M (l.take q) * (greenBlk L W E u M l[q].1 * blockMat X *
        greenBlk L W E u M l[q].1 * Eblk L W l[q].2 * QVN_wd E u M (l.drop (q + 1))) =
      (QVN_wd E u M (l.take q) * greenBlk L W E u M l[q].1) *
        (blockMat X * (greenBlk L W E u M l[q].1 * Eblk L W l[q].2 *
          QVN_wd E u M (l.drop (q + 1)))) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The cut chain of edge `j`: `A_j(b) = wd(rot_j(σ, b)) · G^{σ_j}`, where `rot_j` starts the
chain at the `j`-th factor. -/
private def QVN_cut (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Z2 L) (j : Fin k) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  QVN_wd E u M (((List.ofFn σ).zip (List.ofFn b)).drop j ++
      ((List.ofFn σ).zip (List.ofFn b)).take j) * greenBlk L W E u M (σ j)

/-- **Leibniz decomposition of the loop derivative**: `∂_X 𝓛_{σ,b} = -Σ_j tr(X̂ · A_j(b))`. -/
private theorem QVN_loopDerivN_eq {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx L W) (Idx L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    loopDerivN L W E u M X σ b =
      ∑ j : Fin k, -Matrix.trace (blockMat X * QVN_cut E u M σ b j) := by
  set l : List (Bool × Z2 L) := (List.ofFn σ).zip (List.ofFn b) with hl
  have hlen : l.length = k := by simp [hl]
  have hfun : (fun y : ℝ => gloop L W (blockMat (M + (y : ℂ) • X)) (spectralZ E u)
      (loopOf σ b)) = fun y : ℝ => Matrix.trace (QVN_wd E u (M + (y : ℂ) • X) l) := rfl
  have hD := QVN_hasDerivAt_trace (QVN_hasDerivAt_wd hE hu hM X l)
  rw [loopDerivN, hfun, hD.deriv, QVN_wordDeriv, Matrix.trace_sum, hlen, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QVN_trace_term E u M X l (by omega : (j : ℕ) < l.length)]
  simp [QVN_cut, hl]

/-- **The glued `(2k+2)`-loop of the cut `j` is `tr(A_j(a) E_{β'} A_j(a')ᴴ E_β)`** (the layout is
`eeLoop` of `RBM2D.Induction.HierVocab`). -/
private theorem QVN_eeLoop_gloop (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → Z2 L) (j : Fin k)
    (β β' : Z2 L) :
    LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (QVN_cut E u M σ a j * Eblk L W β' * (QVN_cut E u M σ a' j)ᴴ *
        Eblk L W β) := by
  have QVN_wd_nil (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
      QVN_wd E u M ([] : List (Bool × Z2 L)) =
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := rfl
  have hq : (j : ℕ) < (List.ofFn σ).length := by simp
  have hz := QVN_eeLoop_zip (L := L) (List.ofFn σ) (List.ofFn a) (List.ofFn a') (by simp)
    (by simp) hq β β'
  have hs : (List.ofFn σ)[(j : ℕ)] = σ j := by simp
  rw [hs] at hz
  have hL : LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (QVN_wd E u M ((eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').σ.zip (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').a)) := rfl
  rw [hL, hz, QVN_wd_append, QVN_wd_append, ← QVN_wd_rflip E u hM]
  simp only [QVN_cut, Matrix.conjTranspose_mul, QVN_greenBlk_conjTranspose E u hM,
    QVN_wd_cons, QVN_wd_nil, Matrix.mul_one, Matrix.mul_assoc]

end Deriv

/-! ## 4. The per-cut identity and the assembly -/

section Assembly

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Swapping the summation labels of an `S^{(B)}`-weighted double sum. -/
private theorem QVN_SB_swap (F : Z2 L → Z2 L → ℂ) :
    ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' * F b' b = ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' * F b b' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [show SB L b' b = SB L b b' from congrFun (congrFun (SB_transpose L) b) b']

/-- **The per-cut identity of `def:CALE`** (not written explicitly in the paper): for two block
matrices `A, A'`,
`Σ_c gvar_c ⟨X̂_c, A⟩ conj ⟨X̂_c, A'⟩ = W² Σ_{x,y} S^B_{xy} tr(A E_x A'ᴴ E_y)`, with
`⟨X̂, A⟩ = -tr(X̂ A)`. -/
private theorem QVN_cut_pair (A A' : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (-Matrix.trace (blockMat (coordinateMatrix L W c) * A) *
          (starRingEnd ℂ) (-Matrix.trace (blockMat (coordinateMatrix L W c) * A'))) =
      (W : ℂ) ^ 2 * ∑ x : Z2 L, ∑ y : Z2 L, SB L x y *
        Matrix.trace (A * Eblk L W x * A'ᴴ * Eblk L W y) := by
  simp only [QVN_trace_blockMat_mul, map_neg, neg_mul_neg]
  rw [QVN_coord_sum, QVN_svar_sum]

/-- `Σ_{k' ∈ [1,n]} F k' = Σ_{j : Fin n} F (j + 1)`. -/
private theorem QVN_sum_Icc_fin (n : ℕ) (F : ℕ → ℂ) :
    ∑ k' ∈ Finset.Icc 1 n, F k' = ∑ j : Fin n, F ((j : ℕ) + 1) := by
  rw [← Finset.sum_range (fun j => F (j + 1)), Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 n 1]
  rfl

/-- The `j`-th cut of `𝓔⊗𝓔`: `W² Σ_{x,y} S^B_{xy} tr(A_j(b) E_x A_j(b')ᴴ E_y)`. -/
private def QVN_Ecut (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (j : Fin k) (b b' : Fin k → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ x : Z2 L, ∑ y : Z2 L, SB L x y *
    Matrix.trace (QVN_cut E u M σ b j * Eblk L W x * (QVN_cut E u M σ b' j)ᴴ * Eblk L W y)

/-- **`𝓔⊗𝓔` is the sum of its `k` cuts.** -/
private theorem QVN_eeN_eq (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (b b' : Fin k → Z2 L) :
    eeN L W E u M σ b b' = ∑ j : Fin k, QVN_Ecut E u M σ j b b' := by
  rw [eeN, QVN_sum_Icc_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QVN_Ecut]
  congr 1
  simp only [QVN_eeLoop_gloop E u hM]
  exact QVN_SB_swap (fun x y => Matrix.trace (QVN_cut E u M σ b j * Eblk L W x *
    (QVN_cut E u M σ b' j)ᴴ * Eblk L W y))

/-- Cauchy–Schwarz over the `k` cuts: `‖Σ_j P_j‖² ≤ k Σ_j ‖P_j‖²`. -/
private theorem QVN_norm_sum_sq_le {k : ℕ} (P : Fin k → ℂ) :
    ‖∑ j, P j‖ ^ 2 ≤ (k : ℝ) * ∑ j, ‖P j‖ ^ 2 := by
  calc ‖∑ j, P j‖ ^ 2 ≤ (∑ j, ‖P j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) * ∑ j, ‖P j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (k : ℝ) * ∑ j, ‖P j‖ ^ 2 := by simp

/-- `‖x‖² = x · conj x`, as a complex identity. -/
private theorem QVN_mul_conj (x : ℂ) : x * (starRingEnd ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Assembly

/-! ## 5. The theorem -/

/-- **`qvPropagatedN`** (the statement `QVPropagatedN`, general `n = k ≥ 2`, every sign vector): the
variance proxy of a propagated increment.  Per cut `j` the coordinate sum is the glued loop
(`QVN_cut_pair`, `QVN_eeLoop_gloop`); Cauchy–Schwarz over the `k` cuts gives the factor `k`.  At
`k = 2`, `σ = (+,-)` this is `qvPropagated` (`RBM2D.Path.QVIdentity`). -/
theorem qvPropagatedN : QVPropagatedN := by
  intro L W _ _ E u hL hE hu0 hu M hM k hk σ κ
  -- the `j`-th cut of the propagated increment
  set P : Fin k → Coord L W → ℂ := fun j c =>
    ∑ b : Fin k → Z2 L, κ b *
      (-Matrix.trace (blockMat (coordinateMatrix L W c) * QVN_cut E u M σ b j)) with hP
  have hsplit : ∀ c : Coord L W,
      ∑ b : Fin k → Z2 L, κ b * loopDerivN L W E u M (coordinateMatrix L W c) σ b =
        ∑ j : Fin k, P j c := by
    intro c
    simp only [hP, QVN_loopDerivN_eq hE hu hM, Finset.mul_sum]
    exact Finset.sum_comm
  -- the per-cut variance identity
  have hcut : ∀ j : Fin k, ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (P j c * (starRingEnd ℂ) (P j c)) =
      ∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
        κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut E u M σ j b b' := by
    intro j
    have hPP : ∀ c : Coord L W, P j c * (starRingEnd ℂ) (P j c) =
        ∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L, κ b * (starRingEnd ℂ) (κ b') *
          (-Matrix.trace (blockMat (coordinateMatrix L W c) * QVN_cut E u M σ b j) *
            (starRingEnd ℂ) (-Matrix.trace (blockMat (coordinateMatrix L W c) *
              QVN_cut E u M σ b' j))) := by
      intro c
      simp only [hP, map_sum, map_mul, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [hPP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [QVN_Ecut, ← QVN_cut_pair (QVN_cut E u M σ b j) (QVN_cut E u M σ b' j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hre : ∀ j : Fin k, ∑ c : Coord L W, (gvar L W c : ℝ) * ‖P j c‖ ^ 2 =
      (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
        κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut E u M σ j b b').re := by
    intro j
    rw [← hcut j, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVN_mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [hsplit]
  calc ∑ c : Coord L W, (gvar L W c : ℝ) * ‖∑ j : Fin k, P j c‖ ^ 2
      ≤ ∑ c : Coord L W, (gvar L W c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_left (QVN_norm_sum_sq_le _) (gvar L W c).2
    _ = (k : ℝ) * ∑ j : Fin k, ∑ c : Coord L W, (gvar L W c : ℝ) * ‖P j c‖ ^ 2 := by
        have h1 : ∀ c : Coord L W, (gvar L W c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) =
            (k : ℝ) * ∑ j : Fin k, (gvar L W c : ℝ) * ‖P j c‖ ^ 2 := by
          intro c
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl fun c _ => h1 c, ← Finset.mul_sum, Finset.sum_comm]
    _ = (k : ℝ) * ∑ j : Fin k, (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
          κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut E u M σ j b b').re := by
        simp only [hre]
    _ = (k : ℝ) * (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
          κ b * (starRingEnd ℂ) (κ b') * eeN L W E u M σ b b').re := by
        congr 1
        rw [← Complex.re_sum]
        congr 1
        simp only [QVN_eeN_eq E u hM, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]

end RBM.Ind

end
