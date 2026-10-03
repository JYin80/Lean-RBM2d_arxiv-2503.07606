/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Vocab
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.GreenDerivative
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Hierarchy.WardResolvent

/-!
# The quadratic-variation identities of Step 2

Three statements and their proofs:
* `EECutIdentity` / `eeCutIdentity`: the per-cut `(𝓔⊗𝓔)` identity.  Per coordinate `c`, the two
  cut derivatives `cutDeriv1`, `cutDeriv2` pair through `gvar` into
  `Σ_{k,l} svar_{kl} (·)_{lk} conj (·)_{lk}`; `svar_cast_eq_Spaper` turns this into
  `W² Σ_{b,b'} S^{(B)}_{bb'} tr(A E_b Bᴴ E_{b'})`, which is one six-loop of `EE` for each cut.
* `QVPropagated` / `qvPropagated`: `loopDeriv = cutDeriv1 + cutDeriv2` (resolvent derivative),
  `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`, then `eeCutIdentity`.
* `EEShift` / `eeShift`: telescoping of the six-loop words with `G(z₁) - G(z₂) = (z₁ - z₂) G G`,
  `‖G‖ ≤ η_{u+Δ}⁻¹`, `‖E_b‖ ≤ W⁻²`, the trace bound by `N = (WL)²`, and the unit row sums of
  `S^{(B)}`.  The bound obtained is `12 L² W⁻¹⁰ N η⁻⁷ Δ ≤ 16 N² η⁻⁷ Δ`.

The telescoping lemma bounds the difference of two products of Green functions and block
insertions, with separate bounds for `G` and `E_b`.

Paper: arXiv:2503.07606, `defEOTE`, `def_diffakn_k`, `alu9_STime`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

section CoordAlgebra

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem QVIdentity_cm_lt {i j : Idx L W} (h : idxKey L W i < idxKey L W j) (b : Bool) :
    coordinateMatrix L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind


private theorem QVIdentity_cm_diag_true (i : Idx L W) :
    coordinateMatrix L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVIdentity_cm_diag_false (i : Idx L W) :
    coordinateMatrix L W (i, i, false) = 0 := by
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVIdentity_cm_gt {i j : Idx L W} (h : idxKey L W j < idxKey L W i) (b : Bool) :
    coordinateMatrix L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [coordinateMatrix_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The pairing `Σ_{k,l} X_{kl} f_{lk}` (the trace `tr(X F)` with `F_{lk} = f l k`). -/
private def QVIdentity_pair (X : Matrix (Idx L W) (Idx L W) ℂ) (f : Idx L W → Idx L W → ℂ) : ℂ :=
  ∑ k, ∑ l, X k l * f l k

private theorem QVIdentity_pair_single (i j : Idx L W) (x : ℂ) (f : Idx L W → Idx L W → ℂ) :
    QVIdentity_pair (Matrix.single i j x) f = x * f j i := by
  simp only [QVIdentity_pair, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem QVIdentity_pair_add (X Y : Matrix (Idx L W) (Idx L W) ℂ)
    (f : Idx L W → Idx L W → ℂ) :
    QVIdentity_pair (X + Y) f = QVIdentity_pair X f + QVIdentity_pair Y f := by
  simp only [QVIdentity_pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem QVIdentity_pair_zero (f : Idx L W → Idx L W → ℂ) :
    QVIdentity_pair (0 : Matrix (Idx L W) (Idx L W) ℂ) f = 0 := by
  simp [QVIdentity_pair]

/-- Sum of an ordered-pair function over the three cases of `idxKey`. -/
private theorem QVIdentity_sum_tri (T : Idx L W → Idx L W → ℂ) :
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
private theorem QVIdentity_coord_sum (f g : Idx L W → Idx L W → ℂ) :
    ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (QVIdentity_pair (coordinateMatrix L W c) f *
          (starRingEnd ℂ) (QVIdentity_pair (coordinateMatrix L W c) g)) =
      ∑ k, ∑ l, (svar L W k l : ℂ) * (f l k * (starRingEnd ℂ) (g l k)) := by
  have hc : ∀ F : Coord L W → ℂ,
      ∑ c : Coord L W, F c = ∑ i : Idx L W, ∑ j : Idx L W, (F (i, j, true) + F (i, j, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Fintype.sum_bool _
  rw [← QVIdentity_sum_tri, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_left h, QVIdentity_cm_lt h, QVIdentity_cm_lt h, gvar_offDiag L W i j true hij,
      gvar_offDiag L W i j false hij, svar_comm L W j i]
    simp only [QVIdentity_pair_add, QVIdentity_pair_single, ite_true, Bool.false_eq_true,
      ite_false, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, QVIdentity_cm_diag_true,
      QVIdentity_cm_diag_false,
      gvar_diag, gvar_diag]
    simp [QVIdentity_pair_single, QVIdentity_pair_zero]
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right hij, QVIdentity_cm_gt h, QVIdentity_cm_gt h]
    simp [QVIdentity_pair_zero]

/-- `tr(blockMat X · A) = Σ_{k,l} X_{kl} A_{e l, e k}` with `e = splitEquiv`. -/
private theorem QVIdentity_trace_blockMat_mul (X : Matrix (Idx L W) (Idx L W) ℂ)
    (A : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (blockMat X * A) =
      QVIdentity_pair X (fun l k => A (splitEquiv L W l) (splitEquiv L W k)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, blockMat, Matrix.submatrix_apply,
    QVIdentity_pair]
  rw [← (splitEquiv L W).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (splitEquiv L W).sum_comp]
  simp

/-- Reordering four finite sums. -/
private theorem QVIdentity_sum_swap4 {α β : Type*} [Fintype α] [Fintype β]
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
private theorem QVIdentity_svar_sum (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
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
  rw [QVIdentity_sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hcollapse]
  field_simp

end CoordAlgebra

section Cuts

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem QVIdentity_loop6_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 6 → Bool) (x : Fin 6 → Z2 L) :
    loop6 L W E u M σ x = Matrix.trace (greenBlk L W E u M (σ 0) * Eblk L W (x 0) *
      greenBlk L W E u M (σ 1) * Eblk L W (x 1) * greenBlk L W E u M (σ 2) * Eblk L W (x 2) *
      greenBlk L W E u M (σ 3) * Eblk L W (x 3) * greenBlk L W E u M (σ 4) * Eblk L W (x 4) *
      greenBlk L W E u M (σ 5) * Eblk L W (x 5)) := by
  simp only [loop6, gloop, gloopProd, loopOf, List.ofFn_succ, List.ofFn_zero, List.zip_cons_cons,
    List.zip_nil_left, List.foldr_cons, List.foldr_nil, Matrix.mul_one, greenBlk, Matrix.mul_assoc]
  rfl

/-- The edge-1 derivative as a pairing: `∂^{(1)}_X 𝓛_a = -tr(X̂ · G₊E_{a₁}G₋E_{a₂}G₊)`. -/
private theorem QVIdentity_cut1_eq (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    (a : Z2 L × Z2 L) :
    cutDeriv1 L W E u M X a = -Matrix.trace (blockMat X * (greenBlk L W E u M true *
      Eblk L W a.1 * greenBlk L W E u M false * Eblk L W a.2 * greenBlk L W E u M true)) := by
  rw [cutDeriv1]
  congr 1
  calc Matrix.trace (greenBlk L W E u M true * blockMat X * greenBlk L W E u M true *
          Eblk L W a.1 * greenBlk L W E u M false * Eblk L W a.2)
      = Matrix.trace (greenBlk L W E u M true * (blockMat X * greenBlk L W E u M true *
          Eblk L W a.1 * greenBlk L W E u M false * Eblk L W a.2)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((blockMat X * greenBlk L W E u M true *
          Eblk L W a.1 * greenBlk L W E u M false * Eblk L W a.2) * greenBlk L W E u M true) :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The edge-2 derivative as a pairing: `∂^{(2)}_X 𝓛_a = -tr(X̂ · G₋E_{a₂}G₊E_{a₁}G₋)`. -/
private theorem QVIdentity_cut2_eq (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    (a : Z2 L × Z2 L) :
    cutDeriv2 L W E u M X a = -Matrix.trace (blockMat X * (greenBlk L W E u M false *
      Eblk L W a.2 * greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false)) := by
  rw [cutDeriv2]
  congr 1
  calc Matrix.trace (greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false *
          blockMat X * greenBlk L W E u M false * Eblk L W a.2)
      = Matrix.trace ((greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false) *
          (blockMat X * greenBlk L W E u M false * Eblk L W a.2)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((blockMat X * greenBlk L W E u M false * Eblk L W a.2) *
          (greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false)) :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- A coordinate sum of a cut pairing, in block form. -/
private theorem QVIdentity_cut_pair
    (A : Z2 L × Z2 L → Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (f : Matrix (Idx L W) (Idx L W) ℂ → Z2 L × Z2 L → ℂ)
    (hf : ∀ X a, f X a = -Matrix.trace (blockMat X * A a)) (a a' : Z2 L × Z2 L) :
    ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (f (coordinateMatrix L W c) a * (starRingEnd ℂ) (f (coordinateMatrix L W c) a')) =
      (W : ℂ) ^ 2 * ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        Matrix.trace (A a * Eblk L W b * (A a')ᴴ * Eblk L W b') := by
  simp only [hf, QVIdentity_trace_blockMat_mul, map_neg, neg_mul_neg]
  rw [QVIdentity_coord_sum, QVIdentity_svar_sum]

private theorem QVIdentity_greenBlk_conjTranspose (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (σ : Bool) :
    (greenBlk L W E u M σ)ᴴ = greenBlk L W E u M (!σ) :=
  Gsig_conjTranspose (hM.submatrix _) _ σ

/-- Swapping the summation labels of an `S^{(B)}`-weighted double sum. -/
private theorem QVIdentity_SB_swap (F : Z2 L → Z2 L → ℂ) :
    ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' * F b' b = ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' * F b b' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [show SB L b' b = SB L b b' from congrFun (congrFun (SB_transpose L) b) b']


end Cuts

/-! ## The statements -/

/-- **The per-cut identity**: `(𝓔⊗𝓔)_{a,a'}` is the sum over the two edges `k` of
`Σ_α S_α ∂^{(k)}_α 𝓛_a · conj(∂^{(k)}_α 𝓛_{a'})` (diagonal cuts only).  The identity without
the cut split, `Σ_α S_α ∂_α𝓛 conj ∂_α𝓛 = (𝓔⊗𝓔)`, is false. -/
def EECutIdentity : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ a a' : Z2 L × Z2 L,
      EE L W E u M a a' = ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (cutDeriv1 L W E u M (coordinateMatrix L W c) a *
            (starRingEnd ℂ) (cutDeriv1 L W E u M (coordinateMatrix L W c) a') +
          cutDeriv2 L W E u M (coordinateMatrix L W c) a *
            (starRingEnd ℂ) (cutDeriv2 L W E u M (coordinateMatrix L W c) a'))

/-- **QV of a propagated increment**: for any coefficients `κ` (the kernel of
`𝒰_{u_{j+1},v}` at the target `a`), `Σ_c gvar_c |Σ_b κ_b ∂_c 𝓛_b|² ≤ 2 Re Σ_{b,b'} κ_b κ̄_{b'}
(𝓔⊗𝓔)_{b,b'}` (Cauchy–Schwarz over the two cuts; the factor `2 = n`). -/
def QVPropagated : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ κ : Z2 L × Z2 L → ℂ,
      ∑ c : Coord L W, (gvar L W c : ℝ) *
          ‖∑ b : Z2 L × Z2 L, κ b * loopDeriv L W E u M (coordinateMatrix L W c) b‖ ^ 2 ≤
        2 * (∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          κ b * (starRingEnd ℂ) (κ b') * EE L W E u M b b').re

/-- **One-step time shift of `𝓔⊗𝓔`**: `‖(𝓔⊗𝓔)_{u+Δ}(M) - (𝓔⊗𝓔)_u(M)‖ ≤
16 N² η_{u+Δ}^{-7} Δ` for Hermitian `M`. -/
def EEShift : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u Δ : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → 0 ≤ Δ →
    u + Δ < 1 → ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ a a' : Z2 L × Z2 L,
      ‖EE L W E (u + Δ) M a a' - EE L W E u M a a'‖ ≤
        16 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (etaT E (u + Δ))⁻¹ ^ 7 * Δ

/-! ## `EECutIdentity` -/

/-- **`eeCutIdentity`**: the per-cut `(𝓔⊗𝓔)` identity.
Each cut pairs through `svar_cast_eq_Spaper` into one of the two six-loops of `EE`. -/
theorem eeCutIdentity : EECutIdentity := by
  intro L W _ _ E u _ _ _ _ M hM a a'
  have hG := QVIdentity_greenBlk_conjTranspose (L := L) (W := W) E u hM
  have hE := Eblk_conjTranspose L W
  have h1 : ∀ x y : Z2 L,
      loop6 L W E u M ![true, false, true, false, true, false] ![a.1, a.2, x, a'.2, a'.1, y] =
        Matrix.trace ((greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false *
          Eblk L W a.2 * greenBlk L W E u M true) * Eblk L W x *
          (greenBlk L W E u M true * Eblk L W a'.1 * greenBlk L W E u M false *
            Eblk L W a'.2 * greenBlk L W E u M true)ᴴ * Eblk L W y) := by
    intro x y
    rw [QVIdentity_loop6_eq]
    simp [Matrix.conjTranspose_mul, hG, hE, Matrix.mul_assoc]
  have h2 : ∀ x y : Z2 L,
      loop6 L W E u M ![false, true, false, true, false, true] ![a.2, a.1, x, a'.1, a'.2, y] =
        Matrix.trace ((greenBlk L W E u M false * Eblk L W a.2 * greenBlk L W E u M true *
          Eblk L W a.1 * greenBlk L W E u M false) * Eblk L W x *
          (greenBlk L W E u M false * Eblk L W a'.2 * greenBlk L W E u M true *
            Eblk L W a'.1 * greenBlk L W E u M false)ᴴ * Eblk L W y) := by
    intro x y
    rw [QVIdentity_loop6_eq]
    simp [Matrix.conjTranspose_mul, hG, hE, Matrix.mul_assoc]
  rw [EE]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [QVIdentity_cut_pair _ _ (QVIdentity_cut1_eq E u M) a a',
    QVIdentity_cut_pair _ _ (QVIdentity_cut2_eq E u M) a a']
  simp only [h1, h2]
  exact congrArg₂ (· + ·) (congrArg ((W : ℂ) ^ 2 * ·) (QVIdentity_SB_swap _))
    (congrArg ((W : ℂ) ^ 2 * ·) (QVIdentity_SB_swap _))

/-! ## `QVPropagated` -/

section Deriv

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

set_option linter.unusedDecidableInType false in
/-- The trace of a differentiable matrix path (the `DecidableEq` instance is used by the
`L2Operator` norm). -/
private theorem QVIdentity_hasDerivAt_trace {n : Type*} [Fintype n] [DecidableEq n]
    {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- **`loopDeriv = cutDeriv1 + cutDeriv2`** along any direction `X`, at a Hermitian `M`, for
`|E| < 2` and `u < 1` (so `Im z_u ≠ 0`). -/
private theorem QVIdentity_loopDeriv_eq {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (X : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L × Z2 L) :
    loopDeriv L W E u M X a = cutDeriv1 L W E u M X a + cutDeriv2 L W E u M X a := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  set Hy : ℝ → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
    fun y => blockMat M + (y : ℂ) • blockMat X with hHy
  have hH0 : Hy 0 = blockMat M := by simp [hHy]
  have hline : HasDerivAt Hy (blockMat X) 0 := hasDerivAt_line _ _ 0
  have hG : ∀ σ : Bool, HasDerivAt (fun y => Gsig (Hy y) (spectralZ E u) σ)
      (-(greenBlk L W E u M σ * blockMat X * greenBlk L W E u M σ)) 0 := by
    intro σ
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
  have hfun : (fun y : ℝ => loopPM L W E u (M + (y : ℂ) • X) a.1 a.2) =
      fun y => Matrix.trace (Gsig (Hy y) (spectralZ E u) true * Eblk L W a.1 *
        (Gsig (Hy y) (spectralZ E u) false * Eblk L W a.2)) := by
    funext y
    simp only [loopPM, gloop, gloopProd, pmLoop, List.zip_cons_cons, List.zip_nil_left,
      List.foldr_cons, List.foldr_nil, Matrix.mul_one, hHy]
    rfl
  have hD : HasDerivAt (fun y => Matrix.trace (Gsig (Hy y) (spectralZ E u) true * Eblk L W a.1 *
        (Gsig (Hy y) (spectralZ E u) false * Eblk L W a.2)))
      (Matrix.trace (-(greenBlk L W E u M true * blockMat X * greenBlk L W E u M true) *
          Eblk L W a.1 * (Gsig (Hy 0) (spectralZ E u) false * Eblk L W a.2) +
        Gsig (Hy 0) (spectralZ E u) true * Eblk L W a.1 *
          (-(greenBlk L W E u M false * blockMat X * greenBlk L W E u M false) *
            Eblk L W a.2))) 0 :=
    QVIdentity_hasDerivAt_trace
      (((hG true).mul_const (Eblk L W a.1)).mul ((hG false).mul_const (Eblk L W a.2)))
  rw [loopDeriv, hfun, hD.deriv, cutDeriv1, cutDeriv2, hH0]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg,
    Matrix.mul_assoc, greenBlk]

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
private theorem QVIdentity_norm_add_sq_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- `‖x‖² = Re(x · conj x)`, as a complex identity. -/
private theorem QVIdentity_mul_conj (x : ℂ) : x * (starRingEnd ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **`qvPropagated`**: Cauchy–Schwarz over the two cuts (factor `2 = n`), then
`eeCutIdentity`. -/
theorem qvPropagated : QVPropagated := by
  intro L W _ _ E u hL hE hu0 hu M hM κ
  set P : Coord L W → ℂ := fun c =>
    ∑ b : Z2 L × Z2 L, κ b * cutDeriv1 L W E u M (coordinateMatrix L W c) b with hP
  set Q : Coord L W → ℂ := fun c =>
    ∑ b : Z2 L × Z2 L, κ b * cutDeriv2 L W E u M (coordinateMatrix L W c) b with hQ
  have hsplit : ∀ c, ∑ b : Z2 L × Z2 L, κ b * loopDeriv L W E u M (coordinateMatrix L W c) b =
      P c + Q c := by
    intro c
    simp only [hP, hQ, QVIdentity_loopDeriv_eq hE hu hM, mul_add, Finset.sum_add_distrib]
  -- the complex identity
  have hkey : ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        (P c * (starRingEnd ℂ) (P c) + Q c * (starRingEnd ℂ) (Q c)) =
      ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L, κ b * (starRingEnd ℂ) (κ b') * EE L W E u M b b' := by
    have hPP : ∀ c, P c * (starRingEnd ℂ) (P c) + Q c * (starRingEnd ℂ) (Q c) =
        ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L, κ b * (starRingEnd ℂ) (κ b') *
          (cutDeriv1 L W E u M (coordinateMatrix L W c) b *
              (starRingEnd ℂ) (cutDeriv1 L W E u M (coordinateMatrix L W c) b') +
            cutDeriv2 L W E u M (coordinateMatrix L W c) b *
              (starRingEnd ℂ) (cutDeriv2 L W E u M (coordinateMatrix L W c) b')) := by
      intro c
      simp only [hP, hQ, map_sum, map_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [hPP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [eeCutIdentity L W E u hL hE hu0 hu M hM b b', Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hre : ∑ c : Coord L W, (gvar L W c : ℝ) * (‖P c‖ ^ 2 + ‖Q c‖ ^ 2) =
      (∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
        κ b * (starRingEnd ℂ) (κ b') * EE L W E u M b b').re := by
    rw [← hkey, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVIdentity_mul_conj, QVIdentity_mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  simp only [hsplit]
  rw [← hre, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hg : (0 : ℝ) ≤ (gvar L W c : ℝ) := (gvar L W c).2
  have := QVIdentity_norm_add_sq_le (P c) (Q c)
  nlinarith

end Deriv


/-! ## `EEShift` -/

section Shift

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Product bound for a signed Green / block-insertion word (with separate bounds `K` for `G` and
`w` for `E_b`). -/
private theorem QVIdentity_norm_foldr_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    {z : ℂ} {K w : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w) (hG : ∀ σ, ‖Gsig H z σ‖ ≤ K)
    (hE : ∀ b, ‖Eblk L W b‖ ≤ w) (l : List (Bool × Z2 L)) :
    ‖l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)‖ ≤ (K * w) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ']
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      exact mul_le_mul (mul_le_mul (hG p.1) (hE p.2) (norm_nonneg _) hK) ih (norm_nonneg _)
        (mul_nonneg hK hw)

/-- Telescoping bound for two signed Green / block-insertion words. -/
private theorem QVIdentity_norm_foldr_sub_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    {z₁ z₂ : ℂ} {K w δ : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w) (hδ : 0 ≤ δ)
    (hG₁ : ∀ σ, ‖Gsig H z₁ σ‖ ≤ K) (hG₂ : ∀ σ, ‖Gsig H z₂ σ‖ ≤ K)
    (hE : ∀ b, ‖Eblk L W b‖ ≤ w) (hsub : ∀ σ, ‖Gsig H z₁ σ - Gsig H z₂ σ‖ ≤ δ)
    (l : List (Bool × Z2 L)) :
    ‖l.foldr (fun p M => Gsig H z₁ p.1 * Eblk L W p.2 * M)
          (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) -
        l.foldr (fun p M => Gsig H z₂ p.1 * Eblk L W p.2 * M) 1‖ ≤
      (l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1) := by
  induction l with
  | nil => simp
  | cons p l ih =>
      set P₁ := l.foldr (fun p M => Gsig H z₁ p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      set P₂ := l.foldr (fun p M => Gsig H z₂ p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      have hP₁ : ‖P₁‖ ≤ (K * w) ^ l.length := QVIdentity_norm_foldr_le hK hw hG₁ hE l
      have hsplit : Gsig H z₁ p.1 * Eblk L W p.2 * P₁ - Gsig H z₂ p.1 * Eblk L W p.2 * P₂ =
          (Gsig H z₁ p.1 - Gsig H z₂ p.1) * Eblk L W p.2 * P₁ +
            Gsig H z₂ p.1 * Eblk L W p.2 * (P₁ - P₂) := by noncomm_ring
      simp only [List.foldr_cons, List.length_cons]
      rw [hsplit]
      have hA : ‖(Gsig H z₁ p.1 - Gsig H z₂ p.1) * Eblk L W p.2 * P₁‖ ≤
          δ * w * (K * w) ^ l.length := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hsub p.1) (hE p.2) (norm_nonneg _) hδ) hP₁ (norm_nonneg _)
          (mul_nonneg hδ hw)
      have hB : ‖Gsig H z₂ p.1 * Eblk L W p.2 * (P₁ - P₂)‖ ≤
          K * w * ((l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1)) := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hG₂ p.1) (hE p.2) (norm_nonneg _) hK) ih (norm_nonneg _)
          (mul_nonneg hK hw)
      have hC : K * w * ((l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1)) =
          (l.length : ℝ) * δ * w * (K * w) ^ l.length := by
        rcases Nat.eq_zero_or_pos l.length with h0 | hpos
        · rw [h0]; simp
        · obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 := ⟨l.length - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel, pow_succ]
          push_cast
          ring
      refine (norm_add_le _ _).trans ?_
      rw [Nat.add_sub_cancel]
      push_cast
      nlinarith [hA, hB, hC]

/-- The `S^{(B)}` rows have total norm `1`. -/
private theorem QVIdentity_sum_norm_SB (hL : 3 ≤ L) (b : Z2 L) :
    ∑ b' : Z2 L, ‖SB L b b'‖ = 1 := by
  have h : ∀ b' : Z2 L, ‖SB L b b'‖ = (SB L b b').re := by
    intro b'
    rw [SB_apply, sbKernel]
    split_ifs
    · rw [norm_inv, Complex.norm_ofNat]
      simp
    · simp
  simp only [h]
  rw [← Complex.re_sum, sum_SB_row L hL b, Complex.one_re]

/-- The spectral parameter moves by `Δ` in norm: `‖z_{u+Δ} - z_u‖ = Δ` (`|m| = 1`). -/
private theorem QVIdentity_norm_spectralZ_sub {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) :
    ‖spectralZ E (u + Δ) - spectralZ E u‖ = Δ := by
  have h : spectralZ E (u + Δ) - spectralZ E u = (-(Δ : ℂ)) * spectralM E := by
    simp only [spectralZ]; push_cast; ring
  rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ,
    norm_spectralM hE.le, mul_one]

omit [NeZero W] in
/-- Resolvent bounds at the two times `u ≤ u + Δ`, with `η = η_{u+Δ}`. -/
private theorem QVIdentity_Gsig_shift {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ)
    (huΔ : u + Δ < 1) {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) :
    (∀ σ, ‖Gsig H (spectralZ E u) σ‖ ≤ (etaT E (u + Δ))⁻¹) ∧
      (∀ σ, ‖Gsig H (spectralZ E (u + Δ)) σ‖ ≤ (etaT E (u + Δ))⁻¹) ∧
      (∀ σ, ‖Gsig H (spectralZ E (u + Δ)) σ - Gsig H (spectralZ E u) σ‖ ≤
        Δ * (etaT E (u + Δ))⁻¹ ^ 2) := by
  have hm := spectralM_im_pos hE
  have hη : 0 < etaT E (u + Δ) := etaT_pos hE huΔ
  have him1 : etaT E (u + Δ) ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, etaT]
    refine le_trans ?_ (le_abs_self _)
    nlinarith
  have him2 : etaT E (u + Δ) ≤ |(spectralZ E (u + Δ)).im| := by
    rw [spectralZ_im, etaT]
    exact le_abs_self _
  have hG1 : ∀ σ, ‖Gsig H (spectralZ E u) σ‖ ≤ (etaT E (u + Δ))⁻¹ :=
    norm_Gsig_le_inv_eta L W hH hη him1
  have hG2 : ∀ σ, ‖Gsig H (spectralZ E (u + Δ)) σ‖ ≤ (etaT E (u + Δ))⁻¹ :=
    norm_Gsig_le_inv_eta L W hH hη him2
  refine ⟨hG1, hG2, fun σ => ?_⟩
  have hne1 : (spectralZ E u).im ≠ 0 := fun h => by
    rw [h, abs_zero] at him1; linarith
  have hne2 : (spectralZ E (u + Δ)).im ≠ 0 := fun h => by
    rw [h, abs_zero] at him2; linarith
  set w₁ : ℂ := if σ then spectralZ E (u + Δ) else (starRingEnd ℂ) (spectralZ E (u + Δ)) with hw₁
  set w₂ : ℂ := if σ then spectralZ E u else (starRingEnd ℂ) (spectralZ E u) with hw₂
  have hU1 : IsUnit (H - w₁ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    refine RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH ?_
    cases σ <;> simpa [hw₁] using hne2
  have hU2 : IsUnit (H - w₂ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) := by
    refine RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH ?_
    cases σ <;> simpa [hw₂] using hne1
  have hw : ‖w₁ - w₂‖ = Δ := by
    cases σ
    · simp only [hw₁, hw₂, Bool.false_eq_true, ite_false]
      rw [← map_sub, Complex.norm_conj, QVIdentity_norm_spectralZ_sub hE hΔ]
    · simp only [hw₁, hw₂, ite_true]
      exact QVIdentity_norm_spectralZ_sub hE hΔ
  have heq : Gsig H (spectralZ E (u + Δ)) σ - Gsig H (spectralZ E u) σ =
      (w₁ - w₂) • (Gsig H (spectralZ E (u + Δ)) σ * Gsig H (spectralZ E u) σ) := by
    have := green_sub_green hU1 hU2
    simpa only [Gsig, hw₁, hw₂] using this
  rw [heq]
  refine (norm_smul_le _ _).trans ?_
  rw [hw]
  calc Δ * ‖Gsig H (spectralZ E (u + Δ)) σ * Gsig H (spectralZ E u) σ‖
      ≤ Δ * ((etaT E (u + Δ))⁻¹ * (etaT E (u + Δ))⁻¹) :=
        mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul (hG2 σ) (hG1 σ) (norm_nonneg _) (inv_nonneg.mpr hη.le))) hΔ
    _ = Δ * (etaT E (u + Δ))⁻¹ ^ 2 := by ring

/-- One six-loop moves by at most `N · 6 Δ η⁻² W⁻² (η⁻¹ W⁻²)⁵` between `u` and `u + Δ`. -/
private theorem QVIdentity_loop6_shift {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ)
    (huΔ : u + Δ < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin 6 → Bool) (x : Fin 6 → Z2 L) :
    ‖loop6 L W E (u + Δ) M σ x - loop6 L W E u M σ x‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) * (6 * (Δ * (etaT E (u + Δ))⁻¹ ^ 2) *
        (W : ℝ)⁻¹ ^ 2 * ((etaT E (u + Δ))⁻¹ * (W : ℝ)⁻¹ ^ 2) ^ 5) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hη : 0 < etaT E (u + Δ) := etaT_pos hE huΔ
  obtain ⟨hG1, hG2, hsub⟩ := QVIdentity_Gsig_shift (L := L) (W := W) hE hΔ huΔ hH
  have hlen : ((loopOf σ x).σ.zip (loopOf σ x).a).length = 6 := by simp [loopOf]
  have h := QVIdentity_norm_foldr_sub_le (inv_nonneg.mpr hη.le) (by positivity)
    (mul_nonneg hΔ (by positivity)) hG2 hG1 (norm_Eblk_le_inv_W_sq L W) hsub
    ((loopOf σ x).σ.zip (loopOf σ x).a)
  rw [hlen] at h
  rw [loop6, loop6, gloop, gloop, ← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine h.trans_eq ?_
  norm_num

/-- **`eeShift`**: the one-step time shift of `(𝓔⊗𝓔)`, `‖ΔEE‖ ≤ 16 N² η_{u+Δ}^{-7} Δ`. -/
theorem eeShift : EEShift := by
  intro L W _ _ E u Δ hL hE hu0 hΔ huΔ M hM a a'
  set η := etaT E (u + Δ) with hηdef
  have hη : 0 < η := etaT_pos hE huΔ
  set N : ℝ := (Fintype.card (BlockIndex L W) : ℝ) with hNdef
  set w : ℝ := (W : ℝ)⁻¹ ^ 2 with hwdef
  set B : ℝ := N * (6 * (Δ * η⁻¹ ^ 2) * w * (η⁻¹ * w) ^ 5) with hBdef
  have hloop : ∀ σ x, ‖loop6 L W E (u + Δ) M σ x - loop6 L W E u M σ x‖ ≤ B :=
    fun σ x => QVIdentity_loop6_shift hE hΔ huΔ hM σ x
  have hB0 : 0 ≤ B := by positivity
  have hdiff : EE L W E (u + Δ) M a a' - EE L W E u M a a' =
      (W : ℂ) ^ 2 * ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        ((loop6 L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b])) := by
    rw [EE, EE, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have hsum : ‖∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        ((loop6 L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b]))‖ ≤ (L : ℝ) ^ 2 * (2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    have hrow : ∀ b : Z2 L, ‖∑ b' : Z2 L, SB L b b' *
        ((loop6 L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b]))‖ ≤ 2 * B := by
      intro b
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b' : Z2 L, ‖SB L b b' *
          ((loop6 L W E (u + Δ) M ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b] -
            loop6 L W E u M ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b]) +
           (loop6 L W E (u + Δ) M ![false, true, false, true, false, true]
              ![a.2, a.1, b', a'.1, a'.2, b] -
            loop6 L W E u M ![false, true, false, true, false, true]
              ![a.2, a.1, b', a'.1, a'.2, b]))‖
          ≤ ∑ b' : Z2 L, ‖SB L b b'‖ * (2 * B) := by
            refine Finset.sum_le_sum fun b' _ => ?_
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (norm_add_le _ _).trans ?_
            linarith [hloop ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b],
              hloop ![false, true, false, true, false, true] ![a.2, a.1, b', a'.1, a'.2, b]]
        _ = 2 * B := by rw [← Finset.sum_mul, QVIdentity_sum_norm_SB hL b, one_mul]
    calc ∑ b : Z2 L, _ ≤ ∑ _b : Z2 L, 2 * B := Finset.sum_le_sum fun b _ => hrow b
      _ = (L : ℝ) ^ 2 * (2 * B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [Z2, ZMod.card, sq]
  -- the final arithmetic
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hwdef]
    exact pow_le_one₀ (inv_nonneg.mpr hW0.le) (inv_le_one_of_one_le₀ hW1)
  have hWw : (W : ℝ) ^ 2 * w = 1 := by
    rw [hwdef, inv_pow, mul_inv_cancel₀ (by positivity)]
  have hNval : N = (((W * L) ^ 2 : ℕ) : ℝ) := by
    rw [hNdef, card_BlockIndex]
    push_cast
    ring
  have hLN : (L : ℝ) ^ 2 ≤ N := by
    rw [hNval]
    push_cast
    nlinarith [sq_nonneg (L : ℝ), mul_pow (W : ℝ) (L : ℝ) 2]
  have hN0 : 0 ≤ N := by positivity
  have hι : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hw5 : w ^ 5 ≤ 1 := pow_le_one₀ hw0 hw1
  rw [hdiff, norm_mul, norm_pow, Complex.norm_natCast, ← hNval]
  calc (W : ℝ) ^ 2 * ‖_‖ ≤ (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * B)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 12 * ((W : ℝ) ^ 2 * w) * (L : ℝ) ^ 2 * N * w ^ 5 * η⁻¹ ^ 7 * Δ := by
        rw [hBdef]; ring
    _ = 12 * (L : ℝ) ^ 2 * N * w ^ 5 * η⁻¹ ^ 7 * Δ := by rw [hWw]; ring
    _ ≤ 12 * N * N * 1 * η⁻¹ ^ 7 * Δ := by
        have h7 : 0 ≤ η⁻¹ ^ 7 * Δ := mul_nonneg (pow_nonneg hι 7) hΔ
        have h1 : (L : ℝ) ^ 2 * N * w ^ 5 ≤ N * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hLN hN0) hw5 (pow_nonneg hw0 5)
            (mul_nonneg hN0 hN0)
        nlinarith
    _ ≤ 16 * N ^ 2 * η⁻¹ ^ 7 * Δ := by
        have h7 : 0 ≤ N ^ 2 * η⁻¹ ^ 7 * Δ := by positivity
        nlinarith

end Shift

end RBM.Path
