/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Model
import RBM2D.Delocalization

/-!
# Deterministic resolvent loops in two dimensions

This is the deterministic front of `Def:G_loop`. A loop label has a list of
resolvent signs and a list of block labels in `Z_L²`. The physical matrix index
has `W²` sites per block, so each insertion is the existing `Eblk L W a`
with weight `W⁻²`.

The lists need equal lengths to represent an `n`-loop. This is recorded by
`LoopIdx.WF`; the underlying `List.zip` truncates malformed pairs, so claims
about the intended loop use matching lists.
-/

namespace RBM

open Matrix Finset

/-- Signs (`true` for `+`) and block labels for a resolvent loop. -/
@[ext]
structure LoopIdx (α : Type*) where
  σ : List Bool
  a : List α
  deriving DecidableEq

namespace LoopIdx

/-- Equal numbers of signs and block labels. -/
def WF {α : Type*} (I : LoopIdx α) : Prop := I.σ.length = I.a.length

/-- The number of resolvent edges in a well-formed loop. -/
def length {α : Type*} (I : LoopIdx α) : ℕ := I.a.length

end LoopIdx

section Gsig

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Green function with a `+` or `−` spectral sign. -/
noncomputable def Gsig (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  green H (if σ then z else (starRingEnd ℂ) z)

@[simp] theorem Gsig_true (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z true = green H z := rfl

@[simp] theorem Gsig_false (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z false = green H ((starRingEnd ℂ) z) := rfl

omit [Fintype n] in
private theorem conjTranspose_sub_smul {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) :
    (H - z • (1 : Matrix n n ℂ))ᴴ =
      H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ) := by
  rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  rfl

/-- The two Green functions of a Hermitian matrix are adjoints:
`G(σ)ᴴ = G(!σ)`. The identity is algebraic and also holds at real `z`,
where the nonsingular inverse convention is used. -/
theorem Gsig_conjTranspose {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gsig H z σ)ᴴ = Gsig H z (!σ) := by
  cases σ
  · change (green H ((starRingEnd ℂ) z))ᴴ = green H z
    rw [green, green, conjTranspose_nonsing_inv,
      conjTranspose_sub_smul hH, Complex.conj_conj]
  · change (green H z)ᴴ = green H ((starRingEnd ℂ) z)
    rw [green, green, conjTranspose_nonsing_inv,
      conjTranspose_sub_smul hH]

end Gsig

section Loop

variable (L W : ℕ) [NeZero L]

/-- The matrix product `∏ᵢ G(σᵢ) E_{aᵢ}` of `Def:G_loop`. -/
noncomputable def gloopProd
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  (I.σ.zip I.a).foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

/-- The ordinary, unnormalized trace of a resolvent loop. -/
noncomputable def gloop
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) : ℂ :=
  Matrix.trace (gloopProd L W H z I)

variable {L W} {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ}

@[simp] theorem gloopProd_nil :
    gloopProd L W H z ⟨[], []⟩ = 1 := rfl

@[simp] theorem gloopProd_cons (s : Bool) (b : Z2 L)
    (σ : List Bool) (a : List (Z2 L)) :
    gloopProd L W H z ⟨s :: σ, b :: a⟩ =
      Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩ := rfl

omit [NeZero L] in
/-- Adding a matching sign and label preserves well-formedness. -/
theorem loopIdx_WF_cons (s : Bool) (b : Z2 L)
    {σ : List Bool} {a : List (Z2 L)}
    (h : (⟨σ, a⟩ : LoopIdx (Z2 L)).WF) :
    (⟨s :: σ, b :: a⟩ : LoopIdx (Z2 L)).WF := by
  simpa [LoopIdx.WF] using h

/-- A concatenation of two well-formed index lists gives the product of
their matrix words. The length hypothesis prevents `List.zip` truncation. -/
theorem gloopProd_append {σ₁ : List Bool} {a₁ : List (Z2 L)}
    (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (Z2 L)) :
    gloopProd L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd L W H z ⟨σ₁, a₁⟩ * gloopProd L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, gloopProd_cons, ih h, Matrix.mul_assoc]

/-- Cyclicity of the ordinary trace rotates one matching sign/block pair to
the end of the loop. -/
theorem gloop_rotate (s : Bool) (b : Z2 L)
    {σ : List Bool} {a : List (Z2 L)}
    (h : σ.length = a.length) :
    gloop L W H z ⟨s :: σ, b :: a⟩ =
      gloop L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [gloop, gloop, gloopProd_cons, gloopProd_append h [s] [b]]
  rw [Matrix.trace_mul_comm]
  simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one]

/-- Summing a loop over its first block label removes one `E_b` and gives
the dimension-correct factor `W⁻²`. -/
theorem sum_gloop_head (s : Bool) (σ : List Bool) (a : List (Z2 L)) :
    ∑ b : Z2 L, gloop L W H z ⟨s :: σ, b :: a⟩ =
      ((W : ℂ)⁻¹ ^ 2) *
        Matrix.trace (Gsig H z s * gloopProd L W H z ⟨σ, a⟩) := by
  have hterm : ∀ b : Z2 L, gloop L W H z ⟨s :: σ, b :: a⟩ =
      Matrix.trace (Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩) :=
    fun _ => rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The two-edge loop, in the form used for block resolvent correlations. -/
theorem gloop_two (s₁ s₂ : Bool) (b₁ b₂ : Z2 L) :
    gloop L W H z ⟨[s₁, s₂], [b₁, b₂]⟩ =
      Matrix.trace (Gsig H z s₁ * Eblk L W b₁ *
        (Gsig H z s₂ * Eblk L W b₂)) := by
  simp [gloop, gloopProd_cons, gloopProd_nil]

/-- The `(+,-)` two-loop is the ordinary trace of a Green function and its
adjoint with the two normalized block insertions. -/
theorem gloop_two_plus_minus_eq (hH : H.IsHermitian) (a b : Z2 L) :
    gloop L W H z ⟨[true, false], [a, b]⟩ =
      Matrix.trace (green H z * Eblk L W a *
        ((green H z)ᴴ * Eblk L W b)) := by
  have hG : green H ((starRingEnd ℂ) z) = (green H z)ᴴ :=
    (Gsig_conjTranspose hH z true).symm
  rw [gloop_two, Gsig_true, Gsig_false, hG]

/-- The `(+,-)` two-loop is a block-restricted sum of squared Green entries.
Each insertion `E_a` has weight `W⁻²`, hence the two-loop coefficient is
`W⁻⁴`. The row index lies in block `b`, the column index in block `a`. -/
theorem gloop_two_plus_minus_entries (hH : H.IsHermitian) (a b : Z2 L) :
    gloop L W H z ⟨[true, false], [a, b]⟩ =
      ((W : ℂ)⁻¹ ^ 2) ^ 2 *
        ∑ p : BlockIndex L W, ∑ q : BlockIndex L W,
          (if p.1 = b then if q.1 = a then
            (Complex.normSq (green H z p q) : ℂ) else 0 else 0) := by
  have hdiag : ∀ p : BlockIndex L W,
      Matrix.diag (green H z * Eblk L W a * ((green H z)ᴴ * Eblk L W b)) p =
        ∑ q : BlockIndex L W,
          (green H z p q * (if q.1 = a then (W : ℂ)⁻¹ ^ 2 else 0)) *
            ((starRingEnd ℂ) (green H z p q) *
              (if p.1 = b then (W : ℂ)⁻¹ ^ 2 else 0)) := by
    intro p
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    · simp only [Eblk, Matrix.mul_diagonal]
    · simp only [Eblk, Matrix.mul_diagonal,
        Matrix.conjTranspose_apply, Complex.star_def]
  have hterm : ∀ p q : BlockIndex L W,
      (green H z p q * (if q.1 = a then (W : ℂ)⁻¹ ^ 2 else 0)) *
          ((starRingEnd ℂ) (green H z p q) *
            (if p.1 = b then (W : ℂ)⁻¹ ^ 2 else 0)) =
        ((W : ℂ)⁻¹ ^ 2) ^ 2 *
          (if p.1 = b then if q.1 = a then
            (Complex.normSq (green H z p q) : ℂ) else 0 else 0) := by
    intro p q
    rw [mul_mul_mul_comm, Complex.mul_conj]
    split_ifs <;> ring
  rw [gloop_two_plus_minus_eq hH]
  rw [Matrix.trace]
  simp only [hdiag, hterm, ← Finset.mul_sum]

/-- Restricting the two site sums to their specified block fibers. The
remaining fiber at each block is `Fin W × Fin W`. -/
theorem sum_block_ite (f : BlockIndex L W → BlockIndex L W → ℂ)
    (a b : Z2 L) :
    (∑ p : BlockIndex L W, ∑ q : BlockIndex L W,
      (if p.1 = b then if q.1 = a then f p q else 0 else 0)) =
      ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W, f (b, β) (a, α) := by
  have hq : ∀ p : BlockIndex L W,
      (∑ q : BlockIndex L W,
        (if p.1 = b then if q.1 = a then f p q else 0 else 0)) =
        if p.1 = b then ∑ α : Fin W × Fin W, f p (a, α) else 0 := by
    intro p
    by_cases hp : p.1 = b
    · simp only [hp, ↓reduceIte]
      conv_lhs => rw [Fintype.sum_prod_type]
      refine (Finset.sum_eq_single a ?_ ?_).trans ?_
      · intro q₁ _ hne
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ a) h
      · simp
    · simp [hp]
  simp_rw [hq]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro p₁ _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ b) h
  · simp

/-- Explicit block-fiber form of the nonnegative `(+,-)` two-loop.
The coefficient remains `W⁻⁴`; each block contains `W²` sites. -/
theorem gloop_two_plus_minus_blocks (hH : H.IsHermitian) (a b : Z2 L) :
    gloop L W H z ⟨[true, false], [a, b]⟩ =
      ((W : ℂ)⁻¹ ^ 2) ^ 2 *
        ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,
          (Complex.normSq (green H z (b, β) (a, α)) : ℂ) := by
  rw [gloop_two_plus_minus_entries hH a b, sum_block_ite]

/-- The `(+,-)` two-loop is a nonnegative real number. -/
theorem gloop_two_plus_minus_nonneg (hH : H.IsHermitian) (a b : Z2 L) :
    ∃ r : ℝ, 0 ≤ r ∧
      gloop L W H z ⟨[true, false], [a, b]⟩ = (r : ℂ) := by
  refine ⟨((W : ℝ)⁻¹ ^ 2) ^ 2 *
      ∑ p : BlockIndex L W, ∑ q : BlockIndex L W,
        (if p.1 = b then if q.1 = a then
          Complex.normSq (green H z p q) else 0 else 0), ?_, ?_⟩
  · have hsum : (0 : ℝ) ≤
        ∑ p : BlockIndex L W, ∑ q : BlockIndex L W,
          (if p.1 = b then if q.1 = a then
            Complex.normSq (green H z p q) else 0 else 0) := by
      exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by
        split_ifs <;> first | exact Complex.normSq_nonneg _ | norm_num
    exact mul_nonneg (by positivity) hsum
  · rw [gloop_two_plus_minus_entries hH a b]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> rfl

end Loop

end RBM
