/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The two-dimensional block band model

Section 2.1 and equation `Def_matE` of the d=2 paper.  Coordinates of the paper's
`Z_{WL}²` are represented by `ZMod (W * L) × ZMod (W * L)`; the paper's
one-based blocks become the zero-based intervals `a.val * W + {0, …, W-1}`.
-/

namespace RBM

open Matrix Finset
open scoped Kronecker

/-- Block and within-block coordinates of a site. -/
abbrev BlockIndex (L W : ℕ) := Z2 L × (Fin W × Fin W)

section Kronecker

variable (L W : ℕ)

/-- The `W² × W²` matrix `S_W` with every entry `W⁻²` (Section 2.1). -/
noncomputable def SW : Matrix (Fin W × Fin W) (Fin W × Fin W) ℂ :=
  Matrix.of fun _ _ => (W : ℂ)⁻¹ ^ 2

/-- `S = S^(B) ⊗ S_W`, indexed by block and offset pairs. -/
noncomputable def Svar : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  SB L ⊗ₖ SW W

theorem Svar_apply (a b : Z2 L) (α β : Fin W × Fin W) :
    Svar L W (a, α) (b, β) = SB L a b * (W : ℂ)⁻¹ ^ 2 := rfl

theorem SW_transpose : (SW W)ᵀ = SW W := rfl

theorem sum_SW_row [NeZero W] (α : Fin W × Fin W) :
    ∑ β, SW W α β = 1 := by
  simp only [SW, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  field_simp
  norm_num [Nat.cast_mul, pow_two]

/-- The variance matrix is real symmetric. -/
theorem Svar_transpose : (Svar L W)ᵀ = Svar L W := by
  ext ⟨a, α⟩ ⟨b, β⟩
  rw [transpose_apply, Svar_apply, Svar_apply,
    show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]

theorem Svar_conjTranspose : (Svar L W)ᴴ = Svar L W := by
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [conjTranspose_apply, Svar_apply]
  rw [show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
  simp only [SB_apply, sbKernel]
  split_ifs
  · simp only [star_mul', star_inv₀, star_pow, star_ofNat, star_natCast]
  · simp only [zero_mul, star_zero]

/-- Every row of `S` has mass one, provided `L ≥ 3` and `W > 0`. -/
theorem sum_Svar_row [NeZero L] [NeZero W] (hL : 3 ≤ L) (i : BlockIndex L W) :
    ∑ j, Svar L W i j = 1 := by
  obtain ⟨a, α⟩ := i
  rw [Fintype.sum_prod_type]
  simp only [Svar, kronecker_apply, ← Finset.mul_sum, sum_SW_row, mul_one]
  exact sum_SB_row L hL a

/-- The normalized block identity `E_a` of `Def_matE`. -/
noncomputable def Eblk (a : Z2 L) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  diagonal fun p => if p.1 = a then (W : ℂ)⁻¹ ^ 2 else 0

theorem Eblk_apply (a : Z2 L) (p q : BlockIndex L W) :
    Eblk L W a p q = if p = q then (if p.1 = a then (W : ℂ)⁻¹ ^ 2 else 0) else 0 := by
  simp [Eblk, diagonal_apply]

/-- The blocks partition the identity with factor `W⁻²`. -/
theorem sum_Eblk [NeZero L] :
    ∑ a, Eblk L W a = ((W : ℂ)⁻¹ ^ 2) • (1 : Matrix _ _ ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, diagonal_apply, Matrix.smul_apply, one_apply,
    smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

theorem Eblk_conjTranspose (a : Z2 L) : (Eblk L W a)ᴴ = Eblk L W a := by
  rw [Eblk, diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem Eblk_mul_Eblk [NeZero L] (a b : Z2 L) :
    Eblk L W a * Eblk L W b =
      if a = b then ((W : ℂ)⁻¹ ^ 2) • Eblk L W a else 0 := by
  rw [Eblk, Eblk, diagonal_mul_diagonal]
  split_ifs with hab
  · subst hab
    rw [← diagonal_smul]
    congr 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  · rw [← diagonal_zero]
    congr 1
    funext p
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hab
    · ring
    · ring
    · ring

end Kronecker

section Paper

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The block containing a one-dimensional coordinate. -/
def blk (i : ZMod (W * L)) : ZMod L := ((i.val / W : ℕ) : ZMod L)

/-- The offset within a one-dimensional block. -/
def ofs (i : ZMod (W * L)) : Fin W := ⟨i.val % W, Nat.mod_lt _ (NeZero.pos W)⟩

/-- Coordinatewise block-offset decomposition. -/
def split (i : Z2 (W * L)) : BlockIndex L W :=
  ((blk L W i.1, blk L W i.2), (ofs L W i.1, ofs L W i.2))

theorem blk_val (i : ZMod (W * L)) : (blk L W i).val = i.val / W :=
  ZMod.val_natCast_of_lt (Nat.div_lt_of_lt_mul (ZMod.val_lt i))

/-- A zero-based version of the paper's interval `I_a`. -/
def I₁ (a : ZMod L) : Finset (ZMod (W * L)) :=
  (Finset.range W).image fun α => ((a.val * W + α : ℕ) : ZMod (W * L))

/-- The paper's two-dimensional block `I_a^(2) = I_(a₁) × I_(a₂)`. -/
def Iblk (a : Z2 L) : Finset (Z2 (W * L)) := (I₁ L W a.1).product (I₁ L W a.2)

theorem mem_I₁ (a : ZMod L) (i : ZMod (W * L)) :
    i ∈ I₁ L W a ↔ blk L W i = a := by
  have hW : 0 < W := NeZero.pos W
  rw [I₁, Finset.mem_image]
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [Finset.mem_range] at hα
    have hlt : a.val * W + α < W * L := by
      have := ZMod.val_lt a
      nlinarith
    rw [blk, ZMod.val_natCast_of_lt hlt, mul_comm, Nat.mul_add_div hW,
      Nat.div_eq_of_lt hα, add_zero, ZMod.natCast_zmod_val]
  · intro h
    refine ⟨i.val % W, Finset.mem_range.mpr (Nat.mod_lt _ hW), ?_⟩
    rw [← h, blk_val, Nat.div_add_mod', ZMod.natCast_zmod_val]

theorem mem_Iblk (a : Z2 L) (i : Z2 (W * L)) :
    i ∈ Iblk L W a ↔ (split L W i).1 = a := by
  rcases a with ⟨a₁, a₂⟩
  simp [Iblk, split, mem_I₁]

theorem split_injective : Function.Injective (split L W) := by
  intro i j h
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := h
  apply Prod.ext
  · apply ZMod.val_injective
    have hb : i.1.val / W = j.1.val / W := by rw [← blk_val, ← blk_val, h₁]
    have ho : i.1.val % W = j.1.val % W := congrArg Fin.val h₃
    rw [← Nat.div_add_mod' i.1.val W, ← Nat.div_add_mod' j.1.val W, hb, ho]
  · apply ZMod.val_injective
    have hb : i.2.val / W = j.2.val / W := by rw [← blk_val, ← blk_val, h₂]
    have ho : i.2.val % W = j.2.val % W := congrArg Fin.val h₄
    rw [← Nat.div_add_mod' i.2.val W, ← Nat.div_add_mod' j.2.val W, hb, ho]

theorem split_bijective : Function.Bijective (split L W) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨split_injective L W, ?_⟩
  simp only [Z2, BlockIndex, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring

/-- `Z_(WL)² ≃ Z_L² × {0,…,W-1}²`. -/
noncomputable def splitEquiv : Z2 (W * L) ≃ BlockIndex L W :=
  Equiv.ofBijective _ (split_bijective L W)

/-- The Section 2.1 covariance at literal paper indices. -/
noncomputable def Spaper (i j : Z2 (W * L)) : ℂ :=
  SB L (blk L W i.1, blk L W i.2) (blk L W j.1, blk L W j.2) * (W : ℂ)⁻¹ ^ 2

/- Literal five-point indicator form of the paper's covariance entry. -/
omit [NeZero L] [NeZero W] in
theorem Spaper_indicator (i j : Z2 (W * L)) :
    Spaper L W i j =
      if (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L
      then (5 : ℂ)⁻¹ * (W : ℂ)⁻¹ ^ 2 else 0 := by
  simp only [Spaper, SB_apply, sbKernel]
  split_ifs <;> ring

omit [NeZero L] in
theorem Spaper_eq (i j : Z2 (W * L)) :
    Spaper L W i j = Svar L W (split L W i) (split L W j) := rfl

omit [NeZero L] in
theorem Spaper_eq_submatrix :
    Matrix.of (Spaper L W) = (Svar L W).submatrix (split L W) (split L W) := by
  ext i j
  exact Spaper_eq L W i j

omit [NeZero L] in
theorem Spaper_transpose :
    (Matrix.of (Spaper L W))ᵀ = Matrix.of (Spaper L W) := by
  ext i j
  change Spaper L W j i = Spaper L W i j
  rw [Spaper_eq, Spaper_eq]
  simpa only [transpose_apply] using
    (congrFun (congrFun (Svar_transpose L W) (split L W i)) (split L W j))

omit [NeZero L] in
theorem Spaper_conjTranspose :
    (Matrix.of (Spaper L W))ᴴ = Matrix.of (Spaper L W) := by
  ext i j
  change star (Spaper L W j i) = Spaper L W i j
  rw [Spaper_eq, Spaper_eq]
  simpa only [conjTranspose_apply] using
    (congrFun (congrFun (Svar_conjTranspose L W) (split L W i)) (split L W j))

/-- Every row of the covariance matrix sums to one at paper indices. -/
theorem sum_Spaper_row (hL : 3 ≤ L) (i : Z2 (W * L)) :
    ∑ j, Spaper L W i j = 1 := by
  simp only [Spaper_eq]
  calc
    ∑ j : Z2 (W * L), Svar L W (split L W i) (split L W j) =
        ∑ k : BlockIndex L W, Svar L W (split L W i) k := by
          exact Fintype.sum_equiv (splitEquiv L W) _ _ (fun _ => rfl)
    _ = 1 := sum_Svar_row L W hL (split L W i)

/-- The matrix `E_a` in `Def_matE` at literal paper indices. -/
noncomputable def Epaper (a : Z2 L) :
    Matrix (Z2 (W * L)) (Z2 (W * L)) ℂ :=
  Matrix.of fun i j => if i = j then (W : ℂ)⁻¹ ^ 2 * (if i ∈ Iblk L W a then 1 else 0) else 0

theorem Epaper_eq (a : Z2 L) (i j : Z2 (W * L)) :
    Epaper L W a i j = Eblk L W a (split L W i) (split L W j) := by
  simp only [Epaper, Matrix.of_apply, Eblk, diagonal_apply,
    (split_injective L W).eq_iff, mem_Iblk]
  by_cases h : i = j
  · subst h
    split_ifs <;> simp [*]
  · simp [h]

theorem Epaper_eq_submatrix (a : Z2 L) :
    Epaper L W a = (Eblk L W a).submatrix (split L W) (split L W) := by
  ext i j
  exact Epaper_eq L W a i j

theorem Epaper_conjTranspose (a : Z2 L) : (Epaper L W a)ᴴ = Epaper L W a := by
  ext i j
  change star (Epaper L W a j i) = Epaper L W a i j
  rw [Epaper_eq, Epaper_eq]
  simpa only [conjTranspose_apply] using
    (congrFun (congrFun (Eblk_conjTranspose L W a) (split L W i)) (split L W j))

/-- The paper-indexed block identities partition `W⁻² I`. -/
theorem sum_Epaper :
    ∑ a, Epaper L W a = ((W : ℂ)⁻¹ ^ 2) • (1 : Matrix _ _ ℂ) := by
  ext i j
  have h := congrFun (congrFun (sum_Eblk L W) (split L W i)) (split L W j)
  simpa only [Matrix.sum_apply, Matrix.smul_apply, one_apply, smul_eq_mul,
    ← Epaper_eq, (split_injective L W).eq_iff] using h

end Paper

/-- A nondegenerate instance: distinct sites in one block have covariance `1/20`. -/
theorem model_concrete_witness :
    Svar 3 2 ((0, 0), (0, 0)) ((0, 0), (1, 1)) = (1 / 20 : ℂ) := by
  have h : (0 : Z2 3) ∈ sbSupport 3 := by
    simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton]
    left
    apply Prod.ext <;> rfl
  norm_num [Svar_apply, SB_apply, sbKernel, h]

end RBM
