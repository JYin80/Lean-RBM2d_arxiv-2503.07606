/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Split
import RBM2D.Hierarchy.WardResolvent
import RBM2D.Gauss.SpectralWindow
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Path.Scales
import Mathlib.Algebra.Order.Chebyshev

/-!
# The deterministic part of `lem_ConArg` in `d = 2`: (6.3)–(6.12) of [YY_25]

The argument parallels the one-dimensional formalization, for the two-dimensional block index
`BlockIndex L W = Z2 L × (Fin W × Fin W)` and block labels in `Z2 L`.  Everything here is for a
**fixed deterministic Hermitian** `H`: no expectation and no `≺`.  The paper (Section
`sec:Inh_LE`, the proof of Lemma `lem_ConArg`) states that the only changes with respect to
`d = 1` are the factor `W²` for `W` and `ℓ²` for `ℓ`; here the block has `W²` sites,
`E_a = W⁻² 1_{𝓘_a}`, and `ℓ` does not enter.

* `zSig`, `isUnit_sub_zSig`, `green_eq_add_smul_mul`, `Gsig_eq_add_smul_mul`: **(6.3)**.
* `list_prod_add_eq`, `gchainMixed`, `gchain_eq_add_sum_gchainMixed`: **(6.7)**, **(6.8)**.
* `norm_gchain_apply_sq_le`: **(6.9)**, `C_m = m + 1`.
* `gloop_symm_eq_trace`: **(6.5)**.
* `ward_chain_row`, `ward_chain_row'`: **(6.12)**, row average `W⁻² ∑_{α ∈ [W]²}`.
* `ztTilde`, `ztTilde_arith`: the arithmetic of `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`.
* `IsGLoopProd`, `norm_trace_smul_sub_pow_mul_le`, `exists_conjTranspose_mul_Eblk`,
  `sum_norm_gchain_row_sq_le`: Ward for loop products and (6.12) as an inequality.
* `blockCols`, `blockSel`, `trace_gram_blockCols_pow`, `trace_gram_rpow_le`: the Gram matrix
  `A` of the `W²` block columns; `R Rᵀ = W² E_b`, and
  `(tr A^p)^{1/p} ≤ W² (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`.
* `wmass_gchain_mul_gchain_le`, `wmass_gchainMixed_le`: **(6.10)**, the powers `W⁻²` and `W²`
  cancel exactly as `W⁻¹` and `W` do for `d = 1`.
* `norm_gloop_symIdx_le_tilde`, `loopMax_two_mul_le_tilde`: **(6.11)**.

Names in `RBM.Gauss` and `RBM.Path` are written qualified; `RBM.Gauss` is not opened
(`RBM.KLoop.etaT` and `RBM.Path.etaT` both exist).
-/

namespace RBM.Ind

open Matrix

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral parameter carried by the charge `s`: `z` for `+`, `z̄` for `-`.
By definition `Gsig H z s = green H (zSig z s)`. -/
def zSig (z : ℂ) (s : Bool) : ℂ := if s then z else (starRingEnd ℂ) z

theorem norm_zSig_sub_zSig (z w : ℂ) (s : Bool) : ‖zSig z s - zSig w s‖ = ‖z - w‖ := by
  cases s
  · simp only [zSig, Bool.false_eq_true, ↓reduceIte, ← map_sub, Complex.norm_conj]
  · rfl

theorem im_zSig (z : ℂ) (s : Bool) : (zSig z s).im = if s then z.im else -z.im := by
  cases s <;> simp [zSig]

/-- A Hermitian matrix minus a non-real multiple of the identity is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hHv : H *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have him := hH.im_star_dotProduct_mulVec_self v
  rw [hHv, dotProduct_smul, smul_eq_mul] at him
  have hd : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hpos : (∑ i, Complex.normSq (v i) : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (v j))).mp h0 i (Finset.mem_univ i))
  rw [hd, RCLike.im_to_complex, Complex.im_mul_ofReal] at him
  exact hz ((mul_eq_zero.mp him).resolve_right hpos)

theorem isUnit_sub_zSig {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (s : Bool) : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)) := by
  refine isUnit_sub_smul_one_of_im_ne_zero hH ?_
  rw [im_zSig]
  split_ifs
  · exact hz
  · exact neg_ne_zero.mpr hz

/-- **(6.3)**, the two-parameter resolvent identity `G = G̃ + (z - z̃)·G·G̃`, where
`G = (H - z)⁻¹` and `G̃ = (H - z̃)⁻¹` share the same matrix `H`. -/
theorem green_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ))) (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z = green H w + (z - w) • (green H z * green H w) := by
  rw [← green_sub_green hz hw]
  abel

/-- **(6.3) with charges**: `G(σ) = G̃(σ) + (z_σ - z̃_σ)·G(σ)·G̃(σ)`, where `z_+ = z` and
`z_- = z̄`. -/
theorem Gsig_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ} {s : Bool}
    (hz : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - zSig w s • (1 : Matrix n n ℂ))) :
    Gsig H z s = Gsig H w s + (zSig z s - zSig w s) • (Gsig H z s * Gsig H w s) :=
  green_eq_add_smul_mul hz hw

/-- The conjugate resolvent identity in the order `G(z) G(z̄)`, from `green_sub_green`
(`green_sub_green_conj'` has the order `G(z̄) G(z)`). -/
private theorem green_sub_green_conj {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ)) • (green H z * green H ((starRingEnd ℂ) z)) := by
  rw [green_sub_green hz hz']
  congr 1
  rw [Complex.sub_conj]
  push_cast
  ring

end Spectral

section ChainExpansion

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

/-- The `l`-th term of the chain expansion (6.8): the mixed chain
`G_1 E_{a_1} ⋯ E_{a_{l-1}} G_l · G̃_l E_{a_l} G̃_{l+1} ⋯ E_{a_{m-1}} G̃_m`
(indices counted from `0` here), with `l+1` resolvents at `z` and `m-l` at `w = z̃`, and
no `E` between `G_l` and `G̃_l`. -/
noncomputable def gchainMixed (L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z w : ℂ) (τ : List Bool)
    (a : List (Z2 L)) (l : ℕ) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  gchain L W H z (τ.take (l + 1)) (a.take l) * gchain L W H w (τ.drop l) (a.drop l)

/-- **(6.8)**, the chain expansion.  If every resolvent of the chain at `z` is expanded
around `w = z̃` by (6.3), then
\[ C_z = C_w + \sum_{l} (z_{σ_l} - w_{σ_l})\,
      G_1E_{a_1}\cdots G_l\cdot\tilde G_lE_{a_l}\cdots\tilde G_m . \]
This is (6.7) with `a_k + b_k ↦ G_k E_{a_k}`, `a_k ↦ G̃_k E_{a_k}`; we prove it directly
by induction on the chain. -/
theorem gchain_eq_add_sum_gchainMixed {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    {τ : List Bool} {a : List (Z2 L)} (h : τ.length = a.length + 1) :
    gchain L W H z τ a = gchain L W H w τ a
      + ∑ l ∈ Finset.range τ.length,
          (zSig z (τ.getD l true) - zSig w (τ.getD l true)) • gchainMixed L W H z w τ a l := by
  induction τ generalizing a with
  | nil => simp at h
  | cons s τ ih =>
    cases a with
    | nil =>
      have hτ : τ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hτ
      simp only [gchainMixed, List.length_singleton, Finset.sum_range_one, List.getD_cons_zero,
        List.drop_zero, gchain, List.take_succ_cons, List.take_nil]
      exact Gsig_eq_add_smul_mul (hz s) (hw s)
    | cons c a =>
      have h' : τ.length = a.length + 1 := by simpa using h
      have key : Gsig H z s * Eblk L W c * gchain L W H w τ a
          = gchain L W H w (s :: τ) (c :: a)
            + (zSig z s - zSig w s) • (Gsig H z s * gchain L W H w (s :: τ) (c :: a)) := by
        rw [gchain_cons]
        nth_rewrite 1 [Gsig_eq_add_smul_mul (hz s) (hw s)]
        simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [gchain_cons, ih h', Matrix.mul_add, key, List.length_cons, Finset.sum_range_succ']
      simp only [gchainMixed, gchain_cons, List.take_succ_cons, List.drop_succ_cons,
        List.getD_cons_succ, List.getD_cons_zero, List.take_zero, List.drop_zero, gchain]
      simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]
      abel

/-- The elementary Cauchy–Schwarz step behind (6.9):
`‖x + ∑_{l<m} y_l‖² ≤ (m+1)(‖x‖² + ∑_{l<m} ‖y_l‖²)`. -/
theorem norm_add_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] (x : E) (y : ℕ → E)
    (m : ℕ) :
    ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2
      ≤ (m + 1 : ℝ) * (‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2) := by
  set f : ℕ → ℝ := fun k => if k = 0 then ‖x‖ else ‖y (k - 1)‖ with hf
  have hsum : ∑ k ∈ Finset.range (m + 1), f k = ‖x‖ + ∑ l ∈ Finset.range m, ‖y l‖ := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have hsum2 : ∑ k ∈ Finset.range (m + 1), f k ^ 2
      = ‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2 := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have h1 : ‖x + ∑ l ∈ Finset.range m, y l‖ ≤ ∑ k ∈ Finset.range (m + 1), f k := by
    rw [hsum]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := f)
  rw [Finset.card_range, hsum2] at h2
  push_cast at h2
  calc ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2 ≤ (∑ k ∈ Finset.range (m + 1), f k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **(6.9)**, the termwise Cauchy–Schwarz bound: for every entry `(i, j)`,
\[ |(C_z)_{ij}|^2 \le (m+1)\Bigl(|(C_{w})_{ij}|^2
      + |z-w|^2\sum_{l<m}\bigl|(G_1E_{a_1}\cdots G_l\tilde G_l\cdots\tilde G_m)_{ij}\bigr|^2\Bigr),
\]
`m` the number of resolvents in the chain.  The paper's `C_m` is `m + 1` here. -/
theorem norm_gchain_apply_sq_le {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    {τ : List Bool} {a : List (Z2 L)} (h : τ.length = a.length + 1)
    (i j : BlockIndex L W) :
    ‖gchain L W H z τ a i j‖ ^ 2
      ≤ (τ.length + 1 : ℝ) * (‖gchain L W H w τ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range τ.length, ‖gchainMixed L W H z w τ a l i j‖ ^ 2) := by
  have hij := congrFun (congrFun (gchain_eq_add_sum_gchainMixed hz hw h) i) j
  rw [Matrix.add_apply, Matrix.sum_apply] at hij
  rw [hij]
  refine (norm_add_sum_sq_le _ _ _).trans_eq ?_
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_zSig_sub_zSig, mul_pow]

end ChainExpansion

section SymmetricLoop

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
  {z : ℂ}

omit [NeZero W] in
/-- A chain ending in `G(s)` is the loop product of its first blocks times `G(s)`. -/
theorem gchain_append_singleton {ρ : List Bool} {b : List (Z2 L)} (h : ρ.length = b.length)
    (s : Bool) :
    gchain L W H z (ρ ++ [s]) b = gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s := by
  induction ρ generalizing b with
  | nil =>
    obtain rfl : b = [] := List.eq_nil_of_length_eq_zero h.symm
    simp [gchain]
  | cons r ρ ih =>
    cases b with
    | nil => simp at h
    | cons c b =>
      have h' : ρ.length = b.length := by simpa using h
      rw [List.cons_append, gchain_cons, ih h', gloopProd_cons]
      simp only [Matrix.mul_assoc]

omit [NeZero W] in
/-- `2iη·G(σ)G(σ)† = G(+) - G(-)` for either charge `σ`: the resolvent form of Ward's
identity `G G† = (G - G†)/(2i Im z)` used twice in §6. -/
theorem Gsig_mul_conjTranspose (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (s : Bool) :
    (2 * Complex.I * (z.im : ℂ)) • (Gsig H z s * (Gsig H z s)ᴴ)
      = Gsig H z true - Gsig H z false := by
  rw [Gsig_conjTranspose hH]
  cases s
  · exact (green_sub_green_conj' hz hz').symm
  · exact (green_sub_green_conj hz hz').symm

omit [NeZero W] in
/-- `⟨E_{a₀} P P†⟩ = W⁻² ∑_{i ∈ I_{a₀}} ‖P_{i·}‖²`: the trace against a block projection
is the averaged squared row norm. -/
theorem trace_Eblk_mul_mul_conjTranspose (P : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (a0 : Z2 L) :
    Matrix.trace (Eblk L W a0 * P * Pᴴ)
      = (W : ℂ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
          (Complex.normSq (P (a0, α) k) : ℂ) := by
  have hdiag : ∀ p : BlockIndex L W, (Eblk L W a0 * P * Pᴴ) p p
      = if p.1 = a0 then (W : ℂ)⁻¹ ^ 2 * ∑ k, (Complex.normSq (P p k) : ℂ) else 0 := by
    intro p
    rw [Matrix.mul_assoc, Eblk, Matrix.diagonal_mul]
    split_ifs
    · congr 1
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    · simp
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a0]
  · simp [Finset.mul_sum]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ a0) h

omit [NeZero W] in
/-- Closing a half-chain around `G(s')` gives a symmetric loop of odd length:
`⟨E_{a₀} Q G(s') Q†⟩ = L_{(ρ, s', \bar ρ^{rev}), (b, b^{rev}, a₀)}` with
`Q = G_1E_{b_1}⋯G_kE_{b_k}`. -/
theorem trace_Eblk_gloopProd_Gsig_conjTranspose (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (Z2 L)} (h : ρ.length = b.length) (s : Bool) (a0 : Z2 L) :
    Matrix.trace (Eblk L W a0 * gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s
        * (gloopProd L W H z ⟨ρ, b⟩)ᴴ)
      = gloop L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ
      = gchain L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, Gsig_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.trace_mul_comm, Matrix.mul_assoc,
    gchain_mul_Eblk h', gloop, gloopProd_append h]

omit [NeZero W] in
/-- **(6.12)**, the Ward step.  With `v^{(l)}_k = (G_1E_{a_1}⋯E_{a_{l-1}}G_l)_{ik}`,
\[ 2i\operatorname{Im}z\cdot W^{-2}\sum_{i\in I_{a_0}}\|v^{(l)}\|_2^2
    = \mathcal L_{σ^{(1)}_l, \mathbf a_l} - \mathcal L_{σ^{(2)}_l, \mathbf a_l}, \]
where `σ^{(1,2)}_l = (σ_1, …, σ_{l-1}, ±, \bar σ_{l-1}, …, \bar σ_1)` and
`a_l = (a_1, …, a_{l-1}, a_{l-1}, …, a_1, a_0)` (a rotation of the paper's labelling).
Here the chain is `gchain (ρ ++ [s]) b` with `ρ = (σ_1, …, σ_{l-1})`, `s = σ_l`,
`b = (a_1, …, a_{l-1})`; the right side does not depend on `s`. -/
theorem ward_chain_row (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)))
    {ρ : List Bool} {b : List (Z2 L)} (h : ρ.length = b.length) (s : Bool) (a0 : Z2 L) :
    (2 * Complex.I * (z.im : ℂ)) * ((W : ℂ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
        (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ))
      = gloop L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  rw [← trace_Eblk_mul_mul_conjTranspose, ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h,
    ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h, ← Matrix.trace_sub, ← smul_eq_mul,
    ← Matrix.trace_smul, gchain_append_singleton h, Matrix.conjTranspose_mul]
  congr 1
  set Q := gloopProd L W H z ⟨ρ, b⟩
  have hW := Gsig_mul_conjTranspose hH hz hz' s
  calc (2 * Complex.I * (z.im : ℂ)) • (Eblk L W a0 * (Q * Gsig H z s) * ((Gsig H z s)ᴴ * Qᴴ))
      = Eblk L W a0 * Q * ((2 * Complex.I * (z.im : ℂ)) • (Gsig H z s * (Gsig H z s)ᴴ))
          * Qᴴ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hW, Matrix.mul_sub, Matrix.sub_mul]

omit [NeZero W] in
/-- **(6.12)** in the paper's form, solved for the row norms:
`W⁻² ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² = (2i Im z)⁻¹ (L_{σ^{(1)}} - L_{σ^{(2)}})`. -/
theorem ward_chain_row' (hH : H.IsHermitian) (hη : z.im ≠ 0)
    {ρ : List Bool} {b : List (Z2 L)} (h : ρ.length = b.length) (s : Bool) (a0 : Z2 L) :
    (W : ℂ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
        (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ)
      = (2 * Complex.I * (z.im : ℂ))⁻¹
        * (gloop L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
          - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩) := by
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, hη]
  rw [eq_inv_mul_iff_mul_eq₀ hc]
  exact ward_chain_row hH (isUnit_sub_smul_one_of_im_ne_zero hH hη)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hη)) h s a0

end SymmetricLoop

section Arithmetic

/-- The shifted spectral parameter of §6: `z̃_{t₁} := (t₂/t₁)^{1/2} z_{t₁}`. -/
noncomputable def ztTilde (E t₁ t₂ : ℝ) : ℂ := (Real.sqrt (t₂ / t₁) : ℂ) * Gauss.spectralZ E t₁

theorem ztTilde_im (E t₁ t₂ : ℝ) :
    (ztTilde E t₁ t₂).im = Real.sqrt (t₂ / t₁) * Path.etaT E t₁ := by
  rw [ztTilde, Complex.im_ofReal_mul, Gauss.spectralZ_im, Path.etaT]

theorem etaT_nonneg (E : ℝ) {t : ℝ} (ht : t ≤ 1) : 0 ≤ Path.etaT E t := by
  rw [Path.etaT, Gauss.spectralM_im]
  have : 0 ≤ 1 - t := by linarith
  positivity

/-- In the bulk `|E| ≤ 2 - κ`, `Im m^{(E)} ≥ κ/2`. -/
theorem half_le_mE_im {E κ : ℝ} (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ (Gauss.spectralM E).im := by
  rw [Gauss.spectralM_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have : κ ≤ Real.sqrt (4 - E ^ 2) := by
    rw [Real.le_sqrt hκ (by nlinarith)]
    nlinarith
  linarith

variable {c E t₁ t₂ : ℝ}

/-- `1 ≤ (t₂/t₁)^{1/2} ≤ t₂/t₁ ≤ c⁻¹` and `(t₂/t₁)^{1/2} - 1 ≤ (t₂-t₁)/c`. -/
theorem sqrt_div_bounds (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    1 ≤ Real.sqrt (t₂ / t₁) ∧ Real.sqrt (t₂ / t₁) ≤ c⁻¹
      ∧ Real.sqrt (t₂ / t₁) - 1 ≤ (t₂ - t₁) / c := by
  have ht₁ : 0 < t₁ := lt_of_lt_of_le hc h₁
  have hq : 1 ≤ t₂ / t₁ := (one_le_div ht₁).mpr h₁₂
  have hs1 : 1 ≤ Real.sqrt (t₂ / t₁) := Real.one_le_sqrt.mpr hq
  have hsq : Real.sqrt (t₂ / t₁) ^ 2 = t₂ / t₁ := Real.sq_sqrt (by linarith)
  have hle : Real.sqrt (t₂ / t₁) ≤ t₂ / t₁ := by nlinarith
  have hq' : t₂ / t₁ ≤ c⁻¹ := by
    rw [div_le_iff₀ ht₁]
    calc t₂ ≤ 1 := h₂
      _ = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ * t₁ := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr hc.le)
  refine ⟨hs1, hle.trans hq', ?_⟩
  have h1 : Real.sqrt (t₂ / t₁) - 1 ≤ t₂ / t₁ - 1 := by linarith
  have h2 : t₂ / t₁ - 1 = (t₂ - t₁) / t₁ := by field_simp
  have h3 : (t₂ - t₁) / t₁ ≤ (t₂ - t₁) / c :=
    div_le_div_of_nonneg_left (by linarith) hc h₁
  linarith

/-- `Im z̃_{t₁} ≍ Im z_{t₁}`: `η_{t₁} ≤ Im z̃_{t₁} ≤ c⁻¹ η_{t₁}`. -/
theorem etaT_le_ztTilde_im (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    Path.etaT E t₁ ≤ (ztTilde E t₁ t₂).im ∧ (ztTilde E t₁ t₂).im ≤ c⁻¹ * Path.etaT E t₁ := by
  obtain ⟨hs1, hsc, -⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  rw [ztTilde_im]
  constructor
  · nlinarith
  · exact mul_le_mul_of_nonneg_right hsc hη

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (t₂ - t₁)` with `C = 3/c + 1`. -/
theorem norm_zt_sub_ztTilde_le (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1)
    (hE : |E| ≤ 2) : ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (t₂ - t₁) := by
  obtain ⟨hs1, -, hs⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  set s := Real.sqrt (t₂ / t₁)
  have hm := Gauss.norm_spectralM hE
  have hkey : Gauss.spectralZ E t₂ - ztTilde E t₁ t₂
      = ((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E)
        - ((t₂ - t₁ : ℝ) : ℂ) * Gauss.spectralM E := by
    simp only [Gauss.spectralZ, ztTilde, s]
    push_cast
    ring
  have ht₁ : 1 - t₁ ≤ 1 := by linarith [lt_of_lt_of_le hc h₁]
  have ht₁' : 0 ≤ 1 - t₁ := by linarith
  have hin : ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E‖ ≤ 3 := by
    calc ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E‖
        ≤ ‖(E : ℂ)‖ + ‖((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E‖ := norm_add_le _ _
      _ = |E| + (1 - t₁) := by
          rw [norm_mul, hm, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_of_nonneg ht₁', mul_one]
      _ ≤ 3 := by linarith
  rw [hkey]
  calc ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E)
        - ((t₂ - t₁ : ℝ) : ℂ) * Gauss.spectralM E‖
      ≤ ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * Gauss.spectralM E)‖
        + ‖((t₂ - t₁ : ℝ) : ℂ) * Gauss.spectralM E‖ := norm_sub_le _ _
    _ ≤ (s - 1) * 3 + (t₂ - t₁) := by
        rw [norm_mul, norm_mul, hm, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonpos (by linarith), Real.norm_of_nonneg (by linarith), mul_one]
        have := mul_le_mul_of_nonneg_left hin (by linarith : 0 ≤ -(1 - s))
        linarith
    _ ≤ 3 * ((t₂ - t₁) / c) + (t₂ - t₁) := by linarith
    _ = (3 / c + 1) * (t₂ - t₁) := by ring

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (1 - t₁)`, the form stated in §6. -/
theorem norm_zt_sub_ztTilde_le_one_sub (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2) :
    ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (1 - t₁) := by
  refine (norm_zt_sub_ztTilde_le hc h₁ h₁₂ h₂ hE).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- In the bulk, `|z_{t₂} - z̃_{t₁}| ≤ C η_{t₁}` with `C = (3/c + 1)·(2/κ)`. -/
theorem norm_zt_sub_ztTilde_le_etaT {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (h₁ : c ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2 - κ) :
    ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (2 / κ) * Path.etaT E t₁ := by
  refine (norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)).trans ?_
  have hm := half_le_mE_im hκ.le hE
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h1 : 1 - t₁ ≤ 2 / κ * Path.etaT E t₁ := by
    rw [Path.etaT, div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The arithmetic of `z̃_{t₁}` in §6.**  For `c ≤ t₁ ≤ t₂ ≤ 1` and `|E| ≤ 2 - κ`:
\[ |z_{t_2}-\tilde z_{t_1}| \le C(1-t_1),\quad |z_{t_2}-\tilde z_{t_1}|^2 \le C\eta_{t_1}^2,
    \quad \frac{|z_{t_2}-\tilde z_{t_1}|^2}{\operatorname{Im}\tilde z_{t_1}} \le C\eta_{t_1},
    \quad \eta_{t_1}\le\operatorname{Im}\tilde z_{t_1}\le C\eta_{t_1}. \]
The constant depends only on `c` and `κ`. -/
theorem ztTilde_arith {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ C > 0, ∀ E t₁ t₂ : ℝ, c ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 → |E| ≤ 2 - κ →
      ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ≤ C * (1 - t₁)
      ∧ ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ C * Path.etaT E t₁ ^ 2
      ∧ ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ^ 2 / (ztTilde E t₁ t₂).im ≤ C * Path.etaT E t₁
      ∧ Path.etaT E t₁ ≤ (ztTilde E t₁ t₂).im
      ∧ (ztTilde E t₁ t₂).im ≤ C * Path.etaT E t₁ := by
  set K := (3 / c + 1) * (2 / κ) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(3 / c + 1) + K ^ 2 + c⁻¹, by positivity, ?_⟩
  intro E t₁ t₂ h₁ h₁₂ h₂ hE
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  have hd := norm_zt_sub_ztTilde_le_etaT hc hκ h₁ h₁₂ h₂ hE
  have hd' := norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)
  obtain ⟨hIm1, hIm2⟩ := etaT_le_ztTilde_im (E := E) hc h₁ h₁₂ h₂
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h3 : 0 ≤ 3 / c + 1 := by positivity
  have hC1 : K ^ 2 ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hC2 : c⁻¹ ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hsq : ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * Path.etaT E t₁ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  refine ⟨?_, ?_, ?_, hIm1, ?_⟩
  · refine hd'.trans ?_
    nlinarith
  · exact hsq.trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg _))
  · refine div_le_of_le_mul₀ (hη.trans hIm1) (by positivity) ?_
    calc ‖Gauss.spectralZ E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * Path.etaT E t₁ ^ 2 := hsq
      _ = (K ^ 2 * Path.etaT E t₁) * Path.etaT E t₁ := by ring
      _ ≤ ((3 / c + 1) + K ^ 2 + c⁻¹) * Path.etaT E t₁ * (ztTilde E t₁ t₂).im := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hC1 hη) hIm1 hη (by positivity)
  · exact hIm2.trans (mul_le_mul_of_nonneg_right hC2 hη)

end Arithmetic

section LoopProd

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
  {z : ℂ}

variable (L W) in
/-- `M` is the loop product `∏_i G(σ_i) E_{a_i}` of some loop index of length `r`. -/
def IsGLoopProd (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (r : ℕ)
    (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) : Prop :=
  ∃ I : LoopIdx (Z2 L), I.σ.length = r ∧ I.a.length = r ∧ M = gloopProd L W H z I

omit [NeZero W] in
theorem isGLoopProd_one : IsGLoopProd L W H z 0 1 :=
  ⟨⟨[], []⟩, rfl, rfl, gloopProd_nil.symm⟩

omit [NeZero W] in
theorem IsGLoopProd.mul {r r' : ℕ} {M M' : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (h : IsGLoopProd L W H z r M) (h' : IsGLoopProd L W H z r' M') :
    IsGLoopProd L W H z (r + r') (M * M') := by
  obtain ⟨⟨σ, a⟩, hσ, ha, rfl⟩ := h
  obtain ⟨⟨σ', a'⟩, hσ', ha', rfl⟩ := h'
  refine ⟨⟨σ ++ σ', a ++ a'⟩, by simp_all, by simp_all, ?_⟩
  exact (gloopProd_append (by simp_all) σ' a').symm

omit [NeZero W] in
theorem IsGLoopProd.norm_trace_le {r : ℕ} {M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (h : IsGLoopProd L W H z r M) : ‖trace M‖ ≤ loopMax L W H z r := by
  obtain ⟨I, hσ, ha, rfl⟩ := h
  exact norm_gloop_le_loopMax I hσ ha

omit [NeZero W] in
/-- The trace of a power of `c(Z₊ - Z₋)`, `Z_±` loop products of length `q`, times a loop
product of length `r`, is bounded by `(2|c|)^j max|L^{(jq+r)}|`: expand one factor at a time. -/
theorem norm_trace_smul_sub_pow_mul_le {q : ℕ} {Zp Zm : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hp : IsGLoopProd L W H z q Zp) (hm : IsGLoopProd L W H z q Zm) {c : ℂ} {β : ℝ}
    (hβ : 2 * ‖c‖ ≤ β) (j : ℕ) :
    ∀ {r : ℕ} {R : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}, IsGLoopProd L W H z r R →
      ‖trace ((c • (Zp - Zm)) ^ j * R)‖ ≤ β ^ j * loopMax L W H z (j * q + r) := by
  have hβ0 : 0 ≤ β := le_trans (by positivity) hβ
  induction j with
  | zero =>
    intro r R hR
    simpa using hR.norm_trace_le
  | succ j ih =>
    intro r R hR
    have e : (j + 1) * q + r = j * q + (q + r) := by ring
    rw [pow_succ, Matrix.mul_assoc, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_sub, trace_smul, trace_sub, e, norm_smul]
    have h1 := ih (hp.mul hR)
    have h2 := ih (hm.mul hR)
    calc ‖c‖ * ‖trace ((c • (Zp - Zm)) ^ j * (Zp * R)) - trace ((c • (Zp - Zm)) ^ j * (Zm * R))‖
        ≤ ‖c‖ * (β ^ j * loopMax L W H z (j * q + (q + r))
            + β ^ j * loopMax L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _)
      _ = (2 * ‖c‖) * (β ^ j * loopMax L W H z (j * q + (q + r))) := by ring
      _ ≤ β * (β ^ j * loopMax L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_right hβ (mul_nonneg (pow_nonneg hβ0 _) (loopMax_nonneg _))
      _ = _ := by ring

end LoopProd

section Ward

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
  {z : ℂ}

omit [NeZero W] in
/-- The matrix form of closing a half-chain around `G(s)`:
`Q G(s) Q† E_{a₀} = ∏ G E` over the index `(ρ, s, \bar ρ^{rev}), (b, b^{rev}, a₀)`. -/
theorem gloopProd_Gsig_conjTranspose_Eblk (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (Z2 L)} (h : ρ.length = b.length) (s : Bool) (a0 : Z2 L) :
    gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ * Eblk L W a0
      = gloopProd L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ
      = gchain L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, Gsig_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc (gloopProd L W H z ⟨ρ, b⟩), hG, Matrix.mul_assoc, gchain_mul_Eblk h',
    ← gloopProd_append h]

omit [NeZero W] in
/-- **Ward's identity for the Gram matrix of (6.10).**  For a chain `Y` with `k` resolvents,
`Y† Y E_b = (2i Im z)⁻¹ (Z₊ - Z₋)` with `Z_±` loop products of length `2k - 1`. -/
theorem exists_conjTranspose_mul_Eblk (hH : H.IsHermitian) (hz : z.im ≠ 0) {τ : List Bool}
    {c : List (Z2 L)} (h : τ.length = c.length + 1) (b : Z2 L) :
    ∃ Zp Zm : Matrix (BlockIndex L W) (BlockIndex L W) ℂ,
      IsGLoopProd L W H z (2 * τ.length - 1) Zp ∧ IsGLoopProd L W H z (2 * τ.length - 1) Zm ∧
      (gchain L W H z τ c)ᴴ * gchain L W H z τ c * Eblk L W b
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Zp - Zm) := by
  have hY := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH h
  set τ' := (τ.map (!·)).reverse with hτ'
  have hlen : τ'.length = τ.length := by simp [hτ']
  rcases List.eq_nil_or_concat' τ' with h0 | ⟨ρ, s, hρ⟩
  · rw [h0] at hlen; simp at hlen; omega
  have hρτ : ρ.length + 1 = τ.length := by
    have := congrArg List.length hρ
    rw [List.length_append, List.length_singleton] at this
    omega
  have hρlen : ρ.length = c.reverse.length := by
    rw [List.length_reverse]; omega
  have hQ : gchain L W H z τ' c.reverse = gloopProd L W H z ⟨ρ, c.reverse⟩ * Gsig H z s := by
    rw [hρ, gchain_append_singleton hρlen]
  set Q := gloopProd L W H z ⟨ρ, c.reverse⟩
  have hY2 : gchain L W H z τ c = (Q * Gsig H z s)ᴴ := by
    rw [← hQ, ← hY, conjTranspose_conjTranspose]
  have hYY : (gchain L W H z τ c)ᴴ * gchain L W H z τ c
      = Q * (Gsig H z s * (Gsig H z s)ᴴ) * Qᴴ := by
    rw [hY2, conjTranspose_conjTranspose, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hW := Gsig_mul_conjTranspose (z := z) hH (isUnit_sub_smul_one_of_im_ne_zero hH hz)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz)) s
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hGG : Gsig H z s * (Gsig H z s)ᴴ
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gsig H z true - Gsig H z false) := by
    rw [← hW, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hlen2 : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * τ.length - 1 := by
    intro t; simp; omega
  have hlen3 : (c.reverse ++ (c.reverse.reverse ++ [b])).length = 2 * τ.length - 1 := by
    simp; omega
  refine ⟨_, _,
    ⟨⟨ρ ++ true :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 true, hlen3, rfl⟩,
    ⟨⟨ρ ++ false :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 false, hlen3, rfl⟩, ?_⟩
  rw [← gloopProd_Gsig_conjTranspose_Eblk hH hρlen, ← gloopProd_Gsig_conjTranspose_Eblk hH hρlen,
    hYY, hGG, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul]

omit [NeZero W] in
/-- **(6.12) as an inequality**: `W⁻² ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² ≤ (Im z)⁻¹ max|L^{(2l-1)}|`,
where `v^{(l)}` is the row `i` of a chain with `l` resolvents. -/
theorem sum_norm_gchain_row_sq_le (hH : H.IsHermitian) (hz : 0 < z.im) {ρ : List Bool}
    {b : List (Z2 L)} (h : ρ.length = b.length) (s : Bool) (a0 : Z2 L) :
    (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
        ‖gchain L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2
      ≤ (z.im)⁻¹ * loopMax L W H z (2 * ρ.length + 1) := by
  have hw := ward_chain_row' (H := H) hH hz.ne' h s a0
  set S : ℝ := (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
    ‖gchain L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hSC : (S : ℂ) = (W : ℂ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k : BlockIndex L W,
      (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ) := by
    rw [hS]
    simp only [← Complex.sq_norm]
    push_cast
    rfl
  have hlen : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * ρ.length + 1 := by
    intro t; simp; ring
  have hlen' : (b ++ (b.reverse ++ [a0])).length = 2 * ρ.length + 1 := by simp [h]; ring
  have h1 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen true) hlen'
  have h2 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen false) hlen'
  have hnc : ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz.le]
    norm_num
  calc S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
    _ = ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ * ‖gloop L W H z
          ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩‖ := by
        rw [hSC, hw, norm_mul]
    _ ≤ (2 * z.im)⁻¹ * (loopMax L W H z (2 * ρ.length + 1)
          + loopMax L W H z (2 * ρ.length + 1)) := by
        rw [hnc]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
          (by positivity)
    _ = _ := by field_simp; ring

end Ward

section Gram

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The columns `Y_{·,(b,β)}`, `β ∈ Fin W × Fin W`, of a matrix, as vectors of `ℓ²`: the vectors
`w^{(l)}_j`, `j ∈ I_b`, of (6.10). -/
noncomputable def blockCols (Y : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (b : Z2 L) :
    Fin W × Fin W → EuclideanSpace ℂ (BlockIndex L W) :=
  fun β => WithLp.toLp 2 (fun k => Y k (b, β))

/-- The selection matrix `R_{x,β} = 1(x = (b,β))` of the block `I_b`. -/
noncomputable def blockSel (b : Z2 L) : Matrix (BlockIndex L W) (Fin W × Fin W) ℂ :=
  Matrix.of fun x β => if x = (b, β) then 1 else 0

omit [NeZero W] in
theorem gram_blockCols (Y : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (b : Z2 L) :
    gram ℂ (blockCols Y b) = (blockSel b)ᵀ * (Yᴴ * Y) * blockSel b := by
  ext β β'
  simp [gram_apply, blockCols, PiLp.inner_apply, blockSel, Matrix.mul_apply, mul_comm]

omit [NeZero L] in
theorem blockSel_mul_transpose (b : Z2 L) :
    blockSel (W := W) b * (blockSel b)ᵀ = ((W : ℂ) ^ 2) • Eblk L W b := by
  ext x y
  simp only [blockSel, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Eblk,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = b
    · rw [Finset.sum_eq_single x.2]
      · simp [hx, Prod.ext_iff]
      · intro β _ hβ; simp [Prod.ext_iff, hβ.symm]
      · simp
    · simp [hx, Prod.ext_iff]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hxy)]
    simp only [mul_ite, mul_one, mul_zero]
    refine Finset.sum_eq_zero fun β _ => ?_
    split_ifs with h1 h2 <;>
      first | rfl | exact absurd (h1.trans h2.symm) hxy | exact absurd (h1.trans h2.symm).symm hxy

theorem trace_transpose_mul_mul_pow_succ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (R : Matrix m n ℂ) (K : Matrix m m ℂ) (p : ℕ) :
    trace ((Rᵀ * K * R) ^ (p + 1)) = trace ((K * (R * Rᵀ)) ^ (p + 1)) := by
  have key : ∀ p : ℕ, (Rᵀ * K * R) ^ (p + 1) = Rᵀ * ((K * (R * Rᵀ)) ^ p * K * R) := by
    intro p
    induction p with
    | zero => simp [Matrix.mul_assoc]
    | succ p ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, pow_succ]
  simp only [Matrix.mul_assoc]

/-- `tr (A^{p+1}) = (W²)^{p+1} tr ((Y†Y E_b)^{p+1})` for the Gram matrix `A` of the block
columns of `Y` (the identity behind "`(2i Im z / W²)^p tr A^p` is a sum of loops" in §6). -/
theorem trace_gram_blockCols_pow (Y : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (b : Z2 L)
    (p : ℕ) :
    trace (gram ℂ (blockCols Y b) ^ (p + 1))
      = ((W : ℂ) ^ 2) ^ (p + 1) * trace ((Yᴴ * Y * Eblk L W b) ^ (p + 1)) := by
  rw [gram_blockCols, trace_transpose_mul_mul_pow_succ, blockSel_mul_transpose, Matrix.mul_smul,
    smul_pow, trace_smul, smul_eq_mul]

omit [NeZero W] in
/-- `∑_i bw_b(i) f(i) = W⁻² ∑_{α ∈ [W]²} f(b, α)`. -/
theorem sum_bw_mul (b : Z2 L) (f : BlockIndex L W → ℝ) :
    ∑ i, bw b i * f i = (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, f (b, α) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [bw, Finset.mul_sum]
  · intro c _ hc; simp [bw, hc]
  · simp

end Gram

section Six10

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

/-- The `ℓ²` bound on the Gram matrix of (6.10): for a chain `Y` with `k` resolvents at `w`
and `p ≥ 1`, `(tr A^p)^{1/p} ≤ W² (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`. -/
theorem trace_gram_rpow_le (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) {τ : List Bool}
    {c : List (Z2 L)} (h : τ.length = c.length + 1) (b : Z2 L) {p : ℕ} (hp : 1 ≤ p) :
    (trace (gram ℂ (blockCols (gchain L W H w τ c) b) ^ p)).re ^ (1 / (p : ℝ))
      ≤ (W : ℝ) ^ 2 * (w.im)⁻¹ * loopMax L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  set Y := gchain L W H w τ c
  set LM := loopMax L W H w ((p' + 1) * (2 * τ.length - 1))
  obtain ⟨Zp, Zm, hZp, hZm, hK⟩ := exists_conjTranspose_mul_Eblk hH hw.ne' h b
  have hc : 2 * ‖(2 * Complex.I * (w.im : ℂ))⁻¹‖ ≤ (w.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hw.le]
    field_simp
    norm_num
  have hb : ‖trace ((Yᴴ * Y * Eblk L W b) ^ (p' + 1))‖ ≤ (w.im)⁻¹ ^ (p' + 1) * LM := by
    rw [hK]
    have := norm_trace_smul_sub_pow_mul_le hZp hZm hc (p' + 1) (isGLoopProd_one (L := L) (W := W)
      (H := H) (z := w))
    simpa using this
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hLM : 0 ≤ LM := loopMax_nonneg _
  have hnorm : ‖trace (gram ℂ (blockCols Y b) ^ (p' + 1))‖
      ≤ ((W : ℝ) ^ 2 * (w.im)⁻¹) ^ (p' + 1) * LM := by
    rw [trace_gram_blockCols_pow, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, mul_pow,
      mul_assoc (((W : ℝ) ^ 2) ^ (p' + 1))]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hp0 : ((p' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set x := (trace (gram ℂ (blockCols Y b) ^ (p' + 1))).re
  calc x ^ (1 / ((p' + 1 : ℕ) : ℝ)) ≤ |x ^ (1 / ((p' + 1 : ℕ) : ℝ))| := le_abs_self _
    _ ≤ |x| ^ (1 / ((p' + 1 : ℕ) : ℝ)) := Real.abs_rpow_le_abs_rpow _ _
    _ ≤ (((W : ℝ) ^ 2 * (w.im)⁻¹) ^ (p' + 1) * LM) ^ (1 / ((p' + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) ((Complex.abs_re_le_norm _).trans hnorm)
          (by positivity)
    _ = (W : ℝ) ^ 2 * (w.im)⁻¹ * LM ^ (1 / ((p' + 1 : ℕ) : ℝ)) := by
        rw [Real.mul_rpow (by positivity) hLM, one_div,
          Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- **(6.10)** summed over the rows, with the Ward identities (6.12) and (Gram).  For the
mixed chain `M = X·Y`, `X` a chain of `l` resolvents at `z` (ending in `G_l`) and `Y` a chain of
`k` resolvents at `w` (starting with `G̃_l`),
\[ \sum_{i\in I_{a_0}, j\in I_{a_m}} W^{-4}|M_{ij}|^2
    \le (\operatorname{Im} z\operatorname{Im} w)^{-1}\max|\mathcal L_z^{(2l-1)}|
      \bigl(\max|\mathcal L_w^{(p(2k-1))}|\bigr)^{1/p}. \] -/
theorem wmass_gchain_mul_gchain_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {ρ : List Bool} {b₁ : List (Z2 L)} (h₁ : ρ.length = b₁.length) (s : Bool)
    {τ : List Bool} {c : List (Z2 L)} (h₂ : τ.length = c.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (a0 am : Z2 L) :
    wmass (bw a0) (bw am) (gchain L W H z (ρ ++ [s]) b₁ * gchain L W H w τ c)
      ≤ (z.im * w.im)⁻¹ * loopMax L W H z (2 * ρ.length + 1)
        * loopMax L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  set X := gchain L W H z (ρ ++ [s]) b₁
  set Y := gchain L W H w τ c
  set M := X * Y
  set T := (trace (gram ℂ (blockCols Y am) ^ p)).re ^ (1 / (p : ℝ))
  set v : Fin W × Fin W → EuclideanSpace ℂ (BlockIndex L W) :=
    fun α => WithLp.toLp 2 (fun k => star (X (a0, α) k))
  have hinner : ∀ α β, inner ℂ (v α) (blockCols Y am β) = M (a0, α) (am, β) := by
    intro α β
    simp [v, blockCols, PiLp.inner_apply, M, Matrix.mul_apply, mul_comm]
  have hv : ∀ α, ‖v α‖ ^ 2 = ∑ k, ‖X (a0, α) k‖ ^ 2 := by
    intro α
    rw [EuclideanSpace.norm_sq_eq]
    simp [v]
  have h61 : ∀ α, ∑ β, ‖M (a0, α) (am, β)‖ ^ 2 ≤ (∑ k, ‖X (a0, α) k‖ ^ 2) * T := by
    intro α
    have := sum_norm_inner_sq_le_trace_pow (v α) (blockCols Y am) hp
    simp_rw [hinner, hv] at this
    exact this
  have hT := trace_gram_rpow_le hH hw h₂ am hp
  have hrow := sum_norm_gchain_row_sq_le (W := W) (H := H) hH hz h₁ s a0
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set LMz := loopMax L W H z (2 * ρ.length + 1)
  set LMw := loopMax L W H w (p * (2 * τ.length - 1))
  have hLMw : 0 ≤ LMw ^ (1 / (p : ℝ)) := Real.rpow_nonneg (loopMax_nonneg _) _
  have hS0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2 := by positivity
  calc wmass (bw a0) (bw am) M
      = ∑ i, bw a0 i * ∑ j, bw am j * ‖M i j‖ ^ 2 := by
        unfold wmass
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, bw a0 i * ((W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M i (am, β)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => by rw [sum_bw_mul am (fun j => ‖M i j‖ ^ 2)]
    _ = (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W,
          ((W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M (a0, α) (am, β)‖ ^ 2) :=
        sum_bw_mul a0 (fun i => (W : ℝ)⁻¹ ^ 2 * ∑ β : Fin W × Fin W, ‖M i (am, β)‖ ^ 2)
    _ ≤ (W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ((W : ℝ)⁻¹ ^ 2 * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)) := by
        gcongr with α
        exact h61 α
    _ = (W : ℝ)⁻¹ ^ 2 * ((W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2) * T := by
        have e : ∀ α : Fin W × Fin W, (W : ℝ)⁻¹ ^ 2 * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)
            = (∑ k, ‖X (a0, α) k‖ ^ 2) * ((W : ℝ)⁻¹ ^ 2 * T) := fun α => by ring
        simp_rw [e, ← Finset.sum_mul]
        ring
    _ ≤ (W : ℝ)⁻¹ ^ 2 * ((W : ℝ)⁻¹ ^ 2 * ∑ α : Fin W × Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2)
          * ((W : ℝ) ^ 2 * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (by positivity) hS0)
    _ ≤ (W : ℝ)⁻¹ ^ 2 * ((z.im)⁻¹ * LMz) * ((W : ℝ) ^ 2 * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) := by
        gcongr
    _ = (z.im * w.im)⁻¹ * LMz * LMw ^ (1 / (p : ℝ)) := by
        field_simp

end Six10

section Six11

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

/-- The `l`-th mixed chain of (6.8) satisfies the bound (6.10):
`W⁻² ∑_{i ∈ I_b, j ∈ I_{b'}} |(G_1 E ⋯ G_l G̃_l ⋯ G̃_m)_{ij}|²
  ≤ (Im z Im w)⁻¹ max|L_z^{(2l+1)}| (max|L_w^{(p(2(m-l)-1))}|)^{1/p}` (`l` counted from `0`). -/
theorem wmass_gchainMixed_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    {σ : List Bool} {a : List (Z2 L)} (h : σ.length = a.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (b' b : Z2 L) {l : ℕ} (hl : l < σ.length) :
    wmass (bw b) (bw b') (gchainMixed L W H z w σ a l)
      ≤ (z.im * w.im)⁻¹ * (loopMax L W H z (2 * l + 1)
        * loopMax L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ))) := by
  have h₁ : (σ.take l).length = (a.take l).length := by simp; omega
  have h₂ : (σ.drop l).length = (a.drop l).length + 1 := by simp; omega
  have key := wmass_gchain_mul_gchain_le (W := W) hH hz hw h₁ σ[l] h₂ hp b b'
  rw [List.take_concat_get' σ l hl] at key
  have e1 : (σ.take l).length = l := by simp; omega
  have e2 : (σ.drop l).length = σ.length - l := by simp
  rw [e1, e2] at key
  rw [gchainMixed, ← mul_assoc]
  exact key

/-- **(6.9) + (6.10) + (6.12) = (6.11)**, one symmetric loop at a time.  For a chain `C` of
`m` resolvents, the symmetric loop `⟨C E_{b'} C† E_b⟩` at `z` is bounded by the one at `w`
plus the error terms of the expansion (6.8):
\[ |\mathcal L_z| \le (m+1)\Bigl(|\mathcal L_w| + \frac{|z-w|^2}{\operatorname{Im}z\,
   \operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \] -/
theorem norm_gloop_symIdx_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {σ : List Bool} {a : List (Z2 L)} (h : σ.length = a.length + 1) {p : ℕ}
    (hp : 1 ≤ p) (b' b : Z2 L) :
    ‖gloop L W H z (symIdx σ a b' b)‖
      ≤ (σ.length + 1 : ℝ) * (‖gloop L W H w (symIdx σ a b' b)‖ + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range σ.length, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ)))) := by
  rw [gloop_symIdx hH h, gloop_symIdx hH h, norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk]
  have hent := norm_gchain_apply_sq_le (isUnit_sub_zSig hH hz.ne') (isUnit_sub_zSig hH hw.ne') h
  set u := bw (W := W) b
  set v := bw (W := W) b'
  have hu : ∀ i, 0 ≤ u i := bw_nonneg b
  have hv : ∀ j, 0 ≤ v j := bw_nonneg b'
  set m := σ.length
  set M := gchainMixed L W H z w σ a
  have hswap : ∑ l ∈ Finset.range m, wmass u v (M l)
      = ∑ i, ∑ j, u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2 := by
    unfold wmass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hmix : ∑ l ∈ Finset.range m, wmass u v (M l)
      ≤ (z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl =>
      wmass_gchainMixed_le hH hz hw h hp b' b (Finset.mem_range.mp hl)
  calc wmass u v (gchain L W H z σ a)
      ≤ ∑ i, ∑ j, u i * v j * ((m + 1 : ℝ) * (‖gchain L W H w σ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hent i j) (mul_nonneg (hu i) (hv j))
    _ = (m + 1 : ℝ) * (wmass u v (gchain L W H w σ a)
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, wmass u v (M l)) := by
        have e1 : ∀ i j, u i * v j * ((m + 1 : ℝ) * (‖gchain L W H w σ a i j‖ ^ 2
            + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2))
            = (m + 1 : ℝ) * (u i * v j * ‖gchain L W H w σ a i j‖ ^ 2)
              + ((m + 1 : ℝ) * ‖z - w‖ ^ 2) * (u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2) :=
          fun i j => by ring
        rw [hswap, wmass]
        simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ _ := by gcongr

/-- **(6.11) for the maxima**: for `m ≥ 1`, `p ≥ 1`,
\[ \max|\mathcal L_z^{(2m)}| \le (m+1)\Bigl(\max|\mathcal L_w^{(2m)}| + \frac{|z-w|^2}
   {\operatorname{Im}z\,\operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \]
Every loop of length `2m` is controlled by symmetric ones ((5.115)). -/
theorem loopMax_two_mul_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : 1 ≤ p) :
    loopMax L W H z (2 * m)
      ≤ (m + 1 : ℝ) * (loopMax L W H w (2 * m) + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)))) := by
  refine loopMax_le fun I hσ ha => norm_gloop_le_of_symIdx_le hH hm ?_ I hσ ha
  intro σ a hσ' ha' b' b
  have h : σ.length = a.length + 1 := by omega
  refine (norm_gloop_symIdx_le_tilde hH hz hw h hp b' b).trans ?_
  rw [hσ']
  gcongr
  have := norm_gloop_symIdx_le_loopMax (W := W) (H := H) (z := w) h b' b
  rwa [hσ'] at this

end Six11

end RBM.Ind
