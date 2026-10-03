/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.EntryCore
import RBM2D.Green.Stability
import RBM2D.Green.Pins

/-!
# Entry estimates for the Green's function: the `d = 2` block model

The block part of the one-dimensional entry estimates, in `d = 2`: the profile lives on
`BlockIndex L W = Z_L² × {0,…,W-1}²`, `S = S^{(B)} ⊗ S_W` with `S^{(B)} = (1/5) 1(|a-b|_L ≤ 1)` and
`S_W = W⁻²` (Section 1, the definition of `S`), the block weights are those of
`Def_matE` (`W⁻² 1(x ∈ 𝓘_a)`), and the loops are `loopPM`, `maxLoopPM`, `gexRHS`.  The
stability constant is `Kstab2` (`stable_svar`, `stable_svar_bulk`) in place of `Kstab`.
The paper does not restate (4.2), (4.3), (4.5): it says that the proof of `lem_GbEXP`
follows Lemma 4.2 of [YY_25].

Contents:
1. the resolvent helpers `green_mul_sub_of_im`, `sub_mul_green_of_im`, `zt_im_ne_zero`,
   `mE_mul_add_zt` (with `zt`, `mE` read as `spectralZ`, `spectralM`);
2. the profile `Sblk2` and its bridge to `svar`; stability of `1 - t m² Sblk2`;
3. the neighbour sums of `∑_{k,l} S_{pk} |G_{kl}|² S_{lq}` and their bound by `maxLoopPM`;
4. (4.2) block form (`offSq_le_gexRHS_blk`, the swapped pair);
5. the lower bounds `W⁻² ≤ 4 maxLoopPM`, `S ≤ 2 maxLoopPM`;
6. (4.3) block form (`diagSq_le_maxLoopPM_blk`);
7. (4.5): `blkCoef2` and `avgErr = ∑_k blkCoef2 (G_kk - m)` and the bound.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open Matrix Finset RBM RBM.Gauss RBM.Path

/-! ## 1. Resolvent helpers -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `G (H - z) = 1` for Hermitian `H` and `Im z ≠ 0`; the invertibility is
`RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero`. -/
theorem green_mul_sub_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  green_mul_self (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz))

/-- `(H - z) G = 1` for Hermitian `H` and `Im z ≠ 0`. -/
theorem sub_mul_green_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  self_mul_green (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz))

end Resolvent

/-- `z_t` has nonzero imaginary part, with `z_t = spectralZ E t`. -/
theorem zt_im_ne_zero {E κ t : ℝ} (hκ0 : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t < 1) :
    (spectralZ E t).im ≠ 0 := by
  rw [spectralZ_im]
  have h := spectralM_im_pos (E := E) (by linarith [abs_nonneg E])
  have : 0 < 1 - t := by linarith
  positivity

/-- `m = -(t m + z_t)⁻¹`, with `m = spectralM E`, `z_t = spectralZ E t`. -/
theorem mE_mul_add_zt {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    spectralM E * ((t : ℂ) * spectralM E + spectralZ E t) = -1 := by
  have h := spectralM_mul hE
  rw [spectralZ]
  linear_combination h

/-! ## 2. The profile on `BlockIndex` -/

section Profile

variable (L W : ℕ)

/-- The kernel of `S^{(B)}` as a real function: `1/5` on `sbSupport`, zero elsewhere
(`sbKernel` over `ℝ`). -/
noncomputable def sbKre2 (u : Z2 L) : ℝ := if u ∈ sbSupport L then 1 / 5 else 0

/-- The variance profile `S = S^{(B)} ⊗ S_W` on the block/offset index `BlockIndex L W`:
`S_{(a,α),(b,β)} = (1/5) 1(a - b ∈ sbSupport) W⁻²` (Section 1, the definition of `S`), with the
block weight `W⁻²` of `S_W`. -/
noncomputable def Sblk2 (p q : BlockIndex L W) : ℝ := sbKre2 L (p.1 - q.1) * ((W : ℝ)⁻¹) ^ 2

variable {L W}

theorem sbKre2_nonneg (u : Z2 L) : 0 ≤ sbKre2 L u := by
  unfold sbKre2; split_ifs <;> norm_num

theorem sbKre2_le (u : Z2 L) : sbKre2 L u ≤ 1 / 5 := by
  unfold sbKre2; split_ifs <;> norm_num

theorem sbKre2_neg (u : Z2 L) : sbKre2 L (-u) = sbKre2 L u := by
  unfold sbKre2
  exact if_congr (neg_mem_sbSupport L) rfl rfl

private theorem sbKernel_eq_sbKre2 (u : Z2 L) : sbKernel L u = (sbKre2 L u : ℂ) := by
  unfold sbKernel sbKre2
  split_ifs <;> push_cast <;> ring

variable [NeZero L]

/-- `sbKre2` is zero off `sbSupport`, and hence at most `1` on the nearest-neighbour ball. -/
private theorem sbKre2_le_ind (u : Z2 L) (hL : 3 ≤ L) :
    sbKre2 L u ≤ if zdist2 L u ≤ 1 then 1 else 0 := by
  unfold sbKre2
  split_ifs with h1 h2
  · norm_num
  · exact absurd (zdist2_le_one_of_mem_sbSupport L hL h1) h2
  · norm_num
  · exact le_rfl

theorem sum_sbKre2 (hL : 3 ≤ L) : ∑ u : Z2 L, sbKre2 L u = 1 := by
  have h := sum_sbKernel L hL
  simp only [sbKernel_eq_sbKre2] at h
  exact_mod_cast h

theorem sum_sbKre2_sub_left (hL : 3 ≤ L) (a : Z2 L) : ∑ b : Z2 L, sbKre2 L (a - b) = 1 := by
  rw [← sum_sbKre2 hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl

theorem sum_sbKre2_sub_right (hL : 3 ≤ L) (b : Z2 L) : ∑ a : Z2 L, sbKre2 L (a - b) = 1 := by
  rw [← sum_sbKre2 hL]
  exact Fintype.sum_equiv (Equiv.subRight b) _ _ fun a => rfl

omit [NeZero L] in
theorem Sblk2_nonneg (p q : BlockIndex L W) : 0 ≤ Sblk2 L W p q :=
  mul_nonneg (sbKre2_nonneg _) (by positivity)

omit [NeZero L] in
theorem Sblk2_le (p q : BlockIndex L W) : Sblk2 L W p q ≤ 1 / 5 * ((W : ℝ)⁻¹) ^ 2 :=
  mul_le_mul_of_nonneg_right (sbKre2_le _) (by positivity)

omit [NeZero L] in
/-- `S_{pq}` vanishes unless `p.1 - q.1 ∈ sbSupport`, where it is `≤ W⁻²`. -/
private theorem Sblk2_le_ind (p q : BlockIndex L W) :
    Sblk2 L W p q ≤ if p.1 - q.1 ∈ sbSupport L then ((W : ℝ)⁻¹) ^ 2 else 0 := by
  unfold Sblk2 sbKre2
  split_ifs
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg ((W : ℝ)⁻¹)]
  · simp

variable [NeZero W]

theorem sum_Sblk2_row (hL : 3 ≤ L) (p : BlockIndex L W) : ∑ q, Sblk2 L W p q = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type]
  simp only [Sblk2, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  have : ∀ b : Z2 L, ((W * W : ℕ) : ℝ) * (sbKre2 L (p.1 - b) * ((W : ℝ)⁻¹) ^ 2)
      = sbKre2 L (p.1 - b) := fun b => by
    push_cast; field_simp
  simp only [this]
  exact sum_sbKre2_sub_left hL p.1

theorem sum_Sblk2_col (hL : 3 ≤ L) (q : BlockIndex L W) : ∑ p, Sblk2 L W p q = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type]
  simp only [Sblk2, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  have : ∀ a : Z2 L, ((W * W : ℕ) : ℝ) * (sbKre2 L (a - q.1) * ((W : ℝ)⁻¹) ^ 2)
      = sbKre2 L (a - q.1) := fun a => by
    push_cast; field_simp
  simp only [this]
  exact sum_sbKre2_sub_right hL q.1

end Profile

/-! ### The bridge to `svar` and stability -/

section Bridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The profile on `BlockIndex` is `svar` (`Gauss/Model.lean`, the profile on `Z_{WL}²`) read
through `splitEquiv`. -/
theorem Sblk2_eq_svar (p q : BlockIndex L W) :
    Sblk2 L W p q = svar L W ((splitEquiv L W).symm p) ((splitEquiv L W).symm q) := by
  have hp : (blk L W ((splitEquiv L W).symm p).1, blk L W ((splitEquiv L W).symm p).2) = p.1 :=
    congrArg Prod.fst ((splitEquiv L W).apply_symm_apply p)
  have hq : (blk L W ((splitEquiv L W).symm q).1, blk L W ((splitEquiv L W).symm q).2) = q.1 :=
    congrArg Prod.fst ((splitEquiv L W).apply_symm_apply q)
  unfold Sblk2 sbKre2 svar
  rw [hp, hq]
  split_ifs <;> ring

/-- `Stable` is invariant under relabelling the index set. -/
theorem stable_relabel {n n' : Type*} [Fintype n] [Fintype n'] (e : n ≃ n') {S : n → n → ℝ}
    {ξ : ℂ} {K : ℝ} (h : Stable S ξ K) :
    Stable (fun i j => S (e.symm i) (e.symm j)) ξ K := by
  intro v B hB i
  have h1 := h (fun k => v (e k)) B (fun j => by
    have h2 := hB (e j)
    have h3 : ∑ k', (S (e.symm (e j)) (e.symm k') : ℂ) * v k' = ∑ k, (S j k : ℂ) * v (e k) := by
      rw [← Equiv.sum_comp e]
      simp
    rw [h3] at h2
    simpa using h2) (e.symm i)
  simpa using h1

/-- `‖(1 - t m² S)⁻¹‖_{max→max} ≤ Kstab2 κ L` for the block profile `Sblk2` (`stable_svar_bulk`,
transported through `splitEquiv`). -/
theorem stable_Sblk2_bulk (hL : 3 ≤ L) {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (Sblk2 L W) ((t : ℂ) * spectralM E ^ 2) (Kstab2 κ L) := by
  have h := stable_relabel (splitEquiv L W) (stable_svar_bulk (W := W) hL hκ hE ht0 ht1)
  have hfun : (fun p q : BlockIndex L W =>
      svar L W ((splitEquiv L W).symm p) ((splitEquiv L W).symm q)) = Sblk2 L W :=
    funext fun p => funext fun q => (Sblk2_eq_svar p q).symm
  rwa [hfun] at h

end Bridge

/-! ## 3. The neighbour sums -/

section Loops

variable {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- The two-sided sum in (4.11) is a weighted sum of `2`-loops: with the orientation of
`norm_loopPM_eq` (rows in block `b`, columns in block `a`),
`∑_{k,l} S_{pk}|G_{kl}|²S_{lq} = ∑_{a',b'} S^{(B)}_{[p]a'} S^{(B)}_{b'[q]} ‖𝓛_{(+,-),(b',a')}‖`
(with `‖loopPM‖` for the norm of the loop). -/
theorem sum_sum_Sblk2_eq (hM : M.IsHermitian) (p q : BlockIndex L W) :
    ∑ k, ∑ l, Sblk2 L W p k * ‖greenBlk L W E u M true k l‖ ^ 2 * Sblk2 L W l q
      = ∑ a' : Z2 L, ∑ b' : Z2 L,
          sbKre2 L (p.1 - a') * sbKre2 L (b' - q.1) * ‖loopPM L W E u M b' a'‖ := by
  simp only [Fintype.sum_prod_type (α₁ := Z2 L) (α₂ := Fin W × Fin W)]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [norm_loopPM_eq M hM b' a']
  simp only [Sblk2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

private theorem norm_loopPM_le_maxLoopPM (a b : Z2 L) :
    ‖loopPM L W E u M a b‖ ≤ maxLoopPM L W E u M :=
  Finset.le_sup' (fun p : Z2 L × Z2 L => ‖loopPM L W E u M p.1 p.2‖) (Finset.mem_univ (a, b))

/-- `∑_{k,l} S_{pk}|G_{kl}|²S_{lq} ≤ max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`. -/
theorem sum_sum_Sblk2_le_maxLoopPM (hL : 3 ≤ L) (hM : M.IsHermitian) (p q : BlockIndex L W) :
    ∑ k, ∑ l, Sblk2 L W p k * ‖greenBlk L W E u M true k l‖ ^ 2 * Sblk2 L W l q
      ≤ maxLoopPM L W E u M := by
  rw [sum_sum_Sblk2_eq hM]
  calc ∑ a' : Z2 L, ∑ b' : Z2 L,
        sbKre2 L (p.1 - a') * sbKre2 L (b' - q.1) * ‖loopPM L W E u M b' a'‖
      ≤ ∑ a' : Z2 L, ∑ b' : Z2 L,
        sbKre2 L (p.1 - a') * sbKre2 L (b' - q.1) * maxLoopPM L W E u M :=
        Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
          mul_le_mul_of_nonneg_left (norm_loopPM_le_maxLoopPM b' a')
            (mul_nonneg (sbKre2_nonneg _) (sbKre2_nonneg _))
    _ = (∑ a' : Z2 L, sbKre2 L (p.1 - a')) * (∑ b' : Z2 L, sbKre2 L (b' - q.1)) *
          maxLoopPM L W E u M := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_mul]
    _ = maxLoopPM L W E u M := by rw [sum_sbKre2_sub_left hL, sum_sbKre2_sub_right hL]; ring

end Loops

/-! ## 4. (4.2) in block form -/

section BlockForms

variable {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem greenBlk_true_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    greenBlk L W E u M true = green (blockMat M) (spectralZ E u) := by
  simp [greenBlk]

private theorem blockMat_isHermitian (hM : M.IsHermitian) : (blockMat M).IsHermitian :=
  hM.submatrix _

private theorem greenBlk_mul_sub (hM : M.IsHermitian) (hz : (spectralZ E u).im ≠ 0) :
    greenBlk L W E u M true * (blockMat M - spectralZ E u •
      (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) = 1 := by
  rw [greenBlk_true_eq]
  exact green_mul_sub_of_im (blockMat_isHermitian hM) hz

private theorem sub_mul_greenBlk (hM : M.IsHermitian) (hz : (spectralZ E u).im ≠ 0) :
    (blockMat M - spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
      greenBlk L W E u M true = 1 := by
  rw [greenBlk_true_eq]
  exact sub_mul_green_of_im (blockMat_isHermitian hM) hz

omit [NeZero L] in
private theorem sbKre2_sub_comm (a b : Z2 L) : sbKre2 L (a - b) = sbKre2 L (b - a) := by
  rw [← neg_sub b a, sbKre2_neg]

private theorem sbKre2_mul_mul_le (hL : 3 ≤ L) (x y : Z2 L) {n : ℝ} (hn : 0 ≤ n) :
    sbKre2 L x * sbKre2 L y * n ≤ if zdist2 L x ≤ 1 ∧ zdist2 L y ≤ 1 then n else 0 := by
  have hx := sbKre2_le_ind x hL
  have hy := sbKre2_le_ind y hL
  have hx0 := sbKre2_nonneg x
  have hy0 := sbKre2_nonneg y
  by_cases h : zdist2 L x ≤ 1 ∧ zdist2 L y ≤ 1
  · rw [ite_eq_left h]
    have h1 := sbKre2_le x
    have h2 := sbKre2_le y
    have h3 : sbKre2 L x * sbKre2 L y ≤ 1 := by nlinarith
    calc sbKre2 L x * sbKre2 L y * n ≤ 1 * n := mul_le_mul_of_nonneg_right h3 hn
      _ = n := one_mul n
  · rw [ite_eq_right h]
    have h0 : sbKre2 L x * sbKre2 L y = 0 := by
      by_cases h1 : zdist2 L x ≤ 1
      · have h2 : ¬ zdist2 L y ≤ 1 := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_right h2] at hy
        rw [le_antisymm hy hy0, mul_zero]
      · rw [ite_eq_right h1] at hx
        rw [le_antisymm hx hx0, zero_mul]
    rw [h0, zero_mul]

/-- The double sum is bounded by the double sum of `gexRHS … q.1 p.1` (the swapped pair):
each `S^{(B)}` factor is `≤ 1` and vanishes off the ball `|·|_L ≤ 1`. -/
private theorem sum_sum_Sblk2_le_gexRHS (hL : 3 ≤ L) (hM : M.IsHermitian) (p q : BlockIndex L W) :
    ∑ k, ∑ l, Sblk2 L W p k * ‖greenBlk L W E u M true k l‖ ^ 2 * Sblk2 L W l q
      ≤ ∑ a' : Z2 L, ∑ b' : Z2 L,
          if zdist2 L (a' - q.1) ≤ 1 ∧ zdist2 L (b' - p.1) ≤ 1
          then ‖loopPM L W E u M a' b'‖ else 0 := by
  rw [sum_sum_Sblk2_eq hM, Finset.sum_comm]
  refine Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun a' _ => ?_
  have h := sbKre2_mul_mul_le hL (b' - q.1) (a' - p.1) (norm_nonneg (loopPM L W E u M b' a'))
  rw [sbKre2_sub_comm p.1 a']
  calc _ = sbKre2 L (b' - q.1) * sbKre2 L (a' - p.1) * ‖loopPM L W E u M b' a'‖ := by ring
    _ ≤ _ := h

omit [NeZero W] in
/-- The diagonal-block term `S_{pq} ≤ W⁻² 1(|[q]-[p]|_L ≤ 1)`. -/
private theorem Sblk2_le_gexRHS_ind (hL : 3 ≤ L) (p q : BlockIndex L W) :
    Sblk2 L W p q ≤ if zdist2 L (q.1 - p.1) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0 := by
  have h := Sblk2_le_ind p q
  refine h.trans ?_
  by_cases hs : p.1 - q.1 ∈ sbSupport L
  · have hs' : q.1 - p.1 ∈ sbSupport L := by
      rw [← neg_sub p.1 q.1, neg_mem_sbSupport]; exact hs
    rw [ite_eq_left hs, ite_eq_left (zdist2_le_one_of_mem_sbSupport L hL hs'), inv_pow]
  · rw [ite_eq_right hs]
    split_ifs <;> positivity

/-- **(4.2)**, deterministic block form (the two-sided bound of `norm_sq_green_le_two_sided` with
`S = Sblk2`): on the good event, for all blocks-and-offsets `p, q`,
`|G_{pq}|² ≤ 81 Φ² · gexRHS … [q] [p]` (the swapped pair; `offSq` is `0` on the diagonal).
The constant `81` is kept: `1/25 ≤ 1` and `1/5 ≤ 1`. -/
theorem offSq_le_gexRHS_blk (hL : 3 ≤ L) (hM : M.IsHermitian) (hE : |E| ≤ 2)
    (hz : (spectralZ E u).im ≠ 0) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E u M true) (spectralM E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow (blockMat M) (greenBlk L W E u M true) (Sblk2 L W) Φ)
    (hLcol : LDECol (blockMat M) (greenBlk L W E u M true) (Sblk2 L W) Φ)
    (p q : BlockIndex L W) :
    offSq L W E u M p q ≤ 81 * Φ ^ 2 * gexRHS L W E u M q.1 p.1 := by
  by_cases hpq : p = q
  · simp only [offSq, ite_eq_left hpq]
    exact mul_nonneg (by positivity) (gexRHS_nonneg E u M _ _)
  · simp only [offSq, ite_eq_right hpq]
    have hm := norm_spectralM hE
    have h := norm_sq_green_le_two_sided (greenBlk_mul_sub hM hz) (sub_mul_greenBlk hM hz) hm hΩ
      hδ (fun i k => Sblk2_nonneg i k) (fun i => (sum_Sblk2_row hL i).le)
      (fun j => (sum_Sblk2_col hL j).le) hΦ1 hΦδ hLrow hLcol hpq
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add (sum_sum_Sblk2_le_gexRHS hL hM p q) (Sblk2_le_gexRHS_ind hL p q)

/-! ## 5. Lower bounds on `maxLoopPM` -/

/-- On the good event, `W⁻² ≤ 4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`: the diagonal entries alone
contribute `≥ W⁻²/4` to `𝓛_{(+,-),(0,0)}`; the block size is `W²`. -/
theorem inv_W2_le_maxLoopPM (hM : M.IsHermitian) (hE : |E| ≤ 2) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E u M true) (spectralM E) δ) (hδ : δ ≤ 1 / 2) :
    ((W : ℝ)⁻¹) ^ 2 ≤ 4 * maxLoopPM L W E u M := by
  have hm := norm_spectralM hE
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : ((W : ℝ)⁻¹) ^ 2 / 4 ≤ ‖loopPM L W E u M 0 0‖ := by
    rw [norm_loopPM_eq M hM 0 0]
    have hdiag : ∀ β : Fin W × Fin W, (1 : ℝ) / 4 ≤
        ∑ α : Fin W × Fin W, ‖greenBlk L W E u M true ((0 : Z2 L), β) (0, α)‖ ^ 2 := by
      intro β
      have h2 := hΩ.half_le_norm_diag hm hδ ((0 : Z2 L), β)
      have h3 : (1 : ℝ) / 4 ≤ ‖greenBlk L W E u M true ((0 : Z2 L), β) (0, β)‖ ^ 2 := by
        nlinarith
      exact h3.trans (Finset.single_le_sum
        (f := fun α => ‖greenBlk L W E u M true ((0 : Z2 L), β) (0, α)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ β))
    have h4 : ((W : ℝ) ^ 2) * (1 / 4) ≤ ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,
        ‖greenBlk L W E u M true ((0 : Z2 L), β) (0, α)‖ ^ 2 := by
      calc ((W : ℝ) ^ 2) * (1 / 4) = ∑ _β : Fin W × Fin W, (1 : ℝ) / 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast; ring
        _ ≤ _ := Finset.sum_le_sum fun β _ => hdiag β
    calc ((W : ℝ)⁻¹) ^ 2 / 4 = (((W : ℝ)⁻¹) ^ 2) ^ 2 * (((W : ℝ) ^ 2) * (1 / 4)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h5 := norm_loopPM_le_maxLoopPM (E := E) (u := u) (M := M) (0 : Z2 L) 0
  linarith

/-- On the good event, `S_{pq} ≤ (1/5) W⁻² ≤ 2 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`. -/
theorem Sblk2_le_maxLoopPM (hM : M.IsHermitian) (hE : |E| ≤ 2) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E u M true) (spectralM E) δ) (hδ : δ ≤ 1 / 2)
    (p q : BlockIndex L W) : Sblk2 L W p q ≤ 2 * maxLoopPM L W E u M := by
  have h1 := Sblk2_le (L := L) (W := W) p q
  have h2 := inv_W2_le_maxLoopPM hM hE hΩ hδ
  have h3 := maxLoopPM_nonneg (L := L) (W := W) E u M
  linarith

/-! ## 6. (4.3) in block form -/

/-- **(4.3)**, deterministic block form: on the good event, given the LDE inputs and the
absorption `Kstab2 κ L · δ ≤ 1/2`,
`|G_{pp} - m|² ≤ 2160 · Kstab2² · Φ² · (2 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖)`; the hypothesis `κ ≤ 1`
is not needed (`stable_svar_bulk` does not use it). -/
theorem diagSq_le_maxLoopPM_blk (hL : 3 ≤ L) (hM : M.IsHermitian) {κ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E u M true) (spectralM E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hKδ : Kstab2 κ L * δ ≤ 1 / 2)
    (hLrow : LDERow (blockMat M) (greenBlk L W E u M true) (Sblk2 L W) Φ)
    (hLcol : LDECol (blockMat M) (greenBlk L W E u M true) (Sblk2 L W) Φ)
    (hLquad : LDEQuad (blockMat M) (greenBlk L W E u M true) (Sblk2 L W) u Φ)
    (hLdiag : ∀ i, ‖blockMat M i i‖ ^ 2 ≤ Φ * Sblk2 L W i i) (p : BlockIndex L W) :
    diagSq L W E u M p ≤ 2160 * Kstab2 κ L ^ 2 * Φ ^ 2 * (2 * maxLoopPM L W E u M) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hz := zt_im_ne_zero hκ hE hu1
  have hm := norm_spectralM hE2
  have hL0 := maxLoopPM_nonneg (L := L) (W := W) E u M
  have h := norm_sq_green_diag_sub_le (greenBlk_mul_sub hM hz) (sub_mul_greenBlk hM hz) hm
    (mE_mul_add_zt hE2 u) hu0 hu1.le hΩ hδ (fun i k => Sblk2_nonneg i k) (sum_Sblk2_row hL)
    (fun j => (sum_Sblk2_col hL j).le) hΦ1 hΦδ hLrow hLcol hLquad hLdiag
    (Λ := 2 * maxLoopPM L W E u M)
    (fun i j => (sum_sum_Sblk2_le_maxLoopPM hL hM i j).trans (by linarith))
    (Sblk2_le_maxLoopPM hM hE2 hΩ hδ) hKδ (stable_Sblk2_bulk hL hκ hE hu0 hu1) p
  exact h

end BlockForms

/-! ## 7. (4.5): the coefficients `W⁻² 1(k ∈ 𝓘_a)` and the bound -/

section Coef

variable {L W : ℕ}

/-- The coefficients `c_k = W⁻² 1(k ∈ 𝓘_a)` used for (4.5): the entries of `E_a`
(`Def_matE`), with the block weight `W⁻²` of `d = 2`. -/
noncomputable def blkCoef2 (L W : ℕ) (a : Z2 L) (k : BlockIndex L W) : ℝ :=
  if k.1 = a then ((W : ℝ)⁻¹) ^ 2 else 0

/-- The weights sum to `1`: a block has `W²` sites of weight `W⁻²`. -/
theorem sum_abs_blkCoef2 [NeZero L] [NeZero W] (a : Z2 L) : ∑ k, |blkCoef2 L W a k| = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [blkCoef2, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    field_simp
  · intro b _ hb
    simp [blkCoef2, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The weights `W⁻² 1(k ∈ 𝓘_a)` are non-negative and sum to `1`. -/
theorem sum_blkCoef2 [NeZero L] [NeZero W] (a : Z2 L) : ∑ k, blkCoef2 L W a k = 1 := by
  rw [← sum_abs_blkCoef2 (W := W) a]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [abs_of_nonneg]
  unfold blkCoef2
  split_ifs <;> positivity

/-- `⟨(G - m) E_a⟩ = ∑_k c_k (G_{kk} - m)` with `c_k = W⁻² 1(k ∈ 𝓘_a)`. -/
theorem trace_sub_mul_Eblk2 [NeZero L] [NeZero W] (G : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (m : ℂ) (a : Z2 L) :
    Matrix.trace ((G - m • (1 : Matrix _ _ ℂ)) * Eblk L W a)
      = ∑ k, (blkCoef2 L W a k : ℂ) * (G k k - m) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Eblk, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, blkCoef2]
  split_ifs <;> push_cast <;> ring

/-- The `avgErr` at the sign `+` is the trace form of (4.5) (`KLoop.mSig E true = m`). -/
private theorem avgErr_true_eq_trace [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (a : Z2 L) :
    avgErr L W E u M true a
      = Matrix.trace ((greenBlk L W E u M true - spectralM E • (1 : Matrix _ _ ℂ)) *
          Eblk L W a) := by
  simp [avgErr, KLoop.mSig]

variable [NeZero L] [NeZero W]

/-- **(4.5)**, deterministic block form.  With `x_k` standing for `E_k(G_{kk} - m)`: if
`x_i = t m² ∑_k S_{ik} (G_{kk} - m) + O(A)` and the fluctuation
averaging holds with error `B` for the weights `S_{ik}` and `B'` for the weights
`c_k = W⁻² 1(k ∈ 𝓘_a)`, then `|⟨(G - m)E_a⟩| ≤ B' + Kstab2 κ L · (A + B)`.  Here `Kstab2 κ L`
replaces the one-dimensional `Kstab κ`, and `κ ≤ 1` is not needed. -/
theorem norm_trace_green_sub_mul_Eblk2_le (hL : 3 ≤ L) {E κ t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (G : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (x : BlockIndex L W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (t : ℂ) * spectralM E ^ 2 *
      ∑ k, (Sblk2 L W i k : ℂ) * (G k k - spectralM E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (Sblk2 L W i k : ℂ) * ((G k k - spectralM E) - x k)‖ ≤ B) (a : Z2 L)
    (hFA' : ‖∑ k, (blkCoef2 L W a k : ℂ) * ((G k k - spectralM E) - x k)‖ ≤ B') :
    ‖Matrix.trace ((G - spectralM E • (1 : Matrix _ _ ℂ)) * Eblk L W a)‖
      ≤ B' + Kstab2 κ L * (A + B) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * spectralM E ^ 2‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_spectralM hE2, Complex.norm_real, Real.norm_of_nonneg ht0,
      one_pow, mul_one]
    exact ht1.le
  rw [trace_sub_mul_Eblk2]
  exact norm_sum_coef_green_sub_le hξ (stable_Sblk2_bulk hL hκ hE ht0 ht1) x hIBP hFA
    (sum_abs_blkCoef2 a).le hFA'

/-- The `avgErr` form of (4.5): the same bound for `avgErr L W E u M true a`, with
`G = greenBlk L W E u M true`. -/
theorem norm_avgErr_le (hL : 3 ≤ L) {E κ u : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (x : BlockIndex L W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (u : ℂ) * spectralM E ^ 2 *
      ∑ k, (Sblk2 L W i k : ℂ) * (greenBlk L W E u M true k k - spectralM E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (Sblk2 L W i k : ℂ) *
      ((greenBlk L W E u M true k k - spectralM E) - x k)‖ ≤ B) (a : Z2 L)
    (hFA' : ‖∑ k, (blkCoef2 L W a k : ℂ) *
      ((greenBlk L W E u M true k k - spectralM E) - x k)‖ ≤ B') :
    ‖avgErr L W E u M true a‖ ≤ B' + Kstab2 κ L * (A + B) := by
  rw [avgErr_true_eq_trace]
  exact norm_trace_green_sub_mul_Eblk2_le hL hκ hE hu0 hu1 (greenBlk L W E u M true) x hIBP hFA a
    hFA'

end Coef

end RBM.Green
