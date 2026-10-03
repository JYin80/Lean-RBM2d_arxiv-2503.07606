/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.RowIndep
import RBM2D.Green.EntryDom

/-!
# The large deviation inputs of Lemma 4.2 of [YY_25] for the Gaussian flow

The paper does not state these inputs (Section "Estimates for entries of `G`" refers to
Lemma 4.2 of [YY_25]); for the Gaussian flow they are elementary.

The three produced statements have, as conclusions, the text of the hypotheses `hLrow`, `hLcol`,
`hLdiag` of `entry_bound_stochDom` and `diag_bound_stochDom` (`Green/EntryDom.lean`).

* `im_green_diag`, `green_diag_ne_zero`, `isUnit_det_Hflow_sub`, `green_Hflow_diag_ne_zero`:
  the side conditions of the minor formula hold for every `ω` when `Im z ≠ 0`;
* `minorRowConj_eq_greenMinor`, `ldeColLHS_eq`, `rowVarSum_minorRowConj_eq`: the column sum is
  the conjugate of a row sum;
* `stochDom_ldeRow`, `stochDom_ldeCol`: `hLrow`, `hLcol`;
* `Sblk_diag_pos`, `integral_pow_coord`, `integrable_pow_coord`, `normSq_Hflow_diag`,
  `integral_norm_Hflow_diag_pow`, `integrable_norm_Hflow_diag_pow`, `eventually_card_Idx_le`,
  `stochDom_normSq_Hflow_diag`: the diagonal input `hLdiag`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
open scoped ComplexOrder NNReal ENNReal

/-! ### The diagonal Green function never vanishes off the real axis -/

section GreenDiag

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

private theorem LDE_isUnit_det {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (H - z • (1 : Matrix ν ν ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_sub_smul_one_of_im_ne_zero hH hz)

/-- **The Ward identity at one site.**  For Hermitian `H` and `Im z ≠ 0`, writing
`v = G e_i`, we have `Im G_{ii} = Im z · ‖v‖²`. -/
theorem im_green_diag {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) :
    (green H z i i).im
      = z.im * (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := LDE_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hvi : v i = green H z i i := by
    rw [hv]; simp
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hsplit : star v ⬝ᵥ ((H - z • (1 : Matrix ν ν ℂ)) *ᵥ v)
      = star v ⬝ᵥ (H *ᵥ v) - z * (star v ⬝ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hMv, dotProduct_single_one] at hsplit
  have hHim : (star v ⬝ᵥ H *ᵥ v).im = 0 := by
    simpa [RCLike.im_to_complex] using hH.im_star_dotProduct_mulVec_self v
  have hself : (star v ⬝ᵥ v).im = 0 := by
    have := dotProduct_star_self_nonneg v
    rw [Complex.le_def] at this
    exact this.2.symm
  have := congrArg Complex.im hsplit
  rw [Complex.sub_im, hHim, Complex.mul_im, hself] at this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_im, hvi] at this
  linarith [this]

/-- **`G_{ii} ≠ 0`.**  For Hermitian `H` and `Im z ≠ 0` the diagonal Green function is never
zero. -/
theorem green_diag_ne_zero {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : ν) : green H z i i ≠ 0 := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := LDE_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hMv
    have h1 := congrFun hMv i
    simp at h1
  have hpos : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hvne
  rw [Complex.lt_def] at hpos
  have hre : (0 : ℝ) < (star v ⬝ᵥ v).re := by simpa using hpos.1
  intro hzero
  have him := im_green_diag hH hz i
  rw [hzero] at him
  simp only [Complex.zero_im] at him
  have : z.im = 0 := by
    rcases mul_eq_zero.1 him.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hre)
  exact hz this

end GreenDiag

section SideConditions

variable {d : Sizes} {n : ℕ} {u : ℝ} {z : ℂ}

/-! ### The side conditions hold for every `ω` -/

theorem isUnit_det_Hflow_sub (d : Sizes) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d) (hz : z.im ≠ 0) :
    IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det :=
  LDE_isUnit_det (Sizes.seqHflow_isHermitian d n u ω) hz

theorem green_Hflow_diag_ne_zero (d : Sizes) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d)
    (hz : z.im ≠ 0) (x : Idx (d.L n) (d.W n)) :
    green (Sizes.seqHflow d n u ω) z x x ≠ 0 :=
  green_diag_ne_zero (Sizes.seqHflow_isHermitian d n u ω) hz x

/-! ### The column LDE: the conjugated minor row -/

/-- Where the resolvent exists, the coefficients `minorRowConj` are the conjugated entries of
`G^{(j)}`. -/
theorem minorRowConj_eq_greenMinor (u : ℝ) {j : Idx (d.L n) (d.W n)}
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j}) {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow d n u ω) z j j ≠ 0) {l : Idx (d.L n) (d.W n)} (hl : l ≠ j) :
    minorRowConj d n u z j k ω l
      = (starRingEnd ℂ) (greenMinor (green (Sizes.seqHflow d n u ω) z) j k.1 l) := by
  unfold minorRowConj
  rw [dite_eq_left_of_eq_true (by simpa using hl), inv_minor_resolvent hdet j hGjj]
  rfl

/-- **The left-hand side of the column LDE** is the row sum with the conjugated minor row. -/
theorem ldeColLHS_eq (u : ℝ) {j : Idx (d.L n) (d.W n)}
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j}) {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow d n u ω) z j j ≠ 0) :
    ldeColLHS (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z) k.1 j
      = ‖rowSum d n u j (minorRowConj d n u z j k) ω‖ ^ 2 := by
  have key : rowSum d n u j (minorRowConj d n u z j k) ω
      = (starRingEnd ℂ) (∑ l ∈ Finset.univ.erase j,
          greenMinor (green (Sizes.seqHflow d n u ω) z) j k.1 l * Sizes.seqHflow d n u ω l j) := by
    unfold rowSum
    rw [map_sum, Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
      (fun l => by simp [Finset.mem_erase]) _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, map_mul,
      show (starRingEnd ℂ) (Sizes.seqHflow d n u ω l.1 j) = Sizes.seqHflow d n u ω j l.1 from
        (Sizes.seqHflow_isHermitian d n u ω).apply j l.1]
    ring
  rw [key, Complex.norm_conj, ldeColLHS]

/-- **The right-hand side of the column LDE** is the variance of that row sum, up to the factor
`u` (using `svar_comm`). -/
theorem rowVarSum_minorRowConj_eq (u : ℝ) {j : Idx (d.L n) (d.W n)}
    (k : {a : Idx (d.L n) (d.W n) // a ≠ j}) {ω : Sizes.SeqΩ d}
    (hdet : IsUnit (Sizes.seqHflow d n u ω - z • (1 : Matrix (Idx (d.L n) (d.W n))
      (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow d n u ω) z j j ≠ 0) :
    rowVarSum d n u j (minorRowConj d n u z j k) ω
      = u * ldeColRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) k.1 j := by
  unfold rowVarSum ldeColRHS
  congr 1
  rw [Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
    (fun l => by simp [Finset.mem_erase]) _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, Complex.norm_conj,
    svar_comm (d.L n) (d.W n) j l.1]
  ring

end SideConditions

/-! ### Relabelling from the fine lattice `Idx` to the block index `BlockIndex`

The statements of `Green/EntryDom.lean` are on `BlockIndex L W` through
`blockMat`, `greenBlk`, `Sblk2`, whereas the row-sum results of `Green/RowIndep.lean` are on
`Idx L W = Z2 (W * L)`; the two are joined by `splitEquiv`. -/

section Relabel

variable {m ν : Type*} [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν]

omit [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν] in
private theorem LDE_greenMinor_submatrix (e : m ≃ ν) (G : Matrix ν ν ℂ) (a k l : m) :
    greenMinor (G.submatrix e e) a k l = greenMinor G (e a) (e k) (e l) := by
  simp [greenMinor]

private theorem LDE_ldeRowLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ) (a b : m) :
    ldeRowLHS (H.submatrix e e) (G.submatrix e e) a b = ldeRowLHS H G (e a) (e b) := by
  unfold ldeRowLHS
  congr 2
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeRowRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ) (G : Matrix ν ν ℂ)
    (a b : m) :
    ldeRowRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a b = ldeRowRHS S G (e a) (e b) := by
  unfold ldeRowRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeColLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ) (a b : m) :
    ldeColLHS (H.submatrix e e) (G.submatrix e e) a b = ldeColLHS H G (e a) (e b) := by
  unfold ldeColLHS
  congr 2
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeColRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ) (G : Matrix ν ν ℂ)
    (a b : m) :
    ldeColRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a b = ldeColRHS S G (e a) (e b) := by
  unfold ldeColRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

end Relabel

section RelabelBlock

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The block resolvent is the fine-lattice resolvent, relabelled by `splitEquiv`. -/
private theorem LDE_greenBlk_true (E t : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    greenBlk L W E t M true
      = (green M (spectralZ E t)).submatrix (splitEquiv L W).symm (splitEquiv L W).symm := by
  change green (blockMat M) (spectralZ E t) = _
  unfold green blockMat
  have h : (M - spectralZ E t • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
      (splitEquiv L W).symm (splitEquiv L W).symm
      = M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm
        - spectralZ E t • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, (splitEquiv L W).symm.injective.eq_iff]
  rw [← h, Matrix.inv_submatrix_equiv]

variable (M : Matrix (Idx L W) (Idx L W) ℂ) (E t : ℝ)

private theorem LDE_Sblk2_eq (a b : BlockIndex L W) :
    Sblk2 L W a b = svar L W ((splitEquiv L W).symm a) ((splitEquiv L W).symm b) :=
  Sblk2_eq_svar a b

private theorem LDE_blk_rowLHS (a b : BlockIndex L W) :
    ldeRowLHS (blockMat M) (greenBlk L W E t M true) a b
      = ldeRowLHS M (green M (spectralZ E t)) ((splitEquiv L W).symm a)
          ((splitEquiv L W).symm b) := by
  rw [LDE_greenBlk_true]
  exact LDE_ldeRowLHS_submatrix (splitEquiv L W).symm M _ a b

private theorem LDE_blk_rowRHS (a b : BlockIndex L W) :
    ldeRowRHS (Sblk2 L W) (greenBlk L W E t M true) a b
      = ldeRowRHS (svar L W) (green M (spectralZ E t)) ((splitEquiv L W).symm a)
          ((splitEquiv L W).symm b) := by
  rw [LDE_greenBlk_true]
  have h : Sblk2 L W = fun p q => svar L W ((splitEquiv L W).symm p) ((splitEquiv L W).symm q) := by
    funext p q; exact LDE_Sblk2_eq p q
  rw [h]
  exact LDE_ldeRowRHS_submatrix (splitEquiv L W).symm (svar L W) _ a b

private theorem LDE_blk_colLHS (a b : BlockIndex L W) :
    ldeColLHS (blockMat M) (greenBlk L W E t M true) a b
      = ldeColLHS M (green M (spectralZ E t)) ((splitEquiv L W).symm a)
          ((splitEquiv L W).symm b) := by
  rw [LDE_greenBlk_true]
  exact LDE_ldeColLHS_submatrix (splitEquiv L W).symm M _ a b

private theorem LDE_blk_colRHS (a b : BlockIndex L W) :
    ldeColRHS (Sblk2 L W) (greenBlk L W E t M true) a b
      = ldeColRHS (svar L W) (green M (spectralZ E t)) ((splitEquiv L W).symm a)
          ((splitEquiv L W).symm b) := by
  rw [LDE_greenBlk_true]
  have h : Sblk2 L W = fun p q => svar L W ((splitEquiv L W).symm p) ((splitEquiv L W).symm q) := by
    funext p q; exact LDE_Sblk2_eq p q
  rw [h]
  exact LDE_ldeColRHS_submatrix (splitEquiv L W).symm (svar L W) _ a b

end RelabelBlock

/-! ### The bridge from the normalised row sum to `PerTimeDomAt`, with a time sequence

The time is a sequence `tim n ∈ [0, 1]`, so the degenerate
fibre argument is done per `n` on top of `stochDom_rowSum_generalTime`.  The
conclusion is the per-time form `PerTimeDomAt` (no union bound is needed for it). -/

section Bridge

variable {d : Sizes}

/-- **From `‖Z‖ / √V ≺ 1` to `‖Z‖² ≺ B`, uniformly in a time sequence.**  If `A = ‖Z‖²` and the
conditional variance is `tim n · B` with `0 ≤ tim n ≤ 1` and `B ≥ 0`, then `A ≺ B` in the
per-time form. -/
private theorem LDE_perTime_sq_of_rowSum (hsize : Filter.Tendsto d.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (d.size n : ℝ) ^ Ccard)
    (tim : ℕ → ℝ) (h0 : ∀ n, 0 ≤ tim n) (h1 : ∀ n, tim n ≤ 1)
    (row : ∀ n, U n → Idx (d.L n) (d.W n))
    (C : ∀ n, U n → Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ d),
      (∀ c ∈ offRowCoord d n (row n q), ω c = ω' c) → C n q ω = C n q ω')
    {V : ℕ → Type*} (f : ∀ n, V n → U n) (A B : ∀ n, V n → Sizes.SeqΩ d → ℝ)
    (hB : ∀ n v ω, 0 ≤ B n v ω)
    (hA : ∀ n v ω, A n v ω = ‖rowSum d n (tim n) (row n (f n v)) (C n (f n v)) ω‖ ^ 2)
    (hVar : ∀ n v ω,
      rowVarSum d n (tim n) (row n (f n v)) (C n (f n v)) ω = tim n * B n v ω) :
    PerTimeDomAt (Sizes.seqP d) d.size A B := by
  classical
  intro τ hτ D hD
  have hgood := stochDom_rowSum_generalTime (d := d) hsize hcard (fun n _ => tim n)
    (fun n _ => h0 n) row C hCmeas hC
  filter_upwards [hgood (τ / 2) (by linarith) D hD, hsize.eventually_ge_atTop 1] with n hn hn1
  intro v
  have hpos : (0 : ℝ) < (d.size n : ℝ) := by exact_mod_cast hn1
  set q := f n v with hq
  have hnull : (Sizes.seqP d) {ω | ¬ (rowVarSum d n (tim n) (row n q) (C n q) ω = 0 →
      rowSum d n (tim n) (row n q) (C n q) ω = 0)} = 0 := by
    have hae := rowSum_ae_eq_zero_of_varSum_eq_zero (d := d) (n := n) (i := row n q)
      (h0 n) (C n q) (hCmeas n q) (hC n q)
    simpa [MeasureTheory.ae_iff] using hae
  have hsub : {ω | (d.size n : ℝ) ^ τ * B n v ω < A n v ω}
      ⊆ badSetAt d.size (fun n q ω =>
          ‖rowSum d n (tim n) (row n q) (rowCoeffNorm d n (tim n) (row n q) (C n q)) ω‖)
          (fun _ _ _ => (1 : ℝ)) (τ / 2) n
        ∪ {ω | ¬ (rowVarSum d n (tim n) (row n q) (C n q) ω = 0 →
            rowSum d n (tim n) (row n q) (C n q) ω = 0)} := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1', h2'⟩ := hcon
    have h1'' : ‖rowSum d n (tim n) (row n q)
        (rowCoeffNorm d n (tim n) (row n q) (C n q)) ω‖ ≤ (d.size n : ℝ) ^ (τ / 2) * 1 := by
      by_contra hlt
      exact h1' ⟨q, not_le.1 hlt⟩
    have h2'' : rowVarSum d n (tim n) (row n q) (C n q) ω = 0 →
        rowSum d n (tim n) (row n q) (C n q) ω = 0 := by
      by_contra hne
      exact h2' hne
    have hω' : (d.size n : ℝ) ^ τ * B n v ω
        < ‖rowSum d n (tim n) (row n q) (C n q) ω‖ ^ 2 := by
      have h := hω
      rw [Set.mem_ofPred_eq (p := fun ω => (d.size n : ℝ) ^ τ * B n v ω < A n v ω)] at h
      rwa [hA n v ω] at h
    have hNB : 0 ≤ (d.size n : ℝ) ^ τ * B n v ω :=
      mul_nonneg (Real.rpow_nonneg hpos.le τ) (hB n v ω)
    have hV0 : 0 ≤ rowVarSum d n (tim n) (row n q) (C n q) ω := by
      rw [hVar n v ω]; exact mul_nonneg (h0 n) (hB n v ω)
    rcases eq_or_lt_of_le hV0 with hV | hV
    · rw [h2'' hV.symm] at hω'
      simp at hω'
      linarith
    · have hs : (0 : ℝ) < Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω) :=
        Real.sqrt_pos.2 hV
      rw [rowSum_rowCoeffNorm (C n q) hV, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs.le, mul_one] at h1''
      have hle : ‖rowSum d n (tim n) (row n q) (C n q) ω‖
          ≤ (d.size n : ℝ) ^ (τ / 2)
            * Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω) := by
        rw [inv_mul_le_iff₀ hs] at h1''
        linarith [h1'']
      have hnn : (0 : ℝ) ≤ ‖rowSum d n (tim n) (row n q) (C n q) ω‖ := norm_nonneg _
      have hrhs : (0 : ℝ) ≤ (d.size n : ℝ) ^ (τ / 2)
          * Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω) := by
        have : (0 : ℝ) ≤ (d.size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg hpos.le _
        positivity
      have hsq := mul_le_mul hle hle hnn hrhs
      have hsqrt : Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω) *
          Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω)
          = rowVarSum d n (tim n) (row n q) (C n q) ω := Real.mul_self_sqrt hV0
      have hNpow : (d.size n : ℝ) ^ (τ / 2) * (d.size n : ℝ) ^ (τ / 2) = (d.size n : ℝ) ^ τ := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      have hchain : ‖rowSum d n (tim n) (row n q) (C n q) ω‖ ^ 2
          ≤ (d.size n : ℝ) ^ τ * rowVarSum d n (tim n) (row n q) (C n q) ω := by
        calc ‖rowSum d n (tim n) (row n q) (C n q) ω‖ ^ 2
            = ‖rowSum d n (tim n) (row n q) (C n q) ω‖
              * ‖rowSum d n (tim n) (row n q) (C n q) ω‖ := by ring
          _ ≤ ((d.size n : ℝ) ^ (τ / 2)
                * Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω)) *
              ((d.size n : ℝ) ^ (τ / 2)
                * Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω)) := hsq
          _ = ((d.size n : ℝ) ^ (τ / 2) * (d.size n : ℝ) ^ (τ / 2)) *
              (Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω) *
                Real.sqrt (rowVarSum d n (tim n) (row n q) (C n q) ω)) := by ring
          _ = (d.size n : ℝ) ^ τ * rowVarSum d n (tim n) (row n q) (C n q) ω := by
              rw [hNpow, hsqrt]
      have hvarle : rowVarSum d n (tim n) (row n q) (C n q) ω ≤ B n v ω := by
        rw [hVar n v ω]
        nlinarith [hB n v ω, h1 n, h0 n]
      have hmul : (d.size n : ℝ) ^ τ * rowVarSum d n (tim n) (row n q) (C n q) ω
          ≤ (d.size n : ℝ) ^ τ * B n v ω :=
        mul_le_mul_of_nonneg_left hvarle (Real.rpow_nonneg hpos.le τ)
      linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  exact hn

end Bridge

/-! ### The two hypotheses `hLrow`, `hLcol` of `entry_bound_stochDom` -/

section RowCol

variable (d : Sizes)

/-- **The row large deviation input `hLrow` of `entry_bound_stochDom`,** for the Gaussian flow
`H_{t_n}`: `|∑_{k≠i} H_{ik} G^{(i)}_{kj}|² ≺ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}|²`, uniformly in
`i ≠ j`, per time `t n` (the conclusion is the text of `hLrow`). -/
theorem stochDom_ldeRow {κ : ℝ} (hκ : 0 < κ) (hsz : RBM.Ind.SizeTendsto d) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2) := by
  have hsz' : Filter.Tendsto d.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hz : ∀ n, (spectralZ (E n) (t n)).im ≠ 0 := fun n => zt_im_ne_zero hκ (hE n) (ht1 n)
  refine LDE_perTime_sq_of_rowSum (d := d) hsz' (eventually_card_LdeIdx_le d) t ht0
    (fun n => (ht1 n).le) (fun n q => q.1)
    (fun n q => minorCol d n (t n) (spectralZ (E n) (t n)) q.1 q.2)
    (fun n q => measurable_minorCol (t n) _ q.1 q.2)
    (fun n q ω ω' h => minorCol_congr (t n) _ q.2 h)
    (V := fun n => OffPair (d.L n) (d.W n))
    (fun n p => (⟨(splitEquiv (d.L n) (d.W n)).symm p.1.1,
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.2,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne (Ne.symm p.2)⟩⟩ : LdeIdx d n)) _ _ ?_ ?_ ?_
  · intro n p ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Sblk2_nonneg _ _) (by positivity)
  · intro n p ω
    rw [LDE_blk_rowLHS]
    exact ldeRowLHS_eq (z := spectralZ (E n) (t n)) (t n)
      (i := (splitEquiv (d.L n) (d.W n)).symm p.1.1)
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.2,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne (Ne.symm p.2)⟩
      (isUnit_det_Hflow_sub d n (t n) ω (hz n))
      (green_Hflow_diag_ne_zero d n (t n) ω (hz n) _)
  · intro n p ω
    rw [LDE_blk_rowRHS]
    exact rowVarSum_eq (z := spectralZ (E n) (t n)) (t n)
      (i := (splitEquiv (d.L n) (d.W n)).symm p.1.1)
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.2,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne (Ne.symm p.2)⟩
      (isUnit_det_Hflow_sub d n (t n) ω (hz n))
      (green_Hflow_diag_ne_zero d n (t n) ω (hz n) _)

/-- **The column large deviation input `hLcol` of `entry_bound_stochDom`,** for the Gaussian flow
`H_{t_n}`: `|∑_{l≠j} G^{(j)}_{kl} H_{lj}|² ≺ ∑_{l≠j} |G^{(j)}_{kl}|² S_{lj}`, uniformly in
`k ≠ j`. -/
theorem stochDom_ldeCol {κ : ℝ} (hκ : 0 < κ) (hsz : RBM.Ind.SizeTendsto d) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2) := by
  have hsz' : Filter.Tendsto d.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hz : ∀ n, (spectralZ (E n) (t n)).im ≠ 0 := fun n => zt_im_ne_zero hκ (hE n) (ht1 n)
  refine LDE_perTime_sq_of_rowSum (d := d) hsz' (eventually_card_LdeIdx_le d) t ht0
    (fun n => (ht1 n).le) (fun n q => q.1)
    (fun n q => minorRowConj d n (t n) (spectralZ (E n) (t n)) q.1 q.2)
    (fun n q => measurable_minorRowConj (t n) _ q.1 q.2)
    (fun n q ω ω' h => minorRowConj_congr (t n) _ q.2 h)
    (V := fun n => OffPair (d.L n) (d.W n))
    (fun n p => (⟨(splitEquiv (d.L n) (d.W n)).symm p.1.2,
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.1,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne p.2⟩⟩ : LdeIdx d n)) _ _ ?_ ?_ ?_
  · intro n p ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk2_nonneg _ _)
  · intro n p ω
    rw [LDE_blk_colLHS]
    exact ldeColLHS_eq (z := spectralZ (E n) (t n)) (t n)
      (j := (splitEquiv (d.L n) (d.W n)).symm p.1.2)
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.1,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne p.2⟩
      (isUnit_det_Hflow_sub d n (t n) ω (hz n))
      (green_Hflow_diag_ne_zero d n (t n) ω (hz n) _)
  · intro n p ω
    rw [LDE_blk_colRHS]
    exact rowVarSum_minorRowConj_eq (z := spectralZ (E n) (t n)) (t n)
      (j := (splitEquiv (d.L n) (d.W n)).symm p.1.2)
      ⟨(splitEquiv (d.L n) (d.W n)).symm p.1.1,
        (splitEquiv (d.L n) (d.W n)).symm.injective.ne p.2⟩
      (isUnit_det_Hflow_sub d n (t n) ω (hz n))
      (green_Hflow_diag_ne_zero d n (t n) ω (hz n) _)

end RowCol

/-! ### The diagonal input `hLdiag`

The diagonal entry `H_xx = √u · ω⟨n,x,x,tt⟩` is a real centred Gaussian of variance
`u · svar_xx = u / (5 W²)`; the Gaussian moments below are private copies of those of
`RowIndep.lean`. -/

section DiagMoments

private theorem LDE_integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

private theorem LDE_integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

private theorem LDE_integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := LDE_integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((LDE_integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    LDE_integrable_mul_gaussianPDFReal hv
      ((LDE_integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    LDE_integrable_mul_gaussianPDFReal hv (LDE_integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`. -/
private theorem LDE_integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = RowIndep_dfac p * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, LDE_integral_pow_gaussianReal_succ, ih,
      RowIndep_dfac_succ]
    ring

end DiagMoments

section Diag

/-- The diagonal of the variance profile is `1 / (5 W²) > 0`. -/
theorem Sblk_diag_pos {L W : ℕ} [NeZero L] [NeZero W] (i : BlockIndex L W) :
    0 < Sblk2 L W i i := by
  have hW : (0 : ℝ) < W := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hm : (0 : Z2 L) ∈ sbSupport L := by
    rw [sbSupport]; exact Finset.mem_insert.2 (Or.inl rfl)
  have h0 : sbKre2 L (i.1 - i.1) = 1 / 5 := by
    simp only [sub_self, sbKre2, hm, ↓reduceIte]
  rw [Sblk2, h0]
  positivity

variable {d : Sizes} {n : ℕ} {u : ℝ}

/-! #### One coordinate -/

/-- Moments of a single coordinate, pushed through `Sizes.seqP_map_eval`. -/
theorem integral_pow_coord (d : Sizes) (c : Sizes.SeqCoord d) (k : ℕ) :
    ∫ ω, (ω c) ^ k ∂(Sizes.seqP d) = ∫ x : ℝ, x ^ k ∂(gaussianReal 0 (Sizes.seqGvar d c)) := by
  have hf : AEMeasurable (fun ω : Sizes.SeqΩ d => ω c) (Sizes.seqP d) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((Sizes.seqP d).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, Sizes.seqP_map_eval]

theorem integrable_pow_coord (d : Sizes) (c : Sizes.SeqCoord d) (k : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ d => (ω c) ^ k) (Sizes.seqP d) := by
  have hf : AEMeasurable (fun ω : Sizes.SeqΩ d => ω c) (Sizes.seqP d) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((Sizes.seqP d).map fun ω => ω c) := by
    fun_prop
  refine (integrable_map_measure hg hf).1 ?_
  rw [Sizes.seqP_map_eval]
  exact LDE_integrable_pow_gaussianReal _ k

/-! #### The diagonal entry of the flow -/

/-- The diagonal entry is real: `|H_{xx}|² = u · ω⟨n,x,x,tt⟩²`. -/
theorem normSq_Hflow_diag (hu : 0 ≤ u) (ω : Sizes.SeqΩ d) (x : Idx (d.L n) (d.W n)) :
    ‖Sizes.seqHflow d n u ω x x‖ ^ 2 = u * (ω ⟨n, (x, x, true)⟩) ^ 2 := by
  have hX : Xentry (d.L n) (d.W n) (Sizes.slice d n ω) x x
      = ((ω ⟨n, (x, x, true)⟩ : ℝ) : ℂ) := by
    rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    rfl
  change ‖Hflow (d.L n) (d.W n) u (Sizes.slice d n ω) x x‖ ^ 2 = _
  rw [Hflow_apply, hX, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u), mul_pow, Real.sq_sqrt hu, sq_abs]

/-- **All even moments of the diagonal entry**: `E|H_{xx}|^{2p} = u^p (2p-1)!! S_{xx}^p`. -/
theorem integral_norm_Hflow_diag_pow (hu : 0 ≤ u) (x : Idx (d.L n) (d.W n)) (p : ℕ) :
    ∫ ω, ‖Sizes.seqHflow d n u ω x x‖ ^ (2 * p) ∂(Sizes.seqP d)
      = u ^ p * (RowIndep_dfac p * svar (d.L n) (d.W n) x x ^ p) := by
  have hpow : ∀ ω : Sizes.SeqΩ d, ‖Sizes.seqHflow d n u ω x x‖ ^ (2 * p)
      = u ^ p * (ω ⟨n, (x, x, true)⟩) ^ (2 * p) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω x, mul_pow, ← pow_mul, mul_comm 2 p]
  simp only [hpow]
  rw [integral_const_mul, integral_pow_coord, LDE_integral_pow_gaussianReal]
  have : ((Sizes.seqGvar d ⟨n, (x, x, true)⟩ : ℝ≥0) : ℝ) = svar (d.L n) (d.W n) x x :=
    gvar_diag (d.L n) (d.W n) x true
  rw [this]

theorem integrable_norm_Hflow_diag_pow (hu : 0 ≤ u) (x : Idx (d.L n) (d.W n)) (k : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ d => ‖Sizes.seqHflow d n u ω x x‖ ^ (2 * k))
      (Sizes.seqP d) := by
  have hpow : ∀ ω : Sizes.SeqΩ d, ‖Sizes.seqHflow d n u ω x x‖ ^ (2 * k)
      = u ^ k * (ω ⟨n, (x, x, true)⟩) ^ (2 * k) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω x, mul_pow, ← pow_mul, mul_comm 2 k]
  simp only [hpow]
  exact (integrable_pow_coord d _ (2 * k)).const_mul _

/-! #### The union bound -/

/-- The block index set has exactly `d.size n = (W L)²` elements. -/
theorem eventually_card_Idx_le (d : Sizes) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Fintype.card (BlockIndex (d.L n) (d.W n)) : ℝ) ≤ (d.size n : ℝ) ^ (1 : ℝ) := by
  refine Filter.Eventually.of_forall fun n => ?_
  rw [card_BlockIndex, Real.rpow_one, Sizes.size, mul_comm (d.W n)]

/-- **The input `hLdiag` of `diag_bound_stochDom`**, for the Gaussian flow: `|H_{ii}|² ≺ S_{ii}`,
uniformly in `i`, per time `t n` with `0 ≤ t n < 1` (the constant is uniform in the time
because `t n ≤ 1`). -/
theorem stochDom_normSq_Hflow_diag (d : Sizes) (hsz : RBM.Ind.SizeTendsto d) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (fun n i _ => Sblk2 (d.L n) (d.W n) i i) := by
  have hsz' : Filter.Tendsto d.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hsd : StochDomAt (Sizes.seqP d) d.size
      (fun n (i : BlockIndex (d.L n) (d.W n)) ω =>
        ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (fun n (i : BlockIndex (d.L n) (d.W n)) _ => Sblk2 (d.L n) (d.W n) i i) := by
    refine stochDomAt_of_momentDomAt (P := Sizes.seqP d) d.size hsz'
      (U := fun n => BlockIndex (d.L n) (d.W n)) (Ccard := 1) (eventually_card_Idx_le d)
      (Y := fun n (i : BlockIndex (d.L n) (d.W n)) ω =>
        ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (Φ := fun n (i : BlockIndex (d.L n) (d.W n)) => Sblk2 (d.L n) (d.W n) i i)
      (fun n i => Sblk_diag_pos i) ?_ ?_
    · intro p n i
      have habs : ∀ ω : Sizes.SeqΩ d,
          |‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2| ^ (2 * p)
            = ‖Sizes.seqHflow d n (t n) ω ((splitEquiv (d.L n) (d.W n)).symm i)
                ((splitEquiv (d.L n) (d.W n)).symm i)‖ ^ (2 * (2 * p)) := fun ω => by
        rw [abs_of_nonneg (by positivity), ← pow_mul]
        rfl
      simp only [habs]
      exact integrable_norm_Hflow_diag_pow (ht0 n) _ (2 * p)
    · intro ε hε p
      have hd0 : (0 : ℝ) ≤ RowIndep_dfac (2 * p) := by unfold RowIndep_dfac; positivity
      refine ⟨RowIndep_dfac (2 * p) + 1, by linarith, ?_⟩
      filter_upwards [hsz'.eventually_ge_atTop 1] with n hn1 i
      have hN1' : (1 : ℝ) ≤ (d.size n : ℝ) := by exact_mod_cast hn1
      have hS : (0 : ℝ) < Sblk2 (d.L n) (d.W n) i i := Sblk_diag_pos i
      have hpt : ∀ ω : Sizes.SeqΩ d,
          |‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2| ^ (2 * p)
            = ‖Sizes.seqHflow d n (t n) ω ((splitEquiv (d.L n) (d.W n)).symm i)
                ((splitEquiv (d.L n) (d.W n)).symm i)‖ ^ (2 * (2 * p)) := fun ω => by
        rw [abs_of_nonneg (by positivity), ← pow_mul]
        rfl
      simp only [hpt]
      rw [integral_norm_Hflow_diag_pow (ht0 n), ← Sblk2_eq_svar i i]
      have hpow : (1 : ℝ) ≤ (d.size n : ℝ) ^ (ε * p) := Real.one_le_rpow hN1' (by positivity)
      have hu : (t n) ^ (2 * p) ≤ 1 := pow_le_one₀ (ht0 n) (ht1 n).le
      set A : ℝ := Sblk2 (d.L n) (d.W n) i i ^ (2 * p) with hAdef
      have hA0 : 0 < A := by rw [hAdef]; positivity
      calc (t n) ^ (2 * p) * (RowIndep_dfac (2 * p) * A)
          ≤ 1 * (RowIndep_dfac (2 * p) * A) :=
            mul_le_mul_of_nonneg_right hu (by positivity)
        _ = RowIndep_dfac (2 * p) * A := one_mul _
        _ ≤ (RowIndep_dfac (2 * p) + 1) * A := by nlinarith
        _ ≤ (RowIndep_dfac (2 * p) + 1) * ((d.size n : ℝ) ^ (ε * p) * A) := by
            have h1 : A ≤ (d.size n : ℝ) ^ (ε * p) * A := le_mul_of_one_le_left hA0.le hpow
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
  exact perTimeOfStochDomAt _ _ _ _ hsd

end Diag

end RBM.Green
