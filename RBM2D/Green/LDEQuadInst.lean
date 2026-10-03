/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.IBPPoly
import RBM2D.Green.LDEQuadT
import RBM2D.Green.RowIndep
import RBM2D.Green.LDE

/-!
# The row chaos of the Gaussian model, and the input `hLquad`

The paper (arXiv:2503.07606) does not state
the quadratic large deviation input (Section "Estimates for entries of `G`" refers to Lemma 4.2
of [YY_25]); for the Gaussian flow it is proved here from the Gaussian calculus of
`Green/LDEQuad.lean`, `Green/LDEQuadMom.lean`, `Green/LDEQuadT.lean` and `Green/IBPPoly.lean`.

* `minorRes`: the minor resolvent `(H^{(i)} - z)^{-1}`, bounded by `|Im z|⁻¹` for every `ω`,
  continuous, and reading only the off-row block;
* `modelChaos`: the `RowChaos` of the model at row `i` (row coordinates `rowCoord`, sign
  `rowSign`, scale `√u`, matrix `minorRes`); `modelChaos_normSq_chaos`, `modelChaos_Vq`: its
  chaos and control are `ldeQuadLHS` and `u² · ldeQuadRHS`;
* `modelChaosEps`, `mom_modelChaosEps_le`, `meas_lt_normSq_chaos_le`: the normalised chaos and
  the tail bound with the random control;
* `stochDom_ldeQuad`: the hypothesis `hLquad` of `diag_bound_stochDom` (`Green/EntryDom.lean`),
  in its literal text, for the Gaussian flow.

The resolvent continuity lemma is `RBM.Gauss.continuous_green_of_isHermitian`
(`Gauss/GreenTimeCont.lean`); it is not re-declared.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM RBM.Gauss RBM.Path

/-! ### An entry is bounded by the operator norm -/

section OpNorm

open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- An entry is bounded by the `ℓ² → ℓ²` operator norm (as `RBM.Ind.norm_apply_le_l2_opNorm`, which
this file does not import). -/
private theorem LDEQuadInst_norm_apply_le (M : Matrix ν ν ℂ) (p q : ν) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

end OpNorm

variable {d : Sizes} {n : ℕ} {u : ℝ} {z : ℂ}

/-- The size-`n` flow is continuous on the common sample space. -/
private theorem LDEQuadInst_continuous_seqHflow (d : Sizes) (n : ℕ) (u : ℝ) :
    Continuous fun ω : Sizes.SeqΩ d => Sizes.seqHflow d n u ω :=
  (continuous_Hflow (d.L n) (d.W n) u).comp
    (continuous_pi fun c => continuous_apply (⟨n, c⟩ : Sizes.SeqCoord d))

/-! ### The minor resolvent as the matrix of the chaos -/

/-- `(H^{(i)} - z)^{-1}`, the resolvent of the minor. -/
noncomputable def minorRes (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (i : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) :
    Matrix {a : Idx (d.L n) (d.W n) // a ≠ i} {a : Idx (d.L n) (d.W n) // a ≠ i} ℂ :=
  green ((Sizes.seqHflow d n u ω).submatrix
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))) z

theorem isHermitian_Hflow_submatrix (d : Sizes) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d)
    (i : Idx (d.L n) (d.W n)) :
    ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))).IsHermitian :=
  (Sizes.seqHflow_isHermitian d n u ω).submatrix _

/-- **The minor resolvent is bounded by `|Im z|⁻¹`, for every `ω`.** -/
theorem norm_minorRes_le (hz : z.im ≠ 0) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d)
    (k l : {a : Idx (d.L n) (d.W n) // a ≠ i}) : ‖minorRes d n u z i ω k l‖ ≤ |z.im|⁻¹ := by
  open scoped Matrix.Norms.L2Operator in
  exact le_trans (LDEQuadInst_norm_apply_le _ k l)
    (norm_green_le (isHermitian_Hflow_submatrix d n u ω i) (abs_pos.2 hz) le_rfl)

theorem continuous_minorRes (hz : z.im ≠ 0) (i : Idx (d.L n) (d.W n))
    (k l : {a : Idx (d.L n) (d.W n) // a ≠ i}) :
    Continuous fun ω : Sizes.SeqΩ d => minorRes d n u z i ω k l := by
  refine Continuous.matrix_elem ?_ k l
  exact continuous_green_of_isHermitian
    ((LDEQuadInst_continuous_seqHflow d n u).matrix_submatrix _ _)
    (fun ω => isHermitian_Hflow_submatrix d n u ω i) hz

/-- The minor resolvent reads only the off-row block. -/
theorem minorRes_congr (i : Idx (d.L n) (d.W n)) {ω ω' : Sizes.SeqΩ d}
    (h : ∀ c ∈ offRowCoord d n i, ω c = ω' c) :
    minorRes d n u z i ω = minorRes d n u z i ω' := by
  unfold minorRes
  rw [Hflow_submatrix_congr_offRowCoord u h]

/-! ### The instance -/

/-- **The row chaos of the Gaussian model at row `i`.**  The row is `h_k = (H_u)_{ik}`, the
matrix is the minor resolvent `(H^{(i)} - z)^{-1}`, and the scale is `r = √u`. -/
noncomputable def modelChaos (d : Sizes) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx (d.L n) (d.W n)) : RowChaos d {a : Idx (d.L n) (d.W n) // a ≠ i} where
  co k b := rowCoord d n i k.1 b
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
    subst h1; subst h2; rfl
  gvar_tag k := by rw [gvar_rowCoord k.2, gvar_rowCoord k.2]
  eps k := rowSign d n i k.1
  eps_sq k := by unfold rowSign; split_ifs <;> norm_num
  r := Real.sqrt u
  B ω k l := minorRes d n u z i ω k l
  B_cont k l := continuous_minorRes hz i k l
  Bbd := |z.im|⁻¹
  B_bdd ω k l := norm_minorRes_le hz i ω k l
  Ifree := offRowCoord d n i
  Ifree_free k b := by
    intro hmem
    exact (Finset.mem_sdiff.1 hmem).2 (rowCoord_mem_rowSet i k.1 b)
  B_free ω ω' h := by
    funext k l
    rw [minorRes_congr (u := u) (z := z) i h]

/-! ### What the instance is -/

section Instance

variable (hz : z.im ≠ 0) (i : Idx (d.L n) (d.W n))

/-- **The row of the chaos is the `i`-th row of `H_u`.** -/
theorem modelChaos_h (ω : Sizes.SeqΩ d) (k : {a : Idx (d.L n) (d.W n) // a ≠ i}) :
    (modelChaos d n u hz i).h ω k = Sizes.seqHflow d n u ω i k.1 := by
  change (Real.sqrt u : ℂ) * ((ω (rowCoord d n i k.1 true) : ℂ)
      + ((rowSign d n i k.1 : ℂ) * Complex.I) * (ω (rowCoord d n i k.1 false) : ℂ))
    = (Real.sqrt u : ℂ) * Xentry (d.L n) (d.W n) (Sizes.slice d n ω) i k.1
  rw [Xentry_eq_rowCoord (Ne.symm k.2) ω]

/-- **The variance of the row is `σ_k = u S_{ik}`** (`S = svar`, the two-dimensional profile). -/
theorem modelChaos_sg (hu : 0 ≤ u) (k : {a : Idx (d.L n) (d.W n) // a ≠ i}) :
    (modelChaos d n u hz i).sg k = u * svar (d.L n) (d.W n) i k.1 := by
  change 2 * Real.sqrt u ^ 2 * (Sizes.seqGvar d (rowCoord d n i k.1 true) : ℝ) = _
  rw [gvar_rowCoord k.2, Real.sq_sqrt hu]
  ring

/-- **The matrix of the chaos is `G^{(i)}`, for every `ω`.**  The two side conditions of
`RBM.Green.inv_minor_resolvent` hold unconditionally off the real axis. -/
theorem modelChaos_B_eq (ω : Sizes.SeqΩ d) (k l : {a : Idx (d.L n) (d.W n) // a ≠ i}) :
    (modelChaos d n u hz i).B ω k l
      = greenMinor (green (Sizes.seqHflow d n u ω) z) i k.1 l.1 := by
  change minorRes d n u z i ω k l = _
  unfold minorRes
  rw [show green ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ i} → Idx (d.L n) (d.W n))) z
      = ((Sizes.seqHflow d n u ω).submatrix Subtype.val Subtype.val
        - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ i} _ ℂ))⁻¹ from rfl,
    inv_minor_resolvent (isUnit_det_Hflow_sub d n u ω hz) i
      (green_Hflow_diag_ne_zero d n u ω hz i)]
  rfl

/-! ### The two sides of (4.7), in the paper's notation -/

/-- **The chaos of the instance is `ldeQuadLHS`.** -/
theorem modelChaos_normSq_chaos (hu : 0 ≤ u) (ω : Sizes.SeqΩ d) :
    ‖(modelChaos d n u hz i).chaos ω‖ ^ 2
      = ldeQuadLHS (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z)
          (svar (d.L n) (d.W n)) u i :=
  RowChaos.norm_chaos_sq_eq_ldeQuadLHS (modelChaos d n u hz i) ω
    (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z) (svar (d.L n) (d.W n)) u
    (fun k => modelChaos_h hz i ω k)
    (fun k => by
      rw [modelChaos_h hz i ω k]
      exact (Sizes.seqHflow_isHermitian d n u ω).apply k.1 i)
    (fun k l => modelChaos_B_eq hz i ω k l)
    (fun k => modelChaos_sg hz i hu k)

/-- **The control of the instance is `u² · ldeQuadRHS`.**  The factor `u²` comes from
`E|H_{ik}|² = u S_{ik}` while `ldeQuadRHS` is written with `S`; the column form `hsg'` of
`RowChaos.Vq_eq_ldeQuadRHS` is `modelChaos_sg` with `svar_comm`. -/
theorem modelChaos_Vq (hu : 0 ≤ u) (ω : Sizes.SeqΩ d) :
    (modelChaos d n u hz i).Vq ω
      = u ^ 2 * ldeQuadRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i :=
  RowChaos.Vq_eq_ldeQuadRHS (modelChaos d n u hz i) ω
    (green (Sizes.seqHflow d n u ω) z) (svar (d.L n) (d.W n)) u
    (fun k l => modelChaos_B_eq hz i ω k l)
    (fun k => modelChaos_sg hz i hu k)
    (fun k => by rw [modelChaos_sg hz i hu k, svar_comm])

end Instance

/-! ### The control of the model instance, as a function of `ω` -/

/-- `V_q` of the model instance, written out: `∑_{k,l} (uS_{ik})‖G^{(i)}_{kl}‖²(uS_{il})`. -/
noncomputable def vqM (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (i : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) : ℝ :=
  ∑ k : {a : Idx (d.L n) (d.W n) // a ≠ i}, ∑ l : {a : Idx (d.L n) (d.W n) // a ≠ i},
    (u * svar (d.L n) (d.W n) i k.1) * ‖minorRes d n u z i ω k l‖ ^ 2 *
      (u * svar (d.L n) (d.W n) i l.1)

theorem vqM_nonneg (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    0 ≤ vqM d n u z i ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hu (svar_nonneg _ _ _ _)) (by positivity))
      (mul_nonneg hu (svar_nonneg _ _ _ _))

theorem continuous_vqM (hz : z.im ≠ 0) (i : Idx (d.L n) (d.W n)) :
    Continuous fun ω : Sizes.SeqΩ d => vqM d n u z i ω := by
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact ((continuous_const.mul (((continuous_minorRes hz i k l).norm).pow 2)).mul
    continuous_const)

theorem vqM_congr (i : Idx (d.L n) (d.W n)) {ω ω' : Sizes.SeqΩ d}
    (h : ∀ c ∈ offRowCoord d n i, ω c = ω' c) :
    vqM d n u z i ω = vqM d n u z i ω' := by
  unfold vqM
  rw [minorRes_congr (u := u) (z := z) i h]

theorem vqM_eq (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    (modelChaos d n u hz i).Vq ω = vqM d n u z i ω := by
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [modelChaos_sg hz i hu k, modelChaos_sg hz i hu l]
  rfl

/-! ### The `ε`-normalised instance -/

/-- The normalising factor `(V_q + ε)^{1/2}`. -/
noncomputable def sqVq (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (i : Idx (d.L n) (d.W n)) (ε : ℝ)
    (ω : Sizes.SeqΩ d) : ℝ :=
  Real.sqrt (vqM d n u z i ω + ε)

theorem sqVq_pos (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) : 0 < sqVq d n u z i ε ω :=
  Real.sqrt_pos.2 (by linarith [vqM_nonneg (z := z) hu i ω])

theorem sq_sqVq (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) : sqVq d n u z i ε ω ^ 2 = vqM d n u z i ω + ε :=
  Real.sq_sqrt (by linarith [vqM_nonneg (z := z) hu i ω])

theorem sqVq_ge (hu : 0 ≤ u) {ε : ℝ} (_hε : 0 < ε) (i : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) : Real.sqrt ε ≤ sqVq d n u z i ε ω :=
  Real.sqrt_le_sqrt (by linarith [vqM_nonneg (z := z) hu i ω])

/-- **The `ε`-normalised row chaos**: the same row, with the matrix divided by
`(V_q + ε)^{1/2}`.  The factor does not depend on `(k, l)`, so the chaos is divided by it too,
and it reads only the off-row block, so `B_free` survives. -/
noncomputable def modelChaosEps (d : Sizes) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (ε : ℝ) (hε : 0 < ε) :
    RowChaos d {a : Idx (d.L n) (d.W n) // a ≠ i} :=
  { modelChaos d n u hz i with
    B := fun ω k l => minorRes d n u z i ω k l / ((sqVq d n u z i ε ω : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (continuous_minorRes hz i k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp
          ((continuous_vqM (u := u) hz i).add continuous_const).sqrt
      · intro ω
        exact_mod_cast (sqVq_pos (z := z) hu hε i ω).ne'
    Bbd := |z.im|⁻¹ / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos := sqVq_pos (z := z) hu hε i ω
      have hge := sqVq_ge (z := z) hu hε i ω
      have hεp : (0 : ℝ) < Real.sqrt ε := Real.sqrt_pos.2 hε
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact div_le_div₀ (by positivity) (norm_minorRes_le hz i ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : sqVq d n u z i ε ω = sqVq d n u z i ε ω' := by
        unfold sqVq
        rw [vqM_congr (u := u) (z := z) i h]
      funext k l
      rw [minorRes_congr (u := u) (z := z) i h, hs] }

/-- **The normalised chaos is the chaos, divided by `(V_q+ε)^{1/2}`.** -/
theorem chaos_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) {ε : ℝ}
    (hε : 0 < ε) (ω : Sizes.SeqΩ d) :
    (modelChaosEps d n u hz hu i ε hε).chaos ω
      = (modelChaos d n u hz i).chaos ω / ((sqVq d n u z i ε ω : ℝ) : ℂ) := by
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    change (modelChaos d n u hz i).h ω k *
        (minorRes d n u z i ω k l / ((sqVq d n u z i ε ω : ℝ) : ℂ)) *
        (starRingEnd ℂ) ((modelChaos d n u hz i).h ω l)
      = (modelChaos d n u hz i).h ω k * minorRes d n u z i ω k l *
        (starRingEnd ℂ) ((modelChaos d n u hz i).h ω l) / ((sqVq d n u z i ε ω : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (((modelChaos d n u hz i).sg k : ℝ) : ℂ) *
        (minorRes d n u z i ω k k / ((sqVq d n u z i ε ω : ℝ) : ℂ))
      = (((modelChaos d n u hz i).sg k : ℝ) : ℂ) * minorRes d n u z i ω k k /
        ((sqVq d n u z i ε ω : ℝ) : ℂ)
    ring

/-- **The normalised control is `V_q/(V_q+ε)`.** -/
theorem Vq_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) {ε : ℝ}
    (hε : 0 < ε) (ω : Sizes.SeqΩ d) :
    (modelChaosEps d n u hz hu i ε hε).Vq ω
      = vqM d n u z i ω / (vqM d n u z i ω + ε) := by
  have hpos := sqVq_pos (z := z) hu hε i ω
  have hsq := sq_sqVq (z := z) hu hε i ω
  have hpt : ∀ k l : {a : Idx (d.L n) (d.W n) // a ≠ i},
      (modelChaosEps d n u hz hu i ε hε).sg k *
          ‖(modelChaosEps d n u hz hu i ε hε).B ω k l‖ ^ 2 *
          (modelChaosEps d n u hz hu i ε hε).sg l
        = ((modelChaos d n u hz i).sg k * ‖(modelChaos d n u hz i).B ω k l‖ ^ 2 *
            (modelChaos d n u hz i).sg l) / (vqM d n u z i ω + ε) := by
    intro k l
    change (modelChaos d n u hz i).sg k *
        ‖minorRes d n u z i ω k l / ((sqVq d n u z i ε ω : ℝ) : ℂ)‖ ^ 2 *
        (modelChaos d n u hz i).sg l = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
    change _ = ((modelChaos d n u hz i).sg k * ‖minorRes d n u z i ω k l‖ ^ 2 *
      (modelChaos d n u hz i).sg l) / (vqM d n u z i ω + ε)
    ring
  have hd : ∀ (A : {a : Idx (d.L n) (d.W n) // a ≠ i} → {a : Idx (d.L n) (d.W n) // a ≠ i} → ℝ)
      (c : ℝ), (∑ k, ∑ l, A k l / c) = (∑ k, ∑ l, A k l) / c := by
    intro A c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_div _ _ _).symm
  unfold RowChaos.Vq
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l,
    hd (fun k l => (modelChaos d n u hz i).sg k * ‖(modelChaos d n u hz i).B ω k l‖ ^ 2 *
      (modelChaos d n u hz i).sg l) (vqM d n u z i ω + ε),
    show (∑ k, ∑ l, (modelChaos d n u hz i).sg k *
        ‖(modelChaos d n u hz i).B ω k l‖ ^ 2 * (modelChaos d n u hz i).sg l)
      = vqM d n u z i ω from vqM_eq hz hu i ω]

theorem Vq_modelChaosEps_le_one (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ d) : (modelChaosEps d n u hz hu i ε hε).Vq ω ≤ 1 := by
  rw [Vq_modelChaosEps hz hu i hε ω]
  have h0 := vqM_nonneg (z := z) hu i ω
  rw [div_le_one (by linarith)]
  linarith

/-! ### The moment bound for the normalised chaos -/

/-- The constant of `RowChaos.mom_le_momVpow` at `p = q+1`. -/
noncomputable def hwConst (q : ℕ) : ℝ := ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1)

theorem hwConst_pos (q : ℕ) : 0 < hwConst q := by unfold hwConst; positivity

/-- **`E[(|Q|²/(V_q+ε))^{q+1}] ≤ A_{q+1}`, uniformly in `ε`.** -/
theorem mom_modelChaosEps_le (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (modelChaosEps d n u hz hu i ε hε).mom (q + 1) ≤ hwConst q := by
  have h := (modelChaosEps d n u hz hu i ε hε).mom_le_momVpow (gaussIBP d) q
  have hV : (modelChaosEps d n u hz hu i ε hε).momVpow (q + 1) ≤ 1 := by
    change (∫ ω, (modelChaosEps d n u hz hu i ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP d)) ≤ 1
    calc ∫ ω, (modelChaosEps d n u hz hu i ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP d)
        ≤ ∫ _ω : Sizes.SeqΩ d, (1 : ℝ) ∂(Sizes.seqP d) :=
          MeasureTheory.integral_mono
            ((modelChaosEps d n u hz hu i ε hε).integrable_Vq_pow (gaussIBP d) (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω)
              (Vq_modelChaosEps_le_one hz hu i hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ hwConst q := (hwConst_pos q).le
  refine h.trans ?_
  calc hwConst q * (modelChaosEps d n u hz hu i ε hε).momVpow (q + 1)
      ≤ hwConst q * 1 := mul_le_mul_of_nonneg_left hV hc
    _ = hwConst q := mul_one _

/-! ### The tail bound, at fixed `ε` and then in the limit -/

theorem norm_chaos_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ d) :
    ‖(modelChaosEps d n u hz hu i ε hε).chaos ω‖
      = ‖(modelChaos d n u hz i).chaos ω‖ / sqVq d n u z i ε ω := by
  rw [chaos_modelChaosEps hz hu i hε ω, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sqVq_pos (z := z) hu hε i ω).le]

/-- **Markov at fixed `ε`.** -/
theorem meas_lt_normSq_chaos_le_eps (hz : z.im ≠ 0) (hu : 0 ≤ u)
    (i : Idx (d.L n) (d.W n)) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (Sizes.seqP d)
        {ω | lam * (vqM d n u z i ω + ε) < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := modelChaosEps d n u hz hu i ε hε with hC'
  set Y : Sizes.SeqΩ d → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (Sizes.seqP d) := by
    simpa only [habs] using C'.integrable_norm_pow (gaussIBP d) (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(Sizes.seqP d)) ≤ hwConst q :=
    mom_modelChaosEps_le hz hu i hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(Sizes.seqP d) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := Sizes.seqP d) (Y := Y) ht hint hmom
  have hset : {ω | lam * (vqM d n u z i ω + ε) < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2}
      = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    have hs := sqVq_pos (z := z) hu hε i ω
    have hsq := sq_sqVq (z := z) hu hε i ω
    have hYv : Y ω = ‖(modelChaos d n u hz i).chaos ω‖ / sqVq d n u z i ε ω := by
      rw [hY, hC']; exact norm_chaos_modelChaosEps hz hu i hε ω
    have hc : (0 : ℝ) ≤ ‖(modelChaos d n u hz i).chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs, ← hsq]
    constructor
    · intro h
      nlinarith [h, hs, hc, hsl, hsln,
        sq_nonneg (Real.sqrt lam * sqVq d n u z i ε ω - ‖(modelChaos d n u hz i).chaos ω‖),
        sq_nonneg (Real.sqrt lam * sqVq d n u z i ε ω + ‖(modelChaos d n u hz i).chaos ω‖)]
    · intro h
      have hms := mul_self_lt_mul_self (mul_nonneg hsln hs.le) h
      nlinarith [hms, hsl, hs]
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

/-- **The tail bound with the true control.**  `{λV_q < |Q|²} = ⋃_m {λ(V_q + 1/(m+1)) < |Q|²}`
is an increasing union, so continuity of the measure from below removes `ε`: no integral limit
theorem, and no separate treatment of `{V_q = 0}`. -/
theorem meas_lt_normSq_chaos_le (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n))
    {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (Sizes.seqP d) {ω | lam * vqM d n u z i ω < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set S : ℕ → Set (Sizes.SeqΩ d) := fun m =>
    {ω | lam * (vqM d n u z i ω + 1 / ((m : ℝ) + 1))
      < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2} with hS
  have hmono : Monotone S := by
    intro m m' hmm ω hω
    simp only [hS, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmm' : ((m : ℝ) + 1) ≤ ((m' : ℝ) + 1) := by
        have : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm
        linarith
      exact one_div_le_one_div_of_le hm hmm'
    nlinarith [hω, h1, hlam]
  have hunion : (⋃ m, S m)
      = {ω | lam * vqM d n u z i ω < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      nlinarith [hm, hlam, hpos]
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (‖(modelChaos d n u hz i).chaos ω‖ ^ 2
          - lam * vqM d n u z i ω) / lam by
          apply div_pos _ hlam; linarith)
      refine ⟨m, ?_⟩
      rw [lt_div_iff₀ hlam] at hm
      nlinarith [hm]
  rw [← hunion]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := Sizes.seqP d) hmono)
    (Filter.Eventually.of_forall fun m => ?_)
  exact meas_lt_normSq_chaos_le_eps hz hu i hlam q (by positivity)

/-- With `u = 0` the flow is the zero matrix, so the chaos vanishes. -/
theorem chaos_modelChaos_zero (hz : z.im ≠ 0) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    (modelChaos d n 0 hz i).chaos ω = 0 := by
  have hh : ∀ k : {a : Idx (d.L n) (d.W n) // a ≠ i}, (modelChaos d n 0 hz i).h ω k = 0 := by
    intro k
    rw [modelChaos_h hz i ω k, Sizes.seqHflow_zero]
    rfl
  have hsg : ∀ k : {a : Idx (d.L n) (d.W n) // a ≠ i}, (modelChaos d n 0 hz i).sg k = 0 := by
    intro k
    rw [modelChaos_sg hz i le_rfl k]
    ring
  change (∑ k, ∑ l, _) - (∑ k, _) = 0
  rw [show (∑ k : {a : Idx (d.L n) (d.W n) // a ≠ i}, ∑ l : {a : Idx (d.L n) (d.W n) // a ≠ i},
        (modelChaos d n 0 hz i).h ω k * (modelChaos d n 0 hz i).B ω k l *
          (starRingEnd ℂ) ((modelChaos d n 0 hz i).h ω l)) = 0 from by
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
      rw [hh k]; ring,
    show (∑ k : {a : Idx (d.L n) (d.W n) // a ≠ i},
        (((modelChaos d n 0 hz i).sg k : ℝ) : ℂ) * (modelChaos d n 0 hz i).B ω k k) = 0 from by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hsg k]; simp]
  ring

/-! ### Relabelling the quadratic LDE from `Idx` to `BlockIndex`

The statement `hLquad` of `Green/EntryDom.lean` is on `BlockIndex L W` through
`blockMat`, `greenBlk`, `Sblk2`; the model lives on `Idx L W = Z2 (W * L)`.  These are the
`ldeQuadLHS`/`ldeQuadRHS` analogues of the private relabelling lemmas of `Green/LDE.lean`. -/

section Relabel

variable {m ν : Type*} [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν]

omit [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν] in
private theorem LDEQuadInst_greenMinor_submatrix (e : m ≃ ν) (G : Matrix ν ν ℂ) (a k l : m) :
    greenMinor (G.submatrix e e) a k l = greenMinor G (e a) (e k) (e l) := by
  simp [greenMinor]

private theorem LDEQuadInst_ldeQuadLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ)
    (S : ν → ν → ℝ) (t : ℝ) (a : m) :
    ldeQuadLHS (H.submatrix e e) (G.submatrix e e) (fun p q => S (e p) (e q)) t a
      = ldeQuadLHS H G S t (e a) := by
  have h1 : ∑ k ∈ univ.erase a, ∑ l ∈ univ.erase a,
        H.submatrix e e a k * greenMinor (G.submatrix e e) a k l * H.submatrix e e l a
      = ∑ k ∈ univ.erase (e a), ∑ l ∈ univ.erase (e a),
        H (e a) k * greenMinor G (e a) k l * H l (e a) := by
    refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
    refine Finset.sum_equiv e (fun l => by simp [Finset.mem_erase]) (fun l _ => ?_)
    simp [LDEQuadInst_greenMinor_submatrix]
  have h2 : ∑ k ∈ univ.erase a, ((S (e a) (e k) : ℝ) : ℂ) * greenMinor (G.submatrix e e) a k k
      = ∑ k ∈ univ.erase (e a), ((S (e a) k : ℝ) : ℂ) * greenMinor G (e a) k k := by
    refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
    simp [LDEQuadInst_greenMinor_submatrix]
  unfold ldeQuadLHS
  rw [h1, h2]

private theorem LDEQuadInst_ldeQuadRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ)
    (G : Matrix ν ν ℂ) (a : m) :
    ldeQuadRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a = ldeQuadRHS S G (e a) := by
  unfold ldeQuadRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  refine Finset.sum_equiv e (fun l => by simp [Finset.mem_erase]) (fun l _ => ?_)
  simp [LDEQuadInst_greenMinor_submatrix]

end Relabel

section RelabelBlock

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The block resolvent is the fine-lattice resolvent, relabelled by `splitEquiv`. -/
private theorem LDEQuadInst_greenBlk_true (E t : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
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

private theorem LDEQuadInst_Sblk2_fun :
    Sblk2 L W = fun p q => svar L W ((splitEquiv L W).symm p) ((splitEquiv L W).symm q) := by
  funext p q
  exact Sblk2_eq_svar p q

private theorem LDEQuadInst_blk_quadLHS (M : Matrix (Idx L W) (Idx L W) ℂ) (E t : ℝ)
    (a : BlockIndex L W) :
    ldeQuadLHS (blockMat M) (greenBlk L W E t M true) (Sblk2 L W) t a
      = ldeQuadLHS M (green M (spectralZ E t)) (svar L W) t ((splitEquiv L W).symm a) := by
  rw [LDEQuadInst_greenBlk_true, LDEQuadInst_Sblk2_fun]
  exact LDEQuadInst_ldeQuadLHS_submatrix (splitEquiv L W).symm M _ (svar L W) t a

private theorem LDEQuadInst_blk_quadRHS (M : Matrix (Idx L W) (Idx L W) ℂ) (E t : ℝ)
    (a : BlockIndex L W) :
    ldeQuadRHS (Sblk2 L W) (greenBlk L W E t M true) a
      = ldeQuadRHS (svar L W) (green M (spectralZ E t)) ((splitEquiv L W).symm a) := by
  rw [LDEQuadInst_greenBlk_true, LDEQuadInst_Sblk2_fun]
  exact LDEQuadInst_ldeQuadRHS_submatrix (splitEquiv L W).symm (svar L W) _ a

end RelabelBlock

/-! ### The hypothesis `hLquad` of `diag_bound_stochDom` -/

/-- The tail bound at one size and one index, with a deterministic threshold `s > 0` and
`0 ≤ u ≤ 1`, on the fine lattice. -/
private theorem LDEQuadInst_meas_le (hz : z.im ≠ 0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (i : Idx (d.L n) (d.W n)) {s : ℝ} (hs : 0 < s) (q : ℕ) :
    (Sizes.seqP d) {ω | s * ldeQuadRHS (svar (d.L n) (d.W n))
          (green (Sizes.seqHflow d n u ω) z) i
        < ldeQuadLHS (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z)
          (svar (d.L n) (d.W n)) u i}
      ≤ ENNReal.ofReal (hwConst q / s ^ (q + 1)) := by
  have hrhs : ∀ ω : Sizes.SeqΩ d,
      0 ≤ ldeQuadRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i := fun ω =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (svar_nonneg _ _ _ _) (by positivity)) (svar_nonneg _ _ _ _)
  rcases eq_or_lt_of_le hu0 with hu | hupos
  · -- `u = 0`: the chaos vanishes, so the failure event is empty
    subst hu
    have hempty : {ω : Sizes.SeqΩ d | s * ldeQuadRHS (svar (d.L n) (d.W n))
          (green (Sizes.seqHflow d n 0 ω) z) i
        < ldeQuadLHS (Sizes.seqHflow d n 0 ω) (green (Sizes.seqHflow d n 0 ω) z)
          (svar (d.L n) (d.W n)) 0 i} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [← modelChaos_normSq_chaos hz i le_rfl ω, chaos_modelChaos_zero hz i ω, norm_zero]
      have := hrhs ω
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      nlinarith
    rw [hempty, measure_empty]
    exact zero_le
  · set lam : ℝ := s / u ^ 2 with hlamdef
    have hlam : 0 < lam := by rw [hlamdef]; positivity
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hupos, hu1]
    have hlamge : s ≤ lam := by
      rw [hlamdef, le_div_iff₀ (by positivity)]
      nlinarith [hs, hu2]
    have hset : {ω : Sizes.SeqΩ d | s * ldeQuadRHS (svar (d.L n) (d.W n))
          (green (Sizes.seqHflow d n u ω) z) i
        < ldeQuadLHS (Sizes.seqHflow d n u ω) (green (Sizes.seqHflow d n u ω) z)
          (svar (d.L n) (d.W n)) u i}
        = {ω | lam * vqM d n u z i ω < ‖(modelChaos d n u hz i).chaos ω‖ ^ 2} := by
      ext ω
      have hL := modelChaos_normSq_chaos hz i hu0 ω
      have hV : vqM d n u z i ω
          = u ^ 2 * ldeQuadRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i := by
        rw [← vqM_eq hz hu0 i ω]; exact modelChaos_Vq hz i hu0 ω
      have hune : u ≠ 0 := ne_of_gt hupos
      simp only [Set.mem_ofPred_eq, ← hL, hV, hlamdef]
      rw [show s / u ^ 2 * (u ^ 2 *
          ldeQuadRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i)
          = s * ldeQuadRHS (svar (d.L n) (d.W n)) (green (Sizes.seqHflow d n u ω) z) i from by
        field_simp]
    rw [hset]
    refine (meas_lt_normSq_chaos_le hz hu0 i hlam q).trans (ENNReal.ofReal_le_ofReal ?_)
    have hden : s ^ (q + 1) ≤ lam ^ (q + 1) := pow_le_pow_left₀ hs.le hlamge (q + 1)
    exact div_le_div_of_nonneg_left (hwConst_pos q).le (by positivity) hden

/-- **The quadratic large deviation input `hLquad` of `diag_bound_stochDom`,** for the Gaussian
flow `H_{t_n}`:
`|∑_{k,l≠i} H_{ik}G^{(i)}_{kl}H_{li} − t_n∑_{k≠i}S_{ik}G^{(i)}_{kk}|²
  ≺ ∑_{k,l≠i}S_{ik}|G^{(i)}_{kl}|²S_{li}`,
uniformly in `i`, per time `t n` (the conclusion is the text of `hLquad`, in the per-time form,
so without the union bound). -/
theorem stochDom_ldeQuad (d : Sizes) {κ : ℝ} (hκ : 0 < κ) (hsz : RBM.Ind.SizeTendsto d)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i)
      (fun n i ω => ldeQuadRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i) := by
  have hsz' : Filter.Tendsto d.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  intro τ hτ D hD
  obtain ⟨q, hq⟩ := exists_nat_ge ((D + 1) / τ)
  have hDq : D + 1 ≤ τ * (q : ℝ) := by rw [div_le_iff₀ hτ] at hq; linarith
  have hexp : 0 < τ * ((q : ℝ) + 1) - D := by nlinarith
  filter_upwards [hsz'.eventually (eventually_le_rpow (hwConst q) hexp),
    hsz'.eventually_ge_atTop 1] with n hCN hn1 i
  have hz : (spectralZ (E n) (t n)).im ≠ 0 := zt_im_ne_zero hκ (hE n) (ht1 n)
  have hN0 : (0 : ℝ) < (d.size n : ℝ) := by exact_mod_cast hn1
  have hNτ : (0 : ℝ) < (d.size n : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 τ
  have hset : {ω : Sizes.SeqΩ d | (d.size n : ℝ) ^ τ *
        ldeQuadRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i
      < ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i}
      = {ω : Sizes.SeqΩ d | (d.size n : ℝ) ^ τ * ldeQuadRHS (svar (d.L n) (d.W n))
          (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)))
          ((splitEquiv (d.L n) (d.W n)).symm i)
        < ldeQuadLHS (Sizes.seqHflow d n (t n) ω)
          (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)))
          (svar (d.L n) (d.W n)) (t n) ((splitEquiv (d.L n) (d.W n)).symm i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, LDEQuadInst_blk_quadLHS, LDEQuadInst_blk_quadRHS]
  change (Sizes.seqP d) {ω : Sizes.SeqΩ d | (d.size n : ℝ) ^ τ *
        ldeQuadRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i
      < ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i} ≤ _
  rw [hset]
  refine (LDEQuadInst_meas_le hz (ht0 n) (ht1 n).le _ hNτ q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hpow : (d.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) = ((d.size n : ℝ) ^ τ) ^ (q + 1) := by
    rw [← Real.rpow_natCast ((d.size n : ℝ) ^ τ) (q + 1), ← Real.rpow_mul hN0.le]
    push_cast
    ring_nf
  calc hwConst q / ((d.size n : ℝ) ^ τ) ^ (q + 1)
      = hwConst q / (d.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) := by rw [hpow]
    _ ≤ (d.size n : ℝ) ^ (τ * ((q : ℝ) + 1) - D) / (d.size n : ℝ) ^ (τ * ((q : ℝ) + 1)) := by
        gcongr
    _ = (d.size n : ℝ) ^ (-D) := by
        rw [← Real.rpow_sub hN0]
        congr 1
        ring

end RBM.Green
