/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Markov
import RBM2D.Path.OneStep

/-!
# The one-step conditional drift on the walk

The one-step recursion `pathH_succ` of the grid walk, the complex-valued freezing lemma,
`condExp_loop_step` (the freezing lemma applied to a resolvent loop observable) and
`condExp_loop_drift` (the conditional drift of the loop observable along the grid walk).

* The loop observable `A ↦ 𝓛(blockMat A, z, I)` is neither bounded nor continuous on all
  matrices (the resolvent is unbounded off the Hermitian set).  The freezing lemma is therefore
  applied to the observable of the Hermitian part `LoopStep_herm A = ½ (A + Aᴴ)`, which is
  continuous (`continuous_green_of_isHermitian`) and bounded (`norm_gloop_le_crude`)
  everywhere, and agrees with the observable at every Hermitian matrix.
* The integral in `condExp_loop_step` is over the fixed-size law `P (d.L n) (d.W n)` with
  `Xmat`, as in `OneStepEnvelope`; the bridge is `Sizes.seqP_map_slice`.
* The drift is bounded by the one-step envelope `oneStepEnvelope` applied pointwise at
  `M = pathH k ω` (Hermitian).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

variable (d : Sizes)

/-! ### The one-step recursion -/

/-- **The grid walk one-step recursion** `H_{k+1} = H_k + √Δ X_{k+1}`. -/
theorem pathH_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    pathH d s t K n (k + 1) ω
      = pathH d s t K n k ω
        + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat d n (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold pathH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

/-! ### The complex-valued freezing lemma -/

section FreezeC

variable {d}

/-- The complex-valued freezing lemma.  `condExp_freeze` is real-valued; the complex case is its
real and imaginary parts, glued with `ContinuousLinearMap.comp_condExp_comm`. -/
private theorem LoopStep_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℂ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (Sizes.seqP d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (pathP d)) :
    (pathP d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[pathP d] fun ω => ∫ x, F (Y ω) x ∂(Sizes.seqP d) := by
  classical
  set f : PathΩ d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Sizes.SeqΩ d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Sizes.SeqΩ d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (pathP d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (pathP d) := hInt.im
  have hfreezeRe := condExp_freeze k hY hFre hIntRe
  have hfreezeIm := condExp_freeze k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((pathP d)[f | filt d k] ω))
      =ᵐ[pathP d] fun ω => ∫ x, Fre (Y ω) x ∂(Sizes.seqP d) := by
    have hRe' : (fun ω => RCLike.re ((pathP d)[f | filt d k] ω))
        =ᵐ[pathP d] (pathP d)[fun ω => Fre (Y ω) (ω (k + 1)) | filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((pathP d)[f | filt d k] ω))
      =ᵐ[pathP d] fun ω => ∫ x, Fim (Y ω) x ∂(Sizes.seqP d) := by
    have hIm' : (fun ω => RCLike.im ((pathP d)[f | filt d k] ω))
        =ᵐ[pathP d] (pathP d)[fun ω => Fim (Y ω) (ω (k + 1)) | filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(Sizes.seqP d) = RCLike.re (∫ x, F p x ∂(Sizes.seqP d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(Sizes.seqP d) = RCLike.im (∫ x, F p x ∂(Sizes.seqP d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((pathP d)[f | filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(Sizes.seqP d))
    rw [hωre, hreEq]
  · change RCLike.im ((pathP d)[f | filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(Sizes.seqP d))
    rw [hωim, himEq]

end FreezeC

/-! ### The observable of the Hermitian part: continuity and a global bound -/

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)`. -/
private def LoopStep_herm (A : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (Idx L W) (Idx L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem LoopStep_herm_isHermitian (A : Matrix (Idx L W) (Idx L W) ℂ) :
    (LoopStep_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem LoopStep_herm_of_isHermitian {A : Matrix (Idx L W) (Idx L W) ℂ}
    (hA : A.IsHermitian) : LoopStep_herm A = A := by
  unfold LoopStep_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem LoopStep_continuous_herm :
    Continuous (LoopStep_herm : Matrix (Idx L W) (Idx L W) ℂ → _) := by
  unfold LoopStep_herm
  have h1 : Continuous fun A : Matrix (Idx L W) (Idx L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix. -/
private def LoopStep_Phi (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : LoopIdx (Z2 L))
    (A : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  gloop L W (blockMat (LoopStep_herm A)) z I

/-- Continuity of a resolvent loop along a continuous Hermitian family
(`continuous_gloop_HflowBlock_sample` is stated only for `HflowBlock`). -/
private theorem LoopStep_continuous_gloop {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hf : Continuous f)
    (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    Continuous fun v => gloop L W (f v) z I := by
  have hG : ∀ σ : Bool, Continuous fun v => Gsig (f v) z σ := by
    intro σ
    cases σ with
    | true => exact continuous_green_of_isHermitian hf hh hz
    | false =>
        apply continuous_green_of_isHermitian hf hh
        simpa using hz
  have hfold : ∀ l : List (Bool × Z2 L), Continuous fun v =>
      l.foldr (fun p M => Gsig (f v) z p.1 * Eblk L W p.2 * M)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
    intro l
    induction l with
    | nil => exact continuous_const
    | cons p l ih => exact (((hG p.1).mul continuous_const)).mul ih
  exact (continuous_matrixTrace L W).comp (hfold (I.σ.zip I.a))

private theorem LoopStep_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    Continuous (LoopStep_Phi L W z I) := by
  unfold LoopStep_Phi
  exact LoopStep_continuous_gloop (f := fun A => blockMat (LoopStep_herm A))
    ((LoopStep_continuous_herm (L := L) (W := W)).matrix_submatrix _ _)
    (fun A => (LoopStep_herm_isHermitian A).submatrix _) hz I

private theorem LoopStep_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hwf : I.WF)
    (A : Matrix (Idx L W) (Idx L W) ℂ) :
    ‖LoopStep_Phi L W z I A‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) * (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
  norm_gloop_le_crude L W ((LoopStep_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl I hwf

private theorem LoopStep_isHermitian_add_smul {p X : Matrix (Idx L W) (Idx L W) ℂ}
    (hp : p.IsHermitian) (hX : X.IsHermitian) (r : ℝ) :
    (p + (r : ℂ) • X).IsHermitian :=
  hp.add (hX.smul (by simp [IsSelfAdjoint]))

end Observable

/-! ### The one-step conditional expectation -/

/-- A private copy of the (private) `StandardBorelSpace` instance of `Markov.lean`. -/
private instance LoopStep_instStandardBorelSpaceMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ))

/-- The grid walk is `filt d k`-measurable as a matrix-valued map (entrywise from
`pathH_adapted`). -/
private theorem LoopStep_measurable_pathH_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt d k] (pathH d s t K n k) :=
  @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun j =>
      (pathH_adapted d s t K n k i j).measurable

/-- The freezing lemma applied to the one-step recursion `pathH_succ`, for the loop observable
`Φ_{u_{k+1}} = 𝓛(blockMat ·, z_{u_{k+1}}, I)`.  The right side is the Gaussian integral over the
fixed-size law `P (d.L n) (d.W n)`, as in `OneStepEnvelope`. -/
theorem condExp_loop_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF) (hu1 : gridTime s t K n (k + 1) < 1) :
    (pathP d)[fun ω : PathΩ d =>
        gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (k + 1) ω))
          (spectralZ E (gridTime s t K n (k + 1))) I | filt d k]
      =ᵐ[pathP d] fun ω =>
        ∫ x, gloop (d.L n) (d.W n)
          (blockMat (pathH d s t K n k ω
            + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat (d.L n) (d.W n) x))
          (spectralZ E (gridTime s t K n (k + 1))) I ∂(P (d.L n) (d.W n)) := by
  classical
  have hz : (spectralZ E (gridTime s t K n (k + 1))).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (sub_pos.2 hu1) (spectralM_im_pos hE)).ne'
  set z : ℂ := spectralZ E (gridTime s t K n (k + 1)) with hzdef
  set Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ :=
    LoopStep_Phi (d.L n) (d.W n) z I with hΦdef
  have hΦcont : Continuous Φ := LoopStep_continuous_Phi hz I
  set F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℂ :=
    fun p x => Φ (p + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat d n x) with hFdef
  have hXmeas : Measurable (Sizes.seqXmat d n) :=
    (continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)
  have hFmeas : Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
      Sizes.SeqΩ d => F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ d =>
        (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat d n x :=
      hXmeas.const_smul (Real.sqrt (gridStep s t K n) : ℂ)
    have h3 : Measurable fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
        Sizes.SeqΩ d => p.1 + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat d n p.2 :=
      measurable_fst.add (h2.comp measurable_snd)
    have h4 := hΦcont.measurable.comp h3
    exact h4
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) *
      (|z.im|⁻¹ * (((d.W n : ℕ) : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
    fun p x => LoopStep_norm_Phi_le hz hwf _
  have hYmeas : Measurable[filt d k] (pathH d s t K n k) :=
    LoopStep_measurable_pathH_filt d s t K n k
  have hYmeas' : Measurable (pathH d s t K n k) := hYmeas.mono ((filt d).le k) le_rfl
  have hFInt : ∀ p, Integrable (F p) (Sizes.seqP d) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ d => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm : Measurable (fun x : Sizes.SeqΩ d => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ d => F (pathH d s t K n k ω) (ω (k + 1)))
      (pathP d) := by
    have hm : Measurable (fun ω : PathΩ d => F (pathH d s t K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω : PathΩ d => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (k + 1) ω)) z I)
      = fun ω => F (pathH d s t K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (pathH d s t K n (k + 1) ω).IsHermitian := pathH_isHermitian d s t K n (k + 1) ω
    change _ = LoopStep_Phi (d.L n) (d.W n) z I _
    rw [← pathH_succ d s t K n k ω]
    unfold LoopStep_Phi
    rw [LoopStep_herm_of_isHermitian hH]
  rw [hEq]
  filter_upwards [LoopStep_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget] with ω hω
  rw [hω]
  have hp : (pathH d s t K n k ω).IsHermitian := pathH_isHermitian d s t K n k ω
  set f : Ω (d.L n) (d.W n) → ℂ := fun y =>
    gloop (d.L n) (d.W n)
      (blockMat (pathH d s t K n k ω
        + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat (d.L n) (d.W n) y)) z I with hfdef
  have hfeq : f = fun y => Φ (pathH d s t K n k ω
      + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat (d.L n) (d.W n) y) := by
    funext y
    have hh := LoopStep_isHermitian_add_smul hp (Xmat_isHermitian (d.L n) (d.W n) y)
      (Real.sqrt (gridStep s t K n))
    simp only [hΦdef, LoopStep_Phi, LoopStep_herm_of_isHermitian hh, hfdef]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω (d.L n) (d.W n) =>
        (Real.sqrt (gridStep s t K n) : ℂ) • Xmat (d.L n) (d.W n) y :=
      (continuous_Xmat (d.L n) (d.W n)).const_smul (Real.sqrt (gridStep s t K n) : ℂ)
    exact hΦcont.comp (continuous_const.add h2)
  have hFf : ∀ x, F (pathH d s t K n k ω) x = f (Sizes.slice d n x) := by
    intro x
    have hh := LoopStep_isHermitian_add_smul hp (Sizes.seqXmat_isHermitian d n x)
      (Real.sqrt (gridStep s t K n))
    simp only [hFdef, hΦdef, LoopStep_Phi, LoopStep_herm_of_isHermitian hh, hfdef]
    rfl
  calc ∫ x, F (pathH d s t K n k ω) x ∂(Sizes.seqP d)
      = ∫ x, f (Sizes.slice d n x) ∂(Sizes.seqP d) := by simp only [hFf]
    _ = ∫ y, f y ∂((Sizes.seqP d).map (Sizes.slice d n)) :=
        (integral_map (Sizes.measurable_slice d n).aemeasurable
          hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(P (d.L n) (d.W n)) := by rw [Sizes.seqP_map_slice]

/-! ### The one-step conditional drift -/

/-- **The conditional drift** of the loop observable along the grid walk, bounded by the
one-step envelope (`oneStepEnvelope`) applied pointwise at `M = pathH k ω`, with right side
`envConst`.  The hypotheses `_hK`, `_hk` are not used by the proof. -/
theorem condExp_loop_drift (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (_hK : K n ≠ 0) (_hk : k < K n) (hu1 : gridTime s t K n (k + 1) < 1) :
    ∀ᵐ ω ∂(pathP d),
      ‖(pathP d)[fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (k + 1) ω'))
              (spectralZ E (gridTime s t K n (k + 1))) I | filt d k] ω
          - gloop (d.L n) (d.W n) (blockMat (pathH d s t K n k ω))
              (spectralZ E (gridTime s t K n k)) I
          - (gridStep s t K n : ℂ) * genMat E (gridTime s t K n k) (pathH d s t K n k ω) I‖
        ≤ envConst (d.L n) (d.W n) E I.length (gridTime s t K n (k + 1))
            * gridStep s t K n ^ ((3 : ℝ) / 2) := by
  filter_upwards [condExp_loop_step d s t K n k E hE hwf hu1] with ω hω
  rw [hω]
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  have hu : gridTime s t K n (k + 1) = gridTime s t K n k + gridStep s t K n := by
    unfold gridTime
    push_cast
    ring
  have hu0 : 0 ≤ gridTime s t K n k := by
    unfold gridTime
    positivity
  have key := oneStepEnvelope (d.L n) (d.W n) E hE I hwf (gridTime s t K n k)
    (gridStep s t K n) hu0 hΔ (hu ▸ hu1) (pathH d s t K n k ω)
    (pathH_isHermitian d s t K n k ω)
  rw [← hu] at key
  exact key

end RBM.Path

end
