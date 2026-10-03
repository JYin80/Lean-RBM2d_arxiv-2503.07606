/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpVocab
import RBM2D.Hierarchy.LoopHierarchyCutContinuity
import RBM2D.Gauss.LoopGeneratorExpectation
import RBM2D.Gauss.LoopExpectationDerivative
import RBM2D.Loop.TreeRep

/-!
# The expected hierarchy at `n = 2` (`ExpHierPin` of `ML:exp`)

Paper: Section 1 (`ML:exp`, `eq:step6main`) and Sections 5-6 (`eq_L-Keee`, `LK_SDE`,
Step 6 proof of `lemma:step6-1`).
Namespace `RBM.Evol`, `variable (d : Sizes)`.

**Statement** `expHierPin d : ExpHierPin d` (the statement of `Evolution/MLExpVocab.lean`).

## Argument

1. Fixed size (`L`, `W`, measure `P L W`).  A regularity class `Good b F` for a family
   `F u ω` on the window `u ∈ [0, b]`, `b < 1` (continuous in `ω`, continuous in `u`, uniformly
   bounded) is closed under sums, products and deterministic continuous coefficients; it contains
   the loop values `𝓛_u(J)` and `(𝓛 - 𝒦)_u(J)`; `Good b F` gives integrability and continuity of
   `u ↦ 𝔼 F u`.  This gives continuity of `𝔼𝓛` and of the drift `D_u` on `[0, 1)`, **including
   `u = 0`** (the drift identity holds on the open window only).
2. Samplewise bridge (`0 < u < 1`): the Gaussian second derivative of the flow sample in the
   coordinate `ω_c` carries the factor `u` (`H_u = √u X`), so the samplewise cut
   expression (`samplewiseLoopGeneratorCuts`) equals the one-step generator
   `genMat E u (H_u)`.  With `hierarchyN_two` (`Ind.hierarchyN` at `k = 2`, built on
   `loopGenN`) and `deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts` this
   is `∂_u 𝔼𝓛 = ∂_u 𝒦 + 𝔼 ϴ(𝓛-𝒦) + 𝔼(elklkN + egtN)`.
3. Expectation of the linear terms (`ϴ` is a finite linear combination, `𝒦` deterministic,
   probability measure), transfer from `P L W` to the common space `seqP d` (`seqP_map_slice`).

Helpers are prefixed `MLExpHier_` and private.  Two private helpers of other files are copied
under a different name: `LoopGenN_hasDerivAt_Gsig_spec` and
`MLExpDrift_elklkN_two`, `MLExpDrift_egtN_two` (`Evolution/MLExpDrift.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. The regularity class `Good` -/

section Good

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A family `F u ω` is regular on `[0, b]`: continuous in the sample, continuous in the time, and
uniformly bounded. -/
private structure MLExpHier_Good (L W : ℕ) [NeZero L] [NeZero W] (b : ℝ)
    (F : ℝ → Ω L W → ℂ) : Prop where
  cont_ω : ∀ u ∈ Set.Icc (0 : ℝ) b, Continuous (F u)
  cont_u : ∀ ω : Ω L W, ContinuousOn (fun u => F u ω) (Set.Icc 0 b)
  bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0 : ℝ) b, ∀ ω : Ω L W, ‖F u ω‖ ≤ B

private theorem MLExpHier_Good_add {b : ℝ} {F G : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) (hG : MLExpHier_Good L W b G) :
    MLExpHier_Good L W b (fun u ω => F u ω + G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).add (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).add (hG.cont_u ω), B₁ + B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (h₁ u hu ω) (h₂ u hu ω))

private theorem MLExpHier_Good_sub {b : ℝ} {F G : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) (hG : MLExpHier_Good L W b G) :
    MLExpHier_Good L W b (fun u ω => F u ω - G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).sub (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).sub (hG.cont_u ω), B₁ + B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (h₁ u hu ω) (h₂ u hu ω))

private theorem MLExpHier_Good_mul {b : ℝ} {F G : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) (hG : MLExpHier_Good L W b G) :
    MLExpHier_Good L W b (fun u ω => F u ω * G u ω) := by
  obtain ⟨B₁, hB₁, h₁⟩ := hF.bdd
  obtain ⟨B₂, hB₂, h₂⟩ := hG.bdd
  refine ⟨fun u hu => (hF.cont_ω u hu).mul (hG.cont_ω u hu),
    fun ω => (hF.cont_u ω).mul (hG.cont_u ω), B₁ * B₂, by positivity, fun u hu ω => ?_⟩
  exact (norm_mul_le _ _).trans
    (mul_le_mul (h₁ u hu ω) (h₂ u hu ω) (norm_nonneg _) hB₁)

/-- A deterministic coefficient continuous on the window. -/
private theorem MLExpHier_Good_coef {b : ℝ} (c : ℝ → ℂ) (hc : ContinuousOn c (Set.Icc 0 b)) :
    MLExpHier_Good L W b (fun u _ => c u) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨fun u _ => continuous_const, fun _ => hc, max C 0, le_max_right _ _,
    fun u hu _ => (hC u hu).trans (le_max_left _ _)⟩

private theorem MLExpHier_Good_const {b : ℝ} (c : ℂ) :
    MLExpHier_Good L W b (fun _ _ => c) :=
  MLExpHier_Good_coef (fun _ => c) continuousOn_const

private theorem MLExpHier_Good_sum {ι : Type*} {b : ℝ} (s : Finset ι)
    (F : ι → ℝ → Ω L W → ℂ) (h : ∀ i ∈ s, MLExpHier_Good L W b (F i)) :
    MLExpHier_Good L W b (fun u ω => ∑ i ∈ s, F i u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MLExpHier_Good_const (L := L) (W := W) (b := b) 0
  | insert i s hi ih =>
      have h1 := h i (Finset.mem_insert_self i s)
      have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using MLExpHier_Good_add h1 h2

/-- The loop value along the spectral path is regular on `[0, b]`, `b < 1`. -/
private theorem MLExpHier_Good_gloop {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (J : LoopIdx (Z2 L)) :
    MLExpHier_Good L W b (fun u ω => gloop L W (HflowBlock L W u ω) (spectralZ E u) J) := by
  have hη : 0 < (1 - b) * (spectralM E).im := mul_pos (by linarith) (spectralM_im_pos hE)
  have hlow : ∀ u ∈ Set.Icc (0 : ℝ) b, (1 - b) * (spectralM E).im ≤ |(spectralZ E u).im| :=
    fun u hu => spectralZ_im_gap hE hb hu
  have hzim : ∀ u ∈ Set.Icc (0 : ℝ) b, (spectralZ E u).im ≠ 0 := fun u hu =>
    abs_pos.mp (hη.trans_le (hlow u hu))
  refine ⟨fun u hu => (continuous_matrixTrace L W).comp
      (continuous_gloopProd_HflowBlock_sample L W u (hzim u hu) J),
    fun ω => continuousOn_gloop_any_window L W hb0 ω (continuous_spectralZ E) hzim J,
    (Fintype.card (BlockIndex L W) : ℝ) *
      (((1 - b) * (spectralM E).im)⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (J.σ.zip J.a).length,
    by positivity, fun u hu ω => ?_⟩
  exact norm_gloop_any_window_le L W hη hlow J hu ω

/-- Regularity gives integrability at every time of the window. -/
private theorem MLExpHier_Good_integrable {b : ℝ} {F : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) b) :
    Integrable (F u) (P L W) := by
  obtain ⟨B, hB, h⟩ := hF.bdd
  exact Integrable.of_bound (hF.cont_ω u hu).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => h u hu ω)

/-- Regularity gives continuity of the expectation on the window. -/
private theorem MLExpHier_Good_continuousOn_integral {b : ℝ} {F : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) :
    ContinuousOn (fun u => ∫ ω, F u ω ∂(P L W)) (Set.Icc 0 b) := by
  obtain ⟨B, hB, h⟩ := hF.bdd
  exact MeasureTheory.continuousOn_of_dominated
    (fun u hu => (hF.cont_ω u hu).measurable.aestronglyMeasurable)
    (fun u hu => Filter.Eventually.of_forall fun ω => h u hu ω)
    (integrable_const B) (Filter.Eventually.of_forall fun ω => hF.cont_u ω)

/-- Transport of regularity along a pointwise equality. -/
private theorem MLExpHier_Good_congr {b : ℝ} {F G : ℝ → Ω L W → ℂ}
    (hF : MLExpHier_Good L W b F) (h : ∀ u ω, F u ω = G u ω) : MLExpHier_Good L W b G := by
  have : G = F := by funext u ω; exact (h u ω).symm
  rw [this]; exact hF

end Good

/-! ## 2. The `n = 2` drift as a window sum, and its regularity -/

section Drift

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Σ_{x,y} A_x S^{(B)}_{xy} B_y`. -/
private def MLExpHier_sbSum (A B : Z2 L → ℂ) : ℂ := ∑ x : Z2 L, ∑ y : Z2 L, A x * SB L x y * B y

/-- At length `2` the sum `𝓔^{LK×LK}` has the single cut `(1,2)`. -/
private theorem MLExpHier_elklkN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    elklkN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * MLExpHier_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u M (loopOf σ ![a 0, y])) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold elklkN MLExpHier_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : Finset.Ioc 1 2 = {2} := by decide
  have h3 : Finset.Ioc 2 2 = ∅ := by decide
  rw [h1, Finset.sum_pair (by norm_num), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  rfl

/-- At length `2` the sum `𝓔^{(G̃)}` has the two cuts `k = 1, 2`. -/
private theorem MLExpHier_egtN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    egtN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * (MLExpHier_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpHier_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold egtN MLExpHier_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num)]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rfl

/-- `⟨G̃(σ) E_a⟩ = 𝓛_{⟨[σ],[a]⟩} - m(σ)`. -/
private theorem MLExpHier_avgErr_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool)
    (x : Z2 L) :
    avgErr L W E u M s x = gloop L W (blockMat M) (spectralZ E u) ⟨[s], [x]⟩ - KLoop.mSig E s := by
  rw [avgErr, greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, trace_Eblk_eq_one, smul_eq_mul, mul_one]
  simp [gloop, gloopProd]

private theorem MLExpHier_loopOf_wf {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).WF := by
  change (List.ofFn σ).length = (List.ofFn a).length
  simp

private theorem MLExpHier_loopOf_length {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- `𝒦(J)` is continuous on `[0,1)` for a well-formed loop of length `≥ 2`
(`isPrimitive_Kcal`, the equation `pro_dyncalK`). -/
private theorem MLExpHier_Kcal_continuousOn (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h2 : 2 ≤ J.length) :
    ContinuousOn (fun u : ℝ => KLoop.Kcal L W E u J) (Set.Ico 0 1) := by
  have hW : 1 ≤ W := Nat.pos_of_ne_zero (NeZero.ne W)
  intro t ht
  exact ((KLoop.isPrimitive_Kcal L W hL hW E hE).1 t ht J hJ h2).continuousAt.continuousWithinAt

/-- `(𝓛-𝒦)_u(J)` is regular on `[0,b]`. -/
private theorem MLExpHier_Good_LKf (hL : 3 ≤ L) {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b)
    (hb : b < 1) (J : LoopIdx (Z2 L)) (hJ : J.WF) (h2 : 2 ≤ J.length) :
    MLExpHier_Good L W b (fun u ω => LKf L W E u (Hflow L W u ω) J) := by
  have hK : ContinuousOn (fun u => KLoop.Kcal L W E u J) (Set.Icc 0 b) :=
    (MLExpHier_Kcal_continuousOn (W := W) hL hE J hJ h2).mono
      (fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hb⟩)
  exact MLExpHier_Good_sub (MLExpHier_Good_gloop hE hb0 hb J)
    (MLExpHier_Good_coef _ hK)

/-- `𝓛_u(J)` at the flow sample is regular on `[0,b]`. -/
private theorem MLExpHier_Good_LLf {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (J : LoopIdx (Z2 L)) :
    MLExpHier_Good L W b (fun u ω => LLf L W E u (Hflow L W u ω) J) :=
  MLExpHier_Good_gloop hE hb0 hb J

private theorem MLExpHier_Good_avgErr {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b) (hb : b < 1)
    (s : Bool) (x : Z2 L) :
    MLExpHier_Good L W b (fun u ω => avgErr L W E u (Hflow L W u ω) s x) := by
  refine MLExpHier_Good_congr (F := fun u ω => gloop L W (HflowBlock L W u ω) (spectralZ E u)
    ⟨[s], [x]⟩ - KLoop.mSig E s) (MLExpHier_Good_sub (MLExpHier_Good_gloop hE hb0 hb _)
      (MLExpHier_Good_const _)) fun u ω => ?_
  exact (MLExpHier_avgErr_eq E u (Hflow L W u ω) s x).symm

private theorem MLExpHier_Good_sbSum {b : ℝ} (A B : Z2 L → ℝ → Ω L W → ℂ)
    (hA : ∀ x, MLExpHier_Good L W b (A x)) (hB : ∀ y, MLExpHier_Good L W b (B y)) :
    MLExpHier_Good L W b (fun u ω => MLExpHier_sbSum (fun x => A x u ω) (fun y => B y u ω)) := by
  unfold MLExpHier_sbSum
  refine MLExpHier_Good_sum _ _ fun x _ => MLExpHier_Good_sum _ _ fun y _ => ?_
  exact MLExpHier_Good_mul (MLExpHier_Good_mul (hA x) (MLExpHier_Good_const _)) (hB y)

/-- The drift integrand `elklkN + egtN` at `n = 2` is regular on `[0,b]`. -/
private theorem MLExpHier_Good_drift (hL : 3 ≤ L) {E b : ℝ} (hE : |E| < 2) (hb0 : 0 ≤ b)
    (hb : b < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    MLExpHier_Good L W b (fun u ω => elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
      egtN L W E u (Hflow L W u ω) (loopOf σ a)) := by
  have hW2 : MLExpHier_Good L W b (fun _ _ => (W : ℂ) ^ 2) := MLExpHier_Good_const _
  have hlk : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Z2 L),
      MLExpHier_Good L W b (fun u ω => LKf L W E u (Hflow L W u ω) (loopOf σ' a')) := fun σ' a' =>
    MLExpHier_Good_LKf hL hE hb0 hb _ (MLExpHier_loopOf_wf _ _)
      (by rw [MLExpHier_loopOf_length])
  have h1 : MLExpHier_Good L W b (fun u ω => elklkN L W E u (Hflow L W u ω) (loopOf σ a)) := by
    refine MLExpHier_Good_congr (F := fun u ω => (W : ℂ) ^ 2 *
      MLExpHier_sbSum (fun x => LKf L W E u (Hflow L W u ω) (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u (Hflow L W u ω) (loopOf σ ![a 0, y]))) (MLExpHier_Good_mul hW2
          (MLExpHier_Good_sbSum (fun x u ω => LKf L W E u (Hflow L W u ω) (loopOf σ ![x, a 1]))
            (fun y u ω => LKf L W E u (Hflow L W u ω) (loopOf σ ![a 0, y]))
            (fun x => hlk σ _) (fun y => hlk σ _))) fun u ω => ?_
    exact (MLExpHier_elklkN_two E u (Hflow L W u ω) σ a).symm
  have h2 : MLExpHier_Good L W b (fun u ω => egtN L W E u (Hflow L W u ω) (loopOf σ a)) := by
    refine MLExpHier_Good_congr (F := fun u ω => (W : ℂ) ^ 2 *
      (MLExpHier_sbSum (fun x => avgErr L W E u (Hflow L W u ω) (σ 0) x)
          (fun y => LLf L W E u (Hflow L W u ω) (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpHier_sbSum (fun x => avgErr L W E u (Hflow L W u ω) (σ 1) x)
          (fun y => LLf L W E u (Hflow L W u ω) (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))))
      (MLExpHier_Good_mul hW2 (MLExpHier_Good_add
        (MLExpHier_Good_sbSum (fun x u ω => avgErr L W E u (Hflow L W u ω) (σ 0) x)
          (fun y u ω => LLf L W E u (Hflow L W u ω) (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))
          (fun x => MLExpHier_Good_avgErr hE hb0 hb _ _) (fun y => MLExpHier_Good_LLf hE hb0 hb _))
        (MLExpHier_Good_sbSum (fun x u ω => avgErr L W E u (Hflow L W u ω) (σ 1) x)
          (fun y u ω => LLf L W E u (Hflow L W u ω) (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))
          (fun x => MLExpHier_Good_avgErr hE hb0 hb _ _) (fun y => MLExpHier_Good_LLf hE hb0 hb _))))
      fun u ω => ?_
    exact (MLExpHier_egtN_two E u (Hflow L W u ω) σ a).symm
  exact MLExpHier_Good_add h1 h2

end Drift

/-! ## 3. The samplewise bridge: `genMat E u (H_u) = ` the cut expression (`u > 0`) -/

section Bridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The line `y ↦ blockMat (H_u + y X_c)` is the coordinate line of the flow block. -/
private theorem MLExpHier_blockMat_line (u : ℝ) (ω : Ω L W) (c : Coord L W) (y : ℝ) :
    blockMat (Hflow L W u ω + (y : ℂ) • coordinateMatrix L W c) =
      HflowBlock L W u ω + y • coordinateBlock L W c := by
  ext i j
  simp [blockMat, HflowBlock, coordinateBlock, Matrix.submatrix_apply, Complex.real_smul]

/-- **The factor `u` of the second derivative** (`H_u = √u X`): the coordinate Hessian of the flow
sample at time `u` is `u` times the line Hessian of `y ↦ 𝓛(H_u + y X_c)` at `y = 0`. -/
private theorem MLExpHier_second_deriv {u : ℝ} (hu : 0 < u) (ω : Ω L W) (c : Coord L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (Hflow L W u ω + (y : ℂ) • coordinateMatrix L W c)) z I)) 0 =
      (u : ℂ)⁻¹ * Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)) := by
  set s : ℝ := Real.sqrt u with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu
  have hss : s * s = u := Real.mul_self_sqrt hu.le
  set g : ℝ → ℂ := fun t => gloop L W (HflowBlock L W u (Function.update ω c t)) z I with hg
  set f : ℝ → ℂ := fun y => gloop L W
    (blockMat (Hflow L W u ω + (y : ℂ) • coordinateMatrix L W c)) z I with hf
  have hfg : f = fun y => g (ω c + s⁻¹ * y) := by
    funext y
    simp only [hf, hg, MLExpHier_blockMat_line, HflowBlock_update]
    congr 2
    rw [show ω c + s⁻¹ * y - ω c = s⁻¹ * y by ring, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
  have hg1 : ∀ t, HasDerivAt g (Matrix.trace (coordinateWordDeriv L W u (Function.update ω c t) c z
      (I.σ.zip I.a))) t := by
    intro t
    have h := hasDerivAt_gloop_update L W u (Function.update ω c t) c hz I hI
    have hpoint : (Function.update ω c t) c = t := by simp
    rw [hpoint] at h
    have hpath : (fun s : ℝ => gloop L W
        (HflowBlock L W u (Function.update (Function.update ω c t) c s)) z I) = g := by
      funext s'
      simp [hg, Function.update_idem]
    rw [hpath] at h
    exact h
  have hg1' : ∀ t, HasDerivAt g (deriv g t) t := fun t => (hg1 t).differentiableAt.hasDerivAt
  have hg2 : HasDerivAt (fun t => deriv g t)
      (Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) (ω c) :=
    hasDerivAt_deriv_gloop_update L W u ω c hz I hI
  have hin : ∀ y : ℝ, HasDerivAt (fun y : ℝ => ω c + s⁻¹ * y) s⁻¹ y := fun y => by
    simpa using ((hasDerivAt_id y).const_mul s⁻¹).const_add (ω c)
  have h1 : ∀ y, HasDerivAt f (s⁻¹ • deriv g (ω c + s⁻¹ * y)) y := fun y => by
    rw [hfg]
    exact (hg1' (ω c + s⁻¹ * y)).scomp y (hin y)
  have hderiv : deriv f = fun y => s⁻¹ • deriv g (ω c + s⁻¹ * y) := by
    funext y; exact (h1 y).deriv
  have h2 : HasDerivAt (fun y : ℝ => deriv g (ω c + s⁻¹ * y))
      (s⁻¹ • Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) 0 := by
    have hg2' : HasDerivAt (fun t => deriv g t)
        (Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)))
        (ω c + s⁻¹ * (0 : ℝ)) := by simpa using hg2
    exact hg2'.scomp (0 : ℝ) (hin 0)
  have h3 : HasDerivAt (fun y : ℝ => s⁻¹ • deriv g (ω c + s⁻¹ * y))
      (s⁻¹ • s⁻¹ • Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))) 0 :=
    h2.const_smul s⁻¹
  change deriv (deriv f) 0 = _
  rw [hderiv, h3.deriv]
  have hu' : (u : ℂ) = (s : ℂ) * (s : ℂ) := by rw [← Complex.ofReal_mul, hss]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [hu']
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix
(as the private `LoopGenN_hasDerivAt_Gsig_spec`, `Induction/LoopGenN.lean`). -/
private theorem MLExpHier_hasDerivAt_Gsig {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gsig H (spectralZ E v) σ)
      (-(Gsig H (spectralZ E u) σ *
        (spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
        Gsig H (spectralZ E u) σ)) u := by
  have him : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) (hasDerivAt_spectralZ E u) hH him
      simpa only [Gsig_true, spectralMSign, ite_true, zero_sub, neg_smul, neg_neg,
        Matrix.mul_neg, Matrix.neg_mul] using h
  | false =>
      have hz : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (spectralZ E v))
          (-((starRingEnd ℂ) (spectralM E))) u := by
        simpa using (hasDerivAt_spectralZ E u).star
      have him' : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by simpa using him
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) hz hH him'
      simpa only [Gsig_false, spectralMSign, Bool.false_eq_true, ite_false, zero_sub, neg_smul,
        neg_neg, Matrix.mul_neg, Matrix.neg_mul] using h

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of a signed word at the flow block `H_u` is the recursive
`spectralWordDeriv`. -/
private theorem MLExpHier_hasDerivAt_word (ω : Ω L W) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (l : List (Bool × Z2 L)) :
    HasDerivAt (fun v : ℝ => l.foldr (fun q M =>
        Gsig (HflowBlock L W u ω) (spectralZ E v) q.1 * Eblk L W q.2 * M) 1)
      (spectralWordDeriv L W ω E u l) u := by
  induction l with
  | nil =>
      simpa [spectralWordDeriv] using
        hasDerivAt_const u (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have h := ((MLExpHier_hasDerivAt_Gsig (HflowBlock_isHermitian L W u ω) hE hu
        p.1).mul_const (Eblk L W p.2)).mul ih
      refine h.congr_deriv ?_
      simp only [spectralWordDeriv, gsigSpectralFlowDeriv]

open scoped Matrix.Norms.L2Operator in
/-- The spectral derivative of a loop at the fixed flow block `H_u`. -/
private theorem MLExpHier_deriv_spec (ω : Ω L W) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (I : LoopIdx (Z2 L)) :
    deriv (fun v : ℝ => gloop L W (HflowBlock L W u ω) (spectralZ E v) I) u =
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) := by
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u (MLExpHier_hasDerivAt_word ω hE hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => gloop L W (HflowBlock L W u ω) (spectralZ E v) I) =
      fun v : ℝ => Matrix.trace (((I.σ.zip I.a)).foldr (fun q M =>
        Gsig (HflowBlock L W u ω) (spectralZ E v) q.1 * Eblk L W q.2 * M) 1) := by
    funext v
    rfl
  rw [hfun]
  exact h.deriv

/-- **The samplewise bridge** (`0 < u < 1`): the one-step generator at the flow sample `H_u` is the
samplewise cut expression (Hessian factor `u`, `MLExpHier_second_deriv`, and the spectral
drift, `MLExpHier_deriv_spec`). -/
private theorem MLExpHier_genMat_eq_cuts {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (ω : Ω L W) (I : LoopIdx (Z2 L)) (hI : I.WF) :
    genMat E u (Hflow L W u ω) I = samplewiseLoopGeneratorCuts L W ω E u I := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  rw [← samplewise_loop_generator_eq_cuts L W ω hu hu1 I hI]
  unfold genMat
  simp only [MLExpHier_second_deriv hu ω _ hz I hI]
  have h2 := MLExpHier_deriv_spec (E := E) (u := u) ω hE hu1 I
  have h3 : deriv (fun v : ℝ => gloop L W (blockMat (Hflow L W u ω)) (spectralZ E v) I) u =
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) := h2
  rw [h3]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  field_simp

end Bridge

/-! ## 4. The expected hierarchy at a fixed size -/

section FixedSize

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `𝔼 (𝓛-𝒦)_u(J)` is `𝔼𝓛_u(J) - 𝒦_u(J)` (probability measure). -/
private theorem MLExpHier_integral_LKf {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h2 : 2 ≤ J.length) (hL : 3 ≤ L) :
    ∫ ω, LKf L W E u (Hflow L W u ω) J ∂(P L W) =
      (∫ ω, gloop L W (HflowBlock L W u ω) (spectralZ E u) J ∂(P L W)) -
        KLoop.Kcal L W E u J := by
  have hg := MLExpHier_Good_integrable
    (MLExpHier_Good_gloop (L := L) (W := W) (E := E) hE hu0 hu1 J) (u := u) ⟨hu0, le_rfl⟩
  change ∫ ω, (gloop L W (HflowBlock L W u ω) (spectralZ E u) J - KLoop.Kcal L W E u J) ∂(P L W) = _
  rw [integral_sub hg (integrable_const _)]
  simp

/-- The expectation of `ϴ_{u,σ}` of a family of integrable tensors is `ϴ_{u,σ}` of the expectation. -/
private theorem MLExpHier_integral_thetaSig (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L)
    (Φ : Ω L W → (Fin 2 → Z2 L) → ℂ) (hΦ : ∀ b, Integrable (fun ω => Φ ω b) (P L W)) :
    ∫ ω, thetaSig L E σ u (Φ ω) a ∂(P L W) =
      thetaSig L E σ u (fun b => ∫ ω, Φ ω b ∂(P L W)) a := by
  unfold thetaSig
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun b _ => (hΦ _).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

/-- A function continuous on every `[0,b]`, `b < 1`, is continuous on `[0,1)`. -/
private theorem MLExpHier_continuousOn_Ico {F : ℝ → ℂ}
    (h : ∀ b : ℝ, 0 ≤ b → b < 1 → ContinuousOn F (Set.Icc 0 b)) :
    ContinuousOn F (Set.Ico 0 1) := by
  intro u hu
  have hb : u < (u + 1) / 2 := by linarith [hu.2]
  have hcw := h ((u + 1) / 2) (by linarith [hu.1]) (by linarith [hu.2]) u
    ⟨hu.1, hb.le⟩
  refine hcw.mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Set.Iio ((u + 1) / 2), isOpen_Iio, hb, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩

/-- Continuity of `𝔼𝓛_u(J)` on `[0,1)`, including `u = 0`. -/
private theorem MLExpHier_continuousOn_Lexp {E : ℝ} (hE : |E| < 2) (J : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => ∫ ω, gloop L W (HflowBlock L W u ω) (spectralZ E u) J ∂(P L W))
      (Set.Ico 0 1) :=
  MLExpHier_continuousOn_Ico fun b hb0 hb1 =>
    MLExpHier_Good_continuousOn_integral (MLExpHier_Good_gloop hE hb0 hb1 J)

/-- Continuity of the drift `𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})` on `[0,1)`, including `u = 0`. -/
private theorem MLExpHier_continuousOn_drift (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    ContinuousOn (fun u : ℝ => ∫ ω, (elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
      egtN L W E u (Hflow L W u ω) (loopOf σ a)) ∂(P L W)) (Set.Ico 0 1) :=
  MLExpHier_continuousOn_Ico fun b hb0 hb1 =>
    MLExpHier_Good_continuousOn_integral (MLExpHier_Good_drift hL hE hb0 hb1 σ a)

/-- **The expected hierarchy at a fixed size** (`0 < u < 1`):
`∂_u (𝔼𝓛_u - 𝒦_u) = ϴ_{u,σ}(𝔼𝓛_u - 𝒦_u) + 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})`. -/
private theorem MLExpHier_hasDerivAt (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    HasDerivAt (fun v : ℝ =>
        (∫ ω, gloop L W (HflowBlock L W v ω) (spectralZ E v) (loopOf σ a) ∂(P L W)) -
          KLoop.Kcal L W E v (loopOf σ a))
      (thetaSig L E σ u (fun b => (∫ ω, gloop L W (HflowBlock L W u ω) (spectralZ E u)
          (loopOf σ b) ∂(P L W)) - KLoop.Kcal L W E u (loopOf σ b)) a +
        ∫ ω, (elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
          egtN L W E u (Hflow L W u ω) (loopOf σ a)) ∂(P L W)) u := by
  have hI : (loopOf σ a).WF := MLExpHier_loopOf_wf σ a
  have hlen : 2 ≤ (loopOf σ a).length := by rw [MLExpHier_loopOf_length]
  have hW : 1 ≤ W := Nat.pos_of_ne_zero (NeZero.ne W)
  -- the expected loop
  have hL1 := hasDerivAt_integral_gloop_HflowBlock_spectralZ L W hE hu0 hu1 (loopOf σ a) hI
  have hL2 : HasDerivAt (fun v : ℝ => ∫ ω : Ω L W,
      gloop L W (HflowBlock L W v ω) (spectralZ E v) (loopOf σ a) ∂(P L W))
      (∫ ω : Ω L W, genMat E u (Hflow L W u ω) (loopOf σ a) ∂(P L W)) u := by
    have h0 := hL1.differentiableAt.hasDerivAt
    rw [deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts L W hE hu0 hu1 (loopOf σ a)
      hI] at h0
    have hcuts : (∫ ω : Ω L W, genMat E u (Hflow L W u ω) (loopOf σ a) ∂(P L W)) =
        ∫ ω : Ω L W, samplewiseLoopGeneratorCuts L W ω E u (loopOf σ a) ∂(P L W) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        MLExpHier_genMat_eq_cuts hE hu0 hu1 ω (loopOf σ a) hI)
    rw [hcuts]
    exact h0
  -- the deterministic `𝒦`
  have hK1 := (KLoop.isPrimitive_Kcal L W hL hW E hE).1 u ⟨hu0.le, hu1⟩ (loopOf σ a) hI hlen
  have hK2 : HasDerivAt (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a))
      (deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u) u :=
    hK1.differentiableAt.hasDerivAt
  refine (hL2.sub hK2).congr_deriv ?_
  -- integrability
  have hgen : Integrable (fun ω : Ω L W => genMat E u (Hflow L W u ω) (loopOf σ a)) (P L W) := by
    have := integrable_samplewiseLoopGeneratorCuts L W hE hu0 hu1 (loopOf σ a) hI
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (MLExpHier_genMat_eq_cuts hE hu0 hu1 ω (loopOf σ a) hI).symm
  have hlkI : ∀ b : Fin 2 → Z2 L, Integrable
      (fun ω => LKf L W E u (Hflow L W u ω) (loopOf σ b)) (P L W) := fun b =>
    MLExpHier_Good_integrable (MLExpHier_Good_LKf hL hE hu0.le hu1 (loopOf σ b)
      (MLExpHier_loopOf_wf _ _) (by rw [MLExpHier_loopOf_length])) (u := u) ⟨hu0.le, le_rfl⟩
  have hXi : Integrable (fun ω : Ω L W =>
      thetaSig L E σ u (lkTensor L W E u (Hflow L W u ω) σ) a) (P L W) := by
    unfold thetaSig
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun b _ =>
      (hlkI _).const_mul _
  have hDe : Integrable (fun ω : Ω L W => elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
      egtN L W E u (Hflow L W u ω) (loopOf σ a)) (P L W) :=
    MLExpHier_Good_integrable (MLExpHier_Good_drift hL hE hu0.le hu1 σ a) (u := u)
      ⟨hu0.le, le_rfl⟩
  -- the pointwise hierarchy identity
  have hpt : ∀ ω : Ω L W, genMat E u (Hflow L W u ω) (loopOf σ a) -
      deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u =
        thetaSig L E σ u (lkTensor L W E u (Hflow L W u ω) σ) a +
          (elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
            egtN L W E u (Hflow L W u ω) (loopOf σ a)) := fun ω => by
    have := hierarchyN_two L W E hL hE u hu0.le hu1 (Hflow L W u ω) (Hflow_isHermitian L W u ω)
      σ a
    rw [this]; ring
  have hint : (∫ ω : Ω L W, genMat E u (Hflow L W u ω) (loopOf σ a) ∂(P L W)) -
      deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u =
      (∫ ω : Ω L W, thetaSig L E σ u (lkTensor L W E u (Hflow L W u ω) σ) a ∂(P L W)) +
        ∫ ω : Ω L W, (elklkN L W E u (Hflow L W u ω) (loopOf σ a) +
          egtN L W E u (Hflow L W u ω) (loopOf σ a)) ∂(P L W) := by
    rw [← integral_add hXi hDe]
    rw [← integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_sub hgen (integrable_const _)]
    simp
  rw [hint]
  congr 1
  refine (MLExpHier_integral_thetaSig E u σ a
    (fun ω b => LKf L W E u (Hflow L W u ω) (loopOf σ b)) hlkI).trans ?_
  congr 1
  funext b
  exact MLExpHier_integral_LKf hE hu0.le hu1 (loopOf σ b) (MLExpHier_loopOf_wf _ _)
    (by rw [MLExpHier_loopOf_length]) hL

end FixedSize

/-! ## 5. Transfer to the common probability space, and `expHierPin` -/

section Target

variable (d : Sizes)

/-- Integrals over the common space of a function of the size-`n` slice are integrals over `P`. -/
private theorem MLExpHier_integral_slice (n : ℕ) (G : Ω (d.L n) (d.W n) → ℂ)
    (hG : AEStronglyMeasurable G (P (d.L n) (d.W n))) :
    ∫ ω, G (Sizes.slice d n ω) ∂(Sizes.seqP d) = ∫ ω, G ω ∂(P (d.L n) (d.W n)) := by
  have hf : AEMeasurable (Sizes.slice d n) (Sizes.seqP d) :=
    (Sizes.measurable_slice d n).aemeasurable
  have hg : AEStronglyMeasurable G ((Sizes.seqP d).map (Sizes.slice d n)) := by
    rw [Sizes.seqP_map_slice]; exact hG
  rw [← integral_map hf hg, Sizes.seqP_map_slice]

/-- `f_u(b) = 𝔼𝓛_u(b) - 𝒦_u(b)` over the size-`n` measure `P`, for `u < 1`. -/
private theorem MLExpHier_expErrT_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu1 : u < 1)
    (σ : Fin 2 → Bool) (b : Fin 2 → Z2 (d.L n)) :
    expErrT d n E u σ b =
      (∫ ω, gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) u ω) (spectralZ E u)
          (loopOf σ b) ∂(P (d.L n) (d.W n))) - KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ b) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  unfold expErrT expLoopErr
  congr 1
  exact MLExpHier_integral_slice d n
    (fun ω' => gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) u ω') (spectralZ E u) (loopOf σ b))
    ((continuous_gloop_HflowBlock_sample (d.L n) (d.W n) u hz (loopOf σ b)
      (MLExpHier_loopOf_wf _ _)).aestronglyMeasurable)

/-- `D_u(a) = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})` over the size-`n` measure `P`, for `0 ≤ u < 1`. -/
private theorem MLExpHier_expDriftT_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)) :
    expDriftT d n E u σ a =
      ∫ ω, (elklkN (d.L n) (d.W n) E u (Hflow (d.L n) (d.W n) u ω) (loopOf σ a) +
        egtN (d.L n) (d.W n) E u (Hflow (d.L n) (d.W n) u ω) (loopOf σ a)) ∂(P (d.L n) (d.W n)) := by
  unfold expDriftT
  exact MLExpHier_integral_slice d n
    (fun ω' => elklkN (d.L n) (d.W n) E u (Hflow (d.L n) (d.W n) u ω') (loopOf σ a) +
      egtN (d.L n) (d.W n) E u (Hflow (d.L n) (d.W n) u ω') (loopOf σ a))
    (((MLExpHier_Good_drift (d.three_le_L n) hE hu0 hu1 σ a).cont_ω u
      ⟨hu0, le_rfl⟩).aestronglyMeasurable)

/-- **`ExpHierPin`, the expected hierarchy at `n = 2`, all `σ`**: for every `n`,
`|E| < 2`, `σ`, label `a`: `f_0 = 0`; `f = 𝔼(𝓛-𝒦)` and `D = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})` are continuous
on `[0,1)`; and `f' = ϴ_{u,σ} f + D` on `(0,1)`.  No martingale term (expectation), and the drift
identity holds on the open window only (`H_u = √u X` is not differentiable at `u = 0`). -/
theorem expHierPin : ExpHierPin d := by
  intro n E hE σ a
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hI : (loopOf σ a).WF := MLExpHier_loopOf_wf σ a
  have hlen : 2 ≤ (loopOf σ a).length := by rw [MLExpHier_loopOf_length]
  refine ⟨expErrT_zero d n hE σ a, ?_, ?_, ?_⟩
  · have h1 := (MLExpHier_continuousOn_Lexp (L := d.L n) (W := d.W n) hE (loopOf σ a)).sub
      (MLExpHier_Kcal_continuousOn (W := d.W n) hL hE (loopOf σ a) hI hlen)
    exact h1.congr fun v hv => MLExpHier_expErrT_eq d n hE hv.2 σ a
  · have h1 := MLExpHier_continuousOn_drift (L := d.L n) (W := d.W n) hL hE σ a
    exact h1.congr fun v hv => MLExpHier_expDriftT_eq d n hE hv.1 hv.2 σ a
  · intro u hu
    have h1 := MLExpHier_hasDerivAt (L := d.L n) (W := d.W n) hL hE hu.1 hu.2 σ a
    have hev : (fun v => expErrT d n E v σ a) =ᶠ[nhds u] (fun v : ℝ =>
        (∫ ω, gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) v ω) (spectralZ E v)
          (loopOf σ a) ∂(P (d.L n) (d.W n))) - KLoop.Kcal (d.L n) (d.W n) E v (loopOf σ a)) := by
      filter_upwards [Iio_mem_nhds hu.2] with v hv
      exact MLExpHier_expErrT_eq d n hE hv σ a
    refine (h1.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [MLExpHier_expDriftT_eq d n hE hu.1.le hu.2 σ a]
    congr 2
    funext b
    exact (MLExpHier_expErrT_eq d n hE hu.2 σ b).symm

end Target

end RBM.Evol

end
