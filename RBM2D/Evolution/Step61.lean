/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Defs
import RBM2D.Evolution.XiBounds
import RBM2D.Hierarchy.ContractionSecondLoopSameEdge
import RBM2D.Gauss.LoopFlowCoordinateChain
import RBM2D.Gauss.LoopCoordinateDerivativeBounds
import RBM2D.Gauss.LoopInitialValueScalar
import RBM2D.Gauss.MomentBridge
import RBM2D.Gauss.SteinMatrix
import RBM2D.Path.PerTime

/-!
# `lemma:step6-1`: `𝔼⟨(G_u - m)E_a⟩ ≺ M_u^{-2}`

Paper: arXiv:2503.07606, Section 5-6, `lemma:step6-1`, from (`Eq:L-KGt`) at `u`, per energy and
time sequence.
Statement (namespace `RBM.Evol`): `Step61Pin`; proved: `step61`.  `InitLK` is `RBM.Ind.InitLK`,
`Step61Concl`, `oneLoopExpErr` are in the `RBM.Evol` vocabulary (`Defs.lean`), `xiRowBoundShort`,
`cShortRow` are in `XiBounds.lean`.

Argument (`d = 2`).
* `step61_stein`: the resolvent identity `tr(H G E_a) = 1 + z tr(G E_a)` and coordinatewise Gaussian
  integration by parts (`GaussianProduct.stein`, applied to `tr(B_c G E_a)`), summed with
  the block contraction `sum_coordinateBlock_trace_pair`, give
  `𝔼 tr(H G E_a) = -u ∑_p S_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`.
* `step61_selfcons`: with `m z_u + u m² = -1` (`spectralM_quadratic`) this is the self-consistent
  equation `x = u m² S x + y` on `Z_L²`.
* `step61_theta_solve`, `step61_norm_solve`: `Θ_{u m²}` inverts it.
  d = 2 change: the row sum of `Θ_{u m²}` is `1 + cShortRow κ (1 + log L)` (`xiRowBoundShort` at
  `s = 0`, `t = u`, `σ = +`), not the d = 1 bound (3.36); the `log L` is
  absorbed by `≺` (`step61_log_absorb`).
* `step61_moment`: the second moments of `G_bb - m` from `InitLK` at `k = 1`
  through the reverse bridge `momentDomAt_of_stochDomAt` and `stochDomAt_of_perTimeDomAt`
  (a first-moment bridge would not do; here the quadratic term uses
  `|Z_b Z_a| ≤ (|Z_b|² + |Z_a|²)/2`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section FixedSize

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem step61_sub_mul_green {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) * green H z = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_sub_smul_one_of_im_ne_zero hH hz)
  exact Matrix.mul_nonsing_inv _ hdet

private theorem step61_gloop_one (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (b : Z2 L) :
    gloop L W H z ⟨[true], [b]⟩ = Matrix.trace (green H z * Eblk L W b) :=
  by simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true]

/-- Resolvent identity at the level of a single sample: `tr(H G E_a) = 1 + z tr(G E_a)`. -/
private theorem step61_trace_HGE (u : ℝ) (ω : Ω L W) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) :
    Matrix.trace (HflowBlock L W u ω * green (HflowBlock L W u ω) z * Eblk L W a) =
      1 + z * gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩ := by
  have h := step61_sub_mul_green L W (HflowBlock_isHermitian L W u ω) hz
  have hHG : HflowBlock L W u ω * green (HflowBlock L W u ω) z =
      1 + z • green (HflowBlock L W u ω) z := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [hHG, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.one_mul, trace_Eblk_eq_one, step61_gloop_one, smul_eq_mul]


private theorem step61_norm_trace_mul3_le (A M C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ‖Matrix.trace (A * M * C)‖ ≤ (((L * W) ^ 2 : ℕ) : ℝ) * (‖A‖ * ‖M‖ * ‖C‖) := by
  have h := norm_matrix_trace_le_card_mul (A * M * C)
  rw [card_BlockIndex] at h
  refine h.trans ?_
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- A Gaussian coordinate times a bounded measurable complex observable is integrable. -/
private theorem step61_integrable_coord_smul (c : Coord L W)
    (g : Ω L W → ℂ) (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω L W => ω c • g ω) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gvar L W c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (P L W) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have h := hcoord.ofReal.bdd_mul hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  simpa [Complex.real_smul, mul_comm] using h

private theorem step61_integrable_of_cont_bdd {f : Ω L W → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (P L W) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem step61_green_norm_le (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω L W) :
    ‖green (HflowBlock L W u ω) z‖ ≤ (|z.im|)⁻¹ :=
  norm_green_le (HflowBlock_isHermitian L W u ω) (abs_pos.mpr hz) le_rfl

private theorem step61_g_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    Continuous fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a) :=
  (continuous_matrixTrace L W).comp
    ((continuous_const.mul (continuous_green_HflowBlock_sample L W u hz)).mul continuous_const)

private theorem step61_g'_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    Continuous fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a) := by
  have hGc := continuous_green_HflowBlock_sample L W u hz
  exact (continuous_matrixTrace L W).comp
    ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const)

private theorem step61_g_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    ∃ C : ℝ, ∀ ω : Ω L W, ‖Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
    (‖coordinateBlock L W c‖ * (|z.im|)⁻¹ * ‖Eblk L W a‖), fun ω => ?_⟩
  refine (step61_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  exact step61_green_norm_le L W u hz ω

private theorem step61_g'_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) (c : Coord L W) :
    ∃ C : ℝ, ∀ ω : Ω L W, ‖Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ 2 : ℕ) : ℝ) *
    (‖coordinateBlock L W c‖ * ((|z.im|)⁻¹ * ‖Real.sqrt u • coordinateBlock L W c‖ *
      (|z.im|)⁻¹) * ‖Eblk L W a‖), fun ω => ?_⟩
  refine (step61_norm_trace_mul3_le L W _ _ _).trans ?_
  gcongr
  rw [norm_neg]
  refine (norm_mul_le _ _).trans ?_
  gcongr
  · exact (norm_mul_le _ _).trans (by gcongr; exact step61_green_norm_le L W u hz ω)
  · exact step61_green_norm_le L W u hz ω

/-- One-coordinate Stein identity for `tr(B_c G E_a)`. -/
private theorem step61_stein_coord (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L)
    (c : Coord L W) :
    ∫ ω : Ω L W, ω c • Matrix.trace
        (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a) ∂(P L W) =
      (gvar L W c : ℝ) • ∫ ω : Ω L W, Matrix.trace
        (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
          (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
          Eblk L W a) ∂(P L W) := by
  set B := coordinateBlock L W c with hB
  set E := Eblk L W a with hE
  let g : Ω L W → ℂ := fun ω => Matrix.trace (B * green (HflowBlock L W u ω) z * E)
  let g' : Ω L W → ℂ := fun ω => Matrix.trace (B * (-(green (HflowBlock L W u ω) z *
    (Real.sqrt u • B) * green (HflowBlock L W u ω) z)) * E)
  have hgc : Continuous g := step61_g_cont L W u hz a c
  have hg'c : Continuous g' := step61_g'_cont L W u hz a c
  have hderiv : ∀ ω : Ω L W,
      HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_HflowBlock_update L W u ω c hz
    have h2 := ((hasDerivAt_const (ω c) B).mul h1).mul_const E
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, g', zero_mul, zero_add, hB]
  have hgb : ∃ C : ℝ, ∀ ω : Ω L W, ‖g ω‖ ≤ C := step61_g_bdd L W u hz a c
  have hg'b : ∃ C : ℝ, ∀ ω : Ω L W, ‖g' ω‖ ≤ C := step61_g'_bdd L W u hz a c
  have h := GaussianProduct.stein (gvar L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [hlaw]
  exact h

/-- The contraction of the two `B_c` insertions: the `W²` of the block covariance cancels the
`W⁻²` of `E_a E_a`. -/
private theorem step61_contraction (u : ℝ) (hu : 0 ≤ u)
    (G : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (a : Z2 L) :
    ∑ c : Coord L W, ((Real.sqrt u : ℂ) * ((gvar L W c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c *
        (-(G * (Real.sqrt u • coordinateBlock L W c) * G)) * Eblk L W a) =
    -(u : ℂ) * ∑ p : Z2 L, SB L p a *
      (Matrix.trace (G * Eblk L W p) * Matrix.trace (G * Eblk L W a)) := by
  have hterm : ∀ c : Coord L W,
      ((Real.sqrt u : ℂ) * ((gvar L W c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c *
        (-(G * (Real.sqrt u • coordinateBlock L W c) * G)) * Eblk L W a) =
      -(u : ℂ) * (((gvar L W c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock L W c * (G * Eblk L W a) *
          coordinateBlock L W c)) := by
    intro c
    set B := coordinateBlock L W c
    have h1 : B * (-(G * (Real.sqrt u • B) * G)) * Eblk L W a =
        -(Real.sqrt u • (B * (G * B * (G * Eblk L W a)))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    have h2 : Matrix.trace (B * (G * B * (G * Eblk L W a))) =
        Matrix.trace (G * B * (G * Eblk L W a) * B) :=
      Matrix.trace_mul_comm _ _
    rw [h1, Matrix.trace_neg, Matrix.trace_smul, h2, Complex.real_smul]
    have h3 : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    linear_combination
      (-(((gvar L W c : ℝ) : ℂ) * Matrix.trace (G * B * (G * Eblk L W a) * B))) * h3
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_coordinateBlock_trace_pair L W G (G * Eblk L W a)]
  congr 1
  have hq : ∀ q : Z2 L, Matrix.trace (G * Eblk L W a * Eblk L W q) =
      if a = q then (W : ℂ)⁻¹ ^ 2 * Matrix.trace (G * Eblk L W a) else 0 := by
    intro q
    rw [Matrix.mul_assoc, Eblk_mul_Eblk]
    split_ifs
    · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    · simp
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  simp_rw [hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  field_simp

private theorem step61_HflowBlock_eq (u : ℝ) (ω : Ω L W) :
    HflowBlock L W u ω =
      (Real.sqrt u : ℂ) • ∑ c : Coord L W, ω c • coordinateBlock L W c := by
  rw [← Xblock_eq_sum_coordinates]
  ext i j
  simp [HflowBlock, Hflow]

private theorem step61_gloop_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Z2 L) (ω : Ω L W) :
    ‖gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2)) := by
  have h := norm_gloop_le_crude L W (HflowBlock_isHermitian L W u ω)
    (abs_pos.mpr hz) le_rfl ⟨[true], [b]⟩ (by simp [LoopIdx.WF])
  simpa using h

private theorem step61_gloop_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Z2 L) :
    Continuous fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ :=
  continuous_gloop_HflowBlock_sample L W u hz _ (by simp [LoopIdx.WF])

private theorem step61_integrable_gloop (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Z2 L) :
    Integrable (fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩) (P L W) :=
  step61_integrable_of_cont_bdd L W (step61_gloop_cont L W u hz b) (step61_gloop_bdd L W u hz b)

private theorem step61_integrable_gloop_mul (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b a : Z2 L) :
    Integrable (fun ω : Ω L W => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ *
      gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩) (P L W) := by
  refine step61_integrable_of_cont_bdd L W
    ((step61_gloop_cont L W u hz b).mul (step61_gloop_cont L W u hz a))
    (C := ((((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2))) *
      ((((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2)))) (fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (step61_gloop_bdd L W u hz b ω) (step61_gloop_bdd L W u hz a ω)
    (norm_nonneg _) ((norm_nonneg _).trans (step61_gloop_bdd L W u hz b ω))

/-- **Stein step**: `𝔼 tr(H G E_a) = -u ∑_p S_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`. -/
private theorem step61_stein (u : ℝ) (hu : 0 ≤ u) {z : ℂ} (hz : z.im ≠ 0) (a : Z2 L) :
    ∫ ω : Ω L W, Matrix.trace (HflowBlock L W u ω * green (HflowBlock L W u ω) z *
        Eblk L W a) ∂(P L W) =
      -(u : ℂ) * ∑ p : Z2 L, SB L p a * ∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) z ⟨[true], [p]⟩ *
          gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩ ∂(P L W) := by
  classical
  -- integrability of the coordinate terms
  have hI1 : ∀ c : Coord L W, Integrable (fun ω : Ω L W => ω c • Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)) (P L W) := by
    intro c
    obtain ⟨C, hC⟩ := step61_g_bdd L W u hz a c
    exact step61_integrable_coord_smul L W c _ (step61_g_cont L W u hz a c).measurable hC
  have hI2 : ∀ c : Coord L W, Integrable (fun ω : Ω L W => Matrix.trace
      (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a)) (P L W) := by
    intro c
    obtain ⟨C, hC⟩ := step61_g'_bdd L W u hz a c
    exact step61_integrable_of_cont_bdd L W (step61_g'_cont L W u hz a c) hC
  -- pointwise expansion of `tr(H G E_a)`
  have hexp : ∀ ω : Ω L W, Matrix.trace (HflowBlock L W u ω *
      green (HflowBlock L W u ω) z * Eblk L W a) =
      ∑ c : Coord L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
        (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)) := by
    intro ω
    generalize green (HflowBlock L W u ω) z = G
    rw [step61_HflowBlock_eq L W u ω]
    simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      Complex.real_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun c _ => (hI1 c).const_mul _)]
  have hstein : ∀ c : Coord L W, ∫ ω : Ω L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
      (coordinateBlock L W c * green (HflowBlock L W u ω) z * Eblk L W a)) ∂(P L W) =
      ∫ ω : Ω L W, ((Real.sqrt u : ℂ) * ((gvar L W c : ℝ) : ℂ)) * Matrix.trace
        (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
          (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
          Eblk L W a) ∂(P L W) := by
    intro c
    rw [integral_const_mul, step61_stein_coord L W u hz a c, integral_const_mul,
      Complex.real_smul, mul_assoc]
  simp_rw [hstein]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  have hpt : ∀ ω : Ω L W, ∑ c : Coord L W, ((Real.sqrt u : ℂ) * ((gvar L W c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock L W c * (-(green (HflowBlock L W u ω) z *
        (Real.sqrt u • coordinateBlock L W c) * green (HflowBlock L W u ω) z)) *
        Eblk L W a) =
      -(u : ℂ) * ∑ p : Z2 L, SB L p a * (gloop L W (HflowBlock L W u ω) z ⟨[true], [p]⟩ *
        gloop L W (HflowBlock L W u ω) z ⟨[true], [a]⟩) := by
    intro ω
    rw [step61_contraction L W u hu]
    simp only [step61_gloop_one]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _
    (fun p _ => (step61_integrable_gloop_mul L W u hz p a).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

private theorem step61_SB_symm (a b : Z2 L) : SB L b a = SB L a b :=
  congrFun (congrFun (SB_transpose L) a) b

private theorem step61_sum_SB_col (hL : 3 ≤ L) (a : Z2 L) : ∑ b : Z2 L, SB L b a = 1 := by
  simp_rw [step61_SB_symm L a]
  exact sum_SB_row L hL a

/-- **(5.127)/(5.128) before inversion**: with `x_b = 𝔼 g_b - m`, `Z_b = g_b - m`, `ξ = u m²`,
`x_a = ξ ∑_b S_{ba} x_b + u m ∑_b S_{ba} 𝔼[Z_b Z_a]`. -/
private theorem step61_selfcons (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (a : Z2 L) :
    (∫ ω : Ω L W, gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ ∂(P L W)) -
        spectralM E =
      (u : ℂ) * spectralM E ^ 2 * ∑ b : Z2 L, SB L b a *
        ((∫ ω : Ω L W, gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩
          ∂(P L W)) - spectralM E) +
      (u : ℂ) * spectralM E * ∑ b : Z2 L, SB L b a * ∫ ω : Ω L W,
        (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - spectralM E) *
          (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - spectralM E)
          ∂(P L W) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  set z := spectralZ E u with hzdef
  set m := spectralM E with hm
  set g : Z2 L → Ω L W → ℂ := fun b ω => gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ with hg
  have hgI : ∀ b, Integrable (g b) (P L W) := fun b => step61_integrable_gloop L W u hz b
  have hgg : ∀ b, Integrable (fun ω => g b ω * g a ω) (P L W) :=
    fun b => step61_integrable_gloop_mul L W u hz b a
  -- the Stein identity, integrated resolvent identity
  have hres : ∫ ω : Ω L W, Matrix.trace (HflowBlock L W u ω * green (HflowBlock L W u ω) z *
      Eblk L W a) ∂(P L W) = 1 + z * ∫ ω, g a ω ∂(P L W) := by
    simp_rw [step61_trace_HGE L W u _ hz a]
    rw [integral_add (integrable_const _) ((hgI a).const_mul z), integral_const_mul,
      integral_const]
    simp
  have hst : 1 + z * ∫ ω, g a ω ∂(P L W) =
      -(u : ℂ) * ∑ p : Z2 L, SB L p a * ∫ ω, g p ω * g a ω ∂(P L W) := by
    have h := step61_stein L W u hu0 hz a
    rw [hres] at h
    exact h
  -- `m z + u m² = -1`
  have hmz : m * z + (u : ℂ) * m ^ 2 = -1 := by
    have hq := spectralM_quadratic (E := E) hE.le
    simp only [hzdef, spectralZ]
    linear_combination hq
  have hSum1 := step61_sum_SB_col L hL a
  change (∫ ω, g a ω ∂(P L W)) - m =
    (u : ℂ) * m ^ 2 * ∑ b : Z2 L, SB L b a * ((∫ ω, g b ω ∂(P L W)) - m) +
      (u : ℂ) * m * ∑ b : Z2 L, SB L b a * ∫ ω, (g b ω - m) * (g a ω - m) ∂(P L W)
  -- centred product integrals
  have hZ : ∀ b, ∫ ω : Ω L W, (g b ω - m) * (g a ω - m) ∂(P L W) =
      (∫ ω, g b ω * g a ω ∂(P L W)) - m * (∫ ω, g b ω ∂(P L W)) -
        m * (∫ ω, g a ω ∂(P L W)) + m ^ 2 := by
    intro b
    have i1 : Integrable (fun ω : Ω L W => g b ω * g a ω) (P L W) := hgg b
    have i2 : Integrable (fun ω : Ω L W => m * g b ω) (P L W) := (hgI b).const_mul m
    have i3 : Integrable (fun ω : Ω L W => m * g a ω) (P L W) := (hgI a).const_mul m
    have hfun : (fun ω : Ω L W => (g b ω - m) * (g a ω - m)) =
        fun ω => g b ω * g a ω - m * g b ω - m * g a ω + m ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω : Ω L W => g b ω * g a ω - m * g b ω) (P L W) := i1.sub i2
    have i123 : Integrable (fun ω : Ω L W => g b ω * g a ω - m * g b ω - m * g a ω)
        (P L W) := i12.sub i3
    rw [hfun, integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  simp_rw [hZ]
  set Ia := ∫ ω, g a ω ∂(P L W) with hIa
  have e1 : ∑ b : Z2 L, SB L b a * ((∫ ω, g b ω ∂(P L W)) - m) =
      (∑ b : Z2 L, SB L b a * ∫ ω, g b ω ∂(P L W)) - m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum1, one_mul]
  have e2 : ∑ b : Z2 L, SB L b a * ((∫ ω, g b ω * g a ω ∂(P L W)) -
      m * (∫ ω, g b ω ∂(P L W)) - m * Ia + m ^ 2) =
      (∑ b : Z2 L, SB L b a * ∫ ω, g b ω * g a ω ∂(P L W)) -
        m * (∑ b : Z2 L, SB L b a * ∫ ω, g b ω ∂(P L W)) - m * Ia + m ^ 2 := by
    have hb : ∀ b : Z2 L, SB L b a * ((∫ ω, g b ω * g a ω ∂(P L W)) -
        m * (∫ ω, g b ω ∂(P L W)) - m * Ia + m ^ 2) =
        SB L b a * (∫ ω, g b ω * g a ω ∂(P L W)) -
          m * (SB L b a * ∫ ω, g b ω ∂(P L W)) + SB L b a * (m ^ 2 - m * Ia) :=
      fun b => by ring
    simp_rw [hb]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hSum1]
    ring
  rw [e1, e2]
  set T1 := ∑ b : Z2 L, SB L b a * ∫ ω, g b ω ∂(P L W)
  set T2 := ∑ b : Z2 L, SB L b a * ∫ ω, g b ω * g a ω ∂(P L W)
  linear_combination (-m) * hst + Ia * hmz

end FixedSize

section Deterministic

variable (L : ℕ) [NeZero L]

/-- On `Z_L²`: `x = ξ S x + y` is solved by `x = Θ_ξ y`. -/
private theorem step61_theta_solve (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {x y : Z2 L → ℂ}
    (h : ∀ a, x a = ξ * ∑ b, SB L b a * x b + y a) (a : Z2 L) :
    x a = ∑ a', Theta L ξ a a' * y a' := by
  have hy : y = (1 - ξ • SB L) *ᵥ x := by
    funext c
    have hc := h c
    have hm : ((1 - ξ • SB L) *ᵥ x) c = x c - ξ * ∑ b, SB L c b * x b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    rw [hm]
    have e : ∑ b, SB L b c * x b = ∑ b, SB L c b * x b :=
      Finset.sum_congr rfl fun b _ => by rw [step61_SB_symm L c b]
    rw [e] at hc
    linear_combination -hc
  have hx : Theta L ξ *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Theta_mul L hL hξ, Matrix.one_mulVec]
  rw [← hx]
  rfl

/-- Row sum of `Θ_{u m²}` on `Z_L²`: `1 + cShortRow κ (1 + log L)` (`xiRowBoundShort` at
`s = 0`, `t = u`, `σ = +`; this replaces the d = 1 bound (3.36)). -/
private theorem step61_theta_row_sum (hL : 3 ≤ L) {κ E u : ℝ} (hκ : 0 < κ)
    (hEκ : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Z2 L) :
    ∑ a' : Z2 L, ‖Theta L ((u : ℂ) * spectralM E ^ 2) a a'‖ ≤
      1 + cShortRow κ * (1 + Real.log L) := by
  have h := xiRowBoundShort L hL κ E hκ hEκ true 0 u le_rfl hu0 hu1 a
  have hxi : ∀ a' : Z2 L,
      xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 u a a' =
        Theta L ((u : ℂ) * spectralM E ^ 2) a a' - (1 : Matrix (Z2 L) (Z2 L) ℂ) a a' := by
    intro a'
    simp only [xiMat, ukerMat, KLoop.mSig, ite_true, Complex.ofReal_zero, zero_mul, zero_smul,
      sub_zero, Matrix.one_mul, Matrix.sub_apply]
    rw [sq]
  have hone : ∑ a' : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖ = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  calc ∑ a' : Z2 L, ‖Theta L ((u : ℂ) * spectralM E ^ 2) a a'‖
      ≤ ∑ a' : Z2 L, (‖xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 u a a'‖ +
          ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖) := by
        refine Finset.sum_le_sum fun a' _ => ?_
        have : Theta L ((u : ℂ) * spectralM E ^ 2) a a' =
            xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 u a a' +
              (1 : Matrix (Z2 L) (Z2 L) ℂ) a a' := by
          rw [hxi a']; ring
        rw [this]
        exact norm_add_le _ _
    _ = ∑ a' : Z2 L, ‖xiMat L (KLoop.mSig E true * KLoop.mSig E true) 0 u a a'‖ +
          ∑ a' : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a a'‖ := Finset.sum_add_distrib
    _ ≤ cShortRow κ * (1 + Real.log L) + 1 := add_le_add h hone.le
    _ = 1 + cShortRow κ * (1 + Real.log L) := by ring

/-- **Deterministic inversion.**  If `‖y_b‖ ≤ K` for all `b` and `x = ξ S x + y` with `ξ = u m²`,
`|E| ≤ 2 - κ`, `0 ≤ u < 1`, then `‖x_a‖ ≤ (1 + cShortRow κ (1 + log L)) K` (with the
d = 2 row sum). -/
private theorem step61_norm_solve (hL : 3 ≤ L) {κ E u : ℝ} (hκ : 0 < κ)
    (hEκ : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {x y : Z2 L → ℂ}
    (h : ∀ a, x a = ((u : ℂ) * spectralM E ^ 2) * ∑ b, SB L b a * x b + y a) {K : ℝ}
    (hy : ∀ a, ‖y a‖ ≤ K) (a : Z2 L) :
    ‖x a‖ ≤ (1 + cShortRow κ * (1 + Real.log L)) * K := by
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  have hξ : ‖(u : ℂ) * spectralM E ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, norm_spectralM hE2, Complex.norm_of_nonneg hu0]
    simpa using hu1
  have hK : 0 ≤ K := (norm_nonneg _).trans (hy a)
  rw [step61_theta_solve L hL hξ h a]
  calc ‖∑ a', Theta L ((u : ℂ) * spectralM E ^ 2) a a' * y a'‖
      ≤ ∑ a', ‖Theta L ((u : ℂ) * spectralM E ^ 2) a a'‖ * K := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hy a') (norm_nonneg _)
    _ = (∑ a', ‖Theta L ((u : ℂ) * spectralM E ^ 2) a a'‖) * K := by rw [Finset.sum_mul]
    _ ≤ (1 + cShortRow κ * (1 + Real.log L)) * K :=
        mul_le_mul_of_nonneg_right (step61_theta_row_sum L hL hκ hEκ hu0 hu1 a) hK

end Deterministic

section Combine

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem step61_hz {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) : (spectralZ E u).im ≠ 0 := by
  rw [spectralZ_im]
  exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))

private theorem step61_integrable_normsq (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (m : ℂ) (b : Z2 L) :
    Integrable (fun ω : Ω L W =>
      ‖gloop L W (HflowBlock L W u ω) z ⟨[true], [b]⟩ - m‖ ^ 2) (P L W) := by
  refine Integrable.of_bound (C := ((((L * W) ^ 2 : ℕ) : ℝ) * ((|z.im|)⁻¹ * ((W : ℝ)⁻¹ ^ 2)) +
    ‖m‖) ^ 2) (((step61_gloop_cont L W u hz b).sub continuous_const).norm.pow 2
      |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le _ _).trans (add_le_add_left (step61_gloop_bdd L W u hz b ω) _)) 2

/-- The fixed-size deterministic core of `lemma:step6-1`: second moments of `G_bb`-fluctuations
bound the expected fluctuation, with the d = 2 row sum. -/
private theorem step61_expErr_le (hL : 3 ≤ L) {κ E u : ℝ} (hκ : 0 < κ) (hEκ : |E| ≤ 2 - κ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {K : ℝ}
    (hK : ∀ b : Z2 L, ∫ ω : Ω L W, ‖gloop L W (HflowBlock L W u ω) (spectralZ E u)
      ⟨[true], [b]⟩ - spectralM E‖ ^ 2 ∂(P L W) ≤ K) (a : Z2 L) :
    ‖(∫ ω : Ω L W, gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ ∂(P L W)) -
        spectralM E‖ ≤ (1 + cShortRow κ * (1 + Real.log L)) * K := by
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  have hz := step61_hz hE hu1
  set m := spectralM E with hm
  set y : Z2 L → ℂ := fun a => (u : ℂ) * m * ∑ b : Z2 L, SB L b a * ∫ ω : Ω L W,
    (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - m) *
      (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - m) ∂(P L W) with hy
  have hself := step61_selfcons L W hL hE hu0 hu1
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ ∫ ω : Ω L W, ‖gloop L W (HflowBlock L W u ω) (spectralZ E u)
      ⟨[true], [a]⟩ - m‖ ^ 2 ∂(P L W) := integral_nonneg fun ω => sq_nonneg _
    exact this.trans (hK a)
  -- the pair bound
  have hpair : ∀ b a : Z2 L, ‖∫ ω : Ω L W,
      (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - m) *
        (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - m) ∂(P L W)‖ ≤ K := by
    intro b a
    refine (norm_integral_le_integral_norm _).trans ?_
    have hg : Integrable (fun ω : Ω L W => (1 / 2 : ℝ) *
        (‖gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - m‖ ^ 2 +
          ‖gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - m‖ ^ 2)) (P L W) :=
      ((step61_integrable_normsq L W u hz m b).add
        (step61_integrable_normsq L W u hz m a)).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hg
      (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
    · beta_reduce
      rw [norm_mul]
      nlinarith [sq_nonneg (‖gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - m‖ -
        ‖gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - m‖)]
    · rw [integral_const_mul, integral_add (step61_integrable_normsq L W u hz m b)
        (step61_integrable_normsq L W u hz m a)]
      have := hK b
      have := hK a
      linarith
  have hyK : ∀ a : Z2 L, ‖y a‖ ≤ K := by
    intro a
    have hum : ‖(u : ℂ) * m‖ ≤ 1 := by
      rw [norm_mul, hm, norm_spectralM hE2, Complex.norm_of_nonneg hu0]
      simpa using hu1.le
    have hrow : ∑ b : Z2 L, ‖SB L b a‖ = 1 := by
      simp_rw [step61_SB_symm L a]
      have h := congrArg (fun r : NNReal => (r : ℝ)) (sum_nnnorm_SB_row L hL a)
      simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using h
    calc ‖y a‖ = ‖(u : ℂ) * m‖ * ‖∑ b : Z2 L, SB L b a * ∫ ω : Ω L W,
          (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ - m) *
            (gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [a]⟩ - m) ∂(P L W)‖ := by
          rw [hy]; simp only [mul_assoc, norm_mul]
      _ ≤ 1 * (∑ b : Z2 L, ‖SB L b a‖ * K) := by
          refine mul_le_mul hum ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
            (norm_nonneg _) zero_le_one
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpair b a) (norm_nonneg _)
      _ = K := by rw [← Finset.sum_mul, hrow, one_mul, one_mul]
  exact step61_norm_solve L hL hκ hEκ hu0 hu1 (x := fun b => (∫ ω : Ω L W,
    gloop L W (HflowBlock L W u ω) (spectralZ E u) ⟨[true], [b]⟩ ∂(P L W)) - m) (y := y)
    (fun a => hself a) hyK a

end Combine

section Scalars

private theorem step61_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    ‖KLoop.mSig E s‖ = 1 := by
  cases s
  · simp [KLoop.mSig, norm_spectralM hE]
  · simp [KLoop.mSig, norm_spectralM hE]

/-- `𝒦` at a one-edge loop is `m(σ)`: `‖𝒦_{u,σ,a}‖ = 1` (`Kgen`, `if I.length = 1`). -/
private theorem step61_norm_Kcal_one (L W : ℕ) [NeZero L] {E : ℝ} (hE : |E| ≤ 2) (t : ℝ)
    (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    ‖KLoop.Kcal L W E t (loopOf σ a)‖ = 1 := by
  have h : KLoop.Kcal L W E t (loopOf σ a) = KLoop.mSig E (σ 0) := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length, loopOf, List.getD]
  rw [h, step61_norm_mSig hE]

private theorem step61_Kcal_true (L W : ℕ) [NeZero L] (E t : ℝ) (b : Z2 L) :
    KLoop.Kcal L W E t (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => b)) = spectralM E := by
  simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length, loopOf, List.getD, KLoop.mSig]

end Scalars

section ScaleFacts

private theorem step61_im_le_one {E : ℝ} (hE : |E| ≤ 2) : (spectralM E).im ≤ 1 := by
  have h := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE] at h
  exact (le_abs_self _).trans h

/-- The uniform lower bound of `Im m` on the bulk `|E| ≤ 2 - κ`. -/
private theorem step61_im_lower {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt (2 * κ) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have habs := abs_le.mp hE
  have h4 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h4) (by norm_num)

private theorem step61_scaleM_le (L W : ℕ) (hL : 1 ≤ L) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    scaleM L W E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  have hell := ellT_pos_le hL hu1
  have hη : etaT E u ≤ 1 := by
    unfold etaT
    have h1 := step61_im_le_one hE.le
    have h2 := spectralM_im_pos hE
    nlinarith
  have hη0 := etaT_pos hE hu1
  unfold scaleM
  calc (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * 1 := by
        gcongr
        · exact hell.1.le
        · exact hell.2
    _ = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := mul_one _

private theorem step61_norm_gloop_one_le (L W : ℕ) [NeZero L] [NeZero W] {E u : ℝ}
    (hE : |E| < 2) (hu1 : u < 1) (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (hH : H.IsHermitian) (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    ‖gloop L W H (spectralZ E u) (loopOf σ a)‖ ≤ (L : ℝ) ^ 2 * (etaT E u)⁻¹ := by
  have hη := etaT_pos hE hu1
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE))]
    rfl
  have h := norm_gloop_le_crude L W hH hη hz (loopOf σ a) (by simp [loopOf, LoopIdx.WF])
  have hlen : (loopOf σ a).a.length = 1 := by simp [loopOf]
  rw [hlen] at h
  refine h.trans (le_of_eq ?_)
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  push_cast
  field_simp

end ScaleFacts

section Moment

variable (d : Sizes)

private theorem step61_integral_slice {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (n : ℕ) (F : Ω (d.L n) (d.W n) → F')
    (hF : AEStronglyMeasurable F (P (d.L n) (d.W n))) :
    ∫ ω, F (Sizes.slice d n ω) ∂(Sizes.seqP d) = ∫ ω, F ω ∂(P (d.L n) (d.W n)) := by
  have hm : AEMeasurable (Sizes.slice d n) (Sizes.seqP d) :=
    (Sizes.measurable_slice d n).aemeasurable
  have hF' : AEStronglyMeasurable F (Measure.map (Sizes.slice d n) (Sizes.seqP d)) := by
    rw [Sizes.seqP_map_slice]; exact hF
  rw [← integral_map hm hF', Sizes.seqP_map_slice]

/-- The second-moment bound from `InitLK` at `k = 1` (the input (`Eq:L-KGt`) at `u`), through
the reverse bridge `momentDomAt_of_stochDomAt`. -/
private theorem step61_moment (κ τ : ℝ) (E u : ℕ → ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1)
    (hsize : SizeTendsto d) (hrange : RangeCond d τ u) (hinit : InitLK d E u) :
    MomentDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n)))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n _ => (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ 1) := by
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hL1 : ∀ n, 1 ≤ d.L n := fun n => by have := d.three_le_L n; omega
  have hsz : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  set c0 : ℝ := Real.sqrt (2 * κ) / 2 with hc0def
  have hc0 : 0 < c0 := by positivity
  have hMpos : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (u n) := fun n =>
    scaleM_pos (hL1 n) (d.W_pos n) (hE2 n) (hu1 n)
  have hMle : ∀ n, scaleM (d.L n) (d.W n) (E n) (u n) ≤ ((d.size n : ℕ) : ℝ) := by
    intro n
    have h := step61_scaleM_le (d.L n) (d.W n) (hL1 n) (hE2 n) (hu0 n) (hu1 n)
    rw [Sizes.size_eq]
    push_cast
    exact h
  -- the parameter set is polynomially small
  have hcardEq : ∀ n, Fintype.card (Unit × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n))) =
      2 * (d.L n * d.L n) := by
    intro n
    simp [Fintype.card_prod, ZMod.card, Z2]
  have hcard : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Unit × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n))) : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
    filter_upwards [hsz.eventually (eventually_ge_atTop 2)] with n hn
    rw [hcardEq, Real.rpow_two]
    have h1 : (d.L n * d.L n : ℕ) ≤ d.size n := by
      rw [Sizes.size_eq]
      have hW : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
      calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
        _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul_right _ hW
    have h2 : 2 * (d.L n * d.L n) ≤ d.size n ^ 2 := by nlinarith
    exact_mod_cast h2
  have hdomU := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := 2) (by norm_num) hcard
    (hinit 1 le_rfl)
  -- the pieces of the reverse bridge
  have hmeas : ∀ (n : ℕ) (p : Unit × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n))),
      Measurable (fun ω => lkGen (d.L n) (d.W n) (E n) (u n)
        (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2) := by
    intro n p
    have hz := step61_hz (hE2 n) (hu1 n)
    have h1 := (measurable_gloop_HflowBlock_sample (d.L n) (d.W n) (u n) hz
      (loopOf p.2.1 p.2.2) (by simp [loopOf, LoopIdx.WF])).comp (Sizes.measurable_slice d n)
    exact (h1.sub_const _).norm
  refine momentDomAt_of_stochDomAt d.size hsz (Env := fun n =>
      ((d.L n : ℝ)) ^ 2 * (etaT (E n) (u n))⁻¹ + 1) (Kenv := 3) (B := 1) hmeas
    (fun n _ => by have := hMpos n; positivity) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_
  · -- `hΦlow`
    refine Filter.Eventually.of_forall fun n p => ?_
    rw [Real.rpow_neg_one, pow_one]
    exact inv_anti₀ (hMpos n) (hMle n)
  · -- `hEnv0`
    intro n
    have := etaT_pos (hE2 n) (hu1 n)
    positivity
  · -- `henv`
    intro n p ω
    change |‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω)) (spectralZ (E n) (u n))
      (loopOf p.2.1 p.2.2) - KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf p.2.1 p.2.2)‖| ≤ _
    rw [abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ?_
    rw [step61_norm_Kcal_one (d.L n) (d.W n) (hE2 n).le]
    gcongr
    exact step61_norm_gloop_one_le (d.L n) (d.W n) (hE2 n) (hu1 n) _
      (Hflow_isHermitian (d.L n) (d.W n) (u n) (Sizes.slice d n ω) |>.submatrix _) _ _
  · -- `hEnvpoly`
    filter_upwards [hrange, hsz.eventually (eventually_ge_atTop (⌈c0⁻¹⌉₊ + 1))] with n hr hn
    set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
    have hcinv : 0 < c0⁻¹ := inv_pos.mpr hc0
    have hNge : c0⁻¹ + 1 ≤ N := by
      have h1 := Nat.le_ceil c0⁻¹
      have h2 : ((⌈c0⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr hn
      push_cast at h2
      linarith
    have hN1 : 1 ≤ N := by linarith
    have hNpos : 0 < N := by linarith
    have hpos : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hNpos _
    have h1 : (1 - u n)⁻¹ ≤ (N ^ (-1 + τ))⁻¹ := inv_anti₀ hpos hr
    have h2 : (N ^ (-1 + τ))⁻¹ = N ^ (1 - τ) := by
      rw [← Real.rpow_neg hNpos.le]; congr 1; ring
    have h3 : N ^ (1 - τ) ≤ N := by
      calc N ^ (1 - τ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N := Real.rpow_one N
    have hIm : c0 ≤ (spectralM (E n)).im := step61_im_lower hκ (hE n)
    have hImpos : 0 < (spectralM (E n)).im := lt_of_lt_of_le hc0 hIm
    have h1u : 0 < 1 - u n := by linarith [hu1 n]
    have hηinv : (etaT (E n) (u n))⁻¹ ≤ N * c0⁻¹ := by
      unfold etaT
      rw [mul_inv]
      exact mul_le_mul (h1.trans (h2 ▸ h3)) (inv_anti₀ hc0 hIm) (inv_nonneg.mpr hImpos.le)
        hNpos.le
    have hL2 : ((d.L n : ℕ) : ℝ) ^ 2 ≤ N := by
      rw [hNdef, Sizes.size_eq]
      push_cast
      have hW : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast d.W_pos n)
      nlinarith [sq_nonneg (d.L n : ℝ)]
    have hη0 : 0 ≤ (etaT (E n) (u n))⁻¹ := (inv_pos.mpr (etaT_pos (hE2 n) (hu1 n))).le
    have h3' : (N : ℝ) ^ (3 : ℝ) = N ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    change ((d.L n : ℝ)) ^ 2 * (etaT (E n) (u n))⁻¹ + 1 ≤ N ^ (3 : ℝ)
    rw [h3']
    have h4 : ((d.L n : ℝ)) ^ 2 * (etaT (E n) (u n))⁻¹ ≤ N * (N * c0⁻¹) :=
      mul_le_mul hL2 hηinv hη0 hNpos.le
    nlinarith [mul_nonneg hNpos.le hNpos.le,
      mul_nonneg (mul_nonneg hNpos.le hNpos.le) (sub_nonneg.mpr hNge)]
  · -- `hdom`
    have habs : (fun n (p : Unit × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n))) ω =>
        |lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2|) =
        (fun n p ω => lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
          p.2.1 p.2.2) := by
      funext n p ω
      exact abs_of_nonneg (norm_nonneg _)
    rw [habs]
    exact hdomU

end Moment

section Asymptotics

/-- A fixed constant times `1 + a (1 + log x)` is eventually `≤ x^δ` (absorbs the `log L` of the
d = 2 short-edge row sum, `cShortRow κ (1 + log L)`). -/
private theorem step61_log_absorb (a C δ : ℝ) (ha : 0 ≤ a) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, (1 + a * (1 + Real.log x)) * C ≤ x ^ δ := by
  set B : ℝ := (1 + a) * C + a * C * (2 / δ) + 1 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (1 + a) * C := by positivity
    have : 0 ≤ a * C * (2 / δ) := by positivity
    linarith
  have ht : Tendsto (fun x : ℝ => x ^ (δ / 2)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [ht.eventually (eventually_ge_atTop B), eventually_gt_atTop 0] with x hxB hx0
  set t : ℝ := x ^ (δ / 2) with htdef
  have ht1 : 1 ≤ t := hB1.trans hxB
  have hlog : Real.log x ≤ t / (δ / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hxδ : x ^ δ = t * t := by
    rw [htdef, ← Real.rpow_add hx0]; congr 1; ring
  rw [hxδ]
  have h1 : (1 + a * (1 + Real.log x)) * C ≤ (1 + a) * C + a * C * (t / (δ / 2)) := by
    have : a * C * Real.log x ≤ a * C * (t / (δ / 2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith
  have h2 : a * C * (t / (δ / 2)) = a * C * (2 / δ) * t := by field_simp
  have h3 : (1 + a) * C ≤ (1 + a) * C * t := by
    have : 0 ≤ (1 + a) * C := by positivity
    nlinarith
  have h4 : (1 + a) * C * t + a * C * (2 / δ) * t ≤ B * t := by
    rw [hB]; nlinarith
  nlinarith

end Asymptotics

section Main

variable (d : Sizes)

/-- **`Step61Pin`** (`lemma:step6-1`), energy sequence, per time
sequence `u` with `0 ≤ u ≤ 1 - N^{-1+τ}`; input (`Eq:L-KGt`) at `u` (`InitLK`, used at `k = 1`). -/
def Step61Pin (κ τ : ℝ) (E u : ℕ → ℝ) : Prop :=
  0 < κ → 0 < τ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ u n) → (∀ n, u n < 1) → SizeTendsto d →
    RangeCond d τ u → InitLK d E u → Step61Concl d E u

/-- **`lemma:step6-1`**: `𝔼⟨(G_u - m)E_a⟩ ≺ M_u^{-2}`, from the input
(`Eq:L-KGt`) at `u` (`InitLK` at `k = 1`), per energy and time sequence.  Argument: the resolvent
identity and Gaussian integration by parts give the self-consistent equation
`x = u m² S x + y` on `Z_L²` (`step61_selfcons`); `Θ_{u m²}` inverts it with the d = 2 short-edge
row sum `1 + cShortRow κ (1 + log L)` (`xiRowBoundShort`); `y` is bounded by the second moments of
`G_bb - m` (`momentDomAt_of_stochDomAt`). -/
theorem step61 (κ τ : ℝ) (E u : ℕ → ℝ) : Step61Pin d κ τ E u := by
  intro hκ hτ hE hu0 hu1 hsize hrange hinit ε hε
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hsz : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop := hsize
  obtain ⟨C, hC, hCn⟩ := step61_moment d κ τ E u hκ hτ hE hu0 hu1 hsize hrange hinit (ε / 2)
    (half_pos hε) 1
  have hcs : 0 ≤ cShortRow κ := by
    have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    unfold cShortRow
    have : 0 ≤ 2 * cProp5 := by unfold cProp5; positivity
    positivity
  have habs := hsz.eventually (step61_log_absorb (cShortRow κ) C (ε / 2) hcs hC (half_pos hε))
  filter_upwards [hCn, habs] with n hn hnabs a
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hL3 := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hW2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast d.W_pos n)
  have hL1r : (1 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast hL1
  have hL2N : (d.L n : ℝ) ^ 2 ≤ N := by
    rw [hNdef, Sizes.size_eq]
    push_cast
    exact le_mul_of_one_le_left (sq_nonneg _) hW2
  have hLN : (d.L n : ℝ) ≤ N := (le_self_pow₀ hL1r two_ne_zero).trans hL2N
  have hNge1 : (1 : ℝ) ≤ N := hL1r.trans hLN
  have hNpos : 0 < N := by linarith
  set M : ℝ := scaleM (d.L n) (d.W n) (E n) (u n) with hMdef
  have hMpos : 0 < M := scaleM_pos hL1 (d.W_pos n) (hE2 n) (hu1 n)
  set K : ℝ := C * (N ^ (ε / 2) * (M⁻¹) ^ 2) with hKdef
  -- second moments of `G_bb - m`, transferred from the common probability space
  have hKint : ∀ b : Z2 (d.L n), ∫ ω : Ω (d.L n) (d.W n), ‖gloop (d.L n) (d.W n)
      (HflowBlock (d.L n) (d.W n) (u n) ω) (spectralZ (E n) (u n)) ⟨[true], [b]⟩ -
        spectralM (E n)‖ ^ 2 ∂(P (d.L n) (d.W n)) ≤ K := by
    intro b
    have hz := step61_hz (hE2 n) (hu1 n)
    have hcont : Continuous fun ω' : Ω (d.L n) (d.W n) => ‖gloop (d.L n) (d.W n)
        (HflowBlock (d.L n) (d.W n) (u n) ω') (spectralZ (E n) (u n)) ⟨[true], [b]⟩ -
          spectralM (E n)‖ ^ 2 :=
      (((step61_gloop_cont (d.L n) (d.W n) (u n) hz b).sub continuous_const).norm).pow 2
    have hslice := step61_integral_slice d n (fun ω' : Ω (d.L n) (d.W n) => ‖gloop (d.L n) (d.W n)
        (HflowBlock (d.L n) (d.W n) (u n) ω') (spectralZ (E n) (u n)) ⟨[true], [b]⟩ -
          spectralM (E n)‖ ^ 2) hcont.aestronglyMeasurable
    have hloop : loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => b) =
        (⟨[true], [b]⟩ : LoopIdx (Z2 (d.L n))) := by simp [loopOf]
    have hpt : ∀ ω : Sizes.SeqΩ d, |lkGen (d.L n) (d.W n) (E n) (u n)
        (Sizes.seqHflow d n (u n) ω) (fun _ : Fin 1 => true) (fun _ : Fin 1 => b)| ^ (2 * 1) =
        ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) (u n) (Sizes.slice d n ω))
          (spectralZ (E n) (u n)) ⟨[true], [b]⟩ - spectralM (E n)‖ ^ 2 := by
      intro ω
      have hK' : KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (⟨[true], [b]⟩ : LoopIdx (Z2 (d.L n))) =
          spectralM (E n) := by
        rw [← hloop]; exact step61_Kcal_true (d.L n) (d.W n) (E n) (u n) b
      simp only [lkGen, hloop, hK', abs_norm, mul_one]
      rfl
    have h' := hn ((), fun _ => true, fun _ => b)
    simp only [Nat.cast_one, mul_one, pow_one] at h'
    calc ∫ ω, ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) (u n) ω)
            (spectralZ (E n) (u n)) ⟨[true], [b]⟩ - spectralM (E n)‖ ^ 2 ∂(P (d.L n) (d.W n))
        = ∫ ω, ‖gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) (u n) (Sizes.slice d n ω))
            (spectralZ (E n) (u n)) ⟨[true], [b]⟩ - spectralM (E n)‖ ^ 2 ∂(Sizes.seqP d) :=
          hslice.symm
      _ = ∫ ω, |lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
            (fun _ : Fin 1 => true) (fun _ : Fin 1 => b)| ^ (2 * 1) ∂(Sizes.seqP d) := by
          congr 1; funext ω; exact (hpt ω).symm
      _ ≤ K := by simpa only [hKdef, hMdef, hNdef] using h'
  have hz := step61_hz (hE2 n) (hu1 n)
  have hexp : oneLoopExpErr d n (E n) (u n) a =
      (∫ ω : Ω (d.L n) (d.W n), gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) (u n) ω)
        (spectralZ (E n) (u n)) ⟨[true], [a]⟩ ∂(P (d.L n) (d.W n))) - spectralM (E n) := by
    have hslice := step61_integral_slice d n (fun ω' : Ω (d.L n) (d.W n) =>
      gloop (d.L n) (d.W n) (HflowBlock (d.L n) (d.W n) (u n) ω') (spectralZ (E n) (u n))
        ⟨[true], [a]⟩) (step61_gloop_cont (d.L n) (d.W n) (u n) hz a).aestronglyMeasurable
    unfold oneLoopExpErr
    exact congrArg (fun x => x - spectralM (E n)) hslice
  have hbound := step61_expErr_le (d.L n) (d.W n) (d.three_le_L n) hκ (hE n) (hu0 n) (hu1 n)
    hKint a
  have hlog : Real.log (d.L n : ℝ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < d.L n)) hLN
  have hK0 : 0 ≤ (N ^ (ε / 2) * (M⁻¹) ^ 2) := by positivity
  calc ‖oneLoopExpErr d n (E n) (u n) a‖
      ≤ (1 + cShortRow κ * (1 + Real.log (d.L n : ℝ))) * K := by rw [hexp]; exact hbound
    _ ≤ (1 + cShortRow κ * (1 + Real.log N)) * K := by
        have : 0 ≤ K := mul_nonneg hC.le hK0
        gcongr
    _ = ((1 + cShortRow κ * (1 + Real.log N)) * C) * (N ^ (ε / 2) * (M⁻¹) ^ 2) := by
        rw [hKdef]; ring
    _ ≤ N ^ (ε / 2) * (N ^ (ε / 2) * (M⁻¹) ^ 2) := by gcongr
    _ = N ^ ε * (M ^ 2)⁻¹ := by
        rw [← mul_assoc, ← Real.rpow_add hNpos, inv_pow]
        congr 2
        ring

end Main

end RBM.Evol
