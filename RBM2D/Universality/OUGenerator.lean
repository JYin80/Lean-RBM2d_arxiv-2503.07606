/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.OU
import RBM2D.Universality.OUHessian
import RBM2D.Gauss.SteinMatrix
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The OU generator identity

The second-order Gaussian interpolation identity behind `(EMCTE2)`,

  `d/dt E Φ(𝐇_t) = -½ e^{-t} ∑_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(𝐇_t)`,

for `𝐇_t = ouMat L W t = e^{-t/2} H + √(1 - e^{-t}) H'` on the carrier `ouP L W = P ⊗ gueP`,
`S°_{ab} = centeredVarianceEntry L W a b = svar a b - N⁻¹`, and test functions `Φ` that are `C²`
near every Hermitian matrix with value and first two Fréchet derivatives bounded on Hermitian
matrices (`TestFunH`).

Every matrix that occurs, `𝐇_t(ω)` and `Y + a Xmat ω` with `Y` Hermitian, is Hermitian, so the
argument works at Hermitian points directly (`ContDiffAt` at Hermitian points is all it reads).

Proof: the pointwise chain rule in `t` along `ouMat`, differentiation under the
integral dominated on `Ioi (t/2)`, Stein's identity for each of the two independent Gaussian
fields (`RBM.Gauss.GaussianProduct.stein`, with the variances `gvar L W` for `P L W` and
`gueVar L W` for `gueP L W`) under Fubini, and the collapse of the used coordinates to the index
pairs, once with `svar` and once with the constant `N⁻¹`; the weights combine to
`svar - N⁻¹ = centeredVarianceEntry` because `a'(t) a(t) = -½ e^{-t}`, `b'(t) b(t) = ½ e^{-t}`.

Vocabulary: the index set is `Idx L W`; `RBM.Green.Bmat L W`; `RBM.Gauss.usedCoords`; `svar`;
`RBM.Endpoints.gueVar L W` (`N⁻¹` on the diagonal, `(2N)⁻¹` off it, `N = (W L)²`); the carrier
is `ouP L W`; the Stieltjes transform is `stieltjesN`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal
open scoped Matrix.Norms.L2Operator

/-- **Test functions for the OU generator identity**: `C²` near every Hermitian matrix, with the
value and the first
two Fréchet derivatives bounded on Hermitian matrices. -/
def TestFunH (L W : ℕ) [NeZero L] [NeZero W] (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) : Prop :=
  (∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)

/-! ## 1. Calculus at Hermitian points -/

section Basic

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

private theorem OUGenerator_continuousAt_fderiv (h : TestFunH L W Φ)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) : ContinuousAt (fderiv ℝ Φ) M :=
  ((h.1 M hM).fderiv_right (m := 1) (by norm_num)).continuousAt

private theorem OUGenerator_continuousAt_fderiv2 (h : TestFunH L W Φ)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContinuousAt (fderiv ℝ (fderiv ℝ Φ)) M :=
  (((h.1 M hM).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt

private theorem OUGenerator_differentiableAt_fderiv (h : TestFunH L W Φ)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    DifferentiableAt ℝ (fderiv ℝ Φ) M :=
  ((h.1 M hM).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- A function continuous at every Hermitian matrix, composed with a continuous map into the
Hermitian matrices, is continuous. -/
private theorem OUGenerator_continuous_comp {α E : Type*} [TopologicalSpace α]
    [TopologicalSpace E] {F : Matrix (Idx L W) (Idx L W) ℂ → E}
    (hF : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ContinuousAt F M)
    {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f) (hherm : ∀ a, (f a).IsHermitian) :
    Continuous fun a => F (f a) :=
  continuous_iff_continuousAt.2 fun a => (hF _ (hherm a)).comp hf.continuousAt

private theorem OUGenerator_continuous_Phi (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) : Continuous fun a => Φ (f a) :=
  OUGenerator_continuous_comp (fun M hM => (h.1 M hM).continuousAt) hf hherm

private theorem OUGenerator_continuous_coordD1 (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : Coord L W) :
    Continuous fun a => coordD1 L W Φ (f a) p :=
  (OUGenerator_continuous_comp (fun M hM => OUGenerator_continuousAt_fderiv h hM) hf
    hherm).clm_apply continuous_const

private theorem OUGenerator_continuous_coordD2 (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : Coord L W) :
    Continuous fun a => coordD2 L W Φ (f a) p :=
  ((OUGenerator_continuous_comp (fun M hM => OUGenerator_continuousAt_fderiv2 h hM) hf
    hherm).clm_apply continuous_const).clm_apply continuous_const

private theorem OUGenerator_norm_coordD1_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (p : Coord L W) :
    ‖coordD1 L W Φ M p‖ ≤ C * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ Φ M).le_opNorm _) (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))

private theorem OUGenerator_norm_coordD2_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (p : Coord L W) :
    ‖coordD2 L W Φ M p‖
      ≤ C * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))) (norm_nonneg _))

/-- Differentiating `M ↦ fderiv ℝ Φ M A` in `M`, where `fderiv ℝ Φ` is differentiable. -/
private theorem OUGenerator_hasFDerivAt_fderiv_apply {M : Matrix (Idx L W) (Idx L W) ℂ}
    (h : DifferentiableAt ℝ (fderiv ℝ Φ) M) (A : Matrix (Idx L W) (Idx L W) ℂ) :
    HasFDerivAt (fun M' => fderiv ℝ Φ M' A) ((fderiv ℝ (fderiv ℝ Φ) M).flip A) M := by
  have hc := (h.hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- The first derivative of `Φ` in the direction `Xmat ω` is the coordinate sum of the
directional derivatives. -/
private theorem OUGenerator_fderiv_apply_Xmat (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (ω : Ω L W) :
    fderiv ℝ Φ M (Xmat L W ω) = ∑ p ∈ usedCoords L W, ω p • coordD1 L W Φ M p := by
  conv_lhs => rw [RBM.Green.Xmat_eq_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end Basic


/-! ## 2. The interpolation coefficients and the pointwise chain rule -/

section Chain

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `d/dt e^{-t/2}`. -/
private def OUGenerator_aC (x : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.exp (-x / 2)

/-- `d/dt √(1 - e^{-t})`. -/
private def OUGenerator_bC (x : ℝ) : ℝ := Real.exp (-x) / (2 * Real.sqrt (1 - Real.exp (-x)))

/-- The band-field coordinate sum `∑_p ω₁_p ∂_p Φ(𝐇_x(ω))`. -/
private def OUGenerator_S1 (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (x : ℝ)
    (z : Ω L W × Ω L W) : ℂ :=
  ∑ p ∈ usedCoords L W, z.1 p • coordD1 L W Φ (ouMat L W x z) p

/-- The GUE-field coordinate sum `∑_p ω₂_p ∂_p Φ(𝐇_x(ω))`. -/
private def OUGenerator_S2 (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (x : ℝ)
    (z : Ω L W × Ω L W) : ℂ :=
  ∑ p ∈ usedCoords L W, z.2 p • coordD1 L W Φ (ouMat L W x z) p

/-- The pointwise `t`-derivative of `Φ (𝐇_t(ω))`. -/
private def OUGenerator_dF (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (x : ℝ)
    (z : Ω L W × Ω L W) : ℂ :=
  OUGenerator_aC x • OUGenerator_S1 L W Φ x z + OUGenerator_bC x • OUGenerator_S2 L W Φ x z

end Chain

private theorem OUGenerator_hasDerivAt_band (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (OUGenerator_aC t) t := by
  unfold OUGenerator_aC
  have hg : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2 : ℝ)) t := by
    have h := (hasDerivAt_id t).neg.div_const (2 : ℝ)
    norm_num at h
    convert h using 1
  have h2 := hg.exp
  rw [mul_comm] at h2
  exact h2

private theorem OUGenerator_hasDerivAt_zeta (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) (Real.exp (-t)) t := by
  have hg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have h2 := hg.exp
  have h3 := h2.const_sub (1 : ℝ)
  simp only [mul_neg_one, neg_neg] at h3
  exact h3

private theorem OUGenerator_zeta_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private theorem OUGenerator_hasDerivAt_gue {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-s))) (OUGenerator_bC t) t :=
  (OUGenerator_hasDerivAt_zeta t).sqrt (OUGenerator_zeta_pos ht).ne'

section Chain2

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

/-- **The pointwise `t`-derivative of `Φ` along the OU interpolation.** -/
private theorem OUGenerator_hasDerivAt_pointwise (h : TestFunH L W Φ) (z : Ω L W × Ω L W)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Φ (ouMat L W s z)) (OUGenerator_dF L W Φ t z) t := by
  have hM : HasDerivAt (fun s : ℝ => ouMat L W s z)
      (OUGenerator_aC t • Xmat L W z.1 + OUGenerator_bC t • Xmat L W z.2) t :=
    ((OUGenerator_hasDerivAt_band t).smul_const (Xmat L W z.1)).add
      ((OUGenerator_hasDerivAt_gue ht).smul_const (Xmat L W z.2))
  have key := ((h.1 _ (ouMat_isHermitian L W t z)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hM
  rw [map_add, map_smul, map_smul, OUGenerator_fderiv_apply_Xmat,
    OUGenerator_fderiv_apply_Xmat] at key
  exact key

end Chain2

/-! ## 3. Integrability of the coordinates, continuity of `ouMat` -/

section Integrability

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OUGenerator_integrable_coord (v : Coord L W → ℝ≥0) (c : Coord L W) :
    Integrable (fun ω : Ω L W => ω c) (Measure.infinitePi fun c => gaussianReal 0 (v c)) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c)
      (Measure.infinitePi fun c => gaussianReal 0 (v c)) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x)
      ((Measure.infinitePi fun c => gaussianReal 0 (v c)).map fun ω => ω c) := by
    rw [Measure.infinitePi_map_eval]
    exact RBM.integrable_id_gaussianReal
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem OUGenerator_integrable_fst (c : Coord L W) :
    Integrable (fun z : Ω L W × Ω L W => z.1 c) (ouP L W) :=
  (OUGenerator_integrable_coord (gvar L W) c).comp_fst (gueP L W)

private theorem OUGenerator_integrable_snd (c : Coord L W) :
    Integrable (fun z : Ω L W × Ω L W => z.2 c) (ouP L W) :=
  (OUGenerator_integrable_coord (gueVar L W) c).comp_snd (P L W)

private theorem OUGenerator_continuous_ouMat (s : ℝ) :
    Continuous fun z : Ω L W × Ω L W => ouMat L W s z :=
  (((continuous_Xmat L W).comp continuous_fst).const_smul (Real.exp (-s / 2))).add
    (((continuous_Xmat L W).comp continuous_snd).const_smul (Real.sqrt (1 - Real.exp (-s))))

end Integrability

/-! ## 4. Differentiating under the joint integral -/

section Dominated

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

private theorem OUGenerator_abs_aC_le {x : ℝ} (hx : 0 ≤ x) : |OUGenerator_aC x| ≤ 1 / 2 := by
  unfold OUGenerator_aC
  have he1 : Real.exp (-x / 2) ≤ 1 := by
    have : -x / 2 ≤ 0 := by linarith
    exact Real.exp_le_one_iff.mpr this
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_of_pos (Real.exp_pos _)]
  nlinarith [Real.exp_pos (-x / 2)]

private theorem OUGenerator_abs_bC_le {t x : ℝ} (ht : 0 < t / 2) (hx : t / 2 < x) :
    |OUGenerator_bC x| ≤ Real.exp (-(t / 2)) / (2 * Real.sqrt (1 - Real.exp (-(t / 2)))) := by
  have hzt2 : 0 < 1 - Real.exp (-(t / 2)) := OUGenerator_zeta_pos ht
  have hzx : 0 < 1 - Real.exp (-x) := OUGenerator_zeta_pos (lt_trans ht hx)
  have hexp : Real.exp (-x) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hmono : 1 - Real.exp (-(t / 2)) ≤ 1 - Real.exp (-x) := by linarith
  unfold OUGenerator_bC
  rw [abs_of_pos (by positivity)]
  gcongr

/-- The norm bound for the two coordinate sums. -/
private theorem OUGenerator_norm_S1_le {C₁ : ℝ}
    (hC₁ : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C₁)
    (x : ℝ) (z : Ω L W × Ω L W) :
    ‖OUGenerator_S1 L W Φ x z‖ ≤ ∑ p ∈ usedCoords L W,
      |z.1 p| * (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p) (abs_nonneg _)

private theorem OUGenerator_norm_S2_le {C₁ : ℝ}
    (hC₁ : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C₁)
    (x : ℝ) (z : Ω L W × Ω L W) :
    ‖OUGenerator_S2 L W Φ x z‖ ≤ ∑ p ∈ usedCoords L W,
      |z.2 p| * (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p) (abs_nonneg _)

private theorem OUGenerator_continuous_S1 (h : TestFunH L W Φ) (x : ℝ) :
    Continuous fun z : Ω L W × Ω L W => OUGenerator_S1 L W Φ x z :=
  continuous_finsetSum _ fun p _ => ((continuous_apply p).comp continuous_fst).smul
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p)

private theorem OUGenerator_continuous_S2 (h : TestFunH L W Φ) (x : ℝ) :
    Continuous fun z : Ω L W × Ω L W => OUGenerator_S2 L W Φ x z :=
  continuous_finsetSum _ fun p _ => ((continuous_apply p).comp continuous_snd).smul
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p)

private theorem OUGenerator_integrable_S1 (h : TestFunH L W Φ) (x : ℝ) :
    Integrable (fun z : Ω L W × Ω L W => OUGenerator_S1 L W Φ x z) (ouP L W) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  refine integrable_finsetSum _ fun p _ => ?_
  exact (OUGenerator_integrable_fst p).smul_bdd (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p)

private theorem OUGenerator_integrable_S2 (h : TestFunH L W Φ) (x : ℝ) :
    Integrable (fun z : Ω L W × Ω L W => OUGenerator_S2 L W Φ x z) (ouP L W) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  refine integrable_finsetSum _ fun p _ => ?_
  exact (OUGenerator_integrable_snd p).smul_bdd (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p)

/-- **The generator identity, joint-integral form, before Stein.**  Differentiation under the
integral sign over `ouP L W`, dominated on `Set.Ioi (t/2)` (the coefficient `√(1 - e^{-t})` has a
square-root singularity at `0`, hence `t > 0` and the `t/2` margin). -/
private theorem OUGenerator_hasDerivAt_integral_joint (h : TestFunH L W Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, Φ (ouMat L W s z) ∂(ouP L W))
      (∫ z, OUGenerator_dF L W Φ t z ∂(ouP L W)) t := by
  obtain ⟨C₀, hC₀⟩ := h.2.1
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  have ht2 : 0 < t / 2 := by linarith
  have hcontF : ∀ x : ℝ, Continuous fun z : Ω L W × Ω L W => Φ (ouMat L W x z) :=
    fun x => OUGenerator_continuous_Phi h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z)
  have hcontdF : ∀ x : ℝ, Continuous fun z : Ω L W × Ω L W => OUGenerator_dF L W Φ x z :=
    fun x => ((OUGenerator_continuous_S1 h x).const_smul (OUGenerator_aC x)).add
      ((OUGenerator_continuous_S2 h x).const_smul (OUGenerator_bC x))
  set B1 : ℝ := Real.exp (-(t / 2)) / (2 * Real.sqrt (1 - Real.exp (-(t / 2)))) with hB1
  set bound : Ω L W × Ω L W → ℝ := fun z =>
    (1 / 2 : ℝ) * (∑ p ∈ usedCoords L W,
        |z.1 p| * (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖))
      + B1 * (∑ p ∈ usedCoords L W,
        |z.2 p| * (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)) with hbound_def
  have hbound : ∀ᵐ z ∂(ouP L W), ∀ x ∈ Set.Ioi (t / 2),
      ‖OUGenerator_dF L W Φ x z‖ ≤ bound z := by
    refine Eventually.of_forall fun z x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := by
      have : t / 2 < x := hx
      linarith
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (OUGenerator_abs_aC_le hx0) (OUGenerator_norm_S1_le hC₁ x z)
        (norm_nonneg _) (by norm_num)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (OUGenerator_abs_bC_le ht2 hx) (OUGenerator_norm_S2_le hC₁ x z)
        (norm_nonneg _) (by positivity)
  have hbndint : Integrable bound (ouP L W) := by
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact integrable_finsetSum _ fun p _ => (OUGenerator_integrable_fst p).abs.mul_const _
    · exact integrable_finsetSum _ fun p _ => (OUGenerator_integrable_snd p).abs.mul_const _
  have hdiff : ∀ᵐ z ∂(ouP L W), ∀ x ∈ Set.Ioi (t / 2),
      HasDerivAt (fun s : ℝ => Φ (ouMat L W s z)) (OUGenerator_dF L W Φ x z) x :=
    Eventually.of_forall fun z x hx => OUGenerator_hasDerivAt_pointwise h z (lt_trans ht2 hx)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ouP L W) (𝕜 := ℝ)
    (F := fun (s : ℝ) (z : Ω L W × Ω L W) => Φ (ouMat L W s z))
    (F' := fun (s : ℝ) (z : Ω L W × Ω L W) => OUGenerator_dF L W Φ s z)
    (x₀ := t) (s := Set.Ioi (t / 2))
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable)
    ((memLp_top_of_bound (hcontF t).aestronglyMeasurable C₀
      (Eventually.of_forall fun z => hC₀ _ (ouMat_isHermitian L W t z))).integrable le_top)
    (hcontdF t).aestronglyMeasurable hbound hbndint hdiff).2

end Dominated

/-! ## 5. Stein's identity for each field, under Fubini -/

section Stein

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

private theorem OUGenerator_isHermitian_shift {Y : Matrix (Idx L W) (Idx L W) ℂ}
    (hY : Y.IsHermitian) (a : ℝ) (ω : Ω L W) : (Y + a • Xmat L W ω).IsHermitian :=
  hY.add ((Xmat_isHermitian L W ω).smul (IsSelfAdjoint.all _))

/-- **The coordinate derivative of `coordD1` along a shifted scalar-linear line.**  Moving the
Gaussian coordinate `p` of `ω` moves the matrix argument along `a • Bmat p`; this is where
Stein's identity turns a coordinate value into a second derivative. -/
private theorem OUGenerator_hasDerivAt_coordD1_shift (h : TestFunH L W Φ)
    (Y : Matrix (Idx L W) (Idx L W) ℂ) (hY : Y.IsHermitian) (a : ℝ) (ω : Ω L W)
    {p : Coord L W} (hp : p ∈ usedCoords L W) :
    HasDerivAt
      (fun t : ℝ => coordD1 L W Φ (Y + a • Xmat L W (Function.update ω p t)) p)
      (a • coordD2 L W Φ (Y + a • Xmat L W ω) p) (ω p) := by
  set B := RBM.Green.Bmat L W p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Y + a • Xmat L W (Function.update ω p t)
      = (Y + a • Xmat L W ω) + (a * (t - ω p)) • B := by
    intro t
    rw [RBM.Green.GreenDeriv_Xmat_update ω hp t, smul_add, smul_smul]
    abel
  have hscal : HasDerivAt (fun t : ℝ => a * (t - ω p)) a (ω p) := by
    simpa using ((hasDerivAt_id (ω p)).sub_const (ω p)).const_mul a
  have hpath : HasDerivAt (fun t : ℝ => Y + a • Xmat L W (Function.update ω p t))
      (a • B) (ω p) := by
    have h1 : HasDerivAt (fun t : ℝ => (Y + a • Xmat L W ω) + (a * (t - ω p)) • B)
        (a • B) (ω p) := (hscal.smul_const B).const_add _
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun t => hline t)
  have hself : Y + a • Xmat L W (Function.update ω p (ω p)) = Y + a • Xmat L W ω := by
    rw [Function.update_eq_self]
  have hF : HasFDerivAt (fun M' => fderiv ℝ Φ M' B)
      ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat L W ω)).flip B) (Y + a • Xmat L W ω) :=
    OUGenerator_hasFDerivAt_fderiv_apply
      (OUGenerator_differentiableAt_fderiv h (OUGenerator_isHermitian_shift hY a ω)) B
  have hF' : HasFDerivAt (fun M' => fderiv ℝ Φ M' B)
      ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat L W ω)).flip B)
      (Y + a • Xmat L W (Function.update ω p (ω p))) := by
    rw [hself]; exact hF
  have key := hF'.comp_hasDerivAt (ω p) hpath
  have hval : ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat L W ω)).flip B) (a • B)
      = a • coordD2 L W Φ (Y + a • Xmat L W ω) p := by
    rw [ContinuousLinearMap.flip_apply, map_smul]
    rfl
  rw [hval] at key
  exact key

/-- **Stein's identity for one Gaussian field, under a fixed Hermitian shift.** -/
private theorem OUGenerator_stein_shift (v : Coord L W → ℝ≥0) (h : TestFunH L W Φ)
    (Y : Matrix (Idx L W) (Idx L W) ℂ) (hY : Y.IsHermitian) (a : ℝ) {p : Coord L W}
    (hp : p ∈ usedCoords L W) :
    ∫ ω, ω p • coordD1 L W Φ (Y + a • Xmat L W ω) p ∂(GaussianProduct.law v)
      = (v p : ℝ) •
          ∫ ω, a • coordD2 L W Φ (Y + a • Xmat L W ω) p ∂(GaussianProduct.law v) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  have hcont : Continuous fun ω : Ω L W => Y + a • Xmat L W ω :=
    continuous_const.add ((continuous_Xmat L W).const_smul a)
  have hherm := OUGenerator_isHermitian_shift hY a
  exact GaussianProduct.stein v p
    (fun ω => coordD1 L W Φ (Y + a • Xmat L W ω) p)
    (fun ω => a • coordD2 L W Φ (Y + a • Xmat L W ω) p)
    (OUGenerator_continuous_coordD1 h hcont hherm p)
    ((OUGenerator_continuous_coordD2 h hcont hherm p).const_smul a)
    (fun ω => OUGenerator_hasDerivAt_coordD1_shift h Y hY a ω hp)
    ⟨C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖,
      fun ω => OUGenerator_norm_coordD1_le hC₁ (hherm ω) p⟩
    ⟨|a| * (C₂ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖),
      fun ω => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (OUGenerator_norm_coordD2_le hC₂ (hherm ω) p)
          (abs_nonneg _)⟩

private theorem OUGenerator_integrable_coordD2 (h : TestFunH L W Φ) (x : ℝ) (p : Coord L W) :
    Integrable (fun z : Ω L W × Ω L W => coordD2 L W Φ (ouMat L W x z) p) (ouP L W) := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  exact (memLp_top_of_bound
    (OUGenerator_continuous_coordD2 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p).aestronglyMeasurable
    (C₂ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD2_le hC₂ (ouMat_isHermitian L W x z) p)).integrable le_top

private theorem OUGenerator_integrable_term_fst (h : TestFunH L W Φ) (x : ℝ) (p : Coord L W) :
    Integrable (fun z : Ω L W × Ω L W => z.1 p • coordD1 L W Φ (ouMat L W x z) p)
      (ouP L W) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  exact (OUGenerator_integrable_fst p).smul_bdd (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p)

private theorem OUGenerator_integrable_term_snd (h : TestFunH L W Φ) (x : ℝ) (p : Coord L W) :
    Integrable (fun z : Ω L W × Ω L W => z.2 p • coordD1 L W Φ (ouMat L W x z) p)
      (ouP L W) := by
  obtain ⟨C₁, hC₁⟩ := h.2.2.1
  exact (OUGenerator_integrable_snd p).smul_bdd (C₁ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖)
    (OUGenerator_continuous_coordD1 h (OUGenerator_continuous_ouMat x)
      (fun z => ouMat_isHermitian L W x z) p).aestronglyMeasurable
    (Eventually.of_forall fun z =>
      OUGenerator_norm_coordD1_le hC₁ (ouMat_isHermitian L W x z) p)

/-- **The band-field Stein identity, at the level of the joint measure.** -/
private theorem OUGenerator_joint_stein_fst (h : TestFunH L W Φ) (t : ℝ) {p : Coord L W}
    (hp : p ∈ usedCoords L W) :
    ∫ z, z.1 p • coordD1 L W Φ (ouMat L W t z) p ∂(ouP L W)
      = (gvar L W p : ℝ) • Real.exp (-t / 2) •
          ∫ z, coordD2 L W Φ (ouMat L W t z) p ∂(ouP L W) := by
  have hInt1 := OUGenerator_integrable_term_fst h t p
  have hInt2 := OUGenerator_integrable_coordD2 h t p
  unfold ouP
  have hstep : ∀ ω2 : Ω L W, ∫ ω1, ω1 p • coordD1 L W Φ (ouMat L W t (ω1, ω2)) p ∂(P L W)
      = (gvar L W p : ℝ) • Real.exp (-t / 2) •
          ∫ ω1, coordD2 L W Φ (ouMat L W t (ω1, ω2)) p ∂(P L W) := by
    intro ω2
    have hs : ∫ ω1, ω1 p • coordD1 L W Φ
          (Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2 + Real.exp (-t / 2) • Xmat L W ω1) p
          ∂(P L W)
        = (gvar L W p : ℝ) • ∫ ω1, Real.exp (-t / 2) • coordD2 L W Φ
          (Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2 + Real.exp (-t / 2) • Xmat L W ω1) p
          ∂(P L W) :=
      OUGenerator_stein_shift (gvar L W) h _
        ((Xmat_isHermitian L W ω2).smul (IsSelfAdjoint.all _)) _ hp
    have hcomm : ∀ ω1 : Ω L W, ouMat L W t (ω1, ω2)
        = Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2 + Real.exp (-t / 2) • Xmat L W ω1 :=
      fun ω1 => add_comm _ _
    simp only [hcomm] at hs ⊢
    rw [hs, integral_smul]
  rw [integral_prod_symm _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod_symm _ hInt2]

/-- **The GUE-field Stein identity, at the level of the joint measure.** -/
private theorem OUGenerator_joint_stein_snd (h : TestFunH L W Φ) (t : ℝ) {p : Coord L W}
    (hp : p ∈ usedCoords L W) :
    ∫ z, z.2 p • coordD1 L W Φ (ouMat L W t z) p ∂(ouP L W)
      = (gueVar L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) •
          ∫ z, coordD2 L W Φ (ouMat L W t z) p ∂(ouP L W) := by
  have hInt1 := OUGenerator_integrable_term_snd h t p
  have hInt2 := OUGenerator_integrable_coordD2 h t p
  unfold ouP
  have hstep : ∀ ω1 : Ω L W, ∫ ω2, ω2 p • coordD1 L W Φ (ouMat L W t (ω1, ω2)) p ∂(gueP L W)
      = (gueVar L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) •
          ∫ ω2, coordD2 L W Φ (ouMat L W t (ω1, ω2)) p ∂(gueP L W) := by
    intro ω1
    have hs : ∫ ω2, ω2 p • coordD1 L W Φ
          (Real.exp (-t / 2) • Xmat L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2) p
          ∂(gueP L W)
        = (gueVar L W p : ℝ) • ∫ ω2, Real.sqrt (1 - Real.exp (-t)) • coordD2 L W Φ
          (Real.exp (-t / 2) • Xmat L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2) p
          ∂(gueP L W) :=
      OUGenerator_stein_shift (gueVar L W) h _
        ((Xmat_isHermitian L W ω1).smul (IsSelfAdjoint.all _)) _ hp
    change ∫ ω2, ω2 p • coordD1 L W Φ
          (Real.exp (-t / 2) • Xmat L W ω1 + Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω2) p
          ∂(gueP L W) = _
    rw [hs, integral_smul]
    rfl
  rw [integral_prod _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod _ hInt2]

end Stein

/-! ## 6. The coordinate sum collapses to the index-pair sum

The sum over the used coordinates collapses to the sum over index pairs; the bookkeeping lemma is
a private re-proof of the private `IBP_sum_used_eq_sum_pairs` of `Green/IBP.lean`. -/

section Collapse

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

/-- `coordD2` is unchanged when the two indices of the coordinate are swapped. -/
private theorem OUGenerator_coordD2_swap (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) (b : Bool) :
    coordD2 L W Φ M (i, j, b) = coordD2 L W Φ M (j, i, b) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  cases b
  · change fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W i j false) (RBM.Green.Bmat L W i j false)
      = fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W j i false) (RBM.Green.Bmat L W j i false)
    rw [Bmat_swap_false L W hij]
    simp
  · change fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W i j true) (RBM.Green.Bmat L W i j true)
      = fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W j i true) (RBM.Green.Bmat L W j i true)
    rw [Bmat_swap_true L W i j]

omit [NeZero L] [NeZero W] in
/-- The variance of a coordinate, read off from the index pair. -/
private theorem OUGenerator_gvar_eq (p : Coord L W) :
    (gvar L W p : ℝ)
      = if p.1 = p.2.1 then svar L W p.1 p.2.1 else svar L W p.1 p.2.1 / 2 := by
  obtain ⟨i, j, b⟩ := p
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]; exact gvar_diag L W i b
  · rw [ite_eq_right hij]; exact gvar_offDiag L W i j b hij

/-- The GUE coordinate variance, read off from the index pair: `N⁻¹` on the diagonal and
`N⁻¹ / 2` off it, `N = card (Idx L W) = (W L)²`. -/
private theorem OUGenerator_gueVar_eq (p : Coord L W) :
    (gueVar L W p : ℝ)
      = if p.1 = p.2.1 then (Fintype.card (Idx L W) : ℝ)⁻¹
        else (Fintype.card (Idx L W) : ℝ)⁻¹ / 2 := by
  rw [card_Idx_eq L W]
  unfold gueVar
  by_cases hp : p.1 = p.2.1
  · simp [hp]
  · simp only [hp, ite_false]
    push_cast
    rw [mul_inv]
    ring

/-- Halving is injective on an `ℝ`-module: `X + X = Y + Y` forces `X = Y`. -/
private theorem OUGenerator_eq_of_add_self_eq_add_self {V : Type*} [AddCommGroup V]
    [Module ℝ V] {X Y : V} (h : X + X = Y + Y) : X = Y := by
  have h2 : ((2 : ℝ)⁻¹ * 2) • X = ((2 : ℝ)⁻¹ * 2) • Y := by
    rw [mul_smul, mul_smul, two_smul, two_smul, h]
  have hc : ((2 : ℝ)⁻¹ * 2) = 1 := by norm_num
  rwa [hc, one_smul, one_smul] at h2

/-- The off-diagonal bookkeeping: a quarter of each of the two copies, twice over, is a half. -/
private theorem OUGenerator_smul_quarter_pair {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (A B : V) :
    (c / 2) • A + (c / 2) • B =
      c • (1 / 4 : ℝ) • (A + B) + c • (1 / 4 : ℝ) • (A + B) := by
  rw [smul_smul, ← two_smul ℝ, smul_smul,
    show (2 * (c * (1 / 4)) : ℝ) = c / 2 by ring, smul_add]

/-- A double sum over a square index set is determined by the swap-symmetrization of its
summand. -/
private theorem OUGenerator_sum_sum_eq_of_swap_add_eq {ι : Type*} [Fintype ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V] (g h : ι → ι → V)
    (key : ∀ i j, g i j + g j i = h i j + h j i) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, h i j := by
  have e1 : ∀ F : ι → ι → V,
      (∑ i, ∑ j, (F i j + F j i)) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
    intro F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hg : (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := Finset.sum_comm
  have hh : (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := Finset.sum_comm
  refine OUGenerator_eq_of_add_self_eq_add_self ?_
  calc (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g i j)
      = (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g j i) := by rw [← hg]
    _ = ∑ i, ∑ j, (g i j + g j i) := (e1 g).symm
    _ = ∑ i, ∑ j, (h i j + h j i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h j i) := e1 h
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h i j) := by rw [← hh]

/-- **The bookkeeping lemma**.  Summing a
symmetric weight `S` against a symmetric family `f` over the "used" index set equals the full
double sum over ordered pairs, the diagonal separately and the off-diagonal terms weighted by
`1/4`. -/
private theorem OUGenerator_sum_used_eq_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i)
    (f : ι × ι × Bool → V)
    (htt : ∀ i j, f (i, j, true) = f (j, i, true))
    (hff : ∀ i j, f (i, j, false) = f (j, i, false)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, S i j •
          (if i = j then f (i, i, true)
           else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine OUGenerator_sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero]
      exact OUGenerator_smul_quarter_pair _ _ _
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero, zero_add]
      exact OUGenerator_smul_quarter_pair _ _ _

/-- The `wirtSecond` expectation over the joint measure, in terms of the two real directional
derivatives. -/
private theorem OUGenerator_integral_wirtSecond (h : TestFunH L W Φ) (t : ℝ) (i j : Idx L W) :
    ∫ z, wirtSecond L W Φ (ouMat L W t z) i j ∂(ouP L W)
      = if i = j then ∫ z, coordD2 L W Φ (ouMat L W t z) (i, i, true) ∂(ouP L W)
        else (1 / 4 : ℝ) • (∫ z, coordD2 L W Φ (ouMat L W t z) (i, j, true) ∂(ouP L W)
          + ∫ z, coordD2 L W Φ (ouMat L W t z) (i, j, false) ∂(ouP L W)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change wirtSecond L W Φ (ouMat L W t z) i i = _
    rw [wirtSecond, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    have hpt : (fun z : Ω L W × Ω L W => wirtSecond L W Φ (ouMat L W t z) i j)
        = fun z : Ω L W × Ω L W => (1 / 4 : ℝ) • (coordD2 L W Φ (ouMat L W t z) (i, j, true)
            + coordD2 L W Φ (ouMat L W t z) (i, j, false)) := by
      funext z
      rw [wirtSecond, ite_eq_right hij]
    rw [hpt, integral_smul, integral_add (OUGenerator_integrable_coordD2 h t _)
      (OUGenerator_integrable_coordD2 h t _)]

/-- Combining two weighted double sums that share the same values `W i j`: pure `Finset`
algebra. -/
private theorem OUGenerator_sum2_combine {ι : Type*} [Fintype ι] (S1 S2 : ι → ι → ℝ)
    (c1 c2 : ℝ) (V : ι → ι → ℂ) :
    c1 • (∑ i, ∑ j, S1 i j • V i j) + c2 • (∑ i, ∑ j, S2 i j • V i j)
      = ∑ i, ∑ j, (c1 * S1 i j + c2 * S2 i j) • V i j := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, ← add_smul]

end Collapse

/-! ## 7. The generator identity in the paper's `∑_{ab} S°_{ab} ∂_{ab}∂_{ba}` form -/

section Pairs

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

/-- **The generator identity for a `TestFunH`, with `t > 0`.**  The `svar` collapse (band field)
and the constant-weight `N⁻¹` collapse (GUE field) use the same family
`p ↦ ∫ z, coordD2 Φ (𝐇_t z) p` and combine into the single weight
`svar - N⁻¹ = centeredVarianceEntry`, because `a'(t) a(t) = -½ e^{-t}` and
`b'(t) b(t) = ½ e^{-t}`. -/
private theorem OUGenerator_hasDerivAt_integral_pairs (h : TestFunH L W Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, Φ (ouMat L W s z) ∂(ouP L W))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx L W, ∑ b : Idx L W,
          (centeredVarianceEntry L W a b : ℂ) *
            ∫ z, wirtSecond L W Φ (ouMat L W t z) a b ∂(ouP L W)) t := by
  have hbase := OUGenerator_hasDerivAt_integral_joint h ht
  set f : Coord L W → ℂ := fun p => ∫ z, coordD2 L W Φ (ouMat L W t z) p ∂(ouP L W)
    with hf
  have hswap : ∀ (i j : Idx L W) (b : Bool), f (i, j, b) = f (j, i, b) := by
    intro i j b
    simp only [hf]
    exact integral_congr_ae (Eventually.of_forall fun z =>
      OUGenerator_coordD2_swap Φ _ i j b)
  have hband : ∑ p ∈ usedCoords L W, (gvar L W p : ℝ) • f p
      = ∑ i : Idx L W, ∑ j : Idx L W, svar L W i j •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoords L W, (gvar L W p : ℝ) • f p
        = ∑ p ∈ usedCoords L W,
          (if p.1 = p.2.1 then svar L W p.1 p.2.1 else svar L W p.1 p.2.1 / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [OUGenerator_gvar_eq]
    rw [hlhs, show usedCoords L W = Finset.univ.filter
        (fun p : Idx L W × Idx L W × Bool =>
          idxKey L W p.1 < idxKey L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      OUGenerator_sum_used_eq_sum_pairs (idxKey L W) (idxKey_injective L W) (svar L W)
        (svar_comm L W) f (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hgue : ∑ p ∈ usedCoords L W, (gueVar L W p : ℝ) • f p
      = ∑ i : Idx L W, ∑ j : Idx L W, (Fintype.card (Idx L W) : ℝ)⁻¹ •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoords L W, (gueVar L W p : ℝ) • f p
        = ∑ p ∈ usedCoords L W,
          (if p.1 = p.2.1 then (Fintype.card (Idx L W) : ℝ)⁻¹
           else (Fintype.card (Idx L W) : ℝ)⁻¹ / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [OUGenerator_gueVar_eq]
    rw [hlhs, show usedCoords L W = Finset.univ.filter
        (fun p : Idx L W × Idx L W × Bool =>
          idxKey L W p.1 < idxKey L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      OUGenerator_sum_used_eq_sum_pairs (idxKey L W) (idxKey_injective L W)
        (fun _ _ => (Fintype.card (Idx L W) : ℝ)⁻¹) (fun _ _ => rfl) f
        (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hIeq : (∫ z, OUGenerator_dF L W Φ t z ∂(ouP L W))
      = OUGenerator_aC t • (∑ p ∈ usedCoords L W,
              (gvar L W p : ℝ) • Real.exp (-t / 2) • f p)
        + OUGenerator_bC t • (∑ p ∈ usedCoords L W,
              (gueVar L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) • f p) := by
    have hA : Integrable (fun z : Ω L W × Ω L W => OUGenerator_aC t •
        OUGenerator_S1 L W Φ t z) (ouP L W) :=
      Integrable.smul (OUGenerator_aC t) (OUGenerator_integrable_S1 h t)
    have hB : Integrable (fun z : Ω L W × Ω L W => OUGenerator_bC t •
        OUGenerator_S2 L W Φ t z) (ouP L W) :=
      Integrable.smul (OUGenerator_bC t) (OUGenerator_integrable_S2 h t)
    have hS1 : ∫ z, OUGenerator_S1 L W Φ t z ∂(ouP L W)
        = ∑ p ∈ usedCoords L W, ∫ z, z.1 p • coordD1 L W Φ (ouMat L W t z) p ∂(ouP L W) :=
      integral_finsetSum _ (fun p _ => OUGenerator_integrable_term_fst h t p)
    have hS2 : ∫ z, OUGenerator_S2 L W Φ t z ∂(ouP L W)
        = ∑ p ∈ usedCoords L W, ∫ z, z.2 p • coordD1 L W Φ (ouMat L W t z) p ∂(ouP L W) :=
      integral_finsetSum _ (fun p _ => OUGenerator_integrable_term_snd h t p)
    change ∫ z, (OUGenerator_aC t • OUGenerator_S1 L W Φ t z
        + OUGenerator_bC t • OUGenerator_S2 L W Φ t z) ∂(ouP L W) = _
    rw [integral_add hA hB, integral_smul, integral_smul, hS1, hS2,
      Finset.sum_congr rfl (fun p hp => OUGenerator_joint_stein_fst h t hp),
      Finset.sum_congr rfl (fun p hp => OUGenerator_joint_stein_snd h t hp)]
  have hcomm1 : ∀ p : Coord L W,
      (gvar L W p : ℝ) • Real.exp (-t / 2) • f p
        = Real.exp (-t / 2) • (gvar L W p : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  have hcomm2 : ∀ p : Coord L W,
      (gueVar L W p : ℝ) • Real.sqrt (1 - Real.exp (-t)) • f p
        = Real.sqrt (1 - Real.exp (-t)) • (gueVar L W p : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl (fun p _ => hcomm1 p), Finset.sum_congr rfl (fun p _ => hcomm2 p),
    ← Finset.smul_sum, ← Finset.smul_sum, smul_smul, smul_smul, hband, hgue] at hIeq
  set V : Idx L W → Idx L W → ℂ := fun a b =>
    if a = b then f (a, a, true) else (1 / 4 : ℝ) • (f (a, b, true) + f (a, b, false))
    with hV
  have hcoef : OUGenerator_aC t * Real.exp (-t / 2) = -(1 / 2 : ℝ) * Real.exp (-t) := by
    unfold OUGenerator_aC
    rw [show -(1 / 2 : ℝ) * Real.exp (-t / 2) * Real.exp (-t / 2)
        = -(1 / 2 : ℝ) * (Real.exp (-t / 2) * Real.exp (-t / 2)) by ring,
      ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring]
  have hcoef2 : OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t)) = (1 / 2 : ℝ) * Real.exp (-t) := by
    unfold OUGenerator_bC
    have hpos : 0 < Real.sqrt (1 - Real.exp (-t)) := Real.sqrt_pos.mpr (OUGenerator_zeta_pos ht)
    field_simp
  have hscalar : ∀ a b : Idx L W,
      (OUGenerator_aC t * Real.exp (-t / 2)) * svar L W a b
        + (OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t))) * (Fintype.card (Idx L W) : ℝ)⁻¹
        = -(1 / 2 : ℝ) * Real.exp (-t) * (centeredVarianceEntry L W a b : ℝ) := by
    intro a b
    rw [hcoef, hcoef2]
    unfold centeredVarianceEntry
    ring
  have hcombine : (OUGenerator_aC t * Real.exp (-t / 2)) •
        (∑ i : Idx L W, ∑ j : Idx L W, svar L W i j • V i j)
      + (OUGenerator_bC t * Real.sqrt (1 - Real.exp (-t))) •
        (∑ i : Idx L W, ∑ j : Idx L W, (Fintype.card (Idx L W) : ℝ)⁻¹ • V i j)
      = (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ i : Idx L W, ∑ j : Idx L W, (centeredVarianceEntry L W i j : ℝ) • V i j := by
    rw [OUGenerator_sum2_combine, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hscalar i j, smul_smul]
  have hfinal : ∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        ∫ z, wirtSecond L W Φ (ouMat L W t z) a b ∂(ouP L W)
      = ∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℝ) • V a b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [OUGenerator_integral_wirtSecond h t a b]
    exact Complex.real_smul.symm
  rw [hfinal, ← hcombine, ← hIeq]
  exact hbase

end Pairs

/-! ## 8. Continuity at `t = 0` and the FTC form -/

section FTC

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

/-- `s ↦ 𝐇_s(z)` is continuous **everywhere**, including at `s = 0`: only its `t`-derivative
(through `√(1 - e^{-s})`) is singular there. -/
private theorem OUGenerator_continuous_ouMat_in_s (z : Ω L W × Ω L W) :
    Continuous fun s : ℝ => ouMat L W s z := by
  have h1 : Continuous fun s : ℝ => Real.exp (-s / 2) := by fun_prop
  have h2 : Continuous fun s : ℝ => Real.sqrt (1 - Real.exp (-s)) := by fun_prop
  exact (h1.smul continuous_const).add (h2.smul continuous_const)

/-- **`s ↦ ∫ Φ (𝐇_s) ∂ouP` is continuous everywhere**, in particular at `s = 0` where it is not
differentiable. -/
private theorem OUGenerator_continuous_integral (h : TestFunH L W Φ) :
    Continuous (fun s : ℝ => ∫ z, Φ (ouMat L W s z) ∂(ouP L W)) := by
  obtain ⟨C₀, hC₀⟩ := h.2.1
  refine continuous_of_dominated
    (fun s => (OUGenerator_continuous_Phi h (OUGenerator_continuous_ouMat s)
      (fun z => ouMat_isHermitian L W s z)).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => hC₀ _ (ouMat_isHermitian L W s z))
    (integrable_const C₀) (Eventually.of_forall fun z => ?_)
  exact OUGenerator_continuous_Phi h (OUGenerator_continuous_ouMat_in_s z)
    (fun s => ouMat_isHermitian L W s z)

/-- A global bound on `wirtSecond` at Hermitian matrices, for a fixed index pair. -/
private theorem OUGenerator_exists_bound_wirtSecond (h : TestFunH L W Φ) (a b : Idx L W) :
    ∃ C : ℝ, ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
      ‖wirtSecond L W Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  rcases eq_or_ne a b with rfl | hab
  · refine ⟨C₂ * ‖RBM.Green.Bmat L W a a true‖ * ‖RBM.Green.Bmat L W a a true‖,
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_left rfl]
    exact OUGenerator_norm_coordD2_le hC₂ hM (a, a, true)
  · refine ⟨(1 / 4 : ℝ) * (C₂ * ‖RBM.Green.Bmat L W a b true‖ * ‖RBM.Green.Bmat L W a b true‖
        + C₂ * ‖RBM.Green.Bmat L W a b false‖ * ‖RBM.Green.Bmat L W a b false‖),
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_right hab]
    calc ‖(1 / 4 : ℝ) • (coordD2 L W Φ M (a, b, true) + coordD2 L W Φ M (a, b, false))‖
        = (1 / 4 : ℝ) * ‖coordD2 L W Φ M (a, b, true) + coordD2 L W Φ M (a, b, false)‖ := by
          rw [norm_smul]; simp
      _ ≤ (1 / 4 : ℝ) * (‖coordD2 L W Φ M (a, b, true)‖ + ‖coordD2 L W Φ M (a, b, false)‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) * (C₂ * ‖RBM.Green.Bmat L W a b true‖ * ‖RBM.Green.Bmat L W a b true‖
            + C₂ * ‖RBM.Green.Bmat L W a b false‖ * ‖RBM.Green.Bmat L W a b false‖) := by
          gcongr
          · exact OUGenerator_norm_coordD2_le hC₂ hM (a, b, true)
          · exact OUGenerator_norm_coordD2_le hC₂ hM (a, b, false)

private theorem OUGenerator_continuous_wirtSecond_comp (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (i j : Idx L W) :
    Continuous fun a => wirtSecond L W Φ (f a) i j := by
  unfold wirtSecond
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact OUGenerator_continuous_coordD2 h hf hherm (j, j, true)
  · simp only [hij, ite_false]
    exact ((OUGenerator_continuous_coordD2 h hf hherm (i, j, true)).add
      (OUGenerator_continuous_coordD2 h hf hherm (i, j, false))).const_smul (1 / 4 : ℝ)

/-- `s ↦ ∫ wirtSecond Φ (𝐇_s) a b ∂ouP` is continuous everywhere. -/
private theorem OUGenerator_continuous_integral_wirtSecond (h : TestFunH L W Φ)
    (a b : Idx L W) :
    Continuous (fun s : ℝ => ∫ z, wirtSecond L W Φ (ouMat L W s z) a b ∂(ouP L W)) := by
  obtain ⟨C, hC⟩ := OUGenerator_exists_bound_wirtSecond h a b
  refine continuous_of_dominated
    (fun s => (OUGenerator_continuous_wirtSecond_comp h (OUGenerator_continuous_ouMat s)
      (fun z => ouMat_isHermitian L W s z) a b).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => hC _ (ouMat_isHermitian L W s z))
    (integrable_const C) (Eventually.of_forall fun z => ?_)
  exact OUGenerator_continuous_wirtSecond_comp h (OUGenerator_continuous_ouMat_in_s z)
    (fun s => ouMat_isHermitian L W s z) a b

/-- The continuity of the right-hand side of the generator identity, for interval
integrability. -/
private theorem OUGenerator_continuous_rhs (h : TestFunH L W Φ) :
    Continuous (fun t : ℝ => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ∫ z, wirtSecond L W Φ (ouMat L W t z) a b ∂(ouP L W)) := by
  have hc : Continuous fun t : ℝ => -(1 / 2 : ℝ) * Real.exp (-t) := by fun_prop
  have hs : Continuous fun t : ℝ => ∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ∫ z, wirtSecond L W Φ (ouMat L W t z) a b ∂(ouP L W) :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_const.mul (OUGenerator_continuous_integral_wirtSecond h a b)
  exact hc.smul hs

end FTC

/-- **The OU generator identity** `d/dt E Φ(𝐇_t) = -½ e^{-t} ∑_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(𝐇_t)`
for `t > 0`. -/
theorem ouGenerator_hasDerivAt_integral (L W : ℕ) [NeZero L] [NeZero W]
    (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (hΦ : TestFunH L W Φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (RBM.Univ.ouMat L W s ω) ∂(RBM.Univ.ouP L W))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx L W, ∑ b : Idx L W,
        (RBM.Univ.centeredVarianceEntry L W a b : ℂ) *
          ∫ ω, RBM.Univ.wirtSecond L W Φ (RBM.Univ.ouMat L W t ω) a b
            ∂(RBM.Univ.ouP L W)) t :=
  OUGenerator_hasDerivAt_integral_pairs hΦ ht

/-- **The FTC form** of the generator identity from `t = 0`. -/
theorem ouGenerator_integral_sub_eq (L W : ℕ) [NeZero L] [NeZero W]
    (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ) (hΦ : TestFunH L W Φ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, Φ (RBM.Univ.ouMat L W T ω) ∂(RBM.Univ.ouP L W)) -
        ∫ ω, Φ (RBM.Univ.ouMat L W 0 ω) ∂(RBM.Univ.ouP L W) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx L W, ∑ b : Idx L W,
        (RBM.Univ.centeredVarianceEntry L W a b : ℂ) *
          ∫ ω, RBM.Univ.wirtSecond L W Φ (RBM.Univ.ouMat L W t ω) a b
            ∂(RBM.Univ.ouP L W) := by
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (RBM.Univ.ouMat L W s ω) ∂(RBM.Univ.ouP L W) with hF
  set g : ℝ → ℂ := fun t => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx L W, ∑ b : Idx L W,
      (RBM.Univ.centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, RBM.Univ.wirtSecond L W Φ (RBM.Univ.ouMat L W t ω) a b
          ∂(RBM.Univ.ouP L W) with hg
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · simp [← hT0]
  have hcont : ContinuousOn F (Set.Icc 0 T) := (OUGenerator_continuous_integral hΦ).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt F (g t) t := fun t ht =>
    OUGenerator_hasDerivAt_integral_pairs hΦ ht.1
  have hint : IntervalIntegrable g MeasureTheory.volume 0 T :=
    (OUGenerator_continuous_rhs hΦ).intervalIntegrable 0 T
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0.le hcont hderiv hint).symm

/-! ## 9. `∏ Im m(z_i)` is a `TestFunH`

Near a Hermitian `x`, each factor is `K ↦ ℓ(Ring.inverse (K - w))` with
`ℓ = Im ∘ (|ι|⁻¹ tr)` real-linear; `Ring.inverse` is smooth on the open set of units,
`D inv(u) = -mulLeftRight u⁻¹ u⁻¹` (`fderiv_inverse`), and on the units
`D inv(y) = mulLeftRight (-y⁻¹) y⁻¹`, whose derivative is bounded by Mathlib's bilinear Leibniz
bound `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`, giving
`‖D^k inv(u)‖ ≤ ‖u⁻¹‖, ‖u⁻¹‖², 2‖u⁻¹‖³` for `k = 0, 1, 2`.  At Hermitian `x` with `Im w > 0`,
`‖(x - w)⁻¹‖ ≤ (Im w)⁻¹` (`RBM.Gauss.norm_green_le`).  The finite product is handled by
Mathlib's `norm_iteratedFDerivWithin_prod_le` on the open set where every factor's shift is a
unit. -/

section StieltjesTestFun

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem OUGenerator_inv_norm_iter_one {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      ‖Ring.inverse u‖ * ‖Ring.inverse u‖ := by
  rw [norm_iteratedFDeriv_one]
  obtain ⟨v, rfl⟩ := hu
  rw [fderiv_inverse, norm_neg, ← Ring.inverse_unit]
  exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _

private theorem OUGenerator_inv_fderiv_eventually {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    fderiv ℝ (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) =ᶠ[𝓝 u]
      fun y => ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) (-Ring.inverse y)
        (Ring.inverse y) := by
  filter_upwards [Units.isOpen.mem_nhds hu] with y hy
  obtain ⟨v, rfl⟩ := hy
  rw [fderiv_inverse, Ring.inverse_unit]
  ext h : 1
  simp

private theorem OUGenerator_inv_norm_iter_two {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 2 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      2 * (‖Ring.inverse u‖ * ‖Ring.inverse u‖ * ‖Ring.inverse u‖) := by
  set s : Set (Matrix ι ι ℂ) := {x | IsUnit x}
  have hs : IsOpen s := Units.isOpen
  have hcd : ContDiffOn ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) s := fun y hy => by
    obtain ⟨v, rfl⟩ := hy
    exact ((contDiffAt_ringInverse ℝ v).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hcd' : ContDiffOn ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) s := hcd.neg
  rw [← norm_iteratedFDeriv_fderiv,
    ((OUGenerator_inv_fderiv_eventually hu).iteratedFDeriv ℝ 1).eq_of_nhds,
    ← iteratedFDerivWithin_of_isOpen 1 hs hu]
  have hB :=
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ)).norm_iteratedFDerivWithin_le_of_bilinear
      hcd' hcd hs.uniqueDiffOn hu (n := 1) le_rfl
  refine hB.trans ?_
  refine le_trans (mul_le_of_le_one_left (by positivity) ?_) ?_
  · exact ContinuousLinearMap.opNorm_mulLeftRight_le ℝ (Matrix ι ι ℂ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, zero_add, Nat.sub_zero]
  rw [iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, norm_neg]
  have hneg : ‖iteratedFDeriv ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) u‖ =
      ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ := by
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, fderiv_fun_neg, norm_neg]
  rw [hneg]
  have h1 := OUGenerator_inv_norm_iter_one hu
  have h0 := norm_nonneg (Ring.inverse u)
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

/-- `K ↦ Im (|ι|⁻¹ tr K)`, the real-linear functional through which `Im m` factors. -/
private noncomputable def OUGenerator_stImCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.imLm.comp (((Fintype.card ι : ℂ)⁻¹ • Matrix.traceLinearMap ι ℂ ℂ).restrictScalars ℝ))

private theorem OUGenerator_stieltjes_im_eq (K : Matrix ι ι ℂ) (w : ℂ) :
    (stieltjesN K w).im
      = OUGenerator_stImCLM ι (Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) := by
  simp [OUGenerator_stImCLM, stieltjesN, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

private theorem OUGenerator_contDiffAt_inv_shift {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) x := by
  obtain ⟨v, hv⟩ := hx
  have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := 2) v
  rw [hv] at h
  exact h.comp x (contDiffAt_id.sub contDiffAt_const)

private theorem OUGenerator_contDiffAt_stieltjes_im {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) x := by
  have : (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) =
      OUGenerator_stImCLM ι ∘ fun K : Matrix ι ι ℂ =>
        Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact OUGenerator_stieltjes_im_eq K w
  rw [this]
  exact (OUGenerator_stImCLM ι).contDiff.contDiffAt.comp x (OUGenerator_contDiffAt_inv_shift hx)

/-- The derivatives of order `≤ 2` of one factor `Im m(w)`, at a Hermitian matrix, in every
real direction. -/
private theorem OUGenerator_norm_iteratedFDeriv_stieltjes_im_le {x : Matrix ι ι ℂ}
    (hx : x.IsHermitian) {w : ℂ} (hw : 0 < w.im) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) x‖ ≤
      ‖OUGenerator_stImCLM ι‖ *
        (w.im⁻¹ + w.im⁻¹ * w.im⁻¹ + 2 * (w.im⁻¹ * w.im⁻¹ * w.im⁻¹)) := by
  have hu : IsUnit (x - w • (1 : Matrix ι ι ℂ)) :=
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hx hw.ne'
  have hg : ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ ≤ w.im⁻¹ := by
    have := RBM.Gauss.norm_green_le hx hw (le_abs_self w.im)
    simpa [RBM.green, Matrix.nonsing_inv_eq_ringInverse] using this
  have h0 : 0 ≤ ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ := norm_nonneg _
  have hr : 0 ≤ w.im⁻¹ := inv_nonneg.mpr hw.le
  have : (fun K : Matrix ι ι ℂ => (stieltjesN K w).im) =
      OUGenerator_stImCLM ι ∘ fun K : Matrix ι ι ℂ =>
        Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact OUGenerator_stieltjes_im_eq K w
  rw [this]
  refine ((OUGenerator_stImCLM ι).norm_iteratedFDeriv_comp_left (N := 2)
    (OUGenerator_contDiffAt_inv_shift hu)
    (by exact_mod_cast hk)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [iteratedFDeriv_comp_sub]
  have hB : ‖iteratedFDeriv ℝ k (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (x - w • (1 : Matrix ι ι ℂ))‖ ≤
      ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        2 * (‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖) := by
    interval_cases k
    · rw [norm_iteratedFDeriv_zero]
      nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
    · have := OUGenerator_inv_norm_iter_one hu
      nlinarith [mul_nonneg (mul_nonneg h0 h0) h0]
    · have := OUGenerator_inv_norm_iter_two hu
      nlinarith [mul_nonneg h0 h0]
  refine hB.trans ?_
  gcongr

/-- **`Φ = ∏ Im m(z_i)` lifted to `ℂ` has bounded derivatives of order `≤ 2` at Hermitian
matrices.** -/
private theorem OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le {m : ℕ} (z : Fin m → ℂ)
    (hz : ∀ i, 0 < (z i).im) {k : ℕ} (hk : k ≤ 2) :
    ∃ C : ℝ, ∀ x : Matrix ι ι ℂ, x.IsHermitian →
      ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) x ∧
      ‖iteratedFDeriv ℝ k
        (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) x‖ ≤ C := by
  set β : Fin m → ℝ := fun i => ‖OUGenerator_stImCLM ι‖ *
    ((z i).im⁻¹ + (z i).im⁻¹ * (z i).im⁻¹ + 2 * ((z i).im⁻¹ * (z i).im⁻¹ * (z i).im⁻¹))
  refine ⟨‖Complex.ofRealCLM‖ * ∑ p ∈ (Finset.univ : Finset (Fin m)).sym k,
    ((p : Multiset (Fin m)).countPerms : ℝ) * ∏ j, β j, fun x hx => ?_⟩
  set s : Set (Matrix ι ι ℂ) := {K | ∀ i, IsUnit (K - z i • (1 : Matrix ι ι ℂ))}
  have hs : IsOpen s := by
    have : s = ⋂ i, (fun K : Matrix ι ι ℂ => K - z i • (1 : Matrix ι ι ℂ)) ⁻¹'
        {y | IsUnit y} := by
      ext K; simp [s]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      Units.isOpen.preimage (continuous_id.sub continuous_const)
  have hxs : x ∈ s := fun i =>
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hx (hz i).ne'
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ContDiffOn ℝ 2 (fun K : Matrix ι ι ℂ => (stieltjesN K (z i)).im) s :=
    fun i _ K hK => (OUGenerator_contDiffAt_stieltjes_im (hK i)).contDiffWithinAt
  have hP : ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ∏ i, (stieltjesN K (z i)).im) x :=
    contDiffAt_prod fun i _ => OUGenerator_contDiffAt_stieltjes_im (hxs i)
  refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp x hP, ?_⟩
  have hcomp : (fun K : Matrix ι ι ℂ => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ fun K : Matrix ι ι ℂ => ∏ i, (stieltjesN K (z i)).im := rfl
  rw [hcomp]
  refine (Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (N := 2) hP
    (by exact_mod_cast hk)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← iteratedFDerivWithin_of_isOpen k hs hxs]
  refine (norm_iteratedFDerivWithin_prod_le hfac hs.uniqueDiffOn hxs
    (by exact_mod_cast hk)).trans ?_
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hcnt : Multiset.count j (p : Multiset (Fin m)) ≤ 2 :=
    ((Multiset.count_le_card _ _).trans_eq p.2).trans hk
  rw [iteratedFDerivWithin_of_isOpen _ hs hxs]
  exact OUGenerator_norm_iteratedFDeriv_stieltjes_im_le hx (hz j) hcnt

end StieltjesTestFun

/-- **`∏ Im m(z_i)` is a `TestFunH`**: a product of imaginary
parts of Stieltjes transforms at spectral parameters in the upper half-plane is `C²`
near every Hermitian matrix with bounded value, first and second Fréchet derivatives there. -/
theorem testFunH_stieltjesImProduct (L W : ℕ) [NeZero L] [NeZero W] (n : ℕ) (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    TestFunH L W (fun K => ((∏ i, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) := by
  obtain ⟨C0, hC0⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx L W) z hz (k := 0)
      (by norm_num)
  obtain ⟨C1, hC1⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx L W) z hz (k := 1)
      (by norm_num)
  obtain ⟨C2, hC2⟩ :=
    OUGenerator_norm_iteratedFDeriv_stieltjesImProduct_le (ι := Idx L W) z hz (k := 2) le_rfl
  refine ⟨fun M hM => (hC0 M hM).1, ⟨C0, fun M hM => ?_⟩, ⟨C1, fun M hM => ?_⟩,
    ⟨C2, fun M hM => ?_⟩⟩
  · have h := (hC0 M hM).2
    rwa [norm_iteratedFDeriv_zero] at h
  · have h := (hC1 M hM).2
    rwa [norm_iteratedFDeriv_one] at h
  · have h := (hC2 M hM).2
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h

end RBM.Univ

end
