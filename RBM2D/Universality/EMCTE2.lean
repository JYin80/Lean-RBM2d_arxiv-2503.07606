/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.OUGenerator
import RBM2D.Universality.OUContraction
import RBM2D.Universality.OUHessian
import RBM2D.Endpoints
import RBM2D.Induction.Split

/-!
# The weighted `(EMCTE2)` from the OU generator identity

Paper: arXiv:2503.07606, proof of `Thm: B_Univ`, display `(EMCTE2)` ("argue as in Step 3 of the
proof of Theorem 2.6 in [YY_25]").

* `eq225_interval`: on `[t, T]` with `0 ≤ t ≤ T`, a bound `Bd` on the expected weighted
  kernels `E[∑_i (∏_{j≠i} Im m_j) L1t(z_i) + ∑_{i≠j} (∏_{k∉{i,j}} Im m_k) L2t(z_i,z_j)]` along
  the flow bounds `|E ∏ Im m(H_t) - E ∏ Im m(H_T)| ≤ ½ (T - t) Bd`.
  Proof: the FTC form of the generator identity (`ouGenerator_integral_sub_eq`) at `T` and
  at `t`, subtracted; the pointwise kernel bound
  (`centeredVariance_wirtProduct_kernel_bound`), rewritten with
  (`paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`); `e^{-s} ≤ 1`.
* `emcte2Row`: `EMCTE2Row`, with `Cn = 1`, `τ₀ = 1`: the left side of `EMCTE2` is
  `≤ ½ nf² (T - t) B ≤ ½ nf² N^{-1+τ_U} B ≤ N^ε N^{-1+τ_U} B` once `½ nf² ≤ N^ε` (eventually,
  `N → ∞`).

The time interval is `[t, T]`, so the FTC is applied at `T` and at `t` and the
two interval integrals are combined by an integrability case split (integrability of the
generator integrand on `[t, T]` comes from its measurability as `deriv` of the expected test
function on `(0, ∞)` and from the hypothesis, not from a continuity argument).  The kernels
`L1t`, `L2t` are taken at the Hermitian matrix `ouMat L W t`, and the test functions are
Hermitian-only (`TestFunH`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal
open scoped Matrix.Norms.L2Operator

/-! ## 1. Bounded measurable functions -/

section BM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- A bounded measurable function `Ω' → ℂ`. -/
private def EMCTE2_BM (f : Ω' → ℂ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ ω, ‖f ω‖ ≤ K

private theorem EMCTE2_BM_const (c : ℂ) : EMCTE2_BM (fun _ : Ω' => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem EMCTE2_BM_add {f g : Ω' → ℂ} (hf : EMCTE2_BM f) (hg : EMCTE2_BM g) :
    EMCTE2_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  exact ⟨hfm.add hgm, Kf + Kg, fun ω => (norm_add_le _ _).trans (add_le_add (hKf ω) (hKg ω))⟩

private theorem EMCTE2_BM_mul {f g : Ω' → ℂ} (hf : EMCTE2_BM f) (hg : EMCTE2_BM g) :
    EMCTE2_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  refine ⟨hfm.mul hgm, |Kf| * |Kg|, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hKf ω).trans (le_abs_self _)) ((hKg ω).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private theorem EMCTE2_BM_sum {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, EMCTE2_BM (f i)) : EMCTE2_BM (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EMCTE2_BM_const (Ω' := Ω') 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact EMCTE2_BM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem EMCTE2_BM_prod {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, EMCTE2_BM (f i)) : EMCTE2_BM (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EMCTE2_BM_const (Ω' := Ω') 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact EMCTE2_BM_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The real-valued norm of a bounded measurable function, as a complex-valued one. -/
private theorem EMCTE2_BM_norm {f : Ω' → ℂ} (hf : EMCTE2_BM f) :
    EMCTE2_BM (fun ω => ((‖f ω‖ : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp hfm.norm, K, fun ω => ?_⟩
  simpa using hK ω

/-- The imaginary part of a bounded measurable function, as a complex-valued one. -/
private theorem EMCTE2_BM_im {f : Ω' → ℂ} (hf : EMCTE2_BM f) :
    EMCTE2_BM (fun ω => (((f ω).im : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hfm), K, fun ω => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans (hK ω)

/-- A real function whose complex lift is bounded measurable is integrable on a finite measure. -/
private theorem EMCTE2_integrable_of_BM {f : Ω' → ℝ} (μ : Measure Ω') [IsFiniteMeasure μ]
    (hf : EMCTE2_BM (fun ω => ((f ω : ℝ) : ℂ))) : Integrable f μ := by
  obtain ⟨hfm, K, hK⟩ := hf
  have hm : Measurable f := by
    have h := Complex.measurable_re.comp hfm
    have h2 : (Complex.re ∘ fun ω => ((f ω : ℝ) : ℂ)) = f := by
      funext ω
      simp
    rwa [h2] at h
  refine Integrable.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall fun ω => ?_)
  simpa using hK ω

end BM

/-! ## 2. Measurability and boundedness of the Green-function entries -/

section GreenBM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem EMCTE2_measurable_matrix_inv_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    {M : Ω' → Matrix ν ν ℂ} (hM : Measurable M) (i j : ν) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- `|G_{xy}| ≤ (Im z)⁻¹` for Hermitian `H` and `Im z > 0`. -/
private theorem EMCTE2_norm_green_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x y : ι) :
    ‖green H z x y‖ ≤ (z.im)⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (RBM.Gauss.norm_green_le hH hz (le_of_eq (abs_of_pos hz).symm))

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Entries of `gSel` of a measurable Hermitian-valued `M` are bounded measurable. -/
private theorem EMCTE2_BM_gSel {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : Bool) (x y : Idx L W) :
    EMCTE2_BM (fun ω => gSel L W (M ω) z b x y) := by
  have hmeas : ∀ p q : Idx L W, Measurable fun ω => green (M ω) z p q := fun p q =>
    EMCTE2_measurable_matrix_inv_apply
      (M := fun ω => M ω - z • (1 : Matrix (Idx L W) (Idx L W) ℂ))
      ((continuous_sub_right (z • (1 : Matrix (Idx L W) (Idx L W) ℂ))).measurable.comp hM) p q
  cases b
  · refine ⟨?_, (z.im)⁻¹, fun ω => ?_⟩
    · have h : Measurable fun ω => (starRingEnd ℂ) (green (M ω) z y x) :=
        (Complex.continuous_conj.measurable).comp (hmeas y x)
      simpa [gSel, Matrix.conjTranspose_apply] using h
    · simpa [gSel, Matrix.conjTranspose_apply] using EMCTE2_norm_green_entry_le (hH ω) hz y x
  · refine ⟨?_, (z.im)⁻¹, fun ω => ?_⟩
    · simpa [gSel] using hmeas x y
    · simpa [gSel] using EMCTE2_norm_green_entry_le (hH ω) hz x y

/-- Entries of a product `gSel(z₁,b₁) * gSel(z₂,b₂)`. -/
private theorem EMCTE2_BM_gSel_mul {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (b₁ b₂ : Bool) (x y : Idx L W) :
    EMCTE2_BM (fun ω => (gSel L W (M ω) z₁ b₁ * gSel L W (M ω) z₂ b₂) x y) := by
  simp only [Matrix.mul_apply]
  exact EMCTE2_BM_sum _ fun c _ =>
    EMCTE2_BM_mul (EMCTE2_BM_gSel hM hH hz₁ b₁ x c) (EMCTE2_BM_gSel hM hH hz₂ b₂ c y)

/-- The normalized trace `m(z) = N⁻¹ tr G(z)` is bounded measurable. -/
private theorem EMCTE2_BM_stieltjes {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    EMCTE2_BM (fun ω => stieltjesN (M ω) z) := by
  have h : (fun ω => stieltjesN (M ω) z) =
      fun ω => (Fintype.card (Idx L W) : ℂ)⁻¹ * ∑ i, green (M ω) z i i := rfl
  rw [h]
  exact EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun i _ => by simpa [gSel] using EMCTE2_BM_gSel hM hH hz true i i)

/-- `Im m(z) ≥ 0` for Hermitian `H` and `Im z > 0`. -/
private theorem EMCTE2_im_stieltjesN_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjesN H z).im := by
  have h := stieltjesN_im_eq_normalized_specWeight H hH z.re z.im hz
  rw [Complex.re_add_im] at h
  rw [h]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  positivity

/-- `L1t` as a bounded measurable function (complex lift). -/
private theorem EMCTE2_BM_L1t {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    EMCTE2_BM (fun ω => ((L1t L W (M ω) z : ℝ) : ℂ)) := by
  unfold L1t
  simp only [Complex.ofReal_sum]
  refine EMCTE2_BM_sum _ fun b₁ _ => EMCTE2_BM_sum _ fun b₂ _ => ?_
  exact EMCTE2_BM_norm (EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun a _ => EMCTE2_BM_sum _ fun b _ => EMCTE2_BM_mul
      (EMCTE2_BM_mul (EMCTE2_BM_gSel_mul hM hH hz hz b₁ b₁ a a) (EMCTE2_BM_const _))
      (EMCTE2_BM_gSel hM hH hz b₂ b b)))

/-- `L2t` as a bounded measurable function (complex lift). -/
private theorem EMCTE2_BM_L2t {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    EMCTE2_BM (fun ω => ((L2t L W (M ω) z₁ z₂ : ℝ) : ℂ)) := by
  unfold L2t
  simp only [Complex.ofReal_sum]
  refine EMCTE2_BM_sum _ fun b₁ _ => EMCTE2_BM_sum _ fun b₂ _ => ?_
  exact EMCTE2_BM_norm (EMCTE2_BM_mul (EMCTE2_BM_const _)
    (EMCTE2_BM_sum _ fun a _ => EMCTE2_BM_sum _ fun b _ => EMCTE2_BM_mul
      (EMCTE2_BM_mul (EMCTE2_BM_gSel_mul hM hH hz₁ hz₁ b₁ b₁ a b) (EMCTE2_BM_const _))
      (EMCTE2_BM_gSel_mul hM hH hz₂ hz₂ b₂ b₂ b a)))

end GreenBM

/-! ## 3. Integrability and positivity of the weighted kernel integrands -/

section Terms

variable {Ω' : Type*} [MeasurableSpace Ω'] {L W : ℕ} [NeZero L] [NeZero W]

/-- `(∏_{j∈s} Im m(z_j)) · L1t(z_i)` is integrable along a measurable Hermitian-valued `M`. -/
private theorem EMCTE2_integrable_L1t_term (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {ι : Type*} (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i : ι) :
    Integrable (fun ω => (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) * L1t L W (M ω) (zs i)) μ := by
  refine EMCTE2_integrable_of_BM μ ?_
  have h := EMCTE2_BM_mul
    (EMCTE2_BM_prod s fun j _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz j)))
    (EMCTE2_BM_L1t hM hH (hz i))
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- `(∏_{k∈s} Im m(z_k)) · L2t(z_i, z_j)` is integrable along a measurable Hermitian-valued `M`. -/
private theorem EMCTE2_integrable_L2t_term (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {ι : Type*} (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i j : ι) :
    Integrable (fun ω => (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) *
      L2t L W (M ω) (zs i) (zs j)) μ := by
  refine EMCTE2_integrable_of_BM μ ?_
  have h := EMCTE2_BM_mul
    (EMCTE2_BM_prod s fun k _ => EMCTE2_BM_im (EMCTE2_BM_stieltjes hM hH (hz k)))
    (EMCTE2_BM_L2t hM hH (hz i) (hz j))
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- The weighted kernel sum of `eq225_interval` at a matrix `M`. -/
private def EMCTE2_hsum (L W : ℕ) [NeZero L] [NeZero W] {n : ℕ} (z : Fin n → ℂ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  (∑ i, (∏ j ∈ Finset.univ.erase i, (stieltjesN M (z j)).im) * L1t L W M (z i)) +
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, (stieltjesN M (z k)).im) * L2t L W M (z i) (z j)

private theorem EMCTE2_integrable_hsum (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    Integrable (fun ω => EMCTE2_hsum L W z (M ω)) μ := by
  unfold EMCTE2_hsum
  exact (integrable_finsetSum _ fun i _ => EMCTE2_integrable_L1t_term μ hM hH z hz _ i).add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      EMCTE2_integrable_L2t_term μ hM hH z hz _ i j)

private theorem EMCTE2_hsum_nonneg {M : Matrix (Idx L W) (Idx L W) ℂ} (hH : M.IsHermitian)
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) : 0 ≤ EMCTE2_hsum L W z M := by
  have hL1 : ∀ w : ℂ, 0 ≤ L1t L W M w := fun w =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL2 : ∀ w₁ w₂ : ℂ, 0 ≤ L2t L W M w₁ w₂ := fun w₁ w₂ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hIm : ∀ i, 0 ≤ (stieltjesN M (z i)).im := fun i =>
    EMCTE2_im_stieltjesN_nonneg hH (hz i)
  unfold EMCTE2_hsum
  refine add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg
    (Finset.prod_nonneg fun j _ => hIm j) (hL1 _)) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (Finset.prod_nonneg fun k _ => hIm k) (hL2 _ _))

end Terms

/-! ## 4. Integrability of the `wirtSecond` terms along the flow (with the Hermitian bounds of
`TestFunH`) -/

section Wirt

variable {L W : ℕ} [NeZero L] [NeZero W] {Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ}

private theorem EMCTE2_continuousAt_fderiv2 (h : TestFunH L W Φ)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    ContinuousAt (fderiv ℝ (fderiv ℝ Φ)) M :=
  (((h.1 M hM).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt

private theorem EMCTE2_continuous_comp {α E : Type*} [TopologicalSpace α]
    [TopologicalSpace E] {F : Matrix (Idx L W) (Idx L W) ℂ → E}
    (hF : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ContinuousAt F M)
    {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f) (hherm : ∀ a, (f a).IsHermitian) :
    Continuous fun a => F (f a) :=
  continuous_iff_continuousAt.2 fun a => (hF _ (hherm a)).comp hf.continuousAt

private theorem EMCTE2_continuous_coordD2 (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (p : Coord L W) :
    Continuous fun a => coordD2 L W Φ (f a) p :=
  ((EMCTE2_continuous_comp (fun M hM => EMCTE2_continuousAt_fderiv2 h hM) hf
    hherm).clm_apply continuous_const).clm_apply continuous_const

private theorem EMCTE2_norm_coordD2_le {C : ℝ}
    (hC : ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (p : Coord L W) :
    ‖coordD2 L W Φ M p‖
      ≤ C * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ * ‖RBM.Green.Bmat L W p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat L W p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hC M hM) (norm_nonneg _))) (norm_nonneg _))

/-- A global bound on `wirtSecond` at Hermitian matrices, for a fixed index pair. -/
private theorem EMCTE2_exists_bound_wirtSecond (h : TestFunH L W Φ) (a b : Idx L W) :
    ∃ C : ℝ, ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
      ‖wirtSecond L W Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := h.2.2.2
  rcases eq_or_ne a b with rfl | hab
  · refine ⟨C₂ * ‖RBM.Green.Bmat L W a a true‖ * ‖RBM.Green.Bmat L W a a true‖,
      fun M hM => ?_⟩
    unfold wirtSecond
    rw [ite_eq_left rfl]
    exact EMCTE2_norm_coordD2_le hC₂ hM (a, a, true)
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
          · exact EMCTE2_norm_coordD2_le hC₂ hM (a, b, true)
          · exact EMCTE2_norm_coordD2_le hC₂ hM (a, b, false)

private theorem EMCTE2_continuous_wirtSecond_comp (h : TestFunH L W Φ)
    {α : Type*} [TopologicalSpace α] {f : α → Matrix (Idx L W) (Idx L W) ℂ} (hf : Continuous f)
    (hherm : ∀ a, (f a).IsHermitian) (i j : Idx L W) :
    Continuous fun a => wirtSecond L W Φ (f a) i j := by
  unfold wirtSecond
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact EMCTE2_continuous_coordD2 h hf hherm (j, j, true)
  · simp only [hij, ite_false]
    exact ((EMCTE2_continuous_coordD2 h hf hherm (i, j, true)).add
      (EMCTE2_continuous_coordD2 h hf hherm (i, j, false))).const_smul (1 / 4 : ℝ)

private theorem EMCTE2_continuous_ouMat (s : ℝ) :
    Continuous fun z : Ω L W × Ω L W => ouMat L W s z :=
  (((continuous_Xmat L W).comp continuous_fst).const_smul (Real.exp (-s / 2))).add
    (((continuous_Xmat L W).comp continuous_snd).const_smul (Real.sqrt (1 - Real.exp (-s))))

/-- Each `wirtSecond` term along the flow is integrable. -/
private theorem EMCTE2_integrable_wirtSecond (h : TestFunH L W Φ) (s : ℝ) (a b : Idx L W) :
    Integrable (fun ω => wirtSecond L W Φ (ouMat L W s ω) a b) (ouP L W) := by
  obtain ⟨C, hC⟩ := EMCTE2_exists_bound_wirtSecond h a b
  exact Integrable.of_bound
    (EMCTE2_continuous_wirtSecond_comp h (EMCTE2_continuous_ouMat s)
      (fun ω => ouMat_isHermitian L W s ω) a b).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (ouMat_isHermitian L W s ω))

/-- `∑ a b, S°_{ab} ∫ wirtSecond a b = ∫ ∑ a b, S°_{ab} wirtSecond a b`. -/
private theorem EMCTE2_sum_integral_swap (h : TestFunH L W Φ) (s : ℝ) :
    ∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) =
      ∫ ω, ∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) := by
  have hb : ∀ a : Idx L W, (∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W)) =
      ∫ ω, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) := by
    intro a
    have hterm : ∀ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
          ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) =
        ∫ ω, (centeredVarianceEntry L W a b : ℂ) *
          wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) := by
      intro b
      rw [MeasureTheory.integral_const_mul]
    rw [Finset.sum_congr rfl fun b _ => hterm b,
      MeasureTheory.integral_finsetSum Finset.univ
        (fun b _ => (EMCTE2_integrable_wirtSecond h s a b).const_mul _)]
  rw [Finset.sum_congr rfl fun a _ => hb a,
    MeasureTheory.integral_finsetSum Finset.univ
      (fun a _ => integrable_finsetSum Finset.univ
        (fun b _ => (EMCTE2_integrable_wirtSecond h s a b).const_mul _))]

end Wirt

/-! ## 5. `eq225_interval` -/

/-- **`eq225_interval`.**  A bound
`Bd` on the expected weighted kernels `L1t`, `L2t` along the OU flow on `(t, T)` bounds the change
of `E ∏ Im m` between the times `t` and `T` by `½ (T - t) Bd` (display `(EMCTE2)`; hypotheses on
the spectral parameters: `0 < Im z_i` only). -/
theorem eq225_interval (L W : ℕ) [NeZero L] [NeZero W] (n : ℕ) (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) (t T Bd : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hB : ∀ s ∈ Set.Ioo t T,
      ∫ ω, ((∑ i, (∏ j ∈ Finset.univ.erase i,
              (RBM.Univ.stieltjesN (RBM.Univ.ouMat L W s ω) (z j)).im) *
              RBM.Univ.L1t L W (RBM.Univ.ouMat L W s ω) (z i)) +
            ∑ i, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (RBM.Univ.stieltjesN (RBM.Univ.ouMat L W s ω) (z k)).im) *
              RBM.Univ.L2t L W (RBM.Univ.ouMat L W s ω) (z i) (z j))
        ∂(RBM.Univ.ouP L W) ≤ Bd) :
    |(∫ ω, ∏ i, (RBM.Univ.stieltjesN (RBM.Univ.ouMat L W t ω) (z i)).im ∂(RBM.Univ.ouP L W)) -
      ∫ ω, ∏ i, (RBM.Univ.stieltjesN (RBM.Univ.ouMat L W T ω) (z i)).im ∂(RBM.Univ.ouP L W)| ≤
      (1 / 2) * (T - t) * Bd := by
  classical
  set Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ :=
    fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ) with hΦdef
  have hΦ : TestFunH L W Φ := testFunH_stieltjesImProduct L W n z hz
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (ouMat L W s ω) ∂(ouP L W) with hFdef
  set g : ℝ → ℂ := fun s => (-(1 / 2 : ℝ) * Real.exp (-s)) • ∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W) with hgdef
  have hcast : ∀ s : ℝ, F s =
      ((∫ ω, ∏ i, (stieltjesN (ouMat L W s ω) (z i)).im ∂(ouP L W) : ℝ) : ℂ) := by
    intro s
    simp only [hFdef, hΦdef]
    exact integral_ofReal
  have hFd : ∀ s : ℝ, 0 < s → HasDerivAt F (g s) s := fun s hs =>
    ouGenerator_hasDerivAt_integral L W Φ hΦ s hs
  have hFT : F T - F 0 = ∫ s in (0 : ℝ)..T, g s :=
    ouGenerator_integral_sub_eq L W Φ hΦ T (ht.trans htT)
  have hFt : F t - F 0 = ∫ s in (0 : ℝ)..t, g s :=
    ouGenerator_integral_sub_eq L W Φ hΦ t ht
  -- the hypothesis forces `0 ≤ Bd` as soon as `(t, T)` is nonempty
  have hBd : t < T → 0 ≤ Bd := by
    intro htT'
    have hmid : (t + T) / 2 ∈ Set.Ioo t T := ⟨by linarith, by linarith⟩
    refine le_trans ?_ (hB _ hmid)
    exact integral_nonneg fun ω => EMCTE2_hsum_nonneg (ouMat_isHermitian L W _ ω) z hz
  -- the norm of the weighted sum of expected Hessians is at most `Bd`
  have hS : ∀ s ∈ Set.Ioo t T,
      ‖∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W)‖ ≤ Bd := by
    intro s hs
    rw [EMCTE2_sum_integral_swap hΦ s]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound : ∀ᵐ ω ∂(ouP L W),
        ‖∑ a : Idx L W, ∑ b : Idx L W, (centeredVarianceEntry L W a b : ℂ) *
          wirtSecond L W Φ (ouMat L W s ω) a b‖ ≤ EMCTE2_hsum L W z (ouMat L W s ω) := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have hH := ouMat_isHermitian L W s ω
      have hpt := centeredVariance_wirtProduct_kernel_bound L W (Finset.univ : Finset (Fin n))
        (ouMat L W s ω) hH z (fun i _ => hz i)
      simp only [paperL1Kernel_eq_L1t L W hH, paperL2Kernel_eq_L2t L W hH] at hpt
      exact hpt
    exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
      (EMCTE2_integrable_hsum (ouP L W) (measurable_ouMat L W s) (ouMat_isHermitian L W s) z hz)
      hbound).trans (hB s hs)
  -- the generator integrand is bounded by `½ Bd` on `(t, T)` (`e^{-s} ≤ 1` for `s ≥ 0`)
  have hg : ∀ s ∈ Set.Ioo t T, ‖g s‖ ≤ (1 / 2) * Bd := by
    intro s hs
    have hS' := hS s hs
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    have hexppos : 0 < Real.exp (-s) := Real.exp_pos _
    have habs : ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ = (1 / 2 : ℝ) * Real.exp (-s) := by
      rw [Real.norm_eq_abs, abs_of_neg (by nlinarith [hexppos])]
      ring
    have hSnn := norm_nonneg (∑ a : Idx L W, ∑ b : Idx L W,
      (centeredVarianceEntry L W a b : ℂ) *
        ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W))
    calc ‖g s‖ = ‖(-(1 / 2 : ℝ) * Real.exp (-s))‖ * ‖∑ a : Idx L W, ∑ b : Idx L W,
          (centeredVarianceEntry L W a b : ℂ) *
            ∫ ω, wirtSecond L W Φ (ouMat L W s ω) a b ∂(ouP L W)‖ := by
          rw [hgdef]; exact norm_smul _ _
      _ ≤ (1 / 2 : ℝ) * Bd := by
          rw [habs]
          nlinarith [mul_le_mul_of_nonneg_right hexp hSnn, hS']
  -- `g` is interval integrable on `[t, T]`: it is `deriv F` (measurable) on `(0, ∞)` and bounded
  have hIntTT : IntervalIntegrable g MeasureTheory.volume t T := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le htT]
    have hm : AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioc t T)) := by
      have hm' : AEStronglyMeasurable (deriv F)
          (MeasureTheory.volume.restrict (Set.Ioc t T)) :=
        (measurable_deriv F).aestronglyMeasurable
      refine hm'.congr ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun s hs => (hFd s (lt_of_le_of_lt ht hs.1)).deriv)
    refine Integrable.of_bound (C := (1 / 2) * Bd) hm ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
    exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
  have hnn : 0 ≤ (1 / 2 * Bd) * |T - t| := by
    rcases eq_or_lt_of_le htT with h | h
    · simp [h]
    · exact mul_nonneg (by have := hBd h; positivity) (abs_nonneg _)
  have hmain : ‖F T - F t‖ ≤ (1 / 2 * Bd) * |T - t| := by
    by_cases h0t : IntervalIntegrable g MeasureTheory.volume 0 t
    · have hsum := intervalIntegral.integral_add_adjacent_intervals h0t hIntTT
      have hdiff : F T - F t = ∫ s in t..T, g s := by
        linear_combination hFT - hFt - hsum
      rw [hdiff]
      refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
      filter_upwards [MeasureTheory.volume.ae_ne T] with s hsne hs
      rw [Set.uIoc_of_le htT] at hs
      exact hg s ⟨hs.1, hs.2.lt_of_ne hsne⟩
    · have hnot : ¬ IntervalIntegrable g MeasureTheory.volume 0 T := fun h =>
        h0t (h.mono_set (by
          rw [Set.uIcc_of_le ht, Set.uIcc_of_le (ht.trans htT)]
          exact Set.Icc_subset_Icc_right htT))
      rw [intervalIntegral.integral_undef hnot] at hFT
      rw [intervalIntegral.integral_undef h0t] at hFt
      have : F T - F t = 0 := by linear_combination hFT - hFt
      rw [this, norm_zero]
      exact hnn
  calc _ = |(∫ ω, ∏ i, (stieltjesN (ouMat L W T ω) (z i)).im ∂(ouP L W)) -
        ∫ ω, ∏ i, (stieltjesN (ouMat L W t ω) (z i)).im ∂(ouP L W)| := abs_sub_comm _ _
    _ = ‖F T - F t‖ := by
        rw [hcast T, hcast t, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / 2 * Bd) * |T - t| := hmain
    _ = (1 / 2) * (T - t) * Bd := by rw [abs_of_nonneg (sub_nonneg.2 htT)]; ring

/-! ## 6. `emcte2Row` -/

/-- **`emcte2Row`** (`EMCTE2Row`, the weighted `(EMCTE2)`).
`Cn = 1`, `τ₀ = 1`: for `0 ≤ t ≤ t*`, `|E ∏ Im m_t - E ∏ Im m_{t*}| ≤ ½ (t* - t) nf² B
≤ ½ nf² N^{-1+τ_U} B ≤ N^ε N^{-1+τ_U} B` once `½ nf² ≤ N^ε` (eventually in `n`, `N → ∞`).
No `𝐇_t` claim, no external hypothesis. -/
theorem emcte2Row : EMCTE2Row := by
  intro 𝔠 h𝔠 d hd κ hκ E hE nf
  rcases Nat.eq_zero_or_pos nf with rfl | hpos
  · exact ⟨1, 1, one_pos, fun τU _ _ => PinsCheck.emcte2_zero d E τU 1⟩
  refine ⟨1, 1, one_pos, fun τU hτU hτU1 => ?_⟩
  intro C₀ ε hC₀ hε
  have hN : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd.1
  have hNε : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hN
  filter_upwards [hNε.eventually_ge_atTop ((1 / 2) * (nf : ℝ) ^ 2)] with n hn
  intro z hz B hB0 hB1 hB2 t ht htT
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
    have : 0 < d.size n := by
      simp only [Sizes.size]
      have := d.three_le_L n
      have := d.W_pos n
      positivity
    exact_mod_cast this
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hz i).2.1
  have hT0 : 0 ≤ ouTStar d τU n := Real.rpow_nonneg hNpos.le _
  have hnf : 0 ≤ (nf : ℝ) ^ 2 * B := by positivity
  have key := eq225_interval (d.L n) (d.W n) nf z hzim t (ouTStar d τU n) ((nf : ℝ) ^ 2 * B)
    ht htT (fun s hs => by
      have hs0 : 0 ≤ s := ht.trans hs.1.le
      have hsT : s ≤ ouTStar d τU n := hs.2.le
      have hH := ouMat_isHermitian (d.L n) (d.W n) s
      have hM := measurable_ouMat (d.L n) (d.W n) s
      have iL1 := fun i => EMCTE2_integrable_L1t_term (ouP (d.L n) (d.W n)) hM hH z hzim
        (Finset.univ.erase i) i
      have iL2 := fun i j => EMCTE2_integrable_L2t_term (ouP (d.L n) (d.W n)) hM hH z hzim
        ((Finset.univ.erase i).erase j) i j
      rw [integral_add (integrable_finsetSum _ fun i _ => iL1 i)
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j),
        integral_finsetSum _ fun i _ => iL1 i,
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iL2 i j]
      have e2 : ∀ i, ∫ ω, ∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j,
            (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z k)).im) *
            L2t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z i) (z j) ∂(ouP (d.L n) (d.W n)) =
          ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
            (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z k)).im) *
            L2t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z i) (z j)
              ∂(ouP (d.L n) (d.W n)) := fun i =>
        integral_finsetSum _ fun j _ => iL2 i j
      simp only [e2]
      have h1 : ∑ i : Fin nf, ∫ ω, (∏ j ∈ Finset.univ.erase i,
          (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z j)).im) *
          L1t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z i) ∂(ouP (d.L n) (d.W n)) ≤
          ∑ _i : Fin nf, B := Finset.sum_le_sum fun i _ => hB1 s hs0 hsT i
      have h2 : ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i, ∫ ω, (∏ k ∈ (Finset.univ.erase i).erase j,
          (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z k)).im) *
          L2t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z i) (z j)
            ∂(ouP (d.L n) (d.W n)) ≤ ∑ _i : Fin nf, ∑ _j ∈ Finset.univ.erase _i, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
          hB2 s hs0 hsT i j (Finset.ne_of_mem_erase hj).symm
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.card_erase_of_mem (Finset.mem_univ _), nsmul_eq_mul]
      rw [Nat.cast_sub hpos]
      push_cast
      ring)
  refine key.trans ?_
  have hNeq : ((d.size n : ℕ) : ℝ) ^ (-1 + 1 * τU) = ouTStar d τU n := by
    rw [one_mul]; rfl
  rw [hNeq]
  have hq : (1 / 2 : ℝ) * (ouTStar d τU n - t) * ((nf : ℝ) ^ 2 * B) ≤
      (1 / 2 : ℝ) * ouTStar d τU n * ((nf : ℝ) ^ 2 * B) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self (ouTStar d τU n) ht) (by norm_num : (0 : ℝ) ≤ 1 / 2))
      hnf
    exact this
  refine hq.trans ?_
  have hTB : 0 ≤ ouTStar d τU n * B := mul_nonneg hT0 hB0
  have := mul_le_mul_of_nonneg_right hn hTB
  nlinarith [this]

end RBM.Univ

end
