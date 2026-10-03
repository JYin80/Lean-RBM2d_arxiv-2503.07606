/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Apriori
import RBM2D.Universality.GreenCorr
import RBM2D.Universality.EigenMeasurable
import RBM2D.Induction.Split
import RBM2D.Gauss.Envelope
import RBM2D.Green.LDE

/-!
# The two arithmetic reductions of the universality argument: `UnivMainRow` and `ClaimRow`

Paper: arXiv:2503.07606, the proof of `Thm: B_Univ`.

* `univMainRow` (`(univ-main)`): from `ClaimAll`, `locSC`, `GreenCorrAll`.
  For `nf ≤ k`, `ClaimAll` gives `Cn nf`, `τ₀(nf)`; `aprioriRow` gives `AprioriImM d E`;
  `GreenCorrAll` at `c' = 𝔠/36` and this `Cn` gives `τ₀'`; `τ₀ := min τ₀' (min_{nf ≤ k} τ₀ nf)`.
  The law transfer `seqP → ouP` at `t = 0` (`seqXmat_map_eq_ouMat_zero`,
  `integral_kPoint_eq_of_map_eq`) turns the `GreenCorr` limit into `UnivMain`.
* `claimRow` (`(417)`, the Claim `417`): from the weighted `EMCTE2`, `Jak`, `Uyw` with
  `Cn' = Cn + C + 1`.
  `Jak` at `s = univ.erase u` bounds the `L₁` term, `Uyw` at `s = (univ.erase u).erase v` the `L₂`
  term (triangle inequality in `b`, `Im m ≥ 0`, integrability of bounded measurable integrands),
  both by `B = 4 N^{τ_U/4} N^{1 - c' + C τ_U}`; the factor `4` (four `(b₁,b₂)` summands) is absorbed
  by the exponent slack `τ_U/2` once `N^{τ_U/2} ≥ 4` (eventually, `size → ∞`).
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints

/-! ### Bounded measurable complex-valued functions -/

section BM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- A bounded measurable function `Ω' → ℂ`. -/
private def UnivMain_BM (f : Ω' → ℂ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ ω, ‖f ω‖ ≤ K

private theorem UnivMain_BM_const (c : ℂ) : UnivMain_BM (fun _ : Ω' => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem UnivMain_BM_add {f g : Ω' → ℂ} (hf : UnivMain_BM f) (hg : UnivMain_BM g) :
    UnivMain_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  exact ⟨hfm.add hgm, Kf + Kg, fun ω => (norm_add_le _ _).trans (add_le_add (hKf ω) (hKg ω))⟩

private theorem UnivMain_BM_mul {f g : Ω' → ℂ} (hf : UnivMain_BM f) (hg : UnivMain_BM g) :
    UnivMain_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Kf, hKf⟩ := hf
  obtain ⟨hgm, Kg, hKg⟩ := hg
  refine ⟨hfm.mul hgm, |Kf| * |Kg|, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hKf ω).trans (le_abs_self _)) ((hKg ω).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private theorem UnivMain_BM_sum {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, UnivMain_BM (f i)) : UnivMain_BM (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UnivMain_BM_const (Ω' := Ω') 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact UnivMain_BM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem UnivMain_BM_prod {ι : Type*} (s : Finset ι) {f : ι → Ω' → ℂ}
    (hf : ∀ i ∈ s, UnivMain_BM (f i)) : UnivMain_BM (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UnivMain_BM_const (Ω' := Ω') 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact UnivMain_BM_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The real-valued norm of a bounded measurable function, as a complex-valued one. -/
private theorem UnivMain_BM_norm {f : Ω' → ℂ} (hf : UnivMain_BM f) :
    UnivMain_BM (fun ω => ((‖f ω‖ : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp hfm.norm, K, fun ω => ?_⟩
  simpa using hK ω

/-- The imaginary part of a bounded measurable function, as a complex-valued one. -/
private theorem UnivMain_BM_im {f : Ω' → ℂ} (hf : UnivMain_BM f) :
    UnivMain_BM (fun ω => (((f ω).im : ℝ) : ℂ)) := by
  obtain ⟨hfm, K, hK⟩ := hf
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hfm), K, fun ω => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans (hK ω)

/-- A real function whose complex lift is bounded measurable is integrable on a finite measure. -/
private theorem UnivMain_integrable_of_BM {f : Ω' → ℝ} (μ : Measure Ω') [IsFiniteMeasure μ]
    (hf : UnivMain_BM (fun ω => ((f ω : ℝ) : ℂ))) : Integrable f μ := by
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

/-! ### Measurability and boundedness of the Green-function entries -/

section GreenBM

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Entries of `A⁻¹` are measurable in `A` (a private copy of `measurable_matrix_inv_apply` of
`Green/RowIndep.lean`). -/
private theorem UnivMain_measurable_matrix_inv_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
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
private theorem UnivMain_norm_green_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x y : ι) :
    ‖green H z x y‖ ≤ (z.im)⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (RBM.Gauss.norm_green_le hH hz (le_of_eq (abs_of_pos hz).symm))

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Entries of `gSel` of a measurable Hermitian-valued `M` are bounded measurable. -/
private theorem UnivMain_BM_gSel {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) (b : Bool) (x y : Idx L W) :
    UnivMain_BM (fun ω => gSel L W (M ω) z b x y) := by
  have hmeas : ∀ p q : Idx L W, Measurable fun ω => green (M ω) z p q := fun p q =>
    UnivMain_measurable_matrix_inv_apply
      (M := fun ω => M ω - z • (1 : Matrix (Idx L W) (Idx L W) ℂ))
      ((continuous_sub_right (z • (1 : Matrix (Idx L W) (Idx L W) ℂ))).measurable.comp hM) p q
  cases b
  · refine ⟨?_, (z.im)⁻¹, fun ω => ?_⟩
    · have h : Measurable fun ω => (starRingEnd ℂ) (green (M ω) z y x) :=
        (Complex.continuous_conj.measurable).comp (hmeas y x)
      simpa [gSel, Matrix.conjTranspose_apply] using h
    · simpa [gSel, Matrix.conjTranspose_apply] using UnivMain_norm_green_entry_le (hH ω) hz y x
  · refine ⟨?_, (z.im)⁻¹, fun ω => ?_⟩
    · simpa [gSel] using hmeas x y
    · simpa [gSel] using UnivMain_norm_green_entry_le (hH ω) hz x y

/-- Entries of a product `gSel(z₁,b₁) * gSel(z₂,b₂)`. -/
private theorem UnivMain_BM_gSel_mul {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (b₁ b₂ : Bool) (x y : Idx L W) :
    UnivMain_BM (fun ω => (gSel L W (M ω) z₁ b₁ * gSel L W (M ω) z₂ b₂) x y) := by
  simp only [Matrix.mul_apply]
  exact UnivMain_BM_sum _ fun c _ =>
    UnivMain_BM_mul (UnivMain_BM_gSel hM hH hz₁ b₁ x c) (UnivMain_BM_gSel hM hH hz₂ b₂ c y)

/-- The normalized trace `m(z) = N⁻¹ tr G(z)` is bounded measurable. -/
private theorem UnivMain_BM_stieltjes {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M)
    (hH : ∀ ω, (M ω).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    UnivMain_BM (fun ω => stieltjesN (M ω) z) := by
  have h : (fun ω => stieltjesN (M ω) z) =
      fun ω => (Fintype.card (Idx L W) : ℂ)⁻¹ * ∑ i, green (M ω) z i i := rfl
  rw [h]
  exact UnivMain_BM_mul (UnivMain_BM_const _)
    (UnivMain_BM_sum _ fun i _ => by simpa [gSel] using UnivMain_BM_gSel hM hH hz true i i)

/-- `Im m(z) ≥ 0` for Hermitian `H` and `Im z > 0`. -/
private theorem UnivMain_im_stieltjesN_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (stieltjesN H z).im := by
  have h := stieltjesN_im_eq_normalized_specWeight H hH z.re z.im hz
  rw [Complex.re_add_im] at h
  rw [h]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  positivity

end GreenBM

/-! ### The `L₁`, `L₂` terms against the weights: `∫ w · L ≤ 4 · (bound of one summand)` -/

section LBound

variable {Ω' : Type*} [MeasurableSpace Ω'] {L W : ℕ} [NeZero L] [NeZero W]

/-- Triangle inequality in `b` for `L_{1,t}`: `L1t ≤ ∑_{b₁ b₂} N⁻¹ ∑_y ‖∑_x …‖`. -/
private theorem UnivMain_L1t_le (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) :
    L1t L W M z ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ *
      ∑ y, ‖∑ x, (gSel L W M z b₁ * gSel L W M z b₁) x x * Scirc L W x y *
        gSel L W M z b₂ y y‖ := by
  unfold L1t
  refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [Finset.sum_comm]
  exact norm_sum_le _ _

/-- Triangle inequality in `b` for `L_{2,t}`: `L2t ≤ ∑_{b₁ b₂} N⁻² ∑_y ‖∑_x …‖`. -/
private theorem UnivMain_L2t_le (M : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ) :
    L2t L W M z₁ z₂ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, (((((W * L) ^ 2 : ℕ) : ℝ))⁻¹) ^ 2 *
      ∑ y, ‖∑ x, (gSel L W M z₁ b₁ * gSel L W M z₁ b₁) x y * Scirc L W x y *
        (gSel L W M z₂ b₂ * gSel L W M z₂ b₂) y x‖ := by
  unfold L2t
  refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_comm]
  exact norm_sum_le _ _

private theorem UnivMain_L1t_nonneg (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) :
    0 ≤ L1t L W M z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem UnivMain_L2t_nonneg (M : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ) :
    0 ≤ L2t L W M z₁ z₂ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The abstract integration step: `R ≤ ∑_{b₁ b₂} c ∑_y F` pointwise, `w ≥ 0`, and each
`∫ w F ≤ b` give `∫ w R ≤ 4 c #ι b`. -/
private theorem UnivMain_integral_mul_le {ι : Type*} [Fintype ι] (μ : Measure Ω')
    [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 ≤ c) (w : Ω' → ℝ) (hw0 : ∀ ω, 0 ≤ w ω)
    (F : Bool → Bool → ι → Ω' → ℝ)
    (hF : ∀ b₁ b₂ y, Integrable (fun ω => w ω * F b₁ b₂ y ω) μ)
    (R : Ω' → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hR : ∀ ω, R ω ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, F b₁ b₂ y ω)
    {b : ℝ} (hb : ∀ b₁ b₂ y, ∫ ω, w ω * F b₁ b₂ y ω ∂μ ≤ b) :
    ∫ ω, w ω * R ω ∂μ ≤ 4 * (c * ((Fintype.card ι : ℝ) * b)) := by
  have hint2 : ∀ b₁ b₂ : Bool, Integrable (fun ω => c * ∑ y, w ω * F b₁ b₂ y ω) μ :=
    fun b₁ b₂ => (integrable_finsetSum _ fun y _ => hF b₁ b₂ y).const_mul c
  have hint : Integrable (fun ω => ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω) μ :=
    integrable_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => hint2 b₁ b₂
  calc ∫ ω, w ω * R ω ∂μ
      ≤ ∫ ω, ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => mul_nonneg (hw0 ω) (hR0 ω)) hint
          (ae_of_all _ fun ω => ?_)
        calc w ω * R ω
            ≤ w ω * ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, F b₁ b₂ y ω :=
              mul_le_mul_of_nonneg_left (hR ω) (hw0 ω)
          _ = ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, w ω * F b₁ b₂ y ω := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b₁ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b₂ _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ y, ∫ ω, w ω * F b₁ b₂ y ω ∂μ := by
        rw [integral_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => hint2 b₁ b₂]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [integral_finsetSum _ fun b₂ _ => hint2 b₁ b₂]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun y _ => hF b₁ b₂ y]
    _ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool, c * ∑ _y : ι, b := by
        refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hb b₁ b₂ y) hc
    _ = 4 * (c * ((Fintype.card ι : ℝ) * b)) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

/-- The integrand `w · ‖F‖` is integrable for a bounded measurable `F`. -/
private theorem UnivMain_integrable_w_mul_norm {ι : Type*} (μ : Measure Ω') [IsFiniteMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) {F : Ω' → ℂ} (hF : UnivMain_BM F) :
    Integrable (fun ω => (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) * ‖F ω‖) μ := by
  refine UnivMain_integrable_of_BM μ ?_
  have h := UnivMain_BM_mul
    (UnivMain_BM_prod s fun j _ => UnivMain_BM_im (UnivMain_BM_stieltjes hM hH (hz j)))
    (UnivMain_BM_norm hF)
  simpa [Complex.ofReal_mul, Complex.ofReal_prod] using h

/-- `∫ w · L1t ≤ 4 b` if each of the four-times-`N` summands of `Jak` is `≤ b`. -/
private theorem UnivMain_integral_L1t_le {ι : Type*} (μ : Measure Ω') [IsProbabilityMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i : ι) {b : ℝ}
    (hJ : ∀ (y : Idx L W) (b₁ b₂ : Bool),
      ∫ ω, (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) *
        ‖∑ x, (gSel L W (M ω) (zs i) b₁ * gSel L W (M ω) (zs i) b₁) x x * Scirc L W x y *
          gSel L W (M ω) (zs i) b₂ y y‖ ∂μ ≤ b) :
    ∫ ω, (∏ j ∈ s, (stieltjesN (M ω) (zs j)).im) * L1t L W (M ω) (zs i) ∂μ ≤ 4 * b := by
  have hcard : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
    simp [Idx, Z2, Fintype.card_prod, ZMod.card, pow_two]
  have hNpos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 0 < (W * L) ^ 2 := pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L))) 2
    exact_mod_cast this
  have key := UnivMain_integral_mul_le (ι := Idx L W) μ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹
    (inv_nonneg.2 hNpos.le) (fun ω => ∏ j ∈ s, (stieltjesN (M ω) (zs j)).im)
    (fun ω => Finset.prod_nonneg fun j _ => UnivMain_im_stieltjesN_nonneg (hH ω) (hz j))
    (fun b₁ b₂ y ω => ‖∑ x, (gSel L W (M ω) (zs i) b₁ * gSel L W (M ω) (zs i) b₁) x x *
      Scirc L W x y * gSel L W (M ω) (zs i) b₂ y y‖)
    (fun b₁ b₂ y => UnivMain_integrable_w_mul_norm μ hM hH zs hz s
      (UnivMain_BM_sum _ fun x _ => UnivMain_BM_mul
        (UnivMain_BM_mul (UnivMain_BM_gSel_mul hM hH (hz i) (hz i) b₁ b₁ x x)
          (UnivMain_BM_const _)) (UnivMain_BM_gSel hM hH (hz i) b₂ y y)))
    (fun ω => L1t L W (M ω) (zs i)) (fun ω => UnivMain_L1t_nonneg _ _)
    (fun ω => UnivMain_L1t_le _ _) (fun b₁ b₂ y => hJ y b₁ b₂)
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  field_simp

/-- `∫ w · L2t ≤ 4 N⁻¹ b` if each summand of `Uyw` is `≤ b`. -/
private theorem UnivMain_integral_L2t_le {ι : Type*} (μ : Measure Ω') [IsProbabilityMeasure μ]
    {M : Ω' → Matrix (Idx L W) (Idx L W) ℂ} (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    (zs : ι → ℂ) (hz : ∀ j, 0 < (zs j).im) (s : Finset ι) (i j : ι) {b : ℝ}
    (hU : ∀ (y : Idx L W) (b₁ b₂ : Bool),
      ∫ ω, (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) *
        ‖∑ x, (gSel L W (M ω) (zs i) b₁ * gSel L W (M ω) (zs i) b₁) x y * Scirc L W x y *
          (gSel L W (M ω) (zs j) b₂ * gSel L W (M ω) (zs j) b₂) y x‖ ∂μ ≤ b) :
    ∫ ω, (∏ k ∈ s, (stieltjesN (M ω) (zs k)).im) * L2t L W (M ω) (zs i) (zs j) ∂μ ≤
      4 * ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹ * b) := by
  have hcard : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
    simp [Idx, Z2, Fintype.card_prod, ZMod.card, pow_two]
  have hNpos : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 0 < (W * L) ^ 2 := pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L))) 2
    exact_mod_cast this
  have key := UnivMain_integral_mul_le (ι := Idx L W) μ ((((W * L) ^ 2 : ℕ) : ℝ)⁻¹ ^ 2)
    (by positivity) (fun ω => ∏ k ∈ s, (stieltjesN (M ω) (zs k)).im)
    (fun ω => Finset.prod_nonneg fun k _ => UnivMain_im_stieltjesN_nonneg (hH ω) (hz k))
    (fun b₁ b₂ y ω => ‖∑ x, (gSel L W (M ω) (zs i) b₁ * gSel L W (M ω) (zs i) b₁) x y *
      Scirc L W x y * (gSel L W (M ω) (zs j) b₂ * gSel L W (M ω) (zs j) b₂) y x‖)
    (fun b₁ b₂ y => UnivMain_integrable_w_mul_norm μ hM hH zs hz s
      (UnivMain_BM_sum _ fun x _ => UnivMain_BM_mul
        (UnivMain_BM_mul
          (UnivMain_BM_gSel_mul hM hH (hz i) (hz i) b₁ b₁ x y) (UnivMain_BM_const _))
        (UnivMain_BM_gSel_mul hM hH (hz j) (hz j) b₂ b₂ y x)))
    (fun ω => L2t L W (M ω) (zs i) (zs j)) (fun ω => UnivMain_L2t_nonneg _ _ _)
    (fun ω => UnivMain_L2t_le _ _ _) (fun b₁ b₂ y => hU y b₁ b₂)
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  field_simp

end LBound

/-! ### `claimRow` -/

/-- The arithmetic core of `claimRow`: `EMCTE2` with `Jak`, `Uyw` (all weighted) give `Claim417`
with `C_n' = C_n + C + 1`, for `size → ∞`.  `Jak` at `s = univ.erase u`, `i = u` bounds the `L₁`
hypothesis of `EMCTE2` by `B = 4 N^{τ_U/4} N^{1 - c' + C τ_U}`; `Uyw` at
`s = (univ.erase u).erase v`, `i = u`, `j = v` bounds the `L₂` hypothesis by the same `B`
(`4 N⁻¹ N^{τ_U/4} N^{2 - c' + C τ_U}`).  Then `EMCTE2` at slack `τ_U/4` gives
`N^{τ_U/4} N^{-1 + Cn τ_U} B = 4 N^{-c' + (Cn + C + 1/2) τ_U} ≤ N^{-c' + (Cn + C + 1) τ_U}`
as soon as `N^{τ_U/2} ≥ 4`. -/
private theorem UnivMain_claim417_of (d : Sizes) (hsize : Tendsto (fun n => d.size n) atTop atTop)
    {E : ℝ} {nf : ℕ} {τU c' Cn C : ℝ} (hτ : 0 < τU)
    (hEM : EMCTE2 d E nf τU Cn) (hJ : Jak d E nf τU C c') (hU : Uyw d E nf τU C c') :
    Claim417 d E nf τU c' (Cn + C + 1) := by
  intro C₀ hC₀
  have h1 := hEM C₀ (τU / 4) hC₀ (by positivity)
  have h2 := hJ C₀ (τU / 4) hC₀ (by positivity)
  have h3 := hU C₀ (τU / 4) hC₀ (by positivity)
  have hN : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  have h4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (τU / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τU / 2)).comp hN).eventually_ge_atTop 4
  filter_upwards [h1, h2, h3, h4] with n e1 j1 u1 f4
  intro z hz t ht0 htT
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < d.size n := pow_pos (Nat.mul_pos (d.W_pos n)
      (lt_of_lt_of_le (by norm_num) (d.three_le_L n))) 2
    rw [hNdef]
    exact_mod_cast this
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (hz i).2.1
  set B : ℝ := 4 * (N ^ (τU / 4) * N ^ (1 - c' + C * τU)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hL1 : ∀ s : ℝ, 0 ≤ s → s ≤ ouTStar d τU n → ∀ u : Fin nf,
      ∫ ω, (∏ j ∈ Finset.univ.erase u,
          (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z j)).im) *
        L1t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z u) ∂(ouP (d.L n) (d.W n)) ≤ B := by
    intro s hs0 hsT u
    exact UnivMain_integral_L1t_le (ouP (d.L n) (d.W n)) (measurable_ouMat (d.L n) (d.W n) s)
      (ouMat_isHermitian (d.L n) (d.W n) s) z hzim (Finset.univ.erase u) u
      (b := N ^ (τU / 4) * N ^ (1 - c' + C * τU))
      (fun y b₁ b₂ => j1 z hz s hs0 hsT (Finset.univ.erase u) u y b₁ b₂)
  have hL2 : ∀ s : ℝ, 0 ≤ s → s ≤ ouTStar d τU n → ∀ u v : Fin nf, u ≠ v →
      ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v,
          (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z k)).im) *
        L2t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z u) (z v)
        ∂(ouP (d.L n) (d.W n)) ≤ B := by
    intro s hs0 hsT u v huv
    have key := UnivMain_integral_L2t_le (ouP (d.L n) (d.W n))
      (measurable_ouMat (d.L n) (d.W n) s) (ouMat_isHermitian (d.L n) (d.W n) s) z hzim
      ((Finset.univ.erase u).erase v) u v
      (b := N ^ (τU / 4) * N ^ (2 - c' + C * τU))
      (fun y b₁ b₂ => u1 z hz s hs0 hsT ((Finset.univ.erase u).erase v) u v huv y b₁ b₂)
    refine key.trans (le_of_eq ?_)
    have h2e : N ^ (2 - c' + C * τU) = N * N ^ (1 - c' + C * τU) := by
      have : (2 - c' + C * τU) = 1 + (1 - c' + C * τU) := by ring
      rw [this, Real.rpow_add hNpos, Real.rpow_one]
    rw [hBdef, h2e]
    change 4 * (N⁻¹ * (N ^ (τU / 4) * (N * N ^ (1 - c' + C * τU)))) = _
    field_simp
  have e := e1 z hz B hB0 hL1 hL2 t ht0 htT
  refine e.trans ?_
  have hX : 0 ≤ N ^ (-c' + (Cn + C + 1 / 2) * τU) := Real.rpow_nonneg hNpos.le _
  have hlhs : N ^ (τU / 4) * N ^ (-1 + Cn * τU) * B =
      4 * N ^ (-c' + (Cn + C + 1 / 2) * τU) := by
    rw [hBdef, show -c' + (Cn + C + 1 / 2) * τU =
      (τU / 4 + (-1 + Cn * τU)) + (τU / 4 + (1 - c' + C * τU)) by ring,
      Real.rpow_add hNpos (τU / 4 + (-1 + Cn * τU)), Real.rpow_add hNpos (τU / 4),
      Real.rpow_add hNpos (τU / 4)]
    ring
  have hrhs : N ^ (-c' + (Cn + C + 1) * τU) =
      N ^ (τU / 2) * N ^ (-c' + (Cn + C + 1 / 2) * τU) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right f4 hX

/-- **`ClaimRow`** (arithmetic): the weighted `(EMCTE2)` with `(jaklsdufowe)`,
`(uywy7723r3rf)` give `(417)` at `c' = 𝔠/36` with `C_n' = C_n + C + 1`. -/
theorem claimRow : ClaimRow := by
  intro h 𝔠 h𝔠 d hd κ hκ E hE nf
  obtain ⟨Cn, C, τ₀, hτ₀, hh⟩ := h 𝔠 h𝔠 d hd κ hκ E hE nf
  refine ⟨Cn + C + 1, τ₀, hτ₀, fun τU hτU hτU0 => ?_⟩
  obtain ⟨hEM, hJ, hU⟩ := hh τU hτU hτU0
  exact UnivMain_claim417_of d hd.1 hτU hEM hJ hU

/-! ### `univMainRow` -/

private theorem UnivMain_measurable_seqXmat (d : Sizes) (n : ℕ) : Measurable (seqXmat d n) :=
  (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    measurable_Xentry (d.L n) (d.W n) i j).comp (measurable_slice d n)

/-- **`UnivMainRow`** — `(univ-main)` from the Claim family `ClaimAll`
(at `c' = 𝔠/36`), the a priori bound (`aprioriRow`, from `locSC`) and `GreenCorrAll`, plus the
law transfer `seqP d → ouP` at `t = 0`.  `τ₀ := min τ₀' (min_{nf ≤ k} τ₀(nf))` depends on
`𝔠, d, κ, E, k` (through `ClaimAll`'s `Cn`, `τ₀(nf)` and `GreenCorr`'s `τ₀'`), not on `τ_U`, `O`. -/
theorem univMainRow : UnivMainRow := by
  intro hClaim hloc hGC 𝔠 h𝔠 d hd k κ hκ E hE
  choose Cn τ0 hτ0 hCl using fun nf : ℕ => hClaim 𝔠 h𝔠 d hd κ hκ E hE nf
  obtain ⟨τ', hτ', hGC'⟩ := hGC d hd.1 E k (𝔠 / 36) (by positivity) Cn
  have hap : AprioriImM d E := aprioriRow hloc 𝔠 h𝔠 d hd κ hκ E hE
  have hne : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩
  have hτm_pos : 0 < (Finset.range (k + 1)).inf' hne τ0 :=
    (Finset.lt_inf'_iff hne).2 fun i _ => hτ0 i
  refine ⟨min τ' ((Finset.range (k + 1)).inf' hne τ0), lt_min hτ' hτm_pos,
    fun τU hτU hτUle O hO hOc => ?_⟩
  have h417 : ∀ nf ≤ k, Claim417 d E nf τU (𝔠 / 36) (Cn nf) := fun nf hnf =>
    hCl nf τU hτU (hτUle.trans ((min_le_right _ _).trans
      (Finset.inf'_le τ0 (Finset.mem_range.2 (Nat.lt_succ_of_le hnf)))))
  have hGCl := hGC' τU hτU (hτUle.trans (min_le_left _ _)) h417 hap O hO hOc
  refine hGCl.congr fun n => ?_
  have hlaw := integral_kPoint_eq_of_map_eq (seqP d) (ouP (d.L n) (d.W n)) (seqXmat d n)
    (ouMat (d.L n) (d.W n) 0) (seqXmat_isHermitian d n) (ouMat_isHermitian (d.L n) (d.W n) 0)
    (UnivMain_measurable_seqXmat d n) (measurable_ouMat (d.L n) (d.W n) 0)
    (seqXmat_map_eq_ouMat_zero d n) k O hO.continuous E
  rw [hlaw]

end RBM.Univ

end
