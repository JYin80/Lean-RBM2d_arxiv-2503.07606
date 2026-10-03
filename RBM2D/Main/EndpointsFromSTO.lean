/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Main.P7FromSTO
import RBM2D.Main.ZRescale
import RBM2D.Main.DecolFromLocal
import RBM2D.Main.QUEFromQDiff

/-!
# Endpoint conversions from the stopped-evolution estimate

`STOAll → locSC ∧ QDiff` and `STOAll → decol ∧ QUE` from the loop estimates `P7Out`, `P7ExpOut`
(`P7FromSTO`) and the six deterministic transfer statements (`ZRescale`): sections, transfer,
endpoint conversion; concrete instances at `witnessSizes`.  Namespace `RBM.Endpoints`.  Paper:
arXiv:2503.07606, Theorems `MR:locSC` and `MR:QDiff`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## Generic lemmas -/

section Generic

/-- Sections ⇒ eventually-for-all: if for every sequence `s n ∈ Z n` the property `Q n (s n)`
holds eventually, then `Q n z` holds eventually for all `z : Z n` (diagonal argument). -/
theorem EndpointsFromSTO_eventually_forall_of_sections {Z : ℕ → Type*} (hne : ∀ n, Nonempty (Z n))
    {Q : ∀ n, Z n → Prop} (h : ∀ s : ∀ n, Z n, ∀ᶠ n in atTop, Q n (s n)) :
    ∀ᶠ n in atTop, ∀ z : Z n, Q n z := by
  classical
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  let s : ∀ n, Z n := fun n => if hb : ∃ z, ¬ Q n z then hb.choose else (hne n).some
  have hfreq : ∃ᶠ n in atTop, ¬ Q n (s n) := by
    refine hnot.mono fun n hn => ?_
    have hb : ∃ z, ¬ Q n z := by
      by_contra hb
      push Not at hb
      exact hn hb
    simp only [s, hb, dite_true]
    exact hb.choose_spec
  obtain ⟨n, hn, hQ⟩ := (hfreq.and_eventually (h s)).exists
  exact hn hQ

/-- Monotonicity of `StochDomAt`: a smaller left side and a control that is a constant multiple
of a larger one. -/
theorem EndpointsFromSTO_stochDomAt_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U : ℕ → Type*} {ξ ζ ξ' ζ' : ∀ l, U l → Ω → ℝ} {C : ℝ}
    (hξ : ∀ l u ω, ξ' l u ω ≤ ξ l u ω) (hζ0 : ∀ l u ω, 0 ≤ ζ' l u ω)
    (hζ : ∀ l u ω, ζ l u ω ≤ C * ζ' l u ω)
    (h : StochDomAt P size ξ ζ) : StochDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hsz : Tendsto (fun l => ((size l : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  filter_upwards [h (τ / 2) hτ2 D hD, hsz.eventually_gt_atTop 0,
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop C] with l hl hpos hC
  refine le_trans (measure_mono ?_) hl
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hhalf : (size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2) = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_add hpos]; ring_nf
  have hr0 : (0 : ℝ) ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg hpos.le _
  have hCz : C * ζ' l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ' l u ω :=
    mul_le_mul_of_nonneg_right hC (hζ0 l u ω)
  calc (size l : ℝ) ^ (τ / 2) * ζ l u ω
      ≤ (size l : ℝ) ^ (τ / 2) * (C * ζ' l u ω) :=
        mul_le_mul_of_nonneg_left (hζ l u ω) hr0
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ' l u ω) :=
        mul_le_mul_of_nonneg_left hCz hr0
    _ = (size l : ℝ) ^ τ * ζ' l u ω := by rw [← mul_assoc, hhalf]
    _ < ξ' l u ω := hu
    _ ≤ ξ l u ω := hξ l u ω

/-- The endpoint conversion: a per-time domination over `Z × V` (`V` finite of polynomial size)
with control `μ(z)` gives, for every `z`, the union-inside bound with the threshold
`W^τ μ(z)` (`W ≥ N^𝔠`); the `z`-quantifier stays outside `P` (as in `locSC`, `QDiff`). -/
theorem EndpointsFromSTO_endpoint_of_perTime {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size W : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hW : ∀ᶠ n in atTop, (size n : ℝ) ^ 𝔠 ≤ (W n : ℝ))
    {Z V : ℕ → Type*} [∀ n, Fintype (V n)] {C : ℝ}
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ C)
    {ξ : ∀ n, Z n × V n → Ω → ℝ} {μ : ∀ n, Z n → ℝ} (hμ : ∀ n z, 0 ≤ μ n z)
    (h : PerTimeDomAt P size ξ (fun n p _ => μ n p.1))
    {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ∀ z : Z n,
      P {ω | ¬ ∀ v : V n, ξ n (z, v) ω ≤ (W n : ℝ) ^ τ * μ n z} ≤
        ENNReal.ofReal ((size n : ℝ) ^ (-D)) := by
  have hsz : Tendsto (fun l => ((size l : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  filter_upwards [h (𝔠 * τ) (mul_pos h𝔠 hτ) (D + C) (by linarith), hW, hcard,
    hsz.eventually_ge_atTop 1] with n hn hWn hcn h1
  intro z
  have hp : (0 : ℝ) ≤ (size n : ℝ) ^ (-(D + C)) := Real.rpow_nonneg (by linarith) _
  have hsub : {ω | ¬ ∀ v : V n, ξ n (z, v) ω ≤ (W n : ℝ) ^ τ * μ n z} ⊆
      ⋃ v : V n, {ω | (size n : ℝ) ^ (𝔠 * τ) * μ n z < ξ n (z, v) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨v, hv⟩ := hω
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    have : (size n : ℝ) ^ (𝔠 * τ) ≤ (W n : ℝ) ^ τ := by
      rw [Real.rpow_mul (by linarith)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hWn hτ.le
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right this (hμ n z)) hv
  calc P {ω | ¬ ∀ v : V n, ξ n (z, v) ω ≤ (W n : ℝ) ^ τ * μ n z}
      ≤ P (⋃ v : V n, {ω | (size n : ℝ) ^ (𝔠 * τ) * μ n z < ξ n (z, v) ω}) := measure_mono hsub
    _ ≤ ∑ v : V n, P {ω | (size n : ℝ) ^ (𝔠 * τ) * μ n z < ξ n (z, v) ω} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _v : V n, ENNReal.ofReal ((size n : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun v _ => hn (z, v)
    _ = ENNReal.ofReal (Fintype.card (V n) * (size n : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size n : ℝ) ^ C * (size n : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcn hp)
    _ = ENNReal.ofReal ((size n : ℝ) ^ (-D)) := by
        rw [rpow_mul_rpow_neg_add (Nat.one_le_cast.1 h1)]

end Generic

/-! ## Assembly: sections, transfer, endpoint conversion -/

section Skeleton

theorem EndpointsFromSTO_Meta_pos (L W : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W) {z : ℂ} (hz : 0 < z.im) :
    0 < Meta L W z := by
  unfold Meta ellz
  have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h1 : 0 < min (z.im ^ (-(1 / 2 : ℝ))) (L : ℝ) :=
    lt_min (Real.rpow_pos_of_pos hz _) hL'
  have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  positivity

theorem EndpointsFromSTO_one_le_L (d : Sizes) (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

theorem EndpointsFromSTO_one_le_W (d : Sizes) (n : ℕ) : 1 ≤ d.W n := d.W_pos n

theorem EndpointsFromSTO_locDomain_im_pos (d : Sizes) (n : ℕ) {κ τ : ℝ} {z : ℂ}
    (h : locDomain (d.size n) κ τ z) : 0 < z.im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (P7FromSTO_size_pos d n) _) h.2.1

theorem EndpointsFromSTO_zdom_nonempty (d : Sizes) {κ τ : ℝ} (hκ : κ ≤ 2) (hτ : τ ≤ 1) (n : ℕ) :
    Nonempty (ZDom d κ τ n) := by
  refine ⟨⟨Complex.I, ?_, ?_, by simp⟩⟩
  · simp only [Complex.I_re, abs_zero]; linarith
  · simp only [Complex.I_im]
    have h1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
      have := P7FromSTO_size_pos d n
      have h2 : 0 < d.size n := by exact_mod_cast this
      exact_mod_cast h2
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

/-- Unit-section extraction from a per-time domination over `Unit × V`. -/
theorem EndpointsFromSTO_unit_section {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {V : ℕ → Type*} (hV : ∀ n, Nonempty (V n)) {ξ ζ : ∀ n, Unit × V n → Ω → ℝ}
    (h : PerTimeDomAt P size ξ ζ) (v : ∀ n, V n) :
    StochDomAt P size (fun n (_ : Unit) ω => ξ n ((), v n) ω)
      (fun n (_ : Unit) ω => ζ n ((), v n) ω) :=
  (perTimeDomAt_iff_forall_section P size (fun n => ⟨((), (hV n).some)⟩) ξ ζ).1 h
    (fun n => ((), v n))

/-- The hypotheses of `P7Out`/`P7ExpOut` along a section `z` of the spectral domain, at the range
exponent `τ/2`: bulk energies `lemE z_n`, times `lemT z_n ∈ (0,1)`, `N^{-1+τ/2} ≤ 1 - lemT z_n`
eventually (`ZRange`: `1 - u ≥ Im z / 4`, and `N^{τ/2} ≥ 4` eventually). -/
theorem EndpointsFromSTO_section_data (hR : ZRange) {𝔠 : ℝ} {d : Sizes} (hAdm : Admissible 𝔠 d) {κ τ : ℝ}
    (hκ : 0 < κ) (hτ : 0 < τ) (z : ∀ n, ZDom d κ τ n) :
    (∀ n, |lemE (z n).1| ≤ 2 - κ) ∧ (∀ n, 0 ≤ lemT (z n).1) ∧
      ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ / 2) ≤ 1 - lemT (z n).1 := by
  have hz : ∀ n, 0 < (z n).1.im := fun n => EndpointsFromSTO_locDomain_im_pos d n (z n).2
  have hrange := fun n => hR κ hκ (z n).1 (hz n) (z n).2.2.2 (z n).2.1
  refine ⟨fun n => (hrange n).1, fun n => (hrange n).2.1.le, ?_⟩
  filter_upwards [hAdm.1.eventually (eventually_le_rpow 4 (half_pos hτ))] with n h4
  have hN := P7FromSTO_size_pos d n
  have hsplit : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) =
      ((d.size n : ℕ) : ℝ) ^ (τ / 2) * ((d.size n : ℕ) : ℝ) ^ (-1 + τ / 2) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have hp : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ / 2) := Real.rpow_nonneg hN.le _
  have h1 := (z n).2.2.1
  have h2 := (hrange n).2.2.2
  nlinarith

/-- The `P7Out` input along a section of the spectral domain. -/
theorem EndpointsFromSTO_section_mlConcl (hR : ZRange) (hP7 : Univ.P7Out) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {d : Sizes}
    (hAdm : Admissible 𝔠 d) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (z : ∀ n, ZDom d κ τ n) :
    Ind.MLConcl d (fun n => lemE (z n).1) (fun n => lemT (z n).1) := by
  obtain ⟨hE, ht0, hRc⟩ := EndpointsFromSTO_section_data hR hAdm hκ hτ z
  exact hP7 𝔠 h𝔠 d hAdm κ hκ _ hE (τ / 2) (half_pos hτ) _ ht0 hRc

/-- The `P7ExpOut` input along a section of the spectral domain. -/
theorem EndpointsFromSTO_section_mlExp (hR : ZRange) (hP7 : Univ.P7ExpOut) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    {d : Sizes} (hAdm : Admissible 𝔠 d) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    (z : ∀ n, ZDom d κ τ n) :
    Evol.MLExpConcl d (fun n => lemE (z n).1) (fun n => lemT (z n).1) := by
  obtain ⟨hE, ht0, hRc⟩ := EndpointsFromSTO_section_data hR hAdm hκ hτ z
  exact hP7 𝔠 h𝔠 d hAdm κ hκ _ hE (τ / 2) (half_pos hτ) _ ht0 hRc

theorem EndpointsFromSTO_Kcal_one (L W : ℕ) [NeZero L] (E u : ℝ) (a : Z2 L) :
    KLoop.Kcal L W E u (loopOf ![true] ![a]) = spectralM E := by
  simp [KLoop.Kcal, KLoop.Kgen, loopOf, LoopIdx.length, KLoop.mSig]

theorem EndpointsFromSTO_ctrl_nonneg (d : Sizes) (n : ℕ) {κ τ : ℝ} (z : ZDom d κ τ n) :
    0 ≤ (Meta (d.L n) (d.W n) z.1)⁻¹ :=
  inv_nonneg.2 (EndpointsFromSTO_Meta_pos _ _ (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n)
    (EndpointsFromSTO_locDomain_im_pos d n z.2)).le

theorem EndpointsFromSTO_cMeta_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < cMeta κ := by
  unfold cMeta
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- `S⁻¹ ≤ c M⁻¹` from `M ≤ c S`. -/
theorem EndpointsFromSTO_inv_le {M S c : ℝ} (hM : 0 < M) (hS : 0 < S) (hc : 0 < c) (h : M ≤ c * S) :
    S⁻¹ ≤ c * M⁻¹ := by
  have h1 : (c * S)⁻¹ ≤ M⁻¹ := inv_anti₀ hM h
  rw [mul_inv] at h1
  calc S⁻¹ = c * (c⁻¹ * S⁻¹) := by field_simp
    _ ≤ c * M⁻¹ := mul_le_mul_of_nonneg_left h1 hc.le

/-- `M_u > 0` along a point of the domain. -/
theorem EndpointsFromSTO_scaleM_pos_dom (hR : ZRange) (d : Sizes) (n : ℕ) {κ τ : ℝ} (hκ : 0 < κ)
    (z : ZDom d κ τ n) : 0 < scaleM (d.L n) (d.W n) (lemE z.1) (lemT z.1) := by
  have hr := hR κ hκ z.1 (EndpointsFromSTO_locDomain_im_pos d n z.2) z.2.2.2 z.2.1
  exact scaleM_pos (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n)
    (by linarith [hr.1, abs_nonneg (lemE z.1)]) hr.2.2.1

/-- Control comparison along a point of the domain: `M_u^{-1} ≤ c_κ M_η^{-1}`. -/
theorem EndpointsFromSTO_scale_ctrl (hR : ZRange) (hM : ZMeta) (d : Sizes) (n : ℕ) {κ τ : ℝ} (hκ : 0 < κ)
    (hκ2 : κ ≤ 2) (z : ZDom d κ τ n) :
    (scaleM (d.L n) (d.W n) (lemE z.1) (lemT z.1))⁻¹ ≤
      cMeta κ * (Meta (d.L n) (d.W n) z.1)⁻¹ := by
  have hz := EndpointsFromSTO_locDomain_im_pos d n z.2
  exact EndpointsFromSTO_inv_le (EndpointsFromSTO_Meta_pos (d.L n) (d.W n) (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n) hz)
    (EndpointsFromSTO_scaleM_pos_dom hR d n hκ z) (EndpointsFromSTO_cMeta_pos hκ hκ2)
    (hM κ hκ (d.L n) (d.W n) (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n) z.1 hz z.2.2.2 z.2.1)

/-- `M_u^{-k} ≤ c_κ^k M_η^{-k}` (natural power). -/
theorem EndpointsFromSTO_scale_ctrl_pow (hR : ZRange) (hM : ZMeta) (d : Sizes) (n : ℕ) {κ τ : ℝ}
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (z : ZDom d κ τ n) (k : ℕ) :
    (scaleM (d.L n) (d.W n) (lemE z.1) (lemT z.1))⁻¹ ^ k ≤
      cMeta κ ^ k * (Meta (d.L n) (d.W n) z.1)⁻¹ ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (EndpointsFromSTO_scaleM_pos_dom hR d n hκ z).le)
    (EndpointsFromSTO_scale_ctrl hR hM d n hκ hκ2 z) k

/-- `M_u^{-p} ≤ c_κ^p M_η^{-p}` (real power, `p ≥ 0`). -/
theorem EndpointsFromSTO_scale_ctrl_rpow (hR : ZRange) (hM : ZMeta) (d : Sizes) (n : ℕ) {κ τ : ℝ}
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (z : ZDom d κ τ n) {p : ℝ} (hp : 0 ≤ p) :
    (scaleM (d.L n) (d.W n) (lemE z.1) (lemT z.1))⁻¹ ^ p ≤
      cMeta κ ^ p * (Meta (d.L n) (d.W n) z.1)⁻¹ ^ p := by
  rw [← Real.mul_rpow (EndpointsFromSTO_cMeta_pos hκ hκ2).le (EndpointsFromSTO_ctrl_nonneg d n z)]
  exact Real.rpow_le_rpow (inv_nonneg.2 (EndpointsFromSTO_scaleM_pos_dom hR d n hκ z).le)
    (EndpointsFromSTO_scale_ctrl hR hM d n hκ hκ2 z) hp

/-- Pointwise: the `(x,y)` entry of `G_X(z) - m(z)` has norm `√u · llErrMat ≤ llErrMat`. -/
theorem EndpointsFromSTO_gEntry_le (hG : ZGreen) (d : Sizes) (n : ℕ) (ω : d.SeqΩ) {z : ℂ} (hz : 0 < z.im)
    (hu1 : lemT z < 1) (x y : Idx (d.L n) (d.W n)) :
    ‖Gn d n ω z x y - (if x = y then mSC z else 0)‖ ≤
      llErrMat (d.L n) (d.W n) (lemE z) (lemT z) (Sizes.seqHflow d n (lemT z) ω) x y := by
  have hgz := hG d n ω z hz
  have hm := ZRescale_msc_eq hz
  have h : Gn d n ω z x y - (if x = y then mSC z else 0) =
      (Real.sqrt (lemT z) : ℂ) * (green (Sizes.seqHflow d n (lemT z) ω)
        (spectralZ (lemE z) (lemT z)) x y - (if x = y then spectralM (lemE z) else 0)) := by
    rw [hgz, hm]
    by_cases hxy : x = y <;> simp [hxy, Matrix.smul_apply]; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact Real.sqrt_le_one.2 hu1.le

/-- `(G_bound)` as a per-time domination over the spectral domain and the entries
(union over `z` outside `P`). -/
theorem EndpointsFromSTO_gBound_perTime (hR : ZRange) (hG : ZGreen) (hM : ZMeta) (hP7 : Univ.P7Out)
    {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {d : Sizes} (hAdm : Admissible 𝔠 d) {κ τ : ℝ} (hκ : 0 < κ)
    (hτ : 0 < τ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => ZDom d κ τ n × (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)))
      (fun n p ω => ‖Gn d n ω p.1.1 p.2.1 p.2.2 - (if p.2.1 = p.2.2 then mSC p.1.1 else 0)‖)
      (fun n p _ => (Meta (d.L n) (d.W n) p.1.1)⁻¹ ^ ((1 : ℝ) / 2)) := by
  have hne : ∀ n, Nonempty (ZDom d κ τ n × (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))) :=
    fun n => ⟨((EndpointsFromSTO_zdom_nonempty d hκ2 hτ1 n).some, (0, 0))⟩
  rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hne]
  intro sec
  have hML := EndpointsFromSTO_section_mlConcl hR hP7 h𝔠 hAdm hκ hτ (fun n => (sec n).1)
  have h1 := EndpointsFromSTO_unit_section (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n => ⟨(0, 0)⟩) hML.1.2.2 (fun n => (sec n).2)
  refine EndpointsFromSTO_stochDomAt_mono hAdm.1 (C := cMeta κ ^ ((1 : ℝ) / 2)) ?_ ?_ ?_ h1
  · intro l _ ω
    have hz := EndpointsFromSTO_locDomain_im_pos d l (sec l).1.2
    exact EndpointsFromSTO_gEntry_le hG d l ω hz (hR κ hκ (sec l).1.1 hz (sec l).1.2.2.2
      (sec l).1.2.1).2.2.1 _ _
  · intro l _ ω
    exact Real.rpow_nonneg (inv_nonneg.2 (EndpointsFromSTO_Meta_pos _ _ (EndpointsFromSTO_one_le_L d l)
      (EndpointsFromSTO_one_le_W d l) (EndpointsFromSTO_locDomain_im_pos d l (sec l).1.2)).le) _
  · intro l _ ω
    exact EndpointsFromSTO_scale_ctrl_rpow hR hM d l hκ hκ2 (sec l).1 (by norm_num)

theorem EndpointsFromSTO_card_idx (d : Sizes) (n : ℕ) : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Idx, Z2, Fintype.card_prod, ZMod.card, Sizes.size, sq]

theorem EndpointsFromSTO_card_z2 (d : Sizes) (n : ℕ) : Fintype.card (Z2 (d.L n)) = d.L n * d.L n := by
  simp [Z2, Fintype.card_prod, ZMod.card]

theorem EndpointsFromSTO_card_z2_le (d : Sizes) (n : ℕ) : Fintype.card (Z2 (d.L n)) ≤ d.size n := by
  rw [EndpointsFromSTO_card_z2]
  unfold Sizes.size
  have := d.W_pos n
  nlinarith [Nat.mul_le_mul (Nat.one_le_iff_ne_zero.2 this.ne') (le_refl (d.L n))]

theorem EndpointsFromSTO_card_pairs (d : Sizes) (n : ℕ) :
    ((Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℕ) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [Fintype.card_prod, EndpointsFromSTO_card_idx, Real.rpow_two]
  push_cast
  ring_nf
  exact le_rfl

theorem EndpointsFromSTO_card_blocks (d : Sizes) (n : ℕ) :
    ((Fintype.card (Z2 (d.L n)) : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  exact_mod_cast EndpointsFromSTO_card_z2_le d n

theorem EndpointsFromSTO_card_block_pairs (d : Sizes) (n : ℕ) :
    ((Fintype.card (Z2 (d.L n) × Z2 (d.L n)) : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [Fintype.card_prod, Real.rpow_two]
  have h' : (Fintype.card (Z2 (d.L n)) : ℝ) ≤ (d.size n : ℝ) := by
    exact_mod_cast EndpointsFromSTO_card_z2_le d n
  have h0 : (0 : ℝ) ≤ Fintype.card (Z2 (d.L n)) := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul h' h' h0 (le_trans h0 h')]

theorem EndpointsFromSTO_div_sqrt {W M : ℝ} (hM : 0 ≤ M) : W / Real.sqrt M = W * M⁻¹ ^ ((1 : ℝ) / 2) := by
  rw [Real.inv_rpow hM, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- Pointwise: the block average of `G_X(z)` against `m(z)` has norm `√u · |𝓛 - 𝒦| ≤ lkGen`. -/
theorem EndpointsFromSTO_ave_le (hA : ZAve) (d : Sizes) (n : ℕ) (ω : d.SeqΩ) {z : ℂ} (hz : 0 < z.im)
    (hu1 : lemT z < 1) (a : Z2 (d.L n)) :
    ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x - mSC z‖ ≤
      Ind.lkGen (d.L n) (d.W n) (lemE z) (lemT z) (Sizes.seqHflow d n (lemT z) ω)
        ![true] ![a] := by
  have h : ((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x - mSC z =
      (Real.sqrt (lemT z) : ℂ) *
        (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (lemT z) ω))
          (spectralZ (lemE z) (lemT z)) (loopOf ![true] ![a]) -
          KLoop.Kcal (d.L n) (d.W n) (lemE z) (lemT z) (loopOf ![true] ![a])) := by
    rw [hA d n ω z hz a, ZRescale_msc_eq hz, EndpointsFromSTO_Kcal_one]
    ring
  unfold Ind.lkGen
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.2 hu1.le)

/-- `(G_bound_ave)` as a per-time domination over the spectral domain and the blocks. -/
theorem EndpointsFromSTO_ave_perTime (hR : ZRange) (hA : ZAve) (hM : ZMeta) (hP7 : Univ.P7Out)
    {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {d : Sizes} (hAdm : Admissible 𝔠 d) {κ τ : ℝ} (hκ : 0 < κ)
    (hτ : 0 < τ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => ZDom d κ τ n × Z2 (d.L n))
      (fun n p ω => ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) p.2, Gn d n ω p.1.1 x x -
        mSC p.1.1‖)
      (fun n p _ => (Meta (d.L n) (d.W n) p.1.1)⁻¹) := by
  have hne : ∀ n, Nonempty (ZDom d κ τ n × Z2 (d.L n)) :=
    fun n => ⟨((EndpointsFromSTO_zdom_nonempty d hκ2 hτ1 n).some, 0)⟩
  rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hne]
  intro sec
  have hML := EndpointsFromSTO_section_mlConcl hR hP7 h𝔠 hAdm hκ hτ (fun n => (sec n).1)
  have h1 := EndpointsFromSTO_unit_section (V := fun n => (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩) (hML.1.1 1 le_rfl)
    (fun n => (![true], ![(sec n).2]))
  refine EndpointsFromSTO_stochDomAt_mono hAdm.1 (C := cMeta κ) ?_ ?_ ?_ h1
  · intro l _ ω
    have hz := EndpointsFromSTO_locDomain_im_pos d l (sec l).1.2
    exact EndpointsFromSTO_ave_le hA d l ω hz (hR κ hκ (sec l).1.1 hz (sec l).1.2.2.2
      (sec l).1.2.1).2.2.1 _
  · intro l _ ω
    exact EndpointsFromSTO_ctrl_nonneg d l (sec l).1
  · intro l _ ω
    have h := EndpointsFromSTO_scale_ctrl hR hM d l hκ hκ2 (sec l).1
    simpa using h

/-- Pointwise: `tr(G E_a G^σ E_b) - profile = u (𝓛 - 𝒦)`, of norm `u · lkGen ≤ lkGen`. -/
theorem EndpointsFromSTO_trace_le (hP : ZProfile) (hT : ZTrace) (d : Sizes) (n : ℕ) (ω : d.SeqΩ) {z : ℂ}
    (hz : 0 < z.im) (hu1 : lemT z < 1) (hu0 : 0 < lemT z) (σ : Bool) (a b : Z2 (d.L n)) :
    ‖trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b‖ ≤
      Ind.lkGen (d.L n) (d.W n) (lemE z) (lemT z) (Sizes.seqHflow d n (lemT z) ω)
        (qdSign σ) ![a, b] := by
  have h : trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b = (lemT z : ℂ) *
      (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (lemT z) ω))
          (spectralZ (lemE z) (lemT z)) (loopOf (qdSign σ) ![a, b]) -
        KLoop.Kcal (d.L n) (d.W n) (lemE z) (lemT z) (loopOf (qdSign σ) ![a, b])) := by
    rw [hT d n ω z hz σ a b, hP (d.L n) (d.W n) z hz σ a b]
    ring
  unfold Ind.lkGen
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0.le]
  exact mul_le_of_le_one_left (norm_nonneg _) hu1.le

/-- `(Meq:QdW1/2)` as a per-time domination over the spectral domain, `σ`, and the blocks. -/
theorem EndpointsFromSTO_qdW_perTime (hR : ZRange) (hP : ZProfile) (hT : ZTrace) (hM : ZMeta)
    (hP7 : Univ.P7Out) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {d : Sizes} (hAdm : Admissible 𝔠 d) {κ τ : ℝ}
    (hκ : 0 < κ) (hτ : 0 < τ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => (ZDom d κ τ n × Bool) × (Z2 (d.L n) × Z2 (d.L n)))
      (fun n p ω => ‖trGEGE d n ω p.1.1.1 p.1.2 p.2.1 p.2.2 -
        profile (d.L n) (d.W n) p.1.1.1 p.1.2 p.2.1 p.2.2‖)
      (fun n p _ => (Meta (d.L n) (d.W n) p.1.1.1)⁻¹ ^ 2) := by
  have hne : ∀ n, Nonempty ((ZDom d κ τ n × Bool) × (Z2 (d.L n) × Z2 (d.L n))) :=
    fun n => ⟨(((EndpointsFromSTO_zdom_nonempty d hκ2 hτ1 n).some, true), (0, 0))⟩
  rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hne]
  intro sec
  have hML := EndpointsFromSTO_section_mlConcl hR hP7 h𝔠 hAdm hκ hτ (fun n => (sec n).1.1)
  have h1 := EndpointsFromSTO_unit_section (V := fun n => (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩) (hML.1.1 2 (by norm_num))
    (fun n => (qdSign (sec n).1.2, ![(sec n).2.1, (sec n).2.2]))
  refine EndpointsFromSTO_stochDomAt_mono hAdm.1 (C := cMeta κ ^ 2) ?_ ?_ ?_ h1
  · intro l _ ω
    have hz := EndpointsFromSTO_locDomain_im_pos d l (sec l).1.1.2
    have hr := hR κ hκ (sec l).1.1.1 hz (sec l).1.1.2.2.2 (sec l).1.1.2.1
    exact EndpointsFromSTO_trace_le hP hT d l ω hz hr.2.2.1 hr.2.1 _ _ _
  · intro l _ ω
    exact pow_nonneg (EndpointsFromSTO_ctrl_nonneg d l (sec l).1.1) 2
  · intro l _ ω
    exact EndpointsFromSTO_scale_ctrl_pow hR hM d l hκ hκ2 (sec l).1.1 2

/-- Pointwise: `E tr(G E_a G^σ E_b) - profile = u (𝔼𝓛 - 𝒦)`, of norm `u |𝔼𝓛 - 𝒦| ≤ |expLoopErr|`
(the integral is only moved through the constant `u`: `integral_const_mul`). -/
theorem EndpointsFromSTO_qdS_le (hP : ZProfile) (hT : ZTrace) (d : Sizes) (n : ℕ) {z : ℂ} (hz : 0 < z.im)
    (hu1 : lemT z < 1) (hu0 : 0 < lemT z) (σ : Bool) (a b : Z2 (d.L n)) :
    ‖(∫ ω, trGEGE d n ω z σ a b ∂(Sizes.seqP d)) - profile (d.L n) (d.W n) z σ a b‖ ≤
      ‖Evol.expLoopErr d n (lemE z) (lemT z) (qdSign σ) ![a, b]‖ := by
  have h : (∫ ω, trGEGE d n ω z σ a b ∂(Sizes.seqP d)) - profile (d.L n) (d.W n) z σ a b =
      (lemT z : ℂ) * Evol.expLoopErr d n (lemE z) (lemT z) (qdSign σ) ![a, b] := by
    have hω : ∀ ω, trGEGE d n ω z σ a b = (lemT z : ℂ) *
        gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (lemT z) ω))
          (spectralZ (lemE z) (lemT z)) (loopOf (qdSign σ) ![a, b]) :=
      fun ω => hT d n ω z hz σ a b
    simp_rw [hω]
    rw [integral_const_mul, hP (d.L n) (d.W n) z hz σ a b]
    unfold Evol.expLoopErr
    ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0.le]
  exact mul_le_of_le_one_left (norm_nonneg _) hu1.le

/-- `(Meq:QdS1/2)`, eventually and uniformly over the spectral domain, `σ`, and the blocks
(the diagonal argument over sections, `EndpointsFromSTO_eventually_forall_of_sections`). -/
theorem EndpointsFromSTO_qdS_eventually (hR : ZRange) (hP : ZProfile) (hT : ZTrace) (hM : ZMeta)
    (hExp : Univ.P7ExpOut) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {d : Sizes} (hAdm : Admissible 𝔠 d)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) :
    ∀ᶠ n in atTop, ∀ p : (ZDom d κ τ n × Bool) × (Z2 (d.L n) × Z2 (d.L n)),
      ‖(∫ ω, trGEGE d n ω p.1.1.1 p.1.2 p.2.1 p.2.2 ∂(Sizes.seqP d)) -
          profile (d.L n) (d.W n) p.1.1.1 p.1.2 p.2.1 p.2.2‖ ≤
        (Meta (d.L n) (d.W n) p.1.1.1) ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τ := by
  have hne : ∀ n, Nonempty ((ZDom d κ τ n × Bool) × (Z2 (d.L n) × Z2 (d.L n))) :=
    fun n => ⟨(((EndpointsFromSTO_zdom_nonempty d hκ2 hτ1 n).some, true), (0, 0))⟩
  refine EndpointsFromSTO_eventually_forall_of_sections hne ?_
  intro sec
  have hε : 0 < 𝔠 * τ / 2 := by positivity
  have hExpC := EndpointsFromSTO_section_mlExp hR hExp h𝔠 hAdm hκ hτ (fun n => (sec n).1.1)
  filter_upwards [hExpC (𝔠 * τ / 2) hε, hAdm.1.eventually (eventually_le_rpow (cMeta κ ^ 3) hε),
    hAdm.2] with n hn hc hW
  have hN := P7FromSTO_size_pos d n
  have hz := EndpointsFromSTO_locDomain_im_pos d n (sec n).1.1.2
  have hr := hR κ hκ (sec n).1.1.1 hz (sec n).1.1.2.2.2 (sec n).1.1.2.1
  have hMpos := EndpointsFromSTO_Meta_pos _ _ (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n) hz
  have hNe : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) := Real.rpow_nonneg hN.le _
  have hinv3 : (scaleM (d.L n) (d.W n) (lemE (sec n).1.1.1) (lemT (sec n).1.1.1) ^ 3)⁻¹ ≤
      cMeta κ ^ 3 * ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ := by
    rw [← inv_pow, ← inv_pow]
    exact EndpointsFromSTO_scale_ctrl_pow hR hM d n hκ hκ2 (sec n).1.1 3
  have hNN : ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) * ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) =
      ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have hNW : ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ) ≤ (d.W n : ℝ) ^ τ := by
    rw [Real.rpow_mul hN.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hW hτ.le
  have hM3 : 0 ≤ ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ := by positivity
  calc ‖(∫ ω, trGEGE d n ω (sec n).1.1.1 (sec n).1.2 (sec n).2.1 (sec n).2.2 ∂(Sizes.seqP d)) -
          profile (d.L n) (d.W n) (sec n).1.1.1 (sec n).1.2 (sec n).2.1 (sec n).2.2‖
      ≤ ‖Evol.expLoopErr d n (lemE (sec n).1.1.1) (lemT (sec n).1.1.1) (qdSign (sec n).1.2)
          ![(sec n).2.1, (sec n).2.2]‖ := EndpointsFromSTO_qdS_le hP hT d n hz hr.2.2.1 hr.2.1 _ _ _
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) *
          (scaleM (d.L n) (d.W n) (lemE (sec n).1.1.1) (lemT (sec n).1.1.1) ^ 3)⁻¹ :=
        hn (qdSign (sec n).1.2) ![(sec n).2.1, (sec n).2.2]
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) *
          (cMeta κ ^ 3 * ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv3 hNe
    _ = (((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) * cMeta κ ^ 3) *
          ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ := by ring
    _ ≤ (((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2) * ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ / 2)) *
          ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hNe) hM3
    _ = ((d.size n : ℕ) : ℝ) ^ (𝔠 * τ) * ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ := by
        rw [hNN]
    _ ≤ (d.W n : ℝ) ^ τ * ((Meta (d.L n) (d.W n) (sec n).1.1.1) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hNW hM3
    _ = (Meta (d.L n) (d.W n) (sec n).1.1.1) ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τ := by
        rw [_root_.zpow_neg, zpow_ofNat, mul_comm]

theorem EndpointsFromSTO_locDomain_empty {N : ℕ} {κ τ : ℝ} (hN : 2 ≤ N) (h : ¬ (κ ≤ 2 ∧ τ ≤ 1)) (z : ℂ) :
    ¬ locDomain N κ τ z := by
  intro hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [not_and_or, not_le, not_le] at h
  rcases h with hκ | hτ
  · have := abs_nonneg z.re
    linarith
  · have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have := Real.one_lt_rpow hN1 (by linarith : 0 < -1 + τ)
    linarith

/-- **`locSC`** from `P7Out` and the transfer statements `ZRange`, `ZGreen`, `ZMeta`, `ZAve`. -/
theorem locSC_of_pins (hR : ZRange) (hG : ZGreen) (hM : ZMeta) (hA : ZAve) (hP7 : Univ.P7Out) :
    locSC := by
  intro 𝔠 h𝔠 d hAdm κ τ D hκ hτ hD
  by_cases hdom : κ ≤ 2 ∧ τ ≤ 1
  · obtain ⟨hκ2, hτ1⟩ := hdom
    have e1 := EndpointsFromSTO_endpoint_of_perTime (P := Sizes.seqP d) (size := d.size) (W := d.W)
      hAdm.1 h𝔠 hAdm.2 (Z := fun n => ZDom d κ τ n)
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (C := 2)
      (Eventually.of_forall (EndpointsFromSTO_card_pairs d))
      (μ := fun n z => (Meta (d.L n) (d.W n) z.1)⁻¹ ^ ((1 : ℝ) / 2))
      (fun n z => Real.rpow_nonneg (EndpointsFromSTO_ctrl_nonneg d n z) _)
      (EndpointsFromSTO_gBound_perTime hR hG hM hP7 h𝔠 hAdm hκ hτ hκ2 hτ1) hτ hD (by norm_num)
    have e2 := EndpointsFromSTO_endpoint_of_perTime (P := Sizes.seqP d) (size := d.size) (W := d.W)
      hAdm.1 h𝔠 hAdm.2 (Z := fun n => ZDom d κ τ n) (V := fun n => Z2 (d.L n)) (C := 1)
      (Eventually.of_forall (EndpointsFromSTO_card_blocks d))
      (μ := fun n z => (Meta (d.L n) (d.W n) z.1)⁻¹)
      (fun n z => EndpointsFromSTO_ctrl_nonneg d n z)
      (EndpointsFromSTO_ave_perTime hR hA hM hP7 h𝔠 hAdm hκ hτ hκ2 hτ1) hτ hD (by norm_num)
    filter_upwards [e1, e2] with n h1 h2 z hz
    have hMpos := EndpointsFromSTO_Meta_pos (d.L n) (d.W n) (EndpointsFromSTO_one_le_L d n) (EndpointsFromSTO_one_le_W d n)
      (EndpointsFromSTO_locDomain_im_pos d n hz)
    refine ⟨?_, ?_⟩
    · have hset : {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
          ‖Gn d n ω z x y - (if x = y then mSC z else 0)‖ ≤
            (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z)} =
          {ω | ¬ ∀ v : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n),
            ‖Gn d n ω z v.1 v.2 - (if v.1 = v.2 then mSC z else 0)‖ ≤
              (d.W n : ℝ) ^ τ * (Meta (d.L n) (d.W n) z)⁻¹ ^ ((1 : ℝ) / 2)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Prod.forall, EndpointsFromSTO_div_sqrt hMpos.le]
      rw [hset]
      exact h1 ⟨z, hz⟩
    · have hset : {ω | ¬ ∀ a : Z2 (d.L n),
          ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x - mSC z‖ ≤
            (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z} =
          {ω | ¬ ∀ a : Z2 (d.L n),
            ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x - mSC z‖ ≤
              (d.W n : ℝ) ^ τ * (Meta (d.L n) (d.W n) z)⁻¹} := by
        ext ω
        simp only [Set.mem_ofPred_eq, div_eq_mul_inv]
      rw [hset]
      exact h2 ⟨z, hz⟩
  · filter_upwards [hAdm.1.eventually_ge_atTop 2] with n hn z hz
    exact absurd hz (EndpointsFromSTO_locDomain_empty hn hdom z)

/-- **`QDiff`** from `P7Out`, `P7ExpOut` and the transfer statements `ZRange`, `ZProfile`,
`ZTrace`, `ZMeta`. -/
theorem QDiff_of_pins (hR : ZRange) (hP : ZProfile) (hT : ZTrace) (hM : ZMeta)
    (hP7 : Univ.P7Out) (hExp : Univ.P7ExpOut) : QDiff := by
  intro 𝔠 h𝔠 d hAdm κ τ D hκ hτ hD
  by_cases hdom : κ ≤ 2 ∧ τ ≤ 1
  · obtain ⟨hκ2, hτ1⟩ := hdom
    have e1 := EndpointsFromSTO_endpoint_of_perTime (P := Sizes.seqP d) (size := d.size) (W := d.W)
      hAdm.1 h𝔠 hAdm.2 (Z := fun n => ZDom d κ τ n × Bool)
      (V := fun n => Z2 (d.L n) × Z2 (d.L n)) (C := 2)
      (Eventually.of_forall (EndpointsFromSTO_card_block_pairs d))
      (μ := fun n z => (Meta (d.L n) (d.W n) z.1.1)⁻¹ ^ 2)
      (fun n z => pow_nonneg (EndpointsFromSTO_ctrl_nonneg d n z.1) 2)
      (EndpointsFromSTO_qdW_perTime hR hP hT hM hP7 h𝔠 hAdm hκ hτ hκ2 hτ1) hτ hD (by norm_num)
    have e2 := EndpointsFromSTO_qdS_eventually hR hP hT hM hExp h𝔠 hAdm hκ hτ hκ2 hτ1
    filter_upwards [e1, e2] with n h1 h2 z hz σ
    refine ⟨?_, fun a b => h2 ((⟨z, hz⟩, σ), (a, b))⟩
    have hset : {ω | ¬ ∀ a b : Z2 (d.L n),
          ‖trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b‖ ≤
            (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z ^ 2} =
          {ω | ¬ ∀ v : Z2 (d.L n) × Z2 (d.L n),
            ‖trGEGE d n ω z σ v.1 v.2 - profile (d.L n) (d.W n) z σ v.1 v.2‖ ≤
              (d.W n : ℝ) ^ τ * (Meta (d.L n) (d.W n) z)⁻¹ ^ 2} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Prod.forall, div_eq_mul_inv, inv_pow]
    rw [hset]
    exact h1 (⟨z, hz⟩, σ)
  · filter_upwards [hAdm.1.eventually_ge_atTop 2] with n hn z hz
    exact absurd hz (EndpointsFromSTO_locDomain_empty hn hdom z)

end Skeleton

/-- **`locSC ∧ QDiff` from the six transfer statements and the estimate `STOAll`.** -/
theorem EndpointsFromSTO_skeleton_T1 (hR : ZRange) (hG : ZGreen) (hM : ZMeta) (hA : ZAve) (hT : ZTrace)
    (hP : ZProfile) : STOAll → locSC ∧ QDiff := fun hSTO =>
  ⟨locSC_of_pins hR hG hM hA (p7Out_of_STOAll hSTO),
    QDiff_of_pins hR hP hT hM (p7Out_of_STOAll hSTO) (p7ExpOut_of_STOAll hSTO)⟩

/-- `decol ∧ QUE` from the six transfer statements and the estimate `STOAll`, by `decol_of_locSC`
and `QUE_of_QDiff`. -/
theorem EndpointsFromSTO_skeleton_decol_QUE (hR : ZRange) (hG : ZGreen) (hM : ZMeta) (hA : ZAve)
    (hT : ZTrace) (hP : ZProfile) (hSTO : STOAll) : decol ∧ QUE :=
  ⟨decol_of_locSC (EndpointsFromSTO_skeleton_T1 hR hG hM hA hT hP hSTO).1,
    QUE_of_QDiff (EndpointsFromSTO_skeleton_T1 hR hG hM hA hT hP hSTO).2⟩

/-- **`locSC ∧ QDiff` outright**: the six transfer statements are proved in `ZRescale`, so
`locSC ∧ QDiff` follows from the estimate `STOAll` alone. -/
theorem locSC_QDiff_of_STOAll : STOAll → locSC ∧ QDiff :=
  EndpointsFromSTO_skeleton_T1 zRange zGreen zMeta zAve zTrace
    zProfile

/-- `decol ∧ QUE` from the estimate `STOAll` alone. -/
theorem decol_QUE_of_STOAll (hSTO : STOAll) : decol ∧ QUE :=
  EndpointsFromSTO_skeleton_decol_QUE zRange zGreen zMeta zAve zTrace
    zProfile hSTO

end RBM.Endpoints
