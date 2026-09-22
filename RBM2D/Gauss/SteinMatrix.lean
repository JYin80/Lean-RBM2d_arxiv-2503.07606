/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Stein
import Mathlib.Probability.ProductMeasure

/-!
# Coordinatewise Stein identity for a product Gaussian measure

This result is independent of the indexing of the band matrix. Given a countable family
of independent centred real Gaussian coordinates, resampling one coordinate from its own
law leaves the product measure unchanged. The complex one-dimensional Stein identity then
gives `E[ω c • g ω] = v c • E[g' ω]`.

The concrete d=2 Gaussian matrix model can instantiate this theorem after its coordinates,
variance map, and product law have been constructed in `Gauss/Model.lean`.
-/

namespace RBM.Gauss.GaussianProduct

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The sample space with one independent real coordinate at each index. -/
abbrev Sample (ι : Type*) := ι → ℝ

/-- Independent centred Gaussian coordinates with specified variances. -/
noncomputable def law (v : ι → ℝ≥0) : Measure (Sample ι) :=
  Measure.infinitePi fun c => gaussianReal 0 (v c)

instance (v : ι → ℝ≥0) : IsProbabilityMeasure (law v) := by
  unfold law
  infer_instance

/-- The complex one-dimensional identity also holds at zero variance, when the law is Dirac. -/
theorem integral_mul_gaussianReal_complex_all {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · exact RBM.integral_mul_gaussianReal_complex hv hf hf'c hb hb'

/-- Replace the `c`-th coordinate by an independent real number. -/
noncomputable def update (c : ι) (p : Sample ι × ℝ) : Sample ι :=
  Function.update p.1 c p.2

omit [Countable ι] in
@[simp] theorem update_self (c : ι) (p : Sample ι × ℝ) : update c p c = p.2 :=
  Function.update_self _ _ _

omit [Countable ι] in
theorem update_of_ne (c : ι) (p : Sample ι × ℝ) {i : ι} (h : i ≠ c) :
    update c p i = p.1 i :=
  Function.update_of_ne h _ _

omit [Countable ι] in
theorem measurable_update (c : ι) : Measurable (update c) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [update_self] using measurable_snd
  · simpa only [update_of_ne c _ h, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

omit [Countable ι] in
theorem continuous_update_coord (c : ι) (ω : Sample ι) :
    Continuous fun t : ℝ => Function.update ω c t := by
  refine continuous_pi fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [Function.update_self] using continuous_id'
  · simpa only [Function.update_of_ne h] using continuous_const

omit [Countable ι] [DecidableEq ι] in
/-- Measurable rectangles witness the independence of the coordinate laws. -/
theorem law_pi (v : ι → ℝ≥0) {s : Finset ι} {t : ι → Set ℝ}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    law v (Set.pi (↑s) t) = ∏ i ∈ s, (gaussianReal 0 (v i)) (t i) := by
  unfold law
  exact Measure.infinitePi_pi _ ht

omit [Countable ι] in
/-- Replacing one coordinate by an independent copy of its law preserves the product law. -/
theorem map_update (v : ι → ℝ≥0) (c : ι) :
    ((law v).prod (gaussianReal 0 (v c))).map (update c) = law v := by
  classical
  have hUm : Measurable (update c) := measurable_update c
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hst : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply hUm hst]
  by_cases hc : c ∈ s
  · have hpre : update c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑(s.erase c)) t) ×ˢ t c := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_erase,
        Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← update_of_ne c p hi.2]
          exact h i hi.1
        · rw [← update_self c p]
          exact h c hc
      · rintro ⟨h1, h2⟩ i hi
        by_cases hic : i = c
        · subst hic
          rwa [update_self]
        · rw [update_of_ne c p hic]
          exact h1 i ⟨hi, hic⟩
    rw [hpre, Measure.prod_prod, law_pi v (fun i _ => ht i), ← Finset.prod_erase_mul s _ hc]
  · have hpre : update c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑s) t) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Set.mem_univ, and_true,
        Finset.mem_coe]
      constructor
      · intro h i hi
        rw [← update_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
      · intro h i hi
        rw [update_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, law_pi v (fun i _ => ht i)]

/-- Coordinatewise complex Stein identity for a genuine product Gaussian measure.
The derivative is along the fibre obtained by varying only coordinate `c`. -/
theorem stein (v : ι → ℝ≥0) (c : ι) (g g' : Sample ι → ℂ)
    (hgc : Continuous g) (hg'c : Continuous g')
    (hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t))
      (g' ω) (ω c))
    (hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C)
    (hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C) :
    ∫ ω, ω c • g ω ∂(law v) = (v c : ℝ) • ∫ ω, g' ω ∂(law v) := by
  obtain ⟨C₀, hC₀⟩ := hgb
  obtain ⟨C₁, hC₁⟩ := hg'b
  have hC : ∀ ω, ‖g ω‖ ≤ max C₀ C₁ := fun ω => (hC₀ ω).trans (le_max_left _ _)
  have hC' : ∀ ω, ‖g' ω‖ ≤ max C₀ C₁ := fun ω => (hC₁ ω).trans (le_max_right _ _)
  have hgm : Measurable g := hgc.measurable
  have hg'm : Measurable g' := hg'c.measurable
  have hUm : Measurable (update c) := measurable_update c
  have hfib : ∀ (ω : Sample ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s))
        (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  have hInt : Integrable (fun p : Sample ι × ℝ => p.2 • g (update c p))
      ((law v).prod (gaussianReal 0 (v c))) := by
    have hbase : Integrable (fun p : Sample ι × ℝ => p.2)
        ((law v).prod (gaussianReal 0 (v c))) :=
      (RBM.integrable_id_gaussianReal (var := v c)).comp_snd (law v)
    refine Integrable.mono' (hbase.abs.const_mul (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (measurable_snd.smul (hgm.comp hUm)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg p.2)
  have hInt' : Integrable (fun p : Sample ι × ℝ => g' (update c p))
      ((law v).prod (gaussianReal 0 (v c))) := by
    refine Integrable.mono' (integrable_const (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => hC' _)
    exact (hg'm.comp hUm).aestronglyMeasurable
  have hL : ∫ ω, ω c • g ω ∂(law v)
      = ∫ p : Sample ι × ℝ, p.2 • g (update c p)
          ∂((law v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [map_update v c]
      exact ((measurable_pi_apply c).smul hgm).aestronglyMeasurable)]
    simp only [update_self]
  have hR : ∫ ω, g' ω ∂(law v)
      = ∫ p : Sample ι × ℝ, g' (update c p)
          ∂((law v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [map_update v c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hInt, integral_prod _ hInt', ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ∫ t : ℝ, t • g (Function.update ω c t) ∂(gaussianReal 0 (v c))
      = (v c : ℝ) • ∫ t : ℝ, g' (Function.update ω c t) ∂(gaussianReal 0 (v c))
  have hcont : Continuous fun t : ℝ => g' (Function.update ω c t) :=
    hg'c.comp (continuous_update_coord c ω)
  have hst := integral_mul_gaussianReal_complex_all (var := v c)
    (f := fun t => g (Function.update ω c t))
    (f' := fun t => g' (Function.update ω c t))
    (C := max C₀ C₁) (hfib ω) hcont (fun t => hC _) (fun t => hC' _)
  simpa only [Complex.real_smul] using hst

/-! ### A nonconstant, positive-variance instance -/

/-- A two-coordinate product with unit variance and a nonconstant bounded test function. -/
example :
    (∫ ω : Sample Bool, ω true • (↑(Real.sin (ω true)) : ℂ)
        ∂(law (fun _ : Bool => (1 : ℝ≥0))))
      = ∫ ω : Sample Bool, (↑(Real.cos (ω true)) : ℂ)
          ∂(law (fun _ : Bool => (1 : ℝ≥0))) := by
  let g : Sample Bool → ℂ := fun ω => ↑(Real.sin (ω true))
  let g' : Sample Bool → ℂ := fun ω => ↑(Real.cos (ω true))
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_apply true))
  have hg' : Continuous g' :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_apply true))
  have hd : ∀ ω : Sample Bool,
      HasDerivAt (fun t : ℝ => g (Function.update ω true t)) (g' ω) (ω true) := by
    intro ω
    simpa [g, g'] using (Real.hasDerivAt_sin (ω true)).ofReal_comp
  have hb : ∃ C : ℝ, ∀ ω : Sample Bool, ‖g ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [g, Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (ω true)
  have hb' : ∃ C : ℝ, ∀ ω : Sample Bool, ‖g' ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [g', Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (ω true)
  simpa [g, g'] using
    (stein (fun _ : Bool => (1 : ℝ≥0)) true g g' hg hg' hd hb hb')

end RBM.Gauss.GaussianProduct
