/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Model
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Linear forms in the Gaussian coordinates of the sequence-level sample

The coordinates of `Sizes.seqP d` are independent centred Gaussians (`seqP` is an infinite
product), so a finite real linear combination of them is again a centred Gaussian, with variance
the weighted sum of the coordinate variances.

## Main statements

* `RBM.Gauss.LinearForm.iIndepFun_coord` : the coordinates are independent
* `RBM.Gauss.LinearForm.map_sum_const_mul_coord` : a finite linear form is a centred Gaussian
* `RBM.Gauss.LinearForm.integral_indep_pair`, `lintegral_indep_pair` : conditioning on an
  independent block (iterated integrals)
-/

namespace RBM.Gauss.LinearForm

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The coordinates are independent.**  `seqP` is an infinite product measure. -/
theorem iIndepFun_coord :
    iIndepFun (fun (c : Sizes.SeqCoord d) (ω : Sizes.SeqΩ d) => ω c) (Sizes.seqP d) := by
  have := iIndepFun_infinitePi (P := fun c : Sizes.SeqCoord d => gaussianReal 0 (Sizes.seqGvar d c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [Sizes.seqP] using this

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι]

/-- **A finite real linear form in an independent Gaussian family is a centred Gaussian**, with
variance `∑ a_i² v_i`.  Induction on the finite set: a scaled variable is independent of the sum
of the others, and Gaussians convolve. -/
theorem map_sum_const_mul_of_indep {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P) (a : ι → ℝ)
    (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  have hmul : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul _
  have hindep' : iIndepFun (fun i ω => a i * X i ω) P :=
    hindep.comp (fun i => fun x : ℝ => a i * x) fun _ => by fun_prop
  have hlaw' : ∀ i, P.map (fun ω => a i * X i ω)
      = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    intro i
    have h : P.map (fun ω => a i * X i ω) = (P.map (X i)).map (fun x : ℝ => a i * x) := by
      rw [Measure.map_map (by fun_prop) (hmeas i)]
      rfl
    rw [h, hlaw i, gaussianReal_map_const_mul (a i)]
    simp
  induction s using Finset.induction with
  | empty => simp [Measure.map_const]
  | insert i₀ s hi₀ ih =>
    have hsum : Measurable (fun ω => ∑ i ∈ s, a i * X i ω) :=
      Finset.measurable_sum _ fun i _ => hmul i
    have hindep0 := hindep'.indepFun_finsetSum_of_notMem (fun i => hmul i) hi₀
    have hfun : (∑ j ∈ s, fun ω => a j * X j ω) = fun ω => ∑ i ∈ s, a i * X i ω := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun] at hindep0
    have hadd : (fun ω => ∑ i ∈ insert i₀ s, a i * X i ω)
        = (fun ω => a i₀ * X i₀ ω) + (fun ω => ∑ i ∈ s, a i * X i ω) := by
      funext ω
      simp [Finset.sum_insert hi₀]
    rw [hadd, (hindep0.symm).map_add_eq_map_conv_map (hmul i₀) hsum, ih, hlaw' i₀,
      gaussianReal_conv_gaussianReal, Finset.sum_insert hi₀]
    simp

end General

/-- **A finite real linear form in the coordinates is a centred Gaussian**, with variance the
weighted sum `∑ a_c² v_c`. -/
theorem map_sum_const_mul_coord (a : Sizes.SeqCoord d → ℝ) (s : Finset (Sizes.SeqCoord d)) :
    (Sizes.seqP d).map (fun ω : Sizes.SeqΩ d => ∑ c ∈ s, a c * ω c)
      = gaussianReal 0 (∑ c ∈ s, NNReal.mk (a c ^ 2) (sq_nonneg _) * Sizes.seqGvar d c) :=
  map_sum_const_mul_of_indep (fun c => measurable_pi_apply c) (fun c => Sizes.seqP_map_eval d c)
    (iIndepFun_coord d) a s

section MomentBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι] {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- The variance of the linear form `∑ a_i X_i`. -/
noncomputable def linVar (v : ι → ℝ≥0) (a : ι → ℝ) (s : Finset ι) : ℝ≥0 :=
  ∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i

variable (hmeas : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
  (hindep : iIndepFun X P)
include hmeas hlaw hindep

omit [IsProbabilityMeasure P] [DecidableEq ι] hlaw hindep in
theorem measurable_lin (a : ι → ℝ) (s : Finset ι) :
    Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
  Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _

/-- The law of the linear form, in terms of `linVar`. -/
theorem map_lin (a : ι → ℝ) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω) = gaussianReal 0 (linVar v a s) :=
  map_sum_const_mul_of_indep hmeas hlaw hindep a s

end MomentBound

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Conditioning on an independent block.**  If `U` and `V` are independent, an integral of
`F(U, V)` is the iterated integral against their laws: the outer variable `V` may be held fixed and
the inner integral computed against the law of `U` alone. -/
theorem integral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V))) :
    ∫ ω, F (U ω, V ω) ∂P = ∫ y, (∫ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  have hmap := integral_map (μ := P) (φ := fun ω => (U ω, V ω)) (f := F)
    (hU.prodMk hV).aemeasurable (by rw [hpair]; exact hF.aestronglyMeasurable)
  rw [hpair] at hmap
  rw [← hmap, integral_prod_symm F hF]

/-- The same, as an upper bound: a uniform bound on the inner (conditional) integral gives a
bound on the whole integral. -/
theorem integral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V)))
    {g : β → ℝ} (hg : Integrable g (P.map V))
    (hbound : ∀ᵐ y ∂(P.map V), (∫ x, F (x, y) ∂(P.map U)) ≤ g y) :
    ∫ ω, F (U ω, V ω) ∂P ≤ ∫ y, g y ∂(P.map V) := by
  rw [integral_indep_pair hU hV h hF]
  exact integral_mono_ae hF.integral_prod_right hg hbound

/-- **Tonelli across an independent pair.**  For a nonnegative measurable `F`, no integrability
is needed: the integral of `F(U, V)` is the iterated integral against the two laws.  This is what
lets the conditional bound be proved without assuming integrability first. -/
theorem lintegral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  rw [← lintegral_map hF (hU.prodMk hV), hpair, lintegral_prod_symm' F hF]

/-- The same, as an upper bound from a bound on the inner (conditional) integral. -/
theorem lintegral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) {c : ℝ≥0∞}
    (hbound : ∀ y, (∫⁻ x, F (x, y) ∂(P.map U)) ≤ c) [IsProbabilityMeasure P] :
    ∫⁻ ω, F (U ω, V ω) ∂P ≤ c := by
  rw [lintegral_indep_pair hU hV h hF]
  calc ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V)
      ≤ ∫⁻ _y, c ∂(P.map V) := lintegral_mono hbound
    _ = c := by
        rw [lintegral_const]
        simp

end Block

section Glue

variable {ι : Type*} [DecidableEq ι]

/-- Glue two coordinate blocks into a full sample point, filling the rest with `0`. -/
def glue (S T : Finset ι) (p : (S → ℝ) × (T → ℝ)) : ι → ℝ := fun c =>
  if h : c ∈ S then p.1 ⟨c, h⟩ else if h' : c ∈ T then p.2 ⟨c, h'⟩ else 0

theorem measurable_glue (S T : Finset ι) : Measurable (glue S T) := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ S
  · simpa [glue, h] using (measurable_fst.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.1 _)
  · by_cases h' : c ∈ T
    · simpa [glue, h, h'] using
        (measurable_snd.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.2 _)
    · simp only [glue, h, h', ↓reduceDIte]
      exact measurable_const

/-- Gluing the two blocks of `ω` back together reproduces `ω` on `S ∪ T`. -/
theorem glue_agree (S T : Finset ι) (ω : ι → ℝ) {c : ι} (hc : c ∈ S ∪ T) :
    glue S T ((fun c : S => ω c), (fun c : T => ω c)) c = ω c := by
  simp only [glue]
  by_cases h : c ∈ S
  · simp [h]
  · have h' : c ∈ T := by
      rcases Finset.mem_union.1 hc with h'' | h''
      · exact absurd h'' h
      · exact h''
    simp [h, h']

end Glue

end RBM.Gauss.LinearForm
