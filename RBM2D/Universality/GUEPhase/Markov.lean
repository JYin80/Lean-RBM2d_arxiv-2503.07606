/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Grid
import RBM2D.Path.Markov
import RBM2D.Path.PerTime
import Mathlib.Probability.Moments.SubGaussian

/-!
# The `Pgue` Markov toolkit, `d = 2`

The freezing / conditional sub-Gaussianity toolkit for the GUE-phase grid measure `Pgue d` on the
sequence-level carrier `PathΩ d` (`Universality/GUEPhase/Grid.lean`), the analogue of what
`Path/Markov.lean` provides for the band grid measure `pathP d`: the freezing lemma
`gueCondExp_freeze`, a general freezing-based conditional sub-Gaussianity lemma
(`gueHasCondSubgaussianMGF_of_frozen`), the linear case (`gueHasCondSubgaussianMGF_linear`), and
the entrywise truncation event of the unit GUE increments (`gue_highProb_incr_le`).

Conventions (`d = 2`): `PathΩ d`, `filt d`, `Sizes.SeqΩ d`, `Sizes.SeqCoord d`,
`Idx (d.L n) (d.W n)`, `Sizes.seqXmat d n`, `linTr`, `coordFinset`.  `gue_highProb_incr_le` is
stated as `HighProbAt (Pgue d) d.size` with threshold `d.size n`, grid range `gueGridK d n0 n`,
and the hypothesis `Tendsto d.size atTop atTop` (without it a bounded size gives a constant
failure probability).  The cardinality count uses `card (Idx (d.L n) (d.W n)) = d.size n` and
`gueGridK d n0 n = (d.size n + 1)^(32 n₀ + 64)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
open scoped NNReal ENNReal MeasureTheory

variable (d : Sizes)

/-! ### Private helpers: the `Pgue`-analogues of `Path/Markov.lean`'s freezing plumbing -/

section Freeze

private theorem Markov_indep_incr (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : PathΩ d => ω (k + 1)) inferInstance) (filt d k)
      (Pgue d) := by
  have hI : iIndepFun (fun i : ℕ => (fun ω : PathΩ d => ω i)) (Pgue d) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : Sizes.SeqΩ d → Sizes.SeqΩ d))
      (mX := fun _ => measurable_id)
  have hIndep : iIndep
      (fun n : ℕ => MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance)
      (Pgue d) := (iIndepFun_iff_iIndep
        (fun _ : ℕ => (inferInstance : MeasurableSpace (Sizes.SeqΩ d)))
        (fun i ω => ω i) (Pgue d)).mp hI
  have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance
      ≤ (inferInstance : MeasurableSpace (PathΩ d)) :=
    fun n => le_iSup (fun n => MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance) n
  have hsplit := indep_biSup_compl hle hIndep (Set.Iic k)
  have hfilt : filt d k
      = ⨆ n ∈ Set.Iic k, MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance := by
    have hshow : filt d k =
        (inferInstance : MeasurableSpace (↥(Set.Iic k) → Sizes.SeqΩ d)).comap
          (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k) := rfl
    have hpi : (inferInstance : MeasurableSpace (↥(Set.Iic k) → Sizes.SeqΩ d))
        = ⨆ a : ↥(Set.Iic k),
            MeasurableSpace.comap (fun g : ↥(Set.Iic k) → Sizes.SeqΩ d => g a) inferInstance :=
      rfl
    rw [hshow, hpi, MeasurableSpace.comap_iSup, iSup_subtype]
    simp only [MeasurableSpace.comap_comp]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro _
    rfl
  rw [hfilt]
  have hmono : MeasurableSpace.comap (fun ω : PathΩ d => ω (k + 1)) inferInstance
      ≤ ⨆ n ∈ (Set.Iic k)ᶜ, MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance := by
    have hmem : (k + 1) ∈ (Set.Iic k)ᶜ := by simp
    exact le_biSup (fun n => MeasurableSpace.comap (fun ω : PathΩ d => ω n) inferInstance) hmem
  exact indep_of_indep_of_le_left hsplit.symm hmono

private theorem Markov_map_incr (k : ℕ) :
    (Pgue d).map (fun ω : PathΩ d => ω (k + 1)) = gueUnit d :=
  Measure.infinitePi_map_eval _ (k + 1)

/-- **The freezing lemma for `Pgue`**.  For
`k`, a `filt d k`-measurable `Y : PathΩ d → β` and a jointly measurable
`F : β → Sizes.SeqΩ d → ℝ` with `F (Y ·) (· (k+1))` integrable, conditioning on `filt d k`
freezes `Y` and averages the independent next draw `ω (k+1)` against its own law `gueUnit d`
(the step law at every step `k + 1 ≥ 1` under `Pgue d`). -/
theorem gueCondExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set μ : Measure (PathΩ d) := Pgue d with hμdef
  set Z : PathΩ d → Sizes.SeqΩ d := fun ω => ω (k + 1) with hZdef
  set Φ : PathΩ d → β × Sizes.SeqΩ d := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Sizes.SeqΩ d) := gueUnit d with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((filt d).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := Markov_map_incr d k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt d k := hY.comap_le
    exact (indep_of_indep_of_le_right (Markov_indep_incr d k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  have hkey : ∀ A : Set (PathΩ d), MeasurableSet[filt d k] A →
      ∫ ω in A, F (Y ω) (Z ω) ∂μ = ∫ ω in A, G (Y ω) ∂μ := by
    intro A hA
    have hprodA : (μ.restrict A).map Φ = ((μ.restrict A).map Y).prod ν := by
      refine (Measure.prod_eq ?_).symm
      intro s t hs ht
      have hpre : Φ ⁻¹' (s ×ˢ t) = Y ⁻¹' s ∩ Z ⁻¹' t := by
        ext ω; simp [Φ, Set.mem_prod]
      rw [Measure.map_apply hΦmeas (hs.prod ht), Measure.map_apply hYmeas hs,
        Measure.restrict_apply (hΦmeas (hs.prod ht)), Measure.restrict_apply (hYmeas hs), hpre]
      have hrearrange : Y ⁻¹' s ∩ Z ⁻¹' t ∩ A = Z ⁻¹' t ∩ (A ∩ Y ⁻¹' s) := by
        ext ω; simp only [Set.mem_inter_iff]; tauto
      rw [hrearrange]
      have hASmem : MeasurableSet[filt d k] (A ∩ Y ⁻¹' s) := hA.inter (hY hs)
      have hZTmem : MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have hindep := (Indep_iff (MeasurableSpace.comap Z inferInstance) (filt d k) μ).1
        (Markov_indep_incr d k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
      rw [hindep, ← Measure.map_apply hZmeas ht, hνmap, Set.inter_comm (Y ⁻¹' s) A]
      ring
    have hIntΦA : Integrable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) ((μ.restrict A).map Φ) :=
      hIntΦ.mono_measure (Measure.map_mono Measure.restrict_le_self hΦmeas)
    calc
      ∫ ω in A, F (Y ω) (Z ω) ∂μ
          = ∫ p, F p.1 p.2 ∂((μ.restrict A).map Φ) :=
            (integral_map hΦmeas.aemeasurable hFsm.aestronglyMeasurable).symm
      _ = ∫ p, F p.1 p.2 ∂(((μ.restrict A).map Y).prod ν) := by rw [hprodA]
      _ = ∫ y, G y ∂((μ.restrict A).map Y) := integral_prod _ (hprodA ▸ hIntΦA)
      _ = ∫ ω in A, G (Y ω) ∂μ := integral_map hYmeas.aemeasurable hGmeas.aestronglyMeasurable
  have hIntG : Integrable G (μ.map Y) := by
    have hIntΦY : Integrable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) ((μ.map Y).prod ν) :=
      hprodglobal ▸ hIntΦ
    exact hIntΦY.integral_prod_left
  have hGYint : Integrable (fun ω => G (Y ω)) μ :=
    (integrable_map_measure hGmeas.aestronglyMeasurable hYmeas.aemeasurable).mp hIntG
  have hGYmeas : StronglyMeasurable[filt d k] (fun ω => G (Y ω)) := hGmeas.comp_measurable hY
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((filt d).le k) hInt
    (fun s _ _ => hGYint.integrableOn) (fun s hs _ => (hkey s hs).symm)
    hGYmeas.aestronglyMeasurable).symm

end Freeze

/-! ### `gueHasCondSubgaussianMGF_of_frozen`: conditional sub-Gaussianity from a uniform-in-`y`
unconditional bound on the family. -/

section OfFrozen

/-- **Conditional sub-Gaussianity of a family**. -/
theorem gueHasCondSubgaussianMGF_of_frozen {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace β] (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    {c : ℝ≥0} (hsub : ∀ y, HasSubgaussianMGF (F y) c (gueUnit d)) :
    HasCondSubgaussianMGF (filt d k) ((filt d).le k)
      (fun ω => F (Y ω) (ω (k + 1))) c (Pgue d) := by
  classical
  set hm := (filt d).le k
  have hYmeas : Measurable Y := hY.mono hm le_rfl
  have hUmeas : Measurable (fun ω : PathΩ d => ω (k + 1)) := measurable_pi_apply (k + 1)
  have hindep : IndepFun (fun ω : PathΩ d => ω (k + 1)) Y (Pgue d) := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt d k := hY.comap_le
    exact indep_of_indep_of_le_right (Markov_indep_incr d k) hcle
  have hintegrable : ∀ t : ℝ,
      Integrable (fun ω : PathΩ d => Real.exp (t * F (Y ω) (ω (k + 1)))) (Pgue d) := by
    intro t
    set Fe : Sizes.SeqΩ d × β → ℝ≥0∞ :=
      fun p => ENNReal.ofReal (Real.exp (t * F p.2 p.1)) with hFedef
    have hFe : Measurable Fe := by
      have h0 : Measurable (fun p : Sizes.SeqΩ d × β => F p.2 p.1) := hF.comp measurable_swap
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (h0.const_mul t))
    have hbound : ∀ y : β,
        (∫⁻ x, Fe (x, y) ∂(Pgue d).map (fun ω : PathΩ d => ω (k + 1)))
          ≤ ENNReal.ofReal (Real.exp ((c : ℝ) * t ^ 2 / 2)) := by
      intro y
      rw [Markov_map_incr d k]
      have hintY : Integrable (fun x => Real.exp (t * F y x)) (gueUnit d) :=
        (hsub y).integrable_exp_mul t
      have hofreal := ofReal_integral_eq_lintegral_ofReal hintY
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      have : (∫ x, Real.exp (t * F y x) ∂(gueUnit d)) = mgf (F y) (gueUnit d) t := rfl
      rw [hFedef]
      dsimp only
      rw [← hofreal, this]
      exact ENNReal.ofReal_le_ofReal ((hsub y).mgf_le t)
    have hlt := lintegral_indep_pair_le hUmeas hYmeas hindep hFe hbound
    refine ⟨?_, ?_⟩
    · have h1 : Measurable (fun ω : PathΩ d => F (Y ω) (ω (k + 1))) := by
        have heq : (fun ω : PathΩ d => F (Y ω) (ω (k + 1)))
            = (fun p : β × Sizes.SeqΩ d => F p.1 p.2) ∘ (fun ω => (Y ω, ω (k + 1))) := rfl
        rw [heq]
        exact hF.comp (hYmeas.prodMk hUmeas)
      exact (Real.measurable_exp.comp (h1.const_mul t)).aestronglyMeasurable
    · rw [hasFiniteIntegral_def]
      have heq : ∀ ω, ‖Real.exp (t * F (Y ω) (ω (k + 1)))‖ₑ = Fe (ω (k + 1), Y ω) := by
        intro ω
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFedef]
      simp_rw [heq]
      exact lt_of_le_of_lt hlt ENNReal.ofReal_lt_top
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact hintegrable t
  · intro q
    set t : ℝ := (q : ℝ) with htdef
    set X : PathΩ d → ℝ := fun ω => F (Y ω) (ω (k + 1)) with hXdef
    set Gr : PathΩ d → ℝ := fun ω => Real.exp (t * X ω) with hGrdef
    set Fr : β → Sizes.SeqΩ d → ℝ := fun y x => Real.exp (t * F y x) with hFrdef
    have hFrmeas : Measurable (fun p : β × Sizes.SeqΩ d => Fr p.1 p.2) :=
      Real.measurable_exp.comp (hF.const_mul t)
    have hGreq : (fun ω : PathΩ d => Fr (Y ω) (ω (k + 1))) = Gr := by
      funext ω; rw [hFrdef, hGrdef, hXdef]
    have hIntGr : Integrable Gr (Pgue d) := hintegrable t
    have hfreeze := gueCondExp_freeze d k hY hFrmeas (hGreq ▸ hIntGr)
    have hRHS : (fun ω : PathΩ d => ∫ x, Fr (Y ω) x ∂(gueUnit d))
        = fun ω => mgf (F (Y ω)) (gueUnit d) t := rfl
    rw [hRHS, hGreq] at hfreeze
    have hsm1 : StronglyMeasurable[filt d k] ((Pgue d)[Gr | filt d k]) :=
      stronglyMeasurable_condExp
    have hsm2 : StronglyMeasurable[filt d k] (fun ω => mgf (F (Y ω)) (gueUnit d) t) := by
      have hFrsm : StronglyMeasurable (fun p : β × Sizes.SeqΩ d => Fr p.1 p.2) :=
        hFrmeas.stronglyMeasurable
      have hGmeas : StronglyMeasurable (fun y => ∫ x, Fr y x ∂(gueUnit d)) :=
        hFrsm.integral_prod_right'
      exact hGmeas.comp_measurable hY
    have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
    have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
    have hcomb : ∀ᵐ ρ ∂(Pgue d).trim hm,
        (∫ σ, Gr σ ∂condExpKernel (Pgue d) (filt d k) ρ) = mgf (F (Y ρ)) (gueUnit d) t := by
      filter_upwards [hbridge, htrim] with ρ h1 h2
      rw [← h1, h2]
    filter_upwards [hcomb] with ρ hρ
    change (∫ σ, Gr σ ∂condExpKernel (Pgue d) (filt d k) ρ) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
    rw [hρ, htdef]
    exact (hsub (Y ρ)).mgf_le _

end OfFrozen

/-! ### `vGue`, `gueMap_lin_Xmat`: the law of a linear functional under `gueUnit d`.
The deterministic plumbing (`linTr`, `coordFinset`, `linTr_seqXmat_eq_sum`) is that of
`Path/Markov.lean`; only the two facts tying `gueUnit d` to the coordinates (independence,
per-coordinate law) are specific to the GUE increments. -/

section LinearVariance

private theorem Markov_unitMapEval (c : Sizes.SeqCoord d) :
    (gueUnit d).map (fun ω : Sizes.SeqΩ d => ω c) = gaussianReal 0 (gueUnitVar d c) :=
  Measure.infinitePi_map_eval _ c

private theorem Markov_unitIIndepFun :
    iIndepFun (fun (c : Sizes.SeqCoord d) (ω : Sizes.SeqΩ d) => ω c) (gueUnit d) := by
  have := iIndepFun_infinitePi (P := fun c : Sizes.SeqCoord d => gaussianReal 0 (gueUnitVar d c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [gueUnit] using this

/-- **`vGue`**: the conditional variance of a linear functional under `gueUnit d`, in the
direction `A`. -/
def vGue (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) : ℝ≥0 :=
  linVar (gueUnitVar d)
    (fun c => linTr n A (Sizes.seqXmat d n (Pi.single c 1))) (coordFinset n)

/-- **The law of a linear functional**: under `gueUnit d`, `y ↦ Re tr (A · seqXmat d n y)` is the
centred
Gaussian of variance `vGue d n A`. -/
theorem gueMap_lin_Xmat (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    (gueUnit d).map (fun y => linTr n A (Sizes.seqXmat d n y)) =
      gaussianReal 0 (vGue d n A) := by
  classical
  have hfun : (fun y : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n y))
      = fun y => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) * y c := by
    funext y
    rw [linTr_seqXmat_eq_sum]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfun]
  have hsum := map_sum_const_mul_of_indep (P := gueUnit d)
    (X := fun (c : Sizes.SeqCoord d) (ω : Sizes.SeqΩ d) => ω c) (v := gueUnitVar d)
    (fun c => measurable_pi_apply c) (Markov_unitMapEval d) (Markov_unitIIndepFun d)
    (fun c => linTr n A (Sizes.seqXmat d n (Pi.single c 1))) (coordFinset n)
  rw [hsum]
  rfl

end LinearVariance

/-! ### `gueHasCondSubgaussianMGF_linear`: the `Pgue`-analogue of `Path/Markov.lean`'s
`hasCondSubgaussianMGF_linear`

(Pointwise-bound argument: the private lemmas `measurable_linTr_uncurry`, `mgf_linTr_seqXmat`,
`integrable_exp_mul_X`, `condMGF_le` of `Path/Markov.lean` are reproduced here; the changes are
`pathP d ↦ Pgue d`, `Sizes.seqP d ↦ gueUnit d`, `Sizes.seqGvar d ↦ gueUnitVar d`,
`linTrVar ↦ vGue`, and `√(gridStep) ↦ s`.) -/

section LinearMGF

variable {d}

private theorem Markov_measurable_seqXmat (n : ℕ) : Measurable (Sizes.seqXmat d n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry (d.L n) (d.W n) i j).comp (Sizes.measurable_slice d n)

private theorem Markov_linTr_eq_sum (n : ℕ)
    (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n A X = ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n), (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem Markov_measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
      linTr n p.1 (Sizes.seqXmat d n p.2)) := by
  have heq : (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
      linTr n p.1 (Sizes.seqXmat d n p.2))
      = fun p => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n),
          (p.1 i k * Sizes.seqXmat d n p.2 k i).re :=
    funext fun p => Markov_linTr_eq_sum n p.1 (Sizes.seqXmat d n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        Sizes.seqXmat d n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((Markov_measurable_seqXmat n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem Markov_measurable_linTr_left (n : ℕ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Measurable (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTr n A M) := by
  have heq : (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTr n A M)
      = fun A => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n), (A i k * M k i).re :=
    funext fun A => Markov_linTr_eq_sum n A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

private theorem Markov_measurable_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Measurable (fun x : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n x)) := by
  have heq : (fun x : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n x))
      = fun x => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n),
          (A i k * Sizes.seqXmat d n x k i).re :=
    funext fun x => Markov_linTr_eq_sum n A (Sizes.seqXmat d n x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (Markov_measurable_seqXmat n)))

private theorem Markov_vGue_eq_sum (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    (vGue d n A : ℝ) = ∑ c ∈ coordFinset n,
      (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) ^ 2 * (gueUnitVar d c : ℝ) := by
  unfold vGue linVar
  push_cast [NNReal.coe_mk]
  rfl

private theorem Markov_measurable_vGue (n : ℕ) :
    Measurable (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      (vGue d n A : ℝ)) := by
  have heq : (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      (vGue d n A : ℝ))
      = fun A => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) ^ 2 * (gueUnitVar d c : ℝ) :=
    funext (Markov_vGue_eq_sum n)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ => ((Markov_measurable_linTr_left n _).pow_const 2).mul_const _

private theorem Markov_mgf_lin_Xmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (r : ℝ) :
    mgf (fun x => linTr n A (Sizes.seqXmat d n x)) (gueUnit d) r
      = Real.exp ((vGue d n A : ℝ) * r ^ 2 / 2) := by
  have hlaw : HasLaw (fun x => linTr n A (Sizes.seqXmat d n x))
      (gaussianReal 0 (vGue d n A)) (gueUnit d) :=
    ⟨(Markov_measurable_linTr_seqXmat n A).aemeasurable, gueMap_lin_Xmat d n A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  ring

private theorem Markov_integrable_exp_lin_Xmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * linTr n A (Sizes.seqXmat d n x))) (gueUnit d) := by
  have h : Integrable (fun x : ℝ => Real.exp (r * x))
      ((gueUnit d).map (fun x => linTr n A (Sizes.seqXmat d n x))) := by
    rw [gueMap_lin_Xmat d n A]; exact integrable_exp_mul_gaussianReal r
  exact (integrable_map_measure h.aestronglyMeasurable
    (Markov_measurable_linTr_seqXmat n A).aemeasurable).1 h

private theorem Markov_linTr_zero (n : ℕ)
    (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n 0 X = 0 := by
  unfold linTr; simp

private theorem Markov_vGue_zero (n : ℕ) :
    vGue d n (0 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) = 0 := by
  unfold vGue linVar; simp [Markov_linTr_zero]

private instance Markov_standardBorelMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ))

section MGFBound

variable {n k : ℕ} {A : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}

private theorem Markov_integrable_exp_mul_X (hA : Measurable[filt d k] A) {s c : ℝ} (_hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue d n (A ω) : ℝ) ≤ c) (r : ℝ) :
    Integrable (fun ω : PathΩ d =>
      Real.exp (r * (s * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))) (Pgue d) := by
  classical
  set U : PathΩ d → Sizes.SeqΩ d := fun ω => ω (k + 1) with hUdef
  set F : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp ((r * s) * linTr n p.2 (Sizes.seqXmat d n p.1))) with hFdef
  have hUmeas : Measurable U := measurable_pi_apply (k + 1)
  have hAmeas : Measurable A := hA.mono ((filt d).le k) le_rfl
  have hindep : IndepFun U A (Pgue d) := by
    have hcle : MeasurableSpace.comap A inferInstance ≤ filt d k := hA.comap_le
    exact indep_of_indep_of_le_right (Markov_indep_incr d k) hcle
  have hFmeas : Measurable F := by
    have h0 : Measurable
        (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat d n p.1)) := by
      have heq : (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat d n p.1))
          = fun p => ∑ i : Idx (d.L n) (d.W n), ∑ k' : Idx (d.L n) (d.W n),
              (p.2 i k' * Sizes.seqXmat d n p.1 k' i).re :=
        funext fun p => Markov_linTr_eq_sum n p.2 (Sizes.seqXmat d n p.1)
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
      have hM : Measurable
          (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            p.2 i k') :=
        Measurable.eval_matrix (i := i) (j := k') measurable_snd
      have hX : Measurable
          (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            Sizes.seqXmat d n p.1 k' i) :=
        Measurable.eval_matrix (i := k') (j := i)
          ((Markov_measurable_seqXmat n).comp measurable_fst)
      exact Complex.measurable_re.comp (hM.mul hX)
    have h1 : Measurable
        (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          (r * s) * linTr n p.2 (Sizes.seqXmat d n p.1)) := h0.const_mul _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)
  have hkey := lintegral_indep_pair hUmeas hAmeas hindep hFmeas
  rw [Markov_map_incr d k] at hkey
  have hinner : ∀ y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      (∫⁻ x, F (x, y) ∂(gueUnit d)) =
        ENNReal.ofReal (Real.exp ((vGue d n y : ℝ) * (r * s) ^ 2 / 2)) := by
    intro y
    have hint := Markov_integrable_exp_lin_Xmat n y (r * s)
    have hofreal := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hmgf := Markov_mgf_lin_Xmat n y (r * s)
    rw [mgf] at hmgf
    rw [hFdef]
    dsimp only
    rw [← hofreal, hmgf]
  have hp : MeasurableSet {y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ |
      (vGue d n y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2} :=
    measurableSet_le (((Markov_measurable_vGue n).mul_const _).div_const _) measurable_const
  have hptwise : ∀ ω, (vGue d n (A ω) : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    intro ω
    have h2 := hAs ω
    nlinarith [sq_nonneg r]
  have hae : ∀ᵐ y ∂(Pgue d).map A, (vGue d n y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    rw [ae_map_iff hAmeas.aemeasurable hp]
    exact Filter.Eventually.of_forall hptwise
  have houter_eq : ∫⁻ ω, F (U ω, A ω) ∂(Pgue d)
      = ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue d n y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue d).map A) := by
    rw [hkey]; exact lintegral_congr hinner
  have houter_le : ∫⁻ ω, F (U ω, A ω) ∂(Pgue d) ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
    rw [houter_eq]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue d n y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue d).map A)
        ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) ∂((Pgue d).map A) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hy)
      _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue d).map A) Set.univ := by
          rw [lintegral_const]
      _ ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
          calc ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue d).map A) Set.univ
              ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * 1 := by
                gcongr
                exact prob_le_one
            _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := mul_one _
  refine ⟨?_, ?_⟩
  · have hXmeas : Measurable (fun ω : PathΩ d =>
        Real.exp (r * (s * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))) := by
      have h1 : Measurable (fun ω : PathΩ d =>
          linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))) := by
        have heq : (fun ω : PathΩ d => linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1))))
            = fun ω => ∑ i : Idx (d.L n) (d.W n), ∑ k' : Idx (d.L n) (d.W n),
              (A ω i k' * Sizes.seqXmat d n (ω (k + 1)) k' i).re :=
          funext fun ω => Markov_linTr_eq_sum n (A ω) (Sizes.seqXmat d n (ω (k + 1)))
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
        have hM : Measurable (fun ω : PathΩ d => A ω i k') := Measurable.eval_matrix hAmeas
        have hX : Measurable (fun ω : PathΩ d => Sizes.seqXmat d n (ω (k + 1)) k' i) :=
          Measurable.eval_matrix ((Markov_measurable_seqXmat n).comp hUmeas)
        exact Complex.measurable_re.comp (hM.mul hX)
      exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
    exact hXmeas.aestronglyMeasurable
  · rw [hasFiniteIntegral_def]
    have heq : ∀ ω, ‖Real.exp (r * (s *
        linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))‖ₑ = F (U ω, A ω) := by
      intro ω
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFdef]
      dsimp only
      congr 2
      ring
    simp_rw [heq]
    exact lt_of_le_of_lt houter_le ENNReal.ofReal_lt_top

private theorem Markov_cond_mgf_le (hA : Measurable[filt d k] A) {s c : ℝ} (hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue d n (A ω) : ℝ) ≤ c) (r : ℝ) :
    ∀ᵐ ω ∂((Pgue d).trim ((filt d).le k)),
      mgf (fun ρ => s * linTr n (A ρ) (Sizes.seqXmat d n (ρ (k + 1))))
        (condExpKernel (Pgue d) (filt d k) ω) r ≤ Real.exp (c * r ^ 2 / 2) := by
  classical
  set X : PathΩ d → ℝ := fun ρ => s * linTr n (A ρ) (Sizes.seqXmat d n (ρ (k + 1))) with hXdef
  set Gr : PathΩ d → ℝ := fun ρ => Real.exp (r * X ρ) with hGrdef
  set Fr : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℝ :=
    fun y x => Real.exp (r * (s * linTr n y (Sizes.seqXmat d n x))) with hFrdef
  have hFrmeas : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        Fr p.1 p.2) := by
    have h1 : Measurable
        (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
          linTr n p.1 (Sizes.seqXmat d n p.2)) := Markov_measurable_linTr_uncurry n
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : PathΩ d => Fr (A ρ) (ρ (k + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef, hXdef]
  have hIntGr : Integrable Gr (Pgue d) := Markov_integrable_exp_mul_X hA hc hAs r
  have hfreeze := gueCondExp_freeze d k hA hFrmeas (hGreq ▸ hIntGr)
  have hRHS : (fun ρ : PathΩ d => ∫ x, Fr (A ρ) x ∂(gueUnit d))
      = fun ρ => Real.exp ((vGue d n (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    funext ρ
    have hmgf := Markov_mgf_lin_Xmat n (A ρ) (r * s)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * s) * linTr n (A ρ) (Sizes.seqXmat d n x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  have hm : filt d k ≤ (inferInstance : MeasurableSpace (PathΩ d)) := (filt d).le k
  have hsm1 : StronglyMeasurable[filt d k] ((Pgue d)[Gr | filt d k]) :=
    stronglyMeasurable_condExp
  have hsm2 : StronglyMeasurable[filt d k]
      (fun ρ => Real.exp ((vGue d n (A ρ) : ℝ) * (r * s) ^ 2 / 2)) := by
    have hcont : Measurable (fun y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        Real.exp ((vGue d n y : ℝ) * (r * s) ^ 2 / 2)) :=
      Real.measurable_exp.comp (((Markov_measurable_vGue n).mul_const _).div_const _)
    exact (hcont.comp hA).stronglyMeasurable
  have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
  have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
  have hcomb : ∀ᵐ ρ ∂(Pgue d).trim hm,
      (∫ σ, Gr σ ∂condExpKernel (Pgue d) (filt d k) ρ)
        = Real.exp ((vGue d n (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    filter_upwards [hbridge, htrim] with ρ h1 h2
    rw [← h1, h2]
  filter_upwards [hcomb] with ρ hρ
  change (∫ σ, Gr σ ∂condExpKernel (Pgue d) (filt d k) ρ) ≤ Real.exp (c * r ^ 2 / 2)
  rw [hρ]
  apply Real.exp_le_exp.2
  have h2 := hAs ρ
  nlinarith [sq_nonneg r]

end MGFBound

end LinearMGF

/-- **Conditional sub-Gaussianity of a linear functional under `Pgue d`**.  For a
`filt d k`-measurable
direction `A`, a `filt d k`-measurable set `E` and `c : ℝ≥0` with `s² · vGue d n (A ω) ≤ c` on `E`,
the `E`-truncated variable `s · Re tr (A · seqXmat d n (ω (k+1)))` has a conditionally
sub-Gaussian mgf with parameter `c` given `filt d k`. -/
theorem gueHasCondSubgaussianMGF_linear (n k : ℕ) (s : ℝ)
    {A : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hA : Measurable[filt d k] A) (E : Set (PathΩ d)) (hE : MeasurableSet[filt d k] E) (c : ℝ≥0)
    (hbound : ∀ ω ∈ E, s ^ 2 * (vGue d n (A ω) : ℝ) ≤ c) :
    HasCondSubgaussianMGF (filt d k) ((filt d).le k)
      (fun ω => E.indicator (fun ω => s * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))) ω)
      c (Pgue d) := by
  classical
  have hc : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
  set A' : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
    fun ω => if ω ∈ E then A ω else 0 with hA'def
  have hA'meas : Measurable[filt d k] A' :=
    Measurable.ite (p := fun ω => ω ∈ E) hE hA measurable_const
  have hAs : ∀ ω, s ^ 2 * (vGue d n (A' ω) : ℝ) ≤ c := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hA'def, hω] using hbound ω hω
    · simp only [hA'def, hω, ite_false, Markov_vGue_zero, NNReal.coe_zero, mul_zero]
      exact hc
  have hXeq : (fun ω => E.indicator
      (fun ω => s * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))) ω)
      = fun ω => s * linTr n (A' ω) (Sizes.seqXmat d n (ω (k + 1))) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp [Set.indicator, hω, hA'def]
    · simp [Set.indicator, hω, hA'def, Markov_linTr_zero]
  rw [hXeq]
  change Kernel.HasSubgaussianMGF (fun ω => s * linTr n (A' ω) (Sizes.seqXmat d n (ω (k + 1))))
    c (condExpKernel (Pgue d) (filt d k)) ((Pgue d).trim ((filt d).le k))
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro r
    rw [condExpKernel_comp_trim ((filt d).le k)]
    exact Markov_integrable_exp_mul_X hA'meas hc hAs r
  · intro q
    exact Markov_cond_mgf_le hA'meas hc hAs (q : ℝ)

/-! ### `gue_highProb_incr_le`: the entrywise truncation event -/

section Truncation

/-- If every raw coordinate of `y` is `≤ t` in absolute value, every entry of `Xmat L W y` is `≤ 2t`
in norm (triangle inequality on the two coordinates `Xentry` reads; the diagonal case needs only
one of them, plus `t ≥ 0` from the other). -/
private theorem Markov_norm_Xentry_le {L W : ℕ} [NeZero L] [NeZero W] (y : Ω L W)
    (i j : Idx L W) {t : ℝ} (h : ∀ c : Coord L W, |y c| ≤ t) : ‖Xentry L W y i j‖ ≤ 2 * t := by
  unfold Xentry
  split_ifs with h1 h2
  · calc ‖(y (i, j, true) : ℂ) + Complex.I * (y (i, j, false) : ℂ)‖
        ≤ ‖(y (i, j, true) : ℂ)‖ + ‖Complex.I * (y (i, j, false) : ℂ)‖ := norm_add_le _ _
      _ = |y (i, j, true)| + |y (i, j, false)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _) (h _)
      _ = 2 * t := by ring
  · calc ‖(y (j, i, true) : ℂ) - Complex.I * (y (j, i, false) : ℂ)‖
        ≤ ‖(y (j, i, true) : ℂ)‖ + ‖Complex.I * (y (j, i, false) : ℂ)‖ := norm_sub_le _ _
      _ = |y (j, i, true)| + |y (j, i, false)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _) (h _)
      _ = 2 * t := by ring
  · have h1 := h (i, j, true)
    have h2 := h (i, j, false)
    have ht0 : (0 : ℝ) ≤ t := (abs_nonneg _).trans h2
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

end Truncation

/-! ### The Gaussian tail bound and the exponential-beats-polynomial fact -/

section Tail

private theorem Markov_hasSubgaussianMGF_id (v : ℝ≥0) :
    HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    have hlaw : HasLaw (fun x : ℝ => x) (gaussianReal 0 v) (gaussianReal (0 : ℝ) v) :=
      ⟨measurable_id.aemeasurable, by
        rw [show (fun x : ℝ => x) = id from rfl]; exact Measure.map_id⟩
    rw [mgf_gaussianReal hlaw]
    simp

/-- The two-sided Gaussian tail bound: for a centred Gaussian of variance `v ≤ 1`, the probability
of exceeding `t ≥ 0` in absolute value is `≤ 2 exp(-t²/2)`. -/
private theorem Markov_gaussian_tail_le {v : ℝ≥0} (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v) {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by
  have hsub : HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) :=
    Markov_hasSubgaussianMGF_id v
  have hexple : Real.exp (-(t ^ 2) / (2 * (v : ℝ))) ≤ Real.exp (-(t ^ 2) / 2) := by
    apply Real.exp_le_exp.2
    have hden : (0 : ℝ) < 2 * (v : ℝ) := by positivity
    have hle : (2 : ℝ) * (v : ℝ) ≤ 2 := by linarith
    have hkey : t ^ 2 / 2 ≤ t ^ 2 / (2 * (v : ℝ)) :=
      div_le_div_of_nonneg_left (sq_nonneg t) hden hle
    rw [neg_div, neg_div]
    linarith
  have h1 : (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
    hsub.measure_ge_le ht
  have h2 : (gaussianReal 0 v).real {x : ℝ | t ≤ -x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) := by
    have h2' := hsub.neg.measure_ge_le ht
    simpa using h2'
  have hsub' : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases le_total 0 x with hx0 | hx0
    · have heq : |x| = x := abs_of_nonneg hx0
      exact Or.inl (le_of_lt (heq ▸ hx))
    · have heq : |x| = -x := abs_of_nonpos hx0
      exact Or.inr (le_of_lt (heq ▸ hx))
  have hreal : (gaussianReal 0 v).real {x : ℝ | t < |x|} ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
    calc (gaussianReal 0 v).real {x : ℝ | t < |x|}
        ≤ (gaussianReal 0 v).real ({x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x}) :=
          measureReal_mono hsub'
      _ ≤ (gaussianReal 0 v).real {x : ℝ | t ≤ x} + (gaussianReal 0 v).real {x : ℝ | t ≤ -x} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) + Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
          add_le_add h1 h2
      _ ≤ Real.exp (-(t ^ 2) / 2) + Real.exp (-(t ^ 2) / 2) := add_le_add hexple hexple
      _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring
  calc (gaussianReal 0 v) {x : ℝ | t < |x|}
      = ENNReal.ofReal ((gaussianReal 0 v).real {x : ℝ | t < |x|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := ENNReal.ofReal_le_ofReal hreal

/-- The Gaussian tail `2 exp(-S²/8)` beats every polynomial `S^{-D'}`. -/
private theorem Markov_eventually_exp_beats_rpow (D' : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.exp (-((N : ℝ) ^ 2) / 8) ≤ (N : ℝ) ^ (-D') := by
  have hz : Filter.Tendsto (fun u : ℝ => u ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * u)) atTop
      (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D' / 2 + 1) (1 / 8) (by norm_num)
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ (2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hN : Filter.Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcomp : Filter.Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ))) atTop
      (nhds 0) := hz.comp (hsq.comp hN)
  have hev : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ)) < 1 :=
    hcomp.eventually (eventually_lt_nhds one_pos)
  filter_upwards [hev, eventually_ge_atTop 2] with N hev hN2
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hrpoweq : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hpoweq : ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) = (N : ℝ) ^ (D' + 2) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hexpeq : -(1 / 8 : ℝ) * (N : ℝ) ^ (2 : ℝ) = -((N : ℝ) ^ 2) / 8 := by
    rw [hrpoweq]; ring
  rw [hpoweq, hexpeq] at hev
  have hDpos : (0 : ℝ) < (N : ℝ) ^ D' := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ (D' + 2) = (N : ℝ) ^ D' * (N : ℝ) ^ (2 : ℕ) := by
    rw [← hrpoweq, Real.rpow_add hN0]
  rw [hsplit] at hev
  have hN2R : (2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hnn : (0 : ℝ) ≤ Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D' :=
    mul_nonneg (Real.exp_pos _).le hDpos.le
  have hfinal : 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D')
      ≤ (N : ℝ) ^ 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D') :=
    mul_le_mul_of_nonneg_right hN2R hnn
  rw [Real.rpow_neg (Nat.cast_nonneg N), inv_eq_one_div, le_div_iff₀ hDpos]
  nlinarith [hfinal, hev]

end Tail

/-! ### The cardinality of the (step, coordinate) index set is polynomial in `d.size n` -/

section Cardinality

private theorem Markov_card_Idx (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Idx, Z2, ZMod.card, Sizes.size, pow_two]

private theorem Markov_card_coordFinset (n : ℕ) :
    (coordFinset (d := d) n).card = d.size n * (d.size n * 2) := by
  change (Finset.univ.map (Function.Embedding.sigmaMk n)).card = _
  rw [Finset.card_map, Finset.card_univ]
  change Fintype.card (Idx (d.L n) (d.W n) × (Idx (d.L n) (d.W n) × Bool)) = _
  rw [Fintype.card_prod (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n) × Bool),
    Fintype.card_prod (Idx (d.L n) (d.W n)) Bool, Fintype.card_bool, Markov_card_Idx]

private theorem Markov_card_K (n0 n : ℕ) :
    Fintype.card (Fin (gueGridK d n0 n) × ↥(coordFinset (d := d) n))
      = (d.size n + 1) ^ (32 * n0 + 64) * (d.size n * (d.size n * 2)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Markov_card_coordFinset]
  rfl

/-- Pure arithmetic: for `S ≥ 2^(32 n₀ + 65)`, `(S+1)^(32 n₀+64) · (2 S²) ≤ S^(32 n₀ + 68)`. -/
private theorem Markov_card_arith (n0 S : ℕ) (hSbig : 2 ^ (32 * n0 + 65) ≤ S) :
    (((S + 1) ^ (32 * n0 + 64) * (S * (S * 2)) : ℕ) : ℝ) ≤ (S : ℝ) ^ (32 * n0 + 68) := by
  have hS1 : 1 ≤ S := le_trans (Nat.one_le_two_pow) hSbig
  have hS1R : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  have h2S : (S : ℝ) + 1 ≤ 2 * S := by linarith
  have hpow2 : (2 * (S : ℝ)) ^ (32 * n0 + 64)
      = (2 : ℝ) ^ (32 * n0 + 64) * (S : ℝ) ^ (32 * n0 + 64) := mul_pow 2 (S : ℝ) _
  have hbig : (2 : ℝ) ^ (32 * n0 + 65) ≤ (S : ℝ) := by
    have : ((2 ^ (32 * n0 + 65) : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSbig
    rwa [Nat.cast_pow, Nat.cast_ofNat] at this
  have hstep : ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2))
      ≤ (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := by
    calc ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2))
        ≤ (2 * (S : ℝ)) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by
          gcongr
      _ = (2 : ℝ) ^ (32 * n0 + 64) * (S : ℝ) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by
          rw [hpow2]
      _ = (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := by ring
  have hfinal : (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) ≤ (S : ℝ) ^ (32 * n0 + 68) := by
    have hS66 : (0 : ℝ) ≤ (S : ℝ) ^ (32 * n0 + 66) := by positivity
    calc (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66)
        ≤ (S : ℝ) * (S : ℝ) ^ (32 * n0 + 66) := mul_le_mul_of_nonneg_right hbig hS66
      _ = (S : ℝ) ^ (32 * n0 + 67) := by ring
      _ ≤ (S : ℝ) ^ (32 * n0 + 68) := pow_le_pow_right₀ hS1R (by omega)
  calc (((S + 1) ^ (32 * n0 + 64) * (S * (S * 2)) : ℕ) : ℝ)
      = ((S : ℝ) + 1) ^ (32 * n0 + 64) * ((S : ℝ) * ((S : ℝ) * 2)) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (32 * n0 + 65) * (S : ℝ) ^ (32 * n0 + 66) := hstep
    _ ≤ (S : ℝ) ^ (32 * n0 + 68) := hfinal

private theorem Markov_eventually_cardK_le (hsize : Tendsto (fun n => d.size n) atTop atTop)
    (n0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Fin (gueGridK d n0 n) × ↥(coordFinset (d := d) n)) : ℝ)
        ≤ ((d.size n : ℕ) : ℝ) ^ ((32 * n0 + 68 : ℕ) : ℝ) := by
  filter_upwards [hsize.eventually (eventually_ge_atTop (2 ^ (32 * n0 + 65)))] with n hbig
  rw [Real.rpow_natCast, Markov_card_K]
  exact Markov_card_arith n0 (d.size n) hbig

end Cardinality

/-! ### `gue_highProb_incr_le` -/

section IncrTruncation

private theorem Markov_unitVar_pos (c : Sizes.SeqCoord d) : 0 < (gueUnitVar d c : ℝ) := by
  unfold gueUnitVar; split_ifs <;> norm_num

private theorem Markov_unitVar_le_one (c : Sizes.SeqCoord d) : (gueUnitVar d c : ℝ) ≤ 1 := by
  unfold gueUnitVar; split_ifs <;> norm_num

/-- **The entrywise truncation event of the unit GUE increments**.  With high probability on the
matrix
dimension `d.size n`, every entry of every GUE increment `seqXmat d n (ω k)`,
`1 ≤ k ≤ gueGridK d n0 n`, is at most `d.size n` in norm. -/
theorem gue_highProb_incr_le (n0 : ℕ) (hsize : Tendsto (fun n => d.size n) atTop atTop) :
    HighProbAt (Pgue d) d.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK d n0 n →
      ∀ i j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n (ω k) i j‖ ≤ ((d.size n : ℕ) : ℝ)}) := by
  classical
  set K : ℕ → Type := fun n => Fin (gueGridK d n0 n) × ↥(coordFinset (d := d) n) with hKdef
  set Ξ : ∀ n, K n → Set (PathΩ d) :=
    fun n p => {ω | |ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord d)| ≤ ((d.size n : ℕ) : ℝ) / 2}
    with hΞdef
  have hmeas : ∀ n (p : K n),
      Measurable (fun ω : PathΩ d => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord d)) :=
    fun n p => (measurable_pi_apply (p.2 : Sizes.SeqCoord d)).comp
      (measurable_pi_apply (p.1.1 + 1))
  have hcompl : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ p : K n,
      (Pgue d) (Ξ n p)ᶜ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
    intro D _
    filter_upwards [hsize.eventually (Markov_eventually_exp_beats_rpow D)] with n hn p
    have hms : MeasurableSet {y : ℝ | ((d.size n : ℕ) : ℝ) / 2 < |y|} :=
      measurableSet_lt measurable_const measurable_norm
    have heq : (Ξ n p)ᶜ = (fun ω : PathΩ d => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord d)) ⁻¹'
        {y : ℝ | ((d.size n : ℕ) : ℝ) / 2 < |y|} := by
      ext ω; simp [hΞdef, not_le]
    rw [heq, ← Measure.map_apply (hmeas n p) hms]
    have hmapeq : (Pgue d).map (fun ω : PathΩ d => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord d))
        = gaussianReal 0 (gueUnitVar d (p.2 : Sizes.SeqCoord d)) := by
      rw [show (fun ω : PathΩ d => ω (p.1.1 + 1) (p.2 : Sizes.SeqCoord d))
          = (fun y : Sizes.SeqΩ d => y (p.2 : Sizes.SeqCoord d)) ∘
            (fun ω : PathΩ d => ω (p.1.1 + 1)) from rfl,
        ← Measure.map_map (measurable_pi_apply (p.2 : Sizes.SeqCoord d))
          (measurable_pi_apply (p.1.1 + 1)),
        Markov_map_incr d p.1.1, Markov_unitMapEval d (p.2 : Sizes.SeqCoord d)]
    rw [hmapeq]
    have htail := Markov_gaussian_tail_le (Markov_unitVar_pos d (p.2 : Sizes.SeqCoord d))
      (Markov_unitVar_le_one d (p.2 : Sizes.SeqCoord d))
      (show (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) / 2 by positivity)
    have hEq : -((((d.size n : ℕ) : ℝ) / 2) ^ 2) / 2 = -(((d.size n : ℕ) : ℝ) ^ 2) / 8 := by ring
    rw [hEq] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal hn)
  have hsub : ∀ n, (⋂ p : K n, Ξ n p) ⊆ {ω | ∀ k, 1 ≤ k → k ≤ gueGridK d n0 n →
      ∀ i j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n (ω k) i j‖ ≤ ((d.size n : ℕ) : ℝ)} := by
    intro n ω hω k hk1 hkK i j
    simp only [Set.mem_iInter] at hω
    have hbound : ∀ c : Coord (d.L n) (d.W n),
        |Sizes.slice d n (ω k) c| ≤ ((d.size n : ℕ) : ℝ) / 2 := by
      intro c
      have hmem : (⟨n, c⟩ : Sizes.SeqCoord d) ∈ coordFinset (d := d) n := by
        unfold coordFinset
        exact Finset.mem_map.2 ⟨c, Finset.mem_univ _, rfl⟩
      have hkey := hω (⟨⟨k - 1, by omega⟩, ⟨⟨n, c⟩, hmem⟩⟩ : K n)
      simp only [hΞdef, Set.mem_ofPred_eq] at hkey
      have heqk : k - 1 + 1 = k := by omega
      rw [heqk] at hkey
      exact hkey
    have hle := Markov_norm_Xentry_le (Sizes.slice d n (ω k)) i j hbound
    unfold Sizes.seqXmat
    rw [Xmat_apply]
    calc ‖Xentry (d.L n) (d.W n) (Sizes.slice d n (ω k)) i j‖
        ≤ 2 * (((d.size n : ℕ) : ℝ) / 2) := hle
      _ = ((d.size n : ℕ) : ℝ) := by ring
  have hI := highProbAt_iInter (Pgue d) d.size (K := K) (Ξ := Ξ)
    (C := ((32 * n0 + 68 : ℕ) : ℝ)) (Nat.cast_nonneg _) (Markov_eventually_cardK_le d hsize n0)
    hcompl
  intro D hD
  filter_upwards [hI D hD] with n hn
  exact le_trans (measure_mono (Set.compl_subset_compl.2 (hsub n))) hn

end IncrTruncation

end RBM.Univ.GUEPhase

end
