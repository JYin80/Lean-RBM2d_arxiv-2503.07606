/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Walk
import RBM2D.Gauss.LinearForm
import Mathlib.Probability.Moments.SubGaussian

/-!
# The discrete grid Markov property: freezing and conditional sub-Gaussian linear forms

Conditioning a function of a `filt d k`-measurable coefficient and the independent next draw
`ω (k+1)` on `filt d k` freezes the coefficient and averages the draw against its own law
`Sizes.seqP d` (`condExp_freeze`).  For a direction `A`, the linear form
`Re tr (A · seqXmat d n (ω (k+1)))` is then a conditionally centred Gaussian, which gives a
conditional sub-Gaussian mgf with the deterministic parameter `c` of a bound
`gridStep · linTrVar ≤ c` (`hasCondSubgaussianMGF_linear`).

The coordinate set `coordFinset n` is the whole fibre `{⟨n, c⟩}` over the size index `n`.  The
coordinates of that fibre that `Xentry` never reads (`(i, j, b)` with `idxKey j < idxKey i`, and
`(i, i, false)`) have coefficient `linTr n A 0 = 0` in `linTr_seqXmat_eq_sum`, so they add `0`
to `linTrVar`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm
open scoped NNReal ENNReal MeasureTheory

variable (d : Sizes)

/-! ### The freezing lemma -/

section Freeze

variable {d}

/-- **The freezing lemma**.  For `k`, a
`filt d k`-measurable `Y : PathΩ d → β` and a jointly measurable `F : β → Sizes.SeqΩ d → ℝ`
with `F (Y ·) (· (k+1))` integrable, conditioning on `filt d k` freezes `Y` and averages the
independent next draw `ω (k+1)` against its own law `Sizes.seqP d`. -/
theorem condExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (pathP d)) :
    (pathP d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[pathP d] fun ω => ∫ x, F (Y ω) x ∂(Sizes.seqP d) := by
  classical
  set μ : Measure (PathΩ d) := pathP d with hμdef
  set Z : PathΩ d → Sizes.SeqΩ d := fun ω => ω (k + 1) with hZdef
  set Φ : PathΩ d → β × Sizes.SeqΩ d := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Sizes.SeqΩ d) := Sizes.seqP d with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((filt d).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := map_incr d k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt d k := hY.comap_le
    exact (indep_of_indep_of_le_right (indep_incr d k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Sizes.SeqΩ d => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  -- the key set-wise identity, for every `A ∈ filt d k`
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
        (indep_incr d k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
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

/-! ### The conditional Gaussian MGF of a fixed-direction linear functional -/

section LinearFunctional

variable {d}

/-- The real-linear pairing `Re(trace(A*X))`. -/
def linTr (n : ℕ) (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) : ℝ :=
  (Matrix.trace (A * X)).re

/-- The finite set of sequence coordinates `⟨n, c⟩` over the size index `n`; it contains every
coordinate that `Sizes.seqXmat d n` reads. -/
def coordFinset (n : ℕ) : Finset (Sizes.SeqCoord d) :=
  Finset.univ.map (Function.Embedding.sigmaMk (β := fun m => Coord (d.L m) (d.W m)) n)

private theorem mem_coordFinset (n : ℕ) (c : Sizes.SeqCoord d) :
    c ∈ coordFinset n ↔ c.1 = n := by
  obtain ⟨c1, c2⟩ := c
  unfold coordFinset
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p, -, hp⟩
    exact (congrArg Sigma.fst hp).symm
  · intro h
    simp only at h
    subst h
    exact ⟨c2, Finset.mem_univ _, rfl⟩

private theorem linTr_add (n : ℕ) (A X Y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n A (X + Y) = linTr n A X + linTr n A Y := by
  unfold linTr
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

private theorem linTr_smul (n : ℕ) (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (a : ℝ) : linTr n A ((a : ℂ) • X) = a * linTr n A X := by
  unfold linTr
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

private theorem seqXmat_add' (n : ℕ) (y₁ y₂ : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (y₁ + y₂) = Sizes.seqXmat d n y₁ + Sizes.seqXmat d n y₂ :=
  Xmat_add (d.L n) (d.W n) (Sizes.slice d n y₁) (Sizes.slice d n y₂)

private theorem seqXmat_smul' (n : ℕ) (a : ℝ) (y : Sizes.SeqΩ d) :
    Sizes.seqXmat d n (a • y) = (a : ℂ) • Sizes.seqXmat d n y := by
  have h := Xmat_smul (d.L n) (d.W n) a (Sizes.slice d n y)
  change Xmat (d.L n) (d.W n) (a • Sizes.slice d n y) = _
  rw [h]
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rfl

/-- `Sizes.seqXmat d n` reads only the coordinates in `coordFinset n`. -/
private theorem seqXmat_congr (n : ℕ) {y y' : Sizes.SeqΩ d}
    (h : ∀ c ∈ coordFinset n, y c = y' c) :
    Sizes.seqXmat d n y = Sizes.seqXmat d n y' := by
  unfold Sizes.seqXmat
  congr 1
  funext c
  exact h ⟨n, c⟩ ((mem_coordFinset n _).2 rfl)

private theorem seqXmat_zero' (n : ℕ) : Sizes.seqXmat d n (0 : Sizes.SeqΩ d) = 0 := by
  have h := Xmat_smul (d.L n) (d.W n) 0 (0 : Coord (d.L n) (d.W n) → ℝ)
  simp only [zero_smul] at h
  exact h

private theorem seqXmat_sum' (n : ℕ) (S : Finset (Sizes.SeqCoord d))
    (y : Sizes.SeqCoord d → ℝ) :
    Sizes.seqXmat d n (∑ c ∈ S, y c • Pi.single c 1)
      = ∑ c ∈ S, (y c : ℂ) • Sizes.seqXmat d n (Pi.single c 1) := by
  classical
  induction S using Finset.induction with
  | empty => simp [seqXmat_zero']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, seqXmat_add', ih, seqXmat_smul']

private theorem linTr_sum (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (S : Finset (Sizes.SeqCoord d)) (y : Sizes.SeqCoord d → ℝ)
    (M : Sizes.SeqCoord d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n A (∑ c ∈ S, (y c : ℂ) • M c) = ∑ c ∈ S, y c * linTr n A (M c) := by
  classical
  induction S using Finset.induction with
  | empty => simp [linTr]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, linTr_add, ih, linTr_smul]

/-- The coordinatewise decomposition of `y` into the coordinates of `coordFinset n`. -/
private theorem sum_single_agree (n : ℕ) (y : Sizes.SeqΩ d) {c : Sizes.SeqCoord d}
    (hc : c ∈ coordFinset n) :
    (∑ c' ∈ coordFinset n, y c' • Pi.single c' 1 : Sizes.SeqΩ d) c = y c := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, hc, ite_true]

/-- **The linear decomposition**.
`linTr n A (seqXmat d n y)` is the finite real-linear form in the coordinates of `coordFinset n`,
with coefficients the values of `linTr n A ∘ seqXmat d n` at the standard basis vectors (`0` at
the coordinates that `Xentry` does not read). -/
theorem linTr_seqXmat_eq_sum (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
    (y : Sizes.SeqΩ d) :
    linTr n A (Sizes.seqXmat d n y)
      = ∑ c ∈ coordFinset n, y c * linTr n A (Sizes.seqXmat d n (Pi.single c 1)) := by
  classical
  have hagree : ∀ c ∈ coordFinset n,
      y c = (∑ c' ∈ coordFinset n, y c' • Pi.single c' 1 : Sizes.SeqΩ d) c :=
    fun c hc => (sum_single_agree n y hc).symm
  rw [seqXmat_congr n hagree, seqXmat_sum', linTr_sum]

/-- **The conditional variance of a fixed-direction linear functional** at size index `n`, in the
direction `A`: the sum over `coordFinset n` of the
coordinate variance `Sizes.seqGvar d c` times the squared coefficient of that coordinate in
`linTr n A ∘ seqXmat d n`. -/
def linTrVar (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) : ℝ :=
  linVar (Sizes.seqGvar d) (fun c => linTr n A (Sizes.seqXmat d n (Pi.single c 1)))
    (coordFinset n)

theorem linTrVar_nonneg (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    0 ≤ linTrVar n A := by
  unfold linTrVar linVar
  positivity

/-- **The law of a fixed-direction linear functional**.  For a fixed matrix `A`,
`y ↦ linTr n A (seqXmat d n y)` is, under
`Sizes.seqP d`, a centred Gaussian of variance `linTrVar n A`. -/
theorem map_linTr_seqXmat (n : ℕ) (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    (Sizes.seqP d).map (fun y => linTr n A (Sizes.seqXmat d n y))
      = gaussianReal 0 (NNReal.mk (linTrVar n A) (linTrVar_nonneg n A)) := by
  have hfun : (fun y : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n y))
      = fun y => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) * y c := by
    funext y
    rw [linTr_seqXmat_eq_sum]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfun, map_sum_const_mul_coord d
    (fun c => linTr n A (Sizes.seqXmat d n (Pi.single c 1))) (coordFinset n)]
  rfl

private theorem measurable_seqXmat' (n : ℕ) : Measurable (Sizes.seqXmat d n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry (d.L n) (d.W n) i j).comp (Sizes.measurable_slice d n)

/-- `Re(trace(M*X)) = ∑ i, ∑ k, Re(M i k * X k i)`. -/
private theorem linTr_eq_sum (n : ℕ) (A X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n A X = ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n), (A i k * X k i).re := by
  unfold linTr
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem measurable_linTr_uncurry (n : ℕ) :
    Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
      linTr n p.1 (Sizes.seqXmat d n p.2)) := by
  have heq : (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
      linTr n p.1 (Sizes.seqXmat d n p.2))
      = fun p => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n),
          (p.1 i k * Sizes.seqXmat d n p.2 k i).re :=
    funext fun p => linTr_eq_sum n p.1 (Sizes.seqXmat d n p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        Sizes.seqXmat d n p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((measurable_seqXmat' n).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

/-- `linTr n A (seqXmat d n ·)` is measurable in the sample point, for a fixed direction `A`. -/
private theorem measurable_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Measurable (fun x : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n x)) := by
  have heq : (fun x : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n x))
      = fun x => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n),
          (A i k * Sizes.seqXmat d n x k i).re :=
    funext fun x => linTr_eq_sum n A (Sizes.seqXmat d n x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (measurable_seqXmat' n)))

/-- **The mean of a fixed-direction linear functional is zero**. -/
theorem integral_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    ∫ x, linTr n A (Sizes.seqXmat d n x) ∂(Sizes.seqP d) = 0 := by
  have h := integral_map (μ := Sizes.seqP d)
    (φ := fun x : Sizes.SeqΩ d => linTr n A (Sizes.seqXmat d n x))
    (f := fun y : ℝ => y) (measurable_linTr_seqXmat n A).aemeasurable
    stronglyMeasurable_id.aestronglyMeasurable
  rw [map_linTr_seqXmat] at h
  rw [← h, integral_id_gaussianReal]

private instance instStandardBorelSpaceMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ))

variable (s t : ℕ → ℝ) (K : ℕ → ℕ)

/-- **The conditional mean of a fixed-direction linear functional is zero**.  For a
`filt d k`-measurable direction `A`, a `filt d k`-measurable set `E`, and integrability of the
un-truncated linear functional, the conditional expectation of the `E`-truncated variable is `0`
a.e. -/
theorem condExp_linear_eq_zero (n k : ℕ)
    {A : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hA : Measurable[filt d k] A) (E : Set (PathΩ d)) (hE : MeasurableSet[filt d k] E)
    (hIntG : Integrable
      (fun ω => Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1))))
      (pathP d)) :
    (pathP d)[fun ω => E.indicator
        (fun ω => Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1))))
        ω | filt d k]
      =ᵐ[pathP d] (fun _ => (0 : ℝ)) := by
  set G : PathΩ d → ℝ :=
    fun ω => Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))
    with hGdef
  set F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℝ :=
    fun p x => Real.sqrt (gridStep s t K n) * linTr n p (Sizes.seqXmat d n x) with hFdef
  have hF : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        F p.1 p.2) :=
    (measurable_linTr_uncurry n).const_mul _
  have hIntG' : Integrable (fun ω => F (A ω) (ω (k + 1))) (pathP d) := hIntG
  have hfreeze := condExp_freeze k hA hF hIntG'
  have hzero : (fun ω : PathΩ d => ∫ x, F (A ω) x ∂(Sizes.seqP d)) = fun _ => (0 : ℝ) := by
    funext ω
    change ∫ x, Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat d n x)
      ∂(Sizes.seqP d) = 0
    rw [integral_const_mul, integral_linTr_seqXmat, mul_zero]
  rw [hzero] at hfreeze
  have hFG : (fun ω : PathΩ d => F (A ω) (ω (k + 1))) = G := by
    funext ω; rw [hFdef, hGdef]
  rw [hFG] at hfreeze
  have hEmeas : MeasurableSet E := (filt d).le k E hE
  have hcondEq : (pathP d)[fun ω => E.indicator (fun ω => G ω) ω | filt d k]
      =ᵐ[pathP d] (Set.indicator E (fun _ => (1 : ℝ))) * (pathP d)[G | filt d k] := by
    have heq : (fun ω => E.indicator (fun ω => G ω) ω)
        = (Set.indicator E (fun _ => (1 : ℝ))) * G := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
    rw [heq]
    refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
    · exact (stronglyMeasurable_const.indicator hE)
    · rw [← heq]; exact hIntG.indicator hEmeas
    · exact hIntG
  refine hcondEq.trans ?_
  filter_upwards [hfreeze] with ω hω
  simp only [Pi.mul_apply, hω, mul_zero]

/-! ### The conditional Gaussian MGF of a fixed-direction linear functional -/

/-- `linTr` vanishes at the zero direction. -/
private theorem linTr_zero (n : ℕ) (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n 0 X = 0 := by
  unfold linTr; simp

/-- The conditional variance vanishes at the zero direction. -/
private theorem linTrVar_zero (n : ℕ) :
    linTrVar n (0 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) = 0 := by
  unfold linTrVar linVar; simp [linTr_zero]

/-- `linTr n A M` is measurable in the direction `A`, for a fixed matrix `M`. -/
private theorem measurable_linTr_left (n : ℕ)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    Measurable (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTr n A M) := by
  have heq : (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTr n A M)
      = fun A => ∑ i : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n), (A i k * M k i).re :=
    funext fun A => linTr_eq_sum n A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

/-- The real-valued formula for `linTrVar`, unfolding the `ℝ≥0`-valued `linVar`. -/
private theorem linTrVar_eq_sum (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTrVar n A = ∑ c ∈ coordFinset n,
      (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) ^ 2 * (Sizes.seqGvar d c : ℝ) := by
  unfold linTrVar linVar
  push_cast [NNReal.coe_mk]
  rfl

/-- `linTrVar` is measurable in the direction argument. -/
private theorem measurable_linTrVar (n : ℕ) :
    Measurable (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTrVar n A) := by
  have heq : (fun A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTrVar n A)
      = fun A => ∑ c ∈ coordFinset n,
          (linTr n A (Sizes.seqXmat d n (Pi.single c 1))) ^ 2 * (Sizes.seqGvar d c : ℝ) :=
    funext (linTrVar_eq_sum n)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ => ((measurable_linTr_left n _).pow_const 2).mul_const _

/-- **The mgf of the fixed-direction linear functional**: the Gaussian mgf. -/
private theorem mgf_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (r : ℝ) :
    mgf (fun x => linTr n A (Sizes.seqXmat d n x)) (Sizes.seqP d) r
      = Real.exp (linTrVar n A * r ^ 2 / 2) := by
  have hlaw : HasLaw (fun x => linTr n A (Sizes.seqXmat d n x))
      (gaussianReal 0 (NNReal.mk (linTrVar n A) (linTrVar_nonneg n A))) (Sizes.seqP d) :=
    ⟨(measurable_linTr_seqXmat n A).aemeasurable, map_linTr_seqXmat n A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  push_cast [NNReal.coe_mk]
  ring

/-- `exp (r · linTr n A (seqXmat d n ·))` is integrable, for a fixed direction `A`. -/
private theorem integrable_exp_linTr_seqXmat (n : ℕ)
    (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * linTr n A (Sizes.seqXmat d n x))) (Sizes.seqP d) := by
  have h : Integrable (fun x : ℝ => Real.exp (r * x))
      ((Sizes.seqP d).map (fun x => linTr n A (Sizes.seqXmat d n x))) := by
    rw [map_linTr_seqXmat n A]; exact integrable_exp_mul_gaussianReal r
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_linTr_seqXmat n A).aemeasurable).1 h

section MGFBound

variable {n k : ℕ} {A : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}

/-- **The unconditional integrability of `exp (r · X)`** for the fixed-direction linear functional
`X ω = √Δ · linTr n (A ω) (seqXmat d n (ω (k+1)))`, given `(√Δ)² · linTrVar n (A ω) ≤ c` for every
`ω`.  Tonelli (`RBM.Gauss.LinearForm.lintegral_indep_pair`) across the independent pair
`(ω (k+1), A ω)`: the inner integral is the Gaussian mgf `exp (linTrVar n (A ω) · (r√Δ)² / 2)`,
bounded by `exp (c r² / 2)`. -/
private theorem integrable_exp_mul_X (hA : Measurable[filt d k] A) {Δ c : ℝ} (hc : 0 ≤ c)
    (hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * linTrVar n (A ω) ≤ c) (r : ℝ) :
    Integrable (fun ω : PathΩ d =>
      Real.exp (r * (Real.sqrt Δ * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))) (pathP d) := by
  classical
  set U : PathΩ d → Sizes.SeqΩ d := fun ω => ω (k + 1) with hUdef
  set F : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp ((r * Real.sqrt Δ) * linTr n p.2 (Sizes.seqXmat d n p.1)))
    with hFdef
  have hUmeas : Measurable U := measurable_pi_apply (k + 1)
  have hAmeas : Measurable A := hA.mono ((filt d).le k) le_rfl
  have hindep : IndepFun U A (pathP d) := by
    have hcle : MeasurableSpace.comap A inferInstance ≤ filt d k := hA.comap_le
    exact indep_of_indep_of_le_right (indep_incr d k) hcle
  have hFmeas : Measurable F := by
    have h0 : Measurable
        (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat d n p.1)) := by
      have heq : (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          linTr n p.2 (Sizes.seqXmat d n p.1))
          = fun p => ∑ i : Idx (d.L n) (d.W n), ∑ k' : Idx (d.L n) (d.W n),
              (p.2 i k' * Sizes.seqXmat d n p.1 k' i).re :=
        funext fun p => linTr_eq_sum n p.2 (Sizes.seqXmat d n p.1)
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
      have hM : Measurable
          (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            p.2 i k') :=
        Measurable.eval_matrix (i := i) (j := k') measurable_snd
      have hX : Measurable
          (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            Sizes.seqXmat d n p.1 k' i) :=
        Measurable.eval_matrix (i := k') (j := i) ((measurable_seqXmat' n).comp measurable_fst)
      exact Complex.measurable_re.comp (hM.mul hX)
    have h1 : Measurable
        (fun p : Sizes.SeqΩ d × Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
          (r * Real.sqrt Δ) * linTr n p.2 (Sizes.seqXmat d n p.1)) := h0.const_mul _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)
  have hkey := lintegral_indep_pair hUmeas hAmeas hindep hFmeas
  rw [map_incr d k] at hkey
  have hinner : ∀ y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ,
      (∫⁻ x, F (x, y) ∂ (Sizes.seqP d))
        = ENNReal.ofReal (Real.exp (linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2)) := by
    intro y
    have hint := integrable_exp_linTr_seqXmat n y (r * Real.sqrt Δ)
    have hofreal := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hmgf := mgf_linTr_seqXmat n y (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [hFdef]
    dsimp only
    rw [← hofreal, hmgf]
  have hp : MeasurableSet {y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ |
      linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2} :=
    measurableSet_le (((measurable_linTrVar n).mul_const _).div_const _) measurable_const
  have hptwise : ∀ ω, linTrVar n (A ω) * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    intro ω
    have h2 := hAle2 ω
    nlinarith [sq_nonneg r]
  have hae : ∀ᵐ y ∂ (pathP d).map A, linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    rw [ae_map_iff hAmeas.aemeasurable hp]
    exact Filter.Eventually.of_forall hptwise
  have houter_eq : ∫⁻ ω, F (U ω, A ω) ∂ (pathP d)
      = ∫⁻ y, ENNReal.ofReal (Real.exp (linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2))
          ∂ ((pathP d).map A) := by
    rw [hkey]; exact lintegral_congr hinner
  have houter_le : ∫⁻ ω, F (U ω, A ω) ∂ (pathP d) ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
    rw [houter_eq]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp (linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2))
          ∂ ((pathP d).map A)
        ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) ∂ ((pathP d).map A) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hy)
      _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((pathP d).map A) Set.univ := by
          rw [lintegral_const]
      _ ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
          calc ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((pathP d).map A) Set.univ
              ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * 1 := by
                gcongr
                exact prob_le_one
            _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := mul_one _
  refine ⟨?_, ?_⟩
  · have hXmeas : Measurable (fun ω : PathΩ d =>
        Real.exp (r * (Real.sqrt Δ * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))) := by
      have h1 : Measurable
          (fun ω : PathΩ d => linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))) := by
        have heq : (fun ω : PathΩ d => linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1))))
            = fun ω => ∑ i : Idx (d.L n) (d.W n), ∑ k' : Idx (d.L n) (d.W n),
              (A ω i k' * Sizes.seqXmat d n (ω (k + 1)) k' i).re :=
          funext fun ω => linTr_eq_sum n (A ω) (Sizes.seqXmat d n (ω (k + 1)))
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
        have hM : Measurable (fun ω : PathΩ d => A ω i k') := Measurable.eval_matrix hAmeas
        have hX : Measurable (fun ω : PathΩ d => Sizes.seqXmat d n (ω (k + 1)) k' i) :=
          Measurable.eval_matrix ((measurable_seqXmat' n).comp hUmeas)
        exact Complex.measurable_re.comp (hM.mul hX)
      exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
    exact hXmeas.aestronglyMeasurable
  · rw [hasFiniteIntegral_def]
    have heq : ∀ ω,
        ‖Real.exp (r * (Real.sqrt Δ * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))))‖ₑ
          = F (U ω, A ω) := by
      intro ω
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFdef]
      dsimp only
      congr 2
      ring
    simp_rw [heq]
    exact lt_of_le_of_lt houter_le ENNReal.ofReal_lt_top

/-- **The a.e. conditional mgf bound.**  For a fixed real `r`, almost everywhere for the trimmed
measure, the mgf of the fixed-direction linear functional at `r` for the conditional expectation
kernel is at most `exp (c r² / 2)`: `condExp_freeze` identifies the conditional expectation of
`exp (r X)` with the Gaussian mgf, bridged to the kernel by
`condExp_ae_eq_trim_integral_condExpKernel`. -/
private theorem condMGF_le (hA : Measurable[filt d k] A) {Δ c : ℝ} (hc : 0 ≤ c)
    (hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * linTrVar n (A ω) ≤ c) (r : ℝ) :
    ∀ᵐ ω ∂ ((pathP d).trim ((filt d).le k)),
      mgf (fun ρ => Real.sqrt Δ * linTr n (A ρ) (Sizes.seqXmat d n (ρ (k + 1))))
        (condExpKernel (pathP d) (filt d k) ω) r ≤ Real.exp (c * r ^ 2 / 2) := by
  classical
  set X : PathΩ d → ℝ :=
    fun ρ => Real.sqrt Δ * linTr n (A ρ) (Sizes.seqXmat d n (ρ (k + 1))) with hXdef
  set Gr : PathΩ d → ℝ := fun ρ => Real.exp (r * X ρ) with hGrdef
  set Fr : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℝ :=
    fun y x => Real.exp (r * (Real.sqrt Δ * linTr n y (Sizes.seqXmat d n x))) with hFrdef
  have hFrmeas : Measurable
      (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
        Fr p.1 p.2) := by
    have h1 : Measurable
        (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ × Sizes.SeqΩ d =>
          linTr n p.1 (Sizes.seqXmat d n p.2)) := measurable_linTr_uncurry n
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : PathΩ d => Fr (A ρ) (ρ (k + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef, hXdef]
  have hIntGr : Integrable Gr (pathP d) := integrable_exp_mul_X hA hc hAle2 r
  have hfreeze := condExp_freeze k hA hFrmeas (hGreq ▸ hIntGr)
  have hRHS : (fun ρ : PathΩ d => ∫ x, Fr (A ρ) x ∂ (Sizes.seqP d))
      = fun ρ => Real.exp (linTrVar n (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    funext ρ
    have hmgf := mgf_linTr_seqXmat n (A ρ) (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * Real.sqrt Δ) * linTr n (A ρ) (Sizes.seqXmat d n x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  have hm : filt d k ≤ (inferInstance : MeasurableSpace (PathΩ d)) := (filt d).le k
  have hsm1 : StronglyMeasurable[filt d k] ((pathP d)[Gr | filt d k]) := stronglyMeasurable_condExp
  have hsm2 : StronglyMeasurable[filt d k]
      (fun ρ => Real.exp (linTrVar n (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2)) := by
    have hcont : Measurable (fun y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        Real.exp (linTrVar n y * (r * Real.sqrt Δ) ^ 2 / 2)) :=
      Real.measurable_exp.comp (((measurable_linTrVar n).mul_const _).div_const _)
    exact (hcont.comp hA).stronglyMeasurable
  have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
  have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
  have hcomb : ∀ᵐ ρ ∂ (pathP d).trim hm,
      (∫ σ, Gr σ ∂ condExpKernel (pathP d) (filt d k) ρ)
        = Real.exp (linTrVar n (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    filter_upwards [hbridge, htrim] with ρ h1 h2
    rw [← h1, h2]
  filter_upwards [hcomb] with ρ hρ
  change (∫ σ, Gr σ ∂ condExpKernel (pathP d) (filt d k) ρ) ≤ Real.exp (c * r ^ 2 / 2)
  rw [hρ]
  apply Real.exp_le_exp.2
  have h2 := hAle2 ρ
  nlinarith [sq_nonneg r]

end MGFBound

/-- **The conditional Gaussian MGF of a fixed-direction linear functional**.  For a
`filt d k`-measurable direction `A`, a `filt d k`-measurable set `E`, and `c ≥ 0` with
`gridStep s t K n · linTrVar n (A ω) ≤ c` for every `ω ∈ E`, the `E`-truncated fixed-direction
linear functional `√(gridStep s t K n) · linTr n (A ω) (seqXmat d n (ω (k+1)))` has a conditionally
sub-Gaussian mgf with parameter `c` given `filt d k`. -/
theorem hasCondSubgaussianMGF_linear (n k : ℕ)
    {A : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ}
    (hA : Measurable[filt d k] A) (E : Set (PathΩ d)) (hE : MeasurableSet[filt d k] E)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ ω ∈ E, gridStep s t K n * linTrVar n (A ω) ≤ c) :
    HasCondSubgaussianMGF (filt d k) ((filt d).le k)
      (fun ω => E.indicator
        (fun ω => Real.sqrt (gridStep s t K n) * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1))))
        ω)
      ⟨c, hc⟩ (pathP d) := by
  classical
  set Δ : ℝ := gridStep s t K n with hΔdef
  set A' : PathΩ d → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
    fun ω => if ω ∈ E then A ω else 0 with hA'def
  have hA'meas : Measurable[filt d k] A' :=
    Measurable.ite (p := fun ω => ω ∈ E) hE hA measurable_const
  have hAle : ∀ ω, Δ * linTrVar n (A' ω) ≤ c := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hA'def, hω] using hbound ω hω
    · simp only [hA'def, hω, ite_false, linTrVar_zero, mul_zero]
      exact hc
  have hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * linTrVar n (A' ω) ≤ c := by
    intro ω
    by_cases hΔ : 0 ≤ Δ
    · rw [Real.sq_sqrt hΔ]; exact hAle ω
    · rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hΔ).le]
      simpa using hc
  have hXeq : (fun ω => E.indicator
      (fun ω => Real.sqrt Δ * linTr n (A ω) (Sizes.seqXmat d n (ω (k + 1)))) ω)
      = fun ω => Real.sqrt Δ * linTr n (A' ω) (Sizes.seqXmat d n (ω (k + 1))) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp [Set.indicator, hω, hA'def]
    · simp [Set.indicator, hω, hA'def, linTr_zero]
  rw [hXeq]
  change Kernel.HasSubgaussianMGF
    (fun ω => Real.sqrt Δ * linTr n (A' ω) (Sizes.seqXmat d n (ω (k + 1))))
    ⟨c, hc⟩ (condExpKernel (pathP d) (filt d k)) ((pathP d).trim ((filt d).le k))
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro r
    rw [condExpKernel_comp_trim ((filt d).le k)]
    exact integrable_exp_mul_X hA'meas hc hAle2 r
  · intro q
    exact condMGF_le hA'meas hc hAle2 (q : ℝ)

end LinearFunctional

end RBM.Path

end
