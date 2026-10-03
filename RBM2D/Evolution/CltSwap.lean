/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Model

/-!
# The independent copy and the partial replacement on the finite Gaussian model

On the finite product model `RBM.Gauss.P L W` over the `2 N²` real coordinates of `Coord L W`
(`N = (W L)²`) this file gives

* the coordinate split `cltSplit S ω ω'` (coordinates in `S` from `ω'`, the others from `ω`) and
  the fact that `(ω, ω') ↦ cltSplit S ω ω'` pushes `P ⊗ P` to `P`
  (`measurePreserving_cltSplit`; pattern: `RBM.Green.measurePreserving_rowSplit`);
* the hybrids `cltHyb e k` and the telescoping sum `cltTelescope`;
* the one-coordinate exchange `cltSwap c` and the fact that it preserves `P ⊗ P`
  (`measurePreserving_cltSwap`), and its consequence that an antisymmetric integrand integrates
  to zero (`integral_eq_zero_of_cltSwap_neg`);
* the transfer `cltTransfer` from `Sizes.seqP d` to `P (d.L n) (d.W n)`.

The paper (arXiv:2503.07606) does not contain this argument; the i.i.d. copy `H'` is that of
(`clt-delta`), and the exchange replaces "The last line vanishes" of the proof of
(`clt-lemmafar`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory RBM RBM.Gauss
open scoped NNReal ENNReal

section Rep

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The coordinate-wise switch: coordinates in `S` from `ω'`, the others from `ω`.  With
`(ω, ω') ∼ P ⊗ P`, `ω'` is the paper's i.i.d. copy `H'` (`clt-lemmafar`). -/
def cltSplit (S : Finset (Coord L W)) (ω ω' : Ω L W) : Ω L W :=
  fun c => if c ∈ S then ω' c else ω c

/-- **The law of a hybrid** (paper: `H'` an i.i.d. copy, `clt-delta`).  For every
set of coordinates `S`, `(ω, ω') ↦ cltSplit S ω ω'` pushes `P ⊗ P` to `P`.  Pattern: the
`RBM.Green.measurePreserving_rowSplit` with its row predicate replaced by `S`. -/
def MeasurePreservingCltSplit : Prop :=
  ∀ S : Finset (Coord L W),
    MeasurePreserving (fun p : Ω L W × Ω L W => cltSplit L W S p.1 p.2)
      ((P L W).prod (P L W)) (P L W)

/-- The first `k` coordinates in the enumeration `e`. -/
def cltHybSet (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ) : Finset (Coord L W) :=
  Finset.univ.filter fun c => ((e c : ℕ) < k)

/-- The hybrid `T_k`: the first `k` coordinates (in the enumeration `e`) replaced by those of
`ω'`.  `T_0 = ω`, `T_{card} = ω'` (`cltHyb_zero`, `cltHyb_card`). -/
def cltHyb (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ) (ω ω' : Ω L W) : Ω L W :=
  cltSplit L W (cltHybSet L W e k) ω ω'

/-- **Telescoping** (`clt-telescope-general`, `clt-lemmatelescope`).  For
every `Φ : Ω → ℂ`, `Φ ω - Φ ω' = Σ_{k < card} (Φ T_k - Φ T_{k+1})`.  The paper sums over the
entries `i ≤ j`; here over the `card (Coord L W) = 2 N²` real coordinates.  Proved:
`cltTelescope`. -/
def CltTelescope : Prop :=
  ∀ (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (Φ : Ω L W → ℂ) (ω ω' : Ω L W),
    Φ ω - Φ ω' = ∑ k ∈ Finset.range (Fintype.card (Coord L W)),
      (Φ (cltHyb L W e k ω ω') - Φ (cltHyb L W e (k + 1) ω ω'))

theorem cltHyb_zero (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (ω ω' : Ω L W) :
    cltHyb L W e 0 ω ω' = ω := by
  funext c
  simp [cltHyb, cltSplit, cltHybSet]

theorem cltHyb_card (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (ω ω' : Ω L W) :
    cltHyb L W e (Fintype.card (Coord L W)) ω ω' = ω' := by
  funext c
  have hc := (e c).isLt
  simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and, hc,
    ite_true]

theorem cltTelescope : CltTelescope L W := by
  intro e Φ ω ω'
  rw [Finset.sum_range_sub' (fun k => Φ (cltHyb L W e k ω ω')), cltHyb_zero, cltHyb_card]

private theorem cltHyb_ne (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) {k : ℕ}
    (hk : k < Fintype.card (Coord L W)) {c : Coord L W} (h : c ≠ e.symm ⟨k, hk⟩) :
    (e c : ℕ) ≠ k := by
  intro h'
  apply h
  rw [Equiv.eq_symm_apply]
  exact Fin.ext h'

/-- `T_{k+1} = update T_k c_k (ω' c_k)` with `c_k = e.symm k` (the step `Δ` of `clt-delta`, for one
real coordinate). -/
theorem cltHyb_succ (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ)
    (hk : k < Fintype.card (Coord L W)) (ω ω' : Ω L W) :
    cltHyb L W e (k + 1) ω ω' =
      Function.update (cltHyb L W e k ω ω') (e.symm ⟨k, hk⟩) (ω' (e.symm ⟨k, hk⟩)) := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet]
  · have hne := cltHyb_ne L W e hk h
    rw [Function.update_of_ne h]
    simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- `T_k = update T_{k+1} c_k (ω c_k)`. -/
theorem cltHyb_eq_update_succ (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ)
    (hk : k < Fintype.card (Coord L W)) (ω ω' : Ω L W) :
    cltHyb L W e k ω ω' =
      Function.update (cltHyb L W e (k + 1) ω ω') (e.symm ⟨k, hk⟩) (ω (e.symm ⟨k, hk⟩)) := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet]
  · have hne := cltHyb_ne L W e hk h
    rw [Function.update_of_ne h]
    simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The one-coordinate exchange `σ_c(ω, ω') = (update ω c (ω' c), update ω' c (ω c))`. -/
def cltSwap (c : Coord L W) (p : Ω L W × Ω L W) : Ω L W × Ω L W :=
  (Function.update p.1 c (p.2 c), Function.update p.2 c (p.1 c))

/-- **The exchange preserves `P ⊗ P`.**  Paper: none; it replaces the vanishing of the
`H'` term before (`clt-ibp`), "The last line vanishes" (proof of `clt-lemma`). -/
def MeasurePreservingCltSwap : Prop :=
  ∀ c : Coord L W,
    MeasurePreserving (cltSwap L W c) ((P L W).prod (P L W)) ((P L W).prod (P L W))

/-- **Antisymmetric integrands integrate to zero** (a consequence of the exchange, since
`cltSwap c` is an involution, hence a measurable equivalence).  No measurability or boundedness
hypothesis is needed: `∫ F = ∫ F ∘ σ_c = -∫ F`.  Paper: none; it replaces "The last line vanishes" in the proof of `clt-lemma`. -/
def IntegralEqZeroOfCltSwapNeg : Prop :=
  ∀ (c : Coord L W) (F : Ω L W × Ω L W → ℂ), (∀ p, F (cltSwap L W c p) = -F p) →
    ∫ p, F p ∂((P L W).prod (P L W)) = 0

/-- The exchange at `c_k` maps `T_k` to `T_{k+1}`. -/
theorem cltHyb_cltSwap (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ)
    (hk : k < Fintype.card (Coord L W)) (p : Ω L W × Ω L W) :
    cltHyb L W e k (cltSwap L W (e.symm ⟨k, hk⟩) p).1 (cltSwap L W (e.symm ⟨k, hk⟩) p).2 =
      cltHyb L W e (k + 1) p.1 p.2 := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet, cltSwap]
  · have hne := cltHyb_ne L W e hk h
    simp only [cltHyb, cltSplit, cltHybSet, cltSwap, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.update_of_ne h]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The exchange at `c_k` maps `T_{k+1}` to `T_k`. -/
theorem cltHyb_succ_cltSwap (e : Coord L W ≃ Fin (Fintype.card (Coord L W))) (k : ℕ)
    (hk : k < Fintype.card (Coord L W)) (p : Ω L W × Ω L W) :
    cltHyb L W e (k + 1) (cltSwap L W (e.symm ⟨k, hk⟩) p).1 (cltSwap L W (e.symm ⟨k, hk⟩) p).2 =
      cltHyb L W e k p.1 p.2 := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet, cltSwap]
  · have hne := cltHyb_ne L W e hk h
    simp only [cltHyb, cltSplit, cltHybSet, cltSwap, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.update_of_ne h]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The first component of the exchange, with coordinate `c` set to `0`, is `ω^{c→0}`. -/
theorem update_cltSwap_fst (c : Coord L W) (p : Ω L W × Ω L W) :
    Function.update (cltSwap L W c p).1 c 0 = Function.update p.1 c 0 := by
  simp [cltSwap]


/-! ### The three statements -/

private theorem cltSplit_measurable (S : Finset (Coord L W)) :
    Measurable fun p : Ω L W × Ω L W => cltSplit L W S p.1 p.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : c ∈ S
  · have h : (fun p : Ω L W × Ω L W => cltSplit L W S p.1 p.2 c) = fun p => p.2 c := by
      funext p; simp [cltSplit, hc]
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun p : Ω L W × Ω L W => cltSplit L W S p.1 p.2 c) = fun p => p.1 c := by
      funext p; simp [cltSplit, hc]
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

private theorem cltSplit_preimage_pi (S : Finset (Coord L W)) (s : Finset (Coord L W))
    (t : Coord L W → Set ℝ) :
    (fun p : Ω L W × Ω L W => cltSplit L W S p.1 p.2) ⁻¹' ((s : Set (Coord L W)).pi t)
      = ((↑(s.filter fun c => c ∉ S) : Set (Coord L W)).pi t)
        ×ˢ ((↑(s.filter fun c => c ∈ S) : Set (Coord L W)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      simpa [cltSplit, hc.2] using this
    · have := h c hc.1
      simpa [cltSplit, hc.2] using this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcS : c ∈ S
    · simpa [cltSplit, hcS] using h2 c ⟨hc, hcS⟩
    · simpa [cltSplit, hcS] using h1 c ⟨hc, hcS⟩

/-- **The law of a hybrid.**  For every set of coordinates `S`, `(ω, ω') ↦ cltSplit S ω ω'`
pushes `P ⊗ P` to `P` (`MeasurePreservingCltSplit`).  Proof: test on measurable boxes
(`Measure.eq_infinitePi`); the preimage of a box is the product of the box restricted to `S` and
the box restricted to the complement of `S`.  Pattern: `RBM.Green.measurePreserving_rowSplit`. -/
theorem measurePreserving_cltSplit : MeasurePreservingCltSplit L W := by
  intro S
  refine ⟨cltSplit_measurable L W S, ?_⟩
  have hmeas := cltSplit_measurable L W S
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    cltSplit_preimage_pi L W S s t, Measure.prod_prod]
  show P L W _ * P L W _ = _
  rw [P, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun i _ => ht i,
    mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s (fun c => c ∈ S) _

private theorem cltSwap_involutive (c : Coord L W) : Function.Involutive (cltSwap L W c) := by
  intro p
  simp [cltSwap]

/-- **The exchange.**  For every coordinate `c`, the exchange `cltSwap c` preserves `P ⊗ P`
(`MeasurePreservingCltSwap`).  Proof: `P = Measure.pi μ` (finite index), so `P ⊗ P` is the image
of `Measure.pi fun c' => μ c' ⊗ μ c'` under `MeasurableEquiv.arrowProdEquivProdArrow`; there the
exchange is the coordinatewise map which is `Prod.swap` at `c` and the identity elsewhere
(`measurePreserving_pi`, `Measure.measurePreserving_swap`). -/
theorem measurePreserving_cltSwap : MeasurePreservingCltSwap L W := by
  intro c
  classical
  set μ : Coord L W → Measure ℝ := fun c' => gaussianReal 0 (gvar L W c') with hμ
  have hP : P L W = Measure.pi μ := Measure.infinitePi_eq_pi μ
  let A : (Coord L W → ℝ × ℝ) ≃ᵐ (Coord L W → ℝ) × (Coord L W → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Coord L W)
  have hA : MeasurePreserving A (Measure.pi fun c' => (μ c').prod (μ c'))
      ((P L W).prod (P L W)) := by
    rw [hP]
    exact measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Coord L W) μ μ
  have hG : MeasurePreserving
      (fun (a : Coord L W → ℝ × ℝ) (c' : Coord L W) =>
        (if c' = c then (Prod.swap : ℝ × ℝ → ℝ × ℝ) else id) (a c'))
      (Measure.pi fun c' => (μ c').prod (μ c')) (Measure.pi fun c' => (μ c').prod (μ c')) := by
    refine measurePreserving_pi _ _ (f := fun c' => if c' = c then Prod.swap else id) fun c' => ?_
    by_cases h : c' = c
    · simp only [h, ite_true]
      exact Measure.measurePreserving_swap
    · simp only [h, ite_false]
      exact MeasurePreserving.id _
  have hfun : cltSwap L W c = A ∘ (fun (a : Coord L W → ℝ × ℝ) (c' : Coord L W) =>
      (if c' = c then (Prod.swap : ℝ × ℝ → ℝ × ℝ) else id) (a c')) ∘ A.symm := by
    funext p
    refine Prod.ext ?_ ?_
    · funext c'
      by_cases h : c' = c
      · subst h
        simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          h]
    · funext c'
      by_cases h : c' = c
      · subst h
        simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          h]
  rw [hfun]
  exact (hA.comp (hG.comp (hA.symm A)))

/-- **Antisymmetric integrands.**  An integrand with `F ∘ cltSwap c = -F` integrates to zero
against `P ⊗ P` (`IntegralEqZeroOfCltSwapNeg`).  No measurability, integrability or boundedness
of `F` is used: `cltSwap c` is a measurable involution preserving `P ⊗ P`
(`measurePreserving_cltSwap`), hence `∫ F = ∫ F ∘ cltSwap c = -∫ F`. -/
theorem integral_eq_zero_of_cltSwap_neg : IntegralEqZeroOfCltSwapNeg L W := by
  intro c F hF
  have hmp := measurePreserving_cltSwap L W c
  let σ : (Ω L W × Ω L W) ≃ᵐ (Ω L W × Ω L W) :=
    { toEquiv := (cltSwap_involutive L W c).toPerm _
      measurable_toFun := hmp.measurable
      measurable_invFun := hmp.measurable }
  have hσ : MeasurePreserving σ ((P L W).prod (P L W)) ((P L W).prod (P L W)) := hmp
  have h1 : ∫ p, F (σ p) ∂((P L W).prod (P L W)) = ∫ p, F p ∂((P L W).prod (P L W)) :=
    hσ.integral_comp' F
  have h2 : ∫ p, F (σ p) ∂((P L W).prod (P L W)) = -∫ p, F p ∂((P L W).prod (P L W)) := by
    have : ∀ p, F (σ p) = -F p := fun p => hF p
    simp_rw [this]
    exact integral_neg _
  have h3 : ∫ p, F p ∂((P L W).prod (P L W)) = -∫ p, F p ∂((P L W).prod (P L W)) :=
    h1.symm.trans h2
  linear_combination (1 / 2 : ℂ) * h3

end Rep

/-- **Transfer**: an integral of a measurable function of the size-`n` slice over
`Sizes.seqP d` is the same integral over `P (d.L n) (d.W n)` (`Sizes.seqP_map_slice`).  The
integrand of `CltFar` is such a function (`Sizes.seqHflow d n u ω = Hflow … u (slice d n ω)`). -/
theorem cltTransfer (d : Sizes) (n : ℕ) (f : Ω (d.L n) (d.W n) → ℂ) (hf : Measurable f) :
    ∫ ω, f (Sizes.slice d n ω) ∂(Sizes.seqP d) = ∫ ω, f ω ∂(P (d.L n) (d.W n)) := by
  rw [← Sizes.seqP_map_slice d n,
    integral_map (Sizes.measurable_slice d n).aemeasurable hf.aestronglyMeasurable]

end RBM.Evol

end
