/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.PoissonSmoothing
import RBM2D.Universality.EigenMeasurable

/-!
# The Green-function-to-correlation comparison

Paper: arXiv:2503.07606, the paragraph after `univ-main` ("Theorem 15.3 in [25], Proposition 4.17
in [45], and (2.23) in [YY_25]"): from the Claim `(417)` for all `n_f ≤ k` and an a priori bound at
the level spacing, the `k`-point functionals of `𝐇_0` and `𝐇_{t*}` have the same limit.

* `greenCorrAll` -- the statement `GreenCorrAll` of `Universality/Pins.lean`, proved.

Notation: the Stieltjes transform is `stieltjesN`, the correlation functional is `kPoint`, the
test-function class is `InjSum_IsTestFun`, the matrix flow is `ouMat (d.L n) (d.W n) t` on the
carrier `ouP`, the Claim is `Claim417` (a constant `Cn nf` per number of factors), and the time is
`ouTStar`.  The lemmas `injSum_decomp`, `sum_poissonSmooth_eq`, `poissonSmooth_error`,
`sum_prod_lorentz_eq` and `eigenvalues₀_abs_sub_le` are used.

Main lemmas:
* `gcc_continuous_eigenvalues₀_subtype`, `gcc_continuous_eigenvalues_subtype`,
  `gcc_measurable_eigenvalues`: continuity and measurability of the eigenvalues;
* `gccSpec`, `gccSpec_nonneg`, `gccSpec_le`, `gccSpec_measurable`;
* `gcc_stieltjes_im_eq`, `gcc_stieltjes_im_eq_inv`;
* `gcc_imInv_props`, `gcc_main`, `gcc_fullSum_integrable`, `gcc_err`, `gcc_piece`;
* `gcc_kPoint_expand`, `gcc_prefactor_le` (`N^k / N.descFactorial k`), `gcc_card_idx`;
* `gcc_quantitative` (support radius, decomposition, eventualities) and `gcc_step`;
* `gccCmax`, `gcc_tendsto` (threshold `τ₀`, limits), `greenCorrAll`.

Proof outline: the injective sum is decomposed into full sums (`injSum_decomp`); each full sum is
Poisson-smoothed at scale `ε' = N^{-τ_U}` (`sum_poissonSmooth_eq`), which turns its expectation
into an integral of `E ∏ Im m_t(z_j)` with `Im z_j = N^{-1-τ_U}`, to which `(417)` applies; the
smoothing error is controlled by `poissonSmooth_error` and `sum_prod_lorentz_eq` in terms of
`E (Im m_t(E + i/N))^p`, which at `t = t*` is transferred from `t = 0` by `(417)` at
`z ≡ E + i/N`.  With `Cmax = max 0 (max_{n_f ≤ k} C_{n_f})` and `τ₀ = c' / (2 (Cmax + 1))`, for
`0 < τ_U ≤ τ₀` the two error terms are `N^{-c'+Cmax τ_U} ≤ N^{-c'/2}` and `N^{-τ_U/2}`, both
tending to `0`; `τ₀` depends only on `k, c', C_n` (not on `E`, `O`, the sizes or `τ_U`).
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints

/-! ### Generic finite-dimensional helpers -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]

/-- Continuity of `eigenvalues₀ i` on the Hermitian subtype (Weyl bound
`eigenvalues₀_abs_sub_le`). -/
private theorem gcc_continuous_eigenvalues₀_subtype (i : Fin (Fintype.card n)) :
    Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues₀ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ i)
    (𝓝 x) (𝓝 (x.2.eigenvalues₀ i))
  rw [tendsto_iff_dist_tendsto_zero]
  have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
  have hcont : Continuous (fun A : Matrix n n ℂ =>
      Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
    Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun b _ =>
        (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
  have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
      (𝓝 x.1) (𝓝 0) := by
    have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
    have := hcont.continuousAt (x := x.1)
    rwa [ContinuousAt, hval] at this
  have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
      Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
    h0.comp (continuous_subtype_val.continuousAt (x := x))
  refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
  rw [Real.dist_eq]
  exact eigenvalues₀_abs_sub_le y.2 x.2 i

private theorem gcc_continuous_eigenvalues_subtype (i : n) :
    Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) := by
  simpa [Matrix.IsHermitian.eigenvalues] using gcc_continuous_eigenvalues₀_subtype (n := n)
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)

/-- The eigenvalue vector of a measurable, everywhere-Hermitian matrix-valued map is
measurable. -/
private theorem gcc_measurable_eigenvalues {Hm : Ω → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) : Measurable (fun ω => (hH ω).eigenvalues) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk
  have h : Measurable ((fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) ∘
      (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian}))) :=
    (gcc_continuous_eigenvalues_subtype i).measurable.comp hφ
  exact h

/-- The spectral weight `|n|⁻¹ ∑ₗ η/((λₗ-a)²+η²)` (`= Im m(a+iη)` for `η > 0`). -/
private noncomputable def gccSpec (lam : n → ℝ) (a η : ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ l, η / ((lam l - a) ^ 2 + η ^ 2)

omit [DecidableEq n] in
private lemma gccSpec_nonneg (lam : n → ℝ) (a : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ gccSpec lam a η := by
  unfold gccSpec
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => div_nonneg hη (by positivity))

omit [DecidableEq n] in
private lemma gccSpec_le (lam : n → ℝ) (a : ℝ) {η : ℝ} (hη : 0 < η) :
    gccSpec lam a η ≤ η⁻¹ := by
  unfold gccSpec
  have hterm : ∀ l, η / ((lam l - a) ^ 2 + η ^ 2) ≤ η⁻¹ := fun l => by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ η⁻¹ * (lam l - a) ^ 2 := by positivity
    have h2 : η⁻¹ * ((lam l - a) ^ 2 + η ^ 2) = η⁻¹ * (lam l - a) ^ 2 + η := by
      field_simp
    linarith
  calc (Fintype.card n : ℝ)⁻¹ * ∑ l, η / ((lam l - a) ^ 2 + η ^ 2)
      ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _l : n, η⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hterm l) (by positivity)
    _ = ((Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)) * η⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ η⁻¹ := by
        by_cases h : (Fintype.card n : ℝ) = 0
        · rw [h]; simp only [_root_.inv_zero, zero_mul]; positivity
        · rw [inv_mul_cancel₀ h, one_mul]

omit [DecidableEq n] in
private lemma gccSpec_measurable :
    Measurable (fun p : (n → ℝ) × ℝ × ℝ => gccSpec p.1 p.2.1 p.2.2) := by
  unfold gccSpec
  refine measurable_const.mul (Finset.measurable_sum _ fun l _ => ?_)
  exact (measurable_snd.snd).div
    ((((measurable_pi_apply l).comp measurable_fst).sub measurable_snd.fst).pow_const 2 |>.add
      (measurable_snd.snd.pow_const 2))

private lemma gcc_stieltjes_im_eq (Hm : Matrix n n ℂ) (hH : Hm.IsHermitian) (a η : ℝ)
    (hη : 0 < η) :
    (stieltjesN Hm ((a : ℂ) + (η : ℂ) * Complex.I)).im = gccSpec hH.eigenvalues a η :=
  stieltjesN_im_eq_normalized_specWeight Hm hH a η hη

private lemma gcc_stieltjes_im_eq_inv (Hm : Matrix n n ℂ) (hH : Hm.IsHermitian) (a Nr : ℝ)
    (hNr : 0 < Nr) :
    (stieltjesN Hm ((a : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im = gccSpec hH.eigenvalues a Nr⁻¹ := by
  rw [← gcc_stieltjes_im_eq Hm hH a Nr⁻¹ (inv_pos.2 hNr)]
  push_cast
  rfl

/-- Measurability and the bound `0 ≤ Im m(E+i/Nr) ≤ Nr` for the level-spacing observable. -/
private lemma gcc_imInv_props (P : Measure Ω) [IsProbabilityMeasure P] {Hm : Ω → Matrix n n ℂ}
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (E Nr : ℝ) (hNr : 0 < Nr) (m : ℕ) :
    Integrable (fun ω => (stieltjesN (Hm ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ m) P := by
  have heq : (fun ω => (stieltjesN (Hm ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ m) =
      fun ω => gccSpec (hH ω).eigenvalues E Nr⁻¹ ^ m := by
    funext ω; rw [gcc_stieltjes_im_eq_inv (Hm ω) (hH ω) E Nr hNr]
  rw [heq]
  have hmeas : Measurable (fun ω => gccSpec (hH ω).eigenvalues E Nr⁻¹ ^ m) := by
    have h := (gccSpec_measurable (n := n)).comp
      ((gcc_measurable_eigenvalues hm hH).prodMk (measurable_const (a := ((E, Nr⁻¹) : ℝ × ℝ))))
    exact h.pow_const m
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Nr⁻¹⁻¹ ^ m) (ae_of_all _ fun ω => ?_)
  have h0 := gccSpec_nonneg (hH ω).eigenvalues E (inv_pos.2 hNr).le
  have h1 := gccSpec_le (hH ω).eigenvalues E (inv_pos.2 hNr)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 m)]
  exact pow_le_pow_left₀ h0 h1 m

/-- **Main term (Fubini).** The expectation of the Poisson-smoothed full sum is
`π^{-m} ∫ O(y) E ∏ⱼ Im m(E + yⱼ/N + iε/N) dy`, with the relevant integrabilities. -/
private lemma gcc_main (P : Measure Ω) [IsProbabilityMeasure P] {Hm : Ω → Matrix n n ℂ}
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) {m : ℕ} {O : (Fin m → ℝ) → ℝ}
    (hO : InjSum_IsTestFun O) (E : ℝ) {ε : ℝ} (hε : 0 < ε) (hcard : 0 < (Fintype.card n : ℝ)) :
    Integrable (fun ω => ∑ g : Fin m → n, poissonSmooth ε O
      (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) P ∧
    Integrable (fun y : Fin m → ℝ => O y * ∫ ω, ∏ j, (stieltjesN (Hm ω)
      (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
        Complex.I)).im ∂P) ∧
    ∫ ω, ∑ g : Fin m → n, poissonSmooth ε O
      (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P =
      Real.pi⁻¹ ^ m * ∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (Hm ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P := by
  set Nc : ℝ := (Fintype.card n : ℝ) with hNc
  have hη : 0 < ε / Nc := div_pos hε hcard
  set f : Ω → (Fin m → ℝ) → ℝ := fun ω y => O y * ∏ j, Real.pi⁻¹ *
    (stieltjesN (Hm ω) (((E + y j / Nc : ℝ) : ℂ) + ((ε / Nc : ℝ) : ℂ) * Complex.I)).im with hf
  have hsum : ∀ ω, ∑ g : Fin m → n, poissonSmooth ε O
      (fun j => Nc * ((hH ω).eigenvalues (g j) - E)) = ∫ y, f ω y := fun ω =>
    sum_poissonSmooth_eq (Hm ω) (hH ω) hO E hε
  have hfeq : Function.uncurry f = fun p : Ω × (Fin m → ℝ) => O p.2 * ∏ j, Real.pi⁻¹ *
      gccSpec (hH p.1).eigenvalues (E + p.2 j / Nc) (ε / Nc) := by
    funext p
    simp only [Function.uncurry, hf]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [gcc_stieltjes_im_eq (Hm p.1) (hH p.1) _ _ hη]
  have hΛ := gcc_measurable_eigenvalues hm hH
  have hfmeas : Measurable (Function.uncurry f) := by
    rw [hfeq]
    refine (hO.1.continuous.measurable.comp measurable_snd).mul
      (Finset.measurable_prod _ fun j _ => measurable_const.mul ?_)
    have hz : Measurable (fun p : Ω × (Fin m → ℝ) =>
        (((hH p.1).eigenvalues, E + p.2 j / Nc, ε / Nc) : (n → ℝ) × ℝ × ℝ)) := by
      refine (hΛ.comp measurable_fst).prodMk (Measurable.prodMk ?_ measurable_const)
      exact measurable_const.add (((measurable_pi_apply j).comp measurable_snd).div_const _)
    exact (gccSpec_measurable (n := n)).comp hz
  set cb : ℝ := (Real.pi⁻¹ * (ε / Nc)⁻¹) ^ m with hcb
  have hbound : ∀ p : Ω × (Fin m → ℝ), ‖Function.uncurry f p‖ ≤ 1 * (|O p.2| * cb) := by
    intro p
    rw [hfeq, one_mul, Real.norm_eq_abs, abs_mul,
      show cb = ∏ _j : Fin m, (Real.pi⁻¹ * (ε / Nc)⁻¹) by simp [hcb], Finset.abs_prod]
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => ?_
      have h0 := gccSpec_nonneg (hH p.1).eigenvalues (E + p.2 j / Nc) hη.le
      have h1 := gccSpec_le (hH p.1).eigenvalues (E + p.2 j / Nc) hη
      rw [abs_of_nonneg (mul_nonneg (by positivity) h0)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hOint : Integrable O := hO.1.continuous.integrable_of_hasCompactSupport hO.2
  have hint : Integrable (Function.uncurry f) (P.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod (hOint.abs.mul_const cb))
      hfmeas.aestronglyMeasurable (ae_of_all _ hbound)
  have hinner : ∀ y, ∫ ω, f ω y ∂P = Real.pi⁻¹ ^ m * (O y * ∫ ω, ∏ j, (stieltjesN (Hm ω)
      (((E + y j / Nc : ℝ) : ℂ) + ((ε / Nc : ℝ) : ℂ) * Complex.I)).im ∂P) := by
    intro y
    simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [show (fun ω => O y * (Real.pi⁻¹ ^ m * ∏ j, (stieltjesN (Hm ω)
        (((E + y j / Nc : ℝ) : ℂ) + ((ε / Nc : ℝ) : ℂ) * Complex.I)).im)) =
        fun ω => (O y * Real.pi⁻¹ ^ m) * ∏ j, (stieltjesN (Hm ω)
        (((E + y j / Nc : ℝ) : ℂ) + ((ε / Nc : ℝ) : ℂ) * Complex.I)).im from by
      funext ω; ring]
    rw [integral_const_mul]; ring
  refine ⟨?_, ?_, ?_⟩
  · have h := hint.integral_prod_left
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.uncurry]
    exact (hsum ω).symm
  · have h := (hint.integral_prod_right).const_mul (Real.pi ^ m)
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [Function.uncurry]
    rw [hinner y, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow, one_mul]
  · calc ∫ ω, ∑ g : Fin m → n, poissonSmooth ε O
          (fun j => Nc * ((hH ω).eigenvalues (g j) - E)) ∂P
        = ∫ ω, (∫ y, f ω y) ∂P := integral_congr_ae (ae_of_all _ hsum)
      _ = ∫ y, ∫ ω, f ω y ∂P := integral_integral_swap hint
      _ = ∫ y, Real.pi⁻¹ ^ m * (O y * ∫ ω, ∏ j, (stieltjesN (Hm ω)
            (((E + y j / Nc : ℝ) : ℂ) + ((ε / Nc : ℝ) : ℂ) * Complex.I)).im ∂P) :=
          integral_congr_ae (ae_of_all _ hinner)
      _ = _ := integral_const_mul _ _

/-- Full sums of a test function of the rescaled eigenvalues are integrable. -/
private lemma gcc_fullSum_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    {Hm : Ω → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) {m : ℕ}
    {O : (Fin m → ℝ) → ℝ} (hO : InjSum_IsTestFun O) (E : ℝ) :
    Integrable (fun ω => ∑ g : Fin m → n,
      O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) P := by
  obtain ⟨M, hM⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  have hΛ := gcc_measurable_eigenvalues hm hH
  have hmeas : Measurable (fun ω => ∑ g : Fin m → n,
      O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) := by
    refine Finset.measurable_sum _ fun g _ => hO.1.continuous.measurable.comp ?_
    exact measurable_pi_iff.mpr fun j =>
      measurable_const.mul (((measurable_pi_apply (g j)).comp hΛ).sub measurable_const)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ _g : Fin m → n, M)
    (ae_of_all _ fun ω => ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => hM _)

/-- **Smoothing error.** `|E ∑_g (O − O*P_ε)(λ̂_g)| ≤ C' ε E (Im m(E+i/N))^m`. -/
private lemma gcc_err (P : Measure Ω) [IsProbabilityMeasure P] [Nonempty n]
    {Hm : Ω → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) {m : ℕ}
    {O : (Fin m → ℝ) → ℝ} (E : ℝ) {ε C' : ℝ}
    (hC' : ∀ x, |O x - poissonSmooth ε O x| ≤ C' * ε * ∏ j, (1 + x j ^ 2)⁻¹) :
    |∫ ω, ∑ g : Fin m → n,
        (O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) -
          poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)))
        ∂P| ≤
      C' * ε * ∫ ω, (stieltjesN (Hm ω)
        ((E : ℂ) + (((Fintype.card n : ℝ) : ℂ))⁻¹ * Complex.I)).im ^ m ∂P := by
  have hcard : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [← integral_const_mul]
  have h := norm_integral_le_of_norm_le (μ := P)
    (f := fun ω => ∑ g : Fin m → n,
        (O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) -
          poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))))
    ((gcc_imInv_props P hm hH E _ hcard m).const_mul (C' * ε)) (ae_of_all _ fun ω => ?_)
  · simpa only [Real.norm_eq_abs] using h
  rw [Real.norm_eq_abs]
  calc |∑ g : Fin m → n,
        (O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) -
          poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)))|
      ≤ ∑ g : Fin m → n,
        |O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) -
          poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g : Fin m → n, C' * ε *
          ∏ j, (1 + ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun g _ => hC' _
    _ = C' * ε * ∑ g : Fin m → n,
          ∏ j, (1 + ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ = C' * ε * (stieltjesN (Hm ω)
          ((E : ℂ) + (((Fintype.card n : ℝ) : ℂ))⁻¹ * Complex.I)).im ^ m :=
        congrArg (fun x => C' * ε * x) (sum_prod_lorentz_eq (Hm ω) (hH ω) m E)

/-- **One piece of the decomposition.** For a test function `O` of `m` variables, the difference
of the expected full sums at two times is bounded by the `(417)`-type difference `δ` of the
Poisson-smoothed main terms plus the smoothing errors. -/
private lemma gcc_piece (P : Measure Ω) [IsProbabilityMeasure P] [Nonempty n]
    {H0 H1 : Ω → Matrix n n ℂ} (hm0 : Measurable H0) (hm1 : Measurable H1)
    (hH0 : ∀ ω, (H0 ω).IsHermitian) (hH1 : ∀ ω, (H1 ω).IsHermitian) {m : ℕ}
    {O : (Fin m → ℝ) → ℝ} (hO : InjSum_IsTestFun O) (E : ℝ) {ε C' δ Nr : ℝ}
    (hNr : (Fintype.card n : ℝ) = Nr) (hε : 0 < ε)
    (hC' : ∀ x, |O x - poissonSmooth ε O x| ≤ C' * ε * ∏ j, (1 + x j ^ 2)⁻¹)
    (hδ : ∀ y : Fin m → ℝ, O y ≠ 0 →
      |(∫ ω, ∏ j, (stieltjesN (H0 ω)
          (((E + y j / Nr : ℝ) : ℂ) + ((ε / Nr : ℝ) : ℂ) * Complex.I)).im ∂P) -
        ∫ ω, ∏ j, (stieltjesN (H1 ω)
          (((E + y j / Nr : ℝ) : ℂ) + ((ε / Nr : ℝ) : ℂ) * Complex.I)).im ∂P| ≤ δ) :
    Integrable (fun ω => ∑ g : Fin m → n,
      O (fun j => (Fintype.card n : ℝ) * ((hH0 ω).eigenvalues (g j) - E))) P ∧
    Integrable (fun ω => ∑ g : Fin m → n,
      O (fun j => (Fintype.card n : ℝ) * ((hH1 ω).eigenvalues (g j) - E))) P ∧
    |(∫ ω, ∑ g : Fin m → n,
        O (fun j => (Fintype.card n : ℝ) * ((hH0 ω).eigenvalues (g j) - E)) ∂P) -
      ∫ ω, ∑ g : Fin m → n,
        O (fun j => (Fintype.card n : ℝ) * ((hH1 ω).eigenvalues (g j) - E)) ∂P| ≤
      (∫ y, |O y|) * δ + C' * ε *
        ((∫ ω, (stieltjesN (H0 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ m ∂P) +
          ∫ ω, (stieltjesN (H1 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ m ∂P) := by
  subst hNr
  have hcard : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hF0 := gcc_fullSum_integrable P hm0 hH0 hO E
  have hF1 := gcc_fullSum_integrable P hm1 hH1 hO E
  obtain ⟨hS0, hA0, hM0⟩ := gcc_main P hm0 hH0 hO E hε hcard
  obtain ⟨hS1, hA1, hM1⟩ := gcc_main P hm1 hH1 hO E hε hcard
  have hX0 := gcc_err P hm0 hH0 E hC'
  have hX1 := gcc_err P hm1 hH1 E hC'
  refine ⟨hF0, hF1, ?_⟩
  -- split each full sum into main term plus smoothing error
  have hsplit : ∀ {Hm : Ω → Matrix n n ℂ} (hH : ∀ ω, (Hm ω).IsHermitian),
      Integrable (fun ω => ∑ g : Fin m → n,
        O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) P →
      Integrable (fun ω => ∑ g : Fin m → n, poissonSmooth ε O
        (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) P →
      ∫ ω, ∑ g : Fin m → n,
          O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P =
        (∫ ω, ∑ g : Fin m → n, poissonSmooth ε O
          (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P) +
        ∫ ω, ∑ g : Fin m → n,
          (O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) -
            poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)))
          ∂P := by
    intro Hm hH hF hS
    simp_rw [Finset.sum_sub_distrib]
    rw [integral_sub hF hS]
    ring
  rw [hsplit hH0 hF0 hS0, hsplit hH1 hF1 hS1, hM0, hM1]
  set X0 := ∫ ω, ∑ g : Fin m → n,
    (O (fun j => (Fintype.card n : ℝ) * ((hH0 ω).eigenvalues (g j) - E)) -
      poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH0 ω).eigenvalues (g j) - E))) ∂P
  set X1 := ∫ ω, ∑ g : Fin m → n,
    (O (fun j => (Fintype.card n : ℝ) * ((hH1 ω).eigenvalues (g j) - E)) -
      poissonSmooth ε O (fun j => (Fintype.card n : ℝ) * ((hH1 ω).eigenvalues (g j) - E))) ∂P
  -- main-term difference
  have hmain : |(∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H0 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) -
      ∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H1 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P| ≤ (∫ y, |O y|) * δ := by
    rw [← integral_sub hA0 hA1, ← integral_mul_const]
    have hOint : Integrable O := hO.1.continuous.integrable_of_hasCompactSupport hO.2
    have h := norm_integral_le_of_norm_le (μ := volume)
      (f := fun y : Fin m → ℝ => O y * (∫ ω, ∏ j, (stieltjesN (H0 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) - O y * ∫ ω, ∏ j, (stieltjesN (H1 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) (hOint.abs.mul_const δ) (ae_of_all _ fun y => ?_)
    · simpa only [Real.norm_eq_abs] using h
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    by_cases hy : O y = 0
    · simp [hy]
    · exact mul_le_mul_of_nonneg_left (hδ y hy) (abs_nonneg _)
  have hpi : Real.pi⁻¹ ^ m ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three]))
  have hpi0 : 0 ≤ Real.pi⁻¹ ^ m := by positivity
  set D := (∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H0 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) -
      ∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H1 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P with hD
  have hdiff : Real.pi⁻¹ ^ m * (∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H0 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) + X0 -
      (Real.pi⁻¹ ^ m * (∫ y : Fin m → ℝ, O y * ∫ ω, ∏ j, (stieltjesN (H1 ω)
        (((E + y j / Fintype.card n : ℝ) : ℂ) + ((ε / Fintype.card n : ℝ) : ℂ) *
          Complex.I)).im ∂P) + X1) = Real.pi⁻¹ ^ m * D + X0 - X1 := by
    rw [hD]; ring
  rw [hdiff]
  have hpD : |Real.pi⁻¹ ^ m * D| ≤ (∫ y, |O y|) * δ := by
    rw [abs_mul, abs_of_nonneg hpi0]
    calc Real.pi⁻¹ ^ m * |D| ≤ 1 * |D| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
      _ = |D| := one_mul _
      _ ≤ _ := hmain
  calc |Real.pi⁻¹ ^ m * D + X0 - X1| ≤ |Real.pi⁻¹ ^ m * D| + |X0| + |X1| := by
        have h1 := abs_sub (Real.pi⁻¹ ^ m * D + X0) X1
        have h2 := abs_add_le (Real.pi⁻¹ ^ m * D) X0
        linarith
    _ ≤ (∫ y, |O y|) * δ + C' * ε * (∫ ω, (stieltjesN (H0 ω)
          ((E : ℂ) + (((Fintype.card n : ℝ) : ℂ))⁻¹ * Complex.I)).im ^ m ∂P) +
        C' * ε * (∫ ω, (stieltjesN (H1 ω)
          ((E : ℂ) + (((Fintype.card n : ℝ) : ℂ))⁻¹ * Complex.I)).im ^ m ∂P) := by
        linarith
    _ = _ := by ring

/-- The `k`-point functional expanded along an injective-sum decomposition. -/
private lemma gcc_kPoint_expand (P : Measure Ω) {Hm : Ω → Matrix n n ℂ}
    (hH : ∀ ω, (Hm ω).IsHermitian) {k : ℕ} {O : (Fin k → ℝ) → ℝ} {ι : Type} [Fintype ι]
    (c : ι → ℤ) (kk : ι → ℕ) (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ)
    (hdec : ∀ lam : n → ℝ, ∑ f : Fin k ↪ n, O (lam ∘ f) =
      ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g)) (E : ℝ)
    (hint : ∀ i, Integrable (fun ω => ∑ g : Fin (kk i) → n,
      Oj i (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E))) P) :
    ∫ ω, kPoint k O E (hH ω).eigenvalues ∂P =
      ((Fintype.card n : ℝ) ^ k / ((Fintype.card n).descFactorial k : ℝ)) *
        ∑ i, (c i : ℝ) * ∫ ω, ∑ g : Fin (kk i) → n,
          Oj i (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P := by
  unfold kPoint
  rw [integral_const_mul]
  congr 1
  calc ∫ ω, ∑ f : Fin k ↪ n,
          O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) ∂P
      = ∫ ω, ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n,
          Oj i (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω =>
          hdec (fun l => (Fintype.card n : ℝ) * ((hH ω).eigenvalues l - E)))
    _ = ∑ i, ∫ ω, (c i : ℝ) * ∑ g : Fin (kk i) → n,
          Oj i (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (g j) - E)) ∂P :=
        integral_finsetSum _ fun i _ => (hint i).const_mul _
    _ = _ := Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Generic

/-- The normalization `N^k / N.descFactorial k` of `kPoint` is at most `2^k` once `N ≥ 2k`. -/
private lemma gcc_prefactor_le {M k : ℕ} (hM : 2 * k ≤ M) :
    (M : ℝ) ^ k / (M.descFactorial k : ℝ) ≤ 2 ^ k := by
  have hkM : k ≤ M := by omega
  have hdesc := Nat.pow_sub_le_descFactorial M k
  have hpow : M ^ k ≤ 2 ^ k * M.descFactorial k := by
    calc M ^ k ≤ (2 * (M + 1 - k)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (M + 1 - k) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * M.descFactorial k := Nat.mul_le_mul_left _ hdesc
  have hpos : (0 : ℝ) < (M.descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hkM
  rw [div_le_iff₀ hpos]
  exact_mod_cast hpow


/-! ### The comparison at one size -/

section Step

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The comparison at one size**: for a decomposition `injSum_decomp` of the test function `O` and
the smoothing constants `Cs`, the `k`-point functionals of `𝐇_0` and `𝐇_{t₁}` differ by at most
`K (N^{-c'+Cτ_U} + N^{-τ_U/2})`, given the `(417)` bounds for `n_f ≤ k` at the window points
`E + y/N + iN^{-1-τ_U}`, `|y| ≤ R`, and at `z ≡ E + i/N`, and the a priori bound at `t = 0`. -/
private theorem gcc_step (t₁ : ℝ) {k : ℕ} {O : (Fin k → ℝ) → ℝ} (E : ℝ)
    {τU c' C R Nr : ℝ} (Cn : ℕ → ℝ) (hτU : 0 < τU) (hCn : ∀ nf ≤ k, Cn nf ≤ C)
    (hR : 0 < R + 1) {ι : Type} [Fintype ι] (c : ι → ℤ) (kk : ι → ℕ)
    (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ) (hkk : ∀ i, kk i ≤ k)
    (hOj : ∀ i, InjSum_IsTestFun (Oj i)) (hOjR : ∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ R)
    (hdec : ∀ lam : Idx L W → ℝ, ∑ f : Fin k ↪ Idx L W, O (lam ∘ f) =
      ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → Idx L W, Oj i (lam ∘ g))
    (Cs : ι → ℝ) (hCs0 : ∀ i, 0 ≤ Cs i)
    (hCs : ∀ i, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin (kk i) → ℝ,
      |Oj i x - poissonSmooth ε (Oj i) x| ≤ Cs i * ε * ∏ j, (1 + x j ^ 2)⁻¹)
    (hcardN : (Fintype.card (Idx L W) : ℝ) = Nr) (hNr1 : 1 ≤ Nr)
    (h2k : 2 * k ≤ Fintype.card (Idx L W))
    (hN1 : ∀ nf ∈ Finset.range (k + 1), ∀ z : Fin nf → ℂ,
      (∀ i, |(z i).re - E| ≤ (R + 1) / Nr ∧ Nr ^ (-1 - τU) ≤ (z i).im ∧
        (z i).im ≤ Nr ^ (-1 + τU)) →
      |(∫ ω, ∏ i, (stieltjesN (ouMat L W 0 ω) (z i)).im ∂(ouP L W)) -
        ∫ ω, ∏ i, (stieltjesN (ouMat L W t₁ ω) (z i)).im ∂(ouP L W)| ≤
        Nr ^ (-c' + Cn nf * τU))
    (hN2 : ∀ nf ∈ Finset.range (k + 1),
      ∫ ω, (stieltjesN (ouMat L W 0 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ nf
        ∂(ouP L W) ≤ Nr ^ (τU / 2)) :
    |(∫ ω, kPoint k O E (ouMat_isHermitian L W 0 ω).eigenvalues ∂(ouP L W)) -
        ∫ ω, kPoint k O E (ouMat_isHermitian L W t₁ ω).eigenvalues ∂(ouP L W)| ≤
      (2 ^ k * ∑ i, |(c i : ℝ)| * ((∫ y, |Oj i y|) + 2 * Cs i)) *
        (Nr ^ (-c' + C * τU) + Nr ^ (-(τU / 2))) := by
  have hNr0 : 0 < Nr := by linarith
  set ε : ℝ := Nr ^ (-τU) with hεdef
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hNr0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by linarith)
  set A : ℝ := Nr ^ (-c' + C * τU) with hAdef
  set Bt : ℝ := Nr ^ (-(τU / 2)) with hBdef
  have hA0 : 0 ≤ A := (Real.rpow_pos_of_pos hNr0 _).le
  have hB0 : 0 ≤ Bt := (Real.rpow_pos_of_pos hNr0 _).le
  have hεN : ε / Nr = Nr ^ (-1 - τU) := by
    rw [show (-1 - τU) = -τU + -1 by ring, Real.rpow_add hNr0, Real.rpow_neg_one, div_eq_mul_inv]
  have hinvN : Nr⁻¹ = Nr ^ (-1 : ℝ) := (Real.rpow_neg_one Nr).symm
  have hwin_lo : Nr ^ (-1 - τU) ≤ Nr ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hwin_hi : Nr ^ (-1 : ℝ) ≤ Nr ^ (-1 + τU) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hεB : ε * Nr ^ (τU / 2) = Bt := by
    rw [hεdef, hBdef, ← Real.rpow_add hNr0]; ring_nf
  -- per-piece bound
  have hpiece : ∀ i,
      Integrable (fun ω => ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
        (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W 0 ω).eigenvalues (g j) - E)))
        (ouP L W) ∧
      Integrable (fun ω => ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
        (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W t₁ ω).eigenvalues (g j) - E)))
        (ouP L W) ∧
      |(∫ ω, ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
          (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W 0 ω).eigenvalues (g j) - E))
          ∂(ouP L W)) -
        ∫ ω, ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
          (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W t₁ ω).eigenvalues (g j) - E))
          ∂(ouP L W)| ≤
        ((∫ y, |Oj i y|) + 2 * Cs i) * (A + Bt) := by
    intro i
    have hkki : kk i ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le (hkk i))
    have hexp : Nr ^ (-c' + Cn (kk i) * τU) ≤ A := by
      refine Real.rpow_le_rpow_of_exponent_le hNr1 ?_
      have := mul_le_mul_of_nonneg_right (hCn (kk i) (hkk i)) hτU.le
      linarith
    obtain ⟨hi0, hi1, hb⟩ := gcc_piece (ouP L W) (measurable_ouMat L W 0)
      (measurable_ouMat L W t₁) (ouMat_isHermitian L W 0) (ouMat_isHermitian L W t₁) (hOj i) E
      (δ := A) hcardN hε0 (hCs i ε hε0 hε1) (fun y hy => by
        refine (hN1 (kk i) hkki
          (fun j => ((E + y j / Nr : ℝ) : ℂ) + ((ε / Nr : ℝ) : ℂ) * Complex.I)
          fun j => ⟨?_, ?_, ?_⟩).trans hexp
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_mul]
          rw [add_sub_cancel_left, abs_div, abs_of_pos hNr0]
          exact div_le_div_of_nonneg_right (by linarith [hOjR i y hy j]) hNr0.le
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
          rw [hεN]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
          rw [hεN]; exact hwin_lo.trans hwin_hi)
    refine ⟨hi0, hi1, hb.trans ?_⟩
    have hI0 := hN2 (kk i) hkki
    have hI1 : ∫ ω, (stieltjesN (ouMat L W t₁ ω)
        ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ (kk i) ∂(ouP L W) ≤ Nr ^ (τU / 2) + A := by
      have hzc : ∀ _j : Fin (kk i),
          |((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I).re - E| ≤ (R + 1) / Nr ∧
            Nr ^ (-1 - τU) ≤ ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I).im ∧
            ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I).im ≤ Nr ^ (-1 + τU) := by
        intro _j
        rw [← Complex.ofReal_inv]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add, sub_self, abs_zero]
        refine ⟨div_nonneg hR.le hNr0.le, ?_, ?_⟩
        · rw [hinvN]; exact hwin_lo
        · rw [hinvN]; exact hwin_hi
      have h := hN1 (kk i) hkki (fun _ => (E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I) hzc
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      have h' := (abs_sub_le_iff.1 (h.trans hexp)).2
      linarith
    have hCε : 0 ≤ Cs i * ε := mul_nonneg (hCs0 i) hε0.le
    have hOn : 0 ≤ ∫ y, |Oj i y| := integral_nonneg fun y => abs_nonneg _
    have hεA : ε * A ≤ A := by nlinarith
    calc (∫ y, |Oj i y|) * A + Cs i * ε *
          ((∫ ω, (stieltjesN (ouMat L W 0 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ (kk i)
            ∂(ouP L W)) +
            ∫ ω, (stieltjesN (ouMat L W t₁ ω)
              ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ (kk i) ∂(ouP L W))
        ≤ (∫ y, |Oj i y|) * A + Cs i * ε * (Nr ^ (τU / 2) + (Nr ^ (τU / 2) + A)) := by
          gcongr
      _ = (∫ y, |Oj i y|) * A + Cs i * (2 * (ε * Nr ^ (τU / 2)) + ε * A) := by ring
      _ ≤ (∫ y, |Oj i y|) * A + Cs i * (2 * Bt + A) := by
          rw [hεB]; gcongr; exact hCs0 i
      _ ≤ ((∫ y, |Oj i y|) + 2 * Cs i) * (A + Bt) := by
          nlinarith [hCs0 i]
  -- assemble
  have hE0 := gcc_kPoint_expand (ouP L W) (ouMat_isHermitian L W 0) c kk Oj hdec E
    (fun i => (hpiece i).1)
  have hE1 := gcc_kPoint_expand (ouP L W) (ouMat_isHermitian L W t₁) c kk Oj hdec E
    (fun i => (hpiece i).2.1)
  rw [hE0, hE1, ← mul_sub, ← Finset.sum_sub_distrib]
  have hp0 : 0 ≤ (Fintype.card (Idx L W) : ℝ) ^ k /
      ((Fintype.card (Idx L W)).descFactorial k : ℝ) := by positivity
  have hp : (Fintype.card (Idx L W) : ℝ) ^ k /
      ((Fintype.card (Idx L W)).descFactorial k : ℝ) ≤ 2 ^ k := gcc_prefactor_le h2k
  have hK0 : 0 ≤ ∑ i, |(c i : ℝ)| * ((∫ y, |Oj i y|) + 2 * Cs i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (integral_nonneg fun y => abs_nonneg _) (by linarith [hCs0 i]))
  have hsum : |∑ i, ((c i : ℝ) * (∫ ω, ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
        (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W 0 ω).eigenvalues (g j) - E))
        ∂(ouP L W)) -
      (c i : ℝ) * ∫ ω, ∑ g : Fin (kk i) → Idx L W, Oj i (fun j =>
        (Fintype.card (Idx L W) : ℝ) * ((ouMat_isHermitian L W t₁ ω).eigenvalues (g j) - E))
        ∂(ouP L W))| ≤
      (∑ i, |(c i : ℝ)| * ((∫ y, |Oj i y|) + 2 * Cs i)) * (A + Bt) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpiece i).2.2 (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg hp0]
  calc _ ≤ 2 ^ k * ((∑ i, |(c i : ℝ)| * ((∫ y, |Oj i y|) + 2 * Cs i)) * (A + Bt)) :=
        mul_le_mul hp hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Step

/-! ### The comparison along a size sequence -/

private theorem gcc_card_idx (d : Sizes) (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Idx, Z2, Sizes.size, ZMod.card, pow_two]

private theorem gcc_ouTStar_nonneg (d : Sizes) (τU : ℝ) (n : ℕ) : 0 ≤ ouTStar d τU n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **`(417)` and the a priori bound give the quantitative comparison**:
`|∫ kPoint(𝐇_0) − ∫ kPoint(𝐇_{t*})| ≤
K (N^{-c'+Cτ_U} + N^{-τ_U/2})` eventually, where `C` bounds `C_{n_f}`, `n_f ≤ k`. -/
private theorem gcc_quantitative (d : Sizes)
    (hsize : Tendsto (fun n => d.size n) atTop atTop) {E : ℝ} {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : InjSum_IsTestFun O) {τU c' C : ℝ} (Cn : ℕ → ℝ) (hτU : 0 < τU)
    (hCn : ∀ nf ≤ k, Cn nf ≤ C) (h417 : ∀ nf ≤ k, Claim417 d E nf τU c' (Cn nf))
    (hap : AprioriImM d E) :
    ∃ K : ℝ, ∀ᶠ n in atTop,
      |(∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) 0 ω).eigenvalues
            ∂(ouP (d.L n) (d.W n))) -
        ∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) (ouTStar d τU n) ω).eigenvalues
            ∂(ouP (d.L n) (d.W n))| ≤
        K * (((d.size n : ℕ) : ℝ) ^ (-c' + C * τU) + ((d.size n : ℕ) : ℝ) ^ (-(τU / 2))) := by
  -- a support radius `R ≥ 1`
  obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ x, O x ≠ 0 → ∀ j, |x j| ≤ R := by
    obtain ⟨r, hr⟩ := hO.2.isCompact.isBounded.subset_closedBall (0 : Fin k → ℝ)
    refine ⟨max r 1, le_max_right _ _, fun x hx j => ?_⟩
    have hxr := hr (subset_tsupport _ hx)
    rw [Metric.mem_closedBall, dist_zero_right] at hxr
    exact (norm_le_pi_norm x j).trans (hxr.trans (le_max_left _ _))
  obtain ⟨ι, hι, c, kk, Oj, hkk, hOj, hOjR, hdec⟩ := injSum_decomp k hO hR
  choose Cs hCs0 hCs using fun i => poissonSmooth_error (hOj i)
  refine ⟨2 ^ k * ∑ i, |(c i : ℝ)| * ((∫ y, |Oj i y|) + 2 * Cs i), ?_⟩
  have hC0 : (0 : ℝ) < R + 1 := by linarith
  have e1 := (eventually_all_finset (Finset.range (k + 1))).2 fun nn hnn =>
    h417 nn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hnn)) (R + 1) hC0
  have e2 := (eventually_all_finset (Finset.range (k + 1))).2 fun nn _ =>
    hap nn (τU / 2) (by positivity)
  have e3 : ∀ᶠ n in atTop, 2 * k ≤ d.size n := hsize.eventually_ge_atTop _
  filter_upwards [e1, e2, e3] with n hN1 hN2 hN3
  have hcardNat : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := gcc_card_idx d n
  have hcardN : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hpos : 0 < d.size n := hcardNat ▸ Fintype.card_pos
  have hNr1 : 1 ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hpos
  exact gcc_step (d.L n) (d.W n) (ouTStar d τU n) E Cn hτU hCn hC0 c kk Oj hkk hOj hOjR
    (fun lam => hdec (Idx (d.L n) (d.W n)) lam) Cs hCs0 hCs hcardN hNr1
    (by rw [hcardNat]; exact hN3)
    (fun nf hnf z hz => hN1 nf hnf z hz 0 le_rfl (gcc_ouTStar_nonneg d τU n))
    (fun nf hnf => hN2 nf hnf)

/-- `Cmax = max 0 (max_{n_f ≤ k} C_{n_f})`. -/
private def gccCmax (k : ℕ) (Cn : ℕ → ℝ) : ℝ :=
  max 0 ((Finset.range (k + 1)).sup' Finset.nonempty_range_add_one Cn)

private theorem gccCmax_nonneg (k : ℕ) (Cn : ℕ → ℝ) : 0 ≤ gccCmax k Cn := le_max_left _ _

private theorem le_gccCmax {k nf : ℕ} (Cn : ℕ → ℝ) (h : nf ≤ k) : Cn nf ≤ gccCmax k Cn :=
  (Finset.le_sup' Cn (Finset.mem_range.2 (Nat.lt_succ_of_le h))).trans (le_max_right _ _)

/-- **`GreenCorr` at the explicit threshold** `τ₀ = c' / (2 (Cmax + 1))`. -/
private theorem gcc_tendsto (d : Sizes) (hsize : Tendsto (fun n => d.size n) atTop atTop)
    {E : ℝ} {k : ℕ} {c' : ℝ} (hc' : 0 < c') (Cn : ℕ → ℝ) {τU : ℝ} (hτU : 0 < τU)
    (hτU0 : τU ≤ c' / (2 * (gccCmax k Cn + 1)))
    (h417 : ∀ nf ≤ k, Claim417 d E nf τU c' (Cn nf)) (hap : AprioriImM d E)
    {O : (Fin k → ℝ) → ℝ} (hOs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O)
    (hOc : HasCompactSupport O) :
    Tendsto (fun n =>
      (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) 0 ω).eigenvalues
          ∂(ouP (d.L n) (d.W n))) -
      (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) (ouTStar d τU n) ω).eigenvalues
          ∂(ouP (d.L n) (d.W n))))
      atTop (𝓝 0) := by
  have hC0 : 0 ≤ gccCmax k Cn := gccCmax_nonneg k Cn
  obtain ⟨K, hK⟩ := gcc_quantitative d hsize ⟨hOs, hOc⟩ Cn hτU (fun nf hnf => le_gccCmax Cn hnf)
    h417 hap
  -- `Cmax τ_U ≤ c'/2`
  have hCτ : gccCmax k Cn * τU ≤ c' / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (gccCmax k Cn + 1))).1 hτU0
    nlinarith
  have hN : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  have hA : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-c' + gccCmax k Cn * τU)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := c' - gccCmax k Cn * τU) (by linarith)).comp hN
    refine h.congr fun n => ?_
    simp only [Function.comp]
    congr 1
    ring
  have hB : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-(τU / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := τU / 2) (by positivity)).comp hN
    exact h
  have hlim : Tendsto (fun n => K * (((d.size n : ℕ) : ℝ) ^ (-c' + gccCmax k Cn * τU) +
      ((d.size n : ℕ) : ℝ) ^ (-(τU / 2)))) atTop (𝓝 0) := by
    simpa using (hA.add hB).const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hK] with n hn
  rwa [Real.norm_eq_abs]

/-- **The Green-function-to-correlation comparison** (the paragraph after `univ-main`): the
statement `GreenCorrAll`, proved from the Claim `(417)` and the a priori bound (`GreenCorr d` for
every size sequence with `size n → ∞`). -/
theorem greenCorrAll : GreenCorrAll := by
  intro d hsize E k c' hc' Cn
  refine ⟨c' / (2 * (gccCmax k Cn + 1)), by have := gccCmax_nonneg k Cn; positivity, ?_⟩
  intro τU hτU hτU0 h417 hap O hOs hOc
  exact gcc_tendsto d hsize hc' Cn hτU hτU0 h417 hap hOs hOc

end RBM.Univ

end
