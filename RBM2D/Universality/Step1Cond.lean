/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEInvariance
import RBM2D.Universality.EigenMeasurable
import RBM2D.Universality.OU
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Step 1 of Theorem 2.6: conditioning on the initial matrix, stationarity of `𝐇_∞`, rescaling
# and counting

Paper: arXiv:2503.07606, the OU marginal `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'` in the proof of
`Thm: B_Univ` and the two limits `1infyuniv` and `univ-main`.

* `integral_kPoint_ouMat_cond`: for any probability law `μ` of the first coordinate
  block, the expected `k`-point functional of `ouMat L W t` on `μ ⊗ gueP` is the `μ`-average of the
  `k`-point functional of the DBM matrix `diag(e^{-t/2} λ(X₁)) + √(1 - e^{-t}) X₂` on `gueP`.
* `gueP_prod_map_ouMat`: for `t ≥ 0`, `𝐇_t` has the GUE law when both blocks are GUE.
* `Step1Cond_gueMatPairing_eq_integral`: conditioning the GUE `k`-point functional on the first
  block of `gueP ⊗ gueP`.
* `Step1Cond_scaledPairing_lipschitz`, `Step1Cond_exists_dominating_testFun`,
  `Step1Cond_corrPairing_le_count`, `Step1Cond_exists_le_indicator`,
  `Step1Cond_corrPairing_le_count_smul`: rescaling and counting.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## Conditioning on the initial matrix -/

section Cond

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem Step1Cond_measurable_Xmat : Measurable (Xmat L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j

/-- The law of `a X + b Y` for independent centred Gaussians `X`, `Y`. -/
private theorem Step1Cond_pair_map (a b : ℝ) (v₁ v₂ : ℝ≥0) :
    ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      gaussianReal 0
        (NNReal.mk (a ^ 2) (sq_nonneg a) * v₁ + NNReal.mk (b ^ 2) (sq_nonneg b) * v₂) := by
  have h : (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun x : ℝ => a * x) (fun y : ℝ => b * y) := by
    funext p
    rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  have := gaussianReal_conv_gaussianReal (m₁ := a * 0) (m₂ := b * 0)
    (v₁ := NNReal.mk (a ^ 2) (sq_nonneg a) * v₁) (v₂ := NNReal.mk (b ^ 2) (sq_nonneg b) * v₂)
  rw [mul_zero] at this
  simpa [Measure.conv] using this

/-- The interpolated coordinates `e^{-t/2} ω₁ + √(1 - e^{-t}) ω₂` of two independent GUE
coordinate blocks have the GUE coordinate law (`t ≥ 0`): the finite-dimensional marginals are
products of Gaussians of variance `e^{-t} v_c + (1 - e^{-t}) v_c = v_c`.  Same computation as
`ouSample_law` with `gueP` in the first block. -/
private theorem Step1Cond_gue_interp_law {t : ℝ} (ht : 0 ≤ t) :
    ((gueP L W).prod (gueP L W)).map (ouSample L W t) =
      Measure.infinitePi (fun c => gaussianReal 0 (gueVar L W c)) := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hA : NNReal.mk (Real.exp (-t / 2) ^ 2) (sq_nonneg _) = (Real.exp (-t)).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ (Real.exp_pos _).le, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hB : NNReal.mk (Real.sqrt (1 - Real.exp (-t)) ^ 2) (sq_nonneg _) =
      (1 - Real.exp (-t)).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ (sub_nonneg.2 he)]
    exact Real.sq_sqrt (sub_nonneg.2 he)
  have hsum : (Real.exp (-t)).toNNReal + (1 - Real.exp (-t)).toNNReal = 1 := by
    rw [← Real.toNNReal_add (Real.exp_pos _).le (sub_nonneg.2 he), add_sub_cancel]
    exact Real.toNNReal_one
  refine IsProjectiveLimit.unique ?_
    (Measure.isProjectiveLimit_infinitePi (fun c => gaussianReal 0 (gueVar L W c)))
  intro I
  set a : ℝ := Real.exp (-t / 2) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-t)) with hb
  let f : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
  have hf : Measurable f := by fun_prop
  let R : (Ω L W × Ω L W) → (I → ℝ) × (I → ℝ) := Prod.map I.restrict I.restrict
  let g : (I → ℝ) × (I → ℝ) → (I → ℝ) := fun q i => a * q.1 i + b * q.2 i
  have hR : Measurable R := (Finset.measurable_restrict I).prodMap (Finset.measurable_restrict I)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun i => ?_
    have h1 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    have h2 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (h1.const_mul _).add (h2.const_mul _)
  have hcomp : (fun ω : Ω L W => I.restrict ω) ∘ ouSample L W t = g ∘ R := by
    funext ω
    rfl
  have hR_map : ((gueP L W).prod (gueP L W)).map R =
      (Measure.pi fun i : I => gaussianReal 0 (gueVar L W i)).prod
        (Measure.pi fun i : I => gaussianReal 0 (gueVar L W i)) := by
    have h2 : (gueP L W).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gueVar L W i) :=
      Measure.infinitePi_map_restrict _
    rw [← h2, Measure.map_prod_map _ _ (Finset.measurable_restrict I)
      (Finset.measurable_restrict I)]
  have he_map := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i : I => gaussianReal 0 (gueVar L W i))
    (fun i : I => gaussianReal 0 (gueVar L W i))).map_eq
  have hge : g ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) = fun x i => f (x i) := by
    funext x i
    rfl
  have : ∀ i : I, SigmaFinite
      (((gaussianReal 0 (gueVar L W i)).prod (gaussianReal 0 (gueVar L W i))).map f) :=
    fun i => by
      rw [Step1Cond_pair_map]
      infer_instance
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_ouSample L W t), hcomp,
    ← Measure.map_map hg hR, hR_map, ← he_map, Measure.map_map hg
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).measurable, hge,
    Measure.pi_map_pi (fun i => hf.aemeasurable)]
  congr 1
  funext i
  rw [Step1Cond_pair_map, hA, hB, ← add_mul, hsum, one_mul]

/-- **Stationarity of `𝐇_∞`**: with both blocks GUE, `𝐇_t = e^{-t/2} X₁ +
√(1 - e^{-t}) X₂` has the GUE law for `t ≥ 0`. -/
theorem gueP_prod_map_ouMat (L W : ℕ) [NeZero L] [NeZero W] (t : ℝ) (ht : 0 ≤ t) :
    ((gueP L W).prod (gueP L W)).map (ouMat L W t) = (gueP L W).map (Xmat L W) := by
  have h : ouMat L W t = Xmat L W ∘ ouSample L W t :=
    funext (ouMat_eq_Xmat_ouSample L W t)
  rw [h, ← Measure.map_map (Step1Cond_measurable_Xmat L W) (measurable_ouSample L W t),
    Step1Cond_gue_interp_law L W ht]
  rfl

/-- Conjugation by a fixed unitary matrix does not change the `k`-point functional of the
spectrum (equal characteristic polynomials, hence equal `IsHermitian.eigenvalues`). -/
private theorem Step1Cond_kPoint_conj {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {H H' : Matrix n n ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (hconj : H' = Uᴴ * H * U) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    kPoint k O E hH'.eigenvalues = kPoint k O E hH.eigenvalues := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hchar : H'.charpoly = H.charpoly := by
    rw [hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have heig : hH'.eigenvalues = hH.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hH' hH).mpr hchar
  rw [heig]

/-- The inner (conditional) identity at a fixed first sample `x`: spectral theorem
`Xmat x = V D Vᴴ`, conjugation by `V`, and the unitary invariance `gueP_map_unitary_conj`.  The
energy shift is carried by `E` inside `kPoint`. -/
private theorem Step1Cond_inner_eq (t : ℝ) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : Continuous O)
    (E : ℝ) (x : Ω L W) :
    ∫ y, kPoint k O E (ouMat_isHermitian L W t (x, y)).eigenvalues ∂(gueP L W) =
      ∫ y, kPoint k O E
        (dbmMat_isHermitian L W
          (fun i => Real.exp (-t / 2) * (Xmat_isHermitian L W x).eigenvalues i)
          (1 - Real.exp (-t)) y).eigenvalues ∂(gueP L W) := by
  set hX := Xmat_isHermitian L W x with hX_def
  set V : Matrix (Idx L W) (Idx L W) ℂ :=
    (hX.eigenvectorUnitary : Matrix (Idx L W) (Idx L W) ℂ) with hV_def
  have hV : V ∈ Matrix.unitaryGroup (Idx L W) ℂ := hX.eigenvectorUnitary.2
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  set D : Matrix (Idx L W) (Idx L W) ℂ := Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))
    with hD_def
  have hXeq : Xmat L W x = V * D * Vᴴ := by
    have hspec := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hspec
    have hDeq : Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) =
        Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
      congr 1
    rw [hDeq] at hspec
    exact hspec
  have hVXV : Vᴴ * Xmat L W x * V = D := by
    rw [hXeq, show Vᴴ * (V * D * Vᴴ) * V = (Vᴴ * V) * D * (Vᴴ * V) by
      simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  set v : Idx L W → ℝ := fun i => Real.exp (-t / 2) * hX.eigenvalues i with hv_def
  let K : Ω L W → Matrix (Idx L W) (Idx L W) ℂ := fun y =>
    Matrix.diagonal (fun i => (v i : ℂ)) +
      Real.sqrt (1 - Real.exp (-t)) • (Vᴴ * Xmat L W y * V)
  have hK : ∀ y, K y = Vᴴ * ouMat L W t (x, y) * V := by
    intro y
    have hdiag : Matrix.diagonal (fun i => (v i : ℂ)) = Real.exp (-t / 2) • D := by
      ext i j
      rw [hD_def]
      by_cases hij : i = j
      · subst hij; simp [hv_def]
      · simp [Matrix.diagonal_apply_ne _ hij]
    change Matrix.diagonal (fun i => (v i : ℂ)) +
      Real.sqrt (1 - Real.exp (-t)) • (Vᴴ * Xmat L W y * V) =
      Vᴴ * (Real.exp (-t / 2) • Xmat L W x + Real.sqrt (1 - Real.exp (-t)) • Xmat L W y) * V
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, hVXV, hdiag]
  have hKh : ∀ y, (K y).IsHermitian := by
    intro y
    rw [hK y]
    exact Matrix.isHermitian_conjTranspose_mul_mul V (ouMat_isHermitian L W t (x, y))
  -- the spectra of `K y` and `ouMat t (x, y)` agree
  have hpt : ∀ y, kPoint k O E (hKh y).eigenvalues =
      kPoint k O E (ouMat_isHermitian L W t (x, y)).eigenvalues := fun y =>
    Step1Cond_kPoint_conj hV (ouMat_isHermitian L W t (x, y)) (hKh y) (hK y) k O E
  -- law of `K` is the law of `dbmMat v (1 - e^{-t})`
  have hcont : Continuous (fun Y : Matrix (Idx L W) (Idx L W) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt (1 - Real.exp (-t)) • Y) := by
    fun_prop
  have hmeasV : Measurable (fun y => Vᴴ * Xmat L W y * V) := by
    have hc : Continuous (fun Y : Matrix (Idx L W) (Idx L W) ℂ => Vᴴ * Y * V) := by fun_prop
    exact hc.measurable.comp (Step1Cond_measurable_Xmat L W)
  have hfun1 : K = (fun Y => Matrix.diagonal (fun i => (v i : ℂ)) +
      Real.sqrt (1 - Real.exp (-t)) • Y) ∘ (fun y => Vᴴ * Xmat L W y * V) := rfl
  have hfun2 : dbmMat L W v (1 - Real.exp (-t)) = (fun Y => Matrix.diagonal (fun i => (v i : ℂ)) +
      Real.sqrt (1 - Real.exp (-t)) • Y) ∘ (Xmat L W) := rfl
  have hVstar : star V ∈ Matrix.unitaryGroup (Idx L W) ℂ := Unitary.star_mem hV
  have hconj : (gueP L W).map (fun y => Vᴴ * Xmat L W y * V) = (gueP L W).map (Xmat L W) := by
    have h := gueP_map_unitary_conj L W (star V) hVstar
    simpa only [star_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h
  have hlaw : (gueP L W).map K = (gueP L W).map (dbmMat L W v (1 - Real.exp (-t))) := by
    rw [hfun1, hfun2, ← Measure.map_map hcont.measurable hmeasV,
      ← Measure.map_map hcont.measurable (Step1Cond_measurable_Xmat L W), hconj]
  have hKmeas : Measurable K := hcont.measurable.comp hmeasV
  have hDmeas : Measurable (dbmMat L W v (1 - Real.exp (-t))) :=
    hcont.measurable.comp (Step1Cond_measurable_Xmat L W)
  calc ∫ y, kPoint k O E (ouMat_isHermitian L W t (x, y)).eigenvalues ∂(gueP L W)
      = ∫ y, kPoint k O E (hKh y).eigenvalues ∂(gueP L W) :=
        integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    _ = ∫ y, kPoint k O E
          (dbmMat_isHermitian L W v (1 - Real.exp (-t)) y).eigenvalues ∂(gueP L W) :=
        integral_kPoint_eq_of_map_eq (gueP L W) (gueP L W) K (dbmMat L W v (1 - Real.exp (-t)))
          hKh (dbmMat_isHermitian L W v (1 - Real.exp (-t))) hKmeas hDmeas hlaw k O hO E

end Cond

/-- **Conditioning on the initial matrix**: for any probability law `μ` of the first
coordinate block, the expected `k`-point functional of `𝐇_t = e^{-t/2} X₁ + √(1 - e^{-t}) X₂`
(`X₂` GUE) equals the `μ`-average of the same functional of `diag(e^{-t/2} λ(X₁)) +
√(1 - e^{-t}) X₂`.  At `μ = P L W` the left side is the `ouP` functional.
Fubini on `μ.prod gueP` (the integrand is bounded since `O` is continuous with compact support),
then `Step1Cond_inner_eq` at each `ω₁`. -/
theorem integral_kPoint_ouMat_cond (L W : ℕ) [NeZero L] [NeZero W]
    (μ : Measure (Ω L W)) [IsProbabilityMeasure μ] (t : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (hOc : HasCompactSupport O) (E : ℝ) :
    ∫ ω, kPoint k O E (ouMat_isHermitian L W t ω).eigenvalues ∂(μ.prod (gueP L W)) =
      ∫ ω₁, (∫ ω₂, kPoint k O E
          (dbmMat_isHermitian L W
            (fun i => Real.exp (-t / 2) * (Xmat_isHermitian L W ω₁).eigenvalues i)
            (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP L W)) ∂μ := by
  obtain ⟨B, hB⟩ := hOc.exists_bound_of_continuous hO
  let F : Ω L W × Ω L W → ℝ := fun p => kPoint k O E (ouMat_isHermitian L W t p).eigenvalues
  have hmeasF : Measurable F :=
    measurable_kPoint_eigenvalues (ouMat L W t) (ouMat_isHermitian L W t)
      (measurable_ouMat L W t) k O hO E
  set C₀ : ℝ := (Fintype.card (Idx L W) : ℝ) ^ k /
    ((Fintype.card (Idx L W)).descFactorial k : ℝ) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hint : Integrable F (μ.prod (gueP L W)) := by
    refine Integrable.of_bound hmeasF.aestronglyMeasurable
      (C₀ * ((Fintype.card (Fin k ↪ Idx L W) : ℝ) * B)) (Eventually.of_forall fun p => ?_)
    change ‖C₀ * ∑ f : Fin k ↪ Idx L W, O (fun j => (Fintype.card (Idx L W) : ℝ) *
      ((ouMat_isHermitian L W t p).eigenvalues (f j) - E))‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg hC₀0]
    refine mul_le_mul_of_nonneg_left ?_ hC₀0
    calc ‖∑ f : Fin k ↪ Idx L W, O (fun j => (Fintype.card (Idx L W) : ℝ) *
          ((ouMat_isHermitian L W t p).eigenvalues (f j) - E))‖
        ≤ ∑ f : Fin k ↪ Idx L W, ‖O (fun j => (Fintype.card (Idx L W) : ℝ) *
          ((ouMat_isHermitian L W t p).eigenvalues (f j) - E))‖ := norm_sum_le _ _
      _ ≤ ∑ _f : Fin k ↪ Idx L W, B := Finset.sum_le_sum fun f _ => hB _
      _ = (Fintype.card (Fin k ↪ Idx L W) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∫ ω, kPoint k O E (ouMat_isHermitian L W t ω).eigenvalues ∂(μ.prod (gueP L W))
      = ∫ x, ∫ y, F (x, y) ∂(gueP L W) ∂μ := integral_prod F hint
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => Step1Cond_inner_eq L W t k hO E x)

/-- **Conditioning the GUE `k`-point functional on the first block of `gueP ⊗ gueP`**, through
`gueP_prod_map_ouMat` and `integral_kPoint_ouMat_cond` at `μ = gueP L W`.  The functional is
`∫ kPoint k O E₀ (Xmat_isHermitian ω).eigenvalues ∂gueP`; the energy shift is carried by the
single energy `E` inside `kPoint`. -/
theorem Step1Cond_gueMatPairing_eq_integral (L W : ℕ) [NeZero L] [NeZero W] {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) (E : ℝ) :
    ∫ ω, kPoint k O E (Xmat_isHermitian L W ω).eigenvalues ∂(gueP L W) =
      ∫ ω₁, (∫ ω₂, kPoint k O E
          (dbmMat_isHermitian L W
            (fun i => Real.exp (-t / 2) * (Xmat_isHermitian L W ω₁).eigenvalues i)
            (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP L W)) ∂(gueP L W) := by
  have hlaw := integral_kPoint_eq_of_map_eq (gueP L W) ((gueP L W).prod (gueP L W))
    (Xmat L W) (ouMat L W t) (Xmat_isHermitian L W) (ouMat_isHermitian L W t)
    (Step1Cond_measurable_Xmat L W) (measurable_ouMat L W t)
    (gueP_prod_map_ouMat L W t ht).symm k O hO.1.continuous E
  exact hlaw.trans (integral_kPoint_ouMat_cond L W (gueP L W) t k O hO.1.continuous hO.2 E)

/-! ## Rescaling and counting

Vocabulary: `corrPairing Pm Hm hH k O E` is `∫ ω, kPoint k O E (hH ω).eigenvalues ∂Pm`,
`IsTestFun O` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O`, and
`scaledPairing Pm Hm hH k O E ρ` is
`ρ ^ k * ∫ ω, kPoint k (fun β => O (fun j => ρ * β j)) E (hH ω).eigenvalues ∂Pm`. -/

section Rescale

open Metric Set

/-! ### Elementary facts about test functions -/

/-- A test function vanishes outside a closed ball. File-stem-prefixed helper. -/
private theorem Step1Cond_exists_support_radius {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) :
    ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ x, R0 < ‖x‖ → O x = 0 := by
  obtain ⟨R, hR⟩ := hO.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h := hR hmem
  rw [mem_closedBall, dist_zero_right] at h
  linarith [le_max_left R 0]

/-- A smooth bump on `Fin k → ℝ` equal to `1` on `closedBall 0 r`. File-stem-prefixed helper. -/
private theorem Step1Cond_exists_bump {k : ℕ} (r : ℝ) :
    ∃ Q : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) ∧
      0 ≤ Q ∧ ∀ x, ‖x‖ ≤ r → Q x = 1 := by
  let b : ContDiffBump (0 : Fin k → ℝ) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, fun x => b.nonneg, fun x hx => ?_⟩
  apply b.one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ max r 0 + 1
  linarith [le_max_left r 0]

/-- Integrability of a correlation sum with a bounded continuous test function.
File-stem-prefixed helper. -/
private theorem Step1Cond_integrable_corrSum {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) {B : ℝ} (hB : ∀ x, ‖O x‖ ≤ B) (c E : ℝ) :
    Integrable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) Pm := by
  refine Integrable.of_bound (measurable_corrSum hm hH k hO c E).aestronglyMeasurable
    ((Finset.univ : Finset (Fin k ↪ n)).card * B) (Eventually.of_forall fun ω => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun f _ => hB _).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ### `Step1Cond_scaledPairing_lipschitz` -/

/-- The pointwise Lipschitz bound behind `Step1Cond_scaledPairing_lipschitz`.
File-stem-prefixed helper. -/
private theorem Step1Cond_pointwise_lipschitz {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) {ρmin ρmax : ℝ}
    (h0 : 0 < ρmin) :
    ∃ Q : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) ∧
      0 ≤ Q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Fin k → ℝ, ∀ ρ ρ' : ℝ, ρ ∈ Icc ρmin ρmax → ρ' ∈ Icc ρmin ρmax →
        |ρ ^ k * O (fun j => ρ * x j) - ρ' ^ k * O (fun j => ρ' * x j)| ≤
          C * |ρ - ρ'| * Q x := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Cond_exists_support_radius hO
  obtain ⟨B0, hB0⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  obtain ⟨B1, hB1⟩ := (hO.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hO.2.fderiv (𝕜 := ℝ))
  have hdiff : Differentiable ℝ O := hO.1.differentiable (by simp)
  set R1 : ℝ := R0 / ρmin with hR1def
  have hR1 : 0 ≤ R1 := div_nonneg hR0 h0.le
  obtain ⟨Q, hQ, hQ0, hQ1⟩ := Step1Cond_exists_bump (k := k) R1
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  have hB1' : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  set C : ℝ := k * |ρmax| ^ (k - 1) * B0 + |ρmax| ^ k * B1 * R1 with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨Q, hQ, hQ0, C, hC, fun x ρ ρ' hρ hρ' => ?_⟩
  have hsx : ∀ s : ℝ, (fun j => s * x j) = s • x := fun s => rfl
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖s • x‖ = s * ‖x‖ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  by_cases hx : ‖x‖ ≤ R1
  · rw [hQ1 x hx, mul_one, hsx ρ, hsx ρ']
    set φ : ℝ → ℝ := fun s => s ^ k * O (s • x) with hφ
    set φ' : ℝ → ℝ := fun s =>
      (k : ℝ) * s ^ (k - 1) * O (s • x) + s ^ k * (fderiv ℝ O (s • x) ((1 : ℝ) • x)) with hφ'
    have hder : ∀ s ∈ Icc ρmin ρmax, HasDerivWithinAt φ (φ' s) (Icc ρmin ρmax) s := by
      intro s _
      have hg : HasDerivAt (fun y : ℝ => y • x) ((1 : ℝ) • x) s := (hasDerivAt_id s).smul_const x
      have hcomp : HasDerivAt (fun y : ℝ => O (y • x)) (fderiv ℝ O (s • x) ((1 : ℝ) • x)) s :=
        (hdiff (s • x)).hasFDerivAt.comp_hasDerivAt s hg
      exact ((hasDerivAt_pow k s).mul hcomp).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc ρmin ρmax, ‖φ' s‖ ≤ C := by
      intro s hs
      have hs0 : 0 ≤ s := h0.le.trans hs.1
      have hsm : s ≤ |ρmax| := hs.2.trans (le_abs_self _)
      have h1 : |s ^ (k - 1)| ≤ |ρmax| ^ (k - 1) := by
        rw [abs_of_nonneg (pow_nonneg hs0 _)]; exact pow_le_pow_left₀ hs0 hsm _
      have h2 : |s ^ k| ≤ |ρmax| ^ k := by
        rw [abs_of_nonneg (pow_nonneg hs0 _)]; exact pow_le_pow_left₀ hs0 hsm _
      have h3 : |O (s • x)| ≤ B0 := by simpa [Real.norm_eq_abs] using hB0 (s • x)
      have h4 : |fderiv ℝ O (s • x) ((1 : ℝ) • x)| ≤ B1 * R1 := by
        rw [← Real.norm_eq_abs, one_smul]
        refine ((fderiv ℝ O (s • x)).le_opNorm x).trans ?_
        exact mul_le_mul (hB1 _) hx (norm_nonneg _) hB1'
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e1 : (k : ℝ) * |s ^ (k - 1)| * |O (s • x)| ≤ k * |ρmax| ^ (k - 1) * B0 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hk) h3 (abs_nonneg _) (by positivity)
      have e2 : |s ^ k| * |fderiv ℝ O (s • x) ((1 : ℝ) • x)| ≤ |ρmax| ^ k * B1 * R1 := by
        rw [mul_assoc]; exact mul_le_mul h2 h4 (abs_nonneg _) (by positivity)
      rw [hCdef]; linarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
      (convex_Icc ρmin ρmax) hρ' hρ
    simpa [hφ, Real.norm_eq_abs] using hmvt
  · push Not at hx
    have hzero : ∀ s ∈ Icc ρmin ρmax, O (s • x) = 0 := by
      intro s hs
      apply hsupp
      rw [hnorm s (h0.le.trans hs.1)]
      have hR0eq : ρmin * R1 = R0 := by rw [hR1def]; field_simp
      calc R0 = ρmin * R1 := hR0eq.symm
        _ < ρmin * ‖x‖ := mul_lt_mul_of_pos_left hx h0
        _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)
    rw [hsx ρ, hsx ρ', hzero ρ hρ, hzero ρ' hρ']
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (abs_nonneg _)) (hQ0 x)

/-- **Lipschitz dependence** of the `ρ`-rescaled pairing on `ρ ∈ [ρmin, ρmax]`,
with the Lipschitz factor a fixed multiple of an unrescaled pairing against a nonnegative test
function `Q`. `Q` and `C` depend only on `k, O, ρmin, ρmax` (fixed before the measure). -/
theorem Step1Cond_scaledPairing_lipschitz {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O)
    {ρmin ρmax : ℝ} (h0 : 0 < ρmin) (h1 : ρmin ≤ ρmax) :
    ∃ Q : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) ∧
      0 ≤ Q ∧ ∃ C : ℝ, ∀ {Ω' : Type}
      [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type} [Fintype n]
      [DecidableEq n] (Hm : Ω' → Matrix n n ℂ), Measurable Hm → ∀ (hH : ∀ ω, (Hm ω).IsHermitian)
      (E ρ ρ' : ℝ), ρ ∈ Set.Icc ρmin ρmax → ρ' ∈ Set.Icc ρmin ρmax →
        |ρ ^ k * (∫ ω, kPoint k (fun β => O (fun j => ρ * β j)) E (hH ω).eigenvalues ∂Pm) -
            ρ' ^ k * (∫ ω, kPoint k (fun β => O (fun j => ρ' * β j)) E (hH ω).eigenvalues ∂Pm)| ≤
          C * |ρ - ρ'| * ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm := by
  have _hne : ρmin ≤ ρmax := h1
  obtain ⟨Q, hQ, hQ0, C, hC, hpt⟩ := Step1Cond_pointwise_lipschitz hO (ρmax := ρmax) h0
  refine ⟨Q, hQ, hQ0, C, ?_⟩
  intro Ω' _ Pm _ n _ _ Hm hm hH E ρ ρ' hρ hρ'
  obtain ⟨B0, hB0⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hcontρ : ∀ r : ℝ, Continuous (fun β : Fin k → ℝ => O (fun j => r * β j)) := fun r =>
    hO.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
  have hboundρ : ∀ r : ℝ, ∀ β : Fin k → ℝ, ‖O (fun j => r * β j)‖ ≤ B0 := fun r β => hB0 _
  have hIρ := Step1Cond_integrable_corrSum Pm hm hH k (hcontρ ρ) (hboundρ ρ)
    (Fintype.card n : ℝ) E
  have hIρ' := Step1Cond_integrable_corrSum Pm hm hH k (hcontρ ρ') (hboundρ ρ')
    (Fintype.card n : ℝ) E
  have hIQ := Step1Cond_integrable_corrSum Pm hm hH k hQ.1.continuous hBQ
    (Fintype.card n : ℝ) E
  set c : ℝ := (Fintype.card n : ℝ) ^ k / ((Fintype.card n).descFactorial k : ℝ) with hcdef
  have hc : 0 ≤ c := by positivity
  have hkP : ∀ O' : (Fin k → ℝ) → ℝ, ∫ ω, kPoint k O' E (hH ω).eigenvalues ∂Pm =
      c * ∫ ω, ∑ f : Fin k ↪ n,
        O' (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) ∂Pm :=
    fun O' => integral_const_mul c _
  set A : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    O (fun j => ρ * ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E))) with hA
  set B : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    O (fun j => ρ' * ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E))) with hB
  set S : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    Q (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) with hS
  rw [hkP (fun β => O (fun j => ρ * β j)), hkP (fun β => O (fun j => ρ' * β j)), hkP Q]
  change |ρ ^ k * (c * ∫ ω, A ω ∂Pm) - ρ' ^ k * (c * ∫ ω, B ω ∂Pm)| ≤
    C * |ρ - ρ'| * (c * ∫ ω, S ω ∂Pm)
  have hdiff : ρ ^ k * ∫ ω, A ω ∂Pm - ρ' ^ k * ∫ ω, B ω ∂Pm =
      ∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm := by
    rw [integral_sub (hIρ.const_mul _) (hIρ'.const_mul _), integral_const_mul, integral_const_mul]
  have hle : |∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm| ≤ ∫ ω, C * |ρ - ρ'| * S ω ∂Pm := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hIQ.const_mul _) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [hA, hB, hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun f _ => hpt _ ρ ρ' hρ hρ')
  have hrw : ρ ^ k * (c * ∫ ω, A ω ∂Pm) - ρ' ^ k * (c * ∫ ω, B ω ∂Pm) =
      c * (ρ ^ k * ∫ ω, A ω ∂Pm - ρ' ^ k * ∫ ω, B ω ∂Pm) := by ring
  rw [hrw, abs_mul, abs_of_nonneg hc, hdiff]
  calc c * |∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm| ≤ c * (C * |ρ - ρ'| * ∫ ω, S ω ∂Pm) :=
        mul_le_mul_of_nonneg_left (hle.trans_eq (integral_const_mul _ _)) hc
    _ = C * |ρ - ρ'| * (c * ∫ ω, S ω ∂Pm) := by ring

/-! ### `Step1Cond_exists_dominating_testFun` -/

/-- **A dominating test function**: a nonnegative test function `Q'` dominating `Q` after every
dilation
`β ↦ ρ β` with `ρ ∈ [ρmin, ρmax]`: `Q β ≤ Q' (ρ β)`. (No sign condition on `ρmin, ρmax` is
needed.) -/
theorem Step1Cond_exists_dominating_testFun {k : ℕ} {Q : (Fin k → ℝ) → ℝ}
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q)
    (ρmin ρmax : ℝ) :
    ∃ Q' : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q' ∧ HasCompactSupport Q') ∧
      0 ≤ Q' ∧
      ∀ ρ ∈ Set.Icc ρmin ρmax, ∀ β : Fin k → ℝ, Q β ≤ Q' (fun j => ρ * β j) := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Cond_exists_support_radius hQ
  obtain ⟨B0, hB0⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  set ρbar : ℝ := max |ρmin| |ρmax|
  obtain ⟨b, hb, hb0, hb1⟩ := Step1Cond_exists_bump (k := k) (ρbar * R0)
  refine ⟨fun y => B0 * b y, ⟨contDiff_const.mul hb.1, hb.2.mul_left⟩,
    fun y => mul_nonneg hB0' (hb0 y), fun ρ hρ β => ?_⟩
  by_cases hβ : ‖β‖ ≤ R0
  · have hρabs : |ρ| ≤ ρbar := by
      rcases le_or_gt 0 ρ with h | h
      · rw [abs_of_nonneg h]; exact (hρ.2.trans (le_abs_self _)).trans (le_max_right _ _)
      · rw [abs_of_neg h]
        exact (neg_le_neg hρ.1 |>.trans (neg_le_abs _)).trans (le_max_left _ _)
    have hn : ‖(fun j => ρ * β j : Fin k → ℝ)‖ ≤ ρbar * R0 := by
      change ‖ρ • β‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hρabs hβ (norm_nonneg _) ((abs_nonneg _).trans hρabs)
    change Q β ≤ B0 * b (fun j => ρ * β j)
    rw [hb1 _ hn, mul_one]
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB0 β)
  · push Not at hβ
    rw [hsupp β hβ]
    exact mul_nonneg hB0' (hb0 _)

/-! ### `Step1Cond_corrPairing_le_count` -/

/-- Measurability of a single eigenvalue along a measurable, everywhere-Hermitian matrix map
(the same Weyl-bound argument as in `EigenMeasurable.lean`, whose helpers are private).
File-stem-prefixed helper. -/
private theorem Step1Cond_measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
    [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (i : n) : Measurable (fun ω => (hH ω).eigenvalues i) := by
  have hcont : Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      x.2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)) := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ _)
      (𝓝 x) (𝓝 (x.2.eigenvalues₀ _))
    rw [tendsto_iff_dist_tendsto_zero]
    have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
    have hc : Continuous (fun A : Matrix n n ℂ =>
        Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
      Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
    have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
        (𝓝 x.1) (𝓝 0) := by
      have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
      have := hc.continuousAt (x := x.1)
      rwa [ContinuousAt, hval] at this
    have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
        Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
      h0.comp (continuous_subtype_val.continuousAt (x := x))
    refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
    rw [Real.dist_eq]
    exact eigenvalues₀_abs_sub_le y.2 x.2 _
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have := hcont.measurable.comp hφ
  simpa [Matrix.IsHermitian.eigenvalues, Function.comp_def] using this

/-- The number of injective `k`-tuples with values in a finite set `S` is at most `|S|^k`.
File-stem-prefixed helper. -/
private theorem Step1Cond_card_embedding_filter_le {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (S : Finset n) :
    ((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card ≤ S.card ^ k := by
  calc ((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card
      ≤ (Fintype.piFinset (fun _ : Fin k => S)).card := by
        refine Finset.card_le_card_of_injOn (fun f => ⇑f) (fun f hf => ?_) ?_
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
          simpa [Fintype.mem_piFinset] using hf
        · intro f _ g _ hfg
          exact DFunLike.coe_injective hfg
    _ = S.card ^ k := by simp [Fintype.card_piFinset]

/-- The normalization `M^k / M.descFactorial k` of `kPoint` is at most `(M/(M-k))^k` for `k < M`.
File-stem-prefixed helper. -/
private theorem Step1Cond_prefactor_le {M k : ℕ} (hk : k < M) :
    (M : ℝ) ^ k / (M.descFactorial k : ℝ) ≤ ((M : ℝ) / ((M : ℝ) - k)) ^ k := by
  have hMk : (0 : ℝ) < (M : ℝ) - k := by
    have : (k : ℝ) < M := by exact_mod_cast hk
    linarith
  have hdesc : ((M : ℝ) - k) ^ k ≤ (M.descFactorial k : ℝ) := by
    have h1 : (M - k) ^ k ≤ M.descFactorial k :=
      (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_sub_le_descFactorial M k)
    have h2 : (((M - k : ℕ) : ℝ)) = (M : ℝ) - k := by rw [Nat.cast_sub hk.le]
    rw [← h2]; exact_mod_cast h1
  have hdpos : (0 : ℝ) < ((M : ℝ) - k) ^ k := pow_pos hMk k
  rw [div_pow]
  exact div_le_div_of_nonneg_left (by positivity) hdpos hdesc

/-- **Counting bound**: for `0 ≤ Q ≤ 1_{[-R,R]^k}` and `k < M`, the pairing is bounded by the
`k`-th moment of the number of eigenvalues in the window `[E - R/M, E + R/M]`:
`corrPairing … k Q E ≤ (M/(M-k))^k · E[#{i : |λ_i - E| ≤ R/M}^k]`. -/
theorem Step1Cond_corrPairing_le_count {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (hk : k < Fintype.card n)
    {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {R : ℝ}
    (hQR : ∀ β, Q β ≤ Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm ≤
      ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm := by
  set M : ℕ := Fintype.card n with hMdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  set cnt : Ω' → ℝ := fun ω => (((Finset.univ : Finset n).filter
    (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ))).card : ℝ) ^ k with hcnt
  -- measurability and integrability of the count
  have hcnt_meas : Measurable cnt := by
    have heq : cnt = fun ω => (∑ i : n,
        if |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ) then (1 : ℝ) else 0) ^ k := by
      funext ω; simp only [hcnt, Finset.natCast_card_filter]
    rw [heq]
    refine Measurable.pow_const (Finset.measurable_sum _ fun i _ => ?_) k
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le
      (continuous_abs.measurable.comp
        ((Step1Cond_measurable_eigenvalue hm hH i).sub_const E)) measurable_const
  have hcnt_int : Integrable cnt Pm := by
    refine Integrable.of_bound hcnt_meas.aestronglyMeasurable ((M : ℝ) ^ k)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have := Finset.card_filter_le (Finset.univ : Finset n)
      (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ))
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have hcnt_nonneg : ∀ ω, 0 ≤ cnt ω := fun ω => by positivity
  -- the pointwise count bound
  have hpt : ∀ ω, (∑ f : Fin k ↪ n,
      Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ≤ cnt ω := by
    intro ω
    set S : Finset n := (Finset.univ : Finset n).filter
      (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ)) with hSdef
    have hmem : ∀ i, (M : ℝ) * ((hH ω).eigenvalues i - E) ∈ Set.Icc (-R) R ↔ i ∈ S := by
      intro i
      rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos hMpos, hSdef, Finset.mem_filter,
        le_div_iff₀ hMpos]
      rw [mul_comm]
      simp
    calc (∑ f : Fin k ↪ n, Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E)))
        ≤ ∑ f : Fin k ↪ n, (if ∀ j, f j ∈ S then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun f _ => (hQR _).trans_eq ?_
          by_cases h : ∀ j, f j ∈ S
          · rw [Set.indicator_of_mem
              (Set.mem_univ_pi.mpr fun j => (hmem (f j)).mpr (h j))]
            simp [h]
          · rw [Set.indicator_of_notMem
              (fun hc => h fun j => (hmem (f j)).mp (Set.mem_univ_pi.mp hc j))]
            simp [h]
      _ = (((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card : ℝ) := by
          rw [Finset.natCast_card_filter]
      _ ≤ ((S.card ^ k : ℕ) : ℝ) := by
          exact_mod_cast Step1Cond_card_embedding_filter_le k S
      _ = cnt ω := by simp only [hcnt, hSdef, Nat.cast_pow]
  -- integrate
  have hint : ∫ ω, (∑ f : Fin k ↪ n,
      Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ∂Pm ≤ ∫ ω, cnt ω ∂Pm :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun f _ => hQ0 _) hcnt_int
      (Eventually.of_forall hpt)
  have hpre := Step1Cond_prefactor_le hk
  have hint0 : 0 ≤ ∫ ω, cnt ω ∂Pm := integral_nonneg hcnt_nonneg
  have hkP : ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm = (M : ℝ) ^ k / (M.descFactorial k : ℝ) *
      ∫ ω, (∑ f : Fin k ↪ n, Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ∂Pm :=
    integral_const_mul _ _
  rw [hkP]
  exact mul_le_mul hpre hint (integral_nonneg fun ω => Finset.sum_nonneg fun f _ => hQ0 _)
    (pow_nonneg (div_nonneg hMpos.le (by
      have : (k : ℝ) < M := by exact_mod_cast hk
      linarith)) k)

/-! ### Public forms (file-stem prefixed): bounds by box indicators -/

/-- A test function is bounded by a positive multiple of the indicator of a box `[-R,R]^k`.
Used to feed `Step1Cond_corrPairing_le_count` and `Step1Cond_corrPairing_le_count_smul` with a
dominating test function. -/
theorem Step1Cond_exists_le_indicator {k : ℕ} {Q : (Fin k → ℝ) → ℝ}
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) :
    ∃ B R : ℝ, 0 < B ∧ 0 ≤ R ∧ ∀ β, Q β ≤ B * Set.indicator
      (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R) (fun _ => (1 : ℝ)) β := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Cond_exists_support_radius hQ
  obtain ⟨B0, hB0⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  refine ⟨B0 + 1, R0, by linarith, hR0, fun β => ?_⟩
  by_cases hβ : ‖β‖ ≤ R0
  · have hmem : β ∈ Set.univ.pi fun _ : Fin k => Set.Icc (-R0) R0 := by
      refine Set.mem_univ_pi.mpr fun j => ?_
      rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm β j).trans hβ
    rw [Set.indicator_of_mem hmem, mul_one]
    have := (le_abs_self (Q β)).trans (by simpa [Real.norm_eq_abs] using hB0 β)
    linarith
  · push Not at hβ
    rw [hsupp β hβ]
    exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `Step1Cond_corrPairing_le_count` with a general height: for `0 ≤ Q ≤ B · 1_{[-R,R]^k}`, `0 < B`,
`k < M`: `corrPairing … k Q E ≤ B (M/(M-k))^k · E[#{i : |λ_i - E| ≤ R/M}^k]`. -/
theorem Step1Cond_corrPairing_le_count_smul {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Ω' → Matrix n n ℂ) (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    (hk : k < Fintype.card n) {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {B R : ℝ} (hB : 0 < B)
    (hQR : ∀ β, Q β ≤ B * Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm ≤
      B * ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm := by
  have h := Step1Cond_corrPairing_le_count Pm Hm hm hH k hk (Q := fun β => B⁻¹ * Q β)
    (fun β => mul_nonneg (inv_nonneg.mpr hB.le) (hQ0 β)) (R := R)
    (fun β => by
      rw [inv_mul_le_iff₀ hB]; exact hQR β) E
  have hlin : ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm =
      B * ∫ ω, kPoint k (fun β => B⁻¹ * Q β) E (hH ω).eigenvalues ∂Pm := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [kPoint, ← Finset.mul_sum]
    field_simp
  rw [hlin, mul_assoc B]
  exact mul_le_mul_of_nonneg_left h hB.le


end Rescale

end RBM.Univ

/-! ## A bump test function -/

namespace RBM.Univ.Step1CondCheck

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-- The statement of `integral_kPoint_ouMat_cond` as a closed proposition. -/
def T1Stmt : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (μ : Measure (RBM.Gauss.Ω L W)) [IsProbabilityMeasure μ]
    (t : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), Continuous O → HasCompactSupport O → ∀ E : ℝ,
    ∫ ω, RBM.Endpoints.kPoint k O E (RBM.Univ.ouMat_isHermitian L W t ω).eigenvalues
        ∂(μ.prod (RBM.Endpoints.gueP L W)) =
      ∫ ω₁, (∫ ω₂, RBM.Endpoints.kPoint k O E
          (RBM.Univ.dbmMat_isHermitian L W
            (fun i => Real.exp (-t / 2) * (RBM.Gauss.Xmat_isHermitian L W ω₁).eigenvalues i)
            (1 - Real.exp (-t)) ω₂).eigenvalues ∂(RBM.Endpoints.gueP L W)) ∂μ

/-- A smooth bump on `Fin 1 → ℝ`, `1` on the ball of radius `1`, supported in radius `2`. -/
def bump : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bump_testFun :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump : (Fin 1 → ℝ) → ℝ) ∧
      HasCompactSupport (bump : (Fin 1 → ℝ) → ℝ) :=
  ⟨bump.contDiff, bump.hasCompactSupport⟩

end RBM.Univ.Step1CondCheck

end
