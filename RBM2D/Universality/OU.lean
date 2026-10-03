/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins

/-!
# The OU carrier facts

The matrix OU marginal `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'` of `ouMat` is the Hermitian matrix
`Xmat` of the interpolated coordinates `ouSample`; under `ouP` its coordinates are independent
centred Gaussians with variance `e^{-t} S_c + (1 - e^{-t}) N⁻¹_c` (`ouSample_law`); at `t = 0`
the law of `𝐇_0` is that of the band matrix, on `P L W` and on the carrier `seqP d`
(`ouMat_zero_map`, `seqXmat_map_eq_ouMat_zero`).
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

section U0

variable (L W : ℕ) [NeZero L] [NeZero W]

instance isProbabilityMeasure_gueP : IsProbabilityMeasure (gueP L W) := by
  unfold gueP
  infer_instance

instance isProbabilityMeasure_ouP : IsProbabilityMeasure (ouP L W) := by
  unfold ouP
  infer_instance

/-- The interpolated real coordinates `e^{-t/2} ω₁ + √(1 - e^{-t}) ω₂`. -/
def ouSample (t : ℝ) (ω : Ω L W × Ω L W) : Ω L W :=
  fun c => Real.exp (-t / 2) * ω.1 c + Real.sqrt (1 - Real.exp (-t)) * ω.2 c

/-- The coordinate variance of `𝐇_t`: `e^{-t} S_c + (1 - e^{-t}) N⁻¹_c` (the OU process in the
proof of `Thm: B_Univ`). -/
def ouVar (t : ℝ) (c : Coord L W) : ℝ≥0 :=
  (Real.exp (-t)).toNNReal * gvar L W c + (1 - Real.exp (-t)).toNNReal * gueVar L W c

/-- `𝐇_t` is the matrix `Xmat` of the interpolated coordinates, by `Xmat_add`, `Xmat_smul`. -/
theorem ouMat_eq_Xmat_ouSample (t : ℝ) (ω : Ω L W × Ω L W) :
    ouMat L W t ω = Xmat L W (ouSample L W t ω) := by
  have h : ouSample L W t ω =
      Real.exp (-t / 2) • ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2 := by
    funext c
    simp [ouSample]
  rw [h, Xmat_add, Xmat_smul, Xmat_smul]
  rfl

set_option linter.unusedSectionVars false in
theorem measurable_ouSample (t : ℝ) : Measurable (ouSample L W t) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : Ω L W × Ω L W => ω.1 c :=
    (measurable_pi_apply c).comp measurable_fst
  have h2 : Measurable fun ω : Ω L W × Ω L W => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

private theorem ou_measurable_Xmat : Measurable (Xmat L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j

theorem measurable_ouMat (t : ℝ) : Measurable (ouMat L W t) := by
  have h : ouMat L W t = Xmat L W ∘ ouSample L W t := by
    funext ω
    exact ouMat_eq_Xmat_ouSample L W t ω
  rw [h]
  exact (ou_measurable_Xmat L W).comp (measurable_ouSample L W t)

end U0

/-- The law of `a X + b Y` for independent centred Gaussians `X`, `Y`. -/
private theorem ou_pair_map (a b : ℝ) (v₁ v₂ : ℝ≥0) :
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

section U0Law

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The one-time Gaussian law**: under `ouP` the coordinates of `𝐇_t` are
independent centred Gaussians with variance `e^{-t} S_c + (1 - e^{-t}) N⁻¹_c`. -/
theorem ouSample_law {t : ℝ} (ht : 0 ≤ t) :
    (ouP L W).map (ouSample L W t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar L W t c)) := by
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
  refine IsProjectiveLimit.unique ?_
    (Measure.isProjectiveLimit_infinitePi (fun c => gaussianReal 0 (ouVar L W t c)))
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
  have hR_map : (ouP L W).map R =
      (Measure.pi fun i : I => gaussianReal 0 (gvar L W i)).prod
        (Measure.pi fun i : I => gaussianReal 0 (gueVar L W i)) := by
    have h1 : (P L W).map I.restrict = Measure.pi fun i : I => gaussianReal 0 (gvar L W i) :=
      Measure.infinitePi_map_restrict _
    have h2 : (gueP L W).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gueVar L W i) :=
      Measure.infinitePi_map_restrict _
    rw [← h1, ← h2, Measure.map_prod_map _ _ (Finset.measurable_restrict I)
      (Finset.measurable_restrict I)]
    rfl
  have he_map := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i : I => gaussianReal 0 (gvar L W i)) (fun i : I => gaussianReal 0 (gueVar L W i))).map_eq
  have hge : g ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) = fun x i => f (x i) := by
    funext x i
    rfl
  have : ∀ i : I, SigmaFinite
      (((gaussianReal 0 (gvar L W i)).prod (gaussianReal 0 (gueVar L W i))).map f) := fun i => by
    rw [ou_pair_map]
    infer_instance
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_ouSample L W t), hcomp,
    ← Measure.map_map hg hR, hR_map, ← he_map, Measure.map_map hg
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).measurable, hge,
    Measure.pi_map_pi (fun i => hf.aemeasurable)]
  congr 1
  funext i
  rw [ou_pair_map, hA, hB]
  rfl

end U0Law

section U0Zero

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **Law transfer at `t = 0`**: `𝐇_0 = H` under `ouP` has the law of `Xmat` under
`P L W` (first marginal of `ouP`, `ouMat_zero`). -/
theorem ouMat_zero_map :
    (ouP L W).map (ouMat L W 0) = (P L W).map (Xmat L W) := by
  have h : ouMat L W 0 = Xmat L W ∘ Prod.fst := funext (ouMat_zero L W)
  rw [h, ← Measure.map_map (ou_measurable_Xmat L W) measurable_fst]
  unfold ouP
  rw [Measure.map_fst_prod, measure_univ, one_smul]

end U0Zero

/-- **Law transfer from the carrier `seqP d`**: the band matrix `seqXmat d n` on `seqP d` and
`𝐇_0` on `ouP` have the same law (`seqP_map_slice`). -/
theorem seqXmat_map_eq_ouMat_zero (d : Sizes) (n : ℕ) :
    (seqP d).map (seqXmat d n) = (ouP (d.L n) (d.W n)).map (ouMat (d.L n) (d.W n) 0) := by
  rw [ouMat_zero_map, ← seqP_map_slice d n,
    Measure.map_map (ou_measurable_Xmat _ _) (measurable_slice d n)]
  rfl

end RBM.Univ

end
