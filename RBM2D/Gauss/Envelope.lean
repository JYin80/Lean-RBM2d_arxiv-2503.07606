/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Delocalization
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The deterministic envelope

Work order S1, and the second step of the d=1 playbook for replacing the Ito
layer: **prove the envelope first, because it is free and it unlocks everything
after it.**

For Hermitian `H` and `|Im z| ≥ η > 0`,

  `‖(H - z)⁻¹‖ ≤ η⁻¹`  and  `‖d^k/dt^k (H + tA - z)⁻¹‖ ≤ k! ‖A‖^k η^{-(k+1)}`,

and the point of both is that they hold **on the whole space**, not on a good
event.  Two consequences, both of which pay for the file several times over:

* `Delocalization.lean` currently takes `‖G_xx‖ ≤ C` as a *hypothesis*
  (`sq_norm_eigenvector_le_of_norm_green_le`).  `norm_green_le` discharges it.
* The reverse bridge `≺ ⟹ moments` needs something to bound the bad event with.
  Because the envelope is global, the bad event can simply be dominated by it,
  and no mollifying cutoff is needed anywhere.

Everything here is about `Matrix n n ℂ` for an arbitrary `Fintype n`, so it is
**independent of the dimension** and was ported from the d=1 development
(`RBM2D/Gauss/Generator.lean`, `RBM2D/Loop/Continuity.lean`) essentially
verbatim.  The loop-level envelope that sits on top of it is not dimension-free
-- it carries `W^{-2}` rather than `W^{-1}` -- and is a separate work order.
-/

namespace RBM.Gauss

open Matrix ComplexConjugate
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix minus a non-real multiple of the identity is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hHv : H *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have him := hH.im_star_dotProduct_mulVec_self v
  rw [hHv, dotProduct_smul, smul_eq_mul] at him
  have hd : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hpos : (∑ i, Complex.normSq (v i) : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (v j))).mp h0 i (Finset.mem_univ i))
  rw [hd, RCLike.im_to_complex, Complex.im_mul_ofReal] at him
  exact hz ((mul_eq_zero.mp him).resolve_right hpos)


variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The imaginary part of `⟪v, H v⟫` vanishes for a Hermitian matrix `H`. -/
theorem im_inner_toEuclideanCLM_self {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (v : EuclideanSpace ℂ n) :
    (⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v⟫_ℂ).im = 0 := by
  have := hH.im_star_dotProduct_mulVec_self (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using this

/-- The quantitative lower bound `|Im z| ‖v‖ ≤ ‖(H - z) v‖` for Hermitian `H`.  This is the
whole content of `‖(H - z)⁻¹‖ ≤ |Im z|⁻¹`. -/
theorem abs_im_mul_norm_le_norm_sub_smul_one {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ n) :
    |z.im| * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - z • (1 : Matrix n n ℂ)) v‖ := by
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - z • (1 : Matrix n n ℂ)) with hT
  have hTv : T v = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v - z • v := by
    simp [hT, map_sub, map_smul]
  have hinner : ⟪v, T v⟫_ℂ
      = ⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v⟫_ℂ - z * ⟪v, v⟫_ℂ := by
    rw [hTv, inner_sub_right, inner_smul_right]
  have hvv_im : (⟪v, v⟫_ℂ).im = 0 := by
    simpa [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) v
  have hvv_re : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
    simpa [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v⟫_ℂ).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, hvv_im, hvv_re,
      im_inner_toEuclideanCLM_self hH v]
    ring
  have hcs : ‖⟪v, T v⟫_ℂ‖ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm v (T v)
  have h1 : |z.im| * ‖v‖ ^ 2 ≤ ‖v‖ * ‖T v‖ := by
    refine le_trans ?_ hcs
    have hle := Complex.abs_im_le_norm ⟪v, T v⟫_ℂ
    rw [him] at hle
    calc |z.im| * ‖v‖ ^ 2 = |(-(z.im * ‖v‖ ^ 2))| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
      _ ≤ _ := hle
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · simp [← hv]
  · exact (mul_le_mul_iff_of_pos_left hv).mp
      (by linarith [h1] : ‖v‖ * (|z.im| * ‖v‖) ≤ ‖v‖ * ‖T v‖)

/-- **`‖G‖ ≤ η⁻¹` on the whole space.**  For Hermitian `H` and `|Im z| ≥ η > 0` the Green
function `G = (H - z)⁻¹` of `RBM2D/Delocalization.lean` is bounded by `η⁻¹`, with no
exceptional set. -/
theorem norm_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) : ‖green H z‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set A : Matrix n n ℂ := H - z • (1 : Matrix n n ℂ) with hA
  have hAu : IsUnit A := isUnit_sub_smul_one_of_im_ne_zero hH hzim
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  change ‖A⁻¹‖ ≤ η⁻¹
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  set w := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ v with hw
  have hAw : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w = v := by
    have hmul : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
        * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv A hdet, map_one]
    calc Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w
        = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
            * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹) v := rfl
      _ = v := by rw [hmul]; rfl
  have hkey := abs_im_mul_norm_le_norm_sub_smul_one hH z w
  rw [hAw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The affine line `s ↦ M + s • A` has derivative `A`.
The unused matrix instances are retained in the declaration type for compatibility. -/
theorem hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

/-- Along the line `t ↦ M + t • A`, the inverse has derivative `-R A R`. -/
theorem hasDerivAt_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A))) t := by
  set u : (Matrix n n ℂ)ˣ := (hU t).unit
  have hus : (u : Matrix n n ℂ) = M + (t : ℂ) • A := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = Ring.inverse (M + (t : ℂ) • A) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹)
      (M + (t : ℂ) • A) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt t (hasDerivAt_line M A t)
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

/-- The chain of derivatives: `d/dt [(R A)^k R] = -(k+1) (R A)^{k+1} R`. -/
theorem hasDerivAt_lineInversePow {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ k
        * Ring.inverse (M + (s : ℂ) • A))
      ((-((k : ℝ) + 1)) • ((Ring.inverse (M + (t : ℂ) • A) * A) ^ (k + 1)
        * Ring.inverse (M + (t : ℂ) • A))) t := by
  induction k with
  | zero => simpa using hasDerivAt_lineInverse hU t
  | succ k ih =>
      have h1 : HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A) * A)
          (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A)) * A) t :=
        (hasDerivAt_lineInverse hU t).mul_const A
      have hmul := h1.mul ih
      have key : (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ (k + 1)
            * Ring.inverse (M + (s : ℂ) • A))
          = (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A) * A)
            * (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ k
                * Ring.inverse (M + (s : ℂ) • A)) := by
        funext s
        simp [Pi.mul_apply, pow_succ', mul_assoc]
      rw [key]
      convert hmul using 1
      set R := Ring.inverse (M + (t : ℂ) • A)
      have e1 : -(R * A * R) * A * ((R * A) ^ k * R)
          = -((R * A) ^ (k + 1 + 1) * R) := by
        rw [pow_succ' (R * A) (k + 1), pow_succ' (R * A) k]
        simp [mul_assoc]
      have e2 : R * A * ((-((k : ℝ) + 1)) • ((R * A) ^ (k + 1) * R))
          = (-((k : ℝ) + 1)) • ((R * A) ^ (k + 1 + 1) * R) := by
        rw [mul_smul_comm, pow_succ' (R * A) (k + 1)]
        simp [mul_assoc]
      rw [e1, e2]
      push_cast
      module

/-- The `k`-th derivative of the resolvent along a line, as an equality of functions. -/
theorem iteratedDeriv_lineInverse_eq {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      = fun t : ℝ => ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
          ((Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)) := by
  induction k with
  | zero => funext t; simp
  | succ k ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have hd : HasDerivAt
          (fun s : ℝ => ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
            ((Ring.inverse (M + (s : ℂ) • A) * A) ^ k * Ring.inverse (M + (s : ℂ) • A)))
          (((-1 : ℝ) ^ k * (k.factorial : ℝ)) • ((-((k : ℝ) + 1)) •
            ((Ring.inverse (M + (t : ℂ) • A) * A) ^ (k + 1)
              * Ring.inverse (M + (t : ℂ) • A)))) t :=
        (hasDerivAt_lineInversePow hU k t).const_smul
          ((-1 : ℝ) ^ k * (k.factorial : ℝ))
      rw [hd.deriv, smul_smul]
      congr 1
      push_cast [Nat.factorial_succ]
      ring

/-- The `k`-th derivative of the resolvent along a line is `(-1)^k k! (R A)^k R`. -/
theorem iteratedDeriv_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A)) t
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
          ((Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)) :=
  congrFun (iteratedDeriv_lineInverse_eq hU k) t

/-- Submultiplicativity bound for `(R A)^k R`. -/
theorem norm_lineInversePow_le {M A : Matrix n n ℂ} {K : ℝ}
    (hK : ∀ t : ℝ, ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K) (k : ℕ) (t : ℝ) :
    ‖(Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)‖
      ≤ K ^ (k + 1) * ‖A‖ ^ k := by
  have hRK : ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K := hK t
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) hRK
  set R := Ring.inverse (M + (t : ℂ) • A)
  have hRA : ‖R * A‖ ≤ K * ‖A‖ := le_trans (norm_mul_le _ _) (by gcongr)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hRK
  · have hpow : ‖(R * A) ^ k‖ ≤ (K * ‖A‖) ^ k :=
      le_trans (norm_pow_le' _ hk) (pow_le_pow_left₀ (norm_nonneg _) hRA k)
    calc ‖(R * A) ^ k * R‖ ≤ ‖(R * A) ^ k‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ (K * ‖A‖) ^ k * K := by
          have h0 : (0 : ℝ) ≤ (K * ‖A‖) ^ k := by positivity
          exact mul_le_mul hpow hRK (norm_nonneg _) h0
      _ = K ^ (k + 1) * ‖A‖ ^ k := by ring

/-- **The abstract global bound.**  If the resolvent is bounded by `K` on the whole line, every
derivative of order `k` is bounded by `k! K^{k+1} ‖A‖^k`. -/
theorem norm_iteratedDeriv_lineInverse_le {M A : Matrix n n ℂ} {K : ℝ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A))
    (hK : ∀ t : ℝ, ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A)) t‖
      ≤ (k.factorial : ℝ) * K ^ (k + 1) * ‖A‖ ^ k := by
  rw [iteratedDeriv_lineInverse hU k t, norm_smul, mul_assoc]
  have h1 : ‖(-1 : ℝ) ^ k * (k.factorial : ℝ)‖ = (k.factorial : ℝ) := by simp
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_lineInversePow_le hK k t) (Nat.cast_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
theorem isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- **The global derivative bound, in the form every later file needs.**

For Hermitian `M` and a Hermitian direction `A`, and `|Im z| ≥ η > 0`, every derivative of
order `k` of `s ↦ G(M + s A) = (M + s A - z)⁻¹` is bounded, **at every point of the whole
line**, by `k! η^{-(k+1)} ‖A‖^k`.  Because the bound is a constant, the `bound_integrable`
hypothesis of the parametric-integral lemma is discharged by
`RBM.Gauss.integrable_of_continuous_of_bound`. -/
theorem norm_iteratedDeriv_green_le {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => green (M + (s : ℂ) • A) z) t‖
      ≤ (k.factorial : ℝ) * η⁻¹ ^ (k + 1) * ‖A‖ ^ k := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hgr : (fun s : ℝ => green (M + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    change (M + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    intro s
    have he : M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (M + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA s) hzim
  have hK : ∀ s : ℝ, ‖Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A)‖ ≤ η⁻¹ := by
    intro s
    have he : Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A)
        = green (M + (s : ℂ) • A) z := (congrFun hgr s).symm
    rw [he]
    exact norm_green_le (isHermitian_add_realSmul hM hA s) hη hz
  rw [hgr]
  exact norm_iteratedDeriv_lineInverse_le hU hK k t

end RBM.Gauss
