/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Endpoints
import RBM2D.Propagator.FiniteDiff
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.GreenTimeCont

/-!
# `MR:QUE` from `MR:QDiff`

`QUE_of_QDiff : QDiff → QUE`: the deduction of generalized quantum unique ergodicity from
quantum diffusion (the endpoint statements of `RBM2D/Endpoints.lean`).

Proof outline:
* `z = E + iη` with `η = W^{2/3}/N`; the window half-width `N^{-1-τ} W^{2/3}` is `≤ η`;
* `QDiff` is used at `τ_Q = min(𝔠, 1)/12`, `D = 1`, and only through its expectation half
  `(Meq:QdS1)`/`(Meq:QdS2)`;
* for any orthonormal eigenbasis, `|ψ_k^* B ψ_{k'}|² ≤ 4η² tr(Im G B Im G B)` for `k, k'` in
  the window and Hermitian `B` (`(ssfa2)`);
* `B = ∑_u (c_u - L⁻²) E_u` with `∑ c = 1`, so `E tr(Im G B Im G B)` is a double sum of
  `E tr(Im G E_u Im G E_v)` with coefficients summing to zero (`(que0)`); these are the four
  `trGEGE` expectations, compared with the profile by `QDiff`;
* the profile differences are bounded by the Fourier estimate `norm_Theta_sub_le_log`
  (not by the `(prop:BD1)` lattice path);
* the exponent chain gives `E[4N²η² tr(…)] ≤ N^{-τ/2}`, and Markov's inequality finishes.
-/

namespace RBM.Endpoints

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes
open scoped ComplexConjugate

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- The matrix imaginary part `Im G = (G - G†)/(2i)`. -/
private noncomputable def QUEFromQDiff_imG (H : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  ((2 : ℂ) * Complex.I)⁻¹ • (green H z - (green H z)ᴴ)

/-- The matrix of eigenvector columns. -/
private def QUEFromQDiff_U (ψ : ι → ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y

private theorem QUEFromQDiff_UU (hψ : IsOrthoEigenbasis H μ ψ) :
    star (QUEFromQDiff_U ψ) * QUEFromQDiff_U ψ = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, QUEFromQDiff_U, Matrix.of_apply,
    Matrix.one_apply]
  exact h

private theorem QUEFromQDiff_green_eq (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) :
    green H z = QUEFromQDiff_U ψ * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) *
      star (QUEFromQDiff_U ψ) := by
  set U := QUEFromQDiff_U ψ with hU
  have hUU : star U * U = 1 := QUEFromQDiff_UU hψ
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, QUEFromQDiff_U, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - z • 1) * U = U * diagonal (fun l => (μ l : ℂ) - z) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  apply Matrix.inv_eq_right_inv
  calc (H - z • 1) * (U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U)
      = ((H - z • 1) * U) * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal (fun l => (μ l : ℂ) - z)
          * diagonal (fun l => ((μ l : ℂ) - z)⁻¹)) * star U := by
        rw [hsub]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        have hd : (fun l => ((μ l : ℂ) - z) * ((μ l : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']

/-- The resolvent weight `w_l = η / ((μ_l - E)² + η²)`. -/
private noncomputable def QUEFromQDiff_w (μ : ι → ℝ) (E η : ℝ) (l : ι) : ℝ :=
  η / ((μ l - E) ^ 2 + η ^ 2)

/-- `Im G(E + iη) = U diag(w) U*` for any orthonormal eigenbasis. -/
private theorem QUEFromQDiff_imG_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) :
    QUEFromQDiff_imG H (E + η * Complex.I) = QUEFromQDiff_U ψ *
      diagonal (fun l => ((QUEFromQDiff_w μ E η l : ℝ) : ℂ)) * star (QUEFromQDiff_U ψ) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hz : ∀ l, (μ l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp [hzdef] at this
    exact hη this.symm
  set U := QUEFromQDiff_U ψ with hU
  set d : ι → ℂ := fun l => ((μ l : ℂ) - z)⁻¹ with hd
  have hG := QUEFromQDiff_green_eq hψ hz
  rw [← hd] at hG
  have hGH : (green H z)ᴴ = U * diagonal (star d) * star U := by
    rw [hG, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdiag : diagonal (fun l => ((QUEFromQDiff_w μ E η l : ℝ) : ℂ)) =
      ((2 : ℂ) * Complex.I)⁻¹ • (diagonal d - diagonal (star d)) := by
    rw [diagonal_sub, ← diagonal_smul]
    congr 1
    funext l
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, RCLike.star_def]
    rw [Complex.sub_conj]
    have hn : Complex.normSq ((μ l : ℂ) - z) = (μ l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp [hzdef]
      ring
    have him : ((μ l : ℂ) - z).im = -η := by simp [hzdef]
    have hdim : (d l).im = QUEFromQDiff_w μ E η l := by
      simp only [hd, Complex.inv_im, hn, him, QUEFromQDiff_w]
      ring
    rw [hdim]
    have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
    push_cast
    ring
  unfold QUEFromQDiff_imG
  rw [hGH, hG, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
/-- The entry `(U* B U)_{lm} = ψ_l^* B ψ_m`. -/
private theorem QUEFromQDiff_C_apply (B : Matrix ι ι ℂ) (l m : ι) :
    (star (QUEFromQDiff_U ψ) * B * QUEFromQDiff_U ψ) l m = star (ψ l) ⬝ᵥ (B *ᵥ ψ m) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, QUEFromQDiff_U,
    Matrix.star_apply, Matrix.of_apply, Pi.star_apply]

/-- For Hermitian `B`: `tr(Im G B Im G B) = ∑_{l,m} w_l w_m |ψ_l^* B ψ_m|²`. -/
private theorem QUEFromQDiff_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    trace (QUEFromQDiff_imG H (E + η * Complex.I) * B *
        QUEFromQDiff_imG H (E + η * Complex.I) * B) =
      ∑ l, ∑ m, ((QUEFromQDiff_w μ E η l * QUEFromQDiff_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) : ℝ) : ℂ) := by
  rw [QUEFromQDiff_imG_eq hψ E hη]
  set U := QUEFromQDiff_U ψ with hU
  set D : Matrix ι ι ℂ := diagonal (fun l => ((QUEFromQDiff_w μ E η l : ℝ) : ℂ)) with hD
  set C : Matrix ι ι ℂ := star U * B * U with hC
  have hCH : Cᴴ = C := by
    rw [hC, conjTranspose_mul, conjTranspose_mul, hB, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  have htr : trace (U * D * star U * B * (U * D * star U) * B) = trace (D * C * D * C) := by
    have h1 : U * D * star U * B * (U * D * star U) * B =
        U * (D * star U * B * U * D * star U * B) := by simp only [Matrix.mul_assoc]
    rw [h1, trace_mul_comm, hC]
    simp only [Matrix.mul_assoc]
  rw [htr, trace]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hml : C m l = star (C l m) := by
    have h := congrFun (congrFun hCH m) l
    rw [conjTranspose_apply] at h
    exact h.symm
  rw [hml, hD, mul_diagonal, diagonal_mul, ← QUEFromQDiff_C_apply B l m]
  rw [RCLike.star_def]
  have := Complex.mul_conj (C l m)
  push_cast
  linear_combination (((QUEFromQDiff_w μ E η l : ℝ) : ℂ) *
    ((QUEFromQDiff_w μ E η m : ℝ) : ℂ)) * this

private theorem QUEFromQDiff_re_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    (trace (QUEFromQDiff_imG H (E + η * Complex.I) * B *
        QUEFromQDiff_imG H (E + η * Complex.I) * B)).re =
      ∑ l, ∑ m, QUEFromQDiff_w μ E η l * QUEFromQDiff_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
  rw [QUEFromQDiff_trace_eq hψ E hη B hB, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] in
private theorem QUEFromQDiff_w_nonneg (μ : ι → ℝ) (E : ℝ) {η : ℝ} (hη : 0 ≤ η) (l : ι) :
    0 ≤ QUEFromQDiff_w μ E η l := by
  unfold QUEFromQDiff_w
  positivity

/-- `Re tr(Im G B Im G B) ≥ 0` for Hermitian `B`. -/
private theorem QUEFromQDiff_re_trace_nonneg (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    0 ≤ (trace (QUEFromQDiff_imG H (E + η * Complex.I) * B *
        QUEFromQDiff_imG H (E + η * Complex.I) * B)).re := by
  rw [QUEFromQDiff_re_trace_eq hψ E hη.ne' B hB]
  refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => ?_
  have := QUEFromQDiff_w_nonneg μ E hη.le l
  have := QUEFromQDiff_w_nonneg μ E hη.le m
  have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
  positivity

/-- **Pointwise domination.** If `|μ_k - E| ≤ η` and `|μ_{k'} - E| ≤ η`, then
`|ψ_k^* B ψ_{k'}|² ≤ 4 η² Re tr(Im G B Im G B)`. -/
private theorem QUEFromQDiff_normSq_le (hψ : IsOrthoEigenbasis H μ ψ) {E η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) {k k' : ι}
    (hk : |μ k - E| ≤ η) (hk' : |μ k' - E| ≤ η) :
    Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      4 * η ^ 2 * (trace (QUEFromQDiff_imG H (E + η * Complex.I) * B *
        QUEFromQDiff_imG H (E + η * Complex.I) * B)).re := by
  rw [QUEFromQDiff_re_trace_eq hψ E hη.ne' B hB]
  have hterm : ∀ l ∈ Finset.univ, ∀ m ∈ Finset.univ, 0 ≤ QUEFromQDiff_w μ E η l *
      QUEFromQDiff_w μ E η m * Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
    intro l _ m _
    have := QUEFromQDiff_w_nonneg μ E hη.le l
    have := QUEFromQDiff_w_nonneg μ E hη.le m
    have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
    positivity
  have hsingle : QUEFromQDiff_w μ E η k * QUEFromQDiff_w μ E η k' *
      Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      ∑ l, ∑ m, QUEFromQDiff_w μ E η l * QUEFromQDiff_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) :=
    le_trans (Finset.single_le_sum (hterm k (Finset.mem_univ k)) (Finset.mem_univ k'))
      (Finset.single_le_sum (fun l hl => Finset.sum_nonneg (hterm l hl))
        (Finset.mem_univ k))
  have hw : ∀ j, |μ j - E| ≤ η → 1 / (2 * η) ≤ QUEFromQDiff_w μ E η j := by
    intro j hj
    unfold QUEFromQDiff_w
    have hsq : (μ j - E) ^ 2 ≤ η ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hj 2
    have hden : 0 < (μ j - E) ^ 2 + η ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  have hwk := hw k hk
  have hwk' := hw k' hk'
  set c := Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) with hc
  have hc0 : 0 ≤ c := Complex.normSq_nonneg _
  have h2η : 0 < 2 * η := by positivity
  have hprod : 1 / (2 * η) * (1 / (2 * η)) ≤
      QUEFromQDiff_w μ E η k * QUEFromQDiff_w μ E η k' :=
    mul_le_mul hwk hwk' (by positivity) (QUEFromQDiff_w_nonneg μ E hη.le k)
  have hkey : c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := by
    field_simp
    ring
  calc c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := hkey
    _ ≤ 4 * η ^ 2 * (QUEFromQDiff_w μ E η k * QUEFromQDiff_w μ E η k' * c) := by
        gcongr
    _ ≤ _ := by gcongr

/-- Every Hermitian matrix has an orthonormal eigenbasis in the sense of
`IsOrthoEigenbasis` (Mathlib's `eigenvectorBasis`). -/
private theorem QUEFromQDiff_exists_basis (hH : H.IsHermitian) :
    ∃ (μ : ι → ℝ) (ψ : ι → ι → ℂ), IsOrthoEigenbasis H μ ψ := by
  refine ⟨hH.eigenvalues, fun k => ⇑(hH.eigenvectorBasis k), ?_, fun k => ?_⟩
  · intro k k'
    have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · rw [hH.mulVec_eigenvectorBasis k]
    ext x
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

end Spectral

/-! ### Trace algebra -/

section TraceAlgebra

variable {ι : Type*} [Fintype ι]

/-- `tr(Im G E_u Im G E_v) = -¼ (tr(G E_u G E_v) + conj tr(G E_u G E_v) - tr(G E_u G† E_v)
- tr(G E_v G† E_u))` for Hermitian `E_u, E_v`. -/
private theorem QUEFromQDiff_trace_imG (G Eu Ev : Matrix ι ι ℂ) (hEu : Euᴴ = Eu)
    (hEv : Evᴴ = Ev) :
    trace ((((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) * Eu * (((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) *
        Ev) =
      -(1 / 4 : ℂ) * (trace (G * Eu * G * Ev) + conj (trace (G * Eu * G * Ev)) -
        trace (G * Eu * Gᴴ * Ev) - trace (G * Ev * Gᴴ * Eu)) := by
  have h1 : trace (Gᴴ * Eu * G * Ev) = trace (G * Ev * Gᴴ * Eu) := by
    have : Gᴴ * Eu * G * Ev = (Gᴴ * Eu) * (G * Ev) := by simp only [Matrix.mul_assoc]
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : trace (Gᴴ * Eu * Gᴴ * Ev) = conj (trace (G * Eu * G * Ev)) := by
    rw [← RCLike.star_def, ← trace_conjTranspose]
    simp only [conjTranspose_mul, hEu, hEv]
    have : Gᴴ * Eu * Gᴴ * Ev = (Gᴴ * Eu * Gᴴ) * Ev := rfl
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hc : ((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
    rw [← mul_inv, show (2 : ℂ) * Complex.I * (2 * Complex.I) = -4 by
      ring_nf; rw [Complex.I_sq]; ring]
    norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, Matrix.sub_mul,
    Matrix.mul_sub, trace_sub, smul_eq_mul]
  rw [h1, h2]
  linear_combination (trace (G * Eu * G * Ev) - trace (G * Ev * Gᴴ * Eu) -
    trace (G * Eu * Gᴴ * Ev) + conj (trace (G * Eu * G * Ev))) * hc

/-- Bilinear expansion of `tr(M B M B')` for `B = ∑ β_u E_u`, `B' = ∑ β'_v E_v`. -/
private theorem QUEFromQDiff_trace_sum {κ : Type*} [Fintype κ] (M : Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (β : κ → ℂ) :
    trace (M * (∑ u, β u • E u) * M * (∑ v, β v • E v)) =
      ∑ u, ∑ v, β u * β v * trace (M * E u * M * E v) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sum,
    trace_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- `|∑_{u,v} β_u β_v h_{uv}| ≤ (∑|β|)² K` when `∑ β = 0` and `|h_{uv} - p₀| ≤ K`. -/
private theorem QUEFromQDiff_norm_double_sum_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
    (hβ0 : ∑ u, β u = 0) (h : κ → κ → ℂ) (p₀ : ℂ) {K : ℝ}
    (hK : ∀ u v, ‖h u v - p₀‖ ≤ K) :
    ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v‖ ≤ (∑ u, |β u|) ^ 2 * K := by
  have hsplit : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v =
      ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - p₀) := by
    have hz : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * p₀ = 0 := by
      have : (∑ u, (β u : ℂ)) = 0 := by exact_mod_cast hβ0
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, this, zero_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, hz, sub_zero]
  rw [hsplit]
  calc ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - p₀)‖
      ≤ ∑ u, ∑ v, ‖((β u : ℂ) * (β v : ℂ)) * (h u v - p₀)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_sum_le _ _)
    _ ≤ ∑ u, ∑ v, |β u| * |β v| * K := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hK u v) (by positivity)
    _ = (∑ u, |β u|) ^ 2 * K := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

end TraceAlgebra

/-! ### The observable `B_c = ∑_u (c_u - L⁻²) E_u` -/

section Observable

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `B_c = ∑_u (c_u - L⁻²) E_u`; for `∑ c = 1` this is `∑_u c_u E_u - N⁻¹` (`B_eq`). -/
private noncomputable def QUEFromQDiff_B (c : Z2 L → ℝ) :
    Matrix (Z2 (W * L)) (Z2 (W * L)) ℂ :=
  ∑ u, (((c u - ((L : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) • Epaper L W u

private theorem QUEFromQDiff_B_herm (c : Z2 L → ℝ) :
    (QUEFromQDiff_B L W c)ᴴ = QUEFromQDiff_B L W c := by
  unfold QUEFromQDiff_B
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [conjTranspose_smul, Epaper_conjTranspose, RCLike.star_def, Complex.conj_ofReal]

private theorem QUEFromQDiff_B_eq (c : Z2 L → ℝ) :
    QUEFromQDiff_B L W c = ∑ u, ((c u : ℝ) : ℂ) • Epaper L W u -
      ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix _ _ ℂ) := by
  unfold QUEFromQDiff_B
  simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.smul_sum, sum_Epaper, smul_smul]
  congr 1
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  push_cast
  field_simp

private theorem QUEFromQDiff_card : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

private theorem QUEFromQDiff_sum_beta (c : Z2 L → ℝ) (hc1 : ∑ u, c u = 1) :
    ∑ u, (c u - ((L : ℝ) ^ 2)⁻¹) = 0 := by
  rw [Finset.sum_sub_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    QUEFromQDiff_card]
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  field_simp
  ring

private theorem QUEFromQDiff_sum_abs_beta (c : Z2 L → ℝ) (hc0 : ∀ u, 0 ≤ c u)
    (hc1 : ∑ u, c u = 1) :
    ∑ u, |c u - ((L : ℝ) ^ 2)⁻¹| ≤ 2 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  calc ∑ u, |c u - ((L : ℝ) ^ 2)⁻¹| ≤ ∑ u, (c u + ((L : ℝ) ^ 2)⁻¹) := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_le]
        have := hc0 u
        have : 0 ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
        constructor <;> linarith
    _ = 2 := by
        rw [Finset.sum_add_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          QUEFromQDiff_card]
        field_simp
        ring

end Observable

/-! ### Integrability of `tr(G E_a G^σ E_b)` -/

section Integr

variable (d : Sizes) (n : ℕ)

open scoped Matrix.Norms.L2Operator in
private theorem QUEFromQDiff_trGEGE_bound {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    (a b : Z2 (d.L n)) : ∃ C : ℝ, ∀ ω, ‖trGEGE d n ω z σ a b‖ ≤ C := by
  refine ⟨(Fintype.card (Idx (d.L n) (d.W n)) : ℝ) * (|z.im|⁻¹ *
    ‖Epaper (d.L n) (d.W n) a‖ * |z.im|⁻¹ * ‖Epaper (d.L n) (d.W n) b‖), fun ω => ?_⟩
  have hG : ‖Gn d n ω z‖ ≤ |z.im|⁻¹ :=
    norm_green_le (seqXmat_isHermitian d n ω) (abs_pos.mpr hz) le_rfl
  have hGσ : ‖(if σ then Gn d n ω z else (Gn d n ω z)ᴴ)‖ ≤ |z.im|⁻¹ := by
    cases σ
    · simp only [Bool.false_eq_true, ite_false, l2_opNorm_conjTranspose]; exact hG
    · simp only [ite_true]; exact hG
  unfold trGEGE
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr

private theorem QUEFromQDiff_trGEGE_meas {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    (a b : Z2 (d.L n)) : Measurable fun ω => trGEGE d n ω z σ a b := by
  have hcont : Continuous fun ω' : Ω (d.L n) (d.W n) =>
      green (Xmat (d.L n) (d.W n) ω') z :=
    continuous_green_of_isHermitian (continuous_Xmat _ _) (fun v => Xmat_isHermitian _ _ v) hz
  have hΦ : Continuous fun ω' : Ω (d.L n) (d.W n) =>
      trace (green (Xmat (d.L n) (d.W n) ω') z * Epaper (d.L n) (d.W n) a *
        (if σ then green (Xmat (d.L n) (d.W n) ω') z
          else (green (Xmat (d.L n) (d.W n) ω') z)ᴴ) * Epaper (d.L n) (d.W n) b) := by
    cases σ
    · simp only [Bool.false_eq_true, ite_false]
      exact (((hcont.matrix_mul continuous_const).matrix_mul
        hcont.matrix_conjTranspose).matrix_mul continuous_const).matrix_trace
    · simp only [ite_true]
      exact (((hcont.matrix_mul continuous_const).matrix_mul
        hcont).matrix_mul continuous_const).matrix_trace
  exact hΦ.measurable.comp (measurable_slice d n)

private theorem QUEFromQDiff_trGEGE_integrable {z : ℂ} (hz : z.im ≠ 0) (σ : Bool)
    (a b : Z2 (d.L n)) : Integrable (fun ω => trGEGE d n ω z σ a b) (seqP d) := by
  obtain ⟨C, hC⟩ := QUEFromQDiff_trGEGE_bound d n hz σ a b
  exact Integrable.of_bound (QUEFromQDiff_trGEGE_meas d n hz σ a b).aestronglyMeasurable C
    (ae_of_all _ hC)

end Integr

/-! ### The profile differences (Fourier bound, not the `(prop:BD1)` path) -/

private theorem QUEFromQDiff_norm_xi_lt_one {z : ℂ} (hz : 0 < z.im) (σ : Bool) :
    ‖(if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ))‖ < 1 := by
  have hm : ‖mSC z‖ < 1 := by rw [mSC_eq_msc hz]; exact norm_msc_lt_one hz
  have hm2 : ‖mSC z‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hm two_ne_zero
  cases σ
  · simp only [Bool.false_eq_true, ite_false, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact hm2
  · simp only [ite_true, norm_pow]
    exact hm2

/-- `|P_σ(u,v) - P_σ(0,0)| ≤ 90 W⁻² (1 + log L)` for every `u, v`. -/
private theorem QUEFromQDiff_profile_diff (L W : ℕ) [NeZero L] (hL : 3 ≤ L) {z : ℂ}
    (hz : 0 < z.im) (σ : Bool) (u v : Z2 L) :
    ‖profile L W z σ u v - profile L W z σ 0 0‖ ≤
      ((W : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log L)) := by
  have hξ := QUEFromQDiff_norm_xi_lt_one hz σ
  set ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ) with hξdef
  have hp : ∀ a b : Z2 L, profile L W z σ a b = ((W : ℂ) ^ 2)⁻¹ * (ξ * Theta L ξ a b) :=
    fun a b => rfl
  have hshift : Theta L ξ u v = Theta L ξ (u - v) 0 := by
    have h := Theta_apply_add_right L hL hξ (u - v) 0 v
    simp only [sub_add_cancel, zero_add] at h
    exact h
  rw [hp, hp, hshift, ← mul_sub, ← mul_sub]
  have hΘ := norm_Theta_sub_le_log L hL hξ (u - v) 0
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖ξ‖ * ‖Theta L ξ (u - v) 0 - Theta L ξ 0 0‖
      ≤ 1 * (90 * (1 + Real.log L)) := by
        gcongr
    _ = 90 * (1 + Real.log L) := one_mul _

/-- The four-term combination is `1`-Lipschitz for the maximum of the three differences. -/
private theorem QUEFromQDiff_quad_diff {a a' b b' c c' : ℂ} {K : ℝ} (ha : ‖a - a'‖ ≤ K)
    (hb : ‖b - b'‖ ≤ K) (hc : ‖c - c'‖ ≤ K) :
    ‖-(1 / 4 : ℂ) * (a + conj a - b - c) - -(1 / 4 : ℂ) * (a' + conj a' - b' - c')‖ ≤ K := by
  have h : -(1 / 4 : ℂ) * (a + conj a - b - c) - -(1 / 4 : ℂ) * (a' + conj a' - b' - c') =
      -(1 / 4 : ℂ) * ((a - a') + conj (a - a') - (b - b') - (c - c')) := by
    rw [map_sub]; ring
  rw [h, norm_mul]
  have h4 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [h4]
  have hsum : ‖(a - a') + conj (a - a') - (b - b') - (c - c')‖ ≤ K + K + K + K := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ha ?_)) hb)) hc
    rw [RCLike.norm_conj]; exact ha
  linarith

/-! ### The core: expectation of `Re tr(Im G B_c Im G B_c)` -/

section Core

variable (d : Sizes) (n : ℕ)

/-- `X_c(ω) = Re tr(Im G B_c Im G B_c)` at the spectral parameter `z`. -/
private noncomputable def QUEFromQDiff_X (z : ℂ) (c : Z2 (d.L n) → ℝ) (ω : SeqΩ d) : ℝ :=
  (trace (QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c *
    QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c)).re

/-- The complex four-term combination of `trGEGE`. -/
private noncomputable def QUEFromQDiff_F (z : ℂ) (ω : SeqΩ d) (u v : Z2 (d.L n)) : ℂ :=
  -(1 / 4 : ℂ) * (trGEGE d n ω z true u v + conj (trGEGE d n ω z true u v) -
    trGEGE d n ω z false u v - trGEGE d n ω z false v u)

private theorem QUEFromQDiff_trace_eq_sum (z : ℂ) (c : Z2 (d.L n) → ℝ) (ω : SeqΩ d) :
    trace (QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c *
      QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c) =
      ∑ u, ∑ v, ((((c u - ((d.L n : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) *
        (((c v - ((d.L n : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ)) * QUEFromQDiff_F d n z ω u v := by
  unfold QUEFromQDiff_B
  rw [QUEFromQDiff_trace_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  unfold QUEFromQDiff_imG
  rw [QUEFromQDiff_trace_imG _ _ _ (Epaper_conjTranspose _ _ u) (Epaper_conjTranspose _ _ v)]
  rfl

private theorem QUEFromQDiff_F_integrable {z : ℂ} (hz : z.im ≠ 0) (u v : Z2 (d.L n)) :
    Integrable (fun ω => QUEFromQDiff_F d n z ω u v) (seqP d) := by
  have hT := QUEFromQDiff_trGEGE_integrable d n hz true u v
  have hF := QUEFromQDiff_trGEGE_integrable d n hz false u v
  have hF' := QUEFromQDiff_trGEGE_integrable d n hz false v u
  have hTc : Integrable (fun ω => conj (trGEGE d n ω z true u v)) (seqP d) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  exact (((hT.add hTc).sub hF).sub hF').const_mul _

private theorem QUEFromQDiff_integral_F {z : ℂ} (hz : z.im ≠ 0) (u v : Z2 (d.L n)) :
    ∫ ω, QUEFromQDiff_F d n z ω u v ∂(seqP d) =
      -(1 / 4 : ℂ) * ((∫ ω, trGEGE d n ω z true u v ∂(seqP d)) +
        conj (∫ ω, trGEGE d n ω z true u v ∂(seqP d)) -
        (∫ ω, trGEGE d n ω z false u v ∂(seqP d)) -
        (∫ ω, trGEGE d n ω z false v u ∂(seqP d))) := by
  have hT := QUEFromQDiff_trGEGE_integrable d n hz true u v
  have hF := QUEFromQDiff_trGEGE_integrable d n hz false u v
  have hF' := QUEFromQDiff_trGEGE_integrable d n hz false v u
  have hTc : Integrable (fun ω => conj (trGEGE d n ω z true u v)) (seqP d) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  have h0 : Integrable (fun ω => trGEGE d n ω z true u v + conj (trGEGE d n ω z true u v))
      (seqP d) := hT.add hTc
  have h1 : Integrable (fun ω => trGEGE d n ω z true u v + conj (trGEGE d n ω z true u v) -
      trGEGE d n ω z false u v) (seqP d) := h0.sub hF
  unfold QUEFromQDiff_F
  rw [integral_const_mul, integral_sub h1 hF', integral_sub h0 hF,
    integral_add hT hTc, integral_conj]

/-- **Core estimate** (`(que0)` with the Fourier profile bound).  If `(Meq:QdS1)`/`(Meq:QdS2)`
hold with error `ε` at `z = E + iη`, then `X_c ≥ 0` is integrable and
`E X_c ≤ 4 (90 W⁻² (1 + log L) + ε)`. -/
private theorem QUEFromQDiff_core (E : ℝ) {η : ℝ} (hη : 0 < η) {ε : ℝ}
    (hQ : ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGE d n ω (E + η * Complex.I) σ a b ∂(seqP d)) -
        profile (d.L n) (d.W n) (E + η * Complex.I) σ a b‖ ≤ ε)
    (c : Z2 (d.L n) → ℝ) (hc0 : ∀ u, 0 ≤ c u) (hc1 : ∑ u, c u = 1) :
    Integrable (QUEFromQDiff_X d n (E + η * Complex.I) c) (seqP d) ∧
      (∀ ω, 0 ≤ QUEFromQDiff_X d n (E + η * Complex.I) c ω) ∧
      ∫ ω, QUEFromQDiff_X d n (E + η * Complex.I) c ω ∂(seqP d) ≤
        4 * (((d.W n : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log (d.L n))) + ε) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : z.im ≠ 0 := by rw [hzim]; exact hη.ne'
  have hz0 : 0 < z.im := by rw [hzim]; exact hη
  set β : Z2 (d.L n) → ℝ := fun u => c u - ((d.L n : ℝ) ^ 2)⁻¹ with hβ
  set Xc : SeqΩ d → ℂ := fun ω =>
    trace (QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c *
      QUEFromQDiff_imG (seqXmat d n ω) z * QUEFromQDiff_B (d.L n) (d.W n) c) with hXc
  have hXc_eq : Xc = fun ω => ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
      QUEFromQDiff_F d n z ω u v :=
    funext fun ω => QUEFromQDiff_trace_eq_sum d n z c ω
  have hXc_int : Integrable Xc (seqP d) := by
    rw [hXc_eq]
    refine integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ?_
    exact (QUEFromQDiff_F_integrable d n hz u v).const_mul _
  have hX : QUEFromQDiff_X d n z c = fun ω => (Xc ω).re := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]; exact hXc_int.re
  · intro ω
    obtain ⟨μ, ψ, hψ⟩ := QUEFromQDiff_exists_basis (seqXmat_isHermitian d n ω)
    exact QUEFromQDiff_re_trace_nonneg hψ E hη _ (QUEFromQDiff_B_herm _ _ c)
  · have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hQ true 0 0)
    set δ : ℝ := ((d.W n : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log (d.L n))) with hδ
    have hδ0 : 0 ≤ δ := by
      have : 0 ≤ Real.log (d.L n) := Real.log_natCast_nonneg _
      positivity
    have hint : ∫ ω, Xc ω ∂(seqP d) = ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
        ∫ ω, QUEFromQDiff_F d n z ω u v ∂(seqP d) := by
      rw [hXc_eq, integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
        (QUEFromQDiff_F_integrable d n hz u v).const_mul _]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum _ fun v _ => (QUEFromQDiff_F_integrable d n hz u v).const_mul _]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul]
    set P : Bool → Z2 (d.L n) → Z2 (d.L n) → ℂ := fun σ a b => profile (d.L n) (d.W n) z σ a b
      with hP
    set p₀ : ℂ := -(1 / 4 : ℂ) * (P true 0 0 + conj (P true 0 0) - P false 0 0 - P false 0 0)
      with hp₀
    have hK : ∀ u v, ‖(∫ ω, QUEFromQDiff_F d n z ω u v ∂(seqP d)) - p₀‖ ≤ ε + δ := by
      intro u v
      rw [QUEFromQDiff_integral_F d n hz u v]
      have h1 := QUEFromQDiff_quad_diff (hQ true u v) (hQ false u v) (hQ false v u)
      have hd := fun σ a b => QUEFromQDiff_profile_diff (d.L n) (d.W n) (d.three_le_L n) hz0 σ a b
      have h2 := QUEFromQDiff_quad_diff (hd true u v) (hd false u v) (hd false v u)
      calc _ ≤ ‖-(1 / 4 : ℂ) * ((∫ ω, trGEGE d n ω z true u v ∂(seqP d)) +
              conj (∫ ω, trGEGE d n ω z true u v ∂(seqP d)) -
              (∫ ω, trGEGE d n ω z false u v ∂(seqP d)) -
              (∫ ω, trGEGE d n ω z false v u ∂(seqP d))) -
            -(1 / 4 : ℂ) * (P true u v + conj (P true u v) - P false u v - P false v u)‖ +
            ‖-(1 / 4 : ℂ) * (P true u v + conj (P true u v) - P false u v - P false v u) - p₀‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + δ := add_le_add h1 h2
    have hnorm := QUEFromQDiff_norm_double_sum_le β
      (QUEFromQDiff_sum_beta (d.L n) c hc1) _ p₀ hK
    have hsum2 : (∑ u, |β u|) ^ 2 ≤ 4 := by
      have h := QUEFromQDiff_sum_abs_beta (d.L n) c hc0 hc1
      have h0 : 0 ≤ ∑ u, |β u| := Finset.sum_nonneg fun u _ => abs_nonneg _
      nlinarith
    rw [hX]
    have hre : (∫ ω, (Xc ω).re ∂(seqP d)) = (∫ ω, Xc ω ∂(seqP d)).re := integral_re hXc_int
    change (∫ ω, (Xc ω).re ∂(seqP d)) ≤ _
    rw [hre]
    calc (∫ ω, Xc ω ∂(seqP d)).re ≤ ‖∫ ω, Xc ω ∂(seqP d)‖ := Complex.re_le_norm _
      _ ≤ (∑ u, |β u|) ^ 2 * (ε + δ) := by rw [hint]; exact hnorm
      _ ≤ 4 * (ε + δ) := by gcongr
      _ = 4 * (δ + ε) := by ring

end Core

/-! ### The failure events are dominated by `4 N² η² X_c` -/

section Events

private theorem QUEFromQDiff_quad_Epaper (L W : ℕ) [NeZero L] [NeZero W]
    (ψ : Z2 (W * L) → ℂ) (u : Z2 L) :
    star ψ ⬝ᵥ (Epaper L W u *ᵥ ψ) =
      ((((W : ℝ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W u, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Epaper, Matrix.of_apply, Pi.star_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Iblk L W u)]
  have hf : Finset.univ.filter (· ∈ Iblk L W u) = Iblk L W u := by
    ext x; simp
  rw [hf]
  have h0 : ∑ x ∈ Finset.univ.filter (fun x => x ∉ Iblk L W u),
      star (ψ x) * ((W : ℂ)⁻¹ ^ 2 * (if x ∈ Iblk L W u then 1 else 0) * ψ x) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_filter] at hx
    simp [hx.2]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  simp only [hx, ite_true, RCLike.star_def]
  have := RCLike.conj_mul (ψ x)
  linear_combination ((W : ℂ)⁻¹ ^ 2) * this

variable (d : Sizes) (n : ℕ)

/-- `(Meq:QUE)` event inside `{N^{-τ/6} ≤ 4 N² η² X_{δ_a}}` (window half-width `≤ η`). -/
private theorem QUEFromQDiff_queBad_sub {τ E η : ℝ} (hη : 0 < η)
    (hwin : ((d.size n : ℕ) : ℝ) ^ (-1 - τ) * (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ η)
    (a : Z2 (d.L n)) :
    {ω | queBad d n τ E a ω} ⊆ {ω | ((d.size n : ℕ) : ℝ) ^ (-τ / 6) ≤
      4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFromQDiff_X d n (E + η * Complex.I) (fun u => if u = a then 1 else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, k, k', hk, hk', hbad⟩ := hω
  simp only [Set.mem_ofPred_eq]
  refine le_trans hbad ?_
  have hBeq : QUEFromQDiff_B (d.L n) (d.W n) (fun u => if u = a then 1 else 0) =
      Epaper (d.L n) (d.W n) a - ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ) := by
    rw [QUEFromQDiff_B_eq]
    congr 1
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdom := QUEFromQDiff_normSq_le hψ hη (QUEFromQDiff_B (d.L n) (d.W n)
    (fun u => if u = a then 1 else 0)) (QUEFromQDiff_B_herm _ _ _) (hk.trans hwin)
    (hk'.trans hwin)
  rw [hBeq] at hdom
  have hX : QUEFromQDiff_X d n (E + η * Complex.I) (fun u => if u = a then 1 else 0) ω =
      (trace (QUEFromQDiff_imG (seqXmat d n ω) (E + η * Complex.I) *
        (Epaper (d.L n) (d.W n) a - ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *
        QUEFromQDiff_imG (seqXmat d n ω) (E + η * Complex.I) *
        (Epaper (d.L n) (d.W n) a - ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)))).re := by
    unfold QUEFromQDiff_X; rw [hBeq]
  rw [hX, norm_mul, mul_pow, Complex.norm_natCast, ← Complex.normSq_eq_norm_sq]
  have hN : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ 2 := by positivity
  calc ((d.size n : ℕ) : ℝ) ^ 2 * Complex.normSq _
      ≤ ((d.size n : ℕ) : ℝ) ^ 2 * (4 * η ^ 2 * _) := mul_le_mul_of_nonneg_left hdom hN
    _ = _ := by ring

/-- `(Meq:QUE2)` event inside `{N^{-τ/3} ≤ 4 N² η² X_{1_A/|A|}}`. -/
private theorem QUEFromQDiff_que2Bad_sub {τ E η : ℝ} (hη : 0 < η)
    (hwin : ((d.size n : ℕ) : ℝ) ^ (-1 - τ) * (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ η)
    (A : Finset (Z2 (d.L n))) (hA : A.Nonempty) :
    {ω | que2Bad d n τ E A ω} ⊆ {ω | ((d.size n : ℕ) : ℝ) ^ (-τ / 3) ≤
      4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFromQDiff_X d n (E + η * Complex.I)
          (fun u => if u ∈ A then (A.card : ℝ)⁻¹ else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, k, hk, hbad⟩ := hω
  simp only [Set.mem_ofPred_eq]
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := (d.W n : ℝ) with hWdef
  set cA : Z2 (d.L n) → ℝ := fun u => if u ∈ A then (A.card : ℝ)⁻¹ else 0 with hcA
  have hNpos : 0 < N := by
    rw [hNdef]
    have : 0 < d.size n := by
      rw [Sizes.size]; have := d.W_pos n; have := d.three_le_L n; positivity
    exact_mod_cast this
  have hWpos : 0 < W := by rw [hWdef]; exact_mod_cast d.W_pos n
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hdom := QUEFromQDiff_normSq_le hψ hη (QUEFromQDiff_B (d.L n) (d.W n) cA)
    (QUEFromQDiff_B_herm _ _ _) (hk.trans hwin) (hk.trans hwin)
  have hX : QUEFromQDiff_X d n (E + η * Complex.I) cA ω =
      (trace (QUEFromQDiff_imG (seqXmat d n ω) (E + η * Complex.I) *
        QUEFromQDiff_B (d.L n) (d.W n) cA *
        QUEFromQDiff_imG (seqXmat d n ω) (E + η * Complex.I) *
        QUEFromQDiff_B (d.L n) (d.W n) cA)).re := rfl
  rw [hX]
  -- the quadratic form is real: `ψ_k^* B ψ_k = r`
  set S : Z2 (d.L n) → ℝ := fun u => ∑ x ∈ Iblk (d.L n) (d.W n) u, ‖ψ k x‖ ^ 2 with hS
  set r : ℝ := (A.card : ℝ)⁻¹ * (W ^ 2)⁻¹ * ∑ a ∈ A, S a - N⁻¹ with hr
  have hunit : star (ψ k) ⬝ᵥ ψ k = 1 := by rw [hψ.1 k k]; simp
  have hC : star (ψ k) ⬝ᵥ (QUEFromQDiff_B (d.L n) (d.W n) cA *ᵥ ψ k) = (r : ℂ) := by
    rw [QUEFromQDiff_B_eq, sub_mulVec, sum_mulVec, dotProduct_sub, dotProduct_sum,
      smul_mulVec, one_mulVec, dotProduct_smul, hunit]
    simp only [smul_mulVec, dotProduct_smul, QUEFromQDiff_quad_Epaper, smul_eq_mul]
    have hsum : ∑ u, ((cA u : ℝ) : ℂ) * ((((W : ℝ) ^ 2)⁻¹ * S u : ℝ) : ℂ) =
        (((A.card : ℝ)⁻¹ * (W ^ 2)⁻¹ * ∑ a ∈ A, S a : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
      have hf : Finset.univ.filter (· ∈ A) = A := by ext x; simp
      rw [hf]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => x ∉ A),
          ((cA x : ℝ) : ℂ) * (((W : ℂ) ^ 2)⁻¹ * (S x : ℂ)) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_filter] at hx
        simp [hcA, hx.2]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [hcA, hx, ite_true]
      push_cast
      ring
    rw [hsum, hr, hNdef]
    push_cast
    simp only [Sizes.size]
    push_cast
    ring
  rw [hC, Complex.normSq_ofReal] at hdom
  -- the event gives `N^{-τ/6} ≤ N |r|`
  have hid : ∑ a ∈ A, S a - (A.card : ℝ) * W ^ 2 / N = (A.card : ℝ) * W ^ 2 * r := by
    rw [hr]; field_simp
  have hbad' : (A.card : ℝ) * W ^ 2 / N ^ (1 + τ / 6) ≤ (A.card : ℝ) * W ^ 2 * |r| := by
    have := hbad
    have hsumS : A.sum S = ∑ a ∈ A, S a := rfl
    rw [hsumS, hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A.card : ℝ) * W ^ 2)] at this
    exact this
  have hpow : N ^ (1 + τ / 6) = N * N ^ (τ / 6) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hNt : 0 < N ^ (τ / 6) := Real.rpow_pos_of_pos hNpos _
  have h1 : N ^ (-τ / 6) ≤ N * |r| := by
    rw [hpow] at hbad'
    have hAW : 0 < (A.card : ℝ) * W ^ 2 := by positivity
    have h2 : 1 / (N * N ^ (τ / 6)) ≤ |r| := by
      rw [div_eq_mul_one_div, mul_comm] at hbad'
      exact le_of_mul_le_mul_right (by linarith [hbad']) hAW
    have h3 : N ^ (-τ / 6) = N * (1 / (N * N ^ (τ / 6))) := by
      rw [neg_div, Real.rpow_neg hNpos.le]
      field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 hNpos.le
  have hsq : N ^ (-τ / 3) = N ^ (-τ / 6) * N ^ (-τ / 6) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [hsq]
  have h0 : 0 ≤ N ^ (-τ / 6) := (Real.rpow_pos_of_pos hNpos _).le
  calc N ^ (-τ / 6) * N ^ (-τ / 6) ≤ (N * |r|) * (N * |r|) := mul_le_mul h1 h1 h0 (by positivity)
    _ = N ^ 2 * (r * r) := by
        rw [show N * |r| * (N * |r|) = N ^ 2 * (|r| * |r|) by ring, abs_mul_abs_self]
    _ ≤ N ^ 2 * (4 * η ^ 2 * _) := mul_le_mul_of_nonneg_left hdom (by positivity)
    _ = _ := by ring

end Events

/-! ### Markov -/

private theorem QUEFromQDiff_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    {s T : ℝ} (hs : 0 < s) (hT : ∫ ω, f ω ∂P ≤ T) (S : Set Ω') (hS : S ⊆ {ω | s ≤ f ω}) :
    P S ≤ ENNReal.ofReal (T / s) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hf s
  have hreal : P.real {ω | s ≤ f ω} ≤ T / s := by
    rw [le_div_iff₀ hs, mul_comm]
    exact h.trans hT
  calc P S ≤ P {ω | s ≤ f ω} := measure_mono hS
    _ = ENNReal.ofReal (P.real {ω | s ≤ f ω}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (T / s) := ENNReal.ofReal_le_ofReal hreal

/-! ### The exponent chain -/

/-- `W^{2/3} ≤ M_η` when `W² L² η = W^{2/3}`. -/
private theorem QUEFromQDiff_Meta_ge (L W : ℕ) (z : ℂ) (hη : 0 < z.im) (hW1 : 1 ≤ (W : ℝ))
    (hNη : (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * z.im = (W : ℝ) ^ ((2 : ℝ) / 3)) :
    (W : ℝ) ^ ((2 : ℝ) / 3) ≤ Meta L W z := by
  unfold Meta ellz
  set η := z.im with hηdef
  have hW2 : (W : ℝ) ^ ((2 : ℝ) / 3) ≤ (W : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  rcases min_choice (η ^ (-(1 / 2 : ℝ))) (L : ℝ) with hmin | hmin
  · rw [hmin]
    have hsq : (η ^ (-(1 / 2 : ℝ))) ^ 2 * η = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      norm_num
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hη.ne']
    have h0 : 0 ≤ η ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hη.le _
    have h1 : 1 ≤ (η ^ (-(1 / 2 : ℝ)) + 1) ^ 2 * η := by nlinarith
    calc (W : ℝ) ^ ((2 : ℝ) / 3) ≤ (W : ℝ) ^ 2 * 1 := by rw [mul_one]; exact hW2
      _ ≤ (W : ℝ) ^ 2 * ((η ^ (-(1 / 2 : ℝ)) + 1) ^ 2 * η) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (W : ℝ) ^ 2 * (η ^ (-(1 / 2 : ℝ)) + 1) ^ 2 * η := by ring
  · rw [hmin, ← hNη]
    have hL : (L : ℝ) ^ 2 ≤ ((L : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
    have := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 2)
    exact mul_le_mul_of_nonneg_right this hη.le

/-- `W = w¹²`, `W^{2/3} = w⁸` and `N^{𝔠/12} ≤ w` for `w = W^{1/12}`. -/
private theorem QUEFromQDiff_w_facts {𝔠 N W : ℝ} (hW1 : 1 ≤ W) (hN1 : 1 ≤ N)
    (hNW : N ^ 𝔠 ≤ W) :
    W = (W ^ (1 / 12 : ℝ)) ^ 12 ∧ W ^ ((2 : ℝ) / 3) = (W ^ (1 / 12 : ℝ)) ^ 8 ∧
      N ^ (𝔠 / 12) ≤ W ^ (1 / 12 : ℝ) ∧ 1 ≤ W ^ (1 / 12 : ℝ) := by
  have hW0 : 0 ≤ W := by linarith
  refine ⟨?_, ?_, ?_, Real.one_le_rpow hW1 (by norm_num)⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; norm_num
  · have h1 : N ^ (𝔠 / 12) = (N ^ 𝔠) ^ (1 / 12 : ℝ) := by
      rw [← Real.rpow_mul (by linarith)]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hNW (by norm_num)

/-- The spectral domain and the window, at `η = W^{2/3}/N`. -/
private theorem QUEFromQDiff_domain {𝔠 τ τQ N W L : ℝ} (hτ : 0 < τ) (hτQ𝔠 : τQ ≤ 𝔠 / 12)
    (hW1 : 1 ≤ W) (hL3 : 3 ≤ L) (hNeq : N = W ^ 2 * L ^ 2) (hNW : N ^ 𝔠 ≤ W) :
    N ^ (-1 + τQ) ≤ W ^ ((2 : ℝ) / 3) / N ∧ W ^ ((2 : ℝ) / 3) / N ≤ 1 ∧
      N ^ (-1 - τ) * W ^ ((2 : ℝ) / 3) ≤ W ^ ((2 : ℝ) / 3) / N := by
  have hL1 : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
  have hW21 : 1 ≤ W ^ 2 := one_le_pow₀ hW1
  have hN1 : 1 ≤ N := by rw [hNeq]; nlinarith
  have hNpos : 0 < N := by linarith
  obtain ⟨hWw, hW23, hNc, hw1⟩ := QUEFromQDiff_w_facts hW1 hN1 hNW
  set w := W ^ (1 / 12 : ℝ) with hwdef
  have hw8 : w ≤ w ^ 8 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 8 := pow_le_pow_right₀ hw1 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : N ^ (-1 + τQ) = N⁻¹ * N ^ τQ := by
      rw [Real.rpow_add hNpos, Real.rpow_neg_one]
    have h2 : N ^ τQ ≤ w ^ 8 :=
      ((Real.rpow_le_rpow_of_exponent_le hN1 hτQ𝔠).trans hNc).trans hw8
    rw [h1, hW23, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · rw [div_le_one hNpos, hW23, hNeq, hWw]
    have : w ^ 8 ≤ (w ^ 12) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hw1 (by norm_num)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < w) 24]
  · rw [show W ^ ((2 : ℝ) / 3) / N = N⁻¹ * W ^ ((2 : ℝ) / 3) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ W) _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- The exponent chain: `16 N² η² (90 W⁻² (1 + log L) + M⁻³ W^{τ_Q}) ≤ N^{-τ/2}` at
`η = W^{2/3}/N`, once `16 (91 + 1080/𝔠) ≤ W^{1/12}`. -/
private theorem QUEFromQDiff_chain {𝔠 τ τQ N W L M : ℝ} (h𝔠 : 0 < 𝔠) (hτ𝔠 : τ < 𝔠 / 2)
    (hτQ1 : τQ ≤ 1 / 12) (hW1 : 1 ≤ W) (hL3 : 3 ≤ L) (hNeq : N = W ^ 2 * L ^ 2)
    (hNW : N ^ 𝔠 ≤ W) (hKw : 16 * (91 + 1080 / 𝔠) ≤ W ^ (1 / 12 : ℝ))
    (hM : W ^ ((2 : ℝ) / 3) ≤ M) :
    4 * N ^ 2 * (W ^ ((2 : ℝ) / 3) / N) ^ 2 *
        (4 * ((W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + M ^ (-(3 : ℤ)) * W ^ τQ)) ≤
      N ^ (-τ / 2) := by
  have hL1 : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
  have hW21 : 1 ≤ W ^ 2 := one_le_pow₀ hW1
  have hN1 : 1 ≤ N := by rw [hNeq]; nlinarith
  have hNpos : 0 < N := by linarith
  obtain ⟨hWw, hW23, hNc, hw1⟩ := QUEFromQDiff_w_facts hW1 hN1 hNW
  set w := W ^ (1 / 12 : ℝ) with hwdef
  have hwpos : 0 < w := by linarith
  -- `ε ≤ w/w²⁴`
  have hε : M ^ (-(3 : ℤ)) * W ^ τQ ≤ w / w ^ 24 := by
    have hMpos : 0 < M := lt_of_lt_of_le (by rw [hW23]; positivity) hM
    have h1 : M ^ (-(3 : ℤ)) ≤ (w ^ 24)⁻¹ := by
      rw [_root_.zpow_neg, zpow_ofNat]
      apply inv_anti₀ (by positivity)
      calc w ^ 24 = (w ^ 8) ^ 3 := by ring
        _ ≤ M ^ 3 := pow_le_pow_left₀ (by positivity) (hW23 ▸ hM) 3
    have h2 : W ^ τQ ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 hτQ1
    have h3 : 0 ≤ W ^ τQ := Real.rpow_nonneg (by linarith) _
    calc M ^ (-(3 : ℤ)) * W ^ τQ ≤ (w ^ 24)⁻¹ * w := mul_le_mul h1 h2 h3 (by positivity)
      _ = w / w ^ 24 := by ring
  -- `δ ≤ 90 (1 + 12/𝔠) w/w²⁴`
  have hδ : (W ^ 2)⁻¹ * (90 * (1 + Real.log L)) ≤ 90 * (1 + 12 / 𝔠) * w / w ^ 24 := by
    have hlog : Real.log L ≤ L ^ (𝔠 / 12) / (𝔠 / 12) :=
      Real.log_le_rpow_div (by linarith) (by positivity)
    have hLN : L ^ (𝔠 / 12) ≤ w := by
      refine le_trans (Real.rpow_le_rpow (by linarith) ?_ (by positivity)) hNc
      rw [hNeq]; nlinarith
    have h12 : L ^ (𝔠 / 12) / (𝔠 / 12) ≤ 12 / 𝔠 * w := by
      rw [div_le_iff₀ (by positivity)]
      have : 12 / 𝔠 * w * (𝔠 / 12) = w := by field_simp
      rw [this]; exact hLN
    have h1 : 1 + Real.log L ≤ (1 + 12 / 𝔠) * w := by nlinarith
    have hW2 : W ^ 2 = w ^ 24 := by rw [hWw]; ring
    rw [hW2, div_eq_mul_inv, mul_comm _ ((w ^ 24)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  have hsum : (W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + M ^ (-(3 : ℤ)) * W ^ τQ ≤
      (91 + 1080 / 𝔠) * w / w ^ 24 := by
    have h : 90 * (1 + 12 / 𝔠) * w / w ^ 24 + w / w ^ 24 = (91 + 1080 / 𝔠) * w / w ^ 24 := by
      field_simp; ring
    linarith
  have hNη : N * (W ^ ((2 : ℝ) / 3) / N) = w ^ 8 := by rw [hW23]; field_simp
  have hN2η2 : 4 * N ^ 2 * (W ^ ((2 : ℝ) / 3) / N) ^ 2 = 4 * w ^ 16 := by
    rw [show 4 * N ^ 2 * (W ^ ((2 : ℝ) / 3) / N) ^ 2 =
      4 * (N * (W ^ ((2 : ℝ) / 3) / N)) ^ 2 by ring, hNη]; ring
  have hNτ : N ^ (τ / 2) ≤ w ^ 3 := by
    calc N ^ (τ / 2) ≤ N ^ (𝔠 / 12 * 3) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N ^ (𝔠 / 12)) ^ 3 := by rw [Real.rpow_mul hNpos.le]; norm_num
      _ ≤ w ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hNc 3
  rw [hN2η2]
  set K : ℝ := 16 * (91 + 1080 / 𝔠) with hKdef
  have h1 : 4 * w ^ 16 * (4 * ((91 + 1080 / 𝔠) * w / w ^ 24)) = K / w ^ 7 := by
    rw [hKdef]; field_simp; ring
  have h2 : K / w ^ 7 ≤ 1 / w ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : w ≤ w ^ 4 := by
      calc w = w ^ 1 := (pow_one w).symm
        _ ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
    have h7 : w ^ 7 = w ^ 3 * w ^ 4 := by ring
    rw [h7, one_mul]
    have := mul_le_mul_of_nonneg_left (hKw.trans h4) (by positivity : (0 : ℝ) ≤ w ^ 3)
    linarith
  have h3 : 1 / w ^ 3 ≤ N ^ (-τ / 2) := by
    rw [neg_div, Real.rpow_neg hNpos.le, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hNpos _) hNτ
  calc 4 * w ^ 16 * (4 * ((W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + M ^ (-(3 : ℤ)) * W ^ τQ))
      ≤ 4 * w ^ 16 * (4 * ((91 + 1080 / 𝔠) * w / w ^ 24)) := by gcongr
    _ = K / w ^ 7 := h1
    _ ≤ N ^ (-τ / 2) := h2.trans h3

/-! ### The deduction at a fixed size -/

private theorem QUEFromQDiff_fixed (d : Sizes) (n : ℕ) {𝔠 τ κ τQ : ℝ} (h𝔠 : 0 < 𝔠)
    (hτ : 0 < τ) (hτ𝔠 : τ < 𝔠 / 2) (hτQ𝔠 : τQ ≤ 𝔠 / 12) (hτQ1 : τQ ≤ 1 / 12)
    (hn : ∀ z : ℂ, locDomain (d.size n) κ τQ z → ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGE d n ω z σ a b ∂(seqP d)) - profile (d.L n) (d.W n) z σ a b‖ ≤
        Meta (d.L n) (d.W n) z ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τQ)
    (hNW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (hKw : 16 * (91 + 1080 / 𝔠) ≤ (d.W n : ℝ) ^ (1 / 12 : ℝ)) (E : ℝ) (hE : |E| < 2 - κ) :
    (∀ a : Z2 (d.L n),
      seqP d {ω | queBad d n τ E a ω} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6))) ∧
    (∀ A : Finset (Z2 (d.L n)), A.Nonempty →
      seqP d {ω | que2Bad d n τ E A ω} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6))) := by
  have hW1 : 1 ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hL3 : 3 ≤ (d.L n : ℝ) := by exact_mod_cast d.three_le_L n
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) := by
    rw [hNeq]; nlinarith [one_le_pow₀ (n := 2) hW1,
      one_le_pow₀ (n := 2) (by linarith : (1 : ℝ) ≤ (d.L n : ℝ))]
  have hNpos : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  obtain ⟨hdom1, hdom2, hwin⟩ := QUEFromQDiff_domain (L := (d.L n : ℝ)) hτ hτQ𝔠 hW1 hL3
    hNeq hNW
  set η : ℝ := (d.W n : ℝ) ^ ((2 : ℝ) / 3) / ((d.size n : ℕ) : ℝ) with hηdef
  have hηpos : 0 < η := by positivity
  have hzim : (E + η * Complex.I : ℂ).im = η := by simp
  have hzre : (E + η * Complex.I : ℂ).re = E := by simp
  have hdom : locDomain (d.size n) κ τQ (E + η * Complex.I) :=
    ⟨by rw [hzre]; exact hE.le, by rw [hzim]; exact hdom1, by rw [hzim]; exact hdom2⟩
  have hQ2 := hn _ hdom
  have hMeta : (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ Meta (d.L n) (d.W n) (E + η * Complex.I) := by
    refine QUEFromQDiff_Meta_ge (d.L n) (d.W n) _ (by rw [hzim]; exact hηpos) hW1 ?_
    rw [hzim, hηdef, ← hNeq]; field_simp
  have hchain := QUEFromQDiff_chain h𝔠 hτ𝔠 hτQ1 hW1 hL3 hNeq hNW hKw hMeta
  have hEY : ∀ c : Z2 (d.L n) → ℝ, (∀ u, 0 ≤ c u) → ∑ u, c u = 1 →
      Integrable (fun ω => 4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFromQDiff_X d n (E + η * Complex.I) c ω) (seqP d) ∧
      (∀ ω, 0 ≤ 4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFromQDiff_X d n (E + η * Complex.I) c ω) ∧
      ∫ ω, 4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFromQDiff_X d n (E + η * Complex.I) c ω ∂(seqP d) ≤
          ((d.size n : ℕ) : ℝ) ^ (-τ / 2) := by
    intro c hc0 hc1
    obtain ⟨hint, hnn, hle⟩ := QUEFromQDiff_core d n E hηpos hQ2 c hc0 hc1
    refine ⟨hint.const_mul _, fun ω => by have := hnn ω; positivity, ?_⟩
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hchain
  refine ⟨fun a => ?_, fun A hA => ?_⟩
  · -- `(Meq:QUE)`
    have hc0 : ∀ u, 0 ≤ (fun u => if u = a then (1 : ℝ) else 0) u := fun u => by
      simp only; split_ifs <;> norm_num
    have hc1 : ∑ u, (fun u => if u = a then (1 : ℝ) else 0) u = 1 := by simp
    obtain ⟨hint, hnn, hle⟩ := hEY _ hc0 hc1
    have hs : 0 < ((d.size n : ℕ) : ℝ) ^ (-τ / 6) := Real.rpow_pos_of_pos hNpos _
    have hsub := QUEFromQDiff_queBad_sub d n hηpos hwin (τ := τ) (E := E) a
    refine (QUEFromQDiff_markov (seqP d) _ hint hnn hs hle _ hsub).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · -- `(Meq:QUE2)`
    have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hc0 : ∀ u, 0 ≤ (fun u => if u ∈ A then (A.card : ℝ)⁻¹ else 0) u := fun u => by
      simp only; split_ifs
      · positivity
      · exact le_rfl
    have hc1 : ∑ u, (fun u => if u ∈ A then (A.card : ℝ)⁻¹ else 0) u = 1 := by
      simp only
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp
    obtain ⟨hint, hnn, hle⟩ := hEY _ hc0 hc1
    have hs : 0 < ((d.size n : ℕ) : ℝ) ^ (-τ / 3) := Real.rpow_pos_of_pos hNpos _
    have hsub := QUEFromQDiff_que2Bad_sub d n hηpos hwin (τ := τ) (E := E) A hA
    refine (QUEFromQDiff_markov (seqP d) _ hint hnn hs hle _ hsub).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
    exact le_of_eq (by ring_nf)

/-! ### The deduction -/

/-- **`MR:QUE` from `MR:QDiff`** (Theorem `MR:QUE` and its proof via `(ssfa2)`, `(que0)`,
`(que2)`).  The proof takes `η = W^{2/3}/N` (not the paper's `N^{-1-τ} W^{2/3}`), `QDiff` at
`τ_Q = min(𝔠,1)/12`, `D = 1`, and only its expectation half `(Meq:QdS1)`/`(Meq:QdS2)`; the
profile differences come from the Fourier bound `norm_Theta_sub_le_log`; Markov's inequality at
the end. -/
theorem QUE_of_QDiff : QDiff → QUE := by
  intro hQ 𝔠 h𝔠 d hAdm τ hτ hτ𝔠 κ hκ
  have hτQpos : 0 < min 𝔠 1 / 12 := div_pos (lt_min h𝔠 one_pos) (by norm_num)
  have hτQ𝔠 : min 𝔠 1 / 12 ≤ 𝔠 / 12 := by
    have := min_le_left 𝔠 1; linarith
  have hτQ1 : min 𝔠 1 / 12 ≤ 1 / 12 := by
    have := min_le_right 𝔠 1; linarith
  have hQ' := hQ 𝔠 h𝔠 d hAdm κ (min 𝔠 1 / 12) 1 hκ hτQpos one_pos
  have hNt : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hAdm.1
  have hWt : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hAdm.2 ((tendsto_rpow_atTop h𝔠).comp hNt)
  have hwK : ∀ᶠ n in atTop, 16 * (91 + 1080 / 𝔠) ≤ (d.W n : ℝ) ^ (1 / 12 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hWt).eventually_ge_atTop _
  filter_upwards [hQ', hAdm.2, hwK] with n hn hNW hKw
  intro E hE
  exact QUEFromQDiff_fixed d n h𝔠 hτ hτ𝔠 hτQ𝔠 hτQ1 (fun z hz σ a b => (hn z hz σ).2 a b)
    hNW hKw E hE

end RBM.Endpoints
