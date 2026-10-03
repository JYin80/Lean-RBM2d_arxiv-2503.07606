/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.ZeroModeProfile

/-!
# The weak QUE for `𝐇_t` from (7.47)

`g2bRow : G2bRow`: for `𝔠 > 0`, an admissible `d` and `0 < τ_U ≤ ouTauMax 𝔠`, the statement
`OUEq747` ((7.47) for `𝐇_t` with `Θ̃`, at the QUE scale `z = E + i η_Q`, `η_Q = W^{2/3}/N`) gives
`OUQUE`: the weak QUE `(Meq:QUE)` for `𝐇_t` at `τ = 𝔠/3`, uniformly in `t ∈ [0, t*]`,
`|E| < 2 - κ` and the block `a`.

Proof: the argument of `QUE_of_QDiff` (`Main/QUEFromQDiff.lean`) re-run on `ouMat` under `ouP`:
* `seqXmat d n ω` under `seqP d` becomes `ouMat L W t ω` under `ouP L W` (Hermitian; measurable by
  `ZeroModeProfile_measurable_trGEGEmat`), `trGEGE` becomes `trGEGEmat`, `queBad` becomes
  `queBadMat`;
* the expectation half of `QDiff` becomes `OUEq747` at `z = E + i η_Q` with the loss `W^{1/12}`
  (any `δ > 0` is allowed by the statement); `profile` with `Θ_ξ` becomes `profileTilde` with
  `Θ̃_ξ`;
* the oscillation `‖Θ̃_ξ(u,v) - Θ̃_ξ(0,0)‖ ≤ 90 (1 + log L)` is `norm_ThetaTilde_sub_le` (valid for
  `0 ≤ ζ ≤ 1`, `‖ξ‖ < 1`; here `ζ = ouZeta t ∈ [0, 1]`).  The coefficients `c_u - L⁻²` of
  `B = ∑_u (c_u - L⁻²) E_u` sum to zero, so the constant zero mode of `Θ̃` cancels exactly as the
  `(0, 0)` value does;
* uniformity in `(t, E)`: `OUEq747` is per sequence `(E_n, t_n)`; the worst-sequence argument
  `ZeroModeProfile_eventually_forall_mem_of_forall_seq'` (as `ouDiag_of_ouLL`) gives the statement
  "eventually, for all `t ∈ [0, t*]`, `|E| ≤ 2 - κ`", then the Markov step at each `(t, E, a)`.

The proof is the `d = 2` re-run of `QUE_of_QDiff` (Fourier bound for `Θ̃`, `N = W² L²`).

Helpers are `private` with the prefix `QUEFlow_` (copied from the private helpers of
`Main/QUEFromQDiff.lean`, prefix `QUEFromQDiff_`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped ComplexConjugate NNReal ENNReal

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- The matrix imaginary part `Im G = (G - G†)/(2i)`. -/
private noncomputable def QUEFlow_imG (H : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  ((2 : ℂ) * Complex.I)⁻¹ • (green H z - (green H z)ᴴ)

/-- The matrix of eigenvector columns. -/
private def QUEFlow_U (ψ : ι → ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y

private theorem QUEFlow_UU (hψ : IsOrthoEigenbasis H μ ψ) :
    star (QUEFlow_U ψ) * QUEFlow_U ψ = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, QUEFlow_U, Matrix.of_apply,
    Matrix.one_apply]
  exact h

private theorem QUEFlow_green_eq (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) :
    green H z = QUEFlow_U ψ * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) *
      star (QUEFlow_U ψ) := by
  set U := QUEFlow_U ψ with hU
  have hUU : star U * U = 1 := QUEFlow_UU hψ
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, QUEFlow_U, Matrix.of_apply]
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
private noncomputable def QUEFlow_w (μ : ι → ℝ) (E η : ℝ) (l : ι) : ℝ :=
  η / ((μ l - E) ^ 2 + η ^ 2)

/-- `Im G(E + iη) = U diag(w) U*` for any orthonormal eigenbasis. -/
private theorem QUEFlow_imG_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) :
    QUEFlow_imG H (E + η * Complex.I) = QUEFlow_U ψ *
      diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) * star (QUEFlow_U ψ) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hz : ∀ l, (μ l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp [hzdef] at this
    exact hη this.symm
  set U := QUEFlow_U ψ with hU
  set d : ι → ℂ := fun l => ((μ l : ℂ) - z)⁻¹ with hd
  have hG := QUEFlow_green_eq hψ hz
  rw [← hd] at hG
  have hGH : (green H z)ᴴ = U * diagonal (star d) * star U := by
    rw [hG, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdiag : diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) =
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
    have hdim : (d l).im = QUEFlow_w μ E η l := by
      simp only [hd, Complex.inv_im, hn, him, QUEFlow_w]
      ring
    rw [hdim]
    have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
    push_cast
    ring
  unfold QUEFlow_imG
  rw [hGH, hG, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
/-- The entry `(U* B U)_{lm} = ψ_l^* B ψ_m`. -/
private theorem QUEFlow_C_apply (B : Matrix ι ι ℂ) (l m : ι) :
    (star (QUEFlow_U ψ) * B * QUEFlow_U ψ) l m = star (ψ l) ⬝ᵥ (B *ᵥ ψ m) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, QUEFlow_U,
    Matrix.star_apply, Matrix.of_apply, Pi.star_apply]

/-- For Hermitian `B`: `tr(Im G B Im G B) = ∑_{l,m} w_l w_m |ψ_l^* B ψ_m|²`. -/
private theorem QUEFlow_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    trace (QUEFlow_imG H (E + η * Complex.I) * B *
        QUEFlow_imG H (E + η * Complex.I) * B) =
      ∑ l, ∑ m, ((QUEFlow_w μ E η l * QUEFlow_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) : ℝ) : ℂ) := by
  rw [QUEFlow_imG_eq hψ E hη]
  set U := QUEFlow_U ψ with hU
  set D : Matrix ι ι ℂ := diagonal (fun l => ((QUEFlow_w μ E η l : ℝ) : ℂ)) with hD
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
  rw [hml, hD, mul_diagonal, diagonal_mul, ← QUEFlow_C_apply B l m]
  rw [RCLike.star_def]
  have := Complex.mul_conj (C l m)
  push_cast
  linear_combination (((QUEFlow_w μ E η l : ℝ) : ℂ) *
    ((QUEFlow_w μ E η m : ℝ) : ℂ)) * this

private theorem QUEFlow_re_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    (trace (QUEFlow_imG H (E + η * Complex.I) * B *
        QUEFlow_imG H (E + η * Complex.I) * B)).re =
      ∑ l, ∑ m, QUEFlow_w μ E η l * QUEFlow_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
  rw [QUEFlow_trace_eq hψ E hη B hB, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] in
private theorem QUEFlow_w_nonneg (μ : ι → ℝ) (E : ℝ) {η : ℝ} (hη : 0 ≤ η) (l : ι) :
    0 ≤ QUEFlow_w μ E η l := by
  unfold QUEFlow_w
  positivity

/-- `Re tr(Im G B Im G B) ≥ 0` for Hermitian `B`. -/
private theorem QUEFlow_re_trace_nonneg (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    0 ≤ (trace (QUEFlow_imG H (E + η * Complex.I) * B *
        QUEFlow_imG H (E + η * Complex.I) * B)).re := by
  rw [QUEFlow_re_trace_eq hψ E hη.ne' B hB]
  refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => ?_
  have := QUEFlow_w_nonneg μ E hη.le l
  have := QUEFlow_w_nonneg μ E hη.le m
  have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
  positivity

/-- **Pointwise domination.** If `|μ_k - E| ≤ η` and `|μ_{k'} - E| ≤ η`, then
`|ψ_k^* B ψ_{k'}|² ≤ 4 η² Re tr(Im G B Im G B)`. -/
private theorem QUEFlow_normSq_le (hψ : IsOrthoEigenbasis H μ ψ) {E η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) {k k' : ι}
    (hk : |μ k - E| ≤ η) (hk' : |μ k' - E| ≤ η) :
    Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      4 * η ^ 2 * (trace (QUEFlow_imG H (E + η * Complex.I) * B *
        QUEFlow_imG H (E + η * Complex.I) * B)).re := by
  rw [QUEFlow_re_trace_eq hψ E hη.ne' B hB]
  have hterm : ∀ l ∈ Finset.univ, ∀ m ∈ Finset.univ, 0 ≤ QUEFlow_w μ E η l *
      QUEFlow_w μ E η m * Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
    intro l _ m _
    have := QUEFlow_w_nonneg μ E hη.le l
    have := QUEFlow_w_nonneg μ E hη.le m
    have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
    positivity
  have hsingle : QUEFlow_w μ E η k * QUEFlow_w μ E η k' *
      Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      ∑ l, ∑ m, QUEFlow_w μ E η l * QUEFlow_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) :=
    le_trans (Finset.single_le_sum (hterm k (Finset.mem_univ k)) (Finset.mem_univ k'))
      (Finset.single_le_sum (fun l hl => Finset.sum_nonneg (hterm l hl))
        (Finset.mem_univ k))
  have hw : ∀ j, |μ j - E| ≤ η → 1 / (2 * η) ≤ QUEFlow_w μ E η j := by
    intro j hj
    unfold QUEFlow_w
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
      QUEFlow_w μ E η k * QUEFlow_w μ E η k' :=
    mul_le_mul hwk hwk' (by positivity) (QUEFlow_w_nonneg μ E hη.le k)
  have hkey : c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := by
    field_simp
    ring
  calc c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := hkey
    _ ≤ 4 * η ^ 2 * (QUEFlow_w μ E η k * QUEFlow_w μ E η k' * c) := by
        gcongr
    _ ≤ _ := by gcongr

/-- Every Hermitian matrix has an orthonormal eigenbasis in the sense of
`IsOrthoEigenbasis` (Mathlib's `eigenvectorBasis`). -/
private theorem QUEFlow_exists_basis (hH : H.IsHermitian) :
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
private theorem QUEFlow_trace_imG (G Eu Ev : Matrix ι ι ℂ) (hEu : Euᴴ = Eu)
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
private theorem QUEFlow_trace_sum {κ : Type*} [Fintype κ] (M : Matrix ι ι ℂ)
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
private theorem QUEFlow_norm_double_sum_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
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
private noncomputable def QUEFlow_B (c : Z2 L → ℝ) :
    Matrix (Z2 (W * L)) (Z2 (W * L)) ℂ :=
  ∑ u, (((c u - ((L : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) • Epaper L W u

private theorem QUEFlow_B_herm (c : Z2 L → ℝ) :
    (QUEFlow_B L W c)ᴴ = QUEFlow_B L W c := by
  unfold QUEFlow_B
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [conjTranspose_smul, Epaper_conjTranspose, RCLike.star_def, Complex.conj_ofReal]

private theorem QUEFlow_B_eq (c : Z2 L → ℝ) :
    QUEFlow_B L W c = ∑ u, ((c u : ℝ) : ℂ) • Epaper L W u -
      ((((W * L) ^ 2 : ℕ) : ℂ))⁻¹ • (1 : Matrix _ _ ℂ) := by
  unfold QUEFlow_B
  simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.smul_sum, sum_Epaper, smul_smul]
  congr 1
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  push_cast
  field_simp

private theorem QUEFlow_card : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

private theorem QUEFlow_sum_beta (c : Z2 L → ℝ) (hc1 : ∑ u, c u = 1) :
    ∑ u, (c u - ((L : ℝ) ^ 2)⁻¹) = 0 := by
  rw [Finset.sum_sub_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    QUEFlow_card]
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  field_simp
  ring

private theorem QUEFlow_sum_abs_beta (c : Z2 L → ℝ) (hc0 : ∀ u, 0 ≤ c u)
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
          QUEFlow_card]
        field_simp
        ring

end Observable

/-! ### Integrability of `tr(G E_a G^σ E_b)` under `ouP` -/

section Integr

variable (L W : ℕ) [NeZero L] [NeZero W] (t : ℝ)

open scoped Matrix.Norms.L2Operator in
private theorem QUEFlow_trGEGEmat_bound {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (a b : Z2 L)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian) :
    ‖trGEGEmat L W M z σ a b‖ ≤ (Fintype.card (Idx L W) : ℝ) * (|z.im|⁻¹ *
      ‖Epaper L W a‖ * |z.im|⁻¹ * ‖Epaper L W b‖) := by
  have hG : ‖green M z‖ ≤ |z.im|⁻¹ := norm_green_le hM (abs_pos.mpr hz) le_rfl
  have hGσ : ‖(if σ then green M z else (green M z)ᴴ)‖ ≤ |z.im|⁻¹ := by
    cases σ
    · simp only [Bool.false_eq_true, ite_false, l2_opNorm_conjTranspose]; exact hG
    · simp only [ite_true]; exact hG
  unfold trGEGEmat
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr

private theorem QUEFlow_trGEGEmat_integrable {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (a b : Z2 L) :
    Integrable (fun ω => trGEGEmat L W (ouMat L W t ω) z σ a b) (ouP L W) := by
  have hm : Measurable fun ω => trGEGEmat L W (ouMat L W t ω) z σ a b :=
    (ZeroModeProfile_measurable_trGEGEmat L W z σ a b).comp (measurable_ouMat L W t)
  exact Integrable.of_bound hm.aestronglyMeasurable _
    (ae_of_all _ fun ω => QUEFlow_trGEGEmat_bound L W hz σ a b _ (ouMat_isHermitian L W t ω))

end Integr

/-! ### The profile differences (`Θ̃`, `norm_ThetaTilde_sub_le`) -/

private theorem QUEFlow_norm_xi_lt_one {z : ℂ} (hz : 0 < z.im) (σ : Bool) :
    ‖(if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ))‖ < 1 := by
  have hm : ‖mSC z‖ < 1 := by rw [mSC_eq_msc hz]; exact norm_msc_lt_one hz
  have hm2 : ‖mSC z‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hm two_ne_zero
  cases σ
  · simp only [Bool.false_eq_true, ite_false, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact hm2
  · simp only [ite_true, norm_pow]
    exact hm2

/-- `|P̃_σ(u,v) - P̃_σ(0,0)| ≤ 90 W⁻² (1 + log L)` for every `u, v`, `0 ≤ ζ ≤ 1`. -/
private theorem QUEFlow_profile_diff (L W : ℕ) [NeZero L] (hL : 3 ≤ L) {ζ : ℝ} (h0 : 0 ≤ ζ)
    (h1 : ζ ≤ 1) {z : ℂ} (hz : 0 < z.im) (σ : Bool) (u v : Z2 L) :
    ‖profileTilde L W ζ z σ u v - profileTilde L W ζ z σ 0 0‖ ≤
      ((W : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log L)) := by
  have hξ := QUEFlow_norm_xi_lt_one hz σ
  set ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ) with hξdef
  have hp : ∀ a b : Z2 L, profileTilde L W ζ z σ a b =
      ((W : ℂ) ^ 2)⁻¹ * (ξ * ThetaTilde L ζ ξ a b) := fun a b => rfl
  rw [hp, hp, ← mul_sub, ← mul_sub]
  have hΘ := norm_ThetaTilde_sub_le L hL hξ h0 h1 u v
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖ξ‖ * ‖ThetaTilde L ζ ξ u v - ThetaTilde L ζ ξ 0 0‖
      ≤ 1 * (90 * (1 + Real.log L)) := by
        gcongr
    _ = 90 * (1 + Real.log L) := one_mul _

/-- The four-term combination is `1`-Lipschitz for the maximum of the three differences. -/
private theorem QUEFlow_quad_diff {a a' b b' c c' : ℂ} {K : ℝ} (ha : ‖a - a'‖ ≤ K)
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

/-! ### The core: expectation of `Re tr(Im G B_c Im G B_c)` for `𝐇_t` -/

section Core

variable (L W : ℕ) [NeZero L] [NeZero W] (t : ℝ)

/-- `X_c = Re tr(Im G B_c Im G B_c)` at the spectral parameter `z`, for the matrix `M`. -/
private noncomputable def QUEFlow_X (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (c : Z2 L → ℝ) : ℝ :=
  (trace (QUEFlow_imG M z * QUEFlow_B L W c * QUEFlow_imG M z * QUEFlow_B L W c)).re

/-- The complex four-term combination of `trGEGEmat`. -/
private noncomputable def QUEFlow_F (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (u v : Z2 L) : ℂ :=
  -(1 / 4 : ℂ) * (trGEGEmat L W M z true u v + conj (trGEGEmat L W M z true u v) -
    trGEGEmat L W M z false u v - trGEGEmat L W M z false v u)

private theorem QUEFlow_trace_eq_sum (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (c : Z2 L → ℝ) :
    trace (QUEFlow_imG M z * QUEFlow_B L W c * QUEFlow_imG M z * QUEFlow_B L W c) =
      ∑ u, ∑ v, ((((c u - ((L : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) *
        (((c v - ((L : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ)) * QUEFlow_F L W M z u v := by
  unfold QUEFlow_B
  rw [QUEFlow_trace_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  unfold QUEFlow_imG
  rw [QUEFlow_trace_imG _ _ _ (Epaper_conjTranspose _ _ u) (Epaper_conjTranspose _ _ v)]
  rfl

private theorem QUEFlow_F_integrable {z : ℂ} (hz : z.im ≠ 0) (u v : Z2 L) :
    Integrable (fun ω => QUEFlow_F L W (ouMat L W t ω) z u v) (ouP L W) := by
  have hT := QUEFlow_trGEGEmat_integrable L W t hz true u v
  have hF := QUEFlow_trGEGEmat_integrable L W t hz false u v
  have hF' := QUEFlow_trGEGEmat_integrable L W t hz false v u
  have hTc : Integrable (fun ω => conj (trGEGEmat L W (ouMat L W t ω) z true u v))
      (ouP L W) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  exact (((hT.add hTc).sub hF).sub hF').const_mul _

private theorem QUEFlow_integral_F {z : ℂ} (hz : z.im ≠ 0) (u v : Z2 L) :
    ∫ ω, QUEFlow_F L W (ouMat L W t ω) z u v ∂(ouP L W) =
      -(1 / 4 : ℂ) * ((∫ ω, trGEGEmat L W (ouMat L W t ω) z true u v ∂(ouP L W)) +
        conj (∫ ω, trGEGEmat L W (ouMat L W t ω) z true u v ∂(ouP L W)) -
        (∫ ω, trGEGEmat L W (ouMat L W t ω) z false u v ∂(ouP L W)) -
        (∫ ω, trGEGEmat L W (ouMat L W t ω) z false v u ∂(ouP L W))) := by
  have hT := QUEFlow_trGEGEmat_integrable L W t hz true u v
  have hF := QUEFlow_trGEGEmat_integrable L W t hz false u v
  have hF' := QUEFlow_trGEGEmat_integrable L W t hz false v u
  have hTc : Integrable (fun ω => conj (trGEGEmat L W (ouMat L W t ω) z true u v))
      (ouP L W) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  have h0 : Integrable (fun ω => trGEGEmat L W (ouMat L W t ω) z true u v +
      conj (trGEGEmat L W (ouMat L W t ω) z true u v)) (ouP L W) := hT.add hTc
  have h1 : Integrable (fun ω => trGEGEmat L W (ouMat L W t ω) z true u v +
      conj (trGEGEmat L W (ouMat L W t ω) z true u v) -
      trGEGEmat L W (ouMat L W t ω) z false u v) (ouP L W) := h0.sub hF
  unfold QUEFlow_F
  rw [integral_const_mul, integral_sub h1 hF', integral_sub h0 hF,
    integral_add hT hTc, integral_conj]

/-- **Core estimate** (`(que0)` with the Fourier profile bound for `Θ̃`).  If the expectations of
`trGEGEmat` for `𝐇_t` agree with `profileTilde` up to `ε` at `z = E + iη` (this is `OUEq747`),
then `X_c ≥ 0` is integrable and `E X_c ≤ 4 (90 W⁻² (1 + log L) + ε)`. -/
private theorem QUEFlow_core (hL : 3 ≤ L) (E : ℝ) {η : ℝ} (hη : 0 < η) {ε ζ : ℝ} (h0 : 0 ≤ ζ)
    (h1 : ζ ≤ 1)
    (hQ : ∀ (σ : Bool) (a b : Z2 L),
      ‖(∫ ω, trGEGEmat L W (ouMat L W t ω) (E + η * Complex.I) σ a b ∂(ouP L W)) -
        profileTilde L W ζ (E + η * Complex.I) σ a b‖ ≤ ε)
    (c : Z2 L → ℝ) (hc0 : ∀ u, 0 ≤ c u) (hc1 : ∑ u, c u = 1) :
    Integrable (fun ω => QUEFlow_X L W (ouMat L W t ω) (E + η * Complex.I) c) (ouP L W) ∧
      (∀ ω, 0 ≤ QUEFlow_X L W (ouMat L W t ω) (E + η * Complex.I) c) ∧
      ∫ ω, QUEFlow_X L W (ouMat L W t ω) (E + η * Complex.I) c ∂(ouP L W) ≤
        4 * (((W : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log L)) + ε) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : z.im ≠ 0 := by rw [hzim]; exact hη.ne'
  have hz0 : 0 < z.im := by rw [hzim]; exact hη
  set β : Z2 L → ℝ := fun u => c u - ((L : ℝ) ^ 2)⁻¹ with hβ
  set Xc : Ω L W × Ω L W → ℂ := fun ω =>
    trace (QUEFlow_imG (ouMat L W t ω) z * QUEFlow_B L W c *
      QUEFlow_imG (ouMat L W t ω) z * QUEFlow_B L W c) with hXc
  have hXc_eq : Xc = fun ω => ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
      QUEFlow_F L W (ouMat L W t ω) z u v :=
    funext fun ω => QUEFlow_trace_eq_sum L W (ouMat L W t ω) z c
  have hXc_int : Integrable Xc (ouP L W) := by
    rw [hXc_eq]
    refine integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ?_
    exact (QUEFlow_F_integrable L W t hz u v).const_mul _
  have hX : (fun ω => QUEFlow_X L W (ouMat L W t ω) z c) = fun ω => (Xc ω).re := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]; exact hXc_int.re
  · intro ω
    obtain ⟨μ, ψ, hψ⟩ := QUEFlow_exists_basis (ouMat_isHermitian L W t ω)
    exact QUEFlow_re_trace_nonneg hψ E hη _ (QUEFlow_B_herm _ _ c)
  · have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hQ true 0 0)
    set δ : ℝ := ((W : ℝ) ^ 2)⁻¹ * (90 * (1 + Real.log L)) with hδ
    have hδ0 : 0 ≤ δ := by
      have : 0 ≤ Real.log L := Real.log_natCast_nonneg _
      positivity
    have hint : ∫ ω, Xc ω ∂(ouP L W) = ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
        ∫ ω, QUEFlow_F L W (ouMat L W t ω) z u v ∂(ouP L W) := by
      rw [hXc_eq, integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
        (QUEFlow_F_integrable L W t hz u v).const_mul _]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum _ fun v _ => (QUEFlow_F_integrable L W t hz u v).const_mul _]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul]
    set P : Bool → Z2 L → Z2 L → ℂ := fun σ a b => profileTilde L W ζ z σ a b with hP
    set p₀ : ℂ := -(1 / 4 : ℂ) * (P true 0 0 + conj (P true 0 0) - P false 0 0 - P false 0 0)
      with hp₀
    have hK : ∀ u v, ‖(∫ ω, QUEFlow_F L W (ouMat L W t ω) z u v ∂(ouP L W)) - p₀‖ ≤ ε + δ := by
      intro u v
      rw [QUEFlow_integral_F L W t hz u v]
      have h1' := QUEFlow_quad_diff (hQ true u v) (hQ false u v) (hQ false v u)
      have hd := fun σ a b => QUEFlow_profile_diff L W hL h0 h1 hz0 σ a b
      have h2 := QUEFlow_quad_diff (hd true u v) (hd false u v) (hd false v u)
      calc _ ≤ ‖-(1 / 4 : ℂ) * ((∫ ω, trGEGEmat L W (ouMat L W t ω) z true u v ∂(ouP L W)) +
              conj (∫ ω, trGEGEmat L W (ouMat L W t ω) z true u v ∂(ouP L W)) -
              (∫ ω, trGEGEmat L W (ouMat L W t ω) z false u v ∂(ouP L W)) -
              (∫ ω, trGEGEmat L W (ouMat L W t ω) z false v u ∂(ouP L W))) -
            -(1 / 4 : ℂ) * (P true u v + conj (P true u v) - P false u v - P false v u)‖ +
            ‖-(1 / 4 : ℂ) * (P true u v + conj (P true u v) - P false u v - P false v u) - p₀‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + δ := add_le_add h1' h2
    have hnorm := QUEFlow_norm_double_sum_le β
      (QUEFlow_sum_beta L c hc1) _ p₀ hK
    have hsum2 : (∑ u, |β u|) ^ 2 ≤ 4 := by
      have h := QUEFlow_sum_abs_beta L c hc0 hc1
      have h0' : 0 ≤ ∑ u, |β u| := Finset.sum_nonneg fun u _ => abs_nonneg _
      nlinarith
    rw [hX]
    have hre : (∫ ω, (Xc ω).re ∂(ouP L W)) = (∫ ω, Xc ω ∂(ouP L W)).re := integral_re hXc_int
    change (∫ ω, (Xc ω).re ∂(ouP L W)) ≤ _
    rw [hre]
    calc (∫ ω, Xc ω ∂(ouP L W)).re ≤ ‖∫ ω, Xc ω ∂(ouP L W)‖ := Complex.re_le_norm _
      _ ≤ (∑ u, |β u|) ^ 2 * (ε + δ) := by rw [hint]; exact hnorm
      _ ≤ 4 * (ε + δ) := by gcongr
      _ = 4 * (δ + ε) := by ring

end Core

/-! ### The failure event is dominated by `4 N² η² X_{δ_a}` -/

section Events

variable (L W : ℕ) [NeZero L] [NeZero W] (t : ℝ)

/-- `(Meq:QUE)` event for `𝐇_t` inside `{N^{-τ/6} ≤ 4 N² η² X_{δ_a}}` (window half-width `≤ η`). -/
private theorem QUEFlow_queBad_sub {N : ℕ} (hN : N = (W * L) ^ 2) {τ E η : ℝ} (hη : 0 < η)
    (hwin : (N : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3) ≤ η) (a : Z2 L) :
    {ω | queBadMat L W N τ E a (ouMat L W t ω)} ⊆ {ω | (N : ℝ) ^ (-τ / 6) ≤
      4 * (N : ℝ) ^ 2 * η ^ 2 *
        QUEFlow_X L W (ouMat L W t ω) (E + η * Complex.I) (fun u => if u = a then 1 else 0)} := by
  subst hN
  intro ω hω
  obtain ⟨μ, ψ, hψ, k, k', hk, hk', hbad⟩ := hω
  simp only [Set.mem_ofPred_eq]
  refine le_trans hbad ?_
  have hBeq : QUEFlow_B L W (fun u => if u = a then 1 else 0) =
      Epaper L W a - (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ) := by
    rw [QUEFlow_B_eq]
    congr 1
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdom := QUEFlow_normSq_le hψ hη (QUEFlow_B L W
    (fun u => if u = a then 1 else 0)) (QUEFlow_B_herm _ _ _) (hk.trans hwin)
    (hk'.trans hwin)
  rw [hBeq] at hdom
  have hX : QUEFlow_X L W (ouMat L W t ω) (E + η * Complex.I) (fun u => if u = a then 1 else 0) =
      (trace (QUEFlow_imG (ouMat L W t ω) (E + η * Complex.I) *
        (Epaper L W a - (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *
        QUEFlow_imG (ouMat L W t ω) (E + η * Complex.I) *
        (Epaper L W a - (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)))).re := by
    unfold QUEFlow_X; rw [hBeq]
  rw [hX, norm_mul, mul_pow, Complex.norm_natCast, ← Complex.normSq_eq_norm_sq]
  have hN : (0 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by positivity
  calc (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * Complex.normSq _
      ≤ (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (4 * η ^ 2 * _) := mul_le_mul_of_nonneg_left hdom hN
    _ = _ := by ring

end Events

/-! ### Markov -/

private theorem QUEFlow_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
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
private theorem QUEFlow_Meta_ge (L W : ℕ) (z : ℂ) (hη : 0 < z.im) (hW1 : 1 ≤ (W : ℝ))
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
private theorem QUEFlow_w_facts {𝔠 N W : ℝ} (hW1 : 1 ≤ W) (hN1 : 1 ≤ N)
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

/-- The window `N^{-1-τ} W^{2/3}` is at most `η = W^{2/3}/N`. -/
private theorem QUEFlow_window {τ N W : ℝ} (hτ : 0 < τ) (hN1 : 1 ≤ N) (hW0 : 0 ≤ W) :
    N ^ (-1 - τ) * W ^ ((2 : ℝ) / 3) ≤ W ^ ((2 : ℝ) / 3) / N := by
  rw [show W ^ ((2 : ℝ) / 3) / N = N⁻¹ * W ^ ((2 : ℝ) / 3) by ring]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hW0 _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- The exponent chain: `16 N² η² (90 W⁻² (1 + log L) + W^{δ} M⁻³) ≤ N^{-τ/2}` at
`η = W^{2/3}/N`, `δ ≤ 1/12`, once `16 (91 + 1080/𝔠) ≤ W^{1/12}`. -/
private theorem QUEFlow_chain {𝔠 τ τQ N W L M : ℝ} (h𝔠 : 0 < 𝔠) (hτ𝔠 : τ < 𝔠 / 2)
    (hτQ1 : τQ ≤ 1 / 12) (hW1 : 1 ≤ W) (hL3 : 3 ≤ L) (hNeq : N = W ^ 2 * L ^ 2)
    (hNW : N ^ 𝔠 ≤ W) (hKw : 16 * (91 + 1080 / 𝔠) ≤ W ^ (1 / 12 : ℝ))
    (hM : W ^ ((2 : ℝ) / 3) ≤ M) :
    4 * N ^ 2 * (W ^ ((2 : ℝ) / 3) / N) ^ 2 *
        (4 * ((W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + W ^ τQ * M⁻¹ ^ 3)) ≤
      N ^ (-τ / 2) := by
  have hL1 : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
  have hW21 : 1 ≤ W ^ 2 := one_le_pow₀ hW1
  have hN1 : 1 ≤ N := by rw [hNeq]; nlinarith
  have hNpos : 0 < N := by linarith
  obtain ⟨hWw, hW23, hNc, hw1⟩ := QUEFlow_w_facts hW1 hN1 hNW
  set w := W ^ (1 / 12 : ℝ) with hwdef
  have hwpos : 0 < w := by linarith
  -- `ε ≤ w/w²⁴`
  have hε : W ^ τQ * M⁻¹ ^ 3 ≤ w / w ^ 24 := by
    have hMpos : 0 < M := lt_of_lt_of_le (by rw [hW23]; positivity) hM
    have h1 : M⁻¹ ^ 3 ≤ (w ^ 24)⁻¹ := by
      rw [inv_pow]
      apply inv_anti₀ (by positivity)
      calc w ^ 24 = (w ^ 8) ^ 3 := by ring
        _ ≤ M ^ 3 := pow_le_pow_left₀ (by positivity) (hW23 ▸ hM) 3
    have h2 : W ^ τQ ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 hτQ1
    have h3 : 0 ≤ W ^ τQ := Real.rpow_nonneg (by linarith) _
    calc W ^ τQ * M⁻¹ ^ 3 ≤ w * (w ^ 24)⁻¹ := mul_le_mul h2 h1 (by positivity) (by positivity)
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
  have hsum : (W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + W ^ τQ * M⁻¹ ^ 3 ≤
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
  calc 4 * w ^ 16 * (4 * ((W ^ 2)⁻¹ * (90 * (1 + Real.log L)) + W ^ τQ * M⁻¹ ^ 3))
      ≤ 4 * w ^ 16 * (4 * ((91 + 1080 / 𝔠) * w / w ^ 24)) := by gcongr
    _ = K / w ^ 7 := h1
    _ ≤ N ^ (-τ / 2) := h2.trans h3

/-! ### The deduction at a fixed size, time and energy -/

/-- At one size `n`, one time `t` and one energy `E`: (7.47) at `η_Q` (the loss `W^{1/12}`),
with `N^𝔠 ≤ W` and `16 (91 + 1080/𝔠) ≤ W^{1/12}`, gives the `(Meq:QUE)` bound at `τ = 𝔠/3`. -/
private theorem QUEFlow_fixed (d : Sizes) (n : ℕ) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {t : ℝ} (ht : 0 ≤ t)
    (E : ℝ)
    (hn : ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω)
            ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b ∂(ouP (d.L n) (d.W n))) -
          profileTilde (d.L n) (d.W n) (ouZeta t)
            ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b‖ ≤
        (d.W n : ℝ) ^ (1 / 12 : ℝ) * (Meta (d.L n) (d.W n)
          ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3)
    (hNW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (hKw : 16 * (91 + 1080 / 𝔠) ≤ (d.W n : ℝ) ^ (1 / 12 : ℝ)) (a : Z2 (d.L n)) :
    ouP (d.L n) (d.W n)
        {ω | queBadMat (d.L n) (d.W n) (d.size n) (𝔠 / 3) E a (ouMat (d.L n) (d.W n) t ω)} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(𝔠 / 3) / 6)) := by
  have hτ : 0 < 𝔠 / 3 := by linarith
  have hτ𝔠 : 𝔠 / 3 < 𝔠 / 2 := by linarith
  have hW1 : 1 ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hL3 : 3 ≤ (d.L n : ℝ) := by exact_mod_cast d.three_le_L n
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hN1 : 1 ≤ ((d.size n : ℕ) : ℝ) := by
    rw [hNeq]; nlinarith [one_le_pow₀ (n := 2) hW1,
      one_le_pow₀ (n := 2) (by linarith : (1 : ℝ) ≤ (d.L n : ℝ))]
  have hNpos : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hwin := QUEFlow_window (N := ((d.size n : ℕ) : ℝ)) (W := (d.W n : ℝ)) hτ hN1
    (by linarith)
  set η : ℝ := ouEtaQ d n with hηdef
  have hηeq : η = (d.W n : ℝ) ^ ((2 : ℝ) / 3) / ((d.size n : ℕ) : ℝ) := rfl
  have hηpos : 0 < η := by rw [hηeq]; positivity
  have hzim : ((E : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
  have hMeta : (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤
      Meta (d.L n) (d.W n) ((E : ℂ) + (η : ℂ) * Complex.I) := by
    refine QUEFlow_Meta_ge (d.L n) (d.W n) _ (by rw [hzim]; exact hηpos) hW1 ?_
    rw [hzim, hηeq, ← hNeq]; field_simp
  have hchain := QUEFlow_chain h𝔠 hτ𝔠 (le_refl (1 / 12 : ℝ)) hW1 hL3 hNeq hNW hKw hMeta
  have hζ0 : 0 ≤ ouZeta t := ZeroModeProfile_ouZeta_nonneg ht
  have hζ1 : ouZeta t ≤ 1 := ZeroModeProfile_ouZeta_le_one t
  have hc0 : ∀ u, 0 ≤ (fun u => if u = a then (1 : ℝ) else 0) u := fun u => by
    simp only; split_ifs <;> norm_num
  have hc1 : ∑ u, (fun u => if u = a then (1 : ℝ) else 0) u = 1 := by simp
  obtain ⟨hint, hnn, hle⟩ := QUEFlow_core (d.L n) (d.W n) t (d.three_le_L n) E hηpos hζ0 hζ1 hn
    _ hc0 hc1
  have hs : 0 < ((d.size n : ℕ) : ℝ) ^ (-(𝔠 / 3) / 6) := Real.rpow_pos_of_pos hNpos _
  have hsub := QUEFlow_queBad_sub (d.L n) (d.W n) t (N := d.size n) rfl hηpos hwin
    (τ := 𝔠 / 3) (E := E) a
  have hEY : ∫ ω, 4 * ((d.size n : ℕ) : ℝ) ^ 2 * η ^ 2 *
        QUEFlow_X (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (E + η * Complex.I)
          (fun u => if u = a then (1 : ℝ) else 0) ∂(ouP (d.L n) (d.W n)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-(𝔠 / 3) / 2) := by
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hchain
  refine (QUEFlow_markov (ouP (d.L n) (d.W n)) _ (hint.const_mul _)
    (fun ω => by have := hnn ω; positivity) hs hEY _ hsub).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_eq_mul_inv, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-! ### The statement `G2bRow` -/

/-- **`G2bRow`, proved (no hypothesis): the weak QUE `(Meq:QUE)` for `𝐇_t` from (7.47).**  For
`𝔠 > 0`, admissible `d` and `0 < τ_U ≤ ouTauMax 𝔠`, the statement `OUEq747`
((7.47) for `𝐇_t` with `Θ̃`, per sequence `(E_n, t_n)`) gives `OUQUE 𝔠 d τ_U`: uniformly in
`0 ≤ t ≤ t* = N^{-1+τ_U}`, `|E| < 2 - κ` and the block `a`, with `τ = 𝔠/3` and threshold
`N^{-τ/6}`.  The argument of `QUE_of_QDiff` on `ouMat` with `norm_ThetaTilde_sub_le` in place
of `norm_Theta_sub_le_log`; the zero mode of `Θ̃` cancels in the zero-sum double sum. -/
theorem g2bRow : G2bRow := by
  intro 𝔠 h𝔠 d hAdm τU hτU _ hEq κ hκ
  by_cases hκ2 : 2 ≤ κ
  · refine Eventually.of_forall fun n t _ _ E hE => ?_
    exfalso
    have := abs_nonneg E
    linarith
  push Not at hκ2
  have hT : ∀ n, ({a : ℝ × ℝ | 0 ≤ a.1 ∧ a.1 ≤ ouTStar d τU n ∧ |a.2| ≤ 2 - κ}).Nonempty := by
    intro n
    refine ⟨(0, 0), le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    simp only [abs_zero]
    linarith
  have key := ZeroModeProfile_eventually_forall_mem_of_forall_seq'
    (P := fun n (a : ℝ × ℝ) => ∀ (σ : Bool) (u v : Z2 (d.L n)),
      ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) a.1 ω)
            ((a.2 : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ u v ∂(ouP (d.L n) (d.W n))) -
          profileTilde (d.L n) (d.W n) (ouZeta a.1)
            ((a.2 : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ u v‖ ≤
        (d.W n : ℝ) ^ (1 / 12 : ℝ) * (Meta (d.L n) (d.W n)
          ((a.2 : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3) hT
    (fun s hs => hEq κ hκ (fun n => (s n).2) (fun n => (hs n).2.2) (fun n => (s n).1)
      (fun n => ⟨(hs n).1, (hs n).2.1⟩) (1 / 12) (by norm_num))
  have hNt : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hAdm.1
  have hWt : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hAdm.2 ((tendsto_rpow_atTop h𝔠).comp hNt)
  have hwK : ∀ᶠ n in atTop, 16 * (91 + 1080 / 𝔠) ≤ (d.W n : ℝ) ^ (1 / 12 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hWt).eventually_ge_atTop _
  filter_upwards [key, hAdm.2, hwK] with n hn hNW hKw
  intro t ht0 htt E hE a
  exact QUEFlow_fixed d n h𝔠 ht0 E (hn (t, E) ⟨ht0, htt, hE.le⟩) hNW hKw a

end RBM.Univ

/-! ## Compiled instances -/
