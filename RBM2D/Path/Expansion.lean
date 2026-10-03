/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.StepDecompLoop
import RBM2D.Path.DriftAlgebra
import RBM2D.Path.LoopStep
import RBM2D.Path.UBounds
import RBM2D.Path.Kernel

/-!
# The one-step expansion of `A_k = (𝓛 - 𝒦)_{u_k,(+,-)}` along the walk (`d = 2`)

Paper: arXiv:2503.07606, (`int_K-L_ST`) and (`LK_SDE`).

* the definitions `Avec`, `martInc`, `predInc`, `StoppedDuhamel105` and the theorem
  `stoppedDuhamel105`, the stopped Duhamel formula (105) in grid form;
* the drift split `Dgrid`, `Rgrid`, `condExp_A_succ`;
* the expansion with the split `grid_expansion`, `grid_expansion_all`;
* the martingale part in the decomposition form of `StepDecomp.lean`: `gridDelta`,
  `stepZ_eq_sum_gridDelta`, `stepZ_ukerMat_eq_Uker`, `stepXi_eq_sum_gridDelta_ae`,
  `stepY_eq_sum_gridDelta_ae`, `stepY_ukerMat_eq_Uker_ae`, `Zvec`, `Yvec`, `Zvec_succ`,
  `Yvec_succ`, `grid_expansion'`, `grid_expansion_all'`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable (d : Sizes)

/-! ### 1. The definitions -/

/-- `A_k = (𝓛 - 𝒦)_{u_k,(+,-)}` along the walk, as a two-index tensor. -/
def Avec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    Z2 (d.L n) × Z2 (d.L n) → ℂ :=
  fun a => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n k ω))
      (spectralZ E (gridTime s t K n k)) (pmLoop a.1 a.2) -
    Kpm (d.L n) (d.W n) E (gridTime s t K n k) a.1 a.2

/-- The martingale difference `ξ_{j+1} = A_{j+1} - E[A_{j+1} | F_j]` (label-wise). -/
def martInc (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d) :
    Z2 (d.L n) × Z2 (d.L n) → ℂ :=
  fun a => Avec d E s t K n (j + 1) ω a -
    (pathP d)[fun ω' => Avec d E s t K n (j + 1) ω' a | filt d j] ω

/-- The predictable part `E[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1}} A_j`. -/
def predInc (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d) :
    Z2 (d.L n) × Z2 (d.L n) → ℂ :=
  fun a => (pathP d)[fun ω' => Avec d E s t K n (j + 1) ω' a | filt d j] ω -
    Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n j)
      (gridTime s t K n (j + 1)) (Avec d E s t K n j ω) a

/-- **The stopped Duhamel formula (105), grid form** (`int_K-L_ST`): for every stopping index `τ`
and target `k`, `A_{k∧τ} = 𝒰_{u_0,u_{k∧τ}} A_0 + Σ_{j<k∧τ} 𝒰_{u_{j+1},u_{k∧τ}} (P_j + ξ_{j+1})`,
with the predictable part `P_j` (the grid drift, to be expanded by `OneStepEnvelope`) and the
martingale difference `ξ_{j+1}`. -/
def StoppedDuhamel105 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  |E| < 2 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n : ℕ) (τ : PathΩ d → ℕ) (k : ℕ) (ω : PathΩ d), min k (τ ω) ≤ K n →
      Avec d E s t K n (min k (τ ω)) ω =
        Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec d E s t K n 0 ω) +
          ∑ j ∈ Finset.range (min k (τ ω)),
            Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n (min k (τ ω)))
              (predInc d E s t K n j ω + martInc d E s t K n j ω)


/-! ### 2. Grid-time arithmetic -/

section GridArith

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

private theorem Expansion_gridStep_nonneg (hst : s n ≤ t n) : 0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem Expansion_gridTime_succ (k : ℕ) :
    gridTime s t K n (k + 1) = gridTime s t K n k + gridStep s t K n := by
  unfold gridTime; push_cast; ring

private theorem Expansion_gridTime_zero : gridTime s t K n 0 = s n := by
  simp [gridTime]

private theorem Expansion_gridTime_mono (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

private theorem Expansion_gridTime_nonneg (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) :
    0 ≤ gridTime s t K n j := by
  have h := Expansion_gridTime_mono s t K n hst (Nat.zero_le j)
  rw [Expansion_gridTime_zero] at h
  linarith

private theorem Expansion_gridTime_lt_one (hst : s n ≤ t n) (hK : K n ≠ 0) (ht1 : t n < 1)
    {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have h := Expansion_gridTime_mono s t K n hst hj
  rw [gridTime_last s t K n hK] at h
  linarith

end GridArith

/-! ### 3. The stopped Duhamel formula (105) in grid form -/

/-- `StoppedDuhamel105` holds, from `Uop_duhamel_telescope_stopped` at `ξ = |m|² = 1`:
`A_{j+1} - 𝒰 A_j = predInc_j + martInc_j` label by label (the conditional expectation cancels). -/
theorem stoppedDuhamel105 (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedDuhamel105 d E s t K := by
  intro hE hs0 hst ht1 hK n τ k ω hkτ
  have hξ : ‖((Complex.normSq (spectralM E) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [normSqSpectralMOne E hE.le]; simp
  have hu0 : ∀ j ≤ min k (τ ω), 0 ≤ gridTime s t K n j :=
    fun j _ => Expansion_gridTime_nonneg s t K n (hs0 n) (hst n) j
  have hu1 : ∀ j ≤ min k (τ ω), gridTime s t K n j < 1 :=
    fun j hj => Expansion_gridTime_lt_one s t K n (hst n) (hK n) (ht1 n) (hj.trans hkτ)
  have h := Uop_duhamel_telescope_stopped (d.L n) (d.three_le_L n) hξ (Ω' := PathΩ d)
    (gridTime s t K n) τ ω k hu0 hu1 (fun j => Avec d E s t K n j ω)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext a
  simp only [predInc, martInc, Pi.add_apply, Pi.sub_apply]
  ring

/-! ### 4. Integrability of a Hermitian-test observable along the walk

The analogues in `StepDecomp.lean` (`StepDecomp_integrable_phi`) are `private`; they are
proved here: the observable of the Hermitian part is continuous and agrees with `Ψ` at the
Hermitian walk. -/

section Integrable

open scoped Matrix.Norms.L2Operator

private def Expansion_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem Expansion_herm_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : (Expansion_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem Expansion_herm_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : Expansion_herm A = A := by
  unfold Expansion_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem Expansion_continuous_herm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (Expansion_herm : Matrix ι ι ℂ → _) := by
  unfold Expansion_herm
  have h1 : Continuous fun A : Matrix ι ι ℂ => Aᴴ := continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- `Ψ ∘ herm` is continuous when `Ψ` is `C²` at every Hermitian point. -/
private theorem Expansion_continuous_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Ψ M) :
    Continuous (fun M : Matrix ι ι ℂ => Ψ (Expansion_herm M)) :=
  continuous_iff_continuousAt.2 fun M =>
    ((h _ (Expansion_herm_isHermitian M)).continuousAt).comp
      Expansion_continuous_herm.continuousAt

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `Ψ` along the walk is measurable. -/
private theorem Expansion_measurable_phi
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ)
    (k : ℕ) : Measurable fun ω : PathΩ d => Ψ (pathH d s t K n k ω) := by
  have heq : (fun ω : PathΩ d => Ψ (pathH d s t K n k ω))
      = fun ω => Ψ (Expansion_herm (pathH d s t K n k ω)) := funext fun ω => by
    rw [Expansion_herm_of_isHermitian (pathH_isHermitian d s t K n k ω)]
  rw [heq]
  exact (Expansion_continuous_comp hΨ.contDiffAt).measurable.comp
    ((pathH_measurable_filt d s t K n k).mono ((filt d).le k) le_rfl)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2). -/
private theorem Expansion_integrable_phi
    {Ψ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ} (hΨ : HermTestFun d n Ψ)
    (k : ℕ) : Integrable (fun ω : PathΩ d => Ψ (pathH d s t K n k ω)) (pathP d) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  exact (memLp_top_of_bound (Expansion_measurable_phi d s t K n hΨ k).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian d s t K n k ω))).integrable
    le_top

end Integrable

/-! ### 5. The second-order step of `𝒦` -/

section KpmStep

open scoped Matrix.Norms.Operator

private theorem Expansion_Kpm_eq {L W : ℕ} [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2) (v : ℝ)
    (a b : Z2 L) : Kpm L W E v a b = ((W : ℂ)⁻¹) ^ 2 * Theta L (v : ℂ) a b := by
  rw [Kpm, normSqSpectralMOne E hE.le]
  simp

private theorem Expansion_norm_mul5 {R : Type*} [NormedRing R] (a b c d e : R) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  have h1 := norm_mul_le (a * b * c * d) e
  have h2 := norm_mul_le (a * b * c) d
  have h3 := norm_mul_le (a * b) c
  have h4 := norm_mul_le a b
  calc ‖a * b * c * d * e‖ ≤ ‖a * b * c * d‖ * ‖e‖ := h1
    _ ≤ (‖a * b * c‖ * ‖d‖) * ‖e‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ ((‖a * b‖ * ‖c‖) * ‖d‖) * ‖e‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
          (norm_nonneg _)
    _ ≤ (((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖) * ‖e‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)

private theorem Expansion_norm_ofReal_lt_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) :
    ‖(v : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

private theorem Expansion_norm_Theta_real {L : ℕ} [NeZero L] (hL : 3 ≤ L) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v < 1) : ‖Theta L (v : ℂ)‖ ≤ (1 - v)⁻¹ := by
  have h := norm_Theta_le L hL (Expansion_norm_ofReal_lt_one h0 h1)
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h

/-- `‖𝒦_{u+Δ} - 𝒦_u - Δ ∂_u 𝒦_u‖ ≤ W⁻² (1-u')⁻¹ (1-u)⁻² Δ²` entrywise (`u' = u + Δ`): twice the
resolvent identity `Θ_{u'} - Θ_u = Δ Θ_{u'} S Θ_u`, then `‖Θ‖ ≤ (1-u)⁻¹`, `‖S‖ = 1`. -/
private theorem Expansion_Kpm_step {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| < 2) {u u' Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu' : u' = u + Δ) (hu1 : u' < 1)
    (a b : Z2 L) :
    ‖Kpm L W E u' a b - Kpm L W E u a b
        - (Δ : ℂ) * deriv (fun v : ℝ => Kpm L W E v a b) u‖
      ≤ ((W : ℝ)⁻¹) ^ 2 * (1 - u')⁻¹ * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by
  have hu0' : 0 ≤ u' := by rw [hu']; linarith
  have hu1' : u < 1 := by linarith
  have hnu : ‖(u : ℂ)‖ < 1 := Expansion_norm_ofReal_lt_one hu0 hu1'
  have hnu' : ‖(u' : ℂ)‖ < 1 := Expansion_norm_ofReal_lt_one hu0' hu1
  have hfun : (fun v : ℝ => Kpm L W E v a b)
      = fun v : ℝ => ((W : ℂ)⁻¹) ^ 2 * Theta L (v : ℂ) a b :=
    funext fun v => Expansion_Kpm_eq hE v a b
  have hderiv : deriv (fun v : ℝ => Kpm L W E v a b) u
      = ((W : ℂ)⁻¹) ^ 2 * (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) a b := by
    rw [hfun]
    exact (((hasDerivAt_Theta_apply L hL hnu a b).comp_ofReal).const_mul
      (((W : ℂ)⁻¹) ^ 2)).deriv
  set T := Theta L (u : ℂ) with hT
  set T' := Theta L (u' : ℂ) with hT'
  set c : ℂ := (Δ : ℂ) with hc
  have hcu : (u' : ℂ) - (u : ℂ) = c := by rw [hu']; push_cast; ring
  have h1 : T' - T = c • (T' * SB L * T) := by
    have h := Theta_sub_Theta L hL hnu hnu'
    rw [hcu] at h
    exact h
  have h3 : T' - T - c • (T * SB L * T) = c • (c • (T' * SB L * T * SB L * T)) := by
    have e1 : T' * SB L * T - T * SB L * T = c • (T' * SB L * T * SB L * T) := by
      rw [← sub_mul, ← sub_mul, h1, smul_mul_assoc, smul_mul_assoc]
    rw [h1, ← smul_sub, e1]
  have hentry : Kpm L W E u' a b - Kpm L W E u a b - c * deriv (fun v : ℝ => Kpm L W E v a b) u
      = ((W : ℂ)⁻¹) ^ 2 * (c * (c * (T' * SB L * T * SB L * T) a b)) := by
    have h := congrFun (congrFun h3 a) b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [hderiv, Expansion_Kpm_eq hE, Expansion_Kpm_eq hE]
    linear_combination ((W : ℂ)⁻¹) ^ 2 * h
  have hM : ‖T' * SB L * T * SB L * T‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ := by
    have e1 : ‖T'‖ ≤ (1 - u')⁻¹ := Expansion_norm_Theta_real hL hu0' hu1
    have e2 : ‖T‖ ≤ (1 - u)⁻¹ := Expansion_norm_Theta_real hL hu0 hu1'
    have e3 : ‖SB L‖ = 1 := norm_SB L hL
    have p1 : 0 < (1 - u')⁻¹ := inv_pos.2 (by linarith)
    have p2 : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
    have e4 := Expansion_norm_mul5 T' (SB L) T (SB L) T
    rw [e3] at e4
    calc ‖T' * SB L * T * SB L * T‖ ≤ ‖T'‖ * 1 * ‖T‖ * 1 * ‖T‖ := e4
      _ = ‖T'‖ * (‖T‖ * ‖T‖) := by ring
      _ ≤ (1 - u')⁻¹ * ((1 - u)⁻¹ * (1 - u)⁻¹) :=
          mul_le_mul e1 (mul_le_mul e2 e2 (norm_nonneg _) p2.le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) p1.le
      _ = (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ := by ring
  rw [hentry, norm_mul, norm_mul, norm_mul, norm_pow, norm_inv]
  have hW : ‖(W : ℂ)‖ = (W : ℝ) := by simp
  have hcn : ‖c‖ = Δ := by rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
  rw [hW, hcn]
  have hW2 : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
  have hent : ‖(T' * SB L * T * SB L * T) a b‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ :=
    (norm_entry_le_norm L _ a b).trans hM
  calc ((W : ℝ)⁻¹) ^ 2 * (Δ * (Δ * ‖(T' * SB L * T * SB L * T) a b‖))
      ≤ ((W : ℝ)⁻¹) ^ 2 * (Δ * (Δ * ((1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹))) := by gcongr
    _ = ((W : ℝ)⁻¹) ^ 2 * (1 - u')⁻¹ * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by ring

end KpmStep

/-! ### 6. The drift split: `Dgrid`, `Rgrid` -/

/-- **`D_j`**: the drift `𝓔^{(LK×LK)} + 𝓔^{(G̃)}` at the grid time `u_j` and the walk `H_j`, as a
function of the label `a = (a₁, a₂)` (`n = 2` has no `l_𝒦 > 2` term).  The factor `Δ` is not
inside `Dgrid`. -/
def Dgrid (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d) :
    Z2 (d.L n) × Z2 (d.L n) → ℂ :=
  fun a => ELKLK (d.L n) (d.W n) E (gridTime s t K n j) (pathH d s t K n j ω) a.1 a.2
    + EGt (d.L n) (d.W n) E (gridTime s t K n j) (pathH d s t K n j ω) a.1 a.2

/-- **`R_j`**: the discretization remainder of the predictable part, named by subtraction:
`predInc_j = Δ · D_j + R_j`. -/
def Rgrid (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℂ :=
  predInc d E s t K n j ω a - (gridStep s t K n : ℂ) * Dgrid d E s t K n j ω a

/-- `predInc_j = Δ · D_j + R_j` (every `ω`, every label; definitional). -/
theorem Expansion_predInc_eq_Dgrid_add_Rgrid (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (ω : PathΩ d) (a : Z2 (d.L n) × Z2 (d.L n)) :
    predInc d E s t K n j ω a
      = (gridStep s t K n : ℂ) * Dgrid d E s t K n j ω a + Rgrid d E s t K n j ω a := by
  unfold Rgrid; ring

/-- The crude bound of `A_j` at the grid time `u_j` (`u_j < 1`): `‖𝓛‖ ≤ N (η_u⁻¹ W⁻²)²` by
`norm_gloop_le_crude` and `‖𝒦‖ ≤ W⁻² (1-u)⁻¹` by `‖Θ‖ ≤ (1-u)⁻¹`. -/
private theorem Expansion_norm_Avec_le (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E| < 2) (ω : PathΩ d) (hu0 : 0 ≤ gridTime s t K n j) (hu1 : gridTime s t K n j < 1)
    (b : Z2 (d.L n) × Z2 (d.L n)) :
    ‖Avec d E s t K n j ω b‖
      ≤ (((d.L n * d.W n) ^ 2 : ℕ) : ℝ)
            * ((etaT E (gridTime s t K n j))⁻¹ * ((d.W n : ℝ)⁻¹ ^ 2)) ^ 2
          + ((d.W n : ℝ)⁻¹) ^ 2 * (1 - gridTime s t K n j)⁻¹ := by
  have hη : 0 < etaT E (gridTime s t K n j) := etaT_pos hE hu1
  have hpos : 0 < (1 - gridTime s t K n j) * (spectralM E).im :=
    mul_pos (by linarith) (spectralM_im_pos hE)
  have hz : etaT E (gridTime s t K n j) ≤ |(spectralZ E (gridTime s t K n j)).im| := by
    rw [spectralZ_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hH : (blockMat (pathH d s t K n j ω)).IsHermitian :=
    (pathH_isHermitian d s t K n j ω).submatrix _
  have h1 := norm_gloop_le_crude (d.L n) (d.W n) hH hη hz (pmLoop b.1 b.2) rfl
  have h2 : ‖Kpm (d.L n) (d.W n) E (gridTime s t K n j) b.1 b.2‖
      ≤ ((d.W n : ℝ)⁻¹) ^ 2 * (1 - gridTime s t K n j)⁻¹ := by
    rw [Expansion_Kpm_eq hE, norm_mul, norm_pow, norm_inv]
    have hW : ‖((d.W n : ℕ) : ℂ)‖ = ((d.W n : ℕ) : ℝ) := by simp
    rw [hW]
    have h3 := norm_Theta_apply_le (d.L n) (d.three_le_L n)
      (Expansion_norm_ofReal_lt_one hu0 hu1) b.1 b.2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at h3
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  calc ‖Avec d E s t K n j ω b‖
      ≤ ‖gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
          (spectralZ E (gridTime s t K n j)) (pmLoop b.1 b.2)‖
        + ‖Kpm (d.L n) (d.W n) E (gridTime s t K n j) b.1 b.2‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- The real inequality behind `Rbd ≤ Rbd'`: with `w = W⁻²`, `a = (1-u')⁻¹`, `b = (1-u)⁻¹`,
`c = η_u⁻¹` all `≤ x = η_{u'}⁻¹`, `1 ≤ x`, `1 ≤ N`. -/
private theorem Expansion_arith {w N a b c x Δ : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hax : a ≤ x) (hbx : b ≤ x) (hcx : c ≤ x) (hx1 : 1 ≤ x)
    (hN : 1 ≤ N) :
    w * a * b ^ 2 * Δ ^ 2 + 3 * Δ ^ 2 * a ^ 2 * (N * (c * w) ^ 2 + w * b)
      ≤ 7 * N * x ^ 4 * Δ ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h1 : w * a * b ^ 2 ≤ x ^ 3 := by
    calc w * a * b ^ 2 ≤ 1 * a * b ^ 2 := by gcongr
      _ ≤ x * x ^ 2 := by rw [one_mul]; gcongr
      _ = x ^ 3 := by ring
  have h2 : (c * w) ^ 2 ≤ x ^ 2 := by
    have : c * w ≤ x := by nlinarith
    exact pow_le_pow_left₀ (mul_nonneg hc0 hw0) this 2
  have h3 : w * b ≤ x := by nlinarith
  have h4 : N * (c * w) ^ 2 + w * b ≤ N * x ^ 2 + x := by
    have : N * (c * w) ^ 2 ≤ N * x ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h5 : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha0 hax 2
  have h6 : a ^ 2 * (N * (c * w) ^ 2 + w * b) ≤ x ^ 2 * (N * x ^ 2 + x) := by
    have hnn : 0 ≤ N * (c * w) ^ 2 + w * b := by
      have : 0 ≤ N := by linarith
      positivity
    exact mul_le_mul h5 h4 hnn (sq_nonneg x)
  have hx3 : x ^ 3 ≤ N * x ^ 4 := by
    have : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    have h44 : x ^ 4 ≤ N * x ^ 4 := by nlinarith [pow_pos (show 0 < x by linarith) 4]
    linarith
  have hfin : w * a * b ^ 2 + 3 * (a ^ 2 * (N * (c * w) ^ 2 + w * b)) ≤ 7 * N * x ^ 4 := by
    have : x ^ 2 * (N * x ^ 2 + x) = N * x ^ 4 + x ^ 3 := by ring
    nlinarith
  calc w * a * b ^ 2 * Δ ^ 2 + 3 * Δ ^ 2 * a ^ 2 * (N * (c * w) ^ 2 + w * b)
      = (w * a * b ^ 2 + 3 * (a ^ 2 * (N * (c * w) ^ 2 + w * b))) * Δ ^ 2 := by ring
    _ ≤ 7 * N * x ^ 4 * Δ ^ 2 := mul_le_mul_of_nonneg_right hfin hΔ2

/-- **The drift split.**  For `j < K n`: `predInc_j = Δ · (ELKLK + EGt)_{u_j}(H_j) + R_j` for
every `ω`, and a.e. `‖R_j‖ ≤ envConst · Δ^{3/2} + 7 N η_{u_{j+1}}⁻⁴ Δ²`, `N = (W L)²`.
Proof: `R_j = r₁ - r₂ - r₃` with `r₁` the drift error of `condExp_loop_drift`, `r₂` the
second-order step of `𝒦` (`Expansion_Kpm_step`), `r₃` the second-order step of `𝒰`
(`uopOneStep`), and the cancellation `genMat - ∂_u 𝒦 - Θ(𝓛 - 𝒦) = ELKLK + EGt` of
`hierarchyN2`. -/
theorem condExp_A_succ (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j < K n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    (∀ (ω : PathΩ d) (a : Z2 (d.L n) × Z2 (d.L n)),
        predInc d E s t K n j ω a
          = (gridStep s t K n : ℂ) * Dgrid d E s t K n j ω a + Rgrid d E s t K n j ω a) ∧
      ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
        ‖Rgrid d E s t K n j ω a‖
          ≤ envConst (d.L n) (d.W n) E 2 (gridTime s t K n (j + 1))
                * gridStep s t K n ^ ((3 : ℝ) / 2)
            + 7 * (Sizes.size d n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4
                * gridStep s t K n ^ 2 := by
  refine ⟨Expansion_predInc_eq_Dgrid_add_Rgrid d E s t K n j, ?_⟩
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  have hu' := Expansion_gridTime_succ s t K n j
  have hu0 : 0 ≤ gridTime s t K n j := Expansion_gridTime_nonneg s t K n hs0 hst j
  have hu0' : 0 ≤ gridTime s t K n (j + 1) := by rw [hu']; linarith
  have hu1j : gridTime s t K n j < 1 := by rw [hu'] at hu1; linarith
  have hξ : ‖((Complex.normSq (spectralM E) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [normSqSpectralMOne E hE.le]; simp
  have hdrift : ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(pathP d)[fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
              (spectralZ E (gridTime s t K n (j + 1))) (pmLoop a.1 a.2) | filt d j] ω
          - gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
              (spectralZ E (gridTime s t K n j)) (pmLoop a.1 a.2)
          - (gridStep s t K n : ℂ) * genMat E (gridTime s t K n j) (pathH d s t K n j ω)
              (pmLoop a.1 a.2)‖
        ≤ envConst (d.L n) (d.W n) E (pmLoop a.1 a.2).length (gridTime s t K n (j + 1))
            * gridStep s t K n ^ ((3 : ℝ) / 2) :=
    ae_all_iff.2 fun a =>
      condExp_loop_drift d s t K n j E hE (I := pmLoop a.1 a.2) rfl hs0 hst hK hj hu1
  have hce : ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
      (pathP d)[fun ω' => Avec d E s t K n (j + 1) ω' a | filt d j] ω
        = (pathP d)[fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
              (spectralZ E (gridTime s t K n (j + 1))) (pmLoop a.1 a.2) | filt d j] ω
          - Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2 := by
    refine ae_all_iff.2 fun a => ?_
    have hint := Expansion_integrable_phi d s t K n
      (hermTestFun_loopPM d n E _ hu0' hu1 hE a).1 (j + 1)
    have h := condExp_sub hint
      (integrable_const (Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2)) (filt d j)
    have hfg : (fun ω' => Avec d E s t K n (j + 1) ω' a)
        = (fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
              (spectralZ E (gridTime s t K n (j + 1))) (pmLoop a.1 a.2))
          - fun _ => Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2 := rfl
    rw [hfg]
    filter_upwards [h] with ω hω
    rw [hω, Pi.sub_apply, condExp_const ((filt d).le j)]
  filter_upwards [hdrift, hce] with ω h1 h2 a
  have hier := hierarchyN2 (d.L n) (d.W n) E (d.three_le_L n) hE (gridTime s t K n j) hu0 hu1j
    (pathH d s t K n j ω) (pathH_isHermitian d s t K n j ω) a.1 a.2
  have hθ : thetaGen (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s t K n j)
        (fun b : Z2 (d.L n) × Z2 (d.L n) =>
          lkMat (d.L n) (d.W n) E (gridTime s t K n j) (pathH d s t K n j ω) b.1 b.2) (a.1, a.2)
      = thetaGen (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s t K n j)
        (Avec d E s t K n j ω) a := rfl
  have hA : Avec d E s t K n j ω a
      = gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
          (spectralZ E (gridTime s t K n j)) (pmLoop a.1 a.2)
        - Kpm (d.L n) (d.W n) E (gridTime s t K n j) a.1 a.2 := rfl
  have h3 := uopOneStep (d.L n) (d.three_le_L n) _ hξ (gridTime s t K n j) (gridStep s t K n)
    hu0 hΔ (by rw [← hu']; exact hu1) (Avec d E s t K n j ω) _
    (fun b => Expansion_norm_Avec_le d E s t K n j hE ω hu0 hu1j b) a
  rw [← hu'] at h3
  have h4 := Expansion_Kpm_step (L := d.L n) (W := d.W n) (d.three_le_L n) hE hu0 hΔ hu' hu1
    a.1 a.2
  have h5 := h1 a
  have hlen : (pmLoop a.1 a.2).length = 2 := rfl
  rw [hlen] at h5
  have hid : Rgrid d E s t K n j ω a
      = ((pathP d)[fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
              (spectralZ E (gridTime s t K n (j + 1))) (pmLoop a.1 a.2) | filt d j] ω
          - gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
              (spectralZ E (gridTime s t K n j)) (pmLoop a.1 a.2)
          - (gridStep s t K n : ℂ) * genMat E (gridTime s t K n j) (pathH d s t K n j ω)
              (pmLoop a.1 a.2))
        - (Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2
            - Kpm (d.L n) (d.W n) E (gridTime s t K n j) a.1 a.2
            - (gridStep s t K n : ℂ) * deriv (fun v : ℝ => Kpm (d.L n) (d.W n) E v a.1 a.2)
                (gridTime s t K n j))
        - (Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s t K n j)
              (gridTime s t K n (j + 1)) (Avec d E s t K n j ω) a
            - Avec d E s t K n j ω a
            - (gridStep s t K n : ℂ) * thetaGen (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ)
                (gridTime s t K n j) (Avec d E s t K n j ω) a) := by
    unfold Rgrid Dgrid predInc
    rw [h2 a]
    rw [hθ] at hier
    linear_combination (gridStep s t K n : ℂ) * hier - hA
  rw [hid]
  have hη := etaT_pos hE hu1
  have hι : 0 < (spectralM E).im := spectralM_im_pos hE
  have hι1 : (spectralM E).im ≤ 1 := by
    have h := Complex.abs_im_le_norm (spectralM E)
    rw [norm_spectralM hE.le] at h
    exact (le_abs_self _).trans h
  have hη1 : etaT E (gridTime s t K n (j + 1)) ≤ 1 - gridTime s t K n (j + 1) := by
    unfold etaT
    nlinarith
  have hηu : etaT E (gridTime s t K n (j + 1)) ≤ etaT E (gridTime s t K n j) := by
    unfold etaT
    rw [hu']
    nlinarith
  have hηu0 : 0 < etaT E (gridTime s t K n j) := etaT_pos hE hu1j
  have hu'1 : 0 < 1 - gridTime s t K n (j + 1) := by linarith
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := Nat.one_le_cast.2 (d.W_pos n)
  have hW0 : 0 ≤ ((d.W n : ℝ)⁻¹) ^ 2 := by positivity
  have hWle : ((d.W n : ℝ)⁻¹) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have hN1 : (1 : ℝ) ≤ (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ (d.L n * d.W n) ^ 2 :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos n))
    exact_mod_cast this
  have key := Expansion_arith (w := ((d.W n : ℝ)⁻¹) ^ 2)
    (N := (((d.L n * d.W n) ^ 2 : ℕ) : ℝ)) (a := (1 - gridTime s t K n (j + 1))⁻¹)
    (b := (1 - gridTime s t K n j)⁻¹) (c := (etaT E (gridTime s t K n j))⁻¹)
    (x := (etaT E (gridTime s t K n (j + 1)))⁻¹) (Δ := gridStep s t K n) hW0 hWle
    (inv_nonneg.2 hu'1.le) (inv_nonneg.2 (by linarith)) (inv_nonneg.2 hηu0.le)
    (inv_anti₀ hη hη1) (inv_anti₀ hη (hη1.trans (by linarith))) (inv_anti₀ hη hηu)
    ((one_le_inv₀ hη).2 (hη1.trans (by linarith))) hN1
  have hNsize : (Sizes.size d n : ℝ) = (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) := by
    rw [Sizes.size, mul_comm]
  have gen : ∀ (r1 r2 r3 : ℂ) (b1 b2 b3 : ℝ), ‖r1‖ ≤ b1 → ‖r2‖ ≤ b2 → ‖r3‖ ≤ b3 →
      ‖r1 - r2 - r3‖ ≤ b1 + b2 + b3 := fun r1 r2 r3 b1 b2 b3 e1 e2 e3 =>
    (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add e1 e2)) e3)
  refine (gen _ _ _ _ _ _ h5 h4 h3).trans ?_
  rw [hNsize]
  linarith [key]

/-- The same bound in the `O(Δ^{3/2})` form: `‖R_j‖ ≤ (envConst + 7 N η_{u_{j+1}}⁻⁴) Δ^{3/2}`
(`Δ ≤ u_{j+1} < 1`, so `Δ² ≤ Δ^{3/2}`). -/
theorem Expansion_condExp_A_succ_rpow (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j < K n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖Rgrid d E s t K n j ω a‖
        ≤ (envConst (d.L n) (d.W n) E 2 (gridTime s t K n (j + 1))
            + 7 * (Sizes.size d n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4)
          * gridStep s t K n ^ ((3 : ℝ) / 2) := by
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  have hu' := Expansion_gridTime_succ s t K n j
  have hu0 : 0 ≤ gridTime s t K n j := Expansion_gridTime_nonneg s t K n hs0 hst j
  have hΔ1 : gridStep s t K n ≤ 1 := by linarith
  have hsq : gridStep s t K n ^ 2 ≤ gridStep s t K n ^ ((3 : ℝ) / 2) := by
    rcases hΔ.eq_or_lt with h0 | hpos
    · rw [← h0]; norm_num
    · have h := Real.rpow_le_rpow_of_exponent_ge hpos hΔ1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
      rwa [Real.rpow_two] at h
  filter_upwards [(condExp_A_succ d E s t K n j hE hs0 hst hK hj hu1).2] with ω h a
  refine (h a).trans ?_
  have hpos : 0 ≤ 7 * (Sizes.size d n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4 := by
    have : 0 ≤ (etaT E (gridTime s t K n (j + 1)))⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hpos]

/-! ### 7. The expansion with the split -/

/-- **The stopped expansion with the drift split** (105): `StoppedDuhamel105` with
`predInc_j` replaced by `Δ • D_j + R_j` (exact, every `ω`, every stopping index `τ`, every `k`);
the bound on `R_j` is `condExp_A_succ`. -/
theorem grid_expansion_all (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n : ℕ) (τ : PathΩ d → ℕ) (k : ℕ) (ω : PathΩ d) (hkτ : min k (τ ω) ≤ K n) :
    Avec d E s t K n (min k (τ ω)) ω
      = Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec d E s t K n 0 ω)
        + ∑ j ∈ Finset.range (min k (τ ω)),
            Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n (min k (τ ω)))
              ((gridStep s t K n : ℂ) • Dgrid d E s t K n j ω + Rgrid d E s t K n j ω
                + martInc d E s t K n j ω) := by
  rw [stoppedDuhamel105 d E s t K hE hs0 hst ht1 hK n τ k ω hkτ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Expansion_predInc_eq_Dgrid_add_Rgrid]

/-- **The expansion with the split at a fixed `k ≤ K n`** (the stopping index is the constant
`k`). -/
theorem grid_expansion (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n k : ℕ) (hk : k ≤ K n) (ω : PathΩ d) :
    Avec d E s t K n k ω
      = Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n k) (Avec d E s t K n 0 ω)
        + ∑ j ∈ Finset.range k,
            Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n k)
              ((gridStep s t K n : ℂ) • Dgrid d E s t K n j ω + Rgrid d E s t K n j ω
                + martInc d E s t K n j ω) := by
  have h := grid_expansion_all d E s t K hE hs0 hst ht1 hK n (fun _ => k) k ω
    (by rw [min_self]; exact hk)
  simpa only [min_self] using h

/-! ### 8. The martingale part in decomposition form

The kernel is the complex `ukerMat`, `Uop` at `ξ = |m|²`; the weight of the `Z`/`Y` bridges is
`Wt_{v,w}(b, a) = (𝒰_{v,w}(b₁,a₁) 𝒰_{v,w}(b₂,a₂)).re`, the one of `stepDecomp_loopPM`, and the
identification of the complex product with the real weight is `ukerNonneg` (`im = 0`).  The
loop family is that of `hermTestFun_loopPM`, and `𝒦` cancels in `martInc` (no reality of `𝒦` is
used). -/

section Bridge

/-- **`gridDelta`**: the identity kernel on labels, `δ b a := if b = a then 1 else 0`. -/
def gridDelta (L : ℕ) (b a : Z2 L × Z2 L) : ℝ := if b = a then 1 else 0

/-- The two-loop observable family at time `u`: `Φ^{(u)}_a(M) = 𝓛_{u,(+,-),(a₁,a₂)}(M)`, the
family of `hermTestFun_loopPM`, `stepDecomp_loopPM`. -/
def Expansion_loopObs (d : Sizes) (n : ℕ) (E u : ℝ) :
    Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ :=
  fun a M => gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (pmLoop a.1 a.2)

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)

/-- `linTr` of `Ab` is the `U`-weighted sum of the per-label `linTr`s (real-linearity in `U`). -/
private theorem Expansion_linTr_Ab
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) (X : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :
    linTr n (Ab d s t K n j Φ U b ω) X
      = ∑ a : Z2 (d.L n) × Z2 (d.L n), U b a * linTr n (gradMat (Φ a) (pathH d s t K n j ω)) X := by
  unfold linTr Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : Z2 (d.L n) × Z2 (d.L n),
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (pathH d s t K n j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (pathH d s t K n j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- `stepZ` at the identity kernel is the single-label linear term. -/
private theorem Expansion_stepZ_gridDelta
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (a : Z2 (d.L n) × Z2 (d.L n)) (ω : PathΩ d) :
    stepZ d s t K n j Φ (gridDelta (d.L n)) a ω
      = Real.sqrt (gridStep s t K n)
          * linTr n (gradMat (Φ a) (pathH d s t K n j ω)) (Sizes.seqXmat d n (ω (j + 1))) := by
  unfold stepZ
  rw [Expansion_linTr_Ab]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp [gridDelta]
  · intro c _ hc
    simp [gridDelta, Ne.symm hc]
  · simp

/-- **`stepZ` is linear in the real kernel `U`** (pointwise, every `ω`):
`stepZ U b ω = Σ_a U(b,a) · stepZ δ a ω`. -/
theorem stepZ_eq_sum_gridDelta
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n))
    (ω : PathΩ d) :
    stepZ d s t K n j Φ U b ω
      = ∑ a : Z2 (d.L n) × Z2 (d.L n), U b a * stepZ d s t K n j Φ (gridDelta (d.L n)) a ω := by
  rw [show stepZ d s t K n j Φ U b ω = Real.sqrt (gridStep s t K n)
      * linTr n (Ab d s t K n j Φ U b ω) (Sizes.seqXmat d n (ω (j + 1))) from rfl,
    Expansion_linTr_Ab, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_stepZ_gridDelta]
  ring

/-- The entries of `𝒰_{v,w}` at `ξ = |m|²` are real (`ukerNonneg`, `|E| ≤ 2`), so the complex
product of two entries is the complex number of its real part. -/
private theorem Expansion_ukerMat_mul_eq (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v)
    (hvw : v ≤ w) (hw1 : w < 1) (b a : Z2 (d.L n) × Z2 (d.L n)) :
    (((ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re : ℝ) : ℂ)
      = ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2 := by
  have hξ : Complex.normSq (spectralM E) = 1 := normSqSpectralMOne E hE
  have h1 := ukerNonneg (d.L n) (d.three_le_L n) (Complex.normSq (spectralM E)) v w
    (Complex.normSq_nonneg _) hv0 hvw (by rw [hξ]; linarith) b.1 a.1
  have h2 := ukerNonneg (d.L n) (d.three_le_L n) (Complex.normSq (spectralM E)) v w
    (Complex.normSq_nonneg _) hv0 hvw (by rw [hξ]; linarith) b.2 a.2
  apply Complex.ext
  · simp
  · simp [Complex.mul_im, h1.1, h2.1]

/-- **`stepZ_ukerMat_eq_Uker`**: for every `ω` and `0 ≤ v ≤ w < 1`, `|E| ≤ 2`, the kernel
folded into the label weight equals `𝒰_{v,w}` applied to the `w`-independent label vector
`a ↦ stepZ δ a ω`. -/
theorem stepZ_ukerMat_eq_Uker
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (b : Z2 (d.L n) × Z2 (d.L n)) (ω : PathΩ d) :
    (stepZ d s t K n j Φ
        (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
          * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω : ℂ)
      = Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w
          (fun a => (stepZ d s t K n j Φ (gridDelta (d.L n)) a ω : ℂ)) b := by
  rw [stepZ_eq_sum_gridDelta]
  push_cast
  unfold Uop
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_ukerMat_mul_eq d n E hE hv0 hvw hw1 b a]

/-- The label-`a` step of `stepXi` at the identity kernel: `Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j]`. -/
private theorem Expansion_stepXi_delta
    (Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (a : Z2 (d.L n) × Z2 (d.L n)) (ω : PathΩ d) :
    stepXi d s t K n j Φ (gridDelta (d.L n)) a ω
      = Φ a (pathH d s t K n (j + 1) ω)
        - (pathP d)[fun ω' => Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω := by
  have hfun : (fun ω' : PathΩ d => ∑ c : Z2 (d.L n) × Z2 (d.L n),
        ((gridDelta (d.L n) a c : ℝ) : ℂ) * Φ c (pathH d s t K n (j + 1) ω'))
      = fun ω' => Φ a (pathH d s t K n (j + 1) ω') := by
    funext ω'
    rw [Finset.sum_eq_single a]
    · simp [gridDelta]
    · intro c _ hc
      simp [gridDelta, Ne.symm hc]
    · simp
  have h1 := congrFun hfun ω
  unfold stepXi
  rw [h1, hfun]

/-- **`stepXi` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`
(the observables lie in the Hermitian class `HermTestFun`; integrability is
`Expansion_integrable_phi`). -/
theorem stepXi_eq_sum_gridDelta_ae
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Z2 (d.L n) × Z2 (d.L n),
      stepXi d s t K n j Φ U b ω
        = ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * stepXi d s t K n j Φ (gridDelta (d.L n)) a ω := by
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset (Z2 (d.L n) × Z2 (d.L n))),
      Integrable (fun ω : PathΩ d => (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω)) (pathP d) :=
    fun a _ => (Expansion_integrable_phi d s t K n (hΦ a) (j + 1)).const_mul (U b a : ℂ)
  have hcondsum := condExp_finsetSum hint_a (filt d j)
  have hsmul_ae : ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
      (pathP d)[fun ω' => (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω
        = (U b a : ℂ) * (pathP d)[fun ω' => Φ a (pathH d s t K n (j + 1) ω') | filt d j] ω :=
    ae_all_iff.mpr fun a => condExp_smul (U b a : ℂ)
      (fun ω' => Φ a (pathH d s t K n (j + 1) ω')) (filt d j)
  have hsum_fn : (∑ a : Z2 (d.L n) × Z2 (d.L n),
        fun ω' : PathΩ d => (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω'))
      = (fun ω' : PathΩ d => ∑ a : Z2 (d.L n) × Z2 (d.L n),
          (U b a : ℂ) * Φ a (pathH d s t K n (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [Expansion_stepXi_delta]
  unfold stepXi
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepY` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`. -/
theorem stepY_eq_sum_gridDelta_ae
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Z2 (d.L n) × Z2 (d.L n),
      stepY d s t K n j Φ U b ω
        = ∑ a : Z2 (d.L n) × Z2 (d.L n), (U b a : ℂ) * stepY d s t K n j Φ (gridDelta (d.L n)) a ω := by
  filter_upwards [stepXi_eq_sum_gridDelta_ae d s t K n j hΦ U] with ω hω b
  unfold stepY
  rw [hω b, stepZ_eq_sum_gridDelta d s t K n j Φ U b ω]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepY_ukerMat_eq_Uker_ae`**: for `0 ≤ v ≤ w < 1`, `|E| ≤ 2`, a.e. `ω`, for every label `b`,
the kernel folded into the label weight equals `𝒰_{v,w}` applied to the `w`-independent label
vector `a ↦ stepY δ a ω`. -/
theorem stepY_ukerMat_eq_Uker_ae
    {Φ : Z2 (d.L n) × Z2 (d.L n) → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun d n (Φ a))
    (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Z2 (d.L n) × Z2 (d.L n),
      stepY d s t K n j Φ
          (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re) b ω
        = Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w
            (fun a => stepY d s t K n j Φ (gridDelta (d.L n)) a ω) b := by
  filter_upwards [stepY_eq_sum_gridDelta_ae d s t K n j hΦ
    (fun b a => (ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) v w b.2 a.2).re)] with ω hω b
  rw [hω b]
  unfold Uop
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_ukerMat_mul_eq d n E hE hv0 hvw hw1 b a]

end Bridge

/-! ### 9. `Zvec`, `Yvec`, the identification `martInc = Zvec + Yvec` and the primed expansion -/

section ExpansionPrime

/-- **`Zvec`**: the `k`-independent label vector of the martingale (`Z`) part of the grid step
ending at index `i` (step `i-1 → i`, loop family at `u_i`, identity kernel):
`Zvec (j+1) ω a = stepZ j (Φ^{(u_{j+1})}) δ a ω`. -/
noncomputable def Zvec (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℂ :=
  (stepZ d s t K n (i - 1) (Expansion_loopObs d n E (gridTime s t K n i))
    (gridDelta (d.L n)) a ω : ℂ)

/-- **`Yvec`**: the `k`-independent label vector of the quadratic (`Y`) part of the grid step
ending at index `i`. -/
noncomputable def Yvec (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℂ :=
  stepY d s t K n (i - 1) (Expansion_loopObs d n E (gridTime s t K n i))
    (gridDelta (d.L n)) a ω

theorem Zvec_succ (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    Zvec d E s t K n (j + 1) ω a
      = (stepZ d s t K n j (Expansion_loopObs d n E (gridTime s t K n (j + 1)))
          (gridDelta (d.L n)) a ω : ℂ) := rfl

theorem Yvec_succ (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    Yvec d E s t K n (j + 1) ω a
      = stepY d s t K n j (Expansion_loopObs d n E (gridTime s t K n (j + 1)))
          (gridDelta (d.L n)) a ω := rfl

/-- **The martingale increment is `Z + Y`** (label-wise, a.e.): `martInc_j = Zvec_{j+1} +
Yvec_{j+1}`.  `𝒦` is a constant in `ω'` and cancels in `A_{j+1} - E[A_{j+1} | F_j]`, which is the
identity-kernel `stepXi`; then `stepXi = stepZ + stepY` by the definition of `stepY`. -/
theorem Expansion_martInc_eq_Zvec_add_Yvec (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    ∀ᵐ ω ∂(pathP d), ∀ a : Z2 (d.L n) × Z2 (d.L n),
      martInc d E s t K n j ω a = Zvec d E s t K n (j + 1) ω a + Yvec d E s t K n (j + 1) ω a := by
  have hu0' : 0 ≤ gridTime s t K n (j + 1) :=
    Expansion_gridTime_nonneg s t K n hs0 hst (j + 1)
  refine ae_all_iff.2 fun a => ?_
  have hΦ : HermTestFun d n (Expansion_loopObs d n E (gridTime s t K n (j + 1)) a) :=
    (hermTestFun_loopPM d n E _ hu0' hu1 hE a).1
  have hint := Expansion_integrable_phi d s t K n hΦ (j + 1)
  have h := condExp_sub hint
    (integrable_const (Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2)) (filt d j)
  have hfg : (fun ω' => Avec d E s t K n (j + 1) ω' a)
      = (fun ω' : PathΩ d => Expansion_loopObs d n E (gridTime s t K n (j + 1)) a
          (pathH d s t K n (j + 1) ω'))
        - fun _ => Kpm (d.L n) (d.W n) E (gridTime s t K n (j + 1)) a.1 a.2 := rfl
  filter_upwards [h] with ω hω
  have hmart : martInc d E s t K n j ω a
      = Expansion_loopObs d n E (gridTime s t K n (j + 1)) a (pathH d s t K n (j + 1) ω)
        - (pathP d)[fun ω' => Expansion_loopObs d n E (gridTime s t K n (j + 1)) a
            (pathH d s t K n (j + 1) ω') | filt d j] ω := by
    unfold martInc
    rw [hfg, hω, Pi.sub_apply, condExp_const ((filt d).le j)]
    simp only [Avec, Expansion_loopObs]
    ring
  rw [hmart, Zvec_succ, Yvec_succ]
  unfold stepY
  rw [Expansion_stepXi_delta]
  ring

/-- **`grid_expansion'`**: the primed version of `grid_expansion`.  For a fixed `k ≤ K n`, a.e.
`ω`, for every label `b`, with the `Z` and `Y` sums in the applied-vector shape
`(Σ_{j<k} 𝒰_{u_{j+1},u_k} (Zvec_{j+1} ω)) b`, `(Σ_{j<k} 𝒰_{u_{j+1},u_k} (Yvec_{j+1} ω)) b`
(label vectors independent of `k`), the drift sum `(Σ_{j<k} Δ • 𝒰_{u_{j+1},u_k} (D_j ω)) b` and the
remainder sum `(Σ_{j<k} 𝒰_{u_{j+1},u_k} (R_j ω)) b`. -/
theorem grid_expansion' (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n k : ℕ) (hk : k ≤ K n) :
    ∀ᵐ ω ∂(pathP d), ∀ b : Z2 (d.L n) × Z2 (d.L n),
      Avec d E s t K n k ω b
        = Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec d E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec d E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec d E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid d E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid d E s t K n j ω)) b := by
  have hae : ∀ᵐ ω ∂(pathP d), ∀ j : ℕ, j < k → ∀ a : Z2 (d.L n) × Z2 (d.L n),
      martInc d E s t K n j ω a
        = Zvec d E s t K n (j + 1) ω a + Yvec d E s t K n (j + 1) ω a := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hjk : j < k
    · have hu1 : gridTime s t K n (j + 1) < 1 :=
        Expansion_gridTime_lt_one s t K n (hst n) (hK n) (ht1 n) (by omega)
      filter_upwards [Expansion_martInc_eq_Zvec_add_Yvec d E s t K n j hE (hs0 n) (hst n) hu1]
        with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hjk
  filter_upwards [hae] with ω hω b
  rw [grid_expansion d E s t K hE hs0 hst ht1 hK n k hk ω]
  have hsum : ∑ j ∈ Finset.range k,
        Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
          (gridTime s t K n k)
          ((gridStep s t K n : ℂ) • Dgrid d E s t K n j ω + Rgrid d E s t K n j ω
            + martInc d E s t K n j ω)
      = (∑ j ∈ Finset.range k,
          Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Zvec d E s t K n (j + 1) ω))
        + (∑ j ∈ Finset.range k,
          Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Yvec d E s t K n (j + 1) ω))
        + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
          Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Dgrid d E s t K n j ω))
        + (∑ j ∈ Finset.range k,
          Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Rgrid d E s t K n j ω)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmj : martInc d E s t K n j ω
        = (Zvec d E s t K n (j + 1) ω) + (Yvec d E s t K n (j + 1) ω) :=
      funext (hω j (Finset.mem_range.1 hj))
    rw [hmj]
    simp only [Uop_add, Uop_smul]
    abel
  rw [hsum]
  simp only [Pi.add_apply]
  ring

/-- **`grid_expansion_all'`**: the statement of `grid_expansion'` a.e. simultaneously for every
`k ≤ K n` and every label `b` (one null set). -/
theorem grid_expansion_all' (d : Sizes) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n : ℕ) :
    ∀ᵐ ω ∂(pathP d), ∀ k : ℕ, k ≤ K n → ∀ b : Z2 (d.L n) × Z2 (d.L n),
      Avec d E s t K n k ω b
        = Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec d E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec d E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec d E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid d E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop (d.L n) (Complex.normSq (spectralM E) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid d E s t K n j ω)) b := by
  refine ae_all_iff.mpr fun k => ?_
  by_cases hk : k ≤ K n
  · filter_upwards [grid_expansion' d E s t K hE hs0 hst ht1 hK n k hk] with ω hω _
    exact hω
  · exact Filter.Eventually.of_forall fun _ h => absurd h hk

end ExpansionPrime

end RBM.Path

end
