/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodEventClose
import RBM2D.Path.DriftPoint
import RBM2D.Path.TimeSums

/-!
# The grid step bound on the good event

Paper: arXiv:2503.07606, the display before `\label{52}` in Step 2 of `lem:main_ind`.

## Main declarations

* `GridStepBoundPT`: the grid step bound;
* `gridStepBoundPT : GridStepBoundPT d`.

## Proof outline

At the first-hit time `τ` the a.e. expansion `grid_expansion_all'` splits `A_τ` into five
parts.  On the good event (`goodEvent_grid_imp`):
* the initial term by `sumNdecayEta` (near, `|a| < ℓ*`) or `tailtoTail` (far);
* the martingale and `Y` parts by the good-event items;
* the drift by `driftPoint` at each `u_j`, after splitting off the transport-start correction
  `𝒰_{u_{j+1},u_τ}(D_j - 𝒰_{u_j,u_{j+1}} D_j)` (`Uop_comp`, `uopOneStep`), and the time sums
  `driftTimeSumD` term by term;
* the remainder by `Expansion_condExp_A_succ_rpow` and `sumNdecayEta`.
The multipliers are absorbed into `N^η` by `azumaMm_le` (`StepBound_absorb`,
`StepBound_absorbΛ`), and the absolute tail `N^{η+δ/16} r² W^{-D}` carries the far part of the
transported initial term.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

variable (d : Sizes)

set_option linter.style.longLine false

/-- **The grid step bound on the good event.**  Paper: the bound of `J*_{u_τ}` in Step 2 before
(`52`): the expansion (`grid_expansion_all'`) at `k = τ` with its five parts, the drift
(`driftPoint`, `driftTimeSumD`), the martingale and `Y` (`goodEvent_grid_imp`), the initial term
(`uopLocalMax`/`tailtoTail`) and the remainder (`condExp_A_succ`).  Deterministic given the good
event, for `pathP`-a.e. `ω` (the expansion identity is a.e.).  With `r = η_s/η_{u_τ}`,
`M = M_{u_τ}`, `N = size n` and any `η > 0`, eventually:
`‖A_τ(a)‖ ≤ N^η [(N^{δ/16} r² + azumaMm r^{5/2} + N^{6ε} r³) 1(|a| ≤ 6ℓ*_{u_τ}) + N^{δ/16}
  + azumaMm (N^δ r^{19/4} M^{-1/4} + N^{3δ/2} r^6 M^{-1/2} + 1) + 3
  + N^{6ε} (N^{2δ} r^8 M^{-1} + N^{2δ} r^9 M^{-1/2})] 𝒯_{u_τ,D}(|a|) + N^{η + δ/16} r² W^{-D}`.
Used in: `GridStep2PTClose`, `GridStep2Eq53PTClose`. -/
def GridStepBoundPT : Prop :=
  ∀ (κ c τ' : ℝ) (E : ℕ → ℝ) (s v t : ℕ → ℝ) (δ D ε D' Cc Cx : ℝ),
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    (∀ n, t n < 1) → 0 < c → Bandwidth d c → 0 < τ' → RangeCond d τ' t →
    CondStInd d E s t → RBM.Ind.SizeTendsto d →
    0 < δ → δ ≤ c / 200 → 20 + 2 / c ≤ D → 0 < ε → 2 * D + 3 + (7 + ε) / c ≤ D' →
    D + 1 ≤ Cc → D + 1 ≤ Cx →
    ∀ D₁ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP d),
      ω ∈ goodEventGrid d E s v (gridK d D (D₁ + 1)) δ D ε D' Cc Cx n →
      ∀ a : Z2 (d.L n) × Z2 (d.L n),
        let N : ℝ := ((d.size n : ℕ) : ℝ)
        let K : ℕ → ℕ := gridK d D (D₁ + 1)
        let uτ : ℝ := gridTime s v K n (gridTauFull d E s v K δ D ε n ω)
        let r : ℝ := etaT (E n) (s n) / etaT (E n) uτ
        let M : ℝ := scaleM (d.L n) (d.W n) (E n) uτ
        let Az : ℝ := azumaMm d E δ ε n
        ‖Avec d (E n) s v K n (gridTauFull d E s v K δ D ε n ω) ω a‖ ≤
          N ^ η *
              ((N ^ (δ / 16) * r ^ 2 + Az * r ^ ((5 : ℝ) / 2) + N ^ (6 * ε) * r ^ 3) *
                  (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) uτ
                    then 1 else 0) +
                N ^ (δ / 16) +
                Az * (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4) +
                  N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2) + 1) + 3 +
                N ^ (6 * ε) * (N ^ (2 * δ) * r ^ 8 * M⁻¹ +
                  N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2))) *
              tailT (d.L n) (d.W n) (E n) D uτ (zdist2 (d.L n) (a.1 - a.2) : ℝ) +
            N ^ (η + δ / 16) * r ^ 2 * (d.W n : ℝ) ^ (-D)

/-! ## 2. Scalar helpers -/

/-- `c_κ = √(κ(4-κ))/2 ≤ Im m(E_n)` under `|E_n| ≤ 2 - κ` (copy of the private
`GoodEventClose_im_ge`, `RBM2D/Path/GoodEventClose.lean`). -/
private theorem StepBound_im_ge {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (n : ℕ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 ∧ Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg (E n); have := hE n; linarith
  have hpos : 0 < κ * (4 - κ) := by nlinarith
  refine ⟨by positivity, ?_⟩
  rw [spectralM_im]
  have hE2 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hE n) 2
  have : κ * (4 - κ) ≤ 4 - E n ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- `Im m(E) ≤ 1`. -/
private theorem StepBound_im_le_one (E : ℝ) : (spectralM E).im ≤ 1 := by
  rw [spectralM_im, div_le_one (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_iff]
  exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩

/-- `𝒰_{v,w}` commutes with differences. -/
private theorem StepBound_Uop_sub (L : ℕ) [NeZero L] (ξ : ℂ) (v w : ℝ)
    (A B : Z2 L × Z2 L → ℂ) : Uop L ξ v w (A - B) = Uop L ξ v w A - Uop L ξ v w B := by
  funext a
  simp only [Uop, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The homogeneity step: `θ² a ≤ θ² b + c` for every `θ > 0` and `c ≥ 0` give `a ≤ b`. -/
private theorem StepBound_le_of_homog {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ θ : ℝ, 0 < θ → θ ^ 2 * a ≤ θ ^ 2 * b + c) : a ≤ b := by
  rcases le_or_gt a b with hle | hab
  · exact hle
  exfalso
  have hab' : 0 < a - b := by linarith
  set θ : ℝ := Real.sqrt ((c + 1) / (a - b)) with hθ
  have hq : 0 < (c + 1) / (a - b) := by positivity
  have hθ0 : 0 < θ := Real.sqrt_pos.2 hq
  have hθ2 : θ ^ 2 = (c + 1) / (a - b) := Real.sq_sqrt hq.le
  have h1 := h θ hθ0
  have h2 : θ ^ 2 * (a - b) = c + 1 := by rw [hθ2]; field_simp
  nlinarith

/-- Five-term triangle inequality. -/
private theorem StepBound_tri5 (x₁ x₂ x₃ x₄ x₅ : ℂ) :
    ‖x₁ + x₂ + x₃ + x₄ + x₅‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ := by
  have h1 := norm_add_le (x₁ + x₂ + x₃ + x₄) x₅
  have h2 := norm_add_le (x₁ + x₂ + x₃) x₄
  have h3 := norm_add_le (x₁ + x₂) x₃
  have h4 := norm_add_le x₁ x₂
  linarith

/-! ## 3. The one-step generator bound -/

section RowHelpers

variable (L : ℕ) [NeZero L]

open scoped Matrix.Norms.Operator

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm (the same bound as the private
`sum_norm_row_le_opNorm` in `RBM2D/Path/UBounds.lean`). -/
private theorem StepBound_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}` (the same bound as the private
`sum_norm_thetaGenMat_row_le` in `RBM2D/Path/UBounds.lean`). -/
private theorem StepBound_thetaGenMat_row_le (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Z2 L, ‖thetaGenMat L ξ s x c‖ =
      ‖ξ‖ * ‖(SB L * Theta L ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((StepBound_row_le_opNorm L _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L ((s : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L ((s : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hsξ

/-- `‖Θ_{u,(+,-)} ∘ A‖_max ≤ 2 (1-u)⁻¹ ‖A‖_max` at `ξ = 1`, `0 ≤ u < 1`. -/
private theorem StepBound_norm_thetaGen_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {A : Z2 L × Z2 L → ℂ} {α : ℝ} (hA : ∀ b, ‖A b‖ ≤ α) (a : Z2 L × Z2 L) :
    ‖thetaGen L 1 u A a‖ ≤ 2 * (1 - u)⁻¹ * α := by
  have hnu : ‖(u : ℂ) * 1‖ = u := by
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have hrow : ∀ x : Z2 L, ∑ c : Z2 L, ‖thetaGenMat L 1 u x c‖ ≤ (1 - u)⁻¹ := by
    intro x
    have h := StepBound_thetaGenMat_row_le L hL (ξ := 1) (s := u) (by rw [hnu]; exact hu1) x
    rwa [hnu, norm_one, one_mul] at h
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA a)
  unfold thetaGen
  calc ‖∑ b : Z2 L, (thetaGenMat L 1 u a.1 b * A (b, a.2) + thetaGenMat L 1 u a.2 b * A (a.1, b))‖
      ≤ ∑ b : Z2 L, ‖thetaGenMat L 1 u a.1 b * A (b, a.2) + thetaGenMat L 1 u a.2 b * A (a.1, b)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : Z2 L, (‖thetaGenMat L 1 u a.1 b‖ * α + ‖thetaGenMat L 1 u a.2 b‖ * α) := by
        refine Finset.sum_le_sum fun b _ => (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _))
    _ = (∑ b : Z2 L, ‖thetaGenMat L 1 u a.1 b‖) * α + (∑ b : Z2 L, ‖thetaGenMat L 1 u a.2 b‖) * α := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (1 - u)⁻¹ * α + (1 - u)⁻¹ * α :=
        add_le_add (mul_le_mul_of_nonneg_right (hrow _) hα) (mul_le_mul_of_nonneg_right (hrow _) hα)
    _ = 2 * (1 - u)⁻¹ * α := by ring

end RowHelpers

/-- `(normSq m(E) : ℂ) = 1` for `|E| < 2`. -/
private theorem StepBound_xi_one {E : ℝ} (hE : |E| < 2) :
    ((Complex.normSq (spectralM E) : ℝ) : ℂ) = 1 := by
  rw [normSqSpectralMOne _ hE.le, Complex.ofReal_one]

/-- `sumNdecayEta` at `ξ = 1`. -/
private theorem StepBound_sumNdecay (L : ℕ) [NeZero L] (hL : 3 ≤ L) {E v w : ℝ} (hE : |E| < 2)
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) {A : Z2 L × Z2 L → ℂ} {α : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ α) (a : Z2 L × Z2 L) :
    ‖Uop L 1 v w A a‖ ≤ (etaT E v / etaT E w) ^ 2 * α := by
  have h := sumNdecayEta L hL E v w hE hv0 hvw hw1 A α hA a
  rwa [StepBound_xi_one hE] at h

/-- **The transport-start correction**: the one-step defect
`A - 𝒰_{u,u+Δ} A`, transported from `u + Δ` to `v`, from `uopOneStep`, the generator bound and
`sumNdecayEta`. -/
private theorem StepBound_corr (L : ℕ) [NeZero L] (hL : 3 ≤ L) {E u v Δ α : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (huv : u + Δ ≤ v) (hv1 : v < 1) {A : Z2 L × Z2 L → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ α) (a : Z2 L × Z2 L) :
    ‖Uop L 1 (u + Δ) v (A - Uop L 1 u (u + Δ) A) a‖ ≤
      (etaT E (u + Δ) / etaT E v) ^ 2 *
        (Δ * (2 * (1 - u)⁻¹ * α) + 3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α) := by
  have huΔ : u + Δ < 1 := huv.trans_lt hv1
  have hu1 : u < 1 := by linarith
  have hX : ∀ b, ‖(A - Uop L 1 u (u + Δ) A) b‖ ≤
      Δ * (2 * (1 - u)⁻¹ * α) + 3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α := by
    intro b
    have h1 := uopOneStep L hL 1 (by rw [norm_one]) u Δ hu0 hΔ huΔ A α hA b
    have h2 := StepBound_norm_thetaGen_le L hL hu0 hu1 hA b
    have e : (A - Uop L 1 u (u + Δ) A) b =
        -(Uop L 1 u (u + Δ) A b - A b - (Δ : ℂ) * thetaGen L 1 u A b) -
          (Δ : ℂ) * thetaGen L 1 u A b := by
      simp only [Pi.sub_apply]; ring
    rw [e]
    have h3 : ‖(Δ : ℂ) * thetaGen L 1 u A b‖ ≤ Δ * (2 * (1 - u)⁻¹ * α) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
      exact mul_le_mul_of_nonneg_left h2 hΔ
    calc ‖-(Uop L 1 u (u + Δ) A b - A b - (Δ : ℂ) * thetaGen L 1 u A b) -
          (Δ : ℂ) * thetaGen L 1 u A b‖
        ≤ ‖-(Uop L 1 u (u + Δ) A b - A b - (Δ : ℂ) * thetaGen L 1 u A b)‖ +
            ‖(Δ : ℂ) * thetaGen L 1 u A b‖ := norm_sub_le _ _
      _ ≤ 3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α + Δ * (2 * (1 - u)⁻¹ * α) := by
          rw [norm_neg]; exact add_le_add h1 h3
      _ = _ := by ring
  exact StepBound_sumNdecay L hL hE (by linarith) huv hv1 hX a

/-! ## 4. The initial term -/

/-- `√((log W)^{3/2}) = (log W)^{3/4}`. -/
private theorem StepBound_sqrt_pow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ ((3 : ℝ) / 2)) = x ^ ((3 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

/-- **The initial term** `𝒰_{s,u} A_0` from `‖A_0‖ ≤ X₄ 𝒯_{s,D}`: near (`|a| < ℓ*_u`) by
`sumNdecayEta` and `M_u ≤ M_s`, far by `tailtoTail`. -/
private theorem StepBound_init (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) {E D D'' s u X4 : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hu1 : u < 1)
    (hlogW : 4 ≤ Real.log W) (hMu : 1 ≤ scaleM L W E u)
    (hfar : UkerFar L W s u (ellStar L W u / 4) D'')
    (hfl : 4 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D))
    (hX4 : 0 < X4) {A : Z2 L × Z2 L → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ X4 * tailT L W E D s (zdist2 L (b.1 - b.2) : ℝ)) (a : Z2 L × Z2 L) :
    ‖Uop L 1 s u A a‖ ≤
      (Real.exp (Real.log W ^ ((3 : ℝ) / 4)) + 1) * (X4 * (etaT E s / etaT E u) ^ 2) *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 6 * ellStar L W u then 1 else 0) *
          tailT L W E D u (zdist2 L (a.1 - a.2) : ℝ) +
        30000 * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * X4 *
          tailT L W E D u (zdist2 L (a.1 - a.2) : ℝ) +
        2 * (X4 * (etaT E s / etaT E u) ^ 2 * (W : ℝ) ^ (-D)) := by
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hs1 : s < 1 := hsu.trans_lt hu1
  set ℓa : ℝ := (zdist2 L (a.1 - a.2) : ℝ) with hℓa
  have hℓa0 : 0 ≤ ℓa := Nat.cast_nonneg _
  set Λ : ℝ := Real.exp (Real.log W ^ ((3 : ℝ) / 4)) with hΛ
  have hlog0 : 0 ≤ Real.log (W : ℝ) := by linarith
  have hΛ1 : 1 ≤ Λ := Real.one_le_exp (Real.rpow_nonneg hlog0 _)
  set T : ℝ := tailT L W E D u ℓa with hT
  have hT0 : 0 < T := tailT_pos hW1 L E D u ℓa
  set r : ℝ := etaT E s / etaT E u with hr
  have hr0 : 0 ≤ r := div_nonneg (etaT_pos hE hs1).le (etaT_pos hE hu1).le
  have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hℓu : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have hst0 : 0 ≤ ellStar L W u := mul_nonneg (Real.rpow_nonneg hlog0 _) hℓu.le
  have hMu0 : 0 < scaleM L W E u := by linarith
  have hind0 : (0 : ℝ) ≤ (if ℓa ≤ 6 * ellStar L W u then 1 else 0) := by
    split_ifs <;> norm_num
  have hterm1 : 0 ≤ (Λ + 1) * (X4 * r ^ 2) * (if ℓa ≤ 6 * ellStar L W u then 1 else 0) * T := by
    have : 0 ≤ Λ + 1 := by linarith
    positivity
  have hterm2 : 0 ≤ 30000 * Λ * X4 * T := by positivity
  have hterm3 : 0 ≤ 2 * (X4 * r ^ 2 * (W : ℝ) ^ (-D)) := by positivity
  by_cases hnear : ℓa < ellStar L W u
  · -- near: `sumNdecayEta`
    have hα : ∀ b : Z2 L × Z2 L, ‖A b‖ ≤ X4 * ((scaleM L W E s ^ 2)⁻¹ + (W : ℝ) ^ (-D)) := by
      intro b
      refine (hA b).trans (mul_le_mul_of_nonneg_left ?_ hX4.le)
      unfold tailT
      have he : Real.exp (-Real.sqrt ((zdist2 L (b.1 - b.2) : ℝ) / ellT L s)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
      have hi : 0 ≤ (scaleM L W E s ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
      exact add_le_add_left (mul_le_of_le_one_right hi he) _
    have h1 := StepBound_sumNdecay L hL hE hs0 hsu hu1 hα a
    have hMsu : scaleM L W E u ≤ scaleM L W E s := (scaleM_anti_ratio (W := W) hL1 hE hsu hu1).1
    have hinvM : (scaleM L W E s ^ 2)⁻¹ ≤ (scaleM L W E u ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hMu0 2) (pow_le_pow_left₀ hMu0.le hMsu 2)
    have hsq : Real.sqrt (ℓa / ellT L u) ≤ Real.log W ^ ((3 : ℝ) / 4) := by
      rw [← StepBound_sqrt_pow hlog0]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ hℓu]
      exact hnear.le
    have hexp : 1 ≤ Λ * Real.exp (-Real.sqrt (ℓa / ellT L u)) := by
      rw [hΛ, ← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hMi0 : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hmain : (scaleM L W E u ^ 2)⁻¹ + (W : ℝ) ^ (-D) ≤ (Λ + 1) * T := by
      rw [hT]; unfold tailT
      have hE0 : 0 ≤ Real.exp (-Real.sqrt (ℓa / ellT L u)) := (Real.exp_pos _).le
      have h1 := mul_le_mul_of_nonneg_left hexp hMi0
      have h2 : 0 ≤ (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (ℓa / ellT L u)) :=
        mul_nonneg hMi0 hE0
      have h3 : 0 ≤ Λ * (W : ℝ) ^ (-D) := mul_nonneg (by linarith) hWD
      linarith
    have hind : (if ℓa ≤ 6 * ellStar L W u then (1 : ℝ) else 0) = 1 := by
      rw [ite_eq_left_iff]; intro h; exact absurd (by linarith) h
    have hchain : ‖Uop L 1 s u A a‖ ≤ (Λ + 1) * (X4 * r ^ 2) * 1 * T := by
      calc ‖Uop L 1 s u A a‖ ≤ r ^ 2 * (X4 * ((scaleM L W E s ^ 2)⁻¹ + (W : ℝ) ^ (-D))) := h1
        _ ≤ r ^ 2 * (X4 * ((Λ + 1) * T)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hX4.le) (sq_nonneg _)
            exact (add_le_add_left hinvM _).trans hmain |>.trans' (by linarith)
        _ = (Λ + 1) * (X4 * r ^ 2) * 1 * T := by ring
    rw [hind]
    linarith
  · -- far: `tailtoTail` applied to `X₄⁻¹ A`
    have hfar_a : ellStar L W u ≤ ℓa := not_lt.1 hnear
    set c : ℂ := ((X4⁻¹ : ℝ) : ℂ) with hc
    have hcn : ‖c‖ = X4⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hX4)]
    have hA' : ∀ b : Z2 L × Z2 L, ‖(c • A) b‖ ≤ tailT L W E D s (zdist2 L (b.1 - b.2) : ℝ) := by
      intro b
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, hcn]
      calc X4⁻¹ * ‖A b‖ ≤ X4⁻¹ * (X4 * tailT L W E D s (zdist2 L (b.1 - b.2) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hA b) (inv_nonneg.2 hX4.le)
        _ = tailT L W E D s (zdist2 L (b.1 - b.2) : ℝ) := by field_simp
    have h := tailtoTail L W E D D'' s u hL hE hD hs0 hsu hu1 hlogW hMu hfar hfl (c • A) hA' a
      hfar_a
    rw [Uop_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hcn] at h
    have hMi0 : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hTge : (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (ℓa / ellT L u)) ≤ T := by
      rw [hT]; unfold tailT; linarith
    have hb : X4⁻¹ * ‖Uop L 1 s u A a‖ ≤ 30000 * Λ * T + 2 * r ^ 2 * (W : ℝ) ^ (-D) := by
      refine h.trans ?_
      have : 0 ≤ 30000 * Λ := by positivity
      have h1 := mul_le_mul_of_nonneg_left hTge this
      linarith
    have hb' : ‖Uop L 1 s u A a‖ ≤ X4 * (30000 * Λ * T + 2 * r ^ 2 * (W : ℝ) ^ (-D)) := by
      have := mul_le_mul_of_nonneg_left hb hX4.le
      rwa [← mul_assoc, mul_inv_cancel₀ hX4.ne', one_mul] at this
    linarith
/-! ## 5. The drift -/

/-- **The drift at one grid time** (`driftPoint` with `J* ≤ Θ (η_s/η_u)⁴`). -/
private theorem StepBound_drift_j (L W : ℕ) [NeZero L] [NeZero W] {E s u v D D'' Λ K₀ Θ : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hE2 : E2Hyp L W E s u v D Λ K₀ M)
    (hfar : UkerFar L W u v (ellStar L W v) D'')
    (hfl : 16 * (L : ℝ) ^ 6 * (W : ℝ) ^ 6 * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D))
    (hJ : jStarMat L W E D u M ≤ Θ * (etaT E s / etaT E u) ^ 4) (a : Z2 L × Z2 L) :
    ‖Uop L 1 u v (fun b => ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2) a‖ ≤
      2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ *
        ((etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ *
            ((scaleM L W E u)⁻¹ * (Θ * (etaT E s / etaT E u) ^ 4) ^ 2 +
              (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E u) ^ 4) ^ 2) +
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) *
            ((etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 6)) *
        tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, -, -, hlogW, -⟩ := id hE2
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu1 : u < 1 := huv.trans_lt hv1
  have h := driftPoint L W E s u v D D'' Λ K₀ M hE2 hfar hfl a
  set J := jStarMat L W E D u M with hJdef
  set B := Θ * (etaT E s / etaT E u) ^ 4 with hB
  have hJ0 : 0 ≤ J := zero_le_one.trans (one_le_jStarMat L W hW1 E D u M)
  have hJ2 : J ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 (scaleM_pos hL1 hW1 hE hu1).le
  have hMh : 0 ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hMi _
  have hρ2 : 0 ≤ (ellT L u / ellT L s) ^ 2 := sq_nonneg _
  have hC : 0 ≤ 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ *
      (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ := by
    have := (etaT_pos hE hu1).le
    unfold lossE2
    positivity
  have hT : 0 ≤ tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) := (tailT_pos hW1 L E D v _).le
  have hin : (scaleM L W E u)⁻¹ * J ^ 2 +
        (ellT L u / ellT L s) ^ 6 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
        (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * J ^ 2 ≤
      (scaleM L W E u)⁻¹ * B ^ 2 +
        (ellT L u / ellT L s) ^ 6 *
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
        (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * B ^ 2 :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left hJ2 hMi) le_rfl)
      (mul_le_mul_of_nonneg_left hJ2 (mul_nonneg hρ2 hMh))
  refine h.trans ?_
  calc _ ≤ 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ *
          (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ *
          ((scaleM L W E u)⁻¹ * B ^ 2 +
            (ellT L u / ellT L s) ^ 6 *
              (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W v then 1 else 0) +
            (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) * B ^ 2) *
          tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hin hC) hT
    _ = _ := by ring

/-- **The drift time sums, term by term**: `driftTimeSumD` at `Θ = 0` gives the near term, and
its homogeneity in `Θ` (`StepBound_le_of_homog`) gives the two far terms. -/
private theorem StepBound_timeSums {L W : ℕ} {E s v Θ : ℝ} {K : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : |E| < 2) (hs : 0 ≤ s) (hsv : s ≤ v) (hv : v < 1) (hK : 0 < K) :
    ∑ j ∈ Finset.range K, (v - s) / K *
        ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
          ((scaleM L W E (gridU s v K j))⁻¹ * (Θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
            (ellT L (gridU s v K j) / ellT L s) ^ 2 *
              (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
              (Θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2)) ≤
      ((spectralM E).im)⁻¹ *
        (Θ ^ 2 * (etaT E s / etaT E v) ^ 8 * (scaleM L W E v)⁻¹ / 6 +
          Θ ^ 2 * (etaT E s / etaT E v) ^ 9 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7) ∧
    ∑ j ∈ Finset.range K, (v - s) / K *
        ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
          (ellT L (gridU s v K j) / ellT L s) ^ 6) ≤
      ((spectralM E).im)⁻¹ * (etaT E s / etaT E v) ^ 3 := by
  set f : ℕ → ℝ := fun j => (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
        ((scaleM L W E (gridU s v K j))⁻¹ * ((etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 2 *
            (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
            ((etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2)) with hf
  set g : ℕ → ℝ := fun j => (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
        (ellT L (gridU s v K j) / ellT L s) ^ 6) with hg
  have hsplit : ∀ θ : ℝ, ∑ j ∈ Finset.range K, (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
        ((scaleM L W E (gridU s v K j))⁻¹ * (θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 2 *
            (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
            (θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 6)) =
      θ ^ 2 * ∑ j ∈ Finset.range K, f j + ∑ j ∈ Finset.range K, g j := by
    intro θ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, hg]
    ring
  have hsplit' : ∀ θ : ℝ, ∑ j ∈ Finset.range K, (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
        ((scaleM L W E (gridU s v K j))⁻¹ * (θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 2 *
            (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
            (θ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2)) =
      θ ^ 2 * ∑ j ∈ Finset.range K, f j := by
    intro θ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    ring
  have hD := fun θ (hθ : 0 ≤ θ) => driftTimeSumD L W E s v θ K hL hW hE hs hsv hv hK hθ
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  have hR0 : 0 ≤ etaT E s / etaT E v :=
    div_nonneg (etaT_pos hE (hsv.trans_lt hv)).le (etaT_pos hE hv).le
  have hg0 : 0 ≤ ∑ j ∈ Finset.range K, g j := by
    refine Finset.sum_nonneg fun j hj => ?_
    have hjK : j ≤ K := (Finset.mem_range.1 hj).le
    have hu : gridU s v K j < 1 := by
      have : gridU s v K j ≤ v := by
        unfold gridU
        have hK' : (0 : ℝ) < K := by exact_mod_cast hK
        have hj' : (j : ℝ) ≤ K := by exact_mod_cast hjK
        have : (j : ℝ) * ((v - s) / K) ≤ K * ((v - s) / K) :=
          mul_le_mul_of_nonneg_right hj' (div_nonneg (by linarith) hK'.le)
        rw [mul_div_cancel₀ _ hK'.ne'] at this
        linarith
      linarith
    have := (etaT_pos hE hu).le
    have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hvs : 0 ≤ v - s := by linarith
    simp only [hg]
    positivity
  refine ⟨?_, ?_⟩
  · rw [hsplit']
    have hF : ∑ j ∈ Finset.range K, f j ≤ ((spectralM E).im)⁻¹ *
        ((etaT E s / etaT E v) ^ 8 * (scaleM L W E v)⁻¹ / 6 +
          (etaT E s / etaT E v) ^ 9 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7) := by
      refine StepBound_le_of_homog (c := ((spectralM E).im)⁻¹ * (etaT E s / etaT E v) ^ 3)
        (by positivity) fun θ hθ => ?_
      have h1 := hD θ hθ.le
      rw [hsplit θ] at h1
      linarith
    calc Θ ^ 2 * ∑ j ∈ Finset.range K, f j ≤ Θ ^ 2 * (((spectralM E).im)⁻¹ *
          ((etaT E s / etaT E v) ^ 8 * (scaleM L W E v)⁻¹ / 6 +
            (etaT E s / etaT E v) ^ 9 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7)) :=
          mul_le_mul_of_nonneg_left hF (sq_nonneg _)
      _ = _ := by ring
  · have h1 := hD 0 le_rfl
    rw [hsplit 0] at h1
    have e : ((spectralM E).im)⁻¹ *
        ((0 : ℝ) ^ 2 * (etaT E s / etaT E v) ^ 8 * (scaleM L W E v)⁻¹ / 6 +
          (0 : ℝ) ^ 2 * (etaT E s / etaT E v) ^ 9 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7 +
          (etaT E s / etaT E v) ^ 3) = ((spectralM E).im)⁻¹ * (etaT E s / etaT E v) ^ 3 := by
      ring
    rw [e] at h1
    have e2 : (0 : ℝ) ^ 2 * ∑ j ∈ Finset.range K, f j = 0 := by ring
    rw [e2, zero_add] at h1
    exact h1

/-- **The drift sum** at the stopping index `τ`: the transport-start correction is split
off by `Uop_comp`, the main part is `StepBound_drift_j` at each `j < τ`, summed by
`StepBound_timeSums` on the grid `u_j = s + jΔ`. -/
private theorem StepBound_driftSum (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {E s D D'' Λ K₀ Θ Δ Cc : ℝ} (u : ℕ → ℝ) (Mj : ℕ → Matrix (Idx L W) (Idx L W) ℂ) (τ : ℕ)
    (hu : ∀ j, u j = s + j * Δ) (hs0 : 0 ≤ s) (hΔ : 0 ≤ Δ) (hτ1 : u τ < 1) (hE : |E| < 2)
    (hE2 : ∀ j < τ, E2Hyp L W E s (u j) (u τ) D Λ K₀ (Mj j))
    (hJ : ∀ j < τ, jStarMat L W E D (u j) (Mj j) ≤ Θ * (etaT E s / etaT E (u j)) ^ 4)
    (hfar : ∀ j < τ, UkerFar L W (u j) (u τ) (ellStar L W (u τ)) D'')
    (hfl : 16 * (L : ℝ) ^ 6 * (W : ℝ) ^ 6 * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D))
    (a : Z2 L × Z2 L)
    (hcorr : ∀ j < τ, ‖Uop L 1 (u (j + 1)) (u τ)
        ((fun b => ELKLK L W E (u j) (Mj j) b.1 b.2 + EGt L W E (u j) (Mj j) b.1 b.2) -
          Uop L 1 (u j) (u (j + 1))
            (fun b => ELKLK L W E (u j) (Mj j) b.1 b.2 + EGt L W E (u j) (Mj j) b.1 b.2)) a‖ ≤
        Cc) :
    ‖∑ j ∈ Finset.range τ, (Δ : ℂ) * Uop L 1 (u (j + 1)) (u τ)
        (fun b => ELKLK L W E (u j) (Mj j) b.1 b.2 + EGt L W E (u j) (Mj j) b.1 b.2) a‖ ≤
      2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ *
        (((spectralM E).im)⁻¹ *
            (Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 8 * (scaleM L W E (u τ))⁻¹ / 6 +
              Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 9 * (scaleM L W E (u τ))⁻¹ ^ ((1 : ℝ) / 2) / 7) +
          (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W (u τ) then 1 else 0) *
            (((spectralM E).im)⁻¹ * (etaT E s / etaT E (u τ)) ^ 3)) *
        tailT L W E D (u τ) (zdist2 L (a.1 - a.2) : ℝ) + τ * (Δ * Cc) := by
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  set Dj : ℕ → Z2 L × Z2 L → ℂ :=
    fun j b => ELKLK L W E (u j) (Mj j) b.1 b.2 + EGt L W E (u j) (Mj j) b.1 b.2 with hDj
  set C : ℝ := 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * lossE2 L W Λ K₀ with hC
  set T : ℝ := tailT L W E D (u τ) (zdist2 L (a.1 - a.2) : ℝ) with hT
  set χ : ℝ := if (zdist2 L (a.1 - a.2) : ℝ) ≤ 3 * ellStar L W (u τ) then 1 else 0 with hχ
  have hC0 : 0 ≤ C := by rw [hC]; unfold lossE2; positivity
  have hT0 : 0 < T := tailT_pos hW1 L E D (u τ) _
  have hχ0 : 0 ≤ χ := by rw [hχ]; split_ifs <;> norm_num
  have hmono : ∀ i j, i ≤ j → u i ≤ u j := fun i j hij => by
    rw [hu, hu]
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have hsu : ∀ j, s ≤ u j := fun j => by
    rw [hu]; have : (0 : ℝ) ≤ j * Δ := mul_nonneg (Nat.cast_nonneg j) hΔ; linarith
  -- one step: the correction is split off
  have hstep : ∀ j < τ, ‖Uop L 1 (u (j + 1)) (u τ) (Dj j) a‖ ≤
      ‖Uop L 1 (u j) (u τ) (Dj j) a‖ + Cc := by
    intro j hj
    have hj1 : u (j + 1) < 1 := (hmono _ _ hj).trans_lt hτ1
    have hv : ‖((u (j + 1) : ℝ) : ℂ) * 1‖ < 1 := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0.trans (hsu _))]
      exact hj1
    have hw : ‖((u τ : ℝ) : ℂ) * 1‖ < 1 := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0.trans (hsu _))]
      exact hτ1
    have e : Uop L 1 (u (j + 1)) (u τ) (Dj j) a =
        Uop L 1 (u j) (u τ) (Dj j) a +
          Uop L 1 (u (j + 1)) (u τ) (Dj j - Uop L 1 (u j) (u (j + 1)) (Dj j)) a := by
      rw [StepBound_Uop_sub, Uop_comp L hL hv hw]
      simp only [Pi.sub_apply]
      ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hcorr j hj))
  -- the main part at each `j < τ`
  have hdj : ∀ j < τ, ‖Uop L 1 (u j) (u τ) (Dj j) a‖ ≤
      C * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            ((scaleM L W E (u j))⁻¹ * (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2 +
              (ellT L (u j) / ellT L s) ^ 2 * (scaleM L W E (u j))⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2) +
          χ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            (ellT L (u j) / ellT L s) ^ 6)) * T := fun j hj =>
    StepBound_drift_j L W (hE2 j hj) (hfar j hj) hfl (hJ j hj) a
  have hsum : ‖∑ j ∈ Finset.range τ, (Δ : ℂ) * Uop L 1 (u (j + 1)) (u τ) (Dj j) a‖ ≤
      ∑ j ∈ Finset.range τ, Δ * ‖Uop L 1 (u j) (u τ) (Dj j) a‖ + τ * (Δ * Cc) := by
    calc ‖∑ j ∈ Finset.range τ, (Δ : ℂ) * Uop L 1 (u (j + 1)) (u τ) (Dj j) a‖
        ≤ ∑ j ∈ Finset.range τ, ‖(Δ : ℂ) * Uop L 1 (u (j + 1)) (u τ) (Dj j) a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range τ, (Δ * ‖Uop L 1 (u j) (u τ) (Dj j) a‖ + Δ * Cc) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ, ← mul_add]
          exact mul_le_mul_of_nonneg_left (hstep j (Finset.mem_range.1 hj)) hΔ
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine hsum.trans ?_
  rcases Nat.eq_zero_or_pos τ with hτ0 | hτpos
  · subst hτ0
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have hm : 0 < (spectralM E).im := spectralM_im_pos hE
    have hR : 0 ≤ etaT E s / etaT E (u 0) := by
      have h0 : u 0 = s := by rw [hu]; simp
      rw [h0]; exact div_nonneg (etaT_pos hE (by rw [← h0]; exact hτ1)).le
        (etaT_pos hE (by rw [← h0]; exact hτ1)).le
    have hM0 : 0 ≤ (scaleM L W E (u 0))⁻¹ := inv_nonneg.2 (scaleM_pos hL1 hW1 hE hτ1).le
    have hMh : 0 ≤ (scaleM L W E (u 0))⁻¹ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hM0 _
    push_cast
    simp only [zero_mul, add_zero]
    positivity
  · have hτR : (0 : ℝ) < τ := by exact_mod_cast hτpos
    have hΔeq : (u τ - s) / τ = Δ := by rw [hu]; field_simp; ring
    have hgu : ∀ j, gridU s (u τ) τ j = u j := fun j => by
      unfold gridU; rw [hΔeq, hu]
    have hTS := StepBound_timeSums (L := L) (W := W) (E := E) (s := s) (v := u τ) (Θ := Θ)
      (K := τ) hL1 hW1 hE hs0 (hsu τ) hτ1 hτpos
    simp only [hgu, hΔeq] at hTS
    obtain ⟨hF, hG⟩ := hTS
    have e : ∀ j, Δ * (C * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            ((scaleM L W E (u j))⁻¹ * (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2 +
              (ellT L (u j) / ellT L s) ^ 2 * (scaleM L W E (u j))⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2) +
          χ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            (ellT L (u j) / ellT L s) ^ 6)) * T) =
        C * T * (Δ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            ((scaleM L W E (u j))⁻¹ * (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2 +
              (ellT L (u j) / ellT L s) ^ 2 * (scaleM L W E (u j))⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2))) +
        C * T * χ * (Δ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            (ellT L (u j) / ellT L s) ^ 6)) := fun j => by ring
    have hmain : ∑ j ∈ Finset.range τ, Δ * ‖Uop L 1 (u j) (u τ) (Dj j) a‖ ≤
        C * T * (((spectralM E).im)⁻¹ *
            (Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 8 * (scaleM L W E (u τ))⁻¹ / 6 +
              Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 9 * (scaleM L W E (u τ))⁻¹ ^ ((1 : ℝ) / 2) / 7)) +
        C * T * χ * (((spectralM E).im)⁻¹ * (etaT E s / etaT E (u τ)) ^ 3) := by
      calc ∑ j ∈ Finset.range τ, Δ * ‖Uop L 1 (u j) (u τ) (Dj j) a‖
          ≤ ∑ j ∈ Finset.range τ, Δ * (C * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            ((scaleM L W E (u j))⁻¹ * (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2 +
              (ellT L (u j) / ellT L s) ^ 2 * (scaleM L W E (u j))⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2) +
          χ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            (ellT L (u j) / ellT L s) ^ 6)) * T) :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_left (hdj j (Finset.mem_range.1 hj)) hΔ
        _ = C * T * ∑ j ∈ Finset.range τ, (Δ * ((etaT E (u j) / etaT E (u τ)) ^ 2 * (etaT E (u j))⁻¹ *
            ((scaleM L W E (u j))⁻¹ * (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2 +
              (ellT L (u j) / ellT L s) ^ 2 * (scaleM L W E (u j))⁻¹ ^ ((1 : ℝ) / 2) *
                (Θ * (etaT E s / etaT E (u j)) ^ 4) ^ 2))) +
            C * T * χ * ∑ j ∈ Finset.range τ, (Δ * ((etaT E (u j) / etaT E (u τ)) ^ 2 *
              (etaT E (u j))⁻¹ * (ellT L (u j) / ellT L s) ^ 6)) := by
            simp_rw [e]
            rw [Finset.sum_add_distrib, Finset.mul_sum (a := C * T), Finset.mul_sum (a := C * T * χ)]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hF (mul_nonneg hC0 hT0.le))
            (mul_le_mul_of_nonneg_left hG (mul_nonneg (mul_nonneg hC0 hT0.le) hχ0))
    have hfin : C * T * (((spectralM E).im)⁻¹ *
            (Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 8 * (scaleM L W E (u τ))⁻¹ / 6 +
              Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 9 * (scaleM L W E (u τ))⁻¹ ^ ((1 : ℝ) / 2) / 7)) +
        C * T * χ * (((spectralM E).im)⁻¹ * (etaT E s / etaT E (u τ)) ^ 3) =
        C * (((spectralM E).im)⁻¹ *
            (Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 8 * (scaleM L W E (u τ))⁻¹ / 6 +
              Θ ^ 2 * (etaT E s / etaT E (u τ)) ^ 9 * (scaleM L W E (u τ))⁻¹ ^ ((1 : ℝ) / 2) / 7) +
          χ * (((spectralM E).im)⁻¹ * (etaT E s / etaT E (u τ)) ^ 3)) * T := by ring
    linarith


/-! ## 6. The eventual scalar facts -/

/-- **The drift multiplier is `N^{6ε} N^{o(1)}`**: from `azumaMm_le` at `δ = 4η`,
`2 e^{2(log W)^{3/4}} lossE2(N^ε, K₀) / Im m ≤ N^{6ε} N^η / 4`, eventually. -/
private theorem StepBound_absorb {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hsize : RBM.Ind.SizeTendsto d) {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4)) *
          lossE2 (d.L n) (d.W n) (((d.size n : ℕ) : ℝ) ^ ε)
            (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) * ((spectralM (E n)).im)⁻¹ ≤
        ((d.size n : ℕ) : ℝ) ^ (6 * ε) * ((d.size n : ℕ) : ℝ) ^ η / 4 := by
  filter_upwards [azumaMm_le (d := d) hκ hE hsize (δ := 4 * η) (by positivity) hε] with n h
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  set X : ℝ := 8 * (lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) *
      Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4))) / (spectralM (E n)).im with hX
  have hX0 : 0 ≤ X := by
    have := spectralM_im_pos (lt_of_le_of_lt (hE n) (by linarith) : |E n| < 2)
    rw [hX]; unfold lossE2; positivity
  unfold azumaMm at h
  rw [← hN, ← hX] at h
  have hq : 1 ≤ N ^ (4 * η / 16) := Real.one_le_rpow hN1 (by positivity)
  have hsX : Real.sqrt X ≤ N ^ (4 * η / 8 + 3 * ε) := by
    have hs0 := Real.sqrt_nonneg X
    have := le_mul_of_one_le_left (by positivity : 0 ≤ Real.sqrt X + 1) hq
    linarith
  have hsq : X ≤ (N ^ (4 * η / 8 + 3 * ε)) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg X) hsX 2
    rwa [Real.sq_sqrt hX0] at this
  have hpow : (N ^ (4 * η / 8 + 3 * ε)) ^ 2 = N ^ (6 * ε) * N ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have e : 2 * Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4)) *
      lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) *
        ((spectralM (E n)).im)⁻¹ = X / 4 := by
    rw [hX]; ring
  rw [e]
  linarith

/-- **`30000 e^{(log W)^{3/4}} + 2 ≤ N^η`**, eventually (from `azumaMm_le` at `ε = 0`). -/
private theorem StepBound_absorbΛ {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hsize : RBM.Ind.SizeTendsto d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      30000 * Real.exp (Real.log (d.W n) ^ ((3 : ℝ) / 4)) + 2 ≤ ((d.size n : ℕ) : ℝ) ^ η := by
  filter_upwards [azumaMm_le (d := d) hκ hE hsize (δ := 4 * η) (by positivity) le_rfl] with n h
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  have hEn : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  have hm0 := spectralM_im_pos hEn
  have hm1 := StepBound_im_le_one (E n)
  have hL1 : (1 : ℝ) ≤ (d.L n : ℝ) := by
    exact_mod_cast (by have := d.three_le_L n; omega : 1 ≤ d.L n)
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  set ℓ : ℝ := Real.log (d.W n) ^ ((3 : ℝ) / 4) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.rpow_nonneg (Real.log_nonneg hW1) _
  set K₀ : ℝ := 180 * 40002 ^ 2 * (1 + Real.log (d.L n)) with hK₀
  have hK₀1 : 1 ≤ K₀ := by
    have := Real.log_nonneg hL1
    rw [hK₀]; nlinarith
  set X : ℝ := 8 * (lossE2 (d.L n) (d.W n) (N ^ (0 : ℝ)) K₀ *
      Real.exp (2 * ℓ)) / (spectralM (E n)).im with hX
  have hX0 : 0 ≤ X := by rw [hX]; unfold lossE2; positivity
  unfold azumaMm at h
  rw [← hN, ← hK₀, ← hX] at h
  -- `(30002 e^ℓ)² ≤ X`
  have hloss : 10 ^ 12 * Real.exp (8 * ℓ) ≤ lossE2 (d.L n) (d.W n) (N ^ (0 : ℝ)) K₀ := by
    unfold lossE2
    rw [Real.rpow_zero, one_pow, mul_one]
    have hA : 1 ≤ (1 + Real.log ((d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12)) ^ 4 := by
      refine one_le_pow₀ ?_
      have := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (n := 2) hL1)
        (one_le_pow₀ (n := 12) hW1))
      linarith
    have hB : 1 ≤ (1 + Real.log (d.W n : ℝ)) ^ 3 := by
      refine one_le_pow₀ ?_
      have := Real.log_nonneg hW1
      linarith
    have hK2 : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK₀1
    have he : 0 < Real.exp (8 * ℓ) := Real.exp_pos _
    have h1 : 1 ≤ K₀ ^ 2 * (1 + Real.log ((d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12)) ^ 4 *
        (1 + Real.log (d.W n : ℝ)) ^ 3 := by
      have := mul_le_mul hK2 hA zero_le_one (by linarith)
      have := mul_le_mul this hB zero_le_one (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 10 ^ 12 * Real.exp (8 * ℓ))
    calc 10 ^ 12 * Real.exp (8 * ℓ) = 10 ^ 12 * Real.exp (8 * ℓ) * 1 := by ring
      _ ≤ 10 ^ 12 * Real.exp (8 * ℓ) * (K₀ ^ 2 * (1 + Real.log ((d.L n : ℝ) ^ 2 *
          (d.W n : ℝ) ^ 12)) ^ 4 * (1 + Real.log (d.W n : ℝ)) ^ 3) := this
      _ = _ := by ring
  have hXge : (30002 * Real.exp ℓ) ^ 2 ≤ X := by
    have h2 : Real.exp (2 * ℓ) ≤ Real.exp (10 * ℓ) := Real.exp_le_exp.2 (by linarith)
    have hsq : (Real.exp ℓ) ^ 2 = Real.exp (2 * ℓ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h10 : Real.exp (8 * ℓ) * Real.exp (2 * ℓ) = Real.exp (10 * ℓ) := by
      rw [← Real.exp_add]; ring_nf
    have hXm : 8 * (10 ^ 12 * Real.exp (10 * ℓ)) ≤ X := by
      rw [hX, le_div_iff₀ hm0]
      have h8 : 8 * (10 ^ 12 * Real.exp (8 * ℓ) * Real.exp (2 * ℓ)) ≤
          8 * (lossE2 (d.L n) (d.W n) (N ^ (0 : ℝ)) K₀ * Real.exp (2 * ℓ)) := by
        have := mul_le_mul_of_nonneg_right hloss (Real.exp_pos (2 * ℓ)).le
        linarith
      rw [← h10]
      have hE10 : 0 ≤ 8 * (10 ^ 12 * (Real.exp (8 * ℓ) * Real.exp (2 * ℓ))) := by positivity
      have := mul_le_mul_of_nonneg_left hm1 hE10
      linarith
    rw [mul_pow, hsq]
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 30002 ^ 2)
    have h4 : (30002 : ℝ) ^ 2 * Real.exp (10 * ℓ) ≤ 8 * (10 ^ 12 * Real.exp (10 * ℓ)) := by
      have := (Real.exp_pos (10 * ℓ)).le
      have h5 := mul_le_mul_of_nonneg_right (by norm_num : (30002 : ℝ) ^ 2 ≤ 8 * 10 ^ 12) this
      linarith
    linarith
  have hsX : 30002 * Real.exp ℓ ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hXge
  have hq : 1 ≤ N ^ (4 * η / 16) := Real.one_le_rpow hN1 (by positivity)
  have hs0 := Real.sqrt_nonneg X
  have h2 : Real.sqrt X ≤ N ^ (4 * η / 8 + 3 * 0) := by
    have := le_mul_of_one_le_left (by positivity : 0 ≤ Real.sqrt X + 1) hq
    linarith
  have h3 : N ^ (4 * η / 8 + 3 * 0) ≤ N ^ η :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hΛ1 : 1 ≤ Real.exp ℓ := Real.one_le_exp hℓ0
  linarith


variable {d} in
/-- **The eventual environment** (adapted from the private `GoodEventGrid_env`,
`RBM2D/Path/GoodEventGrid.lean`): `4 ≤ log W`; the `E2Hyp` floor; `Θ ≤ W` on the window; the
step condition at `n`; `kellStarEv` at `δ = 1/8` for `Θ` (level `D`) and for `𝒰` (level
`D + 3/c + 1`); the far-cost inequality `16 L⁶ W⁶ W^{-(D+3/c+1)} ≤ W^{-D}`; `η_u⁻¹ ≤ N` for
`u ≤ t_n`; `10⁷ ≤ N`. -/
private theorem StepBound_env {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    {s t : ℕ → ℝ} {c τ' δ D : ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hc : 0 < c)
    (hband : Bandwidth d c) (hτ' : 0 < τ') (hrange : RangeCond d τ' t)
    (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d) (hδc : δ ≤ c / 200)
    (hD : 20 + 2 / c ≤ D) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log (d.W n : ℝ) ∧
      (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12 ≤ (d.W n : ℝ) ^ (D / 2) ∧
      (∀ u : ℝ, s n ≤ u → u ≤ t n → thr d E s δ n u ≤ (d.W n : ℝ)) ∧
      (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ ((1 - t n) / (1 - s n)) ^ 30 ∧
      (∀ s' u : ℝ, 0 ≤ s' → s' ≤ u → u ≤ t n → ∀ a b : Z2 (d.L n),
        1 / 8 * ellStar (d.L n) (d.W n) u ≤ (zdist2 (d.L n) (a - b) : ℝ) →
          ‖Theta (d.L n) (u : ℂ) a b‖ ≤ (d.W n : ℝ) ^ (-D)) ∧
      (∀ s' u : ℝ, 0 ≤ s' → s' ≤ u → u ≤ t n → ∀ a b : Z2 (d.L n),
        1 / 8 * ellStar (d.L n) (d.W n) u ≤ (zdist2 (d.L n) (a - b) : ℝ) →
          ‖ukerMat (d.L n) 1 s' u a b‖ ≤ (d.W n : ℝ) ^ (-(D + 3 / c + 1))) ∧
      16 * (d.L n : ℝ) ^ 6 * (d.W n : ℝ) ^ 6 * (d.W n : ℝ) ^ (-(D + 3 / c + 1)) ≤
        (d.W n : ℝ) ^ (-D) ∧
      (∀ u : ℝ, u ≤ t n → (etaT (E n) u)⁻¹ ≤ ((d.size n : ℕ) : ℝ)) ∧
      (10 : ℝ) ^ 7 ≤ ((d.size n : ℕ) : ℝ) := by
  have hE' : ∀ n, |E n| < 2 := fun n => lt_of_le_of_lt (hE n) (by linarith)
  have hT : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.1 hsize
  have hK1 := kellStarEv d c τ' (1 / 8) D t hc hτ' (by norm_num) hT hband hrange ht1
  have hK2 := kellStarEv d c τ' (1 / 8) (D + 3 / c + 1) t hc hτ' (by norm_num) hT hband hrange ht1
  have hNc : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp hsize
  have hWtop : Tendsto (fun n => (d.W n : ℝ)) atTop atTop := tendsto_atTop_mono' _ hband hNc
  have hlog : ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log (d.W n : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtop).eventually_ge_atTop 4
  obtain ⟨hcκ0, -⟩ := StepBound_im_ge hκ hE 0
  set cκ : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hcκ
  have hbig : ∀ᶠ n : ℕ in atTop, cκ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ τ' :=
    ((tendsto_rpow_atTop hτ').comp hsize).eventually (eventually_ge_atTop cκ⁻¹)
  have hN7 : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ^ 7 ≤ ((d.size n : ℕ) : ℝ) :=
    hsize.eventually_ge_atTop _
  filter_upwards [hlog, hband, thr_le_W hE' hst ht1 hc hband hstep hδc, hstep, hK1, hK2, hrange,
    hbig, hN7] with n hlogn hB hthr hS hk1 hk2 hR hbign hN7n
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hNeq : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hNW : ((d.size n : ℕ) : ℝ) ≤ (d.W n : ℝ) ^ (1 / c) := by
    have h1 : (((d.size n : ℕ) : ℝ) ^ c) ^ (1 / c) ≤ (d.W n : ℝ) ^ (1 / c) :=
      Real.rpow_le_rpow (by positivity) hB (by positivity)
    rwa [← Real.rpow_mul hN0, mul_one_div_cancel hc.ne', Real.rpow_one] at h1
  refine ⟨hlogn, ?_, hthr, hS, fun s' u h0 h1 h2 a b hab => (hk1 s' u h0 h1 h2 a b hab).1,
    fun s' u h0 h1 h2 a b hab => (hk2 s' u h0 h1 h2 a b hab).2, ?_, ?_, hN7n⟩
  · -- the `E2Hyp` floor
    have hexp : 1 / c + 10 ≤ D / 2 := by
      have : 2 / c = 2 * (1 / c) := by ring
      linarith
    calc (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 12 = ((d.size n : ℕ) : ℝ) * (d.W n : ℝ) ^ (10 : ℝ) := by
          rw [hNeq, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      _ ≤ (d.W n : ℝ) ^ (1 / c) * (d.W n : ℝ) ^ (10 : ℝ) :=
          mul_le_mul_of_nonneg_right hNW (by positivity)
      _ = (d.W n : ℝ) ^ (1 / c + 10) := (Real.rpow_add hW0 _ _).symm
      _ ≤ (d.W n : ℝ) ^ (D / 2) := Real.rpow_le_rpow_of_exponent_le hW1 hexp
  · -- the far cost
    have h16 : (16 : ℝ) ≤ (d.W n : ℝ) := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have he4 : (16 : ℝ) ≤ Real.exp 4 := by
        have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      calc (16 : ℝ) ≤ Real.exp 4 := he4
        _ ≤ Real.exp (Real.log (d.W n : ℝ)) := Real.exp_le_exp.2 hlogn
        _ = (d.W n : ℝ) := Real.exp_log hW0
    have hN3 : ((d.size n : ℕ) : ℝ) ^ 3 ≤ (d.W n : ℝ) ^ (3 / c) := by
      calc ((d.size n : ℕ) : ℝ) ^ 3 ≤ ((d.W n : ℝ) ^ (1 / c)) ^ 3 := pow_le_pow_left₀ hN0 hNW 3
        _ = (d.W n : ℝ) ^ (3 / c) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have e6 : (d.L n : ℝ) ^ 6 * (d.W n : ℝ) ^ 6 = ((d.size n : ℕ) : ℝ) ^ 3 := by
      rw [hNeq]; ring
    have hWpos : 0 < (d.W n : ℝ) ^ (-(D + 3 / c + 1)) := Real.rpow_pos_of_pos hW0 _
    calc 16 * (d.L n : ℝ) ^ 6 * (d.W n : ℝ) ^ 6 * (d.W n : ℝ) ^ (-(D + 3 / c + 1))
        = 16 * ((d.L n : ℝ) ^ 6 * (d.W n : ℝ) ^ 6) * (d.W n : ℝ) ^ (-(D + 3 / c + 1)) := by ring
      _ ≤ (d.W n : ℝ) * (d.W n : ℝ) ^ (3 / c) * (d.W n : ℝ) ^ (-(D + 3 / c + 1)) := by
          rw [e6]
          exact mul_le_mul_of_nonneg_right (mul_le_mul h16 hN3 (by positivity) hW0.le)
            hWpos.le
      _ = (d.W n : ℝ) ^ ((1 : ℝ) + 3 / c + -(D + 3 / c + 1)) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
      _ = (d.W n : ℝ) ^ (-D) := by congr 1; ring
  · -- `η_u⁻¹ ≤ N`
    intro u hut
    have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
    have hWn : 1 ≤ d.W n := d.W_pos n
    have hm := (StepBound_im_ge hκ hE n).2
    have hm0 : 0 < (spectralM (E n)).im := lt_of_lt_of_le hcκ0 hm
    obtain ⟨-, hη⟩ := scaleM_etaT_of_range hL1 hWn (hE' n) hc hτ' (ht1 n) hB hR
    have hηt : 0 < etaT (E n) (t n) := etaT_pos (hE' n) (ht1 n)
    have hηu : etaT (E n) (t n) ≤ etaT (E n) u := by
      unfold etaT; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    have h1 : (etaT (E n) u)⁻¹ ≤ (etaT (E n) (t n))⁻¹ := inv_anti₀ hηt hηu
    have hNsq : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = ((d.size n : ℕ) : ℝ) := rfl
    rw [hNsq] at hη
    have h2 : ((d.size n : ℕ) : ℝ) ^ (1 - τ') / (spectralM (E n)).im ≤
        ((d.size n : ℕ) : ℝ) ^ (1 - τ') * cκ⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hcκ0 hm) (Real.rpow_nonneg hN0 _)
    have h3 : ((d.size n : ℕ) : ℝ) ^ (1 - τ') * cκ⁻¹ ≤
        ((d.size n : ℕ) : ℝ) ^ (1 - τ') * ((d.size n : ℕ) : ℝ) ^ τ' :=
      mul_le_mul_of_nonneg_left hbign (Real.rpow_nonneg hN0 _)
    have h4 : ((d.size n : ℕ) : ℝ) ^ (1 - τ') * ((d.size n : ℕ) : ℝ) ^ τ' =
        ((d.size n : ℕ) : ℝ) := by
      rw [← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]
    linarith


/-! ## 7. The remainder -/

variable {d} in
/-- **The remainder sum** at the stopping index: each `R_j` is transported by `sumNdecayEta`
(`(η_{u_{j+1}}/η_{u_τ})² ≤ N²`), `envConst(2) + 7 N η⁻⁴ ≤ 640007 N^{10}` once `η⁻¹ ≤ N`, and
`τ Δ ≤ 1`. -/
private theorem StepBound_rem {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n τ : ℕ} {ω : PathΩ d}
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hτK : τ ≤ K n)
    (hη : ∀ u : ℝ, u ≤ v n → (etaT (E n) u)⁻¹ ≤ ((d.size n : ℕ) : ℝ))
    (hR : ∀ j < τ, ∀ b : Z2 (d.L n) × Z2 (d.L n), ‖Rgrid d (E n) s v K n j ω b‖ ≤
      (envConst (d.L n) (d.W n) (E n) 2 (gridTime s v K n (j + 1))
          + 7 * (Sizes.size d n : ℝ) * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 4)
        * gridStep s v K n ^ ((3 : ℝ) / 2))
    (a : Z2 (d.L n) × Z2 (d.L n)) :
    ‖(∑ j ∈ Finset.range τ,
        Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
          (gridTime s v K n τ) (Rgrid d (E n) s v K n j ω)) a‖ ≤
      640007 * ((d.size n : ℕ) : ℝ) ^ 12 * gridStep s v K n ^ ((1 : ℝ) / 2) := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s v K n with hΔ
  have hΔ0 : 0 ≤ Δ := GoodEvent_gridStep_nonneg hsv
  have hm0 := spectralM_im_pos hE
  have hm1 := StepBound_im_le_one (E n)
  have hL3 := d.three_le_L n
  have hτv : gridTime s v K n τ ≤ v n := GoodEvent_gridTime_le hsv hτK
  have hτ1 : gridTime s v K n τ < 1 := hτv.trans_lt hv1
  -- `τ Δ ≤ 1`
  have hτΔ : (τ : ℝ) * Δ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (K n) with hK0 | hKpos
    · have : τ = 0 := by omega
      subst this; simp
    · have hKR : (0 : ℝ) < K n := by exact_mod_cast hKpos
      have hτR : (τ : ℝ) ≤ K n := by exact_mod_cast hτK
      have hv : v n - s n ≤ 1 := by linarith
      calc (τ : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hτR hΔ0
        _ = v n - s n := by rw [hΔ]; unfold gridStep; field_simp
        _ ≤ 1 := hv
  -- the uniform bound on each `R_j`
  have hB : ∀ j < τ, ∀ b, ‖Rgrid d (E n) s v K n j ω b‖ ≤ 640007 * N ^ 10 * Δ ^ ((3 : ℝ) / 2) := by
    intro j hj b
    refine (hR j hj b).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΔ0 _))
    have hu : gridTime s v K n (j + 1) ≤ v n := GoodEvent_gridTime_le hsv (by omega)
    have hηj := hη _ hu
    have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ :=
      inv_nonneg.2 (etaT_pos hE (hu.trans_lt hv1)).le
    have hsz : (Sizes.size d n : ℝ) = N := rfl
    have henv : envConst (d.L n) (d.W n) (E n) 2 (gridTime s v K n (j + 1)) ≤ 640000 * N ^ 10 := by
      unfold envConst
      have hNsq : ((((d.W n * d.L n) ^ 2 : ℕ)) : ℝ) = N := rfl
      rw [hNsq]
      have h1 : 1 + (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ 2 * N := by linarith
      have h2 : (1 + (etaT (E n) (gridTime s v K n (j + 1)))⁻¹) ^ (2 + 4) ≤ (2 * N) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h1 _
      have h3 : 16 * (((2 : ℕ) : ℝ) + 3) ^ 4 * N ^ 4 *
          (1 + (etaT (E n) (gridTime s v K n (j + 1)))⁻¹) ^ (2 + 4) ≤
          16 * (((2 : ℕ) : ℝ) + 3) ^ 4 * N ^ 4 * (2 * N) ^ 6 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc _ ≤ 16 * (((2 : ℕ) : ℝ) + 3) ^ 4 * N ^ 4 * (2 * N) ^ 6 := h3
        _ = 640000 * N ^ 10 := by push_cast; ring
    have h7 : 7 * (Sizes.size d n : ℝ) * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 4 ≤
        7 * N ^ 10 := by
      rw [hsz]
      have h4 : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ hη0 hηj 4
      have h5 : N * N ^ 4 ≤ N ^ 10 := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ hN1 (by norm_num)
      have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 7 * N)
      nlinarith
    linarith
  -- the transport of each `R_j`
  have hU : ∀ j < τ, ‖Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
      (gridTime s v K n (j + 1)) (gridTime s v K n τ) (Rgrid d (E n) s v K n j ω) a‖ ≤
      N ^ 2 * (640007 * N ^ 10 * Δ ^ ((3 : ℝ) / 2)) := by
    intro j hj
    have hj0 : 0 ≤ gridTime s v K n (j + 1) := GoodEvent_gridTime_nonneg hs0 hsv _
    have hjτ : gridTime s v K n (j + 1) ≤ gridTime s v K n τ := GoodEvent_gridTime_mono hsv hj
    have h := sumNdecayEta (d.L n) hL3 (E n) _ _ hE hj0 hjτ hτ1 _ _ (hB j hj) a
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hηj : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hE (hjτ.trans_lt hτ1)
    have hητ : 0 < etaT (E n) (gridTime s v K n τ) := etaT_pos hE hτ1
    have hle1 : etaT (E n) (gridTime s v K n (j + 1)) ≤ 1 := by
      unfold etaT
      have : 1 - gridTime s v K n (j + 1) ≤ 1 := by linarith
      calc (1 - gridTime s v K n (j + 1)) * (spectralM (E n)).im ≤ 1 * 1 :=
            mul_le_mul this hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hr : etaT (E n) (gridTime s v K n (j + 1)) / etaT (E n) (gridTime s v K n τ) ≤ N := by
      rw [div_eq_mul_inv]
      calc etaT (E n) (gridTime s v K n (j + 1)) * (etaT (E n) (gridTime s v K n τ))⁻¹
          ≤ 1 * N := mul_le_mul hle1 (hη _ hτv) (inv_nonneg.2 hητ.le) zero_le_one
        _ = N := one_mul N
    exact pow_le_pow_left₀ (div_nonneg hηj.le hητ.le) hr 2
  rw [Finset.sum_apply]
  calc ‖∑ j ∈ Finset.range τ, Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
        (gridTime s v K n (j + 1)) (gridTime s v K n τ) (Rgrid d (E n) s v K n j ω) a‖
      ≤ ∑ j ∈ Finset.range τ, ‖Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
        (gridTime s v K n (j + 1)) (gridTime s v K n τ) (Rgrid d (E n) s v K n j ω) a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range τ, N ^ 2 * (640007 * N ^ 10 * Δ ^ ((3 : ℝ) / 2)) :=
        Finset.sum_le_sum fun j hj => hU j (Finset.mem_range.1 hj)
    _ = 640007 * N ^ 12 * ((τ : ℝ) * Δ) * Δ ^ ((1 : ℝ) / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : Δ ^ ((3 : ℝ) / 2) = Δ * Δ ^ ((1 : ℝ) / 2) := by
          rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num]
          rcases hΔ0.eq_or_lt with h0 | hpos
          · rw [← h0, Real.zero_rpow (by norm_num), zero_mul]
          · rw [Real.rpow_add hpos, Real.rpow_one]
        rw [this]; ring
    _ ≤ 640007 * N ^ 12 * 1 * Δ ^ ((1 : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτΔ (by positivity))
          (Real.rpow_nonneg hΔ0 _)
    _ = 640007 * N ^ 12 * Δ ^ ((1 : ℝ) / 2) := by ring


/-! ## 8. The crude drift bound -/

/-- **The crude max-norm of the drift vector** `D_j = 𝓔^{LK×LK} + 𝓔^{(G̃)}` at `u_j`, from
`lemDecCalE_lk`, `lemDecCalE_wG` (with `v = u_τ`), `𝒯_v ≤ 2`, `M_u ≥ 1`, `J* ≤ W`,
`ρ ≤ L`, `η_u⁻¹ ≤ N`, `W², L² ≤ N`: `≤ 6 lossE2 N⁴` (input of the correction). -/
private theorem StepBound_Dbound (L W : ℕ) [NeZero L] [NeZero W] {E s u v D Λ K₀ N : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hE2 : E2Hyp L W E s u v D Λ K₀ M) (hD : 0 ≤ D)
    (hηN : (etaT E u)⁻¹ ≤ N) (hWN : (W : ℝ) ^ 2 ≤ N) (hLN : (L : ℝ) ^ 2 ≤ N) (hN1 : 1 ≤ N)
    (b : Z2 L × Z2 L) :
    ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖ ≤ 6 * lossE2 L W Λ K₀ * N ^ 4 := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, -, -, hlogW, -, hMv, -, hJW, -, -⟩ := id hE2
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s < 1 := hsu.trans_lt hu1
  have h1 := lemDecCalE_lk L W E s u v D Λ K₀ M hE2 b.1 b.2
  have h2 := lemDecCalE_wG L W E s u v D Λ K₀ M hE2 b.1 b.2
  set ℓ := lossE2 L W Λ K₀ with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; unfold lossE2; positivity
  set e := (etaT E u)⁻¹ with he
  have he0 : 0 ≤ e := inv_nonneg.2 (etaT_pos hE hu1).le
  have hMu1 : 1 ≤ scaleM L W E u := hMv.trans (scaleM_anti_ratio (W := W) hL1 hE huv hv1).1
  set Mi := (scaleM L W E u)⁻¹ with hMi
  have hMi0 : 0 ≤ Mi := inv_nonneg.2 (by linarith)
  have hMi1 : Mi ≤ 1 := inv_le_one_of_one_le₀ hMu1
  set Mh := Mi ^ ((1 : ℝ) / 2) with hMh
  have hMh0 : 0 ≤ Mh := Real.rpow_nonneg hMi0 _
  have hMh1 : Mh ≤ 1 := Real.rpow_le_one hMi0 hMi1 (by norm_num)
  set J := jStarMat L W E D u M with hJ
  have hJ0 : 0 ≤ J := zero_le_one.trans (one_le_jStarMat L W hW1 E D u M)
  have hJ2 : J ^ 2 ≤ N := (pow_le_pow_left₀ hJ0 hJW 2).trans hWN
  have hJ20 : 0 ≤ J ^ 2 := sq_nonneg _
  set ρ := ellT L u / ellT L s with hρ
  have hℓs : 1 ≤ ellT L s := one_le_ellT hL1 hs0 hs1
  have hℓu := ellT_pos_le hL1 hu1
  have hρ0 : 0 ≤ ρ := div_nonneg hℓu.1.le (by linarith)
  have hρL : ρ ≤ L := by
    rw [hρ, div_le_iff₀ (by linarith)]
    calc ellT L u ≤ L := hℓu.2
      _ = L * 1 := (mul_one _).symm
      _ ≤ L * ellT L s := mul_le_mul_of_nonneg_left hℓs (Nat.cast_nonneg L)
  have hρ2 : ρ ^ 2 ≤ N := (pow_le_pow_left₀ hρ0 hρL 2).trans hLN
  have hρ6 : ρ ^ 6 ≤ N ^ 3 := by
    have : ρ ^ 6 = (ρ ^ 2) ^ 3 := by ring
    rw [this]; exact pow_le_pow_left₀ (sq_nonneg _) hρ2 3
  set χ : ℝ := if (zdist2 L (b.1 - b.2) : ℝ) ≤ ellStar L W u then 1 else 0 with hχ
  have hχ0 : 0 ≤ χ := by rw [hχ]; split_ifs <;> norm_num
  have hχ1 : χ ≤ 1 := by rw [hχ]; split_ifs <;> norm_num
  set T := tailT L W E D v (zdist2 L (b.1 - b.2) : ℝ) with hT
  have hT0 : 0 ≤ T := (tailT_pos hW1 L E D v _).le
  have hT2 : T ≤ 2 := by
    rw [hT]; unfold tailT
    have hMv0 : 0 < scaleM L W E v := by linarith
    have hMv2 : (scaleM L W E v ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hMv)
    have hex : Real.exp (-Real.sqrt ((zdist2 L (b.1 - b.2) : ℝ) / ellT L v)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
    have hWD : (W : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
    have h0 : 0 ≤ (scaleM L W E v ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have := mul_le_mul hMv2 hex (Real.exp_pos _).le zero_le_one
    linarith
  have hN0 : 0 ≤ N := by linarith
  have hA : e * Mi * J ^ 2 ≤ N * 1 * N :=
    mul_le_mul (mul_le_mul hηN hMi1 hMi0 hN0) hJ2 hJ20 (by positivity)
  have hB : e * (ρ ^ 6 * χ + ρ ^ 2 * Mh * J ^ 2) ≤ N * (N ^ 3 * 1 + N * 1 * N) := by
    refine mul_le_mul hηN (add_le_add (mul_le_mul hρ6 hχ1 hχ0 (by positivity))
      (mul_le_mul (mul_le_mul hρ2 hMh1 hMh0 hN0) hJ2 hJ20 (by positivity))) ?_ hN0
    positivity
  have h1' : ‖ELKLK L W E u M b.1 b.2‖ ≤ ℓ * (N * 1 * N) * 2 := by
    refine h1.trans ?_
    have : 0 ≤ e * Mi * J ^ 2 := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA hℓ0) hT2 hT0 (by positivity)
  have h2' : ‖EGt L W E u M b.1 b.2‖ ≤ ℓ * (N * (N ^ 3 * 1 + N * 1 * N)) * 2 := by
    refine h2.trans ?_
    have : 0 ≤ e * (ρ ^ 6 * χ + ρ ^ 2 * Mh * J ^ 2) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB hℓ0) hT2 hT0 (by positivity)
  have hN24 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN34 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have e1 : ℓ * (N * 1 * N) * 2 = 2 * ℓ * N ^ 2 := by ring
  have e2 : ℓ * (N * (N ^ 3 * 1 + N * 1 * N)) * 2 = 2 * ℓ * N ^ 4 + 2 * ℓ * N ^ 3 := by ring
  have h3 := mul_le_mul_of_nonneg_left hN24 (by positivity : (0 : ℝ) ≤ 2 * ℓ)
  have h4 := mul_le_mul_of_nonneg_left hN34 (by positivity : (0 : ℝ) ≤ 2 * ℓ)
  calc ‖ELKLK L W E u M b.1 b.2 + EGt L W E u M b.1 b.2‖
      ≤ ‖ELKLK L W E u M b.1 b.2‖ + ‖EGt L W E u M b.1 b.2‖ := norm_add_le _ _
    _ ≤ 6 * ℓ * N ^ 4 := by linarith


/-! ## 9. The charge -/

/-- **The term-by-term charge**: the five parts plus the correction, each charged to one term of
`GridStepBoundPT`. -/
private theorem StepBound_core {LHS I Zb Yb Drb Corr Rem T Nη Λ X1 X4 Az r52 χ χ5 χ3 X5 X6 Q e6 r3 X7
      X8 tail : ℝ}
    (hLHS : LHS ≤ I + Zb + Yb + Drb + Rem)
    (hI : I ≤ (Λ + 1) * X1 * χ * T + 30000 * Λ * X4 * T + 2 * tail)
    (hZ : Zb ≤ Az * (r52 * χ5 + X5 + X6 + 1) * T) (hY : Yb ≤ T)
    (hDr : Drb ≤ Q * (X7 / 6 + X8 / 7 + χ3 * r3) * T + Corr)
    (hCorr : Corr ≤ e6 * X7 * T) (hRem : Rem ≤ T)
    (hΛ : 30000 * Λ + 2 ≤ Nη) (hΛ1 : 1 ≤ Λ) (hQ : Q ≤ e6 * Nη / 4)
    (hχ5 : χ5 ≤ χ) (hχ3 : χ3 ≤ χ)
    (hT : 0 ≤ T) (hX1 : 0 ≤ X1) (hX4 : 0 ≤ X4) (hAz : 0 ≤ Az) (hr52 : 0 ≤ r52)
    (hχ30 : 0 ≤ χ3) (hX5 : 0 ≤ X5) (hX6 : 0 ≤ X6) (he6 : 0 ≤ e6)
    (hr3 : 0 ≤ r3) (hX7 : 0 ≤ X7) (hX8 : 0 ≤ X8) (htail : 0 ≤ tail) :
    LHS ≤ Nη * ((X1 + Az * r52 + e6 * r3) * χ + X4 + Az * (X5 + X6 + 1) + 3 +
        e6 * (X7 + X8)) * T + Nη * tail := by
  have hχ0 : 0 ≤ χ := hχ30.trans hχ3
  have hN1 : 1 ≤ Nη := by linarith
  have hN2 : 2 ≤ Nη := by linarith
  have h1 : (Λ + 1) * (X1 * χ * T) ≤ Nη * (X1 * χ * T) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (mul_nonneg hX1 hχ0) hT)
  have h2a : Az * r52 * χ5 * T ≤ Az * r52 * χ * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχ5 (mul_nonneg hAz hr52)) hT
  have h2b : 1 * (Az * r52 * χ * T) ≤ Nη * (Az * r52 * χ * T) :=
    mul_le_mul_of_nonneg_right hN1 (mul_nonneg (mul_nonneg (mul_nonneg hAz hr52) hχ0) hT)
  have h3a : Q * (χ3 * r3 * T) ≤ (e6 * Nη / 4) * (χ3 * r3 * T) :=
    mul_le_mul_of_nonneg_right hQ (mul_nonneg (mul_nonneg hχ30 hr3) hT)
  have h3b : (e6 * Nη / 4) * (χ3 * r3 * T) ≤ (e6 * Nη / 4) * (χ * r3 * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hχ3 hr3) hT) (by positivity)
  have h3c : 0 ≤ e6 * Nη * (χ * r3 * T) := by
    have : 0 ≤ Nη := by linarith
    positivity
  have h4 : (30000 * Λ) * (X4 * T) ≤ Nη * (X4 * T) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hX4 hT)
  have h5 : 1 * (Az * (X5 + X6 + 1) * T) ≤ Nη * (Az * (X5 + X6 + 1) * T) :=
    mul_le_mul_of_nonneg_right hN1 (mul_nonneg (mul_nonneg hAz (by linarith)) hT)
  have h6 : 2 * T ≤ 3 * Nη * T := mul_le_mul_of_nonneg_right (by linarith) hT
  have h7a : Q * (X7 * T) ≤ (e6 * Nη / 4) * (X7 * T) :=
    mul_le_mul_of_nonneg_right hQ (mul_nonneg hX7 hT)
  have h7b : Q * (X8 * T) ≤ (e6 * Nη / 4) * (X8 * T) :=
    mul_le_mul_of_nonneg_right hQ (mul_nonneg hX8 hT)
  have h7c : 2 * (e6 * (X7 * T)) ≤ Nη * (e6 * (X7 * T)) :=
    mul_le_mul_of_nonneg_right hN2 (mul_nonneg he6 (mul_nonneg hX7 hT))
  have h7d : 0 ≤ Nη * (e6 * (X7 * T)) := by
    have : 0 ≤ Nη := by linarith
    positivity
  have h7e : 0 ≤ Nη * (e6 * (X8 * T)) := by
    have : 0 ≤ Nη := by linarith
    positivity
  have h8 : 2 * tail ≤ Nη * tail := mul_le_mul_of_nonneg_right hN2 htail
  have hQX : Q * (X7 / 6 + X8 / 7 + χ3 * r3) * T =
      Q * (X7 * T) / 6 + Q * (X8 * T) / 7 + Q * (χ3 * r3 * T) := by ring
  rw [hQX] at hDr
  nlinarith


/-! ## 10. Numeric helpers of the assembly -/

/-- `N^{-D/2} ≤ W^{-D}` from `W² ≤ N`. -/
private theorem StepBound_Wpow {W N D : ℝ} (hW : 1 ≤ W) (hWN : W ^ 2 ≤ N) (hD : 0 ≤ D) :
    N ^ (-(D / 2)) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have e : W ^ (-D) = (W ^ 2) ^ (-(D / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  rw [e]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hWN (by linarith)

/-- `C N^a ≤ 1` for `N ≥ 10⁷`, `a ≤ -1`, `C ≤ 10⁷`. -/
private theorem StepBound_small {N a C : ℝ} (hN : 10 ^ 7 ≤ N) (ha : a ≤ -1)
    (hC : C ≤ 10 ^ 7) : C * N ^ a ≤ 1 := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : N ^ a ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 ha
  rw [Real.rpow_neg_one] at h1
  have h2 : N⁻¹ ≤ (10 ^ 7)⁻¹ := inv_anti₀ (by norm_num) hN
  have h3 : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le _
  calc C * N ^ a ≤ 10 ^ 7 * (10 ^ 7 : ℝ)⁻¹ := mul_le_mul hC (h1.trans h2) h3 (by norm_num)
    _ = 1 := by norm_num

/-- The numeric step of the transport-start correction: `x² (Δ 2yα + 3Δ²z²α) ≤ 5 N⁴ Δ α`. -/
private theorem StepBound_corr_num {N Δ α x y z : ℝ} (hN1 : 1 ≤ N) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hα : 0 ≤ α) (hx0 : 0 ≤ x) (hx : x ≤ N) (hy0 : 0 ≤ y) (hy : y ≤ N) (hz0 : 0 ≤ z)
    (hz : z ≤ N) :
    x ^ 2 * (Δ * (2 * y * α) + 3 * Δ ^ 2 * z ^ 2 * α) ≤ 5 * N ^ 4 * Δ * α := by
  have hx2 : x ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hz2 : z ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have hΔ2 : Δ ^ 2 ≤ Δ := by nlinarith
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hyN : y ≤ N ^ 2 := hy.trans hNN
  have h1 : Δ * (2 * y * α) ≤ Δ * (2 * N ^ 2 * α) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hα) hΔ0
  have h2 : Δ ^ 2 * z ^ 2 ≤ Δ * N ^ 2 := mul_le_mul hΔ2 hz2 (sq_nonneg _) hΔ0
  have h2' : 3 * (Δ ^ 2 * z ^ 2) * α ≤ 3 * (Δ * N ^ 2) * α :=
    mul_le_mul_of_nonneg_right (by linarith) hα
  have hin : Δ * (2 * y * α) + 3 * Δ ^ 2 * z ^ 2 * α ≤ 5 * N ^ 2 * Δ * α := by
    have e1 : 3 * Δ ^ 2 * z ^ 2 * α = 3 * (Δ ^ 2 * z ^ 2) * α := by ring
    have e2 : 5 * N ^ 2 * Δ * α = Δ * (2 * N ^ 2 * α) + 3 * (Δ * N ^ 2) * α := by ring
    rw [e1, e2]; linarith
  have hin0 : 0 ≤ Δ * (2 * y * α) + 3 * Δ ^ 2 * z ^ 2 * α := by positivity
  calc x ^ 2 * (Δ * (2 * y * α) + 3 * Δ ^ 2 * z ^ 2 * α) ≤ N ^ 2 * (5 * N ^ 2 * Δ * α) :=
        mul_le_mul hx2 hin hin0 (by positivity)
    _ = 5 * N ^ 4 * Δ * α := by ring


/-- The window indicators are monotone in the window constant. -/
private theorem StepBound_ind_mono {x y k k' : ℝ} (hy : 0 ≤ y) (hk : k ≤ k') :
    (if x ≤ k * y then (1 : ℝ) else 0) ≤ (if x ≤ k' * y then 1 else 0) := by
  have hky : k * y ≤ k' * y := mul_le_mul_of_nonneg_right hk hy
  by_cases h1 : x ≤ k * y
  · have h2 : x ≤ k' * y := h1.trans hky
    simp only [h1, h2, ite_true, le_refl]
  · simp only [h1, ite_false]
    split_ifs <;> norm_num

/-! ## 11. The result -/

/-- **`gridStepBoundPT`**.  Proof: the a.e. expansion `grid_expansion_all'` at `k = τ` with the
remainder bounds of `Expansion_condExp_A_succ_rpow` (countably many `j`, `ae_all_iff`); on the
good event, `goodEvent_grid_imp` gives the initial, `Z`, `Y` and stopping data; the five parts are
bounded by `StepBound_init`, the `Z` and `Y` items, `StepBound_driftSum` (with the correction
`StepBound_corr`) and `StepBound_rem`, and charged to the terms of `GridStepBoundPT` by
`StepBound_core`. -/
theorem gridStepBoundPT : GridStepBoundPT d := by
  intro κ c τ' E s v t δ D ε D' Cc Cx hκ hE hs0 hsv hvt ht1 hc hband hτ' hrange hstep hsize
    hδ hδc hD hε hD' hCc hCx D₁ hD₁ η hη
  have hst : ∀ n, s n ≤ t n := fun n => (hsv n).trans (hvt n)
  have hE' : ∀ n, |E n| < 2 := fun n => lt_of_le_of_lt (hE n) (by linarith)
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hD0 : 0 ≤ D := by
    have : 0 < 2 / c := by positivity
    linarith
  have hK0 : ∀ m, gridK d D (D₁ + 1) m ≠ 0 := fun m => gridK_ne_zero D (D₁ + 1) m
  filter_upwards [goodEvent_grid_imp hκ hE hs0 hsv hvt ht1 hc hband hτ'.le hrange hstep hsize
      hδ hD0 hε.le hD' hCc hCx D₁ hD₁,
    StepBound_env hκ hE hst ht1 hc hband hτ' hrange hstep hsize hδc hD,
    StepBound_absorb d hκ hE hsize hε.le hη, StepBound_absorb d hκ hE hsize hε.le one_pos,
    StepBound_absorbΛ d hκ hE hsize hη] with n hG hEnv hQ hQ1 hΛ
  obtain ⟨⟨-, hΔCK, hAz0, -⟩, hGω⟩ := hG
  obtain ⟨hlogW, hfloor, hthr, hS, hThfar, hUfar, hfl16, hηN, hN7⟩ := hEnv
  have hRae : ∀ᵐ ω ∂(pathP d), ∀ j, j < gridK d D (D₁ + 1) n →
      ∀ b : Z2 (d.L n) × Z2 (d.L n),
      ‖Rgrid d (E n) s v (gridK d D (D₁ + 1)) n j ω b‖ ≤
        (envConst (d.L n) (d.W n) (E n) 2 (gridTime s v (gridK d D (D₁ + 1)) n (j + 1))
            + 7 * (Sizes.size d n : ℝ) *
              (etaT (E n) (gridTime s v (gridK d D (D₁ + 1)) n (j + 1)))⁻¹ ^ 4)
          * gridStep s v (gridK d D (D₁ + 1)) n ^ ((3 : ℝ) / 2) := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j < gridK d D (D₁ + 1) n
    · have hu1 : gridTime s v (gridK d D (D₁ + 1)) n (j + 1) < 1 :=
        (GoodEvent_gridTime_le (hsv n) (by omega : j + 1 ≤ gridK d D (D₁ + 1) n)).trans_lt
          (hv1 n)
      filter_upwards [Expansion_condExp_A_succ_rpow d (E n) s v (gridK d D (D₁ + 1)) n j
        (hE' n) (hs0 n) (hsv n) (hK0 n) hj hu1] with ω h _
      exact h
    · exact ae_of_all _ fun ω h => absurd h hj
  filter_upwards [grid_expansion_all' d (E n) s v (gridK d D (D₁ + 1)) (hE' n) hs0 hsv hv1 hK0 n,
    hRae] with ω hexp hRω hω a
  obtain ⟨⟨hI0, -⟩, hZ, hY, hjlt, -⟩ := hGω ω hω
  dsimp only
  -- abbreviations
  set K : ℕ → ℕ := gridK d D (D₁ + 1) with hKdef
  set τ : ℕ := gridTauFull d E s v K δ D ε n ω with hτdef
  set u : ℕ → ℝ := gridTime s v K n with hudef
  set Δ : ℝ := gridStep s v K n with hΔdef
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set W : ℕ := d.W n with hWdef
  set Az : ℝ := azumaMm d E δ ε n with hAzdef
  set r : ℝ := etaT (E n) (s n) / etaT (E n) (u τ) with hrdef
  set M : ℝ := scaleM (d.L n) W (E n) (u τ) with hMdef
  set T : ℝ := tailT (d.L n) W (E n) D (u τ) (zdist2 (d.L n) (a.1 - a.2) : ℝ) with hTdef
  set Λ : ℝ := Real.exp (Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) with hΛdef
  set K₀ : ℝ := 180 * 40002 ^ 2 * (1 + Real.log ((d.L n) : ℝ)) with hK₀def
  set D'' : ℝ := D + 3 / c + 1 with hD''def
  -- basic facts
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hL1 : 1 ≤ (d.L n) := by omega
  have hW1 : 1 ≤ W := d.W_pos n
  have hLr : (1 : ℝ) ≤ ((d.L n) : ℝ) := by exact_mod_cast hL1
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < (W : ℝ) := by linarith
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  have hNeq : N = (W : ℝ) ^ 2 * ((d.L n) : ℝ) ^ 2 := by
    rw [hNdef, Sizes.size_eq]; push_cast; ring
  have hL2 : (1 : ℝ) ≤ ((d.L n) : ℝ) ^ 2 := one_le_pow₀ hLr
  have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hWr
  have hWN : (W : ℝ) ^ 2 ≤ N := by rw [hNeq]; exact le_mul_of_one_le_right (sq_nonneg _) hL2
  have hLN : ((d.L n) : ℝ) ^ 2 ≤ N := by rw [hNeq]; exact le_mul_of_one_le_left (sq_nonneg _) hW2
  have hEn : |E n| < 2 := hE' n
  have hm0 : 0 < (spectralM (E n)).im := spectralM_im_pos hEn
  have hm1 : (spectralM (E n)).im ≤ 1 := StepBound_im_le_one (E n)
  have hξ : ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) = 1 := StepBound_xi_one hEn
  have hτK : τ ≤ K n := gridTauFull_le E s v K δ D ε n ω
  have hΔ0 : 0 ≤ Δ := GoodEvent_gridStep_nonneg (hsv n)
  have hu0 : u 0 = s n := GoodEvent_gridTime_zero
  have hmono : ∀ i j, i ≤ j → u i ≤ u j := fun i j h => GoodEvent_gridTime_mono (hsv n) h
  have hsu : ∀ j, s n ≤ u j := fun j => by rw [← hu0]; exact hmono 0 j (Nat.zero_le j)
  have hu_eq : ∀ j, u j = s n + j * Δ := fun j => rfl
  have huτv : u τ ≤ v n := GoodEvent_gridTime_le (hsv n) hτK
  have huτt : u τ ≤ t n := huτv.trans (hvt n)
  have huτ1 : u τ < 1 := huτt.trans_lt (ht1 n)
  have hs1 : s n < 1 := (hsu τ).trans_lt huτ1
  have hMτ : 1 ≤ M := by
    have h29 := scaleM_ge_pow29 hL1 hW1 hEn (hs0 n) (hsu τ) huτt (ht1 n) hS
    have hr : 1 ≤ (1 - s n) / (1 - u τ) := by
      rw [one_le_div (by linarith)]; linarith [hsu τ]
    exact (one_le_pow₀ hr).trans h29
  have hM0 : 0 < M := by linarith
  have hlog0 : 0 ≤ Real.log (W : ℝ) := by linarith
  have hst0 : ∀ x, 0 ≤ ellStar (d.L n) W x := fun x => by
    unfold ellStar
    refine mul_nonneg (Real.rpow_nonneg hlog0 _) ?_
    unfold ellT
    by_cases hx : x < 1
    · exact le_min (by have := Real.sqrt_nonneg (1 - x); positivity) (Nat.cast_nonneg _)
    · have : 1 - x ≤ 0 := by linarith
      rw [Real.sqrt_eq_zero'.2 this, div_zero]
      exact le_min le_rfl (Nat.cast_nonneg _)
  have hηs : 0 < etaT (E n) (s n) := etaT_pos hEn hs1
  have hητ : 0 < etaT (E n) (u τ) := etaT_pos hEn huτ1
  have hr1 : 1 ≤ r := by
    rw [hrdef, one_le_div hητ]
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [hsu τ]) hm0.le
  have hr0 : 0 ≤ r := by linarith
  have hΔ1 : Δ ≤ 1 := by
    refine hΔCK.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 ?_)
    unfold CK; linarith
  have hT0 : 0 < T := tailT_pos hW1 (d.L n) (E n) D (u τ) _
  have hWD : N ^ (-(D / 2)) ≤ (W : ℝ) ^ (-D) := StepBound_Wpow hWr hWN hD0
  have hTW : (W : ℝ) ^ (-D) ≤ T := by
    rw [hTdef]; unfold tailT
    have : 0 ≤ (scaleM (d.L n) W (E n) (u τ) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) (a.1 - a.2) : ℝ) / ellT (d.L n) (u τ))) :=
      mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le
    linarith
  -- the expansion at `k = τ`
  rw [hexp τ hτK a]
  -- (I) the initial term
  have hX4 : 0 < N ^ (δ / 16) := Real.rpow_pos_of_pos hN0 _
  have hA0 : ∀ b : Z2 (d.L n) × Z2 (d.L n), ‖Avec d (E n) s v K n 0 ω b‖ ≤
      N ^ (δ / 16) * tailT (d.L n) W (E n) D (s n) (zdist2 (d.L n) (b.1 - b.2) : ℝ) := by
    intro b; have := hI0 b; rwa [hu0] at this
  have hfar4 : UkerFar (d.L n) W (s n) (u τ) (ellStar (d.L n) W (u τ) / 4) D'' := by
    intro x y hxy
    exact hUfar (s n) (u τ) (hs0 n) (hsu τ) huτt x y (by linarith [hst0 (u τ)])
  have hfl4 : 4 * ((d.L n : ℕ) : ℝ) ^ 2 * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D) := by
    refine le_trans ?_ hfl16
    have hWD'' : 0 ≤ (W : ℝ) ^ (-D'') := Real.rpow_nonneg hW0.le _
    have h1 : 4 * ((d.L n : ℕ) : ℝ) ^ 2 ≤ 16 * ((d.L n : ℕ) : ℝ) ^ 6 * (W : ℝ) ^ 6 := by
      have hL6 : ((d.L n : ℕ) : ℝ) ^ 2 ≤ ((d.L n : ℕ) : ℝ) ^ 6 := pow_le_pow_right₀ hLr (by norm_num)
      have hW6 : 1 ≤ (W : ℝ) ^ 6 := one_le_pow₀ hWr
      have hL0 : 0 ≤ ((d.L n : ℕ) : ℝ) ^ 2 := sq_nonneg _
      calc 4 * ((d.L n : ℕ) : ℝ) ^ 2 ≤ 16 * ((d.L n : ℕ) : ℝ) ^ 6 * 1 := by linarith
        _ ≤ 16 * ((d.L n : ℕ) : ℝ) ^ 6 * (W : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left hW6 (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hWD''
  have hIb : ‖Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (u 0) (u τ)
      (Avec d (E n) s v K n 0 ω) a‖ ≤
      (Λ + 1) * (N ^ (δ / 16) * r ^ 2) *
          (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 6 * ellStar (d.L n) W (u τ) then 1 else 0) * T +
        30000 * Λ * N ^ (δ / 16) * T + 2 * (N ^ (δ / 16) * r ^ 2 * (W : ℝ) ^ (-D)) := by
    rw [hξ, hu0]
    exact StepBound_init (d.L n) W hL3 (E := E n) (D := D) (D'' := D'') (s := s n) (u := u τ)
      hEn hD0 (hs0 n) (hsu τ) huτ1 hlogW hMτ hfar4 hfl4 hX4 hA0 a
  -- (Dr) the drift
  have hK₀1 : 1 ≤ K₀ := by
    have := Real.log_nonneg hLr
    rw [hK₀def]; linarith
  have hΛε : 1 ≤ N ^ ε := Real.one_le_rpow hN1 hε.le
  have hujt : ∀ j ≤ τ, u j ≤ t n := fun j hj => (hmono j τ hj).trans huτt
  have hE2 : ∀ j < τ, E2Hyp (d.L n) W (E n) (s n) (u j) (u τ) D (N ^ ε) K₀
      (pathH d s v K n j ω) := by
    intro j hj
    obtain ⟨hJ, hGj⟩ := hjlt j hj
    have hj0 : 0 ≤ u j := (hs0 n).trans (hsu j)
    have hj1 : u j < 1 := (hujt j hj.le).trans_lt (ht1 n)
    have hKfar : ∀ x y : Z2 (d.L n), ellStar (d.L n) W (u j) / 8 ≤ (zdist2 (d.L n) (x - y) : ℝ) →
        ‖Kpm (d.L n) W (E n) (u j) x y‖ ≤ (W : ℝ) ^ (-D) := by
      intro x y hxy
      have hth := hThfar (u j) (u j) hj0 le_rfl (hujt j hj.le) x y (by linarith)
      have hξ' : (Complex.normSq (spectralM (E n)) : ℂ) = 1 := hξ
      unfold Kpm
      rw [hξ', mul_one, mul_one, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
      have hWi : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hWr)
      calc ((W : ℝ)⁻¹) ^ 2 * ‖Theta (d.L n) (u j : ℂ) x y‖
          ≤ 1 * ‖Theta (d.L n) (u j : ℂ) x y‖ := mul_le_mul_of_nonneg_right hWi (norm_nonneg _)
        _ ≤ (W : ℝ) ^ (-D) := by rw [one_mul]; exact hth
    exact ⟨hL3, hEn, hs0 n, hsu j, hmono j τ hj.le, huτ1, hΛε, hK₀1, hlogW, hfloor, hMτ, hGj,
      hJ.le.trans (hthr (u j) (hsu j) (hujt j hj.le)),
      kpmBoundProp5 (d.L n) W (E n) (u j) hL3 hEn hj0 hj1, hKfar⟩
  have hJj : ∀ j < τ, jStarMat (d.L n) W (E n) D (u j) (pathH d s v K n j ω) ≤
      N ^ δ * (etaT (E n) (s n) / etaT (E n) (u j)) ^ 4 := fun j hj => (hjlt j hj).1.le
  have hfarj : ∀ j < τ, UkerFar (d.L n) W (u j) (u τ) (ellStar (d.L n) W (u τ)) D'' := by
    intro j hj x y hxy
    exact hUfar (u j) (u τ) ((hs0 n).trans (hsu j)) (hmono j τ hj.le) huτt x y
      (by linarith [hst0 (u τ)])
  set α : ℝ := 6 * lossE2 (d.L n) W (N ^ ε) K₀ * N ^ 4 with hαdef
  have hloss0 : 0 ≤ lossE2 (d.L n) W (N ^ ε) K₀ := by unfold lossE2; positivity
  have hα0 : 0 ≤ α := by positivity
  have hηle : ∀ x, u 0 ≤ x → x ≤ t n → (1 - x)⁻¹ ≤ N := by
    intro x hx0 hxt
    have hx1 : x < 1 := hxt.trans_lt (ht1 n)
    have hηx : 0 < etaT (E n) x := etaT_pos hEn hx1
    have h1 : etaT (E n) x ≤ 1 - x := by
      unfold etaT
      calc (1 - x) * (spectralM (E n)).im ≤ (1 - x) * 1 :=
            mul_le_mul_of_nonneg_left hm1 (by linarith)
        _ = 1 - x := mul_one _
    exact (inv_anti₀ hηx h1).trans (hηN x hxt)
  have hcorr : ∀ j < τ, ‖Uop (d.L n) 1 (u (j + 1)) (u τ)
        ((fun b => ELKLK (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2 +
            EGt (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2) -
          Uop (d.L n) 1 (u j) (u (j + 1))
            (fun b => ELKLK (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2 +
              EGt (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2)) a‖ ≤
        5 * N ^ 4 * Δ * α := by
    intro j hj
    have hj0 : 0 ≤ u j := (hs0 n).trans (hsu j)
    have hsucc : u (j + 1) = u j + Δ := by rw [hu_eq, hu_eq]; push_cast; ring
    have hjτ : u j + Δ ≤ u τ := by rw [← hsucc]; exact hmono _ _ hj
    have hDb : ∀ b : Z2 (d.L n) × Z2 (d.L n),
        ‖(fun b : Z2 (d.L n) × Z2 (d.L n) =>
          ELKLK (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2 +
            EGt (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2) b‖ ≤ α := fun b =>
      StepBound_Dbound (d.L n) W (hE2 j hj) hD0 (hηN (u j) (hujt j hj.le)) hWN hLN hN1 b
    have h := StepBound_corr (d.L n) hL3 hEn hj0 hΔ0 hjτ huτ1 hDb a
    rw [hsucc]
    refine h.trans ?_
    have hj1 : u j + Δ ≤ t n := hjτ.trans huτt
    have hηj : 0 < etaT (E n) (u j + Δ) := etaT_pos hEn (hj1.trans_lt (ht1 n))
    have hx0 : 0 ≤ etaT (E n) (u j + Δ) / etaT (E n) (u τ) := div_nonneg hηj.le hητ.le
    have hx : etaT (E n) (u j + Δ) / etaT (E n) (u τ) ≤ N := by
      have hle1 : etaT (E n) (u j + Δ) ≤ 1 := by
        unfold etaT
        have : 1 - (u j + Δ) ≤ 1 := by linarith
        calc (1 - (u j + Δ)) * (spectralM (E n)).im ≤ 1 * 1 :=
              mul_le_mul this hm1 hm0.le zero_le_one
          _ = 1 := one_mul 1
      rw [div_eq_mul_inv]
      calc etaT (E n) (u j + Δ) * (etaT (E n) (u τ))⁻¹ ≤ 1 * N :=
            mul_le_mul hle1 (hηN (u τ) huτt) (inv_nonneg.2 hητ.le) zero_le_one
        _ = N := one_mul N
    have hy0 : 0 ≤ (1 - u j)⁻¹ := inv_nonneg.2 (by linarith [(hujt j hj.le).trans_lt (ht1 n)])
    have hz0 : 0 ≤ (1 - (u j + Δ))⁻¹ := inv_nonneg.2 (by linarith [hj1.trans_lt (ht1 n)])
    exact StepBound_corr_num hN1 hΔ0 hΔ1 hα0 hx0 hx hy0
      (hηle (u j) (by rw [hu0]; exact hsu j) (hujt j hj.le)) hz0
      (hηle (u j + Δ) (by rw [hu0]; linarith [hsu j]) hj1)
  have hDr := StepBound_driftSum (d.L n) W hL3 (E := E n) (s := s n) (D := D) (D'' := D'')
    (Λ := N ^ ε) (K₀ := K₀) (Θ := N ^ δ) (Δ := Δ) (Cc := 5 * N ^ 4 * Δ * α) u
    (fun j => pathH d s v K n j ω) τ hu_eq (hs0 n) hΔ0 huτ1 hEn hE2 hJj hfarj hfl16 a hcorr
  have hDrEq : (∑ j ∈ Finset.range τ, (Δ : ℂ) •
      Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (u (j + 1)) (u τ)
        (Dgrid d (E n) s v K n j ω)) a =
      ∑ j ∈ Finset.range τ, (Δ : ℂ) * Uop (d.L n) 1 (u (j + 1)) (u τ)
        (fun b => ELKLK (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2 +
          EGt (d.L n) W (E n) (u j) (pathH d s v K n j ω) b.1 b.2) a := by
    rw [Finset.sum_apply, hξ]
    rfl
  rw [← hDrEq, ← hrdef, ← hMdef, ← hTdef] at hDr
  set Q : ℝ := 2 * Real.exp (2 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) *
      lossE2 (d.L n) W (N ^ ε) K₀ * ((spectralM (E n)).im)⁻¹ with hQdef
  have hN2δ : (N ^ δ) ^ 2 = N ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  set χ3 : ℝ := if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 3 * ellStar (d.L n) W (u τ) then 1 else 0
    with hχ3def
  have hDr' : ‖(∑ j ∈ Finset.range τ, (Δ : ℂ) •
      Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (u (j + 1)) (u τ)
        (Dgrid d (E n) s v K n j ω)) a‖ ≤
      Q * (N ^ (2 * δ) * r ^ 8 * M⁻¹ / 6 + N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2) / 7 +
        χ3 * r ^ 3) * T + τ * (Δ * (5 * N ^ 4 * Δ * α)) := by
    refine hDr.trans (le_of_eq ?_)
    rw [hQdef, hN2δ]; ring
  -- the transport-start correction against the `r⁸` term
  have hτΔ : (τ : ℝ) * Δ ≤ 1 := by
    have hKpos : 0 < K n := Nat.pos_of_ne_zero (hK0 n)
    have hKR : (0 : ℝ) < K n := by exact_mod_cast hKpos
    have hτR : (τ : ℝ) ≤ K n := by exact_mod_cast hτK
    calc (τ : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hτR hΔ0
      _ = v n - s n := by rw [hΔdef]; unfold gridStep; field_simp
      _ ≤ 1 := by linarith [hv1 n, hs0 n]
  have hlossN : lossE2 (d.L n) W (N ^ ε) K₀ ≤ N ^ (6 * ε) * N / 4 := by
    have he : 1 ≤ Real.exp (2 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) :=
      Real.one_le_exp (by positivity)
    have hi : 1 ≤ ((spectralM (E n)).im)⁻¹ := (one_le_inv₀ hm0).2 hm1
    have h1 : 1 ≤ 2 * Real.exp (2 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) *
        ((spectralM (E n)).im)⁻¹ := by
      have := mul_le_mul he hi zero_le_one (by linarith)
      linarith
    have e : Q = lossE2 (d.L n) W (N ^ ε) K₀ * (2 * Real.exp (2 * Real.log (W : ℝ) ^ ((3 : ℝ) / 4)) *
        ((spectralM (E n)).im)⁻¹) := by rw [hQdef]; ring
    have h2 := mul_le_mul_of_nonneg_left h1 hloss0
    have h3 := hQ1
    rw [Real.rpow_one] at h3
    calc lossE2 (d.L n) W (N ^ ε) K₀ = lossE2 (d.L n) W (N ^ ε) K₀ * 1 := (mul_one _).symm
      _ ≤ _ := h2
      _ = Q := e.symm
      _ ≤ _ := h3
  have hMN : M ≤ N := (LemDecCalE_scaleM_le_sq hL1 hEn huτ1).trans hWN
  have hMi : N⁻¹ ≤ M⁻¹ := inv_anti₀ hM0 hMN
  have hNT : N ^ (-(D / 2)) ≤ T := hWD.trans hTW
  have hN2δ1 : 1 ≤ N ^ (2 * δ) := Real.one_le_rpow hN1 (by positivity)
  have hr8 : 1 ≤ r ^ 8 := one_le_pow₀ hr1
  have hNCK0 : 0 ≤ N ^ (-CK D (D₁ + 1)) := Real.rpow_nonneg hN0.le _
  have hsmallC : 15 / 2 * N ^ (10 + D / 2 - CK D (D₁ + 1)) ≤ 1 :=
    StepBound_small hN7 (by unfold CK; linarith) (by norm_num)
  have eC : N ^ 9 * N ^ (-CK D (D₁ + 1)) =
      N ^ (10 + D / 2 - CK D (D₁ + 1)) * (N ^ (-1 : ℝ) * N ^ (-(D / 2))) := by
    rw [← Real.rpow_natCast N 9, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hCorr : (τ : ℝ) * (Δ * (5 * N ^ 4 * Δ * α)) ≤
      N ^ (6 * ε) * (N ^ (2 * δ) * r ^ 8 * M⁻¹) * T := by
    have he6 : 0 ≤ N ^ (6 * ε) := Real.rpow_nonneg hN0.le _
    have hpos1 : 0 ≤ 5 * N ^ 4 * Δ * α := by positivity
    have hA : 15 / 2 * N ^ 9 * Δ ≤ M⁻¹ * T := by
      have h1 : 15 / 2 * N ^ 9 * Δ ≤ 15 / 2 * N ^ 9 * N ^ (-CK D (D₁ + 1)) :=
        mul_le_mul_of_nonneg_left hΔCK (by positivity)
      have h2 : 15 / 2 * N ^ 9 * N ^ (-CK D (D₁ + 1)) =
          (15 / 2 * N ^ (10 + D / 2 - CK D (D₁ + 1))) * (N⁻¹ * N ^ (-(D / 2))) := by
        rw [mul_assoc, eC, Real.rpow_neg_one]; ring
      have h3 : (15 / 2 * N ^ (10 + D / 2 - CK D (D₁ + 1))) * (N⁻¹ * N ^ (-(D / 2))) ≤
          1 * (N⁻¹ * N ^ (-(D / 2))) :=
        mul_le_mul_of_nonneg_right hsmallC (by positivity)
      have h4 : N⁻¹ * N ^ (-(D / 2)) ≤ M⁻¹ * T :=
        mul_le_mul hMi hNT (by positivity) (inv_nonneg.2 hM0.le)
      linarith
    have hB : M⁻¹ * T ≤ N ^ (2 * δ) * r ^ 8 * M⁻¹ * T := by
      have h0 : 0 ≤ M⁻¹ * T := mul_nonneg (inv_nonneg.2 hM0.le) hT0.le
      have h1 : 1 ≤ N ^ (2 * δ) * r ^ 8 := one_le_mul_of_one_le_of_one_le hN2δ1 hr8
      have := mul_le_mul_of_nonneg_right h1 h0
      linarith
    calc (τ : ℝ) * (Δ * (5 * N ^ 4 * Δ * α)) = ((τ : ℝ) * Δ) * (5 * N ^ 4 * Δ * α) := by ring
      _ ≤ 1 * (5 * N ^ 4 * Δ * α) := mul_le_mul_of_nonneg_right hτΔ hpos1
      _ = 30 * N ^ 8 * Δ * lossE2 (d.L n) W (N ^ ε) K₀ := by rw [hαdef]; ring
      _ ≤ 30 * N ^ 8 * Δ * (N ^ (6 * ε) * N / 4) :=
          mul_le_mul_of_nonneg_left hlossN (by positivity)
      _ = N ^ (6 * ε) * (15 / 2 * N ^ 9 * Δ) := by ring
      _ ≤ N ^ (6 * ε) * (N ^ (2 * δ) * r ^ 8 * M⁻¹ * T) :=
          mul_le_mul_of_nonneg_left (hA.trans hB) he6
      _ = N ^ (6 * ε) * (N ^ (2 * δ) * r ^ 8 * M⁻¹) * T := by ring
  -- (Rem) the remainder
  have hRb := StepBound_rem (d := d) (E := E) (s := s) (v := v) (K := K) (n := n) (τ := τ)
    (ω := ω) hEn (hs0 n) (hsv n) (hv1 n) hτK (fun x hx => hηN x (hx.trans (hvt n)))
    (fun j hj b => hRω j (lt_of_lt_of_le hj hτK) b) a
  have hRem : ‖(∑ j ∈ Finset.range τ,
      Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (u (j + 1)) (u τ)
        (Rgrid d (E n) s v K n j ω)) a‖ ≤ T := by
    refine hRb.trans ?_
    have h1 : Δ ^ ((1 : ℝ) / 2) ≤ N ^ (-CK D (D₁ + 1) * (1 / 2)) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow hΔ0 hΔCK (by norm_num)
    have hsmallR : 640007 * N ^ (12 - CK D (D₁ + 1) * (1 / 2) + D / 2) ≤ 1 :=
      StepBound_small hN7 (by unfold CK; linarith) (by norm_num)
    have e : N ^ 12 * N ^ (-CK D (D₁ + 1) * (1 / 2)) =
        N ^ (12 - CK D (D₁ + 1) * (1 / 2) + D / 2) * N ^ (-(D / 2)) := by
      rw [← Real.rpow_natCast N 12, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    calc 640007 * N ^ 12 * Δ ^ ((1 : ℝ) / 2)
        ≤ 640007 * N ^ 12 * N ^ (-CK D (D₁ + 1) * (1 / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (640007 * N ^ (12 - CK D (D₁ + 1) * (1 / 2) + D / 2)) * N ^ (-(D / 2)) := by
          rw [mul_assoc, e]; ring
      _ ≤ 1 * N ^ (-(D / 2)) :=
          mul_le_mul_of_nonneg_right hsmallR (Real.rpow_nonneg hN0.le _)
      _ ≤ T := by rw [one_mul]; exact hNT
  -- the charge
  have htail : N ^ (η + δ / 16) * r ^ 2 * (W : ℝ) ^ (-D) =
      N ^ η * (N ^ (δ / 16) * r ^ 2 * (W : ℝ) ^ (-D)) := by
    rw [Real.rpow_add hN0]; ring
  rw [htail]
  have hχ5 := StepBound_ind_mono (x := (zdist2 (d.L n) (a.1 - a.2) : ℝ)) (hst0 (u τ))
    (by norm_num : (5 : ℝ) ≤ 6)
  have hχ3 : χ3 ≤
      (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 6 * ellStar (d.L n) W (u τ) then 1 else 0) :=
    StepBound_ind_mono (hst0 (u τ)) (by norm_num : (3 : ℝ) ≤ 6)
  have hind0 : ∀ k : ℝ, (0 : ℝ) ≤ (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ k * ellStar (d.L n) W (u τ)
      then 1 else 0) := fun k => by split_ifs <;> norm_num
  have hMi0 : 0 ≤ M⁻¹ := inv_nonneg.2 hM0.le
  have hΛ1 : 1 ≤ Λ := Real.one_le_exp (by positivity)
  exact StepBound_core (StepBound_tri5 _ _ _ _ _) hIb (hZ a) (hY a) hDr' hCorr hRem hΛ hΛ1 hQ
    hχ5 hχ3 hT0.le (by positivity) hX4.le hAz0 (Real.rpow_nonneg hr0 _) (hind0 3)
    (by positivity) (by positivity) (Real.rpow_nonneg hN0.le _) (pow_nonneg hr0 3)
    (by positivity) (by positivity) (by positivity)

end RBM.Path
