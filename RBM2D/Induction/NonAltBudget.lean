/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.NonAltGood
import RBM2D.Induction.GridEnvelopeN

/-!
# The term budgets of the non-alternating assembled bound

Namespace `RBM.Ind`.  The argument parallels the one-dimensional formalization (the drift,
quadratic-variation and initial terms, the square-root split, and the final budget), with the
`d = 2` data of `RBM2D.Induction.NonAltGood` (`kappaNonAlt`, `epsNonAlt`, `dDriftNonAlt`,
`cQVNonAlt`, and the sharp-kernel identities): no `η_s/η_t` prefactor on any main term.

## Sections

1. `assembledRHSNonAlt`: the right-hand side of `AssembledN` (`RBM2D.Induction.GridGoodN`) at
   the target `m = K n` with the data of `NonAltGood`.
2. Elementary facts (private): `Im m ≤ 1`, `η_u ≤ 1`, `M_u ≤ W² L² = N`, `(1-v)^{-1} ≤ N`, the
   constants `cCase1, cPair1 ≥ 0`, `sqrt_add_le`, the reindexing of the time sum.
3. **Generic term budgets** for abstract kernel weights (reused in the alternating case with the
   `𝒬` weights): `tbInit` (initial term), `tbDrift` (drift term), `tbQv` (quadratic-variation
   term) over the shape `NonAltBudget_qvShape`.  The remainder term is
   `sum_weighted_stepErrN_le` (a hypothesis `hR` of `budgetNonAlt`).
4. **Their instances at the data of `NonAltGood`**: `tbInitNonAlt`, `tbDriftNonAlt`, `tbQvNonAlt`
   (`NonAltBudget_cKap`, `NonAltBudget_aQv`: the constants of `kappaNonAlt`, `qvBdNonAlt`).
5. **`budgetNonAlt`**: `assembledRHSNonAlt ≤ N^{ε₀} (Λ^{1/2} + Φ) M_v^{-k}` under explicit
   numerical inequalities (`hlog`, `hX0`, `hR`, `ha1`-`ha3`, `he1`-`he5`).
5b. `NonAltBudget_merged_inputs`: `hlog` and `hR` are, at each `n`, the conclusions of
   `sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le` at `m = K n`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The left-hand side of the budget -/

/-- **The right-hand side of `AssembledN` at `m = K n`** with the data of `NonAltGood`: `κ =
kappaNonAlt`, `ε = epsNonAlt`, `δ₀ = δ_D = W^{-D'}`, `d_j = dDriftNonAlt(u_j)`, `c = cQVNonAlt`,
`stepErr_j = stepErrN` at the envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, initial sup `X0`. -/
def assembledRHSNonAlt (d : Sizes) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k] (κ τ' : ℝ)
    (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y τK ε X0 : ℝ) (a : Fin k → Z2 (d.L n)) : ℝ :=
  kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) 0 (K n) * X0 +
    epsNonAlt k (gridTime s v K n) 0 (K n) * (d.W n : ℝ) ^ (-D') +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Φ n) D' +
        epsNonAlt k (gridTime s v K n) (j + 1) (K n) * (d.W n : ℝ) ^ (-D')) +
    ((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ)) +
    ((d.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)

/-! ## 2. Elementary facts -/

section Basic

private theorem NonAltBudget_im_le_one {E : ℝ} (hE : |E| < 2) : (spectralM E).im ≤ 1 := by
  have := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE.le] at this
  exact (le_abs_self _).trans this

/-- `η_u ≤ 1` for `0 ≤ u` (`Im m ≤ |m| = 1`). -/
private theorem NonAltBudget_etaT_le_one {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) :
    etaT E u ≤ 1 := by
  unfold etaT
  have hm := NonAltBudget_im_le_one hE
  have hm0 := (spectralM_im_pos hE).le
  nlinarith

/-- `M_u ≤ W² L²` for `0 ≤ u < 1` (`ℓ_u ≤ L`, `η_u ≤ 1`). -/
private theorem NonAltBudget_scaleM_le {L W : ℕ} [NeZero L] {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : scaleM L W E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl := ellT_pos_le hLp hu1
  have hη0 := etaT_pos hE hu1
  have hη1 := NonAltBudget_etaT_le_one hE hu0
  unfold scaleM
  have h1 : ellT L u ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hl.1.le hl.2 2
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := sq_nonneg _
  calc (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hW2) hη1 hη0.le (by positivity)
    _ = _ := mul_one _

/-- `η_v^{-1} ≤ N` gives `(1-v)^{-1} ≤ N` (`Im m ≤ 1`). -/
private theorem NonAltBudget_inv_one_sub_le {E v Nn : ℝ} (hE : |E| < 2) (hv1 : v < 1)
    (hη : (etaT E v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn := by
  have hm := NonAltBudget_im_le_one hE
  have hm0 := spectralM_im_pos hE
  have h1 : 0 < 1 - v := by linarith
  have heq : (1 - v)⁻¹ = (spectralM E).im * (etaT E v)⁻¹ := by
    unfold etaT
    field_simp
  rw [heq]
  have h0 : 0 ≤ (etaT E v)⁻¹ := by
    have := etaT_pos hE hv1
    positivity
  nlinarith

private theorem NonAltBudget_cCase1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cCase1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cCase1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

private theorem NonAltBudget_cPair1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cPair1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cPair1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

/-- Reindexing the time sum: `Σ_{j<K} f(j+1) ≤ Σ_{j<K} f j + f K`
for `0 ≤ f 0`. -/
private theorem NonAltBudget_sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) :
    ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K := by
  have h := Finset.sum_range_succ' f K
  have h2 := Finset.sum_range_succ f K
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem NonAltBudget_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The absorption step of a far part: `y N_p ≤ B`, `N_p^{-1} ≤ X`, `B ≥ 0` give `y ≤ B X`. -/
private theorem NonAltBudget_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

end Basic

/-! ## 3. Generic term budgets (abstract kernel weights) -/

section Generic

/-- **Generic initial term**: for weights `κ` with
`κ(0,K) M_{u_0}^{-k} ≤ C_κ M_{u_K}^{-k}` and an initial sup `X0 ≤ G M_{u_0}^{-k}`,
`κ(0,K) X0 ≤ C_κ G M_{u_K}^{-k}`. -/
theorem tbInit {L W : ℕ} {E : ℝ} {k K : ℕ} {Cκ G X0 : ℝ} (u : ℕ → ℝ) (κ : ℕ → ℕ → ℝ)
    (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G)
    (hker : κ 0 K * (scaleM L W E (u 0) ^ k)⁻¹ ≤ Cκ * (scaleM L W E (u K) ^ k)⁻¹)
    (hX0 : X0 ≤ G * (scaleM L W E (u 0) ^ k)⁻¹) :
    κ 0 K * X0 ≤ Cκ * G * (scaleM L W E (u K) ^ k)⁻¹ := by
  calc κ 0 K * X0 ≤ κ 0 K * (G * (scaleM L W E (u 0) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_left hX0 hκ0
    _ = G * (κ 0 K * (scaleM L W E (u 0) ^ k)⁻¹) := by ring
    _ ≤ G * (Cκ * (scaleM L W E (u K) ^ k)⁻¹) := mul_le_mul_of_nonneg_left hker hG
    _ = _ := by ring

/-- **Generic drift term**: for weights `κ, ε` with
`κ(j+1,K) M_{u_j}^{-k} ≤ C_κ M_{u_K}^{-k}` and `κ(j+1,K) ≤ C_far` (the far part), `ε(j+1,K) ≤ C_ε`,
and drift levels `d_j ≤ a M_{u_j}^{-k} η_{u_j}^{-1} + b`, `0 ≤ δ_j ≤ δ_max`:
`Δ Σ_{j<K} (κ(j+1,K) d_j + ε(j+1,K) δ_j) ≤ C_κ a M_{u_K}^{-k} Σ_j Δ/η_{u_j} +
(K Δ)(C_far b + C_ε δ_max)`. -/
theorem tbDrift {L W : ℕ} {E : ℝ} {k K : ℕ} {Δ Cκ Cε Cfar a b δmax : ℝ} (u : ℕ → ℝ)
    (κ ε : ℕ → ℕ → ℝ) (dd δ : ℕ → ℝ) (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hκ0 : ∀ j < K, 0 ≤ κ (j + 1) K) (hε0 : ∀ j < K, 0 ≤ ε (j + 1) K)
    (hκM : ∀ j < K, κ (j + 1) K * (scaleM L W E (u j) ^ k)⁻¹ ≤ Cκ * (scaleM L W E (u K) ^ k)⁻¹)
    (hκfar : ∀ j < K, κ (j + 1) K ≤ Cfar) (hεC : ∀ j < K, ε (j + 1) K ≤ Cε)
    (hd : ∀ j < K, dd j ≤ a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b)
    (hδ0 : ∀ j < K, 0 ≤ δ j) (hδ : ∀ j < K, δ j ≤ δmax) (hη : ∀ j < K, 0 < etaT E (u j)) :
    Δ * ∑ j ∈ Finset.range K, (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
      Cκ * a * (scaleM L W E (u K) ^ k)⁻¹ * ∑ j ∈ Finset.range K, Δ / etaT E (u j) +
        ((K : ℝ) * Δ) * (Cfar * b + Cε * δmax) := by
  have hstep : ∀ j ∈ Finset.range K,
      Δ * (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤
        Cκ * a * (scaleM L W E (u K) ^ k)⁻¹ * (Δ / etaT E (u j)) +
          Δ * (Cfar * b + Cε * δmax) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have h1 : κ (j + 1) K * dd j ≤
        κ (j + 1) K * (a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b) :=
      mul_le_mul_of_nonneg_left (hd j hjK) (hκ0 j hjK)
    have h2 : κ (j + 1) K * (a * ((scaleM L W E (u j) ^ k)⁻¹ * (etaT E (u j))⁻¹) + b) =
        (a * (etaT E (u j))⁻¹) * (κ (j + 1) K * (scaleM L W E (u j) ^ k)⁻¹) +
          κ (j + 1) K * b := by ring
    have h3 : (a * (etaT E (u j))⁻¹) * (κ (j + 1) K * (scaleM L W E (u j) ^ k)⁻¹) ≤
        (a * (etaT E (u j))⁻¹) * (Cκ * (scaleM L W E (u K) ^ k)⁻¹) :=
      mul_le_mul_of_nonneg_left (hκM j hjK) (mul_nonneg ha (inv_nonneg.2 (hη j hjK).le))
    have h4 : κ (j + 1) K * b ≤ Cfar * b := mul_le_mul_of_nonneg_right (hκfar j hjK) hb
    have h5 : ε (j + 1) K * δ j ≤ Cε * δmax :=
      calc ε (j + 1) K * δ j ≤ ε (j + 1) K * δmax :=
            mul_le_mul_of_nonneg_left (hδ j hjK) (hε0 j hjK)
        _ ≤ Cε * δmax := mul_le_mul_of_nonneg_right (hεC j hjK) ((hδ0 j hjK).trans (hδ j hjK))
    have h6 : κ (j + 1) K * dd j + ε (j + 1) K * δ j ≤
        (a * (etaT E (u j))⁻¹) * (Cκ * (scaleM L W E (u K) ^ k)⁻¹) + (Cfar * b + Cε * δmax) := by
      linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hΔ
    have e : Δ * ((a * (etaT E (u j))⁻¹) * (Cκ * (scaleM L W E (u K) ^ k)⁻¹) +
        (Cfar * b + Cε * δmax)) =
        Cκ * a * (scaleM L W E (u K) ^ k)⁻¹ * (Δ / etaT E (u j)) +
          Δ * (Cfar * b + Cε * δmax) := by
      rw [div_eq_mul_inv]; ring
    rw [e] at h7
    exact h7
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- **The shape of the quadratic-variation majorant** (that of `qvBdNonAlt`, with the constants
`A` (of the first term) and `B` (of the second) abstract, `G = Γ² Λ`, `Wd = W^{-D''}`):
`A ρ_{u,w}^{2k} (G M_u^{-2k} η_u^{-1} + Wd) + B ((1-u)/(1-w))^{2k} Wd`. -/
def NonAltBudget_qvShape (L W : ℕ) (E : ℝ) (k : ℕ) (A B G Wd u w : ℝ) : ℝ :=
  A * rhoR L u w ^ (2 * k) * (G * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + Wd) +
    B * ((1 - u) / (1 - w)) ^ (2 * k) * Wd

/-- One term of the QV budget: `ρ_{u,w}^{2k} M_u^{-2k} = (M_w^{-k})²` (the sharp identity
`NonAltGood_rhoR_mul_scaleM_inv`) and the crude bounds `ρ_{u,w}, (1-u)/(1-w) ≤ N` of the far
part. -/
private theorem NonAltBudget_qv_step {L W : ℕ} [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2)
    (k : ℕ) {A B G Wd Nn u w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hWd : 0 ≤ Wd)
    (hu0 : 0 ≤ u) (huw : u ≤ w) (hw1 : w < 1) (hMw : 1 ≤ scaleM L W E w)
    (hMu : scaleM L W E u ≤ Nn) (hwN : (1 - w)⁻¹ ≤ Nn) :
    NonAltBudget_qvShape L W E k A B G Wd u w ≤
      A * G * ((scaleM L W E w ^ k)⁻¹) ^ 2 * (etaT E u)⁻¹ + (A + B) * Nn ^ (2 * k) * Wd := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu1 : u < 1 := huw.trans_lt hw1
  have hMu0 := scaleM_pos hLp hWp hE hu1
  have hMw0 := scaleM_pos hLp hWp hE hw1
  have hηu := etaT_pos hE hu1
  have hid := NonAltGood_rhoR_mul_scaleM_inv (L := L) (W := W) hE hu1 hw1
  -- `ρ = M_u / M_w`
  have hρ : rhoR L u w = scaleM L W E u * (scaleM L W E w)⁻¹ := by
    have h : rhoR L u w * (scaleM L W E u)⁻¹ = (scaleM L W E w)⁻¹ := hid
    field_simp at h ⊢
    linarith
  have hρ0 : 0 ≤ rhoR L u w := by rw [hρ]; positivity
  have hρN : rhoR L u w ≤ Nn := by
    rw [hρ]
    have h1 : (scaleM L W E w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hMw
    calc scaleM L W E u * (scaleM L W E w)⁻¹ ≤ Nn * 1 :=
          mul_le_mul hMu h1 (by positivity) (hMu0.le.trans hMu)
      _ = Nn := mul_one _
  have hNn0 : 0 ≤ Nn := hMu0.le.trans hMu
  have hρ2k : rhoR L u w ^ (2 * k) * (scaleM L W E u ^ (2 * k))⁻¹ =
      ((scaleM L W E w ^ k)⁻¹) ^ 2 := by
    have h1 : rhoR L u w ^ (2 * k) * (scaleM L W E u ^ (2 * k))⁻¹ =
        ((scaleM L W E w)⁻¹) ^ (2 * k) := by
      rw [← inv_pow, ← mul_pow, hid]
    rw [h1]
    ring
  have hq0 : 0 ≤ (1 - u) / (1 - w) := div_nonneg (by linarith) (by linarith)
  have hqN : (1 - u) / (1 - w) ≤ Nn := by
    have h1w : 0 < 1 - w := by linarith
    have : (1 - u) / (1 - w) ≤ (1 - w)⁻¹ := by
      rw [div_eq_mul_inv]
      have h0 : 0 ≤ (1 - w)⁻¹ := inv_nonneg.2 h1w.le
      nlinarith
    exact this.trans hwN
  have hρk : rhoR L u w ^ (2 * k) ≤ Nn ^ (2 * k) := pow_le_pow_left₀ hρ0 hρN _
  have hqk : ((1 - u) / (1 - w)) ^ (2 * k) ≤ Nn ^ (2 * k) := pow_le_pow_left₀ hq0 hqN _
  unfold NonAltBudget_qvShape
  have e : A * rhoR L u w ^ (2 * k) *
        (G * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + Wd) =
      A * G * (rhoR L u w ^ (2 * k) * (scaleM L W E u ^ (2 * k))⁻¹) * (etaT E u)⁻¹ +
        A * rhoR L u w ^ (2 * k) * Wd := by ring
  rw [e, hρ2k]
  have t1 : A * rhoR L u w ^ (2 * k) * Wd ≤ A * Nn ^ (2 * k) * Wd :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρk hA) hWd
  have t2 : B * ((1 - u) / (1 - w)) ^ (2 * k) * Wd ≤ B * Nn ^ (2 * k) * Wd :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqk hB) hWd
  have e2 : (A + B) * Nn ^ (2 * k) * Wd = A * Nn ^ (2 * k) * Wd + B * Nn ^ (2 * k) * Wd := by ring
  linarith

/-- **Generic quadratic-variation term**: for the proxies `c_j = Δ k
NonAltBudget_qvShape(u_{j+1}, u_K)` with abstract `A, B ≥ 0`,
`Σ_j c_j ≤ k A G M_{u_K}^{-2k} Σ_j Δ/η_{u_{j+1}} + (K Δ) k ((A + B) N^{2k} Wd)`
(`M_{u_K} ≥ 1`, `M_{u_i} ≤ N`, `(1 - u_K)^{-1} ≤ N`). -/
theorem tbQv {L W : ℕ} [NeZero L] [NeZero W] {E : ℝ} (hE : |E| < 2) (k K : ℕ)
    {A B G Wd Δ Nn : ℝ} (u : ℕ → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hWd : 0 ≤ Wd)
    (hΔ : 0 ≤ Δ) (hu0 : ∀ i ≤ K, 0 ≤ u i) (hu1 : ∀ i ≤ K, u i < 1)
    (hmono : ∀ j < K, u (j + 1) ≤ u K) (hMK : 1 ≤ scaleM L W E (u K))
    (hMN : ∀ i ≤ K, scaleM L W E (u i) ≤ Nn) (hKN : (1 - u K)⁻¹ ≤ Nn) :
    ∑ j ∈ Finset.range K, Δ * ((k : ℝ) * NonAltBudget_qvShape L W E k A B G Wd (u (j + 1)) (u K)) ≤
      (k : ℝ) * A * G * ((scaleM L W E (u K) ^ k)⁻¹) ^ 2 *
          ∑ j ∈ Finset.range K, Δ / etaT E (u (j + 1)) +
        ((K : ℝ) * Δ) * ((k : ℝ) * ((A + B) * Nn ^ (2 * k) * Wd)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hstep : ∀ j ∈ Finset.range K,
      Δ * ((k : ℝ) * NonAltBudget_qvShape L W E k A B G Wd (u (j + 1)) (u K)) ≤
        (k : ℝ) * A * G * ((scaleM L W E (u K) ^ k)⁻¹) ^ 2 * (Δ / etaT E (u (j + 1))) +
          Δ * ((k : ℝ) * ((A + B) * Nn ^ (2 * k) * Wd)) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have h := NonAltBudget_qv_step hE k hA hB hG hWd (hu0 (j + 1) (by omega)) (hmono j hjK)
      (hu1 K le_rfl) hMK (hMN (j + 1) (by omega)) hKN
    have h1 := mul_le_mul_of_nonneg_left h hk0
    have h2 := mul_le_mul_of_nonneg_left h1 hΔ
    refine h2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end Generic

/-! ## 4. The generic budgets at the data of `NonAltGood` -/

section Instances

/-- `C_κ = c_1(k,κ) (1 + log L)^k (W^{τ'})^{2(k-1)}`: the constant of `kappaNonAlt` at
`K_w = W^{τ'}` without the factor `ρ^k` (`kappaNonAlt_mul_scale_pow_eq`). -/
def NonAltBudget_cKap (d : Sizes) (n k : ℕ) (κ τ' : ℝ) : ℝ :=
  cCase1 k κ * (1 + Real.log (d.L n)) ^ k * ((d.W n : ℝ) ^ τ') ^ (2 * (k - 1))

/-- `A = c_pair(k,κ) (1 + log L)^{2k} (W^{τ'})^{2(2k-1)}`: the constant of the first term of
`qvBdNonAlt` without `ρ^{2k}`. -/
def NonAltBudget_aQv (d : Sizes) (n k : ℕ) (κ τ' : ℝ) : ℝ :=
  cPair1 k κ * (1 + Real.log (d.L n)) ^ (2 * k) * ((d.W n : ℝ) ^ τ') ^ (2 * (2 * k - 1))

private theorem NonAltBudget_cKap_nonneg (d : Sizes) (n k : ℕ) (κ τ' : ℝ) :
    0 ≤ NonAltBudget_cKap d n k κ τ' := by
  unfold NonAltBudget_cKap
  have hlog : 0 ≤ Real.log (d.L n) := Real.log_natCast_nonneg _
  have hW : (0 : ℝ) ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := NonAltBudget_cCase1_nonneg k κ
  positivity

private theorem NonAltBudget_aQv_nonneg (d : Sizes) (n k : ℕ) (κ τ' : ℝ) :
    0 ≤ NonAltBudget_aQv d n k κ τ' := by
  unfold NonAltBudget_aQv
  have hlog : 0 ≤ Real.log (d.L n) := Real.log_natCast_nonneg _
  have hW : (0 : ℝ) ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := NonAltBudget_cPair1_nonneg k κ
  positivity

/-- The grid facts used throughout: `0 ≤ u_i < 1`, `u_0 = s`, `u_K = v`, `K Δ = v - s`. -/
private theorem NonAltBudget_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (i : ℕ) : 0 ≤ gridTime s v K n i :=
  GoodEvent_gridTime_nonneg hs0 hsv i

private theorem NonAltBudget_gridTime_lt_one {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hv1 : v n < 1) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i < 1 :=
  (GoodEvent_gridTime_le (K := K) hsv hi).trans_lt hv1

private theorem NonAltBudget_gridTime_last {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK1 : 1 ≤ K n) :
    gridTime s v K n (K n) = v n :=
  gridTime_last s v K n (by omega)

private theorem NonAltBudget_K_mul_step {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK1 : 1 ≤ K n) :
    (K n : ℝ) * gridStep s v K n = v n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold gridStep
  rw [mul_div_cancel₀ _ hK']

/-- **The initial term at the data of `NonAltGood`**: `κ_{0,K} X0 ≤ C_κ G M_v^{-k}`
for `X0 ≤ G M_{u_0}^{-k}`, with `C_κ = NonAltBudget_cKap` (`kappaNonAlt_mul_scale_pow_eq`). -/
theorem tbInitNonAlt (d : Sizes) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (κ τ' G X0 : ℝ)
    (hE : |E n| < 2) (hsv : s n ≤ v n) (hs0 : 0 ≤ s n) (hv1 : v n < 1) (hK1 : 1 ≤ K n)
    (hG : 0 ≤ G)
    (hX0 : X0 ≤ G * (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n 0) ^ k)⁻¹) :
    kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) 0 (K n) * X0 ≤
      NonAltBudget_cKap d n k κ τ' * G * (scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹ := by
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    NonAltBudget_gridTime_lt_one hsv hv1 hi
  have hKw : (0 : ℝ) ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hκ0 := nonAlt_hκ0 (L := d.L n) k κ _ hKw hu1 0 (K n) (Nat.zero_le _) le_rfl
  have hker := kappaNonAlt_mul_scale_pow_eq (L := d.L n) (W := d.W n) hE k κ ((d.W n : ℝ) ^ τ')
    (gridTime s v K n) (i := 0) (m := K n) (hu1 0 (Nat.zero_le _)) (hu1 _ le_rfl)
  have h := tbInit (L := d.L n) (W := d.W n) (E := E n) (k := k) (K := K n) (Cκ := NonAltBudget_cKap d n k κ τ')
    (G := G) (X0 := X0) (gridTime s v K n)
    (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n)) hκ0 hG
    (by rw [hker]; exact le_of_eq rfl) hX0
  rwa [NonAltBudget_gridTime_last hK1] at h

private theorem NonAltBudget_size_eq (d : Sizes) (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
  rw [Sizes.size_eq]; push_cast; ring

private theorem NonAltBudget_scaleM_le_size (d : Sizes) {E u : ℝ} (n : ℕ) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    scaleM (d.L n) (d.W n) E u ≤ ((d.size n : ℕ) : ℝ) := by
  rw [NonAltBudget_size_eq]; exact NonAltBudget_scaleM_le hE hu0 hu1

/-- The far part of the kernel weight: `κ M_j^{-k} ≤ C_κ M_K^{-k}`, `M_j ≤ N`, `M_K ≥ 1` give
`κ ≤ C_κ N^k`. -/
private theorem NonAltBudget_far_kappa {κj Cκ Mj MK Nn : ℝ} {k : ℕ} (hMj0 : 0 < Mj)
    (hMjN : Mj ≤ Nn) (hMK : 1 ≤ MK) (hC : 0 ≤ Cκ) (h : κj * (Mj ^ k)⁻¹ ≤ Cκ * (MK ^ k)⁻¹) :
    κj ≤ Cκ * Nn ^ k := by
  have hpos : 0 < Mj ^ k := pow_pos hMj0 k
  have h1 : κj ≤ Cκ * (MK ^ k)⁻¹ * Mj ^ k := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rwa [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one] at this
  have hMK1 : (MK ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hMK)
  have hMK0 : 0 ≤ (MK ^ k)⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) _)
  calc κj ≤ Cκ * (MK ^ k)⁻¹ * Mj ^ k := h1
    _ ≤ Cκ * 1 * Nn ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMK1 hC) (pow_le_pow_left₀ hMj0.le hMjN k)
          (pow_nonneg hMj0.le _) (by positivity)
    _ = _ := by ring

/-- The far part of the decay-error weight: `ε_{i,m} = ((1-u_i)/(1-u_m))^k ≤ N^k` when
`0 ≤ u_i < 1` and `(1 - u_m)^{-1} ≤ N`. -/
private theorem NonAltBudget_far_eps (k : ℕ) (u : ℕ → ℝ) {i m : ℕ} {Nn : ℝ} (hi0 : 0 ≤ u i)
    (hi1 : u i < 1) (hm1 : u m < 1) (hN : (1 - u m)⁻¹ ≤ Nn) : epsNonAlt k u i m ≤ Nn ^ k := by
  unfold epsNonAlt
  have h1 : 0 < 1 - u m := by linarith
  have h0 : 0 ≤ (1 - u i) / (1 - u m) := div_nonneg (by linarith) h1.le
  have : (1 - u i) / (1 - u m) ≤ (1 - u m)⁻¹ := by
    rw [div_eq_mul_inv]
    have h2 : 0 ≤ (1 - u m)⁻¹ := inv_nonneg.2 h1.le
    nlinarith
  exact pow_le_pow_left₀ h0 (this.trans hN) k

/-- **The drift term at the data of `NonAltGood`**: the drift term of the assembly bound
at the target `u_K = v` is at most `C_κ ((k-1)²+1) Γ² Φ M_v^{-k} Σ_j Δ/η_{u_j}` (the sharp kernel:
no `η_s/η_t` prefactor) plus the far part `(K Δ)(C_κ N^k · 2 W^{-D'} + N^k W^{-D'})`. -/
theorem tbDriftNonAlt (d : Sizes) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (hk : 2 ≤ k)
    (κ τ' : ℝ) (Γ Φ : ℕ → ℝ) (D' : ℝ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hK1 : 1 ≤ K n) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n)
    (hM1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n))
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ)) :
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Φ n) D' +
        epsNonAlt k (gridTime s v K n) (j + 1) (K n) * (d.W n : ℝ) ^ (-D')) ≤
      NonAltBudget_cKap d n k κ τ' * ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) *
          (scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹ *
          ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) +
        ((K n : ℝ) * gridStep s v K n) *
          (NonAltBudget_cKap d n k κ τ' * ((d.size n : ℕ) : ℝ) ^ k * (2 * (d.W n : ℝ) ^ (-D')) +
            ((d.size n : ℕ) : ℝ) ^ k * (d.W n : ℝ) ^ (-D')) := by
  have hLp : 1 ≤ d.L n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hWp : 1 ≤ d.W n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => NonAltBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    NonAltBudget_gridTime_lt_one hsv hv1 hi
  have huK := NonAltBudget_gridTime_last (s := s) (v := v) hK1
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    GoodEvent_gridTime_mono hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hKw : (0 : ℝ) ≤ (d.W n : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCκ := NonAltBudget_cKap_nonneg d n k κ τ'
  have hN1 : (1 - v n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := NonAltBudget_inv_one_sub_le hE hv1 hη
  have hMKv : 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) := by rw [huK]; exact hM1
  have hΓ2 : 0 ≤ ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) := by positivity
  have h := tbDrift (L := d.L n) (W := d.W n) (E := E n) (k := k) (K := K n)
    (Δ := gridStep s v K n) (Cκ := NonAltBudget_cKap d n k κ τ')
    (Cε := ((d.size n : ℕ) : ℝ) ^ k)
    (Cfar := NonAltBudget_cKap d n k κ τ' * ((d.size n : ℕ) : ℝ) ^ k)
    (a := (((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) (b := 2 * (d.W n : ℝ) ^ (-D'))
    (δmax := (d.W n : ℝ) ^ (-D')) (gridTime s v K n)
    (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n))
    (epsNonAlt k (gridTime s v K n))
    (fun j => dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Φ n) D')
    (fun _ => (d.W n : ℝ) ^ (-D')) hΔ0 hΓ2 (by positivity)
    (fun j hj => nonAlt_hκ0 (L := d.L n) k κ _ hKw hu1 (j + 1) (K n) (by omega) le_rfl)
    (fun j hj => nonAlt_hε0 k hu1 (j + 1) (K n) (by omega) le_rfl)
    (fun j hj => kappaNonAlt_succ_mul_scale_pow_le (L := d.L n) (W := d.W n) hE k κ _ hKw
      (gridTime s v K n) j (K n) (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega))
      (hu1 _ le_rfl))
    (fun j hj => NonAltBudget_far_kappa (k := k) (scaleM_pos hLp hWp hE (hu1 j hj.le))
      (NonAltBudget_scaleM_le_size d n hE (hu0 j) (hu1 j hj.le)) hMKv hCκ
      (kappaNonAlt_succ_mul_scale_pow_le (L := d.L n) (W := d.W n) hE k κ _ hKw
        (gridTime s v K n) j (K n) (hmono j (j + 1) (by omega)) (hmono (j + 1) (K n) (by omega))
        (hu1 _ le_rfl)))
    (fun j hj => NonAltBudget_far_eps k (gridTime s v K n) (Nn := ((d.size n : ℕ) : ℝ))
      (hu0 (j + 1)) (hu1 (j + 1) (by omega)) (hu1 (K n) le_rfl) (by rw [huK]; exact hN1))
    (fun j hj => by rw [dDriftNonAlt_eq _ _ _ _ hk])
    (fun _ _ => hW0) (fun _ _ => le_rfl)
    (fun j hj => etaT_pos hE (hu1 j hj.le))
  rw [huK] at h
  exact h

/-- **`qvBdNonAlt` has the shape `NonAltBudget_qvShape`** with `A = NonAltBudget_aQv`, `B = 1`,
`G = Γ² Λ`, `Wd = W^{-D''}`. -/
theorem NonAltBudget_qvBdNonAlt_eq_qvShape (d : Sizes) (n k : ℕ) (E : ℝ) (κ Γ Λ τ' D'' u w : ℝ) :
    qvBdNonAlt (d.L n) (d.W n) E k κ Γ Λ τ' D'' u w =
      NonAltBudget_qvShape (d.L n) (d.W n) E k (NonAltBudget_aQv d n k κ τ') 1 (Γ * (Γ * Λ))
        ((d.W n : ℝ) ^ (-D'')) u w := by
  unfold qvBdNonAlt NonAltBudget_qvShape NonAltBudget_aQv
  ring

/-- **The quadratic-variation term at the data of `NonAltGood`**: the sum of the
sub-Gaussian proxies `cQVNonAlt` at the target `u_K = v` is at most `k A Γ² Λ M_v^{-2k}
Σ_j Δ/η_{u_{j+1}}` (`A = NonAltBudget_aQv`) plus the far part `(K Δ) k ((A + 1) N^{2k} W^{-D''})`. -/
theorem tbQvNonAlt (d : Sizes) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) [NeZero k] (κ τ' : ℝ)
    (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin k → Z2 (d.L n)) (hE : |E n| < 2) (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (hv1 : v n < 1) (hK1 : 1 ≤ K n) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n)
    (hM1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n))
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ)) :
    ∑ j ∈ Finset.range (K n), (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ) ≤
      (k : ℝ) * NonAltBudget_aQv d n k κ τ' * (Γ n * (Γ n * Λ n)) *
          ((scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹) ^ 2 *
          ∑ j ∈ Finset.range (K n),
            gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) +
        ((K n : ℝ) * gridStep s v K n) *
          ((k : ℝ) * ((NonAltBudget_aQv d n k κ τ' + 1) * ((d.size n : ℕ) : ℝ) ^ (2 * k) *
            (d.W n : ℝ) ^ (-D''))) := by
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => NonAltBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    NonAltBudget_gridTime_lt_one hsv hv1 hi
  have huK := NonAltBudget_gridTime_last (s := s) (v := v) hK1
  have hmono : ∀ i m, i ≤ m → gridTime s v K n i ≤ gridTime s v K n m := fun i m him =>
    GoodEvent_gridTime_mono hsv him
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : (1 - v n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := NonAltBudget_inv_one_sub_le hE hv1 hη
  have hMKv : 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) := by rw [huK]; exact hM1
  have hcoe : ∀ j ∈ Finset.range (K n),
      (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ) =
        gridStep s v K n * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
          (NonAltBudget_aQv d n k κ τ') 1 (Γ n * (Γ n * Λ n)) ((d.W n : ℝ) ^ (-D''))
          (gridTime s v K n (j + 1)) (gridTime s v K n (K n))) := by
    intro j hj
    have hjK := Finset.mem_range.1 hj
    have hpos := qvBdNonAlt_pos (L := d.L n) (W := d.W n) hE (k := k) (κ := κ) (τ' := τ')
      (D'' := D'') hΓ hΛ (hmono (j + 1) (K n) (by omega)) (hu1 (K n) le_rfl)
    unfold cQVNonAlt
    rw [Real.coe_toNNReal _ (by positivity), NonAltBudget_qvBdNonAlt_eq_qvShape]
  rw [Finset.sum_congr rfl hcoe, huK]
  have h := tbQv (L := d.L n) (W := d.W n) (E := E n) hE k (K n)
    (A := NonAltBudget_aQv d n k κ τ') (B := 1) (G := Γ n * (Γ n * Λ n))
    (Wd := (d.W n : ℝ) ^ (-D'')) (Δ := gridStep s v K n) (Nn := ((d.size n : ℕ) : ℝ))
    (gridTime s v K n) (NonAltBudget_aQv_nonneg d n k κ τ') zero_le_one (by positivity) hW0 hΔ0
    (fun i _ => hu0 i) hu1 (fun j hj => hmono (j + 1) (K n) (by omega)) hMKv
    (fun i hi => NonAltBudget_scaleM_le_size d n hE (hu0 i) (hu1 i hi))
    (by rw [huK]; exact hN1)
  rw [huK] at h
  exact h

end Instances

/-! ## 5. The budget -/

section Budget

set_option maxHeartbeats 1600000 in
-- the proof assembles six term budgets and the final `linarith`
/-- **The budget of the non-alternating endpoint**: at a fixed
size index `n`, the right-hand side `assembledRHSNonAlt` of `AssembledN` at the target
`m = K n` (with `κ = kappaNonAlt`, `ε = epsNonAlt`, `d_j = dDriftNonAlt`, `c = cQVNonAlt`,
`stepErr = stepErrN`) is at most `N^{ε₀} (Λ^{1/2} + Φ) M_v^{-k}`, under explicit numerical
inequalities only (no random object):

* regime: `hE` (`|E| < 2`), `hs0`, `hsv`, `hv1`, `hK1` (`1 ≤ K n`), `hM1` (`1 ≤ M_v`), `hη`
  (`η_v^{-1} ≤ N`), `hΔN` (`Δ N ≤ 1`);
* levels: `hΓ` (`Γ_n = N^{ε₁}`), `hΛ` (`1 ≤ Λ_n`), `hΦ` (`0 ≤ Φ_n`);
* inputs, per index `n`: `hlog` (the conclusion of `sum_gridStep_div_etaT_le`), `hX0`
  (the initial datum), `hR` (the conclusion of `sum_weighted_stepErrN_le` at `m = K n`);
* absorption: `ha1`-`ha3` (the three main terms, against `N^{ε₀}/6, /12, /12`) and `he1`-`he5`
  (the five far parts, against `N^{ε₀}/6, /12, /12, /6, /6`), each a closed inequality between
  powers of `N` and `W`, true `∀ᶠ n` for fixed exponents with `ε₁, τ'` small and `D', D'', D_Y,
  D_t` large.

Sharp kernel: the main terms carry no `η_s/η_t` prefactor (`tbInitNonAlt`, `tbDriftNonAlt`,
`tbQvNonAlt`).  The remainder term is the hypothesis `hR`. -/
theorem budgetNonAlt (d : Sizes) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (κ τ' : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK ε₀ ε ε₁ X0 : ℝ) (a : Fin k → Z2 (d.L n))
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK1 : 1 ≤ K n)
    (hM1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n))
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ))
    (hΔN : gridStep s v K n * ((d.size n : ℕ) : ℝ) ≤ 1)
    (hΓ : Γ n = ((d.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ : 0 ≤ Φ n)
    (hlog : ∑ j ∈ Finset.range (K n),
        gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹)
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
      ((d.size n : ℕ) : ℝ) ^ (-D_t))
    (ha1 : NonAltBudget_cKap d n k κ τ' * ((d.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (ha2 : (((k : ℝ) - 1) ^ 2 + 1) * NonAltBudget_cKap d n k κ τ' *
        (((d.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (ha3 : ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * NonAltBudget_aQv d n k κ τ' *
          ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he1 : ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-D') ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he2 : (2 * NonAltBudget_cKap d n k κ τ' + 1) * ((d.size n : ℕ) : ℝ) ^ (2 * k) *
        (d.W n : ℝ) ^ (-D') ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he3 : ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * ((NonAltBudget_aQv d n k κ τ' + 1) *
          ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-D'')))) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 12)
    (he4 : ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 6)
    (he5 : ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D_t) ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ / 6) :
    assembledRHSNonAlt d E s v K n k κ τ' Γ Λ Φ D' D'' D_Y τK ε X0 a ≤
      ((d.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
        (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k := by
  have hLp : 1 ≤ d.L n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hWp : 1 ≤ d.W n := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size (d := d) n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((d.size n : ℕ) : ℝ) ^ k := pow_pos hN0 k
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => NonAltBudget_gridTime_nonneg hs0 hsv i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    NonAltBudget_gridTime_lt_one hsv hv1 hi
  have huK := NonAltBudget_gridTime_last (s := s) (v := v) hK1
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    rw [NonAltBudget_K_mul_step hK1]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hMv0 := scaleM_pos hLp hWp hE hv1
  have hMvN := NonAltBudget_scaleM_le_size d n hE (hs0.trans hsv) hv1
  have hN1' : (1 - v n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := NonAltBudget_inv_one_sub_le hE hv1 hη
  have hηv0 := etaT_pos hE hv1
  have hCκ := NonAltBudget_cKap_nonneg d n k κ τ'
  have hA0 := NonAltBudget_aQv_nonneg d n k κ τ'
  have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0' : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (spectralM_im_pos hE).le) (Real.log_nonneg hN1)
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Δ := gridStep s v K n with hΔdef
  set X := (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k with hXdef
  set Ls := (spectralM (E n)).im⁻¹ * Real.log N with hLsdef
  have hX0' : 0 ≤ X := by
    have : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ := inv_nonneg.2 hMv0.le
    positivity
  have hXk : (scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹ = X := by rw [hXdef, inv_pow]
  have hXN : (N ^ k)⁻¹ ≤ X := by
    rw [hXdef, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) (inv_anti₀ hMv0 hMvN) k
  have hN2k : N ^ (2 * k) = N ^ k * N ^ k := by rw [two_mul, pow_add]
  set P0 := N ^ ε₀ with hP0def
  set Λr := Λ n ^ ((1 : ℝ) / 2) with hΛrdef
  have hΛr1 : 1 ≤ Λr := Real.one_le_rpow hΛ (by norm_num)
  -- T1: the initial term
  have T1 : kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) 0 (K n) * X0 ≤
      P0 / 6 * X := by
    have hX0'' : X0 ≤ N ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n 0) ^ k)⁻¹ := by
      rw [GoodEvent_gridTime_zero]; exact hX0
    have h := tbInitNonAlt d n k κ τ' (N ^ ε₁) X0 hE hsv hs0 hv1 hK1
      (Real.rpow_nonneg hN0.le _) hX0''
    rw [hXk] at h
    exact h.trans (mul_le_mul_of_nonneg_right ha1 hX0')
  -- T2: the initial decay error
  have T2 : epsNonAlt k (gridTime s v K n) 0 (K n) * (d.W n : ℝ) ^ (-D') ≤ P0 / 6 * X := by
    have he := NonAltBudget_far_eps k (gridTime s v K n) (Nn := N) (i := 0) (m := K n)
      (hu0 0) (hu1 0 (Nat.zero_le _)) (hu1 (K n) le_rfl) (by rw [huK]; exact hN1')
    have h1 : epsNonAlt k (gridTime s v K n) 0 (K n) * (d.W n : ℝ) ^ (-D') ≤
        N ^ k * (d.W n : ℝ) ^ (-D') := mul_le_mul_of_nonneg_right he hW0
    refine h1.trans (NonAltBudget_absorb hNk (by positivity) ?_ hXN)
    have e : N ^ k * (d.W n : ℝ) ^ (-D') * N ^ k = N ^ (2 * k) * (d.W n : ℝ) ^ (-D') := by
      rw [hN2k]; ring
    rw [e]; exact he1
  -- T3: the drift term
  have T3 : Δ * ∑ j ∈ Finset.range (K n),
      (kappaNonAlt (d.L n) k κ ((d.W n : ℝ) ^ τ') (gridTime s v K n) (j + 1) (K n) *
          dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Φ n) D' +
        epsNonAlt k (gridTime s v K n) (j + 1) (K n) * (d.W n : ℝ) ^ (-D')) ≤
      P0 / 12 * (Φ n * X) + P0 / 12 * X := by
    have h := tbDriftNonAlt d n k hk κ τ' Γ Φ D' hE hs0 hsv hv1 hK1 hΓ0 hΦ hM1 hη
    rw [hXk] at h
    refine h.trans ?_
    have hS := hlog
    have hcoef : 0 ≤ NonAltBudget_cKap d n k κ τ' *
        ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) * X := by positivity
    have m1 : NonAltBudget_cKap d n k κ τ' * ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) * X *
        ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n j) ≤
        NonAltBudget_cKap d n k κ τ' * ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) * X * Ls :=
      mul_le_mul_of_nonneg_left hS hcoef
    have m2 : NonAltBudget_cKap d n k κ τ' * ((((k : ℝ) - 1) ^ 2 + 1) * (Γ n ^ 2 * Φ n)) * X *
        Ls = ((((k : ℝ) - 1) ^ 2 + 1) * NonAltBudget_cKap d n k κ τ' * (N ^ ε₁) ^ 2 * Ls) *
          (Φ n * X) := by rw [hΓ]; ring
    have m3 : ((((k : ℝ) - 1) ^ 2 + 1) * NonAltBudget_cKap d n k κ τ' * (N ^ ε₁) ^ 2 * Ls) *
        (Φ n * X) ≤ P0 / 12 * (Φ n * X) :=
      mul_le_mul_of_nonneg_right ha2 (by positivity)
    have hq : 0 ≤ NonAltBudget_cKap d n k κ τ' * N ^ k * (2 * (d.W n : ℝ) ^ (-D')) +
        N ^ k * (d.W n : ℝ) ^ (-D') := by positivity
    have f1 : ((K n : ℝ) * Δ) * (NonAltBudget_cKap d n k κ τ' * N ^ k * (2 * (d.W n : ℝ) ^ (-D')) +
        N ^ k * (d.W n : ℝ) ^ (-D')) ≤
        (2 * NonAltBudget_cKap d n k κ τ' + 1) * N ^ k * (d.W n : ℝ) ^ (-D') := by
      have := mul_le_mul_of_nonneg_right hKΔ1 hq
      linarith
    have f2 : (2 * NonAltBudget_cKap d n k κ τ' + 1) * N ^ k * (d.W n : ℝ) ^ (-D') ≤
        P0 / 12 * X := by
      refine NonAltBudget_absorb hNk (by positivity) ?_ hXN
      have e : (2 * NonAltBudget_cKap d n k κ τ' + 1) * N ^ k * (d.W n : ℝ) ^ (-D') * N ^ k =
          (2 * NonAltBudget_cKap d n k κ τ' + 1) * N ^ (2 * k) * (d.W n : ℝ) ^ (-D') := by
        rw [hN2k]; ring
      rw [e]; exact he2
    linarith
  -- T4: the quadratic-variation term
  have T4 : N ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ)) ≤
      P0 / 12 * (Λr * X) + P0 / 12 * X := by
    have h := tbQvNonAlt d n k κ τ' Γ Λ D'' a hE hs0 hsv hv1 hK1 hΓ0 hΛ0 hM1 hη
    have hSv : ∑ j ∈ Finset.range (K n), Δ / etaT (E n) (gridTime s v K n (j + 1)) ≤ Ls + 1 := by
      have hsucc := NonAltBudget_sum_succ_le (K := K n) (fun j => Δ / etaT (E n) (gridTime s v K n j))
        (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
      simp only [huK] at hsucc
      have hlast : Δ / etaT (E n) (v n) ≤ 1 := by
        rw [div_eq_mul_inv]
        have h1 : Δ * (etaT (E n) (v n))⁻¹ ≤ Δ * N := mul_le_mul_of_nonneg_left hη hΔ0
        linarith
      linarith
    set A := NonAltBudget_aQv d n k κ τ' with hAdef
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set Pq : ℝ := (k : ℝ) * A * (Ls + 1) with hPq
    set Qe : ℝ := (k : ℝ) * ((A + 1) * N ^ (2 * k) * (d.W n : ℝ) ^ (-D'')) with hQe
    have hPq0 : 0 ≤ Pq := by rw [hPq]; positivity
    have hQe0 : 0 ≤ Qe := by rw [hQe]; positivity
    have hΓX : 0 ≤ Γ n * X := mul_nonneg hΓ0 hX0'
    have hsum : ∑ j ∈ Finset.range (K n),
        (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ) ≤ Pq * (Γ n * X) ^ 2 * Λ n + Qe := by
      refine h.trans ?_
      rw [← inv_pow] at h
      have hc0 : 0 ≤ (k : ℝ) * A * (Γ n * (Γ n * Λ n)) * (X ^ 2) := by positivity
      have m1 := mul_le_mul_of_nonneg_left hSv hc0
      have m2 : ((K n : ℝ) * Δ) * Qe ≤ Qe := by
        have := mul_le_mul_of_nonneg_right hKΔ1 hQe0
        linarith
      have e : (k : ℝ) * A * (Γ n * (Γ n * Λ n)) * X ^ 2 * (Ls + 1) =
          Pq * (Γ n * X) ^ 2 * Λ n := by rw [hPq]; ring
      have e2 : ((scaleM (d.L n) (d.W n) (E n) (v n) ^ k)⁻¹) ^ 2 = X ^ 2 := by rw [hXk]
      rw [e2]
      linarith
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt (Pq * (Γ n * X) ^ 2 * Λ n + Qe) ≤
        Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n) + Real.sqrt Qe := by
      have hZ : 0 ≤ Pq * (Γ n * X) ^ 2 * Λ n := by positivity
      refine (NonAltBudget_sqrt_add_le hZ hQe0).trans ?_
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Pq * (Γ n * X) ^ 2),
        Real.sqrt_mul hPq0, Real.sqrt_sq hΓX]
    have hsΛ : Real.sqrt (Λ n) = Λr := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ N ^ ε := Real.rpow_nonneg hN0.le _
    have k1 : N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n)) ≤ P0 / 12 * (Λr * X) := by
      have e : N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n)) =
          (N ^ ε * (N ^ ε₁ * Real.sqrt Pq)) * (Λr * X) := by rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right ha3 (by positivity)
    have k2 : N ^ ε * Real.sqrt Qe ≤ P0 / 12 * X := by
      refine NonAltBudget_absorb hNk (by positivity) ?_ hXN
      have e : N ^ ε * Real.sqrt Qe * N ^ k = N ^ ε * (N ^ k * Real.sqrt Qe) := by ring
      rw [e]; exact he3
    calc N ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' (K n) a j : ℝ))
        ≤ N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n) + Real.sqrt Qe) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = N ^ ε * (Real.sqrt Pq * (Γ n * X) * Real.sqrt (Λ n)) + N ^ ε * Real.sqrt Qe := by ring
      _ ≤ _ := add_le_add k1 k2
  -- T5, T6
  have T5 : N ^ (-D_Y) ≤ P0 / 6 * X := by
    refine NonAltBudget_absorb hNk (by positivity) ?_ hXN
    rw [mul_comm]; exact he4
  have T6 : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (N ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤ P0 / 6 * X := by
    refine hR.trans (NonAltBudget_absorb hNk (by positivity) ?_ hXN)
    rw [mul_comm]; exact he5
  -- total
  unfold assembledRHSNonAlt
  have hPX : P0 * X ≤ P0 * (Λr * X) := by
    have : X ≤ Λr * X := le_mul_of_one_le_left hX0' hΛr1
    exact mul_le_mul_of_nonneg_left this hP0
  have e : P0 * (Λr + Φ n) * X = P0 * (Λr * X) + P0 * (Φ n * X) := by ring
  rw [e]
  have hΦX : 0 ≤ P0 * (Φ n * X) := mul_nonneg hP0 (mul_nonneg hΦ hX0')
  have hPX0 : 0 ≤ P0 * X := mul_nonneg hP0 hX0'
  simp only [hNdef, hΔdef] at T1 T2 T3 T4 T5 T6 hPX ⊢
  linarith [T1, T2, T3, T4, T5, T6, hPX, hΦX, hPX0]

end Budget

/-! ## 5b. The inputs `hlog`, `hR` are conclusions of proved theorems

`hlog` and `hR` of `budgetNonAlt` are, at each `n`, exactly the conclusions of
`sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le` (at `m = K n`): the theorem below states
this (the side conditions are those of the two theorems). -/

section MergedInputs

theorem NonAltBudget_merged_inputs (d : Sizes) {κ τ' τK C_K D_t : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (k : ℕ) [NeZero k] (hκ : 0 < κ) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK)
    (hDt : 0 ≤ D_t) (hk : 2 ≤ k) (hsize : SizeTendsto d) (hE : ∀ n, |E n| ≤ 2 - κ)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hrange : RangeCond d τ' v)
    (h1 : 8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K)
    (h2 : 3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K)
    (h3 : 2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K) (h4 : 1 - τ' < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (K n),
          gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ∧
      (∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
        ((d.size n : ℕ) : ℝ) ^ (-D_t)) := by
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  filter_upwards [sum_gridStep_div_etaT_le hτ' hE2 hs0 hsv hv1 hK0 hrange,
    sum_weighted_stepErrN_le d k hκ hτ' hτ'1 hτK hDt hk hsize hE hs0 hsv hv1 hK0 hrange h1 h2 h3
      h4 hKN] with n hn1 hn2
  exact ⟨hn1, hn2 (K n) le_rfl⟩

end MergedInputs

end RBM.Ind

end
