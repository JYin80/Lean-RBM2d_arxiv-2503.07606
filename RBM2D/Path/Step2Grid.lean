/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.StepBound
import RBM2D.Path.Bootstrap
import RBM2D.Path.StepArith

/-!
# The Step 2 stopping argument on the grid

Paper: arXiv:2503.07606, Step 2 of `lem:main_ind`: the stopping argument (`\label{51}`,
`\label{52}`) and the last display (`\label{53}`).

## Main declarations

* `GridStep2PTClose`, `GridStep2Eq53PT`, `GridStep2Eq53PTClose`, `StepECprimeAz`: the statements;
* `stepECprimeAz : StepECprimeAz`;
* `gridStep2PT : GridStep2PTClose d` and `gridStep2Eq53PT : GridStep2Eq53PTClose d`.

## Proof outline

Take `δ ≤ min(min(2c, τ)/400, 1)`, `ε = η = δ/8`, `D_g = max(D, 20 + 2/c) + 3/c`,
`K = gridK d D_g (D₁+1)`.  On the good event of `goodEvent_grid` (at `κ/2`), for `pathP`-a.e.
`ω`, `gridStepBoundPT` bounds `A_τ` at the stopping index `τ = gridTauFull`.  The four absolute
terms of the bracket are at most `cκ⁻¹ N^{-c₀/13}` (`stepEExponentsD`, `stepECprimeAz`, with
`r^29 ≤ M_t ≤ M_{u_τ}` from `scaleM_ge_pow29`, `scaleM_anti_ratio` and
`cκ N^{c₀} ≤ M_t` from `scaleM_etaT_of_range`); the others are `N^{7δ/8}` times a constant, so
`J*_{u_τ} ≤ 7 N^{7δ/8} (1 + r³) + 2` and `thrImproveD` (`ε_T = 7δ/8`, `C = 7`) gives
`J*_{u_τ}(H_τ) < Θ(u_τ)`.  Hence `τ = K` (`min_firstHit_eq_of_at`).  At the grid end,
`lk_le_of_jS` gives the profile `N^δ r⁴ 𝒯_{u,D}` (`GridStep2PT`), and the bound of
`gridStepBoundPT` at `τ = K`, with the additive initial term `N^{η+δ/16} r² W^{-D_g}` absorbed
into `W^{-D}` by the extra depth `3/c` (`Bandwidth`, `RangeCond`), gives the profile
`N^δ [r³ 1(|a-b| ≤ 6ℓ*_u) + 1] 𝒯_{u,D}` (`GridStep2Eq53PT`).

Both results are conditional: they take `GbEXPHypV3 d (κ/2) c τ`, `InitDecay`, `Step1LoopPT`,
`Step1WeakLawPT` as hypotheses, and are not the unconditional `Step2TargetNV3`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-! ## 1. The statements -/

/-- **The stopping argument of Step 2 on the grid** (`\label{51}`, `\label{52}`): under the
hypotheses of `Step2TargetNV3` (without `InitLocal`, which the argument does not use) and
`GbEXPHypV3 d (κ/2) c τ`, the grid hand-off `GridStep2PT` holds.  Used in:
`step2DecayPT_of_gridStep2PT` (in `Path/Bootstrap.lean`) inside `Step2ClosureV3`. -/
def GridStep2PTClose : Prop :=
  ∀ (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ),
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → RBM.Ind.SizeTendsto d →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    InitDecay d E s → Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    RBM.Green.GbEXPHypV3 d (κ / 2) c τ → GridStep2PT d E s t

/-- **The grid form of (53) with the near exponent `3`** (`\label{53}`).  The shape of
`GridStep2PT` with the profile `[(η_s/η_u)^3 1(|a-b|_L ≤ 6ℓ*_u) + 1] 𝒯_{u,D}(|a-b|_L)` of
`Step2Eq53PTV3`.  Used in: `step2Eq53PTV3_of_gridStep2Eq53PT` (the transfer to
`Step2Eq53PTV3`). -/
def GridStep2Eq53PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), ∀ u : ∀ n, TimeIcc s t n,
    ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D₁ > (0 : ℝ),
      ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
          ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ C) ∧
        ∀ᶠ n : ℕ in atTop, pathP d {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
          ((d.size n : ℕ) : ℝ) ^ δ *
              (((etaT (E n) (s n) / etaT (E n) (u n : ℝ)) ^ (3 : ℝ) *
                  (if (zdist2 (d.L n) (p.1 - p.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) (u n : ℝ)
                    then 1 else 0) + 1) *
                tailT (d.L n) (d.W n) (E n) D (u n : ℝ) (zdist2 (d.L n) (p.1 - p.2) : ℝ)) <
            lkErrMat (d.L n) (d.W n) (E n) (u n : ℝ)
              (pathH d s (fun n => (u n : ℝ)) K n (K n) ω) p.1 p.2}
          ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁))

/-- **The producer of `GridStep2Eq53PT`**: the hypotheses of `GridStep2PTClose` give
`GridStep2Eq53PT` (`\label{53}`, the last display of Step 2).  Used in: `Step2ClosureV3`
(through `step2Eq53PTV3_of_gridStep2Eq53PT`). -/
def GridStep2Eq53PTClose : Prop :=
  ∀ (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ),
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → RBM.Ind.SizeTendsto d →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    InitDecay d E s → Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    RBM.Green.GbEXPHypV3 d (κ / 2) c τ → GridStep2Eq53PT d E s t

/-- **The exponent arithmetic with the multipliers.**  In units of `N`-exponents, with
`M_t ≥ Im m · N^{c₀}` (`c₀ = min(2c, τ)`): the four absolute terms (the drift `LK×LK` term,
the far drift `G̃` term, and the martingale terms `N^δ r^{19/4} M^{-1/4}` and
`N^{3δ/2} r^6 M^{-1/2}`), with the multipliers `N^{6ε+η}` (`driftPoint`, `lossE2` at `Λ = N^ε`)
and `N^{δ/8+3ε+η}` (`azumaMm_le`), have exponent `≤ -c₀/13`; the relative multipliers are at most
`N^{7δ/8}`, so `thrImproveD` applies with `ε_T = 7δ/8`.  Used in the closing step of
`GridStep2PTClose` and `GridStep2Eq53PTClose`. -/
def StepECprimeAz : Prop :=
  ∀ c₀ δ ε η : ℝ, 0 < c₀ → 0 < δ → δ ≤ c₀ / 400 → 0 ≤ ε → ε ≤ δ / 8 → 0 ≤ η → η ≤ δ / 8 →
    c₀ / 13 ≤
        min (min (min (21 / 29 * c₀ - 2 * δ - 6 * ε - η) (11 / 58 * c₀ - 2 * δ - 6 * ε - η))
          (5 / 58 * c₀ - 9 / 8 * δ - 3 * ε - η)) (17 / 58 * c₀ - 13 / 8 * δ - 3 * ε - η) ∧
      max (max (6 * ε) (δ / 8 + 3 * ε)) (δ / 16) + η ≤ 7 / 8 * δ

/-! ## 2. The exponent arithmetic -/

/-- **`StepECprimeAz`** holds. -/
theorem stepECprimeAz : StepECprimeAz := by
  intro c₀ δ ε η hc hδ hδc hε hεδ hη hηδ
  refine ⟨?_, ?_⟩
  · have h1 : c₀ / 13 ≤ 21 / 29 * c₀ - 2 * δ - 6 * ε - η := by linarith
    have h2 : c₀ / 13 ≤ 11 / 58 * c₀ - 2 * δ - 6 * ε - η := by linarith
    have h3 : c₀ / 13 ≤ 5 / 58 * c₀ - 9 / 8 * δ - 3 * ε - η := by linarith
    have h4 : c₀ / 13 ≤ 17 / 58 * c₀ - 13 / 8 * δ - 3 * ε - η := by linarith
    exact le_min (le_min (le_min h1 h2) h3) h4
  · have : max (max (6 * ε) (δ / 8 + 3 * ε)) (δ / 16) ≤ 3 / 4 * δ :=
      max_le (max_le (by linarith) (by linarith)) (by linarith)
    linarith

/-! ## 3. Scalar helpers -/

/-- The bracket of `GridStepBoundPT` (without the factors `N^η` and `𝒯`), as a function of the
scalars `N`, `δ`, `ε`, `Az`, `r`, `M` and the near indicator `ind`. -/
private def Step2Grid_bracket (N δ ε Az r M ind : ℝ) : ℝ :=
  (N ^ (δ / 16) * r ^ 2 + Az * r ^ ((5 : ℝ) / 2) + N ^ (6 * ε) * r ^ 3) * ind +
    N ^ (δ / 16) +
    Az * (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4) +
      N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2) + 1) + 3 +
    N ^ (6 * ε) * (N ^ (2 * δ) * r ^ 8 * M⁻¹ + N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2))

/-- One absolute term: `N^a X ≤ cκ⁻¹ N^{-(c₀/13)}` from `X ≤ Mt^{-p}`, `cκ N^{c₀} ≤ Mt`,
`0 < p ≤ 1`, `cκ ≤ 1` and `a - p c₀ ≤ -(c₀/13)`. -/
private theorem Step2Grid_row {N Mt X cκ c₀ a p : ℝ} (hN : 1 ≤ N) (hcκ : 0 < cκ)
    (hcκ1 : cκ ≤ 1) (hMtc : cκ * N ^ c₀ ≤ Mt) (hp1 : p ≤ 1) (hp0 : 0 ≤ p)
    (hX : X ≤ Mt ^ (-p)) (ha : a - p * c₀ ≤ -(c₀ / 13)) :
    N ^ a * X ≤ cκ⁻¹ * N ^ (-(c₀ / 13)) := by
  have hN0 : 0 < N := by linarith
  have hNc : 0 < N ^ c₀ := Real.rpow_pos_of_pos hN0 _
  have hbase : 0 < cκ * N ^ c₀ := mul_pos hcκ hNc
  have h1 : Mt ^ (-p) ≤ (cκ * N ^ c₀) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hbase hMtc (by linarith)
  have h2 : (cκ * N ^ c₀) ^ (-p) = cκ ^ (-p) * N ^ (c₀ * (-p)) := by
    rw [Real.mul_rpow hcκ.le hNc.le, Real.rpow_mul hN0.le]
  have h3 : cκ ^ (-p) ≤ cκ⁻¹ := by
    rw [Real.rpow_neg hcκ.le, ← Real.inv_rpow hcκ.le]
    calc cκ⁻¹ ^ p ≤ cκ⁻¹ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hcκ).2 hcκ1) hp1
      _ = cκ⁻¹ := Real.rpow_one _
  calc N ^ a * X ≤ N ^ a * (cκ ^ (-p) * N ^ (c₀ * (-p))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN0.le _)
        exact hX.trans (h1.trans h2.le)
    _ = cκ ^ (-p) * N ^ (a + c₀ * (-p)) := by rw [Real.rpow_add hN0]; ring
    _ ≤ cκ⁻¹ * N ^ (-(c₀ / 13)) := by
        apply mul_le_mul h3 _ (Real.rpow_nonneg hN0.le _) (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hN
        linarith


/-- **The bracket bound.**  The bracket of `GridStepBoundPT` (with `ε = η = δ/8`) times `N^η` is
at most `6 N^{7δ/8} (r³ ind + 1)` (`ind` the near indicator): the four absolute terms are each at
most `cκ⁻¹ N^{-c₀/13}` (`stepEExponentsD`, `stepECprimeAz`; `4 cκ⁻¹ ≤ N^{c₀/13}` makes their sum
at most `1`), the others are `N^{7δ/8}` times a constant. -/
private theorem Step2Grid_bracket_le {N r M Mt rt Az cκ c₀ δ ind : ℝ}
    (hN : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδc : δ ≤ c₀ / 400)
    (hr1 : 1 ≤ r) (hrt : r ≤ rt) (hrt29 : rt ^ 29 ≤ Mt) (hMt1 : 1 ≤ Mt) (hMtM : Mt ≤ M)
    (hcκ : 0 < cκ) (hcκ1 : cκ ≤ 1) (hMtc : cκ * N ^ c₀ ≤ Mt)
    (hbig : 4 * cκ⁻¹ ≤ N ^ (c₀ / 13))
    (hAz : Az ≤ N ^ (δ / 8 + 3 * (δ / 8))) (hind0 : 0 ≤ ind) :
    N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az r M ind ≤
      6 * N ^ (7 * δ / 8) * (r ^ 3 * ind + 1) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hpow : ∀ x y : ℝ, x ≤ y → N ^ x ≤ N ^ y := fun x y h =>
    Real.rpow_le_rpow_of_exponent_le hN h
  have hmul : ∀ x y : ℝ, N ^ x * N ^ y = N ^ (x + y) := fun x y => (Real.rpow_add hN0 x y).symm
  have hNnn : ∀ x : ℝ, 0 ≤ N ^ x := fun x => Real.rpow_nonneg hN0.le x
  have hadd3 : ∀ x y z : ℝ, N ^ (x + y + z) = N ^ x * N ^ y * N ^ z := fun x y z => by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  -- the exponent arithmetic
  obtain ⟨E1, E2, E3, E4⟩ := stepEExponentsD rt r M Mt hr1 hrt hMt1 hMtM hrt29
  have hP := (stepECprimeAz c₀ δ (δ / 8) (δ / 8) hc₀ hδ hδc (by positivity) le_rfl
    (by positivity) le_rfl).1
  have hA : c₀ / 13 ≤ 21 / 29 * c₀ - 2 * δ - 6 * (δ / 8) - δ / 8 :=
    hP.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hB : c₀ / 13 ≤ 11 / 58 * c₀ - 2 * δ - 6 * (δ / 8) - δ / 8 :=
    hP.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hC : c₀ / 13 ≤ 5 / 58 * c₀ - 9 / 8 * δ - 3 * (δ / 8) - δ / 8 :=
    hP.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hD : c₀ / 13 ≤ 17 / 58 * c₀ - 13 / 8 * δ - 3 * (δ / 8) - δ / 8 :=
    hP.trans (min_le_right _ _)
  have F1 : r ^ 8 * M⁻¹ ≤ Mt ^ (-(21 / 29 : ℝ)) := by
    have h : (-(21 : ℝ) / 29) = -(21 / 29) := by norm_num
    rwa [h] at E1
  have F2 : r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2) ≤ Mt ^ (-(11 / 58 : ℝ)) := by
    have h : (-(11 : ℝ) / 58) = -(11 / 58) := by norm_num
    rw [h] at E2
    have h2 : M ^ (-(1 : ℝ) / 2) = M⁻¹ ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hM0.le, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by norm_num,
        Real.rpow_neg hM0.le]
    rwa [h2] at E2
  have F3 : r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4) ≤ Mt ^ (-(5 / 58 : ℝ)) := by
    have h : (-(5 : ℝ) / 58) = -(5 / 58) := by norm_num
    rw [h] at E3
    have e : r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4) =
        Real.sqrt (r ^ ((19 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg hM0.le _),
        ← Real.rpow_mul hr0, ← Real.rpow_mul hM0.le, Real.inv_rpow hM0.le,
        ← Real.rpow_neg hM0.le]
      congr 2 <;> norm_num
    rwa [e]
  have F4 : r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2) ≤ Mt ^ (-(17 / 58 : ℝ)) := by
    have h : (-(17 : ℝ) / 58) = -(17 / 58) := by norm_num
    rw [h] at E4
    have e : r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2) = Real.sqrt (r ^ 12 * M⁻¹) := by
      rw [Real.sqrt_mul (by positivity), show r ^ 12 = (r ^ 6) ^ 2 by ring,
        Real.sqrt_sq (pow_nonneg hr0 6), Real.sqrt_eq_rpow]
    rwa [e]
  -- the four absolute terms
  have R1 : N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * (N ^ (2 * δ) * r ^ 8 * M⁻¹)) ≤
      cκ⁻¹ * N ^ (-(c₀ / 13)) := by
    have e : N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * (N ^ (2 * δ) * r ^ 8 * M⁻¹)) =
        N ^ (δ / 8 + 6 * (δ / 8) + 2 * δ) * (r ^ 8 * M⁻¹) := by
      rw [hadd3]; ring
    rw [e]
    exact Step2Grid_row hN hcκ hcκ1 hMtc (by norm_num) (by norm_num) F1 (by linarith)
  have R2 : N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * (N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2))) ≤
      cκ⁻¹ * N ^ (-(c₀ / 13)) := by
    have e : N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * (N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2))) =
        N ^ (δ / 8 + 6 * (δ / 8) + 2 * δ) * (r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2)) := by
      rw [hadd3]; ring
    rw [e]
    exact Step2Grid_row hN hcκ hcκ1 hMtc (by norm_num) (by norm_num) F2 (by linarith)
  have R3 : N ^ (δ / 8) * (Az * (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4))) ≤
      cκ⁻¹ * N ^ (-(c₀ / 13)) := by
    have e : N ^ (δ / 8) * (N ^ (δ / 8 + 3 * (δ / 8)) *
        (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4))) =
        N ^ (δ / 8 + (δ / 8 + 3 * (δ / 8)) + δ) *
          (r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4)) := by
      rw [hadd3]; ring
    calc N ^ (δ / 8) * (Az * (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4)))
        ≤ N ^ (δ / 8) * (N ^ (δ / 8 + 3 * (δ / 8)) *
            (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4))) := by
          apply mul_le_mul_of_nonneg_left _ (hNnn _)
          exact mul_le_mul_of_nonneg_right hAz (by positivity)
      _ = _ := e
      _ ≤ _ := Step2Grid_row hN hcκ hcκ1 hMtc (by norm_num) (by norm_num) F3 (by linarith)
  have R4 : N ^ (δ / 8) * (Az * (N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2))) ≤
      cκ⁻¹ * N ^ (-(c₀ / 13)) := by
    have e : N ^ (δ / 8) * (N ^ (δ / 8 + 3 * (δ / 8)) *
        (N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2))) =
        N ^ (δ / 8 + (δ / 8 + 3 * (δ / 8)) + 3 * δ / 2) *
          (r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2)) := by
      rw [hadd3]; ring
    calc N ^ (δ / 8) * (Az * (N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2)))
        ≤ N ^ (δ / 8) * (N ^ (δ / 8 + 3 * (δ / 8)) *
            (N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (hNnn _)
          exact mul_le_mul_of_nonneg_right hAz (by positivity)
      _ = _ := e
      _ ≤ _ := Step2Grid_row hN hcκ hcκ1 hMtc (by norm_num) (by norm_num) F4 (by linarith)
  -- the near part
  have Nn1 : N ^ (δ / 8) * (N ^ (δ / 16) * r ^ 2) ≤ N ^ (7 * δ / 8) * r ^ 3 := by
    calc N ^ (δ / 8) * (N ^ (δ / 16) * r ^ 2) = (N ^ (δ / 8) * N ^ (δ / 16)) * r ^ 2 := by ring
      _ = N ^ (δ / 8 + δ / 16) * r ^ 2 := by rw [hmul]
      _ ≤ N ^ (7 * δ / 8) * r ^ 3 :=
          mul_le_mul (hpow _ _ (by linarith)) (pow_le_pow_right₀ hr1 (by norm_num))
            (by positivity) (hNnn _)
  have Nn2 : N ^ (δ / 8) * (Az * r ^ ((5 : ℝ) / 2)) ≤ N ^ (7 * δ / 8) * r ^ 3 := by
    have hr52 : r ^ ((5 : ℝ) / 2) ≤ r ^ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le hr1 (show ((5 : ℝ) / 2) ≤ ((3 : ℕ) : ℝ) by norm_num)
      rwa [Real.rpow_natCast] at this
    calc N ^ (δ / 8) * (Az * r ^ ((5 : ℝ) / 2))
        ≤ N ^ (δ / 8) * (N ^ (δ / 8 + 3 * (δ / 8)) * r ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (hNnn _)
          exact mul_le_mul hAz hr52 (by positivity) (hNnn _)
      _ = N ^ (δ / 8 + (δ / 8 + 3 * (δ / 8))) * r ^ 3 := by
          rw [Real.rpow_add hN0 (δ / 8) (δ / 8 + 3 * (δ / 8))]; ring
      _ ≤ N ^ (7 * δ / 8) * r ^ 3 :=
          mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) (by positivity)
  have Nn3 : N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * r ^ 3) = N ^ (7 * δ / 8) * r ^ 3 := by
    have e : δ / 8 + 6 * (δ / 8) = 7 * δ / 8 := by ring
    rw [← mul_assoc, hmul, e]
  have hnear : N ^ (δ / 8) * (N ^ (δ / 16) * r ^ 2 + Az * r ^ ((5 : ℝ) / 2) +
      N ^ (6 * (δ / 8)) * r ^ 3) ≤ 3 * (N ^ (7 * δ / 8) * r ^ 3) := by
    rw [mul_add, mul_add]; linarith [Nn1, Nn2, Nn3.le]
  -- the far part
  have Ff1 : N ^ (δ / 8) * N ^ (δ / 16) ≤ N ^ (7 * δ / 8) := by
    rw [hmul]; exact hpow _ _ (by linarith)
  have Ff2 : N ^ (δ / 8) * Az ≤ N ^ (7 * δ / 8) := by
    calc N ^ (δ / 8) * Az ≤ N ^ (δ / 8) * N ^ (δ / 8 + 3 * (δ / 8)) :=
          mul_le_mul_of_nonneg_left hAz (hNnn _)
      _ = N ^ (δ / 8 + (δ / 8 + 3 * (δ / 8))) := hmul _ _
      _ ≤ N ^ (7 * δ / 8) := hpow _ _ (by linarith)
  have Ff3 : 3 * N ^ (δ / 8) ≤ 3 * N ^ (7 * δ / 8) := by
    linarith [hpow (δ / 8) (7 * δ / 8) (by linarith)]
  have hsmall : 4 * (cκ⁻¹ * N ^ (-(c₀ / 13))) ≤ 1 := by
    have h1 : N ^ (-(c₀ / 13)) = (N ^ (c₀ / 13))⁻¹ := Real.rpow_neg hN0.le _
    have hpos : 0 < N ^ (c₀ / 13) := Real.rpow_pos_of_pos hN0 _
    rw [h1, show 4 * (cκ⁻¹ * (N ^ (c₀ / 13))⁻¹) = (4 * cκ⁻¹) / N ^ (c₀ / 13) by ring]
    exact (div_le_one hpos).2 hbig
  have hN78 : 1 ≤ N ^ (7 * δ / 8) := Real.one_le_rpow hN (by positivity)
  have hPQ : 0 ≤ N ^ (7 * δ / 8) * (r ^ 3 * ind) := by positivity
  have expand : N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az r M ind =
      (N ^ (δ / 8) * (N ^ (δ / 16) * r ^ 2 + Az * r ^ ((5 : ℝ) / 2) +
        N ^ (6 * (δ / 8)) * r ^ 3)) * ind
      + N ^ (δ / 8) * N ^ (δ / 16)
      + (N ^ (δ / 8) * (Az * (N ^ δ * r ^ ((19 : ℝ) / 4) * M⁻¹ ^ ((1 : ℝ) / 4)))
        + N ^ (δ / 8) * (Az * (N ^ (3 * δ / 2) * r ^ 6 * M⁻¹ ^ ((1 : ℝ) / 2)))
        + N ^ (δ / 8) * Az)
      + 3 * N ^ (δ / 8)
      + (N ^ (δ / 8) * (N ^ (6 * (δ / 8)) * (N ^ (2 * δ) * r ^ 8 * M⁻¹))
        + N ^ (δ / 8) * (N ^ (6 * (δ / 8)) *
          (N ^ (2 * δ) * r ^ 9 * M⁻¹ ^ ((1 : ℝ) / 2)))) := by
    unfold Step2Grid_bracket; ring
  rw [expand]
  have hnind := mul_le_mul_of_nonneg_right hnear hind0
  linarith [hnind, Ff1, Ff2, Ff3, R1, R2, R3, R4, hsmall, hN78, hPQ]


/-- The bracket bound at a time `v ∈ [s, t]`, in terms of the Step 2 scales: `r = η_s/η_v`,
`M = M_v`; the inputs are the step condition `con_st_ind` and the lower bound
`cκ N^{c₀} ≤ M_t`. -/
private theorem Step2Grid_pt_bound {L W : ℕ} {E s v t N Az cκ c₀ δ ind : ℝ}
    (hL1 : 1 ≤ L) (hW1 : 1 ≤ W) (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1) (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30)
    (hN : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδc : δ ≤ c₀ / 400)
    (hcκ : 0 < cκ) (hcκ1 : cκ ≤ 1) (hMtc : cκ * N ^ c₀ ≤ scaleM L W E t)
    (hbig : 4 * cκ⁻¹ ≤ N ^ (c₀ / 13)) (hAz : Az ≤ N ^ (δ / 8 + 3 * (δ / 8)))
    (hind0 : 0 ≤ ind) :
    N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az (etaT E s / etaT E v) (scaleM L W E v) ind ≤
      6 * N ^ (7 * δ / 8) * ((etaT E s / etaT E v) ^ 3 * ind + 1) := by
  have hs1 : s < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have hr : etaT E s / etaT E v = (1 - s) / (1 - v) := etaT_div_etaT hE hs1 hv1
  rw [hr]
  have h1v : 0 < 1 - v := by linarith
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hr1 : 1 ≤ (1 - s) / (1 - v) := by rw [le_div_iff₀ h1v]; linarith
  have hrt : (1 - s) / (1 - v) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_left h1s.le h1t (by linarith)
  have hrt29 : ((1 - s) / (1 - t)) ^ 29 ≤ scaleM L W E t :=
    scaleM_ge_pow29 hL1 hW1 hE hs0 (hsv.trans hvt) le_rfl ht1 hstep
  have hMtM : scaleM L W E t ≤ scaleM L W E v := (scaleM_anti_ratio hL1 hE hvt ht1).1
  have hMt1 : 1 ≤ scaleM L W E t := by
    have hNc : N ^ (c₀ / 13) ≤ N ^ c₀ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have h4 : 4 ≤ cκ * N ^ c₀ := by
      have h5 : 4 * cκ⁻¹ ≤ N ^ c₀ := hbig.trans hNc
      calc (4 : ℝ) = cκ * (4 * cκ⁻¹) := by field_simp
        _ ≤ cκ * N ^ c₀ := mul_le_mul_of_nonneg_left h5 hcκ.le
    linarith
  exact Step2Grid_bracket_le hN hc₀ hδ hδc hr1 hrt hrt29 hMt1 hMtM hcκ hcκ1 hMtc hbig hAz hind0


/-- `W^{-D} ≤ 𝒯_{u,D}(ℓ)`. -/
private theorem Step2Grid_W_le_tailT {L W : ℕ} {E D u ℓ : ℝ} :
    (W : ℝ) ^ (-D) ≤ tailT L W E D u ℓ := by
  unfold tailT
  have : 0 ≤ (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (ℓ / ellT L u)) :=
    mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le
  linarith

/-- `𝒯_{u,D'} ≤ 𝒯_{u,D}` for `D ≤ D'` and `1 ≤ W` (as in `lk_le_of_jS`). -/
private theorem Step2Grid_tailT_mono {L W : ℕ} {E D D' u ℓ : ℝ} (hW : 1 ≤ W) (hDD : D ≤ D') :
    tailT L W E D' u ℓ ≤ tailT L W E D u ℓ := by
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold tailT
  have : (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW' (by linarith)
  linarith

/-- `J* < N^δ r⁴` from a pointwise bound of the type of `GridStepBoundPT`: the bracket bound,
`W^{-D_g} ≤ 𝒯` and `thrImproveD` with `ε_T = 7δ/8`, `C = 7`. -/
private theorem Step2Grid_jstar_lt {L W : ℕ} [NeZero L] [NeZero W]
    {E s v t N Az cκ c₀ δ Dg : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hL1 : 1 ≤ L) (hW1 : 1 ≤ W) (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1) (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30)
    (hN : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδc : δ ≤ c₀ / 400)
    (hcκ : 0 < cκ) (hcκ1 : cκ ≤ 1) (hMtc : cκ * N ^ c₀ ≤ scaleM L W E t)
    (hbig : 4 * cκ⁻¹ ≤ N ^ (c₀ / 13)) (hbig2 : 28 < N ^ (δ / 8))
    (hAz : Az ≤ N ^ (δ / 8 + 3 * (δ / 8)))
    (hpt : ∀ a b : Z2 L, lkErrMat L W E v M a b ≤
      N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az (etaT E s / etaT E v) (scaleM L W E v)
          (if (zdist2 L (a - b) : ℝ) ≤ 6 * ellStar L W v then 1 else 0) *
        tailT L W E Dg v (zdist2 L (a - b) : ℝ) +
      N ^ (δ / 8 + δ / 16) * (etaT E s / etaT E v) ^ 2 * (W : ℝ) ^ (-Dg)) :
    jStarMat L W E Dg v M < N ^ δ * (etaT E s / etaT E v) ^ 4 := by
  have hN0 : 0 < N := by linarith
  have hs1 : s < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have hr : etaT E s / etaT E v = (1 - s) / (1 - v) := etaT_div_etaT hE hs1 hv1
  have h1v : 0 < 1 - v := by linarith
  have hr1 : 1 ≤ etaT E s / etaT E v := by rw [hr, le_div_iff₀ h1v]; linarith
  set r : ℝ := etaT E s / etaT E v with hrdef
  have hr0 : 0 ≤ r := by linarith
  set P : ℝ := N ^ (7 * δ / 8) with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hN0.le _
  have hpow : ∀ x y : ℝ, x ≤ y → N ^ x ≤ N ^ y := fun x y h =>
    Real.rpow_le_rpow_of_exponent_le hN h
  have hJ : jStarMat L W E Dg v M ≤ 7 * P * (1 + r ^ 3) + 2 := by
    unfold jStarMat
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 L × Z2 L => lkErrMat L W E v M p.1 p.2 /
          tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ)) ≤ 7 * P * (1 + r ^ 3) := by
      apply Finset.sup'_le
      intro p _
      have hT0 : 0 < tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) := tailT_pos hW1 L E Dg v _
      rw [div_le_iff₀ hT0]
      set ind : ℝ := if (zdist2 L (p.1 - p.2) : ℝ) ≤ 6 * ellStar L W v then 1 else 0 with hind
      have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
      have hind1 : ind ≤ 1 := by rw [hind]; split_ifs <;> norm_num
      have hbr := Step2Grid_pt_bound hL1 hW1 hE hs0 hsv hvt ht1 hstep hN hc₀ hδ hδc hcκ hcκ1 hMtc
        hbig hAz hind0
      have h := hpt p.1 p.2
      rw [← hind] at h
      have hWT := Step2Grid_W_le_tailT (L := L) (W := W) (E := E) (D := Dg) (u := v)
        (ℓ := (zdist2 L (p.1 - p.2) : ℝ))
      have e1 : N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az r (scaleM L W E v) ind *
          tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) ≤
          6 * P * (r ^ 3 * ind + 1) * tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) :=
        mul_le_mul_of_nonneg_right hbr hT0.le
      have e2 : N ^ (δ / 8 + δ / 16) * r ^ 2 * (W : ℝ) ^ (-Dg) ≤
          N ^ (δ / 8 + δ / 16) * r ^ 2 * tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) :=
        mul_le_mul_of_nonneg_left hWT (by positivity)
      have e3 : N ^ (δ / 8 + δ / 16) * r ^ 2 ≤ P * r ^ 3 :=
        mul_le_mul (hpow _ _ (by linarith)) (pow_le_pow_right₀ hr1 (by norm_num))
          (by positivity) hP0
      have e4 : 6 * P * (r ^ 3 * ind + 1) + N ^ (δ / 8 + δ / 16) * r ^ 2 ≤ 7 * P * (1 + r ^ 3) := by
        have h1 : r ^ 3 * ind ≤ r ^ 3 := by
          calc r ^ 3 * ind ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hind1 (by positivity)
            _ = r ^ 3 := mul_one _
        nlinarith [mul_le_mul_of_nonneg_left h1 hP0, hP0, e3]
      calc lkErrMat L W E v M p.1 p.2
          ≤ _ := h
        _ ≤ 6 * P * (r ^ 3 * ind + 1) * tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) +
            N ^ (δ / 8 + δ / 16) * r ^ 2 * tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) :=
          add_le_add e1 e2
        _ = (6 * P * (r ^ 3 * ind + 1) + N ^ (δ / 8 + δ / 16) * r ^ 2) *
            tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) := by ring
        _ ≤ 7 * P * (1 + r ^ 3) * tailT L W E Dg v (zdist2 L (p.1 - p.2) : ℝ) :=
          mul_le_mul_of_nonneg_right e4 hT0.le
    linarith
  have h4 : 4 * (7 : ℝ) < N ^ (δ - 7 * δ / 8) := by
    have : δ - 7 * δ / 8 = δ / 8 := by ring
    rw [this]; linarith
  exact thrImproveD N r 7 (7 * δ / 8) δ _ hN hr1 (by norm_num) (by positivity) h4 hJ


/-- The ratio `(1-s)/(1-u)` is nonnegative and at most `N^{1-τ'}` when `1 - t ≥ N^{-1+τ'}`
(copy of the private `bootstrap_ratio_le`, `RBM2D/Path/Bootstrap.lean`). -/
private theorem Step2Grid_ratio_le {s u t N τ' : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (hut : u ≤ t)
    (ht1 : t < 1) (hN : 0 < N) (hR : N ^ (-1 + τ') ≤ 1 - t) :
    0 ≤ (1 - s) / (1 - u) ∧ (1 - s) / (1 - u) ≤ N ^ (1 - τ') := by
  have h1u : 0 < 1 - u := by linarith
  refine ⟨div_nonneg (by linarith) h1u.le, ?_⟩
  rw [div_le_iff₀ h1u]
  calc 1 - s ≤ 1 := by linarith
    _ = N ^ (1 - τ') * N ^ (-1 + τ') := by
        rw [← Real.rpow_add hN]; norm_num
    _ ≤ N ^ (1 - τ') * (1 - u) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hN.le _)

/-- The absorption of the additive initial term: `N^e r² W^{-(D₀+3/c)} ≤ W^{-D}` for `r ≤ N`,
`N^c ≤ W`, `D ≤ D₀`, `e ≤ 1`. -/
private theorem Step2Grid_absorb {N W r c D D₀ e : ℝ} (hN : 1 ≤ N) (hW : 1 ≤ W) (hc : 0 < c)
    (hWN : N ^ c ≤ W) (hr0 : 0 ≤ r) (hrN : r ≤ N) (hDD : D ≤ D₀) (he : e ≤ 1) :
    N ^ e * r ^ 2 * W ^ (-(D₀ + 3 / c)) ≤ W ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have hq : W ^ (-(3 / c)) ≤ N ^ (-(3 : ℝ)) := by
    have h3 : 0 < 3 / c := by positivity
    have h1 : W ^ (-(3 / c)) ≤ (N ^ c) ^ (-(3 / c)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 c) hWN (by linarith)
    rw [← Real.rpow_mul hN0.le] at h1
    have h2 : c * -(3 / c) = -(3 : ℝ) := by field_simp
    rwa [h2] at h1
  have hsplit : W ^ (-(D₀ + 3 / c)) = W ^ (-D₀) * W ^ (-(3 / c)) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have hD : W ^ (-D₀) ≤ W ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have hr2 : r ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hr0 hrN 2
  have hW0' : 0 ≤ W ^ (-D₀) := Real.rpow_nonneg hW0.le _
  have hNe : 0 ≤ N ^ e := Real.rpow_nonneg hN0.le _
  have hkey : N ^ e * r ^ 2 * N ^ (-(3 : ℝ)) ≤ 1 := by
    calc N ^ e * r ^ 2 * N ^ (-(3 : ℝ)) ≤ N ^ e * N ^ 2 * N ^ (-(3 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
          exact mul_le_mul_of_nonneg_left hr2 hNe
      _ = N ^ (e + 2 + -(3 : ℝ)) := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_two]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  calc N ^ e * r ^ 2 * W ^ (-(D₀ + 3 / c))
      = (N ^ e * r ^ 2) * (W ^ (-D₀) * W ^ (-(3 / c))) := by rw [hsplit]
    _ ≤ (N ^ e * r ^ 2) * (W ^ (-D₀) * N ^ (-(3 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hq hW0'
    _ = (N ^ e * r ^ 2 * N ^ (-(3 : ℝ))) * W ^ (-D₀) := by ring
    _ ≤ 1 * W ^ (-D₀) := mul_le_mul_of_nonneg_right hkey hW0'
    _ = W ^ (-D₀) := one_mul _
    _ ≤ W ^ (-D) := hD

/-- The near-exponent-3 form (53): from a pointwise bound of the type of `GridStepBoundPT` at
depth `D_g = D₀ + 3/c`, `lkErr ≤ N^δ [(η_s/η_v)^3 1(near) + 1] 𝒯_{v,D}`. -/
private theorem Step2Grid_lk_le {L W : ℕ} [NeZero L] [NeZero W]
    {E s v t N Az cκ c₀ δ c τ D D₀ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hL1 : 1 ≤ L) (hW1 : 1 ≤ W) (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1) (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30)
    (hN : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδc : δ ≤ c₀ / 400) (hδ1 : δ ≤ 1)
    (hcκ : 0 < cκ) (hcκ1 : cκ ≤ 1) (hMtc : cκ * N ^ c₀ ≤ scaleM L W E t)
    (hbig : 4 * cκ⁻¹ ≤ N ^ (c₀ / 13)) (hbig2 : 28 < N ^ (δ / 8))
    (hAz : Az ≤ N ^ (δ / 8 + 3 * (δ / 8)))
    (hc : 0 < c) (hτ : 0 < τ) (hWN : N ^ c ≤ (W : ℝ)) (hrange : N ^ (-1 + τ) ≤ 1 - t)
    (hDD : D ≤ D₀)
    (hpt : ∀ a b : Z2 L, lkErrMat L W E v M a b ≤
      N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az (etaT E s / etaT E v) (scaleM L W E v)
          (if (zdist2 L (a - b) : ℝ) ≤ 6 * ellStar L W v then 1 else 0) *
        tailT L W E (D₀ + 3 / c) v (zdist2 L (a - b) : ℝ) +
      N ^ (δ / 8 + δ / 16) * (etaT E s / etaT E v) ^ 2 * (W : ℝ) ^ (-(D₀ + 3 / c)))
    (a b : Z2 L) :
    lkErrMat L W E v M a b ≤ N ^ δ * (((etaT E s / etaT E v) ^ (3 : ℝ) *
        (if (zdist2 L (a - b) : ℝ) ≤ 6 * ellStar L W v then 1 else 0) + 1) *
      tailT L W E D v (zdist2 L (a - b) : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hst : s ≤ t := hsv.trans hvt
  have hs1 : s < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have hr : etaT E s / etaT E v = (1 - s) / (1 - v) := etaT_div_etaT hE hs1 hv1
  have h1v : 0 < 1 - v := by linarith
  have hr1 : 1 ≤ etaT E s / etaT E v := by rw [hr, le_div_iff₀ h1v]; linarith
  have hrN : etaT E s / etaT E v ≤ N := by
    rw [hr]
    calc (1 - s) / (1 - v) ≤ N ^ (1 - τ) := (Step2Grid_ratio_le hs0 hst hvt ht1 hN0 hrange).2
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N := Real.rpow_one N
  set r : ℝ := etaT E s / etaT E v with hrdef
  have hr0 : 0 ≤ r := by linarith
  set P : ℝ := N ^ (7 * δ / 8) with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN (by positivity)
  have hr3 : r ^ (3 : ℝ) = r ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr3]
  set ind : ℝ := if (zdist2 L (a - b) : ℝ) ≤ 6 * ellStar L W v then 1 else 0 with hind
  have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
  have hbr := Step2Grid_pt_bound hL1 hW1 hE hs0 hsv hvt ht1 hstep hN hc₀ hδ hδc hcκ hcκ1 hMtc
    hbig hAz hind0
  have h := hpt a b
  rw [← hind] at h
  set T : ℝ := tailT L W E D v (zdist2 L (a - b) : ℝ) with hT
  have hT0 : 0 < T := tailT_pos hW1 L E D v _
  have hTmono : tailT L W E (D₀ + 3 / c) v (zdist2 L (a - b) : ℝ) ≤ T :=
    Step2Grid_tailT_mono hW1 (by
      have : 0 < 3 / c := by positivity
      linarith)
  have e1 : N ^ (δ / 8) * Step2Grid_bracket N δ (δ / 8) Az r (scaleM L W E v) ind *
      tailT L W E (D₀ + 3 / c) v (zdist2 L (a - b) : ℝ) ≤ 6 * P * (r ^ 3 * ind + 1) * T :=
    calc _ ≤ 6 * P * (r ^ 3 * ind + 1) * tailT L W E (D₀ + 3 / c) v (zdist2 L (a - b) : ℝ) :=
          mul_le_mul_of_nonneg_right hbr (tailT_pos hW1 L E _ v _).le
      _ ≤ 6 * P * (r ^ 3 * ind + 1) * T :=
          mul_le_mul_of_nonneg_left hTmono (by positivity)
  have e2 : N ^ (δ / 8 + δ / 16) * r ^ 2 * (W : ℝ) ^ (-(D₀ + 3 / c)) ≤ T :=
    calc _ ≤ (W : ℝ) ^ (-D) :=
          Step2Grid_absorb hN (by exact_mod_cast hW1) hc hWN hr0 hrN hDD (by linarith)
      _ ≤ T := Step2Grid_W_le_tailT
  have hq1 : 1 ≤ r ^ 3 * ind + 1 := by
    have : 0 ≤ r ^ 3 * ind := by positivity
    linarith
  have hNδ : N ^ δ = N ^ (δ / 8) * P := by
    rw [hPdef, ← Real.rpow_add hN0]; congr 1; ring
  have hNδ' : 6 * P + 1 ≤ N ^ δ := by
    rw [hNδ]; nlinarith
  calc lkErrMat L W E v M a b ≤ _ := h
    _ ≤ 6 * P * (r ^ 3 * ind + 1) * T + T := add_le_add e1 e2
    _ ≤ (6 * P + 1) * ((r ^ 3 * ind + 1) * T) := by nlinarith [mul_pos hT0 hT0, hP1, hT0.le]
    _ ≤ N ^ δ * ((r ^ 3 * ind + 1) * T) :=
        mul_le_mul_of_nonneg_right hNδ' (by positivity)


/-- `c_κ = √(κ(4-κ))/2 ≤ Im m(E)` under `|E| ≤ 2 - κ` (copy of the private
`GoodEventClose_im_ge`, `RBM2D/Path/GoodEventClose.lean`); and `c_κ ≤ 1`. -/
private theorem Step2Grid_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 ∧ Real.sqrt (κ * (4 - κ)) / 2 ≤ 1 ∧
      Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hpos : 0 < κ * (4 - κ) := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have h : Real.sqrt (κ * (4 - κ)) ≤ 2 := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by nlinarith [sq_nonneg (κ - 2)]⟩
    linarith
  · rw [spectralM_im]
    have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hE 2
    have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt this
    linarith

/-- The conclusion at the grid end `u = u_K`: (i) `J*_{u,D_g}(H_K) < Θ(u)` and (ii) the
near-exponent-3 profile `N^δ [(η_s/η_u)^3 1(|a-b| ≤ 6ℓ*_u) + 1] 𝒯_{u,D}` for every label. -/
private def Step2Grid_concl (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (δ D Dg : ℝ) (n : ℕ)
    (ω : PathΩ d) : Prop :=
  jStarMat (d.L n) (d.W n) (E n) Dg (v n) (pathH d s v K n (K n) ω) < thr d E s δ n (v n) ∧
  ∀ a : Z2 (d.L n) × Z2 (d.L n),
    lkErrMat (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) a.1 a.2 ≤
      ((d.size n : ℕ) : ℝ) ^ δ * (((etaT (E n) (s n) / etaT (E n) (v n)) ^ (3 : ℝ) *
        (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) (v n) then 1 else 0)
          + 1) *
        tailT (d.L n) (d.W n) (E n) D (v n) (zdist2 (d.L n) (a.1 - a.2) : ℝ))

/-- **The core.**  For `D_g = max(D, 20 + 2/c) + 3/c`, `ε = δ/8` and the grid `K = gridK d D_g
(D₁+1)` from `s` to `v`, eventually in `n`: outside a set of `pathP`-probability at most `N^{-D₁}`
the walk satisfies `Step2Grid_concl`.  Proof: `goodEvent_grid` (at `κ/2`), `gridStepBoundPT`,
the stopping argument (`min_firstHit_eq_of_at`) with the exponent-arithmetic closing
(`Step2Grid_jstar_lt`), then (53) (`Step2Grid_lk_le`). -/
private theorem Step2Grid_core {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hc : 0 < c) (hτ : 0 < τ)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d c) (hcs : CondStInd d E s t)
    (hrc : RangeCond d τ t) (hid : InitDecay d E s) (h1 : Step1LoopPT d E s t)
    (hw : Step1WeakLawPT d E s t) (hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) c τ)
    (v : ℕ → ℝ) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    {D δ D₁ : ℝ} (hδ : 0 < δ) (hδc : δ ≤ min (2 * c) τ / 400) (hδ1 : δ ≤ 1) (hD₁ : 0 < D₁) :
    ∀ᶠ n : ℕ in atTop,
      pathP d {ω | ¬ Step2Grid_concl d E s v (gridK d (max D (20 + 2 / c) + 3 / c) (D₁ + 1)) δ D
          (max D (20 + 2 / c) + 3 / c) n ω} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
  have hc₀ : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  set c₀ : ℝ := min (2 * c) τ with hc₀def
  set D₀ : ℝ := max D (20 + 2 / c) with hD₀
  set Dg : ℝ := D₀ + 3 / c with hDgdef
  have h3c : 0 < 3 / c := by positivity
  have hDg : 20 + 2 / c ≤ Dg := by
    have : 20 + 2 / c ≤ D₀ := le_max_right _ _
    linarith
  have hDD : D ≤ D₀ := le_max_left _ _
  set ε : ℝ := δ / 8 with hεdef
  have hε : 0 < ε := by positivity
  have hδc' : δ ≤ c / 200 := by
    have : c₀ ≤ 2 * c := min_le_left _ _
    linarith
  set D' : ℝ := 2 * Dg + 3 + (7 + ε) / c with hD'
  set Cc : ℝ := Dg + 1 with hCc
  set K : ℕ → ℕ := gridK d Dg (D₁ + 1) with hKdef
  have hK0 : ∀ n, K n ≠ 0 := gridK_ne_zero Dg (D₁ + 1)
  have hst : ∀ n, s n ≤ t n := fun n => (hsv n).trans (hvt n)
  have hE' : ∀ n, |E n| < 2 - κ / 2 := fun n => by have := hE n; linarith
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hGood := goodEvent_grid (κ := κ / 2) (half_pos hκ) hE' hs0 hsv hvt ht1 hc hbw hτ hrc hcs
    hsz hV3 h1 hw hid hδ hδc' hDg hε D' Cc Cc D₁ hD₁
  have hPE := gridStepBoundPT d κ c τ E s v t δ Dg ε D' Cc Cc hκ hE hs0 hsv hvt ht1 hc hbw hτ hrc
    hcs hsz hδ hδc' hDg hε le_rfl le_rfl le_rfl D₁ hD₁ ε hε
  set cκ : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hcκdef
  have hcκ : 0 < cκ := (Step2Grid_im_ge hκ (hE 0)).1
  have hcκ1 : cκ ≤ 1 := (Step2Grid_im_ge hκ (hE 0)).2.1
  have hIm : ∀ n, cκ ≤ (spectralM (E n)).im := fun n => (Step2Grid_im_ge hκ (hE n)).2.2
  have hbig1 : ∀ᶠ n : ℕ in atTop, 4 * cκ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ / 13) :=
    ((tendsto_rpow_atTop (by positivity : 0 < c₀ / 13)).comp hsz).eventually
      (eventually_ge_atTop (4 * cκ⁻¹))
  have hbig2 : ∀ᶠ n : ℕ in atTop, 28 < ((d.size n : ℕ) : ℝ) ^ (δ / 8) :=
    ((tendsto_rpow_atTop (by positivity : 0 < δ / 8)).comp hsz).eventually_gt_atTop 28
  have hAz := azumaMm_le (d := d) hκ hE hsz hδ hε.le
  filter_upwards [hGood, hPE, hAz, hbig1, hbig2, hbw, hrc, hcs] with n hG hP hAzn hb1 hb2 hbwn
    hrcn hcsn
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hMtc : cκ * ((d.size n : ℕ) : ℝ) ^ c₀ ≤ scaleM (d.L n) (d.W n) (E n) (t n) := by
    have h := (scaleM_etaT_of_range (E := E n) (c := c) (τ := τ) (t := t n) hL1 hW1 (hE2 n) hc hτ
      (ht1 n) hbwn hrcn).1
    exact le_trans (mul_le_mul_of_nonneg_right (hIm n) (Real.rpow_nonneg (by linarith) _)) h
  have hae : ∀ᵐ ω ∂(pathP d), ω ∈ goodEventGrid d E s v K δ Dg ε D' Cc Cc n →
      Step2Grid_concl d E s v K δ D Dg n ω := by
    filter_upwards [hP] with ω hω hgood
    have hPEω := hω hgood
    have hC : ∀ k ≤ K n, pathH d s v K n k ω ∈ goodSet (d.L n) (d.W n) (E n) (s n)
        (gridTime s v K n k) (((d.size n : ℕ) : ℝ) ^ ε) := hgood.1.2
    have hτK : gridTauFull d E s v K δ Dg ε n ω ≤ K n := gridTauFull_le E s v K δ Dg ε n ω
    have hsuτ : s n ≤ gridTime s v K n (gridTauFull d E s v K δ Dg ε n ω) := by
      have h := GoodEvent_gridTime_mono (K := K) (hsv n)
        (Nat.zero_le (gridTauFull d E s v K δ Dg ε n ω))
      rwa [GoodEvent_gridTime_zero] at h
    have huτ : gridTime s v K n (gridTauFull d E s v K δ Dg ε n ω) ≤ t n :=
      (GoodEvent_gridTime_le (hsv n) hτK).trans (hvt n)
    have hat : jStarMat (d.L n) (d.W n) (E n) Dg
        (gridTime s v K n (gridTauFull d E s v K δ Dg ε n ω))
        (pathH d s v K n (gridTauFull d E s v K δ Dg ε n ω) ω) <
        thr d E s δ n (gridTime s v K n (gridTauFull d E s v K δ Dg ε n ω)) :=
      Step2Grid_jstar_lt hL1 hW1 (hE2 n) (hs0 n) hsuτ huτ (ht1 n) hcsn hN1 hc₀ hδ hδc hcκ hcκ1
        hMtc hb1 hb2 hAzn (fun a b => hPEω (a, b))
    have hτeq : gridTauFull d E s v K δ Dg ε n ω = K n := by
      refine min_firstHit_eq_of_at
        (fun j (ω' : PathΩ d) => jStarMat (d.L n) (d.W n) (E n) Dg (gridTime s v K n j)
          (pathH d s v K n j ω'))
        (fun k (ω' : PathΩ d) => (goodSet (d.L n) (d.W n) (E n) (s n)
          (gridTime s v K n (min k (K n))) (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator
            (fun _ => (1 : ℝ)) (pathH d s v K n k ω'))
        (fun j => thr d E s δ n (gridTime s v K n j)) (1 / 2) (K n) ?_ hat
      intro j hj
      have hmem := hC j hj
      change (goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s v K n (min j (K n)))
          (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ)) (pathH d s v K n j ω) < 1 / 2
      rw [min_eq_left hj, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hmem)]
      norm_num
    unfold Step2Grid_concl
    refine ⟨?_, ?_⟩
    · have h := hat
      rw [hτeq, gridTime_last s v K n (hK0 n)] at h
      exact h
    · intro a
      have h := Step2Grid_lk_le hL1 hW1 (hE2 n) (hs0 n) hsuτ huτ (ht1 n) hcsn hN1 hc₀ hδ hδc hδ1
        hcκ hcκ1 hMtc hb1 hb2 hAzn hc hτ hbwn hrcn hDD (fun a b => hPEω (a, b)) a.1 a.2
      rw [hτeq, gridTime_last s v K n (hK0 n)] at h
      exact h
  have h0 := ae_iff.1 hae
  calc pathP d {ω | ¬ Step2Grid_concl d E s v K δ D Dg n ω}
      ≤ pathP d ((goodEventGrid d E s v K δ Dg ε D' Cc Cc n)ᶜ ∪
          {ω | ¬ (ω ∈ goodEventGrid d E s v K δ Dg ε D' Cc Cc n →
            Step2Grid_concl d E s v K δ D Dg n ω)}) := by
        apply measure_mono
        intro ω hω
        by_cases hg : ω ∈ goodEventGrid d E s v K δ Dg ε D' Cc Cc n
        · right; exact fun h => hω (h hg)
        · left; exact hg
    _ ≤ pathP d (goodEventGrid d E s v K δ Dg ε D' Cc Cc n)ᶜ +
          pathP d {ω | ¬ (ω ∈ goodEventGrid d E s v K δ Dg ε D' Cc Cc n →
            Step2Grid_concl d E s v K δ D Dg n ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
        rw [h0, add_zero]; exact hG


/-! ## 4. The two results -/

/-- **The stopping argument of Step 2 on the grid** (`\label{51}`, `\label{52}`).  From the grid
step bound (`gridStepBoundPT`), the good event (`goodEvent_grid` at `κ/2`) and the exponent
arithmetic (`stepEExponentsD`, `stepECprimeAz`, `thrImproveD`): on the good event the threshold
`Θ(u_τ) = N^δ (η_s/η_{u_τ})^4` is never reached before the grid end, so `τ = K`
(`min_firstHit_eq_of_at`) and `lk_le_of_jS` gives the last step.
The grid is `K = gridK d D_g (D₁+1)` with `D_g = max(D, 20 + 2/c) + 3/c`, `δ₀ = min(c₀/400, 1)`
with `c₀ = min(2c, τ)`, and `ε = η = δ/8`.  A conditional result (under `GbEXPHypV3 d (κ/2) c τ`,
`InitDecay`, `Step1LoopPT`, `Step1WeakLawPT`), not the unconditional `Step2TargetNV3`. -/
theorem gridStep2PT : GridStep2PTClose d := by
  intro κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc hid h1 hw hV3 D hD u
  have hc₀ : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  refine ⟨min (min (2 * c) τ / 400) 1, lt_min (by positivity) one_pos, ?_⟩
  intro δ hδ hδ₀ D₁ hD₁
  have hδc : δ ≤ min (2 * c) τ / 400 := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_right _ _)
  set Dg : ℝ := max D (20 + 2 / c) + 3 / c with hDg
  have hDD : D ≤ Dg := by
    have : 0 < 3 / c := by positivity
    have : D ≤ max D (20 + 2 / c) := le_max_left _ _
    linarith
  have hCK : 0 ≤ CK Dg (D₁ + 1) := by
    unfold CK
    have : 0 < 2 / c := by positivity
    have : 0 < 3 / c := by positivity
    have : (20 : ℝ) + 2 / c ≤ max D (20 + 2 / c) := le_max_right _ _
    linarith
  refine ⟨gridK d Dg (D₁ + 1), gridK_ne_zero Dg (D₁ + 1),
    ⟨CK Dg (D₁ + 1) + 2, by linarith, gridK_card_le hCK⟩, ?_⟩
  filter_upwards [Step2Grid_core d hκ hE hc hτ hs0 ht1 hsz hbw hcs hrc hid h1 hw hV3
    (fun n => (u n : ℝ)) (fun n => (u n).2.1) (fun n => (u n).2.2) (D := D) hδ hδc hδ1 hD₁]
    with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω hcon
  obtain ⟨p, hp⟩ := hω
  unfold Step2Grid_concl at hcon
  have hlk := lk_le_of_jS (E := E n) (D := D) (D' := Dg) (u := (u n : ℝ))
    (Λ := thr d E s δ n (u n : ℝ)) (d.W_pos n) hDD hcon.1.le p.1 p.2
  have hY : thr d E s δ n (u n : ℝ) *
      tailT (d.L n) (d.W n) (E n) D (u n : ℝ) (zdist2 (d.L n) (p.1 - p.2) : ℝ) =
      ((d.size n : ℕ) : ℝ) ^ δ *
        ((etaT (E n) (s n) / etaT (E n) (u n : ℝ)) ^ 4 *
          tailT (d.L n) (d.W n) (E n) D (u n : ℝ) (zdist2 (d.L n) (p.1 - p.2) : ℝ)) := by
    unfold thr; ring
  exact absurd (lt_of_lt_of_le hp (hlk.trans (le_of_eq hY))) (lt_irrefl _)

/-- **The grid form of (53) with the near exponent `3`** (`\label{53}`): the same argument as
`gridStep2PT`; the end point `u` keeps the bound of `gridStepBoundPT` at `τ = K`, with the
additive initial term `N^{η+δ/16} r² W^{-D_g}` absorbed into `𝒯_{u,D}` by the extra depth `3/c`
(`Bandwidth`, `RangeCond`).  A conditional result, as `gridStep2PT`. -/
theorem gridStep2Eq53PT : GridStep2Eq53PTClose d := by
  intro κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc hid h1 hw hV3 D hD u
  have hc₀ : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  refine ⟨min (min (2 * c) τ / 400) 1, lt_min (by positivity) one_pos, ?_⟩
  intro δ hδ hδ₀ D₁ hD₁
  have hδc : δ ≤ min (2 * c) τ / 400 := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_right _ _)
  set Dg : ℝ := max D (20 + 2 / c) + 3 / c with hDg
  have hCK : 0 ≤ CK Dg (D₁ + 1) := by
    unfold CK
    have : 0 < 2 / c := by positivity
    have : 0 < 3 / c := by positivity
    have : (20 : ℝ) + 2 / c ≤ max D (20 + 2 / c) := le_max_right _ _
    linarith
  refine ⟨gridK d Dg (D₁ + 1), gridK_ne_zero Dg (D₁ + 1),
    ⟨CK Dg (D₁ + 1) + 2, by linarith, gridK_card_le hCK⟩, ?_⟩
  filter_upwards [Step2Grid_core d hκ hE hc hτ hs0 ht1 hsz hbw hcs hrc hid h1 hw hV3
    (fun n => (u n : ℝ)) (fun n => (u n).2.1) (fun n => (u n).2.2) (D := D) hδ hδc hδ1 hD₁]
    with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω hcon
  obtain ⟨p, hp⟩ := hω
  unfold Step2Grid_concl at hcon
  exact absurd (lt_of_lt_of_le hp (hcon.2 p)) (lt_irrefl _)

end RBM.Path
