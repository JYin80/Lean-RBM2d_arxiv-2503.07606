/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodEvent
import RBM2D.Path.Stop
import RBM2D.Path.Transfer
import RBM2D.Path.Walk
import RBM2D.Path.PerTime
import RBM2D.Path.Scales
import RBM2D.Path.Step2Props

/-!
# The grid hand-off `GridStep2PT` of (`Eq:Gdecay_w`) and its transfer to `Step2DecayPT`

The deterministic bootstrap step on the grid walk, and the transfer of the grid-endpoint
statement `GridStep2PT` to the single-time statement `Step2DecayPT`.  In dimension two the
index is `Z2 L`, the size index is `n` with `N = size n = (W L)²`, the walk is `pathH`,
`pathP`, the matrix functionals are `lkErrMat`, `jStarMat`, and the profile is `tailT`
(`def_WTuD`), whose `W^{-D}` term carries no factor `M_u^{-2}`.

## Main declarations

* `GridStep2PT`: the grid hand-off, with the energy sequence `E`.
* `firstHit_eq_of_below`, `min_firstHit_eq_of_at`: the deterministic bootstrap step.
* `lk_le_of_jS`: `J*_{u,D'} ≤ Λ` gives `|(𝓛-𝒦)_{ab}| ≤ Λ 𝒯_{u,D}` for `D ≤ D'`.
* `pg_bad_eq_flow`: the grid-endpoint law of an `∃ p` event equals its single-time law.
* `step2DecayPT_of_gridStep2PT`: `GridStep2PT → Step2DecayPT`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-! ## The grid hand-off statement -/

/-- **Grid hand-off of (`Eq:Gdecay_w`)**: for every `D > 0` and endpoint sequence `u ∈ [s,t]`
there is `δ₀ > 0` such that for all `δ ∈ (0, δ₀]` and `D₁ > 0` there is a polynomial grid from
`s` to `u` on which, eventually, the last grid step violates `N^δ (η_s/η_u)^4 𝒯_{u,D}` with
probability `≤ N^{-D₁}`.  The grid is chosen after `D₁`; this is legitimate because the
conclusion concerns one-time laws only (`TransferLaw`).  The energy is a sequence `E`,
evaluated at `E n`. -/
def GridStep2PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), ∀ u : ∀ n, TimeIcc s t n,
    ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D₁ > (0 : ℝ),
      ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
          ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ C) ∧
        ∀ᶠ n : ℕ in atTop, pathP d {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
          ((d.size n : ℕ) : ℝ) ^ δ *
              ((etaT (E n) (s n) / etaT (E n) (u n : ℝ)) ^ 4 *
                tailT (d.L n) (d.W n) (E n) D (u n : ℝ) (zdist2 (d.L n) (p.1 - p.2) : ℝ)) <
            lkErrMat (d.L n) (d.W n) (E n) (u n : ℝ)
              (pathH d s (fun n => (u n : ℝ)) K n (K n) ω) p.1 p.2}
          ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁))

/-! ## The deterministic bootstrap step -/

section Deterministic

variable {Ω' : Type*}

/-- If `J` stays strictly below `θ` up to the grid horizon `K`, the grid stopping index
`firstHit J θ K` does not fire. -/
theorem firstHit_eq_of_below (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {ω : Ω'}
    (h : ∀ j ≤ K, J j ω < θ) : firstHit J θ K ω = K := by
  by_contra hne
  have hlt : firstHit J θ K ω < K := lt_of_le_of_ne (firstHit_le J θ K ω) hne
  have hmem : θ ≤ J (firstHit J θ K ω) ω :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-- Bootstrap step: let `τ ω := min (firstHit (J - θ) 0 K ω) (firstHit J' θ' K ω)`.
If the second process stays below its level up to `K` and `J τ < θ τ` holds at the random
index `τ`, then `τ = K`. -/
theorem min_firstHit_eq_of_at (J J' : ℕ → Ω' → ℝ) (θ : ℕ → ℝ) (θ' : ℝ) (K : ℕ)
    {ω : Ω'} (hgood : ∀ j ≤ K, J' j ω < θ')
    (hat : J (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω)) ω
      < θ (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω))) :
    min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω) = K := by
  have hb : firstHit J' θ' K ω = K := firstHit_eq_of_below J' θ' K hgood
  have haK : firstHit (fun j ω => J j ω - θ j) 0 K ω ≤ K := firstHit_le _ _ _ _
  rw [hb, min_eq_left haK] at hat ⊢
  by_contra hne
  have hlt : firstHit (fun j ω => J j ω - θ j) 0 K ω < K := lt_of_le_of_ne haK hne
  have hmem : (0 : ℝ) ≤ J (firstHit (fun j ω => J j ω - θ j) 0 K ω) ω
      - θ (firstHit (fun j ω => J j ω - θ j) 0 K ω) :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  linarith

end Deterministic

/-! ## From `J*` to `lkErrMat` -/

/-- Deterministic and pointwise: `J*_{u,D'}(M) ≤ Λ` with `D ≤ D'` gives
`|(𝓛-𝒦)_{ab}| ≤ Λ 𝒯_{u,D}(|a-b|_L)`.  For `d = 2` the profile `𝒯` has a bare `W^{-D}`, so no
shift `D + 4 ≤ D'` and no scale bracket are needed. -/
theorem lk_le_of_jS {L W : ℕ} [NeZero L] [NeZero W] (hW : 1 ≤ W) {E D D' Λ u : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hDD : D ≤ D')
    (hJ : jStarMat L W E D' u M ≤ Λ) (a b : Z2 L) :
    lkErrMat L W E u M a b ≤ Λ * tailT L W E D u (zdist2 L (a - b) : ℝ) := by
  have h1 : (1 : ℝ) ≤ jStarMat L W E D' u M := one_le_jStarMat L W hW E D' u M
  have hΛ0 : 0 ≤ Λ := le_trans (le_trans zero_le_one h1) hJ
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hkey := lkErrMat_le_jStarMat_mul_tailT L W hW E D' u M a b
  have hT' : tailT L W E D' u (zdist2 L (a - b) : ℝ) ≤ tailT L W E D u (zdist2 L (a - b) : ℝ) := by
    unfold tailT
    have : (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_exponent_le hW' (by linarith)
    linarith
  have hT0 : 0 ≤ tailT L W E D' u (zdist2 L (a - b) : ℝ) := (tailT_pos hW L E D' u _).le
  calc lkErrMat L W E u M a b
      ≤ jStarMat L W E D' u M * tailT L W E D' u (zdist2 L (a - b) : ℝ) := hkey
    _ ≤ Λ * tailT L W E D' u (zdist2 L (a - b) : ℝ) := mul_le_mul_of_nonneg_right hJ hT0
    _ ≤ Λ * tailT L W E D u (zdist2 L (a - b) : ℝ) := mul_le_mul_of_nonneg_left hT' hΛ0

/-! ## The per-`n` transfer of an `∃ p` event -/

private theorem bootstrap_measurable_pathH (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH d s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH d s t K n k i j

private theorem bootstrap_measurable_seqHflow (n : ℕ) (u : ℝ) :
    Measurable (Sizes.seqHflow d n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n u i j

/-- The per-`n` transfer of a bad-set probability from the grid walk (at the last grid step
`k = K n`) to the single-time model at `uR n`: both events are preimages of one measurable
matrix set, and `transferLaw` at `k = K n` with `gridTime_last` identifies the two image laws.
The walk is `pathH`, the flow is `Sizes.seqHflow`, and the index is `Z2 (d.L n)`. -/
theorem pg_bad_eq_flow {E δ : ℝ} {s uR : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsu : s n ≤ uR n) (hK : K n ≠ 0) (ζ : Z2 (d.L n) × Z2 (d.L n) → ℝ) :
    pathP d {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
        ((d.size n : ℕ) : ℝ) ^ δ * ζ p <
          lkErrMat (d.L n) (d.W n) E (uR n) (pathH d s uR K n (K n) ω) p.1 p.2}
      = Sizes.seqP d {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
        ((d.size n : ℕ) : ℝ) ^ δ * ζ p <
          lkErrMat (d.L n) (d.W n) E (uR n) (Sizes.seqHflow d n (uR n) ω) p.1 p.2} := by
  set S : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
    {M | ∃ p : Z2 (d.L n) × Z2 (d.L n),
      ((d.size n : ℕ) : ℝ) ^ δ * ζ p < lkErrMat (d.L n) (d.W n) E (uR n) M p.1 p.2} with hSdef
  have hS : MeasurableSet S := by
    have heq : S = ⋃ p : Z2 (d.L n) × Z2 (d.L n),
        {M | ((d.size n : ℕ) : ℝ) ^ δ * ζ p <
          lkErrMat (d.L n) (d.W n) E (uR n) M p.1 p.2} := by
      ext M; simp [hSdef]
    rw [heq]
    exact MeasurableSet.iUnion fun p =>
      measurableSet_lt measurable_const (measurable_lkErrMat (d.L n) (d.W n) E (uR n) p.1 p.2)
  have hmap : (pathP d).map (pathH d s uR K n (K n)) =
      (Sizes.seqP d).map (Sizes.seqHflow d n (uR n)) := by
    have h := transferLaw d s uR K n (K n) hs0 hsu hK
    rwa [gridTime_last s uR K n hK] at h
  have e1 : {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
      ((d.size n : ℕ) : ℝ) ^ δ * ζ p <
        lkErrMat (d.L n) (d.W n) E (uR n) (pathH d s uR K n (K n) ω) p.1 p.2}
      = pathH d s uR K n (K n) ⁻¹' S := rfl
  have e2 : {ω | ∃ p : Z2 (d.L n) × Z2 (d.L n),
      ((d.size n : ℕ) : ℝ) ^ δ * ζ p <
        lkErrMat (d.L n) (d.W n) E (uR n) (Sizes.seqHflow d n (uR n) ω) p.1 p.2}
      = Sizes.seqHflow d n (uR n) ⁻¹' S := rfl
  rw [e1, e2, ← Measure.map_apply (bootstrap_measurable_pathH d s uR K n (K n)) hS,
    ← Measure.map_apply (bootstrap_measurable_seqHflow d n (uR n)) hS, hmap]

/-! ## Real-number arithmetic of the absorption -/

/-- The ratio `(1-s)/(1-u)` is nonnegative and at most `N^{1-τ'}` when `1 - t ≥ N^{-1+τ'}`,
`0 ≤ s`, `u ≤ t < 1`. -/
private theorem bootstrap_ratio_le {s u t N τ' : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (hut : u ≤ t)
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

/-- The absorption inequality (★): with `D_g = D + (1 + 4|1-τ'|)/c`,
`N^δ · r⁴ · (A + W^{-D_g}) ≤ N^τ · (r⁴ A + W^{-D})`. -/
private theorem bootstrap_absorb {N W r A δ τ D Dg c τ' : ℝ} (hN : 1 ≤ N) (hW : 0 < W)
    (hδτ : δ ≤ τ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hc : 0 < c)
    (hDg : Dg = D + (1 + 4 * |1 - τ'|) / c)
    (hr0 : 0 ≤ r) (hr : r ≤ N ^ (1 - τ')) (hA : 0 ≤ A) (hWN : N ^ c ≤ W) :
    N ^ δ * (r ^ 4 * (A + W ^ (-Dg))) ≤ N ^ τ * (r ^ 4 * A + W ^ (-D)) := by
  have hN0 : 0 < N := by linarith
  have hNτ : N ^ δ ≤ N ^ τ := Real.rpow_le_rpow_of_exponent_le hN hδτ
  have hNδ0 : 0 ≤ N ^ δ := Real.rpow_nonneg hN0.le _
  have hNτ1 : 1 ≤ N ^ τ := Real.one_le_rpow hN hτ.le
  have hWD0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hr4 : r ^ 4 ≤ N ^ (4 * (1 - τ')) := by
    calc r ^ 4 ≤ (N ^ (1 - τ')) ^ 4 := pow_le_pow_left₀ hr0 hr 4
      _ = N ^ (4 * (1 - τ')) := by
        rw [show (4 * (1 - τ')) = (1 - τ') * ((4 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_mul hN0.le, Real.rpow_natCast]
  have hq : 0 < (1 + 4 * |1 - τ'|) / c := by positivity
  have hWpow : W ^ (-Dg) = W ^ (-D) * W ^ (-((1 + 4 * |1 - τ'|) / c)) := by
    rw [← Real.rpow_add hW, hDg]; congr 1; ring
  have hW2 : W ^ (-((1 + 4 * |1 - τ'|) / c)) ≤ N ^ (-(1 + 4 * |1 - τ'|)) := by
    have h1 : W ^ (-((1 + 4 * |1 - τ'|) / c)) ≤ (N ^ c) ^ (-((1 + 4 * |1 - τ'|) / c)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 c) hWN (by linarith)
    rw [← Real.rpow_mul hN0.le] at h1
    have h2 : c * -((1 + 4 * |1 - τ'|) / c) = -(1 + 4 * |1 - τ'|) := by
      field_simp
    rwa [h2] at h1
  have hprod : N ^ δ * N ^ (4 * (1 - τ')) * N ^ (-(1 + 4 * |1 - τ'|)) ≤ 1 := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hN
    have := le_abs_self (1 - τ')
    linarith
  have hT2 : N ^ δ * (r ^ 4 * W ^ (-Dg)) ≤ W ^ (-D) := by
    have hWq0 : 0 ≤ W ^ (-((1 + 4 * |1 - τ'|) / c)) := Real.rpow_nonneg hW.le _
    calc N ^ δ * (r ^ 4 * W ^ (-Dg))
        = N ^ δ * (r ^ 4 * (W ^ (-D) * W ^ (-((1 + 4 * |1 - τ'|) / c)))) := by rw [hWpow]
      _ ≤ N ^ δ * (N ^ (4 * (1 - τ')) * (W ^ (-D) * N ^ (-(1 + 4 * |1 - τ'|)))) := by
          apply mul_le_mul_of_nonneg_left _ hNδ0
          exact mul_le_mul hr4 (mul_le_mul_of_nonneg_left hW2 hWD0) (mul_nonneg hWD0 hWq0)
            (Real.rpow_nonneg hN0.le _)
      _ = W ^ (-D) * (N ^ δ * N ^ (4 * (1 - τ')) * N ^ (-(1 + 4 * |1 - τ'|))) := by ring
      _ ≤ W ^ (-D) * 1 := mul_le_mul_of_nonneg_left hprod hWD0
      _ = W ^ (-D) := mul_one _
  calc N ^ δ * (r ^ 4 * (A + W ^ (-Dg)))
      = N ^ δ * (r ^ 4 * A) + N ^ δ * (r ^ 4 * W ^ (-Dg)) := by ring
    _ ≤ N ^ τ * (r ^ 4 * A) + N ^ τ * W ^ (-D) :=
        add_le_add (mul_le_mul_of_nonneg_right hNτ (by positivity))
          (hT2.trans (le_mul_of_one_le_left hWD0 hNτ1))
    _ = N ^ τ * (r ^ 4 * A + W ^ (-D)) := by ring

/-! ## The transfer `GridStep2PT → Step2DecayPT` -/

/-- **`GridStep2PT` implies `Step2DecayPT`.**  Hypotheses: `0 ≤ s`, `s ≤ t`, `t < 1`, `|E| < 2`
for every `n`; the bandwidth `N^c ≤ W` with `0 < c` (`Main_DEL_COND`) and the range
`N^{-1+τ'} ≤ 1 - t` eventually.  The `(η_s/η_u)^4` on the `W^{-D}` term of `GridStep2PT`'s
profile is absorbed by the polynomial bound `η_s/η_u ≤ N^{1-τ'}` (from `RangeCond`) and the
loss shift `D_g = D + (1 + 4|1-τ'|)/c` in `GridStep2PT` (via `Bandwidth`). -/
theorem step2DecayPT_of_gridStep2PT {E s t : ℕ → ℝ} {c τ' : ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2)
    (hc : 0 < c) (hBand : Bandwidth d c) (hRange : RangeCond d τ' t)
    (hG : GridStep2PT d E s t) : Step2DecayPT d E s t := by
  intro D hD
  have hU : ∀ n, Nonempty (TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) := fun n =>
    ⟨(⟨s n, le_refl _, hst n⟩, 0, 0)⟩
  refine (perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hU _ _).2 ?_
  intro u τ hτ D' hD'
  have hDg : 0 < D + (1 + 4 * |1 - τ'|) / c := by positivity
  obtain ⟨δ₀, hδ₀, hG'⟩ := hG (D + (1 + 4 * |1 - τ'|) / c) hDg (fun n => (u n).1)
  obtain ⟨K, hK0, -, hbad⟩ := hG' (min δ₀ (min τ 1))
    (lt_min hδ₀ (lt_min hτ one_pos)) (min_le_left _ _) D' hD'
  filter_upwards [hbad, hBand, hRange] with n hn hBn hRn
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have h1 := d.W_pos n
    have h2 := d.three_le_L n
    rw [Sizes.size_eq]
    have : 1 ≤ d.W n ^ 2 * d.L n ^ 2 := by
      have : 0 < d.W n ^ 2 * d.L n ^ 2 := by positivity
      omega
    exact_mod_cast this
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hun : s n ≤ ((u n).1 : ℝ) := (u n).1.2.1
  have hut : ((u n).1 : ℝ) ≤ t n := (u n).1.2.2
  have hpg := pg_bad_eq_flow d (E := E n) (δ := min δ₀ (min τ 1))
    (uR := fun n => (((u n).1 : TimeIcc s t n) : ℝ)) (hs0 n) hun (hK0 n)
    (fun p => (etaT (E n) (s n) / etaT (E n) (((u n).1 : TimeIcc s t n) : ℝ)) ^ 4 *
      tailT (d.L n) (d.W n) (E n) (D + (1 + 4 * |1 - τ'|) / c) (((u n).1 : TimeIcc s t n) : ℝ)
        (zdist2 (d.L n) (p.1 - p.2) : ℝ))
  refine le_trans (measure_mono ?_) (hpg.symm.trans_le hn)
  intro ω hω
  obtain ⟨_, hω'⟩ := hω
  refine ⟨((u n).2.1, (u n).2.2), lt_of_le_of_lt ?_ hω'⟩
  have hs1 : s n < 1 := lt_of_le_of_lt (hst n) (ht1 n)
  have hu1 : ((u n).1 : ℝ) < 1 := lt_of_le_of_lt hut (ht1 n)
  have hratio := etaT_div_etaT (hE n) hs1 hu1
  obtain ⟨hr0, hr⟩ := bootstrap_ratio_le (s := s n) (u := ((u n).1 : ℝ)) (t := t n)
    (N := ((d.size n : ℕ) : ℝ)) (τ' := τ') (hs0 n) (hst n) hut (ht1 n) (by linarith) hRn
  change ((d.size n : ℕ) : ℝ) ^ (min δ₀ (min τ 1)) *
      ((etaT (E n) (s n) / etaT (E n) ((u n).1 : ℝ)) ^ 4 *
        tailT (d.L n) (d.W n) (E n) (D + (1 + 4 * |1 - τ'|) / c) ((u n).1 : ℝ)
          (zdist2 (d.L n) ((u n).2.1 - (u n).2.2) : ℝ)) ≤
    ((d.size n : ℕ) : ℝ) ^ τ *
      ((etaT (E n) (s n) / etaT (E n) ((u n).1 : ℝ)) ^ 4 *
          (scaleM (d.L n) (d.W n) (E n) ((u n).1 : ℝ) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) ((u n).2.1 - (u n).2.2) : ℝ) /
          ellT (d.L n) ((u n).1 : ℝ))) + (d.W n : ℝ) ^ (-D))
  rw [mul_assoc (_ ^ 4)]
  unfold tailT
  rw [hratio]
  exact bootstrap_absorb (N := ((d.size n : ℕ) : ℝ)) (W := (d.W n : ℝ)) (D := D)
    (Dg := D + (1 + 4 * |1 - τ'|) / c) (c := c) (τ' := τ') hN1 hW0
    (le_trans (min_le_right _ _) (min_le_left _ _))
    (le_trans (min_le_right _ _) (min_le_right _ _)) hτ hc rfl hr0 hr
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le) hBn

end RBM.Path

end
