/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Step2TargetV3
import RBM2D.Path.Bootstrap
import RBM2D.Path.Step2Grid
import RBM2D.Path.Step2Local

/-!
# The Step 2 closure of `lem:main_ind`

Paper: Step 2 of `lem:main_ind` (`\label{51}`, `\label{52}`, `\label{53}`), and
(`Gt_bound_flow`), (`Eq:Gdecay_w`).

* `Step2ClosureV3`: `GbEXPHypV3 d (κ/2) c τ → Step2TargetNV3 d κ c τ E s t`;
* `step2Eq53PTV3_of_gridStep2Eq53PT`: `GridStep2Eq53PT → Step2Eq53PTV3` (the transfer);
* `step2ClosureV3_of_rows`, `step2ClosureV3`: the three component theorems give the closure;
* `step2TargetNV3_of_GbEXP`: `Step2TargetNV3` for all parameters once `GbEXPV3Theorem` holds.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-- **The conditional Step 2 closure**.  Paper: Step 2 of `lem:main_ind` (`\label{51}`,
`\label{52}`, `\label{53}`); (`Gt_bound_flow`), (`Eq:Gdecay_w`).  The hypothesis
`GbEXPHypV3 d (κ/2) c τ` is the hypothesis of `lem_GbEXP`; it is discharged by
`GbEXPV3Theorem` (see `step2TargetNV3_of_GbEXP`).  The conclusion supplies the Step 2 inputs
`Step2LocalPT`, `Step2DecayPT`, `Step2Eq53PTV3`. -/
def Step2ClosureV3 : Prop :=
  ∀ (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ),
    RBM.Green.GbEXPHypV3 d (κ / 2) c τ → RBM.Ind.Step2TargetNV3 d κ c τ E s t

/-- **Transfer of the grid form of (53)**: `GridStep2Eq53PT` implies `Step2Eq53PTV3` (the argument
of `step2DecayPT_of_gridStep2PT`, without the absorption step: the profile of `GridStep2Eq53PT`
already is the profile of `Step2Eq53PTV3`). -/
theorem step2Eq53PTV3_of_gridStep2Eq53PT {E s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2)
    (hG : GridStep2Eq53PT d E s t) : Step2Eq53PTV3 d E s t := by
  intro D hD
  have hU : ∀ n, Nonempty (TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) := fun n =>
    ⟨(⟨s n, le_refl _, hst n⟩, 0, 0)⟩
  refine (perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hU _ _).2 ?_
  intro u τ hτ D' hD'
  obtain ⟨δ₀, hδ₀, hG'⟩ := hG D hD (fun n => (u n).1)
  obtain ⟨K, hK0, -, hbad⟩ := hG' (min δ₀ τ) (lt_min hδ₀ hτ) (min_le_left _ _) D' hD'
  filter_upwards [hbad] with n hn
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have h1 := d.W_pos n
    have h2 := d.three_le_L n
    rw [Sizes.size_eq]
    have : 1 ≤ d.W n ^ 2 * d.L n ^ 2 := by
      have : 0 < d.W n ^ 2 * d.L n ^ 2 := by positivity
      omega
    exact_mod_cast this
  have hun : s n ≤ ((u n).1 : ℝ) := (u n).1.2.1
  have hut : ((u n).1 : ℝ) ≤ t n := (u n).1.2.2
  set ζ : Z2 (d.L n) × Z2 (d.L n) → ℝ := fun p =>
    ((etaT (E n) (s n) / etaT (E n) (((u n).1 : TimeIcc s t n) : ℝ)) ^ (3 : ℝ) *
        (if (zdist2 (d.L n) (p.1 - p.2) : ℝ) ≤
            6 * ellStar (d.L n) (d.W n) (((u n).1 : TimeIcc s t n) : ℝ) then 1 else 0) + 1) *
      tailT (d.L n) (d.W n) (E n) D (((u n).1 : TimeIcc s t n) : ℝ)
        (zdist2 (d.L n) (p.1 - p.2) : ℝ) with hζ
  have hpg := pg_bad_eq_flow d (E := E n) (δ := min δ₀ τ)
    (uR := fun n => (((u n).1 : TimeIcc s t n) : ℝ)) (hs0 n) hun (hK0 n) ζ
  refine le_trans (measure_mono ?_) (hpg.symm.trans_le hn)
  intro ω hω
  obtain ⟨_, hω'⟩ := hω
  refine ⟨((u n).2.1, (u n).2.2), lt_of_le_of_lt ?_ hω'⟩
  have hs1 : s n < 1 := lt_of_le_of_lt (hst n) (ht1 n)
  have hu1 : ((u n).1 : ℝ) < 1 := lt_of_le_of_lt hut (ht1 n)
  have hr0 : 0 ≤ etaT (E n) (s n) / etaT (E n) ((u n).1 : ℝ) :=
    div_nonneg (etaT_pos (hE n) hs1).le (etaT_pos (hE n) hu1).le
  have hind : (0 : ℝ) ≤ (if (zdist2 (d.L n) ((u n).2.1 - (u n).2.2) : ℝ) ≤
      6 * ellStar (d.L n) (d.W n) ((u n).1 : ℝ) then 1 else 0) := by split_ifs <;> norm_num
  have hζ0 : 0 ≤ ζ ((u n).2.1, (u n).2.2) := by
    simp only [hζ]
    exact mul_nonneg (add_nonneg (mul_nonneg (Real.rpow_nonneg hr0 _) hind) zero_le_one)
      (tailT_pos (d.W_pos n) _ _ _ _ _).le
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)) hζ0

/-- **The closure from its three component statements**: `GridStep2PTClose`,
`GridStep2Eq53PTClose` and `Step2LocalOfDecay` give `Step2ClosureV3`, through `step2DecayPT_of_gridStep2PT` and the
transfer `step2Eq53PTV3_of_gridStep2Eq53PT`. -/
theorem step2ClosureV3_of_rows (hA : GridStep2PTClose d) (hB : GridStep2Eq53PTClose d)
    (hC : Step2LocalOfDecay d) : Step2ClosureV3 d := by
  intro κ c τ E s t hV3 hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc hid _hil h1 hw
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hdec : Step2DecayPT d E s t :=
    step2DecayPT_of_gridStep2PT d hs0 hst ht1 hE2 hc hbw hrc
      (hA κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc hid h1 hw hV3)
  exact ⟨hC κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc h1 hw hV3 hdec, hdec,
    step2Eq53PTV3_of_gridStep2Eq53PT d hs0 hst ht1 hE2
      (hB κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc hid h1 hw hV3)⟩

/-- **The Step 2 closure**: the component theorems `gridStep2PT`, `gridStep2Eq53PT` and
`step2LocalOfDecay` give `Step2ClosureV3`. -/
theorem step2ClosureV3 : Step2ClosureV3 d :=
  step2ClosureV3_of_rows d (gridStep2PT d) (gridStep2Eq53PT d) (step2LocalOfDecay d)

/-- **Unconditional form**: once `GbEXPV3Theorem` holds, `step2ClosureV3` gives
`Step2TargetNV3` for every `(κ, c, τ, E, s, t)`. -/
theorem step2TargetNV3_of_GbEXP (hG : RBM.Green.GbEXPV3Theorem) :
    ∀ (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ), RBM.Ind.Step2TargetNV3 d κ c τ E s t := by
  intro κ c τ E s t
  unfold RBM.Ind.Step2TargetNV3
  intro hκ hE hc hτ
  exact step2ClosureV3 d κ c τ E s t (hG d (κ / 2) c τ (half_pos hκ) hc hτ) hκ hE hc hτ

end RBM.Path
