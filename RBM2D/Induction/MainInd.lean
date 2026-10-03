/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Chain
import RBM2D.Induction.HierVocab
import RBM2D.Induction.Step1
import RBM2D.Induction.Step3
import RBM2D.Induction.Step45
import RBM2D.Induction.Step2TargetV3
import RBM2D.Induction.GridGoodN
import RBM2D.Path.Step2Close
import RBM2D.Green.GbEXP
import RBM2D.Loop.KBound
import RBM2D.Evolution.Case3
import RBM2D.Evolution.Bridge
import RBM2D.Evolution.MLExpVocab
import RBM2D.Evolution.MLExpDuhamel
import RBM2D.Evolution.MLExpDrift
import RBM2D.Evolution.MLExpInv
import RBM2D.Evolution.MLExpHier
import RBM2D.Evolution.MLExpQ

/-!
# The last link of the induction chain: `lem:main_ind` from Steps 1–5, and `ML:exp`

Everything is an assembly of earlier theorems.

Results (namespace `RBM.Ind`, `variable (d : Sizes)`):
1. `MainIndPinV3`: the statement of `lem:main_ind` without a Step 2 hypothesis (which
   `step2TargetNV3_of_GbEXP d gbEXPV3` discharges);
2. `upstreamSteps34Prec`: the bundle `UpstreamSteps34Prec d κ c τ (cCase3 c 4)` from
   theorems (`Kbound_prec_uncond`, `gbEXPV3`, `sumDecayDetPrec`, `sumDecayCase5Prec` lifted by
   `precMono`, `sumDecayCase3Prec`);
3. `mainIndPinV3_of_R3`: the proof strategy of `lem:main_ind` (Section 2 of the paper) with
   `step1`, `step2TargetNV3_of_GbEXP d gbEXPV3`, `step3`, `step4`, `step5`; conditional only on the
   two statements `STOeqTargetV2`, `PPTargetV2`;
4. `mlConcl_of_R3`: `chainTarget` with `initAtZero`, `chainStepCond`, `KboundConcl` and 2–3, i.e.
   Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` for every bulk energy and time sequence,
   conditional only on the two statements `STOeqTargetV2`, `PPTargetV2`;
5. `mlExp`: `MLExpPin` (Lemma `ML:exp`) from `mlExp_of_pins` and five theorems, unconditional.

Paper: arXiv:2503.07606, Section 2.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. The statement without a Step 2 hypothesis -/

/-- **`MainIndPinV3` (`lem:main_ind`)**: the statement without a Step 2 hypothesis (the
universally quantified Step 2 target), which `step2TargetNV3_of_GbEXP d gbEXPV3` discharges.  The
conclusion is the shape the fifth hypothesis of `ChainTarget` has. -/
def MainIndPinV3 (κ c τ : ℝ) (C : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → ∀ (E s t : ℕ → ℝ), MainIndHyp d κ c τ E s t →
    MainIndConcl d E t

/-! ## 2. The unconditional upstream bundle -/

/-- **The bundle `UpstreamSteps34Prec`, unconditional**, at the constant `cCase3 c 4`:
`KboundConcl κ` is `Kbound_prec_uncond` (`KLoop.loopOf` and `Path.loopOf` have the same body);
`GbEXPHypV3 d (κ/2) c τ` is `gbEXPV3`; `SumDecayDetPrec`, `SumDecayCase5Prec` are the
theorems at `cPrec c ≤ cCase3 c 4` lifted by `precMono`; `SumDecayCase3Prec` is
`sumDecayCase3Prec`. -/
theorem upstreamSteps34Prec {κ c τ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ) :
    UpstreamSteps34Prec d κ c τ (cCase3 c 4) := by
  have hle : ∀ k, cPrec c k ≤ cCase3 c 4 k := fun k => by
    unfold cCase3
    have := abs_nonneg (4 : ℝ)
    linarith
  have hm := precMono κ c τ (cPrec c) (cCase3 c 4) hle
  refine ⟨?_, RBM.Green.gbEXPV3 d (κ / 2) c τ (half_pos hκ) hc hτ,
    hm.1 (sumDecayDetPrec κ c τ), hm.2 (sumDecayCase5Prec κ c τ), sumDecayCase3Prec d κ c τ⟩
  intro n hn
  exact KLoop.Kbound_prec_uncond n hn κ hκ

/-! ## 3. `lem:main_ind` from the five steps and the two remaining statements -/

section Assembly

/-- Restriction of a per-time domination over `u ∈ [s_n,t_n]` to the endpoint `u = t_n`. -/
private theorem mainInd_restrict {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {V : ℕ → Type*} {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ}
    {ξ' ζ' : ∀ n, Unit × V n → Ω → ℝ}
    (hξ : ∀ n (p : Unit × V n) ω, ξ' n p ω = ξ n (⟨t n, hst n, le_rfl⟩, p.2) ω)
    (hζ : ∀ n (p : Unit × V n) ω, ζ' n p ω = ζ n (⟨t n, hst n, le_rfl⟩, p.2) ω)
    (h : PerTimeDomAt P size ξ ζ) : PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn p
  have := hn (⟨t n, hst n, le_rfl⟩, p.2)
  simpa only [hξ, hζ] using this

/-- **`lem:main_ind` from Steps 1–5**, conditional only on `STOeqTargetV2` and `PPTargetV2` (the
proof strategy of the paper): Step 1 (`step1`, uniform to per time by
`perTimeOfStochDomAt`), Step 2 (`step2TargetNV3_of_GbEXP d gbEXPV3`), `STOeqPT` and `PPTwoLoopPT`
from these two statements, then Steps 3, 4, 5; the conclusion at `u = t` restricts each per-time output to
the endpoint `t_n ∈ [s_n, t_n]`. -/
theorem mainIndPinV3_of_R3 {κ c τ : ℝ} {C : ℕ → ℝ}
    (hSTO : ∀ E s t : ℕ → ℝ, STOeqTargetV2 d κ c τ C E s t)
    (hPP : ∀ E s t : ℕ → ℝ, PPTargetV2 d κ c τ C E s t) : MainIndPinV3 d κ c τ C := by
  intro hU E s t h
  obtain ⟨hK, hV3, -, -, -⟩ := id hU
  have h1 := step1 d κ c τ E s t hK hV3 h
  have h1PT : Step1LoopPT d E s t := fun k hk =>
    perTimeOfStochDomAt (Sizes.seqP d) d.size _ _ (h1.1 k hk)
  have hwPT : Step1WeakLawPT d E s t :=
    perTimeOfStochDomAt (Sizes.seqP d) d.size _ _ h1.2
  obtain ⟨hκ, hE, hc, hτ, hs, hst, ht, hsz, hbw, hcs, hrc, hLK, hDec, hLoc⟩ := id h
  obtain ⟨hloc, hdec, h53⟩ :=
    step2TargetNV3_of_GbEXP d RBM.Green.gbEXPV3 κ c τ E s t hκ hE hc hτ hs hst ht hsz hbw hcs hrc
      hDec hLoc h1PT hwPT
  have hSTOk := hSTO E s t hU h hloc hdec
  have hPPT := hPP E s t hU h h1PT hwPT hloc hdec
  have h3 := step3 d κ c τ E s t hK h h1PT hwPT hloc hdec hPPT hSTOk
  have h4 := step4 d κ c τ E s t hK hV3 h hloc hdec hPPT h3 hSTOk
  have h5 := step5 d κ c τ E s t h h4 h53
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact mainInd_restrict hst (fun n p ω => rfl) (fun n p ω => rfl) (h4 k hk)
  · intro D hD
    exact mainInd_restrict hst (fun n p ω => rfl) (fun n p ω => by simp only [tailT]) (h5 D hD)
  · exact mainInd_restrict hst (fun n p ω => rfl) (fun n p ω => rfl) hloc

end Assembly

/-! ## 4. The chain: Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` -/

/-- **Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` for every bulk energy and
time sequence**, conditional only on `STOeqTargetV2`, `PPTargetV2` (at the
constant `cCase3 c 4`): `chainTarget` with `initAtZero`, `chainStepCond`, `KboundConcl κ` (from
`upstreamSteps34Prec`) and `lem:main_ind` from `mainIndPinV3_of_R3`. -/
theorem mlConcl_of_R3 {κ c τ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ) (hsz : SizeTendsto d)
    (hbw : Bandwidth d c)
    (hSTO : ∀ E s t : ℕ → ℝ, STOeqTargetV2 d κ c τ (cCase3 c 4) E s t)
    (hPP : ∀ E s t : ℕ → ℝ, PPTargetV2 d κ c τ (cCase3 c 4) E s t) (E t : ℕ → ℝ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1)
    (hR : RangeCond d τ t) : MLConcl d E t :=
  chainTarget d κ c τ hκ hc hτ hsz hbw (upstreamSteps34Prec d hκ hc hτ).1 (initAtZero d κ)
    (chainStepCond d κ c τ) (mainIndPinV3_of_R3 d hSTO hPP (upstreamSteps34Prec d hκ hc hτ))
    E t hE ht0 ht1 hR

/-! ## 5. `ML:exp` -/

/-- **`MLExpPin` (`ML:exp`), unconditional**: `mlExp_of_pins` with the five
theorems `expDuhamelPin_of_hier d (expHierPin d)`, `expQDuhamelPin_of_hier d (expHierPin d)`,
`expDriftBound`, `expInvariant`, `expQBound`. -/
theorem mlExp (κ c τ : ℝ) (C : ℕ → ℝ) (E t : ℕ → ℝ) : MLExpPin d κ c τ C E t :=
  mlExp_of_pins d (expDuhamelPin_of_hier d (expHierPin d))
    (expQDuhamelPin_of_hier d (expHierPin d)) (expDriftBound d κ c τ E t) (expInvariant d)
    (expQBound d κ c τ E t)

end RBM.Ind

end
