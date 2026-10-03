/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Main.EndpointsFromSTO
import RBM2D.Main.P7FromSTO
import RBM2D.Induction.AltLevelsE

/-!
# The four main theorems

`STOAll` (the universally closed form of the stopped-evolution estimate) is `Ind.stoeqTargetV2`
of `AltLevelsE`.  The conversions in `EndpointsFromSTO` and `P7FromSTO` then give the four
endpoint statements `locSC`, `QDiff`, `decol`, `QUE` (`MR:locSC`, `MR:QDiff`, `MR:decol`,
`MR:QUE`) and the inputs `P7Out`, `P7ExpOut` of the universality argument without any
hypothesis.
-/

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-- `STOAll` holds: it is `Ind.stoeqTargetV2` with the quantifiers in the same order. -/
theorem stoAll_holds : STOAll :=
  fun d κ c τ C E s t => Ind.stoeqTargetV2 d κ c τ C E s t

/-- **The local semicircle law `MR:locSC`.** -/
theorem locSC_holds : locSC := (locSC_QDiff_of_STOAll stoAll_holds).1

/-- **Quantum diffusion `MR:QDiff`.** -/
theorem QDiff_holds : QDiff := (locSC_QDiff_of_STOAll stoAll_holds).2

/-- **Delocalization `MR:decol`.** -/
theorem decol_holds : decol := (decol_QUE_of_STOAll stoAll_holds).1

/-- **Generalized quantum unique ergodicity `MR:QUE`.** -/
theorem QUE_holds : QUE := (decol_QUE_of_STOAll stoAll_holds).2

/-- `P7Out`: the loop estimates `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`. -/
theorem p7Out_holds : Univ.P7Out := p7Out_of_STOAll stoAll_holds

/-- `P7ExpOut`: the improved expectation bound `ML:exp`. -/
theorem p7ExpOut_holds : Univ.P7ExpOut := p7ExpOut_of_STOAll stoAll_holds

/-! ## Concrete instance

`locSC_holds` at `𝔠 = 1/3`, `witnessSizes`, `κ = 1`, `τ = 1/2`, `D = 1`: no hypothesis is left
beyond the numerical positivity and `Admissible (1/3) witnessSizes`. -/

theorem locSC_holds_instance :
    ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (witnessSizes.size n) 1 (1 / 2) z →
      seqP witnessSizes {ω | ¬ ∀ x y : Idx (witnessSizes.L n) (witnessSizes.W n),
          ‖Gn witnessSizes n ω z x y - (if x = y then mSC z else 0)‖ ≤
            (witnessSizes.W n : ℝ) ^ (1 / 2 : ℝ) /
              Real.sqrt (Meta (witnessSizes.L n) (witnessSizes.W n) z)} ≤
        ENNReal.ofReal (((witnessSizes.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  (locSC_holds (1 / 3) (by norm_num) witnessSizes admissible_witnessSizes 1 (1 / 2) 1
    one_pos (by norm_num) one_pos).mono fun _ h z hz => (h z hz).1

end RBM.Endpoints
