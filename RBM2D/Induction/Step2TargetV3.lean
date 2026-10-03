/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Path.Step2PropsV3

/-!
# The Step 2 target with the near exponent `3`

`Step2TargetNV3` is the statement `Step2TargetN` with `Step2Eq53PT` replaced by
`Path.Step2Eq53PTV3`, the near-diagonal exponent `3` in (53) (the paper writes `(η_s/η_t)^2`; its
argument gives `(η_s/η_t)^{5/2}`).

Result: `Step2TargetNV3`, the statement of Step 2 with this exponent.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The Step 2 statement with the near-diagonal exponent `3`** (`Gt_bound_flow`,
`Eq:Gdecay_w`, (53); the paper writes `2`), i.e. `Step2Eq53PT` is replaced by
`Path.Step2Eq53PTV3`.  Everything else is the text of `Step2TargetN`. -/
def Step2TargetNV3 (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → SizeTendsto d →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    InitDecay d E s → InitLocal d E s → Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    Step2LocalPT d E s t ∧ Step2DecayPT d E s t ∧ Path.Step2Eq53PTV3 d E s t

end RBM.Ind
