/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Props

/-!
# The Step 2 statement (53) with the near exponent `3`

`Step2Eq53PTV3` is `Step2Eq53PT` (`Path/Step2Props.lean`) with the near-diagonal exponent `5/2`
replaced by `3`; the paper's exponent is `2`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-- (53), per time and at every endpoint `u ∈ [s,t]`, with the near-diagonal exponent `3` (the
paper has `2`):
`|(𝓛-𝒦)_{u,(+,-),(a,b)}| ≺ [(η_s/η_u)^{3} 1(|a-b|_L ≤ 6ℓ*_u) + 1] 𝒯_{u,D}(|a-b|_L)`.
Evaluated at the energy `E n`. -/
def Step2Eq53PTV3 (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ =>
      ((etaT (E n) (s n) / etaT (E n) p.1) ^ (3 : ℝ) *
          (if (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) p.1
            then 1 else 0) + 1) *
        tailT (d.L n) (d.W n) (E n) D p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ))

end RBM.Path
