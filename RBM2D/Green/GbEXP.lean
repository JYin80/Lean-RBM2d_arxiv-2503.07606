/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucAvgDet
import RBM2D.Green.IBPDet
import RBM2D.Green.LocalLaw

/-!
# `lem_GbEXP` for every size sequence

The theorem `gbEXPV3 : GbEXPV3Theorem`, the assembly of three theorems:

  `gbEXPV3Theorem_of_ports localLawDetThm fixedTimeFAThm ibpDetThm`   (`Green/AvgPins.lean`)

* `localLawDetThm` (`Green/LocalLaw.lean`): the local law at a deterministic
  scale `Ψ ≥ W⁻¹` from (`asGMc`) and `LoopDetSeq`;
* `fixedTimeFAThm` (`Green/FlucAvgDet.lean`): the fixed-time fluctuation
  averaging `jasdu`, both families, with the control `Ψ²`;
* `ibpDetThm` (`Green/IBPDet.lean`): the integration-by-parts display with
  the control `Ψ²`;
* `gbEXPV3Theorem_of_ports` also uses `avgBoundDetThm` (the averaging bound with the `≺ Ψ²`
  input), `loopFloorThm` (the floor `W⁻² ≤ 4 N^ε Ψ²`), and the theorems
  `gijOmegaSeq`, `giiOmegaSeq`, `gijSeq_of_asGMc`, `giiSeq_of_asGMc` of `Green/EntryGauss.lean`.

Paper: arXiv:2503.07606, `lem_GbEXP`, (`GijGEX`), (`GiiGEX`), (`asGMc`), (`GavLGEX`); the proof
is "that of Lemma 4.2 in [YY_25]".  The statement is `GbEXPV3Theorem`; nothing is added.  With
this file, `GbEXPHypV3 d κ 𝔠 δ` holds for every `d` and every `κ, 𝔠, δ > 0`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Green
open scoped NNReal ENNReal

/-- **`lem_GbEXP` for every size sequence**: `GbEXPHypV3 d κ 𝔠 δ` for every `d` and
every `κ, 𝔠, δ > 0` (`GbEXPV3Theorem`), from the three theorems above. -/
theorem gbEXPV3 : GbEXPV3Theorem :=
  gbEXPV3Theorem_of_ports localLawDetThm fixedTimeFAThm ibpDetThm

end RBM.Green
