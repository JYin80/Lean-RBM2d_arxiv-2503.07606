/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Main.Endpoints
import RBM2D.Universality.GUETranslation
import RBM2D.Universality.UnivMain
import RBM2D.Universality.EMCTE2
import RBM2D.Universality.Uyw
import RBM2D.Universality.QUEFlow
import RBM2D.Universality.GUELocalSchur
import RBM2D.Universality.GreenCorr
import RBM2D.Universality.ZeroModeProfile

/-!
# `BUniv` from `G1Row` and the external input `L32`

`bUniv_of_rows` (`Universality/Pins.lean`) applied to every established reduction statement and
endpoint.  The leaves that remain hypotheses are exactly

* `L32`, the external input [32] Theorem 2.2;
* `G1Row`, the random-layer statement for the Ornstein--Uhlenbeck matrix `𝐇_t` (the weak local
  law `OULL` and the two-resolvent asymptotics `OUEq747`), through `OURow`.

`ouRow_of_g1Row` is `ouRow_of_pins` with `g2bRow`; `bUniv_of_g1Row` supplies `infty1Row`,
`univMainRow`, `claimRow`, `emcte2Row`, `jakUywRow`, `gueLocal`, `greenCorrAll` and the endpoints
`p7Out_holds`, `p7ExpOut_holds`, `locSC_holds`, `QDiff_holds`.
-/

namespace RBM.Endpoints

open MeasureTheory Filter Topology Matrix
open RBM RBM.Gauss RBM.Gauss.Sizes
open RBM.Univ

/-- `OURow` from `G1Row` alone: `ouRow_of_pins` with `g2bRow`. -/
theorem ouRow_of_g1Row : G1Row → OURow := fun h => ouRow_of_pins h g2bRow

/-- **`BUniv` from `G1Row` and the external `L32`.** Every other leaf of `bUniv_of_rows` is a
proved theorem. -/
theorem bUniv_of_g1Row : G1Row → L32 → BUniv := fun h h32 =>
  bUniv_of_rows infty1Row univMainRow claimRow emcte2Row jakUywRow (ouRow_of_g1Row h) h32
    p7Out_holds p7ExpOut_holds locSC_holds QDiff_holds gueLocal greenCorrAll

end RBM.Endpoints
