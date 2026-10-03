/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Induction.HierAlgebra
import RBM2D.Induction.LoopGenN
import RBM2D.Path.DriftAlgebra

/-!
# The general-`n` `(𝓛 - 𝒦)` hierarchy identity

Proves `HierarchyN` (`RBM2D.Induction.HierVocab`), the drift part of (`LK_SDE`), as the
composition of `loopGenN` (`LoopGenN`: `genMat 𝓛 = llPairN + egtN`) and the matrix-level
identity `loopDrift_sub_K_deriv_n`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Gauss RBM.Path

/-- **The general-`n` hierarchy identity `HierarchyN`**, the drift part of (`LK_SDE`):
`genMat(𝓛) - ∂_u 𝒦 = ϴ(𝓛-𝒦) + Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}`. -/
theorem hierarchyN : HierarchyN := by
  intro L W _ _ E hL hE u hu0 hu1 M hM k _ hk σ a
  rw [loopGenN L W E hL hE u hu0 hu1 M hM k hk σ a]
  exact loopDrift_sub_K_deriv_n L W E hL hE u hu0 hu1 M k hk σ a

end RBM.Ind

end
