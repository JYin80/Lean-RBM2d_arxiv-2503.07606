/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Main.BUniv
import RBM2D.Universality.GUEPhase.RandomLayerB

/-!
# `BUniv` from the external input `L32` alone

`bUniv_holds : L32 → BUniv` is `bUniv_of_g1Row` (`Main/BUniv.lean`) applied to the proved
statement `g1Row : G1Row` (`Universality/GUEPhase/RandomLayerB.lean`).  The one leaf that remains a
hypothesis is `L32`, the external [32] Theorem 2.2; every other input of `BUniv` is a proved
theorem (`p7Out_holds`, `p7ExpOut_holds`, `locSC_holds`, `QDiff_holds`).

The two `example`s at the end instantiate `bUniv_holds` at
`witnessSizes` (`L n = n + 3`, `W n = (n + 3)²`, `N = (n + 3)⁶`), `𝔠 = 1/3`, `k = 1`, `κ = 1`,
`O` the bump function, at the energies `E = 0` and `E = 1`; only the external input `L32` stays
a hypothesis of the examples.
-/

namespace RBM.Endpoints

open MeasureTheory Filter Topology Matrix
open RBM RBM.Gauss RBM.Gauss.Sizes
open RBM.Univ

/-- **`BUniv` (bulk universality, `(eq:universality)`) from the one external input `L32`**
([32] Theorem 2.2): `bUniv_of_g1Row` at the proved `g1Row`. -/
theorem bUniv_holds : L32 → BUniv := fun h => bUniv_of_g1Row RBM.Univ.GUEPhase.g1Row h

/-! ## Concrete instances -/

/-- **`bUniv_holds` at the concrete data** `witnessSizes` (`N = (n + 3)⁶ → ∞`, `W = N^{1/3}`),
`𝔠 = 1/3`, `k = 1`, `κ = 1`, `E = 0`, `O = bump` (smooth, compactly supported): every deterministic
hypothesis is discharged, only the external input `L32` stays a hypothesis. -/
example (h32 : L32) :
    Tendsto (fun n =>
        (∫ ω, kPoint 1 (Step1CondCheck.bump : (Fin 1 → ℝ) → ℝ) 0
            (seqXmat_isHermitian witnessSizes n ω).eigenvalues ∂(seqP witnessSizes)) -
        (∫ ω, kPoint 1 (Step1CondCheck.bump : (Fin 1 → ℝ) → ℝ) 0
            (Xmat_isHermitian (witnessSizes.L n) (witnessSizes.W n) ω).eigenvalues
          ∂(gueP (witnessSizes.L n) (witnessSizes.W n)))) atTop (𝓝 0) :=
  bUniv_holds h32 (1 / 3) (by norm_num) witnessSizes admissible_witnessSizes 1 le_rfl 1
    one_pos 0 (by norm_num) Step1CondCheck.bump Step1CondCheck.bump_testFun.1
    Step1CondCheck.bump_testFun.2

/-- The same at the energy `E = 1`, the edge `|E| = 2 - κ` of the allowed window for `κ = 1`. -/
example (h32 : L32) :
    Tendsto (fun n =>
        (∫ ω, kPoint 1 (Step1CondCheck.bump : (Fin 1 → ℝ) → ℝ) 1
            (seqXmat_isHermitian witnessSizes n ω).eigenvalues ∂(seqP witnessSizes)) -
        (∫ ω, kPoint 1 (Step1CondCheck.bump : (Fin 1 → ℝ) → ℝ) 1
            (Xmat_isHermitian (witnessSizes.L n) (witnessSizes.W n) ω).eigenvalues
          ∂(gueP (witnessSizes.L n) (witnessSizes.W n)))) atTop (𝓝 0) :=
  bUniv_holds h32 (1 / 3) (by norm_num) witnessSizes admissible_witnessSizes 1 le_rfl 1
    one_pos 1 (by norm_num) Step1CondCheck.bump Step1CondCheck.bump_testFun.1
    Step1CondCheck.bump_testFun.2

end RBM.Endpoints
