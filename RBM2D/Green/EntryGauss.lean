/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.EntryDom
import RBM2D.Green.LDE
import RBM2D.Green.LDEQuadInst
import RBM2D.Green.Pins

/-!
# (`GijGEX`) and (`GiiGEX`) for the Gaussian flow, with no large deviation hypotheses

`entry_bound_stochDom`, `diag_bound_stochDom` and their
`_of_asGMc` forms (`Green/EntryDom.lean`) carry the four large deviation estimates
`hLrow`, `hLcol`, `hLquad`, `hLdiag` as hypotheses.  For the Gaussian flow they are theorems:

| hypothesis | proved in |
| --- | --- |
| `hLrow`  | `stochDom_ldeRow` (`Green/LDE.lean`) |
| `hLcol`  | `stochDom_ldeCol` (`Green/LDE.lean`) |
| `hLdiag` | `stochDom_normSq_Hflow_diag` (`Green/LDE.lean`) |
| `hLquad` | `stochDom_ldeQuad` (`Green/LDEQuadInst.lean`) |

This file is the assembly, in the per-sequence form of `GbEXPHypV3`:
fixed `d`, `κ, 𝔠, δ`, then `SizeTendsto`, `Bandwidth`, the energy and time
sequences `E, t` in the bulk with the range condition, and `c > 0`.  The proofs parallel
the one-dimensional formalization: the body of each
is one call of the `≺` layer on the large deviation theorems.  The
range condition `RangeCond d δ t` and `0 < δ` are premises of `GbEXPHypV3` that no
input uses; they are kept, named with a leading underscore, so that the theorems apply to the
premises of `GbEXPHypV3` in their order.

## Main statements (namespace `RBM.Green`)

* `gijOmegaSeq` : `GijOmegaSeq d E t c` for every `c > 0` (`GijGEX`, on `Ω(t,c)`);
* `giiOmegaSeq` : `GiiOmegaSeq d E t c` for every `c > 0` (`GiiGEX`, on `Ω(t,c)`);
* `gijSeq_of_asGMc`, `giiSeq_of_asGMc` : `GijSeq d E t`, `GiiSeq d E t` under `AsGMcSeq d E t c`
  (`asGMc`).  These are conditional adapters: they are not the statements without the
  hypothesis `AsGMcSeq`.
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind

section EntryGauss

/-- **(`GijGEX`) for the Gaussian flow, `GijOmegaSeq`, for every `c > 0`,** with no large deviation
hypothesis: `entry_bound_stochDom` fed by `stochDom_ldeRow` and `stochDom_ldeCol`
(the proof parallels the one-dimensional formalization).  The premises
are those of `GbEXPHypV3`, in its order; `_hδ` and `_hR` (the range condition) are not used. -/
theorem gijOmegaSeq (d : Sizes) {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (_hδ : 0 < δ)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : RangeCond d δ t) (c : ℝ) (hc : 0 < c) :
    GijOmegaSeq d E t c :=
  entry_bound_stochDom d hκ h𝔠 hsz hbw (fun n => (hE n).le) h1 hc
    (stochDom_ldeRow d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol d hκ hsz (fun n => (hE n).le) h0 h1)

/-- **(`GiiGEX`) for the Gaussian flow, `GiiOmegaSeq`, for every `c > 0`,** with no large deviation
hypothesis: `diag_bound_stochDom` fed by `stochDom_ldeRow`, `stochDom_ldeCol`,
`stochDom_ldeQuad` and `stochDom_normSq_Hflow_diag` (the proof parallels the
one-dimensional formalization).  Same premises as `gijOmegaSeq`. -/
theorem giiOmegaSeq (d : Sizes) {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (_hδ : 0 < δ)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : RangeCond d δ t) (c : ℝ) (hc : 0 < c) :
    GiiOmegaSeq d E t c :=
  diag_bound_stochDom d hκ h𝔠 hsz hbw (fun n => (hE n).le) h0 h1 hc
    (stochDom_ldeRow d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeQuad d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_normSq_Hflow_diag d hsz h0 h1)

/-- **(`GijGEX`) without the indicator, for the Gaussian flow, under (`asGMc`) at `c`:** `GijSeq`.
`entry_bound_stochDom_of_asGMc` fed by `stochDom_ldeRow` and `stochDom_ldeCol`.  A conditional
adapter (the hypothesis `AsGMcSeq d E t c` is the paper's (`asGMc`)), not the statement
without it.  Premises as in `gijOmegaSeq`, then `AsGMcSeq d E t c`. -/
theorem gijSeq_of_asGMc (d : Sizes) {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (_hδ : 0 < δ)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : RangeCond d δ t) (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq d E t c) :
    GijSeq d E t :=
  entry_bound_stochDom_of_asGMc d hκ h𝔠 hsz hbw (fun n => (hE n).le) h1 hc hAs
    (stochDom_ldeRow d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol d hκ hsz (fun n => (hE n).le) h0 h1)

/-- **(`GiiGEX`) without the indicator, for the Gaussian flow, under (`asGMc`) at `c`:** `GiiSeq`.
`diag_bound_stochDom_of_asGMc` fed by the four large deviation theorems.  A conditional adapter,
as `gijSeq_of_asGMc`. -/
theorem giiSeq_of_asGMc (d : Sizes) {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (_hδ : 0 < δ)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
    (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : RangeCond d δ t) (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq d E t c) :
    GiiSeq d E t :=
  diag_bound_stochDom_of_asGMc d hκ h𝔠 hsz hbw (fun n => (hE n).le) h0 h1 hc hAs
    (stochDom_ldeRow d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeCol d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_ldeQuad d hκ hsz (fun n => (hE n).le) h0 h1)
    (stochDom_normSq_Hflow_diag d hsz h0 h1)

end EntryGauss

end RBM.Green
