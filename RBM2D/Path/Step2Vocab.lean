/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Step2Props
import RBM2D.Loop.Kcal

/-!
# The Step 2 loop vocabulary

The definitions `loopPM`, `lkMat`, `greenBlk`, `avgErr`, `loop3`, `EGt`, `LLpair`, `ELKLK`,
`maxLoopPM`, `gexRHS`, `loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopDeriv`.  `avgErr` uses
`RBM.KLoop.mSig`, written qualified (`KLoop.mSig`; `RBM.KLoop` is not opened).  The definitions
are shared by the later Step 2 files.

Paper: arXiv:2503.07606, `Eq:defGLoop`, `def_EwtG`, `eq:mainStoflow`, `def_ELKLK`, `defEOTE`,
`GijGEX`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `𝓛_{u,(+,-),(a,b)}` at the matrix `M` (`Eq:defGLoop`). -/
def loopPM (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) : ℂ :=
  gloop L W (blockMat M) (spectralZ E u) (pmLoop a b)

/-- `(𝓛 - 𝒦)_{u,(+,-),(a,b)}` at `M` (complex, not its norm). -/
def lkMat (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) : ℂ :=
  loopPM L W E u M a b - Kpm L W E u a b

/-- The block-level resolvent `G_u(σ)` of `M`. -/
def greenBlk (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  Gsig (blockMat M) (spectralZ E u) σ

/-- `⟨G̃_u(σ) E_a⟩ = tr((G_u(σ) - m(σ)) E_a)` (`def_EwtG`; `⟨A⟩ = tr A`). -/
def avgErr (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) (a : Z2 L) : ℂ :=
  Matrix.trace ((greenBlk L W E u M σ - KLoop.mSig E σ • (1 : Matrix (BlockIndex L W)
    (BlockIndex L W) ℂ)) * Eblk L W a)

/-- A three-loop `𝓛_{u,σ,a}` at `M`. -/
def loop3 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin 3 → Bool) (a : Fin 3 → Z2 L) :
    ℂ :=
  gloop L W (blockMat M) (spectralZ E u) (loopOf σ a)

/-- `𝓔^{(G̃)}_{u,(+,-),(a₁,a₂)}` (`def_EwtG`, at `n = 2`): cutting edge 1 (`G(+)`) gives
the loop `(+,+,-),(b,a₁,a₂)`, cutting edge 2 (`G(-)`) gives `(+,-,-),(a₁,b,a₂)`. -/
def EGt (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a₁ a₂ : Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
    (avgErr L W E u M true a * SB L a b * loop3 L W E u M ![true, true, false] ![b, a₁, a₂] +
      avgErr L W E u M false a * SB L a b * loop3 L W E u M ![true, false, false] ![a₁, b, a₂])

/-- `W² Σ_{b₁b₂} 𝓛_{(a₁,b₁)} S_{b₁b₂} 𝓛_{(b₂,a₂)}`, the `k < l` term of (`eq:mainStoflow`), at
`n = 2`. -/
def LLpair (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a₁ a₂ : Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
    loopPM L W E u M a₁ b₁ * SB L b₁ b₂ * loopPM L W E u M b₂ a₂

/-- `𝓔^{((L-K)×(L-K))}_{u,(+,-),(a₁,a₂)}` (`def_ELKLK`). -/
def ELKLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a₁ a₂ : Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ b₁ : Z2 L, ∑ b₂ : Z2 L,
    lkMat L W E u M a₁ b₁ * SB L b₁ b₂ * lkMat L W E u M b₂ a₂

/-- `max_{a,b} |𝓛_{u,(+,-),(a,b)}|` at `M`. -/
def maxLoopPM (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Z2 L × Z2 L => ‖loopPM L W E u M p.1 p.2‖)

/-- The right side of (`GijGEX`) at blocks `a, b`. -/
def gexRHS (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) : ℝ :=
  (∑ a' : Z2 L, ∑ b' : Z2 L,
      if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0) +
    if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0

/-- A six-loop `𝓛_{u,σ,a}` at `M`. -/
def loop6 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin 6 → Bool) (a : Fin 6 → Z2 L) :
    ℂ :=
  gloop L W (blockMat M) (spectralZ E u) (loopOf σ a)

/-- `(𝓔 ⊗ 𝓔)_{u,(+,-),a,a'}` (`defEOTE`; `def_diffakn_k`). -/
def EE (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a a' : Z2 L × Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
    (loop6 L W E u M ![true, false, true, false, true, false] ![a.1, a.2, b', a'.2, a'.1, b] +
      loop6 L W E u M ![false, true, false, true, false, true] ![a.2, a.1, b', a'.1, a'.2, b])

/-- The derivative of `𝓛_{(+,-),a}` through the first edge `G(+)`, along a direction `X`. -/
def cutDeriv1 (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L × Z2 L) : ℂ :=
  -Matrix.trace (greenBlk L W E u M true * blockMat X * greenBlk L W E u M true * Eblk L W a.1 *
    greenBlk L W E u M false * Eblk L W a.2)

/-- The derivative of `𝓛_{(+,-),a}` through the second edge `G(-)`, along `X`. -/
def cutDeriv2 (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L × Z2 L) : ℂ :=
  -Matrix.trace (greenBlk L W E u M true * Eblk L W a.1 * greenBlk L W E u M false * blockMat X *
    greenBlk L W E u M false * Eblk L W a.2)

/-- The directional derivative of `𝓛_{u,(+,-),a}` at `M` along `X`. -/
def loopDeriv (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L × Z2 L) : ℂ :=
  deriv (fun y : ℝ => loopPM L W E u (M + (y : ℂ) • X) a.1 a.2) 0

end RBM.Path

end
