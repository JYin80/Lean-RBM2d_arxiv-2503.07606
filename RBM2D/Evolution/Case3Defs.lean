/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Defs
import RBM2D.Evolution.KernelExpand
import RBM2D.Evolution.XiBounds
import RBM2D.Evolution.LatticeSums
import RBM2D.Green.Pins

/-!
# The contracts that depend on `lem_GbEXP`, stated on `GbEXPHypV3`

Definitions only (namespace `RBM.Evol`): Case 3 `SumDecayCase3Prec`, the `clt-lemma` cases
`cltY`, `CltCase1Prec`, `CltCase2Prec`, the constant `cCase3`, the bridge and monotonicity
statements `BridgeCase3`, and the upstream bundle `UpstreamSteps34Prec`.
-/

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The Case 3 sum-decay contract**: Case 3 (`sum_res_3`), random, per time.  The
hypotheses are `Bandwidth d 𝔠`, `RangeCond d δ t` (hence the range at `u ≤ t`), the `(τ,D)`
label decay `LabelDecayPT` at the conclusion's `D`, and the (`GijGEX`) input
`GbEXPHypV3 d (κ/2)` (used in the proof of `clt-lemma`).  The Step 2 inputs are on a window
`[s₀,t₀] ∋ u`; the end time `t` of `𝒰` is only required to satisfy `u ≤ t < 1` and the range. -/
def SumDecayCase3Prec (κ 𝔠 δ : ℝ) (C : ℕ → ℝ) : Prop :=
  0 < κ → 0 < 𝔠 → 0 < δ →
  ∀ (k K : ℕ) [NeZero k], 2 ≤ k → ∀ (C' τ D : ℝ), 0 ≤ C' → 0 < τ → 0 < D →
  ∀ (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (σ : ℕ → Fin k → Bool),
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s₀ n) → (∀ n, s₀ n ≤ u n) → (∀ n, u n ≤ t₀ n) →
    (∀ n, u n ≤ t n) → (∀ n, t n < 1) → SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
    Step2LocalPT d E s₀ t₀ → Step2DecayPT d E s₀ t₀ → RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ →
    (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
    (∀ n, (F n).Local τ (u n)) →
    (∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)) →
    LabelDecayPT d E u F τ D →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => Λ n) →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖Ugen (d.L n) (E n) (σ n) (u n) (t n)
        (fun b => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d)) p.2‖)
      (fun n _ _ => (d.W n : ℝ) ^ (C k * τ) * Λ n * ratioR (d.L n) (E n) (u n) (t n) ^ k +
        (d.W n : ℝ) ^ (-D + C k))

/-! ## `clt-lemma`, used in the proof of Case 3 -/

/-- The scalar field `Y_{s,b}` of (`clt-yform`): a local form with one label. -/
def cltY {L W K : ℕ} [NeZero L] [NeZero W] (F : LocalForm L W 1 K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Z2 L) : ℂ :=
  F.eval E s M (fun _ => b)

/-- **`clt-lemma`, Case 1 (`clt-lemma-final-result`)**: `Z` supported in
`|a - b|_L < W^τ ℓ_t`; `Σ_b Z_{ab}(Y_b - 𝔼Y_b) ≺ W^{Cτ} ℓ_t ℓ_u max_b|Z_{ab}| Λ
+ W^{-D} max_b|Z_{ab}|`, per time at `u`.  The hypotheses are the three conditions and the range
condition of the lemma, plus `SizeTendsto`, `RangeCond`, `Bandwidth`, and `GbEXPHypV3`. -/
def CltCase1Prec (κ 𝔠 δ : ℝ) (C : ℝ) : Prop :=
  0 < κ → 0 < 𝔠 → 0 < δ →
  ∀ (K : ℕ) (C' τ D : ℝ), 0 ≤ C' → 0 < τ → 0 < D →
  ∀ (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K)
    (Z : ∀ n, Matrix (Z2 (d.L n)) (Z2 (d.L n)) ℂ),
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s₀ n) → (∀ n, s₀ n ≤ u n) → (∀ n, u n ≤ t₀ n) →
    (∀ n, u n ≤ t n) → (∀ n, t n < 1) → SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
    Step2LocalPT d E s₀ t₀ → Step2DecayPT d E s₀ t₀ → RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ →
    (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
    (∀ n, (F n).Local τ (u n)) →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => Λ n) →
    (∀ n a b, ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ ≤ (zdist2 (d.L n) (a - b) : ℝ) → Z n a b = 0) →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖∑ b : Z2 (d.L n), Z n p.2 b *
        (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))‖)
      (fun n p _ => (Finset.univ.sup' Finset.univ_nonempty fun b => ‖Z n p.2 b‖) *
        ((d.W n : ℝ) ^ (C * τ) * ellT (d.L n) (t n) * ellT (d.L n) (u n) * Λ n +
          (d.W n : ℝ) ^ (-D)))

/-- **`clt-lemma`, Case 2 (`clt-lemma-final-result2`)**:
`|Z_{ab}| ≺ (1 + |a-b|_L)^{-1}` (deterministic, uniformly); `Σ_b Z_{ab}(Y_b - 𝔼Y_b) ≺
W^{Cτ} ℓ_u Λ + W^{-D}`. -/
def CltCase2Prec (κ 𝔠 δ : ℝ) (C : ℝ) : Prop :=
  0 < κ → 0 < 𝔠 → 0 < δ →
  ∀ (K : ℕ) (C' τ D : ℝ), 0 ≤ C' → 0 < τ → 0 < D →
  ∀ (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K)
    (Z : ∀ n, Matrix (Z2 (d.L n)) (Z2 (d.L n)) ℂ),
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s₀ n) → (∀ n, s₀ n ≤ u n) → (∀ n, u n ≤ t₀ n) →
    (∀ n, u n ≤ t n) → (∀ n, t n < 1) → SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
    Step2LocalPT d E s₀ t₀ → Step2DecayPT d E s₀ t₀ → RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ →
    (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
    (∀ n, (F n).Local τ (u n)) →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => Λ n) →
    (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ a b : Z2 (d.L n),
      ‖Z n a b‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε * ((zdist2 (d.L n) (a - b) : ℝ) + 1)⁻¹) →
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖∑ b : Z2 (d.L n), Z n p.2 b *
        (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))‖)
      (fun n _ _ => (d.W n : ℝ) ^ (C * τ) * ellT (d.L n) (u n) * Λ n + (d.W n : ℝ) ^ (-D))

/-- The Case 3 contract constant: `cPrec 𝔠 k + 2|C_clt|` (the `clt-lemma` is applied at the
decay parameter `2τ`, proof of `lem:sum_decay`). -/
def cCase3 (𝔠 cC : ℝ) (k : ℕ) : ℝ := cPrec 𝔠 k + 2 * |cC|

/-- **The bridge to Case 3**: the two `clt-lemma` cases (constant `cC`), the deterministic
Case 1 (explicit, for non-alternating `σ`, applied `ω`-wise) and the kernel bounds give
`SumDecayCase3Prec` with `C = cCase3 𝔠 cC`. -/
def BridgeCase3 : Prop :=
  ∀ (cC : ℝ) (c1 : ℕ → ℝ → ℝ) (κ 𝔠 δ : ℝ),
    CltCase1Prec d κ 𝔠 δ cC → CltCase2Prec d κ 𝔠 δ cC → UgenCase1Explicit c1 →
    XiEntryBound → XiRowBound → XiFirstDiff → XiSecondDiff → ExpInvSum →
    SumDecayCase3Prec d κ 𝔠 δ (cCase3 𝔠 cC)

/-! ## The bundle of upstream statements -/

/-- The bundle: the `𝒦` bound, the corrected `lem_GbEXP` shape at `κ/2`, and the three
statements of the `clt-lemma` cases and Case 3, with `𝔠 := c` (`Bandwidth`) and `δ := τ`
(`RangeCond`) of `MainIndHyp κ c τ`. -/
def UpstreamSteps34Prec (κ c τ : ℝ) (C : ℕ → ℝ) : Prop :=
  KboundConcl κ ∧ RBM.Green.GbEXPHypV3 d (κ / 2) c τ ∧ SumDecayDetPrec κ c τ C ∧
    SumDecayCase5Prec κ c τ C ∧ SumDecayCase3Prec d κ c τ C


end RBM.Evol

end
