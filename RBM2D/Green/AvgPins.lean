/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.EntryGauss
import RBM2D.Green.CondRow

/-!
# The vocabulary and statements for the (`GavLGEX`) part of `lem_GbEXP`

Paper: arXiv:2503.07606, `lem_GbEXP`, (`asGMc`), (`GavLGEX`); the proof is "that of Lemma 4.2
in [YY_25]", whose steps are: the floor `c W⁻¹ ≤ max 𝓛`, the local law, the fluctuation
averaging display `jasdu` of [YY_25], and the integration-by-parts displays.

The argument: for `Ψ' = max(Ψ, W⁻¹)`,
`AsGMcSeq` + `LoopDetSeq Ψ'` ⟶ `LocalLawDetSeq Ψ'` (LL) ⟶ `FixedTimeFASeq Ψ'` (FA), `IBPDetSeq Ψ'`
(IBP) ⟶ `GavLDetSeq Ψ'` (`AvgBoundDetThm`, the averaging bound with the `≺ Ψ²` input)
⟶ `GavLDetSeq Ψ` (floor lemma `LoopFloorThm`).

Contents:
1. vocabulary: `condDiagBlk` (`E_k(G_kk - m)` on block indices), `LocalLawDetSeq`, `IBPDet`,
   `FARowDet`, `FABlkDet`, `FixedTimeFASeq`, `IBPDetSeq`;
2. the statements: `LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm`, `AvgBoundDetThm`,
   `LoopFloorThm`, `GavLDetFloorThm`, `GavLDetThm`;
3. the wiring, proved: the statements compose to `GbEXPV3Theorem` (the assembly with the four
   theorems of `Green/EntryGauss.lean`; the safe-scale reduction; the chain LL → FA, IBP →
   `AvgBoundDetThm`);
4. two statements proved here outright: `loopFloorThm` (the floor `W⁻² ≤ 4 N^ε Ψ²`) and
   `avgBoundDetThm`;
5. the `η` lower bound as `t → 1`.

`LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm` are proved in `Green/LocalLaw.lean`,
`Green/FlucAvgDet.lean`, `Green/IBPDet.lean`.  `avgBoundDetThm` is the `≺ Ψ²`-input variant of
the averaging bound, and the safe scale `max(Ψ, W^{-1/2})` of the one-dimensional argument
becomes `max(Ψ, W⁻¹)` in `gavLDetThm_of_floor`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Green
open scoped NNReal ENNReal

/-! ## 1. Vocabulary -/

section Vocab

variable (d : Sizes)

/-- `E_k(G_kk - m)` at the block index `k`: `condRow` (`Green/CondRow.lean`) integrates out
row `k` of the fine lattice, `k` read through `splitEquiv`.  This is the conditional diagonal `x` of
the averaging bound. -/
def condDiagBlk (E t : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ d) (k : BlockIndex (d.L n) (d.W n)) : ℂ :=
  condRow d n ((splitEquiv (d.L n) (d.W n)).symm k)
    (fun ω' => greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω') true k k -
      spectralM (E n)) ω

/-- **Local law at a deterministic scale `Ψ`**: `max_{i,j} |(G_t - m)_{ij}| ≺ Ψ` (entries of the
fine lattice, `llErrMat`).  [YY_25] proof of (`GavLGEX`): "`max_{ij} |G_ij - m δ_ij|² ≺ Ψ²`",
the input of `jasdu`.  `AsGMcSeq d E t c` is this at `Ψ = W^{-c}`. -/
def LocalLawDetSeq (E t Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
    (fun n _ _ => Ψ n)

/-- The IBP display with a deterministic control: `max_i |x_i - t m² Σ_k S_ik (G_kk - m)|
≺ Ψ²`.  This is the integration-by-parts input of the averaging bound. -/
def IBPDet (E t : ℕ → ℝ) (x : ∀ n, Sizes.SeqΩ d → BlockIndex (d.L n) (d.W n) → ℂ)
    (Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
    (fun n i ω => ‖x n ω i - (t n : ℂ) * spectralM (E n) ^ 2 *
      ∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
          spectralM (E n))‖)
    (fun n _ _ => Ψ n ^ 2)

/-- `jasdu` for the row family `t_k = S_ik` with a deterministic control: the left
side of the row fluctuation-averaging input of the averaging bound. -/
def FARowDet (E t : ℕ → ℝ) (x : ∀ n, Sizes.SeqΩ d → BlockIndex (d.L n) (d.W n) → ℂ)
    (Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
    (fun n i ω => ‖∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
      ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
        spectralM (E n)) - x n ω k)‖)
    (fun n _ _ => Ψ n ^ 2)

/-- `jasdu` for the block family `t_k = W^{-2} 1(k ∈ 𝓘_a)` (`E_a`, `Def_matE`) with a
deterministic control: the left side of the block fluctuation-averaging input of the averaging
bound. -/
def FABlkDet (E t : ℕ → ℝ) (x : ∀ n, Sizes.SeqΩ d → BlockIndex (d.L n) (d.W n) → ℂ)
    (Ψ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Z2 (d.L n))
    (fun n a ω => ‖∑ k, (blkCoef2 (d.L n) (d.W n) a k : ℂ) *
      ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
        spectralM (E n)) - x n ω k)‖)
    (fun n _ _ => Ψ n ^ 2)

/-- **The fixed-time fluctuation averaging, per-sequence form**: both families of `jasdu` at
`x = condDiagBlk`, control `Ψ²`. -/
def FixedTimeFASeq (E t Ψ : ℕ → ℝ) : Prop :=
  FARowDet d E t (condDiagBlk d E t) Ψ ∧ FABlkDet d E t (condDiagBlk d E t) Ψ

/-- **The IBP display at `x = condDiagBlk`**, per-sequence form of the conclusion of
the weighted conditional-expectation bound for the diagonal. -/
def IBPDetSeq (E t Ψ : ℕ → ℝ) : Prop :=
  IBPDet d E t (condDiagBlk d E t) Ψ

end Vocab

/-! ## 2. The statements -/

section Pins

/-- **`LocalLawDetThm`**.  (`asGMc`) and `max 𝓛 ≺ Ψ²` with the floor
`W⁻¹ ≤ Ψ` give the local law `‖G - m‖_max ≺ Ψ` ([YY_25] proof of (`GavLGEX`):
"`max_{ij}|G_ij - mδ_ij|² ≺ Ψ² := max 𝓛`").  Proof: `gijSeq_of_asGMc`,
`giiSeq_of_asGMc`, `gexRHS ≤ 25 maxLoopPM + W⁻²`, `LoopDetSeq`, union bounds.  Proved in
`Green/LocalLaw.lean`. -/
def LocalLawDetThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ c > (0 : ℝ), AsGMcSeq d E t c →
  ∀ Ψ : ℕ → ℝ, (∀ n, ((d.W n : ℝ))⁻¹ ≤ Ψ n) → LoopDetSeq d E t Ψ → LocalLawDetSeq d E t Ψ

/-- **`FixedTimeFAThm`** (the fluctuation-averaging step `jasdu` of (`GavLGEX`)).  The
premise `η ≥ N^{-K}` is derived from `RangeCond` (`eta_lower_of_rangeCond`, `K = 1`); the
floor `W^{-1/2} ≤ Ψ` of the one-dimensional argument becomes `W⁻¹ ≤ Ψ` (entry scale in d = 2).
Proved in `Green/FlucAvgDet.lean`. -/
def FixedTimeFAThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n ∧ Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq d E t Ψ → FixedTimeFASeq d E t Ψ

/-- **`IBPDetThm`** (the integration-by-parts display used for (`GavLGEX`), with its good-set
input from the local law).  Same premises as `FixedTimeFAThm`.  Proved in
`Green/IBPDet.lean`. -/
def IBPDetThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n ∧ Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq d E t Ψ → IBPDetSeq d E t Ψ

/-- **`AvgBoundDetThm`**: the averaging bound with the controls `Ψ²` in place of
`maxLoopPM` and no `LoopDetSeq` step.  (`GavLGEX`).  Proved below (`avgBoundDetThm`). -/
def AvgBoundDetThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 : ℝ), 0 < κ → 0 < 𝔠 → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) →
  ∀ (x : ∀ n, Sizes.SeqΩ d → BlockIndex (d.L n) (d.W n) → ℂ) (Ψ : ℕ → ℝ),
    IBPDet d E t x Ψ → FARowDet d E t x Ψ → FABlkDet d E t x Ψ → GavLDetSeq d E t Ψ

/-- **`LoopFloorThm`** (the floor).  Under (`asGMc`) and `max 𝓛 ≺ Ψ²`, for every `ε > 0`,
eventually `W⁻² ≤ 4 N^ε Ψ²`.  Paper: [YY_25] "`c W⁻¹ ≤ max 𝓛` in `Ω(t,c)`",
d = 2 form `W⁻² ≤ 4 max 𝓛` (`inv_W2_le_maxLoopPM`).  Proved below (`loopFloorThm`). -/
def LoopFloorThm : Prop :=
  ∀ (d : Sizes) (𝔠 : ℝ), 0 < 𝔠 → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2) → ∀ c > (0 : ℝ), AsGMcSeq d E t c →
  ∀ Ψ : ℕ → ℝ, LoopDetSeq d E t Ψ →
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ((d.W n : ℝ)⁻¹) ^ 2 ≤ 4 * ((d.size n : ℕ) : ℝ) ^ ε * Ψ n ^ 2

/-- **`GavLDetFloorThm`** (the final statement with the floor `W⁻¹ ≤ Ψ` for every `n`):
the (`GavLGEX`) clause of `GbEXPHypV3` (deterministic control) for `Ψ ≥ W⁻¹`. -/
def GavLDetFloorThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ c > (0 : ℝ), AsGMcSeq d E t c →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, ((d.W n : ℝ))⁻¹ ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LoopDetSeq d E t Ψ → GavLDetSeq d E t Ψ

/-- **`GavLDetThm`** (the final statement): the (`GavLGEX`) clause of `GbEXPHypV3`,
with its binders in the order of `GbEXPHypV3`. -/
def GavLDetThm : Prop :=
  ∀ (d : Sizes) (κ 𝔠 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < δ → SizeTendsto d → Bandwidth d 𝔠 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → RangeCond d δ t →
  ∀ c > (0 : ℝ), AsGMcSeq d E t c →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) →
    LoopDetSeq d E t Ψ → GavLDetSeq d E t Ψ

end Pins

/-! ## 3. The wiring -/

section Wiring

/-- `1 ≤ size n`. -/
theorem AvgPins_one_le_size (d : Sizes) (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have hW := d.W_pos n
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have h : 1 ≤ d.size n := by
    unfold Sizes.size
    exact Nat.one_le_pow _ _ (Nat.mul_pos hW hL)
  exact_mod_cast h

/-- **The assembly.**  The four theorems of `Green/EntryGauss.lean` and the final statement give
`GbEXPV3Theorem`: the premises of `GbEXPHypV3` are passed in their order. -/
theorem gbEXPV3Theorem_of_gavLDetThm (h : GavLDetThm) : GbEXPV3Theorem := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc
  exact ⟨gijOmegaSeq d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc,
    giiOmegaSeq d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc, fun hAs =>
      ⟨gijSeq_of_asGMc d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs,
        giiSeq_of_asGMc d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs,
        h d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs⟩⟩

/-- `LoopDetSeq` is monotone in the control. -/
theorem loopDetSeq_mono {d : Sizes} {E t Ψ Ψ' : ℕ → ℝ} (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hΨΨ' : ∀ n, Ψ n ≤ Ψ' n) (h : LoopDetSeq d E t Ψ) : LoopDetSeq d E t Ψ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn p
  refine le_trans (measure_mono fun ω hω => ?_) (hn p)
  have hsq : Ψ n ^ 2 ≤ Ψ' n ^ 2 := pow_le_pow_left₀ (hΨ0 n) (hΨΨ' n) 2
  have hN : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsq hN) hω

/-- **The safe-scale reduction** (exponent `1/2 → 1` as against the one-dimensional argument):
the floor lemma turns the statement for `Ψ ≥ W⁻¹` into
the statement for every `Ψ ≥ 0`, at `Ψ' = max(Ψ, W⁻¹)` and `a' = min(a, 𝔠)`. -/
theorem gavLDetThm_of_floor (hL0 : LoopFloorThm) (hF : GavLDetFloorThm) : GavLDetThm := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs Ψ a ha hΨ0 hΨhi hLoop
  set Ψ' : ℕ → ℝ := fun n => max (Ψ n) ((d.W n : ℝ))⁻¹ with hΨ'
  have hfl : ∀ n, ((d.W n : ℝ))⁻¹ ≤ Ψ' n := fun n => le_max_right _ _
  have hle : ∀ n, Ψ n ≤ Ψ' n := fun n => le_max_left _ _
  have hΨ'hi : ∀ᶠ n : ℕ in atTop, Ψ' n ≤ ((d.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) := by
    filter_upwards [hΨhi, hbw] with n hn hbwn
    have hN1 := AvgPins_one_le_size d n
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have h1 : ((d.size n : ℕ) : ℝ) ^ (-a) ≤ ((d.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_left _ _))
    have h2 : ((d.W n : ℝ))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-𝔠) := by
      rw [Real.rpow_neg hN0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hbwn
    have h3 : ((d.size n : ℕ) : ℝ) ^ (-𝔠) ≤ ((d.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_right _ _))
    exact max_le (hn.trans h1) (h2.trans h3)
  have hG' := hF d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs Ψ' (min a 𝔠) (lt_min ha h𝔠)
    hfl hΨ'hi (loopDetSeq_mono hΨ0 hle hLoop)
  have hE2 : ∀ n, |E n| ≤ 2 := fun n => by linarith [hE n]
  have hfloor := hL0 d 𝔠 h𝔠 hsz hbw E t hE2 c hc hAs Ψ hLoop
  intro τ hτ D hD
  have h4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 4) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 4)).comp hsz).eventually_ge_atTop 4
  filter_upwards [hG' (τ / 2) (half_pos hτ) D hD, hfloor (τ / 4) (by positivity), h4] with
    n hn hfn h4n p
  refine le_trans (measure_mono fun ω hω => ?_) (hn p)
  have hN1 := AvgPins_one_le_size d n
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hWinv0 : 0 ≤ ((d.W n : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hsq : Ψ' n ^ 2 ≤ 4 * N ^ (τ / 4) * Ψ n ^ 2 := by
    have hA : Ψ n ^ 2 ≤ 4 * N ^ (τ / 4) * Ψ n ^ 2 := by
      have : (1 : ℝ) ≤ 4 * N ^ (τ / 4) := by linarith
      nlinarith [sq_nonneg (Ψ n)]
    rcases le_total (Ψ n) ((d.W n : ℝ))⁻¹ with hc' | hc'
    · have : Ψ' n = ((d.W n : ℝ))⁻¹ := max_eq_right hc'
      rw [this]; exact hfn
    · have : Ψ' n = Ψ n := max_eq_left hc'
      rw [this]; exact hA
  have hkey : N ^ (τ / 2) * Ψ' n ^ 2 ≤ N ^ τ * Ψ n ^ 2 := by
    have e1 : N ^ (τ / 2) * Ψ' n ^ 2 ≤ N ^ (τ / 2) * (4 * N ^ (τ / 4) * Ψ n ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0 _)
    have e2 : N ^ (τ / 2) * (4 * N ^ (τ / 4) * Ψ n ^ 2) ≤
        N ^ (τ / 2) * (N ^ (τ / 4) * N ^ (τ / 4) * Ψ n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN0 _)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right h4n (Real.rpow_nonneg hN0 _)
    have e3 : N ^ (τ / 2) * (N ^ (τ / 4) * N ^ (τ / 4) * Ψ n ^ 2) = N ^ τ * Ψ n ^ 2 := by
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add' hN0 (by positivity : τ / 2 + τ / 4 ≠ 0),
        ← Real.rpow_add' hN0 (by positivity : τ / 2 + τ / 4 + τ / 4 ≠ 0)]
      congr 2; ring
    linarith
  exact lt_of_le_of_lt hkey hω

/-- **The chain of the deterministic statements**: LL, FA, IBP and the `≺ Ψ²`-input variant give
the floor statement. -/
theorem gavLDetFloorThm_of_parts (hLL : LocalLawDetThm) (hFA : FixedTimeFAThm)
    (hIBP : IBPDetThm) (hAvg : AvgBoundDetThm) : GavLDetFloorThm := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs Ψ a ha hfl hΨhi hLoop
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => (inv_nonneg.2 (Nat.cast_nonneg _)).trans (hfl n)
  have hll := hLL d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs Ψ hfl hLoop
  have hev : ∀ᶠ n : ℕ in atTop,
      ((d.W n : ℝ))⁻¹ ≤ Ψ n ∧ Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a) :=
    hΨhi.mono fun n hn => ⟨hfl n, hn⟩
  have hfa := hFA d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR Ψ a ha hΨ0 hev hll
  have hibp := hIBP d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR Ψ a ha hΨ0 hev hll
  exact hAvg d κ 𝔠 hκ h𝔠 hsz hbw E t (fun n => (hE n).le) h0 h1 (condDiagBlk d E t) Ψ hibp
    hfa.1 hfa.2

/-- **The whole argument**: the five statements give `GbEXPV3Theorem`. -/
theorem gbEXPV3Theorem_of_parts (hLL : LocalLawDetThm) (hFA : FixedTimeFAThm)
    (hIBP : IBPDetThm) (hAvg : AvgBoundDetThm) (hL0 : LoopFloorThm) : GbEXPV3Theorem :=
  gbEXPV3Theorem_of_gavLDetThm
    (gavLDetThm_of_floor hL0 (gavLDetFloorThm_of_parts hLL hFA hIBP hAvg))

end Wiring


/-! ## 4. Two statements proved here: the floor `LoopFloorThm` and the variant `AvgBoundDetThm` -/

section Proved

variable (d : Sizes)

/-- (copy of the `private` `RBM.Green.tendsto_size_of`, `Green/EntryDom.lean`) -/
private theorem tendsto_size_of' {d : Sizes} (hsz : SizeTendsto d) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

private theorem card_blockIndex' (n : ℕ) :
    Fintype.card (BlockIndex (d.L n) (d.W n)) = d.size n := by
  rw [card_BlockIndex, Sizes.size, mul_comm]

private theorem card_z2' (L : ℕ) [NeZero L] : Fintype.card (Z2 L) = L ^ 2 := by
  simp [Z2, ZMod.card, pow_two]

private theorem card_z2_le' (n : ℕ) : Fintype.card (Z2 (d.L n)) ≤ d.size n ^ 1 := by
  rw [card_z2', Sizes.size, pow_one, mul_pow]
  exact Nat.le_mul_of_pos_left _ (pow_pos (d.W_pos n) 2)

private theorem card_z2_sq_le' (n : ℕ) :
    Fintype.card (Unit × Z2 (d.L n) × Z2 (d.L n)) ≤ d.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, card_z2', Sizes.size]
  have hLW : d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ (d.W_pos n)
  calc 1 * (d.L n ^ 2 * d.L n ^ 2) = d.L n ^ 4 := by ring
    _ ≤ (d.W n * d.L n) ^ 4 := Nat.pow_le_pow_left hLW 4
    _ = ((d.W n * d.L n) ^ 2) ^ 2 := by ring

private theorem card_real_le' {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (h : ∀ n, Fintype.card (V n) ≤ d.size n ^ m) (n : ℕ) :
    (Fintype.card (V n) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (m : ℝ) := by
  rw [Real.rpow_natCast]; exact_mod_cast h n

private theorem highProb_of_perTime' {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (hV : ∀ n, Fintype.card (V n) ≤ d.size n ^ m)
    {ξ ζ : ∀ n, V n → Sizes.SeqΩ d → ℝ} (h : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) {τ : ℝ}
    (hτ : 0 < τ) :
    HighProbAt (Sizes.seqP d) d.size
      (fun n => {ω | ∀ v, ξ n v ω ≤ ((d.size n : ℕ) : ℝ) ^ τ * ζ n v ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
    (stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (m : ℝ)) (Nat.cast_nonneg m)
      (Eventually.of_forall (card_real_le' d hV)) h) hτ

private theorem W_le_size' (n : ℕ) : d.W n ≤ d.size n := by
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have h1 : d.W n ≤ d.W n * d.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : d.W n * d.L n ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact h1.trans h2

private theorem eventually_Kstab2_le_rpow' {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Kstab2 κ (d.L n) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [eventually_Kstab2_mul_rpow_le d hκ h𝔠 hε hsz hbw] with n hn
  have hW : 0 < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWε : 0 < (d.W n : ℝ) ^ ε := Real.rpow_pos_of_pos hW ε
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, div_le_iff₀ hWε] at hn
  have hWN : (d.W n : ℝ) ^ ε ≤ ((d.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow hW.le (by exact_mod_cast W_le_size' d n) hε.le
  have hpos : 0 ≤ (d.W n : ℝ) ^ ε := hWε.le
  linarith

private theorem eventually_one_add_two_kstab2_le' {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 + 2 * Kstab2 κ (d.L n) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [eventually_Kstab2_le_rpow' d hκ h𝔠 hsz hbw (show 0 < ε / 2 by positivity),
    (tendsto_size_of' hsz).eventually (eventually_le_rpow 3 (show 0 < ε / 2 by positivity))]
    with n hK h3
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc 1 + 2 * Kstab2 κ (d.L n)
      ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((d.size n : ℕ) : ℝ) ^ (ε / 2) := by nlinarith
    _ = ((d.size n : ℕ) : ℝ) ^ ε := by
        rw [← Real.rpow_add' hN0 (by positivity : ε / 2 + ε / 2 ≠ 0)]; congr 1; ring

/-- `max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ Ψ²` from `LoopDetSeq`. -/
private theorem maxLoop_dom_of_loopDet' {E t : ℕ → ℝ} {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq d E t Ψ) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n _ ω => maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω))
      (fun n _ _ => Ψ n ^ 2) := by
  have hS := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := ((2 : ℕ) : ℝ))
    (Nat.cast_nonneg 2) (Eventually.of_forall (card_real_le' d (card_z2_sq_le' d))) hLoop
  intro τ hτ D hD
  filter_upwards [hS τ hτ D hD] with n hn u
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  have hω' : ((d.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
      maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) := hω
  unfold maxLoopPM at hω'
  obtain ⟨b, -, hb⟩ := (Finset.lt_sup'_iff _).1 hω'
  exact ⟨((), b.1, b.2), hb⟩

/-- **`AvgBoundDetThm` proved.**  The averaging step
(`of_det` + `norm_avgErr_le`, constant `1 + 2 Kstab2 κ L_n ≤ size^ε`) with the deterministic
control `Ψ²` in place of `maxLoopPM`; no good event, no `LoopDetSeq`. -/
theorem avgBoundDetThm : AvgBoundDetThm := by
  intro d κ 𝔠 hκ h𝔠 hsz hbw E t hE ht0 ht1 x Ψ hIBP hFArow hFAblk
  have hsz' := tendsto_size_of' hsz
  unfold GavLDetSeq
  refine of_det hsz' (fun n p ω => sq_nonneg (Ψ n))
    (Ξ := fun n Φ => {ω | (∀ i : BlockIndex (d.L n) (d.W n),
        ‖x n ω i - (t n : ℂ) * spectralM (E n) ^ 2 *
          ∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
            (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
              spectralM (E n))‖ ≤ Φ * Ψ n ^ 2) ∧
      (∀ i : BlockIndex (d.L n) (d.W n),
        ‖∑ k, (Sblk2 (d.L n) (d.W n) i k : ℂ) *
          ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
            spectralM (E n)) - x n ω k)‖ ≤ Φ * Ψ n ^ 2) ∧
      (∀ a : Z2 (d.L n),
        ‖∑ k, (blkCoef2 (d.L n) (d.W n) a k : ℂ) *
          ((greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true k k -
            spectralM (E n)) - x n ω k)‖ ≤ Φ * Ψ n ^ 2)})
    ?_ (δ := fun _ => 0) (C := fun n => 1 + 2 * Kstab2 κ (d.L n))
    (fun _ => le_rfl) (c₀ := 1) one_pos
    (Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun ε hε => eventually_one_add_two_kstab2_le' d hκ h𝔠 hsz hbw hε) 1 ?_
  · intro τ' hτ'
    have h1 := highProb_of_perTime' d (m := 1) (fun n => (card_blockIndex' d n).le.trans
      (by rw [pow_one])) hIBP hτ'
    have h2 := highProb_of_perTime' d (m := 1) (fun n => (card_blockIndex' d n).le.trans
      (by rw [pow_one])) hFArow hτ'
    have h3 := highProb_of_perTime' d (m := 1) (card_z2_le' d) hFAblk hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2) h3)
      (Eventually.of_forall fun n ω hω => ⟨hω.1.1, hω.1.2, hω.2⟩)
  · refine Eventually.of_forall fun n ω Φ _ _ hmem => ?_
    rintro ⟨_, a⟩
    obtain ⟨hIBPω, hFArowω, hFAblkω⟩ := hmem
    have h := norm_avgErr_le (d.three_le_L n) hκ (hE n) (ht0 n) (ht1 n)
      (Sizes.seqHflow d n (t n) ω) (x n ω)
      (A := Φ * Ψ n ^ 2) (B := Φ * Ψ n ^ 2) (B' := Φ * Ψ n ^ 2)
      hIBPω hFArowω a (hFAblkω a)
    calc _ ≤ _ := h
      _ = _ := by ring

/-- **`LoopFloorThm` proved.**  On `Ω(t, c/2)` (high probability by
`entryDom_goodSet_highProb_of_asGMc`) the lemmas `entryDom_goodEvent_of_llErr` and
`inv_W2_le_maxLoopPM` give `W⁻² ≤ 4 max 𝓛`; `max 𝓛 ≺ Ψ²` then forbids `W⁻² > 4 N^ε Ψ²`,
because both events would have probability `≤ N⁻¹` and cover the whole space. -/
theorem loopFloorThm : LoopFloorThm := by
  intro d 𝔠 h𝔠 hsz hbw E t hE c hc hAs Ψ hLoop ε hε
  have hsz' := tendsto_size_of' hsz
  have hG := entryDom_goodSet_highProb_of_asGMc d h𝔠 hsz hbw hc hAs
  have hM := maxLoop_dom_of_loopDet' d hLoop
  have hWhalf : ∀ᶠ n : ℕ in atTop, (d.W n : ℝ) ^ (-(c / 2)) ≤ 1 / 2 := by
    filter_upwards [hbw, hsz'.eventually (eventually_le_rpow 2
      (show 0 < 𝔠 * (c / 2) by positivity))] with n hbwn h2
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
    have hWc : (2 : ℝ) ≤ (d.W n : ℝ) ^ (c / 2) := by
      calc (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 * (c / 2)) := h2
        _ = (((d.size n : ℕ) : ℝ) ^ 𝔠) ^ (c / 2) := Real.rpow_mul hN0 _ _
        _ ≤ (d.W n : ℝ) ^ (c / 2) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hbwn (by positivity)
    rw [Real.rpow_neg hW.le]
    rw [inv_le_comm₀ (Real.rpow_pos_of_pos hW _) (by norm_num)]
    linarith
  filter_upwards [hG 1 one_pos, hM ε hε 1 one_pos, hWhalf,
    hsz'.eventually (eventually_ge_atTop 3)] with n hGn hMn hWn hN3
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN3' : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN3
  have hsub : RBM.Green.goodSet d E t (c / 2) n ⊆
      {ω | N ^ ε * Ψ n ^ 2 <
        maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω)} := by
    intro ω hω
    have hGE := entryDom_goodEvent_of_llErr (d.L n) (d.W n) (E n) (t n) _
      (Sizes.seqHflow d n (t n) ω) hω
    have hinv := inv_W2_le_maxLoopPM (Sizes.seqHflow_isHermitian d n (t n) ω) (hE n) hGE hWn
    change N ^ ε * Ψ n ^ 2 < _
    linarith
  have hbad := hMn ((), 0)
  have hP1 : Sizes.seqP d (RBM.Green.goodSet d E t (c / 2) n) ≤
      ENNReal.ofReal (N ^ (-(1 : ℝ))) := (measure_mono hsub).trans hbad
  have hsum : (1 : ENNReal) ≤ ENNReal.ofReal (2 * N ^ (-(1 : ℝ))) := by
    have hp : (0 : ℝ) ≤ N ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    calc (1 : ENNReal) = Sizes.seqP d Set.univ := measure_univ.symm
      _ = Sizes.seqP d (RBM.Green.goodSet d E t (c / 2) n ∪
            (RBM.Green.goodSet d E t (c / 2) n)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ Sizes.seqP d (RBM.Green.goodSet d E t (c / 2) n) +
            Sizes.seqP d (RBM.Green.goodSet d E t (c / 2) n)ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (N ^ (-(1 : ℝ))) + ENNReal.ofReal (N ^ (-(1 : ℝ))) :=
          add_le_add hP1 hGn
      _ = ENNReal.ofReal (2 * N ^ (-(1 : ℝ))) := by
          rw [← ENNReal.ofReal_add hp hp]; ring_nf
  have hlt : 2 * N ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    have : N⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have := (ENNReal.ofReal_lt_one.2 hlt)
  exact absurd hsum (not_le.2 this)

/-- **The argument with the two statements proved here inserted**: it remains to supply
`LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm`. -/
theorem gbEXPV3Theorem_of_ports (hLL : LocalLawDetThm) (hFA : FixedTimeFAThm)
    (hIBP : IBPDetThm) : GbEXPV3Theorem :=
  gbEXPV3Theorem_of_parts hLL hFA hIBP avgBoundDetThm loopFloorThm

end Proved

/-! ## 5. Extreme inputs -/

section Extreme

variable (d : Sizes)

/-- **The `RangeCond` edge `t → 1`**: the premise `η_t ≥ N^{-K}` of FA/IBP holds with
`K = 1`, derived: `Im z = (1 - t) Im m ≥ N^{-1+δ} √(κ(4-κ))/2 ≥ N^{-1}` eventually. -/
theorem eta_lower_of_rangeCond {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hsz : SizeTendsto d)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| < 2 - κ) (hR : RangeCond d δ t) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ (spectralZ (E n) (t n)).im := by
  have hκ2 : κ < 2 := by linarith [abs_nonneg (E 0), hE 0]
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc0pos : 0 < c0 := by
    rw [hc0]; exact div_pos (Real.sqrt_pos.2 (by nlinarith)) (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, c0⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hsz).eventually_ge_atTop c0⁻¹
  filter_upwards [hR, hlarge] with n hRn hln
  have hN1 := AvgPins_one_le_size d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hm : c0 ≤ (spectralM (E n)).im := by
    rw [spectralM_im, hc0]
    have hE2 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have h := hE n
      have : |E n| ^ 2 ≤ (2 - κ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h.le 2
      rwa [sq_abs] at this
    have : κ * (4 - κ) ≤ 4 - E n ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt this) (by norm_num)
  have hsplit : N ^ (-1 + δ) = N ^ (-1 : ℝ) * N ^ δ := Real.rpow_add hN0 _ _
  have hp : 0 ≤ N ^ (-1 : ℝ) := Real.rpow_nonneg hN0.le _
  have h1t : N ^ (-1 : ℝ) * N ^ δ ≤ 1 - t n := hsplit ▸ hRn
  have hkey : N ^ (-1 : ℝ) ≤ N ^ (-1 : ℝ) * N ^ δ * c0 := by
    have : 1 ≤ N ^ δ * c0 := by
      have h := mul_le_mul_of_nonneg_right hln hc0pos.le
      rwa [inv_mul_cancel₀ hc0pos.ne'] at h
    nlinarith
  rw [spectralZ_im]
  calc N ^ (-1 : ℝ) ≤ N ^ (-1 : ℝ) * N ^ δ * c0 := hkey
    _ ≤ (1 - t n) * (spectralM (E n)).im :=
        mul_le_mul h1t hm hc0pos.le (le_trans (by positivity) h1t)

end Extreme

end RBM.Green
