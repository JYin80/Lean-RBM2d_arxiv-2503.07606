/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Induction.PerTimeCalc
import RBM2D.Induction.ScaleFacts
import RBM2D.Green.Pins
import RBM2D.Path.Step2PropsV3
import RBM2D.Path.ScalesBridge
import RBM2D.Loop.Cyclic
import RBM2D.Gauss.LoopInitialValueScalar

/-!
# Steps 4 and 5 of Theorem `lem:main_ind`: `Step4TargetV3`, `Step5TargetV3`

Paper: arXiv:2503.07606, Section 5: Step 4 and Step 5 of the proof of Theorem `lem:main_ind`;
Section 2: (`Eq:L-KGt-flow`) and (`Eq:Gdecay_flow`).  Namespace `RBM.Ind`.

## Results

1. `Step4TargetV3` (`GbEXPHypV3` is `RBM.Green.GbEXPHypV3`) and
   `step4 : Step4TargetV3 d κ c τ E s t`.
2. `Step5TargetV3` (its hypothesis is `Path.Step2Eq53PTV3`, near exponent `3`) and
   `step5 : Step5TargetV3 d κ c τ E s t`.

Every other declaration is `private` with the prefix `s45_`.  Both theorems are conditional on
their hypotheses.

## Step 4 (proof of `step4`)

`Ξ_k := Ξ^{(𝓛-𝒦)}_{u,k} = max_{σ,a} |(𝓛-𝒦)_{u,σ,a}| M_u^k`, `a := M_s`, `y := a^{1/30}`,
`N = W²L²`.  Scale facts (eventually, `u ∈ [s,t]`): `M_u ≥ Im m · N^{c₀}`, `c₀ = min(2c, τ)`
(`scaleFacts_R1`); `a^{29/30} ≤ M_u` (`scaleFacts_R2`); `M_u ≤ W²` (`scaleM_eq'`);
`(η_s/η_u)^4 ≤ a^{2/15}` (`CondStInd`).

* `s45_pt_sup`, `s45_pt_xi_of_perIndex`: the union bound over the `≤ N^{2k}` indices `(σ,a)` of a
  `k`-loop turns a per-index bound `f ≺ B m⁻¹` into `sup f · m ≺ B`; hence `Ξ^{(𝓛)}_{u,k} ≺ 1`
  from `Step3PT` (`s45_xiL_le_one`) and the last step from `Ξ_k ≺ 1` to `Step4PT` (`step4`).
* Case `n = 1` (`s45_one_loop`, `s45_xiLK_one`): `Ξ_1 ≺ 1` from the (`GavLGEX`) clause of
  `GbEXPHypV3 d (κ/2) c τ` at every time sequence `u_n ∈ [s_n,t_n]`, with the deterministic control
  `Ψ² = M_u⁻¹` from `Step3PT` at `k = 2` and (`asGMc`) from `Step2LocalPT`.
* A priori bound at `n = 2` (`s45_two_loop`): `Ξ_2 ≺ 2 a^{1/2}`, all four charges: `(+,+)` from
  `PPTwoLoopPT`, `(+,-)` from `Step2DecayPT` at `D = 4`, `(-,+)` by rotation (`gloop_rotate`,
  `Kcal_rotate`), `(-,-)` by conjugation (`Gsig_conjTranspose`, `Kcal_two`, `s45_Theta_star`).
* Case `n = 2` (`s45_xiLK_two`): two passes of `STOeqPT 2`, since Step 3 gives
  `Λ^{(𝓛-𝒦)} ≺ M_s^{1/2}`, not `M_u^{1/2}`.
* Case `n ≥ 3` (`s45_apriori`, `s45_main_ind`): strong induction with one pass of
  `STOeqPT n` (`Λ = Φ = 1`).  The product terms use `Ξ_2 ≺ 1` and the a priori bound
  `Ξ_n ≺ 2 M_u` (`Step3PT` and `KboundConcl`), which is `≺ 1` after the factor `M_u⁻¹`.  The
  a priori bound is not `M_s^{1/2}` for `𝓛-𝒦`, which `Step3PT` does not give.

## Step 5 (proof of `step5`)

Fix `D`.  Near `|a-b|_L ≤ 6ℓ*_u`: `Step4PT` at `k = 2` with `lkErrMat = lkGen` at `(+,-)`
(`s45_lkErrMat_eq`), and `(M_u²)⁻¹ ≤ exp(√6 (log W)^{3/4}) 𝒯_{u,D}` (`scaleFacts_inv_sq_le_tailT`),
`exp(√6 (log W)^{3/4}) ≤ N^ε` (`s45_R8`, from `SizeTendsto`).  Far: the indicator of `Step2Eq53PTV3`
vanishes, so its right side is `𝒯_{u,D}`; only the far part of (53) is used, which is unchanged by
the near exponents `2`, `5/2`, `3`.  The two cases are joined per index
(`perTimeCalc_of_imp_union`), then `N^ε` is absorbed (`of_forall_rpow_mul`).

## Differences from the one-dimensional argument

* The induction on `n` (`s45_main_ind`) takes `Ξ_2 ≺ A^{1/2}` with `A = W ℓ_u η_u` as a
  hypothesis in the one-dimensional case; here the a priori bound at `n = 2` is `2 M_s^{1/2}`
  (`M_s` in place of `M_u`), so there are two passes at `n = 2`.
* The near/far split of Step 5 (`step5`) uses `stochDom_min` and `T_{u,D+2}` in the
  one-dimensional case; here the `M_u^{-2}` factor is inside `tailT` and `PerTimeDomAt` is per
  index, so neither is needed.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Green
open scoped NNReal ENNReal

section Pins

variable (d : Sizes)

/-- **The statement of Step 4**, with
`GbEXPHyp d (κ/2)` replaced by `GbEXPHypV3 d (κ/2) c τ`.  (`GavLGEX`) is used with
the deterministic control `M_u^{-1}` given by `Step3PT` at `k = 2`.  Paper: Step 4. -/
def Step4TargetV3 (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  KboundConcl κ → GbEXPHypV3 d (κ / 2) c τ → MainIndHyp d κ c τ E s t →
    Step2LocalPT d E s t → Step2DecayPT d E s t → PPTwoLoopPT d E s t → Step3PT d E s t →
    (∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k) → Step4PT d E s t

/-- **The statement of Step 5**: Step 4 at `k = 2` for `|a-b|_L ≤ 6ℓ*_u` and (53) with near
exponent `3` (`Step2Eq53PTV3`) otherwise.  Deterministic given the two inputs and `SizeTendsto`
(the factor `exp(√6 (log W)^{3/4}) ≤ N^ε`). -/
def Step5TargetV3 (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  MainIndHyp d κ c τ E s t → Step4PT d E s t → Step2Eq53PTV3 d E s t → Step5PT d E s t

end Pins

section Charge

private theorem s45_loopOf_one {L : ℕ} (s : Bool) (a : Z2 L) :
    loopOf (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = ⟨[s], [a]⟩ := by
  rfl

private theorem s45_loopOf_two {L : ℕ} (s₁ s₂ : Bool) (a b : Z2 L) :
    loopOf (![s₁, s₂] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) = ⟨[s₁, s₂], [a, b]⟩ := by
  simp [loopOf, List.ofFn_succ]

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `lkGen` at length `1` is the norm of `⟨(G - m) E_a⟩`. -/
private theorem s45_lkGen_one (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (a : Z2 L) :
    lkGen L W E u M (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = ‖avgErr L W E u M s a‖ := by
  unfold lkGen avgErr
  rw [s45_loopOf_one]
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]


private theorem s45_blockMat_herm {E : Matrix (Idx L W) (Idx L W) ℂ} (hM : E.IsHermitian) :
    (blockMat E).IsHermitian :=
  hM.submatrix _

/-- Conjugating the `+` one-loop gives the `-` one-loop. -/
private theorem s45_avgErr_false (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (a : Z2 L) :
    avgErr L W E u M false a = star (avgErr L W E u M true a) := by
  have hH := s45_blockMat_herm hM
  have hG : (greenBlk L W E u M true)ᴴ = greenBlk L W E u M false :=
    Gsig_conjTranspose hH (spectralZ E u) true
  have hm : star (KLoop.mSig E true) = KLoop.mSig E false := by
    simp [KLoop.mSig]
  unfold avgErr
  rw [← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hG, hm]


private theorem s45_Kpm_eq (E u : ℝ) (a b : Z2 L) :
    Kpm L W E u a b = KLoop.Kcal L W E u ⟨[true, false], [a, b]⟩ := by
  rw [KLoop.Kcal_two]
  unfold Kpm
  have : KLoop.mSig E true * KLoop.mSig E false = (Complex.normSq (spectralM E) : ℂ) := by
    simp [KLoop.mSig, Complex.mul_conj]
  rw [this, inv_pow]

/-- `lkErrMat` is `lkGen` at the charge `(+,-)`. -/
private theorem s45_lkErrMat_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    lkErrMat L W E u M a b =
      lkGen L W E u M (![true, false] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) := by
  unfold lkErrMat lkGen
  rw [s45_loopOf_two, s45_Kpm_eq]
  rfl

/-- Rotation: `(-,+)` at `(a,b)` is `(+,-)` at `(b,a)`. -/
private theorem s45_lkGen_mp (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    lkGen L W E u M (![false, true] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) =
      lkGen L W E u M (![true, false] : Fin 2 → Bool) (![b, a] : Fin 2 → Z2 L) := by
  unfold lkGen
  rw [s45_loopOf_two, s45_loopOf_two]
  have h1 := gloop_rotate (L := L) (W := W) (H := blockMat M) (z := spectralZ E u) false a
    (σ := [true]) (a := [b]) rfl
  have h2 := KLoop.Kcal_rotate L W hL hW E hE u ⟨hu0, hu1⟩ false a [true] [b] rfl
  simp only [List.cons_append, List.nil_append] at h1 h2
  rw [h1, h2]


/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise (`S^{(B)}` is real). -/
private theorem s45_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L (star ξ) a b = star (Theta L ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hSB : (SB L).map (starRingEnd ℂ) = SB L := by
    ext x y
    simp only [Matrix.map_apply, SB_apply, sbKernel]
    split_ifs <;> simp [map_ofNat]
  have hmul : (Theta L ξ).map (starRingEnd ℂ) * (1 - star ξ • SB L) = 1 := by
    have h := congrArg (fun A : Matrix (Z2 L) (Z2 L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul L hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB L).map (starRingEnd ℂ) = 1 - star ξ • SB L := by
      ext x y
      have := congrFun (congrFun hSB x) y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul] at this ⊢
      rw [this]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul L hL hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm


/-- The `(-,-)` two-loop is the conjugate of the `(+,+)` two-loop. -/
private theorem s45_gloop_mm {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (a b : Z2 L) :
    gloop L W H z ⟨[false, false], [a, b]⟩ = star (gloop L W H z ⟨[true, true], [a, b]⟩) := by
  have hG : (Gsig H z true)ᴴ = Gsig H z false := Gsig_conjTranspose hH z true
  rw [gloop_two, gloop_two, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Eblk_conjTranspose, Eblk_conjTranspose,
    hG]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Eblk L W b)]
  simp only [Matrix.mul_assoc]

/-- `𝒦` at `(-,-)` is the conjugate of `𝒦` at `(+,+)`. -/
private theorem s45_Kcal_mm (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a b : Z2 L) :
    KLoop.Kcal L W E u ⟨[false, false], [a, b]⟩ = star (KLoop.Kcal L W E u ⟨[true, true], [a, b]⟩) := by
  rw [KLoop.Kcal_two, KLoop.Kcal_two]
  have hm : star (KLoop.mSig E true) = KLoop.mSig E false := by simp [KLoop.mSig]
  have hn : ‖(u : ℂ) * (KLoop.mSig E true * KLoop.mSig E true)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, norm_mul]
    have : ‖KLoop.mSig E true‖ = 1 := by simpa [KLoop.mSig] using norm_spectralM hE
    rw [this, Real.norm_eq_abs, abs_of_nonneg hu0]
    simpa using hu1
  have hT := s45_Theta_star (L := L) hL hn a b
  have hξ : star ((u : ℂ) * (KLoop.mSig E true * KLoop.mSig E true)) =
      (u : ℂ) * (KLoop.mSig E false * KLoop.mSig E false) := by
    rw [star_mul', star_mul', hm, Complex.star_def, Complex.conj_ofReal]
  rw [hξ] at hT
  rw [hT]
  simp only [star_mul', star_inv₀, star_pow, hm, star_natCast]

/-- Conjugation: `(-,-)` at `(a,b)` has the same `lkGen` as `(+,+)` at `(a,b)`. -/
private theorem s45_lkGen_mm (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian) (a b : Z2 L) :
    lkGen L W E u M (![false, false] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) =
      lkGen L W E u M (![true, true] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) := by
  unfold lkGen
  rw [s45_loopOf_two, s45_loopOf_two, s45_gloop_mm (s45_blockMat_herm hM), s45_Kcal_mm hL hE hu0 hu1,
    ← star_sub, norm_star]

/-- At length `1` the loop `𝓛-𝒦` is `⟨(G - m) E_a⟩` for the `+` sign, whichever the sign. -/
private theorem s45_lkGen_one_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    lkGen L W E u M σ a = ‖avgErr L W E u M true (a 0)‖ := by
  obtain ⟨x, rfl⟩ : ∃ x, σ = ![x] := ⟨σ 0, by funext i; fin_cases i; rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = ![b] := ⟨a 0, by funext i; fin_cases i; rfl⟩
  rw [s45_lkGen_one]
  cases x
  · rw [s45_avgErr_false E u M hM, norm_star]
    rfl
  · rfl

end Charge

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- Reindexing the parameter family preserves `PerTimeDomAt`. -/
private theorem s45_pt_comap {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} (f : ∀ l, U' l → U l)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l (f l u) ω) (fun l u ω => ζ l (f l u) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  exact hl (f l u)

/-- `PerTimeDomAt` is invariant under pointwise equality of both sides. -/
private theorem s45_pt_congr {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hξ : ∀ l u ω, ξ l u ω = ξ' l u ω) (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) :
    PerTimeDomAt P size ξ ζ ↔ PerTimeDomAt P size ξ' ζ' := by
  have h1 : ξ = ξ' := by funext l u ω; exact hξ l u ω
  have h2 : ζ = ζ' := by funext l u ω; exact hζ l u ω
  subst h1 h2
  exact Iff.rfl

/-- Reindexing plus pointwise rewriting of both sides. -/
private theorem s45_pt_transfer {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {ξ' ζ' : ∀ l, U' l → Ω → ℝ} (f : ∀ l, U' l → U l)
    (hξ : ∀ l u ω, ξ' l u ω = ξ l (f l u) ω) (hζ : ∀ l u ω, ζ' l u ω = ζ l (f l u) ω)
    (h : PerTimeDomAt P size ξ ζ) : PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  have hset : {ω | (size l : ℝ) ^ τ * ζ' l u ω < ξ' l u ω} =
      {ω | (size l : ℝ) ^ τ * ζ l (f l u) ω < ξ l (f l u) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, hζ]
  rw [hset]
  exact hl (f l u)

/-- A pointwise smaller left side and a pointwise equal right side. -/
private theorem s45_pt_of_le {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hξ : ∀ l u ω, ξ l u ω ≤ ξ' l u ω) (hζ : ∀ l u ω, ζ' l u ω = ζ l u ω)
    (h : PerTimeDomAt P size ξ' ζ) : PerTimeDomAt P size ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) (hl u)
  intro ω hω
  simp only [Set.mem_ofPred_eq, hζ] at hω ⊢
  exact lt_of_lt_of_le hω (hξ l u ω)

/-- A bound that holds deterministically (up to `N^δ` for every `δ > 0`) gives `≺`. -/
private theorem s45_pt_of_det {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ δ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ δ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ] with l hl u
  have hE : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [hE, measure_empty]
  exact zero_le

/-- Multiplication by a positive deterministic factor. -/
private theorem s45_pt_mul_pos {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {c : ∀ l, U l → ℝ}
    (hc : ∀ l u, 0 < c l u) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l u ω * c l u) (fun l u ω => ζ l u ω * c l u) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) (hl u)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_right hcon (hc l u).le
  nlinarith

/-- The union bound over a finite index set of polynomial cardinality: the supremum over the
index `i` inherits the per-index bound (right side independent of `i`). -/
private theorem s45_pt_sup {U I : ℕ → Type*} [∀ l, Fintype (I l)] [∀ l, Nonempty (I l)]
    {ξ : ∀ l, U l → I l → Ω → ℝ} {ζ : ∀ l, U l → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (I l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : PerTimeDomAt P size (U := fun l => U l × I l) (fun l p ω => ξ l p.1 p.2 ω)
      (fun l p _ => ζ l p.1)) :
    PerTimeDomAt P size
      (fun l u ω => Finset.univ.sup' Finset.univ_nonempty (fun i => ξ l u i ω))
      (fun l u _ => ζ l u) := by
  intro τ hτ D hD
  filter_upwards [hC, h τ hτ (D + C) (by linarith)] with l hcard hl u
  have hs : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hs _
  have hset : {ω | (size l : ℝ) ^ τ * ζ l u <
        Finset.univ.sup' Finset.univ_nonempty (fun i => ξ l u i ω)} ⊆
      ⋃ i, {ω | (size l : ℝ) ^ τ * ζ l u < ξ l u i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨i, _, hi⟩ := (Finset.lt_sup'_iff _).1 hω
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hexp : (size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C)) = (size l : ℝ) ^ (-D) := by
    rw [← Real.rpow_add' hs (by rw [show C + -(D + C) = -D by ring]; exact neg_ne_zero.mpr hD.ne')]
    congr 1; ring
  calc P {ω | (size l : ℝ) ^ τ * ζ l u < Finset.univ.sup' Finset.univ_nonempty (fun i => ξ l u i ω)}
      ≤ P (⋃ i, {ω | (size l : ℝ) ^ τ * ζ l u < ξ l u i ω}) := measure_mono hset
    _ ≤ ∑ i, P {ω | (size l : ℝ) ^ τ * ζ l u < ξ l u i ω} := measure_iUnion_fintype_le P _
    _ ≤ ∑ _i : I l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun i _ => hl (u, i)
    _ = ENNReal.ofReal (Fintype.card (I l) * (size l : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ C * (size l : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by rw [hexp]

/-- The product bound `X Y A⁻¹ ≺ Φ` from `X ≺ f`, `Y ≺ g` and `f g A⁻¹ ≤ C Φ`. -/
private theorem s45_pt_quad (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {X Y : ∀ l, U l → Ω → ℝ} {f g A Φ : ∀ l, U l → ℝ}
    (hA : ∀ l u, 0 < A l u) (hY0 : ∀ l u ω, 0 ≤ Y l u ω) (hf : ∀ l u, 0 ≤ f l u)
    (hg : ∀ l u, 0 ≤ g l u) (hΦ : ∀ l u, 0 ≤ Φ l u)
    (hX : PerTimeDomAt P size X fun l u _ => f l u)
    (hY : PerTimeDomAt P size Y fun l u _ => g l u)
    (C : ℝ) (hle : ∀ᶠ l : ℕ in atTop, ∀ u, f l u * g l u * (A l u)⁻¹ ≤ C * Φ l u) :
    PerTimeDomAt P size (fun l u ω => X l u ω * Y l u ω * (A l u)⁻¹) fun l u _ => Φ l u := by
  have hA' : ∀ l u (_ : Ω), 0 ≤ (A l u)⁻¹ := fun l u _ => (inv_pos.2 (hA l u)).le
  have h12 := PerTimeCalc.PerTime.perTimeCalc_mul hsize hY0 (fun l u _ => hf l u) hX hY
  have h3 := PerTimeCalc.PerTime.perTimeCalc_mul hsize hA' (fun l u _ => mul_nonneg (hf l u) (hg l u))
    h12 (PerTimeCalc.PerTime.perTimeCalc_refl hsize hA')
  exact PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun l u _ => hΦ l u) C
    (hle.mono fun l hN u _ => hN u) h3

end Generic

section Scales

variable (d : Sizes)

private theorem s45_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem s45_one_le_W (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem s45_hsize (h : SizeTendsto d) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

private theorem s45_size_ge_W_sq (n : ℕ) : (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have h : d.W n ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]
    exact Nat.le_mul_of_pos_right _ (by have := s45_one_le_L d n; positivity)
  exact_mod_cast h

/-- The cardinality of the index set of a `k`-loop is at most `N^{2k}` once `N ≥ 2`. -/
private theorem s45_card_le (k n : ℕ) (hN2 : 2 ≤ d.size n) :
    (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) =
      2 ^ k * (d.L n * d.L n) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) ≤ d.size n ^ (2 * k) := by
    rw [hcard, pow_mul', sq]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hN2 k) (Nat.pow_le_pow_left hLL k)
  rw [Real.rpow_natCast]
  exact_mod_cast hnat

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ`. -/
private theorem s45_im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ (spectralM (E n)).im ∧ (spectralM (E n)).im ≤ 1 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun n => ⟨?_, ?_⟩⟩
  · have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  · rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith
  · rw [spectralM_im]
    have : Real.sqrt (4 - E n ^ 2) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [sq_nonneg (E n)]⟩
    linarith

/-- `M_u ≥ μ N^{c₀}` for all `u ≤ t n`, eventually. -/
private theorem s45_lower {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) :
    ∃ μ c₀ : ℝ, 0 < μ ∧ 0 < c₀ ∧ (∀ n, μ ≤ (spectralM (E n)).im) ∧
      (∀ n, (spectralM (E n)).im ≤ 1) ∧
      ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
        μ * ((d.size n : ℕ) : ℝ) ^ c₀ ≤ scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, hc, hτ, -, -, -, -, hB, -, hR, -, -, -⟩ := hmain
  obtain ⟨μ, hμ, hμb⟩ := s45_im_bounds hE hκ
  refine ⟨μ, min (2 * c) τ, hμ, lt_min (by linarith) hτ, fun n => (hμb n).1, fun n => (hμb n).2, ?_⟩
  filter_upwards [scaleFacts_R1 d κ c τ E t hE hκ hc hτ hB hR] with n hn u hu
  refine le_trans ?_ (hn u hu)
  exact mul_le_mul_of_nonneg_right (hμb n).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Positivity of the scale on `(-∞, t n]`. -/
private theorem s45_scale_pos {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) {u : ℝ} (hu : u ≤ t n) : 0 < scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, -, -, -, -, ht1, -⟩ := hmain
  exact scaleM_pos (s45_one_le_L d n) (s45_one_le_W d n) (by linarith [hE n]) (lt_of_le_of_lt hu (ht1 n))

/-- `M_s → ∞`. -/
private theorem s45_tendsto_Ms {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) :
    Tendsto (fun n => scaleM (d.L n) (d.W n) (E n) (s n)) atTop atTop := by
  obtain ⟨μ, c₀, hμ, hc₀, -, -, hlow⟩ := s45_lower d hmain
  obtain ⟨-, -, -, -, -, hst, -, hN, -⟩ := hmain
  have h1 : Tendsto (fun n => μ * ((d.size n : ℕ) : ℝ) ^ c₀) atTop atTop :=
    Tendsto.const_mul_atTop hμ ((tendsto_rpow_atTop hc₀).comp hN)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [hlow] with n hn
  exact hn (s n) (hst n)


/-- The eventual scale facts on `[s n, t n]`: `1 ≤ M_s`, `M_s^{29/30} ≤ M_u`, `1 ≤ M_u`, `M_u ≤ W²`
and `(η_s/η_u)^4 ≤ M_s^{2/15}`. -/
private theorem s45_eventual {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ scaleM (d.L n) (d.W n) (E n) (s n) ∧
      ∀ u : ℝ, s n ≤ u → u ≤ t n →
        scaleM (d.L n) (d.W n) (E n) (s n) ^ ((29 : ℝ) / 30) ≤ scaleM (d.L n) (d.W n) (E n) u ∧
        1 ≤ scaleM (d.L n) (d.W n) (E n) u ∧
        scaleM (d.L n) (d.W n) (E n) u ≤ (d.W n : ℝ) ^ 2 ∧
        (etaT (E n) (s n) / etaT (E n) u) ^ 4 ≤
          scaleM (d.L n) (d.W n) (E n) (s n) ^ ((2 : ℝ) / 15) := by
  obtain ⟨μ, c₀, -, -, -, him1, -⟩ := s45_lower d hmain
  have hMs := (s45_tendsto_Ms d hmain).eventually_ge_atTop 1
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  filter_upwards [hMs, scaleFacts_R2 d κ τ E s t hE hκ hC hR, hC] with n h1 h2 hCn
  refine ⟨h1, fun u hsu hut => ?_⟩
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 n)
  have hs1 : s n < 1 := lt_of_le_of_lt hsu hu1
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hM29 := h2 u hsu hut
  refine ⟨hM29, ?_, ?_, ?_⟩
  · exact le_trans (Real.one_le_rpow h1 (by norm_num)) hM29
  · rw [scaleM_eq' (s45_one_le_L d n) hu1]
    have him0 : 0 ≤ (spectralM (E n)).im := (spectralM_im_pos hE2).le
    calc (spectralM (E n)).im * min ((d.W n : ℝ) ^ 2) ((((d.W n * d.L n) ^ 2 : ℕ) : ℝ) * (1 - u))
        ≤ 1 * ((d.W n : ℝ) ^ 2) :=
          mul_le_mul (him1 n) (min_le_left _ _) (le_min (by positivity)
            (mul_nonneg (by positivity) (by linarith))) zero_le_one
      _ = (d.W n : ℝ) ^ 2 := one_mul _
  · rw [etaT_div_etaT hE2 hs1 hu1]
    have hxs : 0 < 1 - s n := by linarith
    have hxt : 0 < 1 - t n := by linarith [ht1 n]
    have hxu : 0 < 1 - u := by linarith
    set a := scaleM (d.L n) (d.W n) (E n) (s n) with ha
    have ha0 : 0 < a := lt_of_lt_of_le one_pos h1
    set r := (1 - s n) / (1 - t n) with hr
    have hr0 : 0 < r := div_pos hxs hxt
    have hr30 : r ^ 30 ≤ a := by
      have h3 : a⁻¹ ≤ (r ^ 30)⁻¹ := by
        rw [← inv_pow]
        have : ((1 - t n) / (1 - s n)) = r⁻¹ := by rw [hr, inv_div]
        rw [this] at hCn
        exact hCn
      exact (inv_le_inv₀ ha0 (pow_pos hr0 30)).1 h3
    have hx : (1 - s n) / (1 - u) ≤ r := by
      rw [hr]
      exact div_le_div_of_nonneg_left hxs.le hxt (by linarith)
    have hx0 : 0 ≤ (1 - s n) / (1 - u) := div_nonneg hxs.le hxu.le
    calc ((1 - s n) / (1 - u)) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hx0 hx 4
      _ = (r ^ 30) ^ ((2 : ℝ) / 15) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
          norm_num
      _ ≤ a ^ ((2 : ℝ) / 15) :=
          Real.rpow_le_rpow (pow_nonneg hr0.le _) hr30 (by norm_num)

end Scales


section Xi

variable (d : Sizes)

/-- From a per-index bound `f ≺ B m⁻¹` (`m > 0`) to the bound `sup_i f · m ≺ B`: the union bound over
the `≤ N^{2k}` indices of a `k`-loop, then multiplication by `m`. -/
private theorem s45_pt_xi_of_perIndex (hsize : Tendsto d.size atTop atTop) {s t : ℕ → ℝ} (k : ℕ)
    {f : ∀ n, TimeIcc s t n → (Fin k → Bool) × (Fin k → Z2 (d.L n)) → Sizes.SeqΩ d → ℝ}
    {m B : ∀ n, TimeIcc s t n → ℝ} (hm : ∀ n u, 0 < m n u)
    (h : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1 * (m n p.1)⁻¹)) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n)
      (fun n u ω => Finset.univ.sup' Finset.univ_nonempty (fun i => f n u i ω) * m n u)
      (fun n u _ => B n u) := by
  have hC : ∀ᶠ n : ℕ in atTop,
      (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) :=
    (hsize.eventually_ge_atTop 2).mono fun n hn => s45_card_le d k n hn
  have h1 := s45_pt_sup (P := Sizes.seqP d) (size := d.size) (U := fun n => TimeIcc s t n)
    (I := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n))) (ξ := f)
    (ζ := fun n u => B n u * (m n u)⁻¹) (C := ((2 * k : ℕ) : ℝ)) (by positivity) hC h
  have h2 := s45_pt_mul_pos (c := m) hm h1
  refine (s45_pt_congr (fun _ _ _ => rfl) (fun n u _ => ?_)).1 h2
  have := (hm n u).ne'
  field_simp

/-- `Step3PT` gives `Ξ^{(𝓛)}_{u,k} ≺ 1` per time. -/
private theorem s45_xiL_le_one {E s t : ℕ → ℝ} (hsize : Tendsto d.size atTop atTop)
    (hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u)
    (h3 : Step3PT d E s t) (k : ℕ) (hk : 1 ≤ k) :
    PT d s t (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k)
      (fun _ _ _ => 1) := by
  have h := s45_pt_xi_of_perIndex d hsize k
    (f := fun n u i ω => loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i.1 i.2)
    (m := fun n u => scaleM (d.L n) (d.W n) (E n) u ^ (k - 1)) (B := fun _ _ => 1)
    (fun n u => pow_pos (hpos n u) _)
    ((s45_pt_congr (fun _ _ _ => rfl) (fun n p _ => by simp [inv_pow])).1 (h3 k hk))
  exact h

end Xi


section TwoLoop

variable (d : Sizes)

/-- The elementary time facts on `[s n, t n]`. -/
private theorem s45_time_facts {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) (u : TimeIcc s t n) : |E n| < 2 ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 := by
  obtain ⟨hκ, hE, -, -, hs0, -, ht1, -⟩ := hmain
  exact ⟨by linarith [hE n], le_trans (hs0 n) u.2.1, lt_of_le_of_lt u.2.2 (ht1 n)⟩

/-- Assembling the four charges of a two-loop from the per-index bounds at each charge. -/
private theorem s45_perIndex_two {E s t : ℕ → ℝ} {ζ : ∀ n, TimeIcc s t n → ℝ}
    (hpp : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![true, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1))
    (hpm : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![true, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1))
    (hmp : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![false, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1))
    (hmm : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![false, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1)) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => ζ n p.1) := by
  intro τ hτ D hD
  filter_upwards [hpp τ hτ D hD, hpm τ hτ D hD, hmp τ hτ D hD, hmm τ hτ D hD] with
    n h1 h2 h3 h4 p
  obtain ⟨u, σ, a⟩ := p
  obtain ⟨x, y, rfl⟩ : ∃ x y, σ = ![x, y] := ⟨σ 0, σ 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨b, b', rfl⟩ : ∃ b b', a = ![b, b'] := ⟨a 0, a 1, by funext i; fin_cases i <;> rfl⟩
  cases x <;> cases y
  · exact h4 (u, b, b')
  · exact h3 (u, b, b')
  · exact h2 (u, b, b')
  · exact h1 (u, b, b')

/-- **A priori bound at `n = 2`**:`Ξ^{(𝓛-𝒦)}_{u,2} ≺ 2 M_s^{1/2}` per time, for all four
charges: `(+,+)` from `PPTwoLoopPT`, `(+,-)` from `Step2DecayPT` at `D = 4`, `(-,+)` by rotation,
`(-,-)` by conjugation. -/
private theorem s45_two_loop {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hdec : Step2DecayPT d E s t) (hPP : PPTwoLoopPT d E s t) :
    PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 2)
      (fun n _ _ => 2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => s45_scale_pos d hmain' n u.2.2
  -- the common right side
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ∀ n, TimeIcc s t n → ℝ, ∀ n u, ζ n u =
      2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) *
        (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ := ⟨fun n u =>
    2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) *
      (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹, fun _ _ => rfl⟩
  -- charge `(+,-)`
  have hpm : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![true, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1) := by
    have h0 : PerTimeDomAt (Sizes.seqP d) d.size
        (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
        (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
        (fun n p _ => ζ n p.1) := PerTimeCalc.PerTime.mono_right_eventually
      (ζ' := fun n p _ => ζ n p.1) (hdec 4 (by norm_num)) (by
        filter_upwards [s45_eventual d hmain'] with n hn p ω
        obtain ⟨h1, hfacts⟩ := hn
        obtain ⟨-, -, hMW, hX⟩ := hfacts p.1.1 p.1.2.1 p.1.2.2
        rw [hζ]
        have hM := hpos n p.1
        set a := scaleM (d.L n) (d.W n) (E n) (s n) with ha
        set Q := (scaleM (d.L n) (d.W n) (E n) p.1 ^ 2)⁻¹ with hQ
        have hQ0 : 0 ≤ Q := inv_nonneg.2 (sq_nonneg _)
        have hX' : (etaT (E n) (s n) / etaT (E n) p.1) ^ 4 ≤ a ^ ((1 : ℝ) / 2) :=
          hX.trans (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
        have he1 : Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) /
            ellT (d.L n) p.1)) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
        have he0 := (Real.exp_pos (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) /
            ellT (d.L n) p.1))).le
        have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast s45_one_le_W d n
        have hw : (d.W n : ℝ) ^ (-(4 : ℝ)) ≤ Q := by
          rw [Real.rpow_neg hW0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            hQ]
          refine inv_anti₀ (pow_pos hM 2) ?_
          calc scaleM (d.L n) (d.W n) (E n) p.1 ^ 2 ≤ ((d.W n : ℝ) ^ 2) ^ 2 :=
                pow_le_pow_left₀ hM.le hMW 2
            _ = (d.W n : ℝ) ^ 4 := by ring
        have ha1 : 1 ≤ a ^ ((1 : ℝ) / 2) := Real.one_le_rpow h1 (by norm_num)
        calc (etaT (E n) (s n) / etaT (E n) p.1) ^ 4 * Q *
              Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) p.1)) +
            (d.W n : ℝ) ^ (-(4 : ℝ))
            ≤ a ^ ((1 : ℝ) / 2) * Q * 1 + Q :=
              add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right hX' hQ0) he1 he0
                (mul_nonneg (Real.rpow_nonneg (by linarith) _) hQ0)) hw
          _ ≤ 2 * a ^ ((1 : ℝ) / 2) * Q := by nlinarith)
    have hfam : (fun (n : ℕ) (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
        (ω : Sizes.SeqΩ d) =>
          lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2) =
        (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![true, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))) := by
      funext n p ω
      exact s45_lkErrMat_eq (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2
    rw [hfam] at h0
    exact h0
  -- charge `(+,+)`
  have hpp : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![true, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1) := by
    have h0 := s45_pt_comap (U := fun n => TimeIcc s t n)
      (U' := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) (fun n p => p.1) hPP
    refine PerTimeCalc.PerTime.perTimeCalc_of_imp h0 ?_
    intro τ' hτ'
    refine ⟨τ', hτ', Eventually.of_forall ?_⟩
    intro n p ω hlt
    rw [hζ] at hlt
    have hM2 : 0 < scaleM (d.L n) (d.W n) (E n) p.1 ^ 2 := pow_pos (hpos n p.1) 2
    have hle := Finset.le_sup' (fun q : Z2 (d.L n) × Z2 (d.L n) =>
      lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![true, true] : Fin 2 → Bool) (![q.1, q.2] : Fin 2 → Z2 (d.L n)))
      (Finset.mem_univ (p.2.1, p.2.2))
    have hNτ : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have ha0 : (0 : ℝ) ≤ scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (le_of_lt (s45_scale_pos d hmain' n (hst n))) _
    change ((d.size n : ℕ) : ℝ) ^ τ' * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) <
      Finset.univ.sup' Finset.univ_nonempty (fun q : Z2 (d.L n) × Z2 (d.L n) =>
        lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![true, true] : Fin 2 → Bool) (![q.1, q.2] : Fin 2 → Z2 (d.L n))) *
        scaleM (d.L n) (d.W n) (E n) p.1 ^ 2
    set M2 := scaleM (d.L n) (d.W n) (E n) p.1 ^ 2 with hM2def
    set a := scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) with hadef
    set Nτ := ((d.size n : ℕ) : ℝ) ^ τ' with hNτdef
    have hinv : M2⁻¹ * M2 = 1 := inv_mul_cancel₀ hM2.ne'
    calc Nτ * a ≤ Nτ * (2 * a) := by nlinarith
      _ = Nτ * (2 * a * M2⁻¹) * M2 := by field_simp
      _ < _ * M2 := mul_lt_mul_of_pos_right hlt hM2
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hM2.le
  -- charge `(-,+)`
  have hmp : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![false, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1) := by
    have h0 := s45_pt_comap (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (U' := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p => (p.1, p.2.2, p.2.1)) hpm
    have hfam : (fun (n : ℕ) (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
        (ω : Sizes.SeqΩ d) => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![true, false] : Fin 2 → Bool) (![p.2.2, p.2.1] : Fin 2 → Z2 (d.L n))) =
        (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![false, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))) := by
      funext n p ω
      obtain ⟨hE2, hu0, hu1⟩ := s45_time_facts d hmain' n p.1
      exact (s45_lkGen_mp (d.three_le_L n) (s45_one_le_W d n) hE2 hu0 hu1 _ _ _).symm
    exact hfam ▸ h0
  -- charge `(-,-)`
  have hmm : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (![false, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))
      (fun n p _ => ζ n p.1) := by
    have hfam : (fun (n : ℕ) (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
        (ω : Sizes.SeqΩ d) => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![true, true] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))) =
        (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (![false, false] : Fin 2 → Bool) (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))) := by
      funext n p ω
      obtain ⟨hE2, hu0, hu1⟩ := s45_time_facts d hmain' n p.1
      exact (s45_lkGen_mm (d.three_le_L n) hE2.le hu0 hu1 _
        (Sizes.seqHflow_isHermitian d n p.1 ω) _ _).symm
    exact hfam ▸ hpp
  have hall := s45_perIndex_two d hpp hpm hmp hmm
  simp only [hζ] at hall
  exact s45_pt_xi_of_perIndex d hsize 2
    (f := fun n u i ω => lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i.1 i.2)
    (m := fun n u => scaleM (d.L n) (d.W n) (E n) u ^ 2)
    (B := fun n _ => 2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2))
    (fun n u => pow_pos (hpos n u) _) hall

end TwoLoop

section OneLoop

variable (d : Sizes)

/-- **The case `n = 1`**:`‖⟨(G_u - m) E_a⟩‖ ≺ M_u⁻¹` per time, from the (`GavLGEX`) clause of
`GbEXPHypV3 d (κ/2) c τ` at every time sequence `u ∈ [s,t]`, with the deterministic control
`Ψ² = M_u⁻¹` given by `Step3PT` at `k = 2`. -/
private theorem s45_one_loop {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hV3 : GbEXPHypV3 d (κ / 2) c τ) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (h3 : Step3PT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := s45_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  refine perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst (V := fun n => Z2 (d.L n))
    (fun n => ⟨0⟩)
    (fun n v q ω => ‖avgErr (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) true q‖)
    (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹) ?_
  intro u hu
  obtain ⟨hN', hB', hE', hu0, hu1, hRu⟩ := v3_premises_of_mainIndHyp d hmain' u hu
  have hMpos : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (u n) :=
    fun n => s45_scale_pos d hmain' n (hu n).2
  -- (asGMc) at the exponent `c₀`, from `Step2LocalPT`
  have hAs : AsGMcSeq d E u c₀ := by
    have h1 := perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ ((1 : ℝ) / 2)) hloc u hu
    unfold AsGMcSeq
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n p _ => Real.rpow_nonneg
      (Nat.cast_nonneg _) _) (Real.sqrt μ⁻¹) ?_ h1
    filter_upwards [hlow] with n hn q ω
    have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast s45_one_le_W d n
    have hy : 0 < (d.W n : ℝ) ^ c₀ := Real.rpow_pos_of_pos hW0 _
    have hpow : ((d.W n : ℝ) ^ c₀) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ c₀ := by
      calc ((d.W n : ℝ) ^ c₀) ^ 2 = ((d.W n : ℝ) ^ 2) ^ c₀ := by
            rw [sq, sq, Real.mul_rpow hW0.le hW0.le]
        _ ≤ ((d.size n : ℕ) : ℝ) ^ c₀ :=
            Real.rpow_le_rpow (by positivity) (s45_size_ge_W_sq d n) hc₀.le
    have hM : μ * ((d.W n : ℝ) ^ c₀) ^ 2 ≤ scaleM (d.L n) (d.W n) (E n) (u n) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hμ.le) (hn (u n) (hu n).2)
    have hinv : (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤
        μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by
      calc (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤ (μ * ((d.W n : ℝ) ^ c₀) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) hM
        _ = μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by rw [mul_inv, inv_pow]
    rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹
        ≤ Real.sqrt (μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt μ⁻¹ * ((d.W n : ℝ) ^ c₀)⁻¹ := by
          rw [Real.sqrt_mul (inv_nonneg.2 hμ.le), Real.sqrt_sq (inv_nonneg.2 hy.le)]
  -- the deterministic control `Ψ² = M_u⁻¹`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n,
      Ψ n = Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := ⟨_, fun _ => rfl⟩
  have hΨsq : ∀ n, Ψ n ^ 2 = (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := fun n => by
    rw [hΨ, Real.sq_sqrt (inv_nonneg.2 (hMpos n).le)]
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => by rw [hΨ]; exact Real.sqrt_nonneg _
  have hΨev : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4)) := by
    filter_upwards [hlow, ((tendsto_rpow_atTop (half_pos hc₀)).comp hN).eventually_ge_atTop μ⁻¹]
      with n hn hgrow
    have hgrow' : μ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := hgrow
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNpos : 0 < ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) :=
      lt_of_lt_of_le (inv_pos.2 hμ) hgrow'
    have h1 : 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      calc (1 : ℝ) = μ * μ⁻¹ := (mul_inv_cancel₀ hμ.ne').symm
        _ ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := mul_le_mul_of_nonneg_left hgrow' hμ.le
    have hsplit : ((d.size n : ℕ) : ℝ) ^ c₀ =
        ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      rw [← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
    have hM : ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) ≤ scaleM (d.L n) (d.W n) (E n) (u n) := by
      refine le_trans ?_ (hn (u n) (hu n).2)
      rw [hsplit]
      nlinarith
    rw [hΨ, Real.sqrt_le_iff]
    refine ⟨Real.rpow_nonneg hN0 _, ?_⟩
    have hsq : (((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4))) ^ 2 = (((d.size n : ℕ) : ℝ) ^ (c₀ / 2))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_neg hN0]
      congr 1; push_cast; ring
    rw [hsq]
    exact inv_anti₀ hNpos hM
  -- the loop control `LoopDetSeq` from `Step3PT` at `k = 2`
  have hLoop : LoopDetSeq d E u Ψ := by
    have h1 := perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n => ⟨((fun _ => true), (fun _ => 0))⟩)
      (fun n v q ω => loopAbs (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ (2 - 1)) (h3 2 (by norm_num)) u hu
    unfold LoopDetSeq
    refine s45_pt_transfer (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p => (p.1, ((![true, false] : Fin 2 → Bool),
        (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))))) ?_ ?_ h1
    · intro n p ω
      simp only [loopAbs, loopPM]
      rw [s45_loopOf_two]
      rfl
    · intro n p ω
      simp only [Nat.reduceSub, pow_one]
      rw [hΨsq]
  have hGav : GavLDetSeq d E u Ψ :=
    ((hV3 hN' hB' E u hE' hu0 hu1 hRu c₀ hc₀).2.2 hAs).2.2 Ψ (c₀ / 4) (by positivity) hΨ0 hΨev hLoop
  unfold GavLDetSeq at hGav
  refine s45_pt_transfer (U := fun n => Unit × Z2 (d.L n)) (fun n p => p) (fun _ _ _ => rfl)
    (fun n p ω => (hΨsq n).symm) hGav

/-- `Ξ^{(𝓛-𝒦)}_{u,1} ≺ 1` per time, from the one-loop bound. -/
private theorem s45_xiLK_one {E s t : ℕ → ℝ} (hsize : Tendsto d.size atTop atTop)
    (hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u)
    (hav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹)) :
    PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 1)
      (fun _ _ _ => 1) := by
  have h1 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Z2 (d.L n)))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => 1 * (scaleM (d.L n) (d.W n) (E n) p.1 ^ 1)⁻¹) :=
    s45_pt_transfer (fun n p => (p.1, p.2.2 0))
      (fun n p ω => s45_lkGen_one_eq _ _ _ (Sizes.seqHflow_isHermitian d n p.1 ω) _ _)
      (fun n p ω => by simp) hav
  exact s45_pt_xi_of_perIndex d hsize 1
    (f := fun n u i ω => lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i.1 i.2)
    (m := fun n u => scaleM (d.L n) (d.W n) (E n) u ^ 1) (B := fun _ _ => 1)
    (fun n u => pow_pos (hpos n u) _) h1

end OneLoop

section Apriori

variable (d : Sizes)

/-- (`ML:Kbound`, `KboundConcl`) `‖𝒦_{u,σ,a}‖ ≺ M_u^{-(k-1)}` per time, deterministically: the parameter
`(L_n, W_n, E_n, u)` lies in `KLoop.Par κ N` with `N = size n` and `KLoop.Mt = scaleM`
(`kloop_Mt_eq`, `u ≤ 1`). -/
private theorem s45_Kbound_pt {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KboundConcl κ) (k : ℕ) (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p _ => ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  refine s45_pt_of_det fun δ hδ => ?_
  filter_upwards [hsize.eventually (hK k hk δ hδ)] with n hn p ω
  obtain ⟨hE2, hu0, hu1⟩ := s45_time_facts d hmain' n p.1
  have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
    p.1, hu0, hu1⟩, p.2.1, p.2.2⟩
  have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ δ * (KLoop.Mt (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1) := h
  rw [kloop_Mt_eq hu1.le] at h'
  exact h'

/-- **The a priori bound**: `Ξ^{(𝓛-𝒦)}_{u,k} ≺ 2 M_u` per time, from `Step3PT` and `KboundConcl`. -/
private theorem s45_apriori {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KboundConcl κ) (h3 : Step3PT d E s t) (k : ℕ) (hk : 1 ≤ k) :
    PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k)
      (fun n u _ => 2 * scaleM (d.L n) (d.W n) (E n) u) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => s45_scale_pos d hmain' n u.2.2
  have h1 := PerTimeCalc.PerTime.perTimeCalc_add hsize (h3 k hk) (s45_Kbound_pt d hmain' hK k hk)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin (j + 1) → Bool) × (Fin (j + 1) → Z2 (d.L n)))
      (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => 2 * scaleM (d.L n) (d.W n) (E n) p.1 *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ (j + 1))⁻¹) := by
    refine s45_pt_of_le (fun n p ω => ?_) (fun n p ω => ?_) h1
    · unfold lkGen
      exact norm_sub_le _ _
    · have hM := (hpos n p.1).ne'
      simp only [Nat.add_sub_cancel, inv_pow]
      rw [pow_succ]
      field_simp
      ring
  exact s45_pt_xi_of_perIndex d hsize (j + 1)
    (f := fun n u i ω => lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i.1 i.2)
    (m := fun n u => scaleM (d.L n) (d.W n) (E n) u ^ (j + 1))
    (B := fun n u => 2 * scaleM (d.L n) (d.W n) (E n) u)
    (fun n u => pow_pos (hpos n u) _) h2

end Apriori

section Induction

variable (d : Sizes)

/-- `Ξ^{(𝓛-𝒦)}_{u,k} ≥ 0` for `M_u ≥ 0`. -/
private theorem s45_xiLK_nonneg {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) (hM : 0 ≤ scaleM L W E u) :
    0 ≤ xiLK L W E u M k := by
  unfold xiLK
  refine mul_nonneg ?_ (pow_nonneg hM _)
  obtain ⟨i⟩ : Nonempty ((Fin k → Bool) × (Fin k → Z2 L)) := inferInstance
  exact le_trans (norm_nonneg _)
    (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Z2 L) => lkGen L W E u M p.1 p.2)
      (Finset.mem_univ i))

/-- `y = a^{1/30}` and the three powers of `a` that occur. -/
private theorem s45_rpow_facts {a : ℝ} (ha : 0 ≤ a) :
    a ^ ((1 : ℝ) / 2) = (a ^ ((1 : ℝ) / 30)) ^ 15 ∧
      a ^ ((29 : ℝ) / 30) = (a ^ ((1 : ℝ) / 30)) ^ 29 ∧ a = (a ^ ((1 : ℝ) / 30)) ^ 30 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

/-- **The case `n = 2`** (two passes of `STOeqPT 2`):
`Ξ^{(𝓛-𝒦)}_{u,2} ≺ 1` per time, from the a priori bound `≺ 2 M_s^{1/2}` and `Ξ^{(𝓛-𝒦)}_{u,1} ≺ 1`.
First pass with `Λ = 1`, `Φ₁ = 1 + y`, `y = M_s^{1/30}`: the product term is
`4 M_s M_u⁻¹ ≤ 4 y`; second pass with `Φ₂ = 1`: `(2+y)² M_u⁻¹ ≤ 9`. -/
private theorem s45_xiLK_two {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hxiL : ∀ k, 1 ≤ k → PT d s t
      (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k) (fun _ _ _ => 1))
    (hxi1 : PT d s t
      (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 1) (fun _ _ _ => 1))
    (hxi2 : PT d s t
      (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 2)
      (fun n _ _ => 2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2)))
    (hSTO2 : STOeqPT d E s t 2) :
    PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 2)
      (fun _ _ _ => 1) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => s45_scale_pos d hmain' n u.2.2
  have hposs : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (s n) :=
    fun n => s45_scale_pos d hmain' n (hst n)
  have hev := s45_eventual d hmain'
  have hy0 : ∀ n, 0 ≤ scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30) :=
    fun n => Real.rpow_nonneg (hposs n).le _
  have hX0 : ∀ n (u : TimeIcc s t n) (ω : Sizes.SeqΩ d) (k : ℕ),
      0 ≤ xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k :=
    fun n u ω k => s45_xiLK_nonneg _ _ _ _ (hpos n u).le
  -- first pass
  have hpass1 : PT d s t
      (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) 2)
      (fun n _ _ => 2 + scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30)) := by
    have h := hSTO2 (fun _ => 1) (fun n => 1 + scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30))
      (fun _ => zero_le_one) (fun n => by linarith [hy0 n]) (Eventually.of_forall fun _ => le_rfl)
      (hxiL 6 (by norm_num))
      (fun m hm1 hm2 => by
        obtain rfl : m = 1 := by omega
        exact PerTimeCalc.PerTime.mono_right_eventually hxi1
          (Eventually.of_forall fun n u ω => by linarith [hy0 n]))
      (fun m hm1 hm2 => by
        obtain rfl : m = 2 := by omega
        refine s45_pt_quad (U := fun n => TimeIcc s t n) hsize
          (f := fun n _ => 2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2))
          (g := fun n _ => 2 * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2))
          (A := fun n u => scaleM (d.L n) (d.W n) (E n) u)
          (Φ := fun n _ => 1 + scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30))
          (fun n u => hpos n u) (fun n u ω => hX0 n u ω 2)
          (fun n _ => mul_nonneg two_pos.le (Real.rpow_nonneg (hposs n).le _))
          (fun n _ => mul_nonneg two_pos.le (Real.rpow_nonneg (hposs n).le _))
          (fun n _ => by linarith [hy0 n]) hxi2 hxi2 4 ?_
        filter_upwards [hev] with n hn u
        obtain ⟨h1, hfacts⟩ := hn
        obtain ⟨h29, -, -, -⟩ := hfacts u.1 u.2.1 u.2.2
        obtain ⟨r1, r2, r3⟩ := s45_rpow_facts (hposs n).le
        set a := scaleM (d.L n) (d.W n) (E n) (s n) with ha
        set y := a ^ ((1 : ℝ) / 30) with hy
        have hy1 : 1 ≤ y := Real.one_le_rpow h1 (by norm_num)
        have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
        have hM : y ^ 29 ≤ scaleM (d.L n) (d.W n) (E n) u := by rw [← r2]; exact h29
        change 2 * a ^ ((1 : ℝ) / 2) * (2 * a ^ ((1 : ℝ) / 2)) *
            (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ 4 * (1 + y)
        rw [r1]
        calc 2 * y ^ 15 * (2 * y ^ 15) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹
            ≤ 2 * y ^ 15 * (2 * y ^ 15) * (y ^ 29)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hypos 29) hM) (by positivity)
          _ = 4 * y := by field_simp; ring
          _ ≤ 4 * (1 + y) := by linarith)
      (PerTimeCalc.PerTime.mono_right_eventually (hxiL 3 (by norm_num))
        (Eventually.of_forall fun n u ω => by linarith [hy0 n]))
    exact PerTimeCalc.PerTime.mono_right_eventually h
      (Eventually.of_forall fun n u ω => by simp only [Real.one_rpow]; linarith)
  -- second pass
  have h2 := hSTO2 (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one) (fun _ => zero_le_one)
    (Eventually.of_forall fun _ => le_rfl) (hxiL 6 (by norm_num))
    (fun m hm1 hm2 => by
      obtain rfl : m = 1 := by omega
      exact hxi1)
    (fun m hm1 hm2 => by
      obtain rfl : m = 2 := by omega
      refine s45_pt_quad (U := fun n => TimeIcc s t n) hsize
        (f := fun n _ => 2 + scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30))
        (g := fun n _ => 2 + scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 30))
        (A := fun n u => scaleM (d.L n) (d.W n) (E n) u) (Φ := fun n _ => 1)
        (fun n u => hpos n u) (fun n u ω => hX0 n u ω 2)
        (fun n _ => by linarith [hy0 n]) (fun n _ => by linarith [hy0 n])
        (fun n _ => zero_le_one) hpass1 hpass1 9 ?_
      filter_upwards [hev] with n hn u
      obtain ⟨h1, hfacts⟩ := hn
      obtain ⟨h29, -, -, -⟩ := hfacts u.1 u.2.1 u.2.2
      obtain ⟨r1, r2, r3⟩ := s45_rpow_facts (hposs n).le
      set a := scaleM (d.L n) (d.W n) (E n) (s n) with ha
      set y := a ^ ((1 : ℝ) / 30) with hy
      have hy1 : 1 ≤ y := Real.one_le_rpow h1 (by norm_num)
      have hM : y ^ 29 ≤ scaleM (d.L n) (d.W n) (E n) u := by rw [← r2]; exact h29
      have hM0 : 0 < scaleM (d.L n) (d.W n) (E n) u := hpos n u
      change (2 + y) * (2 + y) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ 9 * 1
      rw [← div_eq_mul_inv, div_le_iff₀ hM0]
      have hy2 : y ^ 2 ≤ y ^ 29 := pow_le_pow_right₀ hy1 (by norm_num)
      nlinarith)
    (PerTimeCalc.PerTime.mono_right_eventually (hxiL 3 (by norm_num))
      (Eventually.of_forall fun n u ω => le_rfl))
  exact PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun _ _ _ => zero_le_one) 2
    (Eventually.of_forall fun n u ω => by simp only [Real.one_rpow]; linarith) h2

/-- **The induction on `k`**: `Ξ^{(𝓛-𝒦)}_{u,k} ≺ 1` per time, for every `k ≥ 1`: `k = 1` from (`GavLGEX`),
`k = 2` by two passes of `STOeqPT 2`, `k ≥ 3` by strong induction with one pass of `STOeqPT k`
(`Ξ_2 ≺ 1` times the a priori bound `Ξ_k ≺ 2 M_u`, times `M_u⁻¹`). -/
private theorem s45_main_ind {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hK : KboundConcl κ) (hV3 : GbEXPHypV3 d (κ / 2) c τ) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t) (hPP : PPTwoLoopPT d E s t)
    (h3 : Step3PT d E s t) (hSTO : ∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k) :
    ∀ k : ℕ, 1 ≤ k → PT d s t
      (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k) (fun _ _ _ => 1) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => s45_scale_pos d hmain' n u.2.2
  have hev := s45_eventual d hmain'
  have hxiL := s45_xiL_le_one d hsize hpos h3
  have hxi1 := s45_xiLK_one d hsize hpos (s45_one_loop d hV3 hmain' hloc h3)
  have hxi2 := s45_xiLK_two d hmain' hxiL hxi1 (s45_two_loop d hmain' hdec hPP) (hSTO 2 le_rfl)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk1 : k = 1
    · subst hk1; exact hxi1
    by_cases hk2 : k = 2
    · subst hk2; exact hxi2
    have hk3 : 3 ≤ k := by omega
    have hbd : ∀ i, 1 ≤ i → i ≤ k → PT d s t
        (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i)
        (fun n u _ => if i = k then 2 * scaleM (d.L n) (d.W n) (E n) u else 1) := by
      intro i hi1 hik
      by_cases hik' : i = k
      · subst hik'
        simpa using s45_apriori d hmain' hK h3 i hi1
      · simp only [hik', ite_false]
        exact ih i (lt_of_le_of_ne hik hik') hi1
    have h := hSTO k (by omega) (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one)
      (fun _ => zero_le_one) (Eventually.of_forall fun _ => le_rfl) (hxiL (2 * k + 2) (by omega))
      (fun m hm1 hm2 => ih m hm2 hm1)
      (fun m hm1 hm2 => by
        refine s45_pt_quad (U := fun n => TimeIcc s t n) hsize
          (f := fun n u => if m = k then 2 * scaleM (d.L n) (d.W n) (E n) u else 1)
          (g := fun n u => if k - m + 2 = k then 2 * scaleM (d.L n) (d.W n) (E n) u else 1)
          (A := fun n u => scaleM (d.L n) (d.W n) (E n) u) (Φ := fun n _ => 1)
          (fun n u => hpos n u)
          (fun n u ω => s45_xiLK_nonneg _ _ _ _ (hpos n u).le ..)
          (fun n u => by split_ifs <;> linarith [hpos n u])
          (fun n u => by split_ifs <;> linarith [hpos n u])
          (fun n _ => zero_le_one) (hbd m (by omega) hm2)
          (hbd (k - m + 2) (by omega) (by omega)) 2 ?_
        filter_upwards [hev] with n hn u
        obtain ⟨h1, hfacts⟩ := hn
        obtain ⟨h29, hM1, -, -⟩ := hfacts u.1 u.2.1 u.2.2
        have hM0 := hpos n u
        change (if m = k then 2 * scaleM (d.L n) (d.W n) (E n) u else 1) *
            (if k - m + 2 = k then 2 * scaleM (d.L n) (d.W n) (E n) u else 1) *
            (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ 2 * 1
        have hinv : (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM1
        have hinv0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := inv_nonneg.2 hM0.le
        have hcancel : scaleM (d.L n) (d.W n) (E n) u * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ = 1 :=
          mul_inv_cancel₀ hM0.ne'
        by_cases hmk : m = k
        · have hg : ¬ (k - m + 2 = k) := by omega
          rw [ite_eq_left hmk, ite_eq_right hg]
          nlinarith
        · by_cases hmk2 : k - m + 2 = k
          · rw [ite_eq_right hmk, ite_eq_left hmk2]
            nlinarith
          · rw [ite_eq_right hmk, ite_eq_right hmk2]
            nlinarith)
      (hxiL (k + 1) (by omega))
    exact PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun _ _ _ => zero_le_one) 2
      (Eventually.of_forall fun n u ω => by simp only [Real.one_rpow]; linarith) h

end Induction


section Step4

variable (d : Sizes)

/-- **Step 4 of `lem:main_ind`**: `Step4TargetV3`.  Conditional on its hypotheses
(`KboundConcl`, `GbEXPHypV3`, `Step3PT`, `STOeqPT`, the Step 2 outputs), not the paper's Step 4
unconditionally. -/
theorem step4 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step4TargetV3 d κ c τ E s t := by
  intro hK hV3 hmain hloc hdec hPP h3 hSTO k hk
  have hmain' := hmain
  have hall := s45_main_ind d hK hV3 hmain' hloc hdec hPP h3 hSTO k hk
  intro τ' hτ' D hD
  filter_upwards [hall τ' hτ' D hD] with n hn p
  refine le_trans (measure_mono ?_) (hn p.1)
  intro ω hω
  have hM : 0 < scaleM (d.L n) (d.W n) (E n) p.1 := s45_scale_pos d hmain' n p.1.2.2
  have hMk : 0 < scaleM (d.L n) (d.W n) (E n) p.1 ^ k := pow_pos hM k
  have hinv : (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ k * scaleM (d.L n) (d.W n) (E n) p.1 ^ k =
      1 := by
    rw [← mul_pow, inv_mul_cancel₀ hM.ne', one_pow]
  have hle := Finset.le_sup' (fun q : (Fin k → Bool) × (Fin k → Z2 (d.L n)) =>
    lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) q.1 q.2)
    (Finset.mem_univ (p.2.1, p.2.2))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  unfold xiLK
  calc ((d.size n : ℕ) : ℝ) ^ τ' * 1
      = ((d.size n : ℕ) : ℝ) ^ τ' * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ k *
          scaleM (d.L n) (d.W n) (E n) p.1 ^ k := by rw [mul_assoc, hinv, mul_one]
    _ < lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 *
          scaleM (d.L n) (d.W n) (E n) p.1 ^ k := mul_lt_mul_of_pos_right hω hMk
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hMk.le

end Step4

section Step5

variable (d : Sizes)

/-- **The factor `exp(√6 (log W)^{3/4})` is subpolynomial**: `exp(√6 (log W)^{3/4}) ≤ N^ε` eventually, for every `ε > 0`, from `N → ∞` and
`W ≤ N` (`log W ≤ log N`, `(log N)^{3/4} = (log N)(log N)^{-1/4}`). -/
private theorem s45_R8 (hN : SizeTendsto d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.sqrt 6 * Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 4)) ≤
        ((d.size n : ℕ) : ℝ) ^ ε := by
  have hY : Tendsto (fun n => Real.log ((d.size n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hN
  have hY4 : Tendsto (fun n => Real.log ((d.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hY
  filter_upwards [hY4.eventually_ge_atTop (Real.sqrt 6 / ε), hY.eventually_ge_atTop 1] with n h4 h1
  have hW1 : (1 : ℝ) ≤ d.W n := by exact_mod_cast s45_one_le_W d n
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hNW : (d.W n : ℝ) ≤ ((d.size n : ℕ) : ℝ) :=
    le_trans (by nlinarith) (s45_size_ge_W_sq d n)
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le hW0 hNW
  have hlogW0 : 0 ≤ Real.log (d.W n : ℝ) := Real.log_nonneg hW1
  have hlogWN : Real.log (d.W n : ℝ) ≤ Real.log ((d.size n : ℕ) : ℝ) :=
    Real.log_le_log hW0 hNW
  set Y := Real.log ((d.size n : ℕ) : ℝ) with hYdef
  have hYpos : 0 < Y := by linarith
  have h34 : Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 4) ≤ Y ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hlogW0 hlogWN (by norm_num)
  have hsq6 : Real.sqrt 6 ≤ ε * Y ^ ((1 : ℝ) / 4) := by
    rwa [div_le_iff₀ hε, mul_comm] at h4
  have hprod : Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) = Y := by
    rw [← Real.rpow_add hYpos]; norm_num
  rw [Real.rpow_def_of_pos hN0]
  refine Real.exp_le_exp.2 ?_
  calc Real.sqrt 6 * Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 4)
      ≤ Real.sqrt 6 * Y ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_left h34 (Real.sqrt_nonneg _)
    _ ≤ (ε * Y ^ ((1 : ℝ) / 4)) * Y ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hsq6 (Real.rpow_nonneg hYpos.le _)
    _ = ε * (Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4)) := by ring
    _ = Y * ε := by rw [hprod]; ring

/-- **Step 5 of `lem:main_ind`**: `Step5TargetV3`.  Near `|a-b|_L ≤ 6ℓ*_u`:
`Step4PT` at `k = 2` and `(M_u²)⁻¹ ≤ exp(√6 (log W)^{3/4}) 𝒯_{u,D}` (`scaleFacts_inv_sq_le_tailT`),
`exp(…) ≤ N^ε` (`s45_R8`); far: the indicator of `Step2Eq53PTV3` vanishes. -/
theorem step5 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step5TargetV3 d κ c τ E s t := by
  intro hmain h4 h53 D hD
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := s45_hsize d hN
  refine PerTimeCalc.PerTime.of_forall_rpow_mul fun δ hδ => ?_
  have hnear : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ 2) :=
    s45_pt_transfer (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p => (p.1, ((![true, false] : Fin 2 → Bool),
        (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n)))))
      (fun n p ω => s45_lkErrMat_eq _ _ _ _ _) (fun _ _ _ => rfl) (h4 2 (by norm_num))
  refine PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsize hnear (h53 D hD) ?_
  intro τ' hτ'
  refine ⟨τ', hτ', ?_⟩
  filter_upwards [s45_R8 d hN hδ, hsize.eventually_ge_atTop 1] with n hn hn1 p ω hlt
  obtain ⟨hE2, hu0, hu1⟩ := s45_time_facts d hmain' n p.1
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hn1
  have hδ1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ δ := Real.one_le_rpow hN1 hδ.le
  have hNτ : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htail := tailT_pos (s45_one_le_W d n) (d.L n) (E n) D p.1
    (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)
  by_cases hnr : (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) p.1
  · left
    have h1 := scaleFacts_inv_sq_le_tailT (E := E n) (D := D) (s45_one_le_L d n)
      (s45_one_le_W d n) hu1 hnr
    change ((d.size n : ℕ) : ℝ) ^ τ' * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ 2 <
      lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2
    calc ((d.size n : ℕ) : ℝ) ^ τ' * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ 2
        = ((d.size n : ℕ) : ℝ) ^ τ' * (scaleM (d.L n) (d.W n) (E n) p.1 ^ 2)⁻¹ := by
          rw [inv_pow]
      _ ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (Real.exp (Real.sqrt 6 * Real.log (d.W n : ℝ) ^
            ((3 : ℝ) / 4)) * tailT (d.L n) (d.W n) (E n) D p.1
              (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)) := mul_le_mul_of_nonneg_left h1 hNτ
      _ ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (((d.size n : ℕ) : ℝ) ^ δ * tailT (d.L n) (d.W n) (E n) D
            p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn htail.le) hNτ
      _ < _ := hlt
  · right
    change ((d.size n : ℕ) : ℝ) ^ τ' * (((etaT (E n) (s n) / etaT (E n) p.1) ^ (3 : ℝ) *
        (if (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) p.1
          then 1 else 0) + 1) *
        tailT (d.L n) (d.W n) (E n) D p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)) <
      lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2
    rw [ite_eq_right hnr, mul_zero, zero_add, one_mul]
    calc ((d.size n : ℕ) : ℝ) ^ τ' * tailT (d.L n) (d.W n) (E n) D p.1
          (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)
        ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (((d.size n : ℕ) : ℝ) ^ δ * tailT (d.L n) (d.W n) (E n) D
            p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left htail.le hδ1) hNτ
      _ < _ := hlt

end Step5

end RBM.Ind

end
