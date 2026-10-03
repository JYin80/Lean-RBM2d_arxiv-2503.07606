/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.PPGoodEvent

/-!
# The deterministic `(+,+)` drift bound `ppDriftN`

The result is the statement `PPDriftN` (`RBM2D.Induction.PPVocab`), proved verbatim, with no
hypothesis added:

`theorem ppDriftN : PPDriftN`.

Paper: arXiv:2503.07606, Section 5: the base case of Step 3 (the `(+,+)` two-loop bound is proved
separately, as the paper's argument covers only `σ = (+,-)`), `def_ELKLK`, `def_EwtG`.  The
argument parallels the one-dimensional formalization.

Layout: 1. the two terms `elklkN`, `egtN` at the `(+,+)` two-loop written out (only the cut
`(k, l') = (1, 2)`, resp. `k = 1, 2` survive); 2. the near/far split of a bilinear
`S^{(B)}`-sum over `Z_L²` (window count `(2r+1)²` of `KLoop.card_ball_le`; the `d = 1` factor is
`6 e ℓ'`); 3. the clauses (G1), (G2) and the definition of `J` as pointwise bounds; 4. the
arithmetic (`9`, `18`, `2 ≤ 1000`); 5. the theorem `ppDriftN`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The two terms at the `(+,+)` two-loop -/

section Algebra

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem PPD_loopOf_pp (a : Fin 2 → Z2 L) :
    loopOf sigPPN a = (⟨[true, true], [a 0, a 1]⟩ : LoopIdx (Z2 L)) := by
  simp [loopOf, sigPPN, List.ofFn_succ]

/-- `𝓔^{LK×LK}` at `I = ((+,+),(a₀,a₁))`: the only surviving cut is `(k, l') = (1, 2)`
(`Ioc 2 2 = ∅`), with `cutGlueL 1 2 x I = ((+,+),(x,a₁))` and `cutGlueR 1 2 y I = ((+,+),(a₀,y))`. -/
private theorem PPD_elklk_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin 2 → Z2 L) :
    elklkN L W E u M (loopOf sigPPN a) =
      (W : ℂ) ^ 2 * ∑ x : Z2 L, ∑ y : Z2 L,
        LKf L W E u M ⟨[true, true], [x, a 1]⟩ * SB L x y *
          LKf L W E u M ⟨[true, true], [a 0, y]⟩ := by
  rw [PPD_loopOf_pp]
  have hlen : (⟨[true, true], [a 0, a 1]⟩ : LoopIdx (Z2 L)).length = 2 := rfl
  simp only [elklkN, hlen, show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide)]
  simp [show Finset.Ioc (1 : ℕ) 2 = ({2} : Finset ℕ) from by decide,
    LoopIdx.cutGlueL, LoopIdx.cutGlueR, List.take, List.drop]

/-- `𝓔^{(G̃)}` at `I = ((+,+),(a₀,a₁))`: both cuts `k = 1, 2` carry the charge `+`; `cutGlue 1 y I =
((+,+,+),(y,a₀,a₁))` and `cutGlue 2 y I = ((+,+,+),(a₀,y,a₁))`. -/
private theorem PPD_egt_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin 2 → Z2 L) :
    egtN L W E u M (loopOf sigPPN a) =
      (W : ℂ) ^ 2 * ((∑ x : Z2 L, ∑ y : Z2 L,
          avgErr L W E u M true x * SB L x y * LLf L W E u M ⟨[true, true, true], [y, a 0, a 1]⟩) +
        ∑ x : Z2 L, ∑ y : Z2 L,
          avgErr L W E u M true x * SB L x y * LLf L W E u M ⟨[true, true, true], [a 0, y, a 1]⟩) := by
  rw [PPD_loopOf_pp]
  have hlen : (⟨[true, true], [a 0, a 1]⟩ : LoopIdx (Z2 L)).length = 2 := rfl
  simp only [egtN, hlen, show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [LoopIdx.cutGlue, List.getD, List.take, List.drop]

end Algebra

/-! ## 2. The near/far split of a bilinear `S^{(B)}`-sum over `Z_L²` -/

section CoreSum

variable {L : ℕ} [NeZero L]

private theorem PPD_card_Z2 : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

/-- The near/far split of an `ℓ¹` sum over `Z_L²`: `f` bounded by `B` everywhere and by `δ` at
periodic distance `≥ r` from `p` has `Σ_x |f x| ≤ B (2r+1)² + L² δ` (window count of
`KLoop.card_ball_le`; the `d = 1` factor is `6 e ℓ'`). -/
private theorem PPD_sum_norm_le_near (p : Z2 L) {r δ B : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    {f : Z2 L → ℂ} (hf : ∀ x, ‖f x‖ ≤ B)
    (hfd : ∀ x, r ≤ (zdist2 L (p - x) : ℝ) → ‖f x‖ ≤ δ) :
    ∑ x : Z2 L, ‖f x‖ ≤ B * (2 * r + 1) ^ 2 + (L : ℝ) ^ 2 * δ := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  set near : Finset (Z2 L) := Finset.univ.filter fun x => (zdist2 L (p - x) : ℝ) ≤ r with hnear
  have hpt : ∀ x : Z2 L, ‖f x‖ ≤ (if x ∈ near then B else 0) + δ := by
    intro x
    by_cases hx : x ∈ near
    · simp only [hx, ↓reduceIte]; linarith [hf x]
    · have h : r ≤ (zdist2 L (p - x) : ℝ) := by
        simp only [hnear, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx
        exact hx.le
      simpa [hx] using hfd x h
  have hcard : (near.card : ℝ) ≤ (2 * r + 1) ^ 2 := KLoop.card_ball_le L p r hr
  calc ∑ x : Z2 L, ‖f x‖ ≤ ∑ x : Z2 L, ((if x ∈ near then B else 0) + δ) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = B * near.card + (L : ℝ) ^ 2 * δ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, PPD_card_Z2]
        ring
    _ ≤ B * (2 * r + 1) ^ 2 + (L : ℝ) ^ 2 * δ := by
        have := mul_le_mul_of_nonneg_left hcard hB
        linarith

/-- **The two-index core estimate** (with
the window count `(2r+1)²` of `Z_L²`): `S^{(B)}` is row-stochastic, so it costs nothing, and the
`x`-sum is confined to the window by the decay of `f`. -/
private theorem PPD_core_sum (hL : 3 ≤ L) {p : Z2 L} {r δ Bf Bg : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hBg : 0 ≤ Bg) {f g : Z2 L → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf)
    (hfd : ∀ x, r ≤ (zdist2 L (p - x) : ℝ) → ‖f x‖ ≤ δ) (hg : ∀ y, ‖g y‖ ≤ Bg) :
    ‖∑ x : Z2 L, ∑ y : Z2 L, f x * SB L x y * g y‖ ≤
      Bg * (Bf * (2 * r + 1) ^ 2 + (L : ℝ) ^ 2 * δ) := by
  have hinner : ∀ x : Z2 L, ‖∑ y : Z2 L, f x * SB L x y * g y‖ ≤ ‖f x‖ * Bg := by
    intro x
    calc ‖∑ y : Z2 L, f x * SB L x y * g y‖
        ≤ ∑ y : Z2 L, ‖f x * SB L x y * g y‖ := norm_sum_le _ _
      _ = ‖f x‖ * ∑ y : Z2 L, ‖SB L x y‖ * ‖g y‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [norm_mul, norm_mul, mul_assoc]
      _ ≤ ‖f x‖ * ∑ y : Z2 L, ‖SB L x y‖ * Bg :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hg y) (norm_nonneg _))
            (norm_nonneg _)
      _ = ‖f x‖ * ((∑ y : Z2 L, ‖SB L x y‖) * Bg) := by rw [Finset.sum_mul]
      _ = ‖f x‖ * Bg := by rw [RBM.Gauss.sum_norm_SB_row L hL x]; ring
  have houter : ‖∑ x : Z2 L, ∑ y : Z2 L, f x * SB L x y * g y‖ ≤ ∑ x : Z2 L, ‖f x‖ * Bg :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hinner x)
  refine houter.trans ?_
  rw [← Finset.sum_mul]
  calc (∑ x : Z2 L, ‖f x‖) * Bg
      ≤ (Bf * (2 * r + 1) ^ 2 + (L : ℝ) ^ 2 * δ) * Bg :=
        mul_le_mul_of_nonneg_right (PPD_sum_norm_le_near p hr hδ hf hfd) hBg
    _ = Bg * (Bf * (2 * r + 1) ^ 2 + (L : ℝ) ^ 2 * δ) := by ring

/-- `S^{(B)}` is symmetric: the two orders of a bilinear `S^{(B)}`-sum agree. -/
private theorem PPD_sum_swap (f g : Z2 L → ℂ) :
    ∑ x : Z2 L, ∑ y : Z2 L, g x * SB L x y * f y =
      ∑ y : Z2 L, ∑ x : Z2 L, f y * SB L y x * g x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have hS : SB L x y = SB L y x := (congrFun (congrFun (SB_transpose L) x) y).symm
  rw [hS]
  ring

end CoreSum

/-! ## 3. The clauses of `GoodSetPPN` as pointwise bounds -/

section GoodBounds

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem PPD_loopOf_two (x y : Z2 L) :
    loopOf (![true, true] : Fin 2 → Bool) (![x, y] : Fin 2 → Z2 L) =
      (⟨[true, true], [x, y]⟩ : LoopIdx (Z2 L)) := by
  simp [loopOf, List.ofFn_succ]

private theorem PPD_loopOf_three (x y z : Z2 L) :
    loopOf (fun _ : Fin 3 => true) (![x, y, z] : Fin 3 → Z2 L) =
      (⟨[true, true, true], [x, y, z]⟩ : LoopIdx (Z2 L)) := by
  simp [loopOf, List.ofFn_succ]

private theorem PPD_loopOf_one (s : Bool) (a : Z2 L) :
    loopOf (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = (⟨[s], [a]⟩ : LoopIdx (Z2 L)) := by
  rfl

/-- `lkGen` at length `1` is the norm of `⟨(G - m) E_a⟩`. -/
private theorem PPD_lkGen_one (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (a : Z2 L) :
    lkGen L W E u M (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = ‖avgErr L W E u M s a‖ := by
  unfold lkGen avgErr
  rw [PPD_loopOf_one]
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]

/-- (G1) at a label: `‖⟨(G - m) E_x⟩‖ ≤ Γ M⁻¹`. -/
private theorem PPD_avgErr_le {E u Γ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hMv : 0 < scaleM L W E u) (hG1 : xiLK L W E u M 1 ≤ Γ) (x : Z2 L) :
    ‖avgErr L W E u M true x‖ ≤ Γ * (scaleM L W E u)⁻¹ := by
  have h1 : lkGen L W E u M (![true] : Fin 1 → Bool) (![x] : Fin 1 → Z2 L) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin 1 → Bool) × (Fin 1 → Z2 L) => lkGen L W E u M p.1 p.2) :=
    Finset.le_sup' (fun p : (Fin 1 → Bool) × (Fin 1 → Z2 L) => lkGen L W E u M p.1 p.2)
      (Finset.mem_univ (![true], ![x]))
  rw [PPD_lkGen_one] at h1
  unfold xiLK at hG1
  have h2 : ‖avgErr L W E u M true x‖ * scaleM L W E u ≤ Γ := by
    refine le_trans ?_ hG1
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right h1 hMv.le
  calc ‖avgErr L W E u M true x‖
      = ‖avgErr L W E u M true x‖ * scaleM L W E u * (scaleM L W E u)⁻¹ := by field_simp
    _ ≤ Γ * (scaleM L W E u)⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hMv.le)

/-- (G2) at a `3`-loop: `‖𝓛_{(+,+,+),(x,y,z)}‖ ≤ Γ Φ₃ M⁻²`. -/
private theorem PPD_loop3_le {E u B : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hMv : 0 < scaleM L W E u) (hxi : xiL L W E u M 3 ≤ B) (x y z : Z2 L) :
    ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ ≤ B * (scaleM L W E u)⁻¹ ^ 2 := by
  have h1 : loopAbs L W E u M (fun _ : Fin 3 => true) (![x, y, z] : Fin 3 → Z2 L) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin 3 → Bool) × (Fin 3 → Z2 L) => loopAbs L W E u M p.1 p.2) :=
    Finset.le_sup' (fun p : (Fin 3 → Bool) × (Fin 3 → Z2 L) => loopAbs L W E u M p.1 p.2)
      (Finset.mem_univ ((fun _ => true), ![x, y, z]))
  have h0 : loopAbs L W E u M (fun _ : Fin 3 => true) (![x, y, z] : Fin 3 → Z2 L) =
      ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ := by
    unfold loopAbs LLf
    rw [PPD_loopOf_three]
  rw [h0] at h1
  unfold xiL at hxi
  have h2 : ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ * scaleM L W E u ^ 2 ≤ B := by
    refine le_trans ?_ hxi
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hMv2 : 0 < scaleM L W E u ^ 2 := by positivity
  calc ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖
      = ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ * scaleM L W E u ^ 2 *
          (scaleM L W E u)⁻¹ ^ 2 := by field_simp
    _ ≤ B * (scaleM L W E u)⁻¹ ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)

/-- The definition of `J`: `‖(𝓛-𝒦)_{(+,+),(x,y)}‖ ≤ J M⁻²`. -/
private theorem PPD_lk2_le {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hMv : 0 < scaleM L W E u) (x y : Z2 L) :
    ‖LKf L W E u M ⟨[true, true], [x, y]⟩‖ ≤ jPPN L W E u M * (scaleM L W E u)⁻¹ ^ 2 := by
  have h1 : lkGen L W E u M (![true, true] : Fin 2 → Bool) (![x, y] : Fin 2 → Z2 L) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]) :=
    Finset.le_sup' (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2])
      (Finset.mem_univ (x, y))
  have h0 : lkGen L W E u M (![true, true] : Fin 2 → Bool) (![x, y] : Fin 2 → Z2 L) =
      ‖LKf L W E u M ⟨[true, true], [x, y]⟩‖ := by
    unfold lkGen LKf LLf
    rw [PPD_loopOf_two]
  rw [h0] at h1
  unfold jPPN
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hMv.ne', one_pow, mul_one]
  exact h1

/-- A pair of labels of a tuple is at distance `≤ maxDist` from each other. -/
private theorem PPD_le_maxDist {n : ℕ} (a : Fin n → Z2 L) (i j : Fin n) :
    zdist2 L (a i - a j) ≤ KLoop.maxDist L a := by
  unfold KLoop.maxDist
  exact Finset.le_sup (f := fun p : Fin n × Fin n => zdist2 L (a p.1 - a p.2))
    (Finset.mem_univ (i, j))

/-- The decay clause of `GoodSetPPN` at a `2`-loop `((+,+),(x,p))`, far from the anchor `p`:
`‖(𝓛-𝒦)‖ ≤ W^{-D'}` (`loopAbs ≥ 0`). -/
private theorem PPD_dec_lk2 {E u τ' D' : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hdec : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) →
        loopAbs L W E u M σ a + lkGen L W E u M σ a ≤ (W : ℝ) ^ (-D'))
    (x p : Z2 L) (hx : ellT L u * (W : ℝ) ^ τ' ≤ (zdist2 L (p - x) : ℝ)) :
    ‖LKf L W E u M ⟨[true, true], [x, p]⟩‖ ≤ (W : ℝ) ^ (-D') := by
  have hmd : (zdist2 L (p - x) : ℝ) ≤ (KLoop.maxDist L (![x, p] : Fin 2 → Z2 L) : ℝ) :=
    Nat.cast_le.2 (PPD_le_maxDist (![x, p] : Fin 2 → Z2 L) 1 0)
  have h := hdec 2 (by norm_num) (by norm_num) (![true, true] : Fin 2 → Bool)
    (![x, p] : Fin 2 → Z2 L) (hx.trans hmd)
  have h0 : lkGen L W E u M (![true, true] : Fin 2 → Bool) (![x, p] : Fin 2 → Z2 L) =
      ‖LKf L W E u M ⟨[true, true], [x, p]⟩‖ := by
    unfold lkGen LKf LLf
    rw [PPD_loopOf_two]
  rw [← h0]
  have hla : 0 ≤ loopAbs L W E u M (![true, true] : Fin 2 → Bool) (![x, p] : Fin 2 → Z2 L) :=
    norm_nonneg _
  linarith

/-- The decay clause of `GoodSetPPN` at a `3`-loop `((+,+,+),(x,y,z))` with `maxDist ≥ r`:
`‖𝓛‖ ≤ W^{-D'}` (`lkGen ≥ 0`). -/
private theorem PPD_dec_loop3 {E u τ' D' : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hdec : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) →
        loopAbs L W E u M σ a + lkGen L W E u M σ a ≤ (W : ℝ) ^ (-D'))
    (x y z : Z2 L)
    (hx : ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L (![x, y, z] : Fin 3 → Z2 L) : ℝ)) :
    ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ ≤ (W : ℝ) ^ (-D') := by
  have h := hdec 3 (by norm_num) (by norm_num) (fun _ : Fin 3 => true)
    (![x, y, z] : Fin 3 → Z2 L) hx
  have h0 : loopAbs L W E u M (fun _ : Fin 3 => true) (![x, y, z] : Fin 3 → Z2 L) =
      ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ := by
    unfold loopAbs LLf
    rw [PPD_loopOf_three]
  rw [← h0]
  have hlk : 0 ≤ lkGen L W E u M (fun _ : Fin 3 => true) (![x, y, z] : Fin 3 → Z2 L) :=
    norm_nonneg _
  linarith

end GoodBounds

/-! ## 4. The arithmetic (`9`, `18`, `2 ≤ 1000`) -/

/-- The arithmetic of the `(+,+)` drift bound: with `M = W² ℓ² η`, `q = M⁻¹`, `r = ℓ ρ`,
`ρ = W^{τ'}`, `N = W² L²`, `(2r+1)² ≤ 9 r²` for `r ≥ 1`, `W² ℓ² q = η⁻¹`. -/
private theorem PPD_arith {Wr ℓ ρ ηv Mv q Lr δ J Γ Φ : ℝ} (hWr : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hρ : 1 ≤ ρ)
    (hη : 0 < ηv) (hMv1 : 1 ≤ Mv) (hMeq : Mv = Wr ^ 2 * ℓ ^ 2 * ηv) (hq : q = Mv⁻¹)
    (hLr : 1 ≤ Lr) (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) :
    Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2 + Lr ^ 2 * δ)) +
      Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2 + Lr ^ 2 * δ))) ≤
    1000 * (ρ ^ 2 * J ^ 2 * q ^ 3 * ηv⁻¹ + ρ ^ 2 * Γ ^ 2 * Φ * q ^ 2 * ηv⁻¹ +
      (Wr ^ 2 * Lr ^ 2) ^ 2 * δ * (J + Γ)) := by
  have hMv0 : 0 < Mv := by linarith
  have hq0 : 0 < q := hq ▸ inv_pos.2 hMv0
  have hq1 : q ≤ 1 := hq ▸ inv_le_one_of_one_le₀ hMv1
  have hqM : q * Mv = 1 := hq ▸ inv_mul_cancel₀ hMv0.ne'
  have hWr0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hLr0 : 0 < Lr := by linarith
  have hX0 : 0 < Wr ^ 2 * ℓ ^ 2 := by positivity
  have hXq : Wr ^ 2 * ℓ ^ 2 * q = ηv⁻¹ := by
    have h1 : Wr ^ 2 * ℓ ^ 2 * q * ηv = 1 := by
      calc Wr ^ 2 * ℓ ^ 2 * q * ηv = q * (Wr ^ 2 * ℓ ^ 2 * ηv) := by ring
        _ = q * Mv := by rw [← hMeq]
        _ = 1 := hqM
    exact (eq_inv_of_mul_eq_one_left h1)
  have hs : 1 ≤ ℓ * ρ := by
    have := mul_le_mul hℓ hρ zero_le_one hℓ0.le
    linarith
  have hsq : (2 * (ℓ * ρ) + 1) ^ 2 ≤ 9 * (ℓ ^ 2 * ρ ^ 2) := by
    have h1 : (2 * (ℓ * ρ) + 1) ^ 2 ≤ 9 * (ℓ * ρ) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 5 * (ℓ * ρ) + 1) (by linarith : (0:ℝ) ≤ ℓ * ρ - 1)]
    rw [mul_pow] at h1
    exact h1
  have hNn1 : 1 ≤ Wr ^ 2 * Lr ^ 2 := by
    have h1 : 1 ≤ Wr ^ 2 := one_le_pow₀ hWr
    have h2 : 1 ≤ Lr ^ 2 := one_le_pow₀ hLr
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hT1 : Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2)) ≤
      9 * (ρ ^ 2 * J ^ 2 * q ^ 3 * ηv⁻¹) := by
    have h0 : 0 ≤ Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2)) := by positivity
    calc Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2))
        = (Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2))) * (2 * (ℓ * ρ) + 1) ^ 2 := by ring
      _ ≤ (Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2))) * (9 * (ℓ ^ 2 * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq h0
      _ = 9 * (ρ ^ 2 * J ^ 2 * q ^ 3 * (Wr ^ 2 * ℓ ^ 2 * q)) := by ring
      _ = 9 * (ρ ^ 2 * J ^ 2 * q ^ 3 * ηv⁻¹) := by rw [hXq]
  have hT2 : Wr ^ 2 * (J * q ^ 2 * (Lr ^ 2 * δ)) ≤ (Wr ^ 2 * Lr ^ 2) * δ * J := by
    have h0 : 0 ≤ Wr ^ 2 * (Lr ^ 2 * δ * J) := by positivity
    calc Wr ^ 2 * (J * q ^ 2 * (Lr ^ 2 * δ)) = q ^ 2 * (Wr ^ 2 * (Lr ^ 2 * δ * J)) := by ring
      _ ≤ 1 * (Wr ^ 2 * (Lr ^ 2 * δ * J)) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hq0.le hq1) h0
      _ = (Wr ^ 2 * Lr ^ 2) * δ * J := by ring
  have hT3 : Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2))) ≤
      18 * (ρ ^ 2 * Γ ^ 2 * Φ * q ^ 2 * ηv⁻¹) := by
    have h0 : 0 ≤ Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2))) := by positivity
    calc Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2)))
        = (Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2)))) * (2 * (ℓ * ρ) + 1) ^ 2 := by ring
      _ ≤ (Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2)))) * (9 * (ℓ ^ 2 * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq h0
      _ = 18 * (ρ ^ 2 * Γ ^ 2 * Φ * q ^ 2 * (Wr ^ 2 * ℓ ^ 2 * q)) := by ring
      _ = 18 * (ρ ^ 2 * Γ ^ 2 * Φ * q ^ 2 * ηv⁻¹) := by rw [hXq]
  have hT4 : Wr ^ 2 * (2 * (Γ * q * (Lr ^ 2 * δ))) ≤ 2 * ((Wr ^ 2 * Lr ^ 2) * δ * Γ) := by
    have h0 : 0 ≤ Wr ^ 2 * (2 * (Lr ^ 2 * δ * Γ)) := by positivity
    calc Wr ^ 2 * (2 * (Γ * q * (Lr ^ 2 * δ))) = q * (Wr ^ 2 * (2 * (Lr ^ 2 * δ * Γ))) := by ring
      _ ≤ 1 * (Wr ^ 2 * (2 * (Lr ^ 2 * δ * Γ))) := mul_le_mul_of_nonneg_right hq1 h0
      _ = 2 * ((Wr ^ 2 * Lr ^ 2) * δ * Γ) := by ring
  have hN2 : (Wr ^ 2 * Lr ^ 2) * δ * (J + 2 * Γ) ≤
      2 * ((Wr ^ 2 * Lr ^ 2) ^ 2 * δ * (J + Γ)) := by
    have hN0 : 0 ≤ Wr ^ 2 * Lr ^ 2 := by positivity
    have h0 : 0 ≤ (Wr ^ 2 * Lr ^ 2) * δ := mul_nonneg hN0 hδ
    have h1 : (Wr ^ 2 * Lr ^ 2) * δ * (J + 2 * Γ) ≤ (Wr ^ 2 * Lr ^ 2) * δ * (2 * (J + Γ)) :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    have h2 : (Wr ^ 2 * Lr ^ 2) * δ ≤ (Wr ^ 2 * Lr ^ 2) * ((Wr ^ 2 * Lr ^ 2) * δ) := by
      have := mul_le_mul_of_nonneg_right hNn1 h0
      linarith
    have h3 : (Wr ^ 2 * Lr ^ 2) * δ * (2 * (J + Γ)) ≤
        (Wr ^ 2 * Lr ^ 2) * ((Wr ^ 2 * Lr ^ 2) * δ) * (2 * (J + Γ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    calc (Wr ^ 2 * Lr ^ 2) * δ * (J + 2 * Γ) ≤ (Wr ^ 2 * Lr ^ 2) * δ * (2 * (J + Γ)) := h1
      _ ≤ (Wr ^ 2 * Lr ^ 2) * ((Wr ^ 2 * Lr ^ 2) * δ) * (2 * (J + Γ)) := h3
      _ = 2 * ((Wr ^ 2 * Lr ^ 2) ^ 2 * δ * (J + Γ)) := by ring
  have hA1 : 0 ≤ ρ ^ 2 * J ^ 2 * q ^ 3 * ηv⁻¹ := by positivity
  have hA2 : 0 ≤ ρ ^ 2 * Γ ^ 2 * Φ * q ^ 2 * ηv⁻¹ := by positivity
  have hA3 : 0 ≤ (Wr ^ 2 * Lr ^ 2) ^ 2 * δ * (J + Γ) := by positivity
  have hsplit : Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2 + Lr ^ 2 * δ)) +
      Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2 + Lr ^ 2 * δ))) =
      Wr ^ 2 * (J * q ^ 2 * (J * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2)) +
        Wr ^ 2 * (J * q ^ 2 * (Lr ^ 2 * δ)) +
      Wr ^ 2 * (2 * (Γ * q * (Γ * Φ * q ^ 2 * (2 * (ℓ * ρ) + 1) ^ 2))) +
        Wr ^ 2 * (2 * (Γ * q * (Lr ^ 2 * δ))) := by ring
  rw [hsplit]
  have hsum : (Wr ^ 2 * Lr ^ 2) * δ * J + 2 * ((Wr ^ 2 * Lr ^ 2) * δ * Γ) =
      (Wr ^ 2 * Lr ^ 2) * δ * (J + 2 * Γ) := by ring
  linarith [hT1, hT2, hT3, hT4, hN2, hA1, hA2, hA3, hsum]

/-! ## 5. The theorem -/

/-- **The `(+,+)` drift bound `ppDriftN`**, the statement `PPDriftN`, with no hypothesis added:
on `GoodSetPPN`
the non-linear drift `𝓔^{LK×LK} + 𝓔^{(G̃)}` of the `(+,+)` two-loop is bounded by `dBoundPPN` in
terms of `J = jPPN`, deterministically.  The proof: only the cut `(k, l') = (1, 2)` of `elklkN` and
the cuts `k = 1, 2` of `egtN` survive at `k = 2`; `S^{(B)}` is stochastic; the `x`-sum is confined
to the window `{|x - a|_L < ℓ_u W^{τ'}}` (at most `(2 ℓ_u W^{τ'} + 1)² ≤ 9 ℓ_u² W^{2τ'}` points of
`Z_L²`) by the decay clause, the rest costs `L² W^{-D'}`; `W² ℓ_u² = M_u/η_u`. -/
theorem ppDriftN : PPDriftN := by
  intro L W _ _ hL E u hE hu0 hu1 hM1 Γ Φ₃ Φ₆ τ' D' hΓ hΦ₃ hΦ₆ hτ' hD' M hM a
  rcases hM with ⟨_hHerm, hG1, hG2, _hG3, hdec⟩
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hMv : 0 < scaleM L W E u := by linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hL1 hu0 hu1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hρ1 : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'.le
  have hδ0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (by linarith) _
  have hJ0 : 0 ≤ jPPN L W E u M := jPPN_nonneg E u M
  have hr1 : 1 ≤ ellT L u * (W : ℝ) ^ τ' := by
    have := mul_le_mul hℓ1 hρ1 zero_le_one (by linarith)
    linarith
  have hr0 : 0 ≤ ellT L u * (W : ℝ) ^ τ' := by linarith
  have hBJ0 : 0 ≤ jPPN L W E u M * (scaleM L W E u)⁻¹ ^ 2 := by positivity
  have hBA0 : 0 ≤ Γ * (scaleM L W E u)⁻¹ := by
    have : 0 ≤ Γ := by linarith
    positivity
  have hBh : ∀ x y z : Z2 L, ‖LLf L W E u M ⟨[true, true, true], [x, y, z]⟩‖ ≤
      Γ * Φ₃ * (scaleM L W E u)⁻¹ ^ 2 := fun x y z => PPD_loop3_le hMv hG2 x y z
  -- the `LK × LK` term
  have hE1 : ‖elklkN L W E u M (loopOf sigPPN a)‖ ≤ (W : ℝ) ^ 2 *
      (jPPN L W E u M * (scaleM L W E u)⁻¹ ^ 2 *
        (jPPN L W E u M * (scaleM L W E u)⁻¹ ^ 2 * (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 +
          (L : ℝ) ^ 2 * (W : ℝ) ^ (-D'))) := by
    rw [PPD_elklk_eq, norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact PPD_core_sum hL (p := a 1) hr0 hδ0 hBJ0
      (f := fun x => LKf L W E u M ⟨[true, true], [x, a 1]⟩)
      (g := fun y => LKf L W E u M ⟨[true, true], [a 0, y]⟩)
      (fun x => PPD_lk2_le hMv x (a 1)) (fun x hx => PPD_dec_lk2 hdec x (a 1) hx)
      (fun y => PPD_lk2_le hMv (a 0) y)
  -- the `G̃` term
  have hE2 : ‖egtN L W E u M (loopOf sigPPN a)‖ ≤ (W : ℝ) ^ 2 * (2 *
      (Γ * (scaleM L W E u)⁻¹ * (Γ * Φ₃ * (scaleM L W E u)⁻¹ ^ 2 *
        (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D')))) := by
    rw [PPD_egt_eq, norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : ‖∑ x : Z2 L, ∑ y : Z2 L, avgErr L W E u M true x * SB L x y *
        LLf L W E u M ⟨[true, true, true], [y, a 0, a 1]⟩‖ ≤
        Γ * (scaleM L W E u)⁻¹ * (Γ * Φ₃ * (scaleM L W E u)⁻¹ ^ 2 *
          (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D')) := by
      rw [PPD_sum_swap (f := fun y => LLf L W E u M ⟨[true, true, true], [y, a 0, a 1]⟩)
        (g := fun x => avgErr L W E u M true x)]
      refine PPD_core_sum hL (p := a 0) hr0 hδ0 hBA0
        (f := fun y => LLf L W E u M ⟨[true, true, true], [y, a 0, a 1]⟩)
        (g := fun x => avgErr L W E u M true x)
        (fun y => hBh y (a 0) (a 1)) (fun y hy => ?_) (fun x => PPD_avgErr_le hMv hG1 x)
      refine PPD_dec_loop3 hdec y (a 0) (a 1) (hy.trans ?_)
      exact Nat.cast_le.2 (PPD_le_maxDist (![y, a 0, a 1] : Fin 3 → Z2 L) 1 0)
    have h2 : ‖∑ x : Z2 L, ∑ y : Z2 L, avgErr L W E u M true x * SB L x y *
        LLf L W E u M ⟨[true, true, true], [a 0, y, a 1]⟩‖ ≤
        Γ * (scaleM L W E u)⁻¹ * (Γ * Φ₃ * (scaleM L W E u)⁻¹ ^ 2 *
          (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D')) := by
      rw [PPD_sum_swap (f := fun y => LLf L W E u M ⟨[true, true, true], [a 0, y, a 1]⟩)
        (g := fun x => avgErr L W E u M true x)]
      refine PPD_core_sum hL (p := a 0) hr0 hδ0 hBA0
        (f := fun y => LLf L W E u M ⟨[true, true, true], [a 0, y, a 1]⟩)
        (g := fun x => avgErr L W E u M true x)
        (fun y => hBh (a 0) y (a 1)) (fun y hy => ?_) (fun x => PPD_avgErr_le hMv hG1 x)
      refine PPD_dec_loop3 hdec (a 0) y (a 1) (hy.trans ?_)
      exact Nat.cast_le.2 (PPD_le_maxDist (![a 0, y, a 1] : Fin 3 → Z2 L) 0 1)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  -- the assembly
  have hN : nPPN L W = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    unfold nPPN; push_cast; ring
  have hρ2 : (W : ℝ) ^ (2 * τ') = ((W : ℝ) ^ τ') ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by linarith), Real.rpow_two]
  calc ‖elklkN L W E u M (loopOf sigPPN a) + egtN L W E u M (loopOf sigPPN a)‖
      ≤ ‖elklkN L W E u M (loopOf sigPPN a)‖ + ‖egtN L W E u M (loopOf sigPPN a)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add hE1 hE2
    _ ≤ dBoundPPN L W E u Γ Φ₃ τ' D' (jPPN L W E u M) := by
        unfold dBoundPPN
        rw [hN, hρ2]
        exact PPD_arith hW1r hℓ1 hρ1 hη hM1 rfl rfl hL1r hδ0 hJ0 (by linarith) hΦ₃

end RBM.Ind

end
