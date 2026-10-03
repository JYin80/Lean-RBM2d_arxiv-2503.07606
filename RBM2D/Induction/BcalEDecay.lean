/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Induction.Split
import RBM2D.Loop.LatticeCount
import RBM2D.Hierarchy.LoopHierarchyCutBlockSumBound

/-!
# Decay through cuts, and conjunct (v) of `BcalEPT`

Paper: arXiv:2503.07606, Section 5: `Def_decay`, `lem_decayLoop`, `lem_BcalE` and its last
sentence.  Namespace `RBM.Ind`.

## Part 1: decay through cuts (deterministic)

* `LoopDecay L N R δ F`: `‖F J‖ ≤ δ` for every well-formed loop `J` of length `≤ N` with two
  labels at `zdist2`-distance `≥ R`; `LoopDecay.mono`, `LoopDecay.sub`.
* Anchors: `mem_cutGlueL`, `mem_cutGlueR`, `mem_cutGlue`, `mem_cutGlue_of_mem`,
  `exists_anchor_cutGlueL`, `exists_anchor_cutGlueR`, `mem_cutGlueL_or_mem_cutGlueR`.
* `far_cutGlueL_or_far_cutGlueR`: if `2R + 1 ≤ |x - y|_L` for two labels of `I` and
  `|α - β|_L ≤ 1`, one of the pieces `I.cutGlueL k l α`, `I.cutGlueR k l β` has two labels at
  distance `≥ R`.
* `norm_sum_SB_le_left`, `norm_sum_SB_le_right`: the window sums
  `‖Σ_{a,b} S^{(B)}_{ab} F_{ab}‖ ≤ (2R+1)² M + L² δ` (five-point stencil, window `(2R+1)²`).
* `glueTerm`, `sum_norm_glue_le_of_far`, `norm_glueTerm_le_of_far`: one cut of a far loop is
  `≤ L² (δ_F M_G + M_F δ_G)`.
* `mem_eeLoop_left`, `mem_eeLoop_right`, `eeLoop_WF`, `length_eeLoop`: the `(2n+2)`-loop of
  `𝓔⊗𝓔` keeps every label of `a` and of `a'`.

## Part 2: `bcalE_labelDecay`

Conjunct (v) of `BcalEPT` from its seven hypotheses.  Per time `u` and size `n`, on the event that
every loop of length `≤ 2k+2` with spread `≥ ℓ_u W^{τ'/2}` has `|𝓛| + |𝓛 - 𝒦| ≤ N^{τ_d} W^{-D''}`
(`DecayLoopPT`, union bound over `≤ (2k+2) N^{4k+4}` loops), every term of the four non-linear
terms has a far factor (`far_cutGlueL_or_far_cutGlueR`, `mem_cutGlue_of_mem`, `mem_eeLoop_left`,
`mem_eeLoop_right`)
bounded by `N^{τ_d} W^{-D''}` (`DecayLoopPT` or `KcalDecay`), and the other factor is
`≤ 2 N^{2k+2}` (`norm_gloop_le_opNorm`, `KboundConcl`, `η_u^{-1} ≤ N` from `RangeCond`).
`D'' = D' + (2k+4)/c`.  Unused hypotheses: `GbEXPHypV3`, `Step2LocalPT`, `Step2DecayPT`.

The decay-through-cuts lemmas parallel the one-dimensional formalization, with the `d = 2` changes:
`Z2 L`, `zdist2`, `Σ_{a,b} |S_{ab}| = L²`, window `(2R+1)²` (`card_ball_le`), separate `δ_F`,
`δ_G`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Decay of loop functions (`Def_decay`) -/

section Def

variable (L : ℕ) [NeZero L]

/-- `F` has `(R, δ)` decay on loops of length `≤ N`: `‖F J‖ ≤ δ` as soon as two labels of the
well-formed loop `J` are at `zdist2`-distance `≥ R`. -/
def LoopDecay (N : ℕ) (R δ : ℝ) (F : LoopIdx (Z2 L) → ℂ) : Prop :=
  ∀ J : LoopIdx (Z2 L), J.WF → J.length ≤ N → ∀ x ∈ J.a, ∀ y ∈ J.a,
    R ≤ (zdist2 L (x - y) : ℝ) → ‖F J‖ ≤ δ

theorem LoopDecay.mono {N N' : ℕ} {R R' δ δ' : ℝ} {F : LoopIdx (Z2 L) → ℂ}
    (h : LoopDecay L N R δ F) (hN : N' ≤ N) (hR : R ≤ R') (hδ : δ ≤ δ') :
    LoopDecay L N' R' δ' F :=
  fun J hJ hJN x hx y hy hxy => (h J hJ (hJN.trans hN) x hx y hy (hR.trans hxy)).trans hδ

end Def

/-! ## 2. Anchors: labels that survive cutting and gluing -/

section Anchor

variable {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}

theorem mem_cutGlueL (k l : ℕ) : b ∈ (x.cutGlueL k l b).a := by
  simp [LoopIdx.cutGlueL]

theorem mem_cutGlueR (k l : ℕ) : b ∈ (x.cutGlueR k l b).a := by
  simp [LoopIdx.cutGlueR]

theorem mem_cutGlue (k : ℕ) : b ∈ (x.cutGlue k b).a := by
  simp [LoopIdx.cutGlue]

/-- Every label of the loop survives `cutGlue` (the new label is only inserted). -/
theorem mem_cutGlue_of_mem (k : ℕ) {c : α} (hc : c ∈ x.a) : c ∈ (x.cutGlue k b).a := by
  simp only [LoopIdx.cutGlue, List.mem_append, List.mem_cons]
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append] at hc
  tauto

/-- The left loop of the cut `(k, l)` keeps the label `a_l`, whatever the glued label is. -/
theorem exists_anchor_cutGlueL (hl1 : 1 ≤ l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueL k l b).a := by
  have h : 0 < (x.a.drop (l - 1)).length := by
    simp only [List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨(x.a.drop (l - 1))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueL, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (List.getElem_mem h))

/-- The right loop of the cut `(k, l)` keeps the label `a_k`. -/
theorem exists_anchor_cutGlueR (hk1 : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueR k l b).a := by
  have h : 0 < ((x.a.drop (k - 1)).take (l - k)).length := by
    simp only [List.length_take, List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨((x.a.drop (k - 1)).take (l - k))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueR, List.mem_append]
  exact Or.inl (List.getElem_mem h)

/-- Every label of the loop goes to the left or to the right loop of the cut `(k, l)`. -/
theorem mem_cutGlueL_or_mem_cutGlueR (hk : 1 ≤ k) (hkl : k < l) {c : α} (hc : c ∈ x.a) :
    (∀ b, c ∈ (x.cutGlueL k l b).a) ∨ (∀ b, c ∈ (x.cutGlueR k l b).a) := by
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append,
    ← List.take_append_drop (l - k) (x.a.drop (k - 1)), List.mem_append, List.drop_drop] at hc
  have e : k - 1 + (l - k) = l - 1 := by omega
  rw [e] at hc
  rcases hc with h | h | h
  · left; intro b; simp [LoopIdx.cutGlueL, h]
  · right; intro b; simp [LoopIdx.cutGlueR, h]
  · left; intro b; simp [LoopIdx.cutGlueL, h]

/-- The left piece is not longer than the loop. -/
theorem BcalEDecay_length_cutGlueL_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueL x b hk hkl hl]; omega

/-- The right piece is not longer than the loop. -/
theorem BcalEDecay_length_cutGlueR_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]; omega

end Anchor

/-! ## 3. The cut spread "up to one block" -/

section Spread

variable {L : ℕ} [NeZero L]

private theorem bcalEDecay_zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

/-- `|-u|_L = |u|_L` on `Z2 L`. -/
private theorem bcalEDecay_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, bcalEDecay_zdist_neg]

private theorem bcalEDecay_zdist2_sub_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← bcalEDecay_zdist2_neg, neg_sub]

/-- **Far labels of a cut loop**: if two labels of
`I` are at distance `≥ 2R + 1` and `|α - β|_L ≤ 1`, then the left piece `I.cutGlueL k l α` or the
right piece `I.cutGlueR k l β` has two labels at distance `≥ R`. -/
theorem far_cutGlueL_or_far_cutGlueR (I : LoopIdx (Z2 L)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    {R : ℝ} {x y : Z2 L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdist2 L (x - y) : ℝ)) {α β : Z2 L} (hab : zdist2 L (α - β) ≤ 1) :
    (∃ x' ∈ (I.cutGlueL k l α).a, ∃ y' ∈ (I.cutGlueL k l α).a, R ≤ (zdist2 L (x' - y') : ℝ)) ∨
      (∃ x' ∈ (I.cutGlueR k l β).a, ∃ y' ∈ (I.cutGlueR k l β).a,
        R ≤ (zdist2 L (x' - y') : ℝ)) := by
  have hR : R ≤ (zdist2 L (x - y) : ℝ) := by
    have h0 : (0 : ℝ) ≤ (zdist2 L (x - y) : ℝ) := Nat.cast_nonneg _
    rcases le_or_gt R 0 with h | h
    · linarith
    · linarith
  have hR' : R ≤ (zdist2 L (y - x) : ℝ) := by rwa [bcalEDecay_zdist2_sub_comm]
  -- the triangle inequality through the glued labels
  have key : ∀ x y : Z2 L, 2 * R + 1 ≤ (zdist2 L (x - y) : ℝ) →
      R ≤ (zdist2 L (x - α) : ℝ) ∨ R ≤ (zdist2 L (β - y) : ℝ) := by
    intro x y hxy
    by_contra hcon
    push Not at hcon
    have t1 := zdist2_add_le L (x - α) (α - β)
    have t2 := zdist2_add_le L (x - α + (α - β)) (β - y)
    have e : x - α + (α - β) + (β - y) = x - y := by abel
    rw [e] at t2
    have : (zdist2 L (x - y) : ℝ) ≤ zdist2 L (x - α) + zdist2 L (α - β) + zdist2 L (β - y) := by
      exact_mod_cast t2.trans (Nat.add_le_add_right t1 _)
    have hab' : (zdist2 L (α - β) : ℝ) ≤ 1 := by exact_mod_cast hab
    linarith
  rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hx with hxL | hxR <;>
    rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hy with hyL | hyR
  · exact Or.inl ⟨x, hxL α, y, hyL α, hR⟩
  · rcases key x y hxy with h | h
    · exact Or.inl ⟨x, hxL α, α, mem_cutGlueL I α k l, h⟩
    · exact Or.inr ⟨β, mem_cutGlueR I β k l, y, hyR β, h⟩
  · have hyx : 2 * R + 1 ≤ (zdist2 L (y - x) : ℝ) := by rwa [bcalEDecay_zdist2_sub_comm]
    rcases key y x hyx with h | h
    · exact Or.inl ⟨y, hyL α, α, mem_cutGlueL I α k l, h⟩
    · exact Or.inr ⟨β, mem_cutGlueR I β k l, x, hxR β, h⟩
  · exact Or.inr ⟨x, hxR β, y, hyR β, hR⟩

end Spread

/-! ## 4. The window sums (five-point stencil, windows `(2R+1)²`) -/

section Window

variable (L : ℕ) [NeZero L]

/-- `Σ_b |S^{(B)}_{ab}| = 1`. -/
private theorem bcalEDecay_row (hL : 3 ≤ L) (a : Z2 L) : ∑ b : Z2 L, ‖SB L a b‖ = 1 :=
  RBM.Gauss.sum_norm_SB_row L hL a

/-- `Σ_{a,b} |S^{(B)}_{ab}| = L²`. -/
theorem BcalEDecay_sum_sum_norm_SB (hL : 3 ≤ L) : ∑ a : Z2 L, ∑ b : Z2 L, ‖SB L a b‖ = (L : ℝ) ^ 2 := by
  simp only [bcalEDecay_row L hL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp [Fintype.card_prod, ZMod.card, sq]

/-- **The window sum `norm_sum_SB_le_left`**: if `‖F_{ab}‖ ≤ M`, and `‖F_{ab}‖ ≤ δ`
once `a` is at distance `≥ R` from an anchor `c`, then
`‖Σ_{a,b} S^{(B)}_{ab} F_{ab}‖ ≤ (2R+1)² M + L² δ`. -/
theorem norm_sum_SB_le_left (hL : 3 ≤ L) {R M δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (c : Z2 L)
    (F : Z2 L → Z2 L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, R ≤ (zdist2 L (a - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : Z2 L, ∑ b : Z2 L, SB L a b * F a b‖ ≤ (2 * R + 1) ^ 2 * M + (L : ℝ) ^ 2 * δ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF 0 0)
  set win : Z2 L → ℝ := fun a => if (zdist2 L (c - a) : ℝ) ≤ R then 1 else 0 with hwin
  have hrow : ∀ a, ∑ b : Z2 L, ‖SB L a b * F a b‖ ≤ win a * M + δ := by
    intro a
    by_cases h : (zdist2 L (a - c) : ℝ) < R
    · have hw : win a = 1 := by
        simp [hwin, bcalEDecay_zdist2_sub_comm c a, h.le]
      calc ∑ b : Z2 L, ‖SB L a b * F a b‖ ≤ ∑ b : Z2 L, ‖SB L a b‖ * M :=
            Finset.sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hF a b) (norm_nonneg _)
        _ = M := by rw [← Finset.sum_mul, bcalEDecay_row L hL, one_mul]
        _ ≤ win a * M + δ := by rw [hw]; linarith
    · push Not at h
      calc ∑ b : Z2 L, ‖SB L a b * F a b‖ ≤ ∑ b : Z2 L, ‖SB L a b‖ * δ :=
            Finset.sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hFd a b h) (norm_nonneg _)
        _ = δ := by rw [← Finset.sum_mul, bcalEDecay_row L hL, one_mul]
        _ ≤ win a * M + δ := by
          have : 0 ≤ win a := by simp only [hwin]; split_ifs <;> norm_num
          nlinarith
  have hcount : ∑ a : Z2 L, win a ≤ (2 * R + 1) ^ 2 := by
    have e : ∑ a : Z2 L, win a =
        (((Finset.univ.filter fun u : Z2 L => (zdist2 L (c - u) : ℝ) ≤ R).card : ℕ) : ℝ) := by
      simp only [hwin]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [e]
    exact RBM.KLoop.card_ball_le L c R hR
  calc ‖∑ a : Z2 L, ∑ b : Z2 L, SB L a b * F a b‖
      ≤ ∑ a : Z2 L, ∑ b : Z2 L, ‖SB L a b * F a b‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : Z2 L, (win a * M + δ) := Finset.sum_le_sum fun a _ => hrow a
    _ = (∑ a : Z2 L, win a) * M + (L : ℝ) ^ 2 * δ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        simp [Fintype.card_prod, ZMod.card, sq]
    _ ≤ (2 * R + 1) ^ 2 * M + (L : ℝ) ^ 2 * δ := by gcongr

/-- **T1.3**, decay in the second variable (by the symmetry of `S^{(B)}`). -/
theorem norm_sum_SB_le_right (hL : 3 ≤ L) {R M δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (c : Z2 L)
    (F : Z2 L → Z2 L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, R ≤ (zdist2 L (b - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : Z2 L, ∑ b : Z2 L, SB L a b * F a b‖ ≤ (2 * R + 1) ^ 2 * M + (L : ℝ) ^ 2 * δ := by
  have e : ∑ a : Z2 L, ∑ b : Z2 L, SB L a b * F a b
      = ∑ b : Z2 L, ∑ a : Z2 L, SB L b a * F a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [show SB L a b = SB L b a from congrFun (congrFun (SB_transpose L) b) a]
  rw [e]
  exact norm_sum_SB_le_left L hL hR hδ c (fun b a => F a b) (fun b a => hF a b)
    (fun b a h => hFd a b h)

end Window

/-! ## 5. One cut of a far loop -/

section Glue

variable (L : ℕ) [NeZero L]

/-- **A far cut, pointwise** (two decay levels): on the
support `|a - b|_L ≤ 1` of `S^{(B)}`, one factor of a cut of a far loop is small. -/
theorem norm_mul_le_of_far_aux {F G : LoopIdx (Z2 L) → ℂ} {I : LoopIdx (Z2 L)} (hI : I.WF)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay L I.length R δF F) (hGd : LoopDecay L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Z2 L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : 2 * R + 1 ≤ (zdist2 L (x - y) : ℝ))
    {a b : Z2 L} (hab : zdist2 L (a - b) ≤ 1) :
    ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG + MF * δG := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF a)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG b)
  rcases far_cutGlueL_or_far_cutGlueR I hk hkl hx hy hxy hab with
    ⟨x', hx', y', hy', h⟩ | ⟨x', hx', y', hy', h⟩
  · have h1 := hFd _ (hI.cutGlueL a hk hkl hl) (BcalEDecay_length_cutGlueL_le I a hk hkl hl) x' hx' y' hy' h
    have h2 := hG b
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG :=
      mul_le_mul h1 h2 (norm_nonneg _) hδF
    nlinarith [mul_nonneg hMF hδG]
  · have h1 := hGd _ (hI.cutGlueR b hk hkl hl) (BcalEDecay_length_cutGlueR_le I b hk hkl hl) x' hx' y' hy' h
    have h2 := hF a
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ MF * δG :=
      mul_le_mul h2 h1 (norm_nonneg _) hMF
    nlinarith [mul_nonneg hδF hMG]

/-- **T1.4, summed norms**: `Σ_{a,b} ‖F(L_a)‖ ‖S_{ab}‖ ‖G(R_b)‖ ≤ L² (δ_F M_G + M_F δ_G)` for a
cut of a loop with two labels at distance `≥ 2R + 1`. -/
theorem sum_norm_glue_le_of_far (hL : 3 ≤ L) {F G : LoopIdx (Z2 L) → ℂ} {I : LoopIdx (Z2 L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay L I.length R δF F) (hGd : LoopDecay L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Z2 L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : 2 * R + 1 ≤ (zdist2 L (x - y) : ℝ)) :
    ∑ a : Z2 L, ∑ b : Z2 L, ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖ ≤
      (L : ℝ) ^ 2 * (δF * MG + MF * δG) := by
  calc ∑ a : Z2 L, ∑ b : Z2 L, ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖
      ≤ ∑ a : Z2 L, ∑ b : Z2 L, ‖SB L a b‖ * (δF * MG + MF * δG) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        by_cases hab : zdist2 L (a - b) ≤ 1
        · have := norm_mul_le_of_far_aux L hI hk hkl hl hδF hδG hFd hGd hF hG hx hy hxy hab
          calc ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖
              = ‖SB L a b‖ * (‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖) := by ring
            _ ≤ ‖SB L a b‖ * (δF * MG + MF * δG) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
        · rw [SB_apply_eq_zero L hL (by omega)]; simp
    _ = (L : ℝ) ^ 2 * (δF * MG + MF * δG) := by
        simp only [← Finset.sum_mul, BcalEDecay_sum_sum_norm_SB L hL]

end Glue

/-! ## 6. The `(2n+2)`-loop of `𝓔⊗𝓔` keeps every label -/

section EE

variable {L : ℕ} [NeZero L]

theorem length_eeLoop (σ : List Bool) (a a' : List (Z2 L)) {k : ℕ} (hk : k ≤ a.length + 1)
    (ha' : a'.length = a.length) (b b' : Z2 L) :
    (eeLoop L σ a a' k b b').length = 2 * a.length + 2 := by
  simp only [eeLoop, LoopIdx.length, List.length_append, List.length_drop, List.length_take,
    List.length_reverse, List.length_singleton, ha']
  omega

theorem eeLoop_WF (σ : List Bool) (a a' : List (Z2 L)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ a.length)
    (hσ : σ.length = a.length) (ha' : a'.length = a.length) (b b' : Z2 L) :
    (eeLoop L σ a a' k b b').WF := by
  simp only [eeLoop, LoopIdx.WF, List.length_append, List.length_drop, List.length_take,
    List.length_reverse, List.length_map, List.length_singleton, hσ, ha']
  omega

theorem mem_eeLoop_left (σ : List Bool) (a a' : List (Z2 L)) (k : ℕ) (b b' : Z2 L) {c : Z2 L}
    (hc : c ∈ a) : c ∈ (eeLoop L σ a a' k b b').a := by
  rw [← List.take_append_drop (k - 1) a, List.mem_append] at hc
  simp only [eeLoop, List.mem_append, List.mem_reverse, List.mem_singleton]
  tauto

theorem mem_eeLoop_right (σ : List Bool) (a a' : List (Z2 L)) (k : ℕ) (b b' : Z2 L) {c : Z2 L}
    (hc : c ∈ a') : c ∈ (eeLoop L σ a a' k b b').a := by
  rw [← List.take_append_drop (k - 1) a', List.mem_append] at hc
  simp only [eeLoop, List.mem_append, List.mem_reverse, List.mem_singleton]
  tauto

end EE

/-! ## 7. Deterministic bounds on the four terms of a far loop -/

section Det

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem bcalEDecay_loopOf_eq (J : LoopIdx (Z2 L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` to `LoopDecay`. -/
private theorem bcalEDecay_loopDecay_of (F : LoopIdx (Z2 L) → ℂ) {K : ℕ} {R δ : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L),
      R ≤ (KLoop.maxDist L a : ℝ) → ‖F (loopOf σ a)‖ ≤ δ) :
    LoopDecay L K R δ F := by
  intro J hJ hJK x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at hJK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1]) (by
      refine le_trans hxy ?_
      exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
        zdist2 L (J.a[q.1.1] - J.a[q.2.1]))
        (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length))))
  rwa [bcalEDecay_loopOf_eq J hJ] at this

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` to all well-formed loops. -/
private theorem bcalEDecay_bound_of (F : LoopIdx (Z2 L) → ℂ) {K : ℕ} {B : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L), ‖F (loopOf σ a)‖ ≤ B)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hK : J.length ≤ K) : ‖F J‖ ≤ B := by
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at h1 hK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1])
  rwa [bcalEDecay_loopOf_eq J hJ] at this

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = (𝓛 - 𝒦)_{u,(σ),(a)}`. -/
private theorem bcalEDecay_avgErr_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool)
    (a : Z2 L) : avgErr L W E u M s a = LKf L W E u M ⟨[s], [a]⟩ := by
  unfold LKf LLf avgErr
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]

private theorem bcalEDecay_norm_ite_le (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

/-- `Σ_{1 ≤ k < l ≤ n} f(k, l) ≤ n² T`. -/
private theorem bcalEDecay_sum_pairs (n : ℕ) (f : ℕ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ k ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Ioc k n, f k l ≤ T) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l ≤ (n : ℝ) ^ 2 * T := by
  calc ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l
      ≤ ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, T :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hf k hk l hl
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (n : ℝ) * T := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le n k
    _ = (n : ℝ) ^ 2 * T := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

private theorem bcalEDecay_length_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).length = n := by
  simp [loopOf, LoopIdx.length]

private theorem bcalEDecay_WF_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem bcalEDecay_mem_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) (i : Fin n) :
    a i ∈ (loopOf σ a).a := by
  simp only [loopOf]
  exact List.mem_ofFn.2 ⟨i, rfl⟩

/-- One cut of a far loop, both orientations of `[𝒦 ∼ (𝓛 - 𝒦)]` (or `(𝓛-𝒦) × (𝓛-𝒦)`). -/
private theorem bcalEDecay_cut (hL : 3 ≤ L) {F G : LoopIdx (Z2 L) → ℂ} {n : ℕ} {R δ B : ℝ}
    (hδ : 0 ≤ δ)
    (hFb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n → ‖F J‖ ≤ B)
    (hGb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n → ‖G J‖ ≤ B)
    (hFd : LoopDecay L n R δ F) (hGd : LoopDecay L n R δ G)
    (σ : Fin n → Bool) (a : Fin n → Z2 L) {i j : Fin n}
    (hfar : 2 * R + 1 ≤ (zdist2 L (a i - a j) : ℝ)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ n) :
    ∑ x : Z2 L, ∑ y : Z2 L, ‖F ((loopOf σ a).cutGlueL k l x)‖ * ‖SB L x y‖ *
        ‖G ((loopOf σ a).cutGlueR k l y)‖ ≤ (L : ℝ) ^ 2 * (δ * B + B * δ) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = n := bcalEDecay_length_loopOf σ a
  have hI : I.WF := bcalEDecay_WF_loopOf σ a
  have hl' : l ≤ I.length := hlen ▸ hl
  refine sum_norm_glue_le_of_far L hL hI hk hkl hl' hδ hδ (LoopDecay.mono L hFd (le_of_eq hlen) le_rfl le_rfl)
    (LoopDecay.mono L hGd (le_of_eq hlen) le_rfl le_rfl) (fun x => ?_) (fun y => ?_)
    (bcalEDecay_mem_loopOf σ a i) (bcalEDecay_mem_loopOf σ a j) hfar
  · refine hFb _ (hI.cutGlueL x hk hkl hl') ?_ ((BcalEDecay_length_cutGlueL_le I x hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueL I x hk hkl hl']; omega
  · refine hGb _ (hI.cutGlueR y hk hkl hl') ?_ ((BcalEDecay_length_cutGlueR_le I y hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueR I y hk hkl hl']; omega

/-- **(v.1), deterministic**: for a loop with two labels at distance `≥ 2R+1`, the three terms
`Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l`, `𝓔^{LK×LK}`, `𝓔^{(G̃)}` are `≤ 7 n³ W² L² δ B`. -/
private theorem bcalEDecay_det_v1 (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    {n : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hLKb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n → ‖LKf L W E u M J‖ ≤ B)
    (hKb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n →
      ‖KLoop.Kcal L W E u J‖ ≤ B)
    (havg : ∀ s a, ‖avgErr L W E u M s a‖ ≤ B)
    (hdLL : LoopDecay L (n + 1) R δ (LLf L W E u M))
    (hdLK : LoopDecay L n R δ (LKf L W E u M))
    (hdK : LoopDecay L n R δ (KLoop.Kcal L W E u))
    (σ : Fin n → Bool) (a : Fin n → Z2 L) {i j : Fin n}
    (hfar : 2 * R + 1 ≤ (zdist2 L (a i - a j) : ℝ)) :
    ‖∑ l ∈ Finset.Icc 3 n, ksimLK L W E u M l (loopOf σ a)‖ +
        ‖elklkN L W E u M (loopOf σ a)‖ + ‖egtN L W E u M (loopOf σ a)‖ ≤
      7 * (n : ℝ) ^ 3 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (δ * B) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (havg true 0)
  set I := loopOf σ a with hIdef
  have hlen : I.length = n := bcalEDecay_length_loopOf σ a
  have hI : I.WF := bcalEDecay_WF_loopOf σ a
  have hn1 : 1 ≤ n := by have := i.2; omega
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hR : R ≤ (zdist2 L (a i - a j) : ℝ) := by
    have h0 : (0 : ℝ) ≤ (zdist2 L (a i - a j) : ℝ) := Nat.cast_nonneg _
    rcases le_or_gt R 0 with h | h <;> linarith
  -- one `ksimLK`
  have hks : ∀ l, ‖ksimLK L W E u M l I‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (4 * (δ * B)))) := by
    intro l
    unfold ksimLK
    rw [norm_mul, hW2, hlen]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
    refine bcalEDecay_sum_pairs n _ (by positivity) fun k hk l' hl' => ?_
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
    have h1 := bcalEDecay_cut hL hδ hLKb hKb hdLK hdK σ a hfar hk.1 hl'.1 hl'.2
    have h2 := bcalEDecay_cut hL hδ hKb hLKb hdK hdLK σ a hfar hk.1 hl'.1 hl'.2
    calc ‖∑ x : Z2 L, ∑ y : Z2 L,
          ((if (I.cutGlueR k l' y).length = l then
              LKf L W E u M (I.cutGlueL k l' x) * SB L x y * KLoop.Kcal L W E u (I.cutGlueR k l' y)
            else 0) +
           (if (I.cutGlueL k l' x).length = l then
              KLoop.Kcal L W E u (I.cutGlueL k l' x) * SB L x y * LKf L W E u M (I.cutGlueR k l' y)
            else 0))‖
        ≤ ∑ x : Z2 L, ∑ y : Z2 L,
            (‖LKf L W E u M (I.cutGlueL k l' x)‖ * ‖SB L x y‖ *
                ‖KLoop.Kcal L W E u (I.cutGlueR k l' y)‖ +
              ‖KLoop.Kcal L W E u (I.cutGlueL k l' x)‖ * ‖SB L x y‖ *
                ‖LKf L W E u M (I.cutGlueR k l' y)‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun y _ => ?_))
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (bcalEDecay_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
          · refine (bcalEDecay_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ (L : ℝ) ^ 2 * (δ * B + B * δ) + (L : ℝ) ^ 2 * (δ * B + B * δ) := by
          simp only [Finset.sum_add_distrib]
          exact add_le_add h1 h2
      _ = (L : ℝ) ^ 2 * (4 * (δ * B)) := by ring
  -- the sum over `l`
  have hksum : ‖∑ l ∈ Finset.Icc 3 n, ksimLK L W E u M l I‖ ≤
      (n : ℝ) * ((W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (4 * (δ * B))))) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun l _ => hks l).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    gcongr
    exact_mod_cast (by omega : n + 1 - 3 ≤ n)
  -- `𝓔^{LK×LK}`
  have hel : ‖elklkN L W E u M I‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (δ * B + B * δ))) := by
    unfold elklkN
    rw [norm_mul, hW2, hlen]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
    refine bcalEDecay_sum_pairs n _ (by positivity) fun k hk l' hl' => ?_
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
    refine le_trans ?_ (bcalEDecay_cut hL hδ hLKb hLKb hdLK hdLK σ a hfar hk.1 hl'.1 hl'.2)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => ?_))
    rw [norm_mul, norm_mul]
  -- `𝓔^{(G̃)}`
  have heg : ‖egtN L W E u M I‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) * ((L : ℝ) ^ 2 * (B * δ))) := by
    unfold egtN
    rw [norm_mul, hW2, hlen]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.Icc 1 n, ‖∑ x : Z2 L, ∑ y : Z2 L,
          avgErr L W E u M (I.σ.getD (k - 1) false) x * SB L x y * LLf L W E u M (I.cutGlue k y)‖
        ≤ ∑ k ∈ Finset.Icc 1 n, ∑ x : Z2 L, ∑ y : Z2 L, ‖SB L x y‖ * (B * δ) := by
          refine Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun y _ => ?_))
          simp only [Finset.mem_Icc] at hk
          have hkI : k ≤ I.length := hlen ▸ hk.2
          have hd : ‖LLf L W E u M (I.cutGlue k y)‖ ≤ δ := by
            refine hdLL _ (hI.cutGlue y hk.1 hkI) ?_ (a i)
              (mem_cutGlue_of_mem I y k (bcalEDecay_mem_loopOf σ a i)) (a j)
              (mem_cutGlue_of_mem I y k (bcalEDecay_mem_loopOf σ a j)) hR
            rw [LoopIdx.length_cutGlue I y hkI, hlen]
          rw [norm_mul, norm_mul]
          calc ‖avgErr L W E u M (I.σ.getD (k - 1) false) x‖ * ‖SB L x y‖ *
                ‖LLf L W E u M (I.cutGlue k y)‖
              = ‖SB L x y‖ * (‖avgErr L W E u M (I.σ.getD (k - 1) false) x‖ *
                  ‖LLf L W E u M (I.cutGlue k y)‖) := by ring
            _ ≤ ‖SB L x y‖ * (B * δ) := mul_le_mul_of_nonneg_left
                (mul_le_mul (havg _ _) hd (norm_nonneg _) hB) (norm_nonneg _)
      _ = (n : ℝ) * ((L : ℝ) ^ 2 * (B * δ)) := by
          simp only [← Finset.sum_mul, BcalEDecay_sum_sum_norm_SB L hL, Finset.sum_const, Nat.card_Icc,
            nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hδB : 0 ≤ δ * B := mul_nonneg hδ hB
  have hWL : 0 ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by positivity
  calc ‖∑ l ∈ Finset.Icc 3 n, ksimLK L W E u M l I‖ + ‖elklkN L W E u M I‖ + ‖egtN L W E u M I‖
      ≤ (n : ℝ) * ((W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (4 * (δ * B))))) +
          (W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (δ * B + B * δ))) +
          (W : ℝ) ^ 2 * ((n : ℝ) * ((L : ℝ) ^ 2 * (B * δ))) := add_le_add (add_le_add hksum hel) heg
    _ = (4 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + n) * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (δ * B) := by ring
    _ ≤ 7 * (n : ℝ) ^ 3 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (δ * B) := by
        have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
        have h1 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
        have : 4 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + n ≤ 7 * (n : ℝ) ^ 3 := by linarith
        have := mul_le_mul_of_nonneg_right this hWL
        exact mul_le_mul_of_nonneg_right this hδB

/-- Every label of `a` and of `a'` is a label of the `(2n+2)`-loop at every cut. -/
private theorem bcalEDecay_mem_eeLoop {n : ℕ} (σ : Fin n → Bool) (a a' : Fin n → Z2 L) (k : ℕ)
    (b b' : Z2 L) (i : Fin (n + n)) :
    Fin.append a a' i ∈ (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    exact mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  · rw [Fin.append_right]
    exact mem_eeLoop_right _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- **(v.2), deterministic**: `‖(𝓔⊗𝓔)_{σ,a,a'}‖ ≤ n W² L² δ` when two labels of `(a, a')` are at
distance `≥ R`. -/
private theorem bcalEDecay_det_v2 (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    {n : ℕ} {R δ : ℝ} (hδ : 0 ≤ δ) (hdLL : LoopDecay L (2 * n + 2) R δ (LLf L W E u M))
    (σ : Fin n → Bool) (a a' : Fin n → Z2 L) {i j : Fin (n + n)}
    (hfar : R ≤ (zdist2 L (Fin.append a a' i - Fin.append a a' j) : ℝ)) :
    ‖eeN L W E u M σ a a'‖ ≤ (n : ℝ) * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * δ := by
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  unfold eeN
  rw [norm_mul, hW2]
  have key : ‖∑ k ∈ Finset.Icc 1 n, ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
      LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      (n : ℝ) * ((L : ℝ) ^ 2 * δ) := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ b : Z2 L, ∑ b' : Z2 L, ‖SB L b b'‖ * δ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b' _ => ?_)))
          simp only [Finset.mem_Icc] at hk
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hdLL _ (eeLoop_WF _ _ _ hk.1 (by simpa using hk.2) (by simp) (by simp) b b') ?_
            _ (bcalEDecay_mem_eeLoop σ a a' k b b' i) _ (bcalEDecay_mem_eeLoop σ a a' k b b' j) hfar
          rw [length_eeLoop _ _ _ (by simp; omega) (by simp) b b']
          simp
      _ = (n : ℝ) * ((L : ℝ) ^ 2 * δ) := by
          simp only [← Finset.sum_mul, BcalEDecay_sum_sum_norm_SB L hL, Finset.sum_const, Nat.card_Icc,
            nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  calc (W : ℝ) ^ 2 * ‖_‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) * ((L : ℝ) ^ 2 * δ)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (n : ℝ) * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * δ := by ring

end Det

/-! ## 8. Numerical and measure-theoretic helpers -/

section Helpers

/-- The union bound over a finite family of finite index sets. -/
private theorem bcalEDecay_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Finset ℕ)
    {I : ℕ → Type*} [∀ m, Fintype (I m)] (A : ∀ m, I m → Set Ω) {ε C : ℝ} (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hcard : ∀ m ∈ T, (Fintype.card (I m) : ℝ) ≤ C)
    (hA : ∀ m ∈ T, ∀ q, P (A m q) ≤ ENNReal.ofReal ε) :
    P (⋃ m ∈ T, ⋃ q, A m q) ≤ ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
  calc P (⋃ m ∈ T, ⋃ q, A m q) ≤ ∑ m ∈ T, P (⋃ q, A m q) := measure_biUnion_finset_le T _
    _ ≤ ∑ m ∈ T, ∑ q, P (A m q) := Finset.sum_le_sum fun m _ => measure_iUnion_fintype_le P _
    _ ≤ ∑ m ∈ T, ∑ _q : I m, ENNReal.ofReal ε :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun q _ => hA m hm q
    _ = ∑ m ∈ T, ENNReal.ofReal ((Fintype.card (I m) : ℝ) * ε) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ m ∈ T, ENNReal.ofReal (C * ε) := Finset.sum_le_sum fun m hm =>
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcard m hm) hε)
    _ = ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc,
          ENNReal.ofReal_mul (p := (T.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The index set of an `m`-loop has at most `N^{2K}` elements for `m ≤ K`, `N ≥ 2`. -/
private theorem bcalEDecay_card_le (d : Sizes) (n m K : ℕ) (hm : m ≤ K) (hN : 2 ≤ d.size n) :
    (Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (2 * K) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) =
      2 ^ m * (d.L n * d.L n) ^ m := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) ≤ d.size n ^ (2 * K) := by
    rw [hcard]
    calc 2 ^ m * (d.L n * d.L n) ^ m ≤ d.size n ^ m * d.size n ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hN m) (Nat.pow_le_pow_left hLL m)
      _ = d.size n ^ (2 * m) := by ring
      _ ≤ d.size n ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  exact_mod_cast hnat

/-- `(2k+2) N^{a} N^{-(D_p + a + 1)} ≤ N^{-D_p}` for `N ≥ 2k+2`. -/
private theorem bcalEDecay_prob_num {N Dp : ℝ} {k a : ℕ} (hN1 : 1 ≤ N)
    (hN : ((2 * k + 2 : ℕ) : ℝ) ≤ N) :
    ((2 * k + 2 : ℕ) : ℝ) * N ^ a * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) ≤ N ^ (-Dp) := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_natCast N a]
  have e : N ^ (a : ℝ) * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) = N ^ (-Dp) * N⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1
    push_cast; ring
  rw [mul_assoc, e]
  have h1 : ((2 * k + 2 : ℕ) : ℝ) * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have h2 : 0 ≤ N ^ (-Dp) := Real.rpow_nonneg hN0.le _
  calc ((2 * k + 2 : ℕ) : ℝ) * (N ^ (-Dp) * N⁻¹) = N ^ (-Dp) * (((2 * k + 2 : ℕ) : ℝ) * N⁻¹) := by
        ring
    _ ≤ N ^ (-Dp) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = N ^ (-Dp) := mul_one _

/-- `W^{-(D' + e/c)} N^e ≤ W^{-D'}` from `N^c ≤ W`. -/
private theorem bcalEDecay_WD {N W c D' e : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (he : 0 ≤ e) (hNW : N ^ c ≤ W) : W ^ (-(D' + e / c)) * N ^ e ≤ W ^ (-D') := by
  have h1 : N ^ e ≤ W ^ (e / c) := by
    calc N ^ e = (N ^ c) ^ (e / c) := by
          rw [← Real.rpow_mul hN]; congr 1; field_simp
      _ ≤ W ^ (e / c) := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hNW (div_nonneg he hc.le)
  have h2 : W ^ (-(D' + e / c)) = W ^ (-D') * (W ^ (e / c))⁻¹ := by
    rw [show -(D' + e / c) = -D' + -(e / c) by ring, Real.rpow_add hW, Real.rpow_neg hW.le (e / c)]
  rw [h2]
  have h3 : 0 < W ^ (e / c) := Real.rpow_pos_of_pos hW _
  have h4 : 0 ≤ W ^ (-D') * (W ^ (e / c))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hW.le _) (inv_nonneg.2 h3.le)
  calc W ^ (-D') * (W ^ (e / c))⁻¹ * N ^ e ≤ W ^ (-D') * (W ^ (e / c))⁻¹ * W ^ (e / c) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = W ^ (-D') := by field_simp

/-- `((1-u) Im m)^{-1} ≤ N` from `N^{-1+τ} ≤ 1-u`, `μ ≤ Im m`, `1 ≤ μ N^τ`. -/
private theorem bcalEDecay_eta_inv {N x μ m τ : ℝ} (hN : 0 < N) (hx : N ^ (-1 + τ) ≤ x)
    (hμ : 0 < μ) (hm : μ ≤ m) (hμN : 1 ≤ μ * N ^ τ) : (x * m)⁻¹ ≤ N := by
  have e : N * N ^ (-1 + τ) = N ^ τ := by
    rw [Real.rpow_add hN, Real.rpow_neg_one]; field_simp
  have hp : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN _
  have hx0 : 0 < x := lt_of_lt_of_le hp hx
  have hxm : 0 < x * m := mul_pos hx0 (lt_of_lt_of_le hμ hm)
  have key : 1 ≤ N * (x * m) := by
    rw [← e] at hμN
    have : μ * (N * N ^ (-1 + τ)) ≤ m * (N * x) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left hx hN.le) (by positivity) (by linarith)
    nlinarith
  calc (x * m)⁻¹ = (x * m)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (x * m)⁻¹ * (N * (x * m)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hxm.le)
    _ = N := by rw [mul_comm N, ← mul_assoc, inv_mul_cancel₀ hxm.ne', one_mul]

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ`. -/
private theorem bcalEDecay_im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hκ : 0 < κ) :
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

/-- The final count of (v.1): `7k³ N (N^{τ_d} W'' · 2N^{2k+2}) ≤ N^{τ_d} W^{-D'}`. -/
private theorem bcalEDecay_num1 {N T W'' W' : ℝ} {k : ℕ} (hN : 14 * (k : ℝ) ^ 3 ≤ N)
    (hN1 : 1 ≤ N) (hT : 0 ≤ T) (hW'' : 0 ≤ W'') (hWD : W'' * N ^ (2 * k + 4) ≤ W') :
    7 * (k : ℝ) ^ 3 * N * (T * W'' * (2 * N ^ (2 * k + 2))) ≤ T * W' := by
  have hP : 0 ≤ N * N ^ (2 * k + 2) := by positivity
  calc 7 * (k : ℝ) ^ 3 * N * (T * W'' * (2 * N ^ (2 * k + 2)))
      = T * (14 * (k : ℝ) ^ 3 * (N * N ^ (2 * k + 2)) * W'') := by ring
    _ ≤ T * (N * (N * N ^ (2 * k + 2)) * W'') := by gcongr
    _ = T * (W'' * N ^ (2 * k + 4)) := by ring
    _ ≤ T * W' := mul_le_mul_of_nonneg_left hWD hT

/-- The final count of (v.2): `k N (N^{τ_d} W'') ≤ N^{τ_d} W^{-D'}`. -/
private theorem bcalEDecay_num2 {N T W'' W' : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ N) (hN1 : 1 ≤ N)
    (hT : 0 ≤ T) (hW'' : 0 ≤ W'') (hWD : W'' * N ^ (2 * k + 4) ≤ W') :
    (k : ℝ) * N * (T * W'') ≤ T * W' := by
  have h1 : (k : ℝ) * N ≤ N ^ (2 * k + 4) := by
    calc (k : ℝ) * N ≤ N * N := mul_le_mul_of_nonneg_right hk (by linarith)
      _ = N ^ 2 := (sq N).symm
      _ ≤ N ^ (2 * k + 4) := pow_le_pow_right₀ hN1 (by omega)
  calc (k : ℝ) * N * (T * W'') = T * (W'' * ((k : ℝ) * N)) := by ring
    _ ≤ T * (W'' * N ^ (2 * k + 4)) := by gcongr
    _ ≤ T * W' := mul_le_mul_of_nonneg_left hWD hT

end Helpers

/-! ## 9. The good event (per size and time) -/

section Core

variable (d : Sizes)

/-- **The good event.**  Eventually in `n`, for every time `u ∈ [s_n, t_n]`: the radius facts, and
an event `S` of probability `≤ N^{-D_p}` off which `𝓛`, `𝓛 - 𝒦` and `𝒦` have
`(ℓ_u W^{τ'/2}, N^{τ_d} W^{-D''})` decay on loops of length `≤ 2k+2` and `𝓛`, `𝒦` are
`≤ N^{2k+2}` there.  `D'' = D' + (2k+4)/c`. -/
private theorem bcalEDecay_core {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hKd : KcalDecay κ) (hDL : DecayLoopPT d E s t) (k : ℕ)
    {τ' D' τd Dp : ℝ} (hτ' : 0 < τ') (hD' : 0 < D') (hτd : 0 < τd) (hDp : 0 < Dp) :
    ∀ᶠ n : ℕ in atTop,
      14 * (k : ℝ) ^ 3 ≤ ((d.size n : ℕ) : ℝ) ∧ 1 ≤ ((d.size n : ℕ) : ℝ) ∧
      (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)) * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4) ≤
        (d.W n : ℝ) ^ (-D') ∧
      ∀ u : TimeIcc s t n,
        2 * (ellT (d.L n) u * (d.W n : ℝ) ^ (τ' / 2)) + 1 ≤ ellT (d.L n) u * (d.W n : ℝ) ^ τ' ∧
        0 ≤ ellT (d.L n) u * (d.W n : ℝ) ^ (τ' / 2) ∧
        ∃ S : Set (Sizes.SeqΩ d), Sizes.seqP d S ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) ∧
          ∀ ω ∉ S,
            LoopDecay (d.L n) (2 * k + 2) (ellT (d.L n) u * (d.W n : ℝ) ^ (τ' / 2))
              (((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)))
              (LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)) ∧
            LoopDecay (d.L n) (2 * k + 2) (ellT (d.L n) u * (d.W n : ℝ) ^ (τ' / 2))
              (((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)))
              (LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)) ∧
            LoopDecay (d.L n) (2 * k + 2) (ellT (d.L n) u * (d.W n : ℝ) ^ (τ' / 2))
              (((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)))
              (KLoop.Kcal (d.L n) (d.W n) (E n) u) ∧
            (∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
              ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) J‖ ≤
                ((d.size n : ℕ) : ℝ) ^ (2 * k + 2)) ∧
            (∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
              ‖KLoop.Kcal (d.L n) (d.W n) (E n) u J‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 2)) := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hN
  obtain ⟨μ, hμ, hμb⟩ := bcalEDecay_im_bounds hE hκ
  set D'' : ℝ := D' + ((2 * k + 4 : ℕ) : ℝ) / c with hD''
  have hD''pos : 0 < D'' := by rw [hD'']; positivity
  set D₁ : ℝ := Dp + ((2 * (2 * k + 2) + 1 : ℕ) : ℝ) with hD₁
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  have hτ'2 : 0 < τ' / 2 := by linarith
  -- eventual facts
  have e3 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hN).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have e4 : ∀ᶠ n : ℕ in atTop,
      max (14 * (k : ℝ) ^ 3) ((2 * k + 2 : ℕ) : ℝ) + 2 ≤ ((d.size n : ℕ) : ℝ) :=
    hN.eventually_ge_atTop _
  have e5 : ∀ᶠ n : ℕ in atTop, 3 ≤ ((d.size n : ℕ) : ℝ) ^ (c * (τ' / 2)) :=
    ((tendsto_rpow_atTop (by positivity)).comp hN).eventually_ge_atTop 3
  have e6 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 (2 * k + 2), ∀ u : TimeIcc s t n,
      ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    filter_upwards [hsize.eventually (hKb m hm1 1 one_pos)] with n hn u σ a
    have hu0 : 0 ≤ (u : ℝ) := le_trans (hs0 n) u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
      u, hu0, hu1⟩, σ, a⟩
    have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (KLoop.Mt (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := h
    rwa [kloop_Mt_eq hu1.le] at h'
  have e7 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 (2 * k + 2),
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = d.size n →
        ((d.size n : ℕ) : ℝ) ^ c ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
        ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L),
          ellT L u * (W : ℝ) ^ (τ' / 2) ≤ (KLoop.maxDist L a : ℝ) →
            ‖KLoop.Kcal L W E u (loopOf σ a)‖ ≤ (W : ℝ) ^ (-D'') := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    exact hsize.eventually (hKd hκ c hc m hm1 (τ' / 2) D'' hτ'2 hD''pos)
  have e8 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 (2 * k + 2),
      ∀ p : TimeIcc s t n × (Fin m → Bool) × (Fin m → Z2 (d.L n)),
        Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 +
            lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2) *
          (if ellT (d.L n) p.1 * (d.W n : ℝ) ^ (τ' / 2) ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ)
            then 1 else 0)} ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    exact hDL m hm1 (τ' / 2) hτ'2 D'' hD''pos τd hτd D₁ hD₁pos
  filter_upwards [hB, hR, e3, e4, e5, e6, e7, e8] with n h1 h2 h3 h4 h5 h6 h7 h8
  -- abbreviations
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Wr : ℝ := (d.W n : ℝ) with hWr
  have hN14 : 14 * (k : ℝ) ^ 3 ≤ N := by
    have := le_max_left (14 * (k : ℝ) ^ 3) ((2 * k + 2 : ℕ) : ℝ); linarith
  have hN2k : ((2 * k + 2 : ℕ) : ℝ) ≤ N := by
    have := le_max_right (14 * (k : ℝ) ^ 3) ((2 * k + 2 : ℕ) : ℝ); linarith
  have hN2 : (2 : ℝ) ≤ N := by
    have := le_max_right (14 * (k : ℝ) ^ 3) ((2 * k + 2 : ℕ) : ℝ)
    have : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ Wr := by rw [hWr]; exact_mod_cast d.W_pos n
  have hW0 : (0 : ℝ) < Wr := by linarith
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  refine ⟨hN14, hN1, ?_, fun u => ?_⟩
  · have := bcalEDecay_WD (D' := D') hN0.le hW0 hc (Nat.cast_nonneg (2 * k + 4)) h1
    rwa [Real.rpow_natCast] at this
  have hu0 : 0 ≤ (u : ℝ) := le_trans (hs0 n) u.2.1
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hℓ : 1 ≤ ellT (d.L n) u := one_le_ellT hL1 hu0 hu1
  have hw3 : 3 ≤ Wr ^ (τ' / 2) := by
    refine h5.trans ?_
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) h1 hτ'2.le
  have hwsq : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hRpos : 0 ≤ ellT (d.L n) u * Wr ^ (τ' / 2) := by positivity
  refine ⟨?_, hRpos, ?_⟩
  · rw [hwsq]
    have hℓw : 3 ≤ ellT (d.L n) u * Wr ^ (τ' / 2) := by nlinarith
    nlinarith
  -- `η_u^{-1} ≤ N`
  have hη : ((1 - (u : ℝ)) * (spectralM (E n)).im)⁻¹ ≤ N :=
    bcalEDecay_eta_inv hN0 (h2.trans (by linarith [u.2.2])) hμ (hμb n).1 h3
  have hη0 : 0 < (1 - (u : ℝ)) * (spectralM (E n)).im :=
    mul_pos (by linarith) (lt_of_lt_of_le hμ (hμb n).1)
  -- the bad event
  set S : Set (Sizes.SeqΩ d) := ⋃ m ∈ Finset.Icc 1 (2 * k + 2),
    ⋃ q : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      {ω | N ^ τd * Wr ^ (-D'') <
        (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
        (if ellT (d.L n) u * Wr ^ (τ' / 2) ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0)}
    with hS
  refine ⟨S, ?_, fun ω hω => ?_⟩
  · have hU := bcalEDecay_union (Sizes.seqP d) (Finset.Icc 1 (2 * k + 2))
      (I := fun m => (Fin m → Bool) × (Fin m → Z2 (d.L n)))
      (fun m q => {ω | N ^ τd * Wr ^ (-D'') <
        (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
        (if ellT (d.L n) u * Wr ^ (τ' / 2) ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0)})
      (ε := N ^ (-D₁)) (C := N ^ (2 * (2 * k + 2))) (Real.rpow_nonneg hN0.le _) (by positivity)
      (fun m hm => bcalEDecay_card_le d n m (2 * k + 2) (Finset.mem_Icc.1 hm).2
        (by have h := hN2; rw [hNdef] at h; exact_mod_cast h))
      (fun m hm q => h8 m hm (u, q.1, q.2))
    refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Nat.card_Icc, Nat.add_sub_cancel, hD₁]
    exact bcalEDecay_prob_num hN1 hN2k
  -- off the bad event
  simp only [hS, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hω
  have hT1 : 1 ≤ N ^ τd := Real.one_le_rpow hN1 hτd.le
  have hWD0 : 0 ≤ Wr ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hgood : ∀ m ∈ Finset.Icc 1 (2 * k + 2), ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ellT (d.L n) u * Wr ^ (τ' / 2) ≤ (KLoop.maxDist (d.L n) a : ℝ) →
      ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ +
        ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤ N ^ τd * Wr ^ (-D'') := by
    intro m hm σ a hfar
    have := hω m hm (σ, a)
    simp only [hfar, ↓reduceIte, mul_one] at this
    exact this
  refine ⟨bcalEDecay_loopDecay_of _ fun m hm σ a hfar => ?_,
    bcalEDecay_loopDecay_of _ fun m hm σ a hfar => ?_,
    bcalEDecay_loopDecay_of _ fun m hm σ a hfar => ?_, fun J hJ hJ1 hJK => ?_,
    bcalEDecay_bound_of _ fun m hm σ a => ?_⟩
  · have := hgood m hm σ a hfar
    linarith [norm_nonneg (LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a))]
  · have := hgood m hm σ a hfar
    linarith [norm_nonneg (LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a))]
  · have := h7 m hm (d.L n) (d.W n) (d.three_le_L n) (Sizes.size_eq d n).symm h1 (E n) (hE n) u
      hu0 hu1 σ a hfar
    calc _ ≤ Wr ^ (-D'') := this
      _ = 1 * Wr ^ (-D'') := (one_mul _).symm
      _ ≤ N ^ τd * Wr ^ (-D'') := mul_le_mul_of_nonneg_right hT1 hWD0
  · -- `‖𝓛_u(J)‖ ≤ η_u^{-|J|} ≤ N^{2k+2}`
    have hH : (blockMat (Sizes.seqHflow d n u ω)).IsHermitian :=
      (Sizes.seqHflow_isHermitian d n u ω).submatrix _
    have hzim : (spectralZ (E n) u).im = (1 - (u : ℝ)) * (spectralM (E n)).im :=
      Gauss.spectralZ_im (E n) u
    have hz : (spectralZ (E n) u).im ≠ 0 := by rw [hzim]; exact hη0.ne'
    have hg := norm_gloop_le_opNorm (W := d.W n) hH hz J hJ hJ1
    have habs : |(spectralZ (E n) u).im|⁻¹ ≤ N := by
      rw [hzim, abs_of_pos hη0]; exact hη
    have hWinv : (Wr⁻¹ ^ 2) ^ (J.a.length - 1) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
    unfold LLf
    calc ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n u ω)) (spectralZ (E n) u) J‖
        ≤ |(spectralZ (E n) u).im|⁻¹ ^ J.a.length * (((d.W n : ℝ))⁻¹ ^ 2) ^ (J.a.length - 1) := hg
      _ ≤ N ^ J.a.length * 1 := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) habs _) hWinv (by positivity)
            (by positivity)
      _ ≤ N ^ (2 * k + 2) := by
          rw [mul_one]; exact pow_le_pow_right₀ hN1 hJK
  · -- `‖𝒦_u(σ,a)‖ ≤ N M_u^{-(m-1)} ≤ N^m`
    have hM : (1 - (u : ℝ)) * (spectralM (E n)).im ≤ scaleM (d.L n) (d.W n) (E n) u := by
      unfold scaleM etaT
      have hWℓ : (1 : ℝ) ≤ Wr ^ 2 * ellT (d.L n) u ^ 2 := by
        have := one_le_pow₀ (n := 2) hW1
        have := one_le_pow₀ (n := 2) hℓ
        nlinarith
      nlinarith
    have hMinv : (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ N := (inv_anti₀ hη0 hM).trans hη
    have hMinv0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := inv_nonneg.2 (hη0.le.trans hM)
    have hm' := Finset.mem_Icc.1 hm
    have h6' := h6 m hm u σ a
    rw [Real.rpow_one] at h6'
    refine h6'.trans ?_
    calc N * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) ≤ N * N ^ (m - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMinv0 hMinv _) hN0.le
      _ = N ^ m := by rw [← pow_succ']; congr 1; omega
      _ ≤ N ^ (2 * k + 2) := pow_le_pow_right₀ hN1 hm'.2

end Core

/-! ## 10. Conjunct (v) of `BcalEPT` -/

section Main

variable (d : Sizes)

/-- **Conjunct (v) of `BcalEPT`** (`lem_BcalE`, last sentence): under the seven
hypotheses of `BcalEPT` (of which `GbEXPHypV3`, `Step2LocalPT`, `Step2DecayPT` are not used), for
every `k ≥ 2`, `τ', D' > 0`, per time over `[s,t]`,
`(‖Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l‖ + ‖𝓔^{LK×LK}‖ + ‖𝓔^{(G̃)}‖) · 1(ℓ_u W^{τ'} ≤ max|a_i - a_j|) ≺ W^{-D'}`
and `‖𝓔⊗𝓔‖ · 1(ℓ_u W^{τ'} ≤ max|(a,a')_i - (a,a')_j|) ≺ W^{-D'}`.  The conclusion is the text of
conjunct (v) of `BcalEPT` (`Induction/HierVocab.lean`). -/
theorem bcalE_labelDecay (κ c τ : ℝ) (E s t : ℕ → ℝ) :
  MainIndHyp d κ c τ E s t → KboundConcl κ → KcalDecay κ →
  RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
  Step2LocalPT d E s t → Step2DecayPT d E s t → DecayLoopPT d E s t →
  ∀ k : ℕ, 2 ≤ k →
    (∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ),
      PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
        (fun n p ω => (‖∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) p.1
            (Sizes.seqHflow d n p.1 ω) l (loopOf p.2.1 p.2.2)‖ +
          ‖elklkN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (loopOf p.2.1 p.2.2)‖ +
          ‖egtN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (loopOf p.2.1 p.2.2)‖) *
          farInd d n p.1 τ' p.2.2)
        (fun n _ _ => (d.W n : ℝ) ^ (-D')) ∧
      PerTimeDomAt (Sizes.seqP d) d.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)) ×
          (Fin k → Z2 (d.L n)))
        (fun n p ω => ‖eeN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2.1
            p.2.2.2‖ * farInd d n p.1 τ' (Fin.append p.2.2.1 p.2.2.2))
        (fun n _ _ => (d.W n : ℝ) ^ (-D'))) := by
  intro hmain hKb hKd _ _ _ hDL k hk τ' hτ' D' hD'
  have hc : 0 < c := hmain.2.2.1
  have hk0 : 0 < k := by omega
  refine ⟨fun τd hτd Dp hDp => ?_, fun τd hτd Dp hDp => ?_⟩
  · filter_upwards [bcalEDecay_core d hmain hKb hKd hDL k hτ' hD' hτd hDp] with n hn p
    obtain ⟨h14, hN1, hWD, hu⟩ := hn
    obtain ⟨h2R, hR0, S, hS, hgood⟩ := hu p.1
    refine le_trans (measure_mono ?_) hS
    intro ω hω
    by_contra hωS
    obtain ⟨hdLL, hdLK, hdK, hbLL, hbK⟩ := hgood ω hωS
    simp only [Set.mem_ofPred_eq] at hω
    refine absurd hω (not_lt.2 ?_)
    have hT0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τd := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hW'0 : 0 ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hW''0 : 0 ≤ (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
      rw [Sizes.size_eq]; push_cast; ring
    unfold farInd
    split_ifs with hf
    · rw [mul_one]
      obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
        ⟨(⟨0, hk0⟩, ⟨0, hk0⟩), Finset.mem_univ _⟩
        (fun q : Fin k × Fin k => zdist2 (d.L n) (p.2.2 q.1 - p.2.2 q.2))
      have hfar : 2 * (ellT (d.L n) p.1 * (d.W n : ℝ) ^ (τ' / 2)) + 1 ≤
          (zdist2 (d.L n) (p.2.2 q.1 - p.2.2 q.2) : ℝ) := by
        refine h2R.trans (hf.trans (le_of_eq ?_))
        unfold KLoop.maxDist
        rw [hq]
      have hB0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 2) := by positivity
      have hLKb : ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
          ‖LKf (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) J‖ ≤
            2 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 2) := fun J hJ h1 hJk => by
        unfold LKf
        have := hbLL J hJ h1 (by omega)
        have := hbK J hJ h1 (by omega)
        exact (norm_sub_le _ _).trans (by linarith)
      have hKb' : ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
          ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 J‖ ≤ 2 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 2) :=
        fun J hJ h1 hJk => (hbK J hJ h1 (by omega)).trans (by linarith)
      have havg : ∀ s' a', ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) s' a'‖ ≤
          2 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 2) := fun s' a' => by
        rw [bcalEDecay_avgErr_eq]
        exact hLKb _ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
          (by simp [LoopIdx.length]; omega)
      have hdet := bcalEDecay_det_v1 (d.three_le_L n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (n := k) (mul_nonneg hT0 hW''0) hLKb hKb' havg
        (LoopDecay.mono _ hdLL (by omega) le_rfl le_rfl)
        (LoopDecay.mono _ hdLK (by omega) le_rfl le_rfl)
        (LoopDecay.mono _ hdK (by omega) le_rfl le_rfl) p.2.1 p.2.2 hfar
      refine hdet.trans ?_
      rw [hWL]
      exact bcalEDecay_num1 h14 hN1 hT0 hW''0 hWD
    · rw [mul_zero]; exact mul_nonneg hT0 hW'0
  · filter_upwards [bcalEDecay_core d hmain hKb hKd hDL k hτ' hD' hτd hDp] with n hn p
    obtain ⟨h14, hN1, hWD, hu⟩ := hn
    obtain ⟨h2R, hR0, S, hS, hgood⟩ := hu p.1
    refine le_trans (measure_mono ?_) hS
    intro ω hω
    by_contra hωS
    obtain ⟨hdLL, -, -, -, -⟩ := hgood ω hωS
    simp only [Set.mem_ofPred_eq] at hω
    refine absurd hω (not_lt.2 ?_)
    have hT0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τd := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hW'0 : 0 ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hW''0 : 0 ≤ (d.W n : ℝ) ^ (-(D' + ((2 * k + 4 : ℕ) : ℝ) / c)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
      rw [Sizes.size_eq]; push_cast; ring
    unfold farInd
    split_ifs with hf
    · rw [mul_one]
      have hkk : 0 < k + k := by omega
      obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup
        (Finset.univ : Finset (Fin (k + k) × Fin (k + k)))
        ⟨(⟨0, hkk⟩, ⟨0, hkk⟩), Finset.mem_univ _⟩
        (fun q : Fin (k + k) × Fin (k + k) => zdist2 (d.L n)
          (Fin.append p.2.2.1 p.2.2.2 q.1 - Fin.append p.2.2.1 p.2.2.2 q.2))
      have hfar : ellT (d.L n) p.1 * (d.W n : ℝ) ^ (τ' / 2) ≤
          (zdist2 (d.L n) (Fin.append p.2.2.1 p.2.2.2 q.1 - Fin.append p.2.2.1 p.2.2.2 q.2) : ℝ) := by
        have h0 : ellT (d.L n) p.1 * (d.W n : ℝ) ^ (τ' / 2) ≤
            2 * (ellT (d.L n) p.1 * (d.W n : ℝ) ^ (τ' / 2)) + 1 := by linarith
        refine h0.trans (h2R.trans (hf.trans (le_of_eq ?_)))
        unfold KLoop.maxDist
        rw [hq]
      have hdet := bcalEDecay_det_v2 (d.three_le_L n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        (n := k) (mul_nonneg hT0 hW''0) hdLL p.2.1 p.2.2.1 p.2.2.2 hfar
      refine hdet.trans ?_
      rw [hWL]
      have hkN : (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
        have h3 : (k : ℝ) ^ 1 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1 (by norm_num)
        rw [pow_one] at h3
        have h3' : (0 : ℝ) ≤ (k : ℝ) ^ 3 := by positivity
        linarith
      exact bcalEDecay_num2 hkN hN1 hT0 hW''0 hWD
    · rw [mul_zero]; exact mul_nonneg hT0 hW'0

end Main

/-! ## 11. Checks -/

end RBM.Ind

end
