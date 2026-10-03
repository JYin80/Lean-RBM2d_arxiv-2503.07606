/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Case4

/-!
# Case 5 of `lem:sum_decay`: the `2k`-kernel

Paper: arXiv:2503.07606, Section 7: `eq:double_sum_zero_tensor`, `nonalternating`, the Case 5
proof (`eq-dsz`).

Statements (namespace `RBM.Evol`): the `Prop`s `UgenPairCase1Explicit`,
`UgenPairCase5AltExplicit`.  Proved here, for the explicit constants
`cPair1`, `cCase5`: `ugenPairCase1Explicit : UgenPairCase1Explicit cPair1`,
`ugenPairCase5AltExplicit : UgenPairCase5AltExplicit cCase5`.

Argument (`d = 2`).  The `2k` labels `(b, b')` are one tuple
`c : Fin (k + k) → Z2 L` (`Fin.appendEquiv`), the tensor `A(b, b')` is `pairA A c`, and the edge
weights of the two copies are `pairXi E σ`.
* Repeated sign (`σ_{i₀} = σ_{i₀+1}`): the anchored window bound `KernelExpand_core_bound`
  over the `k + k` labels, anchored at the short edge `i₀` of the first copy
  (`xiRowBoundShort`).
* Alternating `σ`, `|E| ≤ 2`: every weight is `|m|² = 1`, so every kernel is `1 + Ξ`.
  The terms with a `δ` are bounded as in Case 4 (`KernelExpand_core_bound`).  In the all-`Ξ` term
  each `Ξ(a_j, c_j)` with `j ≠ j₀ = castAdd 0` (the label `b₀`) is split around the **common**
  anchor `c_{j₀} = b₀` as `Ξ⁰ + Ξ*`, `Ξ⁰ = Ξ(a_j, b₀)`, `Ξ* = Ξ(a_j, c_j) - Ξ(a_j, b₀)`.  If every
  first-copy piece is `Ξ⁰`, the term vanishes by the first half of `DoubleSumZero` (sum over `b`
  with `b₀` fixed); if every second-copy piece is `Ξ⁰`, by the second half (sum over `b'` with
  `b'₀` fixed).  Otherwise there is a `Ξ*` in each copy: two factors `xiFirstDiff`,
  `Case4_window_sum_one`, and the anchor sums `Case4_anchor_a`, `Case4_anchor_b`,
  `Case4_anchor_c`.

The private helpers below are copies of private lemmas of `KernelExpand.lean` and
`Case4.lean`, adapted where stated.
-/

noncomputable section

namespace RBM.Evol

open Finset RBM.Path RBM.Ind

/-- **Case 5, repeated sign** (`eq:double_sum_zero_tensor`, with a repeated sign as in
`nonalternating`): the `2k`-kernel has a short edge; Case 1's argument over all `2k` labels. -/
def UgenPairCase1Explicit (c : ℕ → ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ κ E : ℝ, 0 < κ →
    |E| ≤ 2 - κ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ σ : Fin k → Bool,
    (∃ i : Fin k, σ i = σ (i + 1)) → ∀ K M δA : ℝ, 1 ≤ K → 0 ≤ M → 0 ≤ δA →
    ∀ A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ, (∀ b b', ‖A b b'‖ ≤ M) →
    DecayWin2 L (ellT L s * K) δA A → ∀ a : Fin k → Z2 L,
      ‖UgenPair L E σ s t A a‖ ≤
        c k κ * (1 + Real.log L) ^ (2 * k) * K ^ (2 * (2 * k - 1)) * rhoR L s t ^ (2 * k) * M +
          ((1 - s) / (1 - t)) ^ (2 * k) * δA

/-- **Case 5, alternating `σ`** (`eq:double_sum_zero_tensor`, explicit): double sum
zero.  Specific to `d = 2`. -/
def UgenPairCase5AltExplicit (c : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ σ : Fin k → Bool, (∀ i : Fin k, σ i ≠ σ (i + 1)) →
    ∀ K M δA : ℝ, 1 ≤ K → 0 ≤ M → 0 ≤ δA →
    ∀ A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ, (∀ b b', ‖A b b'‖ ≤ M) →
    DecayWin2 L (ellT L s * K) δA A → DoubleSumZero L A → ∀ a : Fin k → Z2 L,
      ‖UgenPair L E σ s t A a‖ ≤
        c k * (1 + Real.log L) ^ (2 * k + 1) * K ^ (4 * k) * rhoR L s t ^ (2 * k) * M +
          c k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * ((1 - s) / (1 - t)) ^ (2 * k) * δA

/-- The explicit constant of the repeated-sign case: `(1 + cShortRow κ)(1 + 18 cProp5)^(2k-1)`
(`cCase1` at
`2k` labels). -/
def cPair1 (k : ℕ) (κ : ℝ) : ℝ := (1 + cShortRow κ) * (1 + 18 * cProp5) ^ (2 * k - 1)

/-- The explicit constant of the alternating case: `(4 X)^(2k)` with
`X = 10⁶ (cProp5 + 8·10¹⁴ + 720)`
(`cCase4` at `2k` labels). -/
def cCase5 (k : ℕ) : ℝ := (4 * (10 ^ 6 * (cProp5 + (8 * 10 ^ 14 + 720)))) ^ (2 * k)

/-! ## Two copies as one tuple of `k + k` labels -/

section Pair

variable {L : ℕ} [NeZero L]

/-- A sum over `Fin (k + k) → Z2 L` is a double sum over the two blocks (`Fin.appendEquiv`). -/
private theorem sum_append {R : Type*} [AddCommMonoid R] {k : ℕ}
    (F : (Fin (k + k) → Z2 L) → R) :
    ∑ c, F c = ∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L, F (Fin.append b b') := by
  rw [← Equiv.sum_comp (Fin.appendEquiv k k) F, Fintype.sum_prod_type]
  rfl

/-- The `2k`-tensor as a function of one tuple of `k + k` labels. -/
private def pairA {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) :
    (Fin (k + k) → Z2 L) → ℂ :=
  fun c => A (fun i => c (Fin.castAdd k i)) (fun i => c (Fin.natAdd k i))

omit [NeZero L] in
private theorem pairA_append {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (b b' : Fin k → Z2 L) : pairA A (Fin.append b b') = A b b' := by
  simp only [pairA, Fin.append_left, Fin.append_right]

omit [NeZero L] in
private theorem pairA_norm {k : ℕ} {A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ} {M : ℝ}
    (h : ∀ b b', ‖A b b'‖ ≤ M) (c : Fin (k + k) → Z2 L) : ‖pairA A c‖ ≤ M :=
  h _ _

private theorem pairA_decay {k : ℕ} {A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ} {ρ δA : ℝ}
    (h : DecayWin2 L ρ δA A) : DecayWin L ρ δA (pairA A) := by
  intro c hc
  have h1 := h (fun i => c (Fin.castAdd k i)) (fun i => c (Fin.natAdd k i))
  rw [Fin.append_castAdd_natAdd] at h1
  exact h1 hc

/-- The edge weights of the two copies: `m(σᵢ) m(σᵢ₊₁)`, then `m(σ̄ᵢ) m(σ̄ᵢ₊₁)`. -/
private def pairXi (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) : Fin (k + k) → ℂ :=
  Fin.append (fun i => KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))
    (fun i => KLoop.mSig E (!σ i) * KLoop.mSig E (!σ (i + 1)))

/-- `UgenPair` as one sum over `k + k` labels. -/
private theorem ugenPair_eq (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    UgenPair L E σ s t A a = ∑ c : Fin (k + k) → Z2 L,
      (∏ j, ukerMat L (pairXi E σ j) s t (Fin.append a a j) (c j)) * pairA A c := by
  rw [sum_append]
  unfold UgenPair
  refine sum_congr rfl fun b _ => sum_congr rfl fun b' _ => ?_
  rw [Fin.prod_univ_add, pairA_append]
  simp only [pairXi, Fin.append_left, Fin.append_right]

private theorem castAdd_ne_natAdd {k : ℕ} (i i' : Fin k) :
    Fin.castAdd k i ≠ Fin.natAdd k i' := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  omega

end Pair

/-! ## Helpers copied from `KernelExpand.lean` (private there) -/

section KEHelpers

variable {L : ℕ} [NeZero L]

/-- Copy of `KernelExpand.lean`'s private `norm_mSig_one`. -/
private theorem norm_mSig_one {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ‖ = 1 := by
  cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

/-- Copy of `KernelExpand.lean`'s private `norm_edge_one`. -/
private theorem norm_edge_one {E : ℝ} (hE : |E| ≤ 2) (σ σ' : Bool) :
    ‖KLoop.mSig E σ * KLoop.mSig E σ'‖ = 1 := by
  rw [norm_mul, norm_mSig_one hE, norm_mSig_one hE, one_mul]

private theorem norm_ukerMat_le (ξ : ℂ) (v w : ℝ) (a c : Z2 L) :
    ‖ukerMat L ξ v w a c‖ ≤
      ‖xiMat L ξ v w a c‖ + ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ := by
  rw [KernelExpand_ukerMat_apply]; exact norm_add_le _ _

private theorem sum_norm_ukerMat_le {ξ : ℂ} {v w r : ℝ} (a : Z2 L)
    (h : ∑ c : Z2 L, ‖xiMat L ξ v w a c‖ ≤ r) :
    ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖ ≤ r + 1 := by
  calc ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖
      ≤ ∑ c : Z2 L, (‖xiMat L ξ v w a c‖ + ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖) :=
        Finset.sum_le_sum fun c _ => norm_ukerMat_le ξ v w a c
    _ = ∑ c : Z2 L, ‖xiMat L ξ v w a c‖ + ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ :=
        Finset.sum_add_distrib
    _ ≤ r + 1 := by rw [KernelExpand_sum_norm_one_row]; linarith

/-- Copy of `KernelExpand.lean`'s private `row_le`. -/
private theorem row_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a : Z2 L) :
    ∑ c : Z2 L, ‖ukerMat L ξ s t a c‖ ≤ (1 - s) / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have h := sum_norm_ukerMat_le a (xiRowBound L hL ξ hξ s t hs hst ht a)
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- Copy of `KernelExpand.lean`'s private `ball_le`. -/
private theorem ball_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a x : Z2 L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
        ‖ukerMat L ξ s t a c‖ ≤
      1 + (2 * ρ + 1) ^ 2 *
        (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by
  classical
  set e : ℝ := 2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) with he
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have he0 : 0 ≤ e := by
    rw [he]
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hlog) (by linarith)) hm.le
  have hent : ∀ c : Z2 L, ‖xiMat L ξ s t a c‖ ≤ e := by
    intro c
    have h := xiEntryBound L hL ξ hξ s t hs hst ht a c
    have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
    have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by simp) (by linarith)
    calc ‖xiMat L ξ s t a c‖
        ≤ e * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) := h
      _ ≤ e * 1 := mul_le_mul_of_nonneg_left hexp he0
      _ = e := mul_one e
  have hcard := RBM.KLoop.card_ball_le L x ρ hρ
  calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
        ‖ukerMat L ξ s t a c‖
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
          (‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ + e) :=
        Finset.sum_le_sum fun c _ => by
          have h1 := norm_ukerMat_le ξ s t a c
          have h2 := hent c
          linarith
    _ = ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
          ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ +
        ((Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ)).card : ℝ) * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 + (2 * ρ + 1) ^ 2 * e := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hcard he0)
        calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
              ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖
            ≤ ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun c _ _ => norm_nonneg _)
          _ = 1 := KernelExpand_sum_norm_one_row a

omit [NeZero L] in
/-- Copy of `KernelExpand.lean`'s private `window_const`. -/
private theorem window_const (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (hK : 1 ≤ K) :
    1 + (2 * (ellT L s * K) + 1) ^ 2 *
        (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) ≤
      (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hlog1 : 1 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  set ℓ : ℝ := ellT L s with hℓdef
  set R : ℝ := rhoR L s t with hRdef
  set m : ℝ := min 1 ((L : ℝ) ^ 2 * (1 - t)) with hmdef
  set lam : ℝ := 1 + Real.log L with hlam
  have hρ1 : 1 ≤ ℓ * K := by nlinarith
  have hq : ℓ ^ 2 * (t - s) / m ≤ R := by
    rw [hRdef, KernelExpand_rhoR_eq hs1 ht, ← KernelExpand_ellT_sq_mul hs1,
      div_le_div_iff_of_pos_right hm]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have h9 : (2 * (ℓ * K) + 1) ^ 2 ≤ 9 * (ℓ * K) ^ 2 := by nlinarith
  have he0 : 0 ≤ 2 * cProp5 * lam * (t - s) / m :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hlog) (by linarith)) hm.le
  have hρe : (ℓ * K) ^ 2 * (2 * cProp5 * lam * (t - s) / m) =
      2 * cProp5 * lam * K ^ 2 * (ℓ ^ 2 * (t - s) / m) := by ring
  have hpos : 0 ≤ 2 * cProp5 * lam * K ^ 2 := by positivity
  have h1 : 1 ≤ lam * K ^ 2 * R := by
    have : 1 ≤ K ^ 2 := by nlinarith
    have h2 : 1 ≤ lam * K ^ 2 := by nlinarith
    nlinarith
  calc 1 + (2 * (ℓ * K) + 1) ^ 2 * (2 * cProp5 * lam * (t - s) / m)
      ≤ 1 + 9 * (ℓ * K) ^ 2 * (2 * cProp5 * lam * (t - s) / m) := by
        have := mul_le_mul_of_nonneg_right h9 he0
        linarith
    _ = 1 + 9 * (2 * cProp5 * lam * K ^ 2 * (ℓ ^ 2 * (t - s) / m)) := by
        rw [mul_assoc 9, hρe]
    _ ≤ 1 + 9 * (2 * cProp5 * lam * K ^ 2 * R) := by
        have := mul_le_mul_of_nonneg_left hq hpos
        linarith
    _ ≤ (1 + 18 * cProp5) * lam * K ^ 2 * R := by nlinarith

end KEHelpers

/-! ## Helpers copied from `Case4.lean` (private there) -/

section C4Helpers

variable {L : ℕ} [NeZero L]

private theorem c5_zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem c5_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, c5_zdist_neg]

private theorem c5_zdist2_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← neg_sub x y, c5_zdist2_neg]

/-- Copy of `Case4.lean`'s private `card_near_le`. -/
private theorem card_near_le {ρ : ℝ} (hρ : 1 ≤ ρ) (c : Z2 L) :
    ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ) ≤ 9 * ρ ^ 2 := by
  have hsub : (univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ) ⊆
      (univ.filter fun x : Z2 L => (zdist2 L (c - x) : ℝ) ≤ ρ) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [c5_zdist2_comm]; exact hx.le
  have h1 := RBM.KLoop.card_ball_le L c ρ (by linarith)
  calc ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ)
      ≤ (((univ.filter fun x : Z2 L => (zdist2 L (c - x) : ℝ) ≤ ρ).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ (2 * ρ + 1) ^ 2 := h1
    _ ≤ 9 * ρ ^ 2 := by nlinarith

end C4Helpers

section C4Scales

variable {L : ℕ}

/-- Copy of `Case4.lean`'s private `eT`: `e = 2 cProp5 (1 + log L)(t - s)/min(1, L²(1-t))`. -/
private def eT (L : ℕ) (s t : ℝ) : ℝ :=
  2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))

private theorem c5_cProp5_ge_one : 1 ≤ cProp5 := by unfold cProp5; norm_num

private theorem c5_lam_ge_one (L : ℕ) : 1 ≤ 1 + Real.log L := by
  linarith [Real.log_natCast_nonneg L]

private theorem eT_nonneg (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 0 ≤ eT L s t := by
  unfold eT
  have hm := KernelExpand_min_one_pos' hL ht
  have h1 := c5_lam_ge_one L
  have h2 := c5_cProp5_ge_one
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hm.le

/-- Copy of `Case4.lean`'s private `ellT_sq_eT_le`: `ℓ_s² e ≤ 2 cProp5 λ R`. -/
private theorem ellT_sq_eT_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    ellT L s ^ 2 * eT L s t ≤ 2 * cProp5 * (1 + Real.log L) * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm := KernelExpand_min_one_pos' hL ht
  have hq : ellT L s ^ 2 * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ rhoR L s t := by
    rw [KernelExpand_rhoR_eq hs1 ht, ← KernelExpand_ellT_sq_mul hs1,
      div_le_div_iff_of_pos_right hm]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have heq : ellT L s ^ 2 * eT L s t = 2 * cProp5 * (1 + Real.log L) *
      (ellT L s ^ 2 * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by
    unfold eT; ring
  rw [heq]
  have h1 := c5_lam_ge_one L
  have h2 := c5_cProp5_ge_one
  exact mul_le_mul_of_nonneg_left hq (mul_nonneg (by linarith) (by linarith))

/-- Copy of `Case4.lean`'s private `L2_eT_le`: `L² e ≤ 2 cProp5 λ L² (1-s)/(1-t)`. -/
private theorem L2_eT_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (L : ℝ) ^ 2 * eT L s t ≤
      2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) := by
  have h1t : 0 < 1 - t := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hmle : 1 - t ≤ min 1 ((L : ℝ) ^ 2 * (1 - t)) :=
    le_min (by linarith) (by nlinarith)
  have h1 := c5_lam_ge_one L
  have h2 := c5_cProp5_ge_one
  have hc : 0 ≤ 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  unfold eT
  calc (L : ℝ) ^ 2 * (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)))
      = 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 *
          ((t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by ring
    _ ≤ 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) := by
      refine mul_le_mul_of_nonneg_left ?_ hc
      calc (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ (t - s) / (1 - t) :=
            div_le_div_of_nonneg_left (by linarith) h1t hmle
        _ ≤ (1 - s) / (1 - t) := div_le_div_of_nonneg_right (by linarith) h1t.le

/-- Copy of `Case4.lean`'s private `Pl_le`. -/
private theorem Pl_le (L : ℕ) :
    derivativePrefactor (10 ^ 14) L ≤ (8 * 10 ^ 14 + 720) * (1 + Real.log L) := by
  unfold derivativePrefactor
  have := c5_lam_ge_one L
  nlinarith

private theorem Pl_nonneg (L : ℕ) : 0 ≤ derivativePrefactor (10 ^ 14) L := by
  unfold derivativePrefactor
  have := c5_lam_ge_one L
  nlinarith

end C4Scales

section C4Entry

variable {L : ℕ} [NeZero L]

/-- Copy of `Case4.lean`'s private `xi_le_eT`: `|Ξ(a, c)| ≤ e`. -/
private theorem xi_le_eT (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a c : Z2 L) : ‖xiMat L ξ s t a c‖ ≤ eT L s t := by
  have h := xiEntryBound L hL ξ hξ s t hs hst ht a c
  have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by simp) (by linarith)
  calc ‖xiMat L ξ s t a c‖
      ≤ eT L s t * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) := h
    _ ≤ eT L s t * 1 := mul_le_mul_of_nonneg_left hexp (eT_nonneg hL hst ht)
    _ = eT L s t := mul_one _

/-- Copy of `Case4.lean`'s private `anchor_eq`: `Σ_b ∏ᵢ g_i(b_j, b_i) =
Σ_x g_j(x, x) ∏_{i ≠ j} Σ_c g_i(x, c)` (see `sum_prod_anchor_le`). -/
private theorem anchor_eq {R : Type*} [CommSemiring R] {n : ℕ} (g : Fin n → Z2 L → Z2 L → R)
    (j : Fin n) :
    ∑ b : Fin n → Z2 L, ∏ i, g i (b j) (b i) =
      ∑ x : Z2 L, g j x x * ∏ i ∈ univ.erase j, ∑ c : Z2 L, g i x c := by
  classical
  set h : Z2 L → Fin n → Z2 L → R := fun x i c =>
    if i = j then (if c = x then g i x c else 0) else g i x c with hh
  have h1 : ∀ b : Fin n → Z2 L, ∏ i, g i (b j) (b i) = ∑ x : Z2 L, ∏ i, h x i (b i) := by
    intro b
    rw [Finset.sum_eq_single (b j)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hh]
      split_ifs with hi
      · rfl
      · subst hi; exact absurd rfl ‹¬b i = b i›
      · rfl
    · intro x _ hx
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [hh, ite_true]
      rw [ite_eq_right_iff]
      intro hbx; exact absurd hbx.symm hx
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [KernelExpand_sum_prod_pi (h x), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  · simp only [hh, ite_true]
    rw [Finset.sum_ite_eq' Finset.univ x (g j x)]; simp
  · refine prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [hh, hij, ite_false]

/-- Copy of `Case4.lean`'s private `mSig_alt`: `m(σ) m(σ') = |m|² = 1` for `σ ≠ σ'`. -/
private theorem mSig_alt {E : ℝ} (hE : |E| ≤ 2) {σ σ' : Bool} (h : σ ≠ σ') :
    KLoop.mSig E σ * KLoop.mSig E σ' = 1 := by
  have hn := Gauss.norm_spectralM hE
  cases σ <;> cases σ'
  · exact absurd rfl h
  · simp only [KLoop.mSig, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.conj_mul', hn]; simp
  · simp only [KLoop.mSig, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.mul_conj', hn]; simp
  · exact absurd rfl h

end C4Entry

/-! ## Numerical bookkeeping (copied from `Case4.lean`, private there) -/

section Numerics

/-- `X = 10⁶ (cProp5 + 8·10¹⁴ + 720)`. -/
private def case5X : ℝ := 10 ^ 6 * (cProp5 + (8 * 10 ^ 14 + 720))

private theorem cCase5_eq (k : ℕ) : cCase5 k = 4 ^ (k + k) * case5X ^ (k + k) := by
  unfold cCase5 case5X; rw [show 2 * k = k + k by ring, mul_pow]

private theorem case5X_ge_one : 1 ≤ case5X := by unfold case5X cProp5; norm_num

private theorem case5X_ge_B : 1 + 18 * cProp5 ≤ case5X := by unfold case5X cProp5; norm_num

private theorem case5X_ge_F : 2 + 2 * cProp5 ≤ case5X := by unfold case5X cProp5; norm_num

private theorem case5X_ge_G : 54 * cProp5 ≤ case5X := by unfold case5X cProp5; norm_num

private theorem case5X_iv : 81000000 * (8 * 10 ^ 14 + 720) ^ 2 * cProp5 ≤ case5X ^ 3 := by
  unfold case5X cProp5; norm_num

/-- Copy of `Case4.lean`'s private `num_T`. -/
private theorem num_T {k : ℕ} (hk : 2 ≤ k) {lam K R : ℝ} (hlam : 1 ≤ lam) (hK : 1 ≤ K)
    (hR : 1 ≤ R) :
    ((1 + 18 * cProp5) * lam * K ^ 2 * R) ^ (k - 1) ≤
      case5X ^ k * (lam ^ (k + 1) * K ^ (2 * k) * R ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case5X_ge_one
  have hXB := case5X_ge_B
  have hP : (0 : ℝ) ≤ 1 + 18 * cProp5 := by unfold cProp5; norm_num
  have hB0 : 0 ≤ (1 + 18 * cProp5) * lam * K ^ 2 * R := by
    have : 0 ≤ K ^ 2 := sq_nonneg K
    exact mul_nonneg (mul_nonneg (mul_nonneg hP (by linarith)) this) (by linarith)
  have hBle : (1 + 18 * cProp5) * lam * K ^ 2 * R ≤ case5X * lam * K ^ 2 * R := by
    have : 0 ≤ lam * K ^ 2 * R := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg K)) (by linarith)
    nlinarith
  have hbase : 0 ≤ case5X ^ m * lam ^ m * K ^ (2 * m) * R ^ m := by
    have : 0 ≤ case5X := by linarith
    have : 0 ≤ lam := by linarith
    have : 0 ≤ R := by linarith
    positivity
  have h1 : 1 ≤ case5X * lam ^ 2 * K ^ 2 * R := by
    have a1 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam
    have a2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
    have a3 : 1 ≤ case5X * lam ^ 2 := one_le_mul_of_one_le_of_one_le hX a1
    have a4 : 1 ≤ case5X * lam ^ 2 * K ^ 2 := one_le_mul_of_one_le_of_one_le a3 a2
    exact one_le_mul_of_one_le_of_one_le a4 hR
  calc ((1 + 18 * cProp5) * lam * K ^ 2 * R) ^ m ≤ (case5X * lam * K ^ 2 * R) ^ m :=
        pow_le_pow_left₀ hB0 hBle m
    _ = case5X ^ m * lam ^ m * K ^ (2 * m) * R ^ m := by ring
    _ ≤ case5X ^ m * lam ^ m * K ^ (2 * m) * R ^ m * (case5X * lam ^ 2 * K ^ 2 * R) :=
        le_mul_of_one_le_right hbase h1
    _ = case5X ^ (m + 1) * (lam ^ (m + 1 + 1) * K ^ (2 * (m + 1)) * R ^ (m + 1)) := by ring

/-- Copy of `Case4.lean`'s private `num_far_T`. -/
private theorem num_far_T {k : ℕ} {Y lamL : ℝ} (hY : 0 ≤ Y) (hl : 1 ≤ lamL) :
    Y ^ k ≤ case5X ^ k * (lamL ^ k * Y ^ k) := by
  have hX := case5X_ge_one
  have h1 : 1 ≤ case5X ^ k * lamL ^ k :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) (one_le_pow₀ hl)
  calc Y ^ k ≤ Y ^ k * (case5X ^ k * lamL ^ k) := le_mul_of_one_le_right (pow_nonneg hY k) h1
    _ = case5X ^ k * (lamL ^ k * Y ^ k) := by ring

/-- Copy of `Case4.lean`'s private `num_far_V`. -/
private theorem num_far_V {k : ℕ} (hk : 2 ≤ k) {y Y F lamL : ℝ} (hy : y ≤ Y)
    (hY : 1 ≤ Y) (hl : 1 ≤ lamL) (hF0 : 0 ≤ F) (hF : F ≤ (2 + 2 * cProp5) * lamL * Y) :
    y * F ^ (k - 1) ≤ case5X ^ k * (lamL ^ k * Y ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case5X_ge_one
  have hXF := case5X_ge_F
  have hFle : F ≤ case5X * lamL * Y := by
    have : 0 ≤ lamL * Y := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbase : 0 ≤ case5X ^ m * lamL ^ m * Y ^ (m + 1) := by
    have : 0 ≤ case5X := by linarith
    have : 0 ≤ lamL := by linarith
    have : 0 ≤ Y := by linarith
    positivity
  calc y * F ^ m ≤ Y * (case5X * lamL * Y) ^ m :=
        mul_le_mul hy (pow_le_pow_left₀ hF0 hFle m) (pow_nonneg hF0 m) (by linarith)
    _ = case5X ^ m * lamL ^ m * Y ^ (m + 1) := by ring
    _ ≤ case5X ^ m * lamL ^ m * Y ^ (m + 1) * (case5X * lamL) :=
        le_mul_of_one_le_right hbase (one_le_mul_of_one_le_of_one_le hX hl)
    _ = case5X ^ (m + 1) * (lamL ^ (m + 1) * Y ^ (m + 1)) := by ring

/-- Copy of `Case4.lean`'s private `num_iv` (the two-`Ξ*` group). -/
private theorem num_iv {k : ℕ} (hk : 3 ≤ k) {lam K R Pl G S r5 sl : ℝ} (hlam : 1 ≤ lam)
    (hK : 1 ≤ K) (hR : 1 ≤ R) (hPl0 : 0 ≤ Pl) (hPl : Pl ≤ (8 * 10 ^ 14 + 720) * lam)
    (hG0 : 0 ≤ G) (hG : G ≤ 54 * cProp5 * lam * K ^ 2 * R) (hr50 : 0 ≤ r5)
    (hr5 : r5 ≤ 3) (hsl0 : 0 ≤ sl) (hsl : sl ≤ lam)
    (hS : S ≤ (18 * Pl) ^ 2 * K ^ 6 * (10 * cProp5 * lam ^ 2 * R +
      2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3)) :
    S * G ^ (k - 3) ≤ case5X ^ k * (lam ^ (k + 1) * K ^ (2 * k) * R ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case5X_ge_one
  have hXG := case5X_ge_G
  have hX3 := case5X_iv
  have hP := c5_cProp5_ge_one
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hK6 : 0 ≤ K ^ 6 := by positivity
  have hPlam : 1 ≤ cProp5 * lam ^ 2 :=
    one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hlam)
  have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  have hR30 : 0 ≤ R ^ 3 := pow_nonneg hR0 3
  have hbr : 10 * cProp5 * lam ^ 2 * R + 2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) +
      R ^ 3 ≤ 250000 * (cProp5 * lam ^ 2) * R ^ 3 := by
    have b1 : 10 * cProp5 * lam ^ 2 * R ≤ 10 * (cProp5 * lam ^ 2) * R ^ 3 := by
      have : 0 ≤ 10 * (cProp5 * lam ^ 2) := by linarith
      nlinarith
    have b2 : r5 * (lam * sl) ≤ 3 * lam ^ 2 := by
      have : lam * sl ≤ lam ^ 2 := by nlinarith
      have : 0 ≤ lam * sl := mul_nonneg hlam0 hsl0
      nlinarith
    have b2' : 2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) ≤
        240012 * (cProp5 * lam ^ 2) * R ^ 3 := by
      have hPR : 0 ≤ cProp5 * R ^ 3 := mul_nonneg (by linarith) hR30
      have := mul_le_mul_of_nonneg_left b2 hPR
      nlinarith
    have b3 : R ^ 3 ≤ (cProp5 * lam ^ 2) * R ^ 3 := le_mul_of_one_le_left hR30 hPlam
    nlinarith
  have hPl2 : (18 * Pl) ^ 2 ≤ 324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2 := by
    have : 18 * Pl ≤ 18 * ((8 * 10 ^ 14 + 720) * lam) := by linarith
    have h := pow_le_pow_left₀ (by linarith) this 2
    calc (18 * Pl) ^ 2 ≤ (18 * ((8 * 10 ^ 14 + 720) * lam)) ^ 2 := h
      _ = 324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2 := by ring
  have hS1 : S ≤ case5X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) := by
    have hbr0 : 0 ≤ 10 * cProp5 * lam ^ 2 * R +
        2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3 := by
      have : 0 ≤ cProp5 := by linarith
      positivity
    calc S ≤ (18 * Pl) ^ 2 * K ^ 6 * (10 * cProp5 * lam ^ 2 * R +
          2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3) := hS
      _ ≤ (324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2) * K ^ 6 *
          (250000 * (cProp5 * lam ^ 2) * R ^ 3) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hPl2 hK6) hbr hbr0 ?_
          positivity
      _ = 81000000 * (8 * 10 ^ 14 + 720) ^ 2 * cProp5 * (lam ^ 4 * K ^ 6 * R ^ 3) := by ring
      _ ≤ case5X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) :=
          mul_le_mul_of_nonneg_right hX3 (by positivity)
  have hGle : G ≤ case5X * (lam * K ^ 2 * R) := by
    have : 0 ≤ lam * K ^ 2 * R := mul_nonneg (mul_nonneg hlam0 (sq_nonneg K)) hR0
    nlinarith
  have hGm : G ^ m ≤ (case5X * (lam * K ^ 2 * R)) ^ m := pow_le_pow_left₀ hG0 hGle m
  have hA0 : 0 ≤ case5X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) := by positivity
  calc S * G ^ m ≤ case5X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) * (case5X * (lam * K ^ 2 * R)) ^ m :=
        mul_le_mul hS1 hGm (pow_nonneg hG0 m) hA0
    _ = case5X ^ (m + 3) * (lam ^ (m + 3 + 1) * K ^ (2 * (m + 3)) * R ^ (m + 3)) := by ring

end Numerics

/-! ## The two pieces around the common anchor -/

section Pieces

variable {L : ℕ} [NeZero L]

/-- The two pieces of `Ξ(a, x)` around the anchor `c` (`Ξ = xiMat L 1 s t`):
`Ξ⁰ = Ξ(a, c)`, `Ξ* = Ξ(a, x) - Ξ(a, c)`. -/
private def piece2 (L : ℕ) [NeZero L] (s t : ℝ) (a c x : Z2 L) : Fin 2 → ℂ :=
  ![xiMat L 1 s t a c, xiMat L 1 s t a x - xiMat L 1 s t a c]

private theorem piece2_zero_eq (s t : ℝ) (a c x : Z2 L) :
    piece2 L s t a c x 0 = xiMat L 1 s t a c := rfl

private theorem piece2_one_eq (s t : ℝ) (a c x : Z2 L) :
    piece2 L s t a c x 1 = xiMat L 1 s t a x - xiMat L 1 s t a c := rfl

private theorem piece2_sum (s t : ℝ) (a c x : Z2 L) :
    ∑ p : Fin 2, piece2 L s t a c x p = xiMat L 1 s t a x := by
  rw [Fin.sum_univ_two, piece2_zero_eq, piece2_one_eq]
  ring

/-- At `x = c` the piece `Ξ*` vanishes. -/
private theorem piece2_self (s t : ℝ) (a c : Z2 L) {p : Fin 2} (hp : p ≠ 0) :
    piece2 L s t a c c p = 0 := by
  fin_cases p
  · exact absurd rfl hp
  · change piece2 L s t a c c 1 = 0
    rw [piece2_one_eq, sub_self]

/-- `|Ξ^p(a, c, x)| ≤ |Ξ(a, x)| + |Ξ(a, c)|`. -/
private theorem norm_piece2_le (s t : ℝ) (a c x : Z2 L) (p : Fin 2) :
    ‖piece2 L s t a c x p‖ ≤ ‖xiMat L 1 s t a x‖ + ‖xiMat L 1 s t a c‖ := by
  have hx := norm_nonneg (xiMat L 1 s t a x)
  have hc := norm_nonneg (xiMat L 1 s t a c)
  fin_cases p
  · change ‖piece2 L s t a c x 0‖ ≤ _
    rw [piece2_zero_eq]; linarith
  · change ‖piece2 L s t a c x 1‖ ≤ _
    rw [piece2_one_eq]
    exact norm_sub_le _ _

/-- `|Ξ*| ≤ 2 P_L (t-s) |x - c| (1/(|a-c|+1) + 1/(√(1-t) ℓ_t²))` (`xiFirstDiff` at `(a, c, x - c)`).
-/
private theorem norm_piece2_one_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a c x : Z2 L) :
    ‖piece2 L s t a c x 1‖ ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (zdist2 L (x - c) : ℝ) *
        (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
  have h1 := xiFirstDiff L hL s t hs hst ht a c (x - c)
  have e1 : c + (x - c) = x := by abel
  rw [e1] at h1
  rw [piece2_one_eq, norm_sub_rev]
  refine h1.trans (le_of_eq ?_)
  ring

/-- Window sum of any piece: `Σ_{|x - c| < ρ} |Ξ^p| ≤ 27 ρ² e`. -/
private theorem win_all2 (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (a c : Z2 L) (p : Fin 2) :
    ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece2 L s t a c x p‖ ≤
      27 * ρ ^ 2 * eT L s t := by
  have he : ∀ y, ‖xiMat L 1 s t a y‖ ≤ eT L s t := fun y =>
    xi_le_eT hL (by simp) hs hst ht a y
  have he0 := eT_nonneg hL hst ht
  calc ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece2 L s t a c x p‖
      ≤ ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), 3 * eT L s t :=
        sum_le_sum fun x _ => (norm_piece2_le s t a c x p).trans
          (by linarith [he x, he c])
    _ = ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ) *
          (3 * eT L s t) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ρ ^ 2 * (3 * eT L s t) :=
        mul_le_mul_of_nonneg_right (card_near_le hρ c) (by linarith)
    _ = 27 * ρ ^ 2 * eT L s t := by ring

/-- Window sum of `Ξ*`: `≤ 2 P_L (t-s) (1/(|a-c|+1) + β) · 9ρ³` (`Case4_window_sum_one`). -/
private theorem win_one2 (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (a c : Z2 L) :
    ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece2 L s t a c x 1‖ ≤
      2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * ρ ^ 3) := by
  have hC : 0 ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
    have := Pl_nonneg L
    have : 0 ≤ t - s := by linarith
    positivity
  calc ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece2 L s t a c x 1‖
      ≤ ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
          2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              (zdist2 L (x - c) : ℝ) :=
        sum_le_sum fun x _ => (norm_piece2_one_le hL hs hst ht a c x).trans (le_of_eq (by ring))
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
              (zdist2 L (x - c) : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Case4_window_sum_one hρ c) hC

/-- Full row of any piece: `Σ_x |Ξ^p| ≤ 2 (t-s)/(1-t) + L² e`. -/
private theorem row_all2 (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (a c : Z2 L) (p : Fin 2) :
    ∑ x : Z2 L, ‖piece2 L s t a c x p‖ ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by
  have hrow := xiRowBound L hL 1 (by simp) s t hs hst ht a
  have hcard : ∑ _x : Z2 L, ‖xiMat L 1 s t a c‖ = (L : ℝ) ^ 2 * ‖xiMat L 1 s t a c‖ := by
    rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, ZMod.card]
    push_cast; ring
  have he : ‖xiMat L 1 s t a c‖ ≤ eT L s t := xi_le_eT hL (by simp) hs hst ht a c
  have hts : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  calc ∑ x : Z2 L, ‖piece2 L s t a c x p‖
      ≤ ∑ x : Z2 L, (‖xiMat L 1 s t a x‖ + ‖xiMat L 1 s t a c‖) :=
        sum_le_sum fun x _ => norm_piece2_le s t a c x p
    _ = ∑ x : Z2 L, ‖xiMat L 1 s t a x‖ + ∑ _x : Z2 L, ‖xiMat L 1 s t a c‖ := by
        rw [sum_add_distrib]
    _ ≤ (t - s) / (1 - t) + (L : ℝ) ^ 2 * eT L s t := by
        rw [hcard]
        have : (L : ℝ) ^ 2 * ‖xiMat L 1 s t a c‖ ≤ (L : ℝ) ^ 2 * eT L s t :=
          mul_le_mul_of_nonneg_left he (by positivity)
        linarith
    _ ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by linarith

end Pieces

/-! ## The all-`Ξ` terms, anchored at a label `j₀` -/

section Terms

variable {L : ℕ} [NeZero L]

/-- The all-`Ξ` term with the piece pattern `f : Fin n → Fin 2`, anchored at `b_{j₀}`:
`V_f = Σ_b ∏_l Ξ^{f l}(a_l; b_{j₀}, b_l) A_b`. -/
private def Vterm2 {n : ℕ} (L : ℕ) [NeZero L] (s t : ℝ) (a : Fin n → Z2 L)
    (A : (Fin n → Z2 L) → ℂ) (j₀ : Fin n) (f : Fin n → Fin 2) : ℂ :=
  ∑ b : Fin n → Z2 L, (∏ l, piece2 L s t (a l) (b j₀) (b l) (f l)) * A b

/-- **The near/far split of `V_f`** (Case 4's `norm_V_le` with the anchor `j₀` and two pieces). -/
private theorem norm_V2_le {n : ℕ} (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a : Fin n → Z2 L) (j₀ : Fin n) (f : Fin n → Fin 2) (hf0 : f j₀ = 0)
    {ρ M δA : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin n → Z2 L) → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ M) (hdec : DecayWin L ρ δA A) (W : Fin n → Z2 L → ℝ)
    (hW : ∀ l, l ≠ j₀ → ∀ c, ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
      ‖piece2 L s t (a l) c x (f l)‖ ≤ W l c) :
    ‖Vterm2 L s t a A j₀ f‖ ≤
      M * ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ * ∏ l ∈ univ.erase j₀, W l c +
        δA * ((t - s) / (1 - t) *
          (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1)) := by
  classical
  set ψ : Fin n → Z2 L → Z2 L → ℝ := fun l c x => ‖piece2 L s t (a l) c x (f l)‖ with hψ
  set ψn : Fin n → Z2 L → Z2 L → ℝ := fun l c x =>
    if (zdist2 L (x - c) : ℝ) < ρ then ψ l c x else 0 with hψn
  have hψ0 : ∀ l c x, 0 ≤ ψ l c x := fun _ _ _ => norm_nonneg _
  have hψn0 : ∀ l c x, 0 ≤ ψn l c x := by
    intro l c x; simp only [hψn]; split_ifs <;> first | exact hψ0 _ _ _ | exact le_rfl
  have hpt : ∀ b : Fin n → Z2 L, ‖(∏ l, piece2 L s t (a l) (b j₀) (b l) (f l)) * A b‖ ≤
      M * ∏ l, ψn l (b j₀) (b l) + δA * ∏ l, ψ l (b j₀) (b l) := by
    intro b
    rw [norm_mul, norm_prod]
    have hP0 : 0 ≤ ∏ l, ψ l (b j₀) (b l) := prod_nonneg fun l _ => hψ0 _ _ _
    have hPn0 : 0 ≤ ∏ l, ψn l (b j₀) (b l) := prod_nonneg fun l _ => hψn0 _ _ _
    change (∏ l, ψ l (b j₀) (b l)) * ‖A b‖ ≤ _
    by_cases hfar : ρ ≤ (KLoop.maxDist L b : ℝ)
    · have h1 : (∏ l, ψ l (b j₀) (b l)) * ‖A b‖ ≤ (∏ l, ψ l (b j₀) (b l)) * δA :=
        mul_le_mul_of_nonneg_left (hdec b hfar) hP0
      nlinarith [mul_nonneg hM hPn0]
    · push Not at hfar
      have hd : ∀ l, (zdist2 L (b l - b j₀) : ℝ) < ρ := by
        intro l
        have h := Finset.le_sup (f := fun p : Fin n × Fin n => zdist2 L (b p.1 - b p.2))
          (Finset.mem_univ (l, j₀))
        have h' : (zdist2 L (b l - b j₀) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by
          exact_mod_cast h
        linarith
      have hgeq : ∏ l, ψn l (b j₀) (b l) = ∏ l, ψ l (b j₀) (b l) := by
        refine prod_congr rfl fun l _ => ?_
        simp only [hψn, ite_eq_left (hd l)]
      rw [hgeq]
      have h1 : (∏ l, ψ l (b j₀) (b l)) * ‖A b‖ ≤ (∏ l, ψ l (b j₀) (b l)) * M :=
        mul_le_mul_of_nonneg_left (hAM b) hP0
      nlinarith [mul_nonneg hδ hP0]
  have hnear : ∑ b : Fin n → Z2 L, ∏ l, ψn l (b j₀) (b l) ≤
      ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ * ∏ l ∈ univ.erase j₀, W l c := by
    rw [anchor_eq ψn j₀]
    refine sum_le_sum fun c _ => ?_
    have h0 : ψn j₀ c c = ‖xiMat L 1 s t (a j₀) c‖ := by
      simp only [hψn, hψ, sub_self, zdist2_zero, Nat.cast_zero, ite_eq_left hρ, hf0, piece2_zero_eq]
    rw [h0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine prod_le_prod₀ (fun l _ => sum_nonneg fun x _ => hψn0 _ _ _) (fun l hl => ?_)
    have hl0 : l ≠ j₀ := ne_of_mem_erase hl
    calc ∑ x : Z2 L, ψn l c x
        = ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ψ l c x := by
          rw [sum_filter]
      _ ≤ W l c := hW l hl0 c
  have hF0 : 0 ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by
    have h1 : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
    have h2 := eT_nonneg hL hst ht
    positivity
  have hfar : ∑ b : Fin n → Z2 L, ∏ l, ψ l (b j₀) (b l) ≤
      (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) := by
    rw [anchor_eq ψ j₀]
    have hprod : ∀ c, ∏ l ∈ univ.erase j₀, ∑ x : Z2 L, ψ l c x ≤
        (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) := by
      intro c
      calc ∏ l ∈ univ.erase j₀, ∑ x : Z2 L, ψ l c x
          ≤ ∏ _l ∈ univ.erase j₀, (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) :=
            prod_le_prod₀ (fun l _ => sum_nonneg fun x _ => hψ0 _ _ _)
              (fun l _ => row_all2 hL hs hst ht (a l) c (f l))
        _ = (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) := by
            rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have hFk : 0 ≤ (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) :=
      pow_nonneg hF0 _
    calc ∑ c : Z2 L, ψ j₀ c c * ∏ l ∈ univ.erase j₀, ∑ x : Z2 L, ψ l c x
        ≤ ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ *
            (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) :=
          sum_le_sum fun c _ => by
            have h0 : ψ j₀ c c = ‖xiMat L 1 s t (a j₀) c‖ := by
              simp only [hψ, hf0, piece2_zero_eq]
            rw [h0]; exact mul_le_mul_of_nonneg_left (hprod c) (norm_nonneg _)
      _ = (∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖) *
            (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) := by rw [sum_mul]
      _ ≤ (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right (xiRowBound L hL 1 (by simp) s t hs hst ht (a j₀)) hFk
  unfold Vterm2
  calc ‖∑ b : Fin n → Z2 L, (∏ l, piece2 L s t (a l) (b j₀) (b l) (f l)) * A b‖
      ≤ ∑ b : Fin n → Z2 L, ‖(∏ l, piece2 L s t (a l) (b j₀) (b l) (f l)) * A b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : Fin n → Z2 L, (M * ∏ l, ψn l (b j₀) (b l) + δA * ∏ l, ψ l (b j₀) (b l)) :=
        sum_le_sum fun b _ => hpt b
    _ = M * ∑ b : Fin n → Z2 L, ∏ l, ψn l (b j₀) (b l) +
          δA * ∑ b : Fin n → Z2 L, ∏ l, ψ l (b j₀) (b l) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hnear hM) (mul_le_mul_of_nonneg_left hfar hδ)

/-- `V_f = 0` if `f j₀ ≠ 0` (`Ξ*` vanishes at the anchor itself). -/
private theorem V2_eq_zero_of_f0 {n : ℕ} (s t : ℝ) (a : Fin n → Z2 L)
    (A : (Fin n → Z2 L) → ℂ) (j₀ : Fin n) (f : Fin n → Fin 2) (hf : f j₀ ≠ 0) :
    Vterm2 L s t a A j₀ f = 0 := by
  unfold Vterm2
  refine sum_eq_zero fun b _ => ?_
  rw [prod_eq_zero (mem_univ j₀) (piece2_self s t (a j₀) (b j₀) (p := f j₀) hf), zero_mul]

/-- **`B = ∅`**: `V_f = 0` if every first-copy piece is `Ξ⁰` (first half of `DoubleSumZero`,
the sum over `b` with `b₀` fixed). -/
private theorem V2_eq_zero_first {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin (k + k) → Z2 L)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (hdsz : DoubleSumZero L A)
    (f : Fin (k + k) → Fin 2) (hf : ∀ i : Fin k, f (Fin.castAdd k i) = 0) :
    Vterm2 L s t a (pairA A) (Fin.castAdd k 0) f = 0 := by
  classical
  unfold Vterm2
  rw [sum_append]
  have h1 : ∀ b b' : Fin k → Z2 L,
      (∏ l, piece2 L s t (a l) (Fin.append b b' (Fin.castAdd k 0)) (Fin.append b b' l) (f l)) *
          pairA A (Fin.append b b') =
        ((∏ i, xiMat L 1 s t (a (Fin.castAdd k i)) (b 0)) *
          ∏ i, piece2 L s t (a (Fin.natAdd k i)) (b 0) (b' i) (f (Fin.natAdd k i))) * A b b' := by
    intro b b'
    rw [Fin.prod_univ_add, pairA_append]
    simp only [Fin.append_left, Fin.append_right, hf, piece2_zero_eq]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun b' _ => h1 b b', sum_comm]
  refine sum_eq_zero fun b' _ => ?_
  rw [← sum_fiberwise univ (fun b : Fin k → Z2 L => b 0)]
  refine sum_eq_zero fun x _ => ?_
  have h2 : ∑ b ∈ univ.filter (fun b : Fin k → Z2 L => b 0 = x),
      ((∏ i, xiMat L 1 s t (a (Fin.castAdd k i)) (b 0)) *
        ∏ i, piece2 L s t (a (Fin.natAdd k i)) (b 0) (b' i) (f (Fin.natAdd k i))) * A b b' =
      ∑ b ∈ univ.filter (fun b : Fin k → Z2 L => b 0 = x),
        ((∏ i, xiMat L 1 s t (a (Fin.castAdd k i)) x) *
          ∏ i, piece2 L s t (a (Fin.natAdd k i)) x (b' i) (f (Fin.natAdd k i))) * A b b' :=
    sum_congr rfl fun b hb => by rw [(mem_filter.1 hb).2]
  rw [h2, ← mul_sum, hdsz.1 x b', mul_zero]

/-- **`B' = ∅`**: `V_f = 0` if every second-copy piece is `Ξ⁰` (second half of `DoubleSumZero`,
the sum over `b'` with `b'₀` fixed). -/
private theorem V2_eq_zero_second {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin (k + k) → Z2 L)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (hdsz : DoubleSumZero L A)
    (f : Fin (k + k) → Fin 2) (hf : ∀ i : Fin k, f (Fin.natAdd k i) = 0) :
    Vterm2 L s t a (pairA A) (Fin.castAdd k 0) f = 0 := by
  classical
  unfold Vterm2
  rw [sum_append]
  have h1 : ∀ b b' : Fin k → Z2 L,
      (∏ l, piece2 L s t (a l) (Fin.append b b' (Fin.castAdd k 0)) (Fin.append b b' l) (f l)) *
          pairA A (Fin.append b b') =
        ((∏ i, piece2 L s t (a (Fin.castAdd k i)) (b 0) (b i) (f (Fin.castAdd k i))) *
          ∏ i, xiMat L 1 s t (a (Fin.natAdd k i)) (b 0)) * A b b' := by
    intro b b'
    rw [Fin.prod_univ_add, pairA_append]
    simp only [Fin.append_left, Fin.append_right, hf, piece2_zero_eq]
  rw [sum_congr rfl fun b _ => sum_congr rfl fun b' _ => h1 b b']
  refine sum_eq_zero fun b _ => ?_
  rw [← mul_sum, ← sum_fiberwise univ (fun b' : Fin k → Z2 L => b' 0),
    sum_eq_zero (fun x _ => hdsz.2 b x), mul_zero]

/-- `∏_{l ≠ j₀} (if l = i then Dᵢ else if l = j then Dⱼ else G) = Dᵢ (Dⱼ G^{n-3})` for distinct
`i, j ≠ j₀`; also `3 ≤ n` (Case 4's `prod_erase_ite_two` with the anchor `j₀`). -/
private theorem prod_erase_ite_two' {n : ℕ} (j₀ i j : Fin n) (hi : i ≠ j₀) (hj : j ≠ j₀)
    (hij : i ≠ j) (Di Dj G : ℝ) :
    3 ≤ n ∧ ∏ l ∈ univ.erase j₀, (if l = i then Di else if l = j then Dj else G) =
      Di * (Dj * G ^ (n - 3)) := by
  have hmi : i ∈ univ.erase j₀ := mem_erase.2 ⟨hi, mem_univ i⟩
  have hmj : j ∈ (univ.erase j₀).erase i :=
    mem_erase.2 ⟨Ne.symm hij, mem_erase.2 ⟨hj, mem_univ j⟩⟩
  have hc2 : ((univ.erase j₀).erase i).card = n - 1 - 1 := by
    rw [card_erase_of_mem hmi, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hk : 3 ≤ n := by
    have := card_pos.2 ⟨j, hmj⟩
    omega
  refine ⟨hk, ?_⟩
  rw [← mul_prod_erase _ _ hmi, ite_eq_left rfl]
  congr 1
  rw [← mul_prod_erase _ _ hmj, ite_eq_right (Ne.symm hij), ite_eq_left rfl]
  congr 1
  rw [prod_congr rfl fun l hl => by
      rw [ite_eq_right (ne_of_mem_erase (mem_of_mem_erase hl)), ite_eq_right (ne_of_mem_erase hl)],
    prod_const, card_erase_of_mem hmj, hc2]
  congr 1

private theorem div_prod_eq_aux (x u v : ℝ) : x / (u * v) = x * (1 / u) * (1 / v) := by
  rw [mul_one_div, mul_one_div, div_div]

omit [NeZero L] in
/-- The far bound of the all-`Ξ` terms (Case 4's `far_V_le`). -/
private theorem far_V_le {n : ℕ} (hk : 2 ≤ n) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) :
    (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (n - 1) ≤
      case5X ^ n * (((1 + Real.log L) * (L : ℝ) ^ 2) ^ n * ((1 - s) / (1 - t)) ^ n) := by
  have h1t : 0 < 1 - t := by linarith
  have hY1 : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hts : (t - s) / (1 - t) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_right (by linarith) h1t.le
  have hts0 : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) h1t.le
  have hlam := c5_lam_ge_one L
  have hP := c5_cProp5_ge_one
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hlL : 1 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hlam hL1
  have hL2e := L2_eT_le hL hs hst ht
  have he0 := eT_nonneg hL hst ht
  have hF0 : 0 ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by positivity
  have hF : 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t ≤
      (2 + 2 * cProp5) * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by
    have h2 : 2 * ((t - s) / (1 - t)) ≤
        2 * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by
      have : (1 - s) / (1 - t) ≤ ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) :=
        le_mul_of_one_le_left (by linarith) hlL
      linarith
    have h3 : 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) =
        2 * cProp5 * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by ring
    nlinarith
  exact num_far_V hk hts hY1 hlL hF0 hF

/-- **Two `Ξ*` pieces** at `i ≠ j` (both `≠ j₀`): Case 4's `bound_iv` with the two-piece split. -/
private theorem bound_iv2 {n : ℕ} (hn : 2 ≤ n) (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (hK : 1 ≤ K) (a : Fin n → Z2 L) (j₀ : Fin n) (f : Fin n → Fin 2)
    (hf0 : f j₀ = 0) (i j : Fin n) (hi0 : i ≠ j₀) (hj0 : j ≠ j₀) (hij : i ≠ j) (hi : f i = 1)
    (hj : f j = 1) {M δA : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin n → Z2 L) → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ M) (hdec : DecayWin L (ellT L s * K) δA A) :
    ‖Vterm2 L s t a A j₀ f‖ ≤
      M * (case5X ^ n * ((1 + Real.log L) ^ (n + 1) * K ^ (2 * n) * rhoR L s t ^ n)) +
        δA * (case5X ^ n * (((1 + Real.log L) * (L : ℝ) ^ 2) ^ n * ((1 - s) / (1 - t)) ^ n)) := by
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ1 : 1 ≤ ellT L s * K := by nlinarith
  have hlam := c5_lam_ge_one L
  have hP := c5_cProp5_ge_one
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have he0 := eT_nonneg hL hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  have hPl0 := Pl_nonneg L
  have hk3 := (prod_erase_ite_two' j₀ i j hi0 hj0 hij (1 : ℝ) 1 1).1
  have ha := Case4_anchor_a hL (ξ := 1) (by simp) hs hst ht (a j₀) (a i) (a j)
  have hbi := Case4_anchor_b hL (ξ := 1) (by simp) hs hst ht (a j₀) (a i)
  have hbj := Case4_anchor_b hL (ξ := 1) (by simp) hs hst ht (a j₀) (a j)
  have hc := Case4_anchor_c hL (ξ := 1) (by simp) hs hst ht (a j₀)
  have hS : ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ *
      ((2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a i - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * (ellT L s * K) ^ 3)) *
        (2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a j - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * (ellT L s * K) ^ 3))) ≤
      (18 * derivativePrefactor (10 ^ 14) L) ^ 2 * K ^ 6 *
        (10 * cProp5 * (1 + Real.log L) ^ 2 * rhoR L s t +
          2 * (2 * 20001 * Real.sqrt 5 * cProp5 *
            ((1 + Real.log L) * Real.sqrt (1 + Real.log L)) * rhoR L s t ^ 3) +
          rhoR L s t ^ 3) := by
    have heq : ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ *
        ((2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a i - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            (9 * (ellT L s * K) ^ 3)) *
          (2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a j - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            (9 * (ellT L s * K) ^ 3))) =
        (18 * derivativePrefactor (10 ^ 14) L) ^ 2 * K ^ 6 *
          (((t - s) * ellT L s ^ 3) ^ 2 * ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ /
              (((zdist2 L (a i - c) : ℝ) + 1) * ((zdist2 L (a j - c) : ℝ) + 1)) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ / ((zdist2 L (a i - c) : ℝ) + 1) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ / ((zdist2 L (a j - c) : ℝ) + 1) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) ^ 2 *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun c _ => ?_
      rw [div_prod_eq_aux ‖xiMat L 1 s t (a j₀) c‖ ((zdist2 L (a i - c) : ℝ) + 1)
        ((zdist2 L (a j - c) : ℝ) + 1)]
      ring
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  set ρ := ellT L s * K with hρ
  set Pl := derivativePrefactor (10 ^ 14) L with hPldef
  set β := 1 / (Real.sqrt (1 - t) * ellT L t ^ 2) with hβ
  set G := 27 * ρ ^ 2 * eT L s t with hG
  set D1 : Fin n → Z2 L → ℝ := fun l c => 2 * Pl * (t - s) *
    (1 / ((zdist2 L (a l - c) : ℝ) + 1) + β) * (9 * ρ ^ 3) with hD1
  set W : Fin n → Z2 L → ℝ := fun l c =>
    if l = i then D1 i c else if l = j then D1 j c else G with hW
  have hWb : ∀ l, l ≠ j₀ → ∀ c, ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
      ‖piece2 L s t (a l) c x (f l)‖ ≤ W l c := by
    intro l _ c
    by_cases hli : l = i
    · subst hli
      simp only [hW, ite_eq_left rfl, hi, hD1]
      exact win_one2 hL hs hst ht hρ1 (a l) c
    · by_cases hlj : l = j
      · subst hlj
        simp only [hW, ite_eq_right hli, hj, hD1]
        exact win_one2 hL hs hst ht hρ1 (a l) c
      · simp only [hW, ite_eq_right hli, ite_eq_right hlj, hG]
        exact win_all2 hL hs hst ht hρ1 (a l) c (f l)
  have h := norm_V2_le hL hs hst ht a j₀ f hf0 (by linarith) hM hδ hAM hdec W hWb
  refine h.trans (add_le_add ?_
    (mul_le_mul_of_nonneg_left (far_V_le hn hL hs hst ht) hδ))
  refine mul_le_mul_of_nonneg_left ?_ hM
  have hprod : ∀ c, ∏ l ∈ univ.erase j₀, W l c = D1 i c * (D1 j c * G ^ (n - 3)) := fun c =>
    (prod_erase_ite_two' j₀ i j hi0 hj0 hij (D1 i c) (D1 j c) G).2
  have hGle : G ≤ 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by
    have : G = 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t) := by rw [hG, hρ]; ring
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left hlse (by positivity : (0 : ℝ) ≤ 27 * K ^ 2)
    calc 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t)
        ≤ 27 * K ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t) := h2
      _ = 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by ring
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hr5 : Real.sqrt 5 ≤ 3 := by
    rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsl : Real.sqrt (1 + Real.log L) ≤ 1 + Real.log L := by
    rw [Real.sqrt_le_left (by linarith)]
    exact le_self_pow₀ hlam (by norm_num)
  have hnum := num_iv hk3 hlam hK hR1 hPl0 (Pl_le L) hG0 hGle (Real.sqrt_nonneg 5) hr5
    (Real.sqrt_nonneg _) hsl hS
  calc ∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ * ∏ l ∈ univ.erase j₀, W l c
      = (∑ c : Z2 L, ‖xiMat L 1 s t (a j₀) c‖ * (D1 i c * D1 j c)) * G ^ (n - 3) := by
        rw [sum_mul]
        refine sum_congr rfl fun c _ => ?_
        rw [hprod c]; ring
    _ ≤ _ := hnum

/-- The two pieces `δ`, `Ξ` of `ψ = 1 + Ξ`. -/
private def dpiece (L : ℕ) [NeZero L] (s t : ℝ) : Fin 2 → Matrix (Z2 L) (Z2 L) ℂ :=
  ![1, xiMat L 1 s t]

/-- **A term with a `δ` at `j`** (Case 4's `norm_T_le`): `≤ M B^{n-1} + δ_A ((1-s)/(1-t))^n`. -/
private theorem norm_T_le {n : ℕ} (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (hK : 1 ≤ K) (a : Fin n → Z2 L) (g : Fin n → Fin 2) (j : Fin n) (hj : g j = 0)
    {M δA : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin n → Z2 L) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hdec : DecayWin L (ellT L s * K) δA A) :
    ‖∑ b : Fin n → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ ≤
      M * ((1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t) ^ (n - 1) +
        δA * ((1 - s) / (1 - t)) ^ n := by
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * K := by nlinarith
  have hρ1 : 1 ≤ ellT L s * K := by nlinarith
  have hlam := c5_lam_ge_one L
  have hP := c5_cProp5_ge_one
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have he0 := eT_nonneg hL hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  set Bc := (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t with hBc
  set Y := (1 - s) / (1 - t) with hY
  have hY1 : 1 ≤ Y := by rw [hY, le_div_iff₀ h1t]; linarith
  have hts : (t - s) / (1 - t) ≤ Y := div_le_div_of_nonneg_right (by linarith) h1t.le
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hlKR : 1 ≤ (1 + Real.log L) * K ^ 2 * rhoR L s t :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hlam hK2) hR1
  have hB1 : 1 ≤ Bc := by
    have : Bc = (1 + 18 * cProp5) * ((1 + Real.log L) * K ^ 2 * rhoR L s t) := by
      rw [hBc]; ring
    rw [this]; exact one_le_mul_of_one_le_of_one_le (by linarith) hlKR
  have hwinX : ∀ x y : Z2 L, ∑ c ∈ univ.filter (fun c : Z2 L =>
      (zdist2 L (x - c) : ℝ) ≤ ellT L s * K), ‖xiMat L 1 s t y c‖ ≤ Bc := by
    intro x y
    have hcard := RBM.KLoop.card_ball_le L x (ellT L s * K) hρ0
    calc ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
          ‖xiMat L 1 s t y c‖
        ≤ ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
            eT L s t := sum_le_sum fun c _ => xi_le_eT hL (by simp) hs hst ht y c
      _ = ((univ.filter fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K).card : ℝ) *
            eT L s t := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * (ellT L s * K) + 1) ^ 2 * eT L s t := mul_le_mul_of_nonneg_right hcard he0
      _ ≤ 9 * (ellT L s * K) ^ 2 * eT L s t := by
          have : (2 * (ellT L s * K) + 1) ^ 2 ≤ 9 * (ellT L s * K) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this he0
      _ = 9 * K ^ 2 * (ellT L s ^ 2 * eT L s t) := by ring
      _ ≤ 9 * K ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t) :=
          mul_le_mul_of_nonneg_left hlse (by positivity)
      _ ≤ Bc := by
          rw [hBc]
          have : 0 ≤ (1 + Real.log L) * K ^ 2 * rhoR L s t := by linarith
          nlinarith
  have hrow : ∀ (p : Fin 2) (y : Z2 L), ∑ c : Z2 L, ‖dpiece L s t p y c‖ ≤ Y := by
    intro p y
    fin_cases p
    · change ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ ≤ Y
      rw [KernelExpand_sum_norm_one_row]; exact hY1
    · change ∑ c : Z2 L, ‖xiMat L 1 s t y c‖ ≤ Y
      exact (xiRowBound L hL 1 (by simp) s t hs hst ht y).trans hts
  have hwin : ∀ (p : Fin 2) (x y : Z2 L), ∑ c ∈ univ.filter (fun c : Z2 L =>
      (zdist2 L (x - c) : ℝ) ≤ ellT L s * K), ‖dpiece L s t p y c‖ ≤ Bc := by
    intro p x y
    fin_cases p
    · change ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
        ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ ≤ Bc
      calc ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
            ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖
          ≤ ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun c _ _ => norm_nonneg _)
        _ = 1 := KernelExpand_sum_norm_one_row y
        _ ≤ Bc := hB1
    · exact hwinX x y
  have hanc : ∑ c : Z2 L, ‖dpiece L s t (g j) (a j) c‖ ≤ 1 := by
    rw [hj]
    change ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a j) c‖ ≤ 1
    rw [KernelExpand_sum_norm_one_row]
  have hcore := KernelExpand_core_bound (L := L)
    (fun l c => ‖dpiece L s t (g l) (a l) c‖) (fun l c => norm_nonneg _) (A := A)
    (ρ := ellT L s * K) (M := M) (δA := δA) (r := Y) (Rj := 1) (B := Bc) hM hδ hAM hdec j
    (fun l => hrow (g l) (a l)) hanc (fun l _ x => hwin (g l) x (a l))
  calc ‖∑ b : Fin n → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖
      ≤ ∑ b : Fin n → Z2 L, ‖(∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ := norm_sum_le _ _
    _ = ∑ b : Fin n → Z2 L, (∏ l, ‖dpiece L s t (g l) (a l) (b l)‖) * ‖A b‖ := by
        refine sum_congr rfl fun b _ => ?_
        rw [norm_mul, norm_prod]
    _ ≤ M * (1 * Bc ^ (n - 1)) + δA * Y ^ n := hcore
    _ = M * Bc ^ (n - 1) + δA * Y ^ n := by ring

end Terms

/-! ## The theorems -/

section Theorems

/-- **Case 5 with a repeated sign** (`eq:double_sum_zero_tensor` via `nonalternating`), explicit
form,
`cPair1 k κ = (1 + cShortRow κ)(1 + 18 cProp5)^(2k-1)`. -/
theorem ugenPairCase1Explicit : UgenPairCase1Explicit cPair1 := by
  intro k _ hk L _ hL κ E hκ hE s t hs hst ht σ hσ K M δA hK hM hδ A hAM hdec a
  obtain ⟨i₀, hi₀⟩ := hσ
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hE2 : |E| ≤ 2 := by linarith
  have hlam : 1 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * K := by nlinarith
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hedge : ∀ j : Fin (k + k), ‖pairXi E σ j‖ ≤ 1 := by
    intro j
    induction j using Fin.addCases with
    | left i => simp only [pairXi, Fin.append_left]; exact (norm_edge_one hE2 _ _).le
    | right i => simp only [pairXi, Fin.append_right]; exact (norm_edge_one hE2 _ _).le
  have hcs : 0 ≤ cShortRow κ := by
    have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    unfold cShortRow
    refine mul_nonneg (div_nonneg ?_ hg) (sq_nonneg _)
    unfold cProp5; norm_num
  -- the anchor row: the short edge `i₀` of the first copy (`xiRowBoundShort`)
  have hanchor : ∑ c : Z2 L, ‖ukerMat L (pairXi E σ (Fin.castAdd k i₀)) s t
      (Fin.append a a (Fin.castAdd k i₀)) c‖ ≤ (1 + cShortRow κ) * (1 + Real.log L) := by
    have h0 := xiRowBoundShort L hL κ E hκ hE (σ i₀) s t hs hst ht (a i₀)
    have e1 : pairXi E σ (Fin.castAdd k i₀) = KLoop.mSig E (σ i₀) * KLoop.mSig E (σ i₀) := by
      simp only [pairXi, Fin.append_left]
      rw [← hi₀]
    rw [e1, Fin.append_left]
    have h1 := sum_norm_ukerMat_le (a i₀) h0
    nlinarith
  have hcore := KernelExpand_core_bound (L := L)
    (fun j c => ‖ukerMat L (pairXi E σ j) s t (Fin.append a a j) c‖)
    (fun j c => norm_nonneg _) (A := pairA A) (ρ := ellT L s * K) (M := M) (δA := δA)
    (r := (1 - s) / (1 - t)) (Rj := (1 + cShortRow κ) * (1 + Real.log L))
    (B := (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t) hM hδ
    (pairA_norm hAM) (pairA_decay hdec) (Fin.castAdd k i₀)
    (fun j => row_le hL (hedge j) hs hst ht (Fin.append a a j)) hanchor
    (fun j _ x => (ball_le hL (hedge j) hs hst ht (Fin.append a a j) x hρ0).trans
      (window_const hL hs hst ht hK))
  have hnorm : ‖UgenPair L E σ s t A a‖ ≤ ∑ c : Fin (k + k) → Z2 L,
      (∏ j, ‖ukerMat L (pairXi E σ j) s t (Fin.append a a j) (c j)‖) * ‖pairA A c‖ := by
    rw [ugenPair_eq]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_prod]
  have hkk1 : k + k - 1 = 2 * k - 1 := by omega
  rw [hkk1] at hcore
  have hYk : ((1 - s) / (1 - t)) ^ (k + k) = ((1 - s) / (1 - t)) ^ (2 * k) := by rw [two_mul]
  rw [hYk] at hcore
  refine hnorm.trans (hcore.trans ?_)
  unfold cPair1
  obtain ⟨m, hm⟩ : ∃ m, 2 * k - 1 = m := ⟨_, rfl⟩
  have h2k : 2 * k = m + 1 := by omega
  rw [hm, h2k]
  have hX : 0 ≤ (1 + cShortRow κ) * (1 + 18 * cProp5) ^ m * (1 + Real.log L) ^ (m + 1) *
      K ^ (2 * m) * M := by
    have : 0 ≤ cProp5 := by unfold cProp5; norm_num
    have : 0 ≤ 1 + Real.log L := by linarith
    positivity
  have hfirst : M * ((1 + cShortRow κ) * (1 + Real.log L) *
      ((1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t) ^ m) ≤
      (1 + cShortRow κ) * (1 + 18 * cProp5) ^ m * (1 + Real.log L) ^ (m + 1) *
        K ^ (2 * m) * rhoR L s t ^ (m + 1) * M := by
    have heq : M * ((1 + cShortRow κ) * (1 + Real.log L) *
        ((1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t) ^ m) =
        ((1 + cShortRow κ) * (1 + 18 * cProp5) ^ m * (1 + Real.log L) ^ (m + 1) *
          K ^ (2 * m) * M) * rhoR L s t ^ m := by
      rw [pow_mul]
      simp only [mul_pow]
      ring
    have heq2 : (1 + cShortRow κ) * (1 + 18 * cProp5) ^ m * (1 + Real.log L) ^ (m + 1) *
        K ^ (2 * m) * rhoR L s t ^ (m + 1) * M =
        ((1 + cShortRow κ) * (1 + 18 * cProp5) ^ m * (1 + Real.log L) ^ (m + 1) *
          K ^ (2 * m) * M) * rhoR L s t ^ (m + 1) := by ring
    rw [heq, heq2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.le_succ m)) hX
  have : δA * ((1 - s) / (1 - t)) ^ (m + 1) = ((1 - s) / (1 - t)) ^ (m + 1) * δA :=
    mul_comm _ _
  rw [this]
  linarith

/-- `2^n + 2^n ≤ 4^n` for `n ≥ 1`. -/
private theorem two_two_four {n : ℕ} (hn : 1 ≤ n) : (2 : ℝ) ^ n + 2 ^ n ≤ 4 ^ n := by
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]; norm_num
  have h2 : (2 : ℝ) ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
  have h0 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rw [h4]
  nlinarith

/-- **Case 5, alternating `σ`** (`eq:double_sum_zero_tensor`), explicit form,
`cCase5 k = (4 · 10⁶ (cProp5 + 8·10¹⁴ + 720))^(2k)`. -/
theorem ugenPairCase5AltExplicit : UgenPairCase5AltExplicit cCase5 := by
  intro k _ hk L _ hL E hE s t hs hst ht σ hσ K M δA hK hM hδ A hAM hdec hdsz a
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hlam := c5_lam_ge_one L
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hY1 : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hlL : 1 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hlam hL1
  have hX := case5X_ge_one
  have hn : 2 ≤ k + k := by omega
  have hAM2 := pairA_norm hAM
  have hdec2 := pairA_decay hdec
  set N0 := (1 + Real.log L) ^ (k + k + 1) * K ^ (2 * (k + k)) * rhoR L s t ^ (k + k) with hN0
  set Er := ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (k + k) * ((1 - s) / (1 - t)) ^ (k + k) with hEr
  set Bnd := M * (case5X ^ (k + k) * N0) + δA * (case5X ^ (k + k) * Er) with hBnd
  have hN00 : 0 ≤ N0 := by
    have : 0 ≤ 1 + Real.log L := by linarith
    have : 0 ≤ rhoR L s t := by linarith
    positivity
  have hEr0 : 0 ≤ Er := by
    have : 0 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := by linarith
    have : 0 ≤ (1 - s) / (1 - t) := by linarith
    positivity
  have hBnd0 : 0 ≤ Bnd := by
    have : 0 ≤ case5X ^ (k + k) := pow_nonneg (by linarith) _
    positivity
  -- every edge weight of both copies is `|m|² = 1`
  have hedge : ∀ j : Fin (k + k), pairXi E σ j = 1 := by
    intro j
    induction j using Fin.addCases with
    | left i => simp only [pairXi, Fin.append_left]; exact mSig_alt hE (hσ i)
    | right i =>
        simp only [pairXi, Fin.append_right]
        refine mSig_alt hE fun h => hσ i ?_
        simpa using h
  have hU : UgenPair L E σ s t A a = ∑ g : Fin (k + k) → Fin 2,
      ∑ c : Fin (k + k) → Z2 L,
        (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c := by
    rw [ugenPair_eq]
    simp only [hedge]
    have h1 : ∀ c : Fin (k + k) → Z2 L,
        (∏ i, ukerMat L 1 s t (Fin.append a a i) (c i)) * pairA A c =
        ∑ g : Fin (k + k) → Fin 2,
          (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c := by
      intro c
      rw [← sum_mul]
      congr 1
      calc ∏ i, ukerMat L 1 s t (Fin.append a a i) (c i)
          = ∏ i, ∑ p : Fin 2, dpiece L s t p (Fin.append a a i) (c i) := by
            refine prod_congr rfl fun i _ => ?_
            rw [Fin.sum_univ_two, KernelExpand_ukerMat_apply]
            change xiMat L 1 s t (Fin.append a a i) (c i) +
                (1 : Matrix (Z2 L) (Z2 L) ℂ) (Fin.append a a i) (c i) =
              (1 : Matrix (Z2 L) (Z2 L) ℂ) (Fin.append a a i) (c i) +
                xiMat L 1 s t (Fin.append a a i) (c i)
            ring
        _ = ∑ g : Fin (k + k) → Fin 2, ∏ l, dpiece L s t (g l) (Fin.append a a l) (c l) :=
            Case4_prod_sum_pieces _
    rw [sum_congr rfl fun c _ => h1 c, sum_comm]
  -- the terms with a `δ`
  have hTg : ∀ g : Fin (k + k) → Fin 2, g ≠ (fun _ => 1) →
      ‖∑ c : Fin (k + k) → Z2 L,
        (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c‖ ≤ Bnd := by
    intro g hg
    obtain ⟨j, hj⟩ : ∃ j, g j = 0 := by
      by_contra hcon
      push Not at hcon
      apply hg
      funext l
      have h01 : ∀ p : Fin 2, p ≠ 0 → p = 1 := by decide
      exact h01 (g l) (hcon l)
    refine (norm_T_le hL hs hst ht hK (Fin.append a a) g j hj hM hδ hAM2 hdec2).trans ?_
    have h1 := num_T hn hlam hK hR1
    have h2 := num_far_T (k := k + k) (by linarith : (0 : ℝ) ≤ (1 - s) / (1 - t)) hlL
    rw [hBnd, hN0, hEr, ← mul_pow]
    rw [← mul_pow] at h2
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hM) (mul_le_mul_of_nonneg_left h2 hδ)
  -- the all-`Ξ` term, piece by piece, around the common anchor `b₀`
  have hV : ∀ f : Fin (k + k) → Fin 2,
      ‖Vterm2 L s t (Fin.append a a) (pairA A) (Fin.castAdd k 0) f‖ ≤ Bnd := by
    intro f
    have h01 : ∀ p : Fin 2, p ≠ 0 → p = 1 := by decide
    by_cases hf0 : f (Fin.castAdd k 0) = 0
    swap
    · rw [V2_eq_zero_of_f0 s t _ _ _ f hf0, norm_zero]; exact hBnd0
    by_cases h1 : ∀ i : Fin k, f (Fin.castAdd k i) = 0
    · rw [V2_eq_zero_first s t _ A hdsz f h1, norm_zero]; exact hBnd0
    by_cases h2 : ∀ i : Fin k, f (Fin.natAdd k i) = 0
    · rw [V2_eq_zero_second s t _ A hdsz f h2, norm_zero]; exact hBnd0
    push Not at h1 h2
    obtain ⟨i, hi⟩ := h1
    obtain ⟨i', hi'⟩ := h2
    have hi0 : Fin.castAdd k i ≠ Fin.castAdd k 0 := by
      intro h; rw [h] at hi; exact hi hf0
    have hj0 : Fin.natAdd k i' ≠ Fin.castAdd k 0 := by
      intro h; rw [h] at hi'; exact hi' hf0
    exact bound_iv2 hn hL hs hst ht hK (Fin.append a a) (Fin.castAdd k 0) f hf0
      (Fin.castAdd k i) (Fin.natAdd k i') hi0 hj0 (castAdd_ne_natAdd i i') (h01 _ hi)
      (h01 _ hi') hM hδ hAM2 hdec2
  have hT1 : ‖∑ c : Fin (k + k) → Z2 L,
      (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (Fin.append a a l) (c l)) * pairA A c‖ ≤
      2 ^ (k + k) * Bnd := by
    have hexp : ∑ c : Fin (k + k) → Z2 L,
        (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (Fin.append a a l) (c l)) * pairA A c =
        ∑ f : Fin (k + k) → Fin 2,
          Vterm2 L s t (Fin.append a a) (pairA A) (Fin.castAdd k 0) f := by
      have h1 : ∀ c : Fin (k + k) → Z2 L,
          (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (Fin.append a a l) (c l)) *
            pairA A c =
          ∑ f : Fin (k + k) → Fin 2, (∏ l, piece2 L s t (Fin.append a a l)
            (c (Fin.castAdd k 0)) (c l) (f l)) * pairA A c := by
        intro c
        rw [← sum_mul]
        congr 1
        calc ∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (Fin.append a a l) (c l)
            = ∏ l, ∑ p : Fin 2, piece2 L s t (Fin.append a a l) (c (Fin.castAdd k 0)) (c l) p :=
              prod_congr rfl fun l _ =>
                (piece2_sum s t (Fin.append a a l) (c (Fin.castAdd k 0)) (c l)).symm
          _ = ∑ f : Fin (k + k) → Fin 2,
                ∏ l, piece2 L s t (Fin.append a a l) (c (Fin.castAdd k 0)) (c l) (f l) :=
              Case4_prod_sum_pieces _
      rw [sum_congr rfl fun c _ => h1 c, sum_comm]
      rfl
    rw [hexp]
    calc ‖∑ f : Fin (k + k) → Fin 2,
          Vterm2 L s t (Fin.append a a) (pairA A) (Fin.castAdd k 0) f‖
        ≤ ∑ f : Fin (k + k) → Fin 2,
            ‖Vterm2 L s t (Fin.append a a) (pairA A) (Fin.castAdd k 0) f‖ := norm_sum_le _ _
      _ ≤ ∑ _f : Fin (k + k) → Fin 2, Bnd := sum_le_sum fun f _ => hV f
      _ = 2 ^ (k + k) * Bnd := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  -- assembling
  have hcard : ((univ.erase (fun _ => (1 : Fin 2)) : Finset (Fin (k + k) → Fin 2)).card : ℝ) ≤
      2 ^ (k + k) := by
    have h := card_erase_le (s := (univ : Finset (Fin (k + k) → Fin 2))) (a := fun _ => 1)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact_mod_cast h
  have h224 := two_two_four (n := k + k) (by omega)
  rw [hU]
  calc ‖∑ g : Fin (k + k) → Fin 2, ∑ c : Fin (k + k) → Z2 L,
        (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c‖
      ≤ ∑ g : Fin (k + k) → Fin 2, ‖∑ c : Fin (k + k) → Z2 L,
          (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c‖ := norm_sum_le _ _
    _ = ‖∑ c : Fin (k + k) → Z2 L,
          (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (Fin.append a a l) (c l)) * pairA A c‖ +
        ∑ g ∈ univ.erase (fun _ => (1 : Fin 2)), ‖∑ c : Fin (k + k) → Z2 L,
          (∏ l, dpiece L s t (g l) (Fin.append a a l) (c l)) * pairA A c‖ :=
        (add_sum_erase _ _ (mem_univ _)).symm
    _ ≤ 2 ^ (k + k) * Bnd + ∑ _g ∈ univ.erase (fun _ => (1 : Fin 2)), Bnd :=
        add_le_add hT1 (sum_le_sum fun g hg => hTg g (ne_of_mem_erase hg))
    _ = 2 ^ (k + k) * Bnd +
          ((univ.erase (fun _ => (1 : Fin 2)) : Finset (Fin (k + k) → Fin 2)).card : ℝ) * Bnd := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (k + k) * Bnd + 2 ^ (k + k) * Bnd := by
        have := mul_le_mul_of_nonneg_right hcard hBnd0
        linarith
    _ ≤ 4 ^ (k + k) * Bnd := by
        have := mul_le_mul_of_nonneg_right h224 hBnd0
        linarith
    _ = cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * K ^ (4 * k) * rhoR L s t ^ (2 * k) * M +
          cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * ((1 - s) / (1 - t)) ^ (2 * k) *
            δA := by
        rw [cCase5_eq, hBnd, hN0, hEr, show 2 * k = k + k by ring,
          show 4 * k = 2 * (k + k) by ring]
        ring

end Theorems

end RBM.Evol

end
