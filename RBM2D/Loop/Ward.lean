/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Cyclic

/-!
# Ward's identity for `𝒦` (`(WI_calK)`)

The theorem `Kcal_ward`: for `σ₁ = +`, `σₙ = −`,
`∑_{aₙ} 𝒦_{t,σ,a} = (2 i W² η_t)⁻¹ (𝒦_{t,σ+,a/aₙ} − 𝒦_{t,σ−,a/aₙ})`
(`(WI_calK)` in Section 3 of the paper).

The proof follows the one-dimensional formalization (index bookkeeping, the derivative
identity, `Ward_kappa`, `Ward_kappa_mul`, `Ward_hasDerivAt_kappa`, `Ward_sum_allEq_append`,
`Ward_wD_primInit`, `Ward_level`, `Ward_of_isPrimitive`, `Ward_c`), with
`ZMod L → Z2 L`, `W → W²` in `primRhs` (so the Grönwall constant is `W² ∑ ⋯`),
`W⁻¹ → (W²)⁻¹` in `primInit`, `κ_t = (2 i W² η_t)⁻¹`, `c_t = (W² (1 − t))⁻¹`, and sums over
`Z_L²`.

* Level `2` (loops `(+,−)`) is `WI_calK_two` (in `Kcal.lean`).
* The cyclic invariance used in the cut `(k, n)` is `Kcal_rotate` (in `Cyclic.lean`).
* The `2`-loop bound needed by Grönwall is the compactness argument of
  `RBM2D/Loop/Cyclic.lean` (`Cyclic_two_loop_bound`), re-proved here with the prefix `Ward_`.

All helpers are `private` and prefixed `Ward_`.
-/

namespace RBM.KLoop

open Finset

/-! ## 1. Index bookkeeping -/

section Ind

variable {α : Type*}

/-- Move the first edge to the end. -/
private def Ward_rot (x : LoopIdx α) : LoopIdx α := ⟨x.σ.rotate 1, x.a.rotate 1⟩

private theorem Ward_rot_mk_cons (s : Bool) (ss : List Bool) (c : α) (cs : List α) :
    Ward_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α) = ⟨ss ++ [s], cs ++ [c]⟩ := by
  simp [Ward_rot, List.rotate_cons_succ]

private theorem Ward_two_le_length_cutGlueL (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

/-- `(+, μ, -; a', x)`: a loop with first charge `+` and last charge `-`. -/
private def Ward_fullLoop (μ : List Bool) (a' : List α) (x : α) : LoopIdx α :=
  ⟨true :: μ ++ [false], a' ++ [x]⟩

/-- `(s, μ; a')`: the loops `σ±` on the right-hand side of `(WI_calK)`. -/
private def Ward_pmLoop (s : Bool) (μ : List Bool) (a' : List α) : LoopIdx α := ⟨s :: μ, a'⟩

/-- The middle charges after cutting at `(k, l)`. -/
private def Ward_cutMu (k l : ℕ) (μ : List Bool) : List Bool := μ.take (k - 1) ++ μ.drop (l - 2)

/-- The labels (without the last) after cutting at `(k, l)` and gluing with `b`. -/
private def Ward_cutA (k l : ℕ) (b : α) (a' : List α) : List α :=
  a'.take (k - 1) ++ b :: a'.drop (l - 1)

variable (μ : List Bool) (a' : List α) (x b : α) {k l : ℕ}

private theorem Ward_cutGlueL_fullLoop (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (Ward_fullLoop μ a' x).cutGlueL k l b
      = Ward_fullLoop (Ward_cutMu k l μ) (Ward_cutA k l b a') x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [Ward_fullLoop, LoopIdx.cutGlueL, Ward_cutMu, Ward_cutA, Nat.add_sub_cancel,
    List.take_succ_cons, show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega,
    List.drop_succ_cons, List.cons_append, List.append_assoc]
  congr 1
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]

private theorem Ward_cutGlueL_pmLoop (s : Bool) (_hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (Ward_pmLoop s μ a').cutGlueL k l b
      = Ward_pmLoop s (Ward_cutMu k l μ) (Ward_cutA k l b a') := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [Ward_pmLoop, LoopIdx.cutGlueL, Ward_cutMu, Ward_cutA, Nat.add_sub_cancel,
    List.take_succ_cons, show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega,
    List.drop_succ_cons, List.cons_append]

private theorem Ward_cutGlueR_fullLoop (s : Bool) (hμ : μ.length + 1 = a'.length)
    (hk : 2 ≤ k) (hkl : k < l) (hl : l ≤ a'.length) :
    (Ward_fullLoop μ a' x).cutGlueR k l b = (Ward_pmLoop s μ a').cutGlueR k l b := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [Ward_fullLoop, Ward_pmLoop, LoopIdx.cutGlueR, show k + 2 - 1 = k + 1 by omega,
    List.drop_succ_cons, List.cons_append]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

private theorem Ward_cutGlueR_fullLoop_one (hμ : μ.length + 1 = a'.length) (hl1 : 1 < l)
    (hl : l ≤ a'.length) :
    (Ward_fullLoop μ a' x).cutGlueR 1 l b = (Ward_pmLoop true μ a').cutGlueR 1 l b := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [Ward_fullLoop, Ward_pmLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero,
    Nat.add_sub_cancel, List.take_succ_cons, List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega)]

private theorem Ward_cutGlueL_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkn : k ≤ a'.length) :
    (Ward_fullLoop μ a' x).cutGlueL k (a'.length + 1) b
      = Ward_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [b]) x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Ward_fullLoop, LoopIdx.cutGlueL, Nat.add_sub_cancel, List.take_succ_cons,
    List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega), ← hμ, List.drop_succ_cons, List.drop_left]
  · rw [List.take_append_of_le_length (by omega), List.drop_left]
    simp

private theorem Ward_cutGlueR_fullLoop_last_one (hμ : μ.length + 1 = a'.length) :
    (Ward_fullLoop μ a' x).cutGlueR 1 (a'.length + 1) b = Ward_fullLoop μ a' b := by
  simp only [Ward_fullLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel]
  congr 1
  · rw [List.take_of_length_le (by simp; omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length]

/-- The right chain of the cut `(k, n)`, `k ≥ 2`, is the rotation of the left chain of
`pmLoop -` at `(1, k)`. -/
private theorem Ward_cutGlueR_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 2 ≤ k)
    (hkn : k ≤ a'.length) :
    (Ward_fullLoop μ a' x).cutGlueR k (a'.length + 1) b
      = Ward_rot ((Ward_pmLoop false μ a').cutGlueL 1 k b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [Ward_fullLoop, Ward_pmLoop, LoopIdx.cutGlueR, LoopIdx.cutGlueL,
    show k + 2 - 1 = k + 1 by omega, List.drop_succ_cons, List.cons_append, Nat.sub_self,
    List.take_zero, List.nil_append, List.take_succ_cons, List.take_zero]
  rw [Ward_rot_mk_cons]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]

/-- The right chain never contains the last label `x`. -/
private theorem Ward_cutGlueR_fullLoop_indep (y : α) (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ a'.length + 1) :
    (Ward_fullLoop μ a' x).cutGlueR k l b = (Ward_fullLoop μ a' y).cutGlueR k l b := by
  simp only [Ward_fullLoop, LoopIdx.cutGlueR]
  congr 1
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]

/-- The right chain of `pmLoop s` at `(1, m)` is `pmLoop s` of the base of the left chain of
`fullLoop` at `(m, n)`. -/
private theorem Ward_cutGlueR_pmLoop_one (s : Bool) (hm : 1 < l) :
    (Ward_pmLoop s μ a').cutGlueR 1 l b
      = Ward_pmLoop s (μ.take (l - 1)) (a'.take (l - 1) ++ [b]) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [Ward_pmLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel,
    List.take_succ_cons]

end Ind

/-! ## 2. The derivative identity -/

section Step

variable (L : ℕ) [NeZero L]

/-- `∑_x K_{(+,μ,-),(a',x)}`: the left-hand side of `(WI_calK)`. -/
private noncomputable def Ward_wStar (K : LoopIdx (Z2 L) → ℂ) (μ : List Bool)
    (a' : List (Z2 L)) : ℂ :=
  ∑ x : Z2 L, K (Ward_fullLoop μ a' x)

/-- The difference of the two sides of `(WI_calK)`, with `κ = (2 i W² η_t)⁻¹`. -/
private noncomputable def Ward_wD (K : LoopIdx (Z2 L) → ℂ) (κ : ℂ) (μ : List Bool)
    (a' : List (Z2 L)) : ℂ :=
  Ward_wStar L K μ a' - κ * (K (Ward_pmLoop true μ a') - K (Ward_pmLoop false μ a'))

/-- The `x`-summed right-hand side of `(pro_dyncalK)` at `fullLoop μ a' x`, split into the
cuts with `l ≤ N` and the cuts `(k, N + 1)`. -/
private theorem Ward_sum_primRhs_fullLoop (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (μ : List Bool)
    (a' : List (Z2 L)) :
    ∑ x : Z2 L, primRhs L W K (Ward_fullLoop μ a' x) = (W : ℂ) ^ 2 *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : Z2 L, ∑ b : Z2 L,
          (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
            K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : Z2 L, ∑ b : Z2 L,
          (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB L a b *
            K ((Ward_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
  have hlen : ∀ x : Z2 L, (Ward_fullLoop μ a' x).length = a'.length + 1 := fun x => by
    simp [Ward_fullLoop, LoopIdx.length]
  have hR : ∀ x : Z2 L, ∀ k l, 1 ≤ k → k < l → l ≤ a'.length + 1 → ∀ b : Z2 L,
      (Ward_fullLoop μ a' x).cutGlueR k l b = (Ward_fullLoop μ a' 0).cutGlueR k l b :=
    fun x k l hk hkl hl b => Ward_cutGlueR_fullLoop_indep μ a' x b 0 hk hkl hl
  have hsplit : ∀ x : Z2 L, primRhs L W K (Ward_fullLoop μ a' x) = (W : ℂ) ^ 2 *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : Z2 L, ∑ b : Z2 L,
          K ((Ward_fullLoop μ a' x).cutGlueL k l a) * SB L a b *
            K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : Z2 L, ∑ b : Z2 L,
          K ((Ward_fullLoop μ a' x).cutGlueL k (a'.length + 1) a) * SB L a b *
            K ((Ward_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
    intro x
    rw [primRhs, hlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero,
      ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k l hk.1 hl.1 (by omega) b]
    · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k (a'.length + 1) hk.1 (by omega) le_rfl b]
  simp only [hsplit, ← Finset.mul_sum, sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]

section Cuts

variable (K : LoopIdx (Z2 L) → ℂ) (κ : ℂ) (μ : List Bool) (a' : List (Z2 L))

private theorem Ward_wStar_eq (μ' : List Bool) (a'' : List (Z2 L)) :
    Ward_wStar L K μ' a'' = Ward_wD L K κ μ' a''
      + κ * (K (Ward_pmLoop true μ' a'') - K (Ward_pmLoop false μ' a'')) := by
  rw [Ward_wD]
  ring

/-- **W1**: a cut `(k, l)` with `l ≤ N`. -/
private theorem Ward_cut_inner (hμ : μ.length + 1 = a'.length) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) (a b : Z2 L) :
    (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
        K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
      - κ * (K ((Ward_pmLoop true μ a').cutGlueL k l a) * SB L a b *
            K ((Ward_pmLoop true μ a').cutGlueR k l b)
          - K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
            K ((Ward_pmLoop false μ a').cutGlueR k l b))
      = Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
          K ((Ward_pmLoop true μ a').cutGlueR k l b)
        + κ * K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
          (K ((Ward_pmLoop false μ a').cutGlueR k l b)
            - K ((Ward_pmLoop true μ a').cutGlueR k l b)) := by
  have hL : ∀ x, (Ward_fullLoop μ a' x).cutGlueL k l a
      = Ward_fullLoop (Ward_cutMu k l μ) (Ward_cutA k l a a') x :=
    fun x => Ward_cutGlueL_fullLoop μ a' x a hμ hk hkl hl
  have hR : (Ward_fullLoop μ a' 0).cutGlueR k l b = (Ward_pmLoop true μ a').cutGlueR k l b := by
    rcases hk.lt_or_eq with hk2 | rfl
    · exact Ward_cutGlueR_fullLoop μ a' 0 b true hμ hk2 hkl hl
    · exact Ward_cutGlueR_fullLoop_one μ a' 0 b hμ hkl hl
  simp only [hL, hR, Ward_cutGlueL_pmLoop μ a' a true hμ hk hkl hl,
    Ward_cutGlueL_pmLoop μ a' a false hμ hk hkl hl]
  rw [show ∑ x : Z2 L, K (Ward_fullLoop (Ward_cutMu k l μ) (Ward_cutA k l a a') x)
      = Ward_wStar L K (Ward_cutMu k l μ) (Ward_cutA k l a a') from rfl, Ward_wStar_eq L K κ]
  ring

omit [NeZero L] in
/-- For `k ≥ 2` the remainder of W1 vanishes: the right chain does not see the first
charge. -/
private theorem Ward_cutGlueR_pmLoop_indep (hμ : μ.length + 1 = a'.length) {k l : ℕ}
    (hk : 2 ≤ k) (hkl : k < l) (hl : l ≤ a'.length) (b : Z2 L) :
    (Ward_pmLoop false μ a').cutGlueR k l b = (Ward_pmLoop true μ a').cutGlueR k l b := by
  rw [← Ward_cutGlueR_fullLoop μ a' (0 : Z2 L) b false hμ hk hkl hl,
    Ward_cutGlueR_fullLoop μ a' (0 : Z2 L) b true hμ hk hkl hl]

/-- **W2**: a cut `(k, N + 1)` with `2 ≤ k ≤ N`; uses cyclic invariance. -/
private theorem Ward_cut_last (hμ : μ.length + 1 = a'.length) {k : ℕ} (hk : 2 ≤ k)
    (hkN : k ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → K (Ward_rot J) = K J) (a b : Z2 L) :
    (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB L a b *
        K ((Ward_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)
      = (Ward_wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a])
          + κ * (K ((Ward_pmLoop true μ a').cutGlueR 1 k a)
            - K ((Ward_pmLoop false μ a').cutGlueR 1 k a))) * SB L a b *
          K ((Ward_pmLoop false μ a').cutGlueL 1 k b) := by
  have hL : ∀ x, (Ward_fullLoop μ a' x).cutGlueL k (a'.length + 1) a
      = Ward_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x :=
    fun x => Ward_cutGlueL_fullLoop_last μ a' x a hμ (by omega) hkN
  have hWF : ((Ward_pmLoop false μ a').cutGlueL 1 k b).WF := by
    refine LoopIdx.WF.cutGlueL ?_ b le_rfl (by omega) ?_
    · simp [LoopIdx.WF, Ward_pmLoop, hμ]
    · simp [LoopIdx.length, Ward_pmLoop]; omega
  have hlen : 2 ≤ ((Ward_pmLoop false μ a').cutGlueL 1 k b).length := by
    refine Ward_two_le_length_cutGlueL _ b le_rfl (by omega) ?_
    simp [LoopIdx.length, Ward_pmLoop]; omega
  simp only [hL, Ward_cutGlueR_fullLoop_last μ a' 0 b hμ hk hkN, hcyc _ hWF hlen,
    Ward_cutGlueR_pmLoop_one μ a' a true (by omega : 1 < k),
    Ward_cutGlueR_pmLoop_one μ a' a false (by omega : 1 < k)]
  rw [show ∑ x : Z2 L, K (Ward_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x)
      = Ward_wStar L K (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) from rfl, Ward_wStar_eq L K κ]

/-- **W3**: the cut `(1, N + 1)`; the column sums of `S^(B)` are `1`. -/
private theorem Ward_cut_one_last (hL : 3 ≤ L) (hμ : μ.length + 1 = a'.length) (c : ℂ)
    (h2 : ∀ a : Z2 L, Ward_wStar L K [] [a] = c) :
    ∑ a : Z2 L, ∑ b : Z2 L,
        (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a)) * SB L a b *
          K ((Ward_fullLoop μ a' 0).cutGlueR 1 (a'.length + 1) b)
      = c * Ward_wStar L K μ a' := by
  have hL1 : ∀ x a, (Ward_fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a
      = Ward_fullLoop [] [a] x := by
    intro x a
    rw [Ward_cutGlueL_fullLoop_last μ a' x a hμ le_rfl (by omega)]
    simp
  simp only [hL1, Ward_cutGlueR_fullLoop_last_one μ a' 0 _ hμ]
  simp only [show ∀ a, ∑ x : Z2 L, K (Ward_fullLoop [] [a] x) = Ward_wStar L K [] [a]
    from fun _ => rfl, h2]
  rw [Finset.sum_comm, Ward_wStar, Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcol : ∑ a : Z2 L, SB L a b = 1 := by
    rw [← sum_SB_row L hL b]
    exact sum_congr rfl fun a _ => congrFun (congrFun (SB_transpose L) b) a
  rw [hcol, mul_one]

/-- A double sum over `1 ≤ k < l ≤ N` of a function vanishing unless `l = k + 1`. -/
private theorem Ward_sum_Icc_Ioc_adjacent {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℕ → ℕ → M) (hf : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, k + 1 < l → f k l = 0) :
    ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, f k l = ∑ k ∈ Icc 1 (N - 1), f k (k + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [mem_Ioc]; omega)]
  intro l hl hne
  refine hf k (by rw [mem_Icc]; omega) l hl ?_
  rw [mem_Ioc] at hl
  omega

/-- **The right-hand side of the derivative of `(WI_calK)`**, at a fixed time. -/
private theorem Ward_rhs_identity (hL : 3 ≤ L) (W : ℕ) (c : ℂ)
    (hμ : μ.length + 1 = a'.length) (hN : 2 ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → K (Ward_rot J) = K J)
    (h2 : ∀ a : Z2 L, Ward_wStar L K [] [a] = c)
    (hlow : ∀ (μ'' : List Bool) (a'' : List (Z2 L)), μ''.length + 1 = a''.length →
      a''.length < a'.length → Ward_wD L K κ μ'' a'' = 0) :
    ∑ x : Z2 L, primRhs L W K (Ward_fullLoop μ a' x)
      - κ * (primRhs L W K (Ward_pmLoop true μ a') - primRhs L W K (Ward_pmLoop false μ a'))
      = (W : ℂ) ^ 2 *
        (∑ k ∈ Icc 1 (a'.length - 1), ∑ a : Z2 L, ∑ b : Z2 L,
            Ward_wD L K κ (Ward_cutMu k (k + 1) μ) (Ward_cutA k (k + 1) a a') * SB L a b *
              K ((Ward_pmLoop true μ a').cutGlueR k (k + 1) b)
          + ∑ a : Z2 L, ∑ b : Z2 L,
            Ward_wD L K κ (μ.take (a'.length - 1)) (a'.take (a'.length - 1) ++ [a])
              * SB L a b * K ((Ward_pmLoop false μ a').cutGlueL 1 a'.length b)
          + c * Ward_wStar L K μ a') := by
  set N := a'.length with hNdef
  have hpmlen : ∀ s, (Ward_pmLoop s μ a').length = N := fun s => by
    simp [LoopIdx.length, Ward_pmLoop, hNdef]
  have hpm : ∀ s, primRhs L W K (Ward_pmLoop s μ a') = (W : ℂ) ^ 2 *
      ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
        K ((Ward_pmLoop s μ a').cutGlueL k l a) * SB L a b *
          K ((Ward_pmLoop s μ a').cutGlueR k l b) :=
    fun s => by rw [primRhs, hpmlen]
  rw [Ward_sum_primRhs_fullLoop L W K μ a', hpm, hpm]
  -- (i) the cuts with `l ≤ N`
  have hA : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a b : Z2 L,
      (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
          K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
        - κ * (K ((Ward_pmLoop true μ a').cutGlueL k l a) * SB L a b *
              K ((Ward_pmLoop true μ a').cutGlueR k l b)
            - K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
              K ((Ward_pmLoop false μ a').cutGlueR k l b))
        = Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
            K ((Ward_pmLoop true μ a').cutGlueR k l b)
          + (if k = 1 then κ * K ((Ward_pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
              (K ((Ward_pmLoop false μ a').cutGlueR 1 l b)
                - K ((Ward_pmLoop true μ a').cutGlueR 1 l b)) else 0) := by
    intro k hk l hl a b
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    rw [Ward_cut_inner L K κ μ a' hμ hk.1 hl.1 hl.2]
    split_ifs with h1
    · subst h1
      rfl
    · rw [Ward_cutGlueR_pmLoop_indep L μ a' hμ (by omega) hl.1 hl.2, sub_self, mul_zero]
  -- (ii) the cuts `(k, N + 1)`
  have hB : ∀ k ∈ Icc 2 N, ∀ a b : Z2 L,
      (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB L a b *
          K ((Ward_fullLoop μ a' 0).cutGlueR k (N + 1) b)
        = Ward_wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
            K ((Ward_pmLoop false μ a').cutGlueL 1 k b)
          + κ * (K ((Ward_pmLoop true μ a').cutGlueR 1 k a)
              - K ((Ward_pmLoop false μ a').cutGlueR 1 k a))
            * SB L a b * K ((Ward_pmLoop false μ a').cutGlueL 1 k b) := by
    intro k hk a b
    rw [mem_Icc] at hk
    rw [Ward_cut_last L K κ μ a' hμ hk.1 hk.2 hcyc]
    ring
  have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  have hcutlen : ∀ k l, 1 ≤ k → k < l → l ≤ N → ∀ a : Z2 L,
      (Ward_cutMu k l μ).length + 1 = (Ward_cutA k l a a').length ∧
        (Ward_cutA k l a a').length = N + k - l + 1 := by
    intro k l hk hkl hl a
    simp only [Ward_cutMu, Ward_cutA, List.length_append, List.length_take, List.length_drop,
      List.length_cons]
    omega
  have hT1 : ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
      Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
        K ((Ward_pmLoop true μ a').cutGlueR k l b)
      = ∑ k ∈ Icc 1 (N - 1), ∑ a : Z2 L, ∑ b : Z2 L,
          Ward_wD L K κ (Ward_cutMu k (k + 1) μ) (Ward_cutA k (k + 1) a a') * SB L a b *
            K ((Ward_pmLoop true μ a').cutGlueR k (k + 1) b) := by
    refine Ward_sum_Icc_Ioc_adjacent N (fun k l => ∑ a : Z2 L, ∑ b : Z2 L,
      Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
        K ((Ward_pmLoop true μ a').cutGlueR k l b)) ?_
    intro k hk l hl hkl
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    obtain ⟨h1, h2⟩ := hcutlen k l hk.1 hl.1 hl.2 a
    rw [hlow _ _ h1 (by omega), zero_mul, zero_mul]
  have hU2 : ∑ k ∈ Icc 2 N, ∑ a : Z2 L, ∑ b : Z2 L,
      Ward_wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
        K ((Ward_pmLoop false μ a').cutGlueL 1 k b)
      = ∑ a : Z2 L, ∑ b : Z2 L,
          Ward_wD L K κ (μ.take (N - 1)) (a'.take (N - 1) ++ [a]) * SB L a b *
            K ((Ward_pmLoop false μ a').cutGlueL 1 N b) := by
    rw [Finset.sum_eq_single_of_mem N (by rw [mem_Icc]; omega)]
    intro k hk hkN
    rw [mem_Icc] at hk
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [hlow _ _ (by simp only [List.length_take, List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_take, List.length_singleton]; omega),
      zero_mul, zero_mul]
  have hcancel : (∑ l ∈ Ioc 1 N, ∑ a : Z2 L, ∑ b : Z2 L,
        κ * K ((Ward_pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
          (K ((Ward_pmLoop false μ a').cutGlueR 1 l b)
            - K ((Ward_pmLoop true μ a').cutGlueR 1 l b)))
      + ∑ k ∈ Icc 2 N, ∑ a : Z2 L, ∑ b : Z2 L,
        κ * (K ((Ward_pmLoop true μ a').cutGlueR 1 k a)
            - K ((Ward_pmLoop false μ a').cutGlueR 1 k a))
          * SB L a b * K ((Ward_pmLoop false μ a').cutGlueL 1 k b) = 0 := by
    rw [hIoc, ← sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.sum_comm (s := (univ : Finset (Z2 L))) (t := (univ : Finset (Z2 L)))
      (f := fun a b => κ * (K ((Ward_pmLoop true μ a').cutGlueR 1 k a)
        - K ((Ward_pmLoop false μ a').cutGlueR 1 k a)) * SB L a b *
          K ((Ward_pmLoop false μ a').cutGlueL 1 k b)), ← sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
    ring
  simp only [← hNdef]
  -- the Ward-bracket part
  have eA : (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
        (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
          K ((Ward_fullLoop μ a' 0).cutGlueR k l b))
      - κ * ((∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
          K ((Ward_pmLoop true μ a').cutGlueL k l a) * SB L a b *
            K ((Ward_pmLoop true μ a').cutGlueR k l b))
        - ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
          K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
            K ((Ward_pmLoop false μ a').cutGlueR k l b))
      = (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
          Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
            K ((Ward_pmLoop true μ a').cutGlueR k l b))
        + ∑ l ∈ Ioc 1 N, ∑ a : Z2 L, ∑ b : Z2 L,
          κ * K ((Ward_pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
            (K ((Ward_pmLoop false μ a').cutGlueR 1 l b)
              - K ((Ward_pmLoop true μ a').cutGlueR 1 l b)) := by
    have e1 : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a : Z2 L,
        ∑ b : Z2 L, ((∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
            K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
          - κ * (K ((Ward_pmLoop true μ a').cutGlueL k l a) * SB L a b *
                K ((Ward_pmLoop true μ a').cutGlueR k l b)
              - K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
                K ((Ward_pmLoop false μ a').cutGlueR k l b)))
        = ∑ b : Z2 L, (Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
              K ((Ward_pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((Ward_pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
                (K ((Ward_pmLoop false μ a').cutGlueR 1 l b)
                  - K ((Ward_pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
      fun k hk l hl a => sum_congr rfl fun b _ => hA k hk l hl a b
    calc _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
          ((∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
              K ((Ward_fullLoop μ a' 0).cutGlueR k l b)
            - κ * (K ((Ward_pmLoop true μ a').cutGlueL k l a) * SB L a b *
                  K ((Ward_pmLoop true μ a').cutGlueR k l b)
                - K ((Ward_pmLoop false μ a').cutGlueL k l a) * SB L a b *
                  K ((Ward_pmLoop false μ a').cutGlueR k l b))) := by
          simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Z2 L, ∑ b : Z2 L,
          (Ward_wD L K κ (Ward_cutMu k l μ) (Ward_cutA k l a a') * SB L a b *
              K ((Ward_pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((Ward_pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
                (K ((Ward_pmLoop false μ a').cutGlueR 1 l b)
                  - K ((Ward_pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
          sum_congr rfl fun k hk => sum_congr rfl fun l hl => sum_congr rfl fun a _ =>
            e1 k hk l hl a
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          congr 1
          rw [hIcc, sum_insert (by simp)]
          simp only [ite_true]
          rw [Finset.sum_eq_zero (s := Icc 2 N) fun k hk => ?_, add_zero]
          rw [mem_Icc] at hk
          simp only [show k ≠ 1 by omega, ite_false, Finset.sum_const_zero]
  -- the cuts `(k, N + 1)`
  have eB : (∑ k ∈ Icc 1 N, ∑ a : Z2 L, ∑ b : Z2 L,
        (∑ x : Z2 L, K ((Ward_fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB L a b *
          K ((Ward_fullLoop μ a' 0).cutGlueR k (N + 1) b))
      = c * Ward_wStar L K μ a'
        + (∑ k ∈ Icc 2 N, ∑ a : Z2 L, ∑ b : Z2 L,
            Ward_wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
              K ((Ward_pmLoop false μ a').cutGlueL 1 k b))
        + ∑ k ∈ Icc 2 N, ∑ a : Z2 L, ∑ b : Z2 L,
            κ * (K ((Ward_pmLoop true μ a').cutGlueR 1 k a)
                - K ((Ward_pmLoop false μ a').cutGlueR 1 k a))
              * SB L a b * K ((Ward_pmLoop false μ a').cutGlueL 1 k b) := by
    rw [hIcc, sum_insert (by simp), hNdef, Ward_cut_one_last L K μ a' hL hμ c h2, ← hNdef,
      add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => hB k hk a b
  rw [show ∀ A B P P' : ℂ, (W : ℂ) ^ 2 * (A + B) - κ * ((W : ℂ) ^ 2 * P - (W : ℂ) ^ 2 * P')
      = (W : ℂ) ^ 2 * ((A - κ * (P - P')) + B) from fun A B P P' => by ring, eA, eB, hT1, hU2]
  rw [show ∀ T1 T2 cw U2 U3 : ℂ, T1 + T2 + (cw + U2 + U3) = T1 + U2 + cw + (T2 + U3)
      from fun T1 T2 cw U2 U3 => by ring, hcancel, add_zero]

end Cuts

end Step

/-! ## 3. `κ_t`, `c_t` and the initial value -/

section Kappa

variable {E : ℝ}

/-- `κ_t = (2 i W² η_t)⁻¹`, the coefficient of `(WI_calK)`. -/
private noncomputable def Ward_kappa (W : ℕ) (E t : ℝ) : ℂ :=
  (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹

/-- `c_t = (W² (1 − t))⁻¹`, the common value of the two sides at `n = 2`. -/
private noncomputable def Ward_c (W : ℕ) (t : ℝ) : ℂ := ((W : ℂ) ^ 2 * (1 - t))⁻¹

/-- `η_t = (1 − t) Im m^{(E)}`. -/
private theorem Ward_etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem Ward_mSig_mul (hE : |E| ≤ 2) : mSig E true * mSig E false = 1 := by
  simp only [mSig, ↓reduceIte, Bool.false_eq_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
  simp

/-- `κ_t (m − m̄) = c_t`. -/
private theorem Ward_kappa_mul (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    Ward_kappa W E t * (mSig E true - mSig E false) = Ward_c W t := by
  have him : ((Gauss.spectralM E).im : ℂ) ≠ 0 := by
    exact_mod_cast (Gauss.spectralM_im_pos hE).ne'
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  simp only [Ward_kappa, Ward_c, mSig, ↓reduceIte, Bool.false_eq_true, Complex.sub_conj,
    Ward_etaT_eq]
  push_cast
  field_simp

/-- `∂_t κ_t = κ_t / (1 − t)`. -/
private theorem Ward_hasDerivAt_kappa (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2) {t : ℝ}
    (ht1 : t < 1) : HasDerivAt (Ward_kappa W E) (Ward_kappa W E t / (1 - t)) t := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hIm : ((Gauss.spectralM E).im : ℂ) ≠ 0 := by
    exact_mod_cast (Gauss.spectralM_im_pos hE).ne'
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  have hg : HasDerivAt (fun s : ℝ => 2 * Complex.I * (W : ℂ) ^ 2 * (etaT E s : ℂ))
      (-(2 * Complex.I * (W : ℂ) ^ 2 * (Gauss.spectralM E).im)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (etaT E s : ℂ)) (-((Gauss.spectralM E).im : ℂ)) t := by
      have := (((hasDerivAt_id t).const_sub 1).mul_const (Gauss.spectralM E).im).ofReal_comp
      simpa [Ward_etaT_eq] using this
    exact (h1.const_mul (2 * Complex.I * (W : ℂ) ^ 2)).congr_deriv (by ring)
  have hne : 2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ) ≠ 0 := by
    rw [Ward_etaT_eq]
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (pow_ne_zero 2 hW0)) (mul_ne_zero ht hIm)
  refine (hg.inv hne).congr_deriv ?_
  simp only [Ward_kappa, Ward_etaT_eq]
  push_cast
  field_simp

end Kappa

section Init

variable (L : ℕ) [NeZero L]

/-- Summing the "all labels equal" indicator over the last label. -/
private theorem Ward_sum_allEq_append (a' : List (Z2 L)) (ha : a' ≠ []) :
    ∑ x : Z2 L, (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then (1 : ℂ) else 0)
      = if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0 := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil ha
  have hh : h ∈ h :: t := List.mem_cons_self
  by_cases hall : ∀ y ∈ h :: t, ∀ z ∈ h :: t, y = z
  · rw [ite_eq_left hall]
    have key : ∀ x : Z2 L,
        (∀ y ∈ h :: t ++ [x], ∀ z ∈ h :: t ++ [x], y = z) ↔ x = h := by
      intro x
      constructor
      · intro hx
        exact hx x (List.mem_append_right _ (List.mem_singleton_self x)) h
          (List.mem_append_left _ hh)
      · intro hxh
        have hin : ∀ w ∈ h :: t ++ [x], w ∈ h :: t := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hw
          · rw [List.mem_singleton.mp hw, hxh]
            exact hh
        exact fun y hy z hz => hall y (hin y hy) z (hin z hz)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [ite_eq_right hall]
    refine Finset.sum_eq_zero fun x _ => ite_eq_right fun hx => hall fun y hy z hz =>
      hx y (List.mem_append_left _ hy) z (List.mem_append_left _ hz)

/-- **The initial value.**  At `t = 0`, `(WI_calK)` holds for the initial value `primInit`. -/
private theorem Ward_wD_primInit (W : ℕ) (hW : W ≠ 0) {E : ℝ} (hE : |E| < 2) (μ : List Bool)
    (a' : List (Z2 L)) (hμ : μ.length + 1 = a'.length) :
    Ward_wD L (primInit L W (mSig E)) (Ward_kappa W E 0) μ a' = 0 := by
  have ha : a' ≠ [] := by
    intro h
    rw [h] at hμ
    simp at hμ
  obtain ⟨N, hN⟩ : ∃ N, a'.length = N + 1 := ⟨a'.length - 1, by omega⟩
  have hfull : ∀ x : Z2 L, primInit L W (mSig E) (Ward_fullLoop μ a' x)
      = ((W : ℂ) ^ 2)⁻¹ ^ (N + 1) * (mSig E true * (μ.map (mSig E)).prod * mSig E false) *
        (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then 1 else 0) := by
    intro x
    simp only [primInit, Ward_fullLoop, LoopIdx.length, List.length_append,
      List.length_singleton, hN, Nat.add_sub_cancel, List.map_cons, List.map_append,
      List.map_nil, List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc]
    rfl
  have hpm : ∀ s, primInit L W (mSig E) (Ward_pmLoop s μ a')
      = ((W : ℂ) ^ 2)⁻¹ ^ N * (mSig E s * (μ.map (mSig E)).prod) *
        (if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0) := by
    intro s
    simp only [primInit, Ward_pmLoop, LoopIdx.length, hN, Nat.add_sub_cancel, List.map_cons,
      List.prod_cons]
    rfl
  have hk := Ward_kappa_mul W hW hE (t := 0) (by norm_num)
  have hc0 : Ward_c W 0 = ((W : ℂ) ^ 2)⁻¹ := by simp [Ward_c]
  have hmm : mSig E true * mSig E false = 1 := Ward_mSig_mul hE.le
  simp only [Ward_wD, Ward_wStar, hfull, hpm, ← Finset.mul_sum, Ward_sum_allEq_append L a' ha]
  set P := (μ.map (mSig E)).prod
  set I := (if ∀ y ∈ a', ∀ z ∈ a', y = z then (1 : ℂ) else 0)
  calc ((W : ℂ) ^ 2)⁻¹ ^ (N + 1) * (mSig E true * P * mSig E false) * I
        - Ward_kappa W E 0 * (((W : ℂ) ^ 2)⁻¹ ^ N * (mSig E true * P) * I
          - ((W : ℂ) ^ 2)⁻¹ ^ N * (mSig E false * P) * I)
      = ((W : ℂ) ^ 2)⁻¹ ^ N * P * I * (((W : ℂ) ^ 2)⁻¹ * (mSig E true * mSig E false)
          - Ward_kappa W E 0 * (mSig E true - mSig E false)) := by ring
    _ = 0 := by rw [hmm, hk, hc0, mul_one, sub_self, mul_zero]

end Init

/-! ## 4. Grönwall and induction on the length -/

section Level

variable (L : ℕ) [NeZero L] {E : ℝ}

private theorem Ward_cutMu_adjacent (μ : List Bool) (k : ℕ) : Ward_cutMu k (k + 1) μ = μ := by
  simp only [Ward_cutMu, show k + 1 - 2 = k - 1 by omega, List.take_append_drop]

omit [NeZero L] in
private theorem Ward_length_cutA_adjacent (a' : List (Z2 L)) (a : Z2 L) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ a'.length) : (Ward_cutA k (k + 1) a a').length = a'.length := by
  simp only [Ward_cutA, List.length_append, List.length_take, List.length_cons,
    List.length_drop, Nat.add_sub_cancel]
  omega

private theorem Ward_norm_SB_apply_le (hL : 3 ≤ L) (a b : Z2 L) : ‖SB L a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB L a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row L hL a] at h
  exact_mod_cast h

/-- The index set of the level-`N` Ward defects: middle charges and labels. -/
private abbrev Ward_Vec (N : ℕ) := List.Vector Bool (N - 1) × List.Vector (Z2 L) N

/-- **One level of the induction** (loops of length `N + 1 ≥ 3`). -/
private theorem Ward_level (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)
    (K : ℝ → LoopIdx (Z2 L) → ℂ) (T₀ R : ℝ) (N : ℕ) (hN : 2 ≤ N) (hT₀ : T₀ < 1)
    (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => K s J) (primRhs L W (K t) J) t)
    (hcyc : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length →
      K t (Ward_rot J) = K t J)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Z2 L), J.WF → J.length = 2 → ‖K t J‖ ≤ R)
    (h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Z2 L, Ward_wStar L (K t) [] [a] = Ward_c W t)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Z2 L)),
      μ.length + 1 = a'.length → a'.length < N → Ward_wD L (K t) (Ward_kappa W E t) μ a' = 0)
    (h0 : ∀ (μ : List Bool) (a' : List (Z2 L)), μ.length + 1 = a'.length → a'.length = N →
      Ward_wD L (K 0) (Ward_kappa W E 0) μ a' = 0) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Z2 L)), μ.length + 1 = a'.length →
      a'.length = N → Ward_wD L (K t) (Ward_kappa W E t) μ a' = 0 := by
  let κ := Ward_kappa W E
  let D : ℝ → Ward_Vec L N → ℂ := fun t p => Ward_wD L (K t) (κ t) p.1.1 p.2.1
  have hp : ∀ p : Ward_Vec L N, p.1.1.length + 1 = p.2.1.length := fun p => by
    rw [p.1.2, p.2.2]
    omega
  have hpN : ∀ p : Ward_Vec L N, p.2.1.length = N := fun p => p.2.2
  let T : ℝ → Ward_Vec L N → ℂ := fun t p =>
    (∑ k ∈ Icc 1 (N - 1), ∑ a : Z2 L, ∑ b : Z2 L,
        Ward_wD L (K t) (κ t) (Ward_cutMu k (k + 1) p.1.1) (Ward_cutA k (k + 1) a p.2.1)
          * SB L a b * K t ((Ward_pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b))
      + ∑ a : Z2 L, ∑ b : Z2 L,
        Ward_wD L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB L a b *
          K t ((Ward_pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)
  let D' : ℝ → Ward_Vec L N → ℂ := fun t p =>
    (W : ℂ) ^ 2 * T t p + (1 - (t : ℂ))⁻¹ * D t p
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hfullWF : ∀ (μ : List Bool) (a' : List (Z2 L)) (x : Z2 L),
      μ.length + 1 = a'.length →
        (Ward_fullLoop μ a' x).WF ∧ (Ward_fullLoop μ a' x).length = a'.length + 1 :=
    fun μ a' x h => ⟨by simp [LoopIdx.WF, Ward_fullLoop]; omega,
      by simp [LoopIdx.length, Ward_fullLoop]⟩
  have hpmWF : ∀ (s : Bool) (μ : List Bool) (a' : List (Z2 L)),
      μ.length + 1 = a'.length →
        (Ward_pmLoop s μ a').WF ∧ (Ward_pmLoop s μ a').length = a'.length :=
    fun s μ a' h => ⟨by simp [LoopIdx.WF, Ward_pmLoop]; omega,
      by simp [LoopIdx.length, Ward_pmLoop]⟩
  -- the derivative
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    refine hasDerivAt_pi.2 fun p => ?_
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hsum : HasDerivAt (fun s => ∑ x : Z2 L, K s (Ward_fullLoop p.1.1 p.2.1 x))
        (∑ x : Z2 L, primRhs L W (K t) (Ward_fullLoop p.1.1 p.2.1 x)) t :=
      HasDerivAt.fun_sum fun x _ => hK t ht _ (hfullWF _ _ x (hp p)).1
        (by rw [(hfullWF _ _ x (hp p)).2, hpN]; omega)
    have hplus := hK t ht _ hWFp (by rw [hlp, hpN]; omega)
    have hminus := hK t ht _ hWFm (by rw [hlm, hpN]; omega)
    have hprod := (Ward_hasDerivAt_kappa W hW hE ht1).mul (hplus.sub hminus)
    refine (hsum.sub hprod).congr_deriv ?_
    have hid := Ward_rhs_identity L (K t) (κ t) p.1.1 p.2.1 hL W (Ward_c W t) (hp p)
      (by rw [hpN]; exact hN) (hcyc t ht) (h2 t ht)
      (fun μ'' a'' h1 h2' => hlow t ht μ'' a'' h1 (by rw [hpN] at h2'; exact h2'))
    have hWc : (W : ℂ) ^ 2 * Ward_c W t = (1 - (t : ℂ))⁻¹ := by
      rw [Ward_c, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hW0), one_mul]
    have ht' : (1 : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero, ne_comm]
      exact_mod_cast ht1.ne
    simp only [D', T, D, Ward_wD, κ, hpN, Pi.sub_apply] at hid ⊢
    linear_combination hid + Ward_wStar L (K t) p.1.1 p.2.1 * hWc
  -- components of `D t`
  have hcomp : ∀ t (μ : List Bool) (a' : List (Z2 L)), μ.length = N - 1 → a'.length = N →
      ‖Ward_wD L (K t) (κ t) μ a'‖ ≤ ‖D t‖ :=
    fun t μ a' h1 h2 => norm_le_pi_norm (D t) (⟨μ, h1⟩, ⟨a', h2⟩)
  -- the bound
  set C : ℝ := (W : ℝ) ^ 2 * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : Z2 L, ∑ _b : Z2 L, R)
    + ∑ _a : Z2 L, ∑ _b : Z2 L, R) + (1 - T₀)⁻¹ with hC
  have hT₀' : 0 < 1 - T₀ := by linarith
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))).2 fun p => ?_
    have hμN : p.1.1.length = N - 1 := p.1.2
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hT1 : ∀ k ∈ Icc 1 (N - 1), ∀ a b : Z2 L,
        ‖Ward_wD L (K t) (κ t) (Ward_cutMu k (k + 1) p.1.1) (Ward_cutA k (k + 1) a p.2.1)
          * SB L a b * K t ((Ward_pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b)‖
          ≤ R * ‖D t‖ := by
      intro k hk a b
      rw [mem_Icc] at hk
      have hlpN : k + 1 ≤ (Ward_pmLoop true p.1.1 p.2.1).length := by rw [hlp, hpN]; omega
      have hWR := LoopIdx.WF.cutGlueR hWFp b hk.1 (Nat.lt_succ_self k) hlpN
      have hlen := LoopIdx.length_cutGlueR (Ward_pmLoop true p.1.1 p.2.1) b hk.1
        (Nat.lt_succ_self k) hlpN
      have hK2 := hR t ht' _ hWR (by rw [hlen]; omega)
      have hD1 := hcomp t (Ward_cutMu k (k + 1) p.1.1) (Ward_cutA k (k + 1) a p.2.1)
        (by rw [Ward_cutMu_adjacent]; exact hμN)
        (by rw [Ward_length_cutA_adjacent L p.2.1 a hk.1 (by rw [hpN]; omega), hpN])
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact Ward_norm_SB_apply_le L hL a b
        _ = R * ‖D t‖ := by ring
    have hT2 : ∀ a b : Z2 L,
        ‖Ward_wD L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB L a b *
          K t ((Ward_pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)‖ ≤ R * ‖D t‖ := by
      intro a b
      have hlmN : N ≤ (Ward_pmLoop false p.1.1 p.2.1).length := by rw [hlm, hpN]
      have hWL := LoopIdx.WF.cutGlueL hWFm b le_rfl (by omega) hlmN
      have hlen := LoopIdx.length_cutGlueL (Ward_pmLoop false p.1.1 p.2.1) b le_rfl
        (by omega) hlmN
      have hK2 := hR t ht' _ hWL (by rw [hlen, hlm, hpN]; omega)
      have hD1 := hcomp t (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a])
        (by rw [List.length_take, hμN]; omega)
        (by rw [List.length_append, List.length_take, hpN, List.length_singleton]; omega)
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact Ward_norm_SB_apply_le L hL a b
        _ = R * ‖D t‖ := by ring
    have hinv : ‖(1 - (t : ℂ))⁻¹‖ ≤ (1 - T₀)⁻¹ := by
      rw [norm_inv, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg h1t.le]
      exact inv_anti₀ hT₀' (by linarith [ht.2])
    calc ‖D' t p‖ ≤ ‖(W : ℂ) ^ 2 * T t p‖ + ‖(1 - (t : ℂ))⁻¹ * D t p‖ := norm_add_le _ _
      _ ≤ (W : ℝ) ^ 2 * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : Z2 L, ∑ _b : Z2 L, R * ‖D t‖)
            + ∑ _a : Z2 L, ∑ _b : Z2 L, R * ‖D t‖) + (1 - T₀)⁻¹ * ‖D t‖ := by
          gcongr
          · rw [norm_mul, norm_pow, Complex.norm_natCast]
            gcongr
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT1 k hk a b
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT2 a b
          · rw [norm_mul]
            exact mul_le_mul hinv (norm_le_pi_norm (D t) p) (norm_nonneg _) (by positivity)
      _ = C * ‖D t‖ := by
          simp only [hC, add_mul, Finset.sum_mul, mul_assoc]
  have hD0 : D 0 = 0 := funext fun p => h0 _ _ (hp p) (hpN p)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) hD0 hbound
  intro t ht μ a' hμ ha'
  have hμ' : μ.length = N - 1 := by omega
  exact congrFun (hzero t ht) (⟨μ, hμ'⟩, ⟨a', ha'⟩)

/-- **`(WI_calK)` at every length** for a primitive family with bounded `2`-loops, cyclic
invariance and the level-`2` identity (the level `2` identity and the cyclic invariance are
hypotheses `hlev2`, `hcyc`). -/
private theorem Ward_of_isPrimitive (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)
    {T : Set ℝ} {K : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W (mSig E) T K) {T₀ R : ℝ}
    (hT₀ : T₀ < 1) (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (hcyc : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length →
      K t (Ward_rot J) = K t J)
    (hlev2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Z2 L, Ward_wD L (K t) (Ward_kappa W E t) [] [a] = 0) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Z2 L)), μ.length + 1 = a'.length →
      Ward_wD L (K t) (Ward_kappa W E t) μ a' = 0 := by
  have h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Z2 L, Ward_wStar L (K t) [] [a] = Ward_c W t := by
    intro t ht a
    have h := hlev2 t ht a
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    simp only [Ward_wD, sub_eq_zero] at h
    rw [h]
    simp only [Ward_pmLoop]
    rw [hK.2.2 t (hT ht) true a, hK.2.2 t (hT ht) false a, Ward_kappa_mul W hW hE ht1]
  -- the initial value
  have h0 : ∀ (μ : List Bool) (a' : List (Z2 L)), μ.length + 1 = a'.length → 2 ≤ a'.length →
      Ward_wD L (K 0) (Ward_kappa W E 0) μ a' = 0 := by
    intro μ a' hμ h2'
    rw [← Ward_wD_primInit L W hW hE μ a' hμ]
    simp only [Ward_wD, Ward_wStar]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => hK.2.1 _ ?_ ?_
      · simp [LoopIdx.WF, Ward_fullLoop]; omega
      · simp [LoopIdx.length, Ward_fullLoop]; omega
    · rw [hK.2.1 _ (by simp [LoopIdx.WF, Ward_pmLoop]; omega)
          (by simp [LoopIdx.length, Ward_pmLoop]; omega),
        hK.2.1 _ (by simp [LoopIdx.WF, Ward_pmLoop]; omega)
          (by simp [LoopIdx.length, Ward_pmLoop]; omega)]
  -- induction on the length
  have main : ∀ N : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Z2 L)),
      μ.length + 1 = a'.length → a'.length = N →
        Ward_wD L (K t) (Ward_kappa W E t) μ a' = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro t ht μ a' hμ hN
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · have hμ0 : μ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨a, ha⟩ : ∃ a, a' = [a] := List.length_eq_one_iff.mp (by omega)
        rw [hμ0, ha]
        exact hlev2 t ht a
      · refine Ward_level L hL W hW hE K T₀ R N hN2 hT₀ hR0 (fun s hs => hK.1 s (hT hs))
          hcyc hR h2 ?_ ?_ t ht μ a' hμ hN
        · intro s hs μ'' a'' h1 hlt
          exact ih _ hlt s hs μ'' a'' h1 rfl
        · intro μ'' a'' h1 hN'
          exact h0 μ'' a'' h1 (by omega)
  intro t ht μ a' hμ
  exact main _ t ht μ a' hμ rfl

/-! ### The `2`-loop bound (as `Cyclic_two_loop_bound` in `RBM2D/Loop/Cyclic.lean`) -/

private abbrev Ward_LoopVec (n : ℕ) := List.Vector Bool n × List.Vector (Z2 L) n

private def Ward_toLoop {n : ℕ} (p : Ward_LoopVec L n) : LoopIdx (Z2 L) := ⟨p.1.1, p.2.1⟩

omit [NeZero L] in
private theorem Ward_toLoop_wf {n : ℕ} (p : Ward_LoopVec L n) : (Ward_toLoop L p).WF := by
  change p.1.1.length = p.2.1.length
  rw [p.1.2, p.2.2]

omit [NeZero L] in
private theorem Ward_toLoop_length {n : ℕ} (p : Ward_LoopVec L n) :
    (Ward_toLoop L p).length = n := p.2.2

omit [NeZero L] in
private theorem Ward_exists_toLoop {n : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF)
    (hJn : J.length = n) : ∃ p : Ward_LoopVec L n, Ward_toLoop L p = J :=
  ⟨(⟨J.σ, hJ.trans hJn⟩, ⟨J.a, hJn⟩), rfl⟩

/-- A primitive family has bounded `2`-loops on any `[0, T₀] ⊆ T`. -/
private theorem Ward_two_loop_bound (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ C := by
  let f : ℝ → Ward_LoopVec L 2 → ℂ := fun s p => K s (Ward_toLoop L p)
  have hf : ContinuousOn f (Set.Icc 0 T₀) := by
    refine continuousOn_pi.2 fun p s hs => ?_
    have := hK.1 s (hT hs) (Ward_toLoop L p) (Ward_toLoop_wf L p)
      (by rw [Ward_toLoop_length L p])
    exact this.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨C, fun t ht I hI hI2 => ?_⟩
  obtain ⟨p, rfl⟩ := Ward_exists_toLoop L I hI hI2
  exact (norm_le_pi_norm (f t) p).trans (hC t ht)

end Level

/-! ## 5. The main statement -/

/-- **`(WI_calK)`.**  For `σ = (+, σ₂, …, σ_{n−1}, −)`:
`∑_{aₙ} 𝒦_{t,σ,a} = (2 i W² η_t)⁻¹ (𝒦_{t,σ+,a/aₙ} − 𝒦_{t,σ−,a/aₙ})`.
Proof: `Ward_of_isPrimitive` applied to `Kcal` (primitive by `isPrimitive_Kcal`) on `[0, t]`,
with cyclic invariance from `Kcal_rotate` and level `2` from `WI_calK_two`. -/
theorem Kcal_ward :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (σ : List Bool) (a : List (Z2 L)), a.length = σ.length + 1 →
      ∑ x : Z2 L, Kcal L W E t ⟨true :: σ ++ [false], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹ *
            (Kcal L W E t ⟨true :: σ, a⟩ - Kcal L W E t ⟨false :: σ, a⟩) := by
  intro L W _ hL hW E hE t ht σ a ha
  have hW0 : W ≠ 0 := by omega
  have hKc := isPrimitive_Kcal L W hL hW E hE
  have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  obtain ⟨C, hC⟩ := Ward_two_loop_bound L W (mSig E) hKc hT
  have hcyc : ∀ r ∈ Set.Icc 0 t, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length →
      Kcal L W E r (Ward_rot J) = Kcal L W E r J := by
    intro r hr J hJ hJ2
    obtain ⟨σJ, aJ⟩ := J
    rcases aJ with _ | ⟨b, aJ⟩
    · simp [LoopIdx.length] at hJ2
    rcases σJ with _ | ⟨s, σJ⟩
    · simp [LoopIdx.WF] at hJ
    rw [Ward_rot_mk_cons]
    exact (Kcal_rotate L W hL hW E hE r (hT hr) s b σJ aJ (by simpa [LoopIdx.WF] using hJ)).symm
  have hlev2 : ∀ r ∈ Set.Icc 0 t, ∀ a₁ : Z2 L,
      Ward_wD L (Kcal L W E r) (Ward_kappa W E r) [] [a₁] = 0 := by
    intro r hr a₁
    have h := WI_calK_two L hL W hW hE (hT hr) a₁
    simp only [Ward_wD, Ward_wStar, Ward_fullLoop, Ward_pmLoop, Ward_kappa]
    rw [h, sub_self]
  have h := Ward_of_isPrimitive L hL W hW0 hE hKc ht.2 hT (le_max_left 0 C)
    (fun r hr J hJ hJ2 => (hC r hr J hJ hJ2).trans (le_max_right 0 C)) hcyc hlev2 t
    ⟨ht.1, le_rfl⟩ σ a ha.symm
  simp only [Ward_wD, Ward_wStar, Ward_fullLoop, Ward_pmLoop, Ward_kappa, sub_eq_zero] at h
  exact h

end RBM.KLoop
