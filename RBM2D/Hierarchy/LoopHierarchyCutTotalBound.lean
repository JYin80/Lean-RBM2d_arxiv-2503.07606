/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyCutBlockSumBound

/-!
# Summing finite cut bounds over edge positions

The same-edge family has exactly `n` positions and one uniform envelope.
The pair family is bounded by a finite sum retaining each pair's actual
left/right cut lengths; no unproved comparison of powers is used.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem list_sum_map_le_sum_map {α : Type*} (l : List α)
    (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h x (by simp)) (ih (by
        intro y hy
        exact h y (by simp [hy])))

private theorem list_sum_map_le_card_mul {α : Type*} (l : List α)
    (f : α → ℝ) (C : ℝ) (h : ∀ x ∈ l, f x ≤ C) :
    (l.map f).sum ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        f x + (xs.map f).sum ≤ C + (xs.length : ℝ) * C := add_le_add hx hxs
        _ = ((xs.length : ℝ) + 1) * C := by ring

omit [NeZero L] in
/-- Every edge of a finite word contributes exactly one same-edge split. -/
theorem length_edgeSplits (l : List (Bool × Z2 L)) :
    (edgeSplits l).length = l.length := by
  have h := congrArg List.length (edgeSplits_prefix_lengths l)
  simpa using h

private theorem length_pairSplits_cons {α : Type*} (x : α) (xs : List α) :
    (pairSplits (x :: xs)).length = xs.length + (pairSplits xs).length := by
  have hed : (edgeSplits xs).length = xs.length := by
    have h := congrArg List.length (edgeSplits_prefix_lengths xs)
    simpa using h
  simp [pairSplits, edgeSplits, List.length_flatMap, List.length_map,
    hed, Function.comp_def]

/-- Every unordered choice of two distinct edge positions appears once in
the increasing-position pair enumerator. -/
theorem length_pairSplits {α : Type*} (l : List α) :
    (pairSplits l).length = l.length.choose 2 := by
  induction l with
  | nil => simp [pairSplits, edgeSplits]
  | cons x xs ih =>
      rw [length_pairSplits_cons, ih]
      simp only [List.length_cons, Nat.choose_succ_succ,
        Nat.choose_one_right]

/-- The same pair count in the familiar `n(n−1)/2` form. -/
theorem length_pairSplits_two_formula {α : Type*} (l : List α) :
    (pairSplits l).length = l.length * (l.length - 1) / 2 := by
  rw [length_pairSplits, Nat.choose_two_right]

/-- Sum of norm bounds for all same-edge cuts of a well-formed `n`-loop.
The absolute row mass of `SB` removes one of the two block sums. -/
theorem sum_all_sameEdgeCutIntegrand_norm_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ((edgeSplits (I.σ.zip I.a)).map fun e =>
      ∑ p : Z2 L, ∑ q : Z2 L,
        ‖∫ ω : Ω L W,
          sameEdgeCutIntegrand L W u ω z e p q ∂(P L W)‖).sum ≤
      (I.length : ℝ) *
        ((Fintype.card (Z2 L) : ℝ) *
          (cutResolventEnvelope L W η (I.length + 1) *
            cutResolventEnvelope L W η 1)) := by
  have hsum := list_sum_map_le_card_mul
    (edgeSplits (I.σ.zip I.a))
    (fun e => ∑ p : Z2 L, ∑ q : Z2 L,
      ‖∫ ω : Ω L W,
        sameEdgeCutIntegrand L W u ω z e p q ∂(P L W)‖)
    ((Fintype.card (Z2 L) : ℝ) *
      (cutResolventEnvelope L W η (I.length + 1) *
        cutResolventEnvelope L W η 1))
    (by
      intro e he
      exact sum_norm_integral_sameEdgeCutIntegrand_le L W hL
        I hwf e he u hη hz)
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.WF, LoopIdx.length] at hwf ⊢
    omega
  simpa only [length_edgeSplits, hzip] using hsum

/-- Sum of norm bounds for every ordered distinct-edge cut. Each pair keeps
its actual two loop lengths in the right-hand finite sum. -/
theorem sum_all_pairCutIntegrand_norm_le
    (hL : 3 ≤ L) (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (u : ℝ) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) :
    ((pairSplits (I.σ.zip I.a)).map fun p =>
      ∑ v : Z2 L, ∑ w : Z2 L,
        ‖∫ ω : Ω L W,
          pairCutIntegrand L W u ω z p v w ∂(P L W)‖).sum ≤
    ((pairSplits (I.σ.zip I.a)).map fun p =>
      (Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η
          (p.before.length + p.after.length + 2) *
          cutResolventEnvelope L W η (p.middle.length + 2))).sum := by
  apply list_sum_map_le_sum_map
  intro p hp
  exact sum_norm_integral_pairCutIntegrand_le L W hL
    I hwf p hp u hη hz

end RBM.Gauss
