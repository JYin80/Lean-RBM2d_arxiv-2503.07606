/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionSecondLoopPositionSum

/-!
# Enumerating one selected edge of a finite word
-/

namespace RBM.Gauss

/-- A chosen edge, with the word before and after it. -/
structure EdgeSplit (α : Type*) where
  before : List α
  selected : α
  after : List α

/-- Enumerate the edge at every position from left to right. -/
def edgeSplits {α : Type*} : List α → List (EdgeSplit α)
  | [] => []
  | x :: xs =>
      ⟨[], x, xs⟩ :: (edgeSplits xs).map
        (fun e => ⟨x :: e.before, e.selected, e.after⟩)

/-- Every enumerated split reconstructs the original word. -/
theorem edgeSplits_reconstruct {α : Type*} (l : List α)
    (e : EdgeSplit α) (he : e ∈ edgeSplits l) :
    e.before ++ e.selected :: e.after = l := by
  induction l generalizing e with
  | nil => simp [edgeSplits] at he
  | cons x xs ih =>
      simp only [edgeSplits, List.mem_cons, List.mem_map] at he
      rcases he with rfl | ⟨d, hd, rfl⟩
      · rfl
      · simpa only [List.cons_append] using congrArg (List.cons x) (ih d hd)

/-- The prefix lengths occur in exactly the order `0, ..., length - 1`. -/
theorem edgeSplits_prefix_lengths {α : Type*} (l : List α) :
    (edgeSplits l).map (fun e => e.before.length) = List.range l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [edgeSplits, List.map_cons, List.map_map, List.length_nil,
        List.length_cons, List.range_succ_eq_map]
      congr 1
      rw [← ih, List.map_map]
      rfl

/-- Each valid position occurs exactly once in the edge-split enumeration. -/
theorem edgeSplits_unique_position {α : Type*} (l : List α)
    (i : ℕ) (hi : i < l.length) :
    ∃! e : EdgeSplit α, e ∈ edgeSplits l ∧ e.before.length = i := by
  have hmap : ((edgeSplits l).map (fun e => e.before.length)).Nodup := by
    rw [edgeSplits_prefix_lengths]
    exact List.nodup_range
  have himem : i ∈ (edgeSplits l).map (fun e => e.before.length) := by
    rw [edgeSplits_prefix_lengths]
    exact List.mem_range.mpr hi
  obtain ⟨e, he, heq⟩ := List.mem_map.mp himem
  refine ⟨e, ⟨he, heq⟩, ?_⟩
  intro d ⟨hd, hdeq⟩
  exact (List.inj_on_of_nodup_map hmap he hd (heq.trans hdeq.symm)).symm

end RBM.Gauss
