/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.ContractionEdgeSplits

/-!
# Enumerating two ordered edges of a finite word
-/

namespace RBM.Gauss

/-- Two selected edges with the three intervening word segments. -/
structure PairSplit (α : Type*) where
  before : List α
  first : α
  middle : List α
  second : α
  after : List α

/-- Choose the first edge, then choose the second edge in its suffix. -/
def pairSplits {α : Type*} (l : List α) : List (PairSplit α) :=
  (edgeSplits l).flatMap fun e =>
    (edgeSplits e.after).map fun f =>
      ⟨e.before, e.selected, f.before, f.selected, f.after⟩

private theorem mem_pairSplits_iff {α : Type*} (l : List α) (p : PairSplit α) :
    p ∈ pairSplits l ↔
      ∃ e ∈ edgeSplits l, ∃ f ∈ edgeSplits e.after,
        p = ⟨e.before, e.selected, f.before, f.selected, f.after⟩ := by
  simp only [pairSplits, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, he, f, hf, hfp⟩
    exact ⟨e, he, f, hf, hfp.symm⟩
  · rintro ⟨e, he, f, hf, rfl⟩
    exact ⟨e, he, f, hf, rfl⟩

/-- Every enumerated pair reconstructs the original word. -/
theorem pairSplits_reconstruct {α : Type*} (l : List α)
    (p : PairSplit α) (hp : p ∈ pairSplits l) :
    p.before ++ p.first :: p.middle ++ p.second :: p.after = l := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_pairSplits_iff l p).mp hp
  have houter := edgeSplits_reconstruct l e he
  have hinner := edgeSplits_reconstruct e.after f hf
  simpa only [List.append_assoc, List.cons_append] using
    (hinner ▸ houter)

end RBM.Gauss
