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

/-- An enumerated pair always consists of two valid increasing positions. -/
theorem pairSplits_positions_valid {α : Type*} (l : List α)
    (p : PairSplit α) (hp : p ∈ pairSplits l) :
    p.before.length < p.before.length + 1 + p.middle.length ∧
      p.before.length + 1 + p.middle.length < l.length := by
  have h := pairSplits_reconstruct l p hp
  have hlen : l.length =
      p.before.length + 1 + p.middle.length + 1 + p.after.length := by
    rw [← h, List.length_append, List.length_cons, List.length_append,
      List.length_cons]
    omega
  omega

private theorem edgeSplits_injective_position {α : Type*} (l : List α)
    (e d : EdgeSplit α) (he : e ∈ edgeSplits l) (hd : d ∈ edgeSplits l)
    (h : e.before.length = d.before.length) : e = d := by
  have hnodup : ((edgeSplits l).map (fun x => x.before.length)).Nodup := by
    rw [edgeSplits_prefix_lengths]
    exact List.nodup_range
  exact List.inj_on_of_nodup_map hnodup he hd h

private theorem pairSplits_injective_positions {α : Type*} (l : List α)
    (p q : PairSplit α) (hp : p ∈ pairSplits l) (hq : q ∈ pairSplits l)
    (hfirst : p.before.length = q.before.length)
    (hsecond : p.middle.length = q.middle.length) : p = q := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_pairSplits_iff l p).mp hp
  obtain ⟨d, hd, g, hg, rfl⟩ := (mem_pairSplits_iff l q).mp hq
  have hed : e = d := edgeSplits_injective_position l e d he hd hfirst
  subst d
  have hfg : f = g := edgeSplits_injective_position e.after f g hf hg hsecond
  subst g
  rfl

/-- Every ordered pair of distinct positions occurs exactly once. -/
theorem pairSplits_unique_positions {α : Type*} (l : List α)
    (i j : ℕ) (hij : i < j) (hj : j < l.length) :
    ∃! p : PairSplit α,
      p ∈ pairSplits l ∧ p.before.length = i ∧
        p.before.length + 1 + p.middle.length = j := by
  obtain ⟨e, ⟨he, hei⟩, _⟩ := edgeSplits_unique_position l i (lt_trans hij hj)
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have h := edgeSplits_reconstruct l e he
    rw [← h, List.length_append, List.length_cons]
    omega
  have hk : j - (i + 1) < e.after.length := by omega
  obtain ⟨f, ⟨hf, hfk⟩, _⟩ :=
    edgeSplits_unique_position e.after (j - (i + 1)) hk
  let p : PairSplit α := ⟨e.before, e.selected, f.before, f.selected, f.after⟩
  have hp : p ∈ pairSplits l := (mem_pairSplits_iff l p).mpr ⟨e, he, f, hf, rfl⟩
  refine ⟨p, ⟨hp, hei, ?_⟩, ?_⟩
  · dsimp [p]
    omega
  · intro q ⟨hq, hqi, hqj⟩
    apply pairSplits_injective_positions l q p hq hp
    · exact hqi.trans hei.symm
    · dsimp [p] at hqj ⊢
      omega

end RBM.Gauss
