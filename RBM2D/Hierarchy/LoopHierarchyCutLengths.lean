/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyTwoEdge

/-!
# Lengths of the finite cut loops

These identities relate the resolvent powers in cut terms to the number of
edges in the original well-formed loop. They only concern finite index lists.
-/

namespace RBM.Gauss

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The outer loop index in a same-edge Gaussian contraction. -/
def sameEdgeOuterIdx (e : EdgeSplit (Bool × Z2 L)) (p : Z2 L) :
    LoopIdx (Z2 L) :=
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
    e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩

/-- The one-edge inner loop index in a same-edge Gaussian contraction. -/
def sameEdgeInnerIdx (e : EdgeSplit (Bool × Z2 L)) (q : Z2 L) :
    LoopIdx (Z2 L) := ⟨[e.selected.1], [q]⟩

/-- The reconstructed original loop index at a chosen pair of edges. -/
def pairBaseIdx (p : PairSplit (Bool × Z2 L)) : LoopIdx (Z2 L) :=
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  ⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
    I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩

omit [NeZero L] in
/-- The two loops in each same-edge cut are well formed. -/
theorem sameEdge_cut_WF (e : EdgeSplit (Bool × Z2 L)) (p q : Z2 L) :
    (sameEdgeOuterIdx L e p).WF ∧ (sameEdgeInnerIdx L e q).WF := by
  constructor <;> simp [sameEdgeOuterIdx, sameEdgeInnerIdx,
    LoopIdx.WF, segmentLoopIdx]

omit [NeZero L] in
/-- A same-edge cut turns an `n`-edge loop into loops of lengths `n+1` and
`1`, hence total length `n+2`. -/
theorem sameEdge_cut_lengths (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (e : EdgeSplit (Bool × Z2 L))
    (he : e ∈ edgeSplits (I.σ.zip I.a)) (p q : Z2 L) :
    (sameEdgeOuterIdx L e p).length = I.length + 1 ∧
    (sameEdgeInnerIdx L e q).length = 1 := by
  have hrec := edgeSplits_reconstruct (I.σ.zip I.a) e he
  have hlen := congrArg List.length hrec
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, LoopIdx.WF] at hwf ⊢
    omega
  rw [hzip] at hlen
  constructor
  · simp [sameEdgeOuterIdx, segmentLoopIdx, LoopIdx.length] at hlen ⊢
    omega
  · rfl

omit [NeZero L] in
/-- The pair split reconstructs a well-formed original-length loop index. -/
theorem pairBaseIdx_length_WF (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    (pairBaseIdx L p).length = I.length ∧ (pairBaseIdx L p).WF := by
  have hrec := pairSplits_reconstruct (I.σ.zip I.a) p hp
  have hlen := congrArg List.length hrec
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, LoopIdx.WF] at hwf ⊢
    omega
  rw [hzip] at hlen
  constructor
  · simp [pairBaseIdx, segmentLoopIdx, LoopIdx.length] at hlen ⊢
    omega
  · simp [pairBaseIdx, segmentLoopIdx, LoopIdx.WF]

omit [NeZero L] in
/-- At a spectral cut selected from a well-formed word, the one-based
position is valid and the cut loop has one more edge. -/
theorem spectral_cut_length_WF (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a)) (q : Z2 L) :
    (I.cutGlue (s.pre.length + 1) q).length = I.length + 1 ∧
      (I.cutGlue (s.pre.length + 1) q).WF := by
  have hrec := spectralEdgeSplits_reconstruct L (I.σ.zip I.a) s hs
  have hlen := congrArg List.length hrec
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, LoopIdx.WF] at hwf ⊢
    omega
  have hk : s.pre.length + 1 ≤ I.length := by
    simp only [List.length_append, List.length_cons] at hlen
    omega
  exact ⟨LoopIdx.length_cutGlue I q hk,
    hwf.cutGlue q (by omega) hk⟩

omit [NeZero L] in
/-- A pair cut yields well-formed left and right loops. Their lengths are
`before + after + 2` and `middle + 2`, respectively, summing to `n + 2`. -/
theorem pair_cut_lengths_WF (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a)) (v w : Z2 L) :
    (pairBaseIdx L p |>.cutGlueL (p.before.length + 1)
      (p.before.length + p.middle.length + 2) v).length =
        p.before.length + p.after.length + 2 ∧
    (pairBaseIdx L p |>.cutGlueR (p.before.length + 1)
      (p.before.length + p.middle.length + 2) w).length =
        p.middle.length + 2 ∧
    (pairBaseIdx L p |>.cutGlueL (p.before.length + 1)
      (p.before.length + p.middle.length + 2) v).WF ∧
    (pairBaseIdx L p |>.cutGlueR (p.before.length + 1)
      (p.before.length + p.middle.length + 2) w).WF := by
  have hbase := pairBaseIdx_length_WF L I hwf p hp
  have hrec := pairSplits_reconstruct (I.σ.zip I.a) p hp
  have hwordlen := congrArg List.length hrec
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, LoopIdx.WF] at hwf ⊢
    omega
  rw [hzip] at hwordlen
  simp only [List.length_append, List.length_cons] at hwordlen
  have hk : 1 ≤ p.before.length + 1 := by omega
  have hkl : p.before.length + 1 <
      p.before.length + p.middle.length + 2 := by omega
  have hl : p.before.length + p.middle.length + 2 ≤
      (pairBaseIdx L p).length := by omega
  constructor
  · rw [LoopIdx.length_cutGlueL (pairBaseIdx L p) v hk hkl hl]
    omega
  constructor
  · rw [LoopIdx.length_cutGlueR (pairBaseIdx L p) w hk hkl hl]
    omega
  exact ⟨hbase.2.cutGlueL v hk hkl hl,
    hbase.2.cutGlueR w hk hkl hl⟩

/-- A concrete two-edge pair cut gives two nonempty two-edge loops. -/
example (a b v w : Z2 3) :
    let p : PairSplit (Bool × Z2 3) := ⟨[], (true, a), [], (false, b), []⟩
    ((pairBaseIdx 3 p).cutGlueL 1 2 v).length = 2 ∧
      ((pairBaseIdx 3 p).cutGlueR 1 2 w).length = 2 := by
  let I : LoopIdx (Z2 3) := ⟨[true, false], [a, b]⟩
  let p : PairSplit (Bool × Z2 3) := ⟨[], (true, a), [], (false, b), []⟩
  have hp : p ∈ pairSplits (I.σ.zip I.a) := by
    simp [I, p, pairSplits_two_edges]
  have h := pair_cut_lengths_WF 3 I (by simp [I, LoopIdx.WF]) p hp v w
  exact ⟨by simpa [p] using h.1, by simpa [p] using h.2.1⟩

end RBM.Gauss
