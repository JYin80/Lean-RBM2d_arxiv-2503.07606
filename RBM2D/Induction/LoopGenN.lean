/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Path.DriftAlgebra
import RBM2D.Hierarchy.ContractionSecondLoopAllCuts
import RBM2D.Hierarchy.OperationsPairWord
import RBM2D.Hierarchy.ContractionDrift
import RBM2D.Gauss.LoopCoordinateSecondDerivative
import RBM2D.Gauss.GreenDerivative

/-!
# The general-`n` loop generator

Proves `LoopGenN` (`RBM2D.Induction.HierVocab`): for a Hermitian `M`, the one-step generator
`genMat` of the loop functional `𝓛_{u,I}(M)` equals `W² Σ_{k<l} 𝓛 S 𝓛 + 𝓔^{(G̃)}`, the drift part
of (`eq:mainStoflow`) with (`def_EwtG`).

Proof.
1. Matrix bridge: `M = Xmat ω_M` for the coordinates `ω_M` of `M`, so
   `HflowBlock 1 ω_M = blockMat M`.
2. Second-derivative bridge: the line Hessian of `genMat` along `coordinateMatrix c` is the
   coordinate Hessian `tr coordinateSecondWordDeriv 1 ω_M c z l` at the auxiliary flow time `1`;
   `sum_coordinateSecondWordDeriv_allCuts` contracts it into same-edge and pair cuts.
3. Spectral bridge at a general Hermitian block matrix: the `v`-derivative of the loop is a sum
   of scalar insertions, each turned into single-edge cuts by `neg_trace_scalarDrift_cutGlue_split`.
4. `u = 0` needs no separate case: nothing above uses the flow time `u`.
5. Reindexing: `edgeSplits`/`pairSplits` list sums become the `Finset.Icc`/`Finset.Ioc` sums of
   `egtN` and `llPairN`.

Every helper is `private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Gauss RBM.Path

/-! ## 1. The matrix bridge -/

section MatrixBridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The real coordinates of a matrix: real parts on `true`, imaginary parts on `false`. -/
private def LoopGenN_omega (M : Matrix (Idx L W) (Idx L W) ℂ) : Ω L W :=
  fun c => if c.2.2 then (M c.1 c.2.1).re else (M c.1 c.2.1).im

/-- A Hermitian matrix is the Gaussian matrix of its coordinates. -/
private theorem LoopGenN_Xmat_omega {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    Xmat L W (LoopGenN_omega M) = M := by
  ext i j
  rw [Xmat_apply, Xentry]
  simp only [LoopGenN_omega, ite_true, Bool.false_eq_true, ite_false]
  split_ifs with h1 h2
  · apply Complex.ext <;> simp
  · rw [← hM.apply i j]
    apply Complex.ext <;> simp
  · have hij : i = j := by
      rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
      · exact absurd h h1
      · exact h
      · exact absurd h h2
    subst hij
    exact hM.coe_re_apply_self i

/-- At the auxiliary flow time `1`, the flow sample of `ω_M` is `blockMat M`. -/
private theorem LoopGenN_HflowBlock_one {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    HflowBlock L W 1 (LoopGenN_omega M) = blockMat M := by
  rw [HflowBlock, Hflow, Real.sqrt_one, Complex.ofReal_one, one_smul, LoopGenN_Xmat_omega hM]
  rfl

end MatrixBridge

/-! ## 2. The second-derivative bridge -/

section SecondBridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The line Hessian of the loop along `coordinateMatrix c` at a Hermitian `M` is the coordinate
Hessian of the flow sample `ω_M` at the auxiliary time `1`. -/
private theorem LoopGenN_deriv2 {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) z I)) 0 =
      Matrix.trace (coordinateSecondWordDeriv L W 1 (LoopGenN_omega M) c z (I.σ.zip I.a)) := by
  set ω := LoopGenN_omega M with hω
  set g : ℝ → ℂ := fun s => gloop L W (HflowBlock L W 1 (Function.update ω c s)) z I with hg
  have hfg : (fun y : ℝ =>
      gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) z I) =
      fun y => g (y + ω c) := by
    funext y
    simp only [hg, HflowBlock_update, hω, LoopGenN_HflowBlock_one hM, Real.sqrt_one, one_mul,
      add_sub_cancel_right]
    congr 1
  rw [hfg]
  have h1 : deriv (fun y : ℝ => g (y + ω c)) = fun y => deriv g (y + ω c) := by
    funext y
    exact deriv_comp_add_const _ _ _
  rw [h1, deriv_comp_add_const, zero_add]
  exact (hasDerivAt_deriv_gloop_update L W 1 ω c hz I hI).deriv

end SecondBridge

/-! ## 3. The spectral bridge at a general Hermitian block matrix -/

section SpectralBridge

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The signed word `Π G(σ) E_a` of a list of edges, at a general block matrix. -/
private def LoopGenN_word (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

private theorem LoopGenN_word_eq (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    LoopGenN_word H z l = gloopProd L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]
  rfl

/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix
(the generic-`H` form of the private `OneStep_hasDerivAt_spec0`). -/
private theorem LoopGenN_hasDerivAt_Gsig_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gsig H (spectralZ E v) σ)
      (-(Gsig H (spectralZ E u) σ *
        (spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
        Gsig H (spectralZ E u) σ)) u := by
  have him : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) (hasDerivAt_spectralZ E u) hH him
      simpa only [Gsig_true, spectralMSign, ite_true, zero_sub, neg_smul, neg_neg,
        Matrix.mul_neg, Matrix.neg_mul] using h
  | false =>
      have hz : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (spectralZ E v))
          (-((starRingEnd ℂ) (spectralM E))) u := by
        simpa using (hasDerivAt_spectralZ E u).star
      have him' : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by simpa using him
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) hz hH him'
      simpa only [Gsig_false, spectralMSign, Bool.false_eq_true, ite_false, zero_sub, neg_smul,
        neg_neg, Matrix.mul_neg, Matrix.neg_mul] using h

/-- The scalar insertion at one selected edge. -/
private def LoopGenN_edgeTerm (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (E u : ℝ)
    (e : EdgeSplit (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  -(LoopGenN_word H (spectralZ E u) e.before *
    (Gsig H (spectralZ E u) e.selected.1 *
        (spectralMSign E e.selected.1 • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
      (Gsig H (spectralZ E u) e.selected.1 * Eblk L W e.selected.2 *
        LoopGenN_word H (spectralZ E u) e.after)))

/-- The product rule over the word: the spectral derivative is the sum of the edge insertions. -/
private theorem LoopGenN_hasDerivAt_word_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (l : List (Bool × Z2 L)) :
    HasDerivAt (fun v : ℝ => LoopGenN_word H (spectralZ E v) l)
      (((edgeSplits l).map (LoopGenN_edgeTerm H E u)).sum) u := by
  induction l with
  | nil =>
      simpa [LoopGenN_word, edgeSplits] using
        hasDerivAt_const u (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have h := ((LoopGenN_hasDerivAt_Gsig_spec hH hE hu p.1).mul_const (Eblk L W p.2)).mul ih
      have hfun : (fun v : ℝ => Gsig H (spectralZ E v) p.1 * Eblk L W p.2) *
          (fun v : ℝ => LoopGenN_word H (spectralZ E v) l) =
          fun v : ℝ => LoopGenN_word H (spectralZ E v) (p :: l) := by
        funext v
        rfl
      rw [hfun] at h
      refine h.congr_deriv ?_
      have hcons : ∀ e : EdgeSplit (Bool × Z2 L),
          LoopGenN_edgeTerm H E u ⟨p :: e.before, e.selected, e.after⟩ =
            (Gsig H (spectralZ E u) p.1 * Eblk L W p.2) * LoopGenN_edgeTerm H E u e := by
        intro e
        simp only [LoopGenN_edgeTerm, LoopGenN_word, List.foldr_cons, Matrix.mul_neg,
          Matrix.mul_assoc]
      simp only [edgeSplits, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        hcons, List.sum_map_mul_left]
      simp only [LoopGenN_edgeTerm, LoopGenN_word, List.foldr_nil, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.neg_mul]

/-- The spectral derivative of a loop at a fixed Hermitian block matrix. -/
private theorem LoopGenN_deriv_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (I : LoopIdx (Z2 L)) :
    deriv (fun v : ℝ => gloop L W H (spectralZ E v) I) u =
      ((edgeSplits (I.σ.zip I.a)).map
        (fun e => Matrix.trace (LoopGenN_edgeTerm H E u e))).sum := by
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (LoopGenN_hasDerivAt_word_spec hH hE hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => gloop L W H (spectralZ E v) I) =
      fun v : ℝ => Matrix.trace (LoopGenN_word H (spectralZ E v) (I.σ.zip I.a)) := by
    funext v
    rfl
  rw [hfun, h.deriv, Matrix.trace_list_sum, List.map_map]
  rfl

/-- One edge insertion is a sum of single-edge cuts. -/
private theorem LoopGenN_trace_edgeTerm (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (E u : ℝ) (e : EdgeSplit (Bool × Z2 L)) :
    Matrix.trace (LoopGenN_edgeTerm H E u e) =
      -(spectralMSign E e.selected.1 * (W : ℂ) ^ 2) *
        ∑ b : Z2 L, gloop L W H (spectralZ E u)
          ((⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
              e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ :
            LoopIdx (Z2 L)).cutGlue ((e.before.map Prod.fst).length + 1) b) := by
  have hpre : (e.before.map Prod.fst).length = (e.before.map Prod.snd).length := by simp
  have h := RBM.neg_trace_scalarDrift_cutGlue_split L W H (spectralZ E u)
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 (spectralMSign E e.selected.1) hpre
  rw [← h, LoopGenN_edgeTerm, Matrix.trace_neg, LoopGenN_word_eq, LoopGenN_word_eq]

end SpectralBridge

/-! ## 4. Reindexing the cut enumerations -/

section Reindex

/-- A list sum over `List.range n` is the `Finset.range` sum. -/
private theorem LoopGenN_sum_listRange (n : ℕ) (f : ℕ → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `Σ_{i<n} F(i+1) = Σ_{k ∈ [1,n]} F k`. -/
private theorem LoopGenN_sum_range_Icc (n : ℕ) (F : ℕ → ℂ) :
    ∑ i ∈ Finset.range n, F (i + 1) = ∑ k ∈ Finset.Icc 1 n, F k := by
  refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]; omega
  · intro i _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro i _; rfl

/-- A sum over the edge enumeration, whose summand depends only on the one-based position. -/
private theorem LoopGenN_sum_edgeSplits {α : Type*} (l : List α) (f : EdgeSplit α → ℂ)
    (F : ℕ → ℂ) (h : ∀ e ∈ edgeSplits l, f e = F (e.before.length + 1)) :
    ((edgeSplits l).map f).sum = ∑ k ∈ Finset.Icc 1 l.length, F k := by
  rw [List.map_congr_left h]
  have hmap : (edgeSplits l).map (fun e => F (e.before.length + 1)) =
      ((edgeSplits l).map (fun e => e.before.length)).map (fun i => F (i + 1)) := by
    rw [List.map_map]
    rfl
  rw [hmap, edgeSplits_prefix_lengths, LoopGenN_sum_listRange, LoopGenN_sum_range_Icc]

/-- The sum of a `flatMap` is the sum of the inner sums. -/
private theorem LoopGenN_sum_flatMap {α β : Type*} (xs : List α) (g : α → List β) (f : β → ℂ) :
    ((xs.flatMap g).map f).sum = (xs.map fun x => ((g x).map f).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

/-- A sum over the pair enumeration, whose summand depends only on the two one-based positions. -/
private theorem LoopGenN_sum_pairSplits {α : Type*} (l : List α) (f : PairSplit α → ℂ)
    (F : ℕ → ℕ → ℂ)
    (h : ∀ p ∈ pairSplits l,
      f p = F (p.before.length + 1) (p.before.length + p.middle.length + 2)) :
    ((pairSplits l).map f).sum =
      ∑ k ∈ Finset.Icc 1 l.length, ∑ l' ∈ Finset.Ioc k l.length, F k l' := by
  rw [List.map_congr_left h, pairSplits, LoopGenN_sum_flatMap]
  refine LoopGenN_sum_edgeSplits l _ _ fun e he => ?_
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have hr := edgeSplits_reconstruct l e he
    rw [← hr, List.length_append, List.length_cons]
    omega
  rw [List.map_map]
  rw [LoopGenN_sum_edgeSplits e.after _
    (fun j => F (e.before.length + 1) (e.before.length + j + 1)) (fun d _ => by
      simp only [Function.comp_apply]
      congr 1)]
  refine Finset.sum_nbij' (fun j => e.before.length + j + 1)
    (fun l' => l' - (e.before.length + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_Ioc]; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'
    simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'; omega
  · intro j _; rfl

end Reindex

/-! ## 5. Identifying each cut term with the loop's own cuts -/

section Cuts

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A selected edge of the zipped word of a well-formed loop splits that loop. -/
private theorem LoopGenN_edge_eq (I : LoopIdx (Z2 L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Z2 L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    I = ⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
      e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ := by
  have hr := edgeSplits_reconstruct _ e he
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- Two selected edges of the zipped word of a well-formed loop split that loop. -/
private theorem LoopGenN_pair_eq (I : LoopIdx (Z2 L)) (hI : I.WF)
    (p : PairSplit (Bool × Z2 L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    I = ⟨p.before.map Prod.fst ++ p.first.1 :: p.middle.map Prod.fst ++
          p.second.1 :: p.after.map Prod.fst,
      p.before.map Prod.snd ++ p.first.2 :: p.middle.map Prod.snd ++
          p.second.2 :: p.after.map Prod.snd⟩ := by
  have hr := pairSplits_reconstruct _ p hp
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- The sign at the selected edge. -/
private theorem LoopGenN_getD (b a : List (Bool × Z2 L)) (s : Bool) :
    (b.map Prod.fst ++ s :: a.map Prod.fst).getD (b.length + 1 - 1) false = s := by
  rw [Nat.add_sub_cancel, List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The rotated same-edge loop is the single-edge cut of the original loop. -/
private theorem LoopGenN_gloop_same (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (b a : List (Bool × Z2 L)) (s : Bool) (x p : Z2 L) :
    gloop L W H z ⟨s :: (a.map Prod.fst ++ (b.map Prod.fst ++ [s])),
        x :: (a.map Prod.snd ++ (b.map Prod.snd ++ [p]))⟩ =
      gloop L W H z ((⟨b.map Prod.fst ++ s :: a.map Prod.fst,
        b.map Prod.snd ++ x :: a.map Prod.snd⟩ : LoopIdx (Z2 L)).cutGlue (b.length + 1) p) := by
  have hb : (b.map Prod.fst).length = (b.map Prod.snd).length := by simp
  have ha : (a.map Prod.fst).length = (a.map Prod.snd).length := by simp
  have hc := LoopIdx.cutGlue_split (b.map Prod.fst) (a.map Prod.fst) (b.map Prod.snd)
    (a.map Prod.snd) s x p hb
  rw [List.length_map] at hc
  rw [hc]
  simp only [gloop, gloopProd_cons, gloopProd_append ha, gloopProd_append hb, gloopProd_nil]
  have h := Matrix.trace_mul_comm (Gsig H z s * Eblk L W x * gloopProd L W H z
      ⟨a.map Prod.fst, a.map Prod.snd⟩)
    (gloopProd L W H z ⟨b.map Prod.fst, b.map Prod.snd⟩ * (Gsig H z s * Eblk L W p))
  simp only [Matrix.mul_assoc, Matrix.mul_one] at h ⊢
  exact h

/-- The same-edge cut value at a selected edge, as a function of its one-based position. -/
private theorem LoopGenN_sameEdge {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Z2 L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    sameEdgeCutValue L W 1 (LoopGenN_omega M) z e =
      ∑ p : Z2 L, ∑ q : Z2 L, gloop L W (blockMat M) z (I.cutGlue (e.before.length + 1) p) *
        SB L p q * Matrix.trace (Gsig (blockMat M) z (I.σ.getD (e.before.length + 1 - 1) false) *
          Eblk L W q) := by
  have hIe := LoopGenN_edge_eq I hI e he
  simp only [sameEdgeCutValue, segmentLoopIdx, LoopGenN_HflowBlock_one hM]
  rw [hIe, LoopGenN_getD]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [LoopGenN_gloop_same]
  congr 1
  simp [gloop]

/-- The pair cut value at two selected edges, as a function of their one-based positions. -/
private theorem LoopGenN_pairCut {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (E u : ℝ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (p : PairSplit (Bool × Z2 L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    pairCutValue L W 1 (LoopGenN_omega M) (spectralZ E u) p =
      ∑ v : Z2 L, ∑ w : Z2 L,
        LLf L W E u M (I.cutGlueL (p.before.length + 1)
            (p.before.length + p.middle.length + 2) v) * SB L v w *
          LLf L W E u M (I.cutGlueR (p.before.length + 1)
            (p.before.length + p.middle.length + 2) w) := by
  have hIp := LoopGenN_pair_eq I hI p hp
  simp only [pairCutValue, segmentLoopIdx, LoopGenN_HflowBlock_one hM, List.length_map]
  rw [← hIp]
  rfl

/-- The spectral insertion at a selected edge, as a function of its one-based position. -/
private theorem LoopGenN_specEdge (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (E u : ℝ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Z2 L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Matrix.trace (LoopGenN_edgeTerm H E u e) =
      -(spectralMSign E (I.σ.getD (e.before.length + 1 - 1) false) * (W : ℂ) ^ 2) *
        ∑ b : Z2 L, gloop L W H (spectralZ E u) (I.cutGlue (e.before.length + 1) b) := by
  have hIe := LoopGenN_edge_eq I hI e he
  rw [LoopGenN_trace_edgeTerm, List.length_map]
  conv_rhs => rw [hIe, LoopGenN_getD]

end Cuts

/-! ## 6. The single-edge algebra and the assembly -/

section Assembly

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)`. -/
private theorem LoopGenN_avgErr (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (a : Z2 L) :
    avgErr L W E u M σ a =
      Matrix.trace (Gsig (blockMat M) (spectralZ E u) σ * Eblk L W a) - spectralMSign E σ := by
  rw [avgErr, greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, trace_Eblk_eq_one, smul_eq_mul, mul_one]
  rfl

/-- Column sums of `S^{(B)}` are `1`. -/
private theorem LoopGenN_sum_SB_col (hL : 3 ≤ L) (b : Z2 L) : ∑ a : Z2 L, SB L a b = 1 := by
  rw [← sum_SB_row L hL b]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrFun (congrFun (SB_transpose L) b) a

/-- `Σ_{a,b} (t_a - m) S_{ab} g_b = Σ_{p,q} g_p S_{pq} t_q - m Σ_b g_b`. -/
private theorem LoopGenN_sum_algebra (hL : 3 ≤ L) (f g : Z2 L → ℂ) (m : ℂ) :
    ∑ a' : Z2 L, ∑ b' : Z2 L, (g a' - m) * SB L a' b' * f b' =
      ∑ p : Z2 L, ∑ q : Z2 L, f p * SB L p q * g q - m * ∑ p : Z2 L, f p := by
  have hS : ∀ p q : Z2 L, SB L p q = SB L q p := fun p q =>
    congrFun (congrFun (SB_transpose L) q) p
  have h1 : ∑ a' : Z2 L, ∑ b' : Z2 L, g a' * SB L a' b' * f b' =
      ∑ p : Z2 L, ∑ q : Z2 L, f p * SB L p q * g q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hS q p]
    ring
  have h2 : ∑ a' : Z2 L, ∑ b' : Z2 L, m * SB L a' b' * f b' = m * ∑ p : Z2 L, f p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, LoopGenN_sum_SB_col hL, mul_one]
  rw [← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- The same-edge cuts and the spectral cuts of one edge combine into its `𝓔^{(G̃)}` term. -/
private theorem LoopGenN_edge_algebra (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) (k : ℕ) :
    (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W (blockMat M) (spectralZ E u) (I.cutGlue k p) * SB L p q *
          Matrix.trace (Gsig (blockMat M) (spectralZ E u) (I.σ.getD (k - 1) false) *
            Eblk L W q) +
      -(spectralMSign E (I.σ.getD (k - 1) false) * (W : ℂ) ^ 2) *
        ∑ b : Z2 L, gloop L W (blockMat M) (spectralZ E u) (I.cutGlue k b) =
    (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
      avgErr L W E u M (I.σ.getD (k - 1) false) a * SB L a b * LLf L W E u M (I.cutGlue k b) := by
  simp only [LoopGenN_avgErr]
  rw [LoopGenN_sum_algebra hL (fun b => LLf L W E u M (I.cutGlue k b))
    (fun a => Matrix.trace (Gsig (blockMat M) (spectralZ E u) (I.σ.getD (k - 1) false) *
      Eblk L W a))]
  simp only [LLf]
  ring

end Assembly

/-- **`LoopGenN`** (`eq:mainStoflow`, drift part, general `n`). -/
theorem loopGenN : LoopGenN := by
  intro L W _ _ E hL hE u hu0 hu1 M hM k hk σ a
  set I : LoopIdx (Z2 L) := loopOf σ a with hIdef
  have hI : I.WF := by simp [hIdef, loopOf, LoopIdx.WF]
  have hlen : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, List.length_zip, hI.symm]
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  set l := I.σ.zip I.a with hl
  set ω := LoopGenN_omega M with hω
  set z := spectralZ E u with hzdef
  -- the three families of cut terms as functions of the one-based positions
  set Fs : ℕ → ℂ := fun k' => ∑ p : Z2 L, ∑ q : Z2 L,
    gloop L W (blockMat M) z (I.cutGlue k' p) * SB L p q *
      Matrix.trace (Gsig (blockMat M) z (I.σ.getD (k' - 1) false) * Eblk L W q) with hFs
  set Fsp : ℕ → ℂ := fun k' => -(spectralMSign E (I.σ.getD (k' - 1) false) * (W : ℂ) ^ 2) *
    ∑ b : Z2 L, gloop L W (blockMat M) z (I.cutGlue k' b) with hFsp
  set Fp : ℕ → ℕ → ℂ := fun k' l' => ∑ v : Z2 L, ∑ w : Z2 L,
    LLf L W E u M (I.cutGlueL k' l' v) * SB L v w * LLf L W E u M (I.cutGlueR k' l' w) with hFp
  have hsame := LoopGenN_sum_edgeSplits l (sameEdgeCutValue L W 1 ω z) Fs
    (fun e he => LoopGenN_sameEdge hM z I hI e he)
  have hpair := LoopGenN_sum_pairSplits l (pairCutValue L W 1 ω z) Fp
    (fun p hp => LoopGenN_pairCut hM E u I hI p hp)
  have hspec := LoopGenN_sum_edgeSplits l
    (fun e => Matrix.trace (LoopGenN_edgeTerm (blockMat M) E u e)) Fsp
    (fun e he => LoopGenN_specEdge (blockMat M) E u I hI e he)
  -- the left side
  have hlhs : genMat E u M I =
      (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, Fs k' +
        (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k' I.length, Fp k' l' +
        ∑ k' ∈ Finset.Icc 1 I.length, Fsp k' := by
    rw [genMat, Finset.sum_congr rfl fun c _ => by rw [LoopGenN_deriv2 hM c hz I hI],
      sum_coordinateSecondWordDeriv_allCuts L W 1 zero_le_one ω z l,
      LoopGenN_deriv_spec hH hE hu1 I, hsame, hpair, hspec, hlen]
    push_cast
    ring
  have hedge : ∑ k' ∈ Finset.Icc 1 I.length, ((W : ℂ) ^ 2 * Fs k' + Fsp k') =
      (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
        avgErr L W E u M (I.σ.getD (k' - 1) false) a * SB L a b *
          LLf L W E u M (I.cutGlue k' b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => LoopGenN_edge_algebra hL E u M I k'
  rw [hlhs]
  unfold llPairN egtN
  rw [← hedge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hFp]
  ring

end RBM.Ind

end
