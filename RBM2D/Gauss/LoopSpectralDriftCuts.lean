/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopFlowCoordinateChain
import RBM2D.Hierarchy.ContractionDrift

/-!
# Spectral drift as a finite sum of single-edge cuts

Each signed edge supplies one scalar resolvent insertion. The existing
cut-and-glue contraction converts its trace into a sum over the inserted
block label.
-/

namespace RBM.Gauss

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- A split at one signed edge of a paired loop word. -/
structure SpectralEdgeSplit (L : ℕ) where
  pre : List (Bool × Z2 L)
  edge : Bool × Z2 L
  post : List (Bool × Z2 L)

/-- One split per signed edge, in its original list order. -/
def spectralEdgeSplits : List (Bool × Z2 L) → List (SpectralEdgeSplit L)
  | [] => []
  | p :: l => ⟨[], p, l⟩ ::
      (spectralEdgeSplits l).map fun s => ⟨p :: s.pre, s.edge, s.post⟩

omit [NeZero L] in
theorem length_spectralEdgeSplits (l : List (Bool × Z2 L)) :
    (spectralEdgeSplits (L := L) l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [spectralEdgeSplits, ih]

omit [NeZero L] in
/-- Every generated split reconstructs its original paired word. -/
theorem spectralEdgeSplits_reconstruct (l : List (Bool × Z2 L))
    (s : SpectralEdgeSplit L) (hs : s ∈ spectralEdgeSplits L l) :
    s.pre ++ s.edge :: s.post = l := by
  induction l generalizing s with
  | nil => simp [spectralEdgeSplits] at hs
  | cons p l ih =>
      simp only [spectralEdgeSplits, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | ⟨s', hs', rfl⟩
      · rfl
      · simpa only [List.cons_append] using congrArg (List.cons p) (ih s' hs')

private noncomputable def pairedWord (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (z : ℂ) (l : List (Bool × Z2 L)) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

omit [NeZero W] in
private theorem pairedWord_eq_gloopProd
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    pairedWord L W H z l =
      gloopProd L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]
  rfl

/-- The matrix insertion at a selected signed edge. -/
noncomputable def spectralEdgeTerm (ω : Ω L W) (E u : ℝ)
    (s : SpectralEdgeSplit L) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  let H := HflowBlock L W u ω;
  let z := spectralZ E u;
  let G := Gsig H z s.edge.1;
  let M := spectralMSign E s.edge.1 •
    (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ);
  -(pairedWord L W H z s.pre *
    (G * M * (G * Eblk L W s.edge.2 * pairedWord L W H z s.post)))

private theorem spectralEdgeTerm_head (ω : Ω L W) (E u : ℝ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) :
    spectralEdgeTerm L W ω E u ⟨[], p, l⟩ =
      (gsigSpectralFlowDeriv L W ω E u p.1 * Eblk L W p.2) *
        pairedWord L W (HflowBlock L W u ω) (spectralZ E u) l := by
  simp only [spectralEdgeTerm, pairedWord, List.foldr_nil, one_mul,
    gsigSpectralFlowDeriv]
  noncomm_ring

private theorem spectralEdgeTerm_cons_prefix (ω : Ω L W) (E u : ℝ)
    (p : Bool × Z2 L) (s : SpectralEdgeSplit L) :
    spectralEdgeTerm L W ω E u ⟨p :: s.pre, s.edge, s.post⟩ =
      (Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2) *
        spectralEdgeTerm L W ω E u s := by
  simp only [spectralEdgeTerm, pairedWord, List.foldr_cons]
  noncomm_ring

/-- The recursive spectral derivative is the finite sum of all signed-edge insertions. -/
theorem spectralWordDeriv_eq_sum_edgeTerms (ω : Ω L W) (E u : ℝ)
    (l : List (Bool × Z2 L)) :
    spectralWordDeriv L W ω E u l =
      ((spectralEdgeSplits L l).map (spectralEdgeTerm L W ω E u)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      have htail :
          ((spectralEdgeSplits L l).map fun s => spectralEdgeTerm L W ω E u
            ⟨p :: s.pre, s.edge, s.post⟩).sum =
          (Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2) *
            ((spectralEdgeSplits L l).map (spectralEdgeTerm L W ω E u)).sum := by
        simp_rw [spectralEdgeTerm_cons_prefix]
        exact List.sum_map_mul_left _ _ _
      rw [spectralWordDeriv]
      simp only [spectralEdgeSplits, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def, spectralEdgeTerm_head]
      rw [htail]
      rw [← ih]
      rfl

/-- A single signed-edge insertion is the existing cut-and-glue loop sum. -/
theorem trace_spectralEdgeTerm_eq_cutGlue (ω : Ω L W) (E u : ℝ)
    (s : SpectralEdgeSplit L) :
    Matrix.trace (spectralEdgeTerm L W ω E u s) =
      -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
        ∑ b : Z2 L,
          gloop L W (HflowBlock L W u ω) (spectralZ E u)
            ((⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
                s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
              LoopIdx (Z2 L)).cutGlue (s.pre.length + 1) b) := by
  have hpre : (s.pre.map Prod.fst).length = (s.pre.map Prod.snd).length := by simp
  have h := RBM.neg_trace_scalarDrift_cutGlue_split L W
    (HflowBlock L W u ω) (spectralZ E u)
    (s.pre.map Prod.fst) (s.post.map Prod.fst)
    (s.pre.map Prod.snd) (s.post.map Prod.snd)
    s.edge.1 s.edge.2 (spectralMSign E s.edge.1) hpre
  simpa only [spectralEdgeTerm, Matrix.trace_neg, pairedWord_eq_gloopProd,
    List.length_map] using h

/-- The traced spectral drift is the finite sum of the single-edge cut-loop sums. -/
theorem trace_spectralWordDeriv_eq_sum_cuts (ω : Ω L W) (E u : ℝ)
    (l : List (Bool × Z2 L)) :
    Matrix.trace (spectralWordDeriv L W ω E u l) =
      ((spectralEdgeSplits L l).map fun s =>
        -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
          ∑ b : Z2 L,
            gloop L W (HflowBlock L W u ω) (spectralZ E u)
              ((⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
                  s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
                LoopIdx (Z2 L)).cutGlue (s.pre.length + 1) b)).sum := by
  rw [spectralWordDeriv_eq_sum_edgeTerms, Matrix.trace_list_sum]
  simp only [List.map_map, Function.comp_def, trace_spectralEdgeTerm_eq_cutGlue]

omit [NeZero L] in
private theorem map_zip_fst_snd (σ : List Bool) (a : List (Z2 L))
    (h : σ.length = a.length) :
    (σ.zip a).map Prod.fst = σ ∧ (σ.zip a).map Prod.snd = a := by
  induction σ generalizing a with
  | nil =>
      have ha : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst a
      simp
  | cons s σ ih =>
      cases a with
      | nil => simp at h
      | cons b a =>
          have ht : σ.length = a.length := by simpa using h
          obtain ⟨hσ, ha⟩ := ih a ht
          simp [hσ, ha]

omit [NeZero L] in
/-- A selected edge cut in a well-formed loop acts on that original loop. -/
theorem spectralEdgeSplit_cutGlue_eq (I : LoopIdx (Z2 L)) (hI : I.WF)
    (s : SpectralEdgeSplit L)
    (hs : s ∈ spectralEdgeSplits L (I.σ.zip I.a)) (b : Z2 L) :
    (⟨s.pre.map Prod.fst ++ s.edge.1 :: s.post.map Prod.fst,
       s.pre.map Prod.snd ++ s.edge.2 :: s.post.map Prod.snd⟩ :
       LoopIdx (Z2 L)).cutGlue (s.pre.length + 1) b =
      I.cutGlue (s.pre.length + 1) b := by
  have hrec := spectralEdgeSplits_reconstruct L (I.σ.zip I.a) s hs
  have hσ := congrArg (List.map Prod.fst) hrec
  have ha := congrArg (List.map Prod.snd) hrec
  obtain ⟨hzσ, hza⟩ := map_zip_fst_snd L I.σ I.a hI
  simp only [List.map_append, List.map_cons] at hσ ha
  rw [hzσ] at hσ
  rw [hza] at ha
  cases I with
  | mk σ a =>
      simp only at hσ ha ⊢
      rw [hσ, ha]

/-- The spectral drift of a well-formed loop is a sum of cuts of that loop. -/
theorem trace_spectralWordDeriv_eq_sum_original_cuts
    (ω : Ω L W) (E u : ℝ) (I : LoopIdx (Z2 L)) (hI : I.WF) :
    Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) =
      ((spectralEdgeSplits L (I.σ.zip I.a)).map fun s =>
        -(spectralMSign E s.edge.1 * (W : ℂ) ^ 2) *
          ∑ b : Z2 L,
            gloop L W (HflowBlock L W u ω) (spectralZ E u)
              (I.cutGlue (s.pre.length + 1) b)).sum := by
  rw [trace_spectralWordDeriv_eq_sum_cuts]
  congr 1
  apply List.map_congr_left
  intro s hs
  simp only [spectralEdgeSplit_cutGlue_eq L I hI s hs]

end RBM.Gauss
