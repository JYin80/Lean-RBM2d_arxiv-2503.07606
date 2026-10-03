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
import RBM2D.Universality.GUEPhase.Bootstrap
import RBM2D.Endpoints

/-!
# Lemma 2.11 for the GUE profile: the generator of one GUE-phase increment (`d = 2`)

The GUE-phase twin of the band identity `LoopGenN` (`Induction/HierVocab.lean`, proved in
`Induction/LoopGenN.lean`):

* `genMatGUE` is `genMat` (`Path/OneStep.lean`) with the band coordinate weight `gvar` replaced
  by the GUE one `gueVar` (`Endpoints.lean`: `1/N` on the diagonal, `1/(2N)` per real
  coordinate off the diagonal, `N = (W L)²`);
* `egtNGUE` is `egtN` (`Induction/HierVocab.lean`) with `SB ↦ SBgue = 1/L²`
  (`Universality/GUEPhase/Bootstrap.lean`);
* `loopGenGUE`: `genMatGUE(𝓛_{σ,a}) = primRhsGUE(𝓛) + egtNGUE` for loops of length `k ≥ 2`
  (`primRhsGUE = W² Σ_{k<l} 𝓛 S_GUE 𝓛`, `Bootstrap.lean`), `loopGenGUE_one` the same at
  `k = 1` (where `primRhsGUE` of a 1-loop is `0`).

## Proof (that of `LoopGenN`, with `gvar ↦ gueVar`, `SB ↦ SBgue`)

0. The GUE contraction chain (section `Contraction`).  The chain
   `sum_coordinateSecondWordDeriv_allCuts` states `gvar` and `SB` literally, so its GUE analogue
   `Generator_sum_csd_allCuts` is proved here.  Its only profile-dependent leaf is
   `Generator_leaf`: `Σ_c gueVar_c tr(A D_c C D_c) = N⁻¹ tr A tr C`, from
   `trace_coordinate_real/imag/diag` (`Hierarchy/ContractionDirections.lean`), the vanishing of the
   unused coordinates, and the weights `1/N` (diagonal) and `2 · 1/(2N)` (the two real coordinates
   of an off-diagonal pair).  `Generator_blockContraction` rewrites it in block notation with
   `W² Σ_{p,q} tr(A E_p) SBgue_{pq} tr(C E_q)` (`Σ_p E_p = W⁻² I`).  The rest is the proof of
   `sum_gsigCoordinateSecondDeriv_word`, `sum_sameEdge_cutLoops`, `sum_twoEdge_mixed_*`,
   `sum_coordinateSecondWordDeriv_trace_positions` and `…_allCuts` with this leaf.
1. Matrix bridge `M = Xmat ω_M`, so `HflowBlock 1 ω_M = blockMat M`.
2. The line Hessian of `genMatGUE` along `coordinateMatrix c` is the coordinate Hessian at the
   auxiliary flow time `1`; `Generator_sum_csd_allCuts` contracts it into same-edge and pair cuts.
3. Spectral bridge (it does not see the profile): the `v`-derivative of the loop is a sum of
   scalar insertions, turned into single-edge cuts by `neg_trace_scalarDrift_cutGlue_split`.
4. The `m`-cancellation uses only the column sums `Σ_a SBgue_{ab} = 1`.
5. Reindexing of the `edgeSplits`/`pairSplits` list sums into the `Finset.Icc`/`Finset.Ioc` sums of
   `egtNGUE` and `primRhsGUE`.

Every helper is `private` or prefixed `Generator_`.  The hypothesis `3 ≤ L` is carried but unused:
the column sums of `SBgue` need only `NeZero L`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open Matrix RBM RBM.Gauss RBM.Path
open RBM.Ind (LLf)

/-! ## 0. The two definitions -/

section Defs

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The generator of one GUE-phase increment for the loop functional,
`½ ∑_c gueVar(c) ∂²_c Φ_u(M) + ∂_u Φ_u(M)` (`genMat` with `gvar ↦ gueVar`). -/
def genMatGUE (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : Coord L W, ((RBM.Endpoints.gueVar L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) (spectralZ E u) I)) 0 +
    deriv (fun v : ℝ => gloop L W (blockMat M) (spectralZ E v) I) u

/-- `𝓔^{(G̃)}` of the GUE phase (`egtN` with `SB ↦ SBgue`). -/
def egtNGUE (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    avgErr L W E u M (I.σ.getD (k - 1) false) a * RBM.Univ.GUEPhase.SBgue L a b *
      RBM.Ind.LLf L W E u M (I.cutGlue k b)

end Defs

/-! ## 1. The GUE contraction chain -/

section Contraction

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- A diagonal GUE coordinate has variance `N⁻¹`, `N = (W L)²`. -/
private theorem Generator_gueVar_diag (i : Idx L W) (b : Bool) :
    ((RBM.Endpoints.gueVar L W (i, i, b) : NNReal) : ℝ) = ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Endpoints.gueVar]

/-- An off-diagonal GUE coordinate has variance `(2N)⁻¹`. -/
private theorem Generator_gueVar_offDiag {i j : Idx L W} (b : Bool) (hij : i ≠ j) :
    ((RBM.Endpoints.gueVar L W (i, j, b) : NNReal) : ℝ) = (2 * (((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Endpoints.gueVar, hij]

/-- An upper-triangular sum, with its transposed term, plus the diagonal is the full
ordered-pair sum. -/
private theorem Generator_sum_orderedPairs_from_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℕ) (hkey : Function.Injective key)
    (S : ι → ι → ℂ) (hS : ∀ i j, S i j = S j i)
    (f : ι → ι → ℂ) :
    ∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0) =
      ∑ i : ι, ∑ j : ι, S i j * f i j := by
  classical
  have point (i j : ι) : S i j * f i j =
      (if key i < key j then S i j * f i j else 0) +
      (if i = j then S i i * f i i else 0) +
      (if key j < key i then S i j * f i j else 0) := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
    · have hij : i = j := hkey h
      subst j
      simp
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
  have hswap :
      (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) =
      (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hS]
  calc
    (∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0)) =
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : key i < key j
          · have hne : i ≠ j := by
              intro he
              subst j
              exact (lt_irrefl _) hij
            simp [hij, hne, mul_add]
          · simp [hij]
    _ = (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
          rw [hswap]
    _ = ∑ i : ι, ∑ j : ι, S i j * f i j := by
          symm
          calc
            (∑ i : ι, ∑ j : ι, S i j * f i j) =
                ∑ i : ι, ∑ j : ι,
                  ((if key i < key j then S i j * f i j else 0) +
                   (if i = j then S i i * f i i else 0) +
                   (if key j < key i then S i j * f i j else 0)) := by
                    refine Finset.sum_congr rfl fun i _ =>
                      Finset.sum_congr rfl fun j _ => point i j
            _ = _ := by simp only [Finset.sum_add_distrib]

/-- **The GUE coordinate contraction** (leaf): the sum over all product coordinates of
`gueVar_c tr(A D_c C D_c)` is `N⁻¹ tr A tr C`, `N = (W L)²`. -/
private theorem Generator_leaf (A C : Matrix (Idx L W) (Idx L W) ℂ) :
    ∑ c : Coord L W, ((RBM.Endpoints.gueVar L W c : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W c * C * coordinateMatrix L W c) =
      (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * ((∑ i, A i i) * (∑ j, C j j)) := by
  classical
  have splitCoord (f : Coord L W → ℂ) :
      ∑ c : Coord L W, f c =
        ∑ i : Idx L W, ∑ j : Idx L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx L W × Bool => f (i, jb))
  rw [splitCoord]
  have hpoint (i j : Idx L W) :
      ∑ b : Bool, ((RBM.Endpoints.gueVar L W (i, j, b) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix L W (i, j, b) * C * coordinateMatrix L W (i, j, b)) =
      (if idxKey L W i < idxKey L W j then
        (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * (A i i * C j j + A j j * C i i)
       else if i = j then (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * (A i i * C i i) else 0) := by
    rcases idxKey_lt_or_eq_or_lt L W i j with h | h | h
    · have hne : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      have hv (b : Bool) : ((RBM.Endpoints.gueVar L W (i, j, b) : ℝ) : ℂ) =
          (2 * (((W * L) ^ 2 : ℕ) : ℂ))⁻¹ := by
        have hr := Generator_gueVar_offDiag (L := L) (W := W) b hne
        rw [hr]
        push_cast
        rfl
      simp only [h, ite_true, Fintype.sum_bool]
      rw [trace_coordinate_real L W A C h, trace_coordinate_imag L W A C h, hv true, hv false]
      ring
    · subst j
      have hv (b : Bool) : ((RBM.Endpoints.gueVar L W (i, i, b) : ℝ) : ℂ) =
          (((W * L) ^ 2 : ℕ) : ℂ)⁻¹ := by
        rw [Generator_gueVar_diag (L := L) (W := W) i b]
        push_cast
        rfl
      simp only [lt_irrefl, ite_false, ite_true, Fintype.sum_bool]
      rw [coordinateMatrix_diag_imag_zero L W i, trace_coordinate_diag L W A C i, hv true]
      simp
    · have hne : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      have hrev : ¬ idxKey L W i < idxKey L W j := not_lt_of_ge (le_of_lt h)
      simp only [hrev, hne, ite_false, Fintype.sum_bool]
      rw [coordinateMatrix_lower_zero L W h true, coordinateMatrix_lower_zero L W h false]
      simp
  simp_rw [hpoint]
  rw [Generator_sum_orderedPairs_from_upper (idxKey L W) (idxKey_injective L W)
    (fun _ _ => (((W * L) ^ 2 : ℕ) : ℂ)⁻¹) (fun _ _ => rfl) (fun i j => A i i * C j j)]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- Relabelling preserves the trace. -/
private theorem Generator_trace_blockRelabel (M : Matrix (Idx L W) (Idx L W) ℂ) :
    Matrix.trace (blockRelabel L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, blockRelabel]
  exact (Equiv.sum_comp (splitEquiv L W).symm (fun i => M i i))

private theorem Generator_blockRelabel_mul (M N : Matrix (Idx L W) (Idx L W) ℂ) :
    blockRelabel L W (M * N) = blockRelabel L W M * blockRelabel L W N :=
  (Matrix.submatrix_mul_equiv M N
    (splitEquiv L W).symm (splitEquiv L W).symm (splitEquiv L W).symm).symm

/-- The block trace pattern in physical-site coordinates. -/
private theorem Generator_trace_coordinateBlock_pair
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (γ : Coord L W) :
    Matrix.trace (A * coordinateBlock L W γ * C * coordinateBlock L W γ) =
    Matrix.trace (A.submatrix (split L W) (split L W) * coordinateMatrix L W γ *
      C.submatrix (split L W) (split L W) * coordinateMatrix L W γ) := by
  let P := A.submatrix (split L W) (split L W)
  let Q := C.submatrix (split L W) (split L W)
  have hA : blockRelabel L W P = A := blockRelabel_submatrix_split L W A
  have hC : blockRelabel L W Q = C := blockRelabel_submatrix_split L W C
  change Matrix.trace (A * blockRelabel L W (coordinateMatrix L W γ) *
    C * blockRelabel L W (coordinateMatrix L W γ)) =
    Matrix.trace (P * coordinateMatrix L W γ * Q * coordinateMatrix L W γ)
  rw [← hA, ← hC, ← Generator_blockRelabel_mul, ← Generator_blockRelabel_mul,
    ← Generator_blockRelabel_mul]
  exact Generator_trace_blockRelabel L W _

/-- **The GUE coordinate contraction in block notation**: the analogue of
`sum_coordinateBlock_trace_pair` (`Hierarchy/ContractionSecondLoopSameEdge.lean`) with
`gvar ↦ gueVar`, `SB ↦ SBgue`. -/
private theorem Generator_blockContraction
    (A C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (A * coordinateBlock L W γ * C * coordinateBlock L W γ) =
      (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
        Matrix.trace (A * Eblk L W p) * SBgue L p q * Matrix.trace (C * Eblk L W q) := by
  simp_rw [Generator_trace_coordinateBlock_pair (L := L) (W := W) A C]
  rw [Generator_leaf]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have htr (B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
      ∑ i : Idx L W, B.submatrix (split L W) (split L W) i i = Matrix.trace B :=
    Equiv.sum_comp (splitEquiv L W) (fun p => B p p)
  have hsumE (B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
      ∑ p : Z2 L, Matrix.trace (B * Eblk L W p) = ((W : ℂ)⁻¹ ^ 2) * Matrix.trace B := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_Eblk L W, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, smul_eq_mul]
  simp only [SBgue_apply]
  have h2 : ∑ p : Z2 L, ∑ q : Z2 L,
      Matrix.trace (A * Eblk L W p) * ((L : ℂ) ^ 2)⁻¹ * Matrix.trace (C * Eblk L W q) =
      ((L : ℂ) ^ 2)⁻¹ * ((∑ p : Z2 L, Matrix.trace (A * Eblk L W p)) *
        (∑ q : Z2 L, Matrix.trace (C * Eblk L W q))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h2, hsumE, hsumE, htr, htr]
  push_cast
  field_simp

/-! ### The same-edge contraction -/

/-- The cut-loop product attached to one same-edge position, without its common coefficient
`2uW²` (`sameEdgeCutValue`, `Hierarchy/ContractionSecondLoopAllCuts.lean`, with
`SB ↦ SBgue`). -/
private def Generator_sameEdgeCutValue (u : ℝ) (ω : Ω L W) (z : ℂ)
    (e : EdgeSplit (Bool × Z2 L)) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L e.before
  let I₂ := segmentLoopIdx L e.after
  ∑ p : Z2 L, ∑ q : Z2 L,
    gloop L W H z
      ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
        e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
      SBgue L p q * gloop L W H z ⟨[e.selected.1], [q]⟩

/-- The left/right cut-loop product attached to one pair of distinct edges, without its common
coefficient (`pairCutValue`, `Hierarchy/ContractionSecondLoopAllCuts.lean`, with
`SB ↦ SBgue`). -/
private def Generator_pairCutValue (u : ℝ) (ω : Ω L W) (z : ℂ)
    (p : PairSplit (Bool × Z2 L)) : ℂ :=
  let H := HflowBlock L W u ω
  let I₁ := segmentLoopIdx L p.before
  let I₂ := segmentLoopIdx L p.middle
  let I₃ := segmentLoopIdx L p.after
  ∑ v : Z2 L, ∑ w : Z2 L,
    gloop L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueL
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
      SBgue L v w *
    gloop L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Z2 L)).cutGlueR
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)

/-- The weighted same-edge term at one chosen position of a finite word (GUE version of
`sum_gsigCoordinateSecondDeriv_word`, `Hierarchy/ContractionSecondLoopSameEdgeWord.lean`). -/
private theorem Generator_sum_gsigSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ) (s : Bool) (a : Z2 L)
    (P T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    let G := Gsig (HflowBlock L W u ω) z s
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a) * T) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ∑ p : Z2 L, ∑ q : Z2 L,
          Matrix.trace (((G * Eblk L W a * T * P) * G) * Eblk L W p) *
            SBgue L p q * Matrix.trace (G * Eblk L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_word L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : Coord L W,
          (((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
            Matrix.trace (((Gsig (HflowBlock L W u ω) z s * Eblk L W a *
              T * P) * Gsig (HflowBlock L W u ω) z s) *
              coordinateBlock L W γ * Gsig (HflowBlock L W u ω) z s *
              coordinateBlock L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [Generator_blockContraction]
      ring

/-- The same-edge variance contraction at the specified split of a finite loop word (GUE
version of `sum_sameEdge_cutLoops`, `Hierarchy/ContractionSecondLoopSameEdgeCut.lean`). -/
private theorem Generator_sum_sameEdge_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (s : Bool) (a : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock L W u ω
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let T := gloopProd L W H z ⟨σ₂, a₂⟩
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv L W u ω γ z s * Eblk L W a) * T) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
      ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W H z
          ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ *
          SBgue L p q * gloop L W H z ⟨[s], [q]⟩ := by
  dsimp only
  rw [Generator_sum_gsigSecondDeriv_word L W u hu ω z s a
    (gloopProd L W (HflowBlock L W u ω) z ⟨σ₁, a₁⟩)
    (gloopProd L W (HflowBlock L W u ω) z ⟨σ₂, a₂⟩)]
  simp_rw [trace_sameEdge_cutLoop L W (HflowBlock L W u ω) z
    σ₁ σ₂ a₁ a₂ s a _ h₁ h₂,
    trace_sameEdge_oneLoop L W (HflowBlock L W u ω) z s]

/-- At any chosen edge, the weighted second-coordinate insertion is the GUE same-edge cut-loop
double sum (`sum_coordinateSameEdgeTerm_cutLoops`,
`Hierarchy/ContractionSameEdgePositionCut.lean`). -/
private theorem Generator_sum_sameEdgeTerm
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm L W u ω γ z e) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 * Generator_sameEdgeCutValue L W u ω z e := by
  have h₁ : (e.before.map Prod.fst).length = (e.before.map Prod.snd).length :=
    segmentLoopIdx_WF L e.before
  have h₂ : (e.after.map Prod.fst).length = (e.after.map Prod.snd).length :=
    segmentLoopIdx_WF L e.after
  unfold Generator_sameEdgeCutValue
  dsimp only [coordinateSameEdgeTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd L W u ω z e.after]
  exact Generator_sum_sameEdge_cutLoops L W u hu ω z
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 h₁ h₂

/-! ### The two-edge contraction -/

omit [NeZero W] in
private theorem Generator_trace_two_smul (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

private theorem Generator_trace_twoEdge_deriv_signs
    (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ)
    (P M T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (s t : Bool) (a c : Z2 L) :
    let H := HflowBlock L W u ω
    let B := Real.sqrt u • coordinateBlock L W γ
    Matrix.trace (P * (gsigCoordinateDeriv L W u ω γ z s * Eblk L W a) * M *
      (gsigCoordinateDeriv L W u ω γ z t * Eblk L W c) * T) =
    Matrix.trace (P * (Gsig H z s * B * Gsig H z s * Eblk L W a) * M *
      (Gsig H z t * B * Gsig H z t * Eblk L W c) * T) := by
  simp only [gsigCoordinateDeriv, neg_mul, mul_neg, neg_neg]

/-- Covariance summation of one ordered, unscaled two-edge cross term (GUE version of
`sum_twoEdge_mixed_cutChains`, `Hierarchy/ContractionSecondLoop.lean`). -/
private theorem Generator_sum_twoEdge_mixed_cutChains
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (cutLeftChain L W H z σ₁ σ₃ a₁ a₃ s t c *
          coordinateBlock L W γ * cutRightChain L W H z σ₂ a₂ s t a *
          coordinateBlock L W γ) =
    (W : ℂ) ^ 2 * ∑ u : Z2 L, ∑ v : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
        SBgue L u v *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  rw [Generator_blockContraction]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [trace_cutLeftChain_Eblk L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c u h₁ h₂,
    trace_cutRightChain_Eblk L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c v h₁ h₂]

/-- One ordered cross term, after the GUE coordinate weights are summed (GUE version of
`sum_twoEdge_mixed_coordinate`, `Hierarchy/ContractionSecondLoop.lean`). -/
private theorem Generator_sum_twoEdge_mixed_coordinate
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock L W u ω
    let Gs := Gsig H z s
    let Gt := Gsig H z t
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let M := gloopProd L W H z ⟨σ₂, a₂⟩
    let T := gloopProd L W H z ⟨σ₃, a₃⟩
    (∑ γ : Coord L W,
      let B := Real.sqrt u • coordinateBlock L W γ
      (((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gs * B * Gs * Eblk L W a) * M *
          (Gt * B * Gt * Eblk L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SBgue L p q *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_mixed_eq_cutChains L W]
  simp_rw [Generator_trace_two_smul L W u hu]
  calc
    _ = (u : ℂ) * ∑ γ : Coord L W,
          (((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
            Matrix.trace (cutLeftChain L W (HflowBlock L W u ω) z
              σ₁ σ₃ a₁ a₃ s t c * coordinateBlock L W γ *
              cutRightChain L W (HflowBlock L W u ω) z
                σ₂ a₂ s t a * coordinateBlock L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [Generator_sum_twoEdge_mixed_cutChains L W (HflowBlock L W u ω) z
        σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂]
      ring

/-- The same contraction written with the two actual first derivatives of the signed Green
factors in `coordinateSecondWordDeriv` (GUE version of `sum_twoEdge_mixed_deriv`,
`Hierarchy/ContractionSecondLoop.lean`). -/
private theorem Generator_sum_twoEdge_mixed_deriv
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Z2 L))
    (s t : Bool) (a c : Z2 L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock L W u ω
    let P := gloopProd L W H z ⟨σ₁, a₁⟩
    let M := gloopProd L W H z ⟨σ₂, a₂⟩
    let T := gloopProd L W H z ⟨σ₃, a₃⟩
    (∑ γ : Coord L W,
      (((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (P *
          (gsigCoordinateDeriv L W u ω γ z s * Eblk L W a) * M *
          (gsigCoordinateDeriv L W u ω γ z t * Eblk L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SBgue L p q *
      gloop L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Z2 L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [Generator_trace_twoEdge_deriv_signs L W u ω]
  exact Generator_sum_twoEdge_mixed_coordinate L W u hu ω z
    σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

/-- At any chosen ordered pair of edges, the GUE variance contraction is the corresponding
left/right cut-loop double sum (`sum_coordinatePairTerm_cutLoops`,
`Hierarchy/ContractionPairPositionCut.lean`). -/
private theorem Generator_sum_pairTerm
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ) (p : PairSplit (Bool × Z2 L)) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm L W u ω γ z p) =
      (u : ℂ) * (W : ℂ) ^ 2 * Generator_pairCutValue L W u ω z p := by
  have h₁ : (p.before.map Prod.fst).length = (p.before.map Prod.snd).length :=
    segmentLoopIdx_WF L p.before
  have h₂ : (p.middle.map Prod.fst).length = (p.middle.map Prod.snd).length :=
    segmentLoopIdx_WF L p.middle
  unfold Generator_pairCutValue
  dsimp only [coordinatePairTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd L W u ω z p.after]
  exact Generator_sum_twoEdge_mixed_deriv L W u hu ω z
    (p.before.map Prod.fst) (p.middle.map Prod.fst) (p.after.map Prod.fst)
    (p.before.map Prod.snd) (p.middle.map Prod.snd) (p.after.map Prod.snd)
    p.first.1 p.second.1 p.first.2 p.second.2 h₁ h₂

/-! ### The full cut formula -/

private theorem Generator_sum_weighted_trace_list {α : Type*}
    (es : List α) (w : Coord L W → ℂ)
    (T : Coord L W → α → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :
    ∑ γ : Coord L W, w γ * Matrix.trace ((es.map (T γ)).sum) =
      (es.map (fun e => ∑ γ : Coord L W, w γ * Matrix.trace (T γ e))).sum := by
  induction es with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Matrix.trace_zero, mul_zero,
        Finset.sum_const_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, mul_add,
        Finset.sum_add_distrib, ih]

omit [NeZero L] [NeZero W] in
private theorem Generator_list_sum_map_mul_left {α : Type*} (c : ℂ)
    (es : List α) (f : α → ℂ) :
    (es.map (fun e => c * f e)).sum = c * (es.map f).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- Exact finite exchange of coordinate and edge-position sums in the traced second product
rule, with the GUE weights (`sum_coordinateSecondWordDeriv_trace_positions`,
`Hierarchy/ContractionSecondDerivativeTraceSum.lean`). -/
private theorem Generator_sum_csd_trace_positions
    (u : ℝ) (ω : Ω L W) (z : ℂ) (l : List (Bool × Z2 L)) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l) =
    ((edgeSplits l).map (fun e => ∑ γ : Coord L W,
      ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm L W u ω γ z e))).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p => ∑ γ : Coord L W,
      ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm L W u ω γ z p))).sum := by
  simp_rw [coordinateSecondWordDeriv_eq_position_sums L W]
  simp only [two_nsmul, Matrix.trace_add, mul_add, Finset.sum_add_distrib,
    coordinateSameEdgeSum, coordinatePairSum]
  rw [Generator_sum_weighted_trace_list L W (edgeSplits l),
    Generator_sum_weighted_trace_list L W (pairSplits l)]
  ring

/-- **The GUE all-cuts formula**: the full finite samplewise cut formula for any signed word, at
the GUE weights.  Both same-edge and distinct-edge families have coefficient `2uW²`
(`sum_coordinateSecondWordDeriv_allCuts`, `Hierarchy/ContractionSecondLoopAllCuts.lean`). -/
private theorem Generator_sum_csd_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω L W) (z : ℂ) (l : List (Bool × Z2 L)) :
    ∑ γ : Coord L W, ((RBM.Endpoints.gueVar L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv L W u ω γ z l) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((edgeSplits l).map (Generator_sameEdgeCutValue L W u ω z)).sum +
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ 2 *
        ((pairSplits l).map (Generator_pairCutValue L W u ω z)).sum := by
  rw [Generator_sum_csd_trace_positions L W u ω z l]
  simp_rw [Generator_sum_sameEdgeTerm L W u hu ω z]
  simp_rw [Generator_sum_pairTerm L W u hu ω z]
  rw [Generator_list_sum_map_mul_left, Generator_list_sum_map_mul_left]
  ring

end Contraction

/-! ## 2. The matrix bridge -/

section MatrixBridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The real coordinates of a matrix: real parts on `true`, imaginary parts on `false`. -/
private def Generator_omega (M : Matrix (Idx L W) (Idx L W) ℂ) : Ω L W :=
  fun c => if c.2.2 then (M c.1 c.2.1).re else (M c.1 c.2.1).im

/-- A Hermitian matrix is the Gaussian matrix of its coordinates. -/
private theorem Generator_Xmat_omega {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    Xmat L W (Generator_omega M) = M := by
  ext i j
  rw [Xmat_apply, Xentry]
  simp only [Generator_omega, ite_true, Bool.false_eq_true, ite_false]
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
private theorem Generator_HflowBlock_one {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    HflowBlock L W 1 (Generator_omega M) = blockMat M := by
  rw [HflowBlock, Hflow, Real.sqrt_one, Complex.ofReal_one, one_smul, Generator_Xmat_omega hM]
  rfl

end MatrixBridge

/-! ## 3. The second-derivative bridge -/

section SecondBridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The line Hessian of the loop along `coordinateMatrix c` at a Hermitian `M` is the coordinate
Hessian of the flow sample `ω_M` at the auxiliary time `1`. -/
private theorem Generator_deriv2 {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (c : Coord L W) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) z I)) 0 =
      Matrix.trace (coordinateSecondWordDeriv L W 1 (Generator_omega M) c z (I.σ.zip I.a)) := by
  set ω := Generator_omega M with hω
  set g : ℝ → ℂ := fun s => gloop L W (HflowBlock L W 1 (Function.update ω c s)) z I with hg
  have hfg : (fun y : ℝ =>
      gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) z I) =
      fun y => g (y + ω c) := by
    funext y
    simp only [hg, HflowBlock_update, hω, Generator_HflowBlock_one hM, Real.sqrt_one, one_mul,
      add_sub_cancel_right]
    congr 1
  rw [hfg]
  have h1 : deriv (fun y : ℝ => g (y + ω c)) = fun y => deriv g (y + ω c) := by
    funext y
    exact deriv_comp_add_const _ _ _
  rw [h1, deriv_comp_add_const, zero_add]
  exact (hasDerivAt_deriv_gloop_update L W 1 ω c hz I hI).deriv

end SecondBridge

/-! ## 4. The spectral bridge at a general Hermitian block matrix -/

section SpectralBridge

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The signed word `Π G(σ) E_a` of a list of edges, at a general block matrix. -/
private def Generator_word (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  l.foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

private theorem Generator_word_eq (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (l : List (Bool × Z2 L)) :
    Generator_word H z l = gloopProd L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]
  rfl

/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix
(the generic-`H` form of the private `OneStep_hasDerivAt_spec0`). -/
private theorem Generator_hasDerivAt_Gsig_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
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
private def Generator_edgeTerm (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (E u : ℝ)
    (e : EdgeSplit (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  -(Generator_word H (spectralZ E u) e.before *
    (Gsig H (spectralZ E u) e.selected.1 *
        (spectralMSign E e.selected.1 • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) *
      (Gsig H (spectralZ E u) e.selected.1 * Eblk L W e.selected.2 *
        Generator_word H (spectralZ E u) e.after)))

/-- The product rule over the word: the spectral derivative is the sum of the edge insertions. -/
private theorem Generator_hasDerivAt_word_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (l : List (Bool × Z2 L)) :
    HasDerivAt (fun v : ℝ => Generator_word H (spectralZ E v) l)
      (((edgeSplits l).map (Generator_edgeTerm H E u)).sum) u := by
  induction l with
  | nil =>
      simpa [Generator_word, edgeSplits] using
        hasDerivAt_const u (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
  | cons p l ih =>
      have h := ((Generator_hasDerivAt_Gsig_spec hH hE hu p.1).mul_const (Eblk L W p.2)).mul ih
      have hfun : (fun v : ℝ => Gsig H (spectralZ E v) p.1 * Eblk L W p.2) *
          (fun v : ℝ => Generator_word H (spectralZ E v) l) =
          fun v : ℝ => Generator_word H (spectralZ E v) (p :: l) := by
        funext v
        rfl
      rw [hfun] at h
      refine h.congr_deriv ?_
      have hcons : ∀ e : EdgeSplit (Bool × Z2 L),
          Generator_edgeTerm H E u ⟨p :: e.before, e.selected, e.after⟩ =
            (Gsig H (spectralZ E u) p.1 * Eblk L W p.2) * Generator_edgeTerm H E u e := by
        intro e
        simp only [Generator_edgeTerm, Generator_word, List.foldr_cons, Matrix.mul_neg,
          Matrix.mul_assoc]
      simp only [edgeSplits, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        hcons, List.sum_map_mul_left]
      simp only [Generator_edgeTerm, Generator_word, List.foldr_nil, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.neg_mul]

/-- The spectral derivative of a loop at a fixed Hermitian block matrix. -/
private theorem Generator_deriv_spec {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (I : LoopIdx (Z2 L)) :
    deriv (fun v : ℝ => gloop L W H (spectralZ E v) I) u =
      ((edgeSplits (I.σ.zip I.a)).map
        (fun e => Matrix.trace (Generator_edgeTerm H E u e))).sum := by
  set T : Matrix (BlockIndex L W) (BlockIndex L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (BlockIndex L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (Generator_hasDerivAt_word_spec hH hE hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => gloop L W H (spectralZ E v) I) =
      fun v : ℝ => Matrix.trace (Generator_word H (spectralZ E v) (I.σ.zip I.a)) := by
    funext v
    rfl
  rw [hfun, h.deriv, Matrix.trace_list_sum, List.map_map]
  rfl

/-- One edge insertion is a sum of single-edge cuts. -/
private theorem Generator_trace_edgeTerm (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (E u : ℝ) (e : EdgeSplit (Bool × Z2 L)) :
    Matrix.trace (Generator_edgeTerm H E u e) =
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
  rw [← h, Generator_edgeTerm, Matrix.trace_neg, Generator_word_eq, Generator_word_eq]

end SpectralBridge

/-! ## 5. Reindexing the cut enumerations -/

section Reindex

/-- A list sum over `List.range n` is the `Finset.range` sum. -/
private theorem Generator_sum_listRange (n : ℕ) (f : ℕ → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `Σ_{i<n} F(i+1) = Σ_{k ∈ [1,n]} F k`. -/
private theorem Generator_sum_range_Icc (n : ℕ) (F : ℕ → ℂ) :
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
private theorem Generator_sum_edgeSplits {α : Type*} (l : List α) (f : EdgeSplit α → ℂ)
    (F : ℕ → ℂ) (h : ∀ e ∈ edgeSplits l, f e = F (e.before.length + 1)) :
    ((edgeSplits l).map f).sum = ∑ k ∈ Finset.Icc 1 l.length, F k := by
  rw [List.map_congr_left h]
  have hmap : (edgeSplits l).map (fun e => F (e.before.length + 1)) =
      ((edgeSplits l).map (fun e => e.before.length)).map (fun i => F (i + 1)) := by
    rw [List.map_map]
    rfl
  rw [hmap, edgeSplits_prefix_lengths, Generator_sum_listRange, Generator_sum_range_Icc]

/-- The sum of a `flatMap` is the sum of the inner sums. -/
private theorem Generator_sum_flatMap {α β : Type*} (xs : List α) (g : α → List β) (f : β → ℂ) :
    ((xs.flatMap g).map f).sum = (xs.map fun x => ((g x).map f).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

/-- A sum over the pair enumeration, whose summand depends only on the two one-based positions. -/
private theorem Generator_sum_pairSplits {α : Type*} (l : List α) (f : PairSplit α → ℂ)
    (F : ℕ → ℕ → ℂ)
    (h : ∀ p ∈ pairSplits l,
      f p = F (p.before.length + 1) (p.before.length + p.middle.length + 2)) :
    ((pairSplits l).map f).sum =
      ∑ k ∈ Finset.Icc 1 l.length, ∑ l' ∈ Finset.Ioc k l.length, F k l' := by
  rw [List.map_congr_left h, pairSplits, Generator_sum_flatMap]
  refine Generator_sum_edgeSplits l _ _ fun e he => ?_
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have hr := edgeSplits_reconstruct l e he
    rw [← hr, List.length_append, List.length_cons]
    omega
  rw [List.map_map]
  rw [Generator_sum_edgeSplits e.after _
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

/-! ## 6. Identifying each cut term with the loop's own cuts -/

section Cuts

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A selected edge of the zipped word of a well-formed loop splits that loop. -/
private theorem Generator_edge_eq (I : LoopIdx (Z2 L)) (hI : I.WF)
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
private theorem Generator_pair_eq (I : LoopIdx (Z2 L)) (hI : I.WF)
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
private theorem Generator_getD (b a : List (Bool × Z2 L)) (s : Bool) :
    (b.map Prod.fst ++ s :: a.map Prod.fst).getD (b.length + 1 - 1) false = s := by
  rw [Nat.add_sub_cancel, List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The rotated same-edge loop is the single-edge cut of the original loop. -/
private theorem Generator_gloop_same (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
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
private theorem Generator_sameEdge {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Z2 L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Generator_sameEdgeCutValue L W 1 (Generator_omega M) z e =
      ∑ p : Z2 L, ∑ q : Z2 L, gloop L W (blockMat M) z (I.cutGlue (e.before.length + 1) p) *
        SBgue L p q * Matrix.trace (Gsig (blockMat M) z (I.σ.getD (e.before.length + 1 - 1) false) *
          Eblk L W q) := by
  have hIe := Generator_edge_eq I hI e he
  simp only [Generator_sameEdgeCutValue, segmentLoopIdx, Generator_HflowBlock_one hM]
  rw [hIe, Generator_getD]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Generator_gloop_same]
  congr 1
  simp [gloop]

/-- The pair cut value at two selected edges, as a function of their one-based positions. -/
private theorem Generator_pairCut {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (E u : ℝ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (p : PairSplit (Bool × Z2 L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    Generator_pairCutValue L W 1 (Generator_omega M) (spectralZ E u) p =
      ∑ v : Z2 L, ∑ w : Z2 L,
        LLf L W E u M (I.cutGlueL (p.before.length + 1)
            (p.before.length + p.middle.length + 2) v) * SBgue L v w *
          LLf L W E u M (I.cutGlueR (p.before.length + 1)
            (p.before.length + p.middle.length + 2) w) := by
  have hIp := Generator_pair_eq I hI p hp
  simp only [Generator_pairCutValue, segmentLoopIdx, Generator_HflowBlock_one hM, List.length_map]
  rw [← hIp]
  rfl

/-- The spectral insertion at a selected edge, as a function of its one-based position. -/
private theorem Generator_specEdge (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (E u : ℝ) (I : LoopIdx (Z2 L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Z2 L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Matrix.trace (Generator_edgeTerm H E u e) =
      -(spectralMSign E (I.σ.getD (e.before.length + 1 - 1) false) * (W : ℂ) ^ 2) *
        ∑ b : Z2 L, gloop L W H (spectralZ E u) (I.cutGlue (e.before.length + 1) b) := by
  have hIe := Generator_edge_eq I hI e he
  rw [Generator_trace_edgeTerm, List.length_map]
  conv_rhs => rw [hIe, Generator_getD]

end Cuts

/-! ## 7. The single-edge algebra -/

section Assembly

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)`. -/
private theorem Generator_avgErr (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (a : Z2 L) :
    avgErr L W E u M σ a =
      Matrix.trace (Gsig (blockMat M) (spectralZ E u) σ * Eblk L W a) - spectralMSign E σ := by
  rw [avgErr, greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, trace_Eblk_eq_one, smul_eq_mul, mul_one]
  rfl

/-- Column sums of `S^{(B)}_{GUE}` are `1` (`L² · L⁻² = 1`). -/
private theorem Generator_sum_SBgue_col (b : Z2 L) : ∑ a : Z2 L, SBgue L a b = 1 := by
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  simp only [SBgue_apply, Finset.sum_const, Finset.card_univ, Z2, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul]
  push_cast
  field_simp

/-- `Σ_{a,b} (t_a - m) S_{ab} g_b = Σ_{p,q} g_p S_{pq} t_q - m Σ_b g_b`. -/
private theorem Generator_sum_algebra (f g : Z2 L → ℂ) (m : ℂ) :
    ∑ a' : Z2 L, ∑ b' : Z2 L, (g a' - m) * SBgue L a' b' * f b' =
      ∑ p : Z2 L, ∑ q : Z2 L, f p * SBgue L p q * g q - m * ∑ p : Z2 L, f p := by
  have hS : ∀ p q : Z2 L, SBgue L p q = SBgue L q p := fun p q => rfl
  have h1 : ∑ a' : Z2 L, ∑ b' : Z2 L, g a' * SBgue L a' b' * f b' =
      ∑ p : Z2 L, ∑ q : Z2 L, f p * SBgue L p q * g q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hS q p]
    ring
  have h2 : ∑ a' : Z2 L, ∑ b' : Z2 L, m * SBgue L a' b' * f b' = m * ∑ p : Z2 L, f p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, Generator_sum_SBgue_col, mul_one]
  rw [← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- The same-edge cuts and the spectral cuts of one edge combine into its `𝓔^{(G̃)}` term. -/
private theorem Generator_edge_algebra (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) (k : ℕ) :
    (W : ℂ) ^ 2 * ∑ p : Z2 L, ∑ q : Z2 L,
        gloop L W (blockMat M) (spectralZ E u) (I.cutGlue k p) * SBgue L p q *
          Matrix.trace (Gsig (blockMat M) (spectralZ E u) (I.σ.getD (k - 1) false) *
            Eblk L W q) +
      -(spectralMSign E (I.σ.getD (k - 1) false) * (W : ℂ) ^ 2) *
        ∑ b : Z2 L, gloop L W (blockMat M) (spectralZ E u) (I.cutGlue k b) =
    (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
      avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b * LLf L W E u M (I.cutGlue k b) := by
  simp only [Generator_avgErr]
  rw [Generator_sum_algebra (fun b => LLf L W E u M (I.cutGlue k b))
    (fun a => Matrix.trace (Gsig (blockMat M) (spectralZ E u) (I.σ.getD (k - 1) false) *
      Eblk L W a))]
  simp only [LLf]
  ring

end Assembly

/-! ## 8. The assembly -/

/-- The core identity for every length, with `k` free (so `k = 1` and `k ≥ 2` are both
instances). -/
private theorem Generator_core (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ) (hE : |E| < 2) (u : ℝ)
    (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    genMatGUE L W E u M (loopOf σ a) =
      primRhsGUE L W (LLf L W E u M) (loopOf σ a) + egtNGUE L W E u M (loopOf σ a) := by
  set I : LoopIdx (Z2 L) := loopOf σ a with hIdef
  have hI : I.WF := by simp [hIdef, loopOf, LoopIdx.WF]
  have hlen : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, List.length_zip, hI.symm]
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  set l := I.σ.zip I.a with hl
  set ω := Generator_omega M with hω
  set z := spectralZ E u with hzdef
  -- the three families of cut terms as functions of the one-based positions
  set Fs : ℕ → ℂ := fun k' => ∑ p : Z2 L, ∑ q : Z2 L,
    gloop L W (blockMat M) z (I.cutGlue k' p) * SBgue L p q *
      Matrix.trace (Gsig (blockMat M) z (I.σ.getD (k' - 1) false) * Eblk L W q) with hFs
  set Fsp : ℕ → ℂ := fun k' => -(spectralMSign E (I.σ.getD (k' - 1) false) * (W : ℂ) ^ 2) *
    ∑ b : Z2 L, gloop L W (blockMat M) z (I.cutGlue k' b) with hFsp
  set Fp : ℕ → ℕ → ℂ := fun k' l' => ∑ v : Z2 L, ∑ w : Z2 L,
    LLf L W E u M (I.cutGlueL k' l' v) * SBgue L v w * LLf L W E u M (I.cutGlueR k' l' w) with hFp
  have hsame := Generator_sum_edgeSplits l (Generator_sameEdgeCutValue L W 1 ω z) Fs
    (fun e he => Generator_sameEdge hM z I hI e he)
  have hpair := Generator_sum_pairSplits l (Generator_pairCutValue L W 1 ω z) Fp
    (fun p hp => Generator_pairCut hM E u I hI p hp)
  have hspec := Generator_sum_edgeSplits l
    (fun e => Matrix.trace (Generator_edgeTerm (blockMat M) E u e)) Fsp
    (fun e he => Generator_specEdge (blockMat M) E u I hI e he)
  -- the left side
  have hlhs : genMatGUE L W E u M I =
      (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, Fs k' +
        (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k' I.length, Fp k' l' +
        ∑ k' ∈ Finset.Icc 1 I.length, Fsp k' := by
    rw [genMatGUE, Finset.sum_congr rfl fun c _ => by rw [Generator_deriv2 hM c hz I hI],
      Generator_sum_csd_allCuts L W 1 zero_le_one ω z l,
      Generator_deriv_spec hH hE hu1 I, hsame, hpair, hspec, hlen]
    push_cast
    ring
  have hedge : ∑ k' ∈ Finset.Icc 1 I.length, ((W : ℂ) ^ 2 * Fs k' + Fsp k') =
      (W : ℂ) ^ 2 * ∑ k' ∈ Finset.Icc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
        avgErr L W E u M (I.σ.getD (k' - 1) false) a * SBgue L a b *
          LLf L W E u M (I.cutGlue k' b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => Generator_edge_algebra E u M I k'
  rw [hlhs]
  unfold primRhsGUE primBilGUE egtNGUE
  rw [← hedge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hFp]
  ring

/-- **Lemma 2.11 for the GUE profile, loops of length `k ≥ 2`**:
`genMatGUE(𝓛_{σ,a}) = W² Σ_{k<l} 𝓛 S_GUE 𝓛 + 𝓔^{(G̃)}_{GUE}`, the first sum being
`primRhsGUE (𝓛)`. -/
theorem loopGenGUE :
    ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
        RBM.Univ.GUEPhase.genMatGUE L W E u M (loopOf σ a) =
          RBM.Univ.GUEPhase.primRhsGUE L W (RBM.Ind.LLf L W E u M) (loopOf σ a) +
            RBM.Univ.GUEPhase.egtNGUE L W E u M (loopOf σ a) := by
  intro L W _ _ E _hL hE u _hu0 hu1 M hM k _hk σ a
  exact Generator_core L W E hE u hu1 M hM σ a

/-- **The same at `k = 1`**, where `primRhsGUE` of a 1-loop is `0` (`Finset.Ioc 1 1 = ∅`). -/
theorem loopGenGUE_one :
    ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
      ∀ (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L),
        RBM.Univ.GUEPhase.genMatGUE L W E u M (loopOf σ a) =
          RBM.Univ.GUEPhase.egtNGUE L W E u M (loopOf σ a) := by
  intro L W _ _ E _hL hE u _hu0 hu1 M hM σ a
  have hlen : (loopOf σ a).length = 1 := by simp [loopOf, LoopIdx.length]
  have h0 : primRhsGUE L W (LLf L W E u M) (loopOf σ a) = 0 := by
    unfold primRhsGUE primBilGUE
    rw [hlen]
    simp
  rw [Generator_core L W E hE u hu1 M hM σ a, h0, zero_add]

/-! ## 9. Compiled instances -/

end RBM.Univ.GUEPhase

end
