/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.HypA
import RBM2D.Green.EntryDom
import RBM2D.Induction.PerTimeCalc
import RBM2D.Path.Bootstrap

/-!
# (7.45)G and (7.46)G for the stopped GUE-phase processes, part II (`d = 2`)

The pathwise assembly on the stopped processes, the per-step events and the fixed-point argument,
written against the public `Hyp_` interface of `HypA.lean`.

Proof idea.  On the good event, pathwise, the discrete Duhamel formula `Hyp_grid` holds at every
grid time `k ≤ σ*` with the bilinear drift (`primRhsGUE_sub`, `norm_primBilGUE_le`, `HypB_bil`),
the `E^{(G)}` drift (`norm_egtNGUE_le`, with `ε ≤ ‖G − m‖_max` + D4a + A3 + R6a for (7.45)G
(`HypB_entry_le`, `HypB_eG_745`) and `ε ≤ D₁` for (7.46)G (`HypB_eG_746`)) and the discretization
error of `K̃` (`Hyp_Kt_disc`); off the grid the exact linear interpolation of the affine prefactor
and the concavity of `√·` (`Hyp_interp_bound`); the exponent bookkeeping is `HypB_fixed`.

## Contents

* `HypB_entry_le`, `HypB_eG_745`, `HypB_eG_746`, `HypB_q_745`: the entry bound at the stopped grid
  times, the `E^{(G)}` drift lines and the martingale line;
* `HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range`: the per-step events;
* `HypB_fixed`, `HypB_step_le`, `HypB_Kt_le_one`, `HypB_Lproc_grid`, `HypB_Dproc_grid`,
  `HypB_sqrt_cont`: the fixed-point argument and the grid facts.

The other helpers (`HypB_sum_reflect`, `HypB_bil`, `HypB_le_Dmax`, `HypB_scale_pos`, `HypB_path`)
are `private`.

## Conventions (`d = 2`)

Loops are on `blockMat` with labels in `Z2 (d.L n)` (pairs `(Fin m → Bool) × (Fin m → Z2 (d.L n))`
with `loopOf`) and `RBM.Ind.loopMax`; `egtNGUE` and `genMatGUE` are the drift terms; the entry
good event is `RBM.Green.entryDom_goodEvent_of_llErr`; thresholds and failure rates are on
`d.size n` (`HighProbAt … d.size`); counts are `N = (W L)² = d.size n`, with `W⁻²` where rows or
blocks are counted.  The hypothesis `hD4` of `HypB_entry_le` has the constant `3 = 1 + 2`, because
the d = 2 entry bound has `1 · L₂` and the A3 factor is `W⁻² ≤ 2 L₂`.  `HypB_ev_grid`,
`HypB_ev_delta`, `HypB_highProb_range` assume `hsz : Tendsto d.size atTop atTop`.  Since
`1 ≤ d.size n` is proved, no hypotheses `1 ≤ N` or `W L ≤ N` are needed.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### Small helpers -/

section HypBHelpers

private theorem HypB_size_pos (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.size n := by
    unfold Sizes.size
    have hW := d.W_pos n
    have hL := d.three_le_L n
    positivity
  exact_mod_cast h1

private theorem HypB_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.size n := by
    unfold Sizes.size
    have hW := d.W_pos n
    have hL := d.three_le_L n
    positivity
  exact_mod_cast h1

/-- `d.size n = (W L)²` as a cast. -/
private theorem HypB_size_cast (n : ℕ) :
    (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = ((d.size n : ℕ) : ℝ) := rfl

private theorem HypB_loopOf_wf {L k : ℕ} [NeZero L] (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).WF := by
  change (List.ofFn σ).length = (List.ofFn a).length
  simp

private theorem HypB_loopOf_length {L k : ℕ} [NeZero L] (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- `‖(G − m)_{ij}‖` is the `llErrMat` of the (4.9) bridge. -/
private theorem HypB_llErr_eq {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    llErrMat L W E u M i j =
      ‖(green M (spectralZ E u) - spectralM E • (1 : Matrix (Idx L W) (Idx L W) ℂ)) i j‖ := by
  unfold llErrMat green
  by_cases h : i = j
  · subst h; simp [Matrix.sub_apply, Matrix.smul_apply]
  · simp [h, Matrix.sub_apply, Matrix.smul_apply]

end HypBHelpers

/-! ### The entry bound at the stopped grid times (D4a with A3) -/

section HypBEntry

/-- **D4a at the stopped grid times, with A3**: on the D4a event (at level `c`, the hypothesis
`hD4`), for `j < σ*` every diagonal entry of `G_j - m` is at most `√(3 c L₂)`. -/
theorem HypB_entry_le {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} {τU : ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (n : ℕ)
    (hellN : (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1) (hδN : gueDelta d τU n ≤ (spectralM (E n)).im / 2)
    (ω : PathΩ d) {c : ℝ} (hc : 0 ≤ c)
    (hD4 : ∀ (k : Fin (gueGridK d n0 n + 1)) (i j : Idx (d.L n) (d.W n)),
      {ω' : PathΩ d | ∀ a b : Idx (d.L n) (d.W n),
          ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω')
              (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
            spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
          gueDelta d τU n}.indicator
        (fun ω' => ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω')
              (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
            spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ^ 2) ω ≤
        c * (gueLmax d E t1 t0 (gueGridK d n0) n 2 k ω + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹))
    {j : ℕ} (hj : j < gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω)
    (q : Idx (d.L n) (d.W n)) :
    ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω)
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) q q‖ ≤
      Real.sqrt (3 * c * RBM.Ind.loopMax (d.L n) (d.W n)
        (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2) := by
  have hσK : gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω ≤ gueGridK d n0 n :=
    firstHit_le _ _ _ ω
  have hjK : j < gueGridK d n0 n + 1 := by omega
  have hj' : j < firstHit (fun k ω' => gueDev d E t1 t0 (gueGridK d n0) n k ω')
      (gueDelta d τU n) (gueGridK d n0 n) ω := hj
  have hdev : gueDev d E t1 t0 (gueGridK d n0) n j ω < gueDelta d τU n :=
    lt_firstHit_imp (fun k ω' => gueDev d E t1 t0 (gueGridK d n0) n k ω') (gueDelta d τU n)
      (gueGridK d n0 n) hj'
  have hentry : ∀ i i' : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω)
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i i'‖ ≤
        gueDelta d τU n := by
    intro i i'
    refine le_trans ?_ hdev.le
    unfold gueDev
    exact le_ciSup (f := fun ij : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) =>
      ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω)
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) ij.1 ij.2‖)
      (Set.finite_range _).bddAbove (i, i')
  have h4 : ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω)
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) q q‖ ^ 2 ≤
      c * (RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2 +
        (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h := hD4 ⟨j, hjK⟩ q q
    rw [Set.indicator_of_mem (show ω ∈ {ω' : PathΩ d | ∀ a b : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω')
        (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
        gueDelta d τU n} from hentry)] at h
    exact h
  -- A3: `W⁻² ≤ 2 L₂` on the a-priori event
  have hEN : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  have hu1 : gridTime t1 t0 (gueGridK d n0) n j < 1 :=
    lt_of_le_of_lt (Hyp_time_le (ht10 n) (gueGridK_ne_zero d n0 n) (by omega)) (ht0 n)
  have hellj : (d.L n : ℝ) ^ 2 * (1 - gridTime t1 t0 (gueGridK d n0) n j) ≤ 1 := by
    have h1 := Hyp_time_ge (K := gueGridK d n0) (ht10 n) j
    have hL : (0 : ℝ) ≤ (d.L n : ℝ) ^ 2 := sq_nonneg _
    have h2 : 1 - gridTime t1 t0 (gueGridK d n0) n j ≤ 1 - t1 n := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hL) hellN
  have hW := gue_inv_W_le_loopMax (L := d.L n) (W := d.W n)
    (gueH_isHermitian d t1 t0 (gueGridK d n0) n j ω) hEN hu1 hellj
    (RBM.Green.entryDom_goodEvent_of_llErr _ _ _ _ _ _ fun i i' => by
      rw [HypB_llErr_eq]; exact hentry i i') hδN
  have hL0 := RBM.Ind.loopMax_nonneg (L := d.L n) (W := d.W n)
    (H := blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
    (z := spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2
  have hWinv : (((d.W n : ℕ) : ℝ) ^ 2)⁻¹ = (((d.W n : ℕ) : ℝ)⁻¹) ^ 2 := by rw [inv_pow]
  apply Real.le_sqrt_of_sq_le
  calc _ ≤ c * (RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2 +
          (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) := h4
    _ ≤ c * (RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2 +
          2 * RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2) := by
        rw [hWinv]; gcongr
    _ = 3 * c * RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) 2 := by ring

end HypBEntry

/-! ### The `E^{(G)}` and martingale lines of (7.45)G and (7.46)G -/

section HypBLines

/-- `|L_k(J) - K̃_{u_k}(J)| ≤ D^{(|J|)}_k` for every well-formed `J`. -/
private theorem HypB_le_Dmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n k : ℕ) (ω : PathΩ d)
    (J : LoopIdx (Z2 (d.L n))) (hJ : J.WF) :
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
        (spectralZ (E n) (gridTime t1 t0 K n k)) J -
      Kt n (gridTime t1 t0 K n k) J‖ ≤ gueDmax d E t1 t0 K Kt n J.length k ω := by
  obtain ⟨x, hx⟩ := Hyp_exists_loopOf J hJ
  unfold gueDmax
  have h := le_ciSup (f := fun x' : (Fin J.length → Bool) × (Fin J.length → Z2 (d.L n)) =>
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
        (spectralZ (E n) (gridTime t1 t0 K n k)) (loopOf x'.1 x'.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x'.1 x'.2)‖) (Set.finite_range _).bddAbove x
  simp only [hx] at h
  exact h

/-- **The drift line for (7.45)G** (even `m = 2l`): `|𝓔̃| ≤ 4 m c N L₂ L_m` from `ε ≤ √(3 c L₂)`
(D4a + A3, the
conclusion of `HypB_entry_le`) and R6a `L_{2l+1} ≤ √L₂ L_{2l}`. -/
theorem HypB_eG_745 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ d)
    {c : ℝ} (hc : 1 ≤ c) {l : ℕ} (hl : 1 ≤ l)
    (hdiag : ∀ q : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 K n j ω) (spectralZ (E n) (gridTime t1 t0 K n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) q q‖ ≤
      Real.sqrt (3 * c * RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
        (spectralZ (E n) (gridTime t1 t0 K n j)) 2))
    (x : (Fin (2 * l) → Bool) × (Fin (2 * l) → Z2 (d.L n))) :
    ‖egtNGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      (4 * ((2 * l : ℕ) : ℝ) * c * ((d.size n : ℕ) : ℝ)) *
        (RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
            (spectralZ (E n) (gridTime t1 t0 K n j)) 2 *
          RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
            (spectralZ (E n) (gridTime t1 t0 K n j)) (2 * l)) := by
  set M := gueH d t1 t0 K n j ω with hMdef
  set u := gridTime t1 t0 K n j with hudef
  have hH : M.IsHermitian := gueH_isHermitian d t1 t0 K n j ω
  have hHb : (blockMat M).IsHermitian := hH.submatrix _
  set L2 := RBM.Ind.loopMax (d.L n) (d.W n) (blockMat M) (spectralZ (E n) u) 2 with hL2
  set Ln := RBM.Ind.loopMax (d.L n) (d.W n) (blockMat M) (spectralZ (E n) u) (2 * l) with hLn
  have hL20 : 0 ≤ L2 := RBM.Ind.loopMax_nonneg _
  have hLn0 : 0 ≤ Ln := RBM.Ind.loopMax_nonneg _
  have hlen : (loopOf x.1 x.2).length = 2 * l := HypB_loopOf_length _ _
  have hb := norm_egtNGUE_le (d.L n) (d.W n) (E n) u M (loopOf x.1 x.2)
    (ε := Real.sqrt (3 * c * L2)) (B := Real.sqrt L2 * Ln)
    (fun σ a => Hyp_eps_le_dev hH (E n) u hdiag σ a)
    (fun k hk b => (Hyp_cutGlue_le (HypB_loopOf_wf _ _) hk b).trans (by
      rw [hlen]; exact gueLoopMax_odd_succ_le hHb (spectralZ (E n) u) hl))
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans ?_
  have hc0 : 0 ≤ c := by linarith
  have hs : Real.sqrt (3 * c * L2) * (Real.sqrt L2 * Ln) = Real.sqrt (3 * c) * (L2 * Ln) := by
    rw [Real.sqrt_mul (by positivity) L2]
    have := Real.mul_self_sqrt hL20
    calc Real.sqrt (3 * c) * Real.sqrt L2 * (Real.sqrt L2 * Ln)
        = Real.sqrt (3 * c) * (Real.sqrt L2 * Real.sqrt L2) * Ln := by ring
      _ = Real.sqrt (3 * c) * (L2 * Ln) := by rw [this]; ring
  have h3 : Real.sqrt (3 * c) ≤ 4 * c := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hS : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((2 * l : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) * Real.sqrt (3 * c * L2) *
        (Real.sqrt L2 * Ln)
      = ((2 * l : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) * (Real.sqrt (3 * c) * (L2 * Ln)) := by
        rw [mul_assoc _ (Real.sqrt (3 * c * L2)), hs]
    _ ≤ ((2 * l : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) * (4 * c * (L2 * Ln)) := by
        gcongr
    _ = _ := by ring

/-- **The drift line for (7.46)G**: `|𝓔̃| ≤ m N D₁ L_{m+1}`, from `ε ≤ D^{(1)}` (`K̃ = m_σ` at
length `1`,
`Hyp_Kt_one`). -/
theorem HypB_eG_746 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (n j m : ℕ) (hu : gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n)) (ω : PathΩ d)
    (x : (Fin m → Bool) × (Fin m → Z2 (d.L n))) :
    ‖egtNGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      ((m : ℝ) * ((d.size n : ℕ) : ℝ)) *
        (gueDmax d E t1 t0 K Kt n 1 j ω *
          RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
            (spectralZ (E n) (gridTime t1 t0 K n j)) (m + 1)) := by
  have hlen : (loopOf x.1 x.2).length = m := HypB_loopOf_length _ _
  have hε : ∀ (σ : Bool) (a : Z2 (d.L n)),
      ‖avgErr (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω) σ a‖ ≤
        gueDmax d E t1 t0 K Kt n 1 j ω := by
    intro σ a
    have h1 : avgErr (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω) σ a =
        gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
          (spectralZ (E n) (gridTime t1 t0 K n j)) ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ :=
      Hyp_trace_eq_gloop_one (blockMat (gueH d t1 t0 K n j ω)) (spectralZ (E n) (gridTime t1 t0 K n j))
        (KLoop.mSig (E n)) σ a
    rw [h1, ← Hyp_Kt_one d n0 hn0 Kt hKinit hK n hu σ a]
    exact HypB_le_Dmax d E t1 t0 K Kt n j ω ⟨[σ], [a]⟩ rfl
  have hb := norm_egtNGUE_le (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω)
    (loopOf x.1 x.2) hε
    (fun k hk b => by
      have := Hyp_cutGlue_le (L := d.L n) (W := d.W n)
        (H := blockMat (gueH d t1 t0 K n j ω)) (z := spectralZ (E n) (gridTime t1 t0 K n j))
        (HypB_loopOf_wf x.1 x.2) hk b
      rwa [hlen] at this)
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- The martingale line of h745E: `√(a L_{4l}) ≤ √a L_{2l}`, `a = N⁻¹η⁻²` (R6b). -/
theorem HypB_q_745 {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {a : ℝ}
    (ha : 0 ≤ a) {l : ℕ} (hl : 1 ≤ l) :
    Real.sqrt (a * RBM.Ind.loopMax L W H z (2 * (2 * l))) ≤
      Real.sqrt a * RBM.Ind.loopMax L W H z (2 * l) := by
  have h := gueLoopMax_four_mul_le hH z hl
  rw [show 2 * (2 * l) = 4 * l by ring]
  calc Real.sqrt (a * RBM.Ind.loopMax L W H z (4 * l))
      ≤ Real.sqrt (a * RBM.Ind.loopMax L W H z (2 * l) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h ha)
    _ = Real.sqrt a * RBM.Ind.loopMax L W H z (2 * l) := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq (RBM.Ind.loopMax_nonneg _)]

end HypBLines

/-! ### Eventual deterministic facts on the size scale -/

section HypBEventually

/-- The grid is fine enough for the discretization error (`M³ N Δ ≤ 1`) and for the absorption of
the discretization error into `N^{-2n₀}` (`N = d.size n`, `K = (N + 1)^{32 n₀ + 64}`). -/
private theorem HypB_grid_of_size (n0 N : ℕ) (hN : 3 * (2 * n0) ^ 6 + (2 * n0) ^ 3 + 1 ≤ N) :
    ((2 * n0 : ℕ) : ℝ) ^ 3 * (N : ℝ) * ((((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ))⁻¹ ≤ 1 ∧
      3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ))⁻¹ ≤
        ((N : ℝ)⁻¹) ^ (2 * n0) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ) := by positivity
  have hKge : (N : ℝ) ^ (2 * n0 + 3) ≤ (((N + 1) ^ (32 * n0 + 64) : ℕ) : ℝ) := by
    push_cast
    calc (N : ℝ) ^ (2 * n0 + 3) ≤ (N : ℝ) ^ (32 * n0 + 64) :=
          pow_le_pow_right₀ hNR (by omega)
      _ ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) := pow_le_pow_left₀ hN0.le (by linarith) _
  have hA : ((3 * (2 * n0) ^ 6 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  have hB : (((2 * n0) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  push_cast at hA hB
  push_cast at hKpos hKge ⊢
  constructor
  · rw [← div_eq_mul_inv, div_le_one hKpos]
    calc ((2 * (n0 : ℝ))) ^ 3 * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hB hN0.le
      _ = (N : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) ^ (2 * n0 + 3) := pow_le_pow_right₀ hNR (by omega)
      _ ≤ _ := hKge
  · rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hKpos]
    have hpow : (0 : ℝ) < (N : ℝ) ^ (2 * n0) := pow_pos hN0 _
    rw [← div_eq_inv_mul, le_div_iff₀ hpow]
    calc 3 * (2 * (n0 : ℝ)) ^ 6 * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0)
        ≤ (N : ℝ) * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0) := by gcongr
      _ = (N : ℝ) ^ (2 * n0 + 3) := by ring
      _ ≤ _ := hKge

/-- The grid is fine enough for the discretization error (`M³ N Δ ≤ 1`) and for the absorption of
the discretization error into `N^{-2n₀}`, eventually in the size index (`N = d.size n`, under
`hsz : Tendsto d.size atTop atTop`). -/
theorem HypB_ev_grid (hsz : Tendsto d.size atTop atTop) (n0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((2 * n0 : ℕ) : ℝ) ^ 3 * ((d.size n : ℕ) : ℝ) * ((gueGridK d n0 n : ℝ))⁻¹ ≤ 1 ∧
      3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((d.size n : ℕ) : ℝ) ^ 2 * ((gueGridK d n0 n : ℝ))⁻¹ ≤
        (((d.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0) := by
  filter_upwards [hsz.eventually
    (eventually_ge_atTop (3 * (2 * n0) ^ 6 + (2 * n0) ^ 3 + 1))] with n hN
  exact HypB_grid_of_size n0 (d.size n) hN

/-- `Im m ≥ √(2κ)/2` for `|E| ≤ 2 - κ`, hence `δ_n = N^{-τU/4} ≤ Im m / 2` eventually in the size
index. -/
theorem HypB_ev_delta {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hsz : Tendsto d.size atTop atTop) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) :
    ∀ᶠ n : ℕ in atTop, gueDelta d τU n ≤ (spectralM (E n)).im / 2 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  have hlow : ∀ n, Real.sqrt (2 * κ) / 2 ≤ (spectralM (E n)).im := by
    intro n
    rw [spectralM_im]
    have hsq : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have h := hE n
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have : 2 * κ ≤ 4 - E n ^ 2 := by nlinarith
    gcongr
  have hc : 0 < Real.sqrt (2 * κ) / 4 := by positivity
  filter_upwards [hsz.eventually
    (eventually_le_rpow (Real.sqrt (2 * κ) / 4)⁻¹ (by positivity : 0 < τU / 4)),
    hsz.eventually (eventually_ge_atTop 1)] with n hN hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  unfold gueDelta
  rw [Real.rpow_neg hN0.le]
  have hpos : 0 < ((d.size n : ℕ) : ℝ) ^ (τU / 4) := Real.rpow_pos_of_pos hN0 _
  calc (((d.size n : ℕ) : ℝ) ^ (τU / 4))⁻¹ ≤ Real.sqrt (2 * κ) / 4 := by
        rw [inv_le_comm₀ hpos hc]; exact hN
    _ ≤ (spectralM (E n)).im / 2 := by linarith [hlow n]

end HypBEventually

/-! ### Finitely many high-probability events -/

/-- Finitely many `HighProbAt` events hold simultaneously with high probability. -/
theorem HypB_highProb_range {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hsz : Tendsto d.size atTop atTop) (M : ℕ) (Ξ : ℕ → ℕ → Set Ω)
    (h : ∀ m, 1 ≤ m → m ≤ M → HighProbAt P d.size (Ξ m)) :
    HighProbAt P d.size (fun n => {ω | ∀ m, 1 ≤ m → m ≤ M → ω ∈ Ξ m n}) := by
  induction M with
  | zero =>
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ P d.size)
      (Eventually.of_forall fun n ω _ m h1 h2 => by omega)
  | succ M ih =>
    have h1 := ih fun m hm1 hm2 => h m hm1 (by omega)
    have h2 := h (M + 1) (by omega) le_rfl
    refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz h1 h2)
      (Eventually.of_forall fun n ω hω m hm1 hm2 => ?_)
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · exact hω.1 m hm1 (by omega)
    · obtain rfl : m = M + 1 := by omega
      exact hω.2


/-! ### Drift bounds and the pathwise assembly -/

section HypBPath

/-- `∑_{j=2}^m h(m-j+2) = ∑_{j=2}^m h(j)`. -/
private theorem HypB_sum_reflect (n : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 2 n, h (n - j + 2) = ∑ j ∈ Finset.Icc 2 n, h j := by
  refine Finset.sum_nbij' (fun j => n - j + 2) (fun j => n - j + 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a _; rfl

/-- **The bilinear drift** ((7.39), (7.40), `d = 2`): with `|K̃(J)| ≤ c λ^{|J|-1}` and
`|L(J) - K̃(J)| ≤ D_{|J|}`, `|F(L) - F(K̃)| ≤ 3 m² c N ∑_{i=2}^m (λ^{i-1} + D_i) D_{m-i+2}`,
`N = (W L)²`. -/
private theorem HypB_bil {L W : ℕ} [NeZero L] (Lf K : LoopIdx (Z2 L) → ℂ)
    (I : LoopIdx (Z2 L)) (hI : I.WF) (Dv : ℕ → ℝ) {lam c : ℝ} (hc : 1 ≤ c) (hlam : 0 ≤ lam)
    (hDv0 : ∀ i, 0 ≤ Dv i)
    (hD : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖Lf J - K J‖ ≤ Dv J.length)
    (hK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ c * lam ^ (J.length - 1)) :
    ‖primRhsGUE L W Lf I - primRhsGUE L W K I‖ ≤
      3 * (I.length : ℝ) ^ 2 * c * (((W * L) ^ 2 : ℕ) : ℝ) *
        ∑ i ∈ Finset.Icc 2 I.length, (lam ^ (i - 1) + Dv i) * Dv (I.length - i + 2) := by
  set n := I.length with hn
  set T := ∑ i ∈ Finset.Icc 2 n, (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) with hT
  set S : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by linarith
  have hBk0 : ∀ i, 0 ≤ c * lam ^ (i - 1) := fun i => mul_nonneg hc0 (pow_nonneg hlam _)
  have hD' : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(Lf - K) J‖ ≤ Dv J.length := fun J h1 h2 h3 => by rw [Pi.sub_apply]; exact hD J h1 h2 h3
  rw [primRhsGUE_sub]
  have b1 := norm_primBilGUE_le L W K (Lf - K) (fun i => c * lam ^ (i - 1)) Dv I hI
    hK hD' hBk0 hDv0
  have b2 := norm_primBilGUE_le L W (Lf - K) K Dv (fun i => c * lam ^ (i - 1)) I hI
    hD' hK hDv0 hBk0
  have b3 := norm_primBilGUE_le L W (Lf - K) (Lf - K) Dv Dv I hI hD' hD' hDv0 hDv0
  have hterm : ∀ i ∈ Finset.Icc 2 n, 0 ≤ (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) :=
    fun i _ => mul_nonneg (add_nonneg (pow_nonneg hlam _) (hDv0 i)) (hDv0 _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg hterm
  -- the three sums against `c T`
  have s2 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * (c * lam ^ (j - 1)) ≤ c * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_nonneg (mul_nonneg hc0 (hDv0 i)) (hDv0 (n - i + 2))
    nlinarith
  have s1 : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j ≤ c * T := by
    have hre := HypB_sum_reflect n (fun j => c * lam ^ (j - 1) * Dv (n - j + 2))
    have hre' : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j =
        ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv (n - (n - j + 2) + 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      rw [show n - (n - j + 2) + 2 = j by omega]
    rw [hre', hre]
    refine le_trans (le_of_eq ?_) s2
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have s3 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * Dv j ≤ c * T := by
    refine le_trans ?_ (le_mul_of_one_le_left hT0 hc)
    rw [hT]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hDv0 (n - i + 2)
    have := pow_nonneg hlam (i - 1)
    nlinarith [hDv0 i]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * S := by positivity
  calc ‖primBilGUE L W K (Lf - K) I + primBilGUE L W (Lf - K) K I +
          primBilGUE L W (Lf - K) (Lf - K) I‖
      ≤ ‖primBilGUE L W K (Lf - K) I‖ + ‖primBilGUE L W (Lf - K) K I‖ +
          ‖primBilGUE L W (Lf - K) (Lf - K) I‖ := norm_add₃_le
    _ ≤ (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) := by
        gcongr
        · exact b1.trans (mul_le_mul_of_nonneg_left s1 hn2)
        · exact b2.trans (mul_le_mul_of_nonneg_left s2 hn2)
        · exact b3.trans (mul_le_mul_of_nonneg_left s3 hn2)
    _ = 3 * (n : ℝ) ^ 2 * c * S * T := by ring

/-- `N η_u > 0` on `[t₁, t₀]`. -/
private theorem HypB_scale_pos {E t0 : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2)
    (ht0 : t0 n < 1) {u : ℝ} (hu : u ≤ t0 n) : 0 < gueScale d E n u := by
  unfold gueScale
  exact mul_pos (HypB_size_pos d n) (etaT_pos hE (by linarith))

/-- **The pathwise bound at one length `m`**: on the good event, the
stopped interpolated `D_m(t)` is bounded by a constant times the right side
`N(t-t₁) sup g₁ + (Nη_t)^{-m} + N(t-t₁) sup g₃ + √(t-t₁) sup g₄`, for all `t ∈ [t₁, t₀]`. -/
private theorem HypB_path (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (ω : PathΩ d)
    (g3 g4 : ℝ → ℝ) {c Ce err : ℝ}
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK0 : K n ≠ 0)
    (hm : 1 ≤ m) (hc : 1 ≤ c) (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * (m : ℝ) ^ 2 * c * ((d.size n : ℕ) : ℝ))
    (hΔ : gridStep t1 t0 K n ≤ 1 - t0 n)
    (herr : ∀ t ∈ Set.Icc (t1 n) (t0 n), err ≤ (gueScale d E n t)⁻¹ ^ m)
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω))
          (spectralZ (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * (gueScale d E n (t1 n))⁻¹ ^ m)
    (hM : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
          (spectralZ (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2)
          - gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω))
            (spectralZ (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j)
                (gueH d t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤
        c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((d.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
              (spectralZ (E n) (gridTime t1 t0 K n j)) (2 * m)))
          + (gueScale d E n (gridTime t1 t0 K n k))⁻¹ ^ m))
    (hq : ∀ j < gueStop d E t1 t0 K δ n ω,
      Real.sqrt ((((d.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
          (spectralZ (E n) (gridTime t1 t0 K n j)) (2 * m)) ≤ g4 (gridTime t1 t0 K n j))
    (hKt : ∀ j ≤ K n, ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length → J.length ≤ m →
      ‖Kt n (gridTime t1 t0 K n j) J‖ ≤ c * (gueScale d E n (gridTime t1 t0 K n j))⁻¹ ^
        (J.length - 1))
    (heG : ∀ j < gueStop d E t1 t0 K δ n ω, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖egtNGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j))
    (hdisc : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE (d.L n) (d.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDproc d E t1 t0 K δ Kt n m t ω ≤ c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) *
      (((d.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((((d.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 K δ Kt n k u ω) * gueDproc d E t1 t0 K δ Kt n (m - k + 2) u ω)
          (t1 n) t
        + (((d.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ^ m
        + ((d.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  set S : ℝ := ((d.size n : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := HypB_size_pos d n
  set σ := gueStop d E t1 t0 K δ n ω with hσdef
  have hσK : σ ≤ K n := firstHit_le _ _ _ ω
  have hc0 : 0 ≤ c := by linarith
  have hscale_eq : ∀ u, gueScale d E n u = S * etaT (E n) u := fun u => rfl
  have hηpos : ∀ u, u ≤ t0 n → 0 < etaT (E n) u := fun u hu => etaT_pos hE (by linarith)
  set g1 : ℝ → ℝ := fun u => ∑ k ∈ Finset.Icc 2 m,
    ((S * etaT (E n) u)⁻¹ ^ (k - 1) + gueDproc d E t1 t0 K δ Kt n k u ω) *
      gueDproc d E t1 t0 K δ Kt n (m - k + 2) u ω with hg1def
  have hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u := by
    intro u hu
    refine Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (pow_nonneg (inv_nonneg.2
      (mul_nonneg hS0.le (hηpos u hu.2).le)) _) (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _))
      (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
  have hηc : Continuous fun u => etaT (E n) u := by unfold etaT; fun_prop
  have hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n)) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.mul (ContinuousOn.add ?_ (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _))
      (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _)
    refine ContinuousOn.pow (ContinuousOn.inv₀ (continuous_const.mul hηc).continuousOn
      fun u hu => (mul_pos hS0 (hηpos u hu.2)).ne') _
  -- the bilinear drift, `Cf = 3 m² c S`
  have hF : ∀ j < σ, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖primRhsGUE (d.L n) (d.W n) (RBM.Ind.LLf (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j)
          (gueH d t1 t0 K n j ω)) (loopOf x.1 x.2) -
        primRhsGUE (d.L n) (d.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤
        (3 * (m : ℝ) ^ 2 * c * S) * g1 (gridTime t1 t0 K n j) := by
    intro j hj x
    have hjK : j ≤ K n := (le_of_lt hj).trans hσK
    have hmin : min j σ = j := min_eq_left hj.le
    have hDp : ∀ i, gueDproc d E t1 t0 K δ Kt n i (gridTime t1 t0 K n j) ω =
        gueDmax d E t1 t0 K Kt n i j ω := by
      intro i; rw [gueDproc_time d E t1 t0 K δ Kt n i j ht10 hjK ω, ← hσdef, hmin]
    have hlen : (loopOf x.1 x.2).length = m := HypB_loopOf_length _ _
    have hb := HypB_bil (W := d.W n)
      (RBM.Ind.LLf (d.L n) (d.W n) (E n) (gridTime t1 t0 K n j) (gueH d t1 t0 K n j ω))
      (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2) (HypB_loopOf_wf _ _)
      (fun i => gueDproc d E t1 t0 K δ Kt n i (gridTime t1 t0 K n j) ω)
      (lam := (S * etaT (E n) (gridTime t1 t0 K n j))⁻¹) hc
      (inv_nonneg.2 (mul_nonneg hS0.le (hηpos _ (Hyp_time_le ht10 hK0 hjK)).le))
      (fun i => gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (fun J hJ _ _ => by rw [hDp]; exact HypB_le_Dmax d E t1 t0 K Kt n j ω J hJ)
      (fun J hJ h2 hJn => by rw [hlen] at hJn; exact hKt j hjK J hJ h2 hJn)
    rw [hlen, HypB_size_cast] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hg1def]
  have hCf0 : 0 ≤ 3 * (m : ℝ) ^ 2 * c * S := by positivity
  set Λ0 := (gueScale d E n (t1 n))⁻¹ ^ m with hΛ0def
  set S1 := supOn g1 (t1 n) t with hS1def
  set S3 := supOn g3 (t1 n) t with hS3def
  set S4 := supOn g4 (t1 n) t with hS4def
  have hS1n : 0 ≤ S1 := supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS4n : 0 ≤ S4 := supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hlam : ∀ k ≤ K n, gridTime t1 t0 K n k ≤ t + gridStep t1 t0 K n →
      (fun u => (gueScale d E n u)⁻¹ ^ m) (gridTime t1 t0 K n k) ≤
        2 ^ m * (fun u => (gueScale d E n u)⁻¹ ^ m) t := by
    intro k hk hkt
    simp only
    have hmem := Hyp_time_mem (K := K) ht10 hK0 hk
    have him := spectralM_im_pos hE
    have hηk : etaT (E n) t ≤ 2 * etaT (E n) (gridTime t1 t0 K n k) := by
      unfold etaT
      have h1 : (gridTime t1 t0 K n k - t) * (spectralM (E n)).im ≤
          gridStep t1 t0 K n * (spectralM (E n)).im :=
        mul_le_mul_of_nonneg_right (by linarith) him.le
      have h2 : gridStep t1 t0 K n * (spectralM (E n)).im ≤ (1 - t0 n) * (spectralM (E n)).im :=
        mul_le_mul_of_nonneg_right hΔ him.le
      have h3 : (1 - t0 n) * (spectralM (E n)).im ≤
          (1 - gridTime t1 t0 K n k) * (spectralM (E n)).im :=
        mul_le_mul_of_nonneg_right (by linarith [hmem.2]) him.le
      nlinarith
    have hpk := HypB_scale_pos d (E := E) hE ht0 hmem.2
    have hpt := HypB_scale_pos d (E := E) hE ht0 ht.2
    have hinv : (gueScale d E n (gridTime t1 t0 K n k))⁻¹ ≤ 2 * (gueScale d E n t)⁻¹ := by
      rw [show (2 : ℝ) * (gueScale d E n t)⁻¹ = 2 / gueScale d E n t by ring, inv_eq_one_div,
        div_le_div_iff₀ hpk hpt]
      rw [hscale_eq, hscale_eq]
      nlinarith
    calc (gueScale d E n (gridTime t1 t0 K n k))⁻¹ ^ m ≤ (2 * (gueScale d E n t)⁻¹) ^ m :=
          pow_le_pow_left₀ (inv_nonneg.2 hpk.le) hinv m
      _ = 2 ^ m * (gueScale d E n t)⁻¹ ^ m := by rw [mul_pow]
  have hint := Hyp_interp_bound (f := fun k => gueDmax d E t1 t0 K Kt n m k ω) hσK hK0 ht10
    ht (fun u => (gueScale d E n u)⁻¹ ^ m) (P := c * Λ0 + err) (Q := c)
    (A := 3 * (m : ℝ) ^ 2 * c * S * S1 + Ce * S3) (B := c * S4) (C := 2 ^ m) hc0
    (by positivity) (by positivity) hlam
    (fun k hk hkt => Hyp_grid d E t1 t0 K δ Kt n m ω g1 g3 g4 ht10 hE ht1 ht0 hm hc0 hCf0 hCe0
      hg1 hg3 hg4 hg1c hg3c hg4c h0 hM hq hF heG hdisc ht hk hkt)
  have hLHS : gueDproc d E t1 t0 K δ Kt n m t ω =
      gueInterp t1 t0 K n (fun k => gueDmax d E t1 t0 K Kt n m (min k σ) ω) t := rfl
  rw [hLHS]
  refine hint.trans ?_
  set X2 := (gueScale d E n t)⁻¹ ^ m with hX2def
  have hX2eq : (S * etaT (E n) t)⁻¹ ^ m = X2 := rfl
  rw [hX2eq]
  have hpt := HypB_scale_pos d (E := E) hE ht0 ht.2
  have hX2n : 0 ≤ X2 := pow_nonneg (inv_nonneg.2 hpt.le) _
  have hΛ0le : Λ0 ≤ X2 := by
    have hp1 := HypB_scale_pos d (E := E) hE ht0 ht10
    have hle : gueScale d E n t ≤ gueScale d E n (t1 n) := by
      rw [hscale_eq, hscale_eq]
      refine mul_le_mul_of_nonneg_left ?_ hS0.le
      unfold etaT
      have := spectralM_im_pos hE
      nlinarith [ht.1]
    exact pow_le_pow_left₀ (inv_nonneg.2 hp1.le) (inv_anti₀ hpt hle) m
  have herr' := herr t ht
  have htt : 0 ≤ t - t1 n := by linarith [ht.1]
  have hsq : 0 ≤ Real.sqrt (t - t1 n) := Real.sqrt_nonneg _
  have hn2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hX1 : 0 ≤ S * (t - t1 n) * S1 := by positivity
  have hX3 : 0 ≤ S * (t - t1 n) * S3 := by positivity
  have hX4 : 0 ≤ Real.sqrt (t - t1 n) * S4 := by positivity
  have e1 : c * Λ0 + err + c * (2 ^ m * X2) ≤ c * (2 + 2 ^ m) * X2 := by
    have := mul_le_mul_of_nonneg_left hΛ0le hc0
    have : err ≤ c * X2 := herr'.trans (le_mul_of_one_le_left hX2n hc)
    nlinarith
  have e2 : (3 * (m : ℝ) ^ 2 * c * S * S1 + Ce * S3) * (t - t1 n) ≤
      c * (7 * (m : ℝ) ^ 2) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) := by
    have hCe' : Ce * S3 * (t - t1 n) ≤ 4 * (m : ℝ) ^ 2 * c * S * S3 * (t - t1 n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe hS3n) htt
    have ha : 0 ≤ c * (m : ℝ) ^ 2 * (S * (t - t1 n) * S1) := by positivity
    have hb : 0 ≤ c * (m : ℝ) ^ 2 * (S * (t - t1 n) * S3) := by positivity
    nlinarith
  have e3 : c * S4 * Real.sqrt (t - t1 n) ≤
      c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by
    have hK1 : (1 : ℝ) ≤ 2 + 2 ^ m + 7 * (m : ℝ) ^ 2 := by linarith
    have hX : 0 ≤ c * (Real.sqrt (t - t1 n) * S4) := by positivity
    have h := mul_le_mul_of_nonneg_left hK1 hX
    calc c * S4 * Real.sqrt (t - t1 n) = c * (Real.sqrt (t - t1 n) * S4) * 1 := by ring
      _ ≤ c * (Real.sqrt (t - t1 n) * S4) * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) := h
      _ = c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by ring
  have hfin : c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) *
      (S * (t - t1 n) * S1 + X2 + S * (t - t1 n) * S3 + Real.sqrt (t - t1 n) * S4) =
      c * (2 + 2 ^ m) * X2 + c * (7 * (m : ℝ) ^ 2) *
        (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) +
      (c * (2 + 2 ^ m) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
        c * (7 * (m : ℝ) ^ 2) * X2) := by ring
  have hextra : 0 ≤ c * (2 + 2 ^ m) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * (7 * (m : ℝ) ^ 2) * X2 := by positivity
  rw [hfin]
  linarith

end HypBPath


/-! ### The pathwise bound at a fixed size index with the exponent bookkeeping -/

section HypBFixed

/-- **One length, one size index, one sample point**: the eventual deterministic facts and the
good event at level `N^{τ/2}` give `D_m(t) ≤ N^τ · rhs(t)` for every `t ∈ [t₁, t₀]` (the bounds on
`K̃` and on the discretization error, the step-size conditions and the final absorption).
`N = d.size n = (W L)²`; since `1 ≤ d.size n`, no hypotheses `1 ≤ N` or `W L ≤ N` are needed. -/
theorem HypB_fixed {τ : ℝ} (hτ : 0 < τ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (τU : ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (n m : ℕ) (ω : PathΩ d) (g3 g4 : ℝ → ℝ) {Ce : ℝ}
    (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (hm1 : 1 ≤ m) (hm : m ≤ 2 * n0)
    (hΔ : gridStep t1 t0 (gueGridK d n0) n ≤ 1 - t0 n)
    (hgrid1 : ((2 * n0 : ℕ) : ℝ) ^ 3 * ((d.size n : ℕ) : ℝ) * ((gueGridK d n0 n : ℝ))⁻¹ ≤ 1)
    (hgrid2 : 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((d.size n : ℕ) : ℝ) ^ 2 * ((gueGridK d n0 n : ℝ))⁻¹ ≤
      (((d.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0))
    (hbd : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1)
    (hKtc : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 →
      ‖Kt n t J‖ ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale d E n t)⁻¹ ^ (J.length - 1))
    (hbig : 2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2))
    (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * (m : ℝ) ^ 2 * ((d.size n : ℕ) : ℝ) ^ (τ / 2) * ((d.size n : ℕ) : ℝ))
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n 0 ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 (gueGridK d n0) n 0) (loopOf x.1 x.2)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale d E n (t1 n))⁻¹ ^ m)
    (hM : ∀ k ≤ gueGridK d n0 n, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n k ω))
            (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) (loopOf x.1 x.2)
          - gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n 0 ω))
            (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 (gueGridK d n0) n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 (gueGridK d n0) n j)
                (gueH d t1 t0 (gueGridK d n0) n j ω) (loopOf x.1 x.2)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (τ / 2) * (Real.sqrt (gridTime t1 t0 (gueGridK d n0) n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((d.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
              (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) (2 * m)))
          + (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m))
    (hq : ∀ j < gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω,
      Real.sqrt ((((d.size n : ℕ) : ℝ))⁻¹ *
        (etaT (E n) (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n j ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) (2 * m)) ≤
        g4 (gridTime t1 t0 (gueGridK d n0) n j))
    (heG : ∀ j < gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω,
      ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖egtNGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 (gueGridK d n0) n j)
          (gueH d t1 t0 (gueGridK d n0) n j ω) (loopOf x.1 x.2)‖ ≤
        Ce * g3 (gridTime t1 t0 (gueGridK d n0) n j))
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω ≤
      ((d.size n : ℕ) : ℝ) ^ τ *
      (((d.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((((d.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n k u ω) *
            gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n (m - k + 2) u ω)
          (t1 n) t
        + (((d.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ^ m
        + ((d.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  have hNR : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := HypB_one_le_size d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set c := N ^ (τ / 2) with hcdef
  have hc : 1 ≤ c := Real.one_le_rpow hNR (by positivity)
  have hK0 : gueGridK d n0 n ≠ 0 := gueGridK_ne_zero d n0 n
  have hKR : (1 : ℝ) ≤ (gueGridK d n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hK0
  set Δ := gridStep t1 t0 (gueGridK d n0) n with hΔdef
  have hΔ0 : 0 ≤ Δ := Hyp_step_nonneg ht10
  have hΔK : Δ ≤ ((gueGridK d n0 n : ℝ))⁻¹ := by
    rw [hΔdef]; unfold gridStep
    rw [div_eq_mul_inv]
    have : t0 n - t1 n ≤ 1 := by linarith
    have hKi : 0 ≤ ((gueGridK d n0 n : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    have h0 : 0 ≤ t0 n - t1 n := by linarith
    calc (t0 n - t1 n) * ((gueGridK d n0 n : ℝ))⁻¹ ≤ 1 * ((gueGridK d n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right this hKi
      _ = ((gueGridK d n0 n : ℝ))⁻¹ := one_mul _
  -- the discretization condition `M³ N Δ ≤ 1`
  have hsmall : ((2 * n0 : ℕ) : ℝ) ^ 3 * (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) * Δ ≤ 1 := by
    rw [HypB_size_cast]
    calc ((2 * n0 : ℕ) : ℝ) ^ 3 * N * Δ
        ≤ ((2 * n0 : ℕ) : ℝ) ^ 3 * N * ((gueGridK d n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hΔK (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hN0.le)
      _ ≤ 1 := hgrid1
  have hK' : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t := fun t ht I hI h1 h2 => hK n t ht I hI h1 (by omega)
  set err := 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n) with herrdef
  have hdisc : ∀ k ≤ gueGridK d n0 n, ∀ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖Kt n (gridTime t1 t0 (gueGridK d n0) n k) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 (gueGridK d n0) n 0) (loopOf x.1 x.2) -
        (Δ : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE (d.L n) (d.W n) (Kt n (gridTime t1 t0 (gueGridK d n0) n j))
            (loopOf x.1 x.2)‖ ≤ err := fun k hk x => by
    have h := Hyp_Kt_disc d Kt ht10 hK0 hK' hbd hsmall hk (loopOf x.1 x.2)
      (HypB_loopOf_wf _ _) (by rw [HypB_loopOf_length]; exact hm1)
      (by rw [HypB_loopOf_length]; exact hm)
    rw [HypB_size_cast] at h
    exact h
  have herr : ∀ t' ∈ Set.Icc (t1 n) (t0 n), err ≤ (gueScale d E n t')⁻¹ ^ m := by
    intro t' ht'
    have hsc := HypB_scale_pos d (E := E) hEb ht0 ht'.2
    have hsN : gueScale d E n t' ≤ N := by
      unfold gueScale
      have hη1 : etaT (E n) t' ≤ 1 := by
        unfold etaT
        have hm1' : (spectralM (E n)).im ≤ 1 := by
          have h1 := Complex.abs_im_le_norm (spectralM (E n))
          rw [norm_spectralM hEb.le] at h1
          exact (abs_le.mp h1).2
        have hm0 := (spectralM_im_pos hEb).le
        have : 1 - t' ≤ 1 := by linarith [ht'.1]
        have : 0 ≤ 1 - t' := by linarith [ht'.2]
        nlinarith
      have hη0 : 0 ≤ etaT (E n) t' := by
        unfold etaT; have := (spectralM_im_pos hEb).le; nlinarith [ht'.2]
      nlinarith
    have hinv : N⁻¹ ≤ (gueScale d E n t')⁻¹ := inv_anti₀ hsc hsN
    have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
    have hNi0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    calc err ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK d n0 n : ℝ))⁻¹ := by
          rw [herrdef]
          have h1 : t0 n - t1 n ≤ 1 := by linarith
          have h2 : 0 ≤ t0 n - t1 n := by linarith
          have h4 : Δ * (t0 n - t1 n) ≤ ((gueGridK d n0 n : ℝ))⁻¹ := by
            calc Δ * (t0 n - t1 n) ≤ Δ * 1 := mul_le_mul_of_nonneg_left h1 hΔ0
              _ ≤ _ := by rw [mul_one]; exact hΔK
          have h5 : (0 : ℝ) ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 :=
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
              (sq_nonneg _)
          calc 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n)
              = 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * (Δ * (t0 n - t1 n)) := by ring
            _ ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK d n0 n : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_left h4 h5
      _ ≤ (N⁻¹) ^ (2 * n0) := hgrid2
      _ ≤ (N⁻¹) ^ m := pow_le_pow_of_le_one hNi0 hNi1 hm
      _ ≤ (gueScale d E n t')⁻¹ ^ m := pow_le_pow_left₀ hNi0 hinv m
  -- the bound on `K̃` on the grid
  have hKt : ∀ j ≤ gueGridK d n0 n, ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ m → ‖Kt n (gridTime t1 t0 (gueGridK d n0) n j) J‖ ≤
        c * (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ ^ (J.length - 1) :=
    fun j hj J hJ h2 hJn => hKtc _ (Hyp_time_mem ht10 hK0 hj) J hJ h2 (hJn.trans hm)
  have hn2 : (m : ℝ) ^ 2 ≤ ((2 * n0 : ℕ) : ℝ) ^ 2 := by
    have : (m : ℝ) ≤ ((2 * n0 : ℕ) : ℝ) := by exact_mod_cast hm
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hpath := HypB_path d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m ω g3 g4 (c := c)
    (Ce := Ce) (err := err) hEb ht1 ht10 ht0 hK0 hm1 hc hCe0 hCe hΔ herr hg3 hg4 hg3c hg4c h0 hM hq
    hKt heG hdisc ht
  set R := N * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((N * etaT (E n) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n k u ω) *
            gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n (m - k + 2) u ω)
          (t1 n) t
        + (N * etaT (E n) t)⁻¹ ^ m
        + N * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t with hRdef
  have hK0' : (0 : ℝ) < 2 + 2 ^ m + 7 * (m : ℝ) ^ 2 := by positivity
  have hDp0 := gueDproc_nonneg d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω
  have hcpos : 0 < c := by linarith
  have hR0 : 0 ≤ R := by
    by_contra hneg
    push Not at hneg
    have : c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) * R < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hcpos hK0') hneg
    linarith
  have hKn : 2 + 2 ^ m + 7 * (m : ℝ) ^ 2 ≤ c := by
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ (2 * n0) := pow_le_pow_right₀ (by norm_num) hm
    rw [hcdef]
    linarith
  have hNτ : N ^ τ = c * c := by
    rw [hcdef, ← Real.rpow_add hN0]; ring_nf
  calc gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω
      ≤ c * (2 + 2 ^ m + 7 * (m : ℝ) ^ 2) * R := hpath
    _ ≤ c * c * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKn (by linarith)) hR0
    _ = N ^ τ * R := by rw [hNτ]

end HypBFixed


/-! ### Two more eventual facts at a fixed size index, the grid values and a continuity fact -/

section HypBFacts

/-- Step-size input: `Δ ≤ t₀ − t₁ ≤ N^{-τU} η_{t₀} ≤ 1 − t₀`. -/
theorem HypB_step_le {E t1 t0 : ℕ → ℝ} {τU : ℝ} (n0 n : ℕ) (hEb : |E n| < 2)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (h730 : t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n)) (hτU : 0 < τU) :
    gridStep t1 t0 (gueGridK d n0) n ≤ 1 - t0 n := by
  have hNR : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := HypB_one_le_size d n
  have hKR : (1 : ℝ) ≤ (gueGridK d n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (gueGridK_ne_zero d n0 n)
  have hm1 : (spectralM (E n)).im ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (spectralM (E n))
    rw [norm_spectralM hEb.le] at h1
    exact (abs_le.mp h1).2
  have hm0 := (spectralM_im_pos hEb).le
  have hη0 : 0 ≤ etaT (E n) (t0 n) := by unfold etaT; nlinarith
  have hη1 : etaT (E n) (t0 n) ≤ 1 - t0 n := by unfold etaT; nlinarith
  have hNp : ((d.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hstep : gridStep t1 t0 (gueGridK d n0) n ≤ t0 n - t1 n := by
    unfold gridStep
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc gridStep t1 t0 (gueGridK d n0) n ≤ t0 n - t1 n := hstep
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n) := h730
    _ ≤ 1 * etaT (E n) (t0 n) := mul_le_mul_of_nonneg_right hNp hη0
    _ ≤ 1 - t0 n := by rw [one_mul]; exact hη1

/-- `‖K̃_t(J)‖ ≤ 1` on `[t₁, t₀]` for `2 ≤ |J| ≤ 2n₀`, from the bound (7.36) at `τU/2` and
`(N η_t)^{-1} ≤ N^{-τU}`. -/
theorem HypB_Kt_le_one {E t1 t0 : ℕ → ℝ} {τU : ℝ} (hτU : 0 < τU) (n0 n : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (hEb : |E n| < 2) (ht0 : t0 n < 1)
    (hK1 : ∀ p : TimeIcc t1 t0 n × LoopSet (d.L n) (2 * n0), ‖Kt n p.1 p.2.1‖ ≤
      ((d.size n : ℕ) : ℝ) ^ (τU / 2) * (gueScale d E n p.1)⁻¹ ^ ((p.2.1).length - 1))
    (hscale : (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU)) :
    ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1 := by
  intro t ht J hJ h2 hJn
  have hNR : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := HypB_one_le_size d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have h := hK1 (⟨t, ht⟩, ⟨J, hJ, h2, hJn⟩)
  simp only at h
  have hst := HypB_scale_pos d (E := E) hEb ht0 ht.2
  have hs0 := HypB_scale_pos d (E := E) hEb ht0 (le_refl (t0 n))
  have hle : gueScale d E n (t0 n) ≤ gueScale d E n t := by
    unfold gueScale
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold etaT
    have := (spectralM_im_pos hEb).le
    nlinarith [ht.2]
  have hinv : (gueScale d E n t)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) :=
    (inv_anti₀ hs0 hle).trans hscale
  have hNp1 : ((d.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hNp0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
  have hpow : (gueScale d E n t)⁻¹ ^ (J.length - 1) ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := by
    calc (gueScale d E n t)⁻¹ ^ (J.length - 1) ≤ (((d.size n : ℕ) : ℝ) ^ (-τU)) ^ (J.length - 1) :=
          pow_le_pow_left₀ (inv_nonneg.2 hst.le) hinv _
      _ ≤ (((d.size n : ℕ) : ℝ) ^ (-τU)) ^ 1 := pow_le_pow_of_le_one hNp0 hNp1 (by omega)
      _ = ((d.size n : ℕ) : ℝ) ^ (-τU) := pow_one _
  have hcomb : ((d.size n : ℕ) : ℝ) ^ (τU / 2) * ((d.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  calc ‖Kt n t J‖ ≤ ((d.size n : ℕ) : ℝ) ^ (τU / 2) * (gueScale d E n t)⁻¹ ^ (J.length - 1) := h
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (τU / 2) * ((d.size n : ℕ) : ℝ) ^ (-τU) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hN0.le _)
    _ ≤ 1 := hcomb

/-- Grid values of the stopped process `L^{(m)}` before the stopping index. -/
theorem HypB_Lproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m j : ℕ)
    (ω : PathΩ d) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop d E t1 t0 K δ n ω) :
    gueLproc d E t1 t0 K δ n m (gridTime t1 t0 K n j) ω =
      RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n j ω))
        (spectralZ (E n) (gridTime t1 t0 K n j)) m := by
  have hσK : gueStop d E t1 t0 K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueLproc_time d E t1 t0 K δ n m j ht10 (by omega) ω, min_eq_left hj.le]
  rfl

/-- Grid values of the stopped process `D^{(m)}` before the stopping index. -/
theorem HypB_Dproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m j : ℕ)
    (ω : PathΩ d) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop d E t1 t0 K δ n ω) :
    gueDproc d E t1 t0 K δ Kt n m (gridTime t1 t0 K n j) ω = gueDmax d E t1 t0 K Kt n m j ω := by
  have hσK : gueStop d E t1 t0 K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueDproc_time d E t1 t0 K δ Kt n m j ht10 (by omega) ω, min_eq_left hj.le]

/-- Continuity of `u ↦ √(N⁻¹ η_u⁻²)` on `[t₁, t₀]`. -/
theorem HypB_sqrt_cont {E t1 t0 : ℕ → ℝ} (n : ℕ) (hEb : |E n| < 2) (ht0 : t0 n < 1) :
    ContinuousOn (fun u => Real.sqrt ((((d.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) u)⁻¹ ^ 2))
      (Set.Icc (t1 n) (t0 n)) := by
  have hηc : Continuous fun u => etaT (E n) u := by unfold etaT; fun_prop
  have hη : ∀ u ∈ Set.Icc (t1 n) (t0 n), etaT (E n) u ≠ 0 := fun u hu =>
    (etaT_pos hEb (by linarith [hu.2])).ne'
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul ((hηc.continuousOn.inv₀ hη).pow 2))

end HypBFacts




end RBM.Univ.GUEPhase

end
