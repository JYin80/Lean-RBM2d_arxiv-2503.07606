/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Grid
import RBM2D.Universality.GUEPhase.Bootstrap
import RBM2D.Universality.GUEPhase.Generator
import RBM2D.Universality.GUEPhase.KPrim
import RBM2D.Universality.GUEPhase.EntryDet
import RBM2D.Induction.Split
import RBM2D.Loop.KBound
import RBM2D.Path.ScalesBridge
import RBM2D.Path.Stop

/-!
# The process layer of the §7.2 random layer on the GUE-phase grid, `d = 2`

On the size scale:

* the a priori threshold `gueDelta` (`δ_n = (d.size n)^{-τU/4}`), the tent function `gueTent`, the
  piecewise-linear interpolation `gueInterp`, the entry deviation `gueDev`, the freezing index
  `gueStop`;
* the loop maximum / deviation / deterministic running maximum `gueLmax`, `gueDmax`, `gueKbar` at
  the grid steps, and the stopped interpolated processes `gueLproc`, `gueDproc`, `gueKproc`;
* their structural facts `gueLproc_nonneg`, …, `gueLproc_time`, `gueDproc_time`;
* `gueLoopMax_odd_succ_le`, `gueLoopMax_four_mul_le` ((6.4) and (5.117)), the Ward lower bound
  `gue_inv_W_le_loopMax` (`W⁻² ≤ 2 L₂`), the bound `norm_egtNGUE_le` on `𝓔^{(G̃)}`, the one-step
  jump `gueDev_succ_le` of the entry deviation by the resolvent identity;
* the deterministic bound `gueKproc_detDom` on the interpolated running maximum of `K̃`, in the
  explicit size-scale form.

Conventions (`d = 2`): the path is `PathΩ d` with `gridTime`, `gridStep`, `Path.firstHit`; the index
set is `Idx (d.L n) (d.W n)`, the matrix is `Sizes.seqXmat d n`, and the size is `d.size n`;
`RBM.Ind.loopMax (d.L n) (d.W n) (blockMat M) z m` is the loop maximum; loops are pairs
`(Fin m → Bool) × (Fin m → Z2 L)` with `loopOf`; the drift correction is `egtNGUE`; `N = (W L)²`
and `W²` count rows and blocks.

Helpers are `private` or carry the prefix `Proc_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### Definitions -/

/-- The a priori threshold `δ_n = N^{-τU/4}`, `N = d.size n`. -/
def gueDelta (τU : ℝ) (n : ℕ) : ℝ := ((d.size n : ℕ) : ℝ) ^ (-(τU / 4))

/-- The tent function at the grid time `u_k`. -/
def gueTent (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (t : ℝ) : ℝ :=
  max 0 (1 - |t - gridTime t1 t0 K n k| / gridStep t1 t0 K n)

/-- Piecewise-linear interpolation of grid values (`f 0` if `Δ = 0`). -/
def gueInterp (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  if gridStep t1 t0 K n = 0 then f 0
  else ∑ k ∈ Finset.range (K n + 1), f k * gueTent t1 t0 K n k t

/-- `max_{i,j} |(G_k - m)_{ij}|` at the grid step `k`. -/
def gueDev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) : ℝ :=
  ⨆ ij : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n),
    ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) ij.1 ij.2‖

/-- The freezing index: the first grid step with `gueDev ≥ δ_n` (else `K n`). -/
def gueStop (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n : ℕ) (ω : PathΩ d) : ℕ :=
  firstHit (fun k ω' => gueDev d E t1 t0 K n k ω') (δ n) (K n) ω

/-- `L^{(m)}_k = max_{σ,a} |L_{σ,a}|` at the grid step `k`. -/
def gueLmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n m k : ℕ) (ω : PathΩ d) : ℝ :=
  RBM.Ind.loopMax (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
    (spectralZ (E n) (gridTime t1 t0 K n k)) m

/-- `D^{(m)}_k = max_{x} |L_x - K̃_x|` at the grid step `k`. -/
def gueDmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (n m k : ℕ) (ω : PathΩ d) : ℝ :=
  ⨆ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
        (spectralZ (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2)‖

/-- `K̄^{(m)}_k = max_{j ≤ k} max_x |K̃(u_j, x)|`, the deterministic running maximum. -/
def gueKbar (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (n m k : ℕ) : ℝ :=
  ⨆ j : Fin (k + 1), ⨆ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
    ‖Kt n (gridTime t1 t0 K n j) (loopOf x.1 x.2)‖

/-- The stopped, interpolated `Lm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueLproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ) (ω : PathΩ d) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueLmax d E t1 t0 K n m (min k (gueStop d E t1 t0 K δ n ω)) ω) t

/-- The stopped, interpolated `Dm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueDproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ d) : ℝ :=
  gueInterp t1 t0 K n
    (fun k => gueDmax d E t1 t0 K Kt n m (min k (gueStop d E t1 t0 K δ n ω)) ω) t

/-- The deterministic `Km` fed to `eq727GEAt`. -/
def gueKproc (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (n m : ℕ) (t : ℝ) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueKbar d t1 t0 K Kt n m k) t

/-! ### Generic helpers for `gueInterp` -/

section GueInterpHelpers

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

private theorem Proc_gueTent_nonneg (k : ℕ) (t : ℝ) : 0 ≤ gueTent t1 t0 K n k t :=
  le_max_left _ _

private theorem Proc_gueInterp_add (f g : ℕ → ℝ) (t : ℝ) :
    gueInterp t1 t0 K n (fun k => f k + g k) t
      = gueInterp t1 t0 K n f t + gueInterp t1 t0 K n g t := by
  unfold gueInterp
  split_ifs with h0
  · rfl
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

private theorem Proc_gueInterp_mono {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (t : ℝ) :
    gueInterp t1 t0 K n f t ≤ gueInterp t1 t0 K n g t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (Proc_gueTent_nonneg k t)

private theorem Proc_gueInterp_nonneg {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (t : ℝ) :
    0 ≤ gueInterp t1 t0 K n f t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (h k) (Proc_gueTent_nonneg k t)

private theorem Proc_gueTent_continuous (j : ℕ) : Continuous (gueTent t1 t0 K n j) := by
  unfold gueTent
  fun_prop

private theorem Proc_gueInterp_continuousOn (f : ℕ → ℝ) :
    ContinuousOn (fun t => gueInterp t1 t0 K n f t) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueInterp
  by_cases h0 : gridStep t1 t0 K n = 0
  · simp only [ite_eq_left h0]
    exact continuousOn_const
  · simp only [ite_eq_right h0]
    exact (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (Proc_gueTent_continuous k)).continuousOn

private theorem Proc_gueInterp_sqrt_mul_le {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (t : ℝ) :
    gueInterp t1 t0 K n (fun k => Real.sqrt (a k * b k)) t
      ≤ Real.sqrt (gueInterp t1 t0 K n a t * gueInterp t1 t0 K n b t) := by
  unfold gueInterp
  split_ifs with h0
  · exact le_refl _
  · have hw : ∀ k, 0 ≤ gueTent t1 t0 K n k t := fun k => Proc_gueTent_nonneg k t
    rw [Real.sqrt_mul (Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hw k))]
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.range (K n + 1))
      (f := fun k => a k * gueTent t1 t0 K n k t) (g := fun k => b k * gueTent t1 t0 K n k t)
      (fun k => mul_nonneg (ha k) (hw k)) (fun k => mul_nonneg (hb k) (hw k))
    have heq : ∀ k, Real.sqrt (a k * gueTent t1 t0 K n k t)
        * Real.sqrt (b k * gueTent t1 t0 K n k t)
        = Real.sqrt (a k * b k) * gueTent t1 t0 K n k t := by
      intro k
      rw [← Real.sqrt_mul (mul_nonneg (ha k) (hw k)),
        show a k * gueTent t1 t0 K n k t * (b k * gueTent t1 t0 K n k t)
          = (a k * b k) * (gueTent t1 t0 K n k t) ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg (ha k) (hb k)), Real.sqrt_sq (hw k)]
    calc ∑ k ∈ Finset.range (K n + 1), Real.sqrt (a k * b k) * gueTent t1 t0 K n k t
        = ∑ k ∈ Finset.range (K n + 1),
            Real.sqrt (a k * gueTent t1 t0 K n k t) * Real.sqrt (b k * gueTent t1 t0 K n k t) :=
          Finset.sum_congr rfl fun k _ => (heq k).symm
      _ ≤ Real.sqrt (∑ k ∈ Finset.range (K n + 1), a k * gueTent t1 t0 K n k t) *
            Real.sqrt (∑ k ∈ Finset.range (K n + 1), b k * gueTent t1 t0 K n k t) := hcs

/-- Tent functions form a Kronecker delta at grid points, provided the grid is nondegenerate
(`Δ ≠ 0`) and `t1 n ≤ t0 n` (so `Δ ≥ 0`). -/
private theorem Proc_gueTent_time_eq (ht10 : t1 n ≤ t0 n) (hstep : gridStep t1 t0 K n ≠ 0)
    (j k : ℕ) :
    gueTent t1 t0 K n j (gridTime t1 t0 K n k) = if j = k then 1 else 0 := by
  have hK0 : (K n : ℝ) ≠ 0 := by
    intro hc
    apply hstep
    unfold gridStep
    rw [hc, div_zero]
  have hKpos : (0:ℝ) < (K n : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hK0)
  have hΔ0 : 0 ≤ gridStep t1 t0 K n := by
    unfold gridStep
    exact div_nonneg (by linarith) hKpos.le
  have hΔpos : 0 < gridStep t1 t0 K n := hΔ0.lt_of_ne (Ne.symm hstep)
  have hdiff : gridTime t1 t0 K n k - gridTime t1 t0 K n j
      = ((k : ℝ) - (j : ℝ)) * gridStep t1 t0 K n := by
    unfold gridTime; ring
  have habs : |gridTime t1 t0 K n k - gridTime t1 t0 K n j|
      = |(k : ℝ) - (j : ℝ)| * gridStep t1 t0 K n := by
    rw [hdiff, abs_mul, abs_of_pos hΔpos]
  unfold gueTent
  rw [habs, mul_div_assoc, div_self hΔpos.ne', mul_one]
  by_cases hjk : j = k
  · simp [hjk]
  · have h1 : (1 : ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      have hne : (k : ℝ) ≠ (j : ℝ) := by
        intro hc; exact hjk (by exact_mod_cast hc.symm)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_of_neg (by linarith)]
        have : (1:ℝ) ≤ (j:ℝ) - (k:ℝ) := by
          have hlt : (k:ℕ) < (j:ℕ) := by exact_mod_cast (by linarith : (k:ℝ) < (j:ℝ))
          have : (k:ℕ) + 1 ≤ (j:ℕ) := hlt
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this
          linarith
        linarith
      · rw [abs_of_pos (by linarith)]
        have hlt : (j:ℕ) < (k:ℕ) := by exact_mod_cast (by linarith : (j:ℝ) < (k:ℝ))
        have hle : (j:ℕ) + 1 ≤ (k:ℕ) := hlt
        have := (Nat.cast_le (α := ℝ)).2 hle
        push_cast at this
        linarith
    simp only [hjk, ite_false]
    have : 1 - |(k:ℝ) - (j:ℝ)| ≤ 0 := by linarith
    rw [max_eq_left_iff.2 this]

private theorem Proc_gueInterp_time {f : ℕ → ℝ} (hconst : gridStep t1 t0 K n = 0 → ∀ k', f k' = f 0)
    (ht10 : t1 n ≤ t0 n) {k : ℕ} (hk : k ≤ K n) :
    gueInterp t1 t0 K n f (gridTime t1 t0 K n k) = f k := by
  unfold gueInterp
  split_ifs with h0
  · exact (hconst h0 k).symm
  · rw [Finset.sum_eq_single k]
    · rw [Proc_gueTent_time_eq ht10 h0 k k, ite_eq_left rfl, mul_one]
    · intro j hj hjk
      rw [Proc_gueTent_time_eq ht10 h0 j k, ite_eq_right hjk, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.2 (by omega)) hk'

end GueInterpHelpers

/-! ### Constancy of the grid processes when `Δ = 0` -/

section GueConstZero

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

private theorem Proc_gueTime_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (k : ℕ) :
    gridTime t1 t0 K n k = t1 n := by
  unfold gridTime; rw [h0]; ring

private theorem Proc_gueH_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (k : ℕ)
    (ω : PathΩ d) : gueH d t1 t0 K n k ω = gueH d t1 t0 K n 0 ω := by
  unfold gueH
  rw [h0, zero_div, Real.sqrt_zero]
  simp

variable {E : ℕ → ℝ}

private theorem Proc_gueLmax_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (m k : ℕ)
    (ω : PathΩ d) :
    gueLmax d E t1 t0 K n m k ω = gueLmax d E t1 t0 K n m 0 ω := by
  unfold gueLmax
  rw [Proc_gueH_const_of_step_zero d h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

private theorem Proc_gueDmax_const_of_step_zero (h0 : gridStep t1 t0 K n = 0)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (m k : ℕ) (ω : PathΩ d) :
    gueDmax d E t1 t0 K Kt n m k ω = gueDmax d E t1 t0 K Kt n m 0 ω := by
  unfold gueDmax
  rw [Proc_gueH_const_of_step_zero d h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

end GueConstZero

/-! ### Pointwise triangle-inequality helpers -/

section GueTriangle

private theorem Proc_norm_le_norm_sub_add_norm {α : Type*} [SeminormedAddGroup α] (a b : α) :
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  calc ‖a‖ = ‖a - b + b‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _

private theorem Proc_le_ciSup_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {E : ℕ → ℝ}

private theorem Proc_gueLmax_le_gueDmax_add_gueKbar (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (n m k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ d) :
    gueLmax d E t1 t0 K n m k' ω ≤ gueDmax d E t1 t0 K Kt n m k' ω + gueKbar d t1 t0 K Kt n m k := by
  unfold gueLmax gueDmax gueKbar RBM.Ind.loopMax
  apply ciSup_le
  intro x
  have h1 := Proc_norm_le_norm_sub_add_norm
    (gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω)) (spectralZ (E n) (gridTime t1 t0 K n k'))
      (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n))))
    (Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n))))
  have h2 : ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
        (spectralZ (E n) (gridTime t1 t0 K n k'))
        (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n)))
      - Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n)))‖
      ≤ ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
          ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
            (spectralZ (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
            Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
    Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Z2 (d.L n)) =>
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
          (spectralZ (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
          Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n)))‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ := by
    calc ‖Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Z2 (d.L n)))‖
        ≤ ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Z2 (d.L n)) =>
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
            ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun j : Fin (k + 1) =>
            ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
              ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem Proc_gueDmax_le_gueLmax_add_gueKbar (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (n m k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ d) :
    gueDmax d E t1 t0 K Kt n m k' ω ≤ gueLmax d E t1 t0 K n m k' ω + gueKbar d t1 t0 K Kt n m k := by
  unfold gueDmax gueLmax RBM.Ind.loopMax gueKbar
  apply ciSup_le
  intro x
  have h1 := norm_sub_le
    (gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω)) (spectralZ (E n) (gridTime t1 t0 K n k'))
      (loopOf x.1 x.2))
    (Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2))
  have h2 : ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
        (spectralZ (E n) (gridTime t1 t0 K n k')) (loopOf x.1 x.2)‖
      ≤ ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
          ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
            (spectralZ (E n) (gridTime t1 t0 K n k'))
            ⟨List.ofFn y.1, List.ofFn y.2⟩‖ :=
    Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Z2 (d.L n)) =>
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k' ω))
          (spectralZ (E n) (gridTime t1 t0 K n k')) ⟨List.ofFn y.1, List.ofFn y.2⟩‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2)‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ := by
    calc ‖Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2)‖
        ≤ ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → Z2 (d.L n)) =>
            ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
            ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
          Proc_le_ciSup_finite (fun j : Fin (k + 1) =>
            ⨆ y : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
              ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem Proc_gueLmax_odd_sq_le (n l k : ℕ) (hl : 1 ≤ l) (ω : PathΩ d) :
    gueLmax d E t1 t0 K n (2 * l + 1) k ω ≤
      Real.sqrt (gueLmax d E t1 t0 K n (2 * l) k ω * gueLmax d E t1 t0 K n (2 * l + 2) k ω) := by
  unfold gueLmax
  exact Real.le_sqrt_of_sq_le
    (RBM.Ind.loopMax_odd_sq_le ((gueH_isHermitian d t1 t0 K n k ω).submatrix _) hl)

end GueTriangle

private theorem Proc_le_ciSup_finite_aux {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

/-! ### Structural facts of the stopped processes -/

theorem gueLproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ)
    (ω : PathΩ d) : 0 ≤ gueLproc d E t1 t0 K δ n m t ω := by
  unfold gueLproc
  exact Proc_gueInterp_nonneg (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg m) t

theorem gueDproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ d) :
    0 ≤ gueDproc d E t1 t0 K δ Kt n m t ω := by
  unfold gueDproc
  exact Proc_gueInterp_nonneg
    (fun k => by unfold gueDmax; exact Real.iSup_nonneg fun _ => norm_nonneg _) t

theorem gueLproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ)
    (ω : PathΩ d) :
    ContinuousOn (fun t => gueLproc d E t1 t0 K δ n m t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueLproc
  exact Proc_gueInterp_continuousOn _

theorem gueDproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (ω : PathΩ d) :
    ContinuousOn (fun t => gueDproc d E t1 t0 K δ Kt n m t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueDproc
  exact Proc_gueInterp_continuousOn _

/-- `hLDK` for the stopped processes (every `t`, every `ω`). -/
theorem gueLproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ d) :
    gueLproc d E t1 t0 K δ n m t ω ≤
      gueDproc d E t1 t0 K δ Kt n m t ω + gueKproc d t1 t0 K Kt n m t := by
  unfold gueLproc gueDproc gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => Proc_gueLmax_le_gueDmax_add_gueKbar d Kt n m (min k (gueStop d E t1 t0 K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hDLK` for the stopped processes (every `t`, every `ω`). -/
theorem gueDproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ d) :
    gueDproc d E t1 t0 K δ Kt n m t ω ≤
      gueLproc d E t1 t0 K δ n m t ω + gueKproc d t1 t0 K Kt n m t := by
  unfold gueDproc gueLproc gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => Proc_gueDmax_le_gueLmax_add_gueKbar d Kt n m (min k (gueStop d E t1 t0 K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hodd` for the stopped processes: (6.4) at the grid, Cauchy–Schwarz for the tent weights. -/
theorem gueLproc_odd (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n l : ℕ) (hl : 1 ≤ l) (t : ℝ)
    (ω : PathΩ d) :
    gueLproc d E t1 t0 K δ n (2 * l + 1) t ω ≤
      Real.sqrt (gueLproc d E t1 t0 K δ n (2 * l) t ω *
        gueLproc d E t1 t0 K δ n (2 * l + 2) t ω) := by
  unfold gueLproc
  set σ := gueStop d E t1 t0 K δ n ω with hσ
  calc gueInterp t1 t0 K n (fun k => gueLmax d E t1 t0 K n (2 * l + 1) (min k σ) ω) t
      ≤ gueInterp t1 t0 K n (fun k => Real.sqrt (gueLmax d E t1 t0 K n (2 * l) (min k σ) ω *
          gueLmax d E t1 t0 K n (2 * l + 2) (min k σ) ω)) t :=
        Proc_gueInterp_mono (fun k => Proc_gueLmax_odd_sq_le d n l (min k σ) hl ω) t
    _ ≤ Real.sqrt (gueInterp t1 t0 K n (fun k => gueLmax d E t1 t0 K n (2 * l) (min k σ) ω) t *
          gueInterp t1 t0 K n (fun k => gueLmax d E t1 t0 K n (2 * l + 2) (min k σ) ω) t) :=
        Proc_gueInterp_sqrt_mul_le (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg _)
          (fun k => by unfold gueLmax; exact RBM.Ind.loopMax_nonneg _) t

/-- Grid values of `gueLproc`. -/
theorem gueLproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m k : ℕ)
    (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) (ω : PathΩ d) :
    gueLproc d E t1 t0 K δ n m (gridTime t1 t0 K n k) ω =
      gueLmax d E t1 t0 K n m (min k (gueStop d E t1 t0 K δ n ω)) ω := by
  unfold gueLproc
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [Proc_gueLmax_const_of_step_zero d h0 m (min k' (gueStop d E t1 t0 K δ n ω)) ω, Nat.zero_min]

/-- Grid values of `gueDproc`. -/
theorem gueDproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m k : ℕ) (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n)
    (ω : PathΩ d) :
    gueDproc d E t1 t0 K δ Kt n m (gridTime t1 t0 K n k) ω =
      gueDmax d E t1 t0 K Kt n m (min k (gueStop d E t1 t0 K δ n ω)) ω := by
  unfold gueDproc
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [Proc_gueDmax_const_of_step_zero d h0 Kt m (min k' (gueStop d E t1 t0 K δ n ω)) ω,
    Nat.zero_min]

/-! ### Structural facts on the loop maxima (R6a, R6b), the Ward lower bound (A3) -/

section LoopMaxFacts

/-- **(R6a)**: for even length `2l`, `L_{2l+1} ≤ √L₂ · L_{2l}` ((6.4) + (5.117)). -/
theorem gueLoopMax_odd_succ_le {L W : ℕ} [NeZero L]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax L W H z (2 * l + 1) ≤
      Real.sqrt (RBM.Ind.loopMax L W H z 2) * RBM.Ind.loopMax L W H z (2 * l) := by
  have h0 := RBM.Ind.loopMax_two_mul_add_le (z := z) hH hl (le_refl 1)
  have h1 : RBM.Ind.loopMax L W H z (2 * l + 2) ≤
      RBM.Ind.loopMax L W H z (2 * l) * RBM.Ind.loopMax L W H z 2 := by
    have e1 : 2 * (l + 1) = 2 * l + 2 := by ring
    have e2 : 2 * 1 = 2 := by norm_num
    rwa [e1, e2] at h0
  have h2 := RBM.Ind.loopMax_odd_sq_le (z := z) hH hl
  have h3 : RBM.Ind.loopMax L W H z (2 * l + 1) ^ 2
      ≤ RBM.Ind.loopMax L W H z (2 * l) *
        (RBM.Ind.loopMax L W H z (2 * l) * RBM.Ind.loopMax L W H z 2) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (RBM.Ind.loopMax_nonneg _))
  have h4 : RBM.Ind.loopMax L W H z (2 * l + 1) ^ 2
      ≤ (RBM.Ind.loopMax L W H z (2 * l)) ^ 2 * RBM.Ind.loopMax L W H z 2 := by nlinarith [h3]
  calc RBM.Ind.loopMax L W H z (2 * l + 1)
      ≤ Real.sqrt ((RBM.Ind.loopMax L W H z (2 * l)) ^ 2 * RBM.Ind.loopMax L W H z 2) :=
        Real.le_sqrt_of_sq_le h4
    _ = Real.sqrt (RBM.Ind.loopMax L W H z 2 * (RBM.Ind.loopMax L W H z (2 * l)) ^ 2) := by
        rw [mul_comm]
    _ = Real.sqrt (RBM.Ind.loopMax L W H z 2) * Real.sqrt ((RBM.Ind.loopMax L W H z (2 * l)) ^ 2) :=
        Real.sqrt_mul (RBM.Ind.loopMax_nonneg _) _
    _ = Real.sqrt (RBM.Ind.loopMax L W H z 2) * RBM.Ind.loopMax L W H z (2 * l) := by
        rw [Real.sqrt_sq (RBM.Ind.loopMax_nonneg _)]

/-- **(R6b)**: for even length `2l`, `L_{4l} ≤ L_{2l}²` ((5.117)). -/
theorem gueLoopMax_four_mul_le {L W : ℕ} [NeZero L]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax L W H z (4 * l) ≤ RBM.Ind.loopMax L W H z (2 * l) ^ 2 := by
  have h := RBM.Ind.loopMax_two_mul_add_le (z := z) hH hl hl
  have e : 4 * l = 2 * (l + l) := by ring
  rw [e, sq]
  exact h

/-- `max_{a,b} |𝓛_{u,(+,-),(a,b)}| ≤ L₂` (the two-loops `(+,-)` are loops of length `2`). -/
private theorem Proc_maxLoopPM_le_loopMax {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) :
    maxLoopPM L W E u M ≤ RBM.Ind.loopMax L W (blockMat M) (spectralZ E u) 2 := by
  unfold maxLoopPM
  refine Finset.sup'_le _ _ fun p _ => ?_
  exact RBM.Ind.norm_gloop_le_loopMax (pmLoop p.1 p.2) rfl rfl

/-- **A3**: the Ward lower bound turns `W⁻²` into `2 L₂` on the a-priori event (with `hell`); it
uses `inv_N_le_maxLoopPM` (`N = (W L)²`), and `hell : L²(1-u) ≤ 1` with the factor `L²` of the
d = 2 row count. -/
theorem gue_inv_W_le_loopMax {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) (hell : (L : ℝ) ^ 2 * (1 - u) ≤ 1) {δ : ℝ}
    (hΩ : RBM.Green.GoodEvent (greenBlk L W E u M true) (spectralM E) δ)
    (hδ : δ ≤ (spectralM E).im / 2) :
    ((W : ℝ)⁻¹) ^ 2 ≤ 2 * RBM.Ind.loopMax L W (blockMat M) (spectralZ E u) 2 := by
  have him : 0 < (spectralM E).im := spectralM_im_pos hE
  have hzeq : (spectralZ E u).im = (1 - u) * (spectralM E).im := spectralZ_im E u
  have h1u : 0 < 1 - u := by linarith
  have hzim : 0 < (spectralZ E u).im := by rw [hzeq]; exact mul_pos h1u him
  have hward := inv_N_le_maxLoopPM hM hzim hΩ hδ
  have hmax := Proc_maxLoopPM_le_loopMax E u M
  have hmax0 : 0 ≤ maxLoopPM L W E u M := RBM.Green.maxLoopPM_nonneg E u M
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by push_cast; ring
  rw [hN, hzeq] at hward
  have heq : ((W : ℝ)⁻¹) ^ 2 = (2 * ((L : ℝ) ^ 2 * (1 - u))) *
      ((spectralM E).im / (2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((1 - u) * (spectralM E).im)))) := by
    field_simp
  have hc0 : 0 ≤ 2 * ((L : ℝ) ^ 2 * (1 - u)) := by positivity
  calc ((W : ℝ)⁻¹) ^ 2
      = (2 * ((L : ℝ) ^ 2 * (1 - u))) *
        ((spectralM E).im / (2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((1 - u) * (spectralM E).im)))) :=
        heq
    _ ≤ (2 * ((L : ℝ) ^ 2 * (1 - u))) * maxLoopPM L W E u M :=
        mul_le_mul_of_nonneg_left hward hc0
    _ ≤ (2 * 1) * maxLoopPM L W E u M := by
        apply mul_le_mul_of_nonneg_right _ hmax0
        linarith
    _ ≤ 2 * RBM.Ind.loopMax L W (blockMat M) (spectralZ E u) 2 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hmax (by norm_num)

end LoopMaxFacts

/-! ### The bound on `𝓔^{(G̃)}` for `SBgue` -/

section EgtBound

/-- **`𝓔^{(G̃)}` of the GUE profile** (`SBgue = 1/L²`): `|𝓔̃_GUE(I)| ≤ n · (W L)² · ε · B`
(hypothesis in the `avgErr` form).  The prefactor is `W²`, `SBgue = 1/L²` and the label sums over
`Z2 L` have `L²` terms each, so that `W² · (L² · L²) · L⁻² = (W L)²`. -/
theorem norm_egtNGUE_le (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) {ε B : ℝ}
    (hε : ∀ (σ : Bool) (a : Z2 L), ‖avgErr L W E u M σ a‖ ≤ ε)
    (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : Z2 L, ‖RBM.Ind.LLf L W E u M (I.cutGlue k b)‖ ≤ B) :
    ‖egtNGUE L W E u M I‖ ≤ (I.length : ℝ) * (((W * L) ^ 2 : ℕ) : ℝ) * ε * B := by
  rcases Nat.eq_zero_or_pos I.length with hn0 | hn1
  · have hSempty : Finset.Icc 1 I.length = (∅ : Finset ℕ) := by
      rw [hn0]; exact Finset.Icc_eq_empty (by omega)
    unfold egtNGUE
    rw [hSempty]
    simp [hn0]
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε true 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (Finset.mem_Icc.2 ⟨le_refl 1, hn1⟩) 0)
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hcard : Fintype.card (Z2 L) = L * L := by
      rw [Fintype.card_prod, ZMod.card]
    have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ a b : Z2 L,
        ‖avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
            RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
        ≤ ε * ((L : ℝ) ^ 2)⁻¹ * B := by
      intro k hk a b
      rw [norm_mul, norm_mul]
      have h1 := hε (I.σ.getD (k - 1) false) a
      have h2 : ‖SBgue L a b‖ = ((L : ℝ) ^ 2)⁻¹ := by
        rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
      have h3 := hB k hk b
      rw [h2]
      have e1 : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
      calc ‖avgErr L W E u M (I.σ.getD (k - 1) false) a‖ * ((L : ℝ) ^ 2)⁻¹ *
            ‖RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
          ≤ ε * ((L : ℝ) ^ 2)⁻¹ * ‖RBM.Ind.LLf L W E u M (I.cutGlue k b)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 e1) (norm_nonneg _)
        _ ≤ ε * ((L : ℝ) ^ 2)⁻¹ * B := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hTk : ∀ k ∈ Finset.Icc 1 I.length,
        ‖∑ a : Z2 L, ∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
            RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
        ≤ (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (ε * ((L : ℝ) ^ 2)⁻¹ * B)) := by
      intro k hk
      calc ‖∑ a : Z2 L, ∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
              RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
          ≤ ∑ a : Z2 L, ‖∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
              RBM.Ind.LLf L W E u M (I.cutGlue k b)‖ := norm_sum_le _ _
        _ ≤ ∑ _a : Z2 L, (L : ℝ) ^ 2 * (ε * ((L : ℝ) ^ 2)⁻¹ * B) := by
            apply Finset.sum_le_sum
            intro a _
            calc ‖∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
                    RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
                ≤ ∑ b : Z2 L, ‖avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
                    RBM.Ind.LLf L W E u M (I.cutGlue k b)‖ := norm_sum_le _ _
              _ ≤ ∑ _b : Z2 L, ε * ((L : ℝ) ^ 2)⁻¹ * B :=
                  Finset.sum_le_sum fun b _ => hterm k hk a b
              _ = (L : ℝ) ^ 2 * (ε * ((L : ℝ) ^ 2)⁻¹ * B) := by
                  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
                  push_cast; ring
        _ = (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (ε * ((L : ℝ) ^ 2)⁻¹ * B)) := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
            push_cast; ring
    unfold egtNGUE
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc (W : ℝ) ^ 2 * ‖∑ k ∈ Finset.Icc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
            avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
              RBM.Ind.LLf L W E u M (I.cutGlue k b)‖
        ≤ (W : ℝ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ‖∑ a : Z2 L, ∑ b : Z2 L,
            avgErr L W E u M (I.σ.getD (k - 1) false) a * SBgue L a b *
              RBM.Ind.LLf L W E u M (I.cutGlue k b)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (W : ℝ) ^ 2 * ∑ _k ∈ Finset.Icc 1 I.length,
            (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (ε * ((L : ℝ) ^ 2)⁻¹ * B)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hTk) (by positivity)
      _ = (W : ℝ) ^ 2 * ((I.length : ℝ) * ((L : ℝ) ^ 2 * ((L : ℝ) ^ 2 *
            (ε * ((L : ℝ) ^ 2)⁻¹ * B)))) := by
          have hc : (Finset.Icc 1 I.length).card = I.length := by
            rw [Nat.card_Icc]; omega
          rw [Finset.sum_const, hc, nsmul_eq_mul]
      _ = (I.length : ℝ) * (((W * L) ^ 2 : ℕ) : ℝ) * ε * B := by
          push_cast
          field_simp

end EgtBound

/-! ### The one-step change of the entry deviation -/

section DevStep

open scoped Matrix.Norms.L2Operator

/-- `‖A‖ ≤ ∑_{ij} |A_{ij}|` for the `ℓ² → ℓ²` operator norm. -/
private theorem Proc_opNorm_le_sum_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i : n, ∑ j : n, ‖A i j‖ := by
  set S : ℝ := ∑ i : n, ∑ j : n, ‖A i j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set T := toEuclideanCLM (n := n) (𝕜 := ℂ) A with hT
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine T.opNorm_le_bound hS0 fun x => ?_
  have hx : ∀ j, ‖x j‖ ≤ ‖x‖ := fun j => PiLp.norm_apply_le x j
  have hrow : ∀ i, ‖(T x) i‖ ≤ (∑ j, ‖A i j‖) * ‖x‖ := by
    intro i
    have : (T x) i = ∑ j, A i j * x j := by
      simp [hT, Matrix.mulVec, dotProduct]
    rw [this]
    calc ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)
      _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
  have hl2 : ‖T x‖ ≤ ∑ i, ‖(T x) i‖ := by
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖(T x) i‖ ^ 2) ≤ Real.sqrt ((∑ i, ‖(T x) i‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _)
      _ = ∑ i, ‖(T x) i‖ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => norm_nonneg _)
  calc ‖T x‖ ≤ ∑ i, ‖(T x) i‖ := hl2
    _ ≤ ∑ i, (∑ j, ‖A i j‖) * ‖x‖ := Finset.sum_le_sum fun i _ => hrow i
    _ = S * ‖x‖ := by rw [hS, Finset.sum_mul]

/-- The two-parameter resolvent bound
`‖G(H', z') - G(H, z)‖ ≤ ‖G(H', z')‖ (‖H' - H‖ + |z' - z|) ‖G(H, z)‖`
(`norm_green_sub_le_of_herm` is for equal `z`). -/
private theorem Proc_norm_green_sub_le {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    {H H' : Matrix ν ν ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) {z z' : ℂ}
    (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    ‖green H' z' - green H z‖ ≤ ‖green H' z'‖ * (‖H' - H‖ + ‖z' - z‖) * ‖green H z‖ := by
  have hu := isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := isUnit_sub_smul_one_of_im_ne_zero hH' hz'
  have hd : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hd' : IsUnit (H' - z' • (1 : Matrix ν ν ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu'
  have h1 : green H' z' * (H' - z' • (1 : Matrix ν ν ℂ)) = 1 := by
    rw [green]; exact Matrix.nonsing_inv_mul _ hd'
  have h2 : (H - z • (1 : Matrix ν ν ℂ)) * green H z = 1 := by
    rw [green]; exact Matrix.mul_nonsing_inv _ hd
  have hid : green H' z' - green H z
      = green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ)) * green H z := by
    have hmid : (H - H') + (z' - z) • (1 : Matrix ν ν ℂ)
        = (H - z • (1 : Matrix ν ν ℂ)) - (H' - z' • (1 : Matrix ν ν ℂ)) := by
      module
    have e1 : green H' z' * (H - z • (1 : Matrix ν ν ℂ)) * green H z = green H' z' := by
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    have e2 : green H' z' * (H' - z' • (1 : Matrix ν ν ℂ)) * green H z = green H z := by
      rw [h1, Matrix.one_mul]
    rw [hmid, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [hid]
  have hnorm : ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖ ≤ ‖H' - H‖ + ‖z' - z‖ := by
    calc ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖
        ≤ ‖H - H'‖ + ‖(z' - z) • (1 : Matrix ν ν ℂ)‖ := norm_add_le _ _
      _ = ‖H' - H‖ + ‖z' - z‖ := by rw [norm_sub_rev H H', norm_smul, norm_one, mul_one]
  calc ‖green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ)) * green H z‖
      ≤ ‖green H' z' * ((H - H') + (z' - z) • (1 : Matrix ν ν ℂ))‖ * ‖green H z‖ :=
        norm_mul_le _ _
    _ ≤ ‖green H' z'‖ * ‖(H - H') + (z' - z) • (1 : Matrix ν ν ℂ)‖ * ‖green H z‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖green H' z'‖ * (‖H' - H‖ + ‖z' - z‖) * ‖green H z‖ := by
        gcongr

private theorem Proc_gridTime_mono {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n)
    {i j : ℕ} (hij : i ≤ j) : gridTime t1 t0 K n i ≤ gridTime t1 t0 K n j := by
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold gridTime
  nlinarith [hstep0]

/-- **One-step change of the entry deviation**: the
resolvent identity `G' - G = G' ((H - H') + (z' - z)) G`, `H' - H = √(Δ/N) X_{k+1}`,
`|z' - z| = Δ |m| = Δ`, and `η_u ≥ η_{t₀}` at the grid times. -/
theorem gueDev_succ_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hE : |E n| < 2)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) (ω : PathΩ d) :
    gueDev d E t1 t0 K n (k + 1) ω ≤ gueDev d E t1 t0 K n k ω +
      (etaT (E n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) *
        ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
          ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
  have : Nonempty (Idx (d.L n) (d.W n)) := ⟨(0 : Z2 (d.W n * d.L n))⟩
  have hKne : K n ≠ 0 := by omega
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have htimeK : gridTime t1 t0 K n (K n) = t0 n := gridTime_last t1 t0 K n hKne
  have htk : gridTime t1 t0 K n k ≤ t0 n :=
    htimeK ▸ Proc_gridTime_mono ht10 (by omega : k ≤ K n)
  have htk1 : gridTime t1 t0 K n (k + 1) ≤ t0 n :=
    htimeK ▸ Proc_gridTime_mono ht10 (by omega : k + 1 ≤ K n)
  have him : 0 < (spectralM (E n)).im := spectralM_im_pos hE
  have hetak : etaT (E n) (t0 n) ≤ etaT (E n) (gridTime t1 t0 K n k) := by
    unfold etaT; nlinarith [htk]
  have hetak1 : etaT (E n) (t0 n) ≤ etaT (E n) (gridTime t1 t0 K n (k + 1)) := by
    unfold etaT; nlinarith [htk1]
  have het0pos : 0 < etaT (E n) (t0 n) := by unfold etaT; nlinarith [ht0]
  have hzkim : (spectralZ (E n) (gridTime t1 t0 K n k)).im = etaT (E n) (gridTime t1 t0 K n k) :=
    spectralZ_im (E n) (gridTime t1 t0 K n k)
  have hzk1im : (spectralZ (E n) (gridTime t1 t0 K n (k + 1))).im
      = etaT (E n) (gridTime t1 t0 K n (k + 1)) := spectralZ_im (E n) (gridTime t1 t0 K n (k + 1))
  have hetakpos : 0 < etaT (E n) (gridTime t1 t0 K n k) := lt_of_lt_of_le het0pos hetak
  have hetak1pos : 0 < etaT (E n) (gridTime t1 t0 K n (k + 1)) := lt_of_lt_of_le het0pos hetak1
  have hzkim0 : (spectralZ (E n) (gridTime t1 t0 K n k)).im ≠ 0 := by rw [hzkim]; linarith
  have hzk1im0 : (spectralZ (E n) (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by
    rw [hzk1im]; linarith
  have hHk := gueH_isHermitian d t1 t0 K n k ω
  have hHk1 := gueH_isHermitian d t1 t0 K n (k + 1) ω
  have hGk_le : ‖green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaT (E n) (t0 n))⁻¹ :=
    RBM.Gauss.norm_green_le hHk het0pos (by rw [hzkim, abs_of_pos hetakpos]; exact hetak)
  have hGk1_le :
      ‖green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))‖
      ≤ (etaT (E n) (t0 n))⁻¹ :=
    RBM.Gauss.norm_green_le hHk1 het0pos (by rw [hzk1im, abs_of_pos hetak1pos]; exact hetak1)
  have hHdiff : gueH d t1 t0 K n (k + 1) ω - gueH d t1 t0 K n k ω
      = (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ) •
          Sizes.seqXmat d n (ω (k + 1)) := by
    unfold gueH
    have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp), smul_add]
    abel
  have hHnorm : ‖gueH d t1 t0 K n (k + 1) ω - gueH d t1 t0 K n k ω‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ))
        * ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
            ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ := by
    rw [hHdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Proc_opNorm_le_sum_norm _) (Real.sqrt_nonneg _)
  have hzdiff : spectralZ (E n) (gridTime t1 t0 K n (k + 1)) -
      spectralZ (E n) (gridTime t1 t0 K n k) = (-(gridStep t1 t0 K n : ℂ)) * spectralM (E n) := by
    unfold spectralZ gridTime
    push_cast
    ring
  have hznorm : ‖spectralZ (E n) (gridTime t1 t0 K n (k + 1)) -
      spectralZ (E n) (gridTime t1 t0 K n k)‖ = gridStep t1 t0 K n := by
    rw [hzdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hstep0,
      norm_spectralM (by linarith [abs_lt.mp hE]), mul_one]
  have hAZ : ‖gueH d t1 t0 K n (k + 1) ω - gueH d t1 t0 K n k ω‖
        + ‖spectralZ (E n) (gridTime t1 t0 K n (k + 1)) - spectralZ (E n) (gridTime t1 t0 K n k)‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) *
          ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
            ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ + gridStep t1 t0 K n := by
    rw [hznorm]; exact add_le_add hHnorm (le_refl _)
  have hAZ0 : 0 ≤ ‖gueH d t1 t0 K n (k + 1) ω - gueH d t1 t0 K n k ω‖
        + ‖spectralZ (E n) (gridTime t1 t0 K n (k + 1)) - spectralZ (E n) (gridTime t1 t0 K n k)‖ := by
    positivity
  have hGdiff := Proc_norm_green_sub_le hHk hHk1 hzkim0 hzk1im0
  have hop : ‖green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
        - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaT (E n) (t0 n))⁻¹ ^ 2 *
        (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) *
          ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
            ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
    have hη0 : 0 ≤ (etaT (E n) (t0 n))⁻¹ := by positivity
    calc ‖green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
            - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))‖
        ≤ ‖green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))‖
            * (‖gueH d t1 t0 K n (k + 1) ω - gueH d t1 t0 K n k ω‖
              + ‖spectralZ (E n) (gridTime t1 t0 K n (k + 1)) -
                  spectralZ (E n) (gridTime t1 t0 K n k)‖)
            * ‖green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))‖ := hGdiff
      _ ≤ (etaT (E n) (t0 n))⁻¹
            * (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) *
                ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
                  ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ + gridStep t1 t0 K n)
            * (etaT (E n) (t0 n))⁻¹ := by
          apply mul_le_mul (mul_le_mul hGk1_le hAZ hAZ0 hη0) hGk_le (norm_nonneg _)
          positivity
      _ = (etaT (E n) (t0 n))⁻¹ ^ 2 *
            (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) *
              ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n),
                ‖Sizes.seqXmat d n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
          ring
  unfold gueDev
  apply ciSup_le
  intro ij
  have heq : (green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
        - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) ij.1 ij.2
      = (green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))) ij.1 ij.2
        + (green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))
            - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
            ij.1 ij.2 := by
    simp only [Matrix.sub_apply]
    ring
  have hE1 : ‖(green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
        - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
          ij.1 ij.2‖
      ≤ ‖(green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))) ij.1 ij.2‖
        + ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))
            - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
              ij.1 ij.2‖ := by
    rw [heq]; exact norm_add_le _ _
  have hE2 : ‖(green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
        - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))) ij.1 ij.2‖
      ≤ ‖green (gueH d t1 t0 K n (k + 1) ω) (spectralZ (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))‖ :=
    RBM.Ind.norm_apply_le_l2_opNorm _ ij.1 ij.2
  have hE3 : ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))
        - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
          ij.1 ij.2‖
      ≤ ⨆ ij' : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n),
          ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))
            - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
              ij'.1 ij'.2‖ :=
    Proc_le_ciSup_finite_aux (fun ij' : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) =>
        ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k))
          - spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
            ij'.1 ij'.2‖) ij
  linarith [hE1, hE2, hE3, hop]

end DevStep

/-! ### `gueKproc_detDom`: the deterministic bound on `K̃`, interpolated, on the size scale -/

section KprocDom

/-- Two nearby continuum points give comparable values of the (affine, decreasing) scale
`lam n t = M (1 - t) (Im m)`, provided the gap is dominated by the value at the right endpoint
`t0`. -/
private theorem Proc_lam_near_le {M im0 t t' t0 Δ : ℝ} (hM : 0 ≤ M) (him0 : 0 ≤ im0)
    (him1 : im0 ≤ 1) (ht' : t' ≤ t0) (hclose : |t - t'| ≤ Δ)
    (hsmall : M * Δ ≤ M * (1 - t0) * im0) :
    M * (1 - t) * im0 ≤ 2 * (M * (1 - t') * im0) := by
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hclose
  have hMim0 : 0 ≤ M * im0 := mul_nonneg hM him0
  have hLt0t' : M * (1 - t0) * im0 ≤ M * (1 - t') * im0 := by
    have h : M * im0 * (t0 - t') ≥ 0 := mul_nonneg hMim0 (by linarith)
    nlinarith [h]
  have habs1 := abs_le.mp hclose
  have hb0 : M * im0 * (t - t') ≤ M * im0 * Δ := mul_le_mul_of_nonneg_left habs1.2 hMim0
  have hb1 : M * im0 * (t - t') ≤ M * Δ := by
    have hstep : M * im0 * Δ ≤ M * Δ := by
      have hle : M * im0 ≤ M * 1 := mul_le_mul_of_nonneg_left him1 hM
      nlinarith [mul_le_mul_of_nonneg_right hle hΔ0]
    linarith [hb0, hstep]
  nlinarith [hb1, hsmall, hLt0t']

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- At most two grid tents are nonzero at a continuum point, and each is `≤ 1`, so the whole
partition of unity is `≤ 2`. -/
private theorem Proc_gueTent_sum_le_two (t : ℝ) (hstep : 0 < gridStep t1 t0 K n)
    (ht1 : t1 n ≤ t) :
    ∑ k ∈ Finset.range (K n + 1), gueTent t1 t0 K n k t ≤ 2 := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set s := (t - t1 n) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hzero : ∀ k ∈ Finset.range (K n + 1), k ≠ k0 → k ≠ k0 + 1 →
      gueTent t1 t0 K n k t = 0 := by
    intro k _ hk1 hk2
    unfold gueTent gridTime
    rw [← hΔdef]
    have hval : t - (t1 n + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have hkcase : k < k0 ∨ k0 + 1 < k := by omega
    rcases hkcase with hlt | hgt
    · have h1 : (k : ℝ) + 1 ≤ (k0 : ℝ) := by exact_mod_cast hlt
      have h2 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have habsk : |s - (k : ℝ)| = s - (k : ℝ) := abs_of_nonneg (by linarith)
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
    · have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
        rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
  have hsub : ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1))
      ⊆ Finset.range (K n + 1) := Finset.filter_subset _ _
  have heq : ∑ k ∈ Finset.range (K n + 1), gueTent t1 t0 K n k t
      = ∑ k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1),
          gueTent t1 t0 K n k t := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hk'
    simp only [Finset.mem_filter, not_and, not_or] at hk'
    exact hzero k hk (hk' hk).1 (hk' hk).2
  rw [heq]
  have hcard : ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card ≤ 2 := by
    calc ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card
        ≤ ({k0, k0 + 1} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_filter] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hk.2
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  calc ∑ k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), gueTent t1 t0 K n k t
      ≤ ∑ _k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        unfold gueTent
        exact max_le (by norm_num)
          (by linarith [div_nonneg (abs_nonneg (t - gridTime t1 t0 K n k)) hstep.le])
    _ = ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 := by exact_mod_cast hcard

/-- `b⁻¹ ≤ 2a⁻¹` from `a ≤ 2b` (elementary real-analysis helper). -/
private theorem Proc_inv_le_two_inv_of_le_two_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ 2 * b) : b⁻¹ ≤ 2 * a⁻¹ := by
  rw [show (2 : ℝ) * a⁻¹ = 2 / a by ring, inv_eq_one_div, div_le_div_iff₀ hb ha]
  linarith

/-- `gueKbar` is nondecreasing in the grid index (a running maximum). -/
private theorem Proc_gueKbar_mono (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (m : ℕ) {k k' : ℕ}
    (hkk' : k ≤ k') :
    gueKbar d t1 t0 K Kt n m k ≤ gueKbar d t1 t0 K Kt n m k' := by
  unfold gueKbar
  apply ciSup_le
  intro j
  exact Proc_le_ciSup_finite_aux
    (fun j' : Fin (k' + 1) => ⨆ x : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ‖Kt n (gridTime t1 t0 K n j') (loopOf x.1 x.2)‖)
    ⟨j, by omega⟩

/-- Every grid time with index `≤ K n` lies in `[t1 n, t0 n]`. -/
private theorem Proc_gueTime_mem_Icc (ht10' : t1 n ≤ t0 n) (hKne : K n ≠ 0) {k : ℕ}
    (hk : k ≤ K n) : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) := by
  refine ⟨?_, ?_⟩
  · have h0 := Proc_gridTime_mono (K := K) ht10' (Nat.zero_le k)
    have e : gridTime t1 t0 K n 0 = t1 n := by simp [gridTime]
    rwa [e] at h0
  · have h1 := Proc_gridTime_mono (K := K) ht10' hk
    rwa [gridTime_last t1 t0 K n hKne] at h1

/-- There is a grid index `kstar ≤ K n` within one step of any `t ∈ [t1 n, t0 n]`, which
dominates (in index) every grid index whose tent is nonzero at `t`. -/
private theorem Proc_gueTime_kstar_near (hstep : 0 < gridStep t1 t0 K n) (_ht10' : t1 n ≤ t0 n)
    (t : ℝ) (htlo : t1 n ≤ t) (hthi : t ≤ t0 n) (hKne : K n ≠ 0) :
    ∃ kstar : ℕ, kstar ≤ K n ∧ |t - gridTime t1 t0 K n kstar| ≤ gridStep t1 t0 K n ∧
      ∀ k : ℕ, k ≤ K n → gueTent t1 t0 K n k t > 0 → k ≤ kstar := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set s := (t - t1 n) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hKNne0 : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
  have hΔKN : Δ * (K n : ℝ) = t0 n - t1 n := by
    rw [hΔdef]; unfold gridStep; field_simp
  have hsKN : s ≤ (K n : ℝ) := by
    rw [hsdef, div_le_iff₀ hstep]
    linarith [hΔKN, hthi]
  have hk0KN : k0 ≤ K n := by
    have := Nat.floor_le hs0
    have hle : (k0 : ℝ) ≤ (K n : ℝ) := le_trans this hsKN
    exact_mod_cast hle
  refine ⟨min (k0 + 1) (K n), min_le_right _ _, ?_, ?_⟩
  · by_cases hcase : k0 + 1 ≤ K n
    · rw [min_eq_left hcase]
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have htimeeq : gridTime t1 t0 K n (k0 + 1) - t = Δ * ((k0 : ℝ) + 1 - s) := by
        unfold gridTime; rw [← hΔdef, hsdef]; push_cast; field_simp; ring
      have hnn : 0 ≤ (k0 : ℝ) + 1 - s := by linarith
      have hle1 : (k0 : ℝ) + 1 - s ≤ 1 := by linarith
      rw [abs_sub_comm, htimeeq, abs_of_nonneg (by positivity)]
      nlinarith [hstep.le]
    · have hk0eq : k0 = K n := by omega
      rw [min_eq_right (by omega : K n ≤ k0 + 1)]
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have h1' : (K n : ℝ) ≤ s := by rw [← hk0eq]; exact h1
      have hseq : s = (K n : ℝ) := le_antisymm hsKN h1'
      have hts : t - t1 n = Δ * (K n : ℝ) := by
        rw [hsdef] at hseq; field_simp at hseq; linarith
      have htimeeq : gridTime t1 t0 K n (K n) = t1 n + Δ * (K n : ℝ) := by
        unfold gridTime; rw [← hΔdef]; ring
      rw [htimeeq]
      have hteq : t = t1 n + Δ * (K n : ℝ) := by linarith
      rw [hteq]
      simp [hstep.le]
  · intro k hkKN hkpos
    by_contra hcon
    have hgt : k0 + 1 < k := by omega
    apply absurd hkpos (not_lt.2 (le_of_eq ?_))
    unfold gueTent gridTime
    rw [← hΔdef]
    have hval : t - (t1 n + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
    have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
    have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
      rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
    have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
    rw [mul_div_cancel_left₀ _ hstep.ne']
    exact max_eq_left hgoal

/-- The per-grid-index bound on `gueKbar` obtained from a pointwise bound `hbase` at fixed `n`,
using that the bound is monotone increasing in the grid index. -/
private theorem Proc_gueKbar_le_of_hbase (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n n0 m : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (lam : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ht10n : t1 n ≤ t0 n) (hKne : K n ≠ 0)
    (hlam_pos : ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < lam t)
    (hlam_anti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      lam t ≤ lam u)
    (hbase : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 → ‖Kt n t I‖ ≤ A * (lam t)⁻¹ ^ (I.length - 1))
    (hm2 : 2 ≤ m) (hm2n0 : m ≤ 2 * n0) (k : ℕ) (hk : k ≤ K n) :
    gueKbar d t1 t0 K Kt n m k ≤ A * (lam (gridTime t1 t0 K n k))⁻¹ ^ (m - 1) := by
  unfold gueKbar
  apply ciSup_le
  intro j
  apply ciSup_le
  intro x
  have hjk : (j : ℕ) ≤ k := by omega
  have htimej_mem : gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n) :=
    Proc_gueTime_mem_Icc ht10n hKne (by omega)
  have htimek_mem : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) :=
    Proc_gueTime_mem_Icc ht10n hKne hk
  have hIlen : (loopOf x.1 x.2 : LoopIdx (Z2 (d.L n))).length = m := by
    simp [loopOf, LoopIdx.length]
  have hIWF : (loopOf x.1 x.2 : LoopIdx (Z2 (d.L n))).WF := by
    simp [loopOf, LoopIdx.WF]
  have hbound := hbase _ htimej_mem (loopOf x.1 x.2) hIWF (by omega) (by omega)
  rw [hIlen] at hbound
  refine hbound.trans ?_
  have hle : lam (gridTime t1 t0 K n k) ≤ lam (gridTime t1 t0 K n j) :=
    hlam_anti _ htimej_mem _ htimek_mem (Proc_gridTime_mono ht10n hjk)
  have hinvle : (lam (gridTime t1 t0 K n j))⁻¹ ^ (m - 1)
      ≤ (lam (gridTime t1 t0 K n k))⁻¹ ^ (m - 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 (hlam_pos _ htimej_mem).le)
      (inv_anti₀ (hlam_pos _ htimek_mem) hle) (m - 1)
  exact mul_le_mul_of_nonneg_left hinvle hA

end KprocDom

/-! #### The size-scale input: `K̃` at `t₁` and the bootstrap (7.36) -/

section KprocInput

private theorem Proc_size_pos (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.size n := by
    unfold Sizes.size
    have hW := d.W_pos n
    have hL := d.three_le_L n
    positivity
  exact_mod_cast h1

private theorem Proc_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.size n := by
    unfold Sizes.size
    have hW := d.W_pos n
    have hL := d.three_le_L n
    positivity
  exact_mod_cast h1

private theorem Proc_etaT_nonneg {e t : ℝ} (ht : t ≤ 1) : 0 ≤ etaT e t := by
  unfold etaT
  have h2 : 0 ≤ (spectralM e).im := by rw [spectralM_im]; positivity
  nlinarith

private theorem Proc_etaT_anti (e : ℝ) {u t : ℝ} (hut : u ≤ t) : etaT e t ≤ etaT e u := by
  unfold etaT
  have h2 : 0 ≤ (spectralM e).im := by rw [spectralM_im]; positivity
  nlinarith

private theorem Proc_gueScale_pos {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) (n : ℕ)
    {t : ℝ} (ht : t < 1) : 0 < gueScale d E n t := by
  have h2 : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  unfold gueScale
  exact mul_pos (Proc_size_pos d n) (etaT_pos h2 ht)

private theorem Proc_ofFn_getD {α : Type*} (l : List α) (dflt : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i dflt) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `KLoop.loopOf` of its own signs and labels. -/
private theorem Proc_loopOf_eq {L : ℕ} [NeZero L] (J : LoopIdx (Z2 L)) (hJ : J.WF) :
    KLoop.loopOf L (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i 0) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [KLoop.loopOf, LoopIdx.length]
  rw [Proc_ofFn_getD σ' false a'.length hJ, Proc_ofFn_getD a' 0 a'.length rfl]

/-- The initial data of `K̃` at `t₁`: `‖Kcal_{t₁, I}‖ ≤ N^{τ'} (N η_{t₁})^{-|I|+1}` for loops of
length in `[2, 2 n₀]`, from `Kbound_prec_uncond` at the parameter point
`(d.L n, d.W n, E n, t1 n)` of `KLoop.Par κ (d.size n)` and `ℓ_{t₁} = L` (`hell`); the `≺` has
no explicit constant, the finitely many lengths are intersected, and `Tendsto d.size atTop atTop`
turns `∀ᶠ N` into `∀ᶠ n`. -/
private theorem Proc_initial {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto d.size atTop atTop)
    (hell : ∀ᶠ n : ℕ in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ n : ℕ in atTop, ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n (t1 n) I‖ ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (gueScale d E n (t1 n))⁻¹ ^ (I.length - 1) := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ ℓ ∈ Finset.Icc 2 (2 * n0),
      ∀ x : (p : KLoop.Par κ N) × (Fin ℓ → Bool) × (Fin ℓ → Z2 p.L),
        ‖KLoop.Kcal x.1.L x.1.W x.1.E x.1.t (KLoop.loopOf x.1.L x.2.1 x.2.2)‖ ≤
          (N : ℝ) ^ τ' * (KLoop.Mt x.1.L x.1.W x.1.E x.1.t)⁻¹ ^ (ℓ - 1) :=
    (Filter.eventually_all_finset _).2 fun ℓ hℓ =>
      KLoop.Kbound_prec_uncond ℓ (by have := (Finset.mem_Icc.1 hℓ).1; omega) κ hκ τ' hτ'
  filter_upwards [hsz.eventually hall, hell] with n hn hellN I hWF h2 h2n
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hIlen : I.length ∈ Finset.Icc 2 (2 * n0) := Finset.mem_Icc.2 ⟨h2, h2n⟩
  let par : KLoop.Par κ (d.size n) :=
    { L := d.L n, W := d.W n, hL := d.three_le_L n, hW := d.W_pos n,
      hN := (Sizes.size_eq d n).symm, E := E n, hE := hE n, t := t1 n,
      ht0 := ht1 n, ht1 := ht1lt }
  have hx := hn I.length hIlen
    ⟨par, fun i : Fin I.length => I.σ.getD i false, fun i : Fin I.length => I.a.getD i 0⟩
  have hx' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n)
        (KLoop.loopOf (d.L n) (fun i : Fin I.length => I.σ.getD i false)
          (fun i : Fin I.length => I.a.getD i 0))‖ ≤
      ((d.size n : ℕ) : ℝ) ^ τ' * (KLoop.Mt (d.L n) (d.W n) (E n) (t1 n))⁻¹ ^ (I.length - 1) := hx
  rw [Proc_loopOf_eq I hWF] at hx'
  have hMt : KLoop.Mt (d.L n) (d.W n) (E n) (t1 n) = gueScale d E n (t1 n) := by
    rw [kloop_Mt_eq ht1lt.le]
    unfold scaleM gueScale
    rw [ellT_eq_L ht1lt hellN, Sizes.size_eq]
    push_cast
    ring
  rw [hKinit n I, ← hMt]
  exact hx'

/-- (7.36) on the size scale: for every `τ > 0`, eventually in `n`, `‖K̃_{t,I}‖ ≤ N^τ (N η_t)^{-|I|+1}`
on `[t₁, t₀]` for loops of length in `[2, 2 n₀]`.  The scale-free `eq736` is applied at each `n`
with `A = N^{τ'}`, `ε = N^{-τ_U}`; the three index-scale thresholds (`eventually_small`,
`2 ≤ N^{τ-τ'}`, and the initial bound) are transferred along `d.size`. -/
private theorem Proc_hbase {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto d.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n t I‖ ≤ ((d.size n : ℕ) : ℝ) ^ τ * (gueScale d E n t)⁻¹ ^ (I.length - 1) := by
  set τ' := min τ τU / 2 with hτ'
  have hτ'0 : 0 < τ' := by have := lt_min hτ hτU; positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : τ' < τU := by have := min_le_right τ τU; linarith
  filter_upwards [Proc_initial d hκ n0 hE ht1 ht10 ht0 hsz hell Kt hKinit hτ'0, h730,
    hsz.eventually (eventually_small (n := 2 * n0) hτ'U),
    hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ'τ))] with n hinit h730n hε h2
  intro t ht I hWF h2I hIn
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := Proc_size_pos d n
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale d E n u := fun u hu =>
    Proc_gueScale_pos d hE hκ n (ht1lt u hu)
  have hanti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      gueScale d E n v ≤ gueScale d E n u := by
    intro u _ v _ huv
    unfold gueScale
    exact mul_le_mul_of_nonneg_left (Proc_etaT_anti (E n) huv) hN0.le
  have hlamc : ContinuousOn (gueScale d E n) (Set.Icc (t1 n) (t0 n)) := by
    have heq : gueScale d E n = fun t => ((d.size n : ℕ) : ℝ) * ((1 - t) * (spectralM (E n)).im) :=
      rfl
    rw [heq]
    fun_prop
  have hA : 0 < ((d.size n : ℕ) : ℝ) ^ τ' := Real.rpow_pos_of_pos hN0 _
  have hsmall : ∀ u ∈ Set.Icc (t1 n) (t0 n),
      (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) * (u - t1 n) ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * gueScale d E n u := by
    intro u hu
    have h1 : u - t1 n ≤ t0 n - t1 n := by linarith [hu.2]
    have h2' : etaT (E n) (t0 n) ≤ etaT (E n) u := Proc_etaT_anti (E n) hu.2
    have hNpow : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
    have h3 : u - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) u :=
      le_trans h1 (le_trans h730n (mul_le_mul_of_nonneg_left h2' hNpow))
    have e : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = ((d.size n : ℕ) : ℝ) := rfl
    rw [e]
    unfold gueScale
    calc ((d.size n : ℕ) : ℝ) * (u - t1 n)
        ≤ ((d.size n : ℕ) : ℝ) * (((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) u) :=
          mul_le_mul_of_nonneg_left h3 hN0.le
      _ = ((d.size n : ℕ) : ℝ) ^ (-τU) * (((d.size n : ℕ) : ℝ) * etaT (E n) u) := by ring
  have key := eq736 (d.L n) (d.W n) (Kt n) (n := 2 * n0) (ht10 n) (gueScale d E n) hlam hanti
    hlamc (hK n) hA (fun J hJ h2J hJn => hinit J hJ h2J hJn) hsmall hε t ht I hWF h2I hIn
  have hx : 0 ≤ (gueScale d E n t)⁻¹ ^ (I.length - 1) :=
    pow_nonneg (inv_pos.2 (hlam t ht)).le _
  have hsplit : ((d.size n : ℕ) : ℝ) ^ τ
      = ((d.size n : ℕ) : ℝ) ^ (τ - τ') * ((d.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [hsplit]
  have : 2 * ((d.size n : ℕ) : ℝ) ^ τ' * (gueScale d E n t)⁻¹ ^ (I.length - 1)
      ≤ ((d.size n : ℕ) : ℝ) ^ (τ - τ') * ((d.size n : ℕ) : ℝ) ^ τ' *
        (gueScale d E n t)⁻¹ ^ (I.length - 1) := by
    gcongr
  linarith

/-- **`hK` for `gueKproc`**: `K̃ ≺ Λ^{m-1}` on the grid, interpolated, in the explicit size-scale
form `∀ ε > 0, ∀ᶠ n, … ≤ (d.size n)^ε · (N η_t)^{-(m-1)}`, with `N = d.size n = (W L)²` (`h730`,
`hscale` on `N^{-τ_U}`).  The initial data at `t₁` come from `Kbound_prec_uncond`, the bootstrap
`eq736` is applied at each `n`, and `Tendsto d.size atTop atTop` (`hsz`) turns `∀ᶠ N` into
`∀ᶠ n`.  The hypothesis `hscale` is not used and is kept as stated. -/
theorem gueKproc_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hsz : Tendsto d.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n : ℕ in atTop, (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n : ℕ in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * n0)),
      gueKproc d t1 t0 (gueGridK d n0) Kt n (m : ℕ) (t : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ ε * (gueScale d E n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1) := by
  have _hs := hscale
  intro τ hτ
  have hτ'0 : 0 < τ / 2 := by positivity
  filter_upwards [Proc_hbase d hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell Kt hKinit
      (fun n t ht I hWF h2 hlen => hK n t ht I hWF (by omega) (by omega)) hτ'0, h730,
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ (2 * n0 + 1)) hτ'0)] with n hbaseN h730n h2pow
  rintro ⟨t, ht⟩ ⟨m, hm⟩
  simp only [Set.mem_Icc] at hm ht
  change gueKproc d t1 t0 (gueGridK d n0) Kt n m t ≤
    ((d.size n : ℕ) : ℝ) ^ τ * (gueScale d E n t)⁻¹ ^ (m - 1)
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  have hN0 : 0 < Nn := Proc_size_pos d n
  have hN1 : 1 ≤ Nn := Proc_one_le_size d n
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam_pos : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale d E n u := fun u hu =>
    Proc_gueScale_pos d hE hκ n (ht1lt u hu)
  have hlam_anti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      gueScale d E n v ≤ gueScale d E n u := by
    intro u _ v _ huv
    unfold gueScale
    exact mul_le_mul_of_nonneg_left (Proc_etaT_anti (E n) huv) hN0.le
  have hKne : gueGridK d n0 n ≠ 0 := gueGridK_ne_zero d n0 n
  have hstepN : gridStep t1 t0 (gueGridK d n0) n ≤ etaT (E n) (t0 n) := by
    have hetat0nonneg : 0 ≤ etaT (E n) (t0 n) := Proc_etaT_nonneg (ht0 n).le
    have hK1 : (1 : ℝ) ≤ (gueGridK d n0 n : ℝ) := by
      have hge1 : 1 ≤ gueGridK d n0 n := Nat.one_le_iff_ne_zero.2 hKne
      exact_mod_cast hge1
    have hNpow_le1 : Nn ^ (-τU) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    unfold gridStep
    have hK0 : (0 : ℝ) < (gueGridK d n0 n : ℝ) := by linarith
    rw [div_le_iff₀ hK0]
    calc t0 n - t1 n ≤ Nn ^ (-τU) * etaT (E n) (t0 n) := h730n
      _ ≤ 1 * etaT (E n) (t0 n) := mul_le_mul_of_nonneg_right hNpow_le1 hetat0nonneg
      _ = etaT (E n) (t0 n) := one_mul _
      _ ≤ etaT (E n) (t0 n) * (gueGridK d n0 n : ℝ) := by nlinarith [hK1, hetat0nonneg]
  have hperk : ∀ k : ℕ, k ≤ gueGridK d n0 n →
      gueKbar d t1 t0 (gueGridK d n0) Kt n m k ≤
        Nn ^ (τ / 2) * (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ (m - 1) :=
    fun k hk => Proc_gueKbar_le_of_hbase d t1 t0 (gueGridK d n0) n n0 m Kt (gueScale d E n)
      (Nn ^ (τ / 2)) (Real.rpow_nonneg hN0.le _) (ht10 n) hKne hlam_pos hlam_anti
      (fun u hu I hWF h2 hlen => hbaseN u hu I hWF h2 hlen) hm.1 hm.2 k hk
  by_cases hstep0 : gridStep t1 t0 (gueGridK d n0) n = 0
  · have ht1t0eq : t1 n = t0 n := by
      by_contra hne
      apply hne
      have hKR : (gueGridK d n0 n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
      have := hstep0
      unfold gridStep at this
      field_simp at this
      linarith [this]
    have hteq : t = t1 n := le_antisymm (by rw [ht1t0eq]; exact ht.2) ht.1
    have hgoal_eq : gueKproc d t1 t0 (gueGridK d n0) Kt n m t
        = gueKbar d t1 t0 (gueGridK d n0) Kt n m 0 := by
      unfold gueKproc gueInterp
      rw [ite_eq_left hstep0]
    rw [hgoal_eq, hteq]
    have h0 := hperk 0 (Nat.zero_le _)
    have e0 : gridTime t1 t0 (gueGridK d n0) n 0 = t1 n := by simp [gridTime]
    rw [e0] at h0
    refine h0.trans ?_
    have hnn : (0 : ℝ) ≤ (gueScale d E n (t1 n))⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos (t1 n) ⟨le_refl _, ht10 n⟩).le) _
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hnn
  · have hstepPos : 0 < gridStep t1 t0 (gueGridK d n0) n :=
      lt_of_le_of_ne (div_nonneg (by linarith [ht10 n]) (Nat.cast_nonneg _)) (Ne.symm hstep0)
    obtain ⟨kstar, hkstarKN, hknear, hkdom⟩ :=
      Proc_gueTime_kstar_near hstepPos (ht10 n) t ht.1 ht.2 hKne
    have htimekstar_mem : gridTime t1 t0 (gueGridK d n0) n kstar ∈ Set.Icc (t1 n) (t0 n) :=
      Proc_gueTime_mem_Icc (ht10 n) hKne hkstarKN
    have hlamnear : gueScale d E n t ≤ 2 * gueScale d E n (gridTime t1 t0 (gueGridK d n0) n kstar) := by
      have hM : (0 : ℝ) ≤ Nn := hN0.le
      have hE2 : |E n| ≤ 2 := by have := hE n; have := hκ; linarith
      have him1 : (spectralM (E n)).im ≤ 1 := by
        have h1 := Complex.abs_im_le_norm (spectralM (E n))
        rw [norm_spectralM hE2] at h1
        exact (abs_le.mp h1).2
      have him0 : 0 ≤ (spectralM (E n)).im := by rw [spectralM_im]; positivity
      have hsmall : Nn * gridStep t1 t0 (gueGridK d n0) n ≤
          Nn * (1 - t0 n) * (spectralM (E n)).im := by
        have hstepmul := mul_le_mul_of_nonneg_left hstepN hM
        rw [show Nn * etaT (E n) (t0 n) = Nn * (1 - t0 n) * (spectralM (E n)).im by
          unfold etaT; ring] at hstepmul
        exact hstepmul
      have hkey := Proc_lam_near_le hM him0 him1 htimekstar_mem.2 hknear hsmall
      unfold gueScale etaT
      linarith [hkey, mul_assoc Nn (1 - t) (spectralM (E n)).im,
        mul_assoc Nn (1 - gridTime t1 t0 (gueGridK d n0) n kstar) (spectralM (E n)).im]
    have hinvnear : (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n kstar))⁻¹
        ≤ 2 * (gueScale d E n t)⁻¹ :=
      Proc_inv_le_two_inv_of_le_two_mul (hlam_pos t ht) (hlam_pos _ htimekstar_mem) hlamnear
    have hkstarbound : gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar ≤
        Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale d E n t)⁻¹ ^ (m - 1)) := by
      refine (hperk kstar hkstarKN).trans ?_
      have hNnn2 : (0 : ℝ) ≤ Nn ^ (τ / 2) := Real.rpow_nonneg hN0.le _
      apply mul_le_mul_of_nonneg_left _ hNnn2
      have hkstarinv_nn : (0 : ℝ) ≤ (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n kstar))⁻¹ :=
        inv_nonneg.2 (hlam_pos _ htimekstar_mem).le
      have htinv_nn : (0 : ℝ) ≤ (gueScale d E n t)⁻¹ ^ (m - 1) :=
        pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
      calc (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n kstar))⁻¹ ^ (m - 1)
          ≤ (2 * (gueScale d E n t)⁻¹) ^ (m - 1) :=
            pow_le_pow_left₀ hkstarinv_nn hinvnear (m - 1)
        _ = 2 ^ (m - 1) * (gueScale d E n t)⁻¹ ^ (m - 1) := by rw [mul_pow]
        _ ≤ 2 ^ (2 * n0) * (gueScale d E n t)⁻¹ ^ (m - 1) := by
            apply mul_le_mul_of_nonneg_right _ htinv_nn
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hgueKproc_le : gueKproc d t1 t0 (gueGridK d n0) Kt n m t
        ≤ 2 * gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar := by
      unfold gueKproc gueInterp
      rw [ite_eq_right hstep0]
      have hdomle : ∀ k, k ∈ Finset.range (gueGridK d n0 n + 1) →
          gueKbar d t1 t0 (gueGridK d n0) Kt n m k * gueTent t1 t0 (gueGridK d n0) n k t
            ≤ gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar *
              gueTent t1 t0 (gueGridK d n0) n k t := by
        intro k hk
        by_cases hpos : 0 < gueTent t1 t0 (gueGridK d n0) n k t
        swap
        · have htent0 : gueTent t1 t0 (gueGridK d n0) n k t = 0 :=
            le_antisymm (not_lt.1 hpos) (Proc_gueTent_nonneg k t)
          rw [htent0, mul_zero, mul_zero]
        · have hkkstar : k ≤ kstar :=
            hkdom k (by simpa using (Finset.mem_range.mp hk : k < gueGridK d n0 n + 1)) hpos
          exact mul_le_mul_of_nonneg_right (Proc_gueKbar_mono d Kt m hkkstar)
            (Proc_gueTent_nonneg k t)
      calc ∑ k ∈ Finset.range (gueGridK d n0 n + 1),
            gueKbar d t1 t0 (gueGridK d n0) Kt n m k * gueTent t1 t0 (gueGridK d n0) n k t
          ≤ ∑ k ∈ Finset.range (gueGridK d n0 n + 1),
              gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar *
                gueTent t1 t0 (gueGridK d n0) n k t :=
            Finset.sum_le_sum hdomle
        _ = gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar *
              ∑ k ∈ Finset.range (gueGridK d n0 n + 1), gueTent t1 t0 (gueGridK d n0) n k t := by
            rw [Finset.mul_sum]
        _ ≤ gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar * 2 := by
            have hkbar_nonneg : (0 : ℝ) ≤ gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar := by
              unfold gueKbar
              exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
            apply mul_le_mul_of_nonneg_left (Proc_gueTent_sum_le_two t hstepPos ht.1) hkbar_nonneg
        _ = 2 * gueKbar d t1 t0 (gueGridK d n0) Kt n m kstar := by ring
    have hcomb : gueKproc d t1 t0 (gueGridK d n0) Kt n m t
        ≤ 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale d E n t)⁻¹ ^ (m - 1))) := by
      refine hgueKproc_le.trans ?_
      exact mul_le_mul_of_nonneg_left hkstarbound (by norm_num)
    refine hcomb.trans ?_
    have hfin : 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale d E n t)⁻¹ ^ (m - 1)))
        = (2 ^ (2 * n0 + 1)) * Nn ^ (τ / 2) * (gueScale d E n t)⁻¹ ^ (m - 1) := by ring
    rw [hfin]
    have hpow2N : (2 : ℝ) ^ (2 * n0 + 1) ≤ Nn ^ (τ / 2) := h2pow
    have hNpow_split : Nn ^ τ = Nn ^ (τ / 2) * Nn ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hNpow_split]
    have htinv_nn' : (0 : ℝ) ≤ (gueScale d E n t)⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
    have hfinal : (2 : ℝ) ^ (2 * n0 + 1) * Nn ^ (τ / 2) ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) :=
      mul_le_mul_of_nonneg_right hpow2N (Real.rpow_nonneg hN0.le _)
    exact mul_le_mul_of_nonneg_right hfinal htinv_nn'

end KprocInput

end RBM.Univ.GUEPhase
