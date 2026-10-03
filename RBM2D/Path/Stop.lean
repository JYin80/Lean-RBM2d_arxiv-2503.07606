/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Walk
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Grid stopping times and their stopping-time properties

The first block is generic (filtration-agnostic): `firstHit J θ K` is the first grid index
`j ≤ K` at which the adapted real process `J` reaches `θ` (else `K`), built on Mathlib's
`MeasureTheory.hittingBtwn`.  The second block specialises it to the coordinate filtration
`RBM.Path.filt d` of the grid walk `pathH`, for processes `j ↦ F j (pathH … j ω)` with
every `F j` Borel on matrices.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory RBM RBM.Gauss

section Generic

variable {Ω' : Type*} {m : MeasurableSpace Ω'}

/-- The first grid index `j ≤ K` at which `J j ω` reaches the threshold `θ`
(i.e. lands in `Set.Ici θ`), or `K` if it never does before the grid horizon. -/
noncomputable def firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) : Ω' → ℕ :=
  fun ω => MeasureTheory.hittingBtwn J (Set.Ici θ) 0 K ω

section OneProcess

variable {ℱ : Filtration ℕ m}

/-- `firstHit` is a stopping time for the filtration `ℱ`, provided the
underlying process `J` is `ℱ`-adapted. -/
theorem isStoppingTime_firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J) :
    IsStoppingTime ℱ (fun ω => (firstHit J θ K ω : ℕ)) :=
  hJ.isStoppingTime_hittingBtwn measurableSet_Ici

/-- `firstHit` never exceeds the grid horizon `K`. -/
theorem firstHit_le (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (ω : Ω') :
    firstHit J θ K ω ≤ K :=
  MeasureTheory.hittingBtwn_le ω

/-- The event that the grid has not stopped by time `j` is
`ℱ j`-measurable. -/
theorem lt_firstHit_measurableSet (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J)
    (j : ℕ) : MeasurableSet[ℱ j] {ω | j < firstHit J θ K ω} := by
  have hτ := isStoppingTime_firstHit (ℱ := ℱ) J θ K hJ
  have hmeas : MeasurableSet[ℱ j] {ω : Ω' | firstHit J θ K ω ≤ j} := by
    have h' := hτ.measurableSet_le j
    simpa using h'
  have hset : {ω : Ω' | j < firstHit J θ K ω} = {ω : Ω' | firstHit J θ K ω ≤ j}ᶜ := by
    ext ω; simp [not_le]
  rw [hset]
  exact hmeas.compl

/-- Strictly before the grid stops, the process is strictly below the
threshold. -/
theorem lt_firstHit_imp (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {j : ℕ} {ω : Ω'}
    (h : j < firstHit J θ K ω) : J j ω < θ := by
  have hnotmem : J j ω ∉ Set.Ici θ :=
    MeasureTheory.notMem_of_lt_hittingBtwn (u := J) (s := Set.Ici θ) (n := 0) h
      (Nat.zero_le j)
  simpa [Set.mem_Ici, not_le] using hnotmem

end OneProcess

section TwoProcesses

variable {ℱ : Filtration ℕ m}

/-- The minimum of two grid stopping times `firstHit J θ K` and
`firstHit J' θ' K` (over the same grid horizon `K`) is again a stopping time.
Cites Mathlib's `IsStoppingTime.min`. -/
theorem isStoppingTime_min_firstHit (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ)
    (hJ : Adapted ℱ J) (hJ' : Adapted ℱ J') :
    IsStoppingTime ℱ
      (fun ω => (min (firstHit J θ K ω) (firstHit J' θ' K ω) : ℕ)) := by
  have h1 := isStoppingTime_firstHit (ℱ := ℱ) J θ K hJ
  have h2 := isStoppingTime_firstHit (ℱ := ℱ) J' θ' K hJ'
  intro i
  have hunion := (h1.measurableSet_le i).union (h2.measurableSet_le i)
  convert hunion using 2
  ext ω
  simp [min_le_iff]

/-- The event that neither grid time has stopped by `j` is
`ℱ j`-measurable. -/
theorem lt_min_firstHit_measurableSet (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ)
    (hJ : Adapted ℱ J) (hJ' : Adapted ℱ J') (j : ℕ) :
    MeasurableSet[ℱ j]
      {ω | j < min (firstHit J θ K ω) (firstHit J' θ' K ω)} := by
  have hτ := isStoppingTime_min_firstHit (ℱ := ℱ) J J' θ θ' K hJ hJ'
  have hmeas :
      MeasurableSet[ℱ j]
        {ω : Ω' | min (firstHit J θ K ω) (firstHit J' θ' K ω) ≤ j} := by
    have h' := hτ.measurableSet_le j
    simpa using h'
  have hset :
      {ω : Ω' | j < min (firstHit J θ K ω) (firstHit J' θ' K ω)}
        = {ω : Ω' | min (firstHit J θ K ω) (firstHit J' θ' K ω) ≤ j}ᶜ := by
    ext ω; simp [not_le]
  rw [hset]
  exact hmeas.compl

/-- Strictly before both grid times stop, both processes are
strictly below their respective thresholds. -/
theorem lt_min_firstHit_imp (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ) {j : ℕ} {ω : Ω'}
    (h : j < min (firstHit J θ K ω) (firstHit J' θ' K ω)) :
    J j ω < θ ∧ J' j ω < θ' := by
  rw [lt_min_iff] at h
  exact ⟨lt_firstHit_imp J θ K h.1, lt_firstHit_imp J' θ' K h.2⟩

end TwoProcesses

/-- Per-`ω` identity turning a sum stopped at `τ` into a sum over the full
grid range with the stopped-indicator inserted, used to put stopped sums in Azuma
form. Purely combinatorial: no measurability or stopping-time hypothesis needed. -/
theorem sum_stopped {M : Type*} [AddCommMonoid M] (Y : ℕ → Ω' → M) (τ : Ω' → ℕ)
    (k : ℕ) (ω : Ω') :
    ∑ j ∈ Finset.range (min k (τ ω)), Y (j + 1) ω
      = ∑ j ∈ Finset.range k, ({ω' | j < τ ω'}.indicator (Y (j + 1))) ω := by
  have hfilter : (Finset.range k).filter (fun j => j < τ ω) = Finset.range (min k (τ ω)) := by
    ext j
    simp [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j < τ ω <;> simp [hj]

end Generic

section Grid

variable (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-! ### The matrix-level measurability lemma

`pathH_adapted` (`Walk.lean`) only gives entrywise `StronglyMeasurable[filt d k]` of the grid
walk `pathH`.  `Matrix i j ℂ` unfolds to the nested Pi type `i → j → ℂ`, and Mathlib's
`Matrix.measurable_iff` is stated for an arbitrary source `MeasurableSpace`, so it applies to the
relative measurable space `filt d k`.  This assembles the entrywise statement into the
matrix-level one. -/
theorem pathH_measurable_filt (k : ℕ) :
    Measurable[filt d k] (fun ω : PathΩ d => pathH d s t K n k ω) :=
  (@Matrix.measurable_iff (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ _ (PathΩ d) (filt d k)
      (fun ω => pathH d s t K n k ω)).mpr
    (fun i j => stronglyMeasurable_iff_measurable.mp (pathH_adapted d s t K n k i j))

/-- A "loop-observable" process built from a family `F` of measurable functions of the grid
matrix `pathH` is adapted to the coordinate filtration. -/
theorem adapted_of_measurable_pathH
    {F : ℕ → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) :
    Adapted (filt d) (fun j (ω : PathΩ d) => F j (pathH d s t K n j ω)) :=
  fun j => (hF j).comp (pathH_measurable_filt d s t K n j)

/-- The event that a grid-observable process has not yet stopped by time `j` is
`filt d j`-measurable. -/
theorem lt_firstHit_grid_measurableSet
    {F : ℕ → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (θ : ℝ) (K' : ℕ) (j : ℕ) :
    MeasurableSet[filt d j]
      {ω | j < firstHit (fun j (ω : PathΩ d) => F j (pathH d s t K n j ω)) θ K' ω} :=
  lt_firstHit_measurableSet (ℱ := filt d) (fun j (ω : PathΩ d) => F j (pathH d s t K n j ω)) θ K'
    (adapted_of_measurable_pathH d s t K n hF) j

/-- The event that neither of two grid-observable stopping times has fired by `j`
is `filt d j`-measurable. -/
theorem lt_min_firstHit_grid_measurableSet
    {F F' : ℕ → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℝ}
    (hF : ∀ j, Measurable (F j)) (hF' : ∀ j, Measurable (F' j)) (θ θ' : ℝ) (K' : ℕ) (j : ℕ) :
    MeasurableSet[filt d j]
      {ω | j < min (firstHit (fun j (ω : PathΩ d) => F j (pathH d s t K n j ω)) θ K' ω)
        (firstHit (fun j (ω : PathΩ d) => F' j (pathH d s t K n j ω)) θ' K' ω)} :=
  lt_min_firstHit_measurableSet (ℱ := filt d) (fun j (ω : PathΩ d) => F j (pathH d s t K n j ω))
    (fun j (ω : PathΩ d) => F' j (pathH d s t K n j ω)) θ θ' K'
    (adapted_of_measurable_pathH d s t K n hF) (adapted_of_measurable_pathH d s t K n hF') j

end Grid

end RBM.Path

end
