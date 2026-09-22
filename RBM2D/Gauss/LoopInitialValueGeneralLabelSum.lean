/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopInitialValueThreeLabelSum
import RBM2D.Gauss.LoopInitialValueConstantCount

/-!
# General initial-loop label sum

`List.ofFn` transports finite-function assignments to well-formed block-label
lists. Only constant assignments survive the initial block-projector product.
-/

namespace RBM.Gauss

open Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
private theorem all_same_of_no_mismatch
    (a : Z2 L) (as : List (Z2 L))
    (hm : ¬AdjacentMismatch L (a :: as)) :
    ∀ b ∈ as, b = a := by
  induction as generalizing a with
  | nil => simp
  | cons c cs ih =>
      have hac : a = c := by
        by_contra h
        exact hm (Or.inl h)
      have htail : ¬AdjacentMismatch L (c :: cs) := by
        intro h
        exact hm (Or.inr h)
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact hac.symm
      · exact (ih c htail b hmem).trans hac.symm

/-- The magnitude of a length-`m+1` initial loop, indexed by a finite
function, is the common value exactly on constant assignments. -/
theorem norm_initialLoopValue_ofFn {E : ℝ} (hE : |E| < 2)
    (m : ℕ) (σ : List Bool) (hσ : σ.length = m + 1)
    (f : Fin (m + 1) → Z2 L) :
    ‖initialLoopValue L W E ⟨σ, List.ofFn f⟩‖ =
      if f ∈ constantBlockAssignments L (m + 1) then
        ((W : ℝ)⁻¹) ^ (2 * m) else 0 := by
  classical
  have hI : (⟨σ, List.ofFn f⟩ : LoopIdx (Z2 L)).WF := by
    simp [LoopIdx.WF, hσ]
  by_cases hc : f ∈ constantBlockAssignments L (m + 1)
  · obtain ⟨a, -, ha⟩ : ∃ a : Z2 L, (fun _ : Fin (m + 1) => a) = f := by
      simpa [constantBlockAssignments] using hc
    have hsame : ∀ b ∈ List.replicate m a, b = a := by simp
    have hval := norm_initialLoopValue_all_same L W hE
      ⟨σ, a :: List.replicate m a⟩ (by simp [LoopIdx.WF, hσ])
      a (List.replicate m a) rfl hsame
    simpa [hc, List.ofFn_const, List.replicate_succ] using hval
  · let tail : Fin m → Z2 L := fun i => f i.succ
    have hword : List.ofFn f = f 0 :: List.ofFn tail := List.ofFn_succ
    have hm : AdjacentMismatch L (List.ofFn f) := by
      rw [hword]
      by_contra hnot
      have hsame := all_same_of_no_mismatch L (f 0) (List.ofFn tail) hnot
      have htail : ∀ i : Fin m, f i.succ = f 0 :=
        (List.forall_mem_ofFn_iff).mp hsame
      have hforall : ∀ i : Fin (m + 1), f i = f 0 := by
        intro i
        cases i using Fin.cases with
        | zero => rfl
        | succ j => exact htail j
      apply hc
      unfold constantBlockAssignments
      apply Finset.mem_image.mpr
      refine ⟨f 0, Finset.mem_univ _, ?_⟩
      funext i
      exact (hforall i).symm
    have hm' : AdjacentMismatch L (f 0 :: List.ofFn tail) := by
      simpa only [hword] using hm
    have hzero := initialLoopValue_zero_of_adjacentMismatch L W hE
      ⟨σ, List.ofFn f⟩ hI (f 0) (List.ofFn tail) hword hm'
    rw [hzero]
    simp [hc]

/-- For a fixed signed word of length `m+1`, summing the absolute initial
value over every block-label assignment leaves exactly `L²` constant words. -/
theorem sum_norm_initialLoopValue_ofFn {E : ℝ} (hE : |E| < 2)
    (m : ℕ) (σ : List Bool) (hσ : σ.length = m + 1) :
    ∑ f : Fin (m + 1) → Z2 L,
      ‖initialLoopValue L W E ⟨σ, List.ofFn f⟩‖ =
        (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * m) := by
  classical
  simp_rw [norm_initialLoopValue_ofFn L W hE m σ hσ]
  simp [card_constantBlockAssignments L (by omega : 0 < m + 1)]

/-- The same exact sum for any positive number `n` of signed edges. -/
theorem sum_norm_initialLoopValue_fin {E : ℝ} (hE : |E| < 2)
    {n : ℕ} (hn : 0 < n) (σ : List Bool) (hσ : σ.length = n) :
    ∑ f : Fin n → Z2 L,
      ‖initialLoopValue L W E ⟨σ, List.ofFn f⟩‖ =
        (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * (n - 1)) := by
  cases n with
  | zero => omega
  | succ m =>
      simpa [Nat.succ_eq_add_one] using
        sum_norm_initialLoopValue_ofFn L W hE m σ (by simpa using hσ)

end RBM.Gauss
