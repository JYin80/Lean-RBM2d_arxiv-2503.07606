/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Analysis.MomentClosing
import Mathlib.Topology.Order.Compact

/-!
# Removing the explicit supremum witness from moment closure

A pointwise upper bound on a nonempty time interval supplies the least upper bound required by
`RBM.sqrt_le_of_integral_le`. The bound and the integrated differential inequality remain
explicit hypotheses for a later matrix-model application.
-/

namespace RBM

open Real MeasureTheory

/-- The image of a nonempty closed time interval has a least upper bound whenever `ψ` is
bounded above there. Ported from the dimension-independent argument in
`RBM1D.Gauss.MomentDuhamelHyp`. -/
theorem exists_isLUB_Icc {ψ : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) {C : ℝ}
    (hC : ∀ u ∈ Set.Icc s t, ψ u ≤ C) : ∃ M, IsLUB (ψ '' Set.Icc s t) M := by
  refine Real.exists_isLUB ⟨ψ s, ⟨s, ⟨le_rfl, hst⟩, rfl⟩⟩ ⟨C, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  exact hC u hu

/-- A continuous real function is bounded above on a compact time interval. -/
theorem exists_upperBound_Icc_of_continuousOn {ψ : ℝ → ℝ} {s t : ℝ}
    (hcont : ContinuousOn ψ (Set.Icc s t)) :
    ∃ C, ∀ u ∈ Set.Icc s t, ψ u ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  exact ⟨C, fun u hu => hC (Set.mem_image_of_mem ψ hu)⟩

/-- Scale-preserving moment closure with a concrete interval upper bound in place of an
`IsLUB` witness. The model must still prove `hC` and the integrated inequality `hdu`. -/
theorem sqrt_le_of_integral_le_of_bdd {s t : ℝ} (hst : s ≤ t)
    {ψ f g : ℝ → ℝ} {c C : ℝ}
    (hψ0 : ∀ u ∈ Set.Icc s t, 0 ≤ ψ u)
    (hf0 : ∀ r ∈ Set.Icc s t, 0 ≤ f r)
    (hg0 : ∀ r ∈ Set.Icc s t, 0 ≤ g r) (hc0 : 0 ≤ c)
    (hC : ∀ u ∈ Set.Icc s t, ψ u ≤ C)
    (hintψf : ∀ u ∈ Set.Icc s t,
      IntervalIntegrable (fun r => √(ψ r) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s t)
    (hintg : IntervalIntegrable g volume s t)
    (hdu : ∀ u ∈ Set.Icc s t,
      ψ u ≤ ψ s + 2 * (∫ r in s..u, √(ψ r) * f r) + c * ∫ r in s..u, g r) :
    √(ψ t) ≤ √(ψ s) + 2 * (∫ r in s..t, f r) + √(c * ∫ r in s..t, g r) := by
  obtain ⟨M, hM⟩ := exists_isLUB_Icc hst hC
  exact sqrt_le_of_integral_le hst hψ0 hf0 hg0 hc0 hM hintψf hintf hintg hdu

/-- Continuity supplies the interval upper bound; the integrated inequality and all sign and
integrability assumptions remain explicit. -/
theorem sqrt_le_of_integral_le_of_continuousOn {s t : ℝ} (hst : s ≤ t)
    {ψ f g : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn ψ (Set.Icc s t))
    (hψ0 : ∀ u ∈ Set.Icc s t, 0 ≤ ψ u)
    (hf0 : ∀ r ∈ Set.Icc s t, 0 ≤ f r)
    (hg0 : ∀ r ∈ Set.Icc s t, 0 ≤ g r) (hc0 : 0 ≤ c)
    (hintψf : ∀ u ∈ Set.Icc s t,
      IntervalIntegrable (fun r => √(ψ r) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s t)
    (hintg : IntervalIntegrable g volume s t)
    (hdu : ∀ u ∈ Set.Icc s t,
      ψ u ≤ ψ s + 2 * (∫ r in s..u, √(ψ r) * f r) + c * ∫ r in s..u, g r) :
    √(ψ t) ≤ √(ψ s) + 2 * (∫ r in s..t, f r) + √(c * ∫ r in s..t, g r) := by
  obtain ⟨C, hC⟩ := exists_upperBound_Icc_of_continuousOn hcont
  exact sqrt_le_of_integral_le_of_bdd hst hψ0 hf0 hg0 hc0 hC hintψf hintf hintg hdu

/-- Nonconstant witness for the wrapper: `ψ(u) = 1 + u` and `g = 1` on `[0, 1]`. -/
theorem sqrt_le_of_integral_le_of_bdd_linear_example : √(2 : ℝ) ≤ 1 + √(1 : ℝ) := by
  have h := sqrt_le_of_integral_le_of_bdd (s := 0) (t := 1)
    (ψ := fun u : ℝ => 1 + u) (f := fun _ => 0) (g := fun _ => 1)
    (c := 1) (C := 2)
    (by norm_num)
    (by intro u hu; have := hu.1; linarith)
    (by intro u hu; norm_num)
    (by intro u hu; norm_num)
    (by norm_num)
    (by intro u hu; have := hu.2; linarith)
    (by intro u hu; simp)
    (by simp)
    (by simp)
    (by intro u hu; simp [intervalIntegral.integral_const])
  convert h using 1 <;> norm_num

/-- The continuity wrapper also applies to the nonconstant function `ψ(u) = 1 + u`. -/
theorem sqrt_le_of_integral_le_of_continuousOn_linear_example :
    √(2 : ℝ) ≤ 1 + √(1 : ℝ) := by
  have h := sqrt_le_of_integral_le_of_continuousOn (s := 0) (t := 1)
    (ψ := fun u : ℝ => 1 + u) (f := fun _ => 0) (g := fun _ => 1)
    (c := 1)
    (by norm_num)
    ((continuous_const.add continuous_id).continuousOn)
    (by intro u hu; have := hu.1; linarith)
    (by intro u hu; norm_num)
    (by intro u hu; norm_num)
    (by norm_num)
    (by intro u hu; simp)
    (by simp)
    (by simp)
    (by intro u hu; simp [intervalIntegral.integral_const])
  convert h using 1 <;> norm_num

end RBM
