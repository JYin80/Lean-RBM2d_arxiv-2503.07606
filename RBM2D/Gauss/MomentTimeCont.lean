/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Time continuity of bounded moments

A deterministic bound on the entire sample space and continuity of every sample path imply
continuity of the moment integral. These assumptions remain to be verified for any particular
matrix observable. The argument is dimension-independent and follows the corresponding part
of `RBM1D.Gauss.MomentDuhamelHypGauss`.
-/

namespace RBM.Gauss

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under a uniform deterministic envelope, dominated convergence makes the `q`-th absolute
moment continuous in time. The bound holds for every sample point, including bad events. -/
theorem continuousOn_integral_abs_pow_of_envelope {P : Measure Ω} [IsFiniteMeasure P]
    {S : Set ℝ} {f : ℝ → Ω → ℝ} {C : ℝ} (q : ℕ)
    (hmeas : ∀ u ∈ S, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn (fun u => ∫ ω, |f u ω| ^ q ∂P) S := by
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ : Ω => |C| ^ q) ?_ ?_
    (integrable_const _) ?_
  · intro u hu
    have h := ((hmeas u hu).norm).pow q
    have he : ((fun ω => ‖f u ω‖) ^ q) = fun ω => |f u ω| ^ q := by
      funext ω
      simp [Real.norm_eq_abs]
    rwa [he] at h
  · refine fun u hu => Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) q)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hbd u hu ω).trans (le_abs_self C)) q
  · exact Filter.Eventually.of_forall fun ω => ((hcont ω).abs).pow q

/-- A positive regularization of the `2p`-moment retains time continuity. The sample-path
continuity, slice measurability, and whole-space envelope are all explicit inputs. -/
theorem continuousOn_regularized_momentRoot_of_envelope {P : Measure Ω} [IsFiniteMeasure P]
    {S : Set ℝ} {f : ℝ → Ω → ℝ} {C ε : ℝ} {p : ℕ}
    (hε : 0 < ε)
    (hmeas : ∀ u ∈ S, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn
      (fun u => ((∫ ω, |f u ω| ^ (2 * p) ∂P) + ε) ^ (1 / (p : ℝ))) S := by
  have hφ := continuousOn_integral_abs_pow_of_envelope (P := P) (q := 2 * p)
    hmeas hbd hcont
  have hbase : ContinuousOn (fun u => (∫ ω, |f u ω| ^ (2 * p) ∂P) + ε) S :=
    hφ.add continuousOn_const
  refine hbase.rpow_const (fun u hu => Or.inl ?_)
  have hint : 0 ≤ ∫ ω, |f u ω| ^ (2 * p) ∂P :=
    integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _
  exact ne_of_gt (add_pos_of_nonneg_of_pos hint hε)

/-- A nonconstant sample path on `[0,1]` satisfies the regularized-moment continuity lemma. -/
theorem continuousOn_regularized_momentRoot_linear_example :
    ContinuousOn
      (fun u : ℝ => ((∫ _ : Unit, |u| ^ (2 : ℕ) ∂(Measure.dirac ())) + 1) ^ (1 : ℝ))
      (Set.Icc 0 1) := by
  have h := continuousOn_regularized_momentRoot_of_envelope
    (P := Measure.dirac ()) (S := Set.Icc 0 1)
    (f := fun u (_ : Unit) => u) (C := 1) (ε := 1) (p := 1)
    (by norm_num)
    (by intro u hu; exact aestronglyMeasurable_const)
    (by intro u hu ω; exact abs_le.mpr ⟨by linarith [hu.1], hu.2⟩)
    (by intro ω; exact continuous_id.continuousOn)
  simpa using h

end RBM.Gauss
