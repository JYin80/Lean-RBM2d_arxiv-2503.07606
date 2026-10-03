/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopGeneratorExpectation

/-!
# Time continuity of finite expected cut terms

Each cut integrand is a product of two finite resolvent loops. On a compact
time window inside `(0,1)` the spectral gap gives a constant envelope, so
dominated convergence applies to its Gaussian expectation.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Time continuity of any finite loop, including a loop index not separately
certified well formed. Its product uses the paired list `σ.zip a`. -/
theorem continuousOn_gloop_any_window {s t : ℝ} (hst : s ≤ t)
    (ω : Ω L W) {z : ℝ → ℂ} (hzcont : Continuous z)
    (hzim : ∀ u ∈ Set.Icc s t, (z u).im ≠ 0)
    (I : LoopIdx (Z2 L)) :
    ContinuousOn (fun u : ℝ => gloop L W (HflowBlock L W u ω) (z u) I)
      (Set.Icc s t) := by
  let clamp : ℝ → ℝ := fun u => max s (min t u)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ u, clamp u ∈ Set.Icc s t := by
    intro u
    exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩
  have hclamp_eq : ∀ u ∈ Set.Icc s t, clamp u = u := by
    intro u hu
    simp [clamp, min_eq_right hu.2, max_eq_right hu.1]
  have hglobal : Continuous (fun u : ℝ =>
      gloop L W (HflowBlock L W u ω) (z (clamp u)) I) :=
    (continuous_matrixTrace L W).comp
      (continuous_gloopProd_Hflow_time L W ω
        (hzcont.comp hclamp_cont)
        (fun u => hzim (clamp u) (hclamp_mem u)) I)
  exact hglobal.continuousOn.congr (fun u hu => by
    change gloop L W (HflowBlock L W u ω) (z u) I =
      gloop L W (HflowBlock L W u ω) (z (clamp u)) I
    rw [hclamp_eq u hu])

/-- A uniform deterministic bound for any finite loop on a spectral window. -/
theorem norm_gloop_any_window_le {s t η : ℝ} (hη : 0 < η)
    {z : ℝ → ℂ} (hzlow : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|)
    (I : LoopIdx (Z2 L)) {u : ℝ} (hu : u ∈ Set.Icc s t)
    (ω : Ω L W) :
    ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        (η⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ (I.σ.zip I.a).length := by
  have ht := norm_matrix_trace_le_card_mul
    (gloopProd L W (HflowBlock L W u ω) (z u) I)
  have hw := norm_foldr_Gsig_Eblk_le L W
    (HflowBlock_isHermitian L W u ω) hη (hzlow u hu) (I.σ.zip I.a)
  calc
    ‖gloop L W (HflowBlock L W u ω) (z u) I‖ ≤
        (Fintype.card (BlockIndex L W) : ℝ) *
          ‖gloopProd L W (HflowBlock L W u ω) (z u) I‖ := ht
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end RBM.Gauss
