/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeConvergence

/-!
# Translation invariance of a periodized lattice kernel

This is the elementary reindexing step of the periodization argument. It applies to any complex
kernel. Summability of the paper's infinite-volume kernel is proved in
`Propagator/PeriodizeKinfSummable.lean`.
-/

namespace RBM

/-- Periodization of an arbitrary complex lattice kernel with lattice spacing `L`. -/
noncomputable def periodizeKernel (L : ℕ) (K : ℤ × ℤ → ℂ) (x : ℤ × ℤ) : ℂ :=
  ∑' n : ℤ × ℤ, K (x + L • n)

/-- Adding an `Lℤ²` shift does not change the periodized sum. -/
theorem periodizeKernel_add_smul (L : ℕ) (K : ℤ × ℤ → ℂ)
    (x k : ℤ × ℤ) :
    periodizeKernel L K (x + L • k) = periodizeKernel L K x := by
  unfold periodizeKernel
  rw [← (Equiv.addRight k).tsum_eq (fun n : ℤ × ℤ => K (x + L • n))]
  congr 1
  funext n
  simp only [Equiv.coe_addRight]
  congr 1
  rw [smul_add]
  abel

end RBM
