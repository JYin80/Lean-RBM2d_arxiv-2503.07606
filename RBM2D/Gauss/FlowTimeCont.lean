/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Model

/-!
# Samplewise time continuity of the Gaussian matrix flow

The coupling `Hflow u ω = √u • Xmat ω` is continuous in time for each fixed sample,
including at `u = 0`. This is a statement about the matrix flow itself; continuity of
resolvent loops composed with the flow requires further model work.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- For each fixed Gaussian sample, the entire matrix flow is continuous in time. -/
theorem continuous_Hflow_time (ω : Ω L W) :
    Continuous fun u : ℝ => Hflow L W u ω := by
  change Continuous fun u : ℝ => (Real.sqrt u : ℂ) • Xmat L W ω
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

/-- Every matrix entry is continuous along the fixed-sample flow. -/
theorem continuous_Hflow_entry_time (ω : Ω L W) (i j : Idx L W) :
    Continuous fun u : ℝ => Hflow L W u ω i j := by
  simp only [Hflow_apply]
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).mul continuous_const

/-- A concrete nonzero lattice index in the `L = 3`, `W = 1` model. -/
theorem continuous_Hflow_nonzero_index_example (ω : Ω 3 1) :
    ((1, 0) : Idx 3 1) ≠ 0 ∧
      Continuous (fun u : ℝ => Hflow 3 1 u ω ((1, 0) : Idx 3 1) (1, 0)) := by
  constructor
  · decide
  · exact continuous_Hflow_entry_time 3 1 ω _ _

namespace Sizes

variable (d : Sizes)

/-- The common-probability-space flow is continuous in time at each fixed size and sample. -/
theorem continuous_seqHflow_time (n : ℕ) (ω : SeqΩ d) :
    Continuous fun u : ℝ => seqHflow d n u ω := by
  change Continuous fun u : ℝ => Hflow (d.L n) (d.W n) u (slice d n ω)
  exact continuous_Hflow_time _ _ _

/-- Entrywise time continuity on the common probability space. -/
theorem continuous_seqHflow_entry_time (n : ℕ) (ω : SeqΩ d)
    (i j : Idx (d.L n) (d.W n)) :
    Continuous fun u : ℝ => seqHflow d n u ω i j := by
  change Continuous fun u : ℝ => Hflow (d.L n) (d.W n) u (slice d n ω) i j
  exact continuous_Hflow_entry_time _ _ _ i j

end Sizes

end RBM.Gauss
