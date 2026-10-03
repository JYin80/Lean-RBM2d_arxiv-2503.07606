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
resolvent loops composed with the flow is shown in `Gauss/LoopTimeCont.lean`.
-/

namespace RBM.Gauss

open Matrix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- For each fixed Gaussian sample, the entire matrix flow is continuous in time. -/
theorem continuous_Hflow_time (ω : Ω L W) :
    Continuous fun u : ℝ => Hflow L W u ω := by
  change Continuous fun u : ℝ => (Real.sqrt u : ℂ) • Xmat L W ω
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

end RBM.Gauss
