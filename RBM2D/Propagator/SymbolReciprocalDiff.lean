/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolDiff

/-!
# First difference of the reciprocal Fourier multiplier

The reciprocal denominator inherits a first-difference bound from `Shat`.
Annular comparison of the two denominator norms is a separate scale estimate.
-/

namespace RBM

/-- The multiplier appearing in the Fourier representation of `Theta`. -/
noncomputable def invSymbolMultiplier (L : ℕ) [NeZero L]
    (ξ : ℂ) (p : Z2 L) : ℂ := (1 - ξ * Shat L p)⁻¹

end RBM
