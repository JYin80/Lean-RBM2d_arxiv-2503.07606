/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Scales
import RBM2D.Loop.Kcal

/-!
# Bridge between the K-loop scales and the `RBM.Path` scales

The K-loop layer (`RBM2D/Loop/Kcal.lean`) has its own `RBM.KLoop.etaT`,
`RBM.KLoop.ellT`, `RBM.KLoop.Mt`; the Step 2 path layer (`RBM2D/Path/Scales.lean`) has
`RBM.Path.etaT`, `RBM.Path.ellT`, `RBM.Path.scaleM`.  This file proves that they agree:

* `kloop_etaT_eq`: `KLoop.etaT E t = etaT E t` for all `E t : ℝ`;
* `kloop_ellT_eq`: `KLoop.ellT L t = ellT L t` for `t ≤ 1`;
* `kloop_Mt_eq`: `KLoop.Mt L W E t = scaleM L W E t` for `t ≤ 1`.

For `t > 1` the two `ellT` differ: `KLoop.ellT L t = min (√(t - 1))⁻¹ L` (since
`‖1 - t‖ = t - 1`), whereas `RBM.Path.ellT L t = 0` (`√(1 - t) = 0` in Lean for `t > 1`).  E.g.
`L = 3`, `t = 2` gives `1` versus `0`.  Hence the range `t ≤ 1` in `kloop_ellT_eq` and
`kloop_Mt_eq` is the largest true one.  At `t = 1` both sides of `kloop_ellT_eq` are `0`.

This is the only `RBM.Path` file that imports an `RBM2D.Loop.*` module.  `RBM.KLoop` is not opened;
the K-loop names are referred to by qualified name.
-/

namespace RBM.Path

private theorem scalesBridge_kappa_ofReal {t : ℝ} (ht : t ≤ 1) :
    kappa (t : ℂ) = Real.sqrt (1 - t) := by
  have h : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  unfold kappa
  rw [h, Complex.norm_of_nonneg (by linarith)]

/-- `KLoop.etaT = Path.etaT` (for all `E t`). -/
theorem kloop_etaT_eq {E t : ℝ} : KLoop.etaT E t = etaT E t := by
  unfold KLoop.etaT etaT
  exact Gauss.spectralZ_im E t

/-- `KLoop.ellT = Path.ellT` for `t ≤ 1` (false for `t > 1`, see the module docstring). -/
theorem kloop_ellT_eq {L : ℕ} [NeZero L] {t : ℝ} (ht : t ≤ 1) :
    KLoop.ellT L t = ellT L t := by
  unfold KLoop.ellT ellT ellhat
  rw [scalesBridge_kappa_ofReal ht, one_div]

/-- `KLoop.Mt = Path.scaleM` for `t ≤ 1`. -/
theorem kloop_Mt_eq {L W : ℕ} [NeZero L] {E t : ℝ} (ht : t ≤ 1) :
    KLoop.Mt L W E t = scaleM L W E t := by
  unfold KLoop.Mt scaleM
  rw [kloop_ellT_eq ht, kloop_etaT_eq]

end RBM.Path
