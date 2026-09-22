/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolLowShell

/-!
# Second-coordinate low-shell bound

The five-point symbol and squared momentum are invariant under swapping
coordinates, so the first-coordinate low-shell estimate transfers exactly.
-/

namespace RBM

private def swapZ2 (L : ℕ) (p : Z2 L) : Z2 L := (p.2, p.1)

private theorem Shat_swapZ2 (L : ℕ) [NeZero L] (p : Z2 L) :
    Shat L (swapZ2 L p) = Shat L p := by
  unfold Shat swapZ2
  ring

private theorem pstar2_swapZ2 (L : ℕ) [NeZero L] (p : Z2 L) :
    pstar2 L (swapZ2 L p) = pstar2 L p := by
  unfold pstar2 swapZ2
  ring

private theorem invSymbolMultiplier_swapZ2 (L : ℕ) [NeZero L]
    (ξ : ℂ) (p : Z2 L) :
    invSymbolMultiplier L ξ (swapZ2 L p) = invSymbolMultiplier L ξ p := by
  simp only [invSymbolMultiplier, Shat_swapZ2]

/-- The second-coordinate low-shell estimate has the same constants as the
first-coordinate result, including at a shifted zero momentum. -/
theorem norm_invSymbolMultiplier_second_diff_e2_low_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (p q r : Z2 L) (hq : q = p + (0, 1)) (hr : r = q + (0, 1))
    (hlow : pstar2 L p ≤ 16 * (symbolGridStep L) ^ 2) :
    ‖invSymbolMultiplier L ξ r - 2 * invSymbolMultiplier L ξ q +
        invSymbolMultiplier L ξ p‖ ≤
      ‖ξ‖ * ((2 / 5 : ℝ) * (symbolGridStep L) ^ 2) /
          (symbolLowDenomScale ξ) ^ 2 +
        ‖ξ‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep L) ^ 4) /
          (symbolLowDenomScale ξ) ^ 3 := by
  have hq' : swapZ2 L q = swapZ2 L p + (1, 0) := by
    rw [hq]
    ext <;> simp [swapZ2]
  have hr' : swapZ2 L r = swapZ2 L q + (1, 0) := by
    rw [hr]
    ext <;> simp [swapZ2]
  have hlow' : pstar2 L (swapZ2 L p) ≤ 16 * (symbolGridStep L) ^ 2 := by
    simpa only [pstar2_swapZ2] using hlow
  have h := norm_invSymbolMultiplier_second_diff_e1_low_le L hL hξ
    (swapZ2 L p) (swapZ2 L q) (swapZ2 L r) hq' hr' hlow'
  simpa only [invSymbolMultiplier_swapZ2] using h

/-- A concrete nonzero resolvent parameter at zero momentum. -/
example :
    let p : Z2 3 := (0, 0)
    let q := p + (0, 1)
    let r := q + (0, 1)
    ‖invSymbolMultiplier 3 (1 / 2) r -
        2 * invSymbolMultiplier 3 (1 / 2) q +
        invSymbolMultiplier 3 (1 / 2) p‖ ≤
      ‖(1 / 2 : ℂ)‖ * ((2 / 5 : ℝ) * (symbolGridStep 3) ^ 2) /
          (symbolLowDenomScale (1 / 2)) ^ 2 +
        ‖(1 / 2 : ℂ)‖ ^ 2 * ((36 / 5 : ℝ) * (symbolGridStep 3) ^ 4) /
          (symbolLowDenomScale (1 / 2)) ^ 3 := by
  apply norm_invSymbolMultiplier_second_diff_e2_low_le 3 (by norm_num)
    (by norm_num) (0, 0) ((0, 0) + (0, 1))
    ((0, 0) + (0, 1) + (0, 1)) rfl rfl
  simp only [pstar2, pstar, zdist_zero, Nat.cast_zero, mul_zero, zero_div]
  nlinarith [sq_nonneg (symbolGridStep 3)]

end RBM
