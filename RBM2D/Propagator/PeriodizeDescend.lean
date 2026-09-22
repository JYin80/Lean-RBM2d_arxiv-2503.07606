/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeShift
import RBM2D.Defs.Block

/-!
# Descending periodization to the two-dimensional torus

The periodized sum is invariant under changing either integer coordinate by a
multiple of `L`. This gives a well-defined function on `ZMod L × ZMod L`.
The argument ports the representative-change step of the one-dimensional
periodization proof; it does not assert convergence for the paper's `Kinf`.
-/

namespace RBM

/-- The canonical integer representative of a point on the discrete torus. -/
def torusLatticeLift {L : ℕ} (u : Z2 L) : ℤ × ℤ :=
  ((u.1.val : ℤ), (u.2.val : ℤ))

/-- A generic periodized complex kernel, now evaluated on `Z_L²`. -/
noncomputable def periodizedTorusKernel (L : ℕ) [NeZero L]
    (K : ℤ × ℤ → ℂ) (u : Z2 L) : ℂ :=
  periodizeKernel L K (torusLatticeLift u)

/-- The torus value can be computed from any integer representative. -/
theorem periodizedTorusKernel_eq_of_cast (L : ℕ) [NeZero L]
    (K : ℤ × ℤ → ℂ) (u : Z2 L) (v : ℤ × ℤ)
    (hv : ((v.1 : ZMod L), (v.2 : ZMod L)) = u) :
    periodizedTorusKernel L K u = periodizeKernel L K v := by
  have h₁ : (v.1 : ZMod L) = u.1 := congrArg Prod.fst hv
  have h₂ : (v.2 : ZMod L) = u.2 := congrArg Prod.snd hv
  have e₁ : (((u.1.val : ℤ) : ZMod L)) = (v.1 : ZMod L) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h₁.symm
  have e₂ : (((u.2.val : ℤ) : ZMod L)) = (v.2 : ZMod L) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h₂.symm
  obtain ⟨k₁, hk₁⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp e₁
  obtain ⟨k₂, hk₂⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp e₂
  have hrep : v = torusLatticeLift u + L • (k₁, k₂) := by
    apply Prod.ext
    · simp only [torusLatticeLift, Prod.fst_add, Prod.smul_mk, nsmul_eq_mul]
      omega
    · simp only [torusLatticeLift, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul]
      omega
  rw [periodizedTorusKernel, hrep, periodizeKernel_add_smul]

/-- A point mass gives a nonzero function after descent. -/
example : periodizedTorusKernel 1
    (fun p : ℤ × ℤ => if p = (0, 0) then 1 else 0) (0, 0) = 1 := by
  simp [periodizedTorusKernel, torusLatticeLift, periodizeKernel, tsum_ite_eq]

end RBM
