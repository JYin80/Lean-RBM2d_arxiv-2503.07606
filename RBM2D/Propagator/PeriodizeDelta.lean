/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.PeriodizeStencil

/-!
# Periodization of the lattice point mass

On the discrete torus, periodizing the point mass at the origin gives the
Kronecker delta at the origin. This is the right-hand-side calculation needed
after periodizing the infinite-volume lattice resolvent equation.
-/

namespace RBM

/-- A canonical representative plus a lattice period vanishes exactly at the
origin with zero shift. -/
theorem torusLatticeLift_add_smul_eq_zero_iff (L : ℕ) [NeZero L]
    (u : Z2 L) (n : ℤ × ℤ) :
    torusLatticeLift u + L • n = 0 ↔ n = 0 ∧ u = 0 := by
  constructor
  · intro h
    have h₁ : (u.1.val : ℤ) + (L : ℤ) * n.1 = 0 := by
      have hc := congrArg Prod.fst h
      simpa only [torusLatticeLift, Prod.fst_add, nsmul_eq_mul,
        Prod.fst_mul, Prod.fst_natCast, Prod.fst_zero] using hc
    have h₂ : (u.2.val : ℤ) + (L : ℤ) * n.2 = 0 := by
      have hc := congrArg Prod.snd h
      simpa only [torusLatticeLift, Prod.snd_add, nsmul_eq_mul,
        Prod.snd_mul, Prod.snd_natCast, Prod.snd_zero] using hc
    have hu₁ : u.1.val = 0 := by
      have hdiv : (L : ℤ) ∣ (u.1.val : ℤ) := by
        refine ⟨-n.1, ?_⟩
        linear_combination h₁
      exact_mod_cast Int.eq_zero_of_dvd_of_nonneg_of_lt
        (by exact_mod_cast Nat.zero_le u.1.val)
        (by exact_mod_cast ZMod.val_lt u.1) hdiv
    have hu₂ : u.2.val = 0 := by
      have hdiv : (L : ℤ) ∣ (u.2.val : ℤ) := by
        refine ⟨-n.2, ?_⟩
        linear_combination h₂
      exact_mod_cast Int.eq_zero_of_dvd_of_nonneg_of_lt
        (by exact_mod_cast Nat.zero_le u.2.val)
        (by exact_mod_cast ZMod.val_lt u.2) hdiv
    have hu : u = 0 := by
      apply Prod.ext
      · exact (ZMod.val_eq_zero u.1).mp hu₁
      · exact (ZMod.val_eq_zero u.2).mp hu₂
    have hn : n = 0 := by
      apply Prod.ext
      · have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
        have hmul : (L : ℤ) * n.1 = 0 := by simpa [hu] using h₁
        exact (mul_eq_zero.mp hmul).resolve_left hL
      · have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
        have hmul : (L : ℤ) * n.2 = 0 := by simpa [hu] using h₂
        exact (mul_eq_zero.mp hmul).resolve_left hL
    exact ⟨hn, hu⟩
  · rintro ⟨rfl, rfl⟩
    simp [torusLatticeLift]

/-- The point mass on `ℤ²` periodizes to the Kronecker delta on `Z_L²`. -/
theorem periodizedTorusKernel_latticePointMass (L : ℕ) [NeZero L]
    (u : Z2 L) :
    periodizedTorusKernel L latticePointMass u =
      if u = 0 then 1 else 0 := by
  simp only [periodizedTorusKernel, periodizeKernel, latticePointMass]
  simp_rw [torusLatticeLift_add_smul_eq_zero_iff L u]
  split_ifs with hu
  · subst hu
    simp only [and_true]
    exact tsum_ite_eq (0 : ℤ × ℤ) (fun _ => (1 : ℂ))
  · simp [hu]

/-- Nonzero value at the origin on a genuine three-by-three torus. -/
example : periodizedTorusKernel 3 latticePointMass ((0, 0) : Z2 3) = 1 := by
  simpa using periodizedTorusKernel_latticePointMass 3 ((0, 0) : Z2 3)

/-- The same kernel vanishes away from the origin. -/
example : periodizedTorusKernel 3 latticePointMass ((1, 0) : Z2 3) = 0 := by
  simpa using periodizedTorusKernel_latticePointMass 3 ((1, 0) : Z2 3)

end RBM
