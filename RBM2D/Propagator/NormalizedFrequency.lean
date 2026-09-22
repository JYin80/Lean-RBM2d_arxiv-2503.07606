/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.SymbolCutoffShell

/-!
# Normalized Fourier frequency for dyadic cutoffs

The two coordinate distances are each at most `π`; division of the Euclidean
radius by `2π` therefore maps every lattice momentum into `[0,1]`. The
normalization factor is kept explicit in support statements.
-/

namespace RBM

/-- A normalized momentum radius in `[0,1]`. -/
noncomputable def normalizedFrequency (L : ℕ) [NeZero L] (p : Z2 L) : ℝ :=
  Real.sqrt (pstar2 L p) / (2 * Real.pi)

theorem normalizedFrequency_nonneg (L : ℕ) [NeZero L] (p : Z2 L) :
    0 ≤ normalizedFrequency L p := by
  unfold normalizedFrequency
  positivity

theorem normalizedFrequency_le_one (L : ℕ) [NeZero L] (p : Z2 L) :
    normalizedFrequency L p ≤ 1 := by
  have h₁ : (pstar L p.1) ^ 2 ≤ Real.pi ^ 2 :=
    (sq_le_sq₀ (pstar_nonneg L p.1) Real.pi_pos.le).2 (pstar_le_pi L p.1)
  have h₂ : (pstar L p.2) ^ 2 ≤ Real.pi ^ 2 :=
    (sq_le_sq₀ (pstar_nonneg L p.2) Real.pi_pos.le).2 (pstar_le_pi L p.2)
  have hP : pstar2 L p ≤ (2 * Real.pi) ^ 2 := by
    dsimp [pstar2]
    nlinarith [sq_nonneg Real.pi]
  have hsqrt : Real.sqrt (pstar2 L p) ≤ 2 * Real.pi := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    simpa only [Real.sq_sqrt (pstar2_nonneg L p)] using hP
  unfold normalizedFrequency
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  simpa using hsqrt

/-- The existing real cutoff evaluated at normalized lattice frequency. -/
noncomputable def normalizedDyadicCutoff (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L) : ℝ :=
  dyadicCutoff j (normalizedFrequency L p)

/-- Exact physical-radius support of the normalized dyadic cutoff. -/
theorem normalizedDyadicCutoff_support (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    (2 * Real.pi) * dyad (j + 1) ≤ Real.sqrt (pstar2 L p) ∧
      Real.sqrt (pstar2 L p) ≤ (2 * Real.pi) * (2 * dyad j) := by
  have ⟨hinner, houter⟩ :=
    dyadicCutoff_support j (normalizedFrequency L p) hcut
  have hM : 0 ≤ 2 * Real.pi := by positivity
  have hscale : (2 * Real.pi) * normalizedFrequency L p =
      Real.sqrt (pstar2 L p) := by
    unfold normalizedFrequency
    field_simp [Real.pi_ne_zero]
  constructor
  · calc
      (2 * Real.pi) * dyad (j + 1) ≤
          (2 * Real.pi) * normalizedFrequency L p :=
            mul_le_mul_of_nonneg_left hinner hM
      _ = _ := hscale
  · calc
      Real.sqrt (pstar2 L p) =
          (2 * Real.pi) * normalizedFrequency L p := hscale.symm
      _ ≤ (2 * Real.pi) * (2 * dyad j) :=
        mul_le_mul_of_nonneg_left houter hM

/-- Squared-radius version, ready for comparison with momentum annuli. -/
theorem normalizedDyadicCutoff_support_sq (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    ((2 * Real.pi) * dyad (j + 1)) ^ 2 ≤ pstar2 L p ∧
      pstar2 L p ≤ ((2 * Real.pi) * (2 * dyad j)) ^ 2 := by
  obtain ⟨hinner, houter⟩ := normalizedDyadicCutoff_support L j p hcut
  have hP := pstar2_nonneg L p
  constructor
  · have h := (sq_le_sq₀ (by have := dyad_nonneg (j + 1); positivity :
        0 ≤ (2 * Real.pi) * dyad (j + 1))
        (Real.sqrt_nonneg _)).2 hinner
    simpa only [Real.sq_sqrt hP] using h
  · have h := (sq_le_sq₀ (Real.sqrt_nonneg _)
        (by have := dyad_nonneg j; positivity :
          0 ≤ (2 * Real.pi) * (2 * dyad j))).2 houter
    simpa only [Real.sq_sqrt hP] using h

/-- A concrete nonzero normalized cutoff at nonzero lattice momentum. -/
example : normalizedDyadicCutoff 6 2 ((1, 0) : Z2 6) ≠ 0 := by
  have hz : zdist 6 (1 : ZMod 6) = 1 := by decide
  have hrad : pstar2 6 ((1, 0) : Z2 6) = (Real.pi / 3) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 6 ((1, 0) : Z2 6) = 1 / 6 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi / 3)]
    field_simp [Real.pi_ne_zero]
    ring
  rw [normalizedDyadicCutoff, hν]
  norm_num [dyadicCutoff, dyad, lowPass, smoothstep3]

end RBM
