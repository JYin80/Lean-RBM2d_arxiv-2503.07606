/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffShellRadius

/-!
# Low-grid normalized cutoff support

In the branch below two grid steps, a nonzero cutoff is confined to a
constant-radius neighborhood of the origin in the cyclic distance. The
antipodal fold has not been discarded; no global quadratic difference bound
is asserted here.
-/

namespace RBM

private theorem pstar_coord_le_sqrt_pstar2 (L : ℕ) [NeZero L]
    (p : Z2 L) (i : Fin 2) :
    pstar L (if i = 0 then p.1 else p.2) ≤ Real.sqrt (pstar2 L p) := by
  have hsq : (pstar L (if i = 0 then p.1 else p.2)) ^ 2 ≤
      pstar2 L p := by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte, pstar2]
      nlinarith [sq_nonneg (pstar L p.2)]
    · simp only [hi, ↓reduceIte, pstar2]
      nlinarith [sq_nonneg (pstar L p.1)]
  apply (sq_le_sq₀ (pstar_nonneg L _) (Real.sqrt_nonneg _)).mp
  simpa only [Real.sq_sqrt (pstar2_nonneg L p)] using hsq

/-- Each cyclic coordinate, measured in units of the side length, is at
most the normalized Euclidean frequency. -/
theorem zdist_coord_div_le_normalizedFrequency (L : ℕ) [NeZero L]
    (p : Z2 L) (i : Fin 2) :
    (zdist L (if i = 0 then p.1 else p.2) : ℝ) / (L : ℝ) ≤
      normalizedFrequency L p := by
  have hpi : 0 < 2 * Real.pi := by positivity
  calc
    (zdist L (if i = 0 then p.1 else p.2) : ℝ) / (L : ℝ) =
        pstar L (if i = 0 then p.1 else p.2) / (2 * Real.pi) := by
          unfold pstar
          field_simp [Real.pi_ne_zero, ne_of_gt (cast_L_pos L)]
    _ ≤ Real.sqrt (pstar2 L p) / (2 * Real.pi) :=
      (div_le_div_iff_of_pos_right hpi).2
        (pstar_coord_le_sqrt_pstar2 L p i)
    _ = normalizedFrequency L p := rfl

/-- Every nonzero lattice frequency has normalized radius at least one
grid step. -/
theorem normalizedFrequency_ge_inv_of_ne_zero (L : ℕ) [NeZero L]
    (p : Z2 L) (hp : p ≠ 0) :
    1 / (L : ℝ) ≤ normalizedFrequency L p := by
  rcases p with ⟨u, v⟩
  have hcoord : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    have hu : u = 0 := by
      by_contra hu
      exact h (Or.inl hu)
    have hv : v = 0 := by
      by_contra hv
      exact h (Or.inr hv)
    exact hp (by simp [hu, hv])
  rcases hcoord with hu | hv
  · have hz : 1 ≤ zdist L u := by
      have hnz : zdist L u ≠ 0 := by
        intro hzero
        exact hu (zdist_eq_zero_iff L |>.mp hzero)
      omega
    have hzR : (1 : ℝ) ≤ (zdist L u : ℝ) := by exact_mod_cast hz
    have hdiv := (div_le_div_iff_of_pos_right (cast_L_pos L)).2 hzR
    exact hdiv.trans (zdist_coord_div_le_normalizedFrequency L (u, v) 0)
  · have hz : 1 ≤ zdist L v := by
      have hnz : zdist L v ≠ 0 := by
        intro hzero
        exact hv (zdist_eq_zero_iff L |>.mp hzero)
      omega
    have hzR : (1 : ℝ) ≤ (zdist L v : ℝ) := by exact_mod_cast hz
    have hdiv := (div_le_div_iff_of_pos_right (cast_L_pos L)).2 hzR
    exact hdiv.trans (zdist_coord_div_le_normalizedFrequency L (u, v) 1)

/-- A nonzero dyadic cutoff in the low-grid branch is supported in a
fixed cyclic box of coordinate radius strictly less than eight. -/
theorem normalizedDyadicCutoff_low_grid_zdist_lt_eight
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (hlow : dyad (j + 1) < 2 / (L : ℝ))
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    zdist L p.1 < 8 ∧ zdist L p.2 < 8 := by
  have houter : normalizedFrequency L p ≤ 2 * dyad j :=
    (dyadicCutoff_support j (normalizedFrequency L p) hcut).2
  have hdyad : dyad j = 2 * dyad (j + 1) := by
    simp [dyad, pow_succ]
    ring
  have hL : 0 < (L : ℝ) := cast_L_pos L
  have hlow' : dyad (j + 1) < 2 * (1 / (L : ℝ)) := by
    calc
      _ < 2 / (L : ℝ) := hlow
      _ = 2 * (1 / (L : ℝ)) := by ring
  have hscale : (L : ℝ) * (2 * dyad j) < 8 := by
    have h := mul_lt_mul_of_pos_left hlow' hL
    rw [hdyad]
    have hinv : (L : ℝ) * (1 / (L : ℝ)) = 1 := by field_simp
    nlinarith
  constructor
  · have hcoord := zdist_coord_div_le_normalizedFrequency L p 0
    have hmul := (div_le_iff₀ hL).mp (hcoord.trans houter)
    have hmul' : (zdist L p.1 : ℝ) ≤ 2 * dyad j * (L : ℝ) := by
      simpa using hmul
    have hreal : (zdist L p.1 : ℝ) < 8 := by nlinarith
    exact_mod_cast hreal
  · have hcoord := zdist_coord_div_le_normalizedFrequency L p 1
    have hmul := (div_le_iff₀ hL).mp (hcoord.trans houter)
    have hmul' : (zdist L p.2 : ℝ) ≤ 2 * dyad j * (L : ℝ) := by
      simpa using hmul
    have hreal : (zdist L p.2 : ℝ) < 8 := by nlinarith
    exact_mod_cast hreal

/-- A nonzero cutoff cannot live on a shell whose inner scale is more than
four times below the normalized grid step. -/
theorem normalizedDyadicCutoff_support_grid_lower_scale
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    1 / (L : ℝ) ≤ 4 * dyad (j + 1) := by
  have hinner : dyad (j + 1) ≤ normalizedFrequency L p :=
    (dyadicCutoff_support j (normalizedFrequency L p) hcut).1
  have houter : normalizedFrequency L p ≤ 2 * dyad j :=
    (dyadicCutoff_support j (normalizedFrequency L p) hcut).2
  have hp : p ≠ 0 := by
    intro hzero
    have hνzero : normalizedFrequency L (0 : Z2 L) = 0 := by
      simp [normalizedFrequency, pstar2, pstar, zdist_zero]
    rw [hzero, hνzero] at hinner
    have hd := dyad_pos (j + 1)
    linarith
  have hfreq := normalizedFrequency_ge_inv_of_ne_zero L p hp
  have hdyad : dyad j = 2 * dyad (j + 1) := by
    simp [dyad, pow_succ]
    ring
  rw [hdyad] at houter
  linarith

/-- The same lower scale applies whenever a three-point cutoff second
difference is nonzero. Thus the low-grid branch occupies only dyadic scales
within a fixed factor of the mesh. -/
theorem cutoff_second_diff_support_grid_lower_scale
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    1 / (L : ℝ) ≤ 4 * dyad (j + 1) := by
  by_contra hnot
  have hsmall : 4 * dyad (j + 1) < 1 / (L : ℝ) := lt_of_not_ge hnot
  have hzero (x : Z2 L) : normalizedDyadicCutoff L j x = 0 := by
    by_contra hx
    have hxscale := normalizedDyadicCutoff_support_grid_lower_scale L j x hx
    linarith
  simp [hzero p, hzero q, hzero r] at hsecond

/-- If the low-grid cutoff second difference is nonzero, one of its three
sampled frequencies lies in the same fixed cyclic box. -/
theorem cutoff_second_diff_low_grid_has_near_origin_support
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hlow : dyad (j + 1) < 2 / (L : ℝ))
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    (zdist L p.1 < 8 ∧ zdist L p.2 < 8) ∨
      (zdist L q.1 < 8 ∧ zdist L q.2 < 8) ∨
      (zdist L r.1 < 8 ∧ zdist L r.2 < 8) := by
  have hs : normalizedDyadicCutoff L j p ≠ 0 ∨
      normalizedDyadicCutoff L j q ≠ 0 ∨
      normalizedDyadicCutoff L j r ≠ 0 := by
    by_cases hp : normalizedDyadicCutoff L j p = 0
    · by_cases hq : normalizedDyadicCutoff L j q = 0
      · by_cases hr : normalizedDyadicCutoff L j r = 0
        · simp [hp, hq, hr] at hsecond
        · exact Or.inr (Or.inr hr)
      · exact Or.inr (Or.inl hq)
    · exact Or.inl hp
  rcases hs with hp | hq | hr
  · exact Or.inl (normalizedDyadicCutoff_low_grid_zdist_lt_eight L j p hlow hp)
  · exact Or.inr (Or.inl
      (normalizedDyadicCutoff_low_grid_zdist_lt_eight L j q hlow hq))
  · exact Or.inr (Or.inr
      (normalizedDyadicCutoff_low_grid_zdist_lt_eight L j r hlow hr))

/-- An active cutoff in the low-grid range at a nonzero momentum. -/
example : normalizedDyadicCutoff 16 3 ((2, 0) : Z2 16) ≠ 0 ∧
    dyad 4 < 2 / (16 : ℝ) := by
  constructor
  · have hz : zdist 16 (2 : ZMod 16) = 2 := by decide
    have hrad : pstar2 16 ((2, 0) : Z2 16) =
        (Real.pi / 4) ^ 2 := by
      simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_ofNat,
        Nat.cast_zero, mul_zero, zero_div]
      ring
    have hν : normalizedFrequency 16 ((2, 0) : Z2 16) = 1 / 8 := by
      rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
        abs_of_pos (by positivity : 0 < Real.pi / 4)]
      field_simp [Real.pi_ne_zero]
      ring
    rw [normalizedDyadicCutoff, hν]
    norm_num [dyadicCutoff, dyad, lowPass, smoothstep3]
  · norm_num [dyad]

end RBM

#print axioms RBM.zdist_coord_div_le_normalizedFrequency
#print axioms RBM.normalizedFrequency_ge_inv_of_ne_zero
#print axioms RBM.normalizedDyadicCutoff_low_grid_zdist_lt_eight
#print axioms RBM.normalizedDyadicCutoff_support_grid_lower_scale
#print axioms RBM.cutoff_second_diff_support_grid_lower_scale
#print axioms RBM.cutoff_second_diff_low_grid_has_near_origin_support
