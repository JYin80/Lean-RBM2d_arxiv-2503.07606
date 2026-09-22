/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Momentum
import RBM2D.Propagator.Shells
import RBM2D.Propagator.Harmonic

/-!
# The punctured-torus lattice sum

The nonzero Fourier modes in Section 8.2 are grouped by the `max`-shells
of `Propagator.Shells`. The shell count `12 k + 4 ≤ 16 k` gives the explicit
constant `4 / π²` in the two-dimensional harmonic bound.
-/

namespace RBM

variable (L : ℕ) [NeZero L]

omit [NeZero L] in
/-- The square of the shell radius is bounded by the momentum square. -/
theorem shell_radius_sq_le_pstar2 (p : Z2 L) :
    (2 * Real.pi * (shellIndex L p : ℝ) / (L : ℝ)) ^ 2 ≤ pstar2 L p := by
  rcases le_total (zdist L p.1) (zdist L p.2) with h | h
  · simp only [shellIndex, max_eq_right h, pstar2, pstar]
    nlinarith [sq_nonneg (2 * Real.pi * (zdist L p.1 : ℝ) / (L : ℝ))]
  · simp only [shellIndex, max_eq_left h, pstar2, pstar]
    nlinarith [sq_nonneg (2 * Real.pi * (zdist L p.2 : ℝ) / (L : ℝ))]

/-- Pointwise inverse-square bound on a nonzero shell. -/
theorem inv_pstar2_le_shell (p : Z2 L) (k : ℕ) (hk : 1 ≤ k)
    (hp : shellIndex L p = k) :
    (pstar2 L p)⁻¹ ≤ (L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hrad : 0 < 2 * Real.pi * (k : ℝ) / (L : ℝ) := by positivity
  have hbound := shell_radius_sq_le_pstar2 L p
  rw [hp] at hbound
  have hinv := inv_anti₀ (pow_pos hrad 2) hbound
  calc
    (pstar2 L p)⁻¹ ≤ ((2 * Real.pi * (k : ℝ) / (L : ℝ)) ^ 2)⁻¹ := hinv
    _ = (L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
      field_simp
      ring

/-- A single shell contributes at most `4 L² / (π² k)`. -/
theorem sum_shell_inv_pstar2_le (k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ Finset.univ.filter (fun p : Z2 L => shellIndex L p = k),
        (pstar2 L p)⁻¹
      ≤ (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 * (k : ℝ)⁻¹ := by
  classical
  let s : Finset (Z2 L) := Finset.univ.filter (fun p => shellIndex L p = k)
  have hpoint : ∀ p ∈ s,
      (pstar2 L p)⁻¹ ≤ (L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
    intro p hp
    exact inv_pstar2_le_shell L p k hk (Finset.mem_filter.mp hp).2
  have hcard : (s.card : ℝ) ≤ 16 * (k : ℝ) := by
    have hc := card_shell_le L k
    have hk' : 1 ≤ k := hk
    have hnat : s.card ≤ 16 * k := by
      dsimp [s]
      omega
    exact_mod_cast hnat
  have hden : 0 ≤ (L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by positivity
  calc
    ∑ p ∈ s, (pstar2 L p)⁻¹
        ≤ ∑ _p ∈ s, (L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) :=
          Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) * ((L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) := by simp
    _ ≤ (16 * (k : ℝ)) * ((L : ℝ) ^ 2 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcard hden
    _ = (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 * (k : ℝ)⁻¹ := by
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
          have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          field_simp
          ring

/-- The explicit punctured-torus estimate used by T4 and T5. -/
theorem sum_inv_pstar2_le (_hL : 3 ≤ L) :
    ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹
      ≤ (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by
  rw [sum_erase_zero_eq_sum_shells L]
  calc
    ∑ k ∈ Finset.Icc 1 L,
        ∑ p ∈ Finset.univ.filter (fun p : Z2 L => shellIndex L p = k),
          (pstar2 L p)⁻¹
      ≤ ∑ k ∈ Finset.Icc 1 L,
          (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 * (k : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro k hk
            exact sum_shell_inv_pstar2_le L k (Finset.mem_Icc.mp hk).1
    _ = (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 *
          ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by rw [← Finset.mul_sum]

/-- After the Fourier normalization by `L²`, only a harmonic factor remains. -/
theorem normalized_sum_inv_pstar2_le (hL : 3 ≤ L) :
    (∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) / (L : ℝ) ^ 2
      ≤ (4 / Real.pi ^ 2) * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := by
  have hLpos : (0 : ℝ) < L := cast_L_pos L
  apply (div_le_iff₀ (pow_pos hLpos 2)).2
  calc
    ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹
        ≤ (4 / Real.pi ^ 2) * (L : ℝ) ^ 2 *
            ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ := sum_inv_pstar2_le L hL
    _ = ((4 / Real.pi ^ 2) * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) *
          (L : ℝ) ^ 2 := by ring

/-- The explicit logarithmic bound corresponding to the paper's `C log L`. -/
theorem normalized_sum_inv_pstar2_le_log (hL : 3 ≤ L) :
    (∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) / (L : ℝ) ^ 2
      ≤ (4 / Real.pi ^ 2) * (1 + Real.log L) := by
  calc
    _ ≤ (4 / Real.pi ^ 2) * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ :=
      normalized_sum_inv_pstar2_le L hL
    _ ≤ (4 / Real.pi ^ 2) * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log L) (by positivity)

end RBM

namespace RBM

/-- The normalized punctured sum, extended by zero at the two irrelevant small
sizes so that it is an ordinary sequence on `ℕ`. -/
noncomputable def normalizedPuncturedSum (L : ℕ) : ℝ :=
  if hL : 3 ≤ L then
    letI : NeZero L := ⟨by omega⟩
    (∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) / (L : ℝ) ^ 2
  else 0

theorem normalizedPuncturedSum_eq (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    normalizedPuncturedSum L =
      (∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) / (L : ℝ) ^ 2 := by
  simp [normalizedPuncturedSum, hL]

/-- The Fourier-normalized lattice sum is `≺ 1`, as required in both the
small-`κL` estimate of Section 8.2 and Case 2 of Section 8.3. -/
theorem normalizedPuncturedSum_detDom_one :
    normalizedPuncturedSum ≺ (fun _ => (1 : ℝ)) := by
  open Filter in
  rw [detDom_iff]
  intro τ hτ
  have hconstant : (4 / Real.pi ^ 2 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ 2)).2
    nlinarith [Real.pi_gt_three]
  filter_upwards [detDom_iff.mp harmonic_detDom_one τ hτ,
    Filter.eventually_ge_atTop 3] with L hH hL
  have : NeZero L := ⟨by omega⟩
  rw [normalizedPuncturedSum_eq L hL]
  calc
    (∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹) / (L : ℝ) ^ 2
        ≤ (4 / Real.pi ^ 2) * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ :=
          normalized_sum_inv_pstar2_le L hL
    _ ≤ (4 / Real.pi ^ 2) * ((L : ℝ) ^ τ * 1) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ (L : ℝ) ^ τ * 1 := by
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg L) τ]

/-- A concrete finite torus has a genuinely nonempty positive punctured sum. -/
example : 0 < ∑ p ∈ Finset.univ.erase (0 : Z2 3), (pstar2 3 p)⁻¹ := by
  apply Finset.sum_pos'
  · intro p hp
    exact (inv_pos.mpr (pstar2_pos_of_ne_zero 3 (Finset.mem_erase.mp hp).1)).le
  · refine ⟨(1, 0), ?_, ?_⟩
    · simp
    · exact inv_pos.mpr (pstar2_pos_of_ne_zero 3 (by decide))

end RBM
