/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic scales and their geometric sums

Work order T17, first half.  Section 8.3 sums over dyadic scales
`r ∈ {2^{-j}}` with `L^{-1} ≲ r ≲ 1`, and the two estimates
`(eq_dyadic_sum1)`, `(eq_dyadic_sum2)` of the paper are what turn those sums
into `1/(d+1)` and `1/(d+1)^2`.  T11 is the hard part of Section 8.3 (the
per-shell estimate `(eq_dyadic)`, which needs discrete summation by parts);
these geometric sums are not hard, and the point of splitting them off is that
**they survive even if T11 stalls or is downgraded to an interface axiom**.

This file is the arithmetic floor of T17 and nothing else: the dyadic scale
itself and the one summation bound every later step reduces to.  It imports
Mathlib only — no lattice, no Fourier, no propagator — so it can be checked in
isolation and cannot break anything else.

## The one bound everything reduces to

`∑_{j < n} (2^{-j})^k ≤ 2` for every `k ≥ 1`, uniformly in `n`.

The proof deliberately does not go through `geom_sum_eq` and a closed form.
Since `dyad j ≤ 1`, raising to a power `k ≥ 1` only decreases it
(`pow_le_of_le_one`), so the sum is dominated termwise by `∑ (1/2)^j`, which is
Mathlib's `sum_geometric_two_le`.  That keeps the whole file free of division
and of any hypothesis relating `k` and `n`.

## Not in this file

The two headline estimates `dyadic_sum_three_le` and `dyadic_sum_four_le`, which
split the range at `r ≤ κ` and at `r ≤ 1/(d+1)`.  They need `RBM.kappa` and
`RBM.ellhat` from `Propagator/Elliptic.lean` and are the second half of T17.
-/

namespace RBM

open Finset

/-- The dyadic scale `r = 2^{-j}` of Section 8.3.  Written as a natural power of
`2⁻¹` rather than as `(2 : ℝ) ^ (-(j : ℤ))` so that everything downstream is
`Monoid.npow` and no `zpow`/`rpow` juggling is needed; `dyad_eq_zpow` records
that the two agree. -/
noncomputable def dyad (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ j

theorem dyad_eq_zpow (j : ℕ) : dyad j = (2 : ℝ) ^ (-(j : ℤ)) := by
  rw [dyad, zpow_neg, zpow_natCast, inv_pow]

@[simp] theorem dyad_zero : dyad 0 = 1 := by
  simp [dyad]

theorem dyad_pos (j : ℕ) : 0 < dyad j :=
  pow_pos (by norm_num) j

theorem dyad_nonneg (j : ℕ) : 0 ≤ dyad j :=
  (dyad_pos j).le

theorem dyad_le_one (j : ℕ) : dyad j ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem dyad_antitone : Antitone dyad := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

/-- A power `k ≥ 1` of a dyadic scale is again at most that scale.  This is the
step that removes `k` from the summation bound below. -/
theorem dyad_pow_le (j : ℕ) {k : ℕ} (hk : 1 ≤ k) : (dyad j) ^ k ≤ dyad j :=
  pow_le_of_le_one (dyad_nonneg j) (dyad_le_one j) (by omega)

/-- `∑_{j < n} 2^{-j} ≤ 2`, uniformly in `n`. -/
theorem sum_dyad_le (n : ℕ) : ∑ j ∈ Finset.range n, dyad j ≤ 2 := by
  have h : ∀ j : ℕ, dyad j = (1 / (2 : ℝ)) ^ j := by
    intro j; rw [dyad, one_div]
  calc ∑ j ∈ Finset.range n, dyad j
      = ∑ j ∈ Finset.range n, (1 / (2 : ℝ)) ^ j := by
        exact Finset.sum_congr rfl fun j _ => h j
    _ ≤ 2 := sum_geometric_two_le n

/-- **The summation bound T17 reduces to.**  Uniform in both the number of
scales and the power, for every power `k ≥ 1`. -/
theorem sum_dyad_pow_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∑ j ∈ Finset.range n, (dyad j) ^ k ≤ 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ => dyad_pow_le j hk) ?_
  exact sum_dyad_le n

/-- The pointwise form of `dyad_antitone`, stated so that call sites do not have
to unfold `Antitone`. -/
theorem dyad_le_dyad_of_le {i j : ℕ} (h : i ≤ j) : dyad j ≤ dyad i :=
  dyad_antitone h

/-- The reciprocal of a dyadic scale is a dyadic scale of `2`.  The second half
of T17 splits the range at `r > 1/(d+1)`, where the filter condition gives
`(dyad j)⁻¹ < d + 1`; on that block the summand carries `(dyad j)⁻¹` rather than
`dyad j`, so the sum is *increasing* and is controlled by its largest term.  This
lemma is what lets that block be handled in the same `2 ^ j` language as the
rest. -/
theorem inv_dyad (j : ℕ) : (dyad j)⁻¹ = (2 : ℝ) ^ j := by
  rw [dyad, inv_pow, inv_inv]

theorem one_le_inv_dyad (j : ℕ) : 1 ≤ (dyad j)⁻¹ := by
  rw [inv_dyad]
  exact one_le_pow₀ (by norm_num)

end RBM
