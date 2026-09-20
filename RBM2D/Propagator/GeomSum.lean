/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecificLimits.Basic
import RBM2D.Propagator.Elliptic

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

/-! ### Geometric sums against their largest term

Both halves of T17 need the same shape twice, once decreasing and once
increasing: a sum over an *arbitrary* subset `s` of scales is at most twice its
largest term.  The two lemmas below are what let the later case analysis use the
filter condition (`dyad j ≤ κ`, or `(dyad j)⁻¹ ≤ d + 1`) directly, without ever
naming the index where the split happens. -/

/-- A decreasing geometric sum is at most twice its largest term: if every scale
occurring in `s` is at most `c`, then their sum is at most `2c`. -/
theorem sum_dyad_le_two_mul {s : Finset ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ s, dyad j ≤ c) : ∑ j ∈ s, dyad j ≤ 2 * c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using by linarith
  have hmem := s.min'_mem hne
  set m := s.min' hne with hm
  have hsplit : ∀ j ∈ s, dyad j = dyad m * dyad (j - m) := by
    intro j hj
    have hmj : m ≤ j := s.min'_le j hj
    rw [dyad, dyad, dyad, ← pow_add]
    congr 1
    omega
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a - m = b - m → a = b := by
    intro a ha b hb hab
    have h1 : m ≤ a := s.min'_le a ha
    have h2 : m ≤ b := s.min'_le b hb
    omega
  have hsub : s.image (fun j => j - m) ⊆ Finset.range (s.max' hne + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have : j ≤ s.max' hne := s.le_max' j hj
    simp only [Finset.mem_range]
    omega
  have htail : ∑ j ∈ s, dyad (j - m) ≤ 2 := by
    rw [← Finset.sum_image hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (sum_dyad_le _)
    exact fun i _ _ => dyad_nonneg i
  calc ∑ j ∈ s, dyad j = ∑ j ∈ s, dyad m * dyad (j - m) := Finset.sum_congr rfl hsplit
    _ = dyad m * ∑ j ∈ s, dyad (j - m) := by rw [Finset.mul_sum]
    _ ≤ dyad m * 2 := mul_le_mul_of_nonneg_left htail (dyad_nonneg m)
    _ ≤ c * 2 := by
        have := h m hmem
        nlinarith [dyad_nonneg m]
    _ = 2 * c := by ring

/-- The decreasing half for a power `k ≥ 1`: the ratio between consecutive terms
is `2^{-k} ≤ 1/2`, so the same bound `2c` holds for every `k`. -/
theorem sum_dyad_pow_le_two_mul {s : Finset ℕ} {c : ℝ} {k : ℕ} (hk : 1 ≤ k) (hc : 0 ≤ c)
    (h : ∀ j ∈ s, (dyad j) ^ k ≤ c) : ∑ j ∈ s, (dyad j) ^ k ≤ 2 * c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; linarith
  have hmem := s.min'_mem hne
  set m := s.min' hne with hm
  have hsplit : ∀ j ∈ s, (dyad j) ^ k = (dyad m) ^ k * (dyad (j - m)) ^ k := by
    intro j hj
    have hmj : m ≤ j := s.min'_le j hj
    rw [← mul_pow, dyad, dyad, dyad, ← pow_add]
    congr 2
    omega
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a - m = b - m → a = b := by
    intro a ha b hb hab
    have h1 : m ≤ a := s.min'_le a ha
    have h2 : m ≤ b := s.min'_le b hb
    omega
  have hsub : s.image (fun j => j - m) ⊆ Finset.range (s.max' hne + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have : j ≤ s.max' hne := s.le_max' j hj
    simp only [Finset.mem_range]
    omega
  have htail : ∑ j ∈ s, (dyad (j - m)) ^ k ≤ 2 := by
    have himg : ∑ i ∈ s.image (fun j => j - m), (dyad i) ^ k
        = ∑ j ∈ s, (dyad (j - m)) ^ k := Finset.sum_image hinj
    rw [← himg]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (sum_dyad_pow_le hk _)
    exact fun i _ _ => pow_nonneg (dyad_nonneg i) k
  calc ∑ j ∈ s, (dyad j) ^ k = ∑ j ∈ s, (dyad m) ^ k * (dyad (j - m)) ^ k :=
        Finset.sum_congr rfl hsplit
    _ = (dyad m) ^ k * ∑ j ∈ s, (dyad (j - m)) ^ k := by rw [Finset.mul_sum]
    _ ≤ (dyad m) ^ k * 2 := mul_le_mul_of_nonneg_left htail (pow_nonneg (dyad_nonneg m) k)
    _ ≤ c * 2 := by nlinarith [h m hmem, pow_nonneg (dyad_nonneg m) k]
    _ = 2 * c := by ring

/-- **The increasing half, in general form.**  For any ratio `b ≥ 2`, a sum of
`b ^ j` over an arbitrary set of exponents is at most twice its largest term.
The bound `b/(b-1) ≤ 2` is exactly the condition `b ≥ 2`, which is why this one
statement covers both `(dyad j)⁻¹ = 2 ^ j` and its square `4 ^ j`. -/
theorem sum_pow_le_two_mul {s : Finset ℕ} {b c : ℝ} (hb : 2 ≤ b) (hc : 0 ≤ c)
    (h : ∀ j ∈ s, b ^ j ≤ c) : ∑ j ∈ s, b ^ j ≤ 2 * c := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : b ≠ 1 := by intro hh; rw [hh] at hb; linarith
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; linarith
  have hmem := s.max'_mem hne
  set M := s.max' hne with hM
  have hsub : s ⊆ Finset.range (M + 1) := by
    intro j hj
    have := s.le_max' j hj
    simp only [Finset.mem_range]
    omega
  have hgeom : ∑ j ∈ Finset.range (M + 1), b ^ j = (b ^ (M + 1) - 1) / (b - 1) :=
    geom_sum_eq hb1 _
  have h1 : ∑ j ∈ s, b ^ j ≤ (b ^ (M + 1) - 1) / (b - 1) := by
    rw [← hgeom]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => (pow_pos hb0 i).le
  have hb1' : (0 : ℝ) < b - 1 := by linarith
  have h2 : (b ^ (M + 1) - 1) / (b - 1) ≤ 2 * b ^ M := by
    rw [div_le_iff₀ hb1', pow_succ]
    nlinarith [pow_pos hb0 M]
  have h3 : b ^ M ≤ c := h M hmem
  linarith

/-- The increasing half at `b = 2`: used on the block `r > 1/(d+1)`, where the
filter condition bounds `(dyad j)⁻¹` by `d + 1`. -/
theorem sum_inv_dyad_le_two_mul {s : Finset ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ s, (dyad j)⁻¹ ≤ c) : ∑ j ∈ s, (dyad j)⁻¹ ≤ 2 * c := by
  simp only [inv_dyad] at h ⊢
  exact sum_pow_le_two_mul (by norm_num) hc h

theorem inv_dyad_sq (j : ℕ) : ((dyad j)⁻¹) ^ 2 = (4 : ℝ) ^ j := by
  rw [inv_dyad, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The increasing half at `b = 4`: the second dyadic sum carries `r⁻²`. -/
theorem sum_inv_dyad_sq_le_two_mul {s : Finset ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ s, ((dyad j)⁻¹) ^ 2 ≤ c) : ∑ j ∈ s, ((dyad j)⁻¹) ^ 2 ≤ 2 * c := by
  simp only [inv_dyad_sq] at h ⊢
  exact sum_pow_le_two_mul (by norm_num) hc h

section Dyadic

variable (L : ℕ) [NeZero L] (ξ : ℂ)

omit [NeZero L] in
/-- `(eq_dyadic_sum1)`.  Note there is **no hypothesis on `ξ` and none on `L`**:
the denominator `κ² + r²` is positive because `r > 0`, and the `ℓ̂⁻¹` term on the
right is nonnegative for free.  In fact the proof never uses that term at all --
see the note below. -/
theorem dyadic_sum_three_le (d J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ)
      ≤ 8 * ((d : ℝ) + 1)⁻¹ + 8 * (ellhat L ξ)⁻¹ := by
  have hD : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hbase : ∀ j : ℕ, (1 : ℝ) ≤ 1 + dyad j * d := by
    intro j
    have h1 := (dyad_pos j).le
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hzp : ∀ j : ℕ, (1 + dyad j * d) ^ (-3 : ℤ) = ((1 + dyad j * d) ^ 3)⁻¹ := by
    intro j
    rw [zpow_neg]
    norm_num
  set T : ℕ → ℝ := fun j =>
    (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ) with hTdef
  -- the pointwise facts, all of them uniform in `j`
  have hpow : ∀ j : ℕ, (0 : ℝ) < (1 + dyad j * d) ^ 3 := fun j =>
    pow_pos (by have := hbase j; linarith) 3
  have hden : ∀ j : ℕ, (0 : ℝ) < kappa ξ ^ 2 + (dyad j) ^ 2 := fun j => by
    have h1 := pow_pos (dyad_pos j) 2
    nlinarith [sq_nonneg (kappa ξ)]
  have hfrac : ∀ j : ℕ, (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) ≤ dyad j := by
    intro j
    have hr := dyad_pos j
    rw [div_le_iff₀ (hden j)]
    nlinarith [mul_nonneg hr.le (sq_nonneg (kappa ξ))]
  have hTnn : ∀ j : ℕ, 0 ≤ T j := by
    intro j
    rw [hTdef]
    simp only [hzp j]
    exact mul_nonneg (div_nonneg (pow_nonneg (dyad_pos j).le 3) (hden j).le)
      (inv_nonneg.mpr (hpow j).le)
  have hTle : ∀ j : ℕ, T j ≤ dyad j := by
    intro j
    rw [hTdef]
    simp only [hzp j]
    have hr := dyad_pos j
    have h2 : ((1 + dyad j * d) ^ 3)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (hpow j)]
      exact one_le_pow₀ (hbase j)
    calc (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) * ((1 + dyad j * d) ^ 3)⁻¹
        ≤ dyad j * 1 :=
          mul_le_mul (hfrac j) h2 (by positivity) hr.le
      _ = dyad j := mul_one _
  -- the one split: `r ≤ 1/(d+1)` or not
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (J + 1))
        (fun j => dyad j ≤ ((d : ℝ) + 1)⁻¹)]
  have hsmall : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => dyad j ≤ ((d : ℝ) + 1)⁻¹), T j
      ≤ 2 * ((d : ℝ) + 1)⁻¹ := by
    refine le_trans (Finset.sum_le_sum fun j _ => hTle j) ?_
    exact sum_dyad_le_two_mul (by positivity) fun j hj => (Finset.mem_filter.mp hj).2
  have hlarge : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹), T j
      ≤ 2 * ((d : ℝ) + 1)⁻¹ := by
    -- on this block `1 + r d ≥ r (d+1)` because `r ≤ 1`, so `T j ≤ r⁻² (d+1)⁻³`
    have key : ∀ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹),
        T j ≤ ((dyad j)⁻¹) ^ 2 * (((d : ℝ) + 1) ^ 3)⁻¹ := by
      intro j _
      rw [hTdef]
      simp only [hzp j]
      have hr := dyad_pos j
      have hr1 := dyad_le_one j
      have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hge : dyad j * ((d : ℝ) + 1) ≤ 1 + dyad j * d := by nlinarith
      have hlo : (0 : ℝ) < dyad j * ((d : ℝ) + 1) := by positivity
      have hcube : (dyad j * ((d : ℝ) + 1)) ^ 3 ≤ (1 + dyad j * d) ^ 3 := by
        exact pow_le_pow_left₀ hlo.le hge 3
      have hinv : ((1 + dyad j * d) ^ 3)⁻¹ ≤ ((dyad j * ((d : ℝ) + 1)) ^ 3)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le (pow_pos hlo 3) hcube
      calc (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) * ((1 + dyad j * d) ^ 3)⁻¹
          ≤ dyad j * ((dyad j * ((d : ℝ) + 1)) ^ 3)⁻¹ :=
            mul_le_mul (hfrac j) hinv (by positivity) hr.le
        _ = ((dyad j)⁻¹) ^ 2 * (((d : ℝ) + 1) ^ 3)⁻¹ := by
            field_simp
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [← Finset.sum_mul]
    have hbd : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹),
        ((dyad j)⁻¹) ^ 2 ≤ 2 * ((d : ℝ) + 1) ^ 2 := by
      refine sum_inv_dyad_sq_le_two_mul (by positivity) fun j hj => ?_
      have hj2 : ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹ := (Finset.mem_filter.mp hj).2
      have hgt : ((d : ℝ) + 1)⁻¹ < dyad j := lt_of_not_ge hj2
      have hinv : (dyad j)⁻¹ ≤ (d : ℝ) + 1 := by
        rw [inv_le_comm₀ (dyad_pos j) hD]
        exact le_of_lt hgt
      nlinarith [inv_pos.mpr (dyad_pos j)]
    have hfac : (0 : ℝ) ≤ (((d : ℝ) + 1) ^ 3)⁻¹ := by positivity
    calc (∑ j ∈ _, ((dyad j)⁻¹) ^ 2) * (((d : ℝ) + 1) ^ 3)⁻¹
        ≤ (2 * ((d : ℝ) + 1) ^ 2) * (((d : ℝ) + 1) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hbd hfac
      _ = 2 * ((d : ℝ) + 1)⁻¹ := by field_simp
  have hell : (0 : ℝ) ≤ 8 * (ellhat L ξ)⁻¹ := by
    have h : (0 : ℝ) ≤ ellhat L ξ :=
      le_min (inv_nonneg.mpr (kappa_nonneg ξ)) (Nat.cast_nonneg L)
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr h)
  have hDinv : (0 : ℝ) ≤ ((d : ℝ) + 1)⁻¹ := by positivity
  linarith

omit [NeZero L] in
/-- `(eq_dyadic_sum2)`.  Word for word the previous proof with every power
raised by one: the fraction is bounded by `r²` instead of `r`, the small block
gives `2(d+1)^{-2}` instead of `2(d+1)^{-1}`, and the large block carries `r⁻¹`
instead of `r⁻²`. -/
theorem dyadic_sum_four_le (d J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ)
      ≤ 8 * (((d : ℝ) ^ 2 + 1))⁻¹ + 8 * (ellhat L ξ) ^ (-2 : ℤ) := by
  have hD : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hbase : ∀ j : ℕ, (1 : ℝ) ≤ 1 + dyad j * d := by
    intro j
    have h1 := (dyad_pos j).le
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hzp : ∀ j : ℕ, (1 + dyad j * d) ^ (-3 : ℤ) = ((1 + dyad j * d) ^ 3)⁻¹ := by
    intro j
    rw [zpow_neg]
    norm_num
  have hpow : ∀ j : ℕ, (0 : ℝ) < (1 + dyad j * d) ^ 3 := fun j =>
    pow_pos (by have := hbase j; linarith) 3
  have hden : ∀ j : ℕ, (0 : ℝ) < kappa ξ ^ 2 + (dyad j) ^ 2 := fun j => by
    have h1 := pow_pos (dyad_pos j) 2
    nlinarith [sq_nonneg (kappa ξ)]
  set T : ℕ → ℝ := fun j =>
    (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ) with hTdef
  have hfrac : ∀ j : ℕ, (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) ≤ (dyad j) ^ 2 := by
    intro j
    rw [div_le_iff₀ (hden j)]
    nlinarith [mul_nonneg (pow_nonneg (dyad_pos j).le 2) (sq_nonneg (kappa ξ))]
  have hTle : ∀ j : ℕ, T j ≤ (dyad j) ^ 2 := by
    intro j
    rw [hTdef]
    simp only [hzp j]
    have h2 : ((1 + dyad j * d) ^ 3)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (hpow j)]
      exact one_le_pow₀ (hbase j)
    calc (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) * ((1 + dyad j * d) ^ 3)⁻¹
        ≤ (dyad j) ^ 2 * 1 :=
          mul_le_mul (hfrac j) h2 (inv_nonneg.mpr (hpow j).le)
            (pow_nonneg (dyad_pos j).le 2)
      _ = (dyad j) ^ 2 := mul_one _
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (J + 1))
        (fun j => dyad j ≤ ((d : ℝ) + 1)⁻¹)]
  have hsmall : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => dyad j ≤ ((d : ℝ) + 1)⁻¹), T j
      ≤ 2 * (((d : ℝ) + 1) ^ 2)⁻¹ := by
    refine le_trans (Finset.sum_le_sum fun j _ => hTle j) ?_
    refine sum_dyad_pow_le_two_mul (by omega) (by positivity) fun j hj => ?_
    have hj2 : dyad j ≤ ((d : ℝ) + 1)⁻¹ := (Finset.mem_filter.mp hj).2
    calc (dyad j) ^ 2 ≤ (((d : ℝ) + 1)⁻¹) ^ 2 := pow_le_pow_left₀ (dyad_pos j).le hj2 2
      _ = (((d : ℝ) + 1) ^ 2)⁻¹ := by rw [inv_pow]
  have hlarge : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹), T j
      ≤ 2 * (((d : ℝ) + 1) ^ 2)⁻¹ := by
    have key : ∀ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹),
        T j ≤ (dyad j)⁻¹ * (((d : ℝ) + 1) ^ 3)⁻¹ := by
      intro j _
      rw [hTdef]
      simp only [hzp j]
      have hr := dyad_pos j
      have hr1 := dyad_le_one j
      have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hge : dyad j * ((d : ℝ) + 1) ≤ 1 + dyad j * d := by nlinarith
      have hlo : (0 : ℝ) < dyad j * ((d : ℝ) + 1) := by positivity
      have hcube : (dyad j * ((d : ℝ) + 1)) ^ 3 ≤ (1 + dyad j * d) ^ 3 :=
        pow_le_pow_left₀ hlo.le hge 3
      have hinv : ((1 + dyad j * d) ^ 3)⁻¹ ≤ ((dyad j * ((d : ℝ) + 1)) ^ 3)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le (pow_pos hlo 3) hcube
      calc (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) * ((1 + dyad j * d) ^ 3)⁻¹
          ≤ (dyad j) ^ 2 * ((dyad j * ((d : ℝ) + 1)) ^ 3)⁻¹ :=
            mul_le_mul (hfrac j) hinv (by positivity) (pow_nonneg hr.le 2)
        _ = (dyad j)⁻¹ * (((d : ℝ) + 1) ^ 3)⁻¹ := by field_simp
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [← Finset.sum_mul]
    have hbd : ∑ j ∈ (Finset.range (J + 1)).filter (fun j => ¬ dyad j ≤ ((d : ℝ) + 1)⁻¹),
        (dyad j)⁻¹ ≤ 2 * ((d : ℝ) + 1) := by
      refine sum_inv_dyad_le_two_mul hD.le fun j hj => ?_
      have hgt : ((d : ℝ) + 1)⁻¹ < dyad j := lt_of_not_ge (Finset.mem_filter.mp hj).2
      rw [inv_le_comm₀ (dyad_pos j) hD]
      exact le_of_lt hgt
    calc (∑ j ∈ _, (dyad j)⁻¹) * (((d : ℝ) + 1) ^ 3)⁻¹
        ≤ (2 * ((d : ℝ) + 1)) * (((d : ℝ) + 1) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hbd (by positivity)
      _ = 2 * (((d : ℝ) + 1) ^ 2)⁻¹ := by field_simp
  have hell : (0 : ℝ) ≤ 8 * (ellhat L ξ) ^ (-2 : ℤ) := by
    have h : (0 : ℝ) ≤ ellhat L ξ :=
      le_min (inv_nonneg.mpr (kappa_nonneg ξ)) (Nat.cast_nonneg L)
    have h2 : (0 : ℝ) ≤ (ellhat L ξ) ^ (-2 : ℤ) := by
      rw [zpow_neg]
      exact inv_nonneg.mpr (by positivity)
    linarith
  have hfin : 4 * (((d : ℝ) + 1) ^ 2)⁻¹ ≤ 8 * (((d : ℝ) ^ 2 + 1))⁻¹ := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have h1 : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (d : ℝ) ^ 2 + 1 := by positivity
    rw [← sub_nonneg]
    have hrw : 8 * (((d : ℝ) ^ 2 + 1))⁻¹ - 4 * (((d : ℝ) + 1) ^ 2)⁻¹
        = (8 * ((d : ℝ) + 1) ^ 2 - 4 * ((d : ℝ) ^ 2 + 1)) /
            (((d : ℝ) ^ 2 + 1) * ((d : ℝ) + 1) ^ 2) := by
      field_simp
    rw [hrw]
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith


end Dyadic

end RBM
