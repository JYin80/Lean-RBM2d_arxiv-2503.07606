/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import RBM2D.Defs.Dist

/-!
# Lattice counts on `Z_L²` (periodic `L¹` distance)

Four elementary facts:

* `zdist2_le` : `|u|_L ≤ L`;
* `card_ball_le` : `#{u : |a - u|_L ≤ R} ≤ (2R+1)²`;
* `sum_inv_sq_le` : `Σ_u (|a - u|_L² + 1)⁻¹ ≤ 5 + 4 log L`;
* `sum_exp_le` : `Σ_u e^{-s |a - u|_L} ≤ (1 + 2/s)²`.

Method: there are at most `2` points of `Z_L` at each 1-dimensional distance `j ≥ 1` (and one at
`j = 0`), hence at most `4r` points of `Z_L²` at distance `r ≥ 1`; the exponential sum factors
through `zdist2 = zdist + zdist`.
-/

namespace RBM.KLoop

open Finset

section Dist

variable (L : ℕ) [NeZero L]

/-- `|u|_L ≤ L` on `Z_L²` (so the complement of the ball of radius `R ≥ L` is empty). -/
theorem zdist2_le (u : Z2 L) : zdist2 L u ≤ L := by
  have h1 : 2 * zdist L u.1 ≤ L := by
    have := ZMod.val_lt u.1
    simp only [zdist]; omega
  have h2 : 2 * zdist L u.2 ≤ L := by
    have := ZMod.val_lt u.2
    simp only [zdist]; omega
  simp only [zdist2]; omega

end Dist

/-! ### Private counting helpers -/

/-- Bound on the number of points of `Z_L` at a given distance from `0`. -/
private def cnt (j : ℕ) : ℕ := if j = 0 then 1 else 2

private theorem cnt_zero : cnt 0 = 1 := by simp [cnt]

private theorem cnt_succ (j : ℕ) : cnt (j + 1) = 2 := by simp [cnt]

/-- Bound on the number of points of `Z_L²` at a given distance from `0`. -/
private def cnt2 (r : ℕ) : ℕ := ∑ i ∈ range (r + 1), cnt i * cnt (r - i)

private theorem cnt2_zero : cnt2 0 = 1 := by simp [cnt2, cnt]

private theorem sum_cnt (m : ℕ) : ∑ j ∈ range (m + 1), cnt j = 2 * m + 1 := by
  induction m with
  | zero => simp [cnt_zero]
  | succ n ih => rw [sum_range_succ, ih, cnt_succ]; ring

private theorem cnt2_le (r : ℕ) (hr : 1 ≤ r) : cnt2 r ≤ 4 * r := by
  have h : ∀ i ∈ range (r + 1), cnt i * cnt (r - i) + 2 * (if i = 0 then 1 else 0)
      + 2 * (if i = r then 1 else 0) ≤ 4 := by
    intro i hi
    rw [mem_range] at hi
    unfold cnt
    split_ifs <;> omega
  have h2 := sum_le_sum h
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at h2
  simp only [sum_ite_eq', mem_range, sum_const, card_range, smul_eq_mul] at h2
  have h3 : (if 0 < r + 1 then 1 else 0) = 1 := by simp
  have h4 : (if r < r + 1 then 1 else 0) = 1 := by simp
  rw [h3, h4] at h2
  unfold cnt2
  omega

private theorem zdist_le_self (L : ℕ) [NeZero L] (y : ZMod L) : zdist L y ≤ L := by
  have := ZMod.val_lt y
  simp only [zdist]; omega

private theorem zdist_fiber_card (L : ℕ) [NeZero L] (j : ℕ) :
    (univ.filter fun x : ZMod L => zdist L x = j).card ≤ cnt j := by
  by_cases hj : j = 0
  · subst hj
    rw [cnt_zero]
    apply Finset.card_le_one.2
    intro x hx y hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    rw [zdist_eq_zero_iff] at hx hy
    rw [hx, hy]
  · have hsub : (univ.filter fun x : ZMod L => zdist L x = j) ⊆
        ({(j : ZMod L), -(j : ZMod L)} : Finset (ZMod L)) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hv := ZMod.val_lt x
      have hx' : (x.val : ZMod L) = x := ZMod.natCast_zmod_val x
      simp only [zdist] at hx
      simp only [mem_insert, mem_singleton]
      by_cases h : x.val ≤ L - x.val
      · left
        have : x.val = j := by omega
        rw [← hx', this]
      · right
        have hle : j ≤ L := by omega
        have : x.val = L - j := by omega
        rw [← hx', this, Nat.cast_sub hle, ZMod.natCast_self]
        simp
    calc _ ≤ ({(j : ZMod L), -(j : ZMod L)} : Finset (ZMod L)).card := card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
      _ = cnt j := by simp [cnt, hj]

private theorem card_ball1_le (L : ℕ) [NeZero L] (m : ℕ) :
    (univ.filter fun x : ZMod L => zdist L x ≤ m).card ≤ 2 * m + 1 := by
  have hsub : (univ.filter fun x : ZMod L => zdist L x ≤ m) ⊆
      (range (m + 1)).biUnion (fun j => univ.filter fun x : ZMod L => zdist L x = j) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    exact ⟨zdist L x, by omega, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ j ∈ range (m + 1), (univ.filter fun x : ZMod L => zdist L x = j).card :=
        card_biUnion_le
    _ ≤ ∑ j ∈ range (m + 1), cnt j := sum_le_sum fun j _ => zdist_fiber_card L j
    _ = 2 * m + 1 := sum_cnt m

private theorem card_sphere2_le (L : ℕ) [NeZero L] (r : ℕ) :
    (univ.filter fun x : Z2 L => zdist2 L x = r).card ≤ cnt2 r := by
  have hsub : (univ.filter fun x : Z2 L => zdist2 L x = r) ⊆
      (range (r + 1)).biUnion (fun i => (univ.filter fun y : ZMod L => zdist L y = i) ×ˢ
        (univ.filter fun y : ZMod L => zdist L y = r - i)) := by
    intro x hx
    have hx2 : zdist2 L x = r := (mem_filter.1 hx).2
    simp only [zdist2] at hx2
    simp only [mem_biUnion, mem_range, mem_product, mem_filter, mem_univ, true_and]
    exact ⟨zdist L x.1, by omega, rfl, by omega⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i ∈ range (r + 1), ((univ.filter fun y : ZMod L => zdist L y = i) ×ˢ
        (univ.filter fun y : ZMod L => zdist L y = r - i)).card := card_biUnion_le
    _ ≤ cnt2 r := sum_le_sum fun i _ => by
        rw [card_product]
        exact Nat.mul_le_mul (zdist_fiber_card L i) (zdist_fiber_card L (r - i))

private theorem sum_zdist_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ y : ZMod L, f (zdist L y) ≤ ∑ j ∈ range (L + 1), (cnt j : ℝ) * f j := by
  rw [← sum_fiberwise_of_maps_to (g := zdist L) (t := range (L + 1))
    (fun y _ => mem_range.2 (Nat.lt_succ_of_le (zdist_le_self L y)))]
  refine sum_le_sum fun j _ => ?_
  have : ∑ y ∈ univ.filter (fun y : ZMod L => zdist L y = j), f (zdist L y)
      = ((univ.filter fun y : ZMod L => zdist L y = j).card : ℝ) * f j := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun y hy => by rw [(mem_filter.1 hy).2]
  rw [this]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (zdist_fiber_card L j)) (hf j)

private theorem sum_zdist2_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ x : Z2 L, f (zdist2 L x) ≤ ∑ r ∈ range (L + 1), (cnt2 r : ℝ) * f r := by
  rw [← sum_fiberwise_of_maps_to (g := zdist2 L) (t := range (L + 1))
    (fun y _ => mem_range.2 (Nat.lt_succ_of_le (zdist2_le L y)))]
  refine sum_le_sum fun j _ => ?_
  have : ∑ y ∈ univ.filter (fun y : Z2 L => zdist2 L y = j), f (zdist2 L y)
      = ((univ.filter fun y : Z2 L => zdist2 L y = j).card : ℝ) * f j := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun y hy => by rw [(mem_filter.1 hy).2]
  rw [this]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (card_sphere2_le L j)) (hf j)

/-! ### The counts -/

/-- **Ball count** on `Z_L²` with the periodic `L¹` distance: `#{u : |a - u|_L ≤ R} ≤ (2R+1)²`. -/
theorem card_ball_le : ∀ (L : ℕ) [NeZero L] (a : Z2 L) (R : ℝ), 0 ≤ R →
    (((Finset.univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ)
      ≤ (2 * R + 1) ^ 2 := by
  intro L _ a R hR
  set m : ℕ := ⌊R⌋₊ with hm
  have hmR : (m : ℝ) ≤ R := Nat.floor_le hR
  have hinj : (univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card ≤
      ((univ.filter fun x : ZMod L => zdist L x ≤ m) ×ˢ
        (univ.filter fun x : ZMod L => zdist L x ≤ m)).card := by
    refine Finset.card_le_card_of_injOn (fun u => a - u) ?_ ?_
    · intro u hu
      have hu' : (zdist2 L (a - u) : ℝ) ≤ R := by simpa using hu
      have h1 : zdist2 L (a - u) ≤ m := Nat.le_floor hu'
      simp only [zdist2] at h1
      simp only [coe_product, Set.mem_prod, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨by omega, by omega⟩
    · intro u _ v _ h
      exact sub_right_injective h
  have hc : (univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card ≤ (2 * m + 1) ^ 2 := by
    refine hinj.trans ?_
    rw [card_product, sq]
    exact Nat.mul_le_mul (card_ball1_le L m) (card_ball1_le L m)
  calc (((univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ)
      ≤ (((2 * m + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_le.2 hc
    _ = (2 * (m : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ (2 * R + 1) ^ 2 := by gcongr

/-- **The logarithmic sum**: `Σ_{u ∈ Z_L²} (|a - u|_L² + 1)⁻¹ ≤ 5 + 4 log L` (at most `4r` points
at distance `r ≥ 1`, and `|·|_L ≤ L`). -/
theorem sum_inv_sq_le : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ a : Z2 L,
    ∑ u : Z2 L, ((zdist2 L (a - u) : ℝ) ^ 2 + 1)⁻¹ ≤ 5 + 4 * Real.log L := by
  intro L _ _ a
  have hre : ∑ u : Z2 L, ((zdist2 L (a - u) : ℝ) ^ 2 + 1)⁻¹
      = ∑ x : Z2 L, ((zdist2 L x : ℝ) ^ 2 + 1)⁻¹ :=
    Equiv.sum_comp (Equiv.subLeft a) (fun x : Z2 L => ((zdist2 L x : ℝ) ^ 2 + 1)⁻¹)
  rw [hre]
  have h := sum_zdist2_le L (fun r : ℕ => (((r : ℕ) : ℝ) ^ 2 + 1)⁻¹) (fun r => by positivity)
  refine h.trans ?_
  rw [sum_range_succ']
  have hpt : ∀ j ∈ range L, (cnt2 (j + 1) : ℝ) * ((((j + 1 : ℕ) : ℝ)) ^ 2 + 1)⁻¹
      ≤ 4 * (((j : ℝ) + 1))⁻¹ := by
    intro j _
    have hc : (cnt2 (j + 1) : ℝ) ≤ 4 * ((j : ℝ) + 1) := by
      have := cnt2_le (j + 1) (by omega)
      exact_mod_cast this
    have hx : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    push_cast
    calc (cnt2 (j + 1) : ℝ) * (((j : ℝ) + 1) ^ 2 + 1)⁻¹
        ≤ (4 * ((j : ℝ) + 1)) * (((j : ℝ) + 1) ^ 2 + 1)⁻¹ := by gcongr
      _ ≤ 4 * (((j : ℝ) + 1))⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hx]
        nlinarith
  have hsum : ∑ j ∈ range L, (cnt2 (j + 1) : ℝ) * ((((j + 1 : ℕ) : ℝ)) ^ 2 + 1)⁻¹
      ≤ 4 * (1 + Real.log L) := by
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum]
    have hH : ∑ j ∈ range L, (((j : ℝ) + 1))⁻¹ = ((harmonic L : ℚ) : ℝ) := by
      simp [harmonic]
    rw [hH]
    have := harmonic_le_one_add_log L
    linarith
  have hz : (cnt2 0 : ℝ) * (((0 : ℕ) : ℝ) ^ 2 + 1)⁻¹ = 1 := by
    simp [cnt2_zero]
  rw [hz]
  push_cast at hsum ⊢
  linarith

/-- The one-dimensional exponential sum after peeling the geometric series. -/
private theorem geo_le (s : ℝ) (n : ℕ) :
    (∑ j ∈ range n, Real.exp (-(s * ((j : ℝ) + 1)))) * s ≤ 1 := by
  set q := Real.exp (-s) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q * (s + 1) ≤ 1 := by
    have h1 := Real.add_one_le_exp s
    have h : q * Real.exp s = 1 := by rw [hq, ← Real.exp_add]; simp
    nlinarith
  have hterm : ∀ j : ℕ, Real.exp (-(s * ((j : ℝ) + 1))) = q ^ (j + 1) := by
    intro j
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : ∀ n : ℕ, (∑ j ∈ range n, q ^ (j + 1)) * (1 - q) = q * (1 - q ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, add_mul, ih]; ring
  simp only [hterm]
  set T := ∑ j ∈ range n, q ^ (j + 1) with hT
  have hT0 : 0 ≤ T := sum_nonneg fun j _ => by positivity
  have hqn : 0 ≤ q ^ n := by positivity
  have hk := key n
  have h1 : T * (s * q) ≤ T * (1 - q) := mul_le_mul_of_nonneg_left (by nlinarith) hT0
  have h2 : T * (1 - q) ≤ q := by rw [hk]; nlinarith
  have h3 : q * (T * s) ≤ q * 1 := by nlinarith
  exact le_of_mul_le_mul_left h3 hq0

/-- **The exponential sum**: `Σ_{u ∈ Z_L²} e^{-s |a - u|_L} ≤ (1 + 2/s)²`. -/
theorem sum_exp_le : ∀ (L : ℕ) [NeZero L] (s : ℝ), 0 < s → ∀ a : Z2 L,
    ∑ u : Z2 L, Real.exp (-(s * (zdist2 L (a - u) : ℝ))) ≤ (1 + 2 / s) ^ 2 := by
  intro L _ s hs a
  have hre : ∑ u : Z2 L, Real.exp (-(s * (zdist2 L (a - u) : ℝ)))
      = ∑ x : Z2 L, Real.exp (-(s * (zdist2 L x : ℝ))) :=
    Equiv.sum_comp (Equiv.subLeft a) (fun x : Z2 L => Real.exp (-(s * (zdist2 L x : ℝ))))
  have hfac : ∑ x : Z2 L, Real.exp (-(s * (zdist2 L x : ℝ)))
      = (∑ y : ZMod L, Real.exp (-(s * (zdist L y : ℝ)))) ^ 2 := by
    rw [sq, sum_mul_sum, ← Fintype.sum_prod_type']
    refine sum_congr rfl fun x _ => ?_
    simp only [zdist2, Nat.cast_add, mul_add, neg_add, Real.exp_add]
  have h1 : ∑ y : ZMod L, Real.exp (-(s * (zdist L y : ℝ))) ≤ 1 + 2 / s := by
    have h := sum_zdist_le L (fun j : ℕ => Real.exp (-(s * (j : ℝ)))) (fun j => (Real.exp_pos _).le)
    refine h.trans ?_
    rw [sum_range_succ']
    have hs' : ∑ j ∈ range L, (cnt (j + 1) : ℝ) * Real.exp (-(s * (((j + 1 : ℕ) : ℝ))))
        = 2 * ∑ j ∈ range L, Real.exp (-(s * ((j : ℝ) + 1))) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [cnt_succ]; push_cast; ring_nf
    rw [hs']
    simp only [cnt_zero, Nat.cast_one, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have hg := geo_le s L
    have : ∑ j ∈ range L, Real.exp (-(s * ((j : ℝ) + 1))) ≤ 1 / s := by
      rw [le_div_iff₀ hs]; exact hg
    have h2 : 2 * ∑ j ∈ range L, Real.exp (-(s * ((j : ℝ) + 1))) ≤ 2 / s := by
      calc _ ≤ 2 * (1 / s) := by linarith
        _ = 2 / s := by ring
    linarith
  rw [hre, hfac]
  exact pow_le_pow_left₀ (sum_nonneg fun y _ => (Real.exp_pos _).le) h1 2

end RBM.KLoop
