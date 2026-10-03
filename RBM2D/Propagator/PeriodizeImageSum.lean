/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Shells
import RBM2D.Propagator.PeriodizeDescend

/-!
# Image sums for the periodization (Section 8.2)

One- and two-dimensional image sums of `exp (-(α |·|))` over the non-centered lift
`torusLatticeLift`; the two-dimensional sums are reduced coordinatewise to the
one-dimensional ones.
-/

namespace RBM

open Real

section Geom

/-- Geometric-series bound: `∑_{n ∈ ℤ} e^{-a|u + nL|} ≤ 2 e^{-ad} / (1 - e^{-aL})`. -/
private theorem PeriodizeImageSum_shift_le {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 0 < L) {u : ℤ}
    (hu0 : 0 ≤ u) (huL : u < L) {d : ℝ} (hd1 : d ≤ u) (hd2 : d ≤ L - u) :
    Summable (fun n : ℤ => exp (-(a * |(u : ℝ) + n * L|))) ∧
    ∑' n : ℤ, exp (-(a * |(u : ℝ) + n * L|)) ≤ 2 * exp (-(a * d)) / (1 - exp (-(a * L))) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set r := exp (-(a * L)) with hr
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := exp_lt_one_iff.2 (by nlinarith)
  set f : ℤ → ℝ := fun n => exp (-(a * |(u : ℝ) + n * L|)) with hf
  set g : ℕ → ℝ := fun k => exp (-(a * d)) * r ^ k with hg
  have hgs : Summable g := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hrk : ∀ k : ℕ, exp (-(a * d)) * r ^ k = exp (-(a * (d + k * L))) := by
    intro k
    rw [hr, ← exp_nat_mul, ← exp_add]; ring_nf
  have hpos : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simp only [hf, hg, hrk, Int.cast_natCast]
    apply exp_le_exp.2
    have : (u : ℝ) + k * L ≥ 0 := by positivity
    rw [abs_of_nonneg this]
    have hu : d ≤ (u : ℝ) := hd1
    nlinarith
  have hneg : ∀ k : ℕ, f (-(k + 1 : ℤ)) ≤ g k := by
    intro k
    simp only [hf, hg, hrk]
    apply exp_le_exp.2
    push_cast
    have huL' : (u : ℝ) < L := by exact_mod_cast huL
    have : (u : ℝ) + -((k : ℝ) + 1) * L ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]
    nlinarith
  have hf0 : ∀ n, 0 ≤ f n := fun n => (exp_pos _).le
  have s1 : Summable fun k : ℕ => f k := Summable.of_nonneg_of_le (fun k => hf0 _) hpos hgs
  have s2 : Summable fun k : ℕ => f (-(k + 1 : ℤ)) :=
    Summable.of_nonneg_of_le (fun k => hf0 _) hneg hgs
  have hsum : ∑' k : ℕ, g k = exp (-(a * d)) / (1 - r) := by
    simp only [hg]
    rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one hr0 hr1),
      tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  refine ⟨Summable.of_nat_of_neg_add_one s1 s2, ?_⟩
  calc ∑' n : ℤ, f n = ∑' k : ℕ, f k + ∑' k : ℕ, f (-(k + 1 : ℤ)) :=
        tsum_of_nat_of_neg_add_one s1 s2
    _ ≤ ∑' k : ℕ, g k + ∑' k : ℕ, g k :=
        add_le_add (Summable.tsum_le_tsum hpos s1 hgs) (Summable.tsum_le_tsum hneg s2 hgs)
    _ = 2 * exp (-(a * d)) / (1 - r) := by rw [hsum]; ring

end Geom

private theorem PeriodizeImageSum_zdist_le_sub_val {L : ℕ} [NeZero L] (u : ZMod L) :
    (zdist L u : ℝ) ≤ L - u.val := by
  have h : zdist L u ≤ L - u.val := min_le_right _ _
  have hv : u.val ≤ L := (ZMod.val_lt u).le
  calc (zdist L u : ℝ) ≤ ((L - u.val : ℕ) : ℝ) := by exact_mod_cast h
    _ = L - u.val := by rw [Nat.cast_sub hv]

/-- `1 / (1 - e^{-x}) ≤ 20001` for `x ≥ 1/20000`. -/
private theorem PeriodizeImageSum_inv_one_sub_le {x : ℝ} (hx : 1 ≤ 20000 * x) :
    (1 - exp (-x))⁻¹ ≤ 20001 := by
  have hx0 : 0 < x := by linarith
  have h1 : x + 1 ≤ exp x := Real.add_one_le_exp x
  have hexp : exp (-x) = (exp x)⁻¹ := Real.exp_neg x
  have hE : 0 < exp x := exp_pos x
  have hpos : 0 < 1 - exp (-x) := by
    rw [hexp]
    have : (exp x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  rw [hexp]
  have : (exp x)⁻¹ ≤ 1 - 1 / 20001 := by
    rw [inv_le_comm₀ hE (by norm_num)]
    rw [show (1 - 1 / 20001 : ℝ)⁻¹ = 20001 / 20000 by norm_num]
    have : 20001 / 20000 ≤ 1 + x := by linarith
    linarith
  linarith

theorem tsum_exp_neg_abs_lift_le :
    ∀ (L : ℕ) [NeZero L], ∀ α : ℝ, 0 < α → 1 ≤ 20000 * α * L → ∀ v : ZMod L,
      Summable (fun n : ℤ => Real.exp (-(α * |(((v.val : ℤ) + n * L : ℤ) : ℝ)|))) ∧
      ∑' n : ℤ, Real.exp (-(α * |(((v.val : ℤ) + n * L : ℤ) : ℝ)|)) ≤
        40002 * Real.exp (-(α * zdist L v)) := by
  intro L _ α hα hαL v
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hvL : (v.val : ℤ) < L := by exact_mod_cast ZMod.val_lt v
  have hd1 : (zdist L v : ℝ) ≤ ((v.val : ℤ) : ℝ) := by
    have := zdist_le_val L v
    have h2 : (zdist L v : ℝ) ≤ (v.val : ℝ) := by exact_mod_cast this
    simpa using h2
  have hd2 : (zdist L v : ℝ) ≤ (L : ℝ) - ((v.val : ℤ) : ℝ) := by
    simpa using PeriodizeImageSum_zdist_le_sub_val v
  obtain ⟨hs, hb⟩ := PeriodizeImageSum_shift_le hα hL (u := (v.val : ℤ)) (by positivity) hvL hd1 hd2
  have hcast : ∀ n : ℤ, (((v.val : ℤ) + n * L : ℤ) : ℝ) = ((v.val : ℤ) : ℝ) + n * L := by
    intro n; push_cast; ring
  simp only [hcast]
  refine ⟨hs, hb.trans ?_⟩
  have hinv := PeriodizeImageSum_inv_one_sub_le (x := α * L) (by linarith)
  have he : 0 < exp (-(α * (zdist L v : ℝ))) := exp_pos _
  rw [mul_div_assoc, div_eq_mul_inv]
  calc 2 * (exp (-(α * (zdist L v : ℝ))) * (1 - exp (-(α * L)))⁻¹)
      ≤ 2 * (exp (-(α * (zdist L v : ℝ))) * 20001) := by gcongr
    _ = 40002 * exp (-(α * (zdist L v : ℝ))) := by ring

theorem tsum_exp_neg_l1_periodized_le :
    ∀ (L : ℕ) [NeZero L], ∀ α : ℝ, 0 < α → 1 ≤ 20000 * α * L → ∀ u : Z2 L,
      Summable (fun n : ℤ × ℤ => Real.exp (-(α *
          (|((torusLatticeLift u + L • n).1 : ℝ)| +
            |((torusLatticeLift u + L • n).2 : ℝ)|)))) ∧
      ∑' n : ℤ × ℤ, Real.exp (-(α *
          (|((torusLatticeLift u + L • n).1 : ℝ)| +
            |((torusLatticeLift u + L • n).2 : ℝ)|))) ≤
        40002 ^ 2 * Real.exp (-(α * zdist2 L u)) := by
  intro L _ α hα hαL u
  obtain ⟨hs1, hb1⟩ := tsum_exp_neg_abs_lift_le L α hα hαL u.1
  obtain ⟨hs2, hb2⟩ := tsum_exp_neg_abs_lift_le L α hα hαL u.2
  set f : ℤ → ℝ := fun n => Real.exp (-(α * |(((u.1.val : ℤ) + n * L : ℤ) : ℝ)|)) with hf
  set g : ℤ → ℝ := fun n => Real.exp (-(α * |(((u.2.val : ℤ) + n * L : ℤ) : ℝ)|)) with hg
  have hterm : ∀ n : ℤ × ℤ, Real.exp (-(α *
          (|((torusLatticeLift u + L • n).1 : ℝ)| +
            |((torusLatticeLift u + L • n).2 : ℝ)|))) = f n.1 * g n.2 := by
    intro n
    simp only [hf, hg, torusLatticeLift, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, ← Real.exp_add]
    congr 1
    have h1 : (L • n.1 : ℤ) = n.1 * L := by simp [mul_comm]
    have h2 : (L • n.2 : ℤ) = n.2 * L := by simp [mul_comm]
    rw [h1, h2]; ring
  have hfn : Summable fun n => ‖f n‖ := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hf] using hs1
  have hgn : Summable fun n => ‖g n‖ := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hg] using hs2
  simp only [hterm]
  refine ⟨summable_mul_of_summable_norm hfn hgn, ?_⟩
  rw [← tsum_mul_tsum_of_summable_norm hfn hgn]
  have h0f : 0 ≤ ∑' n, f n := tsum_nonneg fun n => (Real.exp_pos _).le
  have h0g : 0 ≤ ∑' n, g n := tsum_nonneg fun n => (Real.exp_pos _).le
  calc (∑' n, f n) * ∑' n, g n
      ≤ (40002 * Real.exp (-(α * zdist L u.1))) * (40002 * Real.exp (-(α * zdist L u.2))) :=
        mul_le_mul hb1 hb2 h0g (by positivity)
    _ = 40002 ^ 2 * Real.exp (-(α * zdist2 L u)) := by
        have : (zdist2 L u : ℝ) = (zdist L u.1 : ℝ) + (zdist L u.2 : ℝ) := by
          simp [zdist2]
        rw [this, mul_add, neg_add, Real.exp_add]; ring

end RBM
