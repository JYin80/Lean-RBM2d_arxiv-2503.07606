/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.AbelSum
import RBM2D.Propagator.ZeroMode
import RBM2D.Propagator.SymbolShiftAnnulus
import RBM2D.Propagator.GeomSum
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Shell phases, three-factor Leibniz rule and threefold summation by parts

Three ingredients used by the
dyadic-shell kernel estimates of Section 8.3:

* the two phase functions `shellPhase1`, `shellPhase2` and their scale-uniform forward
  differences on a shell (`shellPhase_fwdDiff_le`);
* the three-factor Leibniz rule for the third forward difference
  (`fwdDiff_three_mul_three`);
* threefold summation by parts against a plane wave (`norm_sum_mul_chr_le_fwdDiff_three`).
-/

namespace RBM

open Finset

/-! ## Three-factor Leibniz rule -/

private theorem shellSBP_dsucc {L : ℕ} [NeZero L] (e : Z2 L) (F : Z2 L → ℂ) (n : ℕ) (y : Z2 L) :
    (fwdDiff e)^[n + 1] F y = (fwdDiff e)^[n] F (y + e) - (fwdDiff e)^[n] F y := by
  rw [Function.iterate_succ_apply']
  rfl

private theorem shellSBP_d1 {L : ℕ} [NeZero L] (e : Z2 L) (F : Z2 L → ℂ) (y : Z2 L) :
    (fwdDiff e)^[1] F y = F (y + e) - F y := rfl

private theorem shellSBP_d2 {L : ℕ} [NeZero L] (e : Z2 L) (F : Z2 L → ℂ) (y : Z2 L) :
    (fwdDiff e)^[2] F y = F (y + e + e) - 2 * F (y + e) + F y := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, shellSBP_dsucc, shellSBP_d1, shellSBP_d1]
  ring

private theorem shellSBP_d3 {L : ℕ} [NeZero L] (e : Z2 L) (F : Z2 L → ℂ) (y : Z2 L) :
    (fwdDiff e)^[3] F y =
      F (y + e + e + e) - 3 * F (y + e + e) + 3 * F (y + e) - F y := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, shellSBP_dsucc, shellSBP_d2, shellSBP_d2]
  ring

theorem fwdDiff_three_mul_three :
  ∀ (L : ℕ) [NeZero L] (f g φ : Z2 L → ℂ) (e p : Z2 L),
    (fwdDiff e)^[3] (fun q => f q * g q * φ q) p =
      ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range (4 - a),
        ((Nat.choose 3 a * Nat.choose (3 - a) b : ℕ) : ℂ) *
          (fwdDiff e)^[a] f p * (fwdDiff e)^[b] g (p + a • e) *
          (fwdDiff e)^[3 - a - b] φ (p + (a + b) • e) := by
  intro L _ f g φ e p
  have hc : Nat.choose 3 2 = 3 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub, hc,
    Nat.reduceAdd, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right,
    Function.iterate_zero, id_eq, zero_nsmul, add_zero, one_smul, two_nsmul, three_nsmul,
    shellSBP_d1, shellSBP_d2, shellSBP_d3, add_assoc]
  push_cast
  ring

/-! ## Small helpers on `zdist` and `chr` -/

private theorem shellSBP_zdist_neg (L : ℕ) [NeZero L] (x : ZMod L) :
    zdist L (-x) = zdist L x := by
  have hx : x.val < L := ZMod.val_lt x
  by_cases h0 : x = 0
  · subst h0; simp
  · rw [zdist, zdist, ZMod.neg_val]
    simp only [h0, ite_false]
    omega

private theorem shellSBP_chr_add_left (L : ℕ) [NeZero L] (p e u : Z2 L) :
    chr L (p + e) u = chr L p u * chr L e u := by
  rw [chr, chr, chr, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

private theorem shellSBP_chr_sub_left (L : ℕ) [NeZero L] (p e u : Z2 L) :
    chr L (p - e) u * chr L e u = chr L p u := by
  rw [← shellSBP_chr_add_left, sub_add_cancel]

private theorem shellSBP_chr_neg (L : ℕ) [NeZero L] (p u : Z2 L) :
    chr L p (-u) = (chr L p u)⁻¹ := by
  rw [chr, chr, ← AddChar.map_neg_eq_inv]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

private theorem shellSBP_stdAddChar_ne_zero (L : ℕ) [NeZero L] (x : ZMod L) :
    (ZMod.stdAddChar x : ℂ) ≠ 0 := by
  rw [ZMod.stdAddChar_apply]
  exact ne_zero_of_norm_ne_zero (by rw [Circle.norm_coe]; exact one_ne_zero)

/-! ## Threefold summation by parts -/

private theorem shellSBP_step {L : ℕ} [NeZero L] (F g : Z2 L → ℂ) (e : Z2 L) (c : ℂ)
    (hg : ∀ p, g (p - e) = c * g p) :
    ∑ p : Z2 L, fwdDiff e F p * g p = (c - 1) * ∑ p : Z2 L, F p * g p := by
  have h := sum_fwdDiff_mul L F g e
  change ∑ p : Z2 L, (F (p + e) - F p) * g p = _
  rw [h, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hg]
  ring

private theorem shellSBP_step3 {L : ℕ} [NeZero L] (G g : Z2 L → ℂ) (e : Z2 L) (c : ℂ)
    (hg : ∀ p, g (p - e) = c * g p) :
    ∑ p : Z2 L, (fwdDiff e)^[3] G p * g p = (c - 1) ^ 3 * ∑ p : Z2 L, G p * g p := by
  have h3 : (fwdDiff e)^[3] G = fwdDiff e ((fwdDiff e)^[2] G) :=
    Function.iterate_succ_apply' _ _ _
  have h2 : (fwdDiff e)^[2] G = fwdDiff e ((fwdDiff e)^[1] G) :=
    Function.iterate_succ_apply' _ _ _
  have h1 : (fwdDiff e)^[1] G = fwdDiff e G := rfl
  rw [h3, shellSBP_step _ _ e c hg]
  rw [h2, shellSBP_step _ _ e c hg]
  rw [h1, shellSBP_step _ _ e c hg]
  ring

private theorem shellSBP_sbp_dir {L : ℕ} [NeZero L] (G : Z2 L → ℂ) (e u : Z2 L)
    (x : ZMod L) (hx0 : x ≠ 0)
    (hg : ∀ p, chr L (p - e) u = ZMod.stdAddChar (-x) * chr L p u) :
    ‖∑ p : Z2 L, G p * chr L p u‖
      ≤ (∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖) * ((L : ℝ) / (4 * (zdist L x : ℝ))) ^ 3 := by
  have hz : 0 < (zdist L x : ℝ) := by
    have : zdist L x ≠ 0 := fun h => hx0 ((zdist_eq_zero_iff L).mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hLpos := cast_L_pos L
  set a : ℝ := 4 * (zdist L x : ℝ) / (L : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have hlow : a ≤ ‖(ZMod.stdAddChar (-x) : ℂ) - 1‖ := by
    have := zdist_le_norm_stdAddChar_sub_one L (-x)
    rwa [shellSBP_zdist_neg] at this
  have hsum := shellSBP_step3 G (fun p => chr L p u) e (ZMod.stdAddChar (-x)) hg
  set A := ‖∑ p : Z2 L, G p * chr L p u‖ with hA
  set S := ∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖ with hS
  have hnorm : ‖∑ p : Z2 L, (fwdDiff e)^[3] G p * chr L p u‖ ≤ S := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_mul, norm_chr, mul_one]
  rw [hsum, norm_mul, norm_pow] at hnorm
  have hA0 : 0 ≤ A := norm_nonneg _
  have hpow : a ^ 3 ≤ ‖(ZMod.stdAddChar (-x) : ℂ) - 1‖ ^ 3 :=
    pow_le_pow_left₀ ha.le hlow 3
  have hkey : A * a ^ 3 ≤ S := by
    calc A * a ^ 3 ≤ A * ‖(ZMod.stdAddChar (-x) : ℂ) - 1‖ ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hA0
      _ = ‖(ZMod.stdAddChar (-x) : ℂ) - 1‖ ^ 3 * A := by ring
      _ ≤ S := hnorm
  have hinv : (L : ℝ) / (4 * (zdist L x : ℝ)) = a⁻¹ := by
    rw [ha_def, inv_div]
  rw [hinv, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos ha 3)]
  exact hkey

theorem norm_sum_mul_chr_le_fwdDiff_three :
  ∀ (L : ℕ) [NeZero L] (G : Z2 L → ℂ) (u : Z2 L),
    (u.1 ≠ 0 →
      ‖∑ p : Z2 L, G p * chr L p u‖
        ≤ (∑ p : Z2 L, ‖(fwdDiff ((1, 0) : Z2 L))^[3] G p‖) *
            ((L : ℝ) / (4 * (zdist L u.1 : ℝ))) ^ 3)
    ∧
    (u.2 ≠ 0 →
      ‖∑ p : Z2 L, G p * chr L p u‖
        ≤ (∑ p : Z2 L, ‖(fwdDiff ((0, 1) : Z2 L))^[3] G p‖) *
            ((L : ℝ) / (4 * (zdist L u.2 : ℝ))) ^ 3) := by
  intro L _ G u
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · refine shellSBP_sbp_dir G (1, 0) u u.1 hu fun p => ?_
    have h := shellSBP_chr_sub_left L p (1, 0) u
    have he : chr L (1, 0) u = ZMod.stdAddChar u.1 := by simp [chr]
    rw [he] at h
    have hne := shellSBP_stdAddChar_ne_zero L u.1
    rw [AddChar.map_neg_eq_inv]
    field_simp
    exact h
  · refine shellSBP_sbp_dir G (0, 1) u u.2 hu fun p => ?_
    have h := shellSBP_chr_sub_left L p (0, 1) u
    have he : chr L (0, 1) u = ZMod.stdAddChar u.2 := by simp [chr]
    rw [he] at h
    have hne := shellSBP_stdAddChar_ne_zero L u.2
    rw [AddChar.map_neg_eq_inv]
    field_simp
    exact h

/-! ## Shell phases -/

/-- The first-difference phase `1 - e_p(-s)`. -/
noncomputable def shellPhase1 (L : ℕ) [NeZero L] (s p : Z2 L) : ℂ :=
  1 - chr L p (-s)

/-- The second-difference phase `2 - e_p(s) - e_p(-s)`. -/
noncomputable def shellPhase2 (L : ℕ) [NeZero L] (s p : Z2 L) : ℂ :=
  2 - chr L p s - chr L p (-s)

private theorem shellSBP_iter {L : ℕ} [NeZero L] (e : Z2 L) (a α β c₁ c₂ : ℂ)
    (χ₁ χ₂ : Z2 L → ℂ) (h1 : ∀ p, χ₁ (p + e) = c₁ * χ₁ p)
    (h2 : ∀ p, χ₂ (p + e) = c₂ * χ₂ p) (k : ℕ) :
    (fwdDiff e)^[k + 1] (fun p => a + α * χ₁ p + β * χ₂ p) =
      fun p => α * ((c₁ - 1) ^ (k + 1) * χ₁ p) + β * ((c₂ - 1) ^ (k + 1) * χ₂ p) := by
  induction k with
  | zero =>
    funext p
    simp only [zero_add, Function.iterate_one, fwdDiff, h1, h2, pow_one]
    ring
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext p
    simp only [fwdDiff, h1, h2]
    ring

private theorem shellSBP_lift (L : ℕ) [NeZero L] (x : ZMod L) :
    ∃ m : ℤ, (m : ZMod L) = x ∧ |(m : ℝ)| = (zdist L x : ℝ) := by
  have hx : x.val < L := ZMod.val_lt x
  by_cases h : x.val ≤ L - x.val
  · refine ⟨(x.val : ℤ), by simp, ?_⟩
    have hz : zdist L x = x.val := by simp only [zdist]; omega
    rw [hz, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
  · refine ⟨(x.val : ℤ) - L, ?_, ?_⟩
    · push_cast
      simp
    · have hz : zdist L x = L - x.val := by simp only [zdist]; omega
      rw [hz, Nat.cast_sub hx.le]
      push_cast
      rw [abs_sub_comm, abs_of_nonneg]
      have : (x.val : ℝ) ≤ (L : ℝ) := by exact_mod_cast hx.le
      linarith

private theorem shellSBP_angle (L : ℕ) [NeZero L] (p u : Z2 L) :
    ∃ θ : ℝ, chr L p u = Complex.exp (Complex.I * θ) ∧
      |θ| ≤ pstar L p.1 * (zdist L u.1 : ℝ) + pstar L p.2 * (zdist L u.2 : ℝ) := by
  obtain ⟨m1, hm1, hm1'⟩ := shellSBP_lift L p.1
  obtain ⟨m2, hm2, hm2'⟩ := shellSBP_lift L p.2
  obtain ⟨n1, hn1, hn1'⟩ := shellSBP_lift L u.1
  obtain ⟨n2, hn2, hn2'⟩ := shellSBP_lift L u.2
  have hL := cast_L_pos L
  refine ⟨2 * Real.pi * ((m1 * n1 + m2 * n2 : ℤ) : ℝ) / L, ?_, ?_⟩
  · have hchr : p.1 * u.1 + p.2 * u.2 = ((m1 * n1 + m2 * n2 : ℤ) : ZMod L) := by
      push_cast
      rw [hm1, hm2, hn1, hn2]
    rw [chr, hchr, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  · have hcast : ((m1 * n1 + m2 * n2 : ℤ) : ℝ) = (m1 : ℝ) * n1 + (m2 : ℝ) * n2 := by
      push_cast; ring
    rw [hcast, abs_div, abs_mul, abs_of_pos Real.two_pi_pos, abs_of_pos hL, pstar, pstar,
      ← hm1', ← hm2', ← hn1', ← hn2']
    have habs := abs_add_le ((m1 : ℝ) * n1) ((m2 : ℝ) * n2)
    rw [abs_mul, abs_mul] at habs
    have hpi := Real.two_pi_pos
    calc 2 * Real.pi * |(m1 : ℝ) * n1 + (m2 : ℝ) * n2| / L
        ≤ 2 * Real.pi * (|(m1 : ℝ)| * |(n1 : ℝ)| + |(m2 : ℝ)| * |(n2 : ℝ)|) / L := by
          gcongr
      _ = _ := by ring

private theorem shellSBP_angle1 (L : ℕ) [NeZero L] (c : ZMod L) :
    ∃ α : ℝ, (ZMod.stdAddChar c : ℂ) = Complex.exp (Complex.I * α) ∧
      |α| ≤ symbolGridStep L * (zdist L c : ℝ) := by
  obtain ⟨m, hm, hm'⟩ := shellSBP_lift L c
  have hL := cast_L_pos L
  refine ⟨2 * Real.pi * (m : ℝ) / L, ?_, ?_⟩
  · rw [← hm, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  · rw [abs_div, abs_mul, abs_of_pos Real.two_pi_pos, abs_of_pos hL, hm', symbolGridStep]
    ring_nf
    exact le_refl _

private theorem shellSBP_char_sub_one_le (L : ℕ) [NeZero L] (c : ZMod L) :
    ‖(ZMod.stdAddChar c : ℂ) - 1‖ ≤ symbolGridStep L * (zdist L c : ℝ) := by
  have h := norm_stdAddChar_sub_one_le_zdist L c
  rw [symbolGridStep, ← mul_div_right_comm]
  exact h

private theorem shellSBP_edir (L : ℕ) [NeZero L] (e : Z2 L)
    (he : e = (1, 0) ∨ e = (0, 1)) (s : Z2 L) :
    ∃ c : ZMod L, chr L e s = ZMod.stdAddChar c ∧ chr L e (-s) = ZMod.stdAddChar (-c) ∧
      zdist L c ≤ zdist2 L s := by
  rcases he with rfl | rfl
  · refine ⟨s.1, by simp [chr], by simp [chr], ?_⟩
    simp only [zdist2]
    omega
  · refine ⟨s.2, by simp [chr], by simp [chr], ?_⟩
    simp only [zdist2]
    omega

private theorem shellSBP_phase2_eq (τ : ℝ) :
    2 - Complex.exp (Complex.I * τ) - (Complex.exp (Complex.I * τ))⁻¹
      = ((2 - 2 * Real.cos τ : ℝ) : ℂ) := by
  have h := Complex.two_cos (x := (τ : ℂ))
  rw [neg_mul] at h
  rw [← Complex.exp_neg, mul_comm Complex.I, sub_sub]
  push_cast
  rw [h]

private theorem shellSBP_conv1 (h r S : ℝ) (hr : 0 < r) (hh : 0 ≤ h) (hS : 0 ≤ S)
    (hrS : r * S ≤ 1) (k : ℕ) (hk : k ≠ 0) : (h * S) ^ k ≤ (h / r) ^ k * (r * S) := by
  have hpow : (h * S) ^ k = (h / r) ^ k * (r * S) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hpow]
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg hr.le hS) hrS hk)
    (pow_nonneg (div_nonneg hh hr.le) k)

private theorem shellSBP_conv2 (h r S : ℝ) (hr : 0 < r) (hh : 0 ≤ h) (hS : 0 ≤ S)
    (hrS : r * S ≤ 1) (k : ℕ) (hk : 2 ≤ k) : (h * S) ^ k ≤ (h / r) ^ k * (r * S) ^ 2 := by
  have hpow : (h * S) ^ k = (h / r) ^ k * (r * S) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hpow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (mul_nonneg hr.le hS) hrS hk)
    (pow_nonneg (div_nonneg hh hr.le) k)

private theorem shellSBP_iter_bounds (L : ℕ) [NeZero L] (e : Z2 L)
    (he : e = (1, 0) ∨ e = (0, 1)) (s p : Z2 L) (h S : ℝ) (hh : h = symbolGridStep L)
    (hS : S = (zdist2 L s : ℝ)) (m : ℕ) :
    ‖(fwdDiff e)^[m + 1] (shellPhase1 L s) p‖ ≤ (h * S) ^ (m + 1) ∧
      ‖(fwdDiff e)^[m + 1] (shellPhase2 L s) p‖ ≤ 2 * (h * S) ^ (m + 1) := by
  have hL := cast_L_pos L
  have hh0 : 0 < h := by rw [hh, symbolGridStep]; positivity
  obtain ⟨c, hc1, hc2, hcz⟩ := shellSBP_edir L e he s
  have hcS : (zdist L c : ℝ) ≤ S := by rw [hS]; exact_mod_cast hcz
  have hcS' : h * (zdist L c : ℝ) ≤ h * S := mul_le_mul_of_nonneg_left hcS hh0.le
  have hωp : ‖chr L e s - 1‖ ≤ h * S := by
    rw [hc1, hh]
    rw [hh] at hcS'
    exact (shellSBP_char_sub_one_le L c).trans hcS'
  have hωm : ‖chr L e (-s) - 1‖ ≤ h * S := by
    rw [hc2, hh]
    rw [hh] at hcS'
    have := shellSBP_char_sub_one_le L (-c)
    rw [shellSBP_zdist_neg] at this
    exact this.trans hcS'
  have hadd : ∀ u : Z2 L, ∀ q : Z2 L, chr L (q + e) u = chr L e u * chr L q u := by
    intro u q
    rw [shellSBP_chr_add_left, mul_comm]
  have hφ1 : (fwdDiff e)^[m + 1] (shellPhase1 L s) =
      fun q => (-1 : ℂ) * ((chr L e (-s) - 1) ^ (m + 1) * chr L q (-s)) +
        0 * ((chr L e (-s) - 1) ^ (m + 1) * chr L q (-s)) := by
    have := shellSBP_iter e 1 (-1) 0 (chr L e (-s)) (chr L e (-s))
      (fun q => chr L q (-s)) (fun q => chr L q (-s)) (hadd (-s)) (hadd (-s)) m
    rw [← this]
    congr 1
    funext q
    simp only [shellPhase1]
    ring
  have hφ2 : (fwdDiff e)^[m + 1] (shellPhase2 L s) =
      fun q => (-1 : ℂ) * ((chr L e s - 1) ^ (m + 1) * chr L q s) +
        (-1) * ((chr L e (-s) - 1) ^ (m + 1) * chr L q (-s)) := by
    have := shellSBP_iter e 2 (-1) (-1) (chr L e s) (chr L e (-s))
      (fun q => chr L q s) (fun q => chr L q (-s)) (hadd s) (hadd (-s)) m
    rw [← this]
    congr 1
    funext q
    simp only [shellPhase2]
    ring
  refine ⟨?_, ?_⟩
  · rw [hφ1]
    simp only [zero_mul, add_zero, neg_one_mul, norm_neg, norm_mul, norm_pow, norm_chr, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) hωm _
  · rw [hφ2]
    have h₁ : ‖chr L e s - 1‖ ^ (m + 1) ≤ (h * S) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hωp _
    have h₂ : ‖chr L e (-s) - 1‖ ^ (m + 1) ≤ (h * S) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hωm _
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_neg, norm_one, one_mul, norm_pow, norm_chr, mul_one]
    linarith

private theorem shellSBP_theta (L : ℕ) [NeZero L] (s p : Z2 L) (r S : ℝ) (hr : 0 < r)
    (hS : S = (zdist2 L s : ℝ)) (hp : pstar2 L p ≤ (33 / 5 * r) ^ 2) (θ : ℝ)
    (hθ : |θ| ≤ pstar L p.1 * (zdist L s.1 : ℝ) + pstar L p.2 * (zdist L s.2 : ℝ)) :
    |θ| ≤ 33 / 5 * (r * S) := by
  have hSsplit : S = (zdist L s.1 : ℝ) + (zdist L s.2 : ℝ) := by
    rw [hS, zdist2]; push_cast; ring
  have hp1 := pstar_nonneg L p.1
  have hp2 := pstar_nonneg L p.2
  simp only [pstar2] at hp
  have hq1 : pstar L p.1 ≤ 33 / 5 * r := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [sq_nonneg (pstar L p.2)]
  have hq2 : pstar L p.2 ≤ 33 / 5 * r := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [sq_nonneg (pstar L p.1)]
  calc |θ| ≤ pstar L p.1 * (zdist L s.1 : ℝ) + pstar L p.2 * (zdist L s.2 : ℝ) := hθ
    _ ≤ 33 / 5 * r * (zdist L s.1 : ℝ) + 33 / 5 * r * (zdist L s.2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right hq2 (Nat.cast_nonneg _))
    _ = 33 / 5 * (r * S) := by rw [hSsplit]; ring

private theorem shellSBP_k0_1 (L : ℕ) [NeZero L] (s p : Z2 L) (r S : ℝ) (hr : 0 < r)
    (hS : S = (zdist2 L s : ℝ)) (hp : pstar2 L p ≤ (33 / 5 * r) ^ 2) :
    ‖shellPhase1 L s p‖ ≤ 33 / 5 * (r * S) := by
  obtain ⟨θ, hθ, hθb⟩ := shellSBP_angle L p (-s)
  simp only [Prod.fst_neg, Prod.snd_neg, shellSBP_zdist_neg] at hθb
  have hb := shellSBP_theta L s p r S hr hS hp θ hθb
  have : ‖shellPhase1 L s p‖ = ‖Complex.exp (Complex.I * θ) - 1‖ := by
    rw [shellPhase1, hθ, norm_sub_rev]
  rw [this]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (by rw [Real.norm_eq_abs]; exact hb)

private theorem shellSBP_k0_2 (L : ℕ) [NeZero L] (s p : Z2 L) (r S : ℝ) (hr : 0 < r)
    (hS : S = (zdist2 L s : ℝ)) (hp : pstar2 L p ≤ (33 / 5 * r) ^ 2) :
    ‖shellPhase2 L s p‖ ≤ 1089 / 25 * (r * S) ^ 2 := by
  obtain ⟨θ, hθ, hθb⟩ := shellSBP_angle L p s
  have hb := shellSBP_theta L s p r S hr hS hp θ hθb
  have hφ : shellPhase2 L s p = ((2 - 2 * Real.cos θ : ℝ) : ℂ) := by
    rw [shellPhase2, shellSBP_chr_neg, hθ, shellSBP_phase2_eq]
  rw [hφ, Complex.norm_real, Real.norm_eq_abs]
  have hc := one_sub_cos_le_sq θ
  have hc0 := Real.cos_le_one θ
  rw [abs_of_nonneg (by linarith)]
  have hsq : θ ^ 2 ≤ (33 / 5 * (r * S)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith

private theorem shellSBP_k1_2 (L : ℕ) [NeZero L] (e : Z2 L) (he : e = (1, 0) ∨ e = (0, 1))
    (s p : Z2 L) (h r S : ℝ) (hh : h = symbolGridStep L) (hr : 0 < r)
    (h10 : 10 * h ≤ r) (hS : S = (zdist2 L s : ℝ)) (hp : pstar2 L p ≤ (33 / 5 * r) ^ 2) :
    ‖(fwdDiff e)^[1] (shellPhase2 L s) p‖ ≤ 133 / 10 * (h / r) * (r * S) ^ 2 := by
  have hL := cast_L_pos L
  have hh0 : 0 < h := by rw [hh, symbolGridStep]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
  obtain ⟨c, hc1, hc2, hcz⟩ := shellSBP_edir L e he s
  have hcS : (zdist L c : ℝ) ≤ S := by rw [hS]; exact_mod_cast hcz
  have hcS' : h * (zdist L c : ℝ) ≤ h * S := mul_le_mul_of_nonneg_left hcS hh0.le
  obtain ⟨θ, hθ, hθb⟩ := shellSBP_angle L p s
  have hb := shellSBP_theta L s p r S hr hS hp θ hθb
  obtain ⟨α, hα, hαb⟩ := shellSBP_angle1 L c
  have hαb' : |α| ≤ h * S := by rw [hh] at hcS' ⊢; exact hαb.trans hcS'
  have hφ : ∀ (q : Z2 L) (τ : ℝ), chr L q s = Complex.exp (Complex.I * τ) →
      shellPhase2 L s q = ((2 - 2 * Real.cos τ : ℝ) : ℂ) := by
    intro q τ hτ
    rw [shellPhase2, shellSBP_chr_neg, hτ, shellSBP_phase2_eq]
  have hpe : chr L (p + e) s = Complex.exp (Complex.I * ((θ + α : ℝ) : ℂ)) := by
    rw [shellSBP_chr_add_left, hθ, hc1, hα, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hd : (fwdDiff e)^[1] (shellPhase2 L s) p =
      ((2 * Real.cos θ - 2 * Real.cos (θ + α) : ℝ) : ℂ) := by
    change shellPhase2 L s (p + e) - shellPhase2 L s p = _
    rw [hφ _ _ hpe, hφ _ _ hθ]
    push_cast
    ring
  rw [hd, Complex.norm_real, Real.norm_eq_abs]
  have hcos : 2 * Real.cos θ - 2 * Real.cos (θ + α) =
      4 * (Real.sin (θ + α / 2) * Real.sin (α / 2)) := by
    have := Real.cos_sub_cos θ (θ + α)
    have e1 : (θ + (θ + α)) / 2 = θ + α / 2 := by ring
    have e2 : (θ - (θ + α)) / 2 = -(α / 2) := by ring
    rw [e1, e2, Real.sin_neg] at this
    linarith
  rw [hcos, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_mul]
  have hs1 : |Real.sin (θ + α / 2)| ≤ |θ| + |α| / 2 := by
    refine Real.abs_sin_le_abs.trans ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_two]
  have hs2 : |Real.sin (α / 2)| ≤ |α| / 2 := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_div, abs_two]
  have hA0 := abs_nonneg α
  have hT0 := abs_nonneg θ
  have hprod : |Real.sin (θ + α / 2)| * |Real.sin (α / 2)| ≤ (|θ| + |α| / 2) * (|α| / 2) :=
    mul_le_mul hs1 hs2 (abs_nonneg _) (by positivity)
  have hkey : 4 * (|Real.sin (θ + α / 2)| * |Real.sin (α / 2)|) ≤ |α| * (2 * |θ| + |α|) := by
    nlinarith
  have hstep : |α| * (2 * |θ| + |α|) ≤ (h * S) * (2 * (33 / 5 * (r * S)) + h * S) := by
    have hb' : 2 * |θ| + |α| ≤ 2 * (33 / 5 * (r * S)) + h * S := by linarith
    exact mul_le_mul hαb' hb' (by positivity) (by positivity)
  have hfin : (h * S) * (2 * (33 / 5 * (r * S)) + h * S) ≤ 133 / 10 * (h / r) * (r * S) ^ 2 := by
    have hdiv : 133 / 10 * (h / r) * (r * S) ^ 2 = 133 / 10 * h * r * S ^ 2 := by
      field_simp
    rw [hdiv]
    have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
    have : h * S * (2 * (33 / 5 * (r * S)) + h * S) = h * S ^ 2 * (66 / 5 * r + h) := by ring
    rw [this]
    nlinarith [mul_nonneg hh0.le hS2]
  exact hkey.trans (hstep.trans hfin)

theorem shellPhase_fwdDiff_le :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) →
    ∀ (j : ℕ) (s p : Z2 L) (k : Fin 4),
      10 * symbolGridStep L ≤ dyad j →
      dyad j * (zdist2 L s : ℝ) ≤ 1 →
      pstar2 L p ≤ (33 / 5 * dyad j) ^ 2 →
      ‖(fwdDiff e)^[k] (shellPhase1 L s) p‖
          ≤ (![33 / 5, 1, 1, 1] k : ℝ) * (symbolGridStep L / dyad j) ^ (k : ℕ) *
              (dyad j * (zdist2 L s : ℝ))
        ∧
      ‖(fwdDiff e)^[k] (shellPhase2 L s) p‖
          ≤ (![1089 / 25, 133 / 10, 2, 2] k : ℝ) *
              (symbolGridStep L / dyad j) ^ (k : ℕ) *
              (dyad j * (zdist2 L s : ℝ)) ^ 2 := by
  intro L _ _ e he j s p k h10 hrS hp
  have hL := cast_L_pos L
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = symbolGridStep L := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = dyad j := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (zdist2 L s : ℝ) := ⟨_, rfl⟩
  rw [← hh, ← hr] at h10
  rw [← hr] at hp
  rw [← hr, ← hS] at hrS
  rw [← hh, ← hr, ← hS]
  have hh0 : 0 < h := by rw [hh, symbolGridStep]; positivity
  have hr0 : 0 < r := by rw [hr]; exact dyad_pos j
  have hS0 : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
  have c1 : ∀ k : ℕ, 1 ≤ k → ‖(fwdDiff e)^[k] (shellPhase1 L s) p‖ ≤
      1 * (h / r) ^ k * (r * S) := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact le_of_le_of_eq ((shellSBP_iter_bounds L e he s p h S hh hS m).1.trans
      (shellSBP_conv1 h r S hr0 hh0.le hS0 hrS (m + 1) (Nat.succ_ne_zero m))) (by ring)
  have c2 : ∀ k : ℕ, 2 ≤ k → ‖(fwdDiff e)^[k] (shellPhase2 L s) p‖ ≤
      2 * (h / r) ^ k * (r * S) ^ 2 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact le_of_le_of_eq ((shellSBP_iter_bounds L e he s p h S hh hS m).2.trans
      (mul_le_mul_of_nonneg_left
        (shellSBP_conv2 h r S hr0 hh0.le hS0 hrS (m + 1) hk) (by norm_num)))
      (by ring)
  have h01 := shellSBP_k0_1 L s p r S hr0 hS hp
  have h02 := shellSBP_k0_2 L s p r S hr0 hS hp
  have h12 := shellSBP_k1_2 L e he s p h r S hh hr0 h10 hS hp
  fin_cases k
  · exact ⟨le_of_le_of_eq h01 (by simp), le_of_le_of_eq h02 (by simp)⟩
  · exact ⟨c1 1 le_rfl, le_of_le_of_eq h12 (by simp)⟩
  · exact ⟨c1 2 (by norm_num), c2 2 le_rfl⟩
  · exact ⟨c1 3 (by norm_num), c2 3 (by norm_num)⟩

end RBM
