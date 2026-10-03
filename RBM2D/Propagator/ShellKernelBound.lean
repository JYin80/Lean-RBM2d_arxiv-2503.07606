/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ShellCutoff
import RBM2D.Propagator.ShellCutoffDiff
import RBM2D.Propagator.ShellSBP
import RBM2D.Propagator.InvSymbolDiff
import RBM2D.Propagator.Decay
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Per-shell kernel bounds on small and large shells

For the shell kernel
`K_j(u) = L⁻² ∑_p χ_j(p) (1 - ξŜ(p))⁻¹ e_p(u)` (`shellKernel`), with `r = 2⁻ʲ`,
`ρ² = κ² + r²`, `d = |u|_L`, `|s| = |s|_L`:

* `‖K_j(u)‖ ≲ r²/ρ² (1 + r d)⁻³`,
* `‖K_j(u) - K_j(u - s)‖ ≲ |s| r³/ρ² (1 + r d)⁻³`,
* `‖2K_j(u) - K_j(u - s) - K_j(u + s)‖ ≲ |s|² r⁴/ρ² (1 + r d)⁻³`,

on small shells `r L ≤ 64` (no condition on `s`) and on large shells `r L > 64`
(differences under `r |s| ≤ 1`).  Small shells and the near region `r d ≤ 1` use the
trivial bound; the far region `r d > 1` of a large shell uses threefold summation by
parts, the three-factor Leibniz rule and the difference bounds of the cutoff (`ShellCutoffDiff`),
the reciprocal symbol
(`InvSymbolDiff`) and the shell phases (`ShellSBP`).

This is a discrete special form of `(eq_dyadic)` of Section 8.3 for the shell kernels
(finite differences in the kernel argument, decay exponent `M = 3`), not the paper's
general statement.
-/

namespace RBM

open Finset

/-! ## Small helpers on `zdist`, `chr` and angles -/

private theorem shellKernelBound_zdist_neg (L : ℕ) [NeZero L] (x : ZMod L) :
    zdist L (-x) = zdist L x := by
  have hx : x.val < L := ZMod.val_lt x
  by_cases h0 : x = 0
  · subst h0; simp
  · rw [zdist, zdist, ZMod.neg_val]
    simp only [h0, ite_false]
    omega

private theorem shellKernelBound_chr_add (L : ℕ) [NeZero L] (p u v : Z2 L) :
    chr L p (u + v) = chr L p u * chr L p v := by
  rw [chr, chr, chr, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

private theorem shellKernelBound_chr_neg (L : ℕ) [NeZero L] (p u : Z2 L) :
    chr L p (-u) = (chr L p u)⁻¹ := by
  rw [chr, chr, ← AddChar.map_neg_eq_inv]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

private theorem shellKernelBound_lift (L : ℕ) [NeZero L] (x : ZMod L) :
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

private theorem shellKernelBound_angle (L : ℕ) [NeZero L] (p u : Z2 L) :
    ∃ θ : ℝ, chr L p u = Complex.exp (Complex.I * θ) ∧
      |θ| ≤ pstar L p.1 * (zdist L u.1 : ℝ) + pstar L p.2 * (zdist L u.2 : ℝ) := by
  obtain ⟨m1, hm1, hm1'⟩ := shellKernelBound_lift L p.1
  obtain ⟨m2, hm2, hm2'⟩ := shellKernelBound_lift L p.2
  obtain ⟨n1, hn1, hn1'⟩ := shellKernelBound_lift L u.1
  obtain ⟨n2, hn2, hn2'⟩ := shellKernelBound_lift L u.2
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

private theorem shellKernelBound_phase2_eq (τ : ℝ) :
    2 - Complex.exp (Complex.I * τ) - (Complex.exp (Complex.I * τ))⁻¹
      = ((2 - 2 * Real.cos τ : ℝ) : ℂ) := by
  have h := Complex.two_cos (x := (τ : ℂ))
  rw [neg_mul] at h
  rw [← Complex.exp_neg, mul_comm Complex.I, sub_sub]
  push_cast
  rw [h]

/-- `|θ| ≤ R |s|` when `|p|_* < R`. -/
private theorem shellKernelBound_theta (L : ℕ) [NeZero L] (s p : Z2 L) (R : ℝ) (hR : 0 ≤ R)
    (hp : pstar2 L p < R ^ 2) (θ : ℝ)
    (hθ : |θ| ≤ pstar L p.1 * (zdist L s.1 : ℝ) + pstar L p.2 * (zdist L s.2 : ℝ)) :
    |θ| ≤ R * (zdist2 L s : ℝ) := by
  have hp1 := pstar_nonneg L p.1
  have hp2 := pstar_nonneg L p.2
  simp only [pstar2] at hp
  have hq1 : pstar L p.1 ≤ R := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [sq_nonneg (pstar L p.2)]
  have hq2 : pstar L p.2 ≤ R := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [sq_nonneg (pstar L p.1)]
  have hs : (zdist2 L s : ℝ) = (zdist L s.1 : ℝ) + (zdist L s.2 : ℝ) := by
    rw [zdist2]; push_cast; ring
  rw [hs]
  calc |θ| ≤ pstar L p.1 * (zdist L s.1 : ℝ) + pstar L p.2 * (zdist L s.2 : ℝ) := hθ
    _ ≤ R * (zdist L s.1 : ℝ) + R * (zdist L s.2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right hq2 (Nat.cast_nonneg _))
    _ = _ := by ring

/-- Pointwise first phase bound, valid for every `s`. -/
private theorem shellKernelBound_phase1_le (L : ℕ) [NeZero L] (s p : Z2 L) (R : ℝ)
    (hR : 0 ≤ R) (hp : pstar2 L p < R ^ 2) :
    ‖shellPhase1 L s p‖ ≤ R * (zdist2 L s : ℝ) := by
  obtain ⟨θ, hθ, hθb⟩ := shellKernelBound_angle L p (-s)
  simp only [Prod.fst_neg, Prod.snd_neg, shellKernelBound_zdist_neg] at hθb
  have hb := shellKernelBound_theta L s p R hR hp θ hθb
  have : ‖shellPhase1 L s p‖ = ‖Complex.exp (Complex.I * θ) - 1‖ := by
    rw [shellPhase1, hθ, norm_sub_rev]
  rw [this]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (by rw [Real.norm_eq_abs]; exact hb)

/-- Pointwise second phase bound, valid for every `s`. -/
private theorem shellKernelBound_phase2_le (L : ℕ) [NeZero L] (s p : Z2 L) (R : ℝ)
    (hR : 0 ≤ R) (hp : pstar2 L p < R ^ 2) :
    ‖shellPhase2 L s p‖ ≤ (R * (zdist2 L s : ℝ)) ^ 2 := by
  obtain ⟨θ, hθ, hθb⟩ := shellKernelBound_angle L p s
  have hb := shellKernelBound_theta L s p R hR hp θ hθb
  have hφ : shellPhase2 L s p = ((2 - 2 * Real.cos θ : ℝ) : ℂ) := by
    rw [shellPhase2, shellKernelBound_chr_neg, hθ, shellKernelBound_phase2_eq]
  rw [hφ, Complex.norm_real, Real.norm_eq_abs]
  have hc := one_sub_cos_le_sq θ
  have hc0 := Real.cos_le_one θ
  rw [abs_of_nonneg (by linarith)]
  have hsq : θ ^ 2 ≤ (R * (zdist2 L s : ℝ)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith

/-! ## The kernel sums -/

/-- `L⁻² ∑_p χ_j(p) m(p) φ(p) e_p(u)`. -/
private noncomputable def shellKernelBound_Q (L : ℕ) [NeZero L] (ξ : ℂ) (j : ℕ)
    (φ : Z2 L → ℂ) (u : Z2 L) : ℂ :=
  ((L : ℂ) ^ 2)⁻¹ *
    ∑ p : Z2 L, (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * φ p * chr L p u

private theorem shellKernelBound_Q_one (L : ℕ) [NeZero L] (ξ : ℂ) (j : ℕ) (u : Z2 L) :
    shellKernel L ξ j u = shellKernelBound_Q L ξ j (fun _ => 1) u := by
  simp only [shellKernel, shellKernelBound_Q, mul_one]

private theorem shellKernelBound_Q_diff1 (L : ℕ) [NeZero L] (ξ : ℂ) (j : ℕ) (u s : Z2 L) :
    shellKernel L ξ j u - shellKernel L ξ j (u - s) =
      shellKernelBound_Q L ξ j (shellPhase1 L s) u := by
  simp only [shellKernel, shellKernelBound_Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show u - s = u + -s from sub_eq_add_neg u s, shellKernelBound_chr_add, shellPhase1]
  ring

private theorem shellKernelBound_Q_diff2 (L : ℕ) [NeZero L] (ξ : ℂ) (j : ℕ) (u s : Z2 L) :
    2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s) =
      shellKernelBound_Q L ξ j (shellPhase2 L s) u := by
  simp only [shellKernel, shellKernelBound_Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show u - s = u + -s from sub_eq_add_neg u s, shellKernelBound_chr_add,
    shellKernelBound_chr_add, shellPhase2]
  ring

/-! ## The trivial bound -/

private theorem shellKernelBound_norm_m (L : ℕ) [NeZero L] {ξ : ℂ} (hξ : ‖ξ‖ < 1) (j : ℕ)
    (p : Z2 L) (hp : shellCutoff L j p ≠ 0) :
    ‖invSymbolMultiplier L ξ p‖ ≤ 112 / (kappa ξ ^ 2 + dyad j ^ 2) := by
  have h := norm_one_sub_mul_Shat_ge_pstar L hξ p
  have hs := (shellCutoff_support L j p hp).1
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hρ : 0 < kappa ξ ^ 2 + dyad j ^ 2 := by positivity
  have hc : 0 < 4 / (45 * Real.pi ^ 2) := by positivity
  have hlow : 4 / (45 * Real.pi ^ 2) * (kappa ξ ^ 2 + dyad j ^ 2) ≤ ‖1 - ξ * Shat L p‖ := by
    refine le_trans ?_ h
    apply mul_le_mul_of_nonneg_left _ hc.le
    nlinarith [sq_nonneg (dyad j)]
  rw [invSymbolMultiplier, norm_inv]
  calc ‖1 - ξ * Shat L p‖⁻¹ ≤ (4 / (45 * Real.pi ^ 2) * (kappa ξ ^ 2 + dyad j ^ 2))⁻¹ :=
        inv_anti₀ (by positivity) hlow
    _ = (45 * Real.pi ^ 2 / 4) / (kappa ξ ^ 2 + dyad j ^ 2) := by
        field_simp
    _ ≤ 112 / (kappa ξ ^ 2 + dyad j ^ 2) := by
        apply div_le_div_of_nonneg_right _ hρ.le
        nlinarith

private theorem shellKernelBound_trivial (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (j : ℕ) (φ : Z2 L → ℂ) (u : Z2 L) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p, shellCutoff L j p ≠ 0 → ‖φ p‖ ≤ B) :
    ‖shellKernelBound_Q L ξ j φ u‖
      ≤ 1008 * B * (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)) := by
  set S := Finset.univ.filter (fun p : Z2 L => shellCutoff L j p ≠ 0) with hSdef
  set ρ2 := kappa ξ ^ 2 + dyad j ^ 2 with hρ2
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hρ : 0 < ρ2 := by positivity
  have hLpos := cast_L_pos L
  have hM0 : 0 ≤ 112 / ρ2 * B := by positivity
  have hsum : ‖∑ p : Z2 L, (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * φ p *
      chr L p u‖ ≤ (S.card : ℝ) * (112 / ρ2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_filter_of_ne (p := fun p : Z2 L => shellCutoff L j p ≠ 0) ?_]
    · refine (Finset.sum_le_card_nsmul _ _ (112 / ρ2 * B) ?_).trans (by rw [nsmul_eq_mul])
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [norm_mul, norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := shellCutoff_mem_Icc L j p
      have h2 := shellKernelBound_norm_m L hξ j p hp
      have h3 := hB p hp
      have habs : |shellCutoff L j p| ≤ 1 := by rw [abs_of_nonneg h1.1]; exact h1.2
      calc |shellCutoff L j p| * ‖invSymbolMultiplier L ξ p‖ * ‖φ p‖
          ≤ 1 * (112 / ρ2) * B := by
            apply mul_le_mul (mul_le_mul habs h2 (norm_nonneg _) zero_le_one) h3
              (norm_nonneg _) (by positivity)
        _ = 112 / ρ2 * B := by ring
    · intro p _ hne
      contrapose! hne
      simp [hne]
  have hnorm : ‖shellKernelBound_Q L ξ j φ u‖ =
      ‖∑ p : Z2 L, (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * φ p *
        chr L p u‖ / (L : ℝ) ^ 2 := by
    rw [shellKernelBound_Q, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, inv_mul_eq_div]
  have hcard : (S.card : ℝ) / (L : ℝ) ^ 2 ≤ 9 * dyad j ^ 2 := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_div]; positivity
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hc1, hc2⟩ := shellCutoff_count L hL j
      have hrL := hc2 p hp
      have hc1' : (S.card : ℝ) ≤ (2 * dyad j * L + 1) ^ 2 := hc1
      have h3 : (2 * dyad j * L + 1) ^ 2 ≤ (3 * dyad j * L) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  rw [hnorm]
  calc _ ≤ (S.card : ℝ) * (112 / ρ2 * B) / (L : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsum (by positivity)
    _ = (S.card : ℝ) / (L : ℝ) ^ 2 * (112 / ρ2 * B) := by ring
    _ ≤ 9 * dyad j ^ 2 * (112 / ρ2 * B) := mul_le_mul_of_nonneg_right hcard hM0
    _ = 1008 * B * (dyad j ^ 2 / ρ2) := by ring

/-! ## Forward-difference helpers -/

private theorem shellKernelBound_iter_zero {L : ℕ} [NeZero L] (e : Z2 L) (F : Z2 L → ℂ) :
    ∀ (k : ℕ) (p : Z2 L), (∀ l, l ≤ k → F (p + l • e) = 0) → (fwdDiff e)^[k] F p = 0 := by
  intro k
  induction k with
  | zero => intro p h; simpa using h 0 le_rfl
  | succ k ih =>
    intro p h
    rw [Function.iterate_succ_apply']
    change (fwdDiff e)^[k] F (p + e) - (fwdDiff e)^[k] F p = 0
    rw [ih p (fun l hl => h l (by omega)), ih (p + e) (fun l hl => ?_), sub_zero]
    have := h (l + 1) (by omega)
    rwa [succ_nsmul', ← add_assoc] at this

private theorem shellKernelBound_iter_cast {L : ℕ} [NeZero L] (e : Z2 L) (f : Z2 L → ℝ) :
    ∀ (k : ℕ) (p : Z2 L),
      (fwdDiff e)^[k] (fun q => (f q : ℂ)) p = (((fwdDiff e)^[k] f p : ℝ) : ℂ) := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fwdDiff e)^[k] (fun q => (f q : ℂ)) (p + e) - (fwdDiff e)^[k] (fun q => (f q : ℂ)) p
      = (((fwdDiff e)^[k] f (p + e) - (fwdDiff e)^[k] f p : ℝ) : ℂ)
    rw [ih, ih]
    push_cast
    rfl

private theorem shellKernelBound_iter_one {L : ℕ} [NeZero L] (e : Z2 L) (k : ℕ) :
    (fwdDiff e)^[k + 1] (fun _ : Z2 L => (1 : ℂ)) = fun _ => 0 := by
  rw [Function.iterate_succ_apply, fwdDiff_const]
  exact Function.iterate_fixed (fwdDiff_const e (0 : ℂ)) k

/-- Cutoff difference constants `(1, 9, 44, 90061)`. -/
private noncomputable def shellKernelBound_cχ (a : ℕ) : ℝ :=
  if a = 0 then 1 else if a = 1 then 9 else if a = 2 then 44 else 90061

/-- Reciprocal-symbol difference constants `(112, 10⁴, 10⁶, 2·10⁸)`. -/
private noncomputable def shellKernelBound_cm (b : ℕ) : ℝ :=
  if b = 0 then 112 else if b = 1 then 10 ^ 4 else if b = 2 then 10 ^ 6 else 2 * 10 ^ 8

/-- The Leibniz constant `S_Φ = ∑ C(3,a) C(3-a,b) c_a c'_b Φ_{3-a-b}`. -/
private noncomputable def shellKernelBound_sum (Φ : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range 4, ∑ b ∈ range (4 - a),
    ((Nat.choose 3 a * Nat.choose (3 - a) b : ℕ) : ℝ) *
      shellKernelBound_cχ a * shellKernelBound_cm b * Φ (3 - a - b)

private theorem shellKernelBound_leib {L : ℕ} [NeZero L] (f g φ : Z2 L → ℂ) (e p : Z2 L)
    (A B C : ℕ → ℝ)
    (hA : ∀ a, a ≤ 3 → ‖(fwdDiff e)^[a] f p‖ ≤ A a)
    (hB : ∀ a b, a + b ≤ 3 → ‖(fwdDiff e)^[b] g (p + a • e)‖ ≤ B b)
    (hC : ∀ a b, a + b ≤ 3 →
      ‖(fwdDiff e)^[3 - a - b] φ (p + (a + b) • e)‖ ≤ C (3 - a - b)) :
    ‖(fwdDiff e)^[3] (fun q => f q * g q * φ q) p‖ ≤
      ∑ a ∈ range 4, ∑ b ∈ range (4 - a),
        ((Nat.choose 3 a * Nat.choose (3 - a) b : ℕ) : ℝ) * A a * B b * C (3 - a - b) := by
  rw [fwdDiff_three_mul_three]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  have ha' : a < 4 := Finset.mem_range.mp ha
  have hb' : b < 4 - a := Finset.mem_range.mp hb
  have h1 := hA a (by omega)
  have h2 := hB a b (by omega)
  have h3 := hC a b (by omega)
  have h1' := (norm_nonneg _).trans h1
  have h2' := (norm_nonneg _).trans h2
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  have hc : (0 : ℝ) ≤ ((Nat.choose 3 a * Nat.choose (3 - a) b : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
    (mul_nonneg hc h1')) h3 (norm_nonneg _) (mul_nonneg (mul_nonneg hc h1') h2')

private theorem shellKernelBound_sum_factor (Φ : ℕ → ℝ) (t Y X : ℝ) :
    ∑ a ∈ range 4, ∑ b ∈ range (4 - a),
        ((Nat.choose 3 a * Nat.choose (3 - a) b : ℕ) : ℝ) * (shellKernelBound_cχ a * t ^ a) *
          (shellKernelBound_cm b * t ^ b * Y) * (Φ (3 - a - b) * t ^ (3 - a - b) * X)
      = shellKernelBound_sum Φ * (t ^ 3 * Y * X) := by
  rw [shellKernelBound_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b hb => ?_
  have ha' : a < 4 := Finset.mem_range.mp ha
  have hb' : b < 4 - a := Finset.mem_range.mp hb
  have ht : t ^ 3 = t ^ a * t ^ b * t ^ (3 - a - b) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [ht]
  ring

/-! ## Summation by parts on a large shell -/

/-- `∑_p |Δ³_e (χ m φ)(p)| ≤ 17 (rL)² S_Φ (h/r)³ X / ρ²` on a large shell. -/
private theorem shellKernelBound_sum_d3 (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (j : ℕ) (hj : 64 < dyad j * L) (e : Z2 L) (he : e = (1, 0) ∨ e = (0, 1))
    (φ : Z2 L → ℂ) (Φ : ℕ → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hΦ : ∀ q : Z2 L, pstar2 L q ≤ (33 / 5 * dyad j) ^ 2 → ∀ c, c ≤ 3 →
      ‖(fwdDiff e)^[c] φ q‖ ≤ Φ c * (symbolGridStep L / dyad j) ^ c * X)
    (SΦ : ℝ) (hS0 : 0 ≤ SΦ) (hS : shellKernelBound_sum Φ ≤ SΦ) :
    ∑ p : Z2 L, ‖(fwdDiff e)^[3]
        (fun q => (shellCutoff L j q : ℂ) * invSymbolMultiplier L ξ q * φ q) p‖
      ≤ 17 * (dyad j * L) ^ 2 *
          (SΦ * ((symbolGridStep L / dyad j) ^ 3 * (kappa ξ ^ 2 + dyad j ^ 2)⁻¹ * X)) := by
  classical
  obtain ⟨h10, hst⟩ := shellCutoff_stencil L hL j hj
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hρ : 0 < kappa ξ ^ 2 + dyad j ^ 2 := by positivity
  have hLpos := cast_L_pos L
  have ht0 : 0 ≤ symbolGridStep L / dyad j := by rw [symbolGridStep]; positivity
  set t := symbolGridStep L / dyad j with ht
  set ρ2 := kappa ξ ^ 2 + dyad j ^ 2 with hρ2
  set M := SΦ * (t ^ 3 * ρ2⁻¹ * X) with hM
  have hM0 : 0 ≤ M := by positivity
  set G : Z2 L → ℂ := fun q => (shellCutoff L j q : ℂ) * invSymbolMultiplier L ξ q * φ q
    with hG
  set supp := Finset.univ.filter (fun q : Z2 L => shellCutoff L j q ≠ 0) with hsupp
  set Bset := (Finset.range 4).biUnion (fun l => supp.image (fun q => q - l • e)) with hBset
  have hmem : ∀ p, p ∈ Bset ↔ ∃ l, l ≤ 3 ∧ shellCutoff L j (p + l • e) ≠ 0 := by
    intro p
    simp only [hBset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, hsupp,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, q, hq, rfl⟩
      exact ⟨l, by omega, by rwa [sub_add_cancel]⟩
    · rintro ⟨l, hl, hne⟩
      exact ⟨l, by omega, p + l • e, hne, add_sub_cancel_right _ _⟩
  have hvan : ∀ p, p ∉ Bset → (fwdDiff e)^[3] G p = 0 := by
    intro p hp
    apply shellKernelBound_iter_zero
    intro l hl
    have h0 : shellCutoff L j (p + l • e) = 0 := by
      by_contra hne
      exact hp ((hmem p).mpr ⟨l, hl, hne⟩)
    change (shellCutoff L j (p + l • e) : ℂ) * _ * _ = 0
    rw [h0, Complex.ofReal_zero, zero_mul, zero_mul]
  have hbd : ∀ p, p ∈ Bset → ‖(fwdDiff e)^[3] G p‖ ≤ M := by
    intro p hp
    obtain ⟨l0, hl0, hne⟩ := (hmem p).mp hp
    have hstp : ∀ l', l' ≤ 3 → dyad j ^ 2 ≤ pstar2 L (p + l' • e) ∧
        pstar2 L (p + l' • e) ≤ (33 / 5 * dyad j) ^ 2 :=
      fun l' hl' => hst e he p l0 l' hl0 hl' hne
    have hchi := shellCutoff_fwdDiff_le L hL e he j p
    have hA : ∀ a, a ≤ 3 → ‖(fwdDiff e)^[a] (fun q => (shellCutoff L j q : ℂ)) p‖ ≤
        shellKernelBound_cχ a * t ^ a := by
      intro a ha
      rw [shellKernelBound_iter_cast, Complex.norm_real, Real.norm_eq_abs]
      interval_cases a
      · have h1 := shellCutoff_mem_Icc L j p
        simp only [Function.iterate_zero, id_eq, shellKernelBound_cχ, ↓reduceIte, pow_zero,
          mul_one]
        rw [abs_of_nonneg h1.1]
        exact h1.2
      · simpa [shellKernelBound_cχ] using hchi.1
      · simpa [shellKernelBound_cχ] using hchi.2.1
      · simpa [shellKernelBound_cχ] using hchi.2.2
    have hB : ∀ a b, a + b ≤ 3 →
        ‖(fwdDiff e)^[b] (invSymbolMultiplier L ξ) (p + a • e)‖ ≤
          shellKernelBound_cm b * t ^ b * ρ2⁻¹ := by
      intro a b hab
      have hq : ∀ l, l ≤ b → dyad j ^ 2 ≤ pstar2 L (p + a • e + l • e) := by
        intro l hl
        rw [add_assoc, ← add_nsmul]
        exact (hstp (a + l) (by omega)).1
      have hb3 : b ≤ 3 := by omega
      interval_cases b
      · have := invSymbolMultiplier_fwdDiff_le L hL ξ hξ e he j (p + a • e) 0 h10 hq
        refine this.trans (le_of_eq ?_)
        simp [shellKernelBound_cm, ht, hρ2, div_eq_mul_inv]
      · have := invSymbolMultiplier_fwdDiff_le L hL ξ hξ e he j (p + a • e) 1 h10 hq
        refine this.trans (le_of_eq ?_)
        simp [shellKernelBound_cm, ht, hρ2, div_eq_mul_inv]
      · have := invSymbolMultiplier_fwdDiff_le L hL ξ hξ e he j (p + a • e) 2 h10 hq
        refine this.trans (le_of_eq ?_)
        simp [shellKernelBound_cm, ht, hρ2, div_eq_mul_inv]
      · have := invSymbolMultiplier_fwdDiff_le L hL ξ hξ e he j (p + a • e) 3 h10 hq
        refine this.trans (le_of_eq ?_)
        simp [shellKernelBound_cm, ht, hρ2, div_eq_mul_inv]
    have hC : ∀ a b, a + b ≤ 3 → ‖(fwdDiff e)^[3 - a - b] φ (p + (a + b) • e)‖ ≤
        Φ (3 - a - b) * t ^ (3 - a - b) * X := fun a b hab =>
      hΦ _ (hstp (a + b) hab).2 _ (by omega)
    have key := shellKernelBound_leib (fun q => (shellCutoff L j q : ℂ))
      (invSymbolMultiplier L ξ) φ e p
      (fun a => shellKernelBound_cχ a * t ^ a) (fun b => shellKernelBound_cm b * t ^ b * ρ2⁻¹)
      (fun c => Φ c * t ^ c * X) hA hB hC
    rw [shellKernelBound_sum_factor] at key
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_right hS (by positivity)
  have hsum_eq : ∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖ = ∑ p ∈ Bset, ‖(fwdDiff e)^[3] G p‖ :=
    (Finset.sum_subset (Finset.subset_univ Bset)
      (fun p _ hp => by rw [hvan p hp, norm_zero])).symm
  have hcardB : (Bset.card : ℝ) ≤ 4 * (supp.card : ℝ) := by
    have h1 : Bset.card ≤ ∑ l ∈ Finset.range 4, (supp.image (fun q => q - l • e)).card :=
      Finset.card_biUnion_le
    have h2 : ∑ l ∈ Finset.range 4, (supp.image (fun q => q - l • e)).card ≤
        ∑ l ∈ Finset.range 4, supp.card := Finset.sum_le_sum fun l _ => Finset.card_image_le
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have h3 : Bset.card ≤ 4 * supp.card := by omega
    exact_mod_cast h3
  have hcardS : (supp.card : ℝ) ≤ (2 * dyad j * L + 1) ^ 2 := (shellCutoff_count L hL j).1
  have h17 : 4 * (2 * dyad j * L + 1) ^ 2 ≤ 17 * (dyad j * L) ^ 2 := by nlinarith
  calc ∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖ = ∑ p ∈ Bset, ‖(fwdDiff e)^[3] G p‖ := hsum_eq
    _ ≤ Bset.card • M := Finset.sum_le_card_nsmul _ _ _ hbd
    _ = (Bset.card : ℝ) * M := nsmul_eq_mul _ _
    _ ≤ 17 * (dyad j * L) ^ 2 * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        linarith

/-- Far-region bound on a large shell: `‖Q‖ ≤ 17 π³ S_Φ X r²/ρ² (r d)⁻³`. -/
private theorem shellKernelBound_far (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (j : ℕ) (hj : 64 < dyad j * L) (φ : Z2 L → ℂ) (Φ : ℕ → ℝ) (X : ℝ)
    (hX : 0 ≤ X)
    (hΦ : ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) → ∀ q : Z2 L,
      pstar2 L q ≤ (33 / 5 * dyad j) ^ 2 → ∀ c, c ≤ 3 →
      ‖(fwdDiff e)^[c] φ q‖ ≤ Φ c * (symbolGridStep L / dyad j) ^ c * X)
    (SΦ : ℝ) (hS0 : 0 ≤ SΦ) (hS : shellKernelBound_sum Φ ≤ SΦ) (u : Z2 L)
    (hu : 1 < dyad j * (zdist2 L u : ℝ)) :
    ‖shellKernelBound_Q L ξ j φ u‖ ≤
      17 * Real.pi ^ 3 * SΦ * X * (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)) *
        ((dyad j * (zdist2 L u : ℝ)) ^ 3)⁻¹ := by
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hρ : 0 < kappa ξ ^ 2 + dyad j ^ 2 := by positivity
  have hLpos := cast_L_pos L
  have hd0 : 0 < (zdist2 L u : ℝ) := by
    by_contra h
    push Not at h
    nlinarith
  have hdsplit : (zdist2 L u : ℝ) = (zdist L u.1 : ℝ) + (zdist L u.2 : ℝ) := by
    rw [zdist2]; push_cast; ring
  set G : Z2 L → ℂ := fun q => (shellCutoff L j q : ℂ) * invSymbolMultiplier L ξ q * φ q
    with hG
  have hQ : ‖shellKernelBound_Q L ξ j φ u‖ =
      ‖∑ p : Z2 L, G p * chr L p u‖ / (L : ℝ) ^ 2 := by
    rw [shellKernelBound_Q, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, inv_mul_eq_div]
  have hdir : ∃ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) ∧
      ‖∑ p : Z2 L, G p * chr L p u‖ ≤
        (∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖) * ((L : ℝ) / (2 * (zdist2 L u : ℝ))) ^ 3 := by
    obtain ⟨h1, h2⟩ := norm_sum_mul_chr_le_fwdDiff_three L G u
    have hN : ∀ e : Z2 L, 0 ≤ ∑ p : Z2 L, ‖(fwdDiff e)^[3] G p‖ :=
      fun e => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have key : ∀ z : ℝ, (zdist2 L u : ℝ) ≤ 2 * z → 0 < z →
        ((L : ℝ) / (4 * z)) ^ 3 ≤ ((L : ℝ) / (2 * (zdist2 L u : ℝ))) ^ 3 := by
      intro z hz hz0
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left hLpos.le (by positivity) (by linarith)
    rcases le_total (zdist L u.2 : ℝ) (zdist L u.1 : ℝ) with h | h
    · have hz : (zdist2 L u : ℝ) ≤ 2 * (zdist L u.1 : ℝ) := by linarith
      have hz0 : 0 < (zdist L u.1 : ℝ) := by linarith
      have hne : u.1 ≠ 0 := by
        intro h0
        rw [h0, zdist_zero] at hz0
        simp at hz0
      exact ⟨(1, 0), Or.inl rfl,
        (h1 hne).trans (mul_le_mul_of_nonneg_left (key _ hz hz0) (hN _))⟩
    · have hz : (zdist2 L u : ℝ) ≤ 2 * (zdist L u.2 : ℝ) := by linarith
      have hz0 : 0 < (zdist L u.2 : ℝ) := by linarith
      have hne : u.2 ≠ 0 := by
        intro h0
        rw [h0, zdist_zero] at hz0
        simp at hz0
      exact ⟨(0, 1), Or.inr rfl,
        (h2 hne).trans (mul_le_mul_of_nonneg_left (key _ hz hz0) (hN _))⟩
  obtain ⟨e, he, hsbp⟩ := hdir
  have hN := shellKernelBound_sum_d3 L hL hξ j hj e he φ Φ X hX (hΦ e he) SΦ hS0 hS
  rw [hQ]
  have hpow0 : 0 ≤ ((L : ℝ) / (2 * (zdist2 L u : ℝ))) ^ 3 := by positivity
  calc ‖∑ p : Z2 L, G p * chr L p u‖ / (L : ℝ) ^ 2
      ≤ (17 * (dyad j * L) ^ 2 * (SΦ * ((symbolGridStep L / dyad j) ^ 3 *
            (kappa ξ ^ 2 + dyad j ^ 2)⁻¹ * X))) *
          ((L : ℝ) / (2 * (zdist2 L u : ℝ))) ^ 3 / (L : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact hsbp.trans (mul_le_mul_of_nonneg_right hN hpow0)
    _ = 17 * Real.pi ^ 3 * SΦ * X * (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)) *
          ((dyad j * (zdist2 L u : ℝ)) ^ 3)⁻¹ := by
        rw [symbolGridStep]
        field_simp

/-! ## Decay weights and constants -/

private theorem shellKernelBound_w_small (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 64) :
    1 ≤ 65 ^ 3 * (1 + x) ^ (-3 : ℤ) := by
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith) 3

private theorem shellKernelBound_w_near (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    1 ≤ 8 * (1 + x) ^ (-3 : ℤ) := by
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  calc (1 + x) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ = 8 := by norm_num

private theorem shellKernelBound_w_far (x : ℝ) (hx : 1 < x) :
    (x ^ 3)⁻¹ ≤ 8 * (1 + x) ^ (-3 : ℤ) := by
  have hx0 : 0 < x := by linarith
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  have h : (1 + x) ^ 3 ≤ 8 * x ^ 3 := by
    calc (1 + x) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 8 * x ^ 3 := by ring
  calc (x ^ 3)⁻¹ = 8 / (8 * x ^ 3) := by field_simp
    _ ≤ 8 / (1 + x) ^ 3 := div_le_div_of_nonneg_left (by norm_num) (by positivity) h

private theorem shellKernelBound_combine (Q K Z v w c C : ℝ) (hK0 : 0 ≤ K) (hZ : 0 ≤ Z)
    (hw0 : 0 ≤ w) (hQ : Q ≤ K * Z * v) (hv : v ≤ c * w) (hK : K * c ≤ C) :
    Q ≤ C * (Z * w) :=
  calc Q ≤ K * Z * v := hQ
    _ ≤ K * Z * (c * w) := mul_le_mul_of_nonneg_left hv (mul_nonneg hK0 hZ)
    _ = (K * c) * (Z * w) := by ring
    _ ≤ C * (Z * w) := mul_le_mul_of_nonneg_right hK (mul_nonneg hZ hw0)

/-- Phase difference constants for `φ ≡ 1`. -/
private noncomputable def shellKernelBound_Φ0 (c : ℕ) : ℝ := if c = 0 then 1 else 0

/-- Phase difference constants for `shellPhase1`: `(33/5, 1, 1, 1)`. -/
private noncomputable def shellKernelBound_Φ1 (c : ℕ) : ℝ := if c = 0 then 33 / 5 else 1

/-- Phase difference constants for `shellPhase2`: `(1089/25, 133/10, 2, 2)`. -/
private noncomputable def shellKernelBound_Φ2 (c : ℕ) : ℝ :=
  if c = 0 then 1089 / 25 else if c = 1 then 133 / 10 else 2

private theorem shellKernelBound_S0 :
    shellKernelBound_sum shellKernelBound_Φ0 ≤ 238406832 := by
  norm_num [shellKernelBound_sum, Finset.sum_range_succ, shellKernelBound_cχ,
    shellKernelBound_cm, shellKernelBound_Φ0, Nat.choose]

private theorem shellKernelBound_S1 :
    shellKernelBound_sum shellKernelBound_Φ1 ≤ 1577073012 := by
  norm_num [shellKernelBound_sum, Finset.sum_range_succ, shellKernelBound_cχ,
    shellKernelBound_cm, shellKernelBound_Φ1, Nat.choose]

private theorem shellKernelBound_S2 :
    shellKernelBound_sum shellKernelBound_Φ2 ≤ 10432346502 := by
  norm_num [shellKernelBound_sum, Finset.sum_range_succ, shellKernelBound_cχ,
    shellKernelBound_cm, shellKernelBound_Φ2, Nat.choose]

/-! ## The theorems -/

theorem shellKernel_small_shell :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (j : ℕ) (u s : Z2 L),
    dyad j * L ≤ 64 →
      ‖shellKernel L ξ j u‖
          ≤ 3 * 10 ^ 8 *
            (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))
        ∧
      ‖shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
          ≤ 2 * 10 ^ 9 * (zdist2 L s : ℝ) *
            (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))
        ∧
      ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s)‖
          ≤ 2 * 10 ^ 10 * (zdist2 L s : ℝ) ^ 2 *
            (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ j u s hsmall
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hpisq : Real.pi ^ 2 ≤ 10 := by nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (zdist2 L s : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact Nat.cast_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hdL : (zdist2 L u : ℝ) ≤ L := by exact_mod_cast zdist2_le_L L u
  have hx : dyad j * (zdist2 L u : ℝ) ≤ 64 :=
    le_trans (mul_le_mul_of_nonneg_left hdL hr.le) hsmall
  have hw1 : 1 ≤ 65 ^ 3 * w := by rw [hw]; exact shellKernelBound_w_small _ (by positivity) hx
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hsupp : ∀ p, shellCutoff L j p ≠ 0 → pstar2 L p < (2 * Real.pi * dyad j) ^ 2 := by
    intro p hp
    have := (shellCutoff_support L j p hp).2
    nlinarith
  have hR : 0 ≤ 2 * Real.pi * dyad j := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [shellKernelBound_Q_one]
    have h := shellKernelBound_trivial L hL hξ j (fun _ => 1) u 1 zero_le_one
      (fun p _ => by simp)
    rw [← hY] at h
    refine (shellKernelBound_combine _ 1008 Y 1 w (65 ^ 3) (3 * 10 ^ 8) (by norm_num) hY0 hw0
      (h.trans_eq (by ring)) hw1 (by norm_num)).trans_eq ?_
    rw [hY, hw]
  · rw [shellKernelBound_Q_diff1]
    have h := shellKernelBound_trivial L hL hξ j (shellPhase1 L s) u
      (2 * Real.pi * dyad j * (zdist2 L s : ℝ)) (by positivity)
      (fun p hp => shellKernelBound_phase1_le L s p _ hR (hsupp p hp))
    rw [← hY, ← hσ] at h
    refine (shellKernelBound_combine _ (1008 * (2 * Real.pi)) (dyad j * σ * Y) 1 w (65 ^ 3)
      (2 * 10 ^ 9) (by positivity) (by positivity) hw0 (h.trans_eq (by ring)) hw1
      (by nlinarith)).trans_eq ?_
    rw [hY, hw, hσ]
    ring
  · rw [shellKernelBound_Q_diff2]
    have h := shellKernelBound_trivial L hL hξ j (shellPhase2 L s) u
      ((2 * Real.pi * dyad j * (zdist2 L s : ℝ)) ^ 2) (by positivity)
      (fun p hp => shellKernelBound_phase2_le L s p _ hR (hsupp p hp))
    rw [← hY, ← hσ] at h
    refine (shellKernelBound_combine _ (1008 * (2 * Real.pi) ^ 2) ((dyad j * σ) ^ 2 * Y) 1 w
      (65 ^ 3) (2 * 10 ^ 10) (by positivity) (by positivity) hw0 (h.trans_eq (by ring)) hw1
      (by nlinarith)).trans_eq ?_
    rw [hY, hw, hσ]
    ring

theorem shellKernel_large_shell :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (j : ℕ) (u s : Z2 L),
    64 < dyad j * L →
      ‖shellKernel L ξ j u‖
          ≤ 2 * 10 ^ 12 *
            (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))
        ∧
      (dyad j * (zdist2 L s : ℝ) ≤ 1 →
        ‖shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
          ≤ 10 ^ 13 * (zdist2 L s : ℝ) *
            (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)))
        ∧
      (dyad j * (zdist2 L s : ℝ) ≤ 1 →
        ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s)‖
          ≤ 5 * 10 ^ 13 * (zdist2 L s : ℝ) ^ 2 *
            (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
              * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ))) := by
  intro L _ hL ξ hξ j u s hlarge
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hpisq : Real.pi ^ 2 ≤ 10 := by nlinarith
  have hpi3 : Real.pi ^ 3 ≤ 3126 / 100 := by
    have h1 : Real.pi ^ 2 ≤ 99225 / 10000 := by nlinarith
    have h2 : Real.pi ^ 3 = Real.pi * Real.pi ^ 2 := by ring
    rw [h2]
    nlinarith
  obtain ⟨h10, -⟩ := shellCutoff_stencil L hL j hlarge
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (zdist2 L s : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = dyad j * (zdist2 L u : ℝ) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact Nat.cast_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwx : w = (1 + x) ^ (-3 : ℤ) := by rw [hw, hx]
  have hsupp : ∀ p, shellCutoff L j p ≠ 0 → pstar2 L p < (2 * Real.pi * dyad j) ^ 2 := by
    intro p hp
    have := (shellCutoff_support L j p hp).2
    nlinarith
  have hR : 0 ≤ 2 * Real.pi * dyad j := by positivity
  -- phase difference hypotheses of the far-region bound
  have hΦ0 : ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) → ∀ q : Z2 L,
      pstar2 L q ≤ (33 / 5 * dyad j) ^ 2 → ∀ c, c ≤ 3 →
      ‖(fwdDiff e)^[c] (fun _ : Z2 L => (1 : ℂ)) q‖ ≤
        shellKernelBound_Φ0 c * (symbolGridStep L / dyad j) ^ c * 1 := by
    intro e _ q _ c _
    rcases c with _ | k
    · simp [shellKernelBound_Φ0]
    · rw [shellKernelBound_iter_one]
      simp [shellKernelBound_Φ0]
  have hΦ1 : dyad j * (zdist2 L s : ℝ) ≤ 1 → ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) →
      ∀ q : Z2 L, pstar2 L q ≤ (33 / 5 * dyad j) ^ 2 → ∀ c, c ≤ 3 →
      ‖(fwdDiff e)^[c] (shellPhase1 L s) q‖ ≤
        shellKernelBound_Φ1 c * (symbolGridStep L / dyad j) ^ c *
          (dyad j * (zdist2 L s : ℝ)) := by
    intro hrs e he q hq c hc
    have H := fun k : Fin 4 => (shellPhase_fwdDiff_le L hL e he j s q k h10 hrs hq).1
    interval_cases c
    · simpa [shellKernelBound_Φ1] using H 0
    · simpa [shellKernelBound_Φ1] using H 1
    · simpa [shellKernelBound_Φ1] using H 2
    · simpa [shellKernelBound_Φ1] using H 3
  have hΦ2 : dyad j * (zdist2 L s : ℝ) ≤ 1 → ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) →
      ∀ q : Z2 L, pstar2 L q ≤ (33 / 5 * dyad j) ^ 2 → ∀ c, c ≤ 3 →
      ‖(fwdDiff e)^[c] (shellPhase2 L s) q‖ ≤
        shellKernelBound_Φ2 c * (symbolGridStep L / dyad j) ^ c *
          (dyad j * (zdist2 L s : ℝ)) ^ 2 := by
    intro hrs e he q hq c hc
    have H := fun k : Fin 4 => (shellPhase_fwdDiff_le L hL e he j s q k h10 hrs hq).2
    interval_cases c
    · simpa [shellKernelBound_Φ2] using H 0
    · simpa [shellKernelBound_Φ2] using H 1
    · simpa [shellKernelBound_Φ2] using H 2
    · simpa [shellKernelBound_Φ2] using H 3
  refine ⟨?_, fun hrs => ?_, fun hrs => ?_⟩
  · rw [shellKernelBound_Q_one]
    rcases le_or_gt x 1 with hnear | hfar
    · have h := shellKernelBound_trivial L hL hξ j (fun _ => 1) u 1 zero_le_one
        (fun p _ => by simp)
      rw [← hY] at h
      have hw1 : 1 ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_near x hx0 hnear
      refine (shellKernelBound_combine _ 1008 Y 1 w 8 (2 * 10 ^ 12) (by norm_num) hY0 hw0
        (h.trans_eq (by ring)) hw1 (by norm_num)).trans_eq ?_
      rw [hY, hw]
    · have h := shellKernelBound_far L hL hξ j hlarge (fun _ => 1) shellKernelBound_Φ0 1
        zero_le_one hΦ0 238406832 (by norm_num) shellKernelBound_S0 u (by rw [← hx]; exact hfar)
      rw [← hY, ← hx] at h
      have hv : (x ^ 3)⁻¹ ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_far x hfar
      refine (shellKernelBound_combine _ (17 * Real.pi ^ 3 * 238406832) Y (x ^ 3)⁻¹ w 8
        (2 * 10 ^ 12) (by positivity) hY0 hw0 (h.trans_eq (by ring)) hv
        (by nlinarith)).trans_eq ?_
      rw [hY, hw]
  · rw [shellKernelBound_Q_diff1]
    rcases le_or_gt x 1 with hnear | hfar
    · have h := shellKernelBound_trivial L hL hξ j (shellPhase1 L s) u
        (2 * Real.pi * dyad j * (zdist2 L s : ℝ)) (by positivity)
        (fun p hp => shellKernelBound_phase1_le L s p _ hR (hsupp p hp))
      rw [← hY, ← hσ] at h
      have hw1 : 1 ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_near x hx0 hnear
      refine (shellKernelBound_combine _ (1008 * (2 * Real.pi)) (dyad j * σ * Y) 1 w 8
        (10 ^ 13) (by positivity) (by positivity) hw0 (h.trans_eq (by ring)) hw1
        (by nlinarith)).trans_eq ?_
      rw [hY, hw, hσ]
      ring
    · have h := shellKernelBound_far L hL hξ j hlarge (shellPhase1 L s) shellKernelBound_Φ1
        (dyad j * (zdist2 L s : ℝ)) (by positivity) (hΦ1 hrs) 1577073012 (by norm_num)
        shellKernelBound_S1 u (by rw [← hx]; exact hfar)
      rw [← hY, ← hx, ← hσ] at h
      have hv : (x ^ 3)⁻¹ ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_far x hfar
      refine (shellKernelBound_combine _ (17 * Real.pi ^ 3 * 1577073012) (dyad j * σ * Y)
        (x ^ 3)⁻¹ w 8 (10 ^ 13) (by positivity) (by positivity) hw0 (h.trans_eq (by ring)) hv
        (by nlinarith)).trans_eq ?_
      rw [hY, hw, hσ]
      ring
  · rw [shellKernelBound_Q_diff2]
    rcases le_or_gt x 1 with hnear | hfar
    · have h := shellKernelBound_trivial L hL hξ j (shellPhase2 L s) u
        ((2 * Real.pi * dyad j * (zdist2 L s : ℝ)) ^ 2) (by positivity)
        (fun p hp => shellKernelBound_phase2_le L s p _ hR (hsupp p hp))
      rw [← hY, ← hσ] at h
      have hw1 : 1 ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_near x hx0 hnear
      refine (shellKernelBound_combine _ (1008 * (2 * Real.pi) ^ 2) ((dyad j * σ) ^ 2 * Y) 1 w
        8 (5 * 10 ^ 13) (by positivity) (by positivity) hw0 (h.trans_eq (by ring)) hw1
        (by nlinarith)).trans_eq ?_
      rw [hY, hw, hσ]
      ring
    · have h := shellKernelBound_far L hL hξ j hlarge (shellPhase2 L s) shellKernelBound_Φ2
        ((dyad j * (zdist2 L s : ℝ)) ^ 2) (by positivity) (hΦ2 hrs) 10432346502 (by norm_num)
        shellKernelBound_S2 u (by rw [← hx]; exact hfar)
      rw [← hY, ← hx, ← hσ] at h
      have hv : (x ^ 3)⁻¹ ≤ 8 * w := by rw [hwx]; exact shellKernelBound_w_far x hfar
      refine (shellKernelBound_combine _ (17 * Real.pi ^ 3 * 10432346502) ((dyad j * σ) ^ 2 * Y)
        (x ^ 3)⁻¹ w 8 (5 * 10 ^ 13) (by positivity) (by positivity) hw0
        (h.trans_eq (by ring)) hv (by nlinarith)).trans_eq ?_
      rw [hY, hw, hσ]
      ring

end RBM
