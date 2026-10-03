/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ShellKernelBound

/-!
# Finite-difference bounds for the shell kernels

Combines the per-shell bounds of `RBM2D.Propagator.ShellKernelBound`
(`shellKernel_small_shell`, `shellKernel_large_shell`) into the uniform-in-`j` statements
needed for the `decay`, `fd1`, `fd2` fields of `DyadicDecomp`:

* `shellKernel_decay`, `shellKernel_fd1_near`, `shellKernel_fd2_near` (`r |s| ≤ 1`);
* `shellKernel_fd1`, `shellKernel_fd2` in Case 1 (`2 |s|_L ≤ |u|_L`): for `r |s| > 1` the
  decay bound at `u`, `u ∓ s` and `|u ∓ s|_L ≥ |u|_L / 2` are used.

This is a discrete special form of `(eq_dyadic)` of Section 8.3 for the shell kernels, not the
paper's general statement.
-/

namespace RBM

private theorem shellKernelFD_zdist_neg (L : ℕ) [NeZero L] (x : ZMod L) :
    zdist L (-x) = zdist L x := by
  have hx : x.val < L := ZMod.val_lt x
  by_cases h0 : x = 0
  · subst h0; simp
  · rw [zdist, zdist, ZMod.neg_val]
    simp only [h0, ite_false]
    omega

private theorem shellKernelFD_zdist2_neg (L : ℕ) [NeZero L] (s : Z2 L) :
    zdist2 L (-s) = zdist2 L s := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, shellKernelFD_zdist_neg]

/-- `|u - s| ≥ |u| / 2` when `2 |s| ≤ |u|`, in the form `|u| ≤ 2 |u - s|`. -/
private theorem shellKernelFD_sub_lower (L : ℕ) [NeZero L] (u s : Z2 L)
    (hs : 2 * zdist2 L s ≤ zdist2 L u) : zdist2 L u ≤ 2 * zdist2 L (u - s) := by
  have h := zdist2_add_le L (u - s) s
  rw [sub_add_cancel] at h
  omega

/-- `|u| ≤ 2 |u + s|` when `2 |s| ≤ |u|`. -/
private theorem shellKernelFD_add_lower (L : ℕ) [NeZero L] (u s : Z2 L)
    (hs : 2 * zdist2 L s ≤ zdist2 L u) : zdist2 L u ≤ 2 * zdist2 L (u + s) := by
  have h := zdist2_add_le L (u + s) (-s)
  rw [add_neg_cancel_right, shellKernelFD_zdist2_neg] at h
  omega

private theorem shellKernelFD_w_half (r a d : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * a) :
    (1 + r * a) ^ (-3 : ℤ) ≤ 8 * (1 + r * d) ^ (-3 : ℤ) := by
  rw [zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
  have hra : 0 ≤ r * a := by positivity
  have hrd : 0 ≤ r * d := by positivity
  have h : (1 + r * d) ^ 3 ≤ 8 * (1 + r * a) ^ 3 := by
    calc (1 + r * d) ^ 3 ≤ (2 * (1 + r * a)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hd hr.le]) 3
      _ = 8 * (1 + r * a) ^ 3 := by ring
  calc ((1 + r * a) ^ 3)⁻¹ = 8 / (8 * (1 + r * a) ^ 3) := by field_simp
    _ ≤ 8 / (1 + r * d) ^ 3 := div_le_div_of_nonneg_left (by norm_num) (by positivity) h
    _ = 8 * ((1 + r * d) ^ 3)⁻¹ := by rw [div_eq_mul_inv]

theorem shellKernel_decay :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (j : ℕ) (v : Z2 L),
    ‖shellKernel L ξ j v‖
      ≤ 2 * 10 ^ 12 *
          (dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L v : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ j v
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hX : 0 ≤ dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2)
      * (1 + dyad j * (zdist2 L v : ℝ)) ^ (-3 : ℤ) := by positivity
  by_cases h : dyad j * L ≤ 64
  · have := (shellKernel_small_shell L hL ξ hξ j v 0 h).1
    exact this.trans (mul_le_mul_of_nonneg_right (by norm_num) hX)
  · exact (shellKernel_large_shell L hL ξ hξ j v 0 (not_le.mp h)).1

theorem shellKernel_fd1_near :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (j : ℕ) (u s : Z2 L),
    dyad j * (zdist2 L s : ℝ) ≤ 1 →
    ‖shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
      ≤ 10 ^ 13 * (zdist2 L s : ℝ) *
          (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ j u s hnear
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hX : 0 ≤ (zdist2 L s : ℝ) * (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
      * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by positivity
  by_cases h : dyad j * L ≤ 64
  · have := (shellKernel_small_shell L hL ξ hξ j u s h).2.1
    refine this.trans ?_
    have hm := mul_le_mul_of_nonneg_right (by norm_num : (2 * 10 ^ 9 : ℝ) ≤ 10 ^ 13) hX
    linarith
  · exact (shellKernel_large_shell L hL ξ hξ j u s (not_le.mp h)).2.1 hnear

theorem shellKernel_fd2_near :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (j : ℕ) (u s : Z2 L),
    dyad j * (zdist2 L s : ℝ) ≤ 1 →
    ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s)‖
      ≤ 5 * 10 ^ 13 * (zdist2 L s : ℝ) ^ 2 *
          (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ j u s hnear
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hX : 0 ≤ (zdist2 L s : ℝ) ^ 2 * (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
      * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by positivity
  by_cases h : dyad j * L ≤ 64
  · have := (shellKernel_small_shell L hL ξ hξ j u s h).2.2
    refine this.trans ?_
    have hm := mul_le_mul_of_nonneg_right (by norm_num : (2 * 10 ^ 10 : ℝ) ≤ 5 * 10 ^ 13) hX
    linarith
  · exact (shellKernel_large_shell L hL ξ hξ j u s (not_le.mp h)).2.2 hnear

theorem shellKernel_fd1 :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (u s : Z2 L),
    2 * zdist2 L s ≤ zdist2 L u → ∀ j : ℕ,
    ‖shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
      ≤ 10 ^ 14 * (zdist2 L s : ℝ) *
          (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ u s hs j
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hσ0 : (0 : ℝ) ≤ (zdist2 L s : ℝ) := Nat.cast_nonneg _
  by_cases hnear : dyad j * (zdist2 L s : ℝ) ≤ 1
  · have h := shellKernel_fd1_near L hL ξ hξ j u s hnear
    have hX : 0 ≤ (zdist2 L s : ℝ) * (dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2)
        * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by positivity
    refine h.trans ?_
    have hm := mul_le_mul_of_nonneg_right (by norm_num : (10 ^ 13 : ℝ) ≤ 10 ^ 14) hX
    linarith
  · have hfar : 1 < dyad j * (zdist2 L s : ℝ) := not_le.mp hnear
    have h0 := shellKernel_decay L hL ξ hξ j u
    have h1 := shellKernel_decay L hL ξ hξ j (u - s)
    have hw : (1 + dyad j * (zdist2 L (u - s) : ℝ)) ^ (-3 : ℤ)
        ≤ 8 * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) :=
      shellKernelFD_w_half _ _ _ hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (by exact_mod_cast shellKernelFD_sub_lower L u s hs)
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2) := ⟨_, rfl⟩
    obtain ⟨w, hw'⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) := ⟨_, rfl⟩
    obtain ⟨w1, hw1⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L (u - s) : ℝ)) ^ (-3 : ℤ) :=
      ⟨_, rfl⟩
    have hY0 : 0 ≤ Y := by rw [hY]; positivity
    have hw0 : 0 ≤ w := by rw [hw']; positivity
    have hcube : dyad j ^ 3 / (kappa ξ ^ 2 + dyad j ^ 2) = dyad j * Y := by rw [hY]; ring
    rw [← hY, ← hw'] at h0
    rw [← hY, ← hw1] at h1
    rw [← hw1, ← hw'] at hw
    rw [hcube, ← hw']
    have hYw : 0 ≤ Y * w := mul_nonneg hY0 hw0
    calc ‖shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
        ≤ ‖shellKernel L ξ j u‖ + ‖shellKernel L ξ j (u - s)‖ := norm_sub_le _ _
      _ ≤ 2 * 10 ^ 12 * (Y * w) + 2 * 10 ^ 12 * (Y * w1) := add_le_add h0 h1
      _ ≤ 2 * 10 ^ 12 * (Y * w) + 2 * 10 ^ 12 * (Y * (8 * w)) := by
          gcongr
      _ = 18 * 10 ^ 12 * (Y * w) := by ring
      _ ≤ (10 ^ 14 * (dyad j * (zdist2 L s : ℝ))) * (Y * w) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hYw
      _ = 10 ^ 14 * (zdist2 L s : ℝ) * (dyad j * Y * w) := by ring

theorem shellKernel_fd2 :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ (u s : Z2 L),
    2 * zdist2 L s ≤ zdist2 L u → ∀ j : ℕ,
    ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s)‖
      ≤ 10 ^ 14 * (zdist2 L s : ℝ) ^ 2 *
          (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
            * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by
  intro L _ hL ξ hξ u s hs j
  have hr := dyad_pos j
  have hκ := kappa_pos hξ
  have hσ0 : (0 : ℝ) ≤ (zdist2 L s : ℝ) := Nat.cast_nonneg _
  by_cases hnear : dyad j * (zdist2 L s : ℝ) ≤ 1
  · have h := shellKernel_fd2_near L hL ξ hξ j u s hnear
    have hX : 0 ≤ (zdist2 L s : ℝ) ^ 2 * (dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2)
        * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ)) := by positivity
    refine h.trans ?_
    have hm := mul_le_mul_of_nonneg_right (by norm_num : (5 * 10 ^ 13 : ℝ) ≤ 10 ^ 14) hX
    linarith
  · have hfar : 1 < dyad j * (zdist2 L s : ℝ) := not_le.mp hnear
    have h0 := shellKernel_decay L hL ξ hξ j u
    have h1 := shellKernel_decay L hL ξ hξ j (u - s)
    have h2 := shellKernel_decay L hL ξ hξ j (u + s)
    have hw : (1 + dyad j * (zdist2 L (u - s) : ℝ)) ^ (-3 : ℤ)
        ≤ 8 * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) :=
      shellKernelFD_w_half _ _ _ hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (by exact_mod_cast shellKernelFD_sub_lower L u s hs)
    have hw2 : (1 + dyad j * (zdist2 L (u + s) : ℝ)) ^ (-3 : ℤ)
        ≤ 8 * (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) :=
      shellKernelFD_w_half _ _ _ hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (by exact_mod_cast shellKernelFD_add_lower L u s hs)
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = dyad j ^ 2 / (kappa ξ ^ 2 + dyad j ^ 2) := ⟨_, rfl⟩
    obtain ⟨w, hw'⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L u : ℝ)) ^ (-3 : ℤ) := ⟨_, rfl⟩
    obtain ⟨w1, hw1⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L (u - s) : ℝ)) ^ (-3 : ℤ) :=
      ⟨_, rfl⟩
    obtain ⟨w2, hw2'⟩ : ∃ w : ℝ, w = (1 + dyad j * (zdist2 L (u + s) : ℝ)) ^ (-3 : ℤ) :=
      ⟨_, rfl⟩
    have hY0 : 0 ≤ Y := by rw [hY]; positivity
    have hw0 : 0 ≤ w := by rw [hw']; positivity
    have hquart : dyad j ^ 4 / (kappa ξ ^ 2 + dyad j ^ 2) = dyad j ^ 2 * Y := by
      rw [hY]; ring
    rw [← hY, ← hw'] at h0
    rw [← hY, ← hw1] at h1
    rw [← hY, ← hw2'] at h2
    rw [← hw1, ← hw'] at hw
    rw [← hw2', ← hw'] at hw2
    rw [hquart, ← hw']
    have hYw : 0 ≤ Y * w := mul_nonneg hY0 hw0
    have hσ2 : 1 ≤ (dyad j * (zdist2 L s : ℝ)) ^ 2 := by nlinarith
    calc ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s) - shellKernel L ξ j (u + s)‖
        ≤ ‖2 * shellKernel L ξ j u - shellKernel L ξ j (u - s)‖
            + ‖shellKernel L ξ j (u + s)‖ := norm_sub_le _ _
      _ ≤ (‖2 * shellKernel L ξ j u‖ + ‖shellKernel L ξ j (u - s)‖)
            + ‖shellKernel L ξ j (u + s)‖ := by gcongr; exact norm_sub_le _ _
      _ = (2 * ‖shellKernel L ξ j u‖ + ‖shellKernel L ξ j (u - s)‖)
            + ‖shellKernel L ξ j (u + s)‖ := by
          rw [norm_mul]; simp
      _ ≤ (2 * (2 * 10 ^ 12 * (Y * w)) + 2 * 10 ^ 12 * (Y * (8 * w)))
            + 2 * 10 ^ 12 * (Y * (8 * w)) := by
          have e1 : Y * w1 ≤ Y * (8 * w) := mul_le_mul_of_nonneg_left hw hY0
          have e2 : Y * w2 ≤ Y * (8 * w) := mul_le_mul_of_nonneg_left hw2 hY0
          gcongr
          · exact h1.trans (by gcongr)
          · exact h2.trans (by gcongr)
      _ = 36 * 10 ^ 12 * (Y * w) := by ring
      _ ≤ (10 ^ 14 * (dyad j * (zdist2 L s : ℝ)) ^ 2) * (Y * w) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hYw
      _ = 10 ^ 14 * (zdist2 L s : ℝ) ^ 2 * (dyad j ^ 2 * Y * w) := by ring

end RBM
