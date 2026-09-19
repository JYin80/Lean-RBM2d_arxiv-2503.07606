/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Symbol

/-!
# The ellipticity estimate `(eq_elliptic)`

Formalization of the second half of Section 8.1 of the paper: the definitions
`(eq_kappa_def)`, `(eq_qdef)` and the elementary ellipticity estimate
`(eq_elliptic)`

  `|1 - ξ Ŝ(p)| ∼ κ² + q(p)`,  `κ² = |1 - ξ|`,  `q(p) = 1 - Ŝ(p)`.

The paper's `∼` is a two-sided bound up to absolute constants; here it is split
into the explicit pair

* `RBM.norm_one_sub_mul_Shat_le` : `|1 - ξ Ŝ(p)| ≤ q(p) + |1 - ξ|` (no hypothesis on `ξ`)
* `RBM.norm_one_sub_mul_Shat_ge` : `(1/9) (q(p) + |1 - ξ|) ≤ |1 - ξ Ŝ(p)|`

The constants are not optimal and are not meant to be: the paper's argument
gives `1/4` in the regime `Ŝ(p) ≥ 1/2` and an absolute constant in the other
regime, and every downstream use is up to constants.  See `docs/paper-deltas.md`.

The comparison `q(p) ∼ |p|_*²` of `(eq_qcomp)` is **not** in this file; it needs
Jordan's inequality for `sin` and is tracked as a separate work order.

## Names to double-check against the pinned Mathlib

`Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`,
`Complex.norm_le_abs_re_add_abs_im`.  Older Mathlib spells these
`Complex.abs_re_le_abs`, `Complex.abs_im_le_abs`,
`Complex.abs_le_abs_re_add_abs_im` (with `Complex.abs` in place of `‖·‖`).
-/

namespace RBM

open Finset

section ComplexAux

/-- `‖(r : ℂ)‖ = |r|`.  Stated for a bare variable: `simp` proves this shape, but
pushes the cast inward on something like `((1 - lam : ℝ) : ℂ)` and then can no
longer see that the argument is real. -/
theorem norm_ofReal_aux (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

theorem re_le_norm_aux (z : ℂ) : z.re ≤ ‖z‖ :=
  le_trans (le_abs_self z.re) (Complex.abs_re_le_norm z)

theorem abs_im_le_norm_aux (z : ℂ) : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z

theorem norm_le_abs_re_add_abs_im_aux (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| :=
  Complex.norm_le_abs_re_add_abs_im z

end ComplexAux

section RealMultiplier

variable {ξ : ℂ} {lam : ℝ}

/-- The algebraic identity behind the whole estimate:
`1 - λ ξ = (1 - λ) + λ (1 - ξ)`. -/
theorem one_sub_mul_real_eq (ξ : ℂ) (lam : ℝ) :
    1 - ξ * (lam : ℂ) = ((1 - lam : ℝ) : ℂ) + (lam : ℂ) * (1 - ξ) := by
  push_cast
  ring

theorem re_one_sub_mul_real (ξ : ℂ) (lam : ℝ) :
    (1 - ξ * (lam : ℂ)).re = (1 - lam) + lam * (1 - ξ).re := by
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem im_one_sub_mul_real (ξ : ℂ) (lam : ℝ) :
    (1 - ξ * (lam : ℂ)).im = lam * (1 - ξ).im := by
  simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_sub]
  ring

theorem norm_one_sub_lt_two (hξ : ‖ξ‖ < 1) : ‖(1 : ℂ) - ξ‖ < 2 := by
  calc ‖(1 : ℂ) - ξ‖ ≤ ‖(1 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
    _ < 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

/-- `Re (1 - ξ) > 0` whenever `‖ξ‖ < 1`: this is what prevents the real parts of
the two summands of `1 - λ ξ = (1 - λ) + λ (1 - ξ)` from cancelling. -/
theorem re_one_sub_pos (hξ : ‖ξ‖ < 1) : 0 < ((1 : ℂ) - ξ).re := by
  have h : ξ.re ≤ ‖ξ‖ := re_le_norm_aux ξ
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The upper half of `(eq_elliptic)`, for a real multiplier `λ ∈ [-3/5, 1]`.

Unlike the lower half this needs **no** hypothesis on `ξ`: it is the triangle
inequality applied to `1 - λξ = (1 - λ) + λ(1 - ξ)`.  The paper states both
halves under `|ξ| < 1`; see `docs/paper-deltas.md`. -/
theorem norm_one_sub_mul_real_le (h1 : -(3 / 5 : ℝ) ≤ lam)
    (h2 : lam ≤ 1) : ‖1 - ξ * (lam : ℂ)‖ ≤ (1 - lam) + ‖(1 : ℂ) - ξ‖ := by
  have hnl : ‖((lam : ℝ) : ℂ)‖ = |lam| := by simp
  have habs : |lam| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
  have h1l : |(1 - lam : ℝ)| = 1 - lam := abs_of_nonneg (by linarith)
  calc ‖1 - ξ * (lam : ℂ)‖
      = ‖((1 - lam : ℝ) : ℂ) + (lam : ℂ) * (1 - ξ)‖ := by rw [one_sub_mul_real_eq]
    _ ≤ ‖((1 - lam : ℝ) : ℂ)‖ + ‖(lam : ℂ) * (1 - ξ)‖ := norm_add_le _ _
    _ = (1 - lam) + |lam| * ‖(1 : ℂ) - ξ‖ := by
        rw [norm_mul, hnl]
        congr 1
        rw [norm_ofReal_aux, h1l]
    _ ≤ (1 - lam) + 1 * ‖(1 : ℂ) - ξ‖ := by
        have := mul_le_mul_of_nonneg_right habs (norm_nonneg ((1 : ℂ) - ξ))
        linarith
    _ = (1 - lam) + ‖(1 : ℂ) - ξ‖ := by ring

/-- The lower half of `(eq_elliptic)`, for a real multiplier `λ ∈ [-3/5, 1]`.
The constant `1/9` is not optimal. -/
theorem norm_one_sub_mul_real_ge (hξ : ‖ξ‖ < 1) (h1 : -(3 / 5 : ℝ) ≤ lam)
    (h2 : lam ≤ 1) :
    (1 / 9 : ℝ) * ((1 - lam) + ‖(1 : ℂ) - ξ‖) ≤ ‖1 - ξ * (lam : ℂ)‖ := by
  have hlt2 : ‖(1 : ℂ) - ξ‖ < 2 := norm_one_sub_lt_two hξ
  have hnn : (0 : ℝ) ≤ ‖(1 : ℂ) - ξ‖ := norm_nonneg _
  rcases lt_or_ge lam (1 / 2) with hcase | hcase
  · -- Regime `Ŝ(p) ≤ 1/2`: the multiplier is bounded away from `1` outright.
    have habs : |lam| ≤ 3 / 5 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hnl : ‖((lam : ℝ) : ℂ)‖ = |lam| := by simp
    have hprod : ‖ξ * (lam : ℂ)‖ ≤ 3 / 5 := by
      rw [norm_mul, hnl]
      have hmul : ‖ξ‖ * |lam| ≤ 1 * (3 / 5) :=
        mul_le_mul hξ.le habs (abs_nonneg lam) zero_le_one
      linarith
    have hlow : (2 : ℝ) / 5 ≤ ‖1 - ξ * (lam : ℂ)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ξ * (lam : ℂ))
      rw [norm_one] at this
      linarith
    linarith
  · -- Regime `Ŝ(p) ≥ 1/2`: the two summands of `(1-λ) + λ(1-ξ)` cannot cancel.
    set a := ((1 : ℂ) - ξ).re with ha
    set b := ((1 : ℂ) - ξ).im with hb
    have hapos : 0 < a := re_one_sub_pos hξ
    have hre : (1 - ξ * (lam : ℂ)).re = (1 - lam) + lam * a := re_one_sub_mul_real ξ lam
    have him : (1 - ξ * (lam : ℂ)).im = lam * b := im_one_sub_mul_real ξ lam
    have hge1 : (1 - lam) + lam * a ≤ ‖1 - ξ * (lam : ℂ)‖ := by
      rw [← hre]; exact re_le_norm_aux _
    have hge2 : lam * |b| ≤ ‖1 - ξ * (lam : ℂ)‖ := by
      have h := abs_im_le_norm_aux (1 - ξ * (lam : ℂ))
      rw [him, abs_mul, abs_of_pos (by linarith : (0:ℝ) < lam)] at h
      exact h
    have hsplit : ‖(1 : ℂ) - ξ‖ ≤ |a| + |b| := norm_le_abs_re_add_abs_im_aux _
    have haabs : |a| = a := abs_of_pos hapos
    have hsplit' : ‖(1 : ℂ) - ξ‖ ≤ a + |b| := by rw [← haabs]; exact hsplit
    have hla : (0 : ℝ) ≤ lam := by linarith
    have hmul : lam * ‖(1 : ℂ) - ξ‖ ≤ lam * a + lam * |b| := by
      have h := mul_le_mul_of_nonneg_left hsplit' hla
      linarith
    have hkey : (1 - lam) + lam * ‖(1 : ℂ) - ξ‖ ≤ 2 * ‖1 - ξ * (lam : ℂ)‖ := by
      linarith
    have hhalf : (1 / 2 : ℝ) * ‖(1 : ℂ) - ξ‖ ≤ lam * ‖(1 : ℂ) - ξ‖ :=
      mul_le_mul_of_nonneg_right hcase hnn
    linarith

end RealMultiplier

section Scales

variable (L : ℕ) [NeZero L]

/-- `(eq_kappa_def)`: `κ = |1 - ξ|^{1/2}`. -/
noncomputable def kappa (ξ : ℂ) : ℝ := Real.sqrt ‖(1 : ℂ) - ξ‖

/-- `(eq_kappa_def)`: `ℓ̂(ξ) = min(κ⁻¹, L)`. -/
noncomputable def ellhat (ξ : ℂ) : ℝ := min (kappa ξ)⁻¹ (L : ℝ)

theorem kappa_nonneg (ξ : ℂ) : 0 ≤ kappa ξ := Real.sqrt_nonneg _

theorem kappa_pos {ξ : ℂ} (hξ : ‖ξ‖ < 1) : 0 < kappa ξ := by
  have hne : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
  exact Real.sqrt_pos.mpr (norm_pos_iff.mpr hne)

/-- `κ² = |1 - ξ|`. -/
theorem kappa_sq (ξ : ℂ) : (kappa ξ) ^ 2 = ‖(1 : ℂ) - ξ‖ :=
  Real.sq_sqrt (norm_nonneg _)

theorem ellhat_pos {ξ : ℂ} (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) : 0 < ellhat L ξ := by
  have h1 : (0 : ℝ) < (kappa ξ)⁻¹ := inv_pos.mpr (kappa_pos hξ)
  have h2 : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  exact lt_min h1 h2

/-- `κ ℓ̂(ξ) ≤ 1`, used throughout Section 8.3. -/
theorem kappa_mul_ellhat_le_one {ξ : ℂ} (hξ : ‖ξ‖ < 1) : kappa ξ * ellhat L ξ ≤ 1 := by
  have hk : 0 < kappa ξ := kappa_pos hξ
  calc kappa ξ * ellhat L ξ ≤ kappa ξ * (kappa ξ)⁻¹ :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hk.le
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hk)

end Scales

section Elliptic

variable (L : ℕ) [NeZero L]

/-- `(eq_qdef)`: `q(p) = 1 - Ŝ(p) = (2/5)[(1 - cos p₁) + (1 - cos p₂)]`. -/
noncomputable def qsym (p : Z2 L) : ℝ :=
  2 / 5 * ((1 - Real.cos (2 * Real.pi * p.1.val / L))
    + (1 - Real.cos (2 * Real.pi * p.2.val / L)))

theorem qsym_nonneg (p : Z2 L) : 0 ≤ qsym L p := by
  have h1 := Real.cos_le_one (2 * Real.pi * p.1.val / L)
  have h2 := Real.cos_le_one (2 * Real.pi * p.2.val / L)
  simp only [qsym]
  linarith

theorem qsym_le (p : Z2 L) : qsym L p ≤ 8 / 5 := by
  have h1 := Real.neg_one_le_cos (2 * Real.pi * p.1.val / L)
  have h2 := Real.neg_one_le_cos (2 * Real.pi * p.2.val / L)
  simp only [qsym]
  linarith

/-- `Ŝ(p) = 1 - q(p)`; in particular the symbol is real. -/
theorem Shat_eq_one_sub_qsym (p : Z2 L) : Shat L p = ((1 - qsym L p : ℝ) : ℂ) := by
  rw [Shat_eq_cos, qsym]
  push_cast
  ring

/-- The upper half of `(eq_elliptic)`: `|1 - ξ Ŝ(p)| ≤ q(p) + |1 - ξ|`. -/
theorem norm_one_sub_mul_Shat_le {ξ : ℂ} (p : Z2 L) :
    ‖1 - ξ * Shat L p‖ ≤ qsym L p + ‖(1 : ℂ) - ξ‖ := by
  have hq0 := qsym_nonneg L p
  have hq1 := qsym_le L p
  have h := norm_one_sub_mul_real_le (lam := 1 - qsym L p) (by linarith) (by linarith)
  rw [Shat_eq_one_sub_qsym]
  calc ‖1 - ξ * ((1 - qsym L p : ℝ) : ℂ)‖
      ≤ (1 - (1 - qsym L p)) + ‖(1 : ℂ) - ξ‖ := h
    _ = qsym L p + ‖(1 : ℂ) - ξ‖ := by ring

/-- The lower half of `(eq_elliptic)`:
`(1/9) (q(p) + |1 - ξ|) ≤ |1 - ξ Ŝ(p)|`.  The constant is not optimal. -/
theorem norm_one_sub_mul_Shat_ge {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    (1 / 9 : ℝ) * (qsym L p + ‖(1 : ℂ) - ξ‖) ≤ ‖1 - ξ * Shat L p‖ := by
  have hq0 := qsym_nonneg L p
  have hq1 := qsym_le L p
  have h := norm_one_sub_mul_real_ge (lam := 1 - qsym L p) hξ (by linarith) (by linarith)
  rw [Shat_eq_one_sub_qsym]
  calc (1 / 9 : ℝ) * (qsym L p + ‖(1 : ℂ) - ξ‖)
      = (1 / 9 : ℝ) * ((1 - (1 - qsym L p)) + ‖(1 : ℂ) - ξ‖) := by ring
    _ ≤ ‖1 - ξ * ((1 - qsym L p : ℝ) : ℂ)‖ := h

/-- `(eq_elliptic)` restated with `κ² = |1 - ξ|`, the form used in Section 8.2. -/
theorem norm_one_sub_mul_Shat_ge_kappa {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    (1 / 9 : ℝ) * ((kappa ξ) ^ 2 + qsym L p) ≤ ‖1 - ξ * Shat L p‖ := by
  rw [kappa_sq]
  have h := norm_one_sub_mul_Shat_ge L hξ p
  linarith

end Elliptic

end RBM
