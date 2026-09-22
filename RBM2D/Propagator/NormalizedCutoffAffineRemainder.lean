/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffFoldBound

/-!
# Analytic second differences along an affine continuation

A global Lipschitz bound for a function and its derivative separates the
nonuniformity of a three-point mesh from the quadratic equal-step remainder.
This is the one-variable ingredient needed for the affine-frequency term.
-/

namespace RBM

private theorem abs_sub_le_mul_of_hasDerivAt
    (f f' : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f' x| ≤ C) (x y : ℝ) :
    |f y - f x| ≤ C * |y - x| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := f) (x := x) (y := y) (C := C)
    (fun z _ => (hf z).differentiableAt)
    (fun z _ => by rw [(hf z).deriv]; simpa only [Real.norm_eq_abs] using hbound z)
    (by simp) (by simp)
  simpa only [Real.norm_eq_abs] using h

private theorem hasDerivAt_forwardDifference (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h x : ℝ) :
    HasDerivAt (fun y => f (y + h) - f y) (f' (x + h) - f' x) x := by
  have hshift : HasDerivAt (fun y : ℝ => y + h) 1 x :=
    (hasDerivAt_id x).add_const h
  have hcomp := (hf (x + h)).comp x hshift
  convert hcomp.sub (hf x) using 1
  · funext y
    rfl
  · simp

/-- The equal-step second difference follows from a Lipschitz derivative. -/
theorem abs_second_forward_diff_le_of_deriv_lipschitz
    (f f' : ℝ → ℝ) (M : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'Lip : ∀ x y, |f' y - f' x| ≤ M * |y - x|)
    (a h : ℝ) :
    |f (a + 2 * h) - 2 * f (a + h) + f a| ≤ M * |h| ^ 2 := by
  let F : ℝ → ℝ := fun x => f (x + h) - f x
  let F' : ℝ → ℝ := fun x => f' (x + h) - f' x
  have hF : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    exact hasDerivAt_forwardDifference f f' hf h x
  have hF' (x : ℝ) : |F' x| ≤ M * |h| := by
    simpa [F', add_sub_cancel_left] using hf'Lip x (x + h)
  have hMV := abs_sub_le_mul_of_hasDerivAt F F' (M * |h|)
    hF hF' a (a + h)
  have hrepr : F (a + h) - F a =
      f (a + 2 * h) - 2 * f (a + h) + f a := by
    dsimp [F]
    ring_nf
  rw [hrepr] at hMV
  calc
    |f (a + 2 * h) - 2 * f (a + h) + f a| ≤
        (M * |h|) * |h| := by simpa using hMV
    _ = M * |h| ^ 2 := by ring

/-- A nonuniform three-point second difference equals a quadratic affine
remainder plus a first-order mesh defect. -/
theorem abs_second_diff_le_of_deriv_lipschitz
    (f f' : ℝ → ℝ) (M₁ M₂ : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfLip : ∀ x y, |f y - f x| ≤ M₁ * |y - x|)
    (hf'Lip : ∀ x y, |f' y - f' x| ≤ M₂ * |y - x|)
    (a b c : ℝ) :
    |f c - 2 * f b + f a| ≤
      M₁ * |c - 2 * b + a| + M₂ * |b - a| ^ 2 := by
  let h := b - a
  let w := a + 2 * h
  have hb : a + h = b := by dsimp [h]; ring
  have hw : w = 2 * b - a := by dsimp [w, h]; ring
  have hsecond := abs_second_forward_diff_le_of_deriv_lipschitz
    f f' M₂ hf hf'Lip a h
  have hrepr : f c - 2 * f b + f a =
      (f c - f w) + (f w - 2 * f b + f a) := by ring
  rw [hrepr]
  calc
    |(f c - f w) + (f w - 2 * f b + f a)| ≤
      |f c - f w| + |f w - 2 * f b + f a| := abs_add_le _ _
    _ ≤ M₁ * |c - w| + M₂ * |h| ^ 2 := by
      apply add_le_add (hfLip w c)
      simpa only [w, hb] using hsecond
    _ = M₁ * |c - 2 * b + a| + M₂ * |b - a| ^ 2 := by
      rw [hw]
      dsimp [h]
      congr 1
      ring_nf

private theorem abs_lowPassD2_le (t : ℝ) : |lowPassD2 t| ≤ 420 := by
  by_cases h₁ : t ≤ 1
  · simp [lowPassD2, h₁]
  by_cases h₂ : t ≤ 2
  · have hx₀ : 0 ≤ t - 1 := by linarith
    have hx₁ : t - 1 ≤ 1 := by linarith
    have hy₀ : 0 ≤ 1 - (t - 1) := by linarith
    have hy₁ : 1 - (t - 1) ≤ 1 := by linarith
    have hz : |1 - 2 * (t - 1)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hx : |t - 1| ≤ 1 := abs_le.mpr ⟨by linarith, hx₁⟩
    have hy : |1 - (t - 1)| ≤ 1 := abs_le.mpr ⟨by linarith, hy₁⟩
    simp only [lowPassD2, ite_eq_right h₁, ite_eq_left h₂, abs_neg]
    rw [smoothstep3D2_factor]
    calc
      |420 * (t - 1) ^ 2 * (1 - (t - 1)) ^ 2 *
          (1 - 2 * (t - 1))| =
        420 * |t - 1| ^ 2 * |1 - (t - 1)| ^ 2 *
          |1 - 2 * (t - 1)| := by
            simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 420)]
      _ ≤ 420 * 1 ^ 2 * 1 ^ 2 * 1 := by gcongr
      _ = 420 := by norm_num
  · simp [lowPassD2, h₁, h₂]

private theorem abs_lowPassD1_sub_le (u v : ℝ) :
    |lowPassD1 v - lowPassD1 u| ≤ 420 * |v - u| := by
  exact abs_sub_le_mul_of_hasDerivAt lowPassD1 lowPassD2 420
    hasDerivAt_lowPassD1 abs_lowPassD2_le u v

/-- The explicit first derivative of the real dyadic annular cutoff. -/
noncomputable def dyadicCutoffD1 (j : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ j * lowPassD1 ((2 : ℝ) ^ j * x) -
    (2 : ℝ) ^ (j + 1) * lowPassD1 ((2 : ℝ) ^ (j + 1) * x)

theorem hasDerivAt_dyadicCutoff (j : ℕ) (x : ℝ) :
    HasDerivAt (dyadicCutoff j) (dyadicCutoffD1 j x) x := by
  have hA := (hasDerivAt_lowPass ((2 : ℝ) ^ j * x)).comp x
    ((hasDerivAt_id x).const_mul ((2 : ℝ) ^ j))
  have hB := (hasDerivAt_lowPass ((2 : ℝ) ^ (j + 1) * x)).comp x
    ((hasDerivAt_id x).const_mul ((2 : ℝ) ^ (j + 1)))
  convert hA.sub hB using 1
  · funext y
    unfold dyadicCutoff
    rw [inv_dyad j, inv_dyad (j + 1)]
    rfl
  · unfold dyadicCutoffD1
    ring

/-- The derivative of the annular cutoff is globally Lipschitz at the
explicit squared dyadic scale. -/
theorem abs_dyadicCutoffD1_sub_le (j : ℕ) (u v : ℝ) :
    |dyadicCutoffD1 j v - dyadicCutoffD1 j u| ≤
      2100 * ((2 : ℝ) ^ j) ^ 2 * |v - u| := by
  let a : ℝ := (2 : ℝ) ^ j
  let b : ℝ := (2 : ℝ) ^ (j + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA := abs_lowPassD1_sub_le (a * u) (a * v)
  have hB := abs_lowPassD1_sub_le (b * u) (b * v)
  have hrepr : dyadicCutoffD1 j v - dyadicCutoffD1 j u =
      a * (lowPassD1 (a * v) - lowPassD1 (a * u)) -
        b * (lowPassD1 (b * v) - lowPassD1 (b * u)) := by
    dsimp [dyadicCutoffD1, a, b]
    ring
  rw [hrepr]
  calc
    |a * (lowPassD1 (a * v) - lowPassD1 (a * u)) -
        b * (lowPassD1 (b * v) - lowPassD1 (b * u))| ≤
      |a * (lowPassD1 (a * v) - lowPassD1 (a * u))| +
        |b * (lowPassD1 (b * v) - lowPassD1 (b * u))| := abs_sub _ _
    _ ≤ a * (420 * |a * v - a * u|) +
        b * (420 * |b * v - b * u|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      exact add_le_add (mul_le_mul_of_nonneg_left hA ha)
        (mul_le_mul_of_nonneg_left hB hb)
    _ = 2100 * ((2 : ℝ) ^ j) ^ 2 * |v - u| := by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hb]
      have hba : b = 2 * a := by dsimp [a, b]; rw [pow_succ]; ring
      rw [hba]
      dsimp [a]
      ring

/-- Explicit nonuniform second difference for the actual `C³` annular
cutoff. The first term measures mesh curvature; the second is quadratic. -/
theorem abs_dyadicCutoff_second_diff_le (j : ℕ) (a b c : ℝ) :
    |dyadicCutoff j c - 2 * dyadicCutoff j b + dyadicCutoff j a| ≤
      420 * (2 : ℝ) ^ j * |c - 2 * b + a| +
        2100 * ((2 : ℝ) ^ j) ^ 2 * |b - a| ^ 2 := by
  exact abs_second_diff_le_of_deriv_lipschitz (dyadicCutoff j)
    (dyadicCutoffD1 j) (420 * (2 : ℝ) ^ j)
    (2100 * ((2 : ℝ) ^ j) ^ 2)
    (hasDerivAt_dyadicCutoff j)
    (abs_dyadicCutoff_sub_le j)
    (abs_dyadicCutoffD1_sub_le j) a b c

/-- The first-coordinate affine-frequency remainder has an explicit
quadratic mesh term; only its radial curvature remains to estimate. -/
theorem abs_affine_cutoff_remainder_e1_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (hq : q = p + (1, 0)) :
    |dyadicCutoff j (affineFrequencyE1 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        |affineFrequencyE1 L p q - 2 * normalizedFrequency L q +
          normalizedFrequency L p| +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := by
  have hstep : |normalizedFrequency L q - normalizedFrequency L p| ≤
      1 / (L : ℝ) := by
    rw [hq]
    simpa only [normalizedGridStep_eq_inv] using
      abs_normalizedFrequency_shift_e1_le L hL p
  have hsq : |normalizedFrequency L q - normalizedFrequency L p| ^ 2 ≤
      (1 / (L : ℝ)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hstep
  have hcut := abs_dyadicCutoff_second_diff_le j
    (normalizedFrequency L p) (normalizedFrequency L q)
    (affineFrequencyE1 L p q)
  dsimp only [normalizedDyadicCutoff]
  exact hcut.trans (by gcongr)

/-- The same quadratic mesh contribution in the second coordinate. -/
theorem abs_affine_cutoff_remainder_e2_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (hq : q = p + (0, 1)) :
    |dyadicCutoff j (affineFrequencyE2 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      420 * (2 : ℝ) ^ j *
        |affineFrequencyE2 L p q - 2 * normalizedFrequency L q +
          normalizedFrequency L p| +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := by
  have hstep : |normalizedFrequency L q - normalizedFrequency L p| ≤
      1 / (L : ℝ) := by
    rw [hq]
    simpa only [normalizedGridStep_eq_inv] using
      abs_normalizedFrequency_shift_e2_le L hL p
  have hsq : |normalizedFrequency L q - normalizedFrequency L p| ^ 2 ≤
      (1 / (L : ℝ)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hstep
  have hcut := abs_dyadicCutoff_second_diff_le j
    (normalizedFrequency L p) (normalizedFrequency L q)
    (affineFrequencyE2 L p q)
  dsimp only [normalizedDyadicCutoff]
  exact hcut.trans (by gcongr)

private theorem abs_second_le_of_sq_diff_affine
    {a b c ε ρ : ℝ} (hρ : 0 < ρ) (hb : ρ ≤ b)
    (hε : 0 ≤ ε)
    (h₁ : |b - a| ≤ ε) (h₂ : |c - b| ≤ ε)
    (hsq₀ : 0 ≤ c ^ 2 - 2 * b ^ 2 + a ^ 2)
    (hsq₁ : c ^ 2 - 2 * b ^ 2 + a ^ 2 ≤ 2 * ε ^ 2) :
    |c - 2 * b + a| ≤ ε ^ 2 / ρ := by
  have h₁sq : (b - a) ^ 2 ≤ ε ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 h₁
    simpa only [sq_abs] using h
  have h₂sq : (c - b) ^ 2 ≤ ε ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 h₂
    simpa only [sq_abs] using h
  have hident : 2 * b * (c - 2 * b + a) =
      (c ^ 2 - 2 * b ^ 2 + a ^ 2) -
        (c - b) ^ 2 - (a - b) ^ 2 := by ring
  have hlow : -(2 * ε ^ 2) ≤ 2 * b * (c - 2 * b + a) := by
    rw [hident]
    nlinarith [sq_nonneg (a - b)]
  have hupp : 2 * b * (c - 2 * b + a) ≤ 2 * ε ^ 2 := by
    rw [hident]
    nlinarith [sq_nonneg (c - b), sq_nonneg (a - b)]
  have hbpos : 0 < b := lt_of_lt_of_le hρ hb
  have habs : |2 * b * (c - 2 * b + a)| ≤ 2 * ε ^ 2 :=
    abs_le.mpr ⟨hlow, hupp⟩
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * b)] at habs
  have hbabs : b * |c - 2 * b + a| ≤ ε ^ 2 := by nlinarith
  have hρabs : ρ * |c - 2 * b + a| ≤ ε ^ 2 :=
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans hbabs
  exact (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hρabs)

private theorem abs_radial_sqrt_sub_le_affine (x y t : ℝ) :
    |Real.sqrt (x ^ 2 + t ^ 2) - Real.sqrt (y ^ 2 + t ^ 2)| ≤
      |x - y| := by
  let zx : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  let zy : ℂ := (y : ℂ) + (t : ℂ) * Complex.I
  have hx : ‖zx‖ = Real.sqrt (x ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [zx, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  have hy : ‖zy‖ = Real.sqrt (y ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [zy, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring_nf
  have hdiff : zx - zy = ((x - y : ℝ) : ℂ) := by
    dsimp [zx, zy]
    push_cast
    ring
  have h := abs_norm_sub_norm_le zx zy
  rw [hx, hy, hdiff, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

private noncomputable def radialFrequency (x t : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + t ^ 2) / (2 * Real.pi)

private theorem abs_radialFrequency_sub_le (x y t : ℝ) :
    |radialFrequency x t - radialFrequency y t| ≤
      |x - y| / (2 * Real.pi) := by
  have h := abs_radial_sqrt_sub_le_affine x y t
  unfold radialFrequency
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact (div_le_div_iff_of_pos_right
    (by positivity : 0 < 2 * Real.pi)).2 h

private theorem abs_radialFrequency_affine_second_diff_le
    (a b t ε ρ : ℝ) (hρ : 0 < ρ)
    (hmiddle : ρ ≤ radialFrequency b t)
    (hε : 0 ≤ ε)
    (hstep : |b - a| / (2 * Real.pi) ≤ ε) :
    |radialFrequency (2 * b - a) t - 2 * radialFrequency b t +
        radialFrequency a t| ≤ ε ^ 2 / ρ := by
  let A := radialFrequency a t
  let B := radialFrequency b t
  let C := radialFrequency (2 * b - a) t
  have h₁ : |B - A| ≤ ε :=
    (abs_radialFrequency_sub_le b a t).trans hstep
  have h₂ : |C - B| ≤ ε := by
    have h := abs_radialFrequency_sub_le (2 * b - a) b t
    have hident : (2 * b - a) - b = b - a := by ring
    rw [hident] at h
    exact h.trans hstep
  have hsq (x : ℝ) : (radialFrequency x t) ^ 2 =
      (x ^ 2 + t ^ 2) / (2 * Real.pi) ^ 2 := by
    unfold radialFrequency
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hident : C ^ 2 - 2 * B ^ 2 + A ^ 2 =
      2 * ((b - a) / (2 * Real.pi)) ^ 2 := by
    dsimp [A, B, C]
    rw [hsq, hsq, hsq, div_pow]
    ring
  have hsq₀ : 0 ≤ C ^ 2 - 2 * B ^ 2 + A ^ 2 := by
    rw [hident]
    positivity
  have hstepSq : ((b - a) / (2 * Real.pi)) ^ 2 ≤ ε ^ 2 := by
    have hstep' : |(b - a) / (2 * Real.pi)| ≤ ε := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact hstep
    have h := (sq_le_sq₀ (abs_nonneg _) hε).2 hstep'
    simpa only [sq_abs] using h
  have hsq₁ : C ^ 2 - 2 * B ^ 2 + A ^ 2 ≤ 2 * ε ^ 2 := by
    rw [hident]
    linarith
  exact abs_second_le_of_sq_diff_affine hρ hmiddle hε h₁ h₂ hsq₀ hsq₁

private theorem abs_pstar_shift_one_le_grid_affine (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (u : ZMod L) :
    |pstar L (u + 1) - pstar L u| ≤ symbolGridStep L := by
  have hforward : pstar L (u + 1) ≤
      pstar L u + symbolGridStep L := by
    have hz : zdist L (u + 1) ≤ zdist L u + 1 := by
      have h := zdist_add_le L u (1 : ZMod L)
      have h1 := zdist_one_le L hL
      omega
    have hz' : (zdist L (u + 1) : ℝ) ≤
        (zdist L u : ℝ) + 1 := by exact_mod_cast hz
    have hg : 0 ≤ symbolGridStep L := by unfold symbolGridStep; positivity
    calc
      pstar L (u + 1) = symbolGridStep L * (zdist L (u + 1) : ℝ) := by
        unfold pstar symbolGridStep
        ring
      _ ≤ symbolGridStep L * ((zdist L u : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hz' hg
      _ = pstar L u + symbolGridStep L := by
        unfold pstar symbolGridStep
        ring
  apply abs_le.mpr
  constructor
  · have := pstar_le_shift_one L hL u
    linarith
  · linarith

/-- The affine continuation of the first coordinate has quadratic radial
curvature whenever the middle normalized radius is at least `ρ > 0`. -/
theorem abs_affineFrequencyE1_second_diff_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (ρ : ℝ)
    (hq : q = p + (1, 0)) (hρ : 0 < ρ)
    (hmiddle : ρ ≤ normalizedFrequency L q) :
    |affineFrequencyE1 L p q - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  have hq₁ : q.1 = p.1 + 1 := by rw [hq]; rfl
  have hq₂ : q.2 = p.2 := by simp [hq]
  have hstep : |pstar L q.1 - pstar L p.1| /
      (2 * Real.pi) ≤ symbolGridStep L / (2 * Real.pi) := by
    apply (div_le_div_iff_of_pos_right
      (by positivity : 0 < 2 * Real.pi)).2
    rw [hq₁]
    exact abs_pstar_shift_one_le_grid_affine L hL p.1
  have hε : 0 ≤ symbolGridStep L / (2 * Real.pi) := by
    unfold symbolGridStep
    positivity
  have h := abs_radialFrequency_affine_second_diff_le
    (pstar L p.1) (pstar L q.1) (pstar L p.2)
    (symbolGridStep L / (2 * Real.pi)) ρ hρ
    (by simpa only [normalizedFrequency, pstar2, hq₂, radialFrequency]
      using hmiddle) hε hstep
  simpa only [radialFrequency, affineFrequencyE1, normalizedFrequency,
    pstar2, hq₂, normalizedGridStep_eq_inv] using h

/-- The symmetric affine radial-curvature bound in the second coordinate. -/
theorem abs_affineFrequencyE2_second_diff_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (ρ : ℝ)
    (hq : q = p + (0, 1)) (hρ : 0 < ρ)
    (hmiddle : ρ ≤ normalizedFrequency L q) :
    |affineFrequencyE2 L p q - 2 * normalizedFrequency L q +
        normalizedFrequency L p| ≤ (1 / (L : ℝ)) ^ 2 / ρ := by
  have hq₁ : q.1 = p.1 := by simp [hq]
  have hq₂ : q.2 = p.2 + 1 := by rw [hq]; rfl
  have hstep : |pstar L q.2 - pstar L p.2| /
      (2 * Real.pi) ≤ symbolGridStep L / (2 * Real.pi) := by
    apply (div_le_div_iff_of_pos_right
      (by positivity : 0 < 2 * Real.pi)).2
    rw [hq₂]
    exact abs_pstar_shift_one_le_grid_affine L hL p.2
  have hε : 0 ≤ symbolGridStep L / (2 * Real.pi) := by
    unfold symbolGridStep
    positivity
  have h := abs_radialFrequency_affine_second_diff_le
    (pstar L p.2) (pstar L q.2) (pstar L p.1)
    (symbolGridStep L / (2 * Real.pi)) ρ hρ
    (by simpa only [normalizedFrequency, pstar2, hq₁, radialFrequency,
      add_comm] using hmiddle) hε hstep
  simpa only [radialFrequency, affineFrequencyE2, normalizedFrequency,
    pstar2, hq₁, add_comm, normalizedGridStep_eq_inv] using h

/-- The first-coordinate cutoff remainder is quadratic in the normalized
mesh size under a positive lower bound for the middle radius. -/
theorem abs_affine_cutoff_remainder_e1_quadratic_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (1, 0)) (hρ : 0 < ρ)
    (hmiddle : ρ ≤ normalizedFrequency L q) :
    |dyadicCutoff j (affineFrequencyE1 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have hmain := abs_affine_cutoff_remainder_e1_le L hL p q j hq
  have hrad := abs_affineFrequencyE1_second_diff_le L hL p q ρ
    hq hρ hmiddle
  calc
    _ ≤ 420 * (2 : ℝ) ^ j *
        |affineFrequencyE1 L p q - 2 * normalizedFrequency L q +
          normalizedFrequency L p| +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := hmain
    _ ≤ 420 * (2 : ℝ) ^ j * ((1 / (L : ℝ)) ^ 2 / ρ) +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := by
      gcongr
    _ = (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by ring

/-- The second-coordinate cutoff remainder obeys the same quadratic bound. -/
theorem abs_affine_cutoff_remainder_e2_quadratic_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (p q : Z2 L) (j : ℕ)
    (ρ : ℝ) (hq : q = p + (0, 1)) (hρ : 0 < ρ)
    (hmiddle : ρ ≤ normalizedFrequency L q) :
    |dyadicCutoff j (affineFrequencyE2 L p q) -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p| ≤
      (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by
  have hmain := abs_affine_cutoff_remainder_e2_le L hL p q j hq
  have hrad := abs_affineFrequencyE2_second_diff_le L hL p q ρ
    hq hρ hmiddle
  calc
    _ ≤ 420 * (2 : ℝ) ^ j *
        |affineFrequencyE2 L p q - 2 * normalizedFrequency L q +
          normalizedFrequency L p| +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := hmain
    _ ≤ 420 * (2 : ℝ) ^ j * ((1 / (L : ℝ)) ^ 2 / ρ) +
        2100 * ((2 : ℝ) ^ j) ^ 2 * (1 / (L : ℝ)) ^ 2 := by
      gcongr
    _ = (420 * (2 : ℝ) ^ j / ρ +
        2100 * ((2 : ℝ) ^ j) ^ 2) * (1 / (L : ℝ)) ^ 2 := by ring

/-- A nonzero frequency realizes the positive-middle-radius premise. -/
example :
    |dyadicCutoff 2
        (affineFrequencyE1 6 ((0, 0) : Z2 6) ((1, 0) : Z2 6)) -
        2 * normalizedDyadicCutoff 6 2 ((1, 0) : Z2 6) +
        normalizedDyadicCutoff 6 2 ((0, 0) : Z2 6)| ≤
      (420 * (2 : ℝ) ^ 2 / (1 / 6 : ℝ) +
        2100 * ((2 : ℝ) ^ 2) ^ 2) * (1 / (6 : ℝ)) ^ 2 := by
  have hz : zdist 6 (1 : ZMod 6) = 1 := by decide
  have hrad : pstar2 6 ((1, 0) : Z2 6) = (Real.pi / 3) ^ 2 := by
    simp only [pstar2, pstar, hz, zdist_zero, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, zero_div]
    ring
  have hν : normalizedFrequency 6 ((1, 0) : Z2 6) = 1 / 6 := by
    rw [normalizedFrequency, hrad, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi / 3)]
    field_simp [Real.pi_ne_zero]
    ring
  apply abs_affine_cutoff_remainder_e1_quadratic_le 6 (by norm_num)
    ((0, 0) : Z2 6) ((1, 0) : Z2 6) 2 (1 / 6 : ℝ)
  · rfl
  · norm_num
  · rw [hν]

/-- A concrete nonconstant check with `f(x)=x²` on a bounded interval. -/
example (a b c : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |c ^ 2 - 2 * b ^ 2 + a ^ 2| ≤
      4 * |c - 2 * b + a| + 2 * |b - a| ^ 2 := by
  have hrep : c ^ 2 - 2 * b ^ 2 + a ^ 2 =
      (c - 2 * b + a) * (c + 2 * b - a) + 2 * (b - a) ^ 2 := by ring
  rw [hrep]
  have hM : |c + 2 * b - a| ≤ 4 := by
    calc
      |c + 2 * b - a| ≤ |c| + |2 * b| + |a| := by
        calc
          _ = |(c + 2 * b) + (-a)| := by ring_nf
          _ ≤ |c + 2 * b| + |-a| := abs_add_le _ _
          _ ≤ |c| + |2 * b| + |a| := by
            simpa only [abs_neg] using add_le_add_left (abs_add_le c (2 * b)) |a|
      _ ≤ 4 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
  calc
    |(c - 2 * b + a) * (c + 2 * b - a) + 2 * (b - a) ^ 2| ≤
      |(c - 2 * b + a) * (c + 2 * b - a)| +
        |2 * (b - a) ^ 2| := abs_add_le _ _
    _ ≤ 4 * |c - 2 * b + a| + 2 * |b - a| ^ 2 := by
      have hsq : |2 * (b - a) ^ 2| = 2 * |b - a| ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
      rw [abs_mul, hsq]
      nlinarith [mul_le_mul_of_nonneg_left hM (abs_nonneg (c - 2 * b + a))]

end RBM

#print axioms RBM.abs_second_forward_diff_le_of_deriv_lipschitz
#print axioms RBM.abs_second_diff_le_of_deriv_lipschitz
#print axioms RBM.hasDerivAt_dyadicCutoff
#print axioms RBM.abs_dyadicCutoffD1_sub_le
#print axioms RBM.abs_dyadicCutoff_second_diff_le
#print axioms RBM.abs_affine_cutoff_remainder_e1_le
#print axioms RBM.abs_affine_cutoff_remainder_e2_le
#print axioms RBM.abs_affineFrequencyE1_second_diff_le
#print axioms RBM.abs_affineFrequencyE2_second_diff_le
#print axioms RBM.abs_affine_cutoff_remainder_e1_quadratic_le
#print axioms RBM.abs_affine_cutoff_remainder_e2_quadratic_le
