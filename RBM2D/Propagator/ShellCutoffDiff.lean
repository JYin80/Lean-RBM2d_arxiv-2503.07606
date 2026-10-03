/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ShellCutoff
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Scale-uniform forward differences of the shell cutoff

Along a coordinate direction `e_i`, the shell cutoff `χ_j = F_a − F_{4a}` with
`F_a(θ) = φ(a t(θ))`, `φ = lowPass`, `a = 4^j`, `t = (2 − cos θ₁ − cos θ₂)/4`.
Since `t′ = sin θ_i/4`, `t″ = cos θ_i/4`, `t‴ = −sin θ_i/4` and `(t′)² ≤ t/2`,
the chain rule gives `|F′| ≤ 3·2^j`, `|F″| ≤ 8.75·4^j`, `|F‴| ≤ 10006.75·8^j`
(with `D₁ ≤ 3`, `D₂ ≤ 8`, `D₃ ≤ 10000`), and the mean value theorem turns these
into the lattice difference bounds `(9, 44, 90061)`.
-/

namespace RBM

open Finset

/-! ## Sharp bounds on the low-pass derivatives -/

private theorem shellCutoffDiff_abs_lowPassD1_le (x : ℝ) : |lowPassD1 x| ≤ 3 := by
  by_cases h1 : x ≤ 1
  · simp [lowPassD1, h1]
  by_cases h2 : x ≤ 2
  · have hy0 : 0 ≤ x - 1 := by linarith
    have hy1 : 0 ≤ 1 - (x - 1) := by linarith
    have hu0 : 0 ≤ (x - 1) * (1 - (x - 1)) := mul_nonneg hy0 hy1
    have hu1 : (x - 1) * (1 - (x - 1)) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 - 1 / 2)]
    have hu3 : ((x - 1) * (1 - (x - 1))) ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
    have hval : lowPassD1 x = -(140 * ((x - 1) * (1 - (x - 1))) ^ 3) := by
      simp only [lowPassD1, h1, h2, ↓reduceIte, smoothstep3D1_factor]
      ring
    rw [hval, abs_neg, abs_of_nonneg (by positivity)]
    norm_num at hu3 ⊢
    linarith
  · simp [lowPassD1, h1, h2]

private theorem shellCutoffDiff_abs_lowPassD2_le (x : ℝ) : |lowPassD2 x| ≤ 8 := by
  by_cases h1 : x ≤ 1
  · simp [lowPassD2, h1]
  by_cases h2 : x ≤ 2
  · set y := x - 1 with hy
    have hy0 : 0 ≤ y := by linarith
    have hy1 : y ≤ 1 := by linarith
    set u := y * (1 - y) with hu
    have hu0 : 0 ≤ u := mul_nonneg hy0 (by linarith)
    have hu1 : u ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have hval : lowPassD2 x = -(420 * u ^ 2 * (1 - 2 * y)) := by
      simp only [lowPassD2, h1, h2, ↓reduceIte, smoothstep3D2_factor, ← hy, hu]
      ring
    have hsq : (1 - 2 * y) ^ 2 = 1 - 4 * u := by rw [hu]; ring
    have hpoly : 4 * u ^ 5 - u ^ 4 + 1 / 3125 ≥ 0 := by
      have hc : 0 ≤ 4 * u ^ 3 + 3 / 5 * u ^ 2 + 2 / 25 * u + 1 / 125 := by positivity
      nlinarith [mul_nonneg (sq_nonneg (u - 1 / 5)) hc]
    have hkey : (420 * u ^ 2 * (1 - 2 * y)) ^ 2 ≤ 8 ^ 2 := by
      have : (420 * u ^ 2 * (1 - 2 * y)) ^ 2 = 420 ^ 2 * (u ^ 4 * (1 - 4 * u)) := by
        rw [mul_pow, mul_pow, hsq]; ring
      rw [this]
      nlinarith [hpoly]
    rw [hval, abs_neg]
    exact abs_le.mpr (abs_le_of_sq_le_sq' hkey (by norm_num))
  · simp [lowPassD2, h1, h2]

private theorem shellCutoffDiff_lowPassD_zero (x : ℝ) (hx : 2 < x) :
    lowPassD1 x = 0 ∧ lowPassD2 x = 0 ∧ lowPassD3 x = 0 := by
  have h1 : ¬ x ≤ 1 := by linarith
  have h2 : ¬ x ≤ 2 := by linarith
  simp [lowPassD1, lowPassD2, lowPassD3, h1, h2]

/-! ## The real-variable profile along one coordinate -/

/-- The smooth radial variable as a function of the active angle `y`, with the
other coordinate's cosine held fixed at `c`. -/
private noncomputable def shellCutoffDiff_T (c y : ℝ) : ℝ := (2 - Real.cos y - c) / 4

private theorem shellCutoffDiff_hasDerivAt_T (c y : ℝ) :
    HasDerivAt (shellCutoffDiff_T c) (Real.sin y / 4) y := by
  have h := (((Real.hasDerivAt_cos y).const_sub 2).sub_const c).div_const 4
  exact h.congr_deriv (by ring)

private theorem shellCutoffDiff_hasDerivAt_sin4 (y : ℝ) :
    HasDerivAt (fun y => Real.sin y / 4) (Real.cos y / 4) y :=
  (Real.hasDerivAt_sin y).div_const 4

private theorem shellCutoffDiff_hasDerivAt_cos4 (y : ℝ) :
    HasDerivAt (fun y => Real.cos y / 4) (-Real.sin y / 4) y := by
  have h := (Real.hasDerivAt_cos y).div_const 4
  exact h

/-- The profile `F_a` and its first three derivatives, in the chain-rule form. -/
private noncomputable def shellCutoffDiff_F0 (a c y : ℝ) : ℝ :=
  lowPass (a * shellCutoffDiff_T c y)

private noncomputable def shellCutoffDiff_F1 (a c y : ℝ) : ℝ :=
  lowPassD1 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4))

private noncomputable def shellCutoffDiff_F2 (a c y : ℝ) : ℝ :=
  lowPassD2 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4)) ^ 2
    + lowPassD1 (a * shellCutoffDiff_T c y) * (a * (Real.cos y / 4))

private noncomputable def shellCutoffDiff_F3 (a c y : ℝ) : ℝ :=
  lowPassD3 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4)) ^ 3
    + 3 * lowPassD2 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4))
        * (a * (Real.cos y / 4))
    + lowPassD1 (a * shellCutoffDiff_T c y) * (a * (-Real.sin y / 4))

private theorem shellCutoffDiff_hasDerivAt_aT (a c y : ℝ) :
    HasDerivAt (fun y => a * shellCutoffDiff_T c y) (a * (Real.sin y / 4)) y :=
  (shellCutoffDiff_hasDerivAt_T c y).const_mul a

private theorem shellCutoffDiff_hasDerivAt_F0 (a c y : ℝ) :
    HasDerivAt (shellCutoffDiff_F0 a c) (shellCutoffDiff_F1 a c y) y :=
  (hasDerivAt_lowPass _).comp y (shellCutoffDiff_hasDerivAt_aT a c y)

private theorem shellCutoffDiff_hasDerivAt_F1 (a c y : ℝ) :
    HasDerivAt (shellCutoffDiff_F1 a c) (shellCutoffDiff_F2 a c y) y := by
  have h1 : HasDerivAt (fun y => lowPassD1 (a * shellCutoffDiff_T c y))
      (lowPassD2 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4))) y :=
    (hasDerivAt_lowPassD1 _).comp y (shellCutoffDiff_hasDerivAt_aT a c y)
  have h2 : HasDerivAt (fun y => a * (Real.sin y / 4)) (a * (Real.cos y / 4)) y :=
    (shellCutoffDiff_hasDerivAt_sin4 y).const_mul a
  have h := h1.mul h2
  refine h.congr_deriv ?_
  simp only [shellCutoffDiff_F2]
  ring

private theorem shellCutoffDiff_hasDerivAt_F2 (a c y : ℝ) :
    HasDerivAt (shellCutoffDiff_F2 a c) (shellCutoffDiff_F3 a c y) y := by
  have hA : HasDerivAt (fun y => a * (Real.sin y / 4)) (a * (Real.cos y / 4)) y :=
    (shellCutoffDiff_hasDerivAt_sin4 y).const_mul a
  have hB : HasDerivAt (fun y => a * (Real.cos y / 4)) (a * (-Real.sin y / 4)) y :=
    (shellCutoffDiff_hasDerivAt_cos4 y).const_mul a
  have h2 : HasDerivAt (fun y => lowPassD2 (a * shellCutoffDiff_T c y))
      (lowPassD3 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4))) y :=
    (hasDerivAt_lowPassD2 _).comp y (shellCutoffDiff_hasDerivAt_aT a c y)
  have h1 : HasDerivAt (fun y => lowPassD1 (a * shellCutoffDiff_T c y))
      (lowPassD2 (a * shellCutoffDiff_T c y) * (a * (Real.sin y / 4))) y :=
    (hasDerivAt_lowPassD1 _).comp y (shellCutoffDiff_hasDerivAt_aT a c y)
  have h := (h2.mul (hA.pow 2)).add (h1.mul hB)
  refine h.congr_deriv ?_
  simp only [shellCutoffDiff_F3, Pi.pow_apply]
  ring

/-! ## Sharp derivative bounds for the profile -/

private theorem shellCutoffDiff_sin4_sq_le (c y : ℝ) (hc : c ≤ 1) :
    (Real.sin y / 4) ^ 2 ≤ shellCutoffDiff_T c y / 2 := by
  have h1 := Real.cos_le_one y
  have hsq : Real.sin y ^ 2 = 1 - Real.cos y ^ 2 := Real.sin_sq y
  unfold shellCutoffDiff_T
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h1)]

/-- Either all three low-pass derivatives vanish at `σ² t`, or `|σ² t′| ≤ σ`. -/
private theorem shellCutoffDiff_key (σ c y : ℝ) (hσ : 0 ≤ σ) (hc : c ≤ 1) :
    (lowPassD1 (σ ^ 2 * shellCutoffDiff_T c y) = 0 ∧
      lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y) = 0 ∧
      lowPassD3 (σ ^ 2 * shellCutoffDiff_T c y) = 0) ∨
    |σ ^ 2 * (Real.sin y / 4)| ≤ σ := by
  by_cases hx : 2 < σ ^ 2 * shellCutoffDiff_T c y
  · exact Or.inl (shellCutoffDiff_lowPassD_zero _ hx)
  · right
    push Not at hx
    have hT := shellCutoffDiff_sin4_sq_le c y hc
    have hσ2 : 0 ≤ σ ^ 2 := by positivity
    have hsq : (σ ^ 2 * (Real.sin y / 4)) ^ 2 ≤ σ ^ 2 := by
      have h1 : (σ ^ 2 * (Real.sin y / 4)) ^ 2 = σ ^ 4 * (Real.sin y / 4) ^ 2 := by ring
      have h2 : σ ^ 4 * (Real.sin y / 4) ^ 2 ≤ σ ^ 4 * (shellCutoffDiff_T c y / 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      have h3 : σ ^ 4 * (shellCutoffDiff_T c y / 2)
          = σ ^ 2 * (σ ^ 2 * shellCutoffDiff_T c y) / 2 := by ring
      rw [h1]
      nlinarith [mul_le_mul_of_nonneg_left hx hσ2]
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq hσ)

private theorem shellCutoffDiff_abs_cos4 (σ y : ℝ) :
    |σ ^ 2 * (Real.cos y / 4)| ≤ σ ^ 2 / 4 := by
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ ^ 2), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := Real.abs_cos_le_one y
  calc σ ^ 2 * (|Real.cos y| / 4) ≤ σ ^ 2 * (1 / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = σ ^ 2 / 4 := by ring

private theorem shellCutoffDiff_abs_negsin4 (σ y : ℝ) :
    |σ ^ 2 * (-Real.sin y / 4)| ≤ σ ^ 2 / 4 := by
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ ^ 2), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_neg]
  have := Real.abs_sin_le_one y
  calc σ ^ 2 * (|Real.sin y| / 4) ≤ σ ^ 2 * (1 / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = σ ^ 2 / 4 := by ring

private theorem shellCutoffDiff_abs_F1_le (σ c y : ℝ) (hσ : 0 ≤ σ) (hc : c ≤ 1) :
    |shellCutoffDiff_F1 (σ ^ 2) c y| ≤ 3 * σ := by
  unfold shellCutoffDiff_F1
  rcases shellCutoffDiff_key σ c y hσ hc with ⟨h1, -, -⟩ | hX
  · rw [h1, zero_mul, abs_zero]; positivity
  · rw [abs_mul]
    exact mul_le_mul (shellCutoffDiff_abs_lowPassD1_le _) hX (abs_nonneg _) (by norm_num)

private theorem shellCutoffDiff_abs_F2_le (σ c y : ℝ) (hσ : 0 ≤ σ) (hc : c ≤ 1) :
    |shellCutoffDiff_F2 (σ ^ 2) c y| ≤ 35 / 4 * σ ^ 2 := by
  unfold shellCutoffDiff_F2
  have hY := shellCutoffDiff_abs_cos4 σ y
  have hD1 := shellCutoffDiff_abs_lowPassD1_le (σ ^ 2 * shellCutoffDiff_T c y)
  have hD2 := shellCutoffDiff_abs_lowPassD2_le (σ ^ 2 * shellCutoffDiff_T c y)
  have hterm2 : |lowPassD1 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (Real.cos y / 4))|
      ≤ 3 * (σ ^ 2 / 4) := by
    rw [abs_mul]
    exact mul_le_mul hD1 hY (abs_nonneg _) (by norm_num)
  have hterm1 : |lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (Real.sin y / 4)) ^ 2|
      ≤ 8 * σ ^ 2 := by
    rcases shellCutoffDiff_key σ c y hσ hc with ⟨-, h2, -⟩ | hX
    · simp only [h2, zero_mul, abs_zero]; positivity
    · rw [abs_mul, abs_pow]
      have : |σ ^ 2 * (Real.sin y / 4)| ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hX 2
      exact mul_le_mul hD2 this (by positivity) (by norm_num)
  refine (abs_add_le _ _).trans ?_
  linarith

private theorem shellCutoffDiff_abs_F3_le (σ c y : ℝ) (hσ : 1 ≤ σ) (hc : c ≤ 1) :
    |shellCutoffDiff_F3 (σ ^ 2) c y| ≤ 40027 / 4 * σ ^ 3 := by
  unfold shellCutoffDiff_F3
  have hσ0 : 0 ≤ σ := by linarith
  have hZ := shellCutoffDiff_abs_negsin4 σ y
  have hY := shellCutoffDiff_abs_cos4 σ y
  have hD1 := shellCutoffDiff_abs_lowPassD1_le (σ ^ 2 * shellCutoffDiff_T c y)
  have hD2 := shellCutoffDiff_abs_lowPassD2_le (σ ^ 2 * shellCutoffDiff_T c y)
  have hD3 := abs_lowPassD3_le (σ ^ 2 * shellCutoffDiff_T c y)
  have hterm3 :
      |lowPassD1 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (-Real.sin y / 4))|
      ≤ 3 / 4 * σ ^ 3 := by
    rw [abs_mul]
    calc _ ≤ 3 * (σ ^ 2 / 4) := mul_le_mul hD1 hZ (abs_nonneg _) (by norm_num)
      _ ≤ 3 / 4 * σ ^ 3 := by
        nlinarith [sq_nonneg σ, mul_nonneg (sq_nonneg σ) (sub_nonneg.mpr hσ)]
  have hterm1 : |lowPassD3 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (Real.sin y / 4)) ^ 3|
      ≤ 10000 * σ ^ 3 := by
    rcases shellCutoffDiff_key σ c y hσ0 hc with ⟨-, -, h3⟩ | hX
    · rw [h3, zero_mul, abs_zero]; positivity
    · rw [abs_mul, abs_pow]
      have : |σ ^ 2 * (Real.sin y / 4)| ^ 3 ≤ σ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hX 3
      exact mul_le_mul hD3 this (by positivity) (by norm_num)
  have hterm2 : |3 * lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (Real.sin y / 4))
        * (σ ^ 2 * (Real.cos y / 4))| ≤ 6 * σ ^ 3 := by
    rcases shellCutoffDiff_key σ c y hσ0 hc with ⟨-, h2, -⟩ | hX
    · simp only [h2, mul_zero, zero_mul, abs_zero]; positivity
    · have h1 : |3 * lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y) * (σ ^ 2 * (Real.sin y / 4))
          * (σ ^ 2 * (Real.cos y / 4))|
          = 3 * |lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y)| * |σ ^ 2 * (Real.sin y / 4)|
            * |σ ^ 2 * (Real.cos y / 4)| := by
        simp only [abs_mul]; norm_num
      rw [h1]
      have h2 : 3 * |lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y)| ≤ 3 * 8 :=
        mul_le_mul_of_nonneg_left hD2 (by norm_num)
      have h3 : 3 * |lowPassD2 (σ ^ 2 * shellCutoffDiff_T c y)| * |σ ^ 2 * (Real.sin y / 4)|
          ≤ 3 * 8 * σ := mul_le_mul h2 hX (abs_nonneg _) (by norm_num)
      calc _ ≤ 3 * 8 * σ * (σ ^ 2 / 4) := mul_le_mul h3 hY (abs_nonneg _) (by positivity)
        _ = 6 * σ ^ 3 := by ring
  have hab : ∀ A B C : ℝ, |A + B + C| ≤ |A| + |B| + |C| := fun A B C =>
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  refine (hab _ _ _).trans ?_
  linarith

/-! ## Mean value bounds for iterated differences -/

private theorem shellCutoffDiff_abs_sub_le (f f' : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f' x| ≤ C) (x y : ℝ) :
    |f y - f x| ≤ C * |y - x| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := f) (x := x) (y := y) (C := C)
    (fun z _ => (hf z).differentiableAt)
    (fun z _ => by rw [(hf z).deriv]; simpa only [Real.norm_eq_abs] using hbound z)
    (by simp) (by simp)
  simpa only [Real.norm_eq_abs] using h

private theorem shellCutoffDiff_hasDerivAt_fwd (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h x : ℝ) :
    HasDerivAt (fun y => f (y + h) - f y) (f' (x + h) - f' x) x := by
  have hshift : HasDerivAt (fun y : ℝ => y + h) 1 x :=
    (hasDerivAt_id x).add_const h
  have hcomp := (hf (x + h)).comp x hshift
  convert hcomp.sub (hf x) using 1
  · funext y
    rfl
  · simp

private theorem shellCutoffDiff_diff1 (f f₁ : ℝ → ℝ) (C : ℝ)
    (h₀ : ∀ x, HasDerivAt f (f₁ x) x) (h₁ : ∀ x, |f₁ x| ≤ C) (t h : ℝ) :
    |f (t + h) - f t| ≤ C * |h| := by
  simpa using shellCutoffDiff_abs_sub_le f f₁ C h₀ h₁ t (t + h)

private theorem shellCutoffDiff_diff2 (f f₁ f₂ : ℝ → ℝ) (C : ℝ)
    (h₀ : ∀ x, HasDerivAt f (f₁ x) x) (h₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x, |f₂ x| ≤ C) (t h : ℝ) :
    |f (t + 2 * h) - 2 * f (t + h) + f t| ≤ C * |h| ^ 2 := by
  let F₀ : ℝ → ℝ := fun x => f (x + h) - f x
  let F₁ : ℝ → ℝ := fun x => f₁ (x + h) - f₁ x
  have hF₀ : ∀ x, HasDerivAt F₀ (F₁ x) x := fun x =>
    shellCutoffDiff_hasDerivAt_fwd f f₁ h₀ h x
  have hF₁bound (x : ℝ) : |F₁ x| ≤ C * |h| := by
    simpa [F₁] using shellCutoffDiff_abs_sub_le f₁ f₂ C h₁ h₂ x (x + h)
  have hlast := shellCutoffDiff_abs_sub_le F₀ F₁ (C * |h|) hF₀ hF₁bound t (t + h)
  have hrepr : F₀ (t + h) - F₀ t = f (t + 2 * h) - 2 * f (t + h) + f t := by
    dsimp [F₀]
    ring_nf
  rw [hrepr] at hlast
  calc |f (t + 2 * h) - 2 * f (t + h) + f t| ≤ (C * |h|) * |h| := by simpa using hlast
    _ = C * |h| ^ 2 := by ring

private theorem shellCutoffDiff_diff3 (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ)
    (h₀ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (h₃ : ∀ x, |f₃ x| ≤ C) (t h : ℝ) :
    |f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t|
      ≤ C * |h| ^ 3 := by
  let F₀ : ℝ → ℝ := fun x => f (x + h) - f x
  let F₁ : ℝ → ℝ := fun x => f₁ (x + h) - f₁ x
  let F₂ : ℝ → ℝ := fun x => f₂ (x + h) - f₂ x
  have hF₀ : ∀ x, HasDerivAt F₀ (F₁ x) x := fun x =>
    shellCutoffDiff_hasDerivAt_fwd f f₁ h₀ h x
  have hF₁ : ∀ x, HasDerivAt F₁ (F₂ x) x := fun x =>
    shellCutoffDiff_hasDerivAt_fwd f₁ f₂ h₁ h x
  have hF₂bound (x : ℝ) : |F₂ x| ≤ C * |h| := by
    simpa [F₂] using shellCutoffDiff_abs_sub_le f₂ f₃ C h₂ h₃ x (x + h)
  let G₀ : ℝ → ℝ := fun x => F₀ (x + h) - F₀ x
  let G₁ : ℝ → ℝ := fun x => F₁ (x + h) - F₁ x
  have hG₀ : ∀ x, HasDerivAt G₀ (G₁ x) x := fun x =>
    shellCutoffDiff_hasDerivAt_fwd F₀ F₁ hF₀ h x
  have hG₁bound (x : ℝ) : |G₁ x| ≤ C * |h| ^ 2 := by
    have hbound := shellCutoffDiff_abs_sub_le F₁ F₂ (C * |h|) hF₁ hF₂bound x (x + h)
    calc |G₁ x| ≤ (C * |h|) * |h| := by simpa [G₁] using hbound
      _ = C * |h| ^ 2 := by ring
  have hlast := shellCutoffDiff_abs_sub_le G₀ G₁ (C * |h| ^ 2) hG₀ hG₁bound t (t + h)
  have hrepr : G₀ (t + h) - G₀ t =
      f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t := by
    dsimp [G₀, F₀]
    ring_nf
  rw [hrepr] at hlast
  calc |f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t|
      ≤ (C * |h| ^ 2) * |h| := by simpa using hlast
    _ = C * |h| ^ 3 := by ring

/-! ## The real-variable difference bound for `G = F_{s²} - F_{(2s)²}` -/

private noncomputable def shellCutoffDiff_G (s c y : ℝ) : ℝ :=
  shellCutoffDiff_F0 (s ^ 2) c y - shellCutoffDiff_F0 ((2 * s) ^ 2) c y

private theorem shellCutoffDiff_real_diff (s c y h : ℝ) (hs : 1 ≤ s) (hc : c ≤ 1)
    (hh : 0 ≤ h) :
    |shellCutoffDiff_G s c (y + h) - shellCutoffDiff_G s c y| ≤ 9 * (h * s)
    ∧ |shellCutoffDiff_G s c (y + 2 * h) - 2 * shellCutoffDiff_G s c (y + h)
        + shellCutoffDiff_G s c y| ≤ 44 * (h * s) ^ 2
    ∧ |shellCutoffDiff_G s c (y + 3 * h) - 3 * shellCutoffDiff_G s c (y + 2 * h)
        + 3 * shellCutoffDiff_G s c (y + h) - shellCutoffDiff_G s c y|
          ≤ 90061 * (h * s) ^ 3 := by
  have hs0 : 0 ≤ s := by linarith
  have hs2 : 1 ≤ 2 * s := by linarith
  have hs20 : 0 ≤ 2 * s := by linarith
  have hd0 : ∀ y, HasDerivAt (shellCutoffDiff_G s c)
      (shellCutoffDiff_F1 (s ^ 2) c y - shellCutoffDiff_F1 ((2 * s) ^ 2) c y) y := fun y =>
    (shellCutoffDiff_hasDerivAt_F0 _ c y).sub (shellCutoffDiff_hasDerivAt_F0 _ c y)
  have hd1 : ∀ y, HasDerivAt
      (fun y => shellCutoffDiff_F1 (s ^ 2) c y - shellCutoffDiff_F1 ((2 * s) ^ 2) c y)
      (shellCutoffDiff_F2 (s ^ 2) c y - shellCutoffDiff_F2 ((2 * s) ^ 2) c y) y := fun y =>
    (shellCutoffDiff_hasDerivAt_F1 _ c y).sub (shellCutoffDiff_hasDerivAt_F1 _ c y)
  have hd2 : ∀ y, HasDerivAt
      (fun y => shellCutoffDiff_F2 (s ^ 2) c y - shellCutoffDiff_F2 ((2 * s) ^ 2) c y)
      (shellCutoffDiff_F3 (s ^ 2) c y - shellCutoffDiff_F3 ((2 * s) ^ 2) c y) y := fun y =>
    (shellCutoffDiff_hasDerivAt_F2 _ c y).sub (shellCutoffDiff_hasDerivAt_F2 _ c y)
  have hb1 : ∀ y, |shellCutoffDiff_F1 (s ^ 2) c y - shellCutoffDiff_F1 ((2 * s) ^ 2) c y|
      ≤ 9 * s := by
    intro y
    have h1 := shellCutoffDiff_abs_F1_le s c y hs0 hc
    have h2 := shellCutoffDiff_abs_F1_le (2 * s) c y hs20 hc
    have := abs_sub (shellCutoffDiff_F1 (s ^ 2) c y) (shellCutoffDiff_F1 ((2 * s) ^ 2) c y)
    linarith
  have hb2 : ∀ y, |shellCutoffDiff_F2 (s ^ 2) c y - shellCutoffDiff_F2 ((2 * s) ^ 2) c y|
      ≤ 44 * s ^ 2 := by
    intro y
    have h1 := shellCutoffDiff_abs_F2_le s c y hs0 hc
    have h2 := shellCutoffDiff_abs_F2_le (2 * s) c y hs20 hc
    have := abs_sub (shellCutoffDiff_F2 (s ^ 2) c y) (shellCutoffDiff_F2 ((2 * s) ^ 2) c y)
    nlinarith [sq_nonneg s]
  have hb3 : ∀ y, |shellCutoffDiff_F3 (s ^ 2) c y - shellCutoffDiff_F3 ((2 * s) ^ 2) c y|
      ≤ 90061 * s ^ 3 := by
    intro y
    have h1 := shellCutoffDiff_abs_F3_le s c y hs hc
    have h2 := shellCutoffDiff_abs_F3_le (2 * s) c y hs2 hc
    have := abs_sub (shellCutoffDiff_F3 (s ^ 2) c y) (shellCutoffDiff_F3 ((2 * s) ^ 2) c y)
    have hs3 : 0 ≤ s ^ 3 := by positivity
    nlinarith [hs3]
  have hh' : |h| = h := abs_of_nonneg hh
  refine ⟨?_, ?_, ?_⟩
  · have := shellCutoffDiff_diff1 _ _ (9 * s) hd0 hb1 y h
    rw [hh'] at this
    linarith
  · have := shellCutoffDiff_diff2 _ _ _ (44 * s ^ 2) hd0 hd1 hb2 y h
    rw [hh'] at this
    calc _ ≤ _ := this
      _ = 44 * (h * s) ^ 2 := by ring
  · have := shellCutoffDiff_diff3 _ _ _ _ (90061 * s ^ 3) hd0 hd1 hd2 hb3 y h
    rw [hh'] at this
    calc _ ≤ _ := this
      _ = 90061 * (h * s) ^ 3 := by ring

/-! ## From the lattice to the real variable -/

private theorem shellCutoffDiff_F0_congr (a c y y' : ℝ) (h : Real.cos y = Real.cos y') :
    shellCutoffDiff_F0 a c y = shellCutoffDiff_F0 a c y' := by
  unfold shellCutoffDiff_F0 shellCutoffDiff_T
  rw [h]

private theorem shellCutoffDiff_inv_dyad_succ (j : ℕ) :
    ((dyad (j + 1))⁻¹) ^ 2 = (2 * (dyad j)⁻¹) ^ 2 := by
  have h : dyad j ≠ 0 := (dyad_pos j).ne'
  have : dyad (j + 1) = dyad j / 2 := by
    unfold dyad
    rw [pow_succ]
    ring
  rw [this]
  field_simp

private theorem shellCutoffDiff_eq_fst (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) :
    shellCutoff L j p =
      shellCutoffDiff_G (dyad j)⁻¹ (Real.cos (2 * Real.pi * (p.2.val : ℝ) / L))
        (2 * Real.pi * (p.1.val : ℝ) / L) := by
  unfold shellCutoff shellCutoffDiff_G shellCutoffDiff_F0 shellCutoffDiff_T shellRadial qsym
  rw [shellCutoffDiff_inv_dyad_succ]
  congr 2 <;> ring_nf

private theorem shellCutoffDiff_eq_snd (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) :
    shellCutoff L j p =
      shellCutoffDiff_G (dyad j)⁻¹ (Real.cos (2 * Real.pi * (p.1.val : ℝ) / L))
        (2 * Real.pi * (p.2.val : ℝ) / L) := by
  unfold shellCutoff shellCutoffDiff_G shellCutoffDiff_F0 shellCutoffDiff_T shellRadial qsym
  rw [shellCutoffDiff_inv_dyad_succ]
  congr 2 <;> ring_nf

private theorem shellCutoffDiff_G_congr (s c y y' : ℝ) (h : Real.cos y = Real.cos y') :
    shellCutoffDiff_G s c y = shellCutoffDiff_G s c y' := by
  unfold shellCutoffDiff_G
  rw [shellCutoffDiff_F0_congr _ c y y' h, shellCutoffDiff_F0_congr _ c y y' h]

private theorem shellCutoffDiff_cos_val_add (L : ℕ) [NeZero L] (u : ZMod L) (m : ℕ) :
    Real.cos (2 * Real.pi * (((u + (m : ZMod L)).val : ℕ) : ℝ) / L)
      = Real.cos (2 * Real.pi * (u.val : ℝ) / L + (m : ℝ) * (2 * Real.pi / L)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
  have hu : u + (m : ZMod L) = ((u.val + m : ℕ) : ZMod L) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hu, ZMod.val_natCast]
  have hdm := Nat.mod_add_div (u.val + m) L
  have hcast : (((u.val + m) % L : ℕ) : ℝ) + (L : ℝ) * (((u.val + m) / L : ℕ) : ℝ)
      = (u.val : ℝ) + (m : ℝ) := by
    exact_mod_cast hdm
  have hr : (((u.val + m) % L : ℕ) : ℝ)
      = (u.val : ℝ) + (m : ℝ) - (L : ℝ) * (((u.val + m) / L : ℕ) : ℝ) := by linarith
  have harg : 2 * Real.pi * (((u.val + m) % L : ℕ) : ℝ) / L
      = (2 * Real.pi * (u.val : ℝ) / L + (m : ℝ) * (2 * Real.pi / L))
        - (((u.val + m) / L : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hr]
    field_simp
  rw [harg, Real.cos_sub_nat_mul_two_pi]

private theorem shellCutoffDiff_val_fst (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) (m : ℕ) :
    shellCutoff L j (p + m • ((1 : ZMod L), (0 : ZMod L))) =
      shellCutoffDiff_G (dyad j)⁻¹ (Real.cos (2 * Real.pi * (p.2.val : ℝ) / L))
        (2 * Real.pi * (p.1.val : ℝ) / L + (m : ℝ) * symbolGridStep L) := by
  rw [shellCutoffDiff_eq_fst]
  have h1 : (p + m • ((1 : ZMod L), (0 : ZMod L))).2 = p.2 := by simp
  have h2 : (p + m • ((1 : ZMod L), (0 : ZMod L))).1 = p.1 + (m : ZMod L) := by simp
  rw [h1, h2]
  apply shellCutoffDiff_G_congr
  rw [shellCutoffDiff_cos_val_add]
  rfl

private theorem shellCutoffDiff_val_snd (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) (m : ℕ) :
    shellCutoff L j (p + m • ((0 : ZMod L), (1 : ZMod L))) =
      shellCutoffDiff_G (dyad j)⁻¹ (Real.cos (2 * Real.pi * (p.1.val : ℝ) / L))
        (2 * Real.pi * (p.2.val : ℝ) / L + (m : ℝ) * symbolGridStep L) := by
  rw [shellCutoffDiff_eq_snd]
  have h1 : (p + m • ((0 : ZMod L), (1 : ZMod L))).1 = p.1 := by simp
  have h2 : (p + m • ((0 : ZMod L), (1 : ZMod L))).2 = p.2 + (m : ZMod L) := by simp
  rw [h1, h2]
  apply shellCutoffDiff_G_congr
  rw [shellCutoffDiff_cos_val_add]
  rfl

/-! ## The theorem -/

/-- Scale-uniform forward differences of the shell cutoff in a coordinate
direction: `|Δ^k χ_j| ≤ c_k (h / r)^k` with `h = 2π/L`, `r = 2^{-j}` and
`(c₁, c₂, c₃) = (9, 44, 90061)`.  The hypothesis `3 ≤ L` is not used. -/
theorem shellCutoff_fwdDiff_le :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) →
    ∀ (j : ℕ) (p : Z2 L),
      |(fwdDiff e)^[1] (shellCutoff L j) p| ≤ 9 * (symbolGridStep L / dyad j)
      ∧ |(fwdDiff e)^[2] (shellCutoff L j) p| ≤ 44 * (symbolGridStep L / dyad j) ^ 2
      ∧ |(fwdDiff e)^[3] (shellCutoff L j) p|
          ≤ 90061 * (symbolGridStep L / dyad j) ^ 3 := by
  intro L _ _ e he j p
  have hs : 1 ≤ (dyad j)⁻¹ := (one_le_inv₀ (dyad_pos j)).mpr (dyad_le_one j)
  have hh : 0 ≤ symbolGridStep L := by
    unfold symbolGridStep
    have := cast_L_pos L
    positivity
  rw [div_eq_mul_inv]
  have hval : ∃ (c x : ℝ), c ≤ 1 ∧ ∀ m : ℕ, shellCutoff L j (p + m • e)
      = shellCutoffDiff_G (dyad j)⁻¹ c (x + (m : ℝ) * symbolGridStep L) := by
    rcases he with rfl | rfl
    · exact ⟨_, _, Real.cos_le_one _, shellCutoffDiff_val_fst L j p⟩
    · exact ⟨_, _, Real.cos_le_one _, shellCutoffDiff_val_snd L j p⟩
  obtain ⟨c, x, hc, hv⟩ := hval
  obtain ⟨b1, b2, b3⟩ := shellCutoffDiff_real_diff (dyad j)⁻¹ c x (symbolGridStep L) hs hc hh
  have v0 : shellCutoff L j (p + 0 • e) = shellCutoffDiff_G (dyad j)⁻¹ c x := by
    simpa using hv 0
  have v1 : shellCutoff L j (p + 1 • e)
      = shellCutoffDiff_G (dyad j)⁻¹ c (x + symbolGridStep L) := by
    simpa using hv 1
  have v2 : shellCutoff L j (p + 2 • e)
      = shellCutoffDiff_G (dyad j)⁻¹ c (x + 2 * symbolGridStep L) := by
    simpa using hv 2
  have v3 : shellCutoff L j (p + 3 • e)
      = shellCutoffDiff_G (dyad j)⁻¹ c (x + 3 * symbolGridStep L) := by
    simpa using hv 3
  have k1 : (fwdDiff e)^[1] (shellCutoff L j) p
      = shellCutoff L j (p + 1 • e) - shellCutoff L j (p + 0 • e) := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul]
    norm_num [Nat.choose]
    ring
  have k2 : (fwdDiff e)^[2] (shellCutoff L j) p
      = shellCutoff L j (p + 2 • e) - 2 * shellCutoff L j (p + 1 • e)
        + shellCutoff L j (p + 0 • e) := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul]
    norm_num [Nat.choose]
    ring
  have k3 : (fwdDiff e)^[3] (shellCutoff L j) p
      = shellCutoff L j (p + 3 • e) - 3 * shellCutoff L j (p + 2 • e)
        + 3 * shellCutoff L j (p + 1 • e) - shellCutoff L j (p + 0 • e) := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul]
    norm_num [Nat.choose]
    ring
  rw [k1, k2, k3, v0, v1, v2, v3]
  exact ⟨b1, b2, b3⟩

end RBM
