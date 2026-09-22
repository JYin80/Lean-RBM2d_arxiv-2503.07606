/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# An explicit dyadic cutoff for Section 8.3

The seventh-degree smoothstep is flat to order three at both endpoints.
The radial cutoff is one on `(-∞,1]`, vanishes on `[2,∞)`, and its differences
give dyadic annuli. The finite partition identity below is exact; in T22 the
frequency variable must first be normalized into `[dyad J,1]`.
-/

namespace RBM

/-- Seventh-degree smoothstep with three flat derivatives at each endpoint. -/
def smoothstep3 (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

@[simp] theorem smoothstep3_zero : smoothstep3 0 = 0 := by norm_num [smoothstep3]
@[simp] theorem smoothstep3_one : smoothstep3 1 = 1 := by norm_num [smoothstep3]

/-- The first three polynomial derivatives of the smoothstep. -/
def smoothstep3D1 (x : ℝ) : ℝ :=
  140 * x ^ 3 - 420 * x ^ 4 + 420 * x ^ 5 - 140 * x ^ 6

def smoothstep3D2 (x : ℝ) : ℝ :=
  420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5

def smoothstep3D3 (x : ℝ) : ℝ :=
  840 * x - 5040 * x ^ 2 + 8400 * x ^ 3 - 4200 * x ^ 4

theorem hasDerivAt_smoothstep3 (x : ℝ) :
    HasDerivAt smoothstep3 (smoothstep3D1 x) x := by
  have h4 := (hasDerivAt_pow 4 x).const_mul (35 : ℝ)
  have h5 := (hasDerivAt_pow 5 x).const_mul (84 : ℝ)
  have h6 := (hasDerivAt_pow 6 x).const_mul (70 : ℝ)
  have h7 := (hasDerivAt_pow 7 x).const_mul (20 : ℝ)
  convert ((h4.sub h5).add h6).sub h7 using 1
  · funext y; dsimp [smoothstep3]
  · simp [smoothstep3D1]; ring

theorem hasDerivAt_smoothstep3D1 (x : ℝ) :
    HasDerivAt smoothstep3D1 (smoothstep3D2 x) x := by
  have h3 := (hasDerivAt_pow 3 x).const_mul (140 : ℝ)
  have h4 := (hasDerivAt_pow 4 x).const_mul (420 : ℝ)
  have h5 := (hasDerivAt_pow 5 x).const_mul (420 : ℝ)
  have h6 := (hasDerivAt_pow 6 x).const_mul (140 : ℝ)
  convert ((h3.sub h4).add h5).sub h6 using 1
  · funext y; dsimp [smoothstep3D1]
  · simp [smoothstep3D2]; ring

theorem hasDerivAt_smoothstep3D2 (x : ℝ) :
    HasDerivAt smoothstep3D2 (smoothstep3D3 x) x := by
  have h2 := (hasDerivAt_pow 2 x).const_mul (420 : ℝ)
  have h3 := (hasDerivAt_pow 3 x).const_mul (1680 : ℝ)
  have h4 := (hasDerivAt_pow 4 x).const_mul (2100 : ℝ)
  have h5 := (hasDerivAt_pow 5 x).const_mul (840 : ℝ)
  convert ((h2.sub h3).add h4).sub h5 using 1
  · funext y; dsimp [smoothstep3D2]
  · simp [smoothstep3D3]; ring

theorem smoothstep3D1_factor (x : ℝ) :
    smoothstep3D1 x = 140 * x ^ 3 * (1 - x) ^ 3 := by
  unfold smoothstep3D1
  ring

theorem smoothstep3D2_factor (x : ℝ) :
    smoothstep3D2 x = 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) := by
  unfold smoothstep3D2
  ring

theorem smoothstep3D3_factor (x : ℝ) :
    smoothstep3D3 x = 840 * x * (1 - x) * (1 - 5 * x + 5 * x ^ 2) := by
  unfold smoothstep3D3
  ring

@[simp] theorem smoothstep3D1_zero : smoothstep3D1 0 = 0 := by norm_num [smoothstep3D1]
@[simp] theorem smoothstep3D1_one : smoothstep3D1 1 = 0 := by norm_num [smoothstep3D1]
@[simp] theorem smoothstep3D2_zero : smoothstep3D2 0 = 0 := by norm_num [smoothstep3D2]
@[simp] theorem smoothstep3D2_one : smoothstep3D2 1 = 0 := by norm_num [smoothstep3D2]
@[simp] theorem smoothstep3D3_zero : smoothstep3D3 0 = 0 := by norm_num [smoothstep3D3]
@[simp] theorem smoothstep3D3_one : smoothstep3D3 1 = 0 := by norm_num [smoothstep3D3]

/-- Glue two functions at a breakpoint when their values and first
derivatives agree there. -/
private theorem hasDerivAt_ite_le (f g : ℝ → ℝ) (a d : ℝ)
    (heq : f a = g a) (hf : HasDerivAt f d a) (hg : HasDerivAt g d a) :
    HasDerivAt (fun x => if x ≤ a then f x else g x) d a := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hft := hasDerivAt_iff_tendsto_slope.mp hf
  have hgt := hasDerivAt_iff_tendsto_slope.mp hg
  intro s hs
  apply Filter.mem_map.mpr
  have hf' := Filter.mem_map.mp (hft hs)
  have hg' := Filter.mem_map.mp (hgt hs)
  filter_upwards [hf', hg'] with x hfx hgx
  by_cases hx : x ≤ a
  · change slope f a x ∈ s at hfx
    change slope (fun y => if y ≤ a then f y else g y) a x ∈ s
    convert hfx using 1
    simp [slope_def_field, hx]
  · change slope g a x ∈ s at hgx
    change slope (fun y => if y ≤ a then f y else g y) a x ∈ s
    convert hgx using 1
    simp [slope_def_field, hx, heq]

private theorem hasDerivAt_ite_le_global (f g f' g' : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hval : f a = g a) (hder : f' a = g' a) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ a then f y else g y)
      (if x ≤ a then f' x else g' x) x := by
  rcases lt_trichotomy x a with hlt | heq | hgt
  · have hxp : x ≤ a := hlt.le
    rw [ite_eq_left hxp]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hlt] with y hy
    simp [hy.le]
  · subst x
    rw [ite_eq_left le_rfl]
    exact hasDerivAt_ite_le f g a (f' a) hval (hf a) (hder.symm ▸ hg a)
  · have hxn : ¬ x ≤ a := not_le.mpr hgt
    rw [ite_eq_right hxn]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hgt] with y hy
    simp [not_le.mpr hy]

/-- Low-pass cutoff, with both boundary values assigned to the middle
polynomial consistently. -/
noncomputable def lowPass (t : ℝ) : ℝ :=
  if t ≤ 1 then 1 else if t ≤ 2 then 1 - smoothstep3 (t - 1) else 0

/-- Explicit first, second, and third derivatives of `lowPass`. -/
noncomputable def lowPassD1 (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t ≤ 2 then -smoothstep3D1 (t - 1) else 0

noncomputable def lowPassD2 (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t ≤ 2 then -smoothstep3D2 (t - 1) else 0

noncomputable def lowPassD3 (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t ≤ 2 then -smoothstep3D3 (t - 1) else 0

private theorem hasDerivAt_middle0 (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - smoothstep3 (y - 1))
      (-smoothstep3D1 (x - 1)) x := by
  have hi := (hasDerivAt_id x).sub_const (1 : ℝ)
  have h := (hasDerivAt_smoothstep3 (x - 1)).comp x hi
  simpa [Function.comp_def] using h.const_sub (1 : ℝ)

private theorem hasDerivAt_middle1 (x : ℝ) :
    HasDerivAt (fun y : ℝ => -smoothstep3D1 (y - 1))
      (-smoothstep3D2 (x - 1)) x := by
  have hi := (hasDerivAt_id x).sub_const (1 : ℝ)
  have h := (hasDerivAt_smoothstep3D1 (x - 1)).comp x hi
  convert h.neg using 1
  · funext y
    rfl
  · simp

private theorem hasDerivAt_middle2 (x : ℝ) :
    HasDerivAt (fun y : ℝ => -smoothstep3D2 (y - 1))
      (-smoothstep3D3 (x - 1)) x := by
  have hi := (hasDerivAt_id x).sub_const (1 : ℝ)
  have h := (hasDerivAt_smoothstep3D2 (x - 1)).comp x hi
  convert h.neg using 1
  · funext y
    rfl
  · simp

private theorem hasDerivAt_lowPassInner0 (x : ℝ) :
    HasDerivAt (fun y : ℝ => if y ≤ 2 then 1 - smoothstep3 (y - 1) else 0)
      (if x ≤ 2 then -smoothstep3D1 (x - 1) else 0) x := by
  apply hasDerivAt_ite_le_global
    (fun y => 1 - smoothstep3 (y - 1)) (fun _ => 0)
    (fun y => -smoothstep3D1 (y - 1)) (fun _ => 0) 2
    hasDerivAt_middle0 (fun y => hasDerivAt_const y 0)
  · norm_num
  · norm_num

private theorem hasDerivAt_lowPassInner1 (x : ℝ) :
    HasDerivAt (fun y : ℝ => if y ≤ 2 then -smoothstep3D1 (y - 1) else 0)
      (if x ≤ 2 then -smoothstep3D2 (x - 1) else 0) x := by
  apply hasDerivAt_ite_le_global
    (fun y => -smoothstep3D1 (y - 1)) (fun _ => 0)
    (fun y => -smoothstep3D2 (y - 1)) (fun _ => 0) 2
    hasDerivAt_middle1 (fun y => hasDerivAt_const y 0)
  · norm_num
  · norm_num

private theorem hasDerivAt_lowPassInner2 (x : ℝ) :
    HasDerivAt (fun y : ℝ => if y ≤ 2 then -smoothstep3D2 (y - 1) else 0)
      (if x ≤ 2 then -smoothstep3D3 (x - 1) else 0) x := by
  apply hasDerivAt_ite_le_global
    (fun y => -smoothstep3D2 (y - 1)) (fun _ => 0)
    (fun y => -smoothstep3D3 (y - 1)) (fun _ => 0) 2
    hasDerivAt_middle2 (fun y => hasDerivAt_const y 0)
  · norm_num
  · norm_num

/-- The seventh-degree transition really is `C³` across both seams. -/
theorem hasDerivAt_lowPass (x : ℝ) :
    HasDerivAt lowPass (lowPassD1 x) x := by
  change HasDerivAt
    (fun y : ℝ => if y ≤ 1 then 1 else
      if y ≤ 2 then 1 - smoothstep3 (y - 1) else 0)
    (if x ≤ 1 then 0 else if x ≤ 2 then -smoothstep3D1 (x - 1) else 0) x
  apply hasDerivAt_ite_le_global
    (fun _ => 1) (fun y => if y ≤ 2 then 1 - smoothstep3 (y - 1) else 0)
    (fun _ => 0) (fun y => if y ≤ 2 then -smoothstep3D1 (y - 1) else 0) 1
    (fun y => hasDerivAt_const y 1) hasDerivAt_lowPassInner0
  · norm_num
  · norm_num

theorem hasDerivAt_lowPassD1 (x : ℝ) :
    HasDerivAt lowPassD1 (lowPassD2 x) x := by
  change HasDerivAt
    (fun y : ℝ => if y ≤ 1 then 0 else
      if y ≤ 2 then -smoothstep3D1 (y - 1) else 0)
    (if x ≤ 1 then 0 else if x ≤ 2 then -smoothstep3D2 (x - 1) else 0) x
  apply hasDerivAt_ite_le_global
    (fun _ => 0) (fun y => if y ≤ 2 then -smoothstep3D1 (y - 1) else 0)
    (fun _ => 0) (fun y => if y ≤ 2 then -smoothstep3D2 (y - 1) else 0) 1
    (fun y => hasDerivAt_const y 0) hasDerivAt_lowPassInner1
  · norm_num
  · norm_num

theorem hasDerivAt_lowPassD2 (x : ℝ) :
    HasDerivAt lowPassD2 (lowPassD3 x) x := by
  change HasDerivAt
    (fun y : ℝ => if y ≤ 1 then 0 else
      if y ≤ 2 then -smoothstep3D2 (y - 1) else 0)
    (if x ≤ 1 then 0 else if x ≤ 2 then -smoothstep3D3 (x - 1) else 0) x
  apply hasDerivAt_ite_le_global
    (fun _ => 0) (fun y => if y ≤ 2 then -smoothstep3D2 (y - 1) else 0)
    (fun _ => 0) (fun y => if y ≤ 2 then -smoothstep3D3 (y - 1) else 0) 1
    (fun y => hasDerivAt_const y 0) hasDerivAt_lowPassInner2
  · norm_num
  · norm_num

private theorem continuous_ite_le (f g : ℝ → ℝ) (a : ℝ)
    (hf : Continuous f) (hg : Continuous g) (heq : f a = g a) :
    Continuous (fun x => if x ≤ a then f x else g x) := by
  apply Continuous.if _ hf hg
  intro x hx
  have hxa : x = a := by
    change x ∈ frontier (Set.Iic a) at hx
    simpa only [frontier_Iic, Set.mem_singleton_iff] using hx
  subst x
  exact heq

theorem continuous_lowPassD3 : Continuous lowPassD3 := by
  have hm : Continuous (fun x : ℝ => -smoothstep3D3 (x - 1)) := by
    unfold smoothstep3D3
    fun_prop
  have hi : Continuous (fun y : ℝ =>
      if y ≤ 2 then -smoothstep3D3 (y - 1) else 0) :=
    continuous_ite_le _ _ 2 hm continuous_const (by norm_num)
  change Continuous (fun y : ℝ => if y ≤ 1 then 0 else
    if y ≤ 2 then -smoothstep3D3 (y - 1) else 0)
  exact continuous_ite_le _ _ 1 continuous_const hi (by norm_num)

/-- The explicit low-pass cutoff is globally three times continuously
differentiable, including across the joins at radii `1` and `2`. -/
theorem contDiff_lowPass_three : ContDiff ℝ 3 lowPass := by
  have hD1 : deriv lowPass = lowPassD1 := by
    funext x
    exact (hasDerivAt_lowPass x).deriv
  have hD2 : deriv lowPassD1 = lowPassD2 := by
    funext x
    exact (hasDerivAt_lowPassD1 x).deriv
  have hD3 : deriv lowPassD2 = lowPassD3 := by
    funext x
    exact (hasDerivAt_lowPassD2 x).deriv
  have h2 : ContDiff ℝ 1 lowPassD2 :=
    contDiff_one_iff_deriv.mpr
      ⟨fun x => (hasDerivAt_lowPassD2 x).differentiableAt,
        by rw [hD3]; exact continuous_lowPassD3⟩
  have h1 : ContDiff ℝ (1 + 1) lowPassD1 := by
    apply (contDiff_succ_iff_deriv).2
    exact ⟨fun x => (hasDerivAt_lowPassD1 x).differentiableAt,
      by simp, by rw [hD2]; exact h2⟩
  change ContDiff ℝ (2 + 1) lowPass
  apply (contDiff_succ_iff_deriv).2
  exact ⟨fun x => (hasDerivAt_lowPass x).differentiableAt,
    by simp, by rw [hD1]; simpa [one_add_one_eq_two] using h1⟩

/-- The low-pass profile is nonincreasing. Its derivative is zero off the
transition interval and `-140 x³(1-x)³` inside it. -/
theorem lowPass_antitone : Antitone lowPass := by
  apply antitone_of_deriv_nonpos
    (fun x => (hasDerivAt_lowPass x).differentiableAt)
  intro x
  rw [(hasDerivAt_lowPass x).deriv]
  by_cases h1 : x ≤ 1
  · simp [lowPassD1, h1]
  by_cases h2 : x ≤ 2
  · have hx0 : 0 ≤ x - 1 := by linarith
    have hx1 : 0 ≤ 1 - (x - 1) := by linarith
    simp only [lowPassD1, ite_eq_right h1, ite_eq_left h2]
    rw [smoothstep3D1_factor]
    have hnonneg : 0 ≤ 140 * (x - 1) ^ 3 * (1 - (x - 1)) ^ 3 := by positivity
    linarith
  · simp [lowPassD1, h1, h2]

/-- A deliberately coarse absolute bound on the third derivative polynomial
on its unit interval. -/
theorem abs_smoothstep3D3_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |smoothstep3D3 x| ≤ 10000 := by
  have hx : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hx1⟩
  have h1x : |1 - x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hq : |1 - 5 * x + 5 * x ^ 2| ≤ 11 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x]
  rw [smoothstep3D3_factor]
  calc
    |840 * x * (1 - x) * (1 - 5 * x + 5 * x ^ 2)|
        = 840 * (|x| * |1 - x| * |1 - 5 * x + 5 * x ^ 2|) := by
          simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 840)]
          ring
    _ ≤ 840 * (1 * 1 * 11) := by gcongr
    _ ≤ 10000 := by norm_num

/-- The third derivative of the full piecewise cutoff is bounded globally. -/
theorem abs_lowPassD3_le (x : ℝ) : |lowPassD3 x| ≤ 10000 := by
  by_cases h1 : x ≤ 1
  · simp [lowPassD3, h1]
  by_cases h2 : x ≤ 2
  · have hx0 : 0 ≤ x - 1 := by linarith
    have hx1 : x - 1 ≤ 1 := by linarith
    simpa [lowPassD3, h1, h2] using abs_smoothstep3D3_le (x - 1) hx0 hx1
  · simp [lowPassD3, h1, h2]

private theorem abs_sub_le_mul_of_hasDerivAt (f f' : ℝ → ℝ) (C : ℝ)
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

/-- Three applications of the one-dimensional mean value bound give a cubic
finite-difference estimate from a bounded third derivative. -/
private theorem third_forward_difference_bound (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ)
    (h₀ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (h₃ : ∀ x, |f₃ x| ≤ C) (t h : ℝ) :
    |f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t|
      ≤ C * |h| ^ 3 := by
  let F₀ : ℝ → ℝ := fun x => f (x + h) - f x
  let F₁ : ℝ → ℝ := fun x => f₁ (x + h) - f₁ x
  let F₂ : ℝ → ℝ := fun x => f₂ (x + h) - f₂ x
  have hF₀ : ∀ x, HasDerivAt F₀ (F₁ x) x := by
    intro x
    exact hasDerivAt_forwardDifference f f₁ h₀ h x
  have hF₁ : ∀ x, HasDerivAt F₁ (F₂ x) x := by
    intro x
    exact hasDerivAt_forwardDifference f₁ f₂ h₁ h x
  have hF₂bound (x : ℝ) : |F₂ x| ≤ C * |h| := by
    simpa [F₂] using abs_sub_le_mul_of_hasDerivAt f₂ f₃ C h₂ h₃ x (x + h)
  let G₀ : ℝ → ℝ := fun x => F₀ (x + h) - F₀ x
  let G₁ : ℝ → ℝ := fun x => F₁ (x + h) - F₁ x
  have hG₀ : ∀ x, HasDerivAt G₀ (G₁ x) x := by
    intro x
    exact hasDerivAt_forwardDifference F₀ F₁ hF₀ h x
  have hG₁bound (x : ℝ) : |G₁ x| ≤ C * |h| ^ 2 := by
    have hbound := abs_sub_le_mul_of_hasDerivAt F₁ F₂ (C * |h|) hF₁ hF₂bound x (x + h)
    calc
      |G₁ x| ≤ (C * |h|) * |h| := by simpa [G₁] using hbound
      _ = C * |h| ^ 2 := by ring
  have hlast := abs_sub_le_mul_of_hasDerivAt G₀ G₁ (C * |h| ^ 2)
    hG₀ hG₁bound t (t + h)
  have hrepr : G₀ (t + h) - G₀ t =
      f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t := by
    dsimp [G₀, F₀]
    ring_nf
  rw [hrepr] at hlast
  calc
    |f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t|
        ≤ (C * |h| ^ 2) * |h| := by simpa using hlast
    _ = C * |h| ^ 3 := by ring

/-- Third forward difference, in the form used for a quantitative cutoff
estimate on a dyadic shell. -/
def thirdForwardDiff (f : ℝ → ℝ) (t h : ℝ) : ℝ :=
  f (t + 3 * h) - 3 * f (t + 2 * h) + 3 * f (t + h) - f t

/-- Explicit global cubic difference bound for the base low-pass cutoff. -/
theorem abs_lowPass_thirdForwardDiff_le (t h : ℝ) :
    |thirdForwardDiff lowPass t h| ≤ 10000 * |h| ^ 3 :=
  third_forward_difference_bound lowPass lowPassD1 lowPassD2 lowPassD3
    10000 hasDerivAt_lowPass hasDerivAt_lowPassD1 hasDerivAt_lowPassD2
    abs_lowPassD3_le t h

/-- Scaling the argument by a nonnegative factor multiplies the cubic
difference bound by its third power. -/
theorem abs_scaled_lowPass_thirdForwardDiff_le (a t h : ℝ) (ha : 0 ≤ a) :
    |thirdForwardDiff (fun x => lowPass (a * x)) t h|
      ≤ 10000 * a ^ 3 * |h| ^ 3 := by
  have hbase := abs_lowPass_thirdForwardDiff_le (a * t) (a * h)
  have heq : thirdForwardDiff (fun x => lowPass (a * x)) t h =
      thirdForwardDiff lowPass (a * t) (a * h) := by
    unfold thirdForwardDiff
    congr 1; ring_nf
  rw [heq]
  calc
    |thirdForwardDiff lowPass (a * t) (a * h)|
      ≤ 10000 * |a * h| ^ 3 := hbase
    _ = 10000 * a ^ 3 * |h| ^ 3 := by
      rw [abs_mul, abs_of_nonneg ha, mul_pow]
      ring

@[simp] theorem lowPass_eq_one_of_le_one {t : ℝ} (ht : t ≤ 1) :
    lowPass t = 1 := by simp [lowPass, ht]

@[simp] theorem lowPass_eq_zero_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    lowPass t = 0 := by
  by_cases h1 : t ≤ 1
  · linarith
  by_cases h2 : t ≤ 2
  · have : t = 2 := by linarith
    norm_num [lowPass, this, smoothstep3]
  · simp [lowPass, h1, h2]

/-- Annular cutoff at radius `dyad j = 2^{-j}`. -/
noncomputable def dyadicCutoff (j : ℕ) (t : ℝ) : ℝ :=
  lowPass ((dyad j)⁻¹ * t) - lowPass ((dyad (j + 1))⁻¹ * t)

theorem contDiff_dyadicCutoff_three (j : ℕ) :
    ContDiff ℝ 3 (dyadicCutoff j) := by
  unfold dyadicCutoff
  apply ContDiff.sub
  · exact contDiff_lowPass_three.comp (by fun_prop)
  · exact contDiff_lowPass_three.comp (by fun_prop)

/-- The annular weights telescope without any positivity assumption. -/
theorem sum_dyadicCutoff_range (n : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range n, dyadicCutoff j t =
      lowPass t - lowPass ((dyad n)⁻¹ * t) := by
  induction n with
  | zero => simp [dyad]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, dyadicCutoff]
      ring

/-- If the finest radius is no larger than `t`, all annuli together have
weight one. This is the exact partition statement consumed by T22. -/
theorem sum_dyadicCutoff_eq_one (J : ℕ) (t : ℝ)
    (hlow : dyad J ≤ t) (hhigh : t ≤ 1) :
    ∑ j ∈ Finset.range (J + 1), dyadicCutoff j t = 1 := by
  rw [sum_dyadicCutoff_range, lowPass_eq_one_of_le_one hhigh]
  have hJ : 0 < dyad J := dyad_pos J
  have hJ1 : dyad (J + 1) = dyad J / 2 := by
    simp [dyad, pow_succ]
    ring
  have hscaled : 2 ≤ (dyad (J + 1))⁻¹ * t := by
    rw [hJ1]
    rw [mul_comm]
    apply (le_mul_inv_iff₀ (by positivity : 0 < dyad J / 2)).2
    nlinarith
  rw [lowPass_eq_zero_of_two_le hscaled]
  ring

/-- The cutoff vanishes at and below its inner radius. -/
theorem dyadicCutoff_eq_zero_of_le_inner (j : ℕ) (t : ℝ)
    (ht : t ≤ dyad (j + 1)) : dyadicCutoff j t = 0 := by
  have hmono : dyad (j + 1) ≤ dyad j := dyad_le_dyad_of_le (Nat.le_succ j)
  have htj : t ≤ dyad j := ht.trans hmono
  have hscaled (k : ℕ) (hk : t ≤ dyad k) : (dyad k)⁻¹ * t ≤ 1 := by
    have hpos := dyad_pos k
    calc
      (dyad k)⁻¹ * t ≤ (dyad k)⁻¹ * dyad k :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  unfold dyadicCutoff
  rw [lowPass_eq_one_of_le_one (hscaled j htj),
    lowPass_eq_one_of_le_one (hscaled (j + 1) ht)]
  ring

/-- The cutoff vanishes at and above its outer radius. -/
theorem dyadicCutoff_eq_zero_of_outer_le (j : ℕ) (t : ℝ)
    (ht : 2 * dyad j ≤ t) : dyadicCutoff j t = 0 := by
  have hmono : dyad (j + 1) ≤ dyad j := dyad_le_dyad_of_le (Nat.le_succ j)
  have htj1 : 2 * dyad (j + 1) ≤ t := by nlinarith
  have hscaled (k : ℕ) (hk : 2 * dyad k ≤ t) :
      2 ≤ (dyad k)⁻¹ * t := by
    have hpos := dyad_pos k
    calc
      (2 : ℝ) = (dyad k)⁻¹ * (2 * dyad k) := by
        field_simp
      _ ≤ (dyad k)⁻¹ * t :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hpos.le)
  unfold dyadicCutoff
  rw [lowPass_eq_zero_of_two_le (hscaled j ht),
    lowPass_eq_zero_of_two_le (hscaled (j + 1) htj1)]
  ring

/-- Closed support inclusion for the annulus at scale `dyad j`. -/
theorem dyadicCutoff_support (j : ℕ) (t : ℝ)
    (h : dyadicCutoff j t ≠ 0) :
    dyad (j + 1) ≤ t ∧ t ≤ 2 * dyad j := by
  constructor
  · by_contra hlt
    exact h (dyadicCutoff_eq_zero_of_le_inner j t (le_of_lt (lt_of_not_ge hlt)))
  · by_contra hlt
    exact h (dyadicCutoff_eq_zero_of_outer_le j t (le_of_lt (lt_of_not_ge hlt)))

private theorem inv_dyad_succ (j : ℕ) :
    (dyad (j + 1))⁻¹ = 2 * (dyad j)⁻¹ := by
  rw [inv_dyad (j + 1), inv_dyad j, pow_succ]
  ring

/-- The low-pass cutoff takes values in the unit interval. -/
theorem lowPass_nonneg (t : ℝ) : 0 ≤ lowPass t := by
  by_cases ht : t ≤ 2
  · have h := lowPass_antitone ht
    rw [lowPass_eq_zero_of_two_le le_rfl] at h
    exact h
  · rw [lowPass_eq_zero_of_two_le (le_of_lt (lt_of_not_ge ht))]

theorem lowPass_le_one (t : ℝ) : lowPass t ≤ 1 := by
  by_cases ht : 1 ≤ t
  · have h := lowPass_antitone ht
    rw [lowPass_eq_one_of_le_one le_rfl] at h
    exact h
  · rw [lowPass_eq_one_of_le_one (le_of_lt (lt_of_not_ge ht))]

/-- Every annular cutoff is a nonnegative weight at every real radius. -/
theorem dyadicCutoff_nonneg (j : ℕ) (t : ℝ) :
    0 ≤ dyadicCutoff j t := by
  have hab : (dyad j)⁻¹ ≤ (dyad (j + 1))⁻¹ := by
    rw [inv_dyad_succ]
    have h : 0 ≤ (dyad j)⁻¹ := inv_nonneg.mpr (dyad_nonneg j)
    linarith
  by_cases ht : 0 ≤ t
  · have hscaled := mul_le_mul_of_nonneg_right hab ht
    exact sub_nonneg.mpr (lowPass_antitone hscaled)
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have hscaled (k : ℕ) : (dyad k)⁻¹ * t ≤ 1 := by
      have h := mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.mpr (dyad_nonneg k)) ht'
      linarith
    simp [dyadicCutoff, lowPass_eq_one_of_le_one (hscaled j),
      lowPass_eq_one_of_le_one (hscaled (j + 1))]

theorem dyadicCutoff_le_one (j : ℕ) (t : ℝ) :
    dyadicCutoff j t ≤ 1 := by
  unfold dyadicCutoff
  have h₁ := lowPass_le_one ((dyad j)⁻¹ * t)
  have h₀ := lowPass_nonneg ((dyad (j + 1))⁻¹ * t)
  linarith

/-- Quantitative third-difference estimate for the explicit dyadic annulus.
The constant `90000` is `10000 * (1 + 2³)` from its two low-pass edges. -/
theorem abs_dyadicCutoff_thirdForwardDiff_le (j : ℕ) (t h : ℝ) :
    |thirdForwardDiff (dyadicCutoff j) t h|
      ≤ 90000 * |h| ^ 3 * ((2 : ℝ) ^ j) ^ 3 := by
  let a : ℝ := (dyad j)⁻¹
  let b : ℝ := (dyad (j + 1))⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (dyad_nonneg j)
  have hb : 0 ≤ b := inv_nonneg.mpr (dyad_nonneg (j + 1))
  have hb2 : b = 2 * a := inv_dyad_succ j
  have hsplit : thirdForwardDiff (dyadicCutoff j) t h =
      thirdForwardDiff (fun x => lowPass (a * x)) t h -
        thirdForwardDiff (fun x => lowPass (b * x)) t h := by
    unfold thirdForwardDiff dyadicCutoff
    dsimp [a, b]
    ring_nf
  have hfirst := abs_scaled_lowPass_thirdForwardDiff_le a t h ha
  have hsecond := abs_scaled_lowPass_thirdForwardDiff_le b t h hb
  rw [hsplit]
  calc
    |thirdForwardDiff (fun x => lowPass (a * x)) t h -
        thirdForwardDiff (fun x => lowPass (b * x)) t h|
      ≤ |thirdForwardDiff (fun x => lowPass (a * x)) t h| +
          |thirdForwardDiff (fun x => lowPass (b * x)) t h| := abs_sub _ _
    _ ≤ 10000 * a ^ 3 * |h| ^ 3 + 10000 * b ^ 3 * |h| ^ 3 :=
      add_le_add hfirst hsecond
    _ = 90000 * |h| ^ 3 * ((2 : ℝ) ^ j) ^ 3 := by
      rw [hb2, show a = (2 : ℝ) ^ j by exact inv_dyad j]
      ring

/-- A concrete nonzero annular weight: the first shell at radius `1`. -/
example : dyadicCutoff 0 (1 : ℝ) = 1 := by
  norm_num [dyadicCutoff, dyad, lowPass, smoothstep3]

end RBM
