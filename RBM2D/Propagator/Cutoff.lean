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
give dyadic annuli. The finite partition identity below is exact; the frequency variable must first
be normalized into `[dyad J,1]` before it is applied.
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

end RBM
