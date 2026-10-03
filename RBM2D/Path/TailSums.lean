/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Scales
import RBM2D.Loop.LatticeCount
import RBM2D.Defs.Dist
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tail sums of `𝒯_{u,D}` on `Z_L²`

The statements `ConvTailT`, `ConvSqrtTailT`, `TellStar`, proved with explicit constants.

Paper: arXiv:2503.07606, the convolution bound in the proof of `res_deccalE_lk` (before
(`mmxiaoxi`)), its square-root variant in the proof of `res_deccalE_wG` (near (`GGTLJ`)), and
(`Tell*`).

Results (namespace `RBM.Path`):
* `convTailT`     : `Σ_x 𝒯(a-x) 𝒯(x-b) ≤ 2500 ℓ_u² M_u^{-2} 𝒯(a-b)` if `L² ≤ W^{D-4}`;
* `convSqrtTailT` : `Σ_x (𝒯(a-x) 𝒯(x-b))^{1/2} ≤ 30000 ℓ_u² M_u^{-1} 𝒯(a-b)^{1/2}` if
  `L² ≤ W^{D/2-2}`;
* `tellStar`      : `𝒯(ℓ - C ℓ*_u) ≤ exp(√C (log W)^{3/4}) 𝒯(ℓ)` for `C ≥ 0`, `u < 1`.

Proof outline (a lattice version of the integrals of the paper, not the one-dimensional
integrals):
1. `√P + √Q ≥ √R + (4/7) min(√P, √Q)` when `R ≤ P + Q` (`sqrt_add_sqrt_ge`; `4/7 ≤ 2 - √2`), hence
   `e^{-s√P} e^{-s√Q} ≤ e^{-s√R} (e^{-(4s/7)√P} + e^{-(4s/7)√Q})` (`exp_mul_exp_le`);
2. at most `4r` points of `Z_L²` at distance `r ≥ 1` (section 3), so
   `Σ_x e^{-b√|x|_L} ≤ 1 + 4 Σ_{k ≥ 1} k e^{-b√k}`;
3. `k e^{-b√k} ≤ G(k)` with `G(x) = (x + b⁻²) e^{-b√x}` antitone, and `∫_0^a G ≤ 14 b⁻⁴` by the
   explicit antiderivative `psiFun`; hence `Σ_x e^{-b√|x|_L} ≤ 57 b⁻⁴` for `0 < b ≤ 1`;
4. the floor conditions and `M_u ≤ W²` absorb the `W^{-D}` parts.
-/

noncomputable section

namespace RBM.Path

open RBM RBM.Gauss

/-! ## Statements -/

/-- **The `𝒯 ⋆ 𝒯` bound**: `Σ_x 𝒯_{u,D}(a-x) 𝒯_{u,D}(x-b) ≤
2500 ℓ_u² M_u^{-2} 𝒯_{u,D}(a-b)`, under the floor condition `L² ≤ W^{D-4}`. -/
def ConvTailT : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E D u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (D - 4) → ∀ a b : Z2 L,
      ∑ x : Z2 L, tailT L W E D u (zdist2 L (a - x) : ℝ) * tailT L W E D u (zdist2 L (x - b) : ℝ) ≤
        2500 * ellT L u ^ 2 * (scaleM L W E u ^ 2)⁻¹ * tailT L W E D u (zdist2 L (a - b) : ℝ)

/-- **Square-root convolution** (Case 2 of `res_deccalE_wG`):
`Σ_x (𝒯(a-x) 𝒯(x-b))^{1/2} ≤ 30000 ℓ_u² M_u^{-1} 𝒯(a-b)^{1/2}` under `L² ≤ W^{D/2-2}`. -/
def ConvSqrtTailT : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E D u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (D / 2 - 2) → ∀ a b : Z2 L,
      ∑ x : Z2 L, Real.sqrt (tailT L W E D u (zdist2 L (a - x) : ℝ)) *
          Real.sqrt (tailT L W E D u (zdist2 L (x - b) : ℝ)) ≤
        30000 * ellT L u ^ 2 * (scaleM L W E u)⁻¹ *
          Real.sqrt (tailT L W E D u (zdist2 L (a - b) : ℝ))

/-- **The shift bound (`Tell*`)**, exact form: for `C ≥ 0`,
`𝒯_{u,D}(ℓ - C ℓ*_u) ≤ exp(√C (log W)^{3/4}) 𝒯_{u,D}(ℓ)`. -/
def TellStar : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E D u C ℓ : ℝ), u < 1 → 0 ≤ C →
    tailT L W E D u (ℓ - C * ellStar L W u) ≤
      Real.exp (Real.sqrt C * Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D u ℓ

/-! ## 1. Square-root inequalities -/

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem sqrt_add_le_add_sqrt' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

/-- The two-dimensional triangle trick: if `0 ≤ x ≤ y` then `√(x² + y²) ≤ y + (3/7) x`
(the constant `3/7 = 1 - κ` with `κ = 4/7 ≤ 2 - √2`). -/
private theorem sqrt_sq_add_sq_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤ y + 3 / 7 * x := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg hx (sub_nonneg.2 hxy)]

/-- For `0 ≤ P ≤ Q` and `R ≤ P + Q`: `√R + (4/7) √P ≤ √P + √Q`. -/
private theorem sqrt_add_sqrt_ge {P Q R : ℝ} (hP : 0 ≤ P) (hPQ : P ≤ Q) (hR : R ≤ P + Q) :
    Real.sqrt R + 4 / 7 * Real.sqrt P ≤ Real.sqrt P + Real.sqrt Q := by
  have hQ : 0 ≤ Q := hP.trans hPQ
  have h1 : Real.sqrt R ≤ Real.sqrt (P + Q) := Real.sqrt_le_sqrt hR
  have h2 : Real.sqrt P ≤ Real.sqrt Q := Real.sqrt_le_sqrt hPQ
  have h3 : P + Q = Real.sqrt P ^ 2 + Real.sqrt Q ^ 2 := by
    rw [Real.sq_sqrt hP, Real.sq_sqrt hQ]
  rw [h3] at h1
  have h4 := sqrt_sq_add_sq_le (Real.sqrt_nonneg P) h2
  linarith

/-- The exponential form of the triangle trick, for a scale `s ≥ 0`:
`e^{-s√P} e^{-s√Q} ≤ e^{-s√R} (e^{-(4s/7)√P} + e^{-(4s/7)√Q})` if `R ≤ P + Q`. -/
private theorem exp_mul_exp_le {P Q R s : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : R ≤ P + Q)
    (hs : 0 ≤ s) :
    Real.exp (-(s * Real.sqrt P)) * Real.exp (-(s * Real.sqrt Q)) ≤
      Real.exp (-(s * Real.sqrt R)) *
        (Real.exp (-(s * (4 / 7) * Real.sqrt P)) + Real.exp (-(s * (4 / 7) * Real.sqrt Q))) := by
  have e1 := Real.exp_pos (-(s * (4 / 7) * Real.sqrt P))
  have e2 := Real.exp_pos (-(s * (4 / 7) * Real.sqrt Q))
  have e3 := Real.exp_pos (-(s * Real.sqrt R))
  rw [← Real.exp_add]
  rcases le_total P Q with h | h
  · have hs1 := sqrt_add_sqrt_ge hP h hR
    have : Real.exp (-(s * Real.sqrt P) + -(s * Real.sqrt Q)) ≤
        Real.exp (-(s * Real.sqrt R)) * Real.exp (-(s * (4 / 7) * Real.sqrt P)) := by
      rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
    nlinarith
  · have hs1 := sqrt_add_sqrt_ge (R := R) hQ h (by linarith)
    have : Real.exp (-(s * Real.sqrt P) + -(s * Real.sqrt Q)) ≤
        Real.exp (-(s * Real.sqrt R)) * Real.exp (-(s * (4 / 7) * Real.sqrt Q)) := by
      rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
    nlinarith

/-! ## 2. The integral: `∫_0^a (x + b⁻²) e^{-b√x} dx ≤ 14 b⁻⁴` -/

/-- `H_b(s) = (s² + b⁻²) e^{-b s}`; it is antitone on `ℝ`. -/
private def hfun (b s : ℝ) : ℝ := (s ^ 2 + 1 / b ^ 2) * Real.exp (-(b * s))

private theorem hasDerivAt_hfun {b : ℝ} (hb : b ≠ 0) (s : ℝ) :
    HasDerivAt (hfun b)
      (-(1 / b) * (b * s - 1) ^ 2 * Real.exp (-(b * s))) s := by
  have h1 : HasDerivAt (fun s : ℝ => -(b * s)) (-(b * 1)) s :=
    ((hasDerivAt_id s).const_mul b).neg
  have h2 := h1.exp
  have h3 : HasDerivAt (fun s : ℝ => s ^ 2 + 1 / b ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (1 / b ^ 2)
  have h4 := h3.mul h2
  refine h4.congr_deriv ?_
  field_simp
  ring

private theorem antitone_hfun {b : ℝ} (hb : b ≠ 0) (hb0 : 0 < b) : Antitone (hfun b) := by
  refine antitone_of_deriv_nonpos (fun s => (hasDerivAt_hfun hb s).differentiableAt) fun s => ?_
  rw [(hasDerivAt_hfun hb s).deriv]
  have : 0 ≤ 1 / b * (b * s - 1) ^ 2 * Real.exp (-(b * s)) := by positivity
  linarith

/-- The antiderivative `Ψ_b(x) = -e^{-b√x}(2 s³/b + 6 s²/b² + 14 s/b³ + 14/b⁴)`, `s = √x`. -/
private def psiFun (b x : ℝ) : ℝ :=
  -(Real.exp (-(b * Real.sqrt x)) *
    (2 * Real.sqrt x ^ 3 / b + 6 * Real.sqrt x ^ 2 / b ^ 2 + 14 * Real.sqrt x / b ^ 3 +
      14 / b ^ 4))

private theorem hasDerivAt_psiFun {b x : ℝ} (hb : b ≠ 0) (hx : 0 < x) :
    HasDerivAt (psiFun b) ((x + 1 / b ^ 2) * Real.exp (-(b * Real.sqrt x))) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  set s := Real.sqrt x with hsdef
  have h1 : HasDerivAt (fun t : ℝ => -(b * t)) (-(b * 1)) s :=
    ((hasDerivAt_id s).const_mul b).neg
  have h2 := h1.exp
  have h3 : HasDerivAt
      (fun t : ℝ => 2 * t ^ 3 / b + 6 * t ^ 2 / b ^ 2 + 14 * t / b ^ 3 + 14 / b ^ 4)
      (2 * (3 * s ^ 2) / b + 6 * (2 * s) / b ^ 2 + 14 / b ^ 3) s := by
    have a1 : HasDerivAt (fun t : ℝ => 2 * t ^ 3 / b) (2 * (3 * s ^ 2) / b) s := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using
        ((hasDerivAt_pow 3 s).const_mul 2).div_const b
    have a2 : HasDerivAt (fun t : ℝ => 6 * t ^ 2 / b ^ 2) (6 * (2 * s) / b ^ 2) s := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using
        ((hasDerivAt_pow 2 s).const_mul 6).div_const (b ^ 2)
    have a3 : HasDerivAt (fun t : ℝ => 14 * t / b ^ 3) (14 / b ^ 3) s := by
      simpa using ((hasDerivAt_id s).const_mul 14).div_const (b ^ 3)
    exact ((a1.add a2).add a3).add_const _
  have h4 := (h2.mul h3).neg
  have h5 : HasDerivAt (fun t : ℝ => -(Real.exp (-(b * t)) *
      (2 * t ^ 3 / b + 6 * t ^ 2 / b ^ 2 + 14 * t / b ^ 3 + 14 / b ^ 4))) _ s := h4
  have h6 := h5.comp x hsq
  refine h6.congr_deriv ?_
  have hx2 : s ^ 2 = x := Real.sq_sqrt hx.le
  field_simp
  rw [← hx2]
  ring

private theorem continuous_psiFun (b : ℝ) : Continuous (psiFun b) := by
  unfold psiFun; fun_prop

/-- `∫_0^a (x + b⁻²) e^{-b√x} dx ≤ 14 b⁻⁴` for `a ≥ 0`, `b > 0`. -/
private theorem integral_G_le {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    ∫ x in (0 : ℝ)..a, (x + 1 / b ^ 2) * Real.exp (-(b * Real.sqrt x)) ≤ 14 / b ^ 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha
    (continuous_psiFun b).continuousOn (fun x hx => hasDerivAt_psiFun hb.ne' hx.1)]
  · have h0 : psiFun b 0 = -(14 / b ^ 4) := by simp [psiFun]
    have h1 : psiFun b a ≤ 0 := by
      unfold psiFun
      have := Real.sqrt_nonneg a
      have : 0 ≤ Real.exp (-(b * Real.sqrt a)) *
          (2 * Real.sqrt a ^ 3 / b + 6 * Real.sqrt a ^ 2 / b ^ 2 + 14 * Real.sqrt a / b ^ 3 +
            14 / b ^ 4) := by positivity
      linarith
    rw [h0]; linarith
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (x + 1 / b ^ 2) * Real.exp (-(b * Real.sqrt x))).intervalIntegrable _ _

/-- `Σ_{i<n} (i+1) e^{-b√(i+1)} ≤ 14 b⁻⁴`, uniformly in `n`. -/
private theorem sum_range_mul_exp_le {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * Real.exp (-(b * Real.sqrt ((i : ℝ) + 1))) ≤
      14 / b ^ 4 := by
  have hG : ∀ x : ℝ, 0 ≤ x →
      (x + 1 / b ^ 2) * Real.exp (-(b * Real.sqrt x)) = hfun b (Real.sqrt x) := by
    intro x hx; simp only [hfun, Real.sq_sqrt hx]
  have hanti : AntitoneOn (fun x : ℝ => (x + 1 / b ^ 2) * Real.exp (-(b * Real.sqrt x)))
      (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    simp only
    rw [hG x hx.1, hG y hy.1]
    exact antitone_hfun hb.ne' hb (Real.sqrt_le_sqrt hxy)
  have h := hanti.sum_le_integral (x₀ := 0) (a := n)
  have hint := integral_G_le hb (a := 0 + (n : ℝ)) (by positivity)
  refine le_trans ?_ (h.trans hint)
  refine Finset.sum_le_sum fun i _ => ?_
  push_cast
  rw [zero_add]
  have : (i : ℝ) + 1 ≤ (i : ℝ) + 1 + 1 / b ^ 2 := by
    have : 0 ≤ 1 / b ^ 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-! ## 3. Sphere counts on `Z_L²`

At most `2` points of `Z_L` at each one-dimensional distance `j ≥ 1` and one at `j = 0`, hence
at most `4r` points of `Z_L²` at distance `r ≥ 1` (the corresponding counts of `RBM.KLoop` in
`RBM2D/Loop/LatticeCount.lean` are `private`). -/

section Count

open Finset

/-- Bound on the number of points of `Z_L` at a given distance from `0`. -/
private def cnt (j : ℕ) : ℕ := if j = 0 then 1 else 2

private theorem cnt_zero : cnt 0 = 1 := by simp [cnt]

/-- Bound on the number of points of `Z_L²` at a given distance from `0`. -/
private def cnt2 (r : ℕ) : ℕ := ∑ i ∈ range (r + 1), cnt i * cnt (r - i)

private theorem cnt2_zero : cnt2 0 = 1 := by simp [cnt2, cnt]

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

private theorem sum_zdist2_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ x : Z2 L, f (zdist2 L x) ≤ ∑ r ∈ range (L + 1), (cnt2 r : ℝ) * f r := by
  rw [← sum_fiberwise_of_maps_to (g := zdist2 L) (t := range (L + 1))
    (fun y _ => mem_range.2 (Nat.lt_succ_of_le (RBM.KLoop.zdist2_le L y)))]
  refine sum_le_sum fun j _ => ?_
  have : ∑ y ∈ univ.filter (fun y : Z2 L => zdist2 L y = j), f (zdist2 L y)
      = ((univ.filter fun y : Z2 L => zdist2 L y = j).card : ℝ) * f j := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun y hy => by rw [(mem_filter.1 hy).2]
  rw [this]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (card_sphere2_le L j)) (hf j)

/-- `Σ_{x ∈ Z_L²} e^{-b √|x|_L} ≤ 57 b⁻⁴` for `0 < b ≤ 1`. -/
private theorem sum_exp_sqrt_zdist2_le (L : ℕ) [NeZero L] {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∑ x : Z2 L, Real.exp (-(b * Real.sqrt (zdist2 L x : ℝ))) ≤ 57 / b ^ 4 := by
  have h := sum_zdist2_le L (fun r : ℕ => Real.exp (-(b * Real.sqrt (r : ℝ))))
    (fun r => (Real.exp_pos _).le)
  refine h.trans ?_
  rw [sum_range_succ']
  have hpt : ∀ j ∈ range L, (cnt2 (j + 1) : ℝ) * Real.exp (-(b * Real.sqrt (((j + 1 : ℕ) : ℝ))))
      ≤ 4 * (((j : ℝ) + 1) * Real.exp (-(b * Real.sqrt ((j : ℝ) + 1)))) := by
    intro j _
    have hc : (cnt2 (j + 1) : ℝ) ≤ 4 * ((j : ℝ) + 1) := by
      have := cnt2_le (j + 1) (by omega)
      exact_mod_cast this
    push_cast
    calc (cnt2 (j + 1) : ℝ) * Real.exp (-(b * Real.sqrt ((j : ℝ) + 1)))
        ≤ (4 * ((j : ℝ) + 1)) * Real.exp (-(b * Real.sqrt ((j : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = _ := by ring
  have hsum := (sum_le_sum hpt).trans (le_of_eq (by rw [← mul_sum]))
  have h2 := sum_range_mul_exp_le hb L
  have hz : (cnt2 0 : ℝ) * Real.exp (-(b * Real.sqrt (((0 : ℕ) : ℝ)))) = 1 := by
    simp [cnt2_zero]
  rw [hz]
  have h3 : 1 ≤ 1 / b ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have : b ^ 4 ≤ 1 := pow_le_one₀ hb.le hb1
    linarith
  have h4 : 14 / b ^ 4 = 14 * (1 / b ^ 4) := by ring
  have h5 : 57 / b ^ 4 = 57 * (1 / b ^ 4) := by ring
  rw [h5]
  nlinarith

end Count

/-- Rescaled: for `0 < c ≤ 1`, `ℓ ≥ 1`, `Σ_x e^{-c √(|x|_L / ℓ)} ≤ 57 ℓ² c⁻⁴`. -/
private theorem sum_exp_sqrt_scaled_le (L : ℕ) [NeZero L] {c ℓ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hℓ : 1 ≤ ℓ) :
    ∑ x : Z2 L, Real.exp (-(c * Real.sqrt ((zdist2 L x : ℝ) / ℓ))) ≤ 57 * ℓ ^ 2 / c ^ 4 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hsl : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
  have hsl1 : 1 ≤ Real.sqrt ℓ := by
    rw [Real.one_le_sqrt]; exact hℓ
  have hb : 0 < c / Real.sqrt ℓ := div_pos hc hsl
  have hb1 : c / Real.sqrt ℓ ≤ 1 := by
    rw [div_le_one hsl]; linarith
  have e : ∀ u : Z2 L, Real.exp (-(c * Real.sqrt ((zdist2 L u : ℝ) / ℓ))) =
      Real.exp (-(c / Real.sqrt ℓ * Real.sqrt (zdist2 L u : ℝ))) := by
    intro u; rw [Real.sqrt_div' _ hℓ0.le]; ring_nf
  simp_rw [e]
  refine (sum_exp_sqrt_zdist2_le L hb hb1).trans (le_of_eq ?_)
  have h4 : Real.sqrt ℓ ^ 4 = ℓ ^ 2 := by
    have := Real.sq_sqrt hℓ0.le
    calc Real.sqrt ℓ ^ 4 = (Real.sqrt ℓ ^ 2) ^ 2 := by ring
      _ = ℓ ^ 2 := by rw [this]
  rw [div_pow, h4]
  field_simp

/-- Shifted: `Σ_x e^{-c √(|a - x|_L / ℓ)} ≤ 57 ℓ² c⁻⁴`. -/
private theorem sum_exp_sqrt_sub_left_le (L : ℕ) [NeZero L] {c ℓ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hℓ : 1 ≤ ℓ) (a : Z2 L) :
    ∑ x : Z2 L, Real.exp (-(c * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) ≤
      57 * ℓ ^ 2 / c ^ 4 := by
  have hre := Equiv.sum_comp (Equiv.subLeft a)
    (fun u : Z2 L => Real.exp (-(c * Real.sqrt ((zdist2 L u : ℝ) / ℓ))))
  simp only [Equiv.subLeft_apply] at hre
  rw [hre]
  exact sum_exp_sqrt_scaled_le L hc hc1 hℓ

/-- The same for `x - b`. -/
private theorem sum_exp_sqrt_sub_right_le (L : ℕ) [NeZero L] {c ℓ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hℓ : 1 ≤ ℓ) (b : Z2 L) :
    ∑ x : Z2 L, Real.exp (-(c * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) ≤
      57 * ℓ ^ 2 / c ^ 4 := by
  have hre := Equiv.sum_comp (Equiv.subRight b)
    (fun u : Z2 L => Real.exp (-(c * Real.sqrt ((zdist2 L u : ℝ) / ℓ))))
  simp only [Equiv.subRight_apply] at hre
  rw [hre]
  exact sum_exp_sqrt_scaled_le L hc hc1 hℓ

/-! ## 4. The convolution of two stretched exponentials -/

/-- `|a - b|_L ≤ |a - x|_L + |x - b|_L`. -/
private theorem zdist2_tri (L : ℕ) [NeZero L] (a b x : Z2 L) :
    (zdist2 L (a - b) : ℝ) ≤ (zdist2 L (a - x) : ℝ) + (zdist2 L (x - b) : ℝ) := by
  have h := zdist2_add_le L (a - x) (x - b)
  rw [sub_add_sub_cancel] at h
  exact_mod_cast h

/-- Pointwise triangle trick on the lattice, scale `s ≥ 0`. -/
private theorem pt_exp (L : ℕ) [NeZero L] {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 ≤ s) (a b x : Z2 L) :
    Real.exp (-(s * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) *
        Real.exp (-(s * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) ≤
      Real.exp (-(s * Real.sqrt ((zdist2 L (a - b) : ℝ) / ℓ))) *
        (Real.exp (-(s * (4 / 7) * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
          Real.exp (-(s * (4 / 7) * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) := by
  refine exp_mul_exp_le (div_nonneg (Nat.cast_nonneg _) hℓ.le)
    (div_nonneg (Nat.cast_nonneg _) hℓ.le) ?_ hs
  rw [← add_div]
  exact div_le_div_of_nonneg_right (zdist2_tri L a b x) hℓ.le

/-! ## 5. The scales -/

/-- `M_u ≤ W²` for `1 ≤ L`, `|E| < 2`, `u < 1` (`M_u = W² Im m min(1, L²(1-u))`, `Im m ≤ 1`). -/
private theorem scaleM_le_sq {L W : ℕ} {E u : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hu : u < 1) :
    scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  have him0 := spectralM_im_pos hE
  have him : (spectralM E).im ≤ 1 := by
    rw [spectralM_im, div_le_one (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have hx : 0 < 1 - u := by linarith
  have hmin0 : 0 ≤ min 1 ((L : ℝ) ^ 2 * (1 - u)) := le_min zero_le_one (by positivity)
  have hmin : min 1 ((L : ℝ) ^ 2 * (1 - u)) ≤ 1 := min_le_left _ _
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  rw [scaleM_eq hL hu]
  calc (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u))
      ≤ (W : ℝ) ^ 2 * 1 * 1 := by gcongr
    _ = (W : ℝ) ^ 2 := by ring

/-! ## 6. `convTailT` -/

/-- **`convTailT`**: the explicit form of
`Σ_x 𝒯(a₁ - x) 𝒯(a₂ - x) ≺ ℓ_u² M_u^{-2} 𝒯(a₁ - a₂)` (the convolution bound in the proof of
`res_deccalE_lk`), constant `2500`, under the floor `L² ≤ W^{D-4}`.  Writing
`𝒯 = A e^{-√·} + B`: the product sum is `A² Σ e e + A B Σ (e + e) + B² L²`; the first sum is
bounded via `pt_exp` (`s = 1`), the cross sums are `57 ℓ²` each, and the floor gives
`L² B ≤ ℓ² A`. -/
theorem convTailT : ConvTailT := by
  unfold ConvTailT
  intro L W _ _ E D u hE hu0 hu1 hfloor a b
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hL1 hu0 hu1
  have hM : 0 < scaleM L W E u := scaleM_pos hL1 hW1 hE hu1
  have hMW : scaleM L W E u ≤ (W : ℝ) ^ 2 := scaleM_le_sq hL1 hE hu1
  unfold tailT
  set ℓ := ellT L u with hℓdef
  set M := scaleM L W E u with hMdef
  set A : ℝ := (M ^ 2)⁻¹ with hA
  set B : ℝ := (W : ℝ) ^ (-D) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := (Real.rpow_pos_of_pos hW0 _).le
  have hℓ0 : 0 < ℓ := by linarith
  -- the floor
  have hfl : (L : ℝ) ^ 2 * B ≤ ℓ ^ 2 * A := by
    have h1 : (L : ℝ) ^ 2 * B ≤ (W : ℝ) ^ (D - 4) * (W : ℝ) ^ (-D) :=
      mul_le_mul_of_nonneg_right hfloor hB0
    have h2 : (W : ℝ) ^ (D - 4) * (W : ℝ) ^ (-D) = ((W : ℝ) ^ 4)⁻¹ := by
      rw [← Real.rpow_add hW0]
      have : D - 4 + -D = -((4 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg hW0.le, Real.rpow_natCast]
    have h3 : ((W : ℝ) ^ 4)⁻¹ ≤ A := by
      rw [hA]
      apply inv_anti₀ (by positivity)
      calc M ^ 2 ≤ ((W : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hM.le hMW 2
        _ = (W : ℝ) ^ 4 := by ring
    calc (L : ℝ) ^ 2 * B ≤ (W : ℝ) ^ (D - 4) * (W : ℝ) ^ (-D) := h1
      _ = ((W : ℝ) ^ 4)⁻¹ := h2
      _ ≤ A := h3
      _ ≤ ℓ ^ 2 * A := le_mul_of_one_le_left hA0 (by nlinarith)
  set e : ℝ := Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ℓ)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hpt : ∀ x : Z2 L,
      (A * Real.exp (-Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ)) + B) *
          (A * Real.exp (-Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)) + B) ≤
        A ^ 2 * e * (Real.exp (-((4 / 7) * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
            Real.exp (-((4 / 7) * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) +
          A * B * (Real.exp (-Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ)) +
            Real.exp (-Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) + B ^ 2 := by
    intro x
    have hc := pt_exp L hℓ0 (s := 1) zero_le_one a b x
    simp only [one_mul] at hc
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have := mul_le_mul_of_nonneg_left hc hA2
    nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, ZMod.card, nsmul_eq_mul] at hsum
  have sE1 := sum_exp_sqrt_sub_left_le L (c := 1) one_pos le_rfl hℓ1 a
  have sE2 := sum_exp_sqrt_sub_right_le L (c := 1) one_pos le_rfl hℓ1 b
  have sH1 := sum_exp_sqrt_sub_left_le L (c := 4 / 7) (by norm_num) (by norm_num) hℓ1 a
  have sH2 := sum_exp_sqrt_sub_right_le L (c := 4 / 7) (by norm_num) (by norm_num) hℓ1 b
  simp only [one_mul, one_pow, div_one] at sE1 sE2
  have hc4 : (4 / 7 : ℝ) ^ 4 = 256 / 2401 := by norm_num
  rw [hc4] at sH1 sH2
  have hl2 : 0 ≤ ℓ ^ 2 := by positivity
  have k1 : A ^ 2 * e *
      (∑ x : Z2 L, Real.exp (-((4 / 7) * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
        ∑ x : Z2 L, Real.exp (-((4 / 7) * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) ≤
      A ^ 2 * e * (1100 * ℓ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 57 * ℓ ^ 2 / (256 / 2401 : ℝ) ≤ 550 * ℓ ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have k2 : A * B * (∑ x : Z2 L, Real.exp (-Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ)) +
      ∑ x : Z2 L, Real.exp (-Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) ≤
      A * B * (114 * ℓ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have k3 : (L : ℝ) * L * B ^ 2 ≤ B * (ℓ ^ 2 * A) := by
    have := mul_le_mul_of_nonneg_left hfl hB0
    nlinarith
  push_cast at hsum
  have hAB : 0 ≤ A * B * ℓ ^ 2 := by positivity
  have hA2e : 0 ≤ A ^ 2 * e * ℓ ^ 2 := by positivity
  nlinarith

/-! ## 7. `convSqrtTailT` -/

/-- The abstract core of `convSqrtTailT`, with `α(d) = m⁻¹ e^{-√(d/ℓ)/2}`:
`Σ_x (α(a-x) + β)(α(x-b) + β) ≤ ℓ² m⁻¹ (17200 α(a-b) + 1825 β)`, if `L² β ≤ ℓ² m⁻¹`. -/
private theorem conv_sqrt_core (L : ℕ) [NeZero L] {ℓ m β : ℝ} (hℓ : 1 ≤ ℓ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hfl : (L : ℝ) ^ 2 * β ≤ ℓ ^ 2 * m⁻¹) (a b : Z2 L) :
    ∑ x : Z2 L,
        (m⁻¹ * Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) + β) *
          (m⁻¹ * Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) + β) ≤
      ℓ ^ 2 * m⁻¹ *
        (17200 * (m⁻¹ * Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - b) : ℝ) / ℓ)))) +
          1825 * β) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hmi : 0 < m⁻¹ := inv_pos.2 hm
  set e : ℝ := Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - b) : ℝ) / ℓ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hpt : ∀ x : Z2 L,
      (m⁻¹ * Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) + β) *
          (m⁻¹ * Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ))) + β) ≤
        m⁻¹ ^ 2 * e * (Real.exp (-(1 / 2 * (4 / 7) * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
            Real.exp (-(1 / 2 * (4 / 7) * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) +
          β * m⁻¹ * (Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
            Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) + β ^ 2 := by
    intro x
    have hc := pt_exp L hℓ0 (s := 1 / 2) (by norm_num) a b x
    have h2 := mul_le_mul_of_nonneg_left hc (sq_nonneg m⁻¹)
    nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, ZMod.card, nsmul_eq_mul] at hsum
  have sE1 := sum_exp_sqrt_sub_left_le L (c := 1 / 2) (by norm_num) (by norm_num) hℓ a
  have sE2 := sum_exp_sqrt_sub_right_le L (c := 1 / 2) (by norm_num) (by norm_num) hℓ b
  have sH1 := sum_exp_sqrt_sub_left_le L (c := 1 / 2 * (4 / 7)) (by norm_num) (by norm_num) hℓ a
  have sH2 := sum_exp_sqrt_sub_right_le L (c := 1 / 2 * (4 / 7)) (by norm_num) (by norm_num) hℓ b
  have hc4 : (1 / 2 * (4 / 7) : ℝ) ^ 4 = 16 / 2401 := by norm_num
  have hc4' : (1 / 2 : ℝ) ^ 4 = 1 / 16 := by norm_num
  rw [hc4] at sH1 sH2
  rw [hc4'] at sE1 sE2
  have hl2 : 0 ≤ ℓ ^ 2 := by positivity
  have k1 : m⁻¹ ^ 2 * e *
      (∑ x : Z2 L, Real.exp (-(1 / 2 * (4 / 7) * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
        ∑ x : Z2 L, Real.exp (-(1 / 2 * (4 / 7) * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) ≤
      m⁻¹ ^ 2 * e * (17200 * ℓ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 57 * ℓ ^ 2 / (16 / 2401 : ℝ) ≤ 8600 * ℓ ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have k2 : β * m⁻¹ *
      (∑ x : Z2 L, Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (a - x) : ℝ) / ℓ))) +
        ∑ x : Z2 L, Real.exp (-(1 / 2 * Real.sqrt ((zdist2 L (x - b) : ℝ) / ℓ)))) ≤
      β * m⁻¹ * (1824 * ℓ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 57 * ℓ ^ 2 / (1 / 16 : ℝ) = 912 * ℓ ^ 2 := by field_simp; ring
    linarith
  have k3 : (L : ℝ) * L * β ^ 2 ≤ β * (ℓ ^ 2 * m⁻¹) := by
    have := mul_le_mul_of_nonneg_left hfl hβ
    nlinarith
  push_cast at hsum
  have hAB : 0 ≤ β * m⁻¹ * ℓ ^ 2 := by positivity
  have hA2e : 0 ≤ m⁻¹ ^ 2 * e * ℓ ^ 2 := by positivity
  nlinarith

/-- **`convSqrtTailT`**: `Σ_x (𝒯(a-x) 𝒯(x-b))^{1/2} ≤ 30000 ℓ_u² M_u^{-1} 𝒯(a-b)^{1/2}`, under
the floor `L² ≤ W^{D/2-2}`.  Proof: `𝒯 = α² + β²` with `α = M⁻¹ e^{-√(·/ℓ)/2}`, `β = W^{-D/2}`;
`√𝒯 ≤ α + β`; `conv_sqrt_core`; and `α(a-b), β ≤ √𝒯(a-b)` (a bound by the larger of the two,
without a loss `√2`). -/
theorem convSqrtTailT : ConvSqrtTailT := by
  unfold ConvSqrtTailT
  intro L W _ _ E D u hE hu0 hu1 hfloor a b
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hL1 hu0 hu1
  have hM : 0 < scaleM L W E u := scaleM_pos hL1 hW1 hE hu1
  have hMW : scaleM L W E u ≤ (W : ℝ) ^ 2 := scaleM_le_sq hL1 hE hu1
  unfold tailT
  generalize ellT L u = ℓ at *
  generalize scaleM L W E u = M at *
  have hℓ0 : 0 < ℓ := by linarith
  have hMi : 0 < M⁻¹ := inv_pos.2 hM
  set β : ℝ := (W : ℝ) ^ (-D / 2) with hβ
  have hβ0 : 0 < β := Real.rpow_pos_of_pos hW0 _
  have hβ2 : β ^ 2 = (W : ℝ) ^ (-D) := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    congr 1; push_cast; ring
  have hfl : (L : ℝ) ^ 2 * β ≤ ℓ ^ 2 * M⁻¹ := by
    have h1 : (L : ℝ) ^ 2 * β ≤ (W : ℝ) ^ (D / 2 - 2) * β :=
      mul_le_mul_of_nonneg_right hfloor hβ0.le
    have h2 : (W : ℝ) ^ (D / 2 - 2) * β = ((W : ℝ) ^ 2)⁻¹ := by
      rw [hβ, ← Real.rpow_add hW0]
      have : D / 2 - 2 + -D / 2 = -((2 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg hW0.le, Real.rpow_natCast]
    have h3 : ((W : ℝ) ^ 2)⁻¹ ≤ M⁻¹ := inv_anti₀ hM hMW
    calc (L : ℝ) ^ 2 * β ≤ (W : ℝ) ^ (D / 2 - 2) * β := h1
      _ = ((W : ℝ) ^ 2)⁻¹ := h2
      _ ≤ M⁻¹ := h3
      _ ≤ ℓ ^ 2 * M⁻¹ := le_mul_of_one_le_left hMi.le (by nlinarith)
  set α : ℝ → ℝ := fun d => M⁻¹ * Real.exp (-(1 / 2 * Real.sqrt (d / ℓ))) with hα
  have hα0 : ∀ d, 0 ≤ α d := fun d => by simp only [hα]; positivity
  have htail : ∀ d : ℝ, (M ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / ℓ)) + (W : ℝ) ^ (-D) =
      α d ^ 2 + β ^ 2 := by
    intro d
    rw [hβ2]
    have h : Real.exp (-(1 / 2 * Real.sqrt (d / ℓ))) ^ 2 = Real.exp (-Real.sqrt (d / ℓ)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    simp only [hα]
    rw [mul_pow, inv_pow, h]
  have hsqrt : ∀ d : ℝ, Real.sqrt ((M ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / ℓ)) + (W : ℝ) ^ (-D)) ≤
      α d + β := by
    intro d
    rw [htail d, Real.sqrt_le_iff]
    refine ⟨by have := hα0 d; positivity, ?_⟩
    nlinarith [hα0 d]
  have hab : α ((zdist2 L (a - b) : ℕ) : ℝ) ≤
      Real.sqrt ((M ^ 2)⁻¹ * Real.exp (-Real.sqrt (((zdist2 L (a - b) : ℕ) : ℝ) / ℓ)) +
        (W : ℝ) ^ (-D)) := by
    rw [htail, Real.le_sqrt (hα0 _) (by positivity)]
    nlinarith [sq_nonneg β]
  have hβb : β ≤
      Real.sqrt ((M ^ 2)⁻¹ * Real.exp (-Real.sqrt (((zdist2 L (a - b) : ℕ) : ℝ) / ℓ)) +
        (W : ℝ) ^ (-D)) := by
    rw [htail, Real.le_sqrt hβ0.le (by positivity)]
    nlinarith [sq_nonneg (α ((zdist2 L (a - b) : ℕ) : ℝ))]
  have hcore := conv_sqrt_core L hℓ1 hM hβ0.le hfl a b
  refine le_trans (Finset.sum_le_sum fun x _ => ?_) (hcore.trans ?_)
  · have h0 := hα0 ((zdist2 L (a - x) : ℕ) : ℝ)
    exact mul_le_mul (hsqrt _) (hsqrt _) (Real.sqrt_nonneg _) (by positivity)
  · set T := Real.sqrt ((M ^ 2)⁻¹ * Real.exp (-Real.sqrt (((zdist2 L (a - b) : ℕ) : ℝ) / ℓ)) +
        (W : ℝ) ^ (-D)) with hT
    have hpos : 0 ≤ ℓ ^ 2 * M⁻¹ := by positivity
    have : 17200 * α ((zdist2 L (a - b) : ℕ) : ℝ) + 1825 * β ≤ 30000 * T := by
      nlinarith [hα0 ((zdist2 L (a - b) : ℕ) : ℝ)]
    calc ℓ ^ 2 * M⁻¹ * (17200 * (M⁻¹ * Real.exp
            (-(1 / 2 * Real.sqrt (((zdist2 L (a - b) : ℕ) : ℝ) / ℓ)))) + 1825 * β)
        = ℓ ^ 2 * M⁻¹ * (17200 * α ((zdist2 L (a - b) : ℕ) : ℝ) + 1825 * β) := rfl
      _ ≤ ℓ ^ 2 * M⁻¹ * (30000 * T) := mul_le_mul_of_nonneg_left this hpos
      _ = 30000 * ℓ ^ 2 * M⁻¹ * T := by ring

/-! ## 8. `tellStar` -/

/-- `√((log W)^{3/2}) = (log W)^{3/4}` for `W ≥ 1`. -/
private theorem sqrt_log_rpow_three_halves' {W : ℝ} (hW : 1 ≤ W) :
    Real.sqrt (Real.log W ^ ((3 : ℝ) / 2)) = Real.log W ^ ((3 : ℝ) / 4) := by
  have hl : 0 ≤ Real.log W := Real.log_nonneg hW
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hl]
  norm_num

/-- **`tellStar`**: `𝒯_{u,D}(ℓ - C ℓ*_u) ≤ exp(√C (log W)^{3/4}) 𝒯_{u,D}(ℓ)` for `C ≥ 0`
(`Tell*`), in the explicit form; only `u < 1` and `0 ≤ C` are used. -/
theorem tellStar : TellStar := by
  unfold TellStar
  intro L W _ _ E D u C ℓ hu hC
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hℓu : 0 < ellT L u := (ellT_pos_le hL1 hu).1
  have hl : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg hW1'
  set s : ℝ := C * Real.log (W : ℝ) ^ ((3 : ℝ) / 2) with hs
  have hs0 : 0 ≤ s := by positivity
  have hsqrt : Real.sqrt s = Real.sqrt C * Real.log (W : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [hs, Real.sqrt_mul hC, sqrt_log_rpow_three_halves' hW1']
  have hsplit : ℓ / ellT L u = (ℓ - C * ellStar L W u) / ellT L u + s := by
    rw [ellStar, hs]; field_simp; ring
  have hkey : Real.sqrt (ℓ / ellT L u) ≤
      Real.sqrt ((ℓ - C * ellStar L W u) / ellT L u) + Real.sqrt s := by
    have h := sqrt_add_le_add_sqrt' (x := max ((ℓ - C * ellStar L W u) / ellT L u) 0)
      (y := s) (le_max_right _ _) hs0
    have h1 : Real.sqrt (ℓ / ellT L u) ≤
        Real.sqrt (max ((ℓ - C * ellStar L W u) / ellT L u) 0 + s) := by
      apply Real.sqrt_le_sqrt
      rw [hsplit]
      linarith [le_max_left ((ℓ - C * ellStar L W u) / ellT L u) 0]
    have h2 : Real.sqrt (max ((ℓ - C * ellStar L W u) / ellT L u) 0) =
        Real.sqrt ((ℓ - C * ellStar L W u) / ellT L u) := by
      rcases le_total ((ℓ - C * ellStar L W u) / ellT L u) 0 with h | h
      · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
      · rw [max_eq_left h]
    linarith
  have hexp : Real.exp (-Real.sqrt ((ℓ - C * ellStar L W u) / ellT L u)) ≤
      Real.exp (Real.sqrt s) * Real.exp (-Real.sqrt (ℓ / ellT L u)) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have h1 : 1 ≤ Real.exp (Real.sqrt s) := Real.one_le_exp (Real.sqrt_nonneg _)
  have hA : 0 ≤ (scaleM L W E u ^ 2)⁻¹ := by positivity
  have hε : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  rw [← hsqrt]
  unfold tailT
  have := mul_le_mul_of_nonneg_left hexp hA
  nlinarith

end RBM.Path
