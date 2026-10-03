/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.UBounds
import RBM2D.Path.Scales
import RBM2D.Path.Kernel
import RBM2D.Defs.Dist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Transport by the `𝒰` kernel: local-maximum bounds and `TailtoTail`

The definitions `UkerFar`, `UopLocalMax`, `UopPairLocalMax`, `TailtoTail`, each proved.

Paper: arXiv:2503.07606, (`res_deccalE_0`), (`res_deccalE_3`), and (`neiwuj`) in Lemma
`TailtoTail`.

* `uopLocalMax`, `uopPairLocalMax` : nonnegativity (`ukerNonneg`) and row sums (`ukerRowSum`) of
  `ukerMat` give weight `((1-u)/(1-v))^k` to the near labels; the far labels cost
  `L² W^{-D'}` per coordinate (only `card (Z2 L) = L²` is used).
* `tailtoTail` : `uopLocalMax` at radius `ℓ*_t/4`, then the exponent comparison of `neiwuj` with
  the explicit constant `30000 e^{(log W)^{3/4}}`.  Neither of the two `d = 2` adjustments
  mentioned after Lemma `TailtoTail` (the sup-norm bound `‖Θ_t‖_max ≺ ℓ_t^{-2} η_t^{-1}` and the
  ball count) is used: the far region is the hypothesis `UkerFar`.

`RBM.KLoop` is not opened.
-/

noncomputable section

namespace RBM.Path

open RBM RBM.Gauss

/-! ## Definitions -/

/-- The far-kernel condition: `(Θ_u^{-1}Θ_v)_{ab} ≤ W^{-D'}` for `|a - b|_L ≥ R`
(supplied by `KellStarEv`). -/
def UkerFar (L W : ℕ) [NeZero L] (u v R D' : ℝ) : Prop :=
  ∀ a b : Z2 L, R ≤ (zdist2 L (a - b) : ℝ) → ‖ukerMat L 1 u v a b‖ ≤ (W : ℝ) ^ (-D')

/-- **Transport by the local maximum** (`res_deccalE_0`): near labels carry the weight
`((1-u)/(1-v))²`, far labels cost `2 L² W^{-D'} (1-u)/(1-v) ‖A‖_max`. -/
def UopLocalMax : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar L W u v R D' → ∀ (A : Z2 L × Z2 L → ℂ) (α β : ℝ) (a : Z2 L × Z2 L), 0 ≤ β →
      (∀ b, ‖A b‖ ≤ α) →
      (∀ b : Z2 L × Z2 L, (zdist2 L (a.1 - b.1) : ℝ) < R → (zdist2 L (a.2 - b.2) : ℝ) < R →
        ‖A b‖ ≤ β) →
      ‖Uop L 1 u v A a‖ ≤
        ((1 - u) / (1 - v)) ^ 2 * β + 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) * α

/-- **The same for `𝒰 ⊗ 𝒰̄`**, used by the QV (`res_deccalE_3`). -/
def UopPairLocalMax : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar L W u v R D' →
    ∀ (A : Z2 L × Z2 L → Z2 L × Z2 L → ℂ) (α β : ℝ) (a : Z2 L × Z2 L), 0 ≤ β →
      (∀ b b', ‖A b b'‖ ≤ α) →
      (∀ b b' : Z2 L × Z2 L, (zdist2 L (a.1 - b.1) : ℝ) < R → (zdist2 L (a.2 - b.2) : ℝ) < R →
        (zdist2 L (a.1 - b'.1) : ℝ) < R → (zdist2 L (a.2 - b'.2) : ℝ) < R → ‖A b b'‖ ≤ β) →
      ‖∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          ukerMat L 1 u v a.1 b.1 * ukerMat L 1 u v a.2 b.2 *
            (starRingEnd ℂ) (ukerMat L 1 u v a.1 b'.1 * ukerMat L 1 u v a.2 b'.2) * A b b'‖ ≤
        ((1 - u) / (1 - v)) ^ 4 * β +
          4 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) ^ 3 * α

/-- **`TailtoTail`** (`neiwuj`, `d = 2`): for `|a₁ - a₂| ≥ ℓ*_t`,
`(𝒰_{s,t} A)_a ≤ 30000 e^{(log W)^{3/4}} M_t^{-2} e^{-(|a₁-a₂|/ℓ_t)^{1/2}}
  + 2 (η_s/η_t)² W^{-D}`. -/
def TailtoTail : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E D D' s t : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ D → 0 ≤ s →
    s ≤ t → t < 1 → 4 ≤ Real.log W → 1 ≤ scaleM L W E t →
    UkerFar L W s t (ellStar L W t / 4) D' → 4 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) →
    ∀ A : Z2 L × Z2 L → ℂ, (∀ b, ‖A b‖ ≤ tailT L W E D s (zdist2 L (b.1 - b.2) : ℝ)) →
    ∀ a : Z2 L × Z2 L, ellStar L W t ≤ (zdist2 L (a.1 - a.2) : ℝ) →
      ‖Uop L 1 s t A a‖ ≤
        30000 * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * (scaleM L W E t ^ 2)⁻¹ *
            Real.exp (-Real.sqrt ((zdist2 L (a.1 - a.2) : ℝ) / ellT L t)) +
          2 * (etaT E s / etaT E t) ^ 2 * (W : ℝ) ^ (-D)

/-! ## Private helpers -/

section Helpers

variable (L : ℕ) [NeZero L]

/-- `‖z‖ = re z` for `im z = 0`, `0 ≤ re z`. -/
private theorem uT_norm_eq_re_of {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  calc ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
    _ = z.re := Complex.norm_of_nonneg hre

/-- The row `ℓ¹` norm of `ukerMat L 1 u v` is the row sum `(1 - u)/(1 - v)` (`ukerNonneg`,
`ukerRowSum` at `ξ = 1`). -/
private theorem uT_row_sum (hL : 3 ≤ L) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1)
    (x : Z2 L) : ∑ c : Z2 L, ‖ukerMat L 1 u v x c‖ = (1 - u) / (1 - v) := by
  have hvξ : v * (1 : ℝ) < 1 := by rw [mul_one]; exact hv
  have hn : ∀ c : Z2 L, ‖ukerMat L 1 u v x c‖ = (ukerMat L 1 u v x c).re := by
    intro c
    have h := ukerNonneg L hL 1 u v zero_le_one hu huv hvξ x c
    rw [Complex.ofReal_one] at h
    exact uT_norm_eq_re_of h.1 h.2
  simp_rw [hn]
  have hs := ukerRowSum L hL 1 u v zero_le_one (hu.trans huv) hvξ x
  rw [Complex.ofReal_one] at hs
  have hre := congrArg Complex.re hs
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  simpa only [mul_one] using hre

/-- The far indicator `1[R ≤ |a - c|_L]` as a real number. -/
private def uTF (a : Z2 L) (R : ℝ) (c : Z2 L) : ℝ :=
  if R ≤ (zdist2 L (a - c) : ℝ) then 1 else 0

omit [NeZero L] in
private theorem uTF_nonneg (a : Z2 L) (R : ℝ) (c : Z2 L) : 0 ≤ uTF L a R c := by
  unfold uTF; split_ifs <;> norm_num

omit [NeZero L] in
private theorem uTF_eq_one {a : Z2 L} {R : ℝ} {c : Z2 L} (h : R ≤ (zdist2 L (a - c) : ℝ)) :
    uTF L a R c = 1 := by
  unfold uTF; simp [h]

omit [NeZero L] in
private theorem uTF_eq_zero {a : Z2 L} {R : ℝ} {c : Z2 L} (h : (zdist2 L (a - c) : ℝ) < R) :
    uTF L a R c = 0 := by
  unfold uTF; simp [not_le.2 h]

/-- The far part of a nonnegative weight with pointwise far bound `δ` costs at most `L² δ`
(only `card (Z2 L) = L²` is used). -/
private theorem uT_far_sum_le (a : Z2 L) (R δ : ℝ) (hδ : 0 ≤ δ) (k : Z2 L → ℝ)
    (hk : ∀ c, R ≤ (zdist2 L (a - c) : ℝ) → k c ≤ δ) :
    ∑ c : Z2 L, k c * uTF L a R c ≤ (L : ℝ) ^ 2 * δ := by
  have hterm : ∀ c : Z2 L, k c * uTF L a R c ≤ δ := by
    intro c
    by_cases h : R ≤ (zdist2 L (a - c) : ℝ)
    · rw [uTF_eq_one L h, mul_one]; exact hk c h
    · rw [uTF_eq_zero L (not_le.1 h), mul_zero]; exact hδ
  calc ∑ c : Z2 L, k c * uTF L a R c ≤ ∑ _c : Z2 L, δ := Finset.sum_le_sum fun c _ => hterm c
    _ = (L : ℝ) ^ 2 * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
        push_cast; ring

/-- The two-slot sum over `Z2 L × Z2 L` of a product is the product of the sums. -/
private theorem uT_sum2 (p q : Z2 L → ℝ) :
    ∑ b : Z2 L × Z2 L, p b.1 * q b.2 = (∑ x, p x) * ∑ y, q y := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The four-slot double sum of a product is the product of the four sums. -/
private theorem uT_sum4 (p q r s : Z2 L → ℝ) :
    ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L, p b.1 * q b.2 * (r b'.1 * s b'.2) =
      ((∑ x, p x) * ∑ y, q y) * ((∑ x, r x) * ∑ y, s y) := by
  have h : ∀ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L, p b.1 * q b.2 * (r b'.1 * s b'.2) =
      p b.1 * q b.2 * ∑ b' : Z2 L × Z2 L, r b'.1 * s b'.2 :=
    fun b => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl fun b _ => h b, ← Finset.sum_mul, uT_sum2 L p q, uT_sum2 L r s]

end Helpers

/-! ## The theorems -/

/-- **`uopLocalMax`** (`res_deccalE_0`): nonnegativity and row sums of `ukerMat` give the
near labels the weight `((1-u)/(1-v))²`; the far labels cost `L² W^{-D'}` per coordinate. -/
theorem uopLocalMax : UopLocalMax := by
  intro L W _ _ hL u v R D' hu huv hv hFar A α β a hβ hα hnear
  have hr0 : 0 ≤ (1 - u) / (1 - v) := div_nonneg (by linarith) (by linarith)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα a)
  have hδ : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg W) _
  obtain ⟨k₁, hk₁⟩ : ∃ k : Z2 L → ℝ, ∀ c, k c = ‖ukerMat L 1 u v a.1 c‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : Z2 L → ℝ, ∀ c, k c = ‖ukerMat L 1 u v a.2 c‖ := ⟨_, fun _ => rfl⟩
  have hk₁0 : ∀ c, 0 ≤ k₁ c := fun c => by rw [hk₁]; exact norm_nonneg _
  have hk₂0 : ∀ c, 0 ≤ k₂ c := fun c => by rw [hk₂]; exact norm_nonneg _
  have hs₁ : ∑ c, k₁ c = (1 - u) / (1 - v) := by
    simp_rw [hk₁]; exact uT_row_sum L hL hu huv hv a.1
  have hs₂ : ∑ c, k₂ c = (1 - u) / (1 - v) := by
    simp_rw [hk₂]; exact uT_row_sum L hL hu huv hv a.2
  have hg₁ : ∑ c, k₁ c * uTF L a.1 R c ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') :=
    uT_far_sum_le L a.1 R _ hδ k₁ fun c hc => by rw [hk₁]; exact hFar a.1 c hc
  have hg₂ : ∑ c, k₂ c * uTF L a.2 R c ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') :=
    uT_far_sum_le L a.2 R _ hδ k₂ fun c hc => by rw [hk₂]; exact hFar a.2 c hc
  have hpt : ∀ b : Z2 L × Z2 L, ‖A b‖ ≤ β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2) := by
    intro b
    by_cases h1 : (zdist2 L (a.1 - b.1) : ℝ) < R
    · by_cases h2 : (zdist2 L (a.2 - b.2) : ℝ) < R
      · rw [uTF_eq_zero L h1, uTF_eq_zero L h2]
        simpa using hnear b h1 h2
      · have hF := uTF_eq_one L (not_lt.1 h2)
        have hF1 := uTF_nonneg L a.1 R b.1
        have := mul_le_mul_of_nonneg_left (show 1 ≤ uTF L a.1 R b.1 + uTF L a.2 R b.2 by
          rw [hF]; linarith) hα0
        nlinarith [hα b]
    · have hF := uTF_eq_one L (not_lt.1 h1)
      have hF2 := uTF_nonneg L a.2 R b.2
      have := mul_le_mul_of_nonneg_left (show 1 ≤ uTF L a.1 R b.1 + uTF L a.2 R b.2 by
        rw [hF]; linarith) hα0
      nlinarith [hα b]
  have hsplit : ∑ b : Z2 L × Z2 L, k₁ b.1 * k₂ b.2 * (β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2)) =
      β * ∑ b : Z2 L × Z2 L, k₁ b.1 * k₂ b.2 +
        α * ∑ b : Z2 L × Z2 L, (k₁ b.1 * uTF L a.1 R b.1) * k₂ b.2 +
        α * ∑ b : Z2 L × Z2 L, k₁ b.1 * (k₂ b.2 * uTF L a.2 R b.2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e1 : ∑ b : Z2 L × Z2 L, k₁ b.1 * k₂ b.2 = (∑ x, k₁ x) * ∑ y, k₂ y := uT_sum2 L k₁ k₂
  have e2 : ∑ b : Z2 L × Z2 L, (k₁ b.1 * uTF L a.1 R b.1) * k₂ b.2 =
      (∑ x, k₁ x * uTF L a.1 R x) * ∑ y, k₂ y := uT_sum2 L (fun x => k₁ x * uTF L a.1 R x) k₂
  have e3 : ∑ b : Z2 L × Z2 L, k₁ b.1 * (k₂ b.2 * uTF L a.2 R b.2) =
      (∑ x, k₁ x) * ∑ y, k₂ y * uTF L a.2 R y := uT_sum2 L k₁ (fun y => k₂ y * uTF L a.2 R y)
  have hnorm : ‖Uop L 1 u v A a‖ ≤
      ∑ b : Z2 L × Z2 L, k₁ b.1 * k₂ b.2 * (β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2)) := by
    unfold Uop
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul, ← hk₁, ← hk₂]
    exact mul_le_mul_of_nonneg_left (hpt b) (mul_nonneg (hk₁0 _) (hk₂0 _))
  rw [hsplit, e1, e2, e3, hs₁, hs₂] at hnorm
  set r := (1 - u) / (1 - v) with hr
  set Δ := (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') with hΔ
  have m1 : α * ((∑ x, k₁ x * uTF L a.1 R x) * r) ≤ α * (Δ * r) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg₁ hr0) hα0
  have m2 : α * (r * ∑ y, k₂ y * uTF L a.2 R y) ≤ α * (r * Δ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg₂ hr0) hα0
  calc ‖Uop L 1 u v A a‖ ≤ _ := hnorm
    _ ≤ r ^ 2 * β + 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * r * α := by
        rw [hΔ] at m1 m2
        nlinarith [m1, m2]

/-- **`uopPairLocalMax`** (`res_deccalE_3`): the same for the four-factor sum of `𝒰 ⊗ 𝒰̄`;
`‖conj z‖ = ‖z‖`, so only the row `ℓ¹` norms enter. -/
theorem uopPairLocalMax : UopPairLocalMax := by
  intro L W _ _ hL u v R D' hu huv hv hFar A α β a hβ hα hnear
  have hr0 : 0 ≤ (1 - u) / (1 - v) := div_nonneg (by linarith) (by linarith)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα a a)
  have hδ : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg W) _
  obtain ⟨k₁, hk₁⟩ : ∃ k : Z2 L → ℝ, ∀ c, k c = ‖ukerMat L 1 u v a.1 c‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : Z2 L → ℝ, ∀ c, k c = ‖ukerMat L 1 u v a.2 c‖ := ⟨_, fun _ => rfl⟩
  have hk₁0 : ∀ c, 0 ≤ k₁ c := fun c => by rw [hk₁]; exact norm_nonneg _
  have hk₂0 : ∀ c, 0 ≤ k₂ c := fun c => by rw [hk₂]; exact norm_nonneg _
  have hs₁ : ∑ c, k₁ c = (1 - u) / (1 - v) := by
    simp_rw [hk₁]; exact uT_row_sum L hL hu huv hv a.1
  have hs₂ : ∑ c, k₂ c = (1 - u) / (1 - v) := by
    simp_rw [hk₂]; exact uT_row_sum L hL hu huv hv a.2
  have hg₁ : ∑ c, k₁ c * uTF L a.1 R c ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') :=
    uT_far_sum_le L a.1 R _ hδ k₁ fun c hc => by rw [hk₁]; exact hFar a.1 c hc
  have hg₂ : ∑ c, k₂ c * uTF L a.2 R c ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') :=
    uT_far_sum_le L a.2 R _ hδ k₂ fun c hc => by rw [hk₂]; exact hFar a.2 c hc
  have hpt : ∀ b b' : Z2 L × Z2 L, ‖A b b'‖ ≤
      β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2 + uTF L a.1 R b'.1 + uTF L a.2 R b'.2) := by
    intro b b'
    have n1 := uTF_nonneg L a.1 R b.1
    have n2 := uTF_nonneg L a.2 R b.2
    have n3 := uTF_nonneg L a.1 R b'.1
    have n4 := uTF_nonneg L a.2 R b'.2
    by_cases h : (zdist2 L (a.1 - b.1) : ℝ) < R ∧ (zdist2 L (a.2 - b.2) : ℝ) < R ∧
        (zdist2 L (a.1 - b'.1) : ℝ) < R ∧ (zdist2 L (a.2 - b'.2) : ℝ) < R
    · obtain ⟨h1, h2, h3, h4⟩ := h
      rw [uTF_eq_zero L h1, uTF_eq_zero L h2, uTF_eq_zero L h3, uTF_eq_zero L h4]
      simpa using hnear b b' h1 h2 h3 h4
    · have hge : 1 ≤ uTF L a.1 R b.1 + uTF L a.2 R b.2 + uTF L a.1 R b'.1 +
          uTF L a.2 R b'.2 := by
        by_cases h1 : (zdist2 L (a.1 - b.1) : ℝ) < R
        · by_cases h2 : (zdist2 L (a.2 - b.2) : ℝ) < R
          · by_cases h3 : (zdist2 L (a.1 - b'.1) : ℝ) < R
            · by_cases h4 : (zdist2 L (a.2 - b'.2) : ℝ) < R
              · exact absurd ⟨h1, h2, h3, h4⟩ h
              · rw [uTF_eq_one L (not_lt.1 h4)]; linarith
            · rw [uTF_eq_one L (not_lt.1 h3)]; linarith
          · rw [uTF_eq_one L (not_lt.1 h2)]; linarith
        · rw [uTF_eq_one L (not_lt.1 h1)]; linarith
      have := mul_le_mul_of_nonneg_left hge hα0
      nlinarith [hα b b']
  have hsplit : ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
        k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) *
          (β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2 + uTF L a.1 R b'.1 + uTF L a.2 R b'.2)) =
      β * ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L, k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          (k₁ b.1 * uTF L a.1 R b.1) * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          k₁ b.1 * (k₂ b.2 * uTF L a.2 R b.2) * (k₁ b'.1 * k₂ b'.2) +
        α * ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          k₁ b.1 * k₂ b.2 * ((k₁ b'.1 * uTF L a.1 R b'.1) * k₂ b'.2) +
        α * ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
          k₁ b.1 * k₂ b.2 * (k₁ b'.1 * (k₂ b'.2 * uTF L a.2 R b'.2)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  have e1 := uT_sum4 L k₁ k₂ k₁ k₂
  have e2 := uT_sum4 L (fun x => k₁ x * uTF L a.1 R x) k₂ k₁ k₂
  have e3 := uT_sum4 L k₁ (fun y => k₂ y * uTF L a.2 R y) k₁ k₂
  have e4 := uT_sum4 L k₁ k₂ (fun x => k₁ x * uTF L a.1 R x) k₂
  have e5 := uT_sum4 L k₁ k₂ k₁ (fun y => k₂ y * uTF L a.2 R y)
  have hnorm : ‖∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
      ukerMat L 1 u v a.1 b.1 * ukerMat L 1 u v a.2 b.2 *
        (starRingEnd ℂ) (ukerMat L 1 u v a.1 b'.1 * ukerMat L 1 u v a.2 b'.2) * A b b'‖ ≤
      ∑ b : Z2 L × Z2 L, ∑ b' : Z2 L × Z2 L,
        k₁ b.1 * k₂ b.2 * (k₁ b'.1 * k₂ b'.2) *
          (β + α * (uTF L a.1 R b.1 + uTF L a.2 R b.2 + uTF L a.1 R b'.1 +
            uTF L a.2 R b'.2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    simp only [norm_mul, Complex.norm_conj, ← hk₁, ← hk₂]
    exact mul_le_mul_of_nonneg_left (hpt b b')
      (mul_nonneg (mul_nonneg (hk₁0 _) (hk₂0 _)) (mul_nonneg (hk₁0 _) (hk₂0 _)))
  rw [hsplit, e1, e2, e3, e4, e5, hs₁, hs₂] at hnorm
  set r := (1 - u) / (1 - v) with hr
  set Δ := (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') with hΔ
  have hrr : 0 ≤ r * r * (r * r) := by positivity
  have m1 : α * (((∑ x, k₁ x * uTF L a.1 R x) * r) * (r * r)) ≤ α * ((Δ * r) * (r * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg₁ hr0) (by positivity)) hα0
  have m2 : α * ((r * ∑ y, k₂ y * uTF L a.2 R y) * (r * r)) ≤ α * ((r * Δ) * (r * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg₂ hr0) (by positivity)) hα0
  have m3 : α * ((r * r) * ((∑ x, k₁ x * uTF L a.1 R x) * r)) ≤ α * ((r * r) * (Δ * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hg₁ hr0) (by positivity)) hα0
  have m4 : α * ((r * r) * (r * ∑ y, k₂ y * uTF L a.2 R y)) ≤ α * ((r * r) * (r * Δ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hg₂ hr0) (by positivity)) hα0
  calc _ ≤ _ := hnorm
    _ ≤ r ^ 4 * β + 4 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * r ^ 3 * α := by
        rw [hΔ] at m1 m2 m3 m4
        nlinarith [m1, m2, m3, m4]

/-! ## `TailtoTail` -/

section TailHelpers

variable (L : ℕ) [NeZero L]

private theorem uT_zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  have hu : u.val < L := ZMod.val_lt u
  by_cases h : u = 0
  · subst h; simp
  · have hneg : (-u).val = L - u.val := by rw [ZMod.neg_val]; simp [h]
    simp only [zdist, hneg]
    omega

private theorem uT_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, uT_zdist_neg]

/-- Triangle inequality: `|a₁ - a₂| ≤ |a₁ - b₁| + |b₁ - b₂| + |a₂ - b₂|`. -/
private theorem uT_near_far (a₁ a₂ b₁ b₂ : Z2 L) :
    zdist2 L (a₁ - a₂) ≤ zdist2 L (a₁ - b₁) + zdist2 L (b₁ - b₂) + zdist2 L (a₂ - b₂) := by
  have h : a₁ - a₂ = (a₁ - b₁) + (b₁ - b₂) + -(a₂ - b₂) := by abel
  have h1 := zdist2_add_le L (a₁ - b₁) (b₁ - b₂)
  have h2 := zdist2_add_le L ((a₁ - b₁) + (b₁ - b₂)) (-(a₂ - b₂))
  rw [uT_zdist2_neg] at h2
  rw [h]
  omega

end TailHelpers

/-- The scalar core of `neiwuj` (`d = 2`): with `ρ = ℓ_t/ℓ_s ≥ 1`, `ℓ* = Y² ℓ_t`, `Y ≥ 2`
and `d ≥ ℓ*`,
`ρ⁴ exp(-√((d - ℓ*/2)/ℓ_s)) ≤ 30000 e^Y exp(-√(d/ℓ_t))`.  Proof: with `x = √ρ`, `X = √(d/ℓ_t)`,
`√((d - ℓ*/2)/ℓ_s) ≥ x (X - 3Y/10)` (as `X ≥ Y`), hence the exponent is at most
`Y - X - (7Y/10) x`, and `x⁸ exp(-(7Y/10) x) ≤ 8!/(7/5)⁸ ≤ 30000` by `y⁸/8! ≤ e^y`. -/
private theorem uT_scalar {ℓs ℓt d Y : ℝ} (hℓs : 0 < ℓs) (hst : ℓs ≤ ℓt) (hY : 2 ≤ Y)
    (hd : Y ^ 2 * ℓt ≤ d) :
    (ℓt / ℓs) ^ 4 * Real.exp (-Real.sqrt ((d - Y ^ 2 * ℓt / 2) / ℓs)) ≤
      30000 * Real.exp Y * Real.exp (-Real.sqrt (d / ℓt)) := by
  have hℓt : 0 < ℓt := hℓs.trans_le hst
  have hρ1 : 1 ≤ ℓt / ℓs := (one_le_div hℓs).2 hst
  have hd0 : 0 ≤ d / ℓt := by
    have : 0 ≤ Y ^ 2 * ℓt := by positivity
    exact div_nonneg (this.trans hd) hℓt.le
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ℓt / ℓs := ⟨_, rfl⟩
  rw [← hρ]
  rw [← hρ] at hρ1
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt ρ := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by
    rw [hx]; simpa using Real.sqrt_le_sqrt hρ1
  have hxsq : x ^ 2 = ρ := by rw [hx]; exact Real.sq_sqrt (by linarith)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.sqrt (d / ℓt) := ⟨_, rfl⟩
  rw [← hX]
  have hXsq : X ^ 2 = d / ℓt := by rw [hX]; exact Real.sq_sqrt hd0
  have hXY : Y ≤ X := by
    have h : Y ^ 2 ≤ d / ℓt := by rw [le_div_iff₀ hℓt]; exact hd
    rw [hX]
    exact (le_abs_self Y).trans (Real.abs_le_sqrt h)
  have hA : x * (X - 3 * Y / 10) ≤ Real.sqrt ((d - Y ^ 2 * ℓt / 2) / ℓs) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have h1 : (d - Y ^ 2 * ℓt / 2) / ℓs = x ^ 2 * (X ^ 2 - Y ^ 2 / 2) := by
      rw [hxsq, hXsq, hρ]; field_simp
    rw [h1, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [hXY, hY]
  have hB : Real.exp (-Real.sqrt ((d - Y ^ 2 * ℓt / 2) / ℓs)) ≤
      Real.exp Y * Real.exp (-X) * Real.exp (-(7 * Y / 10 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hXY)]
  have hC : x ^ 8 * Real.exp (-(7 * Y / 10 * x)) ≤ 30000 := by
    have hc14 : (7 / 5 : ℝ) ≤ 7 * Y / 10 := by linarith
    have hcx : 0 ≤ 7 * Y / 10 * x := by positivity
    have hexp := Real.pow_div_factorial_le_exp (7 * Y / 10 * x) hcx 8
    have h8 : (7 / 5 : ℝ) ^ 8 * x ^ 8 ≤ (7 * Y / 10 * x) ^ 8 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hc14 (by linarith)) 8
    have hpos := Real.exp_pos (7 * Y / 10 * x)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    norm_num [Nat.factorial] at hexp h8
    nlinarith [hexp, h8, hpos]
  have hρ4 : ρ ^ 4 = x ^ 8 := by rw [← hxsq]; ring
  calc ρ ^ 4 * Real.exp (-Real.sqrt ((d - Y ^ 2 * ℓt / 2) / ℓs))
      ≤ x ^ 8 * (Real.exp Y * Real.exp (-X) * Real.exp (-(7 * Y / 10 * x))) := by
        rw [hρ4]; exact mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (x ^ 8 * Real.exp (-(7 * Y / 10 * x))) * Real.exp Y * Real.exp (-X) := by ring
    _ ≤ 30000 * Real.exp Y * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)
          (Real.exp_pos _).le

/-- **`tailtoTail`** (`neiwuj`, `d = 2`): `uopLocalMax` at radius `ℓ*_t/4` with
`α = M_s⁻² + W^{-D}` and `β` the value of `𝒯_{s,D}` at distance `d - ℓ*_t/2`, then `uT_scalar`.
Neither `d = 2` adjustment mentioned after Lemma `TailtoTail` is used; the far region is the
hypothesis `UkerFar`. -/
theorem tailtoTail : TailtoTail := by
  intro L W _ _ E D D' s t hL hE hD hs0 hst ht hlogW hM hFar hDD' A hA a ha
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hηt : 0 < etaT E t := etaT_pos hE ht
  have hr : etaT E s / etaT E t = (1 - s) / (1 - t) := etaT_div_etaT hE hs1 ht
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (1 - s) / (1 - t) := ⟨_, rfl⟩
  rw [hr, ← hrdef]
  have hr1 : 1 ≤ r := by rw [hrdef, le_div_iff₀ hxt]; linarith
  have hηsr : etaT E s = r * etaT E t := (div_eq_iff hηt.ne').1 (hr.trans hrdef.symm)
  have hℓs : 0 < ellT L s := (ellT_pos_le hL1 hs1).1
  have hℓt : 0 < ellT L t := (ellT_pos_le hL1 ht).1
  have hℓst : ellT L s ≤ ellT L t := (ellT_mono_ratio hL1 hs0 hst ht).1
  -- the scale `Y = (log W)^{3/4}` and `ℓ*_t = Y² ℓ_t`
  have hlog0 : 0 ≤ Real.log W := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.log W ^ ((3 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hY]
  have hYsq : Y ^ 2 = Real.log W ^ ((3 : ℝ) / 2) := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hlog0]; norm_num
  have hY2 : 2 ≤ Y := by
    have hsq2 : 2 ≤ Real.sqrt (Real.log W) :=
      (le_abs_self (2 : ℝ)).trans (Real.abs_le_sqrt (by nlinarith))
    rw [Real.sqrt_eq_rpow] at hsq2
    rw [hY]
    exact hsq2.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hstar : ellStar L W t = Y ^ 2 * ellT L t := by
    unfold ellStar; rw [hYsq]
  -- the scales `M_s ≥ M_t ≥ 1`
  have hMs : 1 ≤ scaleM L W E s := hM.trans (scaleM_anti_ratio hL1 hE hst ht).1
  have hMs2 : ((scaleM L W E s) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hMs)
  have hMs2' : 0 ≤ ((scaleM L W E s) ^ 2)⁻¹ := by positivity
  have hWd0 : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  have hWd1 : (W : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  have hWd'0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg W) _
  -- the data of `uopLocalMax`
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (zdist2 L (a.1 - a.2) : ℝ) := ⟨_, rfl⟩
  rw [← hd] at ha ⊢
  have hdY : Y ^ 2 * ellT L t ≤ d := by rw [← hstar]; exact ha
  have hα : ∀ b : Z2 L × Z2 L, ‖A b‖ ≤ ((scaleM L W E s) ^ 2)⁻¹ + (W : ℝ) ^ (-D) := by
    intro b
    refine (hA b).trans ?_
    unfold tailT
    have h1 : Real.exp (-Real.sqrt ((zdist2 L (b.1 - b.2) : ℝ) / ellT L s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
    have := mul_le_mul_of_nonneg_left h1 hMs2'
    linarith
  have hβ0 : 0 ≤ ((scaleM L W E s) ^ 2)⁻¹ *
      Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s)) + (W : ℝ) ^ (-D) := by
    positivity
  have hnear : ∀ b : Z2 L × Z2 L, (zdist2 L (a.1 - b.1) : ℝ) < ellStar L W t / 4 →
      (zdist2 L (a.2 - b.2) : ℝ) < ellStar L W t / 4 →
      ‖A b‖ ≤ ((scaleM L W E s) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s)) + (W : ℝ) ^ (-D) := by
    intro b h1 h2
    have hnat := uT_near_far L a.1 a.2 b.1 b.2
    have hcast : (zdist2 L (a.1 - a.2) : ℝ) ≤ (zdist2 L (a.1 - b.1) : ℝ) +
        (zdist2 L (b.1 - b.2) : ℝ) + (zdist2 L (a.2 - b.2) : ℝ) := by exact_mod_cast hnat
    rw [hstar] at h1 h2
    have hz : d - Y ^ 2 * ellT L t / 2 ≤ (zdist2 L (b.1 - b.2) : ℝ) := by
      rw [hd]; linarith
    have hsq : Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s) ≤
        Real.sqrt ((zdist2 L (b.1 - b.2) : ℝ) / ellT L s) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hz hℓs.le)
    have hexp : Real.exp (-Real.sqrt ((zdist2 L (b.1 - b.2) : ℝ) / ellT L s)) ≤
        Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s)) :=
      Real.exp_le_exp.2 (neg_le_neg hsq)
    refine (hA b).trans ?_
    unfold tailT
    have := mul_le_mul_of_nonneg_left hexp hMs2'
    linarith
  have key := uopLocalMax L W hL s t (ellStar L W t / 4) D' hs0 hst ht hFar A _ _ a hβ0 hα hnear
  rw [← hrdef] at key
  -- the identity `r² M_s⁻² = ρ⁴ M_t⁻²`
  have hid : r ^ 2 * ((scaleM L W E s) ^ 2)⁻¹ =
      (ellT L t / ellT L s) ^ 4 * ((scaleM L W E t) ^ 2)⁻¹ := by
    have hW0 : (0 : ℝ) < W := by linarith
    unfold scaleM
    rw [hηsr]
    have hr0 : 0 < r := by linarith
    field_simp
  have hmain : r ^ 2 * (((scaleM L W E s) ^ 2)⁻¹ *
      Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s))) ≤
      30000 * Real.exp Y * ((scaleM L W E t) ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / ellT L t)) := by
    have hsc := uT_scalar hℓs hℓst hY2 hdY
    have hMt2' : 0 ≤ ((scaleM L W E t) ^ 2)⁻¹ := by positivity
    calc r ^ 2 * (((scaleM L W E s) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s)))
        = ((scaleM L W E t) ^ 2)⁻¹ * ((ellT L t / ellT L s) ^ 4 *
            Real.exp (-Real.sqrt ((d - Y ^ 2 * ellT L t / 2) / ellT L s))) := by
          rw [← mul_assoc, hid]; ring
      _ ≤ ((scaleM L W E t) ^ 2)⁻¹ * (30000 * Real.exp Y *
            Real.exp (-Real.sqrt (d / ellT L t))) := mul_le_mul_of_nonneg_left hsc hMt2'
      _ = 30000 * Real.exp Y * ((scaleM L W E t) ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / ellT L t)) := by
          ring
  -- the far terms
  have hP : 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) / 2 := by linarith
  have hα2 : ((scaleM L W E s) ^ 2)⁻¹ + (W : ℝ) ^ (-D) ≤ 2 := by linarith
  have hα0 : 0 ≤ ((scaleM L W E s) ^ 2)⁻¹ + (W : ℝ) ^ (-D) := by positivity
  have hP0 : 0 ≤ 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') := by positivity
  have hfar : 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * r *
      (((scaleM L W E s) ^ 2)⁻¹ + (W : ℝ) ^ (-D)) ≤ r * (W : ℝ) ^ (-D) := by
    calc 2 * (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') * r *
          (((scaleM L W E s) ^ 2)⁻¹ + (W : ℝ) ^ (-D))
        ≤ ((W : ℝ) ^ (-D) / 2) * r * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hP (by linarith)) hα2 hα0
            (by positivity)
      _ = r * (W : ℝ) ^ (-D) := by ring
  have hrr : r * (W : ℝ) ^ (-D) ≤ r ^ 2 * (W : ℝ) ^ (-D) := by
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hr1 (by norm_num)) hWd0
  rw [mul_add] at key
  linarith [key, hmain, hfar, hrr]

end RBM.Path

end
