/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.KernelExpand
import RBM2D.Evolution.LatticeSums

/-!
# Case 4 of `lem:sum_decay`: alternating `σ`, sum-zero and symmetric tensor

Paper: arXiv:2503.07606, Section 7: `symmetric_tensor`, `sumAzero`, `Xi-expansion`,
`eq-1sum`, `eq-2sum`.

Statement (namespace `RBM.Evol`): the `Prop` `UgenCase4AltExplicit`.  Proved here, for the
explicit constant `cCase4`: `ugenCase4AltExplicit : UgenCase4AltExplicit cCase4`.

Argument (`d = 2`).  For alternating `σ` and `|E| ≤ 2` every edge
weight is `m m̄ = |m|² = 1`, so every kernel is `ψ = 1 + Ξ`, `Ξ = xiMat L 1 s t`.
* Expand `∏ᵢ (δ + Ξᵢ)` over `g : Fin k → Fin 2`.  A term with some `δ` at `j` is bounded by the
  anchored window bound of Case 1 (`KernelExpand_core_bound`, anchor `j`).
* The all-`Ξ` term: around the anchor `c = b₀` write `Ξ(aᵢ, bᵢ) = Ξ⁰ᵢ + Ξ¹ᵢ + Ξ²ᵢ` (`r = bᵢ - c`,
  `Ξ⁰ = Ξ(aᵢ, c)`, `Ξ¹ = (Ξ(aᵢ, c + r) - Ξ(aᵢ, c - r))/2`, `Ξ² = (Ξ(aᵢ, c + r) + Ξ(aᵢ, c - r))/2 -
  Ξ(aᵢ, c)`) and expand over `f : Fin k → Fin 3` (`Case4_prod_sum_pieces`).  At `i = 0` one has
  `r = 0`, so `Ξ¹₀ = Ξ²₀ = 0`.
  - all `Ξ⁰`: vanishes by `SumZero` at `b₀`;
  - exactly one `Ξ¹`: vanishes by `Symmetric` (the involution `b ↦ b₀ - (b - b₀)`);
  - some `Ξ²`: `xiSecondDiff`, `Case4_window_sum_two` and the anchor sum with `ExpInvSum` and
    `xiRowBound`;
  - two `Ξ¹`: two factors `xiFirstDiff`, `Case4_window_sum_one` and the anchor bounds
    `Case4_anchor_a`, `Case4_anchor_b` (`ExpInvSum` at `c = 20000 ℓ_t`), `Case4_anchor_c`.
  The far part carries `((λ L²)^k ((1-s)/(1-t))^k) δ_A`: the `r`-sums of the pieces run over all of
  `Z_L²`.

There is no one-dimensional counterpart of Case 4.  The exact anchored sum `anchor_eq` follows
`sum_prod_anchor_le` as used in `KernelExpand.lean`.
-/

noncomputable section

namespace RBM.Evol

open Finset RBM.Path RBM.Ind

/-- **Case 4 (`symmetric_tensor`, explicit)**, alternating `σ` (then every
`ξ_i = |m|² = 1`), sum zero and symmetric.  Specific to `d = 2`.  The error term
carries `((1 + log L) L²)^k`: the `r`-sums of the `Ξ⁰` pieces run over all of `Z_L²`. -/
def UgenCase4AltExplicit (c : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ σ : Fin k → Bool, (∀ i : Fin k, σ i ≠ σ (i + 1)) →
    ∀ K M δA : ℝ, 1 ≤ K → 0 ≤ M → 0 ≤ δA →
    ∀ A : (Fin k → Z2 L) → ℂ, (∀ b, ‖A b‖ ≤ M) → DecayWin L (ellT L s * K) δA A →
    SumZero L A → Symmetric L A → ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ s t A a‖ ≤
        c k * (1 + Real.log L) ^ (k + 1) * K ^ (2 * k) * rhoR L s t ^ k * M +
          c k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k * δA

/-- The explicit constant of Case 4: `(4 X)^k` with `X = 10⁶ (cProp5 + 8·10¹⁴ + 720)`
(`8·10¹⁴ + 720` bounds `derivativePrefactor 10¹⁴ L / (1 + log L)`). -/
def cCase4 (k : ℕ) : ℝ := (4 * (10 ^ 6 * (cProp5 + (8 * 10 ^ 14 + 720)))) ^ k

/-! ## Distances and window sums -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem case4_zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem case4_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, case4_zdist_neg]

private theorem case4_zdist2_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← neg_sub x y, case4_zdist2_neg]

/-- `#{x : |x - c|_L < ρ} ≤ 9ρ²` for `ρ ≥ 1` (`KLoop.card_ball_le`). -/
private theorem card_near_le {ρ : ℝ} (hρ : 1 ≤ ρ) (c : Z2 L) :
    ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ) ≤ 9 * ρ ^ 2 := by
  have hsub : (univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ) ⊆
      (univ.filter fun x : Z2 L => (zdist2 L (c - x) : ℝ) ≤ ρ) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [case4_zdist2_comm]; exact hx.le
  have h1 := RBM.KLoop.card_ball_le L c ρ (by linarith)
  calc ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ)
      ≤ (((univ.filter fun x : Z2 L => (zdist2 L (c - x) : ℝ) ≤ ρ).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ (2 * ρ + 1) ^ 2 := h1
    _ ≤ 9 * ρ ^ 2 := by nlinarith

/-- **Window sum, first moment** (shared with D3 and R3): for `ρ ≥ 1`,
`Σ_{|b - x|_L < ρ} |b - x|_L ≤ 9ρ³`. -/
theorem Case4_window_sum_one {ρ : ℝ} (hρ : 1 ≤ ρ) (x : Z2 L) :
    ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ), (zdist2 L (b - x) : ℝ) ≤
      9 * ρ ^ 3 := by
  calc ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ), (zdist2 L (b - x) : ℝ)
      ≤ ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ), ρ :=
        sum_le_sum fun b hb => (mem_filter.1 hb).2.le
    _ = ((univ.filter fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ).card : ℝ) * ρ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ρ ^ 2 * ρ := mul_le_mul_of_nonneg_right (card_near_le hρ x) (by linarith)
    _ = 9 * ρ ^ 3 := by ring

/-- **Window sum, second moment** (shared with D3 and R3): for `ρ ≥ 1`,
`Σ_{|b - x|_L < ρ} |b - x|_L² ≤ 9ρ⁴`. -/
theorem Case4_window_sum_two {ρ : ℝ} (hρ : 1 ≤ ρ) (x : Z2 L) :
    ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ), (zdist2 L (b - x) : ℝ) ^ 2 ≤
      9 * ρ ^ 4 := by
  calc ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ),
        (zdist2 L (b - x) : ℝ) ^ 2
      ≤ ∑ b ∈ univ.filter (fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ), ρ ^ 2 :=
        sum_le_sum fun b hb =>
          pow_le_pow_left₀ (Nat.cast_nonneg _) (mem_filter.1 hb).2.le 2
    _ = ((univ.filter fun b : Z2 L => (zdist2 L (b - x) : ℝ) < ρ).card : ℝ) * ρ ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ρ ^ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_right (card_near_le hρ x) (by positivity)
    _ = 9 * ρ ^ 4 := by ring

end Dist

/-! ## The partition expansion -/

/-- **Expansion of a product of sums of pieces** (shared with D3 and R3):
`∏ᵢ Σ_p xᵢ(p) = Σ_{f : I → Fin n} ∏ᵢ xᵢ(f i)` (`Fintype.prod_sum`). -/
theorem Case4_prod_sum_pieces {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R] {n : ℕ}
    (x : I → Fin n → R) : ∏ i, ∑ p, x i p = ∑ f : I → Fin n, ∏ i, x i (f i) :=
  Fintype.prod_sum x

/-! ## Scale facts -/

section Scales

variable {L : ℕ}

/-- `e = 2 cProp5 (1 + log L)(t - s)/min(1, L²(1-t))`, the entry scale of K1a (`xiEntryBound`). -/
private def eT (L : ℕ) (s t : ℝ) : ℝ :=
  2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))

private theorem case4_cProp5_ge_one : 1 ≤ cProp5 := by unfold cProp5; norm_num

private theorem case4_lam_ge_one (L : ℕ) : 1 ≤ 1 + Real.log L := by
  linarith [Real.log_natCast_nonneg L]

private theorem eT_nonneg (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 0 ≤ eT L s t := by
  unfold eT
  have hm := KernelExpand_min_one_pos' hL ht
  have h1 := case4_lam_ge_one L
  have h2 := case4_cProp5_ge_one
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hm.le

/-- `ℓ_u²(1-u) ≤ 1`. -/
private theorem ellT_sq_mul_le {u : ℝ} (hu : u < 1) : ellT L u ^ 2 * (1 - u) ≤ 1 := by
  rw [KernelExpand_ellT_sq_mul hu]; exact min_le_left _ _

/-- `(t-s) ℓ_s² ≤ 1`. -/
private theorem ts_ellT_sq_le {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    (t - s) * ellT L s ^ 2 ≤ 1 := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h := ellT_sq_mul_le (L := L) hs1
  have : (t - s) * ellT L s ^ 2 ≤ (1 - s) * ellT L s ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  linarith

/-- `ℓ_s² e ≤ 2 cProp5 λ R`. -/
private theorem ellT_sq_eT_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    ellT L s ^ 2 * eT L s t ≤ 2 * cProp5 * (1 + Real.log L) * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm := KernelExpand_min_one_pos' hL ht
  have hq : ellT L s ^ 2 * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ rhoR L s t := by
    rw [KernelExpand_rhoR_eq hs1 ht, ← KernelExpand_ellT_sq_mul hs1,
      div_le_div_iff_of_pos_right hm]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have heq : ellT L s ^ 2 * eT L s t = 2 * cProp5 * (1 + Real.log L) *
      (ellT L s ^ 2 * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by
    unfold eT; ring
  rw [heq]
  have h1 := case4_lam_ge_one L
  have h2 := case4_cProp5_ge_one
  exact mul_le_mul_of_nonneg_left hq (mul_nonneg (by linarith) (by linarith))

/-- `L² e ≤ 2 cProp5 λ L² (1-s)/(1-t)` (`min(1, L²(1-t)) ≥ 1 - t`). -/
private theorem L2_eT_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (L : ℝ) ^ 2 * eT L s t ≤
      2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) := by
  have h1t : 0 < 1 - t := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hmle : 1 - t ≤ min 1 ((L : ℝ) ^ 2 * (1 - t)) :=
    le_min (by linarith) (by nlinarith)
  have h1 := case4_lam_ge_one L
  have h2 := case4_cProp5_ge_one
  have hc : 0 ≤ 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  unfold eT
  calc (L : ℝ) ^ 2 * (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)))
      = 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 *
          ((t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by ring
    _ ≤ 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) := by
      refine mul_le_mul_of_nonneg_left ?_ hc
      calc (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ (t - s) / (1 - t) :=
            div_le_div_of_nonneg_left (by linarith) h1t hmle
        _ ≤ (1 - s) / (1 - t) := div_le_div_of_nonneg_right (by linarith) h1t.le

/-- `ℓ_t √(1-t) ≤ 1`. -/
private theorem ellT_sqrt_le {t : ℝ} (ht : t < 1) : ellT L t * Real.sqrt (1 - t) ≤ 1 := by
  have hsq : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  have h : ellT L t ≤ 1 / Real.sqrt (1 - t) := min_le_left _ _
  calc ellT L t * Real.sqrt (1 - t) ≤ 1 / Real.sqrt (1 - t) * Real.sqrt (1 - t) :=
        mul_le_mul_of_nonneg_right h hsq.le
    _ = 1 := by field_simp

/-- `R · ℓ_t²(1-t) = ℓ_s²(1-s)`. -/
private theorem rhoR_mul_eq (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    rhoR L s t * (ellT L t ^ 2 * (1 - t)) = ellT L s ^ 2 * (1 - s) := by
  have hlt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have h1 : ellT L t ^ 2 * (1 - t) ≠ 0 := by
    have : 0 < ellT L t ^ 2 * (1 - t) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    exact this.ne'
  have h2 : (1 - t) ≠ 0 := by linarith
  have h3 : ellT L t ≠ 0 := by positivity
  unfold rhoR
  field_simp

/-- `derivativePrefactor 10¹⁴ L ≤ (8·10¹⁴ + 720)(1 + log L)` (`P_L ≤ P'λ`). -/
private theorem Pl_le (L : ℕ) :
    derivativePrefactor (10 ^ 14) L ≤ (8 * 10 ^ 14 + 720) * (1 + Real.log L) := by
  unfold derivativePrefactor
  have := case4_lam_ge_one L
  nlinarith

private theorem Pl_nonneg (L : ℕ) : 0 ≤ derivativePrefactor (10 ^ 14) L := by
  unfold derivativePrefactor
  have := case4_lam_ge_one L
  nlinarith

end Scales

/-! ## Entry bounds and the anchor sums -/

section Anchor

variable {L : ℕ} [NeZero L]

/-- `|Ξ(a, c)| ≤ e` (K1a without the exponential factor). -/
private theorem xi_le_eT (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a c : Z2 L) : ‖xiMat L ξ s t a c‖ ≤ eT L s t := by
  have h := xiEntryBound L hL ξ hξ s t hs hst ht a c
  have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by simp) (by linarith)
  calc ‖xiMat L ξ s t a c‖
      ≤ eT L s t * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) := h
    _ ≤ eT L s t * 1 := mul_le_mul_of_nonneg_left hexp (eT_nonneg hL hst ht)
    _ = eT L s t := mul_one _

/-- `1/((u+1)(v+1)) ≤ ((u²+1)⁻¹ + (v²+1)⁻¹)/2` for `u, v ≥ 0`. -/
private theorem inv_mul_le_half {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    1 / ((u + 1) * (v + 1)) ≤ ((u ^ 2 + 1)⁻¹ + (v ^ 2 + 1)⁻¹) / 2 := by
  have hp : ((u + 1)⁻¹) ^ 2 ≤ (u ^ 2 + 1)⁻¹ := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) (by nlinarith)
  have hq : ((v + 1)⁻¹) ^ 2 ≤ (v ^ 2 + 1)⁻¹ := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) (by nlinarith)
  have heq : 1 / ((u + 1) * (v + 1)) = (u + 1)⁻¹ * (v + 1)⁻¹ := by
    rw [one_div, mul_inv]
  rw [heq]
  nlinarith [sq_nonneg ((u + 1)⁻¹ - (v + 1)⁻¹)]

/-- The anchor sum of the `Ξ²` group:
`(t-s) ℓ_s⁴ Σ_c |Ξ(a₀, c)| (1/(|y - c|² + 1) + 1/ℓ_t²) ≤ (10 cProp5 λ² + 1) R`. -/
private theorem anchor_sq (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a₀ y : Z2 L) :
    (t - s) * ellT L s ^ 4 * ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ *
        (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) ≤
      (10 * cProp5 * (1 + Real.log L) ^ 2 + 1) * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hlt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have he0 : 0 ≤ eT L s t := eT_nonneg hL hst ht
  have hlam : 1 ≤ 1 + Real.log L := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hts : (t - s) * ellT L s ^ 2 ≤ 1 := ts_ellT_sq_le hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  have hRD := rhoR_mul_eq hL hs hst ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  set e := eT L s t with he
  set lam := 1 + Real.log L with hlamdef
  set ls := ellT L s with hlsdef
  set lt := ellT L t with hltdef
  set R := rhoR L s t with hRdef
  have hS1 : ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1)) ≤
      e * (5 * lam) := by
    calc ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1))
        ≤ ∑ c : Z2 L, e * ((zdist2 L (y - c) : ℝ) ^ 2 + 1)⁻¹ := sum_le_sum fun c _ => by
          rw [one_div]
          exact mul_le_mul_of_nonneg_right (xi_le_eT hL hξ hs hst ht a₀ c) (by positivity)
      _ = e * ∑ c : Z2 L, ((zdist2 L (y - c) : ℝ) ^ 2 + 1)⁻¹ := by rw [mul_sum]
      _ ≤ e * (5 * lam) := by
          refine mul_le_mul_of_nonneg_left ?_ he0
          refine (RBM.KLoop.sum_inv_sq_le L hL y).trans ?_
          rw [hlamdef]; linarith [Real.log_natCast_nonneg L]
  have hS2 : ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / lt ^ 2) ≤
      (t - s) / (1 - t) * (1 / lt ^ 2) := by
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (xiRowBound L hL ξ hξ s t hs hst ht a₀) (by positivity)
  have hsplit : ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ *
      (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1) + 1 / lt ^ 2) =
      ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1)) +
        ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / lt ^ 2) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun c _ => mul_add _ _ _
  have hA0 : 0 ≤ (t - s) * ls ^ 4 := mul_nonneg (by linarith) (by positivity)
  have ht1 : (t - s) * ls ^ 4 * (e * (5 * lam)) ≤ 10 * cProp5 * lam ^ 2 * R := by
    have heq : (t - s) * ls ^ 4 * (e * (5 * lam)) =
        5 * lam * ((t - s) * ls ^ 2) * (ls ^ 2 * e) := by
      ring
    rw [heq]
    calc 5 * lam * ((t - s) * ls ^ 2) * (ls ^ 2 * e)
        ≤ 5 * lam * 1 * (2 * cProp5 * lam * R) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hts (by linarith)) hlse
            (mul_nonneg (by positivity) he0) (by linarith)
      _ = 10 * cProp5 * lam ^ 2 * R := by ring
  have ht2 : (t - s) * ls ^ 4 * ((t - s) / (1 - t) * (1 / lt ^ 2)) ≤ R := by
    have hlt2 : 0 < lt ^ 2 * (1 - t) := mul_pos (pow_pos (by linarith) 2) h1t
    have hlt0 : lt ≠ 0 := by positivity
    have h1t0 : (1 - t) ≠ 0 := h1t.ne'
    have heq : (t - s) * ls ^ 4 * ((t - s) / (1 - t) * (1 / lt ^ 2)) =
        (t - s) * ((t - s) * ls ^ 2) * ls ^ 2 / (lt ^ 2 * (1 - t)) := by
      field_simp
    have hReq : R = ls ^ 2 * (1 - s) / (lt ^ 2 * (1 - t)) := by
      rw [eq_div_iff hlt2.ne', hRD]
    rw [heq, hReq]
    refine div_le_div_of_nonneg_right ?_ hlt2.le
    have h3 : (t - s) * ((t - s) * ls ^ 2) ≤ 1 - s := by
      have := mul_le_mul_of_nonneg_left hts (by linarith : (0 : ℝ) ≤ t - s)
      linarith
    calc (t - s) * ((t - s) * ls ^ 2) * ls ^ 2 ≤ (1 - s) * ls ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = ls ^ 2 * (1 - s) := by ring
  rw [hsplit, mul_add]
  calc (t - s) * ls ^ 4 * ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ *
          (1 / ((zdist2 L (y - c) : ℝ) ^ 2 + 1)) +
        (t - s) * ls ^ 4 * ∑ c : Z2 L, ‖xiMat L ξ s t a₀ c‖ * (1 / lt ^ 2)
      ≤ (t - s) * ls ^ 4 * (e * (5 * lam)) +
          (t - s) * ls ^ 4 * ((t - s) / (1 - t) * (1 / lt ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hS1 hA0) (mul_le_mul_of_nonneg_left hS2 hA0)
    _ ≤ 10 * cProp5 * lam ^ 2 * R + R := add_le_add ht1 ht2
    _ = (10 * cProp5 * lam ^ 2 + 1) * R := by ring

/-- **Anchor bound (a)** (shared with Case 5): with `Q = (t-s) ℓ_s³`,
`Q² Σ_b |Ξ(a₀, b)| / ((|y - b|_L + 1)(|z - b|_L + 1)) ≤ 10 cProp5 λ² R`, `λ = 1 + log L`,
`R = rhoR L s t`, `Ξ = xiMat L ξ s t`, `‖ξ‖ ≤ 1`. -/
theorem Case4_anchor_a (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a₀ y z : Z2 L) :
    ((t - s) * ellT L s ^ 3) ^ 2 * ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ /
        (((zdist2 L (y - b) : ℝ) + 1) * ((zdist2 L (z - b) : ℝ) + 1)) ≤
      10 * cProp5 * (1 + Real.log L) ^ 2 * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have he0 : 0 ≤ eT L s t := eT_nonneg hL hst ht
  have hlam : 1 ≤ 1 + Real.log L := case4_lam_ge_one L
  have hts : (t - s) * ellT L s ^ 2 ≤ 1 := ts_ellT_sq_le hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  set e := eT L s t with he
  set lam := 1 + Real.log L with hlamdef
  set ls := ellT L s with hlsdef
  set R := rhoR L s t with hRdef
  have hSy := RBM.KLoop.sum_inv_sq_le L hL y
  have hSz := RBM.KLoop.sum_inv_sq_le L hL z
  have hsum : ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ /
        (((zdist2 L (y - b) : ℝ) + 1) * ((zdist2 L (z - b) : ℝ) + 1)) ≤ e * (5 * lam) := by
    calc ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ /
          (((zdist2 L (y - b) : ℝ) + 1) * ((zdist2 L (z - b) : ℝ) + 1))
        ≤ ∑ b : Z2 L, e * ((((zdist2 L (y - b) : ℝ) ^ 2 + 1)⁻¹ +
            ((zdist2 L (z - b) : ℝ) ^ 2 + 1)⁻¹) / 2) := sum_le_sum fun b _ => by
          rw [div_eq_mul_one_div]
          exact mul_le_mul (xi_le_eT hL hξ hs hst ht a₀ b)
            (inv_mul_le_half (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity) he0
      _ = e / 2 * (∑ b : Z2 L, ((zdist2 L (y - b) : ℝ) ^ 2 + 1)⁻¹ +
            ∑ b : Z2 L, ((zdist2 L (z - b) : ℝ) ^ 2 + 1)⁻¹) := by
          rw [← sum_add_distrib, mul_sum]
          exact sum_congr rfl fun b _ => by ring
      _ ≤ e / 2 * ((5 + 4 * Real.log L) + (5 + 4 * Real.log L)) :=
          mul_le_mul_of_nonneg_left (add_le_add hSy hSz) (by positivity)
      _ ≤ e * (5 * lam) := by
          rw [hlamdef]
          have : (5 + 4 * Real.log L) + (5 + 4 * Real.log L) ≤ 2 * (5 * (1 + Real.log L)) := by
            linarith [Real.log_natCast_nonneg L]
          nlinarith
  have hQ0 : 0 ≤ ((t - s) * ls ^ 3) ^ 2 := sq_nonneg _
  calc ((t - s) * ls ^ 3) ^ 2 * ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ /
        (((zdist2 L (y - b) : ℝ) + 1) * ((zdist2 L (z - b) : ℝ) + 1))
      ≤ ((t - s) * ls ^ 3) ^ 2 * (e * (5 * lam)) := mul_le_mul_of_nonneg_left hsum hQ0
    _ = 5 * lam * ((t - s) * ls ^ 2) ^ 2 * (ls ^ 2 * e) := by ring
    _ ≤ 5 * lam * 1 * (2 * cProp5 * lam * R) := by
        have hts2 : ((t - s) * ls ^ 2) ^ 2 ≤ 1 := by
          have h0 : 0 ≤ (t - s) * ls ^ 2 := mul_nonneg (by linarith) (by positivity)
          nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left hts2 (by linarith)) hlse
          (mul_nonneg (by positivity) he0) (by linarith)
    _ = 10 * cProp5 * lam ^ 2 * R := by ring

/-- **Anchor bound (b)** (shared with Case 5): with `Q = (t-s) ℓ_s³` and
`β = 1/(√(1-t) ℓ_t²)`, `Q² β Σ_b |Ξ(a₀, b)| / (|y - b|_L + 1) ≤ 2·20001·√5 cProp5 λ^{3/2} R³`
(`λ^{3/2} = λ √λ`; the exponential factor of `xiEntryBound` and `ExpInvSum` at
`c = 20000 ℓ_t`). -/
theorem Case4_anchor_b (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a₀ y : Z2 L) :
    ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
        ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ / ((zdist2 L (y - b) : ℝ) + 1) ≤
      2 * 20001 * Real.sqrt 5 * cProp5 * ((1 + Real.log L) * Real.sqrt (1 + Real.log L)) *
        rhoR L s t ^ 3 := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hlt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have he0 : 0 ≤ eT L s t := eT_nonneg hL hst ht
  have hlam : 1 ≤ 1 + Real.log L := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hlse := ellT_sq_eT_le hL hst ht
  have hRD := rhoR_mul_eq hL hs hst ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hq1 : ellT L t * Real.sqrt (1 - t) ≤ 1 := ellT_sqrt_le ht
  have hsq : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hsq2 : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  -- the lattice sum
  have hc : 0 < 20000 * ellT L t := by linarith
  have hK0 := expInvSum L hL (20000 * ellT L t) hc a₀ y
  have hsum : ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ / ((zdist2 L (y - b) : ℝ) + 1) ≤
      eT L s t * ((1 + 20000 * ellT L t) * Real.sqrt (5 + 4 * Real.log L)) := by
    calc ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ / ((zdist2 L (y - b) : ℝ) + 1)
        ≤ ∑ b : Z2 L, eT L s t * (Real.exp (-(zdist2 L (b - a₀) : ℝ) / (20000 * ellT L t)) /
            ((zdist2 L (b - y) : ℝ) + 1)) := sum_le_sum fun b _ => by
          have h := xiEntryBound L hL ξ hξ s t hs hst ht a₀ b
          rw [case4_zdist2_comm b a₀, case4_zdist2_comm b y, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right h (by positivity)
      _ = eT L s t * ∑ b : Z2 L, Real.exp (-(zdist2 L (b - a₀) : ℝ) / (20000 * ellT L t)) /
            ((zdist2 L (b - y) : ℝ) + 1) := by rw [mul_sum]
      _ ≤ eT L s t * ((1 + 20000 * ellT L t) * Real.sqrt (5 + 4 * Real.log L)) :=
          mul_le_mul_of_nonneg_left hK0 he0
  set e := eT L s t with he
  set lam := 1 + Real.log L with hlamdef
  set ls := ellT L s with hlsdef
  set lt := ellT L t with hltdef
  set R := rhoR L s t with hRdef
  set q := lt * Real.sqrt (1 - t) with hqdef
  have hq0 : 0 < q := mul_pos (by linarith) hsq
  have hq2 : q ^ 2 = lt ^ 2 * (1 - t) := by rw [hqdef, mul_pow, hsq2]
  -- `√(5 + 4 log L) ≤ √5 √λ` and `1 + 20000 ℓ_t ≤ 20001 ℓ_t`
  have hsqrt : Real.sqrt (5 + 4 * Real.log L) ≤ Real.sqrt 5 * Real.sqrt lam := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    exact Real.sqrt_le_sqrt (by rw [hlamdef]; linarith [Real.log_natCast_nonneg L])
  have h20 : 1 + 20000 * lt ≤ 20001 * lt := by linarith
  have hsum' : ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ / ((zdist2 L (y - b) : ℝ) + 1) ≤
      e * (20001 * lt * (Real.sqrt 5 * Real.sqrt lam)) := by
    refine hsum.trans (mul_le_mul_of_nonneg_left ?_ he0)
    exact mul_le_mul h20 hsqrt (Real.sqrt_nonneg _) (by linarith)
  -- `(t-s)² ℓ_s⁴ / q ≤ R²`
  have hW : (t - s) ^ 2 * ls ^ 4 / q ≤ R ^ 2 := by
    have hRq : R * q ^ 2 = ls ^ 2 * (1 - s) := by rw [hq2]; exact hRD
    have hq3 : q ^ 3 ≤ 1 := pow_le_one₀ hq0.le hq1
    rw [div_le_iff₀ hq0]
    have h1 : (t - s) ^ 2 * ls ^ 4 ≤ (ls ^ 2 * (1 - s)) ^ 2 := by
      have hts' : (t - s) ^ 2 ≤ (1 - s) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith [pow_nonneg (sq_nonneg ls) 2]
    rw [← hRq] at h1
    have h2 : (R * q ^ 2) ^ 2 = R ^ 2 * q * q ^ 3 := by ring
    rw [h2] at h1
    have hRq0 : 0 ≤ R ^ 2 * q := by positivity
    nlinarith
  have hβ : 1 / (Real.sqrt (1 - t) * lt ^ 2) * lt = 1 / q := by
    rw [hqdef]; field_simp
  calc ((t - s) * ls ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * lt ^ 2)) *
        ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ / ((zdist2 L (y - b) : ℝ) + 1)
      ≤ ((t - s) * ls ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * lt ^ 2)) *
          (e * (20001 * lt * (Real.sqrt 5 * Real.sqrt lam))) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = 20001 * Real.sqrt 5 * Real.sqrt lam * ((t - s) ^ 2 * ls ^ 4 *
          (1 / (Real.sqrt (1 - t) * lt ^ 2) * lt)) * (ls ^ 2 * e) := by ring
    _ = 20001 * Real.sqrt 5 * Real.sqrt lam * ((t - s) ^ 2 * ls ^ 4 / q) * (ls ^ 2 * e) := by
        rw [hβ]; ring
    _ ≤ 20001 * Real.sqrt 5 * Real.sqrt lam * R ^ 2 * (2 * cProp5 * lam * R) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hW (by positivity)) hlse
          (mul_nonneg (by positivity) he0) (by positivity)
    _ = 2 * 20001 * Real.sqrt 5 * cProp5 * (lam * Real.sqrt lam) * R ^ 3 := by ring

/-- **Anchor bound (c)** (shared with Case 5): with `Q = (t-s) ℓ_s³` and
`β = 1/(√(1-t) ℓ_t²)`, `Q² β² Σ_b |Ξ(a₀, b)| ≤ R³` (`xiRowBound`). -/
theorem Case4_anchor_c (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a₀ : Z2 L) :
    ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) ^ 2 *
        ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖ ≤ rhoR L s t ^ 3 := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hlt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hRD := rhoR_mul_eq hL hs hst ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hD1 : ellT L t ^ 2 * (1 - t) ≤ 1 := ellT_sq_mul_le ht
  have hsq : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hsq2 : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  have hrow := xiRowBound L hL ξ hξ s t hs hst ht a₀
  set ls := ellT L s with hlsdef
  set lt := ellT L t with hltdef
  set R := rhoR L s t with hRdef
  set D := lt ^ 2 * (1 - t) with hDdef
  have hD0 : 0 < D := mul_pos (pow_pos (by linarith) 2) h1t
  have hβ2 : (1 / (Real.sqrt (1 - t) * lt ^ 2)) ^ 2 = 1 / ((1 - t) * lt ^ 4) := by
    rw [div_pow, mul_pow, hsq2]; ring
  have heq : ((t - s) * ls ^ 3) ^ 2 * (1 / ((1 - t) * lt ^ 4)) * ((t - s) / (1 - t)) =
      (t - s) ^ 3 * ls ^ 6 / D ^ 2 := by
    rw [hDdef]; field_simp
  have hmain : (t - s) ^ 3 * ls ^ 6 / D ^ 2 ≤ R ^ 3 := by
    rw [div_le_iff₀ (pow_pos hD0 2)]
    have h1 : (t - s) ^ 3 * ls ^ 6 ≤ (ls ^ 2 * (1 - s)) ^ 3 := by
      have hts' : (t - s) ^ 3 ≤ (1 - s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      have : (ls ^ 2 * (1 - s)) ^ 3 = (1 - s) ^ 3 * ls ^ 6 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hts' (by positivity)
    rw [← hRD] at h1
    have h2 : (R * D) ^ 3 = R ^ 3 * D ^ 2 * D := by ring
    rw [h2] at h1
    have h3 : R ^ 3 * D ^ 2 * D ≤ R ^ 3 * D ^ 2 :=
      mul_le_of_le_one_right (by positivity) hD1
    linarith
  calc ((t - s) * ls ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * lt ^ 2)) ^ 2 *
        ∑ b : Z2 L, ‖xiMat L ξ s t a₀ b‖
      ≤ ((t - s) * ls ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * lt ^ 2)) ^ 2 * ((t - s) / (1 - t)) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = (t - s) ^ 3 * ls ^ 6 / D ^ 2 := by rw [hβ2, heq]
    _ ≤ R ^ 3 := hmain

end Anchor

/-! ## The three pieces around the anchor -/

section Pieces

variable {L : ℕ} [NeZero L]

/-- The three pieces of `Ξ(a, x)` around the anchor `c` (`r = x - c`, `Ξ = xiMat L 1 s t`):
`Ξ⁰ = Ξ(a, c)`, `Ξ¹ = (Ξ(a, c + r) - Ξ(a, c - r))/2`,
`Ξ² = (Ξ(a, c + r) + Ξ(a, c - r))/2 - Ξ(a, c)`. -/
private def piece (L : ℕ) [NeZero L] (s t : ℝ) (a c x : Z2 L) : Fin 3 → ℂ :=
  ![xiMat L 1 s t a c, (xiMat L 1 s t a x - xiMat L 1 s t a (c - (x - c))) / 2,
    (xiMat L 1 s t a x + xiMat L 1 s t a (c - (x - c))) / 2 - xiMat L 1 s t a c]

private theorem piece_zero_eq (s t : ℝ) (a c x : Z2 L) :
    piece L s t a c x 0 = xiMat L 1 s t a c := rfl

private theorem piece_one_eq (s t : ℝ) (a c x : Z2 L) :
    piece L s t a c x 1 = (xiMat L 1 s t a x - xiMat L 1 s t a (c - (x - c))) / 2 := rfl

private theorem piece_two_eq (s t : ℝ) (a c x : Z2 L) :
    piece L s t a c x 2 =
      (xiMat L 1 s t a x + xiMat L 1 s t a (c - (x - c))) / 2 - xiMat L 1 s t a c := rfl

/-- The pieces add up to `Ξ(a, x)`. -/
private theorem piece_sum (s t : ℝ) (a c x : Z2 L) :
    ∑ p : Fin 3, piece L s t a c x p = xiMat L 1 s t a x := by
  rw [Fin.sum_univ_three, piece_zero_eq, piece_one_eq, piece_two_eq]
  ring

/-- At `x = c` (`r = 0`) the pieces `Ξ¹`, `Ξ²` vanish. -/
private theorem piece_self (s t : ℝ) (a c : Z2 L) {p : Fin 3} (hp : p ≠ 0) :
    piece L s t a c c p = 0 := by
  have hc : c - (c - c) = c := by abel
  fin_cases p
  · exact absurd rfl hp
  · change piece L s t a c c 1 = 0
    rw [piece_one_eq, hc, sub_self, zero_div]
  · change piece L s t a c c 2 = 0
    rw [piece_two_eq, hc]; ring

/-- `Ξ¹` is odd under the reflection `x ↦ c - (x - c)`. -/
private theorem piece_one_mirror (s t : ℝ) (a c x : Z2 L) :
    piece L s t a c (c - (x - c)) 1 = - piece L s t a c x 1 := by
  have h : c - (c - (x - c) - c) = x := by abel
  rw [piece_one_eq, piece_one_eq, h]
  ring

private theorem norm_half (z : ℂ) : ‖z / 2‖ = ‖z‖ / 2 := by
  rw [norm_div]; simp

/-- `|Ξ^p(a, c, x)| ≤ |Ξ(a, x)| + |Ξ(a, c - (x - c))| + |Ξ(a, c)|`. -/
private theorem norm_piece_le (s t : ℝ) (a c x : Z2 L) (p : Fin 3) :
    ‖piece L s t a c x p‖ ≤
      ‖xiMat L 1 s t a x‖ + ‖xiMat L 1 s t a (c - (x - c))‖ + ‖xiMat L 1 s t a c‖ := by
  have hx := norm_nonneg (xiMat L 1 s t a x)
  have hy := norm_nonneg (xiMat L 1 s t a (c - (x - c)))
  have hc := norm_nonneg (xiMat L 1 s t a c)
  fin_cases p
  · change ‖piece L s t a c x 0‖ ≤ _
    rw [piece_zero_eq]; linarith
  · change ‖piece L s t a c x 1‖ ≤ _
    rw [piece_one_eq, norm_half]
    have := norm_sub_le (xiMat L 1 s t a x) (xiMat L 1 s t a (c - (x - c)))
    linarith
  · change ‖piece L s t a c x 2‖ ≤ _
    rw [piece_two_eq]
    have h1 := norm_sub_le ((xiMat L 1 s t a x + xiMat L 1 s t a (c - (x - c))) / 2)
      (xiMat L 1 s t a c)
    have h2 := norm_add_le (xiMat L 1 s t a x) (xiMat L 1 s t a (c - (x - c)))
    rw [norm_half] at h1
    linarith

/-- `|Ξ¹| ≤ 2 P_L (t-s) |r| (1/(|a-c|+1) + 1/(√(1-t) ℓ_t²))` (K1d at `c` with `±r`). -/
private theorem norm_piece_one_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (a c x : Z2 L) :
    ‖piece L s t a c x 1‖ ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (zdist2 L (x - c) : ℝ) *
        (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
  have h1 := xiFirstDiff L hL s t hs hst ht a c (x - c)
  have h2 := xiFirstDiff L hL s t hs hst ht a c (-(x - c))
  have e1 : c + (x - c) = x := by abel
  have e2 : c + -(x - c) = c - (x - c) := by abel
  rw [e1] at h1
  rw [e2, case4_zdist2_neg] at h2
  have heq : 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      ((zdist2 L (x - c) : ℝ) / ((zdist2 L (a - c) : ℝ) + 1) +
        (zdist2 L (x - c) : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2)) =
      2 * derivativePrefactor (10 ^ 14) L * (t - s) * (zdist2 L (x - c) : ℝ) *
        (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
    ring
  rw [heq] at h1 h2
  have hsplit : xiMat L 1 s t a x - xiMat L 1 s t a (c - (x - c)) =
      (xiMat L 1 s t a c - xiMat L 1 s t a (c - (x - c))) -
        (xiMat L 1 s t a c - xiMat L 1 s t a x) := by ring
  rw [piece_one_eq, norm_half, hsplit]
  have h3 := norm_sub_le (xiMat L 1 s t a c - xiMat L 1 s t a (c - (x - c)))
    (xiMat L 1 s t a c - xiMat L 1 s t a x)
  linarith

/-- `|Ξ²| ≤ 2 P_L (t-s) |r|² (1/(|a-c|²+1) + 1/ℓ_t²)` (K1e at `c`). -/
private theorem norm_piece_two_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (a c x : Z2 L) :
    ‖piece L s t a c x 2‖ ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (zdist2 L (x - c) : ℝ) ^ 2 *
        (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) := by
  have h := xiSecondDiff L hL s t hs hst ht a c (x - c)
  have e1 : c + (x - c) = x := by abel
  rw [e1] at h
  have heq : (xiMat L 1 s t a x + xiMat L 1 s t a (c - (x - c))) / 2 - xiMat L 1 s t a c =
      -((2 * xiMat L 1 s t a c - xiMat L 1 s t a x - xiMat L 1 s t a (c - (x - c))) / 2) := by
    ring
  rw [piece_two_eq, heq, norm_neg, norm_half]
  have heq2 : 4 * derivativePrefactor (10 ^ 14) L * (t - s) *
      ((zdist2 L (x - c) : ℝ) ^ 2 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) +
        (zdist2 L (x - c) : ℝ) ^ 2 / ellT L t ^ 2) =
      2 * (2 * derivativePrefactor (10 ^ 14) L * (t - s) * (zdist2 L (x - c) : ℝ) ^ 2 *
        (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2)) := by ring
  rw [heq2] at h
  linarith

/-- Window sum of any piece: `Σ_{|x - c| < ρ} |Ξ^p| ≤ 27 ρ² e` (`|Ξ| ≤ e`, `card ≤ 9ρ²`). -/
private theorem win_all (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (a c : Z2 L) (p : Fin 3) :
    ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x p‖ ≤
      27 * ρ ^ 2 * eT L s t := by
  have he : ∀ y, ‖xiMat L 1 s t a y‖ ≤ eT L s t := fun y =>
    xi_le_eT hL (by simp) hs hst ht a y
  have he0 := eT_nonneg hL hst ht
  calc ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x p‖
      ≤ ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), 3 * eT L s t :=
        sum_le_sum fun x _ => (norm_piece_le s t a c x p).trans
          (by linarith [he x, he (c - (x - c)), he c])
    _ = ((univ.filter fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ).card : ℝ) *
          (3 * eT L s t) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ρ ^ 2 * (3 * eT L s t) :=
        mul_le_mul_of_nonneg_right (card_near_le hρ c) (by linarith)
    _ = 27 * ρ ^ 2 * eT L s t := by ring

/-- Window sum of `Ξ¹`: `≤ 2 P_L (t-s) (1/(|a-c|+1) + β) · 9ρ³`. -/
private theorem win_one (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (a c : Z2 L) :
    ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x 1‖ ≤
      2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * ρ ^ 3) := by
  have hC : 0 ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
    have := Pl_nonneg L
    have : 0 ≤ t - s := by linarith
    positivity
  calc ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x 1‖
      ≤ ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
          2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              (zdist2 L (x - c) : ℝ) :=
        sum_le_sum fun x _ => (norm_piece_one_le hL hs hst ht a c x).trans (le_of_eq (by ring))
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
              (zdist2 L (x - c) : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Case4_window_sum_one hρ c) hC

/-- Window sum of `Ξ²`: `≤ 2 P_L (t-s) (1/(|a-c|²+1) + 1/ℓ_t²) · 9ρ⁴`. -/
private theorem win_two (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (a c : Z2 L) :
    ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x 2‖ ≤
      2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) * (9 * ρ ^ 4) := by
  have hC : 0 ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
      (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) := by
    have := Pl_nonneg L
    have : 0 ≤ t - s := by linarith
    positivity
  calc ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ‖piece L s t a c x 2‖
      ≤ ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
          2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) *
              (zdist2 L (x - c) : ℝ) ^ 2 :=
        sum_le_sum fun x _ => (norm_piece_two_le hL hs hst ht a c x).trans (le_of_eq (by ring))
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) *
            ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
              (zdist2 L (x - c) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Case4_window_sum_two hρ c) hC

/-- Full row of any piece: `Σ_x |Ξ^p| ≤ 2 (t-s)/(1-t) + L² e` (`xiRowBound` twice, and
`|Ξ(a,c)| ≤ e`). -/
private theorem row_all (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (a c : Z2 L) (p : Fin 3) :
    ∑ x : Z2 L, ‖piece L s t a c x p‖ ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by
  have hrow := xiRowBound L hL 1 (by simp) s t hs hst ht a
  have hmir : ∑ x : Z2 L, ‖xiMat L 1 s t a (c - (x - c))‖ =
      ∑ x : Z2 L, ‖xiMat L 1 s t a x‖ := by
    rw [← Equiv.sum_comp (Equiv.subLeft (c + c)) (fun y => ‖xiMat L 1 s t a y‖)]
    refine sum_congr rfl fun x _ => ?_
    have : c - (x - c) = c + c - x := by abel
    rw [this, Equiv.subLeft_apply]
  have hcard : ∑ _x : Z2 L, ‖xiMat L 1 s t a c‖ = (L : ℝ) ^ 2 * ‖xiMat L 1 s t a c‖ := by
    rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, ZMod.card]
    push_cast; ring
  have he : ‖xiMat L 1 s t a c‖ ≤ eT L s t := xi_le_eT hL (by simp) hs hst ht a c
  calc ∑ x : Z2 L, ‖piece L s t a c x p‖
      ≤ ∑ x : Z2 L, (‖xiMat L 1 s t a x‖ + ‖xiMat L 1 s t a (c - (x - c))‖ +
          ‖xiMat L 1 s t a c‖) := sum_le_sum fun x _ => norm_piece_le s t a c x p
    _ = ∑ x : Z2 L, ‖xiMat L 1 s t a x‖ + ∑ x : Z2 L, ‖xiMat L 1 s t a (c - (x - c))‖ +
          ∑ _x : Z2 L, ‖xiMat L 1 s t a c‖ := by rw [sum_add_distrib, sum_add_distrib]
    _ ≤ (t - s) / (1 - t) + (t - s) / (1 - t) + (L : ℝ) ^ 2 * eT L s t := by
        rw [hmir, hcard]
        have : (L : ℝ) ^ 2 * ‖xiMat L 1 s t a c‖ ≤ (L : ℝ) ^ 2 * eT L s t :=
          mul_le_mul_of_nonneg_left he (by positivity)
        linarith
    _ = 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by ring

end Pieces

/-! ## Sums anchored at `b₀` -/

section AnchorSum

variable {L : ℕ} [NeZero L]

/-- **Summing a product around an anchor, exactly**: `Σ_b ∏ᵢ g_i(b_j, b_i) =
Σ_x g_j(x, x) ∏_{i ≠ j} Σ_c g_i(x, c)`.  The equality form of `sum_prod_anchor_le` in
`KernelExpand.lean`; same proof, over a commutative semiring, `Fin n → Z2 L`.  Purely
combinatorial, so valid on `Z_L²`. -/
private theorem anchor_eq {R : Type*} [CommSemiring R] {n : ℕ} (g : Fin n → Z2 L → Z2 L → R)
    (j : Fin n) :
    ∑ b : Fin n → Z2 L, ∏ i, g i (b j) (b i) =
      ∑ x : Z2 L, g j x x * ∏ i ∈ univ.erase j, ∑ c : Z2 L, g i x c := by
  classical
  set h : Z2 L → Fin n → Z2 L → R := fun x i c =>
    if i = j then (if c = x then g i x c else 0) else g i x c with hh
  have h1 : ∀ b : Fin n → Z2 L, ∏ i, g i (b j) (b i) = ∑ x : Z2 L, ∏ i, h x i (b i) := by
    intro b
    rw [Finset.sum_eq_single (b j)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hh]
      split_ifs with hi
      · rfl
      · subst hi; exact absurd rfl ‹¬b i = b i›
      · rfl
    · intro x _ hx
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [hh, ite_true]
      rw [ite_eq_right_iff]
      intro hbx; exact absurd hbx.symm hx
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [KernelExpand_sum_prod_pi (h x), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  · simp only [hh, ite_true]
    rw [Finset.sum_ite_eq' Finset.univ x (g j x)]; simp
  · refine prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [hh, hij, ite_false]

end AnchorSum

/-! ## Numerical bookkeeping -/

section Numerics

/-- `X = 10⁶ (cProp5 + 8·10¹⁴ + 720)`; `cCase4 k = (4X)^k`. -/
private def case4X : ℝ := 10 ^ 6 * (cProp5 + (8 * 10 ^ 14 + 720))

private theorem cCase4_eq (k : ℕ) : cCase4 k = 4 ^ k * case4X ^ k := by
  unfold cCase4 case4X; rw [mul_pow]

private theorem case4X_ge_one : 1 ≤ case4X := by unfold case4X cProp5; norm_num

private theorem case4X_ge_B : 1 + 18 * cProp5 ≤ case4X := by unfold case4X cProp5; norm_num

private theorem case4X_ge_F : 2 + 2 * cProp5 ≤ case4X := by unfold case4X cProp5; norm_num

private theorem case4X_ge_G : 54 * cProp5 ≤ case4X := by unfold case4X cProp5; norm_num

private theorem case4X_iii : 198 * (8 * 10 ^ 14 + 720) * cProp5 ≤ case4X ^ 2 := by
  unfold case4X cProp5; norm_num

private theorem case4X_iv : 81000000 * (8 * 10 ^ 14 + 720) ^ 2 * cProp5 ≤ case4X ^ 3 := by
  unfold case4X cProp5; norm_num

/-- `3^k + 2^k ≤ 4^k` for `k ≥ 2`. -/
private theorem three_two_four {k : ℕ} (hk : 2 ≤ k) : (3 : ℝ) ^ k + 2 ^ k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
    rw [pow_succ, pow_succ, pow_succ]
    nlinarith

/-- The `δ`-terms: `B^{k-1} ≤ X^k λ^{k+1} K^{2k} R^k` for `B = (1 + 18 cProp5) λ K² R`. -/
private theorem num_T {k : ℕ} (hk : 2 ≤ k) {lam K R : ℝ} (hlam : 1 ≤ lam) (hK : 1 ≤ K)
    (hR : 1 ≤ R) :
    ((1 + 18 * cProp5) * lam * K ^ 2 * R) ^ (k - 1) ≤
      case4X ^ k * (lam ^ (k + 1) * K ^ (2 * k) * R ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case4X_ge_one
  have hXB := case4X_ge_B
  have hP : (0 : ℝ) ≤ 1 + 18 * cProp5 := by unfold cProp5; norm_num
  have hB0 : 0 ≤ (1 + 18 * cProp5) * lam * K ^ 2 * R := by
    have : 0 ≤ K ^ 2 := sq_nonneg K
    exact mul_nonneg (mul_nonneg (mul_nonneg hP (by linarith)) this) (by linarith)
  have hBle : (1 + 18 * cProp5) * lam * K ^ 2 * R ≤ case4X * lam * K ^ 2 * R := by
    have : 0 ≤ lam * K ^ 2 * R := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg K)) (by linarith)
    nlinarith
  have hbase : 0 ≤ case4X ^ m * lam ^ m * K ^ (2 * m) * R ^ m := by
    have : 0 ≤ case4X := by linarith
    have : 0 ≤ lam := by linarith
    have : 0 ≤ R := by linarith
    positivity
  have h1 : 1 ≤ case4X * lam ^ 2 * K ^ 2 * R := by
    have a1 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam
    have a2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
    have a3 : 1 ≤ case4X * lam ^ 2 := one_le_mul_of_one_le_of_one_le hX a1
    have a4 : 1 ≤ case4X * lam ^ 2 * K ^ 2 := one_le_mul_of_one_le_of_one_le a3 a2
    exact one_le_mul_of_one_le_of_one_le a4 hR
  calc ((1 + 18 * cProp5) * lam * K ^ 2 * R) ^ m ≤ (case4X * lam * K ^ 2 * R) ^ m :=
        pow_le_pow_left₀ hB0 hBle m
    _ = case4X ^ m * lam ^ m * K ^ (2 * m) * R ^ m := by ring
    _ ≤ case4X ^ m * lam ^ m * K ^ (2 * m) * R ^ m * (case4X * lam ^ 2 * K ^ 2 * R) :=
        le_mul_of_one_le_right hbase h1
    _ = case4X ^ (m + 1) * (lam ^ (m + 1 + 1) * K ^ (2 * (m + 1)) * R ^ (m + 1)) := by ring

/-- The far factor of the `δ`-terms: `Y^k ≤ X^k (λL²)^k Y^k`. -/
private theorem num_far_T {k : ℕ} {Y lamL : ℝ} (hY : 0 ≤ Y) (hl : 1 ≤ lamL) :
    Y ^ k ≤ case4X ^ k * (lamL ^ k * Y ^ k) := by
  have hX := case4X_ge_one
  have h1 : 1 ≤ case4X ^ k * lamL ^ k :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) (one_le_pow₀ hl)
  calc Y ^ k ≤ Y ^ k * (case4X ^ k * lamL ^ k) := le_mul_of_one_le_right (pow_nonneg hY k) h1
    _ = case4X ^ k * (lamL ^ k * Y ^ k) := by ring

/-- The far part of the all-`Ξ` terms: `y F^{k-1} ≤ X^k (λL²)^k Y^k` for `0 ≤ y ≤ Y`,
`0 ≤ F ≤ (2 + 2 cProp5) λL² Y`. -/
private theorem num_far_V {k : ℕ} (hk : 2 ≤ k) {y Y F lamL : ℝ} (hy : y ≤ Y)
    (hY : 1 ≤ Y) (hl : 1 ≤ lamL) (hF0 : 0 ≤ F) (hF : F ≤ (2 + 2 * cProp5) * lamL * Y) :
    y * F ^ (k - 1) ≤ case4X ^ k * (lamL ^ k * Y ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case4X_ge_one
  have hXF := case4X_ge_F
  have hFle : F ≤ case4X * lamL * Y := by
    have : 0 ≤ lamL * Y := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbase : 0 ≤ case4X ^ m * lamL ^ m * Y ^ (m + 1) := by
    have : 0 ≤ case4X := by linarith
    have : 0 ≤ lamL := by linarith
    have : 0 ≤ Y := by linarith
    positivity
  calc y * F ^ m ≤ Y * (case4X * lamL * Y) ^ m :=
        mul_le_mul hy (pow_le_pow_left₀ hF0 hFle m) (pow_nonneg hF0 m) (by linarith)
    _ = case4X ^ m * lamL ^ m * Y ^ (m + 1) := by ring
    _ ≤ case4X ^ m * lamL ^ m * Y ^ (m + 1) * (case4X * lamL) :=
        le_mul_of_one_le_right hbase (one_le_mul_of_one_le_of_one_le hX hl)
    _ = case4X ^ (m + 1) * (lamL ^ (m + 1) * Y ^ (m + 1)) := by ring

/-- The `Ξ²` group: `S G^{k-2} ≤ X^k λ^{k+1} K^{2k} R^k` for
`S ≤ 18 P_L K⁴ (10 cProp5 λ² + 1) R`, `P_L ≤ P'λ`, `0 ≤ G ≤ 54 cProp5 λ K² R`. -/
private theorem num_iii {k : ℕ} (hk : 2 ≤ k) {lam K R Pl G S : ℝ} (hlam : 1 ≤ lam) (hK : 1 ≤ K)
    (hR : 1 ≤ R) (hPl : Pl ≤ (8 * 10 ^ 14 + 720) * lam) (hG0 : 0 ≤ G)
    (hG : G ≤ 54 * cProp5 * lam * K ^ 2 * R)
    (hS : S ≤ 18 * Pl * K ^ 4 * ((10 * cProp5 * lam ^ 2 + 1) * R)) :
    S * G ^ (k - 2) ≤ case4X ^ k * (lam ^ (k + 1) * K ^ (2 * k) * R ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case4X_ge_one
  have hXG := case4X_ge_G
  have hX2 := case4X_iii
  have hP := case4_cProp5_ge_one
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hPlam : 1 ≤ cProp5 * lam ^ 2 :=
    one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hlam)
  -- `S ≤ X² λ³ K⁴ R²`
  have hS1 : S ≤ case4X ^ 2 * (lam ^ 3 * K ^ 4 * R ^ 2) := by
    have e1 : 18 * Pl * K ^ 4 * ((10 * cProp5 * lam ^ 2 + 1) * R) =
        18 * (Pl * (10 * cProp5 * lam ^ 2 + 1)) * (K ^ 4 * R) := by ring
    have h1 : Pl * (10 * cProp5 * lam ^ 2 + 1) ≤
        ((8 * 10 ^ 14 + 720) * lam) * (11 * cProp5 * lam ^ 2) :=
      mul_le_mul hPl (by linarith) (by linarith) (by positivity)
    have hKR : 0 ≤ K ^ 4 * R := mul_nonneg hK4 hR0
    have h2 : 18 * ((8 * 10 ^ 14 + 720) * lam * (11 * cProp5 * lam ^ 2)) =
        198 * (8 * 10 ^ 14 + 720) * cProp5 * lam ^ 3 := by ring
    have hl3 : 0 ≤ lam ^ 3 := pow_nonneg hlam0 3
    have hR2 : R ≤ R ^ 2 := by nlinarith
    calc S ≤ 18 * (Pl * (10 * cProp5 * lam ^ 2 + 1)) * (K ^ 4 * R) := e1 ▸ hS
      _ ≤ 18 * ((8 * 10 ^ 14 + 720) * lam * (11 * cProp5 * lam ^ 2)) * (K ^ 4 * R) := by
          have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 18)
          exact mul_le_mul_of_nonneg_right this hKR
      _ = 198 * (8 * 10 ^ 14 + 720) * cProp5 * lam ^ 3 * (K ^ 4 * R) := by rw [h2]
      _ ≤ case4X ^ 2 * lam ^ 3 * (K ^ 4 * R) := by
          have := mul_le_mul_of_nonneg_right hX2 hl3
          exact mul_le_mul_of_nonneg_right this hKR
      _ ≤ case4X ^ 2 * lam ^ 3 * (K ^ 4 * R ^ 2) := by
          have h0 : 0 ≤ case4X ^ 2 * lam ^ 3 := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2 hK4) h0
      _ = case4X ^ 2 * (lam ^ 3 * K ^ 4 * R ^ 2) := by ring
  have hGle : G ≤ case4X * (lam * K ^ 2 * R) := by
    have : 0 ≤ lam * K ^ 2 * R := mul_nonneg (mul_nonneg hlam0 (sq_nonneg K)) hR0
    nlinarith
  have hGm : G ^ m ≤ (case4X * (lam * K ^ 2 * R)) ^ m := pow_le_pow_left₀ hG0 hGle m
  have hA0 : 0 ≤ case4X ^ 2 * (lam ^ 3 * K ^ 4 * R ^ 2) := by positivity
  calc S * G ^ m ≤ case4X ^ 2 * (lam ^ 3 * K ^ 4 * R ^ 2) * (case4X * (lam * K ^ 2 * R)) ^ m :=
        mul_le_mul hS1 hGm (pow_nonneg hG0 m) hA0
    _ = case4X ^ (m + 2) * (lam ^ (m + 2 + 1) * K ^ (2 * (m + 2)) * R ^ (m + 2)) := by ring

/-- The two-`Ξ¹` group: `S G^{k-3} ≤ X^k λ^{k+1} K^{2k} R^k` for
`S ≤ (18 P_L)² K⁶ (10 cProp5 λ² R + 2 (2·20001 √5 cProp5 λ√λ R³) + R³)`. -/
private theorem num_iv {k : ℕ} (hk : 3 ≤ k) {lam K R Pl G S r5 sl : ℝ} (hlam : 1 ≤ lam)
    (hK : 1 ≤ K) (hR : 1 ≤ R) (hPl0 : 0 ≤ Pl) (hPl : Pl ≤ (8 * 10 ^ 14 + 720) * lam)
    (hG0 : 0 ≤ G) (hG : G ≤ 54 * cProp5 * lam * K ^ 2 * R) (hr50 : 0 ≤ r5)
    (hr5 : r5 ≤ 3) (hsl0 : 0 ≤ sl) (hsl : sl ≤ lam)
    (hS : S ≤ (18 * Pl) ^ 2 * K ^ 6 * (10 * cProp5 * lam ^ 2 * R +
      2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3)) :
    S * G ^ (k - 3) ≤ case4X ^ k * (lam ^ (k + 1) * K ^ (2 * k) * R ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  have hX := case4X_ge_one
  have hXG := case4X_ge_G
  have hX3 := case4X_iv
  have hP := case4_cProp5_ge_one
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hK6 : 0 ≤ K ^ 6 := by positivity
  have hPlam : 1 ≤ cProp5 * lam ^ 2 :=
    one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hlam)
  have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  have hR30 : 0 ≤ R ^ 3 := pow_nonneg hR0 3
  -- the bracket
  have hbr : 10 * cProp5 * lam ^ 2 * R + 2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) +
      R ^ 3 ≤ 250000 * (cProp5 * lam ^ 2) * R ^ 3 := by
    have b1 : 10 * cProp5 * lam ^ 2 * R ≤ 10 * (cProp5 * lam ^ 2) * R ^ 3 := by
      have : 0 ≤ 10 * (cProp5 * lam ^ 2) := by linarith
      nlinarith
    have b2 : r5 * (lam * sl) ≤ 3 * lam ^ 2 := by
      have : lam * sl ≤ lam ^ 2 := by nlinarith
      have : 0 ≤ lam * sl := mul_nonneg hlam0 hsl0
      nlinarith
    have b2' : 2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) ≤
        240012 * (cProp5 * lam ^ 2) * R ^ 3 := by
      have hPR : 0 ≤ cProp5 * R ^ 3 := mul_nonneg (by linarith) hR30
      have := mul_le_mul_of_nonneg_left b2 hPR
      nlinarith
    have b3 : R ^ 3 ≤ (cProp5 * lam ^ 2) * R ^ 3 := le_mul_of_one_le_left hR30 hPlam
    nlinarith
  have hPl2 : (18 * Pl) ^ 2 ≤ 324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2 := by
    have : 18 * Pl ≤ 18 * ((8 * 10 ^ 14 + 720) * lam) := by linarith
    have h := pow_le_pow_left₀ (by linarith) this 2
    calc (18 * Pl) ^ 2 ≤ (18 * ((8 * 10 ^ 14 + 720) * lam)) ^ 2 := h
      _ = 324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2 := by ring
  have hS1 : S ≤ case4X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) := by
    have hbr0 : 0 ≤ 10 * cProp5 * lam ^ 2 * R +
        2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3 := by
      have : 0 ≤ cProp5 := by linarith
      positivity
    calc S ≤ (18 * Pl) ^ 2 * K ^ 6 * (10 * cProp5 * lam ^ 2 * R +
          2 * (2 * 20001 * r5 * cProp5 * (lam * sl) * R ^ 3) + R ^ 3) := hS
      _ ≤ (324 * (8 * 10 ^ 14 + 720) ^ 2 * lam ^ 2) * K ^ 6 *
          (250000 * (cProp5 * lam ^ 2) * R ^ 3) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hPl2 hK6) hbr hbr0 ?_
          positivity
      _ = 81000000 * (8 * 10 ^ 14 + 720) ^ 2 * cProp5 * (lam ^ 4 * K ^ 6 * R ^ 3) := by ring
      _ ≤ case4X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) :=
          mul_le_mul_of_nonneg_right hX3 (by positivity)
  have hGle : G ≤ case4X * (lam * K ^ 2 * R) := by
    have : 0 ≤ lam * K ^ 2 * R := mul_nonneg (mul_nonneg hlam0 (sq_nonneg K)) hR0
    nlinarith
  have hGm : G ^ m ≤ (case4X * (lam * K ^ 2 * R)) ^ m := pow_le_pow_left₀ hG0 hGle m
  have hA0 : 0 ≤ case4X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) := by positivity
  calc S * G ^ m ≤ case4X ^ 3 * (lam ^ 4 * K ^ 6 * R ^ 3) * (case4X * (lam * K ^ 2 * R)) ^ m :=
        mul_le_mul hS1 hGm (pow_nonneg hG0 m) hA0
    _ = case4X ^ (m + 3) * (lam ^ (m + 3 + 1) * K ^ (2 * (m + 3)) * R ^ (m + 3)) := by ring

end Numerics

/-! ## The terms of the expansion -/

section Terms

variable {L : ℕ} [NeZero L]

/-- The all-`Ξ` term with the piece pattern `f : Fin k → Fin 3`, anchored at `b₀`:
`V_f = Σ_b ∏_l Ξ^{f l}(a_l; b₀, b_l) A_b`. -/
private def Vterm {k : ℕ} [NeZero k] (L : ℕ) [NeZero L] (s t : ℝ) (a : Fin k → Z2 L)
    (A : (Fin k → Z2 L) → ℂ) (f : Fin k → Fin 3) : ℂ :=
  ∑ b : Fin k → Z2 L, (∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b

/-- **The near/far split of `V_f`** (anchor `b₀`, `f 0 = 0`): given window bounds `W_l(c)` for the
pieces `l ≠ 0`, `|V_f| ≤ M Σ_c |Ξ(a₀, c)| ∏_{l ≠ 0} W_l(c) + δ_A ((t-s)/(1-t)) F^{k-1}`,
`F = 2 (t-s)/(1-t) + L² e` (`row_all`). -/
private theorem norm_V_le {k : ℕ} [NeZero k] (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a : Fin k → Z2 L) (f : Fin k → Fin 3) (hf0 : f 0 = 0) {ρ M δA : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hdec : DecayWin L ρ δA A) (W : Fin k → Z2 L → ℝ)
    (hW : ∀ l, l ≠ 0 → ∀ c, ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
      ‖piece L s t (a l) c x (f l)‖ ≤ W l c) :
    ‖Vterm L s t a A f‖ ≤
      M * ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * ∏ l ∈ univ.erase 0, W l c +
        δA * ((t - s) / (1 - t) *
          (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1)) := by
  classical
  set ψ : Fin k → Z2 L → Z2 L → ℝ := fun l c x => ‖piece L s t (a l) c x (f l)‖ with hψ
  set ψn : Fin k → Z2 L → Z2 L → ℝ := fun l c x =>
    if (zdist2 L (x - c) : ℝ) < ρ then ψ l c x else 0 with hψn
  have hψ0 : ∀ l c x, 0 ≤ ψ l c x := fun _ _ _ => norm_nonneg _
  have hψn0 : ∀ l c x, 0 ≤ ψn l c x := by
    intro l c x; simp only [hψn]; split_ifs <;> first | exact hψ0 _ _ _ | exact le_rfl
  have hpt : ∀ b : Fin k → Z2 L, ‖(∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b‖ ≤
      M * ∏ l, ψn l (b 0) (b l) + δA * ∏ l, ψ l (b 0) (b l) := by
    intro b
    rw [norm_mul, norm_prod]
    have hP0 : 0 ≤ ∏ l, ψ l (b 0) (b l) := prod_nonneg fun l _ => hψ0 _ _ _
    have hPn0 : 0 ≤ ∏ l, ψn l (b 0) (b l) := prod_nonneg fun l _ => hψn0 _ _ _
    change (∏ l, ψ l (b 0) (b l)) * ‖A b‖ ≤ _
    by_cases hfar : ρ ≤ (KLoop.maxDist L b : ℝ)
    · have h1 : (∏ l, ψ l (b 0) (b l)) * ‖A b‖ ≤ (∏ l, ψ l (b 0) (b l)) * δA :=
        mul_le_mul_of_nonneg_left (hdec b hfar) hP0
      nlinarith [mul_nonneg hM hPn0]
    · push Not at hfar
      have hd : ∀ l, (zdist2 L (b l - b 0) : ℝ) < ρ := by
        intro l
        have h := Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (b p.1 - b p.2))
          (Finset.mem_univ (l, 0))
        have h' : (zdist2 L (b l - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by
          exact_mod_cast h
        linarith
      have hgeq : ∏ l, ψn l (b 0) (b l) = ∏ l, ψ l (b 0) (b l) := by
        refine prod_congr rfl fun l _ => ?_
        simp only [hψn, ite_eq_left (hd l)]
      rw [hgeq]
      have h1 : (∏ l, ψ l (b 0) (b l)) * ‖A b‖ ≤ (∏ l, ψ l (b 0) (b l)) * M :=
        mul_le_mul_of_nonneg_left (hAM b) hP0
      nlinarith [mul_nonneg hδ hP0]
  have hnear : ∑ b : Fin k → Z2 L, ∏ l, ψn l (b 0) (b l) ≤
      ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * ∏ l ∈ univ.erase 0, W l c := by
    rw [anchor_eq ψn 0]
    refine sum_le_sum fun c _ => ?_
    have h0 : ψn 0 c c = ‖xiMat L 1 s t (a 0) c‖ := by
      simp only [hψn, hψ, sub_self, zdist2_zero, Nat.cast_zero, ite_eq_left hρ, hf0, piece_zero_eq]
    rw [h0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine prod_le_prod₀ (fun l _ => sum_nonneg fun x _ => hψn0 _ _ _) (fun l hl => ?_)
    have hl0 : l ≠ 0 := ne_of_mem_erase hl
    calc ∑ x : Z2 L, ψn l c x
        = ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ), ψ l c x := by
          rw [sum_filter]
      _ ≤ W l c := hW l hl0 c
  have hF0 : 0 ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by
    have h1 : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
    have h2 := eT_nonneg hL hst ht
    positivity
  have hfar : ∑ b : Fin k → Z2 L, ∏ l, ψ l (b 0) (b l) ≤
      (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) := by
    rw [anchor_eq ψ 0]
    have hprod : ∀ c, ∏ l ∈ univ.erase 0, ∑ x : Z2 L, ψ l c x ≤
        (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) := by
      intro c
      calc ∏ l ∈ univ.erase 0, ∑ x : Z2 L, ψ l c x
          ≤ ∏ _l ∈ univ.erase (0 : Fin k), (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) :=
            prod_le_prod₀ (fun l _ => sum_nonneg fun x _ => hψ0 _ _ _)
              (fun l _ => row_all hL hs hst ht (a l) c (f l))
        _ = (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) := by
            rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have hFk : 0 ≤ (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) :=
      pow_nonneg hF0 _
    calc ∑ c : Z2 L, ψ 0 c c * ∏ l ∈ univ.erase 0, ∑ x : Z2 L, ψ l c x
        ≤ ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ *
            (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) :=
          sum_le_sum fun c _ => by
            have h0 : ψ 0 c c = ‖xiMat L 1 s t (a 0) c‖ := by
              simp only [hψ, hf0, piece_zero_eq]
            rw [h0]; exact mul_le_mul_of_nonneg_left (hprod c) (norm_nonneg _)
      _ = (∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖) *
            (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) := by rw [sum_mul]
      _ ≤ (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) :=
          mul_le_mul_of_nonneg_right (xiRowBound L hL 1 (by simp) s t hs hst ht (a 0)) hFk
  unfold Vterm
  calc ‖∑ b : Fin k → Z2 L, (∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b‖
      ≤ ∑ b : Fin k → Z2 L, ‖(∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : Fin k → Z2 L, (M * ∏ l, ψn l (b 0) (b l) + δA * ∏ l, ψ l (b 0) (b l)) :=
        sum_le_sum fun b _ => hpt b
    _ = M * ∑ b : Fin k → Z2 L, ∏ l, ψn l (b 0) (b l) +
          δA * ∑ b : Fin k → Z2 L, ∏ l, ψ l (b 0) (b l) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hnear hM) (mul_le_mul_of_nonneg_left hfar hδ)

/-- `V_f = 0` if `f 0 ≠ 0` (`Ξ¹₀ = Ξ²₀ = 0` at `r₀ = 0`). -/
private theorem V_eq_zero_of_f0 {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin k → Z2 L)
    (A : (Fin k → Z2 L) → ℂ) (f : Fin k → Fin 3) (hf : f 0 ≠ 0) : Vterm L s t a A f = 0 := by
  unfold Vterm
  refine sum_eq_zero fun b _ => ?_
  rw [prod_eq_zero (mem_univ 0) (piece_self s t (a 0) (b 0) (p := f 0) hf), zero_mul]

/-- **Case (i)**: `V_f = 0` if every piece is `Ξ⁰` (`SumZero` at `b₀`). -/
private theorem V_eq_zero_of_all0 {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin k → Z2 L)
    (A : (Fin k → Z2 L) → ℂ) (hsz : SumZero L A) (f : Fin k → Fin 3) (hf : ∀ l, f l = 0) :
    Vterm L s t a A f = 0 := by
  classical
  unfold Vterm
  have h1 : ∀ b : Fin k → Z2 L, (∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b =
      (∏ l, xiMat L 1 s t (a l) (b 0)) * A b := by
    intro b
    congr 1
    exact prod_congr rfl fun l _ => by rw [hf l, piece_zero_eq]
  rw [sum_congr rfl fun b _ => h1 b, ← sum_fiberwise univ (fun b : Fin k → Z2 L => b 0)]
  refine sum_eq_zero fun c _ => ?_
  have h2 : ∑ b ∈ univ.filter (fun b : Fin k → Z2 L => b 0 = c),
      (∏ l, xiMat L 1 s t (a l) (b 0)) * A b =
      ∑ b ∈ univ.filter (fun b : Fin k → Z2 L => b 0 = c),
        (∏ l, xiMat L 1 s t (a l) c) * A b :=
    sum_congr rfl fun b hb => by rw [(mem_filter.1 hb).2]
  rw [h2, ← mul_sum, hsz c, mul_zero]

/-- **Case (ii)**: `V_f = 0` if exactly one piece is `Ξ¹` and the others are `Ξ⁰`
(`Symmetric`, via the involution `b ↦ b₀ - (b - b₀)`). -/
private theorem V_eq_zero_of_one {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin k → Z2 L)
    (A : (Fin k → Z2 L) → ℂ) (hsym : Symmetric L A) (f : Fin k → Fin 3) (i : Fin k)
    (hfi : f i = 1) (hf : ∀ l, l ≠ i → f l = 0) : Vterm L s t a A f = 0 := by
  classical
  unfold Vterm
  set φ : (Fin k → Z2 L) → (Fin k → Z2 L) := fun b l => b 0 - (b l - b 0) with hφ
  have hφ0 : ∀ b, φ b 0 = b 0 := by intro b; simp [hφ]
  have hinv : Function.Involutive φ := by
    intro b; funext l; simp only [hφ]; abel
  set F : (Fin k → Z2 L) → ℂ := fun b => (∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b
    with hF
  have hneg : ∀ b, F (φ b) = -F b := by
    intro b
    have hA : A (φ b) = A b := by
      have h : A (fun l => b 0 + (b l - b 0)) = A (fun l => b 0 - (b l - b 0)) :=
        hsym (b 0) (fun l => b l - b 0) (by simp)
      have e1 : (fun l => b 0 + (b l - b 0)) = b := by funext l; abel
      rw [e1] at h
      exact h.symm
    have hP : ∏ l, piece L s t (a l) (φ b 0) (φ b l) (f l) =
        -∏ l, piece L s t (a l) (b 0) (b l) (f l) := by
      rw [hφ0, ← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ _ (mem_univ i)]
      have h1 : piece L s t (a i) (b 0) (φ b i) (f i) = -piece L s t (a i) (b 0) (b i) (f i) := by
        rw [hfi]; exact piece_one_mirror s t (a i) (b 0) (b i)
      have h2 : ∏ l ∈ univ.erase i, piece L s t (a l) (b 0) (φ b l) (f l) =
          ∏ l ∈ univ.erase i, piece L s t (a l) (b 0) (b l) (f l) := by
        refine prod_congr rfl fun l hl => ?_
        rw [hf l (ne_of_mem_erase hl), piece_zero_eq, piece_zero_eq]
      rw [h1, h2, neg_mul]
    simp only [hF]
    rw [hP, hA, neg_mul]
  have hsum : ∑ b, F (φ b) = ∑ b, F b :=
    Equiv.sum_comp (Function.Involutive.toPerm φ hinv) F
  have h2 : ∑ b, F b = -∑ b, F b := by
    rw [← sum_neg_distrib, ← hsum]
    exact sum_congr rfl fun b _ => hneg b
  change ∑ b, F b = 0
  linear_combination h2 / 2

/-- `∏_{l ≠ 0} (if l = i then D else G) = D G^{k-2}` for `i ≠ 0`. -/
private theorem prod_erase_ite_one {k : ℕ} [NeZero k] (i : Fin k) (hi : i ≠ 0) (D G : ℝ) :
    ∏ l ∈ univ.erase (0 : Fin k), (if l = i then D else G) = D * G ^ (k - 2) := by
  have hmem : i ∈ univ.erase (0 : Fin k) := mem_erase.2 ⟨hi, mem_univ i⟩
  rw [← mul_prod_erase _ _ hmem, ite_eq_left rfl]
  congr 1
  rw [prod_congr rfl fun l hl => ite_eq_right (ne_of_mem_erase hl), prod_const,
    card_erase_of_mem hmem, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  congr 1

/-- `∏_{l ≠ 0} (if l = i then Dᵢ else if l = j then Dⱼ else G) = Dᵢ (Dⱼ G^{k-3})` for distinct
`i, j ≠ 0`; also `3 ≤ k`. -/
private theorem prod_erase_ite_two {k : ℕ} [NeZero k] (i j : Fin k) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) (Di Dj G : ℝ) :
    3 ≤ k ∧ ∏ l ∈ univ.erase (0 : Fin k), (if l = i then Di else if l = j then Dj else G) =
      Di * (Dj * G ^ (k - 3)) := by
  have hmi : i ∈ univ.erase (0 : Fin k) := mem_erase.2 ⟨hi, mem_univ i⟩
  have hmj : j ∈ (univ.erase (0 : Fin k)).erase i :=
    mem_erase.2 ⟨Ne.symm hij, mem_erase.2 ⟨hj, mem_univ j⟩⟩
  have hc2 : ((univ.erase (0 : Fin k)).erase i).card = k - 1 - 1 := by
    rw [card_erase_of_mem hmi, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hk : 3 ≤ k := by
    have := card_pos.2 ⟨j, hmj⟩
    omega
  refine ⟨hk, ?_⟩
  rw [← mul_prod_erase _ _ hmi, ite_eq_left rfl]
  congr 1
  rw [← mul_prod_erase _ _ hmj, ite_eq_right (Ne.symm hij), ite_eq_left rfl]
  congr 1
  rw [prod_congr rfl fun l hl => by
      rw [ite_eq_right (ne_of_mem_erase (mem_of_mem_erase hl)), ite_eq_right (ne_of_mem_erase hl)],
    prod_const, card_erase_of_mem hmj, hc2]
  congr 1

private theorem div_prod_eq_aux (x u v : ℝ) : x / (u * v) = x * (1 / u) * (1 / v) := by
  rw [mul_one_div, mul_one_div, div_div]

/-- The two pieces `δ`, `Ξ` of `ψ = 1 + Ξ`. -/
private def dpiece (L : ℕ) [NeZero L] (s t : ℝ) : Fin 2 → Matrix (Z2 L) (Z2 L) ℂ :=
  ![1, xiMat L 1 s t]

/-- **A term with a `δ` at `j`** (`S ≠ [k]`): anchored window bound
(`KernelExpand_core_bound`, anchor `j`): `≤ M B^{k-1} + δ_A ((1-s)/(1-t))^k`,
`B = (1 + 18 cProp5) λ K² R`. -/
private theorem norm_T_le {k : ℕ} [NeZero k] (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (hK : 1 ≤ K) (a : Fin k → Z2 L) (g : Fin k → Fin 2) (j : Fin k) (hj : g j = 0)
    {M δA : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hdec : DecayWin L (ellT L s * K) δA A) :
    ‖∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ ≤
      M * ((1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t) ^ (k - 1) +
        δA * ((1 - s) / (1 - t)) ^ k := by
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * K := by nlinarith
  have hρ1 : 1 ≤ ellT L s * K := by nlinarith
  have hlam := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have he0 := eT_nonneg hL hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  set Bc := (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t with hBc
  set Y := (1 - s) / (1 - t) with hY
  have hY1 : 1 ≤ Y := by rw [hY, le_div_iff₀ h1t]; linarith
  have hts : (t - s) / (1 - t) ≤ Y := div_le_div_of_nonneg_right (by linarith) h1t.le
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hlKR : 1 ≤ (1 + Real.log L) * K ^ 2 * rhoR L s t :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hlam hK2) hR1
  have hB1 : 1 ≤ Bc := by
    have : Bc = (1 + 18 * cProp5) * ((1 + Real.log L) * K ^ 2 * rhoR L s t) := by
      rw [hBc]; ring
    rw [this]; exact one_le_mul_of_one_le_of_one_le (by linarith) hlKR
  -- the window of `Ξ`
  have hwinX : ∀ x y : Z2 L, ∑ c ∈ univ.filter (fun c : Z2 L =>
      (zdist2 L (x - c) : ℝ) ≤ ellT L s * K), ‖xiMat L 1 s t y c‖ ≤ Bc := by
    intro x y
    have hcard := RBM.KLoop.card_ball_le L x (ellT L s * K) hρ0
    calc ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
          ‖xiMat L 1 s t y c‖
        ≤ ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
            eT L s t := sum_le_sum fun c _ => xi_le_eT hL (by simp) hs hst ht y c
      _ = ((univ.filter fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K).card : ℝ) *
            eT L s t := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * (ellT L s * K) + 1) ^ 2 * eT L s t := mul_le_mul_of_nonneg_right hcard he0
      _ ≤ 9 * (ellT L s * K) ^ 2 * eT L s t := by
          have : (2 * (ellT L s * K) + 1) ^ 2 ≤ 9 * (ellT L s * K) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this he0
      _ = 9 * K ^ 2 * (ellT L s ^ 2 * eT L s t) := by ring
      _ ≤ 9 * K ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t) :=
          mul_le_mul_of_nonneg_left hlse (by positivity)
      _ ≤ Bc := by
          rw [hBc]
          have : 0 ≤ (1 + Real.log L) * K ^ 2 * rhoR L s t := by linarith
          nlinarith
  -- row and window sums of the two pieces
  have hrow : ∀ (p : Fin 2) (y : Z2 L), ∑ c : Z2 L, ‖dpiece L s t p y c‖ ≤ Y := by
    intro p y
    fin_cases p
    · change ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ ≤ Y
      rw [KernelExpand_sum_norm_one_row]; exact hY1
    · change ∑ c : Z2 L, ‖xiMat L 1 s t y c‖ ≤ Y
      exact (xiRowBound L hL 1 (by simp) s t hs hst ht y).trans hts
  have hwin : ∀ (p : Fin 2) (x y : Z2 L), ∑ c ∈ univ.filter (fun c : Z2 L =>
      (zdist2 L (x - c) : ℝ) ≤ ellT L s * K), ‖dpiece L s t p y c‖ ≤ Bc := by
    intro p x y
    fin_cases p
    · change ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
        ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ ≤ Bc
      calc ∑ c ∈ univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ellT L s * K),
            ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖
          ≤ ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) y c‖ :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun c _ _ => norm_nonneg _)
        _ = 1 := KernelExpand_sum_norm_one_row y
        _ ≤ Bc := hB1
    · exact hwinX x y
  have hanc : ∑ c : Z2 L, ‖dpiece L s t (g j) (a j) c‖ ≤ 1 := by
    rw [hj]
    change ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a j) c‖ ≤ 1
    rw [KernelExpand_sum_norm_one_row]
  have hcore := KernelExpand_core_bound (L := L)
    (fun l c => ‖dpiece L s t (g l) (a l) c‖) (fun l c => norm_nonneg _) (A := A)
    (ρ := ellT L s * K) (M := M) (δA := δA) (r := Y) (Rj := 1) (B := Bc) hM hδ hAM hdec j
    (fun l => hrow (g l) (a l)) hanc (fun l _ x => hwin (g l) x (a l))
  calc ‖∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖
      ≤ ∑ b : Fin k → Z2 L, ‖(∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ := norm_sum_le _ _
    _ = ∑ b : Fin k → Z2 L, (∏ l, ‖dpiece L s t (g l) (a l) (b l)‖) * ‖A b‖ := by
        refine sum_congr rfl fun b _ => ?_
        rw [norm_mul, norm_prod]
    _ ≤ M * (1 * Bc ^ (k - 1)) + δA * Y ^ k := hcore
    _ = M * Bc ^ (k - 1) + δA * Y ^ k := by ring

omit [NeZero L] in
/-- The far bound of the all-`Ξ` terms. -/
private theorem far_V_le {k : ℕ} (hk : 2 ≤ k) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) :
    (t - s) / (1 - t) * (2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t) ^ (k - 1) ≤
      case4X ^ k * (((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k) := by
  have h1t : 0 < 1 - t := by linarith
  have hY1 : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hts : (t - s) / (1 - t) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_right (by linarith) h1t.le
  have hts0 : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) h1t.le
  have hlam := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hlL : 1 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hlam hL1
  have hL2e := L2_eT_le hL hs hst ht
  have he0 := eT_nonneg hL hst ht
  have hF0 : 0 ≤ 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t := by positivity
  have hF : 2 * ((t - s) / (1 - t)) + (L : ℝ) ^ 2 * eT L s t ≤
      (2 + 2 * cProp5) * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by
    have h2 : 2 * ((t - s) / (1 - t)) ≤
        2 * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by
      have : (1 - s) / (1 - t) ≤ ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) :=
        le_mul_of_one_le_left (by linarith) hlL
      linarith
    have h3 : 2 * cProp5 * (1 + Real.log L) * (L : ℝ) ^ 2 * ((1 - s) / (1 - t)) =
        2 * cProp5 * ((1 + Real.log L) * (L : ℝ) ^ 2) * ((1 - s) / (1 - t)) := by ring
    nlinarith
  exact num_far_V hk hts hY1 hlL hF0 hF

/-- **Case (iii)**: some piece is `Ξ²` (group 1). -/
private theorem bound_iii {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (hK : 1 ≤ K) (a : Fin k → Z2 L) (f : Fin k → Fin 3)
    (hf0 : f 0 = 0) (i : Fin k) (hi0 : i ≠ 0) (hi : f i = 2) {M δA : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hdec : DecayWin L (ellT L s * K) δA A) :
    ‖Vterm L s t a A f‖ ≤
      M * (case4X ^ k * ((1 + Real.log L) ^ (k + 1) * K ^ (2 * k) * rhoR L s t ^ k)) +
        δA * (case4X ^ k * (((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k)) := by
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hlt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hρ1 : 1 ≤ ellT L s * K := by nlinarith
  have hlam := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have he0 := eT_nonneg hL hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  have hPl0 := Pl_nonneg L
  set ρ := ellT L s * K with hρ
  set Pl := derivativePrefactor (10 ^ 14) L with hPldef
  set G := 27 * ρ ^ 2 * eT L s t with hG
  set D2 : Z2 L → ℝ := fun c => 2 * Pl * (t - s) *
    (1 / ((zdist2 L (a i - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2) * (9 * ρ ^ 4) with hD2
  set W : Fin k → Z2 L → ℝ := fun l c => if l = i then D2 c else G with hW
  have hWb : ∀ l, l ≠ 0 → ∀ c, ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
      ‖piece L s t (a l) c x (f l)‖ ≤ W l c := by
    intro l _ c
    by_cases hli : l = i
    · subst hli
      simp only [hW, ite_eq_left rfl, hi, hD2]
      exact win_two hL hs hst ht hρ1 (a l) c
    · simp only [hW, ite_eq_right hli, hG]
      exact win_all hL hs hst ht hρ1 (a l) c (f l)
  have h := norm_V_le hL hs hst ht a f hf0 (by linarith) hM hδ hAM hdec W hWb
  refine h.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left (far_V_le hk hL hs hst ht) hδ))
  refine mul_le_mul_of_nonneg_left ?_ hM
  -- the near part
  have hprod : ∀ c, ∏ l ∈ univ.erase 0, W l c = D2 c * G ^ (k - 2) := fun c =>
    prod_erase_ite_one i hi0 (D2 c) G
  have hS : ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * D2 c ≤
      18 * Pl * K ^ 4 * ((10 * cProp5 * (1 + Real.log L) ^ 2 + 1) * rhoR L s t) := by
    have hanc := anchor_sq hL (ξ := 1) (by simp) hs hst ht (a 0) (a i)
    have heq : ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * D2 c = 18 * Pl * K ^ 4 *
        ((t - s) * ellT L s ^ 4 * ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ *
          (1 / ((zdist2 L (a i - c) : ℝ) ^ 2 + 1) + 1 / ellT L t ^ 2)) := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      simp only [hD2, hρ]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hanc (by positivity)
  have hGle : G ≤ 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by
    have : G = 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t) := by rw [hG, hρ]; ring
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left hlse (by positivity : (0 : ℝ) ≤ 27 * K ^ 2)
    calc 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t)
        ≤ 27 * K ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t) := h2
      _ = 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by ring
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hnum := num_iii hk hlam hK hR1 (Pl_le L) hG0 hGle hS
  calc ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * ∏ l ∈ univ.erase 0, W l c
      = (∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * D2 c) * G ^ (k - 2) := by
        rw [sum_mul]
        refine sum_congr rfl fun c _ => ?_
        rw [hprod c]; ring
    _ ≤ _ := hnum

/-- **Case (iv)**: no `Ξ²` and two pieces `Ξ¹` (group 2). -/
private theorem bound_iv {k : ℕ} [NeZero k] (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (hK : 1 ≤ K) (a : Fin k → Z2 L) (f : Fin k → Fin 3)
    (hf0 : f 0 = 0) (i j : Fin k) (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j) (hi : f i = 1)
    (hj : f j = 1) {M δA : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ M) (hdec : DecayWin L (ellT L s * K) δA A) :
    ‖Vterm L s t a A f‖ ≤
      M * (case4X ^ k * ((1 + Real.log L) ^ (k + 1) * K ^ (2 * k) * rhoR L s t ^ k)) +
        δA * (case4X ^ k * (((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k)) := by
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hls : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ1 : 1 ≤ ellT L s * K := by nlinarith
  have hlam := case4_lam_ge_one L
  have hP := case4_cProp5_ge_one
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have he0 := eT_nonneg hL hst ht
  have hlse := ellT_sq_eT_le hL hst ht
  have hPl0 := Pl_nonneg L
  have hk3 := (prod_erase_ite_two i j hi0 hj0 hij (1 : ℝ) 1 1).1
  -- the anchor bounds (a)–(c)
  have ha := Case4_anchor_a hL (ξ := 1) (by simp) hs hst ht (a 0) (a i) (a j)
  have hbi := Case4_anchor_b hL (ξ := 1) (by simp) hs hst ht (a 0) (a i)
  have hbj := Case4_anchor_b hL (ξ := 1) (by simp) hs hst ht (a 0) (a j)
  have hc := Case4_anchor_c hL (ξ := 1) (by simp) hs hst ht (a 0)
  have hS : ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ *
      ((2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a i - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * (ellT L s * K) ^ 3)) *
        (2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          (1 / ((zdist2 L (a j - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
          (9 * (ellT L s * K) ^ 3))) ≤
      (18 * derivativePrefactor (10 ^ 14) L) ^ 2 * K ^ 6 *
        (10 * cProp5 * (1 + Real.log L) ^ 2 * rhoR L s t +
          2 * (2 * 20001 * Real.sqrt 5 * cProp5 *
            ((1 + Real.log L) * Real.sqrt (1 + Real.log L)) * rhoR L s t ^ 3) +
          rhoR L s t ^ 3) := by
    have heq : ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ *
        ((2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a i - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            (9 * (ellT L s * K) ^ 3)) *
          (2 * derivativePrefactor (10 ^ 14) L * (t - s) *
            (1 / ((zdist2 L (a j - c) : ℝ) + 1) + 1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
            (9 * (ellT L s * K) ^ 3))) =
        (18 * derivativePrefactor (10 ^ 14) L) ^ 2 * K ^ 6 *
          (((t - s) * ellT L s ^ 3) ^ 2 * ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ /
              (((zdist2 L (a i - c) : ℝ) + 1) * ((zdist2 L (a j - c) : ℝ) + 1)) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ / ((zdist2 L (a i - c) : ℝ) + 1) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ / ((zdist2 L (a j - c) : ℝ) + 1) +
            ((t - s) * ellT L s ^ 3) ^ 2 * (1 / (Real.sqrt (1 - t) * ellT L t ^ 2)) ^ 2 *
              ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun c _ => ?_
      rw [div_prod_eq_aux ‖xiMat L 1 s t (a 0) c‖ ((zdist2 L (a i - c) : ℝ) + 1)
        ((zdist2 L (a j - c) : ℝ) + 1)]
      ring
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  set ρ := ellT L s * K with hρ
  set Pl := derivativePrefactor (10 ^ 14) L with hPldef
  set β := 1 / (Real.sqrt (1 - t) * ellT L t ^ 2) with hβ
  set G := 27 * ρ ^ 2 * eT L s t with hG
  set D1 : Fin k → Z2 L → ℝ := fun l c => 2 * Pl * (t - s) *
    (1 / ((zdist2 L (a l - c) : ℝ) + 1) + β) * (9 * ρ ^ 3) with hD1
  set W : Fin k → Z2 L → ℝ := fun l c =>
    if l = i then D1 i c else if l = j then D1 j c else G with hW
  have hWb : ∀ l, l ≠ 0 → ∀ c, ∑ x ∈ univ.filter (fun x : Z2 L => (zdist2 L (x - c) : ℝ) < ρ),
      ‖piece L s t (a l) c x (f l)‖ ≤ W l c := by
    intro l _ c
    by_cases hli : l = i
    · subst hli
      simp only [hW, ite_eq_left rfl, hi, hD1]
      exact win_one hL hs hst ht hρ1 (a l) c
    · by_cases hlj : l = j
      · subst hlj
        simp only [hW, ite_eq_right hli, hj, hD1]
        exact win_one hL hs hst ht hρ1 (a l) c
      · simp only [hW, ite_eq_right hli, ite_eq_right hlj, hG]
        exact win_all hL hs hst ht hρ1 (a l) c (f l)
  have h := norm_V_le hL hs hst ht a f hf0 (by linarith) hM hδ hAM hdec W hWb
  refine h.trans (add_le_add ?_
    (mul_le_mul_of_nonneg_left (far_V_le (by omega) hL hs hst ht) hδ))
  refine mul_le_mul_of_nonneg_left ?_ hM
  -- the near part
  have hprod : ∀ c, ∏ l ∈ univ.erase 0, W l c = D1 i c * (D1 j c * G ^ (k - 3)) := fun c =>
    (prod_erase_ite_two i j hi0 hj0 hij (D1 i c) (D1 j c) G).2
  have hGle : G ≤ 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by
    have : G = 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t) := by rw [hG, hρ]; ring
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left hlse (by positivity : (0 : ℝ) ≤ 27 * K ^ 2)
    calc 27 * K ^ 2 * (ellT L s ^ 2 * eT L s t)
        ≤ 27 * K ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t) := h2
      _ = 54 * cProp5 * (1 + Real.log L) * K ^ 2 * rhoR L s t := by ring
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hr5 : Real.sqrt 5 ≤ 3 := by
    rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsl : Real.sqrt (1 + Real.log L) ≤ 1 + Real.log L := by
    rw [Real.sqrt_le_left (by linarith)]
    exact le_self_pow₀ hlam (by norm_num)
  have hnum := num_iv hk3 hlam hK hR1 hPl0 (Pl_le L) hG0 hGle (Real.sqrt_nonneg 5) hr5
    (Real.sqrt_nonneg _) hsl hS
  calc ∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * ∏ l ∈ univ.erase 0, W l c
      = (∑ c : Z2 L, ‖xiMat L 1 s t (a 0) c‖ * (D1 i c * D1 j c)) * G ^ (k - 3) := by
        rw [sum_mul]
        refine sum_congr rfl fun c _ => ?_
        rw [hprod c]; ring
    _ ≤ _ := hnum

/-- For `|E| ≤ 2` and `σ ≠ σ'`, `m(σ) m(σ') = |m|² = 1`. -/
private theorem mSig_alt {E : ℝ} (hE : |E| ≤ 2) {σ σ' : Bool} (h : σ ≠ σ') :
    KLoop.mSig E σ * KLoop.mSig E σ' = 1 := by
  have hn := Gauss.norm_spectralM hE
  cases σ <;> cases σ'
  · exact absurd rfl h
  · simp only [KLoop.mSig, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.conj_mul', hn]; simp
  · simp only [KLoop.mSig, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.mul_conj', hn]; simp
  · exact absurd rfl h

end Terms

/-! ## The theorem -/

section Theorem

/-- **D2**: Case 4 `symmetric_tensor`, alternating `σ`, explicit form,
`cCase4 k = (4 · 10⁶ (cProp5 + 8·10¹⁴ + 720))^k`. -/
theorem ugenCase4AltExplicit : UgenCase4AltExplicit cCase4 := by
  intro k _ hk L _ hL E hE s t hs hst ht σ hσ K M δA hK hM hδ A hAM hdec hsz hsym a
  classical
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1t : 0 < 1 - t := by linarith
  have hlam := case4_lam_ge_one L
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hY1 : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    nlinarith
  have hlL : 1 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hlam hL1
  have hX := case4X_ge_one
  set N0 := (1 + Real.log L) ^ (k + 1) * K ^ (2 * k) * rhoR L s t ^ k with hN0
  set Er := ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k with hEr
  set Bnd := M * (case4X ^ k * N0) + δA * (case4X ^ k * Er) with hBnd
  have hN00 : 0 ≤ N0 := by
    have : 0 ≤ 1 + Real.log L := by linarith
    have : 0 ≤ rhoR L s t := by linarith
    positivity
  have hEr0 : 0 ≤ Er := by
    have : 0 ≤ (1 + Real.log L) * (L : ℝ) ^ 2 := by linarith
    have : 0 ≤ (1 - s) / (1 - t) := by linarith
    positivity
  have hBnd0 : 0 ≤ Bnd := by
    have : 0 ≤ case4X ^ k := pow_nonneg (by linarith) k
    positivity
  -- every edge weight is `1`
  have hedge : ∀ i : Fin k, KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) = 1 :=
    fun i => mSig_alt hE (hσ i)
  have hU : Ugen L E σ s t A a = ∑ g : Fin k → Fin 2,
      ∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b := by
    unfold Ugen
    simp only [hedge]
    have h1 : ∀ b : Fin k → Z2 L, (∏ i, ukerMat L 1 s t (a i) (b i)) * A b =
        ∑ g : Fin k → Fin 2, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b := by
      intro b
      rw [← sum_mul]
      congr 1
      calc ∏ i, ukerMat L 1 s t (a i) (b i)
          = ∏ i, ∑ p : Fin 2, dpiece L s t p (a i) (b i) := by
            refine prod_congr rfl fun i _ => ?_
            rw [Fin.sum_univ_two, KernelExpand_ukerMat_apply]
            change xiMat L 1 s t (a i) (b i) + (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i) =
              (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i) + xiMat L 1 s t (a i) (b i)
            ring
        _ = ∑ g : Fin k → Fin 2, ∏ l, dpiece L s t (g l) (a l) (b l) :=
            Case4_prod_sum_pieces _
    rw [sum_congr rfl fun b _ => h1 b, sum_comm]
  -- the terms with a `δ`
  have hTg : ∀ g : Fin k → Fin 2, g ≠ (fun _ => 1) →
      ‖∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ ≤ Bnd := by
    intro g hg
    obtain ⟨j, hj⟩ : ∃ j, g j = 0 := by
      by_contra hcon
      push Not at hcon
      apply hg
      funext l
      have h01 : ∀ p : Fin 2, p ≠ 0 → p = 1 := by decide
      exact h01 (g l) (hcon l)
    refine (norm_T_le hL hs hst ht hK a g j hj hM hδ hAM hdec).trans ?_
    have h1 := num_T hk hlam hK hR1
    have h2 := num_far_T (k := k) (by linarith : (0 : ℝ) ≤ (1 - s) / (1 - t)) hlL
    rw [hBnd, hN0, hEr, ← mul_pow]
    rw [← mul_pow] at h2
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hM) (mul_le_mul_of_nonneg_left h2 hδ)
  -- the all-`Ξ` term, piece by piece
  have hV : ∀ f : Fin k → Fin 3, ‖Vterm L s t a A f‖ ≤ Bnd := by
    intro f
    by_cases hf0 : f 0 = 0
    swap
    · rw [V_eq_zero_of_f0 s t a A f hf0, norm_zero]; exact hBnd0
    have h012 : ∀ p : Fin 3, p ≠ 1 → p ≠ 2 → p = 0 := by decide
    by_cases h2 : ∃ i, f i = 2
    · obtain ⟨i, hi⟩ := h2
      have hi0 : i ≠ 0 := by
        rintro rfl; rw [hf0] at hi; exact absurd hi (by decide)
      exact bound_iii hk hL hs hst ht hK a f hf0 i hi0 hi hM hδ hAM hdec
    push Not at h2
    by_cases h11 : ∃ i j, i ≠ j ∧ f i = 1 ∧ f j = 1
    · obtain ⟨i, j, hij, hi, hj⟩ := h11
      have hi0 : i ≠ 0 := by rintro rfl; rw [hf0] at hi; exact absurd hi (by decide)
      have hj0 : j ≠ 0 := by rintro rfl; rw [hf0] at hj; exact absurd hj (by decide)
      exact bound_iv hL hs hst ht hK a f hf0 i j hi0 hj0 hij hi hj hM hδ hAM hdec
    push Not at h11
    by_cases h1 : ∃ i, f i = 1
    · obtain ⟨i, hi⟩ := h1
      have hrest : ∀ l, l ≠ i → f l = 0 := by
        intro l hl
        refine h012 (f l) (fun hl1 => ?_) (h2 l)
        exact h11 l i hl hl1 hi
      rw [V_eq_zero_of_one s t a A hsym f i hi hrest, norm_zero]; exact hBnd0
    · push Not at h1
      rw [V_eq_zero_of_all0 s t a A hsz f (fun l => h012 (f l) (h1 l) (h2 l)), norm_zero]
      exact hBnd0
  have hT1 : ‖∑ b : Fin k → Z2 L,
      (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (a l) (b l)) * A b‖ ≤ 3 ^ k * Bnd := by
    have hexp : ∑ b : Fin k → Z2 L,
        (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (a l) (b l)) * A b =
        ∑ f : Fin k → Fin 3, Vterm L s t a A f := by
      have h1 : ∀ b : Fin k → Z2 L,
          (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (a l) (b l)) * A b =
          ∑ f : Fin k → Fin 3, (∏ l, piece L s t (a l) (b 0) (b l) (f l)) * A b := by
        intro b
        rw [← sum_mul]
        congr 1
        calc ∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (a l) (b l)
            = ∏ l, ∑ p : Fin 3, piece L s t (a l) (b 0) (b l) p :=
              prod_congr rfl fun l _ => (piece_sum s t (a l) (b 0) (b l)).symm
          _ = ∑ f : Fin k → Fin 3, ∏ l, piece L s t (a l) (b 0) (b l) (f l) :=
              Case4_prod_sum_pieces _
      rw [sum_congr rfl fun b _ => h1 b, sum_comm]
      rfl
    rw [hexp]
    calc ‖∑ f : Fin k → Fin 3, Vterm L s t a A f‖
        ≤ ∑ f : Fin k → Fin 3, ‖Vterm L s t a A f‖ := norm_sum_le _ _
      _ ≤ ∑ _f : Fin k → Fin 3, Bnd := sum_le_sum fun f _ => hV f
      _ = 3 ^ k * Bnd := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  -- assembling
  have hcard : ((univ.erase (fun _ => (1 : Fin 2)) : Finset (Fin k → Fin 2)).card : ℝ) ≤
      2 ^ k := by
    have h := card_erase_le (s := (univ : Finset (Fin k → Fin 2))) (a := fun _ => 1)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact_mod_cast h
  have h342 := three_two_four hk
  rw [hU]
  calc ‖∑ g : Fin k → Fin 2, ∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖
      ≤ ∑ g : Fin k → Fin 2,
          ‖∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ := norm_sum_le _ _
    _ = ‖∑ b : Fin k → Z2 L,
          (∏ l, dpiece L s t ((fun _ => (1 : Fin 2)) l) (a l) (b l)) * A b‖ +
        ∑ g ∈ univ.erase (fun _ => (1 : Fin 2)),
          ‖∑ b : Fin k → Z2 L, (∏ l, dpiece L s t (g l) (a l) (b l)) * A b‖ :=
        (add_sum_erase _ _ (mem_univ _)).symm
    _ ≤ 3 ^ k * Bnd + ∑ _g ∈ univ.erase (fun _ => (1 : Fin 2)), Bnd :=
        add_le_add hT1 (sum_le_sum fun g hg => hTg g (ne_of_mem_erase hg))
    _ = 3 ^ k * Bnd +
          ((univ.erase (fun _ => (1 : Fin 2)) : Finset (Fin k → Fin 2)).card : ℝ) * Bnd := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 3 ^ k * Bnd + 2 ^ k * Bnd := by
        have := mul_le_mul_of_nonneg_right hcard hBnd0
        linarith
    _ ≤ 4 ^ k * Bnd := by
        have := mul_le_mul_of_nonneg_right h342 hBnd0
        linarith
    _ = cCase4 k * (1 + Real.log L) ^ (k + 1) * K ^ (2 * k) * rhoR L s t ^ k * M +
          cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k * δA := by
        rw [cCase4_eq, hBnd, hN0, hEr]; ring

end Theorem

end RBM.Evol

end
