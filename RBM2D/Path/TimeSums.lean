/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Scales

/-!
# The time sums on the grid

The definitions `gridU` (the grid times), `QVTimeSum` (left Riemann sums of the
quadratic-variation terms) and `DriftTimeSumD` (left Riemann sums of the drift terms).

Result (notation `x_u = 1 - u`, `μ = Im m^{(E)}`, `r = η_s/η_v = x_s/x_v`, `Δ = (v - s)/K`,
`ρ_u = ℓ_u/ℓ_s`, `Θ = Θ₀ r_u⁴`): `driftTimeSumD : DriftTimeSumD` bounds the sum of the three
drift terms.

Method: the left Riemann sum of `Δ x_u^{-(p+1)}` on the grid is at most
`(x_v^{-p} - x_s^{-p})/p` for `p ≥ 1` (Bernoulli, `one_add_mul_self_le_rpow_one_add`), and every
summand is bounded by a constant times `x_u^{-(p+1)}` through `ellT_mono_ratio`
(`ρ_u² ≤ r_u`), `scaleM_anti_ratio` (`M_v ≤ M_u`) and `etaT_div_etaT`.
-/

noncomputable section

namespace RBM.Path

open RBM RBM.Gauss

/-- The grid time `u_j = s + j (v - s)/K` from `s` to `v`. -/
def gridU (s v : ℝ) (K j : ℕ) : ℝ := s + j * ((v - s) / K)

/-- **QV time sums**, with `J_j ≤ Θ₀ (η_s/η_{u_j})⁴`
and `r = η_s/η_v`: left Riemann sums against `∫_s^v`. -/
def QVTimeSum : Prop :=
  ∀ (L W : ℕ) (E s v Θ₀ : ℝ) (K : ℕ), 1 ≤ L → 1 ≤ W → |E| < 2 → 0 ≤ s → s ≤ v → v < 1 →
    0 < K → 0 ≤ Θ₀ →
    ∑ j ∈ Finset.range K, (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 4 *
        ((etaT E (gridU s v K j))⁻¹ * (ellT L (gridU s v K j) / ellT L s) ^ 10 +
          (etaT E (gridU s v K j))⁻¹ * (ellT L (gridU s v K j) / ellT L s) ^ 3 *
            (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
            (Θ₀ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ * (Θ₀ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 3))
      ≤ ((spectralM E).im)⁻¹ *
        ((etaT E s / etaT E v) ^ 4 * (etaT E s / etaT E v - 1) +
          Θ₀ ^ 2 * (etaT E s / etaT E v) ^ ((19 : ℝ) / 2) *
            (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / (11 / 2) +
          Θ₀ ^ 3 * (etaT E s / etaT E v) ^ 12 * (scaleM L W E v)⁻¹ / 7)

/-- **Drift time sums**, with
`J_j ≤ Θ₀(η_s/η_{u_j})⁴`, `r = η_s/η_v`, `ρ_j = ℓ_{u_j}/ℓ_s`.  The `ρ⁶` term integrates to
`r³ − r² ≤ r³`. -/
def DriftTimeSumD : Prop :=
  ∀ (L W : ℕ) (E s v Θ₀ : ℝ) (K : ℕ), 1 ≤ L → 1 ≤ W → |E| < 2 → 0 ≤ s → s ≤ v → v < 1 →
    0 < K → 0 ≤ Θ₀ →
    ∑ j ∈ Finset.range K, (v - s) / K *
      ((etaT E (gridU s v K j) / etaT E v) ^ 2 * (etaT E (gridU s v K j))⁻¹ *
        ((scaleM L W E (gridU s v K j))⁻¹ * (Θ₀ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 2 *
            (scaleM L W E (gridU s v K j))⁻¹ ^ ((1 : ℝ) / 2) *
            (Θ₀ * (etaT E s / etaT E (gridU s v K j)) ^ 4) ^ 2 +
          (ellT L (gridU s v K j) / ellT L s) ^ 6))
      ≤ ((spectralM E).im)⁻¹ *
        (Θ₀ ^ 2 * (etaT E s / etaT E v) ^ 8 * (scaleM L W E v)⁻¹ / 6 +
          Θ₀ ^ 2 * (etaT E s / etaT E v) ^ 9 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7 +
          (etaT E s / etaT E v) ^ 3)

/-! ## 1. Grid facts -/

private theorem gridU_zero (s v : ℝ) (K : ℕ) : gridU s v K 0 = s := by
  simp [gridU]

private theorem gridU_last {K : ℕ} (hK : 0 < K) (s v : ℝ) : gridU s v K K = v := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold gridU
  field_simp
  ring

private theorem gridU_succ (s v : ℝ) (K j : ℕ) :
    gridU s v K (j + 1) = gridU s v K j + (v - s) / K := by
  unfold gridU; push_cast; ring

private theorem gridU_bounds {s v : ℝ} {K j : ℕ} (hsv : s ≤ v) (hK : 0 < K) (hj : j ≤ K) :
    s ≤ gridU s v K j ∧ gridU s v K j ≤ v := by
  have hΔ : 0 ≤ (v - s) / K := div_nonneg (by linarith) (Nat.cast_nonneg K)
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj
  have h1 : (j : ℝ) * ((v - s) / K) ≤ K * ((v - s) / K) := mul_le_mul_of_nonneg_right hjK hΔ
  have h2 : (K : ℝ) * ((v - s) / K) = v - s := by
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp
  have h3 : 0 ≤ (j : ℝ) * ((v - s) / K) := mul_nonneg (Nat.cast_nonneg j) hΔ
  unfold gridU
  constructor <;> linarith

/-! ## 2. The Riemann step and sums -/

/-- One Riemann step: `(a - b) a^{-(p+1)} ≤ (b^{-p} - a^{-p})/p` for `0 < b ≤ a`, `1 ≤ p`
(Bernoulli for the real exponent `p`). -/
private theorem step_rpow {a b p : ℝ} (hb : 0 < b) (hba : b ≤ a) (hp : 1 ≤ p) :
    (a - b) * a ^ (-(p + 1)) ≤ (b ^ (-p) - a ^ (-p)) / p := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hp0 : 0 < p := by linarith
  rw [le_div_iff₀ hp0]
  have h1 : b ^ (-p) = (a / b) ^ p * a ^ (-p) := by
    rw [Real.div_rpow ha.le hb.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
    have : 0 < a ^ p := Real.rpow_pos_of_pos ha p
    field_simp
  have h2 : a ^ (-(p + 1)) = a ^ (-p) / a := by
    rw [neg_add, Real.rpow_add ha, Real.rpow_neg_one]; field_simp
  have hy : 1 ≤ a / b := (one_le_div hb).2 hba
  have hbern : 1 + p * (a / b - 1) ≤ (a / b) ^ p := by
    have := one_add_mul_self_le_rpow_one_add (s := a / b - 1) (by linarith) hp
    simpa using this
  have hapos : 0 < a ^ (-p) := Real.rpow_pos_of_pos ha _
  have h3 : (a - b) / a ≤ a / b - 1 := by
    have : a / b - 1 = (a - b) / b := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left (by linarith) hb hba
  have h4 : (a - b) * a ^ (-(p + 1)) * p = a ^ (-p) * (p * ((a - b) / a)) := by
    rw [h2]; ring
  rw [h4, h1]
  calc a ^ (-p) * (p * ((a - b) / a)) ≤ a ^ (-p) * (p * (a / b - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hapos.le
        exact mul_le_mul_of_nonneg_left h3 hp0.le
    _ ≤ a ^ (-p) * ((a / b) ^ p - 1) := by
        apply mul_le_mul_of_nonneg_left _ hapos.le
        linarith
    _ = (a / b) ^ p * a ^ (-p) - a ^ (-p) := by ring

/-- The telescoped left Riemann sum of `Δ x_u^{-(p+1)}`, `x_u = 1 - u_j`. -/
private theorem sum_step_rpow {s v : ℝ} {K : ℕ} {p : ℝ} (hsv : s ≤ v) (hv : v < 1) (hK : 0 < K)
    (hp : 1 ≤ p) :
    ∑ j ∈ Finset.range K, (v - s) / K * (1 - gridU s v K j) ^ (-(p + 1)) ≤
      ((1 - v) ^ (-p) - (1 - s) ^ (-p)) / p := by
  have hp0 : 0 < p := by linarith
  have hΔ : 0 ≤ (v - s) / K := div_nonneg (by linarith) (Nat.cast_nonneg K)
  have hterm : ∀ j ∈ Finset.range K,
      (v - s) / K * (1 - gridU s v K j) ^ (-(p + 1)) ≤
        ((1 - gridU s v K (j + 1)) ^ (-p) - (1 - gridU s v K j) ^ (-p)) / p := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.1 hj
    have hb := gridU_bounds hsv hK hjK
    have hsucc := gridU_succ s v K j
    have hb0 : 0 < 1 - gridU s v K (j + 1) := by linarith [hb.2]
    have hba : 1 - gridU s v K (j + 1) ≤ 1 - gridU s v K j := by linarith
    have := step_rpow hb0 hba hp
    have heq : (v - s) / K = (1 - gridU s v K j) - (1 - gridU s v K (j + 1)) := by
      rw [hsucc]; ring
    rw [heq]
    exact this
  calc ∑ j ∈ Finset.range K, (v - s) / K * (1 - gridU s v K j) ^ (-(p + 1))
      ≤ ∑ j ∈ Finset.range K,
          ((1 - gridU s v K (j + 1)) ^ (-p) - (1 - gridU s v K j) ^ (-p)) / p :=
        Finset.sum_le_sum hterm
    _ = ((1 - gridU s v K K) ^ (-p) - (1 - gridU s v K 0) ^ (-p)) / p := by
        rw [← Finset.sum_div]
        congr 1
        exact Finset.sum_range_sub (fun j => (1 - gridU s v K j) ^ (-p)) K
    _ = ((1 - v) ^ (-p) - (1 - s) ^ (-p)) / p := by
        rw [gridU_last hK, gridU_zero]

private theorem rpow_neg_natCast {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

/-- Riemann sum with a natural exponent `n + 1`, `n ≥ 1`. -/
private theorem sum_nat {s v : ℝ} {K : ℕ} (n : ℕ) (hn : 1 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (T : ℕ → ℝ) (hsv : s ≤ v) (hv : v < 1) (hK : 0 < K)
    (hT : ∀ j ∈ Finset.range K, T j ≤ C * ((1 - gridU s v K j) ^ (n + 1))⁻¹) :
    ∑ j ∈ Finset.range K, (v - s) / K * T j ≤
      C * ((((1 - v) ^ n)⁻¹ - ((1 - s) ^ n)⁻¹) / n) := by
  have hΔ : 0 ≤ (v - s) / K := div_nonneg (by linarith) (Nat.cast_nonneg K)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxv : 0 < 1 - v := by linarith
  have hxs : 0 < 1 - s := by linarith
  have hpos : ∀ j ∈ Finset.range K, 0 < 1 - gridU s v K j := fun j hj => by
    have := gridU_bounds hsv hK (Finset.mem_range.1 hj).le
    linarith [this.2]
  calc ∑ j ∈ Finset.range K, (v - s) / K * T j
      ≤ ∑ j ∈ Finset.range K, (v - s) / K * (C * ((1 - gridU s v K j) ^ (n + 1))⁻¹) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hT j hj) hΔ
    _ = C * ∑ j ∈ Finset.range K, (v - s) / K * (1 - gridU s v K j) ^ (-((n : ℝ) + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have h := rpow_neg_natCast (hpos j hj) (n + 1)
        push_cast at h
        rw [h]; ring
    _ ≤ C * (((1 - v) ^ (-(n : ℝ)) - (1 - s) ^ (-(n : ℝ))) / n) :=
        mul_le_mul_of_nonneg_left (sum_step_rpow hsv hv hK hn') hC
    _ = C * ((((1 - v) ^ n)⁻¹ - ((1 - s) ^ n)⁻¹) / n) := by
        rw [rpow_neg_natCast hxv, rpow_neg_natCast hxs]

/-! ## 3. Pointwise algebra on free variables -/

private theorem alg3 {x xs xv μ Θ₀ B B' : ℝ} (hx : 0 < x) (hxv : 0 < xv) (hμ : 0 < μ)
    (hBB : B' ≤ B) :
    (x / xv) ^ 2 * (x * μ)⁻¹ * (B' * (Θ₀ * (xs / x) ^ 4) ^ 2) ≤
      μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ * (x ^ 7)⁻¹ := by
  calc (x / xv) ^ 2 * (x * μ)⁻¹ * (B' * (Θ₀ * (xs / x) ^ 4) ^ 2)
      ≤ (x / xv) ^ 2 * (x * μ)⁻¹ * (B * (Θ₀ * (xs / x) ^ 4) ^ 2) := by gcongr
    _ = μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ * (x ^ 7)⁻¹ := by
        field_simp

private theorem alg5 {x xs xv μ Θ₀ A A' ρ : ℝ} (hx : 0 < x) (hxv : 0 < xv) (hμ : 0 < μ)
    (hA' : 0 ≤ A') (hAA : A' ≤ A) (hρ : ρ ^ 2 ≤ xs / x) :
    (x / xv) ^ 2 * (x * μ)⁻¹ * (ρ ^ 2 * A' * (Θ₀ * (xs / x) ^ 4) ^ 2) ≤
      μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ * (x ^ 8)⁻¹ := by
  have hs0 : 0 ≤ xs / x := le_trans (sq_nonneg ρ) hρ
  calc (x / xv) ^ 2 * (x * μ)⁻¹ * (ρ ^ 2 * A' * (Θ₀ * (xs / x) ^ 4) ^ 2)
      ≤ (x / xv) ^ 2 * (x * μ)⁻¹ * ((xs / x) * A * (Θ₀ * (xs / x) ^ 4) ^ 2) := by gcongr
    _ = μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ * (x ^ 8)⁻¹ := by
        field_simp

private theorem alg4 {x xs xv μ ρ : ℝ} (hx : 0 < x) (hxv : 0 < xv) (hμ : 0 < μ)
    (hρ : ρ ^ 2 ≤ xs / x) :
    (x / xv) ^ 2 * (x * μ)⁻¹ * ρ ^ 6 ≤ μ⁻¹ * xs ^ 3 * (xv ^ 2)⁻¹ * (x ^ 2)⁻¹ := by
  have h6 : ρ ^ 6 ≤ (xs / x) ^ 3 := by
    calc ρ ^ 6 = (ρ ^ 2) ^ 3 := by ring
      _ ≤ (xs / x) ^ 3 := pow_le_pow_left₀ (sq_nonneg ρ) hρ 3
  calc (x / xv) ^ 2 * (x * μ)⁻¹ * ρ ^ 6 ≤ (x / xv) ^ 2 * (x * μ)⁻¹ * (xs / x) ^ 3 := by
        gcongr
    _ = μ⁻¹ * xs ^ 3 * (xv ^ 2)⁻¹ * (x ^ 2)⁻¹ := by
        field_simp

/-! ## 4. Facts at a grid point -/

private theorem rho_nonneg {L : ℕ} {s u : ℝ} (hL : 1 ≤ L) (hu : u < 1) (hs : s < 1) :
    0 ≤ ellT L u / ellT L s :=
  div_nonneg (ellT_pos_le hL hu).1.le (ellT_pos_le hL hs).1.le

/-- Square-root form: `ρ_u ≤ √x_s / √x_u`. -/
private theorem rho_le_sqrt {L : ℕ} {s u : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hu : u < 1) : ellT L u / ellT L s ≤ Real.sqrt (1 - s) / Real.sqrt (1 - u) := by
  have h := (ellT_mono_ratio hL hs hsu hu).2
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by linarith)] at h
  exact h

/-- `ρ_u² ≤ x_s / x_u`. -/
private theorem rho_sq_le {L : ℕ} {s u : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hu : u < 1) : (ellT L u / ellT L s) ^ 2 ≤ (1 - s) / (1 - u) := by
  have h := rho_le_sqrt hL hs hsu hu
  have h0 := rho_nonneg hL hu (lt_of_le_of_lt hsu hu)
  calc (ellT L u / ellT L s) ^ 2 ≤ (Real.sqrt (1 - s) / Real.sqrt (1 - u)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = (1 - s) / (1 - u) := by
        rw [div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]

/-- `M_u⁻¹ ≤ M_v⁻¹` and the same for the power `1/2`. -/
private theorem scaleM_inv_facts {L W : ℕ} {E u v : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : |E| < 2) (huv : u ≤ v) (hv : v < 1) :
    0 ≤ (scaleM L W E u)⁻¹ ∧ (scaleM L W E u)⁻¹ ≤ (scaleM L W E v)⁻¹ ∧
      0 ≤ (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) ∧
      (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) ≤ (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) := by
  have hu : u < 1 := lt_of_le_of_lt huv hv
  have hMu := scaleM_pos hL hW hE hu
  have hMv := scaleM_pos hL hW hE hv
  have hle : (scaleM L W E u)⁻¹ ≤ (scaleM L W E v)⁻¹ :=
    inv_anti₀ hMv (scaleM_anti_ratio hL hE huv hv).1
  exact ⟨inv_nonneg.2 hMu.le, hle, Real.rpow_nonneg (inv_nonneg.2 hMu.le) _,
    Real.rpow_le_rpow (inv_nonneg.2 hMu.le) hle (by norm_num)⟩

/-! ## 5. The three pointwise drift bounds -/

/-- The drift `LK×LK` term: `≤ μ⁻¹ Θ₀² M_v⁻¹ x_s⁸ x_v⁻² x_u⁻⁷`. -/
private theorem dr_row3 {L W : ℕ} {E s u v Θ₀ : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (huv : u ≤ v) (hsu : s ≤ u) (hv : v < 1) :
    (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ *
        ((scaleM L W E u)⁻¹ * (Θ₀ * (etaT E s / etaT E u) ^ 4) ^ 2) ≤
      ((spectralM E).im)⁻¹ * Θ₀ ^ 2 * (scaleM L W E v)⁻¹ * (1 - s) ^ 8 * ((1 - v) ^ 2)⁻¹ *
        ((1 - u) ^ 7)⁻¹ := by
  have hu : u < 1 := lt_of_le_of_lt huv hv
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  obtain ⟨-, hBB, -, -⟩ := scaleM_inv_facts hL hW hE huv hv
  rw [etaT_div_etaT (s := u) (u := v) hE hu hv, etaT_div_etaT hE hs1 hu]
  have e : etaT E u = (1 - u) * (spectralM E).im := rfl
  rw [e]
  exact alg3 (by linarith) (by linarith) (spectralM_im_pos hE) hBB

/-- The far drift term: `≤ μ⁻¹ Θ₀² M_v^{-1/2} x_s⁹ x_v⁻² x_u⁻⁸`. -/
private theorem dr_row5 {L W : ℕ} {E s u v Θ₀ : ℝ} (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : |E| < 2)
    (hs : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv : v < 1) :
    (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ *
        ((ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
          (Θ₀ * (etaT E s / etaT E u) ^ 4) ^ 2) ≤
      ((spectralM E).im)⁻¹ * Θ₀ ^ 2 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) * (1 - s) ^ 9 *
        ((1 - v) ^ 2)⁻¹ * ((1 - u) ^ 8)⁻¹ := by
  have hu : u < 1 := lt_of_le_of_lt huv hv
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  obtain ⟨-, -, hA0, hAA⟩ := scaleM_inv_facts hL hW hE huv hv
  rw [etaT_div_etaT (s := u) (u := v) hE hu hv, etaT_div_etaT hE hs1 hu]
  have e : etaT E u = (1 - u) * (spectralM E).im := rfl
  rw [e]
  exact alg5 (by linarith) (by linarith) (spectralM_im_pos hE) hA0 hAA
    (rho_sq_le hL hs hsu hu)

/-- The near drift term: `≤ μ⁻¹ x_s³ x_v⁻² x_u⁻²`. -/
private theorem dr_row4 {L : ℕ} {E s u v : ℝ} (hL : 1 ≤ L) (hE : |E| < 2) (hs : 0 ≤ s)
    (hsu : s ≤ u) (huv : u ≤ v) (hv : v < 1) :
    (etaT E u / etaT E v) ^ 2 * (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 6 ≤
      ((spectralM E).im)⁻¹ * (1 - s) ^ 3 * ((1 - v) ^ 2)⁻¹ * ((1 - u) ^ 2)⁻¹ := by
  have hu : u < 1 := lt_of_le_of_lt huv hv
  rw [etaT_div_etaT (s := u) (u := v) hE hu hv]
  have e : etaT E u = (1 - u) * (spectralM E).im := rfl
  rw [e]
  exact alg4 (by linarith) (by linarith) (spectralM_im_pos hE) (rho_sq_le hL hs hsu hu)

/-! ## 6. Closing the integrals -/

private theorem sum_split3 (Δ : ℝ) (K : ℕ) (P b c d : ℕ → ℝ) :
    ∑ j ∈ Finset.range K, Δ * (P j * (b j + c j + d j)) =
      ∑ j ∈ Finset.range K, Δ * (P j * b j) + ∑ j ∈ Finset.range K, Δ * (P j * c j) +
        ∑ j ∈ Finset.range K, Δ * (P j * d j) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem fin3 {xs xv μ Θ₀ B : ℝ} (hμ : 0 < μ) (hxs : 0 < xs) (hxv : 0 < xv)
    (hB : 0 ≤ B) :
    μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ * (((xv ^ 6)⁻¹ - (xs ^ 6)⁻¹) / ((6 : ℕ) : ℝ)) ≤
      μ⁻¹ * (Θ₀ ^ 2 * (xs / xv) ^ 8 * B / 6) := by
  have hC : 0 ≤ μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ := by positivity
  push_cast
  calc μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ * (((xv ^ 6)⁻¹ - (xs ^ 6)⁻¹) / 6)
      ≤ μ⁻¹ * Θ₀ ^ 2 * B * xs ^ 8 * (xv ^ 2)⁻¹ * ((xv ^ 6)⁻¹ / 6) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have : 0 ≤ (xs ^ 6)⁻¹ := by positivity
        gcongr
        linarith
    _ = μ⁻¹ * (Θ₀ ^ 2 * (xs / xv) ^ 8 * B / 6) := by
        field_simp

private theorem fin5 {xs xv μ Θ₀ A : ℝ} (hμ : 0 < μ) (hxs : 0 < xs) (hxv : 0 < xv)
    (hA : 0 ≤ A) :
    μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ * (((xv ^ 7)⁻¹ - (xs ^ 7)⁻¹) / ((7 : ℕ) : ℝ)) ≤
      μ⁻¹ * (Θ₀ ^ 2 * (xs / xv) ^ 9 * A / 7) := by
  have hC : 0 ≤ μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ := by positivity
  push_cast
  calc μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ * (((xv ^ 7)⁻¹ - (xs ^ 7)⁻¹) / 7)
      ≤ μ⁻¹ * Θ₀ ^ 2 * A * xs ^ 9 * (xv ^ 2)⁻¹ * ((xv ^ 7)⁻¹ / 7) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have : 0 ≤ (xs ^ 7)⁻¹ := by positivity
        gcongr
        linarith
    _ = μ⁻¹ * (Θ₀ ^ 2 * (xs / xv) ^ 9 * A / 7) := by
        field_simp

/-- `∫ x^{-2}` again: `μ⁻¹ x_s³ x_v⁻² (x_v⁻¹ - x_s⁻¹) = μ⁻¹ (r³ - r²) ≤ μ⁻¹ r³`. -/
private theorem fin4 {xs xv μ : ℝ} (hμ : 0 < μ) (hxs : 0 < xs) (hxv : 0 < xv) :
    μ⁻¹ * xs ^ 3 * (xv ^ 2)⁻¹ * (((xv ^ 1)⁻¹ - (xs ^ 1)⁻¹) / ((1 : ℕ) : ℝ)) ≤
      μ⁻¹ * (xs / xv) ^ 3 := by
  have h : μ⁻¹ * xs ^ 3 * (xv ^ 2)⁻¹ * (((xv ^ 1)⁻¹ - (xs ^ 1)⁻¹) / ((1 : ℕ) : ℝ)) =
      μ⁻¹ * ((xs / xv) ^ 3 - (xs / xv) ^ 2) := by
    push_cast
    field_simp
  rw [h]
  have : 0 ≤ μ⁻¹ * (xs / xv) ^ 2 := by positivity
  nlinarith

/-! ## 7. The result -/

/-- **`driftTimeSumD`**: the drift time sums (the `LK×LK`, near and far terms) on the grid. -/
theorem driftTimeSumD : DriftTimeSumD := by
  intro L W E s v Θ₀ K hL hW hE hs hsv hv hK hΘ
  have hs1 : s < 1 := lt_of_le_of_lt hsv hv
  have hxs : 0 < 1 - s := by linarith
  have hxv : 0 < 1 - v := by linarith
  have hμ : 0 < (spectralM E).im := spectralM_im_pos hE
  have hMv : 0 < scaleM L W E v := scaleM_pos hL hW hE hv
  have hB : 0 ≤ (scaleM L W E v)⁻¹ := inv_nonneg.2 hMv.le
  have hA : 0 ≤ (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hB _
  have hjb : ∀ j ∈ Finset.range K, s ≤ gridU s v K j ∧ gridU s v K j ≤ v := fun j hj =>
    gridU_bounds hsv hK (Finset.mem_range.1 hj).le
  rw [etaT_div_etaT hE hs1 hv]
  refine (sum_split3 _ _ _ _ _ _).trans_le ?_
  refine le_trans (add_le_add (add_le_add
    (sum_nat (C := ((spectralM E).im)⁻¹ * Θ₀ ^ 2 * (scaleM L W E v)⁻¹ * (1 - s) ^ 8 *
        ((1 - v) ^ 2)⁻¹) 6 (by norm_num) (by positivity) _ hsv hv hK ?_)
    (sum_nat (C := ((spectralM E).im)⁻¹ * Θ₀ ^ 2 * (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) *
        (1 - s) ^ 9 * ((1 - v) ^ 2)⁻¹) 7 (by norm_num) (by positivity) _ hsv hv hK ?_))
    (sum_nat (C := ((spectralM E).im)⁻¹ * (1 - s) ^ 3 * ((1 - v) ^ 2)⁻¹) 1 le_rfl
      (by positivity) _ hsv hv hK ?_)) ?_
  · intro j hj
    exact dr_row3 hL hW hE (hjb j hj).2 (hjb j hj).1 hv
  · intro j hj
    exact dr_row5 hL hW hE hs (hjb j hj).1 (hjb j hj).2 hv
  · intro j hj
    exact dr_row4 hL hE hs (hjb j hj).1 (hjb j hj).2 hv
  · calc _ ≤ ((spectralM E).im)⁻¹ * (Θ₀ ^ 2 * ((1 - s) / (1 - v)) ^ 8 * (scaleM L W E v)⁻¹ / 6) +
          ((spectralM E).im)⁻¹ * (Θ₀ ^ 2 * ((1 - s) / (1 - v)) ^ 9 *
            (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) / 7) +
          ((spectralM E).im)⁻¹ * ((1 - s) / (1 - v)) ^ 3 :=
        add_le_add (add_le_add (fin3 hμ hxs hxv hB) (fin5 hμ hxs hxv hA)) (fin4 hμ hxs hxv)
      _ = _ := by ring

end RBM.Path
