/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.JakKernel
import RBM2D.Universality.OU
import RBM2D.Universality.OUHessian

/-!
# The `Jak` half of the reduction `JakUywRow`

Paper: arXiv:2503.07606, the display `(jaklsdufowe)` in the proof of `Thm: B_Univ`, with the two
`𝐇_t` claims of the resolvent estimates after `417`.  The main result `jakRow` says: for every
admissible size sequence `d`, `κ > 0`, `|E| ≤ 2 - κ` and `nf`, there are `C` and `τ₀ > 0` such
that for every `0 < τ_U ≤ τ₀` the statement `Jak` holds with `c' = 𝔠/36` (the paper writes
`𝔠/18`).  The hypotheses are `locSC` (the first hypothesis of the reduction, not used) and
`OUClaims` (`OUQUE` and `OUDiag` for all small `τ_U`).

Proof, per site `y` (no average over `y`, no moment bound, no Markov step):
* pure real arithmetic of the exponents (`η̃ = N^{-1+2τ}`, `C_b = N^δ`, `w' = N^{-1+𝔠/6}/2`,
  `θ = N^{-𝔠/36}`, `δ = τ/(nf+5)`): the factors `Q_y`, `A_y` off and on the bad block, the
  weights, the crude weight, the grid energies, and the three assembled bounds;
* the majorant integration, the union bound over the covering grids (each energy is one
  event of `OUDiag`, with the sites `x` inside the event), `gSel = Gsig` on Hermitian matrices,
  and `𝔠 ≤ 1/2` from admissibility;
* the pointwise bound on the good event with explicit constants (`jak_pointwise_good`);
* the bound at one size and one time: `f ≤ A₀ + c_B 1_B + C_r 1_T`, where `T` is the failure of
  one of at most `(3+nf)N` covering grids (`OUDiag`, `jakGridGood`) and `B` is the bad event of
  the block of `y` (`OUQUE` at `τ = 𝔠/3` through `measure_bad_le_of_queBadMat`, window
  `w = N^{-1+𝔠/6} ≤ N^{-1-𝔠/3} W^{2/3}`, threshold `θ² = N^{-(𝔠/3)/6}`);
* the eventual conditions on `n` and `jakRow`.

The carrier is `ouP L W` with `ouMat L W t`; `N = (W L)²`; the integrand is the `y`-term of `L₁` in
the `gSel` form of `Jak`; there is one bad block (`siteBlock y`); the sum over `(σ, τ)` does not
occur (`b₁`, `b₂` are fixed); the crude constant is `2`; the bound on `∃ x, ‖G_xx‖ > N^δ` per
energy is `OUDiag`; `OUQUE` holds uniformly in `t ∈ [0, t*]`, so `τ_U < 𝔠/3` is not needed; the
grid energies satisfy the strict inequality `|e| < 2 - κ/2` required by `OUDiag`; the
non-negativity of `Im m` for the integrability of the integrand is avoided (a non-integrable
integrand has integral `0`).  `τ₀ ≤ 1/4` is imposed so that `η̃ → 0` (`ev3` of `Jak_main`).  `Jak`
holds without using its slack `N^ε` (`N^ε ≥ 1`).
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## Exponent bookkeeping (pure real arithmetic) -/

private theorem Jak_rpow_mul {X : ℝ} (hX : 0 < X) (a b : ℝ) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add hX a b).symm

private theorem Jak_exists_dyadic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℕ, 2 ^ K * a ≤ b ∧ b < 2 ^ (K + 1) * a := by
  classical
  have hex : ∃ K : ℕ, b < 2 ^ (K + 1) * a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    nlinarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | k
  · simpa using hab
  · have hk : k < Nat.find hex := by omega
    have := Nat.find_min hex hk
    push Not at this
    exact this

/-- The `Q_y` factor: `Q̄ = 6(η̃/η)N^δ + 8K N^δ + (2^K η̃)⁻¹ ≤ (6 + 16/τ + 8/κ) N^{3τ+δ}`. -/
private theorem Jak_Qb_le {X τ δ κ η ηt : ℝ} {K : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η)
    (hK1 : 2 ^ K * ηt ≤ κ / 4) (hK2 : κ / 4 < 2 ^ (K + 1) * ηt) :
    6 * (ηt / η) * X ^ δ + 8 * K * X ^ δ + (2 ^ K * ηt)⁻¹ ≤
      (6 + 16 / τ + 8 / κ) * X ^ (3 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have h1 : ηt / η ≤ X ^ (3 * τ) := by
    calc ηt / η ≤ ηt / X ^ (-1 - τ) := div_le_div_of_nonneg_left hηt0.le (by positivity) hη
      _ = X ^ (3 * τ) := by rw [hηt, ← Real.rpow_sub hX0]; congr 1; ring
  have h2K : (2 : ℝ) ^ K ≤ X := by
    have hle : (2 : ℝ) ^ K * ηt ≤ 1 := by linarith
    have hinv : (2 : ℝ) ^ K ≤ ηt⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hηt0]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      linarith
    calc (2 : ℝ) ^ K ≤ ηt⁻¹ := hinv
      _ = X ^ (1 - 2 * τ) := by rw [hηt, ← Real.rpow_neg hX0.le]; congr 1; ring
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = X := Real.rpow_one X
  have hK : (K : ℝ) ≤ 2 * X ^ τ / τ := by
    have hlog : (K : ℝ) * Real.log 2 ≤ Real.log X := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2K
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [one_div, Real.log_inv] at h
      linarith
    have hlr := Real.log_le_rpow_div hX0.le hτ
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    have : (K : ℝ) * (1 / 2) ≤ X ^ τ / τ := by nlinarith
    rw [mul_div_assoc]; linarith
  have h3 : (2 ^ K * ηt)⁻¹ ≤ 8 / κ := by
    have : κ / 8 < 2 ^ K * ηt := by rw [pow_succ] at hK2; linarith
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    rw [show (8 / κ)⁻¹ = κ / 8 by field_simp]; exact this.le
  have hA : X ^ (τ + δ) ≤ X ^ (3 * τ + δ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hB : (1 : ℝ) ≤ X ^ (3 * τ + δ) := Real.one_le_rpow hX (by linarith)
  have hδX : 0 < X ^ δ := by positivity
  calc 6 * (ηt / η) * X ^ δ + 8 * K * X ^ δ + (2 ^ K * ηt)⁻¹
      ≤ 6 * X ^ (3 * τ) * X ^ δ + 8 * (2 * X ^ τ / τ) * X ^ δ + 8 / κ := by
        gcongr
    _ = 6 * X ^ (3 * τ + δ) + 16 / τ * X ^ (τ + δ) + 8 / κ := by
        rw [← Jak_rpow_mul hX0, ← Jak_rpow_mul hX0]; ring
    _ ≤ 6 * X ^ (3 * τ + δ) + 16 / τ * X ^ (3 * τ + δ) + 8 / κ * X ^ (3 * τ + δ) := by
        gcongr
        · exact le_mul_of_one_le_right (by positivity) hB
    _ = _ := by ring

/-- The window/bulk/outside parts of `A_y` off the bad event:
`α₁ ≤ (193 + 128/κ²) N^{2 - c/36 + 4τ + 2δ}`. -/
private theorem Jak_alpha1_le {X c τ δ κ η ηt w' θ : ℝ} {K' : ℕ} (hX : 1 ≤ X) (hc : 0 < c)
    (hc2 : c < 36) (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hθ : θ = X ^ (-(c / 36))) (hK2 : κ / 4 < 2 ^ (K' + 1) * w') :
    θ * (ηt / η ^ 2 * (X * X ^ δ)) +
        4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤
      (193 + 128 / κ ^ 2) * X ^ (2 - c / 36 + 4 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  set E₁ : ℝ := 2 - c / 36 + 4 * τ + 2 * δ with hE₁
  have hw0 : 0 < w' := by rw [hw']; positivity
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [Jak_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  have hwi : 4 / w' = 8 * X ^ (1 - c / 6) := by rw [hw']; field_simp; ring
  have hwi2 : 4 * ηt / w' ^ 2 = 16 * X ^ (1 + 2 * τ - c / 3) := by
    rw [hw', hηt]
    have : X ^ (1 + 2 * τ - c / 3) = X ^ (-1 + 2 * τ) * (X ^ (1 - c / 6) * X ^ (1 - c / 6)) := by
      rw [Jak_rpow_mul hX0, Jak_rpow_mul hX0]; congr 1; ring
    rw [this]; field_simp; ring
  have ht1 : θ * (ηt / η ^ 2 * (X * X ^ δ)) ≤ X ^ E₁ := by
    calc θ * (ηt / η ^ 2 * (X * X ^ δ)) ≤
          X ^ (-(c / 36)) * (X ^ (1 + 4 * τ) * (X ^ (1 : ℝ) * X ^ δ)) := by
          rw [hθ, Real.rpow_one]; gcongr
      _ = X ^ (-(c / 36) + (1 + 4 * τ + (1 + δ))) := by
          rw [Jak_rpow_mul hX0, Jak_rpow_mul hX0, Jak_rpow_mul hX0]
      _ ≤ X ^ E₁ := Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
  have ht2 : 4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (4 / w' + 4 * ηt / w' ^ 2)) ≤ 192 * X ^ E₁ := by
    rw [hwi, hwi2]
    have e1 : 4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (8 * X ^ (1 - c / 6) +
        16 * X ^ (1 + 2 * τ - c / 3))) =
        64 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 - c / 6)) +
          128 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 + 2 * τ - c / 3)) := by
      simp only [← Jak_rpow_mul hX0, Real.rpow_one, hηt]; ring
    rw [e1]
    have f1 : X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 - c / 6)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    have f2 : X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 + 2 * τ - c / 3)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    linarith
  have ht3 : ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤ 128 / κ ^ 2 * X ^ E₁ := by
    have hb : κ / 8 < 2 ^ K' * w' := by rw [pow_succ] at hK2; linarith
    have hb2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      rw [show (64 / κ ^ 2)⁻¹ = (κ / 8) ^ 2 by field_simp; norm_num]
      exact pow_le_pow_left₀ (by positivity) hb.le 2
    have hXE : X ≤ X ^ E₁ := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ E₁ := Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    calc ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤ 64 / κ ^ 2 * (2 * X ^ E₁) := by gcongr
      _ = 128 / κ ^ 2 * X ^ E₁ := by ring
  linarith

/-- The window part on the bad event: `α₂ = 4Nη̃N^δ · (η̃/η²) N N^δ ≤ 4 N^{2+6τ+2δ}`. -/
private theorem Jak_alpha2_le {X τ δ η ηt : ℝ} (hX : 1 ≤ X)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η) :
    4 * X * ηt * X ^ δ * (ηt / η ^ 2 * (X * X ^ δ)) ≤ 4 * X ^ (2 + 6 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [Jak_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  calc 4 * X * ηt * X ^ δ * (ηt / η ^ 2 * (X * X ^ δ))
      ≤ 4 * X * ηt * X ^ δ * (X ^ (1 + 4 * τ) * (X * X ^ δ)) := by gcongr
    _ = 4 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + ((1 + 4 * τ) + (1 + δ))) := by
        simp only [← Jak_rpow_mul hX0, Real.rpow_one, hηt]; ring
    _ = 4 * X ^ (2 + 6 * τ + 2 * δ) := by congr 2; ring

/-- **Assembly of the good and bad parts** (factors `Im m_t(w_j)`, `Q_y`, `A_y` off/on `B_y`, `L₁`):
`N^a N⁻¹ α₁ Q̄ + N^a N⁻¹ α₂ Q̄ · 5 N^{-c/18} ≤ ⅓ N^{1 - c/36 + (3|s|+16)τ}` once
`3 (C₁ + 20) C₂ ≤ N^{6τ}`; here `(|s|+3)δ ≤ τ` is the normalization of `δ`. -/
private theorem Jak_good_total_le {X c τ δ C₁ C₂ : ℝ} {sc m : ℕ} (hX : 1 ≤ X) (hc : 0 ≤ c)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hsc : sc ≤ m)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hslack : 3 * (C₁ + 20) * C₂ ≤ X ^ (6 * τ)) :
    X ^ ((3 * τ + δ) * (sc : ℝ)) *
          (X⁻¹ * ((C₁ * X ^ (2 - c / 36 + 4 * τ + 2 * δ)) * (C₂ * X ^ (3 * τ + δ)))) +
        X ^ ((3 * τ + δ) * (sc : ℝ)) *
          (X⁻¹ * ((4 * X ^ (2 + 6 * τ + 2 * δ)) * (C₂ * X ^ (3 * τ + δ)))) *
          (5 * X ^ (-(c / 18))) ≤
      1 / 3 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  set T : ℝ := 1 - c / 36 + (3 * (sc : ℝ) + 16) * τ with hT
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (3 * τ + δ) * (sc : ℝ)
  set b : ℝ := 3 * τ + δ
  set e : ℝ := 2 - c / 36 + 4 * τ + 2 * δ
  set f : ℝ := 2 + 6 * τ + 2 * δ
  set g : ℝ := -(c / 18)
  have r1 : X ^ (a + b + e - 1) = X ^ a * X ^ b * X ^ e / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + b) e, Real.rpow_add hX0 a b, Real.rpow_one]
  have r2 : X ^ (a + b + f + g - 1) = X ^ a * X ^ b * X ^ f * X ^ g / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + b + f) g, Real.rpow_add hX0 (a + b) f,
      Real.rpow_add hX0 a b, Real.rpow_one]
  have e1 : X ^ a * (X⁻¹ * ((C₁ * X ^ e) * (C₂ * X ^ b))) =
      C₁ * C₂ * X ^ (a + b + e - 1) := by
    rw [r1]
    generalize X ^ a = A
    generalize X ^ b = B
    generalize X ^ e = Ee
    field_simp
  have e2 : X ^ a * (X⁻¹ * ((4 * X ^ f) * (C₂ * X ^ b))) * (5 * X ^ g) =
      20 * C₂ * X ^ (a + b + f + g - 1) := by
    rw [r2]
    generalize X ^ a = A
    generalize X ^ b = B
    generalize X ^ f = F
    generalize X ^ g = G
    field_simp
    ring
  rw [e1, e2]
  have hsd : (sc + 3 : ℝ) * δ ≤ τ := le_trans (by gcongr) hmδ
  have f1 : X ^ (a + b + e - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, b, e, hT]
    nlinarith
  have f2 : X ^ (a + b + f + g - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, b, f, g, hT]
    nlinarith
  have hsplit : X ^ T = X ^ (T - 6 * τ) * X ^ (6 * τ) := by
    rw [Jak_rpow_mul hX0]; congr 1; ring
  have hpos : 0 ≤ X ^ (T - 6 * τ) := by positivity
  calc C₁ * C₂ * X ^ (a + b + e - 1) + 20 * C₂ * X ^ (a + b + f + g - 1)
      ≤ C₁ * C₂ * X ^ (T - 6 * τ) + 20 * C₂ * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 3 * (3 * (C₁ + 20) * C₂) * X ^ (T - 6 * τ) := by ring
    _ ≤ 1 / 3 * X ^ (6 * τ) * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 3 * X ^ T := by rw [hsplit]; ring

/-- **Assembly of the crude part** (on `Ξᶜ`): with `D ≥ (1+τ)(m+3) + 3`,
`2 N^{(1+τ)(|s|+3)} · (3+m) N · 2N · N^{-D} ≤ 4(3+m) N⁻¹ ≤ ⅓ N^{1 - c/36 + (3|s|+16)τ}`. -/
private theorem Jak_crude_total_le {X c τ D : ℝ} {sc m : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ)
    (hc : c < 36) (hsc : sc ≤ m) (hD : (1 + τ) * ((m : ℝ) + 3) + 3 ≤ D)
    (hXm : 12 * (3 + (m : ℝ)) ≤ X) :
    2 * X ^ ((1 + τ) * ((sc : ℝ) + 3)) *
        (((3 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D))) ≤
      1 / 3 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (1 + τ) * ((sc : ℝ) + 3)
  have r : X ^ (a + 1 + 1 + -D) = X ^ a * X * X * X ^ (-D) := by
    rw [Real.rpow_add hX0 (a + 1 + 1) (-D), Real.rpow_add hX0 (a + 1) 1, Real.rpow_add hX0 a 1,
      Real.rpow_one]
  have e : 2 * X ^ a * (((3 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D))) =
      4 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + -D) := by
    rw [r]
    ring
  rw [e]
  have f : X ^ (a + 1 + 1 + -D) ≤ X ^ (-1 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a]
    nlinarith
  have hT : (1 : ℝ) ≤ X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) :=
    Real.one_le_rpow hX (by
      have : (0 : ℝ) ≤ (3 * (sc : ℝ) + 16) * τ := by positivity
      linarith)
  rw [Real.rpow_neg_one] at f
  have h2 : 4 * (3 + (m : ℝ)) * X⁻¹ ≤ 1 / 3 := by
    rw [mul_inv_le_iff₀ hX0]; linarith
  calc 4 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + -D)
      ≤ 4 * (3 + (m : ℝ)) * X⁻¹ := by gcongr
    _ ≤ 1 / 3 := h2
    _ ≤ _ := by linarith

/-- The factors `Im m_t(w_j)`, product form: `∏_{j∈s} (η̃/Im w_j) N^δ ≤ N^{(3τ+δ)|s|}`. -/
private theorem Jak_prod_row_le {X τ δ ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
    {m : ℕ} (s : Finset (Fin m)) (w : Fin m → ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im) :
    ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hwj : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hw j)
  calc ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ ∏ _j ∈ s, X ^ (3 * τ + δ) := by
        refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
        · have := hwj j
          positivity
        · have h1 : ηt / (w j).im ≤ X ^ (3 * τ) := by
            calc ηt / (w j).im ≤ ηt / X ^ (-1 - τ) :=
                  div_le_div_of_nonneg_left hηt0.le (by positivity) (hw j)
              _ = X ^ (3 * τ) := by rw [hηt, ← Real.rpow_sub hX0]; congr 1; ring
          calc ηt / (w j).im * X ^ δ ≤ X ^ (3 * τ) * X ^ δ := by gcongr
            _ = X ^ (3 * τ + δ) := (Real.rpow_add hX0 _ _).symm
    _ = X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
        rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]

/-- On `Ξᶜ`, crude weight: `∏_{j∈s} (Im w_j)⁻¹ · 2 (Im u)⁻³ ≤ 2 N^{(1+τ)(|s|+3)}`. -/
private theorem Jak_prod_crude_le {X τ : ℝ} (hX : 1 ≤ X) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im) (hu : X ^ (-1 - τ) ≤ u.im) :
    (∏ j ∈ s, (w j).im⁻¹) * (2 * (u.im⁻¹) ^ 3) ≤ 2 * X ^ ((1 + τ) * ((s.card : ℝ) + 3)) := by
  have hX0 : 0 < X := by linarith
  have hinv : ∀ {y : ℝ}, X ^ (-1 - τ) ≤ y → y⁻¹ ≤ X ^ (1 + τ) := by
    intro y hy
    calc y⁻¹ ≤ (X ^ (-1 - τ))⁻¹ := inv_anti₀ (by positivity) hy
      _ = X ^ (1 + τ) := by rw [← Real.rpow_neg hX0.le]; congr 1; ring
  have hP : ∏ j ∈ s, (w j).im⁻¹ ≤ X ^ ((1 + τ) * (s.card : ℝ)) := by
    calc _ ≤ ∏ _j ∈ s, X ^ (1 + τ) :=
          Finset.prod_le_prod₀ (fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j)))
            (fun j _ => hinv (hw j))
      _ = _ := by rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  have hU : (u.im⁻¹) ^ 3 ≤ X ^ ((1 + τ) * 3) := by
    calc (u.im⁻¹) ^ 3 ≤ (X ^ (1 + τ)) ^ 3 :=
          pow_le_pow_left₀ (inv_nonneg.2 (le_trans (by positivity) hu)) (hinv hu) 3
      _ = X ^ ((1 + τ) * 3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_nonneg fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j))
  calc _ ≤ X ^ ((1 + τ) * (s.card : ℝ)) * (2 * X ^ ((1 + τ) * 3)) :=
        mul_le_mul hP (by linarith)
          (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.2 (le_trans (by positivity) hu)) 3))
          (by positivity)
    _ = 2 * X ^ ((1 + τ) * ((s.card : ℝ) + 3)) := by
        rw [mul_add, Real.rpow_add hX0]; ring

/-- Grid energies stay in the local-law domain: a centre within `C` of `E`, a radius `r ≤ κ/4`
and `C + 2η̃ < κ/4` give `|E₀ - r + 2η̃j| < 2 - κ/2` for `j ≤ ⌈r/η̃⌉₊`. -/
private theorem Jak_grid_energy_lt {E E₀ κ C r ηt : ℝ} {j : ℕ} (hηt : 0 < ηt)
    (hE : |E| ≤ 2 - κ) (hE₀ : |E₀ - E| ≤ C) (hr : 0 ≤ r) (hrκ : r ≤ κ / 4)
    (hC : C + 2 * ηt < κ / 4) (hj : j ∈ Finset.range (⌈r / ηt⌉₊ + 1)) :
    |E₀ - r + 2 * ηt * j| < 2 - κ / 2 := by
  have hj' : (j : ℝ) < r / ηt + 1 := by
    have h1 := Finset.mem_range.1 hj
    have h2 : (j : ℝ) ≤ ⌈r / ηt⌉₊ := by exact_mod_cast Nat.lt_succ_iff.1 h1
    linarith [Nat.ceil_lt_add_one (div_nonneg hr hηt.le)]
  have hj2 : 2 * ηt * j < 2 * r + 2 * ηt := by
    have h := mul_lt_mul_of_pos_left hj' (by positivity : (0 : ℝ) < 2 * ηt)
    have he : 2 * ηt * (r / ηt + 1) = 2 * r + 2 * ηt := by field_simp
    linarith
  have hj0 : 0 ≤ 2 * ηt * j := by positivity
  rw [abs_le] at hE hE₀
  rw [abs_lt]
  constructor <;> linarith

/-! ## Measure-theoretic and deterministic helpers -/

/-- Integration of a simple majorant: `f ≤ A₀ + c_B 1_B + C_r 1_T` (measurable `B`, `T`,
nonnegative constants) gives `∫ f ≤ A₀ + c_B P(B) + C_r P(T)`.  No integrability or
measurability of `f` is needed (if `f` is not integrable its integral is `0`). -/
private theorem Jak_integral_le_of_majorant {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {B T : Set Ω} (hB : MeasurableSet B)
    (hT : MeasurableSet T) {A0 cB Cr : ℝ} (hA0 : 0 ≤ A0) (hcB : 0 ≤ cB) (hCr : 0 ≤ Cr)
    (hfg : ∀ ω, f ω ≤ A0 + cB * B.indicator 1 ω + Cr * T.indicator 1 ω) :
    ∫ ω, f ω ∂μ ≤ A0 + cB * μ.real B + Cr * μ.real T := by
  have hint1 : ∀ A : Set Ω, MeasurableSet A → Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  have hI1 : Integrable (fun ω => A0 + cB * B.indicator (1 : Ω → ℝ) ω) μ :=
    (integrable_const A0).add ((hint1 B hB).const_mul cB)
  have hI2 : Integrable (fun ω => Cr * T.indicator (1 : Ω → ℝ) ω) μ :=
    (hint1 T hT).const_mul Cr
  have hgi : Integrable (fun ω => A0 + cB * B.indicator (1 : Ω → ℝ) ω +
      Cr * T.indicator 1 ω) μ := hI1.add hI2
  have hval : ∫ ω, (A0 + cB * B.indicator (1 : Ω → ℝ) ω + Cr * T.indicator 1 ω) ∂μ =
      A0 + cB * μ.real B + Cr * μ.real T := by
    rw [integral_add hI1 hI2, integral_add (integrable_const A0) ((hint1 B hB).const_mul cB),
      integral_const, integral_const_mul, integral_const_mul, integral_indicator_one hB,
      integral_indicator_one hT]
    simp
  rw [← hval]
  by_cases hf : Integrable f μ
  · exact integral_mono hf hgi hfg
  · rw [integral_undef hf]
    refine integral_nonneg fun ω => ?_
    have h1 : 0 ≤ B.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have h2 : 0 ≤ T.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    positivity

/-- Union bound over a finite family `S` of covering grids `(centre, radius)`: if for every grid
of `S` and every energy `e` of it the event `∃ x, Cb < ‖G_xx(e + iη̃)‖` has probability at most
`p`, then the failure of `jakGridGood` on some grid of `S` has probability at most `|S| · G · p`,
where `G` bounds the number of energies per grid. -/
private theorem Jak_measure_grid_fail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Hr : Ω → Matrix ι ι ℂ) {ηt Cb : ℝ}
    (S : Finset (ℝ × ℝ)) (G : ℕ) (hG : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ G) {p : ENNReal}
    (hp : ∀ q ∈ S, ∀ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1),
      μ {ω | ∃ x : ι, Cb <
        ‖RBM.green (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖} ≤ p) :
    μ {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt Cb q.1 q.2} ≤
      (S.card : ENNReal) * ((G : ENNReal) * p) := by
  have hsub : {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt Cb q.1 q.2} ⊆
      ⋃ q ∈ S, ⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖RBM.green (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨q, hq, hn⟩ := hω
    simp only [jakGridGood, not_forall, not_le] at hn
    obtain ⟨j, hj, x, hx⟩ := hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨q, hq, j, hj, x, hx.trans_le (Complex.im_le_norm _)⟩
  calc μ _ ≤ μ (⋃ q ∈ S, ⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖RBM.green (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖}) :=
        measure_mono hsub
    _ ≤ ∑ q ∈ S, μ (⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖RBM.green (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ S, ∑ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), μ {ω | ∃ x : ι, Cb <
        ‖RBM.green (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖} :=
        Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ S, ∑ _j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), p :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun j hj => hp q hq j hj
    _ = ∑ q ∈ S, ((⌈q.2 / ηt⌉₊ + 1 : ℕ) : ENNReal) * p := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ _q ∈ S, (G : ENNReal) * p := by
        refine Finset.sum_le_sum fun q hq => ?_
        gcongr
        exact_mod_cast hG q hq
    _ = (S.card : ENNReal) * ((G : ENNReal) * p) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- On a Hermitian matrix the definition `gSel` is the signed resolvent `Gsig`. -/
private theorem Jak_gSel_eq_Gsig {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (b : Bool) :
    gSel L W H z b = Gsig H z b := by
  rw [← signedGreen_eq_gSel L W hH z b]
  cases b <;> rfl

/-- The integrand of `Jak` is the `Gsig` expression of `jak_pointwise_good`. -/
private theorem Jak_integrand_eq {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (y : Idx L W)
    (b₁ b₂ : Bool) :
    ‖∑ x, (gSel L W H z b₁ * gSel L W H z b₁) x x * Scirc L W x y * gSel L W H z b₂ y y‖ =
      ‖∑ x, (Gsig H z b₁ ^ 2) x x * Scirc L W x y * Gsig H z b₂ y y‖ := by
  rw [Jak_gSel_eq_Gsig hH z b₁, Jak_gSel_eq_Gsig hH z b₂, sq]

/-- `c ≤ 1/2` follows from admissibility (`W ≥ N^c`, `N = (WL)² ≥ W²`, `N → ∞`). -/
private theorem Jak_c_le_half {c : ℝ} {d : Sizes} (hadm : Admissible c d) : c ≤ 1 / 2 := by
  obtain ⟨hsize, hev⟩ := hadm
  obtain ⟨n, hn2, hWn⟩ := ((hsize.eventually_ge_atTop 2).and hev).exists
  by_contra hcon
  push Not at hcon
  have hX2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hn2
  have hWX : ((d.W n : ℝ)) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
    have h1 : d.W n ^ 2 ≤ d.size n := by
      rw [Sizes.size_eq]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by have := d.three_le_L n; omega) 2)
    exact_mod_cast h1
  generalize ((d.size n : ℕ) : ℝ) = X at hX2 hWX hWn
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : 0 < X := by linarith
  have h3 : (X ^ c) ^ 2 ≤ ((d.W n : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hWn 2
  have h4 : (X ^ c) ^ 2 = X ^ (2 * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    congr 1
    push_cast
    ring
  have h5 : X ^ (1 : ℝ) < X ^ (2 * c) := Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
  rw [Real.rpow_one] at h5
  linarith

/-! ## The normalized pointwise bound on the good event -/

/-- **Good-event pointwise bound, normalized** (factors `Im m_t(w_j)`, `Q_y`, `A_y` off/on `B_y`,
`L₁` with `η̃ = N^{-1+2τ}`, `C_b = N^δ`, `w' = N^{-1+c/6}/2`, `θ = N^{-c/36}`), the
`jak_pointwise_good` of the JakKernel layer with the explicit constants. -/
private theorem Jak_pointwise_good_norm {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {H : Matrix (Idx L W) (Idx L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {X c τ δ κ ηt w' θ : ℝ} {K K' : ℕ}
    (hX : (((W * L) ^ 2 : ℕ) : ℝ) = X) (hX1 : 1 ≤ X) (hc : 0 < c) (hc2 : c < 36)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hθ : θ = X ^ (-(c / 36)))
    (hηu1 : X ^ (-1 - τ) ≤ u.im) (hηu' : u.im ≤ ηt) (hηw1 : ∀ j, X ^ (-1 - τ) ≤ (w j).im)
    (hηw' : ∀ j, (w j).im ≤ ηt)
    (hK1 : 2 ^ K * ηt ≤ κ / 4) (hK2 : κ / 4 < 2 ^ (K + 1) * ηt)
    (hK2' : κ / 4 < 2 ^ (K' + 1) * w')
    (hG1 : ∀ k ≤ K, jakGridGood H ηt (X ^ δ) u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt (X ^ δ) u.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt (X ^ δ) u.re 0)
    (hG4 : ∀ j, jakGridGood H ηt (X ^ δ) (w j).re 0)
    (Bad : Z2 L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM L W hH a0 α‖ ≤ θ)
    (y : Idx L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gsig H u σ₁ ^ 2) x x * Scirc L W x y * Gsig H u σ₂ y y‖ ≤
      X ^ ((3 * τ + δ) * (s.card : ℝ)) *
        (X⁻¹ * (((193 + 128 / κ ^ 2) * X ^ (2 - c / 36 + 4 * τ + 2 * δ) +
            (if Bad (siteBlock L W y) then 4 * X ^ (2 + 6 * τ + 2 * δ) else 0)) *
          ((6 + 16 / τ + 8 / κ) * X ^ (3 * τ + δ)))) := by
  have hX0 : 0 < X := by linarith
  have hηu : 0 < u.im := lt_of_lt_of_le (by positivity) hηu1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hw'0 : 0 < w' := by rw [hw']; positivity
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hCb : 0 ≤ X ^ δ := by positivity
  have hα₁ := Jak_alpha1_le (K' := K') hX1 hc hc2 hτ hδ hκ hηt hηu1 hw' hθ hK2'
  have hα₂ := Jak_alpha2_le (δ := δ) hX1 hηt hηu1
  have hQb := Jak_Qb_le (δ := δ) hX1 hτ hδ hκ hκ2 hηt hηu1 hK1 hK2
  have hgood := jak_pointwise_good hL hH s w u hηu hηu' hηw hηw' hCb hw'0 hθ0 K K' hG1 hG2 hG3
    hG4 Bad hBad (α₁ := (193 + 128 / κ ^ 2) * X ^ (2 - c / 36 + 4 * τ + 2 * δ))
    (α₂ := 4 * X ^ (2 + 6 * τ + 2 * δ)) (Qb := (6 + 16 / τ + 8 / κ) * X ^ (3 * τ + δ))
    (by rw [hX]; exact hα₁) (by rw [hX]; exact hα₂) hQb y σ₁ σ₂
  rw [hX] at hgood
  refine hgood.trans ?_
  have hP := Jak_prod_row_le (δ := δ) hX1 hηt s w hηw1
  refine mul_le_mul_of_nonneg_right hP ?_
  have h0 : 0 ≤ (if Bad (siteBlock L W y) then 4 * X ^ (2 + 6 * τ + 2 * δ) else 0) := by
    split_ifs <;> positivity
  positivity

/-! ## The bound at one size and one time -/

/-- **Fixed-time assembly** of `(jaklsdufowe)` at one size `(L, W)`, one time `t`, and one choice
of `s, w, u, y, b₁, b₂`: all eventual conditions are passed as explicit numeric hypotheses, and
the two `𝐇_t` claims enter as the probability bounds `hdiag` (`OUDiag` at the grid energies) and
`hque` (`OUQUE`).  Per site `y`. -/
private theorem Jak_fixed_time {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (t : ℝ)
    {X c κ τ δ C₀ E D : ℝ} {m : ℕ}
    (hX : (((W * L) ^ 2 : ℕ) : ℝ) = X) (hWc : X ^ c ≤ (W : ℝ))
    (hc : 0 < c) (hc36 : c < 36) (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) (hδ : 0 < δ)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hD : (1 + τ) * ((m : ℝ) + 3) + 3 ≤ D)
    (hE : |E| ≤ 2 - κ) (h1 : 12 * (3 + (m : ℝ)) ≤ X) (h2 : 2 * C₀ ≤ X ^ (c / 6))
    (h3 : C₀ / X + 2 * X ^ (-1 + 2 * τ) < κ / 4) (h4 : X ^ (-1 + c / 6) < κ / 2)
    (h5 : 3 * ((193 + 128 / κ ^ 2) + 20) * (6 + 16 / τ + 8 / κ) ≤ X ^ (6 * τ))
    (hdiag : ∀ e : ℝ, |e| < 2 - κ / 2 →
      ouP L W {ω | ∃ x : Idx L W, X ^ δ <
        ‖RBM.green (ouMat L W t ω) ((e : ℂ) + ((X ^ (-1 + 2 * τ) : ℝ) : ℂ) * Complex.I) x x‖} ≤
        ENNReal.ofReal (X ^ (-D)))
    (hque : ∀ a : Z2 L,
      ouP L W {ω | queBadMat L W ((W * L) ^ 2) (c / 3) E a (ouMat L W t ω)} ≤
        ENNReal.ofReal (X ^ (-(c / 3) / 6)))
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u : ℂ)
    (hw : ∀ i, |(w i).re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ (w i).im ∧ (w i).im ≤ X ^ (-1 + τ))
    (hu : |u.re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ u.im ∧ u.im ≤ X ^ (-1 + τ))
    (y : Idx L W) (b₁ b₂ : Bool) :
    ∫ ω, (∏ j ∈ s, (stieltjesN (ouMat L W t ω) (w j)).im) *
        ‖∑ x, (gSel L W (ouMat L W t ω) u b₁ * gSel L W (ouMat L W t ω) u b₁) x x *
            Scirc L W x y * gSel L W (ouMat L W t ω) u b₂ y y‖ ∂(ouP L W) ≤
      X ^ (1 - c / 36 + (3 * (s.card : ℝ) + 16) * τ) := by
  classical
  have hX1 : 1 ≤ X := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨ηt, hηt⟩ : ∃ ηt : ℝ, ηt = X ^ (-1 + 2 * τ) := ⟨_, rfl⟩
  obtain ⟨w', hw'def⟩ : ∃ w' : ℝ, w' = X ^ (-1 + c / 6) / 2 := ⟨_, rfl⟩
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hCb0 : 0 < X ^ δ := by positivity
  have hw'0 : 0 < w' := by rw [hw'def]; positivity
  have hC₀n : 0 ≤ C₀ / X := le_trans (abs_nonneg _) hu.1
  have hηtκ : ηt ≤ κ / 4 := by rw [hηt]; linarith
  have hw'κ : w' ≤ κ / 4 := by rw [hw'def]; linarith
  have hw'eq : w' = (2 * X ^ (1 - c / 6))⁻¹ := by
    rw [hw'def, mul_inv, show -1 + c / 6 = -(1 - c / 6) by ring, Real.rpow_neg hX0.le]
    ring
  obtain ⟨K, hK1, hK2⟩ := Jak_exists_dyadic hηt0 hηtκ
  obtain ⟨K', hK1', hK2'⟩ := Jak_exists_dyadic hw'0 hw'κ
  have hure : |u.re - E| ≤ C₀ / X := hu.1
  have hηu1 : X ^ (-1 - τ) ≤ u.im := hu.2.1
  have hηu : 0 < u.im := lt_of_lt_of_le (by positivity) hηu1
  have hle_ηt : ∀ {y : ℝ}, y ≤ X ^ (-1 + τ) → y ≤ ηt := fun hy =>
    hy.trans (by rw [hηt]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))
  have hηu' : u.im ≤ ηt := hle_ηt hu.2.2
  have hηw1 : ∀ j, X ^ (-1 - τ) ≤ (w j).im := fun j => (hw j).2.1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hηw' : ∀ j, (w j).im ≤ ηt := fun j => hle_ηt (hw j).2.2
  -- the finite family of covering grids (centre, radius)
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (ℝ × ℝ), S =
      ((Finset.range (K + 1)).image fun k => (u.re, (2 : ℝ) ^ k * ηt)) ∪
        ((Finset.range (K' + 1)).image fun k => (u.re, (2 : ℝ) ^ k * w')) ∪
        {(u.re, 0)} ∪ (Finset.univ.image fun j => ((w j).re, (0 : ℝ))) := ⟨_, rfl⟩
  have hS : ∀ q ∈ S, |q.1 - E| ≤ C₀ / X ∧ 0 ≤ q.2 ∧ q.2 ≤ κ / 4 := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton, Finset.mem_univ, true_and] at hq
    rcases hq with ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | rfl) | ⟨j, rfl⟩
    · refine ⟨hure, by positivity, le_trans ?_ hK1⟩
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hηt0.le
    · refine ⟨hure, by positivity, le_trans ?_ hK1'⟩
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hw'0.le
    · exact ⟨hure, le_rfl, by positivity⟩
    · exact ⟨(hw j).1, le_rfl, by positivity⟩
  have hSmem1 : ∀ k ≤ K, (u.re, (2 : ℝ) ^ k * ηt) ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl ⟨k, by omega, rfl⟩))
  have hSmem2 : ∀ k ≤ K', (u.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩))
  have hSmem3 : (u.re, (0 : ℝ)) ∈ S := by
    rw [hSdef]; simp
  have hSmem4 : ∀ j, ((w j).re, (0 : ℝ)) ∈ S := fun j => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, rfl⟩
  -- sizes: `2^K ≤ X`, `2^{K'} ≤ X`, `#S ≤ (3+m) X`, grid size `≤ G ≤ 2X`
  have hηtinv : ηt⁻¹ ≤ X := by
    rw [hηt, ← Real.rpow_neg hX0.le]
    calc X ^ (-(-1 + 2 * τ)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  have h2K : (2 : ℝ) ^ K ≤ X := by
    calc (2 : ℝ) ^ K ≤ 1 / ηt := (le_div_iff₀ hηt0).2 (by linarith)
      _ = ηt⁻¹ := one_div _
      _ ≤ X := hηtinv
  have h2K' : (2 : ℝ) ^ K' ≤ X := by
    have hinv : (2 * w')⁻¹ ≤ X := by
      rw [hw'eq, mul_inv, inv_inv, ← mul_assoc, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, one_mul]
      calc X ^ (1 - c / 6) ≤ X ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    calc (2 : ℝ) ^ K' ≤ 1 / (2 * w') := (le_div_iff₀ (by positivity)).2 (by linarith)
      _ = (2 * w')⁻¹ := one_div _
      _ ≤ X := hinv
  have hScard : (S.card : ℝ) ≤ (3 + m) * X := by
    have hc1 : S.card ≤ (K + 1) + (K' + 1) + 1 + m := by
      rw [hSdef]
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) ?_
      · refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ?_ ?_
        · exact (Finset.card_image_le).trans (by simp)
        · exact (Finset.card_image_le).trans (by simp)
      · exact (Finset.card_image_le).trans (by simp)
    have hK : (K : ℝ) < X := lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) h2K
    have hK' : (K' : ℝ) < X := lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) h2K'
    have hc1' : (S.card : ℝ) ≤ (K + 1) + (K' + 1) + 1 + m := by exact_mod_cast hc1
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    nlinarith
  have hGS : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ ⌈X⌉₊ + 1 := by
    intro q hq
    obtain ⟨-, hq0, hqκ⟩ := hS q hq
    have : q.2 / ηt ≤ X := by
      rw [div_eq_mul_inv]
      calc q.2 * ηt⁻¹ ≤ 1 * X := mul_le_mul (by linarith) hηtinv (by positivity) zero_le_one
        _ = X := one_mul X
    exact Nat.add_le_add_right (Nat.ceil_mono this) 1
  have hG : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * X := by
    push_cast; linarith [Nat.ceil_lt_add_one hX0.le]
  -- the event `T`: failure of a covering grid, with its probability from `OUDiag`
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Ω L W × Ω L W), T = toMeasurable (ouP L W)
      {ω | ¬ ∀ q ∈ S, jakGridGood (ouMat L W t ω) ηt (X ^ δ) q.1 q.2} := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by rw [hTdef]; exact measurableSet_toMeasurable _ _
  have hTprob : (ouP L W).real T ≤ ((3 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D)) := by
    have hgrid := Jak_measure_grid_fail (μ := ouP L W) (ouMat L W t) (ηt := ηt)
      (Cb := X ^ δ) S (⌈X⌉₊ + 1) hGS (p := ENNReal.ofReal (X ^ (-D))) (by
        intro q hq j hj
        obtain ⟨hq1, hq0, hqκ⟩ := hS q hq
        have he := Jak_grid_energy_lt hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
        have := hdiag _ he
        rw [← hηt] at this
        exact this)
    have hne : ((S.card : ENNReal) * (((⌈X⌉₊ + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal (X ^ (-D)))) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
    have hX0D : 0 ≤ X ^ (-D) := by positivity
    calc (ouP L W).real T
        = ((ouP L W) {ω | ¬ ∀ q ∈ S, jakGridGood (ouMat L W t ω) ηt (X ^ δ) q.1 q.2}).toReal := by
          rw [hTdef, Measure.real, measure_toMeasurable]
      _ ≤ ((S.card : ENNReal) * (((⌈X⌉₊ + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (X ^ (-D)))).toReal := ENNReal.toReal_mono hne hgrid
      _ = (S.card : ℝ) * (((⌈X⌉₊ + 1 : ℕ) : ℝ) * X ^ (-D)) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0D,
            ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      _ ≤ ((3 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D)) := by gcongr
  -- the bad blocks: `OUQUE` through the union bound over the five blocks
  obtain ⟨Bs, hBsdef⟩ : ∃ Bs : Z2 L → Set (Ω L W × Ω L W), Bs = fun a0 =>
      {ω | ∃ α, |(ouMat_isHermitian L W t ω).eigenvalues α - E| ≤ X ^ (-1 + c / 6) ∧
        X ^ (-(c / 36)) ≤ ‖blockM L W (ouMat_isHermitian L W t ω) a0 α‖} := ⟨_, rfl⟩
  obtain ⟨Bm, hBmdef⟩ : ∃ Bm : Z2 L → Set (Ω L W × Ω L W),
      Bm = fun a0 => toMeasurable (ouP L W) (Bs a0) := ⟨_, rfl⟩
  have hBmm : ∀ a0, MeasurableSet (Bm a0) := fun a0 => by
    rw [hBmdef]; exact measurableSet_toMeasurable _ _
  have hBprob : ∀ a0, (ouP L W).real (Bm a0) ≤ 5 * X ^ (-(c / 18)) := by
    intro a0
    have hw : X ^ (-1 + c / 6) ≤
        (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 - c / 3) * (W : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [hX]
      have h1 : X ^ (-1 - c / 3) * X ^ (2 * c / 3) ≤
          X ^ (-1 - c / 3) * (W : ℝ) ^ ((2 : ℝ) / 3) := by
        gcongr
        calc X ^ (2 * c / 3) = (X ^ c) ^ ((2 : ℝ) / 3) := by
              rw [← Real.rpow_mul hX0.le]; congr 1; ring
          _ ≤ (W : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hWc (by norm_num)
      calc X ^ (-1 + c / 6) ≤ X ^ (-1 - c / 3 + 2 * c / 3) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X ^ (-1 - c / 3) * X ^ (2 * c / 3) := Real.rpow_add hX0 _ _
        _ ≤ _ := h1
    have hθ0 : 0 ≤ X ^ (-(c / 36)) := by positivity
    have hθτ : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-(c / 3) / 6) ≤ (X ^ (-(c / 36))) ^ 2 := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      apply le_of_eq
      congr 1
      push_cast
      ring
    have h := measure_bad_le_of_queBadMat (L := L) (W := W) (P := ouP L W)
      (Hr := ouMat L W t) (ouMat_isHermitian L W t) (E := E) (w := X ^ (-1 + c / 6))
      (τ := c / 3) (θ := X ^ (-(c / 36))) (ε' := X ^ (-(c / 3) / 6)) hw hθ0 hθτ a0 hque
    rw [Measure.real, hBmdef]
    simp only [measure_toMeasurable]
    rw [hBsdef]
    calc _ ≤ 5 * X ^ (-(c / 3) / 6) := ENNReal.toReal_le_of_le_ofReal (by positivity) h
      _ = 5 * X ^ (-(c / 18)) := by congr 2; ring
  -- the majorant constants
  have hsc : s.card ≤ m := by simpa using Finset.card_le_univ s
  obtain ⟨Pw, hPw⟩ : ∃ Pw : ℝ, Pw = X ^ ((3 * τ + δ) * (s.card : ℝ)) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 193 + 128 / κ ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 6 + 16 / τ + 8 / κ := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hPw0 : 0 ≤ Pw := by rw [hPw]; positivity
  have hA0 : 0 ≤ Pw * (X⁻¹ * ((C₁ * X ^ (2 - c / 36 + 4 * τ + 2 * δ)) *
      (C₂ * X ^ (3 * τ + δ)))) := by positivity
  have hcB0 : 0 ≤ Pw * (X⁻¹ * ((4 * X ^ (2 + 6 * τ + 2 * δ)) * (C₂ * X ^ (3 * τ + δ)))) := by
    positivity
  have hCr0 : 0 ≤ 2 * X ^ ((1 + τ) * ((s.card : ℝ) + 3)) := by positivity
  -- pointwise domination
  have hfg : ∀ ω, (∏ j ∈ s, (stieltjesN (ouMat L W t ω) (w j)).im) *
      ‖∑ x, (gSel L W (ouMat L W t ω) u b₁ * gSel L W (ouMat L W t ω) u b₁) x x *
        Scirc L W x y * gSel L W (ouMat L W t ω) u b₂ y y‖ ≤
      Pw * (X⁻¹ * ((C₁ * X ^ (2 - c / 36 + 4 * τ + 2 * δ)) * (C₂ * X ^ (3 * τ + δ)))) +
        (Pw * (X⁻¹ * ((4 * X ^ (2 + 6 * τ + 2 * δ)) * (C₂ * X ^ (3 * τ + δ))))) *
          (Bm (siteBlock L W y)).indicator 1 ω +
        (2 * X ^ ((1 + τ) * ((s.card : ℝ) + 3))) * T.indicator 1 ω := by
    intro ω
    have hH := ouMat_isHermitian L W t ω
    rw [Jak_integrand_eq hH u y b₁ b₂]
    have hind : ∀ (A : Set (Ω L W × Ω L W)), 0 ≤ A.indicator (1 : Ω L W × Ω L W → ℝ) ω :=
      fun A => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    by_cases hωT : ω ∈ T
    · -- the crude bound
      have hc1 := jak_pointwise_crude hL hH s w u hηu hηw y b₁ b₂
      have hc2 := Jak_prod_crude_le hX1 s w u hηw1 hηu1
      have hTi : T.indicator (1 : Ω L W × Ω L W → ℝ) ω = 1 := by
        simp [Set.indicator_of_mem hωT]
      rw [hTi, mul_one]
      have := mul_nonneg hcB0 (hind (Bm (siteBlock L W y)))
      linarith [hc1.trans hc2]
    · -- good event
      have hΞ : ∀ q ∈ S, jakGridGood (ouMat L W t ω) ηt (X ^ δ) q.1 q.2 := by
        by_contra hn'
        apply hωT
        rw [hTdef]
        exact subset_toMeasurable _ _ hn'
      have hBad : ∀ a0, ¬ (ω ∈ Bm a0) → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
          ‖blockM L W hH a0 α‖ ≤ X ^ (-(c / 36)) := by
        intro a0 hna α hα
        have hnb : ω ∉ Bs a0 := fun hb => hna (by rw [hBmdef]; exact subset_toMeasurable _ _ hb)
        rw [hBsdef] at hnb
        simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hnb
        refine (hnb α ?_).le
        have hsplit : X ^ (-1 + c / 6) = X ^ (c / 6) * X⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hX0]; congr 1; ring
        have hC : C₀ / X ≤ X ^ (-1 + c / 6) / 2 := by
          rw [hsplit, div_eq_mul_inv]
          have := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hX0.le)
          linarith
        calc |hH.eigenvalues α - E| ≤ |hH.eigenvalues α - u.re| + |u.re - E| :=
              abs_sub_le _ _ _
          _ ≤ w' + C₀ / X := add_le_add hα hure
          _ ≤ X ^ (-1 + c / 6) := by rw [hw'def]; linarith
      have hgood := Jak_pointwise_good_norm hL hH s w u (δ := δ) (θ := X ^ (-(c / 36))) hX hX1
        hc hc36 hτ hδ.le hκ hκ2 hηt hw'eq rfl hηu1 hηu' hηw1 hηw' hK1 hK2 hK2'
        (fun k hk => hΞ (u.re, (2 : ℝ) ^ k * ηt) (hSmem1 k hk))
        (fun k hk => hΞ (u.re, (2 : ℝ) ^ k * w') (hSmem2 k hk)) (hΞ (u.re, 0) hSmem3)
        (fun j => hΞ ((w j).re, 0) (hSmem4 j)) (fun a0 => ω ∈ Bm a0) hBad y b₁ b₂
      rw [← hPw, ← hC₁, ← hC₂] at hgood
      have hTi : T.indicator (1 : Ω L W × Ω L W → ℝ) ω = 0 := Set.indicator_of_notMem hωT _
      rw [hTi, mul_zero, add_zero]
      by_cases hb : ω ∈ Bm (siteBlock L W y)
      · simp only [hb, ite_true] at hgood
        rw [Set.indicator_of_mem hb, Pi.one_apply]
        calc _ ≤ _ := hgood
          _ = _ := by ring
      · simp only [hb, ite_false] at hgood
        rw [Set.indicator_of_notMem hb]
        calc _ ≤ _ := hgood
          _ = _ := by ring
  have hint := Jak_integral_le_of_majorant (μ := ouP L W) (hBmm (siteBlock L W y)) hTm hA0 hcB0
    hCr0 hfg
  -- final normalisation: good part, bad part and crude part, each `≤ ⅓ X^T`
  have hgoodT := Jak_good_total_le (X := X) (c := c) (δ := δ) (C₁ := C₁) (C₂ := C₂)
    (sc := s.card) (m := m) hX1 hc.le hτ hδ.le hC₁0 hC₂0 hsc hmδ (by rw [hC₁, hC₂]; exact h5)
  have hcrudeT := Jak_crude_total_le (X := X) (c := c) (τ := τ) (D := D) (sc := s.card) (m := m)
    hX1 hτ hc36 hsc hD h1
  rw [← hPw] at hgoodT
  have hB2 := mul_le_mul_of_nonneg_left (hBprob (siteBlock L W y)) hcB0
  have hT2 := mul_le_mul_of_nonneg_left hTprob hCr0
  have hXT : 0 ≤ X ^ (1 - c / 36 + (3 * (s.card : ℝ) + 16) * τ) := by positivity
  refine hint.trans ?_
  linarith

/-! ## The eventual statement and the reduction `jakRow` -/

/-- `Jak` at `c' = 𝔠/36` and `C = 3 nf + 16`, for one small `τ_U`, from the two `𝐇_t` claims.
The weights `∏ Im m_t(z_j)` and the grid event come from `OUDiag` (at `κ/2`, `ε := δ`,
`D := (1+τ_U)(nf+3)+3`), the bad blocks from `OUQUE` (at `κ/2`). -/
private theorem Jak_main {c : ℝ} (hc : 0 < c) {d : Sizes} (hadm : Admissible c d)
    {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ) (nf : ℕ) {τU : ℝ} (hτ : 0 < τU)
    (hτ4 : τU ≤ 1 / 4) (hQUE : OUQUE c d τU) (hDiag : OUDiag d τU) :
    Jak d E nf τU (3 * (nf : ℝ) + 16) (c / 36) := by
  intro C₀ ε hC₀ hε
  have hc12 : c ≤ 1 / 2 := Jak_c_le_half hadm
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  -- parameters fixed before `n`: `δ = τU/(nf+5)` and the exponent `D` of `OUDiag`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (nf + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((nf : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (1 + τU) * ((nf : ℝ) + 3) + 3 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hsize : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hadm.1
  -- the eventual conditions on `n` (finitely many, uniform in `t, s, z, i, y, b₁, b₂`)
  have ev1 : ∀ᶠ n in atTop, 12 * (3 + (nf : ℝ)) ≤ ((d.size n : ℕ) : ℝ) :=
    hsize.eventually_ge_atTop _
  have ev2 : ∀ᶠ n in atTop, 2 * C₀ ≤ ((d.size n : ℕ) : ℝ) ^ (c / 6) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have ev3 : ∀ᶠ n in atTop, C₀ / ((d.size n : ℕ) : ℝ) +
      2 * ((d.size n : ℕ) : ℝ) ^ (-1 + 2 * τU) < κ / 4 := by
    have h1 : Tendsto (fun n => C₀ / ((d.size n : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsize
    have h2 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-1 + 2 * τU)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - 2 * τU) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    have h3 := h1.add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at h3
    exact h3.eventually_lt_const (by positivity)
  have ev4 : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + c / 6) < κ / 2 := by
    have h2 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-1 + c / 6)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - c / 6) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    exact h2.eventually_lt_const (by positivity)
  have ev5 : ∀ᶠ n in atTop, 3 * ((193 + 128 / κ ^ 2) + 20) * (6 + 16 / τU + 8 / κ) ≤
      ((d.size n : ℕ) : ℝ) ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have evD := hDiag (κ / 2) δ D (half_pos hκ) hδ hD0
  have evQ := hQUE (κ / 2) (half_pos hκ)
  filter_upwards [hadm.2, ev1, ev2, ev3, ev4, ev5, evD, evQ] with n hWn h1 h2 h3 h4 h5 hDn hQn
  intro z hz t ht0 htT s i y b₁ b₂
  have hX1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ nf := nf.cast_nonneg
    linarith
  have hsc : s.card ≤ nf := by simpa using Finset.card_le_univ s
  have hfix := Jak_fixed_time (d.three_le_L n) t (X := ((d.size n : ℕ) : ℝ)) (c := c) (κ := κ)
    (τ := τU) (δ := δ) (C₀ := C₀) (E := E) (D := D) (m := nf) rfl hWn hc (by linarith) hκ hκ2
    hτ hδ hmδ (by rw [hDdef]) hE h1 h2 h3 h4 h5 (fun e he => hDn t ht0 htT e he)
    (hQn t ht0 htT E (by linarith)) s z (z i) (fun j => hz j) (hz i) y b₁ b₂
  refine hfix.trans ?_
  calc ((d.size n : ℕ) : ℝ) ^ (1 - c / 36 + (3 * (s.card : ℝ) + 16) * τU)
      ≤ ((d.size n : ℕ) : ℝ) ^ (1 - c / 36 + (3 * (nf : ℝ) + 16) * τU) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        have : (s.card : ℝ) ≤ nf := by exact_mod_cast hsc
        nlinarith
    _ = 1 * ((d.size n : ℕ) : ℝ) ^ (1 - c / 36 + (3 * (nf : ℝ) + 16) * τU) := (one_mul _).symm
    _ ≤ ((d.size n : ℕ) : ℝ) ^ ε *
        ((d.size n : ℕ) : ℝ) ^ (1 - c / 36 + (3 * (nf : ℝ) + 16) * τU) := by
        gcongr
        exact Real.one_le_rpow hX1 hε.le

/-- **The `Jak` half of `JakUywRow`**: the weighted `(jaklsdufowe)`, at `c' = 𝔠/36`, from the
`𝐇_t` claims.  `locSC` is the first hypothesis of `JakUywRow` and is not used. -/
theorem jakRow :
    locSC → OUClaims → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C : ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
        ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → Jak d E nf τU C (𝔠 / 36) := by
  intro _hloc hclaims 𝔠 h𝔠 d hadm κ hκ E hE nf
  obtain ⟨τ₁, hτ₁, hτ⟩ := hclaims 𝔠 h𝔠 d hadm
  refine ⟨3 * (nf : ℝ) + 16, min τ₁ (1 / 4), lt_min hτ₁ (by norm_num), ?_⟩
  intro τU hτU hτle
  obtain ⟨hQ, hD⟩ := hτ τU hτU (le_min_iff.1 hτle).1
  exact Jak_main h𝔠 hadm hκ hE nf hτU (le_min_iff.1 hτle).2 hQ hD

end RBM.Univ
