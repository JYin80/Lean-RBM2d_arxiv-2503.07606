/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Kcal
import RBM2D.Propagator.Prop5
import RBM2D.Propagator.Prop6

/-!
# Discharging `Prop5Hyp κ (1/20000)` and `Prop6Hyp κ`

Properties 5 and 6 of `lem_propTH` (`prop:ThfadC`, `prop:BD1`, `prop:BD2`) hold in the
`UnifDetDom` form, uniformly over the parameter set `Par κ N`.  The proofs use the
explicit-constant theorems `norm_Theta_apply_le_prop5` and `norm_Theta_fd_prop6` together with
`L ≤ N` (from `W² L² = N`, `W ≥ 1`), so they cover every `(L, W)` and not only `L → ∞`.

Public: `prop5Hyp_holds`, `prop6Hyp_holds`.
-/

open Filter Topology

namespace RBM.KLoop

private theorem PropHyp_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖ξ‖ < 1` for the three spectral parameters of properties 5-6. -/
private theorem PropHyp_norm_xiSet {κ : ℝ} {N : ℕ} (hκ : 0 < κ) (p : Par κ N) (j : Fin 3) :
    ‖xiSet p.E p.t j‖ < 1 := by
  have hE : |p.E| ≤ 2 := by linarith [p.hE]
  have h1 : ‖(p.t : ℂ)‖ = p.t := by
    rw [Complex.norm_real, Real.norm_of_nonneg p.ht0]
  have h2 : ‖(p.t : ℂ) * mSig p.E true ^ 2‖ = p.t := by
    rw [norm_mul, norm_pow, PropHyp_norm_mSig hE, h1]; simp
  have h3 : ‖(p.t : ℂ) * mSig p.E false ^ 2‖ = p.t := by
    rw [norm_mul, norm_pow, PropHyp_norm_mSig hE, h1]; simp
  fin_cases j
  · change ‖(p.t : ℂ) * mSig p.E true ^ 2‖ < 1
    rw [h2]; exact p.ht1
  · change ‖(p.t : ℂ) * mSig p.E false ^ 2‖ < 1
    rw [h3]; exact p.ht1
  · change ‖(p.t : ℂ)‖ < 1
    rw [h1]; exact p.ht1

/-- `L ≤ N` on the parameter set. -/
private theorem PropHyp_L_le {κ : ℝ} {N : ℕ} (p : Par κ N) : p.L ≤ N := by
  have h1 := p.hN
  have h2 := p.hW
  have h3 : p.L ≤ p.L ^ 2 := by nlinarith [p.hL]
  have h4 : p.L ^ 2 ≤ p.W ^ 2 * p.L ^ 2 := by
    have : 1 ≤ p.W ^ 2 := Nat.one_le_pow _ _ h2
    nlinarith [Nat.zero_le (p.L ^ 2)]
  omega

private theorem PropHyp_log_le {κ : ℝ} {N : ℕ} (p : Par κ N) :
    1 + Real.log p.L ≤ 1 + Real.log N := by
  have h : (p.L : ℝ) ≤ N := by exact_mod_cast PropHyp_L_le p
  have hpos : (0 : ℝ) < p.L := by have := p.hL; exact_mod_cast (by omega : 0 < p.L)
  linarith [Real.log_le_log hpos h]

/-- Property 5 (`prop:ThfadC`) with `c = 1/20000`, uniformly over `Par κ N`. -/
theorem prop5Hyp_holds (κ : ℝ) (hκ : 0 < κ) : Prop5Hyp κ (1 / 20000) := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [detDom_iff.mp one_add_log_detDom_one (τ / 2) hτ2,
    eventually_le_rpow (180 * 40002 ^ 2) hτ2] with N hlogN hCN u
  obtain ⟨p, j, a, b⟩ := u
  have hξ := PropHyp_norm_xiSet hκ p j
  have hb := norm_Theta_apply_le_prop5 p.L p.hL _ hξ a b
  set ξ := xiSet p.E p.t j with hξdef
  have hk : kappa ξ ^ 2 = ‖(1 : ℂ) - ξ‖ := kappa_sq ξ
  have hg : 0 ≤ Real.exp (-((1 / 20000 : ℝ) * (zdist2 p.L (a - b) : ℝ)) / ellhat p.L ξ) /
      (‖(1 : ℂ) - ξ‖ * ellhat p.L ξ ^ 2) := by positivity
  have hlog : 0 ≤ 1 + Real.log N := one_add_log_nonneg N
  have hpow : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hlogN' : 1 + Real.log N ≤ (N : ℝ) ^ (τ / 2) := by simpa using hlogN
  have hlogL := PropHyp_log_le p
  have hC0 : (0 : ℝ) ≤ 180 * 40002 ^ 2 := by norm_num
  have heq : (kappa ξ ^ 2 * ellhat p.L ξ ^ 2)⁻¹ *
      Real.exp (-(zdist2 p.L (a - b) : ℝ) / (20000 * ellhat p.L ξ)) =
      Real.exp (-((1 / 20000 : ℝ) * (zdist2 p.L (a - b) : ℝ)) / ellhat p.L ξ) /
      (‖(1 : ℂ) - ξ‖ * ellhat p.L ξ ^ 2) := by
    rw [hk, div_eq_mul_inv, div_eq_mul_inv, mul_comm]
    congr 2
    field_simp
  change ‖Theta p.L ξ a b‖ ≤ (N : ℝ) ^ τ * _
  rw [← heq] at hg ⊢
  calc ‖Theta p.L ξ a b‖
      ≤ (180 * 40002 ^ 2) * (1 + Real.log p.L) *
          ((kappa ξ ^ 2 * ellhat p.L ξ ^ 2)⁻¹ *
            Real.exp (-(zdist2 p.L (a - b) : ℝ) / (20000 * ellhat p.L ξ))) := by
        simpa only [mul_assoc] using hb
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) *
          ((kappa ξ ^ 2 * ellhat p.L ξ ^ 2)⁻¹ *
            Real.exp (-(zdist2 p.L (a - b) : ℝ) / (20000 * ellhat p.L ξ))) := by
        have h1 : (180 * 40002 ^ 2) * (1 + Real.log p.L) ≤
            (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
          mul_le_mul hCN (hlogL.trans hlogN') (by linarith [Real.log_natCast_nonneg p.L]) hpow
        exact mul_le_mul_of_nonneg_right h1 hg
    _ = (N : ℝ) ^ τ *
          ((kappa ξ ^ 2 * ellhat p.L ξ ^ 2)⁻¹ *
            Real.exp (-(zdist2 p.L (a - b) : ℝ) / (20000 * ellhat p.L ξ))) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half N hτ]

private theorem PropHyp_prefactor_le {κ : ℝ} {N : ℕ} (p : Par κ N) :
    derivativePrefactor (10 ^ 14) p.L ≤ derivativePrefactor (10 ^ 14) N := by
  unfold derivativePrefactor
  have := PropHyp_log_le p
  linarith

/-- Properties 6 (`prop:BD1`, `prop:BD2`), uniformly over `Par κ N`. -/
theorem prop6Hyp_holds (κ : ℝ) (hκ : 0 < κ) : Prop6Hyp κ := by
  refine ⟨?_, ?_⟩
  · intro τ hτ
    filter_upwards [derivativePrefactor_eventually_le_rpow (10 ^ 14) (by norm_num) τ hτ]
      with N hN u
    obtain ⟨p, j, a, b, s⟩ := u
    have hξ := PropHyp_norm_xiSet hκ p j
    have hb := (norm_Theta_fd_prop6 p.L p.hL _ hξ a b s).1
    set ξ := xiSet p.E p.t j with hξdef
    have heq : (zdist2 p.L s : ℝ) * ((zdist2 p.L (a - b) : ℝ) + 1)⁻¹ +
        (zdist2 p.L s : ℝ) * (kappa ξ * (ellhat p.L ξ) ^ 2)⁻¹ =
        (zdist2 p.L s : ℝ) / ((zdist2 p.L (a - b) : ℝ) + 1) +
          (zdist2 p.L s : ℝ) / (ellhat p.L ξ ^ 2 * Real.sqrt ‖(1 : ℂ) - ξ‖) := by
      unfold kappa
      simp only [div_eq_mul_inv]
      ring
    have hg : 0 ≤ (zdist2 p.L s : ℝ) * ((zdist2 p.L (a - b) : ℝ) + 1)⁻¹ +
        (zdist2 p.L s : ℝ) * (kappa ξ * (ellhat p.L ξ) ^ 2)⁻¹ := by
      have := fd1Scale_nonneg (L := p.L) hξ (a - b) s
      simpa only [fd1Scale] using this
    change ‖Theta p.L ξ a b - Theta p.L ξ a (b + s)‖ ≤ (N : ℝ) ^ τ * _
    rw [← heq]
    calc _ ≤ _ := hb
      _ ≤ (N : ℝ) ^ τ * _ :=
        mul_le_mul_of_nonneg_right ((PropHyp_prefactor_le p).trans hN) hg
  · intro τ hτ
    filter_upwards [derivativePrefactor_eventually_le_rpow (10 ^ 14) (by norm_num) τ hτ]
      with N hN u
    obtain ⟨p, j, a, b, s⟩ := u
    have hξ := PropHyp_norm_xiSet hκ p j
    have hb := (norm_Theta_fd_prop6 p.L p.hL _ hξ a b s).2
    set ξ := xiSet p.E p.t j with hξdef
    have heq : (zdist2 p.L s : ℝ) ^ 2 * ((zdist2 p.L (a - b) : ℝ) ^ 2 + 1)⁻¹ +
        (zdist2 p.L s : ℝ) ^ 2 * ((ellhat p.L ξ) ^ 2)⁻¹ =
        (zdist2 p.L s : ℝ) ^ 2 / ((zdist2 p.L (a - b) : ℝ) ^ 2 + 1) +
          (zdist2 p.L s : ℝ) ^ 2 / ellhat p.L ξ ^ 2 := by
      simp only [div_eq_mul_inv]
    have hg : 0 ≤ (zdist2 p.L s : ℝ) ^ 2 * ((zdist2 p.L (a - b) : ℝ) ^ 2 + 1)⁻¹ +
        (zdist2 p.L s : ℝ) ^ 2 * ((ellhat p.L ξ) ^ 2)⁻¹ := by
      have := fd2Scale_nonneg (L := p.L) (ξ := ξ) (a - b) s
      simpa only [fd2Scale] using this
    change ‖2 * Theta p.L ξ a b - Theta p.L ξ a (b + s) - Theta p.L ξ a (b - s)‖ ≤
      (N : ℝ) ^ τ * _
    rw [← heq]
    calc _ ≤ _ := hb
      _ ≤ (N : ℝ) ^ τ * _ :=
        mul_le_mul_of_nonneg_right ((PropHyp_prefactor_le p).trans hN) hg

end RBM.KLoop
