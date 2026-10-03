/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Induction.SumZeroQ
import RBM2D.Loop.Ward
import RBM2D.Hierarchy.WardResolvent
import RBM2D.Propagator.Prop5
import RBM2D.Propagator.Bounds
import RBM2D.Path.ScalesBridge
import RBM2D.Loop.LatticeCount
import RBM2D.Induction.Chain

/-!
# `ℬ₅`, `ℬ₄` and `𝒫(𝓛-𝒦)` for alternating `σ`: the deterministic estimates

Paper: arXiv:2503.07606, Section 5: `int_K-L+Q2`, `jfasiuu`, `jywiiwsoks`, `eq:thetadot_bound`,
`kkuuwsaf`, `kkuuwsaf5`; `lem_WI_K` (Ward identity), property 5 (`prop:ThfadC`).  Namespace
`RBM.Ind`.

## Contents

The public declarations are `B45_psum_le_pub`, `B45_norm_vartheta_le_pub`, `B45_P_vartheta_le` and
`B45_core_det_pub`; every other declaration is `private` and carries the prefix `B45_`.

* `B45_psum_le_pub`: the bound `jywiiwsoks` for `𝒫(𝓛-𝒦)`.
* `B45_P_vartheta_le`: the bound for `𝒫(𝓛-𝒦)ϑ`, as needed for the last step
  `𝓛-𝒦 = 𝒬(𝓛-𝒦) + (𝒫(𝓛-𝒦))ϑ` (`kolkisaf`).
* `B45_norm_vartheta_le_pub`, `B45_core_det_pub`: the bound on `ϑ` and the deterministic core for
  `ℬ₄`, `ℬ₅`.

## Proof

Fix `k ≥ 2`, `M = M_u`, `η = η_u`, `ℓ = ℓ_u`, `N = W²L²`, `R = ℓ W^{τ'}`, `𝒜 = (𝓛-𝒦)_{u,σ}`.

1. *Ward step* (`jywiiwsoks`).  For alternating `σ` there is a slot `j ≠ 0` with `(σ_j, σ_{j+1}) =
   (-,+)` (`j = 1` if `σ_0 = +`, `j = 2` if `σ_0 = -` and `k ≥ 4`), or `k = 2`.  Rotation
   invariance of `𝓛` and `𝒦` (`gloop_rotate`, `Kcal_rotate`) turns the last-label identities
   (`sum_gloop_ward_last_div`, `Kcal_ward`, `κ = (2iW²η)⁻¹`) into the interior identity
   `B45_ward_mid`; at `k = 2`, `σ = (-,+)` the slot is the last one with the reversed order, handled
   by `B45_sum_two_swap` (resolvents commute, `Kcal_two`).  So `Σ_{a_j} 𝒜_a = κ (𝒜_{σ∖σ_j, a∖a_j} -
   𝒜_{σ∖σ_{j+1}, a∖a_j})`, rank `k - 1`.
2. *Window count* (`B45_psum_le`).  Averaging over the slot `j` (`SumZeroQ_slot_succ` with `G ≡ 1`)
   gives `|(𝒫𝒜)_{a₀}| ≤ (W²η)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f)` if every rank-`(k-1)`
   entry is `≤ X` and those with two labels `≥ R` apart are `≤ B_f`.
3. *`ϑ̇`, `ϑ`, `ϴ`* (`eq:thetadot_bound`, `kkuuwsaf5`).  `|ϑ| ≤ c^{k-1}` and
   `|ϑ̇| ≤ 2(k-1)(1-u)⁻¹ c^{k-1}` with `c = C₅ (1 + log L) ℓ⁻²` (property 5 at `ξ = u`),
   `‖ϴ_{u,σ}‖_{∞→∞} ≤ k (1-u)⁻¹` (`ξ_i = m m̄ = 1`); the commutator formula of `qopAlgebra`
   (`SumZeroQ_commutator`) gives
   `|ℬ₄| ≤ 2k (1-u)⁻¹ c^{k-1} max|𝒫𝒜|`, and `|ℬ₅| ≤ max|𝒫𝒜| |ϑ̇|` (`B45_core_det`).
4. *Exponents* (used by the consumers of `B45_P_vartheta_le`).  `(W²η)⁻¹ = ℓ² M⁻¹` and
   `ℓ^{2+2(k-2)-2(k-1)} = 1`: the powers of `ℓ` cancel exactly.

The argument parallels the one-dimensional formalization, with the `d = 2` changes (`Z2 L`,
products over `univ.erase 0`, property 5 with the `(1 + log L)` loss, `ℓ_u` and `M_u` of `d = 2`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The bounds on `ϑ_t` and `ϑ̇_t` from property 5 -/

section Theta

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- The constant `C₅ = 180·40002²` of `norm_Theta_apply_le_prop5`. -/
private def B45_C5 : ℝ := 180 * 40002 ^ 2

private theorem B45_C5_pos : 0 < B45_C5 := by unfold B45_C5; positivity

/-- `‖1 - t‖ = 1 - t` for `t ≤ 1`. -/
private theorem B45_norm_one_sub {t : ℝ} (ht : t ≤ 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  have h : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- Property 5 at `ξ = t ∈ [0,1)` (`κ(t)² = 1 - t`, `ℓ̂(t) = ℓ_t`):
`(1-t)|Θ_t(x,y)| ≤ C₅(1+log L)ℓ_t^{-2}exp(-|x-y|_L/(20000ℓ_t))`. -/
private theorem B45_norm_Theta (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x y : Z2 L) :
    (1 - t) * ‖Theta L (t : ℂ) x y‖ ≤ B45_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹ *
      Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h5 := norm_Theta_apply_le_prop5 L hL (t : ℂ) hξ x y
  have hell : ellhat L (t : ℂ) = ellT L t := kloop_ellT_eq ht1.le
  have hkap : kappa (t : ℂ) ^ 2 = 1 - t := by
    rw [kappa_sq, B45_norm_one_sub ht1.le]
  rw [hell, hkap] at h5
  have h1t : 0 < 1 - t := by linarith
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  calc (1 - t) * ‖Theta L (t : ℂ) x y‖
      ≤ (1 - t) * (180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - t) * ellT L t ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t))) :=
        mul_le_mul_of_nonneg_left h5 h1t.le
    _ = B45_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
        unfold B45_C5
        rw [mul_inv]
        field_simp

/-- `‖ϑ_{t,a}‖ = Π_{i ≠ 0} (1-t)‖Θ_t(a₀,a_i)‖`. -/
private theorem B45_norm_vartheta_eq {t : ℝ} (ht1 : t < 1) (a : Fin k → Z2 L) :
    ‖vartheta L t a‖ = ∏ i ∈ Finset.univ.erase (0 : Fin k),
      ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖) := by
  unfold vartheta
  rw [norm_mul, norm_pow, norm_prod, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- The slot bound `c_L(t) = C₅(1+log L)ℓ_t^{-2}`. -/
private def B45_c (L : ℕ) (t : ℝ) : ℝ :=
  B45_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹

private theorem B45_c_nonneg (L : ℕ) (t : ℝ) : 0 ≤ B45_c L t := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  unfold B45_c
  exact mul_nonneg (mul_nonneg B45_C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))

/-- The slot bound in the form `(1-t)‖Θ_t(x,y)‖ ≤ c_L(t)`. -/
private theorem B45_slot_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : Z2 L) :
    (1 - t) * ‖Theta L (t : ℂ) x y‖ ≤ B45_c L t := by
  refine (B45_norm_Theta hL ht0 ht1 x y).trans ?_
  unfold B45_c
  refine mul_le_of_le_one_right ?_ (Real.exp_le_one_iff.mpr ?_)
  · have hlog : 0 ≤ 1 + Real.log L := by
      have := Real.log_natCast_nonneg L
      linarith
    exact mul_nonneg (mul_nonneg B45_C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))
  · have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht1).1
    exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)

/-- `|ϑ_{t,a}| ≤ c^{k-1}`. -/
private theorem B45_norm_vartheta_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin k → Z2 L) : ‖vartheta L t a‖ ≤ B45_c L t ^ (k - 1) := by
  rw [B45_norm_vartheta_eq ht1]
  calc ∏ i ∈ Finset.univ.erase (0 : Fin k), ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖)
      ≤ ∏ _i ∈ Finset.univ.erase (0 : Fin k), B45_c L t := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · exact mul_nonneg (by linarith) (norm_nonneg _)
        · exact B45_slot_le hL ht0 ht1 _ _
    _ = B45_c L t ^ (k - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]

open scoped Matrix.Norms.Operator in
/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
private theorem B45_sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

open scoped Matrix.Norms.Operator in
/-- The row `ℓ¹` sums of `Θ_t S` are at most `(1-t)⁻¹`. -/
private theorem B45_row_TS_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x : Z2 L) :
    ∑ e : Z2 L, ‖(Theta L (t : ℂ) * SB L) x e‖ ≤ (1 - t)⁻¹ := by
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  refine (B45_sum_norm_row_le_opNorm _ x).trans ?_
  calc ‖Theta L (t : ℂ) * SB L‖ ≤ ‖Theta L (t : ℂ)‖ * ‖SB L‖ := norm_mul_le _ _
    _ = ‖Theta L (t : ℂ)‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖(t : ℂ)‖)⁻¹ := norm_Theta_le L hL hξ
    _ = (1 - t)⁻¹ := by rw [hn]

/-- `(1-t)²|(Θ_t S Θ_t)(x,y)| ≤ c_L(t)`: `Σ_e |(ΘS)(x,e)| ≤ (1-t)⁻¹` and
`max_e |Θ(e,y)| ≤ (1-t)⁻¹ c`. -/
private theorem B45_norm_TST (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : Z2 L) :
    (1 - t) ^ 2 * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y‖ ≤ B45_c L t := by
  have h1t : 0 < 1 - t := by linarith
  have hslot : ∀ e : Z2 L, ‖Theta L (t : ℂ) e y‖ ≤ (1 - t)⁻¹ * B45_c L t := fun e => by
    rw [inv_mul_eq_div, le_div_iff₀ h1t, mul_comm]
    exact B45_slot_le hL ht0 ht1 e y
  have hc0 : 0 ≤ B45_c L t := B45_c_nonneg L t
  have hrow := B45_row_TS_le hL ht0 ht1 x
  calc (1 - t) ^ 2 * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y‖
      = (1 - t) ^ 2 * ‖∑ e : Z2 L, (Theta L (t : ℂ) * SB L) x e * Theta L (t : ℂ) e y‖ := by
        rw [Matrix.mul_apply]
    _ ≤ (1 - t) ^ 2 * ∑ e : Z2 L, ‖(Theta L (t : ℂ) * SB L) x e‖ * ((1 - t)⁻¹ * B45_c L t) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        refine Finset.sum_le_sum fun e _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hslot e) (norm_nonneg _)
    _ = (1 - t) ^ 2 * ((∑ e : Z2 L, ‖(Theta L (t : ℂ) * SB L) x e‖) * ((1 - t)⁻¹ * B45_c L t)) := by
        rw [Finset.sum_mul]
    _ ≤ (1 - t) ^ 2 * ((1 - t)⁻¹ * ((1 - t)⁻¹ * B45_c L t)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hrow (by positivity)
    _ = B45_c L t := by field_simp

/-- `Π_{i ∈ S} (1-t)‖Θ_i‖ = (1-t)^{|S|} Π_{i ∈ S} ‖Θ_i‖`. -/
private theorem B45_prod_mul (S : Finset (Fin k)) (t : ℝ) (f : Fin k → ℝ) :
    ∏ i ∈ S, ((1 - t) * f i) = (1 - t) ^ S.card * ∏ i ∈ S, f i := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **`eq:thetadot_bound`**: `‖ϑ̇_{t,a}‖ ≤ 2(k-1)(1-t)⁻¹ c^{k-1}`, from the closed form of
`ϑ̇` (`SumZeroQ_varthetaDot_eq`) and property 5 (with the `d = 2` slot bound `c`). -/
private theorem B45_norm_varthetaDot_le (hL : 3 ≤ L) (hk : 2 ≤ k) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a : Fin k → Z2 L) :
    ‖varthetaDot L t a‖ ≤ 2 * ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  have hc0 : 0 ≤ B45_c L t := B45_c_nonneg L t
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hkk : k - 1 = (k - 2) + 1 := by omega
  rw [SumZeroQ_varthetaDot_eq hL hk ht a]
  refine (norm_add_le _ _).trans ?_
  set S0 : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hS0
  have hcardS0 : S0.card = k - 1 := by
    rw [hS0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- term 1
  have hvt : (1 - t) ^ (k - 1) * ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖ ≤ B45_c L t ^ (k - 1) := by
    have h := B45_norm_vartheta_le (k := k) hL ht0 ht1 a
    rw [B45_norm_vartheta_eq ht1, B45_prod_mul (Finset.univ.erase (0 : Fin k))] at h
    have hc : (Finset.univ.erase (0 : Fin k)).card = k - 1 := hcardS0
    rw [hc] at h
    exact h
  have T1 : ‖-((k - 1 : ℕ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ (k - 2) *
      ∏ i ∈ S0, Theta L (t : ℂ) (a 0) (a i)‖ ≤ ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by
    rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_prod, Complex.norm_real,
      Real.norm_of_nonneg h1t.le, Complex.norm_natCast, hk1]
    have e : (1 - t) ^ (k - 2) * ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖ =
        (1 - t)⁻¹ * ((1 - t) ^ (k - 1) * ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖) := by
      rw [hkk, pow_succ]; field_simp
    calc ((k : ℝ) - 1) * (1 - t) ^ (k - 2) * ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖
        = ((k : ℝ) - 1) * ((1 - t) ^ (k - 2) * ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖) := by ring
      _ = ((k : ℝ) - 1) * ((1 - t)⁻¹ * ((1 - t) ^ (k - 1) *
            ∏ i ∈ S0, ‖Theta L (t : ℂ) (a 0) (a i)‖)) := by rw [e]
      _ ≤ ((k : ℝ) - 1) * ((1 - t)⁻¹ * B45_c L t ^ (k - 1)) := by
          have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
            have : (2 : ℝ) ≤ k := by exact_mod_cast hk
            linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvt (inv_nonneg.2 h1t.le)) hk0
      _ = ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by ring
  -- term 2
  have hj : ∀ j ∈ S0, (1 - t) ^ (k - 1) *
      (‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)‖ *
        ∏ i ∈ S0.erase j, ‖Theta L (t : ℂ) (a 0) (a i)‖) ≤ (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by
    intro j hjS
    have hcard : (S0.erase j).card = k - 2 := by
      rw [Finset.card_erase_of_mem hjS, hcardS0]; omega
    have hpr : ∏ i ∈ S0.erase j, ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖) ≤
        B45_c L t ^ (k - 2) := by
      calc ∏ i ∈ S0.erase j, ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖)
          ≤ ∏ _i ∈ S0.erase j, B45_c L t :=
            Finset.prod_le_prod₀ (fun i _ => mul_nonneg h1t.le (norm_nonneg _))
              (fun i _ => B45_slot_le hL ht0 ht1 _ _)
        _ = B45_c L t ^ (k - 2) := by rw [Finset.prod_const, hcard]
    have hts := B45_norm_TST hL ht0 ht1 (a 0) (a j)
    have e : (1 - t) ^ (k - 1) * (‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)‖ *
        ∏ i ∈ S0.erase j, ‖Theta L (t : ℂ) (a 0) (a i)‖) =
        ((1 - t)⁻¹ * ((1 - t) ^ 2 * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)‖)) *
          ∏ i ∈ S0.erase j, ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖) := by
      rw [B45_prod_mul, hcard, hkk, pow_succ]
      field_simp
    rw [e]
    have hq : 0 ≤ ∏ i ∈ S0.erase j, ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖) :=
      Finset.prod_nonneg fun i _ => mul_nonneg h1t.le (norm_nonneg _)
    calc ((1 - t)⁻¹ * ((1 - t) ^ 2 * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)‖)) *
          ∏ i ∈ S0.erase j, ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖)
        ≤ ((1 - t)⁻¹ * B45_c L t) * B45_c L t ^ (k - 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hts (inv_nonneg.2 h1t.le)) hpr hq
            (mul_nonneg (inv_nonneg.2 h1t.le) hc0)
      _ = (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by rw [hkk, pow_succ]; ring
  have T2 : ‖((1 - t : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ S0,
      (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
        ∏ i ∈ S0.erase j, Theta L (t : ℂ) (a 0) (a i)‖ ≤
      ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h1t.le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    calc ∑ j ∈ S0, (1 - t) ^ (k - 1) * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
            ∏ i ∈ S0.erase j, Theta L (t : ℂ) (a 0) (a i)‖
        = ∑ j ∈ S0, (1 - t) ^ (k - 1) *
            (‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)‖ *
              ∏ i ∈ S0.erase j, ‖Theta L (t : ℂ) (a 0) (a i)‖) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_prod]
      _ ≤ ∑ _j ∈ S0, (1 - t)⁻¹ * B45_c L t ^ (k - 1) := Finset.sum_le_sum hj
      _ = ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by
          rw [Finset.sum_const, hcardS0, nsmul_eq_mul, hk1]; ring
  calc _ ≤ ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) +
        ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := add_le_add T1 T2
    _ = 2 * ((k : ℝ) - 1) * (1 - t)⁻¹ * B45_c L t ^ (k - 1) := by ring

end Theta

/-! ## 2. The Ward identity for `𝓛 - 𝒦` at an interior label -/

section Ward

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Single-step rotation invariance of a loop function. -/
private def B45_RotInv (F : LoopIdx (Z2 L) → ℂ) : Prop :=
  ∀ (s : Bool) (b : Z2 L) (σ : List Bool) (a : List (Z2 L)), σ.length = a.length →
    F ⟨s :: σ, b :: a⟩ = F ⟨σ ++ [s], a ++ [b]⟩

/-- Rotation of a block, from the single-step rotation. -/
private theorem B45_rot_block {F : LoopIdx (Z2 L) → ℂ} (hF : B45_RotInv F) :
    ∀ (σ₁ : List Bool) (a₁ : List (Z2 L)), σ₁.length = a₁.length →
    ∀ (σ₂ : List Bool) (a₂ : List (Z2 L)), σ₂.length = a₂.length →
      F ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ = F ⟨σ₂ ++ σ₁, a₂ ++ a₁⟩ := by
  intro σ₁
  induction σ₁ with
  | nil =>
    intro a₁ h₁ σ₂ a₂ h₂
    have : a₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h₁.symm)
    subst this
    simp
  | cons s σ ih =>
    intro a₁ h₁ σ₂ a₂ h₂
    cases a₁ with
    | nil => simp at h₁
    | cons b a =>
      have h : σ.length = a.length := by simpa using h₁
      have e1 := hF s b (σ ++ σ₂) (a ++ a₂) (by simp [h, h₂])
      have e2 := ih a h (σ₂ ++ [s]) (a₂ ++ [b]) (by simp [h₂])
      simp only [List.cons_append, List.append_assoc] at e1 e2 ⊢
      rw [e1, e2]
      simp

/-- The Ward identity at the last label (first sign `+`, last sign `-`). -/
private def B45_WardLast (F : LoopIdx (Z2 L) → ℂ) (κ : ℂ) : Prop :=
  ∀ (μ : List Bool) (x : Z2 L) (a' : List (Z2 L)), μ.length = a'.length →
    ∑ b : Z2 L, F ⟨true :: μ ++ [false], x :: a' ++ [b]⟩ =
      κ * (F ⟨true :: μ, x :: a'⟩ - F ⟨false :: μ, x :: a'⟩)

/-- The Ward identity at an interior label between `-` and `+`, from rotation invariance and the
last-label identity. -/
private theorem B45_ward_mid {F : LoopIdx (Z2 L) → ℂ} {κ : ℂ} (hF : B45_RotInv F)
    (hW : B45_WardLast F κ) (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L))
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) (c : Z2 L) :
    ∑ b : Z2 L, F ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩ =
      κ * (F ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩ - F ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) := by
  have hrot : ∀ b : Z2 L, F ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩ =
      F ⟨true :: (σ₂ ++ σ₁) ++ [false], c :: (a₂ ++ a₁) ++ [b]⟩ := by
    intro b
    have e1 := B45_rot_block hF σ₁ a₁ h₁ (false :: true :: σ₂) (b :: c :: a₂) (by simp [h₂])
    rw [e1]
    have e2 := hF false b (true :: (σ₂ ++ σ₁)) (c :: (a₂ ++ a₁)) (by simp [h₁, h₂])
    simp only [List.cons_append] at e2 ⊢
    exact e2
  simp_rw [hrot]
  have hlen : (σ₂ ++ σ₁).length = (a₂ ++ a₁).length := by simp [h₁, h₂]
  rw [hW (σ₂ ++ σ₁) c (a₂ ++ a₁) hlen]
  have e3 := B45_rot_block hF σ₁ a₁ h₁ (true :: σ₂) (c :: a₂) (by simp [h₂])
  have e4 := B45_rot_block hF σ₁ a₁ h₁ (false :: σ₂) (c :: a₂) (by simp [h₂])
  simp only [List.cons_append] at e3 e4 ⊢
  rw [e3, e4]

/-- Two resolvents of the same matrix commute. -/
private theorem B45_green_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z w : ℂ) : green H z * green H w = green H w * green H z := by
  unfold green
  rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev]
  congr 1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul]
  rw [mul_comm z w]
  abel

/-- `𝓛 - 𝒦` is invariant under the rotation of a loop. -/
private theorem B45_rotInv_LKf (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    B45_RotInv (LKf L W E u M) := by
  intro s b σ a h
  unfold LKf LLf
  rw [gloop_rotate s b h, KLoop.Kcal_rotate L W hL hW E hE u ⟨hu0, hu1⟩ s b σ a h]

/-- `Im z_u = η_u`, and `z_u` is not real. -/
private theorem B45_zim {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) :
    (spectralZ E u).im = etaT E u ∧ (spectralZ E u).im ≠ 0 := by
  have h1 : (spectralZ E u).im = etaT E u := spectralZ_im E u
  exact ⟨h1, by rw [h1]; exact (etaT_pos hE hu1).ne'⟩

/-- The last-label Ward identity for `𝓛 - 𝒦` (`sum_gloop_ward_last_div` and `Kcal_ward`),
`κ = (2 i W² η_u)⁻¹`. -/
private theorem B45_wardLast_LKf (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) :
    B45_WardLast (LKf L W E u M) ((2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹) := by
  intro μ x a' hμ
  obtain ⟨hzim, hz⟩ := B45_zim hE hu1
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hz' : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by
    rw [Complex.conj_im]; exact neg_ne_zero.mpr hz
  have h1 := sum_gloop_ward_last_div L W (H := blockMat M) (z := spectralZ E u)
    (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz)
    (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz') hz μ x a' hμ
  have h2 := KLoop.Kcal_ward L W hL hW E hE u ⟨hu0, hu1⟩ μ (x :: a') (by simp [hμ])
  unfold LKf LLf
  rw [Finset.sum_sub_distrib, h1, h2, kloop_etaT_eq, hzim, div_eq_inv_mul]
  ring

/-- The interior Ward identity for `𝓛 - 𝒦`. -/
private theorem B45_ward_mid_LKf (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Z2 L)) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) (c : Z2 L) :
    ∑ b : Z2 L, LKf L W E u M ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩ -
          LKf L W E u M ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) :=
  B45_ward_mid (B45_rotInv_LKf hL hW hE hu0 hu1 M) (B45_wardLast_LKf hL hW hE hu0 hu1 hM)
    σ₁ σ₂ a₁ a₂ h₁ h₂ c

/-- At rank `2` the two sign orders give the same slot sum: `Σ_x 𝓛_{(-,+),(a,x)} =
Σ_x 𝓛_{(+,-),(a,x)}` (resolvents commute), and `𝒦_{(-,+)} = 𝒦_{(+,-)}` (`Kcal_two`). -/
private theorem B45_sum_two_swap {E u : ℝ} (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, LKf L W E u M ⟨[true, false], [a, x]⟩ := by
  have hr1 : ∀ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [a, x]⟩ =
      gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [x, a]⟩ := fun x =>
    gloop_rotate (H := blockMat M) (z := spectralZ E u) false a (σ := [true]) (a := [x]) rfl
  have hr2 : ∀ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [a, x]⟩ =
      gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [x, a]⟩ := fun x =>
    gloop_rotate (H := blockMat M) (z := spectralZ E u) true a (σ := [false]) (a := [x]) rfl
  have hg : ∑ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [a, x]⟩ := by
    rw [Finset.sum_congr rfl (fun x _ => hr1 x), Finset.sum_congr rfl (fun x _ => hr2 x),
      sum_gloop_head true [false] [a], sum_gloop_head false [true] [a]]
    simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true, Gsig_false]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      B45_green_comm (blockMat M) (spectralZ E u) ((starRingEnd ℂ) (spectralZ E u))]
  have hk : ∑ x : Z2 L, KLoop.Kcal L W E u ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, KLoop.Kcal L W E u ⟨[true, false], [a, x]⟩ := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [KLoop.Kcal_two, KLoop.Kcal_two, mul_comm (KLoop.mSig E false) (KLoop.mSig E true)]
  unfold LKf LLf
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hg, hk]

/-- **Rank `2`, `σ = (-,+)`**: `Σ_x (𝓛-𝒦)_{(-,+),(a,x)} = κ ((𝓛-𝒦)_{(+),(a)} - (𝓛-𝒦)_{(-),(a)})`. -/
private theorem B45_ward_two_ft (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M ⟨[false, true], [a, x]⟩ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨[true], [a]⟩ - LKf L W E u M ⟨[false], [a]⟩) := by
  rw [B45_sum_two_swap]
  exact B45_wardLast_LKf hL hW hE hu0 hu1 hM [] a [] rfl

/-- **Rank `2`, `σ = (+,-)`**. -/
private theorem B45_ward_two_tf (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M ⟨[true, false], [a, x]⟩ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨[true], [a]⟩ - LKf L W E u M ⟨[false], [a]⟩) :=
  B45_wardLast_LKf hL hW hE hu0 hu1 hM [] a [] rfl

end Ward

/-! ## 3. The slot sum `𝒫(𝓛-𝒦)`: the Ward step, then the window count -/

section Slot

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Splitting a list at a position `j` with `j + 1 < length`. -/
private theorem B45_split {α : Type*} (l : List α) (j : ℕ) (hj : j + 1 < l.length) :
    l = l.take j ++ l[j] :: l[j + 1] :: l.drop (j + 2) := by
  conv_lhs => rw [← List.take_append_drop j l]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]

/-- The list of a tuple with one entry replaced. -/
private theorem B45_ofFn_update {α : Type*} {k : ℕ} (a : Fin k → α) (j : ℕ) (hj : j + 1 < k)
    (x : α) :
    List.ofFn (Function.update a ⟨j, by omega⟩ x) =
      (List.ofFn a).take j ++ x :: a ⟨j + 1, hj⟩ :: (List.ofFn a).drop (j + 2) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hik : i < k := by simpa using h1
    simp only [List.getElem_ofFn]
    have hmin : min j k = j := by omega
    rcases lt_trichotomy i j with h | h | h
    · rw [List.getElem_append_left (by simp; omega)]
      simp [Function.update_of_ne, Fin.ext_iff, h.ne]
    · subst h
      rw [List.getElem_append_right (by simp)]
      simp [hmin]
    · rw [List.getElem_append_right (by simp; omega)]
      have hlen : (List.take j (List.ofFn a)).length = j := by simp [hmin]
      simp only [hlen]
      rcases Nat.lt_or_ge i (j + 2) with h3 | h3
      · have hi : i = j + 1 := by omega
        subst hi
        simp [Function.update_of_ne, Fin.ext_iff]
      · obtain ⟨m, hm⟩ : ∃ m, i - j = m + 2 := ⟨i - j - 2, by omega⟩
        have h4 : i ≠ j := by omega
        simp only [hm, List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn]
        simp only [ne_eq, Fin.ext_iff, h4, not_false_eq_true, Function.update_of_ne]
        congr 1
        exact Fin.ext (by simp only []; omega)

/-- **The Ward step at an interior slot `j`** (`1 ≤ j`, `j + 1 < k`, `σ_j = -`, `σ_{j+1} = +`):
`Σ_x (𝓛-𝒦)_{σ, a^{(j)}_x} = κ ((𝓛-𝒦)_{σ∖σ_j, a∖a_j} - (𝓛-𝒦)_{σ∖σ_{j+1}, a∖a_j})`, the loops of rank
`k - 1` obtained by deleting the slot `j` of the labels and one of the two signs. -/
private theorem B45_ward_slot_mid (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) (j : ℕ) (hjk : j + 1 < k)
    (hF : σ ⟨j, by omega⟩ = false) (hT : σ ⟨j + 1, hjk⟩ = true) :
    ∑ x : Z2 L, LKf L W E u M (loopOf σ (Function.update a ⟨j, by omega⟩ x)) =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨(List.ofFn σ).eraseIdx j, (List.ofFn a).eraseIdx j⟩ -
          LKf L W E u M ⟨(List.ofFn σ).eraseIdx (j + 1), (List.ofFn a).eraseIdx j⟩) := by
  obtain ⟨σ₁, σ₂, hσ', hσ₁, hσ₂⟩ : ∃ σ₁ σ₂ : List Bool,
      List.ofFn σ = σ₁ ++ false :: true :: σ₂ ∧ σ₁.length = j ∧ σ₂.length = k - (j + 2) := by
    have h := B45_split (List.ofFn σ) j (by simpa using hjk)
    simp only [List.getElem_ofFn, hF, hT] at h
    refine ⟨(List.ofFn σ).take j, (List.ofFn σ).drop (j + 2), h, ?_, ?_⟩
    · simp; omega
    · simp
  obtain ⟨a₁, a₂, c, haU, hae, ha₁, ha₂⟩ : ∃ (a₁ a₂ : List (Z2 L)) (c : Z2 L),
      (∀ x, List.ofFn (Function.update a ⟨j, by omega⟩ x) = a₁ ++ x :: c :: a₂) ∧
      (List.ofFn a).eraseIdx j = a₁ ++ c :: a₂ ∧ a₁.length = j ∧ a₂.length = k - (j + 2) := by
    refine ⟨(List.ofFn a).take j, (List.ofFn a).drop (j + 2), a ⟨j + 1, hjk⟩,
      fun x => B45_ofFn_update a j hjk x, ?_, ?_, ?_⟩
    · rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons (by simpa using hjk)]
      simp
    · simp; omega
    · simp
  have e1 : (σ₁ ++ false :: true :: σ₂).eraseIdx j = σ₁ ++ true :: σ₂ := by
    rw [List.eraseIdx_append_of_length_le (by omega), hσ₁]
    simp
  have e2 : (σ₁ ++ false :: true :: σ₂).eraseIdx (j + 1) = σ₁ ++ false :: σ₂ := by
    rw [List.eraseIdx_append_of_length_le (by omega), hσ₁]
    simp
  rw [hσ', e1, e2, hae]
  simp only [loopOf, haU, hσ']
  exact B45_ward_mid_LKf hL hW hE hu0 hu1 hM σ₁ σ₂ a₁ a₂ (by rw [hσ₁, ha₁]) (by rw [hσ₂, ha₂]) c

/-- Alternation at consecutive naturals. -/
private theorem B45_alt_nat {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool}
    (hσ : Alternating σ) : ∀ (i : ℕ) (hi : i + 1 < k), σ ⟨i + 1, hi⟩ = !σ ⟨i, by omega⟩ := by
  intro i hi
  have h := hσ ⟨i, by omega⟩
  have e : (⟨i, by omega⟩ : Fin k) + 1 = ⟨i + 1, hi⟩ := by
    apply Fin.ext
    rw [Fin.val_add]
    have h1 : (1 : Fin k).val = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    simp only [h1]
    exact Nat.mod_eq_of_lt hi
  rwa [e] at h

/-- The rank-`2` case of `B45_ward_slot` (stated at `Fin 2`, where `decide` applies). -/
private theorem B45_ward_slot_two (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) :
    ∃ j : Fin 2, j ≠ 0 ∧ ∃ Jp Jm : (Fin 2 → Z2 L) → LoopIdx (Z2 L),
      (∀ a, (Jp a).WF ∧ (Jp a).length = 2 - 1 ∧ ∀ i : Fin 2, i ≠ j → a i ∈ (Jp a).a) ∧
      (∀ a, (Jm a).WF ∧ (Jm a).length = 2 - 1 ∧ ∀ i : Fin 2, i ≠ j → a i ∈ (Jm a).a) ∧
      ∀ a, ∑ x : Z2 L, LKf L W E u M (loopOf σ (Function.update a j x)) =
        (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
          (LKf L W E u M (Jp a) - LKf L W E u M (Jm a)) := by
  have h01 : σ 1 = !σ 0 := by
    have := hσ 0
    simpa using this
  refine ⟨1, by decide, fun a => ⟨[true], [a 0]⟩, fun a => ⟨[false], [a 0]⟩, ?_, ?_, ?_⟩
  · intro a
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    fin_cases i
    · simp
    · exact absurd rfl hi
  · intro a
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    fin_cases i
    · simp
    · exact absurd rfl hi
  · intro a
    have hl : ∀ x : Z2 L, loopOf σ (Function.update a 1 x) = ⟨[σ 0, σ 1], [a 0, x]⟩ := by
      intro x
      simp [loopOf, List.ofFn_succ, Function.update_of_ne]
    simp_rw [hl]
    cases h0 : σ 0
    · have h1 : σ 1 = true := by rw [h01, h0]; rfl
      rw [h1]
      exact B45_ward_two_ft hL hW hE hu0 hu1 hM (a 0)
    · have h1 : σ 1 = false := by rw [h01, h0]; rfl
      rw [h1]
      exact B45_ward_two_tf hL hW hE hu0 hu1 hM (a 0)

/-- **The Ward step for an alternating `σ`** (`jywiiwsoks`): there is a slot `j ≠ 0` such
that the slot sum of `𝓛 - 𝒦` over `a_j` is `κ` times the difference of two `𝓛 - 𝒦` loops of rank
`k - 1`, whose label lists contain every `a_i`, `i ≠ j`.  For `k ≥ 3` this is an interior slot
(`j = 1` if `σ_0 = +`, `j = 2` if `σ_0 = -`, `σ` being alternating); for `k = 2` it is the last
label, by the last-label identity (`σ = (+,-)`) or `B45_ward_two_ft` (`σ = (-,+)`). -/
private theorem B45_ward_slot (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ) :
    ∃ j : Fin k, j ≠ 0 ∧ ∃ Jp Jm : (Fin k → Z2 L) → LoopIdx (Z2 L),
      (∀ a, (Jp a).WF ∧ (Jp a).length = k - 1 ∧ ∀ i : Fin k, i ≠ j → a i ∈ (Jp a).a) ∧
      (∀ a, (Jm a).WF ∧ (Jm a).length = k - 1 ∧ ∀ i : Fin k, i ≠ j → a i ∈ (Jm a).a) ∧
      ∀ a, ∑ x : Z2 L, LKf L W E u M (loopOf σ (Function.update a j x)) =
        (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
          (LKf L W E u M (Jp a) - LKf L W E u M (Jm a)) := by
  have hσn := B45_alt_nat hk hσ
  by_cases hk2 : k = 2
  · subst hk2
    exact B45_ward_slot_two hL hW hE hu0 hu1 hM hσ
  · have hk3 : 3 ≤ k := by omega
    obtain ⟨j, hjk, hj1, hF, hT⟩ : ∃ j : ℕ, ∃ hjk : j + 1 < k, 1 ≤ j ∧
        σ ⟨j, by omega⟩ = false ∧ σ ⟨j + 1, hjk⟩ = true := by
      have h0 := hσn 0 (by omega)
      cases hs0 : σ ⟨0, by omega⟩
      · -- `σ_0 = -`: `σ_1 = +`, `σ_2 = -`, `σ_3 = +` (needs `k ≥ 4`)
        have hs1 : σ ⟨1, by omega⟩ = true := by rw [h0, hs0]; rfl
        have hs2 : σ ⟨2, by omega⟩ = false := by rw [hσn 1 (by omega), hs1]; rfl
        by_cases hk4 : 3 < k
        · exact ⟨2, by omega, by omega, hs2, by rw [hσn 2 (by omega), hs2]; rfl⟩
        · exfalso
          have hk3' : k = 3 := by omega
          have hw := hσ ⟨2, by omega⟩
          have e : (⟨2, by omega⟩ : Fin k) + 1 = ⟨0, by omega⟩ := by
            apply Fin.ext
            rw [Fin.val_add]
            have h1 : (1 : Fin k).val = 1 := by
              rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
            simp only [h1]
            rw [hk3']
          rw [e, hs0, hs2] at hw
          exact absurd hw (by decide)
      · -- `σ_0 = +`: `σ_1 = -`, `σ_2 = +`
        have hs1 : σ ⟨1, by omega⟩ = false := by rw [h0, hs0]; rfl
        exact ⟨1, by omega, le_rfl, hs1, by rw [hσn 1 (by omega), hs1]; rfl⟩
    have hjk' : j < k := by omega
    have hlen_σ : ∀ i : ℕ, i < k → ((List.ofFn σ).eraseIdx i).length = k - 1 := by
      intro i hi
      rw [List.length_eraseIdx_of_lt (by simpa using hi)]
      simp
    have hlen_a : ∀ (b : Fin k → Z2 L) (i : ℕ), i < k → ((List.ofFn b).eraseIdx i).length = k - 1 := by
      intro b i hi
      rw [List.length_eraseIdx_of_lt (by simpa using hi)]
      simp
    refine ⟨⟨j, hjk'⟩, ?_, fun a => ⟨(List.ofFn σ).eraseIdx j, (List.ofFn a).eraseIdx j⟩,
      fun a => ⟨(List.ofFn σ).eraseIdx (j + 1), (List.ofFn a).eraseIdx j⟩, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · intro a
      refine ⟨?_, ?_, fun i hi => ?_⟩
      · dsimp only [LoopIdx.WF]
        rw [hlen_σ j hjk', hlen_a a j hjk']
      · dsimp only [LoopIdx.length]
        exact hlen_a a j hjk'
      · exact List.mem_eraseIdx_iff_getElem.2 ⟨i, by simp, fun h => hi (Fin.ext h), by simp⟩
    · intro a
      refine ⟨?_, ?_, fun i hi => ?_⟩
      · dsimp only [LoopIdx.WF]
        rw [hlen_σ (j + 1) hjk, hlen_a a j hjk']
      · dsimp only [LoopIdx.length]
        exact hlen_a a j hjk'
      · exact List.mem_eraseIdx_iff_getElem.2 ⟨i, by simp, fun h => hi (Fin.ext h), by simp⟩
    · intro a
      exact B45_ward_slot_mid hL hW hE hu0 hu1 hM σ a j hjk hF hT

/-- `‖κ‖ = (2 W² η)⁻¹` for `κ = (2 i W² η)⁻¹`. -/
private theorem B45_norm_kappa {η : ℝ} (hη : 0 < η) :
    ‖(2 * Complex.I * (W : ℂ) ^ 2 * (η : ℂ))⁻¹‖ = (2 * (W : ℝ) ^ 2 * η)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
    Complex.norm_natCast, Real.norm_of_nonneg hη.le]
  simp

/-- **The window count for `𝒫(𝓛-𝒦)_{a₀}` after the Ward step** (`jywiiwsoks`):
`|[𝒫(𝓛-𝒦)_{u,σ}]_{a₀}| ≤ (W²η_u)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_far)` for alternating `σ`, if
every well-formed rank-`(k-1)` loop has `|𝓛-𝒦| ≤ X` and those with two labels `≥ R` apart have
`|𝓛-𝒦| ≤ B_far`. -/
private theorem B45_psum_le (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ)
    {R X Bf : ℝ} (hR : 0 ≤ R) (hX0 : 0 ≤ X) (hBf0 : 0 ≤ Bf)
    (hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 → ‖LKf L W E u M J‖ ≤ X)
    (hBf : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) → ‖LKf L W E u M J‖ ≤ Bf)
    (a₀ : Z2 L) :
    ‖Psum L (lkTensor L W E u M σ) a₀‖ ≤
      ((W : ℝ) ^ 2 * etaT E u)⁻¹ *
        (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf) := by
  classical
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  obtain ⟨j, hj0, Jp, Jm, hJp, hJm, hward⟩ := B45_ward_slot hL hW hE hu0 hu1 hM hk hσ
  set F : Finset (Fin k → Z2 L) := Finset.univ.filter (fun a => a 0 = a₀) with hF
  set S0 : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hS0
  have hjS0 : j ∈ S0 := Finset.mem_erase.2 ⟨hj0, Finset.mem_univ _⟩
  have hcardS0 : S0.card = k - 1 := by
    rw [hS0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- averaging over the slot `j` (`SumZeroQ_slot_succ` with `G ≡ 1`)
  have hav := SumZeroQ_slot_succ (k := k) hj0 (fun _ _ => (1 : ℂ)) (lkTensor L W E u M σ) a₀
  have hL2 : ((L : ℂ) ^ 2) * Psum L (lkTensor L W E u M σ) a₀ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        ∑ a ∈ F, (LKf L W E u M (Jp a) - LKf L W E u M (Jm a)) := by
    have e1 : ∀ a : Fin k → Z2 L, ∑ b : Z2 L, (1 : ℂ) * lkTensor L W E u M σ (Function.update a j b) =
        (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
          (LKf L W E u M (Jp a) - LKf L W E u M (Jm a)) := fun a => by
      simp only [one_mul, lkTensor]
      exact hward a
    have e2 : ∀ a : Fin k → Z2 L, (∑ c : Z2 L, (1 : ℂ)) * lkTensor L W E u M σ a =
        ((L : ℂ) ^ 2) * lkTensor L W E u M σ a := fun a => by
      simp [Fintype.card_prod, ZMod.card, sq]
    simp only [e1, e2] at hav
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hav
    rw [Psum]
    simp only [hF]
    exact hav.symm
  -- the ball indicator around `a₀`, the slot `j` unconstrained
  set g : Fin k → Z2 L → ℝ := fun i b =>
    if i = j then 1 else if (zdist2 L (a₀ - b) : ℝ) ≤ R then 1 else 0 with hg
  have hg0 : ∀ i b, 0 ≤ g i b := fun i b => by
    simp only [hg]; split_ifs <;> norm_num
  -- pointwise bound
  have hpt : ∀ a ∈ F, ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∀ i : Fin k, i ≠ j → a i ∈ J.a) →
      ‖LKf L W E u M J‖ ≤ X * ∏ i ∈ S0, g i (a i) + Bf := by
    intro a ha J hJwf hJlen hJmem
    have ha0 : a 0 = a₀ := (Finset.mem_filter.mp ha).2
    have hprod0 : 0 ≤ ∏ i ∈ S0, g i (a i) := Finset.prod_nonneg fun i _ => hg0 i _
    by_cases hall : ∀ i ∈ S0, i ≠ j → (zdist2 L (a₀ - a i) : ℝ) ≤ R
    · have h1 : ∏ i ∈ S0, g i (a i) = 1 :=
        Finset.prod_eq_one fun i hi => by
          by_cases hij : i = j
          · simp [hg, hij]
          · simp [hg, hij, hall i hi hij]
      rw [h1, mul_one]
      linarith [hX J hJwf hJlen]
    · push Not at hall
      obtain ⟨i, hi, hij, hlt⟩ := hall
      have hfar : ‖LKf L W E u M J‖ ≤ Bf := by
        refine hBf J hJwf hJlen ⟨a 0, hJmem 0 (Ne.symm hj0), a i, hJmem i hij, ?_⟩
        rw [ha0]; exact hlt.le
      have : 0 ≤ X * ∏ i ∈ S0, g i (a i) := mul_nonneg hX0 hprod0
      linarith
  -- sum over `a ∈ F`
  have hsum1 : ∑ a ∈ F, (‖LKf L W E u M (Jp a)‖ + ‖LKf L W E u M (Jm a)‖) ≤
      2 * (X * ∑ a ∈ F, ∏ i ∈ S0, g i (a i) + (F.card : ℝ) * Bf) := by
    calc ∑ a ∈ F, (‖LKf L W E u M (Jp a)‖ + ‖LKf L W E u M (Jm a)‖)
        ≤ ∑ a ∈ F, (2 * (X * ∏ i ∈ S0, g i (a i)) + 2 * Bf) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have h1 := hpt a ha (Jp a) (hJp a).1 (hJp a).2.1 (hJp a).2.2
          have h2 := hpt a ha (Jm a) (hJm a).1 (hJm a).2.1 (hJm a).2.2
          linarith
      _ = 2 * (X * ∑ a ∈ F, ∏ i ∈ S0, g i (a i) + (F.card : ℝ) * Bf) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul]
          ring
  -- the product of sums
  have hprodsum : ∑ a ∈ F, ∏ i ∈ S0, g i (a i) = ∏ i ∈ S0, ∑ b : Z2 L, g i b :=
    SumZeroQ_sum_filter_prod a₀ g
  have hball : ∀ i ∈ S0.erase j, ∑ b : Z2 L, g i b ≤ (2 * R + 1) ^ 2 := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have := KLoop.card_ball_le L a₀ R hR
    simp only [hg, hij, ↓reduceIte, Finset.sum_boole]
    exact this
  have hprod_le : ∏ i ∈ S0, ∑ b : Z2 L, g i b ≤ ((L : ℝ) ^ 2) * ((2 * R + 1) ^ 2) ^ (k - 2) := by
    rw [← Finset.mul_prod_erase S0 (fun i => ∑ b : Z2 L, g i b) hjS0]
    have hj1 : ∑ b : Z2 L, g j b = (L : ℝ) ^ 2 := by
      simp [hg, Fintype.card_prod, ZMod.card, sq]
    rw [hj1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∏ i ∈ S0.erase j, ∑ b : Z2 L, g i b ≤ ∏ _i ∈ S0.erase j, (2 * R + 1) ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b _ => hg0 i b) hball
      _ = ((2 * R + 1) ^ 2) ^ (k - 2) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem hjS0, hcardS0]; congr 1
  have hcardF : (F.card : ℝ) = ((L : ℝ) ^ 2) ^ (k - 1) := SumZeroQ_card_filter a₀
  -- the norm of the identity
  have hnorm : (L : ℝ) ^ 2 * ‖Psum L (lkTensor L W E u M σ) a₀‖ ≤
      (2 * (W : ℝ) ^ 2 * etaT E u)⁻¹ *
        (∑ a ∈ F, (‖LKf L W E u M (Jp a)‖ + ‖LKf L W E u M (Jm a)‖)) := by
    have h := congrArg norm hL2
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, B45_norm_kappa hη] at h
    rw [h]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sub_le _ _)
  have hk2 : (L : ℝ) ^ 2 * (((L : ℝ) ^ 2) ^ (k - 2)) = ((L : ℝ) ^ 2) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hfin : (L : ℝ) ^ 2 * ‖Psum L (lkTensor L W E u M σ) a₀‖ ≤
      (L : ℝ) ^ 2 * (((W : ℝ) ^ 2 * etaT E u)⁻¹ *
        (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) := by
    refine hnorm.trans ?_
    have hinv : (2 * (W : ℝ) ^ 2 * etaT E u)⁻¹ = (1 / 2) * ((W : ℝ) ^ 2 * etaT E u)⁻¹ := by
      field_simp
    rw [hinv]
    have hS : ∑ a ∈ F, (‖LKf L W E u M (Jp a)‖ + ‖LKf L W E u M (Jm a)‖) ≤
        2 * (X * (((L : ℝ) ^ 2) * ((2 * R + 1) ^ 2) ^ (k - 2)) +
          ((L : ℝ) ^ 2) ^ (k - 1) * Bf) := by
      refine hsum1.trans ?_
      rw [hprodsum, hcardF]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have := mul_le_mul_of_nonneg_left hprod_le hX0
      linarith
    have hpos : 0 ≤ ((W : ℝ) ^ 2 * etaT E u)⁻¹ := by positivity
    calc (1 / 2 * ((W : ℝ) ^ 2 * etaT E u)⁻¹) *
          ∑ a ∈ F, (‖LKf L W E u M (Jp a)‖ + ‖LKf L W E u M (Jm a)‖)
        ≤ (1 / 2 * ((W : ℝ) ^ 2 * etaT E u)⁻¹) *
          (2 * (X * (((L : ℝ) ^ 2) * ((2 * R + 1) ^ 2) ^ (k - 2)) +
            ((L : ℝ) ^ 2) ^ (k - 1) * Bf)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (L : ℝ) ^ 2 * (((W : ℝ) ^ 2 * etaT E u)⁻¹ *
          (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) := by
          rw [← hk2]; ring
  exact le_of_mul_le_mul_left hfin (by positivity)


end Slot

/-! ## 4. The operator `ϴ_{u,σ}` for alternating `σ`, and the bound on `ℬ₄` -/

section ThetaOp

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `m m̄ = |m|² = 1` for `|E| ≤ 2`. -/
private theorem B45_mSig_mul_conj {E : ℝ} (hE : |E| ≤ 2) :
    KLoop.mSig E true * KLoop.mSig E false = 1 := by
  simp only [KLoop.mSig, ↓reduceIte, Bool.false_eq_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
  simp

/-- For alternating `σ` every edge factor `ξ_i = m(σ_i) m(σ_{i+1}) = m m̄ = 1`. -/
private theorem B45_xi_one {E : ℝ} (hE : |E| ≤ 2) {σ : Fin k → Bool} (hσ : Alternating σ)
    (i : Fin k) : KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) = 1 := by
  rw [hσ i]
  cases h : σ i
  · simp only [Bool.not_false]
    rw [mul_comm]; exact B45_mSig_mul_conj hE
  · simp only [Bool.not_true]
    exact B45_mSig_mul_conj hE

open scoped Matrix.Norms.Operator in
/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}`. -/
private theorem B45_thetaGenMat_row_le (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Z2 L, ‖thetaGenMat L ξ s x c‖ =
      ‖ξ‖ * ‖(SB L * Theta L ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((B45_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L ((s : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L ((s : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hsξ

/-- The row `ℓ¹` bound of the generator at `ξ = 1`: `Σ_c |(S Θ_u)(x,c)| ≤ (1-u)⁻¹`. -/
private theorem B45_thetaGenMat_row_one (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (x : Z2 L) : ∑ c : Z2 L, ‖thetaGenMat L 1 u x c‖ ≤ (1 - u)⁻¹ := by
  have hnu : ‖(u : ℂ) * 1‖ = u := by
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have h := B45_thetaGenMat_row_le hL (ξ := 1) (s := u) (by rw [hnu]; exact hu1) x
  rwa [hnu, norm_one, one_mul] at h

/-- The kernel `S Θ_ζ` is symmetric. -/
private theorem B45_SB_mul_Theta_symm (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (x y : Z2 L) :
    (SB L * Theta L ζ) x y = (SB L * Theta L ζ) y x := by
  have h : (SB L * Theta L ζ)ᵀ = SB L * Theta L ζ := by
    rw [Matrix.transpose_mul, SB_transpose, Theta_transpose L hL hζ]
    exact (Theta_commute_SB L hL hζ).eq
  have := congrFun (congrFun h y) x
  simpa [Matrix.transpose_apply] using this

/-- The column sums of `S Θ_ζ` are the constant `(1 - ζ)⁻¹`. -/
private theorem B45_col_sum (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Z2 L) :
    ∑ c : Z2 L, (SB L * Theta L ζ) c y = (1 - ζ)⁻¹ := by
  simp_rw [B45_SB_mul_Theta_symm hL hζ _ y]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_Theta_row L hL hζ]
  rw [← Finset.sum_mul, sum_SB_row L hL y, one_mul]

/-- The column sums of the generator at `ξ = 1` are the constant `(1-u)⁻¹`. -/
private theorem B45_col_sum_one (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (y : Z2 L) :
    ∑ c : Z2 L, thetaGenMat L 1 u c y = (((1 - u)⁻¹ : ℝ) : ℂ) := by
  have hξ : ‖(u : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  simp only [thetaGenMat, one_smul, mul_one]
  rw [B45_col_sum hL hξ y]
  push_cast
  rfl

/-- `‖ϴ_{u,σ}𝒜‖_max ≤ k (1-u)⁻¹ ‖𝒜‖_max` for alternating `σ` (`‖ϴ_{u,σ}‖_{∞→∞} ≤ k(1-u)⁻¹`;
`ξ_i = m m̄ = 1`, row sums of `S Θ_u`). -/
private theorem B45_norm_thetaSig_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {σ : Fin k → Bool} (hσ : Alternating σ) {A : (Fin k → Z2 L) → ℂ} {α : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ α) (a : Fin k → Z2 L) :
    ‖thetaSig L E σ u A a‖ ≤ (k : ℝ) * ((1 - u)⁻¹ * α) := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA a)
  simp only [thetaSig, B45_xi_one hE hσ]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Z2 L, thetaGenMat L 1 u (a i) b * A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * α := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (norm_sum_le _ _).trans ?_
        calc ∑ b : Z2 L, ‖thetaGenMat L 1 u (a i) b * A (Function.update a i b)‖
            ≤ ∑ b : Z2 L, ‖thetaGenMat L 1 u (a i) b‖ * α := by
              refine Finset.sum_le_sum fun b _ => ?_
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
          _ = (∑ b : Z2 L, ‖thetaGenMat L 1 u (a i) b‖) * α := by rw [Finset.sum_mul]
          _ ≤ (1 - u)⁻¹ * α :=
              mul_le_mul_of_nonneg_right (B45_thetaGenMat_row_one hL hu0 hu1 _) hα
    _ = (k : ℝ) * ((1 - u)⁻¹ * α) := by simp

/-- `|𝒫(ϴ_{u,σ}𝒜)| ≤ k (1-u)⁻¹ max|𝒫𝒜|` for alternating `σ`: slot `0` gives
`Σ_b G(a₁,b)(𝒫𝒜)_b`, slot `i ≠ 0` gives the constant column sum `(1-u)⁻¹` times `(𝒫𝒜)_{a₁}`
(`SumZeroQ_slot_zero`, `SumZeroQ_slot_succ`). -/
private theorem B45_norm_Psum_thetaSig_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {σ : Fin k → Bool} (hσ : Alternating σ) {A : (Fin k → Z2 L) → ℂ} {P : ℝ}
    (hP : ∀ b, ‖Psum L A b‖ ≤ P) (a₀ : Z2 L) :
    ‖Psum L (thetaSig L E σ u A) a₀‖ ≤ (k : ℝ) * ((1 - u)⁻¹ * P) := by
  classical
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP a₀)
  have h1u : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
  unfold Psum
  simp only [thetaSig, B45_xi_one hE hσ]
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  have hi : ∀ i : Fin k, ‖∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₀),
      ∑ b : Z2 L, thetaGenMat L 1 u (a i) b * A (Function.update a i b)‖ ≤ (1 - u)⁻¹ * P := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [SumZeroQ_slot_zero (fun x y => thetaGenMat L 1 u x y) A a₀]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b : Z2 L, ‖thetaGenMat L 1 u a₀ b * Psum L A b‖
          ≤ ∑ b : Z2 L, ‖thetaGenMat L 1 u a₀ b‖ * P := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hP b) (norm_nonneg _)
        _ = (∑ b : Z2 L, ‖thetaGenMat L 1 u a₀ b‖) * P := by rw [Finset.sum_mul]
        _ ≤ (1 - u)⁻¹ * P := mul_le_mul_of_nonneg_right (B45_thetaGenMat_row_one hL hu0 hu1 _) hP0
    · rw [SumZeroQ_slot_succ h0 (fun x y => thetaGenMat L 1 u x y) A a₀]
      have hcol : ∀ a : Fin k → Z2 L, (∑ c : Z2 L, thetaGenMat L 1 u c (a i)) * A a =
          (((1 - u)⁻¹ : ℝ) : ℂ) * A a := fun a => by rw [B45_col_sum_one hL hu0 hu1]
      simp only [hcol]
      rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1u.le]
      exact mul_le_mul_of_nonneg_left (hP a₀) h1u.le
  calc ∑ i : Fin k, ‖∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₀),
        ∑ b : Z2 L, thetaGenMat L 1 u (a i) b * A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * P := Finset.sum_le_sum fun i _ => hi i
    _ = (k : ℝ) * ((1 - u)⁻¹ * P) := by simp

/-- **`ℬ₄`** (`kkuuwsaf5`): with the commutator formula of `qopAlgebra`
(`SumZeroQ_commutator`), `‖[𝒬_u, ϴ_{u,σ}]𝒜‖_max ≤ 2k (1-u)⁻¹ ‖ϑ_u‖_max max|𝒫𝒜|`. -/
private theorem B45_B4_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin k → Bool} (hσ : Alternating σ) (A : (Fin k → Z2 L) → ℂ) {P : ℝ}
    (hP : ∀ b, ‖Psum L A b‖ ≤ P) (a : Fin k → Z2 L) :
    ‖Qop L u (thetaSig L E σ u A) a - thetaSig L E σ u (Qop L u A) a‖ ≤
      2 * (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0)
  have h1u : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
  have hc : ∀ b : Fin k → Z2 L, ‖vartheta L u b‖ ≤ B45_c L u ^ (k - 1) := fun b =>
    B45_norm_vartheta_le hL hu0 hu1 b
  rw [SumZeroQ_commutator E σ u A a]
  refine (norm_sub_le _ _).trans ?_
  have T1 := B45_norm_thetaSig_le hL hE hu0 hu1 hσ
    (A := fun b => Psum L A (b 0) * vartheta L u b) (α := P * B45_c L u ^ (k - 1))
    (fun b => by
      rw [norm_mul]
      exact mul_le_mul (hP _) (hc b) (norm_nonneg _) hP0) a
  have T2 : ‖Psum L (thetaSig L E σ u A) (a 0) * vartheta L u a‖ ≤
      (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) := by
    rw [norm_mul]
    have h2 := B45_norm_Psum_thetaSig_le hL hE hu0 hu1 hσ hP (a 0)
    have h3 := hc a
    calc ‖Psum L (thetaSig L E σ u A) (a 0)‖ * ‖vartheta L u a‖
        ≤ ((k : ℝ) * ((1 - u)⁻¹ * P)) * B45_c L u ^ (k - 1) :=
          mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) := by ring
  calc _ ≤ (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) +
        (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) := add_le_add T1 T2
    _ = 2 * (k : ℝ) * ((1 - u)⁻¹ * (P * B45_c L u ^ (k - 1))) := by ring

end ThetaOp

/-! ## 5. The deterministic core: `ℬ₅` and `ℬ₄` -/

section Core

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The deterministic core** (`jfasiuu`, `jywiiwsoks`, `eq:thetadot_bound`, `kkuuwsaf`,
`kkuuwsaf5`): if every well-formed loop of rank `k-1` has `|𝓛-𝒦| ≤ X`, and those
with two labels `≥ R` apart have `|𝓛-𝒦| ≤ B_f`, then for alternating `σ`
`|ℬ₅|, |ℬ₄| ≤ 2k (1-u)⁻¹ c_u^{k-1} (W²η_u)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f)`. -/
private theorem B45_core_det (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ)
    {R X Bf : ℝ} (hR : 0 ≤ R) (hX0 : 0 ≤ X) (hBf0 : 0 ≤ Bf)
    (hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 → ‖LKf L W E u M J‖ ≤ X)
    (hBf : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) → ‖LKf L W E u M J‖ ≤ Bf)
    (a : Fin k → Z2 L) :
    ‖B5 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ *
        ((((W : ℝ) ^ 2 * etaT E u)⁻¹ *
          (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) *
          B45_c L u ^ (k - 1))) ∧
    ‖B4 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ *
        ((((W : ℝ) ^ 2 * etaT E u)⁻¹ *
          (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) *
          B45_c L u ^ (k - 1))) := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1u : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
  set Pb : ℝ := ((W : ℝ) ^ 2 * etaT E u)⁻¹ *
      (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf) with hPb
  have hPb0 : 0 ≤ Pb := by positivity
  have hP : ∀ b : Z2 L, ‖Psum L (lkTensor L W E u M σ) b‖ ≤ Pb := fun b =>
    B45_psum_le hL hW hE hu0 hu1 hM hk hσ hR hX0 hBf0 hX hBf b
  have hc0 : 0 ≤ B45_c L u := B45_c_nonneg L u
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · -- `ℬ₅ = (𝒫(𝓛-𝒦))_{a₁} ϑ̇_a`
    have h5 := B45_norm_varthetaDot_le (k := k) hL hk hu0 hu1 a
    unfold B5
    rw [norm_mul]
    calc ‖Psum L (lkTensor L W E u M σ) (a 0)‖ * ‖varthetaDot L u a‖
        ≤ Pb * (2 * ((k : ℝ) - 1) * (1 - u)⁻¹ * B45_c L u ^ (k - 1)) :=
          mul_le_mul (hP _) h5 (norm_nonneg _) hPb0
      _ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ * (Pb * B45_c L u ^ (k - 1))) := by
          have hpos : 0 ≤ (1 - u)⁻¹ * (Pb * B45_c L u ^ (k - 1)) := by positivity
          nlinarith
  · -- `ℬ₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)`
    unfold B4
    exact B45_B4_le hL hE.le hu0 hu1 hσ (lkTensor L W E u M σ) hP a

end Core

end RBM.Ind

end

/-! ## 6. Public restatements

`B45_psum_le_pub` is the private `B45_psum_le` with the name changed (the bound `jywiiwsoks` for
`𝒫(𝓛-𝒦)`), `B45_P_vartheta_le` is the bound for `𝒫(𝓛-𝒦)ϑ` that the last step
`𝓛-𝒦 = 𝒬(𝓛-𝒦) + (𝒫(𝓛-𝒦))ϑ` (`kolkisaf`) needs (the core bounds `ℬ₄`, `ℬ₅` only, with `ϑ̇`).
`B45_norm_vartheta_le_pub` and `B45_core_det_pub` are the public forms of the private
`B45_norm_vartheta_le` and `B45_core_det`, used for the crude envelope of `ℬ₄`, `ℬ₅` in
`RBM2D.Induction.AltDriftQ`.  `c_L(u) = C₅(1+log L)ℓ_u^{-2}` with `C₅ = 180·40002²` is written
out. -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

section PublicLemmas

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **`jywiiwsoks`, public**: the private `B45_psum_le`.
`|[𝒫(𝓛-𝒦)_{u,σ}]_{a₀}| ≤ (W²η_u)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f)` for alternating `σ`, if
every well-formed rank-`(k-1)` loop has `|𝓛-𝒦| ≤ X` and those with two labels `≥ R` apart have
`|𝓛-𝒦| ≤ B_f`. -/
theorem B45_psum_le_pub (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ)
    {R X Bf : ℝ} (hR : 0 ≤ R) (hX0 : 0 ≤ X) (hBf0 : 0 ≤ Bf)
    (hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 → ‖LKf L W E u M J‖ ≤ X)
    (hBf : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) → ‖LKf L W E u M J‖ ≤ Bf)
    (a₀ : Z2 L) :
    ‖Psum L (lkTensor L W E u M σ) a₀‖ ≤
      ((W : ℝ) ^ 2 * RBM.Path.etaT E u)⁻¹ *
        (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf) :=
  B45_psum_le hL hW hE hu0 hu1 hM hk hσ hR hX0 hBf0 hX hBf a₀

/-- **`|ϑ_{u,a}| ≤ c_L^{k-1}`, public** (property 5 at `ξ = u`): `c_L = C₅(1+log L)ℓ_u^{-2}`,
`C₅ = 180·40002²` (the private `B45_norm_vartheta_le`). -/
theorem B45_norm_vartheta_le_pub {k : ℕ} [NeZero k] (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a : Fin k → Z2 L) :
    ‖vartheta L t a‖ ≤
      ((180 * 40002 ^ 2) * (1 + Real.log L) * (RBM.Path.ellT L t ^ 2)⁻¹) ^ (k - 1) :=
  B45_norm_vartheta_le hL ht0 ht1 a

/-- **The bound for `𝒫(𝓛-𝒦) ϑ` (`jywiiwsoks` and `kolkisaf`)**: under the hypotheses of
`B45_psum_le_pub`, for every label `a`,
`|(𝒫(𝓛-𝒦)_{u,σ})_{a₁} ϑ_{u,a}| ≤ (W²η_u)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f) (C₅(1+log L)ℓ_u^{-2})^{k-1}`.
The powers of `ℓ_u` cancel against `(W²η_u)⁻¹ = ℓ_u²M_u⁻¹` when `X` is the level of `Ξ_{k-1}`
(`R = ℓ_u W^{τ'}`: `2 + 2(k-2) - 2(k-1) = 0`). -/
theorem B45_P_vartheta_le (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ)
    {R X Bf : ℝ} (hR : 0 ≤ R) (hX0 : 0 ≤ X) (hBf0 : 0 ≤ Bf)
    (hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 → ‖LKf L W E u M J‖ ≤ X)
    (hBf : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) → ‖LKf L W E u M J‖ ≤ Bf)
    (a : Fin k → Z2 L) :
    ‖Psum L (lkTensor L W E u M σ) (a 0) * vartheta L u a‖ ≤
      ((W : ℝ) ^ 2 * RBM.Path.etaT E u)⁻¹ *
        (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf) *
        ((180 * 40002 ^ 2) * (1 + Real.log L) * (RBM.Path.ellT L u ^ 2)⁻¹) ^ (k - 1) := by
  rw [norm_mul]
  have h1 := B45_psum_le_pub hL hW hE hu0 hu1 hM hk hσ hR hX0 hBf0 hX hBf (a 0)
  have h2 := B45_norm_vartheta_le_pub (k := k) hL hu0 hu1 a
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- **The deterministic core, public** (the private `B45_core_det`): under the hypotheses of
`B45_psum_le_pub`, `|ℬ₅|, |ℬ₄| ≤ 2k (1-u)⁻¹ c_L^{k-1} (W²η_u)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f)`. -/
theorem B45_core_det_pub (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ)
    {R X Bf : ℝ} (hR : 0 ≤ R) (hX0 : 0 ≤ X) (hBf0 : 0 ≤ Bf)
    (hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 → ‖LKf L W E u M J‖ ≤ X)
    (hBf : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) → ‖LKf L W E u M J‖ ≤ Bf)
    (a : Fin k → Z2 L) :
    ‖B5 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ *
        ((((W : ℝ) ^ 2 * RBM.Path.etaT E u)⁻¹ *
          (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) *
          ((180 * 40002 ^ 2) * (1 + Real.log L) * (RBM.Path.ellT L u ^ 2)⁻¹) ^ (k - 1))) ∧
    ‖B4 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ *
        ((((W : ℝ) ^ 2 * RBM.Path.etaT E u)⁻¹ *
          (((2 * R + 1) ^ 2) ^ (k - 2) * X + ((L : ℝ) ^ 2) ^ (k - 2) * Bf)) *
          ((180 * 40002 ^ 2) * (1 + Real.log L) * (RBM.Path.ellT L u ^ 2)⁻¹) ^ (k - 1))) :=
  B45_core_det hL hW hE hu0 hu1 hM hk hσ hR hX0 hBf0 hX hBf a

end PublicLemmas

end RBM.Ind

end
