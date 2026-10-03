/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Induction.ConArgDet
import RBM2D.Induction.PerTimeCalc

/-!
# `lem_ConArg`: the continuity argument, probabilistic part

The statement `ConArgPin`; `conArg` proves it for every size sequence `d`.

Paper: arXiv:2503.07606, Section 5, Lemma `lem_ConArg` with (`55`), (`usuayzoo`),
(`res_lo_bo_eta`).

## Proof

The argument parallels the one-dimensional formalization.

* Section `Recursion`: `conArg_rpow_pow_mul_sub_one_le`, `conArg_det_mul`, `conArg_odd_of_even`,
  `conArg_continuity_recursion`, stated for `RBM.Path.PerTimeDomAt` along `size n` with the
  `≺`-calculus of `Induction/PerTimeCalc`.  The hypothesis `hsize : Tendsto size atTop atTop`
  replaces the filter on `N`.
* Section `BaseCase`: `conArg_norm_trace_mul_Eblk_le_of_diag`, `conArg_loopMax_one_le`, with the
  `d = 2` weight `E_a = W⁻² 1_{𝓘_a}` (`sum_bw` of `Induction/Split`).
* Section `conArg_loopMax_perTime`: the `d = 2` scales are `a₁ = M_{t₁}⁻¹ = (W²ℓ₁²η₁)⁻¹` and
  `a = (W²ℓ₁²η₂)⁻¹`, so the right side is `a^{k-1} = (ℓ₂/ℓ₁)^{2(k-1)} M_{t₂}^{-(k-1)}` (in
  `d = 1`: `(ℓ₂/ℓ₁)^{k-1}`).  The parameter `(σ, a)` of (`55`) is a `PerTimeDomAt` parameter (union
  outside `P`); it is moved inside `P` by `RBM.Path.stochDomAt_of_perTimeDomAt` with
  `#U ≤ size^{2k}`.
* The scaling (6.1) is proved pointwise on the common sample space (`conArg_inv_smul`,
  `conArg_green_smul_mul`, `conArg_Gsig_smul_mul`, `conArg_gloopProd_smul_mul`,
  `conArg_gloop_smul_mul`, `conArg_loopMax_tilde_le`): `H_u = √u X` (`Sizes.seqHflow_eq_smul`), so
  the loops of `G̃ = (H_{t₂} - z̃_{t₁})⁻¹` are `(t₁/t₂)^{k/2}` times the loops of `G_{t₁}`, and
  `(t₁/t₂)^{k/2} ≤ 1`.

The deterministic inputs are (6.4) `loopMax_odd_sq_le` (`Induction/Split`), (6.11)
`loopMax_two_mul_le_tilde` and the arithmetic `ztTilde_arith` (`Induction/ConArgDet`).

All helpers are `private`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **`lem_ConArg`**, per sequence: `c < t₁ ≤ t₂ < 1` (the paper allows
`t₂ = 1`, where `η_{t₂} = 0`), bulk energy `E n`; if (`55`) `max_{σ,a} |𝓛_{t₁,σ,a}| ≺
M_{t₁}^{-k+1}` for every `k ≥ 1`, then for every `k ≥ 1`,
`1_Ω max_{σ,a} |𝓛_{t₂,σ,a}| ≺ (ℓ_{t₂}/ℓ_{t₁})^{2(k-1)} M_{t₂}^{-k+1}` with
`Ω = {‖G_{t₂}‖_max ≤ 2}` (`res_lo_bo_eta`; the right side equals `(W² ℓ_{t₁}² η_{t₂})^{-k+1}`). -/
def ConArgPin (κ c : ℝ) (E : ℕ → ℝ) (t₁ t₂ : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → (∀ n, c < t₁ n) → (∀ n, t₁ n ≤ t₂ n) →
    (∀ n, t₂ n < 1) → SizeTendsto d →
    (∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => loopAbs (d.L n) (d.W n) (E n) (t₁ n) (Sizes.seqHflow d n (t₁ n) ω) p.2.1 p.2.2)
      (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (t₁ n))⁻¹ ^ (k - 1))) →
    ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω =>
        (if gMax (E n) (t₂ n) (Sizes.seqHflow d n (t₂ n) ω) ≤ 2 then 1 else 0) *
          loopAbs (d.L n) (d.W n) (E n) (t₂ n) (Sizes.seqHflow d n (t₂ n) ω) p.2.1 p.2.2)
      (fun n _ _ => (ellT (d.L n) (t₂ n) / ellT (d.L n) (t₁ n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) (t₂ n))⁻¹ ^ (k - 1))

/-! ## 1. The recursion of §6 under `PerTimeDomAt` -/

section Recursion

open PerTimeCalc.PerTime

/-- `(x^{pj-1})^{1/p} ≤ x^j M^{1/p}` for `x > 0`, `x⁻¹ ≤ M`: the loss `M_{t₁}^{1/p}` of (6.10). -/
private theorem conArg_rpow_pow_mul_sub_one_le {x M : ℝ} (hx : 0 < x) (hM : x⁻¹ ≤ M) {p j : ℕ}
    (hp : 1 ≤ p) (hj : 1 ≤ j) :
    (x ^ (p * j - 1)) ^ (1 / (p : ℝ)) ≤ x ^ j * M ^ (1 / (p : ℝ)) := by
  have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : x ^ (p * j - 1) = (x ^ j) ^ p * x⁻¹ := by
    rw [← pow_mul, mul_comm j p]
    have : x ^ (p * j) = x ^ (p * j - 1) * x := by
      rw [← pow_succ]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  rw [e, Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM (by positivity))
    (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Multiplying both sides of `≺` by a deterministic non-negative factor. -/
private theorem conArg_det_mul (hsize : Tendsto size atTop atTop) {f : ℕ → ℝ}
    (hf : ∀ N, 0 ≤ f N) {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun N u ω => f N * ξ N u ω) (fun N u ω => f N * ζ N u ω) :=
  perTimeCalc_mul (ξ₁ := fun N _ _ => f N) (ζ₁ := fun N _ _ => f N) hsize hξ
    (fun N _ _ => hf N) (perTimeCalc_refl hsize fun N _ _ => hf N) h

/-- A pointwise smaller left side. -/
private theorem conArg_of_le_left {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) (h : PerTimeDomAt P size ξ' ζ) :
    PerTimeDomAt P size ξ ζ :=
  stochDom_of_le_left_eventually (Eventually.of_forall hle) h

/-- **Odd loops from even ones** ((6.4) under `≺`). -/
private theorem conArg_odd_of_even (hsize : Tendsto size atTop atTop)
    {Y : ℕ → ∀ N, U N → Ω → ℝ} {a : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N)
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) {l : ℕ} (hl : 1 ≤ l)
    (hodd : ∀ N u ω, Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (h1 : PerTimeDomAt P size (Y (2 * l)) (fun N _ _ => a N ^ (2 * l - 1)))
    (h2 : PerTimeDomAt P size (Y (2 * l + 2)) (fun N _ _ => a N ^ (2 * l + 1))) :
    PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
  have hm := perTimeCalc_mul hsize (hY0 _) (fun N _ _ => pow_nonneg (ha N) _) h1 h2
  have hs := sqrt_of (fun N u ω => mul_nonneg (hY0 _ N u ω) (hY0 _ N u ω))
    (fun N u ω => mul_nonneg (pow_nonneg (ha N) _) (pow_nonneg (ha N) _)) hm
  have e : ∀ N, Real.sqrt (a N ^ (2 * l - 1) * a N ^ (2 * l + 1)) = a N ^ (2 * l) := by
    intro N
    rw [← pow_add, show 2 * l - 1 + (2 * l + 1) = 2 * (2 * l) by omega, pow_mul',
      Real.sqrt_sq (pow_nonneg (ha N) _)]
  refine conArg_of_le_left (fun N u ω => Real.le_sqrt_of_sq_le (hodd N u ω)) ?_
  simpa only [e] using hs

/-- **The induction of Section 6, abstractly, per time**, with `N ↦ size N`:
for deterministic `0 < a₁ ≤ a`, `K ≥ 0`, `K a₁ ≤ C a`, `a₁⁻¹ ≤ size`, and families `Y_n, T_n ≥ 0`
with `T_n ≺ a₁^{n-1}`, `Y_1 ≤ 2`, (6.4) and (6.11), one has `Y_n ≺ a^{n-1}` for every `n ≥ 1`. -/
private theorem conArg_continuity_recursion (hsize : Tendsto size atTop atTop)
    {Y T : ℕ → ∀ N, U N → Ω → ℝ} {a a1 K : ℕ → ℝ} {C : ℝ}
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) (hT0 : ∀ n N u ω, 0 ≤ T n N u ω)
    (ha1 : ∀ N, 0 < a1 N) (ha1a : ∀ N, a1 N ≤ a N) (hK0 : ∀ N, 0 ≤ K N) (hC : 0 ≤ C)
    (hK : ∀ N, K N * a1 N ≤ C * a N) (hN : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ (size N : ℝ))
    (hT : ∀ n, 1 ≤ n → PerTimeDomAt P size (T n) (fun N _ _ => a1 N ^ (n - 1)))
    (hY1 : ∀ N u ω, Y 1 N u ω ≤ 2)
    (hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ)))) :
    ∀ n, 1 ≤ n → PerTimeDomAt P size (Y n) (fun N _ _ => a N ^ (n - 1)) := by
  have ha0 : ∀ N, 0 < a N := fun N => (ha1 N).trans_le (ha1a N)
  have hY1' : PerTimeDomAt P size (Y 1) (fun N _ _ => a N ^ (2 * 0)) := by
    simp only [mul_zero, pow_zero]
    exact stochDom_of_le_const_mul hsize (hY0 1) (fun _ _ _ => zero_le_one) 2
      (fun N u ω => by linarith [hY1 N u ω])
  -- the even lengths, by strong induction
  have hE : ∀ m, 1 ≤ m → PerTimeDomAt P size (Y (2 * m)) (fun N _ _ => a N ^ (2 * m - 1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hOdd : ∀ l, l < k → PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
      intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hY1'
      · refine conArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hl0 (hodd l hl0)
          (ih l (by omega) hl0) ?_
        have := ih (l + 1) (by omega) (by omega)
        rwa [show 2 * (l + 1) = 2 * l + 2 by ring, show 2 * l + 2 - 1 = 2 * l + 1 by omega]
          at this
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    refine of_forall_rpow_mul fun δ hδ => ?_
    obtain ⟨p0, hp0⟩ := exists_nat_one_div_lt (half_pos hδ)
    set p := p0 + 1 with hp_def
    have hp : 1 ≤ p := by omega
    set r : ℝ := 1 / (p : ℝ) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one (by positivity)]; exact_mod_cast hp
    have hrδ : r + r ≤ δ := by
      have : r < δ / 2 := by rw [hr, hp_def]; push_cast; exact hp0
      linarith
    set A : ℕ → ℝ := fun N => a N ^ (2 * k + 1) with hA
    have hA0 : ∀ N, 0 ≤ A N := fun N => pow_nonneg (ha0 N).le _
    have hNr : ∀ N : ℕ, 0 ≤ (size N : ℝ) ^ r := fun N => Real.rpow_nonneg (Nat.cast_nonneg _) r
    have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ (size N : ℝ) ^ r ∧ (a1 N)⁻¹ ≤ (size N : ℝ) := by
      filter_upwards [hN, hsize.eventually (eventually_ge_atTop 1)] with N hN1 hN2
      exact ⟨Real.one_le_rpow (by exact_mod_cast hN2) hr0.le, hN1⟩
    -- case 1: the `G̃` loop of length `2m`
    have hR1 : PerTimeDomAt P size (T (2 * (k + 1)))
        (fun N _ _ => A N * (size N : ℝ) ^ r) := by
      refine mono_right_eventually (hT (2 * (k + 1)) (by omega)) ?_
      filter_upwards [hev] with N hN u ω
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      calc a1 N ^ (2 * k + 1) ≤ A N := pow_le_pow_left₀ (ha1 N).le (ha1a N) _
        _ ≤ A N * (size N : ℝ) ^ r := le_mul_of_one_le_right (hA0 N) hN.1
    -- the `G̃` factors `T^{1/p}`
    have hTr : ∀ j, 1 ≤ j → PerTimeDomAt P size (fun N u ω => K N * T (p * j) N u ω ^ r)
        (fun N _ _ => C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r) := by
      intro j hj
      have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h1 := conArg_det_mul hsize hK0 (fun N u ω => Real.rpow_nonneg (hT0 _ N u ω) r)
        (rpow_of_le_one hr0 hr1 (hT0 (p * j)) (fun N _ _ => pow_nonneg (ha1 N).le _)
          (hT (p * j) hpj))
      refine mono_right_eventually h1 ?_
      filter_upwards [hev] with N hN u ω
      have h2 := conArg_rpow_pow_mul_sub_one_le (ha1 N) hN.2 hp hj
      calc K N * (a1 N ^ (p * j - 1)) ^ r ≤ K N * (a1 N ^ j * (size N : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left h2 (hK0 N)
        _ = (K N * a1 N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r := by
            rw [show a1 N ^ j = a1 N * a1 N ^ (j - 1) by
              rw [← pow_succ']; congr 1; omega]
            ring
        _ ≤ (C * a N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK N)
              (pow_nonneg (ha1 N).le _)) (hNr N)
        _ = C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r := by ring
    -- case 2: the terms `l < m - 1`
    have hR2 : PerTimeDomAt P size (fun N u ω => ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        (fun N _ _ => ∑ l ∈ Finset.range k, C * A N * (size N : ℝ) ^ r) := by
      refine finset_sum_of hsize _ fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      have hj : 1 ≤ 2 * (k + 1 - l) - 1 := by omega
      have h1 := perTimeCalc_mul hsize
        (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 _ N u ω) r))
        (fun N _ _ => pow_nonneg (ha0 N).le _) (hOdd l hl') (hTr _ hj)
      refine mono_right_eventually (conArg_of_le_left (fun N u ω => le_of_eq ?_) h1) ?_
      · ring
      · filter_upwards [hev] with N hN u ω
        have e : 2 * (k + 1 - l) - 1 - 1 = 2 * (k - l) := by omega
        rw [e]
        calc a N ^ (2 * l) * (C * a1 N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r)
            ≤ a N ^ (2 * l) * (C * a N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (ha1 N).le (ha1a N) _) hC) (ha0 N).le) (hNr N))
                (pow_nonneg (ha0 N).le _)
          _ = C * A N * (size N : ℝ) ^ r := by
              simp only [hA]
              rw [show 2 * k + 1 = 2 * l + 2 * (k - l) + 1 by omega, pow_succ, pow_add]
              ring
    -- case 3: the term `l = m - 1`
    have hR3 : PerTimeDomAt P size (fun N u ω => K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r))
        (fun N u ω => 2 * C * A N * (size N : ℝ) ^ r
          + C * (size N : ℝ) ^ r * Real.sqrt (A N * Y (2 * (k + 1)) N u ω)) := by
      have hT1 := hTr 1 le_rfl
      simp only [mul_one, Nat.sub_self, pow_zero] at hT1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · -- `m = 1`: the base case (5.6)
        have h1 := conArg_det_mul (f := fun _ => (2 : ℝ)) hsize (fun _ => by norm_num)
          (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)) hT1
        refine mono_right_eventually (conArg_of_le_left (fun N u ω => ?_) h1) ?_
        · have hy := hY1 N u ω
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          simp only [mul_zero, zero_add]
          nlinarith
        · filter_upwards with N u ω
          simp only [hA, mul_zero, zero_add, pow_one]
          have h1 : 0 ≤ C * (size N : ℝ) ^ r * Real.sqrt (a N * Y (2 * 1) N u ω) :=
            mul_nonneg (mul_nonneg hC (hNr N)) (Real.sqrt_nonneg _)
          have h2 : 0 ≤ C * a N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)
          linarith
      · -- `m > 1`: (6.4) and the induction hypothesis for the `(2m-2)`-loops
        have hIH := sqrt_of (hY0 _) (fun N _ _ => pow_nonneg (ha0 N).le _)
          (ih k (by omega) hk0)
        have h1 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg _)
          (fun N _ _ => mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)) hT1 hIH
        have h2 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
          (fun N _ _ => mul_nonneg (mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N))
            (Real.sqrt_nonneg _)) h1
          (perTimeCalc_refl hsize fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
        refine mono_right_eventually (conArg_of_le_left (fun N u ω => ?_) h2) ?_
        · have hodd' := hodd k hk0 N u ω
          rw [show 2 * k + 2 = 2 * (k + 1) by ring] at hodd'
          have hy : Y (2 * k + 1) N u ω
              ≤ Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            rw [← Real.sqrt_mul (hY0 _ N u ω)]
            exact Real.le_sqrt_of_sq_le hodd'
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          calc K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)
              = (K N * T p N u ω ^ r) * Y (2 * k + 1) N u ω := by ring
            _ ≤ (K N * T p N u ω ^ r)
                * (Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω)) :=
                mul_le_mul_of_nonneg_left hy hk
            _ = _ := by ring
        · filter_upwards with N u ω
          have e : Real.sqrt (A N * Y (2 * (k + 1)) N u ω)
              = a N * Real.sqrt (a N ^ (2 * k - 1)) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            simp only [hA]
            rw [show 2 * k + 1 = 2 + (2 * k - 1) by omega, pow_add,
              Real.sqrt_mul (mul_nonneg (pow_nonneg (ha0 N).le _) (pow_nonneg (ha0 N).le _)),
              Real.sqrt_mul (pow_nonneg (ha0 N).le _), Real.sqrt_sq (ha0 N).le]
          rw [e]
          have : 0 ≤ 2 * C * A N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (hA0 N)) (hNr N)
          nlinarith [this]
    -- (6.13): assemble
    have hsum : ∀ N u ω, Y (2 * (k + 1)) N u ω ≤ ((k : ℝ) + 2) * ((T (2 * (k + 1)) N u ω
        + ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        + K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)) := by
      intro N u ω
      have h := hrec (k + 1) (by omega) p hp N u ω
      rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega,
        show p * (2 * 1 - 1) = p by ring, ← hr] at h
      refine h.trans (le_of_eq ?_)
      rw [mul_add (K N), Finset.mul_sum]
      push_cast
      ring
    have hR := conArg_det_mul (f := fun _ => (k : ℝ) + 2) hsize (fun _ => by positivity)
      (fun N u ω => add_nonneg (add_nonneg (hT0 _ N u ω) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
        (mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
      (perTimeCalc_add hsize (perTimeCalc_add hsize hR1 hR2) hR3)
    set D1 : ℝ := ((k : ℝ) + 2) * (1 + ((k : ℝ) + 2) * C) with hD1
    set D2 : ℝ := ((k : ℝ) + 2) * C with hD2
    set D : ℝ := (D1 + D2 + 1) ^ 2 with hD
    have hD1_0 : 0 ≤ D1 := mul_nonneg (by positivity) (by nlinarith)
    have hD2_0 : 0 ≤ D2 := mul_nonneg (by positivity) hC
    have hD1D : D1 ≤ D := by nlinarith
    have hD2D : D2 ^ 2 ≤ D := by nlinarith
    have hD0 : 0 ≤ D := sq_nonneg _
    have hstep : PerTimeDomAt P size (Y (2 * (k + 1))) (fun N u ω =>
        D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
          + Real.sqrt (D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
            * Y (2 * (k + 1)) N u ω)) := by
      refine mono_right_eventually (conArg_of_le_left (fun N u ω => hsum N u ω) hR) ?_
      filter_upwards [hev] with N hN u ω
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      set x := (size N : ℝ) ^ r
      set y := Y (2 * (k + 1)) N u ω
      have hx1 : 1 ≤ x := hN.1
      have hy : 0 ≤ y := hY0 _ N u ω
      have hAy : 0 ≤ A N * y := mul_nonneg (hA0 N) hy
      have p1 : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
          ≤ D * (x * x * A N) := by
        have e : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
            = D1 * (A N * x) := by rw [hD1]; ring
        rw [e]
        have hAx : 0 ≤ A N * x := mul_nonneg (hA0 N) (by linarith)
        calc D1 * (A N * x) ≤ D * (A N * x) := mul_le_mul_of_nonneg_right hD1D hAx
          _ ≤ D * (A N * x * x) := mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hAx hx1) hD0
          _ = D * (x * x * A N) := by ring
      have p2 : ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
          ≤ Real.sqrt (D * (x * x * A N) * y) := by
        refine Real.le_sqrt_of_sq_le ?_
        have e : (((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))) ^ 2
            = D2 ^ 2 * (x ^ 2 * (A N * y)) := by
          rw [show ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
            = D2 * x * Real.sqrt (A N * y) by rw [hD2]; ring, mul_pow, mul_pow,
            Real.sq_sqrt hAy]
          ring
        rw [e]
        calc D2 ^ 2 * (x ^ 2 * (A N * y)) ≤ D * (x ^ 2 * (A N * y)) :=
              mul_le_mul_of_nonneg_right hD2D (mul_nonneg (sq_nonneg _) hAy)
          _ = D * (x * x * A N) * y := by ring
      calc ((k : ℝ) + 2) * (A N * x + k * (C * A N * x)
            + (2 * C * A N * x + C * x * Real.sqrt (A N * y)))
          = ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
            + ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y)) := by ring
        _ ≤ _ := add_le_add p1 p2
    have hZ0 : ∀ N (u : U N) (ω : Ω), 0 ≤ (size N : ℝ) ^ r * (size N : ℝ) ^ r * A N :=
      fun N _ _ => mul_nonneg (mul_nonneg (hNr N) (hNr N)) (hA0 N)
    have hZ := of_le_add_sqrt_mul hsize (hY0 _) (fun N u ω => mul_nonneg hD0 (hZ0 N u ω))
      hstep
    refine perTimeCalc_mono hsize
      (fun N _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (hA0 N)) D ?_ hZ
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with N hN1 u ω
    have hN1' : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1' hrδ) (hA0 N)) hD0
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact hE m (by omega)
  · rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hY1'
    · refine conArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hm0 (hodd m hm0) (hE m hm0) ?_
      have := hE (m + 1) (by omega)
      rwa [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 - 1 = 2 * m + 1 by omega]
        at this

end Recursion

/-! ## 2. (6.1) on the common sample space: the loops of `G̃` -/

section Scaling

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar (no invertibility assumption on `A`). -/
private theorem conArg_inv_smul {c : ℂ} (hc : c ≠ 0) (A : Matrix n n ℂ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- `G(cH, cz) = c⁻¹ G(H, z)`. -/
private theorem conArg_green_smul_mul {c : ℂ} (hc : c ≠ 0) (H : Matrix n n ℂ) (z : ℂ) :
    green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold green
  rw [hsub, conArg_inv_smul hc]

/-- The same for `Gsig` with a real scalar. -/
private theorem conArg_Gsig_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0) (H : Matrix n n ℂ) (z : ℂ)
    (σ : Bool) : Gsig ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • Gsig H z σ := by
  cases σ with
  | true => simpa only [Gsig_true] using conArg_green_smul_mul hr H z
  | false =>
    rw [Gsig_false, Gsig_false, map_mul, Complex.conj_ofReal]
    exact conArg_green_smul_mul hr H _

variable {L W : ℕ} [NeZero L]

/-- `∏ G(cH, cz)(σ_i) E_{a_i} = c⁻ⁿ ∏ G(H, z)(σ_i) E_{a_i}` on `BlockIndex L W`. -/
private theorem conArg_gloopProd_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) :
    gloopProd L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = (((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length) • gloopProd L W H z I := by
  obtain ⟨σ, a⟩ := I
  induction σ generalizing a with
  | nil => simp [gloopProd]
  | cons s σ ih =>
    cases a with
    | nil => simp [gloopProd]
    | cons b a =>
      rw [gloopProd_cons, gloopProd_cons, conArg_Gsig_smul_mul hr, ih, smul_mul_assoc,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      simp only [List.zip_cons_cons, List.length_cons]
      congr 1
      ring

/-- `L(cH, cz) = c⁻ⁿ L(H, z)`. -/
private theorem conArg_gloop_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) :
    gloop L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * gloop L W H z I := by
  unfold gloop
  rw [conArg_gloopProd_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

end Scaling

/-- **(6.1) pointwise, as a bound on `loopMax`**: for `0 < t₁ ≤ t₂`, every loop of
`G̃ = (H_{t₂} - z̃_{t₁})⁻¹` is `(t₁/t₂)^{k/2}` times the loop of `G_{t₁}` at the same sample
point, hence `max|L̃^{(k)}| ≤ max|L_{t₁}^{(k)}|`. -/
private theorem conArg_loopMax_tilde_le (n : ℕ) {E t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₁₂ : t₁ ≤ t₂)
    (ω : Sizes.SeqΩ d) (k : ℕ) :
    loopMax (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n t₂ ω)) (ztTilde E t₁ t₂) k
      ≤ loopMax (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n t₁ ω)) (spectralZ E t₁) k := by
  set r : ℝ := Real.sqrt (t₂ / t₁) with hr_def
  have hr1 : 1 ≤ r := by
    rw [hr_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((one_le_div h₁).2 h₁₂)
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hmul : r * Real.sqrt t₁ = Real.sqrt t₂ := by
    have hdiv : (0 : ℝ) ≤ t₂ / t₁ := le_of_lt (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
    rw [hr_def, ← Real.sqrt_mul hdiv t₁, div_mul_cancel₀ _ h₁.ne']
  have hH : blockMat (Sizes.seqHflow d n t₂ ω)
      = (r : ℂ) • blockMat (Sizes.seqHflow d n t₁ ω) := by
    ext i j
    simp only [blockMat, Matrix.submatrix_apply, Sizes.seqHflow_eq_smul, Matrix.smul_apply,
      smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hmul]
  refine loopMax_le fun I hσ ha => ?_
  rw [hH, ztTilde, ← hr_def, conArg_gloop_smul_mul hrC, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hle : r⁻¹ ^ (I.σ.zip I.a).length ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
  calc r⁻¹ ^ (I.σ.zip I.a).length * ‖gloop (d.L n) (d.W n)
        (blockMat (Sizes.seqHflow d n t₁ ω)) (spectralZ E t₁) I‖
      ≤ 1 * ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n t₁ ω)) (spectralZ E t₁) I‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n t₁ ω)) (spectralZ E t₁) I‖ :=
        one_mul _
    _ ≤ _ := norm_gloop_le_loopMax I hσ ha

/-! ## 3. The base case (5.6) -/

section BaseCase

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|⟨M E_b⟩| ≤ K` if every diagonal entry of `M` has modulus `≤ K` (`E_b = W⁻² 1_{𝓘_b}` has
total weight `1`, `sum_bw`). -/
private theorem conArg_norm_trace_mul_Eblk_le_of_diag
    (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (b : Z2 L) {K : ℝ}
    (hM : ∀ p, ‖M p p‖ ≤ K) : ‖trace (M * Eblk L W b)‖ ≤ K := by
  rw [Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((bw b p : ℝ) : ℂ)‖ ≤ ∑ p, K * bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (hM p) (bw_nonneg b p)
    _ = K := by rw [← Finset.mul_sum, sum_bw, mul_one]

/-- **The base case (5.6)**: `|G_{ii}| ≤ K` for all `i` gives `max|L^{(1)}| ≤ K`. -/
private theorem conArg_loopMax_one_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) {K : ℝ} (hK : ∀ i, ‖green H z i i‖ ≤ K) :
    loopMax L W H z 1 ≤ K := by
  refine loopMax_le fun I hσ ha => ?_
  obtain ⟨σ, a⟩ := I
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hσ
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp ha
  have e : gloop L W H z ⟨[s], [b]⟩ = trace (Gsig H z s * Eblk L W b) := by
    simp [gloop, gloopProd_cons, gloopProd_nil]
  rw [e]
  refine conArg_norm_trace_mul_Eblk_le_of_diag _ b fun p => ?_
  cases s
  · have h := Gsig_conjTranspose hH z true
    simp only [Bool.not_true] at h
    rw [← h, conjTranspose_apply, norm_star]
    exact hK p
  · exact hK p

/-- On `Ω = {‖G_u‖_max ≤ 2}` (`gMax ≤ 2`, fine index) every diagonal entry of the block-indexed
Green function is `≤ 2`: `blockMat` is a relabelling by the equivalence `splitEquiv`. -/
private theorem conArg_green_blockMat_diag_le {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : gMax E u M ≤ 2) (i : BlockIndex L W) :
    ‖green (blockMat M) (spectralZ E u) i i‖ ≤ 2 := by
  have hs : blockMat M - spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
      = (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
          (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext p q
    simp [blockMat, Matrix.one_apply]
  have e : green (blockMat M) (spectralZ E u)
      = (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹.submatrix
          (splitEquiv L W).symm (splitEquiv L W).symm := by
    unfold green
    rw [hs, Matrix.inv_submatrix_equiv]
  rw [e, Matrix.submatrix_apply]
  refine le_trans ?_ hM
  exact Finset.le_sup'
    (fun q : Idx L W × Idx L W => ‖(M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹
      q.1 q.2‖)
    (Finset.mem_univ ((splitEquiv L W).symm i, (splitEquiv L W).symm i))

end BaseCase

/-! ## 4. From the parameter `(σ, a)` to `max_{σ,a}` -/

/-- `#(Unit × (Fin k → Bool) × (Fin k → Z2 L)) = 2^k L^{2k} ≤ size^{2k}`. -/
private theorem conArg_card_le (n k : ℕ) :
    (Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ)
      ≤ ((d.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hc : Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      = 2 ^ k * (d.L n * d.L n) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have hL := d.three_le_L n
  have hW := d.W_pos n
  have h1 : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ hW
    nlinarith
  have h2 : 2 ≤ d.size n := le_trans (by nlinarith) h1
  have key : 2 ^ k * (d.L n * d.L n) ^ k ≤ d.size n ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left h2 k) (Nat.pow_le_pow_left h1 k)
  rw [hc]
  exact_mod_cast key

/-- A per-time bound for all loops of length `k` (parameter `(σ, a)`) is a per-time bound for
their maximum `loopMax` (the union over the `2^k L^{2k}` parameters is taken inside `P` by
`Path.stochDomAt_of_perTimeDomAt`). -/
private theorem conArg_loopMax_perTime {E t ζ : ℕ → ℝ} {k : ℕ}
    (h : Path.PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => loopAbs (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
      (fun n _ _ => ζ n)) :
    Path.PerTimeDomAt (Sizes.seqP d) d.size (U := fun _ => Unit)
      (fun n _ ω => loopMax (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (t n) ω))
        (spectralZ (E n) (t n)) k)
      (fun n _ _ => ζ n) := by
  have hU := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := ((2 * k : ℕ) : ℝ))
    (by positivity) (Eventually.of_forall fun n => conArg_card_le d n k) h
  intro τ hτ D hD
  filter_upwards [hU τ hτ D hD] with n hn u
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [Set.mem_ofPred_eq, loopMax] at hω
  obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hω
  exact ⟨((), x.1, x.2), hx⟩

/-! ## 5. `lem_ConArg` -/

/-- **`lem_ConArg`, per sequence.**  Under the hypotheses of `ConArgPin`
(`c < t₁ ≤ t₂ < 1`, bulk energy, `size → ∞`, and (`55`) at `t₁` for every loop length), for every
`k ≥ 1`, `1_Ω |𝓛_{t₂,σ,a}| ≺ (ℓ_{t₂}/ℓ_{t₁})^{2(k-1)} M_{t₂}^{-k+1}`, `Ω = {‖G_{t₂}‖_max ≤ 2}`.
Proof: `conArg_continuity_recursion` with
`a₁ = M_{t₁}⁻¹`, `a = (W²ℓ₁²η₂)⁻¹`, `K = |z_{t₂} - z̃|²/(Im z_{t₂} Im z̃) ≤ Cη₁/η₂`. -/
theorem conArg (κ c : ℝ) (E t₁ t₂ : ℕ → ℝ) : ConArgPin d κ c E t₁ t₂ := by
  intro hκ hE hc h₁ h₁₂ h₂ hsizeT h55 k hk
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsizeT
  obtain ⟨C, hC0, hC⟩ := ztTilde_arith hc hκ
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have ht₁0 : ∀ n, 0 < t₁ n := fun n => hc.trans (h₁ n)
  have ht₁1 : ∀ n, t₁ n < 1 := fun n => (h₁₂ n).trans_lt (h₂ n)
  have hW : ∀ n, (0 : ℝ) < d.W n := fun n => by exact_mod_cast d.W_pos n
  have hL1 : ∀ n, 1 ≤ d.L n := fun n => by have := d.three_le_L n; omega
  have hℓ1 : ∀ n, 0 < ellT (d.L n) (t₁ n) := fun n => (ellT_pos_le (hL1 n) (ht₁1 n)).1
  have hℓ2 : ∀ n, 0 < ellT (d.L n) (t₂ n) := fun n => (ellT_pos_le (hL1 n) (h₂ n)).1
  have hη1 : ∀ n, 0 < etaT (E n) (t₁ n) := fun n => etaT_pos (hE2 n) (ht₁1 n)
  have hη2 : ∀ n, 0 < etaT (E n) (t₂ n) := fun n => etaT_pos (hE2 n) (h₂ n)
  have hη12 : ∀ n, etaT (E n) (t₂ n) ≤ etaT (E n) (t₁ n) := fun n => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [h₁₂ n]) (spectralM_im_pos (hE2 n)).le
  -- the deterministic quantities
  set a : ℕ → ℝ := fun n =>
    ((d.W n : ℝ) ^ 2 * ellT (d.L n) (t₁ n) ^ 2 * etaT (E n) (t₂ n))⁻¹ with ha_def
  set a1 : ℕ → ℝ := fun n => (scaleM (d.L n) (d.W n) (E n) (t₁ n))⁻¹ with ha1_def
  set zz : ℕ → ℂ := fun n => spectralZ (E n) (t₂ n) with hzz_def
  set zw : ℕ → ℂ := fun n => ztTilde (E n) (t₁ n) (t₂ n) with hzw_def
  set K : ℕ → ℝ := fun n => ‖zz n - zw n‖ ^ 2 * ((zz n).im * (zw n).im)⁻¹ with hK_def
  have hzz : ∀ n, (zz n).im = etaT (E n) (t₂ n) := fun n => spectralZ_im _ _
  have harith := fun n => hC (E n) (t₁ n) (t₂ n) (h₁ n).le (h₁₂ n) (h₂ n).le (hE n)
  have hzw : ∀ n, etaT (E n) (t₁ n) ≤ (zw n).im := fun n => (harith n).2.2.2.1
  have hzw0 : ∀ n, 0 < (zw n).im := fun n => (hη1 n).trans_le (hzw n)
  have hA2 : ∀ n, 0 < (d.W n : ℝ) ^ 2 * ellT (d.L n) (t₁ n) ^ 2 * etaT (E n) (t₂ n) :=
    fun n => by have := hW n; have := hℓ1 n; have := hη2 n; positivity
  have hA1 : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (t₁ n) := fun n => by
    unfold scaleM; have := hW n; have := hℓ1 n; have := hη1 n; positivity
  have ha1 : ∀ n, 0 < a1 n := fun n => inv_pos.mpr (hA1 n)
  have ha1a : ∀ n, a1 n ≤ a n := fun n => by
    simp only [ha1_def, ha_def]
    refine inv_anti₀ (hA2 n) ?_
    unfold scaleM
    have := hW n; have := hℓ1 n
    exact mul_le_mul_of_nonneg_left (hη12 n) (by positivity)
  have hK0 : ∀ n, 0 ≤ K n := fun n =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hη2 n).le)
      (hzw0 n).le))
  have hK : ∀ n, K n * a1 n ≤ C * a n := by
    intro n
    have hsq := (harith n).2.1
    have hx : ‖zz n - zw n‖ ^ 2 ≤ C * etaT (E n) (t₁ n) * (zw n).im := by
      calc ‖zz n - zw n‖ ^ 2 ≤ C * etaT (E n) (t₁ n) ^ 2 := hsq
        _ = C * etaT (E n) (t₁ n) * etaT (E n) (t₁ n) := by ring
        _ ≤ C * etaT (E n) (t₁ n) * (zw n).im :=
            mul_le_mul_of_nonneg_left (hzw n) (mul_nonneg hC0.le (hη1 n).le)
    have hden : 0 < etaT (E n) (t₂ n) * (zw n).im := mul_pos (hη2 n) (hzw0 n)
    simp only [hK_def, ha1_def, ha_def, hzz]
    calc ‖zz n - zw n‖ ^ 2 * (etaT (E n) (t₂ n) * (zw n).im)⁻¹
          * (scaleM (d.L n) (d.W n) (E n) (t₁ n))⁻¹
        ≤ (C * etaT (E n) (t₁ n) * (zw n).im) * (etaT (E n) (t₂ n) * (zw n).im)⁻¹
          * (scaleM (d.L n) (d.W n) (E n) (t₁ n))⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx
            (inv_nonneg.mpr hden.le)) (inv_nonneg.mpr (hA1 n).le)
      _ = C * ((d.W n : ℝ) ^ 2 * ellT (d.L n) (t₁ n) ^ 2 * etaT (E n) (t₂ n))⁻¹ := by
          unfold scaleM
          have := hη1 n; have := hη2 n; have := hW n; have := hℓ1 n; have := hzw0 n
          field_simp
  have hNev : ∀ᶠ n : ℕ in atTop, (a1 n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by
    refine Eventually.of_forall fun n => ?_
    simp only [ha1_def, inv_inv]
    have hsz : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
      rw [Sizes.size_eq]; push_cast; ring
    rw [hsz]
    unfold scaleM
    have hℓL := (ellT_pos_le (hL1 n) (ht₁1 n)).2
    have hη1' : etaT (E n) (t₁ n) ≤ 1 := by
      unfold etaT
      have hm1 : (spectralM (E n)).im ≤ 1 := (le_abs_self _).trans
        ((Complex.abs_im_le_norm _).trans (norm_spectralM (by linarith [hE2 n])).le)
      have hm0 := (spectralM_im_pos (hE2 n)).le
      have : 1 - t₁ n ≤ 1 := by linarith [ht₁0 n]
      nlinarith [ht₁1 n]
    have := hW n
    calc (d.W n : ℝ) ^ 2 * ellT (d.L n) (t₁ n) ^ 2 * etaT (E n) (t₁ n)
        ≤ (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hℓ1 n).le hℓL 2)
            (by positivity)) hη1' (hη1 n).le (by positivity)
      _ = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := mul_one _
  -- the random families: `Y_j = 1_Ω max|L_{t₂}^{(j)}|`, `T_j = max|L̃^{(j)}|`
  have hH : ∀ n u ω, (blockMat (Sizes.seqHflow d n u ω)).IsHermitian := fun n u ω =>
    (Sizes.seqHflow_isHermitian d n u ω).submatrix _
  set Y : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → Sizes.SeqΩ d → ℝ := fun j n _ ω =>
    (if gMax (E n) (t₂ n) (Sizes.seqHflow d n (t₂ n) ω) ≤ 2 then 1 else 0) *
      loopMax (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (t₂ n) ω)) (zz n) j with hY
  set T : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → Sizes.SeqΩ d → ℝ := fun j n _ ω =>
    loopMax (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (t₂ n) ω)) (zw n) j with hT
  have hind : ∀ n ω, (0 : ℝ) ≤ if gMax (E n) (t₂ n) (Sizes.seqHflow d n (t₂ n) ω) ≤ 2
      then 1 else 0 := fun n ω => by split_ifs <;> norm_num
  have hY0 : ∀ j n u ω, 0 ≤ Y j n u ω := fun j n u ω =>
    mul_nonneg (hind n ω) (loopMax_nonneg _)
  have hT0 : ∀ j n u ω, 0 ≤ T j n u ω := fun j n u ω => loopMax_nonneg _
  have hTd : ∀ j, 1 ≤ j → Path.PerTimeDomAt (Sizes.seqP d) d.size (T j)
      (fun n _ _ => a1 n ^ (j - 1)) := fun j hj =>
    conArg_of_le_left (fun n _ ω => conArg_loopMax_tilde_le d n (ht₁0 n) (h₁₂ n) ω j)
      (conArg_loopMax_perTime d (h55 j hj))
  have hY1 : ∀ n u ω, Y 1 n u ω ≤ 2 := by
    intro n u ω
    simp only [hY]
    split_ifs with hω
    · rw [one_mul]
      exact conArg_loopMax_one_le (hH n _ ω) fun i => conArg_green_blockMat_diag_le hω i
    · norm_num
  have hodd : ∀ l, 1 ≤ l → ∀ n u ω,
      Y (2 * l + 1) n u ω ^ 2 ≤ Y (2 * l) n u ω * Y (2 * l + 2) n u ω := by
    intro l hl n u ω
    simp only [hY]
    split_ifs
    · simp only [one_mul]
      exact loopMax_odd_sq_le (hH n _ ω) hl
    · simp
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ n u ω, Y (2 * m) n u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) n u ω + K n * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) n u ω * T (p * (2 * (m - l) - 1)) n u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp n u ω
    simp only [hY, hT]
    split_ifs with hω
    · simp only [one_mul]
      have hz : 0 < (zz n).im := by rw [hzz]; exact hη2 n
      refine (loopMax_two_mul_le_tilde (hH n _ ω) hz (hzw0 n) hm hp).trans (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (loopMax_nonneg _)
  have hmain := conArg_continuity_recursion (P := Sizes.seqP d) hsize hY0 hT0 ha1 ha1a hK0
    hC0.le hK hNev hTd hY1 hodd hrec
  -- back to the parameter `(σ, a)` and the paper's second form of the right side
  have hRHS : ∀ n, a n ^ (k - 1) = (ellT (d.L n) (t₂ n) / ellT (d.L n) (t₁ n)) ^ (2 * (k - 1)) *
      (scaleM (d.L n) (d.W n) (E n) (t₂ n))⁻¹ ^ (k - 1) := by
    intro n
    rw [pow_mul, ← mul_pow]
    congr 1
    simp only [ha_def]
    unfold scaleM
    have := hη2 n; have := hW n; have := hℓ1 n; have := hℓ2 n
    field_simp
  intro τ hτ D hD
  filter_upwards [hmain k hk τ hτ D hD] with n hn p
  refine (measure_mono ?_).trans (hn ())
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hRHS n]
  refine hω.trans_le ?_
  simp only [hY]
  exact mul_le_mul_of_nonneg_left
    (norm_gloop_le_loopMax (loopOf p.2.1 p.2.2) (by simp [loopOf]) (by simp [loopOf]))
    (hind n ω)

end RBM.Ind
