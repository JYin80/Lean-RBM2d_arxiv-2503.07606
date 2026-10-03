/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridGoodN
import RBM2D.Induction.KcalDecay

/-!
# The high-probability grid good event `gridGoodN`

The result is the statement `GridGoodN` (`RBM2D.Induction.GridGoodN`), proved with no hypothesis
added:

`theorem gridGoodN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : GridGoodN d κ c τ E s v t K`.

Paper: arXiv:2503.07606, Section 5: the stopping time of `lem:STOeq_NQ` and `lem:STOeq_Qt`,
`lem_decayLoop`, `lem_BcalE`.  The argument parallels the one-dimensional formalization (there the
inputs are `StochDom` on grid arrays, here they are `PerTimeDomAt` per time and the transfer law
replaces the array) and the `d = 2` template `goodEvent_grid` (`RBM2D.Path.GoodEventClose`).

1. Every clause of `GoodSetN` at level `Γ = N^ε` is a per-time statement on `[s, t]`: (G1)-(G4) are
   the four `PT` hypotheses (the levels of `STOeqPT`), (Dec) is `DecayLoopPT`, (D1)-(D4), (V) are
   the five conjuncts of `bcalEPT'`, with `Σ_{m<k} Ξ_m ≤ (k-1) Γ Φ`; the additive
   `N^ε W^{-D''}`, `D'' = D' + ε/c`, is absorbed into `W^{-D'}` through `Bandwidth`
   (`gge_absorb`, `gge_mem_goodSetN`).
2. At a fixed time `u ∈ [s n, t n]` the failure of `GoodSetN` is contained in the union of eleven
   groups of atomic per-time failure events (`GgeR1`-`GgeR10`), each group indexed by the finitely
   many lengths, signs and labels of its clause: at most `(2k+2) (2N)^{2k+2}` events per group
   (`2^j (L²)^j ≤ (2N)^j`, `L² ≤ N`; the count per length is `L^{2(2k+2)}`,
   the exponent stays polynomial in `N`), each of probability `≤ N^{-D₂}` eventually
   (`gge_perTime`).
3. The grid states `pathH d s v K n j` have the law of the flow `Sizes.seqHflow` at the grid time
   `u_j ∈ [s n, v n] ⊆ [s n, t n]` (`map_pathH_eq`) and `GoodSetN` is measurable
   (`measurableGoodSetN`), so the union over `j ≤ K n` costs the factor `K n + 1 ≤ N^C`
   (`gge_grid_union`).
4. `D₂ = D + max C 0 + (2k+2) + 1` is chosen after `D, C, k`; the total is `≤ N^{-D}` as soon as
   `11 (2k+2) 2^{2k+2} ≤ N`, eventually by `SizeTendsto` (`gge_arith`).

Result: `gridGoodN`.  Every other declaration is `private` with the prefix `gge` / `Gge`, except
the public restatements `GridGoodEvent_*` of Section 7.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Union bounds, counts and arithmetic -/

section Helpers

/-- The union over a finite family of atomic events: if every `R v` has probability `≤ x`, the
failure of "no `R v` occurs" has probability `≤ #V · x`. -/
private theorem gge_exists_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : Type*}
    [Fintype V] (R : V → Ω → Prop) {x : ℝ}
    (h : ∀ v, P {ω | R v ω} ≤ ENNReal.ofReal x) :
    P {ω | ¬ ∀ v, ¬ R v ω} ≤ ENNReal.ofReal ((Fintype.card V : ℝ) * x) := by
  have hset : {ω | ¬ ∀ v, ¬ R v ω} = ⋃ v, {ω | R v ω} := by
    ext ω; simp
  rw [hset]
  calc P (⋃ v, {ω | R v ω}) ≤ ∑ v, P {ω | R v ω} := measure_iUnion_fintype_le P _
    _ ≤ ∑ _v : V, ENNReal.ofReal x := Finset.sum_le_sum fun v _ => h v
    _ = ENNReal.ofReal ((Fintype.card V : ℝ) * x) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The union over a finite set `S` of indices: if each `¬ Q i` has probability `≤ y`, the failure
of "`Q i` for every `i ∈ S`" has probability `≤ #S · y`. -/
private theorem gge_forall_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    (S : Finset ι) (Q : ι → Ω → Prop) {y : ℝ}
    (h : ∀ i ∈ S, P {ω | ¬ Q i ω} ≤ ENNReal.ofReal y) :
    P {ω | ¬ ∀ i ∈ S, Q i ω} ≤ ENNReal.ofReal ((S.card : ℝ) * y) := by
  have hset : {ω | ¬ ∀ i ∈ S, Q i ω} = ⋃ i ∈ S, {ω | ¬ Q i ω} := by
    ext ω; simp
  rw [hset]
  calc P (⋃ i ∈ S, {ω | ¬ Q i ω}) ≤ ∑ i ∈ S, P {ω | ¬ Q i ω} := measure_biUnion_finset_le S _
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal y := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((S.card : ℝ) * y) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- The union over a finite set `S` of indices, atomic form: if each `R i` has probability `≤ y`,
the failure of "no `R i` occurs, `i ∈ S`" has probability `≤ #S · y`. -/
private theorem gge_forall_le' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    (S : Finset ι) (R : ι → Ω → Prop) {y : ℝ}
    (h : ∀ i ∈ S, P {ω | R i ω} ≤ ENNReal.ofReal y) :
    P {ω | ¬ ∀ i ∈ S, ¬ R i ω} ≤ ENNReal.ofReal ((S.card : ℝ) * y) :=
  gge_forall_le S (fun i ω => ¬ R i ω) (fun i hi => by simpa using h i hi)

/-- The union of eleven sets, each of probability `≤ y`. -/
private theorem gge_union11 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ G : Set Ω} {y : ℝ}
    (h₁ : P A₁ ≤ ENNReal.ofReal y) (h₂ : P A₂ ≤ ENNReal.ofReal y)
    (h₃ : P A₃ ≤ ENNReal.ofReal y) (h₄ : P A₄ ≤ ENNReal.ofReal y)
    (h₅ : P A₅ ≤ ENNReal.ofReal y) (h₆ : P A₆ ≤ ENNReal.ofReal y)
    (h₇ : P A₇ ≤ ENNReal.ofReal y) (h₈ : P A₈ ≤ ENNReal.ofReal y)
    (h₉ : P A₉ ≤ ENNReal.ofReal y) (h₁₀ : P A₁₀ ≤ ENNReal.ofReal y)
    (h₁₁ : P A₁₁ ≤ ENNReal.ofReal y)
    (hsub : G ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆ ∪ A₇ ∪ A₈ ∪ A₉ ∪ A₁₀ ∪ A₁₁) :
    P G ≤ ENNReal.ofReal (11 * y) := by
  have step : ∀ (A B : Set Ω) (a b : ℝ≥0∞), P A ≤ a → P B ≤ b → P (A ∪ B) ≤ a + b :=
    fun A B a b ha hb => (measure_union_le A B).trans (add_le_add ha hb)
  have h := (measure_mono (μ := P) hsub).trans
    (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ (step _ _ _ _
      (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈)
      h₉) h₁₀) h₁₁)
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11)]
  have h11 : ENNReal.ofReal (11 : ℝ) = 11 := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  rw [h11]; ring

/-- `#Z2 L = L²`. -/
private theorem gge_card_Z2 (L : ℕ) [NeZero L] : Fintype.card (Z2 L) = L ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, pow_two]

/-- The labels and signs of a length-`j` loop: `2^j (L²)^j ≤ (2N)^j` when `L² ≤ N`. -/
private theorem gge_card_lab (L : ℕ) [NeZero L] (j : ℕ) {N : ℕ} (hLN : L ^ 2 ≤ N) :
    Fintype.card ((Fin j → Bool) × (Fin j → Z2 L)) ≤ (2 * N) ^ j := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, gge_card_Z2, ← mul_pow]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hLN) j

/-- The labels and signs of a `(σ, a, a')`: `2^j (L²)^{2j} ≤ (2N)^{2j}` when `L² ≤ N`. -/
private theorem gge_card_lab2 (L : ℕ) [NeZero L] (j : ℕ) {N : ℕ} (hLN : L ^ 2 ≤ N) :
    Fintype.card ((Fin j → Bool) × (Fin j → Z2 L) × (Fin j → Z2 L)) ≤ (2 * N) ^ (2 * j) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, gge_card_Z2]
  calc 2 ^ j * ((L ^ 2) ^ j * (L ^ 2) ^ j) = (2 * (L ^ 2 * L ^ 2)) ^ j := by
        rw [mul_pow, mul_pow]
    _ ≤ ((2 * N) ^ 2) ^ j := by
        refine Nat.pow_le_pow_left ?_ j
        have := Nat.mul_le_mul hLN hLN
        nlinarith
    _ = (2 * N) ^ (2 * j) := by rw [← pow_mul, mul_comm]

/-- `N^ε W^{-(D' + ε/c)} ≤ W^{-D'}` from `N^c ≤ W` (`Bandwidth`). -/
private theorem gge_absorb {N W c ε D' : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (hε : 0 < ε) (hNW : N ^ c ≤ W) :
    N ^ ε * W ^ (-(D' + ε / c)) ≤ W ^ (-D') := by
  have h1 : N ^ ε ≤ W ^ (ε / c) := by
    have : N ^ ε = (N ^ c) ^ (ε / c) := by
      rw [← Real.rpow_mul hN]; congr 1; field_simp
    rw [this]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN c) hNW (div_nonneg hε.le hc.le)
  calc N ^ ε * W ^ (-(D' + ε / c)) ≤ W ^ (ε / c) * W ^ (-(D' + ε / c)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW.le _)
    _ = W ^ (-D') := by rw [← Real.rpow_add hW]; congr 1; ring

end Helpers

section Helpers2

/-- The final arithmetic: `(K + 1) · 11 (2k+2) (2N)^{2k+2} N^{-D₂} ≤ N^{-D}` for
`D₂ = D + max C 0 + (2k+2) + 1`, once `K + 1 ≤ N^C`, `1 ≤ N` and `11 (2k+2) 2^{2k+2} ≤ N`. -/
private theorem gge_arith {N Kp C D : ℝ} {k : ℕ} (hN : 1 ≤ N) (hKp : Kp ≤ N ^ C)
    (hcn : 11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2) ≤ N) :
    Kp * (11 * ((2 * (k : ℝ) + 2) * (2 * N) ^ (2 * k + 2) *
      N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1)))) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hC : N ^ C ≤ N ^ (max C 0) := Real.rpow_le_rpow_of_exponent_le hN (le_max_left _ _)
  have hy0 : 0 ≤ 11 * ((2 * (k : ℝ) + 2) * (2 * N) ^ (2 * k + 2) *
      N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1))) := by positivity
  refine (mul_le_mul_of_nonneg_right (hKp.trans hC) hy0).trans ?_
  have hexp : N ^ (max C 0) * N ^ ((2 * k + 2 : ℕ) : ℝ) *
      N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1)) = N ^ (-D) * N⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1; ring
  have hpow : (2 * N) ^ (2 * k + 2) = 2 ^ (2 * k + 2) * N ^ ((2 * k + 2 : ℕ) : ℝ) := by
    rw [mul_pow, Real.rpow_natCast]
  calc N ^ (max C 0) * (11 * ((2 * (k : ℝ) + 2) * (2 * N) ^ (2 * k + 2) *
        N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1))))
      = (11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2)) * (N ^ (max C 0) *
          N ^ ((2 * k + 2 : ℕ) : ℝ) * N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1))) := by
        rw [hpow]; ring
    _ = (11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2)) * (N ^ (-D) * N⁻¹) := by rw [hexp]
    _ ≤ N ^ (-D) := by
        have hT : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
        have h1 : (11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2)) * N⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hcn
        calc (11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2)) * (N ^ (-D) * N⁻¹)
            = N ^ (-D) * ((11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2)) * N⁻¹) := by ring
          _ ≤ N ^ (-D) * 1 := mul_le_mul_of_nonneg_left h1 hT
          _ = N ^ (-D) := mul_one _

end Helpers2

/-! ## 2. The atomic failure events at a fixed time and the deterministic step

Each `GgeR_i` is the failure of one per-time input at the matrix `M`: `Γ · ζ < ξ`, where `Γ` is the
level `N^ε` of `PerTimeDomAt` and `(ξ, ζ)` are the sides of the corresponding per-time
statement (the four `PT` hypotheses, `DecayLoopPT`, the five conjuncts of `bcalEPT'`). -/

section Events

/-- (G1) `Ξ^{(𝓛)}_{2k+2} > Γ Λ`. -/
private def GgeR1 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (Γ Λ : ℝ) : Prop :=
  Γ * Λ < xiL L W E u M (2 * k + 2)

/-- (G2) `Ξ^{(𝓛-𝒦)}_m > Γ Φ`. -/
private def GgeR2 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (m : ℕ) (Γ Φ : ℝ) : Prop :=
  Γ * Φ < xiLK L W E u M m

/-- (G3) `Ξ_m Ξ_{k-m+2} M^{-1} > Γ Φ`. -/
private def GgeR3 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k m : ℕ) (Γ Φ : ℝ) : Prop :=
  Γ * Φ < xiLK L W E u M m * xiLK L W E u M (k - m + 2) * (scaleM L W E u)⁻¹

/-- (G4) `Ξ^{(𝓛)}_{k+1} > Γ Φ`. -/
private def GgeR4 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (Γ Φ : ℝ) : Prop :=
  Γ * Φ < xiL L W E u M (k + 1)

/-- (Dec) the far-label decay of `𝓛` and `𝓛 - 𝒦` at level `Γ W^{-D''}` fails. -/
private def GgeRd (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (τ' D'' Γ : ℝ) {j : ℕ} (σ : Fin j → Bool) (a : Fin j → Z2 L) : Prop :=
  Γ * (W : ℝ) ^ (-D'') < (loopAbs L W E u M σ a + lkGen L W E u M σ a) *
    (if ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) then 1 else 0)

/-- (D1) `‖[𝒦∼(𝓛-𝒦)]^l‖` exceeds `Γ (Σ_{m<k} Ξ_m) M^{-k} η^{-1}` (`bcalEPT'` (i)). -/
private def GgeR5 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k l : ℕ) (Γ : ℝ) (σ : Fin k → Bool) (a : Fin k → Z2 L) : Prop :=
  Γ * ((∑ m ∈ Finset.Ico 1 k, xiLK L W E u M m) * (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) <
    ‖ksimLK L W E u M l (loopOf σ a)‖

/-- (D2) `‖𝓔^{LK×LK}‖` exceeds its `bcalEPT'` (ii) bound. -/
private def GgeR6 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (D'' Γ : ℝ) (σ : Fin k → Bool) (a : Fin k → Z2 L) : Prop :=
  Γ * ((∑ m ∈ Finset.Icc 2 k, xiLK L W E u M m * xiLK L W E u M (k - m + 2) *
        (scaleM L W E u)⁻¹) * (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ + (W : ℝ) ^ (-D'')) <
    ‖elklkN L W E u M (loopOf σ a)‖

/-- (D3) `‖𝓔^{(G̃)}‖` exceeds its `bcalEPT'` (iii) bound. -/
private def GgeR7 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (D'' Γ : ℝ) (σ : Fin k → Bool) (a : Fin k → Z2 L) : Prop :=
  Γ * (xiL L W E u M (k + 1) * (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ + (W : ℝ) ^ (-D'')) <
    ‖egtN L W E u M (loopOf σ a)‖

/-- (D4) `‖𝓔⊗𝓔‖` exceeds its `bcalEPT'` (iv) bound. -/
private def GgeR8 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (D'' Γ : ℝ) (σ : Fin k → Bool) (a a' : Fin k → Z2 L) : Prop :=
  Γ * (xiL L W E u M (2 * k + 2) * (scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹ +
      (W : ℝ) ^ (-D'')) < ‖eeN L W E u M σ a a'‖

/-- (V, first conjunct) the far-label decay of `Σ_{l ≥ 3} 𝒦∼(𝓛-𝒦) + 𝓔^{LK×LK} + 𝓔^{(G̃)}` fails. -/
private def GgeR9 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (τ' D'' Γ : ℝ) (σ : Fin k → Bool) (a : Fin k → Z2 L) : Prop :=
  Γ * (W : ℝ) ^ (-D'') <
    (‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ + ‖elklkN L W E u M (loopOf σ a)‖ +
        ‖egtN L W E u M (loopOf σ a)‖) *
      (if ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) then 1 else 0)

/-- (V, second conjunct) the far-label decay of `𝓔⊗𝓔` fails. -/
private def GgeR10 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (k : ℕ) (τ' D'' Γ : ℝ) (σ : Fin k → Bool) (a a' : Fin k → Z2 L) : Prop :=
  Γ * (W : ℝ) ^ (-D'') <
    ‖eeN L W E u M σ a a'‖ *
      (if ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L (Fin.append a a') : ℝ) then 1 else 0)

/-- **The deterministic step**: if none of the per-time failure events occurs at the Hermitian
matrix `M`, then `M ∈ GoodSetN` (with `Γ W^{-D''} ≤ W^{-D'}`, the absorption of `Bandwidth`). -/
private theorem gge_mem_goodSetN {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} {k : ℕ} {Γ Λ Φ τ' D' D'' : ℝ}
    (hM : M.IsHermitian) (hΓ : 0 ≤ Γ) (hMpos : 0 < scaleM L W E u) (hηpos : 0 < etaT E u)
    (hab : Γ * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D'))
    (g1 : ¬ GgeR1 L W E u M k Γ Λ)
    (g2 : ∀ m ∈ Finset.Ico 1 k, ¬ GgeR2 L W E u M m Γ Φ)
    (g3 : ∀ m ∈ Finset.Icc 2 k, ¬ GgeR3 L W E u M k m Γ Φ)
    (g4 : ¬ GgeR4 L W E u M k Γ Φ)
    (gd : ∀ j ∈ Finset.Icc 1 (2 * k + 2), ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ¬ GgeRd L W E u M τ' D'' Γ σ a)
    (g5 : ∀ l ∈ Finset.Icc 3 k, ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ¬ GgeR5 L W E u M k l Γ σ a)
    (g6 : ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L), ¬ GgeR6 L W E u M k D'' Γ σ a)
    (g7 : ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L), ¬ GgeR7 L W E u M k D'' Γ σ a)
    (g8 : ∀ (σ : Fin k → Bool) (a a' : Fin k → Z2 L), ¬ GgeR8 L W E u M k D'' Γ σ a a')
    (g9 : ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L), ¬ GgeR9 L W E u M k τ' D'' Γ σ a)
    (g10 : ∀ (σ : Fin k → Bool) (a a' : Fin k → Z2 L),
      ¬ GgeR10 L W E u M k τ' D'' Γ σ a a') :
    M ∈ GoodSetN L W E u k Γ Λ Φ τ' D' := by
  have hX : 0 ≤ (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hMpos.le _)) (inv_nonneg.2 hηpos.le)
  have hX2 : 0 ≤ (scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹ :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hMpos.le _)) (inv_nonneg.2 hηpos.le)
  have hS1 : ∑ m ∈ Finset.Ico 1 k, xiLK L W E u M m ≤ ((k - 1 : ℕ) : ℝ) * (Γ * Φ) := by
    have := Finset.sum_le_card_nsmul (Finset.Ico 1 k) (fun m => xiLK L W E u M m) (Γ * Φ)
      (fun m hm => not_lt.1 (g2 m hm))
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  have hS2 : ∑ m ∈ Finset.Icc 2 k, xiLK L W E u M m * xiLK L W E u M (k - m + 2) *
      (scaleM L W E u)⁻¹ ≤ ((k - 1 : ℕ) : ℝ) * (Γ * Φ) := by
    have := Finset.sum_le_card_nsmul (Finset.Icc 2 k)
      (fun m => xiLK L W E u M m * xiLK L W E u M (k - m + 2) * (scaleM L W E u)⁻¹) (Γ * Φ)
      (fun m hm => not_lt.1 (g3 m hm))
    rwa [Nat.card_Icc, nsmul_eq_mul, show k + 1 - 2 = k - 1 by omega] at this
  have hxL1 : xiL L W E u M (k + 1) ≤ Γ * Φ := not_lt.1 g4
  have hxL2 : xiL L W E u M (2 * k + 2) ≤ Γ * Λ := not_lt.1 g1
  refine ⟨hM, hxL2, ?_, ?_, hxL1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm1 hmk
    exact not_lt.1 (g2 m (Finset.mem_Ico.2 ⟨hm1, hmk⟩))
  · intro m hm2 hmk
    exact not_lt.1 (g3 m (Finset.mem_Icc.2 ⟨hm2, hmk⟩))
  · intro j hj1 hj2 σ a hfar
    have h := not_lt.1 (gd j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) σ a)
    simp only [hfar, ↓reduceIte, mul_one] at h
    exact h.trans hab
  · intro l hl3 hlk σ a
    have h := not_lt.1 (g5 l (Finset.mem_Icc.2 ⟨hl3, hlk⟩) σ a)
    refine h.trans ?_
    calc Γ * ((∑ m ∈ Finset.Ico 1 k, xiLK L W E u M m) * (scaleM L W E u ^ k)⁻¹ *
          (etaT E u)⁻¹)
        = Γ * ((∑ m ∈ Finset.Ico 1 k, xiLK L W E u M m) *
            ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) := by ring
      _ ≤ Γ * ((((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS1 hX) hΓ
      _ = Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) := by ring
  · intro σ a
    have h := not_lt.1 (g6 σ a)
    refine h.trans ?_
    calc Γ * ((∑ m ∈ Finset.Icc 2 k, xiLK L W E u M m * xiLK L W E u M (k - m + 2) *
            (scaleM L W E u)⁻¹) * (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ + (W : ℝ) ^ (-D''))
        = Γ * ((∑ m ∈ Finset.Icc 2 k, xiLK L W E u M m * xiLK L W E u M (k - m + 2) *
            (scaleM L W E u)⁻¹) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) +
          Γ * (W : ℝ) ^ (-D'') := by ring
      _ ≤ Γ * ((((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) +
          (W : ℝ) ^ (-D') :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS2 hX) hΓ) hab
      _ = Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) +
          (W : ℝ) ^ (-D') := by ring
  · intro σ a
    have h := not_lt.1 (g7 σ a)
    refine h.trans ?_
    calc Γ * (xiL L W E u M (k + 1) * (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ + (W : ℝ) ^ (-D''))
        = Γ * (xiL L W E u M (k + 1) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) +
          Γ * (W : ℝ) ^ (-D'') := by ring
      _ ≤ Γ * ((Γ * Φ) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) + (W : ℝ) ^ (-D') :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxL1 hX) hΓ) hab
      _ = Γ * (Γ * Φ) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D') := by ring
  · intro σ a a'
    have h := not_lt.1 (g8 σ a a')
    refine h.trans ?_
    calc Γ * (xiL L W E u M (2 * k + 2) * (scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹ +
          (W : ℝ) ^ (-D''))
        = Γ * (xiL L W E u M (2 * k + 2) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹)) +
          Γ * (W : ℝ) ^ (-D'') := by ring
      _ ≤ Γ * ((Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹)) + (W : ℝ) ^ (-D') :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxL2 hX2) hΓ) hab
      _ = Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D') := by
          ring
  · intro σ a hfar
    have h := not_lt.1 (g9 σ a)
    simp only [hfar, ↓reduceIte, mul_one] at h
    exact h.trans hab
  · intro σ a a' hfar
    have h := not_lt.1 (g10 σ a a')
    simp only [hfar, ↓reduceIte, mul_one] at h
    exact h.trans hab

end Events

/-! ## 3. The per-time union bound -/

section PerTime

variable (d : Sizes)

/-- **The per-time union bound.**  At every time `u ∈ [s n, t n]`, eventually in `n`, the
probability that `Sizes.seqHflow d n u ω` leaves `GoodSetN` at level `Γ = N^ε` is at most
`11 (2k+2) (2N)^{2k+2} N^{-D₂}` for every `D₂ > 0`: the eleven groups of per-time failure
events (`GgeR1`-`GgeR10`, with `GgeRd` the decay clause) each have `≤ (2k+2) (2N)^{2k+2}` members of
probability `≤ N^{-D₂}` (`L² ≤ N`), and outside their union `gge_mem_goodSetN` applies. -/
private theorem gge_perTime (κ c τ : ℝ) (E s t : ℕ → ℝ)
    (hmain : MainIndHyp d κ c τ E s t) (hK : KboundConcl κ) (hKd : KcalDecay κ)
    (hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (hloc : Step2LocalPT d E s t)
    (hdec : Step2DecayPT d E s t) (hdl : DecayLoopPT d E s t)
    (k : ℕ) (hk : 2 ≤ k) (Λ Φ : ℕ → ℝ)
    (hPΛ : PT d s t
      (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (2 * k + 2))
      (fun n _ _ => Λ n))
    (hPΦ1 : ∀ m, 1 ≤ m → m < k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m)
        (fun n _ _ => Φ n))
    (hPΦ2 : ∀ m, 2 ≤ m → m ≤ k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m *
          xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k - m + 2) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹)
        (fun n _ _ => Φ n))
    (hPΦ3 : PT d s t
      (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k + 1))
      (fun n _ _ => Φ n))
    (ε : ℝ) (hε : 0 < ε) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') (D₂ : ℝ)
    (hD₂ : 0 < D₂) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s t n,
      Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
          GoodSetN (d.L n) (d.W n) (E n) u k (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'} ≤
        ENNReal.ofReal (11 * ((2 * (k : ℝ) + 2) * (2 * ((d.size n : ℕ) : ℝ)) ^ (2 * k + 2) *
          ((d.size n : ℕ) : ℝ) ^ (-D₂))) := by
  obtain ⟨hi, hii, hiii, hiv, hv⟩ := bcalEPT' d κ c τ E s t hmain hK hKd hV hloc hdec hdl k hk
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, -, hs0, -, ht1, -, hband, -⟩ := hmain'
  have hD''0 : 0 < D' + ε / c := by positivity
  have eΛ := hPΛ ε hε D₂ hD₂
  have eΦ1 := (Filter.eventually_all_finset (Finset.Ico 1 k)).2 (fun m hm =>
    hPΦ1 m (Finset.mem_Ico.1 hm).1 (Finset.mem_Ico.1 hm).2 ε hε D₂ hD₂)
  have eΦ2 := (Filter.eventually_all_finset (Finset.Icc 2 k)).2 (fun m hm =>
    hPΦ2 m (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2 ε hε D₂ hD₂)
  have eΦ3 := hPΦ3 ε hε D₂ hD₂
  have eDec := (Filter.eventually_all_finset (Finset.Icc 1 (2 * k + 2))).2 (fun j hj =>
    hdl j (Finset.mem_Icc.1 hj).1 τ' hτ' (D' + ε / c) hD''0 ε hε D₂ hD₂)
  have eD1 := (Filter.eventually_all_finset (Finset.Icc 3 k)).2 (fun l hl =>
    hi l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2 ε hε D₂ hD₂)
  have eD2 := hii (D' + ε / c) hD''0 ε hε D₂ hD₂
  have eD3 := hiii (D' + ε / c) hD''0 ε hε D₂ hD₂
  have eD4 := hiv (D' + ε / c) hD''0 ε hε D₂ hD₂
  have eV1 := (hv τ' hτ' (D' + ε / c) hD''0).1 ε hε D₂ hD₂
  have eV2 := (hv τ' hτ' (D' + ε / c) hD''0).2 ε hε D₂ hD₂
  filter_upwards [eΛ, eΦ1, eΦ2, eΦ3, eDec, eD1, eD2, eD3, eD4, eV1, eV2, hband] with
    n e1 e2 e3 e4 ed e5 e6 e7 e8 e9 e10 hbn u
  -- sizes and scales
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  have hN1 : (1 : ℝ) ≤ Nn := GoodEvent_one_le_size (d := d) n
  have hN0 : 0 < Nn := by linarith
  have hx : 0 ≤ Nn ^ (-D₂) := Real.rpow_nonneg hN0.le _
  have hLN : (d.L n) ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]; exact Nat.le_mul_of_pos_left _ (pow_pos (d.W_pos n) 2)
  have hNn1 : 1 ≤ d.size n := Nat.one_le_cast.1 hN1
  have hBn1 : (1 : ℝ) ≤ (2 * Nn) ^ (2 * k + 2) := one_le_pow₀ (by linarith)
  have hB0 : (0 : ℝ) ≤ (2 * Nn) ^ (2 * k + 2) := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcard1 : ∀ j, j ≤ 2 * k + 2 →
      (Fintype.card ((Fin j → Bool) × (Fin j → Z2 (d.L n))) : ℝ) ≤ (2 * Nn) ^ (2 * k + 2) := by
    intro j hj
    have h1 := (gge_card_lab (d.L n) j hLN).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2 * d.size n) hj)
    have h2 : (Fintype.card ((Fin j → Bool) × (Fin j → Z2 (d.L n))) : ℝ) ≤
        (((2 * d.size n) ^ (2 * k + 2) : ℕ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  have hcard2 : (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n))) :
      ℝ) ≤ (2 * Nn) ^ (2 * k + 2) := by
    have h1 := (gge_card_lab2 (d.L n) k hLN).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2 * d.size n) (by omega : 2 * k ≤ 2 * k + 2))
    have h2 : (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n))) :
        ℝ) ≤ (((2 * d.size n) ^ (2 * k + 2) : ℕ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  have hE2 : |E n| < 2 := by have := hE n; linarith
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 n)
  have hLn : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hLn (d.W_pos n) hE2 hu1
  have hηpos : 0 < etaT (E n) u := etaT_pos hE2 hu1
  have hab : Nn ^ ε * (d.W n : ℝ) ^ (-(D' + ε / c)) ≤ (d.W n : ℝ) ^ (-D') :=
    gge_absorb hN0.le (by exact_mod_cast d.W_pos n) hc hε hbn
  have hΓ : 0 ≤ Nn ^ ε := Real.rpow_nonneg hN0.le _
  -- the common bound `y`
  set y : ℝ := (2 * (k : ℝ) + 2) * (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂) with hy
  have hBx : (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂) ≤ y := by
    have h0 : 0 ≤ (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂) := mul_nonneg hB0 hx
    calc (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂) = 1 * ((2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) := by
          ring
      _ ≤ (2 * (k : ℝ) + 2) * ((2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = y := by rw [hy]; ring
  have hxy : Nn ^ (-D₂) ≤ y := by
    calc Nn ^ (-D₂) = 1 * Nn ^ (-D₂) := (one_mul _).symm
      _ ≤ (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂) := mul_le_mul_of_nonneg_right hBn1 hx
      _ ≤ y := hBx
  have hcx : ∀ c' : ℝ, c' ≤ 2 * (k : ℝ) + 2 → c' * Nn ^ (-D₂) ≤ y := by
    intro c' hc'
    calc c' * Nn ^ (-D₂) ≤ (2 * (k : ℝ) + 2) * Nn ^ (-D₂) := mul_le_mul_of_nonneg_right hc' hx
      _ = ((2 * (k : ℝ) + 2) * Nn ^ (-D₂)) * 1 := (mul_one _).symm
      _ ≤ ((2 * (k : ℝ) + 2) * Nn ^ (-D₂)) * (2 * Nn) ^ (2 * k + 2) :=
          mul_le_mul_of_nonneg_left hBn1 (by positivity)
      _ = y := by rw [hy]; ring
  have hcBx : ∀ c' : ℝ, c' ≤ 2 * (k : ℝ) + 2 →
      c' * ((2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) ≤ y := by
    intro c' hc'
    calc c' * ((2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂))
        ≤ (2 * (k : ℝ) + 2) * ((2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) :=
          mul_le_mul_of_nonneg_right hc' (mul_nonneg hB0 hx)
      _ = y := by rw [hy]; ring
  have hfib : ∀ c' : ℝ, c' ≤ (2 * Nn) ^ (2 * k + 2) → c' * Nn ^ (-D₂) ≤ y :=
    fun c' hc' => (mul_le_mul_of_nonneg_right hc' hx).trans hBx
  -- the eleven groups
  have b1 : Sizes.seqP d {ω | GgeR1 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k
      (Nn ^ ε) (Λ n)} ≤ ENNReal.ofReal y :=
    (e1 u).trans (ENNReal.ofReal_le_ofReal hxy)
  have b2 : Sizes.seqP d {ω | ¬ ∀ m ∈ Finset.Ico 1 k,
      ¬ GgeR2 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m (Nn ^ ε) (Φ n)} ≤
      ENNReal.ofReal y := by
    refine (gge_forall_le' (P := Sizes.seqP d) (Finset.Ico 1 k)
      (fun m ω => GgeR2 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m (Nn ^ ε) (Φ n))
      (fun m hm => e2 m hm u)).trans (ENNReal.ofReal_le_ofReal (hcx _ ?_))
    rw [Nat.card_Ico]
    have : ((k - 1 : ℕ) : ℝ) ≤ k := Nat.cast_le.2 (Nat.sub_le _ _)
    linarith
  have b3 : Sizes.seqP d {ω | ¬ ∀ m ∈ Finset.Icc 2 k,
      ¬ GgeR3 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k m (Nn ^ ε) (Φ n)} ≤
      ENNReal.ofReal y := by
    refine (gge_forall_le' (P := Sizes.seqP d) (Finset.Icc 2 k)
      (fun m ω => GgeR3 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k m (Nn ^ ε) (Φ n))
      (fun m hm => e3 m hm u)).trans (ENNReal.ofReal_le_ofReal (hcx _ ?_))
    rw [Nat.card_Icc]
    have : ((k + 1 - 2 : ℕ) : ℝ) ≤ k := Nat.cast_le.2 (by omega)
    linarith
  have b4 : Sizes.seqP d {ω | GgeR4 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k
      (Nn ^ ε) (Φ n)} ≤ ENNReal.ofReal y :=
    (e4 u).trans (ENNReal.ofReal_le_ofReal hxy)
  have bd : Sizes.seqP d {ω | ¬ ∀ j ∈ Finset.Icc 1 (2 * k + 2),
      ∀ v : (Fin j → Bool) × (Fin j → Z2 (d.L n)),
      ¬ GgeRd (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) τ' (D' + ε / c) (Nn ^ ε)
        v.1 v.2} ≤ ENNReal.ofReal y := by
    refine (gge_forall_le (P := Sizes.seqP d) (Finset.Icc 1 (2 * k + 2))
      (fun j ω => ∀ v : (Fin j → Bool) × (Fin j → Z2 (d.L n)),
        ¬ GgeRd (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) τ' (D' + ε / c) (Nn ^ ε)
          v.1 v.2)
      (y := (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) (fun j hj => ?_)).trans
      (ENNReal.ofReal_le_ofReal (hcBx _ ?_))
    · refine (gge_exists_le (P := Sizes.seqP d)
        (fun (v : (Fin j → Bool) × (Fin j → Z2 (d.L n))) ω =>
          GgeRd (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) τ' (D' + ε / c) (Nn ^ ε)
            v.1 v.2) (x := Nn ^ (-D₂)) (fun v => ed j hj (u, v))).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (hcard1 j (Finset.mem_Icc.1 hj).2) hx
    · rw [Nat.card_Icc]
      have : ((2 * k + 2 + 1 - 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by
        rw [show 2 * k + 2 + 1 - 1 = 2 * k + 2 by omega]; push_cast; ring
      rw [this]
  have b5 : Sizes.seqP d {ω | ¬ ∀ l ∈ Finset.Icc 3 k,
      ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
      ¬ GgeR5 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k l (Nn ^ ε) v.1 v.2} ≤
      ENNReal.ofReal y := by
    refine (gge_forall_le (P := Sizes.seqP d) (Finset.Icc 3 k)
      (fun l ω => ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
        ¬ GgeR5 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k l (Nn ^ ε) v.1 v.2)
      (y := (2 * Nn) ^ (2 * k + 2) * Nn ^ (-D₂)) (fun l hl => ?_)).trans
      (ENNReal.ofReal_le_ofReal (hcBx _ ?_))
    · refine (gge_exists_le (P := Sizes.seqP d)
        (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n))) ω =>
          GgeR5 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k l (Nn ^ ε) v.1 v.2)
        (x := Nn ^ (-D₂)) (fun v => e5 l hl (u, v))).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (hcard1 k (by omega)) hx
    · rw [Nat.card_Icc]
      have : ((k + 1 - 3 : ℕ) : ℝ) ≤ k := Nat.cast_le.2 (by omega)
      linarith
  have b6 : Sizes.seqP d {ω | ¬ ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
      ¬ GgeR6 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
        v.1 v.2} ≤ ENNReal.ofReal y :=
    (gge_exists_le (P := Sizes.seqP d)
      (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n))) ω =>
        GgeR6 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
          v.1 v.2) (x := Nn ^ (-D₂)) (fun v => e6 (u, v))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ (hcard1 k (by omega))))
  have b7 : Sizes.seqP d {ω | ¬ ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
      ¬ GgeR7 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
        v.1 v.2} ≤ ENNReal.ofReal y :=
    (gge_exists_le (P := Sizes.seqP d)
      (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n))) ω =>
        GgeR7 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
          v.1 v.2) (x := Nn ^ (-D₂)) (fun v => e7 (u, v))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ (hcard1 k (by omega))))
  have b8 : Sizes.seqP d {ω | ¬ ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n)),
      ¬ GgeR8 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
        v.1 v.2.1 v.2.2} ≤ ENNReal.ofReal y :=
    (gge_exists_le (P := Sizes.seqP d)
      (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n))) ω =>
        GgeR8 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k (D' + ε / c) (Nn ^ ε)
          v.1 v.2.1 v.2.2) (x := Nn ^ (-D₂)) (fun v => e8 (u, v))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ hcard2))
  have b9 : Sizes.seqP d {ω | ¬ ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
      ¬ GgeR9 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k τ' (D' + ε / c) (Nn ^ ε)
        v.1 v.2} ≤ ENNReal.ofReal y :=
    (gge_exists_le (P := Sizes.seqP d)
      (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n))) ω =>
        GgeR9 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k τ' (D' + ε / c) (Nn ^ ε)
          v.1 v.2) (x := Nn ^ (-D₂)) (fun v => e9 (u, v))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ (hcard1 k (by omega))))
  have b10 : Sizes.seqP d {ω | ¬ ∀ v : (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n)),
      ¬ GgeR10 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k τ' (D' + ε / c) (Nn ^ ε)
        v.1 v.2.1 v.2.2} ≤ ENNReal.ofReal y :=
    (gge_exists_le (P := Sizes.seqP d)
      (fun (v : (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n))) ω =>
        GgeR10 (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k τ' (D' + ε / c) (Nn ^ ε)
          v.1 v.2.1 v.2.2) (x := Nn ^ (-D₂)) (fun v => e10 (u, v))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ hcard2))
  refine gge_union11 (P := Sizes.seqP d) b1 b2 b3 b4 bd b5 b6 b7 b8 b9 b10 ?_
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hd⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hcon
  simp only [Set.mem_ofPred_eq] at hω
  exact hω (gge_mem_goodSetN (Sizes.seqHflow_isHermitian d n u ω) hΓ hMpos hηpos hab h1 h2 h3 h4
    (fun j hj σ a => hd j hj (σ, a)) (fun l hl σ a => h5 l hl (σ, a))
    (fun σ a => h6 (σ, a)) (fun σ a => h7 (σ, a)) (fun σ a a' => h8 (σ, a, a'))
    (fun σ a => h9 (σ, a)) (fun σ a a' => h10 (σ, a, a')))

end PerTime

/-! ## 4. The grid union and the endpoint -/

section Grid

variable (d : Sizes)

/-- **The grid union** (part (G) of `goodEvent_grid`, with
`measurableGoodSetN` in place of `measurableGoodSet`): if the flow leaves `GoodSetN` at
every time `u ∈ [s n, t n]` with probability `≤ a`, the grid walk leaves it at some `j ≤ K n`
with probability `≤ (K n + 1) a`, through the transfer law `map_pathH_eq` at the grid times
`u_j ∈ [s n, v n] ⊆ [s n, t n]`. -/
private theorem gge_grid_union {E s v t : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {Γ Λ Φ τ' D' a : ℝ}
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hvt : v n ≤ t n) (hK0 : K n ≠ 0)
    (h : ∀ u : TimeIcc s t n, Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
        GoodSetN (d.L n) (d.W n) (E n) u k Γ Λ Φ τ' D'} ≤ ENNReal.ofReal a) :
    pathP d {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈
        GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k Γ Λ Φ τ' D'}ᶜ ≤
      ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * a) := by
  set G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) := fun j =>
    GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k Γ Λ Φ τ' D' with hGdef
  have hsub : {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ G j}ᶜ ⊆
      ⋃ j ∈ Finset.range (K n + 1), {ω | pathH d s v K n j ω ∉ G j} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨j, hj, hjG⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) hjG
  have hone : ∀ j ∈ Finset.range (K n + 1),
      pathP d {ω | pathH d s v K n j ω ∉ G j} ≤ ENNReal.ofReal a := by
    intro j hj
    have hjK : j ≤ K n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have huj : gridTime s v K n j ≤ t n := (GoodEvent_gridTime_le hsv hjK).trans hvt
    have hsuj : s n ≤ gridTime s v K n j := by
      have h := GoodEvent_gridTime_mono (K := K) hsv (Nat.zero_le j)
      rwa [GoodEvent_gridTime_zero] at h
    have hmeas : MeasurableSet (G j)ᶜ := (measurableGoodSetN _ _ _ _ _ _ _ _ _ _).compl
    have hH : Measurable (pathH d s v K n j) :=
      Measurable.of_eval_matrix _ fun i j' => measurable_pathH d s v K n j i j'
    have hF : Measurable (Sizes.seqHflow d n (gridTime s v K n j)) :=
      Measurable.of_eval_matrix _ fun i j' => Sizes.measurable_seqHflow_entry d n _ i j'
    have h1 : pathP d {ω | pathH d s v K n j ω ∉ G j} =
        Sizes.seqP d {ω | Sizes.seqHflow d n (gridTime s v K n j) ω ∉ G j} := by
      have e1 := Measure.map_apply (μ := pathP d) hH hmeas
      have e2 := Measure.map_apply (μ := Sizes.seqP d) hF hmeas
      rw [map_pathH_eq d s v K n j hs0 hsv hK0] at e1
      exact e1.symm.trans e2
    rw [h1]
    exact h ⟨gridTime s v K n j, hsuj, huj⟩
  calc pathP d {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ G j}ᶜ
      ≤ pathP d (⋃ j ∈ Finset.range (K n + 1), {ω | pathH d s v K n j ω ∉ G j}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (K n + 1), pathP d {ω | pathH d s v K n j ω ∉ G j} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (K n + 1), ENNReal.ofReal a := Finset.sum_le_sum hone
    _ = ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * a) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **The high-probability grid good event** (`d = 2` pattern `goodEvent_grid`): the statement
`GridGoodN`, with no added hypothesis.  With `D₂ = D + max C 0 + (2k+2) + 1` (chosen after `D, C, k`), the
per-time bound of `gge_perTime` at every grid time `u_j ∈ [s n, v n] ⊆ [s n, t n]`, the
factor `K n + 1 ≤ N^C` of `gge_grid_union` and `11 (2k+2) 2^{2k+2} ≤ N` (`SizeTendsto`, a
conjunct of `MainIndHyp`) give the failure probability `≤ N^{-D}`. -/
theorem gridGoodN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : GridGoodN d κ c τ E s v t K := by
  intro hmain hK hKd hV hloc hdec hdl hsv hvt hK0 k hk Λ Φ hΛ0 hΦ0 hΛ1 hPΛ hPΦ1 hPΦ2 hPΦ3 C hC ε
    hε τ' hτ' D' hD' D hD
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  have hD₂ : 0 < D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1 := by
    have h1 := le_max_right C 0
    have h2 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  filter_upwards [gge_perTime d κ c τ E s t hmain hK hKd hV hloc hdec hdl k hk Λ Φ hPΛ hPΦ1 hPΦ2
    hPΦ3 ε hε τ' hτ' D' hD' _ hD₂, hC,
    hsize.eventually_ge_atTop (11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2))] with n hn hCn hNn
  refine (gge_grid_union d (hs0 n) (hsv n) (hvt n) (hK0 n) hn).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact gge_arith (GoodEvent_one_le_size (d := d) n) hCn hNn

end Grid

end RBM.Ind

end

/-! ## 7. Public restatements of the private helpers of Section 1

The `(+,+)` file `RBM2D.Induction.PPGoodEvent` needs the union bounds, the label counts, the
absorption and the final arithmetic of Section 1; they are private above, so they are restated here
as public theorems with the file-stem prefix `GridGoodEvent_` (each is the private helper itself,
applied). -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-- Public form of `gge_exists_le`: the union over a finite family of atomic events. -/
theorem GridGoodEvent_exists_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : Type*}
    [Fintype V] (R : V → Ω → Prop) {x : ℝ}
    (h : ∀ v, P {ω | R v ω} ≤ ENNReal.ofReal x) :
    P {ω | ¬ ∀ v, ¬ R v ω} ≤ ENNReal.ofReal ((Fintype.card V : ℝ) * x) :=
  gge_exists_le R h

/-- Public form of `gge_forall_le`: the union over a finite set of indices. -/
theorem GridGoodEvent_forall_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    (S : Finset ι) (Q : ι → Ω → Prop) {y : ℝ}
    (h : ∀ i ∈ S, P {ω | ¬ Q i ω} ≤ ENNReal.ofReal y) :
    P {ω | ¬ ∀ i ∈ S, Q i ω} ≤ ENNReal.ofReal ((S.card : ℝ) * y) :=
  gge_forall_le S Q h

/-- Public form of `gge_card_Z2`: `#Z2 L = L²`. -/
theorem GridGoodEvent_card_Z2 (L : ℕ) [NeZero L] : Fintype.card (Z2 L) = L ^ 2 :=
  gge_card_Z2 L

/-- Public form of `gge_card_lab`: the labels and signs of a length-`j` loop,
`2^j (L²)^j ≤ (2N)^j` when `L² ≤ N`. -/
theorem GridGoodEvent_card_lab (L : ℕ) [NeZero L] (j : ℕ) {N : ℕ} (hLN : L ^ 2 ≤ N) :
    Fintype.card ((Fin j → Bool) × (Fin j → Z2 L)) ≤ (2 * N) ^ j :=
  gge_card_lab L j hLN

/-- Public form of `gge_absorb`: `N^ε W^{-(D' + ε/c)} ≤ W^{-D'}` from `N^c ≤ W`. -/
theorem GridGoodEvent_absorb {N W c ε D' : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (hε : 0 < ε) (hNW : N ^ c ≤ W) :
    N ^ ε * W ^ (-(D' + ε / c)) ≤ W ^ (-D') :=
  gge_absorb hN hW hc hε hNW

/-- Public form of `gge_arith`: `(K + 1) · 11 (2k+2) (2N)^{2k+2} N^{-D₂} ≤ N^{-D}` for
`D₂ = D + max C 0 + (2k+2) + 1`, once `K + 1 ≤ N^C`, `1 ≤ N` and `11 (2k+2) 2^{2k+2} ≤ N`. -/
theorem GridGoodEvent_arith {N Kp C D : ℝ} {k : ℕ} (hN : 1 ≤ N) (hKp : Kp ≤ N ^ C)
    (hcn : 11 * (2 * (k : ℝ) + 2) * 2 ^ (2 * k + 2) ≤ N) :
    Kp * (11 * ((2 * (k : ℝ) + 2) * (2 * N) ^ (2 * k + 2) *
      N ^ (-(D + max C 0 + ((2 * k + 2 : ℕ) : ℝ) + 1)))) ≤ N ^ (-D) :=
  gge_arith hN hKp hcn

end RBM.Ind

end
