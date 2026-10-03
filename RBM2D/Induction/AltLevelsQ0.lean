/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEnd
import RBM2D.Induction.B45
import RBM2D.Induction.DecayLoop
import RBM2D.Induction.KcalDecay

/-!
# `AltLevelsQ`, part (a): the level of `𝒬_s B_0` at the time `s`

Part (a) of `AltLevelsQ` (`RBM2D.Induction.AltEnd`, the first conjunct of `AltLevelsQConcl`):

`‖𝒬_s B_0‖ = ‖(𝓛-𝒦)_{s,σ} - 𝒫((𝓛-𝒦)_{s,σ})_{a₁} ϑ_{s,a}‖
  ≺ W^{2(k-1)τ'} M_s^{-k} + W^{-D_b}`

at the time `s` only, for every alternating `σ` and label `a`, from `InitLK` (ranks `k` and `k-1`),
`InitDecay` (through `decayLoopAt` at `u = s`, `P ≡ 1`) and `B45_P_vartheta_le`.

* `AltLevelsQ0`: the statement.
* `altLevelsQ0`: the theorem, universally closed.

Proof.  `𝒬_s B_0 = (𝓛-𝒦)_{s,σ,a} - 𝒫((𝓛-𝒦)_{s,σ})_{a₁} ϑ_{s,a}`.  First term: `InitLK` at
rank `k` (`≺ M_s^{-k}`).  Second term: `B45_P_vartheta_le` at `u = s`, `R = ℓ_s W^{τ'}`,
`X = N^{ε} M_s^{-(k-1)}` (`InitLK` at rank `k-1`, union bound over the `≤ N^{2(k-1)}` loops),
`B_f = N W^{-(2k+1)/c}` (`decayLoopAt` at `u = s`, union bound over the far loops of rank `k-1`);
the powers of `ℓ_s` cancel (`2 + 2(k-2) - 2(k-1) = 0`), the near part is
`9^{k-2} C₅^{k-1}(1+log L)^{k-1} W^{2(k-2)τ'} N^ε M_s^{-k}` and the far part
`≤ C₅^{k-1}(1+log L)^{k-1} N^{-1} M_s^{-k}` (`B_f ≤ N^{-(2k)}`, `CondStInd`: `M_s ≥ 1`); so the
sum is `≤ N^{τ₀} W^{2(k-1)τ'} M_s^{-k}` eventually, and `W^{-D_b} ≥ 0` is not needed.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **Part (a) of `AltLevelsQ`** (the first conjunct of `AltLevelsQConcl`, at the time `s`
only; the end time `v` does not enter): under the premises of `AltLevelsQ`,
`‖𝒬_s B_0‖ ≺ altQ0Level`, per time (`PerTimeDomAt`), uniformly in the alternating `σ` and the labels. -/
def AltLevelsQ0 (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) → STOeqLevels d E s t k Λ Φ →
  ∀ τ' Db : ℝ, 0 < τ' → 0 < Db →
  PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1.1 0 p.2.2‖)
      (fun n _ _ => altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db)

/-! ## 1. Elementary helpers (private) -/

section Helpers

/-- The union bound over a finite index set. -/
private theorem AltLevelsQ0_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {I : Type*}
    [Fintype I] (A : I → Set Ω) {ε C : ℝ} (hε : 0 ≤ ε) (hcard : (Fintype.card I : ℝ) ≤ C)
    (hA : ∀ q, P (A q) ≤ ENNReal.ofReal ε) : P (⋃ q, A q) ≤ ENNReal.ofReal (C * ε) := by
  calc P (⋃ q, A q) ≤ ∑ q, P (A q) := measure_iUnion_fintype_le P _
    _ ≤ ∑ _q : I, ENNReal.ofReal ε := Finset.sum_le_sum fun q _ => hA q
    _ = ENNReal.ofReal ((Fintype.card I : ℝ) * ε) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * ε) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hε)

/-- The index set of an `m`-loop has at most `N^{2m}` elements for `N ≥ 2`. -/
private theorem AltLevelsQ0_card_le (n m : ℕ) (hN : 2 ≤ d.size n) :
    (Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (2 * m) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) =
      2 ^ m * (d.L n * d.L n) ^ m := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) ≤ d.size n ^ (2 * m) := by
    rw [hcard]
    calc 2 ^ m * (d.L n * d.L n) ^ m ≤ d.size n ^ m * d.size n ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hN m) (Nat.pow_le_pow_left hLL m)
      _ = d.size n ^ (2 * m) := by ring
  exact_mod_cast hnat

/-- `N^a N^{-(D_p + a + 1)} ≤ N^{-D_p}` for `N ≥ 1`. -/
private theorem AltLevelsQ0_prob_num {N Dp : ℝ} {a : ℕ} (hN1 : 1 ≤ N) :
    N ^ a * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) ≤ N ^ (-Dp) := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_natCast N a]
  have e : N ^ (a : ℝ) * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) = N ^ (-Dp) * N⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1
    push_cast; ring
  rw [e]
  have h1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have h2 : 0 ≤ N ^ (-Dp) := Real.rpow_nonneg hN0.le _
  calc N ^ (-Dp) * N⁻¹ ≤ N ^ (-Dp) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = N ^ (-Dp) := mul_one _

/-- `3 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 3`. -/
private theorem AltLevelsQ0_three_mul_rpow_le {N : ℝ} (D : ℝ) (hN : 3 ≤ N) :
    3 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 3 * (N ^ (-D) * N⁻¹) = N ^ (-D) * (3 / N) := by ring
    _ ≤ N ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN
    _ = _ := mul_one _

/-- `K (1 + log N)^j ≤ N^ε` eventually. -/
private theorem AltLevelsQ0_eventually_log_pow (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ N : ℕ in atTop, K * (1 + Real.log N) ^ j ≤ (N : ℝ) ^ ε := by
  have hε' : 0 < ε / (2 * ((j : ℝ) + 1)) := by positivity
  have h1 := detDom_iff.mp one_add_log_detDom_one (ε / (2 * ((j : ℝ) + 1))) hε'
  have h2 : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN3
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hlog0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  have hb : 1 + Real.log N ≤ (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1))) := by simpa using hN1
  have h3 : (1 + Real.log N) ^ j ≤ (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) := by
    calc (1 + Real.log N) ^ j ≤ ((N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)))) ^ j :=
          pow_le_pow_left₀ hlog0 hb j
      _ = (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have h4 : ε / (2 * ((j : ℝ) + 1)) * j ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [hε]
  calc K * (1 + Real.log N) ^ j ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) :=
        mul_le_mul hN2 h3 (by positivity) (by positivity)
    _ = (N : ℝ) ^ (ε / 2 + ε / (2 * ((j : ℝ) + 1)) * j) := by rw [← Real.rpow_add hN0]
    _ ≤ (N : ℝ) ^ ε := by
        refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
        linarith

/-- `Im m^{(E)} ≤ 1`. -/
private theorem AltLevelsQ0_im_le_one (E : ℝ) : (spectralM E).im ≤ 1 := by
  rw [spectralM_im]
  have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  linarith

end Helpers

/-! ## 2. Loops and the far list -/

section Loops

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem AltLevelsQ0_loopOf_eq (J : LoopIdx (Z2 L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- A uniform bound on `lkGen` of the `m`-loops gives the same bound on `‖(𝓛-𝒦)_J‖` for every
well-formed `J` of length `m`. -/
private theorem AltLevelsQ0_lk_le (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {m : ℕ} {Y : ℝ}
    (h : ∀ (σ' : Fin m → Bool) (a' : Fin m → Z2 L), lkGen L W E u M σ' a' ≤ Y)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m) : ‖LKf L W E u M J‖ ≤ Y := by
  subst hlen
  have hJeq := AltLevelsQ0_loopOf_eq J hJ
  have h1 : ‖LKf L W E u M J‖ = lkGen L W E u M
      (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) := by
    unfold lkGen LKf LLf; rw [hJeq]
  rw [h1]
  exact h _ _

/-- The far bound for well-formed loops given as lists, from the bound for `loopOf`. -/
private theorem AltLevelsQ0_far_list {m : ℕ} {R Bf : ℝ} (F : LoopIdx (Z2 L) → ℂ)
    (h : ∀ (σ' : Fin m → Bool) (a' : Fin m → Z2 L),
      R ≤ (KLoop.maxDist L a' : ℝ) → ‖F (loopOf σ' a')‖ ≤ Bf)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m)
    (hfar : ∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) : ‖F J‖ ≤ Bf := by
  subst hlen
  have hJeq := AltLevelsQ0_loopOf_eq J hJ
  rw [← hJeq]
  refine h _ _ ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := hfar
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  refine le_trans hxy ?_
  exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
    zdist2 L (J.a[q.1.1] - J.a[q.2.1])) (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length)))

end Loops

/-! ## 3. The arithmetic of the two terms -/

section Arith

/-- `W^{-(j/c₀)} ≤ N^{-j}` from `N^{c₀} ≤ W`, `N ≥ 1`. -/
private theorem AltLevelsQ0_rpow_neg_le {Nr Wr c₀ : ℝ} {j : ℕ} (hN1 : 1 ≤ Nr) (hc₀ : 0 < c₀)
    (hNW : Nr ^ c₀ ≤ Wr) : Wr ^ (-((j : ℝ) / c₀)) ≤ (Nr ^ j)⁻¹ := by
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hNW
  have h1 : Nr ^ j ≤ Wr ^ ((j : ℝ) / c₀) := by
    calc Nr ^ j = (Nr ^ c₀) ^ ((j : ℝ) / c₀) := by
          rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hc₀.ne', Real.rpow_natCast]
      _ ≤ Wr ^ ((j : ℝ) / c₀) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNW (by positivity)
  rw [Real.rpow_neg hW0.le]
  exact inv_anti₀ (by positivity) h1

/-- The near part: `(W²η)⁻¹ ((2R+1)²)^m X c^{m+1} ≤ 9^m C^{m+1} (w²)^m Y (M⁻¹)^{m+2}`
for `R = ℓ w`, `X = Y (M⁻¹)^{m+1}`, `c = C ℓ⁻²`, `M = W²ℓ²η` (the exponents of `ℓ` cancel exactly). -/
private theorem AltLevelsQ0_arith_near {m : ℕ} {Wr ℓ η M Y Cc w : ℝ} (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ)
    (hη : 0 < η) (hw : 1 ≤ w) (hY : 0 ≤ Y) (hCc : 0 ≤ Cc) (hM : M = Wr ^ 2 * ℓ ^ 2 * η) :
    (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Y * (M⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2) := by
  have hW0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hR1 : 1 ≤ ℓ * w := by nlinarith
  have h9 : (2 * (ℓ * w) + 1) ^ 2 ≤ 9 * ℓ ^ 2 * w ^ 2 := by nlinarith
  have hpow : ((2 * (ℓ * w) + 1) ^ 2) ^ m ≤ (9 * ℓ ^ 2 * w ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) h9 m
  have hinv : (Wr ^ 2 * η)⁻¹ = ℓ ^ 2 * M⁻¹ := by rw [hM]; field_simp
  have hq : ℓ ^ 2 * (ℓ ^ 2) ^ m * ((ℓ ^ 2)⁻¹) ^ (m + 1) = 1 := by
    rw [← pow_succ', ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  have hnn : 0 ≤ (Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
  calc (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Y * (M⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)
      = ((2 * (ℓ * w) + 1) ^ 2) ^ m *
        ((Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) := by ring
    _ ≤ (9 * ℓ ^ 2 * w ^ 2) ^ m *
        ((Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = (ℓ ^ 2 * (ℓ ^ 2) ^ m * ((ℓ ^ 2)⁻¹) ^ (m + 1)) *
        (9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2)) := by
        rw [hinv]; ring
    _ = 9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2) := by rw [hq, one_mul]

/-- The far part (at `Λ = 1`): `(W²η)⁻¹ (L²)^m B_f c^{m+1} ≤ C^{m+1} N⁻¹ M^{-(m+2)}`
when `B_f ≤ N^{-(2m+4)}`, `M ≤ N`, `η⁻¹ ≤ N`, `L² ≤ N`, `c = C ℓ⁻² ≤ C`. -/
private theorem AltLevelsQ0_arith_far {m : ℕ} {Nr Wr Lr ℓ η M Cc Bf : ℝ} (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ)
    (hη : 0 < η) (hM : M = Wr ^ 2 * ℓ ^ 2 * η) (hMN : M ≤ Nr) (hN1 : 1 ≤ Nr)
    (hL2 : Lr ^ 2 ≤ Nr) (hηN : η⁻¹ ≤ Nr) (hCc : 0 ≤ Cc) (hBf0 : 0 ≤ Bf)
    (hBf : Bf ≤ (Nr ^ (2 * m + 4))⁻¹) :
    (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      Cc ^ (m + 1) * Nr⁻¹ * (M ^ (m + 2))⁻¹ := by
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have h1 : (Wr ^ 2 * η)⁻¹ ≤ Nr := by
    refine le_trans ?_ hηN
    refine inv_anti₀ hη ?_
    have : 1 ≤ Wr ^ 2 := one_le_pow₀ hW
    nlinarith
  have h2 : (Lr ^ 2) ^ m ≤ Nr ^ m := pow_le_pow_left₀ (by positivity) hL2 m
  have h3 : (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤ Cc ^ (m + 1) := by
    have : (ℓ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ)
    have h4 : Cc * (ℓ ^ 2)⁻¹ ≤ Cc := mul_le_of_le_one_right hCc this
    exact pow_le_pow_left₀ (by positivity) h4 _
  have h5 : (Nr ^ (m + 2))⁻¹ ≤ (M ^ (m + 2))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hM0.le hMN _)
  have hc0 : 0 ≤ (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
  calc (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)
      ≤ Nr * (Nr ^ m * (Nr ^ (2 * m + 4))⁻¹) * Cc ^ (m + 1) := by
        gcongr
    _ = Cc ^ (m + 1) * Nr⁻¹ * (Nr ^ (m + 2))⁻¹ := by
        field_simp
        ring
    _ ≤ Cc ^ (m + 1) * Nr⁻¹ * (M ^ (m + 2))⁻¹ := by
        gcongr

/-- **The exponent arithmetic of the two terms** (all quantities real): with `ε ≥ 1`,
`R = ℓ w`, `X = ε (M⁻¹)^{m+1}`, `a₁ ≤ ε (M⁻¹)^{m+2}`, `M = W²ℓ²η`, and
`1 + 2·9^m C^{m+1} ≤ ε`:
`a₁ + (W²η)⁻¹ (((2R+1)²)^m X + (L²)^m B_f) (C ℓ⁻²)^{m+1} ≤ ε² (w²)^{m+1} M^{-(m+2)}`. -/
private theorem AltLevelsQ0_arith_total {m : ℕ} {Nr Wr Lr ℓ η Mm ε Cc w R X Bf a₁ : ℝ}
    (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη : 0 < η) (hMdef : Mm = Wr ^ 2 * ℓ ^ 2 * η)
    (hMN : Mm ≤ Nr) (hN1 : 1 ≤ Nr) (hLN : Lr ^ 2 ≤ Nr) (hηN : η⁻¹ ≤ Nr) (hCc0 : 0 ≤ Cc)
    (hBf0 : 0 ≤ Bf) (hBfle : Bf ≤ (Nr ^ (2 * m + 4))⁻¹) (hw1 : 1 ≤ w)
    (hR : R = ℓ * w) (hX : X = ε * (Mm⁻¹) ^ (m + 1)) (hε1 : 1 ≤ ε)
    (hA : a₁ ≤ ε * (Mm⁻¹) ^ (m + 2)) (hK : 1 + 2 * (9 ^ m * Cc ^ (m + 1)) ≤ ε) :
    a₁ + (Wr ^ 2 * η)⁻¹ * (((2 * R + 1) ^ 2) ^ m * X + (Lr ^ 2) ^ m * Bf) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      ε ^ 2 * ((w ^ 2) ^ (m + 1) * (Mm ^ (m + 2))⁻¹) := by
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hε0 : 0 ≤ ε := by linarith
  have hMm0 : 0 < Mm := by rw [hMdef]; positivity
  have hnear := AltLevelsQ0_arith_near (m := m) (Wr := Wr) (ℓ := ℓ) (η := η) (M := Mm)
    (Y := ε) (Cc := Cc) (w := w) hW hℓ hη hw1 hε0 hCc0 hMdef
  have hfar := AltLevelsQ0_arith_far (m := m) (Nr := Nr) (Wr := Wr) (Lr := Lr) (ℓ := ℓ)
    (η := η) (M := Mm) (Cc := Cc) (Bf := Bf) hW hℓ hη hMdef hMN hN1 hLN hηN hCc0 hBf0 hBfle
  have e : (Wr ^ 2 * η)⁻¹ * (((2 * R + 1) ^ 2) ^ m * X + (Lr ^ 2) ^ m * Bf) *
      (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) =
      (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (ε * (Mm⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) +
      (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by
    rw [hX, hR]; ring
  rw [e]
  -- the abbreviations
  set T : ℝ := (Mm ^ (m + 2))⁻¹ with hT
  have hTe : (Mm⁻¹) ^ (m + 2) = T := by rw [hT, inv_pow]
  have hT0 : 0 ≤ T := by positivity
  rw [hTe] at hnear hA
  set V : ℝ := (w ^ 2) ^ (m + 1) with hV
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw1
  have hV1 : 1 ≤ V := one_le_pow₀ hw2
  have hwm : (w ^ 2) ^ m ≤ V := by
    rw [hV]; exact pow_le_pow_right₀ hw2 (Nat.le_succ m)
  set Q : ℝ := 9 ^ m * Cc ^ (m + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have h9 : (1 : ℝ) ≤ 9 ^ m := one_le_pow₀ (by norm_num)
  have hCQ : Cc ^ (m + 1) ≤ Q := by
    rw [hQ]
    have : 0 ≤ Cc ^ (m + 1) := by positivity
    nlinarith
  have hNinv : Nr⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hP0 : 0 ≤ ε * T * V := by positivity
  -- near ≤ Q V ε T
  have hn : 9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * ε * T ≤ (ε * T * V) * Q := by
    have h1 : Q * (w ^ 2) ^ m * ε * T ≤ Q * V * ε * T := by
      gcongr
    calc 9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * ε * T = Q * (w ^ 2) ^ m * ε * T := by rw [hQ]
      _ ≤ Q * V * ε * T := h1
      _ = (ε * T * V) * Q := by ring
  -- far ≤ Q V ε T
  have hf : Cc ^ (m + 1) * Nr⁻¹ * T ≤ (ε * T * V) * Q := by
    have h1 : Cc ^ (m + 1) * Nr⁻¹ * T ≤ Q * 1 * T := by
      have hc : Cc ^ (m + 1) * Nr⁻¹ ≤ Q * 1 :=
        mul_le_mul hCQ (by simpa using hNinv) (inv_nonneg.2 hN0.le) hQ0
      exact mul_le_mul_of_nonneg_right hc hT0
    have hVε : 1 ≤ V * ε := one_le_mul_of_one_le_of_one_le hV1 hε1
    have h2 : Q * 1 * T ≤ Q * (V * ε) * T := by
      have : Q * 1 ≤ Q * (V * ε) := mul_le_mul_of_nonneg_left hVε hQ0
      exact mul_le_mul_of_nonneg_right this hT0
    calc Cc ^ (m + 1) * Nr⁻¹ * T ≤ Q * 1 * T := h1
      _ ≤ Q * (V * ε) * T := h2
      _ = (ε * T * V) * Q := by ring
  have hA' : a₁ ≤ ε * T * V := by
    refine hA.trans ?_
    have : ε * T * 1 ≤ ε * T * V := mul_le_mul_of_nonneg_left hV1 (by positivity)
    linarith
  calc a₁ + ((Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (ε * (Mm⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) +
      (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1))
      ≤ (ε * T * V) + ((ε * T * V) * Q + (ε * T * V) * Q) := by
        have := add_le_add hnear hfar
        linarith
    _ = (ε * T * V) * (1 + 2 * Q) := by ring
    _ ≤ (ε * T * V) * ε := mul_le_mul_of_nonneg_left hK hP0
    _ = ε ^ 2 * (V * T) := by ring

end Arith

/-! ## 4. The pointwise estimate -/

section Pointwise

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The pointwise estimate**: at one size `n` and the time `u`, on the good event
(`lkGen_{σ,a} ≤ ε M^{-k}`; every rank-`(k-1)` entry is `≤ ε M^{-(k-1)}`; the rank-`(k-1)` entries with
two labels `≥ ℓ_u W^{τ'}` apart are `≤ N W^{-(2k+1)/c₀}`) and the size facts (`N = W²L²`,
`N^{c₀} ≤ W`, `M_u ≥ 1`, `ε ≥ 1`, `1 + 2·9^{k-2}(C₅(1+log L))^{k-1} ≤ ε`), for alternating `σ`:
`‖𝒬_u B_0‖ ≤ ε² W^{2(k-1)τ'} M_u^{-k}`. -/
private theorem AltLevelsQ0_pointwise (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ) (a : Fin k → Z2 L)
    {Nr c₀ τ' ε : ℝ} (hNr : Nr = (W : ℝ) ^ 2 * (L : ℝ) ^ 2) (hN1 : 1 ≤ Nr)
    (hc₀ : 0 < c₀) (hNW : Nr ^ c₀ ≤ W) (hτ' : 0 ≤ τ')
    (hM1 : 1 ≤ scaleM L W E u) (hε1 : 1 ≤ ε)
    (hK : 1 + 2 * (9 ^ (k - 2) * ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (k - 1)) ≤ ε)
    (hA : lkGen L W E u M σ a ≤ ε * (scaleM L W E u)⁻¹ ^ k)
    (hX : ∀ (σ' : Fin (k - 1) → Bool) (a' : Fin (k - 1) → Z2 L),
      lkGen L W E u M σ' a' ≤ ε * (scaleM L W E u)⁻¹ ^ (k - 1))
    (hfarω : ∀ (σ' : Fin (k - 1) → Bool) (a' : Fin (k - 1) → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a' : ℝ) →
      lkGen L W E u M σ' a' ≤ Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀))) :
    ‖altQB L W E u M σ 0 a‖ ≤
      ε ^ 2 * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (scaleM L W E u ^ k)⁻¹) := by
  obtain ⟨m, hkm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hk2 : k - 2 = m := by omega
  have hk1 : k - 1 = m + 1 := by omega
  have hkR : (k : ℝ) = (m : ℝ) + 2 := by rw [hkm]; push_cast; ring
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : 1 ≤ L := by omega
  have hN0 : 0 < Nr := by linarith
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hL1 hu0 hu1
  have hℓL : ellT L u ≤ L := (ellT_pos_le hL1 hu1).2
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hηle : etaT E u ≤ 1 - u := by
    unfold etaT
    have h1 := AltLevelsQ0_im_le_one E
    have h2 : 0 ≤ 1 - u := by linarith
    calc (1 - u) * (spectralM E).im ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = 1 - u := mul_one _
  have hηle1 : etaT E u ≤ 1 := by linarith
  have hMdef : scaleM L W E u = (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u := rfl
  have hMpos : 0 < scaleM L W E u := scaleM_pos hL1 hW hE hu1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLN : (L : ℝ) ^ 2 ≤ Nr := by
    rw [hNr]
    have h1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hW1
    exact le_mul_of_one_le_left (by positivity) h1
  have hMN : scaleM L W E u ≤ Nr := by
    rw [hMdef, hNr]
    have h1 : ellT L u ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hℓL 2
    have h2 : (W : ℝ) ^ 2 * ellT L u ^ 2 ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * 1 :=
          mul_le_mul h2 hηle1 hη.le (by positivity)
      _ = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := mul_one _
  -- `η⁻¹ ≤ N` from `M ≥ 1`
  have hηN : (etaT E u)⁻¹ ≤ Nr := by
    have hWℓ : 0 < (W : ℝ) ^ 2 * ellT L u ^ 2 := by positivity
    have h1 : (etaT E u)⁻¹ = (W : ℝ) ^ 2 * ellT L u ^ 2 * (scaleM L W E u)⁻¹ := by
      rw [hMdef]; field_simp
    have h2 : (scaleM L W E u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM1
    have h3 : (W : ℝ) ^ 2 * ellT L u ^ 2 ≤ Nr := by
      rw [hNr]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hℓL 2) (by positivity)
    calc (etaT E u)⁻¹ = (W : ℝ) ^ 2 * ellT L u ^ 2 * (scaleM L W E u)⁻¹ := h1
      _ ≤ (W : ℝ) ^ 2 * ellT L u ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 hWℓ.le
      _ = (W : ℝ) ^ 2 * ellT L u ^ 2 := mul_one _
      _ ≤ Nr := h3
  -- the parameters
  have hw1 : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hW1 hτ'
  have hR0 : 0 ≤ ellT L u * (W : ℝ) ^ τ' := by positivity
  have hX0 : 0 ≤ ε * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    have : 0 ≤ ε := by linarith
    positivity
  have hBf0 : 0 ≤ Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀)) := by positivity
  -- the two hypotheses of `B45_P_vartheta_le`
  have hXl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      ‖LKf L W E u M J‖ ≤ ε * (scaleM L W E u)⁻¹ ^ (k - 1) := fun J hJ hlen =>
    AltLevelsQ0_lk_le E u M hX J hJ hlen
  have hBl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, ellT L u * (W : ℝ) ^ τ' ≤ (zdist2 L (x - y) : ℝ)) →
      ‖LKf L W E u M J‖ ≤ Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀)) := by
    intro J hJ hlen hfar
    refine AltLevelsQ0_far_list (m := k - 1) (LKf L W E u M) (fun σ' a' hfa => ?_) J hJ hlen hfar
    exact hfarω σ' a' hfa
  have hcore := B45_P_vartheta_le hL hW hE hu0 hu1 hM hk hσ hR0 hX0 hBf0 hXl hBl a
  -- `Bf ≤ N^{-(2m+4)}`
  have hBfle : Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀)) ≤
      (Nr ^ (2 * m + 4))⁻¹ := by
    have h1 := AltLevelsQ0_rpow_neg_le (Nr := Nr) (Wr := (W : ℝ)) (c₀ := c₀) (j := 2 * k + 1)
      hN1 hc₀ hNW
    have h2 : Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀)) ≤
        Nr * (Nr ^ (2 * k + 1))⁻¹ := by
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left h1 hN0.le
    refine h2.trans (le_of_eq ?_)
    have : 2 * k + 1 = (2 * m + 4) + 1 := by omega
    rw [this, pow_succ]
    field_simp
  -- the arithmetic
  have hCc0 : 0 ≤ (180 * 40002 ^ 2) * (1 + Real.log L) := by
    have := Real.log_natCast_nonneg L
    positivity
  have hK' : 1 + 2 * (9 ^ m * ((180 * 40002 ^ 2) * (1 + Real.log L)) ^ (m + 1)) ≤ ε := by
    rw [hk2, hk1] at hK; exact hK
  have hpk : (scaleM L W E u)⁻¹ ^ k = (scaleM L W E u)⁻¹ ^ (m + 2) := by rw [hkm]
  have hA' : lkGen L W E u M σ a ≤ ε * ((scaleM L W E u)⁻¹) ^ (m + 2) := by
    rw [← hpk]; exact hA
  have hΩ := AltLevelsQ0_arith_total (m := m) (Nr := Nr) (Wr := (W : ℝ)) (Lr := (L : ℝ))
    (ℓ := ellT L u) (η := etaT E u) (Mm := scaleM L W E u) (ε := ε)
    (Cc := (180 * 40002 ^ 2) * (1 + Real.log L)) (w := (W : ℝ) ^ τ')
    (R := ellT L u * (W : ℝ) ^ τ')
    (X := ε * (scaleM L W E u)⁻¹ ^ (m + 1))
    (Bf := Nr ^ (1 : ℝ) * (W : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c₀)))
    (a₁ := lkGen L W E u M σ a)
    hW1 hℓ1 hη hMdef hMN hN1 hLN hηN hCc0 hBf0 hBfle hw1 rfl rfl hε1 hA' hK'
  -- `‖𝒬_u B_0‖ ≤ lkGen + ‖𝒫 ϑ‖`
  have hQ : ‖altQB L W E u M σ 0 a‖ ≤ lkGen L W E u M σ a +
      ‖Psum L (lkTensor L W E u M σ) (a 0) * vartheta L u a‖ := by
    have e : altQB L W E u M σ 0 a = lkTensor L W E u M σ a -
        Psum L (lkTensor L W E u M σ) (a 0) * vartheta L u a := rfl
    rw [e]
    refine norm_sub_le _ _ |>.trans ?_
    exact add_le_add_right (le_of_eq rfl) _
  have hexp : (((W : ℝ) ^ τ') ^ 2) ^ (m + 1) = (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') := by
    rw [← Real.rpow_natCast ((W : ℝ) ^ τ') 2, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hW0.le]
    congr 1; rw [hkR]; push_cast; ring
  have hpowk : scaleM L W E u ^ k = scaleM L W E u ^ (m + 2) := by rw [hkm]
  rw [hk2, hk1] at hcore
  rw [hexp] at hΩ
  calc ‖altQB L W E u M σ 0 a‖ ≤ lkGen L W E u M σ a +
        ‖Psum L (lkTensor L W E u M σ) (a 0) * vartheta L u a‖ := hQ
    _ ≤ _ := add_le_add_right hcore _
    _ ≤ _ := hΩ
    _ = _ := by rw [hpowk]

end Pointwise

/-! ## 5. The constant and the monotonicity of the logarithm -/

section Const

/-- `1 + 2·q (c₅ A)^j ≤ (1 + 2 q c₅^j) B^j` for `1 ≤ A ≤ B`. -/
private theorem AltLevelsQ0_K_le {q c5 A B : ℝ} {j : ℕ} (hq : 0 ≤ q) (hc5 : 0 ≤ c5) (hA : 1 ≤ A)
    (hAB : A ≤ B) : 1 + 2 * (q * (c5 * A) ^ j) ≤ (1 + 2 * (q * c5 ^ j)) * B ^ j := by
  have hB1 : 1 ≤ B := hA.trans hAB
  have h1 : 1 ≤ B ^ j := one_le_pow₀ hB1
  have h2 : A ^ j ≤ B ^ j := pow_le_pow_left₀ (by linarith) hAB j
  have h3 : (c5 * A) ^ j ≤ c5 ^ j * B ^ j := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc 1 + 2 * (q * (c5 * A) ^ j) ≤ B ^ j + 2 * (q * (c5 ^ j * B ^ j)) := by
        have : q * (c5 * A) ^ j ≤ q * (c5 ^ j * B ^ j) := mul_le_mul_of_nonneg_left h3 hq
        linarith
    _ = (1 + 2 * (q * c5 ^ j)) * B ^ j := by ring

end Const

/-! ## 6. The theorem -/

section Main

/-- **Part (a) of `AltLevelsQ`** (`AltLevelsQ0`): `‖𝒬_s B_0‖ ≺ W^{2(k-1)τ'} M_s^{-k} + W^{-D_b}`
at the time `s`, per time, uniformly in the alternating `σ` and the labels.  Proof: the bad event is the
union of `{lkGen_{σ,a} > N^{τ₀/2} M_s^{-k}}` (`InitLK`, rank `k`), the rank-`(k-1)` entries
`> N^{τ₀/2} M_s^{-(k-1)}` (`InitLK`, rank `k-1`, union over `≤ N^{2(k-1)}` entries) and the far
rank-`(k-1)` entries `> N W^{-(2k+1)/c}` (`decayLoopAt` at `u = s`, `P ≡ 1`, `InitDecay`); off it the
deterministic `B45_P_vartheta_le` and the exponent arithmetic give `‖𝒬_s B_0‖ ≤ N^{τ₀} W^{2(k-1)τ'} M_s^{-k}`. -/
theorem altLevelsQ0 (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : AltLevelsQ0 d κ c τ C E s t := by
  intro hUp hMain hLoc hDec k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hSTO τ' Db hτ' hDb τ₀ hτ₀ D hD
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hCS, hR, hLK, hDecay, hLoc0⟩ := hMain
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans_lt (ht1 n)
  have hRs : RangeCond d τ s := Green.rangeCond_mono d hR hst
  have hk1 : 1 ≤ k - 1 := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hε : 0 < τ₀ / 2 := half_pos hτ₀
  have hD' : 0 < ((2 * k + 1 : ℕ) : ℝ) / c := by positivity
  set Dfar : ℝ := (D + 1) + (((2 * (k - 1) + 1 : ℕ) : ℝ)) with hDfar
  have hDfar0 : 0 < Dfar := by rw [hDfar]; positivity
  -- the decay input at the time `s` (`InitDecay`, `P ≡ 1`) and the loop decay at `u = s`
  have hdec1 : ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)
      (fun n p _ => (fun _ : ℕ => (1 : ℝ)) n * (scaleM (d.L n) (d.W n) (E n) (s n) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (s n))) +
        (d.W n : ℝ) ^ (-D)) := fun D hD => by
    simpa only [one_mul] using hDecay D hD
  have hdl := decayLoopAt d κ c τ 0 E s (fun _ => 1) hκ hE hc hτ le_rfl hs0 hs1 hN hB hRs
    (kcalDecay κ) hUp.2.1 (fun _ => le_rfl) (Filter.Eventually.of_forall fun n => by simp) hLoc0 hdec1
  -- the three probability inputs
  have eA := hLK k (by omega) (τ₀ / 2) hε (D + 1) (by linarith)
  have eX := hLK (k - 1) hk1 (τ₀ / 2) hε Dfar hDfar0
  have eF := hdl (k - 1) hk1 τ' hτ' (((2 * k + 1 : ℕ) : ℝ) / c) hD' 1 one_pos Dfar hDfar0
  -- the eventual size facts
  have hK0 : 0 ≤ 1 + 2 * (9 ^ (k - 2) * (180 * 40002 ^ 2 : ℝ) ^ (k - 1)) := by positivity
  have eLog := hsize.eventually (AltLevelsQ0_eventually_log_pow _ (τ₀ / 2) hK0 hε (k - 1))
  have e3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hN.eventually_ge_atTop 3
  filter_upwards [eA, eX, eF, eLog, e3, hB, hCS] with n hA hX hF hlog hN3 hbw hcs
  rintro ⟨⟨⟩, ⟨σ, hσ⟩, a⟩
  have hN2nat : 2 ≤ d.size n := by
    have h : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  -- abbreviations
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 3 ≤ d.L n := d.three_le_L n
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hu0 : 0 ≤ s n := hs0 n
  have hE2 : |E n| < 2 := by linarith [hE n]
  have hNr : N = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [hNdef, Sizes.size_eq]; push_cast; ring
  have hL1r : (1 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast (by omega : 1 ≤ d.L n)
  have hLN : (d.L n : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW1)
    calc (d.L n : ℝ) ≤ (d.L n : ℝ) ^ 2 := by nlinarith
      _ ≤ N := by rw [hNr]; exact le_mul_of_one_le_left (by positivity) h1
  -- `M_s ≥ 1`
  have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) (s n) :=
    scaleM_pos (by omega) hW1 hE2 (hs1 n)
  have hM1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) (s n) := by
    have h1 : ((1 - t n) / (1 - s n)) ^ 30 ≤ 1 := by
      refine pow_le_one₀ (div_nonneg (by linarith [ht1 n]) (by linarith [hs1 n])) ?_
      rw [div_le_one (by linarith [hs1 n])]
      linarith [hst n]
    have h2 : (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ 1 := hcs.trans h1
    exact (inv_le_one_iff₀.mp h2).resolve_left (not_le.mpr hMpos)
  -- the constant
  have hK : 1 + 2 * (9 ^ (k - 2) * ((180 * 40002 ^ 2) * (1 + Real.log (d.L n))) ^ (k - 1)) ≤
      N ^ (τ₀ / 2) := by
    refine le_trans ?_ hlog
    have hlogle : Real.log (d.L n : ℝ) ≤ Real.log N := Real.log_le_log (by linarith) hLN
    have hq : (0 : ℝ) ≤ 9 ^ (k - 2) := by positivity
    exact AltLevelsQ0_K_le (q := 9 ^ (k - 2)) (c5 := 180 * 40002 ^ 2) (A := 1 + Real.log (d.L n))
      (B := 1 + Real.log N) (j := k - 1) hq (by norm_num)
      (by have := Real.log_natCast_nonneg (d.L n); linarith) (by linarith)
  have hε1 : (1 : ℝ) ≤ N ^ (τ₀ / 2) := Real.one_le_rpow hN1 hε.le
  have hεsq : (N ^ (τ₀ / 2)) ^ 2 = N ^ τ₀ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  -- the three bad events
  set S₁ : Set (Sizes.SeqΩ d) :=
    {ω | N ^ (τ₀ / 2) * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k <
      lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ a} with hS₁
  set S₂ : Set (Sizes.SeqΩ d) :=
    ⋃ q : (Fin (k - 1) → Bool) × (Fin (k - 1) → Z2 (d.L n)),
      {ω | N ^ (τ₀ / 2) * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ (k - 1) <
        lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2} with hS₂
  set S₃ : Set (Sizes.SeqΩ d) :=
    ⋃ q : (Fin (k - 1) → Bool) × (Fin (k - 1) → Z2 (d.L n)),
      {ω | N ^ (1 : ℝ) * (d.W n : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c)) <
        (loopAbs (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2 +
          lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2) *
        (if ellT (d.L n) (s n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) q.2 : ℝ)
          then 1 else 0)} with hS₃
  -- the probability
  have hP1 : Sizes.seqP d S₁ ≤ ENNReal.ofReal (N ^ (-(D + 1))) := hA ((), σ, a)
  have hP2 : Sizes.seqP d S₂ ≤ ENNReal.ofReal (N ^ (-(D + 1))) := by
    have hU := AltLevelsQ0_union (Sizes.seqP d)
      (I := (Fin (k - 1) → Bool) × (Fin (k - 1) → Z2 (d.L n)))
      (fun q => {ω | N ^ (τ₀ / 2) * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ (k - 1) <
        lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2})
      (ε := N ^ (-Dfar)) (C := N ^ (2 * (k - 1))) (Real.rpow_nonneg hN0.le _)
      (AltLevelsQ0_card_le d n (k - 1) hN2nat)
      (fun q => hX ((), q.1, q.2))
    refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
    have := AltLevelsQ0_prob_num (N := N) (Dp := D + 1) (a := 2 * (k - 1)) hN1
    rw [hDfar]
    exact this
  have hP3 : Sizes.seqP d S₃ ≤ ENNReal.ofReal (N ^ (-(D + 1))) := by
    have hU := AltLevelsQ0_union (Sizes.seqP d)
      (I := (Fin (k - 1) → Bool) × (Fin (k - 1) → Z2 (d.L n)))
      (fun q => {ω | N ^ (1 : ℝ) * (d.W n : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c)) <
        (loopAbs (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2 +
          lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) q.1 q.2) *
        (if ellT (d.L n) (s n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) q.2 : ℝ)
          then 1 else 0)})
      (ε := N ^ (-Dfar)) (C := N ^ (2 * (k - 1))) (Real.rpow_nonneg hN0.le _)
      (AltLevelsQ0_card_le d n (k - 1) hN2nat)
      (fun q => hF ((), q.1, q.2))
    refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
    have := AltLevelsQ0_prob_num (N := N) (Dp := D + 1) (a := 2 * (k - 1)) hN1
    rw [hDfar]
    exact this
  have hPS : Sizes.seqP d (S₁ ∪ S₂ ∪ S₃) ≤ ENNReal.ofReal (N ^ (-D)) := by
    calc Sizes.seqP d (S₁ ∪ S₂ ∪ S₃) ≤ Sizes.seqP d (S₁ ∪ S₂) + Sizes.seqP d S₃ :=
          measure_union_le _ _
      _ ≤ (Sizes.seqP d S₁ + Sizes.seqP d S₂) + Sizes.seqP d S₃ :=
          add_le_add (measure_union_le _ _) le_rfl
      _ ≤ (ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1)))) +
            ENNReal.ofReal (N ^ (-(D + 1))) :=
          add_le_add (add_le_add hP1 hP2) hP3
      _ = ENNReal.ofReal (3 * N ^ (-(D + 1))) := by
          have h0 : 0 ≤ N ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
          rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0]
          ring_nf
      _ ≤ ENNReal.ofReal (N ^ (-D)) :=
          ENNReal.ofReal_le_ofReal (AltLevelsQ0_three_mul_rpow_le D hN3)
  -- off the bad events
  refine le_trans (measure_mono ?_) hPS
  intro ω hω
  by_contra hωS
  have hω1 : ω ∉ S₁ := fun h => hωS (Or.inl (Or.inl h))
  have hω2 : ω ∉ S₂ := fun h => hωS (Or.inl (Or.inr h))
  have hω3 : ω ∉ S₃ := fun h => hωS (Or.inr h)
  have hA' : lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ a ≤
      N ^ (τ₀ / 2) * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k := not_lt.1 hω1
  have hX' : ∀ (σ' : Fin (k - 1) → Bool) (a' : Fin (k - 1) → Z2 (d.L n)),
      lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ' a' ≤
        N ^ (τ₀ / 2) * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ (k - 1) := fun σ' a' =>
    not_lt.1 fun h => hω2 (Set.mem_iUnion.2 ⟨(σ', a'), h⟩)
  have hfarω : ∀ (σ' : Fin (k - 1) → Bool) (a' : Fin (k - 1) → Z2 (d.L n)),
      ellT (d.L n) (s n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a' : ℝ) →
      lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ' a' ≤
        N ^ (1 : ℝ) * (d.W n : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c)) := by
    intro σ' a' hfa
    have h : (loopAbs (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ' a' +
        lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ' a') *
        (if ellT (d.L n) (s n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a' : ℝ)
          then 1 else 0) ≤
        N ^ (1 : ℝ) * (d.W n : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℝ) / c)) :=
      not_lt.1 fun h => hω3 (Set.mem_iUnion.2 ⟨(σ', a'), h⟩)
    simp only [hfa, ↓reduceIte, mul_one] at h
    have := loopAbs_nonneg (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) σ' a'
    linarith
  have hpt := AltLevelsQ0_pointwise (hL := hL1) (hW := hW1) hE2 hu0 (hs1 n)
    (Sizes.seqHflow_isHermitian d n (s n) ω) hk hσ a hNr hN1 hc hbw hτ'.le hM1 hε1 hK hA' hX' hfarω
  rw [hεsq] at hpt
  have hlev : N ^ τ₀ * ((d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') *
      (scaleM (d.L n) (d.W n) (E n) (s n) ^ k)⁻¹) ≤
      N ^ τ₀ * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db := by
    unfold altQ0Level
    have h0 : 0 ≤ N ^ τ₀ := Real.rpow_nonneg hN0.le _
    have h1 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_left (by linarith) h0
  exact absurd (hpt.trans hlev) (not_le.2 (by simpa using hω))

end Main

end RBM.Ind

end
