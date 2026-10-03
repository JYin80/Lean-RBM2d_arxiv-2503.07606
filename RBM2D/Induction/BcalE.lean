/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Induction.BcalEDecay
import RBM2D.Induction.Chain

/-!
# `lem_BcalE` per time over `[s,t]`, random controls: `bcalEPT'`

Paper: arXiv:2503.07606, Section 5: `lem_BcalE`, `CalEbwXi`, `def_ELKLK`, `DefKsimLK`, `def:CALE`;
Section 1: `def_EwtG`.  Namespace `RBM.Ind`.

## Contents

* `BcalEPT'`: `BcalEPT` with an additive `W^{-D}` in (ii), (iii), (iv).
* `bcalEPT' d κ c τ E s t : BcalEPT' d κ c τ E s t`, the only other public declaration; conjunct (v)
  is `bcalE_labelDecay`.

Every other declaration is `private` with the prefix `bcalE_`.

## Proof

Fix `k ≥ 2`, `M = M_u`, `η = η_u`, `ℓ = ℓ_u`, `N = W²L²`, `R = ℓ W^{τ₁}`.  The sums of the four
terms are sums over cuts `(k', l')` (or over `k'`) of `Σ_{a,b} S^{(B)}_{ab} F(a) G(b)` with a window
`|b - c| < R` (`c` a label of the loop) and a tail: `norm_sum_SB_le_left/right` give
`(2R+1)² max|F G| + L² max_{far}|F G|`.  `W² (2R+1)² M^{-1} ≤ 9 N^{τ₁} η^{-1}` (`bcalE_near_factor`,
from `M = W²ℓ²η`, `ℓ ≥ 1`) turns the window part into the right sides of `BcalEPT'`.

* (i) is deterministic: the `𝒦` piece (length `l ≥ 3`) has `|𝒦_J| ≤ N^{τ₁} M^{-(|J|-1)}`
  (`KboundConcl`) and `≤ W^{-D'}` if two labels are `≥ R` apart (`KcalDecay`, `D' = (k+2)/c`); the
  `𝓛-𝒦` piece (length `p = k+2-l`) is `≤ Ξ^{(𝓛-𝒦)}_p M^{-p}` by the definition of `xiLK`, and the
  far part is proportional to it (`bcalE_det_i`, `bcalE_i_arith`).
* (ii)–(iv) on the good event `bcalE_core` (an extension of `bcalEDecay_core`): off an event of probability `≤ N^{-D_p}`, `𝓛` and `𝓛-𝒦` have `(R, N W^{-D''})` decay on
  loops of length `≤ K = 2k+2` (`DecayLoopPT`, union bound), `|𝓛_J|, |𝒦_J| ≤ N^K`, and
  `|⟨(G-m)E_a⟩| ≤ N^{τ₂} M^{-1}` for both signs and all `a` (`bcalE_one_loop`, union bound over the
  `L² ≤ N` labels).  With `D'' = D + (K+3)/c` the far parts are `≤ W^{-D}` (`bcalE_WD`), the window
  parts are `≤ 9 k² N^{τ₁ + τ₂} · (control)` (`bcalE_ii_arith`, `bcalE_iii_arith`,
  `bcalE_iv_arith`), and `N^{τ}` absorbs `9k²N^{τ₁+τ₂}` (`bcalE_absorb`).
* The one-loop control (`bcalE_one_loop`, the proof of `s45_one_loop` with `Step3PT` at `k = 2`
  replaced by `bcalE_loopDet`): `‖⟨(G_u - m)E_a⟩‖ ≺ M_u^{-1}` from the (`GavLGEX`) clause of
  `GbEXPHypV3 d (κ/2) c τ` at every time sequence in `[s,t]` with `Ψ² = M_u^{-1}`, (`asGMc`) from
  `Step2LocalPT`, and `LoopDetSeq` from `KboundConcl` (`n = 2`) and `Step2DecayPT` at `D = 2`, using
  `(η_s/η_u)^4 ≤ M_u` (`scaleM_ge_pow29`, `CondStInd`) and `M_u ≤ W²`.

Several elementary helpers (union bound, cardinality of loop indices, `Im m` bounds, loop
decomposition lemmas) repeat the private helpers of `RBM2D.Induction.BcalEDecay` and
`RBM2D.Induction.Step45` under the prefix `bcalE_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Elementary helpers -/

section Helpers

/-- The union bound over a finite family of finite index sets. -/
private theorem bcalE_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Finset ℕ)
    {I : ℕ → Type*} [∀ m, Fintype (I m)] (A : ∀ m, I m → Set Ω) {ε C : ℝ} (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hcard : ∀ m ∈ T, (Fintype.card (I m) : ℝ) ≤ C)
    (hA : ∀ m ∈ T, ∀ q, P (A m q) ≤ ENNReal.ofReal ε) :
    P (⋃ m ∈ T, ⋃ q, A m q) ≤ ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
  calc P (⋃ m ∈ T, ⋃ q, A m q) ≤ ∑ m ∈ T, P (⋃ q, A m q) := measure_biUnion_finset_le T _
    _ ≤ ∑ m ∈ T, ∑ q, P (A m q) := Finset.sum_le_sum fun m _ => measure_iUnion_fintype_le P _
    _ ≤ ∑ m ∈ T, ∑ _q : I m, ENNReal.ofReal ε :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun q _ => hA m hm q
    _ = ∑ m ∈ T, ENNReal.ofReal ((Fintype.card (I m) : ℝ) * ε) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ m ∈ T, ENNReal.ofReal (C * ε) := Finset.sum_le_sum fun m hm =>
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcard m hm) hε)
    _ = ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc,
          ENNReal.ofReal_mul (p := (T.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The index set of an `m`-loop has at most `N^{2K}` elements for `m ≤ K`, `N ≥ 2`. -/
private theorem bcalE_card_le (d : Sizes) (n m K : ℕ) (hm : m ≤ K) (hN : 2 ≤ d.size n) :
    (Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (2 * K) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) =
      2 ^ m * (d.L n * d.L n) ^ m := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) ≤ d.size n ^ (2 * K) := by
    rw [hcard]
    calc 2 ^ m * (d.L n * d.L n) ^ m ≤ d.size n ^ m * d.size n ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hN m) (Nat.pow_le_pow_left hLL m)
      _ = d.size n ^ (2 * m) := by ring
      _ ≤ d.size n ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  exact_mod_cast hnat

/-- `K N^{a} N^{-(D_p + a + 1)} ≤ N^{-D_p}` for `N ≥ K`, `N ≥ 1`. -/
private theorem bcalE_prob_num {N Dp : ℝ} {K a : ℕ} (hN1 : 1 ≤ N) (hN : (K : ℝ) ≤ N) :
    (K : ℝ) * N ^ a * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) ≤ N ^ (-Dp) := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_natCast N a]
  have e : N ^ (a : ℝ) * N ^ (-(Dp + ((a + 1 : ℕ) : ℝ))) = N ^ (-Dp) * N⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1
    push_cast; ring
  rw [mul_assoc, e]
  have h1 : (K : ℝ) * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have h2 : 0 ≤ N ^ (-Dp) := Real.rpow_nonneg hN0.le _
  calc (K : ℝ) * (N ^ (-Dp) * N⁻¹) = N ^ (-Dp) * ((K : ℝ) * N⁻¹) := by
        ring
    _ ≤ N ^ (-Dp) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = N ^ (-Dp) := mul_one _

/-- `W^{-(D' + e/c)} N^e ≤ W^{-D'}` from `N^c ≤ W`. -/
private theorem bcalE_WD {N W c D' e : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (he : 0 ≤ e) (hNW : N ^ c ≤ W) : W ^ (-(D' + e / c)) * N ^ e ≤ W ^ (-D') := by
  have h1 : N ^ e ≤ W ^ (e / c) := by
    calc N ^ e = (N ^ c) ^ (e / c) := by
          rw [← Real.rpow_mul hN]; congr 1; field_simp
      _ ≤ W ^ (e / c) := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hNW (div_nonneg he hc.le)
  have h2 : W ^ (-(D' + e / c)) = W ^ (-D') * (W ^ (e / c))⁻¹ := by
    rw [show -(D' + e / c) = -D' + -(e / c) by ring, Real.rpow_add hW, Real.rpow_neg hW.le (e / c)]
  rw [h2]
  have h3 : 0 < W ^ (e / c) := Real.rpow_pos_of_pos hW _
  have h4 : 0 ≤ W ^ (-D') * (W ^ (e / c))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hW.le _) (inv_nonneg.2 h3.le)
  calc W ^ (-D') * (W ^ (e / c))⁻¹ * N ^ e ≤ W ^ (-D') * (W ^ (e / c))⁻¹ * W ^ (e / c) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = W ^ (-D') := by field_simp

/-- `((1-u) Im m)^{-1} ≤ N` from `N^{-1+τ} ≤ 1-u`, `μ ≤ Im m`, `1 ≤ μ N^τ`. -/
private theorem bcalE_eta_inv {N x μ m τ : ℝ} (hN : 0 < N) (hx : N ^ (-1 + τ) ≤ x)
    (hμ : 0 < μ) (hm : μ ≤ m) (hμN : 1 ≤ μ * N ^ τ) : (x * m)⁻¹ ≤ N := by
  have e : N * N ^ (-1 + τ) = N ^ τ := by
    rw [Real.rpow_add hN, Real.rpow_neg_one]; field_simp
  have hp : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN _
  have hx0 : 0 < x := lt_of_lt_of_le hp hx
  have hxm : 0 < x * m := mul_pos hx0 (lt_of_lt_of_le hμ hm)
  have key : 1 ≤ N * (x * m) := by
    rw [← e] at hμN
    have : μ * (N * N ^ (-1 + τ)) ≤ m * (N * x) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left hx hN.le) (by positivity) (by linarith)
    nlinarith
  calc (x * m)⁻¹ = (x * m)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (x * m)⁻¹ * (N * (x * m)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hxm.le)
    _ = N := by rw [mul_comm N, ← mul_assoc, inv_mul_cancel₀ hxm.ne', one_mul]

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ`. -/
private theorem bcalE_im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hκ : 0 < κ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ (spectralM (E n)).im ∧ (spectralM (E n)).im ≤ 1 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun n => ⟨?_, ?_⟩⟩
  · have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  · rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith
  · rw [spectralM_im]
    have : Real.sqrt (4 - E n ^ 2) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [sq_nonneg (E n)]⟩
    linarith

/-- `Σ_{1 ≤ k < l ≤ n} f(k, l) ≤ n² T`. -/
private theorem bcalE_sum_pairs (n : ℕ) (f : ℕ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ k ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Ioc k n, f k l ≤ T) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l ≤ (n : ℝ) ^ 2 * T := by
  calc ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l
      ≤ ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, T :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hf k hk l hl
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (n : ℝ) * T := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le n k
    _ = (n : ℝ) ^ 2 * T := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

end Helpers

/-! ## 2. Loops and the controls `Ξ` -/

section Loops

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem bcalE_loopOf_eq (J : LoopIdx (Z2 L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` to `LoopDecay`. -/
private theorem bcalE_loopDecay_of (F : LoopIdx (Z2 L) → ℂ) {K : ℕ} {R δ : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L),
      R ≤ (KLoop.maxDist L a : ℝ) → ‖F (loopOf σ a)‖ ≤ δ) :
    LoopDecay L K R δ F := by
  intro J hJ hJK x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at hJK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1]) (by
      refine le_trans hxy ?_
      exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
        zdist2 L (J.a[q.1.1] - J.a[q.2.1]))
        (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length))))
  rwa [bcalE_loopOf_eq J hJ] at this

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` to all well-formed loops. -/
private theorem bcalE_bound_of (F : LoopIdx (Z2 L) → ℂ) {K : ℕ} {B : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L), ‖F (loopOf σ a)‖ ≤ B)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hK : J.length ≤ K) : ‖F J‖ ≤ B := by
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at h1 hK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1])
  rwa [bcalE_loopOf_eq J hJ] at this

/-- As `bcalE_bound_of`, with a bound `B m` depending on the length. -/
private theorem bcalE_bound_of' (F : LoopIdx (Z2 L) → ℂ) {K : ℕ} {B : ℕ → ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L), ‖F (loopOf σ a)‖ ≤ B m)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hK : J.length ≤ K) :
    ‖F J‖ ≤ B J.length := by
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at h1 hK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1])
  rwa [bcalE_loopOf_eq J hJ] at this

private theorem bcalE_length_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).length = n := by
  simp [loopOf, LoopIdx.length]

private theorem bcalE_WF_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem bcalE_mem_loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) (i : Fin n) :
    a i ∈ (loopOf σ a).a := by
  simp only [loopOf]
  exact List.mem_ofFn.2 ⟨i, rfl⟩

private theorem bcalE_xiLK_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) (m : ℕ) : 0 ≤ xiLK L W E u M m := by
  unfold xiLK
  refine mul_nonneg ?_ (pow_nonneg hpos.le _)
  exact Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Z2 L))))
    (norm_nonneg _)

private theorem bcalE_xiL_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) (m : ℕ) : 0 ≤ xiL L W E u M m := by
  unfold xiL
  refine mul_nonneg ?_ (pow_nonneg hpos.le _)
  exact Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Z2 L))))
    (loopAbs_nonneg L W E u M _ _)

/-- `|𝓛_J| ≤ Ξ^{(𝓛)}_m M^{-(m-1)}` for a well-formed loop of length `m`. -/
private theorem bcalE_ll_le_xiL (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {m : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m) :
    ‖LLf L W E u M J‖ ≤ xiL L W E u M m * (scaleM L W E u)⁻¹ ^ (m - 1) := by
  subst hlen
  have hJeq := bcalE_loopOf_eq J hJ
  have h1 : ‖LLf L W E u M J‖ = loopAbs L W E u M
      (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) := by
    unfold loopAbs LLf; rw [hJeq]
  have h2 := Finset.le_sup'
    (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) => loopAbs L W E u M p.1 p.2)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))
  have hM : scaleM L W E u ^ (J.a.length - 1) * (scaleM L W E u)⁻¹ ^ (J.a.length - 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow]
  calc ‖LLf L W E u M J‖ = _ := h1
    _ ≤ _ := h2
    _ = Finset.univ.sup' Finset.univ_nonempty
          (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) =>
            loopAbs L W E u M p.1 p.2) *
        (scaleM L W E u ^ (J.a.length - 1) * (scaleM L W E u)⁻¹ ^ (J.a.length - 1)) := by
          rw [hM, mul_one]
    _ = xiL L W E u M J.a.length * (scaleM L W E u)⁻¹ ^ (J.a.length - 1) := by
          unfold xiL; ring

/-- `|(𝓛-𝒦)_J| ≤ Ξ^{(𝓛-𝒦)}_m M^{-m}` for a well-formed loop of length `m`. -/
private theorem bcalE_lk_le_xiLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {m : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m) :
    ‖LKf L W E u M J‖ ≤ xiLK L W E u M m * (scaleM L W E u)⁻¹ ^ m := by
  subst hlen
  have hJeq := bcalE_loopOf_eq J hJ
  have h1 : ‖LKf L W E u M J‖ = lkGen L W E u M
      (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) := by
    unfold lkGen LKf LLf; rw [hJeq]
  have h2 := Finset.le_sup'
    (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) => lkGen L W E u M p.1 p.2)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))
  have hM : scaleM L W E u ^ J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow]
  calc ‖LKf L W E u M J‖ = _ := h1
    _ ≤ _ := h2
    _ = Finset.univ.sup' Finset.univ_nonempty
          (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) =>
            lkGen L W E u M p.1 p.2) *
        (scaleM L W E u ^ J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length) := by
          rw [hM, mul_one]
    _ = xiLK L W E u M J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length := by
          unfold xiLK; ring

end Loops

/-! ## 3. The window factor -/

/-- `W² (2R+1)² M^{-1} ≤ 9 N^{τ₁} η^{-1}` for `R = ℓ W^{τ₁}`, `M = W² ℓ² η`, `W² ≤ N`. -/
private theorem bcalE_near_factor {Wr Nr ℓ η τ1 : ℝ} (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη : 0 < η)
    (hWN : Wr ^ 2 ≤ Nr) (hτ1 : 0 ≤ τ1) :
    Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Wr ^ 2 * ℓ ^ 2 * η)⁻¹ ≤ 9 * Nr ^ τ1 * η⁻¹ := by
  have hW0 : 0 < Wr := by linarith
  have hx1 : 1 ≤ Wr ^ τ1 := Real.one_le_rpow hW hτ1
  have hx2 : (Wr ^ τ1) ^ 2 ≤ Nr ^ τ1 := by
    have h := Real.rpow_le_rpow (by positivity) hWN hτ1
    rwa [← Real.rpow_natCast Wr 2, ← Real.rpow_mul hW0.le, mul_comm, Real.rpow_mul hW0.le,
      Real.rpow_natCast] at h
  have hR1 : 1 ≤ ℓ * Wr ^ τ1 := by nlinarith
  have h9 : (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 ≤ 9 * ℓ ^ 2 * Nr ^ τ1 := by
    calc (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 ≤ (3 * (ℓ * Wr ^ τ1)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity); linarith
      _ = 9 * ℓ ^ 2 * (Wr ^ τ1) ^ 2 := by ring
      _ ≤ 9 * ℓ ^ 2 * Nr ^ τ1 := by gcongr
  have hℓ0 : 0 < ℓ := by linarith
  calc Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Wr ^ 2 * ℓ ^ 2 * η)⁻¹
      = (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (ℓ ^ 2 * η)⁻¹ := by field_simp
    _ ≤ (9 * ℓ ^ 2 * Nr ^ τ1) * (ℓ ^ 2 * η)⁻¹ := by gcongr
    _ = 9 * Nr ^ τ1 * η⁻¹ := by field_simp

/-! ## 4. One cut, decay of one factor -/

section Cuts

variable {L : ℕ} [NeZero L]

/-- One cut `(k, l)`: window in `b` from the decay of the right piece `G`; the left factor is
bounded by `BF` (relative) and by `Bc` (crude, used on the far part). -/
private theorem bcalE_cutR (hL : 3 ≤ L) {F G : LoopIdx (Z2 L) → ℂ} {I : LoopIdx (Z2 L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R BF Bc BG δG : ℝ}
    (hR : 0 ≤ R) (hBc : 0 ≤ Bc) (hδG : 0 ≤ δG)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ BF) (hFc : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ Bc)
    (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ BG) (hGd : LoopDecay L I.length R δG G) :
    ‖∑ a : Z2 L, ∑ b : Z2 L, F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ ≤
      (2 * R + 1) ^ 2 * (BF * BG) + (L : ℝ) ^ 2 * (Bc * δG) := by
  obtain ⟨c, hc⟩ := exists_anchor_cutGlueR I hk hkl hl
  have hBF : 0 ≤ BF := (norm_nonneg _).trans (hF 0)
  have e : ∑ a : Z2 L, ∑ b : Z2 L, F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) =
      ∑ a : Z2 L, ∑ b : Z2 L, SB L a b * (F (I.cutGlueL k l a) * G (I.cutGlueR k l b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  refine norm_sum_SB_le_right L hL hR (mul_nonneg hBc hδG) c
    (fun a b => F (I.cutGlueL k l a) * G (I.cutGlueR k l b)) (fun a b => ?_) (fun a b hab => ?_)
  · show ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ BF * BG
    rw [norm_mul]; exact mul_le_mul (hF a) (hG b) (norm_nonneg _) hBF
  · change ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ Bc * δG
    rw [norm_mul]
    have := hGd _ (hI.cutGlueR b hk hkl hl) (BcalEDecay_length_cutGlueR_le I b hk hkl hl) b
      (mem_cutGlueR I b k l) c (hc b) hab
    exact mul_le_mul (hFc a) this (norm_nonneg _) hBc

/-- One cut `(k, l)`: window in `a` from the decay of the left piece `F`. -/
private theorem bcalE_cutL (hL : 3 ≤ L) {F G : LoopIdx (Z2 L) → ℂ} {I : LoopIdx (Z2 L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R BF BG Bc δF : ℝ}
    (hR : 0 ≤ R) (hBc : 0 ≤ Bc) (hδF : 0 ≤ δF)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ BF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ BG)
    (hGc : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ Bc) (hFd : LoopDecay L I.length R δF F) :
    ‖∑ a : Z2 L, ∑ b : Z2 L, F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ ≤
      (2 * R + 1) ^ 2 * (BF * BG) + (L : ℝ) ^ 2 * (δF * Bc) := by
  obtain ⟨c, hc⟩ := exists_anchor_cutGlueL I (k := k) (by omega : 1 ≤ l) hl
  have hBG : 0 ≤ BG := (norm_nonneg _).trans (hG 0)
  have e : ∑ a : Z2 L, ∑ b : Z2 L, F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) =
      ∑ a : Z2 L, ∑ b : Z2 L, SB L a b * (F (I.cutGlueL k l a) * G (I.cutGlueR k l b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  refine norm_sum_SB_le_left L hL hR (mul_nonneg hδF hBc) c
    (fun a b => F (I.cutGlueL k l a) * G (I.cutGlueR k l b)) (fun a b => ?_) (fun a b hab => ?_)
  · show ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ BF * BG
    rw [norm_mul]; exact mul_le_mul (hF a) (hG b) (norm_nonneg _) ((norm_nonneg _).trans (hF a))
  · change ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ δF * Bc
    rw [norm_mul]
    have := hFd _ (hI.cutGlueL a hk hkl hl) (BcalEDecay_length_cutGlueL_le I a hk hkl hl) a
      (mem_cutGlueL I a k l) c (hc a) hab
    exact mul_le_mul this (hGc b) (norm_nonneg _) hδF

end Cuts

/-! ## 5. Deterministic bounds on the four terms -/

section Det

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem bcalE_norm_sum_add {ι κ : Type*} [Fintype ι] [Fintype κ] (f g : ι → κ → ℂ) :
    ‖∑ x, ∑ y, (f x y + g x y)‖ ≤ ‖∑ x, ∑ y, f x y‖ + ‖∑ x, ∑ y, g x y‖ := by
  simp only [Finset.sum_add_distrib]
  exact norm_add_le _ _

/-- **(i), deterministic**: `‖[𝒦∼(𝓛-𝒦)]^l‖` for `3 ≤ l ≤ n`.  The `𝒦`-piece (length `l`) has
`‖𝒦_J‖ ≤ ε M^{-(|J|-1)}` and `(R, δ_K)` decay; the `𝓛-𝒦` piece has length `p = n+2-l` and is
bounded by `Ξ^{(𝓛-𝒦)}_p M^{-p}`. -/
private theorem bcalE_det_i (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {n l : ℕ} (hl3 : 3 ≤ l) (hln : l ≤ n) {R δK ε : ℝ}
    (hR : 0 ≤ R) (hδK : 0 ≤ δK) (hε : 0 ≤ ε)
    (hKb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n →
      ‖KLoop.Kcal L W E u J‖ ≤ ε * (scaleM L W E u)⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L n R δK (KLoop.Kcal L W E u)) (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    ‖ksimLK L W E u M l (loopOf σ a)‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (2 *
      ((2 * R + 1) ^ 2 * (xiLK L W E u M (n + 2 - l) * (scaleM L W E u)⁻¹ ^ (n + 2 - l) *
          (ε * (scaleM L W E u)⁻¹ ^ (l - 1))) +
        (L : ℝ) ^ 2 * (xiLK L W E u M (n + 2 - l) * (scaleM L W E u)⁻¹ ^ (n + 2 - l) * δK)))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = n := bcalE_length_loopOf σ a
  have hI : I.WF := bcalE_WF_loopOf σ a
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hpos.le
  set Bp : ℝ := xiLK L W E u M (n + 2 - l) * (scaleM L W E u)⁻¹ ^ (n + 2 - l) with hBp
  set Bl : ℝ := ε * (scaleM L W E u)⁻¹ ^ (l - 1) with hBl
  have hBp0 : 0 ≤ Bp := mul_nonneg (bcalE_xiLK_nonneg E u M hpos _) (pow_nonneg hMi _)
  have hBl0 : 0 ≤ Bl := mul_nonneg hε (pow_nonneg hMi _)
  have hT0 : 0 ≤ (2 * R + 1) ^ 2 * (Bp * Bl) + (L : ℝ) ^ 2 * (Bp * δK) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hBp0 hBl0))
      (mul_nonneg (sq_nonneg _) (mul_nonneg hBp0 hδK))
  unfold ksimLK
  rw [norm_mul, hW2, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine bcalE_sum_pairs n _ (mul_nonneg (by norm_num) hT0) fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have hl'I : l' ≤ I.length := hlen ▸ hl'.2
  have hlenL : ∀ x, (I.cutGlueL k l' x).length = k + n - l' + 1 := fun x => by
    rw [LoopIdx.length_cutGlueL I x hk.1 hl'.1 hl'I, hlen]
  have hlenR : ∀ y, (I.cutGlueR k l' y).length = l' - k + 1 := fun y =>
    LoopIdx.length_cutGlueR I y hk.1 hl'.1 hl'I
  have hlenL' : ∀ x, (I.cutGlueL k l' x).a.length = k + n - l' + 1 := hlenL
  have hlenR' : ∀ y, (I.cutGlueR k l' y).a.length = l' - k + 1 := hlenR
  refine (bcalE_norm_sum_add _ _).trans ?_
  -- the first term: `𝓛-𝒦` on the left piece, `𝒦` on the right piece
  have hT1 : ‖∑ x : Z2 L, ∑ y : Z2 L,
      (if (I.cutGlueR k l' y).length = l then
        LKf L W E u M (I.cutGlueL k l' x) * SB L x y * KLoop.Kcal L W E u (I.cutGlueR k l' y)
      else 0)‖ ≤ (2 * R + 1) ^ 2 * (Bp * Bl) + (L : ℝ) ^ 2 * (Bp * δK) := by
    by_cases hc : l' - k + 1 = l
    · have hcond : ∀ y, (I.cutGlueR k l' y).length = l := fun y => by rw [hlenR y]; exact hc
      simp only [hcond, ↓reduceIte]
      refine bcalE_cutR hL hI hk.1 hl'.1 hl'I (BF := Bp) (Bc := Bp) (BG := Bl) hR hBp0 hδK
        (fun x => ?_) (fun x => ?_) (fun y => ?_) (hlen ▸ hKd)
      · have := bcalE_lk_le_xiLK E u M hpos (I.cutGlueL k l' x) (hI.cutGlueL x hk.1 hl'.1 hl'I)
          (m := n + 2 - l) (by rw [hlenL']; omega)
        exact this
      · have := bcalE_lk_le_xiLK E u M hpos (I.cutGlueL k l' x) (hI.cutGlueL x hk.1 hl'.1 hl'I)
          (m := n + 2 - l) (by rw [hlenL']; omega)
        exact this
      · have h := hKb (I.cutGlueR k l' y) (hI.cutGlueR y hk.1 hl'.1 hl'I) (by rw [hcond y]; omega)
          (by rw [hlenR y]; omega)
        rw [hcond y] at h
        exact h
    · have hcond : ∀ y, ¬ (I.cutGlueR k l' y).length = l := fun y => by rw [hlenR y]; exact hc
      simp only [hcond, ↓reduceIte, Finset.sum_const_zero, norm_zero]
      exact hT0
  -- the second term: `𝒦` on the left piece, `𝓛-𝒦` on the right piece
  have hT2 : ‖∑ x : Z2 L, ∑ y : Z2 L,
      (if (I.cutGlueL k l' x).length = l then
        KLoop.Kcal L W E u (I.cutGlueL k l' x) * SB L x y * LKf L W E u M (I.cutGlueR k l' y)
      else 0)‖ ≤ (2 * R + 1) ^ 2 * (Bp * Bl) + (L : ℝ) ^ 2 * (Bp * δK) := by
    by_cases hc : k + n - l' + 1 = l
    · have hcond : ∀ x, (I.cutGlueL k l' x).length = l := fun x => by rw [hlenL x]; exact hc
      have h1 : ∀ x y, (if (I.cutGlueL k l' x).length = l then
            KLoop.Kcal L W E u (I.cutGlueL k l' x) * SB L x y * LKf L W E u M (I.cutGlueR k l' y)
          else 0) =
          KLoop.Kcal L W E u (I.cutGlueL k l' x) * SB L x y * LKf L W E u M (I.cutGlueR k l' y) :=
        fun x y => by simp only [hcond x, ↓reduceIte]
      simp only [h1]
      have hb := bcalE_cutL hL hI hk.1 hl'.1 hl'I (F := KLoop.Kcal L W E u)
        (G := LKf L W E u M) (BF := Bl) (BG := Bp) (Bc := Bp) (δF := δK) hR hBp0 hδK
        (fun x => ?_) (fun y => ?_) (fun y => ?_) (hlen ▸ hKd)
      · calc _ ≤ _ := hb
          _ = _ := by ring
      · have h := hKb (I.cutGlueL k l' x) (hI.cutGlueL x hk.1 hl'.1 hl'I) (by rw [hcond x]; omega)
          (by rw [hlenL x]; omega)
        rw [hcond x] at h
        exact h
      · have := bcalE_lk_le_xiLK E u M hpos (I.cutGlueR k l' y) (hI.cutGlueR y hk.1 hl'.1 hl'I)
          (m := n + 2 - l) (by rw [hlenR']; omega)
        exact this
      · have := bcalE_lk_le_xiLK E u M hpos (I.cutGlueR k l' y) (hI.cutGlueR y hk.1 hl'.1 hl'I)
          (m := n + 2 - l) (by rw [hlenR']; omega)
        exact this
    · have hcond : ∀ x, ¬ (I.cutGlueL k l' x).length = l := fun x => by rw [hlenL x]; exact hc
      simp only [hcond, ↓reduceIte, Finset.sum_const_zero, norm_zero]
      exact hT0
  linarith

/-- **(ii), deterministic**: `‖𝓔^{LK×LK}‖` from the `Ξ^{(𝓛-𝒦)}` bounds (relative, on the window)
and the decay of the right piece (`(R, δ)`, crude bound `B` on the left piece). -/
private theorem bcalE_det_ii (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {n : ℕ} (hn : 2 ≤ n) {R δ B : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hB : 0 ≤ B)
    (hLKb : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n → ‖LKf L W E u M J‖ ≤ B)
    (hdLK : LoopDecay L n R δ (LKf L W E u M)) (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    ‖elklkN L W E u M (loopOf σ a)‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) ^ 2 *
      ((2 * R + 1) ^ 2 * ((∑ m ∈ Finset.Icc 2 n,
          xiLK L W E u M m * xiLK L W E u M (n - m + 2)) * (scaleM L W E u)⁻¹ ^ (n + 2)) +
        (L : ℝ) ^ 2 * (B * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = n := bcalE_length_loopOf σ a
  have hI : I.WF := bcalE_WF_loopOf σ a
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hpos.le
  have hXn : ∀ m, 0 ≤ xiLK L W E u M m := fun m => bcalE_xiLK_nonneg E u M hpos m
  set Ssum : ℝ := ∑ m ∈ Finset.Icc 2 n, xiLK L W E u M m * xiLK L W E u M (n - m + 2) with hSsum
  have hS0 : 0 ≤ Ssum := Finset.sum_nonneg fun m _ => mul_nonneg (hXn _) (hXn _)
  have hT0 : 0 ≤ (2 * R + 1) ^ 2 * (Ssum * (scaleM L W E u)⁻¹ ^ (n + 2)) +
      (L : ℝ) ^ 2 * (B * δ) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hS0 (pow_nonneg hMi _)))
      (mul_nonneg (sq_nonneg _) (mul_nonneg hB hδ))
  unfold elklkN
  rw [norm_mul, hW2, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine bcalE_sum_pairs n _ hT0 fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have hl'I : l' ≤ I.length := hlen ▸ hl'.2
  have hlenL' : ∀ x, (I.cutGlueL k l' x).a.length = n - (l' - k + 1) + 2 := fun x => by
    change (I.cutGlueL k l' x).length = _
    rw [LoopIdx.length_cutGlueL I x hk.1 hl'.1 hl'I, hlen]; omega
  have hlenR' : ∀ y, (I.cutGlueR k l' y).a.length = l' - k + 1 := fun y =>
    LoopIdx.length_cutGlueR I y hk.1 hl'.1 hl'I
  have hq2 : 2 ≤ l' - k + 1 := by omega
  have hqn : l' - k + 1 ≤ n := by omega
  have hcut := bcalE_cutR hL hI hk.1 hl'.1 hl'I (F := LKf L W E u M) (G := LKf L W E u M)
    (BF := xiLK L W E u M (n - (l' - k + 1) + 2) * (scaleM L W E u)⁻¹ ^ (n - (l' - k + 1) + 2))
    (Bc := B) (BG := xiLK L W E u M (l' - k + 1) * (scaleM L W E u)⁻¹ ^ (l' - k + 1))
    (δG := δ) hR hB hδ
    (fun x => bcalE_lk_le_xiLK E u M hpos _ (hI.cutGlueL x hk.1 hl'.1 hl'I) (hlenL' x))
    (fun x => hLKb _ (hI.cutGlueL x hk.1 hl'.1 hl'I) (by
        change 1 ≤ (I.cutGlueL k l' x).a.length; rw [hlenL']; omega)
      (by change (I.cutGlueL k l' x).a.length ≤ n; rw [hlenL']; omega))
    (fun y => bcalE_lk_le_xiLK E u M hpos _ (hI.cutGlueR y hk.1 hl'.1 hl'I) (hlenR' y))
    (hlen ▸ hdLK)
  have hterm : xiLK L W E u M (l' - k + 1) * xiLK L W E u M (n - (l' - k + 1) + 2) ≤ Ssum :=
    Finset.single_le_sum (f := fun m => xiLK L W E u M m * xiLK L W E u M (n - m + 2))
      (fun m _ => mul_nonneg (hXn _) (hXn _)) (Finset.mem_Icc.2 ⟨hq2, hqn⟩)
  have hpow : (scaleM L W E u)⁻¹ ^ (n - (l' - k + 1) + 2) * (scaleM L W E u)⁻¹ ^ (l' - k + 1) =
      (scaleM L W E u)⁻¹ ^ (n + 2) := by
    rw [← pow_add]; congr 1; omega
  refine hcut.trans ?_
  refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) _
  calc _ = (xiLK L W E u M (l' - k + 1) * xiLK L W E u M (n - (l' - k + 1) + 2)) *
        ((scaleM L W E u)⁻¹ ^ (n - (l' - k + 1) + 2) * (scaleM L W E u)⁻¹ ^ (l' - k + 1)) := by
        ring
    _ = (xiLK L W E u M (l' - k + 1) * xiLK L W E u M (n - (l' - k + 1) + 2)) *
        (scaleM L W E u)⁻¹ ^ (n + 2) := by rw [hpow]
    _ ≤ Ssum * (scaleM L W E u)⁻¹ ^ (n + 2) :=
        mul_le_mul_of_nonneg_right hterm (pow_nonneg hMi _)

/-- **(iii), deterministic**: `‖𝓔^{(G̃)}‖` from a bound `A` on `⟨(G-m)E_a⟩` (both signs), the
decay of `𝓛` on loops of length `n+1`, and `Ξ^{(𝓛)}_{n+1}`. -/
private theorem bcalE_det_iii (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {n : ℕ} (hn : 1 ≤ n) {R δ A : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (havg : ∀ s' a', ‖avgErr L W E u M s' a'‖ ≤ A)
    (hdLL : LoopDecay L (n + 1) R δ (LLf L W E u M)) (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    ‖egtN L W E u M (loopOf σ a)‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) *
      ((2 * R + 1) ^ 2 * (A * (xiL L W E u M (n + 1) * (scaleM L W E u)⁻¹ ^ n)) +
        (L : ℝ) ^ 2 * (A * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = n := bcalE_length_loopOf σ a
  have hI : I.WF := bcalE_WF_loopOf σ a
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hpos.le
  unfold egtN
  rw [norm_mul, hW2, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 n, ‖∑ x : Z2 L, ∑ y : Z2 L,
        avgErr L W E u M (I.σ.getD (k - 1) false) x * SB L x y * LLf L W E u M (I.cutGlue k y)‖
      ≤ ∑ k ∈ Finset.Icc 1 n, ((2 * R + 1) ^ 2 *
          (A * (xiL L W E u M (n + 1) * (scaleM L W E u)⁻¹ ^ n)) + (L : ℝ) ^ 2 * (A * δ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.mem_Icc] at hk
        have hkI : k ≤ I.length := hlen ▸ hk.2
        obtain ⟨c, hc⟩ : ∃ c : Z2 L, c ∈ I.a :=
          ⟨a ⟨0, by omega⟩, bcalE_mem_loopOf σ a ⟨0, by omega⟩⟩
        have e : ∑ x : Z2 L, ∑ y : Z2 L,
            avgErr L W E u M (I.σ.getD (k - 1) false) x * SB L x y *
              LLf L W E u M (I.cutGlue k y) =
            ∑ x : Z2 L, ∑ y : Z2 L, SB L x y *
              (avgErr L W E u M (I.σ.getD (k - 1) false) x * LLf L W E u M (I.cutGlue k y)) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        rw [e]
        refine norm_sum_SB_le_right L hL hR (mul_nonneg hA hδ) c
          (fun x y => avgErr L W E u M (I.σ.getD (k - 1) false) x *
            LLf L W E u M (I.cutGlue k y)) (fun x y => ?_) (fun x y hy => ?_)
        · show ‖avgErr L W E u M (I.σ.getD (k - 1) false) x * LLf L W E u M (I.cutGlue k y)‖ ≤
            A * (xiL L W E u M (n + 1) * (scaleM L W E u)⁻¹ ^ n)
          rw [norm_mul]
          refine mul_le_mul (havg _ _) ?_ (norm_nonneg _) hA
          have := bcalE_ll_le_xiL E u M hpos (I.cutGlue k y) (hI.cutGlue y hk.1 hkI) (m := n + 1)
            (by change (I.cutGlue k y).length = n + 1; rw [LoopIdx.length_cutGlue I y hkI, hlen])
          simpa using this
        · change ‖avgErr L W E u M (I.σ.getD (k - 1) false) x * LLf L W E u M (I.cutGlue k y)‖ ≤
            A * δ
          rw [norm_mul]
          refine mul_le_mul (havg _ _) ?_ (norm_nonneg _) hA
          exact hdLL _ (hI.cutGlue y hk.1 hkI)
            (by rw [LoopIdx.length_cutGlue I y hkI, hlen]) y (mem_cutGlue I y k) c
            (mem_cutGlue_of_mem I y k hc) hy
    _ = (n : ℝ) * ((2 * R + 1) ^ 2 * (A * (xiL L W E u M (n + 1) * (scaleM L W E u)⁻¹ ^ n)) +
          (L : ℝ) ^ 2 * (A * δ)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- `b` is a label of the `(2n+2)`-loop of `𝓔⊗𝓔`. -/
private theorem bcalE_mem_eeLoop_b (σ : List Bool) (a a' : List (Z2 L)) (k : ℕ) (b b' : Z2 L) :
    b ∈ (eeLoop L σ a a' k b b').a := by
  simp [eeLoop]

/-- **(iv), deterministic**: `‖𝓔⊗𝓔‖` from the decay of `𝓛` on loops of length `2n+2` and
`Ξ^{(𝓛)}_{2n+2}`. -/
private theorem bcalE_det_iv (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {n : ℕ} (hn : 1 ≤ n) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hdLL : LoopDecay L (2 * n + 2) R δ (LLf L W E u M)) (σ : Fin n → Bool)
    (a a' : Fin n → Z2 L) :
    ‖eeN L W E u M σ a a'‖ ≤ (W : ℝ) ^ 2 * ((n : ℝ) *
      ((2 * R + 1) ^ 2 * (xiL L W E u M (2 * n + 2) * (scaleM L W E u)⁻¹ ^ (2 * n + 1)) +
        (L : ℝ) ^ 2 * δ)) := by
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hMi : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hpos.le
  unfold eeN
  rw [norm_mul, hW2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 n, ‖∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖
      ≤ ∑ k ∈ Finset.Icc 1 n, ((2 * R + 1) ^ 2 *
          (xiL L W E u M (2 * n + 2) * (scaleM L W E u)⁻¹ ^ (2 * n + 1)) +
          (L : ℝ) ^ 2 * δ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.mem_Icc] at hk
        have hwf : ∀ b b' : Z2 L, (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').WF :=
          fun b b' => eeLoop_WF _ _ _ hk.1 (by simpa using hk.2) (by simp) (by simp) b b'
        have hlenE : ∀ b b' : Z2 L,
            (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a.length = 2 * n + 2 :=
          fun b b' => by
            have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k)
              (by simp; omega) (by simp) b b'
            simpa [LoopIdx.length] using this
        refine norm_sum_SB_le_left L hL hR hδ (a ⟨0, by omega⟩)
          (fun b b' => LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))
          (fun b b' => ?_) (fun b b' hb => ?_)
        · have := bcalE_ll_le_xiL E u M hpos _ (hwf b b') (hlenE b b')
          have e : 2 * n + 2 - 1 = 2 * n + 1 := by omega
          rw [e] at this
          exact this
        · exact hdLL _ (hwf b b') (by have := hlenE b b'; simp only [LoopIdx.length]; omega) b
            (bcalE_mem_eeLoop_b _ _ _ _ _ _) (a ⟨0, by omega⟩)
            (mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨⟨0, by omega⟩, rfl⟩)) hb
    _ = (n : ℝ) * ((2 * R + 1) ^ 2 *
          (xiL L W E u M (2 * n + 2) * (scaleM L W E u)⁻¹ ^ (2 * n + 1)) +
          (L : ℝ) ^ 2 * δ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

end Det

/-! ## 6. The one-loop control `⟨(G-m)E_a⟩ ≺ M^{-1}` -/

section PTHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- Reindexing plus pointwise rewriting of both sides. -/
private theorem bcalE_pt_transfer {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {ξ' ζ' : ∀ l, U' l → Ω → ℝ} (f : ∀ l, U' l → U l)
    (hξ : ∀ l u ω, ξ' l u ω = ξ l (f l u) ω) (hζ : ∀ l u ω, ζ' l u ω = ζ l (f l u) ω)
    (h : PerTimeDomAt P size ξ ζ) : PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  have hset : {ω | (size l : ℝ) ^ τ * ζ' l u ω < ξ' l u ω} =
      {ω | (size l : ℝ) ^ τ * ζ l (f l u) ω < ξ l (f l u) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, hζ]
  rw [hset]
  exact hl (f l u)

/-- A bound that holds deterministically (up to `N^δ` for every `δ > 0`) gives `≺`. -/
private theorem bcalE_pt_of_det {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ δ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ δ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ] with l hl u
  have hE : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [hE, measure_empty]
  exact zero_le

end PTHelpers

section ScalesAvg

variable (d : Sizes)

private theorem bcalE_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem bcalE_one_le_W (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem bcalE_hsize (h : SizeTendsto d) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

private theorem bcalE_size_ge_W_sq (n : ℕ) : (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have h : d.W n ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]
    exact Nat.le_mul_of_pos_right _ (by have := bcalE_one_le_L d n; positivity)
  exact_mod_cast h

/-- `M_u ≥ μ N^{c₀}` for all `u ≤ t n`, eventually. -/
private theorem bcalE_lower {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) :
    ∃ μ c₀ : ℝ, 0 < μ ∧ 0 < c₀ ∧ (∀ n, μ ≤ (spectralM (E n)).im) ∧
      (∀ n, (spectralM (E n)).im ≤ 1) ∧
      ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
        μ * ((d.size n : ℕ) : ℝ) ^ c₀ ≤ scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, hc, hτ, -, -, -, -, hB, -, hR, -, -, -⟩ := hmain
  obtain ⟨μ, hμ, hμb⟩ := bcalE_im_bounds hE hκ
  refine ⟨μ, min (2 * c) τ, hμ, lt_min (by linarith) hτ, fun n => (hμb n).1, fun n => (hμb n).2, ?_⟩
  filter_upwards [scaleFacts_R1 d κ c τ E t hE hκ hc hτ hB hR] with n hn u hu
  refine le_trans ?_ (hn u hu)
  exact mul_le_mul_of_nonneg_right (hμb n).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Positivity of the scale on `(-∞, t n]`. -/
private theorem bcalE_scale_pos {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) {u : ℝ} (hu : u ≤ t n) : 0 < scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, -, -, -, -, ht1, -⟩ := hmain
  exact scaleM_pos (bcalE_one_le_L d n) (bcalE_one_le_W d n) (by linarith [hE n])
    (lt_of_le_of_lt hu (ht1 n))

/-- The elementary time facts on `[s n, t n]`. -/
private theorem bcalE_time_facts {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) (u : TimeIcc s t n) : |E n| < 2 ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 := by
  obtain ⟨hκ, hE, -, -, hs0, -, ht1, -⟩ := hmain
  exact ⟨by linarith [hE n], le_trans (hs0 n) u.2.1, lt_of_le_of_lt u.2.2 (ht1 n)⟩

/-- (`KboundConcl`) `‖𝒦_{u,σ,a}‖ ≺ M_u^{-(k-1)}` per time, deterministically. -/
private theorem bcalE_Kbound_pt {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KboundConcl κ) (k : ℕ) (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p _ => ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  refine bcalE_pt_of_det fun δ hδ => ?_
  filter_upwards [hsize.eventually (hK k hk δ hδ)] with n hn p ω
  obtain ⟨hE2, hu0, hu1⟩ := bcalE_time_facts d hmain' n p.1
  have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
    p.1, hu0, hu1⟩, p.2.1, p.2.2⟩
  have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ δ * (KLoop.Mt (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1) := h
  rw [kloop_Mt_eq hu1.le] at h'
  exact h'

end ScalesAvg

section ChargeAvg

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem bcalE_loopOf_two (s₁ s₂ : Bool) (a b : Z2 L) :
    loopOf (![s₁, s₂] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) = ⟨[s₁, s₂], [a, b]⟩ := by
  simp [loopOf, List.ofFn_succ]

/-- Conjugating the `+` one-loop gives the `-` one-loop. -/
private theorem bcalE_avgErr_false (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (a : Z2 L) :
    avgErr L W E u M false a = star (avgErr L W E u M true a) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hG : (greenBlk L W E u M true)ᴴ = greenBlk L W E u M false :=
    Gsig_conjTranspose hH (spectralZ E u) true
  have hm : star (KLoop.mSig E true) = KLoop.mSig E false := by
    simp [KLoop.mSig]
  unfold avgErr
  rw [← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hG, hm]

/-- `𝒦` at `(+,-)` is `Kpm`. -/
private theorem bcalE_Kpm_eq (E u : ℝ) (a b : Z2 L) :
    Kpm L W E u a b = KLoop.Kcal L W E u ⟨[true, false], [a, b]⟩ := by
  rw [KLoop.Kcal_two]
  unfold Kpm
  have : KLoop.mSig E true * KLoop.mSig E false = (Complex.normSq (spectralM E) : ℂ) := by
    simp [KLoop.mSig, Complex.mul_conj]
  rw [this, inv_pow]

end ChargeAvg

section OneLoop

variable (d : Sizes)

/-- **`max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ M_u^{-1}`** per time over `[s,t]`, from `KboundConcl`
(`n = 2`) and `Step2DecayPT` at `D = 2` (`(η_s/η_u)^4 ≤ M_u` by
`scaleM_ge_pow29`, `W^{-2} ≤ M_u^{-1}` by `M_u ≤ W²`). -/
private theorem bcalE_loopDet {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hdec : Step2DecayPT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := bcalE_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => bcalE_scale_pos d hmain' n u.2.2
  -- (1) `‖Kpm‖ ≺ M⁻¹`
  have h1 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => ‖Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
    refine bcalE_pt_transfer (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p => (p.1, ((![true, false] : Fin 2 → Bool),
        (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))))) ?_ ?_ (bcalE_Kbound_pt d hmain' hKb 2 (by norm_num))
    · intro n p ω
      simp only []
      rw [bcalE_loopOf_two, bcalE_Kpm_eq]
    · intro n p ω
      simp
  -- (2) `lkErrMat ≺ M⁻¹`
  have h2 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize
      (fun n p _ => inv_nonneg.2 (hpos n p.1).le) 2 ?_ (hdec 2 (by norm_num))
    filter_upwards [hC] with n hCn p ω
    obtain ⟨u, a, b⟩ := p
    obtain ⟨hE2, hu0, hu1⟩ := bcalE_time_facts d hmain' n u
    have hM := hpos n u
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hut : (u : ℝ) ≤ t n := u.2.2
    have hx29 := scaleM_ge_pow29 (bcalE_one_le_L d n) (bcalE_one_le_W d n) hE2 (hs0 n) hsu hut
      (ht1 n) hCn
    have hxu : 0 < 1 - (u : ℝ) := by linarith
    have hx1 : 1 ≤ (1 - s n) / (1 - (u : ℝ)) := by
      rw [le_div_iff₀ hxu]; linarith
    have hx4 : ((1 - s n) / (1 - (u : ℝ))) ^ 4 ≤ scaleM (d.L n) (d.W n) (E n) u :=
      (pow_le_pow_right₀ hx1 (by norm_num)).trans hx29
    have hMW : scaleM (d.L n) (d.W n) (E n) u ≤ (d.W n : ℝ) ^ 2 := by
      rw [scaleM_eq (bcalE_one_le_L d n) hu1]
      have him0 : 0 ≤ (spectralM (E n)).im := (spectralM_im_pos hE2).le
      have hW2 : (0 : ℝ) ≤ (d.W n : ℝ) ^ 2 := by positivity
      have hmin : min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) ≤ 1 := min_le_left _ _
      have hmin0 : 0 ≤ min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) :=
        le_min zero_le_one (mul_nonneg (by positivity) hxu.le)
      calc (d.W n : ℝ) ^ 2 * (spectralM (E n)).im *
            min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ)))
          ≤ (d.W n : ℝ) ^ 2 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (him1 n) hW2) hmin hmin0 (by positivity)
        _ = (d.W n : ℝ) ^ 2 := by ring
    rw [etaT_div_etaT hE2 (by linarith) hu1]
    set Q := (scaleM (d.L n) (d.W n) (E n) u)⁻¹ with hQ
    have hQ0 : 0 < Q := inv_pos.2 hM
    have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast bcalE_one_le_W d n
    have he1 : Real.exp (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) / ellT (d.L n) u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
    have he0 := (Real.exp_pos (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) /
      ellT (d.L n) u))).le
    have hw : (d.W n : ℝ) ^ (-(2 : ℝ)) ≤ Q := by
      rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hQ]
      exact inv_anti₀ hM hMW
    have hr : ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ ≤ Q := by
      calc ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹
          ≤ scaleM (d.L n) (d.W n) (E n) u * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hx4 (inv_nonneg.2 (sq_nonneg _))
        _ = Q := by rw [hQ]; field_simp
    have hr0 : 0 ≤ ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ :=
      mul_nonneg (pow_nonneg (by linarith [hx1]) _) (inv_nonneg.2 (sq_nonneg _))
    calc ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) / ellT (d.L n) u)) +
          (d.W n : ℝ) ^ (-(2 : ℝ))
        ≤ Q * 1 + Q := add_le_add (mul_le_mul hr he1 he0 hQ0.le) hw
      _ = 2 * Q := by ring
  -- (3) assemble
  have h3 := PerTimeCalc.PerTime.perTimeCalc_add hsize h1 h2
  have h4 := PerTimeCalc.PerTime.stochDom_of_le_left_eventually
    (ξ := fun n (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) ω =>
      ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖)
    (Eventually.of_forall fun n p ω => by
      have hx : loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 =
          (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n p.1 ω)) (spectralZ (E n) p.1)
            (pmLoop p.2.1 p.2.2) - Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2) +
            Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2 := by
        unfold loopPM; ring
      change ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖ ≤
        ‖Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2‖ +
          lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2
      rw [hx]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      unfold lkErrMat; ring) h3
  exact PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n p _ => inv_nonneg.2 (hpos n p.1).le) 2
    (Eventually.of_forall fun n p ω => by linarith) h4

/-- **The one-loop control (`n = 1`)**: `‖⟨(G_u - m) E_a⟩‖ ≺ M_u⁻¹` per time over `[s,t]`, from the (`GavLGEX`)
clause of `GbEXPHypV3 d (κ/2) c τ` at every time sequence `u ∈ [s,t]`, with the deterministic
control `Ψ² = M_u⁻¹` (`LoopDetSeq` from `bcalE_loopDet`) and (`asGMc`) from `Step2LocalPT`.  The
proof is that of `s45_one_loop` with `Step3PT` at `k = 2` replaced by `bcalE_loopDet`. -/
private theorem bcalE_one_loop {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := bcalE_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  refine RBM.Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst
    (V := fun n => Z2 (d.L n)) (fun n => ⟨0⟩)
    (fun n v q ω => ‖avgErr (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) true q‖)
    (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹) ?_
  intro u hu
  obtain ⟨hN', hB', hE', hu0, hu1, hRu⟩ := RBM.Green.v3_premises_of_mainIndHyp d hmain' u hu
  have hMpos : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (u n) :=
    fun n => bcalE_scale_pos d hmain' n (hu n).2
  -- (asGMc) at the exponent `c₀`, from `Step2LocalPT`
  have hAs : RBM.Green.AsGMcSeq d E u c₀ := by
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ ((1 : ℝ) / 2)) hloc u hu
    unfold RBM.Green.AsGMcSeq
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n p _ => Real.rpow_nonneg
      (Nat.cast_nonneg _) _) (Real.sqrt μ⁻¹) ?_ h1
    filter_upwards [hlow] with n hn q ω
    have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast bcalE_one_le_W d n
    have hy : 0 < (d.W n : ℝ) ^ c₀ := Real.rpow_pos_of_pos hW0 _
    have hpow : ((d.W n : ℝ) ^ c₀) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ c₀ := by
      calc ((d.W n : ℝ) ^ c₀) ^ 2 = ((d.W n : ℝ) ^ 2) ^ c₀ := by
            rw [sq, sq, Real.mul_rpow hW0.le hW0.le]
        _ ≤ ((d.size n : ℕ) : ℝ) ^ c₀ :=
            Real.rpow_le_rpow (by positivity) (bcalE_size_ge_W_sq d n) hc₀.le
    have hM : μ * ((d.W n : ℝ) ^ c₀) ^ 2 ≤ scaleM (d.L n) (d.W n) (E n) (u n) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hμ.le) (hn (u n) (hu n).2)
    have hinv : (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤
        μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by
      calc (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤ (μ * ((d.W n : ℝ) ^ c₀) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) hM
        _ = μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by rw [mul_inv, inv_pow]
    rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹
        ≤ Real.sqrt (μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt μ⁻¹ * ((d.W n : ℝ) ^ c₀)⁻¹ := by
          rw [Real.sqrt_mul (inv_nonneg.2 hμ.le), Real.sqrt_sq (inv_nonneg.2 hy.le)]
  -- the deterministic control `Ψ² = M_u⁻¹`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n,
      Ψ n = Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := ⟨_, fun _ => rfl⟩
  have hΨsq : ∀ n, Ψ n ^ 2 = (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := fun n => by
    rw [hΨ, Real.sq_sqrt (inv_nonneg.2 (hMpos n).le)]
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => by rw [hΨ]; exact Real.sqrt_nonneg _
  have hΨev : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4)) := by
    filter_upwards [hlow, ((tendsto_rpow_atTop (half_pos hc₀)).comp hN).eventually_ge_atTop μ⁻¹]
      with n hn hgrow
    have hgrow' : μ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := hgrow
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNpos : 0 < ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) :=
      lt_of_lt_of_le (inv_pos.2 hμ) hgrow'
    have h1 : 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      calc (1 : ℝ) = μ * μ⁻¹ := (mul_inv_cancel₀ hμ.ne').symm
        _ ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := mul_le_mul_of_nonneg_left hgrow' hμ.le
    have hsplit : ((d.size n : ℕ) : ℝ) ^ c₀ =
        ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      rw [← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
    have hM : ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) ≤ scaleM (d.L n) (d.W n) (E n) (u n) := by
      refine le_trans ?_ (hn (u n) (hu n).2)
      rw [hsplit]
      nlinarith
    rw [hΨ, Real.sqrt_le_iff]
    refine ⟨Real.rpow_nonneg hN0 _, ?_⟩
    have hsq : (((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4))) ^ 2 =
        (((d.size n : ℕ) : ℝ) ^ (c₀ / 2))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_neg hN0]
      congr 1; push_cast; ring
    rw [hsq]
    exact inv_anti₀ hNpos hM
  -- the loop control `LoopDetSeq` from `bcalE_loopDet`
  have hLoop : RBM.Green.LoopDetSeq d E u Ψ := by
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Z2 (d.L n) × Z2 (d.L n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => ‖loopPM (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2‖)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹) (bcalE_loopDet d hmain' hKb hdec) u hu
    unfold RBM.Green.LoopDetSeq
    exact bcalE_pt_transfer (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n)) (fun n p => p)
      (fun _ _ _ => rfl) (fun n p ω => hΨsq n) h1
  have hGav : RBM.Green.GavLDetSeq d E u Ψ :=
    ((hV3 hN' hB' E u hE' hu0 hu1 hRu c₀ hc₀).2.2 hAs).2.2 Ψ (c₀ / 4) (by positivity) hΨ0 hΨev
      hLoop
  unfold RBM.Green.GavLDetSeq at hGav
  exact bcalE_pt_transfer (U := fun n => Unit × Z2 (d.L n)) (fun n p => p) (fun _ _ _ => rfl)
    (fun n p ω => (hΨsq n).symm) hGav

end OneLoop

/-! ## 7. The good event (per size and time) -/

section Core

variable (d : Sizes)

/-- **The good event** (the analogue of `BcalEDecay.bcalEDecay_core`, which is private).  Eventually
in `n`, for every time `u ∈ [s_n, t_n]` there is an event `S` of probability `≤ N^{-D_p}` off
which: `𝓛` and `𝓛 - 𝒦` have `(ℓ_u W^{τ₁}, N^{τ_d} W^{-D''})` decay on well-formed loops of length
`≤ K` (`DecayLoopPT`, union bound over `≤ K N^{2K}` loops); `‖𝓛_J‖, ‖𝒦_J‖ ≤ N^{K}` on
well-formed loops of length in `[1, K]`; and `|⟨(G_u(σ) - m(σ)) E_a⟩| ≤ N^{τ₂} M_u^{-1}` for both
signs and every `a` (`hav`, union bound over `L² ≤ N` labels). -/
private theorem bcalE_core {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hDL : DecayLoopPT d E s t)
    (hav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹))
    (K : ℕ) (hK : 1 ≤ K) {τ1 D'' τd Dp τ2 : ℝ} (hτ1 : 0 < τ1) (hD'' : 0 < D'') (hτd : 0 < τd)
    (hDp : 0 < Dp) (hτ2 : 0 < τ2) :
    ∀ᶠ n : ℕ in atTop,
      (K : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 2 ≤ ((d.size n : ℕ) : ℝ) ∧
      ∀ u : TimeIcc s t n,
        ∃ S : Set (Sizes.SeqΩ d), Sizes.seqP d S ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) ∧
          ∀ ω ∉ S,
            LoopDecay (d.L n) K (ellT (d.L n) u * (d.W n : ℝ) ^ τ1)
              (((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D''))
              (LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)) ∧
            LoopDecay (d.L n) K (ellT (d.L n) u * (d.W n : ℝ) ^ τ1)
              (((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D''))
              (LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)) ∧
            (∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
              ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) J‖ ≤
                ((d.size n : ℕ) : ℝ) ^ K) ∧
            (∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
              ‖KLoop.Kcal (d.L n) (d.W n) (E n) u J‖ ≤ ((d.size n : ℕ) : ℝ) ^ K) ∧
            (∀ (s' : Bool) (a : Z2 (d.L n)),
              ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) s' a‖ ≤
                ((d.size n : ℕ) : ℝ) ^ τ2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹) := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hN
  obtain ⟨μ, hμ, hμb⟩ := bcalE_im_bounds hE hκ
  set Dq : ℝ := Dp + 1 with hDq
  have hDqpos : 0 < Dq := by rw [hDq]; linarith
  set D₁ : ℝ := Dq + ((2 * K + 1 : ℕ) : ℝ) with hD₁
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  set D₂ : ℝ := Dq + 1 with hD₂
  have hD₂pos : 0 < D₂ := by rw [hD₂]; linarith
  -- eventual facts
  have e3 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hN).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have e4 : ∀ᶠ n : ℕ in atTop, (K : ℝ) + 2 ≤ ((d.size n : ℕ) : ℝ) := hN.eventually_ge_atTop _
  have e6 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 K, ∀ u : TimeIcc s t n,
      ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    filter_upwards [hsize.eventually (hKb m hm1 1 one_pos)] with n hn u σ a
    have hu0 : 0 ≤ (u : ℝ) := le_trans (hs0 n) u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
      u, hu0, hu1⟩, σ, a⟩
    have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (KLoop.Mt (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := h
    rwa [kloop_Mt_eq hu1.le] at h'
  have e8 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 K,
      ∀ p : TimeIcc s t n × (Fin m → Bool) × (Fin m → Z2 (d.L n)),
        Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 +
            lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2) *
          (if ellT (d.L n) p.1 * (d.W n : ℝ) ^ τ1 ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ)
            then 1 else 0)} ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    exact hDL m hm1 τ1 hτ1 D'' hD'' τd hτd D₁ hD₁pos
  have e9 := hav τ2 hτ2 D₂ hD₂pos
  have e10 : ∀ᶠ n : ℕ in atTop, 2 * ((d.size n : ℕ) : ℝ) ^ (-(Dp + 1)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-Dp) := hsize.eventually (eventually_two_mul_rpow_le Dp)
  filter_upwards [hR, e3, e4, e6, e8, e9, e10] with n h2 h3 h4 h6 h8 h9 h10
  -- abbreviations
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Wr : ℝ := (d.W n : ℝ) with hWr
  have hNK : (K : ℝ) ≤ N := by linarith
  have hN2 : (2 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ Wr := by rw [hWr]; exact_mod_cast d.W_pos n
  have hW0 : (0 : ℝ) < Wr := by linarith
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  refine ⟨hNK, hN2, fun u => ?_⟩
  have hu0 : 0 ≤ (u : ℝ) := le_trans (hs0 n) u.2.1
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hℓ : 1 ≤ ellT (d.L n) u := one_le_ellT hL1 hu0 hu1
  -- `η_u^{-1} ≤ N`
  have hη : ((1 - (u : ℝ)) * (spectralM (E n)).im)⁻¹ ≤ N :=
    bcalE_eta_inv hN0 (h2.trans (by linarith [u.2.2])) hμ (hμb n).1 h3
  have hη0 : 0 < (1 - (u : ℝ)) * (spectralM (E n)).im :=
    mul_pos (by linarith) (lt_of_lt_of_le hμ (hμb n).1)
  -- the two bad events
  set S₁ : Set (Sizes.SeqΩ d) := ⋃ m ∈ Finset.Icc 1 K,
    ⋃ q : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      {ω | N ^ τd * Wr ^ (-D'') <
        (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
        (if ellT (d.L n) u * Wr ^ τ1 ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0)}
    with hS₁
  set S₂ : Set (Sizes.SeqΩ d) := ⋃ a : Z2 (d.L n),
    {ω | N ^ τ2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ <
      ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) true a‖} with hS₂
  refine ⟨S₁ ∪ S₂, ?_, fun ω hω => ?_⟩
  · -- probability
    have hP1 : Sizes.seqP d S₁ ≤ ENNReal.ofReal (N ^ (-Dq)) := by
      have hU := bcalE_union (Sizes.seqP d) (Finset.Icc 1 K)
        (I := fun m => (Fin m → Bool) × (Fin m → Z2 (d.L n)))
        (fun m q => {ω | N ^ τd * Wr ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
            lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
          (if ellT (d.L n) u * Wr ^ τ1 ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0)})
        (ε := N ^ (-D₁)) (C := N ^ (2 * K)) (Real.rpow_nonneg hN0.le _) (by positivity)
        (fun m hm => bcalE_card_le d n m K (Finset.mem_Icc.1 hm).2
          (by have h := hN2; rw [hNdef] at h; exact_mod_cast h))
        (fun m hm q => h8 m hm (u, q.1, q.2))
      refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Nat.card_Icc, Nat.add_sub_cancel, hD₁]
      exact bcalE_prob_num hN1 hNK
    have hP2 : Sizes.seqP d S₂ ≤ ENNReal.ofReal (N ^ (-Dq)) := by
      have hcard : ((Fintype.card (Z2 (d.L n)) : ℕ) : ℝ) ≤ N := by
        have hLL : d.L n * d.L n ≤ d.size n := by
          rw [Sizes.size_eq]
          have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
          calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
            _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
        have : Fintype.card (Z2 (d.L n)) = d.L n * d.L n := by
          simp [Fintype.card_prod, ZMod.card]
        rw [this, hNdef]; exact_mod_cast hLL
      calc Sizes.seqP d S₂ ≤ ∑ a : Z2 (d.L n), Sizes.seqP d
            {ω | N ^ τ2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ <
              ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) true a‖} :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _a : Z2 (d.L n), ENNReal.ofReal (N ^ (-D₂)) :=
            Finset.sum_le_sum fun a _ => h9 (u, a)
        _ = ENNReal.ofReal (Fintype.card (Z2 (d.L n)) * N ^ (-D₂)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (N ^ (1 : ℝ) * N ^ (-(Dq + 1))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [Real.rpow_one, hD₂]
            exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
        _ = ENNReal.ofReal (N ^ (-Dq)) := by
            rw [RBM.rpow_mul_rpow_neg_add (N := d.size n)
              (by have h := hN1; rw [hNdef] at h; exact_mod_cast h) 1 Dq]
    calc Sizes.seqP d (S₁ ∪ S₂) ≤ Sizes.seqP d S₁ + Sizes.seqP d S₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (N ^ (-Dq)) + ENNReal.ofReal (N ^ (-Dq)) := add_le_add hP1 hP2
      _ = ENNReal.ofReal (2 * N ^ (-Dq)) := by
          rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
          ring_nf
      _ ≤ ENNReal.ofReal (N ^ (-Dp)) := ENNReal.ofReal_le_ofReal h10
  -- off the bad events
  have hω1 : ω ∉ S₁ := fun h => hω (Or.inl h)
  have hω2 : ω ∉ S₂ := fun h => hω (Or.inr h)
  simp only [hS₁, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hω1
  have hT1 : 1 ≤ N ^ τd := Real.one_le_rpow hN1 hτd.le
  have hWD0 : 0 ≤ Wr ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hgood : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ellT (d.L n) u * Wr ^ τ1 ≤ (KLoop.maxDist (d.L n) a : ℝ) →
      ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ +
        ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤
          N ^ τd * Wr ^ (-D'') := by
    intro m hm σ a hfar
    have := hω1 m hm (σ, a)
    simp only [hfar, ↓reduceIte, mul_one] at this
    exact this
  refine ⟨bcalE_loopDecay_of _ fun m hm σ a hfar => ?_,
    bcalE_loopDecay_of _ fun m hm σ a hfar => ?_, fun J hJ hJ1 hJK => ?_,
    bcalE_bound_of _ fun m hm σ a => ?_, fun s' a => ?_⟩
  · have := hgood m hm σ a hfar
    linarith [norm_nonneg (LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a))]
  · have := hgood m hm σ a hfar
    linarith [norm_nonneg (LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a))]
  · -- `‖𝓛_u(J)‖ ≤ η_u^{-|J|} ≤ N^K`
    have hH : (blockMat (Sizes.seqHflow d n u ω)).IsHermitian :=
      (Sizes.seqHflow_isHermitian d n u ω).submatrix _
    have hzim : (spectralZ (E n) u).im = (1 - (u : ℝ)) * (spectralM (E n)).im :=
      Gauss.spectralZ_im (E n) u
    have hz : (spectralZ (E n) u).im ≠ 0 := by rw [hzim]; exact hη0.ne'
    have hg := norm_gloop_le_opNorm (W := d.W n) hH hz J hJ hJ1
    have habs : |(spectralZ (E n) u).im|⁻¹ ≤ N := by
      rw [hzim, abs_of_pos hη0]; exact hη
    have hWinv : (Wr⁻¹ ^ 2) ^ (J.a.length - 1) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
    unfold LLf
    calc ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n u ω)) (spectralZ (E n) u) J‖
        ≤ |(spectralZ (E n) u).im|⁻¹ ^ J.a.length * (((d.W n : ℝ))⁻¹ ^ 2) ^ (J.a.length - 1) :=
          hg
      _ ≤ N ^ J.a.length * 1 := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) habs _) hWinv (by positivity)
            (by positivity)
      _ ≤ N ^ K := by
          rw [mul_one]; exact pow_le_pow_right₀ hN1 hJK
  · -- `‖𝒦_u(σ,a)‖ ≤ N M_u^{-(m-1)} ≤ N^m`
    have hM : (1 - (u : ℝ)) * (spectralM (E n)).im ≤ scaleM (d.L n) (d.W n) (E n) u := by
      unfold scaleM etaT
      have hWℓ : (1 : ℝ) ≤ Wr ^ 2 * ellT (d.L n) u ^ 2 := by
        have := one_le_pow₀ (n := 2) hW1
        have := one_le_pow₀ (n := 2) hℓ
        nlinarith
      nlinarith
    have hMinv : (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ N := (inv_anti₀ hη0 hM).trans hη
    have hMinv0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := inv_nonneg.2 (hη0.le.trans hM)
    have hm' := Finset.mem_Icc.1 hm
    have h6' := h6 m hm u σ a
    rw [Real.rpow_one] at h6'
    refine h6'.trans ?_
    calc N * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) ≤ N * N ^ (m - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMinv0 hMinv _) hN0.le
      _ = N ^ m := by rw [← pow_succ']; congr 1; omega
      _ ≤ N ^ K := pow_le_pow_right₀ hN1 hm'.2
  · -- the one-loop control, both signs
    have hMhalf : ∀ a : Z2 (d.L n),
        ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) true a‖ ≤
          N ^ τ2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := fun a =>
      not_lt.1 fun h => hω2 (Set.mem_iUnion.2 ⟨a, h⟩)
    cases s'
    · rw [bcalE_avgErr_false _ _ _ (Sizes.seqHflow_isHermitian d n u ω), norm_star]
      exact hMhalf a
    · exact hMhalf a

end Core

/-! ## 8. The statement `BcalEPT'` and the conjuncts -/

section Main

variable (d : Sizes)

/-- **`BcalEPT'` (`lem_BcalE`, `CalEbwXi`), the variant of `BcalEPT` with additive tails**:
as `BcalEPT`, except that (ii) `𝓔^{LK×LK}`, (iii) `𝓔^{(G̃)}` and
(iv) `𝓔⊗𝓔` carry an additive `W^{-D}` for every `D > 0`.  Reason: the far-label parts of these
three terms are bounded only by the additive decay of `DecayLoopPT`, and the random controls
`xiLK`, `xiL` have no lower bound among the hypotheses, so the purely relative form of `BcalEPT`
does not follow.  (i) and (v) are unchanged; (v) is `bcalE_labelDecay`.  The additive tails
integrate to `W^{-D}` times a polynomial factor where this statement is used (the grid endpoint
for non-alternating `σ` and the `ℬ₁–ℬ₃` terms of `int_K-L+Q2`). -/
def BcalEPT' (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  MainIndHyp d κ c τ E s t → KboundConcl κ → KcalDecay κ →
  RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
  Step2LocalPT d E s t → Step2DecayPT d E s t → DecayLoopPT d E s t →
  ∀ k : ℕ, 2 ≤ k →
    -- (i)
    (∀ l : ℕ, 3 ≤ l → l ≤ k → PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖ksimLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) l
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => (∑ m ∈ Finset.Ico 1 k,
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) m) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹)) ∧
    -- (ii)
    (∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖elklkN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => (∑ m ∈ Finset.Icc 2 k,
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) m *
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (k - m + 2) *
          (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹ + (d.W n : ℝ) ^ (-D))) ∧
    -- (iii)
    (∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖egtN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => xiL (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (k + 1) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹ + (d.W n : ℝ) ^ (-D))) ∧
    -- (iv)
    (∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖eeN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2.1
          p.2.2.2‖)
      (fun n p ω => xiL (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (2 * k + 2) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ (2 * k))⁻¹ * (etaT (E n) p.1)⁻¹ + (d.W n : ℝ) ^ (-D))) ∧
    -- (v)
    (∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ),
      PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
        (fun n p ω => (‖∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) p.1
            (Sizes.seqHflow d n p.1 ω) l (loopOf p.2.1 p.2.2)‖ +
          ‖elklkN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (loopOf p.2.1 p.2.2)‖ +
          ‖egtN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (loopOf p.2.1 p.2.2)‖) *
          farInd d n p.1 τ' p.2.2)
        (fun n _ _ => (d.W n : ℝ) ^ (-D')) ∧
      PerTimeDomAt (Sizes.seqP d) d.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)) ×
          (Fin k → Z2 (d.L n)))
        (fun n p ω => ‖eeN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2.1
            p.2.2.2‖ * farInd d n p.1 τ' (Fin.append p.2.2.1 p.2.2.2))
        (fun n _ _ => (d.W n : ℝ) ^ (-D')))

/-- The scale facts on `[s n, t n]`: `0 < M_u ≤ W²`, `1 ≤ ℓ_u`, `0 < η_u ≤ 1`. -/
private theorem bcalE_facts {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) (u : TimeIcc s t n) :
    0 < scaleM (d.L n) (d.W n) (E n) u ∧ scaleM (d.L n) (d.W n) (E n) u ≤ (d.W n : ℝ) ^ 2 ∧
      1 ≤ ellT (d.L n) u ∧ 0 < etaT (E n) u ∧ etaT (E n) u ≤ 1 := by
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := bcalE_lower d hmain
  obtain ⟨hE2, hu0, hu1⟩ := bcalE_time_facts d hmain n u
  have hpos := bcalE_scale_pos d hmain n u.2.2
  have hx : 0 < 1 - (u : ℝ) := by linarith
  refine ⟨hpos, ?_, one_le_ellT (bcalE_one_le_L d n) hu0 hu1, etaT_pos hE2 hu1, ?_⟩
  · rw [scaleM_eq (bcalE_one_le_L d n) hu1]
    have hW2 : (0 : ℝ) ≤ (d.W n : ℝ) ^ 2 := by positivity
    have hmin : min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) ≤ 1 := min_le_left _ _
    have hmin0 : 0 ≤ min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) :=
      le_min zero_le_one (mul_nonneg (by positivity) hx.le)
    calc (d.W n : ℝ) ^ 2 * (spectralM (E n)).im * min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ)))
        ≤ (d.W n : ℝ) ^ 2 * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (him1 n) hW2) hmin hmin0 (by positivity)
      _ = (d.W n : ℝ) ^ 2 := by ring
  · unfold etaT
    have h0 : (0 : ℝ) ≤ (spectralM (E n)).im := (spectralM_im_pos hE2).le
    calc (1 - (u : ℝ)) * (spectralM (E n)).im ≤ 1 * 1 :=
          mul_le_mul (by linarith) (him1 n) h0 zero_le_one
      _ = 1 := one_mul 1

/-- The arithmetic of conjunct (i), in plain reals: `M = W² ℓ² η`, near part `≤ 9 N^{τ₁} η^{-1}`
per window, far part `≤ 1` by `δ_K N^{k+2} ≤ 1`. -/
private theorem bcalE_i_arith {Wr N ℓ η M X S δK Lsq τ1 δ : ℝ} {k p l : ℕ}
    (hW1 : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hτ1 : 0 < τ1) (hδ : δ = 4 * τ1)
    (hM : M = Wr ^ 2 * ℓ ^ 2 * η) (hWN : Wr ^ 2 ≤ N) (hMN : M ≤ N) (hWL : Wr ^ 2 * Lsq = N)
    (hX0 : 0 ≤ X) (hXS : X ≤ S) (hδK0 : 0 ≤ δK) (hpl : p + (l - 1) = k + 1) (hpk : p ≤ k)
    (hδK : δK * N ^ (k + 2) ≤ 1) (h9 : 2 * (k : ℝ) ^ 2 ≤ N)
    (h8 : 18 * (k : ℝ) ^ 2 + 1 ≤ N ^ (τ1 + τ1)) :
    Wr ^ 2 * ((k : ℝ) ^ 2 * (2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 *
        (X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1))) + Lsq * (X * M⁻¹ ^ p * δK)))) ≤
      N ^ δ * (S * M⁻¹ ^ k * η⁻¹) := by
  have hW0 : 0 < Wr := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ Wr ^ 2 := one_le_pow₀ hW1
    linarith
  have hN0 : 0 < N := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMi0 : 0 < M⁻¹ := inv_pos.2 hMpos
  have hηi : 1 ≤ η⁻¹ := (one_le_inv₀ hη0).2 hη1
  have hMi : M⁻¹ = (Wr ^ 2 * ℓ ^ 2 * η)⁻¹ := by rw [hM]
  -- the near part
  have hpow1 : M⁻¹ ^ p * M⁻¹ ^ (l - 1) = M⁻¹ ^ k * M⁻¹ := by
    rw [← pow_add, ← pow_succ]; congr 1
  have hnearf := bcalE_near_factor (τ1 := τ1) hW1 hℓ hη0 hWN hτ1.le
  have hnear : Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1)))) ≤
      9 * N ^ τ1 * N ^ τ1 * (X * M⁻¹ ^ k * η⁻¹) := by
    have e1 : Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1)))) =
        (Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * M⁻¹) * (X * N ^ τ1 * M⁻¹ ^ k) := by
      have : X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1)) = X * N ^ τ1 * (M⁻¹ ^ p * M⁻¹ ^ (l - 1)) := by
        ring
      rw [this, hpow1]; ring
    rw [e1]
    have hXk : 0 ≤ X * N ^ τ1 * M⁻¹ ^ k :=
      mul_nonneg (mul_nonneg hX0 (Real.rpow_nonneg hN0.le _)) (pow_nonneg hMi0.le _)
    calc (Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * M⁻¹) * (X * N ^ τ1 * M⁻¹ ^ k)
        ≤ (9 * N ^ τ1 * η⁻¹) * (X * N ^ τ1 * M⁻¹ ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ hXk
          rw [hMi]; exact hnearf
      _ = 9 * N ^ τ1 * N ^ τ1 * (X * M⁻¹ ^ k * η⁻¹) := by ring
  -- the far part
  have hpowk : M⁻¹ ^ p ≤ M⁻¹ ^ k * N ^ k := by
    have h1 : M⁻¹ ^ p = M⁻¹ ^ k * M ^ (k - p) := by
      have : M⁻¹ ^ k = M⁻¹ ^ p * M⁻¹ ^ (k - p) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc, ← mul_pow, inv_mul_cancel₀ hMpos.ne', one_pow, mul_one]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hMi0.le _)
    calc M ^ (k - p) ≤ N ^ (k - p) := pow_le_pow_left₀ hMpos.le hMN _
      _ ≤ N ^ k := pow_le_pow_right₀ hN1 (by omega)
  have hfar : Wr ^ 2 * Lsq * (X * M⁻¹ ^ p * δK) ≤
      X * M⁻¹ ^ k * η⁻¹ * (N ^ (k + 1) * δK) := by
    rw [hWL]
    have hXk : 0 ≤ X * M⁻¹ ^ k * (N ^ (k + 1) * δK) :=
      mul_nonneg (mul_nonneg hX0 (pow_nonneg hMi0.le _))
        (mul_nonneg (pow_nonneg hN0.le _) hδK0)
    calc N * (X * M⁻¹ ^ p * δK) ≤ N * (X * (M⁻¹ ^ k * N ^ k) * δK) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowk hX0) hδK0) hN0.le
      _ = X * M⁻¹ ^ k * (N ^ (k + 1) * δK) := by ring
      _ ≤ X * M⁻¹ ^ k * η⁻¹ * (N ^ (k + 1) * δK) := by nlinarith
  -- combine
  have hcond : 2 * (k : ℝ) ^ 2 * (N ^ (k + 1) * δK) ≤ 1 := by
    calc 2 * (k : ℝ) ^ 2 * (N ^ (k + 1) * δK) ≤ N * (N ^ (k + 1) * δK) :=
          mul_le_mul_of_nonneg_right h9 (mul_nonneg (pow_nonneg hN0.le _) hδK0)
      _ = δK * N ^ (k + 2) := by ring
      _ ≤ 1 := hδK
  have hXn : 0 ≤ X * M⁻¹ ^ k * η⁻¹ :=
    mul_nonneg (mul_nonneg hX0 (pow_nonneg hMi0.le _)) (inv_nonneg.2 hη0.le)
  have hXZ : X * M⁻¹ ^ k * η⁻¹ ≤ S * M⁻¹ ^ k * η⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXS (pow_nonneg hMi0.le _))
      (inv_nonneg.2 hη0.le)
  have hδN : N ^ (τ1 + τ1) * N ^ (τ1 + τ1) = N ^ δ := by
    rw [← Real.rpow_add hN0]; congr 1; rw [hδ]; ring
  have hττ : N ^ τ1 * N ^ τ1 = N ^ (τ1 + τ1) := (Real.rpow_add hN0 _ _).symm
  have h1τ : 1 ≤ N ^ (τ1 + τ1) := Real.one_le_rpow hN1 (by linarith)
  calc Wr ^ 2 * ((k : ℝ) ^ 2 * (2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 *
          (X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1))) + Lsq * (X * M⁻¹ ^ p * δK))))
      = 2 * (k : ℝ) ^ 2 * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 *
          (X * M⁻¹ ^ p * (N ^ τ1 * M⁻¹ ^ (l - 1)))) + Wr ^ 2 * Lsq * (X * M⁻¹ ^ p * δK)) := by
        ring
    _ ≤ 2 * (k : ℝ) ^ 2 * (9 * N ^ τ1 * N ^ τ1 * (X * M⁻¹ ^ k * η⁻¹) +
        X * M⁻¹ ^ k * η⁻¹ * (N ^ (k + 1) * δK)) :=
        mul_le_mul_of_nonneg_left (add_le_add hnear hfar) (by positivity)
    _ = (18 * (k : ℝ) ^ 2 * (N ^ τ1 * N ^ τ1) + 2 * (k : ℝ) ^ 2 * (N ^ (k + 1) * δK)) *
        (X * M⁻¹ ^ k * η⁻¹) := by ring
    _ ≤ (18 * (k : ℝ) ^ 2 * (N ^ τ1 * N ^ τ1) + 1) * (X * M⁻¹ ^ k * η⁻¹) :=
        mul_le_mul_of_nonneg_right (add_le_add_right hcond _) hXn
    _ ≤ (N ^ (τ1 + τ1) * N ^ (τ1 + τ1)) * (S * M⁻¹ ^ k * η⁻¹) := by
        rw [hττ]
        have h5 : 18 * (k : ℝ) ^ 2 * N ^ (τ1 + τ1) + 1 ≤ N ^ (τ1 + τ1) * N ^ (τ1 + τ1) := by
          nlinarith
        calc (18 * (k : ℝ) ^ 2 * N ^ (τ1 + τ1) + 1) * (X * M⁻¹ ^ k * η⁻¹)
            ≤ (N ^ (τ1 + τ1) * N ^ (τ1 + τ1)) * (X * M⁻¹ ^ k * η⁻¹) :=
              mul_le_mul_of_nonneg_right h5 hXn
          _ ≤ (N ^ (τ1 + τ1) * N ^ (τ1 + τ1)) * (S * M⁻¹ ^ k * η⁻¹) :=
              mul_le_mul_of_nonneg_left hXZ (by positivity)
    _ = N ^ δ * (S * M⁻¹ ^ k * η⁻¹) := by rw [hδN]

/-- The generic near part: `W² (2R+1)² Y M^{-(j+1)} ≤ 9 N^{τ₁} Y M^{-j} η^{-1}` for `R = ℓ W^{τ₁}`,
`M = W² ℓ² η`. -/
private theorem bcalE_near_gen {Wr N ℓ η M τ1 Y : ℝ} {j : ℕ} (hW1 : 1 ≤ Wr) (hℓ : 1 ≤ ℓ)
    (hη0 : 0 < η) (hτ1 : 0 ≤ τ1) (hM : M = Wr ^ 2 * ℓ ^ 2 * η) (hWN : Wr ^ 2 ≤ N) (hY : 0 ≤ Y) :
    Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Y * M⁻¹ ^ (j + 1))) ≤
      9 * N ^ τ1 * (Y * M⁻¹ ^ j * η⁻¹) := by
  have hMi0 : 0 ≤ M⁻¹ := by
    rw [hM]
    have : 0 < Wr := by linarith
    positivity
  have hnearf := bcalE_near_factor (τ1 := τ1) hW1 hℓ hη0 hWN hτ1
  have e1 : Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Y * M⁻¹ ^ (j + 1))) =
      (Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * M⁻¹) * (Y * M⁻¹ ^ j) := by ring
  rw [e1]
  calc (Wr ^ 2 * (2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * M⁻¹) * (Y * M⁻¹ ^ j)
      ≤ (9 * N ^ τ1 * η⁻¹) * (Y * M⁻¹ ^ j) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hY (pow_nonneg hMi0 _))
        rw [hM]; exact hnearf
    _ = 9 * N ^ τ1 * (Y * M⁻¹ ^ j * η⁻¹) := by ring

/-- `C N^{τ₁} N^{τ₂} ≤ N^{τ}` when `C ≤ N^{τ₁}` and `2τ₁ + τ₂ ≤ τ`. -/
private theorem bcalE_absorb {N τ1 τ2 τs C : ℝ} (hN1 : 1 ≤ N) (hτ1 : 0 ≤ τ1) (hτ2 : 0 ≤ τ2)
    (hsum : τ1 + τ1 + τ2 ≤ τs) (hC : C ≤ N ^ τ1) : C * (N ^ τ1 * N ^ τ2) ≤ N ^ τs := by
  have hN0 : 0 < N := by linarith
  calc C * (N ^ τ1 * N ^ τ2) ≤ N ^ τ1 * (N ^ τ1 * N ^ τ2) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg (Real.rpow_nonneg hN0.le _)
          (Real.rpow_nonneg hN0.le _))
    _ = N ^ (τ1 + τ1 + τ2) := by rw [Real.rpow_add hN0, Real.rpow_add hN0]; ring
    _ ≤ N ^ τs := Real.rpow_le_rpow_of_exponent_le hN1 hsum

/-- The arithmetic of conjunct (ii). -/
private theorem bcalE_ii_arith {Wr N ℓ η M S δ B Lsq τ1 τs Wd : ℝ} {k : ℕ}
    (hW1 : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη0 : 0 < η) (hτ1 : 0 ≤ τ1) (hM : M = Wr ^ 2 * ℓ ^ 2 * η)
    (hWN : Wr ^ 2 ≤ N) (hS0 : 0 ≤ S) (hWd0 : 0 ≤ Wd)
    (hfar : Wr ^ 2 * ((k : ℝ) ^ 2 * (Lsq * (B * δ))) ≤ Wd)
    (hτ : 9 * (k : ℝ) ^ 2 * N ^ τ1 ≤ N ^ τs) (hτs : 1 ≤ N ^ τs) :
    Wr ^ 2 * ((k : ℝ) ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (S * M⁻¹ ^ (k + 2)) +
        Lsq * (B * δ))) ≤ N ^ τs * ((S * M⁻¹) * (M ^ k)⁻¹ * η⁻¹ + Wd) := by
  have hW0 : 0 < Wr := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMi0 : 0 < M⁻¹ := inv_pos.2 hMpos
  have hnear := bcalE_near_gen (N := N) (τ1 := τ1) (j := k) hW1 hℓ hη0 hτ1 hM hWN
    (mul_nonneg hS0 hMi0.le)
  have hZ : 0 ≤ (S * M⁻¹) * (M ^ k)⁻¹ * η⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hS0 hMi0.le) (inv_nonneg.2 (pow_nonneg hMpos.le _)))
      (inv_nonneg.2 hη0.le)
  have e1 : Wr ^ 2 * ((k : ℝ) ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (S * M⁻¹ ^ (k + 2)) +
      Lsq * (B * δ))) =
      (k : ℝ) ^ 2 * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (S * M⁻¹ * M⁻¹ ^ (k + 1)))) +
        Wr ^ 2 * ((k : ℝ) ^ 2 * (Lsq * (B * δ))) := by ring
  have e2 : S * M⁻¹ * M⁻¹ ^ (k + 1) = S * M⁻¹ ^ (k + 2) := by ring
  rw [e1]
  have hnear' : Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (S * M⁻¹ * M⁻¹ ^ (k + 1))) ≤
      9 * N ^ τ1 * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹) := hnear
  have hinv : (M ^ k)⁻¹ = M⁻¹ ^ k := (inv_pow M k).symm
  rw [hinv] at hZ ⊢
  calc (k : ℝ) ^ 2 * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (S * M⁻¹ * M⁻¹ ^ (k + 1)))) +
        Wr ^ 2 * ((k : ℝ) ^ 2 * (Lsq * (B * δ)))
      ≤ (k : ℝ) ^ 2 * (9 * N ^ τ1 * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹)) + Wd :=
        add_le_add (mul_le_mul_of_nonneg_left hnear' (sq_nonneg _)) hfar
    _ = (9 * (k : ℝ) ^ 2 * N ^ τ1) * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹) + Wd := by ring
    _ ≤ N ^ τs * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹) + 1 * Wd :=
        add_le_add (mul_le_mul_of_nonneg_right hτ hZ) (by rw [one_mul])
    _ ≤ N ^ τs * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹) + N ^ τs * Wd :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hτs hWd0)
    _ = N ^ τs * (S * M⁻¹ * M⁻¹ ^ k * η⁻¹ + Wd) := by ring

/-- The arithmetic of conjunct (iii): `A = N^{τ₂} M^{-1}` bounds `⟨(G-m)E_a⟩`. -/
private theorem bcalE_iii_arith {Wr N ℓ η M Xi δ Lsq τ1 τ2 τs Wd : ℝ} {k : ℕ}
    (hW1 : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη0 : 0 < η) (hτ1 : 0 ≤ τ1) (hM : M = Wr ^ 2 * ℓ ^ 2 * η)
    (hWN : Wr ^ 2 ≤ N) (hXi0 : 0 ≤ Xi) (hWd0 : 0 ≤ Wd)
    (hfar : Wr ^ 2 * ((k : ℝ) * (Lsq * ((N ^ τ2 * M⁻¹) * δ))) ≤ Wd)
    (hτ : 9 * (k : ℝ) * (N ^ τ1 * N ^ τ2) ≤ N ^ τs) (hτs : 1 ≤ N ^ τs) (hN0 : 0 < N) :
    Wr ^ 2 * ((k : ℝ) * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * ((N ^ τ2 * M⁻¹) * (Xi * M⁻¹ ^ k)) +
        Lsq * ((N ^ τ2 * M⁻¹) * δ))) ≤ N ^ τs * (Xi * (M ^ k)⁻¹ * η⁻¹ + Wd) := by
  have hW0 : 0 < Wr := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMi0 : 0 < M⁻¹ := inv_pos.2 hMpos
  have hnear := bcalE_near_gen (N := N) (τ1 := τ1) (j := k) hW1 hℓ hη0 hτ1 hM hWN
    (mul_nonneg (Real.rpow_nonneg hN0.le τ2) hXi0)
  have hZ : 0 ≤ Xi * (M ^ k)⁻¹ * η⁻¹ :=
    mul_nonneg (mul_nonneg hXi0 (inv_nonneg.2 (pow_nonneg hMpos.le _))) (inv_nonneg.2 hη0.le)
  have hinv : (M ^ k)⁻¹ = M⁻¹ ^ k := (inv_pow M k).symm
  rw [hinv] at hZ ⊢
  have e1 : Wr ^ 2 * ((k : ℝ) * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 *
        ((N ^ τ2 * M⁻¹) * (Xi * M⁻¹ ^ k)) + Lsq * ((N ^ τ2 * M⁻¹) * δ))) =
      (k : ℝ) * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (N ^ τ2 * Xi * M⁻¹ ^ (k + 1)))) +
        Wr ^ 2 * ((k : ℝ) * (Lsq * ((N ^ τ2 * M⁻¹) * δ))) := by ring
  rw [e1]
  calc (k : ℝ) * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (N ^ τ2 * Xi * M⁻¹ ^ (k + 1)))) +
        Wr ^ 2 * ((k : ℝ) * (Lsq * ((N ^ τ2 * M⁻¹) * δ)))
      ≤ (k : ℝ) * (9 * N ^ τ1 * (N ^ τ2 * Xi * M⁻¹ ^ k * η⁻¹)) + Wd :=
        add_le_add (mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg _)) hfar
    _ = (9 * (k : ℝ) * (N ^ τ1 * N ^ τ2)) * (Xi * M⁻¹ ^ k * η⁻¹) + Wd := by ring
    _ ≤ N ^ τs * (Xi * M⁻¹ ^ k * η⁻¹) + 1 * Wd :=
        add_le_add (mul_le_mul_of_nonneg_right hτ hZ) (by rw [one_mul])
    _ ≤ N ^ τs * (Xi * M⁻¹ ^ k * η⁻¹) + N ^ τs * Wd :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hτs hWd0)
    _ = N ^ τs * (Xi * M⁻¹ ^ k * η⁻¹ + Wd) := by ring

/-- The arithmetic of conjunct (iv). -/
private theorem bcalE_iv_arith {Wr N ℓ η M Xi δ Lsq τ1 τs Wd : ℝ} {k : ℕ}
    (hW1 : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη0 : 0 < η) (hτ1 : 0 ≤ τ1) (hM : M = Wr ^ 2 * ℓ ^ 2 * η)
    (hWN : Wr ^ 2 ≤ N) (hXi0 : 0 ≤ Xi) (hWd0 : 0 ≤ Wd)
    (hfar : Wr ^ 2 * ((k : ℝ) * (Lsq * δ)) ≤ Wd)
    (hτ : 9 * (k : ℝ) * N ^ τ1 ≤ N ^ τs) (hτs : 1 ≤ N ^ τs) :
    Wr ^ 2 * ((k : ℝ) * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Xi * M⁻¹ ^ (2 * k + 1)) + Lsq * δ)) ≤
      N ^ τs * (Xi * (M ^ (2 * k))⁻¹ * η⁻¹ + Wd) := by
  have hW0 : 0 < Wr := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMi0 : 0 < M⁻¹ := inv_pos.2 hMpos
  have hnear := bcalE_near_gen (N := N) (τ1 := τ1) (j := 2 * k) hW1 hℓ hη0 hτ1 hM hWN hXi0
  have hZ : 0 ≤ Xi * (M ^ (2 * k))⁻¹ * η⁻¹ :=
    mul_nonneg (mul_nonneg hXi0 (inv_nonneg.2 (pow_nonneg hMpos.le _))) (inv_nonneg.2 hη0.le)
  have hinv : (M ^ (2 * k))⁻¹ = M⁻¹ ^ (2 * k) := (inv_pow M (2 * k)).symm
  rw [hinv] at hZ ⊢
  have e1 : Wr ^ 2 * ((k : ℝ) * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Xi * M⁻¹ ^ (2 * k + 1)) +
        Lsq * δ)) =
      (k : ℝ) * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Xi * M⁻¹ ^ (2 * k + 1)))) +
        Wr ^ 2 * ((k : ℝ) * (Lsq * δ)) := by ring
  rw [e1]
  calc (k : ℝ) * (Wr ^ 2 * ((2 * (ℓ * Wr ^ τ1) + 1) ^ 2 * (Xi * M⁻¹ ^ (2 * k + 1)))) +
        Wr ^ 2 * ((k : ℝ) * (Lsq * δ))
      ≤ (k : ℝ) * (9 * N ^ τ1 * (Xi * M⁻¹ ^ (2 * k) * η⁻¹)) + Wd :=
        add_le_add (mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg _)) hfar
    _ = (9 * (k : ℝ) * N ^ τ1) * (Xi * M⁻¹ ^ (2 * k) * η⁻¹) + Wd := by ring
    _ ≤ N ^ τs * (Xi * M⁻¹ ^ (2 * k) * η⁻¹) + 1 * Wd :=
        add_le_add (mul_le_mul_of_nonneg_right hτ hZ) (by rw [one_mul])
    _ ≤ N ^ τs * (Xi * M⁻¹ ^ (2 * k) * η⁻¹) + N ^ τs * Wd :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hτs hWd0)
    _ = N ^ τs * (Xi * M⁻¹ ^ (2 * k) * η⁻¹ + Wd) := by ring

/-- **Conjunct (i)** of `BcalEPT'` (deterministic given `KboundConcl` and `KcalDecay`): the `𝒦`
piece has length `l ≥ 3`; near the labels of the loop it is bounded by `KboundConcl`, far from them
by `KcalDecay` (`D' = (k+2)/c`), and the `𝓛-𝒦` piece by `Ξ^{(𝓛-𝒦)}_{k+2-l} M^{-(k+2-l)}`. -/
private theorem bcalE_conj_i {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hKd : KcalDecay κ) {k : ℕ} (hk : 2 ≤ k) {l : ℕ} (hl3 : 3 ≤ l)
    (hlk : l ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖ksimLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) l
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => (∑ m ∈ Finset.Ico 1 k,
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) m) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  refine bcalE_pt_of_det fun δ hδ => ?_
  set τ1 : ℝ := δ / 4 with hτ1
  have hτ1pos : 0 < τ1 := by rw [hτ1]; positivity
  set Di : ℝ := ((k + 2 : ℕ) : ℝ) / c with hDi
  have hDipos : 0 < Di := by rw [hDi]; positivity
  have e6 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 k, ∀ u : TimeIcc s t n,
      ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ τ1 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    filter_upwards [hsize.eventually (hKb m hm1 τ1 hτ1pos)] with n hn u σ a
    have hu0 : 0 ≤ (u : ℝ) := le_trans (hs0 n) u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
      u, hu0, hu1⟩, σ, a⟩
    have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ1 * (KLoop.Mt (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := h
    rwa [kloop_Mt_eq hu1.le] at h'
  have e7 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 k,
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = d.size n →
        ((d.size n : ℕ) : ℝ) ^ c ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
        ∀ (σ : Fin m → Bool) (a : Fin m → Z2 L),
          ellT L u * (W : ℝ) ^ τ1 ≤ (KLoop.maxDist L a : ℝ) →
            ‖KLoop.Kcal L W E u (loopOf σ a)‖ ≤ (W : ℝ) ^ (-Di) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    exact hsize.eventually (hKd hκ c hc m hm1 τ1 Di hτ1pos hDipos)
  have e8 : ∀ᶠ n : ℕ in atTop, 18 * (k : ℝ) ^ 2 + 1 ≤ ((d.size n : ℕ) : ℝ) ^ (τ1 + τ1) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ1 + τ1)).comp hN).eventually_ge_atTop _
  have e9 : ∀ᶠ n : ℕ in atTop, 2 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) :=
    hN.eventually_ge_atTop _
  filter_upwards [hB, e6, e7, e8, e9] with n hBn h6 h7 h8 h9 p ω
  obtain ⟨u, σ, a⟩ := p
  dsimp only
  obtain ⟨hMpos, hMW, hℓ, hη0, hη1⟩ := bcalE_facts d hmain' n u
  obtain ⟨hE2, hu0, hu1⟩ := bcalE_time_facts d hmain' n u
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by
    have := bcalE_size_ge_W_sq d n
    have : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW1
    linarith
  have hWL : (d.W n : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
    rw [Sizes.size_eq]; push_cast; ring
  -- `W^{-D_i} N^{k+2} ≤ 1`
  have hδK : (d.W n : ℝ) ^ (-Di) * ((d.size n : ℕ) : ℝ) ^ (k + 2) ≤ 1 := by
    have := bcalE_WD (D' := 0) hN0.le hW0 hc (e := ((k + 2 : ℕ) : ℝ)) (Nat.cast_nonneg _) hBn
    rw [zero_add, ← hDi, Real.rpow_natCast, neg_zero, Real.rpow_zero] at this
    exact this
  -- the deterministic bound
  have hdet := bcalE_det_i (d.three_le_L n) (E n) u (Sizes.seqHflow d n u ω) hMpos hl3 hlk
    (R := ellT (d.L n) u * (d.W n : ℝ) ^ τ1) (δK := (d.W n : ℝ) ^ (-Di))
    (ε := ((d.size n : ℕ) : ℝ) ^ τ1) (by positivity) (Real.rpow_nonneg hW0.le _)
    (Real.rpow_nonneg hN0.le _)
    (fun J hJ h1 hJk => bcalE_bound_of' (KLoop.Kcal (d.L n) (d.W n) (E n) u)
      (B := fun m => ((d.size n : ℕ) : ℝ) ^ τ1 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1))
      (fun m hm σ a => h6 m hm u σ a) J hJ h1 hJk)
    (bcalE_loopDecay_of _ fun m hm σ a hfar => h7 m hm (d.L n) (d.W n) (d.three_le_L n)
      (Sizes.size_eq d n).symm hBn (E n) (hE n) u hu0 hu1 σ a hfar) σ a
  have hXS : xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k + 2 - l) ≤
      ∑ m ∈ Finset.Ico 1 k, xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m :=
    Finset.single_le_sum (f := fun m => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m)
      (fun m _ => bcalE_xiLK_nonneg _ _ _ hMpos _) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
  refine hdet.trans ?_
  refine (bcalE_i_arith (δ := δ) (M := scaleM (d.L n) (d.W n) (E n) u) (hM := rfl)
    (hW1 := hW1) (hℓ := hℓ) (hη0 := hη0) (hη1 := hη1)
    (hτ1 := hτ1pos) (hδ := by rw [hτ1]; ring) (hWN := bcalE_size_ge_W_sq d n)
    (hMN := hMW.trans (bcalE_size_ge_W_sq d n)) (hWL := hWL)
    (hX0 := bcalE_xiLK_nonneg _ _ _ hMpos _) (hXS := hXS)
    (hδK0 := Real.rpow_nonneg hW0.le _) (hpl := by omega) (hpk := by omega)
    (hδK := hδK) (h9 := h9) (h8 := h8)).trans (le_of_eq ?_)
  rw [inv_pow]

/-- The far part of (iii): `W² k L² (N^{τ₂} M^{-1}) (N W'') ≤ W^{-D}` from `W'' N^{K+3} ≤ W^{-D}`,
`k ≤ N`, `M^{-1} ≤ 1`, `τ₂ ≤ 1`. -/
private theorem bcalE_iii_far {Wr N Lsq Mi Wd'' Wd τ2 : ℝ} {k K : ℕ}
    (hWL : Wr ^ 2 * Lsq = N) (hN1 : 1 ≤ N) (hkN : (k : ℝ) ≤ N) (hτ2 : τ2 ≤ 1)
    (hMi0 : 0 ≤ Mi) (hMi1 : Mi ≤ 1) (hWd0 : 0 ≤ Wd'') (hK : 1 ≤ K)
    (hWD : Wd'' * N ^ (K + 3) ≤ Wd) :
    Wr ^ 2 * ((k : ℝ) * (Lsq * ((N ^ τ2 * Mi) * (N ^ (1 : ℝ) * Wd'')))) ≤ Wd := by
  have hN0 : 0 < N := by linarith
  have hNτ : N ^ τ2 ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 hτ2
    rwa [Real.rpow_one] at this
  have hNτ0 : 0 ≤ N ^ τ2 := Real.rpow_nonneg hN0.le _
  rw [Real.rpow_one]
  calc Wr ^ 2 * ((k : ℝ) * (Lsq * ((N ^ τ2 * Mi) * (N * Wd''))))
      = (k : ℝ) * (Wr ^ 2 * Lsq) * ((N ^ τ2 * Mi) * N) * Wd'' := by ring
    _ = (k : ℝ) * N * ((N ^ τ2 * Mi) * N) * Wd'' := by rw [hWL]
    _ ≤ N * N * ((N * 1) * N) * Wd'' := by
        refine mul_le_mul_of_nonneg_right ?_ hWd0
        refine mul_le_mul (mul_le_mul_of_nonneg_right hkN hN0.le) ?_ (by positivity)
          (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul hNτ hMi1 hMi0 hN0.le) hN0.le
    _ = Wd'' * N ^ 4 := by ring
    _ ≤ Wd'' * N ^ (K + 3) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (by omega)) hWd0
    _ ≤ Wd := hWD

/-- The far part of (iv): `W² k L² (N W'') ≤ W^{-D}` from `W'' N^{K+3} ≤ W^{-D}`, `k ≤ N`. -/
private theorem bcalE_iv_far {Wr N Lsq Wd'' Wd : ℝ} {k K : ℕ}
    (hWL : Wr ^ 2 * Lsq = N) (hN1 : 1 ≤ N) (hkN : (k : ℝ) ≤ N) (hWd0 : 0 ≤ Wd'') (hK : 1 ≤ K)
    (hWD : Wd'' * N ^ (K + 3) ≤ Wd) :
    Wr ^ 2 * ((k : ℝ) * (Lsq * (N ^ (1 : ℝ) * Wd''))) ≤ Wd := by
  have hN0 : 0 < N := by linarith
  rw [Real.rpow_one]
  calc Wr ^ 2 * ((k : ℝ) * (Lsq * (N * Wd'')))
      = (k : ℝ) * (Wr ^ 2 * Lsq) * N * Wd'' := by ring
    _ = (k : ℝ) * N * N * Wd'' := by rw [hWL]
    _ ≤ N * N * N * Wd'' :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hkN hN0.le) hN0.le) hWd0
    _ = Wd'' * N ^ 3 := by ring
    _ ≤ Wd'' * N ^ (K + 3) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (by omega)) hWd0
    _ ≤ Wd := hWD

/-- **Conjunct (iii)** of `BcalEPT'`: on the good event, `⟨(G-m)E_a⟩` is `≤ N^{τ₂} M^{-1}`
(`bcalE_one_loop`), and `Ξ^{(𝓛)}_{k+1}` bounds the loop factor on the window; the far part is
`≤ k N³ W^{-D''} ≤ W^{-D}`. -/
private theorem bcalE_conj_iii {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hDL : DecayLoopPT d E s t)
    (hav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹))
    {k : ℕ} (hk : 2 ≤ k) {D : ℝ} (hD : 0 < D) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖egtN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => xiL (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (k + 1) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹ + (d.W n : ℝ) ^ (-D)) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := bcalE_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  intro τs hτs Ds hDs
  set K : ℕ := 2 * k + 2 with hK
  set τ0 : ℝ := min τs 1 with hτ0
  have hτ0pos : 0 < τ0 := lt_min hτs one_pos
  set τ1 : ℝ := τ0 / 4 with hτ1
  have hτ1pos : 0 < τ1 := by rw [hτ1]; positivity
  have hτ1le : τ1 ≤ 1 := by
    have : τ0 ≤ 1 := min_le_right _ _
    rw [hτ1]; linarith
  set D'' : ℝ := D + ((K + 3 : ℕ) : ℝ) / c with hD''
  have hD''pos : 0 < D'' := by rw [hD'']; positivity
  have hcore := bcalE_core d hmain' hKb hDL hav K (by omega) (τ1 := τ1) (D'' := D'')
    (τd := 1) (Dp := Ds) (τ2 := τ1) hτ1pos hD''pos one_pos hDs hτ1pos
  have e1 : ∀ᶠ n : ℕ in atTop, 9 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ τ1 :=
    ((tendsto_rpow_atTop hτ1pos).comp hN).eventually_ge_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, 2 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) :=
    hN.eventually_ge_atTop _
  have e3 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ c₀ := by
    filter_upwards [((tendsto_rpow_atTop hc₀).comp hN).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  filter_upwards [hcore, hB, e1, e2, e3, hlow] with n hcn hBn h1 h2 h3 hlown p
  obtain ⟨hNK, hN2, hu⟩ := hcn
  obtain ⟨u, σ, a⟩ := p
  obtain ⟨S, hS, hgood⟩ := hu u
  refine le_trans (measure_mono ?_) hS
  intro ω hω
  by_contra hωS
  obtain ⟨hdLL, hdLK, hbLL, hbK, havg⟩ := hgood ω hωS
  simp only [Set.mem_ofPred_eq] at hω
  refine absurd hω (not_lt.2 ?_)
  obtain ⟨hMpos, hMW, hℓ, hη0, hη1⟩ := bcalE_facts d hmain' n u
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hWN := bcalE_size_ge_W_sq d n
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW1
    linarith
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hWL : (d.W n : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
    rw [Sizes.size_eq]; push_cast; ring
  have hWD : (d.W n : ℝ) ^ (-D'') * ((d.size n : ℕ) : ℝ) ^ (K + 3) ≤ (d.W n : ℝ) ^ (-D) := by
    have := bcalE_WD (D' := D) hN0.le hW0 hc (e := ((K + 3 : ℕ) : ℝ)) (Nat.cast_nonneg _) hBn
    rw [Real.rpow_natCast] at this
    exact this
  have hM1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) u := le_trans h3 (hlown u u.2.2)
  have hMi0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := inv_nonneg.2 hMpos.le
  have hkN : (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (k : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    linarith
  have hdet := bcalE_det_iii (d.three_le_L n) (E n) u (Sizes.seqHflow d n u ω) hMpos
    (n := k) (by omega) (R := ellT (d.L n) u * (d.W n : ℝ) ^ τ1)
    (δ := ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (d.W n : ℝ) ^ (-D''))
    (A := ((d.size n : ℕ) : ℝ) ^ τ1 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹) (by positivity)
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hW0.le _))
    (mul_nonneg (Real.rpow_nonneg hN0.le _) hMi0) havg
    (LoopDecay.mono _ hdLL (by omega) le_rfl le_rfl) σ a
  have hfar := bcalE_iii_far (Wr := (d.W n : ℝ)) (N := ((d.size n : ℕ) : ℝ))
    (Lsq := ((d.L n : ℕ) : ℝ) ^ 2) (Mi := (scaleM (d.L n) (d.W n) (E n) u)⁻¹)
    (Wd'' := (d.W n : ℝ) ^ (-D'')) (Wd := (d.W n : ℝ) ^ (-D)) (τ2 := τ1) (k := k) (K := K)
    hWL hN1 hkN hτ1le hMi0 (inv_le_one_of_one_le₀ hM1) (Real.rpow_nonneg hW0.le _)
    (by omega) hWD
  have hτ : 9 * (k : ℝ) * (((d.size n : ℕ) : ℝ) ^ τ1 * ((d.size n : ℕ) : ℝ) ^ τ1) ≤
      ((d.size n : ℕ) : ℝ) ^ τs := by
    have h9 : 9 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ1 := by
      have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith
      linarith
    exact bcalE_absorb hN1 hτ1pos.le hτ1pos.le
      (by have : τ0 ≤ τs := min_le_left _ _
          rw [hτ1] at *; linarith) h9
  exact hdet.trans (bcalE_iii_arith (M := scaleM (d.L n) (d.W n) (E n) u) (hM := rfl) hW1 hℓ hη0
    hτ1pos.le hWN (bcalE_xiL_nonneg _ _ _ hMpos _) (Real.rpow_nonneg hW0.le _) hfar hτ
    (Real.one_le_rpow hN1 hτs.le) hN0)

/-- **Conjunct (iv)** of `BcalEPT'`: on the good event, `Ξ^{(𝓛)}_{2k+2}` bounds the loop factor on
the window; the far part is `k N² W^{-D''} ≤ W^{-D}`. -/
private theorem bcalE_conj_iv {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hDL : DecayLoopPT d E s t)
    (hav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹))
    {k : ℕ} (hk : 2 ≤ k) {D : ℝ} (hD : 0 < D) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)) × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖eeN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2.1
          p.2.2.2‖)
      (fun n p ω => xiL (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (2 * k + 2) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ (2 * k))⁻¹ * (etaT (E n) p.1)⁻¹ +
          (d.W n : ℝ) ^ (-D)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  intro τs hτs Ds hDs
  set K : ℕ := 2 * k + 2 with hK
  set τ0 : ℝ := min τs 1 with hτ0
  have hτ0pos : 0 < τ0 := lt_min hτs one_pos
  set τ1 : ℝ := τ0 / 4 with hτ1
  have hτ1pos : 0 < τ1 := by rw [hτ1]; positivity
  set D'' : ℝ := D + ((K + 3 : ℕ) : ℝ) / c with hD''
  have hD''pos : 0 < D'' := by rw [hD'']; positivity
  have hcore := bcalE_core d hmain' hKb hDL hav K (by omega) (τ1 := τ1) (D'' := D'')
    (τd := 1) (Dp := Ds) (τ2 := 1) hτ1pos hD''pos one_pos hDs one_pos
  have e1 : ∀ᶠ n : ℕ in atTop, 9 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ τ1 :=
    ((tendsto_rpow_atTop hτ1pos).comp hN).eventually_ge_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, 2 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) :=
    hN.eventually_ge_atTop _
  filter_upwards [hcore, hB, e1, e2] with n hcn hBn h1 h2 p
  obtain ⟨hNK, hN2, hu⟩ := hcn
  obtain ⟨u, σ, a, a'⟩ := p
  obtain ⟨S, hS, hgood⟩ := hu u
  refine le_trans (measure_mono ?_) hS
  intro ω hω
  by_contra hωS
  obtain ⟨hdLL, hdLK, hbLL, hbK, havg⟩ := hgood ω hωS
  simp only [Set.mem_ofPred_eq] at hω
  refine absurd hω (not_lt.2 ?_)
  obtain ⟨hMpos, hMW, hℓ, hη0, hη1⟩ := bcalE_facts d hmain' n u
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hWN := bcalE_size_ge_W_sq d n
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW1
    linarith
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hWL : (d.W n : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
    rw [Sizes.size_eq]; push_cast; ring
  have hWD : (d.W n : ℝ) ^ (-D'') * ((d.size n : ℕ) : ℝ) ^ (K + 3) ≤ (d.W n : ℝ) ^ (-D) := by
    have := bcalE_WD (D' := D) hN0.le hW0 hc (e := ((K + 3 : ℕ) : ℝ)) (Nat.cast_nonneg _) hBn
    rw [Real.rpow_natCast] at this
    exact this
  have hkN : (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (k : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    linarith
  have hdet := bcalE_det_iv (d.three_le_L n) (E n) u (Sizes.seqHflow d n u ω) hMpos
    (n := k) (by omega) (R := ellT (d.L n) u * (d.W n : ℝ) ^ τ1)
    (δ := ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (d.W n : ℝ) ^ (-D'')) (by positivity)
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hW0.le _))
    (LoopDecay.mono _ hdLL (by omega) le_rfl le_rfl) σ a a'
  have hfar := bcalE_iv_far (Wr := (d.W n : ℝ)) (N := ((d.size n : ℕ) : ℝ))
    (Lsq := ((d.L n : ℕ) : ℝ) ^ 2) (Wd'' := (d.W n : ℝ) ^ (-D'')) (Wd := (d.W n : ℝ) ^ (-D))
    (k := k) (K := K) hWL hN1 hkN (Real.rpow_nonneg hW0.le _) (by omega) hWD
  have hτ : 9 * (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ τ1 ≤ ((d.size n : ℕ) : ℝ) ^ τs := by
    have h9 : 9 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ1 := by
      have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith
      linarith
    have := bcalE_absorb (τ2 := 0) (τs := τs) hN1 hτ1pos.le le_rfl
      (by have : τ0 ≤ τs := min_le_left _ _
          rw [hτ1] at *; linarith) h9
    rw [Real.rpow_zero, mul_one] at this
    exact this
  exact hdet.trans (bcalE_iv_arith (M := scaleM (d.L n) (d.W n) (E n) u) (hM := rfl) hW1 hℓ hη0
    hτ1pos.le hWN (bcalE_xiL_nonneg _ _ _ hMpos _) (Real.rpow_nonneg hW0.le _) hfar hτ
    (Real.one_le_rpow hN1 hτs.le))

/-- **Conjunct (ii)** of `BcalEPT'`: on the good event (`bcalE_core`, `K = 2k+2`), near part relative
(`Ξ^{(𝓛-𝒦)}_pΞ^{(𝓛-𝒦)}_q`), far part `≤ 2k² N^{K+2} W^{-D''} ≤ W^{-D}` with
`D'' = D + (K+3)/c`. -/
private theorem bcalE_conj_ii {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hDL : DecayLoopPT d E s t)
    (hav : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹))
    {k : ℕ} (hk : 2 ≤ k) {D : ℝ} (hD : 0 < D) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := IdxT d s t k)
      (fun n p ω => ‖elklkN (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => (∑ m ∈ Finset.Icc 2 k,
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) m *
          xiLK (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) (k - m + 2) *
          (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) *
        (scaleM (d.L n) (d.W n) (E n) p.1 ^ k)⁻¹ * (etaT (E n) p.1)⁻¹ + (d.W n : ℝ) ^ (-D)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := bcalE_hsize d hN
  intro τs hτs Ds hDs
  set K : ℕ := 2 * k + 2 with hK
  set τ0 : ℝ := min τs 1 with hτ0
  have hτ0pos : 0 < τ0 := lt_min hτs one_pos
  set τ1 : ℝ := τ0 / 4 with hτ1
  have hτ1pos : 0 < τ1 := by rw [hτ1]; positivity
  set D'' : ℝ := D + ((K + 3 : ℕ) : ℝ) / c with hD''
  have hD''pos : 0 < D'' := by rw [hD'']; positivity
  have hcore := bcalE_core d hmain' hKb hDL hav K (by omega) (τ1 := τ1) (D'' := D'')
    (τd := 1) (Dp := Ds) (τ2 := 1) hτ1pos hD''pos one_pos hDs one_pos
  have e1 : ∀ᶠ n : ℕ in atTop, 9 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ τ1 :=
    ((tendsto_rpow_atTop hτ1pos).comp hN).eventually_ge_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, 2 * (k : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) :=
    hN.eventually_ge_atTop _
  filter_upwards [hcore, hB, e1, e2] with n hcn hBn h1 h2 p
  obtain ⟨hNK, hN2, hu⟩ := hcn
  obtain ⟨u, σ, a⟩ := p
  obtain ⟨S, hS, hgood⟩ := hu u
  refine le_trans (measure_mono ?_) hS
  intro ω hω
  by_contra hωS
  obtain ⟨hdLL, hdLK, hbLL, hbK, havg⟩ := hgood ω hωS
  simp only [Set.mem_ofPred_eq] at hω
  refine absurd hω (not_lt.2 ?_)
  obtain ⟨hMpos, hMW, hℓ, hη0, hη1⟩ := bcalE_facts d hmain' n u
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hWN := bcalE_size_ge_W_sq d n
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW1
    linarith
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hWL : (d.W n : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
    rw [Sizes.size_eq]; push_cast; ring
  have hWD : (d.W n : ℝ) ^ (-D'') * ((d.size n : ℕ) : ℝ) ^ (K + 3) ≤ (d.W n : ℝ) ^ (-D) := by
    have := bcalE_WD (D' := D) hN0.le hW0 hc (e := ((K + 3 : ℕ) : ℝ)) (Nat.cast_nonneg _) hBn
    rw [Real.rpow_natCast] at this
    exact this
  have hLKb : ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
      ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) J‖ ≤
        2 * ((d.size n : ℕ) : ℝ) ^ K := fun J hJ h1' hJk => by
    unfold LKf
    have h3 := hbLL J hJ h1' (by omega)
    have h4 := hbK J hJ h1' (by omega)
    exact (norm_sub_le _ _).trans (by linarith)
  have hdet := bcalE_det_ii (d.three_le_L n) (E n) u (Sizes.seqHflow d n u ω) hMpos hk
    (R := ellT (d.L n) u * (d.W n : ℝ) ^ τ1)
    (δ := ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (d.W n : ℝ) ^ (-D''))
    (B := 2 * ((d.size n : ℕ) : ℝ) ^ K) (by positivity)
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hW0.le _)) (by positivity) hLKb
    (LoopDecay.mono _ hdLK (by omega) le_rfl le_rfl) σ a
  have hfar : (d.W n : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((d.L n : ℕ) : ℝ) ^ 2 *
      ((2 * ((d.size n : ℕ) : ℝ) ^ K) * (((d.size n : ℕ) : ℝ) ^ (1 : ℝ) *
        (d.W n : ℝ) ^ (-D''))))) ≤ (d.W n : ℝ) ^ (-D) := by
    rw [Real.rpow_one]
    have hWd0 : 0 ≤ (d.W n : ℝ) ^ (-D'') := Real.rpow_nonneg hW0.le _
    calc (d.W n : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((d.L n : ℕ) : ℝ) ^ 2 *
          ((2 * ((d.size n : ℕ) : ℝ) ^ K) * (((d.size n : ℕ) : ℝ) * (d.W n : ℝ) ^ (-D'')))))
        = (2 * (k : ℝ) ^ 2) * ((d.W n : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2) *
            (((d.size n : ℕ) : ℝ) ^ K * ((d.size n : ℕ) : ℝ)) * (d.W n : ℝ) ^ (-D'') := by ring
      _ = (2 * (k : ℝ) ^ 2) * ((d.size n : ℕ) : ℝ) *
            (((d.size n : ℕ) : ℝ) ^ K * ((d.size n : ℕ) : ℝ)) * (d.W n : ℝ) ^ (-D'') := by
          rw [hWL]
      _ ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) *
            (((d.size n : ℕ) : ℝ) ^ K * ((d.size n : ℕ) : ℝ)) * (d.W n : ℝ) ^ (-D'') :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2 hN0.le) (by positivity)) hWd0
      _ = (d.W n : ℝ) ^ (-D'') * ((d.size n : ℕ) : ℝ) ^ (K + 3) := by ring
      _ ≤ (d.W n : ℝ) ^ (-D) := hWD
  have hτ : 9 * (k : ℝ) ^ 2 * ((d.size n : ℕ) : ℝ) ^ τ1 ≤ ((d.size n : ℕ) : ℝ) ^ τs := by
    have := bcalE_absorb (τ2 := 0) (τs := τs) hN1 hτ1pos.le le_rfl
      (by have : τ0 ≤ τs := min_le_left _ _
          rw [hτ1] at *; linarith) h1
    rw [Real.rpow_zero, mul_one] at this
    exact this
  have hS0 : 0 ≤ ∑ m ∈ Finset.Icc 2 k,
      xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m *
        xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k - m + 2) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (bcalE_xiLK_nonneg _ _ _ hMpos _)
      (bcalE_xiLK_nonneg _ _ _ hMpos _)
  rw [← Finset.sum_mul]
  exact hdet.trans (bcalE_ii_arith (M := scaleM (d.L n) (d.W n) (E n) u) (hM := rfl) hW1 hℓ hη0
    hτ1pos.le hWN hS0 (Real.rpow_nonneg hW0.le _) hfar hτ
    (Real.one_le_rpow hN1 hτs.le))

/-- **`bcalEPT'`** (`lem_BcalE`, `CalEbwXi`, per time over `[s,t]`):
the statement `BcalEPT'`.  Conjunct (i) is `bcalE_conj_i` (deterministic from `KboundConcl`,
`KcalDecay`); (ii)–(iv) are `bcalE_conj_ii`, `bcalE_conj_iii`, `bcalE_conj_iv` (good event of
`DecayLoopPT`, and for (iii) the one-loop control `bcalE_one_loop` from `GbEXPHypV3`,
`Step2LocalPT`, `Step2DecayPT`, `CondStInd`); (v) is `bcalE_labelDecay`. -/
theorem bcalEPT' (κ c τ : ℝ) (E s t : ℕ → ℝ) : BcalEPT' d κ c τ E s t := by
  intro hmain hKb hKd hV3 hloc hdec hDL k hk
  have hav := bcalE_one_loop d hV3 hmain hKb hloc hdec
  exact ⟨fun l hl3 hlk => bcalE_conj_i d hmain hKb hKd hk hl3 hlk,
    fun D hD => bcalE_conj_ii d hmain hKb hDL hav hk hD,
    fun D hD => bcalE_conj_iii d hmain hKb hDL hav hk hD,
    fun D hD => bcalE_conj_iv d hmain hKb hDL hav hk hD,
    bcalE_labelDecay d κ c τ E s t hmain hKb hKd hV3 hloc hdec hDL k hk⟩

end Main

end RBM.Ind

end
