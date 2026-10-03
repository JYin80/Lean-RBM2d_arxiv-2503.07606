/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Defs
import RBM2D.Evolution.XiBounds
import RBM2D.Loop.LatticeCount

/-!
# The explicit deterministic forms of `lem:sum_decay`: the general bound and Case 1

Paper: arXiv:2503.07606, Section 7: `sum_res_1` and `nonalternating`.

Statements (namespace `RBM.Evol`): the `Prop`s `UgenGenExplicit`, `UgenCase1Explicit`.  Proved
here, for the explicit constants `cGen`, `cCase1`:
`ugenGenExplicit : UgenGenExplicit cGen`, `ugenCase1Explicit : UgenCase1Explicit cCase1`.

Argument (`d = 2`; the one-dimensional subset expansion of `∏ᵢ (δ + Ξᵢ)` is not used, see below).
Write `ψᵢ(c) = ‖(1 + Ξᵢ)_{aᵢ c}‖`.  Split `‖A_b‖ ≤ M · 1[maxDist b < ρ] + δ_A`
(`DecayWin`, `ρ = ℓ_s K`).
* Far part: `δ_A ∏ᵢ Σ_c ψᵢ(c) ≤ ((1-s)/(1-t))^k δ_A`, from the row bound `xiRowBound`.
* Near part, around the anchor `j`: `maxDist b < ρ` gives `|b_j - bᵢ|_L ≤ ρ` for every `i`, so by
  the anchored product sum (`sum_prod_anchor_le`, over `Fin k → Z2 L`) the near sum is at most
  `(Σ_c ψ_j(c)) ∏_{i ≠ j} sup_x Σ_{|x - c|_L ≤ ρ} ψᵢ(c)`.  With `‖δ + Ξ‖ ≤ δ + max|Ξ|`
  (`xiEntryBound`) and the ball count `KLoop.card_ball_le` (`(2ρ+1)² ≤ 9ρ²` for `ρ ≥ 1`) each
  window factor is `≤ 1 + 9 ρ² e ≤ (1 + 18 cProp5) (1 + log L) K² R`, `R = rhoR L s t`, because
  `ℓ_s² (t - s) / min(1, L²(1-t)) ≤ R`.  The anchor sum is `(1-s)/(1-t) =
  (ℓ_t/ℓ_s)² R` (general bound) or `≤ (1 + cShortRow κ)(1 + log
  L)` (Case 1, `xiRowBoundShort`, anchor at a repeated sign).
* The one-dimensional subset expansion of `∏ᵢ (δ + Ξᵢ)` carries `(1 + e N)^n` for the terms
  `S ≠ univ`; the exponents `λ^{k-1} K^{2(k-1)}` need `(1 + e N)^{k-1}`, which the direct
  pointwise bound `|δ + Ξ| ≤ δ + |Ξ|` gives.  It is therefore not used.
-/

noncomputable section

namespace RBM.Evol

open Finset RBM.Path RBM.Ind

/-- **The general bound (`sum_res_1`, explicit)**, every `σ`, `|E| ≤ 2`:
`|(𝒰_{s,t,σ}∘A)_a| ≤ c_k (1+log L)^{k-1} K^{2(k-1)} (ℓ_t/ℓ_s)² ρ^k M + ((1-s)/(1-t))^k δ_A`,
`ρ = rhoR L s t`.  The d = 1 factor `ℓ_t/ℓ_s` of the one-dimensional bound becomes
`(ℓ_t/ℓ_s)²`. -/
def UgenGenExplicit (c : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (K M δA : ℝ), 1 ≤ K → 0 ≤ M →
    0 ≤ δA → ∀ A : (Fin k → Z2 L) → ℂ, (∀ b, ‖A b‖ ≤ M) → DecayWin L (ellT L s * K) δA A →
    ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ s t A a‖ ≤
        c k * (1 + Real.log L) ^ (k - 1) * K ^ (2 * (k - 1)) * (ellT L t / ellT L s) ^ 2 *
            rhoR L s t ^ k * M +
          ((1 - s) / (1 - t)) ^ k * δA

/-- **Case 1 (`nonalternating`, explicit)**: a repeated sign `σ_i = σ_{i+1}` (cyclic),
`|E| ≤ 2 - κ`. -/
def UgenCase1Explicit (c : ℕ → ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ κ E : ℝ, 0 < κ →
    |E| ≤ 2 - κ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ σ : Fin k → Bool,
    (∃ i : Fin k, σ i = σ (i + 1)) → ∀ K M δA : ℝ, 1 ≤ K → 0 ≤ M → 0 ≤ δA →
    ∀ A : (Fin k → Z2 L) → ℂ, (∀ b, ‖A b‖ ≤ M) → DecayWin L (ellT L s * K) δA A →
    ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ s t A a‖ ≤
        c k κ * (1 + Real.log L) ^ k * K ^ (2 * (k - 1)) * rhoR L s t ^ k * M +
          ((1 - s) / (1 - t)) ^ k * δA

/-- The explicit constant of the general bound: `(1 + 18 cProp5)^(k-1)`. -/
def cGen (k : ℕ) : ℝ := (1 + 18 * cProp5) ^ (k - 1)

/-- The explicit constant of Case 1: `(1 + cShortRow κ) (1 + 18 cProp5)^(k-1)`. -/
def cCase1 (k : ℕ) (κ : ℝ) : ℝ := (1 + cShortRow κ) * (1 + 18 * cProp5) ^ (k - 1)

/-! ## Anchored product sums -/

section Anchor

variable {L : ℕ} [NeZero L]

/-- Product-sum interchange for `Z2 L`. -/
theorem KernelExpand_sum_prod_pi {R : Type*} [CommSemiring R] {n : ℕ} (g : Fin n → Z2 L → R) :
    ∑ b : Fin n → Z2 L, ∏ i, g i (b i) = ∏ i, ∑ j : Z2 L, g i j := by
  rw [← Finset.sum_prod_piFinset (Finset.univ : Finset (Z2 L)) g, Fintype.piFinset_univ]

/-- **Summing a product around an anchor** (with `ZMod L ↦ Z2 L`,
`LoopArg L n ↦ Fin n → Z2 L`, `n`-fold sum over `Fin n → Z2 L`). -/
private theorem sum_prod_anchor_le {n : ℕ} (g : Fin n → Z2 L → Z2 L → ℝ)
    (hg : ∀ i x c, 0 ≤ g i x c) (j : Fin n) {R : ℝ} (B : Fin n → ℝ)
    (hR : ∑ x : Z2 L, g j x x ≤ R) (hB : ∀ i, i ≠ j → ∀ x, ∑ c : Z2 L, g i x c ≤ B i) :
    ∑ b : Fin n → Z2 L, ∏ i, g i (b j) (b i) ≤ R * ∏ i ∈ univ.erase j, B i := by
  classical
  set h : Z2 L → Fin n → Z2 L → ℝ := fun x i c =>
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
  have hBnn : ∀ i ∈ univ.erase j, 0 ≤ B i := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    exact (Finset.sum_nonneg fun c _ => hg i 0 c).trans (hB i hij 0)
  have h2 : ∀ x : Z2 L, ∑ b : Fin n → Z2 L, ∏ i, h x i (b i)
      ≤ g j x x * ∏ i ∈ univ.erase j, B i := by
    intro x
    rw [KernelExpand_sum_prod_pi (h x), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hj : ∑ c : Z2 L, h x j c = g j x x := by
      simp only [hh, ite_true]
      rw [Finset.sum_ite_eq' Finset.univ x (g j x)]; simp
    rw [hj]
    refine mul_le_mul_of_nonneg_left ?_ (hg j x x)
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i hi => ?_)
    · exact Finset.sum_nonneg fun c _ => by
        simp only [hh]; split_ifs <;> first | exact hg _ _ _ | exact le_rfl
    · have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hh, hij, ite_false]
      exact hB i hij x
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  calc ∑ x : Z2 L, ∑ b : Fin n → Z2 L, ∏ i, h x i (b i)
      ≤ ∑ x : Z2 L, g j x x * ∏ i ∈ univ.erase j, B i := Finset.sum_le_sum fun x _ => h2 x
    _ = (∑ x : Z2 L, g j x x) * ∏ i ∈ univ.erase j, B i := by rw [Finset.sum_mul]
    _ ≤ R * ∏ i ∈ univ.erase j, B i :=
        mul_le_mul_of_nonneg_right hR (Finset.prod_nonneg hBnn)

end Anchor

/-! ## Scale and edge helpers -/

section Helpers

variable {L : ℕ} [NeZero L]

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2` (restated: `norm_mSig` in `Loop/Kcal.lean` is private). -/
private theorem norm_mSig_one {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ‖ = 1 := by
  cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

/-- `‖m(σ) m(σ')‖ = 1` for `|E| ≤ 2`. -/
private theorem norm_edge_one {E : ℝ} (hE : |E| ≤ 2) (σ σ' : Bool) :
    ‖KLoop.mSig E σ * KLoop.mSig E σ'‖ = 1 := by
  rw [norm_mul, norm_mSig_one hE, norm_mSig_one hE, one_mul]

omit [NeZero L] in
/-- `ℓ_u² = min(1/(1-u), L²)` for `u < 1` (restated: `ellT_sq` in `Path/Scales.lean` is
private). -/
private theorem ellT_sq' {u : ℝ} (hu : u < 1) :
    ellT L u ^ 2 = min (1 / (1 - u)) ((L : ℝ) ^ 2) := by
  have hx : 0 < 1 - u := by linarith
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have ha : (1 / Real.sqrt (1 - u)) ^ 2 = 1 / (1 - u) := by
    rw [div_pow, one_pow, Real.sq_sqrt hx.le]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  unfold ellT
  rcases le_total (1 / Real.sqrt (1 - u)) (L : ℝ) with h | h
  · rw [min_eq_left h, ha, min_eq_left]
    rw [← ha]; exact pow_le_pow_left₀ (by positivity) h 2
  · rw [min_eq_right h, min_eq_right]
    rw [← ha]; exact pow_le_pow_left₀ hL0 h 2

omit [NeZero L] in
/-- `ℓ_u² (1 - u) = min(1, L²(1 - u))` for `u < 1`. -/
theorem KernelExpand_ellT_sq_mul {u : ℝ} (hu : u < 1) :
    ellT L u ^ 2 * (1 - u) = min 1 ((L : ℝ) ^ 2 * (1 - u)) := by
  have hx : 0 < 1 - u := by linarith
  rw [ellT_sq' hu, min_mul_of_nonneg _ _ hx.le, one_div_mul_cancel hx.ne']

omit [NeZero L] in
theorem KernelExpand_min_one_pos' (hL : 3 ≤ L) {t : ℝ} (ht : t < 1) :
    0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  exact lt_min one_pos (mul_pos (pow_pos hL' 2) (by linarith))

omit [NeZero L] in
/-- `rhoR L s t = min(1, L²(1-s)) / min(1, L²(1-t))`. -/
theorem KernelExpand_rhoR_eq {s t : ℝ} (hs : s < 1) (ht : t < 1) :
    rhoR L s t = min 1 ((L : ℝ) ^ 2 * (1 - s)) / min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
  unfold rhoR
  rw [KernelExpand_ellT_sq_mul hs, KernelExpand_ellT_sq_mul ht]

omit [NeZero L] in
/-- `1 ≤ R_{s,t}` for `0 ≤ s ≤ t < 1`. -/
theorem KernelExpand_one_le_rhoR (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    1 ≤ rhoR L s t := by
  have hs : s < 1 := lt_of_le_of_lt hst ht
  rw [KernelExpand_rhoR_eq hs ht]
  rw [le_div_iff₀ (KernelExpand_min_one_pos' hL ht), one_mul]
  refine min_le_min le_rfl ?_
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hL2

omit [NeZero L] in
/-- `(1-s)/(1-t) = (ℓ_t/ℓ_s)² R_{s,t}`. -/
private theorem one_sub_div_eq (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (1 - s) / (1 - t) = (ellT L t / ellT L s) ^ 2 * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓs : 0 < ellT L s := lt_of_lt_of_le one_pos (one_le_ellT (by omega) hs0 hs1)
  have hℓt : 0 < ellT L t := lt_of_lt_of_le one_pos (one_le_ellT (by omega) (hs0.trans hst) ht)
  have h1t : 0 < 1 - t := by linarith
  unfold rhoR
  field_simp

end Helpers

/-! ## Edge sums: `ψ = ‖1 + Ξ‖` -/

section Edges

variable {L : ℕ} [NeZero L]

theorem KernelExpand_ukerMat_apply (ξ : ℂ) (v w : ℝ) (a c : Z2 L) :
    ukerMat L ξ v w a c = xiMat L ξ v w a c + (1 : Matrix (Z2 L) (Z2 L) ℂ) a c := by
  simp [xiMat]

private theorem norm_ukerMat_le (ξ : ℂ) (v w : ℝ) (a c : Z2 L) :
    ‖ukerMat L ξ v w a c‖ ≤
      ‖xiMat L ξ v w a c‖ + ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ := by
  rw [KernelExpand_ukerMat_apply]; exact norm_add_le _ _

theorem KernelExpand_sum_norm_one_row (a : Z2 L) :
    ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ = 1 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Row sum of `ψ` from a row sum of `Ξ`. -/
private theorem sum_norm_ukerMat_le {ξ : ℂ} {v w r : ℝ} (a : Z2 L)
    (h : ∑ c : Z2 L, ‖xiMat L ξ v w a c‖ ≤ r) :
    ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖ ≤ r + 1 := by
  calc ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖
      ≤ ∑ c : Z2 L, (‖xiMat L ξ v w a c‖ + ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖) :=
        Finset.sum_le_sum fun c _ => norm_ukerMat_le ξ v w a c
    _ = ∑ c : Z2 L, ‖xiMat L ξ v w a c‖ + ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ :=
        Finset.sum_add_distrib
    _ ≤ r + 1 := by rw [KernelExpand_sum_norm_one_row]; linarith

/-- The full row `Σ_c ψ(c) ≤ (1-s)/(1-t)` (`xiRowBound`). -/
private theorem row_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a : Z2 L) :
    ∑ c : Z2 L, ‖ukerMat L ξ s t a c‖ ≤ (1 - s) / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have h := sum_norm_ukerMat_le a (xiRowBound L hL ξ hξ s t hs hst ht a)
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- The window sum `Σ_{|x - c|_L ≤ ρ} ψ(c) ≤ 1 + (2ρ+1)² e` (`xiEntryBound`, and
`KLoop.card_ball_le`), `e = 2 cProp5 (1 + log L)(t - s)/min(1, L²(1-t))`. -/
private theorem ball_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a x : Z2 L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
        ‖ukerMat L ξ s t a c‖ ≤
      1 + (2 * ρ + 1) ^ 2 *
        (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by
  classical
  set e : ℝ := 2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) with he
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have he0 : 0 ≤ e := by
    rw [he]
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hlog) (by linarith)) hm.le
  have hent : ∀ c : Z2 L, ‖xiMat L ξ s t a c‖ ≤ e := by
    intro c
    have h := xiEntryBound L hL ξ hξ s t hs hst ht a c
    have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
    have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by simp) (by linarith)
    calc ‖xiMat L ξ s t a c‖
        ≤ e * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) := h
      _ ≤ e * 1 := mul_le_mul_of_nonneg_left hexp he0
      _ = e := mul_one e
  have hcard := RBM.KLoop.card_ball_le L x ρ hρ
  calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
        ‖ukerMat L ξ s t a c‖
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
          (‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ + e) :=
        Finset.sum_le_sum fun c _ => by
          have h1 := norm_ukerMat_le ξ s t a c
          have h2 := hent c
          linarith
    _ = ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
          ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ +
        ((Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ)).card : ℝ) * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 + (2 * ρ + 1) ^ 2 * e := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hcard he0)
        calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
              ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖
            ≤ ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun c _ _ => norm_nonneg _)
          _ = 1 := KernelExpand_sum_norm_one_row a

omit [NeZero L] in
/-- The window factor is at most `(1 + 18 cProp5)(1 + log L) K² R`, `ρ = ℓ_s K`. -/
private theorem window_const (hL : 3 ≤ L) {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (hK : 1 ≤ K) :
    1 + (2 * (ellT L s * K) + 1) ^ 2 *
        (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) ≤
      (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hlog1 : 1 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  set ℓ : ℝ := ellT L s with hℓdef
  set R : ℝ := rhoR L s t with hRdef
  set m : ℝ := min 1 ((L : ℝ) ^ 2 * (1 - t)) with hmdef
  set lam : ℝ := 1 + Real.log L with hlam
  have hρ1 : 1 ≤ ℓ * K := by nlinarith
  -- `ℓ_s² (t - s) / m ≤ R`
  have hq : ℓ ^ 2 * (t - s) / m ≤ R := by
    rw [hRdef, KernelExpand_rhoR_eq hs1 ht, ← KernelExpand_ellT_sq_mul hs1,
      div_le_div_iff_of_pos_right hm]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have h9 : (2 * (ℓ * K) + 1) ^ 2 ≤ 9 * (ℓ * K) ^ 2 := by nlinarith
  have he0 : 0 ≤ 2 * cProp5 * lam * (t - s) / m :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hlog) (by linarith)) hm.le
  have hρe : (ℓ * K) ^ 2 * (2 * cProp5 * lam * (t - s) / m) =
      2 * cProp5 * lam * K ^ 2 * (ℓ ^ 2 * (t - s) / m) := by ring
  have hpos : 0 ≤ 2 * cProp5 * lam * K ^ 2 := by positivity
  have h1 : 1 ≤ lam * K ^ 2 * R := by
    have : 1 ≤ K ^ 2 := by nlinarith
    have h2 : 1 ≤ lam * K ^ 2 := by nlinarith
    nlinarith
  calc 1 + (2 * (ℓ * K) + 1) ^ 2 * (2 * cProp5 * lam * (t - s) / m)
      ≤ 1 + 9 * (ℓ * K) ^ 2 * (2 * cProp5 * lam * (t - s) / m) := by
        have := mul_le_mul_of_nonneg_right h9 he0
        linarith
    _ = 1 + 9 * (2 * cProp5 * lam * K ^ 2 * (ℓ ^ 2 * (t - s) / m)) := by
        rw [mul_assoc 9, hρe]
    _ ≤ 1 + 9 * (2 * cProp5 * lam * K ^ 2 * R) := by
        have := mul_le_mul_of_nonneg_left hq hpos
        linarith
    _ ≤ (1 + 18 * cProp5) * lam * K ^ 2 * R := by nlinarith

end Edges

section Core

variable {L : ℕ} [NeZero L]

/-- **The abstract bound.**  `ψᵢ ≥ 0` with row sums `≤ r`, anchor row sum `≤ Rj`, window sums
`Σ_{|x - c|_L ≤ ρ} ψᵢ(c) ≤ B` (`i ≠ j`); `‖A‖ ≤ M`, decay `(ρ, δ_A)`:
`Σ_b (∏ᵢ ψᵢ(bᵢ)) ‖A_b‖ ≤ M Rj B^{k-1} + δ_A r^k`. -/
theorem KernelExpand_core_bound {k : ℕ} (ψ : Fin k → Z2 L → ℝ) (hψ : ∀ i c, 0 ≤ ψ i c)
    {A : (Fin k → Z2 L) → ℂ} {ρ M δA r Rj B : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δA)
    (hAM : ∀ b, ‖A b‖ ≤ M) (hdec : DecayWin L ρ δA A) (j : Fin k)
    (hr : ∀ i, ∑ c : Z2 L, ψ i c ≤ r) (hj : ∑ c : Z2 L, ψ j c ≤ Rj)
    (hB : ∀ i, i ≠ j → ∀ x : Z2 L,
      ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ), ψ i c ≤ B) :
    ∑ b : Fin k → Z2 L, (∏ i, ψ i (b i)) * ‖A b‖ ≤ M * (Rj * B ^ (k - 1)) + δA * r ^ k := by
  classical
  -- the anchored window factor
  set g : Fin k → Z2 L → Z2 L → ℝ := fun i x c =>
    if i = j then ψ i c else if (zdist2 L (x - c) : ℝ) ≤ ρ then ψ i c else 0 with hg
  have hg0 : ∀ i x c, 0 ≤ g i x c := by
    intro i x c
    simp only [hg]
    split_ifs <;> first | exact hψ _ _ | exact le_rfl
  have hprod0 : ∀ b : Fin k → Z2 L, 0 ≤ ∏ i, ψ i (b i) :=
    fun b => Finset.prod_nonneg fun i _ => hψ i (b i)
  have hgprod0 : ∀ b : Fin k → Z2 L, 0 ≤ ∏ i, g i (b j) (b i) :=
    fun b => Finset.prod_nonneg fun i _ => hg0 i (b j) (b i)
  -- pointwise
  have hpt : ∀ b : Fin k → Z2 L, (∏ i, ψ i (b i)) * ‖A b‖ ≤
      M * (∏ i, g i (b j) (b i)) + δA * ∏ i, ψ i (b i) := by
    intro b
    by_cases hnear : ρ ≤ (KLoop.maxDist L b : ℝ)
    · have h1 : ‖A b‖ ≤ δA := hdec b hnear
      calc (∏ i, ψ i (b i)) * ‖A b‖ ≤ (∏ i, ψ i (b i)) * δA :=
            mul_le_mul_of_nonneg_left h1 (hprod0 b)
        _ = δA * ∏ i, ψ i (b i) := mul_comm _ _
        _ ≤ M * (∏ i, g i (b j) (b i)) + δA * ∏ i, ψ i (b i) := by
            have := mul_nonneg hM (hgprod0 b)
            linarith
    · push Not at hnear
      have hd : ∀ i, (zdist2 L (b j - b i) : ℝ) ≤ ρ := by
        intro i
        have h := Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (b p.1 - b p.2))
          (Finset.mem_univ (j, i))
        have h' : (zdist2 L (b j - b i) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by
          exact_mod_cast h
        linarith
      have hgeq : ∏ i, g i (b j) (b i) = ∏ i, ψ i (b i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [hg]
        split_ifs with h1 h2
        · rfl
        · rfl
        · exact absurd (hd i) h2
      rw [hgeq]
      calc (∏ i, ψ i (b i)) * ‖A b‖ ≤ (∏ i, ψ i (b i)) * M :=
            mul_le_mul_of_nonneg_left (hAM b) (hprod0 b)
        _ = M * ∏ i, ψ i (b i) := mul_comm _ _
        _ ≤ M * (∏ i, ψ i (b i)) + δA * ∏ i, ψ i (b i) := by
            have := mul_nonneg hδ (hprod0 b)
            linarith
  -- the near sum
  have hnear : ∑ b : Fin k → Z2 L, ∏ i, g i (b j) (b i) ≤ Rj * B ^ (k - 1) := by
    have h := sum_prod_anchor_le g hg0 j (fun _ => B)
      (R := Rj) (by
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) hj
        simp [hg])
      (by
        intro i hij x
        have : ∑ c : Z2 L, g i x c =
            ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ), ψ i c := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp [hg, hij]
        rw [this]; exact hB i hij x)
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)] at h
    simpa using h
  -- the far sum
  have hfar : ∑ b : Fin k → Z2 L, ∏ i, ψ i (b i) ≤ r ^ k := by
    rw [KernelExpand_sum_prod_pi ψ]
    calc ∏ i, ∑ c : Z2 L, ψ i c ≤ ∏ _i : Fin k, r :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => hψ i c)
            (fun i _ => hr i)
      _ = r ^ k := by simp
  calc ∑ b : Fin k → Z2 L, (∏ i, ψ i (b i)) * ‖A b‖
      ≤ ∑ b : Fin k → Z2 L, (M * (∏ i, g i (b j) (b i)) + δA * ∏ i, ψ i (b i)) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = M * ∑ b : Fin k → Z2 L, ∏ i, g i (b j) (b i) + δA * ∑ b : Fin k → Z2 L, ∏ i, ψ i (b i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ M * (Rj * B ^ (k - 1)) + δA * r ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left hnear hM) (mul_le_mul_of_nonneg_left hfar hδ)

/-- `‖𝒰 ∘ A‖ ≤ Σ_b (∏ᵢ ‖ψᵢ‖) ‖A_b‖`. -/
private theorem norm_Ugen_le {k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool) (s t : ℝ)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ‖Ugen L E σ s t A a‖ ≤ ∑ b : Fin k → Z2 L,
      (∏ i, ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) s t (a i) (b i)‖) *
        ‖A b‖ := by
  unfold Ugen
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_prod]

end Core

section Theorems

/-- **The general bound**: `sum_res_1`, explicit form,
`cGen k = (1 + 18 cProp5)^(k-1)`. -/
theorem ugenGenExplicit : UgenGenExplicit cGen := by
  intro k _ hk L _ hL E hE s t hs hst ht σ K M δA hK hM hδ A hAM hdec a
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hlam : 1 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * K := by nlinarith
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hrat := one_sub_div_eq hL hs hst ht
  have hedge : ∀ i : Fin k,
      ‖KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))‖ ≤ 1 := fun i =>
    (norm_edge_one hE _ _).le
  set Bc : ℝ := (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t with hBc
  have hcore := KernelExpand_core_bound (L := L)
    (fun i c => ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) s t (a i) c‖)
    (fun i c => norm_nonneg _) (A := A) (ρ := ellT L s * K) (M := M) (δA := δA)
    (r := (1 - s) / (1 - t)) (Rj := (1 - s) / (1 - t)) (B := Bc) hM hδ hAM hdec 0
    (fun i => row_le hL (hedge i) hs hst ht (a i)) (row_le hL (hedge 0) hs hst ht (a 0))
    (fun i _ x => (ball_le hL (hedge i) hs hst ht (a i) x hρ0).trans
      (window_const hL hs hst ht hK))
  have hk1 : rhoR L s t ^ k = rhoR L s t * rhoR L s t ^ (k - 1) := by
    rw [← pow_succ']; congr 1; have := NeZero.pos k; omega
  have hfirst : M * ((1 - s) / (1 - t) * Bc ^ (k - 1)) =
      cGen k * (1 + Real.log L) ^ (k - 1) * K ^ (2 * (k - 1)) * (ellT L t / ellT L s) ^ 2 *
        rhoR L s t ^ k * M := by
    rw [hrat, hk1, hBc]
    unfold cGen
    rw [pow_mul]
    simp only [mul_pow]
    ring
  calc ‖Ugen L E σ s t A a‖ ≤ _ := norm_Ugen_le E σ s t A a
    _ ≤ M * ((1 - s) / (1 - t) * Bc ^ (k - 1)) + δA * ((1 - s) / (1 - t)) ^ k := hcore
    _ = _ := by rw [hfirst]; ring

/-- **Case 1**: `nonalternating`, explicit form,
`cCase1 k κ = (1 + cShortRow κ)(1 + 18 cProp5)^(k-1)`. -/
theorem ugenCase1Explicit : UgenCase1Explicit cCase1 := by
  intro k _ hk L _ hL κ E hκ hE s t hs hst ht σ hσ K M δA hK hM hδ A hAM hdec a
  obtain ⟨i₀, hi₀⟩ := hσ
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hE2 : |E| ≤ 2 := by linarith
  have hlam : 1 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * K := by nlinarith
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hedge : ∀ i : Fin k,
      ‖KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))‖ ≤ 1 := fun i =>
    (norm_edge_one hE2 _ _).le
  -- the anchor row (`xiRowBoundShort`)
  have hcs : 0 ≤ cShortRow κ := by
    have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    unfold cShortRow
    refine mul_nonneg (div_nonneg ?_ hg) (sq_nonneg _)
    unfold cProp5; norm_num
  have hanchor : ∑ c : Z2 L, ‖ukerMat L
      (KLoop.mSig E (σ i₀) * KLoop.mSig E (σ (i₀ + 1))) s t (a i₀) c‖ ≤
      (1 + cShortRow κ) * (1 + Real.log L) := by
    have h0 := xiRowBoundShort L hL κ E hκ hE (σ i₀) s t hs hst ht (a i₀)
    rw [← hi₀]
    have h1 := sum_norm_ukerMat_le (a i₀) h0
    nlinarith
  set Bc : ℝ := (1 + 18 * cProp5) * (1 + Real.log L) * K ^ 2 * rhoR L s t with hBc
  have hcore := KernelExpand_core_bound (L := L)
    (fun i c => ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) s t (a i) c‖)
    (fun i c => norm_nonneg _) (A := A) (ρ := ellT L s * K) (M := M) (δA := δA)
    (r := (1 - s) / (1 - t)) (Rj := (1 + cShortRow κ) * (1 + Real.log L)) (B := Bc) hM hδ hAM
    hdec i₀ (fun i => row_le hL (hedge i) hs hst ht (a i)) hanchor
    (fun i _ x => (ball_le hL (hedge i) hs hst ht (a i) x hρ0).trans
      (window_const hL hs hst ht hK))
  have hk1 : rhoR L s t ^ k = rhoR L s t * rhoR L s t ^ (k - 1) := by
    rw [← pow_succ']; congr 1; have := NeZero.pos k; omega
  have hk2 : (1 + Real.log L) ^ k = (1 + Real.log L) * (1 + Real.log L) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; have := NeZero.pos k; omega
  have hX : 0 ≤ (1 + cShortRow κ) * (1 + 18 * cProp5) ^ (k - 1) * (1 + Real.log L) ^ k *
      K ^ (2 * (k - 1)) * M := by
    have : 0 ≤ cProp5 := by unfold cProp5; norm_num
    have : 0 ≤ 1 + Real.log L := by linarith
    positivity
  have hfirst : M * ((1 + cShortRow κ) * (1 + Real.log L) * Bc ^ (k - 1)) ≤
      cCase1 k κ * (1 + Real.log L) ^ k * K ^ (2 * (k - 1)) * rhoR L s t ^ k * M := by
    have heq : M * ((1 + cShortRow κ) * (1 + Real.log L) * Bc ^ (k - 1)) =
        ((1 + cShortRow κ) * (1 + 18 * cProp5) ^ (k - 1) * (1 + Real.log L) ^ k *
          K ^ (2 * (k - 1)) * M) * rhoR L s t ^ (k - 1) := by
      rw [hk2, hBc]
      rw [pow_mul]
      simp only [mul_pow]
      ring
    have heq2 : cCase1 k κ * (1 + Real.log L) ^ k * K ^ (2 * (k - 1)) * rhoR L s t ^ k * M =
        ((1 + cShortRow κ) * (1 + 18 * cProp5) ^ (k - 1) * (1 + Real.log L) ^ k *
          K ^ (2 * (k - 1)) * M) * rhoR L s t ^ k := by
      unfold cCase1; ring
    rw [heq, heq2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.sub_le k 1)) hX
  calc ‖Ugen L E σ s t A a‖ ≤ _ := norm_Ugen_le E σ s t A a
    _ ≤ M * ((1 + cShortRow κ) * (1 + Real.log L) * Bc ^ (k - 1)) +
        δA * ((1 - s) / (1 - t)) ^ k := hcore
    _ ≤ _ := by
        have : δA * ((1 - s) / (1 - t)) ^ k = ((1 - s) / (1 - t)) ^ k * δA := mul_comm _ _
        rw [this]
        linarith

end Theorems

end RBM.Evol

end
