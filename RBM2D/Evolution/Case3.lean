/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.CltDecorrelation
import RBM2D.Green.FlucAvg

/-!
# Case 3 of `lem:sum_decay`: `BridgeCase3` and `SumDecayCase3Prec`

Paper: arXiv:2503.07606, Section 7: `sum_res_3`, its proof, `clt-lemma`.  The file uses the
declarations `KernelExpand_core_bound`, `cltEval_det_le` and
`RBM.Green.measurable_green_apply`.

Statements (namespace `RBM.Evol`, all other declarations are `private`):
`bridgeCase3 : BridgeCase3 d`, `sumDecayCase3Prec d κ 𝔠 δ (cCase3 𝔠 4)`.

Argument.  Fix the section of labels `a n` (`perTimeDomAt_iff_forall_section`; the union over
labels is outside the probability) and write `𝒜 = (F n).eval`, `Ā = 𝔼𝒜`.
* Non-alternating `σ`: Case 1 (`UgenCase1Explicit`) applied `ω`-wise on the decay event, with
  `‖Ā_b‖ ≤ N^ε Λ + crude·N^{-D'}` (the crude bound `‖𝒜‖ ≤ (K+1) N^{C'}(2N³/c_κ)^K`).
* Alternating `σ` (`ξ_i = |m|² = 1`, `ukerMat = 1 + Ξ`): `∏ (Ξ_i + δ_i)` is expanded over subsets
  (`c3_ugen_alt`, `def_psixi`); the terms with a `δ` are bounded by `KernelExpand_core_bound`
  (`iukwjn-d=2`).  The pure-`Ξ` term is telescoped exactly,
  `∏ Ξ_{a_i b_i} - ∏ Ξ_{a_i b_1} = Σ_i (Ξ_{a_i b_i} - Ξ_{a_i b_1}) ∏_{j<i} Ξ_{a_j b_j}
  ∏_{j>i} Ξ_{a_j b_1}` (`Finset.prod_add_ordered`), and the
  anchored product is killed by `SumZero (𝒜 - 𝔼𝒜)` (no truncation defect: the truncation to
  `|b_i - b_1| < ℓ_s W^τ` is applied to each telescoped term afterwards).  Each near part is
  `Σ_{b_1} Ξ_{a_1 b_1} Ỹ_i(b_1)` with `Ỹ_i` a `LocalForm` (`c3FY`, `Local` at `2τ`), split into the
  Case 2 sum with `Z = ϖ Ξ_{a_1 b}(|a_i - b|+1)^{-1}` and the Case 1 sum with
  `Z̃ = ϖ w₂ Ξ_{a b} 1[|a - b| < ℓ_t W^τ]` plus the exponentially small cut-off of
  `Ξ_{a_1 ·}` (`XiEntryBound`); the sizes are the `Z` and `Z̃` exponent bounds
  (`c3_Q1`, `c3_Q2`), `S_Y` (`c3_SY_le`), `q ≤ R` (`c3q_le`, cf. `window_const` of
  `KernelExpand.lean`).
* The polynomial factors of `N` are tracked with `PolyB` (bounded by a fixed power of `N`); the
  constants `C'_Y`, `D_c`, `D_p` are chosen from the resulting exponents.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## Part 1: deterministic kernel facts at a fixed lattice -/

section Det

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem c3_zdist_neg (L : ℕ) [NeZero L] (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem c3_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, c3_zdist_neg]

private theorem c3_zdist2_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← neg_sub y x, c3_zdist2_neg]

/-- The entry bound `e = 2 cProp5 (1 + log L)(t - s)/min(1, L²(1 - t))` of `Ξ` (`Xi-bound-0`). -/
private def c3e (L : ℕ) (s t : ℝ) : ℝ :=
  2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))

private theorem c3_lam_one (L : ℕ) : 1 ≤ 1 + Real.log L := by
  linarith [Real.log_natCast_nonneg L]

private theorem c3e_nonneg (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 0 ≤ c3e L s t := by
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  unfold c3e
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hlog) (by linarith)) hm.le

private theorem c3_entry_le (hXe : XiEntryBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a c : Z2 L) : ‖xiMat L 1 s t a c‖ ≤ c3e L s t := by
  have h := hXe L hL 1 (by simp) s t hs hst ht a c
  have he0 := c3e_nonneg hL hst ht
  have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by simp) (by linarith)
  calc ‖xiMat L 1 s t a c‖ ≤ c3e L s t * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) := h
    _ ≤ c3e L s t * 1 := mul_le_mul_of_nonneg_left hexp he0
    _ = c3e L s t := mul_one _


private theorem c3_row_le' (hXr : XiRowBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a : Z2 L) : ∑ c : Z2 L, ‖xiMat L 1 s t a c‖ ≤ (t - s) / (1 - t) :=
  hXr L hL 1 (by simp) s t hs hst ht a

private theorem c3_card_Z2 (L : ℕ) [NeZero L] : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

/-- The fibre-product sum: `Σ_{b : b 0 = x} ∏ᵢ hᵢ(bᵢ) = h₀(x) ∏_{i ≠ 0} Σ_c hᵢ(c)`. -/
private theorem c3_fiber_prod (h : Fin k → Z2 L → ℝ) (x : Z2 L) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x), ∏ i, h i (b i) =
      h 0 x * ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ c : Z2 L, h i c := by
  classical
  set g : Fin k → Z2 L → ℝ := fun i c => if i = 0 then (if c = x then h i c else 0) else h i c
    with hg
  have h1 : ∀ b : Fin k → Z2 L, (if b 0 = x then ∏ i, h i (b i) else 0) = ∏ i, g i (b i) := by
    intro b
    by_cases hb : b 0 = x
    · simp only [hb, ↓reduceIte]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simp [hg, hb]
      · simp [hg, hi]
    · simp only [hb, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin k))
      simp [hg, hb]
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun b _ => h1 b]
  rw [KernelExpand_sum_prod_pi g]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ c, g i c) (Finset.mem_univ 0)]
  congr 1
  · simp [hg]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ 0 := Finset.ne_of_mem_erase hi
    simp [hg, this]


/-! ### The telescoped terms -/

/-- `b` is within `ρ` of its first label in every coordinate. -/
private def c3Near (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (ρ : ℝ) (b : Fin k → Z2 L) : Prop :=
  ∀ i, (zdist2 L (b i - b 0) : ℝ) < ρ

open scoped Classical in
/-- The indicator of `c3Near`. -/
private def c3Ind (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (ρ : ℝ) (b : Fin k → Z2 L) : ℂ :=
  if c3Near L ρ b then 1 else 0

/-- The difference kernel `Ξ_{a_i b_i} - Ξ_{a_i b_0}` of the `i`-th telescoped term. -/
private def c3G (s t : ℝ) (a : Fin k → Z2 L) (i : Fin k) (b : Fin k → Z2 L) : ℂ :=
  xiMat L 1 s t (a i) (b i) - xiMat L 1 s t (a i) (b 0)

/-- The other kernels of the `i`-th telescoped term (`Finset.prod_add_ordered` on `j ≠ 0`):
`∏_{0<j<i} Ξ_{a_j b_j} ∏_{j>i} Ξ_{a_j b_0}`. -/
private def c3Q (s t : ℝ) (a : Fin k → Z2 L) (i : Fin k) (b : Fin k → Z2 L) : ℂ :=
  (∏ j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => j < i), xiMat L 1 s t (a j) (b j)) *
    ∏ j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => i < j), xiMat L 1 s t (a j) (b 0)

private def c3C (s t : ℝ) (a : Fin k → Z2 L) (i : Fin k) (b : Fin k → Z2 L) : ℂ :=
  c3G s t a i b * c3Q s t a i b

/-- The weight `(|a_i - x|_L + 1)^{-1} + (√(1-t) ℓ_t²)^{-1}` of `Xi-bound-1`. -/
private def c3w (s t : ℝ) (a : Fin k → Z2 L) (i : Fin k) (x : Z2 L) : ℝ :=
  ((zdist2 L (a i - x) : ℝ) + 1)⁻¹ + (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹

/-- The bound `S_Y` of the fibre sums of `c3C`. -/
private def c3SY (L : ℕ) (k : ℕ) (s t ρ : ℝ) : ℝ :=
  2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * c3e L s t ^ (k - 2) *
    ((2 * ρ + 1) ^ 2) ^ (k - 1)

private theorem c3_card_split (i : Fin k) (hi : i ≠ 0) :
    ((Finset.univ.erase (0 : Fin k)).filter (fun j => j < i)).card +
      ((Finset.univ.erase (0 : Fin k)).filter (fun j => i < j)).card = k - 2 := by
  classical
  set s : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hs
  have hi' : i ∈ s := by simp [hs, hi]
  have h1 : s.filter (fun j => j < i) ∪ s.filter (fun j => i < j) = s.erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hj, hlt⟩ | ⟨hj, hlt⟩)
      · exact ⟨hlt.ne, hj⟩
      · exact ⟨hlt.ne', hj⟩
    · rintro ⟨hne, hj⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
  have h2 : Disjoint (s.filter (fun j => j < i)) (s.filter (fun j => i < j)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_filter] at hj1 hj2
    exact lt_asymm hj1.2 hj2.2
  rw [← Finset.card_union_of_disjoint h2, h1, Finset.card_erase_of_mem hi']
  simp only [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

private theorem c3_Q_norm_le (hXe : XiEntryBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0)
    (b : Fin k → Z2 L) : ‖c3Q s t a i b‖ ≤ c3e L s t ^ (k - 2) := by
  unfold c3Q
  rw [norm_mul, norm_prod, norm_prod]
  have he := c3_entry_le hXe hL hs hst ht
  have he0 := c3e_nonneg hL hst ht
  calc (∏ j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => j < i),
        ‖xiMat L 1 s t (a j) (b j)‖) *
      ∏ j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => i < j),
        ‖xiMat L 1 s t (a j) (b 0)‖
      ≤ (∏ _j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => j < i), c3e L s t) *
        ∏ _j ∈ (Finset.univ.erase (0 : Fin k)).filter (fun j => i < j), c3e L s t :=
        mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => he _ _))
          (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => he _ _))
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => he0)
    _ = c3e L s t ^ (k - 2) := by
        rw [Finset.prod_const, Finset.prod_const, ← pow_add, c3_card_split i hi]

private theorem c3_P_nonneg (L : ℕ) : 0 ≤ derivativePrefactor (10 ^ 14) L := by
  have := c3_lam_one L
  unfold derivativePrefactor
  linarith

private theorem c3_G_norm_le (hXd : XiFirstDiff) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (b : Fin k → Z2 L) {ρ : ℝ}
    (hb : (zdist2 L (b i - b 0) : ℝ) < ρ) :
    ‖c3G s t a i b‖ ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * c3w s t a i (b 0) := by
  have h := hXd L hL s t hs hst ht (a i) (b 0) (b i - b 0)
  rw [add_sub_cancel] at h
  have h1 : ‖c3G s t a i b‖ = ‖xiMat L 1 s t (a i) (b 0) - xiMat L 1 s t (a i) (b i)‖ := by
    unfold c3G; rw [norm_sub_rev]
  rw [h1]
  refine h.trans ?_
  have hP := c3_P_nonneg L
  have hts : 0 ≤ t - s := by linarith
  have hD : (0 : ℝ) < (zdist2 L (a i - b 0) : ℝ) + 1 := by positivity
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  have hς : 0 < Real.sqrt (1 - t) * ellT L t ^ 2 := by
    have : 0 < 1 - t := by linarith
    positivity
  have hr0 : (0 : ℝ) ≤ zdist2 L (b i - b 0) := Nat.cast_nonneg _
  unfold c3w
  have hA : (zdist2 L (b i - b 0) : ℝ) / ((zdist2 L (a i - b 0) : ℝ) + 1) ≤
      ρ * ((zdist2 L (a i - b 0) : ℝ) + 1)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hb.le (inv_nonneg.2 hD.le)
  have hB : (zdist2 L (b i - b 0) : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2) ≤
      ρ * (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hb.le (inv_nonneg.2 hς.le)
  have h2 : 0 ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) := by positivity
  calc 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        ((zdist2 L (b i - b 0) : ℝ) / ((zdist2 L (a i - b 0) : ℝ) + 1) +
          (zdist2 L (b i - b 0) : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2))
      ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        (ρ * ((zdist2 L (a i - b 0) : ℝ) + 1)⁻¹ + ρ * (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) h2
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ *
        (((zdist2 L (a i - b 0) : ℝ) + 1)⁻¹ + (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹) := by ring

open scoped Classical in
/-- The number of `b` with `b 0 = x` and all `b i` within `ρ` of `x` is at most
`((2ρ+1)²)^{k-1}`. -/
private theorem c3_near_count {ρ : ℝ} (hρ : 0 ≤ ρ) (x : Z2 L) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
      (if c3Near L ρ b then (1 : ℝ) else 0) ≤ ((2 * ρ + 1) ^ 2) ^ (k - 1) := by
  classical
  have h1 : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
      (if c3Near L ρ b then (1 : ℝ) else 0) =
        ∏ i, (if (zdist2 L (b i - x) : ℝ) < ρ then (1 : ℝ) else 0) := by
    intro b hb
    have hb0 : b 0 = x := (Finset.mem_filter.1 hb).2
    rw [Finset.prod_boole]
    simp only [c3Near, hb0, Finset.mem_univ, true_implies]
  rw [Finset.sum_congr rfl h1, c3_fiber_prod
    (fun _ c => if (zdist2 L (c - x) : ℝ) < ρ then (1 : ℝ) else 0) x]
  have h0 : (if (zdist2 L (x - x) : ℝ) < ρ then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hcard : ∀ i : Fin k, ∑ c : Z2 L, (if (zdist2 L (c - x) : ℝ) < ρ then (1 : ℝ) else 0) ≤
      (2 * ρ + 1) ^ 2 := by
    intro i
    rw [Finset.sum_boole]
    refine le_trans ?_ (RBM.KLoop.card_ball_le L x ρ hρ)
    have : ((Finset.univ.filter fun c : Z2 L => (zdist2 L (c - x) : ℝ) < ρ).card : ℝ) ≤
        ((Finset.univ.filter fun u : Z2 L => (zdist2 L (x - u) : ℝ) ≤ ρ).card : ℝ) := by
      refine Nat.cast_le.2 (Finset.card_le_card ?_)
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [c3_zdist2_comm]; exact hc.le
    exact this
  have hprod : ∏ i ∈ Finset.univ.erase (0 : Fin k),
      ∑ c : Z2 L, (if (zdist2 L (c - x) : ℝ) < ρ then (1 : ℝ) else 0) ≤
      ((2 * ρ + 1) ^ 2) ^ (k - 1) := by
    calc ∏ i ∈ Finset.univ.erase (0 : Fin k),
          ∑ c : Z2 L, (if (zdist2 L (c - x) : ℝ) < ρ then (1 : ℝ) else 0)
        ≤ ∏ _i ∈ Finset.univ.erase (0 : Fin k), (2 * ρ + 1) ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num)
            (fun i _ => hcard i)
      _ = ((2 * ρ + 1) ^ 2) ^ (k - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  calc (if (zdist2 L (x - x) : ℝ) < ρ then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.univ.erase (0 : Fin k),
          ∑ c : Z2 L, (if (zdist2 L (c - x) : ℝ) < ρ then (1 : ℝ) else 0)
      ≤ 1 * ((2 * ρ + 1) ^ 2) ^ (k - 1) :=
        mul_le_mul h0 hprod (Finset.prod_nonneg fun i _ =>
          Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num) zero_le_one
    _ = ((2 * ρ + 1) ^ 2) ^ (k - 1) := one_mul _


open scoped Classical in
/-- **Fibre bound** (`Xi-bound-1`, and the ball count `eq-1sum`): for `i ≠ 0`,
`Σ_{b : b 0 = x} |1[near b] c_i(b)| ≤ S_Y · w_i(x)`. -/
private theorem c3_fiber_bound (hXe : XiEntryBound) (hXd : XiFirstDiff) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (x : Z2 L) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
        ‖c3Ind L ρ b * c3C s t a i b‖ ≤ c3SY L k s t ρ * c3w s t a i x := by
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  have hw : 0 ≤ c3w s t a i x := by
    have : 0 < 1 - t := by linarith
    unfold c3w; positivity
  have hP := c3_P_nonneg L
  have he0 := c3e_nonneg hL hst ht
  have hts : 0 ≤ t - s := by linarith
  set Gb : ℝ := 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * c3w s t a i x with hGb
  have hGb0 : 0 ≤ Gb := by positivity
  have hpt : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
      ‖c3Ind L ρ b * c3C s t a i b‖ ≤
        Gb * c3e L s t ^ (k - 2) * (if c3Near L ρ b then (1 : ℝ) else 0) := by
    intro b hb
    have hb0 : b 0 = x := (Finset.mem_filter.1 hb).2
    by_cases hn : c3Near L ρ b
    · have hind : c3Ind L ρ b = 1 := by simp [c3Ind, hn]
      simp only [hind, one_mul, hn, ↓reduceIte, mul_one]
      unfold c3C
      rw [norm_mul]
      have h1 := c3_G_norm_le hXd hL hs hst ht a i b (hn i)
      rw [hb0] at h1
      have h2 := c3_Q_norm_le hXe hL hs hst ht a i hi b
      exact mul_le_mul h1 h2 (norm_nonneg _) hGb0
    · have hind : c3Ind L ρ b = 0 := by simp [c3Ind, hn]
      simp only [hind, zero_mul, norm_zero, hn, ↓reduceIte, mul_zero, le_refl]
  calc ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
        ‖c3Ind L ρ b * c3C s t a i b‖
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
          Gb * c3e L s t ^ (k - 2) * (if c3Near L ρ b then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = Gb * c3e L s t ^ (k - 2) * ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
          (if c3Near L ρ b then (1 : ℝ) else 0) := by rw [Finset.mul_sum]
    _ ≤ Gb * c3e L s t ^ (k - 2) * ((2 * ρ + 1) ^ 2) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left (c3_near_count hρ x) (by positivity)
    _ = c3SY L k s t ρ * c3w s t a i x := by unfold c3SY; rw [hGb]; ring

/-- The total mass of `|Ξ_{a_0 b_0}| |c_i(b)|` (used for the far part). -/
private theorem c3_far_sum (hXe : XiEntryBound) (hXr : XiRowBound) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0) :
    ∑ b : Fin k → Z2 L, ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖ ≤
      ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k := by
  classical
  have he0 := c3e_nonneg hL hst ht
  have he := c3_entry_le hXe hL hs hst ht
  have h1t : 0 < 1 - t := by linarith
  have hrX0 : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) h1t.le
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  set e : ℝ := c3e L s t with hedef
  set r' : ℝ := (t - s) / (1 - t) + (L : ℝ) ^ 2 * e with hr'
  set h : Fin k → Z2 L → ℝ := fun j c =>
    if j = 0 then ‖xiMat L 1 s t (a 0) c‖ else
      if j = i then ‖xiMat L 1 s t (a i) c‖ + e else e with hh
  have hcardZ : ∀ c0 : ℝ, ∑ _c : Z2 L, c0 = (L : ℝ) ^ 2 * c0 := by
    intro c0
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c3_card_Z2]
  have hi' : i ∈ Finset.univ.erase (0 : Fin k) := by simp [hi]
  have hpt : ∀ b : Fin k → Z2 L,
      ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖ ≤ ∏ j, h j (b j) := by
    intro b
    have hprod : ∏ j, h j (b j) = ‖xiMat L 1 s t (a 0) (b 0)‖ *
        ((‖xiMat L 1 s t (a i) (b i)‖ + e) * e ^ (k - 2)) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => h j (b j)) (Finset.mem_univ 0)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase (0 : Fin k)) (fun j => h j (b j)) hi']
      have hcp : ∏ j ∈ (Finset.univ.erase (0 : Fin k)).erase i, h j (b j) = e ^ (k - 2) := by
        rw [Finset.prod_congr rfl (g := fun _ => e)]
        · rw [Finset.prod_const, Finset.card_erase_of_mem hi',
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          congr 1
        · intro j hj
          have hj1 : j ≠ i := Finset.ne_of_mem_erase hj
          have hj0 : j ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
          simp [hh, hj0, hj1]
      rw [hcp]
      simp [hh, hi]
    rw [hprod]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold c3C
    rw [norm_mul]
    have hG : ‖c3G s t a i b‖ ≤ ‖xiMat L 1 s t (a i) (b i)‖ + e := by
      unfold c3G
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (he _ _))
    exact mul_le_mul hG (c3_Q_norm_le hXe hL hs hst ht a i hi b) (norm_nonneg _)
      (add_nonneg (norm_nonneg _) he0)
  have hsum : ∀ j : Fin k, ∑ c : Z2 L, h j c ≤ r' := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      have h0 : ∀ c, h 0 c = ‖xiMat L 1 s t (a 0) c‖ := fun c => by simp [hh]
      rw [Finset.sum_congr rfl fun c _ => h0 c]
      have := c3_row_le' hXr hL hs hst ht (a 0)
      linarith [mul_nonneg hL2 he0]
    · by_cases hji : j = i
      · subst hji
        have h0 : ∀ c, h j c = ‖xiMat L 1 s t (a j) c‖ + e := fun c => by simp [hh, hj0]
        rw [Finset.sum_congr rfl fun c _ => h0 c, Finset.sum_add_distrib, hcardZ e]
        have := c3_row_le' hXr hL hs hst ht (a j)
        linarith
      · have h0 : ∀ c, h j c = e := fun c => by simp [hh, hj0, hji]
        rw [Finset.sum_congr rfl fun c _ => h0 c, hcardZ e]
        linarith
  calc ∑ b : Fin k → Z2 L, ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖
      ≤ ∑ b : Fin k → Z2 L, ∏ j, h j (b j) := Finset.sum_le_sum fun b _ => hpt b
    _ = ∏ j, ∑ c : Z2 L, h j c := KernelExpand_sum_prod_pi h
    _ ≤ ∏ _j : Fin k, r' :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun c _ => by
          simp only [hh]; split_ifs <;> first | exact norm_nonneg _ | positivity) (fun j _ => hsum j)
    _ = r' ^ k := by simp


/-! ### The alternating case: expansion into the pure-`Ξ` term and the terms with a `δ` -/

private theorem c3_mul_conj_one {m : ℂ} (h : ‖m‖ = 1) : m * (starRingEnd ℂ) m = 1 := by
  rw [Complex.mul_conj', h]; norm_num

private theorem c3_mSig_alt {E : ℝ} (hE : |E| ≤ 2) {σ σ' : Bool} (h : σ ≠ σ') :
    KLoop.mSig E σ * KLoop.mSig E σ' = 1 := by
  have hn : ‖Gauss.spectralM E‖ = 1 := Gauss.norm_spectralM hE
  unfold KLoop.mSig
  cases σ <;> cases σ'
  · exact absurd rfl h
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [mul_comm]; exact c3_mul_conj_one hn
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    exact c3_mul_conj_one hn
  · exact absurd rfl h

private theorem c3_prod_split {ι M : Type*} [CommMonoid M] [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f g : ι → M) :
    ∏ i, (if i ∈ S then f i else g i) = (∏ i ∈ S, f i) * ∏ i ∈ Finset.univ \ S, g i := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext i; simp
  · congr 1; ext i; simp

/-- **Expansion** (`def_psixi`): for alternating `σ` every edge weight is `ξ = |m|² = 1`,
`ukerMat L 1 s t = 1 + Ξ`, and `∏ᵢ (Ξ_i + δ_i)` is expanded over subsets. -/
private theorem c3_ugen_alt {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool)
    (hσ : ∀ i, σ i ≠ σ (i + 1)) (s t : ℝ) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Ugen L E σ s t A a = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ∑ b : Fin k → Z2 L, ((∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
        ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) * A b := by
  classical
  unfold Ugen
  have h1 : ∀ b : Fin k → Z2 L,
      (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) s t (a i) (b i)) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
          ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i) := by
    intro b
    rw [← Finset.prod_add]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [c3_mSig_alt hE (hσ i), KernelExpand_ukerMat_apply]
  simp_rw [h1, Finset.sum_mul]
  exact Finset.sum_comm

/-- `‖X_{a c}‖` summed over a ball is at most `(2ρ+1)² e`. -/
private theorem c3_ball_X (hXe : XiEntryBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a x : Z2 L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
      ‖xiMat L 1 s t a c‖ ≤ (2 * ρ + 1) ^ 2 * c3e L s t := by
  have hcard := RBM.KLoop.card_ball_le L x ρ hρ
  have he0 := c3e_nonneg hL hst ht
  calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
        ‖xiMat L 1 s t a c‖
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ), c3e L s t :=
        Finset.sum_le_sum fun c _ => c3_entry_le hXe hL hs hst ht a c
    _ = ((Finset.univ.filter fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ).card : ℝ) *
          c3e L s t := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * ρ + 1) ^ 2 * c3e L s t := mul_le_mul_of_nonneg_right hcard he0

/-- The terms of the expansion with at least one `δ` (`iukwjn-d=2`). -/
private theorem c3_subset_bound (hXe : XiEntryBound) (hXr : XiRowBound) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) {ρ M δA : ℝ} (hρ : 0 ≤ ρ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hdec : DecayWin L ρ δA A) (S : Finset (Fin k)) (hS : S ≠ Finset.univ) :
    ‖∑ b : Fin k → Z2 L, ((∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
        ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) * A b‖ ≤
      M * (1 * (1 + (2 * ρ + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
        δA * ((1 - s) / (1 - t)) ^ k := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hS (Finset.eq_univ_of_forall hcon)
  have h1t : 0 < 1 - t := by linarith
  have he0 := c3e_nonneg hL hst ht
  have hr1 : 1 ≤ (1 - s) / (1 - t) := by
    rw [le_div_iff₀ h1t]; linarith
  have hrX : (t - s) / (1 - t) ≤ (1 - s) / (1 - t) := by
    apply div_le_div_of_nonneg_right _ h1t.le; linarith
  set ψ : Fin k → Z2 L → ℝ := fun i c =>
    if i ∈ S then ‖xiMat L 1 s t (a i) c‖ else ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) c‖ with hψ
  have hψ0 : ∀ i c, 0 ≤ ψ i c := by
    intro i c; simp only [hψ]; split_ifs <;> exact norm_nonneg _
  have hr : ∀ i, ∑ c : Z2 L, ψ i c ≤ (1 - s) / (1 - t) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hψ, hi, ite_true]
      exact (c3_row_le' hXr hL hs hst ht (a i)).trans hrX
    · simp only [hψ, hi, ite_false]
      rw [KernelExpand_sum_norm_one_row]; exact hr1
  have hj : ∑ c : Z2 L, ψ j₀ c ≤ 1 := by
    simp only [hψ, hj₀, ite_false]
    rw [KernelExpand_sum_norm_one_row]
  have hB : ∀ i, i ≠ j₀ → ∀ x : Z2 L,
      ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ), ψ i c ≤
        1 + (2 * ρ + 1) ^ 2 * c3e L s t := by
    intro i _ x
    by_cases hi : i ∈ S
    · simp only [hψ, hi, ite_true]
      have := c3_ball_X hXe hL hs hst ht (a i) x hρ
      linarith
    · simp only [hψ, hi, ite_false]
      calc ∑ c ∈ Finset.univ.filter (fun c : Z2 L => (zdist2 L (x - c) : ℝ) ≤ ρ),
            ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) c‖
          ≤ ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) c‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun c _ _ => norm_nonneg _)
        _ = 1 := KernelExpand_sum_norm_one_row (a i)
        _ ≤ 1 + (2 * ρ + 1) ^ 2 * c3e L s t := by
            have : 0 ≤ (2 * ρ + 1) ^ 2 * c3e L s t := by positivity
            linarith
  have hcore := KernelExpand_core_bound (L := L) ψ hψ0 (A := A) (ρ := ρ) (M := M) (δA := δA)
    (r := (1 - s) / (1 - t)) (Rj := 1) (B := 1 + (2 * ρ + 1) ^ 2 * c3e L s t) hM hδ hAM hdec
    j₀ hr hj hB
  refine le_trans ?_ hcore
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  have hprod : (∏ i ∈ S, ‖xiMat L 1 s t (a i) (b i)‖) *
      ∏ i ∈ Finset.univ \ S, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)‖ = ∏ i, ψ i (b i) := by
    rw [← c3_prod_split S (fun i => ‖xiMat L 1 s t (a i) (b i)‖)
      (fun i => ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)‖)]
  rw [hprod]


/-! ### The pure-`Ξ` term: sum-zero, telescoping, near and far -/

/-- **Telescoping** (`Xi-expansion`, `Xi-bound-2` and proof of `lem:sum_decay`, with
`Finset.prod_add_ordered`): the
sum-zero property kills the anchored product, leaving `Σ_{i ≠ 0} T_i`. -/
private theorem c3_main_term {A : (Fin k → Z2 L) → ℂ} (hA : SumZero L A) (s t : ℝ)
    (a : Fin k → Z2 L) :
    ∑ b : Fin k → Z2 L, (∏ i, xiMat L 1 s t (a i) (b i)) * A b =
      ∑ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Fin k → Z2 L,
        xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * A b := by
  classical
  set s' : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hs'
  have hpt : ∀ b : Fin k → Z2 L, (∏ i, xiMat L 1 s t (a i) (b i)) * A b =
      (xiMat L 1 s t (a 0) (b 0) * ∏ j ∈ s', xiMat L 1 s t (a j) (b 0)) * A b +
        ∑ i ∈ s', xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * A b := by
    intro b
    have h1 := Finset.prod_add_ordered s' (fun j => xiMat L 1 s t (a j) (b 0))
      (fun j => xiMat L 1 s t (a j) (b j) - xiMat L 1 s t (a j) (b 0))
    simp only [add_sub_cancel] at h1
    rw [← Finset.mul_prod_erase Finset.univ (fun i => xiMat L 1 s t (a i) (b i))
      (Finset.mem_univ 0)]
    change (xiMat L 1 s t (a 0) (b 0) * ∏ j ∈ s', xiMat L 1 s t (a j) (b j)) * A b = _
    rw [h1, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold c3C c3G c3Q
    ring
  have hzero : ∑ b : Fin k → Z2 L,
      (xiMat L 1 s t (a 0) (b 0) * ∏ j ∈ s', xiMat L 1 s t (a j) (b 0)) * A b = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin k → Z2 L => b 0)
      (fun b => (xiMat L 1 s t (a 0) (b 0) * ∏ j ∈ s', xiMat L 1 s t (a j) (b 0)) * A b)]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hfib : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
        (xiMat L 1 s t (a 0) (b 0) * ∏ j ∈ s', xiMat L 1 s t (a j) (b 0)) * A b =
          (xiMat L 1 s t (a 0) x * ∏ j ∈ s', xiMat L 1 s t (a j) x) * A b := by
      intro b hb
      rw [(Finset.mem_filter.1 hb).2]
    rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
    have := hA x
    simp only [this, mul_zero]
  rw [Finset.sum_congr rfl fun b _ => hpt b, Finset.sum_add_distrib, hzero, zero_add]
  exact Finset.sum_comm

/-- The near part of `T_i`: `Ỹ_i[T](x) = Σ_{b : b 0 = x} 1[near b] c_i(b) T_b`. -/
private def c3Yt (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k)
    (T : (Fin k → Z2 L) → ℂ) (x : Z2 L) : ℂ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x), c3Ind L ρ b * c3C s t a i b * T b

private theorem c3_T_split (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k)
    (A : (Fin k → Z2 L) → ℂ) :
    ∑ b : Fin k → Z2 L, xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * A b =
      ∑ b : Fin k → Z2 L, xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (1 - c3Ind L ρ b) * A b +
      ∑ x : Z2 L, xiMat L 1 s t (a 0) x * c3Yt s t a ρ i A x := by
  classical
  have h1 : ∀ b : Fin k → Z2 L, xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * A b =
      xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (1 - c3Ind L ρ b) * A b +
      xiMat L 1 s t (a 0) (b 0) * (c3Ind L ρ b * c3C s t a i b * A b) := by
    intro b; ring
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin k → Z2 L => b 0)
    (fun b => xiMat L 1 s t (a 0) (b 0) * (c3Ind L ρ b * c3C s t a i b * A b))]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold c3Yt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.1 hb).2]

/-- The far part of `T_i` (`≤ δ_A · r'^k`). -/
private theorem c3_far_bound (hXe : XiEntryBound) (hXr : XiRowBound) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0) {ρ δA : ℝ}
    (hδ : 0 ≤ δA) {A : (Fin k → Z2 L) → ℂ} (hfar : ∀ b, ¬ c3Near L ρ b → ‖A b‖ ≤ δA) :
    ‖∑ b : Fin k → Z2 L, xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (1 - c3Ind L ρ b) * A b‖ ≤
      δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k := by
  classical
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : Fin k → Z2 L,
        ‖xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (1 - c3Ind L ρ b) * A b‖
      ≤ ∑ b : Fin k → Z2 L, δA * (‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul, norm_mul]
        by_cases hn : c3Near L ρ b
        · have : c3Ind L ρ b = 1 := by simp [c3Ind, hn]
          rw [this, sub_self, norm_zero]
          simp only [mul_zero, zero_mul]
          positivity
        · have : c3Ind L ρ b = 0 := by simp [c3Ind, hn]
          rw [this, sub_zero, norm_one, mul_one]
          have h1 := hfar b hn
          calc ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖ * ‖A b‖
              ≤ ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖ * δA :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = δA * (‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖) := by ring
    _ = δA * ∑ b : Fin k → Z2 L, ‖xiMat L 1 s t (a 0) (b 0)‖ * ‖c3C s t a i b‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k :=
        mul_le_mul_of_nonneg_left (c3_far_sum hXe hXr hL hs hst ht a i hi) hδ

/-- `w_i(x) > 0`. -/
private theorem c3w_pos (hL : 3 ≤ L) {t : ℝ} (ht : t < 1) (s : ℝ) (a : Fin k → Z2 L) (i : Fin k)
    (x : Z2 L) : 0 < c3w s t a i x := by
  have : 0 < 1 - t := by linarith
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  unfold c3w
  positivity

/-- The normalised field `Y_i[T](x) = Ỹ_i[T](x) / w_i(x)` (`clt-yform`, for the label `x`). -/
private def c3Y (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k)
    (T : (Fin k → Z2 L) → ℂ) (x : Z2 L) : ℂ :=
  (((c3w s t a i x)⁻¹ : ℝ) : ℂ) * c3Yt s t a ρ i T x

private theorem c3_Yt_norm_le (hXe : XiEntryBound) (hXd : XiFirstDiff) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {T : (Fin k → Z2 L) → ℂ} {MT : ℝ} (hMT : 0 ≤ MT) (hT : ∀ b, ‖T b‖ ≤ MT)
    (x : Z2 L) : ‖c3Yt s t a ρ i T x‖ ≤ c3SY L k s t ρ * c3w s t a i x * MT := by
  unfold c3Yt
  calc ‖∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
        c3Ind L ρ b * c3C s t a i b * T b‖
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
          ‖c3Ind L ρ b * c3C s t a i b‖ * MT := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hT b) (norm_nonneg _)
    _ = (∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = x),
          ‖c3Ind L ρ b * c3C s t a i b‖) * MT := by rw [Finset.sum_mul]
    _ ≤ (c3SY L k s t ρ * c3w s t a i x) * MT :=
        mul_le_mul_of_nonneg_right (c3_fiber_bound hXe hXd hL hs hst ht a i hi hρ x) hMT

private theorem c3_Y_norm_le (hXe : XiEntryBound) (hXd : XiFirstDiff) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {T : (Fin k → Z2 L) → ℂ} {MT : ℝ} (hMT : 0 ≤ MT) (hT : ∀ b, ‖T b‖ ≤ MT)
    (x : Z2 L) : ‖c3Y s t a ρ i T x‖ ≤ c3SY L k s t ρ * MT := by
  have hw := c3w_pos hL ht s a i x
  unfold c3Y
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hw.le)]
  have h := c3_Yt_norm_le hXe hXd hL hs hst ht a i hi hρ hMT hT x
  calc (c3w s t a i x)⁻¹ * ‖c3Yt s t a ρ i T x‖
      ≤ (c3w s t a i x)⁻¹ * (c3SY L k s t ρ * c3w s t a i x * MT) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hw.le)
    _ = c3SY L k s t ρ * MT := by field_simp


/-! ### The `clt-lemma` split: `Z`, `Z̃` and the far cut-off of `Ξ₁` -/

/-- `ϖ = ℓ_t² (1 - t)/(1 - s) = η_s^{-1} ℓ_t² η_t` (up to the factor `Im m`), the normalisation of
`Z` in proof of `lem:sum_decay`. -/
private def c3vp (L : ℕ) (s t : ℝ) : ℝ := ellT L t ^ 2 * (1 - t) / (1 - s)

/-- The constant weight `(√(1-t) ℓ_t²)^{-1}` of `Xi-bound-1`. -/
private def c3w2 (L : ℕ) (t : ℝ) : ℝ := (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹

/-- The matrix `Z` of `clt-lemma` Case 2 (proof of `lem:sum_decay`):
`ϖ Ξ_{a_0 x} (|y - x|_L + 1)^{-1}`. -/
private def c3Z1 (s t : ℝ) (a : Fin k → Z2 L) : Matrix (Z2 L) (Z2 L) ℂ :=
  fun y x => ((c3vp L s t : ℝ) : ℂ) * xiMat L 1 s t (a 0) x *
    ((((zdist2 L (y - x) : ℝ) + 1)⁻¹ : ℝ) : ℂ)

open scoped Classical in
/-- The matrix `Z̃` of `clt-lemma` Case 1 (proof of `lem:sum_decay`):
`ϖ w₂ Ξ_{y x} 1[|y - x|_L < ρ_t]`. -/
private def c3Z2 (s t ρt : ℝ) : Matrix (Z2 L) (Z2 L) ℂ :=
  fun y x => ((c3vp L s t * c3w2 L t : ℝ) : ℂ) * xiMat L 1 s t y x *
    (if (zdist2 L (y - x) : ℝ) < ρt then (1 : ℂ) else 0)

private theorem c3vp_pos (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 0 < c3vp L s t := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - s := by linarith
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  unfold c3vp
  positivity

private theorem c3w2_pos (hL : 3 ≤ L) {t : ℝ} (ht : t < 1) : 0 < c3w2 L t := by
  have h1 : 0 < 1 - t := by linarith
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  unfold c3w2
  positivity

private theorem c3Yt_sub (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k)
    (T₁ T₂ : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    c3Yt s t a ρ i (fun b => T₁ b - T₂ b) x = c3Yt s t a ρ i T₁ x - c3Yt s t a ρ i T₂ x := by
  unfold c3Yt
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

private theorem c3Y_sub (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k)
    (T₁ T₂ : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    c3Y s t a ρ i (fun b => T₁ b - T₂ b) x = c3Y s t a ρ i T₁ x - c3Y s t a ρ i T₂ x := by
  unfold c3Y
  rw [c3Yt_sub]
  ring

open scoped Classical in
/-- **Near decomposition** (proof of `lem:sum_decay`): `Σ_x Ξ_{a_0 x} Ỹ_i(x)` splits into the
`Z`-sum of
Case 2, the `Z̃`-sum of Case 1, and the far cut-off of `Ξ_{a_0 ·}`. -/
private theorem c3_near_decomp (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1)
    (a : Fin k → Z2 L) (ρ ρt : ℝ) (i : Fin k) (A : (Fin k → Z2 L) → ℂ) :
    ∑ x : Z2 L, xiMat L 1 s t (a 0) x * c3Yt s t a ρ i A x =
      (((c3vp L s t : ℝ) : ℂ))⁻¹ * (∑ x : Z2 L, c3Z1 s t a (a i) x * c3Y s t a ρ i A x +
        ∑ x : Z2 L, c3Z2 s t ρt (a 0) x * c3Y s t a ρ i A x +
        ∑ x : Z2 L, ((c3vp L s t * c3w2 L t : ℝ) : ℂ) * xiMat L 1 s t (a 0) x *
          (1 - (if (zdist2 L (a 0 - x) : ℝ) < ρt then (1 : ℂ) else 0)) *
            c3Y s t a ρ i A x) := by
  have hvp : ((c3vp L s t : ℝ) : ℂ) ≠ 0 := by
    have := c3vp_pos hL hst ht
    exact_mod_cast this.ne'
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hw := c3w_pos hL ht s a i x
  have hYt : c3Yt s t a ρ i A x = ((c3w s t a i x : ℝ) : ℂ) * c3Y s t a ρ i A x := by
    unfold c3Y
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne']
    simp
  have hw' : c3w s t a i x = ((zdist2 L (a i - x) : ℝ) + 1)⁻¹ + c3w2 L t := rfl
  rw [hYt, hw']
  unfold c3Z1 c3Z2
  push_cast
  field_simp
  ring

/-- The entries of `Ξ` beyond the cut-off `ℓ_t K_w` (`Xi-bound-0`, exponential decay). -/
private theorem c3_entry_far (hXe : XiEntryBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a c : Z2 L) {Kw : ℝ} (h : ellT L t * Kw ≤ (zdist2 L (a - c) : ℝ)) :
    ‖xiMat L 1 s t a c‖ ≤ c3e L s t * Real.exp (-Kw / 20000) := by
  have h0 := hXe L hL 1 (by simp) s t hs hst ht a c
  have he0 := c3e_nonneg hL hst ht
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht).1
  have hexp : Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) ≤ Real.exp (-Kw / 20000) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖xiMat L 1 s t a c‖ ≤ c3e L s t * Real.exp (-(zdist2 L (a - c) : ℝ) / (20000 * ellT L t)) :=
        h0
    _ ≤ c3e L s t * Real.exp (-Kw / 20000) := mul_le_mul_of_nonneg_left hexp he0

open scoped Classical in
/-- The far cut-off sum (`Z̃` is supported in `|b_1 - a_1|_L < ℓ_t K_w`; the rest of `Ξ_{a_1 ·}`
is exponentially small). -/
private theorem c3_tail_bound (hXe : XiEntryBound) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L) {Kw : ℝ} (Yf : Z2 L → ℂ) {Ym : ℝ}
    (hY : ∀ x, ‖Yf x‖ ≤ Ym) :
    ‖∑ x : Z2 L, ((c3vp L s t * c3w2 L t : ℝ) : ℂ) * xiMat L 1 s t (a 0) x *
        (1 - (if (zdist2 L (a 0 - x) : ℝ) < ellT L t * Kw then (1 : ℂ) else 0)) * Yf x‖ ≤
      (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t * (c3e L s t * Real.exp (-Kw / 20000)) * Ym) := by
  have hYm : 0 ≤ Ym := (norm_nonneg _).trans (hY (a 0))
  have hvp := c3vp_pos hL hst ht
  have hw2 := c3w2_pos hL ht
  have he0 := c3e_nonneg hL hst ht
  have hcoef : 0 ≤ c3vp L s t * c3w2 L t * (c3e L s t * Real.exp (-Kw / 20000)) * Ym := by
    positivity
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x : Z2 L, ‖((c3vp L s t * c3w2 L t : ℝ) : ℂ) * xiMat L 1 s t (a 0) x *
          (1 - (if (zdist2 L (a 0 - x) : ℝ) < ellT L t * Kw then (1 : ℂ) else 0)) * Yf x‖
      ≤ ∑ _x : Z2 L, c3vp L s t * c3w2 L t * (c3e L s t * Real.exp (-Kw / 20000)) * Ym := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : (zdist2 L (a 0 - x) : ℝ) < ellT L t * Kw
        · simp only [hx, ↓reduceIte, sub_self, mul_zero, zero_mul, norm_zero]
          exact hcoef
        · simp only [hx, ↓reduceIte, sub_zero, mul_one]
          rw [norm_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
          have h1 := c3_entry_far hXe hL hs hst ht (a 0) x (not_lt.1 hx)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) (hY x) (norm_nonneg _)
            (by positivity)
    _ = (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t * (c3e L s t * Real.exp (-Kw / 20000)) * Ym) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c3_card_Z2]


/-! ### The master deterministic bound for alternating `σ` -/

open scoped Classical in
/-- **Master bound** (`sum_res_3`, proof of `lem:sum_decay`, alternating `σ`, deterministic part):
given the two
`clt-lemma` sums (bounds `B₁` for Case 2, `B₂` for Case 1) and the bounds `M₁`, `δ_A` on `𝒜`, `𝔼𝒜`
and on the far part of `𝒜 - 𝔼𝒜`. -/
private theorem c3_master (hXe : XiEntryBound) (hXr : XiRowBound) (hXd : XiFirstDiff)
    (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool) (hσ : ∀ i, σ i ≠ σ (i + 1))
    (a : Fin k → Z2 L) {Kw : ℝ} (hKw : 1 ≤ Kw)
    (𝒜 Ā : (Fin k → Z2 L) → ℂ) {M₁ δA : ℝ} (hM₁ : 0 ≤ M₁) (hδ : 0 ≤ δA)
    (h𝒜 : ∀ b, ‖𝒜 b‖ ≤ M₁) (hĀ : ∀ b, ‖Ā b‖ ≤ M₁)
    (hdec : ∀ b, ellT L s * Kw ≤ (KLoop.maxDist L b : ℝ) → ‖𝒜 b - Ā b‖ ≤ δA)
    (hsz : SumZero L (fun b => 𝒜 b - Ā b)) {B₁ B₂ : ℝ}
    (hC1 : ∀ i, i ≠ 0 → ‖∑ x : Z2 L, c3Z1 s t a (a i) x *
      (c3Y s t a (ellT L s * Kw) i 𝒜 x - c3Y s t a (ellT L s * Kw) i Ā x)‖ ≤ B₁)
    (hC2 : ∀ i, i ≠ 0 → ‖∑ x : Z2 L, c3Z2 s t (ellT L t * Kw) (a 0) x *
      (c3Y s t a (ellT L s * Kw) i 𝒜 x - c3Y s t a (ellT L s * Kw) i Ā x)‖ ≤ B₂) :
    ‖Ugen L E σ s t (fun b => 𝒜 b - Ā b) a‖ ≤
      ((k - 1 : ℕ) : ℝ) * (δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
        (c3vp L s t)⁻¹ * (B₁ + B₂ + (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t *
          (c3e L s t * Real.exp (-Kw / 20000)) * (c3SY L k s t (ellT L s * Kw) * (2 * M₁))))) +
      2 ^ k * (2 * M₁ * (1 * (1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
        δA * ((1 - s) / (1 - t)) ^ k) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hρ0 : 0 ≤ ellT L s * Kw := by nlinarith
  have hvp := c3vp_pos hL hst ht
  have hAM : ∀ b, ‖𝒜 b - Ā b‖ ≤ 2 * M₁ := fun b => by
    calc ‖𝒜 b - Ā b‖ ≤ ‖𝒜 b‖ + ‖Ā b‖ := norm_sub_le _ _
      _ ≤ 2 * M₁ := by linarith [h𝒜 b, hĀ b]
  have hdecA : DecayWin L (ellT L s * Kw) δA (fun b => 𝒜 b - Ā b) := fun b hb => hdec b hb
  have hfar : ∀ b : Fin k → Z2 L, ¬ c3Near L (ellT L s * Kw) b → ‖𝒜 b - Ā b‖ ≤ δA := by
    intro b hb
    apply hdec b
    unfold c3Near at hb
    push Not at hb
    obtain ⟨i, hi⟩ := hb
    have h := Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (b p.1 - b p.2))
      (Finset.mem_univ (i, (0 : Fin k)))
    have h' : (zdist2 L (b i - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by exact_mod_cast h
    linarith
  rw [c3_ugen_alt hE σ hσ s t (fun b => 𝒜 b - Ā b) a]
  have huniv : (Finset.univ : Finset (Fin k)) ∈ (Finset.univ : Finset (Fin k)).powerset :=
    Finset.mem_powerset.2 (Finset.subset_univ _)
  rw [← Finset.add_sum_erase _ _ huniv]
  -- the pure-`Ξ` term
  have hmain : ∑ b : Fin k → Z2 L, ((∏ i ∈ (Finset.univ : Finset (Fin k)),
        xiMat L 1 s t (a i) (b i)) * ∏ i ∈ Finset.univ \ (Finset.univ : Finset (Fin k)),
          (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) * (𝒜 b - Ā b) =
      ∑ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Fin k → Z2 L,
        xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (𝒜 b - Ā b) := by
    rw [← c3_main_term hsz s t a]
    simp
  rw [hmain]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the main term
    have hTi : ∀ i ∈ Finset.univ.erase (0 : Fin k),
        ‖∑ b : Fin k → Z2 L, xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (𝒜 b - Ā b)‖ ≤
          δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
            (c3vp L s t)⁻¹ * (B₁ + B₂ + (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t *
              (c3e L s t * Real.exp (-Kw / 20000)) *
                (c3SY L k s t (ellT L s * Kw) * (2 * M₁)))) := by
      intro i hi'
      have hi : i ≠ 0 := Finset.ne_of_mem_erase hi'
      rw [c3_T_split s t a (ellT L s * Kw) i (fun b => 𝒜 b - Ā b)]
      refine (norm_add_le _ _).trans (add_le_add
        (c3_far_bound hXe hXr hL hs hst ht a i hi hδ hfar) ?_)
      rw [c3_near_decomp hL hst ht a (ellT L s * Kw) (ellT L t * Kw) i (fun b => 𝒜 b - Ā b)]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hvp.le]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hvp.le)
      simp only [c3Y_sub]
      have hY : ∀ x, ‖c3Y s t a (ellT L s * Kw) i 𝒜 x - c3Y s t a (ellT L s * Kw) i Ā x‖ ≤
          c3SY L k s t (ellT L s * Kw) * (2 * M₁) := by
        intro x
        have := c3_Y_norm_le hXe hXd hL hs hst ht a i hi hρ0 (T := fun b => 𝒜 b - Ā b)
          (MT := 2 * M₁) (by linarith) hAM x
        rw [c3Y_sub] at this
        exact this
      have h3 := c3_tail_bound hXe hL hs hst ht a (Kw := Kw)
        (fun x => c3Y s t a (ellT L s * Kw) i 𝒜 x - c3Y s t a (ellT L s * Kw) i Ā x) hY
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (hC1 i hi) (hC2 i hi))) h3)
    calc ‖∑ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Fin k → Z2 L,
          xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (𝒜 b - Ā b)‖
        ≤ ∑ i ∈ Finset.univ.erase (0 : Fin k), ‖∑ b : Fin k → Z2 L,
          xiMat L 1 s t (a 0) (b 0) * c3C s t a i b * (𝒜 b - Ā b)‖ := norm_sum_le _ _
      _ ≤ (Finset.univ.erase (0 : Fin k)).card •
          (δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
            (c3vp L s t)⁻¹ * (B₁ + B₂ + (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t *
              (c3e L s t * Real.exp (-Kw / 20000)) *
                (c3SY L k s t (ellT L s * Kw) * (2 * M₁))))) :=
          Finset.sum_le_card_nsmul _ _ _ hTi
      _ = ((k - 1 : ℕ) : ℝ) * (δA * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
            (c3vp L s t)⁻¹ * (B₁ + B₂ + (L : ℝ) ^ 2 * (c3vp L s t * c3w2 L t *
              (c3e L s t * Real.exp (-Kw / 20000)) *
                (c3SY L k s t (ellT L s * Kw) * (2 * M₁))))) := by
          rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  · -- the terms with a `δ`
    have hSub : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase Finset.univ,
        ‖∑ b : Fin k → Z2 L, ((∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
            ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) *
              (𝒜 b - Ā b)‖ ≤
          2 * M₁ * (1 * (1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
            δA * ((1 - s) / (1 - t)) ^ k := by
      intro S hS
      exact c3_subset_bound hXe hXr hL hs hst ht a hρ0 (by linarith) hδ hAM hdecA S
        (Finset.ne_of_mem_erase hS)
    calc ‖∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase Finset.univ,
          ∑ b : Fin k → Z2 L, ((∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
            ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) *
              (𝒜 b - Ā b)‖
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase Finset.univ,
          ‖∑ b : Fin k → Z2 L, ((∏ i ∈ S, xiMat L 1 s t (a i) (b i)) *
            ∏ i ∈ Finset.univ \ S, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) *
              (𝒜 b - Ā b)‖ := norm_sum_le _ _
      _ ≤ ((Finset.univ : Finset (Fin k)).powerset.erase Finset.univ).card •
          (2 * M₁ * (1 * (1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
            δA * ((1 - s) / (1 - t)) ^ k) := Finset.sum_le_card_nsmul _ _ _ hSub
      _ ≤ 2 ^ k * (2 * M₁ * (1 * (1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
            δA * ((1 - s) / (1 - t)) ^ k) := by
          rw [nsmul_eq_mul]
          have hcard : (((Finset.univ : Finset (Fin k)).powerset.erase Finset.univ).card : ℝ) ≤
              2 ^ k := by
            have h1 : (((Finset.univ : Finset (Fin k)).powerset.erase Finset.univ).card : ℕ) ≤
                2 ^ k := by
              rw [Finset.card_erase_of_mem huniv, Finset.card_powerset, Finset.card_univ,
                Fintype.card_fin]
              exact Nat.sub_le _ _
            exact_mod_cast h1
          have hnn : 0 ≤ 2 * M₁ * (1 * (1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t) ^ (k - 1)) +
              δA * ((1 - s) / (1 - t)) ^ k := by
            have he0 := c3e_nonneg hL hst ht
            have h1t : 0 < 1 - t := by linarith
            have : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) h1t.le
            positivity
          exact mul_le_mul_of_nonneg_right hcard hnn


/-! ### The `clt-lemma` local form of the field `Y_i` -/

private theorem c3SY_nonneg (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ c3SY L k s t ρ := by
  have hP := c3_P_nonneg L
  have he0 := c3e_nonneg hL hst ht
  have hts : 0 ≤ t - s := by linarith
  unfold c3SY
  positivity

open scoped Classical in
/-- The one-label local form of the field `Y_i` (`clt-yform`): the coefficients
`Y_i[coef(·, j, q)](x)` (zero unless `good`). -/
private def c3FY {W K : ℕ} (F : LocalForm L W k K) (s t : ℝ) (a : Fin k → Z2 L) (ρ : ℝ)
    (i : Fin k) (good : Prop) : LocalForm L W 1 K where
  coef x j q := if good then c3Y s t a ρ i (fun b => F.coef b j q) (x 0) else 0

/-- The form evaluates to `Y_i[𝒜](x)`. -/
private theorem c3FY_eval {W K : ℕ} [NeZero W] (F : LocalForm L W k K) (s t : ℝ)
    (a : Fin k → Z2 L) (ρ : ℝ) (i : Fin k) {good : Prop} (hg : good) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (x : Z2 L) :
    cltY (c3FY F s t a ρ i good) E u M x = c3Y s t a ρ i (fun b => F.eval E u M b) x := by
  classical
  unfold cltY LocalForm.eval c3FY c3Y c3Yt
  simp only [hg, ↓reduceIte]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The coefficients of the form are bounded by `S_Y N^{C'}`. -/
private theorem c3FY_coef_le (hXe : XiEntryBound) (hXd : XiFirstDiff) (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {W K : ℕ} (F : LocalForm L W k K)
    (a : Fin k → Z2 L) (i : Fin k) (hi : i ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) {Nc : ℝ} (hNc : 0 ≤ Nc)
    (hcoef : ∀ b j q, ‖F.coef b j q‖ ≤ Nc) (good : Prop) (x : Fin 1 → Z2 L)
    (j : Fin (K + 1)) (q : Fin j → Idx L W × Idx L W × Bool) :
    ‖(c3FY F s t a ρ i good).coef x j q‖ ≤ c3SY L k s t ρ * Nc := by
  classical
  unfold c3FY
  by_cases hg : good
  · simp only [hg, ↓reduceIte]
    exact c3_Y_norm_le hXe hXd hL hs hst ht a i hi hρ (T := fun b => F.coef b j q) hNc
      (fun b => hcoef b j q) (x 0)
  · simp only [hg, ↓reduceIte, norm_zero]
    exact mul_nonneg (c3SY_nonneg hL hst ht hρ) hNc

/-- The form is local at `2τ` (proof of `lem:sum_decay`, "the `τ` parameter there is equal to two
times the `τ`
parameter here"): `|[x_i] - b_1| + |[y_i] - b_1| ≤ 3 ℓ_s W^τ ≤ ℓ_s W^{2τ}` once `W^τ ≥ 3`. -/
private theorem c3FY_local {W K : ℕ} [NeZero W] (F : LocalForm L W k K) {s : ℝ} (t : ℝ)
    (a : Fin k → Z2 L) {τ : ℝ} (hW0 : 0 < (W : ℝ)) (hℓ : 0 ≤ ellT L s) (hloc : F.Local τ s)
    (i : Fin k) (good : Prop) (hW3g : good → 3 ≤ (W : ℝ) ^ τ) :
    (c3FY F s t a (ellT L s * (W : ℝ) ^ τ) i good).Local (2 * τ) s := by
  classical
  intro b j q hne i'
  have hgood : good := by
    by_contra hg
    apply hne
    simp [c3FY, hg]
  have hW3 : 3 ≤ (W : ℝ) ^ τ := hW3g hgood
  have hne' : c3Yt s t a (ellT L s * (W : ℝ) ^ τ) i (fun b' => F.coef b' j q) (b 0) ≠ 0 := by
    intro h0
    apply hne
    simp [c3FY, hgood, c3Y, h0]
  obtain ⟨b', hb', hne''⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hb'0 : b' 0 = b 0 := (Finset.mem_filter.1 hb').2
  have hind : c3Ind L (ellT L s * (W : ℝ) ^ τ) b' ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hne'')
  have hnear : c3Near L (ellT L s * (W : ℝ) ^ τ) b' := by
    by_contra hn
    apply hind
    simp [c3Ind, hn]
  have hcoef' : F.coef b' j q ≠ 0 := right_ne_zero_of_mul hne''
  obtain ⟨m, hm⟩ := hloc b' j q hcoef' i'
  refine ⟨0, ?_⟩
  rw [← hb'0]
  have hx : zdist2 L ((splitEquiv L W (q i').1).1 - b' 0) ≤
      zdist2 L ((splitEquiv L W (q i').1).1 - b' m) + zdist2 L (b' m - b' 0) := by
    have := zdist2_add_le L ((splitEquiv L W (q i').1).1 - b' m) (b' m - b' 0)
    rwa [sub_add_sub_cancel] at this
  have hy : zdist2 L ((splitEquiv L W (q i').2.1).1 - b' 0) ≤
      zdist2 L ((splitEquiv L W (q i').2.1).1 - b' m) + zdist2 L (b' m - b' 0) := by
    have := zdist2_add_le L ((splitEquiv L W (q i').2.1).1 - b' m) (b' m - b' 0)
    rwa [sub_add_sub_cancel] at this
  have hnb : (zdist2 L (b' m - b' 0) : ℝ) < ellT L s * (W : ℝ) ^ τ := hnear m
  have hW2 : (W : ℝ) ^ (2 * τ) = (W : ℝ) ^ τ * (W : ℝ) ^ τ := by
    rw [two_mul, Real.rpow_add hW0]
  have hρ0 : 0 ≤ ellT L s * (W : ℝ) ^ τ := by positivity
  have h3 : 3 * (ellT L s * (W : ℝ) ^ τ) ≤ ellT L s * (W : ℝ) ^ (2 * τ) := by
    rw [hW2]
    nlinarith
  have hcast : (((zdist2 L ((splitEquiv L W (q i').1).1 - b' 0) +
      zdist2 L ((splitEquiv L W (q i').2.1).1 - b' 0) : ℕ)) : ℝ) ≤
      (((zdist2 L ((splitEquiv L W (q i').1).1 - b' m) +
        zdist2 L ((splitEquiv L W (q i').2.1).1 - b' m) : ℕ)) : ℝ) +
        2 * (zdist2 L (b' m - b' 0) : ℝ) := by
    have : zdist2 L ((splitEquiv L W (q i').1).1 - b' 0) +
        zdist2 L ((splitEquiv L W (q i').2.1).1 - b' 0) ≤
        (zdist2 L ((splitEquiv L W (q i').1).1 - b' m) +
          zdist2 L ((splitEquiv L W (q i').2.1).1 - b' m)) + 2 * zdist2 L (b' m - b' 0) := by
      omega
    exact_mod_cast this
  linarith


/-! ### The scale bookkeeping (exponent bounds, Case 3) -/

/-- `q = ℓ_s² (t - s) / min(1, L²(1 - t))`, the quantity with `q ≤ R_{s,t}`. -/
private def c3q (L : ℕ) (s t : ℝ) : ℝ := ellT L s ^ 2 * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))

private theorem c3q_nonneg (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 0 ≤ c3q L s t := by
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  unfold c3q
  exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hm.le

/-- `q ≤ R` (the step `ℓ_s² (t - s)/min(1, L²(1-t)) ≤ R`). -/
private theorem c3q_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    c3q L s t ≤ rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  unfold c3q
  rw [KernelExpand_rhoR_eq hs1 ht, ← KernelExpand_ellT_sq_mul hs1,
    div_le_div_iff_of_pos_right hm]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

private theorem c3_ell2_e (L : ℕ) (s t : ℝ) :
    ellT L s ^ 2 * c3e L s t = 2 * cProp5 * (1 + Real.log L) * c3q L s t := by
  unfold c3e c3q
  ring

/-- The window factor `1 + (2ρ+1)² e ≤ (1 + 18 cProp5)(1 + log L) K_w² R`
(a re-proof of the private `window_const` of `KernelExpand.lean`). -/
private theorem c3_Bw_le (hL : 3 ≤ L) {s t Kw : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (hK : 1 ≤ Kw) :
    1 + (2 * (ellT L s * Kw) + 1) ^ 2 * c3e L s t ≤
      (1 + 18 * cProp5) * (1 + Real.log L) * Kw ^ 2 * rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hlog1 : 1 ≤ 1 + Real.log L := c3_lam_one L
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hq := c3q_le hL hst ht
  have hq0 := c3q_nonneg hL hst ht
  have he0 := c3e_nonneg hL hst ht
  set ℓ : ℝ := ellT L s with hℓdef
  set R : ℝ := rhoR L s t with hRdef
  set lam : ℝ := 1 + Real.log L with hlam
  have hρ1 : 1 ≤ ℓ * Kw := by nlinarith
  have h9 : (2 * (ℓ * Kw) + 1) ^ 2 ≤ 9 * (ℓ * Kw) ^ 2 := by nlinarith
  have hρe : (ℓ * Kw) ^ 2 * c3e L s t = Kw ^ 2 * (2 * cProp5 * lam * c3q L s t) := by
    rw [← c3_ell2_e L s t]; ring
  have hpos : 0 ≤ 2 * cProp5 * lam * Kw ^ 2 := by positivity
  have h1 : 1 ≤ lam * Kw ^ 2 * R := by
    have : 1 ≤ Kw ^ 2 := by nlinarith
    have h2 : 1 ≤ lam * Kw ^ 2 := by nlinarith
    nlinarith
  calc 1 + (2 * (ℓ * Kw) + 1) ^ 2 * c3e L s t
      ≤ 1 + 9 * (ℓ * Kw) ^ 2 * c3e L s t := by
        have := mul_le_mul_of_nonneg_right h9 he0
        linarith
    _ = 1 + 9 * (2 * cProp5 * lam * Kw ^ 2 * c3q L s t) := by
        rw [mul_assoc 9, hρe]; ring
    _ ≤ 1 + 9 * (2 * cProp5 * lam * Kw ^ 2 * R) := by
        have := mul_le_mul_of_nonneg_left hq hpos
        linarith
    _ ≤ (1 + 18 * cProp5) * lam * Kw ^ 2 * R := by nlinarith

section Scale

variable {Nn : ℝ}

private theorem c3_mt_ge (hL : 3 ≤ L) {t : ℝ} (ht : t < 1) (hN1 : 1 ≤ Nn)
    (h1t : 1 / Nn ≤ 1 - t) : 1 / Nn ≤ min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
  have hN0 : 0 < Nn := by linarith
  refine le_min ?_ ?_
  · rw [div_le_one hN0]; exact hN1
  · have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
      nlinarith
    calc 1 / Nn ≤ 1 - t := h1t
      _ = 1 * (1 - t) := (one_mul _).symm
      _ ≤ (L : ℝ) ^ 2 * (1 - t) := mul_le_mul_of_nonneg_right hL2 (by linarith)

private theorem c3_r_le {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t)
    (hs : 0 ≤ s) : (1 - s) / (1 - t) ≤ Nn := by
  have hN0 : 0 < Nn := by linarith
  have h0 : 0 < 1 - t := by linarith
  rw [div_le_iff₀ h0]
  have : 1 ≤ Nn * (1 - t) := by
    calc (1 : ℝ) = Nn * (1 / Nn) := by field_simp
      _ ≤ Nn * (1 - t) := mul_le_mul_of_nonneg_left h1t hN0.le
  nlinarith

private theorem c3_rX_le {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t)
    (hs : 0 ≤ s) : (t - s) / (1 - t) ≤ Nn := by
  have h0 : 0 < 1 - t := by linarith
  refine le_trans ?_ (c3_r_le hst ht hN1 h1t hs)
  exact div_le_div_of_nonneg_right (by linarith) h0.le

private theorem c3_e_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (hs : 0 ≤ s)
    (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) :
    c3e L s t ≤ 2 * cProp5 * (1 + Real.log L) * Nn := by
  have hm := c3_mt_ge hL ht hN1 h1t
  have hN0 : 0 < Nn := by linarith
  have hm0 : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  unfold c3e
  have h1 : (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ Nn := by
    rw [div_le_iff₀ hm0]
    have : 1 ≤ Nn * min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
      calc (1 : ℝ) = Nn * (1 / Nn) := by field_simp
        _ ≤ Nn * min 1 ((L : ℝ) ^ 2 * (1 - t)) := mul_le_mul_of_nonneg_left hm hN0.le
    nlinarith
  have h2 : 2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) =
      2 * cProp5 * (1 + Real.log L) * ((t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) := by
    rw [mul_div_assoc]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

private theorem c3_rprime_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (hs : 0 ≤ s)
    (hN1 : 1 ≤ Nn) (hL2 : (L : ℝ) ^ 2 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) :
    (t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t ≤ (1 + 2 * cProp5) * (1 + Real.log L) * Nn ^ 2 := by
  have hX := c3_rX_le hst ht hN1 h1t hs
  have he := c3_e_le hL hst ht hs hN1 h1t
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlam := c3_lam_one L
  have hN0 : 0 < Nn := by linarith
  have he0 := c3e_nonneg hL hst ht
  have h1 : (L : ℝ) ^ 2 * c3e L s t ≤ Nn * (2 * cProp5 * (1 + Real.log L) * Nn) :=
    mul_le_mul hL2 he he0 hN0.le
  nlinarith [mul_nonneg hc5 (sub_nonneg.2 hlam), mul_nonneg hN0.le (sub_nonneg.2 hN1)]

private theorem c3_w2_le {s t : ℝ} (hL : 3 ≤ L) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) : c3w2 L t ≤ Nn := by
  have hN0 : 0 < Nn := by linarith
  have h0 : 0 < 1 - t := by linarith
  have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hsq : 1 - t ≤ Real.sqrt (1 - t) := by
    rw [Real.le_sqrt h0.le h0.le]; nlinarith
  have hsq0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h0
  unfold c3w2
  have h1 : (1 - t) * 1 ≤ Real.sqrt (1 - t) * ellT L t ^ 2 :=
    mul_le_mul hsq (by nlinarith) zero_le_one hsq0.le
  calc (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ ≤ ((1 - t) * 1)⁻¹ := inv_anti₀ (by positivity) h1
    _ = (1 - t)⁻¹ := by rw [mul_one]
    _ ≤ Nn := by
        rw [inv_le_comm₀ h0 hN0]
        simpa using h1t

end Scale

private theorem c3_vp_inv (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (c3vp L s t)⁻¹ = rhoR L s t / ellT L s ^ 2 := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓs : 0 < ellT L s := lt_of_lt_of_le one_pos (one_le_ellT (by omega) hs hs1)
  have hℓt : 0 < ellT L t :=
    lt_of_lt_of_le one_pos (one_le_ellT (by omega) (hs.trans hst) ht)
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  unfold c3vp rhoR
  field_simp

private theorem c3_vp_inv_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    (c3vp L s t)⁻¹ ≤ rhoR L s t := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  rw [c3_vp_inv hL hs hst ht, div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ ellT L s ^ 2 := by nlinarith
  calc rhoR L s t = rhoR L s t * 1 := (mul_one _).symm
    _ ≤ rhoR L s t * ellT L s ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)

/-- `w₂ ℓ_t min(1, L²(1-t)) = ℓ_t √(1-t) ≤ 1`. -/
private theorem c3_w2_mt (hL : 3 ≤ L) {t : ℝ} (ht : t < 1) (ht0 : 0 ≤ t) :
    c3w2 L t * ellT L t * min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ 1 := by
  have h0 : 0 < 1 - t := by linarith
  have hℓ : 0 < ellT L t := lt_of_lt_of_le one_pos (one_le_ellT (by omega) ht0 ht)
  have hy0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h0
  have key : ∀ x ℓ : ℝ, 0 < x → 0 < ℓ →
      (Real.sqrt x * ℓ ^ 2)⁻¹ * ℓ * (ℓ ^ 2 * x) = ℓ * Real.sqrt x := by
    intro x ℓ hx hℓ
    have hy : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    field_simp
    nlinarith [hy]
  have h1 : ellT L t * Real.sqrt (1 - t) ≤ 1 := by
    have h2 : ellT L t ≤ 1 / Real.sqrt (1 - t) := min_le_left _ _
    calc ellT L t * Real.sqrt (1 - t) ≤ 1 / Real.sqrt (1 - t) * Real.sqrt (1 - t) :=
          mul_le_mul_of_nonneg_right h2 hy0.le
      _ = 1 := by field_simp
  calc c3w2 L t * ellT L t * min 1 ((L : ℝ) ^ 2 * (1 - t))
      = (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ * ellT L t * (ellT L t ^ 2 * (1 - t)) := by
        rw [KernelExpand_ellT_sq_mul ht]; rfl
    _ = ellT L t * Real.sqrt (1 - t) := key (1 - t) (ellT L t) h0 hℓ
    _ ≤ 1 := h1

/-- **Bound on `S_Y`** (`llswuwg2`, ball count `eq-1sum`, and `Xi-bound-1`):
`S_Y ≤ 18 P ℓ_s K_w³ (q m_t) (9 c₁ K_w² R)^{k-2}`, `c₁ = 2 cProp5 (1 + log L)`. -/
private theorem c3_SY_le (hL : 3 ≤ L) (hk : 2 ≤ k) {s t Kw : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (hK : 1 ≤ Kw) :
    c3SY L k s t (ellT L s * Kw) ≤ 18 * derivativePrefactor (10 ^ 14) L * (ellT L s * Kw ^ 3) *
      (c3q L s t * min 1 ((L : ℝ) ^ 2 * (1 - t))) *
      (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hP := c3_P_nonneg L
  have he0 := c3e_nonneg hL hst ht
  have hq := c3q_le hL hst ht
  have hq0 := c3q_nonneg hL hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlam := c3_lam_one L
  have hts : 0 ≤ t - s := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ellT L s * Kw := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; nlinarith
  have h9 : (2 * ρ + 1) ^ 2 ≤ 9 * ρ ^ 2 := by nlinarith
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  have hqm : ellT L s ^ 2 * (t - s) = c3q L s t * min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
    unfold c3q; field_simp
  have hρe : 9 * ρ ^ 2 * c3e L s t ≤
      9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t := by
    have h1 : ρ ^ 2 * c3e L s t = Kw ^ 2 * (2 * cProp5 * (1 + Real.log L) * c3q L s t) := by
      rw [← c3_ell2_e L s t, hρdef]; ring
    have h2 : 2 * cProp5 * (1 + Real.log L) * c3q L s t ≤
        2 * cProp5 * (1 + Real.log L) * rhoR L s t :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc 9 * ρ ^ 2 * c3e L s t = 9 * (ρ ^ 2 * c3e L s t) := by ring
      _ = 9 * (Kw ^ 2 * (2 * cProp5 * (1 + Real.log L) * c3q L s t)) := by rw [h1]
      _ ≤ 9 * (Kw ^ 2 * (2 * cProp5 * (1 + Real.log L) * rhoR L s t)) := by
          gcongr
      _ = 9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t := by ring
  rw [← hρdef]
  unfold c3SY
  rw [hk1]
  calc 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * c3e L s t ^ (k - 2) *
        ((2 * ρ + 1) ^ 2) ^ (k - 2 + 1)
      ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * c3e L s t ^ (k - 2) *
        (9 * ρ ^ 2) ^ (k - 2 + 1) := by
        gcongr
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * (9 * ρ ^ 2) *
        (9 * ρ ^ 2 * c3e L s t) ^ (k - 2) := by
        rw [pow_succ, mul_pow]; ring
    _ ≤ 2 * derivativePrefactor (10 ^ 14) L * (t - s) * ρ * (9 * ρ ^ 2) *
        (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) := by
        gcongr
    _ = 18 * derivativePrefactor (10 ^ 14) L * (ellT L s * Kw ^ 3) *
        (c3q L s t * min 1 ((L : ℝ) ^ 2 * (1 - t))) *
        (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) := by
        rw [← hqm, hρdef]; ring



/-- Abstract form of (Q1): `(R/ℓ²)(ℓ S) ≤ 18 P K³ R² Y`. -/
private theorem c3_Q1_abs {ℓs S P Kw q mt Y R : ℝ} (hℓ : 0 < ℓs) (hP : 0 ≤ P) (hK : 0 ≤ Kw)
    (hq : 0 ≤ q) (hmt0 : 0 ≤ mt) (hmt : mt ≤ 1) (hqR : q ≤ R) (hR : 0 ≤ R) (hY : 0 ≤ Y)
    (hS : S ≤ 18 * P * (ℓs * Kw ^ 3) * (q * mt) * Y) :
    R / ℓs ^ 2 * (ℓs * S) ≤ 18 * P * Kw ^ 3 * R ^ 2 * Y := by
  have hqm : q * mt ≤ R := by
    calc q * mt ≤ q * 1 := mul_le_mul_of_nonneg_left hmt hq
      _ ≤ R := by linarith
  have hqm0 : 0 ≤ q * mt := mul_nonneg hq hmt0
  calc R / ℓs ^ 2 * (ℓs * S) ≤ R / ℓs ^ 2 * (ℓs * (18 * P * (ℓs * Kw ^ 3) * (q * mt) * Y)) := by
        gcongr
    _ = 18 * P * Kw ^ 3 * R * (q * mt) * Y := by field_simp
    _ ≤ 18 * P * Kw ^ 3 * R * R * Y := by
        have h1 : 0 ≤ 18 * P * Kw ^ 3 * R := by positivity
        have := mul_le_mul_of_nonneg_left hqm h1
        nlinarith
    _ = 18 * P * Kw ^ 3 * R ^ 2 * Y := by ring

/-- Abstract form of (Q2): `w₂ e ℓ_t ℓ_s S ≤ c₁ 18 P K³ R² Y`. -/
private theorem c3_Q2_abs {w2 ℓt ℓs S e c₁ P Kw q mt Y R : ℝ} (hℓ : 0 < ℓs) (hw2 : 0 ≤ w2)
    (hℓt : 0 ≤ ℓt) (hc₁ : 0 ≤ c₁) (hP : 0 ≤ P) (hK : 0 ≤ Kw) (hq : 0 ≤ q) (hmt0 : 0 ≤ mt)
    (hqR : q ≤ R) (hY : 0 ≤ Y) (he : ℓs ^ 2 * e = c₁ * q) (hS0 : 0 ≤ S)
    (hS : S ≤ 18 * P * (ℓs * Kw ^ 3) * (q * mt) * Y) (hwm : w2 * ℓt * mt ≤ 1) :
    w2 * e * (ℓt * (ℓs * S)) ≤ c₁ * (18 * P) * Kw ^ 3 * R ^ 2 * Y := by
  have he' : e = c₁ * q / ℓs ^ 2 := by
    field_simp; linarith
  have hR0 : 0 ≤ R := le_trans hq hqR
  have hq2 : q ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hq hqR 2
  have h1 : 0 ≤ w2 * ℓt := mul_nonneg hw2 hℓt
  calc w2 * e * (ℓt * (ℓs * S)) = (w2 * ℓt) * (c₁ * q / ℓs ^ 2 * (ℓs * S)) := by
        rw [he']; ring
    _ ≤ (w2 * ℓt) * (c₁ * q / ℓs ^ 2 * (ℓs * (18 * P * (ℓs * Kw ^ 3) * (q * mt) * Y))) := by
        gcongr
    _ = (w2 * ℓt * mt) * (c₁ * (18 * P) * Kw ^ 3 * q ^ 2 * Y) := by
        field_simp
    _ ≤ 1 * (c₁ * (18 * P) * Kw ^ 3 * q ^ 2 * Y) := by
        have h2 : 0 ≤ c₁ * (18 * P) * Kw ^ 3 * q ^ 2 * Y := by positivity
        exact mul_le_mul_of_nonneg_right hwm h2
    _ ≤ c₁ * (18 * P) * Kw ^ 3 * R ^ 2 * Y := by
        rw [one_mul]
        have h3 : 0 ≤ c₁ * (18 * P) * Kw ^ 3 := by positivity
        calc c₁ * (18 * P) * Kw ^ 3 * q ^ 2 * Y = (c₁ * (18 * P) * Kw ^ 3) * q ^ 2 * Y := by ring
          _ ≤ (c₁ * (18 * P) * Kw ^ 3) * R ^ 2 * Y := by gcongr

/-- **(Q1)**: `ϖ⁻¹ ℓ_s S_Y ≤ 18 P (18 cProp5 (1 + log L))^{k-2} K_w^{2k-1} R^k`
(the `Z` exponent bound). -/
private theorem c3_Q1 (hL : 3 ≤ L) (hk : 2 ≤ k) {s t Kw : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (hK : 1 ≤ Kw) :
    (c3vp L s t)⁻¹ * (ellT L s * c3SY L k s t (ellT L s * Kw)) ≤
      18 * derivativePrefactor (10 ^ 14) L * (18 * cProp5 * (1 + Real.log L)) ^ (k - 2) *
        Kw ^ (2 * k - 1) * rhoR L s t ^ k := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hP := c3_P_nonneg L
  have hq := c3q_le hL hst ht
  have hq0 := c3q_nonneg hL hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlam := c3_lam_one L
  have hS := c3_SY_le hL hk hs hst ht hK
  have hY : 0 ≤ (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) := by
    apply pow_nonneg; positivity
  rw [c3_vp_inv hL hs hst ht]
  refine (c3_Q1_abs (by linarith) hP (by linarith) hq0 hm.le (min_le_left _ _) hq
    (by linarith) hY hS).trans (le_of_eq ?_)
  have hY_eq : (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) =
      (18 * cProp5 * (1 + Real.log L)) ^ (k - 2) * (Kw ^ 2) ^ (k - 2) *
        rhoR L s t ^ (k - 2) := by
    have h18 : (9 : ℝ) * (2 * cProp5 * (1 + Real.log L)) = 18 * cProp5 * (1 + Real.log L) := by
      ring
    rw [h18, mul_pow, mul_pow]
  have hKw_eq : Kw ^ (2 * k - 1) = Kw ^ 3 * (Kw ^ 2) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hR_eq : rhoR L s t ^ k = rhoR L s t ^ 2 * rhoR L s t ^ (k - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hY_eq, hKw_eq, hR_eq]
  ring

/-- **(Q2)**: `w₂ e ℓ_t ℓ_s S_Y ≤ c₁ · 18 P (18 cProp5 (1 + log L))^{k-2} K_w^{2k-1} R^k`
(the `Z̃` exponent bound). -/
private theorem c3_Q2 (hL : 3 ≤ L) (hk : 2 ≤ k) {s t Kw : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (hK : 1 ≤ Kw) :
    c3w2 L t * c3e L s t * (ellT L t * (ellT L s * c3SY L k s t (ellT L s * Kw))) ≤
      (2 * cProp5 * (1 + Real.log L)) * (18 * derivativePrefactor (10 ^ 14) L) *
        (18 * cProp5 * (1 + Real.log L)) ^ (k - 2) * Kw ^ (2 * k - 1) * rhoR L s t ^ k := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hℓ : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hℓt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hP := c3_P_nonneg L
  have hq := c3q_le hL hst ht
  have hq0 := c3q_nonneg hL hst ht
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlam := c3_lam_one L
  have hS := c3_SY_le hL hk hs hst ht hK
  have hY : 0 ≤ (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) := by
    apply pow_nonneg; positivity
  have hS0 : 0 ≤ c3SY L k s t (ellT L s * Kw) :=
    c3SY_nonneg hL hst ht (by positivity)
  have hw2 := c3w2_pos hL ht
  refine (c3_Q2_abs (by linarith) hw2.le (by linarith) (by positivity) hP (by linarith) hq0
    hm.le hq hY (c3_ell2_e L s t) hS0 hS (c3_w2_mt hL ht (hs.trans hst))).trans (le_of_eq ?_)
  have hY_eq : (9 * (2 * cProp5 * (1 + Real.log L)) * Kw ^ 2 * rhoR L s t) ^ (k - 2) =
      (18 * cProp5 * (1 + Real.log L)) ^ (k - 2) * (Kw ^ 2) ^ (k - 2) *
        rhoR L s t ^ (k - 2) := by
    have h18 : (9 : ℝ) * (2 * cProp5 * (1 + Real.log L)) = 18 * cProp5 * (1 + Real.log L) := by
      ring
    rw [h18, mul_pow, mul_pow]
  have hKw_eq : Kw ^ (2 * k - 1) = Kw ^ 3 * (Kw ^ 2) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hR_eq : rhoR L s t ^ k = rhoR L s t ^ 2 * rhoR L s t ^ (k - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hY_eq, hKw_eq, hR_eq]
  ring

end Det


/-- The integral of the normalised field is the field of the integral. -/
private theorem c3Y_integral {L : ℕ} [NeZero L] {k : ℕ} [NeZero k] (s t : ℝ) (a : Fin k → Z2 L)
    (ρ : ℝ) (i : Fin k) (x : Z2 L) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : (Fin k → Z2 L) → Ω → ℂ) (hf : ∀ b, Integrable (f b) μ) :
    ∫ ω, c3Y s t a ρ i (fun b => f b ω) x ∂μ =
      c3Y s t a ρ i (fun b => ∫ ω, f b ω ∂μ) x := by
  classical
  unfold c3Y c3Yt
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun b _ => ?_)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  · exact (hf b).const_mul _

/-! ## Part 2: the random tensor on the common probability space -/

section Seq

variable (d : Sizes)

/-- Polylog absorption at a real variable: `|c| (1 + log x)^m ≤ x^ε` eventually. -/
private theorem c3_polylog_real (c : ℝ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |c| * (1 + Real.log x) ^ m ≤ x ^ ε := by
  have hc : 0 < (2 ^ m * (|c| + 1))⁻¹ := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hε).def hc
  have h2 : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
  filter_upwards [h1, h2] with x hN1 hN2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hN2
  have hlog1 : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_natCast,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hN1
  have hpow : (1 + Real.log x) ^ m ≤ 2 ^ m * Real.log x ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) m
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
  calc |c| * (1 + Real.log x) ^ m ≤ |c| * (2 ^ m * Real.log x ^ m) := by gcongr
    _ ≤ |c| * (2 ^ m * ((2 ^ m * (|c| + 1))⁻¹ * x ^ ε)) := by gcongr
    _ = |c| / (|c| + 1) * x ^ ε := by field_simp
    _ ≤ 1 * x ^ ε := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = x ^ ε := one_mul _

private theorem c3_L_le_size (n : ℕ) : d.L n ≤ d.size n := by
  have h1 : 1 ≤ d.W n := d.W_pos n
  have h2 : 3 ≤ d.L n := d.three_le_L n
  unfold Sizes.size
  calc d.L n = 1 * d.L n := (one_mul _).symm
    _ ≤ d.W n * d.L n := Nat.mul_le_mul_right _ h1
    _ ≤ (d.W n * d.L n) * (d.W n * d.L n) := Nat.le_mul_of_pos_right _ (Nat.mul_pos h1 (by omega))
    _ = (d.W n * d.L n) ^ 2 := (sq _).symm

/-- Polylog absorption along the admissible sizes. -/
private theorem c3_polylog (hN : SizeTendsto d) (c : ℝ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |c| * (1 + Real.log (d.L n : ℝ)) ^ m ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [hN.eventually (c3_polylog_real c m hε)] with n hn
  refine le_trans ?_ hn
  have hL : (0 : ℝ) < (d.L n : ℝ) := by exact_mod_cast (by have := d.three_le_L n; omega)
  have hlog : Real.log (d.L n : ℝ) ≤ Real.log ((d.size n : ℕ) : ℝ) :=
    Real.log_le_log hL (by exact_mod_cast c3_L_le_size d n)
  have hlog0 : 0 ≤ Real.log (d.L n : ℝ) := Real.log_natCast_nonneg _
  gcongr

/-- `W → ∞` from `Bandwidth` and `SizeTendsto`. -/
private theorem c3_W_large (hN : SizeTendsto d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hW : Bandwidth d 𝔠)
    (X : ℝ) : ∀ᶠ n : ℕ in atTop, X ≤ (d.W n : ℝ) := by
  have h1 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  filter_upwards [h1.eventually_ge_atTop X, hW] with n h1 h2 using h1.trans h2

/-- `Λ ≥ 0` eventually, forced by `Λ ≻ ‖·‖`. -/
private theorem c3_Lambda_nonneg (hN : SizeTendsto d) {k : ℕ} [NeZero k] (Λ : ℕ → ℝ)
    (f : ∀ n, Unit × (Fin k → Z2 (d.L n)) → Sizes.SeqΩ d → ℝ) (hf : ∀ n p ω, 0 ≤ f n p ω)
    (hΛ : PerTimeDomAt (Sizes.seqP d) d.size f (fun n _ _ => Λ n)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ Λ n := by
  filter_upwards [hΛ 1 one_pos 1 one_pos, hN.eventually_ge_atTop (2 : ℝ)] with n hn hN2
  by_contra hneg
  push Not at hneg
  have h1 := hn ((), fun _ => 0)
  have hset : {ω | ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * Λ n < f n ((), fun _ => 0) ω} =
      Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have : ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * Λ n < 0 :=
      mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by linarith) _) hneg
    linarith [hf n ((), fun _ => 0) ω]
  rw [hset, measure_univ] at h1
  have h2 : ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact absurd h1 (not_le.2 h2)

/-- The random tensor `𝒜_b(ω) = (F n).eval (E n) (u n) (H_{u_n}(ω)) b` on the common space. -/
private def c3A {k K : ℕ} (F : ∀ n, LocalForm (d.L n) (d.W n) k K) (E u : ℕ → ℝ) (n : ℕ)
    (b : Fin k → Z2 (d.L n)) (ω : Sizes.SeqΩ d) : ℂ :=
  (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b

private theorem c3A_meas {k K : ℕ} (F : ∀ n, LocalForm (d.L n) (d.W n) k K) (E u : ℕ → ℝ)
    (n : ℕ) (b : Fin k → Z2 (d.L n)) : Measurable (c3A d F E u n b) := by
  unfold c3A LocalForm.eval
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun q _ => ?_
  refine measurable_const.mul (Finset.measurable_prod _ fun i _ => ?_)
  exact RBM.Green.measurable_green_apply d n (u n) _ _ _

/-- The one-label form with the coefficients of `F` at the fixed label tuple `b`. -/
private def c3One {L W k K : ℕ} (F : LocalForm L W k K) (b : Fin k → Z2 L) : LocalForm L W 1 K :=
  ⟨fun _ j q => F.coef b j q⟩

private theorem c3One_eval {L W k K : ℕ} [NeZero L] [NeZero W] (F : LocalForm L W k K)
    (b : Fin k → Z2 L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (x : Z2 L) :
    cltY (c3One F b) E u M x = F.eval E u M b := rfl

/-- **The crude bound** (proof of `lem:sum_decay`, `𝒜 = O(N^{C'+2K} η^{-K})`):
`‖𝒜_b(ω)‖ ≤ (K+1) N^{C'} (2N³/c_κ)^K`
for every `ω` (`cltEval_det_le`, applied to the one-label form `c3One`). -/
private theorem c3A_crude {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {k K : ℕ} [NeZero k]
    (F : ∀ n, LocalForm (d.L n) (d.W n) k K) (E u : ℕ → ℝ) {C' : ℝ} (n : ℕ)
    (hE : |E n| ≤ 2 - κ) (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n)
    (hcoef : ∀ b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C')
    (b : Fin k → Z2 (d.L n)) (ω : Sizes.SeqΩ d) :
    ‖c3A d F E u n b ω‖ ≤ ((K : ℝ) + 1) * ((d.size n : ℕ) : ℝ) ^ C' *
      (2 * ((d.size n : ℕ) : ℝ) ^ 3 / cltCk κ) ^ K := by
  have h := cltEval_det_le (d.L n) (d.W n) κ δ (E n) (u n) K (c3One (F n) b) C'
    (Sizes.seqHflow d n (u n) ω) (b 0) hκ hδ hE hR (fun b' j q => hcoef b j q)
    (Sizes.seqHflow_isHermitian d n (u n) ω)
  rw [c3One_eval] at h
  exact h

private theorem c3A_integrable {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {k K : ℕ} [NeZero k]
    (F : ∀ n, LocalForm (d.L n) (d.W n) k K) (E u : ℕ → ℝ) {C' : ℝ} (n : ℕ)
    (hE : |E n| ≤ 2 - κ) (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n)
    (hcoef : ∀ b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C')
    (b : Fin k → Z2 (d.L n)) : Integrable (c3A d F E u n b) (Sizes.seqP d) :=
  Integrable.of_bound (c3A_meas d F E u n b).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun ω => c3A_crude d hκ hδ F E u n hE hR hcoef b ω)

end Seq

/-! ## Part 3: the numeric assembly of the master bound -/

/-- Algebraic split of the right side of `c3_master` after substituting
`M₁ = N_ε Λ + η₀`, `δ_A = 2 N_ε W_m + η₀`, `B₁ = N_ε (W_C ℓ_s S Λ + W_d)`,
`B₂ = N_ε Z_s (W_C ℓ_t ℓ_s S Λ + W_d)` and `Z_s ≤ ϖ w₂ e`, `ϖ⁻¹ ϖ = 1`. -/
private theorem c3_rhs_split {Nε Λ η₀ Wm Wd WC ℓs ℓt S X vi vp w2 e Bw r r' L2 Zs κ1 T2 : ℝ}
    (hNε : 0 ≤ Nε) (hΛ : 0 ≤ Λ) (hη : 0 ≤ η₀) (hWm : 0 ≤ Wm) (hWd : 0 ≤ Wd) (hWC : 0 ≤ WC)
    (hℓs : 0 ≤ ℓs) (hℓt : 0 ≤ ℓt) (hS : 0 ≤ S) (hX : 0 ≤ X) (hvi : 0 ≤ vi) (hvp : 0 ≤ vp)
    (hw2 : 0 ≤ w2) (he : 0 ≤ e) (hBw : 0 ≤ Bw) (hr : 0 ≤ r) (hr' : 0 ≤ r') (hL2 : 0 ≤ L2)
    (hZs0 : 0 ≤ Zs) (hκ1 : 0 ≤ κ1) (hT2 : 0 ≤ T2) (hvivp : vi * vp = 1)
    (hZs : Zs ≤ vp * w2 * e) {k : ℕ} :
    κ1 * ((2 * Nε * Wm + η₀) * r' ^ k + vi * (Nε * (WC * ℓs * (S * Λ) + Wd) +
        Nε * (Zs * (WC * ℓt * ℓs * (S * Λ) + Wd)) +
        L2 * (vp * w2 * (e * X) * (S * (2 * (Nε * Λ + η₀)))))) +
      T2 * (2 * (Nε * Λ + η₀) * (1 * Bw ^ (k - 1)) + (2 * Nε * Wm + η₀) * r ^ k) ≤
    Nε * Λ * (κ1 * (vi * ℓs * S * WC + w2 * e * (ℓt * (ℓs * S)) * WC) +
        2 * κ1 * (L2 * w2 * e * X * S) + 2 * T2 * Bw ^ (k - 1)) +
      Nε * Wm * (2 * (κ1 * r' ^ k + T2 * r ^ k)) +
      Nε * Wd * (κ1 * (vi + w2 * e)) +
      η₀ * (κ1 * r' ^ k + T2 * r ^ k + 2 * κ1 * (L2 * w2 * e * X * S) + 2 * T2 * Bw ^ (k - 1)) := by
  have h1 : Zs * (WC * ℓt * ℓs * (S * Λ) + Wd) ≤
      (vp * w2 * e) * (WC * ℓt * ℓs * (S * Λ) + Wd) :=
    mul_le_mul_of_nonneg_right hZs (by positivity)
  have h2 : κ1 * (vi * (Nε * (Zs * (WC * ℓt * ℓs * (S * Λ) + Wd)))) ≤
      κ1 * (vi * (Nε * ((vp * w2 * e) * (WC * ℓt * ℓs * (S * Λ) + Wd)))) := by
    gcongr
  have h3 : κ1 * (vi * (Nε * ((vp * w2 * e) * (WC * ℓt * ℓs * (S * Λ) + Wd)))) =
      κ1 * (Nε * (w2 * e * (WC * ℓt * ℓs * (S * Λ) + Wd))) := by
    have : vi * vp = 1 := hvivp
    calc κ1 * (vi * (Nε * ((vp * w2 * e) * (WC * ℓt * ℓs * (S * Λ) + Wd))))
        = κ1 * (Nε * ((vi * vp) * (w2 * e * (WC * ℓt * ℓs * (S * Λ) + Wd)))) := by ring
      _ = κ1 * (Nε * (w2 * e * (WC * ℓt * ℓs * (S * Λ) + Wd))) := by rw [this, one_mul]
  have h4 : κ1 * (vi * (L2 * (vp * w2 * (e * X) * (S * (2 * (Nε * Λ + η₀)))))) =
      κ1 * (L2 * (w2 * e * X * S * (2 * (Nε * Λ + η₀)))) := by
    calc κ1 * (vi * (L2 * (vp * w2 * (e * X) * (S * (2 * (Nε * Λ + η₀))))))
        = κ1 * ((vi * vp) * (L2 * (w2 * e * X * S * (2 * (Nε * Λ + η₀))))) := by ring
      _ = κ1 * (L2 * (w2 * e * X * S * (2 * (Nε * Λ + η₀)))) := by rw [hvivp, one_mul]
  have h5 : κ1 * (vi * (Nε * (Zs * (WC * ℓt * ℓs * (S * Λ) + Wd)))) ≤
      κ1 * (Nε * (w2 * e * (WC * ℓt * ℓs * (S * Λ) + Wd))) := h3 ▸ h2
  have hexp : κ1 * ((2 * Nε * Wm + η₀) * r' ^ k + vi * (Nε * (WC * ℓs * (S * Λ) + Wd) +
        Nε * (Zs * (WC * ℓt * ℓs * (S * Λ) + Wd)) +
        L2 * (vp * w2 * (e * X) * (S * (2 * (Nε * Λ + η₀)))))) =
      κ1 * ((2 * Nε * Wm + η₀) * r' ^ k) + κ1 * (vi * (Nε * (WC * ℓs * (S * Λ) + Wd))) +
      κ1 * (vi * (Nε * (Zs * (WC * ℓt * ℓs * (S * Λ) + Wd)))) +
      κ1 * (vi * (L2 * (vp * w2 * (e * X) * (S * (2 * (Nε * Λ + η₀)))))) := by ring
  rw [hexp, h4]
  nlinarith [h5]


/-- `‖∫ f‖ ≤ Λ' + cr · μ{‖f‖ > Λ'}` for `‖f‖ ≤ cr`. -/
private theorem c3_abar_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℂ) (hf : Measurable f) {cr Λ' : ℝ}
    (hcr : ∀ ω, ‖f ω‖ ≤ cr) (hΛ' : 0 ≤ Λ') :
    ‖∫ ω, f ω ∂μ‖ ≤ Λ' + cr * (μ {ω | Λ' < ‖f ω‖}).toReal := by
  have hS : MeasurableSet {ω | Λ' < ‖f ω‖} := measurableSet_lt measurable_const hf.norm
  have h1 : ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm f
  have hint1 : Integrable (fun ω => ‖f ω‖) μ :=
    Integrable.of_bound hf.norm.aestronglyMeasurable cr
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_norm]; exact hcr ω)
  have hint3 : Integrable ({ω | Λ' < ‖f ω‖}.indicator (fun _ => cr)) μ :=
    (integrable_const cr).indicator hS
  have hint2 : Integrable (fun ω => Λ' + {ω | Λ' < ‖f ω‖}.indicator (fun _ => cr) ω) μ :=
    (integrable_const _).add hint3
  have h2 : ∫ ω, ‖f ω‖ ∂μ ≤ ∫ ω, (Λ' + {ω | Λ' < ‖f ω‖}.indicator (fun _ => cr) ω) ∂μ := by
    refine integral_mono hint1 hint2 fun ω => ?_
    by_cases h : Λ' < ‖f ω‖
    · rw [Set.indicator_of_mem (show ω ∈ {ω | Λ' < ‖f ω‖} from h)]
      linarith [hcr ω]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | Λ' < ‖f ω‖} from h)]
      linarith [not_lt.1 h]
  have h3 : ∫ ω, (Λ' + {ω | Λ' < ‖f ω‖}.indicator (fun _ => cr) ω) ∂μ =
      Λ' + cr * (μ {ω | Λ' < ‖f ω‖}).toReal := by
    rw [integral_add (integrable_const _) hint3, integral_const, integral_indicator_const _ hS]
    simp [Measure.real, mul_comm]
  linarith




/-! ## Part 4: sequences bounded by a power of `N` -/

section Poly

variable (d : Sizes)

/-- `f` is eventually non-negative and eventually bounded by a fixed power of `N = size n`. -/
private def PolyB (f : ℕ → ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop, 0 ≤ f n) ∧ ∃ m : ℝ, ∀ᶠ n : ℕ in atTop, f n ≤ ((d.size n : ℕ) : ℝ) ^ m

variable {d}

private theorem PolyB.rpow_size (hN : SizeTendsto d) (p : ℝ) :
    PolyB d (fun n => ((d.size n : ℕ) : ℝ) ^ p) := by
  refine ⟨?_, p, Filter.Eventually.of_forall fun n => le_rfl⟩
  filter_upwards [hN.eventually_ge_atTop (1 : ℝ)] with n hn
  exact Real.rpow_nonneg (by linarith) _

private theorem PolyB.const (hN : SizeTendsto d) {c : ℝ} (hc : 0 ≤ c) :
    PolyB d (fun _ => c) := by
  refine ⟨Filter.Eventually.of_forall fun _ => hc, 1, ?_⟩
  filter_upwards [hN.eventually_ge_atTop c] with n hn
  simpa using hn

private theorem PolyB.mono {f g : ℕ → ℝ} (hg : PolyB d g) (hf0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PolyB d f := by
  obtain ⟨_, m, hm⟩ := hg
  exact ⟨hf0, m, by filter_upwards [hfg, hm] with n h1 h2 using h1.trans h2⟩

private theorem PolyB.add (hN : SizeTendsto d) {f g : ℕ → ℝ} (hf : PolyB d f) (hg : PolyB d g) :
    PolyB d (fun n => f n + g n) := by
  obtain ⟨hf0, m₁, hm₁⟩ := hf
  obtain ⟨hg0, m₂, hm₂⟩ := hg
  refine ⟨by filter_upwards [hf0, hg0] with n h1 h2 using add_nonneg h1 h2, max m₁ m₂ + 1, ?_⟩
  filter_upwards [hm₁, hm₂, hN.eventually_ge_atTop (2 : ℝ)] with n h1 h2 hN2
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have e1 : ((d.size n : ℕ) : ℝ) ^ m₁ ≤ ((d.size n : ℕ) : ℝ) ^ (max m₁ m₂) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have e2 : ((d.size n : ℕ) : ℝ) ^ m₂ ≤ ((d.size n : ℕ) : ℝ) ^ (max m₁ m₂) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
  have hp : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (max m₁ m₂) := Real.rpow_nonneg (by linarith) _
  have e3 : ((d.size n : ℕ) : ℝ) ^ (max m₁ m₂ + 1) =
      ((d.size n : ℕ) : ℝ) ^ (max m₁ m₂) * ((d.size n : ℕ) : ℝ) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  rw [e3]
  nlinarith

private theorem PolyB.mul (hN : SizeTendsto d) {f g : ℕ → ℝ} (hf : PolyB d f)
    (hg : PolyB d g) : PolyB d (fun n => f n * g n) := by
  obtain ⟨hf0, m₁, hm₁⟩ := hf
  obtain ⟨hg0, m₂, hm₂⟩ := hg
  refine ⟨by filter_upwards [hf0, hg0] with n h1 h2 using mul_nonneg h1 h2, m₁ + m₂, ?_⟩
  filter_upwards [hf0, hg0, hm₁, hm₂, hN.eventually_ge_atTop (1 : ℝ)] with n h1 h2 h3 h4 hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  rw [Real.rpow_add hN0]
  exact mul_le_mul h3 h4 h2 (Real.rpow_nonneg hN0.le _)

private theorem PolyB.pow (hN : SizeTendsto d) {f : ℕ → ℝ} (hf : PolyB d f) (m : ℕ) :
    PolyB d (fun n => f n ^ m) := by
  obtain ⟨hf0, m₁, hm₁⟩ := hf
  refine ⟨by filter_upwards [hf0] with n h using pow_nonneg h m, m₁ * m, ?_⟩
  filter_upwards [hf0, hm₁, hN.eventually_ge_atTop (1 : ℝ)] with n h1 h2 hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  calc f n ^ m ≤ (((d.size n : ℕ) : ℝ) ^ m₁) ^ m := pow_le_pow_left₀ h1 h2 m
    _ = ((d.size n : ℕ) : ℝ) ^ (m₁ * m) := by
        rw [← Real.rpow_natCast (((d.size n : ℕ) : ℝ) ^ m₁) m, ← Real.rpow_mul hN0.le]

/-- A `PolyB` sequence has a polynomial bound with non-negative exponent. -/
private theorem PolyB.exists_nonneg (hN : SizeTendsto d) {f : ℕ → ℝ} (hf : PolyB d f) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ᶠ n : ℕ in atTop, f n ≤ ((d.size n : ℕ) : ℝ) ^ m := by
  obtain ⟨_, m, hm⟩ := hf
  refine ⟨max m 0, le_max_right _ _, ?_⟩
  filter_upwards [hm, hN.eventually_ge_atTop (1 : ℝ)] with n h1 hN1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _))

end Poly


/-! ## Part 5: the context and the scale facts along the sequence -/

section Ctx

variable (d : Sizes)

/-- The hypotheses of `SumDecayCase3Prec` (after `intro`), bundled. -/
private structure C3Ctx (κ 𝔠 δ : ℝ) {k K : ℕ} [NeZero k] (C' τ D : ℝ)
    (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) k K) : Prop where
  hκ : 0 < κ
  h𝔠 : 0 < 𝔠
  hδ : 0 < δ
  hk : 2 ≤ k
  hC' : 0 ≤ C'
  hτ : 0 < τ
  hD : 0 < D
  hE : ∀ n, |E n| ≤ 2 - κ
  hs₀ : ∀ n, 0 ≤ s₀ n
  hsu : ∀ n, s₀ n ≤ u n
  hut₀ : ∀ n, u n ≤ t₀ n
  hut : ∀ n, u n ≤ t n
  ht : ∀ n, t n < 1
  hN : SizeTendsto d
  hW : Bandwidth d 𝔠
  hR : RangeCond d δ t
  hLoc : Step2LocalPT d E s₀ t₀
  hDec : Step2DecayPT d E s₀ t₀
  hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ
  hcoef : ∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C'
  hloc : ∀ n, (F n).Local τ (u n)
  hsz : ∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)
  hLD : LabelDecayPT d E u F τ D
  hΛ : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
    (fun n p ω => ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
    (fun n _ _ => Λ n)

variable {d}

/-- The scale facts, eventually: `N ≥ 2`, `1/N ≤ 1 - t`, `N^𝔠 ≤ W`. -/
private def C3Scale (d : Sizes) (𝔠 : ℝ) (t : ℕ → ℝ) (n : ℕ) : Prop :=
  2 ≤ ((d.size n : ℕ) : ℝ) ∧ 1 / ((d.size n : ℕ) : ℝ) ≤ 1 - t n ∧
    ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)

private theorem c3_scale {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ}
    {E s₀ t₀ u t Λ : ℕ → ℝ} {F : ∀ n, LocalForm (d.L n) (d.W n) k K}
    (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : ∀ᶠ n : ℕ in atTop, C3Scale d 𝔠 t n := by
  filter_upwards [hc.hN.eventually_ge_atTop (2 : ℝ), hc.hR, hc.hW] with n h1 h2 h3
  refine ⟨h1, ?_, h3⟩
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have : ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hc.hδ])
  rw [Real.rpow_neg_one] at this
  calc 1 / ((d.size n : ℕ) : ℝ) = ((d.size n : ℕ) : ℝ)⁻¹ := one_div _
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + δ) := this
    _ ≤ 1 - t n := h2

end Ctx


/-! ## Part 6: the sequences of scale quantities and their polynomial bounds -/

section PB

variable (d : Sizes)

private def c3lam (n : ℕ) : ℝ := 1 + Real.log (d.L n : ℝ)

private def c3Kw (τ : ℝ) (n : ℕ) : ℝ := (d.W n : ℝ) ^ τ

private def c3Rn (u t : ℕ → ℝ) (n : ℕ) : ℝ := rhoR (d.L n) (u n) (t n)

private def c3en (u t : ℕ → ℝ) (n : ℕ) : ℝ := c3e (d.L n) (u n) (t n)

private def c3w2n (t : ℕ → ℝ) (n : ℕ) : ℝ := c3w2 (d.L n) (t n)

private def c3vin (u t : ℕ → ℝ) (n : ℕ) : ℝ := (c3vp (d.L n) (u n) (t n))⁻¹

private def c3Sn (k : ℕ) (τ : ℝ) (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  c3SY (d.L n) k (u n) (t n) (ellT (d.L n) (u n) * c3Kw d τ n)

private def c3Bwn (τ : ℝ) (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + (2 * (ellT (d.L n) (u n) * c3Kw d τ n) + 1) ^ 2 * c3en d u t n

private def c3rn (u t : ℕ → ℝ) (n : ℕ) : ℝ := (1 - u n) / (1 - t n)

private def c3rpn (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  (t n - u n) / (1 - t n) + (d.L n : ℝ) ^ 2 * c3en d u t n

private def c3Xn (τ : ℝ) (n : ℕ) : ℝ := Real.exp (-c3Kw d τ n / 20000)

variable {d}

section
variable {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- The basic facts at an index `n` in the scale set. -/
private theorem c3_at (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) {n : ℕ}
    (hn : C3Scale d 𝔠 t n) :
    3 ≤ d.L n ∧ 0 ≤ u n ∧ u n ≤ t n ∧ t n < 1 ∧ 1 ≤ ((d.size n : ℕ) : ℝ) ∧
      (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧ 1 / ((d.size n : ℕ) : ℝ) ≤ 1 - t n ∧
      1 ≤ (d.W n : ℝ) ∧ (d.W n : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 1 ≤ c3Kw d τ n := by
  refine ⟨d.three_le_L n, (hc.hs₀ n).trans (hc.hsu n), hc.hut n, hc.ht n, by linarith [hn.1], ?_,
    hn.2.1, ?_, ?_, ?_⟩
  · have hW : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
    have : (d.size n : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
      unfold Sizes.size; push_cast; ring
    rw [this]
    have hL0 : (0 : ℝ) ≤ (d.L n : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((d.W n : ℝ) * (d.L n : ℝ)), mul_le_mul_of_nonneg_right hW hL0,
      sq_nonneg (d.L n : ℝ)]
  · exact_mod_cast d.W_pos n
  · have h1 : d.W n ≤ d.size n := by
      have := c3_L_le_size d n
      unfold Sizes.size
      calc d.W n = d.W n * 1 := (mul_one _).symm
        _ ≤ d.W n * d.L n := Nat.mul_le_mul_left _ (by have := d.three_le_L n; omega)
        _ ≤ (d.W n * d.L n) * (d.W n * d.L n) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))
        _ = (d.W n * d.L n) ^ 2 := (sq _).symm
    exact_mod_cast h1
  · unfold c3Kw
    exact Real.one_le_rpow (by exact_mod_cast d.W_pos n) hc.hτ.le

end


private theorem c3_R_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) {Nn : ℝ} (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) : rhoR L s t ≤ Nn := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hm := c3_mt_ge hL ht hN1 h1t
  have hm0 := KernelExpand_min_one_pos' hL ht
  have hN0 : 0 < Nn := by linarith
  rw [KernelExpand_rhoR_eq hs1 ht, div_le_iff₀ hm0]
  have h1 : 1 ≤ Nn * min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
    calc (1 : ℝ) = Nn * (1 / Nn) := by field_simp
      _ ≤ Nn * min 1 ((L : ℝ) ^ 2 * (1 - t)) := mul_le_mul_of_nonneg_left hm hN0.le
  exact (min_le_left _ _).trans h1

private theorem c3_qm_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    c3q L s t * min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ rhoR L s t := by
  have hq := c3q_le hL hst ht
  have hq0 := c3q_nonneg hL hst ht
  calc c3q L s t * min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤ c3q L s t * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hq0
    _ ≤ rhoR L s t := by linarith

section PB2

variable {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

private theorem pb_lam (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3lam d) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => ?_)
  · unfold c3lam; linarith [c3_lam_one (d.L n)]
  · unfold c3lam
    rw [Real.rpow_one]
    have hL : (0 : ℝ) < (d.L n : ℝ) := by exact_mod_cast (by have := d.three_le_L n; omega)
    have := Real.log_le_sub_one_of_pos hL
    have h2 : (d.L n : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast c3_L_le_size d n
    linarith

private theorem pb_Kw (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3Kw d τ) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN τ) (Filter.Eventually.of_forall fun n => ?_) ?_
  · unfold c3Kw; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨-, -, -, -, -, -, -, hW1, hWN, -⟩ := c3_at hc hn
    unfold c3Kw
    exact Real.rpow_le_rpow (by linarith) hWN hc.hτ.le

private theorem pb_ell (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (fun n => ellT (d.L n) (u n)) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    exact (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1.le
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    have h1 := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).2
    have h2 : (d.L n : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast c3_L_le_size d n
    linarith

private theorem pb_R (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3Rn d u t) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    have := KernelExpand_one_le_rhoR hL hut htl
    unfold c3Rn
    linarith
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    exact c3_R_le hL hu0 hut htl hN1 h1t


private theorem pb_P (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (fun n => derivativePrefactor (10 ^ 14) (d.L n)) := by
  have h := ((PolyB.const hc.hN (by norm_num : (0 : ℝ) ≤ 8 * 10 ^ 14)).add hc.hN
    ((PolyB.const hc.hN (by norm_num : (0 : ℝ) ≤ 720)).mul hc.hN (pb_lam hc)))
  refine PolyB.mono h (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => le_of_eq ?_)
  · have := c3_P_nonneg (d.L n); exact this
  · unfold derivativePrefactor c3lam; ring

private theorem pb_e (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3en d u t) := by
  have h := ((PolyB.const hc.hN (by unfold cProp5; norm_num : (0 : ℝ) ≤ 2 * cProp5)).mul hc.hN
    (pb_lam hc)).mul hc.hN (PolyB.rpow_size hc.hN 1)
  refine PolyB.mono h ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    exact c3e_nonneg hL hut htl
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    exact c3_e_le hL hut htl hu0 hN1 h1t

private theorem pb_w2 (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3w2n d t) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    exact (c3w2_pos hL htl).le
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    exact c3_w2_le hL hu0 hut htl hN1 h1t

private theorem pb_vi (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3vin d u t) := by
  refine PolyB.mono (pb_R hc) ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    exact (inv_pos.2 (c3vp_pos hL hut htl)).le
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    exact c3_vp_inv_le hL hu0 hut htl

private theorem pb_L2 (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (fun n => (d.L n : ℝ) ^ 2) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) (Filter.Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [c3_scale hc] with n hn
  obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
  rw [Real.rpow_one]
  exact hL2

private theorem pb_r (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3rn u t) := by
  refine PolyB.mono (PolyB.rpow_size hc.hN 1) ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, -⟩ := c3_at hc hn
    have h0 : 0 < 1 - t n := by linarith
    unfold c3rn
    exact div_nonneg (by linarith) h0.le
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    exact c3_r_le hut htl hN1 h1t hu0

private theorem pb_rp (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3rpn d u t) := by
  have h := ((PolyB.const hc.hN (by unfold cProp5; norm_num : (0 : ℝ) ≤ 1 + 2 * cProp5)).mul
    hc.hN (pb_lam hc)).mul hc.hN ((PolyB.rpow_size hc.hN 1).pow hc.hN 2)
  refine PolyB.mono h ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    have h0 : 0 < 1 - t n := by linarith
    have he0 := c3e_nonneg hL hut htl
    unfold c3rpn c3en
    have : 0 ≤ (t n - u n) / (1 - t n) := div_nonneg (by linarith) h0.le
    positivity
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    rw [Real.rpow_one]
    exact c3_rprime_le hL hut htl hu0 hN1 hL2 h1t

private theorem pb_Bw (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (c3Bwn d τ u t) := by
  have h := (((PolyB.const hc.hN (by unfold cProp5; norm_num : (0 : ℝ) ≤ 1 + 18 * cProp5)).mul
    hc.hN (pb_lam hc)).mul hc.hN ((pb_Kw hc).pow hc.hN 2)).mul hc.hN (pb_R hc)
  refine PolyB.mono h ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    have he0 := c3e_nonneg hL hut htl
    unfold c3Bwn c3en
    positivity
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    exact c3_Bw_le hL hu0 hut htl hKw1

private theorem pb_S (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3Sn d k τ u t) := by
  have h1 := ((PolyB.const hc.hN (by norm_num : (0 : ℝ) ≤ 18)).mul hc.hN (pb_P hc)).mul hc.hN
    ((pb_ell hc).mul hc.hN ((pb_Kw hc).pow hc.hN 3))
  have h2 := h1.mul hc.hN (pb_R hc)
  have h3 := h2.mul hc.hN
    ((((PolyB.const hc.hN (by unfold cProp5; norm_num : (0 : ℝ) ≤ 9 * (2 * cProp5))).mul hc.hN
      (pb_lam hc)).mul hc.hN ((pb_Kw hc).pow hc.hN 2)).mul hc.hN (pb_R hc) |>.pow hc.hN (k - 2))
  refine PolyB.mono h3 ?_ ?_
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    have hρ0 : 0 ≤ ellT (d.L n) (u n) * c3Kw d τ n := by
      have := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1
      positivity
    exact c3SY_nonneg hL hut htl hρ0
  · filter_upwards [c3_scale hc] with n hn
    obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
    have hS := c3_SY_le hL hc.hk hu0 hut htl hKw1
    have hqm := c3_qm_le hL hut htl
    have hR1 := KernelExpand_one_le_rhoR hL hut htl
    have hP := c3_P_nonneg (d.L n)
    have hℓ := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1
    have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
    have hlam := c3_lam_one (d.L n)
    unfold c3Sn
    refine hS.trans ?_
    have hY : 0 ≤ (9 * (2 * cProp5 * (1 + Real.log (d.L n : ℝ))) * c3Kw d τ n ^ 2 *
        rhoR (d.L n) (u n) (t n)) ^ (k - 2) := by apply pow_nonneg; positivity
    have hA : 0 ≤ 18 * derivativePrefactor (10 ^ 14) (d.L n) *
        (ellT (d.L n) (u n) * c3Kw d τ n ^ 3) := by positivity
    calc 18 * derivativePrefactor (10 ^ 14) (d.L n) * (ellT (d.L n) (u n) * c3Kw d τ n ^ 3) *
          (c3q (d.L n) (u n) (t n) * min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - t n))) *
          (9 * (2 * cProp5 * (1 + Real.log (d.L n : ℝ))) * c3Kw d τ n ^ 2 *
            rhoR (d.L n) (u n) (t n)) ^ (k - 2)
        ≤ 18 * derivativePrefactor (10 ^ 14) (d.L n) * (ellT (d.L n) (u n) * c3Kw d τ n ^ 3) *
          rhoR (d.L n) (u n) (t n) *
          (9 * (2 * cProp5 * (1 + Real.log (d.L n : ℝ))) * c3Kw d τ n ^ 2 *
            rhoR (d.L n) (u n) (t n)) ^ (k - 2) := by
          gcongr
      _ = _ := by unfold c3lam c3Rn; ring


private theorem pb_X (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3Xn d τ) := by
  refine PolyB.mono (PolyB.const hc.hN (by norm_num : (0 : ℝ) ≤ 1)) ?_ ?_
  · exact Filter.Eventually.of_forall fun n => (Real.exp_pos _).le
  · refine Filter.Eventually.of_forall fun n => ?_
    unfold c3Xn c3Kw
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (d.W n : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 20000)]

/-- The coefficient of `η₀` in the right side of `c3_rhs_split`. -/
private def c3Teta (d : Sizes) (k : ℕ) (τ : ℝ) (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * c3rpn d u t n ^ k + 2 ^ k * c3rn u t n ^ k +
    2 * ((k - 1 : ℕ) : ℝ) * ((d.L n : ℝ) ^ 2 * c3w2n d t n * c3en d u t n * c3Xn d τ n *
      c3Sn d k τ u t n) + 2 * 2 ^ k * c3Bwn d τ u t n ^ (k - 1)

/-- The coefficient of `N_ε W_d` (the `clt-lemma` error terms). -/
private def c3TD (d : Sizes) (k : ℕ) (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * (c3vin d u t n + c3w2n d t n * c3en d u t n)

/-- The tail coefficient without the factor `exp(-K_w/20000)`. -/
private def c3Qt (d : Sizes) (k : ℕ) (τ : ℝ) (u t : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * ((k - 1 : ℕ) : ℝ) * ((d.L n : ℝ) ^ 2 * c3w2n d t n * c3en d u t n * c3Sn d k τ u t n)

/-- The crude bound of proof of `lem:sum_decay`. -/
private def c3crude (d : Sizes) (κ : ℝ) (K : ℕ) (C' : ℝ) (n : ℕ) : ℝ :=
  ((K : ℝ) + 1) * ((d.size n : ℕ) : ℝ) ^ C' * (2 * ((d.size n : ℕ) : ℝ) ^ 3 / cltCk κ) ^ K

private theorem pb_crude (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (c3crude d κ K C') := by
  have hck : 0 < cltCk κ := by
    have := hc.hκ
    have h1 : κ ≤ 2 := by
      have := abs_nonneg (E 0); have := hc.hE 0; linarith
    unfold cltCk
    have : 0 < κ * (4 - κ) := mul_pos hc.hκ (by linarith)
    positivity
  have h := ((PolyB.const hc.hN (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)).mul hc.hN
    (PolyB.rpow_size hc.hN C')).mul hc.hN
    (((PolyB.const hc.hN (by positivity : (0 : ℝ) ≤ 2 / cltCk κ)).mul hc.hN
      ((PolyB.rpow_size hc.hN 1).pow hc.hN 3)).pow hc.hN K)
  refine PolyB.mono h ?_ ?_
  · filter_upwards [hc.hN.eventually_ge_atTop (1 : ℝ)] with n hn
    unfold c3crude
    have : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
    positivity
  · refine Filter.Eventually.of_forall fun n => le_of_eq ?_
    unfold c3crude
    rw [Real.rpow_one]
    congr 2
    ring

private theorem pb_Teta (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (c3Teta d k τ u t) := by
  have hN := hc.hN
  have hk1 : PolyB d (fun _ => ((k - 1 : ℕ) : ℝ)) := PolyB.const hN (Nat.cast_nonneg _)
  have h2k : PolyB d (fun _ => (2 : ℝ) ^ k) := PolyB.const hN (by positivity)
  have hA : PolyB d (fun n => ((k - 1 : ℕ) : ℝ) * c3rpn d u t n ^ k) :=
    hk1.mul hN ((pb_rp hc).pow hN k)
  have hB : PolyB d (fun n => (2 : ℝ) ^ k * c3rn u t n ^ k) := h2k.mul hN ((pb_r hc).pow hN k)
  have hC : PolyB d (fun n => 2 * ((k - 1 : ℕ) : ℝ) * ((d.L n : ℝ) ^ 2 * c3w2n d t n *
      c3en d u t n * c3Xn d τ n * c3Sn d k τ u t n)) :=
    (PolyB.const hN (by positivity : (0 : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ))).mul hN
      (((((pb_L2 hc).mul hN (pb_w2 hc)).mul hN (pb_e hc)).mul hN (pb_X hc)).mul hN (pb_S hc))
  have hD : PolyB d (fun n => 2 * (2 : ℝ) ^ k * c3Bwn d τ u t n ^ (k - 1)) :=
    (PolyB.const hN (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ k)).mul hN ((pb_Bw hc).pow hN _)
  exact ((hA.add hN hB).add hN hC).add hN hD

private theorem pb_TD (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) : PolyB d (c3TD d k u t) := by
  have hN := hc.hN
  exact (PolyB.const hN (Nat.cast_nonneg _)).mul hN ((pb_vi hc).add hN ((pb_w2 hc).mul hN (pb_e hc)))

private theorem pb_Qt (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    PolyB d (c3Qt d k τ u t) := by
  have hN := hc.hN
  exact (PolyB.const hN (by positivity : (0 : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ))).mul hN
    ((((pb_L2 hc).mul hN (pb_w2 hc)).mul hN (pb_e hc)).mul hN (pb_S hc))

/-- `N^m exp(-W^τ/20000) ≤ 1` eventually (`N ≤ W^{1/𝔠}`, `exp` beats every power of `W^τ`). -/
private theorem c3_poly_exp (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) {m : ℝ} (hm : 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ m * c3Xn d τ n ≤ 1 := by
  have hWt : Tendsto (fun n : ℕ => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop.2 fun X => c3_W_large d hc.hN hc.h𝔠 hc.hW X
  have hKw : Tendsto (fun n : ℕ => c3Kw d τ n) atTop atTop :=
    (tendsto_rpow_atTop hc.hτ).comp hWt
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m / 𝔠 / τ) (1 / 20000)
    (by norm_num)).comp hKw
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hc.hW, hc.hN.eventually_ge_atTop (1 : ℝ)] with n h1 h2 hN1
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) := Nat.cast_nonneg _
  have e1 : ((d.size n : ℕ) : ℝ) ^ m ≤ (d.W n : ℝ) ^ (m / 𝔠) := by
    have : ((d.size n : ℕ) : ℝ) ^ m = (((d.size n : ℕ) : ℝ) ^ 𝔠) ^ (m / 𝔠) := by
      rw [← Real.rpow_mul hN0, mul_div_cancel₀ _ hc.h𝔠.ne']
    rw [this]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h2 (by have := hc.h𝔠; positivity)
  have e2 : (d.W n : ℝ) ^ (m / 𝔠) = (c3Kw d τ n) ^ (m / 𝔠 / τ) := by
    unfold c3Kw
    rw [← Real.rpow_mul hW0, mul_div_cancel₀ _ hc.hτ.ne']
  have hX : c3Xn d τ n = Real.exp (-(1 / 20000) * c3Kw d τ n) := by
    unfold c3Xn; congr 1; ring
  have hX0 : 0 ≤ c3Xn d τ n := (Real.exp_pos _).le
  calc ((d.size n : ℕ) : ℝ) ^ m * c3Xn d τ n ≤ (c3Kw d τ n) ^ (m / 𝔠 / τ) * c3Xn d τ n := by
        rw [← e2]; exact mul_le_mul_of_nonneg_right e1 hX0
    _ = (c3Kw d τ n) ^ (m / 𝔠 / τ) * Real.exp (-(1 / 20000) * c3Kw d τ n) := by rw [hX]
    _ ≤ 1 := h1.le

/-- The polynomial exponents used to choose `C'_Y`, `D_c`, `D_p`. -/
private theorem c3_consts (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    ∃ cY mc m0 mq : ℝ, 0 ≤ cY ∧ 0 ≤ mc ∧ 0 ≤ m0 ∧ 0 ≤ mq ∧
      (∀ᶠ n : ℕ in atTop, c3Sn d k τ u t n ≤ ((d.size n : ℕ) : ℝ) ^ cY) ∧
      (∀ᶠ n : ℕ in atTop, c3TD d k u t n ≤ ((d.size n : ℕ) : ℝ) ^ mc) ∧
      (∀ᶠ n : ℕ in atTop, c3Teta d k τ u t n * c3crude d κ K C' n ≤ ((d.size n : ℕ) : ℝ) ^ m0) ∧
      (∀ᶠ n : ℕ in atTop, c3Qt d k τ u t n ≤ ((d.size n : ℕ) : ℝ) ^ mq) := by
  obtain ⟨cY, hcY, h1⟩ := (pb_S hc).exists_nonneg hc.hN
  obtain ⟨mc, hmc, h2⟩ := (pb_TD hc).exists_nonneg hc.hN
  obtain ⟨m0, hm0, h3⟩ := ((pb_Teta hc).mul hc.hN (pb_crude hc)).exists_nonneg hc.hN
  obtain ⟨mq, hmq, h4⟩ := (pb_Qt hc).exists_nonneg hc.hN
  exact ⟨cY, mc, m0, mq, hcY, hmc, hm0, hmq, h1, h2, h3, h4⟩

end PB2

end PB


/-! ## Part 7: the four coefficient bounds -/

section Coef

/-- `N^m ≤ W^{m/𝔠}` from `N^𝔠 ≤ W`. -/
private theorem c3_pow_le {N W 𝔠 : ℝ} (hN : 0 ≤ N) (h𝔠 : 0 < 𝔠) (hW : N ^ 𝔠 ≤ W) (m : ℕ) :
    N ^ m ≤ W ^ ((m : ℝ) / 𝔠) := by
  have h1 : N ^ m = (N ^ 𝔠) ^ ((m : ℝ) / 𝔠) := by
    rw [← Real.rpow_mul hN, mul_div_cancel₀ _ h𝔠.ne', Real.rpow_natCast]
  rw [h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hN _) hW (by positivity)

/-- `(W^τ)^m W^{2|c|τ} ≤ W^{Ck τ}` when `m + 2|c| ≤ Ck`. -/
private theorem c3_pow_exp {Wr τ : ℝ} (hW1 : 1 ≤ Wr) (hτ : 0 < τ) (m : ℕ) (cC Ckv : ℝ)
    (hCk : (m : ℝ) + 2 * |cC| ≤ Ckv) :
    (Wr ^ τ) ^ m * Wr ^ (2 * |cC| * τ) ≤ Wr ^ (Ckv * τ) := by
  have hW0 : 0 < Wr := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]
  apply Real.rpow_le_rpow_of_exponent_le hW1
  nlinarith

/-- `W^{cC·2τ} ≤ W^{2|cC|τ}`. -/
private theorem c3_WC_le {Wr τ : ℝ} (hW1 : 1 ≤ Wr) (hτ : 0 < τ) (cC : ℝ) :
    Wr ^ (cC * (2 * τ)) ≤ Wr ^ (2 * |cC| * τ) := by
  apply Real.rpow_le_rpow_of_exponent_le hW1
  nlinarith [le_abs_self cC]

/-- `cPrec 𝔠 k ≥ 2k + 4k/𝔠` etc.: the exponent room in `cCase3`. -/
private theorem c3_Ck_room {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (cC : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2 * (k : ℝ) + 2 * |cC|) ≤ cCase3 𝔠 cC k ∧ (2 * (k : ℝ)) / 𝔠 ≤ cCase3 𝔠 cC k := by
  unfold cCase3 cPrec
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 ≤ 4 * (k : ℝ) / 𝔠 := by positivity
  have h2 : 2 * (k : ℝ) / 𝔠 ≤ 4 * (k : ℝ) / 𝔠 :=
    div_le_div_of_nonneg_right (by linarith) h𝔠.le
  constructor <;> linarith [abs_nonneg cC]


private def c3cB : ℝ := 1 + 18 * cProp5

private def c3cP : ℝ := 8 * 10 ^ 14 + 720

/-- The constant of the `N_ε Λ` coefficient. -/
private def c3A1 (k : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * (18 * c3cP * (18 * cProp5) ^ (k - 2) * (1 + 2 * cProp5)) + 1 +
    2 * 2 ^ k * c3cB ^ (k - 1)

private theorem c3_P_le (L : ℕ) : derivativePrefactor (10 ^ 14) L ≤ c3cP * (1 + Real.log L) := by
  have := c3_lam_one L
  unfold derivativePrefactor c3cP
  nlinarith

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem c3_lam_pow_facts {lam : ℝ} {k : ℕ} (hk : 2 ≤ k) (hlam : 1 ≤ lam) :
    lam ^ (k - 2) * lam = lam ^ (k - 1) ∧ lam ^ (k - 1) ≤ lam ^ k ∧
      lam ^ (k - 2) * lam * lam = lam ^ k := by
  refine ⟨?_, pow_le_pow_right₀ hlam (Nat.sub_le k 1), ?_⟩
  · rw [← pow_succ]; congr 1; omega
  · rw [← pow_succ, ← pow_succ]; congr 1; omega

/-- Piece 1 of (B-Λ): the `Z` term. -/
private theorem c3_TLam_p1 {vi ℓs S WC P lam R Kw Wm Wc2 c5 cP : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hvi : 0 ≤ vi) (hWC0 : 0 ≤ WC) (hP0 : 0 ≤ P) (hlam : 1 ≤ lam) (hR : 1 ≤ R) (hKw : 1 ≤ Kw)
    (hWm : 1 ≤ Wm) (hc5 : 0 ≤ c5)
    (hQ1 : vi * (ℓs * S) ≤ 18 * P * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k)
    (hPl : P ≤ cP * lam) (hWC : WC ≤ Wc2) (hpe1 : Kw ^ (2 * k - 1) * Wc2 ≤ Wm) :
    vi * ℓs * S * WC ≤ 18 * cP * (18 * c5) ^ (k - 2) * lam ^ (k - 1) * (Wm * R ^ k) := by
  have hlk := (c3_lam_pow_facts hk hlam).1
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hKw0 : 0 ≤ Kw := by linarith
  have hWm0 : 0 ≤ Wm := by linarith
  have hY : (18 * c5 * lam) ^ (k - 2) = (18 * c5) ^ (k - 2) * lam ^ (k - 2) := by rw [mul_pow]
  have hb0 : 0 ≤ 18 * P * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k := by positivity
  have hYY : 0 ≤ 18 * P * (18 * c5 * lam) ^ (k - 2) * R ^ k := by positivity
  calc vi * ℓs * S * WC = (vi * (ℓs * S)) * WC := by ring
    _ ≤ (18 * P * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k) * Wc2 :=
        mul_le_mul hQ1 hWC hWC0 hb0
    _ = 18 * P * (18 * c5 * lam) ^ (k - 2) * R ^ k * (Kw ^ (2 * k - 1) * Wc2) := by ring
    _ ≤ 18 * P * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm :=
        mul_le_mul_of_nonneg_left hpe1 hYY
    _ ≤ 18 * (cP * lam) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm := by
        have h1 : 18 * P ≤ 18 * (cP * lam) := by linarith
        have h2 : 0 ≤ (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm := by positivity
        calc 18 * P * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm
            = 18 * P * ((18 * c5 * lam) ^ (k - 2) * R ^ k * Wm) := by ring
          _ ≤ 18 * (cP * lam) * ((18 * c5 * lam) ^ (k - 2) * R ^ k * Wm) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = 18 * (cP * lam) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm := by ring
    _ = 18 * cP * (18 * c5) ^ (k - 2) * (lam ^ (k - 2) * lam) * (Wm * R ^ k) := by
        rw [hY]; ring
    _ = 18 * cP * (18 * c5) ^ (k - 2) * lam ^ (k - 1) * (Wm * R ^ k) := by rw [hlk]

/-- Piece 2 of (B-Λ): the `Z̃` term. -/
private theorem c3_TLam_p2 {w2 e ℓs ℓt S WC P lam R Kw Wm Wc2 c5 cP : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hWC0 : 0 ≤ WC) (hP0 : 0 ≤ P) (hlam : 1 ≤ lam) (hR : 1 ≤ R) (hKw : 1 ≤ Kw)
    (hWm : 1 ≤ Wm) (hc5 : 0 ≤ c5)
    (hQ2 : w2 * e * (ℓt * (ℓs * S)) ≤
      (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k)
    (hPl : P ≤ cP * lam) (hWC : WC ≤ Wc2) (hpe1 : Kw ^ (2 * k - 1) * Wc2 ≤ Wm) :
    w2 * e * (ℓt * (ℓs * S)) * WC ≤
      18 * cP * (18 * c5) ^ (k - 2) * (2 * c5 * lam ^ k) * (Wm * R ^ k) := by
  have hlk2 := (c3_lam_pow_facts hk hlam).2.2
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hKw0 : 0 ≤ Kw := by linarith
  have hWm0 : 0 ≤ Wm := by linarith
  have hY : (18 * c5 * lam) ^ (k - 2) = (18 * c5) ^ (k - 2) * lam ^ (k - 2) := by rw [mul_pow]
  have hb0 : 0 ≤ (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) *
      R ^ k := by positivity
  have hYY : 0 ≤ (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * R ^ k := by positivity
  calc w2 * e * (ℓt * (ℓs * S)) * WC
      ≤ ((2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k) *
          Wc2 := mul_le_mul hQ2 hWC hWC0 hb0
    _ = (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * R ^ k *
          (Kw ^ (2 * k - 1) * Wc2) := by ring
    _ ≤ (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm :=
        mul_le_mul_of_nonneg_left hpe1 hYY
    _ ≤ (2 * c5 * lam) * (18 * (cP * lam)) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm := by
        have h1 : 18 * P ≤ 18 * (cP * lam) := by linarith
        have h2 : 0 ≤ (2 * c5 * lam) * ((18 * c5 * lam) ^ (k - 2) * R ^ k * Wm) := by positivity
        calc (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm
            = (18 * P) * ((2 * c5 * lam) * ((18 * c5 * lam) ^ (k - 2) * R ^ k * Wm)) := by ring
          _ ≤ (18 * (cP * lam)) * ((2 * c5 * lam) * ((18 * c5 * lam) ^ (k - 2) * R ^ k * Wm)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (2 * c5 * lam) * (18 * (cP * lam)) * (18 * c5 * lam) ^ (k - 2) * R ^ k * Wm := by
              ring
    _ = 18 * cP * (18 * c5) ^ (k - 2) * (2 * c5 * (lam ^ (k - 2) * lam * lam)) *
          (Wm * R ^ k) := by rw [hY]; ring
    _ = 18 * cP * (18 * c5) ^ (k - 2) * (2 * c5 * lam ^ k) * (Wm * R ^ k) := by rw [hlk2]

/-- Piece 4 of (B-Λ): the `A ≠ ∅` window terms. -/
private theorem c3_TLam_p4 {Bw lam R Kw Wm cB : ℝ} {k : ℕ} (hk : 2 ≤ k) (hBw0 : 0 ≤ Bw)
    (hlam : 1 ≤ lam) (hR : 1 ≤ R) (hKw : 1 ≤ Kw) (hWm : 1 ≤ Wm) (hcB : 0 ≤ cB)
    (hpe2 : Kw ^ (2 * (k - 1)) ≤ Wm) (hBw : Bw ≤ cB * lam * Kw ^ 2 * R) :
    2 * 2 ^ k * Bw ^ (k - 1) ≤ 2 * 2 ^ k * cB ^ (k - 1) * lam ^ k * (Wm * R ^ k) := by
  have hlk1 := (c3_lam_pow_facts hk hlam).2.1
  have hRk : R ^ (k - 1) ≤ R ^ k := pow_le_pow_right₀ hR (Nat.sub_le k 1)
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hKw0 : 0 ≤ Kw := by linarith
  have h1 : Bw ^ (k - 1) ≤ (cB * lam * Kw ^ 2 * R) ^ (k - 1) := pow_le_pow_left₀ hBw0 hBw _
  have h2 : (cB * lam * Kw ^ 2 * R) ^ (k - 1) =
      cB ^ (k - 1) * lam ^ (k - 1) * Kw ^ (2 * (k - 1)) * R ^ (k - 1) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul]
  have h3 : cB ^ (k - 1) * lam ^ (k - 1) * Kw ^ (2 * (k - 1)) * R ^ (k - 1) ≤
      cB ^ (k - 1) * lam ^ k * Wm * R ^ k := by
    have hcB1 : 0 ≤ cB ^ (k - 1) := by positivity
    have hK0 : 0 ≤ Kw ^ (2 * (k - 1)) := by positivity
    have hl0 : 0 ≤ lam ^ (k - 1) := by positivity
    have hR1' : 0 ≤ R ^ (k - 1) := by positivity
    calc cB ^ (k - 1) * lam ^ (k - 1) * Kw ^ (2 * (k - 1)) * R ^ (k - 1)
        ≤ cB ^ (k - 1) * lam ^ k * Kw ^ (2 * (k - 1)) * R ^ (k - 1) := by
          have : cB ^ (k - 1) * lam ^ (k - 1) ≤ cB ^ (k - 1) * lam ^ k :=
            mul_le_mul_of_nonneg_left hlk1 hcB1
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hK0) hR1'
      _ ≤ cB ^ (k - 1) * lam ^ k * Wm * R ^ (k - 1) := by
          have : 0 ≤ cB ^ (k - 1) * lam ^ k := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpe2 this) hR1'
      _ ≤ cB ^ (k - 1) * lam ^ k * Wm * R ^ k := by
          have : 0 ≤ cB ^ (k - 1) * lam ^ k * Wm := by positivity
          exact mul_le_mul_of_nonneg_left hRk this
  calc 2 * 2 ^ k * Bw ^ (k - 1) ≤ 2 * 2 ^ k * (cB ^ (k - 1) * lam ^ k * Wm * R ^ k) := by
        have h4 : Bw ^ (k - 1) ≤ cB ^ (k - 1) * lam ^ k * Wm * R ^ k := by
          rw [h2] at h1; exact h1.trans h3
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * 2 ^ k * cB ^ (k - 1) * lam ^ k * (Wm * R ^ k) := by ring

/-- Abstract form of (B-Λ). -/
private theorem c3_TLam_abs {κ1 vi ℓs ℓt S WC w2 e L2 X Bw P lam R Kw Wm Wc2 c5 cP cB : ℝ}
    {k : ℕ} (hk : 2 ≤ k) (hκ1 : 0 ≤ κ1) (hvi : 0 ≤ vi) (hWC0 : 0 ≤ WC) (hBw0 : 0 ≤ Bw)
    (hP0 : 0 ≤ P) (hlam : 1 ≤ lam) (hR : 1 ≤ R) (hKw : 1 ≤ Kw) (hWm : 1 ≤ Wm)
    (hc5 : 0 ≤ c5) (hcP : 0 ≤ cP) (hcB : 0 ≤ cB)
    (hQ1 : vi * (ℓs * S) ≤ 18 * P * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k)
    (hQ2 : w2 * e * (ℓt * (ℓs * S)) ≤
      (2 * c5 * lam) * (18 * P) * (18 * c5 * lam) ^ (k - 2) * Kw ^ (2 * k - 1) * R ^ k)
    (hPl : P ≤ cP * lam) (hWC : WC ≤ Wc2) (hpe1 : Kw ^ (2 * k - 1) * Wc2 ≤ Wm)
    (hpe2 : Kw ^ (2 * (k - 1)) ≤ Wm) (hBw : Bw ≤ cB * lam * Kw ^ 2 * R)
    (hQ : 2 * κ1 * (L2 * w2 * e * X * S) ≤ 1) :
    κ1 * (vi * ℓs * S * WC + w2 * e * (ℓt * (ℓs * S)) * WC) + 2 * κ1 * (L2 * w2 * e * X * S) +
        2 * 2 ^ k * Bw ^ (k - 1) ≤
      (κ1 * (18 * cP * (18 * c5) ^ (k - 2) * (1 + 2 * c5)) + 1 + 2 * 2 ^ k * cB ^ (k - 1)) *
        lam ^ k * (Wm * R ^ k) := by
  have hlk1 := (c3_lam_pow_facts hk hlam).2.1
  have hlam0 : 0 ≤ lam := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hWm0 : 0 ≤ Wm := by linarith
  have hlk0 : 1 ≤ lam ^ k := one_le_pow₀ hlam
  have hRk0 : 1 ≤ R ^ k := one_le_pow₀ hR
  have hWR : 1 ≤ Wm * R ^ k := one_le_mul_of_one_le_of_one_le hWm hRk0
  have hWR0 : 0 ≤ Wm * R ^ k := by linarith
  have hA : 0 ≤ 18 * cP * (18 * c5) ^ (k - 2) := by positivity
  have p1 := c3_TLam_p1 hk hvi hWC0 hP0 hlam hR hKw hWm hc5 hQ1 hPl hWC hpe1
  have p2 := c3_TLam_p2 (w2 := w2) (e := e) (ℓs := ℓs) (ℓt := ℓt) (S := S) hk hWC0 hP0 hlam hR
    hKw hWm hc5 hQ2 hPl hWC hpe1
  have p4 := c3_TLam_p4 hk hBw0 hlam hR hKw hWm hcB hpe2 hBw
  have p3 : 2 * κ1 * (L2 * w2 * e * X * S) ≤ lam ^ k * (Wm * R ^ k) := by
    have : 1 ≤ lam ^ k * (Wm * R ^ k) := one_le_mul_of_one_le_of_one_le hlk0 hWR
    linarith
  have hsum : 18 * cP * (18 * c5) ^ (k - 2) * lam ^ (k - 1) * (Wm * R ^ k) +
      18 * cP * (18 * c5) ^ (k - 2) * (2 * c5 * lam ^ k) * (Wm * R ^ k) ≤
      18 * cP * (18 * c5) ^ (k - 2) * (1 + 2 * c5) * lam ^ k * (Wm * R ^ k) := by
    have h1 : 18 * cP * (18 * c5) ^ (k - 2) * lam ^ (k - 1) * (Wm * R ^ k) ≤
        18 * cP * (18 * c5) ^ (k - 2) * lam ^ k * (Wm * R ^ k) := by
      have := mul_le_mul_of_nonneg_left hlk1 hA
      exact mul_le_mul_of_nonneg_right this hWR0
    calc _ ≤ 18 * cP * (18 * c5) ^ (k - 2) * lam ^ k * (Wm * R ^ k) +
          18 * cP * (18 * c5) ^ (k - 2) * (2 * c5 * lam ^ k) * (Wm * R ^ k) := by linarith
      _ = _ := by ring
  have h5 := mul_le_mul_of_nonneg_left (add_le_add p1 p2) hκ1
  calc κ1 * (vi * ℓs * S * WC + w2 * e * (ℓt * (ℓs * S)) * WC) + 2 * κ1 * (L2 * w2 * e * X * S) +
        2 * 2 ^ k * Bw ^ (k - 1)
      ≤ κ1 * (18 * cP * (18 * c5) ^ (k - 2) * (1 + 2 * c5) * lam ^ k * (Wm * R ^ k)) +
        lam ^ k * (Wm * R ^ k) + 2 * 2 ^ k * cB ^ (k - 1) * lam ^ k * (Wm * R ^ k) := by
        have := mul_le_mul_of_nonneg_left hsum hκ1
        nlinarith [this, h5, p3, p4]
    _ = _ := by ring


/-- **(B-Λ)**, concrete: the coefficient of `N_ε Λ` in `c3_rhs_split` is
`≤ c_{A1} (1 + log L)^k W^{Ck τ} R^k`. -/
private theorem c3_TLam_le (hL : 3 ≤ L) (hk : 2 ≤ k) {s t τ Wr 𝔠 cC : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (hτ : 0 < τ) (hW1 : 1 ≤ Wr) (h𝔠 : 0 < 𝔠)
    (hQ : 2 * ((k - 1 : ℕ) : ℝ) * ((L : ℝ) ^ 2 * c3w2 L t * c3e L s t *
        Real.exp (-(Wr ^ τ) / 20000) * c3SY L k s t (ellT L s * Wr ^ τ)) ≤ 1) :
    ((k - 1 : ℕ) : ℝ) * ((c3vp L s t)⁻¹ * ellT L s * c3SY L k s t (ellT L s * Wr ^ τ) *
          Wr ^ (cC * (2 * τ)) +
        c3w2 L t * c3e L s t * (ellT L t * (ellT L s * c3SY L k s t (ellT L s * Wr ^ τ))) *
          Wr ^ (cC * (2 * τ))) +
      2 * ((k - 1 : ℕ) : ℝ) * ((L : ℝ) ^ 2 * c3w2 L t * c3e L s t *
        Real.exp (-(Wr ^ τ) / 20000) * c3SY L k s t (ellT L s * Wr ^ τ)) +
      2 * 2 ^ k * (1 + (2 * (ellT L s * Wr ^ τ) + 1) ^ 2 * c3e L s t) ^ (k - 1) ≤
    c3A1 k * (1 + Real.log L) ^ k * (Wr ^ (cCase3 𝔠 cC k * τ) * rhoR L s t ^ k) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hW0 : 0 < Wr := by linarith
  have hKw1 : 1 ≤ Wr ^ τ := Real.one_le_rpow hW1 hτ.le
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hlam := c3_lam_one L
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hroom1, hroom2⟩ := c3_Ck_room h𝔠 cC k hk1
  have hCk0 : 0 ≤ cCase3 𝔠 cC k := by
    have := abs_nonneg cC
    have h1 : (0 : ℝ) ≤ 2 * (k : ℝ) + 2 * |cC| := by positivity
    linarith
  have hWm1 : 1 ≤ Wr ^ (cCase3 𝔠 cC k * τ) := Real.one_le_rpow hW1 (by positivity)
  have hpe1 : (Wr ^ τ) ^ (2 * k - 1) * Wr ^ (2 * |cC| * τ) ≤ Wr ^ (cCase3 𝔠 cC k * τ) := by
    apply c3_pow_exp hW1 hτ (2 * k - 1) cC
    have : ((2 * k - 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
      have : (2 * k - 1 : ℕ) ≤ 2 * k := Nat.sub_le _ _
      exact_mod_cast this
    linarith
  have hpe2 : (Wr ^ τ) ^ (2 * (k - 1)) ≤ Wr ^ (cCase3 𝔠 cC k * τ) := by
    have h1 : (Wr ^ τ) ^ (2 * (k - 1)) = Wr ^ (((2 * (k - 1) : ℕ) : ℝ) * τ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_le hW1
    have h3 : ((2 * (k - 1) : ℕ) : ℝ) ≤ cCase3 𝔠 cC k := by
      have : (2 * (k - 1) : ℕ) ≤ 2 * k := by omega
      have h4 : ((2 * (k - 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast this
      linarith [abs_nonneg cC]
    exact mul_le_mul_of_nonneg_right h3 hτ.le
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hS0 : 0 ≤ c3SY L k s t (ellT L s * Wr ^ τ) :=
    c3SY_nonneg hL hst ht (by positivity)
  have hBw := c3_Bw_le hL hs hst ht hKw1
  have he0 := c3e_nonneg hL hst ht
  have hBw0 : 0 ≤ 1 + (2 * (ellT L s * Wr ^ τ) + 1) ^ 2 * c3e L s t := by positivity
  refine c3_TLam_abs (P := derivativePrefactor (10 ^ 14) L) (c5 := cProp5) (cP := c3cP)
    (cB := c3cB) (Wc2 := Wr ^ (2 * |cC| * τ)) hk (Nat.cast_nonneg _)
    (inv_pos.2 (c3vp_pos hL hst ht)).le (Real.rpow_nonneg hW0.le _) hBw0 (c3_P_nonneg L) hlam hR1
    hKw1 hWm1 hc5 (by unfold c3cP; norm_num) (by unfold c3cB; positivity)
    (c3_Q1 hL hk hs hst ht hKw1) (c3_Q2 hL hk hs hst ht hKw1) (c3_P_le L) (c3_WC_le hW1 hτ cC)
    hpe1 hpe2 (by unfold c3cB; exact hBw) hQ

private def c3F (k : ℕ) : ℝ := 2 * ((k - 1 : ℕ) : ℝ) * (1 + 2 * cProp5) ^ k + 2 * 2 ^ k

/-- `N^m ≤ W^{m/𝔠}` for a real exponent `m ≥ 0`. -/
private theorem c3_rpow_le {N W 𝔠 : ℝ} (hN : 0 ≤ N) (h𝔠 : 0 < 𝔠) (hW : N ^ 𝔠 ≤ W) {m : ℝ}
    (hm : 0 ≤ m) : N ^ m ≤ W ^ (m / 𝔠) := by
  have : N ^ m = (N ^ 𝔠) ^ (m / 𝔠) := by
    rw [← Real.rpow_mul hN, mul_div_cancel₀ _ h𝔠.ne']
  rw [this]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hN _) hW (by positivity)

/-- **(B-F)**: the coefficient of `N_ε W^{-D}` is `≤ c_F (1 + log L)^k W^{Ck}` (far part:
`r^k, r'^k ≤ N^{2k}·polylog ≤ W^{2k/𝔠}·polylog`). -/
private theorem c3_TF_le (hL : 3 ≤ L) (hk : 2 ≤ k) {s t Wr Nn 𝔠 cC : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (hN1 : 1 ≤ Nn) (hL2 : (L : ℝ) ^ 2 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t)
    (h𝔠 : 0 < 𝔠) (hW1 : 1 ≤ Wr) (hNW : Nn ^ 𝔠 ≤ Wr) :
    2 * (((k - 1 : ℕ) : ℝ) * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
        2 ^ k * ((1 - s) / (1 - t)) ^ k) ≤
      c3F k * (1 + Real.log L) ^ k * Wr ^ (cCase3 𝔠 cC k) := by
  have hlam := c3_lam_one L
  have hlam0 : 0 ≤ 1 + Real.log L := by linarith
  have hr := c3_r_le hst ht hN1 h1t hs
  have hrp := c3_rprime_le hL hst ht hs hN1 hL2 h1t
  have hr0 : 0 ≤ (1 - s) / (1 - t) := by
    have : 0 < 1 - t := by linarith
    exact div_nonneg (by linarith) this.le
  have hrp0 : 0 ≤ (t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t := by
    have : 0 < 1 - t := by linarith
    have := c3e_nonneg hL hst ht
    have : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
    positivity
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, hroom2⟩ := c3_Ck_room h𝔠 cC k hk1
  have hN0 : 0 ≤ Nn := by linarith
  have hNk : Nn ^ (2 * k) ≤ Wr ^ (((2 * k : ℕ) : ℝ) / 𝔠) := c3_pow_le hN0 h𝔠 hNW (2 * k)
  have hWk : Wr ^ (((2 * k : ℕ) : ℝ) / 𝔠) ≤ Wr ^ (cCase3 𝔠 cC k) := by
    apply Real.rpow_le_rpow_of_exponent_le hW1
    have : ((2 * k : ℕ) : ℝ) / 𝔠 = 2 * (k : ℝ) / 𝔠 := by push_cast; ring
    rw [this]; exact hroom2
  have hNk1 : Nn ^ k ≤ Nn ^ (2 * k) := pow_le_pow_right₀ hN1 (by omega)
  have h1 : ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k ≤
      (1 + 2 * cProp5) ^ k * (1 + Real.log L) ^ k * Nn ^ (2 * k) := by
    calc ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k
        ≤ ((1 + 2 * cProp5) * (1 + Real.log L) * Nn ^ 2) ^ k := pow_le_pow_left₀ hrp0 hrp k
      _ = (1 + 2 * cProp5) ^ k * (1 + Real.log L) ^ k * Nn ^ (2 * k) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 k]
  have h2 : ((1 - s) / (1 - t)) ^ k ≤ Nn ^ (2 * k) :=
    (pow_le_pow_left₀ hr0 hr k).trans hNk1
  have hWp : 0 ≤ Wr ^ (cCase3 𝔠 cC k) := Real.rpow_nonneg (by linarith) _
  have hlk : 1 ≤ (1 + Real.log L) ^ k := one_le_pow₀ hlam
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hNW2 : Nn ^ (2 * k) ≤ Wr ^ (cCase3 𝔠 cC k) := hNk.trans hWk
  have hNN0 : 0 ≤ Nn ^ (2 * k) := by positivity
  calc 2 * (((k - 1 : ℕ) : ℝ) * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
        2 ^ k * ((1 - s) / (1 - t)) ^ k)
      ≤ 2 * (((k - 1 : ℕ) : ℝ) * ((1 + 2 * cProp5) ^ k * (1 + Real.log L) ^ k * Nn ^ (2 * k)) +
        2 ^ k * Nn ^ (2 * k)) := by
        have := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ))
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 ^ k)
        nlinarith
    _ ≤ (2 * ((k - 1 : ℕ) : ℝ) * (1 + 2 * cProp5) ^ k + 2 * 2 ^ k) * (1 + Real.log L) ^ k *
        Nn ^ (2 * k) := by
        have h3 : 2 ^ k * Nn ^ (2 * k) ≤ 2 ^ k * (1 + Real.log L) ^ k * Nn ^ (2 * k) := by
          have : 0 ≤ 2 ^ k * Nn ^ (2 * k) := by positivity
          nlinarith
        nlinarith
    _ ≤ c3F k * (1 + Real.log L) ^ k * Wr ^ (cCase3 𝔠 cC k) := by
        unfold c3F
        have : 0 ≤ (2 * ((k - 1 : ℕ) : ℝ) * (1 + 2 * cProp5) ^ k + 2 * 2 ^ k) *
            (1 + Real.log L) ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hNW2 this


/-- The assembly of the four coefficient bounds. -/
private theorem c3_assemble {Nε Λ η₀ Wm Wd TΛ TF TD Tη Lk Rk Wpk WCk cA cF : ℝ}
    (hNε : 1 ≤ Nε) (hΛ : 0 ≤ Λ) (hη : 0 ≤ η₀) (hWm : 0 ≤ Wm) (hWd : 0 ≤ Wd)
    (hLk : 1 ≤ Lk) (hRk : 0 ≤ Rk) (hWpk : 0 ≤ Wpk) (hWCk : 1 ≤ WCk) (hcA : 0 ≤ cA)
    (hcF : 0 ≤ cF) (hTΛ : TΛ ≤ cA * Lk * (Wpk * Rk)) (hTF : TF ≤ cF * Lk * WCk)
    (hWdTD : Wd * TD ≤ Wm) (hηTη : η₀ * Tη ≤ Wm) :
    Nε * Λ * TΛ + Nε * Wm * TF + Nε * Wd * TD + η₀ * Tη ≤
      Nε * ((cA + cF + 2) * Lk) * (Wpk * Λ * Rk + Wm * WCk) := by
  have hNε0 : 0 ≤ Nε := by linarith
  have hWG : Wm ≤ Wm * WCk := by nlinarith
  have h1 : Nε * Λ * TΛ ≤ Nε * cA * Lk * (Wpk * Λ * Rk) := by
    have := mul_le_mul_of_nonneg_left hTΛ (mul_nonneg hNε0 hΛ)
    calc Nε * Λ * TΛ ≤ Nε * Λ * (cA * Lk * (Wpk * Rk)) := this
      _ = Nε * cA * Lk * (Wpk * Λ * Rk) := by ring
  have h2 : Nε * Wm * TF ≤ Nε * cF * Lk * (Wm * WCk) := by
    have := mul_le_mul_of_nonneg_left hTF (mul_nonneg hNε0 hWm)
    calc Nε * Wm * TF ≤ Nε * Wm * (cF * Lk * WCk) := this
      _ = Nε * cF * Lk * (Wm * WCk) := by ring
  have h3 : Nε * Wd * TD ≤ Nε * (Wm * WCk) := by
    calc Nε * Wd * TD = Nε * (Wd * TD) := by ring
      _ ≤ Nε * Wm := mul_le_mul_of_nonneg_left hWdTD hNε0
      _ ≤ Nε * (Wm * WCk) := mul_le_mul_of_nonneg_left hWG hNε0
  have h4 : η₀ * Tη ≤ Nε * (Wm * WCk) := by
    calc η₀ * Tη ≤ Wm := hηTη
      _ ≤ Wm * WCk := hWG
      _ = 1 * (Wm * WCk) := (one_mul _).symm
      _ ≤ Nε * (Wm * WCk) := mul_le_mul_of_nonneg_right hNε (by positivity)
  have hGm : 0 ≤ Wpk * Λ * Rk := by positivity
  have hGf : 0 ≤ Wm * WCk := by positivity
  calc Nε * Λ * TΛ + Nε * Wm * TF + Nε * Wd * TD + η₀ * Tη
      ≤ Nε * cA * Lk * (Wpk * Λ * Rk) + Nε * cF * Lk * (Wm * WCk) + Nε * (Wm * WCk) +
        Nε * (Wm * WCk) := by linarith
    _ ≤ Nε * ((cA + cF + 2) * Lk) * (Wpk * Λ * Rk) +
        Nε * ((cA + cF + 2) * Lk) * (Wm * WCk) := by
        have hc1 : cA ≤ (cA + cF + 2) := by linarith
        have hc2 : cF * Lk + 2 ≤ (cA + cF + 2) * Lk := by nlinarith
        have e1 : Nε * cA * Lk * (Wpk * Λ * Rk) ≤ Nε * ((cA + cF + 2) * Lk) * (Wpk * Λ * Rk) := by
          have : cA * Lk ≤ (cA + cF + 2) * Lk := mul_le_mul_of_nonneg_right hc1 (by linarith)
          have := mul_le_mul_of_nonneg_left this hNε0
          calc Nε * cA * Lk * (Wpk * Λ * Rk) = (Nε * (cA * Lk)) * (Wpk * Λ * Rk) := by ring
            _ ≤ (Nε * ((cA + cF + 2) * Lk)) * (Wpk * Λ * Rk) :=
                mul_le_mul_of_nonneg_right this hGm
        have e2 : Nε * cF * Lk * (Wm * WCk) + Nε * (Wm * WCk) + Nε * (Wm * WCk) ≤
            Nε * ((cA + cF + 2) * Lk) * (Wm * WCk) := by
          have := mul_le_mul_of_nonneg_left hc2 hNε0
          calc Nε * cF * Lk * (Wm * WCk) + Nε * (Wm * WCk) + Nε * (Wm * WCk)
              = (Nε * (cF * Lk + 2)) * (Wm * WCk) := by ring
            _ ≤ (Nε * ((cA + cF + 2) * Lk)) * (Wm * WCk) :=
                mul_le_mul_of_nonneg_right this hGf
        linarith
    _ = Nε * ((cA + cF + 2) * Lk) * (Wpk * Λ * Rk + Wm * WCk) := by ring

end Coef


/-! ## Part 8: the forms and the matrices `Z` along the sequence -/

section Pins

variable {d : Sizes}

private theorem c3_vp_e_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) : c3vp L s t * c3e L s t ≤ 2 * cProp5 * (1 + Real.log L) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1s : 0 < 1 - s := by linarith
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := KernelExpand_min_one_pos' hL ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlam := c3_lam_one L
  unfold c3vp c3e
  rw [KernelExpand_ellT_sq_mul ht]
  have : min 1 ((L : ℝ) ^ 2 * (1 - t)) / (1 - s) *
      (2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t))) =
      2 * cProp5 * (1 + Real.log L) * ((t - s) / (1 - s)) := by
    field_simp
  rw [this]
  have h2 : (t - s) / (1 - s) ≤ 1 := by
    rw [div_le_one h1s]; linarith
  have h3 : 0 ≤ 2 * cProp5 * (1 + Real.log L) := by positivity
  calc 2 * cProp5 * (1 + Real.log L) * ((t - s) / (1 - s))
      ≤ 2 * cProp5 * (1 + Real.log L) * 1 := mul_le_mul_of_nonneg_left h2 h3
    _ = 2 * cProp5 * (1 + Real.log L) := mul_one _

private theorem c3_Z1_norm_le (hXe : XiEntryBound) {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]
    (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a : Fin k → Z2 L)
    (y x : Z2 L) :
    ‖c3Z1 s t a y x‖ ≤ 2 * cProp5 * (1 + Real.log L) * ((zdist2 L (y - x) : ℝ) + 1)⁻¹ := by
  have hvp := c3vp_pos hL hst ht
  have he := c3_entry_le hXe hL hs hst ht (a 0) x
  have hve := c3_vp_e_le hL hs hst ht
  have hD : 0 < ((zdist2 L (y - x) : ℝ) + 1)⁻¹ := by positivity
  unfold c3Z1
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hvp.le, Real.norm_of_nonneg hD.le]
  calc c3vp L s t * ‖xiMat L 1 s t (a 0) x‖ * ((zdist2 L (y - x) : ℝ) + 1)⁻¹
      ≤ c3vp L s t * c3e L s t * ((zdist2 L (y - x) : ℝ) + 1)⁻¹ := by
        gcongr
    _ ≤ 2 * cProp5 * (1 + Real.log L) * ((zdist2 L (y - x) : ℝ) + 1)⁻¹ := by
        gcongr

open scoped Classical in
private theorem c3_Z2_norm_le (hXe : XiEntryBound) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (ρt : ℝ) (y x : Z2 L) :
    ‖c3Z2 s t ρt y x‖ ≤ c3vp L s t * c3w2 L t * c3e L s t := by
  have hvp := c3vp_pos hL hst ht
  have hw2 := c3w2_pos hL ht
  have he := c3_entry_le hXe hL hs hst ht y x
  have he0 := c3e_nonneg hL hst ht
  unfold c3Z2
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖(if (zdist2 L (y - x) : ℝ) < ρt then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  calc c3vp L s t * c3w2 L t * ‖xiMat L 1 s t y x‖ *
        ‖(if (zdist2 L (y - x) : ℝ) < ρt then (1 : ℂ) else 0)‖
      ≤ c3vp L s t * c3w2 L t * c3e L s t * 1 := by
        gcongr
    _ = c3vp L s t * c3w2 L t * c3e L s t := mul_one _

open scoped Classical in
private theorem c3_Z2_supp {L : ℕ} [NeZero L] {s t : ℝ} {ρt : ℝ} (y x : Z2 L)
    (h : ρt ≤ (zdist2 L (y - x) : ℝ)) : c3Z2 s t ρt y x = 0 := by
  unfold c3Z2
  simp only [not_lt.2 h, ↓reduceIte, mul_zero]

end Pins


section PinApp

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

private theorem c3_size_one (d : Sizes) (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : 1 ≤ d.size n := by
    unfold Sizes.size
    exact Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))
  exact_mod_cast h1

/-- The index `n` is good for the label `i`: `i ≠ 0`, `W^τ ≥ 3`, and `S_Y ≤ N^{cY}`. -/
private def c3Good (d : Sizes) (k : ℕ) [NeZero k] (τ : ℝ) (u t : ℕ → ℝ) (cY : ℝ) (i : Fin k)
    (n : ℕ) : Prop :=
  i ≠ 0 ∧ 3 ≤ (d.W n : ℝ) ^ τ ∧ c3Sn d k τ u t n ≤ ((d.size n : ℕ) : ℝ) ^ cY

/-- The local form of the field `Y_i` at size `n`. -/
private def c3FYn (d : Sizes) {k K : ℕ} [NeZero k] (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ : ℝ) (u t : ℕ → ℝ) (a : ∀ n, Fin k → Z2 (d.L n)) (cY : ℝ) (i : Fin k) (n : ℕ) :
    LocalForm (d.L n) (d.W n) 1 K :=
  c3FY (F n) (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i (c3Good d k τ u t cY i n)

private theorem c3FYn_coef (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (hXe : XiEntryBound)
    (hXd : XiFirstDiff) (a : ∀ n, Fin k → Z2 (d.L n)) {cY : ℝ} (hcY : 0 ≤ cY) (i : Fin k)
    (n : ℕ) (b : Fin 1 → Z2 (d.L n)) (j : Fin (K + 1))
    (q : Fin j → Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) × Bool) :
    ‖(c3FYn d F τ u t a cY i n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ (C' + cY) := by
  by_cases hg : c3Good d k τ u t cY i n
  · obtain ⟨hi, hW3, hS⟩ := hg
    have hL := d.three_le_L n
    have hu0 : 0 ≤ u n := (hc.hs₀ n).trans (hc.hsu n)
    have hut := hc.hut n
    have htl := hc.ht n
    have hN1 := c3_size_one d n
    have hℓ := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1
    have hρ0 : 0 ≤ ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ := by positivity
    have hNc : 0 ≤ ((d.size n : ℕ) : ℝ) ^ C' := Real.rpow_nonneg (by linarith) _
    have h1 := c3FY_coef_le hXe hXd hL hu0 hut htl (F n) (a n) i hi hρ0 hNc (hc.hcoef n)
      (c3Good d k τ u t cY i n) b j q
    unfold c3FYn
    refine h1.trans ?_
    rw [Real.rpow_add (by linarith), mul_comm (((d.size n : ℕ) : ℝ) ^ C')]
    exact mul_le_mul_of_nonneg_right hS hNc
  · unfold c3FYn c3FY
    simp only [hg, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg (by linarith [c3_size_one d n]) _

private theorem c3FYn_local (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (a : ∀ n, Fin k → Z2 (d.L n)) (cY : ℝ) (i : Fin k) (n : ℕ) :
    (c3FYn d F τ u t a cY i n).Local (2 * τ) (u n) := by
  have hL := d.three_le_L n
  have hu0 : 0 ≤ u n := (hc.hs₀ n).trans (hc.hsu n)
  have hut := hc.hut n
  have htl := hc.ht n
  have hℓ := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1
  unfold c3FYn
  exact c3FY_local (F n) (t n) (a n) (by exact_mod_cast d.W_pos n) hℓ.le (hc.hloc n) i _
    (fun hg => hg.2.1)


private theorem c3_L2_le_size (d : Sizes) (n : ℕ) : (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have hW : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have : ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
    unfold Sizes.size; push_cast; ring
  rw [this]
  have hL0 : (0 : ℝ) ≤ (d.L n : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hW hL0, sq_nonneg (d.L n : ℝ)]

/-- `Λ` dominates `‖𝒜‖` uniformly in the label (the union moves inside `P`). -/
private theorem c3_stoch_Lambda (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    StochDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) := by
  refine stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (k : ℝ)) (Nat.cast_nonneg _) ?_
    hc.hΛ
  refine Filter.Eventually.of_forall fun n => ?_
  have hcard : (Fintype.card (Unit × (Fin k → Z2 (d.L n))) : ℝ) = ((d.L n : ℝ) ^ 2) ^ k := by
    simp [Z2, Fintype.card_prod, ZMod.card, sq]
  rw [hcard, Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) (c3_L2_le_size d n) k

/-- The hypothesis `Y ≺ Λ_Y` of the `clt-lemma` statements, from `𝒜 ≺ Λ` (the bound
`Y_i ≤ S_Y max|𝒜|`). -/
private theorem c3_hΛY (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (hXe : XiEntryBound)
    (hXd : XiFirstDiff) (a : ∀ n, Fin k → Z2 (d.L n)) {cY : ℝ} (i : Fin k)
    (hgood : ∀ᶠ n : ℕ in atTop, c3Good d k τ u t cY i n) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖cltY (c3FYn d F τ u t a cY i n) (E n) (u n)
        (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => c3Sn d k τ u t n * Λ n) := by
  have hst := c3_stoch_Lambda hc
  intro ε hε D' hD'
  filter_upwards [hst ε hε D' hD', hgood] with n hn hg p
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [badSetAt, Set.mem_ofPred_eq]
  by_contra hcon
  push Not at hcon
  have hL := d.three_le_L n
  have hu0 : 0 ≤ u n := (hc.hs₀ n).trans (hc.hsu n)
  have hut := hc.hut n
  have htl := hc.ht n
  have hℓ := (ellT_pos_le (L := d.L n) (by omega) (lt_of_le_of_lt hut htl)).1
  have hρ0 : 0 ≤ ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ := by positivity
  have hbd : ∀ b : Fin k → Z2 (d.L n), ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε * Λ n := fun b => hcon ((), b)
  have hMT : 0 ≤ ((d.size n : ℕ) : ℝ) ^ ε * Λ n :=
    (norm_nonneg _).trans (hbd (fun _ => 0))
  have hev := c3FY_eval (F n) (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i
    (good := c3Good d k τ u t cY i n) hg (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2
  have hY := c3_Y_norm_le hXe hXd hL hu0 hut htl (a n) i hg.1 hρ0
    (T := fun b => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b) hMT hbd p.2
  have : ‖cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖ ≤
      c3Sn d k τ u t n * (((d.size n : ℕ) : ℝ) ^ ε * Λ n) := by
    unfold c3FYn
    rw [hev]
    exact hY
  linarith [hω]


/-- **Case 2 of `clt-lemma`** applied to the field `Y_i` with `Z = c3Z1` (proof of `lem:sum_decay`).
-/
private theorem c3_pin2 {cC : ℝ} (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (h2 : CltCase2Prec d κ 𝔠 δ cC) (hXe : XiEntryBound) (hXd : XiFirstDiff)
    (a : ∀ n, Fin k → Z2 (d.L n)) {cY Dc : ℝ} (hcY : 0 ≤ cY) (hDc : 0 < Dc) (i : Fin k)
    (hgood : ∀ᶠ n : ℕ in atTop, c3Good d k τ u t cY i n) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖∑ b : Z2 (d.L n), c3Z1 (u n) (t n) (a n) p.2 b *
        (cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b
            ∂(Sizes.seqP d))‖)
      (fun n _ _ => (d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (u n) *
        (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc)) := by
  refine h2 hc.hκ hc.h𝔠 hc.hδ K (C' + cY) (2 * τ) Dc (by linarith [hc.hC']) (by linarith [hc.hτ])
    hDc E s₀ t₀ u t (fun n => c3Sn d k τ u t n * Λ n) (c3FYn d F τ u t a cY i)
    (fun n => c3Z1 (u n) (t n) (a n)) hc.hE hc.hs₀ hc.hsu hc.hut₀ hc.hut hc.ht hc.hN hc.hW hc.hR
    hc.hLoc hc.hDec hc.hV3 (fun n b j q => c3FYn_coef hc hXe hXd a hcY i n b j q)
    (c3FYn_local hc a cY i) (c3_hΛY hc hXe hXd a i hgood) ?_
  intro ε hε
  filter_upwards [c3_polylog d hc.hN (2 * cProp5) 1 hε] with n hn y x
  have hL := d.three_le_L n
  have hu0 : 0 ≤ u n := (hc.hs₀ n).trans (hc.hsu n)
  have h1 := c3_Z1_norm_le hXe hL hu0 (hc.hut n) (hc.ht n) (a n) y x
  have hc5 : |2 * cProp5| = 2 * cProp5 := abs_of_nonneg (by unfold cProp5; norm_num)
  rw [hc5, pow_one] at hn
  have hD : 0 ≤ ((zdist2 (d.L n) (y - x) : ℝ) + 1)⁻¹ := by positivity
  calc ‖c3Z1 (u n) (t n) (a n) y x‖
      ≤ 2 * cProp5 * (1 + Real.log (d.L n : ℝ)) * ((zdist2 (d.L n) (y - x) : ℝ) + 1)⁻¹ := h1
    _ ≤ ((d.size n : ℕ) : ℝ) ^ ε * ((zdist2 (d.L n) (y - x) : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hn hD

/-- **Case 1 of `clt-lemma`** applied to the field `Y_i` with `Z̃ = c3Z2` (proof of
`lem:sum_decay`). -/
private theorem c3_pin1 {cC : ℝ} (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (h1 : CltCase1Prec d κ 𝔠 δ cC) (hXe : XiEntryBound) (hXd : XiFirstDiff)
    (a : ∀ n, Fin k → Z2 (d.L n)) {cY Dc : ℝ} (hcY : 0 ≤ cY) (hDc : 0 < Dc) (i : Fin k)
    (hgood : ∀ᶠ n : ℕ in atTop, c3Good d k τ u t cY i n) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖∑ b : Z2 (d.L n),
        c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) p.2 b *
        (cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b
            ∂(Sizes.seqP d))‖)
      (fun n p _ => (Finset.univ.sup' Finset.univ_nonempty fun b : Z2 (d.L n) =>
          ‖c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) p.2 b‖) *
        ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (t n) * ellT (d.L n) (u n) *
          (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc))) := by
  refine h1 hc.hκ hc.h𝔠 hc.hδ K (C' + cY) (2 * τ) Dc (by linarith [hc.hC']) (by linarith [hc.hτ])
    hDc E s₀ t₀ u t (fun n => c3Sn d k τ u t n * Λ n) (c3FYn d F τ u t a cY i)
    (fun n => c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ)) hc.hE hc.hs₀ hc.hsu hc.hut₀
    hc.hut hc.ht hc.hN hc.hW hc.hR hc.hLoc hc.hDec hc.hV3
    (fun n b j q => c3FYn_coef hc hXe hXd a hcY i n b j q) (c3FYn_local hc a cY i)
    (c3_hΛY hc hXe hXd a i hgood) ?_
  intro n y x hyx
  apply c3_Z2_supp
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hut := hc.hut n
  have htl := hc.ht n
  have hu0 : 0 ≤ u n := (hc.hs₀ n).trans (hc.hsu n)
  have hℓ := (ellT_pos_le (L := d.L n) (by have := d.three_le_L n; omega) htl).1
  have h1' : (d.W n : ℝ) ^ τ ≤ (d.W n : ℝ) ^ (2 * τ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [hc.hτ])
  calc ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ ≤ ellT (d.L n) (t n) * (d.W n : ℝ) ^ (2 * τ) :=
        mul_le_mul_of_nonneg_left h1' hℓ.le
    _ ≤ _ := hyx

end PinApp


/-! ## Part 9: the deterministic bound at one size -/

section DetAt

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- **The alternating case at one size** (`sum_res_3`, proof of `lem:sum_decay`): the master bound,
the split and
the four coefficient bounds give `≤ N_ε c (1+log L)^k (W^{Ck τ} Λ R^k + W^{-D+Ck})`. -/
private theorem c3_alt_det (hXe : XiEntryBound) (hXr : XiRowBound) (hXd : XiFirstDiff)
    (hL : 3 ≤ L) (hk : 2 ≤ k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool) (hσ : ∀ i, σ i ≠ σ (i + 1))
    (a : Fin k → Z2 L) {τ Wr Nn 𝔠 cC D Dc : ℝ} (hτ : 0 < τ) (hW1 : 1 ≤ Wr) (h𝔠 : 0 < 𝔠)
    (hN1 : 1 ≤ Nn) (hL2 : (L : ℝ) ^ 2 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) (hNW : Nn ^ 𝔠 ≤ Wr)
    (𝒜 Ā : (Fin k → Z2 L) → ℂ) {Nε Λ η₀ : ℝ} (hNε : 1 ≤ Nε) (hΛ : 0 ≤ Λ) (hη : 0 ≤ η₀)
    (h𝒜 : ∀ b, ‖𝒜 b‖ ≤ Nε * Λ + η₀) (hĀ : ∀ b, ‖Ā b‖ ≤ Nε * Λ + η₀)
    (hdec : ∀ b, ellT L s * Wr ^ τ ≤ (KLoop.maxDist L b : ℝ) →
      ‖𝒜 b - Ā b‖ ≤ 2 * Nε * Wr ^ (-D) + η₀)
    (hsz : SumZero L (fun b => 𝒜 b - Ā b)) {Zs : ℝ} (hZs0 : 0 ≤ Zs)
    (hZs : Zs ≤ c3vp L s t * c3w2 L t * c3e L s t)
    (hC1 : ∀ i, i ≠ 0 → ‖∑ x : Z2 L, c3Z1 s t a (a i) x *
      (c3Y s t a (ellT L s * Wr ^ τ) i 𝒜 x - c3Y s t a (ellT L s * Wr ^ τ) i Ā x)‖ ≤
      Nε * (Wr ^ (cC * (2 * τ)) * ellT L s * (c3SY L k s t (ellT L s * Wr ^ τ) * Λ) +
        Wr ^ (-Dc)))
    (hC2 : ∀ i, i ≠ 0 → ‖∑ x : Z2 L, c3Z2 s t (ellT L t * Wr ^ τ) (a 0) x *
      (c3Y s t a (ellT L s * Wr ^ τ) i 𝒜 x - c3Y s t a (ellT L s * Wr ^ τ) i Ā x)‖ ≤
      Nε * (Zs * (Wr ^ (cC * (2 * τ)) * ellT L t * ellT L s *
        (c3SY L k s t (ellT L s * Wr ^ τ) * Λ) + Wr ^ (-Dc))))
    (hQ : 2 * ((k - 1 : ℕ) : ℝ) * ((L : ℝ) ^ 2 * c3w2 L t * c3e L s t *
        Real.exp (-(Wr ^ τ) / 20000) * c3SY L k s t (ellT L s * Wr ^ τ)) ≤ 1)
    (hWdTD : Wr ^ (-Dc) * (((k - 1 : ℕ) : ℝ) * ((c3vp L s t)⁻¹ + c3w2 L t * c3e L s t)) ≤
      Wr ^ (-D))
    (hηTη : η₀ * (((k - 1 : ℕ) : ℝ) * ((t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) ^ k +
      2 ^ k * ((1 - s) / (1 - t)) ^ k +
      2 * ((k - 1 : ℕ) : ℝ) * ((L : ℝ) ^ 2 * c3w2 L t * c3e L s t *
        Real.exp (-(Wr ^ τ) / 20000) * c3SY L k s t (ellT L s * Wr ^ τ)) +
      2 * 2 ^ k * (1 + (2 * (ellT L s * Wr ^ τ) + 1) ^ 2 * c3e L s t) ^ (k - 1)) ≤ Wr ^ (-D)) :
    ‖Ugen L E σ s t (fun b => 𝒜 b - Ā b) a‖ ≤
      Nε * ((c3A1 k + c3F k + 2) * (1 + Real.log L) ^ k) *
        (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k + Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hW0 : 0 < Wr := by linarith
  have hKw1 : 1 ≤ Wr ^ τ := Real.one_le_rpow hW1 hτ.le
  have hNε0 : 0 ≤ Nε := by linarith
  have hM₁ : 0 ≤ Nε * Λ + η₀ := by positivity
  have hδA : 0 ≤ 2 * Nε * Wr ^ (-D) + η₀ := by
    have : 0 ≤ Wr ^ (-D) := Real.rpow_nonneg hW0.le _
    positivity
  have hm := c3_master hXe hXr hXd hL hs hst ht hE σ hσ a (Kw := Wr ^ τ) hKw1 𝒜 Ā hM₁ hδA
    h𝒜 hĀ hdec hsz hC1 hC2
  refine hm.trans ?_
  -- the split
  have hvi := (inv_pos.2 (c3vp_pos hL hst ht)).le
  have hvp := (c3vp_pos hL hst ht).le
  have hvivp : (c3vp L s t)⁻¹ * c3vp L s t = 1 := inv_mul_cancel₀ (c3vp_pos hL hst ht).ne'
  have hw2 := (c3w2_pos hL ht).le
  have he0 := c3e_nonneg hL hst ht
  have hℓs : 1 ≤ ellT L s := one_le_ellT (by omega) hs hs1
  have hℓt : 1 ≤ ellT L t := one_le_ellT (by omega) (hs.trans hst) ht
  have hS0 : 0 ≤ c3SY L k s t (ellT L s * Wr ^ τ) := c3SY_nonneg hL hst ht (by positivity)
  have hBw0 : 0 ≤ 1 + (2 * (ellT L s * Wr ^ τ) + 1) ^ 2 * c3e L s t := by positivity
  have hr0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hrp0 : 0 ≤ (t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t := by
    have : 0 ≤ (t - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
    positivity
  have hsplit := c3_rhs_split (Nε := Nε) (Λ := Λ) (η₀ := η₀) (Wm := Wr ^ (-D))
    (Wd := Wr ^ (-Dc)) (WC := Wr ^ (cC * (2 * τ))) (ℓs := ellT L s) (ℓt := ellT L t)
    (S := c3SY L k s t (ellT L s * Wr ^ τ)) (X := Real.exp (-(Wr ^ τ) / 20000))
    (vi := (c3vp L s t)⁻¹) (vp := c3vp L s t) (w2 := c3w2 L t) (e := c3e L s t)
    (Bw := 1 + (2 * (ellT L s * Wr ^ τ) + 1) ^ 2 * c3e L s t) (r := (1 - s) / (1 - t))
    (r' := (t - s) / (1 - t) + (L : ℝ) ^ 2 * c3e L s t) (L2 := (L : ℝ) ^ 2) (Zs := Zs)
    (κ1 := ((k - 1 : ℕ) : ℝ)) (T2 := 2 ^ k) (by linarith) hΛ hη (Real.rpow_nonneg hW0.le _)
    (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _) (by linarith) (by linarith) hS0
    (Real.exp_pos _).le hvi hvp hw2 he0 hBw0 hr0 hrp0 (by positivity) hZs0 (Nat.cast_nonneg _)
    (by positivity) hvivp hZs (k := k)
  refine hsplit.trans ?_
  -- the four coefficient bounds
  have hTL := c3_TLam_le hL hk hs hst ht hτ hW1 h𝔠 (cC := cC) hQ
  have hTF := c3_TF_le hL hk hs hst ht hN1 hL2 h1t h𝔠 hW1 hNW (cC := cC)
  have hlam := c3_lam_one L
  have hLk : 1 ≤ (1 + Real.log L) ^ k := one_le_pow₀ hlam
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hRk : 0 ≤ rhoR L s t ^ k := by positivity
  have hCk0 : 0 ≤ cCase3 𝔠 cC k := by
    have := abs_nonneg cC
    unfold cCase3 cPrec
    have : (0 : ℝ) ≤ 4 * (k : ℝ) / 𝔠 := by positivity
    positivity
  have hWpk : 0 ≤ Wr ^ (cCase3 𝔠 cC k * τ) := Real.rpow_nonneg hW0.le _
  have hWCk : 1 ≤ Wr ^ (cCase3 𝔠 cC k) := Real.one_le_rpow hW1 hCk0
  have hcA : 0 ≤ c3A1 k := by
    unfold c3A1 c3cB c3cP
    have : 0 ≤ cProp5 := by unfold cProp5; norm_num
    positivity
  have hcF : 0 ≤ c3F k := by
    unfold c3F
    have : 0 ≤ cProp5 := by unfold cProp5; norm_num
    positivity
  exact c3_assemble hNε hΛ hη (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _) hLk hRk
    hWpk hWCk hcA hcF hTL hTF hWdTD hηTη

end DetAt


section DetAt2

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `ratioR = rhoR` for `|E| < 2` (`Im m` cancels). -/
private theorem c3_ratioR_eq {E s t : ℝ} (hE : |E| < 2) : ratioR L E s t = rhoR L s t := by
  have hI : (RBM.Gauss.spectralM E).im ≠ 0 := (RBM.Gauss.spectralM_im_pos hE).ne'
  unfold ratioR rhoR etaT
  rw [← mul_assoc, ← mul_assoc]
  exact mul_div_mul_right _ _ hI

/-- **The non-alternating case at one size** (`nonalternating`, applied `ω`-wise):
`≤ N_ε (2|c₁| + 3)(1+log L)^k (W^{Ck τ} Λ R^k + W^{-D+Ck})`. -/
private theorem c3_nonalt_det {c1 : ℕ → ℝ → ℝ} (hU : UgenCase1Explicit c1) (hL : 3 ≤ L)
    (hk : 2 ≤ k) {κ : ℝ} (hκ : 0 < κ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1)
    {E : ℝ} (hE : |E| ≤ 2 - κ) (σ : Fin k → Bool) (hrep : ∃ i : Fin k, σ i = σ (i + 1))
    (a : Fin k → Z2 L) {τ Wr Nn 𝔠 cC D : ℝ} (hτ : 0 < τ) (hW1 : 1 ≤ Wr) (h𝔠 : 0 < 𝔠)
    (hN1 : 1 ≤ Nn) (h1t : 1 / Nn ≤ 1 - t) (hNW : Nn ^ 𝔠 ≤ Wr)
    (𝒜 Ā : (Fin k → Z2 L) → ℂ) {Nε Λ η₀ : ℝ} (hNε : 1 ≤ Nε) (hΛ : 0 ≤ Λ) (hη : 0 ≤ η₀)
    (h𝒜 : ∀ b, ‖𝒜 b‖ ≤ Nε * Λ + η₀) (hĀ : ∀ b, ‖Ā b‖ ≤ Nε * Λ + η₀)
    (hdec : ∀ b, ellT L s * Wr ^ τ ≤ (KLoop.maxDist L b : ℝ) →
      ‖𝒜 b - Ā b‖ ≤ 2 * Nε * Wr ^ (-D) + η₀)
    (hηT : η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
      rhoR L s t ^ k + ((1 - s) / (1 - t)) ^ k) ≤ Wr ^ (-D)) :
    ‖Ugen L E σ s t (fun b => 𝒜 b - Ā b) a‖ ≤
      Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
        (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k + Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hW0 : 0 < Wr := by linarith
  have hKw1 : 1 ≤ Wr ^ τ := Real.one_le_rpow hW1 hτ.le
  have hNε0 : 0 ≤ Nε := by linarith
  have hM₁ : 0 ≤ Nε * Λ + η₀ := by positivity
  have hWm0 : 0 ≤ Wr ^ (-D) := Real.rpow_nonneg hW0.le _
  have hδA : 0 ≤ 2 * Nε * Wr ^ (-D) + η₀ := by positivity
  have hAM : ∀ b, ‖𝒜 b - Ā b‖ ≤ 2 * (Nε * Λ + η₀) := fun b => by
    calc ‖𝒜 b - Ā b‖ ≤ ‖𝒜 b‖ + ‖Ā b‖ := norm_sub_le _ _
      _ ≤ 2 * (Nε * Λ + η₀) := by linarith [h𝒜 b, hĀ b]
  have hdecA : DecayWin L (ellT L s * Wr ^ τ) (2 * Nε * Wr ^ (-D) + η₀) (fun b => 𝒜 b - Ā b) :=
    fun b hb => hdec b hb
  have hm := hU k hk L hL κ E hκ hE s t hs hst ht σ hrep (Wr ^ τ) (2 * (Nε * Λ + η₀))
    (2 * Nε * Wr ^ (-D) + η₀) hKw1 (by linarith) hδA (fun b => 𝒜 b - Ā b) hAM hdecA a
  refine hm.trans ?_
  -- bounds
  have hR1 : 1 ≤ rhoR L s t := KernelExpand_one_le_rhoR hL hst ht
  have hlam := c3_lam_one L
  have hCk0 : 0 ≤ cCase3 𝔠 cC k := by
    have := abs_nonneg cC
    unfold cCase3 cPrec
    have : (0 : ℝ) ≤ 4 * (k : ℝ) / 𝔠 := by positivity
    positivity
  obtain ⟨hroom1, hroom2⟩ := c3_Ck_room h𝔠 cC k (by omega)
  have hWpk : 1 ≤ Wr ^ (cCase3 𝔠 cC k * τ) := Real.one_le_rpow hW1 (by positivity)
  have hWCk : 1 ≤ Wr ^ (cCase3 𝔠 cC k) := Real.one_le_rpow hW1 hCk0
  have hpe2 : (Wr ^ τ) ^ (2 * (k - 1)) ≤ Wr ^ (cCase3 𝔠 cC k * τ) := by
    have hW0' : 0 < Wr := hW0
    have h1 : (Wr ^ τ) ^ (2 * (k - 1)) = Wr ^ (((2 * (k - 1) : ℕ) : ℝ) * τ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_le hW1
    have h3 : ((2 * (k - 1) : ℕ) : ℝ) ≤ cCase3 𝔠 cC k := by
      have : (2 * (k - 1) : ℕ) ≤ 2 * k := by omega
      have h4 : ((2 * (k - 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast this
      linarith [abs_nonneg cC]
    exact mul_le_mul_of_nonneg_right h3 hτ.le
  have hr0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hr := c3_r_le hst ht hN1 h1t hs
  have hN0 : 0 ≤ Nn := by linarith
  have hNk : Nn ^ k ≤ Wr ^ (((k : ℕ) : ℝ) / 𝔠) := c3_pow_le hN0 h𝔠 hNW k
  have hWk : Wr ^ (((k : ℕ) : ℝ) / 𝔠) ≤ Wr ^ (cCase3 𝔠 cC k) := by
    apply Real.rpow_le_rpow_of_exponent_le hW1
    have : (k : ℝ) / 𝔠 ≤ 2 * (k : ℝ) / 𝔠 :=
      div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith) h𝔠.le
    linarith
  have hrk : ((1 - s) / (1 - t)) ^ k ≤ Wr ^ (cCase3 𝔠 cC k) :=
    (pow_le_pow_left₀ hr0 hr k).trans (hNk.trans hWk)
  -- the pieces
  have hc1 : c1 k κ * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k *
      (2 * (Nε * Λ + η₀)) ≤
      2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε * (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) +
      η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k) := by
    have hq0 : 0 ≤ (1 + Real.log L) ^ k := by positivity
    have hK0 : 0 ≤ (Wr ^ τ) ^ (2 * (k - 1)) := by positivity
    have hRk0 : 0 ≤ rhoR L s t ^ k := by positivity
    have habs : c1 k κ ≤ |c1 k κ| := le_abs_self _
    have hA0 : 0 ≤ (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k := by
      positivity
    have e1 : c1 k κ * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k ≤
        |c1 k κ| * ((1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k) := by
      calc c1 k κ * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k
          = c1 k κ * ((1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k) := by
            ring
        _ ≤ |c1 k κ| * _ := mul_le_mul_of_nonneg_right habs hA0
    have e2 : c1 k κ * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k *
        (2 * (Nε * Λ + η₀)) ≤
        (|c1 k κ| * ((1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k)) *
          (2 * (Nε * Λ + η₀)) := mul_le_mul_of_nonneg_right e1 (by positivity)
    have e3 : (Wr ^ τ) ^ (2 * (k - 1)) ≤ Wr ^ (cCase3 𝔠 cC k * τ) := hpe2
    calc _ ≤ _ := e2
      _ = 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε * ((Wr ^ τ) ^ (2 * (k - 1)) * Λ *
            rhoR L s t ^ k) +
          η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
            rhoR L s t ^ k) := by ring
      _ ≤ _ := by
          have : (Wr ^ τ) ^ (2 * (k - 1)) * Λ * rhoR L s t ^ k ≤
              Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k := by
            have h1 : 0 ≤ Λ * rhoR L s t ^ k := by positivity
            calc (Wr ^ τ) ^ (2 * (k - 1)) * Λ * rhoR L s t ^ k
                = (Wr ^ τ) ^ (2 * (k - 1)) * (Λ * rhoR L s t ^ k) := by ring
              _ ≤ Wr ^ (cCase3 𝔠 cC k * τ) * (Λ * rhoR L s t ^ k) :=
                  mul_le_mul_of_nonneg_right e3 h1
              _ = _ := by ring
          have h5 : 0 ≤ 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε := by positivity
          have := mul_le_mul_of_nonneg_left this h5
          linarith
  have hc2 : ((1 - s) / (1 - t)) ^ k * (2 * Nε * Wr ^ (-D) + η₀) ≤
      2 * Nε * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) + η₀ * ((1 - s) / (1 - t)) ^ k := by
    calc ((1 - s) / (1 - t)) ^ k * (2 * Nε * Wr ^ (-D) + η₀)
        = 2 * Nε * (Wr ^ (-D) * ((1 - s) / (1 - t)) ^ k) + η₀ * ((1 - s) / (1 - t)) ^ k := by ring
      _ ≤ _ := by
          have : Wr ^ (-D) * ((1 - s) / (1 - t)) ^ k ≤ Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k) :=
            mul_le_mul_of_nonneg_left hrk hWm0
          have h6 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Nε)
          linarith
  -- combine
  have hG : Wr ^ (-D) ≤ Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k) := by nlinarith
  have hLk : 1 ≤ (1 + Real.log L) ^ k := one_le_pow₀ hlam
  have hGm : 0 ≤ Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k := by positivity
  have hGf : 0 ≤ Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k) := by positivity
  have hηsum : η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
        rhoR L s t ^ k) + η₀ * ((1 - s) / (1 - t)) ^ k ≤ Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k) := by
    have : η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
          rhoR L s t ^ k) + η₀ * ((1 - s) / (1 - t)) ^ k =
        η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
          rhoR L s t ^ k + ((1 - s) / (1 - t)) ^ k) := by ring
    rw [this]
    exact hηT.trans hG
  have habs0 : 0 ≤ |c1 k κ| := abs_nonneg _
  calc c1 k κ * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) * rhoR L s t ^ k *
        (2 * (Nε * Λ + η₀)) + ((1 - s) / (1 - t)) ^ k * (2 * Nε * Wr ^ (-D) + η₀)
      ≤ 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε *
          (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) +
        (2 * Nε * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k))) +
        (η₀ * (2 * |c1 k κ| * (1 + Real.log L) ^ k * (Wr ^ τ) ^ (2 * (k - 1)) *
          rhoR L s t ^ k) + η₀ * ((1 - s) / (1 - t)) ^ k) := by linarith
    _ ≤ 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε *
          (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) +
        (2 * Nε * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k))) +
        (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by linarith
    _ ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
        (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k + Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by
        have hN3 : 0 ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) := by positivity
        have e1 : 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε *
            (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) ≤
            Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
              (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) := by
          have : 2 * |c1 k κ| * (1 + Real.log L) ^ k * Nε =
              Nε * ((2 * |c1 k κ|) * (1 + Real.log L) ^ k) := by ring
          rw [this]
          have h7 : Nε * ((2 * |c1 k κ|) * (1 + Real.log L) ^ k) ≤
              Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) := by
            apply mul_le_mul_of_nonneg_left _ hNε0
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith
          exact mul_le_mul_of_nonneg_right h7 hGm
        have e2 : 2 * Nε * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) +
            (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) ≤
            Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
              (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by
          have h8 : 2 * Nε + 1 ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) := by
            have : 3 * Nε ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) := by
              calc 3 * Nε = Nε * 3 := by ring
                _ ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) := by
                    apply mul_le_mul_of_nonneg_left _ hNε0
                    nlinarith
            linarith
          calc 2 * Nε * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) +
                (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k))
              = (2 * Nε + 1) * (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h8 hGf
        calc _ ≤ Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
              (Wr ^ (cCase3 𝔠 cC k * τ) * Λ * rhoR L s t ^ k) +
            Nε * ((2 * |c1 k κ| + 3) * (1 + Real.log L) ^ k) *
              (Wr ^ (-D) * Wr ^ (cCase3 𝔠 cC k)) := by linarith
          _ = _ := by ring

end DetAt2


section Events

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

private theorem c3_rangeU (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n := by
  filter_upwards [hc.hR] with n hn
  linarith [hc.hut n]

private theorem c3_integrable (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (n : ℕ)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n) (b : Fin k → Z2 (d.L n)) :
    Integrable (c3A d F E u n b) (Sizes.seqP d) :=
  c3A_integrable d hc.hκ hc.hδ F E u n (hc.hE n) hR (hc.hcoef n) b

/-- `𝔼𝒜` is sum-zero. -/
private theorem c3_abar_sumzero (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (n : ℕ)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n) :
    SumZero (d.L n) (fun b => ∫ ω, c3A d F E u n b ω ∂(Sizes.seqP d)) := by
  intro a₁
  rw [← integral_finsetSum _ (fun b _ => c3_integrable hc n hR b)]
  have h0 : ∀ ω, ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 (d.L n) => b 0 = a₁),
      c3A d F E u n b ω = 0 := fun ω => hc.hsz n (Sizes.seqHflow d n (u n) ω) a₁
  simp only [h0, integral_zero]

/-- The bounds of `𝔼𝒜` from the probability bounds (proof of `lem:sum_decay`): near and far. -/
private theorem c3_abar (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (n : ℕ)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n) (hΛn : 0 ≤ Λ n) {ε₁ Dp : ℝ}
    (hΩ1 : Sizes.seqP d (badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) ε₁ n) ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)))
    (hΩ2 : Sizes.seqP d (badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
        (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-D)) ε₁ n) ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp))) :
    (∀ b, ‖∫ ω, c3A d F E u n b ω ∂(Sizes.seqP d)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n + c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp)) ∧
    (∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖∫ ω, c3A d F E u n b ω ∂(Sizes.seqP d)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) +
          c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp)) := by
  have hN1 := c3_size_one d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hcr : ∀ b ω, ‖c3A d F E u n b ω‖ ≤ c3crude d κ K C' n := fun b ω => by
    unfold c3crude
    exact c3A_crude d hc.hκ hc.hδ F E u n (hc.hE n) hR (hc.hcoef n) b ω
  have hcr0 : 0 ≤ c3crude d κ K C' n := by
    have := hcr (fun _ => 0) (fun _ => 0)
    exact (norm_nonneg _).trans this
  have hDp0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-Dp) := Real.rpow_nonneg hN0.le _
  have hle : ∀ (S : Set (Sizes.SeqΩ d)),
      Sizes.seqP d S ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) →
        (Sizes.seqP d S).toReal ≤ ((d.size n : ℕ) : ℝ) ^ (-Dp) := fun S h =>
    ENNReal.toReal_le_of_le_ofReal hDp0 h
  constructor
  · intro b
    have h1 := c3_abar_bound (Sizes.seqP d) (c3A d F E u n b) (c3A_meas d F E u n b)
      (hcr b) (Λ' := ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n)
      (mul_nonneg (Real.rpow_nonneg hN0.le _) hΛn)
    refine h1.trans ?_
    have hsub : {ω | ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n < ‖c3A d F E u n b ω‖} ⊆
        badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
          (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) ε₁ n := by
      intro ω hω
      exact ⟨((), b), hω⟩
    have h2 := hle _ ((measure_mono hsub).trans hΩ1)
    have := mul_le_mul_of_nonneg_left h2 hcr0
    linarith
  · intro b hb
    have hW0 : (0 : ℝ) ≤ (d.W n : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1 := c3_abar_bound (Sizes.seqP d) (c3A d F E u n b) (c3A_meas d F E u n b)
      (hcr b) (Λ' := ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D))
      (mul_nonneg (Real.rpow_nonneg hN0.le _) hW0)
    refine h1.trans ?_
    have hsub : {ω | ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) < ‖c3A d F E u n b ω‖} ⊆
        badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
          (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
            (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
              then 1 else 0))
          (fun n _ _ => (d.W n : ℝ) ^ (-D)) ε₁ n := by
      intro ω hω
      refine ⟨((), b), ?_⟩
      simp only [hb, ↓reduceIte, mul_one]
      exact hω
    have h2 := hle _ ((measure_mono hsub).trans hΩ2)
    have := mul_le_mul_of_nonneg_left h2 hcr0
    linarith

end Events


section Main

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- The `clt-lemma` quantity of Case 2 (label `y`). -/
private def c3Xi1 (d : Sizes) {k K : ℕ} [NeZero k] (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ : ℝ) (E u t : ℕ → ℝ) (a : ∀ n, Fin k → Z2 (d.L n)) (cY : ℝ) (i : Fin k) (n : ℕ)
    (y : Z2 (d.L n)) (ω : Sizes.SeqΩ d) : ℝ :=
  ‖∑ b : Z2 (d.L n), c3Z1 (u n) (t n) (a n) y b *
    (cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
      ∫ ω', cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b
        ∂(Sizes.seqP d))‖

/-- The `clt-lemma` quantity of Case 1 (label `y`). -/
private def c3Xi2 (d : Sizes) {k K : ℕ} [NeZero k] (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ : ℝ) (E u t : ℕ → ℝ) (a : ∀ n, Fin k → Z2 (d.L n)) (cY : ℝ) (i : Fin k) (n : ℕ)
    (y : Z2 (d.L n)) (ω : Sizes.SeqΩ d) : ℝ :=
  ‖∑ b : Z2 (d.L n), c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) y b *
    (cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
      ∫ ω', cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b
        ∂(Sizes.seqP d))‖

/-- The translation of the `clt-lemma` quantities into the field `Y_i` of the tensor `𝒜(ω)`. -/
private theorem c3_translate (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (a : ∀ n, Fin k → Z2 (d.L n)) {cY : ℝ} (i : Fin k) (n : ℕ)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n) (hg : c3Good d k τ u t cY i n)
    (Zm : Matrix (Z2 (d.L n)) (Z2 (d.L n)) ℂ) (y : Z2 (d.L n)) (ω : Sizes.SeqΩ d) :
    ∑ b : Z2 (d.L n), Zm y b *
        (cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
          ∫ ω', cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b
            ∂(Sizes.seqP d)) =
      ∑ x : Z2 (d.L n), Zm y x *
        (c3Y (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i
            (fun b => c3A d F E u n b ω) x -
          c3Y (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i
            (fun b => ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have hev : ∀ ω' : Sizes.SeqΩ d,
      cltY (c3FYn d F τ u t a cY i n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') x =
        c3Y (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i
          (fun b => c3A d F E u n b ω') x := fun ω' =>
    c3FY_eval (F n) (u n) (t n) (a n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i
      (good := c3Good d k τ u t cY i n) hg (E n) (u n) (Sizes.seqHflow d n (u n) ω') x
  rw [hev ω]
  have hfun : (fun ω' : Sizes.SeqΩ d => cltY (c3FYn d F τ u t a cY i n) (E n) (u n)
      (Sizes.seqHflow d n (u n) ω') x) = fun ω' => c3Y (u n) (t n) (a n)
        (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ) i (fun b => c3A d F E u n b ω') x := funext hev
  rw [hfun, c3Y_integral (u n) (t n) (a n) _ i x (Sizes.seqP d) (c3A d F E u n)
    (fun b => c3_integrable hc n hR b)]

end Main


section Main2

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- The label decay, uniformly in the label. -/
private theorem c3_stoch_LD (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    StochDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
        (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-D)) := by
  refine stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (k : ℝ)) (Nat.cast_nonneg _) ?_
    hc.hLD
  refine Filter.Eventually.of_forall fun n => ?_
  have hcard : (Fintype.card (Unit × (Fin k → Z2 (d.L n))) : ℝ) = ((d.L n : ℝ) ^ 2) ^ k := by
    simp [Z2, Fintype.card_prod, ZMod.card, sq]
  rw [hcard, Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) (c3_L2_le_size d n) k

private theorem c3_hW3 (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ (d.W n : ℝ) ^ τ := by
  have hWt : Tendsto (fun n : ℕ => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop.2 fun X => c3_W_large d hc.hN hc.h𝔠 hc.hW X
  have hKw : Tendsto (fun n : ℕ => (d.W n : ℝ) ^ τ) atTop atTop :=
    (tendsto_rpow_atTop hc.hτ).comp hWt
  exact hKw.eventually_ge_atTop 3

private theorem c3_good_ev (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) {cY : ℝ}
    (hS : ∀ᶠ n : ℕ in atTop, c3Sn d k τ u t n ≤ ((d.size n : ℕ) : ℝ) ^ cY) (i : Fin k)
    (hi : i ≠ 0) : ∀ᶠ n : ℕ in atTop, c3Good d k τ u t cY i n := by
  filter_upwards [c3_hW3 hc, hS] with n h1 h2 using ⟨hi, h1, h2⟩

/-- The `η₀`-coefficient of the non-alternating case. -/
private def c3TetaN (d : Sizes) (k : ℕ) (τ : ℝ) (u t : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  2 * |c| * c3lam d n ^ k * c3Kw d τ n ^ (2 * (k - 1)) * c3Rn d u t n ^ k + c3rn u t n ^ k

private theorem pb_TetaN (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (c : ℝ) :
    PolyB d (c3TetaN d k τ u t c) := by
  have hN := hc.hN
  have h1 := (((PolyB.const hN (by positivity : (0 : ℝ) ≤ 2 * |c|)).mul hN
    ((pb_lam hc).pow hN k)).mul hN ((pb_Kw hc).pow hN (2 * (k - 1)))).mul hN
    ((pb_R hc).pow hN k)
  exact h1.add hN ((pb_r hc).pow hN k)

private theorem c3_constN (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (c : ℝ) :
    ∃ mN : ℝ, 0 ≤ mN ∧ ∀ᶠ n : ℕ in atTop,
      c3TetaN d k τ u t c n * c3crude d κ K C' n ≤ ((d.size n : ℕ) : ℝ) ^ mN := by
  obtain ⟨mN, hmN, h⟩ := ((pb_TetaN hc c).mul hc.hN (pb_crude hc)).exists_nonneg hc.hN
  exact ⟨mN, hmN, h⟩

end Main2


section Main3

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- **The alternating case at `(n, ω)`**, from the outputs of the `clt-lemma` statements. -/
private theorem c3_alt_seq {cC : ℝ} (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (hXe : XiEntryBound) (hXr : XiRowBound) (hXd : XiFirstDiff) (σ : ℕ → Fin k → Bool)
    (a : ∀ n, Fin k → Z2 (d.L n)) {cY Dc ε₁ Dp : ℝ} (n : ℕ) (hn : C3Scale d 𝔠 t n)
    (hΛn : 0 ≤ Λ n) (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n)
    (hgood : ∀ i, i ≠ 0 → c3Good d k τ u t cY i n) (hσ : ∀ i, σ n i ≠ σ n (i + 1))
    (hε₁ : 0 < ε₁) (ω : Sizes.SeqΩ d)
    (hb𝒜 : ∀ b, ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n)
    (hbfar : ∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D))
    (hĀ1 : ∀ b, ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n + c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp))
    (hĀ2 : ∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) +
          c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp))
    (hB1 : ∀ i, i ≠ 0 → c3Xi1 d F τ E u t a cY i n (a n i) ω ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (u n) *
        (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc)))
    (hB2 : ∀ i, i ≠ 0 → c3Xi2 d F τ E u t a cY i n (a n 0) ω ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ *
        ((Finset.univ.sup' Finset.univ_nonempty fun b : Z2 (d.L n) =>
          ‖c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) (a n 0) b‖) *
          ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (t n) * ellT (d.L n) (u n) *
            (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc))))
    (hQ : c3Qt d k τ u t n * c3Xn d τ n ≤ 1)
    (hWdTD : (d.W n : ℝ) ^ (-Dc) * c3TD d k u t n ≤ (d.W n : ℝ) ^ (-D))
    (hηTη : c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) * c3Teta d k τ u t n ≤
      (d.W n : ℝ) ^ (-D)) :
    ‖Ugen (d.L n) (E n) (σ n) (u n) (t n)
        (fun b => c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) (a n)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * ((c3A1 k + c3F k + 2) * (1 + Real.log (d.L n : ℝ)) ^ k) *
        ((d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n * rhoR (d.L n) (u n) (t n) ^ k +
          (d.W n : ℝ) ^ (-D) * (d.W n : ℝ) ^ (cCase3 𝔠 cC k)) := by
  obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
  have hEn : |E n| ≤ 2 := by linarith [hc.hE n, hc.hκ]
  have hkk : 2 ≤ k := hc.hk
  have hNε : 1 ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁.le
  have hcr0 : 0 ≤ c3crude d κ K C' n := by
    have := c3A_crude d hc.hκ hc.hδ F E u n (hc.hE n) hR (hc.hcoef n) (fun _ => 0) ω
    exact (norm_nonneg _).trans this
  have hη : 0 ≤ c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) :=
    mul_nonneg hcr0 (Real.rpow_nonneg (by linarith) _)
  have hZ2ne : (Finset.univ : Finset (Z2 (d.L n))).Nonempty := Finset.univ_nonempty
  have hQ' : 2 * ((k - 1 : ℕ) : ℝ) * ((d.L n : ℝ) ^ 2 * c3w2 (d.L n) (t n) *
      c3e (d.L n) (u n) (t n) * Real.exp (-((d.W n : ℝ) ^ τ) / 20000) *
      c3SY (d.L n) k (u n) (t n) (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ)) ≤ 1 := by
    calc _ = c3Qt d k τ u t n * c3Xn d τ n := by
          unfold c3Qt c3Xn c3w2n c3en c3Sn c3Kw
          ring
      _ ≤ 1 := hQ
  refine c3_alt_det hXe hXr hXd hL hkk hu0 hut htl hEn (σ n) hσ (a n) (Nn := ((d.size n : ℕ) : ℝ))
    (𝔠 := 𝔠) (cC := cC) (D := D) (Dc := Dc) hc.hτ hW1 hc.h𝔠 hN1 hL2 h1t hn.2.2
    (fun b => c3A d F E u n b ω) (fun b => ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) hNε hΛn hη
    (fun b => (hb𝒜 b).trans (by linarith)) hĀ1 (fun b hb => ?_) ?_
    (Zs := Finset.univ.sup' hZ2ne fun b : Z2 (d.L n) =>
      ‖c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) (a n 0) b‖) ?_ ?_ ?_ ?_ hQ' ?_ ?_
  · -- far decay of `𝒜 - 𝔼𝒜`
    calc ‖c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖
        ≤ ‖c3A d F E u n b ω‖ + ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ := norm_sub_le _ _
      _ ≤ 2 * ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) +
          c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) := by
        linarith [hbfar b hb, hĀ2 b hb]
  · -- sum-zero
    intro a₁
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 (d.L n) => b 0 = a₁),
        c3A d F E u n b ω = 0 := hc.hsz n (Sizes.seqHflow d n (u n) ω) a₁
    have h2 : ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 (d.L n) => b 0 = a₁),
        ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d) = 0 := c3_abar_sumzero hc n hR a₁
    change ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 (d.L n) => b 0 = a₁),
      (c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) = 0
    rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
  · exact Finset.le_sup'_of_le _ (Finset.mem_univ (a n 0)) le_rfl |>.trans' (norm_nonneg _)
  · exact Finset.sup'_le _ _ fun b _ => c3_Z2_norm_le hXe hL hu0 hut htl _ (a n 0) b
  · intro i hi
    have := hB1 i hi
    unfold c3Xi1 at this
    rw [c3_translate hc a i n hR (hgood i hi) (c3Z1 (u n) (t n) (a n)) (a n i) ω] at this
    exact this
  · intro i hi
    have := hB2 i hi
    unfold c3Xi2 at this
    rw [c3_translate hc a i n hR (hgood i hi)
      (c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ)) (a n 0) ω] at this
    exact this
  · exact hWdTD
  · exact hηTη

end Main3


section Main4

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- **The non-alternating case at `(n, ω)`** (Case 1 applied `ω`-wise on the decay event). -/
private theorem c3_non_seq {cC : ℝ} {c1 : ℕ → ℝ → ℝ}
    (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F) (hU : UgenCase1Explicit c1)
    (σ : ℕ → Fin k → Bool) (a : ∀ n, Fin k → Z2 (d.L n)) {ε₁ Dp : ℝ} (n : ℕ)
    (hn : C3Scale d 𝔠 t n) (hΛn : 0 ≤ Λ n) (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u n)
    (hε₁ : 0 < ε₁) (ω : Sizes.SeqΩ d)
    (hb𝒜 : ∀ b, ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n)
    (hbfar : ∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D))
    (hĀ1 : ∀ b, ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * Λ n + c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp))
    (hĀ2 : ∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) +
          c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp))
    (hrep : ∃ i : Fin k, σ n i = σ n (i + 1))
    (hηT : c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) * c3TetaN d k τ u t (c1 k κ) n ≤
      (d.W n : ℝ) ^ (-D)) :
    ‖Ugen (d.L n) (E n) (σ n) (u n) (t n)
        (fun b => c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) (a n)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε₁ * ((2 * |c1 k κ| + 3) * (1 + Real.log (d.L n : ℝ)) ^ k) *
        ((d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n * rhoR (d.L n) (u n) (t n) ^ k +
          (d.W n : ℝ) ^ (-D) * (d.W n : ℝ) ^ (cCase3 𝔠 cC k)) := by
  obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
  have hkk : 2 ≤ k := hc.hk
  have hNε : 1 ≤ ((d.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁.le
  have hcr0 : 0 ≤ c3crude d κ K C' n := by
    have := c3A_crude d hc.hκ hc.hδ F E u n (hc.hE n) hR (hc.hcoef n) (fun _ => 0) ω
    exact (norm_nonneg _).trans this
  have hη : 0 ≤ c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) :=
    mul_nonneg hcr0 (Real.rpow_nonneg (by linarith) _)
  refine c3_nonalt_det hU hL hkk hc.hκ hu0 hut htl (hc.hE n) (σ n) hrep (a n)
    (Nn := ((d.size n : ℕ) : ℝ)) (𝔠 := 𝔠) (cC := cC) (D := D) hc.hτ hW1 hc.h𝔠 hN1 h1t hn.2.2
    (fun b => c3A d F E u n b ω) (fun b => ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) hNε hΛn hη
    (fun b => (hb𝒜 b).trans (by linarith)) hĀ1 (fun b hb => ?_) ?_
  · calc ‖c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖
        ≤ ‖c3A d F E u n b ω‖ + ‖∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)‖ := norm_sub_le _ _
      _ ≤ 2 * ((d.size n : ℕ) : ℝ) ^ ε₁ * (d.W n : ℝ) ^ (-D) +
          c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) := by
        linarith [hbfar b hb, hĀ2 b hb]
  · exact hηT

end Main4


section Main5

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- The failure event of Case 2 for the label `i`. -/
private def c3B1 (d : Sizes) {k K : ℕ} [NeZero k] (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ : ℝ) (E u t Λ : ℕ → ℝ) (a : ∀ n, Fin k → Z2 (d.L n)) (cY cC Dc ε₁ : ℝ) (i : Fin k)
    (n : ℕ) : Set (Sizes.SeqΩ d) :=
  {ω | ((d.size n : ℕ) : ℝ) ^ ε₁ * ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (u n) *
      (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc)) < c3Xi1 d F τ E u t a cY i n (a n i) ω}

/-- The failure event of Case 1 for the label `i`. -/
private def c3B2 (d : Sizes) {k K : ℕ} [NeZero k] (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ : ℝ) (E u t Λ : ℕ → ℝ) (a : ∀ n, Fin k → Z2 (d.L n)) (cY cC Dc ε₁ : ℝ) (i : Fin k)
    (n : ℕ) : Set (Sizes.SeqΩ d) :=
  {ω | ((d.size n : ℕ) : ℝ) ^ ε₁ *
      ((Finset.univ.sup' Finset.univ_nonempty fun b : Z2 (d.L n) =>
        ‖c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) (a n 0) b‖) *
        ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (t n) * ellT (d.L n) (u n) *
          (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc))) < c3Xi2 d F τ E u t a cY i n (a n 0) ω}

/-- The union bound of the `2k` failure events. -/
private theorem c3_union_arith {Nn Dp D₁ : ℝ} {k : ℕ} (hN1 : 1 ≤ Nn) (hk2 : 2 * (k : ℝ) ≤ Nn)
    (hD : D₁ + 1 ≤ Dp) :
    2 * (k : ℝ) * Nn ^ (-Dp) ≤ Nn ^ (-D₁) := by
  have hN0 : 0 < Nn := by linarith
  have h1 : Nn ^ (-Dp) ≤ Nn ^ (-(D₁ + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : Nn ^ (-(D₁ + 1)) = Nn ^ (-D₁) * Nn⁻¹ := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h3 : 0 ≤ Nn ^ (-D₁) := Real.rpow_nonneg hN0.le _
  have hk0 : 0 ≤ 2 * (k : ℝ) := by positivity
  calc 2 * (k : ℝ) * Nn ^ (-Dp) ≤ 2 * (k : ℝ) * (Nn ^ (-D₁) * Nn⁻¹) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hk0
    _ = Nn ^ (-D₁) * (2 * (k : ℝ) / Nn) := by field_simp
    _ ≤ Nn ^ (-D₁) * 1 := by
        apply mul_le_mul_of_nonneg_left _ h3
        rw [div_le_one hN0]; exact hk2
    _ = Nn ^ (-D₁) := mul_one _

end Main5



private theorem c3A1_nonneg (k : ℕ) : 0 ≤ c3A1 k := by
  unfold c3A1 c3cB c3cP
  have : 0 ≤ cProp5 := by unfold cProp5; norm_num
  positivity

private theorem c3F_nonneg (k : ℕ) : 0 ≤ c3F k := by
  unfold c3F
  have : 0 ≤ cProp5 := by unfold cProp5; norm_num
  positivity

section Main6

variable {d : Sizes} {κ 𝔠 δ : ℝ} {k K : ℕ} [NeZero k] {C' τ D : ℝ} {E s₀ t₀ u t Λ : ℕ → ℝ}
  {F : ∀ n, LocalForm (d.L n) (d.W n) k K}

/-- `T · N^{-Dp} ≤ W^{-D}` when `T ≤ N^m` and `Dp ≥ m + D`. -/
private theorem c3_eta_absorb {Nn Wr Dp D m Tc : ℝ} (hN1 : 1 ≤ Nn) (hW : 1 ≤ Wr) (hWN : Wr ≤ Nn)
    (hD : 0 < D) (hDp : m + D ≤ Dp) (hTc : Tc ≤ Nn ^ m) (hT0 : 0 ≤ Tc) :
    Tc * Nn ^ (-Dp) ≤ Wr ^ (-D) := by
  have hN0 : 0 < Nn := by linarith
  have hW0 : 0 < Wr := by linarith
  calc Tc * Nn ^ (-Dp) ≤ Nn ^ m * Nn ^ (-Dp) :=
        mul_le_mul_of_nonneg_right hTc (Real.rpow_nonneg hN0.le _)
    _ = Nn ^ (m + -Dp) := by rw [← Real.rpow_add hN0]
    _ ≤ Nn ^ (-D) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ ≤ Wr ^ (-D) := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)

/-- The main proof: `SumDecayCase3Prec`'s conclusion for one `(F, σ, Λ)`. -/
private theorem c3_main {cC : ℝ} {c1 : ℕ → ℝ → ℝ}
    (hc : C3Ctx d κ 𝔠 δ C' τ D E s₀ t₀ u t Λ F)
    (h1 : CltCase1Prec d κ 𝔠 δ cC) (h2 : CltCase2Prec d κ 𝔠 δ cC) (hU : UgenCase1Explicit c1)
    (hXe : XiEntryBound) (hXr : XiRowBound) (hXd : XiFirstDiff) (σ : ℕ → Fin k → Bool) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖Ugen (d.L n) (E n) (σ n) (u n) (t n)
        (fun b => c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) p.2‖)
      (fun n _ _ => (d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n *
          ratioR (d.L n) (E n) (u n) (t n) ^ k + (d.W n : ℝ) ^ (-D + cCase3 𝔠 cC k)) := by
  classical
  rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size
    (fun n => ⟨((), fun _ => 0)⟩)]
  intro a₀ ε hε D₁ hD₁
  obtain ⟨cY, mc, m0, mq, hcY, hmc, hm0, hmq, hS, hTD, hTe, hQt⟩ := c3_consts hc
  obtain ⟨mN, hmN, hTeN⟩ := c3_constN hc (c1 k κ)
  obtain ⟨a, ha⟩ : ∃ a : ∀ n, Fin k → Z2 (d.L n), a = fun n => (a₀ n).2 := ⟨_, rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : ℝ, Dc = D + mc / 𝔠 := ⟨_, rfl⟩
  obtain ⟨Dp, hDp⟩ : ∃ Dp : ℝ, Dp = max (D₁ + 1) (max m0 mN + D) := ⟨_, rfl⟩
  have hε₁ : 0 < ε / 2 := by linarith
  have hD0 := hc.hD
  have hDc0 : 0 < Dc := by
    have : 0 ≤ mc / 𝔠 := div_nonneg hmc hc.h𝔠.le
    linarith
  have hDp1 : D₁ + 1 ≤ Dp := by rw [hDp]; exact le_max_left _ _
  have hDp2 : max m0 mN + D ≤ Dp := by rw [hDp]; exact le_max_right _ _
  have hDp0 : 0 < Dp := by linarith
  -- eventual facts
  have hΛnn : ∀ᶠ n : ℕ in atTop, 0 ≤ Λ n :=
    c3_Lambda_nonneg d hc.hN Λ
      (fun n p ω => ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun _ _ _ => norm_nonneg _) hc.hΛ
  have hΩ1 := c3_stoch_Lambda hc (ε / 2) hε₁ Dp hDp0
  have hΩ2 := c3_stoch_LD hc (ε / 2) hε₁ Dp hDp0
  have hgoodI : ∀ i ∈ Finset.univ.erase (0 : Fin k), ∀ᶠ n : ℕ in atTop,
      c3Good d k τ u t cY i n := fun i hi => c3_good_ev hc hS i (Finset.ne_of_mem_erase hi)
  have hgoodAll : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.univ.erase (0 : Fin k),
      c3Good d k τ u t cY i n := by
    rw [Filter.eventually_all_finset]; exact hgoodI
  have hEvB : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.univ.erase (0 : Fin k),
      Sizes.seqP d (c3B1 d F τ E u t Λ a cY cC Dc (ε / 2) i n) ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) ∧
      Sizes.seqP d (c3B2 d F τ E u t Λ a cY cC Dc (ε / 2) i n) ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have e1 := c3_pin2 hc h2 hXe hXd a hcY hDc0 i (hgoodI i hi) (ε / 2) hε₁ Dp hDp0
    have e2 := c3_pin1 hc h1 hXe hXd a hcY hDc0 i (hgoodI i hi) (ε / 2) hε₁ Dp hDp0
    filter_upwards [e1, e2] with n hn1 hn2
    exact ⟨hn1 ((), a n i), hn2 ((), a n 0)⟩
  have hpoly : ∀ᶠ n : ℕ in atTop,
      |(c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3)| * (1 + Real.log (d.L n : ℝ)) ^ k ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 2) := c3_polylog d hc.hN _ k hε₁
  have hexp : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ mq * c3Xn d τ n ≤ 1 :=
    c3_poly_exp hc hmq
  have hN2k : ∀ᶠ n : ℕ in atTop, 2 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) :=
    hc.hN.eventually_ge_atTop _
  filter_upwards [c3_scale hc, hΛnn, c3_rangeU hc, hΩ1, hΩ2, hEvB, hgoodAll, hpoly, hexp, hTe,
    hTeN, hTD, hQt, hN2k, (pb_Teta hc).1, (pb_TetaN hc (c1 k κ)).1, (pb_crude hc).1, (pb_TD hc).1,
    (pb_Qt hc).1] with n hn hΛ hR hΩ1n hΩ2n hBn hgood hpolyn hexpn hTen hTeNn hTDn hQtn hN2n
    hTeta0 hTetaN0 hcr0 hTD0 hQt0
  obtain ⟨hL, hu0, hut, htl, hN1, hL2, h1t, hW1, hWN, hKw1⟩ := c3_at hc hn
  have hNe : ∀ x : ℝ, 0 ≤ x → 0 ≤ x := fun x hx => hx
  -- the union bound
  have hx0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-Dp) := Real.rpow_nonneg (by linarith) _
  have hPbad : Sizes.seqP d
      (badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
          (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) (ε / 2) n ∪
        badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
          (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
            (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
              then 1 else 0)) (fun n _ _ => (d.W n : ℝ) ^ (-D)) (ε / 2) n ∪
        ⋃ i ∈ Finset.univ.erase (0 : Fin k),
          (c3B1 d F τ E u t Λ a cY cC Dc (ε / 2) i n ∪ c3B2 d F τ E u t Λ a cY cC Dc (ε / 2) i n))
      ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
    calc Sizes.seqP d _ ≤ Sizes.seqP d (badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
            (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) (ε / 2) n ∪
          badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
            (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
              (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
                then 1 else 0)) (fun n _ _ => (d.W n : ℝ) ^ (-D)) (ε / 2) n) +
          Sizes.seqP d (⋃ i ∈ Finset.univ.erase (0 : Fin k),
            (c3B1 d F τ E u t Λ a cY cC Dc (ε / 2) i n ∪
              c3B2 d F τ E u t Λ a cY cC Dc (ε / 2) i n)) := measure_union_le _ _
      _ ≤ (ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) +
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp))) +
          ∑ i ∈ Finset.univ.erase (0 : Fin k), (ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) +
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp))) := by
          refine add_le_add ((measure_union_le _ _).trans (add_le_add hΩ1n hΩ2n)) ?_
          refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          exact (measure_union_le _ _).trans (add_le_add (hBn i hi).1 (hBn i hi).2)
      _ = ENNReal.ofReal (2 * (k : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-Dp)) := by
          have e1 : ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) +
              ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) =
              ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp) + ((d.size n : ℕ) : ℝ) ^ (-Dp)) :=
            (ENNReal.ofReal_add hx0 hx0).symm
          simp only [e1]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
            ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by positivity)]
          congr 1
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          have hk1 : 1 ≤ k := by have := hc.hk; omega
          have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk1]; simp
          rw [this]; ring
      _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) :=
          ENNReal.ofReal_le_ofReal (c3_union_arith hN1 hN2n hDp1)
  refine le_trans (measure_mono ?_) hPbad
  intro ω hω
  by_contra hωBad
  obtain ⟨_, hlt0⟩ := hω
  have hlt : ((d.size n : ℕ) : ℝ) ^ ε * ((d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n *
      ratioR (d.L n) (E n) (u n) (t n) ^ k + (d.W n : ℝ) ^ (-D + cCase3 𝔠 cC k)) <
      ‖Ugen (d.L n) (E n) (σ n) (u n) (t n)
        (fun b => c3A d F E u n b ω - ∫ ω', c3A d F E u n b ω' ∂(Sizes.seqP d)) (a₀ n).2‖ := hlt0
  have hω1 : ω ∉ badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖) (fun n _ _ => Λ n) (ε / 2) n :=
    fun h => hωBad (Or.inl (Or.inl h))
  have hω2 : ω ∉ badSetAt d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖c3A d F E u n p.2 ω‖ *
        (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
          then 1 else 0)) (fun n _ _ => (d.W n : ℝ) ^ (-D)) (ε / 2) n :=
    fun h => hωBad (Or.inl (Or.inr h))
  have hω3 : ∀ i ∈ Finset.univ.erase (0 : Fin k),
      ω ∉ c3B1 d F τ E u t Λ a cY cC Dc (ε / 2) i n ∧
        ω ∉ c3B2 d F τ E u t Λ a cY cC Dc (ε / 2) i n := fun i hi =>
    ⟨fun h => hωBad (Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Or.inl h⟩)),
     fun h => hωBad (Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Or.inr h⟩))⟩
  have hb𝒜 : ∀ b, ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) * Λ n := by
    intro b
    by_contra hb
    exact hω1 ⟨((), b), not_le.1 hb⟩
  have hbfar : ∀ b, ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) b : ℝ) →
      ‖c3A d F E u n b ω‖ ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) * (d.W n : ℝ) ^ (-D) := by
    intro b hb
    by_contra hcon
    refine hω2 ⟨((), b), ?_⟩
    simp only [hb, ↓reduceIte, mul_one]
    exact not_le.1 hcon
  obtain ⟨hĀ1, hĀ2⟩ := c3_abar hc n hR hΛ hΩ1n hΩ2n
  have hae : a n = (a₀ n).2 := by rw [ha]
  have hE2 : |E n| < 2 := by linarith [hc.hE n, hc.hκ]
  have hratio : ratioR (d.L n) (E n) (u n) (t n) = rhoR (d.L n) (u n) (t n) := c3_ratioR_eq hE2
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hgeq : (d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n *
      ratioR (d.L n) (E n) (u n) (t n) ^ k + (d.W n : ℝ) ^ (-D + cCase3 𝔠 cC k) =
      (d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n * rhoR (d.L n) (u n) (t n) ^ k +
        (d.W n : ℝ) ^ (-D) * (d.W n : ℝ) ^ (cCase3 𝔠 cC k) := by
    rw [hratio, Real.rpow_add hW0]
  -- the coefficient
  have hNe1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 hε₁.le
  have hcA0 := c3A1_nonneg k
  have hcF0 := c3F_nonneg k
  have hc10 : 0 ≤ |c1 k κ| := abs_nonneg _
  have hlam := c3_lam_one (d.L n)
  have hlamk0 : 0 ≤ (1 + Real.log (d.L n : ℝ)) ^ k := by positivity
  have hNε : ((d.size n : ℕ) : ℝ) ^ (ε / 2) * (((c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3)) *
      (1 + Real.log (d.L n : ℝ)) ^ k) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
    have hcp : 0 ≤ (c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3) := by positivity
    rw [abs_of_nonneg hcp] at hpolyn
    calc ((d.size n : ℕ) : ℝ) ^ (ε / 2) * (((c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3)) *
          (1 + Real.log (d.L n : ℝ)) ^ k)
        ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((d.size n : ℕ) : ℝ) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left hpolyn (by linarith)
      _ = ((d.size n : ℕ) : ℝ) ^ ε := by
          rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hGm0 : 0 ≤ (d.W n : ℝ) ^ (cCase3 𝔠 cC k * τ) * Λ n * rhoR (d.L n) (u n) (t n) ^ k := by
    have := KernelExpand_one_le_rhoR hL hut htl
    positivity
  have hGf0 : 0 ≤ (d.W n : ℝ) ^ (-D) * (d.W n : ℝ) ^ (cCase3 𝔠 cC k) := by positivity
  -- the two cases
  by_cases hrep : ∃ i : Fin k, σ n i = σ n (i + 1)
  · have hηT : c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) *
        c3TetaN d k τ u t (c1 k κ) n ≤ (d.W n : ℝ) ^ (-D) := by
      have := c3_eta_absorb hN1 hW1 hWN hc.hD (m := mN) (Dp := Dp)
        (by linarith [le_max_right m0 mN]) hTeNn (mul_nonneg hTetaN0 hcr0)
      calc _ = (c3TetaN d k τ u t (c1 k κ) n * c3crude d κ K C' n) *
            ((d.size n : ℕ) : ℝ) ^ (-Dp) := by ring
        _ ≤ _ := this
    have hbd := c3_non_seq (cC := cC) hc hU σ a n hn hΛ hR hε₁ ω hb𝒜 hbfar hĀ1 hĀ2 hrep hηT
    rw [hae] at hbd
    rw [hgeq] at hlt
    have hcx : (2 * |c1 k κ| + 3) ≤ (c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3) := by linarith
    have h5 : ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((2 * |c1 k κ| + 3) *
        (1 + Real.log (d.L n : ℝ)) ^ k) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
      refine le_trans ?_ hNε
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hcx hlamk0
    have h6 := mul_le_mul_of_nonneg_right h5 (add_nonneg hGm0 hGf0)
    linarith
  · push Not at hrep
    have hTQ : c3Qt d k τ u t n * c3Xn d τ n ≤ 1 := by
      have hX0 : 0 ≤ c3Xn d τ n := (Real.exp_pos _).le
      calc c3Qt d k τ u t n * c3Xn d τ n ≤ ((d.size n : ℕ) : ℝ) ^ mq * c3Xn d τ n :=
            mul_le_mul_of_nonneg_right hQtn hX0
        _ ≤ 1 := hexpn
    have hWdTD : (d.W n : ℝ) ^ (-Dc) * c3TD d k u t n ≤ (d.W n : ℝ) ^ (-D) := by
      have h7 : ((d.size n : ℕ) : ℝ) ^ mc ≤ (d.W n : ℝ) ^ (mc / 𝔠) :=
        c3_rpow_le (by linarith) hc.h𝔠 hn.2.2 hmc
      calc (d.W n : ℝ) ^ (-Dc) * c3TD d k u t n
          ≤ (d.W n : ℝ) ^ (-Dc) * (d.W n : ℝ) ^ (mc / 𝔠) :=
            mul_le_mul_of_nonneg_left (hTDn.trans h7) (Real.rpow_nonneg hW0.le _)
        _ = (d.W n : ℝ) ^ (-D) := by
            rw [← Real.rpow_add hW0, hDc]; congr 1; ring
    have hηTη : c3crude d κ K C' n * ((d.size n : ℕ) : ℝ) ^ (-Dp) * c3Teta d k τ u t n ≤
        (d.W n : ℝ) ^ (-D) := by
      have := c3_eta_absorb hN1 hW1 hWN hc.hD (m := m0) (Dp := Dp)
        (by linarith [le_max_left m0 mN]) hTen (mul_nonneg hTeta0 hcr0)
      calc _ = (c3Teta d k τ u t n * c3crude d κ K C' n) * ((d.size n : ℕ) : ℝ) ^ (-Dp) := by
            ring
        _ ≤ _ := this
    have hB1' : ∀ i, i ≠ 0 → c3Xi1 d F τ E u t a cY i n (a n i) ω ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (u n) *
          (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc)) := by
      intro i hi
      have := (hω3 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)).1
      unfold c3B1 at this
      exact not_lt.1 this
    have hB2' : ∀ i, i ≠ 0 → c3Xi2 d F τ E u t a cY i n (a n 0) ω ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 2) *
          ((Finset.univ.sup' Finset.univ_nonempty fun b : Z2 (d.L n) =>
            ‖c3Z2 (u n) (t n) (ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ) (a n 0) b‖) *
            ((d.W n : ℝ) ^ (cC * (2 * τ)) * ellT (d.L n) (t n) * ellT (d.L n) (u n) *
              (c3Sn d k τ u t n * Λ n) + (d.W n : ℝ) ^ (-Dc))) := by
      intro i hi
      have := (hω3 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)).2
      unfold c3B2 at this
      exact not_lt.1 this
    have hbd := c3_alt_seq (cC := cC) (cY := cY) (Dc := Dc) (Dp := Dp) hc hXe hXr hXd σ a n hn hΛ hR
      (fun i hi => hgood i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)) hrep hε₁ ω hb𝒜 hbfar
      hĀ1 hĀ2 hB1' hB2' hTQ hWdTD hηTη
    rw [hae] at hbd
    rw [hgeq] at hlt
    have hcx : (c3A1 k + c3F k + 2) ≤ (c3A1 k + c3F k + 2) + (2 * |c1 k κ| + 3) := by linarith
    have h5 : ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((c3A1 k + c3F k + 2) *
        (1 + Real.log (d.L n : ℝ)) ^ k) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
      refine le_trans ?_ hNε
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hcx hlamk0
    have h6 := mul_le_mul_of_nonneg_right h5 (add_nonneg hGm0 hGf0)
    linarith

end Main6


/-! ## Part 10: the statements -/

variable (d : Sizes)

/-- **The bridge to Case 3**: the two `clt-lemma` cases, the explicit Case 1 kernel
bound and the `Ξ` kernel statements give `SumDecayCase3Prec` with `C = cCase3 𝔠 cC`
(`sum_res_3`, proof of `lem:sum_decay`). -/
theorem bridgeCase3 : BridgeCase3 d := by
  intro cC c1 κ 𝔠 δ h1 h2 hU hXe hXr hXd _hXd2 _hExp hκ h𝔠 hδ k K _ hk C' τ D hC' hτ hD E s₀ t₀
    u t Λ F σ hE hs₀ hsu hut₀ hut ht hN hW hR hLoc hDec hV3 hcoef hloc hsz hLD hΛ
  exact c3_main ⟨hκ, h𝔠, hδ, hk, hC', hτ, hD, hE, hs₀, hsu, hut₀, hut, ht, hN, hW, hR, hLoc,
    hDec, hV3, hcoef, hloc, hsz, hLD, hΛ⟩ h1 h2 hU hXe hXr hXd σ

/-- **`SumDecayCase3Prec`**: `SumDecayCase3Prec d κ 𝔠 δ (cCase3 𝔠 4)`, unconditionally: the
composition of `bridgeCase3` with `cltCase1Prec`, `cltCase2Prec` (`cC = 4`), `ugenCase1Explicit`
and the `Ξ`, `ExpInvSum` kernel theorems. -/
theorem sumDecayCase3Prec (κ 𝔠 δ : ℝ) : SumDecayCase3Prec d κ 𝔠 δ (cCase3 𝔠 4) :=
  bridgeCase3 d 4 cCase1 κ 𝔠 δ (cltCase1Prec d κ 𝔠 δ) (cltCase2Prec d κ 𝔠 δ)
    ugenCase1Explicit xiEntryBound xiRowBound xiFirstDiff xiSecondDiff expInvSum






end RBM.Evol

end
