/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.AvgPins
import RBM2D.Path.Step2Local

/-!
# The local law at a deterministic control: `LocalLawDetThm`

The statement `LocalLawDetThm` of `Green/AvgPins.lean`, proved outright:
under (`asGMc`) (`AsGMcSeq d E t c`) and the deterministic loop control
`LoopDetSeq d E t Ψ` (`max_{a,b} |𝓛_{t,(+,-),(a,b)}| ≺ Ψ²`) with the floor `W_n⁻¹ ≤ Ψ_n`,
`|(G_t - m)_{ij}| ≺ Ψ` per time (`LocalLawDetSeq`).  Source: [YY_25], proof of (`GavLGEX`):
"`max_{ij}|G_ij - m δ_ij|² ≺ Ψ² := max_a 𝓛`".

## Method

1. `LocalLaw_gexRHS_le_maxLoopPM`: `gexRHS ≤ 25 · maxLoopPM + W⁻²` (`5 × 5` points of the two
   `L¹` unit balls, `sbSupport`; the diagonal-block term `W⁻²`);
2. `LoopDetSeq` and the grid union over `(a, b)` (`L⁴ ≤ N²`) give `maxLoopPM ≺ Ψ²`
   (`LocalLaw_maxLoop_dom`, at any index type);
3. `gijSeq_of_asGMc` and `giiSeq_of_asGMc`: `offSq ≺ gexRHS`, `diagSq ≺ maxLoopPM`;
   transitivity (`LocalLaw_trans`, `25 + 1 = 26` absorbed by `N^{τ/2} ≥ 26`) gives
   `offSq ≺ Ψ²`, `diagSq ≺ Ψ²`;
4. `sqrt_of`, the bridge `step2Local_llErrMat_eq` and the case split `i = j` / `i ≠ j`
   (`stochDom_of_forall_or`) give `LocalLawDetSeq`.

The helpers `LocalLaw_mem_sbSupport`, `LocalLaw_near_card`, `LocalLaw_gexRHS_le` are copies of the
`private` `Step2Local_mem_sbSupport`, `Step2Local_near_card`, `Step2Local_gexRHS_le`
(`Path/Step2Local.lean`), and `LocalLaw_maxLoop_dom` is the bound `max 𝓛 ≺ Ψ²`
from `LoopDetSeq` at a general index type.  The hypotheses of the
theorem are exactly those of `LocalLawDetThm`: no hypothesis is added.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Green
open scoped NNReal ENNReal

/-! ## 1. The deterministic bound `gexRHS ≤ 25 · maxLoopPM + W⁻²` -/

section Gex

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem LocalLaw_zdist_le_one (hL : 3 ≤ L) {x : ZMod L} (h : zdist L x ≤ 1) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hx : x.val < L := ZMod.val_lt x
  simp only [zdist] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  have hneg : (-1 : ZMod L).val = L - 1 := by
    rw [ZMod.neg_val, ite_eq_right h1, hval]
  by_cases hs : x.val ≤ 1
  · rcases (by omega : x.val = 0 ∨ x.val = 1) with h0 | h0
    · left
      exact (ZMod.val_eq_zero x).1 h0
    · right; left
      exact ZMod.val_injective L (by rw [h0, hval])
  · right; right
    exact ZMod.val_injective L (by rw [hneg]; omega)

omit [NeZero W] in
private theorem LocalLaw_mem_sbSupport (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    v ∈ sbSupport L := by
  obtain ⟨x, y⟩ := v
  simp only [zdist2] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hz1 : zdist L (1 : ZMod L) ≠ 0 := fun h0 => h1 ((zdist_eq_zero_iff L).1 h0)
  have hzm : zdist L (-1 : ZMod L) ≠ 0 := fun h0 => neg_ne_zero.2 h1 ((zdist_eq_zero_iff L).1 h0)
  have hx : zdist L x ≤ 1 := by omega
  have hy : zdist L y ≤ 1 := by omega
  rcases LocalLaw_zdist_le_one hL hx with rfl | rfl | rfl <;>
    rcases LocalLaw_zdist_le_one hL hy with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | simp [sbSupport]

omit [NeZero W] in
private theorem LocalLaw_near_card (hL : 3 ≤ L) (a : Z2 L) :
    ((Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1)).card : ℝ) ≤ 5 := by
  have hsub : Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1) ⊆
      (sbSupport L).image (fun v => v + a) := by
    intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    exact Finset.mem_image.2 ⟨a' - a, LocalLaw_mem_sbSupport hL ha', by simp⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_sbSupport L hL] at this
  exact_mod_cast this

/-- The right side of (`GijGEX`) is at most `25 B + W⁻²` if every `|𝓛_{(+,-),(a,b)}| ≤ B` (the
number of `(a', b')` with `|a' - a|_L, |b' - b|_L ≤ 1` is at most `5 × 5 = 25`). -/
private theorem LocalLaw_gexRHS_le (hL : 3 ≤ L) (E u B : ℝ) (hB : 0 ≤ B)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : ∀ a b, ‖loopPM L W E u M a b‖ ≤ B) (a b : Z2 L) :
    gexRHS L W E u M a b ≤ 25 * B + ((W : ℝ) ^ 2)⁻¹ := by
  unfold gexRHS
  have h1 : (∑ a' : Z2 L, ∑ b' : Z2 L,
      if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0) ≤
      25 * B := by
    calc (∑ a' : Z2 L, ∑ b' : Z2 L,
        if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then ‖loopPM L W E u M a' b'‖ else 0)
        ≤ ∑ a' : Z2 L, ∑ b' : Z2 L, (if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          by_cases h1 : zdist2 L (a' - a) ≤ 1 <;> by_cases h2 : zdist2 L (b' - b) ≤ 1 <;>
            simp [h1, h2, hM]
      _ = (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 5 * (5 * B) := by
          have e1 : (∑ a' : Z2 L, if zdist2 L (a' - a) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact LocalLaw_near_card hL a
          have e2 : (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact LocalLaw_near_card hL b
          have e0 : 0 ≤ (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) := by
            exact Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
          exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hB) (mul_nonneg e0 hB) (by norm_num)
      _ = 25 * B := by ring
  have h2 : (if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    split_ifs
    · exact le_rfl
    · positivity
  linarith

/-- `gexRHS ≤ 25 · maxLoopPM + W⁻²`, pointwise, for `L ≥ 3` (the double sum
over the two `L¹` unit balls has `5 × 5 = 25` terms, each `≤ maxLoopPM`; the diagonal-block term
is `≤ W⁻²`). -/
theorem LocalLaw_gexRHS_le_maxLoopPM (hL : 3 ≤ L) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    gexRHS L W E u M a b ≤ 25 * maxLoopPM L W E u M + ((W : ℝ) ^ 2)⁻¹ :=
  LocalLaw_gexRHS_le hL E u _ (maxLoopPM_nonneg E u M) M
    (fun a b => Finset.le_sup' (fun p : Z2 L × Z2 L => ‖loopPM L W E u M p.1 p.2‖)
      (Finset.mem_univ (a, b))) a b

/-- The fine entry `|(G - m)_{ij}|` for `i ≠ j` is `√(offSq)` at the blocks (bridge
`step2Local_llErrMat_eq`, `splitEquiv` is injective). -/
private theorem LocalLaw_llErr_off (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    {i j : Idx L W} (hij : i ≠ j) :
    llErrMat L W E u M i j =
      Real.sqrt (offSq L W E u M (splitEquiv L W i) (splitEquiv L W j)) := by
  have hne : splitEquiv L W i ≠ splitEquiv L W j := fun h => hij ((splitEquiv L W).injective h)
  rw [step2Local_llErrMat_eq]
  simp only [hij, ite_false, sub_zero]
  unfold offSq
  simp only [hne, ite_false]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- The fine entry `|(G - m)_{ii}|` is `√(diagSq)` at the block of `i`. -/
private theorem LocalLaw_llErr_diag (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i : Idx L W) :
    llErrMat L W E u M i i = Real.sqrt (diagSq L W E u M (splitEquiv L W i)) := by
  rw [step2Local_llErrMat_eq]
  simp only [ite_true]
  unfold diagSq
  rw [Real.sqrt_sq (norm_nonneg _)]

private theorem LocalLaw_offSq_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (p q : BlockIndex L W) : 0 ≤ offSq L W E u M p q := by
  unfold offSq
  split_ifs <;> positivity

private theorem LocalLaw_diagSq_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (p : BlockIndex L W) : 0 ≤ diagSq L W E u M p := by
  unfold diagSq
  positivity

end Gex

/-! ## 2. The `≺` calculus used here -/

section Calc

/-- Reindexing a per-time domination along a map of index types `V l → U l`. -/
private theorem LocalLaw_reindex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} (φ : ∀ l, V l → U l)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (U := V) (fun l v ω => ξ l (φ l v) ω) (fun l v ω => ζ l (φ l v) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl v
  exact hl (φ l v)

/-- The real-number core of `LocalLaw_trans`: `a = s^{τ/4}`, `b = a² = s^{τ/2}`, `c = b² = s^τ`. -/
private theorem LocalLaw_absorb {a b c X Y M Q : ℝ} (h1 : 1 ≤ a) (h26 : 26 ≤ b)
    (hab : a * a = b) (hbc : b * b = c) (hQ : 0 ≤ Q) (hX : X ≤ a * Y) (hM : M ≤ a * Q)
    (hY : Y ≤ 25 * M + Q) : X ≤ c * Q := by
  have ha0 : 0 ≤ a := by linarith
  have hab' : a ≤ b := by nlinarith
  have hY' : Y ≤ 25 * a * Q + Q := by nlinarith
  have e1 : X ≤ a * (25 * a * Q + Q) := hX.trans (mul_le_mul_of_nonneg_left hY' ha0)
  have e2 : a * (25 * a * Q + Q) = 25 * b * Q + a * Q := by rw [← hab]; ring
  have e3 : a * Q ≤ b * Q := mul_le_mul_of_nonneg_right hab' hQ
  have e4 : 26 * b * Q ≤ b * b * Q := mul_le_mul_of_nonneg_right (by nlinarith) hQ
  rw [← hbc]
  linarith

/-- **Transitivity with the constant `25 + 1`**: if `X ≺ Y`, `M ≺ Q` and `Y ≤ 25 M + Q`
pointwise (`Q ≥ 0`), then `X ≺ Q`.  Proof by `perTimeCalc_of_imp_union` at `τ' = τ/4`:
`X ≤ N^{τ/4} Y ≤ N^{τ/4}(25 N^{τ/4} Q + Q) ≤ 26 N^{τ/2} Q ≤ N^τ Q` once `N^{τ/2} ≥ 26`. -/
private theorem LocalLaw_trans {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} (hsize : Tendsto size atTop atTop)
    {X Y M : ∀ l, U l → Ω → ℝ} {Q : ℕ → ℝ}
    (hXY : PerTimeDomAt P size X Y) (hMQ : PerTimeDomAt P size M (fun l _ _ => Q l))
    (hQ : ∀ l, 0 ≤ Q l) (hY : ∀ l u ω, Y l u ω ≤ 25 * M l u ω + Q l) :
    PerTimeDomAt P size X (fun l _ _ => Q l) := by
  refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsize hXY hMQ ?_
  intro τ hτ
  refine ⟨τ / 4, by positivity, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow 1 (show 0 < τ / 4 by positivity)),
    hsize.eventually (eventually_le_rpow 26 (show 0 < τ / 2 by positivity))]
    with l h1 h26 u ω hlt
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨hX, hM⟩ := hcon
  have hs0 : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hab : (size l : ℝ) ^ (τ / 4) * (size l : ℝ) ^ (τ / 4) = (size l : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hs0 (by positivity : τ / 4 + τ / 4 ≠ 0)]; congr 1; ring
  have hbc : (size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2) = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_add' hs0 (by positivity : τ / 2 + τ / 2 ≠ 0)]; congr 1; ring
  exact absurd hlt (not_lt.2 (LocalLaw_absorb h1 h26 hab hbc (hQ l) hX hM (hY l u ω)))

end Calc

/-! ## 3. `max 𝓛 ≺ Ψ²` at a general index type -/

section MaxLoop

variable (d : Sizes)

private theorem LocalLaw_card_le (n : ℕ) :
    (Fintype.card (Unit × Z2 (d.L n) × Z2 (d.L n)) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((2 : ℕ)) : ℝ) := by
  have h : Fintype.card (Unit × Z2 (d.L n) × Z2 (d.L n)) ≤ d.size n ^ 2 := by
    have hc : Fintype.card (Z2 (d.L n)) = d.L n ^ 2 := by simp [Z2, ZMod.card, pow_two]
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, hc, Sizes.size]
    have hLW : d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ (d.W_pos n)
    calc 1 * (d.L n ^ 2 * d.L n ^ 2) = d.L n ^ 4 := by ring
      _ ≤ (d.W n * d.L n) ^ 4 := Nat.pow_le_pow_left hLW 4
      _ = ((d.W n * d.L n) ^ 2) ^ 2 := by ring
  rw [Real.rpow_natCast]; exact_mod_cast h

/-- `max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ Ψ²` from `LoopDetSeq` (grid union over `(Z_L²)²`,
`L⁴ ≤ size²`, then `maxLoopPM = ‖loopPM a₀ b₀‖` for some pair), at any index type `V`. -/
private theorem LocalLaw_maxLoop_dom {E t : ℕ → ℝ} {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq d E t Ψ)
    (V : ℕ → Type*) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := V)
      (fun n _ ω => maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω))
      (fun n _ _ => Ψ n ^ 2) := by
  have hS := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := ((2 : ℕ) : ℝ))
    (Nat.cast_nonneg 2) (Eventually.of_forall (LocalLaw_card_le d)) hLoop
  intro τ hτ D hD
  filter_upwards [hS τ hτ D hD] with n hn u
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  have hω' : ((d.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
      maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) := hω
  unfold maxLoopPM at hω'
  obtain ⟨b, -, hb⟩ := (Finset.lt_sup'_iff _).1 hω'
  exact ⟨((), b.1, b.2), hb⟩

end MaxLoop

/-! ## 4. The theorem -/

/-- **The local law at a deterministic control** (`LocalLawDetThm`).  Under
(`asGMc`) (`AsGMcSeq d E t c`) and `LoopDetSeq d E t Ψ` with `W_n⁻¹ ≤ Ψ_n`:
`max_{ij} |(G_t - m)_{ij}| ≺ Ψ` per time ([YY_25] proof of (`GavLGEX`)).  A
conditional statement (the hypotheses `AsGMcSeq`, `LoopDetSeq` are the inputs the callers
supply). -/
theorem localLawDetThm : LocalLawDetThm := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs Ψ hΨ hLoop
  have hsz' : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => (inv_nonneg.2 (Nat.cast_nonneg _)).trans (hΨ n)
  have hΨ2 : ∀ n, 0 ≤ Ψ n ^ 2 := fun n => sq_nonneg _
  have hW2 : ∀ n, ((d.W n : ℝ) ^ 2)⁻¹ ≤ Ψ n ^ 2 := fun n => by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (Nat.cast_nonneg _)) (hΨ n) 2
  have hsq : ∀ n, Real.sqrt (Ψ n ^ 2) = Ψ n := fun n => Real.sqrt_sq (hΨ0 n)
  have hloop := LocalLaw_maxLoop_dom d hLoop
  -- off-diagonal: `offSq ≺ gexRHS ≤ 25 maxLoopPM + W⁻² ≤ 25 maxLoopPM + Ψ²`, so `offSq ≺ Ψ²`
  have hoff : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
      (fun n p ω => offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
      (fun n _ _ => Ψ n ^ 2) :=
    LocalLaw_trans hsz' (gijSeq_of_asGMc d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs)
      (hloop (fun n => Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)))
      (Q := fun n => Ψ n ^ 2) hΨ2
      (fun n u ω => (LocalLaw_gexRHS_le_maxLoopPM (d.three_le_L n) _ _ _ _ _).trans
        (by have := hW2 n; linarith))
  -- diagonal: `diagSq ≺ maxLoopPM ≤ 25 maxLoopPM + Ψ²`, so `diagSq ≺ Ψ²`
  have hdiag : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × BlockIndex (d.L n) (d.W n))
      (fun n p ω => diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2)
      (fun n _ _ => Ψ n ^ 2) :=
    LocalLaw_trans hsz' (giiSeq_of_asGMc d hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR c hc hAs)
      (hloop (fun n => Unit × BlockIndex (d.L n) (d.W n)))
      (Q := fun n => Ψ n ^ 2) hΨ2
      (fun n u ω => by
        have h1 := maxLoopPM_nonneg (L := d.L n) (W := d.W n) (E n) (t n)
          (Sizes.seqHflow d n (t n) ω)
        have h2 := hΨ2 n
        change maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) ≤
          25 * maxLoopPM (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) + Ψ n ^ 2
        linarith)
  -- square roots: `√offSq ≺ Ψ`, `√diagSq ≺ Ψ`
  have hoffS : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
      (fun n p ω => Real.sqrt
        (offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2))
      (fun n _ _ => Ψ n) := by
    have := RBM.Ind.PerTimeCalc.PerTime.sqrt_of
      (fun n p ω => LocalLaw_offSq_nonneg _ _ _ _ _) (fun n p ω => hΨ2 n) hoff
    simpa only [hsq] using this
  have hdiagS : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × BlockIndex (d.L n) (d.W n))
      (fun n p ω => Real.sqrt
        (diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2))
      (fun n _ _ => Ψ n) := by
    have := RBM.Ind.PerTimeCalc.PerTime.sqrt_of
      (fun n p ω => LocalLaw_diagSq_nonneg _ _ _ _) (fun n p ω => hΨ2 n) hdiag
    simpa only [hsq] using this
  -- back to the fine index, and the case split `i = j` / `i ≠ j`
  have h₁ := LocalLaw_reindex (fun n (p : Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) =>
    (((), splitEquiv (d.L n) (d.W n) p.2.1, splitEquiv (d.L n) (d.W n) p.2.2) :
      Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))) hoffS
  have h₂ := LocalLaw_reindex (fun n (p : Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) =>
    (((), splitEquiv (d.L n) (d.W n) p.2.1) : Unit × BlockIndex (d.L n) (d.W n))) hdiagS
  unfold LocalLawDetSeq
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_forall_or hsz' h₁ h₂ ?_
  intro n p ω
  obtain ⟨-, i, j⟩ := p
  by_cases hij : i = j
  · subst hij
    right
    exact ⟨(LocalLaw_llErr_diag _ _ _ _).le, le_rfl⟩
  · left
    exact ⟨(LocalLaw_llErr_off _ _ _ hij).le, le_rfl⟩

end RBM.Green
