/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodSet
import RBM2D.Path.KellStar

/-!
# (`Gt_bound_flow`) per time from (`Eq:Gdecay_w`)

The statement `Step2LocalOfDecay` and the bridge `step2Local_llErrMat_eq` between fine and block
resolvent entries.

Result: `step2LocalOfDecay : Step2LocalOfDecay d` for every size sequence `d`.  It is conditional
on the hypothesis `RBM.Green.GbEXPHypV3 d (κ/2) c τ` (the paper's `lem_GbEXP`), which the
statement carries as a premise.

Paper: arXiv:2503.07606, proof of (`Gt_bound_flow`): (`Eq:Gdecay_w`) and the `𝒦` bound give
(`lk2safyas`) `max_{a,b} |𝓛_{u,(+,-),(a,b)}| ≺ M_u^{-1}`; the weak local law lets one
apply (`GijGEX`), (`GiiGEX`); together `‖G_u - m‖²_max ≺ M_u^{-1}`.

## Proof outline

* The good event of `goodSetPT` (at `κ/2`, level `N^{τ'/2}`, probability `N^{-(D+1)}`) supplies
  the (`GijGEX`) and (`GiiGEX`) clauses;
* `Step2DecayPT` at `D₂ = 2` (level `N^{τ'/2}`, probability `N^{-(D+3)}`), with a union over the
  `L⁴ ≤ N²` pairs `(a, b)`, bounds `|𝓛 - 𝒦|`;
* `kpmBoundProp5` bounds `|𝒦| ≤ 180·40002² (1 + log L) M_u^{-1}`;
* on both events the deterministic core `Step2Local_core` gives
  `|(G_u - m)_{ij}| ≤ N^{τ'} M_u^{-1/2}` once `N^{τ'} ≥ 51 + 25·180·40002²(1 + 2/τ')`.

For `d = 2` the scale is `M_u = W² ℓ_u² η_u`, the labels are `Z2 L`, the good set is `goodSetPT`,
and the domination is per time.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-- **`Gt_bound_flow` per time from `Eq:Gdecay_w`**.  Paper: (`Gt_bound_flow`); proof:
(`lk2safyas`; "we use the weak local law (`Gtmwc`); this lets us apply (`GiiGEX`) and
(`GijGEX`)").  Used in: `Step2ClosureV3`. -/
def Step2LocalOfDecay : Prop :=
  ∀ (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ),
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → RBM.Ind.SizeTendsto d →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    RBM.Green.GbEXPHypV3 d (κ / 2) c τ → Step2DecayPT d E s t → Step2LocalPT d E s t

/-- **The block/fine bridge**: the fine entry `|(G_u - m)_{ij}|` is the entry of the
block resolvent `greenBlk` at `(splitEquiv i, splitEquiv j)`. -/
theorem step2Local_llErrMat_eq (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    llErrMat L W E u M i j =
      ‖greenBlk L W E u M true (splitEquiv L W i) (splitEquiv L W j) -
        (if i = j then spectralM E else 0)‖ := by
  unfold llErrMat greenBlk
  rw [Gsig_true]
  unfold green blockMat
  have key : M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm -
        spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
        (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext p q
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      (splitEquiv L W).symm.apply_eq_iff_eq]
  rw [key, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply]
  simp

/-! ## Deterministic helpers -/

section Helpers

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Step2Local_im_le_one {E : ℝ} (hE : |E| ≤ 2) : (spectralM E).im ≤ 1 := by
  have h := Complex.abs_im_le_norm (spectralM E)
  rw [norm_spectralM hE] at h
  exact (le_abs_self _).trans h

/-- `M_u ≤ W²` (`Im m ≤ 1`). -/
private theorem Step2Local_scaleM_le_W2 {L W : ℕ} (hL : 1 ≤ L) {E u : ℝ} (hE : |E| ≤ 2)
    (hu : u < 1) : scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  rw [scaleM_eq' hL hu]
  have hm := Step2Local_im_le_one hE
  have hm0 : 0 ≤ (spectralM E).im := by rw [spectralM_im]; positivity
  have h1 : min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) ≤ (W : ℝ) ^ 2 := min_le_left _ _
  have h0 : 0 ≤ min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u)) :=
    le_min (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  calc (spectralM E).im * min ((W : ℝ) ^ 2) ((((W * L) ^ 2 : ℕ) : ℝ) * (1 - u))
      ≤ 1 * (W : ℝ) ^ 2 := mul_le_mul hm h1 h0 zero_le_one
    _ = _ := one_mul _

omit [NeZero W] in
private theorem Step2Local_zdist_le_one (hL : 3 ≤ L) {x : ZMod L} (h : zdist L x ≤ 1) :
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
private theorem Step2Local_mem_sbSupport (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    v ∈ sbSupport L := by
  obtain ⟨x, y⟩ := v
  simp only [zdist2] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hz1 : zdist L (1 : ZMod L) ≠ 0 := fun h0 => h1 ((zdist_eq_zero_iff L).1 h0)
  have hzm : zdist L (-1 : ZMod L) ≠ 0 := fun h0 => neg_ne_zero.2 h1 ((zdist_eq_zero_iff L).1 h0)
  have hx : zdist L x ≤ 1 := by omega
  have hy : zdist L y ≤ 1 := by omega
  rcases Step2Local_zdist_le_one hL hx with rfl | rfl | rfl <;>
    rcases Step2Local_zdist_le_one hL hy with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | simp [sbSupport]

omit [NeZero W] in
private theorem Step2Local_near_card (hL : 3 ≤ L) (a : Z2 L) :
    ((Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1)).card : ℝ) ≤ 5 := by
  have hsub : Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1) ⊆
      (sbSupport L).image (fun v => v + a) := by
    intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    exact Finset.mem_image.2 ⟨a' - a, Step2Local_mem_sbSupport hL ha', by simp⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_sbSupport L hL] at this
  exact_mod_cast this

/-- The right side of (`GijGEX`) is at most `25 B + W⁻²` if every `|𝓛_{(+,-),(a,b)}| ≤ B`
(the number of `(a',b')` with `|a'-a|_L, |b'-b|_L ≤ 1` is at most `25`). -/
private theorem Step2Local_gexRHS_le (hL : 3 ≤ L) (E u B : ℝ) (hB : 0 ≤ B)
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
            rw [Finset.sum_boole]; exact Step2Local_near_card hL a
          have e2 : (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) ≤ 5 := by
            rw [Finset.sum_boole]; exact Step2Local_near_card hL b
          have e0 : 0 ≤ (∑ b' : Z2 L, if zdist2 L (b' - b) ≤ 1 then (1 : ℝ) else 0) := by
            exact Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
          exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hB) (mul_nonneg e0 hB) (by norm_num)
      _ = 25 * B := by ring
  have h2 : (if zdist2 L (a - b) ≤ 1 then ((W : ℝ) ^ 2)⁻¹ else 0) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    split_ifs
    · exact le_rfl
    · positivity
  linarith

/-! ## The deterministic core (`lk2safyas`) -/

/-- **The deterministic core.**  On the good set at level `N^{τ'/2}` and under the decay bound
`|(𝓛-𝒦)_{ab}| ≤ N^{τ'/2}((η_s/η_u)^4 M_u^{-2} e^{-√(|a-b|/ℓ_u)} + W^{-2})` for all `a, b`, with
(`con_st_ind`) at `(s,t)` and `N^{τ'} ≥ 51 + 25·180·40002²(1 + 2/τ')`, every entry satisfies
`|(G_u - m)_{ij}| ≤ N^{τ'} M_u^{-1/2}`. -/
private theorem Step2Local_core (hL : 3 ≤ L) {E s u t N τ' : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s)
    (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1)
    (hstep : (scaleM L W E s)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30)
    (hN1 : 1 ≤ N) (hLN : (L : ℝ) ≤ N) (hτ' : 0 < τ')
    (hK : 51 + 25 * (180 * 40002 ^ 2) * (1 + 2 / τ') ≤ N ^ τ')
    {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hG : M ∈ goodSet L W E s u (N ^ (τ' / 2)))
    (hD : ∀ a b : Z2 L, lkErrMat L W E u M a b ≤ N ^ (τ' / 2) *
      ((etaT E s / etaT E u) ^ 4 * (scaleM L W E u ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u)) + (W : ℝ) ^ (-(2 : ℝ))))
    (i j : Idx L W) :
    llErrMat L W E u M i j ≤ N ^ τ' * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  have hN0 : 0 < N := by linarith
  have hMpos : 0 < scaleM L W E u := scaleM_pos hL1 hW1 hE hu1
  have hMW : scaleM L W E u ≤ (W : ℝ) ^ 2 := Step2Local_scaleM_le_W2 hL1 hE.le hu1
  -- `(η_s/η_u)^4 ≤ M_u` from `con_st_ind` (`scaleM_ge_pow29` at `v = u`)
  have hr : etaT E s / etaT E u = (1 - s) / (1 - u) := etaT_div_etaT hE hs1 hu1
  have hr1 : 1 ≤ (1 - s) / (1 - u) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hr29 : ((1 - s) / (1 - u)) ^ 29 ≤ scaleM L W E u :=
    scaleM_ge_pow29 hL1 hW1 hE hs0 hsu hut ht hstep
  have hr4 : ((1 - s) / (1 - u)) ^ 4 ≤ scaleM L W E u :=
    (pow_le_pow_right₀ hr1 (by norm_num)).trans hr29
  set Mu := scaleM L W E u with hMu
  have hMi : 0 < Mu⁻¹ := inv_pos.2 hMpos
  -- `W^{-2} ≤ M_u^{-1}`
  have hWinv' : ((W : ℝ) ^ 2)⁻¹ ≤ Mu⁻¹ := inv_anti₀ hMpos hMW
  have hWinv : (W : ℝ) ^ (-(2 : ℝ)) ≤ Mu⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact hWinv'
  -- the decay bracket is at most `2 M_u^{-1}`
  have hdec : ∀ a b : Z2 L, (etaT E s / etaT E u) ^ 4 * (Mu ^ 2)⁻¹ *
      Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u)) + (W : ℝ) ^ (-(2 : ℝ)) ≤
        2 * Mu⁻¹ := by
    intro a b
    have he : Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
    have he0 := Real.exp_pos (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u))
    rw [hr]
    have hq0 : 0 ≤ ((1 - s) / (1 - u)) ^ 4 := by positivity
    have h1 : ((1 - s) / (1 - u)) ^ 4 * (Mu ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u)) ≤ Mu * (Mu ^ 2)⁻¹ * 1 := by
      gcongr
    have h2 : Mu * (Mu ^ 2)⁻¹ * 1 = Mu⁻¹ := by field_simp
    linarith
  -- `|𝓛_{ab}| ≤ B`
  set X := N ^ (τ' / 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by linarith)
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  have hK0 : ∀ a b : Z2 L, ‖Kpm L W E u a b‖ ≤
      180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * Mu⁻¹ :=
    kpmBoundProp5 L W E u hL hE (hs0.trans hsu) hu1
  set B := (2 * X + 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) * Mu⁻¹ with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ 2 * X + 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) := by positivity
    exact mul_nonneg this hMi.le
  have hloop : ∀ a b : Z2 L, ‖loopPM L W E u M a b‖ ≤ B := by
    intro a b
    have h1 := norm_le_norm_sub_add (loopPM L W E u M a b) (Kpm L W E u a b)
    have h2 : ‖loopPM L W E u M a b - Kpm L W E u a b‖ = lkErrMat L W E u M a b := rfl
    have h3 := hD a b
    have h5 : X * ((etaT E s / etaT E u) ^ 4 * (Mu ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L (a - b) : ℝ) / ellT L u)) + (W : ℝ) ^ (-(2 : ℝ))) ≤
        X * (2 * Mu⁻¹) := mul_le_mul_of_nonneg_left (hdec a b) (by linarith)
    have h6 := hK0 a b
    have e : B = X * (2 * Mu⁻¹) + 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) * Mu⁻¹ := by
      rw [hB]; ring
    rw [e]
    linarith
  have hmax : maxLoopPM L W E u M ≤ B := Finset.sup'_le _ _ fun p _ => hloop p.1 p.2
  have hgex : ∀ a b : Z2 L, gexRHS L W E u M a b ≤ 25 * B + Mu⁻¹ := fun a b =>
    (Step2Local_gexRHS_le hL E u B hB0 M hloop a b).trans (by linarith)
  -- the squared entry bound on the good set
  have hsq : llErrMat L W E u M i j ^ 2 ≤ X * (25 * B + Mu⁻¹) := by
    rw [step2Local_llErrMat_eq]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      calc ‖greenBlk L W E u M true (splitEquiv L W i) (splitEquiv L W i) - spectralM E‖ ^ 2
          ≤ X * maxLoopPM L W E u M := hG.2.2.2.2.1 (splitEquiv L W i)
        _ ≤ X * B := mul_le_mul_of_nonneg_left hmax (by linarith)
        _ ≤ X * (25 * B + Mu⁻¹) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    · have hne : splitEquiv L W i ≠ splitEquiv L W j := fun h => hij ((splitEquiv L W).injective h)
      simp only [hij, ite_false, sub_zero]
      exact (hG.2.2.2.1 _ _ hne).trans (mul_le_mul_of_nonneg_left (hgex _ _) (by linarith))
  -- absorb `log L` and the constants into `N^{τ'}`
  have hXsq : X ^ 2 = N ^ τ' := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hlogN : Real.log (L : ℝ) ≤ (2 / τ') * X := by
    have h1 : Real.log (L : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (show 0 < L by omega)) hLN
    have h2 : Real.log N ≤ N ^ (τ' / 2) / (τ' / 2) := Real.log_le_rpow_div hN0.le (by linarith)
    have h3 : N ^ (τ' / 2) / (τ' / 2) = (2 / τ') * X := by
      rw [hX]; field_simp
    linarith
  have hbr : 50 * X + 25 * (180 * 40002 ^ 2) * (1 + Real.log (L : ℝ)) + 1 ≤
      (51 + 25 * (180 * 40002 ^ 2) * (1 + 2 / τ')) * X := by
    have h2t : 0 < 2 / τ' := by positivity
    have : 1 + Real.log (L : ℝ) ≤ (1 + 2 / τ') * X := by nlinarith
    nlinarith
  have hfin : X * (25 * B + Mu⁻¹) ≤ (N ^ τ' * Mu⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 := by
    have e1 : X * (25 * B + Mu⁻¹) =
        X * (50 * X + 25 * (180 * 40002 ^ 2) * (1 + Real.log (L : ℝ)) + 1) * Mu⁻¹ := by
      rw [hB]; ring
    have e2 : (N ^ τ' * Mu⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 = N ^ τ' * N ^ τ' * Mu⁻¹ := by
      rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hMi.le]; ring
    rw [e1, e2]
    have hNt : 0 ≤ N ^ τ' := by positivity
    have h3 : X * (50 * X + 25 * (180 * 40002 ^ 2) * (1 + Real.log (L : ℝ)) + 1) ≤
        (51 + 25 * (180 * 40002 ^ 2) * (1 + 2 / τ')) * N ^ τ' := by
      rw [← hXsq]
      have := mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ X)
      nlinarith
    have h4 : (51 + 25 * (180 * 40002 ^ 2) * (1 + 2 / τ')) * N ^ τ' ≤ N ^ τ' * N ^ τ' :=
      mul_le_mul_of_nonneg_right hK hNt
    exact mul_le_mul_of_nonneg_right (h3.trans h4) hMi.le
  have h0 : 0 ≤ N ^ τ' * Mu⁻¹ ^ ((1 : ℝ) / 2) := by positivity
  exact (pow_le_pow_iff_left₀ (llErrMat_nonneg L W E u M i j) h0 (by norm_num)).1
    (hsq.trans hfin)

end Helpers

/-! ## The result -/

/-- **(`Gt_bound_flow`) per time from (`Eq:Gdecay_w`)**.  Paper: proof of (`Gt_bound_flow`).
Conditional on `RBM.Green.GbEXPHypV3 d (κ/2) c τ` (a premise of the statement). -/
theorem step2LocalOfDecay : Step2LocalOfDecay d := by
  intro κ c τ E s t hκ hE hc hτ hs0 hst ht1 hsz hbw hcs hrc h1 hw hV3 hdec
  have hE2 : ∀ n, |E n| < 2 - κ / 2 := fun n => by linarith [hE n]
  have hE' : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  intro τ' hτ' D hD
  have hG := goodSetPT d (κ / 2) c τ E s t (half_pos hκ) hc hτ hV3 hsz hbw hrc hcs hE2 hs0 hst
    ht1 h1 hw (τ' / 2) (half_pos hτ') (D + 1) (by linarith)
  have hDec := hdec 2 two_pos (τ' / 2) (half_pos hτ') (D + 3) (by linarith)
  have hN2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hsz.eventually_ge_atTop 2
  have hNK : ∀ᶠ n : ℕ in atTop,
      51 + 25 * (180 * 40002 ^ 2) * (1 + 2 / τ') ≤ ((d.size n : ℕ) : ℝ) ^ τ' :=
    ((tendsto_rpow_atTop hτ').comp hsz).eventually_ge_atTop _
  filter_upwards [hG, hDec, hcs, hN2, hNK] with n hGn hDn hcsn hN2n hNKn p
  obtain ⟨u, i, j⟩ := p
  have hu0 : s n ≤ (u : ℝ) := u.2.1
  have hut : (u : ℝ) ≤ t n := u.2.2
  -- sizes: `L ≤ N` and `L⁴ ≤ N²`
  have hLN : (d.L n : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have h : d.L n ≤ d.size n := by
      unfold Sizes.size
      have hW := d.W_pos n
      calc d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ hW
        _ ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact_mod_cast h
  have hL4 : ((d.L n : ℝ)) ^ 4 ≤ ((d.size n : ℕ) : ℝ) ^ 2 := by
    have h : d.L n ^ 4 ≤ d.size n ^ 2 := by
      unfold Sizes.size
      have hW := d.W_pos n
      rw [← pow_mul]
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) _
    exact_mod_cast h
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  -- the bad event lies in the union of the two failure events
  have hsub : {ω | N ^ τ' * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ ((1 : ℝ) / 2) <
        llErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i j} ⊆
      {ω | Sizes.seqHflow d n u ω ∉ goodSet (d.L n) (d.W n) (E n) (s n) u (N ^ (τ' / 2))} ∪
        ⋃ ab : Z2 (d.L n) × Z2 (d.L n), {ω | N ^ (τ' / 2) *
          ((etaT (E n) (s n) / etaT (E n) u) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ *
            Real.exp (-Real.sqrt ((zdist2 (d.L n) (ab.1 - ab.2) : ℝ) / ellT (d.L n) u)) +
            (d.W n : ℝ) ^ (-(2 : ℝ))) <
          lkErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) ab.1 ab.2} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_lt,
      not_not] at hno
    obtain ⟨hgood, hdecω⟩ := hno
    exact absurd (Step2Local_core (d.three_le_L n) (hE' n) (hs0 n) hu0 hut (ht1 n) hcsn
      (by linarith) hLN hτ' hNKn hgood (fun a b => hdecω (a, b)) i j) (not_le.2 hω)
  -- the real inequality `N^{-(D+1)} + L⁴ N^{-(D+3)} ≤ N^{-D}`
  have hreal : N ^ (-(D + 1)) + (d.L n : ℝ) ^ 4 * N ^ (-(D + 3)) ≤ N ^ (-D) := by
    have hy : 0 < N ^ (-(D + 1)) := Real.rpow_pos_of_pos hN0 _
    have e1 : N ^ (-D) = N ^ (-(D + 1)) * N := by
      rw [← Real.rpow_add_one hN0.ne']; ring_nf
    have e2 : N ^ (-(D + 3)) = N ^ (-(D + 1)) / N ^ 2 := by
      rw [show -(D + 3) = -(D + 1) - 2 by ring, Real.rpow_sub hN0,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hN2p : 0 < N ^ 2 := by positivity
    have h3 : (d.L n : ℝ) ^ 4 * N ^ (-(D + 3)) ≤ N ^ (-(D + 1)) := by
      rw [e2, mul_div_assoc']
      rw [div_le_iff₀ hN2p]
      exact mul_le_mul_of_nonneg_right hL4 hy.le |>.trans_eq (by ring)
    rw [e1]
    nlinarith
  have hcard : Fintype.card (Z2 (d.L n) × Z2 (d.L n)) = d.L n ^ 4 := by
    simp only [Z2, Fintype.card_prod, ZMod.card]; ring
  calc Sizes.seqP d {ω | N ^ τ' * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ ((1 : ℝ) / 2) <
        llErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) i j}
      ≤ Sizes.seqP d ({ω | Sizes.seqHflow d n u ω ∉
          goodSet (d.L n) (d.W n) (E n) (s n) u (N ^ (τ' / 2))} ∪
        ⋃ ab : Z2 (d.L n) × Z2 (d.L n), {ω | N ^ (τ' / 2) *
          ((etaT (E n) (s n) / etaT (E n) u) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ *
            Real.exp (-Real.sqrt ((zdist2 (d.L n) (ab.1 - ab.2) : ℝ) / ellT (d.L n) u)) +
            (d.W n : ℝ) ^ (-(2 : ℝ))) <
          lkErrMat (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) ab.1 ab.2}) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (N ^ (-(D + 1))) +
        ∑ _ab : Z2 (d.L n) × Z2 (d.L n), ENNReal.ofReal (N ^ (-(D + 3))) := by
        refine (measure_union_le _ _).trans (add_le_add (hGn u) ?_)
        exact (measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun ab _ => hDn (u, ab))
    _ = ENNReal.ofReal (N ^ (-(D + 1)) + (d.L n : ℝ) ^ 4 * N ^ (-(D + 3))) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          ENNReal.ofReal_add (Real.rpow_pos_of_pos hN0 _).le
            (by positivity), ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

end RBM.Path
