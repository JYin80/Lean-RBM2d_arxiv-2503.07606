/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.Pins
import RBM2D.Path.KellStar
import RBM2D.Induction.PerTimeCalc

/-!
# The far-entry decay of the resolvent on the Step 2 window

Paper: arXiv:2503.07606, Section 7: "by the assumption (`Eq:Gdecay_w`) and (`GijGEX`),
`|(G_s)_{i_n i_{n+1}}| ≺ W^{-D'}`" (proof of `clt-lemma`), `clt-gij-decay`, the fast decay of
`G_s` in the proof of `clt-lemma`; and the section "Estimates for entries of `G`": `lem_GbEXP`,
(`GijGEX`), (`asGMc`), "without the
indicator".

Results (namespace `RBM.Evol`):
1. `FarEntryDecayPT d E s t`: for every `τ', D' > 0`, per time
   on `[s_n, t_n]` and every pair of block indices `(p, q)`,
   `‖G_u(p, q)‖ · 1[W^{τ'} ℓ_u ≤ |p.1 - q.1|_L] ≺ W^{-D'}`;
2. `farEntryDecayPT`: from `GbEXPHypV3 d (κ/2) 𝔠 δ`, `Step2LocalPT`, `Step2DecayPT` and the
   deterministic hypotheses;
3. packaging: `farEntry_step2LocalPT_mono`,
   `farEntry_step2DecayPT_mono` (restriction of the Step 2 outputs to a shorter window) and
   `farEntryDecayPT_clt` (the theorem on `[s₀, u]` from the hypotheses of the `Clt` statements,
   whose Step 2 window is `[s₀, t₀] ∋ u`), and `farEntry_perTime_comp` (precomposition of a
   per-time domination with a map of index types).

Argument.  `Step2LocalPT` and `M_v ≥ Im m · N^{min(2𝔠,δ)} ≥ 𝔪 W^{min(2𝔠,δ)}` give (`asGMc`) per
time at `c = min(2𝔠,δ)/2`; `RBM.Green.gijGEXPTSwap_giiGEXPT_of_V3` gives (`GijGEX`) per
time, off the diagonal, with the swapped right side `gexRHS … q.1 p.1`.  On the far set the `W⁻²`
term of `gexRHS` vanishes and the sum has at most `5 × 5` neighbouring loops `𝓛_{(a',b')}` with
`|a' - b'|_L ≥ ℓ_v (W^{τ'} - 2)`; each is `𝒦 + (𝓛 - 𝒦)`: `𝒦` by `kellStarEv` (with
`normSqSpectralMOne`) and `𝓛 - 𝒦` by `Step2DecayPT` at `D = 2D'` (the term
`(η_s/η_v)^4 M_v^{-2} exp(-(|a'-b'|/ℓ_v)^{1/2})` is `≤ W^{-2D'}` eventually, since `η_s/η_v ≤ N ≤
W^{1/𝔠}`).  Then the `≺` calculus: `finset_sum_of`, transitivity (`farEntry_trans`), `sqrt_of`.
-/

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind

/-! ## Generic per-time facts -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- Precomposition with a map of index types preserves a per-time domination. -/
theorem farEntry_perTime_comp {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (g : ∀ l, U' l → U l) (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun l u ω => ξ l (g l u) ω) (fun l u ω => ζ l (g l u) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  exact hl (g l u)

/-- Transitivity of `≺` (per time). -/
private theorem farEntry_trans (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {ξ ζ η : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ ζ) (h₂ : PerTimeDomAt P size ζ η) :
    PerTimeDomAt P size ξ η := by
  refine PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsize h₁ h₂ ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with l hl u ω h
  have hN0 : (0 : ℝ) < (size l : ℝ) := by exact_mod_cast hl
  by_cases hA : (size l : ℝ) ^ (τ / 2) * ζ l u ω < ξ l u ω
  · exact Or.inl hA
  · right
    have hle : ξ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ζ l u ω := not_lt.1 hA
    have hpos : 0 < (size l : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
    have hsplit : (size l : ℝ) ^ τ = (size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hsplit, mul_assoc] at h
    exact lt_of_mul_lt_mul_left (h.trans_le hle) hpos.le

end Generic

/-! ## Lattice geometry -/

section Geometry

variable {L : ℕ} [NeZero L]

/-- `|-x|_L = |x|_L` on `Z_L`. -/
private theorem farEntry_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

/-- `|-u|_L = |u|_L` on `Z_L²`. -/
private theorem farEntry_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, farEntry_zdist_neg]

/-- `|P - Q|_L ≤ |a' - b'|_L + 2` when `|a' - Q|_L ≤ 1` and `|b' - P|_L ≤ 1`. -/
private theorem farEntry_zdist2_tri (P Q a' b' : Z2 L) (h1 : zdist2 L (a' - Q) ≤ 1)
    (h2 : zdist2 L (b' - P) ≤ 1) : zdist2 L (P - Q) ≤ zdist2 L (a' - b') + 2 := by
  have e : P - Q = ((P - b') + (b' - a')) + (a' - Q) := by abel
  have hA := zdist2_add_le L (P - b' + (b' - a')) (a' - Q)
  have hB := zdist2_add_le L (P - b') (b' - a')
  have hC : zdist2 L (P - b') = zdist2 L (b' - P) := by
    rw [← neg_sub b' P, farEntry_zdist2_neg]
  have hD : zdist2 L (b' - a') = zdist2 L (a' - b') := by
    rw [← neg_sub a' b', farEntry_zdist2_neg]
  rw [e]
  omega

private theorem farEntry_zdist_le_one_cases (hL : 3 ≤ L) {x : ZMod L} (h : zdist L x ≤ 1) :
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

private theorem farEntry_mem_sbSupport (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    v ∈ sbSupport L := by
  obtain ⟨x, y⟩ := v
  simp only [zdist2] at h
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hz1 : zdist L (1 : ZMod L) ≠ 0 := fun h0 => h1 ((zdist_eq_zero_iff L).1 h0)
  have hzm : zdist L (-1 : ZMod L) ≠ 0 := fun h0 => neg_ne_zero.2 h1 ((zdist_eq_zero_iff L).1 h0)
  have hx : zdist L x ≤ 1 := by omega
  have hy : zdist L y ≤ 1 := by omega
  rcases farEntry_zdist_le_one_cases hL hx with rfl | rfl | rfl <;>
    rcases farEntry_zdist_le_one_cases hL hy with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | simp [sbSupport]

/-- The five offsets `(0,0), (±1,0), (0,±1)` of the nearest-neighbour support. -/
private def farOff (L : ℕ) : Fin 5 → Z2 L :=
  ![((0 : ZMod L), (0 : ZMod L)), (1, 0), (-1, 0), (0, 1), (0, -1)]

private theorem farOff_mem (L : ℕ) [NeZero L] (i : Fin 5) : farOff L i ∈ sbSupport L := by
  fin_cases i <;> simp [farOff, sbSupport]

private theorem farOff_zdist2_le (hL : 3 ≤ L) (i : Fin 5) : zdist2 L (farOff L i) ≤ 1 :=
  zdist2_le_one_of_mem_sbSupport L hL (farOff_mem L i)

private theorem farEntry_near_off (hL : 3 ≤ L) {v : Z2 L} (h : zdist2 L v ≤ 1) :
    ∃ i : Fin 5, v = farOff L i := by
  have hm := farEntry_mem_sbSupport hL h
  simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm | hm | hm
  · exact ⟨0, by simpa [farOff] using hm⟩
  · exact ⟨1, by simpa [farOff] using hm⟩
  · exact ⟨2, by simpa [farOff] using hm⟩
  · exact ⟨3, by simpa [farOff] using hm⟩
  · exact ⟨4, by simpa [farOff] using hm⟩

/-- A sum over the pairs `(a', b')` with `|a' - a|_L ≤ 1`, `|b' - b|_L ≤ 1` of a nonnegative `f` is
at most the sum over the `5 × 5` offsets. -/
private theorem farEntry_near_sum_le (hL : 3 ≤ L) (f : Z2 L → Z2 L → ℝ)
    (hf : ∀ a b, 0 ≤ f a b) (a b : Z2 L) :
    (∑ a' : Z2 L, ∑ b' : Z2 L,
        if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then f a' b' else 0) ≤
      ∑ ij : Fin 5 × Fin 5, f (a + farOff L ij.1) (b + farOff L ij.2) := by
  classical
  let Φ : Fin 5 × Fin 5 → Z2 L × Z2 L := fun ij => (a + farOff L ij.1, b + farOff L ij.2)
  have h1 : (∑ a' : Z2 L, ∑ b' : Z2 L,
        if zdist2 L (a' - a) ≤ 1 ∧ zdist2 L (b' - b) ≤ 1 then f a' b' else 0) =
      ∑ x ∈ (Finset.univ : Finset (Z2 L × Z2 L)).filter
        (fun x => zdist2 L (x.1 - a) ≤ 1 ∧ zdist2 L (x.2 - b) ≤ 1), f x.1 x.2 := by
    rw [Finset.sum_filter]
    exact (Fintype.sum_prod_type (fun x : Z2 L × Z2 L =>
      if zdist2 L (x.1 - a) ≤ 1 ∧ zdist2 L (x.2 - b) ≤ 1 then f x.1 x.2 else 0)).symm
  rw [h1]
  have hsub : (Finset.univ : Finset (Z2 L × Z2 L)).filter
        (fun x => zdist2 L (x.1 - a) ≤ 1 ∧ zdist2 L (x.2 - b) ≤ 1) ⊆
      (Finset.univ : Finset (Fin 5 × Fin 5)).image Φ := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := farEntry_near_off hL hx.1
    obtain ⟨j, hj⟩ := farEntry_near_off hL hx.2
    refine Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, ?_⟩
    refine Prod.ext ?_ ?_
    · change a + farOff L i = x.1
      rw [← hi]; abel
    · change b + farOff L j = x.2
      rw [← hj]; abel
  calc (∑ x ∈ (Finset.univ : Finset (Z2 L × Z2 L)).filter
        (fun x => zdist2 L (x.1 - a) ≤ 1 ∧ zdist2 L (x.2 - b) ≤ 1), f x.1 x.2)
      ≤ ∑ x ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).image Φ, f x.1 x.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hf _ _)
    _ ≤ ∑ ij : Fin 5 × Fin 5, f (Φ ij).1 (Φ ij).2 :=
        Finset.sum_image_le_of_nonneg (fun x _ => hf _ _)

end Geometry

/-! ## Asymptotics in `W` -/

section Asymptotics

/-- `w^A exp(-c w^β) → 0` as `w → ∞`, for `c, β > 0` (via `x = w^β` and
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`). -/
private theorem farEntry_tendsto_rpow_exp (A c β : ℝ) (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (fun w : ℝ => w ^ A * Real.exp (-c * w ^ β)) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ (A / β) * Real.exp (-c * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / β) c hc
  have h2 : Tendsto (fun w : ℝ => w ^ β) atTop atTop := tendsto_rpow_atTop hβ
  have h3 := h1.comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  simp only [Function.comp]
  rw [← Real.rpow_mul hw.le, mul_div_cancel₀ _ hβ.ne']

/-- Eventually in `w`: `4 ≤ w^τ'` and `(log w)^{3/2} + 2 ≤ w^τ'`. -/
private theorem farEntry_eventually_log (τ' : ℝ) (hτ' : 0 < τ') :
    ∀ᶠ w : ℝ in atTop, 4 ≤ w ^ τ' ∧ Real.log w ^ ((3 : ℝ) / 2) + 2 ≤ w ^ τ' := by
  have h4 : ∀ᶠ w : ℝ in atTop, 4 ≤ w ^ τ' :=
    (tendsto_rpow_atTop hτ').eventually (eventually_ge_atTop 4)
  have hlo := (isLittleO_log_rpow_rpow_atTop ((3 : ℝ) / 2) hτ').def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h4, hlo, eventually_gt_atTop (0 : ℝ)] with w h4w hw hw0
  refine ⟨h4w, ?_⟩
  have h1 : Real.log w ^ ((3 : ℝ) / 2) ≤ ‖Real.log w ^ ((3 : ℝ) / 2)‖ := by
    rw [Real.norm_eq_abs]; exact le_abs_self _
  have h2 : ‖w ^ τ'‖ = w ^ τ' := by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Real.rpow_nonneg hw0.le _)
  rw [h2] at hw
  linarith

end Asymptotics

/-! ## Deterministic bounds at one size index -/

section PerSize

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Im m^{(E)} ≥ √(κ (4 - κ)) / 2` for `|E| ≤ 2 - κ` (as the private `spectralM_im_ge` of
`RBM2D/Loop/KBoundInner.lean`). -/
private theorem farEntry_spectralM_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

omit [NeZero W] in
/-- `𝒦 = W⁻² Θ_u` for `|E| < 2` (as the private `kellStar_Kpm_eq` of `RBM2D/Path/KellStar.lean`). -/
private theorem farEntry_Kpm_eq {E : ℝ} (hE : |E| < 2) (u : ℝ) (a b : Z2 L) :
    Kpm L W E u a b = ((W : ℂ)⁻¹) ^ 2 * Theta L (u : ℂ) a b := by
  have h1 : Complex.normSq (spectralM E) = 1 := normSqSpectralMOne E hE.le
  unfold Kpm
  rw [h1]
  simp

/-- The far indicator `1[W^{τ'} ℓ_v ≤ |p - q|_L]` at block indices. -/
private def feInd (L W : ℕ) (τ' v : ℝ) (p q : BlockIndex L W) : ℝ :=
  if (W : ℝ) ^ τ' * ellT L v ≤ (zdist2 L (p.1 - q.1) : ℝ) then 1 else 0

omit [NeZero W] in
/-- **The far-pair bounds at one size index.**  Let `|P - Q|_L ≥ W^{τ'} ℓ_v` and let `(a', b')` be a
pair with `|a' - Q|_L ≤ 1`, `|b' - P|_L ≤ 1`.  Then `‖𝒦_{v,(+,-),(a',b')}‖ ≤ W^{-D₂}` and the
right side of `Step2DecayPT` at `D = D₂` is at most `2 W^{-D₂}`.  Every hypothesis is a
deterministic input which holds eventually in `n` (`hbw`, `hrange`, `hτ4`, `hlog`, `hK`,
`hTheta`). -/
private theorem farEntry_pair_bounds {E s v t κ 𝔠 δ τ' D₂ : ℝ}
    (hL3 : 3 ≤ L) (hW1 : 1 ≤ W) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hbw : (((W * L) ^ 2 : ℕ) : ℝ) ^ 𝔠 ≤ (W : ℝ))
    (hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t)
    (hτ4 : 4 ≤ (W : ℝ) ^ τ') (hlog : Real.log (W : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤ (W : ℝ) ^ τ')
    (hK : ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
      ((W : ℝ) ^ (4 / 𝔠 + D₂) * Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2))) ≤ 1)
    (hTheta : ∀ a b : Z2 L, 1 * ellStar L W v ≤ (zdist2 L (a - b) : ℝ) →
      ‖Theta L (v : ℂ) a b‖ ≤ (W : ℝ) ^ (-D₂))
    {P Q : Z2 L} (hfar : (W : ℝ) ^ τ' * ellT L v ≤ (zdist2 L (P - Q) : ℝ))
    {a' b' : Z2 L} (ha : zdist2 L (a' - Q) ≤ 1) (hb : zdist2 L (b' - P) ≤ 1) :
    ‖Kpm L W E v a' b'‖ ≤ (W : ℝ) ^ (-D₂) ∧
      (etaT E s / etaT E v) ^ 4 * (scaleM L W E v ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 L (a' - b') : ℝ) / ellT L v)) + (W : ℝ) ^ (-D₂) ≤
        2 * (W : ℝ) ^ (-D₂) := by
  have hL1 : 1 ≤ L := by omega
  have hE2 : |E| < 2 := by linarith
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hv1 : v < 1 := hvt.trans_lt ht1
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW1 hL1)
    rw [hNdef]; exact_mod_cast this
  have hN0 : 0 < N := by linarith
  have hℓ1 : 1 ≤ ellT L v := one_le_ellT hL1 hv0 hv1
  have hℓpos : 0 < ellT L v := by linarith
  -- geometry
  have hz : (zdist2 L (P - Q) : ℝ) ≤ (zdist2 L (a' - b') : ℝ) + 2 := by
    exact_mod_cast farEntry_zdist2_tri P Q a' b' ha hb
  have hdist : ((W : ℝ) ^ τ' - 2) * ellT L v ≤ (zdist2 L (a' - b') : ℝ) := by
    have : ((W : ℝ) ^ τ' - 2) * ellT L v = (W : ℝ) ^ τ' * ellT L v - 2 * ellT L v := by ring
    linarith
  have hlog0 : 0 ≤ Real.log (W : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_nonneg (Real.log_nonneg hW1r) _
  -- the `𝒦` bound
  have hKpm : ‖Kpm L W E v a' b'‖ ≤ (W : ℝ) ^ (-D₂) := by
    have hell : 1 * ellStar L W v ≤ (zdist2 L (a' - b') : ℝ) := by
      rw [one_mul]
      unfold ellStar
      refine le_trans ?_ hdist
      exact mul_le_mul_of_nonneg_right (by linarith) hℓpos.le
    have hTh := hTheta a' b' hell
    rw [farEntry_Kpm_eq hE2, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    have hinv : ((W : ℝ)⁻¹) ^ 2 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 hWpos.le) (inv_le_one_of_one_le₀ hW1r)
    calc ((W : ℝ)⁻¹) ^ 2 * ‖Theta L (v : ℂ) a' b'‖ ≤ 1 * (W : ℝ) ^ (-D₂) :=
          mul_le_mul hinv hTh (norm_nonneg _) zero_le_one
      _ = (W : ℝ) ^ (-D₂) := one_mul _
  refine ⟨hKpm, ?_⟩
  -- the `η` ratio
  have hη : etaT E s / etaT E v = (1 - s) / (1 - v) := etaT_div_etaT hE2 (by linarith) hv1
  have hratio : (1 - s) / (1 - v) ≤ N := by
    have hxv : 0 < 1 - v := by linarith
    rw [div_le_iff₀ hxv]
    have h1 : N ^ (-1 : ℝ) ≤ N ^ (-1 + δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : N⁻¹ ≤ 1 - v := by linarith
    have h3 : 1 ≤ N * (1 - v) := by
      calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
        _ ≤ N * (1 - v) := mul_le_mul_of_nonneg_left h2 hN0.le
    linarith
  have hr0 : 0 ≤ (1 - s) / (1 - v) := div_nonneg (by linarith) (by linarith)
  have hN4 : ((1 - s) / (1 - v)) ^ 4 ≤ (W : ℝ) ^ (4 / 𝔠) := by
    have h1 : N ≤ (W : ℝ) ^ (1 / 𝔠) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le 𝔠) hbw (by positivity : (0 : ℝ) ≤ 1 / 𝔠)
      rwa [← Real.rpow_mul hN0.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one] at this
    calc ((1 - s) / (1 - v)) ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ hr0 hratio 4
      _ ≤ ((W : ℝ) ^ (1 / 𝔠)) ^ 4 := pow_le_pow_left₀ hN0.le h1 4
      _ = (W : ℝ) ^ (4 / 𝔠) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
        congr 1; push_cast; ring
  -- the `M` lower bound
  have hm0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  have hM : Real.sqrt (κ * (4 - κ)) / 2 ≤ scaleM L W E v := by
    have h1 := (scaleM_etaT_of_range (L := L) (W := W) (E := E) (c := 𝔠) (τ := δ) (t := t) hL1
      hW1 hE2 h𝔠 hδ ht1 hbw hrange).1
    have h2 := (scaleM_anti_ratio (W := W) (E := E) (s := v) (v := t) hL1 hE2 hvt ht1).1
    have h3 : 1 ≤ N ^ (min (2 * 𝔠) δ) :=
      Real.one_le_rpow hN1 (le_min (by linarith) hδ.le)
    have him : 0 < (spectralM E).im := spectralM_im_pos hE2
    have h4 : (spectralM E).im ≤ (spectralM E).im * N ^ (min (2 * 𝔠) δ) :=
      le_mul_of_one_le_right him.le h3
    linarith [farEntry_spectralM_im_ge hE]
  have hB : (scaleM L W E v ^ 2)⁻¹ ≤ ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hm0 2) (pow_le_pow_left₀ hm0.le hM 2)
  have hB0 : 0 ≤ (scaleM L W E v ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  -- the exponential
  have hy : (W : ℝ) ^ τ' / 2 ≤ (zdist2 L (a' - b') : ℝ) / ellT L v := by
    rw [le_div_iff₀ hℓpos]
    refine le_trans ?_ hdist
    have : (W : ℝ) ^ τ' / 2 ≤ (W : ℝ) ^ τ' - 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hℓpos.le
  have hsq : (1 / 2) * (W : ℝ) ^ (τ' / 2) ≤ Real.sqrt ((zdist2 L (a' - b') : ℝ) / ellT L v) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hw2 : ((W : ℝ) ^ (τ' / 2)) ^ 2 = (W : ℝ) ^ τ' := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
      congr 1; push_cast; ring
    have : ((1 / 2) * (W : ℝ) ^ (τ' / 2)) ^ 2 = (W : ℝ) ^ τ' / 4 := by
      rw [mul_pow, hw2]; ring
    rw [this]
    linarith
  have hexp : Real.exp (-Real.sqrt ((zdist2 L (a' - b') : ℝ) / ellT L v)) ≤
      Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2)) := by
    refine Real.exp_le_exp.2 ?_
    linarith
  have hexp0 : 0 ≤ Real.exp (-Real.sqrt ((zdist2 L (a' - b') : ℝ) / ellT L v)) :=
    (Real.exp_pos _).le
  -- combine
  have hA0 : 0 ≤ (etaT E s / etaT E v) ^ 4 := by rw [hη]; exact pow_nonneg hr0 4
  have hAle : (etaT E s / etaT E v) ^ 4 ≤ (W : ℝ) ^ (4 / 𝔠) := by rw [hη]; exact hN4
  have hprod : (etaT E s / etaT E v) ^ 4 * (scaleM L W E v ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L (a' - b') : ℝ) / ellT L v)) ≤
      (W : ℝ) ^ (4 / 𝔠) * ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
        Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2)) := by
    refine mul_le_mul (mul_le_mul hAle hB hB0 (Real.rpow_nonneg hWpos.le _)) hexp hexp0 ?_
    exact mul_nonneg (Real.rpow_nonneg hWpos.le _) (inv_nonneg.2 (sq_nonneg _))
  have hfin : (W : ℝ) ^ (4 / 𝔠) * ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
        Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2)) ≤ (W : ℝ) ^ (-D₂) := by
    have hWD : 0 < (W : ℝ) ^ D₂ := Real.rpow_pos_of_pos hWpos _
    have hsplit : (W : ℝ) ^ (4 / 𝔠 + D₂) = (W : ℝ) ^ (4 / 𝔠) * (W : ℝ) ^ D₂ :=
      Real.rpow_add hWpos _ _
    rw [hsplit] at hK
    rw [Real.rpow_neg hWpos.le]
    calc (W : ℝ) ^ (4 / 𝔠) * ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
          Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2))
        = ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
            ((W : ℝ) ^ (4 / 𝔠) * (W : ℝ) ^ D₂ * Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2))) *
            ((W : ℝ) ^ D₂)⁻¹ := by field_simp
      _ ≤ 1 * ((W : ℝ) ^ D₂)⁻¹ := by gcongr
      _ = ((W : ℝ) ^ D₂)⁻¹ := one_mul _
  linarith

omit [NeZero L] [NeZero W] in
/-- The `AsGMcPT` step at one size index: `M_v^{-1/2} ≤ 𝔪^{-1/2} W^{-c₀/2}`, `c₀ = min(2𝔠, δ)`,
`𝔪 = √(κ(4-κ))/2`, on `v ≤ t < 1` (from `scaleM_etaT_of_range` and `scaleM_anti_ratio`). -/
private theorem farEntry_local_le {E v t κ 𝔠 δ : ℝ}
    (hL3 : 3 ≤ L) (hW1 : 1 ≤ W) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    (hvt : v ≤ t) (ht1 : t < 1)
    (hbw : (((W * L) ^ 2 : ℕ) : ℝ) ^ 𝔠 ≤ (W : ℝ))
    (hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t) :
    (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2) ≤
      ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹) ^ ((1 : ℝ) / 2) * (W : ℝ) ^ (-(min (2 * 𝔠) δ / 2)) := by
  have hL1 : 1 ≤ L := by omega
  have hE2 : |E| < 2 := by linarith
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW1 hL1)
    rw [hNdef]; exact_mod_cast this
  have hNW : (W : ℝ) ≤ N := by
    have h1 : W ≤ (W * L) ^ 2 := by
      calc W = W * 1 := (mul_one W).symm
        _ ≤ W * L := Nat.mul_le_mul_left W hL1
        _ ≤ (W * L) ^ 2 := by
          have : 1 ≤ W * L := Nat.mul_pos hW1 hL1
          nlinarith
    rw [hNdef]; exact_mod_cast h1
  have hm0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  set c₀ : ℝ := min (2 * 𝔠) δ with hc₀
  have hc0 : 0 ≤ c₀ := le_min (by linarith) hδ.le
  have hM : Real.sqrt (κ * (4 - κ)) / 2 * (W : ℝ) ^ c₀ ≤ scaleM L W E v := by
    have h1 := (scaleM_etaT_of_range (L := L) (W := W) (E := E) (c := 𝔠) (τ := δ) (t := t) hL1
      hW1 hE2 h𝔠 hδ ht1 hbw hrange).1
    have h2 := (scaleM_anti_ratio (W := W) (E := E) (s := v) (v := t) hL1 hE2 hvt ht1).1
    have h3 : (W : ℝ) ^ c₀ ≤ N ^ c₀ := Real.rpow_le_rpow hWpos.le hNW hc0
    have him := farEntry_spectralM_im_ge hE
    have hWc : 0 ≤ (W : ℝ) ^ c₀ := Real.rpow_nonneg hWpos.le _
    have h4 : Real.sqrt (κ * (4 - κ)) / 2 * (W : ℝ) ^ c₀ ≤ (spectralM E).im * N ^ c₀ :=
      mul_le_mul him h3 hWc (le_trans hm0.le him)
    linarith
  have hWc : 0 < (W : ℝ) ^ c₀ := Real.rpow_pos_of_pos hWpos _
  have hinv : (scaleM L W E v)⁻¹ ≤ (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * (W : ℝ) ^ (-c₀) := by
    rw [Real.rpow_neg hWpos.le, ← mul_inv]
    exact inv_anti₀ (mul_pos hm0 hWc) hM
  calc (scaleM L W E v)⁻¹ ^ ((1 : ℝ) / 2)
      ≤ ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹ * (W : ℝ) ^ (-c₀)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (inv_nonneg.2 (le_trans (mul_pos hm0 hWc).le hM)) hinv (by norm_num)
    _ = ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹) ^ ((1 : ℝ) / 2) * ((W : ℝ) ^ (-c₀)) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (inv_nonneg.2 hm0.le) (Real.rpow_nonneg hWpos.le _)
    _ = ((Real.sqrt (κ * (4 - κ)) / 2)⁻¹) ^ ((1 : ℝ) / 2) * (W : ℝ) ^ (-(c₀ / 2)) := by
        rw [← Real.rpow_mul hWpos.le]
        congr 2; ring

omit [NeZero L] [NeZero W] in
private theorem feInd_nonneg (τ' v : ℝ) (p q : BlockIndex L W) : 0 ≤ feInd L W τ' v p q := by
  unfold feInd; split_ifs <;> norm_num

omit [NeZero L] [NeZero W] in
/-- A far pair of blocks is off the diagonal. -/
private theorem farEntry_far_ne (τ' v : ℝ) (hpos : 0 < (W : ℝ) ^ τ' * ellT L v)
    {P Q : BlockIndex L W} (hf : (W : ℝ) ^ τ' * ellT L v ≤ (zdist2 L (P.1 - Q.1) : ℝ)) :
    P ≠ Q := by
  rintro rfl
  rw [sub_self, zdist2_zero] at hf
  simp at hf
  linarith

omit [NeZero L] [NeZero W] in
/-- On the far set the indicator is `1`; `(‖G_{PQ}‖ 1_far)² = 1_far · |G_{PQ}|²·1(P ≠ Q)`. -/
private theorem farEntry_sq_eq (τ' v : ℝ) (hpos : 0 < (W : ℝ) ^ τ' * ellT L v)
    (G : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (P Q : BlockIndex L W) :
    (‖G P Q‖ * feInd L W τ' v P Q) ^ 2 =
      feInd L W τ' v P Q * (if P = Q then 0 else ‖G P Q‖ ^ 2) := by
  by_cases hf : (W : ℝ) ^ τ' * ellT L v ≤ (zdist2 L (P.1 - Q.1) : ℝ)
  · have hne := farEntry_far_ne τ' v hpos hf
    simp [feInd, hf, hne]
  · simp [feInd, hf]

/-- Far part of the right side of (`GijGEX`): at most the `5 × 5` neighbouring loops, since the
`W⁻²` term vanishes there (`|Q - P|_L ≥ W^{τ'} ℓ_v > 1`). -/
private theorem farEntry_ind_gexRHS_le (hL3 : 3 ≤ L) {E v τ' : ℝ}
    (M : Matrix (Idx L W) (Idx L W) ℂ) (P Q : BlockIndex L W) (hτ1 : 1 < (W : ℝ) ^ τ')
    (hℓ : 1 ≤ ellT L v) :
    feInd L W τ' v P Q * gexRHS L W E v M Q.1 P.1 ≤
      ∑ ij : Fin 5 × Fin 5, feInd L W τ' v P Q *
        ‖loopPM L W E v M (Q.1 + farOff L ij.1) (P.1 + farOff L ij.2)‖ := by
  by_cases hf : (W : ℝ) ^ τ' * ellT L v ≤ (zdist2 L (P.1 - Q.1) : ℝ)
  · have h1 : feInd L W τ' v P Q = 1 := by simp [feInd, hf]
    rw [h1]
    simp only [one_mul]
    have hgt : ¬ zdist2 L (Q.1 - P.1) ≤ 1 := by
      intro hle
      have hle' : (zdist2 L (Q.1 - P.1) : ℝ) ≤ 1 := by exact_mod_cast hle
      have hsym : zdist2 L (Q.1 - P.1) = zdist2 L (P.1 - Q.1) := by
        rw [← neg_sub P.1 Q.1, farEntry_zdist2_neg]
      rw [hsym] at hle'
      have : (W : ℝ) ^ τ' ≤ (W : ℝ) ^ τ' * ellT L v := by
        have h0 : 0 ≤ (W : ℝ) ^ τ' := by linarith
        nlinarith
      linarith
    unfold gexRHS
    simp only [hgt, ↓reduceIte, add_zero]
    exact farEntry_near_sum_le hL3 (fun a b => ‖loopPM L W E v M a b‖) (fun _ _ => norm_nonneg _)
      Q.1 P.1
  · have h1 : feInd L W τ' v P Q = 0 := by simp [feInd, hf]
    simp [h1]

/-- The step at one size index: on the far set, `1_far ‖𝓛_{(a',b')}‖ > 3 N^τ W^{-D₂}` forces
`|𝓛 - 𝒦| > N^τ ·(right side of Step2DecayPT)`. -/
private theorem farEntry_term_step {E s v t κ 𝔠 δ τ' D₂ Nτ : ℝ}
    (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hL3 : 3 ≤ L) (hW1 : 1 ≤ W) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hbw : (((W * L) ^ 2 : ℕ) : ℝ) ^ 𝔠 ≤ (W : ℝ))
    (hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t)
    (hτ4 : 4 ≤ (W : ℝ) ^ τ') (hlog : Real.log (W : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤ (W : ℝ) ^ τ')
    (hK : ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
      ((W : ℝ) ^ (4 / 𝔠 + D₂) * Real.exp (-(1 / 2) * (W : ℝ) ^ (τ' / 2))) ≤ 1)
    (hTheta : ∀ a b : Z2 L, 1 * ellStar L W v ≤ (zdist2 L (a - b) : ℝ) →
      ‖Theta L (v : ℂ) a b‖ ≤ (W : ℝ) ^ (-D₂))
    (hNτ : 1 ≤ Nτ) (P Q : BlockIndex L W) (i j : Fin 5)
    (h : Nτ * (3 * (W : ℝ) ^ (-D₂)) <
      feInd L W τ' v P Q * ‖loopPM L W E v M (Q.1 + farOff L i) (P.1 + farOff L j)‖) :
    Nτ * ((etaT E s / etaT E v) ^ 4 * (scaleM L W E v ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L ((Q.1 + farOff L i) - (P.1 + farOff L j)) : ℝ) /
          ellT L v)) + (W : ℝ) ^ (-D₂)) <
      lkErrMat L W E v M (Q.1 + farOff L i) (P.1 + farOff L j) := by
  have hWpos : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    linarith
  have ha2 : 0 ≤ (W : ℝ) ^ (-D₂) := Real.rpow_nonneg hWpos.le _
  unfold feInd at h
  split_ifs at h with hf
  · obtain ⟨hK', hζ⟩ := farEntry_pair_bounds (E := E) (s := s) (v := v) (t := t) (κ := κ)
      (𝔠 := 𝔠) (δ := δ) (τ' := τ') (D₂ := D₂) hL3 hW1 hκ hE h𝔠 hδ hs0 hsv hvt ht1 hbw hrange
      hτ4 hlog hK hTheta (P := P.1) (Q := Q.1) hf
      (a' := Q.1 + farOff L i) (b' := P.1 + farOff L j)
      (by rw [add_sub_cancel_left]; exact farOff_zdist2_le hL3 i)
      (by rw [add_sub_cancel_left]; exact farOff_zdist2_le hL3 j)
    have hnorm : ‖loopPM L W E v M (Q.1 + farOff L i) (P.1 + farOff L j)‖ ≤
        ‖Kpm L W E v (Q.1 + farOff L i) (P.1 + farOff L j)‖ +
          lkErrMat L W E v M (Q.1 + farOff L i) (P.1 + farOff L j) := by
      unfold lkErrMat loopPM
      calc ‖gloop L W (blockMat M) (spectralZ E v) (pmLoop (Q.1 + farOff L i) (P.1 + farOff L j))‖
          = ‖(gloop L W (blockMat M) (spectralZ E v) (pmLoop (Q.1 + farOff L i) (P.1 + farOff L j))
              - Kpm L W E v (Q.1 + farOff L i) (P.1 + farOff L j)) +
              Kpm L W E v (Q.1 + farOff L i) (P.1 + farOff L j)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ = _ := add_comm _ _
    have h5 : Nτ * ((etaT E s / etaT E v) ^ 4 * (scaleM L W E v ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 L ((Q.1 + farOff L i) - (P.1 + farOff L j)) : ℝ) /
          ellT L v)) + (W : ℝ) ^ (-D₂)) ≤ Nτ * (2 * (W : ℝ) ^ (-D₂)) :=
      mul_le_mul_of_nonneg_left hζ (by linarith)
    have h6 : 0 ≤ (Nτ - 1) * (W : ℝ) ^ (-D₂) := mul_nonneg (by linarith) ha2
    rw [one_mul] at h
    nlinarith
  · exfalso
    rw [zero_mul] at h
    have : 0 ≤ Nτ * (3 * (W : ℝ) ^ (-D₂)) := by
      have : 0 ≤ Nτ := by linarith
      positivity
    linarith

end PerSize

/-! ## The statements -/

/-- **`FarEntryDecayPT`**: the far-entry decay of the resolvent on the Step 2 window,
`|G_u(x,y)| 1[W^{τ'} ℓ_u ≤ |[x] - [y]|_L] ≺ W^{-D'}` for every `τ', D' > 0`, per time on
`[s_n, t_n]` and every pair of block indices `(p, q)` (`x = p`, `y = q`, `[x] = p.1`);
energy `E n`, resolvent of `Sizes.seqHflow d n u` at `spectralZ (E n) u` in block form
(`greenBlk … true`, as `RBM.Green.offSq`).  Paper: proof of `clt-lemma` (`clt-gij-decay`). -/
def FarEntryDecayPT (d : Sizes) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ),
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
      (fun n p ω =>
        ‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2.1 p.2.2‖ *
          (if (d.W n : ℝ) ^ τ' * ellT (d.L n) p.1 ≤ (zdist2 (d.L n) (p.2.1.1 - p.2.2.1) : ℝ)
            then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-D'))

/-- The index type of the per-time statements of this file. -/
private abbrev FU (d : Sizes) (s t : ℕ → ℝ) (n : ℕ) : Type :=
  TimeIcc s t n × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)

/-- `Step2LocalPT` restricts to a shorter window `[s, t] ⊆ [s, t']` (`t ≤ t'`): the `Clt`
statements carry the window `[s₀, t₀] ∋ u` and are applied to `[s₀, u]`. -/
theorem farEntry_step2LocalPT_mono (d : Sizes) {E s t t' : ℕ → ℝ} (hle : ∀ n, t n ≤ t' n)
    (h : Step2LocalPT d E s t') : Step2LocalPT d E s t := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn u
  exact hn (⟨u.1.1, u.1.2.1, u.1.2.2.trans (hle n)⟩, u.2)

/-- `Step2DecayPT` restricts to a shorter window `[s, t] ⊆ [s, t']` (`t ≤ t'`). -/
theorem farEntry_step2DecayPT_mono (d : Sizes) {E s t t' : ℕ → ℝ} (hle : ∀ n, t n ≤ t' n)
    (h : Step2DecayPT d E s t') : Step2DecayPT d E s t := by
  intro D hD τ hτ D' hD'
  filter_upwards [h D hD τ hτ D' hD'] with n hn u
  exact hn (⟨u.1.1, u.1.2.1, u.1.2.2.trans (hle n)⟩, u.2)

/-- **`farEntryDecayPT`**: from `GbEXPHypV3` (`GijGEX`, without the indicator
under (`asGMc`), `lem_GbEXP`) and the Step 2 outputs `Step2LocalPT`, `Step2DecayPT` on the window
`[s, t]`, the resolvent entries between far blocks satisfy `FarEntryDecayPT`.  The hypotheses are
the Step 2 part of those of `CltCase1Prec`/`CltCase2Prec` at `(s₀, u) := (s, t)`; see
`farEntryDecayPT_clt` for the form with the `Clt` window `[s₀, t₀] ∋ u`. -/
theorem farEntryDecayPT (d : Sizes) {E s t : ℕ → ℝ} {κ 𝔠 δ : ℝ}
    (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hN : SizeTendsto d) (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t)
    (hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ)
    (hLoc : Step2LocalPT d E s t) (hDec : Step2DecayPT d E s t) :
    FarEntryDecayPT d E s t := by
  intro τ' hτ' D' hD'
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hNc : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  have hWtop : Tendsto (fun n => (d.W n : ℝ)) atTop atTop := tendsto_atTop_mono' _ hW hNc
  have hD2 : 0 < 2 * D' := by linarith
  -- (asGMc) at `c = min(2𝔠, δ)/2`, from `Step2LocalPT` (r4)
  have hAs : RBM.Green.AsGMcPT d E s t (min (2 * 𝔠) δ / 2) := by
    have hc : 0 < min (2 * 𝔠) δ / 2 := by
      have := lt_min (by linarith : (0 : ℝ) < 2 * 𝔠) hδ
      linarith
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (((Real.sqrt (κ * (4 - κ)) / 2)⁻¹) ^ ((1 : ℝ) / 2)) ?_ hLoc
    filter_upwards [hW, hR] with n hbw hrange
    intro u ω
    exact farEntry_local_le (d.three_le_L n) (d.W_pos n) hκ (hE n) h𝔠 hδ u.1.2.2 (ht n) hbw hrange
  have hbr := RBM.Green.gijGEXPTSwap_giiGEXPT_of_V3 d hV3 hN hW
    (fun n => by have := hE n; linarith) hs hst ht hR
    (by have := lt_min (by linarith : (0 : ℝ) < 2 * 𝔠) hδ; linarith) hAs
  -- pointwise nonnegativity and the positivity of the far threshold
  have hpos : ∀ (n : ℕ) (u : FU d s t n),
      0 < (d.W n : ℝ) ^ τ' * ellT (d.L n) u.1 := by
    intro n u
    have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
    exact mul_pos (Real.rpow_pos_of_pos hW0 _)
      (ellT_pos_le (by have := d.three_le_L n; omega) (u.1.2.2.trans_lt (ht n))).1
  -- (1) `(‖G‖ 1_far)² ≺ 1_far · gexRHS`, from (`GijGEX`) without the indicator
  have h3a : PerTimeDomAt (Sizes.seqP d) d.size (U := FU d s t)
      (fun n p ω => (‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true
          p.2.1 p.2.2‖ * feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2) ^ 2)
      (fun n p ω => feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 *
        gexRHS (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.2.1 p.2.1.1) := by
    refine PerTimeCalc.PerTime.perTimeCalc_of_imp hbr.1 ?_
    intro τ hτ
    refine ⟨τ, hτ, Eventually.of_forall ?_⟩
    intro n p ω h
    show (d.size n : ℝ) ^ τ * gexRHS (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
        p.2.2.1 p.2.1.1 <
      (if p.2.1 = p.2.2 then 0 else
        ‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2.1 p.2.2‖ ^ 2)
    rw [farEntry_sq_eq τ' _ (hpos n p)] at h
    by_cases hf : (d.W n : ℝ) ^ τ' * ellT (d.L n) p.1 ≤
        (zdist2 (d.L n) (p.2.1.1 - p.2.2.1) : ℝ)
    · have h1 : feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 = 1 := by simp [feInd, hf]
      rw [h1, one_mul, one_mul] at h
      exact h
    · have h1 : feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 = 0 := by simp [feInd, hf]
      rw [h1, zero_mul, zero_mul] at h
      exact absurd h (not_lt.2 (by simp))
  -- eventual deterministic inputs
  have hlogev : ∀ᶠ n : ℕ in atTop, 4 ≤ (d.W n : ℝ) ^ τ' ∧
      Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤ (d.W n : ℝ) ^ τ' :=
    hWtop.eventually (farEntry_eventually_log τ' hτ')
  have hm0 : 0 < (Real.sqrt (κ * (4 - κ)) / 2) ^ 2 := by
    have hκ2 : κ ≤ 2 := by have := abs_nonneg (E 0); have := hE 0; linarith
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  have hKev : ∀ᶠ n : ℕ in atTop, ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
      ((d.W n : ℝ) ^ (4 / 𝔠 + 2 * D') * Real.exp (-(1 / 2) * (d.W n : ℝ) ^ (τ' / 2))) ≤ 1 := by
    have h1 := farEntry_tendsto_rpow_exp (4 / 𝔠 + 2 * D') (1 / 2) (τ' / 2) (by norm_num)
      (by linarith)
    have h2 := (h1.comp hWtop).eventually (gt_mem_nhds hm0)
    filter_upwards [h2] with n hn
    calc ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ *
        ((d.W n : ℝ) ^ (4 / 𝔠 + 2 * D') * Real.exp (-(1 / 2) * (d.W n : ℝ) ^ (τ' / 2)))
        ≤ ((Real.sqrt (κ * (4 - κ)) / 2) ^ 2)⁻¹ * (Real.sqrt (κ * (4 - κ)) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hn.le (inv_nonneg.2 hm0.le)
      _ = 1 := inv_mul_cancel₀ hm0.ne'
  have hKell := kellStarEv d 𝔠 δ 1 (2 * D') t h𝔠 hδ one_pos hsize hW hR ht
  have hsize1 : ∀ᶠ n : ℕ in atTop, 1 ≤ d.size n := hsize.eventually (eventually_ge_atTop 1)
  -- (2) each of the 25 neighbouring loops: `1_far ‖𝓛_{(a',b')}‖ ≺ 3 W^{-2D'}`
  have hterm : ∀ ij : Fin 5 × Fin 5, PerTimeDomAt (Sizes.seqP d) d.size (U := FU d s t)
      (fun n p ω => feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 *
        ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (p.2.2.1 + farOff (d.L n) ij.1) (p.2.1.1 + farOff (d.L n) ij.2)‖)
      (fun n _ _ => 3 * (d.W n : ℝ) ^ (-(2 * D'))) := by
    intro ij
    have hc := farEntry_perTime_comp (U' := FU d s t)
      (g := fun n p => (p.1, p.2.2.1 + farOff (d.L n) ij.1, p.2.1.1 + farOff (d.L n) ij.2))
      (hDec (2 * D') hD2)
    refine PerTimeCalc.PerTime.perTimeCalc_of_imp hc ?_
    intro τ hτ
    refine ⟨τ, hτ, ?_⟩
    filter_upwards [hW, hR, hlogev, hKev, hKell, hsize1] with n hbw hrange hlg hK hKe hs1
    intro p ω h
    have hNτ : (1 : ℝ) ≤ (d.size n : ℝ) ^ τ :=
      Real.one_le_rpow (by exact_mod_cast hs1) hτ.le
    have hTheta : ∀ a b : Z2 (d.L n), 1 * ellStar (d.L n) (d.W n) p.1 ≤
        (zdist2 (d.L n) (a - b) : ℝ) → ‖Theta (d.L n) ((p.1 : ℝ) : ℂ) a b‖ ≤
          (d.W n : ℝ) ^ (-(2 * D')) := fun a b hab =>
      (hKe 0 p.1 le_rfl ((hs n).trans p.1.2.1) p.1.2.2 a b hab).1
    exact farEntry_term_step (E := E n) (s := s n) (v := p.1) (t := t n) (κ := κ) (𝔠 := 𝔠)
      (δ := δ) (τ' := τ') (D₂ := 2 * D') (Sizes.seqHflow d n p.1 ω) (d.three_le_L n)
      (d.W_pos n) hκ (hE n) h𝔠 hδ (hs n) p.1.2.1 p.1.2.2 (ht n) hbw hrange hlg.1 hlg.2 hK
      hTheta hNτ p.2.1 p.2.2 ij.1 ij.2 h
  -- (3) the sum of the 25 terms
  have hsum := PerTimeCalc.PerTime.finset_sum_of hsize (Finset.univ : Finset (Fin 5 × Fin 5))
    (ξ := fun ij n (p : FU d s t n) ω => feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 *
        ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          (p.2.2.1 + farOff (d.L n) ij.1) (p.2.1.1 + farOff (d.L n) ij.2)‖)
    (ζ := fun _ n (_ : FU d s t n) _ => 3 * (d.W n : ℝ) ^ (-(2 * D')))
    (fun ij _ => hterm ij)
  have h3b : PerTimeDomAt (Sizes.seqP d) d.size (U := FU d s t)
      (fun n p ω => feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 *
        gexRHS (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.2.1 p.2.1.1)
      (fun n _ _ => 75 * (d.W n : ℝ) ^ (-(2 * D'))) := by
    have hsum' : PerTimeDomAt (Sizes.seqP d) d.size (U := FU d s t)
        (fun n p ω => ∑ ij : Fin 5 × Fin 5, feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 *
          ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
            (p.2.2.1 + farOff (d.L n) ij.1) (p.2.1.1 + farOff (d.L n) ij.2)‖)
        (fun n _ _ => 75 * (d.W n : ℝ) ^ (-(2 * D'))) := by
      have hc : ∀ x : ℝ, ∑ _ij : Fin 5 × Fin 5, 3 * x = 75 * x := by
        intro x
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring
      exact PerTimeCalc.PerTime.mono_right_eventually hsum
        (Eventually.of_forall fun n u ω => le_of_eq (hc _))
    refine PerTimeCalc.PerTime.stochDom_of_le_left_eventually ?_ hsum'
    filter_upwards [hlogev] with n hlg
    intro p ω
    exact farEntry_ind_gexRHS_le (d.three_le_L n) _ p.2.1 p.2.2
      (by linarith [hlg.1])
      (one_le_ellT (by have := d.three_le_L n; omega) ((hs n).trans p.1.2.1)
        (p.1.2.2.trans_lt (ht n)))
  -- (4) transitivity, square root, constants
  have h3 := farEntry_trans hsize h3a h3b
  have h4 := PerTimeCalc.PerTime.sqrt_of (fun n p ω => sq_nonneg _)
    (fun n p ω => by positivity) h3
  have h5 : PerTimeDomAt (Sizes.seqP d) d.size (U := FU d s t)
      (fun n p ω => Real.sqrt ((‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω)
          true p.2.1 p.2.2‖ * feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2) ^ 2))
      (fun n _ _ => (d.W n : ℝ) ^ (-D')) := by
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) 9 ?_ h4
    refine Eventually.of_forall fun n u ω => ?_
    have ha : 0 ≤ (d.W n : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hW0 : (0 : ℝ) ≤ d.W n := Nat.cast_nonneg _
    have hsq : (d.W n : ℝ) ^ (-(2 * D')) = ((d.W n : ℝ) ^ (-D')) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]
      congr 1; push_cast; ring
    rw [hsq]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((d.W n : ℝ) ^ (-D'))]
  refine PerTimeCalc.PerTime.perTimeCalc_of_imp h5 ?_
  intro τ hτ
  refine ⟨τ, hτ, Eventually.of_forall ?_⟩
  intro n p ω h
  have hX : 0 ≤ ‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true
      p.2.1 p.2.2‖ * feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2 :=
    mul_nonneg (norm_nonneg _) (feInd_nonneg _ _ _ _)
  change (d.size n : ℝ) ^ τ * (d.W n : ℝ) ^ (-D') <
    Real.sqrt ((‖greenBlk (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true
      p.2.1 p.2.2‖ * feInd (d.L n) (d.W n) τ' p.1 p.2.1 p.2.2) ^ 2)
  rw [Real.sqrt_sq hX]
  exact h

/-- **`farEntryDecayPT` on the `Clt` window**: the
hypotheses are exactly the Step 2 part of those of `CltCase1Prec`/`CltCase2Prec`/
`SumDecayCase3Prec` (window `[s₀, t₀] ∋ u`, end time `t` with `u ≤ t < 1` and `RangeCond d δ t`),
and the conclusion is `FarEntryDecayPT` on `[s₀, u]`. -/
theorem farEntryDecayPT_clt (d : Sizes) {E s₀ t₀ u t : ℕ → ℝ} {κ 𝔠 δ : ℝ}
    (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs₀ : ∀ n, 0 ≤ s₀ n) (hsu : ∀ n, s₀ n ≤ u n)
    (hut₀ : ∀ n, u n ≤ t₀ n) (hut : ∀ n, u n ≤ t n) (ht : ∀ n, t n < 1)
    (hN : SizeTendsto d) (hW : Bandwidth d 𝔠) (hR : RangeCond d δ t)
    (hLoc : Step2LocalPT d E s₀ t₀) (hDec : Step2DecayPT d E s₀ t₀)
    (hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ) :
    FarEntryDecayPT d E s₀ u :=
  farEntryDecayPT d hκ h𝔠 hδ hE hs₀ hsu (fun n => (hut n).trans_lt (ht n)) hN hW
    (RBM.Green.rangeCond_mono d hR hut) hV3
    (farEntry_step2LocalPT_mono d hut₀ hLoc) (farEntry_step2DecayPT_mono d hut₀ hDec)

end RBM.Evol

end
