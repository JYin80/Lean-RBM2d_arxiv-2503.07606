/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.DuhamelTail
import RBM2D.Path.GoodSet
import RBM2D.Path.Transfer
import RBM2D.Induction.Defs
import RBM2D.Induction.Chain

/-!
# The grid stopping index, the initial event, the grid size and the Chebyshev event

The `J*` half of the stopping index `gridTau`, the full stopping index `gridTauFull`, the
initial event on the grid, the grid size `CK`/`gridK`, the quadratic part (`YvecCut` and the
Chebyshev event at the stopping index), `ZvecCut`, and a matrix-level `gloop` measurability
helper.

Setting for `d = 2`: labels `Z2 L × Z2 L` (`L⁴` labels), the two-index `Uop` at
`ξ = |m(E_n)|²`, the good set `goodSet` of `Path/GoodSet.lean`, the walk `pathH`/`pathP`/`filt`,
the size index `n` with `N = size n = (W L)²`, and an energy sequence `E`.

## Main declarations

* `gridTau`: the `J*` half of the stopping index.
* `gridTauFull`: `min` of `gridTau` and the good-set exit index;
  `lt_gridTauFull_measurableSet`, `lt_gridTauFull_imp`, `gridTauFull_le`.
* `initSet`, `measurableSet_initSet`, `jStarMat_le_of_mem_initSet`, `highProb_init_grid`.
* `CK`, `gridK`, `gridK_ne_zero`, `rpow_CK_le_gridK`, `step_gridK_le`, `gridK_card_le`.
* `YvecCut`, `YvecCut_succ`, `stronglyMeasurable_YvecCut`, `GoodEvent_Yterm_inputs`
  (the per-step inputs), `cheb_grid_at_tau`.
* `ZvecCut`, `ZvecCut_succ`, `stronglyMeasurable_ZvecCut`.
* `GoodEvent_measurable_gloop`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## The `J*` half of the stopping index -/

/-- The grid stopping index: the first `k ≤ K_n` with `J*_{u_k,D}(H_k) ≥ Θ(u_k)`, else `K_n`.
The good-set exit is a second `firstHit` and is not part of this index.  The energy is a
sequence `E`: `J*` at `E n`, `Θ = thr d E s δ n`. -/
def gridTau (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (δ D : ℝ) (n : ℕ) (ω : PathΩ d) : ℕ :=
  hittingBtwn (fun k ω' => jStarMat (d.L n) (d.W n) (E n) D (gridTime s t K n k)
      (pathH d s t K n k ω') - thr d E s δ n (gridTime s t K n k)) (Set.Ici 0) 0 (K n) ω

/-! ## Grid-time facts -/

section GridTime

variable {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

theorem GoodEvent_gridStep_nonneg (hst : s n ≤ t n) : 0 ≤ gridStep s t K n :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

theorem GoodEvent_gridTime_mono (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := GoodEvent_gridStep_nonneg (K := K) hst
  have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold gridTime
  nlinarith

theorem GoodEvent_gridTime_zero : gridTime s t K n 0 = s n := by
  simp [gridTime]

theorem GoodEvent_gridTime_nonneg (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (k : ℕ) :
    0 ≤ gridTime s t K n k := by
  have h := GoodEvent_gridTime_mono (K := K) hst (Nat.zero_le k)
  rw [GoodEvent_gridTime_zero] at h
  linarith

/-- Every grid time up to the horizon is at most the endpoint, also when `K n = 0`
(then `Δ = 0` and every grid time is `s n`). -/
theorem GoodEvent_gridTime_le (hst : s n ≤ t n) {k : ℕ} (hk : k ≤ K n) :
    gridTime s t K n k ≤ t n := by
  by_cases hK : K n = 0
  · have : gridStep s t K n = 0 := by simp [gridStep, hK]
    simp [gridTime, this, hst]
  · have h := GoodEvent_gridTime_mono (K := K) hst hk
    rwa [gridTime_last s t K n hK] at h

end GridTime

/-! ## The stopping index -/

section T1

/-- **The full grid stopping index**: the minimum of the `J*` index `gridTau` and the first
`k ≤ K_n` with `H_k ∉ goodSet … (E n) (s n) u_{min(k,K_n)} (N^ε)` (else `K_n`), written as the
first hit of level `1/2` by the indicator of the complement.  The good set is taken at the
clamped time `u_{min(k,K_n)}`, which is `< 1` for every `k`; on the indices `k ≤ K_n` that
`hittingBtwn` reads, it is `u_k`. -/
def gridTauFull (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (δ D ε : ℝ) (n : ℕ) (ω : PathΩ d) : ℕ :=
  min (gridTau d E s t K δ D n ω)
    (firstHit (fun k (ω' : PathΩ d) =>
        (goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s t K n (min k (K n)))
          (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ)) (pathH d s t K n k ω'))
      (1 / 2) (K n) ω)

variable {d}

private theorem GoodEvent_measurable_tauJ (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (δ D : ℝ)
    (n j : ℕ) :
    Measurable (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      jStarMat (d.L n) (d.W n) (E n) D (gridTime s t K n j) M
        - thr d E s δ n (gridTime s t K n j)) :=
  (measurable_jStarMat (d.L n) (d.W n) (E n) D _).sub measurable_const

private theorem GoodEvent_measurable_tauG {E : ℕ → ℝ} {s t : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2)
    (hst : s n ≤ t n) (ht1 : t n < 1) (K : ℕ → ℕ) (ε : ℝ) (j : ℕ) :
    Measurable (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      (goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s t K n (min j (K n)))
        (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ)) M) := by
  have hu : gridTime s t K n (min j (K n)) < 1 :=
    (GoodEvent_gridTime_le hst (min_le_right _ _)).trans_lt ht1
  exact measurable_const.indicator
    ((measurableGoodSet (d.L n) (d.W n) (E n) (s n) _ _ hE hu).compl)

/-- `{j < gridTauFull}` is `filt d j`-measurable. -/
theorem lt_gridTauFull_measurableSet {E : ℕ → ℝ} {s t : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2)
    (hst : s n ≤ t n) (ht1 : t n < 1) (K : ℕ → ℕ) (δ D ε : ℝ) (j : ℕ) :
    MeasurableSet[filt d j] {ω | j < gridTauFull d E s t K δ D ε n ω} :=
  lt_min_firstHit_grid_measurableSet d s t K n
    (F := fun j M => jStarMat (d.L n) (d.W n) (E n) D (gridTime s t K n j) M
      - thr d E s δ n (gridTime s t K n j))
    (F' := fun j M => (goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s t K n (min j (K n)))
      (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (GoodEvent_measurable_tauJ E s t K δ D n) (GoodEvent_measurable_tauG hE hst ht1 K ε) 0 (1 / 2)
    (K n) j

/-- `gridTauFull ≤ K n`. -/
theorem gridTauFull_le (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (δ D ε : ℝ) (n : ℕ)
    (ω : PathΩ d) : gridTauFull d E s t K δ D ε n ω ≤ K n :=
  (min_le_right _ _).trans (firstHit_le _ _ _ ω)

/-- Strictly before `gridTauFull`, `J*` is below the threshold and the grid state is in
the good set at the (unclamped) grid time `u_j`. -/
theorem lt_gridTauFull_imp {E : ℕ → ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} {δ D ε : ℝ} {n j : ℕ}
    {ω : PathΩ d} (h : j < gridTauFull d E s t K δ D ε n ω) :
    jStarMat (d.L n) (d.W n) (E n) D (gridTime s t K n j) (pathH d s t K n j ω)
        < thr d E s δ n (gridTime s t K n j) ∧
      pathH d s t K n j ω ∈
        goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s t K n j) (((d.size n : ℕ) : ℝ) ^ ε) := by
  have hjK : j < K n := lt_of_lt_of_le h (gridTauFull_le E s t K δ D ε n ω)
  obtain ⟨h1, h2⟩ := lt_min_firstHit_imp
    (fun k (ω' : PathΩ d) => jStarMat (d.L n) (d.W n) (E n) D (gridTime s t K n k)
      (pathH d s t K n k ω') - thr d E s δ n (gridTime s t K n k))
    (fun k (ω' : PathΩ d) => (goodSet (d.L n) (d.W n) (E n) (s n)
      (gridTime s t K n (min k (K n))) (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ))
      (pathH d s t K n k ω'))
    0 (1 / 2) (K n) h
  refine ⟨by linarith, ?_⟩
  have hmin : min j (K n) = j := min_eq_left hjK.le
  by_contra hmem
  have h2' : (goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s t K n (min j (K n)))
      (((d.size n : ℕ) : ℝ) ^ ε))ᶜ.indicator (fun _ => (1 : ℝ)) (pathH d s t K n j ω) < 1 / 2 := h2
  rw [hmin, Set.indicator_of_mem (Set.mem_compl hmem)] at h2'
  norm_num at h2'

end T1

/-! ## The initial value on the grid -/

section T5

/-- The matrix set of the initial bound at time `v` with multiplier `x`:
`lkErrMat(v, M)_{ab} ≤ x · 𝒯_{v,D}(|a - b|_L)` for all labels `a b : Z2 L`. -/
def initSet (L W : ℕ) [NeZero L] [NeZero W] (E v D x : ℝ) : Set (Matrix (Idx L W) (Idx L W) ℂ) :=
  {M | ∀ a b : Z2 L, lkErrMat L W E v M a b ≤ x * tailT L W E D v (zdist2 L (a - b) : ℝ)}

/-- `initSet` is measurable. -/
theorem measurableSet_initSet (L W : ℕ) [NeZero L] [NeZero W] (E v D x : ℝ) :
    MeasurableSet (initSet L W E v D x) := by
  have heq : initSet L W E v D x = ⋂ a : Z2 L, ⋂ b : Z2 L,
      {M | lkErrMat L W E v M a b ≤ x * tailT L W E D v (zdist2 L (a - b) : ℝ)} := by
    ext M; simp [initSet]
  rw [heq]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_le (measurable_lkErrMat L W E v a b) measurable_const

/-- On `initSet … x`, `J* ≤ x + 1`. -/
theorem jStarMat_le_of_mem_initSet {L W : ℕ} [NeZero L] [NeZero W] {E v D x : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ initSet L W E v D x) :
    jStarMat L W E D v M ≤ x + 1 := by
  unfold jStarMat
  refine add_le_add (Finset.sup'_le _ _ fun p _ => ?_) le_rfl
  have hT := tailT_pos (Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)) L E D v
    (zdist2 L (p.1 - p.2) : ℝ)
  rw [div_le_iff₀ hT]
  exact hM p.1 p.2

variable {d}

/-- The label count `#(Unit × Z2 L × Z2 L) = L⁴ ≤ N²`. -/
private theorem GoodEvent_card_le_size_sq (n : ℕ) :
    (Fintype.card (Unit × Z2 (d.L n) × Z2 (d.L n)) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [Real.rpow_two]
  have hW : 1 ≤ d.W n := d.W_pos n
  have hc : Fintype.card (Unit × Z2 (d.L n) × Z2 (d.L n)) = (d.L n) ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_unit, one_mul, Z2, ZMod.card]
    ring
  rw [hc]
  have h : (d.L n) ^ 4 ≤ (d.size n) ^ 2 := by
    unfold Sizes.size
    calc (d.L n) ^ 4 ≤ (d.W n * d.L n) ^ 4 :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) 4
      _ = ((d.W n * d.L n) ^ 2) ^ 2 := by ring
  exact_mod_cast h

/-- **`highProb_init_grid`**: with high probability the grid initial value obeys
`‖A_0(a)‖ ≤ N^{δ/16} 𝒯_{u_0,D}(|a.1 - a.2|_L)` for every label and `J*` starts below the
threshold, `J*_{u_0}(H_0) < Θ(u_0) = N^δ`.  Source: `InitDecay` (`Eq:Gdecay+IND` at `s`),
transferred to the grid by the law of `H_0` (`map_pathH_eq` at `k = 0`); `L⁴ ≤ N²` labels. -/
theorem highProb_init_grid {E : ℕ → ℝ} {s v : ℕ → ℝ} (hInit : InitDecay d E s)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    {K : ℕ → ℕ} (hK0 : ∀ n, K n ≠ 0) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (hsize : RBM.Ind.SizeTendsto d) :
    HighProbAt (pathP d) d.size (fun n => {ω : PathΩ d |
      (∀ a : Z2 (d.L n) × Z2 (d.L n), ‖Avec d (E n) s v K n 0 ω a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (δ / 16) *
          tailT (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (zdist2 (d.L n) (a.1 - a.2) : ℝ))
      ∧ jStarMat (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (pathH d s v K n 0 ω)
        < thr d E s δ n (gridTime s v K n 0)}) := by
  intro D' hD'
  have hδ16 : 0 < δ / 16 := by positivity
  have hSD := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := 2) (by norm_num)
    (Eventually.of_forall fun n => GoodEvent_card_le_size_sq n) (hInit D hD)
  have hy : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (δ / 16) :=
    ((tendsto_rpow_atTop hδ16).comp hsize).eventually_ge_atTop 2
  filter_upwards [hSD (δ / 16) hδ16 D' hD', hy] with n hn hyn
  set y : ℝ := ((d.size n : ℕ) : ℝ) ^ (δ / 16) with hydef
  set S := initSet (d.L n) (d.W n) (E n) (s n) D y with hSdef
  have hu0 : gridTime s v K n 0 = s n := GoodEvent_gridTime_zero
  -- the complement of the event lies in `{H_0 ∉ S}`
  have hsub : {ω : PathΩ d |
      (∀ a : Z2 (d.L n) × Z2 (d.L n), ‖Avec d (E n) s v K n 0 ω a‖ ≤
        y * tailT (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (zdist2 (d.L n) (a.1 - a.2) : ℝ))
      ∧ jStarMat (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (pathH d s v K n 0 ω)
        < thr d E s δ n (gridTime s v K n 0)}ᶜ ⊆ (pathH d s v K n 0) ⁻¹' Sᶜ := by
    intro ω hω
    rw [Set.mem_compl_iff] at hω
    rw [Set.mem_preimage, Set.mem_compl_iff]
    intro hS
    apply hω
    refine ⟨fun a => ?_, ?_⟩
    · have e : ‖Avec d (E n) s v K n 0 ω a‖ = lkErrMat (d.L n) (d.W n) (E n)
          (gridTime s v K n 0) (pathH d s v K n 0 ω) a.1 a.2 := rfl
      rw [e, hu0]; exact hS a.1 a.2
    · rw [hu0]
      have hj := jStarMat_le_of_mem_initSet hS
      have hs1 : s n < 1 := (hsv n).trans_lt (hv1 n)
      have hη : etaT (E n) (s n) ≠ 0 := (etaT_pos (hE n) hs1).ne'
      have hthr : thr d E s δ n (s n) = ((d.size n : ℕ) : ℝ) ^ δ := by
        unfold thr; rw [div_self hη]; ring
      rw [hthr]
      have hpow : y ^ (16 : ℕ) = ((d.size n : ℕ) : ℝ) ^ δ := by
        rw [hydef, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 1; push_cast; ring
      rw [← hpow]
      have h16 : y ^ (2 : ℕ) ≤ y ^ (16 : ℕ) :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
  -- law of `H_0`
  have hHmeas : Measurable (pathH d s v K n 0) :=
    (pathH_measurable_filt d s v K n 0).mono ((filt d).le 0) le_rfl
  have hFmeas : Measurable (Sizes.seqHflow d n (s n)) :=
    Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n (s n) i j
  have hSmeas : MeasurableSet S := measurableSet_initSet _ _ _ _ _ _
  have hlaw : (pathP d) ((pathH d s v K n 0) ⁻¹' Sᶜ)
      = (Sizes.seqP d) ((Sizes.seqHflow d n (s n)) ⁻¹' Sᶜ) := by
    rw [← Measure.map_apply hHmeas hSmeas.compl, ← Measure.map_apply hFmeas hSmeas.compl,
      map_pathH_eq d s v K n 0 (hs0 n) (hsv n) (hK0 n), hu0]
  -- `{seqHflow ∉ S}` lies in the bad set of `InitDecay`
  have hbad : (Sizes.seqHflow d n (s n)) ⁻¹' Sᶜ ⊆
      badSetAt d.size
        (fun n (p : Unit × Z2 (d.L n) × Z2 (d.L n)) ω =>
          lkErrMat (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)
        (fun n (p : Unit × Z2 (d.L n) × Z2 (d.L n)) _ =>
          (scaleM (d.L n) (d.W n) (E n) (s n) ^ 2)⁻¹ *
            Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (s n))) +
          (d.W n : ℝ) ^ (-D)) (δ / 16) n := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff, hSdef, initSet, Set.mem_ofPred_eq,
      not_forall, not_le] at hω
    obtain ⟨a, b, hab⟩ := hω
    exact ⟨((), a, b), hab⟩
  calc (pathP d) _ ≤ (pathP d) ((pathH d s v K n 0) ⁻¹' Sᶜ) := measure_mono hsub
    _ = (Sizes.seqP d) ((Sizes.seqHflow d n (s n)) ⁻¹' Sᶜ) := hlaw
    _ ≤ _ := measure_mono hbad
    _ ≤ _ := hn

end T5

/-! ## The grid size `CK`, `gridK` -/

section GridK

/-- **The grid-size exponent** `C_K(D, D₁) = D₁ + 2D + 80`. -/
def CK (D D₁ : ℝ) : ℝ := D₁ + 2 * D + 80

/-- **The grid size** `K_n = max 1 ⌈N^{C_K}⌉`, `N = size n`. -/
def gridK (D D₁ : ℝ) (n : ℕ) : ℕ := max 1 ⌈((d.size n : ℕ) : ℝ) ^ CK D D₁⌉₊

variable {d}

theorem gridK_ne_zero (D D₁ : ℝ) (n : ℕ) : gridK d D D₁ n ≠ 0 := by
  unfold gridK; omega

theorem rpow_CK_le_gridK (D D₁ : ℝ) (n : ℕ) :
    ((d.size n : ℕ) : ℝ) ^ CK D D₁ ≤ gridK d D D₁ n := by
  unfold gridK
  calc ((d.size n : ℕ) : ℝ) ^ CK D D₁ ≤ (⌈((d.size n : ℕ) : ℝ) ^ CK D D₁⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((max 1 ⌈((d.size n : ℕ) : ℝ) ^ CK D D₁⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast le_max_right _ _

/-- `N ≥ 1` for every size index. -/
theorem GoodEvent_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have hW : 1 ≤ d.W n := d.W_pos n
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have h : 1 ≤ d.size n := by
    unfold Sizes.size
    exact Nat.one_le_pow _ _ (Nat.mul_pos hW hL)
  exact_mod_cast h

/-- `Δ ≤ N^{-C_K}` on the grid `gridK`, once `v n - s n ≤ 1`. -/
theorem step_gridK_le {s v : ℕ → ℝ} {D D₁ : ℝ} {n : ℕ} (hvs : v n - s n ≤ 1) :
    gridStep s v (gridK d D D₁) n ≤ ((d.size n : ℕ) : ℝ) ^ (-CK D D₁) := by
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (GoodEvent_one_le_size n)
  have hpos : 0 < ((d.size n : ℕ) : ℝ) ^ CK D D₁ := Real.rpow_pos_of_pos hN0 _
  have hK := rpow_CK_le_gridK (d := d) D D₁ n
  have hK0 : (0 : ℝ) < gridK d D D₁ n := lt_of_lt_of_le hpos hK
  unfold gridStep
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc v n - s n ≤ 1 := hvs
    _ = (((d.size n : ℕ) : ℝ) ^ CK D D₁)⁻¹ * ((d.size n : ℕ) : ℝ) ^ CK D D₁ :=
        (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (((d.size n : ℕ) : ℝ) ^ CK D D₁)⁻¹ * gridK d D D₁ n :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- `gridK` has polynomially many points: `K_n + 1 ≤ N^{C_K + 2}` (it holds for every `n` since
`N ≥ 9`). -/
theorem gridK_card_le {D D₁ : ℝ} (hCK : 0 ≤ CK D D₁) :
    ∀ᶠ n : ℕ in atTop,
      ((gridK d D D₁ n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (CK D D₁ + 2) := by
  refine Eventually.of_forall fun n => ?_
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by
    have hW : 1 ≤ d.W n := d.W_pos n
    have hL : 3 ≤ d.L n := d.three_le_L n
    have h : 2 ≤ d.size n := by
      unfold Sizes.size
      calc 2 ≤ 3 ^ 2 := by norm_num
        _ ≤ (d.W n * d.L n) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    rw [hNdef]; exact_mod_cast h
  have hN0 : (0 : ℝ) < N := by linarith
  have hA1 : (1 : ℝ) ≤ N ^ CK D D₁ := Real.one_le_rpow (by linarith) hCK
  have hK : (gridK d D D₁ n : ℝ) ≤ N ^ CK D D₁ + 1 := by
    unfold gridK
    rcases le_total 1 ⌈N ^ CK D D₁⌉₊ with h | h
    · rw [max_eq_right h]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    · rw [max_eq_left h]; push_cast; linarith
  push_cast
  rw [Real.rpow_add hN0, Real.rpow_two]
  have hN4 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hN4 (by linarith : (0 : ℝ) ≤ N ^ CK D D₁)
  linarith

end GridK

/-! ## Measurability of the loop observables and of the one-step parts -/

section Measurability

set_option linter.unusedFintypeInType false in
private theorem GoodEvent_measurable_matrix_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix ι ι ℂ} (hM : Measurable M) (i j : ι) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

set_option linter.unusedFintypeInType false in
private theorem GoodEvent_measurable_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) : Measurable fun M : Matrix ι ι ℂ => M - z • (1 : Matrix ι ι ℂ) :=
  (continuous_id.sub continuous_const).measurable

private theorem GoodEvent_measurable_green {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (i j : ι) : Measurable fun M : Matrix ι ι ℂ => green M z i j :=
  GoodEvent_measurable_matrix_inv_apply (GoodEvent_measurable_sub_smul_one z) i j

private theorem GoodEvent_measurable_Gsig {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (σ : Bool) (i j : ι) : Measurable fun M : Matrix ι ι ℂ => Gsig M z σ i j := by
  cases σ
  · simpa [Gsig] using GoodEvent_measurable_green ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using GoodEvent_measurable_green z i j

private theorem GoodEvent_measurable_mul {ι : Type*} [Fintype ι]
    {Θ : Type*} [MeasurableSpace Θ] {A C : Θ → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hC : ∀ i j, Measurable fun x => C x i j)
    (i j : ι) : Measurable fun x => (A x * C x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

private theorem GoodEvent_measurable_gloopProd (L W : ℕ) [NeZero L] (z : ℂ)
    (I : LoopIdx (Z2 L)) (i j : BlockIndex L W) :
    Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloopProd L W H z I i j := by
  suffices h : ∀ l : List (Bool × Z2 L), ∀ i j : BlockIndex L W,
      Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => (l.foldr
        (fun (p : Bool × Z2 L) (Acc : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =>
          Gsig H z p.1 * Eblk L W p.2 * Acc)
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) i j by
    simpa [gloopProd] using h (I.σ.zip I.a) i j
  intro l
  induction l with
  | nil => intro i j; simp
  | cons p l ih =>
      intro i j
      simp only [List.foldr_cons]
      refine GoodEvent_measurable_mul ?_ (fun a b => ih a b) i j
      intro a b
      refine GoodEvent_measurable_mul (fun c e => GoodEvent_measurable_Gsig z p.1 c e)
        (C := fun _ => Eblk L W p.2) (fun _ _ => measurable_const) a b

/-- **The matrix-level `gloop` measurability helper**: for every spectral parameter `z` and loop
`I`, `M ↦ gloop L W (blockMat M) z I` is measurable on all matrices. -/
theorem GoodEvent_measurable_gloop (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => gloop L W (blockMat M) z I := by
  have h : ∀ H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ, gloop L W H z I
      = ∑ i : BlockIndex L W, gloopProd L W H z I i i := fun _ => rfl
  have hg : Measurable fun H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ => gloop L W H z I := by
    simp only [h]
    exact Finset.measurable_sum _ fun i _ => GoodEvent_measurable_gloopProd L W z I i i
  have hb : Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => blockMat M :=
    (continuous_id.matrix_submatrix _ _).measurable
  exact hg.comp hb

variable {d}

/-- The draw `ω l` is `filt d k`-measurable for `l ≤ k` (as in `pathH_adapted`, `Walk.lean`). -/
private theorem GoodEvent_measurable_coord {k l : ℕ} (hl : l ≤ k) :
    Measurable[filt d k] (fun ω : PathΩ d => ω l) := by
  have : (fun ω : PathΩ d => ω l)
      = (fun g : Set.Iic k → Sizes.SeqΩ d => g ⟨l, hl⟩)
        ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k))

private theorem GoodEvent_measurable_linTr (n : ℕ) :
    Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
        Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ => linTr (d := d) n p.1 p.2) := by
  unfold linTr Matrix.trace Matrix.diag
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ =>
    GoodEvent_measurable_mul (fun a b => measurable_fst.eval_matrix)
      (fun a b => measurable_snd.eval_matrix) i i)

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)

/-- `stepZ` of the two-loop family is `filt d (j+1)`-measurable, for any real kernel `U`. -/
private theorem GoodEvent_measurable_stepZ {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Measurable[filt d (j + 1)]
      (fun ω => stepZ d s t K n j (Expansion_loopObs d n E u) U b ω) := by
  have hΦ : ∀ a, HermTestFun d n (Expansion_loopObs d n E u a) :=
    fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).1
  have hReal : ∀ a (A : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), A.IsHermitian →
      (Expansion_loopObs d n E u a A).im = 0 :=
    fun a A hA => loopPM_real_of_herm d n E u a hA
  have hC := fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).2
  have hInt := stepDecomp_integrable_stepZ d s t K n j hΦ hReal hC hΔ U b
  have hA : Measurable[filt d (j + 1)]
      (fun ω => Ab d s t K n j (Expansion_loopObs d n E u) U b ω) :=
    (stepDecomp d s t K n j hΦ hReal hC hΔ U b hInt).2.1.mono ((filt d).mono (Nat.le_succ j))
      le_rfl
  have hX : Measurable[filt d (j + 1)] (fun ω : PathΩ d => Sizes.seqXmat d n (ω (j + 1))) :=
    ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).comp
      (GoodEvent_measurable_coord le_rfl)
  have hL := (GoodEvent_measurable_linTr (d := d) n).comp (hA.prodMk hX)
  exact hL.const_mul _

/-- `stepY` of the two-loop family is `filt d (j+1)`-measurable, for any real kernel `U`. -/
private theorem GoodEvent_measurable_stepY {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ) (b : Z2 (d.L n) × Z2 (d.L n)) :
    Measurable[filt d (j + 1)]
      (fun ω => stepY d s t K n j (Expansion_loopObs d n E u) U b ω) := by
  have hH := pathH_measurable_filt d s t K n (j + 1)
  have h1 : Measurable[filt d (j + 1)] (fun ω => ∑ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * Expansion_loopObs d n E u a (pathH d s t K n (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ =>
      ((GoodEvent_measurable_gloop (d.L n) (d.W n) (spectralZ E u) (pmLoop a.1 a.2)).comp
        hH).const_mul _
  have h2 : Measurable[filt d (j + 1)] ((pathP d)[fun ω' => ∑ a : Z2 (d.L n) × Z2 (d.L n),
      (U b a : ℂ) * Expansion_loopObs d n E u a (pathH d s t K n (j + 1) ω') | filt d j]) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have h3 := GoodEvent_measurable_stepZ s t K n j hE hu0 hu1 hΔ U b
  unfold stepY stepXi
  exact (h1.sub h2).sub (Complex.measurable_ofReal.comp h3)

end Measurability

/-! ## The cut increments `ZvecCut`, `YvecCut` -/

section Cuts

/-- The increments `Zvec i` cut to `1 ≤ i ≤ K_n` (`0` elsewhere). -/
def ZvecCut (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K n then (1 : ℂ) else 0) * Zvec d E s t K n i ω a

/-- The increments `Yvec i` cut to `1 ≤ i ≤ K_n` (`0` elsewhere). -/
def YvecCut (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ d)
    (a : Z2 (d.L n) × Z2 (d.L n)) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K n then (1 : ℂ) else 0) * Yvec d E s t K n i ω a

variable {d}

theorem ZvecCut_succ {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} {n j : ℕ} (hj : j < K n) :
    ZvecCut d E s t K n (j + 1) = Zvec d E s t K n (j + 1) := by
  funext ω a
  unfold ZvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K n then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

theorem YvecCut_succ {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} {n j : ℕ} (hj : j < K n) :
    YvecCut d E s t K n (j + 1) = Yvec d E s t K n (j + 1) := by
  funext ω a
  unfold YvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K n then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

/-- `ZvecCut i` is `filt d i`-strongly measurable for every `i`. -/
theorem stronglyMeasurable_ZvecCut {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (i : ℕ) :
    StronglyMeasurable[filt d i] (ZvecCut d E s t K n i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K n
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [ZvecCut_succ (by omega)]
    have hu0 := GoodEvent_gridTime_nonneg (K := K) hs0 hst (j + 1)
    have hu1 : gridTime s t K n (j + 1) < 1 := (GoodEvent_gridTime_le hst hi.2).trans_lt ht1
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact Complex.measurable_ofReal.comp (GoodEvent_measurable_stepZ s t K n j hE hu0 hu1
      (GoodEvent_gridStep_nonneg hst) _ a)
  · have : ZvecCut d E s t K n i = fun _ => 0 := by
      funext ω a; unfold ZvecCut
      have h0 : (if 1 ≤ i ∧ i ≤ K n then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

/-- `YvecCut i` is `filt d i`-strongly measurable for every `i`. -/
theorem stronglyMeasurable_YvecCut {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (i : ℕ) :
    StronglyMeasurable[filt d i] (YvecCut d E s t K n i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K n
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [YvecCut_succ (by omega)]
    have hu0 := GoodEvent_gridTime_nonneg (K := K) hs0 hst (j + 1)
    have hu1 : gridTime s t K n (j + 1) < 1 := (GoodEvent_gridTime_le hst hi.2).trans_lt ht1
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact GoodEvent_measurable_stepY s t K n j hE hu0 hu1 (GoodEvent_gridStep_nonneg hst) _ a
  · have : YvecCut d E s t K n i = fun _ => 0 := by
      funext ω a; unfold YvecCut
      have h0 : (if 1 ≤ i ∧ i ≤ K n then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

end Cuts

/-! ## The quadratic part: per-step inputs and the Chebyshev event at the stopping index -/

section Quadratic

open scoped Matrix.Norms.L2Operator

variable {d}

/-- The row sum of the product kernel at `ξ = |m(E)|² = 1`:
`Σ_a (𝒰_{u,w}(b₁,a₁) 𝒰_{u,w}(b₂,a₂)).re = ((1 - u)/(1 - w))²` (`ukerRowSum`, `normSqSpectralMOne`).
-/
private theorem GoodEvent_weight_sum {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
    {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w) (hw1 : w < 1) (b : Z2 L × Z2 L) :
    ∑ a : Z2 L × Z2 L, (ukerMat L ((Complex.normSq (spectralM E) : ℝ) : ℂ) u w b.1 a.1
        * ukerMat L ((Complex.normSq (spectralM E) : ℝ) : ℂ) u w b.2 a.2).re
      = ((1 - u) / (1 - w)) ^ 2 := by
  have hξ : Complex.normSq (spectralM E) = 1 := normSqSpectralMOne E hE.le
  have hw0 : 0 ≤ w := hu0.trans huw
  have hr : ∀ c : Z2 L, ∑ a : Z2 L, ukerMat L ((Complex.normSq (spectralM E) : ℝ) : ℂ) u w c a
      = (((1 - u * Complex.normSq (spectralM E)) / (1 - w * Complex.normSq (spectralM E)) : ℝ)
        : ℂ) :=
    fun c => ukerRowSum L hL (Complex.normSq (spectralM E)) u w (Complex.normSq_nonneg _) hw0
      (by rw [hξ]; linarith) c
  rw [← Complex.re_sum, Fintype.sum_prod_type]
  simp only
  rw [← Finset.sum_mul_sum, hr, hr, hξ]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **The per-step inputs of the Chebyshev tail for `YvecCut`**.  For a map `τ` with
`{j < τ} ∈ F_j`, a label
`b` and `j < K_n`, the stopped term `Y′ = 1_{j<τ} (𝒰_{u_{j+1}, v_n} YvecCut_{j+1})(b)` (at
`ξ = |m(E)|²`) has conditional mean zero (real and imaginary parts), is in `L²`, and
`∫ (Re Y′)² + ∫ (Im Y′)² ≤ 4 (R_j · 3 N η_{u_{j+1}}^{-4})² Δ² · 768 N⁸`,
`R_j = ((1 - u_{j+1})/(1 - v_n))²`. -/
theorem GoodEvent_Yterm_inputs {E : ℝ} (hE : |E| < 2) {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) {τ : PathΩ d → ℕ}
    (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) (b : Z2 (d.L n) × Z2 (d.L n)) {j : ℕ}
    (hj : j < K n) :
    (pathP d)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
        Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
          (YvecCut d E s v K n (j + 1) ω') b) ω).re | filt d j] =ᵐ[pathP d] 0
    ∧ (pathP d)[fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
        Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
          (YvecCut d E s v K n (j + 1) ω') b) ω).im | filt d j] =ᵐ[pathP d] 0
    ∧ MemLp (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
        Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
          (YvecCut d E s v K n (j + 1) ω') b) ω).re) 2 (pathP d)
    ∧ MemLp (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
        Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
          (YvecCut d E s v K n (j + 1) ω') b) ω).im) 2 (pathP d)
    ∧ ∫ ω, ({ω' | j < τ ω'}.indicator (fun ω' =>
          Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
            (YvecCut d E s v K n (j + 1) ω') b) ω).re ^ 2 ∂(pathP d)
        + ∫ ω, ({ω' | j < τ ω'}.indicator (fun ω' =>
          Uop (d.L n) ((Complex.normSq (spectralM E) : ℝ) : ℂ) (gridTime s v K n (j + 1)) (v n)
            (YvecCut d E s v K n (j + 1) ω') b) ω).im ^ 2 ∂(pathP d)
      ≤ 4 * (((1 - gridTime s v K n (j + 1)) / (1 - v n)) ^ 2
            * (3 * ((d.size n : ℕ) : ℝ) * (etaT E (gridTime s v K n (j + 1)))⁻¹ ^ 4)) ^ 2
          * (gridStep s v K n) ^ 2 * (768 * ((d.size n : ℕ) : ℝ) ^ 8) := by
  set u : ℝ := gridTime s v K n (j + 1) with hudef
  set S : Set (PathΩ d) := {ω' | j < τ ω'} with hSdef
  set ξ : ℂ := ((Complex.normSq (spectralM E) : ℝ) : ℂ) with hξdef
  have hS : MeasurableSet[filt d j] S := hτ j
  have hu0 : 0 ≤ u := GoodEvent_gridTime_nonneg hs0 hsv (j + 1)
  have huv : u ≤ v n := GoodEvent_gridTime_le hsv hj
  have hu1 : u < 1 := huv.trans_lt hv1
  have hΔ : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hΦ : ∀ a, HermTestFun d n (Expansion_loopObs d n E u a) :=
    fun a => (hermTestFun_loopPM d n E u hu0 hu1 hE a).1
  set U : Z2 (d.L n) × Z2 (d.L n) → Z2 (d.L n) × Z2 (d.L n) → ℝ :=
    fun b a => (ukerMat (d.L n) ξ u (v n) b.1 a.1 * ukerMat (d.L n) ξ u (v n) b.2 a.2).re
    with hUdef
  set Y : PathΩ d → ℂ := stepY d s v K n j (Expansion_loopObs d n E u) U b with hYdef
  -- `Y′ = 1_S Y` a.e.
  have hae := stepY_ukerMat_eq_Uker_ae d s v K n j hΦ E hE.le hu0 huv hv1
  have hf : (fun ω => S.indicator (fun ω' => Uop (d.L n) ξ u (v n)
      (YvecCut d E s v K n (j + 1) ω') b) ω) =ᵐ[pathP d] S.indicator Y := by
    filter_upwards [hae] with ω hω
    by_cases hωS : ω ∈ S
    · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS, YvecCut_succ hj]
      exact (hω b).symm
    · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
  obtain ⟨-, -, h3, h4, h5⟩ :=
    stepDecomp_loopPM d s v K n j E u hu0 hu1 hE u (v n) hu0 huv hv1 hΔ b
  -- `Y ∈ L²`
  have hYmeas : Measurable Y :=
    (GoodEvent_measurable_stepY s v K n j hE hu0 hu1 hΔ U b).mono ((filt d).le (j + 1)) le_rfl
  set c : ℝ := (∑ a : Z2 (d.L n) × Z2 (d.L n), U b a)
      * ((6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2) * gridStep s v K n) with hcdef
  set g : PathΩ d → ℝ := fun ω => c * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 2 with hgdef
  have hgmeas : Measurable g := by
    have hX : Measurable (fun ω : PathΩ d => Sizes.seqXmat d n (ω (j + 1))) :=
      ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).comp
        (measurable_pi_apply (j + 1))
    exact measurable_const.mul ((measurable_norm.comp hX).pow_const 2)
  have hg2 : MemLp g 2 (pathP d) := by
    rw [memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable]
    have : (fun ω => g ω ^ 2) = fun ω => c ^ 2 * ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 := by
      funext ω; rw [hgdef]; ring
    rw [this]
    exact (integrable_normPow4_incr d n j).const_mul _
  have hsum : MemLp (fun ω => g ω + (pathP d)[g | filt d j] ω) 2 (pathP d) :=
    hg2.add (hg2.condExp (by norm_num))
  have hm : MemLp Y 2 (pathP d) := by
    refine hsum.of_le hYmeas.aestronglyMeasurable ?_
    filter_upwards [h3] with ω hω
    exact hω.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)
  have hint : Integrable Y (pathP d) := hm.integrable (by norm_num)
  have h4' : (pathP d)[Y | filt d j] =ᵐ[pathP d] fun _ => (0 : ℂ) := h4
  have hmI : MemLp (S.indicator Y) 2 (pathP d) := hm.indicator ((filt d).le j S hS)
  -- mean zero
  have hmean : ∀ F : ℂ →L[ℝ] ℝ,
      (pathP d)[fun ω => F (S.indicator Y ω) | filt d j] =ᵐ[pathP d] 0 := by
    intro F
    have hfun : (fun ω => F (S.indicator Y ω)) = S.indicator (fun ω => F (Y ω)) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have hF : Integrable (fun ω => F (Y ω)) (pathP d) := F.integrable_comp hint
    have h1 := condExp_indicator (m := filt d j) hF hS
    have h2 : (pathP d)[fun ω => F (Y ω) | filt d j] =ᵐ[pathP d] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint F).symm
      have hc' : (pathP d)[fun ω => F (Y ω) | filt d j]
          =ᵐ[pathP d] fun ω => F ((pathP d)[Y | filt d j] ω) := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', h4'] with ω h1 h2
      rw [h1, h2]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (condExp_congr_ae (hf.fun_comp Complex.re)).trans ?_
    exact hmean Complex.reCLM
  · refine (condExp_congr_ae (hf.fun_comp Complex.im)).trans ?_
    exact hmean Complex.imCLM
  · exact hmI.re.ae_eq (hf.fun_comp Complex.re).symm
  · exact hmI.im.ae_eq (hf.fun_comp Complex.im).symm
  · have e1 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.re ^ 2))
    have e2 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.im ^ 2))
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2]
    have hre : Integrable (fun ω => (S.indicator Y ω).re ^ 2) (pathP d) := hmI.re.integrable_sq
    have him : Integrable (fun ω => (S.indicator Y ω).im ^ 2) (pathP d) := hmI.im.integrable_sq
    have hn2 : Integrable (fun ω => ‖Y ω‖ ^ 2) (pathP d) :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    rw [← integral_add hre him]
    have hrow : ∑ a : Z2 (d.L n) × Z2 (d.L n), U b a = ((1 - u) / (1 - v n)) ^ 2 :=
      GoodEvent_weight_sum (d.three_le_L n) hE hu0 huv hv1 b
    have hX4 := integral_normPow4_incr_le d n j
    calc ∫ ω, ((S.indicator Y ω).re ^ 2 + (S.indicator Y ω).im ^ 2) ∂(pathP d)
        ≤ ∫ ω, ‖Y ω‖ ^ 2 ∂(pathP d) := by
          refine integral_mono (hre.add him) hn2 fun ω => ?_
          have e : (S.indicator Y ω).re ^ 2 + (S.indicator Y ω).im ^ 2
              = ‖S.indicator Y ω‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          simp only
          rw [e]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2
      _ ≤ 4 * ((∑ a : Z2 (d.L n) × Z2 (d.L n), U b a)
              * (6 * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ 4 / 2)) ^ 2
            * (gridStep s v K n) ^ 2
            * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := h5
      _ = 4 * (((1 - u) / (1 - v n)) ^ 2 * (3 * ((d.size n : ℕ) : ℝ) * (etaT E u)⁻¹ ^ 4)) ^ 2
            * (gridStep s v K n) ^ 2
            * ∫ ω, ‖Sizes.seqXmat d n (ω (j + 1))‖ ^ 4 ∂(pathP d) := by
          rw [hrow]; ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hX4
          positivity


/-- **The Chebyshev event at the stopping index**.  For every `D₁ > 0`, on
the grid `K = gridK d D D₁` (`C_K = D₁ + 2D + 80`) and with `τ = gridTauFull`, eventually in `n`,
`P{∃ a, 𝒯_{u_τ,D}(|a.1 - a.2|_L) ≤ ‖(Σ_{j<τ} 𝒰_{u_{j+1},u_τ} Yvec_{j+1})(a)‖} ≤ N^{-D₁}`
(no union over targets).  Proof: `stopped_duhamel_cheb_tail` at `x = W^{-D}/4`, `ξ = |m(E_n)|²`,
target `v n = u_{K_n}`, with the per-step inputs `GoodEvent_Yterm_inputs` and
`e_j = 27648 c_κ^{-8} N²² Δ²` (`R_j ≤ N²`, `η_u⁻¹ ≤ N c_κ⁻¹`, `c_κ = √(κ(4-κ))/2 ≤ Im m(E_n)`,
`1 - v n ≥ N⁻¹` from `RangeCond`); then `P ≤ 442368 c_κ^{-8} N^{-D₁-D-56}`. -/
theorem cheb_grid_at_tau {E : ℕ → ℝ} {s v t : ℕ → ℝ} {κ τ' D : ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hvt : ∀ n, v n ≤ t n) (ht1 : ∀ n, t n < 1) (hτ' : 0 ≤ τ') (hrange : RangeCond d τ' t)
    (hsize : RBM.Ind.SizeTendsto d) (hD0 : 0 ≤ D) (δ ε : ℝ) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      pathP d {ω | ∃ a : Z2 (d.L n) × Z2 (d.L n),
        tailT (d.L n) (d.W n) (E n) D
            (gridTime s v (gridK d D D₁) n (gridTauFull d E s v (gridK d D D₁) δ D ε n ω))
            (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
          ‖(∑ j ∈ Finset.range (gridTauFull d E s v (gridK d D D₁) δ D ε n ω),
              Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
                (gridTime s v (gridK d D D₁) n (j + 1))
                (gridTime s v (gridK d D D₁) n (gridTauFull d E s v (gridK d D D₁) δ D ε n ω))
                (Yvec d (E n) s v (gridK d D D₁) n (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
  intro D₁ _
  -- the lower bound `c ≤ Im m(E n)`
  have hκ2 : κ ≤ 2 := by have := hE 0; linarith [abs_nonneg (E 0)]
  set c : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hcdef
  have hc0 : 0 < c := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    exact div_pos (Real.sqrt_pos.2 this) (by norm_num)
  have hcm : ∀ n, c ≤ (spectralM (E n)).im := by
    intro n
    rw [spectralM_im, hcdef]
    have h0 : 0 ≤ 2 - κ := le_trans (abs_nonneg _) (hE n)
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      rw [← sq_abs (E n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hE n) 2
    have h2 : κ * (4 - κ) ≤ 4 - E n ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h2) (by norm_num)
  set ci : ℝ := c⁻¹ with hcidef
  have hci0 : 0 < ci := inv_pos.2 hc0
  set Cc : ℝ := 442368 * ci ^ 8 with hCcdef
  have hbig : ∀ᶠ n : ℕ in atTop, max 1 Cc ≤ ((d.size n : ℕ) : ℝ) :=
    (show Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop from hsize).eventually_ge_atTop _
  unfold RangeCond at hrange
  filter_upwards [hrange, hbig] with n hrn hNn
  set K : ℕ → ℕ := gridK d D D₁ with hKdef
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hNn
  have hNC : Cc ≤ N := le_trans (le_max_right _ _) hNn
  have hN0 : 0 < N := by linarith
  have hEn : |E n| < 2 := by linarith [hE n]
  have hv1 : v n < 1 := (hvt n).trans_lt (ht1 n)
  -- `1 - v n ≥ N⁻¹`
  have h1v : N⁻¹ ≤ 1 - v n := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (-1 : ℝ) ≤ -1 + τ' by linarith)
    rw [Real.rpow_neg_one] at h
    linarith [hvt n]
  have hK0 : ∀ m, K m ≠ 0 := gridK_ne_zero D D₁
  have hvs : v n - s n ≤ 1 := by linarith [hs0 n, hv1]
  have hΔCK : gridStep s v K n ≤ N ^ (-CK D D₁) := step_gridK_le hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    have hKne : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 n)
    have : (K n : ℝ) * gridStep s v K n = v n - s n := by unfold gridStep; field_simp
    rw [this]; exact hvs
  have hτK : ∀ ω, gridTauFull d E s v K δ D ε n ω ≤ K n := fun ω =>
    gridTauFull_le E s v K δ D ε n ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < gridTauFull d E s v K δ D ε n ω} :=
    fun j => lt_gridTauFull_measurableSet hEn (hsv n) hv1 K δ D ε j
  have hY : ∀ i ≤ K n, StronglyMeasurable[filt d i] (YvecCut d (E n) s v K n i) :=
    fun i _ => stronglyMeasurable_YvecCut hEn (hs0 n) (hsv n) hv1 i
  have hu0 : 0 ≤ gridTime s v K n 0 := by rw [GoodEvent_gridTime_zero]; exact hs0 n
  have hu_succ : ∀ j, gridTime s v K n j ≤ gridTime s v K n (j + 1) := fun j =>
    GoodEvent_gridTime_mono (hsv n) (Nat.le_succ j)
  have hutK : gridTime s v K n (K n) = v n := gridTime_last s v K n (hK0 n)
  have hξ : ‖((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [normSqSpectralMOne (E n) hEn.le]; simp
  set e0 : ℝ := 27648 * ci ^ 8 * N ^ 22 * gridStep s v K n ^ 2 with he0
  -- the per-step constant
  have hstep : ∀ j < K n,
      4 * (((1 - gridTime s v K n (j + 1)) / (1 - v n)) ^ 2
            * (3 * N * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 4)) ^ 2
          * (gridStep s v K n) ^ 2 * (768 * N ^ 8) ≤ e0 := by
    intro j hj
    set u := gridTime s v K n (j + 1) with hudef
    have huv : u ≤ v n := GoodEvent_gridTime_le (hsv n) hj
    have hu0' : 0 ≤ u := GoodEvent_gridTime_nonneg (hs0 n) (hsv n) (j + 1)
    have h1v0 : 0 < 1 - v n := by linarith
    have hR0 : 0 ≤ (1 - u) / (1 - v n) := div_nonneg (by linarith) h1v0.le
    have hR : (1 - u) / (1 - v n) ≤ N := by
      rw [div_le_iff₀ h1v0]
      have h := mul_le_mul_of_nonneg_left h1v hN0.le
      rw [mul_inv_cancel₀ hN0.ne'] at h
      linarith
    have hη : c * N⁻¹ ≤ etaT (E n) u := by
      unfold etaT
      have h1 : N⁻¹ ≤ 1 - u := by linarith
      have h := mul_le_mul h1 (hcm n) hc0.le (by linarith)
      linarith [mul_comm (N⁻¹) c]
    have hη0 : 0 < c * N⁻¹ := by positivity
    have hηi : (etaT (E n) u)⁻¹ ≤ N * ci := by
      calc (etaT (E n) u)⁻¹ ≤ (c * N⁻¹)⁻¹ := inv_anti₀ hη0 hη
        _ = N * ci := by rw [mul_inv, inv_inv, hcidef]; ring
    have hηi0 : 0 ≤ (etaT (E n) u)⁻¹ := inv_nonneg.2 (hη0.le.trans hη)
    have hA : ((1 - u) / (1 - v n)) ^ 2 * (3 * N * (etaT (E n) u)⁻¹ ^ 4)
        ≤ 3 * N ^ 7 * ci ^ 4 := by
      have h1 : ((1 - u) / (1 - v n)) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hR0 hR 2
      have h2 : (etaT (E n) u)⁻¹ ^ 4 ≤ (N * ci) ^ 4 := pow_le_pow_left₀ hηi0 hηi 4
      calc ((1 - u) / (1 - v n)) ^ 2 * (3 * N * (etaT (E n) u)⁻¹ ^ 4)
          ≤ N ^ 2 * (3 * N * (N * ci) ^ 4) := by gcongr
        _ = 3 * N ^ 7 * ci ^ 4 := by ring
    have hA0 : 0 ≤ ((1 - u) / (1 - v n)) ^ 2 * (3 * N * (etaT (E n) u)⁻¹ ^ 4) := by positivity
    have hA2 := pow_le_pow_left₀ hA0 hA 2
    calc 4 * (((1 - u) / (1 - v n)) ^ 2 * (3 * N * (etaT (E n) u)⁻¹ ^ 4)) ^ 2
          * (gridStep s v K n) ^ 2 * (768 * N ^ 8)
        ≤ 4 * (3 * N ^ 7 * ci ^ 4) ^ 2 * (gridStep s v K n) ^ 2 * (768 * N ^ 8) := by
          have hN8 : 0 ≤ 768 * N ^ 8 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA2 (by norm_num)) (sq_nonneg _)) hN8
      _ = e0 := by rw [he0]; ring
  have hW0 : (0 : ℝ) < d.W n := by exact_mod_cast d.W_pos n
  set x : ℝ := ((d.W n : ℝ) ^ (-D)) / 4 with hxdef
  have hx0 : 0 < x := div_pos (Real.rpow_pos_of_pos hW0 _) (by norm_num)
  have hcheb := stopped_duhamel_cheb_tail (μ := pathP d) (ℱ := filt d) (d.L n) (d.three_le_L n)
    hξ (u := gridTime s v K n) (t := v n) hu0 hu_succ hutK hv1 hτK hτmeas hY (e := fun _ => e0)
    (fun b j hj => (GoodEvent_Yterm_inputs hEn (hs0 n) (hsv n) hv1 hτmeas b hj).1)
    (fun b j hj => (GoodEvent_Yterm_inputs hEn (hs0 n) (hsv n) hv1 hτmeas b hj).2.1)
    (fun b j hj => (GoodEvent_Yterm_inputs hEn (hs0 n) (hsv n) hv1 hτmeas b hj).2.2.1)
    (fun b j hj => (GoodEvent_Yterm_inputs hEn (hs0 n) (hsv n) hv1 hτmeas b hj).2.2.2.1)
    (fun b j hj => ((GoodEvent_Yterm_inputs hEn (hs0 n) (hsv n) hv1 hτmeas b hj).2.2.2.2).trans
      (hstep j hj))
    hx0
  -- the event inclusion
  set Sbad : Set (PathΩ d) := {ω | ∃ a, 4 * x ≤
      ‖(∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
        Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
          (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
          (YvecCut d (E n) s v K n (j + 1) ω)) a‖} with hSbad
  have hsub : {ω | ∃ a : Z2 (d.L n) × Z2 (d.L n),
        tailT (d.L n) (d.W n) (E n) D (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
          ‖(∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
              Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
                (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
                (Yvec d (E n) s v K n (j + 1) ω)) a‖} ⊆ Sbad := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    refine ⟨a, ?_⟩
    have hsum : (∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (YvecCut d (E n) s v K n (j + 1) ω))
        = ∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (Yvec d (E n) s v K n (j + 1) ω) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [YvecCut_succ (lt_of_lt_of_le (Finset.mem_range.1 hj) (hτK ω))]
    rw [hsum]
    have hT : (d.W n : ℝ) ^ (-D) ≤ tailT (d.L n) (d.W n) (E n) D
        (gridTime s v K n (gridTauFull d E s v K δ D ε n ω)) (zdist2 (d.L n) (a.1 - a.2) : ℝ) := by
      unfold tailT
      exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le)
    calc 4 * x = (d.W n : ℝ) ^ (-D) := by rw [hxdef]; ring
      _ ≤ _ := hT
      _ ≤ _ := ha
  -- the arithmetic
  have hWW : (d.W n : ℝ) * d.W n ≤ N := by
    have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
    have h : d.W n * d.W n ≤ d.size n := by
      unfold Sizes.size
      calc d.W n * d.W n ≤ (d.W n * d.L n) * (d.W n * d.L n) :=
            Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hL) (Nat.le_mul_of_pos_right _ hL)
        _ = (d.W n * d.L n) ^ 2 := by ring
    rw [hNdef]; exact_mod_cast h
  have hL4 : (d.L n : ℝ) ^ 4 ≤ N ^ 2 := by
    have hW : 1 ≤ d.W n := d.W_pos n
    have h : (d.L n) ^ 4 ≤ (d.size n) ^ 2 := by
      unfold Sizes.size
      calc (d.L n) ^ 4 ≤ (d.W n * d.L n) ^ 4 :=
            Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) 4
        _ = ((d.W n * d.L n) ^ 2) ^ 2 := by ring
    rw [hNdef]; exact_mod_cast h
  have hx2 : N ^ (-D) / 16 ≤ x ^ 2 := by
    have h1 : N ^ (-D) ≤ ((d.W n : ℝ) * d.W n) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hW0 hW0) hWW (by linarith)
    rw [Real.mul_rpow hW0.le hW0.le] at h1
    have e : x ^ 2 = (d.W n : ℝ) ^ (-D) * (d.W n : ℝ) ^ (-D) / 16 := by rw [hxdef]; ring
    rw [e]; linarith
  have hsplit : N ^ (-CK D D₁) = N ^ (-D₁) * N ^ (-D) * N ^ (-D) * (N ^ 80)⁻¹ := by
    rw [show -CK D D₁ = -D₁ + -D + -D + -((80 : ℕ) : ℝ) by unfold CK; push_cast; ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0,
      Real.rpow_neg hN0.le ((80 : ℕ) : ℝ), Real.rpow_natCast]
  have hP0 : 0 < N ^ (-D₁) := Real.rpow_pos_of_pos hN0 _
  have hQ0 : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hQ1 : N ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hN56 : 16 * (27648 * ci ^ 8) ≤ N ^ 56 := by
    have h : N ≤ N ^ 56 := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 56 := pow_le_pow_right₀ hN1 (by norm_num)
    have : Cc ≤ N ^ 56 := hNC.trans h
    rw [hCcdef] at this; linarith
  have hfinal : (d.L n : ℝ) ^ 4 * (∑ _j ∈ Finset.range (K n), e0) / x ^ 2 ≤ N ^ (-D₁) := by
    rw [div_le_iff₀ (pow_pos hx0 2), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hKe : (K n : ℝ) * e0 ≤ 27648 * ci ^ 8 * N ^ 22 * N ^ (-CK D D₁) := by
      have e : (K n : ℝ) * e0 = 27648 * ci ^ 8 * N ^ 22 * gridStep s v K n
          * ((K n : ℝ) * gridStep s v K n) := by rw [he0]; ring
      rw [e]
      have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
      have h0 : 0 ≤ 27648 * ci ^ 8 * N ^ 22 * gridStep s v K n := by positivity
      calc _ ≤ 27648 * ci ^ 8 * N ^ 22 * gridStep s v K n * 1 :=
            mul_le_mul_of_nonneg_left hKΔ h0
        _ = 27648 * ci ^ 8 * N ^ 22 * gridStep s v K n := mul_one _
        _ ≤ _ := mul_le_mul_of_nonneg_left hΔCK (by positivity)
    have hKe0 : 0 ≤ (K n : ℝ) * e0 := by
      have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
      rw [he0]; positivity
    have h56 : 0 < N ^ 56 := by positivity
    calc (d.L n : ℝ) ^ 4 * ((K n : ℝ) * e0)
        ≤ N ^ 2 * (27648 * ci ^ 8 * N ^ 22 * N ^ (-CK D D₁)) :=
          mul_le_mul hL4 hKe hKe0 (by positivity)
      _ = N ^ (-D₁) * N ^ (-D) * (27648 * ci ^ 8 * (N ^ 24 * (N ^ 80)⁻¹) * N ^ (-D)) := by
          rw [hsplit]; ring
      _ ≤ N ^ (-D₁) * N ^ (-D) * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have e : N ^ 24 * (N ^ 80)⁻¹ = (N ^ 56)⁻¹ := by
            rw [show N ^ 80 = N ^ 24 * N ^ 56 by ring, mul_inv, ← mul_assoc,
              mul_inv_cancel₀ (by positivity), one_mul]
          rw [e]
          calc 27648 * ci ^ 8 * (N ^ 56)⁻¹ * N ^ (-D)
              ≤ 27648 * ci ^ 8 * (N ^ 56)⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left hQ1 (by positivity)
            _ = 27648 * ci ^ 8 / N ^ 56 := by ring
            _ ≤ 1 / 16 := by rw [div_le_div_iff₀ h56 (by norm_num)]; linarith
      _ = N ^ (-D₁) * (N ^ (-D) / 16) := by ring
      _ ≤ N ^ (-D₁) * x ^ 2 := mul_le_mul_of_nonneg_left hx2 hP0.le
  calc (pathP d) _ ≤ (pathP d) Sbad := measure_mono hsub
    _ = ENNReal.ofReal ((pathP d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (N ^ (-D₁)) := ENNReal.ofReal_le_ofReal (hcheb.trans hfinal)

end Quadratic

end RBM.Path

end
