/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.BoundsA
import RBM2D.Universality.GUEPhase.DuhamelC
import RBM2D.Universality.GUEPhase.EntryGrid
import RBM2D.Universality.GUEPhase.HypB
import RBM2D.Green.FlucAvg
import RBM2D.Main.Endpoints

/-!
# The output of the §7.2 random layer on the grid: `gueGrid_pathBounds`, `d = 2`

Under the hypotheses of `gueGrid_pathBounds`, the GUE-phase grid path `gueH` satisfies
`GUEPathBounds` (`Grid.lean`): (7.28) at every grid time `k ≤ K n` for `1 ≤ m ≤ n₀` against the
primitive family `Kt`, and `‖G̃ − m‖_max ≺ (N η_u)^{-1/2}`, `N = d.size n = (W L)²`, on the size
scale.

Contents.
* `gueBds_h745E`, `gueBds_h746` (public): the inputs `h745`, `h746` of the size-scale
  bootstraps `eq727GEAt` (at `2 n₀`) and `eq728GAt` (`BootstrapAt.lean`) for the stopped,
  interpolated processes `gueLproc`, `gueDproc` (`Proc.lean`) with `δ = gueDelta d τU`,
  `K = gueGridK d n0`: on the intersection of the w.h.p. events at level `τ/2` (the step-`0`
  loops, the loop Duhamel remainder `gueGrid_loop_duhamel`, for `h745E` also the entry
  bound `gueGrid_entry_bound`), the deterministic facts of `HypB.lean` and the
  fixed-point step `HypB_fixed` bound `D_m` by `N^τ · rhs745G` resp. `N^τ · rhs746G`.
* `PathBounds_init_loops`, `PathBounds_init_local` (private): the step-`0` laws: `InitLK` and
  `InitLocal` of the loop estimate `MLConcl d E t₁` (per time, for `Sizes.seqP d` at `t₁`) are
  moved to `Pgue` at step `0` through the coordinate marginal (`gueH … 0 ω = seqHflow d n t₁ (ω 0)`,
  `(Pgue d).map (· 0) = seqP d`, `Measure.le_map_apply`), with `Kt n t₁ = Kcal` (`hKinit`) and
  `M_{t₁} = W² ℓ_{t₁}² η_{t₁} = N η_{t₁}` once `ℓ_{t₁} = L` (`hell`, `ellT_eq_L`); the union over
  `(σ, a)` (`≤ N^{k+1}` points) resp. `(i, j)` (`N²` points) is the per-time to uniform union
  bound `stochDomAt_of_perTimeDomAt`.
* `gueGrid_pathBounds` (public): the two bootstraps, the entry bound at `δ = gueDelta d τU`,
  `c₀ = τU/4`, the step-`0` local law, the truncation `gue_highProb_incr_le`, and the pathwise
  unfreezing `Bounds_path` on their intersection (`τ₁ = min(τ, τU)/16`), concluded by
  `pathBounds_of_forall_highProbAt`.

Conventions (`d = 2`): the loop estimate is `RBM.Ind.MLConcl d E t1`; `Admissible 𝔠 d` gives
`d.size → ∞` and the hypothesis of `gueGrid_entry_bound` (in `gueBds_h746` only `d.size → ∞` is
needed); the step-`0` transfer uses the coordinate marginal with `Measure.le_map_apply` (no
measurability of the failure set) and a per-time to uniform union bound with polynomially many
index points; loops are on `blockMat`; thresholds and failure rates are in `d.size n`; the
constants of the entry bound (`3`) and of the unfreezing (`1/32`, `2`) are those of `HypB.lean`
and `BoundsA.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ### The step-0 laws (private) -/

section PathBoundsInit

/-- The step-`0` marginal of the grid measure is the band law `seqP d`. -/
private theorem PathBounds_map_eval0 : (Pgue d).map (fun ω : PathΩ d => ω 0) = Sizes.seqP d := by
  unfold Pgue
  rw [Measure.infinitePi_map_eval]
  rfl

/-- A bad set at step `0` is bounded by its image under the coordinate marginal, with no
measurability (`Measure.le_map_apply`). -/
private theorem PathBounds_step0_le (B : Set (Sizes.SeqΩ d)) :
    Pgue d ((fun ω : PathΩ d => ω 0) ⁻¹' B) ≤ Sizes.seqP d B := by
  have h := Measure.le_map_apply (μ := Pgue d) (measurable_pi_apply (0 : ℕ)).aemeasurable B
  rwa [PathBounds_map_eval0] at h

/-- `H_0 = H^{band}_{t₁}(ω 0)` (the pointwise identity inside `map_gueH_zero`). -/
private theorem PathBounds_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ω : PathΩ d) :
    gueH d t1 t0 K n 0 ω = Sizes.seqHflow d n (t1 n) (ω 0) := by
  unfold gueH
  simp [Sizes.seqHflow_eq_smul]

/-- `‖(G - m)_{ij}‖` is the `llErrMat` of the (4.9) bridge. -/
private theorem PathBounds_llErr_eq {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    llErrMat L W E u M i j =
      ‖(green M (spectralZ E u) - spectralM E • (1 : Matrix (Idx L W) (Idx L W) ℂ)) i j‖ := by
  unfold llErrMat green
  by_cases h : i = j
  · subst h; simp [Matrix.sub_apply, Matrix.smul_apply]
  · simp [h, Matrix.sub_apply, Matrix.smul_apply]

/-- `M_{t₁} = N η_{t₁}` once `ℓ_{t₁} = L` (`hell`): `scaleM = gueScale` at `t₁`. -/
private theorem PathBounds_scale_eq {E t1 : ℕ → ℝ} {n : ℕ} (ht : t1 n < 1)
    (hell : (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1) :
    scaleM (d.L n) (d.W n) (E n) (t1 n) = gueScale d E n (t1 n) := by
  unfold scaleM gueScale
  rw [ellT_eq_L ht hell]
  simp only [Sizes.size]
  push_cast
  ring

/-- `#((σ, a)) = 2^k (L²)^k ≤ N^{k+1}` eventually. -/
private theorem PathBounds_card_loops (hsz : Tendsto (fun n => d.size n) atTop atTop) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((k + 1 : ℕ)) : ℝ) := by
  filter_upwards [hsz.eventually (eventually_ge_atTop (2 ^ k))] with n hn
  rw [Real.rpow_natCast]
  have h1 : Fintype.card ((Fin k → Bool) × (Fin k → Z2 (d.L n))) =
      2 ^ k * Fintype.card (Z2 (d.L n)) ^ k := by
    simp [Fintype.card_prod]
  have h2 := RBM.Green.flucAvg_card_Z2_le_size d n
  rw [h1]
  have h3 : 2 ^ k * Fintype.card (Z2 (d.L n)) ^ k ≤ d.size n * d.size n ^ k :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_left h2 k)
  calc (((2 ^ k * Fintype.card (Z2 (d.L n)) ^ k : ℕ)) : ℝ)
      ≤ ((d.size n * d.size n ^ k : ℕ) : ℝ) := by exact_mod_cast h3
    _ = ((d.size n : ℕ) : ℝ) ^ (k + 1) := by push_cast; ring

/-- `#(Idx × Idx) = N²`. -/
private theorem PathBounds_card_idx (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ ((2 : ℕ) : ℝ) := by
  rw [Real.rpow_natCast, Fintype.card_prod, RBM.Green.flucAvg_card_Idx_eq_size]
  push_cast
  ring_nf
  exact le_rfl


/-- **The loops at step `0`**: the step-`0` input `‖L_0 − K̃_{t₁}‖ ≺ (N η_{t₁})^{-k}` on `Pgue`,
from `InitLK` (of `MLConcl`) transferred through the coordinate marginal, with
`K̃_{t₁} = 𝒦_{t₁}` (`hKinit`) and `ℓ_{t₁} = L` (`hell`), `M_{t₁} = N η_{t₁}`.  The failure set is
handled through the coordinate marginal with `Measure.le_map_apply`; the union over `(σ, a)` is a
per-time to uniform union bound (`#(σ, a) ≤ N^{k+1}`). -/
private theorem PathBounds_init_loops {E t1 : ℕ → ℝ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (hsz : Tendsto (fun n => d.size n) atTop atTop)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hLK : RBM.Ind.InitLK d E t1) (k : ℕ) (hk : 1 ≤ k) :
    StochDomAt (Pgue d) d.size
      (fun n (x : (Fin k → Bool) × (Fin k → Z2 (d.L n))) ω =>
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω))
            (spectralZ (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖)
      (fun n _ _ => (gueScale d E n (t1 n))⁻¹ ^ k) := by
  have hpt : PerTimeDomAt (Pgue d) d.size
      (U := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n x ω => ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω))
            (spectralZ (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖)
      (fun n _ _ => (gueScale d E n (t1 n))⁻¹ ^ k) := by
    intro τ hτ D hD
    filter_upwards [hLK k hk τ hτ D hD, hell] with n hn hellN x
    have h1 := hn ((), x)
    refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le d _) h1)
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
    rw [PathBounds_gueH_zero, GoodEvent_gridTime_zero, hKinit] at hω
    rw [PathBounds_scale_eq d (lt_of_le_of_lt (ht10 n) (ht0 n)) hellN]
    exact hω
  exact stochDomAt_of_perTimeDomAt (Pgue d) d.size (C := ((k + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (PathBounds_card_loops d hsz k) hpt

/-- **The local law at step `0`**: `InitLocal` (of `MLConcl`) transferred to `Pgue` through the
coordinate marginal, with `ℓ_{t₁} = L` (`hell`); `llErr` is `llErrMat` (`PathBounds_llErr_eq`);
no measurability of the failure set is needed; the union over `(i, j)` has `N²` terms. -/
private theorem PathBounds_init_local {E t1 : ℕ → ℝ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (hLoc : RBM.Path.InitLocal d E t1) :
    StochDomAt (Pgue d) d.size
      (fun n (ij : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) ω =>
        ‖(green (gueH d t1 t0 K n 0 ω) (spectralZ (E n) (t1 n)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
            ij.1 ij.2‖)
      (fun n _ _ => (gueScale d E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) := by
  have hpt : PerTimeDomAt (Pgue d) d.size
      (U := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
      (fun n ij ω => ‖(green (gueH d t1 t0 K n 0 ω) (spectralZ (E n) (t1 n)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
            ij.1 ij.2‖)
      (fun n _ _ => (gueScale d E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) := by
    intro τ hτ D hD
    filter_upwards [hLoc τ hτ D hD, hell] with n hn hellN ij
    have h1 := hn ((), ij)
    refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le d _) h1)
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
    rw [PathBounds_gueH_zero] at hω
    rw [PathBounds_scale_eq d (lt_of_le_of_lt (ht10 n) (ht0 n)) hellN, PathBounds_llErr_eq]
    exact hω
  exact stochDomAt_of_perTimeDomAt (Pgue d) d.size (C := ((2 : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (Eventually.of_forall (PathBounds_card_idx d)) hpt

end PathBoundsInit

/-! ### (7.45)G and (7.46)G for the stopped, interpolated processes -/

section PathBoundsHyp

open RBM.Ind.PerTimeCalc

/-- **(7.45)G at even lengths `2 ≤ m ≤ 2n₀`** for the stopped, interpolated processes: the `h745`
of `eq727GEAt` (with `n₀' = 2 n₀`), over the whole interval `[t₁, t₀]`, on `Pgue d` and the size
scale.  The step-`0` inputs are `InitLK`, `InitLocal` of `MLConcl d E t1`; `Admissible 𝔠 d` gives
`d.size → ∞` and the hypothesis of `gueGrid_entry_bound`; constants and counts are on
`N = d.size n` (`HypB_*`). -/
theorem gueBds_h745E {𝔠 κ τU : ℝ} (h𝔠 : 0 < 𝔠) (hadm : RBM.Endpoints.Admissible 𝔠 d)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (_hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hB : RBM.Ind.MLConcl d E t1) :
    StochDomAt (Pgue d) d.size
      (fun n (p : TimeIcc t1 t0 n × {m : ℕ // m ∈ Set.Icc 2 (2 * n0) ∧ Even m}) ω =>
        gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n p.2.1 p.1 ω)
      (fun n p ω => rhs745G ((d.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n m t ω)
        (fun m t => gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω) p.2.1 p.1) := by
  classical
  have hsz : Tendsto (fun n => d.size n) atTop atTop := hadm.1
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hI := fun k (hk : 1 ≤ k) =>
    PathBounds_init_loops d t0 (gueGridK d n0) hsz ht10 ht0 hell Kt hKinit hB.1.1 k hk
  have hKtd := Hyp_Kt_detDom d hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell Kt hKinit hK
  have hD4 := gueGrid_entry_bound d h𝔠 hadm hκ n0 hE ht1 ht10 ht0 (δ := gueDelta d τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range d hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range d hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamel d hκ hτU n0 hsz hE ht1 ht10 ht0 hscale k h1 h2) hτ2)
  have hG3 := perTimeCalc_highProbAt_of_stochDomAt hD4 hτ2
  filter_upwards [(perTimeCalc_highProbAt_inter hsz (perTimeCalc_highProbAt_inter hsz hG1 hG2) hG3)
      D hD, hKtd (τ / 2) hτ2, hKtd (τU / 2) (by positivity), hell, hscale, h730,
    HypB_ev_grid d hsz n0, HypB_ev_delta d hκ hτU hsz hE,
    hsz.eventually (eventually_le_rpow (2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2),
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hellN hscaleN h730N hgridN hδN hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨m, ⟨hm2, hmn⟩, heven⟩⟩, hp⟩ hω
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨l, hl⟩ := heven
  have hnl : m = 2 * l := by omega
  subst hnl
  have hl1 : 1 ≤ l := by omega
  refine absurd hp (not_lt.2 ?_)
  have hω1' := hω1 (2 * l) (by omega) hmn
  have hω2' := hω2 (2 * l) (by omega) hmn
  simp only [Set.mem_ofPred_eq] at hω1' hω2' hω3
  have hN1R : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact HypB_fixed d hτ n0 τU Kt hK n (2 * l) ω
    (fun u => gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n 2 u ω *
      gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * l) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaT (E n) u)⁻¹ ^ 2) *
      gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * l) u ω)
    (Ce := 4 * ((2 * l : ℕ) : ℝ) * N ^ (τ / 2) * N)
    (hEb n) (ht1 n) (ht10 n) (ht0 n) (by omega) hmn
    (HypB_step_le d n0 n (hEb n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypB_Kt_le_one d hτU n0 n Kt (hEb n) (ht0 n)
      (fun p => hKt1N p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hl' : (1 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * l)
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have : ((2 * l : ℕ) : ℝ) ≤ ((2 * l : ℕ) : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right this (mul_nonneg hc0 hS0)
      nlinarith)
    (fun u _ => mul_nonneg (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    ((gueLproc_continuousOn _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((HypB_sqrt_cont d n (hEb n) (ht0 n)).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [HypB_Lproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * l) j ω (ht10 n) hj]
      exact HypB_q_745 ((gueH_isHermitian d t1 t0 (gueGridK d n0) n j ω).submatrix _) _
        (by positivity) hl1)
    (fun j hj x => by
      rw [HypB_Lproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) n 2 j ω (ht10 n) hj,
        HypB_Lproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * l) j ω (ht10 n) hj]
      exact HypB_eG_745 d (gueGridK d n0) n j ω hc1 hl1
        (fun q => HypB_entry_le d hκ n0 hE ht10 ht0 n hellN hδN ω (by linarith)
          (fun k i j' => hω3 (k, (i, j'))) hj q) x)
    ht

/-- **(7.46)G at lengths `1 ≤ m ≤ n₀`** for the stopped, interpolated processes: the `h746` of
`eq728GAt`, over the whole interval `[t₁, t₀]`.  Only `d.size → ∞` is needed (`hsz`), not the
entry bound. -/
theorem gueBds_h746 {κ τU : ℝ} (hsz : Tendsto (fun n => d.size n) atTop atTop)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hB : RBM.Ind.MLConcl d E t1) :
    StochDomAt (Pgue d) d.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n p.2 p.1 ω)
      (fun n p ω => rhs746G ((d.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n m t ω)
        (fun m t => gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω) p.2 p.1) := by
  classical
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hI := fun k (hk : 1 ≤ k) =>
    PathBounds_init_loops d t0 (gueGridK d n0) hsz ht10 ht0 hell Kt hKinit hB.1.1 k hk
  have hKtd := Hyp_Kt_detDom d hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell Kt hKinit hK
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range d hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range d hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamel d hκ hτU n0 hsz hE ht1 ht10 ht0 hscale k h1 h2) hτ2)
  filter_upwards [(perTimeCalc_highProbAt_inter hsz hG1 hG2) D hD, hKtd (τ / 2) hτ2,
    hKtd (τU / 2) (by positivity), hscale, h730, HypB_ev_grid d hsz n0,
    hsz.eventually (eventually_le_rpow (2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2),
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hscaleN h730N hgridN hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨m, hmem⟩⟩, hp⟩ hω
  have hm1 : 1 ≤ m := hmem.1
  have hmn : m ≤ n0 := hmem.2
  obtain ⟨hω1, hω2⟩ := hω
  refine absurd hp (not_lt.2 ?_)
  have hm' : m ≤ 2 * n0 := by omega
  have hω1' := hω1 m hm1 hm'
  have hω2' := hω2 m hm1 hm'
  have hN1R : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact HypB_fixed d hτ n0 τU Kt hK n m ω
    (fun u => gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n 1 u ω *
      gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (m + 1) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaT (E n) u)⁻¹ ^ 2) *
      Real.sqrt (gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * m) u ω))
    (Ce := (m : ℝ) * N)
    (hEb n) (ht1 n) (ht10 n) (ht0 n) hm1 hm'
    (HypB_step_le d n0 n (hEb n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypB_Kt_le_one d hτU n0 n Kt (hEb n) (ht0 n)
      (fun p => hKt1N p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hn1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have h1 : (m : ℝ) ≤ 4 * (m : ℝ) ^ 2 * N ^ (τ / 2) := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hS0)
    (fun u _ => mul_nonneg (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    ((gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((HypB_sqrt_cont d n (hEb n) (ht0 n)).mul
      (Real.continuous_sqrt.comp_continuousOn (gueLproc_continuousOn _ _ _ _ _ _ _ _ _)))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [HypB_Lproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (2 * m) j ω (ht10 n) hj,
        ← Real.sqrt_mul (by positivity)])
    (fun j hj x => by
      rw [HypB_Dproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n 1 j ω (ht10 n) hj,
        HypB_Lproc_grid d E t1 t0 (gueGridK d n0) (gueDelta d τU) n (m + 1) j ω (ht10 n) hj]
      exact HypB_eG_746 d (gueGridK d n0) n0 (by omega) Kt hKinit hK n j m
        (Hyp_time_mem (ht10 n) (gueGridK_ne_zero d n0 n)
          ((le_of_lt hj).trans (firstHit_le _ _ _ ω))) ω x)
    ht

end PathBoundsHyp

/-! ### The main statement -/

section PathBoundsMain

open RBM.Ind.PerTimeCalc

/-- **The output of the §7.2 random layer on the grid**: under the hypotheses of the theorem,
the GUE-phase grid path `gueH` satisfies `GUEPathBounds`: (7.28) at every grid time `k ≤ K n` for
`1 ≤ m ≤ n₀` against the primitive family `Kt`, and `‖G̃ − m‖_max ≺ (N η_u)^{-1/2}`.

Proof: the two bootstraps `eq727GEAt` (at `2 n₀`, with the processes of
`Proc.lean`, `gueBds_h745E`) and `eq728GAt` (`gueBds_h746`); the other random inputs (the entry
bound `gueGrid_entry_bound` at `δ = gueDelta d τU`, `c₀ = τU/4`, the step-`0` local law, the
increment truncation `gue_highProb_incr_le`); the pathwise unfreezing `Bounds_path` on their
intersection (`τ₁ = min(τ, τU)/16`); `pathBounds_of_forall_highProbAt`.

Here `MLConcl d E t1` (`RBM.Ind.MLConcl`) is the loop estimate: `InitLK` gives the step-`0` loops,
`InitLocal` the step-`0` local law; `Admissible 𝔠 d` gives `d.size → ∞` and the hypothesis of the
entry bound; the size scale `N = d.size n = (W L)²` is used throughout;
`hsmallN : N^{2τ₁ − τU/2} ≤ 1/32`, `h4N : 2 ≤ N^{τ − τ₁}` as in `Bounds_path`. -/
theorem gueGrid_pathBounds {𝔠 κ τU : ℝ} (h𝔠 : 0 < 𝔠) (hadm : RBM.Endpoints.Admissible 𝔠 d)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hB : RBM.Ind.MLConcl d E t1) :
    GUEPathBounds d E t1 t0 (gueGridK d n0) n0 Kt := by
  classical
  have hsz : Tendsto (fun n => d.size n) atTop atTop := hadm.1
  /- Deterministic facts on `η = etaT (E n)` (the side conditions of the bootstraps). -/
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hmim : ∀ n, 0 < (spectralM (E n)).im := fun n => spectralM_im_pos (hEb n)
  have hη : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < etaT (E n) t := fun n t ht =>
    mul_pos (by linarith [ht.2, ht0 n]) (hmim n)
  have hanti : ∀ n, ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      etaT (E n) t ≤ etaT (E n) u := fun n u _ t _ hut => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (hmim n).le
  have hηc : ∀ n, ContinuousOn (etaT (E n)) (Set.Icc (t1 n) (t0 n)) := fun n => by
    unfold etaT
    exact ((continuous_const.sub continuous_id).mul continuous_const).continuousOn
  have hNpos : ∀ n, (0 : ℝ) < ((d.size n : ℕ) : ℝ) := fun n => by
    have h1 : 0 < d.size n := by
      unfold Sizes.size
      have hW := d.W_pos n
      have hL := d.three_le_L n
      positivity
    exact_mod_cast h1
  have ht0mem : ∀ n, t0 n ∈ Set.Icc (t1 n) (t0 n) := fun n => ⟨ht10 n, le_rfl⟩
  have h730' : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      t - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t := by
    filter_upwards [h730] with n hN t ht
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    calc t - t1 n ≤ t0 n - t1 n := by linarith [ht.2]
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n) := hN
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hscale' : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((d.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := by
    filter_upwards [hscale] with n hN t ht
    refine le_trans ?_ hN
    unfold gueScale
    have h0 := hη n (t0 n) (ht0mem n)
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    exact inv_anti₀ (mul_pos (hNpos n) h0) (mul_le_mul_of_nonneg_left h1 (hNpos n).le)
  /- The bootstraps: `eq727GEAt` at `2 n₀`, then `eq728GAt`. -/
  have h727 := eq727GEAt (Pgue d) d.size hsz (n0 := 2 * n0) (even_two_mul n0)
    (fun n => ((d.size n : ℕ) : ℝ)) (fun n => etaT (E n)) t1 t0
    (fun n m t ω => gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n m t ω)
    (fun n m t ω => gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω)
    (fun n m t => gueKproc d t1 t0 (gueGridK d n0) Kt n m t)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n m t ω => gueLproc_nonneg d E t1 t0 _ _ n m t ω)
    (fun n m t ω => gueDproc_nonneg d E t1 t0 _ _ Kt n m t ω)
    (fun n ω m _ t _ => gueLproc_le d E t1 t0 _ _ Kt n m t ω)
    (fun n ω m _ t _ => gueDproc_le d E t1 t0 _ _ Kt n m t ω)
    (fun n ω l hl _ t _ => gueLproc_odd d E t1 t0 _ _ n l hl t ω)
    (fun ε hε => (gueKproc_detDom d hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hscale hell Kt hKinit hK
      ε hε).mono fun n hn u => hn u.1 u.2)
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ m _ _ => gueLproc_continuousOn d E t1 t0 _ _ n m ω))
    (gueBds_h745E d h𝔠 hadm hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB)
  have h728 := eq728GAt (Pgue d) d.size hsz (n0 := n0)
    (fun n => ((d.size n : ℕ) : ℝ)) (fun n => etaT (E n)) t1 t0
    (fun n m t ω => gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n m t ω)
    (fun n m t ω => gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m t ω)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n m t ω => gueLproc_nonneg d E t1 t0 _ _ n m t ω)
    (fun n m t ω => gueDproc_nonneg d E t1 t0 _ _ Kt n m t ω) h727
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ m _ => gueDproc_continuousOn d E t1 t0 _ _ Kt n m ω))
    (gueBds_h746 d hsz hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB)
  /- The other random inputs: D4a with `δ = N^{-τU/4}`, the step-`0` local law, truncation. -/
  have hD4 := gueGrid_entry_bound d h𝔠 hadm hκ n0 hE ht1 ht10 ht0 (δ := gueDelta d τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  have hinit := PathBounds_init_local d t0 (gueGridK d n0) ht10 ht0 hell hB.1.2.2
  /- Unfreezing and conclusion on the intersection of the good events. -/
  have hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue d) d.size
      (fun n => {ω : PathΩ d | BoundsACheck.Concl d E t1 t0 n0 Kt τ n ω}) := by
    intro τ hτ
    set τ₁ : ℝ := min τ τU / 16 with hτ₁
    have hτ₁0 : 0 < τ₁ := by have := lt_min hτ hτU; positivity
    have hτ₁τ : τ₁ < τ := by have := min_le_left τ τU; have := lt_min hτ hτU; linarith
    have hneg : 2 * τ₁ - τU / 2 < 0 := by have := min_le_right τ τU; linarith
    have hev := perTimeCalc_highProbAt_inter hsz
      (perTimeCalc_highProbAt_inter hsz
        (perTimeCalc_highProbAt_inter hsz
          (perTimeCalc_highProbAt_inter hsz
            (BoundsACheck.highProbAt_hA d E t1 t0 n0 τU hτ₁0 h727)
            (BoundsACheck.highProbAt_hB d E t1 t0 n0 τU hτ₁0 Kt h728))
          (BoundsACheck.highProbAt_HC d E t1 t0 n0 τU hτ₁0 hD4))
        (BoundsACheck.highProbAt_hD d E t1 t0 n0 hτ₁0 hinit))
      (BoundsACheck.highProbAt_hF d n0 hsz)
    refine perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hscale', hell,
      hsz.eventually (eventually_rpow_le_of_neg hneg (by norm_num : (0 : ℝ) < 1 / 32)),
      hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ₁τ))]
      with n hscN hellN hsmallN h4N
    rintro ω ⟨⟨⟨⟨hA, hBω⟩, hC⟩, hD⟩, hFω⟩
    exact Bounds_path d n0 hn0 Kt n hτU (hEb n) (ht1 n) (ht10 n) (ht0 n) hτ₁0 hτ₁τ hscN hellN
      hsmallN h4N ω hA hBω hC hD hFω
  exact BoundsACheck.pathBounds_of_forall_highProbAt d E t1 t0 n0 Kt hmain

end PathBoundsMain

end RBM.Univ.GUEPhase

end
