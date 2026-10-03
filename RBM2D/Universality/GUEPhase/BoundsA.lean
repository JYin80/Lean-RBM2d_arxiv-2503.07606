/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Proc
import RBM2D.Universality.GUEPhase.BootstrapAt
import RBM2D.Universality.GUEPhase.Markov
import RBM2D.Path.GoodEvent
import RBM2D.Evolution.MLExpVocab

/-!
# The unfreezing of the §7.2 random layer, pathwise at one `n` and one `ω`, `d = 2`

`Bounds_path` is the pathwise unfreezing: on the intersection of the pathwise forms of the
high-probability events (the two bootstrap outputs `eq727GEAt`, `eq728GAt` for the stopped
processes `gueLproc`, `gueDproc`, the entry bound at `δ = gueDelta d τU`, the step-`0` local law,
the increment truncation `gue_highProb_incr_le`), an induction over the grid shows that the
a-priori threshold `gueDelta d τU` is never reached, so the freezing index `gueStop` never acts,
and the bootstrap outputs give (7.28) and the local law at every grid time.  Its conclusion is the
two fields of `GUEPathBounds` (`Grid.lean`) unfolded at `n`, `ω` and the threshold `(d.size n)^τ`,
so that `GUEPathBounds` follows with `stochDomAt_of_forall_highProbAt`
(`BoundsACheck.pathBounds_of_forall_highProbAt`).

Conventions.  Thresholds are `((d.size n : ℕ) : ℝ)^τ` with `N = d.size n = (W L)²`; the scale is
`gueScale d E n t`; the bound `W⁻¹ ≤ (S η_u)⁻¹` reads `(W²)⁻¹ ≤ (N η_u)⁻¹` (from `hellN`:
`L² η_u ≤ L²(1 − t₁) ≤ 1`).  The entry-bound hypothesis is `BoundsACheck.HC` (control
`gueLmax … 2 + (W²)⁻¹`, coefficients `1, 1`); the constants of the unfreezing induction are
`x² ≤ 2 p² Λ`, `hsmallN : N^{2τ₁ − τU/2} ≤ 1/32` and `h4N : 2 ≤ N^{τ − τ₁}`.

Helper lemmas are `private` and carry the prefix `Bounds_`.  The namespace `BoundsACheck` at the
end holds the entry-bound hypothesis `HC`, the statements `highProbAt_HC`, `highProbAt_hA`,
`highProbAt_hB`, `highProbAt_hD`, `highProbAt_hF` (each of the five pathwise hypotheses is the
event of a high-probability statement) and `pathBounds_of_forall_highProbAt` (the conclusion of
`Bounds_path`, w.h.p., gives `GUEPathBounds`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ### Elementary real-variable helpers (private) -/

section BoundsHelpers

/-- Before `firstHit` has reached `k`, i.e. if no index `i ≤ k ≤ K` hits the threshold, then
`k ≤ firstHit`. -/
private theorem Bounds_le_firstHit {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (ω : Ω')
    {k : ℕ} (hk : k ≤ K) (h : ∀ i ≤ k, J i ω < θ) : k ≤ firstHit J θ K ω := by
  by_contra hlt
  push Not at hlt
  have hlt' : firstHit J θ K ω < K := lt_of_lt_of_le hlt hk
  have hmem : J (firstHit J θ K ω) ω ∈ Set.Ici θ :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt (u := J) (s := Set.Ici θ) (n := 0) hlt'
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-- The unfreezing induction, in abstract form. -/
private theorem Bounds_unfreeze {K : ℕ} (dev : ℕ → ℝ) (σ : ℕ) {δ : ℝ}
    (hσ : ∀ k ≤ K, (∀ i ≤ k, dev i < δ) → k ≤ σ)
    (h0 : dev 0 < δ)
    (hstep : ∀ j < K, j ≤ σ → dev j < δ → dev j ≤ δ / 4)
    (hjump : ∀ j < K, dev (j + 1) ≤ dev j + δ / 2) (hδ : 0 < δ) :
    ∀ k ≤ K, ∀ i ≤ k, dev i < δ := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      exact h0
  | succ k ih =>
      intro hk i hi
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact ih' i (by omega)
      · have hi' : i = k + 1 := by omega
        subst hi'
        have hkσ := hσ k (by omega) ih'
        have h1 := hstep k (by omega) hkσ (ih' k le_rfl)
        have h2 := hjump k (by omega)
        linarith

/-- The D4a arithmetic of `HC` (coefficients `1, 1`): `x² ≤ p (L + w)`, `L ≤ p Λ`, `w ≤ Λ`,
`Λ ≤ q` give `x² ≤ 2 p² Λ ≤ 2 p² q`. -/
private theorem Bounds_sq_le {x p L Λ w q : ℝ} (hp1 : 1 ≤ p) (hL : L ≤ p * Λ) (hw : w ≤ Λ)
    (hΛq : Λ ≤ q) (hΛ0 : 0 ≤ Λ) (hx2 : x ^ 2 ≤ p * (L + w)) :
    x ^ 2 ≤ 2 * p ^ 2 * Λ ∧ 2 * p ^ 2 * Λ ≤ 2 * p ^ 2 * q := by
  have hp0 : 0 ≤ p := by linarith
  have hΛp : Λ ≤ p * Λ := le_mul_of_one_le_left hΛ0 hp1
  have h1 : L + w ≤ 2 * (p * Λ) := by linarith
  refine ⟨?_, ?_⟩
  · calc x ^ 2 ≤ p * (L + w) := hx2
      _ ≤ p * (2 * (p * Λ)) := mul_le_mul_of_nonneg_left h1 hp0
      _ = 2 * p ^ 2 * Λ := by ring
  · have : 0 ≤ 2 * p ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hΛq this

/-- The one-step jump of `‖G - m‖_max` is at most `δ/2`. -/
private theorem Bounds_jump {N : ℕ} (hN : 1 ≤ N) {S e Δ Sg δ : ℝ} (hS1 : 1 ≤ S)
    (hSN : S ≤ N) (he : 0 ≤ e) (heS : e ≤ S) (hΔ0 : 0 ≤ Δ) (hΔ : Δ * ((N : ℝ) + 1) ^ 64 ≤ 1)
    (hSg0 : 0 ≤ Sg) (hSg : Sg ≤ S ^ 2 * N) (hδ : 1 / (N : ℝ) ≤ δ) :
    e ^ 2 * (Real.sqrt (Δ / S) * Sg + Δ) ≤ δ / 2 := by
  set X : ℝ := (N : ℝ) + 1 with hX
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hX2 : 2 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hNX : (N : ℝ) ≤ X := by rw [hX]; linarith
  set r : ℝ := Real.sqrt (Δ / S) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hX32 : 1 ≤ X ^ 32 := one_le_pow₀ hX1
  have hX64 : X ^ 64 = X ^ 32 * X ^ 32 := by rw [← pow_add]
  -- `r X^32 ≤ 1`
  have hrX : r * X ^ 32 ≤ 1 := by
    have hDS : Δ / S ≤ Δ := div_le_self hΔ0 hS1
    have hsq : (r * X ^ 32) ^ 2 ≤ 1 := by
      rw [mul_pow, hr, Real.sq_sqrt (div_nonneg hΔ0 (by linarith)), ← pow_mul]
      calc Δ / S * X ^ (32 * 2) ≤ Δ * X ^ (32 * 2) :=
            mul_le_mul_of_nonneg_right hDS (by positivity)
        _ ≤ 1 := by simpa using hΔ
    have h0 : 0 ≤ r * X ^ 32 := by positivity
    exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 hsq
  have hΔX : Δ * X ^ 32 ≤ 1 := by
    have : Δ * X ^ 32 ≤ Δ * X ^ 64 := by
      rw [hX64]
      have : X ^ 32 ≤ X ^ 32 * X ^ 32 := le_mul_of_one_le_right (by positivity) hX32
      exact mul_le_mul_of_nonneg_left this hΔ0
    linarith
  have he2 : e ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ he (by linarith) 2
  have hSgX : Sg ≤ X ^ 3 := by
    have hS2 : S ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc Sg ≤ S ^ 2 * N := hSg
      _ ≤ X ^ 2 * X := mul_le_mul hS2 hNX (by linarith) (by positivity)
      _ = X ^ 3 := by ring
  have hinner : r * Sg + Δ ≤ X ^ 3 * (r + Δ) := by
    have h1 : r * Sg ≤ r * X ^ 3 := mul_le_mul_of_nonneg_left hSgX hr0
    have h2 : Δ ≤ X ^ 3 * Δ := le_mul_of_one_le_left hΔ0 (one_le_pow₀ hX1)
    calc r * Sg + Δ ≤ r * X ^ 3 + X ^ 3 * Δ := add_le_add h1 h2
      _ = X ^ 3 * (r + Δ) := by ring
  have hsum : (r + Δ) * X ^ 32 ≤ 2 := by rw [add_mul]; linarith
  have hmain : e ^ 2 * (r * Sg + Δ) * X ^ 32 ≤ 2 * X ^ 5 := by
    have h0 : 0 ≤ r * Sg + Δ := by positivity
    calc e ^ 2 * (r * Sg + Δ) * X ^ 32 ≤ X ^ 2 * (X ^ 3 * (r + Δ)) * X ^ 32 := by
          gcongr
      _ = X ^ 5 * ((r + Δ) * X ^ 32) := by ring
      _ ≤ X ^ 5 * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * X ^ 5 := by ring
  -- `4 N X^5 ≤ X^32`
  have hbig : 4 * (N : ℝ) * X ^ 5 ≤ X ^ 32 := by
    have h26 : (2 : ℝ) ^ 26 ≤ X ^ 26 := pow_le_pow_left₀ (by norm_num) hX2 26
    have h4 : (4 : ℝ) ≤ X ^ 26 := le_trans (by norm_num) h26
    calc 4 * (N : ℝ) * X ^ 5 ≤ X ^ 26 * X * X ^ 5 := by
          have : 0 ≤ X ^ 5 := by positivity
          have : 4 * (N : ℝ) ≤ X ^ 26 * X := mul_le_mul h4 hNX (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = X ^ 32 := by ring
  have hNpos : (0 : ℝ) < N := by linarith
  have hX32pos : 0 < X ^ 32 := by positivity
  have hfin : e ^ 2 * (r * Sg + Δ) ≤ 1 / (N : ℝ) / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h1 : e ^ 2 * (r * Sg + Δ) * X ^ 32 * (N * 2) ≤ 2 * X ^ 5 * (N * 2) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    have h2 : 2 * X ^ 5 * (N * 2) ≤ X ^ 32 := by
      calc 2 * X ^ 5 * (N * 2) = 4 * (N : ℝ) * X ^ 5 := by ring
        _ ≤ X ^ 32 := hbig
    have h3 : e ^ 2 * (r * Sg + Δ) * (N * 2) * X ^ 32 ≤ 1 * X ^ 32 := by
      calc e ^ 2 * (r * Sg + Δ) * (N * 2) * X ^ 32
          = e ^ 2 * (r * Sg + Δ) * X ^ 32 * (N * 2) := by ring
        _ ≤ 2 * X ^ 5 * (N * 2) := h1
        _ ≤ X ^ 32 := h2
        _ = 1 * X ^ 32 := by ring
    exact le_of_mul_le_mul_right h3 hX32pos
  linarith

/-- The exponent bookkeeping of the induction steps: `2 p² q ≤ (δ/4)²` for `p = N^{τ₁}`,
`q = N^{-τU}`,
`δ = N^{-τU/4}`, once `N^{2τ₁ - τU/2} ≤ 1/32`. -/
private theorem Bounds_rpow_key {N τ₁ τU : ℝ} (hN0 : 0 < N)
    (hsmall : N ^ (2 * τ₁ - τU / 2) ≤ 1 / 32) :
    2 * (N ^ τ₁) ^ 2 * N ^ (-τU) ≤ (N ^ (-(τU / 4)) / 4) ^ 2 := by
  have e1 : (N ^ τ₁) ^ 2 = N ^ (2 * τ₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have e2 : (N ^ (-(τU / 4))) ^ 2 = N ^ (-(τU / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have e3 : N ^ (2 * τ₁) * N ^ (-τU) = N ^ (2 * τ₁ - τU / 2) * N ^ (-(τU / 2)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1; ring
  have hδ2 : 0 ≤ N ^ (-(τU / 2)) := Real.rpow_nonneg hN0.le _
  calc 2 * (N ^ τ₁) ^ 2 * N ^ (-τU)
      = 2 * (N ^ (2 * τ₁ - τU / 2) * N ^ (-(τU / 2))) := by
        rw [e1, mul_assoc, e3]
    _ ≤ 2 * (1 / 32 * N ^ (-(τU / 2))) := by gcongr
    _ = (N ^ (-(τU / 4)) / 4) ^ 2 := by rw [div_pow, e2]; ring

/-- `x ≤ p √Λ`, `Λ ≤ q`, `2 p² q ≤ (δ/4)²` give `x ≤ δ/4`. -/
private theorem Bounds_le_of_sqrt {x p Λ q δ : ℝ} (hx : 0 ≤ x) (hΛ0 : 0 ≤ Λ)
    (hΛq : Λ ≤ q) (hδ : 0 ≤ δ) (hkey : 2 * p ^ 2 * q ≤ (δ / 4) ^ 2)
    (h : x ≤ p * Real.sqrt Λ) : x ≤ δ / 4 := by
  have h2 : x ^ 2 ≤ p ^ 2 * Λ := by
    have := pow_le_pow_left₀ hx h 2
    rwa [mul_pow, Real.sq_sqrt hΛ0] at this
  have hp2 : 0 ≤ p ^ 2 := by positivity
  have hq0 : 0 ≤ q := hΛ0.trans hΛq
  have h3 : x ^ 2 ≤ (δ / 4) ^ 2 := by
    have : p ^ 2 * Λ ≤ 2 * p ^ 2 * q := by
      calc p ^ 2 * Λ ≤ p ^ 2 * q := mul_le_mul_of_nonneg_left hΛq hp2
        _ ≤ 2 * p ^ 2 * q := by nlinarith [mul_nonneg hp2 hq0]
    linarith
  exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 h3

/-- `x² ≤ 2 p² q ≤ (δ/4)²` gives `x ≤ δ/4`. -/
private theorem Bounds_le_of_sq {x y δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) (h1 : x ^ 2 ≤ y)
    (h2 : y ≤ (δ / 4) ^ 2) : x ≤ δ / 4 :=
  (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 (h1.trans h2)

/-- `x² ≤ 2 p² Λ` and `2 p ≤ P` give `x ≤ P √Λ`. -/
private theorem Bounds_final {x p P Λ : ℝ} (hx : 0 ≤ x) (hΛ : 0 ≤ Λ) (hp : 0 ≤ p)
    (hP : 2 * p ≤ P) (h : x ^ 2 ≤ 2 * p ^ 2 * Λ) : x ≤ P * Real.sqrt Λ := by
  have hP0 : 0 ≤ P := by linarith
  have hy : 0 ≤ P * Real.sqrt Λ := mul_nonneg hP0 (Real.sqrt_nonneg _)
  refine (pow_le_pow_iff_left₀ hx hy two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hΛ]
  have h4 : 2 * p ^ 2 ≤ P ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hP) (by linarith : 0 ≤ P + 2 * p), sq_nonneg p]
  calc x ^ 2 ≤ 2 * p ^ 2 * Λ := h
    _ ≤ P ^ 2 * Λ := mul_le_mul_of_nonneg_right h4 hΛ

end BoundsHelpers

variable (d : Sizes)

section BoundsGrid

/-- The matrix dimension is positive (`size = (W L)²`, `W ≥ 1`, `L ≥ 3`). -/
private theorem Bounds_one_le_size (n : ℕ) : 1 ≤ d.size n := by
  unfold Sizes.size
  exact Nat.one_le_pow _ _ (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega))

/-- An entry of `G_k - m` is at most `gueDev`. -/
private theorem Bounds_entry_le_dev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d)
    (a b : Idx (d.L n) (d.W n)) :
    ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
      gueDev d E t1 t0 K n k ω := by
  unfold gueDev
  exact le_ciSup (f := fun ij : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) =>
    ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) ij.1 ij.2‖)
    (Set.finite_range _).bddAbove (a, b)

/-- `gueDev` is at most any nonnegative entrywise bound. -/
private theorem Bounds_dev_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 K n k ω) (spectralZ (E n) (gridTime t1 t0 K n k)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤ c) :
    gueDev d E t1 t0 K n k ω ≤ c := by
  unfold gueDev
  exact Real.iSup_le (fun ij => h ij.1 ij.2) hc

/-- A loop deviation is at most `gueDmax`. -/
private theorem Bounds_le_dmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n m k : ℕ) (ω : PathΩ d)
    (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)) :
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
        (spectralZ (E n) (gridTime t1 t0 K n k)) (loopOf σ a) -
      Kt n (gridTime t1 t0 K n k) (loopOf σ a)‖ ≤ gueDmax d E t1 t0 K Kt n m k ω := by
  unfold gueDmax
  exact le_ciSup (f := fun y : (Fin m → Bool) × (Fin m → Z2 (d.L n)) =>
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
        (spectralZ (E n) (gridTime t1 t0 K n k)) (loopOf y.1 y.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf y.1 y.2)‖)
    (Set.finite_range _).bddAbove (σ, a)

/-- The sum of the entries of an increment, on the truncation event. -/
private theorem Bounds_sum_le (n : ℕ) (w : Sizes.SeqΩ d)
    (h : ∀ i j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n w i j‖ ≤ ((d.size n : ℕ) : ℝ)) :
    ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n w i j‖ ≤
      ((d.size n : ℕ) : ℝ) ^ 2 * ((d.size n : ℕ) : ℝ) := by
  have hcard : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
    exact_mod_cast RBM.Green.flucAvg_card_Idx_eq_size d n
  calc ∑ i : Idx (d.L n) (d.W n), ∑ j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n w i j‖
      ≤ ∑ _i : Idx (d.L n) (d.W n), ∑ _j : Idx (d.L n) (d.W n), ((d.size n : ℕ) : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) ^ 2 * ((d.size n : ℕ) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = _ := by rw [hcard]

/-- **(T3)** `(W²)⁻¹ ≤ (N η_u)⁻¹` on `[t₁, t₀]`, `N = d.size n = W² L²`:
`L² η_u ≤ L²(1 - t₁) ≤ 1`. -/
private theorem Bounds_T3 {E t1 t0 : ℕ → ℝ} (n : ℕ) (hEb : |E n| < 2) (ht0 : t0 n < 1)
    (hellN : (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) :
    (((d.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ (gueScale d E n u)⁻¹ := by
  have hmim : 0 < (spectralM (E n)).im := spectralM_im_pos hEb
  have hmim1 : (spectralM (E n)).im ≤ 1 := RBM.Evol.MLExpVocab_im_le_one (E n)
  have hW : (0 : ℝ) < ((d.W n : ℕ) : ℝ) := by exact_mod_cast d.W_pos n
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have h1t : 0 ≤ 1 - t1 n := by linarith [hu.1]
  have hηpos : 0 < etaT (E n) u := mul_pos hu1 hmim
  have hSpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Bounds_one_le_size d n)
  have hstep1 : (1 - u) * (spectralM (E n)).im ≤ (1 - t1 n) * 1 :=
    mul_le_mul (by linarith [hu.1]) hmim1 hmim.le h1t
  have hLη : (d.L n : ℝ) ^ 2 * etaT (E n) u ≤ 1 := by
    change (d.L n : ℝ) ^ 2 * ((1 - u) * (spectralM (E n)).im) ≤ 1
    calc (d.L n : ℝ) ^ 2 * ((1 - u) * (spectralM (E n)).im)
        ≤ (d.L n : ℝ) ^ 2 * ((1 - t1 n) * 1) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = (d.L n : ℝ) ^ 2 * (1 - t1 n) := by rw [mul_one]
      _ ≤ 1 := hellN
  have hSη : gueScale d E n u ≤ ((d.W n : ℕ) : ℝ) ^ 2 := by
    unfold gueScale
    have e : ((d.size n : ℕ) : ℝ) * etaT (E n) u
        = ((d.W n : ℕ) : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * etaT (E n) u) := by
      rw [Sizes.size_eq]; push_cast; ring
    rw [e]
    calc ((d.W n : ℕ) : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * etaT (E n) u)
        ≤ ((d.W n : ℕ) : ℝ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hLη (by positivity)
      _ = ((d.W n : ℕ) : ℝ) ^ 2 := mul_one _
  exact inv_anti₀ (mul_pos hSpos hηpos) hSη

/-- **The jump step**: the increment term of `gueDev_succ_le` is at most `δ_n / 2` on the
truncation event. -/
private theorem Bounds_jump_le {τU : ℝ} (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (n : ℕ)
    (hτU : 0 < τU) (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (hscN : ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (gueScale d E n t)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (j : ℕ) (ω : PathΩ d)
    (hF : ∀ i i' : Idx (d.L n) (d.W n),
      ‖Sizes.seqXmat d n (ω (j + 1)) i i'‖ ≤ ((d.size n : ℕ) : ℝ)) :
    (etaT (E n) (t0 n))⁻¹ ^ 2 *
        (Real.sqrt (gridStep t1 t0 (gueGridK d n0) n / ((d.size n : ℕ) : ℝ)) *
          ∑ i : Idx (d.L n) (d.W n), ∑ i' : Idx (d.L n) (d.W n),
            ‖Sizes.seqXmat d n (ω (j + 1)) i i'‖ +
          gridStep t1 t0 (gueGridK d n0) n) ≤ gueDelta d τU n / 2 := by
  have hN1 : 1 ≤ d.size n := Bounds_one_le_size d n
  have hN1' : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hK0 : gueGridK d n0 n ≠ 0 := gueGridK_ne_zero d n0 n
  have hmim : 0 < (spectralM (E n)).im := spectralM_im_pos hEb
  have hmim1 : (spectralM (E n)).im ≤ 1 := RBM.Evol.MLExpVocab_im_le_one (E n)
  have hMpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have ht0m : t0 n ∈ Set.Icc (t1 n) (t0 n) := ⟨ht10, le_rfl⟩
  have hη0 : 0 < etaT (E n) (t0 n) := mul_pos (by linarith) hmim
  have hsc0 : (((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) :=
    hscN (t0 n) ht0m
  have hq1 : ((d.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hone : 1 ≤ ((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n) := by
    have := hsc0.trans hq1
    rwa [inv_le_one₀ (mul_pos hMpos hη0)] at this
  have heS : (etaT (E n) (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by
    calc (etaT (E n) (t0 n))⁻¹ = (etaT (E n) (t0 n))⁻¹ * 1 := (mul_one _).symm
      _ ≤ (etaT (E n) (t0 n))⁻¹ * (((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n)) :=
          mul_le_mul_of_nonneg_left hone (inv_nonneg.2 hη0.le)
      _ = ((d.size n : ℕ) : ℝ) := by field_simp
  have hΔ0 : 0 ≤ gridStep t1 t0 (gueGridK d n0) n :=
    GoodEvent_gridStep_nonneg (K := gueGridK d n0) ht10
  have hΔ : gridStep t1 t0 (gueGridK d n0) n * (((d.size n : ℕ) : ℝ) + 1) ^ 64 ≤ 1 := by
    have hKc : ((gueGridK d n0 n : ℕ) : ℝ) = (((d.size n : ℕ) : ℝ) + 1) ^ (32 * n0 + 64) := by
      unfold gueGridK; push_cast; ring
    have hKpos : (0 : ℝ) < (gueGridK d n0 n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hK0
    have hXK : (((d.size n : ℕ) : ℝ) + 1) ^ 64 ≤ (gueGridK d n0 n : ℝ) := by
      rw [hKc]; exact pow_le_pow_right₀ (by linarith) (by omega)
    calc gridStep t1 t0 (gueGridK d n0) n * (((d.size n : ℕ) : ℝ) + 1) ^ 64
        ≤ gridStep t1 t0 (gueGridK d n0) n * (gueGridK d n0 n : ℝ) :=
          mul_le_mul_of_nonneg_left hXK hΔ0
      _ = t0 n - t1 n := by unfold gridStep; field_simp
      _ ≤ 1 := by linarith
  have hSg := Bounds_sum_le d n (ω (j + 1)) hF
  have hδ1 : 1 / ((d.size n : ℕ) : ℝ) ≤ gueDelta d τU n := by
    have hη01 : etaT (E n) (t0 n) ≤ 1 := by
      change (1 - t0 n) * (spectralM (E n)).im ≤ 1
      calc (1 - t0 n) * (spectralM (E n)).im ≤ 1 * 1 :=
            mul_le_mul (by linarith) hmim1 hmim.le (by norm_num)
        _ = 1 := one_mul 1
    calc 1 / ((d.size n : ℕ) : ℝ) ≤ (((d.size n : ℕ) : ℝ))⁻¹ := by rw [one_div]
      _ ≤ (((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹ :=
          inv_anti₀ (mul_pos hMpos hη0) (mul_le_of_le_one_right hMpos.le hη01)
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := hsc0
      _ ≤ gueDelta d τU n := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hSg0 : 0 ≤ ∑ i : Idx (d.L n) (d.W n), ∑ i' : Idx (d.L n) (d.W n),
      ‖Sizes.seqXmat d n (ω (j + 1)) i i'‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact Bounds_jump hN1 hN1' le_rfl (inv_nonneg.2 hη0.le) heS hΔ0 hΔ hSg0 hSg hδ1

end BoundsGrid

/-! ### The pathwise unfreezing -/

/-- **Unfreezing and conclusion, pathwise at a fixed `n` and `ω`**: on the good events the
a-priori threshold `gueDelta d τU` is never reached on the grid, the freezing index never acts,
and the bootstrap outputs give (7.28) and the local law at every grid time.

Hypotheses (all pathwise at the one `n` and the one `ω`, `N = (d.size n : ℝ)`,
`Λ_u = (gueScale d E n u)⁻¹`):
* `hA`, `hB`: the outputs of `eq727GEAt` (at `2 n₀`) and `eq728GAt` for the stopped processes
  `gueLproc`, `gueDproc` (`δ = gueDelta d τU`, `K = gueGridK d n0`, `Nf = size`), at the threshold
  `N^{τ₁}`;
* `hC`: `BoundsACheck.HC` (the pathwise form of the conclusion of `gueGrid_entry_bound` at
  `δ = gueDelta d τU`, threshold `N^{τ₁}`, control `gueLmax … 2 + (W²)⁻¹`);
* `hD`: the step-`0` local law at `t₁`;
* `hF`: the truncation event of `gue_highProb_incr_le` (threshold `d.size n`).

Conclusion: the two fields of `GUEPathBounds` (`Grid.lean`) unfolded at `n`, `ω` and the threshold
`N^τ`. -/
theorem Bounds_path {τU : ℝ} (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n : ℕ) (hτU : 0 < τU)
    (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {τ τ₁ : ℝ} (hτ₁0 : 0 < τ₁) (hτ₁τ : τ₁ < τ)
    (hscN : ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (gueScale d E n t)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hellN : (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (hsmallN : ((d.size n : ℕ) : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 32)
    (h4N : 2 ≤ ((d.size n : ℕ) : ℝ) ^ (τ - τ₁))
    (ω : PathΩ d)
    (hA : ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0),
      gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n u.2 u.1 ω ≤
        ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1))
    (hB : ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0,
      gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n u.2 u.1 ω ≤
        ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n u.1)⁻¹ ^ (u.2 : ℕ))
    (hC : ∀ (k : Fin (gueGridK d n0 n + 1)) (i j : Idx (d.L n) (d.W n)),
      {ω' : PathΩ d | ∀ a b : Idx (d.L n) (d.W n),
          ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω')
              (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
            spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
          gueDelta d τU n}.indicator
        (fun ω' => ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω')
              (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
            spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ^ 2) ω ≤
        ((d.size n : ℕ) : ℝ) ^ τ₁ *
          (gueLmax d E t1 t0 (gueGridK d n0) n 2 k ω +
            (((d.W n : ℕ) : ℝ) ^ 2)⁻¹))
    (hD : ∀ i j : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n 0 ω) (spectralZ (E n) (t1 n)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2))
    (hF : ∀ k, 1 ≤ k → k ≤ gueGridK d n0 n → ∀ i j : Idx (d.L n) (d.W n),
      ‖Sizes.seqXmat d n (ω k) i j‖ ≤ ((d.size n : ℕ) : ℝ)) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n0 → ∀ (k : Fin (gueGridK d n0 n + 1)) (σ : Fin m → Bool)
        (a : Fin m → Z2 (d.L n)),
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n k ω))
            (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) (loopOf σ a) -
          Kt n (gridTime t1 t0 (gueGridK d n0) n k) (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ τ *
            (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m) ∧
      (∀ (k : Fin (gueGridK d n0 n + 1)) (i j : Idx (d.L n) (d.W n)),
        ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω)
            (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
          ((d.size n : ℕ) : ℝ) ^ τ *
            (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ ((1 : ℝ) / 2)) := by
  classical
  have hN1 : 1 ≤ d.size n := Bounds_one_le_size d n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hp1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  have hp0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τ₁ := by linarith
  have hδpos : 0 < gueDelta d τU n := Real.rpow_pos_of_pos hN0 _
  have hmim : 0 < (spectralM (E n)).im := spectralM_im_pos hEb
  have hη : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < etaT (E n) u := fun u hu =>
    mul_pos (by linarith [hu.2]) hmim
  have htime : ∀ k ≤ gueGridK d n0 n,
      gridTime t1 t0 (gueGridK d n0) n k ∈ Set.Icc (t1 n) (t0 n) := by
    intro k hk
    refine ⟨?_, GoodEvent_gridTime_le ht10 hk⟩
    have h := GoodEvent_gridTime_mono (K := gueGridK d n0) ht10 (Nat.zero_le k)
    rwa [GoodEvent_gridTime_zero] at h
  have hΛ0 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ (gueScale d E n u)⁻¹ :=
    fun u hu => (inv_pos.2 (mul_pos hN0 (hη u hu))).le
  have hT3 : ∀ u ∈ Set.Icc (t1 n) (t0 n),
      (((d.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ (gueScale d E n u)⁻¹ :=
    fun u hu => Bounds_T3 d n hEb ht0 hellN hu
  have hkey : 2 * (((d.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * ((d.size n : ℕ) : ℝ) ^ (-τU) ≤
      (gueDelta d τU n / 4) ^ 2 :=
    Bounds_rpow_key hN0 hsmallN
  -- the entry bound `hC` at an step below the threshold: `|(G_j - m)_{ab}|² ≤ 2 p² Λ_{u_j}`
  have hsq : ∀ j ≤ gueGridK d n0 n,
      j ≤ gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω →
      gueDev d E t1 t0 (gueGridK d n0) n j ω < gueDelta d τU n → ∀ a b : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω)
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ^ 2 ≤
        2 * (((d.size n : ℕ) : ℝ) ^ τ₁) ^ 2 *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ := by
    intro j hj hjσ hdev a b
    have hmem : ω ∈ {ω' : PathΩ d | ∀ a b : Idx (d.L n) (d.W n),
        ‖(green (gueH d t1 t0 (gueGridK d n0) n j ω')
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n j)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
          gueDelta d τU n} :=
      fun a b => (Bounds_entry_le_dev d E t1 t0 (gueGridK d n0) n j ω a b).trans hdev.le
    have hCj := hC ⟨j, Nat.lt_succ_of_le hj⟩ a b
    rw [Set.indicator_of_mem hmem] at hCj
    have hAj := hA (⟨gridTime t1 t0 (gueGridK d n0) n j, htime j hj⟩, ⟨2, le_rfl, by omega⟩)
    have hAj' : gueLmax d E t1 t0 (gueGridK d n0) n 2 j ω ≤ ((d.size n : ℕ) : ℝ) ^ τ₁ *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ := by
      have e := gueLproc_time d E t1 t0 (gueGridK d n0) (gueDelta d τU) n 2 j ht10 hj ω
      rw [Nat.min_eq_left hjσ] at e
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      have h : gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n 2
          (gridTime t1 t0 (gueGridK d n0) n j) ω ≤ ((d.size n : ℕ) : ℝ) ^ τ₁ *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ ^ ((2 : ℕ) - 1) := hAj
      rw [e, h21, pow_one] at h
      exact h
    exact (Bounds_sq_le hp1 hAj' (hT3 _ (htime j hj)) (hscN _ (htime j hj))
      (hΛ0 _ (htime j hj)) hCj).1
  have hσ : ∀ k ≤ gueGridK d n0 n,
      (∀ i ≤ k, gueDev d E t1 t0 (gueGridK d n0) n i ω < gueDelta d τU n) →
      k ≤ gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω :=
    fun k hk h => Bounds_le_firstHit
      (fun k ω' => gueDev d E t1 t0 (gueGridK d n0) n k ω') (gueDelta d τU n) (gueGridK d n0 n)
      ω hk h
  -- step `0` of the induction
  have h0 : gueDev d E t1 t0 (gueGridK d n0) n 0 ω < gueDelta d τU n := by
    have hle : gueDev d E t1 t0 (gueGridK d n0) n 0 ω ≤ gueDelta d τU n / 4 := by
      refine Bounds_dev_le d E t1 t0 (gueGridK d n0) n 0 ω (by positivity) fun a b => ?_
      have h := hD a b
      rw [← Real.sqrt_eq_rpow] at h
      have hmem1 : t1 n ∈ Set.Icc (t1 n) (t0 n) := ⟨le_rfl, ht10⟩
      have hx := Bounds_le_of_sqrt (norm_nonneg _) (hΛ0 _ hmem1) (hscN _ hmem1) hδpos.le hkey h
      rw [GoodEvent_gridTime_zero]
      exact hx
    linarith
  -- the one-step jump
  have hjump : ∀ j < gueGridK d n0 n, gueDev d E t1 t0 (gueGridK d n0) n (j + 1) ω ≤
      gueDev d E t1 t0 (gueGridK d n0) n j ω + gueDelta d τU n / 2 := fun j hj =>
    (gueDev_succ_le d E t1 t0 (gueGridK d n0) n j hEb ht10 ht0 hj ω).trans
      (add_le_add le_rfl (Bounds_jump_le d n0 n hτU hEb ht1 ht10 ht0 hscN j ω
        (fun a b => hF (j + 1) (by omega) (by omega) a b)))
  -- the inductive step below the threshold
  have hstep : ∀ j < gueGridK d n0 n,
      j ≤ gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω →
      gueDev d E t1 t0 (gueGridK d n0) n j ω < gueDelta d τU n →
      gueDev d E t1 t0 (gueGridK d n0) n j ω ≤ gueDelta d τU n / 4 := by
    intro j hj hjσ hdev
    refine Bounds_dev_le d E t1 t0 (gueGridK d n0) n j ω (by positivity) fun a b => ?_
    have hq : 2 * (((d.size n : ℕ) : ℝ) ^ τ₁) ^ 2 *
        (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n j))⁻¹ ≤
        2 * (((d.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * ((d.size n : ℕ) : ℝ) ^ (-τU) :=
      mul_le_mul_of_nonneg_left (hscN _ (htime j hj.le)) (by positivity)
    exact Bounds_le_of_sq (norm_nonneg _) hδpos.le (hsq j hj.le hjσ hdev a b) (hq.trans hkey)
  have hall := Bounds_unfreeze (K := gueGridK d n0 n)
    (fun k => gueDev d E t1 t0 (gueGridK d n0) n k ω)
    (gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω) hσ h0 hstep hjump hδpos
  have hdev : ∀ k ≤ gueGridK d n0 n,
      gueDev d E t1 t0 (gueGridK d n0) n k ω < gueDelta d τU n :=
    fun k hk => hall k hk k le_rfl
  have hkσ : ∀ k ≤ gueGridK d n0 n,
      k ≤ gueStop d E t1 t0 (gueGridK d n0) (gueDelta d τU) n ω :=
    fun k hk => hσ k hk (hall k hk)
  have hpτ : ((d.size n : ℕ) : ℝ) ^ τ₁ ≤ ((d.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1' hτ₁τ.le
  refine ⟨fun m hm1 hmn k σ a => ?_, fun k i j => ?_⟩
  · have hk : (k : ℕ) ≤ gueGridK d n0 n := Nat.lt_succ_iff.1 k.2
    have h1 := Bounds_le_dmax d E t1 t0 (gueGridK d n0) Kt n m k ω σ a
    have h2 := gueDproc_time d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m k ht10 hk ω
    rw [Nat.min_eq_left (hkσ k hk)] at h2
    have h3 : gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n m
        (gridTime t1 t0 (gueGridK d n0) n k) ω ≤ ((d.size n : ℕ) : ℝ) ^ τ₁ *
        (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m :=
      hB (⟨gridTime t1 t0 (gueGridK d n0) n k, htime k hk⟩, ⟨m, hm1, hmn⟩)
    rw [h2] at h3
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ ≤ ((d.size n : ℕ) : ℝ) ^ τ *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right hpτ (pow_nonneg (hΛ0 _ (htime k hk)) m)
  · have hk : (k : ℕ) ≤ gueGridK d n0 n := Nat.lt_succ_iff.1 k.2
    have hx2 := hsq k hk (hkσ k hk) (hdev k hk) i j
    have hP : 2 * ((d.size n : ℕ) : ℝ) ^ τ₁ ≤ ((d.size n : ℕ) : ℝ) ^ τ := by
      have e : ((d.size n : ℕ) : ℝ) ^ τ =
          ((d.size n : ℕ) : ℝ) ^ (τ - τ₁) * ((d.size n : ℕ) : ℝ) ^ τ₁ := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [e]; exact mul_le_mul_of_nonneg_right h4N hp0
    have hΛ := hΛ0 _ (htime k hk)
    rw [← Real.sqrt_eq_rpow]
    exact Bounds_final (norm_nonneg _) hΛ hp0 hP hx2

/-! ### The entry-bound hypothesis and the interface with `GUEPathBounds` -/

namespace BoundsACheck

/-- The entry-bound hypothesis of `Bounds_path`: the pathwise form of the conclusion of
`gueGrid_entry_bound`. -/
def HC (d : Sizes) (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (τU τ₁ : ℝ) (n : ℕ) (ω : PathΩ d) : Prop :=
  ∀ (k : Fin (RBM.Univ.GUEPhase.gueGridK d n0 n + 1)) (i j : Idx (d.L n) (d.W n)),
    {ω' : PathΩ d | ∀ a b : Idx (d.L n) (d.W n),
        ‖(green (RBM.Univ.GUEPhase.gueH d t1 t0 (RBM.Univ.GUEPhase.gueGridK d n0) n k ω')
            (spectralZ (E n) (gridTime t1 t0 (RBM.Univ.GUEPhase.gueGridK d n0) n k)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b‖ ≤
        RBM.Univ.GUEPhase.gueDelta d τU n}.indicator
      (fun ω' => ‖(green (RBM.Univ.GUEPhase.gueH d t1 t0 (RBM.Univ.GUEPhase.gueGridK d n0) n k ω')
            (spectralZ (E n) (gridTime t1 t0 (RBM.Univ.GUEPhase.gueGridK d n0) n k)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ^ 2) ω ≤
      ((d.size n : ℕ) : ℝ) ^ τ₁ *
        (RBM.Univ.GUEPhase.gueLmax d E t1 t0 (RBM.Univ.GUEPhase.gueGridK d n0) n 2 k ω +
          (((d.W n : ℕ) : ℝ) ^ 2)⁻¹)

/-- The conclusion of `Bounds_path` at `(n, ω, τ)` (the two fields of `GUEPathBounds` unfolded). -/
abbrev Concl (d : Sizes) (E t1 t0 : ℕ → ℝ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (τ : ℝ) (n : ℕ) (ω : PathΩ d) : Prop :=
  (∀ m : ℕ, 1 ≤ m → m ≤ n0 → ∀ (k : Fin (gueGridK d n0 n + 1)) (σ : Fin m → Bool)
      (a : Fin m → Z2 (d.L n)),
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n k ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK d n0) n k) (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m) ∧
    (∀ (k : Fin (gueGridK d n0 n + 1)) (i j : Idx (d.L n) (d.W n)),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n k ω)
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) -
        spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ *
          (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ ((1 : ℝ) / 2))

section Sources

variable (d : Sizes) (E t1 t0 : ℕ → ℝ) (n0 : ℕ) {τ₁ : ℝ}

/-- Source of `hC`: the conclusion of `gueGrid_entry_bound` at `δ = gueDelta d τU` gives, for
`τ₁ > 0`, the w.h.p. event `{ω | HC … ω}`. -/
theorem highProbAt_HC (τU : ℝ) (hτ₁ : 0 < τ₁)
    (h : StochDomAt (Pgue d) d.size
      (fun n (p : Fin (gueGridK d n0 n + 1) × (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))) ω =>
        {ω' : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
            ‖(green (gueH d t1 t0 (gueGridK d n0) n p.1 ω')
                (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) -
              spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
            gueDelta d τU n}.indicator
          (fun ω' => ‖(green (gueH d t1 t0 (gueGridK d n0) n p.1 ω')
                (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) -
              spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax d E t1 t0 (gueGridK d n0) n 2 p.1 ω + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹)) :
    HighProbAt (Pgue d) d.size (fun n => {ω : PathΩ d | HC d E t1 t0 n0 τU τ₁ n ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h hτ₁)
    (Filter.Eventually.of_forall fun _ _ hω k i j => hω (k, (i, j)))

/-- Source of `hA`: the output of `eq727GEAt` (`P = Pgue d`, `size = d.size`, `Nf n = d.size n`,
`η n = etaT (E n)`, `Lm = gueLproc`, `n₀ ↦ 2 n₀`). -/
theorem highProbAt_hA (τU : ℝ) (hτ₁ : 0 < τ₁)
    (h : StochDomAt (Pgue d) d.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0)) ω =>
        gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n p.2 p.1 ω)
      (fun n p _ => (((d.size n : ℕ) : ℝ) * etaT (E n) p.1)⁻¹ ^ ((p.2 : ℕ) - 1))) :
    HighProbAt (Pgue d) d.size (fun n => {ω : PathΩ d |
      ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0),
        gueLproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) n u.2 u.1 ω ≤
          ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1)}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h hτ₁

/-- Source of `hB`: the output of `eq728GAt` (`Dm = gueDproc`). -/
theorem highProbAt_hB (τU : ℝ) (hτ₁ : 0 < τ₁) (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (h : StochDomAt (Pgue d) d.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n p.2 p.1 ω)
      (fun n p _ => (((d.size n : ℕ) : ℝ) * etaT (E n) p.1)⁻¹ ^ (p.2 : ℕ))) :
    HighProbAt (Pgue d) d.size (fun n => {ω : PathΩ d |
      ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0,
        gueDproc d E t1 t0 (gueGridK d n0) (gueDelta d τU) Kt n u.2 u.1 ω ≤
          ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n u.1)⁻¹ ^ (u.2 : ℕ)}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h hτ₁

/-- Source of `hD`: the step-`0` local law at `t₁` gives, for `τ₁ > 0`, the w.h.p. event
`{ω | hD-statement}`. -/
theorem highProbAt_hD (hτ₁ : 0 < τ₁)
    (h : StochDomAt (Pgue d) d.size
      (fun n (ij : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) ω =>
        ‖(green (gueH d t1 t0 (gueGridK d n0) n 0 ω) (spectralZ (E n) (t1 n)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
            ij.1 ij.2‖)
      (fun n _ _ => (gueScale d E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2))) :
    HighProbAt (Pgue d) d.size (fun n => {ω : PathΩ d | ∀ i j : Idx (d.L n) (d.W n),
      ‖(green (gueH d t1 t0 (gueGridK d n0) n 0 ω) (spectralZ (E n) (t1 n)) -
          spectralM (E n) • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) i j‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ₁ * (gueScale d E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h hτ₁)
    (Filter.Eventually.of_forall fun _ _ hω i j => hω (i, j))

/-- Source of `hF`: `gue_highProb_incr_le` (threshold `d.size n`). -/
theorem highProbAt_hF (hsize : Tendsto (fun n => d.size n) atTop atTop) :
    HighProbAt (Pgue d) d.size (fun n => {ω : PathΩ d | ∀ k, 1 ≤ k → k ≤ gueGridK d n0 n →
      ∀ i j : Idx (d.L n) (d.W n), ‖Sizes.seqXmat d n (ω k) i j‖ ≤ ((d.size n : ℕ) : ℝ)}) :=
  gue_highProb_incr_le d n0 hsize

end Sources

/-- **The interface fit**: if for every `τ > 0` the conclusion of `Bounds_path` holds
with high probability (on the size scale), then `GUEPathBounds` holds, by
`stochDomAt_of_forall_highProbAt` applied to the two fields. -/
theorem pathBounds_of_forall_highProbAt (d : Sizes) (E t1 t0 : ℕ → ℝ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue d) d.size
      (fun n => {ω : PathΩ d | Concl d E t1 t0 n0 Kt τ n ω})) :
    GUEPathBounds d E t1 t0 (gueGridK d n0) n0 Kt := by
  refine ⟨fun m hm1 hmn => stochDomAt_of_forall_highProbAt fun τ hτ => ?_,
    stochDomAt_of_forall_highProbAt fun τ hτ => ?_⟩
  · exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (hmain τ hτ)
      (Filter.Eventually.of_forall fun n ω hω u => hω.1 m hm1 hmn u.1 u.2.1 u.2.2)
  · exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (hmain τ hτ)
      (Filter.Eventually.of_forall fun n ω hω u => hω.2 u.1 u.2.1 u.2.2)

end BoundsACheck

end RBM.Univ.GUEPhase
