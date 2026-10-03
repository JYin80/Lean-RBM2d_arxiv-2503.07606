/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.EntryCore
import RBM2D.Green.Stability
import RBM2D.Green.Pins
import RBM2D.Green.EntryBlock
import RBM2D.Induction.PerTimeCalc

/-!
# The `≺` layer of Lemma 4.2 of [YY_25] in the per-sequence form of `GbEXPHypV3`

The paper does not restate (4.2), (4.3), (4.5): it says that the proof of `lem_GbEXP` follows
Lemma 4.2 of [YY_25].  This file carries out the stochastic layer of that proof onto the `≺`
calculus `PerTimeDomAt (Sizes.seqP d) d.size` (`Induction/PerTimeCalc.lean`) and the block model
(`EntryCore`, `Stability`, `EntryBlock`).  Time `t n` and energy `E n` are sequences indexed by
the size index `n`.

Contents:
1. `of_det`: from a deterministic implication to `≺`.  The
   constant is a sequence (`Kstab2 κ L_n = O(log L_n)`), and the event of the input bounds is an
   abstract high-probability event family;
2. bookkeeping: `OffPair`, `goodSet`, the indicator `omegaInd` as an indicator of `goodSet`
   (`entryDom_omegaInd_mul_eq_indicator`), the bridge `entryDom_goodEvent_of_llErr` (fine-lattice
   `llErrMat` to the block-level `GoodEvent`), the grid union bound, the absorption
   `Kstab2 κ L_n ≤ size^ε`, and `AsGMcSeq ⟹ Ω(t, c/2)` w.h.p.
   (`entryDom_goodSet_highProb_of_asGMc`);
3. (4.2): `entry_bound_stochDom` (`GijOmegaSeq`), `entry_bound_stochDom_of_highProb`,
   `entry_bound_stochDom_of_asGMc` (`GijSeq`);
4. (4.3): `diag_bound_stochDom` (`GiiOmegaSeq`), `diag_bound_stochDom_of_highProb`,
   `diag_bound_stochDom_of_asGMc` (`GiiSeq`).

The `≺` calculus uses `perTimeCalc_highProbAt_inter` and `PerTime.stochDom_of_indicator`.  The
LDE inputs are `PerTimeDomAt` hypotheses over `OffPair` (row, column) or `BlockIndex` (quadratic
form, diagonal).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. The engine `of_det` -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- **From a deterministic implication to `≺`.**  `Ξ l Φ` is the event that all the input
bounds hold with the factor `Φ`; it holds with high probability at `Φ = (size l)^{τ'}` for
every `τ' > 0`.  The constant is a sequence `C l ≤ (size l)^ε` (for `d = 2` it contains
`Kstab2 κ L_n`, which grows like `log L_n`), and the requirement `δ ≤ ε₀` is absorbed into
`hdet`. -/
theorem of_det (hsize : Tendsto size atTop atTop) {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) {Ξ : ℕ → ℝ → Set Ω}
    (hΞ : ∀ τ' > (0 : ℝ), HighProbAt P size (fun l => Ξ l ((size l : ℝ) ^ τ')))
    {δ C : ℕ → ℝ} (hδ0 : ∀ l, 0 ≤ δ l) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ l : ℕ in atTop, δ l ≤ (size l : ℝ) ^ (-c₀))
    (hC : ∀ ε > (0 : ℝ), ∀ᶠ l : ℕ in atTop, C l ≤ (size l : ℝ) ^ ε) (k : ℕ)
    (hdet : ∀ᶠ l : ℕ in atTop, ∀ ω (Φ : ℝ), 1 ≤ Φ → 36 * Φ * δ l ^ 2 ≤ 1 → ω ∈ Ξ l Φ →
      ∀ u, ξ l u ω ≤ C l * Φ ^ k * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  have hk0 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  obtain ⟨τ', hτ'⟩ : ∃ τ', τ' = min (τ / (2 * ((k : ℝ) + 1))) c₀ := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := hτ' ▸ lt_min (div_pos hτ hk0) hc₀
  have hτ'c : τ' ≤ c₀ := hτ' ▸ min_le_right _ _
  have hτ'k : τ' * k ≤ τ / 2 := by
    have h1 : τ' ≤ τ / (2 * ((k : ℝ) + 1)) := hτ' ▸ min_le_left _ _
    have h2 : τ' * (2 * ((k : ℝ) + 1)) ≤ τ := by rwa [le_div_iff₀ hk0] at h1
    nlinarith [hτ'0]
  filter_upwards [hΞ τ' hτ'0 D hD, hsize.eventually (eventually_ge_atTop 1), hδ,
    hsize.eventually (eventually_le_rpow 36 hc₀), hC (τ / 2) (half_pos hτ), hdet] with
    l hP hN1 hδl h36 hCl hdetl u
  refine (measure_mono ?_).trans hP
  have hN : (1 : ℝ) ≤ (size l : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (size l : ℝ) := by linarith
  have hNc : 0 < (size l : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN0 c₀
  have hNneg : (size l : ℝ) ^ (-c₀) = ((size l : ℝ) ^ c₀)⁻¹ := Real.rpow_neg hN0.le c₀
  intro ω hω hmem
  have hω' : (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω := hω
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (size l : ℝ) ^ τ' := ⟨_, rfl⟩
  have hΦ1 : 1 ≤ Φ := hΦ ▸ Real.one_le_rpow hN hτ'0.le
  have hΦc : Φ ≤ (size l : ℝ) ^ c₀ := hΦ ▸ Real.rpow_le_rpow_of_exponent_le hN hτ'c
  have hΦδ : 36 * Φ * δ l ^ 2 ≤ 1 := by
    have h1 : δ l ^ 2 ≤ ((size l : ℝ) ^ (-c₀)) ^ 2 := pow_le_pow_left₀ (hδ0 l) hδl 2
    have h2 : Φ * ((size l : ℝ) ^ (-c₀)) ^ 2 ≤ (size l : ℝ) ^ (-c₀) := by
      rw [hNneg]
      have h3 : Φ * ((size l : ℝ) ^ c₀)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hNc, one_mul]; exact hΦc
      calc Φ * (((size l : ℝ) ^ c₀)⁻¹) ^ 2
          = (Φ * ((size l : ℝ) ^ c₀)⁻¹) * ((size l : ℝ) ^ c₀)⁻¹ := by ring
        _ ≤ 1 * ((size l : ℝ) ^ c₀)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ((size l : ℝ) ^ c₀)⁻¹ := one_mul _
    have h4 : 36 * (size l : ℝ) ^ (-c₀) ≤ 1 := by
      rw [hNneg, ← div_eq_mul_inv, div_le_one hNc]; exact h36
    have h5 : 0 ≤ Φ := by linarith
    calc 36 * Φ * δ l ^ 2 ≤ 36 * (Φ * ((size l : ℝ) ^ (-c₀)) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h1 h5
          linarith
      _ ≤ 36 * (size l : ℝ) ^ (-c₀) := by linarith
      _ ≤ 1 := h4
  have hmem' : ω ∈ Ξ l Φ := hΦ ▸ hmem
  have hbound := hdetl ω Φ hΦ1 hΦδ hmem' u
  have hΦk : Φ ^ k ≤ (size l : ℝ) ^ (τ / 2) := by
    rw [hΦ, ← Real.rpow_mul_natCast hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN hτ'k
  have hζu := hζ l u ω
  have hΦk0 : 0 ≤ Φ ^ k := pow_nonneg (by linarith) k
  have hfin : C l * Φ ^ k * ζ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω := by
    have e1 : C l * Φ ^ k * ζ l u ω ≤ (size l : ℝ) ^ (τ / 2) * (Φ ^ k * ζ l u ω) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hCl (mul_nonneg hΦk0 hζu)
    have e2 : (size l : ℝ) ^ (τ / 2) * (Φ ^ k * ζ l u ω)
        ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦk hζu)
        (Real.rpow_nonneg hN0.le _)
    have e3 : (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω)
        = (size l : ℝ) ^ τ * ζ l u ω := by
      rw [← mul_assoc, ← Real.rpow_add hN0]
      congr 2
      ring
    linarith
  linarith

end Engine

/-! ## 2. Size bookkeeping, the union bound, the good event -/

section Bookkeeping

variable (d : Sizes)

/-- Ordered pairs of distinct block indices (in `BlockIndex L W`). -/
abbrev OffPair (L W : ℕ) : Type := {p : BlockIndex L W × BlockIndex L W // p.1 ≠ p.2}

/-- The event `Ω(t,c)_n = {‖G_t - m‖_max ≤ W^{-c}}` of `def_asGMc` at size index `n`;
`omegaInd` is its indicator.  The event `GoodEvent (green (H N ω) z) m (δ N)` is here stated on
the fine lattice, through `llErrMat`, because that is the form of `omegaInd` and `AsGMcSeq`. -/
def goodSet (d : Sizes) (E t : ℕ → ℝ) (c : ℝ) (n : ℕ) : Set (Sizes.SeqΩ d) :=
  {ω | ∀ i j : Idx (d.L n) (d.W n),
    llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤ (d.W n : ℝ) ^ (-c)}

private theorem omegaInd_of_forall {L W : ℕ} [NeZero L] [NeZero W] {E u c : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ}
    (h : ∀ i j : Idx L W, llErrMat L W E u M i j ≤ (W : ℝ) ^ (-c)) : omegaInd L W E u c M = 1 := by
  simp [omegaInd, h]

private theorem omegaInd_of_not {L W : ℕ} [NeZero L] [NeZero W] {E u c : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ}
    (h : ¬ ∀ i j : Idx L W, llErrMat L W E u M i j ≤ (W : ℝ) ^ (-c)) : omegaInd L W E u c M = 0 := by
  simp only [omegaInd, h, ↓reduceIte]

theorem entryDom_omegaInd_mul_eq_indicator (E t : ℕ → ℝ) (c : ℝ) (n : ℕ) (ω : Sizes.SeqΩ d)
    (f : Sizes.SeqΩ d → ℝ) :
    omegaInd (d.L n) (d.W n) (E n) (t n) c (Sizes.seqHflow d n (t n) ω) * f ω =
      (goodSet d E t c n).indicator f ω := by
  by_cases h : ω ∈ goodSet d E t c n
  · rw [Set.indicator_of_mem h]
    have h' : ∀ i j : Idx (d.L n) (d.W n),
        llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤
          (d.W n : ℝ) ^ (-c) := h
    rw [omegaInd_of_forall h', one_mul]
  · rw [Set.indicator_of_notMem h]
    have h' : ¬ ∀ i j : Idx (d.L n) (d.W n),
        llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤
          (d.W n : ℝ) ^ (-c) := h
    rw [omegaInd_of_not h', zero_mul]

private theorem tendsto_size_of {d : Sizes} (hsz : RBM.Ind.SizeTendsto d) :
    Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

private theorem card_blockIndex (n : ℕ) :
    Fintype.card (BlockIndex (d.L n) (d.W n)) = d.size n := by
  rw [card_BlockIndex, Sizes.size, mul_comm]

private theorem card_offPair_le (n : ℕ) :
    Fintype.card (OffPair (d.L n) (d.W n)) ≤ d.size n ^ 2 := by
  calc Fintype.card (OffPair (d.L n) (d.W n))
      ≤ Fintype.card (BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) :=
        Fintype.card_subtype_le _
    _ = d.size n ^ 2 := by rw [Fintype.card_prod, card_blockIndex, sq]

private theorem card_idx_sq (n : ℕ) :
    Fintype.card (Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) ≤ d.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit]
  have : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
    simp [Idx, Z2, ZMod.card, Sizes.size, pow_two]
  rw [this, one_mul, sq]

private theorem card_real_le {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (h : ∀ n, Fintype.card (V n) ≤ d.size n ^ m) (n : ℕ) :
    (Fintype.card (V n) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (m : ℝ) := by
  rw [Real.rpow_natCast]; exact_mod_cast h n

/-- The grid union bound in the form used here: a per-time bound over an index set of size at most
`size^m` gives an event of high probability (`stochDomAt_of_perTimeDomAt`,
`perTimeCalc_highProbAt_of_stochDomAt`). -/
private theorem highProb_of_perTime {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (hV : ∀ n, Fintype.card (V n) ≤ d.size n ^ m)
    {ξ ζ : ∀ n, V n → Sizes.SeqΩ d → ℝ} (h : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) {τ : ℝ}
    (hτ : 0 < τ) :
    HighProbAt (Sizes.seqP d) d.size
      (fun n => {ω | ∀ v, ξ n v ω ≤ ((d.size n : ℕ) : ℝ) ^ τ * ζ n v ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
    (stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (m : ℝ)) (Nat.cast_nonneg m)
      (Eventually.of_forall (card_real_le d hV)) h) hτ

private theorem W_le_size (n : ℕ) : d.W n ≤ d.size n := by
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have h1 : d.W n ≤ d.W n * d.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : d.W n * d.L n ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact h1.trans h2

private theorem kstab2_nonneg (κ : ℝ) (L : ℕ) : 0 ≤ Kstab2 κ L := by
  unfold Kstab2
  have hg : 0 ≤ RBM.KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  positivity

/-- `Kstab2 κ L_n ≤ (size n)^ε` eventually, for every `ε > 0` (from
`eventually_Kstab2_mul_rpow_le` and `W ≤ size`). -/
private theorem eventually_Kstab2_le_rpow {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Kstab2 κ (d.L n) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [eventually_Kstab2_mul_rpow_le d hκ h𝔠 hε hsz hbw] with n hn
  have hW : 0 < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWε : 0 < (d.W n : ℝ) ^ ε := Real.rpow_pos_of_pos hW ε
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, div_le_iff₀ hWε] at hn
  have hWN : (d.W n : ℝ) ^ ε ≤ ((d.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow hW.le (by exact_mod_cast W_le_size d n) hε.le
  have hpos : 0 ≤ (d.W n : ℝ) ^ ε := hWε.le
  linarith

/-- `W^{-c} ≤ (size)^{-(𝔠 c)}` eventually (Bandwidth). -/
private theorem eventually_W_rpow_neg_le {𝔠 : ℝ} (hsz : RBM.Ind.SizeTendsto d)
    (hbw : Bandwidth d 𝔠) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, (d.W n : ℝ) ^ (-c) ≤ ((d.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by
  filter_upwards [hbw, hsz.eventually_gt_atTop 0] with n hn hN0
  have hNp : 0 < ((d.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  calc (d.W n : ℝ) ^ (-c) ≤ (((d.size n : ℕ) : ℝ) ^ 𝔠) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hNp hn (by linarith)
    _ = ((d.size n : ℕ) : ℝ) ^ (𝔠 * -c) := (Real.rpow_mul hN0.le _ _).symm
    _ = ((d.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by rw [mul_neg]

private theorem delta_le_half {Φ δ : ℝ} (hδ0 : 0 ≤ δ) (hΦ1 : 1 ≤ Φ) (h : 36 * Φ * δ ^ 2 ≤ 1) :
    δ ≤ 1 / 2 := by
  by_contra hcon
  have hcon := lt_of_not_ge hcon
  nlinarith [sq_nonneg δ, mul_nonneg (sub_nonneg.2 hΦ1) (sq_nonneg δ)]

/-- Deterministic bridge: `‖G_u - m‖_max ≤ δ` on the fine lattice (`llErrMat`) is the `GoodEvent`
of the block-level resolvent `greenBlk` (`greenBlk = (blockMat M - z)⁻¹` is the fine-lattice
resolvent relabelled by `splitEquiv`, `Matrix.inv_submatrix_equiv`). -/
theorem entryDom_goodEvent_of_llErr (L W : ℕ) [NeZero L] [NeZero W] (E u δ : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (h : ∀ i j, llErrMat L W E u M i j ≤ δ) :
    GoodEvent (greenBlk L W E u M true) (spectralM E) δ := by
  intro x y
  have hG : greenBlk L W E u M true =
      ((M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹).submatrix
        (splitEquiv L W).symm (splitEquiv L W).symm := by
    rw [greenBlk, Gsig_true, green, blockMat]
    have h1 : M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm -
        spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
        (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
          (splitEquiv L W).symm (splitEquiv L W).symm := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp
      · have : (splitEquiv L W).symm i ≠ (splitEquiv L W).symm j :=
          fun h => hij ((splitEquiv L W).symm.injective h)
        simp [hij, this]
    rw [h1, Matrix.inv_submatrix_equiv]
  rw [hG, Matrix.submatrix_apply]
  have h2 := h ((splitEquiv L W).symm x) ((splitEquiv L W).symm y)
  unfold llErrMat at h2
  by_cases hxy : x = y
  · subst hxy; simpa using h2
  · have hxy' : (splitEquiv L W).symm x ≠ (splitEquiv L W).symm y :=
      fun h3 => hxy ((splitEquiv L W).symm.injective h3)
    simpa [hxy, hxy'] using h2

/-- `4320 K_n² ≤ size^ε` eventually (the constant of (4.3)). -/
private theorem eventually_const_kstab2_sq_le {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 4320 * Kstab2 κ (d.L n) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [eventually_Kstab2_le_rpow d hκ h𝔠 hsz hbw (show 0 < ε / 4 by positivity),
    (tendsto_size_of hsz).eventually (eventually_le_rpow 4320 (show 0 < ε / 2 by positivity))]
    with n hK h4320
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK0 := kstab2_nonneg κ (d.L n)
  have h1 : Kstab2 κ (d.L n) ^ 2 ≤ (((d.size n : ℕ) : ℝ) ^ (ε / 4)) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  have h2 : (((d.size n : ℕ) : ℝ) ^ (ε / 4)) ^ 2 = ((d.size n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; congr 1; push_cast; ring
  calc 4320 * Kstab2 κ (d.L n) ^ 2
      ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) * ((d.size n : ℕ) : ℝ) ^ (ε / 2) :=
        mul_le_mul h4320 (h1.trans h2.le) (sq_nonneg _) (Real.rpow_nonneg hN0 _)
    _ = ((d.size n : ℕ) : ℝ) ^ ε := by
        rw [← Real.rpow_add' hN0 (by positivity : ε / 2 + ε / 2 ≠ 0)]; congr 1; ring

/-- `AsGMcSeq d E t c` gives `Ω(t, c/2)` with high probability. -/
theorem entryDom_goodSet_highProb_of_asGMc {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : RBM.Ind.SizeTendsto d)
    (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hAs : AsGMcSeq d E t c) :
    HighProbAt (Sizes.seqP d) d.size (goodSet d E t (c / 2)) := by
  have h1 := highProb_of_perTime d (m := 2) (card_idx_sq d) hAs
    (τ := 𝔠 * c / 2) (by positivity)
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono h1 ?_
  filter_upwards [hbw, (tendsto_size_of hsz).eventually_gt_atTop 0] with n hn hN0 ω hω i j
  have hN : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN0
  have hW : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hNW : ((d.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) ≤ (d.W n : ℝ) ^ (c / 2) := by
    calc ((d.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) = (((d.size n : ℕ) : ℝ) ^ 𝔠) ^ (c / 2) := by
          rw [← Real.rpow_mul hN.le]; congr 1; ring
      _ ≤ (d.W n : ℝ) ^ (c / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hn (by positivity)
  have h2 := hω ((), i, j)
  calc llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j
      ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) * (d.W n : ℝ) ^ (-c) := h2
    _ ≤ (d.W n : ℝ) ^ (c / 2) * (d.W n : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right hNW (Real.rpow_nonneg hW.le _)
    _ = (d.W n : ℝ) ^ (-(c / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

end Bookkeeping

/-! ## 3. (4.2): the entry bound `GijOmegaSeq`, `GijSeq` -/

section Entry

variable (d : Sizes)

/-- **(4.2), `GijOmegaSeq`** (`GijGEX`, on `Ω(t,c)`, off the diagonal, swapped right side):
`1_{Ω(t,c)} |G_{pq}|² ≺ gexRHS … q.1 p.1` from the large deviation bounds for the row and column
sums of (4.8) (`hLrow`, `hLcol`, in `PerTimeDomAt` form, over the ordered pairs of distinct
blocks-with-offsets), with `PerTimeDomAt (seqP d) d.size` as the `≺` calculus,
`δ = W^{-c} ≤ size^{-𝔠c}` (`Bandwidth`), constants `81`, `k = 2` (`offSq_le_gexRHS_blk`).  The
hypothesis `0 ≤ t n` of the shared list is not used here and is omitted. -/
theorem entry_bound_stochDom {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)) :
    GijOmegaSeq d E t c := by
  have hsz' := tendsto_size_of hsz
  unfold GijOmegaSeq
  refine of_det hsz' (fun n p ω => gexRHS_nonneg _ _ _ _ _)
    (Ξ := fun n Φ => {ω | (∀ u : OffPair (d.L n) (d.W n),
        ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeRowRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2) ∧
      (∀ u : OffPair (d.L n) (d.W n),
        ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeColRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)})
    ?_ (δ := fun n => (d.W n : ℝ) ^ (-c)) (C := fun _ => 81)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 𝔠 * c) (mul_pos h𝔠 hc)
    (eventually_W_rpow_neg_le d hsz hbw hc)
    (fun ε hε => hsz'.eventually (eventually_le_rpow 81 hε)) 2 ?_
  · intro τ' hτ'
    have h1 := highProb_of_perTime d (m := 2) (card_offPair_le d) hLrow hτ'
    have h2 := highProb_of_perTime d (m := 2) (card_offPair_le d) hLcol hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2)
      (Eventually.of_forall fun n ω hω => ⟨hω.1, hω.2⟩)
  · refine Eventually.of_forall fun n ω Φ hΦ1 hΦδ hmem => ?_
    rintro ⟨_, p, q⟩
    obtain ⟨hrow, hcol⟩ := hmem
    by_cases hg : ∀ i j : Idx (d.L n) (d.W n),
        llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤
          (d.W n : ℝ) ^ (-c)
    · rw [omegaInd_of_forall hg, one_mul]
      exact offSq_le_gexRHS_blk (d.three_le_L n) (Sizes.seqHflow_isHermitian d n (t n) ω)
        (by linarith [hE n, hκ]) (zt_im_ne_zero hκ (hE n) (ht1 n))
        (entryDom_goodEvent_of_llErr _ _ _ _ _ _ hg)
        (delta_le_half (Real.rpow_nonneg (Nat.cast_nonneg _) _) hΦ1 hΦδ) hΦ1 hΦδ
        (fun i j hij => hrow ⟨(i, j), hij⟩) (fun k j hkj => hcol ⟨(k, j), hkj⟩) p q
    · rw [omegaInd_of_not hg, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (gexRHS_nonneg _ _ _ _ _)

/-- **(4.2) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability.
Conclusion `GijSeq`. -/
theorem entry_bound_stochDom_of_highProb {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hΩ : HighProbAt (Sizes.seqP d) d.size (goodSet d E t c))
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)) :
    GijSeq d E t := by
  have hsz' := tendsto_size_of hsz
  have h := entry_bound_stochDom d hκ h𝔠 hsz hbw hE ht1 hc hLrow hLcol
  unfold GijOmegaSeq at h
  unfold GijSeq
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_indicator hsz'
    (Ωs := fun n _ => goodSet d E t c n)
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hΩ
      (Eventually.of_forall fun n ω hω _ => hω)) ?_
  have key : ∀ (n : ℕ) (p : Unit × BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n)) ω,
      omegaInd (d.L n) (d.W n) (E n) (t n) c (Sizes.seqHflow d n (t n) ω) *
        offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2 =
      (goodSet d E t c n).indicator
        (fun ω => offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2) ω :=
    fun n p ω => entryDom_omegaInd_mul_eq_indicator d E t c n ω
      (fun ω => offSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
  simp only [key] at h
  exact h

/-- **(4.2) without the indicator, under (`asGMc`)**: `AsGMcSeq d E t c` gives
`Ω(t, c/2)` with high probability (grid union bound over `(WL)⁴ = size²` pairs, then
`size^{𝔠c/2} ≤ W^{c/2}` by `Bandwidth`), and `entry_bound_stochDom_of_highProb` at `c/2` applies.
(In the one-dimensional argument `Ω` with high probability is a hypothesis.) -/
theorem entry_bound_stochDom_of_asGMc {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hAs : AsGMcSeq d E t c)
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)) :
    GijSeq d E t :=
  entry_bound_stochDom_of_highProb d hκ h𝔠 hsz hbw hE ht1 (half_pos hc)
    (entryDom_goodSet_highProb_of_asGMc d h𝔠 hsz hbw hc hAs) hLrow hLcol

end Entry

/-! ## 4. (4.3): the diagonal bound `GiiOmegaSeq`, `GiiSeq` -/

section Diag

variable (d : Sizes)

/-- **(4.3), `GiiOmegaSeq`** (`GiiGEX`, on `Ω(t,c)`): `1_{Ω(t,c)} |G_{pp} - m|² ≺
max_{a,b} |𝓛_{(+,-),(a,b)}|` from the large deviation bounds `hLrow`, `hLcol`, `hLquad` and
`|H_{pp}|² ≺ S_{pp}` (`hLdiag`), with the constant `4320 Kstab2 κ L_n²`
(`diagSq_le_maxLoopPM_blk`, `k = 2`) which is `≤ size^ε` eventually, and the absorption
`Kstab2 κ L_n W_n^{-c} ≤ 1/2` from `eventually_Kstab2_mul_rpow_le`. -/
theorem diag_bound_stochDom {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i)
      (fun n i ω => ldeQuadRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i))
    (hLdiag : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (fun n i _ => Sblk2 (d.L n) (d.W n) i i)) :
    GiiOmegaSeq d E t c := by
  have hsz' := tendsto_size_of hsz
  unfold GiiOmegaSeq
  refine of_det hsz' (fun n p ω => maxLoopPM_nonneg _ _ _)
    (Ξ := fun n Φ => {ω | ((∀ u : OffPair (d.L n) (d.W n),
        ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeRowRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2) ∧
      (∀ u : OffPair (d.L n) (d.W n),
        ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeColRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)) ∧
      (∀ i : BlockIndex (d.L n) (d.W n),
        ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
          (Sblk2 (d.L n) (d.W n)) (t n) i ≤
        Φ * ldeQuadRHS (Sblk2 (d.L n) (d.W n))
          (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i) ∧
      (∀ i : BlockIndex (d.L n) (d.W n),
        ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2 ≤ Φ * Sblk2 (d.L n) (d.W n) i i)})
    ?_ (δ := fun n => (d.W n : ℝ) ^ (-c)) (C := fun n => 4320 * Kstab2 κ (d.L n) ^ 2)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 𝔠 * c) (mul_pos h𝔠 hc)
    (eventually_W_rpow_neg_le d hsz hbw hc)
    (fun ε hε => eventually_const_kstab2_sq_le d hκ h𝔠 hsz hbw hε) 2 ?_
  · intro τ' hτ'
    have h1 := highProb_of_perTime d (m := 2) (card_offPair_le d) hLrow hτ'
    have h2 := highProb_of_perTime d (m := 2) (card_offPair_le d) hLcol hτ'
    have h3 := highProb_of_perTime d (m := 1) (fun n => (card_blockIndex d n).le.trans
      (by rw [pow_one])) hLquad hτ'
    have h4 := highProb_of_perTime d (m := 1) (fun n => (card_blockIndex d n).le.trans
      (by rw [pow_one])) hLdiag hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
          (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2) h3) h4)
      (Eventually.of_forall fun n ω hω => ⟨⟨hω.1.1.1, hω.1.1.2⟩, hω.1.2, hω.2⟩)
  · filter_upwards [eventually_Kstab2_mul_rpow_le d hκ h𝔠 hc hsz hbw] with n hKn ω Φ hΦ1 hΦδ hmem
    rintro ⟨_, p⟩
    obtain ⟨⟨hrow, hcol⟩, hquad, hdiag⟩ := hmem
    by_cases hg : ∀ i j : Idx (d.L n) (d.W n),
        llErrMat (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) i j ≤
          (d.W n : ℝ) ^ (-c)
    · rw [omegaInd_of_forall hg, one_mul]
      have h := diagSq_le_maxLoopPM_blk (d.three_le_L n)
        (Sizes.seqHflow_isHermitian d n (t n) ω) hκ (hE n) (ht0 n) (ht1 n)
        (entryDom_goodEvent_of_llErr _ _ _ _ _ _ hg)
        (delta_le_half (Real.rpow_nonneg (Nat.cast_nonneg _) _) hΦ1 hΦδ) hΦ1 hΦδ hKn
        (fun i j hij => hrow ⟨(i, j), hij⟩) (fun k j hkj => hcol ⟨(k, j), hkj⟩) hquad hdiag p
      calc _ ≤ _ := h
        _ = _ := by ring
    · rw [omegaInd_of_not hg, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
        (maxLoopPM_nonneg _ _ _)

/-- **(4.3) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability.
Conclusion `GiiSeq`. -/
theorem diag_bound_stochDom_of_highProb {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hΩ : HighProbAt (Sizes.seqP d) d.size (goodSet d E t c))
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i)
      (fun n i ω => ldeQuadRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i))
    (hLdiag : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (fun n i _ => Sblk2 (d.L n) (d.W n) i i)) :
    GiiSeq d E t := by
  have hsz' := tendsto_size_of hsz
  have h := diag_bound_stochDom d hκ h𝔠 hsz hbw hE ht0 ht1 hc hLrow hLcol hLquad hLdiag
  unfold GiiOmegaSeq at h
  unfold GiiSeq
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_indicator hsz'
    (Ωs := fun n _ => goodSet d E t c n)
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hΩ
      (Eventually.of_forall fun n ω hω _ => hω)) ?_
  have key : ∀ (n : ℕ) (p : Unit × BlockIndex (d.L n) (d.W n)) ω,
      omegaInd (d.L n) (d.W n) (E n) (t n) c (Sizes.seqHflow d n (t n) ω) *
        diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2 =
      (goodSet d E t c n).indicator
        (fun ω => diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2) ω :=
    fun n p ω => entryDom_omegaInd_mul_eq_indicator d E t c n ω
      (fun ω => diagSq (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2)
  simp only [key] at h
  exact h

/-- **(4.3) without the indicator, under (`asGMc`)** (Lemma `lem_GbEXP`): as
`entry_bound_stochDom_of_asGMc`, through `Ω(t, c/2)`.  Conclusion `GiiSeq`. -/
theorem diag_bound_stochDom_of_asGMc {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hAs : AsGMcSeq d E t c)
    (hLrow : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeRowLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => OffPair (d.L n) (d.W n))
      (fun n u ω => ldeColLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i)
      (fun n i ω => ldeQuadRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i))
    (hLdiag : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ‖blockMat (Sizes.seqHflow d n (t n) ω) i i‖ ^ 2)
      (fun n i _ => Sblk2 (d.L n) (d.W n) i i)) :
    GiiSeq d E t :=
  diag_bound_stochDom_of_highProb d hκ h𝔠 hsz hbw hE ht0 ht1 (half_pos hc)
    (entryDom_goodSet_highProb_of_asGMc d h𝔠 hsz hbw hc hAs) hLrow hLcol hLquad hLdiag

end Diag

end RBM.Green
