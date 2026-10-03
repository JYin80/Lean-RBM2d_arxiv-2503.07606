/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.FarEntry
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The good event for the replacement step on the finite model

Paper: arXiv:2503.07606, Section 7: "`X^{i,j}` ... entries `O_≺(S_ij^{1/2})`" (proof of
`clt-lemma`), `Gt_bound_flow` as used in the proof of `clt-lemma` (`clt-gij-bound`),
`Eq:Gdecay_w` and `GijGEX` as used in the proof of `clt-lemma`.

The definitions `HClt`, `CltCoordTail`, `CltGmaxWhp`, `CltFarEntryWhp` are stated below.

Results (namespace `RBM.Evol`):
* `cltCoord_tail : CltCoordTail d` (E1): every real coordinate exceeds `W^{-1/2}` with probability
  `≤ 2 exp(-5W/2) ≤ N^{-D}`, eventually; with variance `≤ (5W²)⁻¹` and threshold
  `W^{-1/2}` on the finite model `P L W`.
* `cltGmax_whp : CltGmaxWhp d` (E2): under `HClt`, all entries of `G_u(±)` are `≤ 2` outside an
  event of probability `≤ N^{-D}`: `Step2LocalPT` (restricted to the section `u n ∈ [s₀ n, t₀ n]`,
  exponent `D + 2`), `M_u ≥ Im m N^{min(2𝔠,δ)}` (`scaleM_etaT_of_range`, `scaleM_anti_ratio`),
  `|m| = 1` (`normSqSpectralMOne`), the union bound over the `N²` pairs, and
  `G(-)_{xy} = conj G(+)_{yx}` (`Gsig_conjTranspose`).
* `cltFarEntry_whp : CltFarEntryWhp d` (E3): under `HClt`, far entries of `G_u(±)` are `≤ W^{-D'}`
  outside an event of probability `≤ N^{-D}`: `farEntryDecayPT_clt` at `(τ', D' + 1)`, the section
  `u n ∈ [s₀ n, u n]`, exponent `D + 2`, the identification of `greenBlk` with `gEntry`, the union
  bound and the transpose.

The transfer from the common product space `seqP d` to the finite model `P L W` is
`Sizes.seqP_map_slice` and `Measure.map_apply`; it needs the events to be measurable, which is the
private matrix-inverse measurability.
-/

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ## The good event (per size `n`, on `P (d.L n) (d.W n)`) -/

section Good

variable (d : Sizes)

/-- The hypothesis list `H_clt`: the part of the binders of `CltCase1Prec` before the
coefficient bound, bundled. -/
def HClt (κ 𝔠 δ : ℝ) (E s₀ t₀ u t : ℕ → ℝ) : Prop :=
  0 < κ ∧ 0 < 𝔠 ∧ 0 < δ ∧ (∀ n, |E n| ≤ 2 - κ) ∧ (∀ n, 0 ≤ s₀ n) ∧ (∀ n, s₀ n ≤ u n) ∧
    (∀ n, u n ≤ t₀ n) ∧ (∀ n, u n ≤ t n) ∧ (∀ n, t n < 1) ∧ SizeTendsto d ∧
    Bandwidth d 𝔠 ∧ RangeCond d δ t ∧ Step2LocalPT d E s₀ t₀ ∧ Step2DecayPT d E s₀ t₀ ∧
    RBM.Green.GbEXPHypV3 d (κ / 2) 𝔠 δ

/-- **E1: coordinate tails** ("`X^{i,j}` … entries `O_≺(S_ij^{1/2})`", proof of `clt-lemma`).
Every real coordinate exceeds `W^{-1/2}` with probability `≤ N^{-D}`, eventually
(`gvar ≤ (5W²)⁻¹`, Gaussian tail `2exp(-5W/2)`, `W ≥ N^𝔠`). -/
def CltCoordTail : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → SizeTendsto d → Bandwidth d 𝔠 →
    ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ c : Coord (d.L n) (d.W n),
      P (d.L n) (d.W n) {ω | (d.W n : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **E2: bounded entries** (`Gt_bound_flow` as used in `clt-gij-bound`).  Under `H_clt`, all
entries of `G_u(±)` at `Hflow … (u n) ω` are `≤ 2` outside an event of probability `≤ N^{-D}`,
eventually.  Inputs: `Step2LocalPT` (restricted to `u n ∈ [s₀ n, t₀ n]`), `RangeCond`,
`Bandwidth` (the lower bound `M_u ≥ 𝔪 N^{c₀}`), `normSqSpectralMOne`, the union bound over `N²`
entries, and `G(-)_{xy} = conj G(+)_{yx}`. -/
def CltGmaxWhp : Prop :=
  ∀ (κ 𝔠 δ : ℝ) (E s₀ t₀ u t : ℕ → ℝ), HClt d κ 𝔠 δ E s₀ t₀ u t →
    ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop,
      P (d.L n) (d.W n) {ω | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
          2 < ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **E3: far entries** (`Eq:Gdecay_w` + `GijGEX` as used in the proof of `clt-lemma`; the far
bounds of `clt-ibp-bound1`, `clt-ibp-bound3`).  Under `H_clt`, every entry of `G_u(±)` whose
blocks are at distance `≥ W^{τ'} ℓ_u` is `≤ W^{-D'}` outside an event of probability `≤ N^{-D}`,
eventually.  Input: `farEntryDecayPT_clt` (conclusion `FarEntryDecayPT d E s₀ u`) at
the time `u n ∈ [s₀ n, u n]`, `blockMat`/`splitEquiv`, `σ = false` by transpose, the union bound. -/
def CltFarEntryWhp : Prop :=
  ∀ (κ 𝔠 δ : ℝ) (E s₀ t₀ u t : ℕ → ℝ), HClt d κ 𝔠 δ E s₀ t₀ u t →
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop,
      P (d.L n) (d.W n) {ω | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
          (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
              (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) x).1 -
                (splitEquiv (d.L n) (d.W n) y).1) : ℝ) ∧
            (d.W n : ℝ) ^ (-D') <
              ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

end Good


/-! ## Private helpers -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A` (the index type is an arbitrary finite type). -/
private theorem cltg_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
    (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- The entrywise form of the measurability of the matrix inverse. -/
private theorem cltg_measurable_inv_entries {A : Θ → Matrix ν ν ℂ}
    (hA : ∀ k l, Measurable fun ω => A ω k l) (k l : ν) :
    Measurable fun ω => (A ω)⁻¹ k l :=
  cltg_measurable_matrix_inv_apply
    (Measurable.of_eval fun a => Measurable.of_eval fun b => hA a b) k l

end MatrixMeasurable

section Helpers

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The entries `G_u(σ)_{xy}` of the resolvent of `H_u(ω)` are measurable in `ω`. -/
private theorem cltg_gEntry_meas (E s u : ℝ) (σ : Bool) (x y : Idx L W) :
    Measurable fun ω : Ω L W => gEntry L W E s (Hflow L W u ω) σ x y := by
  unfold gEntry
  refine cltg_measurable_inv_entries (A := fun ω : Ω L W =>
    Hflow L W u ω - (if σ then spectralZ E s else (starRingEnd ℂ) (spectralZ E s)) •
      (1 : Matrix (Idx L W) (Idx L W) ℂ)) (fun k l => ?_) x y
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (measurable_Hflow L W u k l).sub measurable_const

/-- The entries `|(G_u - m)_{xy}|` are measurable in `ω`. -/
private theorem cltg_llErr_meas (E u : ℝ) (x y : Idx L W) :
    Measurable fun ω : Ω L W => llErrMat L W E u (Hflow L W u ω) x y := by
  unfold llErrMat
  refine Measurable.norm ?_
  refine Measurable.sub ?_ measurable_const
  refine cltg_measurable_inv_entries (A := fun ω : Ω L W =>
    Hflow L W u ω - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)) (fun k l => ?_) x y
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (measurable_Hflow L W u k l).sub measurable_const

end Helpers

/-- The transfer from the common product space `seqP d` to the finite model `P L W`, for a
measurable event. -/
private theorem cltg_P_le_of_seqP (d : Sizes) (n : ℕ) {S : Set (Ω (d.L n) (d.W n))}
    (hS : MeasurableSet S) {b : ℝ≥0∞} (h : Sizes.seqP d (Sizes.slice d n ⁻¹' S) ≤ b) :
    P (d.L n) (d.W n) S ≤ b := by
  rw [← Sizes.seqP_map_slice d n, Measure.map_apply (Sizes.measurable_slice d n) hS]
  exact h

/-- Finite union bound. -/
private theorem cltg_union_le {α I : Type*} [MeasurableSpace α] (μ : Measure α) [Fintype I]
    (S : I → Set α) (b : ℝ≥0∞) (h : ∀ i, μ (S i) ≤ b) :
    μ (⋃ i, S i) ≤ (Fintype.card I : ℝ≥0∞) * b := by
  calc μ (⋃ i, S i) ≤ ∑ i, μ (S i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : I, b := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card I : ℝ≥0∞) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem cltg_size_pos (d : Sizes) (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.W n * d.L n := Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega)
  have : 0 < d.size n := by
    unfold Sizes.size; exact pow_pos h1 2
  exact_mod_cast this

private theorem cltg_card_Z2 (m : ℕ) [NeZero m] : (Fintype.card (Z2 m) : ℝ) = (m : ℝ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, pow_two]

private theorem cltg_card_Idx (d : Sizes) (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  change (Fintype.card (Z2 (d.W n * d.L n)) : ℝ) = _
  rw [cltg_card_Z2]
  simp [Sizes.size]

/-- `#(I × I) · N^{-(D+2)} = N^{-D}` for `I = Idx`, `N = size n`. -/
private theorem cltg_pairs_mul (d : Sizes) (n : ℕ) (D : ℝ) :
    (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ≥0∞) *
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) =
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  have hN := cltg_size_pos d n
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Fintype.card_prod]
  congr 1
  push_cast
  rw [cltg_card_Idx, ← pow_two]
  have : ((d.size n : ℕ) : ℝ) ^ (2 : ℕ) = ((d.size n : ℕ) : ℝ) ^ ((2 : ℕ) : ℝ) :=
    (Real.rpow_natCast _ 2).symm
  rw [this, ← Real.rpow_add hN]
  congr 1
  push_cast; ring



/-! ## E1: the coordinate tail -/

section CoordTail

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Every coordinate variance is at most `(5 W²)⁻¹`. -/
private theorem cltg_gvar_le (c : Coord L W) : (gvar L W c : ℝ) ≤ ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹ := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h5 : ((5 : ℝ)⁻¹ * ((W : ℝ)⁻¹) ^ 2) = ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹ := by
    rw [mul_inv, inv_pow]
  have hs : svar L W c.1 c.2.1 ≤ ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹ := by
    unfold svar
    split_ifs
    · exact h5.le
    · positivity
  have h0 := svar_nonneg L W c.1 c.2.1
  change (if c.1 = c.2.1 then svar L W c.1 c.2.1 else svar L W c.1 c.2.1 / 2) ≤ _
  split_ifs <;> linarith

/-- The Gaussian tail of one coordinate on the finite model:
`P(W^{-1/2} < |ω_c|) ≤ 2 exp(-5W/2)` (variance at most `(5 W²)⁻¹`), for every size. -/
private theorem cltg_coord_tail_finite (c : Coord L W) :
    P L W {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
      ENNReal.ofReal (2 * Real.exp (-(5 * (W : ℝ)) / 2)) := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set B : ℝ := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hBdef
  have hB : 0 ≤ B := Real.rpow_nonneg hW.le _
  have hB2 : B ^ 2 = (W : ℝ)⁻¹ := by
    rw [hBdef, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num [Real.rpow_neg_one]
  have hmeas : Measurable (fun ω : Ω L W => ω c) := measurable_pi_apply c
  have hv0 : (0 : ℝ) ≤ ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹ := by positivity
  let v : ℝ≥0 := ⟨((5 : ℝ) * (W : ℝ) ^ 2)⁻¹, hv0⟩
  have hsg : HasSubgaussianMGF (fun ω : Ω L W => ω c) v (P L W) := by
    rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable]
    have hmap : (P L W).map (fun ω : Ω L W => ω c) = gaussianReal 0 (gvar L W c) :=
      Measure.infinitePi_map_eval _ c
    rw [hmap]
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.2
    have h1 := cltg_gvar_le (L := L) (W := W) c
    have h2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have hvc : (v : ℝ) = ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹ := rfl
    simp only [zero_mul, zero_add]
    rw [hvc]
    nlinarith
  have h1 := hsg.measure_ge_le hB
  have h2 := hsg.neg.measure_ge_le hB
  have hexp : -B ^ 2 / (2 * (v : ℝ)) = -(5 * (W : ℝ)) / 2 := by
    change -B ^ 2 / (2 * ((5 : ℝ) * (W : ℝ) ^ 2)⁻¹) = _
    rw [hB2]
    field_simp
  rw [hexp] at h1 h2
  have hsub : {ω : Ω L W | B < |ω c|} ⊆
      {ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω L W => ω c)) ω} := by
    intro ω hω
    have hω' : B < |ω c| := hω
    rcases le_abs.1 (le_of_lt hω') with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hf1 : P L W {ω | B ≤ ω c} ≤ ENNReal.ofReal (Real.exp (-(5 * (W : ℝ)) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h1
  have hf2 : P L W {ω | B ≤ (-(fun ω : Ω L W => ω c)) ω} ≤
      ENNReal.ofReal (Real.exp (-(5 * (W : ℝ)) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2
  have hp : (0 : ℝ) ≤ Real.exp (-(5 * (W : ℝ)) / 2) := (Real.exp_pos _).le
  calc P L W {ω | B < |ω c|}
      ≤ P L W ({ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω L W => ω c)) ω}) := measure_mono hsub
    _ ≤ P L W {ω | B ≤ ω c} + P L W {ω | B ≤ (-(fun ω : Ω L W => ω c)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(5 * (W : ℝ)) / 2)) +
          ENNReal.ofReal (Real.exp (-(5 * (W : ℝ)) / 2)) := add_le_add hf1 hf2
    _ = ENNReal.ofReal (2 * Real.exp (-(5 * (W : ℝ)) / 2)) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf

end CoordTail

/-- `2 exp(-5W/2) ≤ N^{-D}` eventually, from `W ≥ N^𝔠` and `N → ∞`. -/
private theorem cltg_tail_eventually (d : Sizes) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hN : SizeTendsto d)
    (hW : Bandwidth d 𝔠) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-(5 * (d.W n : ℝ)) / 2) ≤ ((d.size n : ℕ) : ℝ) ^ (-D) := by
  have hx : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  have h1 : Tendsto (fun x : ℝ => x ^ (D / 𝔠) * Real.exp (-(5 / 2) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D / 𝔠) (5 / 2) (by norm_num)
  filter_upwards [(h1.comp hx).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), hW,
    hN.eventually_gt_atTop 0] with n hn hWn hN0
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := hN0
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := N ^ 𝔠 with hxdef
  have hND : x ^ (D / 𝔠) = N ^ D := by
    rw [hxdef, ← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
  have hNDpos : 0 < N ^ D := Real.rpow_pos_of_pos hNpos D
  have hexp : Real.exp (-(5 * (d.W n : ℝ)) / 2) ≤ Real.exp (-(5 / 2) * x) := by
    apply Real.exp_le_exp.2
    linarith
  have hexp0 : 0 < Real.exp (-(5 / 2) * x) := Real.exp_pos _
  have hcomb : 2 * Real.exp (-(5 / 2) * x) * N ^ D ≤ 1 := by
    have : N ^ D * Real.exp (-(5 / 2) * x) < 1 / 2 := by
      have hn' : x ^ (D / 𝔠) * Real.exp (-(5 / 2) * x) < 1 / 2 := hn
      rwa [hND] at hn'
    nlinarith
  rw [Real.rpow_neg hNpos.le]
  calc 2 * Real.exp (-(5 * (d.W n : ℝ)) / 2) ≤ 2 * Real.exp (-(5 / 2) * x) := by linarith
    _ = 2 * Real.exp (-(5 / 2) * x) * N ^ D * (N ^ D)⁻¹ := by field_simp
    _ ≤ 1 * (N ^ D)⁻¹ := by gcongr
    _ = (N ^ D)⁻¹ := one_mul _

/-- **E1.**  Every real coordinate exceeds `W^{-1/2}` with probability at most `N^{-D}`,
eventually. -/
theorem cltCoord_tail (d : Sizes) : CltCoordTail d := by
  intro 𝔠 h𝔠 hN hW D hD
  filter_upwards [cltg_tail_eventually d h𝔠 hN hW D] with n hn c
  exact (cltg_coord_tail_finite c).trans (ENNReal.ofReal_le_ofReal hn)

/-! ## E2 and E3: common deterministic facts -/

section Transpose

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `G(-)_{xy} = conj G(+)_{yx}` for a Hermitian `M`, in norm. -/
private theorem cltg_norm_gEntry_false (E s : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (x y : Idx L W) :
    ‖gEntry L W E s M false x y‖ = ‖gEntry L W E s M true y x‖ := by
  have h := Gsig_conjTranspose hM (spectralZ E s) true
  have h2 : gEntry L W E s M false x y = star (gEntry L W E s M true y x) := by
    have h3 := congrFun (congrFun h x) y
    rw [Matrix.conjTranspose_apply] at h3
    exact h3.symm
  rw [h2, norm_star]

/-- `G(σ)` at any sign is bounded by `G(+)` at the transposed pair. -/
private theorem cltg_exists_true {M : Matrix (Idx L W) (Idx L W) ℂ} (E s : ℝ)
    (hM : M.IsHermitian) {r : ℝ} {P : Idx L W → Idx L W → Prop}
    (hsym : ∀ x y, P x y → P y x)
    (h : ∃ (σ : Bool) (x y : Idx L W), P x y ∧ r < ‖gEntry L W E s M σ x y‖) :
    ∃ x y : Idx L W, P x y ∧ r < ‖gEntry L W E s M true x y‖ := by
  obtain ⟨σ, x, y, hP, hr⟩ := h
  cases σ
  · rw [cltg_norm_gEntry_false E s hM] at hr
    exact ⟨y, x, hsym x y hP, hr⟩
  · exact ⟨x, y, hP, hr⟩

end Transpose

/-- The arithmetic of the exponents of E2: `N^{c₀/4} M^{-1/2} ≤ 1` once `M ≥ m N^{c₀}` and
`N^{c₀/2} ≥ m⁻¹`. -/
private theorem cltg_scale_le_one {N M m c₀ : ℝ} (hN : 1 ≤ N) (hm : 0 < m)
    (hM : m * N ^ c₀ ≤ M) (hbig : m⁻¹ ≤ N ^ (c₀ / 2)) :
    N ^ (c₀ / 4) * M⁻¹ ^ ((1 : ℝ) / 2) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : 0 < N ^ c₀ := Real.rpow_pos_of_pos hN0 _
  have hNh : 0 < N ^ (c₀ / 2) := Real.rpow_pos_of_pos hN0 _
  have hM0 : 0 < M := lt_of_lt_of_le (mul_pos hm hNc) hM
  have hsplit : N ^ c₀ = N ^ (c₀ / 2) * N ^ (c₀ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have h1 : 1 ≤ m * N ^ (c₀ / 2) := by
    have := mul_le_mul_of_nonneg_left hbig hm.le
    rwa [mul_inv_cancel₀ hm.ne'] at this
  have hM' : N ^ (c₀ / 2) ≤ M := by
    calc N ^ (c₀ / 2) = 1 * N ^ (c₀ / 2) := (one_mul _).symm
      _ ≤ (m * N ^ (c₀ / 2)) * N ^ (c₀ / 2) := mul_le_mul_of_nonneg_right h1 hNh.le
      _ = m * N ^ c₀ := by rw [hsplit]; ring
      _ ≤ M := hM
  have h2 : (N ^ (c₀ / 2)) ^ ((1 : ℝ) / 2) ≤ M ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hNh.le hM' (by norm_num)
  have h3 : (N ^ (c₀ / 2)) ^ ((1 : ℝ) / 2) = N ^ (c₀ / 4) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  rw [h3] at h2
  have hMh : 0 < M ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hM0 _
  rw [Real.inv_rpow hM0.le]
  calc N ^ (c₀ / 4) * (M ^ ((1 : ℝ) / 2))⁻¹ ≤ M ^ ((1 : ℝ) / 2) * (M ^ ((1 : ℝ) / 2))⁻¹ := by
        gcongr
    _ = 1 := mul_inv_cancel₀ hMh.ne'

/-- Lower bound for `Im m^{(E)}` from `|E| ≤ 2 - κ`. -/
private theorem cltg_im_lower {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have habs := abs_le.mp hE
  have hsq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hsq
  linarith

/-- **E2.**  Under `HClt`, all entries of `G_u(±)` are at most `2` outside an event of
probability at most `N^{-D}`, eventually. -/
theorem cltGmax_whp (d : Sizes) : CltGmaxWhp d := by
  intro κ 𝔠 δ E s₀ t₀ u t h D hD
  obtain ⟨hκ, h𝔠, hδ, hE, hs₀, hsu, hut₀, hut, ht, hN, hW, hR, hLoc, hDec, hV3⟩ := h
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  set c₀ : ℝ := min (2 * 𝔠) δ with hc₀
  have hc₀pos : 0 < c₀ := lt_min (by linarith) hδ
  set m : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hmdef
  have hm : 0 < m := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  -- the Step 2 input at the section `u`
  have hu_mem : ∀ n, u n ∈ Set.Icc (s₀ n) (t₀ n) := fun n => ⟨hsu n, hut₀ n⟩
  have hLoc' := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size (s := s₀) (t := t₀)
    (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n => ⟨(0, 0)⟩)
    (fun n v x ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) x.1 x.2)
    (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ ((1 : ℝ) / 2))
    hLoc u hu_mem
  have hLoc2 := hLoc' (c₀ / 4) (by linarith) (D + 2) (by linarith)
  -- the size threshold
  have hbig : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (c₀ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hN
  filter_upwards [hLoc2, hW, hR, hbig.eventually_ge_atTop m⁻¹, hN.eventually_ge_atTop 1]
    with n hn hWn hRn hbn hN1
  have hE2 : |E n| < 2 := by have := hE n; linarith
  have hL1 : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hNpos := cltg_size_pos d n
  obtain ⟨hsc, -⟩ := scaleM_etaT_of_range (L := d.L n) (W := d.W n) (E := E n) (c := 𝔠)
    (τ := δ) (t := t n) hL1 hW1 hE2 h𝔠 hδ (ht n) hWn hRn
  have hanti := (scaleM_anti_ratio (L := d.L n) (W := d.W n) (E := E n) hL1 hE2 (hut n)
    (ht n)).1
  have him := cltg_im_lower (hE n)
  have hMlow : m * ((d.size n : ℕ) : ℝ) ^ c₀ ≤ scaleM (d.L n) (d.W n) (E n) (u n) :=
    calc m * ((d.size n : ℕ) : ℝ) ^ c₀
        ≤ (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ c₀ :=
          mul_le_mul_of_nonneg_right him (Real.rpow_nonneg hNpos.le _)
      _ ≤ scaleM (d.L n) (d.W n) (E n) (t n) := hsc
      _ ≤ scaleM (d.L n) (d.W n) (E n) (u n) := hanti
  have hζ : ((d.size n : ℕ) : ℝ) ^ (c₀ / 4) *
      (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ ((1 : ℝ) / 2) ≤ 1 :=
    cltg_scale_le_one hN1 hm hMlow hbn
  have hmnorm : ‖spectralM (E n)‖ ≤ 1 := by
    have h1 := normSqSpectralMOne (E n) hE2.le
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (spectralM (E n))]
  let S : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) → Set (Ω (d.L n) (d.W n)) := fun p =>
    {ω | ((d.size n : ℕ) : ℝ) ^ (c₀ / 4) * (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ^ ((1 : ℝ) / 2) <
      llErrMat (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) p.1 p.2}
  have hSmeas : ∀ p, MeasurableSet (S p) := fun p =>
    measurableSet_lt measurable_const (cltg_llErr_meas (E n) (u n) p.1 p.2)
  have hsub : {ω : Ω (d.L n) (d.W n) | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
      2 < ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖} ⊆
      ⋃ p, S p := by
    intro ω hω
    obtain ⟨x, y, -, hxy⟩ := cltg_exists_true (P := fun _ _ => True) (E n) (u n)
      (Hflow_isHermitian (d.L n) (d.W n) (u n) ω) (fun _ _ _ => trivial)
      (by obtain ⟨σ, x, y, hxy⟩ := hω; exact ⟨σ, x, y, trivial, hxy⟩)
    refine Set.mem_iUnion.2 ⟨(x, y), ?_⟩
    change _ < llErrMat (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) x y
    have hg : gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) true x y =
        (Hflow (d.L n) (d.W n) (u n) ω - spectralZ (E n) (u n) •
          (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ x y := rfl
    rw [hg] at hxy
    unfold llErrMat
    have hite : ‖(if x = y then spectralM (E n) else 0)‖ ≤ 1 := by
      split_ifs
      · exact hmnorm
      · simp
    have := norm_sub_norm_le ((Hflow (d.L n) (d.W n) (u n) ω - spectralZ (E n) (u n) •
          (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))⁻¹ x y)
        (if x = y then spectralM (E n) else 0)
    linarith
  calc P (d.L n) (d.W n) {ω | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
          2 < ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖}
      ≤ P (d.L n) (d.W n) (⋃ p, S p) := measure_mono hsub
    _ ≤ (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) :=
        cltg_union_le _ S _ fun p => cltg_P_le_of_seqP d n (hSmeas p) (hn ((), p))
    _ = ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := cltg_pairs_mul d n D

/-! ## E3: far entries -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem cltg_zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem cltg_zdist2_comm (a b : Z2 L) : zdist2 L (a - b) = zdist2 L (b - a) := by
  have h : zdist2 L (-(a - b)) = zdist2 L (a - b) := by
    simp only [zdist2, Prod.fst_neg, Prod.snd_neg, cltg_zdist_neg]
  rw [← h, neg_sub]

end Dist

/-- The block-level resolvent at block indices is the fine-lattice resolvent entry. -/
private theorem cltg_greenBlk_eq {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (x y : Idx L W) :
    greenBlk L W E u M true (splitEquiv L W x) (splitEquiv L W y) =
      gEntry L W E u M true x y := by
  have h1 : blockMat M - spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
        (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext p q
    simp [blockMat, Matrix.one_apply]
  unfold greenBlk Gsig green gEntry
  simp only [ite_true]
  rw [h1, Matrix.inv_submatrix_equiv]
  simp

/-- **E3.**  Under `HClt`, far entries of `G_u(±)` are at most `W^{-D'}` outside an
event of probability at most `N^{-D}`, eventually. -/
theorem cltFarEntry_whp (d : Sizes) : CltFarEntryWhp d := by
  intro κ 𝔠 δ E s₀ t₀ u t h τ' hτ' D' hD' D hD
  obtain ⟨hκ, h𝔠, hδ, hE, hs₀, hsu, hut₀, hut, ht, hN, hW, hR, hLoc, hDec, hV3⟩ := h
  have hF := farEntryDecayPT_clt d hκ h𝔠 hδ hE hs₀ hsu hut₀ hut ht hN hW hR hLoc hDec hV3
  have hF' := hF τ' hτ' (D' + 1) (by linarith)
  have hu_mem : ∀ n, u n ∈ Set.Icc (s₀ n) (u n) := fun n => ⟨hsu n, le_rfl⟩
  have hF2 := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size (s := s₀) (t := u)
    (V := fun n => BlockIndex (d.L n) (d.W n) × BlockIndex (d.L n) (d.W n))
    (fun n => ⟨((0, (⟨0, d.W_pos n⟩, ⟨0, d.W_pos n⟩)), (0, (⟨0, d.W_pos n⟩, ⟨0, d.W_pos n⟩)))⟩)
    (fun n v p ω => ‖greenBlk (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) true p.1 p.2‖ *
      (if (d.W n : ℝ) ^ τ' * ellT (d.L n) v ≤ (zdist2 (d.L n) (p.1.1 - p.2.1) : ℝ)
        then 1 else 0))
    (fun n _ _ _ => (d.W n : ℝ) ^ (-(D' + 1)))
    hF' u hu_mem
  have hF3 := hF2 𝔠 h𝔠 (D + 2) (by linarith)
  filter_upwards [hF3, hW] with n hn hWn
  have hNpos := cltg_size_pos d n
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  let far : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → Prop := fun x y =>
    (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
      (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) x).1 -
        (splitEquiv (d.L n) (d.W n) y).1) : ℝ)
  let B : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) → Set (Ω (d.L n) (d.W n)) := fun p =>
    {ω | far p.1 p.2 ∧ (d.W n : ℝ) ^ (-D') <
      ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) true p.1 p.2‖}
  have hBmeas : ∀ p, MeasurableSet (B p) := fun p =>
    MeasurableSet.inter (MeasurableSet.const (far p.1 p.2))
      (measurableSet_lt measurable_const
        (cltg_gEntry_meas (E n) (u n) (u n) true p.1 p.2).norm)
  have hsym : ∀ x y, far x y → far y x := by
    intro x y hxy
    change _ ≤ (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) y).1 -
        (splitEquiv (d.L n) (d.W n) x).1) : ℝ)
    rw [cltg_zdist2_comm]
    exact hxy
  have hsub : {ω : Ω (d.L n) (d.W n) | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
      (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
          (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) x).1 -
            (splitEquiv (d.L n) (d.W n) y).1) : ℝ) ∧
        (d.W n : ℝ) ^ (-D') <
          ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖} ⊆
      ⋃ p, B p := by
    intro ω hω
    obtain ⟨x, y, hf, hg⟩ := cltg_exists_true (P := far) (E n) (u n)
      (Hflow_isHermitian (d.L n) (d.W n) (u n) ω) hsym hω
    exact Set.mem_iUnion.2 ⟨(x, y), hf, hg⟩
  have hpre : ∀ p, Sizes.seqP d (Sizes.slice d n ⁻¹' B p) ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) := by
    intro p
    refine le_trans (measure_mono ?_)
      (hn ((), (splitEquiv (d.L n) (d.W n) p.1, splitEquiv (d.L n) (d.W n) p.2)))
    intro ω hω
    obtain ⟨hf, hg⟩ := hω
    change ((d.size n : ℕ) : ℝ) ^ 𝔠 * (d.W n : ℝ) ^ (-(D' + 1)) <
      ‖greenBlk (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) true
        (splitEquiv (d.L n) (d.W n) p.1) (splitEquiv (d.L n) (d.W n) p.2)‖ *
        (if (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
          (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) p.1).1 -
            (splitEquiv (d.L n) (d.W n) p.2).1) : ℝ) then 1 else 0)
    have hone : (if (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
        (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) p.1).1 -
          (splitEquiv (d.L n) (d.W n) p.2).1) : ℝ) then (1 : ℝ) else 0) = 1 := by
      split_ifs <;> rfl
    rw [hone, mul_one, cltg_greenBlk_eq]
    calc ((d.size n : ℕ) : ℝ) ^ 𝔠 * (d.W n : ℝ) ^ (-(D' + 1))
        ≤ (d.W n : ℝ) * (d.W n : ℝ) ^ (-(D' + 1)) :=
          mul_le_mul_of_nonneg_right hWn (Real.rpow_nonneg hW0.le _)
      _ = (d.W n : ℝ) ^ (-D') := by
          rw [← Real.rpow_one_add' hW0.le (by linarith)]
          congr 1; ring
      _ < _ := hg
  calc P (d.L n) (d.W n) {ω | ∃ (σ : Bool) (x y : Idx (d.L n) (d.W n)),
          (d.W n : ℝ) ^ τ' * ellT (d.L n) (u n) ≤
              (zdist2 (d.L n) ((splitEquiv (d.L n) (d.W n) x).1 -
                (splitEquiv (d.L n) (d.W n) y).1) : ℝ) ∧
            (d.W n : ℝ) ^ (-D') <
              ‖gEntry (d.L n) (d.W n) (E n) (u n) (Hflow (d.L n) (d.W n) (u n) ω) σ x y‖}
      ≤ P (d.L n) (d.W n) (⋃ p, B p) := measure_mono hsub
    _ ≤ (Fintype.card (Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) : ℝ≥0∞) *
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) :=
        cltg_union_le _ B _ fun p => cltg_P_le_of_seqP d n (hBmeas p) (hpre p)
    _ = ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := cltg_pairs_mul d n D

end RBM.Evol
