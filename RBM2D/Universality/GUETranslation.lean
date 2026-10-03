/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Step1RegularityGUE
import RBM2D.Universality.Step1Band
import RBM2D.Universality.Step1Cond
import RBM2D.Universality.Pins
import RBM2D.Endpoints

/-!
# The GUE translation and the reduction `Infty1Row`

Paper: arXiv:2503.07606, the proof of `Thm: B_Univ` (`1infyuniv` is proved in the paragraph after
`univ-main` from `MR:locSC` and [32] Theorem 2.2); [32] Definition 2.1 and Theorem 2.2 as stated in
`Universality/Pins.lean` (`IsRegular32`, `IsFreeConv32`, `L32`).  `GUELocal` is not in the paper
(see `Pins.lean`).

Contents.
* `GUETranslation` (the GUE side of `1infyuniv`) and `GUETranslationRow` (`GUETranslation` from
  the good event `GUEGoodHighProb`).
* `guetranslationRow`: the GUE translation proved from `L32`, `GUELocal` and the good event
  `GUEGoodAt` (`Universality/Step1RegularityGUE.lean`), following `Step1Band.lean`: the private
  helpers of `Step1Band.lean` that do not mention the band carrier are copied under the prefix
  `GUETranslation_`; `core`, `uniform` and the assembly are adapted to the GUE carrier
  `Ω (d.L n) (d.W n)` under `gueP`.
* `infty1Row_of_translation` (`step1Band` plus `GUETranslation`), `infty1Row_of_pins`, and
  `infty1Row : Infty1Row` (`L32`, `locSC`, `GUELocal` are hypotheses inside the reduction
  statement).

The GUE side of `1infyuniv` is proved with an internal time `τs` independent of `τ_U`, without
`τs ≤ 𝔠`.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ## The statements `GUETranslation`, `GUETranslationRow` -/

/-- **Output of S8b**: for a bulk energy `E`, the GUE `k`-point functional at `E` is asymptotically
the
GUE functional at energy `0` with the test function dilated by `ρ_sc(0)/ρ_sc(E)`.  The carrier is
the GUE alone (`gueP`), so the statement needs no `Admissible`, no `locSC`, no `τ_U`; the internal
time `τs` of its proof is its own. -/
def GUETranslation : Prop :=
  L32 → GUELocal →
    ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
        ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
          Tendsto (fun n =>
            (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
                (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues ∂(gueP (d.L n) (d.W n))) -
            (∫ ω, kPoint k O E (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
                ∂(gueP (d.L n) (d.W n))))
            atTop (𝓝 0)

/-- **`GUETranslation` from the good event** (proved below as `guetranslationRow`).  It takes
`GUEGoodHighProb` as a hypothesis. -/
def GUETranslationRow : Prop := GUEGoodHighProb → GUETranslation

/-! ## The GUE translation (`GUETranslationRow`)

The private helpers of `Step1Band.lean` that do not mention the band carrier (`SeqΩ d`, `seqP d`,
`vOU`) are copied under the prefix `GUETranslation_`; the carrier-bound `core`, `uniform`
and the assembly are adapted to the GUE carrier `Ω (d.L n) (d.W n)` under `gueP`, with `vOU`
replaced by `vGUE`, the good event by `GUEGoodAt` (the statement `GUEGoodHighProb` is the
hypothesis of the row), the conditioning by `Step1Cond_gueMatPairing_eq_integral`, and the
diagonal argument by a version for the dependent carriers `Ω (d.L n) (d.W n)`.  `GUELocal` enters
only through `GUETranslation_gue_count` (`Step1Band_gue_count`, `Step1Band.lean`). -/

private theorem GUETranslation_card (d : Sizes) (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  simp [Sizes.size, Idx, Z2, Fintype.card_prod, ZMod.card, sq, mul_comm]

private theorem GUETranslation_card_real (d : Sizes) (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  rw [GUETranslation_card]

private theorem GUETranslation_size_ge_nine (d : Sizes) (n : ℕ) : 9 ≤ d.size n := by
  have h3 : 3 ≤ d.W n * d.L n :=
    (d.three_le_L n).trans (Nat.le_mul_of_pos_left _ (d.W_pos n))
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ (d.W n * d.L n) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = d.size n := rfl

private theorem GUETranslation_Nr_ge_nine (d : Sizes) (n : ℕ) : (9 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  exact_mod_cast GUETranslation_size_ge_nine d n

private theorem GUETranslation_Nr_pos (d : Sizes) (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  linarith [GUETranslation_Nr_ge_nine d n]

private theorem GUETranslation_Nr_ge_one (d : Sizes) (n : ℕ) : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  linarith [GUETranslation_Nr_ge_nine d n]

private theorem GUETranslation_Nr_tendsto {d : Sizes}
    (hd : Tendsto (fun n => d.size n) atTop atTop) :
    Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hd

private theorem GUETranslation_rpow_tendsto_zero {d : Sizes}
    (hd : Tendsto (fun n => d.size n) atTop atTop) {e : ℝ} (he : e < 0) :
    Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp (GUETranslation_Nr_tendsto hd)
  simpa [Function.comp_def] using h

private theorem GUETranslation_rhoSC_pos {E : ℝ} (hE : |E| < 2) : 0 < rhoSC E := by
  unfold rhoSC
  apply div_pos (Real.sqrt_pos.mpr ?_) (by positivity)
  have h1 : |E| ^ 2 < 2 ^ 2 := by
    have := abs_nonneg E
    nlinarith
  rw [sq_abs] at h1
  linarith

private theorem GUETranslation_zeta_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

private theorem GUETranslation_zeta_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ 1 - Real.exp (-T) := by
  have : Real.exp (-T) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith

private theorem GUETranslation_zeta_ge_half {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

/-- `|kPoint k P E λ| ≤ N^k sup|P|`: the prefactor `N^k / descFactorial N k` times at most
`descFactorial N k` embeddings. -/
private theorem GUETranslation_abs_kPoint_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P : (Fin k → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |P x| ≤ B) (E : ℝ) (lam : ι → ℝ) :
    |kPoint k P E lam| ≤ (Fintype.card ι : ℝ) ^ k * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold kPoint
  set M : ℕ := Fintype.card ι with hM
  set S : ℝ := ∑ f : Fin k ↪ ι, P (fun j => (M : ℝ) * (lam (f j) - E)) with hS
  have hcard : Fintype.card (Fin k ↪ ι) = M.descFactorial k := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
  have hSle : |S| ≤ (M.descFactorial k : ℝ) * B := by
    calc |S| ≤ ∑ f : Fin k ↪ ι, |P (fun j => (M : ℝ) * (lam (f j) - E))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _f : Fin k ↪ ι, B := Finset.sum_le_sum fun f _ => hB _
      _ = (M.descFactorial k : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ) ^ k / (M.descFactorial k : ℝ))]
  by_cases h0 : (M.descFactorial k : ℝ) = 0
  · rw [h0, div_zero, zero_mul]; positivity
  · calc (M : ℝ) ^ k / (M.descFactorial k : ℝ) * |S|
        ≤ (M : ℝ) ^ k / (M.descFactorial k : ℝ) * ((M.descFactorial k : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
      _ = (M : ℝ) ^ k * B := by field_simp

private theorem GUETranslation_kPoint_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P : (Fin k → ℝ) → ℝ} (hP : ∀ x, 0 ≤ P x) (E : ℝ) (lam : ι → ℝ) :
    0 ≤ kPoint k P E lam := by
  unfold kPoint
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun f _ => hP _)

private theorem GUETranslation_kPoint_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hPQ : ∀ x, P x ≤ Q x) (E : ℝ) (lam : ι → ℝ) :
    kPoint k P E lam ≤ kPoint k Q E lam := by
  unfold kPoint
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hPQ _) (by positivity)

private theorem GUETranslation_kPoint_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (P : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) :
    kPoint k (fun β => -P β) E lam = -kPoint k P E lam := by
  unfold kPoint
  simp only [Finset.sum_neg_distrib, mul_neg]

/-- Integrability of the `k`-point functional of a measurable Hermitian matrix map. -/
private theorem GUETranslation_integrable_kPoint {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ}
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) {B : ℝ} (hB : ∀ x, |O x| ≤ B) (E : ℝ) :
    Integrable (fun ω => kPoint k O E (hH ω).eigenvalues) Pm :=
  Integrable.of_bound (measurable_kPoint_eigenvalues Hm hH hm k O hO E).aestronglyMeasurable
    ((Fintype.card n : ℝ) ^ k * B) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact GUETranslation_abs_kPoint_le k hB E _)

/-- A crude deterministic bound: `|∫ kPoint k P E λ| ≤ N^k sup|P|`. -/
private theorem GUETranslation_abs_integral_kPoint_le {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Ω' → Matrix n n ℂ) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ}
    {B : ℝ} (hB : ∀ x, |P x| ≤ B) (E : ℝ) :
    |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ (Fintype.card n : ℝ) ^ k * B := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := (Fintype.card n : ℝ) ^ k * B)
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact GUETranslation_abs_kPoint_le k hB E _
  · rw [probReal_univ, mul_one]

private theorem GUETranslation_integral_kPoint_nonneg {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} (hP : 0 ≤ P) (E : ℝ) :
    0 ≤ ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm :=
  integral_nonneg fun _ => GUETranslation_kPoint_nonneg k (fun x => hP x) E _

/-- `|∫ kPoint P| ≤ ∫ kPoint Q` when `|P| ≤ Q` pointwise (smooth compactly supported `P`, `Q`). -/
private theorem GUETranslation_abs_integral_le_of_abs_le {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P ∧ HasCompactSupport P)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q)
    (hPQ : ∀ β, |P β| ≤ Q β) (E : ℝ) :
    |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm := by
  obtain ⟨BP, hBP⟩ := hP.1.continuous.bounded_above_of_compact_support hP.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hBP' : ∀ x, |P x| ≤ BP := fun x => by simpa [Real.norm_eq_abs] using hBP x
  have hBQ' : ∀ x, |Q x| ≤ BQ := fun x => by simpa [Real.norm_eq_abs] using hBQ x
  have hIP := GUETranslation_integrable_kPoint Pm hm hH k hP.1.continuous hBP' E
  have hIQ := GUETranslation_integrable_kPoint Pm hm hH k hQ.1.continuous hBQ' E
  have hBPn : ∀ x, |(fun β => -P β) x| ≤ BP := fun x => by simpa using hBP' x
  have hIPn := GUETranslation_integrable_kPoint Pm hm hH k hP.1.neg.continuous hBPn E
  have h1 : ∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIP hIQ fun ω =>
      GUETranslation_kPoint_mono k (fun β => (le_abs_self _).trans (hPQ β)) E _
  have h2 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm ≤
      ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm :=
    integral_mono hIPn hIQ fun ω =>
      GUETranslation_kPoint_mono k (fun β => (neg_le_abs _).trans (hPQ β)) E _
  have h3 : ∫ ω, kPoint k (fun β => -P β) E (hH ω).eigenvalues ∂Pm =
      -∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm := by
    simp only [GUETranslation_kPoint_neg, integral_neg]
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- A dilate of a test function is a test function. -/
private theorem GUETranslation_isTestFun_dilate {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) {a : ℝ} (ha : a ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : Fin k → ℝ => O (fun j => a * β j)) ∧
      HasCompactSupport (fun β : Fin k → ℝ => O (fun j => a * β j)) := by
  have heq : (fun β : Fin k → ℝ => O (fun j => a * β j)) =
      O ∘ (Homeomorph.smulOfNeZero a ha : (Fin k → ℝ) ≃ₜ (Fin k → ℝ)) := by
    funext β; rfl
  refine ⟨?_, ?_⟩
  · have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : Fin k → ℝ => a • β) :=
      contDiff_id.const_smul a
    exact hO.1.comp this
  · rw [heq]; exact hO.2.comp_homeomorph _

/-- A nonnegative test function dominating `|O|`. -/
private theorem GUETranslation_exists_abs_dominating {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) :
    ∃ Qa : (Fin k → ℝ) → ℝ,
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Qa ∧ HasCompactSupport Qa) ∧ 0 ≤ Qa ∧
        ∀ β, |O β| ≤ Qa β := by
  have hO' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β => -O β) ∧
      HasCompactSupport (fun β => -O β) := ⟨hO.1.neg, hO.2.neg⟩
  obtain ⟨Q1, hQ1, hQ10, h1⟩ := Step1Cond_exists_dominating_testFun hO 1 1
  obtain ⟨Q2, hQ2, hQ20, h2⟩ := Step1Cond_exists_dominating_testFun hO' 1 1
  refine ⟨fun β => Q1 β + Q2 β, ⟨hQ1.1.add hQ2.1, hQ1.2.add hQ2.2⟩,
    fun β => add_nonneg (hQ10 β) (hQ20 β), fun β => ?_⟩
  have e : (fun j => (1 : ℝ) * β j) = β := by funext j; simp
  have a1 := h1 1 ⟨le_rfl, le_rfl⟩ β
  have a2 := h2 1 ⟨le_rfl, le_rfl⟩ β
  rw [e] at a1 a2
  have b1 : 0 ≤ Q1 β := hQ10 β
  have b2 : 0 ≤ Q2 β := hQ20 β
  change |O β| ≤ Q1 β + Q2 β
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem GUETranslation_measurable_Xmat (L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j

/-- Measurability of `dbmMat` in the GUE sample. -/
private theorem GUETranslation_measurable_dbm (L W : ℕ) [NeZero L] [NeZero W] (v : Idx L W → ℝ)
    (t : ℝ) : Measurable (dbmMat L W v t) := by
  have hcont : Continuous (fun Y : Matrix (Idx L W) (Idx L W) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Y) := by fun_prop
  exact hcont.measurable.comp (GUETranslation_measurable_Xmat L W)

/-- Measurability of a single eigenvalue along a measurable Hermitian matrix map (Weyl's bound
`eigenvalues₀_abs_sub_le`; the analogous helpers of `EigenMeasurable`/`Step1Cond` are private). -/
private theorem GUETranslation_measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
    [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (i : n) : Measurable (fun ω => (hH ω).eigenvalues i) := by
  have hcont : Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      x.2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)) := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ _)
      (𝓝 x) (𝓝 (x.2.eigenvalues₀ _))
    rw [tendsto_iff_dist_tendsto_zero]
    have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
    have hc : Continuous (fun A : Matrix n n ℂ =>
        Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
      Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
    have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
        (𝓝 x.1) (𝓝 0) := by
      have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
      have := hc.continuousAt (x := x.1)
      rwa [ContinuousAt, hval] at this
    have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
        Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
      h0.comp (continuous_subtype_val.continuousAt (x := x))
    refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
    rw [Real.dist_eq]
    exact eigenvalues₀_abs_sub_le y.2 x.2 _
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have := hcont.measurable.comp hφ
  simpa [Matrix.IsHermitian.eigenvalues, Function.comp_def] using this

/-- `stieltjesN` is the finite-sum Stieltjes transform `mV` of the eigenvalues. -/
private theorem GUETranslation_stieltjesN_eq_mV {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    stieltjesN H z = mV hH.eigenvalues z := by
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold stieltjesN mV
  congr 1
  rw [green_eq_spectral hH hzne]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

/-- **Counting by the Stieltjes transform**: `#{i : |λ_i| ≤ η} ≤ 2 n η Im m(iη)`. -/
private theorem GUETranslation_count_le_im {n : Type*} [Fintype n] (lam : n → ℝ) {η : ℝ}
    (hη : 0 < η) :
    (((Finset.univ : Finset n).filter (fun i => |lam i| ≤ η)).card : ℝ) ≤
      2 * (Fintype.card n : ℝ) * η * (mV lam ⟨0, η⟩).im := by
  have hterm : ∀ i, (((lam i : ℂ) - ⟨0, η⟩)⁻¹).im = η / (lam i ^ 2 + η ^ 2) := by
    intro i
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.sub_re, Complex.ofReal_re]
    ring
  have him : (mV lam ⟨0, η⟩).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    unfold mV
    have hc : ((Fintype.card n : ℂ))⁻¹ = (((Fintype.card n : ℝ))⁻¹ : ℝ) := by simp
    rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [hterm]
  set S := (Finset.univ : Finset n).filter (fun i => |lam i| ≤ η) with hS
  have hsum : (S.card : ℝ) / (2 * η) ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    calc (S.card : ℝ) / (2 * η) = ∑ _i ∈ S, 1 / (2 * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ S, η / (lam i ^ 2 + η ^ 2) := Finset.sum_le_sum fun i hi => by
          have hi' : |lam i| ≤ η := (Finset.mem_filter.mp hi).2
          have h2 : lam i ^ 2 ≤ η ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi' 2
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by positivity)
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have hempty : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    have : S = ∅ := by
      rw [hS]; exact Finset.eq_empty_of_forall_notMem fun i => (hempty.false i).elim
    simp [this]
  · have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    rw [him]
    have e : 2 * (Fintype.card n : ℝ) * η * ((Fintype.card n : ℝ)⁻¹ *
        ∑ i, η / (lam i ^ 2 + η ^ 2)) = 2 * η * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
      field_simp
    rw [e]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η)).mp hsum
    linarith

/-- Two finite families with the same multiset of values differ by a permutation of the index. -/
private theorem GUETranslation_exists_perm {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Equiv.Perm ι, ∀ i, g (σ i) = f i := by
  classical
  have hc : ∀ x : ℝ, (Finset.univ.filter (fun i => f i = x)).card =
      (Finset.univ.filter (fun i => g i = x)).card := by
    intro x
    have h1 := congrArg (Multiset.count x) h
    simpa [Multiset.count_map, Finset.card_def, Finset.filter_val, eq_comm] using h1
  let e : ∀ x : ℝ, {i // f i = x} ≃ {i // g i = x} := fun x =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact hc x)
  exact ⟨Equiv.ofFiberEquiv e, fun i => Equiv.ofFiberEquiv_map e i⟩

/-- The eigenvalues of `A - c·1` are those of `A` minus `c`, up to a permutation of the index. -/
private theorem GUETranslation_eigenvalues_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ)
    (hB : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian) :
    ∃ σ : Equiv.Perm ι, ∀ i, hA.eigenvalues (σ i) - c = hB.eigenvalues i := by
  have h1 : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).charpoly =
      A.charpoly.comp (Polynomial.X + Polynomial.C (c : ℂ)) := by
    have := Matrix.charpoly_sub_scalar A (c : ℂ)
    rw [Matrix.scalar_apply] at this
    rw [Matrix.smul_one_eq_diagonal]
    exact this
  have h2 : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)).charpoly.roots =
      Multiset.map (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ)) Finset.univ.val := by
    rw [h1]
    have h3 := Polynomial.roots_comp_C_mul_X_add_C A.charpoly 1 (c : ℂ) isUnit_one
    rw [Polynomial.C_1, one_mul] at h3
    rw [h3, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [Ring.inverse_one]
  have h4 : Multiset.map hB.eigenvalues Finset.univ.val =
      Multiset.map (fun i => hA.eigenvalues i - c) Finset.univ.val := by
    have h5 := hB.roots_charpoly_eq_eigenvalues
    rw [h2] at h5
    have h6 := congrArg (Multiset.map Complex.re) h5
    simp only [Multiset.map_map] at h6
    simpa [Function.comp_def] using h6.symm
  exact GUETranslation_exists_perm h4

/-- `kPoint` is invariant under a permutation of the eigenvalue labels. -/
private theorem GUETranslation_kPoint_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) :
    kPoint k O E (fun i => lam (σ i)) = kPoint k O E lam := by
  let e : (Fin k ↪ ι) ≃ (Fin k ↪ ι) :=
    { toFun := fun f => f.trans σ.toEmbedding
      invFun := fun f => f.trans σ.symm.toEmbedding
      left_inv := fun f => by ext j; simp
      right_inv := fun f => by ext j; simp }
  unfold kPoint
  congr 1
  exact Fintype.sum_equiv e _ _ (fun f => rfl)

/-- **The energy shift**: `kPoint k O 0 (λ(A - c)) = kPoint k O c (λ(A))`. -/
private theorem GUETranslation_kPoint_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ)
    (hBA : B = A - (c : ℂ) • (1 : Matrix ι ι ℂ)) (k : ℕ) (O : (Fin k → ℝ) → ℝ) :
    kPoint k O 0 hB.eigenvalues = kPoint k O c hA.eigenvalues := by
  subst hBA
  obtain ⟨σ, hσ⟩ := GUETranslation_eigenvalues_shift hA c hB
  rw [← GUETranslation_kPoint_perm σ k O c hA.eigenvalues]
  unfold kPoint
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  funext j
  rw [← hσ (f j)]
  ring

private theorem GUETranslation_dbmMat_shift (L W : ℕ) [NeZero L] [NeZero W] (v : Idx L W → ℝ)
    (t E : ℝ) (ω : Ω L W) :
    dbmMat L W (fun i => v i - E) t ω =
      dbmMat L W v t ω - (E : ℂ) • (1 : Matrix (Idx L W) (Idx L W) ℂ) := by
  unfold dbmMat
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.ofReal_sub]
    ring
  · simp [hij]

/-- The shift inside the DBM functional: `kPoint k O 0` of `dbmMat (v - E)` is `kPoint k O E` of
`dbmMat v`, pointwise and hence after integration over the GUE block. -/
private theorem GUETranslation_integral_dbm_shift (L W : ℕ) [NeZero L] [NeZero W]
    (v : Idx L W → ℝ) (t E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) :
    ∫ ω, kPoint k O 0 (dbmMat_isHermitian L W (fun i => v i - E) t ω).eigenvalues
        ∂(gueP L W) =
      ∫ ω, kPoint k O E (dbmMat_isHermitian L W v t ω).eigenvalues ∂(gueP L W) :=
  integral_congr_ae (Eventually.of_forall fun ω =>
    GUETranslation_kPoint_shift (dbmMat_isHermitian L W v t ω)
      (dbmMat_isHermitian L W (fun i => v i - E) t ω) E
      (GUETranslation_dbmMat_shift L W v t E ω) k O)

/-- **GUE count**: for a nonnegative test function `Q`,
`N^{-3τ_U/8} · ∫ kPoint k Q 0 (λ(GUE)) → 0`.  The functional is bounded by
`E[#{i : |λ_i| ≤ R/N}^k]`; on the `GUELocal` good event at `z = i N^{-1+a}`,
`a = τ_U/(8(k+1))`, `τ_G = a/2` (so that `N^{τ_G}/√(N Im z) = 1`), one has `‖m_N - m_sc‖ ≤ 1`,
`Im m_N ≤ 2` and the count is `≤ 4 N^a`; the bad event costs `N^k N^{-(k+1)} ≤ 1`.
Slack: `3τ_U/8 - k a > τ_U/4`. -/
private theorem GUETranslation_gue_count (hGUE : GUELocal) (d : Sizes)
    (hd : Tendsto (fun n => d.size n) atTop atTop) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) (k : ℕ)
    {Q : (Fin k → ℝ) → ℝ} (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q)
    (hQ0 : 0 ≤ Q) :
    Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
        ∂(gueP (d.L n) (d.W n))) atTop (𝓝 0) := by
  obtain ⟨B, R, hB, hR, hQR⟩ := Step1Cond_exists_le_indicator hQ
  set a : ℝ := τs / (8 * ((k : ℝ) + 1)) with ha_def
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have ha : 0 < a := by rw [ha_def]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 8 * ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hka : a * k + -(3 * τs / 8) < 0 := by
    rw [ha_def]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : τs / (8 * ((k : ℝ) + 1)) * k ≤ τs / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hr : -(3 * τs / 8) < 0 := by linarith
  have hGN := hGUE d hd 1 (a / 2) ((k + 1 : ℕ) : ℝ) one_pos (by positivity) (by positivity)
  have hNr := GUETranslation_Nr_tendsto hd
  have hRM : ∀ᶠ n in atTop, R ≤ ((d.size n : ℕ) : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp hNr).eventually_ge_atTop R
  have hkM : ∀ᶠ n in atTop, 2 * (k : ℝ) + 1 ≤ ((d.size n : ℕ) : ℝ) :=
    hNr.eventually_ge_atTop _
  have hbound : ∀ᶠ n in atTop,
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
          ∂(gueP (d.L n) (d.W n)) ≤
        B * 2 ^ k * ((4 * ((d.size n : ℕ) : ℝ) ^ a) ^ k + 1) := by
    filter_upwards [hGN, hRM, hkM] with n hGb hRMn hkMn
    have hNpos := GUETranslation_Nr_pos d n
    have hN1 := GUETranslation_Nr_ge_one d n
    have hcard := GUETranslation_card_real d n
    set N : ℝ := ((d.size n : ℕ) : ℝ) with hN_def
    have hk : k < Fintype.card (Idx (d.L n) (d.W n)) := by
      have : (k : ℝ) < (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) := by rw [hcard]; linarith
      exact_mod_cast this
    have h1 := Step1Cond_corrPairing_le_count_smul (gueP (d.L n) (d.W n))
      (Xmat (d.L n) (d.W n)) (GUETranslation_measurable_Xmat _ _) (Xmat_isHermitian (d.L n) (d.W n))
      k hk hQ0 hB hQR 0
    rw [hcard] at h1
    refine h1.trans ?_
    -- the prefactor
    have hMk : (0 : ℝ) < N - k := by linarith
    have hX : (N / (N - k)) ^ k ≤ 2 ^ k := by
      refine pow_le_pow_left₀ (div_nonneg hNpos.le hMk.le) ?_ k
      rw [div_le_iff₀ hMk]; linarith
    -- the count moment
    set η : ℝ := N ^ (-1 + a) with hη_def
    have hηpos : 0 < η := Real.rpow_pos_of_pos hNpos _
    have hNη : N * η = N ^ a := by
      rw [hη_def]
      calc N * N ^ (-1 + a) = N ^ (1 : ℝ) * N ^ (-1 + a) := by rw [Real.rpow_one]
        _ = N ^ ((1 : ℝ) + (-1 + a)) := (Real.rpow_add hNpos _ _).symm
        _ = N ^ a := by congr 1; ring
    have hRη : R / N ≤ η := by
      rw [div_le_iff₀ hNpos, mul_comm, hNη]; exact hRMn
    have hz0 : 0 < (⟨0, η⟩ : ℂ).im := hηpos
    have hsqrt : Real.sqrt (N * η) = N ^ (a / 2) := by
      rw [hNη, Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
      congr 1; ring
    set bad : Set (Ω (d.L n) (d.W n)) := {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧
        N ^ (-1 + a / 2) ≤ z.im ∧ z.im ≤ 10 ∧
        N ^ (a / 2) / Real.sqrt (N * z.im) <
          ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖} with hbad
    set T := toMeasurable (gueP (d.L n) (d.W n)) bad with hT_def
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    have hsubT : bad ⊆ T := subset_toMeasurable _ _
    have hμT : gueP (d.L n) (d.W n) T = gueP (d.L n) (d.W n) bad := measure_toMeasurable _
    set cnt : Ω (d.L n) (d.W n) → ℝ := fun ω =>
      (((Finset.univ : Finset (Idx (d.L n) (d.W n))).filter
        (fun i => |(Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues i - 0| ≤ R / N)).card : ℝ)
      with hcnt
    have hcnt0 : ∀ ω, 0 ≤ cnt ω := fun ω => Nat.cast_nonneg _
    have hcntM : ∀ ω, cnt ω ≤ N := fun ω => by
      rw [← hcard]
      have := Finset.card_filter_le (Finset.univ : Finset (Idx (d.L n) (d.W n)))
        (fun i => |(Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues i - 0| ≤ R / N)
      rw [Finset.card_univ] at this
      simp only [hcnt]
      exact_mod_cast this
    have hcntgood : ∀ ω, ω ∉ bad → cnt ω ≤ 4 * N ^ a := by
      intro ω hω
      have hzcond : |(⟨0, η⟩ : ℂ).re| ≤ 2 - 1 ∧ N ^ (-1 + a / 2) ≤ (⟨0, η⟩ : ℂ).im ∧
          (⟨0, η⟩ : ℂ).im ≤ 10 := by
        refine ⟨by simp, ?_, ?_⟩
        · exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        · have : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
          change η ≤ 10
          linarith
      have hle : ‖stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩ - msc ⟨0, η⟩‖ ≤ 1 := by
        by_contra hcon
        push Not at hcon
        refine hω ⟨⟨0, η⟩, hzcond.1, hzcond.2.1, hzcond.2.2, ?_⟩
        change N ^ (a / 2) / Real.sqrt (N * η) < _
        rw [hsqrt, div_self (Real.rpow_pos_of_pos hNpos _).ne']
        exact hcon
      set lam := (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues with hlam
      have hsubset : (Finset.univ : Finset (Idx (d.L n) (d.W n))).filter
          (fun i => |lam i - 0| ≤ R / N) ⊆
          (Finset.univ : Finset (Idx (d.L n) (d.W n))).filter (fun i => |lam i| ≤ η) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_zero] at hi ⊢
        exact hi.trans hRη
      have hc1 : cnt ω ≤ (((Finset.univ : Finset (Idx (d.L n) (d.W n))).filter
          (fun i => |lam i| ≤ η)).card : ℝ) := by
        simp only [hcnt]
        exact_mod_cast Finset.card_le_card hsubset
      have hc2 := GUETranslation_count_le_im lam hηpos
      rw [hcard] at hc2
      have hst : mV lam ⟨0, η⟩ = stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩ :=
        (GUETranslation_stieltjesN_eq_mV (Xmat_isHermitian (d.L n) (d.W n) ω) hz0).symm
      rw [hst] at hc2
      have hIm : (stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩).im ≤ 2 := by
        have h1 := Complex.im_le_norm (stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩)
        have h2 := norm_msc_lt_one hz0
        have h3 := norm_le_insert' (stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩) (msc ⟨0, η⟩)
        linarith
      calc cnt ω ≤ 2 * N * η * (stieltjesN (Xmat (d.L n) (d.W n) ω) ⟨0, η⟩).im := hc1.trans hc2
        _ ≤ 2 * N * η * 2 := mul_le_mul_of_nonneg_left hIm (by positivity)
        _ = 4 * N ^ a := by rw [mul_assoc 2 N η, hNη]; ring
    have hg : Integrable (fun ω => (4 * N ^ a) ^ k + T.indicator (fun _ => N ^ k) ω)
        (gueP (d.L n) (d.W n)) :=
      (integrable_const _).add ((integrable_const _).indicator hTm)
    have hpt : ∀ ω, cnt ω ^ k ≤ (4 * N ^ a) ^ k + T.indicator (fun _ => N ^ k) ω := by
      intro ω
      by_cases hω : ω ∈ bad
      · rw [Set.indicator_of_mem (hsubT hω)]
        have : cnt ω ^ k ≤ N ^ k := pow_le_pow_left₀ (hcnt0 ω) (hcntM ω) k
        have : 0 ≤ (4 * N ^ a) ^ k := by positivity
        linarith
      · have h1 : cnt ω ^ k ≤ (4 * N ^ a) ^ k :=
          pow_le_pow_left₀ (hcnt0 ω) (hcntgood ω hω) k
        have h2 : 0 ≤ T.indicator (fun _ => N ^ k) ω :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        linarith
    have hint : ∫ ω, cnt ω ^ k ∂(gueP (d.L n) (d.W n)) ≤ (4 * N ^ a) ^ k + 1 := by
      refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hcnt0 ω) k) hg
        (Eventually.of_forall hpt)).trans ?_
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm),
        integral_const, integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
      have hTreal : (gueP (d.L n) (d.W n)).real T ≤ N ^ (-((k + 1 : ℕ) : ℝ)) := by
        rw [measureReal_def, hμT]
        exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hGb
      have hNpow : N ^ (-((k + 1 : ℕ) : ℝ)) * N ^ k ≤ 1 := by
        rw [Real.rpow_neg hNpos.le, Real.rpow_natCast,
          inv_mul_le_iff₀ (by positivity), mul_one]
        exact pow_le_pow_right₀ hN1 (Nat.le_succ k)
      have := mul_le_mul_of_nonneg_right hTreal (pow_nonneg hNpos.le k)
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hX hB.le) hint
      (integral_nonneg fun ω => pow_nonneg (hcnt0 ω) k) (by positivity)
  -- conclude
  have hlim : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
      (B * 2 ^ k * ((4 * ((d.size n : ℕ) : ℝ) ^ a) ^ k + 1))) atTop (𝓝 0) := by
    have e : ∀ n, ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
        (B * 2 ^ k * ((4 * ((d.size n : ℕ) : ℝ) ^ a) ^ k + 1)) =
        B * 2 ^ k * 4 ^ k * ((d.size n : ℕ) : ℝ) ^ (a * k + -(3 * τs / 8)) +
          B * 2 ^ k * ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by
      intro n
      rw [Real.rpow_add (GUETranslation_Nr_pos d n),
        Real.rpow_mul_natCast (GUETranslation_Nr_pos d n).le, mul_pow]
      ring
    simp_rw [e]
    have hsum := ((GUETranslation_rpow_tendsto_zero hd hka).const_mul (B * 2 ^ k * 4 ^ k)).add
      ((GUETranslation_rpow_tendsto_zero hd hr).const_mul (B * 2 ^ k))
    simpa using hsum
  have hnn : ∀ n, 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
        ∂(gueP (d.L n) (d.W n)) := fun n =>
    mul_nonneg (Real.rpow_nonneg (GUETranslation_Nr_pos d n).le _)
      (GUETranslation_integral_kPoint_nonneg _ _ _ k hQ0 0)
  have hle : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
      ∫ ω, kPoint k Q 0 (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
        ∂(gueP (d.L n) (d.W n)) ≤
        ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) *
          (B * 2 ^ k * ((4 * ((d.size n : ℕ) : ℝ) ^ a) ^ k + 1)) := by
    filter_upwards [hbound] with n hn
    exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (GUETranslation_Nr_pos d n).le _)
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim

/-- The conditional (DBM) functional given the first block `ω₁` of the band sample:
`∫ kPoint k O 0 (λ(diag(e^{-T/2} λ(X₁) - E₀) + √(1 - e^{-T}) X₂)) d gueP(X₂)`. -/
private def GUETranslation_Hs (L W : ℕ) [NeZero L] [NeZero W] (T E₀ : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (ω₁ : Ω L W) : ℝ :=
  ∫ y, kPoint k O 0 (dbmMat_isHermitian L W
    (fun i => Real.exp (-T / 2) * (Xmat_isHermitian L W ω₁).eigenvalues i - E₀)
    (1 - Real.exp (-T)) y).eigenvalues ∂(gueP L W)

/-- The conditional functional is measurable in the first block. -/
private theorem GUETranslation_measurable_Hs (L W : ℕ) [NeZero L] [NeZero W] (T E₀ : ℝ) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) : Measurable (GUETranslation_Hs L W T E₀ k O) := by
  set t := 1 - Real.exp (-T) with ht
  have heig : Measurable (fun ω : Ω L W => fun i => (Xmat_isHermitian L W ω).eigenvalues i) :=
    measurable_pi_iff.mpr fun i =>
      GUETranslation_measurable_eigenvalue (GUETranslation_measurable_Xmat L W)
        (Xmat_isHermitian L W) i
  have hv : Measurable (fun ω : Ω L W => fun i =>
      Real.exp (-T / 2) * (Xmat_isHermitian L W ω).eigenvalues i - E₀) :=
    measurable_pi_iff.mpr fun i => (((measurable_pi_apply i).comp heig).const_mul _).sub_const _
  have hGc : Continuous (fun q : (Idx L W → ℝ) × Matrix (Idx L W) (Idx L W) ℂ =>
      Matrix.diagonal (fun i => (q.1 i : ℂ)) + Real.sqrt t • q.2) := by
    refine Continuous.add ?_ (continuous_snd.const_smul (Real.sqrt t))
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))
  have hm : Measurable (fun p : Ω L W × Ω L W => dbmMat L W
      (fun i => Real.exp (-T / 2) * (Xmat_isHermitian L W p.1).eigenvalues i - E₀) t p.2) :=
    hGc.measurable.comp ((hv.comp measurable_fst).prodMk
      ((GUETranslation_measurable_Xmat L W).comp measurable_snd))
  have hf := measurable_kPoint_eigenvalues
    (fun p : Ω L W × Ω L W => dbmMat L W
      (fun i => Real.exp (-T / 2) * (Xmat_isHermitian L W p.1).eigenvalues i - E₀) t p.2)
    (fun p => dbmMat_isHermitian L W
      (fun i => Real.exp (-T / 2) * (Xmat_isHermitian L W p.1).eigenvalues i - E₀) t p.2)
    hm k O hO 0
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := gueP L W)).measurable


/-- **Conditioning on the first GUE block** (via `Step1Cond_gueMatPairing_eq_integral` and the
energy shift): the GUE functional at `E₀` is the `gueP`-average of the conditional functional
`GUETranslation_Hs`. -/
private theorem GUETranslation_integral_gue (L W : ℕ) [NeZero L] [NeZero W] {T : ℝ} (hT : 0 ≤ T)
    (E₀ : ℝ) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) :
    ∫ ω, kPoint k O E₀ (Xmat_isHermitian L W ω).eigenvalues ∂(gueP L W) =
      ∫ ω, GUETranslation_Hs L W T E₀ k O ω ∂(gueP L W) := by
  rw [Step1Cond_gueMatPairing_eq_integral L W hT k hO E₀]
  refine integral_congr_ae (Eventually.of_forall fun ω₁ => ?_)
  exact (GUETranslation_integral_dbm_shift L W
    (fun i => Real.exp (-T / 2) * (Xmat_isHermitian L W ω₁).eigenvalues i)
    (1 - Real.exp (-T)) E₀ k O).symm

/-- **Worst-sequence core**: along any sequence `ω n`
eventually in the good event, `L32` applies to `v n = vGUE … (ω n)` at energy `0`, time
`1 - e^{-t*}`, with `δ = σ = min (τ_U/4) ((1-τ_U)/3)`, `q = 1/2`, `c = min κ 1 / 960`, `C = 2`,
`CV = 2`, `g = N^{-1+τ_U/4}`, `G = N^{-σ}`, `m = freeConvST (v n) (tt n)`, and the test
function `O(ρ_sc(E₀)⁻¹ ·)`; the conditional functional is close to the dilated GUE functional. -/
private theorem GUETranslation_core (hL32 : L32) (hGUE : GUELocal) (d : Sizes)
    (hd : Tendsto (fun n => d.size n) atTop atTop) {κ : ℝ} (hκ : 0 < κ) {τs : ℝ}
    (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) (ω : ∀ n, Ω (d.L n) (d.W n))
    (hω : ∀ᶠ n in atTop, GUEGoodAt d n κ τs E₀ (ω n)) :
    Tendsto (fun n => GUETranslation_Hs (d.L n) (d.W n) (ouTStar d τs n) E₀ k O (ω n) -
      ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
        (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)))
      atTop (𝓝 0) := by
  classical
  set ρ₁ := rhoSC E₀ with hρ₁
  set ρ₀ := rhoSC 0 with hρ₀
  have hρ₁pos : 0 < ρ₁ := GUETranslation_rhoSC_pos (by linarith)
  have hρ₀pos : 0 < ρ₀ := GUETranslation_rhoSC_pos (by norm_num)
  set σ : ℝ := min (τs / 4) ((1 - τs) / 3) with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by linarith)
  have hσ1 : σ ≤ τs / 4 := min_le_left _ _
  have hσ2 : σ ≤ (1 - τs) / 3 := min_le_right _ _
  have hc : 0 < min κ 1 / 960 := div_pos (lt_min hκ one_pos) (by norm_num)
  -- the data fed to `L32`
  let v : ∀ n, Idx (d.L n) (d.W n) → ℝ := fun n => vGUE d n τs E₀ (ω n)
  let tt : ℕ → ℝ := fun n => 1 - Real.exp (-(ouTStar d τs n))
  let g : ℕ → ℝ := fun n => ((d.size n : ℕ) : ℝ) ^ (-1 + τs / 4)
  let G : ℕ → ℝ := fun n => ((d.size n : ℕ) : ℝ) ^ (-σ)
  let m : ℕ → ℂ → ℂ := fun n => freeConvST (v n) (tt n)
  let PP : ℕ → Prop := fun n => ∃ ρ : ℝ, Tendsto (fun η : ℝ => (m n ⟨0, η⟩).im / Real.pi)
    (𝓝[>] 0) (𝓝 ρ) ∧ |ρ - ρ₁| ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8))
  let ρs : ℕ → ℝ := fun n => if h : PP n then Classical.choose h else ρ₁
  have hgood : ∀ᶠ n in atTop,
      IsRegular32 (v n) (g n) (G n) (min κ 1 / 960) 2 2 ∧
      Tendsto (fun η : ℝ => (m n ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρs n)) ∧
      |ρs n - ρ₁| ≤ ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) := by
    filter_upwards [hω] with n hn
    obtain ⟨hreg, hex⟩ := hn
    have hP : PP n := hex
    have hspec := Classical.choose_spec hP
    have hρsN : ρs n = Classical.choose hP := by simp only [ρs, hP, ↓reduceDIte]
    rw [hρsN]
    exact ⟨hreg, hspec⟩
  -- eventual size facts
  have hM2 : ∀ᶠ n in atTop, 2 ≤ ((d.size n : ℕ) : ℝ) ^ (τs / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τs / 2)).comp
      (GUETranslation_Nr_tendsto hd)).eventually_ge_atTop 2
  -- the premises of `L32`
  have hprem : ∀ᶠ n in atTop,
      ((d.size n : ℕ) : ℝ) ^ σ / ((d.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((d.size n : ℕ) : ℝ) ^ (-σ) ∧ G n ≤ ((d.size n : ℕ) : ℝ) ^ (-σ) ∧
      g n * ((d.size n : ℕ) : ℝ) ^ σ ≤ tt n ∧
      tt n ≤ ((d.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |(fun _ : ℕ => (0 : ℝ)) n| ≤ 1 / 2 * G n ∧
      IsRegular32 (v n) (g n) (G n) (min κ 1 / 960) 2 2 ∧ IsFreeConv32 (v n) (tt n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨(fun _ : ℕ => (0 : ℝ)) n, η⟩).im / Real.pi) (𝓝[>] 0)
        (𝓝 (ρs n)) := by
    filter_upwards [hgood, hM2] with n hn hM2n
    have hM := GUETranslation_Nr_pos d n
    have hM1 := GUETranslation_Nr_ge_one d n
    set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
    have ht : ouTStar d τs n = N ^ (-1 + τs) := rfl
    have ht0 : 0 ≤ N ^ (-1 + τs) := Real.rpow_nonneg hM.le _
    have ht1 : N ^ (-1 + τs) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
    refine ⟨?_, ?_, le_rfl, ?_, ?_, ?_, hn.1, ?_, hn.2.1⟩
    · change N ^ σ / N ≤ N ^ (-1 + τs / 4)
      rw [← Real.rpow_sub_one hM.ne']
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    · change N ^ (-1 + τs / 4) ≤ N ^ (-σ)
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    · change N ^ (-1 + τs / 4) * N ^ σ ≤ 1 - Real.exp (-(ouTStar d τs n))
      rw [← Real.rpow_add hM, ht]
      refine le_trans ?_ (GUETranslation_zeta_ge_half ht0 ht1)
      have hsplit : N ^ (-1 + τs) = N ^ (-1 + τs / 2) * N ^ (τs / 2) := by
        rw [← Real.rpow_add hM]; congr 1; ring
      have hle : N ^ (-1 + τs / 4 + σ) ≤ N ^ (-1 + τs / 2) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      have hpos : 0 ≤ N ^ (-1 + τs / 2) := Real.rpow_nonneg hM.le _
      rw [hsplit]
      nlinarith
    · change 1 - Real.exp (-(ouTStar d τs n)) ≤ N ^ (-σ) * (N ^ (-σ)) ^ 2
      rw [← Real.rpow_mul_natCast hM.le, ← Real.rpow_add hM, ht]
      refine (GUETranslation_zeta_le _).trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by push_cast; linarith)
    · change |(0 : ℝ)| ≤ 1 / 2 * N ^ (-σ)
      rw [abs_zero]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hM.le _)
    · exact isFreeConv51_freeConvST (v n) (GUETranslation_zeta_nonneg (by rw [ht]; exact ht0))
  have hL : ∀ P : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → HasCompactSupport P →
      Tendsto (fun n =>
        (∫ y, kPoint k (fun β => P (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian (d.L n) (d.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP (d.L n) (d.W n))) -
        ∫ y, kPoint k (fun β => P (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)))
        atTop (𝓝 0) := fun P hP hPc =>
    hL32 d hd σ σ (1 / 2) (min κ 1 / 960) 2 2 hσpos hσpos (by norm_num) (by norm_num) hc
      g G tt (fun _ => 0) v m ρs hprem k P hP hPc
  -- `ρs → ρ₁` at rate `N^{-3τ_U/8}`
  have hclose : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) < ρ₁ / 2 :=
    (GUETranslation_rpow_tendsto_zero hd (by linarith : -(3 * τs / 8) < 0)).eventually
      (gt_mem_nhds (by positivity))
  -- step (i): `L32` with `Õ = O(ρ₁⁻¹ ·)`
  have hOt := GUETranslation_isTestFun_dilate hO (inv_ne_zero hρ₁pos.ne')
  let A : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρs n / ρ₁ * β j)) 0
    (dbmMat_isHermitian (d.L n) (d.W n) (v n) (tt n) y).eigenvalues ∂(gueP (d.L n) (d.W n))
  let gue0 : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => O (fun j => ρ₀ / ρ₁ * β j)) 0
    (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n))
  have hA : Tendsto (fun n => A n - gue0 n) atTop (𝓝 0) := by
    refine (hL _ hOt.1 hOt.2).congr fun n => ?_
    have e1 : (fun β : Fin k → ℝ => O (fun j => ρ₁⁻¹ * (ρs n * β j))) =
        (fun β : Fin k → ℝ => O (fun j => ρs n / ρ₁ * β j)) := by
      funext β; congr 1; funext j; field_simp
    have e2 : (fun β : Fin k → ℝ => O (fun j => ρ₁⁻¹ * (ρ₀ * β j))) =
        (fun β : Fin k → ℝ => O (fun j => ρ₀ / ρ₁ * β j)) := by
      funext β; congr 1; funext j; field_simp
    simp only [A, gue0, e1, e2]
  -- step (ii): Lipschitz in the scale
  obtain ⟨Q, hQ, hQ0, C, hC⟩ := Step1Cond_scaledPairing_lipschitz hO (ρmin := 1 / 2) (ρmax := 2)
    (by norm_num) (by norm_num)
  -- step (iii): domination and the counts
  obtain ⟨Q', hQ', hQ'0, hdom⟩ := Step1Cond_exists_dominating_testFun hQ (ρ₁ / 2) (2 * ρ₁)
  have hQ'1 : ∀ᶠ n in atTop,
      (∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
          (dbmMat_isHermitian (d.L n) (d.W n) (v n) (tt n) y).eigenvalues
            ∂(gueP (d.L n) (d.W n))) -
        ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)) < 1 :=
    (hL Q' hQ'.1 hQ'.2).eventually (gt_mem_nhds one_pos)
  obtain ⟨Qa, hQa, hQa0, hQaO⟩ := GUETranslation_exists_abs_dominating hO
  have hc0 : ρ₀ / ρ₁ ≠ 0 := (div_pos hρ₀pos hρ₁pos).ne'
  have hGc := GUETranslation_gue_count hGUE d hd h0 h1 k
    (Q := fun β => Q' (fun j => ρ₀ * β j)) (GUETranslation_isTestFun_dilate hQ' hρ₀pos.ne')
    (fun β => hQ'0 (fun j => ρ₀ * β j))
  have hGa := GUETranslation_gue_count hGUE d hd h0 h1 k
    (Q := fun β => Qa (fun j => ρ₀ / ρ₁ * β j)) (GUETranslation_isTestFun_dilate hQa hc0)
    (fun β => hQa0 (fun j => ρ₀ / ρ₁ * β j))
  set Lc : ℝ := k * 2 ^ (k - 1) / ρ₁ with hLc_def
  have hLc0 : 0 ≤ Lc := by positivity
  set GQ : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
    (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)) with hGQ
  set Ga : ℕ → ℝ := fun n => ∫ y, kPoint k (fun β => Qa (fun j => ρ₀ / ρ₁ * β j)) 0
    (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)) with hGa_def
  set mr : ℕ → ℝ := fun n => ((d.size n : ℕ) : ℝ) ^ (-(3 * τs / 8)) with hmr
  have hbound : ∀ᶠ n in atTop,
      ‖GUETranslation_Hs (d.L n) (d.W n) (ouTStar d τs n) E₀ k O (ω n) - gue0 n‖ ≤
        |A n - gue0 n| * (1 + Lc * mr n) + |C| / ρ₁ * (mr n * GQ n + mr n) +
          Lc * (mr n * Ga n) := by
    filter_upwards [hgood, hclose, hQ'1] with n hn hcl hQ'n
    have hMr : 0 ≤ mr n := Real.rpow_nonneg (GUETranslation_Nr_pos d n).le _
    have hdist : |ρs n - ρ₁| < ρ₁ / 2 := lt_of_le_of_lt hn.2.2 hcl
    have hρsI : ρs n ∈ Set.Icc (ρ₁ / 2) (2 * ρ₁) := by
      rw [abs_lt] at hdist; constructor <;> linarith
    have hρspos : 0 < ρs n := by linarith [hρsI.1]
    set r : ℝ := ρs n / ρ₁ with hr_def
    have hrI : r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rw [abs_lt] at hdist
      constructor
      · rw [hr_def, le_div_iff₀ hρ₁pos]; linarith
      · rw [hr_def, div_le_iff₀ hρ₁pos]; linarith
    have hmeas := GUETranslation_measurable_dbm (d.L n) (d.W n) (v n) (tt n)
    set Hh := dbmMat_isHermitian (d.L n) (d.W n) (v n) (tt n) with hHh
    have hF : GUETranslation_Hs (d.L n) (d.W n) (ouTStar d τs n) E₀ k O (ω n) =
        ∫ y, kPoint k O 0 (Hh y).eigenvalues ∂(gueP (d.L n) (d.W n)) := rfl
    set Fv := ∫ y, kPoint k O 0 (Hh y).eigenvalues ∂(gueP (d.L n) (d.W n)) with hFv
    have hAn : A n = ∫ y, kPoint k (fun β => O (fun j => r * β j)) 0 (Hh y).eigenvalues
        ∂(gueP (d.L n) (d.W n)) := rfl
    set g' := gue0 n with hg'
    set D := A n - g' with hD
    -- `|r - 1| ≤ N^{-rate}/ρ₁`
    have hr1 : |r - 1| ≤ mr n / ρ₁ := by
      rw [show r - 1 = (ρs n - ρ₁) / ρ₁ by rw [hr_def]; field_simp, abs_div, abs_of_pos hρ₁pos]
      exact div_le_div_of_nonneg_right hn.2.2 hρ₁pos.le
    -- the Lipschitz term
    set corrQ := ∫ y, kPoint k Q 0 (Hh y).eigenvalues ∂(gueP (d.L n) (d.W n)) with hcorrQ_def
    have hcorrQ0 : 0 ≤ corrQ := GUETranslation_integral_kPoint_nonneg _ _ _ k hQ0 0
    obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
    obtain ⟨BQ', hBQ'⟩ := hQ'.1.continuous.bounded_above_of_compact_support hQ'.2
    have hcont' : Continuous (fun β : Fin k → ℝ => Q' (fun j => ρs n * β j)) :=
      hQ'.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
    have hmono : corrQ ≤ ∫ y, kPoint k (fun β => Q' (fun j => ρs n * β j)) 0
        (Hh y).eigenvalues ∂(gueP (d.L n) (d.W n)) :=
      integral_mono
        (GUETranslation_integrable_kPoint _ hmeas Hh k hQ.1.continuous
          (fun x => by simpa [Real.norm_eq_abs] using hBQ x) 0)
        (GUETranslation_integrable_kPoint _ hmeas Hh k hcont'
          (fun x => by simpa [Real.norm_eq_abs] using hBQ' _) 0)
        (fun y => GUETranslation_kPoint_mono k (fun β => hdom (ρs n) hρsI β) 0 _)
    have hcorrQ : corrQ ≤ GQ n + 1 := by
      have h2 : GQ n = ∫ y, kPoint k (fun β => Q' (fun j => ρ₀ * β j)) 0
          (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)) := rfl
      linarith
    have hGQ0 : 0 ≤ GQ n :=
      GUETranslation_integral_kPoint_nonneg _ _ _ k (fun β => hQ'0 (fun j => ρ₀ * β j)) 0
    have hlip := hC (gueP (d.L n) (d.W n)) (dbmMat (d.L n) (d.W n) (v n) (tt n)) hmeas Hh 0 1 r
      ⟨by norm_num, by norm_num⟩ hrI
    have e1 : (fun β : Fin k → ℝ => O (fun j => (1 : ℝ) * β j)) = O := by
      funext β; congr 1; funext j; simp
    rw [e1, one_pow, one_mul] at hlip
    have hT1 : |Fv - r ^ k * A n| ≤ |C| * (mr n / ρ₁) * (GQ n + 1) := by
      rw [hAn]
      refine hlip.trans ?_
      rw [abs_sub_comm 1 r]
      calc C * |r - 1| * corrQ ≤ |C| * |r - 1| * corrQ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C)
              (abs_nonneg _)) hcorrQ0
        _ ≤ |C| * (mr n / ρ₁) * (GQ n + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr1 (abs_nonneg C)) hcorrQ hcorrQ0
              (by positivity)
    -- `|r^k - 1| ≤ Lc N^{-rate}`
    have hT2 : |r ^ k - 1| ≤ Lc * mr n := by
      have h := _root_.abs_pow_sub_pow_le (a := r) (b := 1) (n := k)
      rw [one_pow] at h
      have hmax : max |r| |(1 : ℝ)| ≤ 2 := by
        rw [abs_of_pos (by linarith [hrI.1] : (0 : ℝ) < r), abs_one]
        exact max_le hrI.2 (by norm_num)
      have hpow : max |r| |(1 : ℝ)| ^ (k - 1) ≤ 2 ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_right (abs_nonneg _)) hmax _
      refine h.trans ?_
      calc |r - 1| * k * max |r| |(1 : ℝ)| ^ (k - 1) ≤ (mr n / ρ₁) * k * 2 ^ (k - 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg k)) hpow
              (by positivity) (by positivity)
        _ = Lc * mr n := by rw [hLc_def]; ring
    -- the reference is bounded by a count
    have hT3 : |g'| ≤ Ga n :=
      GUETranslation_abs_integral_le_of_abs_le _ (GUETranslation_measurable_Xmat _ _)
        (Xmat_isHermitian (d.L n) (d.W n)) k (GUETranslation_isTestFun_dilate hO hc0)
        (GUETranslation_isTestFun_dilate hQa hc0) (fun β => hQaO _) 0
    -- assemble
    have hsplit : Fv - g' = (Fv - r ^ k * A n) + (r ^ k - 1) * (D + g') + D := by
      rw [hD]; ring
    have hmul : |(r ^ k - 1) * (D + g')| ≤ (Lc * mr n) * (|D| + Ga n) := by
      rw [abs_mul]
      exact mul_le_mul hT2 ((abs_add_le D g').trans (by linarith)) (abs_nonneg _)
        (by positivity)
    have heq : |C| * (mr n / ρ₁) * (GQ n + 1) + (Lc * mr n) * (|D| + Ga n) + |D| =
        |D| * (1 + Lc * mr n) + |C| / ρ₁ * (mr n * GQ n + mr n) + Lc * (mr n * Ga n) := by
      field_simp; ring
    rw [Real.norm_eq_abs, hF, hsplit]
    have h3 := abs_add_three (Fv - r ^ k * A n) ((r ^ k - 1) * (D + g')) D
    linarith
  have hU : Tendsto (fun n =>
      |A n - gue0 n| * (1 + Lc * mr n) + |C| / ρ₁ * (mr n * GQ n + mr n) +
        Lc * (mr n * Ga n)) atTop (𝓝 0) := by
    have hm0 : Tendsto mr atTop (𝓝 0) :=
      GUETranslation_rpow_tendsto_zero hd (by linarith : -(3 * τs / 8) < 0)
    have h := ((hA.abs.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hm0.const_mul Lc))).add
      ((hGc.add hm0).const_mul (|C| / ρ₁))).add (hGa.const_mul Lc)
    simpa using h
  exact squeeze_zero_norm' hbound hU


/-- The diagonal argument for a family of carriers `α n` (the GUE sample space
`Ω (d.L n) (d.W n)` depends on `n`): if every sequence eventually satisfying `A` eventually
satisfies `P`, then `P n z` holds eventually at every `z` with `A n z`. -/
private theorem GUETranslation_eventually_forall {α : ℕ → Type*} (A P : ∀ n, α n → Prop)
    (b : ∀ n, α n) (hb : ∀ᶠ n : ℕ in atTop, A n (b n))
    (hseq : ∀ f : ∀ n, α n, (∀ᶠ n : ℕ in atTop, A n (f n)) → ∀ᶠ n : ℕ in atTop, P n (f n)) :
    ∀ᶠ n : ℕ in atTop, ∀ z, A n z → P n z := by
  classical
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  let bad (n : ℕ) : Prop := ∃ z : α n, A n z ∧ ¬ P n z
  have hbad : ∃ᶠ n : ℕ in atTop, bad n :=
    hnot.mono fun n hn => by
      simp only [not_forall] at hn
      obtain ⟨z, ha1, hp⟩ := hn
      exact ⟨z, ha1, hp⟩
  let f (n : ℕ) : α n := if hn : bad n then hn.choose else b n
  have hf1 : ∀ᶠ n : ℕ in atTop, A n (f n) := by
    filter_upwards [hb] with n hbn
    by_cases hn : bad n
    · simpa [f, hn] using (hn.choose_spec : A n hn.choose ∧ ¬ P n hn.choose).1
    · simpa [f, hn] using hbn
  have hfP := hseq f hf1
  obtain ⟨n, hn, hp⟩ := (hbad.and_eventually hfP).exists
  have hfn : f n = hn.choose := by simp [f, hn]
  exact (hn.choose_spec : A n hn.choose ∧ ¬ P n hn.choose).2 (hfn ▸ hp)

/-- **Uniformity over the good event**, with `GUEGoodHighProb` for the nonemptiness of the good
event. -/
private theorem GUETranslation_uniform (hGood : GUEGoodHighProb) (hL32 : L32) (hGUE : GUELocal)
    (d : Sizes) (hd : Tendsto (fun n => d.size n) atTop atTop) {κ : ℝ} (hκ : 0 < κ) {τs : ℝ}
    (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ ω : Ω (d.L n) (d.W n), GUEGoodAt d n κ τs E₀ ω →
      |GUETranslation_Hs (d.L n) (d.W n) (ouTStar d τs n) E₀ k O ω -
        ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
          (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n))| ≤ ε := by
  classical
  -- the good event is nonempty for large `n`: its complement has measure `≤ N^{-1} < 1`
  have hex : ∀ᶠ n in atTop, ∃ ω : Ω (d.L n) (d.W n), GUEGoodAt d n κ τs E₀ ω := by
    filter_upwards [hGood hGUE d hd κ τs E₀ 1 hκ h0 h1 hE₀ one_pos] with n hn
    by_contra hne
    push Not at hne
    have huniv : {ω : Ω (d.L n) (d.W n) | ¬ GUEGoodAt d n κ τs E₀ ω} = Set.univ :=
      Set.eq_univ_of_forall fun ω => hne ω
    have hN9 := GUETranslation_Nr_ge_nine d n
    have hlt : ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
      rw [ENNReal.ofReal_lt_one, Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    rw [huniv, measure_univ] at hn
    exact absurd hn (not_le.mpr hlt)
  let b : ∀ n, Ω (d.L n) (d.W n) := fun n =>
    if h : ∃ ω : Ω (d.L n) (d.W n), GUEGoodAt d n κ τs E₀ ω then h.choose else fun _ => 0
  have hb1 : ∀ᶠ n in atTop, GUEGoodAt d n κ τs E₀ (b n) := by
    filter_upwards [hex] with n hn
    have hbN : b n = hn.choose := by simp only [b, hn, ↓reduceDIte]
    rw [hbN]; exact hn.choose_spec
  have h := GUETranslation_eventually_forall (fun n ω => GUEGoodAt d n κ τs E₀ ω)
    (fun n ω => |GUETranslation_Hs (d.L n) (d.W n) (ouTStar d τs n) E₀ k O ω -
      ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
        (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n))| ≤ ε) b hb1
    (fun f hf => by
      have hc := GUETranslation_core hL32 hGUE d hd hκ h0 h1 hE₀ k hO f hf
      filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact hn.le)
  filter_upwards [h] with n hn ω hω using hn ω hω

/-- **The GUE translation** (assuming `GUEGoodHighProb` through the hypothesis of
`GUETranslationRow`) with
internal time `τs = 1/2`. -/
theorem guetranslationRow : GUETranslationRow := by
  intro hGood hL32 hGUE d hd k κ hκ E hE O hO hOc
  have hO' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O := ⟨hO, hOc⟩
  obtain ⟨BO, hBO⟩ := hO.continuous.bounded_above_of_compact_support hOc
  have hBO' : ∀ x, |O x| ≤ BO := fun x => by simpa [Real.norm_eq_abs] using hBO x
  have hBO0 : 0 ≤ BO := (abs_nonneg _).trans (hBO' 0)
  set K0 : ℝ := 2 * BO with hK0
  have hK00 : 0 ≤ K0 := by positivity
  -- it suffices to show the difference in the order `GUE(E, O) - GUE(0, O(ρ_sc(0)/ρ_sc(E) ·))`
  suffices hmain : Tendsto (fun n =>
      (∫ ω, kPoint k O E (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
          ∂(gueP (d.L n) (d.W n))) -
      (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
          (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues ∂(gueP (d.L n) (d.W n))))
      atTop (𝓝 0) by
    have h := hmain.neg
    rw [neg_zero] at h
    exact h.congr fun n => by ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hunif := GUETranslation_uniform hGood hL32 hGUE d hd hκ (τs := 1 / 2) (by norm_num)
    (by norm_num) hE k hO' (ε / 2) (half_pos hε)
  have hbadP := hGood hGUE d hd κ (1 / 2) E ((k + 1 : ℕ) : ℝ) hκ (by norm_num) (by norm_num) hE
    (by positivity)
  have hsmall : ∀ᶠ n in atTop, K0 / ((d.size n : ℕ) : ℝ) < ε / 2 :=
    (tendsto_const_nhds.div_atTop (GUETranslation_Nr_tendsto hd)).eventually
      (gt_mem_nhds (half_pos hε))
  filter_upwards [hunif, hbadP, hsmall] with n hU hB hS
  have hNpos := GUETranslation_Nr_pos d n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hT0 : 0 ≤ ouTStar d (1 / 2) n := Real.rpow_nonneg hNpos.le _
  rw [Real.dist_eq, sub_zero, GUETranslation_integral_gue (d.L n) (d.W n) hT0 E k hO']
  set c := ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
    (Xmat_isHermitian (d.L n) (d.W n) y).eigenvalues ∂(gueP (d.L n) (d.W n)) with hc_def
  set F : Ω (d.L n) (d.W n) → ℝ :=
    GUETranslation_Hs (d.L n) (d.W n) (ouTStar d (1 / 2) n) E k O with hF_def
  have hFb : ∀ ω, |F ω| ≤ N ^ k * BO := fun ω => by
    have h := GUETranslation_abs_integral_kPoint_le (gueP (d.L n) (d.W n)) _
      (dbmMat_isHermitian (d.L n) (d.W n) (vGUE d n (1 / 2) E ω)
        (1 - Real.exp (-(ouTStar d (1 / 2) n)))) k hBO' 0
    rwa [GUETranslation_card_real] at h
  have hc : |c| ≤ N ^ k * BO := by
    have h := GUETranslation_abs_integral_kPoint_le (gueP (d.L n) (d.W n)) (Xmat (d.L n) (d.W n))
      (Xmat_isHermitian (d.L n) (d.W n)) k
      (P := fun α => O ((rhoSC 0 / rhoSC E) • α)) (fun x => hBO' _) 0
    rwa [GUETranslation_card_real] at h
  have hFm : Measurable F :=
    GUETranslation_measurable_Hs (d.L n) (d.W n) (ouTStar d (1 / 2) n) E k hO.continuous
  have hFint : Integrable F (gueP (d.L n) (d.W n)) :=
    Integrable.of_bound hFm.aestronglyMeasurable (N ^ k * BO)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb ω)
  have hsplit : ∫ ω, F ω ∂(gueP (d.L n) (d.W n)) - c =
      ∫ ω, (F ω - c) ∂(gueP (d.L n) (d.W n)) := by
    rw [integral_sub hFint (integrable_const c), integral_const, probReal_univ, one_smul]
  rw [hsplit]
  refine abs_integral_le_integral_abs.trans_lt ?_
  set T := toMeasurable (gueP (d.L n) (d.W n)) {ω | ¬ GUEGoodAt d n κ (1 / 2) E ω} with hT_def
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hsubT : {ω | ¬ GUEGoodAt d n κ (1 / 2) E ω} ⊆ T := subset_toMeasurable _ _
  set X : ℝ := N ^ k * BO + |c| with hX
  have hX0 : 0 ≤ X := by positivity
  have hpt : ∀ ω, |F ω - c| ≤ ε / 2 + T.indicator (fun _ => X) ω := by
    intro ω
    by_cases hω : GUEGoodAt d n κ (1 / 2) E ω
    · have h2 : 0 ≤ T.indicator (fun _ => X) ω := Set.indicator_nonneg (fun _ _ => hX0) _
      linarith [hU ω hω]
    · rw [Set.indicator_of_mem (hsubT hω)]
      have := abs_sub (F ω) c
      linarith [hFb ω]
  have hint : ∫ ω, |F ω - c| ∂(gueP (d.L n) (d.W n)) ≤
      ε / 2 + (gueP (d.L n) (d.W n)).real T * X := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      ((integrable_const _).add ((integrable_const _).indicator hTm))
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm), integral_const,
      integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
  have hTreal : (gueP (d.L n) (d.W n)).real T ≤ N ^ (-((k + 1 : ℕ) : ℝ)) := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hB
  have hXle : X ≤ K0 * N ^ k := by
    have e : K0 * N ^ k = N ^ k * BO + N ^ k * BO := by rw [hK0]; ring
    rw [hX, e]; linarith
  have hfinal : (gueP (d.L n) (d.W n)).real T * X ≤ K0 / N := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast] at hTreal
    calc (gueP (d.L n) (d.W n)).real T * X ≤ (N ^ (k + 1))⁻¹ * (K0 * N ^ k) :=
          mul_le_mul hTreal hXle hX0 (by positivity)
      _ = K0 / N := by rw [pow_succ]; field_simp
  linarith

/-! ## `Infty1Row` from `step1Band`, `GUETranslation` and the good event -/

/-- **`Infty1Row`** from `step1Band`, `GUETranslation` and the
subtraction of the common reference: `(𝐇_{t*} − GUE_0^{dil}) + (GUE_0^{dil} − GUE_E)`.
`τ₁ := min 𝔠 (1/2)` (`step1Band` asks `τ_U < 1`, `τ_U ≤ 𝔠`). -/
theorem infty1Row_of_translation (hT : GUETranslation) : Infty1Row := by
  intro h32 hloc hGUE 𝔠 h𝔠 d hd k κ hκ E hE O hO hOc
  refine ⟨min 𝔠 (1 / 2), lt_min h𝔠 (by norm_num), fun τU hτU hle => ?_⟩
  have hband := step1Band h32 hloc hGUE 𝔠 h𝔠 d hd k κ hκ E hE O hO hOc τU hτU
    (lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)) (hle.trans (min_le_left _ _))
  have hgue := hT h32 hGUE d hd.1 k κ hκ E hE O hO hOc
  have h := hband.add hgue
  rw [add_zero] at h
  refine h.congr fun n => ?_
  ring

/-- `Infty1Row` from `guetranslationRow`, `gueGoodHighProb` and `step1Band`. -/
theorem infty1Row_of_pins (h8b : GUETranslationRow) : Infty1Row :=
  infty1Row_of_translation (h8b gueGoodHighProb)

/-- **`Infty1Row` proved**: `step1Band` plus `gueGoodHighProb` and `guetranslationRow` above. -/
theorem infty1Row : Infty1Row := infty1Row_of_pins guetranslationRow


end RBM.Univ
