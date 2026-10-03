/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.OU
import RBM2D.Universality.InjSum
import RBM2D.Green.FlucAvg

/-!
# The a priori bound `AprioriRow`

From the endpoint `locSC` (kept as the hypothesis of `AprioriRow`) we prove
`E (Im m_0(E + i/N))^p ≤ N^ε` eventually, for every bulk `E`.

Proof outline: law transfer `seqXmat_map_eq_ouMat_zero`; deterministic bounds `0 ≤ Im m ≤ 1/η`
and `η Im m(E + iη)` nondecreasing in `η` (`stieltjesN_eta_mul_im_mono`); the good event of
`(G_bound)` at `z₁ = E + i N^{-1+τ}` gives `Im m(z₀) ≤ 2 N^τ`; the bad event has probability
`≤ N^{-(p+1)}` and there `Im m(z₀) ≤ N`.  Only the `(G_bound)` half of `locSC` is used.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal

/-! ### Deterministic facts -/

private theorem apriori_im_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    0 ≤ (stieltjesN H (E + η * Complex.I)).im ∧
      (stieltjesN H (E + η * Complex.I)).im ≤ 1 / η := by
  rw [stieltjesN_im_eq_normalized_specWeight H hH E η hη]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · refine mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun l _ => ?_)
    positivity
  · calc (Fintype.card ι : ℝ)⁻¹ * ∑ l : ι, (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _l : ι, (1 / η) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (inv_nonneg.2 hc.le)
          rw [div_le_div_iff₀ (by positivity) hη]
          nlinarith [sq_nonneg (hH.eigenvalues l - E)]
      _ = 1 / η := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `(W^τ / √Meta) ≤ 1` at `Im z = N^{-1+τ}`, `N = W² L²`. -/
private theorem apriori_ratio_le_one (L W : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (N : ℝ) (hN : N = (W : ℝ) ^ 2 * (L : ℝ) ^ 2) (z : ℂ)
    (hz : z.im = N ^ (-1 + τ)) :
    (W : ℝ) ^ τ / Real.sqrt (Meta L W z) ≤ 1 := by
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNpos : 0 < N := by rw [hN]; positivity
  have hη : 0 < z.im := by rw [hz]; exact Real.rpow_pos_of_pos hNpos _
  set η := z.im with hηdef
  set m := min (η ^ (-(1 / 2 : ℝ))) (L : ℝ) with hm
  have hmpos : 0 < m := lt_min (Real.rpow_pos_of_pos hη _) (by linarith)
  have hwτ : 0 < (W : ℝ) ^ τ := Real.rpow_pos_of_pos (by linarith) _
  have hsq : ((W : ℝ) ^ τ) ^ 2 ≤ Meta L W z := by
    have hMeta : (W : ℝ) ^ 2 * m ^ 2 * η ≤ Meta L W z := by
      unfold Meta ellz
      rw [← hηdef, ← hm]
      have : m ^ 2 ≤ (m + 1) ^ 2 := by nlinarith
      have h2 : (W : ℝ) ^ 2 * m ^ 2 ≤ (W : ℝ) ^ 2 * (m + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      exact mul_le_mul_of_nonneg_right h2 hη.le
    refine le_trans ?_ hMeta
    rcases le_total (η ^ (-(1 / 2 : ℝ))) (L : ℝ) with h | h
    · rw [hm, min_eq_left h]
      have h1 : (η ^ (-(1 / 2 : ℝ))) ^ 2 * η = 1 := by
        rw [sq, ← Real.rpow_add hη]
        norm_num
        exact Real.rpow_neg_one η ▸ inv_mul_cancel₀ hη.ne'
      have h2 : ((W : ℝ) ^ τ) ^ 2 ≤ (W : ℝ) ^ 2 := by
        have : (W : ℝ) ^ τ ≤ (W : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hw hτ1
        rw [Real.rpow_one] at this
        exact pow_le_pow_left₀ hwτ.le this 2
      calc ((W : ℝ) ^ τ) ^ 2 ≤ (W : ℝ) ^ 2 := h2
        _ = (W : ℝ) ^ 2 * ((η ^ (-(1 / 2 : ℝ))) ^ 2 * η) := by rw [h1, mul_one]
        _ = _ := by ring
    · rw [hm, min_eq_right h]
      have hNη : N * η = N ^ τ := by
        rw [hz]
        calc N * N ^ (-1 + τ) = N ^ (1 : ℝ) * N ^ (-1 + τ) := by rw [Real.rpow_one]
          _ = N ^ (1 + (-1 + τ)) := (Real.rpow_add hNpos _ _).symm
          _ = N ^ τ := by ring_nf
      have hwwN : (W : ℝ) * W ≤ N := by
        rw [hN]
        have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (W : ℝ)]
      have h3 : ((W : ℝ) * W) ^ τ ≤ N ^ τ :=
        Real.rpow_le_rpow (by positivity) hwwN hτ0.le
      have h4 : ((W : ℝ) * W) ^ τ = ((W : ℝ) ^ τ) ^ 2 := by
        rw [Real.mul_rpow (by positivity) (by positivity), sq]
      calc ((W : ℝ) ^ τ) ^ 2 ≤ N ^ τ := h4 ▸ h3
        _ = N * η := hNη.symm
        _ = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * η := by rw [hN]
  have hMpos : 0 < Meta L W z := lt_of_lt_of_le (by positivity) hsq
  have : (W : ℝ) ^ τ ≤ Real.sqrt (Meta L W z) := by
    apply Real.le_sqrt_of_sq_le hsq
  have hsqpos : 0 < Real.sqrt (Meta L W z) := Real.sqrt_pos.2 hMpos
  rw [div_le_one hsqpos]
  exact this

/-! ### Measurability and law transfer -/

private theorem apriori_measurable_inv_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
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

private theorem apriori_measurable_sub {ν : Type*} [Fintype ν] [DecidableEq ν] (z : ℂ) :
    Measurable fun M : Matrix ν ν ℂ => M - z • (1 : Matrix ν ν ℂ) := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  have h : (fun M : Matrix ν ν ℂ => (M - z • (1 : Matrix ν ν ℂ)) a b)
      = fun M => M a b - z * (1 : Matrix ν ν ℂ) a b := by
    funext M; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact ((measurable_pi_apply (X := fun _ : ν => ℂ) b).comp
    (measurable_pi_apply (X := fun _ : ν => ν → ℂ) a)).sub measurable_const

private theorem apriori_measurable_g {ν : Type*} [Fintype ν] [DecidableEq ν] (z : ℂ) (p : ℕ) :
    Measurable fun M : Matrix ν ν ℂ => (stieltjesN M z).im ^ p := by
  have h1 : Measurable fun M : Matrix ν ν ℂ => stieltjesN M z := by
    unfold stieltjesN
    refine Measurable.const_mul ?_ _
    simp only [Matrix.trace, Matrix.diag, green]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact apriori_measurable_inv_apply (apriori_measurable_sub z) i i
  exact (Complex.measurable_im.comp h1).pow_const p

private theorem apriori_measurable_seqXmat (d : Sizes) (n : ℕ) : Measurable (seqXmat d n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_Xentry (d.L n) (d.W n) i j).comp (measurable_slice d n)

/-- The shifted point `z₀ = E + i/N`, written as in `AprioriImM`. -/
private def aprioriZ0 (d : Sizes) (n : ℕ) (E : ℝ) : ℂ :=
  (E : ℂ) + ((((d.size n : ℕ) : ℝ))⁻¹ : ℂ) * Complex.I

private theorem apriori_transfer (d : Sizes) (n : ℕ) (E : ℝ) (p : ℕ) :
    ∫ ω, (stieltjesN (ouMat (d.L n) (d.W n) 0 ω) (aprioriZ0 d n E)).im ^ p
        ∂(ouP (d.L n) (d.W n)) =
      ∫ ω, (stieltjesN (seqXmat d n ω) (aprioriZ0 d n E)).im ^ p ∂(seqP d) := by
  have hg := apriori_measurable_g (ν := Idx (d.L n) (d.W n)) (aprioriZ0 d n E) p
  have h1 := integral_map (measurable_ouMat (d.L n) (d.W n) 0).aemeasurable
    (μ := ouP (d.L n) (d.W n)) (f := fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      (stieltjesN M (aprioriZ0 d n E)).im ^ p) hg.aestronglyMeasurable
  have h2 := integral_map (apriori_measurable_seqXmat d n).aemeasurable
    (μ := seqP d) (f := fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      (stieltjesN M (aprioriZ0 d n E)).im ^ p) hg.aestronglyMeasurable
  rw [← h1, ← h2, seqXmat_map_eq_ouMat_zero]

/-! ### Size facts -/

private theorem apriori_size_pos (d : Sizes) (n : ℕ) : 0 < d.size n := by
  have h1 := d.W_pos n
  have h2 := d.three_le_L n
  unfold Sizes.size
  positivity

private theorem apriori_nonempty (d : Sizes) (n : ℕ) : Nonempty (Idx (d.L n) (d.W n)) :=
  Fintype.card_pos_iff.1 (by
    rw [RBM.Green.flucAvg_card_Idx_eq_size]; exact apriori_size_pos d n)

/-- `0 ≤ Im m(z₀) ≤ N`. -/
private theorem apriori_F_bounds (d : Sizes) (n : ℕ) (E : ℝ) (ω : SeqΩ d) :
    0 ≤ (stieltjesN (seqXmat d n ω) (aprioriZ0 d n E)).im ∧
      (stieltjesN (seqXmat d n ω) (aprioriZ0 d n E)).im ≤ ((d.size n : ℕ) : ℝ) := by
  have := apriori_nonempty d n
  have hN : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by exact_mod_cast apriori_size_pos d n
  have hz : aprioriZ0 d n E = (E : ℂ) + (((((d.size n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * Complex.I := by
    unfold aprioriZ0; push_cast; rfl
  rw [hz]
  have := apriori_im_bounds (seqXmat d n ω) (seqXmat_isHermitian d n ω) E
    (((d.size n : ℕ) : ℝ))⁻¹ (inv_pos.2 hN)
  rwa [one_div, inv_inv] at this

/-- On the good event of `(G_bound)` at `z₁ = E + i N^{-1+τ}`: `Im m(z₀) ≤ 2 N^τ`. -/
private theorem apriori_good_bound (d : Sizes) (n : ℕ) (E τ : ℝ) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (ω : SeqΩ d)
    (hgood : ∀ x y : Idx (d.L n) (d.W n),
      ‖Gn d n ω ((E : ℂ) + ((((d.size n : ℕ) : ℝ) ^ (-1 + τ) : ℝ) : ℂ) * Complex.I) x y -
          (if x = y then mSC ((E : ℂ) + ((((d.size n : ℕ) : ℝ) ^ (-1 + τ) : ℝ) : ℂ) *
            Complex.I) else 0)‖ ≤
        (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n)
          ((E : ℂ) + ((((d.size n : ℕ) : ℝ) ^ (-1 + τ) : ℝ) : ℂ) * Complex.I))) :
    (stieltjesN (seqXmat d n ω) (aprioriZ0 d n E)).im ≤ 2 * ((d.size n : ℕ) : ℝ) ^ τ := by
  have := apriori_nonempty d n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast apriori_size_pos d n
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast apriori_size_pos d n
  set η₁ : ℝ := N ^ (-1 + τ) with hη₁
  have hη₁pos : 0 < η₁ := Real.rpow_pos_of_pos hNpos _
  have hle : N⁻¹ ≤ η₁ := by
    rw [hη₁, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  set H := seqXmat d n ω with hH
  have hmono := stieltjesN_eta_mul_im_mono H (seqXmat_isHermitian d n ω) E N⁻¹ η₁
    (inv_pos.2 hNpos) hle
  have hz : aprioriZ0 d n E = (E : ℂ) + ((N⁻¹ : ℝ) : ℂ) * Complex.I := by
    unfold aprioriZ0; rw [hNdef]; push_cast; rfl
  set z₁ : ℂ := (E : ℂ) + (η₁ : ℂ) * Complex.I with hz₁
  -- `Im m(z₁) ≤ 2`
  have hz₁im : z₁.im = η₁ := by simp [hz₁]
  have hmsc : ‖mSC z₁‖ < 1 := by
    rw [mSC_eq_msc (by rw [hz₁im]; exact hη₁pos)]
    exact norm_msc_lt_one (by rw [hz₁im]; exact hη₁pos)
  have hcard : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = N := by
    rw [RBM.Green.flucAvg_card_Idx_eq_size]
  have hnorm : ‖stieltjesN H z₁‖ ≤ 2 := by
    unfold stieltjesN
    rw [norm_mul, norm_inv, Complex.norm_natCast, hcard]
    have hdiag : ‖(green H z₁).trace‖ ≤ 2 * N := by
      calc ‖(green H z₁).trace‖ ≤ ∑ i, ‖(green H z₁) i i‖ := by
            unfold Matrix.trace; exact norm_sum_le _ _
        _ ≤ ∑ _i : Idx (d.L n) (d.W n), (2 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := hgood i i
            have hG : Gn d n ω z₁ i i = (green H z₁) i i := rfl
            simp only [↓reduceIte] at h1
            rw [hG] at h1
            have h2 : ‖(green H z₁) i i‖ ≤ ‖(green H z₁) i i - mSC z₁‖ + ‖mSC z₁‖ := by
              have := norm_add_le ((green H z₁) i i - mSC z₁) (mSC z₁)
              simpa using this
            have h3 : (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z₁) ≤ 1 :=
              apriori_ratio_le_one (d.L n) (d.W n) (d.W_pos n) (by have := d.three_le_L n; omega)
                τ hτ0 hτ1 N (by rw [hNdef, Sizes.size_eq]; push_cast; ring) z₁
                (by rw [hz₁im])
            linarith
        _ = 2 * N := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
    calc N⁻¹ * ‖(green H z₁).trace‖ ≤ N⁻¹ * (2 * N) :=
          mul_le_mul_of_nonneg_left hdiag (inv_nonneg.2 hNpos.le)
      _ = 2 := by field_simp
  have him2 : (stieltjesN H z₁).im ≤ 2 :=
    (Complex.im_le_norm _).trans hnorm
  rw [hz]
  have hNη : N * η₁ = N ^ τ := by
    rw [hη₁]
    calc N * N ^ (-1 + τ) = N ^ (1 : ℝ) * N ^ (-1 + τ) := by rw [Real.rpow_one]
      _ = N ^ (1 + (-1 + τ)) := (Real.rpow_add hNpos _ _).symm
      _ = N ^ τ := by ring_nf
  have h5 : (stieltjesN H ((E : ℂ) + ((N⁻¹ : ℝ) : ℂ) * Complex.I)).im ≤
      N * (η₁ * (stieltjesN H z₁).im) := by
    have := mul_le_mul_of_nonneg_left hmono hNpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at this
    exact this
  calc _ ≤ N * (η₁ * (stieltjesN H z₁).im) := h5
    _ = N ^ τ * (stieltjesN H z₁).im := by rw [← hNη]; ring
    _ ≤ N ^ τ * 2 := mul_le_mul_of_nonneg_left him2 (Real.rpow_nonneg hNpos.le _)
    _ = 2 * N ^ τ := by ring

/-! ### The a priori bound -/

/-- **The a priori bound `AprioriRow`**: from `locSC`,
`E (Im m_0(E + i/N))^p ≤ N^ε` eventually, for every bulk `E`. -/
theorem aprioriRow : AprioriRow := by
  intro hloc 𝔠 h𝔠 d hd κ hκ E hE p ε hε
  set τ : ℝ := min (ε / (2 * ((p : ℝ) + 1))) (1 / 2) with hτdef
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hτ0 : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτ12 : τ ≤ 1 / 2 := min_le_right _ _
  have hpτ : (p : ℝ) * τ ≤ ε / 2 := by
    have h1 : τ ≤ ε / (2 * ((p : ℝ) + 1)) := min_le_left _ _
    calc (p : ℝ) * τ ≤ (p : ℝ) * (ε / (2 * ((p : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg p)
      _ = ε / 2 * ((p : ℝ) / ((p : ℝ) + 1)) := by field_simp
      _ ≤ ε / 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hp1]; linarith
      _ = ε / 2 := mul_one _
  have hev := hloc 𝔠 h𝔠 d hd κ τ ((p : ℝ) + 1) hκ hτ0 hp1
  have hNtend : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd.1
  have hbig : ∀ᶠ n in atTop, (2 ^ p + 1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNtend).eventually_ge_atTop _
  have hN1' : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hNtend.eventually_ge_atTop 1
  filter_upwards [hev, hbig, hN1'] with n hn hbig hN1
  refine le_of_eq_of_le (apriori_transfer d n E p) ?_
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  set η₁ : ℝ := N ^ (-1 + τ) with hη₁
  have hη₁pos : 0 < η₁ := Real.rpow_pos_of_pos hNpos _
  set z₁ : ℂ := (E : ℂ) + (η₁ : ℂ) * Complex.I with hz₁
  have hdom : locDomain (d.size n) κ τ z₁ := by
    refine ⟨?_, ?_, ?_⟩
    · have : z₁.re = E := by simp [hz₁]
      rw [this]; have := abs_le.1 hE; rw [abs_le]; constructor <;> linarith
    · have : z₁.im = η₁ := by simp [hz₁]
      rw [this]
    · have : z₁.im = η₁ := by simp [hz₁]
      rw [this, hη₁]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hprob := (hn z₁ hdom).1
  set Bset := {ω : SeqΩ d | ¬ ∀ x y : Idx (d.L n) (d.W n),
      ‖Gn d n ω z₁ x y - (if x = y then mSC z₁ else 0)‖ ≤
        (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z₁)} with hBset
  set B' := toMeasurable (seqP d) Bset with hB'
  have hB'meas : MeasurableSet B' := measurableSet_toMeasurable _ _
  set c : ℝ := (2 * N ^ τ) ^ p with hc
  have hc0 : 0 ≤ c := by positivity
  set F : SeqΩ d → ℝ := fun ω => (stieltjesN (seqXmat d n ω) (aprioriZ0 d n E)).im with hF
  have hpt : ∀ ω, F ω ^ p ≤ c + N ^ p * B'.indicator 1 ω := by
    intro ω
    obtain ⟨hF0, hFN⟩ := apriori_F_bounds d n E ω
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω]
      have : F ω ^ p ≤ N ^ p := pow_le_pow_left₀ hF0 hFN p
      simp only [Pi.one_apply, mul_one]
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hω' : ω ∉ Bset := fun h => hω (subset_toMeasurable _ _ h)
      have hgood : ∀ x y : Idx (d.L n) (d.W n),
          ‖Gn d n ω z₁ x y - (if x = y then mSC z₁ else 0)‖ ≤
            (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z₁) := by
        by_contra hcon
        exact hω' hcon
      have := apriori_good_bound d n E τ hτ0 (by linarith) ω hgood
      have h2 : F ω ^ p ≤ (2 * N ^ τ) ^ p := pow_le_pow_left₀ hF0 this p
      simp only [mul_zero, add_zero]
      exact h2
  have hint : Integrable (fun ω => c + N ^ p * B'.indicator (1 : SeqΩ d → ℝ) ω) (seqP d) := by
    refine (integrable_const c).add (Integrable.const_mul ?_ _)
    exact (integrable_const (1 : ℝ)).indicator hB'meas
  have hmain : ∫ ω, F ω ^ p ∂(seqP d) ≤
      ∫ ω, (c + N ^ p * B'.indicator (1 : SeqΩ d → ℝ) ω) ∂(seqP d) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hint
      (Filter.Eventually.of_forall hpt)
    exact pow_nonneg (apriori_F_bounds d n E ω).1 p
  have hval : ∫ ω, (c + N ^ p * B'.indicator (1 : SeqΩ d → ℝ) ω) ∂(seqP d) =
      c + N ^ p * (seqP d).real B' := by
    have hI : Integrable (B'.indicator (1 : SeqΩ d → ℝ)) (seqP d) :=
      (integrable_const (1 : ℝ)).indicator hB'meas
    rw [integral_add (integrable_const c) (hI.const_mul _), integral_const_mul,
      integral_indicator_one hB'meas]
    simp
  have hreal : (seqP d).real B' ≤ N ^ (-((p : ℝ) + 1)) := by
    unfold Measure.real
    rw [hB', measure_toMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)] at this
  have hbad : N ^ p * (seqP d).real B' ≤ 1 := by
    calc N ^ p * (seqP d).real B' ≤ N ^ p * N ^ (-((p : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = N ^ (-1 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hgoodc : c ≤ 2 ^ p * N ^ (ε / 2) := by
    rw [hc, mul_pow, ← Real.rpow_natCast (N ^ τ) p, ← Real.rpow_mul hNpos.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    rw [mul_comm]; exact hpτ
  have hX1 : (1 : ℝ) ≤ N ^ (ε / 2) := Real.one_le_rpow hN1 (by positivity)
  have hNε : N ^ ε = N ^ (ε / 2) * N ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have h2p : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc ∫ ω, F ω ^ p ∂(seqP d) ≤ c + N ^ p * (seqP d).real B' := hmain.trans hval.le
    _ ≤ 2 ^ p * N ^ (ε / 2) + 1 := add_le_add hgoodc hbad
    _ ≤ (2 ^ p + 1) * N ^ (ε / 2) := by nlinarith
    _ ≤ N ^ (ε / 2) * N ^ (ε / 2) := mul_le_mul_of_nonneg_right hbig (by linarith)
    _ = N ^ ε := hNε.symm

end RBM.Univ

