/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUELocalBootstrap
import RBM2D.Universality.GUEPhase.AuxCarrier
import RBM2D.Universality.EigenInterlacing
import RBM2D.Green.Minor
import RBM2D.Green.LDE
import RBM2D.Green.LDEQuadInst
import RBM2D.Green.Pins

/-!
# The GUE local law from the Schur tail: the probabilistic input

Goals: the statement `GUESchurTail` (`Universality/GUELocalBootstrap.lean`, the probabilistic input
of the GUE local law) and, with the deterministic bootstrap `GUELocal_of_tail`, the statement
`GUELocal` of `Universality/Pins.lean`, the weak averaged bulk local law
`|m_N(z) - m_sc(z)| ≤ N^τ (N Im z)^{-1/2}` of the `N × N` GUE, `N = (W L)²` (not stated in the
paper: the proof of `Thm: B_Univ` cites only `MR:locSC` and [32]).  Both are proved without
hypotheses: `gueSchurTail : GUESchurTail` and `gueLocal : GUELocal`.

Proof outline, for `H = Xmat` under `gueP`, `G = green H z`,
`G⁽ⁱ⁾ = green (H.submatrix val val) z` on `{a // a ≠ i}`,
`Q_i = ∑_{k,l ≠ i} H_{ik} G⁽ⁱ⁾_{kl} H_{li}`, `M = N = (W L)²`, `η = Im z`, `a = N^{ε/2}`
(so `a² = N^ε`).

* Deterministic part.  `schurErr_eq`: the Schur identity
  `Υ_i = H_ii - (Q_i - N⁻¹ tr G⁽ⁱ⁾) + N⁻¹ (tr G - tr G⁽ⁱ⁾)` (`Green.green_diag_paper`,
  `Green.inv_minor_resolvent`, `Green.green_diag_ne_zero`); `trace_diff_le`:
  `‖tr G - tr G⁽ⁱ⁾‖ ≤ (π + 1)/η` (`trace_green_submatrix_sub_le`, card difference 1);
  `ward_sum`: `η ∑_{kl} |G⁽ⁱ⁾_{kl}|² = Im tr G⁽ⁱ⁾` (`Green.im_green_diag` summed over the columns);
  `schur_arith`, `schurErr_le_of_good`: on `|H_ii| ≤ a N^{-1/2}`,
  `|Q_i - N⁻¹ tr G⁽ⁱ⁾|² ≤ a² N⁻² ∑_{kl} |G⁽ⁱ⁾_{kl}|²`, `Im m_N ≤ 2`, `a ≥ 5`, the Schur error is
  at most `schurBud N ε z`.  No lower bound on `N η` is used.
* The diagonal tail.  `gaussianReal_tail`: `P(|g| > t) ≤ 2 exp(-t²/(2v))` for a centred real
  Gaussian of variance `v` (Chernoff bound from Mathlib's `mgf_id_gaussianReal`);
  `gueP_diag_tail`: `Xmat ω i i` is the single coordinate `ω (i, i, true)`, of law
  `gaussianReal 0 (gueVar (i,i,true)) = N(0, N⁻¹)`, so `P(|H_ii| > t) ≤ 2 exp(-t² N/2)`.
* The union bound.  `schur_union_bound`: for a finite `Γ ⊂ {Im z > 0}`, the probability that
  for some `z ∈ Γ`, some row `i`, `Im m_N ≤ 2` and the Schur error exceeds the budget with
  `a ≥ 5` is at most `|Γ| N (2 exp(-a²/2) + A_{q'}/(a²)^{q'+1})`, by subadditivity
  (`measure_biUnion_finset_le`, `measure_iUnion_fintype_le`), `gueP_diag_tail` and `gue_quad_tail`
  (`AuxCarrier.lean`) at `lam = a²`; no measurability is needed.
* The constants.  `final_arith`: with `q' ≥ (q + D + 2)/ε - 1`, `|Γ| ≤ N^q`, and
  `N^{q+1+D} exp(-N^ε/2) ≤ 1/4`, `2 A_{q'} ≤ N`, the union bound is at most `N^{-D}`.
* The conclusion: `gueSchurTail`, `gueLocal := GUELocal_of_tail gueSchurTail`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

section Det

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The minor `H^{(i)}` (delete row and column `i`). -/
private abbrev minorOf (H : Matrix ι ι ℂ) (i : ι) :
    Matrix {a : ι // a ≠ i} {a : ι // a ≠ i} ℂ :=
  H.submatrix Subtype.val Subtype.val

/-- **The Schur identity** (deterministic):
`Υ_i = H_ii - (Q_i - N⁻¹ tr G^{(i)}) + N⁻¹ (tr G - tr G^{(i)})`. -/
private theorem schurErr_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (i : ι) :
    schurErr H z i =
      H i i - ((∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
          H i k.1 * green (minorOf H i) z k l * H l.1 i)
        - (Fintype.card ι : ℂ)⁻¹ * (green (minorOf H i) z).trace)
      + (Fintype.card ι : ℂ)⁻¹ *
          ((green H z).trace - (green (minorOf H i) z).trace) := by
  have hdet : IsUnit (H - z • (1 : Matrix ι ι ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz)
  have hG := RBM.Green.green_diag_ne_zero hH hz i
  have h1 := RBM.Green.green_diag_paper hdet i hG
  have h2 : RBM.Green.minorGreen (green H z) i = green (minorOf H i) z :=
    (RBM.Green.inv_minor_resolvent hdet i hG).symm
  have h3 : (green H z i i)⁻¹ = H i i - z - ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
        H i k.1 * green (minorOf H i) z k l * H l.1 i := by
    rw [h1, inv_inv, h2]
  unfold schurErr stieltjesN
  rw [h3]
  ring

/-- **The Ward identity**: `η ∑_{k,l} |G_{kl}|² = Im tr G`. -/
private theorem ward_sum {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    z.im * ∑ k, ∑ l, ‖green H z k l‖ ^ 2 = (green H z).trace.im := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have key : ∀ i, (green H z i i).im = z.im * ∑ k, ‖green H z k i‖ ^ 2 := by
    intro i
    rw [RBM.Green.im_green_diag hH hz0 i]
    congr 1
    rw [Matrix.mulVec_single_one]
    simp only [dotProduct, Pi.star_apply, Matrix.col_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := Complex.conj_mul' (green H z k i)
    rw [show star (green H z k i) = (starRingEnd ℂ) (green H z k i) from rfl, h]
    norm_cast
  have htr : (green H z).trace.im = ∑ i, (green H z i i).im := by
    simp [Matrix.trace, Complex.im_sum]
  rw [htr]
  simp_rw [key]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- The trace difference: `‖tr G - tr G^{(i)}‖ ≤ (π + 1)/η` (interlacing, one row removed). -/
private theorem trace_diff_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (i : ι) :
    ‖(green H z).trace - (green (minorOf H i) z).trace‖ ≤ (Real.pi + 1) / z.im := by
  have h := trace_green_submatrix_sub_le hH (Function.Embedding.subtype (fun a : ι => a ≠ i)) hz
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
  have hc : Fintype.card ι - Fintype.card {a : ι // a ≠ i} = 1 := by
    have h1 := Fintype.card_subtype_compl (fun x : ι => x = i)
    rw [Fintype.card_subtype_eq] at h1
    change Fintype.card {a : ι // a ≠ i} = Fintype.card ι - 1 at h1
    omega
  rw [hc] at h
  simpa using h

/-- The arithmetic core of the good-event bound (the arithmetic part of the proof outline), with
abstract data:
`schur = A - (Q - M⁻¹ t') + M⁻¹ (t - t')`, `|A| ≤ a/√M`, `|Q - M⁻¹ t'|² ≤ a² M⁻² S`,
`|t - t'| ≤ (π + 1)/η`, `η S = Im t'`, `t = M m`, `Im m ≤ 2`, `a ≥ 5`. -/
private theorem schur_arith {A Q t t' schur m : ℂ} {S η a : ℝ} {M : ℕ}
    (hM0 : (0 : ℝ) < M) (hη : 0 < η) (ha : 5 ≤ a)
    (hid : schur = A - (Q - (M : ℂ)⁻¹ * t') + (M : ℂ)⁻¹ * (t - t'))
    (hdiag : ‖A‖ ≤ a / Real.sqrt M)
    (hquad : ‖Q - (M : ℂ)⁻¹ * t'‖ ^ 2 ≤ a ^ 2 * (((M : ℝ)⁻¹) ^ 2 * S))
    (htd : ‖t - t'‖ ≤ (Real.pi + 1) / η)
    (hward : η * S = t'.im) (ht : t = (M : ℂ) * m) (hm : m.im ≤ 2) :
    ‖schur‖ ≤ a ^ 2 * (1 / Real.sqrt M + Real.sqrt (2 / (M * η)) + 1 / (M * η)) := by
  have hpi : Real.pi + 1 ≤ 5 := by linarith [Real.pi_le_four]
  have hmIm : t.im = M * m.im := by rw [ht]; simp
  -- `Im t' ≤ 2 M + 5/η`
  have hIm' : t'.im ≤ 2 * M + 5 / η := by
    have h1 : t'.im = t.im - (t - t').im := by simp
    have h3 : -‖t - t'‖ ≤ (t - t').im := by
      have := Complex.abs_im_le_norm (t - t')
      linarith [neg_abs_le (t - t').im]
    have h4 : t.im ≤ 2 * M := by rw [hmIm]; nlinarith
    have h5 : ‖t - t'‖ ≤ 5 / η := htd.trans (div_le_div_of_nonneg_right hpi hη.le)
    linarith
  have hS_le : S ≤ (2 * M + 5 / η) / η := by
    rw [le_div_iff₀ hη]
    calc S * η = η * S := by ring
      _ = t'.im := hward
      _ ≤ 2 * M + 5 / η := hIm'
  set u : ℝ := 1 / (M * η) with hu_def
  have hu : 0 < u := by positivity
  have hqb : ((M : ℝ)⁻¹) ^ 2 * S ≤ 2 * u + 5 * u ^ 2 := by
    have e : ((M : ℝ)⁻¹) ^ 2 * ((2 * M + 5 / η) / η) = 2 * u + 5 * u ^ 2 := by
      rw [hu_def]; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hS_le (by positivity)
  -- the quadratic part
  have hx2 : ‖Q - (M : ℂ)⁻¹ * t'‖ ^ 2 ≤ a ^ 2 * (2 * u + 5 * u ^ 2) :=
    hquad.trans (mul_le_mul_of_nonneg_left hqb (sq_nonneg a))
  set sq : ℝ := Real.sqrt (2 * u) with hsq_def
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hsq2 : sq ^ 2 = 2 * u := Real.sq_sqrt (by positivity)
  have hx : ‖Q - (M : ℂ)⁻¹ * t'‖ ≤ a * (sq + 3 * u) := by
    have hnn : 0 ≤ a * (sq + 3 * u) := by positivity
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).1 ?_
    calc ‖Q - (M : ℂ)⁻¹ * t'‖ ^ 2 ≤ a ^ 2 * (2 * u + 5 * u ^ 2) := hx2
      _ ≤ a ^ 2 * (sq ^ 2 + 6 * u * sq + 9 * u ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
          have : 0 ≤ 6 * u * sq + 4 * u ^ 2 := by positivity
          rw [hsq2]; linarith
      _ = (a * (sq + 3 * u)) ^ 2 := by ring
  -- the triangle inequality
  have hcn : ‖(M : ℂ)⁻¹‖ = (M : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have htri : ‖schur‖ ≤ ‖A‖ + ‖Q - (M : ℂ)⁻¹ * t'‖ + (M : ℝ)⁻¹ * ‖t - t'‖ := by
    rw [hid]
    calc ‖A - (Q - (M : ℂ)⁻¹ * t') + (M : ℂ)⁻¹ * (t - t')‖
        ≤ ‖A - (Q - (M : ℂ)⁻¹ * t')‖ + ‖(M : ℂ)⁻¹ * (t - t')‖ := norm_add_le _ _
      _ ≤ (‖A‖ + ‖Q - (M : ℂ)⁻¹ * t'‖) + ‖(M : ℂ)⁻¹ * (t - t')‖ := by
          gcongr
          exact norm_sub_le _ _
      _ = ‖A‖ + ‖Q - (M : ℂ)⁻¹ * t'‖ + (M : ℝ)⁻¹ * ‖t - t'‖ := by
          rw [norm_mul, hcn]
  have h5u : (M : ℝ)⁻¹ * ‖t - t'‖ ≤ 5 * u := by
    calc (M : ℝ)⁻¹ * ‖t - t'‖ ≤ (M : ℝ)⁻¹ * (5 / η) :=
          mul_le_mul_of_nonneg_left (htd.trans (div_le_div_of_nonneg_right hpi hη.le))
            (by positivity)
      _ = 5 * u := by rw [hu_def]; field_simp
  -- assemble
  have hr0 : 0 ≤ 1 / Real.sqrt M := by positivity
  have hdiag' : ‖A‖ ≤ a * (1 / Real.sqrt M) := by rwa [← div_eq_mul_one_div]
  have hu2 : 2 / ((M : ℝ) * η) = 2 * u := by rw [hu_def]; ring
  rw [hu2]
  have hfin : ‖schur‖ ≤ a * (1 / Real.sqrt M) + a * (sq + 3 * u) + 5 * u :=
    htri.trans (by linarith)
  have hA1 : 0 ≤ (a ^ 2 - a) * (1 / Real.sqrt M) := mul_nonneg (by nlinarith) hr0
  have hA2 : 0 ≤ (a ^ 2 - a) * sq := mul_nonneg (by nlinarith) hsq0
  have hA3 : 0 ≤ (a ^ 2 - 3 * a - 5) * u := mul_nonneg (by nlinarith) hu.le
  calc ‖schur‖ ≤ a * (1 / Real.sqrt M) + a * (sq + 3 * u) + 5 * u := hfin
    _ ≤ a ^ 2 * (1 / Real.sqrt M + sq + u) := by nlinarith

/-- **The deterministic bound on the good event** (the deterministic part of the proof outline): if
`|H_ii| ≤ a/√M`, `|Q_i - M⁻¹ tr G^{(i)}|² ≤ a² M⁻² ∑_{kl} |G^{(i)}_{kl}|²`, `Im m_N ≤ 2` and
`a ≥ 5`, then the Schur error is at most `a² (M^{-1/2} + (2/(M η))^{1/2} + (M η)⁻¹)`. -/
private theorem schurErr_le_of_good {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : ι) {M : ℕ} (hM : Fintype.card ι = M) {a : ℝ} (ha : 5 ≤ a)
    (hmim : (stieltjesN H z).im ≤ 2)
    (hdiag : ‖H i i‖ ≤ a / Real.sqrt M)
    (hquad : ‖(∑ k : {b : ι // b ≠ i}, ∑ l : {b : ι // b ≠ i},
          H i k.1 * green (minorOf H i) z k l * H l.1 i) -
        (((M : ℝ)⁻¹ : ℝ) : ℂ) * ∑ k : {b : ι // b ≠ i}, green (minorOf H i) z k k‖ ^ 2 ≤
      a ^ 2 * (((M : ℝ)⁻¹) ^ 2 * ∑ k : {b : ι // b ≠ i}, ∑ l : {b : ι // b ≠ i},
          ‖green (minorOf H i) z k l‖ ^ 2)) :
    ‖schurErr H z i‖ ≤ a ^ 2 * (1 / Real.sqrt M + Real.sqrt (2 / (M * z.im)) + 1 / (M * z.im)) := by
  have hM0 : (0 : ℝ) < M := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [hM] at this
    exact_mod_cast this
  have hcardC : (Fintype.card ι : ℂ) = (M : ℂ) := by rw [hM]
  have hcoef : ((((M : ℝ)⁻¹ : ℝ)) : ℂ) = (M : ℂ)⁻¹ := by push_cast; rfl
  have hid := schurErr_eq hH hz.ne' i
  rw [hcardC] at hid
  rw [hcoef] at hquad
  have ht : (green H z).trace = (M : ℂ) * stieltjesN H z := by
    have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    unfold stieltjesN
    rw [hcardC]
    field_simp
  exact schur_arith hM0 hz ha hid hdiag hquad (trace_diff_le hH hz i)
    (ward_sum (H := minorOf H i) (hH.submatrix _) hz) ht hmim

end Det

/-! ### The diagonal Gaussian tail -/

section DiagTail

/-- Chernoff bound, upper tail, for a centred real Gaussian. -/
private theorem gaussianReal_ge_le {v : ℝ≥0} {t s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- Chernoff bound, lower tail, for a centred real Gaussian. -/
private theorem gaussianReal_le_le {v : ℝ≥0} {t s : ℝ} (hs : s ≤ 0) :
    (gaussianReal 0 v).real {x : ℝ | x ≤ t} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- The two-sided Gaussian tail `P(|g| > t) ≤ 2 exp(-t²/(2v))`. -/
private theorem gaussianReal_tail {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    gaussianReal 0 v {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hsub : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    rcases lt_abs.1 (show t < |x| from hx) with h | h
    · exact Or.inl (show t ≤ x from h.le)
    · exact Or.inr (show x ≤ -t by linarith)
  have h1 : gaussianReal 0 v {x : ℝ | t ≤ x} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((gaussianReal_ge_le (t := t) (s := t / v)
      (by positivity)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  have h2 : gaussianReal 0 v {x : ℝ | x ≤ -t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((gaussianReal_le_le (t := -t) (s := -(t / v))
      (by have : 0 ≤ t / v := by positivity
          linarith)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  calc gaussianReal 0 v {x : ℝ | t < |x|}
      ≤ gaussianReal 0 v ({x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t}) := measure_mono hsub
    _ ≤ gaussianReal 0 v {x : ℝ | t ≤ x} + gaussianReal 0 v {x : ℝ | x ≤ -t} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) +
          ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- The diagonal entry of `Xmat` is one real coordinate. -/
private theorem Xmat_diag_eq (L W : ℕ) [NeZero L] [NeZero W] (ω : Ω L W) (i : Idx L W) :
    Xmat L W ω i i = ((ω (i, i, true) : ℝ) : ℂ) := by
  simp [Xmat, Xentry]

/-- **The diagonal tail**: under the GUE, `H_ii` is a centred real Gaussian of variance `N⁻¹`,
so `P(|H_ii| > t) ≤ 2 exp(-t² N/2)`, `N = (W L)²`. -/
private theorem gueP_diag_tail (L W : ℕ) [NeZero L] [NeZero W] (i : Idx L W) {t : ℝ} (ht : 0 < t) :
    Endpoints.gueP L W {ω | t < ‖Xmat L W ω i i‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) * ((((W * L) ^ 2 : ℕ) : ℝ)) / 2)) := by
  have hmeas : MeasurableSet {x : ℝ | t < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hset : {ω : Ω L W | t < ‖Xmat L W ω i i‖} =
      (fun ω : Ω L W => ω (i, i, true)) ⁻¹' {x : ℝ | t < |x|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Xmat_diag_eq, Complex.norm_real,
      Real.norm_eq_abs]
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  have hmap : (Endpoints.gueP L W).map (fun ω : Ω L W => ω (i, i, true)) =
      gaussianReal 0 (Endpoints.gueVar L W (i, i, true)) := Measure.infinitePi_map_eval _ _
  have hmeasf : Measurable (fun ω : Ω L W => ω (i, i, true)) := measurable_pi_apply _
  have hpre : Endpoints.gueP L W ((fun ω : Ω L W => ω (i, i, true)) ⁻¹' {x : ℝ | t < |x|}) =
      gaussianReal 0 (Endpoints.gueVar L W (i, i, true)) {x : ℝ | t < |x|} := by
    rw [← hmap, Measure.map_apply hmeasf hmeas]
  rw [hset, hpre]
  have hvar : Endpoints.gueVar L W (i, i, true) = ((((W * L) ^ 2 : ℕ) : ℝ≥0))⁻¹ := by
    simp [Endpoints.gueVar]
  rw [hvar]
  have hne : ((((W * L) ^ 2 : ℕ) : ℝ≥0))⁻¹ ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  refine (gaussianReal_tail hne ht).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  congr 2
  push_cast
  field_simp

end DiagTail

/-! ### The fixed-size union bound -/

section Union

/-- **The fixed-size union bound** (before the choice of the constants):
for a finite set `Γ` of points of the upper half plane and `a ≥ 5`, with `N = (W L)²`, the GUE
probability that for some `z ∈ Γ` and some row `i` the Schur error exceeds
`a² (N^{-1/2} + (2/(N Im z))^{1/2} + (N Im z)⁻¹)` while `Im m_N(z) ≤ 2`, is at most
`|Γ| N (2 exp(-a²/2) + A_{q'} / (a²)^{q'+1})`. -/
private theorem schur_union_bound (L W : ℕ) [NeZero L] [NeZero W] (Γ : Finset ℂ)
    (hΓ : ∀ z ∈ Γ, 0 < z.im) {a : ℝ} (ha : 5 ≤ a) (q' : ℕ) :
    Endpoints.gueP L W {ω | ∃ z ∈ Γ, ∃ i : Idx L W,
        (stieltjesN (Xmat L W ω) z).im ≤ 2 ∧
          a ^ 2 * (1 / Real.sqrt ((((W * L) ^ 2 : ℕ) : ℝ)) +
              Real.sqrt (2 / ((((W * L) ^ 2 : ℕ) : ℝ) * z.im)) +
              1 / ((((W * L) ^ 2 : ℕ) : ℝ) * z.im)) <
            ‖schurErr (Xmat L W ω) z i‖} ≤
      ENNReal.ofReal ((Γ.card : ℝ) * ((((W * L) ^ 2 : ℕ) : ℝ) *
        (2 * Real.exp (-(a ^ 2) / 2) + RBM.Green.hwConst q' / (a ^ 2) ^ (q' + 1)))) := by
  classical
  have ha0 : 0 < a := by linarith
  set M : ℕ := (W * L) ^ 2 with hM
  have hM0 : (0 : ℝ) < M := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  set A : ℝ := 2 * Real.exp (-(a ^ 2) / 2) with hA
  set B : ℝ := RBM.Green.hwConst q' / (a ^ 2) ^ (q' + 1) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by
    have := RBM.Green.hwConst_pos q'
    positivity
  -- the two bad events
  let E1 : Idx L W → Set (Ω L W) := fun i => {ω | a / Real.sqrt M < ‖Xmat L W ω i i‖}
  let E2 : ℂ → Idx L W → Set (Ω L W) := fun z i =>
    {s | a ^ 2 * ((((M : ℝ))⁻¹) ^ 2 *
        ∑ k : {b : Idx L W // b ≠ i}, ∑ l : {b : Idx L W // b ≠ i},
          ‖green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2) <
      ‖(∑ k : {b : Idx L W // b ≠ i}, ∑ l : {b : Idx L W // b ≠ i},
          Xmat L W s i k.1 * green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l *
            Xmat L W s l.1 i) -
        (((M : ℝ))⁻¹) * ∑ k : {b : Idx L W // b ≠ i},
          green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
  have hE1 : ∀ i, Endpoints.gueP L W (E1 i) ≤ ENNReal.ofReal A := by
    intro i
    have hsq : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
    refine (gueP_diag_tail L W i (div_pos ha0 hsq)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hA]
    congr 2
    rw [div_pow, Real.sq_sqrt hM0.le]
    field_simp
    rfl
  have hE2 : ∀ z ∈ Γ, ∀ i, Endpoints.gueP L W (E2 z i) ≤ ENNReal.ofReal B := by
    intro z hz i
    exact gue_quad_tail (hΓ z hz).ne' i (lam := a ^ 2) (by positivity) q'
  -- containment of the bad event
  have hsub : {ω | ∃ z ∈ Γ, ∃ i : Idx L W,
        (stieltjesN (Xmat L W ω) z).im ≤ 2 ∧
          a ^ 2 * (1 / Real.sqrt ((((W * L) ^ 2 : ℕ) : ℝ)) +
              Real.sqrt (2 / ((((W * L) ^ 2 : ℕ) : ℝ) * z.im)) +
              1 / ((((W * L) ^ 2 : ℕ) : ℝ) * z.im)) <
            ‖schurErr (Xmat L W ω) z i‖} ⊆ ⋃ z ∈ Γ, ⋃ i, (E1 i ∪ E2 z i) := by
    intro ω hω
    obtain ⟨z, hz, i, hm, hbad⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨z, hz, i, ?_⟩
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have hd : ‖Xmat L W ω i i‖ ≤ a / Real.sqrt M := not_lt.1 h1
    simp only [E2, Set.mem_ofPred_eq, not_lt] at h2
    have hle := schurErr_le_of_good (Xmat_isHermitian L W ω) (hΓ z hz) i (card_Idx L W) ha hm hd h2
    exact absurd hbad (not_lt.2 hle)
  have hpair : ∀ z ∈ Γ, ∀ i, Endpoints.gueP L W (E1 i ∪ E2 z i) ≤ ENNReal.ofReal (A + B) := by
    intro z hz i
    calc Endpoints.gueP L W (E1 i ∪ E2 z i)
        ≤ Endpoints.gueP L W (E1 i) + Endpoints.gueP L W (E2 z i) := measure_union_le _ _
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal B := add_le_add (hE1 i) (hE2 z hz i)
      _ = ENNReal.ofReal (A + B) := (ENNReal.ofReal_add hA0 hB0).symm
  refine (measure_mono hsub).trans ?_
  calc Endpoints.gueP L W (⋃ z ∈ Γ, ⋃ i, (E1 i ∪ E2 z i))
      ≤ ∑ z ∈ Γ, Endpoints.gueP L W (⋃ i, (E1 i ∪ E2 z i)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ z ∈ Γ, ∑ i : Idx L W, Endpoints.gueP L W (E1 i ∪ E2 z i) :=
        Finset.sum_le_sum fun z _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ z ∈ Γ, ∑ i : Idx L W, ENNReal.ofReal (A + B) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun i _ => hpair z hz i
    _ = ENNReal.ofReal ((Γ.card : ℝ) * ((M : ℝ) * (A + B))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_Idx, nsmul_eq_mul,
          nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end Union

/-! ### The choice of the constants -/

section Constants

/-- The real inequality closing the union bound: with `a² = N^ε`, `|Γ| ≤ N^q`, `q'` such that
`(q' + 1) ε ≥ q + D + 2`, and `N` large. -/
private theorem final_arith {N ε D : ℝ} {q q' : ℕ} {c : ℝ} (hN : 1 ≤ N)
    (hq' : (q : ℝ) + D + 2 ≤ ((q' : ℝ) + 1) * ε) (hc : c ≤ N ^ q)
    (h2 : N ^ ((q : ℝ) + 1 + D) * Real.exp (-(N ^ ε) / 2) ≤ 1 / 4)
    (h3 : 2 * RBM.Green.hwConst q' ≤ N) :
    c * (N * (2 * Real.exp (-((N ^ (ε / 2)) ^ 2) / 2) +
      RBM.Green.hwConst q' / ((N ^ (ε / 2)) ^ 2) ^ (q' + 1))) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hY : (N ^ (ε / 2)) ^ 2 = N ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  rw [hY]
  have hhw := RBM.Green.hwConst_pos q'
  have hYpos : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  -- the exponential part
  have hA : N ^ ((q : ℝ) + 1) * (2 * Real.exp (-(N ^ ε) / 2)) ≤ N ^ (-D) / 2 := by
    have e : N ^ ((q : ℝ) + 1) = N ^ (-D) * N ^ ((q : ℝ) + 1 + D) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [e]
    calc N ^ (-D) * N ^ ((q : ℝ) + 1 + D) * (2 * Real.exp (-(N ^ ε) / 2))
        = 2 * N ^ (-D) * (N ^ ((q : ℝ) + 1 + D) * Real.exp (-(N ^ ε) / 2)) := by ring
      _ ≤ 2 * N ^ (-D) * (1 / 4) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = N ^ (-D) / 2 := by ring
  -- the polynomial part
  have hB : N ^ ((q : ℝ) + 1) * (RBM.Green.hwConst q' / (N ^ ε) ^ (q' + 1)) ≤ N ^ (-D) / 2 := by
    have e1 : (N ^ ε) ^ (q' + 1) = N ^ (ε * ((q' : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    rw [e1]
    have e2 : N ^ ((q : ℝ) + 1) * (RBM.Green.hwConst q' / N ^ (ε * ((q' : ℝ) + 1)))
        = RBM.Green.hwConst q' * N ^ ((q : ℝ) + 1 - ε * ((q' : ℝ) + 1)) := by
      rw [Real.rpow_sub hN0]
      ring
    rw [e2]
    have e3 : N ^ ((q : ℝ) + 1 - ε * ((q' : ℝ) + 1)) ≤ N ^ (-D - 1) :=
      Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
    have e4 : N ^ (-D - 1) = N ^ (-D) * N⁻¹ := by
      rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_neg_one]
    calc RBM.Green.hwConst q' * N ^ ((q : ℝ) + 1 - ε * ((q' : ℝ) + 1))
        ≤ RBM.Green.hwConst q' * (N ^ (-D) * N⁻¹) := by
          rw [← e4]; exact mul_le_mul_of_nonneg_left e3 hhw.le
      _ = N ^ (-D) * (RBM.Green.hwConst q' / N) := by field_simp
      _ ≤ N ^ (-D) * (1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hND.le
          rw [div_le_iff₀ hN0]
          linarith
      _ = N ^ (-D) / 2 := by ring
  have hA0 : 0 ≤ 2 * Real.exp (-(N ^ ε) / 2) := by positivity
  have hB0 : 0 ≤ RBM.Green.hwConst q' / (N ^ ε) ^ (q' + 1) := by positivity
  calc c * (N * (2 * Real.exp (-(N ^ ε) / 2) + RBM.Green.hwConst q' / (N ^ ε) ^ (q' + 1)))
      ≤ N ^ q * (N * (2 * Real.exp (-(N ^ ε) / 2) + RBM.Green.hwConst q' / (N ^ ε) ^ (q' + 1))) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = N ^ ((q : ℝ) + 1) * (2 * Real.exp (-(N ^ ε) / 2)) +
          N ^ ((q : ℝ) + 1) * (RBM.Green.hwConst q' / (N ^ ε) ^ (q' + 1)) := by
        rw [Real.rpow_add hN0, Real.rpow_one, Real.rpow_natCast]
        ring
    _ ≤ N ^ (-D) / 2 + N ^ (-D) / 2 := add_le_add hA hB
    _ = N ^ (-D) := by ring

end Constants

/-! ### The theorems -/

section Main

open RBM.Gauss.Sizes

/-- **The Schur tail (the probabilistic input of the GUE local law)**: `GUESchurTail`.
The Schur identity and the
deterministic good-event bound (`schurErr_le_of_good`), the diagonal Gaussian tail
(`gueP_diag_tail`), the quadratic Gaussian chaos (`gue_quad_tail`) and the union bound
(`schur_union_bound`) with `a = N^{ε/2}`. -/
theorem gueSchurTail : GUESchurTail := by
  intro d hd κ τ ε D hκ hτ hε hD q Γ hΓmem hΓcard
  have hNr : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  -- the exponent `q'` of the quadratic tail
  obtain ⟨q', hq'⟩ : ∃ q' : ℕ, (q : ℝ) + D + 2 ≤ ((q' : ℝ) + 1) * ε := by
    refine ⟨⌈((q : ℝ) + D + 2) / ε⌉₊, ?_⟩
    have h1 : ((q : ℝ) + D + 2) / ε ≤ (⌈((q : ℝ) + D + 2) / ε⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    nlinarith
  -- the eventual conditions on `N`
  have e1 : ∀ᶠ n in atTop, 5 ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hNr).eventually_ge_atTop 5
  have e2 : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ ((q : ℝ) + 1 + D) *
      Real.exp (-(((d.size n : ℕ) : ℝ) ^ ε) / 2) ≤ 1 / 4 := by
    have hT := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((q : ℝ) + 1 + D) / ε) (1 / 2)
      (by norm_num)
    have hY : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp hNr
    refine ((hT.comp hY).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      fun n hn => ?_
    have hn' : (((d.size n : ℕ) : ℝ) ^ ε) ^ (((q : ℝ) + 1 + D) / ε) *
        Real.exp (-(1 / 2) * ((d.size n : ℕ) : ℝ) ^ ε) < 1 / 4 := hn
    rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_div_cancel₀ _ hε.ne'] at hn'
    refine hn'.le.trans' (le_of_eq ?_)
    congr 2
    ring
  have e3 : ∀ᶠ n in atTop, 2 * RBM.Green.hwConst q' ≤ ((d.size n : ℕ) : ℝ) :=
    hNr.eventually_ge_atTop _
  have e4 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hNr.eventually_ge_atTop _
  filter_upwards [hΓcard, e1, e2, e3, e4] with n hcard h5 h2 h3 h1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hΓpos : ∀ z ∈ Γ n, 0 < z.im := fun z hz =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hΓmem n z hz).2.1
  have hub := schur_union_bound (d.L n) (d.W n) (Γ n) hΓpos h5 q'
  refine le_trans (measure_mono ?_) (hub.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hω
    obtain ⟨z, hz, i, hm, hbad⟩ := hω
    refine ⟨z, hz, i, hm, ?_⟩
    have hY : (((d.size n : ℕ) : ℝ) ^ (ε / 2)) ^ 2 = ((d.size n : ℕ) : ℝ) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    unfold schurBud at hbad
    rw [← hY] at hbad
    exact hbad
  · exact final_arith h1 hq' hcard h2 h3

/-- **The GUE averaged local law** `GUELocal`: the deterministic bootstrap
`GUELocal_of_tail` applied to `gueSchurTail`. -/
theorem gueLocal : GUELocal := GUELocal_of_tail gueSchurTail

end Main

end RBM.Univ
