/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.IBP
import RBM2D.Path.PerTime
import RBM2D.Path.Scales
import RBM2D.Gauss.Domination

/-!
# Conditional expectations at a fixed time: the row-slice bounds and the moment wrapper

The paper (arXiv:2503.07606) does not state these as lemmas: it says that the estimates on
`G_t` "follow that of Lemma 4.2 in [YY_25], which is dimension-independent"
(Section "Estimates for entries of `G`"), and the mathematics is that of the one-dimensional
formalization: the exceptional event of Definition 2.1 (i) does not disappear under `E_k`, so a
deterministic envelope, the Fubini identity for the row section and Markov are needed.

## Why `≺` does not simply pass through `E_k`

`X ≺ Y` (Definition 2.1 (i)) says only that `P(|X| > N^τ Y) ≤ N^{-D}`, and nothing about the size
of `X` on the exceptional event.  Writing `E_k` out as the coordinate integral over row `k`
(`condRow`, `RBM2D/Green/CondRow.lean`) gives the good/bad split

  `‖E_k[X](ω)‖ ≤ c · E_k[f](ω) + Env · P(slice_ω)`      (`norm_condRow_le_split`),

where the bad part carries the **deterministic envelope** `Env` times the probability of the row
section `slice_ω = {ω' : rowSplit k ω ω' ∈ S}` of the exceptional set `S`.  The Fubini identity
`∫ P(slice_ω) dP(ω) = P(S)` (`lintegral_measure_rowSlice`) and Markov
(`meas_measure_rowSlice_ge`) then show that `P(slice_ω)` is small outside a small set of `ω`.

## The per-time form

The `≺` results are stated as `PerTimeDomAt (Sizes.seqP d) d.size ξ ζ` with
`ξ ζ : ∀ n, V n → Sizes.SeqΩ d → ℝ` at the time `t n`; a hypothesis for all `u ∈ [s n, t n]`
becomes the hypothesis at the one time `u = t n`, and every power of `N` becomes the same power
of `size n`.  The divergence of the sizes is the explicit hypothesis
`hsize : Tendsto size atTop atTop` (as in `stochDomAt_of_momentDomAt` and the `perTimeCalc_*`
lemmas).  `perTimeDomAt_of_moment` is stated for a general finite measure `P` and size function
`size`, like `stochDomAt_of_momentDomAt`; it applies to `Sizes.seqP d` and `d.size`.

## Main results

* `condRowReal`, `rowSlice`, `measurableSet_rowSlice`, `measurable_measure_rowSlice`,
  `lintegral_measure_rowSlice`, `meas_measure_rowSlice_ge` -- `E_k` of a real observable, the row
  section of a set, its measure, the Fubini identity and Markov.
* `norm_condRow_le_split` -- the pointwise good/bad split of the row integral.
* `norm_green_diag_sub_mE_le`, `norm_condExpDiag_sub_le_offdiag` -- the weighted reduction of the
  remainder of the integration-by-parts display (`ibpRem`): the diagonal term `k = i` carries the
  coefficient `S_ii = (5 W²)⁻¹` (`svar`).
* `W_le_self` -- `W ≤ size` (d = 2).
* `perTimeDomAt_of_moment` -- Markov: moments give `≺`, per time and per index, with no
  cardinality hypothesis.

## d = 2 changes

`Sblk` becomes the variance profile `svar` on the fine index `Idx L W = Z2 (W L)` (as in
`condExpDiag_eq_sum_Sblk`); its row sums are `1` (`IBP_sum_svar_row`, `3 ≤ L`) and
`svar (i, i) = (5 W²)⁻¹`.  `W_le_self` holds for every `n` (`W ≤ (W L)² = size n`), not only
eventually.
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path
open scoped ENNReal

variable {d : Sizes} {n : ℕ}

/-! ### `E_k` of a real observable -/

/-- **`E_k[f]` for a real-valued `f`**, the same exact coordinate integral as `condRow`:
integrate the row-`k` coordinates out and freeze the others.  No `MeasureTheory.condExp` is
involved, and the identity is pointwise in `ω`. -/
noncomputable def condRowReal (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (f : Sizes.SeqΩ d → ℝ) : Sizes.SeqΩ d → ℝ :=
  fun ω => ∫ ω', f (rowSplit d n k ω ω') ∂(Sizes.seqP d)

@[simp] theorem condRowReal_const (k : Idx (d.L n) (d.W n)) (c : ℝ) :
    condRowReal d n k (fun _ => c) = fun _ => c := by
  funext ω; simp [condRowReal]

/-! ### The row section of a set, and its measure -/

/-- The **row-`k` section** of `S` at `ω`: the `ω'` for which the split point `rowSplit k ω ω'`
lands in `S`.  `E_k[1_S](ω)` is its probability. -/
def rowSlice (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) (S : Set (Sizes.SeqΩ d))
    (ω : Sizes.SeqΩ d) : Set (Sizes.SeqΩ d) :=
  {ω' | rowSplit d n k ω ω' ∈ S}

theorem measurableSet_rowSlice {k : Idx (d.L n) (d.W n)} {S : Set (Sizes.SeqΩ d)}
    (hS : MeasurableSet S) (ω : Sizes.SeqΩ d) :
    MeasurableSet (rowSlice d n k S ω) :=
  hS.preimage (measurable_rowSplit_right d n k ω)

theorem measurable_measure_rowSlice (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S) :
    Measurable fun ω => (Sizes.seqP d) (rowSlice d n k S ω) := by
  have hpre : MeasurableSet
      ((fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) ⁻¹' S) :=
    hS.preimage (measurable_rowSplit d n k)
  exact measurable_measure_prodMk_left hpre

/-- **The Fubini identity for the row section.**  Averaging the probability of the section over
the fixed coordinates returns the probability of the set itself.  This is
`measurePreserving_rowSplit`, and it is the reason the exceptional event of Definition 2.1 (i) can
be controlled *after* conditioning. -/
theorem lintegral_measure_rowSlice (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S) :
    ∫⁻ ω, (Sizes.seqP d) (rowSlice d n k S ω) ∂(Sizes.seqP d) = (Sizes.seqP d) S := by
  have hmeas := measurable_rowSplit d n k
  have hpre : MeasurableSet
      ((fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) ⁻¹' S) :=
    hS.preimage hmeas
  have h1 : (Sizes.seqP d) S
      = ((Sizes.seqP d).prod (Sizes.seqP d))
          ((fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) ⁻¹' S) := by
    conv_lhs => rw [← (measurePreserving_rowSplit d n k).map_eq]
    exact Measure.map_apply hmeas hS
  rw [h1, Measure.prod_apply hpre]
  rfl

/-- **Markov for the row section.**  The set of fixed configurations whose section is not small
is itself small: `ε · P{ω : P(slice_ω) ≥ ε} ≤ P(S)`. -/
theorem meas_measure_rowSlice_ge (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S) (ε : ℝ≥0∞) :
    ε * (Sizes.seqP d) {ω | ε ≤ (Sizes.seqP d) (rowSlice d n k S ω)} ≤ (Sizes.seqP d) S := by
  have h := mul_meas_ge_le_lintegral₀
    (μ := Sizes.seqP d) (measurable_measure_rowSlice d n k hS).aemeasurable ε
  rwa [lintegral_measure_rowSlice d n k hS] at h

/-! ### The pointwise good/bad split of a row integral

The accounting of a good-event bound, an envelope on the complement, and the probability of the
complement, transplanted from the integral over the whole space to the
integral over one row: on the good set the integrand obeys `‖X‖ ≤ c f`, and on the
bad set it obeys only the deterministic envelope, whose contribution is the envelope times the
probability of the row section. -/

/-- **The split.**  If `‖X‖ ≤ c f` off a set `S` and `‖X‖ ≤ Env` everywhere, then

  `‖E_k[X](ω)‖ ≤ c E_k[f](ω) + Env · P(slice of S at ω)`. -/
theorem norm_condRow_le_split {k : Idx (d.L n) (d.W n)} {X : Sizes.SeqΩ d → ℂ}
    (hX : Measurable X) {f : Sizes.SeqΩ d → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfint : ∀ ω : Sizes.SeqΩ d,
      Integrable (fun ω' => f (rowSplit d n k ω ω')) (Sizes.seqP d))
    {Env c : ℝ} (hEnv : ∀ σ, ‖X σ‖ ≤ Env) (hc : 0 ≤ c)
    {S : Set (Sizes.SeqΩ d)} (hS : MeasurableSet S)
    (hgood : ∀ σ, σ ∉ S → ‖X σ‖ ≤ c * f σ) (ω : Sizes.SeqΩ d) :
    ‖condRow d n k X ω‖
      ≤ c * condRowReal d n k f ω + Env * (Sizes.seqP d).real (rowSlice d n k S ω) := by
  have hsm := measurable_rowSplit_right d n k ω
  have hSω : MeasurableSet (rowSlice d n k S ω) := measurableSet_rowSlice hS ω
  have hXint : Integrable (fun ω' => X (rowSplit d n k ω ω')) (Sizes.seqP d) :=
    Integrable.mono' (integrable_const Env) ((hX.comp hsm).aestronglyMeasurable)
      (Eventually.of_forall fun _ => hEnv _)
  have hindint : Integrable ((rowSlice d n k S ω).indicator fun _ => Env) (Sizes.seqP d) :=
    (integrable_const Env).indicator hSω
  have hcf : Integrable (fun ω' => c * f (rowSplit d n k ω ω')) (Sizes.seqP d) :=
    (hfint ω).const_mul c
  have hpt : ∀ ω' : Sizes.SeqΩ d, ‖X (rowSplit d n k ω ω')‖
      ≤ c * f (rowSplit d n k ω ω')
        + (rowSlice d n k S ω).indicator (fun _ => Env) ω' := by
    intro ω'
    by_cases hω' : ω' ∈ rowSlice d n k S ω
    · rw [Set.indicator_of_mem hω']
      have h1 := hEnv (rowSplit d n k ω ω')
      have h2 : 0 ≤ c * f (rowSplit d n k ω ω') := mul_nonneg hc (hf0 _)
      linarith
    · rw [Set.indicator_of_notMem hω']
      have h1 := hgood (rowSplit d n k ω ω') hω'
      linarith
  rw [condRow_apply]
  calc ‖∫ ω', X (rowSplit d n k ω ω') ∂(Sizes.seqP d)‖
      ≤ ∫ ω', ‖X (rowSplit d n k ω ω')‖ ∂(Sizes.seqP d) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω', (c * f (rowSplit d n k ω ω')
        + (rowSlice d n k S ω).indicator (fun _ => Env) ω') ∂(Sizes.seqP d) :=
        integral_mono hXint.norm (hcf.add hindint) hpt
    _ = c * condRowReal d n k f ω + Env * (Sizes.seqP d).real (rowSlice d n k S ω) := by
        rw [integral_add hcf hindint, integral_const_mul,
          integral_indicator_const _ hSω, smul_eq_mul, mul_comm ((Sizes.seqP d).real _) Env]
        rfl

/-! ### The envelope of `G_{ii} - m`, and the weighted reduction of the remainder `ibpRem` -/

section Assembly

variable {E t : ℝ}

/-- `|G_{ii} - m| ≤ η_t⁻¹ + 1` on the whole space; this is `norm_greenDiagCentered_le_env`,
with `(spectralZ E t).im = η_t`. -/
theorem norm_green_diag_sub_mE_le (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    ‖green (Sizes.seqHflow d n u ω) (spectralZ E t) i i - spectralM E‖ ≤ (etaT E t)⁻¹ + 1 := by
  have h := norm_greenDiagCentered_le_env (d := d) (n := n) hE ht u i ω
  rwa [spectralZ_im] at h

/-- **The weighted reduction.**  The remainder of the integration-by-parts display,
`E_i(G_{ii} - m) - t m² ∑_k S_{ik} (G_{kk} - m)`, is bounded by a bound `A` on
`ibpRem d n E t (i, k)` for `k ≠ i`, plus the diagonal term with its own bound and its own
coefficient `S_ii`: the row sums of `S` are one (`IBP_sum_svar_row`), so

  `‖remainder‖ ≤ A + S_{ii} · A_diag`

as soon as `‖ibpRem(i,k)‖ ≤ A` for `k ≠ i` and `‖ibpRem(i,i)‖ ≤ A_diag`.  Here
`S_ii = svar (i, i) = (5 W²)⁻¹`. -/
theorem norm_condExpDiag_sub_le_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) {A Adiag : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ k : Idx (d.L n) (d.W n), k ≠ i → ‖ibpRem d n E t (i, k) ω‖ ≤ A)
    (hAd : ‖ibpRem d n E t (i, i) ω‖ ≤ Adiag) :
    ‖condExpDiag d n t (spectralZ E t) (spectralM E) i ω
        - (t : ℂ) * spectralM E ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E)‖
      ≤ A + svar (d.L n) (d.W n) i i * Adiag := by
  classical
  have hterm : ∀ k : Idx (d.L n) (d.W n),
      (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω
      = (svar (d.L n) (d.W n) i k : ℂ) * condRow d n i
          (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
            * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω
        - spectralM E * ((svar (d.L n) (d.W n) i k : ℂ)
          * (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E)) := by
    intro k
    simp only [ibpRem]
    ring
  have hkey : condExpDiag d n t (spectralZ E t) (spectralM E) i ω
      - (t : ℂ) * spectralM E ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
        * (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E)
      = (t : ℂ) * spectralM E
        * ∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω := by
    rw [condExpDiag_eq_sum_Sblk hG hE hE.le ht0 ht i ω,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hSrow := IBP_sum_svar_row (L := d.L n) (W := d.W n) (d.three_le_L n) i
  have hsum : ‖∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖
      ≤ A + svar (d.L n) (d.W n) i i * Adiag := by
    have hstep : ∑ k, svar (d.L n) (d.W n) i k * ‖ibpRem d n E t (i, k) ω‖
        ≤ A + svar (d.L n) (d.W n) i i * Adiag := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun k => svar (d.L n) (d.W n) i k * ‖ibpRem d n E t (i, k) ω‖) (Finset.mem_univ i)]
      have hdiagle : svar (d.L n) (d.W n) i i * ‖ibpRem d n E t (i, i) ω‖
          ≤ svar (d.L n) (d.W n) i i * Adiag :=
        mul_le_mul_of_nonneg_left hAd (svar_nonneg _ _ _ _)
      have hoffle : ∑ k ∈ Finset.univ.erase i,
            svar (d.L n) (d.W n) i k * ‖ibpRem d n E t (i, k) ω‖ ≤ A := by
        calc ∑ k ∈ Finset.univ.erase i,
              svar (d.L n) (d.W n) i k * ‖ibpRem d n E t (i, k) ω‖
            ≤ ∑ k ∈ Finset.univ.erase i, svar (d.L n) (d.W n) i k * A := by
              refine Finset.sum_le_sum fun k hk => ?_
              exact mul_le_mul_of_nonneg_left (hA k (Finset.ne_of_mem_erase hk))
                (svar_nonneg _ _ _ _)
          _ = (∑ k ∈ Finset.univ.erase i, svar (d.L n) (d.W n) i k) * A := by
              rw [Finset.sum_mul]
          _ ≤ (∑ k, svar (d.L n) (d.W n) i k) * A := by
              refine mul_le_mul_of_nonneg_right ?_ hA0
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun k _ _ => svar_nonneg _ _ _ _
          _ = A := by rw [hSrow, one_mul]
      linarith
    calc ‖∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖
        ≤ ∑ k, ‖(svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖ := norm_sum_le _ _
      _ = ∑ k, svar (d.L n) (d.W n) i k * ‖ibpRem d n E t (i, k) ω‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (svar_nonneg _ _ _ _)]
      _ ≤ A + svar (d.L n) (d.W n) i i * Adiag := hstep
  rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_spectralM hE.le,
    mul_one]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.le
  calc |t| * ‖∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖
      ≤ 1 * ‖∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖∑ k, (svar (d.L n) (d.W n) i k : ℂ) * ibpRem d n E t (i, k) ω‖ := one_mul _
    _ ≤ A + svar (d.L n) (d.W n) i i * Adiag := hsum

end Assembly

/-! ### `W ≤ size` -/

/-- **`W ≤ size`.**  For `d = 2`, `size n = (W L)²`, so `W ≤ W L ≤ (W L)²` for every `n`
(using `3 ≤ L`). -/
theorem W_le_self (d : Sizes) (n : ℕ) : d.W n ≤ d.size n := by
  have hL := d.three_le_L n
  have hW := d.W_pos n
  calc d.W n ≤ d.W n * d.L n := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _

/-! ### Moments give `≺`, per time and per index -/

/-- **Markov's inequality, per time.**  The moment version of `PerTimeDomAt`, and the reason the
fixed-time inputs need no net: `PerTimeDomAt` bounds the failure probability at each index (and
each time) separately, so no union bound -- and hence no cardinality hypothesis, in contrast
with `stochDomAt_of_momentDomAt` -- is taken.  The size index `l` (`= n`) carries `size l` in
every power.

The hypothesis `hsize` cannot be dropped: on the constant sizes `L = 3`, `W = 2`
(`size ≡ 36`), `Y ≡ 10`, `Φ ≡ 1` satisfy `MomentDomAt`, while
`P{size^{1/10} Φ < |Y|} = 1 > size^{-1}`.  The threshold of the constant is
`C ≤ size^{τp - D}` with `p ≥ (D + 1)/τ` (so the exponent is `≥ 1`). -/
theorem perTimeDomAt_of_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {Y : ∀ l, U l → Ω → ℝ} {Φ : ∀ l, U l → ℝ} (hΦ : ∀ l u, 0 < Φ l u)
    (hint : ∀ (p l : ℕ) (u : U l), Integrable (fun ω => |Y l u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size Y Φ) :
    PerTimeDomAt P size Y (fun l u _ => Φ l u) := by
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + 1) / τ)
  have hDp : D + 1 ≤ τ * (p : ℝ) := by rw [div_le_iff₀ hτ] at hp; linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - D := by linarith
  filter_upwards [hCN, hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow C hexp)] with l hN hsize1 hCle u
  have hNpos : (0 : ℝ) < size l := by exact_mod_cast hsize1
  have hΦu := hΦ l u
  have hrp : (0 : ℝ) < (size l : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have ht : 0 < (size l : ℝ) ^ τ * Φ l u := mul_pos hrp hΦu
  refine (meas_gt_le_of_moment P ht (hint p l u) (hN u)).trans (ENNReal.ofReal_le_ofReal ?_)
  set a : ℝ := (size l : ℝ) ^ (τ * (p : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hb : (0 : ℝ) < Φ l u ^ (2 * p) := by positivity
  have h1 : ((size l : ℝ) ^ τ * Φ l u) ^ (2 * p) = a * a * Φ l u ^ (2 * p) := by
    rw [mul_pow, ha_def, ← Real.rpow_natCast ((size l : ℝ) ^ τ) (2 * p),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    push_cast
    ring_nf
  have h2 : C * (a * Φ l u ^ (2 * p)) / (a * a * Φ l u ^ (2 * p)) = C * a⁻¹ := by
    field_simp
  have h3 : a⁻¹ = (size l : ℝ) ^ (-(τ * (p : ℝ))) := by
    rw [ha_def, Real.rpow_neg hNpos.le]
  rw [h1, h2]
  calc C * a⁻¹ ≤ (size l : ℝ) ^ (τ * (p : ℝ) - D) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
    _ = (size l : ℝ) ^ (-D) := by
        rw [h3, ← Real.rpow_add hNpos]
        congr 1
        ring

end RBM.Green
