/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridGoodN

/-!
# The stopped Azuma bound for the first-chaos part and the assembled pathwise bound

Paper: arXiv:2503.07606, Section 5: the stopped loop hierarchy (`int_K-L_ST`), its martingale
term (`alu9_STime`, with BDG replaced by Azuma-Hoeffding) and the assembly of Lemma `lem_BcalE`.

Result: `assembledN : AssembledN d` (the statement is in `RBM2D.Induction.GridGoodN`; section 8).
The label-weighted stopped Azuma bound for the first-chaos part is `GridAssemblyN_azuma_Ugen`
(section 4).

The argument parallels the one-dimensional formalization (the complex Azuma argument, the
fourth-moment bound for martingale differences, the probability budgets).  The `d = 2` changes:
the labels are `Fin k → Z2 L`, their number is `(L·L)^k ≤ N^k` (`N = (W L)^2`), so the exponent
count reads `D₁ + 4D + k + 2C_P + 8 ≤ C_K`; the kernel is the slotwise product `Ugen` of `ukerMat`s
with the slot parameters `m(σ_i) m(σ_{i+1})` of modulus `1`; its coarse row sum is
`(1 + (1 - u_m)⁻¹)^k`; the increments are step-indexed (`Z j`, `Y j` is the step `j → j+1`); the
`Z`-union runs over the targets `1 ≤ m ≤ K` (the `m = 0` sum is empty).  Every helper is `private`
and carries the prefix `GridAssemblyN_`.

Layout: 1. fourth-moment bound for martingale differences; 2. the complex Azuma step; 3. the
kernel `Ugen` (measurability, sum of four increments, coarse row bound); 4. the stopped Azuma
bound; 5. the probability budgets; 6. the fourth-moment tail of `Y`; 7. the single-scale core;
8. `assembledN`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The fourth-moment bound for real martingale differences (the `p = 2` Burkholder bound) -/

section Moment4

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

private lemma GridAssemblyN_abs_le_B1 (a b : ℝ) : |a| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2),
      sq_nonneg (b ^ 2)]

private lemma GridAssemblyN_abs_mul_le_B (a b : ℝ) : |a * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - 1 / 2),
      sq_nonneg (b ^ 2 - 1 / 2), sq_nonneg (a ^ 2 - b ^ 2)]

private lemma GridAssemblyN_abs_sq_le_B (a b : ℝ) : |a ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (sq_nonneg a)]
  nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (b ^ 2)]

private lemma GridAssemblyN_abs_cube_mul_le_B (a b : ℝ) :
    |a ^ 3 * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  have h1 : |a ^ 3 * b| = a ^ 2 * |a * b| := by
    rw [show a ^ 3 * b = a ^ 2 * (a * b) by ring, abs_mul, abs_of_nonneg (sq_nonneg a)]
  have h2 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  rw [h1]
  have h3 : a ^ 2 * |a * b| ≤ a ^ 2 * ((a ^ 2 + b ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg a, sq_nonneg b]

private lemma GridAssemblyN_abs_sq_mul_sq_le_B (a b : ℝ) :
    |a ^ 2 * b ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

private lemma GridAssemblyN_pow4_add_le (a b : ℝ) :
    (a + b) ^ 4 ≤ a ^ 4 + 4 * (a ^ 3 * b) + 8 * (a ^ 2 * b ^ 2) + 3 * b ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (a - b))]

private lemma GridAssemblyN_pow4_add_le_eight (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b)), sq_nonneg (a * b),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - b))]

/-- One step of the fourth-moment recursion: for an `ℱ m`-measurable `S` and a martingale
difference `d` with `E[d | ℱ m] = 0`, `E[d² | ℱ m] ≤ v`:
`E(S+d)² ≤ E S² + v` and `E(S+d)⁴ ≤ E S⁴ + 8 v E S² + 3 E d⁴`. -/
private lemma GridAssemblyN_moment4_step (m : ℕ) {S d : Ω' → ℝ} (hS : StronglyMeasurable[ℱ m] S)
    (hd : StronglyMeasurable d) (hS4 : Integrable (fun ω => S ω ^ 4) μ)
    (hd4 : Integrable (fun ω => d ω ^ 4) μ) (hmean : μ[d | ℱ m] =ᵐ[μ] 0) {v : ℝ}
    (hcond : μ[fun ω => d ω ^ 2 | ℱ m] ≤ᵐ[μ] fun _ => v) :
    Integrable (fun ω => (S ω + d ω) ^ 4) μ
      ∧ ∫ ω, (S ω + d ω) ^ 2 ∂μ ≤ ∫ ω, S ω ^ 2 ∂μ + v
      ∧ ∫ ω, (S ω + d ω) ^ 4 ∂μ
          ≤ ∫ ω, S ω ^ 4 ∂μ + 8 * v * ∫ ω, S ω ^ 2 ∂μ + 3 * ∫ ω, d ω ^ 4 ∂μ := by
  have hS0 : StronglyMeasurable S := hS.mono (ℱ.le m)
  set B : Ω' → ℝ := fun ω => 1 + 2 * (S ω ^ 4 + d ω ^ 4) with hBdef
  have hB : Integrable B μ := (integrable_const 1).add ((hS4.add hd4).const_mul 2)
  have hint : ∀ f : Ω' → ℝ, StronglyMeasurable f → (∀ ω, |f ω| ≤ B ω) → Integrable f μ :=
    fun f hf hfB => hB.mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB ω)
  have hid : Integrable d μ := hint d hd fun ω => by
    have := GridAssemblyN_abs_le_B1 (d ω) (S ω); simp only [hBdef]; linarith
  have hid2 : Integrable (fun ω => d ω ^ 2) μ :=
    hint _ (hd.pow 2) fun ω => by
      have := GridAssemblyN_abs_sq_le_B (d ω) (S ω); simp only [hBdef]; linarith
  have hiS2 : Integrable (fun ω => S ω ^ 2) μ :=
    hint _ (hS0.pow 2) fun ω => GridAssemblyN_abs_sq_le_B (S ω) (d ω)
  have hiSd : Integrable (fun ω => S ω * d ω) μ :=
    hint _ (hS0.mul hd) fun ω => GridAssemblyN_abs_mul_le_B (S ω) (d ω)
  have hiS3d : Integrable (fun ω => S ω ^ 3 * d ω) μ :=
    hint _ ((hS0.pow 3).mul hd) fun ω => GridAssemblyN_abs_cube_mul_le_B (S ω) (d ω)
  have hiS2d2 : Integrable (fun ω => S ω ^ 2 * d ω ^ 2) μ :=
    hint _ ((hS0.pow 2).mul (hd.pow 2)) fun ω => GridAssemblyN_abs_sq_mul_sq_le_B (S ω) (d ω)
  have hiSum4 : Integrable (fun ω => (S ω + d ω) ^ 4) μ := by
    refine ((hS4.add hd4).const_mul 8).mono' ((hS0.add hd).pow 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact GridAssemblyN_pow4_add_le_eight (S ω) (d ω)
  -- `E[S^p d] = 0` for an `ℱ m`-measurable `S^p`
  have hzero : ∀ p : ℕ, Integrable (fun ω => S ω ^ p * d ω) μ →
      ∫ ω, S ω ^ p * d ω ∂μ = 0 := by
    intro p hp
    have h1 : μ[(fun ω => S ω ^ p) * d | ℱ m] =ᵐ[μ] (fun ω => S ω ^ p) * μ[d | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow p) hp hid
    calc ∫ ω, S ω ^ p * d ω ∂μ = ∫ ω, (μ[(fun ω => S ω ^ p) * d | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ p) * μ[d | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ _ω, (0 : ℝ) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmean] with ω hω
          simp [hω]
      _ = 0 := integral_zero _ _
  have hSd0 : ∫ ω, S ω * d ω ∂μ = 0 := by
    have := hzero 1 (by simpa using hiSd)
    simpa using this
  have hS3d0 : ∫ ω, S ω ^ 3 * d ω ∂μ = 0 := hzero 3 hiS3d
  -- `E[d²] ≤ v`
  have hd2v : ∫ ω, d ω ^ 2 ∂μ ≤ v := by
    calc ∫ ω, d ω ^ 2 ∂μ = ∫ ω, (μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ ≤ ∫ _ω, v ∂μ := integral_mono_ae integrable_condExp (integrable_const v) hcond
      _ = v := by simp
  -- `E[S² d²] ≤ v E[S²]`
  have hS2d2 : ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ ≤ v * ∫ ω, S ω ^ 2 ∂μ := by
    have h1 : μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]
        =ᵐ[μ] (fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow 2) hiS2d2 hid2
    have hi1 : Integrable ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) μ :=
      (integrable_condExp (μ := μ) (m := ℱ m)
        (f := (fun ω => S ω ^ 2) * (fun ω => d ω ^ 2))).congr h1
    calc ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
        = ∫ ω, (μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ ≤ ∫ ω, v * S ω ^ 2 ∂μ := by
          refine integral_mono_ae hi1 (hiS2.const_mul v) ?_
          filter_upwards [hcond] with ω hω
          simp only [Pi.mul_apply]
          nlinarith [sq_nonneg (S ω)]
      _ = v * ∫ ω, S ω ^ 2 ∂μ := integral_const_mul v _
  refine ⟨hiSum4, ?_, ?_⟩
  · have heq : (fun ω => (S ω + d ω) ^ 2)
        = fun ω => S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2 := by funext ω; ring
    rw [heq, integral_add (f := fun ω => S ω ^ 2 + 2 * (S ω * d ω))
        (hiS2.add (hiSd.const_mul 2)) hid2,
      integral_add (f := fun ω => S ω ^ 2) hiS2 (hiSd.const_mul 2), integral_const_mul, hSd0]
    linarith
  · calc ∫ ω, (S ω + d ω) ^ 4 ∂μ
        ≤ ∫ ω, (S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2) + 3 * d ω ^ 4) ∂μ :=
          integral_mono hiSum4
            (((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)).add (hd4.const_mul 3))
            fun ω => GridAssemblyN_pow4_add_le (S ω) (d ω)
      _ = ∫ ω, S ω ^ 4 ∂μ + 4 * ∫ ω, S ω ^ 3 * d ω ∂μ + 8 * ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
            + 3 * ∫ ω, d ω ^ 4 ∂μ := by
          rw [integral_add
              (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2))
              ((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)) (hd4.const_mul 3),
            integral_add (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω))
              (hS4.add (hiS3d.const_mul 4)) (hiS2d2.const_mul 8),
            integral_add (f := fun ω => S ω ^ 4) hS4 (hiS3d.const_mul 4), integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by rw [hS3d0]; nlinarith [hS2d2]

/-- **The `p = 2` Burkholder bound for real martingale differences** (elementary).  For `d_j` `ℱ (j+1)`-measurable with
`E[d_j | ℱ j] = 0`, `d_j⁴` integrable, `E[d_j² | ℱ j] ≤ v_j` a.s. (`v_j ≥ 0`) and `E d_j⁴ ≤ w_j`,
the partial sum `S_m = Σ_{j<m} d_j` satisfies `E S_m² ≤ Σ_{j<m} v_j` and
`E S_m⁴ ≤ 8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j`. -/
private theorem GridAssemblyN_mart_moment4 (d : ℕ → Ω' → ℝ) (v w : ℕ → ℝ) (m : ℕ)
    (hd : ∀ j, StronglyMeasurable[ℱ (j + 1)] (d j))
    (hmean : ∀ j < m, μ[d j | ℱ j] =ᵐ[μ] 0)
    (hint : ∀ j < m, Integrable (fun ω => d j ω ^ 4) μ)
    (hcond : ∀ j < m, μ[fun ω => d j ω ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hv0 : ∀ j < m, 0 ≤ v j)
    (hw : ∀ j < m, ∫ ω, d j ω ^ 4 ∂μ ≤ w j) :
    Integrable (fun ω => (∑ j ∈ Finset.range m, d j ω) ^ 4) μ
      ∧ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ ≤ ∑ j ∈ Finset.range m, v j
      ∧ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 4 ∂μ
          ≤ 8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hI, h2, h4⟩ := ih (fun j hj => hmean j (by omega)) (fun j hj => hint j (by omega))
      (fun j hj => hcond j (by omega)) (fun j hj => hv0 j (by omega)) (fun j hj => hw j (by omega))
    have hSm : StronglyMeasurable[ℱ m] (fun ω => ∑ j ∈ Finset.range m, d j ω) := by
      refine Finset.stronglyMeasurable_fun_sum (Finset.range m)
        (fun j hj => (hd j).mono (ℱ.mono ?_))
      have := Finset.mem_range.mp hj; omega
    have hdm : StronglyMeasurable (d m) := (hd m).mono (ℱ.le (m + 1))
    obtain ⟨hI', h2', h4'⟩ := GridAssemblyN_moment4_step (μ := μ) m hSm hdm hI
      (hint m (by omega)) (hmean m (by omega)) (hcond m (by omega))
    have hsum : ∀ ω, ∑ j ∈ Finset.range (m + 1), d j ω
        = (∑ j ∈ Finset.range m, d j ω) + d m ω := fun ω => Finset.sum_range_succ _ _
    simp only [hsum]
    have hV0 : 0 ≤ ∑ j ∈ Finset.range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hvm := hv0 m (by omega)
    have hwm := hw m (by omega)
    have hS2nn : 0 ≤ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    refine ⟨hI', ?_, ?_⟩
    · rw [Finset.sum_range_succ]; linarith
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h8 : 8 * v m * ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ
          ≤ 8 * v m * ∑ j ∈ Finset.range m, v j :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [mul_nonneg hvm hV0, sq_nonneg (v m)]

end Moment4

/-! ## 2. The complex Azuma step and the stopped `Ugen`-propagated sums -/

section AzumaStep

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- Prepend a dummy zero term. -/
private def GridAssemblyN_prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

private theorem GridAssemblyN_sum_range_succ_prependZero {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), GridAssemblyN_prependZero f i = ∑ j ∈ Finset.range m, f j := by
  rw [Finset.sum_range_succ' (GridAssemblyN_prependZero f) m]
  simp [GridAssemblyN_prependZero]

/-- The complex Azuma tail for `Σ_{j<m} X_j` when `X_j` is `ℱ (j+1)`-strongly measurable and its
real and imaginary parts are conditionally sub-Gaussian given `ℱ j` with proxy `c j` (the process
`0, X_0, …, X_{m-1}, 0, …` fed to `azuma_complex` with horizon `m + 1`). -/
private theorem GridAssemblyN_azuma_step {X : ℕ → Ω' → ℂ} {m : ℕ}
    (hX : ∀ j < m, StronglyMeasurable[ℱ (j + 1)] (X j)) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := fun i => if i ≤ m then GridAssemblyN_prependZero X i else 0 with hYdef
  set cc : ℕ → ℝ≥0 := GridAssemblyN_prependZero c with hccdef
  have hYsucc : ∀ j, j + 1 ≤ m → Y (j + 1) = X j := by
    intro j hj
    simp only [hYdef, hj, ↓reduceIte]
    rfl
  have hYzero : Y 0 = 0 := by
    simp [hYdef, GridAssemblyN_prependZero]
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).re)
        rw [hYsucc j hj]
        exact Complex.continuous_re.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).im)
        rw [hYsucc j hj]
        exact Complex.continuous_im.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYzero, hccdef, GridAssemblyN_prependZero]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYzero, hccdef, GridAssemblyN_prependZero]
  have hCR : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).1
  have hCI : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).2
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (m + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ Finset.range m, X j ω = ∑ i ∈ Finset.range (m + 1), Y i ω := by
    intro ω
    have h3 := GridAssemblyN_sum_range_succ_prependZero (fun j => X j ω) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hYdef, him, ↓reduceIte]
    cases i <;> rfl
  have hsumeq : ∑ i ∈ Finset.range (m + 1), (cc i : ℝ) = ∑ j ∈ Finset.range m, (c j : ℝ) := by
    have h3 := GridAssemblyN_sum_range_succ_prependZero (fun j => (c j : ℝ)) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases i <;> rfl
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖}
      = {ω | x ≤ ‖∑ i ∈ Finset.range (m + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

end AzumaStep

/-! ## 3. The kernel `Ugen`: strong measurability, sums of four, and the coarse row bound -/

section UgenBounds

/-- `A ↦ (𝒰_{v,w,σ} A)_a` is continuous, so it preserves strong measurability. -/
private theorem GridAssemblyN_stronglyMeasurable_Ugen_apply {Ω' : Type*} {m : MeasurableSpace Ω'}
    (L : ℕ) [NeZero L] (E' : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ)
    {W : Ω' → (Fin k → Z2 L) → ℂ} (hW : StronglyMeasurable[m] W) (a : Fin k → Z2 L) :
    StronglyMeasurable[m] (fun ω => Ugen L E' σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Z2 L) → ℂ => Ugen L E' σ v w A a) := by
    unfold Ugen
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `𝒰` of the four-term increment `Δ D + Z + Y + R`, at one label. -/
private theorem GridAssemblyN_Ugen_four (L : ℕ) [NeZero L] (E : ℝ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (v w : ℝ) (Δ : ℂ) (D Z Y R : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Ugen L E σ v w (Δ • D + Z + Y + R) a =
      Δ * Ugen L E σ v w D a + Ugen L E σ v w Z a + Ugen L E σ v w Y a + Ugen L E σ v w R a := by
  unfold Ugen
  have hterm : ∀ b : Fin k → Z2 L, (∏ i : Fin k,
        ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) *
      ((Δ • D + Z + Y + R) b) =
      Δ * ((∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * D b)
      + (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * Z b
      + (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * Y b
      + (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * R b := by
    intro b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2`. -/
private theorem GridAssemblyN_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (b : Bool) :
    ‖KLoop.mSig E b‖ = 1 := by
  cases b <;> simp [KLoop.mSig, norm_spectralM hE]

/-- The slot parameter `m(σ) m(σ')` has modulus `1` for `|E| ≤ 2`. -/
private theorem GridAssemblyN_norm_slot {E : ℝ} (hE : |E| ≤ 2) (b b' : Bool) :
    ‖KLoop.mSig E b * KLoop.mSig E b'‖ ≤ 1 := by
  rw [norm_mul, GridAssemblyN_norm_mSig hE, GridAssemblyN_norm_mSig hE]
  simp

open scoped Matrix.Norms.Operator in
/-- The exact form of the kernel `(1 - vξS) Θ_{wξ} = 1 + (w - v) ξ SΘ_{wξ}`, from
`(1 - wξ S) Θ_{wξ} = 1` (`mul_Theta`). -/
private theorem GridAssemblyN_ukerMat_eq (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v w = 1 + ((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w := by
  have h := mul_Theta L hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat thetaGenMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

open scoped Matrix.Norms.Operator in
/-- The `ℓ^∞` operator norm of the one-slot kernel: `‖(1 - vξS) Θ_{wξ}‖ ≤ 1 + (1 - w)⁻¹` for
`0 ≤ v, w < 1`, `‖ξ‖ ≤ 1` (no order between `v` and `w`; via `|w - v| ≤ 1`). -/
private theorem GridAssemblyN_norm_ukerMat_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ‖ukerMat L ξ v w‖ ≤ 1 + (1 - w)⁻¹ := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hwξ : ‖(w : ℂ) * ξ‖ = w * ‖ξ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
  have hw' : ‖(w : ℂ) * ξ‖ < 1 := by
    rw [hwξ]
    calc w * ‖ξ‖ ≤ w * 1 := mul_le_mul_of_nonneg_left hξ hw0
      _ = w := mul_one w
      _ < 1 := hw1
  have hwv : ‖(w : ℂ) - (v : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hgen : ‖thetaGenMat L ξ w‖ ≤ ‖ξ‖ * (1 - w * ‖ξ‖)⁻¹ := by
    unfold thetaGenMat
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ hξ0
    calc ‖SB L * Theta L ((w : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((w : ℂ) * ξ)‖ := norm_mul_le _ _
      _ = ‖Theta L ((w : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
      _ ≤ (1 - ‖(w : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hw'
      _ = (1 - w * ‖ξ‖)⁻¹ := by rw [hwξ]
  have harith : ‖ξ‖ * (1 - w * ‖ξ‖)⁻¹ ≤ (1 - w)⁻¹ := by
    have hsr : w * ‖ξ‖ ≤ w := mul_le_of_le_one_right hw0 hξ
    have hd : 0 < 1 - w * ‖ξ‖ := by linarith
    have hd' : 0 < 1 - w := by linarith
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hd hd']
    nlinarith
  rw [GridAssemblyN_ukerMat_eq L hL hw']
  calc ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) + ((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w‖
      ≤ ‖(1 : Matrix (Z2 L) (Z2 L) ℂ)‖ + ‖((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w‖ :=
        norm_add_le _ _
    _ = 1 + ‖(w : ℂ) - (v : ℂ)‖ * ‖thetaGenMat L ξ w‖ := by rw [norm_one, norm_smul]
    _ ≤ 1 + 1 * ((1 - w)⁻¹) := by
        refine add_le_add le_rfl (mul_le_mul hwv (hgen.trans harith) (norm_nonneg _) zero_le_one)
    _ = 1 + (1 - w)⁻¹ := by rw [one_mul]

open scoped Matrix.Norms.Operator in
/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
private theorem GridAssemblyN_sum_norm_row_le_opNorm (L : ℕ) [NeZero L]
    (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) : ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- **The coarse row-sum kernel bound of `Ugen`** (derived, not assumed): for `|E| ≤ 2`, `3 ≤ L`, `0 ≤ v, w < 1`,
`‖(𝒰_{v,w,σ} X)_a‖ ≤ (1 + (1 - w)⁻¹)^k ‖X‖_max` (each of the `k` slots has row sum at most
`1 + (1 - w)⁻¹`, `|ξ_i| = |m(σ_i) m(σ_{i+1})| = 1`). -/
private theorem GridAssemblyN_norm_Ugen_coarse (L : ℕ) [NeZero L] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} [NeZero k] (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) {X : (Fin k → Z2 L) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Z2 L) :
    ‖Ugen L E σ v w X a‖ ≤ (1 + (1 - w)⁻¹) ^ k * M := by
  have hrow : ∀ (i : Fin k) (x : Z2 L),
      ∑ c : Z2 L, ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w x c‖ ≤
        1 + (1 - w)⁻¹ := fun i x =>
    (GridAssemblyN_sum_norm_row_le_opNorm L _ x).trans
      (GridAssemblyN_norm_ukerMat_le L hL (GridAssemblyN_norm_slot hE _ _) hv0 hv1 hw0 hw1)
  have hprod : ∑ b : Fin k → Z2 L, ∏ i : Fin k,
      ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)‖ ≤
      (1 + (1 - w)⁻¹) ^ k := by
    rw [← Fintype.prod_sum (fun (i : Fin k) (c : Z2 L) =>
      ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) c‖)]
    calc ∏ i : Fin k, ∑ c : Z2 L,
          ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) c‖
        ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
            (fun i _ => hrow i (a i))
      _ = (1 + (1 - w)⁻¹) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖Ugen L E σ v w X a‖
      = ‖∑ b : Fin k → Z2 L, (∏ i : Fin k,
          ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * X b‖ := rfl
    _ ≤ ∑ b : Fin k → Z2 L, ‖(∏ i : Fin k,
          ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * X b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : Fin k → Z2 L, (∏ i : Fin k,
          ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)‖) * M :=
        Finset.sum_le_sum fun b _ => by
          rw [norm_mul, norm_prod]
          exact mul_le_mul_of_nonneg_left (hX b) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∑ b : Fin k → Z2 L, ∏ i : Fin k,
          ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)‖) * M := by
        rw [Finset.sum_mul]
    _ ≤ (1 + (1 - w)⁻¹) ^ k * M := mul_le_mul_of_nonneg_right hprod hM

end UgenBounds

/-! ## 4. The stopped Azuma bound for the first-chaos part `ZvecN` -/

section StoppedAzuma

variable (d : Sizes)

/-- The label-weighted Azuma tail for a fixed target `m` and label `a` and an arbitrary
step-indexed increment `Z` (`Z j` is the step `j → j+1`, `ℱ (j+1)`-strongly measurable for
`j < m`): `sum_stopped` rewrites the stopped sum as `Σ_{j<m} 1{j<τ} (𝒰_{u_{j+1},u_m} Z_j)_a` and
`azuma_complex` (via `GridAssemblyN_azuma_step`) gives the tail. -/
private theorem GridAssemblyN_azuma_Ugen {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool)
    (u : ℕ → ℝ) {τ : PathΩ d → ℕ} (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    {Z : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ} (m : ℕ)
    (hZ : ∀ j < m, StronglyMeasurable[filt d (j + 1)] (Z j)) (a : Fin k → Z2 (d.L n))
    (c : ℕ → ℝ≥0) (hsubG : ∀ j < m, SubGaussStopN d E σ u τ Z m a j (c j)) {x : ℝ}
    (hx : 0 ≤ x) :
    (pathP d).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set X : ℕ → PathΩ d → ℂ := fun j => {ω' | j < τ ω'}.indicator (fun ω' =>
    Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω') a) with hXdef
  have hX : ∀ j < m, StronglyMeasurable[filt d (j + 1)] (X j) := by
    intro j hj
    have hset : MeasurableSet[filt d (j + 1)] {ω | j < τ ω} :=
      ((filt d).mono (Nat.le_succ j)) _ (hτ j)
    exact (GridAssemblyN_stronglyMeasurable_Ugen_apply (d.L n) E σ _ _ (hZ j hj) a).indicator hset
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have h := sum_stopped (Ω' := PathΩ d) (M := ℂ)
      (fun i ω' => Ugen (d.L n) E σ (u i) (u m) (Z (i - 1) ω') a) τ m ω
    simp only [Nat.add_sub_cancel] at h
    rw [h]
  rw [hset]
  exact GridAssemblyN_azuma_step (μ := pathP d) (ℱ := filt d) hX hsubG hx

end StoppedAzuma

/-! ## 5. The probability budget -/

section Budget

/-- `C N^A e^{-c N^{τ₁}} ≤ 1` eventually in the real variable `N`: the Gaussian tail beats every
power. -/
private theorem GridAssemblyN_eventually_exp_small (C A c : ℝ) {τ₁ : ℝ} (hc : 0 < c)
    (hτ₁ : 0 < τ₁) :
    ∀ᶠ N : ℝ in atTop, C * N ^ A * Real.exp (-(c * N ^ τ₁)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / τ₁) c hc
  have hg : Tendsto (fun N : ℝ => N ^ τ₁) atTop atTop := tendsto_rpow_atTop hτ₁
  have h2 := h.comp hg
  have hpos : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hpos), eventually_gt_atTop (0 : ℝ)] with N hN hN0
  simp only [Function.comp_apply] at hN
  have e : (N ^ τ₁) ^ (A / τ₁) = N ^ A := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  rw [e] at hN
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hx : 0 ≤ N ^ A * Real.exp (-(c * N ^ τ₁)) := by positivity
  have hN' : N ^ A * Real.exp (-c * N ^ τ₁) < (|C| + 1)⁻¹ := hN
  rw [neg_mul] at hN'
  calc C * N ^ A * Real.exp (-(c * N ^ τ₁))
      = C * (N ^ A * Real.exp (-(c * N ^ τ₁))) := by ring
    _ ≤ (|C| + 1) * (N ^ A * Real.exp (-(c * N ^ τ₁))) := mul_le_mul_of_nonneg_right hC hx
    _ ≤ (|C| + 1) * (|C| + 1)⁻¹ := mul_le_mul_of_nonneg_left hN'.le (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

/-- **The Azuma budget**: for every `k`,
`ε > 0`, `D₁` and `C_K ≥ 0`, eventually in the real `N`: `N ≥ 2` and, uniformly over
`K ≤ ⌈N^{C_K}⌉₊` and `0 ≤ Lc ≤ N^k` (`Lc` the number of labels, `(L·L)^k ≤ N^k`),
`4 K Lc exp(-(N^ε)²/4) ≤ N^{-D₁}/2`.  `SizeTendsto` is needed only to make this eventual in `n`. -/
private theorem GridAssemblyN_zBudget (k : ℕ) {ε : ℝ} (hε : 0 < ε) (D₁ C_K : ℝ)
    (hCK : 0 ≤ C_K) :
    ∀ᶠ N : ℝ in atTop, (2 : ℝ) ≤ N ∧ ∀ (K : ℕ) (Lc : ℝ), K ≤ ⌈N ^ C_K⌉₊ → 0 ≤ Lc →
      Lc ≤ N ^ k → 4 * (K : ℝ) * Lc * Real.exp (-(N ^ ε) ^ 2 / 4) ≤ N ^ (-D₁) / 2 := by
  filter_upwards [GridAssemblyN_eventually_exp_small 16 (C_K + k + D₁) (1 / 4) (by norm_num)
    (by linarith : (0 : ℝ) < 2 * ε), eventually_ge_atTop (2 : ℝ)] with N hexp hN2
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨hN2, fun K Lc hK hLc0 hLc => ?_⟩
  have hNCK : 1 ≤ N ^ C_K := Real.one_le_rpow (by linarith) hCK
  have hK' : (K : ℝ) ≤ 2 * N ^ C_K := by
    have h1 : (K : ℝ) ≤ (⌈N ^ C_K⌉₊ : ℝ) := by exact_mod_cast hK
    have h2 : (⌈N ^ C_K⌉₊ : ℝ) < N ^ C_K + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hsq : (N ^ ε) ^ 2 = N ^ (2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    ring_nf
  rw [hsq]
  set ex : ℝ := Real.exp (-N ^ (2 * ε) / 4) with hexdef
  have hex_eq : Real.exp (-(1 / 4 * N ^ (2 * ε))) = ex := by
    rw [hexdef]; congr 1; ring
  rw [hex_eq] at hexp
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have hsplit : N ^ (C_K + (k : ℝ) + D₁) = N ^ C_K * N ^ (k : ℕ) * N ^ D₁ := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
  have hD : N ^ D₁ * N ^ (-D₁) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hr : 0 < N ^ (-D₁) := Real.rpow_pos_of_pos hN0 _
  rw [hsplit] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp hr.le
  have e1 : 16 * (N ^ C_K * N ^ (k : ℕ) * N ^ D₁) * ex * N ^ (-D₁)
      = 16 * (N ^ C_K * N ^ (k : ℕ) * ex) * (N ^ D₁ * N ^ (-D₁)) := by ring
  rw [e1, hD, mul_one, one_mul] at hmul
  have hKL : 4 * (K : ℝ) * Lc * ex ≤ 4 * (2 * N ^ C_K) * N ^ (k : ℕ) * ex := by
    gcongr
  linarith

/-- The `ΔP`-form of the moment bound: under `v_j ≤ Δ²P`, `w_j ≤ Δ⁴P²`, `KΔ ≤ 1`, `1 ≤ K`, `P ≥ 0`, `Δ ≥ 0`, the budget
`(K+1)·4(8V²+3W) ≤ 88 Δ P²` (`Δ ≤ 1` follows from `1 ≤ K`, `KΔ ≤ 1`). -/
private theorem GridAssemblyN_moment4_budget_le {K : ℕ} {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hP0 : 0 ≤ P)
    (hKΔ : (K : ℝ) * Δ ≤ 1) (hK1 : 1 ≤ K) {v w : ℕ → ℝ} (hv0 : ∀ j < K, 0 ≤ v j)
    (hw0 : ∀ j < K, 0 ≤ w j) (hv : ∀ j < K, v j ≤ Δ ^ 2 * P)
    (hw : ∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) :
    (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
      ≤ 88 * Δ * P ^ 2 := by
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hΔ1 : Δ ≤ 1 := by nlinarith
  have hV : ∑ j ∈ Finset.range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := by
    have := Finset.sum_le_sum (s := Finset.range K) fun j hj => hv j (Finset.mem_range.mp hj)
    simpa using this
  have hV0 : 0 ≤ ∑ j ∈ Finset.range K, v j :=
    Finset.sum_nonneg fun j hj => hv0 j (Finset.mem_range.mp hj)
  have hW : ∑ j ∈ Finset.range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := by
    have := Finset.sum_le_sum (s := Finset.range K) fun j hj => hw j (Finset.mem_range.mp hj)
    simpa using this
  have hKΔ0 : 0 ≤ (K : ℝ) * Δ := by positivity
  have hV' : ∑ j ∈ Finset.range K, v j ≤ Δ * P := by
    calc ∑ j ∈ Finset.range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := hV
      _ = ((K : ℝ) * Δ) * (Δ * P) := by ring
      _ ≤ 1 * (Δ * P) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ * P := one_mul _
  have hV2 : (∑ j ∈ Finset.range K, v j) ^ 2 ≤ (Δ * P) ^ 2 := pow_le_pow_left₀ hV0 hV' 2
  have hW' : ∑ j ∈ Finset.range K, w j ≤ Δ ^ 3 * P ^ 2 := by
    calc ∑ j ∈ Finset.range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := hW
      _ = ((K : ℝ) * Δ) * (Δ ^ 3 * P ^ 2) := by ring
      _ ≤ 1 * (Δ ^ 3 * P ^ 2) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ ^ 3 * P ^ 2 := one_mul _
  have hΔ3 : Δ ^ 3 * P ^ 2 ≤ (Δ * P) ^ 2 := by
    have : Δ ^ 3 ≤ Δ ^ 2 := pow_le_pow_of_le_one hΔ0 hΔ1 (by norm_num)
    have h2 : Δ ^ 3 * P ^ 2 ≤ Δ ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg P)
    nlinarith [h2]
  have hA : 4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)
      ≤ 44 * (Δ * P) ^ 2 := by
    nlinarith
  have hK2 : (K + 1 : ℝ) ≤ 2 * K := by linarith
  calc (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
      ≤ (2 * K) * (44 * (Δ * P) ^ 2) := by
        have hW0 : 0 ≤ ∑ j ∈ Finset.range K, w j :=
          Finset.sum_nonneg fun j hj => hw0 j (Finset.mem_range.mp hj)
        refine mul_le_mul hK2 hA (by positivity) (by positivity)
    _ = 88 * ((K : ℝ) * Δ) * Δ * P ^ 2 := by ring
    _ ≤ 88 * 1 * Δ * P ^ 2 := by
        have : 0 ≤ Δ * P ^ 2 := by positivity
        nlinarith
    _ = 88 * Δ * P ^ 2 := by ring

/-- **The fourth-moment `Y` budget** (deterministic; the label count is `Lc ≤ N^k`): for
`N ≥ 2`, `0 ≤ Lc ≤ N^k`, `0 ≤ Δ ≤ N^{-C_K}`, `0 ≤ P ≤ N^{C_P}` and
`C_K ≥ D₁ + 4D + k + 2C_P + 8`: `Lc · 88 Δ P² / (N^{-D})⁴ ≤ N^{-D₁}/2`. -/
private theorem GridAssemblyN_yBudget {N : ℝ} (hN2 : (2 : ℝ) ≤ N) (k : ℕ) {D D₁ C_P C_K : ℝ}
    (hCK : D₁ + 4 * D + k + 2 * C_P + 8 ≤ C_K) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : Lc ≤ N ^ k)
    {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ N ^ (-C_K)) (hP0 : 0 ≤ P) (hP : P ≤ N ^ C_P) :
    Lc * (88 * Δ * P ^ 2) / (N ^ (-D)) ^ 4 ≤ N ^ (-D₁) / 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hLk : Lc ≤ N ^ (k : ℝ) := by rwa [Real.rpow_natCast]
  have hP2 : P ^ 2 ≤ N ^ (2 * C_P) := by
    have h1 : P ^ 2 ≤ (N ^ C_P) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    have h2 : (N ^ C_P) ^ 2 = N ^ (2 * C_P) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    linarith
  have hx : (N ^ (-D)) ^ 4 = N ^ (-(4 * D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hxpos : 0 < (N ^ (-D)) ^ 4 := by positivity
  have key : Lc * (88 * Δ * P ^ 2) ≤ 88 * N ^ ((k : ℝ) + -C_K + 2 * C_P) := by
    calc Lc * (88 * Δ * P ^ 2) = 88 * (Lc * Δ * P ^ 2) := by ring
      _ ≤ 88 * (N ^ (k : ℝ) * N ^ (-C_K) * N ^ (2 * C_P)) := by gcongr
      _ = 88 * N ^ ((k : ℝ) + -C_K + 2 * C_P) := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hexp : (k : ℝ) + -C_K + 2 * C_P ≤ -D₁ + -(4 * D) + -8 := by linarith
  have hmono : N ^ ((k : ℝ) + -C_K + 2 * C_P) ≤ N ^ (-D₁ + -(4 * D) + -8) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have h8 : 88 * N ^ (-8 : ℝ) ≤ 1 / 2 := by
    have hN8 : (256 : ℝ) ≤ N ^ (8 : ℝ) := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ N ^ 8 := pow_le_pow_left₀ (by norm_num) hN2 8
    rw [Real.rpow_neg hN0.le]
    have hpos : 0 < N ^ (8 : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  rw [div_le_iff₀ hxpos, hx]
  have hsplit : N ^ (-D₁ + -(4 * D) + -8) = N ^ (-D₁) * N ^ (-(4 * D)) * N ^ (-8 : ℝ) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hA : 0 ≤ N ^ (-D₁) * N ^ (-(4 * D)) := by positivity
  calc Lc * (88 * Δ * P ^ 2)
      ≤ 88 * N ^ (-D₁ + -(4 * D) + -8) := key.trans (by linarith)
    _ = (N ^ (-D₁) * N ^ (-(4 * D))) * (88 * N ^ (-8 : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ (N ^ (-D₁) * N ^ (-(4 * D))) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h8 hA
    _ = N ^ (-D₁) / 2 * N ^ (-(4 * D)) := by ring

end Budget

/-! ## 6. The fourth-moment tail of the second-order part `Y` -/

section YMoment

variable (d : Sizes)

private lemma GridAssemblyN_norm_pow4_le_re_im (z : ℂ) : ‖z‖ ^ 4 ≤ 2 * (z.re ^ 4 + z.im ^ 4) := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  have h4 : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by rw [← h]; ring
  rw [h4]
  nlinarith [sq_nonneg (z.re ^ 2 - z.im ^ 2)]

/-- `stoppedEdgeN … b j` is `filt d (j+1)`-strongly measurable. -/
private theorem GridAssemblyN_stronglyMeasurable_stoppedEdgeN {n k : ℕ} [NeZero k] (E : ℝ)
    (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ) {τ : PathΩ d → ℕ}
    (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    {Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ}
    (hY : ∀ j, StronglyMeasurable[filt d (j + 1)] (Y j)) (b : Fin k → Z2 (d.L n)) (j : ℕ) :
    StronglyMeasurable[filt d (j + 1)] (stoppedEdgeN d E σ u t' τ Y b j) := by
  have hset : MeasurableSet[filt d (j + 1)] {ω | j < τ ω} :=
    ((filt d).mono (Nat.le_succ j)) _ (hτ j)
  exact (GridAssemblyN_stronglyMeasurable_Ugen_apply (d.L n) E σ _ _ (hY j) b).indicator hset

/-- The stopped sum at one label is the `m`-horizon sum of `stoppedEdgeN` (`sum_stopped`). -/
private theorem GridAssemblyN_stopped_sum_eq {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool)
    (u : ℕ → ℝ) (t' : ℝ) (τ : PathΩ d → ℕ)
    (Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ) (m : ℕ) (ω : PathΩ d)
    (b : Fin k → Z2 (d.L n)) :
    ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) E σ (u (j + 1)) t' (Y j ω) b
      = ∑ j ∈ Finset.range m, stoppedEdgeN d E σ u t' τ Y b j ω := by
  have h := sum_stopped (Ω' := PathΩ d) (M := ℂ)
    (fun i ω' => Ugen (d.L n) E σ (u i) t' (Y (i - 1) ω') b) τ m ω
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  rfl

/-- **The per-target fourth moment of the propagated, stopped `Y` sum**: from `YMomentBoundsN`,
`E‖(Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j)_b‖⁴ ≤ 4 (8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j)`; the fourth power is
integrable. -/
private theorem GridAssemblyN_moment4_fixed {n k : ℕ} [NeZero k] {E : ℝ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ d → ℕ} (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsN d E σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) {m : ℕ} (hm : m ≤ K)
    (b : Fin k → Z2 (d.L n)) :
    Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) (pathP d)
      ∧ ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂(pathP d)
        ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
  set W : ℕ → PathΩ d → ℂ := stoppedEdgeN d E σ u (u m) τ Y b with hWdef
  have hsum : ∀ ω, ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b = ∑ j ∈ Finset.range m, W j ω :=
    fun ω => GridAssemblyN_stopped_sum_eq d E σ u (u m) τ Y m ω b
  have hWm : ∀ j, StronglyMeasurable[filt d (j + 1)] (W j) := fun j =>
    GridAssemblyN_stronglyMeasurable_stoppedEdgeN d E σ u (u m) hτ hY.1 b j
  have h8 : ∀ j < m, _ := fun j hj => hY.2 m hm b j hj
  have hre := GridAssemblyN_mart_moment4 (μ := pathP d) (ℱ := filt d) (fun j ω => (W j ω).re) v w m
    (fun j => Complex.continuous_re.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).1) (fun j hj => (h8 j hj).2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.1)
  have him := GridAssemblyN_mart_moment4 (μ := pathP d) (ℱ := filt d) (fun j ω => (W j ω).im) v w m
    (fun j => Complex.continuous_im.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).2.1) (fun j hj => (h8 j hj).2.2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.2)
  have hpt : ∀ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4
        ≤ 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) := by
    intro ω
    rw [hsum ω]
    have := GridAssemblyN_norm_pow4_le_re_im (∑ j ∈ Finset.range m, W j ω)
    rwa [Complex.re_sum, Complex.im_sum] at this
  have hsm : StronglyMeasurable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) := by
    have heq : (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4)
        = fun ω => ‖∑ j ∈ Finset.range m, W j ω‖ ^ 4 := funext fun ω => by rw [hsum ω]
    rw [heq]
    refine (Finset.stronglyMeasurable_fun_sum (Finset.range m) fun j _ =>
      (hWm j).mono ((filt d).le (j + 1))).norm.pow 4
  have hdom : Integrable (fun ω =>
      2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4))
      (pathP d) := (hre.1.add him.1).const_mul 2
  have hint : Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) (pathP d) :=
    hdom.mono' hsm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂(pathP d)
      ≤ ∫ ω, 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4
          + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) ∂(pathP d) := integral_mono hint hdom hpt
    _ = 2 * (∫ ω, (∑ j ∈ Finset.range m, (W j ω).re) ^ 4 ∂(pathP d)
          + ∫ ω, (∑ j ∈ Finset.range m, (W j ω).im) ^ 4 ∂(pathP d)) := by
        rw [integral_const_mul, integral_add hre.1 him.1]
    _ ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
        linarith [hre.2.2, him.2.2]

/-- **Markov + union (the moment `Y` tail)**: over all targets `m ≤ K` and all labels,
`P{∃ m ≤ K, ∃ a, x ≤ ‖Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j‖_a} ≤ (K+1) Lc · 4 (8 V² + 3 W) / x⁴` with
`Lc` the number of labels, `V = Σ_{j<K} v_j`, `W = Σ_{j<K} w_j`. -/
private theorem GridAssemblyN_moment4_union {n k : ℕ} [NeZero k] {E : ℝ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ d → ℕ} (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsN d E σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) (hw0 : ∀ j < K, 0 ≤ w j)
    {x : ℝ} (hx : 0 < x) :
    (pathP d).real {ω | ∃ m ≤ K, ∃ a : Fin k → Z2 (d.L n), x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) a‖} ≤
      (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / x ^ 4 := by
  set F : ℕ → (Fin k → Z2 (d.L n)) → PathΩ d → ℝ := fun m a ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) a‖ with hFdef
  set Bd : ℝ := 4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)
    with hBd
  have hx4 : 0 < x ^ 4 := by positivity
  have hone : ∀ m ≤ K, ∀ a, (pathP d).real {ω | x ≤ F m a ω} ≤ Bd / x ^ 4 := by
    intro m hm a
    obtain ⟨hI, hM⟩ := GridAssemblyN_moment4_fixed d hτ hY hv0 hm a
    have hV : ∑ j ∈ Finset.range m, v j ≤ ∑ j ∈ Finset.range K, v j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hv0 j (Finset.mem_range.mp hj))
    have hV0 : 0 ≤ ∑ j ∈ Finset.range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hW : ∑ j ∈ Finset.range m, w j ≤ ∑ j ∈ Finset.range K, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hw0 j (Finset.mem_range.mp hj))
    have hMk : ∫ ω, F m a ω ^ 4 ∂(pathP d) ≤ Bd := by
      refine hM.trans ?_
      rw [hBd]
      have : (∑ j ∈ Finset.range m, v j) ^ 2 ≤ (∑ j ∈ Finset.range K, v j) ^ 2 :=
        pow_le_pow_left₀ hV0 hV 2
      linarith
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => by positivity) hI (x ^ 4)
    have hset : {ω | x ≤ F m a ω} = {ω | x ^ 4 ≤ F m a ω ^ 4} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact pow_le_pow_left₀ hx.le h 4
      · intro h
        exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp h
    rw [hset, le_div_iff₀ hx4]
    calc (pathP d).real {ω | x ^ 4 ≤ F m a ω ^ 4} * x ^ 4
        = x ^ 4 * (pathP d).real {ω | x ^ 4 ≤ F m a ω ^ 4} := by ring
      _ ≤ ∫ ω, F m a ω ^ 4 ∂(pathP d) := hmark
      _ ≤ Bd := hMk
  have hincl : {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ⊆ ⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Z2 (d.L n), {ω | x ≤ F m a ω} := by
    rintro ω ⟨m, hm, a, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨m, Finset.mem_range.mpr (by omega), a, ha⟩
  calc (pathP d).real {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ≤ (pathP d).real (⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Z2 (d.L n), {ω | x ≤ F m a ω}) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ m ∈ Finset.range (K + 1), (pathP d).real
          (⋃ a : Fin k → Z2 (d.L n), {ω | x ≤ F m a ω}) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.range (K + 1), ∑ a : Fin k → Z2 (d.L n),
          (pathP d).real {ω | x ≤ F m a ω} :=
        Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _m ∈ Finset.range (K + 1), ∑ _a : Fin k → Z2 (d.L n), Bd / x ^ 4 := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => ?_
        exact hone m (by have := Finset.mem_range.mp hm; omega) a
    _ = (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) * Bd / x ^ 4 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast
        ring

end YMoment

/-! ## 7. The single-scale core -/

section Core

variable (d : Sizes)

/-- **The single-scale core of `assembledN`**, with free thresholds `lam ≥ 0` (Azuma, for the first-chaos part `Z`)
and `xY > 0` (fourth-moment tail, for the second-order part `Y`).  The sharp restricted `κ, ε` act
only on `A0` and the drift; the remainder `R` uses the derived coarse `(1 + (1 - u_m)⁻¹)^k`.
`Lc = (L·L)^k` is the number of labels.  The `Z`-event is the union over `(m, a)`,
`1 ≤ m ≤ K`, of the Azuma events; the `Y`-event is `GridAssemblyN_moment4_union`. -/
private theorem GridAssemblyN_core {n k : ℕ} [NeZero k] {E : ℝ} {σ : Fin k → Bool} {u : ℕ → ℝ}
    {τ : PathΩ d → ℕ} {Δ : ℝ} {K : ℕ}
    {Cls : ℕ → ℝ → ((Fin k → Z2 (d.L n)) → ℂ) → Prop}
    {A0 : PathΩ d → (Fin k → Z2 (d.L n)) → ℂ} {A : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ}
    {Dr Z Y R : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ} {κ εK : ℕ → ℕ → ℝ} {δ0 : ℝ}
    {dDrift δD : ℕ → PathΩ d → ℝ} {c : ℕ → (Fin k → Z2 (d.L n)) → ℕ → ℝ≥0}
    {v w stepErr : ℕ → ℝ}
    (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (hZmeas : ∀ j, StronglyMeasurable[filt d (j + 1)] (Z j))
    (hsubG : ∀ m ≤ K, ∀ (a : Fin k → Z2 (d.L n)) (j : ℕ), j < m →
      SubGaussStopN d E σ u τ Z m a j (c m a j))
    (h : GridAssemblyHypN d E σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr)
    {lam : ℝ} (hlam : 0 ≤ lam) {xY : ℝ} (hxY : 0 < xY) :
    ∃ G : Set (PathΩ d), (pathP d).real Gᶜ ≤
        4 * (K : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4)
        + (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4
      ∧ ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Z2 (d.L n),
          ‖A m ω a‖ ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + εK 0 m * δ0
            + Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω)
            + lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))
            + xY
            + ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j := by
  -- the Azuma event: targets `1 ≤ m ≤ K` (the `m = 0` sum is empty)
  set GZ : Set (PathΩ d) := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ a : Fin k → Z2 (d.L n),
      lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω) a‖} with hGZdef
  have hGZbound : (pathP d).real GZ ≤
      4 * (K : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
    set E' : ℕ → (Fin k → Z2 (d.L n)) → Set (PathΩ d) := fun m a =>
      {ω | lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω) a‖} with hE'def
    have hincl : GZ ⊆ ⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Z2 (d.L n), E' m a := by
      rintro ω ⟨m, hm, a, ha⟩
      simp only [Set.mem_iUnion]
      exact ⟨m, hm, a, ha⟩
    have hone : ∀ m ∈ Finset.Icc 1 K, ∀ a : Fin k → Z2 (d.L n),
        (pathP d).real (E' m a) ≤ 4 * Real.exp (-lam ^ 2 / 4) := by
      intro m hm a
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmK : m ≤ K := (Finset.mem_Icc.mp hm).2
      have hcpos : 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ) := h.hc_pos m hm1 hmK a
      have hx0 : 0 ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by positivity
      have hax := GridAssemblyN_azuma_Ugen d E σ u hτmeas m (fun j _ => hZmeas j) a (c m a)
        (hsubG m hmK a) hx0
      have hxsq : (lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))) ^ 2
          = lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hcpos.le]
      rw [hxsq] at hax
      have hexp : -(lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) /
          (4 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) = -lam ^ 2 / 4 := by
        field_simp
      rw [hexp] at hax
      exact hax
    calc (pathP d).real GZ
        ≤ (pathP d).real (⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Z2 (d.L n), E' m a) :=
          measureReal_mono hincl (measure_ne_top _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 K, (pathP d).real (⋃ a : Fin k → Z2 (d.L n), E' m a) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 K, ∑ a : Fin k → Z2 (d.L n), (pathP d).real (E' m a) :=
          Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, ∑ _a : Fin k → Z2 (d.L n), 4 * Real.exp (-lam ^ 2 / 4) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => hone m hm a
      _ = 4 * (K : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
          rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Finset.card_univ, nsmul_eq_mul,
            nsmul_eq_mul]
          have hcard : K + 1 - 1 = K := by omega
          rw [hcard]
          ring
  -- the fourth-moment `Y` event
  set GY : Set (PathΩ d) := {ω | ∃ m ≤ K, ∃ a : Fin k → Z2 (d.L n), xY ≤
      ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) a‖} with hGYdef
  have hGYbound : (pathP d).real GY ≤ (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4 :=
    GridAssemblyN_moment4_union d hτmeas h.hY h.hv0 h.hw0 hxY
  -- the full-measure events `hexp`, `hR`
  have hexpAll : ∀ᵐ ω ∂(pathP d), ∀ m, m ≤ K → A m ω = Ugen (d.L n) E σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) E σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) := by
    refine ae_all_iff.mpr fun m => ?_
    by_cases hm : m ≤ K
    · filter_upwards [h.hexp m hm] with ω hω _ using hω
    · exact ae_of_all _ fun ω hm' => absurd hm' hm
  have hAllAE := hexpAll.and h.hR
  set Ω0c : Set (PathΩ d) := {ω | ¬ ((∀ m, m ≤ K → A m ω = Ugen (d.L n) E σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) E σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
      (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j))} with hΩ0cdef
  have hΩ0cnull : (pathP d).real Ω0c = 0 := by
    have h0 : (pathP d) Ω0c = 0 := (MeasureTheory.ae_iff).mp hAllAE
    simp [Measure.real, h0]
  refine ⟨(GZ ∪ GY ∪ Ω0c)ᶜ, ?_, ?_⟩
  · rw [compl_compl]
    calc (pathP d).real (GZ ∪ GY ∪ Ω0c)
        ≤ (pathP d).real (GZ ∪ GY) + (pathP d).real Ω0c := measureReal_union_le _ _
      _ ≤ ((pathP d).real GZ + (pathP d).real GY) + (pathP d).real Ω0c := by
          have h1 := measureReal_union_le (μ := pathP d) GZ GY
          linarith
      _ ≤ _ := by rw [hΩ0cnull]; linarith
  · intro ω hω hτpos m hmK a
    have hωGZ : ω ∉ GZ := fun h' => hω (Or.inl (Or.inl h'))
    have hωGY : ω ∉ GY := fun h' => hω (Or.inl (Or.inr h'))
    have hωΩ0 : ω ∉ Ω0c := fun h' => hω (Or.inr h')
    have hAllω : (∀ m, m ≤ K → A m ω = Ugen (d.L n) E σ (u 0) (u m) (A0 ω)
        + ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) E σ (u (j + 1)) (u m)
            ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
        (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j) := by
      by_contra hc
      exact hωΩ0 hc
    obtain ⟨hAll, hRall⟩ := hAllω
    set INIT : ℂ := Ugen (d.L n) E σ (u 0) (u m) (A0 ω) a with hINITdef
    set S1 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Dr j ω) a with hS1def
    set S2 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω) a with hS2def
    set S3 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (Y j ω) a with hS3def
    set S4 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen (d.L n) E σ (u (j + 1)) (u m) (R j ω) a with hS4def
    have hAeq : A m ω a = INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4) := by
      rw [hAll m hmK, Pi.add_apply, Finset.sum_apply]
      congr 1
      rw [Finset.sum_congr rfl (fun j _ => GridAssemblyN_Ugen_four (d.L n) E σ (u (j + 1)) (u m)
        (Δ : ℂ) (Dr j ω) (Z j ω) (Y j ω) (R j ω) a), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hINITle : ‖INIT‖
        ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 m * δ0 := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin k → Z2 (d.L n)))
      have hA0nn : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) :=
        le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b0))
      exact h.hker 0 m (Nat.zero_le m) hmK (A0 ω) _ δ0 hA0nn h.hδ0
        (fun b => Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b)) (h.hA0cls ω hτpos) a
    have hS1le : ‖S1‖ ≤ ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Ugen (d.L n) E σ (u (j + 1)) (u m) (Dr j ω) a‖
            ≤ κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact h.hker (j + 1) m hjm hmK (Dr j ω) (dDrift j ω) (δD j ω)
          (h.hdDrift0 ω j (by omega)) (h.hδD0 ω j (by omega)) (h.hdrift ω j (by omega) hjτ)
          (h.hDcls ω j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      exact add_nonneg (mul_nonneg (h.hκ0 (j + 1) m hjm hmK) (h.hdDrift0 ω j (by omega)))
        (mul_nonneg (h.hε0 (j + 1) m hjm hmK) (h.hδD0 ω j (by omega)))
    have hS1le' : ‖(Δ : ℂ) * S1‖
        ≤ Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hΔ0]
      exact mul_le_mul_of_nonneg_left hS1le h.hΔ0
    have hS2le : ‖S2‖ ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
      by_cases hm0 : m = 0
      · subst hm0
        simp [hS2def]
      · have hlt : ‖S2‖ < lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
          by_contra hc
          push Not at hc
          exact hωGZ ⟨m, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmK⟩, a, hc⟩
        exact hlt.le
    have hS3le : ‖S3‖ ≤ xY := by
      by_contra hc
      push Not at hc
      exact hωGY ⟨m, hmK, a, hc.le⟩
    have hS4le : ‖S4‖ ≤ ∑ j ∈ Finset.range m, (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
      have hm0 := h.hu0 m hmK
      have hm1 := h.hu1 m hmK
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Ugen (d.L n) E σ (u (j + 1)) (u m) (R j ω) a‖
            ≤ (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact GridAssemblyN_norm_Ugen_coarse (d.L n) (d.three_le_L n) h.hE σ
          (h.hu0 (j + 1) (by omega)) (h.hu1 (j + 1) (by omega)) hm0 hm1
          (h.hstepErr0 j (by omega)) (hRall j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      have hpos : 0 < 1 - u m := by linarith
      exact mul_nonneg (by positivity) (h.hstepErr0 j (by omega))
    rw [hAeq]
    calc ‖INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4)‖
        ≤ ‖INIT‖ + ‖(Δ : ℂ) * S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by
          have e1 := norm_add_le INIT ((Δ : ℂ) * S1 + S2 + S3 + S4)
          have e2 := norm_add_le ((Δ : ℂ) * S1 + S2 + S3) S4
          have e3 := norm_add_le ((Δ : ℂ) * S1 + S2) S3
          have e4 := norm_add_le ((Δ : ℂ) * S1) S2
          linarith
      _ ≤ _ := by linarith

/-- The number of labels `|Z2 L^k| = (L·L)^k` is at most `N^k`, `N = (W L)²` (since `L² ≤ N`). -/
private theorem GridAssemblyN_card_label (n k : ℕ) :
    Fintype.card (Fin k → Z2 (d.L n)) ≤ (d.size n) ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have h : Fintype.card (Z2 (d.L n)) = d.L n * d.L n := by
    rw [Fintype.card_prod, ZMod.card]
  rw [h]
  refine Nat.pow_le_pow_left ?_ k
  have hW : 1 ≤ d.W n := d.W_pos n
  have hL : d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ hW
  calc d.L n * d.L n ≤ (d.W n * d.L n) * (d.W n * d.L n) := Nat.mul_le_mul hL hL
    _ = d.size n := by rw [Sizes.size, sq]

end Core

/-! ## 8. The assembled pathwise bound -/

section Assembled

variable (d : Sizes)

/-- **`assembledN`** (the statement `AssembledN`): the assembled pathwise bound for `Ugen` on
`Fin k → Z2 L`.  Proof: `SizeTendsto` turns the real-variable Azuma budget (`GridAssemblyN_zBudget`) into an
eventual statement in `n`; the single-scale core (`GridAssemblyN_core`) at `lam = N^ε`,
`xY = N^{-D} > 0` gives an event `G` with `P(Gᶜ) ≤ 4 K Lc exp(-N^{2ε}/4) +
(K+1) Lc · 4 (8 V² + 3 W) / xY⁴`; the first term is `≤ N^{-D₁}/2` by the Azuma budget and the
second is `≤ N^{-D₁}/2` by `GridAssemblyN_moment4_budget_le` and the `Y` budget (exponent
`D₁ + 4D + k + 2C_P + 8 ≤ C_K`, label count `Lc ≤ N^k`).  The pathwise bound is the core's.  The
probability budget is the only place where `SizeTendsto d` is used. -/
theorem assembledN : AssembledN d := by
  intro hSize k _ ε hε D D₁ C_P C_K hCK0 hCK
  filter_upwards [hSize.eventually (GridAssemblyN_zBudget k hε D₁ C_K hCK0)] with n hn
  obtain ⟨hN2, hbudZ⟩ := hn
  intro K E σ u τ Δ Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hK1 hK hΔ hKΔ hP0 hP hv
    hw hτmeas hZmeas hsubG h
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hx : 0 < ((d.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨G, hG, hbd⟩ := GridAssemblyN_core d hτmeas hZmeas hsubG h
    (Real.rpow_nonneg hN0.le ε) hx
  refine ⟨G, hG.trans ?_, hbd⟩
  have hLc0 : (0 : ℝ) ≤ (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) := Nat.cast_nonneg _
  have hLc : (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ k := by
    exact_mod_cast GridAssemblyN_card_label d n k
  have hZ := hbudZ K _ hK hLc0 hLc
  have hbud := GridAssemblyN_moment4_budget_le h.hΔ0 hP0 hKΔ hK1 h.hv0 h.hw0 hv hw
  have hY := GridAssemblyN_yBudget hN2 k hCK hLc0 hLc h.hΔ0 hΔ hP0 hP
  have hx4 : 0 < (((d.size n : ℕ) : ℝ) ^ (-D)) ^ 4 := by positivity
  have hYle : (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        / (((d.size n : ℕ) : ℝ) ^ (-D)) ^ 4 ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) / 2 := by
    refine le_trans ?_ hY
    rw [show (K + 1 : ℝ) * (Fintype.card (Fin k → Z2 (d.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        = (Fintype.card (Fin k → Z2 (d.L n)) : ℝ) * ((K + 1 : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbud hLc0) hx4.le
  linarith

end Assembled

end RBM.Ind

end
