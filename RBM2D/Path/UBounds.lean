/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Scales
import RBM2D.Path.Kernel
import RBM2D.Propagator.Bounds
import RBM2D.Propagator.Deriv
import RBM2D.Gauss.SpectralAlgebra

/-!
# The `𝒰` bounds: nonnegativity, row sums, `lem:sum_Ndecay` at `n = 2`, back and one-step kernels

Paper: arXiv:2503.07606, `lem:sum_Ndecay` and `def_Ustz`.

* `thetaGenMat`, `thetaGen` : the generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰`.
* `normSqSpectralMOne` : `|m|² = 1` on `|E| ≤ 2` (from `norm_spectralM`).
* `ukerNonneg` : for real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1` the kernel `ukerMat` is entrywise a
  nonnegative real.
* `ukerRowSum` : the row sums are `(1 - vξ)/(1 - wξ)` (`sum_Theta_row`-type argument).
* `sumNdecay`, `sumNdecayEta` : `lem:sum_Ndecay` at `n = 2`, deterministic with constant `1`.
* `uopBack` : `‖𝒰_{t,u} A‖_max ≤ 4 ‖A‖_max`.
* `uopOneStep` : `‖𝒰_{u,u+Δ} A - A - Δ Θ_u A‖_max ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`.

The d = 2 input is only `Theta_mul`/`mul_Theta`, `Theta_eq_tsum`, `sum_Theta_row`,
`Theta_sub_Theta`, the operator-norm bounds of `Propagator/Bounds.lean`, and the entries of
`SB` on `Z2 L`; no d = 1 closed form is used.
-/

noncomputable section

namespace RBM.Path

open Matrix RBM RBM.Gauss

section Hierarchy

variable (L : ℕ) [NeZero L]

/-- The per-slot generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (the `w`-derivative of `ukerMat`;
`DefTHUST` with the factor `S^{(B)}`). -/
def thetaGenMat (ξ : ℂ) (u : ℝ) : Matrix (Z2 L) (Z2 L) ℂ :=
  ξ • (SB L * Theta L ((u : ℂ) * ξ))

/-- `Θ_{u,(+,-)} ∘ A`, acting on the left in each slot (the generator of `Uop`). -/
def thetaGen (ξ : ℂ) (u : ℝ) (A : Z2 L × Z2 L → ℂ) : Z2 L × Z2 L → ℂ :=
  fun a => ∑ b : Z2 L,
    (thetaGenMat L ξ u a.1 b * A (b, a.2) + thetaGenMat L ξ u a.2 b * A (a.1, b))


end Hierarchy

/-- **One step of `𝒰`**, the grid form of `∂_w 𝒰_{u,w}|_{w=u} = Θ_u`:
`‖𝒰_{u,u+Δ}A - A - Δ Θ_u A‖_max ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`. -/
def UopOneStep : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ u Δ : ℝ, 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
    ∀ (A : Z2 L × Z2 L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Z2 L × Z2 L,
      ‖Uop L ξ u (u + Δ) A a - A a - (Δ : ℂ) * thetaGen L ξ u A a‖ ≤
        3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α

/-- `|m|² = 1` on `|E| ≤ 2`, so `Uop` at `ξ = |m|²` is `Uop` at `ξ = 1`. -/
def NormSqSpectralMOne : Prop :=
  ∀ E : ℝ, |E| ≤ 2 → Complex.normSq (spectralM E) = 1

/-- **Nonnegativity**: for real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1`, the kernel
`(1 - vξS)Θ_{wξ} = I + (w-v)ξ SΘ_{wξ}` is real and entrywise `≥ 0` (needs `v ≤ w`). -/
def UkerNonneg : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ v → v ≤ w → w * ξ < 1 →
    ∀ a b : Z2 L, (ukerMat L (ξ : ℂ) v w a b).im = 0 ∧ 0 ≤ (ukerMat L (ξ : ℂ) v w a b).re

/-- **Row sums**: `Σ_b ((1 - vξS)Θ_{wξ})_{ab} = (1 - vξ)/(1 - wξ)`. -/
def UkerRowSum : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ w → w * ξ < 1 → ∀ a : Z2 L,
    ∑ b : Z2 L, ukerMat L (ξ : ℂ) v w a b = (((1 - v * ξ) / (1 - w * ξ) : ℝ) : ℂ)

/-- **`lem:sum_Ndecay`, `n = 2`**, deterministic with constant 1. -/
def SumNdecay : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ v → v ≤ w → w * ξ < 1 →
    ∀ (A : Z2 L × Z2 L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Z2 L × Z2 L,
      ‖Uop L (ξ : ℂ) v w A a‖ ≤ ((1 - v * ξ) / (1 - w * ξ)) ^ 2 * α

/-- **`lem:sum_Ndecay` in `η` form** at `ξ = |m|²`: factor `(η_v/η_w)²`. -/
def SumNdecayEta : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E v w : ℝ, |E| < 2 → 0 ≤ v → v ≤ w → w < 1 →
    ∀ (A : Z2 L × Z2 L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Z2 L × Z2 L,
      ‖Uop L (Complex.normSq (spectralM E) : ℂ) v w A a‖ ≤ (etaT E v / etaT E w) ^ 2 * α

/-- **Back-kernel bound**: `‖𝒰_{t,u} A‖_max ≤ 4 ‖A‖_max` for `0 ≤ u ≤ t < 1`. -/
def UopBack : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ u t : ℝ, 0 ≤ u → u ≤ t → t < 1 →
    ∀ (A : Z2 L × Z2 L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Z2 L × Z2 L,
      ‖Uop L ξ t u A a‖ ≤ 4 * α

/-! ## Helpers (all `private`) -/

section NonnegHelpers

variable (L : ℕ) [NeZero L]

/-- `z` is a nonnegative real number, viewed inside `ℂ`; bookkeeping for the sign arguments. -/
private def RealNonneg (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

private theorem RealNonneg.ofNonneg {r : ℝ} (hr : 0 ≤ r) : RealNonneg (r : ℂ) := ⟨r, hr, rfl⟩

private theorem realNonneg_zero : RealNonneg (0 : ℂ) := ⟨0, le_refl _, by simp⟩

private theorem realNonneg_one : RealNonneg (1 : ℂ) := ⟨1, zero_le_one, by simp⟩

private theorem RealNonneg.add {z w : ℂ} (hz : RealNonneg z) (hw : RealNonneg w) :
    RealNonneg (z + w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 + r2, by positivity, by rw [e1, e2]; push_cast; ring⟩

private theorem RealNonneg.mul {z w : ℂ} (hz : RealNonneg z) (hw : RealNonneg w) :
    RealNonneg (z * w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 * r2, mul_nonneg hr1 hr2, by rw [e1, e2]; push_cast; ring⟩

private theorem RealNonneg.eq_ofReal_re {z : ℂ} (hz : RealNonneg z) : z = (z.re : ℂ) := by
  obtain ⟨r, _, e⟩ := hz; rw [e]; simp

private theorem RealNonneg.re_nonneg {z : ℂ} (hz : RealNonneg z) : 0 ≤ z.re := by
  obtain ⟨r, hr, e⟩ := hz; rw [e]; simpa using hr

private theorem RealNonneg.norm_eq {z : ℂ} (hz : RealNonneg z) : ‖z‖ = z.re := by
  obtain ⟨r, hr, e⟩ := hz
  rw [e, Complex.norm_of_nonneg hr, Complex.ofReal_re]

private theorem RealNonneg.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, RealNonneg (f i)) : RealNonneg (∑ i ∈ s, f i) :=
  Finset.sum_induction f RealNonneg (fun _ _ ha hb => ha.add hb) realNonneg_zero h

private theorem RealNonneg.tsum {f : ℕ → ℂ} (hf : Summable f)
    (h : ∀ n, RealNonneg (f n)) : RealNonneg (∑' n, f n) := by
  have hnn : ∀ n, 0 ≤ (f n).re := fun n => (h n).re_nonneg
  have hcast : ∀ n, f n = ((f n).re : ℂ) := fun n => (h n).eq_ofReal_re
  have hnormeq : ∀ n, ‖f n‖ = (f n).re := fun n => (h n).norm_eq
  have hreSummable : Summable (fun n => (f n).re) := by
    have hns := hf.norm
    simpa only [hnormeq] using hns
  refine ⟨∑' n, (f n).re, tsum_nonneg hnn, ?_⟩
  calc ∑' n, f n = ∑' n, ((f n).re : ℂ) := tsum_congr hcast
    _ = ((∑' n, (f n).re : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm

omit [NeZero L] in
/-- The five-point kernel `S^{(B)}` has nonnegative real entries (d = 2: `sbKernel` is `1/5` on
the five-point support). -/
private theorem SB_realNonneg (a b : Z2 L) : RealNonneg (SB L a b) := by
  rw [SB_apply]
  unfold sbKernel
  split_ifs
  · exact ⟨(5 : ℝ)⁻¹, by norm_num, by push_cast; ring⟩
  · exact realNonneg_zero

private theorem SBpow_realNonneg (k : ℕ) : ∀ a b : Z2 L, RealNonneg ((SB L ^ k) a b) := by
  induction k with
  | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      split_ifs
      · exact realNonneg_one
      · exact realNonneg_zero
  | succ k ih =>
      intro a b
      rw [pow_succ, Matrix.mul_apply]
      exact RealNonneg.sum Finset.univ _ (fun c _ => (ih a c).mul (SB_realNonneg L c b))

open scoped Matrix.Norms.Operator in
private theorem theta_entries_summable (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) (a b : Z2 L) :
    Summable (fun k : ℕ => ((z • SB L) ^ k) a b) := by
  have hpow := summable_norm_pow L hL hz
  have hnorm : Summable (fun k : ℕ => ‖((z • SB L) ^ k) a b‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_entry_le_norm L _ a b) hpow
  exact hnorm.of_norm

private theorem theta_apply_eq_tsum (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) (a b : Z2 L) :
    Theta L z a b = ∑' k : ℕ, ((z • SB L) ^ k) a b := by
  have hentries : ∀ a b : Z2 L, Summable (fun k : ℕ => ((z • SB L) ^ k) a b) :=
    fun a b => theta_entries_summable L hL hz a b
  have hrows : ∀ a : Z2 L, Summable (fun k : ℕ => ((z • SB L) ^ k) a) :=
    fun a => Pi.summable.mpr (fun b => hentries a b)
  have hmat : Summable (fun k : ℕ => (z • SB L) ^ k) := Pi.summable.mpr hrows
  rw [Theta_eq_tsum L hL hz]
  have h1 := congrFun (Pi.tsum_apply (x := a) hmat) b
  have h2 := Pi.tsum_apply (x := b) (hrows a)
  exact h1.trans h2

/-- For real `z ∈ [0,1)` the entries of `Θ_z` are nonnegative reals (via the Neumann series
`Theta_eq_tsum`). -/
private theorem Theta_real_realNonneg (hL : 3 ≤ L) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (a b : Z2 L) : RealNonneg (Theta L (z : ℂ) a b) := by
  have hzNorm : ‖(z : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz1
  rw [theta_apply_eq_tsum L hL hzNorm a b]
  refine RealNonneg.tsum (theta_entries_summable L hL hzNorm a b) (fun k => ?_)
  have hterm : (((z : ℂ) • SB L) ^ k) a b = (z : ℂ) ^ k * (SB L ^ k) a b := by
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  rw [hterm]
  have hcoef : RealNonneg ((z : ℂ) ^ k) := ⟨z ^ k, pow_nonneg hz0 k, by push_cast; ring⟩
  exact hcoef.mul (SBpow_realNonneg L k a b)

private theorem SB_mul_Theta_real_realNonneg (hL : 3 ≤ L) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (a b : Z2 L) : RealNonneg ((SB L * Theta L (z : ℂ)) a b) := by
  rw [Matrix.mul_apply]
  exact RealNonneg.sum Finset.univ _
    (fun c _ => (SB_realNonneg L a c).mul (Theta_real_realNonneg L hL hz0 hz1 c b))

end NonnegHelpers

section NormHelpers

variable (L : ℕ) [NeZero L]

/-- `‖(s : ℂ) ξ‖ = s ‖ξ‖` for `s ≥ 0`. -/
private theorem norm_ofReal_mul_eq {s : ℝ} (hs : 0 ≤ s) (ξ : ℂ) : ‖(s : ℂ) * ξ‖ = s * ‖ξ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]

/-- `‖(s : ℂ) ξ‖ < 1` from `‖ξ‖ ≤ 1` and `0 ≤ s < 1`. -/
private theorem norm_ofReal_mul_lt {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s < 1) : ‖(s : ℂ) * ξ‖ < 1 := by
  rw [norm_ofReal_mul_eq h0]
  calc s * ‖ξ‖ ≤ s * 1 := mul_le_mul_of_nonneg_left hξ h0
    _ = s := mul_one s
    _ < 1 := h1

/-- `‖z‖ = re z` for a complex number with `im z = 0` and `0 ≤ re z`. -/
private theorem norm_eq_re_of {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  calc ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
    _ = z.re := Complex.norm_of_nonneg hre

/-- Arithmetic core for the generator: for `r ≤ 1`, `0 ≤ s < 1`,
`r (1 - s r)⁻¹ ≤ (1 - s)⁻¹`. -/
private theorem arith_gen {r s : ℝ} (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    r * (1 - s * r)⁻¹ ≤ (1 - s)⁻¹ := by
  have hsr : s * r ≤ s := mul_le_of_le_one_right hs0 hr1
  have hd : 0 < 1 - s * r := by linarith
  have hd' : 0 < 1 - s := by linarith
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hd hd']
  nlinarith

/-- `(1 - s r)⁻¹ ≤ (1 - s)⁻¹` for `0 ≤ r ≤ 1`, `0 ≤ s < 1`. -/
private theorem arith_inv {r s : ℝ} (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s * r)⁻¹ ≤ (1 - s)⁻¹ := by
  have hd' : 0 < 1 - s := by linarith
  refine inv_anti₀ hd' ?_
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hr1)]

end NormHelpers

section KernelIdentity

variable (L : ℕ) [NeZero L]

/-- The exact form `𝒰`-kernel `= 1 + (w - v) · (ξ S Θ_{wξ})`, from `(1 - wξS) Θ_{wξ} = 1`:
`(1 - vξS) Θ_{wξ} = Θ_{wξ} - vξ SΘ_{wξ} = 1 + (w - v) ξ SΘ_{wξ}` (paper `def_Ustz_2`). -/
private theorem ukerMat_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ} (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v w = 1 + ((w : ℂ) - (v : ℂ)) • thetaGenMat L ξ w := by
  have h := mul_Theta L hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat thetaGenMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

/-- Entrywise form of `ukerMat_eq`. -/
private theorem ukerMat_apply_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ} (hw : ‖(w : ℂ) * ξ‖ < 1)
    (a b : Z2 L) :
    ukerMat L ξ v w a b =
      (1 : Matrix (Z2 L) (Z2 L) ℂ) a b + ((w : ℂ) - (v : ℂ)) * thetaGenMat L ξ w a b := by
  rw [ukerMat_eq L hL hw]
  simp [Matrix.add_apply, Matrix.smul_apply]

/-- Entries of the generator for real `ξ ≥ 0`, `w ≥ 0`, `wξ < 1` are nonnegative reals. -/
private theorem thetaGenMat_realNonneg (hL : 3 ≤ L) {ξ w : ℝ} (hξ : 0 ≤ ξ) (hw : 0 ≤ w)
    (hwξ : w * ξ < 1) (a b : Z2 L) : RealNonneg (thetaGenMat L (ξ : ℂ) w a b) := by
  have hz : ((w : ℂ) * (ξ : ℂ)) = ((w * ξ : ℝ) : ℂ) := by push_cast; ring
  have h := SB_mul_Theta_real_realNonneg L hL (mul_nonneg hw hξ) hwξ a b
  rw [← hz] at h
  simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul]
  exact (RealNonneg.ofNonneg hξ).mul h

end KernelIdentity

section RowHelpers

variable (L : ℕ) [NeZero L]

open scoped Matrix.Norms.Operator

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm (as `sum_norm_Theta_row_le`). -/
private theorem sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}`. -/
private theorem sum_norm_thetaGenMat_row_le (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Z2 L, ‖thetaGenMat L ξ s x c‖ =
      ‖ξ‖ * ‖(SB L * Theta L ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le_opNorm L _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L ((s : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L ((s : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u`: by the resolvent
identity `Theta_sub_Theta`,
`ξ S Θ_{(u+Δ)ξ} - ξ S Θ_{uξ} = Δ ξ² S Θ_{(u+Δ)ξ} S Θ_{uξ}`. -/
private theorem sum_norm_thetaGenMat_diff_row_le (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hu : ‖(u : ℂ) * ξ‖ < 1) (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ ≤
      Δ * ‖ξ‖ ^ 2 * ((1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹) := by
  have hTsub := Theta_sub_Theta L hL (ξ := (u : ℂ) * ξ) (ζ := ((u + Δ : ℝ) : ℂ) * ξ) hu hd
  have hcast : ((u + Δ : ℝ) : ℂ) * ξ - (u : ℂ) * ξ = ((Δ : ℝ) : ℂ) * ξ := by
    push_cast; ring
  rw [hcast] at hTsub
  have hM : thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u =
      (((Δ : ℝ) : ℂ) * ξ ^ 2) •
        (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ))) := by
    unfold thetaGenMat
    rw [← smul_sub, ← Matrix.mul_sub, hTsub, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hnormeq : ∀ c : Z2 L, ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ =
      Δ * ‖ξ‖ ^ 2 * ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L *
        Theta L ((u : ℂ) * ξ))) x c‖ := by
    intro c
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΔ, norm_pow]
  simp_rw [hnormeq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le_opNorm L _ x).trans ?_) (by positivity)
  calc ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ))‖
      ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ)‖ := by
        rw [norm_SB L hL, one_mul]
    _ ≤ ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L‖ * ‖Theta L ((u : ℂ) * ξ)‖ := norm_mul_le _ _
    _ ≤ (‖Theta L (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖SB L‖) * ‖Theta L ((u : ℂ) * ξ)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖Theta L ((u : ℂ) * ξ)‖ := by
        rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹ :=
        mul_le_mul (norm_Theta_le L hL hd) (norm_Theta_le L hL hu) (norm_nonneg _)
          (inv_nonneg.mpr (by linarith))

end RowHelpers

section SumHelpers

variable (L : ℕ) [NeZero L]

/-- A matrix with row `ℓ¹` norms `≤ R` maps a max-norm bounded vector to a max-norm bounded
one. -/
private theorem norm_sum_mul_le {B : Matrix (Z2 L) (Z2 L) ℂ} {R α : ℝ}
    (hB : ∀ x : Z2 L, ∑ c : Z2 L, ‖B x c‖ ≤ R) (x : Z2 L) {f : Z2 L → ℂ}
    (hf : ∀ b, ‖f b‖ ≤ α) : ‖∑ b : Z2 L, B x b * f b‖ ≤ R * α := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hf x)
  calc ‖∑ b : Z2 L, B x b * f b‖ ≤ ∑ b : Z2 L, ‖B x b * f b‖ := norm_sum_le _ _
    _ = ∑ b : Z2 L, ‖B x b‖ * ‖f b‖ := by simp only [norm_mul]
    _ ≤ ∑ b : Z2 L, ‖B x b‖ * α :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) (norm_nonneg _)
    _ = (∑ b : Z2 L, ‖B x b‖) * α := (Finset.sum_mul _ _ _).symm
    _ ≤ R * α := mul_le_mul_of_nonneg_right (hB x) hα

/-- The two-slot sum over `Z2 L × Z2 L` as an iterated sum. -/
private theorem sum_prod_eq_iter (P Q : Matrix (Z2 L) (Z2 L) ℂ) (A : Z2 L × Z2 L → ℂ)
    (a : Z2 L × Z2 L) :
    ∑ b : Z2 L × Z2 L, P a.1 b.1 * Q a.2 b.2 * A b =
      ∑ b₁ : Z2 L, P a.1 b₁ * ∑ b₂ : Z2 L, Q a.2 b₂ * A (b₁, b₂) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b₂ _ => by ring

private theorem norm_sum_prod_le {P Q : Matrix (Z2 L) (Z2 L) ℂ} {R R' α : ℝ}
    (hP : ∀ x : Z2 L, ∑ c : Z2 L, ‖P x c‖ ≤ R) (hQ : ∀ x : Z2 L, ∑ c : Z2 L, ‖Q x c‖ ≤ R')
    {A : Z2 L × Z2 L → ℂ} (hA : ∀ b, ‖A b‖ ≤ α) (a : Z2 L × Z2 L) :
    ‖∑ b : Z2 L × Z2 L, P a.1 b.1 * Q a.2 b.2 * A b‖ ≤ R * (R' * α) := by
  rw [sum_prod_eq_iter L P Q A a]
  exact norm_sum_mul_le L hP a.1 (fun b₁ => norm_sum_mul_le L hQ a.2 (fun b₂ => hA (b₁, b₂)))

/-- `Uop` bounded by the square of a uniform row `ℓ¹` bound of `ukerMat`. -/
private theorem norm_Uop_le_of_rows (ξ : ℂ) (v w : ℝ) {R α : ℝ}
    (hR : ∀ x : Z2 L, ∑ c : Z2 L, ‖ukerMat L ξ v w x c‖ ≤ R) {A : Z2 L × Z2 L → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ α) (a : Z2 L × Z2 L) : ‖Uop L ξ v w A a‖ ≤ R ^ 2 * α := by
  calc ‖Uop L ξ v w A a‖ ≤ R * (R * α) := norm_sum_prod_le L hR hR hA a
    _ = R ^ 2 * α := by ring

end SumHelpers

/-! ## The theorems -/

/-- **`normSqSpectralMOne`**: `|m|² = 1` on `|E| ≤ 2` (from `norm_spectralM`). -/
theorem normSqSpectralMOne : NormSqSpectralMOne := by
  intro E hE
  rw [Complex.normSq_eq_norm_sq, norm_spectralM hE]
  norm_num

/-- **`ukerNonneg`**: `ukerMat` is entrywise a nonnegative real for real `ξ ≥ 0`, `0 ≤ v ≤ w`,
`wξ < 1` (using `ukerMat = 1 + (w - v) · ξ SΘ_{wξ}`). -/
theorem ukerNonneg : UkerNonneg := by
  intro L _ hL ξ v w hξ hv hvw hwξ a b
  have hw0 : 0 ≤ w := hv.trans hvw
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw0 hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  rw [ukerMat_apply_eq L hL hnorm]
  have h1 : RealNonneg ((1 : Matrix (Z2 L) (Z2 L) ℂ) a b) := by
    rw [Matrix.one_apply]
    split_ifs
    · exact realNonneg_one
    · exact realNonneg_zero
  have hc : RealNonneg ((w : ℂ) - (v : ℂ)) :=
    ⟨w - v, by linarith, by push_cast; ring⟩
  have hres := h1.add (hc.mul (thetaGenMat_realNonneg L hL hξ hw0 hwξ a b))
  obtain ⟨r, hr, hreq⟩ := hres
  rw [hreq]
  simpa using hr

/-- **`ukerRowSum`**: the row sums of `ukerMat` are `(1 - vξ)/(1 - wξ)` (`(1 - vξS)Θ_{wξ} 1`,
from `Theta_mulVec_one` and `SB_mulVec_one`). -/
theorem ukerRowSum : UkerRowSum := by
  intro L _ hL ξ v w hξ hw hwξ a
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  have hmv : ukerMat L (ξ : ℂ) v w *ᵥ (1 : Z2 L → ℂ) =
      ((1 - (w : ℂ) * ξ)⁻¹ * (1 - (v : ℂ) * ξ)) • (1 : Z2 L → ℂ) := by
    unfold ukerMat
    rw [← Matrix.mulVec_mulVec, Theta_mulVec_one L hL hnorm, Matrix.mulVec_smul, sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, SB_mulVec_one L hL]
    funext x
    simp [Pi.smul_apply, Pi.sub_apply, mul_comm]
  have h := congrFun hmv a
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  have hne : (1 - (w : ℂ) * ξ) ≠ 0 := one_sub_ne_zero hnorm
  push_cast
  field_simp

private theorem ukerMat_row_norm_eq (L : ℕ) [NeZero L] {ξ v w : ℝ} (hL : 3 ≤ L)
    (hξ : 0 ≤ ξ) (hv : 0 ≤ v) (hvw : v ≤ w) (hwξ : w * ξ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖ukerMat L (ξ : ℂ) v w x c‖ = (1 - v * ξ) / (1 - w * ξ) := by
  have hn : ∀ c : Z2 L, ‖ukerMat L (ξ : ℂ) v w x c‖ = (ukerMat L (ξ : ℂ) v w x c).re := by
    intro c
    obtain ⟨him, hre⟩ := ukerNonneg L hL ξ v w hξ hv hvw hwξ x c
    exact norm_eq_re_of him hre
  simp_rw [hn]
  have hs := ukerRowSum L hL ξ v w hξ (hv.trans hvw) hwξ x
  have hre := congrArg Complex.re hs
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  exact hre

/-- **`sumNdecay`** (`lem:sum_Ndecay`, `n = 2`): `‖𝒰_{v,w} A‖_max ≤ ((1 - vξ)/(1 - wξ))² ‖A‖_max`;
the kernel entries are nonnegative reals (`ukerNonneg`), so the row `ℓ¹` norm is the row sum
(`ukerRowSum`). -/
theorem sumNdecay : SumNdecay := by
  intro L _ hL ξ v w hξ hv hvw hwξ A α hA a
  exact norm_Uop_le_of_rows L (ξ : ℂ) v w
    (fun x => (ukerMat_row_norm_eq L hL hξ hv hvw hwξ x).le) hA a

/-- **`sumNdecayEta`**: the `η` form of `sumNdecay` at `ξ = |m|² = 1`. -/
theorem sumNdecayEta : SumNdecayEta := by
  intro L _ hL E v w hE hv hvw hw A α hA a
  have h1 : (Complex.normSq (spectralM E) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [normSqSpectralMOne E hE.le]
  rw [h1, etaT_div_etaT hE (lt_of_le_of_lt hvw hw) hw]
  have := sumNdecay L hL 1 v w zero_le_one hv hvw (by rwa [mul_one]) A α hA a
  simpa only [mul_one] using this

/-- The row `ℓ¹` norm of the back kernel `(1 - tξS)Θ_{uξ}`, `u ≤ t < 1`, `‖ξ‖ ≤ 1`, is at most
`1 + (t - u)‖ξ‖(1 - u‖ξ‖)⁻¹ ≤ 2`. -/
private theorem sum_norm_ukerMat_back_row_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖ukerMat L ξ t u x c‖ ≤ 2 := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have hu' : ‖(u : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ hu0 hu1
  have hrow := sum_norm_thetaGenMat_row_le L hL hu' x
  rw [norm_ofReal_mul_eq hu0] at hrow
  have hentry : ∀ c : Z2 L, ‖ukerMat L ξ t u x c‖ ≤
      ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ + (t - u) * ‖thetaGenMat L ξ u x c‖ := by
    intro c
    rw [ukerMat_apply_eq L hL hu']
    refine (norm_add_le _ _).trans (add_le_add (le_refl _) (le_of_eq ?_))
    rw [norm_mul]
    congr 1
    rw [show (u : ℂ) - (t : ℂ) = -((t - u : ℝ) : ℂ) by push_cast; ring, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hone : ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ = 1 := by
    have hc : ∀ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ = if x = c then 1 else 0 := by
      intro c
      rw [Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ c : Z2 L, ‖ukerMat L ξ t u x c‖
      ≤ ∑ c : Z2 L, (‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ + (t - u) * ‖thetaGenMat L ξ u x c‖) :=
        Finset.sum_le_sum fun c _ => hentry c
    _ = 1 + (t - u) * ∑ c : Z2 L, ‖thetaGenMat L ξ u x c‖ := by
        rw [Finset.sum_add_distrib, hone, Finset.mul_sum]
    _ ≤ 1 + (t - u) * (‖ξ‖ * (1 - u * ‖ξ‖)⁻¹) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrow (by linarith))
    _ ≤ 2 := by
        have hr0 : 0 ≤ ‖ξ‖ := norm_nonneg _
        have hden : 0 < 1 - u * ‖ξ‖ := by
          have : u * ‖ξ‖ ≤ u := mul_le_of_le_one_right hu0 hξ
          linarith
        have htr : t * ‖ξ‖ ≤ t := mul_le_of_le_one_right (hu0.trans hut) hξ
        have hnum : (t - u) * ‖ξ‖ ≤ 1 - u * ‖ξ‖ := by nlinarith
        have : (t - u) * (‖ξ‖ * (1 - u * ‖ξ‖)⁻¹) ≤ 1 := by
          rw [← mul_assoc, ← div_eq_mul_inv]
          exact (div_le_one hden).mpr hnum
        linarith

/-- **`uopBack`**: the back kernel `𝒰_{t,u}`, `u ≤ t`, has max-norm at most `4`. -/
theorem uopBack : UopBack := by
  intro L _ hL ξ hξ u t hu hut ht A α hA a
  have h := norm_Uop_le_of_rows L ξ t u (fun x => sum_norm_ukerMat_back_row_le L hL hξ hu hut ht x)
    hA a
  calc ‖Uop L ξ t u A a‖ ≤ 2 ^ 2 * α := h
    _ = 4 * α := by norm_num

/-- **`uopOneStep`**: one step of `𝒰` (at `n = 2` with the same kernel in both slots): with
`G' = ξ SΘ_{(u+Δ)ξ}` and `G = ξ SΘ_{uξ}`, `ukerMat ξ u (u+Δ) = 1 + Δ G'` and
`𝒰A - A - ΔΘ_u A = Δ ((G'-G)⊗1 + 1⊗(G'-G)) A + Δ² (G'⊗G') A`. -/
theorem uopOneStep : UopOneStep := by
  intro L _ hL ξ hξ u Δ hu hΔ huΔ A α hA a
  have hu1 : u < 1 := by linarith
  have hu' : ‖(u : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ hu hu1
  have hd' : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ (by linarith) huΔ
  set G' : Matrix (Z2 L) (Z2 L) ℂ := thetaGenMat L ξ (u + Δ) with hG'
  set G : Matrix (Z2 L) (Z2 L) ℂ := thetaGenMat L ξ u with hG
  have hK : ∀ x y : Z2 L, ukerMat L ξ u (u + Δ) x y =
      (1 : Matrix (Z2 L) (Z2 L) ℂ) x y + (Δ : ℂ) * G' x y := by
    intro x y
    rw [ukerMat_apply_eq L hL hd']
    congr 2
    push_cast; ring
  -- the inner sums
  have hin : ∀ b₁ : Z2 L, ∑ b₂ : Z2 L, ukerMat L ξ u (u + Δ) a.2 b₂ * A (b₁, b₂) =
      A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂) := by
    intro b₁
    simp only [hK, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
  have hexp : Uop L ξ u (u + Δ) A a = A a
      + (Δ : ℂ) * (∑ b : Z2 L, G' a.1 b * A (b, a.2) + ∑ b : Z2 L, G' a.2 b * A (a.1, b))
      + (Δ : ℂ) ^ 2 * ∑ b₁ : Z2 L, G' a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂) := by
    change ∑ b : Z2 L × Z2 L, ukerMat L ξ u (u + Δ) a.1 b.1 * ukerMat L ξ u (u + Δ) a.2 b.2 * A b
      = _
    rw [sum_prod_eq_iter L (ukerMat L ξ u (u + Δ)) (ukerMat L ξ u (u + Δ)) A a]
    simp only [hin]
    have hterm : ∀ b₁ : Z2 L, ukerMat L ξ u (u + Δ) a.1 b₁ *
        (A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂)) =
        (1 : Matrix (Z2 L) (Z2 L) ℂ) a.1 b₁ * A (b₁, a.2)
        + (Δ : ℂ) * ((1 : Matrix (Z2 L) (Z2 L) ℂ) a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂))
        + (Δ : ℂ) * (G' a.1 b₁ * A (b₁, a.2))
        + (Δ : ℂ) ^ 2 * (G' a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂)) := by
      intro b₁
      rw [hK]; ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hgen : thetaGen L ξ u A a =
      ∑ b : Z2 L, G a.1 b * A (b, a.2) + ∑ b : Z2 L, G a.2 b * A (a.1, b) := by
    unfold thetaGen
    rw [Finset.sum_add_distrib]
  have hdiff : Uop L ξ u (u + Δ) A a - A a - (Δ : ℂ) * thetaGen L ξ u A a =
      (Δ : ℂ) * (∑ b : Z2 L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Z2 L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Z2 L, G' a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂) := by
    rw [hexp, hgen]
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hβ : 0 < 1 - (u + Δ) := by linarith
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
  have hβ0 : 0 ≤ β := inv_nonneg.mpr hβ.le
  have hnd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ = (u + Δ) * ‖ξ‖ := norm_ofReal_mul_eq (by linarith) ξ
  have hnu : ‖(u : ℂ) * ξ‖ = u * ‖ξ‖ := norm_ofReal_mul_eq hu ξ
  have hR1 : ∀ x : Z2 L, ∑ c : Z2 L, ‖G' x c‖ ≤ β := by
    intro x
    refine (sum_norm_thetaGenMat_row_le L hL hd' x).trans ?_
    rw [hnd]
    exact arith_gen hξ (by linarith) huΔ
  have hR2 : ∀ x : Z2 L, ∑ c : Z2 L, ‖(G' - G) x c‖ ≤ Δ * β ^ 2 := by
    intro x
    refine (sum_norm_thetaGenMat_diff_row_le L hL hΔ hu' hd' x).trans ?_
    rw [hnd, hnu]
    have h1 : (1 - (u + Δ) * ‖ξ‖)⁻¹ ≤ β := arith_inv hξ (by linarith) huΔ
    have h2 : (1 - u * ‖ξ‖)⁻¹ ≤ β :=
      (arith_inv hξ hu hu1).trans (inv_anti₀ hβ (by linarith))
    have hQ : 0 ≤ (1 - u * ‖ξ‖)⁻¹ := inv_nonneg.mpr (by
      have : u * ‖ξ‖ ≤ u := mul_le_of_le_one_right hu hξ
      linarith)
    have hxi2 : ‖ξ‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖ξ‖ := norm_nonneg _
      nlinarith
    calc Δ * ‖ξ‖ ^ 2 * ((1 - (u + Δ) * ‖ξ‖)⁻¹ * (1 - u * ‖ξ‖)⁻¹)
        ≤ Δ * 1 * (β * β) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hxi2 hΔ) (mul_le_mul h1 h2 hQ hβ0)
            (mul_nonneg (inv_nonneg.mpr (by
              have : (u + Δ) * ‖ξ‖ ≤ u + Δ := mul_le_of_le_one_right (by linarith) hξ
              linarith)) hQ)
            (by positivity)
      _ = Δ * β ^ 2 := by ring
  have hDA : ‖∑ b : Z2 L, (G' - G) a.1 b * A (b, a.2)‖ ≤ Δ * β ^ 2 * α :=
    norm_sum_mul_le L hR2 a.1 (fun b => hA (b, a.2))
  have hDB : ‖∑ b : Z2 L, (G' - G) a.2 b * A (a.1, b)‖ ≤ Δ * β ^ 2 * α :=
    norm_sum_mul_le L hR2 a.2 (fun b => hA (a.1, b))
  have hS3 : ‖∑ b₁ : Z2 L, G' a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂)‖ ≤ β * (β * α) :=
    norm_sum_mul_le L hR1 a.1 (fun b₁ => norm_sum_mul_le L hR1 a.2 (fun b₂ => hA (b₁, b₂)))
  rw [hdiff]
  have hnΔ : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ]
  calc ‖(Δ : ℂ) * (∑ b : Z2 L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Z2 L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Z2 L, G' a.1 b₁ * ∑ b₂ : Z2 L, G' a.2 b₂ * A (b₁, b₂)‖
      ≤ Δ * (Δ * β ^ 2 * α + Δ * β ^ 2 * α) + Δ ^ 2 * (β * (β * α)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hnΔ]
          exact mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add hDA hDB)) hΔ
        · rw [norm_mul, norm_pow, hnΔ]
          exact mul_le_mul_of_nonneg_left hS3 (by positivity)
    _ = 3 * Δ ^ 2 * β ^ 2 * α := by ring

end RBM.Path

end
