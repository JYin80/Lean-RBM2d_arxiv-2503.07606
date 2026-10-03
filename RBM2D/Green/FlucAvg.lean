/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucVanish
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Induction.Defs
import RBM2D.Induction.Split
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Topology.Instances.Matrix

/-!
# Fluctuation averaging, averaging layer: measurability, envelopes, bounds, counting

The paper (arXiv:2503.07606) does not state these lemmas: the estimates on `G_t` "follow that of
Lemma 4.2 in [YY_25], which is dimension-independent" (Section "Estimates for entries of
`G`"), and the fluctuation averaging behind (`GavLGEX`) is proved internally.  The
declarations here are the measurability facts (including the measurability of the matrix
inverse), the deterministic envelopes, the pointwise
parameters `FlucBound`, the bounds on `flucAvg`, the conditional diagonal `condExpDiag` and the
d = 2 counting facts.

Everything lives at one slice `n` of a size sequence `d : Sizes`, on the fine index
`Idx (d.L n) (d.W n) = Z2 (W L)`, with `E_k = condRow d n k` and the variance `svar`.
`flucAvg`, `flucDiag`, `greenDiagCentered`, ... are those of
`RBM2D/Green/FlucVanish.lean`; nothing is redefined.

* `measurable_Hflow_sub`, `measurable_green_apply`, `measurable_greenMinorMat_apply`,
  `measurable_condRow`, `measurable_greenDiagCentered`, `measurable_greenMinorDiagCentered`,
  `measurable_flucDiag` : measurability of `G_{ij}`, `G^{(κ)}_{ab}`, `E_k[X]` and `Z_k`.
* `norm_green_apply_le_etaT`, `greenMinorMat_eq_green_submatrix`,
  `norm_greenMinorMat_apply_le_etaT`, `norm_greenDiagCentered_le_env`,
  `norm_greenMinorDiagCentered_le_env`, `rowIntegrable_greenDiagCentered`,
  `rowIntegrable_greenMinorDiagCentered` : the deterministic envelope `|G_{ij}| ≤ η⁻¹` for every
  `ω`, with `η = Im z_t = (1 - t) Im m(E)` written as `(spectralZ E t).im`.
* `FlucBound`, `flucBound_env` : the pointwise parameters `B = 2 (η⁻¹ + 1)`, `ε = 4 η⁻¹`.
* `measurable_flucAvg`, `norm_flucAvg_le`, `integrable_norm_flucAvg_pow` : the bounds on
  `flucAvg`.
* `condExpDiag` : `E_k[G_{kk} - m]`.
* `card_blockAvg_support` (`W²`), `card_Sblk_support` (`5 W²`), `flucAvg_card_Idx_eq_size`
  (`#Idx = size`), `flucAvg_card_Z2_le_size` (`#Z2 L ≤ size`), `tendsto_W`, `eventually_le_W` :
  the d = 2 counting facts.  The first two are the cardinalities
  `flucVanish_card_blockSupport`, `flucVanish_card_svarSupport_eq`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM.Gauss

/-! ### Measurability of the matrix inverse (private; `measurable_matrix_inv_apply`) -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem flucAvg_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
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

end MatrixMeasurable

/-! ### Measurability

The last obstruction to the hypotheses of the moment bound: the entries of the Green function,
the minor Green function and the conditional expectation `E_k` are measurable. -/

/-- `ω ↦ H_u(ω) - z` is measurable as a matrix-valued map. -/
theorem measurable_Hflow_sub (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) :
    Measurable fun ω : Sizes.SeqΩ d =>
      Sizes.seqHflow d n u ω
        - z • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  have h : (fun ω : Sizes.SeqΩ d => (Sizes.seqHflow d n u ω
        - z • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) a b)
      = fun ω => Sizes.seqHflow d n u ω a b
        - z * (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) a b := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry d n u a b).sub measurable_const

/-- **`ω ↦ G_{ij}(ω)` is measurable.** -/
theorem measurable_green_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (i j : Idx (d.L n) (d.W n)) :
    Measurable fun ω => green (Sizes.seqHflow d n u ω) z i j :=
  flucAvg_measurable_matrix_inv_apply (measurable_Hflow_sub d n u z) i j

/-- The same for the minor resolvent `G^{(κ)}`. -/
theorem measurable_greenMinorMat_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (κ : Idx (d.L n) (d.W n)) (a b : {a : Idx (d.L n) (d.W n) // a ≠ κ}) :
    Measurable fun ω => greenMinorMat d n u z κ ω a b := by
  refine flucAvg_measurable_matrix_inv_apply (M := fun ω : Sizes.SeqΩ d =>
    (Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ κ}
        {a : Idx (d.L n) (d.W n) // a ≠ κ} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Sizes.SeqΩ d =>
      ((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))
        - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ κ}
          {a : Idx (d.L n) (d.W n) // a ≠ κ} ℂ)) p q)
      = fun ω => Sizes.seqHflow d n u ω p.1 q.1
          - z * (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ κ}
            {a : Idx (d.L n) (d.W n) // a ≠ κ} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry d n u p.1 q.1).sub measurable_const

/-- **`ω ↦ E_k[X](ω)` is measurable** for measurable `X`: `E_k` is an integral over the second
factor of `Ω × Ω`, and `rowSplit` is jointly measurable (`measurable_rowSplit`), so
`MeasureTheory.StronglyMeasurable.integral_prod_right'` applies. -/
theorem measurable_condRow (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    {X : Sizes.SeqΩ d → ℂ} (hX : Measurable X) :
    Measurable (condRow d n k X) := by
  have hjoint : StronglyMeasurable fun p : Sizes.SeqΩ d × Sizes.SeqΩ d =>
      X (rowSplit d n k p.1 p.2) :=
    (hX.comp (measurable_rowSplit d n k)).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

theorem measurable_greenDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) :
    Measurable (greenDiagCentered d n u z m k) :=
  (measurable_green_apply d n u z k k).sub measurable_const

theorem measurable_greenMinorDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx (d.L n) (d.W n)) (k : {a : Idx (d.L n) (d.W n) // a ≠ κ}) :
    Measurable (greenMinorDiagCentered d n u z m κ k) :=
  (measurable_greenMinorMat_apply d n u z κ k k).sub measurable_const

/-- Measurability of `Z_k = (1 - E_k)(G_{kk} - m)`. -/
theorem measurable_flucDiag (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) :
    Measurable (flucDiag d n u z m k) :=
  (measurable_greenDiagCentered d n u z m k).sub
    (measurable_condRow d n k (measurable_greenDiagCentered d n u z m k))

/-! ### The deterministic envelope, entrywise

`Im z_t = η_t = (1 - t) Im m(E) > 0` for `|E| < 2`, `t < 1`, so `‖G_t‖_op ≤ η_t⁻¹`
(`RBM.Gauss.norm_green_le`) for *every* `ω`, and the same for every minor `G^{(κ)}_t`, a
resolvent of the Hermitian matrix `H^{(κ)}`.  The bound is written with `η_t = (spectralZ E t).im`
(the form of `eta_lower_of_rangeCond`). -/

section Envelope

open scoped Matrix.Norms.L2Operator

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- For `|E| < 2` and `t < 1`, `η_t = Im z_t > 0`. -/
private theorem flucAvg_spectralZ_im_pos (hE : |E| < 2) (ht : t < 1) :
    0 < (spectralZ E t).im := by
  rw [spectralZ_im]
  exact mul_pos (by linarith) (spectralM_im_pos hE)

/-- The Green function of a Hermitian matrix at `z_t` has operator norm at most `η_t⁻¹`. -/
private theorem flucAvg_norm_green_spectralZ_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hE : |E| < 2) (ht : t < 1) :
    ‖green H (spectralZ E t)‖ ≤ ((spectralZ E t).im)⁻¹ := by
  have hη := flucAvg_spectralZ_im_pos hE ht
  exact norm_green_le hH hη (le_of_eq (abs_of_pos hη).symm)

/-- `|G_{ij}| ≤ η_t⁻¹` for every `ω`. -/
theorem norm_green_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (i j : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    ‖green (Sizes.seqHflow d n u ω) (spectralZ E t) i j‖ ≤ ((spectralZ E t).im)⁻¹ :=
  le_trans (RBM.Ind.norm_apply_le_l2_opNorm _ i j)
    (flucAvg_norm_green_spectralZ_le (Sizes.seqHflow_isHermitian d n u ω) hE ht)

/-- `G^{(κ)}` is the resolvent of the minor `H^{(κ)}`, which is Hermitian. -/
theorem greenMinorMat_eq_green_submatrix (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (κ : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    greenMinorMat d n u z κ ω
      = green ((Sizes.seqHflow d n u ω).submatrix
          (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))
          (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ κ} → Idx (d.L n) (d.W n))) z := rfl

/-- `|G^{(κ)}_{ab}| ≤ η_t⁻¹` for every `ω`: the minor of a Hermitian matrix is Hermitian, so the
same envelope applies. -/
theorem norm_greenMinorMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx (d.L n) (d.W n)} (a b : {a : Idx (d.L n) (d.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ d) :
    ‖greenMinorMat d n u (spectralZ E t) κ ω a b‖ ≤ ((spectralZ E t).im)⁻¹ := by
  rw [greenMinorMat_eq_green_submatrix]
  exact le_trans (RBM.Ind.norm_apply_le_l2_opNorm _ a b)
    (flucAvg_norm_green_spectralZ_le ((Sizes.seqHflow_isHermitian d n u ω).submatrix _) hE ht)

/-- `|G_{kk} - m| ≤ η_t⁻¹ + 1` for every `ω` (`‖m^{(E)}‖ = 1`). -/
theorem norm_greenDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    ‖greenDiagCentered d n u (spectralZ E t) (spectralM E) k ω‖
      ≤ ((spectralZ E t).im)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _) (add_le_add (norm_green_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_spectralM hE.le)

theorem norm_greenMinorDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx (d.L n) (d.W n)} (k : {a : Idx (d.L n) (d.W n) // a ≠ κ}) (ω : Sizes.SeqΩ d) :
    ‖greenMinorDiagCentered d n u (spectralZ E t) (spectralM E) κ k ω‖
      ≤ ((spectralZ E t).im)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _)
    (add_le_add (norm_greenMinorMat_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_spectralM hE.le)

/-- `RowIntegrable` for `G_{kk} - m`: the hypothesis `hrow` of the moment bound. -/
theorem rowIntegrable_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx (d.L n) (d.W n)) :
    RowIntegrable d n k (greenDiagCentered d n u (spectralZ E t) (spectralM E) k) :=
  rowIntegrable_of_measurable_of_bound
    (measurable_greenDiagCentered d n u (spectralZ E t) (spectralM E) k)
    (norm_greenDiagCentered_le_env hE ht u k)

theorem rowIntegrable_greenMinorDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx (d.L n) (d.W n)} (k : {a : Idx (d.L n) (d.W n) // a ≠ κ})
    (j : Idx (d.L n) (d.W n)) :
    RowIntegrable d n j (greenMinorDiagCentered d n u (spectralZ E t) (spectralM E) κ k) :=
  rowIntegrable_of_measurable_of_bound
    (measurable_greenMinorDiagCentered d n u (spectralZ E t) (spectralM E) κ k)
    (norm_greenMinorDiagCentered_le_env hE ht u k)

end Envelope

/-! ### The pointwise parameters `B` and `ε`

The moment bound is stated for *pointwise-uniform* parameters `B` (a bound on every factor `Z_k`
and every replaced factor `Z^{(κ)}_k`) and `ε` (a bound on the replacement error).
`FlucBound` packages them; the unconditional instance is the deterministic envelope one,
`flucBound_env`. -/

/-- The three uniform bounds the moment bound consumes, packaged. -/
structure FlucBound (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (B ε : ℝ) : Prop where
  /-- `B` is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `ε` is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Every factor `Z_k` is bounded by `B`, for every `ω`. -/
  flucDiag_le : ∀ (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d),
    ‖flucDiag d n u z m k ω‖ ≤ B
  /-- Every replaced factor `Z^{(κ)}_k` is bounded by `B`, for every `ω`. -/
  flucDiagMinor_le : ∀ (κ : Idx (d.L n) (d.W n)) (k : {a : Idx (d.L n) (d.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ d), ‖flucDiagMinor d n u z m κ k ω‖ ≤ B
  /-- The replacement `Z_k ↦ Z^{(κ)}_k` costs at most `ε`, for every `ω`. -/
  repl_le : ∀ (κ : Idx (d.L n) (d.W n)) (k : {a : Idx (d.L n) (d.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ d), ‖flucDiag d n u z m k.1 ω - flucDiagMinor d n u z m κ k ω‖ ≤ ε

section EnvParams

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- **The pointwise parameters exist, unconditionally.**  The deterministic envelope
`‖G_t‖ ≤ η_t⁻¹` holds for *every* `ω`, with no exceptional set, and it survives the `(1 - E_k)`
(factor `2`, `norm_sub_condRow_le`) and the minor replacement (`G` and `G^{(κ)}` are resolvents
of two Hermitian matrices, so their difference is at most `2 η_t⁻¹`).

The parameters are `B = 2(η_t⁻¹ + 1)` and `ε = 4 η_t⁻¹`: finite and explicit, of size `η_t⁻¹`. -/
theorem flucBound_env (hE : |E| < 2) (ht : t < 1) (d : Sizes) (n : ℕ) (u : ℝ) :
    FlucBound d n u (spectralZ E t) (spectralM E)
      (2 * (((spectralZ E t).im)⁻¹ + 1)) (4 * ((spectralZ E t).im)⁻¹) := by
  have hη : 0 < (spectralZ E t).im := flucAvg_spectralZ_im_pos hE ht
  refine ⟨by positivity, by positivity, fun k ω => ?_, fun κ k ω => ?_, fun κ k ω => ?_⟩
  · exact norm_flucDiag_le (norm_greenDiagCentered_le_env hE ht u k) ω
  · exact norm_flucDiagMinor_le (norm_greenMinorDiagCentered_le_env hE ht u k) ω
  · have he : ∀ ω' : Sizes.SeqΩ d,
        ‖green (Sizes.seqHflow d n u ω') (spectralZ E t) k.1 k.1
          - greenMinorMat d n u (spectralZ E t) κ ω' k k‖ ≤ 2 * ((spectralZ E t).im)⁻¹ := by
      intro ω'
      refine le_trans (norm_sub_le _ _) ?_
      have h1 := norm_green_apply_le_etaT hE ht u k.1 k.1 ω'
      have h2 := norm_greenMinorMat_apply_le_etaT hE ht u k k ω'
      linarith
    have := norm_flucDiag_sub_flucDiagMinor_le (u := u) (z := spectralZ E t)
      (m := spectralM E) (κ := κ) (k := k) (rowIntegrable_greenDiagCentered hE ht u k.1)
      (rowIntegrable_greenMinorDiagCentered hE ht u k k.1) he ω
    linarith

end EnvParams

/-! ### The moment bound in the assembled form -/

section Moment

/-- Measurability of the weighted fluctuation average `∑_k t_k Z_k`. -/
theorem measurable_flucAvg (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (T : Idx (d.L n) (d.W n) → ℝ) :
    Measurable (flucAvg d n u z m T) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_flucDiag d n u z m k)

variable {d : Sizes} {n : ℕ} {u : ℝ} {z m : ℂ} {T : Idx (d.L n) (d.W n) → ℝ}

/-- `‖∑_k t_k Z_k‖ ≤ (∑_k |t_k|) B`. -/
theorem norm_flucAvg_le {B : ℝ}
    (hB : ∀ (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d), ‖flucDiag d n u z m k ω‖ ≤ B)
    (ω : Sizes.SeqΩ d) : ‖flucAvg d n u z m T ω‖ ≤ (∑ k, |T k|) * B := by
  calc ‖flucAvg d n u z m T ω‖
      ≤ ∑ k, ‖(T k : ℂ) * flucDiag d n u z m k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, |T k| * B := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB k ω) (abs_nonneg _)
    _ = (∑ k, |T k|) * B := by rw [Finset.sum_mul]

/-- The `2p`-th power of `|∑_k t_k Z_k|` is integrable under a uniform bound on the `Z_k`. -/
theorem integrable_norm_flucAvg_pow {B : ℝ}
    (hB : ∀ (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d), ‖flucDiag d n u z m k ω‖ ≤ B)
    (p : ℕ) :
    Integrable (fun ω => |‖flucAvg d n u z m T ω‖| ^ (2 * p)) (Sizes.seqP d) := by
  have hrw : (fun ω => |‖flucAvg d n u z m T ω‖| ^ (2 * p))
      = fun ω => ‖flucAvg d n u z m T ω‖ ^ (2 * p) := by
    funext ω; rw [abs_norm]
  rw [hrw]
  refine Integrable.mono' (integrable_const (((∑ k, |T k|) * B) ^ (2 * p)))
    (((measurable_flucAvg d n u z m T).norm.pow_const (2 * p)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : (0 : ℝ) ≤ ∑ k, |T k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_flucAvg_le hB ω) _

end Moment

/-! ### The conditional diagonal -/

/-- `E_k(G_{kk} - m)`, the fine-index conditional diagonal (the quantity `x` of the entry-block
estimate). -/
noncomputable def condExpDiag (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) : Sizes.SeqΩ d → ℂ :=
  condRow d n k (greenDiagCentered d n u z m k)

/-! ### The d = 2 counting facts

`t_k = W⁻² 1(k ∈ 𝓘_a)` (`uniformWeight_blockAvg2`) and `t_k = S_{ik}` (`uniformWeight_svar`) are
uniform weights; here the index sets are counted at slice `n` (`W²` and `5 W²` sites), the
index set is counted (`#Idx = size n`), and `W → ∞` is derived from `SizeTendsto` and
`Bandwidth`. -/

section Families

/-- The block average of (4.12) is a uniform weight on a set of `W²` elements; this is
`flucVanish_card_blockSupport` at `(d.L n, d.W n)`. -/
theorem card_blockAvg_support (d : Sizes) (n : ℕ) (a : Z2 (d.L n)) :
    ((univ : Finset (Idx (d.L n) (d.W n))).filter fun k =>
      (blk (d.L n) (d.W n) k.1, blk (d.L n) (d.W n) k.2) = a).card = d.W n ^ 2 :=
  flucVanish_card_blockSupport (d.L n) (d.W n) a

/-- The variance-profile row `t_j = S_{ij}` of (4.12) is a uniform weight on a set of `5 W²`
elements; this is `flucVanish_card_svarSupport_eq` at
`(d.L n, d.W n)` with `3 ≤ d.L n`. -/
theorem card_Sblk_support (d : Sizes) (n : ℕ) (i : Idx (d.L n) (d.W n)) :
    ((univ : Finset (Idx (d.L n) (d.W n))).filter fun j =>
      (blk (d.L n) (d.W n) i.1, blk (d.L n) (d.W n) i.2)
        - (blk (d.L n) (d.W n) j.1, blk (d.L n) (d.W n) j.2) ∈ sbSupport (d.L n)).card
      = 5 * d.W n ^ 2 :=
  flucVanish_card_svarSupport_eq (d.L n) (d.W n) (d.three_le_L n) i

/-- **`#Idx = size`**, exactly: `#(ZMod (WL) × ZMod (WL)) = (WL)² = N`. -/
theorem flucAvg_card_Idx_eq_size (d : Sizes) (n : ℕ) :
    Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
  rw [Sizes.size, sq]
  simp [Idx, Z2, Fintype.card_prod, ZMod.card]

/-- `#Z2 L ≤ size`: `L² ≤ (WL)²` since `W ≥ 1`. -/
theorem flucAvg_card_Z2_le_size (d : Sizes) (n : ℕ) :
    Fintype.card (Z2 (d.L n)) ≤ d.size n := by
  have hW : 1 ≤ d.W n := d.W_pos n
  have hLW : d.L n ≤ d.W n * d.L n := Nat.le_mul_of_pos_left _ (d.W_pos n)
  rw [Sizes.size, sq]
  simp only [Z2, Fintype.card_prod, ZMod.card]
  exact Nat.mul_le_mul hLW hLW

/-- **`W(n) → ∞`**, from `N → ∞` (`SizeTendsto`) and `W ≥ N^𝔠` (`Bandwidth`, `Main_DEL_COND`)
with `𝔠 > 0`. -/
theorem tendsto_W (d : Sizes) {c : ℝ} (hc : 0 < c) (hsz : RBM.Ind.SizeTendsto d)
    (hbw : RBM.Path.Bandwidth d c) :
    Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop hbw ((tendsto_rpow_atTop hc).comp hsz)

/-- Every `p` is eventually below `W(n)`. -/
theorem eventually_le_W (d : Sizes) {c : ℝ} (hc : 0 < c) (hsz : RBM.Ind.SizeTendsto d)
    (hbw : RBM.Path.Bandwidth d c) (p : ℕ) : ∀ᶠ n : ℕ in atTop, p ≤ d.W n := by
  filter_upwards [(tendsto_W d hc hsz hbw).eventually_ge_atTop (p : ℝ)] with n hn
  exact_mod_cast hn

end Families

end RBM.Green
