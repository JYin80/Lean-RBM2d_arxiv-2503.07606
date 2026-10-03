/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.StoppedEndDefs
import RBM2D.Induction.BcalEDecay
import RBM2D.Induction.GridGoodN
import RBM2D.Induction.AzumaProxyN
import RBM2D.Induction.LoopC2N

/-!
# The non-alternating good-set inputs of the assembly

Namespace `RBM.Ind`, `variable (d : Sizes)`.  Paper: arXiv:2503.07606, Section 5: `lem:STOeq_NQ`
and its proof, `int_K-L+Q`, `alu9_STime`.  The proofs are done for `d = 2` (loops have `W⁻²` per
insertion `E_a`, labels in `Z_L²`, `N = (W L)²`) and parallel the one-dimensional formalization.

## Sections

1. **Compositions with the good set**: `driftTensor_norm_le_of_goodSet`,
   `driftTensor_far_of_goodSet` (against `driftTensor`).
2. **The good-set shift `u_j → u_{j+1}`**: `norm_gloop_zshiftN_le`, `norm_gloop_crudeN`,
   `norm_lk_envN`, and the shift of the pair form, `norm_eeN_shiftN_le` with `eeShiftErr` (`eeN`
   contains `𝓛` only).
3. **Constants and classes**: `kappaNonAlt`, `epsNonAlt`,
   `nonAltCls`, `dDriftNonAlt`, the identities `NonAltGood_rhoR_mul_scaleM_inv`,
   `kappaNonAlt_mul_scale_pow_eq`, `kappaNonAlt_succ_mul_scale_pow_le`, and the fields `hker`,
   `hA0cls`, `hdrift`, `hDcls` (and the non-negativity fields) of `GridAssemblyHypN` on the event
   `{H_j ∈ GoodSetN … u_j, j < τ}`: `nonAlt_hker`, `goodSetN_A0cls`, `nonAlt_hA0cls`,
   `nonAlt_hdrift`, `goodSetN_driftCls`, `nonAlt_hDcls`, `nonAlt_hκ0`, `nonAlt_hε0`,
   `nonAlt_hdDrift0`.
4. **The quadratic-variation constant**: `qvBdNonAlt`, `qvBdNonAlt_pos`, the shifted majorant
   `qvFormN_le_of_goodSet_shiftN`, `cQVNonAlt`, `hQ_nonAlt`, `subGaussStop_nonAlt` (the
   `SubGaussStopN` input of `AssembledN` from `azumaSubGN`), `cQVNonAlt_sum_pos` (the field
   `hc_pos`, needs `Δ > 0`).

All statements are for a general `k ≥ 2` (one statement, as `NonAltGridEnd`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Compositions with the good set -/

section Compositions

/-- **The drift sup bound on the good set** (`hdrift`; clauses (D1), (D2), (D3) of `GoodSetN`). -/
theorem driftTensor_norm_le_of_goodSet {L W : ℕ} [NeZero L] [NeZero W] {E u Γ Λ Φ τ' D' : ℝ}
    {k : ℕ} {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D')
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    ‖driftTensor L W E u M σ a‖ ≤
      (((k - 2 : ℕ) : ℝ) * (Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ))) +
        Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) + Γ * (Γ * Φ)) *
          ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) + 2 * (W : ℝ) ^ (-D') := by
  obtain ⟨-, -, -, -, -, -, hD1, hD2, hD3, -, -, -⟩ := hM
  set X : ℝ := (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ with hX
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ ≤
      ((k - 2 : ℕ) : ℝ) * (Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * X) := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ l ∈ Finset.Icc 3 k, ‖ksimLK L W E u M l (loopOf σ a)‖ ≤
        Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * X := fun l hl =>
      hD1 l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2 σ a
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    have : (k + 1 - 3 : ℕ) = k - 2 := by omega
    rw [this]
  have h2 := hD2 σ a
  have h3 := hD3 σ a
  unfold driftTensor
  refine (norm_add₃_le).trans ?_
  nlinarith [h1, h2, h3]

/-- **The drift far decay on the good set** (`hDcls`; clause (V) of `GoodSetN`). -/
theorem driftTensor_far_of_goodSet {L W : ℕ} [NeZero L] [NeZero W] {E u Γ Λ Φ τ' D' : ℝ}
    {k : ℕ} {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D')
    (σ : Fin k → Bool) (a : Fin k → Z2 L)
    (hfar : ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ)) :
    ‖driftTensor L W E u M σ a‖ ≤ (W : ℝ) ^ (-D') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hVa, -⟩ := hM
  have h := hVa σ a hfar
  unfold driftTensor
  exact (norm_add₃_le).trans h

end Compositions

/-! ## 2. The good-set shift `u_j → u_{j+1}` -/

section Shift

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `‖G(z') - G(z)‖ ≤ η⁻¹ ‖z' - z‖ η⁻¹` for one signed Green factor (resolvent identity). -/
private theorem NonAltGood_norm_Gsig_sub_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    (s : Bool) : ‖Gsig H z' s - Gsig H z s‖ ≤ η⁻¹ * ‖z' - z‖ * η⁻¹ := by
  have key : ∀ {w w' : ℂ}, η ≤ |w.im| → η ≤ |w'.im| →
      ‖green H w' - green H w‖ ≤ η⁻¹ * ‖w' - w‖ * η⁻¹ := by
    intro w w' hw hw'
    have hwn : w.im ≠ 0 := abs_pos.mp (hη.trans_le hw)
    have hwn' : w'.im ≠ 0 := abs_pos.mp (hη.trans_le hw')
    have hu := Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hwn
    have hu' := Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hwn'
    rw [green_sub_green hu' hu, norm_smul]
    have hG := Gauss.norm_green_le hH hη hw
    have hG' := Gauss.norm_green_le hH hη hw'
    calc ‖w' - w‖ * ‖green H w' * green H w‖ ≤ ‖w' - w‖ * (η⁻¹ * η⁻¹) := by
          refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (norm_nonneg _)
          exact mul_le_mul hG' hG (norm_nonneg _) (by positivity)
      _ = η⁻¹ * ‖w' - w‖ * η⁻¹ := by ring
  cases s
  · simp only [Gsig_false]
    have h := key (w := (starRingEnd ℂ) z) (w' := (starRingEnd ℂ) z') (by simpa using hz)
      (by simpa using hz')
    rwa [← map_sub, Complex.norm_conj] at h
  · simpa only [Gsig_true] using key hz hz'

/-- `‖C_{σ,a}(z') - C_{σ,a}(z)‖ ≤ |σ| η^{-(|σ|+1)} (W⁻²)^{|a|} |z' - z|` for a `G`-chain: the
telescoping `G'E C' - G E C = (G' - G) E C' + G E (C' - C)`. -/
private theorem NonAltGood_norm_gchain_sub_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    {σ : List Bool} {a : List (Z2 L)} (h : σ.length = a.length + 1) :
    ‖gchain L W H z' σ a - gchain L W H z σ a‖ ≤
      (σ.length : ℝ) * (η⁻¹ ^ (σ.length + 1) * ((W : ℝ)⁻¹ ^ 2) ^ a.length * ‖z' - z‖) := by
  have hz0 : z.im ≠ 0 := abs_pos.mp (hη.trans_le hz)
  have hz0' : z'.im ≠ 0 := abs_pos.mp (hη.trans_le hz')
  have hη0 : 0 ≤ η⁻¹ := (inv_pos.2 hη).le
  have hGle : ∀ (w : ℂ) (s : Bool), η ≤ |w.im| → ‖Gsig H w s‖ ≤ η⁻¹ := by
    intro w s hw
    refine (norm_Gsig_le hH (abs_pos.mp (hη.trans_le hw)) s).trans ?_
    exact inv_anti₀ hη hw
  induction σ generalizing a with
  | nil => simp at h
  | cons s σ ih =>
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      have := NonAltGood_norm_Gsig_sub_le hH hη hz hz' s
      simp only [gchain, List.length_cons, List.length_nil, Nat.cast_one, zero_add,
        pow_zero, mul_one, one_mul]
      calc ‖Gsig H z' s - Gsig H z s‖ ≤ η⁻¹ * ‖z' - z‖ * η⁻¹ := this
        _ = η⁻¹ ^ 2 * ‖z' - z‖ := by ring
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      have hC' : ‖gchain L W H z' σ a‖ ≤ η⁻¹ ^ σ.length * ((W : ℝ)⁻¹ ^ 2) ^ a.length := by
        refine (norm_gchain_le hH hz0' h').trans ?_
        gcongr
      have hrec := ih h'
      have hE := norm_Eblk_le (W := W) b
      have hGd := NonAltGood_norm_Gsig_sub_le hH hη hz hz' s
      have hGz := hGle z s hz
      have hsplit : gchain L W H z' (s :: σ) (b :: a) - gchain L W H z (s :: σ) (b :: a) =
          (Gsig H z' s - Gsig H z s) * Eblk L W b * gchain L W H z' σ a +
            Gsig H z s * Eblk L W b * (gchain L W H z' σ a - gchain L W H z σ a) := by
        rw [gchain_cons, gchain_cons]; noncomm_ring
      rw [hsplit, List.length_cons, List.length_cons]
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖(Gsig H z' s - Gsig H z s) * Eblk L W b * gchain L W H z' σ a‖ ≤
          (η⁻¹ * ‖z' - z‖ * η⁻¹) * ((W : ℝ)⁻¹ ^ 2) *
            (η⁻¹ ^ σ.length * ((W : ℝ)⁻¹ ^ 2) ^ a.length) := by
        refine (norm_mul_le _ _).trans ?_
        refine mul_le_mul ((norm_mul_le _ _).trans ?_) hC' (norm_nonneg _) (by positivity)
        exact mul_le_mul hGd hE (norm_nonneg _) (by positivity)
      have e2 : ‖Gsig H z s * Eblk L W b * (gchain L W H z' σ a - gchain L W H z σ a)‖ ≤
          η⁻¹ * ((W : ℝ)⁻¹ ^ 2) * ((σ.length : ℝ) *
            (η⁻¹ ^ (σ.length + 1) * ((W : ℝ)⁻¹ ^ 2) ^ a.length * ‖z' - z‖)) := by
        refine (norm_mul_le _ _).trans ?_
        refine mul_le_mul ((norm_mul_le _ _).trans ?_) hrec (norm_nonneg _) (by positivity)
        exact mul_le_mul hGz hE (norm_nonneg _) hη0
      refine (add_le_add e1 e2).trans (le_of_eq ?_)
      push_cast
      ring

/-- **Spectral-parameter shift of one loop** at a fixed Hermitian matrix (`d = 2`: the loop has
`ℓ` edges and `ℓ - 1` insertions `E_a` of weight `W⁻²`, so the bound carries the factor
`(W⁻²)^{ℓ-1}` and no hypothesis `η ≤ 1` is needed): `|𝓛(z') - 𝓛(z)| ≤ ℓ η^{-(ℓ+1)} (W⁻²)^{ℓ-1} |z' - z|` for
`|Im z|, |Im z'| ≥ η`. -/
theorem norm_gloop_zshiftN_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    (I : LoopIdx (Z2 L)) (hwf : I.σ.length = I.a.length) (hlen : 1 ≤ I.a.length) :
    ‖gloop L W H z' I - gloop L W H z I‖ ≤
      (I.a.length : ℝ) * (η⁻¹ ^ (I.a.length + 1) * ((W : ℝ)⁻¹ ^ 2) ^ (I.a.length - 1) *
        ‖z' - z‖) := by
  obtain ⟨σ, a⟩ := I
  simp only at hwf hlen ⊢
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hlen
  have h : σ.length = a'.length + 1 := by simpa using hwf
  have hd := NonAltGood_norm_gchain_sub_le hH hη hz hz' h
  have e : gloop L W H z' ⟨σ, a' ++ [b]⟩ - gloop L W H z ⟨σ, a' ++ [b]⟩ =
      Matrix.trace ((gchain L W H z' σ a' - gchain L W H z σ a') * Eblk L W b) := by
    rw [← trace_gchain_mul_Eblk h b, ← trace_gchain_mul_Eblk h b, sub_mul, Matrix.trace_sub]
  rw [e]
  refine (split_norm_trace_mul_Eblk_le _ b).trans (hd.trans (le_of_eq ?_))
  simp [h]

/-- The shift error of one loop of length `ℓ`: `ℓ η^{-(ℓ+1)} (W⁻²)^{ℓ-1} Δ`
(`Δ = u' - u`, `η = η_{u'}`), the right-hand side of `norm_gloop_zshiftN_le` at `|z' - z| = Δ`. -/
def loopShiftErr (W : ℕ) (η : ℝ) (ℓ : ℕ) (Δ : ℝ) : ℝ :=
  (ℓ : ℝ) * (η⁻¹ ^ (ℓ + 1) * ((W : ℝ)⁻¹ ^ 2) ^ (ℓ - 1) * Δ)

private theorem NonAltGood_loopShiftErr_nonneg {W : ℕ} {η Δ : ℝ} (hη : 0 ≤ η) (hΔ : 0 ≤ Δ) (ℓ : ℕ) :
    0 ≤ loopShiftErr W η ℓ Δ := by
  unfold loopShiftErr
  have : 0 ≤ η⁻¹ := inv_nonneg.2 hη
  positivity

/-- `|z_{u'} - z_u| = |u' - u|` (`|m| = 1`). -/
private theorem NonAltGood_norm_zt_sub {E : ℝ} (hE : |E| < 2) (u u' : ℝ) :
    ‖spectralZ E u' - spectralZ E u‖ = |u' - u| := by
  have h : spectralZ E u' - spectralZ E u = ((u - u' : ℝ) : ℂ) * spectralM E := by
    simp only [spectralZ]; push_cast; ring
  rw [h, norm_mul, norm_spectralM hE.le, Complex.norm_real, Real.norm_eq_abs, mul_one,
    abs_sub_comm]

/-- `|Im z_u| = η_u` for `u < 1`. -/
private theorem NonAltGood_abs_zt_im {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) :
    |(spectralZ E u).im| = etaT E u := by
  rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE))]
  rfl

/-- `η_u ≤ 1` for `0 ≤ u` (`Im m ≤ |m| = 1`). -/
private theorem NonAltGood_etaT_le_one {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) : etaT E u ≤ 1 := by
  unfold etaT
  have hm : (spectralM E).im ≤ 1 := by
    have := Complex.abs_im_le_norm (spectralM E)
    rw [norm_spectralM hE.le] at this
    exact (le_abs_self _).trans this
  have hm0 := (spectralM_im_pos hE).le
  nlinarith

/-- `η_{u'} ≤ η_u` for `u ≤ u'`. -/
private theorem NonAltGood_etaT_anti {E : ℝ} (hE : |E| < 2) {u u' : ℝ} (hu : u ≤ u') : etaT E u' ≤ etaT E u := by
  unfold etaT
  have := (spectralM_im_pos hE).le
  nlinarith

/-- **Crude loop bound**: `|𝓛_{u,σ,a}(M)| ≤ η_u^{-ℓ}` for
Hermitian `M`, `ℓ ≥ 1` (`d = 2` has the sharper `η^{-ℓ} (W⁻²)^{ℓ-1}`, `norm_gloop_le_of_le_abs_im`). -/
theorem norm_gloop_crudeN {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu1 : u < 1) (J : LoopIdx (Z2 L)) (hJ : J.WF)
    (hlen : 1 ≤ J.a.length) :
    ‖gloop L W (blockMat M) (spectralZ E u) J‖ ≤ (etaT E u)⁻¹ ^ J.a.length := by
  have hη := etaT_pos hE hu1
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have h := norm_gloop_le_of_le_abs_im hMb hη (le_of_eq (NonAltGood_abs_zt_im hE hu1).symm) J hJ hlen
  refine h.trans ?_
  have hW : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWi : ((W : ℝ)⁻¹ ^ 2) ^ (J.a.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW))
  have h0 : 0 ≤ (etaT E u)⁻¹ ^ J.a.length := by positivity
  calc (etaT E u)⁻¹ ^ J.a.length * ((W : ℝ)⁻¹ ^ 2) ^ (J.a.length - 1)
      ≤ (etaT E u)⁻¹ ^ J.a.length * 1 := mul_le_mul_of_nonneg_left hWi h0
    _ = _ := mul_one _

/-- **The crude `(𝓛-𝒦)` envelope** for all lengths `1 ≤ ℓ ≤ n` (`d = 2`: no length-0 loop, so no `L W` term): `|𝓛_J - 𝒦_J| ≤ η_u^{-n} + M_K`. -/
theorem norm_lk_envN {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {n : ℕ} {MK : ℝ}
    (hK : ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n →
      ‖KLoop.Kcal L W E u J‖ ≤ MK)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hln : J.length ≤ n) :
    ‖LKf L W E u M J‖ ≤ (etaT E u)⁻¹ ^ n + MK := by
  have hη := etaT_pos hE hu1
  have hη1 : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ hη).mpr (NonAltGood_etaT_le_one hE hu0)
  have hG := norm_gloop_crudeN hE hM hu1 J hJ h1
  have h2 : (etaT E u)⁻¹ ^ J.a.length ≤ (etaT E u)⁻¹ ^ n := pow_le_pow_right₀ hη1 hln
  have hKJ := hK J hJ h1 hln
  unfold LKf LLf
  calc ‖gloop L W (blockMat M) (spectralZ E u) J - KLoop.Kcal L W E u J‖
      ≤ ‖gloop L W (blockMat M) (spectralZ E u) J‖ + ‖KLoop.Kcal L W E u J‖ := norm_sub_le _ _
    _ ≤ _ := by
        have : J.a.length = J.length := rfl
        linarith

/-- The shift error of `eeN` at loop length `2k+2`: `W² · k · L² · (2k+2) η_{u'}^{-(2k+3)}
(W⁻²)^{2k+1} (u'-u)` (`W² Σ_{b,b'} |S^{(B)}_{bb'}| = W² L² = N`). -/
def eeShiftErr (L W : ℕ) (E : ℝ) (k : ℕ) (u u' : ℝ) : ℝ :=
  (W : ℝ) ^ 2 * ((k : ℝ) * ((L : ℝ) ^ 2 * loopShiftErr W (etaT E u') (2 * k + 2) (u' - u)))

/-- **The shift of the pair form**: `|(𝓔⊗𝓔)_{u'} - (𝓔⊗𝓔)_u| ≤ eeShiftErr` for Hermitian `M`
(`eeN` uses only `𝓛`, no `𝒦`, so only the loop shift of `norm_gloop_zshiftN_le` enters). -/
theorem norm_eeN_shiftN_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (a a' : Fin k → Z2 L) :
    ‖eeN L W E u' M σ a a' - eeN L W E u M σ a a'‖ ≤ eeShiftErr L W E k u u' := by
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hδ0 := NonAltGood_loopShiftErr_nonneg (W := W) (etaT_pos hE hu'1).le (by linarith : 0 ≤ u' - u) (2 * k + 2)
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hη := etaT_pos hE hu'1
  have hz : etaT E u' ≤ |(spectralZ E u).im| := by
    rw [NonAltGood_abs_zt_im hE (huu'.trans_lt hu'1)]; exact NonAltGood_etaT_anti hE huu'
  have hz' : etaT E u' ≤ |(spectralZ E u').im| := by rw [NonAltGood_abs_zt_im hE hu'1]
  unfold eeN
  rw [← mul_sub, norm_mul, hW2]
  have key : ‖∑ k' ∈ Finset.Icc 1 k, ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        LLf L W E u' M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') -
      ∑ k' ∈ Finset.Icc 1 k, ∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖ ≤
      (k : ℝ) * ((L : ℝ) ^ 2 * loopShiftErr W (etaT E u') (2 * k + 2) (u' - u)) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k' ∈ Finset.Icc 1 k, ∑ b : Z2 L, ∑ b' : Z2 L, ‖SB L b b'‖ *
          loopShiftErr W (etaT E u') (2 * k + 2) (u' - u) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          simp only [Finset.mem_Icc] at hk'
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [← mul_sub, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hwf := eeLoop_WF (L := L) (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk'.1
            (by simpa using hk'.2) (by simp) (by simp) b b'
          have hlenE : (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a.length =
              2 * k + 2 := by
            have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k')
              (by simp; omega) (by simp) b b'
            simpa [LoopIdx.length] using this
          have h1 := norm_gloop_zshiftN_le hMb hη hz hz'
            (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') hwf
            (by rw [hlenE]; omega)
          rw [hlenE, NonAltGood_norm_zt_sub hE, abs_of_nonneg (by linarith)] at h1
          unfold LLf
          exact h1
      _ = (k : ℝ) * ((L : ℝ) ^ 2 * loopShiftErr W (etaT E u') (2 * k + 2) (u' - u)) := by
          simp only [← Finset.sum_mul, BcalEDecay_sum_sum_norm_SB L hL, Finset.sum_const,
            Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  unfold eeShiftErr
  exact mul_le_mul_of_nonneg_left key (by positivity)

end Shift

/-! ## 3. Constants and classes -/

section Classes

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem NonAltGood_cCase1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cCase1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cCase1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

private theorem NonAltGood_cPair1_nonneg (k : ℕ) (κ : ℝ) : 0 ≤ cPair1 k κ := by
  have hg : 0 ≤ KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : 0 ≤ cProp5 := by unfold cProp5; positivity
  have hcs : 0 ≤ cShortRow κ := by
    unfold cShortRow
    exact mul_nonneg (div_nonneg (by linarith) hg) (sq_nonneg _)
  unfold cPair1
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

/-- `ρ_{s,t} M_s^{-1} = M_t^{-1}` (`η_u/(1-u) = Im m` cancels). -/
theorem NonAltGood_rhoR_mul_scaleM_inv {E s t : ℝ} (hE : |E| < 2) (hs : s < 1) (ht : t < 1) :
    rhoR L s t * (scaleM L W E s)⁻¹ = (scaleM L W E t)⁻¹ := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hm := spectralM_im_pos hE
  have hls := (ellT_pos_le hLp hs).1
  have hlt := (ellT_pos_le hLp ht).1
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold rhoR scaleM etaT
  field_simp

private theorem NonAltGood_rhoR_nonneg {s t : ℝ} (hs : s < 1) (ht : t < 1) : 0 ≤ rhoR L s t := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hls := (ellT_pos_le hLp hs).1
  have hlt := (ellT_pos_le hLp ht).1
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold rhoR
  positivity

/-- **The Case 1 kernel class** (the decay window is the class):
`Cls i δ X := DecayWin (ℓ_{u_i} K_w) δ X`, `K_w = W^{τ'}` in the
consumers.  It is the hypothesis of `hker_of_case1`, i.e. of `ugenCase1Explicit`
(D1b), and the class `Cls` of `GridAssemblyHypN` for non-alternating `σ`. -/
def nonAltCls (L : ℕ) [NeZero L] {k : ℕ} (Kw : ℝ) (u : ℕ → ℝ) :
    ℕ → ℝ → ((Fin k → Z2 L) → ℂ) → Prop :=
  fun i δ X => DecayWin L (ellT L (u i) * Kw) δ X

/-- **The kernel weight `κ_{i,m}` of Case 1** (`d = 2`): `c_1(k,κ)
(1 + log L)^k K_w^{2(k-1)} ρ_{u_i,u_m}^k` with `cCase1`. -/
def kappaNonAlt (L k : ℕ) (κ Kw : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) * rhoR L (u i) (u m) ^ k

/-- **The additive decay-error weight** `ε_{i,m} = ((1-u_i)/(1-u_m))^k`. -/
def epsNonAlt (k : ℕ) (u : ℕ → ℝ) (i m : ℕ) : ℝ := ((1 - u i) / (1 - u m)) ^ k

/-- **The drift level** at the grid time `u` (the right-hand side
of `driftTensor_norm_le_of_goodSet`): `((k-2)(k-1) + (k-1) + 1) Γ² Φ M_u^{-k} η_u^{-1} +
2 W^{-D'}`, with `(k-2)(k-1) + (k-1) + 1 = (k-1)² + 1`. -/
def dDriftNonAlt (L W : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ D' : ℝ) : ℝ :=
  (((k - 2 : ℕ) : ℝ) * (Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ))) +
      Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) + Γ * (Γ * Φ)) *
        ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) + 2 * (W : ℝ) ^ (-D')

/-- The closed form of the drift constant: `((k-1)² + 1) Γ² Φ M^{-k} η^{-1} + 2 W^{-D'}`. -/
theorem dDriftNonAlt_eq (L W : ℕ) (E u : ℝ) {k : ℕ} (hk : 2 ≤ k) (Γ Φ D' : ℝ) :
    dDriftNonAlt L W E u k Γ Φ D' =
      (((k : ℝ) - 1) ^ 2 + 1) * (Γ ^ 2 * Φ) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) +
        2 * (W : ℝ) ^ (-D') := by
  unfold dDriftNonAlt
  have h1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h2 : (((k - 2 : ℕ) : ℝ)) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub hk]; simp
  rw [h1, h2]
  ring

private theorem NonAltGood_kappaNonAlt_nonneg (k : ℕ) (κ Kw : ℝ) (u : ℕ → ℝ) {i m : ℕ} (hKw : 0 ≤ Kw)
    (hi : u i < 1) (hm : u m < 1) : 0 ≤ kappaNonAlt L k κ Kw u i m := by
  unfold kappaNonAlt
  have hlog : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  have := NonAltGood_cCase1_nonneg k κ
  have := NonAltGood_rhoR_nonneg (L := L) hi hm
  positivity

private theorem NonAltGood_epsNonAlt_nonneg (k : ℕ) (u : ℕ → ℝ) {i m : ℕ} (hi : u i < 1) (hm : u m < 1) :
    0 ≤ epsNonAlt k u i m := by
  unfold epsNonAlt
  have h1 : 0 < 1 - u i := by linarith
  have h2 : 0 < 1 - u m := by linarith
  positivity

private theorem NonAltGood_dDriftNonAlt_nonneg (L W : ℕ) [NeZero L] [NeZero W] {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (k : ℕ) {Γ Φ : ℝ} (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (D' : ℝ) :
    0 ≤ dDriftNonAlt L W E u k Γ Φ D' := by
  unfold dDriftNonAlt
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hu
  have hη := etaT_pos hE hu
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWp
  have : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  positivity

/-- **The sharp kernel on the initial datum**: `κ_{i,m} M_{u_i}^{-k} = c_1 (1 + log L)^k K_w^{2(k-1)} M_{u_m}^{-k}` exactly, with no
`η_s/η_t` prefactor (`ρ_{i,m} M_{u_i}^{-1} = M_{u_m}^{-1}`). -/
theorem kappaNonAlt_mul_scale_pow_eq {E : ℝ} (hE : |E| < 2) (k : ℕ) (κ Kw : ℝ) (u : ℕ → ℝ)
    {i m : ℕ} (hi : u i < 1) (hm : u m < 1) :
    kappaNonAlt L k κ Kw u i m * (scaleM L W E (u i) ^ k)⁻¹ =
      cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) * (scaleM L W E (u m) ^ k)⁻¹ := by
  unfold kappaNonAlt
  have h := NonAltGood_rhoR_mul_scaleM_inv (L := L) (W := W) hE hi hm
  have h2 : rhoR L (u i) (u m) ^ k * (scaleM L W E (u i) ^ k)⁻¹ = (scaleM L W E (u m) ^ k)⁻¹ := by
    rw [← inv_pow, ← mul_pow, h, inv_pow]
  calc cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) * rhoR L (u i) (u m) ^ k *
        (scaleM L W E (u i) ^ k)⁻¹
      = cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) *
          (rhoR L (u i) (u m) ^ k * (scaleM L W E (u i) ^ k)⁻¹) := by ring
    _ = _ := by rw [h2]

/-- **The sharp kernel on the drift**:
for grid times `0 ≤ u_j ≤ u_{j+1} ≤ u_m < 1`, `κ_{j+1,m} M_{u_j}^{-k} ≤ c_1 (1 + log L)^k
K_w^{2(k-1)} M_{u_m}^{-k}`: the kernel weight from `u_{j+1}` against the drift's own scale at
`u_j` carries no `η_s/η_t` factor (`M_{u_{j+1}} ≤ M_{u_j}`). -/
theorem kappaNonAlt_succ_mul_scale_pow_le {E : ℝ} (hE : |E| < 2) (k : ℕ) (κ Kw : ℝ)
    (hKw : 0 ≤ Kw) (u : ℕ → ℝ) (j m : ℕ) (hjj : u j ≤ u (j + 1)) (hj1m : u (j + 1) ≤ u m)
    (hm : u m < 1) :
    kappaNonAlt L k κ Kw u (j + 1) m * (scaleM L W E (u j) ^ k)⁻¹ ≤
      cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) * (scaleM L W E (u m) ^ k)⁻¹ := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hj1 : u (j + 1) < 1 := hj1m.trans_lt hm
  have hA1 : 0 < scaleM L W E (u (j + 1)) := scaleM_pos hLp hWp hE hj1
  have hle : scaleM L W E (u (j + 1)) ≤ scaleM L W E (u j) :=
    (scaleM_anti_ratio hLp hE hjj hj1).1
  have hinv : (scaleM L W E (u j) ^ k)⁻¹ ≤ (scaleM L W E (u (j + 1)) ^ k)⁻¹ :=
    inv_anti₀ (pow_pos hA1 _) (pow_le_pow_left₀ hA1.le hle k)
  have hκ0 := NonAltGood_kappaNonAlt_nonneg (L := L) k κ Kw u hKw hj1 hm
  calc kappaNonAlt L k κ Kw u (j + 1) m * (scaleM L W E (u j) ^ k)⁻¹
      ≤ kappaNonAlt L k κ Kw u (j + 1) m * (scaleM L W E (u (j + 1)) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hκ0
    _ = _ := kappaNonAlt_mul_scale_pow_eq hE k κ Kw u hj1 hm

/-- **The field `hker` for non-alternating `σ`**: `ugenCase1Explicit` (via `hker_of_case1`) in the shape of the field of `GridAssemblyHypN`,
`Cls = nonAltCls`, `κ = kappaNonAlt`, `εK = epsNonAlt`. -/
theorem nonAlt_hker {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hL : 3 ≤ L) {κ E : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) {σ : Fin k → Bool} (hσ : ∃ i : Fin k, σ i = σ (i + 1)) {K : ℕ}
    {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m)
    (hu1 : ∀ i ≤ K, u i < 1) {Kw : ℝ} (hKw : 1 ≤ Kw) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Z2 L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → nonAltCls L Kw u i δ X → ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ (u i) (u m) X a‖ ≤ kappaNonAlt L k κ Kw u i m * M + epsNonAlt k u i m * δ :=
  hker_of_case1 hk hL hκ hE hσ hu0 hmono hu1 hKw

/-- **The field `hA0cls`**, matrix level: for `M ∈ GoodSetN` the
tensor `a ↦ (𝓛-𝒦)_{u,σ,a}(M)` has `(ℓ_u W^{τ'}, W^{-D'})` decay (clause (Dec) at length `k`). -/
theorem goodSetN_A0cls {E u Γ Λ Φ τ' D' : ℝ} {k : ℕ} (hk : 1 ≤ k)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D')
    (σ : Fin k → Bool) :
    DecayWin L (ellT L u * (W : ℝ) ^ τ') ((W : ℝ) ^ (-D')) (lkTensor L W E u M σ) := by
  obtain ⟨-, -, -, -, -, hDec, -⟩ := hM
  intro a hfar
  have h := hDec k hk (by omega) σ a hfar
  have h0 : 0 ≤ loopAbs L W E u M σ a := norm_nonneg _
  have : ‖lkTensor L W E u M σ a‖ = lkGen L W E u M σ a := rfl
  rw [this]; linarith

/-- **The field `hDcls`**, matrix level: the drift tensor at
`u` has `(ℓ_{u'} W^{τ'}, W^{-D'})` decay for every `u' ≥ u` (clause (V); the radius
`ℓ_u W^{τ'} ≤ ℓ_{u'} W^{τ'}` only grows, so the window only shrinks). -/
theorem goodSetN_driftCls {E u u' Γ Λ Φ τ' D' : ℝ} {k : ℕ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D')
    (σ : Fin k → Bool) (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'1 : u' < 1) :
    DecayWin L (ellT L u' * (W : ℝ) ^ τ') ((W : ℝ) ^ (-D')) (driftTensor L W E u M σ) := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hrad : ellT L u ≤ ellT L u' := (ellT_mono_ratio hLp hu0 huu' hu'1).1
  intro a hfar
  have hWτ : 0 ≤ (W : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact driftTensor_far_of_goodSet hM σ a
    ((mul_le_mul_of_nonneg_right hrad hWτ).trans hfar)

end Classes

section Pathwise

variable {d : Sizes} {E s v : ℕ → ℝ} {K : ℕ → ℕ}

/-- **The field `hA0cls` on the event `{H_0 ∈ GoodSetN(u_0)}`**: on `{0 < τ}` the initial tensor
`A_0 = (𝓛-𝒦)_{u_0}(H_0)` is in the class `nonAltCls` with radius `ℓ_{u_0} W^{τ'}` and
`δ_0 = W^{-D'}`. -/
theorem nonAlt_hA0cls {n k : ℕ} [NeZero k] (hk : 1 ≤ k) (σ : Fin k → Bool)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (τ : PathΩ d → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
      (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω, 0 < τ ω → nonAltCls (d.L n) ((d.W n : ℝ) ^ τ') (gridTime s v K n) 0
      ((d.W n : ℝ) ^ (-D')) (AvecN d E s v K n 0 σ ω) :=
  fun ω hω => goodSetN_A0cls hk (hτG ω 0 hω) σ

/-- **The field `hdrift` on the event `{H_j ∈ GoodSetN(u_j), j < τ}`**: the drift tensor
`Dr_j = Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}` at `(u_j, H_j)` is bounded by
`dDriftNonAlt` (the triangle inequality of
`driftTensor_norm_le_of_goodSet`). -/
theorem nonAlt_hdrift {n k : ℕ} [NeZero k] (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (τ : PathΩ d → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
      (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Z2 (d.L n),
      ‖driftTensor (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ b‖ ≤
        dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Φ n) D' :=
  fun ω j _ hjτ b => driftTensor_norm_le_of_goodSet (hτG ω j hjτ) σ b

/-- **The field `hDcls` on the event**: the drift tensor at `(u_j, H_j)` is in the class
`nonAltCls` at index `j + 1` (radius `ℓ_{u_{j+1}} W^{τ'}`) with `δ_D = W^{-D'}`. -/
theorem nonAlt_hDcls {n k : ℕ} [NeZero k] (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (τ : PathΩ d → ℕ)
    (hτG : ∀ ω j, j < τ ω → pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
      (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') :
    ∀ ω j, j < K n → j < τ ω → nonAltCls (d.L n) ((d.W n : ℝ) ^ τ') (gridTime s v K n) (j + 1)
      ((d.W n : ℝ) ^ (-D'))
      (driftTensor (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ) := by
  intro ω j hjK hjτ
  have hu0 : 0 ≤ gridTime s v K n j := GoodEvent_gridTime_nonneg hs0 hsv j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := GoodEvent_gridTime_mono hsv (by omega)
  have hu1 : gridTime s v K n (j + 1) < 1 :=
    (GoodEvent_gridTime_le (K := K) hsv (show j + 1 ≤ K n by omega)).trans_lt hv1
  exact goodSetN_driftCls (hτG ω j hjτ) σ hu0 hjj hu1

/-- The non-negativity fields `hκ0`, `hε0` of `GridAssemblyHypN`, on the grid. -/
theorem nonAlt_hκ0 {L : ℕ} [NeZero L] (k : ℕ) (κ Kw : ℝ) (hKw : 0 ≤ Kw) {K : ℕ} {u : ℕ → ℝ}
    (hu1 : ∀ i ≤ K, u i < 1) :
    ∀ i m, i ≤ m → m ≤ K → 0 ≤ kappaNonAlt L k κ Kw u i m :=
  fun i m him hmK => NonAltGood_kappaNonAlt_nonneg k κ Kw u hKw (hu1 i (him.trans hmK)) (hu1 m hmK)

theorem nonAlt_hε0 (k : ℕ) {K : ℕ} {u : ℕ → ℝ} (hu1 : ∀ i ≤ K, u i < 1) :
    ∀ i m, i ≤ m → m ≤ K → 0 ≤ epsNonAlt k u i m :=
  fun i m him hmK => NonAltGood_epsNonAlt_nonneg k u (hu1 i (him.trans hmK)) (hu1 m hmK)

/-- The non-negativity fields `hdDrift0` of `GridAssemblyHypN`, on the grid. -/
theorem nonAlt_hdDrift0 {n k : ℕ} (hE : |E n| < 2) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (Γ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n) (D' : ℝ) :
    ∀ (ω : PathΩ d) j, j < K n → 0 ≤ dDriftNonAlt (d.L n) (d.W n) (E n) (gridTime s v K n j) k
      (Γ n) (Φ n) D' := by
  intro ω j hj
  have hu1 : gridTime s v K n j < 1 :=
    (GoodEvent_gridTime_le (K := K) hsv (show j ≤ K n by omega)).trans_lt hv1
  exact NonAltGood_dDriftNonAlt_nonneg (d.L n) (d.W n) hE hu1 k hΓ hΦ D'

end Pathwise

/-! ## 4. The quadratic-variation constant -/

section QVConst

/-- **The variance majorant of Case 1**:
`c_pair (1+log L)^{2k} K_w^{2(2k-1)} ρ_{u,w}^{2k} (Γ² Λ M_u^{-2k} η_u^{-1} + W^{-D''}) +
((1-u)/(1-w))^{2k} W^{-D''}`, `K_w = W^{τ'}` (`d = 2`: `ρ` with `M_u^{-1}`, `c_pair = cPair1`,
the pair form `𝒰_σ ⊗ 𝒰_σ̄` on `𝓔 ⊗ 𝓔`). -/
def qvBdNonAlt (L W : ℕ) (E : ℝ) (k : ℕ) (κ Γ Λ τ' D'' u w : ℝ) : ℝ :=
  cPair1 k κ * (1 + Real.log L) ^ (2 * k) * ((W : ℝ) ^ τ') ^ (2 * (2 * k - 1)) *
      rhoR L u w ^ (2 * k) *
      (Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D'')) +
    ((1 - u) / (1 - w)) ^ (2 * k) * (W : ℝ) ^ (-D'')

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `0 < qvBdNonAlt`: the last term is positive and the first
is non-negative. -/
theorem qvBdNonAlt_pos {E : ℝ} (hE : |E| < 2) {k : ℕ} {κ Γ Λ τ' D'' u w : ℝ} (hΓ : 0 ≤ Γ)
    (hΛ : 0 ≤ Λ) (huw : u ≤ w) (hw1 : w < 1) : 0 < qvBdNonAlt L W E k κ Γ Λ τ' D'' u w := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu1 : u < 1 := huw.trans_lt hw1
  have hM := scaleM_pos hLp hWp hE hu1
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWp
  have hWD : 0 < (W : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hW0 _
  have hWτ : 0 ≤ (W : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hlog : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  have hc := NonAltGood_cPair1_nonneg k κ
  have hρ := NonAltGood_rhoR_nonneg (L := L) hu1 hw1
  have h1u : 0 < 1 - u := by linarith
  have h1w : 0 < 1 - w := by linarith
  unfold qvBdNonAlt
  have hfirst : 0 ≤ cPair1 k κ * (1 + Real.log L) ^ (2 * k) * ((W : ℝ) ^ τ') ^ (2 * (2 * k - 1)) *
      rhoR L u w ^ (2 * k) *
      (Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D'')) := by
    positivity
  have hsecond : 0 < ((1 - u) / (1 - w)) ^ (2 * k) * (W : ℝ) ^ (-D'') := by positivity
  linarith

/-- **The variance majorant of `AzumaSubGN` after the spectral-time shift `u → u'`** (through the shift of the pair form,
`norm_eeN_shiftN_le`): for `M ∈ GoodSetN(u)` (levels `Γ, Λ, Φ`, decay `τ', D'`), `0 ≤ u ≤ u' ≤ w <
1` and a non-alternating `σ`, if `W^{-D'} + eeShiftErr ≤ W^{-D''}`, then
`qvFormN_{u',w}(M) ≤ qvBdNonAlt(u', w; Γ, Λ, τ', D'')`.  (Without the shift, `u' = u`.) -/
theorem qvFormN_le_of_goodSet_shiftN {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hL : 3 ≤ L)
    {κ E u u' w Γ Λ Φ τ' D' D'' : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (huu' : u ≤ u') (hu'w : u' ≤ w) (hw1 : w < 1) {σ : Fin k → Bool}
    (hσ : ∃ i : Fin k, σ i = σ (i + 1)) (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ) (hτ' : 0 ≤ τ')
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D')
    (hδ : (W : ℝ) ^ (-D') + eeShiftErr L W E k u u' ≤ (W : ℝ) ^ (-D'')) (a : Fin k → Z2 L) :
    qvFormN L W E u' w σ M a ≤ qvBdNonAlt L W E k κ Γ Λ τ' D'' u' w := by
  have hMh : M.IsHermitian := hM.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hE' : |E| < 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := hE'.le
  have hLp : 1 ≤ L := by omega
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu1 : u < 1 := (huu'.trans hu'w).trans_lt hw1
  have hu'1 : u' < 1 := hu'w.trans_lt hw1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWp
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWp
  have hKw : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hWr hτ'
  have hWD : 0 ≤ (W : ℝ) ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hMu := scaleM_pos hLp hWp hE' hu1
  have hMu' := scaleM_pos hLp hWp hE' hu'1
  have hηu := etaT_pos hE' hu1
  have hηu' := etaT_pos hE' hu'1
  have hMle : scaleM L W E u' ≤ scaleM L W E u := (scaleM_anti_ratio hLp hE' huu' hu'1).1
  have hηle : etaT E u' ≤ etaT E u := NonAltGood_etaT_anti hE' huu'
  have hG : 0 ≤ Γ * (Γ * Λ) := mul_nonneg hΓ (mul_nonneg hΓ hΛ)
  have hpow : (scaleM L W E u ^ (2 * k))⁻¹ ≤ (scaleM L W E u' ^ (2 * k))⁻¹ :=
    inv_anti₀ (pow_pos hMu' _) (pow_le_pow_left₀ hMu'.le hMle _)
  have hinv : (etaT E u)⁻¹ ≤ (etaT E u')⁻¹ := inv_anti₀ hηu' hηle
  have hmain : Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) ≤
      Γ * (Γ * Λ) * ((scaleM L W E u' ^ (2 * k))⁻¹ * (etaT E u')⁻¹) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hpow hinv (inv_nonneg.2 hηu.le)
      (inv_nonneg.2 (pow_pos hMu' _).le)) hG
  have hMx : 0 ≤ Γ * (Γ * Λ) * ((scaleM L W E u' ^ (2 * k))⁻¹ * (etaT E u')⁻¹) +
      (W : ℝ) ^ (-D'') :=
    add_nonneg (mul_nonneg hG (mul_nonneg (inv_nonneg.2 (pow_pos hMu' _).le)
      (inv_nonneg.2 hηu'.le))) hWD
  have hshift := fun b b' => (norm_eeN_shiftN_le hL hE' hMh huu' hu'1 σ b b')
  have hLK : ellT L u ≤ ellT L u' := (ellT_mono_ratio hLp hu0 huu' hu'1).1
  have hWτ : 0 ≤ (W : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  rw [qvFormN_eq_re_UgenPair hL hE2 (abs_lt.2 ⟨by linarith [hu0], hw1⟩) σ M a]
  refine (Complex.re_le_norm _).trans ?_
  refine ugenPairCase1Explicit k hk L hL κ E hκ hE u' w (hu0.trans huu') hu'w hw1 σ hσ
    ((W : ℝ) ^ τ') _ ((W : ℝ) ^ (-D'')) hKw hMx hWD (eeN L W E u' M σ) (fun b b' => ?_)
    (fun b b' hfar => ?_) a
  · have h1 := hD4 σ b b'
    have h2 := hshift b b'
    have h3 : ‖eeN L W E u' M σ b b'‖ ≤ ‖eeN L W E u M σ b b'‖ +
        ‖eeN L W E u' M σ b b' - eeN L W E u M σ b b'‖ := by
      have := norm_add_le (eeN L W E u M σ b b') (eeN L W E u' M σ b b' - eeN L W E u M σ b b')
      rwa [add_sub_cancel] at this
    linarith
  · have hfar' : ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L (Fin.append b b') : ℝ) :=
      (mul_le_mul_of_nonneg_right hLK hWτ).trans hfar
    have h1 := hVb σ b b' hfar'
    have h2 := hshift b b'
    have h3 : ‖eeN L W E u' M σ b b'‖ ≤ ‖eeN L W E u M σ b b'‖ +
        ‖eeN L W E u' M σ b b' - eeN L W E u M σ b b'‖ := by
      have := norm_add_le (eeN L W E u M σ b b') (eeN L W E u' M σ b b' - eeN L W E u M σ b b')
      rwa [add_sub_cancel] at this
    linarith

end QVConst

section QVGrid

variable {d : Sizes}

/-- **The sub-Gaussian constant of the `j`-th propagated increment** towards the target `u_m`:
`Δ · k · qvBdNonAlt(u_{j+1}, u_m)` (the factor `k` of `qv_at_propagator`;
the label `a` does not enter). -/
def cQVNonAlt (d : Sizes) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (κ : ℝ) (Γ Λ : ℕ → ℝ)
    (τ' D'' : ℝ) (m : ℕ) (_a : Fin k → Z2 (d.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * qvBdNonAlt (d.L n) (d.W n) (E n) k κ (Γ n) (Λ n) τ' D''
    (gridTime s v K n (j + 1)) (gridTime s v K n m))).toNNReal

/-- **The majorant `hQ` of `azumaSubG_goodExit` on the good set** (the
deterministic part): for `M ∈ GoodSetN(u_j)` Hermitian, `Δ · (k · qvFormN_{u_{j+1},u_m}(M)) ≤
cQVNonAlt`, under the shift hypothesis `W^{-D'} + eeShiftErr(u_j, u_{j+1}) ≤ W^{-D''}`. -/
theorem hQ_nonAlt {E s v : ℕ → ℝ} {K : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : ∃ i : Fin k, σ i = σ (i + 1))
    (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (τ' D' D'' : ℝ) (hτ' : 0 ≤ τ') (m : ℕ)
    (hm : m ≤ K n) (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m)
    (hδ : (d.W n : ℝ) ^ (-D') + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-D'')) :
    ∀ M ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormN (d.L n) (d.W n) (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤
        (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' m a j : ℝ) := by
  intro M hM _
  have hΔ : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hu0 : 0 ≤ gridTime s v K n j := GoodEvent_gridTime_nonneg (hs0 n) (hsv n) j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    GoodEvent_gridTime_mono (hsv n) (by omega)
  have hj1m : gridTime s v K n (j + 1) ≤ gridTime s v K n m :=
    GoodEvent_gridTime_mono (hsv n) (by omega)
  have hw1 : gridTime s v K n m < 1 := (GoodEvent_gridTime_le (K := K) (hsv n) hm).trans_lt (hv1 n)
  have hq := qvFormN_le_of_goodSet_shiftN hk (d.three_le_L n) hκ (hE n) hu0 hjj hj1m hw1 hσ hΓ hΛ
    hτ' hM hδ a
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **The `SubGaussStopN` input of `AssembledN` for non-alternating `σ`**: `azumaSubGN`, the test
class `hermTestFunLoopN` and the exit time `goodExitTauN`
give, for the stopped propagated first-chaos part `ZvecN`, sub-Gaussianity with the explicit
proxy `cQVNonAlt`.  The only extra hypothesis is the shift inequality
`W^{-D'} + eeShiftErr(u_j, u_{j+1}) ≤ W^{-D''}`. -/
theorem subGaussStop_nonAlt {E s v : ℕ → ℝ} {K : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : ∃ i : Fin k, σ i = σ (i + 1))
    (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (τ' D' D'' : ℝ) (hτ' : 0 ≤ τ') (m : ℕ)
    (hm : m ≤ K n) (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m)
    (hδ : (d.W n : ℝ) ^ (-D') + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-D'')) :
    SubGaussStopN d (E n) σ (gridTime s v K n) (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
      (fun j ω => ZvecN d E s v K n j σ ω) m a j (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' m a j) :=
  azumaSubG_goodExit (azumaSubGN d s v K) (hermTestFunLoopN d) (goodExitMeasN d E s v K)
    (fun n => by linarith [abs_nonneg (E n), hE n]) hs0 hsv hv1 n k hk σ Γ Λ Φ τ' D' m hm a j hj
    (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' m a j)
    (hQ_nonAlt hκ hE hs0 hsv hv1 n k hk hσ Γ Λ Φ hΓ hΛ τ' D' D'' hτ' m hm a j hj hδ)

/-- **The field `hc_pos`**: `Σ_{j<m} c_j > 0` for `Δ > 0`,
i.e. `s_n < v_n`, `K_n ≠ 0` (the field needs the strict window, `AssembledN` gives only
`0 ≤ Δ`). -/
theorem cQVNonAlt_sum_pos {E s v : ℕ → ℝ} {K : ℕ → ℕ} {κ : ℝ} (n k : ℕ) (hE : |E n| < 2)
    (hk : 1 ≤ k) (hsv : s n < v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (Γ Λ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (τ' D'' : ℝ) :
    ∀ m, 1 ≤ m → m ≤ K n → ∀ a : Fin k → Z2 (d.L n),
      0 < ∑ j ∈ Finset.range m, (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' m a j : ℝ) := by
  intro m hm1 hmK a
  have hΔ : 0 < gridStep s v K n :=
    div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hK)
  have hterm : ∀ j ∈ Finset.range m, 0 ≤ (cQVNonAlt d E s v K n k κ Γ Λ τ' D'' m a j : ℝ) :=
    fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  have h1m : gridTime s v K n (0 + 1) ≤ gridTime s v K n m :=
    GoodEvent_gridTime_mono (le_of_lt hsv) (by omega)
  have hw1 : gridTime s v K n m < 1 :=
    (GoodEvent_gridTime_le (K := K) (le_of_lt hsv) hmK).trans_lt hv1
  have hpos := qvBdNonAlt_pos (L := d.L n) (W := d.W n) hE (k := k) (κ := κ) (τ' := τ')
    (D'' := D'') hΓ hΛ h1m hw1
  unfold cQVNonAlt
  rw [Real.coe_toNNReal _ (by positivity)]
  exact mul_pos hΔ (mul_pos (by exact_mod_cast hk) hpos)

end QVGrid

end RBM.Ind

end
