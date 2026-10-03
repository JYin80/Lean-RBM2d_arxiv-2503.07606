/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Kernel
import RBM2D.Path.ScalesBridge
import RBM2D.Loop.Kcal
import RBM2D.Loop.LatticeCount
import RBM2D.Propagator.Prop5
import RBM2D.Propagator.Prop6

/-!
# The `d = 2` kernel inputs of `lem:sum_decay`: bounds on `Ξ = (1 - vξS)Θ_{wξ} - 1`

Paper: arXiv:2503.07606, Section 7: `def_psixi`, the row bound
`tyzcsq`, `Xi-bound-0`, `Xi-bound-1`, `Xi-bound-2`.

The definitions `xiMat`, `cProp5`, `cShortRow` and the five `Prop`s `XiEntryBound`,
`XiRowBound`, `XiRowBoundShort`, `XiFirstDiff`, `XiSecondDiff` are stated below.  Each is proved
by the theorem of the same name with the first letter in lower case.

Argument (`d = 2`; no `d = 1` closed form is used).
* `Ξ = (w - v) ξ S Θ_{wξ}` (`xiMat_eq`, from `mul_Theta`), so every entry of `Ξ` is `(t - s) ξ`
  times an average of the entries of `Θ_{tξ}` against the five-point kernel `S^{(B)}`
  (`xiMat_apply`, `sum_norm_SB_row`, and `‖S^{(B)}_{ax}‖ ≠ 0 ⇒ |a - x|_L ≤ 1`).
* Entry bound: property 5 (`norm_Theta_apply_le_prop5`) at `ζ = tξ`.  Since `|1 - tξ| ≥ 1 - t` for
  `|ξ| ≤ 1`, one has `κ(ζ) ≥ κ(t)`, hence `ℓ̂(ζ) ≤ ℓ_t` and `κ(ζ)²ℓ̂(ζ)² ≥ min(1, L²(1 - t))`;
  property 5 at `ζ` is therefore at least as strong as property 5 at the real `t` (so the
  entrywise domination `|Θ_{tξ}| ≤ Θ_t` is not needed).  The shift
  `|a - b| ≤ 1 + |x - b|` costs `exp(1/(20000 ℓ_t)) ≤ 2`.
* Row bound: `sum_norm_Theta_row_le` (`Σ_b |Θ_ζ(x, b)| ≤ (1 - |ζ|)⁻¹`) and
  `(1 - |ζ|)⁻¹ ≤ (1 - t)⁻¹`; this loses no constant (equality at `ξ = 1`).
* Short-edge row: property 5 at `ζ = t m(σ)²`, the bulk gap `c_κ ≤ |1 - t m(σ)²|` (restated
  privately from `RBM.KLoop` `gapK_le_norm`), and
  `KLoop.sum_exp_le` at `s = 1/(20000 ℓ̂(ζ))`.
* Differences: property 6 (`norm_Theta_fd_prop6`) at the real `ζ = t` with
  `κ(t)ℓ̂(t)² = √(1 - t) ℓ_t²` (`kloop_ellT_eq`), then `(|x-b|+1)⁻¹ ≤ 2 (|a-b|+1)⁻¹` and
  `(|x-b|²+1)⁻¹ ≤ 4 (|a-b|²+1)⁻¹` for `|a - x|_L ≤ 1`.

Differences from `d = 1`: `ZMod L ↦ Z2 L`; the d = 1 constants become the
d = 2 property 5 and 6 prefactors (`cProp5`, `derivativePrefactor`); the decay of property 5 is
`exp(-|x|_L/(20000 ℓ̂))` in the L¹ distance `zdist2`, and its sum over `Z_L²` is `KLoop.sum_exp_le`
(`(1 + 2/s)²`, not the d = 1 geometric sum); the `d = 2` difference bounds carry the two-term
`(|x|+1)⁻¹` / `(|x|²+1)⁻¹` shape of property 6.
-/

noncomputable section

namespace RBM.Evol

open RBM.Path

section Scales

variable (L : ℕ) [NeZero L]

/-- `Ξ = (1 - vξS)Θ_{wξ} - 1 = (w - v) ξ S Θ_{wξ}` (`def_psixi`). -/
def xiMat (ξ : ℂ) (v w : ℝ) : Matrix (Z2 L) (Z2 L) ℂ := ukerMat L ξ v w - 1

end Scales

/-- The prefactor of property 5 (`norm_Theta_apply_le_prop5`): `180 · 40002²`. -/
def cProp5 : ℝ := 180 * 40002 ^ 2

/-- The short-edge row constant: `2 cProp5 / c_κ · (1 + 40000 / √c_κ)²`, `c_κ = KLoop.gapK κ`. -/
def cShortRow (κ : ℝ) : ℝ :=
  2 * cProp5 / KLoop.gapK κ * (1 + 40000 / Real.sqrt (KLoop.gapK κ)) ^ 2

/-- **`XiEntryBound`** (`Xi-bound-0`), explicit: for `‖ξ‖ ≤ 1`, `0 ≤ s ≤ t < 1`,
`|Ξ_{ab}| ≤ 2 cProp5 (1 + log L) (t - s) / min(1, L²(1-t)) · exp(-|a-b|_L / (20000 ℓ_t))`.
(`(t-s)/min(1, L²(1-t)) ≤ η_s/(ℓ_t²η_t)`.)  Inputs: `norm_Theta_apply_le_prop5` at `ξ = t`,
`Theta_eq_tsum` (entrywise domination `|Θ_{tξ}| ≤ Θ_t`), the support of `SB`. -/
def XiEntryBound : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ a b : Z2 L, ‖xiMat L ξ s t a b‖ ≤
      2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
        Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t))

/-- **`XiRowBound`** (`tyzcsq`, row part): `Σ_b |Ξ_{ab}| ≤ (t - s)/(1 - t)` for `‖ξ‖ ≤ 1`
(so `Σ_b |ψ_{ab}| ≤ (1 - s)/(1 - t) = η_s/η_t`). -/
def XiRowBound : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ a : Z2 L, ∑ b : Z2 L, ‖xiMat L ξ s t a b‖ ≤ (t - s) / (1 - t)

/-- **`XiRowBoundShort`** (the short edge of Case 1, proof of `lem:sum_decay`
"`Σ_{b₁}|Ξ₁| = O(1)`"): for `ξ = m(σ)²`,
`|E| ≤ 2 - κ`, `Σ_b |Ξ_{ab}| ≤ cShortRow κ · (1 + log L)`.  Inputs: property 5 at `ζ = t m(σ)²`
and the gap `c_κ ≤ |1 - t m(σ)²|` (private `gapK_le_norm`, `Loop/SumZero.lean`). -/
def XiRowBoundShort : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ κ E : ℝ, 0 < κ → |E| ≤ 2 - κ → ∀ (σ : Bool) (s t : ℝ),
    0 ≤ s → s ≤ t → t < 1 → ∀ a : Z2 L,
      ∑ b : Z2 L, ‖xiMat L (KLoop.mSig E σ * KLoop.mSig E σ) s t a b‖ ≤
        cShortRow κ * (1 + Real.log L)

/-- **`XiFirstDiff`** (`Xi-bound-1`), `ξ = |m|² = 1`: the first difference in the second
index, `≤ 2 P_L (t - s)(|r|/(|a-b|+1) + |r|/(√(1-t) ℓ_t²))`, `P_L = derivativePrefactor 10¹⁴ L`
(from `norm_Theta_fd_prop6` with `κ(t)ℓ̂(t)² = √(1-t) ℓ_t²`). -/
def XiFirstDiff : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ a b r : Z2 L,
    ‖xiMat L 1 s t a b - xiMat L 1 s t a (b + r)‖ ≤
      2 * derivativePrefactor (10 ^ 14) L * (t - s) *
        ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
          (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2))

/-- **`XiSecondDiff`** (`Xi-bound-2`), `ξ = 1`: the second difference,
`≤ 4 P_L (t - s)(|r|²/(|a-b|²+1) + |r|²/ℓ_t²)`. -/
def XiSecondDiff : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ a b r : Z2 L,
    ‖2 * xiMat L 1 s t a b - xiMat L 1 s t a (b + r) - xiMat L 1 s t a (b - r)‖ ≤
      4 * derivativePrefactor (10 ^ 14) L * (t - s) *
        ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
          (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2)

/-! ## Helpers (all `private`) -/

section Helpers

variable (L : ℕ) [NeZero L]

/-- `‖(t : ℂ) ξ‖ ≤ t` for `‖ξ‖ ≤ 1`, `0 ≤ t`. -/
private theorem norm_ofReal_mul_le_self {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {t : ℝ} (h0 : 0 ≤ t) :
    ‖(t : ℂ) * ξ‖ ≤ t := by
  rw [norm_mul, Complex.norm_of_nonneg h0]
  calc t * ‖ξ‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hξ h0
    _ = t := mul_one t

/-- `1 - t ≤ ‖1 - (t : ℂ) ξ‖` for `‖ξ‖ ≤ 1`, `0 ≤ t`. -/
private theorem one_sub_le_norm_one_sub {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {t : ℝ} (h0 : 0 ≤ t) :
    1 - t ≤ ‖(1 : ℂ) - (t : ℂ) * ξ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * ξ)
  have h2 := norm_ofReal_mul_le_self hξ h0
  rw [norm_one] at h
  linarith

/-- `κ(t) = √(1 - t)` for real `t ≤ 1`. -/
private theorem kappa_ofReal {t : ℝ} (ht : t ≤ 1) : kappa (t : ℂ) = Real.sqrt (1 - t) := by
  have h : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  unfold kappa
  rw [h, Complex.norm_of_nonneg (by linarith)]

/-- `ℓ̂(t) = ℓ_t` for real `t ≤ 1` (`kloop_ellT_eq`). -/
private theorem ellhat_ofReal {t : ℝ} (ht : t ≤ 1) : ellhat L (t : ℂ) = ellT L t :=
  kloop_ellT_eq ht

/-- `ℓ̂(ζ) ≤ ℓ_t` for `‖ζ‖ ≤ t < 1`, `0 ≤ t` (`κ(ζ) ≥ κ(t)`). -/
private theorem ellhat_le_ellT {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ t) :
    ellhat L ζ ≤ ellT L t := by
  have hζ1 : ‖ζ‖ < 1 := lt_of_le_of_lt hζ ht
  have htc : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg ht0]; exact ht
  have h1 : 1 - t ≤ ‖(1 : ℂ) - ζ‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ζ
    rw [norm_one] at h
    linarith
  have hk : kappa (t : ℂ) ≤ kappa ζ := by
    rw [kappa_ofReal ht.le]
    exact Real.sqrt_le_sqrt h1
  rw [← ellhat_ofReal L ht.le]
  exact min_le_min (inv_anti₀ (kappa_pos htc) hk) le_rfl

omit [NeZero L] in
/-- `min(1, L² c) ≤ κ(ζ)² ℓ̂(ζ)²` whenever `c ≤ |1 - ζ| = κ(ζ)²`. -/
private theorem min_le_kappa_sq_ellhat_sq {ζ : ℂ} (hζ : ‖ζ‖ < 1) {c : ℝ}
    (hc : c ≤ ‖(1 : ℂ) - ζ‖) :
    min 1 ((L : ℝ) ^ 2 * c) ≤ kappa ζ ^ 2 * ellhat L ζ ^ 2 := by
  have hk : 0 < kappa ζ := kappa_pos hζ
  by_cases h : (kappa ζ)⁻¹ ≤ (L : ℝ)
  · have h1 : ellhat L ζ = (kappa ζ)⁻¹ := min_eq_left h
    rw [h1, inv_pow, mul_inv_cancel₀ (pow_pos hk 2).ne']
    exact min_le_left _ _
  · have h' : (L : ℝ) ≤ (kappa ζ)⁻¹ := (not_le.1 h).le
    have h1 : ellhat L ζ = (L : ℝ) := min_eq_right h'
    rw [h1, kappa_sq]
    calc min 1 ((L : ℝ) ^ 2 * c) ≤ (L : ℝ) ^ 2 * c := min_le_right _ _
      _ ≤ (L : ℝ) ^ 2 * ‖(1 : ℂ) - ζ‖ := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = ‖(1 : ℂ) - ζ‖ * (L : ℝ) ^ 2 := by ring

/-- `0 < min(1, L²(1 - t))` for `t < 1`, `1 ≤ L`. -/
private theorem min_one_pos {t : ℝ} (ht : t < 1) : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact lt_min one_pos (mul_pos (pow_pos hLpos 2) (by linarith))

/-- Property 5 at `ζ = tξ`, `‖ξ‖ ≤ 1`, restated with the real scales `ℓ_t` and
`min(1, L²(1 - t))`. -/
private theorem theta_entry_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < 1) (x b : Z2 L) :
    ‖Theta L ((t : ℂ) * ξ) x b‖ ≤
      cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
        Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) := by
  have hζt : ‖(t : ℂ) * ξ‖ ≤ t := norm_ofReal_mul_le_self hξ ht0
  have hζ1 : ‖(t : ℂ) * ξ‖ < 1 := lt_of_le_of_lt hζt ht
  have h5 : ‖Theta L ((t : ℂ) * ξ) x b‖ ≤ cProp5 * (1 + Real.log L) *
      (kappa ((t : ℂ) * ξ) ^ 2 * ellhat L ((t : ℂ) * ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ((t : ℂ) * ξ))) :=
    norm_Theta_apply_le_prop5 L hL _ hζ1 x b
  have hℓpos : 0 < ellhat L ((t : ℂ) * ξ) := ellhat_pos L hL hζ1
  have hℓle : ellhat L ((t : ℂ) * ξ) ≤ ellT L t := ellhat_le_ellT L ht0 ht hζt
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := min_one_pos L ht
  have hden : min 1 ((L : ℝ) ^ 2 * (1 - t)) ≤
      kappa ((t : ℂ) * ξ) ^ 2 * ellhat L ((t : ℂ) * ξ) ^ 2 :=
    min_le_kappa_sq_ellhat_sq L hζ1 (one_sub_le_norm_one_sub hξ ht0)
  have hden' : (kappa ((t : ℂ) * ξ) ^ 2 * ellhat L ((t : ℂ) * ξ) ^ 2)⁻¹ ≤
      (min 1 ((L : ℝ) ^ 2 * (1 - t)))⁻¹ := inv_anti₀ hm hden
  have hexp : Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ((t : ℂ) * ξ))) ≤
      Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hK : 0 ≤ cProp5 * (1 + Real.log L) := mul_nonneg hc5 hlog
  calc ‖Theta L ((t : ℂ) * ξ) x b‖
      ≤ cProp5 * (1 + Real.log L) *
          (kappa ((t : ℂ) * ξ) ^ 2 * ellhat L ((t : ℂ) * ξ) ^ 2)⁻¹ *
        Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ((t : ℂ) * ξ))) := h5
    _ ≤ cProp5 * (1 + Real.log L) * (min 1 ((L : ℝ) ^ 2 * (1 - t)))⁻¹ *
        Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hden' hK) hexp (Real.exp_pos _).le
        (mul_nonneg hK (inv_nonneg.2 hm.le))
    _ = cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
        Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) := by ring

/-- `Σ_x ‖S^{(B)}_{ax}‖ = 1`. -/
private theorem sum_norm_SB_row (hL : 3 ≤ L) (a : Z2 L) : ∑ x : Z2 L, ‖SB L a x‖ = 1 := by
  have h := congrArg (fun r : NNReal => (r : ℝ)) (sum_nnnorm_SB_row L hL a)
  simpa using h

/-- `S^{(B)}_{ax} ≠ 0 ⇒ |a - x|_L ≤ 1`. -/
private theorem zdist2_le_one_of_norm_SB_ne (hL : 3 ≤ L) {a x : Z2 L} (h : ‖SB L a x‖ ≠ 0) :
    zdist2 L (a - x) ≤ 1 := by
  by_cases hm : a - x ∈ sbSupport L
  · exact zdist2_le_one_of_mem_sbSupport L hL hm
  · exfalso
    apply h
    simp [SB_apply, sbKernel, hm]

/-- The triangle step `|a - b| ≤ |x - b| + 1` for `S^{(B)}_{ax} ≠ 0`. -/
private theorem zdist2_le_of_norm_SB_ne (hL : 3 ≤ L) {a x : Z2 L} (h : ‖SB L a x‖ ≠ 0)
    (b : Z2 L) : (zdist2 L (a - b) : ℝ) ≤ (zdist2 L (x - b) : ℝ) + 1 := by
  have h1 := zdist2_le_one_of_norm_SB_ne L hL h
  have h2 : zdist2 L (a - x + (x - b)) ≤ zdist2 L (a - x) + zdist2 L (x - b) :=
    zdist2_add_le L (a - x) (x - b)
  rw [show a - x + (x - b) = a - b by abel] at h2
  have h3 : zdist2 L (a - b) ≤ zdist2 L (x - b) + 1 := by omega
  exact_mod_cast h3

/-- `Ξ = (w - v) ξ S Θ_{wξ}` (`def_psixi`), as matrices; from `(1 - wξS) Θ_{wξ} = 1`. -/
private theorem xiMat_eq (hL : 3 ≤ L) {ξ : ℂ} {s t : ℝ} (hζ : ‖(t : ℂ) * ξ‖ < 1) :
    xiMat L ξ s t = (ξ * ((t : ℂ) - s)) • (SB L * Theta L ((t : ℂ) * ξ)) := by
  have h := mul_Theta L hL hζ
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold xiMat ukerMat
  rw [sub_mul, one_mul, smul_mul_assoc, ← h]
  module

/-- Entrywise `Ξ_{ab} = ξ (t - s) Σ_x S^{(B)}_{ax} Θ_{tξ}(x, b)`. -/
private theorem xiMat_apply (hL : 3 ≤ L) {ξ : ℂ} {s t : ℝ} (hζ : ‖(t : ℂ) * ξ‖ < 1)
    (a b : Z2 L) :
    xiMat L ξ s t a b =
      ξ * (((t : ℂ) - s) * ∑ x : Z2 L, SB L a x * Theta L ((t : ℂ) * ξ) x b) := by
  rw [xiMat_eq L hL hζ, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, mul_assoc]

/-- The same at `ξ = 1`. -/
private theorem xiMat_one_apply (hL : 3 ≤ L) {s t : ℝ} (ht : ‖(t : ℂ)‖ < 1) (a b : Z2 L) :
    xiMat L 1 s t a b = ((t : ℂ) - s) * ∑ x : Z2 L, SB L a x * Theta L (t : ℂ) x b := by
  have h := xiMat_apply L hL (ξ := 1) (s := s) (t := t) (by rwa [mul_one]) a b
  simpa only [one_mul, mul_one] using h

/-- `‖(t - s) Σ_x S_{ax} w_x‖ ≤ (t - s) Σ_x ‖S_{ax}‖ ‖w_x‖`. -/
private theorem norm_sub_mul_sum_SB_le {s t : ℝ} (hst : s ≤ t) (a : Z2 L) (w : Z2 L → ℂ) :
    ‖((t : ℂ) - s) * ∑ x : Z2 L, SB L a x * w x‖ ≤
      (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖w x‖ := by
  have h1 : ‖(t : ℂ) - s‖ = t - s := by
    have : (t : ℂ) - s = ((t - s : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_of_nonneg (by linarith)]
  rw [norm_mul, h1]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by linarith)
  simp only [norm_mul]
  exact le_rfl

/-- `‖Ξ_{ab}‖ ≤ (t - s) Σ_x ‖S_{ax}‖ ‖Θ_{tξ}(x, b)‖` for `‖ξ‖ ≤ 1`. -/
private theorem norm_xiMat_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a b : Z2 L) :
    ‖xiMat L ξ s t a b‖ ≤
      (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L ((t : ℂ) * ξ) x b‖ := by
  have hζ1 : ‖(t : ℂ) * ξ‖ < 1 :=
    lt_of_le_of_lt (norm_ofReal_mul_le_self hξ (hs.trans hst)) ht
  rw [xiMat_apply L hL hζ1, norm_mul]
  calc ‖ξ‖ * ‖((t : ℂ) - s) * ∑ x : Z2 L, SB L a x * Theta L ((t : ℂ) * ξ) x b‖
      ≤ 1 * ((t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L ((t : ℂ) * ξ) x b‖) :=
        mul_le_mul hξ (norm_sub_mul_sum_SB_le L hst a _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The row sum of `‖Ξ‖` from a uniform row bound `R` on `Θ_{tξ}`. -/
private theorem sum_norm_xiMat_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (a : Z2 L) {R : ℝ}
    (hR : ∀ x : Z2 L, ∑ b : Z2 L, ‖Theta L ((t : ℂ) * ξ) x b‖ ≤ R) :
    ∑ b : Z2 L, ‖xiMat L ξ s t a b‖ ≤ (t - s) * R := by
  calc ∑ b : Z2 L, ‖xiMat L ξ s t a b‖
      ≤ ∑ b : Z2 L, (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L ((t : ℂ) * ξ) x b‖ :=
        Finset.sum_le_sum fun b _ => norm_xiMat_le L hL hξ hs hst ht a b
    _ = (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ∑ b : Z2 L, ‖Theta L ((t : ℂ) * ξ) x b‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    _ ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * R :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hR x) (norm_nonneg _))
          (by linarith)
    _ = (t - s) * R := by rw [← Finset.sum_mul, sum_norm_SB_row L hL, one_mul]

/-- The first difference of `Ξ` at `ξ = 1`, averaged against `S^{(B)}`. -/
private theorem norm_xiMat_diff1_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a b b' : Z2 L) :
    ‖xiMat L 1 s t a b - xiMat L 1 s t a b'‖ ≤
      (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L (t : ℂ) x b - Theta L (t : ℂ) x b'‖ := by
  have htc : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (hs.trans hst)]; exact ht
  have e : xiMat L 1 s t a b - xiMat L 1 s t a b' =
      ((t : ℂ) - s) * ∑ x : Z2 L, SB L a x * (Theta L (t : ℂ) x b - Theta L (t : ℂ) x b') := by
    rw [xiMat_one_apply L hL htc, xiMat_one_apply L hL htc, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => (mul_sub _ _ _).symm
  rw [e]
  exact norm_sub_mul_sum_SB_le L hst a (fun x => Theta L (t : ℂ) x b - Theta L (t : ℂ) x b')

/-- The second difference of `Ξ` at `ξ = 1`, averaged against `S^{(B)}`. -/
private theorem norm_xiMat_diff2_le (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (a b b' b'' : Z2 L) :
    ‖2 * xiMat L 1 s t a b - xiMat L 1 s t a b' - xiMat L 1 s t a b''‖ ≤
      (t - s) * ∑ x : Z2 L, ‖SB L a x‖ *
        ‖2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x b' - Theta L (t : ℂ) x b''‖ := by
  have htc : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (hs.trans hst)]; exact ht
  have e : 2 * xiMat L 1 s t a b - xiMat L 1 s t a b' - xiMat L 1 s t a b'' =
      ((t : ℂ) - s) * ∑ x : Z2 L, SB L a x *
        (2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x b' - Theta L (t : ℂ) x b'') := by
    rw [xiMat_one_apply L hL htc, xiMat_one_apply L hL htc, xiMat_one_apply L hL htc]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e]
  exact norm_sub_mul_sum_SB_le L hst a
    (fun x => 2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x b' - Theta L (t : ℂ) x b'')

end Helpers


/-! ## Helpers for the short edge: the bulk gap -/

section Gap

/-- `‖m(σ)²‖ = 1` for `|E| ≤ 2`. -/
private theorem norm_mSig_mul_self {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ * KLoop.mSig E σ‖ = 1 := by
  have h : ‖KLoop.mSig E σ‖ = 1 := by
    cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]
  rw [norm_mul, h, one_mul]

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < KLoop.gapK κ := by
  unfold KLoop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem gapK_le_one (κ : ℝ) : KLoop.gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    KLoop.gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ KLoop.gapK κ := (gapK_pos hκ hκ2).le
  have h1 : KLoop.gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 =
      (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him := Gauss.spectralM_im E
  have hs := Gauss.spectralM_sqrt_sq hE
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- The bulk gap `c_κ ≤ |1 - t m(σ)²|` for `t ≥ 0`, `|E| ≤ 2 - κ` (the same statement as
`gapK_le_norm` in `Loop/SumZero.lean`, which is private there). -/
private theorem gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (s : Bool) :
    KLoop.gapK κ ≤ ‖1 - (t : ℂ) * (KLoop.mSig E s * KLoop.mSig E s)‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : KLoop.gapK κ ^ 2 ≤
      ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 := by
    rw [norm_one_sub_sq hE2]
    have hg1 : KLoop.gapK κ ^ 2 ≤ 1 := by
      have := gapK_le_one κ
      have := (gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have hle : KLoop.gapK κ ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ := by
    have := (gapK_pos hκ hκ2).le
    have := norm_nonneg (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E))
    nlinarith
  cases s
  · have hc : (1 : ℂ) - (t : ℂ) * (KLoop.mSig E false * KLoop.mSig E false) =
        (starRingEnd ℂ) (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)) := by
      simp [KLoop.mSig, map_sub, map_mul, Complex.conj_ofReal]
    rw [hc, Complex.norm_conj]
    exact hle
  · simpa [KLoop.mSig] using hle

end Gap

/-! ## The theorems -/

section Theorems

/-- **K1a**: the entry bound `Xi-bound-0`, explicit form. -/
theorem xiEntryBound : XiEntryBound := by
  intro L _ hL ξ hξ s t hs hst ht a b
  have h0 : 0 ≤ t := hs.trans hst
  have hℓ : 1 ≤ ellT L t := one_le_ellT (by omega) h0 ht
  have hD : 0 < 20000 * ellT L t := by linarith
  have hm : 0 < min 1 ((L : ℝ) ^ 2 * (1 - t)) := min_one_pos L ht
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  -- `exp (1 / (20000 ℓ_t)) ≤ 2`
  have hy0 : 0 ≤ 1 / (20000 * ellT L t) := by positivity
  have hy1 : 1 / (20000 * ellT L t) ≤ 1 / 20000 := by
    rw [div_le_div_iff₀ hD (by norm_num)]; nlinarith
  have hexp2 : Real.exp (1 / (20000 * ellT L t)) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval hy0 (by linarith)
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  set K : ℝ := cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
    Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) :=
      div_nonneg (mul_nonneg hc5 hlog) hm.le
    exact mul_nonneg this (Real.exp_pos _).le
  have hterm : ∀ x : Z2 L,
      ‖SB L a x‖ * ‖Theta L ((t : ℂ) * ξ) x b‖ ≤ ‖SB L a x‖ * (2 * K) := by
    intro x
    by_cases hx : ‖SB L a x‖ = 0
    · simp [hx]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := theta_entry_le L hL hξ h0 ht x b
      have h2 := zdist2_le_of_norm_SB_ne L hL hx b
      have h3a : -(zdist2 L (x - b) : ℝ) / (20000 * ellT L t) ≤
          -(zdist2 L (a - b) : ℝ) / (20000 * ellT L t) + 1 / (20000 * ellT L t) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hD.le
      have h3 : Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) ≤
          2 * Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) := by
        calc Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t))
            ≤ Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t) +
                1 / (20000 * ellT L t)) := Real.exp_le_exp.mpr h3a
          _ = Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) *
                Real.exp (1 / (20000 * ellT L t)) := Real.exp_add _ _
          _ ≤ Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) * 2 :=
              mul_le_mul_of_nonneg_left hexp2 (Real.exp_pos _).le
          _ = 2 * Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) := mul_comm _ _
      calc ‖Theta L ((t : ℂ) * ξ) x b‖
          ≤ cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
              Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellT L t)) := h1
        _ ≤ cProp5 * (1 + Real.log L) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
              (2 * Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t))) :=
            mul_le_mul_of_nonneg_left h3 (div_nonneg (mul_nonneg hc5 hlog) hm.le)
        _ = 2 * K := by rw [hK]; ring
  calc ‖xiMat L ξ s t a b‖
      ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L ((t : ℂ) * ξ) x b‖ :=
        norm_xiMat_le L hL hξ hs hst ht a b
    _ ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * (2 * K) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) (by linarith)
    _ = (t - s) * (2 * K) := by rw [← Finset.sum_mul, sum_norm_SB_row L hL, one_mul]
    _ = 2 * cProp5 * (1 + Real.log L) * (t - s) / min 1 ((L : ℝ) ^ 2 * (1 - t)) *
          Real.exp (-(zdist2 L (a - b) : ℝ) / (20000 * ellT L t)) := by rw [hK]; ring

/-- **`xiRowBound`**: the row bound `tyzcsq`, kernel part; no constant is lost. -/
theorem xiRowBound : XiRowBound := by
  intro L _ hL ξ hξ s t hs hst ht a
  have h0 : 0 ≤ t := hs.trans hst
  have hζt : ‖(t : ℂ) * ξ‖ ≤ t := norm_ofReal_mul_le_self hξ h0
  have hζ1 : ‖(t : ℂ) * ξ‖ < 1 := lt_of_le_of_lt hζt ht
  have hR : ∀ x : Z2 L, ∑ b : Z2 L, ‖Theta L ((t : ℂ) * ξ) x b‖ ≤ (1 - t)⁻¹ := fun x =>
    (sum_norm_Theta_row_le L hL hζ1 x).trans (inv_anti₀ (by linarith) (by linarith))
  calc ∑ b : Z2 L, ‖xiMat L ξ s t a b‖ ≤ (t - s) * (1 - t)⁻¹ :=
        sum_norm_xiMat_le L hL hξ hs hst ht a hR
    _ = (t - s) / (1 - t) := by rw [div_eq_mul_inv]

/-- **`xiRowBoundShort`**: the short-edge row bound (proof of `lem:sum_decay`,
`Σ_{b₁}|Ξ₁| = O(1)`), explicit in `κ`. -/
theorem xiRowBoundShort : XiRowBoundShort := by
  intro L _ hL κ E hκ hE σ s t hs hst ht a
  have h0 : 0 ≤ t := hs.trans hst
  have hE2 : |E| ≤ 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hξ : ‖KLoop.mSig E σ * KLoop.mSig E σ‖ = 1 := norm_mSig_mul_self hE2 σ
  have hζt : ‖(t : ℂ) * (KLoop.mSig E σ * KLoop.mSig E σ)‖ ≤ t :=
    norm_ofReal_mul_le_self hξ.le h0
  have hζ1 : ‖(t : ℂ) * (KLoop.mSig E σ * KLoop.mSig E σ)‖ < 1 := lt_of_le_of_lt hζt ht
  set ζ : ℂ := (t : ℂ) * (KLoop.mSig E σ * KLoop.mSig E σ) with hζ
  set c : ℝ := KLoop.gapK κ with hc
  have hcpos : 0 < c := gapK_pos hκ hκ2
  have hc1 : c ≤ 1 := gapK_le_one κ
  have hgap : c ≤ ‖(1 : ℂ) - ζ‖ := gapK_le_norm hκ hE h0 σ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL9 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  -- scales at `ζ`
  have hsqc : Real.sqrt c ≤ kappa ζ := by
    unfold kappa
    exact Real.sqrt_le_sqrt hgap
  have hsqcpos : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hℓle : ellhat L ζ ≤ 1 / Real.sqrt c := by
    calc ellhat L ζ ≤ (kappa ζ)⁻¹ := min_le_left _ _
      _ ≤ (Real.sqrt c)⁻¹ := inv_anti₀ hsqcpos hsqc
      _ = 1 / Real.sqrt c := (one_div _).symm
  have hℓpos : 0 < ellhat L ζ := ellhat_pos L hL hζ1
  have hden : c ≤ kappa ζ ^ 2 * ellhat L ζ ^ 2 :=
    (le_min hc1 (by nlinarith)).trans (min_le_kappa_sq_ellhat_sq L hζ1 hgap)
  have hden' : (kappa ζ ^ 2 * ellhat L ζ ^ 2)⁻¹ ≤ c⁻¹ := inv_anti₀ hcpos hden
  have hc5 : 0 ≤ cProp5 := by unfold cProp5; norm_num
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_natCast_nonneg L]
  have hK : 0 ≤ cProp5 * (1 + Real.log L) := mul_nonneg hc5 hlog
  -- the row bound of `Θ_ζ`
  have hs0 : 0 < 1 / (20000 * ellhat L ζ) := by positivity
  have hR : ∀ x : Z2 L, ∑ b : Z2 L, ‖Theta L ζ x b‖ ≤
      cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 := by
    intro x
    have hexpsum : ∑ b : Z2 L, Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ζ)) ≤
        (1 + 40000 / Real.sqrt c) ^ 2 := by
      have h := KLoop.sum_exp_le L (1 / (20000 * ellhat L ζ)) hs0 x
      have hre : ∀ b : Z2 L, -(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ζ) =
          -((1 / (20000 * ellhat L ζ)) * (zdist2 L (x - b) : ℝ)) := fun b => by ring
      simp only [hre]
      refine h.trans ?_
      have h2 : 2 / (1 / (20000 * ellhat L ζ)) = 40000 * ellhat L ζ := by
        field_simp; ring
      rw [h2]
      have h3 : 40000 * ellhat L ζ ≤ 40000 / Real.sqrt c := by
        calc 40000 * ellhat L ζ ≤ 40000 * (1 / Real.sqrt c) :=
              mul_le_mul_of_nonneg_left hℓle (by norm_num)
          _ = 40000 / Real.sqrt c := by ring
      have h4 : 0 ≤ 1 + 40000 * ellhat L ζ := by positivity
      exact pow_le_pow_left₀ h4 (by linarith) 2
    calc ∑ b : Z2 L, ‖Theta L ζ x b‖
        ≤ ∑ b : Z2 L, cProp5 * (1 + Real.log L) * c⁻¹ *
            Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ζ)) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h5 : ‖Theta L ζ x b‖ ≤ cProp5 * (1 + Real.log L) *
              (kappa ζ ^ 2 * ellhat L ζ ^ 2)⁻¹ *
                Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ζ)) :=
            norm_Theta_apply_le_prop5 L hL ζ hζ1 x b
          exact h5.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden' hK)
            (Real.exp_pos _).le)
      _ = cProp5 * (1 + Real.log L) * c⁻¹ *
            ∑ b : Z2 L, Real.exp (-(zdist2 L (x - b) : ℝ) / (20000 * ellhat L ζ)) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 :=
          mul_le_mul_of_nonneg_left hexpsum (mul_nonneg hK (inv_nonneg.2 hcpos.le))
  have hrow := sum_norm_xiMat_le L hL hξ.le hs hst ht a hR
  have hP : 0 ≤ cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 := by
    have := mul_nonneg hK (inv_nonneg.2 hcpos.le)
    positivity
  have hts : t - s ≤ 1 := by linarith
  calc ∑ b : Z2 L, ‖xiMat L (KLoop.mSig E σ * KLoop.mSig E σ) s t a b‖
      ≤ (t - s) * (cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2) := hrow
    _ ≤ 1 * (cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2) :=
        mul_le_mul_of_nonneg_right hts hP
    _ ≤ cShortRow κ * (1 + Real.log L) := by
        unfold cShortRow
        rw [← hc]
        have : 0 ≤ cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2 := hP
        calc 1 * (cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2)
            ≤ 2 * (cProp5 * (1 + Real.log L) * c⁻¹ * (1 + 40000 / Real.sqrt c) ^ 2) := by
              linarith
          _ = 2 * cProp5 / c * (1 + 40000 / Real.sqrt c) ^ 2 * (1 + Real.log L) := by ring

/-- **K1d**: the first difference `Xi-bound-1` at `ξ = 1`. -/
theorem xiFirstDiff : XiFirstDiff := by
  intro L _ hL s t hs hst ht a b r
  have h0 : 0 ≤ t := hs.trans hst
  have htc : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg h0]; exact ht
  have hell : ellhat L (t : ℂ) = ellT L t := ellhat_ofReal L ht.le
  have hkap : kappa (t : ℂ) = Real.sqrt (1 - t) := kappa_ofReal ht.le
  have hP : 0 ≤ derivativePrefactor (10 ^ 14) L := by
    unfold derivativePrefactor
    linarith [Real.log_natCast_nonneg L]
  have hR0 : (0 : ℝ) ≤ (zdist2 L r : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ := by positivity
  have hterm : ∀ x : Z2 L, ‖SB L a x‖ * ‖Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r)‖ ≤
      ‖SB L a x‖ * (2 * derivativePrefactor (10 ^ 14) L *
        ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
          (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2))) := by
    intro x
    by_cases hx : ‖SB L a x‖ = 0
    · simp [hx]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h6 := (norm_Theta_fd_prop6 L hL (t : ℂ) htc x b r).1
      rw [hell, hkap] at h6
      have h2 := zdist2_le_of_norm_SB_ne L hL hx b
      have hA : 0 ≤ (zdist2 L (a - b) : ℝ) := Nat.cast_nonneg _
      have hB : 0 ≤ (zdist2 L (x - b) : ℝ) := Nat.cast_nonneg _
      have hinv : ((zdist2 L (x - b) : ℝ) + 1)⁻¹ ≤ 2 * ((zdist2 L (a - b) : ℝ) + 1)⁻¹ := by
        have h3 : ((zdist2 L (a - b) : ℝ) + 1) ≤ 2 * ((zdist2 L (x - b) : ℝ) + 1) := by linarith
        have h4 : (2 * ((zdist2 L (x - b) : ℝ) + 1))⁻¹ ≤ ((zdist2 L (a - b) : ℝ) + 1)⁻¹ :=
          inv_anti₀ (by positivity) h3
        calc ((zdist2 L (x - b) : ℝ) + 1)⁻¹ = 2 * (2 * ((zdist2 L (x - b) : ℝ) + 1))⁻¹ := by
              field_simp
          _ ≤ 2 * ((zdist2 L (a - b) : ℝ) + 1)⁻¹ := by linarith
      have hJ : 0 ≤ (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ := hG
      have hI : 0 ≤ ((zdist2 L (a - b) : ℝ) + 1)⁻¹ := by positivity
      calc ‖Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r)‖
          ≤ derivativePrefactor (10 ^ 14) L *
            ((zdist2 L r : ℝ) * ((zdist2 L (x - b) : ℝ) + 1)⁻¹ +
              (zdist2 L r : ℝ) * (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹) := h6
        _ ≤ derivativePrefactor (10 ^ 14) L *
            ((zdist2 L r : ℝ) * (2 * ((zdist2 L (a - b) : ℝ) + 1)⁻¹) +
              (zdist2 L r : ℝ) * (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ hP
            have := mul_le_mul_of_nonneg_left hinv hR0
            linarith
        _ ≤ 2 * derivativePrefactor (10 ^14) L *
            ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
              (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            have : 0 ≤ derivativePrefactor (10 ^ 14) L * (zdist2 L r : ℝ) *
                (Real.sqrt (1 - t) * ellT L t ^ 2)⁻¹ := by positivity
            nlinarith
  calc ‖xiMat L 1 s t a b - xiMat L 1 s t a (b + r)‖
      ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * ‖Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r)‖ :=
        norm_xiMat_diff1_le L hL hs hst ht a b (b + r)
    _ ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * (2 * derivativePrefactor (10 ^ 14) L *
          ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
            (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) (by linarith)
    _ = (t - s) * (2 * derivativePrefactor (10 ^ 14) L *
          ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
            (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2))) := by
        rw [← Finset.sum_mul, sum_norm_SB_row L hL, one_mul]
    _ = 2 * derivativePrefactor (10 ^ 14) L * (t - s) *
          ((zdist2 L r : ℝ) / ((zdist2 L (a - b) : ℝ) + 1) +
            (zdist2 L r : ℝ) / (Real.sqrt (1 - t) * ellT L t ^ 2)) := by ring

/-- **K1e**: the second difference `Xi-bound-2` at `ξ = 1`. -/
theorem xiSecondDiff : XiSecondDiff := by
  intro L _ hL s t hs hst ht a b r
  have h0 : 0 ≤ t := hs.trans hst
  have htc : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg h0]; exact ht
  have hell : ellhat L (t : ℂ) = ellT L t := ellhat_ofReal L ht.le
  have hP : 0 ≤ derivativePrefactor (10 ^ 14) L := by
    unfold derivativePrefactor
    linarith [Real.log_natCast_nonneg L]
  have hR0 : (0 : ℝ) ≤ (zdist2 L r : ℝ) ^ 2 := sq_nonneg _
  have hterm : ∀ x : Z2 L, ‖SB L a x‖ *
      ‖2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r) - Theta L (t : ℂ) x (b - r)‖ ≤
      ‖SB L a x‖ * (4 * derivativePrefactor (10 ^ 14) L *
        ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
          (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2)) := by
    intro x
    by_cases hx : ‖SB L a x‖ = 0
    · simp [hx]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h6 := (norm_Theta_fd_prop6 L hL (t : ℂ) htc x b r).2
      rw [hell] at h6
      have h2 := zdist2_le_of_norm_SB_ne L hL hx b
      have hA : 0 ≤ (zdist2 L (a - b) : ℝ) := Nat.cast_nonneg _
      have hB : 0 ≤ (zdist2 L (x - b) : ℝ) := Nat.cast_nonneg _
      have hinv : ((zdist2 L (x - b) : ℝ) ^ 2 + 1)⁻¹ ≤ 4 * ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹ := by
        have h3 : ((zdist2 L (a - b) : ℝ) ^ 2 + 1) ≤ 4 * ((zdist2 L (x - b) : ℝ) ^ 2 + 1) := by
          nlinarith [mul_self_nonneg ((zdist2 L (x - b) : ℝ) - 1 / 3)]
        have h4 : (4 * ((zdist2 L (x - b) : ℝ) ^ 2 + 1))⁻¹ ≤ ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹ :=
          inv_anti₀ (by positivity) h3
        calc ((zdist2 L (x - b) : ℝ) ^ 2 + 1)⁻¹
            = 4 * (4 * ((zdist2 L (x - b) : ℝ) ^ 2 + 1))⁻¹ := by field_simp
          _ ≤ 4 * ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹ := by linarith
      have hJ : 0 ≤ (ellT L t ^ 2)⁻¹ := by positivity
      calc ‖2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r) - Theta L (t : ℂ) x (b - r)‖
          ≤ derivativePrefactor (10 ^ 14) L *
            ((zdist2 L r : ℝ) ^ 2 * ((zdist2 L (x - b) : ℝ) ^ 2 + 1)⁻¹ +
              (zdist2 L r : ℝ) ^ 2 * (ellT L t ^ 2)⁻¹) := h6
        _ ≤ derivativePrefactor (10 ^ 14) L *
            ((zdist2 L r : ℝ) ^ 2 * (4 * ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹) +
              (zdist2 L r : ℝ) ^ 2 * (ellT L t ^ 2)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ hP
            have := mul_le_mul_of_nonneg_left hinv hR0
            linarith
        _ ≤ 4 * derivativePrefactor (10 ^ 14) L *
            ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
              (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            have : 0 ≤ derivativePrefactor (10 ^ 14) L * (zdist2 L r : ℝ) ^ 2 *
                (ellT L t ^ 2)⁻¹ := by positivity
            nlinarith
  calc ‖2 * xiMat L 1 s t a b - xiMat L 1 s t a (b + r) - xiMat L 1 s t a (b - r)‖
      ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ *
          ‖2 * Theta L (t : ℂ) x b - Theta L (t : ℂ) x (b + r) - Theta L (t : ℂ) x (b - r)‖ :=
        norm_xiMat_diff2_le L hL hs hst ht a b (b + r) (b - r)
    _ ≤ (t - s) * ∑ x : Z2 L, ‖SB L a x‖ * (4 * derivativePrefactor (10 ^ 14) L *
          ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
            (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) (by linarith)
    _ = (t - s) * (4 * derivativePrefactor (10 ^ 14) L *
          ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
            (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2)) := by
        rw [← Finset.sum_mul, sum_norm_SB_row L hL, one_mul]
    _ = 4 * derivativePrefactor (10 ^ 14) L * (t - s) *
          ((zdist2 L r : ℝ) ^ 2 / ((zdist2 L (a - b) : ℝ) ^ 2 + 1) +
            (zdist2 L r : ℝ) ^ 2 / ellT L t ^ 2) := by ring

end Theorems


end RBM.Evol
