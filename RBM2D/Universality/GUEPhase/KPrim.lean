/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Bootstrap
import RBM2D.Universality.ZeroModeProfile
import RBM2D.Loop.Kcal
import RBM2D.Defs.Semicircle
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The 2-loop primitive of the GUE phase and the primitive loops `K̃` (§7.2 of [YY_25], `d = 2`)

* `gueShift`, `kTwoGUE`, `kTwoGUELoop`: the zero-mode coefficient `β(t)` and the 2-loop primitive
  `K_{t,σ,(a,b)} = W⁻² μ (Θ_{t₁μ} + β(t) J)_{ab}`, `μ = m(σ₁) m(σ₂)`, of the GUE phase on
  `[t₁, t₀]`, started from (2.57) at `t₁` (`kTwoGUE_self`), equal to `W⁻² μ Θ̃_{t₀ μ}` at `t₀`
  for `t₁ = (1 - ζ) t₀` ((7.25), `kTwoGUE_eq_ThetaTilde`), and solving (7.33) at `n = 2`
  (`hasDerivAt_kTwoGUELoop`).
* `primRhsGUE_two`, `kTwoGUE_deriv_identity`, `hasDerivAt_kTwoGUE`: the pieces of
  `hasDerivAt_kTwoGUELoop` (the right side of (7.33) at `n = 2`, the scalar identity, and the
  derivative of `kTwoGUE` in `t`; row and column sums of `Θ_{t₁μ}` are `(1 - t₁μ)⁻¹`).
* `gueK_exists`: the primitive loops of the GUE phase exist on `[t₁, t₀]` for every length
  `≤ n₀`, start from `Kgen` at `t₁`, and their 2-loops are `kTwoGUE`.  Induction on the length:
  for each `n ≥ 2` the loops of length `n + 1` solve an ODE on the finite-dimensional space of
  functions on the slice `{WF, length = n + 1}`.  The cut-and-glue lengths of a loop of length
  `n + 1` add up to `n + 3` and each is `≥ 2`, so for `n ≥ 2` at most one of the two factors
  has length `n + 1` (and then the other has length `2 ≤ n`): the right side is affine in the
  unknowns with coefficients from the shorter loops, hence globally Lipschitz.  Global existence
  is the Mathlib Picard-Lindelöf theorem chained in short steps of length `1/(2(C+1))`.
* `lemT_mul_kTwoGUE_pm`, `lemT_mul_kTwoGUE_pp`: `t K` at the spectral parameter of Lemma 2.8
  (the main terms of (7.47)).

Conventions.  The lattice is `Z2 L`; the prefactor is `(W²)⁻¹` in `kTwoGUE` and `W²` in the
derivative; `L²` appears in `gueShift` and in every row sum `∑_b J_{ab}`; `SBgue = 1/L²`; the
zero-time data are `KLoop.mSig` and `KLoop.Kgen L W (KLoop.mSig E)`; `ThetaTilde_eq` has the
hypotheses `3 ≤ L`, `‖ξ‖ < 1`, `0 ≤ ζ ≤ 1`.

The equation numbers (2.55), (2.57), (7.25), (7.33), (7.47) in the docstrings are those of [YY_25].
The `d = 2` paper has no GUE-phase section (`GUE` does not occur in its sections 3–8); there
(2.57) is the label `(Kn2sol)` (`KLoop.kTwo`) and (2.55) is `(pro_dyncalK)` (`KLoop.primRhs`).

Helpers are `private` or carry the prefix `KPrim_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

/-! ### The 2-loop primitive of the GUE phase and the zero mode (7.25) -/

section TwoLoop

/-- The zero-mode coefficient `β(t) = (t - t₁) μ / (L² (1 - t₁ μ)(1 - t μ))`. -/
def gueShift (L : ℕ) (μ : ℂ) (t1 t : ℝ) : ℂ :=
  ((t : ℂ) - t1) * μ / ((L : ℂ) ^ 2 * (1 - (t1 : ℂ) * μ) * (1 - (t : ℂ) * μ))

/-- **The 2-loop primitive of the GUE phase** (the solution of (7.33) for `n = 2` on `[t₁, t₀]`
started from (2.57) at `t₁`): `K_{t,σ,(a,b)} = W⁻² μ (Θ_{t₁μ} + β(t) J)_{ab}`,
`μ = m(σ₁) m(σ₂)`.  By Sherman–Morrison (`ThetaTilde_eq`) this is
`W⁻² μ [(1 - t₁μ S^{(B)} - (t-t₁)μ S^{(B)}_{GUE})⁻¹]_{ab}` (`kTwoGUE_eq_ThetaTilde`). -/
def kTwoGUE (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : Z2 L) : ℂ :=
  ((W : ℂ) ^ 2)⁻¹ * (m σ₁ * m σ₂) *
    (Theta L ((t1 : ℂ) * (m σ₁ * m σ₂)) a b + gueShift L (m σ₁ * m σ₂) t1 t)

/-- `kTwoGUE` on loop indices (`0` off the 2-loops): (7.33) at `n = 2` in cut-and-glue form is
`hasDerivAt_kTwoGUELoop`. -/
def kTwoGUELoop (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) (t1 t : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwoGUE L W m t1 t σ₁ σ₂ a₁ a₂
  | _, _ => 0

/-- At `t = t₁` the GUE-phase 2-loop primitive is the standard one (2.57): `K` is continuous across
the switch of the flow at `t₁`. -/
theorem kTwoGUE_self (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool)
    (a b : Z2 L) :
    kTwoGUE L W m t1 t1 σ₁ σ₂ a b = KLoop.kTwo L W m t1 σ₁ σ₂ a b := by
  simp [kTwoGUE, gueShift, KLoop.kTwo]

/-- **(7.25) and the zero mode**: at `t₀`, with `t₁ = (1 - ζ_U) t₀`, the 2-loop primitive of the
GUE phase is `W⁻² μ ((1 - ξ S̃^{(B)})⁻¹)_{ab}`, `ξ = t₀ μ`, `S̃^{(B)} = (1 - ζ_U) S^{(B)} +
ζ_U/L² J`.  The hypotheses are those of the `ThetaTilde_eq`. -/
theorem kTwoGUE_eq_ThetaTilde (L : ℕ) [NeZero L] (W : ℕ) (hL : 3 ≤ L) (m : Bool → ℂ)
    {ζ t0 : ℝ} (σ₁ σ₂ : Bool) (hT : ‖(t0 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1)
    (a b : Z2 L) :
    kTwoGUE L W m ((1 - ζ) * t0) t0 σ₁ σ₂ a b
      = ((W : ℂ) ^ 2)⁻¹ * (m σ₁ * m σ₂) * ThetaTilde L ζ ((t0 : ℂ) * (m σ₁ * m σ₂)) a b := by
  rw [ThetaTilde_eq L hL hT h0 h1]
  simp only [kTwoGUE, gueShift, Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply,
    smul_eq_mul, mul_one]
  have e1 : (((1 - ζ) * t0 : ℝ) : ℂ) * (m σ₁ * m σ₂)
      = (t0 : ℂ) * (m σ₁ * m σ₂) * (1 - (ζ : ℂ)) := by
    push_cast; ring
  rw [e1]
  congr 2
  push_cast
  ring

/-- The right side of (7.33) at `n = 2`, written without the cut-and-glue operators:
`W² ∑_{a,b} K_{σ,(a₁,a)} (S^{(B)}_{GUE})_{ab} K_{σ,(b,a₂)}` (as `primRhs_two` for (2.55)). -/
theorem primRhsGUE_two (L W : ℕ) [NeZero L] (K : LoopIdx (Z2 L) → ℂ) (σ₁ σ₂ : Bool)
    (a₁ a₂ : Z2 L) :
    primRhsGUE L W K ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
          K ⟨[σ₁, σ₂], [a₁, a]⟩ * SBgue L a b * K ⟨[σ₁, σ₂], [b, a₂]⟩ := by
  have h12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h1 : Finset.Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have h2 : Finset.Ioc 2 2 = (∅ : Finset ℕ) := by decide
  have hlen : (LoopIdx.mk [σ₁, σ₂] [a₁, a₂]).length = 2 := rfl
  rw [primRhsGUE, primBilGUE, hlen, h12, Finset.sum_pair (by norm_num), h1, h2,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change K ⟨[σ₁, σ₂], [b, a₂]⟩ * SBgue L b a * K ⟨[σ₁, σ₂], [a₁, a]⟩ = _
  simp only [SBgue_apply]
  ring

/-- The scalar identity behind `hasDerivAt_kTwoGUE`: with `q + dμ = p`
(`p = 1 - t₁μ`, `q = 1 - tμ`, `d = t - t₁`), the derivative of `W⁻² μ dμ/(L² p q)` equals
`W⁻² μ² L⁻² (p⁻¹ + L² dμ/(L² p q))²`; both are `W⁻² μ² / (L² q²)`. -/
theorem kTwoGUE_deriv_identity (W μ p q d L : ℂ) (h : q + d * μ = p) (hp : p ≠ 0) (hq : q ≠ 0)
    (hL : L ≠ 0) :
    (W ^ 2)⁻¹ * μ * ((μ * (L ^ 2 * p * q) - d * μ * (L ^ 2 * p * -μ)) / (L ^ 2 * p * q) ^ 2)
      = (W ^ 2)⁻¹ * μ ^ 2 * (L ^ 2)⁻¹ *
        ((p⁻¹ + L ^ 2 * (d * μ / (L ^ 2 * p * q))) * (p⁻¹ + L ^ 2 * (d * μ / (L ^ 2 * p * q)))) := by
  have e1 : μ * (L ^ 2 * p * q) - d * μ * (L ^ 2 * p * -μ) = μ * L ^ 2 * p * p := by
    rw [← h]; ring
  have e2 : p⁻¹ + L ^ 2 * (d * μ / (L ^ 2 * p * q)) = q⁻¹ := by
    have : L ^ 2 * (d * μ / (L ^ 2 * p * q)) = d * μ / (p * q) := by field_simp
    rw [this, inv_eq_one_div, inv_eq_one_div, div_add_div _ _ hp (mul_ne_zero hp hq),
      div_eq_div_iff (mul_ne_zero hp (mul_ne_zero hp hq)) hq, ← h]
    ring
  rw [e1, e2]
  field_simp

/-- **(7.33) at `n = 2`**: the closed form `kTwoGUE` solves the primitive equation of the GUE
phase, `d/dt K_{t,σ,(a₁,a₂)} = W² ∑_{a,b} K_{t,σ,(a₁,a)} (S^{(B)}_{GUE})_{ab} K_{t,σ,(b,a₂)}`, as
long as `|t₁ μ| < 1` and `t μ ≠ 1`.  (Together with `kTwoGUE_self`, uniqueness for this ODE
identifies `kTwoGUE` with the primitive 2-loop on `[t₁, t₀]`; uniqueness is not stated here.) -/
theorem hasDerivAt_kTwoGUE (L W : ℕ) [NeZero L] (hL : 3 ≤ L) [NeZero W] (m : Bool → ℂ)
    {t1 t : ℝ} (σ₁ σ₂ : Bool) (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1)
    (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1) (a₁ a₂ : Z2 L) :
    HasDerivAt (fun s => kTwoGUE L W m t1 s σ₁ σ₂ a₁ a₂)
      ((W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        kTwoGUE L W m t1 t σ₁ σ₂ a₁ a * SBgue L a b * kTwoGUE L W m t1 t σ₁ σ₂ b a₂) t := by
  set μ := m σ₁ * m σ₂ with hμ
  set p : ℂ := 1 - (t1 : ℂ) * μ with hp
  have hp0 : p ≠ 0 := by
    intro h
    have : (t1 : ℂ) * μ = 1 := by rw [hp] at h; linear_combination -h
    rw [this, norm_one] at h1
    exact lt_irrefl _ h1
  have hq0 : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have hL20 : (L : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hL0
  -- the complex function
  set Θab := Theta L ((t1 : ℂ) * μ) a₁ a₂ with hΘab
  have hf : HasDerivAt (fun w : ℂ => (w - t1) * μ) μ (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).sub_const (t1 : ℂ)).mul_const μ
  have hg : HasDerivAt (fun w : ℂ => (L : ℂ) ^ 2 * p * (1 - w * μ)) ((L : ℂ) ^ 2 * p * -μ)
      (t : ℂ) := by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const μ).const_sub 1).const_mul ((L : ℂ) ^ 2 * p)
  have hgt : (L : ℂ) ^ 2 * p * (1 - (t : ℂ) * μ) ≠ 0 := mul_ne_zero (mul_ne_zero hL20 hp0) hq0
  have hdiv := hf.div hg hgt
  have hG := ((hdiv.const_add Θab).const_mul (((W : ℂ) ^ 2)⁻¹ * μ)).comp_ofReal
  refine hG.congr_deriv ?_
  -- evaluate the right side
  have hrow : ∀ a : Z2 L, ∑ b : Z2 L, Theta L ((t1 : ℂ) * μ) a b = p⁻¹ :=
    fun a => sum_Theta_row L hL h1 a
  have hcol : ∀ b : Z2 L, ∑ a : Z2 L, Theta L ((t1 : ℂ) * μ) a b = p⁻¹ := by
    intro b
    have hT := Theta_transpose L hL h1
    rw [← hrow b]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := congrFun (congrFun hT b) a
    simpa [Matrix.transpose_apply] using this
  set β := gueShift L μ t1 t with hβ
  have hsum : (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
      kTwoGUE L W m t1 t σ₁ σ₂ a₁ a * SBgue L a b * kTwoGUE L W m t1 t σ₁ σ₂ b a₂
      = ((W : ℂ) ^ 2)⁻¹ * μ ^ 2 * ((L : ℂ) ^ 2)⁻¹ * ((p⁻¹ + (L : ℂ) ^ 2 * β) * (p⁻¹ + (L : ℂ) ^ 2 * β)) := by
    simp only [kTwoGUE, ← hμ, ← hβ, SBgue_apply]
    have e : ∀ a b : Z2 L, ((W : ℂ) ^ 2)⁻¹ * μ * (Theta L ((t1 : ℂ) * μ) a₁ a + β) * ((L : ℂ) ^ 2)⁻¹ *
        (((W : ℂ) ^ 2)⁻¹ * μ * (Theta L ((t1 : ℂ) * μ) b a₂ + β))
        = (((W : ℂ) ^ 2)⁻¹ * μ) ^ 2 * ((L : ℂ) ^ 2)⁻¹ *
          ((Theta L ((t1 : ℂ) * μ) a₁ a + β) * (Theta L ((t1 : ℂ) * μ) b a₂ + β)) := by
      intro a b; ring
    simp only [e, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, hrow, hcol, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, ZMod.card, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hsum, hβ, gueShift]
  exact kTwoGUE_deriv_identity _ μ p _ _ _ (by rw [hp]; ring) hp0 hq0 hL0

/-- (7.33) at `n = 2` in cut-and-glue form: `kTwoGUE`, as a function of the loop index, satisfies
`d/dt K_{t,I} = primRhsGUE (K_t) I` for every 2-loop `I`. -/
theorem hasDerivAt_kTwoGUELoop (L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (hL : 3 ≤ L)
    (m : Bool → ℂ) {t1 t : ℝ} (σ₁ σ₂ : Bool) (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1)
    (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1) (a₁ a₂ : Z2 L) :
    HasDerivAt (fun s => kTwoGUELoop L W m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (primRhsGUE L W (kTwoGUELoop L W m t1 t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  rw [primRhsGUE_two]
  exact hasDerivAt_kTwoGUE L W hL m σ₁ σ₂ h1 h2 a₁ a₂

end TwoLoop

/-! ### `t K` at the spectral parameter of Lemma 2.8 (the main terms of (7.47)) -/

section LemT

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2` (`KLoop.norm_mSig` is private). -/
private theorem KPrim_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, RBM.Gauss.norm_spectralM hE]

/-- `m(+) m(−) = |m|² = 1`. -/
private theorem KPrim_mSig_true_mul_false {E : ℝ} (hE : |E| ≤ 2) :
    KLoop.mSig E true * KLoop.mSig E false = 1 := by
  have h := RBM.Gauss.norm_spectralM hE
  simp only [KLoop.mSig, ite_true, Bool.false_eq_true, ite_false]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

private theorem KPrim_lemT_pos {z : ℂ} (hz : 0 < z.im) : 0 < lemT z := by
  have him := msc_im_pos hz
  have h0 : msc z ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  have := norm_pos_iff.2 h0
  unfold lemT
  positivity

private theorem KPrim_lemT_lt_one {z : ℂ} (hz : 0 < z.im) : lemT z < 1 := by
  have h := norm_msc_lt_one hz
  have := norm_nonneg (msc z)
  unfold lemT
  nlinarith

private theorem KPrim_abs_lemE_lt_two {z : ℂ} (hz : 0 < z.im) : |lemE z| < 2 := by
  have him := msc_im_pos hz
  have hr : 0 < ‖msc z‖ := norm_pos_iff.2 fun h => by
    rw [h, Complex.zero_im] at him
    exact lt_irrefl _ him
  have hr2 : ‖msc z‖ ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : |(msc z).re| < ‖msc z‖ := abs_lt_of_sq_lt_sq (by nlinarith) hr.le
  rw [lemE, abs_div, abs_of_pos hr, div_lt_iff₀ hr, abs_mul]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith

/-- `t K_{t,(+,-),(a,b)}` of the GUE phase at the spectral parameter of Lemma 2.8
(`t₀ = |m_sc(z)|²`, `t₁ = (1 - ζ) t₀`): `W⁻² |m_sc|² ((1 - |m_sc|² S̃^{(B)})⁻¹)_{ab}`, the main
term of the first line of (7.47). -/
theorem lemT_mul_kTwoGUE_pm (L W : ℕ) [NeZero L] (hL : 3 ≤ L) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ}
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Z2 L) :
    (lemT z : ℂ) * kTwoGUE L W (KLoop.mSig (lemE z)) ((1 - ζ) * lemT z) (lemT z) true false a b =
      ((W : ℂ) ^ 2)⁻¹ * ((‖msc z‖ ^ 2 : ℝ) : ℂ) * ThetaTilde L ζ ((‖msc z‖ ^ 2 : ℝ) : ℂ) a b := by
  have hμ : KLoop.mSig (lemE z) true * KLoop.mSig (lemE z) false = 1 :=
    KPrim_mSig_true_mul_false (KPrim_abs_lemE_lt_two hz).le
  have ht0 := KPrim_lemT_pos hz
  have ht1 := KPrim_lemT_lt_one hz
  have hT : ‖(lemT z : ℂ) * (KLoop.mSig (lemE z) true * KLoop.mSig (lemE z) false)‖ < 1 := by
    rw [hμ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  rw [kTwoGUE_eq_ThetaTilde L W hL _ true false hT hζ0 hζ1, hμ]
  simp only [mul_one, lemT]
  ring

/-- `t K_{t,(+,+),(a,b)}` of the GUE phase at the spectral parameter of Lemma 2.8:
`W⁻² m_sc² ((1 - m_sc² S̃^{(B)})⁻¹)_{ab}`, the main term of the second line of (7.47). -/
theorem lemT_mul_kTwoGUE_pp (L W : ℕ) [NeZero L] (hL : 3 ≤ L) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ}
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Z2 L) :
    (lemT z : ℂ) * kTwoGUE L W (KLoop.mSig (lemE z)) ((1 - ζ) * lemT z) (lemT z) true true a b =
      ((W : ℂ) ^ 2)⁻¹ * msc z ^ 2 * ThetaTilde L ζ (msc z ^ 2) a b := by
  have ht0 := KPrim_lemT_pos hz
  have ht1 := KPrim_lemT_lt_one hz
  have hE := (KPrim_abs_lemE_lt_two hz).le
  have h : msc z ^ 2 = (lemT z : ℂ) * (KLoop.mSig (lemE z) true * KLoop.mSig (lemE z) true) := by
    rw [msc_eq_sqrt_mul_spectralM hz, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt ht0.le]
    simp only [KLoop.mSig, ite_true]
    ring
  have hnorm : ‖(lemT z : ℂ) * (KLoop.mSig (lemE z) true * KLoop.mSig (lemE z) true)‖
      = lemT z := by
    rw [norm_mul, norm_mul, KPrim_norm_mSig hE, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    ring
  have hT : ‖(lemT z : ℂ) * (KLoop.mSig (lemE z) true * KLoop.mSig (lemE z) true)‖ < 1 := by
    rw [hnorm]
    exact ht1
  rw [kTwoGUE_eq_ThetaTilde L W hL _ true true hT hζ0 hζ1, h]
  ring

end LemT

/-! ### Global existence for a globally Lipschitz ODE on a compact interval -/

section KPrimODE

open Metric Set
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Local step** (Picard–Lindelöf on one short interval).  For a vector field that is
`K`-Lipschitz in space uniformly on `[t₁, t₀]`, with `‖f t 0‖ ≤ B`, and a step `h` with
`K h ≤ 1/2`, a solution exists on `[s, s']` from any initial value `x` whenever
`t₁ ≤ s ≤ s' ≤ min (s + h) t₀`: the ball radius `a = 2 (B + K‖x‖) h` satisfies the confining
inequality `(B + K(‖x‖ + a)) h ≤ a`. -/
private theorem KPrim_ode_step (f : ℝ → V → V) {t1 t0 : ℝ} (K : ℝ≥0) (B h : ℝ)
    (hB0 : 0 ≤ B) (hh : 0 ≤ h) (hKh : (K : ℝ) * h ≤ 1 / 2)
    (hlip : ∀ t ∈ Icc t1 t0, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (f · x) (Icc t1 t0))
    (hB : ∀ t ∈ Icc t1 t0, ‖f t 0‖ ≤ B)
    {s s' : ℝ} (hs : t1 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ t0) (hsh : s' ≤ s + h) (x : V) :
    ∃ β : ℝ → V, β s = x ∧ ∀ t ∈ Icc s s', HasDerivWithinAt β (f t (β t)) (Icc s s') t := by
  have hsub : Icc s s' ⊆ Icc t1 t0 := Icc_subset_Icc hs hs'
  set a : ℝ := 2 * (B + K * ‖x‖) * h with ha
  have ha0 : 0 ≤ a := by positivity
  set Lb : ℝ := B + K * (‖x‖ + a) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  set aN : ℝ≥0 := ⟨a, ha0⟩ with haN
  set LN : ℝ≥0 := ⟨Lb, hLb0⟩ with hLN
  have haN' : (aN : ℝ) = a := rfl
  have hLN' : (LN : ℝ) = Lb := rfl
  have hP : IsPicardLindelof f (⟨s, ⟨le_rfl, hss'⟩⟩ : Icc s s') x aN 0 LN K := by
    refine ⟨fun t ht => (hlip t (hsub ht)).lipschitzOnWith, fun y _ => (hcont y).mono hsub,
      fun t ht y hy => ?_, ?_⟩
    · have hy' : ‖y‖ ≤ ‖x‖ + a := by
        have := mem_closedBall.1 hy
        rw [dist_eq_norm] at this
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + a := by rw [haN'] at this; linarith
      have hl := (hlip t (hsub ht)).dist_le_mul y 0
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at hl
      have h1 : ‖f t y‖ ≤ ‖f t 0‖ + K * ‖y‖ := by
        calc ‖f t y‖ = ‖(f t y - f t 0) + f t 0‖ := by rw [sub_add_cancel]
          _ ≤ ‖f t y - f t 0‖ + ‖f t 0‖ := norm_add_le _ _
          _ ≤ K * ‖y‖ + ‖f t 0‖ := by linarith
          _ = ‖f t 0‖ + K * ‖y‖ := by ring
      rw [hLN']
      have := hB t (hsub ht)
      have hK0 : (0 : ℝ) ≤ K := K.2
      nlinarith
    · simp only [haN', hLN', NNReal.coe_zero, sub_zero, sub_self]
      have hmax : max (s' - s) 0 ≤ h := max_le (by linarith) hh
      have hK0 : (0 : ℝ) ≤ K := K.2
      calc Lb * max (s' - s) 0 ≤ Lb * h := mul_le_mul_of_nonneg_left hmax hLb0
        _ = (B + K * ‖x‖) * h + a * (K * h) := by rw [hLb]; ring
        _ ≤ (B + K * ‖x‖) * h + a * (1 / 2) := by gcongr
        _ = a := by rw [ha]; ring
  obtain ⟨β, hβ0, hβ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, hβ⟩

omit [CompleteSpace V] in
/-- **Gluing**: solutions on `[t₁, s]` and `[s, s']` agreeing at `s` give a solution on
`[t₁, s']` (`HasDerivWithinAt.union`). -/
private theorem KPrim_ode_glue (f : ℝ → V → V) {t1 s s' : ℝ} (h1 : t1 ≤ s) (h2 : s ≤ s')
    (α β : ℝ → V) (hα : ∀ t ∈ Icc t1 s, HasDerivWithinAt α (f t (α t)) (Icc t1 s) t)
    (hβ : ∀ t ∈ Icc s s', HasDerivWithinAt β (f t (β t)) (Icc s s') t) (hαβ : β s = α s) :
    ∀ t ∈ Icc t1 s', HasDerivWithinAt (fun u => if u ≤ s then α u else β u)
      (f t (if t ≤ s then α t else β t)) (Icc t1 s') t := by
  intro t ht
  rw [← Icc_union_Icc_eq_Icc h1 h2]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases hts : t ≤ s
    · rw [ite_eq_left hts]
      exact (hα t ⟨ht.1, hts⟩).congr_of_mem (fun u hu => ite_eq_left hu.2) ⟨ht.1, hts⟩
    · have : t ∉ closure (Icc t1 s) := by rw [closure_Icc]; exact fun h => hts h.2
      exact HasFDerivWithinAt.of_notMem_closure this
  · by_cases hts : s ≤ t
    · have hγ : (if t ≤ s then α t else β t) = β t := by
        split_ifs with h
        · have : t = s := le_antisymm h hts
          subst this; exact hαβ.symm
        · rfl
      rw [hγ]
      refine (hβ t ⟨hts, ht.2⟩).congr_of_mem (fun u hu => ?_) ⟨hts, ht.2⟩
      split_ifs with h
      · have : u = s := le_antisymm h hu.1
        subst this; exact hαβ.symm
      · rfl
    · have : t ∉ closure (Icc s s') := by rw [closure_Icc]; exact fun h => hts h.1
      exact HasFDerivWithinAt.of_notMem_closure this

/-- **Global existence for a globally Lipschitz ODE on a compact interval**: chaining the local
Picard–Lindelöf theorem in steps of fixed length `h` with `K h ≤ 1/2`. -/
private theorem KPrim_ode_global (f : ℝ → V → V) {t1 t0 : ℝ} (h10 : t1 ≤ t0) (K : ℝ≥0)
    (hlip : ∀ t ∈ Icc t1 t0, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (f · x) (Icc t1 t0)) (x0 : V) :
    ∃ α : ℝ → V, α t1 = x0 ∧ ∀ t ∈ Icc t1 t0, HasDerivWithinAt α (f t (α t)) (Icc t1 t0) t := by
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont 0)
  set B := max B' 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ t ∈ Icc t1 t0, ‖f t 0‖ ≤ B := fun t ht => (hB' t ht).trans (le_max_left _ _)
  set h : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hhdef
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hh : 0 < h := by positivity
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by
    rw [hhdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set sm : ℕ → ℝ := fun m => min (t1 + m * h) t0 with hsm
  have hsm_ge : ∀ m, t1 ≤ sm m := by
    intro m
    have : (0:ℝ) ≤ m * h := by positivity
    exact le_min (by linarith) h10
  have hsm_le : ∀ m, sm m ≤ t0 := fun m => min_le_right _ _
  have claim : ∀ m : ℕ, ∃ α : ℝ → V, α t1 = x0 ∧
      ∀ t ∈ Icc t1 (sm m), HasDerivWithinAt α (f t (α t)) (Icc t1 (sm m)) t := by
    intro m
    induction m with
    | zero =>
      have h0 : sm 0 = t1 := by simp [hsm, h10]
      rw [h0]
      exact KPrim_ode_step f K B h hB0 hh.le hKh hlip hcont hB le_rfl le_rfl h10
        (by linarith) x0
    | succ m ih =>
      obtain ⟨α, hα0, hα⟩ := ih
      have hmono : sm m ≤ sm (m + 1) := by
        simp only [hsm]; push_cast
        exact min_le_min_right _ (by nlinarith)
      have hstep : sm (m + 1) ≤ sm m + h := by
        simp only [hsm]; push_cast
        rcases le_total (t1 + m * h) t0 with hc | hc
        · rw [min_eq_left hc]
          exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_right hc]
          exact (min_le_right _ _).trans (by linarith)
      obtain ⟨β, hβ0, hβ⟩ := KPrim_ode_step f K B h hB0 hh.le hKh hlip hcont hB
        (hsm_ge m) hmono (hsm_le _) hstep (α (sm m))
      refine ⟨fun u => if u ≤ sm m then α u else β u, ?_, ?_⟩
      · simp only [ite_eq_left (hsm_ge m), hα0]
      · exact KPrim_ode_glue f (hsm_ge m) hmono α β hα hβ hβ0
  obtain ⟨m, hm⟩ := exists_nat_ge ((t0 - t1) / h)
  have hsmm : sm m = t0 := by
    simp only [hsm]
    apply min_eq_right
    have := (div_le_iff₀ hh).1 hm
    linarith
  obtain ⟨α, hα0, hα⟩ := claim m
  rw [hsmm] at hα
  exact ⟨α, hα0, hα⟩

end KPrimODE

/-! ### The primitive loops of the GUE phase: existence on `[t₁, t₀]` -/

section KPrimLoops

private theorem KPrim_two_le_length_cutGlueL {α : Type*} (I : LoopIdx α) (a : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem KPrim_two_le_length_cutGlueR {α : Type*} (I : LoopIdx α) (b : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

private theorem KPrim_length_cutGlueL_le {α : Type*} (I : LoopIdx α) (a : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l a).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem KPrim_length_cutGlueR_le {α : Type*} (I : LoopIdx α) (b : α)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueR k l b).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

/-- `Kgen` on a 2-loop is `kTwo` (the same fact is `private` in `Loop/TreeRep.lean`). -/
private theorem KPrim_Kgen_two (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) (t : ℝ)
    (s₁ s₂ : Bool) (x y : Z2 L) :
    KLoop.Kgen L W m t ⟨[s₁, s₂], [x, y]⟩ = KLoop.kTwo L W m t s₁ s₂ x y := by
  simp [KLoop.Kgen, LoopIdx.length]

/-- `primRhsGUE K I` only reads `K` on well-formed loops of length `2..|I|`. -/
private theorem KPrim_primRhsGUE_congr (L W : ℕ) [NeZero L] {K K' : LoopIdx (Z2 L) → ℂ}
    {I : LoopIdx (Z2 L)} (hI : I.WF)
    (h : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length → K J = K' J) :
    primRhsGUE L W K I = primRhsGUE L W K' I := by
  unfold primRhsGUE primBilGUE
  congr 1
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [h _ (LoopIdx.WF.cutGlueL hI a hk.1 hl.1 hl.2)
      (KPrim_two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
      (KPrim_length_cutGlueL_le I a hk.1 hl.1 hl.2),
    h _ (LoopIdx.WF.cutGlueR hI b hk.1 hl.1 hl.2)
      (KPrim_two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
      (KPrim_length_cutGlueR_le I b hk.1 hl.1 hl.2)]

/-- On a loop of length `1` the right side of (7.33) is the empty sum. -/
private theorem KPrim_primRhsGUE_len_one (L W : ℕ) [NeZero L] (K : LoopIdx (Z2 L) → ℂ)
    {I : LoopIdx (Z2 L)} (h : I.length = 1) : primRhsGUE L W K I = 0 := by
  unfold primRhsGUE primBilGUE
  rw [h]
  simp

/-- A well-formed loop of length `2` is `⟨[σ₁, σ₂], [a, b]⟩`. -/
private theorem KPrim_eq_two {L : ℕ} {J : LoopIdx (Z2 L)} (hJ : J.WF) (h : J.length = 2) :
    ∃ (σ₁ σ₂ : Bool) (a b : Z2 L), J = ⟨[σ₁, σ₂], [a, b]⟩ := by
  obtain ⟨σ, a⟩ := J
  have ha : a.length = 2 := h
  have hσ : σ.length = 2 := hJ.trans ha
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  exact ⟨s₁, s₂, x, y, rfl⟩

/-- The two hypotheses of `hasDerivAt_kTwoGUELoop` on `[t₁, t₀] ⊂ [0, 1)`. -/
private theorem KPrim_norm_lt {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) : ‖(t : ℂ) * (KLoop.mSig E σ₁ * KLoop.mSig E σ₂)‖ < 1 := by
  rw [norm_mul, norm_mul, KPrim_norm_mSig hE.le, KPrim_norm_mSig hE.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht0]
  linarith

/-- Existence of the GUE-phase primitive loops up to length `n ≥ 2`, by induction on `n`. -/
private theorem KPrim_exists_upto (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| < 2) {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n : ℕ)
    (hn : 2 ≤ n) :
    ∃ K : ℝ → LoopIdx (Z2 L) → ℂ,
      (∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n →
        K t1 J = KLoop.Kgen L W (KLoop.mSig E) t1 J) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (Z2 L), J.WF → 1 ≤ J.length → J.length ≤ n →
        HasDerivWithinAt (fun s => K s J) (primRhsGUE L W (K t) J)
          (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Z2 L,
        K t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE L W (KLoop.mSig E) t1 t σ₁ σ₂ a b) := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- lengths `1` (constant) and `2` (the closed form `kTwoGUELoop`)
    set K : ℝ → LoopIdx (Z2 L) → ℂ := fun t J =>
      if J.length = 1 then KLoop.Kgen L W (KLoop.mSig E) t1 J
      else kTwoGUELoop L W (KLoop.mSig E) t1 t J with hKdef
    have hK2 : ∀ t (J : LoopIdx (Z2 L)), 2 ≤ J.length →
        K t J = kTwoGUELoop L W (KLoop.mSig E) t1 t J := by
      intro t J h
      exact ite_eq_right (by omega)
    refine ⟨K, fun J hJ h1 h2 => ?_, fun t ht J hJ h1 h2 => ?_, fun t ht σ₁ σ₂ a b => ?_⟩
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · exact ite_eq_left (by omega)
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := KPrim_eq_two hJ (by omega)
        rw [hK2 t1 _ h, KPrim_Kgen_two, ← kTwoGUE_self L W]
        rfl
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · have hl : J.length = 1 := by omega
        have e : (fun s => K s J) = fun _ => KLoop.Kgen L W (KLoop.mSig E) t1 J :=
          funext fun s => ite_eq_left hl
        rw [e, KPrim_primRhsGUE_len_one L W _ hl]
        exact hasDerivWithinAt_const _ _ _
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := KPrim_eq_two hJ (by omega)
        have e : (fun s => K s ⟨[σ₁, σ₂], [a, b]⟩) =
            fun s => kTwoGUELoop L W (KLoop.mSig E) t1 s ⟨[σ₁, σ₂], [a, b]⟩ :=
          funext fun s => hK2 s _ h
        rw [e, KPrim_primRhsGUE_congr L W hJ (K' := kTwoGUELoop L W (KLoop.mSig E) t1 t)
          (fun J' _ hJ' _ => hK2 t J' hJ')]
        refine (hasDerivAt_kTwoGUELoop L W hL (KLoop.mSig E) σ₁ σ₂
          (KPrim_norm_lt hE ht1 (by linarith) σ₁ σ₂) ?_ a b).hasDerivWithinAt
        intro h1
        have := KPrim_norm_lt hE (ht1.trans ht.1) (by linarith [ht.2]) σ₁ σ₂
        rw [h1, norm_one] at this
        exact lt_irrefl _ this
    · rw [hK2 t _ (le_refl 2)]
      rfl
  | succ n hn ih =>
    obtain ⟨Kp, hq1, hq2, hq3⟩ := ih
    -- the unknown slice: well-formed loops of length `n + 1`
    have hSfin : {J : LoopIdx (Z2 L) | J.WF ∧ J.length = n + 1}.Finite :=
      (finite_loopIdx L (n + 1)).subset fun J hJ => by
        obtain ⟨h1, h2⟩ := hJ
        exact ⟨h1, by omega, h2.le⟩
    set S := hSfin.toFinset with hSdef
    have hmemS : ∀ J, J ∈ S ↔ J.WF ∧ J.length = n + 1 := fun J => hSfin.mem_toFinset
    -- the shorter lengths are continuous, hence bounded, on `[t₁, t₀]`
    have hcontK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ContinuousOn (fun t => Kp t J) (Set.Icc t1 t0) := fun J hJ h2 hn' t ht =>
      (hq2 t ht J hJ (by omega) hn').continuousWithinAt
    have hTfin := finite_loopIdx L n
    set T := hTfin.toFinset
    obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t (J : T) => Kp t J.1) (s := Set.Icc t1 t0) (continuousOn_pi.2 fun J => by
        have hJ := hTfin.mem_toFinset.1 J.2
        exact hcontK J.1 hJ.1 hJ.2.1 hJ.2.2)
    set M := max M' 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hM : ∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length →
        J.length ≤ n → ‖Kp t J‖ ≤ M := by
      intro t ht J hJ h2 hn'
      have hJT : J ∈ T := hTfin.mem_toFinset.2 ⟨hJ, h2, hn'⟩
      exact (norm_le_pi_norm (fun J : T => Kp t J.1) ⟨J, hJT⟩).trans
        ((hM' t ht).trans (le_max_left _ _))
    -- the vector field of the linear ODE for the length-`(n+1)` slice
    let g : ℝ → (S → ℂ) → LoopIdx (Z2 L) → ℂ := fun t y J =>
      if h : J ∈ S then y ⟨J, h⟩ else Kp t J
    let f : ℝ → (S → ℂ) → (S → ℂ) := fun t y I => primRhsGUE L W (g t y) I.1
    have hgS : ∀ t y (J : LoopIdx (Z2 L)) (h : J ∈ S), g t y J = y ⟨J, h⟩ :=
      fun t y J h => dite_eq_left h
    have hgN : ∀ t y (J : LoopIdx (Z2 L)), J ∉ S → g t y J = Kp t J :=
      fun t y J h => dite_eq_right h
    have hnotS : ∀ J : LoopIdx (Z2 L), J.WF → J.length ≤ n + 1 → J ∉ S → J.length ≤ n := by
      intro J hJ hl hS
      by_contra hc
      exact hS ((hmemS J).2 ⟨hJ, by omega⟩)
    -- continuity in `t`
    have hcont : ∀ y, ContinuousOn (fun t => f t y) (Set.Icc t1 t0) := by
      intro y
      refine continuousOn_pi.2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hg : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ n + 1 →
          ContinuousOn (fun t => g t y J) (Set.Icc t1 t0) := by
        intro J hJ h2 hl
        by_cases hS : J ∈ S
        · simp only [hgS _ _ _ hS]
          exact continuousOn_const
        · simp only [hgN _ _ _ hS]
          exact hcontK J hJ h2 (hnotS J hJ hl hS)
      change ContinuousOn (fun t => (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.1.length,
        ∑ l ∈ Finset.Ioc k I.1.length, ∑ a : Z2 L, ∑ b : Z2 L,
          g t y (I.1.cutGlueL k l a) * SBgue L a b * g t y (I.1.cutGlueR k l b))
        (Set.Icc t1 t0)
      refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk =>
        continuousOn_finsetSum _ fun l hl => continuousOn_finsetSum _ fun a _ =>
          continuousOn_finsetSum _ fun b _ => ?_)
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      exact ((hg _ (LoopIdx.WF.cutGlueL hI.1 a hk.1 hl.1 hl.2)
        (KPrim_two_le_length_cutGlueL I.1 a hk.1 hl.1 hl.2)
        ((KPrim_length_cutGlueL_le I.1 a hk.1 hl.1 hl.2).trans hI.2.le)).mul
          continuousOn_const).mul
        (hg _ (LoopIdx.WF.cutGlueR hI.1 b hk.1 hl.1 hl.2)
        (KPrim_two_le_length_cutGlueR I.1 b hk.1 hl.1 hl.2)
        ((KPrim_length_cutGlueR_le I.1 b hk.1 hl.1 hl.2).trans hI.2.le))
    -- the uniform Lipschitz bound: at most one cut factor has length `n + 1`
    set c0 : ℝ := ((L : ℝ) ^ 2)⁻¹ * M with hc0
    have hc00 : 0 ≤ c0 := by positivity
    set C : ℝ := (W : ℝ) ^ 2 * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
      ∑ a : Z2 L, ∑ b : Z2 L, c0 with hCdef
    have hC0 : 0 ≤ C := by positivity
    set CN : NNReal := ⟨C, hC0⟩ with hCNdef
    have hCN : (CN : ℝ) = C := rfl
    have hlip : ∀ t ∈ Set.Icc t1 t0, LipschitzWith CN (f t) := by
      intro t ht
      refine LipschitzWith.of_dist_le_mul fun y y' => ?_
      rw [dist_eq_norm, dist_eq_norm, hCN]
      set δ := ‖y - y'‖ with hδ
      have hδ0 : 0 ≤ δ := norm_nonneg _
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hterm : ∀ k ∈ Finset.Icc 1 (n + 1), ∀ l ∈ Finset.Ioc k (n + 1), ∀ a b : Z2 L,
          ‖g t y (I.1.cutGlueL k l a) * SBgue L a b * g t y (I.1.cutGlueR k l b) -
            g t y' (I.1.cutGlueL k l a) * SBgue L a b * g t y' (I.1.cutGlueR k l b)‖
            ≤ c0 * δ := by
        intro k hk l hl a b
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_Ioc] at hl
        have hl2 : l ≤ I.1.length := hI.2 ▸ hl.2
        have hsum := LoopIdx.length_cutGlueL_add_length_cutGlueR I.1 a hk.1 hl.1 hl2
        have hLR : (I.1.cutGlueR k l b).length = (I.1.cutGlueR k l a).length := by
          rw [LoopIdx.length_cutGlueR I.1 b hk.1 hl.1 hl2,
            LoopIdx.length_cutGlueR I.1 a hk.1 hl.1 hl2]
        have hWL := LoopIdx.WF.cutGlueL hI.1 a hk.1 hl.1 hl2
        have hWR := LoopIdx.WF.cutGlueR hI.1 b hk.1 hl.1 hl2
        have h2L := KPrim_two_le_length_cutGlueL I.1 a hk.1 hl.1 hl2
        have h2R := KPrim_two_le_length_cutGlueR I.1 b hk.1 hl.1 hl2
        have hleL := (KPrim_length_cutGlueL_le I.1 a hk.1 hl.1 hl2).trans hI.2.le
        have hleR := (KPrim_length_cutGlueR_le I.1 b hk.1 hl.1 hl2).trans hI.2.le
        have hSB : ‖SBgue L a b‖ = ((L : ℝ) ^ 2)⁻¹ := by
          rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
        have hcoord : ∀ (J : LoopIdx (Z2 L)) (h : J ∈ S), ‖y ⟨J, h⟩ - y' ⟨J, h⟩‖ ≤ δ :=
          fun J h => norm_le_pi_norm (y - y') ⟨J, h⟩
        have hL0 : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
        by_cases hSL : I.1.cutGlueL k l a ∈ S <;> by_cases hSR : I.1.cutGlueR k l b ∈ S
        · exfalso
          have h1 := ((hmemS _).1 hSL).2
          have h2 := ((hmemS _).1 hSR).2
          omega
        · rw [hgS _ _ _ hSL, hgS _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR,
            show ∀ u v s w : ℂ, u * s * w - v * s * w = (u - v) * s * w from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWR h2R (hnotS _ hWR hleR hSR)
          calc ‖y ⟨_, hSL⟩ - y' ⟨_, hSL⟩‖ * ((L : ℝ) ^ 2)⁻¹ * ‖Kp t (I.1.cutGlueR k l b)‖
              ≤ δ * ((L : ℝ) ^ 2)⁻¹ * M := by gcongr; exact hcoord _ hSL
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgS _ _ _ hSR, hgS _ _ _ hSR,
            show ∀ u v s w : ℂ, w * s * u - w * s * v = w * s * (u - v) from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWL h2L (hnotS _ hWL hleL hSL)
          calc ‖Kp t (I.1.cutGlueL k l a)‖ * ((L : ℝ) ^ 2)⁻¹ * ‖y ⟨_, hSR⟩ - y' ⟨_, hSR⟩‖
              ≤ M * ((L : ℝ) ^ 2)⁻¹ * δ := by gcongr; exact hcoord _ hSR
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR, sub_self, norm_zero]
          positivity
      have hIlen : I.1.length = n + 1 := hI.2
      calc ‖(f t y - f t y') I‖
          = ‖(W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Z2 L, ∑ b : Z2 L,
              (g t y (I.1.cutGlueL k l a) * SBgue L a b * g t y (I.1.cutGlueR k l b) -
                g t y' (I.1.cutGlueL k l a) * SBgue L a b *
                  g t y' (I.1.cutGlueR k l b))‖ := by
            simp only [Pi.sub_apply, f, primRhsGUE, primBilGUE, hIlen,
              ← mul_sub, ← Finset.sum_sub_distrib]
        _ = (W : ℝ) ^ 2 * ‖∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Z2 L, ∑ b : Z2 L,
              (g t y (I.1.cutGlueL k l a) * SBgue L a b * g t y (I.1.cutGlueR k l b) -
                g t y' (I.1.cutGlueL k l a) * SBgue L a b *
                  g t y' (I.1.cutGlueR k l b))‖ := by
            rw [norm_mul, norm_pow, Complex.norm_natCast]
        _ ≤ (W : ℝ) ^ 2 * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Z2 L, ∑ b : Z2 L, c0 * δ := by
            gcongr
            exact norm_sum_le_of_le _ fun k hk => norm_sum_le_of_le _ fun l hl =>
              norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ => hterm k hk l hl a b
        _ = C * δ := by
            simp only [hCdef, mul_assoc, Finset.sum_mul]
    -- global existence for the length-`(n+1)` slice
    obtain ⟨α, hα0, hα⟩ := KPrim_ode_global f ht10 CN hlip hcont
      (fun I : S => KLoop.Kgen L W (KLoop.mSig E) t1 I.1)
    refine ⟨fun t J => g t (α t) J, fun J hJ h1 hl => ?_, fun t ht J hJ h1 hl => ?_,
      fun t ht σ₁ σ₂ a b => ?_⟩
    · by_cases hS : J ∈ S
      · simp only [hgS _ _ _ hS, hα0]
      · simp only [hgN _ _ _ hS]
        exact hq1 J hJ h1 (hnotS J hJ hl hS)
    · by_cases hS : J ∈ S
      · have e : (fun s => g s (α s) J) = fun s => α s ⟨J, hS⟩ := funext fun s => hgS _ _ _ hS
        rw [e]
        exact hasDerivWithinAt_pi.1 (hα t ht) ⟨J, hS⟩
      · have hJn := hnotS J hJ hl hS
        have e : (fun s => g s (α s) J) = fun s => Kp s J := funext fun s => hgN _ _ _ hS
        rw [e, KPrim_primRhsGUE_congr L W hJ (K' := Kp t) fun J' hJ' _ hl' =>
          hgN _ _ _ fun hS' => by have := ((hmemS J').1 hS').2; omega]
        exact hq2 t ht J hJ h1 hJn
    · have hS : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Z2 L)) ∉ S := fun hS' => by
        have := ((hmemS _).1 hS').2
        simp only [LoopIdx.length, List.length_cons, List.length_nil] at this
        omega
      simp only [hgN _ _ _ hS]
      exact hq3 t ht σ₁ σ₂ a b

end KPrimLoops

/-- **(7.33)**: the GUE-phase primitive loops exist on `[t₁, t₀]` for every length `≤ n₀`,
start from `Kgen` at `t₁`, and their `2`-loops are `kTwoGUE`. -/
theorem gueK_exists (L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
    {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n0 : ℕ) :
    ∃ Kt : ℝ → LoopIdx (Z2 L) → ℂ,
      (∀ I, Kt t1 I = KLoop.Kgen L W (KLoop.mSig E) t1 I) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (Z2 L), I.WF → 1 ≤ I.length → I.length ≤ n0 →
        HasDerivWithinAt (fun s => Kt s I) (primRhsGUE L W (Kt t) I)
          (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Z2 L,
        Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE L W (KLoop.mSig E) t1 t σ₁ σ₂ a b) := by
  classical
  obtain ⟨K, hK1, hK2, hK3⟩ :=
    KPrim_exists_upto L W hL hE ht1 ht10 ht0 (max n0 2) (le_max_right _ _)
  set N := max n0 2 with hN
  refine ⟨fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
    else KLoop.Kgen L W (KLoop.mSig E) t1 I, fun I => ?_, fun t ht I hI h1 hl => ?_,
    fun t ht σ₁ σ₂ a b => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hK1 I h.1 h.2.1 h.2.2
    · rfl
  · have hIN : I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N := ⟨hI, h1, hl.trans (le_max_left _ _)⟩
    have e : (fun s => (fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
        else KLoop.Kgen L W (KLoop.mSig E) t1 I) s I) = fun s => K s I :=
      funext fun s => ite_eq_left hIN
    rw [e, KPrim_primRhsGUE_congr L W hI (K' := K t) fun J hJ h2 hJl =>
      ite_eq_left ⟨hJ, by omega, hJl.trans hIN.2.2⟩]
    exact hK2 t ht I hI h1 hIN.2.2
  · have h2 : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Z2 L)).WF ∧
        1 ≤ (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Z2 L)).length ∧
        (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Z2 L)).length ≤ N :=
      ⟨rfl, by simp [LoopIdx.length], by simp [LoopIdx.length, hN]⟩
    dsimp only
    rw [ite_eq_left h2]
    exact hK3 t ht σ₁ σ₂ a b

end RBM.Univ.GUEPhase
