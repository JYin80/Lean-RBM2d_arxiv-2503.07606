/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpVocab
import RBM2D.Hierarchy.WardResolvent
import RBM2D.Gauss.LoopSampleCont
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Propagator.Bounds
import RBM2D.Propagator.Prop5
import RBM2D.Path.ScalesBridge

/-!
# The `𝒬`-terms of `ML:exp` for alternating `σ`

Paper: Section 1 (`ML:exp`, `eq:step6main`) and Sections 5-6 (`lem_+Q`, `jywiiwsoks`,
`eq:thetadot_bound`,
`kkuuwsaf`, `kkuuwsaf5`, `eq:step6_improvedexpectation`,
`eq:p_term_step6`, `commutator_step6`).  Namespace `RBM.Evol`,
`variable (d : Sizes)`.

**Statement** `expQBound d κ c τ E t : ExpQBound d κ c τ E t` (the statement of
`Evolution/MLExpVocab.lean`): under `MLExpHyps`, the `ExpDriftBound` conclusion
`ExpDriftBoundConcl` and `ExpInvariant`, for every `ε, τ', D > 0`, eventually in `n`: for every
`u ∈ [0,t_n]` and alternating `σ` (`k = 2`) the source `A_u = qDriftT = 𝒬D + [𝒬,ϴ]f - (𝒫f)ϑ̇` is
sum-zero, symmetric, `(u,τ',D)`-decaying with `‖A_u‖_max ≤ N^ε η_u^{-1} M_u^{-3}`; and
`‖(𝒫f_t)ϑ_t‖ ≤ N^ε M_t^{-3}`.  Hypotheses of `MLExpHyps` that are used: `0 < κ`
(`Im m ≥ √(2κ)/2`), `0 < c`, `Bandwidth` (`cPrec`, `N ≤ W^{1/c}`), `0 < τ`, `RangeCond` (`M_t`,
`η_t`), `|E_n| ≤ 2 - κ`, `0 ≤ t_n < 1`, `SizeTendsto`, and `Step61Concl` along every section
(through `step61_unif`); `KboundConcl`, `Step4PT`, `DecayLoopPT` are not used.

## Argument

1. **Exact form of the source** (`MLExpQ_qDrift_eq`).  For alternating `σ` every edge factor is
   `ξ_i = m m̄ = 1`, so `ϴ_{u,σ}A = Σ_b K(a₀,b)A(b,a₁) + Σ_b K(a₁,b)A(a₀,b)` with `K = SΘ_u`.  The
   commutator formula of `qopAlgebra` (`SumZeroQ_commutator`), `𝒫(ϴA) = K(𝒫A) + (1-u)⁻¹ 𝒫A` (column
   sums of `K`) and the closed form `ϑ̇ = -Θ + (1-u)ΘSΘ` (`SumZeroQ_varthetaDot_eq`) give
   `A_u(a) = (𝒬_u D_u)(a) + Σ_c K(a₀,c)(𝒫f)_c (ϑ_{(c,a₁)} - ϑ_{(a₀,a₁)})`: the `ϑ̇` term of `A_u`
   cancels the `ϑ̇` part of the commutator exactly, so no bound of `ϑ̇` or of `[𝒬,ϴ]` is needed (the
   paper bounds `ℬ₅` and `ℬ₄` separately).  This gives
   `SumZero` (`𝒫ϑ = 1`, `𝒫𝒬 = 0`) and `TensorInvariant` (`MLExpQ_TensorInv_qDrift`, then
   `TensorInvariant.symmetric`).
2. **Ward step** (`MLExpQ_Psum_expErr`): `(𝒫f_u)_x = (2iW²η_u)⁻¹ (g - ḡ)`,
   `g = 𝔼⟨(G_u - m)E_x⟩` (`sum_gloop_ward_last_div`, `KLoop.WI_calK_two`; `σ = (-,+)` by commuting
   resolvents, `MLExpQ_sum_two_swap`; the `σ = (-)` one-loops by conjugation, `MLExpQ_LKf_false`).
   With `Step61Concl` (`step61_unif`) this gives `‖𝒫f_u‖_max ≤ N^{ε/4} ℓ_u² M_u^{-3}`
   (`(W²η)⁻¹ = ℓ² M⁻¹`).
3. **Kernel bounds** from property 5 (`norm_Theta_apply_le_prop5`, `ℓ̂(t) = ℓ_t`, `κ(t)² = 1-t`,
   `C₅ = 180·40002²`): `‖ϑ‖ ≤ c_L := C₅(1+log L)ℓ⁻²`, `Σ_c ‖K(x,c)‖ ≤ (1-u)⁻¹` and
   `‖K(x,c)‖ ≤ 3(1-u)⁻¹c_L e^{-|x-c|/(20000ℓ)}`.  The source `T₂` has `‖T₂‖ ≤ 2(1-u)⁻¹ P c_L` and,
   for `|a₀-a₁| ≥ R`, `‖T₂‖ ≤ 5 P (1-u)⁻¹ c_L e^{-R/(40000ℓ)}` (`MLExpQ_T2_size`,
   `MLExpQ_T2_decay`: either `|a₀-c| ≥ R/2` or `|c-a₁| ≥ R/2`).  Here
   `P c_L = C₅(1+log L) N^{ε/4} M⁻³`: no power of `M` is lost, the exponent `3` closes.
4. **`𝒬D`**: `qopNorm`, `qopDecay` at `𝔠 = c`, `k = 2`, `τ₀ = ε/(2(cPrec+1))`, `D_in`; the
   `ExpDriftBound` conclusion supplies `HasDecay(u,τ₀,D_in) D` and `tmax D ≤ N^{ε/4}η⁻¹M⁻³`.
5. **Absorption** (`MLExpQ_absorb`, `MLExpQ_expdecay`, `MLExpQ_N_poly`): `1 + log L ≤ N`,
   `N ≤ W^{1/c}` and `exp(-W^{τ'}/40000)` beats every power of `W`; the thresholds are in the
   `∀ᶠ n` of the conclusion.

Copies of private helpers of other files: `MLExpQ_green_comm` (through
`B45_green_comm`); `Induction/B45.lean` (`B45_{norm_Theta, sum_norm_row_le_opNorm, xi_one,
mSig_mul_conj, sum_two_swap, ward_two_tf}`), `Induction/SumZeroQ.lean`
(`SumZeroQ_{SB_mul_Theta_symm, col_sum}`), `Evolution/MLExpDrift.lean`
(`MLExpDrift_{LLf_false, measurable_LLf, zdist2_sub_comm, maxDist_two}`).  All helpers are prefixed
`MLExpQ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

section TwoSlot

variable {L : ℕ} [NeZero L]

/-- `update a 0 b = (b, a₁)` for a pair of labels. -/
theorem MLExpQ_update_zero (a : Fin 2 → Z2 L) (b : Z2 L) : Function.update a 0 b = ![b, a 1] := by
  funext i; fin_cases i <;> simp

/-- `update a 1 b = (a₀, b)` for a pair of labels. -/
theorem MLExpQ_update_one (a : Fin 2 → Z2 L) (b : Z2 L) : Function.update a 1 b = ![a 0, b] := by
  funext i; fin_cases i <;> simp

/-- `(𝒫A)_x = Σ_y A_{(x,y)}` at `k = 2`. -/
theorem MLExpQ_Psum_two (A : (Fin 2 → Z2 L) → ℂ) (x : Z2 L) :
    Psum L A x = ∑ y : Z2 L, A ![x, y] := by
  unfold Psum
  refine Finset.sum_nbij' (fun a => a 1) (fun y => ![x, y]) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro y _; simp
  · intro a ha
    have ha0 : a 0 = x := (Finset.mem_filter.mp ha).2
    funext i; fin_cases i <;> simp [ha0]
  · intro y _; simp
  · intro a ha
    have ha0 : a 0 = x := (Finset.mem_filter.mp ha).2
    congr 1
    funext i; fin_cases i <;> simp [ha0]

/-- `ϑ_{t,(x,y)} = (1-t) Θ_t(x,y)` at `k = 2`. -/
theorem MLExpQ_vartheta_two (t : ℝ) (a : Fin 2 → Z2 L) :
    vartheta L t a = ((1 - t : ℝ) : ℂ) * Theta L (t : ℂ) (a 0) (a 1) := by
  have h : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  simp [vartheta, h]

/-- The closed form of `ϑ̇_t` at `k = 2`: `ϑ̇_{(x,y)} = -Θ_t(x,y) + (1-t) (Θ_t S Θ_t)(x,y)`
(`SumZeroQ_varthetaDot_eq`). -/
theorem MLExpQ_varthetaDot_two (hL : 3 ≤ L) {t : ℝ} (ht : |t| < 1) (a : Fin 2 → Z2 L) :
    varthetaDot L t a = -Theta L (t : ℂ) (a 0) (a 1) +
      ((1 - t : ℝ) : ℂ) * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a 1) := by
  rw [SumZeroQ_varthetaDot_eq hL le_rfl ht a]
  have h : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  simp [h]

private theorem MLExpQ_mSig_mul_conj {E : ℝ} (hE : |E| ≤ 2) :
    KLoop.mSig E true * KLoop.mSig E false = 1 := by
  simp only [KLoop.mSig, ↓reduceIte, Bool.false_eq_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
  simp

/-- For alternating `σ` every edge factor is `ξ_i = m(σ_i) m(σ_{i+1}) = m m̄ = 1`
(copy of `B45_xi_one`). -/
theorem MLExpQ_xi_one {E : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} (hσ : Alternating σ)
    (i : Fin 2) : KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) = 1 := by
  rw [hσ i]
  cases h : σ i
  · simp only [Bool.not_false]
    rw [mul_comm]; exact MLExpQ_mSig_mul_conj hE
  · simp only [Bool.not_true]
    exact MLExpQ_mSig_mul_conj hE

/-- The generator `ϴ_{u,σ}` at `k = 2`, alternating `σ`: `Σ_b K(a₀,b) A(b,a₁) + Σ_b K(a₁,b) A(a₀,b)`
with `K = S Θ_u`. -/
theorem MLExpQ_thetaSig_two {E : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} (hσ : Alternating σ)
    (u : ℝ) (A : (Fin 2 → Z2 L) → ℂ) (a : Fin 2 → Z2 L) :
    thetaSig L E σ u A a = ∑ b : Z2 L, (SB L * Theta L (u : ℂ)) (a 0) b * A ![b, a 1] +
      ∑ b : Z2 L, (SB L * Theta L (u : ℂ)) (a 1) b * A ![a 0, b] := by
  simp only [thetaSig, Fin.sum_univ_two, MLExpQ_xi_one hE hσ, thetaGenMat, one_smul, mul_one,
    MLExpQ_update_zero, MLExpQ_update_one]

/-- The kernel `S Θ_ζ` is symmetric (copy of `SumZeroQ_SB_mul_Theta_symm`). -/
theorem MLExpQ_K_symm (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (x y : Z2 L) :
    (SB L * Theta L ζ) x y = (SB L * Theta L ζ) y x := by
  have h : (SB L * Theta L ζ)ᵀ = SB L * Theta L ζ := by
    rw [Matrix.transpose_mul, SB_transpose, Theta_transpose L hL hζ]
    exact (Theta_commute_SB L hL hζ).eq
  have := congrFun (congrFun h y) x
  simpa [Matrix.transpose_apply] using this

/-- The column sums of `S Θ_ζ` are the constant `(1 - ζ)⁻¹` (copy of `SumZeroQ_col_sum`). -/
theorem MLExpQ_K_colsum (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Z2 L) :
    ∑ c : Z2 L, (SB L * Theta L ζ) c y = (1 - ζ)⁻¹ := by
  simp_rw [MLExpQ_K_symm hL hζ _ y]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_Theta_row L hL hζ]
  rw [← Finset.sum_mul, sum_SB_row L hL y, one_mul]

/-- `‖(u : ℂ)‖ < 1` for `0 ≤ u < 1`. -/
theorem MLExpQ_norm_ofReal_lt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : ‖(u : ℂ)‖ < 1 := by
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]

/-- `𝒫(ϴ_{u,σ} A)_x = Σ_c (SΘ_u)(x,c) (𝒫A)_c + (1-u)⁻¹ (𝒫A)_x` for alternating `σ` at `k = 2`. -/
theorem MLExpQ_Psum_thetaSig (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (A : (Fin 2 → Z2 L) → ℂ) (x : Z2 L) :
    Psum L (thetaSig L E σ u A) x = ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) x c * Psum L A c +
      (1 - (u : ℂ))⁻¹ * Psum L A x := by
  have hζ : ‖(u : ℂ)‖ < 1 := MLExpQ_norm_ofReal_lt hu0 hu1
  rw [MLExpQ_Psum_two]
  simp only [MLExpQ_thetaSig_two hE hσ, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MLExpQ_Psum_two, Finset.mul_sum]
  · rw [Finset.sum_comm, MLExpQ_Psum_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, MLExpQ_K_colsum hL hζ c]


/-- **The exact form of the source `A_u = qDriftT` at `k = 2`, alternating `σ`**: the `ϑ̇` term of
`A_u` cancels the `ϑ̇` part of the commutator, and
`A_u = 𝒬D + Σ_c (SΘ_u)(a₀,c) (𝒫f)_c (ϑ_{(c,a₁)} - ϑ_{(a₀,a₁)})` (no `ϑ̇` remains). -/
theorem MLExpQ_qDrift_eq (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (f D : (Fin 2 → Z2 L) → ℂ) (b : Fin 2 → Z2 L) :
    Qop L u D b + (Qop L u (thetaSig L E σ u f) b - thetaSig L E σ u (Qop L u f) b) -
        Psum L f (b 0) * varthetaDot L u b =
      Qop L u D b + ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c * Psum L f c *
        (vartheta L u ![c, b 1] - vartheta L u b) := by
  have hu : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
  have hζ : ‖(u : ℂ)‖ < 1 := MLExpQ_norm_ofReal_lt hu0 hu1
  have hE2 : |E| ≤ 2 := hE.le
  have hcomm := SumZeroQ_commutator (k := 2) E σ u f b
  have hPθ := MLExpQ_Psum_thetaSig hL hE2 hu0 hu1 hσ f (b 0)
  have hϑb := MLExpQ_vartheta_two (L := L) u b
  have hϑdot := MLExpQ_varthetaDot_two hL hu b
  have hg := MLExpQ_thetaSig_two hE2 hσ u (fun b' => Psum L f (b' 0) * vartheta L u b') b
  simp only [Matrix.cons_val_zero] at hg
  have hslot : ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 1) c *
        (Psum L f (b 0) * vartheta L u ![b 0, c]) =
      Psum L f (b 0) * (((1 - u : ℝ) : ℂ) *
        (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (b 0) (b 1)) := by
    have e1 : ∀ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 1) c *
        (Psum L f (b 0) * vartheta L u ![b 0, c]) =
        Psum L f (b 0) * ((1 - u : ℝ) : ℂ) *
          (Theta L (u : ℂ) (b 0) c * (SB L * Theta L (u : ℂ)) c (b 1)) := by
      intro c
      rw [MLExpQ_K_symm hL hζ (b 1) c, MLExpQ_vartheta_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    simp only [e1]
    rw [← Finset.mul_sum]
    have hΘK : ∑ c : Z2 L, Theta L (u : ℂ) (b 0) c * (SB L * Theta L (u : ℂ)) c (b 1) =
        (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (b 0) (b 1) := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
    rw [hΘK]; ring
  have hE1 : ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c * Psum L f c *
      (vartheta L u ![c, b 1] - vartheta L u b) =
      ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c * (Psum L f c * vartheta L u ![c, b 1]) -
        (∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c * Psum L f c) * vartheta L u b := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hs : (1 - (u : ℂ))⁻¹ * ((1 - u : ℝ) : ℂ) = 1 := by
    have : (1 - (u : ℂ)) ≠ 0 := one_sub_ne_zero hζ
    have h2 : ((1 - u : ℝ) : ℂ) = 1 - (u : ℂ) := by push_cast; rfl
    rw [h2, inv_mul_cancel₀ this]
  rw [hE1, hcomm, hg, hslot, hPθ, hϑdot, hϑb]
  linear_combination (-(Psum L f (b 0) * Theta L (u : ℂ) (b 0) (b 1))) * hs


/-- **`𝒫 (qDriftT) = 0`**: the source `A_u` is sum-zero (exact, from the closed form). -/
theorem MLExpQ_sumZero_qDrift (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (f D : (Fin 2 → Z2 L) → ℂ) :
    SumZero L (fun b => Qop L u D b +
        (Qop L u (thetaSig L E σ u f) b - thetaSig L E σ u (Qop L u f) b) -
        Psum L f (b 0) * varthetaDot L u b) := by
  have hu : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
  intro x
  change Psum L _ x = 0
  simp only [MLExpQ_qDrift_eq hL hE hu0 hu1 hσ f D]
  rw [MLExpQ_Psum_two]
  simp only [Finset.sum_add_distrib]
  have h1 : ∑ y : Z2 L, Qop L u D ![x, y] = 0 := by
    rw [← MLExpQ_Psum_two]; exact SumZeroQ_Psum_Qop hL hu D x
  have h2 : ∀ c : Z2 L, ∑ y : Z2 L, vartheta L u ![c, y] = 1 := by
    intro c
    rw [← MLExpQ_Psum_two (fun a => vartheta L u a)]
    exact SumZeroQ_Psum_vartheta hL hu c
  have h3 : ∑ y : Z2 L, ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (![x, y] 0) c * Psum L f c *
      (vartheta L u ![c, ![x, y] 1] - vartheta L u ![x, y]) = 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, h2 c, h2 x]
    ring
  rw [h1, h3]
  simp

/-! ### Invariance under translation and negation of the labels -/

/-- Translation and negation invariance of a matrix on `Z2 L`. -/
def MLExpQ_MatInv (M : Matrix (Z2 L) (Z2 L) ℂ) : Prop :=
  (∀ v x y, M (x + v) (y + v) = M x y) ∧ (∀ x y, M (-x) (-y) = M x y)

/-- Translation and negation invariance of a vector on `Z2 L`. -/
def MLExpQ_VecInv (p : Z2 L → ℂ) : Prop :=
  (∀ v x, p (x + v) = p x) ∧ (∀ x, p (-x) = p x)

/-- `S^{(B)}` is invariant under translation and negation. -/
theorem MLExpQ_MatInv_SB : MLExpQ_MatInv (SB L) := by
  refine ⟨fun v x y => SB_apply_add_right L x y v, fun x y => ?_⟩
  rw [SB_apply, SB_apply, neg_sub_neg, ← neg_sub, sbKernel_neg]

/-- `Θ_ξ` is invariant under translation (property 2) and negation (property 1 and 2). -/
theorem MLExpQ_MatInv_Theta (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    MLExpQ_MatInv (Theta L ξ) := by
  refine ⟨fun v x y => Theta_apply_add_right L hL hξ x y v, fun x y => ?_⟩
  have h := Theta_apply_add_right L hL hξ (-x) (-y) (x + y)
  have e1 : -x + (x + y) = y := by abel
  have e2 : -y + (x + y) = x := by abel
  rw [e1, e2] at h
  rw [← h]
  have hs := congrFun (congrFun (Theta_transpose L hL hξ) x) y
  simpa [Matrix.transpose_apply] using hs

/-- Translation and negation invariance is stable under products. -/
theorem MLExpQ_MatInv_mul {A B : Matrix (Z2 L) (Z2 L) ℂ} (hA : MLExpQ_MatInv A)
    (hB : MLExpQ_MatInv B) : MLExpQ_MatInv (A * B) := by
  refine ⟨fun v x y => ?_, fun x y => ?_⟩
  · simp only [Matrix.mul_apply]
    symm
    refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun w => ?_
    simp only [Equiv.coe_addRight]
    rw [hA.1 v x w, hB.1 v w y]
  · simp only [Matrix.mul_apply]
    symm
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun w => ?_
    simp only [Equiv.neg_apply]
    rw [hA.2 x w, hB.2 w y]

/-- `𝒫A` is invariant if the `2`-tensor `A` is. -/
theorem MLExpQ_VecInv_Psum {A : (Fin 2 → Z2 L) → ℂ} (hA : TensorInvariant A) :
    MLExpQ_VecInv (Psum L A) := by
  refine ⟨fun v x => ?_, fun x => ?_⟩
  · rw [MLExpQ_Psum_two, MLExpQ_Psum_two]
    symm
    refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun y => ?_
    simp only [Equiv.coe_addRight]
    have h : (![x + v, y + v] : Fin 2 → Z2 L) = fun i => ![x, y] i + v := by
      funext i; fin_cases i <;> simp
    rw [h, hA.1 v ![x, y]]
  · rw [MLExpQ_Psum_two, MLExpQ_Psum_two]
    symm
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun y => ?_
    simp only [Equiv.neg_apply]
    have h : (![-x, -y] : Fin 2 → Z2 L) = fun i => -(![x, y] i) := by
      funext i; fin_cases i <;> simp
    rw [h, hA.2 ![x, y]]

/-- `ϑ_u` is a `TensorInvariant` `2`-tensor. -/
theorem MLExpQ_TensorInv_vartheta (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    TensorInvariant (vartheta L u (k := 2)) := by
  have hΘ := MLExpQ_MatInv_Theta hL (MLExpQ_norm_ofReal_lt hu0 hu1)
  refine ⟨fun v a => ?_, fun a => ?_⟩
  · simp only [MLExpQ_vartheta_two]
    rw [hΘ.1 v (a 0) (a 1)]
  · simp only [MLExpQ_vartheta_two]
    rw [hΘ.2 (a 0) (a 1)]

/-- `𝒬_u` preserves `TensorInvariant`. -/
theorem MLExpQ_TensorInv_Qop (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {A : (Fin 2 → Z2 L) → ℂ} (hA : TensorInvariant A) : TensorInvariant (Qop L u A) := by
  have hϑ := MLExpQ_TensorInv_vartheta hL hu0 hu1
  have hp := MLExpQ_VecInv_Psum hA
  refine ⟨fun v a => ?_, fun a => ?_⟩
  · simp only [Qop]
    rw [hA.1 v a, hϑ.1 v a, hp.1 v (a 0)]
  · simp only [Qop]
    rw [hA.2 a, hϑ.2 a, hp.2 (a 0)]

/-- The source `T₂` is a `TensorInvariant` `2`-tensor if `f` is. -/
theorem MLExpQ_TensorInv_T2 (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {f : (Fin 2 → Z2 L) → ℂ} (hf : TensorInvariant f) :
    TensorInvariant (fun b : Fin 2 → Z2 L => ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c *
      Psum L f c * (vartheta L u ![c, b 1] - vartheta L u b)) := by
  have hϑ := MLExpQ_TensorInv_vartheta hL hu0 hu1
  have hp := MLExpQ_VecInv_Psum hf
  have hK := MLExpQ_MatInv_mul MLExpQ_MatInv_SB (MLExpQ_MatInv_Theta hL (MLExpQ_norm_ofReal_lt hu0 hu1))
  refine ⟨fun v a => ?_, fun a => ?_⟩
  · change ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (a 0 + v) c * Psum L f c *
      (vartheta L u ![c, a 1 + v] - vartheta L u (fun i => a i + v)) = _
    symm
    refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun c => ?_
    simp only [Equiv.coe_addRight]
    have h : (![c + v, a 1 + v] : Fin 2 → Z2 L) = fun i => ![c, a 1] i + v := by
      funext i; fin_cases i <;> simp
    rw [h, hϑ.1 v ![c, a 1], hϑ.1 v a, hK.1 v (a 0) c, hp.1 v c]
  · change ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (-a 0) c * Psum L f c *
      (vartheta L u ![c, -a 1] - vartheta L u (fun i => -a i)) = _
    symm
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun c => ?_
    simp only [Equiv.neg_apply]
    have h : (![-c, -a 1] : Fin 2 → Z2 L) = fun i => -(![c, a 1] i) := by
      funext i; fin_cases i <;> simp
    rw [h, hϑ.2 ![c, a 1], hϑ.2 a, hK.2 (a 0) c, hp.2 c]

/-- `TensorInvariant` is stable under sums. -/
theorem MLExpQ_TensorInv_add {A B : (Fin 2 → Z2 L) → ℂ} (hA : TensorInvariant A)
    (hB : TensorInvariant B) : TensorInvariant (fun b => A b + B b) :=
  ⟨fun v a => by
      change A (fun i => a i + v) + B (fun i => a i + v) = A a + B a
      rw [hA.1 v a, hB.1 v a],
    fun a => by
      change A (fun i => -a i) + B (fun i => -a i) = A a + B a
      rw [hA.2 a, hB.2 a]⟩

/-- **`qDriftT` is invariant** if `f` and `D` are. -/
theorem MLExpQ_TensorInv_qDrift (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) {f D : (Fin 2 → Z2 L) → ℂ}
    (hf : TensorInvariant f) (hD : TensorInvariant D) :
    TensorInvariant (fun b => Qop L u D b +
        (Qop L u (thetaSig L E σ u f) b - thetaSig L E σ u (Qop L u f) b) -
        Psum L f (b 0) * varthetaDot L u b) := by
  have h : (fun b => Qop L u D b +
        (Qop L u (thetaSig L E σ u f) b - thetaSig L E σ u (Qop L u f) b) -
        Psum L f (b 0) * varthetaDot L u b) =
      fun b : Fin 2 → Z2 L => Qop L u D b + ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c *
        Psum L f c * (vartheta L u ![c, b 1] - vartheta L u b) :=
    funext fun b => MLExpQ_qDrift_eq hL hE hu0 hu1 hσ f D b
  rw [h]
  exact MLExpQ_TensorInv_add (MLExpQ_TensorInv_Qop hL hu0 hu1 hD) (MLExpQ_TensorInv_T2 hL hu0 hu1 hf)

end TwoSlot

/-! ## Kernel bounds from property 5 -/

section Kernel

variable {L : ℕ} [NeZero L]

/-- The constant `C₅ = 180·40002²` of `norm_Theta_apply_le_prop5`. -/
def MLExpQ_C5 : ℝ := 180 * 40002 ^ 2

/-- `0 < C₅`. -/
theorem MLExpQ_C5_pos : 0 < MLExpQ_C5 := by unfold MLExpQ_C5; positivity

/-- The slot bound `c_L(t) = C₅(1+log L)ℓ_t^{-2}`. -/
def MLExpQ_c (L : ℕ) (t : ℝ) : ℝ := MLExpQ_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹

/-- `0 ≤ c_L(t)`. -/
theorem MLExpQ_c_nonneg (L : ℕ) (t : ℝ) : 0 ≤ MLExpQ_c L t := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  unfold MLExpQ_c
  exact mul_nonneg (mul_nonneg MLExpQ_C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))

/-- `‖1 - t‖ = 1 - t` for `t ≤ 1`. -/
theorem MLExpQ_norm_one_sub {t : ℝ} (ht : t ≤ 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  have h : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- Property 5 at `ξ = t ∈ [0,1)` (`κ(t)² = 1 - t`, `ℓ̂(t) = ℓ_t`):
`(1-t)|Θ_t(x,y)| ≤ C₅(1+log L)ℓ_t^{-2}exp(-|x-y|_L/(20000ℓ_t))` (copy of `QopBounds_norm_Theta`). -/
theorem MLExpQ_norm_Theta (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : Z2 L) :
    (1 - t) * ‖Theta L (t : ℂ) x y‖ ≤ MLExpQ_c L t *
      Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h5 := norm_Theta_apply_le_prop5 L hL (t : ℂ) hξ x y
  have hell : ellhat L (t : ℂ) = ellT L t := kloop_ellT_eq ht1.le
  have hkap : kappa (t : ℂ) ^ 2 = 1 - t := by
    rw [kappa_sq, MLExpQ_norm_one_sub ht1.le]
  rw [hell, hkap] at h5
  have h1t : 0 < 1 - t := by linarith
  calc (1 - t) * ‖Theta L (t : ℂ) x y‖
      ≤ (1 - t) * (180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - t) * ellT L t ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t))) :=
        mul_le_mul_of_nonneg_left h5 h1t.le
    _ = MLExpQ_c L t * Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
        unfold MLExpQ_c MLExpQ_C5
        rw [mul_inv]
        field_simp

open scoped Matrix.Norms.Operator in
/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
theorem MLExpQ_sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

open scoped Matrix.Norms.Operator in
/-- The row `ℓ¹` bound of `S Θ_u`: `Σ_c |(S Θ_u)(x,c)| ≤ (1-u)⁻¹`. -/
theorem MLExpQ_K_row_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(SB L * Theta L (u : ℂ)) x c‖ ≤ (1 - u)⁻¹ := by
  have hξ : ‖(u : ℂ)‖ < 1 := MLExpQ_norm_ofReal_lt hu0 hu1
  have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg hu0]
  refine (MLExpQ_sum_norm_row_le_opNorm _ x).trans ?_
  calc ‖SB L * Theta L (u : ℂ)‖ ≤ ‖SB L‖ * ‖Theta L (u : ℂ)‖ := norm_mul_le _ _
    _ = ‖Theta L (u : ℂ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(u : ℂ)‖)⁻¹ := norm_Theta_le L hL hξ
    _ = (1 - u)⁻¹ := by rw [hn]

open scoped Matrix.Norms.Operator in
/-- `Σ_c |Θ_u(c,y)| ≤ (1-u)⁻¹` (column sums; `Θ_u` is symmetric). -/
theorem MLExpQ_Theta_col_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (y : Z2 L) :
    ∑ c : Z2 L, ‖Theta L (u : ℂ) c y‖ ≤ (1 - u)⁻¹ := by
  have hξ : ‖(u : ℂ)‖ < 1 := MLExpQ_norm_ofReal_lt hu0 hu1
  have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg hu0]
  have hs : ∀ c : Z2 L, Theta L (u : ℂ) c y = Theta L (u : ℂ) y c := fun c => by
    have := congrFun (congrFun (Theta_transpose L hL hξ) y) c
    simpa [Matrix.transpose_apply] using this
  simp_rw [hs]
  refine (MLExpQ_sum_norm_row_le_opNorm _ y).trans ?_
  calc ‖Theta L (u : ℂ)‖ ≤ (1 - ‖(u : ℂ)‖)⁻¹ := norm_Theta_le L hL hξ
    _ = (1 - u)⁻¹ := by rw [hn]

/-- `Σ_c ‖SB x c‖ = 1`. -/
theorem MLExpQ_SB_row_norm (hL : 3 ≤ L) (x : Z2 L) : ∑ c : Z2 L, ‖SB L x c‖ = 1 := by
  have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) (sum_nnnorm_SB_row L hL x)
  simpa [NNReal.coe_sum] using h

/-- Decay of the kernel `S Θ_u`: `|(SΘ_u)(x,c)| ≤ 3(1-u)⁻¹c_L(u) exp(-|x-c|_L/(20000ℓ_u))`
(five-point support of `S`, property 5). -/
theorem MLExpQ_K_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x c : Z2 L) :
    ‖(SB L * Theta L (u : ℂ)) x c‖ ≤ 3 * ((1 - u)⁻¹ * MLExpQ_c L u) *
      Real.exp (-(zdist2 L (x - c) : ℝ) / (20000 * ellT L u)) := by
  have h1u : 0 < 1 - u := by linarith
  have hℓ : 1 ≤ ellT L u := one_le_ellT (by omega) hu0 hu1
  set lam : ℝ := 20000 * ellT L u with hlam
  have hlam1 : 1 ≤ lam := by rw [hlam]; linarith
  have hlam0 : 0 < lam := by linarith
  set G : ℝ := (1 - u)⁻¹ * MLExpQ_c L u * Real.exp (-(zdist2 L (x - c) : ℝ) / lam) with hG
  have hG0 : 0 ≤ G := by
    have := MLExpQ_c_nonneg L u
    positivity
  have hterm : ∀ w : Z2 L, ‖SB L x w‖ * ‖Theta L (u : ℂ) w c‖ ≤ ‖SB L x w‖ * (3 * G) := by
    intro w
    by_cases hw : 1 < zdist2 L (x - w)
    · rw [SB_apply_eq_zero L hL hw]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hw1 : zdist2 L (x - w) ≤ 1 := not_lt.mp hw
      have hΘ := MLExpQ_norm_Theta hL hu0 hu1 w c
      have hΘ' : ‖Theta L (u : ℂ) w c‖ ≤ (1 - u)⁻¹ * (MLExpQ_c L u *
          Real.exp (-(zdist2 L (w - c) : ℝ) / lam)) := by
        rw [← div_eq_inv_mul, le_div_iff₀ h1u, mul_comm]
        exact hΘ
      have htri : (zdist2 L (x - c) : ℝ) ≤ 1 + (zdist2 L (w - c) : ℝ) := by
        have h := zdist2_add_le L (x - w) (w - c)
        rw [show x - w + (w - c) = x - c by abel] at h
        have h2 : (zdist2 L (x - c) : ℝ) ≤ (zdist2 L (x - w) : ℝ) + (zdist2 L (w - c) : ℝ) := by
          exact_mod_cast h
        have h3 : (zdist2 L (x - w) : ℝ) ≤ 1 := by exact_mod_cast hw1
        linarith
      have hexp : Real.exp (-(zdist2 L (w - c) : ℝ) / lam) ≤
          3 * Real.exp (-(zdist2 L (x - c) : ℝ) / lam) := by
        have h1 : -(zdist2 L (w - c) : ℝ) / lam ≤ 1 + -(zdist2 L (x - c) : ℝ) / lam := by
          have : -(zdist2 L (w - c) : ℝ) / lam ≤ (1 - (zdist2 L (x - c) : ℝ)) / lam := by
            apply div_le_div_of_nonneg_right _ hlam0.le
            linarith
          have h2 : (1 - (zdist2 L (x - c) : ℝ)) / lam ≤ 1 + -(zdist2 L (x - c) : ℝ) / lam := by
            rw [sub_div, one_div]
            have : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam1
            linarith [neg_div lam (zdist2 L (x - c) : ℝ)]
          linarith
        calc Real.exp (-(zdist2 L (w - c) : ℝ) / lam)
            ≤ Real.exp (1 + -(zdist2 L (x - c) : ℝ) / lam) := Real.exp_le_exp.mpr h1
          _ = Real.exp 1 * Real.exp (-(zdist2 L (x - c) : ℝ) / lam) := Real.exp_add _ _
          _ ≤ 3 * Real.exp (-(zdist2 L (x - c) : ℝ) / lam) :=
              mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
      calc ‖Theta L (u : ℂ) w c‖ ≤ (1 - u)⁻¹ * (MLExpQ_c L u * Real.exp (-(zdist2 L (w - c) : ℝ) / lam)) := hΘ'
        _ ≤ (1 - u)⁻¹ * (MLExpQ_c L u * (3 * Real.exp (-(zdist2 L (x - c) : ℝ) / lam))) := by
            gcongr
            exact MLExpQ_c_nonneg L u
        _ = 3 * G := by rw [hG]; ring
  calc ‖(SB L * Theta L (u : ℂ)) x c‖
      = ‖∑ w : Z2 L, SB L x w * Theta L (u : ℂ) w c‖ := by rw [Matrix.mul_apply]
    _ ≤ ∑ w : Z2 L, ‖SB L x w * Theta L (u : ℂ) w c‖ := norm_sum_le _ _
    _ = ∑ w : Z2 L, ‖SB L x w‖ * ‖Theta L (u : ℂ) w c‖ := by simp only [norm_mul]
    _ ≤ ∑ w : Z2 L, ‖SB L x w‖ * (3 * G) := Finset.sum_le_sum fun w _ => hterm w
    _ = 3 * G := by rw [← Finset.sum_mul, MLExpQ_SB_row_norm hL x, one_mul]
    _ = 3 * ((1 - u)⁻¹ * MLExpQ_c L u) * Real.exp (-(zdist2 L (x - c) : ℝ) / lam) := by
        rw [hG]; ring

/-- The `ϑ` bound: `‖ϑ_{(x,y)}‖ ≤ c_L(u) exp(-|x-y|_L/(20000ℓ_u))`. -/
theorem MLExpQ_vartheta_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    ‖vartheta L u ![x, y]‖ ≤ MLExpQ_c L u * Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L u)) := by
  rw [MLExpQ_vartheta_two, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simpa using MLExpQ_norm_Theta hL hu0 hu1 x y

theorem MLExpQ_vartheta_col_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (y : Z2 L) :
    ∑ c : Z2 L, ‖vartheta L u ![c, y]‖ ≤ 1 := by
  have h1u : 0 < 1 - u := by linarith
  have h : ∀ c : Z2 L, ‖vartheta L u ![c, y]‖ = (1 - u) * ‖Theta L (u : ℂ) c y‖ := by
    intro c
    rw [MLExpQ_vartheta_two, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1u.le]
    simp
  simp_rw [h]
  rw [← Finset.mul_sum]
  calc (1 - u) * ∑ c : Z2 L, ‖Theta L (u : ℂ) c y‖ ≤ (1 - u) * (1 - u)⁻¹ :=
        mul_le_mul_of_nonneg_left (MLExpQ_Theta_col_le hL hu0 hu1 y) h1u.le
    _ = 1 := mul_inv_cancel₀ h1u.ne'

end Kernel

/-! ## The abstract estimates of the source `Σ_c K(x,c) p(c) (ϑ(c,y) - ϑ(x,y))` -/

section T2

variable {L : ℕ} [NeZero L]

/-- Size: `‖Σ_c K(x,c) p(c) (ϑ(c,y) - ϑ(x,y))‖ ≤ K₀ P 2θ`. -/
theorem MLExpQ_T2_size {Kf : Z2 L → Z2 L → ℂ} {p : Z2 L → ℂ} {ϑ : Z2 L → Z2 L → ℂ}
    {K₀ P θ : ℝ} (hK₀ : ∀ x, ∑ c, ‖Kf x c‖ ≤ K₀) (hp : ∀ c, ‖p c‖ ≤ P)
    (hθ : ∀ x y, ‖ϑ x y‖ ≤ θ) (hP0 : 0 ≤ P) (hθ0 : 0 ≤ θ) (x y : Z2 L) :
    ‖∑ c, Kf x c * p c * (ϑ c y - ϑ x y)‖ ≤ K₀ * (P * (2 * θ)) := by
  calc ‖∑ c, Kf x c * p c * (ϑ c y - ϑ x y)‖
      ≤ ∑ c, ‖Kf x c * p c * (ϑ c y - ϑ x y)‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖Kf x c‖ * (P * (2 * θ)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_mul]
        have h1 : ‖ϑ c y - ϑ x y‖ ≤ 2 * θ :=
          (norm_sub_le _ _).trans (by linarith [hθ c y, hθ x y])
        have h2 : ‖p c‖ * ‖ϑ c y - ϑ x y‖ ≤ P * (2 * θ) :=
          mul_le_mul (hp c) h1 (norm_nonneg _) hP0
        calc ‖Kf x c‖ * ‖p c‖ * ‖ϑ c y - ϑ x y‖
            = ‖Kf x c‖ * (‖p c‖ * ‖ϑ c y - ϑ x y‖) := by ring
          _ ≤ ‖Kf x c‖ * (P * (2 * θ)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (∑ c, ‖Kf x c‖) * (P * (2 * θ)) := by rw [Finset.sum_mul]
    _ ≤ K₀ * (P * (2 * θ)) := mul_le_mul_of_nonneg_right (hK₀ x) (by positivity)

/-- Decay: if `R ≤ |x-y|_L` then the source is `≤ P (κ₁ + 2 K₀ θ) exp(-R/(2λ))`: either `|x-c| ≥ R/2`
(the kernel decays) or `|c-y| ≥ R/2` (`ϑ` decays). -/
theorem MLExpQ_T2_decay {Kf : Z2 L → Z2 L → ℂ} {p : Z2 L → ℂ} {ϑ : Z2 L → Z2 L → ℂ}
    {K₀ κ₁ P θ lam R : ℝ} (hlam : 0 < lam)
    (hK₀ : ∀ x, ∑ c, ‖Kf x c‖ ≤ K₀)
    (hKd : ∀ x c, ‖Kf x c‖ ≤ κ₁ * Real.exp (-(zdist2 L (x - c) : ℝ) / lam))
    (hp : ∀ c, ‖p c‖ ≤ P)
    (hθd : ∀ x y, ‖ϑ x y‖ ≤ θ * Real.exp (-(zdist2 L (x - y) : ℝ) / lam))
    (hϑs : ∀ y, ∑ c, ‖ϑ c y‖ ≤ 1)
    (hP0 : 0 ≤ P) (hθ0 : 0 ≤ θ) (hκ₁ : 0 ≤ κ₁) (hK00 : 0 ≤ K₀) (hR : 0 ≤ R)
    {x y : Z2 L} (hxy : R ≤ (zdist2 L (x - y) : ℝ)) :
    ‖∑ c, Kf x c * p c * (ϑ c y - ϑ x y)‖ ≤
      P * (κ₁ + 2 * (K₀ * θ)) * Real.exp (-R / (2 * lam)) := by
  set e : ℝ := Real.exp (-R / (2 * lam)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hmono : ∀ z : ℝ, R / 2 ≤ z → Real.exp (-z / lam) ≤ e := by
    intro z hz
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    calc R / (2 * lam) = (R / 2) / lam := by rw [div_div]
      _ ≤ z / lam := div_le_div_of_nonneg_right hz hlam.le
  have hxye : ‖ϑ x y‖ ≤ θ * e :=
    (hθd x y).trans (mul_le_mul_of_nonneg_left (hmono _ (by linarith)) hθ0)
  have hcase : ∀ c : Z2 L, ‖Kf x c‖ * ‖ϑ c y‖ ≤ κ₁ * e * ‖ϑ c y‖ + ‖Kf x c‖ * (θ * e) := by
    intro c
    have htri : (zdist2 L (x - y) : ℝ) ≤ (zdist2 L (x - c) : ℝ) + (zdist2 L (c - y) : ℝ) := by
      have h := zdist2_add_le L (x - c) (c - y)
      rw [show x - c + (c - y) = x - y by abel] at h
      exact_mod_cast h
    by_cases hc1 : R / 2 ≤ (zdist2 L (x - c) : ℝ)
    · have h1 : ‖Kf x c‖ ≤ κ₁ * e :=
        (hKd x c).trans (mul_le_mul_of_nonneg_left (hmono _ hc1) hκ₁)
      calc ‖Kf x c‖ * ‖ϑ c y‖ ≤ (κ₁ * e) * ‖ϑ c y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ κ₁ * e * ‖ϑ c y‖ + ‖Kf x c‖ * (θ * e) :=
            le_add_of_nonneg_right (by positivity)
    · have hc2 : R / 2 ≤ (zdist2 L (c - y) : ℝ) := by linarith [not_le.mp hc1]
      have h1 : ‖ϑ c y‖ ≤ θ * e :=
        (hθd c y).trans (mul_le_mul_of_nonneg_left (hmono _ hc2) hθ0)
      calc ‖Kf x c‖ * ‖ϑ c y‖ ≤ ‖Kf x c‖ * (θ * e) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ κ₁ * e * ‖ϑ c y‖ + ‖Kf x c‖ * (θ * e) :=
            le_add_of_nonneg_left (by positivity)
  have hsum1 : ∑ c, ‖Kf x c‖ * ‖ϑ c y‖ ≤ κ₁ * e + K₀ * (θ * e) := by
    calc ∑ c, ‖Kf x c‖ * ‖ϑ c y‖
        ≤ ∑ c, (κ₁ * e * ‖ϑ c y‖ + ‖Kf x c‖ * (θ * e)) := Finset.sum_le_sum fun c _ => hcase c
      _ = κ₁ * e * (∑ c, ‖ϑ c y‖) + (∑ c, ‖Kf x c‖) * (θ * e) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ κ₁ * e * 1 + K₀ * (θ * e) :=
          add_le_add (mul_le_mul_of_nonneg_left (hϑs y) (by positivity))
            (mul_le_mul_of_nonneg_right (hK₀ x) (by positivity))
      _ = κ₁ * e + K₀ * (θ * e) := by ring
  have hlast : (∑ c, ‖Kf x c‖) * ‖ϑ x y‖ ≤ K₀ * (θ * e) :=
    mul_le_mul (hK₀ x) hxye (norm_nonneg _) hK00
  calc ‖∑ c, Kf x c * p c * (ϑ c y - ϑ x y)‖
      ≤ ∑ c, ‖Kf x c * p c * (ϑ c y - ϑ x y)‖ := norm_sum_le _ _
    _ ≤ ∑ c, P * (‖Kf x c‖ * ‖ϑ c y‖ + ‖Kf x c‖ * ‖ϑ x y‖) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_mul]
        have h1 : ‖ϑ c y - ϑ x y‖ ≤ ‖ϑ c y‖ + ‖ϑ x y‖ := norm_sub_le _ _
        calc ‖Kf x c‖ * ‖p c‖ * ‖ϑ c y - ϑ x y‖
            ≤ ‖Kf x c‖ * P * (‖ϑ c y‖ + ‖ϑ x y‖) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hp c) (norm_nonneg _)) h1 (norm_nonneg _)
                (by positivity)
          _ = P * (‖Kf x c‖ * ‖ϑ c y‖ + ‖Kf x c‖ * ‖ϑ x y‖) := by ring
    _ = P * ((∑ c, ‖Kf x c‖ * ‖ϑ c y‖) + (∑ c, ‖Kf x c‖) * ‖ϑ x y‖) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ P * ((κ₁ * e + K₀ * (θ * e)) + K₀ * (θ * e)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hlast) hP0
    _ = P * (κ₁ + 2 * (K₀ * θ)) * e := by ring

end T2

/-! ## The Ward identity for `𝒫 f_u` -/

section Ward

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Two resolvents of the same matrix commute (copy of `B45_green_comm`). -/
theorem MLExpQ_green_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z w : ℂ) : green H z * green H w = green H w * green H z := by
  unfold green
  rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev]
  congr 1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul]
  rw [mul_comm z w]
  abel

theorem MLExpQ_spectralZ_im_ne {E u : ℝ} (hE : |E| < 2) (hu : u < 1) :
    (spectralZ E u).im ≠ 0 := by
  rw [spectralZ_im]
  exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'

/-- The `σ = (-)` one-loop is the complex conjugate of the `σ = (+)` one-loop (copy of
`MLExpDrift_LLf_false`). -/
theorem MLExpQ_LLf_false (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (x : Z2 L) :
    LLf L W E u M ⟨[false], [x]⟩ = (starRingEnd ℂ) (LLf L W E u M ⟨[true], [x]⟩) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  unfold LLf
  simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]
  have hG : Gsig (blockMat M) (spectralZ E u) false = (Gsig (blockMat M) (spectralZ E u) true)ᴴ :=
    ((Gsig_conjTranspose hH (spectralZ E u) true).trans (by simp)).symm
  rw [hG]
  set G := Gsig (blockMat M) (spectralZ E u) true
  have h1 : Gᴴ * Eblk L W x = (Eblk L W x * G)ᴴ := by
    rw [Matrix.conjTranspose_mul, Eblk_conjTranspose]
  rw [h1, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rfl

theorem MLExpQ_LKf_false (E u : ℝ) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (x : Z2 L) :
    LKf L W E u M ⟨[false], [x]⟩ = (starRingEnd ℂ) (LKf L W E u M ⟨[true], [x]⟩) := by
  unfold LKf
  rw [MLExpQ_LLf_false E u hM x, map_sub]
  have h1 : KLoop.Kcal L W E u ⟨[false], [x]⟩ = KLoop.mSig E false := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  have h2 : KLoop.Kcal L W E u ⟨[true], [x]⟩ = KLoop.mSig E true := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2]
  rfl

/-- **Rank `2`, `σ = (+,-)`**: `Σ_x (𝓛-𝒦)_{(+,-),(a,x)} = (2iW²η_u)⁻¹((𝓛-𝒦)_{(+),(a)} - (𝓛-𝒦)_{(-),(a)})`
(`sum_gloop_ward_last_div` and `WI_calK_two`; see `B45_ward_two_tf`). -/
theorem MLExpQ_ward_tf (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M ⟨[true, false], [a, x]⟩ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨[true], [a]⟩ - LKf L W E u M ⟨[false], [a]⟩) := by
  have hzim : (spectralZ E u).im = etaT E u := spectralZ_im E u
  have hz : (spectralZ E u).im ≠ 0 := MLExpQ_spectralZ_im_ne hE hu1
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hz' : ((starRingEnd ℂ) (spectralZ E u)).im ≠ 0 := by
    rw [Complex.conj_im]; exact neg_ne_zero.mpr hz
  have h1 : ∑ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [a, x]⟩ =
      (gloop L W (blockMat M) (spectralZ E u) ⟨[true], [a]⟩ -
        gloop L W (blockMat M) (spectralZ E u) ⟨[false], [a]⟩) /
        (2 * Complex.I * (W : ℂ) ^ 2 * ((spectralZ E u).im : ℂ)) :=
    sum_gloop_ward_last_div L W (H := blockMat M) (z := spectralZ E u)
      (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz)
      (RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hH hz') hz [] a [] rfl
  have h2 : ∑ x : Z2 L, KLoop.Kcal L W E u ⟨[true, false], [a, x]⟩ =
      (2 * Complex.I * (W : ℂ) ^ 2 * (KLoop.etaT E u : ℂ))⁻¹ *
        (KLoop.Kcal L W E u ⟨[true], [a]⟩ - KLoop.Kcal L W E u ⟨[false], [a]⟩) :=
    KLoop.WI_calK_two L hL W hW hE ⟨hu0, hu1⟩ a
  unfold LKf LLf
  rw [Finset.sum_sub_distrib, h1, h2, kloop_etaT_eq, hzim, div_eq_inv_mul]
  ring

/-- **Rank `2`, `σ = (-,+)`**: the same slot sum (resolvents commute, `Kcal_two`; see
`B45_sum_two_swap`). -/
theorem MLExpQ_sum_two_swap {E u : ℝ} (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, LKf L W E u M ⟨[true, false], [a, x]⟩ := by
  have hr1 : ∀ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [a, x]⟩ =
      gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [x, a]⟩ := fun x =>
    gloop_rotate (H := blockMat M) (z := spectralZ E u) false a (σ := [true]) (a := [x]) rfl
  have hr2 : ∀ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [a, x]⟩ =
      gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [x, a]⟩ := fun x =>
    gloop_rotate (H := blockMat M) (z := spectralZ E u) true a (σ := [false]) (a := [x]) rfl
  have hg : ∑ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, gloop L W (blockMat M) (spectralZ E u) ⟨[true, false], [a, x]⟩ := by
    rw [Finset.sum_congr rfl (fun x _ => hr1 x), Finset.sum_congr rfl (fun x _ => hr2 x),
      sum_gloop_head true [false] [a], sum_gloop_head false [true] [a]]
    simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true, Gsig_false]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      MLExpQ_green_comm (blockMat M) (spectralZ E u) ((starRingEnd ℂ) (spectralZ E u))]
  have hk : ∑ x : Z2 L, KLoop.Kcal L W E u ⟨[false, true], [a, x]⟩ =
      ∑ x : Z2 L, KLoop.Kcal L W E u ⟨[true, false], [a, x]⟩ := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [KLoop.Kcal_two, KLoop.Kcal_two, mul_comm (KLoop.mSig E false) (KLoop.mSig E true)]
  unfold LKf LLf
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hg, hk]

/-- **Rank `2`, alternating `σ`**: `Σ_x (𝓛-𝒦)_{σ,(a,x)} = (2iW²η_u)⁻¹((𝓛-𝒦)_{(+),(a)} - (𝓛-𝒦)_{(-),(a)})`. -/
theorem MLExpQ_ward_alt (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (a : Z2 L) :
    ∑ x : Z2 L, LKf L W E u M (loopOf σ ![a, x]) =
      (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf L W E u M ⟨[true], [a]⟩ - LKf L W E u M ⟨[false], [a]⟩) := by
  have hloop : ∀ x : Z2 L, loopOf σ ![a, x] = (⟨[σ 0, σ 1], [a, x]⟩ : LoopIdx (Z2 L)) := by
    intro x; simp [loopOf, List.ofFn_succ]
  simp only [hloop]
  have h1 : σ 1 = !σ 0 := by simpa using hσ 0
  rw [h1]
  cases h0 : σ 0
  · simp only [Bool.not_false]
    rw [MLExpQ_sum_two_swap]
    exact MLExpQ_ward_tf hL hW hE hu0 hu1 hM a
  · simp only [Bool.not_true]
    exact MLExpQ_ward_tf hL hW hE hu0 hu1 hM a

end Ward

section WardSeq

variable (d : Sizes)

/-- The loop is a measurable function of the sample (copy of `MLExpDrift_measurable_LLf`). -/
theorem MLExpQ_measurable_LLf (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) :
    Measurable fun ω : Sizes.SeqΩ d => LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J :=
  (measurable_gloop_HflowBlock_sample (d.L n) (d.W n) u (MLExpQ_spectralZ_im_ne hE hu) J
    hJ).comp (Sizes.measurable_slice d n)

/-- The loop is bounded on every sample (`norm_gloop_le_crude`), hence integrable. -/
theorem MLExpQ_integrable_LLf (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) :
    Integrable (fun ω : Sizes.SeqΩ d => LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J)
      (Sizes.seqP d) := by
  have hz := MLExpQ_spectralZ_im_ne hE hu
  refine Integrable.of_bound (MLExpQ_measurable_LLf d n hE hu hJ).aestronglyMeasurable
    ((((d.L n * d.W n) ^ 2 : ℕ) : ℝ) *
      (|(spectralZ E u).im|⁻¹ * ((d.W n : ℝ)⁻¹ ^ 2)) ^ J.a.length)
    (Eventually.of_forall fun ω => ?_)
  have hH : (blockMat (Sizes.seqHflow d n u ω)).IsHermitian :=
    (Sizes.seqHflow_isHermitian d n u ω).submatrix _
  exact norm_gloop_le_crude (d.L n) (d.W n) hH (abs_pos.mpr hz) le_rfl J hJ

theorem MLExpQ_integrable_LKf (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) :
    Integrable (fun ω : Sizes.SeqΩ d => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J)
      (Sizes.seqP d) :=
  (MLExpQ_integrable_LLf d n hE hu hJ).sub (integrable_const _)

/-- `f_u(a) = 𝔼 (𝓛-𝒦)_{u,σ,a}`, as the integral of `LKf`. -/
theorem MLExpQ_expErrT_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 (d.L n)) :
    expErrT d n E u σ a =
      ∫ ω, LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) ∂(Sizes.seqP d) := by
  have hint := MLExpQ_integrable_LLf d n hE hu1 (J := loopOf σ a) (by simp [loopOf, LoopIdx.WF])
  unfold LKf
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [expErrT, expLoopErr, LLf]

/-- `𝔼 (𝓛-𝒦)_{(+),(x)} = oneLoopExpErr` (`𝒦_{(+),(x)} = m`). -/
theorem MLExpQ_integral_LKf_one (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    (x : Z2 (d.L n)) :
    ∫ ω, LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩ ∂(Sizes.seqP d) =
      oneLoopExpErr d n E u x := by
  have hint := MLExpQ_integrable_LLf d n hE hu1 (J := ⟨[true], [x]⟩) (by simp [LoopIdx.WF])
  unfold LKf
  rw [integral_sub hint (integrable_const _), integral_const]
  have h2 : KLoop.Kcal (d.L n) (d.W n) E u ⟨[true], [x]⟩ = spectralM E := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length, KLoop.mSig]
  simp [oneLoopExpErr, LLf, h2]

/-- **The Ward identity for `𝒫 f_u`** (`eq:step6_improvedexpectation`; alternating `σ`):
`(𝒫 f_u)_x = (2iW²η_u)⁻¹ (g - ḡ)`, `g = 𝔼⟨(G_u - m)E_x⟩` (`oneLoopExpErr`). -/
theorem MLExpQ_Psum_expErr (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (x : Z2 (d.L n)) :
    Psum (d.L n) (expErrT d n E u σ) x =
      (2 * Complex.I * (d.W n : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (oneLoopExpErr d n E u x - (starRingEnd ℂ) (oneLoopExpErr d n E u x)) := by
  have hL3 := d.three_le_L n
  have hW1 : 1 ≤ d.W n := d.W_pos n
  rw [MLExpQ_Psum_two]
  simp only [MLExpQ_expErrT_eq d n hE hu1 σ]
  have hwf : ∀ (y : Z2 (d.L n)), (loopOf σ ![x, y]).WF := fun y => by simp [loopOf, LoopIdx.WF]
  rw [← integral_finsetSum _ (fun y _ => MLExpQ_integrable_LKf d n hE hu1 (hwf y))]
  have hone : Integrable (fun ω : Sizes.SeqΩ d =>
      LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩) (Sizes.seqP d) :=
    MLExpQ_integrable_LKf d n hE hu1 (J := ⟨[true], [x]⟩) (by simp [LoopIdx.WF])
  have hpt : ∀ ω : Sizes.SeqΩ d, ∑ y : Z2 (d.L n),
      LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ ![x, y]) =
      (2 * Complex.I * (d.W n : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹ *
        (LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩ -
          (starRingEnd ℂ) (LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩)) := by
    intro ω
    rw [MLExpQ_ward_alt hL3 hW1 hE hu0 hu1 (Sizes.seqHflow_isHermitian d n u ω) hσ x,
      MLExpQ_LKf_false E u (Sizes.seqHflow_isHermitian d n u ω) x]
  simp only [hpt]
  have hintc : Integrable (fun ω : Sizes.SeqΩ d => (starRingEnd ℂ)
      (LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩)) (Sizes.seqP d) :=
    Integrable.mono' hone.norm (Complex.continuous_conj.comp_aestronglyMeasurable hone.1)
      (Eventually.of_forall fun ω => (Complex.norm_conj _).le)
  rw [integral_const_mul, integral_sub hone hintc, integral_conj,
    MLExpQ_integral_LKf_one d n hE hu1 x]

/-- `‖(𝒫 f_u)_x‖ ≤ (W²η_u)⁻¹ ‖𝔼⟨(G_u - m)E_x⟩‖`. -/
theorem MLExpQ_norm_Psum_expErr (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (x : Z2 (d.L n)) :
    ‖Psum (d.L n) (expErrT d n E u σ) x‖ ≤
      (((d.W n : ℝ) ^ 2) * etaT E u)⁻¹ * ‖oneLoopExpErr d n E u x‖ := by
  rw [MLExpQ_Psum_expErr d n hE hu0 hu1 hσ x, norm_mul]
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hκ : ‖(2 * Complex.I * (d.W n : ℂ) ^ 2 * (etaT E u : ℂ))⁻¹‖ =
      (2 * (((d.W n : ℝ) ^ 2) * etaT E u))⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hη.le, Complex.norm_natCast]
    simp
    ring
  rw [hκ]
  have h2 : ‖oneLoopExpErr d n E u x - (starRingEnd ℂ) (oneLoopExpErr d n E u x)‖ ≤
      2 * ‖oneLoopExpErr d n E u x‖ := by
    calc _ ≤ ‖oneLoopExpErr d n E u x‖ + ‖(starRingEnd ℂ) (oneLoopExpErr d n E u x)‖ :=
          norm_sub_le _ _
      _ = 2 * ‖oneLoopExpErr d n E u x‖ := by rw [Complex.norm_conj]; ring
  have hpos : 0 < (((d.W n : ℝ) ^ 2) * etaT E u) := by positivity
  calc (2 * (((d.W n : ℝ) ^ 2) * etaT E u))⁻¹ *
        ‖oneLoopExpErr d n E u x - (starRingEnd ℂ) (oneLoopExpErr d n E u x)‖
      ≤ (2 * (((d.W n : ℝ) ^ 2) * etaT E u))⁻¹ * (2 * ‖oneLoopExpErr d n E u x‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (((d.W n : ℝ) ^ 2) * etaT E u)⁻¹ * ‖oneLoopExpErr d n E u x‖ := by
        field_simp

end WardSeq

/-! ## Numerics -/

section Numeric

/-- `N^a ≤ W^{a/c}` for `a ≥ 0` from the bandwidth condition `N^c ≤ W`. -/
theorem MLExpQ_N_poly {N Wr c : ℝ} (hN0 : 0 ≤ N) (hc : 0 < c) (hbw : N ^ c ≤ Wr) {a : ℝ}
    (ha : 0 ≤ a) : N ^ a ≤ Wr ^ (a / c) := by
  have hWr : 0 ≤ Wr := le_trans (Real.rpow_nonneg hN0 _) hbw
  have h1 : N = (N ^ c) ^ c⁻¹ := (Real.rpow_rpow_inv hN0 hc.ne').symm
  have h2 : (N ^ c) ^ c⁻¹ ≤ Wr ^ c⁻¹ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hbw (inv_nonneg.mpr hc.le)
  calc N ^ a = ((N ^ c) ^ c⁻¹) ^ a := by rw [← h1]
    _ ≤ (Wr ^ c⁻¹) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg (Real.rpow_nonneg hN0 _) _) h2 ha
    _ = Wr ^ (a / c) := by rw [← Real.rpow_mul hWr, div_eq_inv_mul]

/-- The absorption of the constants and of `log L` into `N^ε`. -/
theorem MLExpQ_absorb {N Lr ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hLN : Lr ≤ N) (hL1 : 1 ≤ Lr)
    (hK : 2 + 2 * MLExpQ_C5 * (1 + 4 / ε) ≤ N ^ (ε / 2)) :
    N ^ (ε / 2) + 1 + 2 * MLExpQ_C5 * (1 + Real.log Lr) * N ^ (ε / 4) ≤ N ^ ε := by
  have hN0 : 0 < N := by linarith
  have hlogL : Real.log Lr ≤ Real.log N := Real.log_le_log (by linarith) hLN
  have hlogN : Real.log N ≤ N ^ (ε / 4) / (ε / 4) :=
    Real.log_le_rpow_div hN0.le (by positivity)
  have hq1 : 1 ≤ N ^ (ε / 4) := Real.one_le_rpow hN (by positivity)
  have hq2 : N ^ (ε / 4) ≤ N ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hq3 : N ^ (ε / 4) * N ^ (ε / 4) = N ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hq4 : N ^ (ε / 2) * N ^ (ε / 2) = N ^ ε := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hq0 : 1 ≤ N ^ (ε / 2) := le_trans hq1 hq2
  have hC5 : 0 < MLExpQ_C5 := MLExpQ_C5_pos
  have h1 : (1 + Real.log Lr) * N ^ (ε / 4) ≤ (1 + 4 / ε) * N ^ (ε / 2) := by
    calc (1 + Real.log Lr) * N ^ (ε / 4)
        ≤ (1 + N ^ (ε / 4) / (ε / 4)) * N ^ (ε / 4) := by gcongr; linarith
      _ = N ^ (ε / 4) + (4 / ε) * (N ^ (ε / 4) * N ^ (ε / 4)) := by field_simp
      _ ≤ N ^ (ε / 2) + (4 / ε) * N ^ (ε / 2) := by rw [hq3]; gcongr
      _ = (1 + 4 / ε) * N ^ (ε / 2) := by ring
  calc N ^ (ε / 2) + 1 + 2 * MLExpQ_C5 * (1 + Real.log Lr) * N ^ (ε / 4)
      = N ^ (ε / 2) + 1 + 2 * MLExpQ_C5 * ((1 + Real.log Lr) * N ^ (ε / 4)) := by ring
    _ ≤ N ^ (ε / 2) + N ^ (ε / 2) + 2 * MLExpQ_C5 * ((1 + 4 / ε) * N ^ (ε / 2)) := by
        gcongr
    _ = (2 + 2 * MLExpQ_C5 * (1 + 4 / ε)) * N ^ (ε / 2) := by ring
    _ ≤ N ^ (ε / 2) * N ^ (ε / 2) := by gcongr
    _ = N ^ ε := hq4

/-- The endpoint absorption: `C₅ (1+log L) N^{ε/4} ≤ N^ε` for `N` large. -/
theorem MLExpQ_absorb_one {N Lr ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hLN : Lr ≤ N) (hL1 : 1 ≤ Lr)
    (hK : 2 + 2 * MLExpQ_C5 * (1 + 4 / ε) ≤ N ^ (ε / 2)) :
    MLExpQ_C5 * (1 + Real.log Lr) * N ^ (ε / 4) ≤ N ^ ε := by
  have h := MLExpQ_absorb hN hε hLN hL1 hK
  have hN0 : 0 < N := by linarith
  have h1 : 0 ≤ N ^ (ε / 2) := by positivity
  have hlog : 0 ≤ 1 + Real.log Lr := by
    have := Real.log_nonneg hL1; linarith
  have hC5 := MLExpQ_C5_pos
  have h2 : 0 ≤ MLExpQ_C5 * (1 + Real.log Lr) * N ^ (ε / 4) := by positivity
  linarith

/-- `K W^s exp(-W^{τ'}/40000) ≤ 1` for large `W`: the stretched exponential beats every power. -/
theorem MLExpQ_expdecay (τ' s K : ℝ) (hτ' : 0 < τ') :
    ∀ᶠ W : ℝ in atTop, K * (W ^ s * Real.exp (-(1 / 40000) * W ^ τ')) ≤ 1 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (s / τ') * Real.exp (-(1 / 40000) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / τ') (1 / 40000) (by norm_num)
  have h2 : Tendsto (fun W : ℝ => W ^ τ') atTop atTop := tendsto_rpow_atTop hτ'
  have h3 : Tendsto (fun W : ℝ => K * ((W ^ τ') ^ (s / τ') *
      Real.exp (-(1 / 40000) * W ^ τ'))) atTop (nhds (K * 0)) :=
    (h1.comp h2).const_mul K
  have h4 : ∀ᶠ W : ℝ in atTop, K * ((W ^ τ') ^ (s / τ') *
      Real.exp (-(1 / 40000) * W ^ τ')) ≤ 1 :=
    h3.eventually_le_const (by simp)
  filter_upwards [h4, eventually_ge_atTop (0 : ℝ)] with W hW hW0
  rwa [← Real.rpow_mul hW0, mul_div_cancel₀ _ hτ'.ne'] at hW

/-- The scale facts for `0 ≤ u ≤ t < 1` under the bandwidth and range conditions. -/
theorem MLExpQ_scale_facts {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (hW : 1 ≤ W)
    {E c τ t u m₀ : ℝ} (hE : |E| < 2) (hc : 0 < c) (hτ : 0 < τ) (hm₀0 : 0 < m₀)
    (hm₀ : m₀ ≤ (spectralM E).im) (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hcW : (((W * L) ^ 2 : ℕ) : ℝ) ^ c ≤ W)
    (hrange : (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t) :
    m₀ ≤ scaleM L W E u ∧ (etaT E u)⁻¹ ≤ (((W * L) ^ 2 : ℕ) : ℝ) / m₀ ∧
      etaT E u ≤ 1 - u ∧ 1 ≤ (etaT E u)⁻¹ := by
  have hL1 : 1 ≤ L := by omega
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have h := scaleM_etaT_of_range (E := E) hL1 hW hE hc hτ ht1 hcW hrange
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (W * L) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hW hL1)
    rw [hN]; exact_mod_cast this
  have him0 : 0 < (spectralM E).im := spectralM_im_pos hE
  have him1 : (spectralM E).im ≤ 1 := MLExpVocab_im_le_one E
  have hN0 : 0 < N := by linarith
  have hmin : 0 ≤ min (2 * c) τ := le_min (by linarith) hτ.le
  have hNm : 1 ≤ N ^ (min (2 * c) τ) := Real.one_le_rpow hN1 hmin
  have hMt : m₀ ≤ scaleM L W E t := by
    calc m₀ ≤ (spectralM E).im := hm₀
      _ = (spectralM E).im * 1 := (mul_one _).symm
      _ ≤ (spectralM E).im * N ^ (min (2 * c) τ) := mul_le_mul_of_nonneg_left hNm him0.le
      _ ≤ scaleM L W E t := h.1
  have hMu : scaleM L W E t ≤ scaleM L W E u := (scaleM_anti_ratio (W := W) hL1 hE hut ht1).1
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hηt : 0 < etaT E t := etaT_pos hE ht1
  have hηle : etaT E t ≤ etaT E u := by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) him0.le
  have hηinv : (etaT E u)⁻¹ ≤ (etaT E t)⁻¹ := inv_anti₀ hηt hηle
  have hN1τ : N ^ (1 - τ) ≤ N := by
    calc N ^ (1 - τ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one N
  refine ⟨hMt.trans hMu, ?_, ?_, ?_⟩
  · calc (etaT E u)⁻¹ ≤ (etaT E t)⁻¹ := hηinv
      _ ≤ N ^ (1 - τ) / (spectralM E).im := h.2
      _ ≤ N / (spectralM E).im := by gcongr
      _ ≤ N / m₀ := by gcongr
  · unfold etaT
    calc (1 - u) * (spectralM E).im ≤ (1 - u) * 1 :=
          mul_le_mul_of_nonneg_left him1 (by linarith)
      _ = 1 - u := mul_one _
  · rw [one_le_inv₀ hηu]
    unfold etaT
    calc (1 - u) * (spectralM E).im ≤ 1 * 1 :=
          mul_le_mul (by linarith) him1 him0.le zero_le_one
      _ = 1 := one_mul 1

end Numeric

/-! ## The source `𝒬D + T₂` and its bounds -/

section Source

variable {L : ℕ} [NeZero L]

/-- The `𝒫f`-part of the source: `A_u = 𝒬_u D_u + T₂`,
`T₂(b) = Σ_c (SΘ_u)(b₀,c) (𝒫f)_c (ϑ_{(c,b₁)} - ϑ_b)` (`MLExpQ_qDrift_eq`). -/
def MLExpQ_T2 (L : ℕ) [NeZero L] (u : ℝ) (f : (Fin 2 → Z2 L) → ℂ) (b : Fin 2 → Z2 L) : ℂ :=
  ∑ c : Z2 L, (SB L * Theta L (u : ℂ)) (b 0) c * Psum L f c *
    (vartheta L u ![c, b 1] - vartheta L u b)

/-- `‖ϑ_{(x,y)}‖ ≤ c_L(u)`. -/
theorem MLExpQ_vartheta_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    ‖vartheta L u ![x, y]‖ ≤ MLExpQ_c L u := by
  refine (MLExpQ_vartheta_decay hL hu0 hu1 x y).trans ?_
  refine mul_le_of_le_one_right (MLExpQ_c_nonneg L u) (Real.exp_le_one_iff.mpr ?_)
  have hℓ : 0 < ellT L u := (ellT_pos_le (by omega) hu1).1
  exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)

/-- A pair of labels is `(b₀, b₁)`. -/
theorem MLExpQ_eta_two (b : Fin 2 → Z2 L) : b = ![b 0, b 1] := by
  funext i; fin_cases i <;> simp

theorem MLExpQ_T2_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {f : (Fin 2 → Z2 L) → ℂ} {P : ℝ} (hP0 : 0 ≤ P) (hP : ∀ x, ‖Psum L f x‖ ≤ P)
    (b : Fin 2 → Z2 L) :
    ‖MLExpQ_T2 L u f b‖ ≤ (1 - u)⁻¹ * (P * (2 * MLExpQ_c L u)) := by
  have h := MLExpQ_T2_size (Kf := fun x c => (SB L * Theta L (u : ℂ)) x c) (p := Psum L f)
    (ϑ := fun x y => vartheta L u ![x, y]) (K₀ := (1 - u)⁻¹) (P := P) (θ := MLExpQ_c L u)
    (fun x => MLExpQ_K_row_le hL hu0 hu1 x) hP (fun x y => MLExpQ_vartheta_le hL hu0 hu1 x y)
    hP0 (MLExpQ_c_nonneg L u) (b 0) (b 1)
  rw [← MLExpQ_eta_two b] at h
  exact h

theorem MLExpQ_T2_far (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {f : (Fin 2 → Z2 L) → ℂ} {P : ℝ} (hP0 : 0 ≤ P) (hP : ∀ x, ‖Psum L f x‖ ≤ P)
    {R : ℝ} (hR : 0 ≤ R) {b : Fin 2 → Z2 L} (hb : R ≤ (zdist2 L (b 0 - b 1) : ℝ)) :
    ‖MLExpQ_T2 L u f b‖ ≤
      P * (5 * ((1 - u)⁻¹ * MLExpQ_c L u)) * Real.exp (-R / (2 * (20000 * ellT L u))) := by
  have h1u : 0 < 1 - u := by linarith
  have hℓ : 1 ≤ ellT L u := one_le_ellT (by omega) hu0 hu1
  have hlam : 0 < 20000 * ellT L u := by linarith
  have hc0 := MLExpQ_c_nonneg L u
  have hinv : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr h1u.le
  have h := MLExpQ_T2_decay (Kf := fun x c => (SB L * Theta L (u : ℂ)) x c) (p := Psum L f)
    (ϑ := fun x y => vartheta L u ![x, y]) (K₀ := (1 - u)⁻¹)
    (κ₁ := 3 * ((1 - u)⁻¹ * MLExpQ_c L u)) (P := P) (θ := MLExpQ_c L u)
    (lam := 20000 * ellT L u) (R := R) hlam
    (fun x => MLExpQ_K_row_le hL hu0 hu1 x) (fun x c => MLExpQ_K_decay hL hu0 hu1 x c) hP
    (fun x y => MLExpQ_vartheta_decay hL hu0 hu1 x y)
    (fun y => MLExpQ_vartheta_col_le hL hu0 hu1 y) hP0 hc0 (by positivity) hinv hR hb
  rw [← MLExpQ_eta_two b] at h
  refine h.trans (le_of_eq ?_)
  ring

theorem MLExpQ_zdist2_sub_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  have h : ∀ u : ZMod L, zdist L (-u) = zdist L u := by
    intro u
    by_cases h0 : u = 0
    · simp [h0]
    · have hu : u.val < L := ZMod.val_lt u
      have hne : u.val ≠ 0 := by
        intro h1; exact h0 ((ZMod.val_eq_zero u).1 h1)
      simp only [zdist, ZMod.neg_val, h0, ite_false]
      omega
  have h2 : ∀ u : Z2 L, zdist2 L (-u) = zdist2 L u := by
    intro u
    simp only [zdist2, Prod.fst_neg, Prod.snd_neg, h]
  rw [← h2, neg_sub]

/-- `max_{p,q} |a_p - a_q|_L ≤ |a_0 - a_1|_L` for a pair of labels (copy of
`MLExpDrift_maxDist_two`). -/
theorem MLExpQ_maxDist_two (a : Fin 2 → Z2 L) :
    (KLoop.maxDist L a : ℝ) ≤ (zdist2 L (a 0 - a 1) : ℝ) := by
  have h : KLoop.maxDist L a ≤ zdist2 L (a 0 - a 1) := by
    unfold KLoop.maxDist
    refine Finset.sup_le fun p _ => ?_
    have h01 : zdist2 L (a 1 - a 0) = zdist2 L (a 0 - a 1) := MLExpQ_zdist2_sub_comm _ _
    fin_cases p <;> simp [h01]
  exact_mod_cast h

/-- `‖A‖_max ≤ X` from a pointwise bound. -/
theorem MLExpQ_tmax_le {k : ℕ} {A : (Fin k → Z2 L) → ℂ} {X : ℝ}
    (h : ∀ a, ‖A a‖ ≤ X) : tmax L A ≤ X :=
  Finset.sup'_le _ _ fun a _ => h a

/-- `‖A_a‖ ≤ ‖A‖_max`. -/
theorem MLExpQ_le_tmax {k : ℕ} (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ‖A a‖ ≤ tmax L A :=
  Finset.le_sup' (fun a => ‖A a‖) (Finset.mem_univ a)

/-- `0 ≤ ‖A‖_max`. -/
theorem MLExpQ_tmax_nonneg {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : 0 ≤ tmax L A :=
  (norm_nonneg _).trans (MLExpQ_le_tmax A (fun _ => 0))

/-- `(W² η_u)⁻¹ = ℓ_u² M_u⁻¹` (`M_u = W² ℓ_u² η_u`). -/
theorem MLExpQ_Winv {L W : ℕ} {E u : ℝ} (hW : 0 < W) (hη : 0 < etaT E u)
    (hℓ : 0 < ellT L u) :
    (((W : ℝ) ^ 2) * etaT E u)⁻¹ = ellT L u ^ 2 * (scaleM L W E u)⁻¹ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold scaleM
  field_simp

end Source

section SourceSeq

variable (d : Sizes)

theorem MLExpQ_qDriftT_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {σ : Fin 2 → Bool} (hσ : Alternating σ) (b : Fin 2 → Z2 (d.L n)) :
    qDriftT d n E u σ b =
      Qop (d.L n) u (expDriftT d n E u σ) b + MLExpQ_T2 (d.L n) u (expErrT d n E u σ) b :=
  MLExpQ_qDrift_eq (d.three_le_L n) hE hu0 hu1 hσ _ _ b

end SourceSeq

/-! ## The main theorem -/

section Main

variable (d : Sizes)

/-- **`ExpQBound`** (the `𝒬`-terms, alternating `σ`).  Under `MLExpHyps`, the conclusion
`ExpDriftBoundConcl` and `ExpInvariant`, for every `ε, τ', D > 0`, eventually in `n`: for every
`u ∈ [0,t_n]` and alternating `σ`, `A_u = qDriftT` is sum-zero, symmetric, `(u,τ',D)`-decaying with
`‖A_u‖_max ≤ N^ε η_u^{-1} M_u^{-3}`; and `‖(𝒫 f_t) ϑ_t‖ ≤ N^ε M_t^{-3}`.  This is the statement
`ExpQBound` with no added hypothesis.  The argument is in the module docstring: the exact
closed form `MLExpQ_qDrift_eq`, the Ward bound `MLExpQ_norm_Psum_expErr` with `step61_unif`, the
kernel bounds of property 5, `qopNorm` and `qopDecay`. -/
theorem expQBound (κ c τ : ℝ) (E t : ℕ → ℝ) : ExpQBound d κ c τ E t := by
  intro hH hDC hInv ε hε τ' hτ' D hD
  obtain ⟨hκ, hc, hτ, hE, ht0, ht1, hsz, hbw, hrc, hK, h4, hDL, h61⟩ := hH
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  -- the constants
  have hε₁ : 0 < ε / 4 := by positivity
  have hcP : 0 < cPrec c 2 := by unfold cPrec; positivity
  have hτ₀ : 0 < ε / (2 * (cPrec c 2 + 1)) := by positivity
  have hDin₁ : 0 < cPrec c 2 + 6 := by positivity
  have hDin₂ : 0 < D + 1 + (1 + ε / 4) / c := by positivity
  have hcP' : cPrec c 2 * (ε / (2 * (cPrec c 2 + 1))) ≤ ε / 2 := by
    have h1 : cPrec c 2 * (ε / (2 * (cPrec c 2 + 1))) =
        (cPrec c 2 / (cPrec c 2 + 1)) * (ε / 2) := by field_simp
    rw [h1]
    have h2 : cPrec c 2 / (cPrec c 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    exact mul_le_of_le_one_left (by positivity) h2
  have hm₀0 : 0 < Real.sqrt (2 * κ) / 2 := by
    have : 0 < 2 * κ := by linarith
    positivity
  -- the eventual facts
  have hNc : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp hsz
  have hWt : Tendsto (fun n => (d.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hbw.mono fun n hn => hn) hNc
  have hstep := step61_unif d ht0 h61 (ε / 4) hε₁
  have hdr1 := hDC (ε / 4) hε₁ (ε / (2 * (cPrec c 2 + 1))) hτ₀ (cPrec c 2 + 6) hDin₁
  have hdr2 := hDC (ε / 4) hε₁ τ' hτ' (D + 1 + (1 + ε / 4) / c) hDin₂
  have hqn := hsize.eventually (qopNorm c hc 2 le_rfl (ε / (2 * (cPrec c 2 + 1)))
    (cPrec c 2 + 6) hτ₀ hDin₁)
  have hqd := hsize.eventually (qopDecay c hc 2 le_rfl τ' (D + 1 + (1 + ε / 4) / c) hτ' hDin₂)
  have hZ := hsize.eventually (eventually_le_rpow (2 + 2 * MLExpQ_C5 * (1 + 4 / ε))
    (show 0 < ε / 2 by positivity))
  set mi : ℝ := (Real.sqrt (2 * κ) / 2)⁻¹ with hmi
  have hexp := hWt.eventually (MLExpQ_expdecay τ' ((2 + ε / 4) / c + D)
    (10 * MLExpQ_C5 * mi ^ 4) hτ')
  have hWbig := hWt.eventually_ge_atTop (2 * (2 + mi ^ 4))
  have hN1e := hsize.eventually_ge_atTop 1
  filter_upwards [hbw, hrc, hstep, hdr1, hdr2, hqn, hqd, hZ, hexp, hWbig, hN1e] with
    n hbwn hrcn hstepn hdr1n hdr2n hqnn hqdn hZn hexpn hWbign hN1
  -- facts at this size index
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hWpos : 0 < d.W n := d.W_pos n
  have hW1 : (1 : ℝ) ≤ ((d.W n : ℕ) : ℝ) := by exact_mod_cast hWpos
  have hN1r : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hsizeeq : d.W n ^ 2 * d.L n ^ 2 = d.size n := (Sizes.size_eq d n).symm
  have hWN : ((d.W n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
    have h : d.W n ^ 2 ≤ d.size n := by
      rw [Sizes.size_eq]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    exact_mod_cast h
  have hLN : ((d.L n : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have h : d.L n ≤ d.size n := by
      rw [Sizes.size_eq]
      calc d.L n ≤ d.L n ^ 2 := Nat.le_self_pow (by norm_num) _
        _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    exact_mod_cast h
  have hL1r : (1 : ℝ) ≤ ((d.L n : ℕ) : ℝ) := by exact_mod_cast hL1
  have hEn' : |E n| ≤ 2 - κ := hE n
  have hEn : |E n| < 2 := by linarith
  have him : Real.sqrt (2 * κ) / 2 ≤ (spectralM (E n)).im := MLExpVocab_im_ge hκ hEn'
  have hmi0 : 0 < mi := inv_pos.mpr hm₀0
  have hcW : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) ^ c ≤ (d.W n : ℝ) := hbwn
  have hrange : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n := hrcn
  have hPb : ∀ u ∈ Set.Icc (0 : ℝ) (t n), ∀ σ : Fin 2 → Bool, Alternating σ →
      ∀ x : Z2 (d.L n), ‖Psum (d.L n) (expErrT d n (E n) u σ) x‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
          (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
    intro u hu σ hσ x
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
    have hℓpos : 0 < ellT (d.L n) u := (ellT_pos_le hL1 hu1).1
    have hηpos : 0 < etaT (E n) u := etaT_pos hEn hu1
    have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hL1 hWpos hEn hu1
    refine (MLExpQ_norm_Psum_expErr d n hEn hu0 hu1 hσ x).trans ?_
    rw [MLExpQ_Winv hWpos hηpos hℓpos]
    have h1 := hstepn u hu x
    calc ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ * ‖oneLoopExpErr d n (E n) u x‖
        ≤ ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ *
            (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
            (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
          field_simp
  have hPcall : ∀ u ∈ Set.Icc (0 : ℝ) (t n),
      ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
        (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) * MLExpQ_c (d.L n) u =
      MLExpQ_C5 * (1 + Real.log (d.L n)) *
        (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
    intro u hu
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
    have hℓpos : 0 < ellT (d.L n) u := (ellT_pos_le hL1 hu1).1
    have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hL1 hWpos hEn hu1
    unfold MLExpQ_c
    field_simp
  have key : ∀ u ∈ Set.Icc (0 : ℝ) (t n), ∀ σ : Fin 2 → Bool, Alternating σ →
      SumZero (d.L n) (qDriftT d n (E n) u σ) ∧ Ind.Symmetric (d.L n) (qDriftT d n (E n) u σ) ∧
        HasDecay (d.L n) (d.W n) u τ' D (qDriftT d n (E n) u σ) ∧
        tmax (d.L n) (qDriftT d n (E n) u σ) ≤
          ((d.size n : ℕ) : ℝ) ^ ε *
            ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
    intro u hu σ hσ
    have hu0 : 0 ≤ u := hu.1
    have hut : u ≤ t n := hu.2
    have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 n)
    obtain ⟨hMm, hηN, hη1, hη1'⟩ := MLExpQ_scale_facts (E := E n) hL3 hWpos hEn hc hτ hm₀0 him
      hu0 hut (ht1 n) hcW hrange
    obtain ⟨hf, hDinv⟩ := hInv n (E n) u hEn hu0 hu1 σ
    have hℓpos : 0 < ellT (d.L n) u := (ellT_pos_le hL1 hu1).1
    have hℓ1 : 1 ≤ ellT (d.L n) u := one_le_ellT hL1 hu0 hu1
    have hηpos : 0 < etaT (E n) u := etaT_pos hEn hu1
    have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hL1 hWpos hEn hu1
    have h1u : 0 < 1 - u := by linarith
    have hMle : scaleM (d.L n) (d.W n) (E n) u ≤ ((d.W n : ℕ) : ℝ) ^ 2 :=
      MLExpVocab_scaleM_le_W2 hL1 hu1
    have hP := hPb u hu σ hσ
    have hP0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
        (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by positivity
    have hPc := hPcall u hu
    refine ⟨MLExpQ_sumZero_qDrift hL3 hEn hu0 hu1 hσ _ _,
      TensorInvariant.symmetric (MLExpQ_TensorInv_qDrift hL3 hEn hu0 hu1 hσ hf hDinv), ?_, ?_⟩
    · -- the decay
      intro a ha
      have hWpos' : (0 : ℝ) < ((d.W n : ℕ) : ℝ) := by linarith
      have hQ := hqdn (d.L n) (d.W n) hL3 hsizeeq hbwn u hu0 hu1 _ (hdr2n u hu σ).1 a ha
      have htD := (hdr2n u hu σ).2
      have hR : ellT (d.L n) u * ((d.W n : ℕ) : ℝ) ^ τ' ≤ (zdist2 (d.L n) (a 0 - a 1) : ℝ) :=
        ha.trans (MLExpQ_maxDist_two a)
      have hRnn : 0 ≤ ellT (d.L n) u * ((d.W n : ℕ) : ℝ) ^ τ' := by positivity
      have hT2f := MLExpQ_T2_far hL3 hu0 hu1 hP0 hP hRnn hR
      have hηNmi : (etaT (E n) u)⁻¹ ≤ ((d.size n : ℕ) : ℝ) * mi := by
        have h : ((d.size n : ℕ) : ℝ) / (Real.sqrt (2 * κ) / 2) = ((d.size n : ℕ) : ℝ) * mi := by
          rw [hmi, div_eq_mul_inv]
        exact hηN.trans h.le
      have hM3mi : (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ ≤ mi ^ 3 := by
        have h1 : (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ mi := by
          rw [hmi]; exact inv_anti₀ hm₀0 hMm
        calc (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ = ((scaleM (d.L n) (d.W n) (E n) u)⁻¹) ^ 3 := by
              rw [inv_pow]
          _ ≤ mi ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      -- Term 1: `𝒬 D`
      have htD' : tmax (d.L n) (expDriftT d n (E n) u σ) ≤
          mi ^ 4 * (((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (ε / 4)) := by
        calc tmax (d.L n) (expDriftT d n (E n) u σ)
            ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
                ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := htD
          _ ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 4) * ((((d.size n : ℕ) : ℝ) * mi) * mi ^ 3) := by
              gcongr
          _ = mi ^ 4 * (((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (ε / 4)) := by ring
      have hNrε : ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) =
          ((d.size n : ℕ) : ℝ) ^ (1 + ε / 4) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
      have hNrε1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ (1 + ε / 4) :=
        Real.one_le_rpow hN1r (by positivity)
      have h2t : 2 + tmax (d.L n) (expDriftT d n (E n) u σ) ≤
          (2 + mi ^ 4) * ((d.size n : ℕ) : ℝ) ^ (1 + ε / 4) := by
        rw [hNrε] at htD'
        linarith [hNrε1]
      have hpoly : ((d.size n : ℕ) : ℝ) ^ (1 + ε / 4) ≤ ((d.W n : ℕ) : ℝ) ^ ((1 + ε / 4) / c) :=
        MLExpQ_N_poly hN0.le hc hbwn (by positivity)
      have hterm1 : ‖Qop (d.L n) u (expDriftT d n (E n) u σ) a‖ ≤
          (2 + mi ^ 4) * ((d.W n : ℕ) : ℝ) ^ (-(D + 1)) := by
        calc ‖Qop (d.L n) u (expDriftT d n (E n) u σ) a‖
            ≤ ((d.W n : ℕ) : ℝ) ^ (-(D + 1 + (1 + ε / 4) / c)) *
                (2 + tmax (d.L n) (expDriftT d n (E n) u σ)) := hQ
          _ ≤ ((d.W n : ℕ) : ℝ) ^ (-(D + 1 + (1 + ε / 4) / c)) *
                ((2 + mi ^ 4) * ((d.W n : ℕ) : ℝ) ^ ((1 + ε / 4) / c)) := by
              gcongr
              exact h2t.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))
          _ = (2 + mi ^ 4) * ((d.W n : ℕ) : ℝ) ^ (-(D + 1)) := by
              rw [show -(D + 1 + (1 + ε / 4) / c) = -(D + 1) - (1 + ε / 4) / c by ring,
                Real.rpow_sub hWpos']
              have : ((d.W n : ℕ) : ℝ) ^ ((1 + ε / 4) / c) ≠ 0 := (Real.rpow_pos_of_pos hWpos' _).ne'
              field_simp
      have hWD1 : ((d.W n : ℕ) : ℝ) ^ (-D) =
          ((d.W n : ℕ) : ℝ) ^ (-(D + 1)) * ((d.W n : ℕ) : ℝ) := by
        rw [show -D = -(D + 1) + 1 by ring, Real.rpow_add hWpos', Real.rpow_one]
      have hterm1' : (2 + mi ^ 4) * ((d.W n : ℕ) : ℝ) ^ (-(D + 1)) ≤
          ((d.W n : ℕ) : ℝ) ^ (-D) / 2 := by
        have hw : 0 < ((d.W n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_pos_of_pos hWpos' _
        rw [hWD1]
        have := mul_le_mul_of_nonneg_left hWbign hw.le
        linarith
      -- Term 2: the source `T₂`
      have hexp' : Real.exp (-(ellT (d.L n) u * ((d.W n : ℕ) : ℝ) ^ τ') /
          (2 * (20000 * ellT (d.L n) u))) =
          Real.exp (-(1 / 40000) * ((d.W n : ℕ) : ℝ) ^ τ') := by
        congr 1
        field_simp
        ring
      have hlogle : 1 + Real.log (d.L n) ≤ ((d.size n : ℕ) : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d.L n : ℝ) by linarith)
        linarith
      have hlog0 : 0 ≤ 1 + Real.log (d.L n) := by
        have := Real.log_natCast_nonneg (d.L n); linarith
      have h1uη : (1 - u)⁻¹ ≤ (etaT (E n) u)⁻¹ := inv_anti₀ hηpos hη1
      have hC5 := MLExpQ_C5_pos
      have hpc2 : ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
          (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) *
            (5 * ((1 - u)⁻¹ * MLExpQ_c (d.L n) u)) =
          5 * ((1 - u)⁻¹ * (MLExpQ_C5 * (1 + Real.log (d.L n)) *
            (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹))) := by
        rw [← hPc]; ring
      have h5 : ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
          (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) *
            (5 * ((1 - u)⁻¹ * MLExpQ_c (d.L n) u)) ≤
          5 * MLExpQ_C5 * mi ^ 4 * (((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) *
            ((d.size n : ℕ) : ℝ) ^ (ε / 4)) := by
        rw [hpc2]
        calc 5 * ((1 - u)⁻¹ * (MLExpQ_C5 * (1 + Real.log (d.L n)) *
              (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹)))
            ≤ 5 * ((((d.size n : ℕ) : ℝ) * mi) * (MLExpQ_C5 * ((d.size n : ℕ) : ℝ) *
              (((d.size n : ℕ) : ℝ) ^ (ε / 4) * mi ^ 3))) := by
              gcongr
              exact h1uη.trans hηNmi
          _ = 5 * MLExpQ_C5 * mi ^ 4 * (((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) *
              ((d.size n : ℕ) : ℝ) ^ (ε / 4)) := by ring
      have hNN2 : ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) =
          ((d.size n : ℕ) : ℝ) ^ (2 + ε / 4) := by
        rw [Real.rpow_add hN0, show ((d.size n : ℕ) : ℝ) ^ (2 : ℝ) =
          ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) by rw [Real.rpow_two]; ring]
      have hpoly2 : ((d.size n : ℕ) : ℝ) ^ (2 + ε / 4) ≤ ((d.W n : ℕ) : ℝ) ^ ((2 + ε / 4) / c) :=
        MLExpQ_N_poly hN0.le hc hbwn (by positivity)
      have hterm2 : ‖MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) a‖ ≤
          5 * MLExpQ_C5 * mi ^ 4 * ((d.W n : ℕ) : ℝ) ^ ((2 + ε / 4) / c) *
            Real.exp (-(1 / 40000) * ((d.W n : ℕ) : ℝ) ^ τ') := by
        refine hT2f.trans ?_
        rw [hexp']
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine h5.trans ?_
        rw [hNN2]
        exact mul_le_mul_of_nonneg_left hpoly2 (by positivity)
      have hterm2' : 5 * MLExpQ_C5 * mi ^ 4 * ((d.W n : ℕ) : ℝ) ^ ((2 + ε / 4) / c) *
            Real.exp (-(1 / 40000) * ((d.W n : ℕ) : ℝ) ^ τ') ≤
          ((d.W n : ℕ) : ℝ) ^ (-D) / 2 := by
        set s₁ : ℝ := (2 + ε / 4) / c with hs₁
        set ee : ℝ := Real.exp (-(1 / 40000) * ((d.W n : ℕ) : ℝ) ^ τ') with hee
        have hWD : ((d.W n : ℕ) : ℝ) ^ (-D) * ((d.W n : ℕ) : ℝ) ^ D = 1 := by
          rw [← Real.rpow_add hWpos']; simp
        have hsplit : ((d.W n : ℕ) : ℝ) ^ (s₁ + D) =
            ((d.W n : ℕ) : ℝ) ^ s₁ * ((d.W n : ℕ) : ℝ) ^ D := Real.rpow_add hWpos' _ _
        rw [hsplit] at hexpn
        have hw : 0 < ((d.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hWpos' _
        have h1 := mul_le_mul_of_nonneg_left hexpn hw.le
        have h2 : ((d.W n : ℕ) : ℝ) ^ (-D) * (10 * MLExpQ_C5 * mi ^ 4 *
            (((d.W n : ℕ) : ℝ) ^ s₁ * ((d.W n : ℕ) : ℝ) ^ D * ee)) =
            10 * MLExpQ_C5 * mi ^ 4 * ((d.W n : ℕ) : ℝ) ^ s₁ * ee := by
          calc _ = 10 * MLExpQ_C5 * mi ^ 4 * ((d.W n : ℕ) : ℝ) ^ s₁ * ee *
                (((d.W n : ℕ) : ℝ) ^ (-D) * ((d.W n : ℕ) : ℝ) ^ D) := by ring
            _ = _ := by rw [hWD, mul_one]
        rw [h2, mul_one] at h1
        linarith
      rw [MLExpQ_qDriftT_eq d n hEn hu0 hu1 hσ a]
      calc ‖Qop (d.L n) u (expDriftT d n (E n) u σ) a +
            MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) a‖
          ≤ ‖Qop (d.L n) u (expDriftT d n (E n) u σ) a‖ +
            ‖MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) a‖ := norm_add_le _ _
        _ ≤ ((d.W n : ℕ) : ℝ) ^ (-D) / 2 + ((d.W n : ℕ) : ℝ) ^ (-D) / 2 :=
            add_le_add (hterm1.trans hterm1') (hterm2.trans hterm2')
        _ = ((d.W n : ℕ) : ℝ) ^ (-D) := by ring
    · -- the size bound
      refine MLExpQ_tmax_le fun b => ?_
      rw [MLExpQ_qDriftT_eq d n hEn hu0 hu1 hσ b]
      have hT2 := MLExpQ_T2_le hL3 hu0 hu1 hP0 hP b
      have hQ1 := hqnn (d.L n) (d.W n) hL3 hsizeeq hbwn u hu0 hu1 _ (hdr1n u hu σ).1
      have hQb := (MLExpQ_le_tmax (Qop (d.L n) u (expDriftT d n (E n) u σ)) b).trans hQ1
      have htD := (hdr1n u hu σ).2
      have hW1' : ((d.W n : ℕ) : ℝ) ^ (cPrec c 2 * (ε / (2 * (cPrec c 2 + 1)))) ≤
          ((d.size n : ℕ) : ℝ) ^ (ε / 4) := by
        have hx0 : 0 ≤ cPrec c 2 * (ε / (2 * (cPrec c 2 + 1))) := by positivity
        have h := MLExpVocab_rpow_le hW1 hWN (x := cPrec c 2 * (ε / (2 * (cPrec c 2 + 1))))
        rw [abs_of_nonneg hx0] at h
        exact h.trans (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith))
      have hW2' : ((d.W n : ℕ) : ℝ) ^ (-(cPrec c 2 + 6) + cPrec c 2) ≤
          (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ := by
        have h1 : -(cPrec c 2 + 6) + cPrec c 2 = -(6 : ℝ) := by ring
        have h2 : ((d.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) = (((d.W n : ℕ) : ℝ) ^ 6)⁻¹ := by
          rw [Real.rpow_neg (by linarith)]
          norm_cast
        have h3 : scaleM (d.L n) (d.W n) (E n) u ^ 3 ≤ ((d.W n : ℕ) : ℝ) ^ 6 := by
          calc scaleM (d.L n) (d.W n) (E n) u ^ 3 ≤ (((d.W n : ℕ) : ℝ) ^ 2) ^ 3 :=
                pow_le_pow_left₀ hMpos.le hMle 3
            _ = ((d.W n : ℕ) : ℝ) ^ 6 := by ring
        rw [h1, h2]
        exact inv_anti₀ (by positivity) h3
      set X : ℝ := (etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ with hX
      have hX0 : 0 ≤ X := by positivity
      have hM3 : (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ ≤ X := by
        calc (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹
            = 1 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹ := (one_mul _).symm
          _ ≤ X := mul_le_mul_of_nonneg_right hη1' (by positivity)
      have hQd : ‖Qop (d.L n) u (expDriftT d n (E n) u σ) b‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (ε / 4) * (((d.size n : ℕ) : ℝ) ^ (ε / 4) * X) + X := by
        refine hQb.trans (add_le_add ?_ (hW2'.trans hM3))
        exact mul_le_mul hW1' htD (MLExpQ_tmax_nonneg _) (by positivity)
      have h1uη : (1 - u)⁻¹ ≤ (etaT (E n) u)⁻¹ := inv_anti₀ hηpos hη1
      have hT2' : ‖MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) b‖ ≤
          2 * MLExpQ_C5 * (1 + Real.log (d.L n)) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) * X := by
        refine hT2.trans ?_
        have hcalc : (1 - u)⁻¹ * (((d.size n : ℕ) : ℝ) ^ (ε / 4) *
            (ellT (d.L n) u ^ 2 * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) *
              (2 * MLExpQ_c (d.L n) u)) =
            2 * ((1 - u)⁻¹ * (MLExpQ_C5 * (1 + Real.log (d.L n)) *
              (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹))) := by
          rw [← hPc]; ring
        rw [hcalc]
        have hnn : 0 ≤ MLExpQ_C5 * (1 + Real.log (d.L n)) *
            (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
          have hlog : 0 ≤ 1 + Real.log (d.L n) := by
            have := Real.log_natCast_nonneg (d.L n); linarith
          have := MLExpQ_C5_pos
          positivity
        calc 2 * ((1 - u)⁻¹ * (MLExpQ_C5 * (1 + Real.log (d.L n)) *
              (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹)))
            ≤ 2 * ((etaT (E n) u)⁻¹ * (MLExpQ_C5 * (1 + Real.log (d.L n)) *
              (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹))) := by
              gcongr
          _ = 2 * MLExpQ_C5 * (1 + Real.log (d.L n)) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) * X := by
              rw [hX]; ring
      have habs := MLExpQ_absorb hN1r hε hLN hL1r hZn
      have hNN : ((d.size n : ℕ) : ℝ) ^ (ε / 4) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) =
          ((d.size n : ℕ) : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_add hN0]; ring_nf
      calc ‖Qop (d.L n) u (expDriftT d n (E n) u σ) b +
            MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) b‖
          ≤ ‖Qop (d.L n) u (expDriftT d n (E n) u σ) b‖ +
            ‖MLExpQ_T2 (d.L n) u (expErrT d n (E n) u σ) b‖ := norm_add_le _ _
        _ ≤ (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (((d.size n : ℕ) : ℝ) ^ (ε / 4) * X) + X) +
            2 * MLExpQ_C5 * (1 + Real.log (d.L n)) * ((d.size n : ℕ) : ℝ) ^ (ε / 4) * X :=
            add_le_add hQd hT2'
        _ = X * (((d.size n : ℕ) : ℝ) ^ (ε / 2) + 1 +
            2 * MLExpQ_C5 * (1 + Real.log (d.L n)) * ((d.size n : ℕ) : ℝ) ^ (ε / 4)) := by
            rw [← hNN]; ring
        _ ≤ X * ((d.size n : ℕ) : ℝ) ^ ε := mul_le_mul_of_nonneg_left habs hX0
        _ = ((d.size n : ℕ) : ℝ) ^ ε * X := mul_comm _ _
  refine ⟨fun u hu σ hσ => key u hu σ hσ, fun σ hσ a => ?_⟩
  -- the endpoint clause at `u = t n`
  have hu : t n ∈ Set.Icc (0 : ℝ) (t n) := ⟨ht0 n, le_rfl⟩
  have hu0 : 0 ≤ t n := ht0 n
  have hu1 : t n < 1 := ht1 n
  have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) (t n) := scaleM_pos hL1 hWpos hEn hu1
  have hP := hPb (t n) hu σ hσ
  have hP0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 4) *
      (ellT (d.L n) (t n) ^ 2 * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹) := by positivity
  have hPc := hPcall (t n) hu
  have hϑ := MLExpQ_vartheta_le hL3 hu0 hu1 (a 0) (a 1)
  rw [← MLExpQ_eta_two a] at hϑ
  have hstepc := MLExpQ_absorb_one hN1r hε hLN hL1r hZn
  calc ‖Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0) * vartheta (d.L n) (t n) a‖
      = ‖Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0)‖ * ‖vartheta (d.L n) (t n) a‖ :=
        norm_mul _ _
    _ ≤ (((d.size n : ℕ) : ℝ) ^ (ε / 4) *
          (ellT (d.L n) (t n) ^ 2 * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹)) *
          MLExpQ_c (d.L n) (t n) := mul_le_mul (hP (a 0)) hϑ (norm_nonneg _) hP0
    _ = MLExpQ_C5 * (1 + Real.log (d.L n)) *
          (((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹) := hPc
    _ = (MLExpQ_C5 * (1 + Real.log (d.L n)) * ((d.size n : ℕ) : ℝ) ^ (ε / 4)) *
          (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ := by ring
    _ ≤ ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hstepc (by positivity)

end Main

end RBM.Evol
