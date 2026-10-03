/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Propagator.Deriv

/-!
# The algebra of `𝒫`, `ϑ_t`, `𝒬_t`

The theorem `qopAlgebra : QopAlgebra` (the statement `QopAlgebra` of `RBM2D.Induction.HierVocab`):
`𝒫ϑ_t = 1`, `𝒫∘𝒬_t = 0`, `𝒬_t = id` on sum-zero tensors, `𝒫ϑ̇_t = 0`, the closed form of `ϑ̇_t`
(`∂_tΘ_t = Θ_tSΘ_t`), `ϴ_{t,σ}` preserves sum-zero, and the commutator formula for `[𝒬_t, ϴ_{t,σ}]`
(`Def:QtPt`, `pqthlk`; the generator carries the factor `S` on the left).

Everything is finite-size algebra on `Fin k → Z2 L`; there is no `∀ᶠ N`.

The lemmas parallel the one-dimensional ones, where `LoopArg L (n+1)` is split by `Fin.cons`;
here the splitting is the filter `a 0 = a₁`:
* `SumZeroQ_Psum_vartheta` (`𝒫ϑ_t = 1`) and `SumZeroQ_Psum_Qop` (`𝒫∘𝒬_t = 0`);
* `SumZeroQ_hasDerivAt_vartheta` and `SumZeroQ_Psum_varthetaDot`;
* `SumZeroQ_slot_succ` and `SumZeroQ_slot_zero` (the slot-by-slot sums of `ϴ`),
  `SumZeroQ_col_sum_thetaGenMat` and `SumZeroQ_SumZero_thetaSig`;
* `SumZeroQ_SB_mul_Theta_symm` and `SumZeroQ_col_sum` (column sums of `S Θ`, the generator has `S`
  on the left).
The commutator is linearity of `thetaSig` (`SumZeroQ_thetaSig_sub`), and no norm bound on the
generator is used.  Specific to this file: the factorisation `SumZeroQ_sum_filter_prod`, the analogue of the
one-dimensional product-sum lemma, on the filter `a 0 = a₁`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Finset Matrix RBM RBM.Gauss RBM.Path

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-! ## 1. Factorisation of a sum over `{a : a 0 = a₁}` -/

/-- **The factorisation** `Σ_{a : a₀ = a₁} Π_{i ≠ 0} g_i(a_i) = Π_{i ≠ 0} Σ_b g_i(b)` (on the
filter `a 0 = a₁` instead of `Fin.cons`). -/
theorem SumZeroQ_sum_filter_prod {R : Type*} [CommSemiring R] (a₁ : Z2 L) (g : Fin k → Z2 L → R) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
        ∏ i ∈ Finset.univ.erase (0 : Fin k), g i (a i)
      = ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, g i b := by
  classical
  set g' : Fin k → Z2 L → R := fun i b => if i = 0 then (if b = a₁ then 1 else 0) else g i b
    with hg'
  have h1 : ∏ i, ∑ b, g' i b = ∑ a : Fin k → Z2 L, ∏ i, g' i (a i) := Fintype.prod_sum g'
  have h2 : ∏ i, ∑ b, g' i b = ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, g i b := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ b, g' i b) (Finset.mem_univ (0 : Fin k))]
    have h0 : ∑ b, g' 0 b = 1 := by simp [hg']
    rw [h0, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    simp [hg', hi0]
  have h3 : ∑ a : Fin k → Z2 L, ∏ i, g' i (a i)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          ∏ i ∈ Finset.univ.erase (0 : Fin k), g i (a i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g' i (a i)) (Finset.mem_univ (0 : Fin k))]
    have h4 : ∏ i ∈ Finset.univ.erase (0 : Fin k), g' i (a i)
        = ∏ i ∈ Finset.univ.erase (0 : Fin k), g i (a i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
      simp [hg', hi0]
    rw [h4]
    by_cases ha : a 0 = a₁ <;> simp [hg', ha]
  rw [← h2, h1, h3]

/-- The number of `a` with `a 0 = a₁` is `(L²)^{k-1}`. -/
theorem SumZeroQ_card_filter (a₁ : Z2 L) :
    (((Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁)).card : ℕ) : ℝ)
      = ((L : ℝ) ^ 2) ^ (k - 1) := by
  have h := SumZeroQ_sum_filter_prod (R := ℝ) (L := L) (k := k) a₁ (fun _ _ => 1)
  simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, ZMod.card, Finset.card_erase_of_mem (Finset.mem_univ _),
    Fintype.card_fin] at h
  rw [h]
  push_cast
  ring

/-! ## 2. `𝒫ϑ_t = 1`, `𝒫∘𝒬_t = 0`, `𝒬_t = id` on sum-zero tensors -/

/-- `‖(t : ℂ)‖ < 1` for `|t| < 1`. -/
private theorem SumZeroQ_norm_ofReal_lt {t : ℝ} (ht : |t| < 1) : ‖(t : ℂ)‖ < 1 := by
  rwa [Complex.norm_real, Real.norm_eq_abs]

/-- `𝒫ϑ_t = 1`, for every real `|t| < 1`. -/
theorem SumZeroQ_Psum_vartheta (hL : 3 ≤ L) {t : ℝ} (ht : |t| < 1) (a₁ : Z2 L) :
    Psum L (vartheta L t (k := k)) a₁ = 1 := by
  have hξ : ‖(t : ℂ)‖ < 1 := SumZeroQ_norm_ofReal_lt ht
  have hne : (1 : ℂ) - (t : ℂ) ≠ 0 := one_sub_ne_zero hξ
  have hcast : (((1 - t : ℝ)) : ℂ) = 1 - (t : ℂ) := by push_cast; rfl
  unfold Psum
  have h1 : ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), vartheta L t a
      = ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          (((1 - t : ℝ) : ℂ) ^ (k - 1) *
            ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (t : ℂ) a₁ (a i)) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [vartheta, ha0]
  rw [h1, ← Finset.mul_sum,
    SumZeroQ_sum_filter_prod a₁ (fun _ b => Theta L (t : ℂ) a₁ b)]
  simp only [sum_Theta_row L hL hξ a₁, Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hcast, ← mul_pow, mul_inv_cancel₀ hne, one_pow]

/-- `𝒫∘𝒬_t = 0`. -/
theorem SumZeroQ_Psum_Qop (hL : 3 ≤ L) {t : ℝ} (ht : |t| < 1) (A : (Fin k → Z2 L) → ℂ)
    (a₁ : Z2 L) : Psum L (Qop L t A) a₁ = 0 := by
  have hv := SumZeroQ_Psum_vartheta (k := k) hL ht a₁
  unfold Psum at hv ⊢
  have h1 : ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), Qop L t A a
      = ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          (A a - Psum L A a₁ * vartheta L t a) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [Qop, ha0]
  rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hv, mul_one]
  unfold Psum
  exact sub_self _

/-- `𝒬_t = id` on sum-zero tensors. -/
theorem SumZeroQ_Qop_of_sumZero (t : ℝ) {A : (Fin k → Z2 L) → ℂ} (hA : SumZero L A) :
    Qop L t A = A := by
  funext a
  have h : Psum L A (a 0) = 0 := hA (a 0)
  simp only [Qop, h, zero_mul, sub_zero]

/-! ## 3. The derivative of `ϑ_t` -/

/-- The derivative of `ϑ_{t,a}` in `t`, with the closed form of `ϑ̇` as in `QopAlgebra`. -/
theorem SumZeroQ_hasDerivAt_vartheta (hL : 3 ≤ L) (hk : 2 ≤ k) {t : ℝ} (ht : |t| < 1)
    (a : Fin k → Z2 L) :
    HasDerivAt (fun v : ℝ => vartheta L v a)
      (-((k - 1 : ℕ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ (k - 2) *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (t : ℂ) (a 0) (a i) +
        ((1 - t : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i)) t := by
  have hξ : ‖(t : ℂ)‖ < 1 := SumZeroQ_norm_ofReal_lt ht
  have h1 : HasDerivAt (fun v : ℝ => (((1 - v : ℝ)) : ℂ) ^ (k - 1))
      (((k - 1 : ℕ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ (k - 1 - 1) * ((-1 : ℝ) : ℂ)) t := by
    have hid : HasDerivAt (fun v : ℝ => 1 - v) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hc := hid.ofReal_comp
    exact hc.pow (k - 1)
  have h2 : HasDerivAt (fun v : ℝ => ∏ i ∈ Finset.univ.erase (0 : Fin k),
      Theta L (v : ℂ) (a 0) (a i))
      (∑ j ∈ Finset.univ.erase (0 : Fin k),
        (∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i)) •
          (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)) t :=
    HasDerivAt.fun_finsetProd fun j _ =>
      (hasDerivAt_Theta_apply L hL hξ (a 0) (a j)).comp_ofReal
  have h3 := h1.mul h2
  have hk2 : k - 1 - 1 = k - 2 := by omega
  refine h3.congr_deriv ?_
  simp only [hk2, smul_eq_mul]
  push_cast
  have hsum : ∑ j ∈ Finset.univ.erase (0 : Fin k),
        (∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i)) *
          (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j)
      = ∑ j ∈ Finset.univ.erase (0 : Fin k),
        (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
          ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hsum]
  ring

/-- The closed form of `ϑ̇_t` (clause 5 of `QopAlgebra`). -/
theorem SumZeroQ_varthetaDot_eq (hL : 3 ≤ L) (hk : 2 ≤ k) {t : ℝ} (ht : |t| < 1)
    (a : Fin k → Z2 L) :
    varthetaDot L t a =
      -((k - 1 : ℕ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ (k - 2) *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (t : ℂ) (a 0) (a i) +
        ((1 - t : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i) :=
  (SumZeroQ_hasDerivAt_vartheta hL hk ht a).deriv

/-- `𝒫ϑ̇_t = 0`: differentiate `𝒫ϑ_t = 1`.  The identity
`𝒫ϑ_v = 1` holds for every `|v| < 1`, so the derivative at `t` is taken on a neighbourhood. -/
theorem SumZeroQ_Psum_varthetaDot (hL : 3 ≤ L) (hk : 2 ≤ k) {t : ℝ} (ht : |t| < 1)
    (a₁ : Z2 L) : Psum L (varthetaDot L t (k := k)) a₁ = 0 := by
  have hd : HasDerivAt (fun v : ℝ => Psum L (vartheta L v (k := k)) a₁)
      (Psum L (varthetaDot L t (k := k)) a₁) t := by
    unfold Psum
    refine HasDerivAt.fun_sum fun a _ => ?_
    have h := SumZeroQ_hasDerivAt_vartheta hL hk ht a
    rwa [← SumZeroQ_varthetaDot_eq hL hk ht a] at h
  have hev : (fun v : ℝ => Psum L (vartheta L v (k := k)) a₁) =ᶠ[nhds t] fun _ => (1 : ℂ) := by
    have hopen : Set.Ioo (-1 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2
    filter_upwards [hopen] with v hv
    exact SumZeroQ_Psum_vartheta hL (abs_lt.mpr hv) a₁
  have h2 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) (Psum L (varthetaDot L t (k := k)) a₁) t :=
    hd.congr_of_eventuallyEq hev.symm
  exact h2.unique (hasDerivAt_const t (1 : ℂ))

/-! ## 4. `ϴ_{t,σ}` preserves sum-zero -/

/-- The kernel `S Θ_ζ` is symmetric (`S`, `Θ_ζ` are symmetric and commute). -/
private theorem SumZeroQ_SB_mul_Theta_symm (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (x y : Z2 L) :
    (SB L * Theta L ζ) x y = (SB L * Theta L ζ) y x := by
  have h : (SB L * Theta L ζ)ᵀ = SB L * Theta L ζ := by
    rw [Matrix.transpose_mul, SB_transpose, Theta_transpose L hL hζ]
    exact (Theta_commute_SB L hL hζ).eq
  have := congrFun (congrFun h y) x
  simpa [Matrix.transpose_apply] using this

/-- The column sums of `S Θ_ζ` are the constant `(1 - ζ)⁻¹` (with `S` on the left). -/
private theorem SumZeroQ_col_sum (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Z2 L) :
    ∑ c : Z2 L, (SB L * Theta L ζ) c y = (1 - ζ)⁻¹ := by
  simp_rw [SumZeroQ_SB_mul_Theta_symm hL hζ _ y]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_Theta_row L hL hζ]
  rw [← Finset.sum_mul, sum_SB_row L hL y, one_mul]

/-- Slot `0`: `Σ_{a₀ = a₁} Σ_b G(a₀, b) A(a^{(0)}_b) = Σ_b G(a₁, b) (𝒫A)_b`. -/
theorem SumZeroQ_slot_zero (G : Z2 L → Z2 L → ℂ) (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
        ∑ b : Z2 L, G (a 0) b * A (Function.update a 0 b)
      = ∑ b : Z2 L, G a₁ b * Psum L A b := by
  have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
      ∑ b : Z2 L, G (a 0) b * A (Function.update a 0 b)
        = ∑ b : Z2 L, G a₁ b * A (Function.update a 0 b) := by
    intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [ha0]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold Psum
  refine Finset.sum_nbij' (fun a => Function.update a 0 b) (fun a => Function.update a 0 a₁)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp
  · intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a _
    rfl

/-- Slot `i ≠ 0`: the reindexing `(a, b) ↦ (a^{(i)}_b, a_i)` of `{a₀ = a₁} × Z2 L`. -/
theorem SumZeroQ_slot_succ {i : Fin k} (hi : i ≠ 0) (G : Z2 L → Z2 L → ℂ)
    (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
        ∑ b : Z2 L, G (a i) b * A (Function.update a i b)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          (∑ c : Z2 L, G c (a i)) * A a := by
  classical
  set F : Finset (Fin k → Z2 L) := Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁) with hF
  have h1 : ∑ a ∈ F, ∑ b : Z2 L, G (a i) b * A (Function.update a i b)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Z2 L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2) :=
    (Finset.sum_product' F Finset.univ (fun a b => G (a i) b * A (Function.update a i b))).symm
  have h2 : ∑ x ∈ F ×ˢ (Finset.univ : Finset (Z2 L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Z2 L)), G x.2 (x.1 i) * A x.1 := by
    refine Finset.sum_nbij' (fun x => (Function.update x.1 i x.2, x.1 i))
      (fun x => (Function.update x.1 i x.2, x.1 i)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      simp
  rw [h1, h2, Finset.sum_product' F Finset.univ (fun a b => G b (a i) * A a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]

/-- The generator's kernel `ξ • (S Θ_{tξ})` has constant column sums `ξ (1 - tξ)⁻¹`. -/
private theorem SumZeroQ_col_sum_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {t : ℝ}
    (h : ‖(t : ℂ) * ξ‖ < 1) (y : Z2 L) :
    ∑ c : Z2 L, thetaGenMat L ξ t c y = ξ * (1 - (t : ℂ) * ξ)⁻¹ := by
  simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, SumZeroQ_col_sum hL h y]

private theorem SumZeroQ_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

private theorem SumZeroQ_norm_xi {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (s s' : Bool) : ‖(u : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ < 1 := by
  rw [norm_mul, norm_mul, SumZeroQ_norm_mSig hE, SumZeroQ_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg hu0, mul_one, mul_one]
  exact hu1

/-- **`ϴ_{t,σ}` preserves sum-zero** (clause 6 of `QopAlgebra`): slot `0` gives `Σ_b G(a₁, b)(𝒫A)_b = 0`, every slot `i ≥ 1` gives the constant
column sum of `G_i` times `(𝒫A)_{a₁} = 0`. -/
theorem SumZeroQ_SumZero_thetaSig (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) (σ : Fin k → Bool)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin k → Z2 L) → ℂ} (hA : SumZero L A) :
    SumZero L (thetaSig L E σ t A) := by
  intro a₁
  simp only [thetaSig]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    refine (SumZeroQ_slot_zero (fun x y => thetaGenMat L
      (KLoop.mSig E (σ 0) * KLoop.mSig E (σ (0 + 1))) t x y) A a₁).trans ?_
    exact Finset.sum_eq_zero fun b _ => by
      have h : Psum L A b = 0 := hA b
      rw [h, mul_zero]
  · refine (SumZeroQ_slot_succ hi (fun x y => thetaGenMat L
      (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) t x y) A a₁).trans ?_
    have hcol : ∀ y : Z2 L,
        ∑ c : Z2 L, thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) t c y
          = (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) *
              (1 - (t : ℂ) * (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))))⁻¹ :=
      fun y => SumZeroQ_col_sum_thetaGenMat hL (SumZeroQ_norm_xi hE.le ht0 ht1 _ _) y
    simp only [hcol]
    rw [← Finset.mul_sum]
    have h : ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), A a = 0 := hA a₁
    rw [h, mul_zero]

/-! ## 5. The commutator formula -/

/-- `ϴ_{u,σ}` is additive (used for the commutator). -/
theorem SumZeroQ_thetaSig_sub (E : ℝ) (σ : Fin k → Bool) (u : ℝ) (A B : (Fin k → Z2 L) → ℂ)
    (a : Fin k → Z2 L) :
    thetaSig L E σ u (fun b => A b - B b) a = thetaSig L E σ u A a - thetaSig L E σ u B a := by
  simp only [thetaSig, mul_sub, Finset.sum_sub_distrib]

/-- The commutator formula (clause 7, `pqthlk`): pure linearity of `𝒫` and `ϴ`. -/
theorem SumZeroQ_commutator (E : ℝ) (σ : Fin k → Bool) (t : ℝ) (A : (Fin k → Z2 L) → ℂ)
    (a : Fin k → Z2 L) :
    Qop L t (thetaSig L E σ t A) a - thetaSig L E σ t (Qop L t A) a =
      thetaSig L E σ t (fun b => Psum L A (b 0) * vartheta L t b) a -
        Psum L (thetaSig L E σ t A) (a 0) * vartheta L t a := by
  have h : thetaSig L E σ t (Qop L t A) a
      = thetaSig L E σ t A a - thetaSig L E σ t (fun b => Psum L A (b 0) * vartheta L t b) a :=
    SumZeroQ_thetaSig_sub E σ t A (fun b => Psum L A (b 0) * vartheta L t b) a
  rw [h]
  simp only [Qop]
  ring

/-! ## 6. The theorem `qopAlgebra` -/

/-- **`qopAlgebra`** (`QopAlgebra` of `RBM2D.Induction.HierVocab`, `Def:QtPt`, `pqthlk`): the
statement, with no added hypothesis. -/
theorem qopAlgebra : QopAlgebra := by
  intro L _ hL k _ hk t ht0 ht1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  refine ⟨fun a₁ => SumZeroQ_Psum_vartheta hL ht a₁,
    fun A a₁ => SumZeroQ_Psum_Qop hL ht A a₁,
    fun A hA => SumZeroQ_Qop_of_sumZero t hA,
    fun a₁ => SumZeroQ_Psum_varthetaDot hL hk ht a₁,
    fun a => SumZeroQ_varthetaDot_eq hL hk ht a, ?_, ?_⟩
  · intro E hE σ A hA
    exact SumZeroQ_SumZero_thetaSig hL hE σ ht0 ht1 hA
  · intro E σ A a
    exact SumZeroQ_commutator E σ t A a

end RBM.Ind
