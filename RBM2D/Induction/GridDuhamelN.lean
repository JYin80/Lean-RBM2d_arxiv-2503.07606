/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Path.GoodEvent

/-!
# The general-`n` stopped grid Duhamel identity (`d = 2`)

Paper: arXiv:2503.07606, Section 5: `int_K-L_ST` and `def_Ustz`.

* `stoppedDuhamelN : StoppedDuhamelN d E s t K` (the statement is in `RBM2D.Induction.HierVocab`).

The kernel algebra of `Ugen` (`GridDuhamelN_Ugen_add`, `GridDuhamelN_Ugen_self`,
`GridDuhamelN_Ugen_comp`, `GridDuhamelN_UgenHom`, `GridDuhamelN_Ugen_duhamel_telescope`) is public
with the file-stem prefix.  The telescope parallels the one-dimensional formalization: the grid
index is clamped so that every time used lies in `[0,1)`.  The `d = 2` changes: labels
`Fin k → Z2 L`, the kernel `Ugen` (real times, slot parameter `m(σ_i) m(σ_{i+1})`), whose
semigroup law comes from `ukerMat_mul` on `Z2 L`.

Every other helper is `private` and carries the prefix `GridDuhamelN_`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. The kernel `Ugen`: additivity, identity and semigroup laws -/

section UgenAlgebra

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2`. -/
private theorem GridDuhamelN_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (b : Bool) :
    ‖KLoop.mSig E b‖ = 1 := by
  cases b <;> simp [KLoop.mSig, norm_spectralM hE]

/-- The slot condition `‖v m(σ) m(σ')‖ < 1` for `0 ≤ v < 1`, `|E| ≤ 2`. -/
private theorem GridDuhamelN_norm_slot_lt_one {E : ℝ} (hE : |E| ≤ 2) (b b' : Bool) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ‖(v : ℂ) * (KLoop.mSig E b * KLoop.mSig E b')‖ < 1 := by
  rw [norm_mul, norm_mul, GridDuhamelN_norm_mSig hE, GridDuhamelN_norm_mSig hE,
    Complex.norm_real, Real.norm_of_nonneg hv0]
  simpa using hv1

variable (L : ℕ) [NeZero L]

/-- `𝒰_{v,w,σ}` is additive. -/
theorem GridDuhamelN_Ugen_add (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Z2 L) → ℂ) :
    Ugen L E σ v w (A + B) = Ugen L E σ v w A + Ugen L E σ v w B := by
  funext a
  simp only [Ugen, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `𝒰_{v,v,σ} = id` for `0 ≤ v < 1`, `|E| ≤ 2` (`ukerMat_self` slot by slot). -/
theorem GridDuhamelN_Ugen_self (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (A : (Fin k → Z2 L) → ℂ) :
    Ugen L E σ v v A = A := by
  funext a
  have h1 : ∀ i : Fin k,
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v v = 1 := fun i =>
    ukerMat_self L hL (GridDuhamelN_norm_slot_lt_one hE _ _ hv0 hv1)
  simp only [Ugen, h1, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : ¬ ∀ i, a i = b i := fun h => hb (funext h).symm
    simp [Fintype.prod_boole, this]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Semigroup law** `𝒰_{v,w,σ} ∘ 𝒰_{u,v,σ} = 𝒰_{u,w,σ}` for `0 ≤ v, w < 1`, `|E| ≤ 2`
(`ukerMat_mul` slot by slot; no condition on `u`). -/
theorem GridDuhamelN_Ugen_comp (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (A : (Fin k → Z2 L) → ℂ) :
    Ugen L E σ v w (Ugen L E σ u v A) = Ugen L E σ u w A := by
  funext a
  set ξ : Fin k → ℂ := fun i => KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) with hξ
  have hm : ∀ (i : Fin k) (x y : Z2 L), ∑ c : Z2 L, ukerMat L (ξ i) v w x c * ukerMat L (ξ i) u v c y
      = ukerMat L (ξ i) u w x y := fun i x y => by
    have h := congrFun (congrFun (ukerMat_mul L (u := u) hL
      (GridDuhamelN_norm_slot_lt_one hE (σ i) (σ (i + 1)) hv0 hv1)
      (GridDuhamelN_norm_slot_lt_one hE (σ i) (σ (i + 1)) hw0 hw1)) x) y
    rwa [Matrix.mul_apply] at h
  calc Ugen L E σ v w (Ugen L E σ u v A) a
      = ∑ c : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) v w (a i) (c i)) *
          ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) u v (c i) (b i)) * A b := rfl
    _ = ∑ c : Fin k → Z2 L, ∑ b : Fin k → Z2 L,
          (∏ i, ukerMat L (ξ i) v w (a i) (c i) * ukerMat L (ξ i) u v (c i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = ∑ b : Fin k → Z2 L, ∑ c : Fin k → Z2 L,
          (∏ i, ukerMat L (ξ i) v w (a i) (c i) * ukerMat L (ξ i) u v (c i) (b i)) * A b :=
        Finset.sum_comm
    _ = ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) u w (a i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul]
        congr 1
        rw [← Fintype.prod_sum (fun i x => ukerMat L (ξ i) v w (a i) x *
          ukerMat L (ξ i) u v x (b i))]
        exact Finset.prod_congr rfl fun i _ => hm i (a i) (b i)
    _ = Ugen L E σ u w A a := rfl

/-- `𝒰_{v,w,σ}` bundled as an `AddMonoidHom`. -/
def GridDuhamelN_UgenHom (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ) :
    ((Fin k → Z2 L) → ℂ) →+ ((Fin k → Z2 L) → ℂ) :=
  AddMonoidHom.mk' (Ugen L E σ v w) (GridDuhamelN_Ugen_add L E σ v w)

@[simp] theorem GridDuhamelN_UgenHom_apply (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (v w : ℝ) (A : (Fin k → Z2 L) → ℂ) :
    GridDuhamelN_UgenHom L E σ v w A = Ugen L E σ v w A := rfl

/-- **The algebraic part of `int_K-L_ST` for `Ugen`** (via the clamped index):
`A_m = 𝒰_{u_0,u_m,σ} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m,σ} (A_{j+1} - 𝒰_{u_j,u_{j+1},σ} A_j)`
for times with `0 ≤ u_j < 1` at the indices `j ≤ m`. -/
theorem GridDuhamelN_Ugen_duhamel_telescope (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    [NeZero k] (σ : Fin k → Bool) (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j)
    (hu1 : ∀ j ≤ m, u j < 1) (A : ℕ → ((Fin k → Z2 L) → ℂ)) :
    A m = Ugen L E σ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Ugen L E σ (u (j + 1)) (u m)
        (A (j + 1) - Ugen L E σ (u j) (u (j + 1)) (A j)) := by
  set uc : ℕ → ℝ := fun j => u (min j m) with huc
  have hc0 : ∀ j, 0 ≤ uc j := fun j => hu0 _ (min_le_right j m)
  have hc1 : ∀ j, uc j < 1 := fun j => hu1 _ (min_le_right j m)
  have hself : ∀ j, GridDuhamelN_UgenHom L E σ (uc j) (uc j)
      = AddMonoidHom.id ((Fin k → Z2 L) → ℂ) := fun j => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.id_apply, GridDuhamelN_UgenHom_apply]
    exact GridDuhamelN_Ugen_self L hL hE σ (hc0 j) (hc1 j) B
  have hcomp : ∀ i j l, i ≤ j → j ≤ l →
      (GridDuhamelN_UgenHom L E σ (uc j) (uc l)).comp (GridDuhamelN_UgenHom L E σ (uc i) (uc j))
        = GridDuhamelN_UgenHom L E σ (uc i) (uc l) := fun i j l _ _ => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.comp_apply, GridDuhamelN_UgenHom_apply, GridDuhamelN_UgenHom_apply,
      GridDuhamelN_UgenHom_apply]
    exact GridDuhamelN_Ugen_comp L hL hE σ (hc0 j) (hc1 j) (hc0 l) (hc1 l) B
  have htel := duhamel_telescope (fun i j => GridDuhamelN_UgenHom L E σ (uc i) (uc j))
    hself hcomp A m
  simp only [GridDuhamelN_UgenHom_apply, huc] at htel
  rw [Nat.zero_min, min_self, sub_eq_iff_eq_add'] at htel
  rw [htel, add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  rw [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]

end UgenAlgebra

/-! ### 2. Grid-time arithmetic (re-proved; the `Expansion_`/`DuhamelTail_` versions are private) -/

section GridArith

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

private theorem GridDuhamelN_gridStep_nonneg (hst : s n ≤ t n) : 0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem GridDuhamelN_gridTime_mono (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := GridDuhamelN_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

private theorem GridDuhamelN_gridTime_nonneg (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) :
    0 ≤ gridTime s t K n j := by
  have h := GridDuhamelN_gridTime_mono s t K n hst (Nat.zero_le j)
  have h0 : gridTime s t K n 0 = s n := by simp [gridTime]
  rw [h0] at h
  linarith

private theorem GridDuhamelN_gridTime_lt_one (hst : s n ≤ t n) (hK : K n ≠ 0) (ht1 : t n < 1)
    {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have h := GridDuhamelN_gridTime_mono s t K n hst hj
  rw [gridTime_last s t K n hK] at h
  linarith

end GridArith

/-! ### 3. The stopped grid Duhamel identity, general `n`, all `σ` -/

/-- **The stopped grid Duhamel identity** (`int_K-L_ST`, grid form): pathwise, for every `τ : PathΩ d → ℕ`,
`A_{j∧τ} = 𝒰_{u_0,u_{j∧τ},σ} A_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_{j∧τ},σ} (P_i + ξ_{i+1})`.  From
`GridDuhamelN_Ugen_duhamel_telescope`: `A_{i+1} - 𝒰 A_i = predIncN_i + martIncN_i` label by label
(the conditional expectation cancels). -/
theorem stoppedDuhamelN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedDuhamelN d E s t K := by
  intro hE hs0 hst ht1 hK n k _ σ τ j ω hjτ
  have h := GridDuhamelN_Ugen_duhamel_telescope (d.L n) (d.three_le_L n) (hE n).le σ
    (gridTime s t K n) (min j (τ ω))
    (fun i _ => GridDuhamelN_gridTime_nonneg s t K n (hs0 n) (hst n) i)
    (fun i hi => GridDuhamelN_gridTime_lt_one s t K n (hst n) (hK n) (ht1 n) (hi.trans hjτ))
    (fun i => AvecN d E s t K n i σ ω)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext a
  simp only [predIncN, martIncN, Pi.add_apply, Pi.sub_apply]
  ring

end RBM.Ind

end
