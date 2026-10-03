/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpVocab

/-!
# The two Duhamel formulas from the expected hierarchy

Paper: `Eexpint_K-L`.  Statements (namespace `RBM.Evol`, `variable (d : Sizes)`; the statements of
`MLExpVocab.lean` under the hypothesis `ExpHierPin`):

* `expDuhamelPin_of_hier (h : ExpHierPin d) : ExpDuhamelPin d`,
* `expQDuhamelPin_of_hier (h : ExpHierPin d) : ExpQDuhamelPin d`.

Argument: `v ↦ 𝒰_{v,t,σ} Y_v` has derivative `𝒰_{v,t}(Y'_v - ϴ_v Y_v)` (`ukerMat` is affine in `v`,
`∂_v ukerMat = -thetaGenMat t`, and `𝒰_{v,t} ϴ_v = ϴ_t` slotwise by `uker_mul_thetaGenMat`,
reindexed by `MLExpDuhamel_sum_update_reindex`); continuity on `[0,t]`, the derivative on `(0,t)`,
`Y_0 = 0` and `𝒰_{t,t} = 1` give `MLExpDuhamel_ftc` (FTC with continuity at the ends).  The first
target is `Y = f = expErrT`, `D = expDriftT`.  The second is `Y_u = 𝒬_u f_u`, `D = qDriftT`: the
product rule `MLExpDuhamel_hasDerivAt_Qop` (`SumZeroQ_hasDerivAt_vartheta`) and `qop_source`, and
the continuity of `A_u` (`MLExpDuhamel_continuousOn_qDriftT`, closed form of `ϑ̇`).

In `d = 2` the kernel is the matrix `ukerMat` on `Z2 L` (affine in the
first time), the slot algebra is `uker_mul_thetaGenMat`
(`Θ_{tξ} S Θ_{vξ}`, with `S` on the left), labels are `Fin k → Z2 L`.  Helpers are prefixed
`MLExpDuhamel_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind

variable (d : Sizes)

section Kernel

variable {L : ℕ} [NeZero L]

theorem MLExpDuhamel_ukerMat_eq (ξ : ℂ) (t r : ℝ) :
    ukerMat L ξ r t = Theta L ((t : ℂ) * ξ) - (r : ℂ) • thetaGenMat L ξ t := by
  simp only [ukerMat, thetaGenMat, sub_mul, one_mul, smul_mul_assoc, smul_smul]

/-- `∂_r (ukerMat ξ r t)_{xy} = -(thetaGenMat ξ t)_{xy}`: `ukerMat` is affine in the first time. -/
theorem MLExpDuhamel_hasDerivAt_ukerMat (ξ : ℂ) (t : ℝ) (x y : Z2 L) (v : ℝ) :
    HasDerivAt (fun r : ℝ => ukerMat L ξ r t x y) (-(thetaGenMat L ξ t x y)) v := by
  have h : (fun r : ℝ => ukerMat L ξ r t x y) = fun r : ℝ =>
      Theta L ((t : ℂ) * ξ) x y - (r : ℂ) * (thetaGenMat L ξ t x y) := by
    funext r
    rw [MLExpDuhamel_ukerMat_eq]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
  exact ((hasDerivAt_const v (Theta L ((t : ℂ) * ξ) x y)).fun_sub
    (hid.mul_const (thetaGenMat L ξ t x y))).congr_deriv (by ring)

theorem MLExpDuhamel_continuous_ukerMat (ξ : ℂ) (t : ℝ) (x y : Z2 L) :
    Continuous fun r : ℝ => ukerMat L ξ r t x y :=
  continuous_iff_continuousAt.2 fun v =>
    (MLExpDuhamel_hasDerivAt_ukerMat ξ t x y v).continuousAt

/-- Reindexing of a double sum over a tensor `b` and one replaced slot `c` (labels are
`Fin k → Z2 L`). -/
theorem MLExpDuhamel_sum_update_reindex {k : ℕ} (i : Fin k) (f : (Fin k → Z2 L) → Z2 L → ℂ) :
    ∑ b : Fin k → Z2 L, ∑ c : Z2 L, f b c
      = ∑ d : Fin k → Z2 L, ∑ e : Z2 L, f (Function.update d i e) (d i) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun p => (Function.update p.1 i p.2, p.1 i))
    (j := fun q => (Function.update q.1 i q.2, q.1 i)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro q _
    exact Finset.mem_univ _
  · intro p _
    exact Prod.ext (by simp) (by simp)
  · intro q _
    exact Prod.ext (by simp) (by simp)
  · intro p _
    simp

/-- **`𝒰_{v,t} ∘ ϴ_v` in closed form** (the slot algebra is `uker_mul_thetaGenMat`, the d = 2
analogue of the one-dimensional slot algebra):
applying the kernel to the generator gives the sum over slots of the kernel with the `i`-th factor
replaced by `thetaGenMat t`. -/
theorem MLExpDuhamel_Uker_theta (hL : 3 ≤ L) {k : ℕ} (ξ : Fin k → ℂ) {v t : ℝ}
    (hv : ∀ i, ‖(v : ℂ) * ξ i‖ < 1) (ht : ∀ i, ‖(t : ℂ) * ξ i‖ < 1)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) v t (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Z2 L, thetaGenMat L (ξ i) v (b i) c * A (Function.update b i c)) =
      ∑ b : Fin k → Z2 L, (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) v t (a j) (b j)) *
          thetaGenMat L (ξ i) t (a i) (b i)) * A b := by
  classical
  have step1 : ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) v t (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Z2 L, thetaGenMat L (ξ i) v (b i) c * A (Function.update b i c))
      = ∑ i : Fin k, ∑ b : Fin k → Z2 L, ∑ c : Z2 L,
          (∏ j, ukerMat L (ξ j) v t (a j) (b j)) *
            (thetaGenMat L (ξ i) v (b i) c * A (Function.update b i c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum]
  have step2 : ∀ i : Fin k,
      (∑ b : Fin k → Z2 L, ∑ c : Z2 L, (∏ j, ukerMat L (ξ j) v t (a j) (b j)) *
            (thetaGenMat L (ξ i) v (b i) c * A (Function.update b i c)))
        = ∑ e : Fin k → Z2 L,
            ((∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) v t (a j) (e j)) *
              thetaGenMat L (ξ i) t (a i) (e i)) * A e := by
    intro i
    rw [MLExpDuhamel_sum_update_reindex i (fun b c => (∏ j, ukerMat L (ξ j) v t (a j) (b j)) *
      (thetaGenMat L (ξ i) v (b i) c * A (Function.update b i c)))]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hkey : ∀ x : Z2 L,
        (∏ j, ukerMat L (ξ j) v t (a j) (Function.update e i x j)) *
            (thetaGenMat L (ξ i) v (Function.update e i x i) (e i) *
              A (Function.update (Function.update e i x) i (e i)))
          = ((∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) v t (a j) (e j)) * A e) *
              (ukerMat L (ξ i) v t (a i) x * thetaGenMat L (ξ i) v x (e i)) := by
      intro x
      have hprod : (∏ j, ukerMat L (ξ j) v t (a j) (Function.update e i x j))
          = ukerMat L (ξ i) v t (a i) x *
            ∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) v t (a j) (e j) := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => ukerMat L (ξ j) v t (a j) (Function.update e i x j)) (Finset.mem_univ i)]
        congr 1
        · rw [Function.update_self]
        · exact Finset.prod_congr rfl fun j hj => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have hup : Function.update (Function.update e i x) i (e i) = e := by
        rw [Function.update_idem, Function.update_eq_self]
      rw [hprod, hup, Function.update_self]
      ring
    simp_rw [hkey]
    rw [← Finset.mul_sum]
    have hmul : ∑ x : Z2 L, ukerMat L (ξ i) v t (a i) x * thetaGenMat L (ξ i) v x (e i)
        = (ukerMat L (ξ i) v t * thetaGenMat L (ξ i) v) (a i) (e i) :=
      (Matrix.mul_apply).symm
    rw [hmul, uker_mul_thetaGenMat hL (hv i) (ht i)]
    ring
  rw [step1]
  simp_rw [step2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]

end Kernel

section FTC

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem MLExpDuhamel_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

/-- `‖v ξ_i‖ < 1` for `ξ_i = m(σ_i) m(σ_{i+1})`, `0 ≤ v < 1`, `|E| ≤ 2`. -/
private theorem MLExpDuhamel_norm_xi {E v : ℝ} (hE : |E| ≤ 2) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (s s' : Bool) : ‖(v : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ < 1 := by
  rw [norm_mul, norm_mul, MLExpDuhamel_norm_mSig hE, MLExpDuhamel_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg hv0, mul_one, mul_one]
  exact hv1

/-- `u ↦ (𝒰_{u,t} Y_u)_a` is continuous on `S` when every entry of `Y` is. -/
theorem MLExpDuhamel_continuousOn_Ugen (E : ℝ) (σ : Fin k → Bool) (t : ℝ) {S : Set ℝ}
    {Y : ℝ → (Fin k → Z2 L) → ℂ} (hY : ∀ b, ContinuousOn (fun u => Y u b) S)
    (a : Fin k → Z2 L) :
    ContinuousOn (fun u : ℝ => Ugen L E σ u t (Y u) a) S := by
  unfold Ugen
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact (continuous_finsetProd _ fun i _ =>
    MLExpDuhamel_continuous_ukerMat (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) t (a i)
      (b i)).continuousOn.mul (hY b)

/-- **The Duhamel formula from the drift identity on the open window**: if `Y_0 = 0`, `Y` and `D`
are continuous on `[0,t]` and
`Y' = ϴ_u Y_u + D_u` on `(0,t)`, then `Y_t = ∫_0^t 𝒰_{u,t,σ} D_u du`. -/
theorem MLExpDuhamel_ftc (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) (σ : Fin k → Bool) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {Y D : ℝ → (Fin k → Z2 L) → ℂ}
    (hY0 : ∀ a, Y 0 a = 0)
    (hYc : ∀ a, ContinuousOn (fun u => Y u a) (Set.Icc 0 t))
    (hDc : ∀ a, ContinuousOn (fun u => D u a) (Set.Icc 0 t))
    (hYd : ∀ u ∈ Set.Ioo 0 t, ∀ a, HasDerivAt (fun v => Y v a)
      (thetaSig L E σ u (Y u) a + D u a) u)
    (a : Fin k → Z2 L) :
    Y t a = ∫ u in (0 : ℝ)..t, Ugen L E σ u t (D u) a := by
  classical
  set ξ : Fin k → ℂ := fun i => KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) with hξ
  have hxi : ∀ {v : ℝ}, 0 ≤ v → v < 1 → ∀ i, ‖(v : ℂ) * ξ i‖ < 1 := fun hv0 hv1 i =>
    MLExpDuhamel_norm_xi hE.le hv0 hv1 _ _
  let g : ℝ → ℂ := fun v => Ugen L E σ v t (Y v) a
  have hcont : ContinuousOn g (Set.Icc 0 t) :=
    MLExpDuhamel_continuousOn_Ugen E σ t hYc a
  have hderiv : ∀ u ∈ Set.Ioo 0 t, HasDerivAt g (Ugen L E σ u t (D u) a) u := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u < 1 := hu.2.trans_le ht1.le
    have hterm : ∀ b : Fin k → Z2 L,
        HasDerivAt (fun r : ℝ => (∏ i, ukerMat L (ξ i) r t (a i) (b i)) * Y r b)
          ((∑ i, (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
              (-(thetaGenMat L (ξ i) t (a i) (b i)))) * Y u b +
            (∏ i, ukerMat L (ξ i) u t (a i) (b i)) * (thetaSig L E σ u (Y u) b + D u b)) u := by
      intro b
      have hprod : HasDerivAt (fun r : ℝ => ∏ i, ukerMat L (ξ i) r t (a i) (b i))
          (∑ i, (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
              (-(thetaGenMat L (ξ i) t (a i) (b i)))) u := by
        have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin k)))
          (f := fun (i : Fin k) (r : ℝ) => ukerMat L (ξ i) r t (a i) (b i))
          (f' := fun i => -(thetaGenMat L (ξ i) t (a i) (b i)))
          (fun i _ => MLExpDuhamel_hasDerivAt_ukerMat (ξ i) t (a i) (b i) u)
        simpa only [smul_eq_mul] using h
      exact hprod.mul (hYd u hu b)
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k → Z2 L)))
      (fun b _ => hterm b)
    refine hsum.congr_deriv ?_
    have hθ := MLExpDuhamel_Uker_theta hL ξ (v := u) (t := t) (hxi hu0 hu1) (hxi ht0 ht1)
      (Y u) a
    have hθ' : ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) u t (a i) (b i)) *
        thetaSig L E σ u (Y u) b = ∑ b : Fin k → Z2 L, (∑ i : Fin k,
          (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
            thetaGenMat L (ξ i) t (a i) (b i)) * Y u b := hθ
    calc ∑ b : Fin k → Z2 L, ((∑ i, (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
              (-(thetaGenMat L (ξ i) t (a i) (b i)))) * Y u b +
            (∏ i, ukerMat L (ξ i) u t (a i) (b i)) * (thetaSig L E σ u (Y u) b + D u b))
        = ∑ b : Fin k → Z2 L, (-((∑ i,
              (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
                thetaGenMat L (ξ i) t (a i) (b i)) * Y u b) +
            (∏ i, ukerMat L (ξ i) u t (a i) (b i)) * thetaSig L E σ u (Y u) b +
            (∏ i, ukerMat L (ξ i) u t (a i) (b i)) * D u b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [mul_neg, Finset.sum_neg_distrib]
          ring
      _ = -(∑ b : Fin k → Z2 L, (∑ i : Fin k,
              (∏ j ∈ Finset.univ.erase i, ukerMat L (ξ j) u t (a j) (b j)) *
                thetaGenMat L (ξ i) t (a i) (b i)) * Y u b) +
            ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) u t (a i) (b i)) *
              thetaSig L E σ u (Y u) b +
            ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) u t (a i) (b i)) * D u b := by
          simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      _ = Ugen L E σ u t (D u) a := by
          rw [hθ']
          unfold Ugen
          ring
  have hint : IntervalIntegrable (fun u : ℝ => Ugen L E σ u t (D u) a) volume 0 t :=
    (MLExpDuhamel_continuousOn_Ugen E σ t hDc a).intervalIntegrable_of_Icc ht0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0 hcont hderiv hint
  have hg0 : g 0 = 0 := by
    change ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) 0 t (a i) (b i)) * Y 0 b = 0
    simp [hY0]
  have hgt : g t = Y t a := by
    change ∑ b : Fin k → Z2 L, (∏ i, ukerMat L (ξ i) t t (a i) (b i)) * Y t b = Y t a
    have h1 : ∀ i, ukerMat L (ξ i) t t = 1 := fun i => ukerMat_self L hL (hxi ht0 ht1 i)
    have h2 : ∀ b : Fin k → Z2 L, (∏ i, (1 : Matrix (Z2 L) (Z2 L) ℂ) (a i) (b i)) =
        if a = b then 1 else 0 := by
      intro b
      simp only [Matrix.one_apply]
      rw [Finset.prod_boole]
      simp [funext_iff]
    simp only [h1, h2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hFTC, hg0, hgt, sub_zero]

end FTC

section QCalculus

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `u ↦ ϑ_{u,a}` is continuous at every `|u| < 1` (`SumZeroQ_hasDerivAt_vartheta`). -/
theorem MLExpDuhamel_continuousOn_vartheta (hL : 3 ≤ L) (hk : 2 ≤ k) {S : Set ℝ}
    (hS : ∀ u ∈ S, |u| < 1) (a : Fin k → Z2 L) :
    ContinuousOn (fun u : ℝ => vartheta L u a) S := fun u hu =>
  (SumZeroQ_hasDerivAt_vartheta hL hk (hS u hu) a).continuousAt.continuousWithinAt

/-- `u ↦ (Θ_{u ζ})_{xy}` is continuous at `‖u ζ‖ < 1` (`continuousAt_Theta`). -/
theorem MLExpDuhamel_continuousAt_Theta_entry (hL : 3 ≤ L) (ζ : ℂ) {u : ℝ}
    (hu : ‖(u : ℂ) * ζ‖ < 1) (x y : Z2 L) :
    ContinuousAt (fun r : ℝ => Theta L ((r : ℂ) * ζ) x y) u := by
  have h1 : ContinuousAt (fun r : ℝ => (r : ℂ) * ζ) u :=
    (Complex.continuous_ofReal.mul continuous_const).continuousAt
  exact (continuous_matrix_entry L x y).continuousAt.comp
    ((continuousAt_Theta L hL hu).comp (f := fun r : ℝ => (r : ℂ) * ζ) h1)

/-- The generator kernel `(thetaGenMat ξ u)_{xy}` is continuous in `u` at `‖u ξ‖ < 1`. -/
theorem MLExpDuhamel_continuousOn_thetaGenMat (hL : 3 ≤ L) (ξ : ℂ) {S : Set ℝ}
    (hS : ∀ u ∈ S, ‖(u : ℂ) * ξ‖ < 1) (x y : Z2 L) :
    ContinuousOn (fun u : ℝ => thetaGenMat L ξ u x y) S := by
  simp only [thetaGenMat, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun z _ => ?_)
  refine continuousOn_const.mul fun u hu => ?_
  exact (MLExpDuhamel_continuousAt_Theta_entry hL ξ (hS u hu) z y).continuousWithinAt

/-- `ϴ_{u,σ}` preserves continuity in `u` on a window `S ⊆ [0,1)`. -/
theorem MLExpDuhamel_continuousOn_thetaSig (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool)
    {S : Set ℝ} (hS0 : ∀ u ∈ S, 0 ≤ u) (hS1 : ∀ u ∈ S, u < 1)
    {Y : ℝ → (Fin k → Z2 L) → ℂ} (hY : ∀ b, ContinuousOn (fun u => Y u b) S)
    (a : Fin k → Z2 L) :
    ContinuousOn (fun u : ℝ => thetaSig L E σ u (Y u) a) S := by
  unfold thetaSig
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun b _ => ?_
  exact (MLExpDuhamel_continuousOn_thetaGenMat hL _
    (fun u hu => MLExpDuhamel_norm_xi hE (hS0 u hu) (hS1 u hu) _ _) (a i) b).mul
      (hY (Function.update a i b))

theorem MLExpDuhamel_continuousOn_Psum {S : Set ℝ} {X : ℝ → (Fin k → Z2 L) → ℂ}
    (hX : ∀ b, ContinuousOn (fun u => X u b) S) (a₁ : Z2 L) :
    ContinuousOn (fun u : ℝ => Psum L (X u) a₁) S := by
  unfold Psum
  exact continuousOn_finsetSum _ fun b _ => hX b

theorem MLExpDuhamel_continuousOn_Qop (hL : 3 ≤ L) (hk : 2 ≤ k) {S : Set ℝ}
    (hS : ∀ u ∈ S, |u| < 1) {X : ℝ → (Fin k → Z2 L) → ℂ}
    (hX : ∀ b, ContinuousOn (fun u => X u b) S) (a : Fin k → Z2 L) :
    ContinuousOn (fun u : ℝ => Qop L u (X u) a) S := by
  unfold Qop
  exact (hX a).sub ((MLExpDuhamel_continuousOn_Psum hX (a 0)).mul
    (MLExpDuhamel_continuousOn_vartheta hL hk hS a))

/-- `u ↦ ϑ̇_{u,a}` is continuous on `S ⊆ (-1,1)` (closed form `SumZeroQ_varthetaDot_eq`). -/
theorem MLExpDuhamel_continuousOn_varthetaDot (hL : 3 ≤ L) (hk : 2 ≤ k) {S : Set ℝ}
    (hS : ∀ u ∈ S, |u| < 1) (a : Fin k → Z2 L) :
    ContinuousOn (fun u : ℝ => varthetaDot L u a) S := by
  have hΘ : ∀ x y : Z2 L, ContinuousOn (fun u : ℝ => Theta L (u : ℂ) x y) S := by
    intro x y u hu
    have h := MLExpDuhamel_continuousAt_Theta_entry hL 1 (u := u) (by simpa using
      (show ‖(u : ℂ)‖ < 1 by rw [Complex.norm_real, Real.norm_eq_abs]; exact hS u hu)) x y
    simpa using h.continuousWithinAt
  have hΘSΘ : ∀ x y : Z2 L, ContinuousOn (fun u : ℝ => (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y) S := by
    intro x y
    simp only [Matrix.mul_apply]
    refine continuousOn_finsetSum _ fun z _ => ?_
    refine ContinuousOn.mul ?_ (hΘ z y)
    refine continuousOn_finsetSum _ fun w _ => ?_
    exact (hΘ x w).mul continuousOn_const
  have hc : ContinuousOn (fun u : ℝ => -((k - 1 : ℕ) : ℂ) * ((1 - u : ℝ) : ℂ) ^ (k - 2) *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (u : ℂ) (a 0) (a i) +
        ((1 - u : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (u : ℂ) (a 0) (a i)) S := by
    have hp : ContinuousOn (fun u : ℝ => ((1 - u : ℝ) : ℂ)) S :=
      (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousOn
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.mul (continuousOn_const.mul (hp.pow _)) ?_
      exact continuousOn_finsetProd _ fun i _ => hΘ (a 0) (a i)
    · refine ContinuousOn.mul (hp.pow _) ?_
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact (hΘSΘ (a 0) (a j)).mul (continuousOn_finsetProd _ fun i _ => hΘ (a 0) (a i))
  exact hc.congr fun u hu => SumZeroQ_varthetaDot_eq hL hk (hS u hu) a

end QCalculus

section QDeriv

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- **The product rule for `𝒬_v X_v`**: `∂_v (𝒬_v X_v) = 𝒬_v X'_v - (𝒫 X_v) ϑ̇_v`
(`SumZeroQ_hasDerivAt_vartheta`). -/
theorem MLExpDuhamel_hasDerivAt_Qop (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu : |u| < 1)
    {X : ℝ → (Fin k → Z2 L) → ℂ} {X' : (Fin k → Z2 L) → ℂ}
    (hX : ∀ b, HasDerivAt (fun v => X v b) (X' b) u) (a : Fin k → Z2 L) :
    HasDerivAt (fun v : ℝ => Qop L v (X v) a)
      (Qop L u X' a - Psum L (X u) (a 0) * varthetaDot L u a) u := by
  have hP : HasDerivAt (fun v : ℝ => Psum L (X v) (a 0)) (Psum L X' (a 0)) u := by
    unfold Psum
    exact HasDerivAt.fun_sum fun b _ => hX b
  have hϑ : HasDerivAt (fun v : ℝ => vartheta L v a) (varthetaDot L u a) u :=
    (SumZeroQ_hasDerivAt_vartheta hL hk hu a).differentiableAt.hasDerivAt
  have h := (hX a).fun_sub (hP.fun_mul hϑ)
  refine h.congr_deriv ?_
  simp only [Qop]
  ring

end QDeriv

section QDrift

/-- Every entry of `A_u = qDriftT` is continuous on a window `S ⊆ [0,1)` once those of `f` and `D` are. -/
theorem MLExpDuhamel_continuousOn_qDriftT (n : ℕ) {E : ℝ} (hE : |E| < 2) (σ : Fin 2 → Bool)
    {S : Set ℝ} (hS0 : ∀ u ∈ S, 0 ≤ u) (hS1 : ∀ u ∈ S, u < 1)
    (hf : ∀ b, ContinuousOn (fun u => expErrT d n E u σ b) S)
    (hD : ∀ b, ContinuousOn (fun u => expDriftT d n E u σ b) S)
    (b : Fin 2 → Z2 (d.L n)) :
    ContinuousOn (fun u : ℝ => qDriftT d n E u σ b) S := by
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hS : ∀ u ∈ S, |u| < 1 := fun u hu => abs_lt.mpr ⟨by linarith [hS0 u hu], hS1 u hu⟩
  have hQf : ∀ c, ContinuousOn (fun u => Qop (d.L n) u (expErrT d n E u σ) c) S := fun c =>
    MLExpDuhamel_continuousOn_Qop hL le_rfl hS hf c
  have hθf : ∀ c, ContinuousOn (fun u => thetaSig (d.L n) E σ u (expErrT d n E u σ) c) S :=
    fun c => MLExpDuhamel_continuousOn_thetaSig hL hE.le σ hS0 hS1 hf c
  unfold qDriftT
  refine ContinuousOn.sub (ContinuousOn.add ?_ (ContinuousOn.sub ?_ ?_)) ?_
  · exact MLExpDuhamel_continuousOn_Qop hL le_rfl hS hD b
  · exact MLExpDuhamel_continuousOn_Qop hL le_rfl hS hθf b
  · exact MLExpDuhamel_continuousOn_thetaSig hL hE.le σ hS0 hS1 hQf b
  · exact (MLExpDuhamel_continuousOn_Psum hf (b 0)).mul
      (MLExpDuhamel_continuousOn_varthetaDot hL le_rfl hS b)

end QDrift

/-! ## The two statements -/

/-- **Duhamel without `𝒬`**: `f_t = ∫_0^t 𝒰_{u,t,σ} D_u du` from the expected hierarchy. -/
theorem expDuhamelPin_of_hier (h : ExpHierPin d) : ExpDuhamelPin d := by
  intro n E t hE ht0 ht1 σ a
  have hL : 3 ≤ d.L n := d.three_le_L n
  exact MLExpDuhamel_ftc hL hE σ ht0 ht1
    (Y := fun u => expErrT d n E u σ) (D := fun u => expDriftT d n E u σ)
    (fun b => (h n E hE σ b).1)
    (fun b => (h n E hE σ b).2.1.mono (Set.Icc_subset_Ico_right ht1))
    (fun b => (h n E hE σ b).2.2.1.mono (Set.Icc_subset_Ico_right ht1))
    (fun u hu b => (h n E hE σ b).2.2.2 u ⟨hu.1, hu.2.trans ht1⟩) a

/-- **Duhamel with `𝒬`**: `(𝒬_t f_t)(a) = ∫_0^t (𝒰_{u,t,σ} A_u)(a) du` with `A = qDriftT`. -/
theorem expQDuhamelPin_of_hier (h : ExpHierPin d) : ExpQDuhamelPin d := by
  intro n E t hE ht0 ht1 σ a
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hI : Set.Icc (0 : ℝ) t ⊆ Set.Ico 0 1 := Set.Icc_subset_Ico_right ht1
  have hf : ∀ b, ContinuousOn (fun u => expErrT d n E u σ b) (Set.Icc 0 t) := fun b =>
    (h n E hE σ b).2.1.mono hI
  have hD : ∀ b, ContinuousOn (fun u => expDriftT d n E u σ b) (Set.Icc 0 t) := fun b =>
    (h n E hE σ b).2.2.1.mono hI
  have hS0 : ∀ u ∈ Set.Icc (0 : ℝ) t, 0 ≤ u := fun u hu => hu.1
  have hS1 : ∀ u ∈ Set.Icc (0 : ℝ) t, u < 1 := fun u hu => hu.2.trans_lt ht1
  have hS : ∀ u ∈ Set.Icc (0 : ℝ) t, |u| < 1 := fun u hu =>
    abs_lt.mpr ⟨by linarith [hS0 u hu], hS1 u hu⟩
  have hf0 : expErrT d n E 0 σ = fun _ => 0 := funext fun b => (h n E hE σ b).1
  exact MLExpDuhamel_ftc hL hE σ ht0 ht1
    (Y := fun u => Qop (d.L n) u (expErrT d n E u σ)) (D := fun u => qDriftT d n E u σ)
    (fun b => by
      show Qop (d.L n) 0 (expErrT d n E 0 σ) b = 0
      rw [hf0]; simp [Qop, Psum])
    (fun b => MLExpDuhamel_continuousOn_Qop hL le_rfl hS hf b)
    (fun b => MLExpDuhamel_continuousOn_qDriftT d n hE σ hS0 hS1 hf hD b)
    (fun u hu b => by
      have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht1⟩
      have hab : |u| < 1 := abs_lt.mpr ⟨by linarith [hu.1], hu'.2⟩
      have hder := MLExpDuhamel_hasDerivAt_Qop hL (le_refl 2) hab
        (X := fun v => expErrT d n E v σ)
        (X' := fun c => thetaSig (d.L n) E σ u (expErrT d n E u σ) c + expDriftT d n E u σ c)
        (fun c => (h n E hE σ c).2.2.2 u hu') b
      refine hder.congr_deriv ?_
      exact qop_source E u σ (expErrT d n E u σ) (expDriftT d n E u σ) b) a

end RBM.Evol
