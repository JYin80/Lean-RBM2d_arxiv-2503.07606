/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Kcal

/-!
# The inner molecule `A` (`innerId`), `Xt`, and the `(spwow3)`-form identity

The inner molecule `innerId`, the size `Xt` of one long boundary edge, and the identities
`treeValW_sum_selfW` (re-attaching the leaf edges to the self-energy gives back the tree
value) and `innerId_eq_sum`, together with `Xt_nonneg` and `one_le_Xt`.  The argument parallels
the one-dimensional formalization; no d = 1 closed form is used.
-/

namespace RBM.KLoop

open Finset

section Molecule

variable (L : ℕ) [NeZero L]

/-- **The object `A` of the decomposition** ([YY_25] (3.75)): the inner
molecule on `k` vertices with the identity as leaf weight at `p` and root label `u`,
`A(u) = Σ_{H ∈ T_SP(k, σ', ∅)} Γ_H` with the leaf at `p` replaced by `1`. -/
noncomputable def innerId {k : ℕ} [NeZero k] (m : Bool → ℂ) (t : ℝ) (σ' : Fin k → Bool)
    (a' : Fin k → Z2 L) (p : Fin k) (u : Z2 L) : ℂ :=
  ∑ H ∈ TSPlong k σ' ∅, treeValW L H (Function.update a' p u)
    (Function.update (fun v => thetaEdge L m t (σ' v) (σ' (v + 1))) p 1)
    (fun d => thetaEdge L m t (σ' d.1.1) (σ' d.1.2) - 1)

end Molecule

/-- `X_t = (ℓ_t² η_t)⁻¹`, the size of one long boundary edge. -/
noncomputable def Xt (L : ℕ) [NeZero L] (E t : ℝ) : ℝ := (ellT L t ^ 2 * etaT E t)⁻¹

section Proofs

variable (L : ℕ) [NeZero L]

/-- Re-attaching the leaf edges to the self-energy gives back the tree value. -/
theorem treeValW_sum_selfW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (a : Fin n → Z2 L) (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) :
    treeValW L F a M E = ∑ d : Fin n → Z2 L, selfW L F E d * ∏ v, M v (a v) (d v) := by
  simp only [selfW, sum_mul]
  rw [sum_comm, treeValW]
  refine sum_congr rfl fun b _ => ?_
  have h : ∀ d : Fin n → Z2 L,
      (∏ v : Fin n, if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0) *
          (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, M v (a v) (d v) =
      (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, (if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) (d v) else 0) := by
    intro d
    rw [mul_comm (∏ v : Fin n, _), mul_assoc, ← prod_mul_distrib]
    congr 2
    funext v
    split_ifs <;> simp
  simp_rw [h, ← mul_sum]
  rw [mul_comm]
  congr 1
  have := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Z2 L)))
    (fun v x => if x = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) x else 0)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine prod_congr rfl fun v _ => ?_
  rw [Fintype.sum_ite_eq']

/-- **The object `A` in `(spwow3)` form**: `A(u) = Σ_{d_p = u} Σ^{(∅)}(σ', d) ∏_{v ≠ p}
(Θ_{t m_v m_{v+1}})_{a'_v d_v}`.  At `p = 0` the right-hand side is the left-hand side of
`(spwow3)`. -/
theorem innerId_eq_sum {k : ℕ} [NeZero k] (m : Bool → ℂ) (t : ℝ) (σ' : Fin k → Bool)
    (a' : Fin k → Z2 L) (p : Fin k) (u : Z2 L) :
    innerId L m t σ' a' p u
      = ∑ d ∈ Finset.univ.filter (fun d : Fin k → Z2 L => d p = u),
          SigmaPi L m t σ' ∅ d *
            ∏ v ∈ Finset.univ.erase p, thetaEdge L m t (σ' v) (σ' (v + 1)) (a' v) (d v) := by
  unfold innerId
  simp_rw [treeValW_sum_selfW]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_mul]
  have hP : ∏ v, (Function.update (fun v => thetaEdge L m t (σ' v) (σ' (v + 1))) p 1) v
        (Function.update a' p u v) (d v)
      = if d p = u then
          ∏ v ∈ Finset.univ.erase p, thetaEdge L m t (σ' v) (σ' (v + 1)) (a' v) (d v)
        else 0 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hrest : ∏ v ∈ Finset.univ.erase p,
        (Function.update (fun v => thetaEdge L m t (σ' v) (σ' (v + 1))) p 1) v
          (Function.update a' p u v) (d v)
        = ∏ v ∈ Finset.univ.erase p, thetaEdge L m t (σ' v) (σ' (v + 1)) (a' v) (d v) :=
      Finset.prod_congr rfl fun v hv => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hv),
          Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hrest, Function.update_self, Function.update_self, Matrix.one_apply]
    by_cases h : d p = u
    · simp only [h, ite_true, one_mul]
    · simp only [Ne.symm h, h, ite_false, zero_mul]
  rw [hP]
  split_ifs
  · rfl
  · rw [mul_zero]

private theorem norm_one_sub_ofReal {t : ℝ} (ht1 : t < 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

private theorem ellT_eq {t : ℝ} (ht1 : t < 1) :
    ellT L t = min (Real.sqrt (1 - t))⁻¹ (L : ℝ) := by
  rw [ellT, ellhat, kappa, norm_one_sub_ofReal ht1]

/-- `ℓ_t ≥ 1`. -/
private theorem one_le_ellT (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ ellT L t := by
  rw [ellT_eq L ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine le_min ((one_le_inv₀ hs0).2 hs1) ?_
  have : (3 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

/-- `ℓ_t² ≤ (1 - t)⁻¹`. -/
private theorem ellT_sq_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ellT L t ^ 2 ≤ (1 - t)⁻¹ := by
  have h1 := one_le_ellT L hL ht0 ht1
  have h2 : ellT L t ≤ (Real.sqrt (1 - t))⁻¹ := by rw [ellT_eq L ht1]; exact min_le_left _ _
  calc ellT L t ^ 2 ≤ ((Real.sqrt (1 - t))⁻¹) ^ 2 := by gcongr
    _ = (1 - t)⁻¹ := by rw [inv_pow, Real.sq_sqrt (by linarith)]

private theorem etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem spectralM_im_le_one (E : ℝ) : (Gauss.spectralM E).im ≤ 1 := by
  rw [Gauss.spectralM_im]
  have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
  linarith

/-- `ℓ_t² η_t ≤ 1`, hence `X_t ≥ 1` when `η_t > 0`. -/
private theorem ellT_sq_mul_etaT_le_one (hL : 3 ≤ L) (E : ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    ellT L t ^ 2 * etaT E t ≤ 1 := by
  have h1 := ellT_sq_le L hL ht0 ht1
  have him0 : 0 ≤ (Gauss.spectralM E).im := by
    rw [Gauss.spectralM_im]; positivity
  have him1 := spectralM_im_le_one E
  rw [etaT_eq]
  have hsub : 0 < 1 - t := by linarith
  calc ellT L t ^ 2 * ((1 - t) * (Gauss.spectralM E).im)
      ≤ (1 - t)⁻¹ * ((1 - t) * (Gauss.spectralM E).im) := by gcongr
    _ = (Gauss.spectralM E).im := by field_simp
    _ ≤ 1 := him1

theorem one_le_Xt (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ Xt L E t := by
  have hpos : 0 < ellT L t ^ 2 * etaT E t := by
    have := one_le_ellT L hL ht0 ht1
    rw [etaT_eq]
    have := Gauss.spectralM_im_pos hE
    have : 0 < 1 - t := by linarith
    positivity
  exact (one_le_inv₀ hpos).2 (ellT_sq_mul_etaT_le_one L hL E ht0 ht1)

theorem Xt_nonneg {E t : ℝ} (ht1 : t < 1) : 0 ≤ Xt L E t := by
  have him0 : 0 ≤ (Gauss.spectralM E).im := by rw [Gauss.spectralM_im]; positivity
  have h1t : 0 < 1 - t := by linarith
  have : 0 ≤ etaT E t := by rw [etaT_eq]; positivity
  rw [Xt]; positivity

end Proofs

end RBM.KLoop
