/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Basic

/-!
# The kernel `𝒰_{v,w}` on two-index tensors and the Duhamel telescope

Paper: arXiv:2503.07606, `def_Ustz` and (`int_K-L_ST`).

* `ukerMat`, `Uop` : the kernel `𝒰_{v,w,(+,-)}` of `def_Ustz` on `Z2 L × Z2 L`.
* `duhamel_telescope` : the abstract discrete Duhamel telescoping identity.
* `UopHom`, `Uop_grid_semigroup` : `𝒰` as an additive homomorphism, and the semigroup law on a
  time grid.
* `ukerMat_mul`, `ukerMat_self`, `Uop_add`, `Uop_smul`, `Uop_comp`, `Uop_self` : the semigroup
  and linearity properties.
* `Uop_duhamel_telescope`, `Uop_duhamel_telescope_stopped` : the algebraic part of (105)
  (`int_K-L_ST`) in `Uop` form.

The d = 2 input is only `Theta_mul`/`mul_Theta` and the commutation of `Θ` with `SB` and with
itself on `Z2 L` (`RBM2D/Propagator/Basic.lean`); no d = 1 closed form is used.
-/

noncomputable section

namespace RBM.Path

open Matrix

section Kernel

variable (L : ℕ) [NeZero L]

/-- The one-index kernel `(1 - v ξ S^{(B)}) Θ^{(B)}_{w ξ}` of `𝒰_{v,w}` (`def_Ustz`). -/
def ukerMat (ξ : ℂ) (v w : ℝ) : Matrix (Z2 L) (Z2 L) ℂ :=
  (1 - ((v : ℂ) * ξ) • SB L) * Theta L ((w : ℂ) * ξ)

/-- `𝒰_{v,w,(+,-)}` on two-index tensors (`def_Ustz`); for `σ = (+,-)` both slots
carry `m_i m_{i+1} = |m|²`. -/
def Uop (ξ : ℂ) (v w : ℝ) (A : Z2 L × Z2 L → ℂ) : Z2 L × Z2 L → ℂ :=
  fun a => ∑ b : Z2 L × Z2 L, ukerMat L ξ v w a.1 b.1 * ukerMat L ξ v w a.2 b.2 * A b

end Kernel

section KernelLemmas

variable (L : ℕ) [NeZero L]

/-- `‖(v : ℂ) ξ‖ < 1` from `‖ξ‖ ≤ 1` and `0 ≤ v < 1`. -/
private theorem norm_ofReal_mul_lt_one {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v < 1) : ‖(v : ℂ) * ξ‖ < 1 := by
  rw [norm_mul, Complex.norm_of_nonneg h0]
  calc v * ‖ξ‖ ≤ v * 1 := mul_le_mul_of_nonneg_left hξ h0
    _ = v := mul_one v
    _ < 1 := h1

/-- The one-index kernels compose:
`(1 - vξS) Θ_{wξ} (1 - uξS) Θ_{vξ} = (1 - uξS) Θ_{wξ}`. -/
theorem ukerMat_mul (hL : 3 ≤ L) {ξ : ℂ} {u v w : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v w * ukerMat L ξ u v = ukerMat L ξ u w := by
  set P : Matrix (Z2 L) (Z2 L) ℂ := 1 - ((u : ℂ) * ξ) • SB L with hP
  set Q : Matrix (Z2 L) (Z2 L) ℂ := 1 - ((v : ℂ) * ξ) • SB L with hQ
  set Tw : Matrix (Z2 L) (Z2 L) ℂ := Theta L ((w : ℂ) * ξ) with hTw
  set Tv : Matrix (Z2 L) (Z2 L) ℂ := Theta L ((v : ℂ) * ξ) with hTv
  have h1 : Commute Tw P :=
    (Commute.one_right Tw).sub_right ((Theta_commute_SB L hL hw).smul_right ((u : ℂ) * ξ))
  have h2 : Commute Q P :=
    (Commute.one_left P).sub_left
      ((Commute.one_right (((v : ℂ) * ξ) • SB L)).sub_right
        (((Commute.refl (SB L)).smul_left ((v : ℂ) * ξ)).smul_right ((u : ℂ) * ξ)))
  have h3 : Commute Tw Tv := Theta_commute L hL hw hv
  have h4 : Q * Tv = 1 := mul_Theta L hL hv
  calc ukerMat L ξ v w * ukerMat L ξ u v = Q * Tw * (P * Tv) := rfl
    _ = Q * (Tw * P) * Tv := by noncomm_ring
    _ = Q * (P * Tw) * Tv := by rw [h1.eq]
    _ = (Q * P) * (Tw * Tv) := by noncomm_ring
    _ = (P * Q) * (Tv * Tw) := by rw [h2.eq, h3.eq]
    _ = P * (Q * Tv) * Tw := by noncomm_ring
    _ = P * Tw := by rw [h4, Matrix.mul_one]

/-- At equal times the one-index kernel is the identity. -/
theorem ukerMat_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v v = 1 :=
  mul_Theta L hL hv

/-- `𝒰_{v,w}` is additive. -/
theorem Uop_add (ξ : ℂ) (v w : ℝ) (A B : Z2 L × Z2 L → ℂ) :
    Uop L ξ v w (A + B) = Uop L ξ v w A + Uop L ξ v w B := by
  funext a
  simp only [Uop, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `𝒰_{v,w}` is homogeneous. -/
theorem Uop_smul (ξ : ℂ) (v w : ℝ) (c : ℂ) (A : Z2 L × Z2 L → ℂ) :
    Uop L ξ v w (c • A) = c • Uop L ξ v w A := by
  funext a
  simp only [Uop, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- At equal times `𝒰_{v,v} = id`. -/
theorem Uop_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (A : Z2 L × Z2 L → ℂ) : Uop L ξ v v A = A := by
  funext a
  obtain ⟨a₁, a₂⟩ := a
  simp only [Uop, ukerMat_self L hL hv, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  simp

/-- **Semigroup law** `𝒰_{v,w} ∘ 𝒰_{u,v} = 𝒰_{u,w}` on two-index tensors (with `n = 2` and the same
kernel in both slots). -/
theorem Uop_comp (hL : 3 ≤ L) {ξ : ℂ} {u v w : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (hw : ‖(w : ℂ) * ξ‖ < 1) (A : Z2 L × Z2 L → ℂ) :
    Uop L ξ v w (Uop L ξ u v A) = Uop L ξ u w A := by
  funext a
  calc Uop L ξ v w (Uop L ξ u v A) a
      = ∑ c : Z2 L × Z2 L, ukerMat L ξ v w a.1 c.1 * ukerMat L ξ v w a.2 c.2 *
          ∑ b : Z2 L × Z2 L, ukerMat L ξ u v c.1 b.1 * ukerMat L ξ u v c.2 b.2 * A b := rfl
    _ = ∑ c : Z2 L × Z2 L, ∑ b : Z2 L × Z2 L,
          (ukerMat L ξ v w a.1 c.1 * ukerMat L ξ u v c.1 b.1) *
            (ukerMat L ξ v w a.2 c.2 * ukerMat L ξ u v c.2 b.2) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b : Z2 L × Z2 L, ∑ c : Z2 L × Z2 L,
          (ukerMat L ξ v w a.1 c.1 * ukerMat L ξ u v c.1 b.1) *
            (ukerMat L ξ v w a.2 c.2 * ukerMat L ξ u v c.2 b.2) * A b :=
        Finset.sum_comm
    _ = ∑ b : Z2 L × Z2 L, ukerMat L ξ u w a.1 b.1 * ukerMat L ξ u w a.2 b.2 * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have hm : ∀ x y : Z2 L, ∑ c : Z2 L, ukerMat L ξ v w x c * ukerMat L ξ u v c y
            = ukerMat L ξ u w x y := fun x y => by
          have h := congrFun (congrFun (ukerMat_mul L (u := u) hL hv hw) x) y
          rwa [Matrix.mul_apply] at h
        rw [← Finset.sum_mul, Fintype.sum_prod_type, ← hm a.1 b.1, ← hm a.2 b.2,
          Finset.sum_mul_sum]
    _ = Uop L ξ u w A a := rfl

/-- `𝒰_{v,w}` bundled as an `AddMonoidHom`. -/
def UopHom (ξ : ℂ) (v w : ℝ) : (Z2 L × Z2 L → ℂ) →+ (Z2 L × Z2 L → ℂ) :=
  AddMonoidHom.mk' (Uop L ξ v w) (Uop_add L ξ v w)

@[simp] theorem UopHom_apply (ξ : ℂ) (v w : ℝ) (A : Z2 L × Z2 L → ℂ) :
    UopHom L ξ v w A = Uop L ξ v w A := rfl

end KernelLemmas

section Telescope

variable {V : Type*} [AddCommGroup V]

/-- **The discrete Duhamel telescoping identity.**  For a family `U j k : V →+ V`
satisfying the evolution-kernel laws `U k k = id` and `(U j k).comp (U i j) = U i k` for
`i ≤ j ≤ k`, and any sequence `A : ℕ → V`,
`A k - U 0 k (A 0) = ∑_{j < k} U (j+1) k (A (j+1) - U j (j+1) (A j))`. -/
theorem duhamel_telescope (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (k : ℕ) :
    A k - U 0 k (A 0) =
      ∑ j ∈ Finset.range k, U (j + 1) k (A (j + 1) - U j (j + 1) (A j)) := by
  induction k with
  | zero =>
      have h0 : U 0 0 (A 0) = A 0 := by rw [hself 0]; rfl
      simp [h0]
  | succ k ih =>
      have hrw : ∀ j ∈ Finset.range k,
          U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
            = U k (k + 1) (U (j + 1) k (A (j + 1) - U j (j + 1) (A j))) := by
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hcomp' := hcomp (j + 1) k (k + 1) hjk (Nat.le_succ k)
        rw [← hcomp']
        rfl
      have hsum : ∑ j ∈ Finset.range k, U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
          = U k (k + 1) (A k - U 0 k (A 0)) := by
        rw [ih]
        rw [map_sum (U k (k+1))]
        exact Finset.sum_congr rfl (fun j hj => hrw j hj)
      have htail : U (k + 1) (k + 1) (A (k + 1) - U k (k + 1) (A k))
          = A (k + 1) - U k (k + 1) (A k) := by rw [hself (k+1)]; rfl
      have hfront : U k (k + 1) (A k - U 0 k (A 0))
          = U k (k + 1) (A k) - U 0 (k + 1) (A 0) := by
        rw [map_sub]
        have := hcomp 0 k (k + 1) (Nat.zero_le k) (Nat.le_succ k)
        rw [show U k (k+1) (U 0 k (A 0)) = (U k (k+1)).comp (U 0 k) (A 0) from rfl, this]
      rw [Finset.sum_range_succ, hsum, hfront, htail]
      abel

end Telescope

section UopGrid

variable (L : ℕ) [NeZero L]

/-- The family `fun j k => UopHom ξ (u j) (u k)` satisfies the hypotheses of
`duhamel_telescope` (the hypothesis `‖u k * ξ i‖ < 1` is derived from `‖ξ‖ ≤ 1`,
`0 ≤ u k < 1`). -/
theorem Uop_grid_semigroup (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (u : ℕ → ℝ)
    (hu0 : ∀ k, 0 ≤ u k) (hu1 : ∀ k, u k < 1) :
    (∀ k, UopHom L ξ (u k) (u k) = AddMonoidHom.id (Z2 L × Z2 L → ℂ)) ∧
      (∀ i j k, i ≤ j → j ≤ k →
        (UopHom L ξ (u j) (u k)).comp (UopHom L ξ (u i) (u j)) = UopHom L ξ (u i) (u k)) := by
  have hu : ∀ k, ‖(u k : ℂ) * ξ‖ < 1 := fun k => norm_ofReal_mul_lt_one hξ (hu0 k) (hu1 k)
  constructor
  · intro k
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.id_apply, UopHom_apply]
    exact Uop_self L hL (hu k) A
  · intro i j k _ _
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.comp_apply, UopHom_apply, UopHom_apply, UopHom_apply]
    exact Uop_comp L hL (hu j) (hu k) A

/-- **The algebraic part of (105)** (`int_K-L_ST`) in `Uop` form:
`A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m} (A_{j+1} - 𝒰_{u_j,u_{j+1}} A_j)`,
for grid times with `0 ≤ u_j < 1` at the indices `j ≤ m`. -/
theorem Uop_duhamel_telescope (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j) (hu1 : ∀ j ≤ m, u j < 1)
    (A : ℕ → (Z2 L × Z2 L → ℂ)) :
    A m = Uop L ξ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Uop L ξ (u (j + 1)) (u m)
        (A (j + 1) - Uop L ξ (u j) (u (j + 1)) (A j)) := by
  have hsg := Uop_grid_semigroup L hL hξ (fun j => u (min j m))
    (fun j => hu0 _ (min_le_right j m)) (fun j => hu1 _ (min_le_right j m))
  have htel := duhamel_telescope (fun i j => UopHom L ξ (u (min i m)) (u (min j m)))
    hsg.1 hsg.2 A m
  simp only [UopHom_apply] at htel
  rw [Nat.zero_min, min_self, sub_eq_iff_eq_add'] at htel
  rw [htel, add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  rw [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]

/-- The stopped form of `Uop_duhamel_telescope`: the identity at `m := min k (τ ω)` for any
`τ : Ω' → ℕ`. -/
theorem Uop_duhamel_telescope_stopped (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    {Ω' : Type*} (u : ℕ → ℝ) (τ : Ω' → ℕ) (ω : Ω') (k : ℕ)
    (hu0 : ∀ j ≤ min k (τ ω), 0 ≤ u j) (hu1 : ∀ j ≤ min k (τ ω), u j < 1)
    (A : ℕ → (Z2 L × Z2 L → ℂ)) :
    A (min k (τ ω)) = Uop L ξ (u 0) (u (min k (τ ω))) (A 0) +
      ∑ j ∈ Finset.range (min k (τ ω)), Uop L ξ (u (j + 1)) (u (min k (τ ω)))
        (A (j + 1) - Uop L ξ (u j) (u (j + 1)) (A j)) :=
  Uop_duhamel_telescope L hL hξ u (min k (τ ω)) hu0 hu1 A

end UopGrid

end RBM.Path

end
