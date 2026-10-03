/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridEnvelopeN
import RBM2D.Induction.GridDuhamelN
import RBM2D.Induction.SumZeroQ
import RBM2D.Induction.HierAlgebra
import RBM2D.Propagator.Bounds
import RBM2D.Propagator.Deriv

/-!
# The `𝒬`-hierarchy on the grid

Paper: arXiv:2503.07606, Section 5: `Def:QtPt`, `int_K-L+Q`, `zjuii2`, `pqthlk`, `int_K-L+Q2`,
`B₄`, `B₅`.

The `𝒬`-analogues of the grid statements `StoppedDuhamelN` (`stoppedDuhamelN`) and `GridDriftN`
(`gridDriftN`) for `A^Q_j = 𝒬_{u_j} A_j`, `A_j = (𝓛-𝒦)_{u_j,σ}(H_j)`:

* `aTrueQN`, `dGridQN`, `aFrozQN`, `qErrQN` (with `qStepErrN`, `lkEnvN`, `driftEnvN`): the
  process, the drift `𝒬_u D + B₄ - B₅` of `int_K-L+Q2` (the sign of `B₅` is the one that comes from
  differentiating `𝒬_u f_u`; the paper writes `+`, a misprint that is harmless since only norms
  enter), the stopped process `aFrozQN` and the explicit one-step remainder in terms of `stepErrN`;
* `gridDriftQN`: a.e., for all labels,
  `‖𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1}} A^Q_j - Δ dGridQN_j‖ ≤ qErrQN_j`;
* `stoppedDuhamelQN`: the pathwise stopped Duhamel expansion of `aFrozQN`;
* `sum_weighted_qErrQN_le`: `Σ_{j<m} (1 + (1-u_m)^{-1})^k qErrQN_j ≤ N^{-D_t}` on the grid.

The argument parallels the one-dimensional formalization.  The `d = 2` changes: labels in `Z2 L`
(`𝒫` has `(L²)^{k-1}` terms), the generator `ξ S Θ_{uξ}` of `Ugen`, `W → W²`; `ϑ`, `ϑ̇` are
bounded from the resolvent identity of `Θ` (no `d = 1` decay input); the `𝒰`-step remainder is
`uStepC`; the drift envelope is counted with `norm_primBil_le` (`W² k² L²`); the numerical
conditions are those of `SumWeightedStepErrN_Stmt`.

Some private helpers of `RBM2D.Induction.GridDriftN` are repeated here with the prefix `AltGridQ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The abstract `k`-slot tensor step -/

section TensorStep

variable {L : ℕ} [NeZero L]

/-- `(⊗_i U_i) A` at `x`: `Σ_y (Π_i U_i(x_i, y_i)) A(y)`. -/
private def AltGridQ_Tens {k : ℕ} (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin k → Z2 L) → ℂ)
    (x : Fin k → Z2 L) : ℂ :=
  ∑ y : Fin k → Z2 L, (∏ i, U i (x i) (y i)) * A y

/-- `(Σ_i (1 ⊗ ⋯ ⊗ G_i ⊗ ⋯ ⊗ 1)) A` at `x`. -/
private def AltGridQ_Gen {k : ℕ} (G : Fin k → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin k → Z2 L) → ℂ)
    (x : Fin k → Z2 L) : ℂ :=
  ∑ i : Fin k, ∑ c : Z2 L, G i (x i) c * A (Function.update x i c)

private theorem AltGridQ_Tens_zero (U : Fin 0 → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin 0 → Z2 L) → ℂ)
    (x : Fin 0 → Z2 L) : AltGridQ_Tens U A x = A x := by
  unfold AltGridQ_Tens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem AltGridQ_Gen_zero (G : Fin 0 → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin 0 → Z2 L) → ℂ)
    (x : Fin 0 → Z2 L) : AltGridQ_Gen G A x = 0 := by
  simp [AltGridQ_Gen]

private theorem AltGridQ_Tens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Z2 L) (Z2 L) ℂ)
    (A : (Fin (k + 1) → Z2 L) → ℂ) (x : Fin (k + 1) → Z2 L) :
    AltGridQ_Tens U A x = ∑ y0 : Z2 L, U 0 (x 0) y0 *
      AltGridQ_Tens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold AltGridQ_Tens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Z2 L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem AltGridQ_Gen_succ {k : ℕ} (G : Fin (k + 1) → Matrix (Z2 L) (Z2 L) ℂ)
    (A : (Fin (k + 1) → Z2 L) → ℂ) (x : Fin (k + 1) → Z2 L) :
    AltGridQ_Gen G A x = ∑ c : Z2 L, G 0 (x 0) c * A (Fin.cons c (Fin.tail x)) +
      AltGridQ_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x) := by
  unfold AltGridQ_Gen
  rw [Fin.sum_univ_succ]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Fin.cons_self_tail x, Fin.update_cons_zero]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Fin.cons_self_tail x, ← Fin.cons_update]
    simp [Fin.tail]

/-- Row sums of `P` are `≤ r`, `f` is bounded by `m`: `‖Σ_c P x c f c‖ ≤ r m`. -/
private theorem AltGridQ_row_mul {P : Matrix (Z2 L) (Z2 L) ℂ} {r m : ℝ}
    (hP : ∀ x : Z2 L, ∑ c : Z2 L, ‖P x c‖ ≤ r) (x : Z2 L) {f : Z2 L → ℂ}
    (hf : ∀ c, ‖f c‖ ≤ m) : ‖∑ c : Z2 L, P x c * f c‖ ≤ r * m := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hf x)
  calc ‖∑ c : Z2 L, P x c * f c‖ ≤ ∑ c : Z2 L, ‖P x c * f c‖ := norm_sum_le _ _
    _ = ∑ c : Z2 L, ‖P x c‖ * ‖f c‖ := by simp only [norm_mul]
    _ ≤ ∑ c : Z2 L, ‖P x c‖ * m :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _)
    _ = (∑ c : Z2 L, ‖P x c‖) * m := (Finset.sum_mul _ _ _).symm
    _ ≤ r * m := mul_le_mul_of_nonneg_right (hP x) hm

/-- Rows of `P = 1 + e` with `e` having row sums `≤ a` have row sums `≤ 1 + a`. -/
private theorem AltGridQ_row_one_add {e : Matrix (Z2 L) (Z2 L) ℂ} {a : ℝ}
    (he : ∀ x : Z2 L, ∑ c : Z2 L, ‖e x c‖ ≤ a) (x : Z2 L) :
    ∑ c : Z2 L, ‖(1 + e) x c‖ ≤ 1 + a := by
  calc ∑ c : Z2 L, ‖(1 + e) x c‖ ≤ ∑ c : Z2 L, (‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ + ‖e x c‖) :=
        Finset.sum_le_sum fun c _ => by rw [Matrix.add_apply]; exact norm_add_le _ _
    _ = ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x c‖ + ∑ c : Z2 L, ‖e x c‖ :=
        Finset.sum_add_distrib
    _ ≤ 1 + a := by
        gcongr
        · simp [Matrix.one_apply, apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq]
        · exact he x

/-- `Σ_c (1 + e) x c f c = f x + Σ_c e x c f c`. -/
private theorem AltGridQ_one_add_mul (e : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) (f : Z2 L → ℂ) :
    ∑ c : Z2 L, (1 + e) x c * f c = f x + ∑ c : Z2 L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/-- The first-order tensor bound: `‖(⊗U_i) A - A‖ ≤ ((1+a)^k - 1) M`. -/
private theorem AltGridQ_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ),
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Z2 L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖AltGridQ_Tens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [AltGridQ_Tens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Z2 L) (Z2 L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Z2 L, ∑ c : Z2 L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact AltGridQ_row_one_add (fun x'' => hU 0 x'') x'
      set T : Z2 L → ℂ := fun y0 => AltGridQ_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Z2 L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : AltGridQ_Tens U A x - A x =
          ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, e (x 0) c * Y c := by
        rw [AltGridQ_Tens_succ, hAx]
        have h1 : ∑ c : Z2 L, U 0 (x 0) c * T c =
            ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Z2 L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Z2 L, e (x 0) c * Y c := by
          rw [hU0]; exact AltGridQ_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        AltGridQ_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Z2 L, e (x 0) c * Y c‖ ≤ a * M :=
        AltGridQ_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Z2 L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

/-- The second-order tensor bound: with `‖(U_i - 1)‖_rows ≤ a`, `‖(U_i - 1 - G_i)‖_rows ≤ b`,
`‖(⊗U_i) A - A - (Σ_i G_i) A‖ ≤ (k b + (1+a)^k - 1 - k a) M`. -/
private theorem AltGridQ_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ (k : ℕ) (U G : Fin k → Matrix (Z2 L) (Z2 L) ℂ),
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1) x c‖ ≤ a) →
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1 - G i) x c‖ ≤ b) →
      ∀ (A : (Fin k → Z2 L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖AltGridQ_Tens U A x - A x - AltGridQ_Gen G A x‖ ≤ ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M := by
  intro k
  induction k with
  | zero =>
      intro U G _ _ A M _ x
      rw [AltGridQ_Tens_zero, AltGridQ_Gen_zero]
      simp
  | succ k ih =>
      intro U G hU hG A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      set e : Matrix (Z2 L) (Z2 L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      set T : Z2 L → ℂ := fun y0 => AltGridQ_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Z2 L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        AltGridQ_tens_sub_le ha k (fun i => U i.succ) (fun i x' => hU i.succ x')
          (fun y' => A (Fin.cons y0 y')) M (fun y' => hA _) (Fin.tail x)
      have hIH : ‖T (x 0) - Y (x 0) - AltGridQ_Gen (fun i : Fin k => G i.succ)
          (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x)‖ ≤
          ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M :=
        ih (fun i => U i.succ) (fun i => G i.succ) (fun i x' => hU i.succ x')
          (fun i x' => hG i.succ x') (fun y' => A (Fin.cons (x 0) y')) M (fun y' => hA _)
          (Fin.tail x)
      set g' : ℂ := AltGridQ_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y'))
        (Fin.tail x) with hg'
      have hsplit : AltGridQ_Tens U A x - A x - AltGridQ_Gen G A x =
          (T (x 0) - Y (x 0) - g') + ∑ c : Z2 L, e (x 0) c * (T c - Y c) +
            ∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c := by
        rw [AltGridQ_Tens_succ, AltGridQ_Gen_succ, hAx]
        have h1 : ∑ c : Z2 L, U 0 (x 0) c * T c =
            T (x 0) + ∑ c : Z2 L, e (x 0) c * (T c - Y c) + ∑ c : Z2 L, e (x 0) c * Y c := by
          rw [hU0, AltGridQ_one_add_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c =
            ∑ c : Z2 L, e (x 0) c * Y c - ∑ c : Z2 L, G 0 (x 0) c * Y c := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [he, Matrix.sub_apply, Matrix.sub_apply]
          ring
        rw [h1, h2]
        simp only [hT, hY, hg']
        ring
      rw [hsplit]
      have hb2 : ‖∑ c : Z2 L, e (x 0) c * (T c - Y c)‖ ≤ a * (((1 + a) ^ k - 1) * M) :=
        AltGridQ_row_mul (fun x' => hU 0 x') (x 0) hTY
      have hb3 : ‖∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c‖ ≤ b * M :=
        AltGridQ_row_mul (fun x' => hG 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖T (x 0) - Y (x 0) - g' + ∑ c : Z2 L, e (x 0) c * (T c - Y c)‖ +
            ‖∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := norm_add_le _ _
        _ ≤ (‖T (x 0) - Y (x 0) - g'‖ + ‖∑ c : Z2 L, e (x 0) c * (T c - Y c)‖) +
            ‖∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M + a * (((1 + a) ^ k - 1) * M)) +
            b * M := by gcongr
        _ = (((k + 1 : ℕ) : ℝ) * b + ((1 + a) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * a)) * M := by
            push_cast; ring

end TensorStep

/-! ## 2. One step of `𝒰` in the `Ugen` vocabulary -/

section UStep

open scoped Matrix.Norms.Operator

variable {L : ℕ} [NeZero L]

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2`. -/
private theorem AltGridQ_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ‖ = 1 := by
  cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

private theorem AltGridQ_norm_edge {E : ℝ} (hE : |E| ≤ 2) (σ σ' : Bool) :
    ‖KLoop.mSig E σ * KLoop.mSig E σ'‖ = 1 := by
  rw [norm_mul, AltGridQ_norm_mSig hE, AltGridQ_norm_mSig hE, one_mul]

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
private theorem AltGridQ_sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}`. -/
private theorem AltGridQ_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Z2 L, ‖thetaGenMat L ξ s x c‖ =
      ‖ξ‖ * ‖(SB L * Theta L ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((AltGridQ_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L ((s : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L ((s : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u` (resolvent identity
`Theta_sub_Theta`). -/
private theorem AltGridQ_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hu : ‖(u : ℂ) * ξ‖ < 1) (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ ≤
      Δ * ‖ξ‖ ^ 2 * ((1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹) := by
  have hTsub := Theta_sub_Theta L hL (ξ := (u : ℂ) * ξ) (ζ := ((u + Δ : ℝ) : ℂ) * ξ) hu hd
  have hcast : ((u + Δ : ℝ) : ℂ) * ξ - (u : ℂ) * ξ = ((Δ : ℝ) : ℂ) * ξ := by
    push_cast; ring
  rw [hcast] at hTsub
  have hM : thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u =
      (((Δ : ℝ) : ℂ) * ξ ^ 2) •
        (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ))) := by
    unfold thetaGenMat
    rw [← smul_sub, ← Matrix.mul_sub, hTsub, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hnormeq : ∀ c : Z2 L, ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ =
      Δ * ‖ξ‖ ^ 2 * ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L *
        Theta L ((u : ℂ) * ξ))) x c‖ := by
    intro c
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΔ, norm_pow]
  simp_rw [hnormeq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((AltGridQ_sum_norm_row_le_opNorm _ x).trans ?_) (by positivity)
  calc ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ))‖
      ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L * Theta L ((u : ℂ) * ξ)‖ := by
        rw [norm_SB L hL, one_mul]
    _ ≤ ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ) * SB L‖ * ‖Theta L ((u : ℂ) * ξ)‖ := norm_mul_le _ _
    _ ≤ (‖Theta L (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖SB L‖) * ‖Theta L ((u : ℂ) * ξ)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖Theta L ((u : ℂ) * ξ)‖ := by
        rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹ :=
        mul_le_mul (norm_Theta_le L hL hd) (norm_Theta_le L hL hu) (norm_nonneg _)
          (inv_nonneg.mpr (by linarith))

/-- `‖(w : ℂ) ξ‖ = w` for `‖ξ‖ = 1`, `0 ≤ w`. -/
private theorem AltGridQ_norm_real_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖(w : ℂ) * ξ‖ = w := by
  rw [norm_mul, hξ, mul_one, Complex.norm_of_nonneg hw]

/-- `(1 - vξS)Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}`, i.e. `𝒰_{u,u+Δ} - 1 = Δ · (generator at u+Δ)`
(`def_Ustz_2`). -/
private theorem AltGridQ_ukerMat_sub_one (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ}
    (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) :
    ukerMat L ξ u (u + Δ) - 1 = (Δ : ℂ) • thetaGenMat L ξ (u + Δ) := by
  have h1 : (1 : Matrix (Z2 L) (Z2 L) ℂ) - ((u : ℂ) * ξ) • SB L =
      (1 - (((u + Δ : ℝ) : ℂ) * ξ) • SB L) + ((Δ : ℂ) * ξ) • SB L := by
    push_cast
    module
  unfold ukerMat thetaGenMat
  rw [h1, add_mul, mul_Theta L hL hd, Matrix.smul_mul, add_sub_cancel_left, smul_smul]

/-- Row sums of `𝒰_{u,u+Δ} - 1` are `≤ Δ (1-(u+Δ))⁻¹` for `‖ξ‖ = 1`. -/
private theorem AltGridQ_row_U (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(ukerMat L ξ u (u + Δ) - 1) x c‖ ≤ Δ * (1 - (u + Δ))⁻¹ := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [AltGridQ_norm_real_mul hξ (by linarith)]; exact hv
  rw [AltGridQ_ukerMat_sub_one hL hd]
  have hentry : ∀ c : Z2 L, ‖((Δ : ℂ) • thetaGenMat L ξ (u + Δ)) x c‖ =
      Δ * ‖thetaGenMat L ξ (u + Δ) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  have := AltGridQ_row_thetaGenMat hL hd x
  rwa [hξ, AltGridQ_norm_real_mul hξ (by linarith), one_mul] at this

/-- Row sums of `𝒰_{u,u+Δ} - 1 - Δ (generator at u)` are `≤ Δ² (1-(u+Δ))⁻²` for `‖ξ‖ = 1`. -/
private theorem AltGridQ_row_UG (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(ukerMat L ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat L ξ u) x c‖ ≤
      Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [AltGridQ_norm_real_mul hξ (by linarith)]; exact hv
  have hu : ‖(u : ℂ) * ξ‖ < 1 := by
    rw [AltGridQ_norm_real_mul hξ hu0]; linarith
  have hM : ukerMat L ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat L ξ u =
      (Δ : ℂ) • (thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) := by
    rw [AltGridQ_ukerMat_sub_one hL hd, smul_sub]
  rw [hM]
  have hentry : ∀ c : Z2 L, ‖((Δ : ℂ) • (thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u)) x c‖ =
      Δ * ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  have h1 := AltGridQ_row_thetaGenMat_diff hL hΔ hu hd x
  rw [hξ, AltGridQ_norm_real_mul hξ (by linarith), AltGridQ_norm_real_mul hξ hu0] at h1
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβu : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hβ0 (by linarith)
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  calc Δ * ∑ c : Z2 L, ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖
      ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹)) :=
        mul_le_mul_of_nonneg_left h1 hΔ
    _ ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - (u + Δ))⁻¹)) := by gcongr
    _ = Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by ring

/-- **One step of `𝒰`** (in the `Ugen`/`thetaSig` vocabulary): for `‖A‖_max ≤ M`,
`‖𝒰_{u,u+Δ,σ} A - A - Δ ϴ_{u,σ} A‖ ≤ uStepC k Δ (u+Δ) M`. -/
private theorem AltGridQ_Ugen_step_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Z2 L) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Z2 L) :
    ‖Ugen L E σ u (u + Δ) A x - A x - (Δ : ℂ) * thetaSig L E σ u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have key := AltGridQ_tens_step_le (L := L) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u)
    (fun i x' => AltGridQ_row_U hL (AltGridQ_norm_edge hE _ _) hu0 hΔ hv x')
    (fun i x' => AltGridQ_row_UG hL (AltGridQ_norm_edge hE _ _) hu0 hΔ hv x') A M hA x
  have hT : AltGridQ_Tens (fun i : Fin k =>
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u (u + Δ)) A x =
      Ugen L E σ u (u + Δ) A x := rfl
  have hG : AltGridQ_Gen (fun i : Fin k =>
      (Δ : ℂ) • thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u) A x =
      (Δ : ℂ) * thetaSig L E σ u A x := by
    unfold AltGridQ_Gen thetaSig
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hT, hG] at key
  refine key.trans (le_of_eq ?_)
  unfold uStepC
  ring

end UStep

/-! ## 3. Grid-time facts and integrability -/

section GridFacts

private theorem AltGridQ_loopOf_wf {L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem AltGridQ_loopOf_length {L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- The grid-time facts used by `gridDriftN`: `Δ ≥ 0`, `u_j ≥ 0`, `u_{j+1} = u_j + Δ`,
`u_{j+1} < 1`, `Δ ≤ 1`. -/
private theorem AltGridQ_time_facts (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) :
    0 ≤ gridStep s t K n ∧ 0 ≤ gridTime s t K n j ∧
      gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n ∧
      gridTime s t K n (j + 1) < 1 ∧ gridStep s t K n ≤ 1 := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) hKpos.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hu : 0 ≤ gridTime s t K n j := add_nonneg hs0 (mul_nonneg hj0 hΔ)
  have hsucc : gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
    unfold gridTime; push_cast; ring
  have hKΔ : (K n : ℝ) * gridStep s t K n = t n - s n := by
    unfold gridStep; field_simp
  have hle : gridTime s t K n (j + 1) ≤ t n := by
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ K n := by exact_mod_cast Nat.succ_le_of_lt hj
    calc gridTime s t K n (j + 1) = s n + ((j + 1 : ℕ) : ℝ) * gridStep s t K n := rfl
      _ ≤ s n + (K n : ℝ) * gridStep s t K n := by gcongr
      _ = t n := by rw [hKΔ]; ring
  have hv1 : gridTime s t K n (j + 1) < 1 := lt_of_le_of_lt hle ht1
  exact ⟨hΔ, hu, hsucc, hv1, by linarith⟩

/-- Integrability of the bounded loop observable along the walk. -/
private theorem AltGridQ_integrable_gloop (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {E : ℝ}
    (hE : |E| < 2) {w : ℝ} (hw : w < 1) (I : LoopIdx (Z2 (d.L n))) (hwf : I.WF)
    (hn : 1 ≤ I.length) :
    Integrable (fun ω : PathΩ d =>
      gloop (d.L n) (d.W n) (blockMat (pathH d s t K n i ω)) (spectralZ E w) I) (pathP d) := by
  have hη : 0 < RBM.Path.etaT E w := RBM.Path.etaT_pos hE hw
  have hz : RBM.Path.etaT E w ≤ |(spectralZ E w).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (sub_pos.2 hw) (spectralM_im_pos hE))]
    exact le_rfl
  have hmeas : Measurable (fun ω : PathΩ d =>
      gloop (d.L n) (d.W n) (blockMat (pathH d s t K n i ω)) (spectralZ E w) I) :=
    (GoodEvent_measurable_gloop (d.L n) (d.W n) (spectralZ E w) I).comp
      ((pathH_measurable_filt d s t K n i).mono ((filt d).le i) le_rfl)
  exact (memLp_top_of_bound hmeas.aestronglyMeasurable
    ((RBM.Path.etaT E w)⁻¹ ^ I.a.length * (((d.W n : ℕ) : ℝ)⁻¹ ^ 2) ^ (I.a.length - 1))
    (Eventually.of_forall fun ω => norm_gloop_le_of_le_abs_im
      (show (blockMat (pathH d s t K n i ω)).IsHermitian from
        (pathH_isHermitian d s t K n i ω).submatrix _) hη hz I hwf hn)).integrable le_top

end GridFacts

/-! ## 4. `ϑ_t` and `ϑ̇_t`: sup, Lipschitz and second-order Taylor bounds

`ϑ_{t,a} = Π_{i≠0} g_t(a₀,a_i)` with the slot factor `g_t(x,y) = (1-t) Θ_t(x,y)`, `|g_t| ≤ 1`.  The
resolvent identity `Θ_v - Θ_u = (v-u) Θ_v S Θ_u` gives `g_v - g_u`, and, applied twice, its Taylor
expansion to second order with the explicit derivative `g'_u = (1-u)(ΘSΘ)_u - Θ_u`; the product
lemmas `AltGridQ_norm_prod_sub_le`, `AltGridQ_second_order` then give the bounds for `ϑ`. -/

section Vartheta

open scoped Matrix.Norms.Operator

variable {L : ℕ} [NeZero L]

/-- The slot factor `g_t(x,y) = (1-t) Θ_t(x,y)`. -/
private def AltGridQ_g (L : ℕ) [NeZero L] (t : ℝ) (x y : Z2 L) : ℂ :=
  ((1 - t : ℝ) : ℂ) * Theta L (t : ℂ) x y

/-- `g'_t(x,y) = (1-t) (Θ_t S Θ_t)(x,y) - Θ_t(x,y)`. -/
private def AltGridQ_gb (L : ℕ) [NeZero L] (t : ℝ) (x y : Z2 L) : ℂ :=
  ((1 - t : ℝ) : ℂ) * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y - Theta L (t : ℂ) x y

/-- The second-order remainder of `g`: `(1-v)(Θ_v S Θ_u S Θ_u)(x,y) - (Θ_u S Θ_u)(x,y)`, `v = u+Δ`. -/
private def AltGridQ_rho (L : ℕ) [NeZero L] (u Δ : ℝ) (x y : Z2 L) : ℂ :=
  ((1 - (u + Δ) : ℝ) : ℂ) *
      (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y -
    (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y

private theorem AltGridQ_vartheta_eq {k : ℕ} [NeZero k] (t : ℝ) (a : Fin k → Z2 L) :
    vartheta L t a = ∏ i ∈ Finset.univ.erase (0 : Fin k), AltGridQ_g L t (a 0) (a i) := by
  unfold vartheta AltGridQ_g
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

private theorem AltGridQ_norm_ofReal_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]

/-- `|g_t| ≤ 1` for `0 ≤ t < 1`. -/
private theorem AltGridQ_norm_g_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x y : Z2 L) : ‖AltGridQ_g L t x y‖ ≤ 1 := by
  have hnt := AltGridQ_norm_ofReal_of_nonneg ht0
  have hξ : ‖(t : ℂ)‖ < 1 := by rw [hnt]; exact ht1
  have h1 := norm_Theta_apply_le L hL hξ x y
  rw [hnt] at h1
  have h1t : 0 < 1 - t := by linarith
  unfold AltGridQ_g
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1t.le]
  calc (1 - t) * ‖Theta L (t : ℂ) x y‖ ≤ (1 - t) * (1 - t)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 h1t.le
    _ = 1 := mul_inv_cancel₀ h1t.ne'

/-- **`|ϑ_{t,a}| ≤ 1`** for `0 ≤ t < 1` (every entry of `Θ_t` is at most `(1-t)⁻¹`). -/
private theorem AltGridQ_norm_vartheta_le_one (hL : 3 ≤ L) {k : ℕ} [NeZero k] {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → Z2 L) : ‖vartheta L t a‖ ≤ 1 := by
  rw [AltGridQ_vartheta_eq, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun i _ => AltGridQ_norm_g_le hL ht0 ht1 _ _)

/-- The resolvent identity between the times `u` and `u + Δ`. -/
private theorem AltGridQ_theta_step (hL : 3 ≤ L) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hv1 : u + Δ < 1) :
    Theta L ((u + Δ : ℝ) : ℂ) = Theta L (u : ℂ) +
      (Δ : ℂ) • (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) := by
  have hu : ‖(u : ℂ)‖ < 1 := by rw [AltGridQ_norm_ofReal_of_nonneg hu0]; linarith
  have hv : ‖((u + Δ : ℝ) : ℂ)‖ < 1 := by
    rw [AltGridQ_norm_ofReal_of_nonneg (by linarith)]; exact hv1
  have h := Theta_sub_Theta L hL hu hv
  have hcast : ((u + Δ : ℝ) : ℂ) - (u : ℂ) = (Δ : ℂ) := by push_cast; ring
  rw [hcast] at h
  rw [← h]; abel

/-- `|(Θ_ζ S Θ_ξ)(x,y)| ≤ (1-|ζ|)⁻¹ (1-|ξ|)⁻¹`. -/
private theorem AltGridQ_norm_entry_TST (hL : 3 ≤ L) {ζ ξ : ℂ} (hζ : ‖ζ‖ < 1) (hξ : ‖ξ‖ < 1)
    (x y : Z2 L) :
    ‖(Theta L ζ * SB L * Theta L ξ) x y‖ ≤ (1 - ‖ζ‖)⁻¹ * (1 - ‖ξ‖)⁻¹ := by
  refine (norm_entry_le_norm L _ x y).trans ?_
  calc ‖Theta L ζ * SB L * Theta L ξ‖ ≤ ‖Theta L ζ * SB L‖ * ‖Theta L ξ‖ := norm_mul_le _ _
    _ ≤ (‖Theta L ζ‖ * ‖SB L‖) * ‖Theta L ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta L ζ‖ * ‖Theta L ξ‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖ζ‖)⁻¹ * (1 - ‖ξ‖)⁻¹ :=
        mul_le_mul (norm_Theta_le L hL hζ) (norm_Theta_le L hL hξ) (norm_nonneg _)
          (inv_nonneg.mpr (by linarith))

/-- `|(Θ_ζ S Θ_ξ S Θ_ξ)(x,y)| ≤ (1-|ζ|)⁻¹ ((1-|ξ|)⁻¹)²`. -/
private theorem AltGridQ_norm_entry_TSTST (hL : 3 ≤ L) {ζ ξ : ℂ} (hζ : ‖ζ‖ < 1)
    (hξ : ‖ξ‖ < 1) (x y : Z2 L) :
    ‖(Theta L ζ * SB L * Theta L ξ * SB L * Theta L ξ) x y‖ ≤
      (1 - ‖ζ‖)⁻¹ * ((1 - ‖ξ‖)⁻¹) ^ 2 := by
  refine (norm_entry_le_norm L _ x y).trans ?_
  calc ‖Theta L ζ * SB L * Theta L ξ * SB L * Theta L ξ‖
      ≤ ‖Theta L ζ * SB L * Theta L ξ * SB L‖ * ‖Theta L ξ‖ := norm_mul_le _ _
    _ ≤ (‖Theta L ζ * SB L * Theta L ξ‖ * ‖SB L‖) * ‖Theta L ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta L ζ * SB L * Theta L ξ‖ * ‖Theta L ξ‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ ((‖Theta L ζ * SB L‖) * ‖Theta L ξ‖) * ‖Theta L ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (((‖Theta L ζ‖ * ‖SB L‖)) * ‖Theta L ξ‖) * ‖Theta L ξ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          (norm_nonneg _)) (norm_nonneg _)
    _ = ‖Theta L ζ‖ * ‖Theta L ξ‖ * ‖Theta L ξ‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖ζ‖)⁻¹ * (1 - ‖ξ‖)⁻¹ * (1 - ‖ξ‖)⁻¹ := by
        have h1 := norm_Theta_le L hL hζ
        have h2 := norm_Theta_le L hL hξ
        have h0 : 0 ≤ (1 - ‖ξ‖)⁻¹ := inv_nonneg.mpr (by linarith)
        exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (inv_nonneg.mpr (by linarith))) h2
          (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (by linarith)) h0)
    _ = (1 - ‖ζ‖)⁻¹ * ((1 - ‖ξ‖)⁻¹) ^ 2 := by ring

/-- The entrywise first-order increment `g_v - g_u = Δ ((1-v)(Θ_v S Θ_u) - Θ_u)`. -/
private theorem AltGridQ_g_sub_eq (hL : 3 ≤ L) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hv1 : u + Δ < 1) (x y : Z2 L) :
    AltGridQ_g L (u + Δ) x y - AltGridQ_g L u x y =
      (Δ : ℂ) * (((1 - (u + Δ) : ℝ) : ℂ) *
        (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y - Theta L (u : ℂ) x y) := by
  have hmat := AltGridQ_theta_step (L := L) hL hu0 hΔ0 hv1
  have hentry : Theta L ((u + Δ : ℝ) : ℂ) x y = Theta L (u : ℂ) x y +
      (Δ : ℂ) * (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y := by
    have := congrFun (congrFun hmat x) y
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
  unfold AltGridQ_g
  rw [hentry]
  push_cast
  ring

/-- **First-order bound** `|g_v - g_u| ≤ 2 Δ (1-u)⁻¹`. -/
private theorem AltGridQ_norm_g_sub_le (hL : 3 ≤ L) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hv1 : u + Δ < 1) (x y : Z2 L) :
    ‖AltGridQ_g L (u + Δ) x y - AltGridQ_g L u x y‖ ≤ 2 * Δ * (1 - u)⁻¹ := by
  rw [AltGridQ_g_sub_eq hL hu0 hΔ0 hv1]
  have hu : ‖(u : ℂ)‖ < 1 := by rw [AltGridQ_norm_ofReal_of_nonneg hu0]; linarith
  have hv : ‖((u + Δ : ℝ) : ℂ)‖ < 1 := by
    rw [AltGridQ_norm_ofReal_of_nonneg (by linarith)]; exact hv1
  have hnu := AltGridQ_norm_ofReal_of_nonneg hu0
  have hnv := AltGridQ_norm_ofReal_of_nonneg (show 0 ≤ u + Δ by linarith)
  have hT := AltGridQ_norm_entry_TST hL hv hu x y
  rw [hnu, hnv] at hT
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - (u + Δ) := by linarith
  have hΘ := norm_Theta_apply_le L hL hu x y
  rw [hnu] at hΘ
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
  have hb : ‖((1 - (u + Δ) : ℝ) : ℂ) * (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y
      - Theta L (u : ℂ) x y‖ ≤ 2 * (1 - u)⁻¹ := by
    calc _ ≤ ‖((1 - (u + Δ) : ℝ) : ℂ) *
          (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y‖ + ‖Theta L (u : ℂ) x y‖ :=
          norm_sub_le _ _
      _ ≤ (1 - (u + Δ)) * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹) + (1 - u)⁻¹ := by
          refine add_le_add ?_ hΘ
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1v.le]
          exact mul_le_mul_of_nonneg_left hT h1v.le
      _ = 2 * (1 - u)⁻¹ := by field_simp; ring
  calc Δ * ‖((1 - (u + Δ) : ℝ) : ℂ) *
        (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y - Theta L (u : ℂ) x y‖
      ≤ Δ * (2 * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left hb hΔ0
    _ = 2 * Δ * (1 - u)⁻¹ := by ring

/-- **Second-order expansion of `g`**: `g_v = g_u + Δ g'_u + Δ² ρ`. -/
private theorem AltGridQ_g_taylor (hL : 3 ≤ L) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hv1 : u + Δ < 1) (x y : Z2 L) :
    AltGridQ_g L (u + Δ) x y =
      AltGridQ_g L u x y + (Δ : ℂ) * AltGridQ_gb L u x y +
        (Δ : ℂ) ^ 2 * AltGridQ_rho L u Δ x y := by
  have hmat := AltGridQ_theta_step (L := L) hL hu0 hΔ0 hv1
  have hentry : Theta L ((u + Δ : ℝ) : ℂ) x y = Theta L (u : ℂ) x y +
      (Δ : ℂ) * (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y := by
    have := congrFun (congrFun hmat x) y
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
  have hT : (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) =
      Theta L (u : ℂ) * SB L * Theta L (u : ℂ) +
        (Δ : ℂ) • (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) := by
    calc Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)
        = (Theta L (u : ℂ) + (Δ : ℂ) • (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ))) *
            SB L * Theta L (u : ℂ) := by rw [← hmat]
      _ = _ := by rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc]
  have hentry2 : (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ)) x y =
      (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y + (Δ : ℂ) *
        (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y := by
    have := congrFun (congrFun hT x) y
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
  unfold AltGridQ_g AltGridQ_gb AltGridQ_rho
  rw [hentry, hentry2]
  push_cast
  ring

/-- `‖ρ‖ ≤ 2 ((1-u)⁻¹)²`. -/
private theorem AltGridQ_norm_rho_le (hL : 3 ≤ L) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hv1 : u + Δ < 1) (x y : Z2 L) :
    ‖AltGridQ_rho L u Δ x y‖ ≤ 2 * ((1 - u)⁻¹) ^ 2 := by
  have hu : ‖(u : ℂ)‖ < 1 := by rw [AltGridQ_norm_ofReal_of_nonneg hu0]; linarith
  have hv : ‖((u + Δ : ℝ) : ℂ)‖ < 1 := by
    rw [AltGridQ_norm_ofReal_of_nonneg (by linarith)]; exact hv1
  have hnu := AltGridQ_norm_ofReal_of_nonneg hu0
  have hnv := AltGridQ_norm_ofReal_of_nonneg (show 0 ≤ u + Δ by linarith)
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - (u + Δ) := by linarith
  have h5 := AltGridQ_norm_entry_TSTST hL hv hu x y
  rw [hnu, hnv] at h5
  have h6 := AltGridQ_norm_entry_TST hL hu hu x y
  rw [hnu] at h6
  unfold AltGridQ_rho
  calc _ ≤ ‖((1 - (u + Δ) : ℝ) : ℂ) *
        (Theta L ((u + Δ : ℝ) : ℂ) * SB L * Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ +
      ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ := norm_sub_le _ _
    _ ≤ (1 - (u + Δ)) * ((1 - (u + Δ))⁻¹ * ((1 - u)⁻¹) ^ 2) + (1 - u)⁻¹ * (1 - u)⁻¹ := by
        refine add_le_add ?_ h6
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1v.le]
        exact mul_le_mul_of_nonneg_left h5 h1v.le
    _ = 2 * ((1 - u)⁻¹) ^ 2 := by field_simp; ring

/-- `∂_t g_t(x,y) = g'_t(x,y)`. -/
private theorem AltGridQ_hasDerivAt_g (hL : 3 ≤ L) {t : ℝ} (ht : |t| < 1) (x y : Z2 L) :
    HasDerivAt (fun s : ℝ => AltGridQ_g L s x y) (AltGridQ_gb L t x y) t := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h1 : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) t := by
    have hid : HasDerivAt (fun v : ℝ => 1 - v) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    exact hid.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => Theta L (s : ℂ) x y)
      ((Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y) t :=
    (hasDerivAt_Theta_apply L hL hξ x y).comp_ofReal
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  unfold AltGridQ_gb
  push_cast
  ring

/-- `ϑ̇_t` through the slot factors (Leibniz rule). -/
private theorem AltGridQ_varthetaDot_eq' (hL : 3 ≤ L) {k : ℕ} [NeZero k] {t : ℝ} (ht : |t| < 1)
    (a : Fin k → Z2 L) :
    varthetaDot L t a = ∑ j ∈ Finset.univ.erase (0 : Fin k),
      (∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, AltGridQ_g L t (a 0) (a i)) *
        AltGridQ_gb L t (a 0) (a j) := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ.erase (0 : Fin k))
    (f := fun i (s : ℝ) => AltGridQ_g L s (a 0) (a i))
    (f' := fun i => AltGridQ_gb L t (a 0) (a i)) (x := t)
    (fun j _ => AltGridQ_hasDerivAt_g hL ht (a 0) (a j))
  have hf : (fun v : ℝ => vartheta L v a) =
      fun v => ∏ i ∈ Finset.univ.erase (0 : Fin k), AltGridQ_g L v (a 0) (a i) :=
    funext fun v => AltGridQ_vartheta_eq v a
  unfold varthetaDot
  rw [hf, h.deriv]
  simp only [smul_eq_mul]

/-- `‖Π f - Π g‖ ≤ Σ ‖f_i - g_i‖` for factors of norm at most `1`. -/
private theorem AltGridQ_norm_prod_sub_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have ih' := ih hf' hg'
    have hga : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) hg'
    have hfa := hf a (Finset.mem_insert_self a s)
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    calc _ ≤ ‖f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ + ‖(f a - g a) * ∏ i ∈ s, g i‖ :=
          norm_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, ‖f i - g i‖ + ‖f a - g a‖ * 1 := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul hfa ih' (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hga (norm_nonneg _))
      _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by ring

/-- **Second-order product bound**: for `F_i = f_i + x_i`, `‖f_i‖, ‖F_i‖ ≤ 1`, `‖x_i‖ ≤ ε`,
`‖Π F - Π f - Σ_j x_j Π_{i≠j} f_i‖ ≤ (|s|(|s|-1)/2) ε²`. -/
private theorem AltGridQ_second_order {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f F x : ι → ℂ) {ε : ℝ} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hF : ∀ i ∈ s, ‖F i‖ ≤ 1)
    (hx : ∀ i ∈ s, F i = f i + x i) (hε : ∀ i ∈ s, ‖x i‖ ≤ ε) :
    ‖∏ i ∈ s, F i - ∏ i ∈ s, f i - ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i‖ ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) / 2 * ε ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hF' : ∀ i ∈ s, ‖F i‖ ≤ 1 := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hx' : ∀ i ∈ s, F i = f i + x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hε' : ∀ i ∈ s, ‖x i‖ ≤ ε := fun i hi => hε i (Finset.mem_insert_of_mem hi)
    have ih' := ih hf' hF' hx' hε'
    have hfa := hf a (Finset.mem_insert_self a s)
    have hxa := hε a (Finset.mem_insert_self a s)
    have hFa := hx a (Finset.mem_insert_self a s)
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans hxa
    have hlip := AltGridQ_norm_prod_sub_le s F f hF' hf'
    have hlip' : ‖∏ i ∈ s, F i - ∏ i ∈ s, f i‖ ≤ (s.card : ℝ) * ε := by
      refine hlip.trans ?_
      calc ∑ i ∈ s, ‖F i - f i‖ ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum fun i hi => by
            rw [hx' i hi, add_sub_cancel_left]; exact hε' i hi
        _ = (s.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    have hsum : ∑ j ∈ insert a s, x j * ∏ i ∈ (insert a s).erase j, f i =
        x a * ∏ i ∈ s, f i + f a * ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i := by
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (by simp [ha])]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hsum, hFa]
    have e : (f a + x a) * ∏ i ∈ s, F i - f a * ∏ i ∈ s, f i -
        (x a * ∏ i ∈ s, f i + f a * ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i) =
        f a * (∏ i ∈ s, F i - ∏ i ∈ s, f i - ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i) +
          x a * (∏ i ∈ s, F i - ∏ i ∈ s, f i) := by ring
    rw [e, Finset.card_insert_of_notMem ha]
    push_cast
    calc _ ≤ ‖f a * (∏ i ∈ s, F i - ∏ i ∈ s, f i - ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i)‖ +
          ‖x a * (∏ i ∈ s, F i - ∏ i ∈ s, f i)‖ := norm_add_le _ _
      _ ≤ 1 * ((s.card : ℝ) * ((s.card : ℝ) - 1) / 2 * ε ^ 2) + ε * ((s.card : ℝ) * ε) := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul hfa ih' (norm_nonneg _) zero_le_one)
            (mul_le_mul hxa hlip' (norm_nonneg _) hε0)
      _ = ((s.card : ℝ) + 1) * ((s.card : ℝ) + 1 - 1) / 2 * ε ^ 2 := by ring

/-- **Lipschitz bound of `ϑ`**: `‖ϑ_{u+Δ,a} - ϑ_{u,a}‖ ≤ 2(k-1) Δ (1-u)⁻¹`. -/
private theorem AltGridQ_vartheta_lip (hL : 3 ≤ L) {k : ℕ} [NeZero k] {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ0 : 0 ≤ Δ) (hv1 : u + Δ < 1) (a : Fin k → Z2 L) :
    ‖vartheta L (u + Δ) a - vartheta L u a‖ ≤ 2 * ((k : ℝ) - 1) * Δ * (1 - u)⁻¹ := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  rw [AltGridQ_vartheta_eq, AltGridQ_vartheta_eq]
  refine (AltGridQ_norm_prod_sub_le _ _ _
    (fun i _ => AltGridQ_norm_g_le hL (by linarith) hv1 _ _)
    (fun i _ => AltGridQ_norm_g_le hL hu0 (by linarith) _ _)).trans ?_
  calc ∑ i ∈ Finset.univ.erase (0 : Fin k),
        ‖AltGridQ_g L (u + Δ) (a 0) (a i) - AltGridQ_g L u (a 0) (a i)‖
      ≤ ∑ _i ∈ Finset.univ.erase (0 : Fin k), 2 * Δ * (1 - u)⁻¹ :=
        Finset.sum_le_sum fun i _ => AltGridQ_norm_g_sub_le hL hu0 hΔ0 hv1 _ _
    _ = 2 * ((k : ℝ) - 1) * Δ * (1 - u)⁻¹ := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast [Nat.cast_sub hk1]
        ring

/-- **Second-order Taylor bound of `ϑ`** (`k ≥ 1`):
`‖ϑ_{u+Δ,a} - ϑ_{u,a} - Δ ϑ̇_{u,a}‖ ≤ 2(k-1)² ((1-u)⁻¹)² Δ²`. -/
private theorem AltGridQ_vartheta_taylor (hL : 3 ≤ L) {k : ℕ} [NeZero k] {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hv1 : u + Δ < 1) (a : Fin k → Z2 L) :
    ‖vartheta L (u + Δ) a - vartheta L u a - (Δ : ℂ) * varthetaDot L u a‖ ≤
      2 * ((k : ℝ) - 1) ^ 2 * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hu1 : u < 1 := by linarith
  have h1u : 0 < 1 - u := by linarith
  set s : Finset (Fin k) := Finset.univ.erase 0 with hs
  set f : Fin k → ℂ := fun i => AltGridQ_g L u (a 0) (a i) with hf
  set F : Fin k → ℂ := fun i => AltGridQ_g L (u + Δ) (a 0) (a i) with hF
  set x : Fin k → ℂ := fun i => F i - f i with hx
  have hf1 : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i _ => AltGridQ_norm_g_le hL hu0 hu1 _ _
  have hF1 : ∀ i ∈ s, ‖F i‖ ≤ 1 := fun i _ => AltGridQ_norm_g_le hL (by linarith) hv1 _ _
  have hε : ∀ i ∈ s, ‖x i‖ ≤ 2 * Δ * (1 - u)⁻¹ := fun i _ =>
    AltGridQ_norm_g_sub_le hL hu0 hΔ0 hv1 _ _
  have h2 := AltGridQ_second_order s f F x hf1 hF1 (fun i _ => by simp [hx]) hε
  have hdot := AltGridQ_varthetaDot_eq' hL (t := u) (by rw [abs_of_nonneg hu0]; exact hu1) a
  have hxi : ∀ i, x i = (Δ : ℂ) * AltGridQ_gb L u (a 0) (a i) +
      (Δ : ℂ) ^ 2 * AltGridQ_rho L u Δ (a 0) (a i) := fun i => by
    have := AltGridQ_g_taylor hL hu0 hΔ0 hv1 (a 0) (a i)
    simp only [hx, hF, hf]
    rw [this]; ring
  have hsum : ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i =
      (Δ : ℂ) * varthetaDot L u a + (Δ : ℂ) ^ 2 *
        ∑ j ∈ s, AltGridQ_rho L u Δ (a 0) (a j) * ∏ i ∈ s.erase j, f i := by
    rw [hdot, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxi j]
    simp only [hf]
    ring
  have hid : vartheta L (u + Δ) a - vartheta L u a - (Δ : ℂ) * varthetaDot L u a =
      (∏ i ∈ s, F i - ∏ i ∈ s, f i - ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i) +
        (Δ : ℂ) ^ 2 * ∑ j ∈ s, AltGridQ_rho L u Δ (a 0) (a j) * ∏ i ∈ s.erase j, f i := by
    rw [AltGridQ_vartheta_eq, AltGridQ_vartheta_eq, hsum]
    simp only [hF, hf]
    ring
  rw [hid]
  have hcard : (s.card : ℝ) = (k : ℝ) - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub hk1]; ring
  have hP : ∀ j ∈ s, ‖∏ i ∈ s.erase j, f i‖ ≤ 1 := fun j _ => by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i hi => hf1 i (Finset.mem_of_mem_erase hi))
  have hρ : ‖(Δ : ℂ) ^ 2 * ∑ j ∈ s, AltGridQ_rho L u Δ (a 0) (a j) * ∏ i ∈ s.erase j, f i‖ ≤
      Δ ^ 2 * ((s.card : ℝ) * (2 * ((1 - u)⁻¹) ^ 2)) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ s, ‖AltGridQ_rho L u Δ (a 0) (a j) * ∏ i ∈ s.erase j, f i‖
        ≤ ∑ _j ∈ s, 2 * ((1 - u)⁻¹) ^ 2 := Finset.sum_le_sum fun j hj => by
          rw [norm_mul]
          calc ‖AltGridQ_rho L u Δ (a 0) (a j)‖ * ‖∏ i ∈ s.erase j, f i‖
              ≤ (2 * ((1 - u)⁻¹) ^ 2) * 1 :=
                mul_le_mul (AltGridQ_norm_rho_le hL hu0 hΔ0 hv1 _ _) (hP j hj) (norm_nonneg _)
                  (by positivity)
            _ = 2 * ((1 - u)⁻¹) ^ 2 := mul_one _
      _ = (s.card : ℝ) * (2 * ((1 - u)⁻¹) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  have h2' : ‖∏ i ∈ s, F i - ∏ i ∈ s, f i - ∑ j ∈ s, x j * ∏ i ∈ s.erase j, f i‖ ≤
      2 * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by
    refine h2.trans (le_of_eq ?_)
    rw [hcard]
    ring
  refine (add_le_add h2' hρ).trans (le_of_eq ?_)
  rw [hcard]
  ring

end Vartheta

/-! ## 5. The definitions -/

section Defs

/-- **`A^Q_j = 𝒬_{u_j} A_j`**, with
`A_j = (𝓛-𝒦)_{u_j,σ}(H_j)` the process `AvecN` and `(𝒬_t 𝒜)_a = 𝒜_a - (𝒫𝒜)_{a₁} ϑ_{t,a}`. -/
def aTrueQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (j : ℕ) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  Qop (d.L n) (gridTime s t K n j) (AvecN d E s t K n j σ ω)

/-- **The drift of `int_K-L+Q2`** at the grid time `u_j`: `𝒬_{u_j}` of the drift
`Σ_{l≥3} [𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}`, plus `ℬ₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)_{u,σ}` (`B4`),
minus `ℬ₅ = 𝒫(𝓛-𝒦)_{u,σ} ϑ̇_u` (`B5`); the sign of the `ϑ̇` term is the one that comes from
differentiating `𝒬_u f_u` (the paper writes `+`, a misprint that is harmless since only norms
enter). -/
def dGridQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (j : ℕ) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a =>
    Qop (d.L n) (gridTime s t K n j)
        (fun b => ∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
              (pathH d s t K n j ω) l (loopOf σ b) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
              (loopOf σ b) +
            egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
              (loopOf σ b)) a +
      B4 (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) σ a -
      B5 (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) σ a

/-- **The stopped `𝒬`-process**: the process stopped at `τ`
and then propagated by the kernel, `A^{Q,frz}_m = 𝒰_{u_{m∧τ},u_m,σ} A^Q_{m∧τ}`. -/
def aFrozQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (τ : PathΩ d → ℕ) (m : ℕ) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  Ugen (d.L n) (E n) σ (gridTime s t K n (min m (τ ω))) (gridTime s t K n m)
    (aTrueQN d E s t K n σ (min m (τ ω)) ω)

/-- The martingale increment `ξ^Q_{j+1} = A^Q_{j+1} - 𝔼[A^Q_{j+1} | F_j]`. -/
def martIncQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (j : ℕ) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => aTrueQN d E s t K n σ (j + 1) ω a -
    (pathP d)[fun ω' => aTrueQN d E s t K n σ (j + 1) ω' a | filt d j] ω

/-- The exact one-step remainder of the `𝒬`-process, named by subtraction:
`R^Q_j = 𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A^Q_j - Δ dGridQN_j`. -/
def rGridQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (j : ℕ) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => (pathP d)[fun ω' => aTrueQN d E s t K n σ (j + 1) ω' a | filt d j] ω -
    Ugen (d.L n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (aTrueQN d E s t K n σ j ω) a -
    (gridStep s t K n : ℂ) * dGridQN d E s t K n σ j ω a

/-- The deterministic sup bound on `A_j = (𝓛-𝒦)_{u,σ}` at loop length `k` (`|𝓛| ≤ η^{-k} W^{-2(k-1)}`
plus the `𝒦` envelope `Bk`); the bracket of `stepErrN`. -/
def lkEnvN (W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
  (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk

/-- The explicit crude envelope of the drift `Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}` at loop
length `k`: with `B_F = η^{-k} + Bk` a bound of `|𝓛-𝒦|` on the loops of length
`2..k`, `W² L² (k · 2k² B_F Bk + k² B_F² + k (η⁻¹ + 1) η^{-(k+1)})`. -/
def driftEnvN (L W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
  (W : ℝ) ^ 2 * (L : ℝ) ^ 2 *
    ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) +
      (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) +
      (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))

/-- The explicit one-step remainder of the `𝒬` identity, `Lp = (L²)^{k-1}` the number of terms of
`𝒫`, `β = (1-(u+Δ))⁻¹`:
`(1+Lp) S + Δ Lp Dm Vd + 2 Lp Ust Mk + Lp Mk τB + Δ Lp (kβMk) Vd` with `S` the `stepErrN`
bound, `Mk`, `Dm` the sup bounds of `A_j` and of the drift, `Ust = uStepC k Δ (u+Δ)`,
`Vd = 2(k-1)βΔ` (Lipschitz constant of `ϑ`) and `τB = 2(k-1)²β²Δ²` (its Taylor remainder). -/
def qStepErrN (L k : ℕ) (u Δ Mk Dm S : ℝ) : ℝ :=
  (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * S +
    (Δ * (((L : ℝ) ^ 2) ^ (k - 1) * Dm) * (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) +
      2 * (((L : ℝ) ^ 2) ^ (k - 1) * (uStepC k Δ (u + Δ) * Mk)) +
      ((L : ℝ) ^ 2) ^ (k - 1) * Mk * (2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) +
      Δ * (((L : ℝ) ^ 2) ^ (k - 1) * ((k : ℝ) * (1 - (u + Δ))⁻¹ * Mk)) *
        (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ))

/-- **The explicit one-step remainder of the grid step `j` of `int_K-L+Q2`**, in terms of
`stepErrN`, `Bk` the `𝒦` envelope on
`[0, u_{j+1}]`. -/
def qErrQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Bk : ℝ) (j : ℕ) : ℝ :=
  qStepErrN (d.L n) k (gridTime s t K n j) (gridStep s t K n)
    (lkEnvN (d.W n) (E n) k (gridTime s t K n j) Bk)
    (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j) Bk)
    (stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
      (gridStep s t K n) Bk)

end Defs

/-! ## 6. The deterministic `𝒬` algebra of one step -/

section QAlgebra

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem AltGridQ_Psum_add (A B : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    Psum L (fun b => A b + B b) x = Psum L A x + Psum L B x := by
  simp only [Psum, Finset.sum_add_distrib]

private theorem AltGridQ_Psum_mul (c : ℂ) (A : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    Psum L (fun b => c * A b) x = c * Psum L A x := by
  simp only [Psum, Finset.mul_sum]

/-- Crude counting bound `‖𝒫𝒜‖ ≤ (L²)^{k-1} max‖𝒜‖`. -/
private theorem AltGridQ_norm_Psum_le {A : (Fin k → Z2 L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (x : Z2 L) : ‖Psum L A x‖ ≤ ((L : ℝ) ^ 2) ^ (k - 1) * M := by
  unfold Psum
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_le_card_nsmul (Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = x))
    (fun a => ‖A a‖) M (fun a _ => hA a)
  rw [nsmul_eq_mul, SumZeroQ_card_filter x] at h
  exact h

private theorem AltGridQ_Ugen_sub (E : ℝ) (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Ugen L E σ v w (fun b => A b - B b) a = Ugen L E σ v w A a - Ugen L E σ v w B a := by
  simp only [Ugen, mul_sub, Finset.sum_sub_distrib]

/-- `‖ϴ_{u,σ} 𝒜‖_max ≤ k (1-u)⁻¹ ‖𝒜‖_max` (row sums of the generator `ξ S Θ_{uξ}`). -/
private theorem AltGridQ_norm_thetaSig_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin k → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {A : (Fin k → Z2 L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Z2 L) :
    ‖thetaSig L E σ u A a‖ ≤ (k : ℝ) * (1 - u)⁻¹ * M := by
  unfold thetaSig
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Z2 L, thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))
          u (a i) b * A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hξ := AltGridQ_norm_edge hE (σ i) (σ (i + 1))
        have hsξ : ‖(u : ℂ) * (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))‖ < 1 := by
          rw [AltGridQ_norm_real_mul hξ hu0]; exact hu1
        exact AltGridQ_row_mul
          (P := thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u)
          (fun x => by
            have := AltGridQ_row_thetaGenMat hL hsξ x
            rwa [hξ, AltGridQ_norm_real_mul hξ hu0, one_mul] at this) (a i) (fun c => hA _)
    _ = (k : ℝ) * (1 - u)⁻¹ * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private theorem AltGridQ_norm_six_le (T1 T2 T3 T4 T5 T6 : ℂ) :
    ‖T1 + T2 + T3 + T4 + T5 - T6‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by
  calc _ ≤ ‖T1 + T2 + T3 + T4 + T5‖ + ‖T6‖ := norm_sub_le _ _
    _ ≤ ‖T1 + T2 + T3 + T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1 + T2 + T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1 + T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _

/-- **The deterministic core of the one-step `𝒬`-identity**: if `c = 𝒰_{u,u+Δ} X + Δ D + e` with
`‖e‖ ≤ S` (the conclusion of `gridDriftN`), then
`𝒬_{u+Δ} c - 𝒰_{u,u+Δ}(𝒬_u X) = Δ (𝒬_u D + [𝒬_u, ϴ_{u,σ}] X - 𝒫X ϑ̇_u) + R`, `‖R‖ ≤ qStepErrN`.
Exact identity:
`R = (e - 𝒫e ϑ_v) + Δ 𝒫D (ϑ_u-ϑ_v) + 𝒫X (ϑ_u-ϑ_v+Δϑ̇_u) + Δ 𝒫(ϴX)(ϑ_u-ϑ_v) + R_U(𝒫Xϑ_u) - 𝒫(R_U X) ϑ_v`,
`R_U = 𝒰 - 1 - Δ ϴ`. -/
private theorem AltGridQ_qstep_algebra (hL : 3 ≤ L) (hk : 2 ≤ k) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1)
    {X D c : (Fin k → Z2 L) → ℂ} {Mk Dm S : ℝ} (hX : ∀ b, ‖X b‖ ≤ Mk) (hD : ∀ b, ‖D b‖ ≤ Dm)
    (hc : ∀ b, ‖c b - Ugen L E σ u (u + Δ) X b - (Δ : ℂ) * D b‖ ≤ S) (a : Fin k → Z2 L) :
    ‖Qop L (u + Δ) c a - Ugen L E σ u (u + Δ) (Qop L u X) a -
        (Δ : ℂ) * (Qop L u D a +
          (Qop L u (thetaSig L E σ u X) a - thetaSig L E σ u (Qop L u X) a) -
          Psum L X (a 0) * varthetaDot L u a)‖ ≤ qStepErrN L k u Δ Mk Dm S := by
  have hu1 : u < 1 := by linarith
  have hv0 : 0 ≤ u + Δ := by linarith
  have hMk0 : 0 ≤ Mk := (norm_nonneg _).trans (hX a)
  have hDm0 : 0 ≤ Dm := (norm_nonneg _).trans (hD a)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hc a)
  set Lp : ℝ := ((L : ℝ) ^ 2) ^ (k - 1) with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  set Ust : ℝ := uStepC k Δ (u + Δ) with hUst
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβ
  have hβ0 : 0 ≤ β := inv_nonneg.mpr (by linarith)
  have hβu : (1 - u)⁻¹ ≤ β := inv_anti₀ (by linarith) (by linarith)
  have hβu0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr (by linarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  -- the objects
  set Y : (Fin k → Z2 L) → ℂ := fun b => Psum L X (b 0) * vartheta L u b with hY
  set e : (Fin k → Z2 L) → ℂ := fun b => c b - Ugen L E σ u (u + Δ) X b - (Δ : ℂ) * D b with he
  set εX : (Fin k → Z2 L) → ℂ := fun b =>
    Ugen L E σ u (u + Δ) X b - X b - (Δ : ℂ) * thetaSig L E σ u X b with hεX
  set εY : (Fin k → Z2 L) → ℂ := fun b =>
    Ugen L E σ u (u + Δ) Y b - Y b - (Δ : ℂ) * thetaSig L E σ u Y b with hεY
  have hUst0 : 0 ≤ Ust := by
    unfold Ust uStepC
    have hx0 : 0 ≤ Δ * (1 - (u + Δ))⁻¹ := mul_nonneg hΔ0 hβ0
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - (u + Δ))⁻¹ by linarith) k
    have e1 : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by positivity
    nlinarith [hb]
  have hεXb : ∀ b, ‖εX b‖ ≤ Ust * Mk := fun b =>
    AltGridQ_Ugen_step_le hL hE σ hu0 hΔ0 hut1 X Mk hX b
  have hϑu := AltGridQ_norm_vartheta_le_one (k := k) hL hu0 hu1
  have hϑv := AltGridQ_norm_vartheta_le_one (k := k) hL hv0 hut1
  have hYb : ∀ b, ‖Y b‖ ≤ Lp * Mk := fun b => by
    simp only [hY]
    rw [norm_mul]
    calc ‖Psum L X (b 0)‖ * ‖vartheta L u b‖ ≤ (Lp * Mk) * 1 :=
          mul_le_mul (AltGridQ_norm_Psum_le hX _) (hϑu b) (norm_nonneg _)
            (by positivity)
      _ = Lp * Mk := mul_one _
  have hεYb : ∀ b, ‖εY b‖ ≤ Ust * (Lp * Mk) := fun b =>
    AltGridQ_Ugen_step_le hL hE σ hu0 hΔ0 hut1 Y (Lp * Mk) hYb b
  have heb : ∀ b, ‖e b‖ ≤ S := hc
  -- the `Psum` identities
  have h3 : Psum L c (a 0) = Psum L e (a 0) + Psum L (Ugen L E σ u (u + Δ) X) (a 0) +
      (Δ : ℂ) * Psum L D (a 0) := by
    have h1 : (fun b => c b) = fun b => (e b + Ugen L E σ u (u + Δ) X b) + (Δ : ℂ) * D b := by
      funext b; simp only [he]; ring
    calc Psum L c (a 0) = Psum L (fun b => (e b + Ugen L E σ u (u + Δ) X b) + (Δ : ℂ) * D b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [AltGridQ_Psum_add, AltGridQ_Psum_add, AltGridQ_Psum_mul]
  have h4 : Psum L (Ugen L E σ u (u + Δ) X) (a 0) = Psum L X (a 0) +
      (Δ : ℂ) * Psum L (thetaSig L E σ u X) (a 0) + Psum L εX (a 0) := by
    have h1 : (fun b => Ugen L E σ u (u + Δ) X b) =
        fun b => (X b + (Δ : ℂ) * thetaSig L E σ u X b) + εX b := by
      funext b; simp only [hεX]; ring
    calc Psum L (Ugen L E σ u (u + Δ) X) (a 0)
        = Psum L (fun b => (X b + (Δ : ℂ) * thetaSig L E σ u X b) + εX b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [AltGridQ_Psum_add, AltGridQ_Psum_add, AltGridQ_Psum_mul]
  have hQX : Qop L u X = fun b => X b - Y b := rfl
  have h5 : Ugen L E σ u (u + Δ) (Qop L u X) a =
      Ugen L E σ u (u + Δ) X a - Ugen L E σ u (u + Δ) Y a := by
    rw [hQX]; exact AltGridQ_Ugen_sub E σ u (u + Δ) X Y a
  have h6 : thetaSig L E σ u (Qop L u X) a =
      thetaSig L E σ u X a - thetaSig L E σ u Y a := by
    rw [hQX]; exact SumZeroQ_thetaSig_sub E σ u X Y a
  -- the exact identity
  have key : Qop L (u + Δ) c a - Ugen L E σ u (u + Δ) (Qop L u X) a -
      (Δ : ℂ) * (Qop L u D a +
        (Qop L u (thetaSig L E σ u X) a - thetaSig L E σ u (Qop L u X) a) -
        Psum L X (a 0) * varthetaDot L u a) =
      (e a - Psum L e (a 0) * vartheta L (u + Δ) a) +
        (Δ : ℂ) * Psum L D (a 0) * (vartheta L u a - vartheta L (u + Δ) a) +
        Psum L X (a 0) * (vartheta L u a - vartheta L (u + Δ) a + (Δ : ℂ) * varthetaDot L u a) +
        (Δ : ℂ) * Psum L (thetaSig L E σ u X) (a 0) *
          (vartheta L u a - vartheta L (u + Δ) a) +
        εY a - Psum L εX (a 0) * vartheta L (u + Δ) a := by
    rw [h5, h6]
    simp only [Qop]
    have hYa : Y a = Psum L X (a 0) * vartheta L u a := rfl
    have hea : e a = c a - Ugen L E σ u (u + Δ) X a - (Δ : ℂ) * D a := rfl
    have hεYa : εY a = Ugen L E σ u (u + Δ) Y a - Y a - (Δ : ℂ) * thetaSig L E σ u Y a := rfl
    rw [h3, h4] at *
    linear_combination (-1 : ℂ) * hea + (-1 : ℂ) * hεYa + (1 : ℂ) * hYa
  rw [key]
  -- the bounds on `ϑ`
  have hVd : ‖vartheta L u a - vartheta L (u + Δ) a‖ ≤ 2 * ((k : ℝ) - 1) * β * Δ := by
    rw [norm_sub_rev]
    refine (AltGridQ_vartheta_lip hL hu0 hΔ0 hut1 a).trans ?_
    have h0 : 0 ≤ 2 * ((k : ℝ) - 1) * Δ := by
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    calc 2 * ((k : ℝ) - 1) * Δ * (1 - u)⁻¹ ≤ 2 * ((k : ℝ) - 1) * Δ * β :=
          mul_le_mul_of_nonneg_left hβu h0
      _ = 2 * ((k : ℝ) - 1) * β * Δ := by ring
  have hτB : ‖vartheta L u a - vartheta L (u + Δ) a + (Δ : ℂ) * varthetaDot L u a‖ ≤
      2 * ((k : ℝ) - 1) ^ 2 * β ^ 2 * Δ ^ 2 := by
    have h := AltGridQ_vartheta_taylor hL hu0 hΔ0 hut1 a
    have e' : vartheta L u a - vartheta L (u + Δ) a + (Δ : ℂ) * varthetaDot L u a =
        -(vartheta L (u + Δ) a - vartheta L u a - (Δ : ℂ) * varthetaDot L u a) := by ring
    rw [e', norm_neg]
    refine h.trans ?_
    have h0 : 0 ≤ 2 * ((k : ℝ) - 1) ^ 2 * Δ ^ 2 := by positivity
    calc 2 * ((k : ℝ) - 1) ^ 2 * ((1 - u)⁻¹) ^ 2 * Δ ^ 2
        = (2 * ((k : ℝ) - 1) ^ 2 * Δ ^ 2) * ((1 - u)⁻¹) ^ 2 := by ring
      _ ≤ (2 * ((k : ℝ) - 1) ^ 2 * Δ ^ 2) * β ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβu0 hβu 2) h0
      _ = 2 * ((k : ℝ) - 1) ^ 2 * β ^ 2 * Δ ^ 2 := by ring
  have hPe : ‖Psum L e (a 0)‖ ≤ Lp * S := AltGridQ_norm_Psum_le heb _
  have hPD : ‖Psum L D (a 0)‖ ≤ Lp * Dm := AltGridQ_norm_Psum_le hD _
  have hPX : ‖Psum L X (a 0)‖ ≤ Lp * Mk := AltGridQ_norm_Psum_le hX _
  have hΘX : ∀ b, ‖thetaSig L E σ u X b‖ ≤ (k : ℝ) * β * Mk := fun b =>
    (AltGridQ_norm_thetaSig_le hL hE σ hu0 hu1 hX b).trans (by
      have h0 : 0 ≤ (k : ℝ) * Mk := by positivity
      calc (k : ℝ) * (1 - u)⁻¹ * Mk = ((k : ℝ) * Mk) * (1 - u)⁻¹ := by ring
        _ ≤ ((k : ℝ) * Mk) * β := mul_le_mul_of_nonneg_left hβu h0
        _ = (k : ℝ) * β * Mk := by ring)
  have hPΘ : ‖Psum L (thetaSig L E σ u X) (a 0)‖ ≤ Lp * ((k : ℝ) * β * Mk) :=
    AltGridQ_norm_Psum_le hΘX _
  have hPεX : ‖Psum L εX (a 0)‖ ≤ Lp * (Ust * Mk) := AltGridQ_norm_Psum_le hεXb _
  have hϑva := hϑv a
  have hVd0 : 0 ≤ 2 * ((k : ℝ) - 1) * β * Δ := by
    have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    positivity
  have t1 : ‖e a - Psum L e (a 0) * vartheta L (u + Δ) a‖ ≤ (1 + Lp) * S := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖Psum L e (a 0)‖ * ‖vartheta L (u + Δ) a‖ ≤ (Lp * S) * 1 :=
      mul_le_mul hPe hϑva (norm_nonneg _) (by positivity)
    have := heb a
    nlinarith
  have t2 : ‖(Δ : ℂ) * Psum L D (a 0) * (vartheta L u a - vartheta L (u + Δ) a)‖ ≤
      Δ * (Lp * Dm) * (2 * ((k : ℝ) - 1) * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPD hΔ0) hVd (norm_nonneg _) (by positivity)
  have t3 : ‖Psum L X (a 0) *
      (vartheta L u a - vartheta L (u + Δ) a + (Δ : ℂ) * varthetaDot L u a)‖ ≤
      Lp * Mk * (2 * ((k : ℝ) - 1) ^ 2 * β ^ 2 * Δ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hPX hτB (norm_nonneg _) (by positivity)
  have t4 : ‖(Δ : ℂ) * Psum L (thetaSig L E σ u X) (a 0) *
      (vartheta L u a - vartheta L (u + Δ) a)‖ ≤
      Δ * (Lp * ((k : ℝ) * β * Mk)) * (2 * ((k : ℝ) - 1) * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPΘ hΔ0) hVd (norm_nonneg _) (by positivity)
  have t5 : ‖εY a‖ ≤ Ust * (Lp * Mk) := hεYb a
  have t6 : ‖Psum L εX (a 0) * vartheta L (u + Δ) a‖ ≤ Lp * (Ust * Mk) := by
    rw [norm_mul]
    have h1 : ‖Psum L εX (a 0)‖ * ‖vartheta L (u + Δ) a‖ ≤ (Lp * (Ust * Mk)) * 1 :=
      mul_le_mul hPεX hϑva (norm_nonneg _) (by positivity)
    linarith
  refine (AltGridQ_norm_six_le _ _ _ _ _ _).trans ?_
  unfold qStepErrN
  linarith [t1, t2, t3, t4, t5, t6]

end QAlgebra

/-! ## 7. The deterministic envelope of the drift

With `η = η_u`, `B_F = η^{-k} + Bk`: `|𝓛-𝒦| ≤ B_F` on the loops of length `2..k` (`Bk` the `𝒦`
envelope), `|𝓛| ≤ η^{-(k+1)}` on the loops of length `k+1`, `|avgErr| ≤ η⁻¹ + 1`.  The drift
`Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}` is bounded by counting (`norm_primBil_le`
for the two cut couplings, one row of `S` for `𝓔^{(G̃)}`). -/

section DriftEnv

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem AltGridQ_eta_le_one {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) : etaT E u ≤ 1 := by
  have hsq : Real.sqrt (4 - E ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have him : (spectralM E).im ≤ 1 := by rw [spectralM_im]; linarith
  have hIm : 0 ≤ (spectralM E).im := (spectralM_im_pos hE).le
  calc etaT E u = (1 - u) * (spectralM E).im := rfl
    _ ≤ 1 * 1 := mul_le_mul (by linarith) him hIm (by norm_num)
    _ = 1 := one_mul 1

/-- `|𝓛_{u,J}| ≤ η^{-K'}` for a well-formed loop `J` of length `1 ≤ |J| ≤ K'`. -/
private theorem AltGridQ_norm_LLf_le {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hHb : (blockMat M).IsHermitian)
    {J : LoopIdx (Z2 L)} (hJ : J.WF) {K' : ℕ} (h1 : 1 ≤ J.length) (hK' : J.length ≤ K') :
    ‖LLf L W E u M J‖ ≤ (etaT E u)⁻¹ ^ K' := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (spectralM_im_pos hE))]
    exact le_rfl
  have h := norm_gloop_le_of_le_abs_im hHb hη hz J hJ h1
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  have hWi : ((W : ℝ)⁻¹ ^ 2) ^ (J.a.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1))
  have hone : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ hη).2 (AltGridQ_eta_le_one hE hu0)
  calc ‖LLf L W E u M J‖ = ‖gloop L W (blockMat M) (spectralZ E u) J‖ := rfl
    _ ≤ (etaT E u)⁻¹ ^ J.a.length * ((W : ℝ)⁻¹ ^ 2) ^ (J.a.length - 1) := h
    _ ≤ (etaT E u)⁻¹ ^ J.a.length * 1 := mul_le_mul_of_nonneg_left hWi (by positivity)
    _ = (etaT E u)⁻¹ ^ J.a.length := mul_one _
    _ ≤ (etaT E u)⁻¹ ^ K' := pow_le_pow_right₀ hone hK'

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = (𝓛-𝒦)_{u,(σ),(a)}`. -/
private theorem AltGridQ_avgErr_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool)
    (a : Z2 L) : avgErr L W E u M s a = LKf L W E u M ⟨[s], [a]⟩ := by
  unfold LKf LLf avgErr
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]

/-- `|avgErr| ≤ η⁻¹ + 1` (`|𝓛_{(σ),(a)}| ≤ η⁻¹`, `|m| = 1`). -/
private theorem AltGridQ_norm_avgErr_le {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hHb : (blockMat M).IsHermitian) (s : Bool) (a : Z2 L) :
    ‖avgErr L W E u M s a‖ ≤ (etaT E u)⁻¹ + 1 := by
  rw [AltGridQ_avgErr_eq]
  unfold LKf
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have h := AltGridQ_norm_LLf_le hE hu0 hu1 hHb (J := ⟨[s], [a]⟩) (K' := 1)
      (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    simpa using h
  · have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
      simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
    rw [h2, AltGridQ_norm_mSig hE.le]

/-- `∑_b ‖S_{ab}‖ = 1`. -/
private theorem AltGridQ_sum_norm_SB_row (hL : 3 ≤ L) (a : Z2 L) :
    ∑ b : Z2 L, ‖SB L a b‖ = 1 := by
  have h := sum_nnnorm_SB_row L hL a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simpa using h'

private theorem AltGridQ_norm_ite_le (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

/-- The graded cut coupling `[𝒦∼(𝓛-𝒦)]^l` is a sum of two `primBil`s with the `𝒦` restricted to
the loops of length `l`. -/
private theorem AltGridQ_ksimLK_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : ℕ)
    (I : LoopIdx (Z2 L)) :
    ksimLK L W E u M l I =
      primBil L W (LKf L W E u M)
          (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) I +
        primBil L W (fun J => if J.length = l then KLoop.Kcal L W E u J else 0)
          (LKf L W E u M) I := by
  unfold ksimLK primBil
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]

private theorem AltGridQ_norm_ksimLK_le (hL : 3 ≤ L) {E u : ℝ}
    (M : Matrix (Idx L W) (Idx L W) ℂ) {I : LoopIdx (Z2 L)} (hI : I.WF) (l : ℕ) {BF Bk : ℝ}
    (hBF0 : 0 ≤ BF) (hBk0 : 0 ≤ Bk)
    (hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖LKf L W E u M J‖ ≤ BF)
    (hK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖KLoop.Kcal L W E u J‖ ≤ Bk) :
    ‖ksimLK L W E u M l I‖ ≤ 2 * ((W : ℝ) ^ 2 * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk) := by
  rw [AltGridQ_ksimLK_eq]
  refine (norm_add_le _ _).trans ?_
  have hKl : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖(if J.length = l then KLoop.Kcal L W E u J else 0)‖ ≤ Bk :=
    fun J h1 h2 h3 => (AltGridQ_norm_ite_le _ _).trans (hK J h1 h2 h3)
  have h1 := norm_primBil_le L hL W (LKf L W E u M)
    (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) I hI hBF0 hBk0 hF hKl
  have h2 := norm_primBil_le L hL W
    (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) (LKf L W E u M) I hI hBk0 hBF0
    hKl hF
  linarith [h1, h2]

private theorem AltGridQ_norm_elklkN_le (hL : 3 ≤ L) {E u : ℝ}
    (M : Matrix (Idx L W) (Idx L W) ℂ) {I : LoopIdx (Z2 L)} (hI : I.WF) {BF : ℝ}
    (hBF0 : 0 ≤ BF)
    (hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖LKf L W E u M J‖ ≤ BF) :
    ‖elklkN L W E u M I‖ ≤ (W : ℝ) ^ 2 * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * BF :=
  norm_primBil_le L hL W (LKf L W E u M) (LKf L W E u M) I hI hBF0 hBF0 hF hF

/-- `‖𝓔^{(G̃)}‖ ≤ W² k L² (η⁻¹ + 1) η^{-(k+1)}` (one row of `S` per cut). -/
private theorem AltGridQ_norm_egtN_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hHb : (blockMat M).IsHermitian)
    {I : LoopIdx (Z2 L)} (hI : I.WF) {k : ℕ} (hk : I.length = k) :
    ‖egtN L W E u M I‖ ≤
      (W : ℝ) ^ 2 * ((k : ℝ) * ((L : ℝ) ^ 2 *
        (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))) := by
  unfold egtN
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  have hone : ∀ k' ∈ Finset.Icc 1 I.length,
      ‖∑ a : Z2 L, ∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k' - 1) false) a * SB L a b *
        LLf L W E u M (I.cutGlue k' b)‖ ≤
      (L : ℝ) ^ 2 * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
    intro k' hk'
    rw [Finset.mem_Icc] at hk'
    have hBG : ∀ b : Z2 L, ‖LLf L W E u M (I.cutGlue k' b)‖ ≤ (etaT E u)⁻¹ ^ (k + 1) := by
      intro b
      have hJ := LoopIdx.WF.cutGlue hI b hk'.1 hk'.2
      have hlen := LoopIdx.length_cutGlue I b hk'.2
      exact AltGridQ_norm_LLf_le hE hu0 hu1 hHb hJ (by omega) (by omega)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Z2 L, ‖∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k' - 1) false) a * SB L a b *
          LLf L W E u M (I.cutGlue k' b)‖
        ≤ ∑ _a : Z2 L, (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b : Z2 L, ‖avgErr L W E u M (I.σ.getD (k' - 1) false) a * SB L a b *
                LLf L W E u M (I.cutGlue k' b)‖
              ≤ ∑ b : Z2 L, (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) * ‖SB L a b‖ := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [norm_mul, norm_mul]
                have h1 := AltGridQ_norm_avgErr_le hE hu0 hu1 hHb (I.σ.getD (k' - 1) false) a
                have h2 := hBG b
                calc ‖avgErr L W E u M (I.σ.getD (k' - 1) false) a‖ * ‖SB L a b‖ *
                      ‖LLf L W E u M (I.cutGlue k' b)‖
                    ≤ ((etaT E u)⁻¹ + 1) * ‖SB L a b‖ * (etaT E u)⁻¹ ^ (k + 1) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
                        (norm_nonneg _) (by positivity)
                  _ = (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) * ‖SB L a b‖ := by ring
            _ = (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
                rw [← Finset.mul_sum, AltGridQ_sum_norm_SB_row hL a, mul_one]
      _ = (L : ℝ) ^ 2 * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
            nsmul_eq_mul]
          push_cast
          ring
  calc ∑ k' ∈ Finset.Icc 1 I.length,
        ‖∑ a : Z2 L, ∑ b : Z2 L, avgErr L W E u M (I.σ.getD (k' - 1) false) a * SB L a b *
          LLf L W E u M (I.cutGlue k' b)‖
      ≤ ∑ _k' ∈ Finset.Icc 1 I.length,
          (L : ℝ) ^ 2 * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) :=
        Finset.sum_le_sum hone
    _ = (k : ℝ) * ((L : ℝ) ^ 2 * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hk]
        simp

/-- **The drift envelope**: for every Hermitian `M`, every sign vector and label, with the `𝒦`
envelope `Bk` at the time `u`,
`|Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}| ≤ driftEnvN`. -/
private theorem AltGridQ_norm_drift_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ} (hHb : (blockMat M).IsHermitian)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KLoop.Kcal L W E u J‖ ≤ Bk) (a : Fin k → Z2 L) :
    ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a) +
        elklkN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a)‖ ≤
      driftEnvN L W E k u Bk := by
  have hI : (loopOf σ a).WF := AltGridQ_loopOf_wf σ a
  have hlen : (loopOf σ a).length = k := AltGridQ_loopOf_length σ a
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  set BF : ℝ := (etaT E u)⁻¹ ^ k + Bk with hBF
  have hBF0 : 0 ≤ BF := by positivity
  have hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ a).length →
      ‖LKf L W E u M J‖ ≤ BF := by
    intro J hJ h2 hJk
    rw [hlen] at hJk
    unfold LKf
    exact (norm_sub_le _ _).trans (add_le_add
      (AltGridQ_norm_LLf_le hE hu0 hu1 hHb hJ (by omega) hJk) (hBk J hJ h2 hJk))
  have hK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ a).length →
      ‖KLoop.Kcal L W E u J‖ ≤ Bk := fun J hJ h2 hJk => hBk J hJ h2 (hlen ▸ hJk)
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ ≤
      (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l ∈ Finset.Icc 3 k, ‖ksimLK L W E u M l (loopOf σ a)‖
        ≤ ∑ _l ∈ Finset.Icc 3 k, (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk)) :=
          Finset.sum_le_sum fun l _ => by
            have := AltGridQ_norm_ksimLK_le hL M hI l hBF0 hBk0 hF hK
            rwa [hlen] at this
      _ = ((Finset.Icc 3 k).card : ℝ) *
            (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : k + 1 - 3 ≤ k)
  have h2 : ‖elklkN L W E u M (loopOf σ a)‖ ≤
      (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * BF := by
    have := AltGridQ_norm_elklkN_le hL M hI hBF0 hF
    rwa [hlen] at this
  have h3 := AltGridQ_norm_egtN_le hL hE hu0 hu1 hHb hI hlen
  calc _ ≤ ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ +
        ‖elklkN L W E u M (loopOf σ a)‖ + ‖egtN L W E u M (loopOf σ a)‖ := norm_add₃_le
    _ ≤ (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk)) +
        (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * BF +
        (W : ℝ) ^ 2 * ((k : ℝ) * ((L : ℝ) ^ 2 *
          (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))) := by linarith [h1, h2, h3]
    _ = driftEnvN L W E k u Bk := by
        unfold driftEnvN
        rw [hBF]
        ring

end DriftEnv

/-! ## 8. The one-step identity of `int_K-L+Q2` on the grid -/

section GridDriftQ

/-- Every label of `A_{i}` is integrable (`𝓛` is bounded by `η^{-k}`, `𝒦` is deterministic). -/
private theorem AltGridQ_integrable_AvecN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ)
    (hE : |E n| < 2) (hi : gridTime s t K n i < 1) {k : ℕ} (σ : Fin k → Bool) (hk : 1 ≤ k)
    (b : Fin k → Z2 (d.L n)) :
    Integrable (fun ω : PathΩ d => AvecN d E s t K n i σ ω b) (pathP d) := by
  have h := AltGridQ_integrable_gloop d s t K n i hE hi (loopOf σ b) (AltGridQ_loopOf_wf σ b)
    (by rw [AltGridQ_loopOf_length]; exact hk)
  exact h.sub (integrable_const _)

/-- **`𝔼[·| F_j]` commutes with `𝒬_{u_{j+1}}`** (a.e., label by label): the `𝒬`-process satisfies
`𝔼[A^Q_{j+1}(a) | F_j] = (𝒬_{u_{j+1}} c)(a)`, `c_b = 𝔼[A_{j+1}(b) | F_j]`. -/
theorem AltGridQ_condExp_aTrueQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hj1 : gridTime s t K n (j + 1) < 1) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (a : Fin k → Z2 (d.L n)) :
    ∀ᵐ ω ∂(pathP d), (pathP d)[fun ω' => aTrueQN d E s t K n σ (j + 1) ω' a | filt d j] ω =
      Qop (d.L n) (gridTime s t K n (j + 1))
        (fun b => (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' b | filt d j] ω) a := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hInt := AltGridQ_integrable_AvecN d E s t K n (j + 1) hE hj1 σ hk1
  set F : Finset (Fin k → Z2 (d.L n)) :=
    Finset.univ.filter (fun b : Fin k → Z2 (d.L n) => b 0 = a 0) with hF
  have hfun : (fun ω' => aTrueQN d E s t K n σ (j + 1) ω' a) =
      (fun ω' => AvecN d E s t K n (j + 1) σ ω' a) -
        vartheta (d.L n) (gridTime s t K n (j + 1)) a •
          ∑ b ∈ F, (fun ω' => AvecN d E s t K n (j + 1) σ ω' b) := by
    funext ω'
    simp only [aTrueQN, Qop, Psum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    ring
  have hsumInt : Integrable (∑ b ∈ F, (fun ω' => AvecN d E s t K n (j + 1) σ ω' b))
      (pathP d) := integrable_finsetSum' F fun b _ => hInt b
  rw [hfun]
  filter_upwards [condExp_sub (hInt a)
      (hsumInt.smul (vartheta (d.L n) (gridTime s t K n (j + 1)) a)) (filt d j),
    condExp_smul (vartheta (d.L n) (gridTime s t K n (j + 1)) a)
      (∑ b ∈ F, (fun ω' => AvecN d E s t K n (j + 1) σ ω' b)) (filt d j),
    condExp_finsetSum (fun b _ => hInt b) (filt d j)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Finset.sum_apply, smul_eq_mul]
  simp only [Qop, Psum]
  ring

/-- **The one-step identity `gridDriftQN`**: the `𝒬`-analogue of `GridDriftN`,
with the same hypotheses (in particular the deterministic envelope `B_k` of
`𝒦` on `[0, u_{j+1}]`): a.e., for all labels,
`‖𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A^Q_j - Δ dGridQN_j‖ ≤ qErrQN_j`.
Proof: `gridDriftN` gives `c = 𝒰 X + Δ D + e`, `‖e‖ ≤ stepErrN`; conditional expectation
commutes with `𝒬_{u_{j+1}}`; the deterministic identity `AltGridQ_qstep_algebra` finishes. -/
theorem gridDriftQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) :
    (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n j : ℕ), j < K n → ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
      (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Z2 (d.L n)), J.WF →
        2 ≤ J.length → J.length ≤ k → ‖KLoop.Kcal (d.L n) (d.W n) (E n) w J‖ ≤ Bk) →
      ∀ᵐ ω ∂(pathP d), ∀ a : Fin k → Z2 (d.L n),
        ‖(pathP d)[fun ω' => aTrueQN d E s t K n σ (j + 1) ω' a | filt d j] ω -
            Ugen (d.L n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
              (aTrueQN d E s t K n σ j ω) a -
            (gridStep s t K n : ℂ) * dGridQN d E s t K n σ j ω a‖ ≤
          qErrQN d E s t K n k Bk j := by
  intro hE hs0 hst ht1 hK n j hj k _ hk σ Bk hBk hB
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := AltGridQ_time_facts s t K n j (hs0 n) (hst n) (ht1 n)
    (hK n) hj
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hkpos : 1 ≤ k := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hT := gridDriftN d E s t K hE hs0 hst ht1 hK n j hj k hk σ Bk hBk hB
  have hlin' := ae_all_iff.2 fun a =>
    AltGridQ_condExp_aTrueQN d E s t K n j (hE n) hv1 σ a
  have hη : 0 < RBM.Path.etaT (E n) (gridTime s t K n j) := RBM.Path.etaT_pos (hE n) hu1
  have hz : RBM.Path.etaT (E n) (gridTime s t K n j) ≤
      |(spectralZ (E n) (gridTime s t K n j)).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (spectralM_im_pos (hE n)))]
    exact le_rfl
  filter_upwards [hT, hlin'] with ω hTω hlinω a
  have hHb : (blockMat (pathH d s t K n j ω)).IsHermitian :=
    (pathH_isHermitian d s t K n j ω).submatrix _
  have hBk' : ∀ J : LoopIdx (Z2 (d.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j) J‖ ≤ Bk := fun J hJ h2 hJk =>
    hB _ ⟨hu0, by rw [hvu]; linarith⟩ J hJ h2 hJk
  -- the sup bound on `A_j`
  have hX : ∀ b : Fin k → Z2 (d.L n), ‖AvecN d E s t K n j σ ω b‖ ≤
      lkEnvN (d.W n) (E n) k (gridTime s t K n j) Bk := by
    intro b
    have hlen : (loopOf σ b).a.length = k := by simp [loopOf]
    have h1 := norm_gloop_le_of_le_abs_im hHb hη hz (loopOf σ b) (AltGridQ_loopOf_wf σ b)
      (by rw [hlen]; exact hkpos)
    rw [hlen] at h1
    have h2 := hBk' (loopOf σ b) (AltGridQ_loopOf_wf σ b)
      (by rw [AltGridQ_loopOf_length]; exact hk) (by rw [AltGridQ_loopOf_length])
    calc ‖AvecN d E s t K n j σ ω b‖ ≤
          ‖gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
            (spectralZ (E n) (gridTime s t K n j)) (loopOf σ b)‖ +
          ‖KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  -- the sup bound on the drift
  have hD : ∀ b : Fin k → Z2 (d.L n),
      ‖∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
            (pathH d s t K n j ω) l (loopOf σ b) +
          elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
            (loopOf σ b) +
          egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
            (loopOf σ b)‖ ≤
        driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j) Bk := fun b =>
    AltGridQ_norm_drift_le hL3 (hE n) hu0 hu1 hHb σ hBk hBk' b
  -- the one-step bound in the shape of the algebra lemma
  have hc : ∀ b : Fin k → Z2 (d.L n),
      ‖(pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' b | filt d j] ω -
          Ugen (d.L n) (E n) σ (gridTime s t K n j)
            (gridTime s t K n j + gridStep s t K n) (AvecN d E s t K n j σ ω) b -
          (gridStep s t K n : ℂ) *
            (∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
                (pathH d s t K n j ω) l (loopOf σ b) +
              elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
                (loopOf σ b) +
              egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω)
                (loopOf σ b))‖ ≤
        stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n) Bk := by
    intro b
    rw [← hvu]
    exact hTω b
  have hmain := AltGridQ_qstep_algebra hL3 hk (hE n).le σ hu0 hΔ0 (by rw [← hvu]; exact hv1) hX hD
    hc a
  rw [← hvu] at hmain
  rw [hlinω a]
  exact hmain

end GridDriftQ

/-! ## 9. The stopped Duhamel expansion of the stopped `𝒬`-process -/

section StoppedDuhamelQ

/-- **The stopped Duhamel expansion `stoppedDuhamelQN`**: the `𝒬`-analogue of `StoppedDuhamelN`
for the stopped process `aFrozQN`, pathwise, for every stopping index
`τ : PathΩ d → ℕ` and every grid index `m ≤ K n`:
`A^{Q,frz}_m = 𝒰_{u_0,u_m} A^Q_0 + Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m}(Δ dGridQN_j + ξ^Q_{j+1} + R^Q_j)`.
The remainder `R^Q_j = rGridQN` is named by subtraction; `gridDriftQN` bounds it a.e. by `qErrQN`. -/
theorem stoppedDuhamelQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) :
    (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) [NeZero k] (σ : Fin k → Bool) (τ : PathΩ d → ℕ) (m : ℕ) (ω : PathΩ d),
      m ≤ K n →
      aFrozQN d E s t K n σ τ m ω =
        Ugen (d.L n) (E n) σ (gridTime s t K n 0) (gridTime s t K n m)
            (aTrueQN d E s t K n σ 0 ω) +
          ∑ j ∈ Finset.range (min m (τ ω)),
            Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              ((gridStep s t K n : ℂ) • dGridQN d E s t K n σ j ω +
                martIncQN d E s t K n σ j ω + rGridQN d E s t K n σ j ω) := by
  intro hE hs0 hst ht1 hK n k _ σ τ m ω hm
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hmin : min m (τ ω) ≤ K n := (min_le_left _ _).trans hm
  have hΔ0 := GoodEvent_gridStep_nonneg (K := K) (hst n)
  have hu0 : ∀ i, 0 ≤ gridTime s t K n i := fun i =>
    add_nonneg (hs0 n) (mul_nonneg (Nat.cast_nonneg _) hΔ0)
  have hu1 : ∀ i ≤ K n, gridTime s t K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) (hst n) hi).trans_lt (ht1 n)
  have htele := GridDuhamelN_Ugen_duhamel_telescope (d.L n) hL3 (hE n).le σ (gridTime s t K n)
    (min m (τ ω)) (fun i _ => hu0 i) (fun i hi => hu1 i (hi.trans hmin))
    (fun i => aTrueQN d E s t K n σ i ω)
  have hinc : ∀ i, aTrueQN d E s t K n σ (i + 1) ω -
      Ugen (d.L n) (E n) σ (gridTime s t K n i) (gridTime s t K n (i + 1))
        (aTrueQN d E s t K n σ i ω) =
      (gridStep s t K n : ℂ) • dGridQN d E s t K n σ i ω +
        martIncQN d E s t K n σ i ω + rGridQN d E s t K n σ i ω := by
    intro i
    funext a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, martIncQN, rGridQN]
    ring
  simp only [hinc] at htele
  unfold aFrozQN
  refine (congrArg (Ugen (d.L n) (E n) σ (gridTime s t K n (min m (τ ω))) (gridTime s t K n m))
    htele).trans ?_
  rw [GridDuhamelN_Ugen_add]
  have hcomp : ∀ (i : ℕ) (A : (Fin k → Z2 (d.L n)) → ℂ),
      Ugen (d.L n) (E n) σ (gridTime s t K n (min m (τ ω))) (gridTime s t K n m)
        (Ugen (d.L n) (E n) σ (gridTime s t K n i) (gridTime s t K n (min m (τ ω))) A) =
      Ugen (d.L n) (E n) σ (gridTime s t K n i) (gridTime s t K n m) A := fun i A =>
    GridDuhamelN_Ugen_comp (d.L n) hL3 (hE n).le σ (hu0 _) (hu1 _ hmin) (hu0 _) (hu1 _ hm) A
  have hsum := map_sum
    (GridDuhamelN_UgenHom (d.L n) (E n) σ (gridTime s t K n (min m (τ ω))) (gridTime s t K n m))
    (fun j => Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1))
      (gridTime s t K n (min m (τ ω)))
      ((gridStep s t K n : ℂ) • dGridQN d E s t K n σ j ω +
        martIncQN d E s t K n σ j ω + rGridQN d E s t K n σ j ω))
    (Finset.range (min m (τ ω)))
  refine congrArg₂ (· + ·) (hcomp 0 _) ?_
  refine hsum.trans (Finset.sum_congr rfl fun j _ => hcomp (j + 1) _)

end StoppedDuhamelQ

/-! ## 10. The envelope of the remainder summed over the grid

`Σ_{j<m} (1 + (1-u_m)⁻¹)^k qErrQN_j`: the term `(1 + Lp) stepErrN` of `qStepErrN` is handled by
`sum_weighted_stepErrN_le` (at the decay exponent `D_t + k`, since `Lp = (L²)^{k-1} ≤ N^{k-1}`); the
remaining terms are `O(Δ²)` with the polynomial coefficient `N^k Q² H²`, `Q = N^{τ_K}(H/c)^k`,
`H = N^{1-τ'}`, absorbed by `K Δ² ≤ N^{-C_K}`.  The four conditions on `C_K` are those of
`SumWeightedStepErrN_Stmt` with `D_t + k` in place of `D_t`; the extra terms need only
`k + 2τ_K + (3k+2)(1-τ') + D_t < C_K`, which the second condition implies. -/

section GridSum

/-- `(1 + x)^k - 1 - k x ≤ k 2^k x²` for `0 ≤ x ≤ 1`. -/
private theorem AltGridQ_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : ℝ) * x ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (1 + x) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * x =
        (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2 := by
      push_cast; ring
    rw [e]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
    have h1 : (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) ≤
        (1 + x) * ((k : ℝ) * 2 ^ k * x ^ 2) := mul_le_mul_of_nonneg_left ih (by linarith)
    have hb : 0 ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_right hx1 hb
    have h3 := mul_le_mul_of_nonneg_right hk2 hx2
    have h4 := mul_nonneg hpk hx2
    push_cast
    rw [pow_succ (2 : ℝ) k]
    nlinarith [h1, h2, h3, h4]

private theorem AltGridQ_uStepC_nonneg (k : ℕ) {Δ v : ℝ} (hΔ0 : 0 ≤ Δ) (hv1 : 0 < 1 - v) :
    0 ≤ uStepC k Δ v := by
  unfold uStepC
  have hβ0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 hv1.le
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 hβ0
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - v)⁻¹ by linarith) k
  have e1 : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
  linarith [hb, e1]

/-- `uStepC k Δ v ≤ (k + k 2^k) H² Δ²` for `(1-v)⁻¹ ≤ H`, `Δ H ≤ 1` (the bound `hU` inside the
private `GridEnvelopeN_stepErr_le`). -/
private theorem AltGridQ_uStepC_le (k : ℕ) {Δ v H : ℝ} (hΔ0 : 0 ≤ Δ) (hv1 : 0 < 1 - v)
    (hv : (1 - v)⁻¹ ≤ H) (hΔH : Δ * H ≤ 1) :
    uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := AltGridQ_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  unfold uStepC
  have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_left hiv2 (by positivity)
  have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left hx2 (by positivity)
  linarith [hrem, e1, e2]

/-- The `(1 + Lp) S` part of `qStepErrN` and its `Δ²` part. -/
private theorem AltGridQ_qStepErrN_split (L k : ℕ) (u Δ Mk Dm S : ℝ) :
    qStepErrN L k u Δ Mk Dm S =
      (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * S + qStepErrN L k u Δ Mk Dm 0 := by
  unfold qStepErrN
  ring

/-- The coefficient of the `Δ²`-part: `20k⁴ + 4(k + k 2^k) + 8k²`. -/
private def AltGridQ_aQ (k : ℕ) : ℝ :=
  20 * (k : ℝ) ^ 4 + 4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) + 8 * (k : ℝ) ^ 2

private theorem AltGridQ_aQ_nonneg (k : ℕ) : 0 ≤ AltGridQ_aQ k := by
  unfold AltGridQ_aQ; positivity

/-- **The `Δ²`-part of `qStepErrN`, for `S = 0`** (per step): with `N = W²L²`, `H ≥ (1-v)⁻¹`,
`H/c ≥ η_u⁻¹, η_v⁻¹`, `Y ≥ 1`, `Δ H ≤ 1`, the envelope `Bk = Y η_v^{-k}`:
`qStepErrN … 0 ≤ Δ² a_Q N^k (Y (H/c)^k)² H²`. -/
private theorem AltGridQ_extra_le (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (u Δ N H Y c : ℝ) (hu0 : 0 ≤ u) (hN1 : 1 ≤ N)
    (hWL : (W : ℝ) ^ 2 * (L : ℝ) ^ 2 = N) (hW : (1 : ℝ) ≤ W) (hL1 : (1 : ℝ) ≤ L)
    (hH : 1 ≤ H) (hY : 1 ≤ Y) (hc0 : 0 < c) (hc1 : c ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E (u + Δ)) (hηu : (etaT E u)⁻¹ ≤ H / c)
    (hηv : (etaT E (u + Δ))⁻¹ ≤ H / c) (hv1 : 0 < 1 - (u + Δ)) (hv : (1 - (u + Δ))⁻¹ ≤ H) :
    qStepErrN L k u Δ (lkEnvN W E k u (Y * (etaT E (u + Δ))⁻¹ ^ k))
        (driftEnvN L W E k u (Y * (etaT E (u + Δ))⁻¹ ^ k)) 0 ≤
      Δ ^ 2 * (AltGridQ_aQ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2) := by
  set Bk : ℝ := Y * (etaT E (u + Δ))⁻¹ ^ k with hBk
  set P : ℝ := (H / c) ^ k with hP
  set Q : ℝ := Y * P with hQ
  have hHc : 1 ≤ H / c := by rw [le_div_iff₀ hc0]; linarith
  have hP1 : 1 ≤ P := one_le_pow₀ hHc
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hY hP1
  have hPQ : P ≤ Q := le_mul_of_one_le_left (by linarith) hY
  have hη' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηv' : 0 ≤ (etaT E (u + Δ))⁻¹ := inv_nonneg.2 hηv0.le
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hBkQ : Bk ≤ Q :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηv' hηv k) (by linarith)
  have hηuP : (etaT E u)⁻¹ ^ k ≤ P := pow_le_pow_left₀ hη' hηu k
  have hWi : ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  -- the sup bounds
  have hMk0 : 0 ≤ lkEnvN W E k u Bk := by unfold lkEnvN; positivity
  have hMk : lkEnvN W E k u Bk ≤ 2 * Q := by
    unfold lkEnvN
    have h1 : (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) ≤ P :=
      (mul_le_of_le_one_right (by positivity) hWi).trans hηuP
    linarith
  have hBF : (etaT E u)⁻¹ ^ k + Bk ≤ 2 * Q := by linarith
  have hBF0 : 0 ≤ (etaT E u)⁻¹ ^ k + Bk := by positivity
  have hDm : driftEnvN L W E k u Bk ≤ 10 * (k : ℝ) ^ 3 * N * Q ^ 2 := by
    unfold driftEnvN
    rw [hWL]
    have hη2 : (etaT E u)⁻¹ + 1 ≤ 2 * (H / c) := by linarith
    have h3 : (etaT E u)⁻¹ ^ (k + 1) ≤ (H / c) ^ (k + 1) := pow_le_pow_left₀ hη' hηu _
    have h4 : ((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1) ≤ 2 * (H / c) * (H / c) ^ (k + 1) :=
      mul_le_mul hη2 h3 (by positivity) (by positivity)
    have h5 : (H / c) ^ (k + 2) ≤ P ^ 2 := by
      rw [hP, ← pow_mul']
      exact pow_le_pow_right₀ hHc (by omega)
    have h6 : 2 * (H / c) * (H / c) ^ (k + 1) ≤ 2 * Q ^ 2 := by
      have : 2 * (H / c) * (H / c) ^ (k + 1) = 2 * (H / c) ^ (k + 2) := by ring
      rw [this]
      have hP2 : P ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by linarith) hPQ 2
      linarith
    have t1 : (k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) ≤
        4 * (k : ℝ) ^ 3 * Q ^ 2 := by
      have : ((etaT E u)⁻¹ ^ k + Bk) * Bk ≤ (2 * Q) * Q :=
        mul_le_mul hBF hBkQ hBk0 (by linarith)
      calc (k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk))
          ≤ (k : ℝ) * (2 * (k : ℝ) ^ 2 * ((2 * Q) * Q)) := by gcongr
        _ = 4 * (k : ℝ) ^ 3 * Q ^ 2 := by ring
    have t2 : (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) ≤
        4 * (k : ℝ) ^ 2 * Q ^ 2 := by
      have : ((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk) ≤ (2 * Q) * (2 * Q) :=
        mul_le_mul hBF hBF hBF0 (by linarith)
      calc (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk))
          ≤ (k : ℝ) ^ 2 * ((2 * Q) * (2 * Q)) := by gcongr
        _ = 4 * (k : ℝ) ^ 2 * Q ^ 2 := by ring
    have t3 : (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) ≤ 2 * (k : ℝ) * Q ^ 2 := by
      calc (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1))
          ≤ (k : ℝ) * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (h4.trans h6) hk0
        _ = 2 * (k : ℝ) * Q ^ 2 := by ring
    have hk1R : (1 : ℝ) ≤ k := by linarith
    have hk2 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1R (by norm_num)
    have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1R (by norm_num)
    have hQ2 : 0 ≤ Q ^ 2 := by positivity
    calc N * ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) +
          (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) +
          (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))
        ≤ N * (4 * (k : ℝ) ^ 3 * Q ^ 2 + 4 * (k : ℝ) ^ 2 * Q ^ 2 + 2 * (k : ℝ) * Q ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [t1, t2, t3]) hN0
      _ ≤ N * (10 * (k : ℝ) ^ 3 * Q ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hN0
          have e2 := mul_le_mul_of_nonneg_right hk2 hQ2
          have e1 := mul_le_mul_of_nonneg_right hk1 hQ2
          linarith [e1, e2]
      _ = 10 * (k : ℝ) ^ 3 * N * Q ^ 2 := by ring
  -- the pieces of `qStepErrN`
  have hLp1 : 1 ≤ ((L : ℝ) ^ 2) ^ (k - 1) := one_le_pow₀ (one_le_pow₀ hL1)
  have hL2N : (L : ℝ) ^ 2 ≤ N := by
    calc (L : ℝ) ^ 2 = 1 * (L : ℝ) ^ 2 := (one_mul _).symm
      _ ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hW) (by positivity)
      _ = N := hWL
  have hLpN : ((L : ℝ) ^ 2) ^ (k - 1) ≤ N ^ (k - 1) := pow_le_pow_left₀ (by positivity) hL2N _
  set M1 : ℝ := N ^ (k - 1) with hM1
  have hM1N : M1 * N = N ^ k := by
    rw [hM1, ← pow_succ]; congr 1; omega
  have hM10 : 0 ≤ M1 := by positivity
  have hM1le : M1 ≤ N ^ k := by
    rw [hM1]; exact pow_le_pow_right₀ hN1 (by omega)
  have hβ0 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.2 hv1.le
  have hUst := AltGridQ_uStepC_le k hΔ0 hv1 hv hΔH
  have hUst0 : 0 ≤ uStepC k Δ (u + Δ) := AltGridQ_uStepC_nonneg k hΔ0 hv1
  have hVd : 2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ ≤ 2 * k * H * Δ := by
    have h1 : ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ ≤ k * H :=
      mul_le_mul (by linarith) hv hβ0 hk0
    calc 2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ
        = 2 * (((k : ℝ) - 1) * (1 - (u + Δ))⁻¹) * Δ := by ring
      _ ≤ 2 * ((k : ℝ) * H) * Δ := by gcongr
      _ = 2 * k * H * Δ := by ring
  have hVd0 : 0 ≤ 2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ := by
    have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    positivity
  have hτB : 2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2 ≤
      2 * (k : ℝ) ^ 2 * H ^ 2 * Δ ^ 2 := by
    have h1 : ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 ≤ (k : ℝ) ^ 2 * H ^ 2 := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (by linarith) hβ0) (mul_le_mul (by linarith) hv hβ0 hk0) 2
    calc 2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2
        = 2 * (((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2) * Δ ^ 2 := by ring
      _ ≤ 2 * ((k : ℝ) ^ 2 * H ^ 2) * Δ ^ 2 := by gcongr
      _ = 2 * (k : ℝ) ^ 2 * H ^ 2 * Δ ^ 2 := by ring
  have hτB0 : 0 ≤ 2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2 := by positivity
  -- the four terms
  set Lp : ℝ := ((L : ℝ) ^ 2) ^ (k - 1) with hLp
  have hLp0 : 0 ≤ Lp := by linarith
  have Ta : Δ * (Lp * driftEnvN L W E k u Bk) * (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) ≤
      20 * (k : ℝ) ^ 4 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H)) := by
    calc Δ * (Lp * driftEnvN L W E k u Bk) * (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ)
        ≤ Δ * (M1 * (10 * (k : ℝ) ^ 3 * N * Q ^ 2)) * (2 * k * H * Δ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hLpN hDm
            (by
              have : 0 ≤ driftEnvN L W E k u Bk := by
                unfold driftEnvN; positivity
              exact this) hM10) hΔ0) hVd hVd0 (by positivity)
      _ = 20 * (k : ℝ) ^ 4 * (Δ ^ 2 * ((M1 * N) * Q ^ 2 * H)) := by ring
      _ = 20 * (k : ℝ) ^ 4 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H)) := by rw [hM1N]
  have Tb : 2 * (Lp * (uStepC k Δ (u + Δ) * lkEnvN W E k u Bk)) ≤
      4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    calc 2 * (Lp * (uStepC k Δ (u + Δ) * lkEnvN W E k u Bk))
        ≤ 2 * (M1 * ((((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2) * (2 * Q))) := by
          gcongr
      _ = 4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  have Tc : Lp * lkEnvN W E k u Bk * (2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) ≤
      4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    calc Lp * lkEnvN W E k u Bk *
          (2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2)
        ≤ M1 * (2 * Q) * (2 * (k : ℝ) ^ 2 * H ^ 2 * Δ ^ 2) :=
          mul_le_mul (mul_le_mul hLpN hMk hMk0 hM10) hτB hτB0 (by positivity)
      _ = 4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  have Td : Δ * (Lp * ((k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN W E k u Bk)) *
      (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) ≤
      4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by
    have hkβ : (k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN W E k u Bk ≤ (k : ℝ) * H * (2 * Q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv hk0) hMk hMk0 (by positivity)
    have hkβ0 : 0 ≤ (k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN W E k u Bk := by positivity
    calc Δ * (Lp * ((k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN W E k u Bk)) *
          (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ)
        ≤ Δ * (M1 * ((k : ℝ) * H * (2 * Q))) * (2 * k * H * Δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hLpN hkβ hkβ0 hM10) hΔ0) hVd hVd0
            (by positivity)
      _ = 4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (M1 * Q * H ^ 2)) := by ring
  -- assemble
  have hH2 : H ≤ H ^ 2 := le_self_pow₀ hH (by norm_num)
  have hMQ : M1 * Q ≤ N ^ k * Q ^ 2 :=
    mul_le_mul hM1le (le_self_pow₀ hQ1 (by norm_num)) (by linarith) (by positivity)
  have hNQH : N ^ k * Q ^ 2 * H ≤ N ^ k * Q ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_left hH2 (by positivity)
  have hMQH : M1 * Q * H ^ 2 ≤ N ^ k * Q ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_right hMQ (by positivity)
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have Ta' : Δ * (Lp * driftEnvN L W E k u Bk) * (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) ≤
      20 * (k : ℝ) ^ 4 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) :=
    Ta.trans (by gcongr)
  have Tb' : 4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (M1 * Q * H ^ 2)) ≤
      4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have Tc' : 4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (M1 * Q * H ^ 2)) ≤
      4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by gcongr
  have hgoal : qStepErrN L k u Δ (lkEnvN W E k u Bk) (driftEnvN L W E k u Bk) 0 =
      Δ * (Lp * driftEnvN L W E k u Bk) * (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) +
        2 * (Lp * (uStepC k Δ (u + Δ) * lkEnvN W E k u Bk)) +
        Lp * lkEnvN W E k u Bk *
          (2 * ((k : ℝ) - 1) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) +
        Δ * (Lp * ((k : ℝ) * (1 - (u + Δ))⁻¹ * lkEnvN W E k u Bk)) *
          (2 * ((k : ℝ) - 1) * (1 - (u + Δ))⁻¹ * Δ) := by
    unfold qStepErrN
    ring
  rw [hgoal]
  have hfin : Δ ^ 2 * (AltGridQ_aQ k * N ^ k * Q ^ 2 * H ^ 2) =
      20 * (k : ℝ) ^ 4 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by
    unfold AltGridQ_aQ; ring
  rw [hQ] at hfin
  calc _ ≤ 20 * (k : ℝ) ^ 4 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) +
        4 * (k : ℝ) ^ 2 * (Δ ^ 2 * (N ^ k * Q ^ 2 * H ^ 2)) := by
        linarith [Ta', Tb, Tb', Tc, Tc', Td]
    _ = Δ ^ 2 * (AltGridQ_aQ k * N ^ k * Q ^ 2 * H ^ 2) := by
        rw [hQ]; unfold AltGridQ_aQ; ring

/-- `N^a (N^θ)^p (N^τ)^q N^b = N^{a + θ p + τ q + b}`. -/
private theorem AltGridQ_mono (N : ℝ) (hN : 0 < N) (a : ℕ) (θ : ℝ) (p : ℕ) (τ : ℝ) (q : ℕ)
    (b : ℝ) :
    N ^ a * (N ^ θ) ^ p * (N ^ τ) ^ q * N ^ b = N ^ ((a : ℝ) + θ * p + τ * q + b) := by
  rw [← Real.rpow_natCast N a, ← Real.rpow_natCast (N ^ θ) p, ← Real.rpow_natCast (N ^ τ) q,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN,
    ← Real.rpow_add hN]

/-- `A N^e ≤ N^f` eventually, for `e < f`. -/
private theorem AltGridQ_eventually_le (d : Sizes) (hsize : SizeTendsto d) (A e f : ℝ)
    (hef : e < f) :
    ∀ᶠ n : ℕ in atTop, A * ((d.size n : ℕ) : ℝ) ^ e ≤ ((d.size n : ℕ) : ℝ) ^ f := by
  have hT : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ) ^ (f - e)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hef)).comp hsize
  filter_upwards [hT.eventually_ge_atTop A, hsize.eventually_ge_atTop 1] with n hA hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  calc A * ((d.size n : ℕ) : ℝ) ^ e ≤ ((d.size n : ℕ) : ℝ) ^ (f - e) * ((d.size n : ℕ) : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hN0.le _)
    _ = ((d.size n : ℕ) : ℝ) ^ f := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A uniform lower bound `0 < c ≤ 1`, `c ≤ Im m(E n)` in the bulk. -/
private theorem AltGridQ_exists_c {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c ≤ (spectralM (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨min (Real.sqrt (2 * κ) / 2) 1, lt_min (by
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith) one_pos, min_le_right _ _,
    fun n => ?_⟩
  rw [spectralM_im]
  refine (min_le_left _ _).trans ?_
  have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.1 (hE n)
    nlinarith
  have h2 : 2 * κ ≤ 4 - E n ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

/-- **The `Δ²`-part summed over the grid**, at a fixed size index (per-step bound
`AltGridQ_extra_le`, `m Δ² ≤ K Δ² ≤ N^{-C_K}`, weight `≤ (2H)^k`), as one `N`-monomial:
`≤ 2^k a_Q c^{-2k} N^k H^{3k+2} Y² N^{-C_K}`, `H = N^{1-τ'}`, `Y = N^{τ_K}`, `c ≤ Im m(E n)`. -/
private theorem AltGridQ_extra_sum_le (d : Sizes) {τ' τK C_K : ℝ} {E s t : ℕ → ℝ}
    {K : ℕ → ℕ} (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcE : c ≤ (spectralM (E n)).im) (hτK : 0 < τK) (hτ'1 : τ' ≤ 1) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + τ') ≤ 1 - t n)
    (hKn : ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (h4 : 1 - τ' ≤ C_K) (m : ℕ) (hm : m ≤ K n) :
    ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        qStepErrN (d.L n) k (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 ≤
      2 ^ k * AltGridQ_aQ k * (c⁻¹) ^ (2 * k) *
        (((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ (1 - τ')) ^ (3 * k + 2) *
          (((d.size n : ℕ) : ℝ) ^ τK) ^ 2 * ((d.size n : ℕ) : ℝ) ^ (-C_K)) := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  set θ : ℝ := 1 - τ' with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set H : ℝ := N ^ θ with hHdef
  set Y : ℝ := N ^ τK with hYdef
  have hH1 : 1 ≤ H := Real.one_le_rpow hN1 hθ0
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 hτK.le
  have hH0 : 0 < H := by linarith
  have hHinv : H⁻¹ ≤ 1 - t n := by
    rw [hHdef, ← Real.rpow_neg hN0.le]
    have e : -θ = -1 + τ' := by rw [hθ]; ring
    rw [e]; exact hR
  have hinv : ∀ x, x ≤ t n → 0 < 1 - x ∧ (1 - x)⁻¹ ≤ H := fun x hx => by
    have h1 : H⁻¹ ≤ 1 - x := hHinv.trans (by linarith)
    have h1x : 0 < 1 - x := lt_of_lt_of_le (inv_pos.2 hH0) h1
    exact ⟨h1x, (inv_le_comm₀ h1x hH0).2 h1⟩
  have hη : ∀ x, x ≤ t n → 0 < etaT (E n) x ∧ (etaT (E n) x)⁻¹ ≤ H / c := fun x hx => by
    obtain ⟨h1x, hxH⟩ := hinv x hx
    have hpos : 0 < etaT (E n) x := etaT_pos hE (by linarith [ht1])
    refine ⟨hpos, ?_⟩
    have hle : (1 - x) * c ≤ etaT (E n) x := by
      unfold etaT; exact mul_le_mul_of_nonneg_left hcE h1x.le
    calc (etaT (E n) x)⁻¹ ≤ ((1 - x) * c)⁻¹ := inv_anti₀ (mul_pos h1x hc0) hle
      _ = (1 - x)⁻¹ * c⁻¹ := mul_inv _ _
      _ ≤ H * c⁻¹ := mul_le_mul_of_nonneg_right hxH (inv_nonneg.2 hc0.le)
      _ = H / c := (div_eq_mul_inv H c).symm
  -- the grid
  set Δ : ℝ := gridStep s t K n with hΔdef
  have hKpos : (0 : ℝ) < (K n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK0)
  have hΔ0 : 0 ≤ Δ := GoodEvent_gridStep_nonneg (K := K) hst
  have hKΔ : (K n : ℝ) * Δ = t n - s n := by
    rw [hΔdef]; unfold gridStep; field_simp
  have hKΔ1 : (K n : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hNC : 0 < N ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hΔD : Δ ≤ N ^ (-C_K) := by
    have h1 : Δ ≤ 1 / (K n : ℝ) := by
      rw [hΔdef]; unfold gridStep
      exact div_le_div_of_nonneg_right (by linarith) hKpos.le
    calc Δ ≤ 1 / (K n : ℝ) := h1
      _ ≤ 1 / N ^ C_K := one_div_le_one_div_of_le hNC hKn
      _ = N ^ (-C_K) := by rw [Real.rpow_neg hN0.le, one_div]
  have hΔH : Δ * H ≤ 1 := by
    calc Δ * H ≤ N ^ (-C_K) * N ^ θ := mul_le_mul hΔD le_rfl hH0.le (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-C_K + θ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N := by
    rw [hNdef]; exact_mod_cast (Sizes.size_eq d n).symm
  have hW : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
  have hL1 : (1 : ℝ) ≤ d.L n := by
    have := d.three_le_L n
    exact_mod_cast (by omega : 1 ≤ d.L n)
  -- the per-step bound
  have hstep : ∀ j < K n,
      qStepErrN (d.L n) k (gridTime s t K n j) Δ
        (lkEnvN (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
        (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 ≤
      Δ ^ 2 * (AltGridQ_aQ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2) := by
    intro j hj
    obtain ⟨_, hu0, hvu, _, _⟩ := AltGridQ_time_facts s t K n j hs0 hst ht1 hK0 hj
    have hu : gridTime s t K n j ≤ t n := GoodEvent_gridTime_le (K := K) hst hj.le
    have hv : gridTime s t K n (j + 1) ≤ t n := GoodEvent_gridTime_le (K := K) hst hj
    obtain ⟨hv1, hvH⟩ := hinv _ hv
    obtain ⟨hηu0, hηu⟩ := hη _ hu
    obtain ⟨hηv0, hηv⟩ := hη _ hv
    rw [hvu] at hv1 hvH hηv0 hηv ⊢
    exact AltGridQ_extra_le (d.L n) (d.W n) (E n) k hk (gridTime s t K n j) Δ N H Y c hu0 hN1 hWL
      hW hL1 hH1 hY1 hc0 hc1 hΔ0 hΔH hηu0 hηv0 hηu hηv hv1 hvH
  -- the weight
  have hum : gridTime s t K n m ≤ t n := GoodEvent_gridTime_le (K := K) hst hm
  obtain ⟨hum1, hwH⟩ := hinv _ hum
  have hinv0 : 0 ≤ (1 - gridTime s t K n m)⁻¹ := inv_nonneg.2 hum1.le
  have hw0 : 0 ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k := by positivity
  have hw : (1 + (1 - gridTime s t K n m)⁻¹) ^ k ≤ (2 * H) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  set Z : ℝ := AltGridQ_aQ k * N ^ k * (Y * (H / c) ^ k) ^ 2 * H ^ 2 with hZ
  have hZ0 : 0 ≤ Z := by
    have := AltGridQ_aQ_nonneg k
    rw [hZ]; positivity
  have hmK : (m : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hm
  have hfull : (K n : ℝ) * Δ ^ 2 ≤ N ^ (-C_K) := by
    calc (K n : ℝ) * Δ ^ 2 = ((K n : ℝ) * Δ) * Δ := by ring
      _ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hKΔ1 hΔ0
      _ ≤ N ^ (-C_K) := by rw [one_mul]; exact hΔD
  have h2H : 0 ≤ (2 * H) ^ k := by positivity
  calc ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        qStepErrN (d.L n) k (gridTime s t K n j) Δ
          (lkEnvN (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0
      ≤ ∑ _j ∈ Finset.range m, (2 * H) ^ k * (Δ ^ 2 * Z) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have h1 := hstep j (lt_of_lt_of_le (Finset.mem_range.1 hj) hm)
        calc (1 + (1 - gridTime s t K n m)⁻¹) ^ k * qStepErrN (d.L n) k (gridTime s t K n j) Δ
              (lkEnvN (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
                (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
              (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (N ^ τK *
                (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0
            ≤ (1 + (1 - gridTime s t K n m)⁻¹) ^ k * (Δ ^ 2 * Z) :=
              mul_le_mul_of_nonneg_left h1 hw0
          _ ≤ (2 * H) ^ k * (Δ ^ 2 * Z) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (m : ℝ) * ((2 * H) ^ k * (Δ ^ 2 * Z)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (K n : ℝ) * ((2 * H) ^ k * (Δ ^ 2 * Z)) :=
        mul_le_mul_of_nonneg_right hmK (by positivity)
    _ = (2 * H) ^ k * (((K n : ℝ) * Δ ^ 2) * Z) := by ring
    _ ≤ (2 * H) ^ k * (N ^ (-C_K) * Z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfull hZ0) h2H
    _ = 2 ^ k * AltGridQ_aQ k * (c⁻¹) ^ (2 * k) *
        (N ^ k * H ^ (3 * k + 2) * Y ^ 2 * N ^ (-C_K)) := by
        rw [hZ, div_eq_mul_inv]
        ring

/-- **The summed remainder `sum_weighted_qErrQN_le`**: on the grid `u_j = gridTime s t K n j` with
`K n ≥ N^{C_K}`, the one-step remainders `qErrQN` of `gridDriftQN` at the envelope
`B_k = N^{τ_K} η_{u_{j+1}}^{-k}`, weighted by the coarse row bound `(1 + (1 - u_m)⁻¹)^k` of `Ugen`,
sum to at most `N^{-D_t}` for every `m ≤ K n`, eventually.  The four numerical conditions are those of
`SumWeightedStepErrN_Stmt` (`θ = 1 - τ'`, `RangeCond d τ' t`) with the decay exponent `D_t + k`
(the factor `1 + Lp ≤ 2 N^{k-1}` of `qErrQN`); the `Δ²`-part of `qErrQN` needs only
`k + 2τ_K + (3k+2)θ + D_t < C_K`, which the second condition implies. -/
theorem sum_weighted_qErrQN_le :
    ∀ (d : Sizes) {κ τ' τK C_K D_t : ℝ} {E s t : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) [NeZero k],
    0 < κ → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k → SizeTendsto d →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) → RangeCond d τ' t →
    8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * (D_t + k) < C_K →
    3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + (D_t + k) < C_K →
    2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + (D_t + k) < C_K →
    1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ K n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          qErrQN d E s t K n k (((d.size n : ℕ) : ℝ) ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) j ≤
        ((d.size n : ℕ) : ℝ) ^ (-D_t) := by
  intro d κ τ' τK C_K D_t E s t K k _ hκ hτ' hτ'1 hτK hDt hk hsize hE hs0 hst ht1 hK0 hrange
    h1 h2 h3 h4 hKN
  obtain ⟨c, hc0, hc1, hcE⟩ := AltGridQ_exists_c hκ hE
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hθ0 : 0 ≤ 1 - τ' := by linarith
  have hS := sum_weighted_stepErrN_le d (κ := κ) (τ' := τ') (τK := τK) (C_K := C_K)
    (D_t := D_t + k) (E := E) (s := s) (t := t) (K := K) k hκ hτ' hτ'1 hτK (by positivity) hk
    hsize hE hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  set A : ℝ := 2 ^ k * AltGridQ_aQ k * (c⁻¹) ^ (2 * k) with hA
  have hef : ((k : ℕ) : ℝ) + (1 - τ') * ((3 * k + 2 : ℕ) : ℝ) + τK * ((2 : ℕ) : ℝ) + (-C_K) <
      -D_t := by
    push_cast
    have hkθ : 0 ≤ ((k : ℝ) - 1) * (1 - τ') := mul_nonneg (by linarith) hθ0
    nlinarith [hkθ]
  have hev := AltGridQ_eventually_le d hsize (2 * A) _ (-D_t) hef
  filter_upwards [hrange, hKN, hS, hev, hsize.eventually_ge_atTop 4] with n hR hKn hSn hevn hN4
  intro m hm
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hsplit : ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        qErrQN d E s t K n k (((d.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) j =
      (1 + (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1)) * (∑ j ∈ Finset.range m,
        (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) (((d.size n : ℕ) : ℝ) ^ τK *
              (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) +
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        qStepErrN (d.L n) k (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold qErrQN
    rw [AltGridQ_qStepErrN_split]
    ring
  rw [hsplit]
  -- the `(1 + Lp) stepErrN` part
  have hL2N : ((d.L n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
    have hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = ((d.size n : ℕ) : ℝ) := by
      exact_mod_cast (Sizes.size_eq d n).symm
    have hW : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
    calc ((d.L n : ℕ) : ℝ) ^ 2 = 1 * ((d.L n : ℕ) : ℝ) ^ 2 := (one_mul _).symm
      _ ≤ (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hW) (by positivity)
      _ = ((d.size n : ℕ) : ℝ) := hWL
  have hLp : (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1) ≤ ((d.size n : ℕ) : ℝ) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) hL2N _
  have hNk1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ (k - 1) := one_le_pow₀ hN1
  have h1Lp : 1 + (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1) ≤ 2 * ((d.size n : ℕ) : ℝ) ^ (k - 1) := by
    linarith
  have hpow : ((d.size n : ℕ) : ℝ) ^ (k - 1) * ((d.size n : ℕ) : ℝ) ^ (-(D_t + (k : ℝ))) =
      ((d.size n : ℕ) : ℝ) ^ (-D_t) * ((d.size n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast ((d.size n : ℕ) : ℝ) (k - 1), ← Real.rpow_add hN0]
    have e : (((k - 1 : ℕ) : ℝ)) + (-(D_t + (k : ℝ))) = -D_t + (-1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
    rw [e, Real.rpow_add hN0, Real.rpow_neg_one]
  have hNinv : ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN4
  have hp1 : (1 + (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1)) * (∑ j ∈ Finset.range m,
        (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) (((d.size n : ℕ) : ℝ) ^ τK *
              (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by
    have hp0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-D_t) := Real.rpow_nonneg hN0.le _
    calc _ ≤ (1 + (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1)) *
          ((d.size n : ℕ) : ℝ) ^ (-(D_t + (k : ℝ))) :=
          mul_le_mul_of_nonneg_left (hSn m hm) (by positivity)
      _ ≤ (2 * ((d.size n : ℕ) : ℝ) ^ (k - 1)) * ((d.size n : ℕ) : ℝ) ^ (-(D_t + (k : ℝ))) :=
          mul_le_mul_of_nonneg_right h1Lp (Real.rpow_nonneg hN0.le _)
      _ = 2 * (((d.size n : ℕ) : ℝ) ^ (-D_t) * ((d.size n : ℕ) : ℝ)⁻¹) := by
          rw [mul_assoc, hpow]
      _ ≤ 2 * (((d.size n : ℕ) : ℝ) ^ (-D_t) * (1 / 4)) := by gcongr
      _ = ((d.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by ring
  -- the `Δ²` part
  have hx := AltGridQ_extra_sum_le d k hk c n hc0 hc1 (hcE n) hτK hτ'1 (hE2 n) (hs0 n) (hst n)
    (ht1 n) (hK0 n) hR hKn h4.le m hm
  rw [AltGridQ_mono ((d.size n : ℕ) : ℝ) hN0 k (1 - τ') (3 * k + 2) τK 2 (-C_K), ← hA] at hx
  have hp2 : ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
        qStepErrN (d.L n) k (gridTime s t K n j) (gridStep s t K n)
          (lkEnvN (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k))
          (driftEnvN (d.L n) (d.W n) (E n) k (gridTime s t K n j)
            (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k)) 0 ≤
      ((d.size n : ℕ) : ℝ) ^ (-D_t) / 2 := by
    refine hx.trans (le_of_mul_le_mul_left ?_ (two_pos : (0 : ℝ) < 2))
    calc 2 * (A * ((d.size n : ℕ) : ℝ) ^ (((k : ℕ) : ℝ) + (1 - τ') * ((3 * k + 2 : ℕ) : ℝ) +
          τK * ((2 : ℕ) : ℝ) + (-C_K))) =
        2 * A * ((d.size n : ℕ) : ℝ) ^ (((k : ℕ) : ℝ) + (1 - τ') * ((3 * k + 2 : ℕ) : ℝ) +
          τK * ((2 : ℕ) : ℝ) + (-C_K)) := by ring
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D_t) := hevn
      _ = 2 * (((d.size n : ℕ) : ℝ) ^ (-D_t) / 2) := by ring
  linarith [hp1, hp2]

end GridSum

end RBM.Ind

end
