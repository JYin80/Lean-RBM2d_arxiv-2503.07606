/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierarchyN
import RBM2D.Induction.HierAlgebra
import RBM2D.Path.LoopStep
import RBM2D.Path.UBounds
import RBM2D.Path.ScalesBridge
import RBM2D.Path.GoodEvent
import RBM2D.Path.Stop
import RBM2D.Loop.KBound

/-!
# One grid step of (`LK_SDE`) for general `n` and all `σ`

Paper: arXiv:2503.07606, Section 5: `LK_SDE`, `def_Ustz`, `def_Ustz_2`, and Section 3:
`eq:bcal_k_2`.

* `gridDriftN` : the statement `GridDriftN` (`RBM2D.Induction.HierVocab`): a.e., the predictable increment
  `P_j = 𝔼[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A_j` equals `Δ` times the non-linear drift
  `Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}` at `u_j`, up to the explicit `stepErrN`, given a
  deterministic envelope `B_k` of `𝒦` on `[0, u_{j+1}]`.  Proof: `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰`
  (`gdn_algebra`), with `R₁` from `condExp_loop_drift`, `R_𝒦` from `gdn_K_step` and `R_𝒰` from
  `gdn_Ugen_step_le`; `D_j` is supplied by `hierarchyN`.
* `exists_norm_Kcal_le_win` : the envelope witness (asymptotic form).

The argument parallels the one-dimensional formalization, re-checked for `d = 2` (`Z2 L` labels,
the five-point `SB`, `W → W²`, `L → L²` in the `𝒦` step, `N = (WL)²`): the `𝒦` step is
`gdn_K_step`; the `𝒰` step is `gdn_tens_sub_le`, `gdn_tens_step_le`, `gdn_Ugen_step_le` (in the
`Ugen`/`thetaSig` vocabulary); the step error is `stepErrN`, assembled in `gridDriftN`; the
Lipschitz bound of `𝒦` is `gdn_K_lip`; the envelope witness is `exists_norm_Kcal_le_win`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The abstract `k`-slot tensor step -/

section TensorStep

variable {L : ℕ} [NeZero L]

/-- `(⊗_i U_i) A` at `x`: `Σ_y (Π_i U_i(x_i, y_i)) A(y)`. -/
private def gdnTens {k : ℕ} (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin k → Z2 L) → ℂ)
    (x : Fin k → Z2 L) : ℂ :=
  ∑ y : Fin k → Z2 L, (∏ i, U i (x i) (y i)) * A y

/-- `(Σ_i (1 ⊗ ⋯ ⊗ G_i ⊗ ⋯ ⊗ 1)) A` at `x`. -/
private def gdnGen {k : ℕ} (G : Fin k → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin k → Z2 L) → ℂ)
    (x : Fin k → Z2 L) : ℂ :=
  ∑ i : Fin k, ∑ c : Z2 L, G i (x i) c * A (Function.update x i c)

private theorem gdnTens_zero (U : Fin 0 → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin 0 → Z2 L) → ℂ)
    (x : Fin 0 → Z2 L) : gdnTens U A x = A x := by
  unfold gdnTens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem gdnGen_zero (G : Fin 0 → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin 0 → Z2 L) → ℂ)
    (x : Fin 0 → Z2 L) : gdnGen G A x = 0 := by
  simp [gdnGen]

private theorem gdnTens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Z2 L) (Z2 L) ℂ)
    (A : (Fin (k + 1) → Z2 L) → ℂ) (x : Fin (k + 1) → Z2 L) :
    gdnTens U A x = ∑ y0 : Z2 L, U 0 (x 0) y0 *
      gdnTens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold gdnTens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Z2 L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem gdnGen_succ {k : ℕ} (G : Fin (k + 1) → Matrix (Z2 L) (Z2 L) ℂ)
    (A : (Fin (k + 1) → Z2 L) → ℂ) (x : Fin (k + 1) → Z2 L) :
    gdnGen G A x = ∑ c : Z2 L, G 0 (x 0) c * A (Fin.cons c (Fin.tail x)) +
      gdnGen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x) := by
  unfold gdnGen
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
private theorem gdn_row_mul {P : Matrix (Z2 L) (Z2 L) ℂ} {r m : ℝ}
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
private theorem gdn_row_one_add {e : Matrix (Z2 L) (Z2 L) ℂ} {a : ℝ}
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
private theorem gdn_one_add_mul (e : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) (f : Z2 L → ℂ) :
    ∑ c : Z2 L, (1 + e) x c * f c = f x + ∑ c : Z2 L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/-- The first-order tensor bound: `‖(⊗U_i) A - A‖ ≤ ((1+a)^k - 1) M`. -/
private theorem gdn_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ),
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Z2 L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖gdnTens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [gdnTens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Z2 L) (Z2 L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Z2 L, ∑ c : Z2 L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact gdn_row_one_add (fun x'' => hU 0 x'') x'
      set T : Z2 L → ℂ := fun y0 => gdnTens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Z2 L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : gdnTens U A x - A x =
          ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, e (x 0) c * Y c := by
        rw [gdnTens_succ, hAx]
        have h1 : ∑ c : Z2 L, U 0 (x 0) c * T c =
            ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Z2 L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Z2 L, e (x 0) c * Y c := by
          rw [hU0]; exact gdn_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        gdn_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Z2 L, e (x 0) c * Y c‖ ≤ a * M :=
        gdn_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Z2 L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

/-- The second-order tensor bound: with `‖(U_i - 1)‖_rows ≤ a`, `‖(U_i - 1 - G_i)‖_rows ≤ b`,
`‖(⊗U_i) A - A - (Σ_i G_i) A‖ ≤ (k b + (1+a)^k - 1 - k a) M`. -/
private theorem gdn_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ (k : ℕ) (U G : Fin k → Matrix (Z2 L) (Z2 L) ℂ),
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1) x c‖ ≤ a) →
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1 - G i) x c‖ ≤ b) →
      ∀ (A : (Fin k → Z2 L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖gdnTens U A x - A x - gdnGen G A x‖ ≤ ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M := by
  intro k
  induction k with
  | zero =>
      intro U G _ _ A M _ x
      rw [gdnTens_zero, gdnGen_zero]
      simp
  | succ k ih =>
      intro U G hU hG A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      set e : Matrix (Z2 L) (Z2 L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      set T : Z2 L → ℂ := fun y0 => gdnTens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Z2 L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        gdn_tens_sub_le ha k (fun i => U i.succ) (fun i x' => hU i.succ x')
          (fun y' => A (Fin.cons y0 y')) M (fun y' => hA _) (Fin.tail x)
      have hIH : ‖T (x 0) - Y (x 0) - gdnGen (fun i : Fin k => G i.succ)
          (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x)‖ ≤
          ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M :=
        ih (fun i => U i.succ) (fun i => G i.succ) (fun i x' => hU i.succ x')
          (fun i x' => hG i.succ x') (fun y' => A (Fin.cons (x 0) y')) M (fun y' => hA _)
          (Fin.tail x)
      set g' : ℂ := gdnGen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y'))
        (Fin.tail x) with hg'
      have hsplit : gdnTens U A x - A x - gdnGen G A x =
          (T (x 0) - Y (x 0) - g') + ∑ c : Z2 L, e (x 0) c * (T c - Y c) +
            ∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c := by
        rw [gdnTens_succ, gdnGen_succ, hAx]
        have h1 : ∑ c : Z2 L, U 0 (x 0) c * T c =
            T (x 0) + ∑ c : Z2 L, e (x 0) c * (T c - Y c) + ∑ c : Z2 L, e (x 0) c * Y c := by
          rw [hU0, gdn_one_add_mul, add_assoc, ← Finset.sum_add_distrib]
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
        gdn_row_mul (fun x' => hU 0 x') (x 0) hTY
      have hb3 : ‖∑ c : Z2 L, (U 0 - 1 - G 0) (x 0) c * Y c‖ ≤ b * M :=
        gdn_row_mul (fun x' => hG 0 x') (x 0) (fun c => hA _)
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
private theorem gdn_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ‖ = 1 := by
  cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

private theorem gdn_norm_edge {E : ℝ} (hE : |E| ≤ 2) (σ σ' : Bool) :
    ‖KLoop.mSig E σ * KLoop.mSig E σ'‖ = 1 := by
  rw [norm_mul, gdn_norm_mSig hE, gdn_norm_mSig hE, one_mul]

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
private theorem gdn_sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}`. -/
private theorem gdn_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Z2 L, ‖thetaGenMat L ξ s x c‖ =
      ‖ξ‖ * ‖(SB L * Theta L ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((gdn_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L ((s : ℂ) * ξ)‖ ≤ ‖SB L‖ * ‖Theta L ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L ((s : ℂ) * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le L hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u` (resolvent identity
`Theta_sub_Theta`). -/
private theorem gdn_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
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
  refine mul_le_mul_of_nonneg_left ((gdn_sum_norm_row_le_opNorm _ x).trans ?_) (by positivity)
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
private theorem gdn_norm_real_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖(w : ℂ) * ξ‖ = w := by
  rw [norm_mul, hξ, mul_one, Complex.norm_of_nonneg hw]

/-- `(1 - vξS)Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}`, i.e. `𝒰_{u,u+Δ} - 1 = Δ · (generator at u+Δ)`
(`def_Ustz_2`). -/
private theorem gdn_ukerMat_sub_one (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ}
    (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) :
    ukerMat L ξ u (u + Δ) - 1 = (Δ : ℂ) • thetaGenMat L ξ (u + Δ) := by
  have h1 : (1 : Matrix (Z2 L) (Z2 L) ℂ) - ((u : ℂ) * ξ) • SB L =
      (1 - (((u + Δ : ℝ) : ℂ) * ξ) • SB L) + ((Δ : ℂ) * ξ) • SB L := by
    push_cast
    module
  unfold ukerMat thetaGenMat
  rw [h1, add_mul, mul_Theta L hL hd, Matrix.smul_mul, add_sub_cancel_left, smul_smul]

/-- Row sums of `𝒰_{u,u+Δ} - 1` are `≤ Δ (1-(u+Δ))⁻¹` for `‖ξ‖ = 1`. -/
private theorem gdn_row_U (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(ukerMat L ξ u (u + Δ) - 1) x c‖ ≤ Δ * (1 - (u + Δ))⁻¹ := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ (by linarith)]; exact hv
  rw [gdn_ukerMat_sub_one hL hd]
  have hentry : ∀ c : Z2 L, ‖((Δ : ℂ) • thetaGenMat L ξ (u + Δ)) x c‖ =
      Δ * ‖thetaGenMat L ξ (u + Δ) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  have := gdn_row_thetaGenMat hL hd x
  rwa [hξ, gdn_norm_real_mul hξ (by linarith), one_mul] at this

/-- Row sums of `𝒰_{u,u+Δ} - 1 - Δ (generator at u)` are `≤ Δ² (1-(u+Δ))⁻²` for `‖ξ‖ = 1`. -/
private theorem gdn_row_UG (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖(ukerMat L ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat L ξ u) x c‖ ≤
      Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ (by linarith)]; exact hv
  have hu : ‖(u : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ hu0]; linarith
  have hM : ukerMat L ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat L ξ u =
      (Δ : ℂ) • (thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) := by
    rw [gdn_ukerMat_sub_one hL hd, smul_sub]
  rw [hM]
  have hentry : ∀ c : Z2 L, ‖((Δ : ℂ) • (thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u)) x c‖ =
      Δ * ‖(thetaGenMat L ξ (u + Δ) - thetaGenMat L ξ u) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  have h1 := gdn_row_thetaGenMat_diff hL hΔ hu hd x
  rw [hξ, gdn_norm_real_mul hξ (by linarith), gdn_norm_real_mul hξ hu0] at h1
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
private theorem gdn_Ugen_step_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Z2 L) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Z2 L) :
    ‖Ugen L E σ u (u + Δ) A x - A x - (Δ : ℂ) * thetaSig L E σ u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have key := gdn_tens_step_le (L := L) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u)
    (fun i x' => gdn_row_U hL (gdn_norm_edge hE _ _) hu0 hΔ hv x')
    (fun i x' => gdn_row_UG hL (gdn_norm_edge hE _ _) hu0 hΔ hv x') A M hA x
  have hT : gdnTens (fun i : Fin k =>
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u (u + Δ)) A x =
      Ugen L E σ u (u + Δ) A x := rfl
  have hG : gdnGen (fun i : Fin k =>
      (Δ : ℂ) • thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u) A x =
      (Δ : ℂ) * thetaSig L E σ u A x := by
    unfold gdnGen thetaSig
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

/-! ## 3. One step of `𝒦` -/

section KStep

variable {L W : ℕ} [NeZero L]

/-- Bound `‖𝒦_w(J)‖ ≤ B` on `[0, v]` for the loops of length at most `k`. -/
private def GdnEnv (L W : ℕ) [NeZero L] (E : ℝ) (k : ℕ) (v B : ℝ) : Prop :=
  ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
    ‖KLoop.Kcal L W E w J‖ ≤ B

/-- `∂_t 𝒦_t(J) = primRhs (𝒦_t)(J)` (`isPrimitive_Kcal`, the equation `pro_dyncalK`). -/
private theorem gdn_hasDeriv (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {J : LoopIdx (Z2 L)} (hJ : J.WF) (h2 : 2 ≤ J.length) :
    HasDerivAt (fun s => KLoop.Kcal L W E s J) (KLoop.primRhs L W (KLoop.Kcal L W E t) J) t :=
  (KLoop.isPrimitive_Kcal L W hL hW E hE).1 t ⟨ht0, ht1⟩ J hJ h2

/-- The `𝒦` family is Lipschitz in time with constant `W²k²L²B²` on `[0, v]` (uses the
derivative bound `‖primRhs (𝒦_w)(J)‖ ≤ W²k²L²B²`, `norm_primBil_le`, with the `d = 2` constant). -/
private theorem gdn_K_lip (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv1 : v < 1)
    {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B) (hB : GdnEnv L W E k v B)
    {J : LoopIdx (Z2 L)} (hJ : J.WF) (h2 : 2 ≤ J.length) (hk : J.length ≤ k)
    {u : ℝ} (hu : 0 ≤ u) :
    ∀ r ∈ Set.Icc u v, ‖KLoop.Kcal L W E r J - KLoop.Kcal L W E u J‖ ≤
      ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * B ^ 2) * (r - u) := by
  have hbound : ∀ r ∈ Set.Icc u v,
      ‖KLoop.primRhs L W (KLoop.Kcal L W E r) J‖ ≤ (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * B ^ 2 := by
    intro r hr
    rw [← primBil_self]
    have hr' : r ∈ Set.Icc (0 : ℝ) v := ⟨hu.trans hr.1, hr.2⟩
    have h1 := norm_primBil_le L hL W (KLoop.Kcal L W E r) (KLoop.Kcal L W E r) J hJ hB0 hB0
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
    have hkk : (J.length : ℝ) ≤ k := by exact_mod_cast hk
    have hJ0 : (0 : ℝ) ≤ J.length := Nat.cast_nonneg _
    calc _ ≤ _ := h1
      _ ≤ (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * B * B := by gcongr
      _ = _ := by ring
  intro r hr
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := r)
    (f := fun s => KLoop.Kcal L W E s J)
    (f' := fun s => KLoop.primRhs L W (KLoop.Kcal L W E s) J)
    (C := (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * B ^ 2)
    (fun x hx => (gdn_hasDeriv hL hW hE (hu.trans hx.1) (lt_of_le_of_lt (hx.2.trans hr.2) hv1) hJ
      h2).hasDerivWithinAt)
    (fun x hx => hbound x ⟨hx.1, hx.2.le.trans hr.2⟩) r ⟨hr.1, le_rfl⟩
  exact hres

/-- **One step of `𝒦`** (with the
`d = 2` constants `W² k² L²`): for `0 ≤ Δ ≤ 1`, `u + Δ < 1`, on the envelope `B`,
`‖𝒦_{u+Δ}(I) - 𝒦_u(I) - Δ ∂_u𝒦_u(I)‖ ≤ kStepC L W k B Δ²`. -/
private theorem gdn_K_step (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hv1 : u + Δ < 1) {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : GdnEnv L W E k (u + Δ) B) {I : LoopIdx (Z2 L)} (hI : I.WF) (h2 : 2 ≤ I.length)
    (hk : I.length = k) :
    ‖KLoop.Kcal L W E (u + Δ) I - KLoop.Kcal L W E u I -
        (Δ : ℂ) * KLoop.primRhs L W (KLoop.Kcal L W E u) I‖ ≤ kStepC L W k B * Δ ^ 2 := by
  set c : ℝ := (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set D1 : ℝ := c * B ^ 2 with hD1
  have hD10 : 0 ≤ D1 := by positivity
  set C0 : ℂ := KLoop.primRhs L W (KLoop.Kcal L W E u) I with hC0
  have hkI : (I.length : ℝ) = k := by exact_mod_cast hk
  -- the derivative bound
  have hbound : ∀ r ∈ Set.Ico u (u + Δ),
      ‖KLoop.primRhs L W (KLoop.Kcal L W E r) I - C0‖ ≤ 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by
    intro r hr
    have hr' : r ∈ Set.Icc u (u + Δ) := ⟨hr.1, hr.2.le⟩
    have hrB : r ∈ Set.Icc (0 : ℝ) (u + Δ) := ⟨hu0.trans hr.1, hr.2.le⟩
    have hδ : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖(KLoop.Kcal L W E r - KLoop.Kcal L W E u) J‖ ≤ D1 * (r - u) := by
      intro J hJ hJ2 hJk
      exact gdn_K_lip hL hW hE hv1 hB0 hB hJ hJ2 (hJk.trans hk.le) hu0 r hr'
    have hδ0 : 0 ≤ D1 * (r - u) := mul_nonneg hD10 (by linarith [hr.1])
    have hKu : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖KLoop.Kcal L W E u J‖ ≤ B := fun J hJ hJ2 hJk =>
      hB u ⟨hu0, by linarith⟩ J hJ hJ2 (hJk.trans hk.le)
    have hsub := primRhs_sub L W (KLoop.Kcal L W E r) (KLoop.Kcal L W E u) I
    have e1 := norm_primBil_le L hL W (KLoop.Kcal L W E u) (KLoop.Kcal L W E r - KLoop.Kcal L W E u)
      I hI hB0 hδ0 hKu hδ
    have e2 := norm_primBil_le L hL W (KLoop.Kcal L W E r - KLoop.Kcal L W E u) (KLoop.Kcal L W E u)
      I hI hδ0 hB0 hδ hKu
    have e3 := norm_primBil_le L hL W (KLoop.Kcal L W E r - KLoop.Kcal L W E u)
      (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I hI hδ0 hδ0 hδ hδ
    rw [hkI, ← hc] at e1 e2 e3
    have hrΔ : r - u ≤ Δ := by linarith [hr.2]
    have hru : 0 ≤ r - u := by linarith [hr.1]
    have hprim : KLoop.primRhs L W (KLoop.Kcal L W E r) I - C0 =
        primBil L W (KLoop.Kcal L W E u) (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I +
        primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u) (KLoop.Kcal L W E u) I +
        primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u)
          (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I := hsub
    rw [hprim]
    calc _ ≤ ‖primBil L W (KLoop.Kcal L W E u) (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I +
            primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u) (KLoop.Kcal L W E u) I‖ +
          ‖primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u)
            (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I‖ := norm_add_le _ _
      _ ≤ (‖primBil L W (KLoop.Kcal L W E u) (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I‖ +
            ‖primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u) (KLoop.Kcal L W E u) I‖) +
          ‖primBil L W (KLoop.Kcal L W E r - KLoop.Kcal L W E u)
            (KLoop.Kcal L W E r - KLoop.Kcal L W E u) I‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (c * B * (D1 * (r - u)) + c * (D1 * (r - u)) * B) + c * (D1 * (r - u)) * (D1 * (r - u)) := by
          exact add_le_add (add_le_add e1 e2) e3
      _ ≤ (c * B * (D1 * Δ) + c * (D1 * Δ) * B) + c * (D1 * Δ) * (D1 * Δ) := by gcongr
      _ = 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by ring
  have hderiv : ∀ x ∈ Set.Icc u (u + Δ), HasDerivWithinAt
      (fun r : ℝ => KLoop.Kcal L W E r I - (r - u) • C0)
      (KLoop.primRhs L W (KLoop.Kcal L W E x) I - C0) (Set.Icc u (u + Δ)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hu0.trans hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have h1 := gdn_hasDeriv (W := W) hL hW hE hx0 hx1 hI h2
    have h2' : HasDerivAt (fun r : ℝ => (r - u) • C0) C0 x := by
      simpa using ((hasDerivAt_id x).sub_const u).smul_const C0
    exact (h1.sub h2').hasDerivWithinAt
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := u + Δ)
    (f := fun r : ℝ => KLoop.Kcal L W E r I - (r - u) • C0)
    (f' := fun x => KLoop.primRhs L W (KLoop.Kcal L W E x) I - C0)
    (C := 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) hderiv hbound (u + Δ) ⟨by linarith, le_rfl⟩
  have hlhs : (KLoop.Kcal L W E (u + Δ) I - (u + Δ - u) • C0) - (KLoop.Kcal L W E u I - (u - u) • C0) =
      KLoop.Kcal L W E (u + Δ) I - KLoop.Kcal L W E u I - (Δ : ℂ) * C0 := by
    have h1 : u + Δ - u = Δ := by ring
    rw [h1, sub_self, zero_smul, sub_zero, Complex.real_smul]
    ring
  have hres' : ‖(KLoop.Kcal L W E (u + Δ) I - (u + Δ - u) • C0) -
      (KLoop.Kcal L W E u I - (u - u) • C0)‖ ≤
      (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * (u + Δ - u) := hres
  rw [hlhs, add_sub_cancel_left] at hres'
  refine hres'.trans ?_
  unfold kStepC
  have hΔ3 : Δ ^ 3 ≤ Δ ^ 2 := by
    calc Δ ^ 3 = Δ ^ 2 * Δ := by ring
      _ ≤ Δ ^ 2 * 1 := by gcongr
      _ = Δ ^ 2 := mul_one _
  have hcD : 0 ≤ c * D1 ^ 2 := by positivity
  calc (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * Δ
      = 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 3 := by ring
    _ ≤ 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 2 := by gcongr
    _ = _ := by rw [hD1, hc]; ring

end KStep

/-! ## 4. The assembly -/

section Assembly

private theorem gdn_loopOf_wf {L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem gdn_loopOf_length {L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- The grid-time facts used by `gridDriftN`: `Δ ≥ 0`, `u_j ≥ 0`, `u_{j+1} = u_j + Δ`,
`u_{j+1} < 1`, `Δ ≤ 1`. -/
private theorem gdn_time_facts (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
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
private theorem gdn_integrable_gloop (d : Sizes) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {E : ℝ}
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

/-- The exact algebra `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰`. -/
private theorem gdn_algebra {g1 Gj gen K1 K0 Kd U θ S : ℂ} {Δ : ℝ} {eR eK eU : ℝ}
    (hier : gen - Kd = θ + S) (hR : ‖g1 - Gj - (Δ : ℂ) * gen‖ ≤ eR)
    (hK : ‖K1 - K0 - (Δ : ℂ) * Kd‖ ≤ eK) (hU : ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ ≤ eU) :
    ‖(g1 - K1 - U) - (Δ : ℂ) * S‖ ≤ eR + eK + eU := by
  have hid : (g1 - K1 - U) - (Δ : ℂ) * S =
      (g1 - Gj - (Δ : ℂ) * gen) - (K1 - K0 - (Δ : ℂ) * Kd) - (U - (Gj - K0) - (Δ : ℂ) * θ) := by
    linear_combination (Δ : ℂ) * hier
  rw [hid]
  calc _ ≤ ‖(g1 - Gj - (Δ : ℂ) * gen) - (K1 - K0 - (Δ : ℂ) * Kd)‖ +
        ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ := norm_sub_le _ _
    _ ≤ (‖g1 - Gj - (Δ : ℂ) * gen‖ + ‖K1 - K0 - (Δ : ℂ) * Kd‖) +
        ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ eR + eK + eU := by gcongr

/-- **`GridDriftN`**: one grid step of (`LK_SDE`), general `n`, all `σ`. -/
theorem gridDriftN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) : GridDriftN d E s t K := by
  intro hE hs0 hst ht1 hK n j hj k _ hk σ Bk hBk hB
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := gdn_time_facts s t K n j (hs0 n) (hst n) (ht1 n) (hK n) hj
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hkpos : 1 ≤ k := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hB' : GdnEnv (d.L n) (d.W n) (E n) k (gridTime s t K n j + gridStep s t K n) Bk := by
    intro w hw J hJ h2 hJk
    exact hB w (by rw [hvu]; exact hw) J hJ h2 hJk
  -- the a.e. facts for a fixed label vector
  have hae : ∀ a : Fin k → Z2 (d.L n), ∀ᵐ ω ∂(pathP d),
      (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' a | filt d j] ω =
        (pathP d)[fun ω' => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
            (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt d j] ω -
          KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a) ∧
      ‖(pathP d)[fun ω' => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
            (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt d j] ω -
          gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
            (spectralZ (E n) (gridTime s t K n j)) (loopOf σ a) -
          (gridStep s t K n : ℂ) * genMat (E n) (gridTime s t K n j) (pathH d s t K n j ω)
            (loopOf σ a)‖ ≤
        envConst (d.L n) (d.W n) (E n) k (gridTime s t K n (j + 1)) *
          gridStep s t K n ^ ((3 : ℝ) / 2) := by
    intro a
    have hint := gdn_integrable_gloop d s t K n (j + 1) (hE n) hv1 (loopOf σ a)
      (gdn_loopOf_wf σ a) (by rw [gdn_loopOf_length]; exact hkpos)
    have hsub := condExp_sub hint
      (integrable_const (KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1))
        (loopOf σ a))) (filt d j)
    have hconst := condExp_const (μ := pathP d) ((filt d).le j)
      (KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a))
    have hdrift := condExp_loop_drift d s t K n j (E n) (hE n) (gdn_loopOf_wf σ a) (hs0 n)
      (hst n) (hK n) hj hv1
    filter_upwards [hsub, hdrift] with ω h1 h2
    refine ⟨?_, ?_⟩
    · have hfun : (fun ω' : PathΩ d => AvecN d E s t K n (j + 1) σ ω' a) =
          (fun ω' => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
            (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ a)) -
          (fun _ => KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1))
            (loopOf σ a)) := rfl
      rw [hfun, h1, Pi.sub_apply, hconst]
    · rw [gdn_loopOf_length] at h2
      exact h2
  filter_upwards [ae_all_iff.2 hae] with ω hω a
  obtain ⟨hce, hR1⟩ := hω a
  have hη : 0 < RBM.Path.etaT (E n) (gridTime s t K n j) := RBM.Path.etaT_pos (hE n) hu1
  have hz : RBM.Path.etaT (E n) (gridTime s t K n j) ≤
      |(spectralZ (E n) (gridTime s t K n j)).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (spectralM_im_pos (hE n)))]
    exact le_rfl
  -- the sup bound on `A_j`
  have hsup : ∀ b : Fin k → Z2 (d.L n), ‖AvecN d E s t K n j σ ω b‖ ≤
      (RBM.Path.etaT (E n) (gridTime s t K n j))⁻¹ ^ k * (((d.W n : ℕ) : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk := by
    intro b
    have hlen : (loopOf σ b).a.length = k := by simp [loopOf]
    have hHb : (blockMat (pathH d s t K n j ω)).IsHermitian :=
      (pathH_isHermitian d s t K n j ω).submatrix _
    have h1 := norm_gloop_le_of_le_abs_im hHb hη hz
      (loopOf σ b) (gdn_loopOf_wf σ b) (by rw [hlen]; exact hkpos)
    rw [hlen] at h1
    have h2 : ‖KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖ ≤ Bk :=
      hB _ ⟨hu0, by rw [hvu]; linarith⟩ (loopOf σ b) (gdn_loopOf_wf σ b)
        (by rw [gdn_loopOf_length]; exact hk) (by rw [gdn_loopOf_length])
    calc ‖AvecN d E s t K n j σ ω b‖ ≤
          ‖gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
            (spectralZ (E n) (gridTime s t K n j)) (loopOf σ b)‖ +
          ‖KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖ :=
            norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  -- the three remainders
  have hK' := gdn_K_step hL3 hW1 (hE n) hu0 hΔ0 hΔ1 (by rw [← hvu]; exact hv1) hBk hB'
    (gdn_loopOf_wf σ a) (by rw [gdn_loopOf_length]; exact hk) (gdn_loopOf_length σ a)
  rw [← hvu] at hK'
  have hKd : deriv (fun x => KLoop.Kcal (d.L n) (d.W n) (E n) x (loopOf σ a))
      (gridTime s t K n j) =
      KLoop.primRhs (d.L n) (d.W n) (KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j))
        (loopOf σ a) :=
    (gdn_hasDeriv hL3 hW1 (hE n) hu0 hu1 (gdn_loopOf_wf σ a)
      (by rw [gdn_loopOf_length]; exact hk)).deriv
  rw [← hKd] at hK'
  have hU' := gdn_Ugen_step_le hL3 (hE n).le σ hu0 hΔ0 (by rw [← hvu]; exact hv1)
    (AvecN d E s t K n j σ ω) _ hsup a
  rw [← hvu] at hU'
  have hier := hierarchyN (d.L n) (d.W n) (E n) hL3 (hE n) (gridTime s t K n j) hu0 hu1
    (pathH d s t K n j ω) (pathH_isHermitian d s t K n j ω) k hk σ a
  have hlk : lkTensor (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) σ =
      AvecN d E s t K n j σ ω := rfl
  rw [hlk] at hier
  have hpred : predIncN d E s t K n j σ ω a =
      ((pathP d)[fun ω' => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n (j + 1) ω'))
            (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt d j] ω -
          KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a)) -
        Ugen (d.L n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
          (AvecN d E s t K n j σ ω) a := by
    unfold predIncN
    rw [hce]
  rw [hpred]
  have key := gdn_algebra
    (S := (∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
              (pathH d s t K n j ω) l (loopOf σ a) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) (loopOf σ a) +
            egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) (loopOf σ a)))
    (by rw [hier]; ring) hR1 hK' hU'
  refine key.trans (le_of_eq ?_)
  unfold stepErrN
  ring

end Assembly

/-! ## 5. The envelope witness -/

section Envelope

/-- `List.ofFn (fun i : Fin n => l.getD i d) = l` when `l.length = n`. -/
private theorem gdn_ofFn_getD {α : Type*} (l : List α) (d : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i d) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `loopOf` of its own signs and labels. -/
private theorem gdn_loopOf_eq {L : ℕ} [NeZero L] (J : LoopIdx (Z2 L)) (hJ : J.WF) :
    KLoop.loopOf L (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i 0) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [KLoop.loopOf, LoopIdx.length]
  rw [gdn_ofFn_getD σ' false a'.length hJ, gdn_ofFn_getD a' 0 a'.length rfl]

/-- **The envelope witness.**  Fixed `κ > 0`, `m`, `τ > 0`: eventually in `N`,
uniformly over `W² L² = N`, `L ≥ 3`, `W ≥ 1`, `|E| ≤ 2 - κ`, `0 ≤ u ≤ v < 1` and the well-formed loops
`J` of length in `[2, m]`, `‖𝒦_u(J)‖ ≤ N^τ η_v^{-m}`.  The input is `Kbound_prec_uncond`
(`(eq:bcal_k_2)`, a `≺` statement), hence the factor `N^τ` (rather than a fixed constant). -/
theorem exists_norm_Kcal_le_win (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = N →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v < 1 →
        ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ m →
          ‖KLoop.Kcal L W E u J‖ ≤ (N : ℝ) ^ τ * ((RBM.Path.etaT E v)⁻¹) ^ m := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Icc 2 m,
      ∀ x : (p : KLoop.Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L),
        ‖KLoop.Kcal x.1.L x.1.W x.1.E x.1.t (KLoop.loopOf x.1.L x.2.1 x.2.2)‖ ≤
          (N : ℝ) ^ τ * (KLoop.Mt x.1.L x.1.W x.1.E x.1.t)⁻¹ ^ (n - 1) :=
    (Filter.eventually_all_finset _).2 fun n hn =>
      KLoop.Kbound_prec_uncond n (by have := (Finset.mem_Icc.1 hn).1; omega) κ hκ τ hτ
  filter_upwards [hall] with N hN L W _ hL hW hWL E hE u v hu huv hv J hJ h2 hJm
  have hn : J.length ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨h2, hJm⟩
  have hx := hN J.length hn
    ⟨⟨L, W, hL, hW, hWL, E, hE, u, hu, lt_of_le_of_lt huv hv⟩,
      fun i => J.σ.getD i false, fun i => J.a.getD i 0⟩
  have hx' : ‖KLoop.Kcal L W E u (KLoop.loopOf L (fun i : Fin J.length => J.σ.getD i false)
        (fun i : Fin J.length => J.a.getD i 0))‖ ≤
      (N : ℝ) ^ τ * (KLoop.Mt L W E u)⁻¹ ^ (J.length - 1) := hx
  rw [gdn_loopOf_eq J hJ] at hx'
  have hE2 : |E| < 2 := by linarith
  have hv0 : 0 ≤ v := hu.trans huv
  have hηv : 0 < RBM.Path.etaT E v := RBM.Path.etaT_pos hE2 hv
  have hIm : 0 ≤ (spectralM E).im := (spectralM_im_pos hE2).le
  have hηle : RBM.Path.etaT E v ≤ RBM.Path.etaT E u :=
    mul_le_mul_of_nonneg_right (by linarith) hIm
  have hη1 : RBM.Path.etaT E v ≤ 1 := by
    have hsq : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    have him : (spectralM E).im ≤ 1 := by rw [spectralM_im]; linarith
    calc RBM.Path.etaT E v = (1 - v) * (spectralM E).im := rfl
      _ ≤ 1 * 1 := mul_le_mul (by linarith) him hIm (by norm_num)
      _ = 1 := one_mul 1
  have hMt : RBM.Path.etaT E v ≤ KLoop.Mt L W E u := by
    rw [RBM.Path.kloop_Mt_eq (by linarith)]
    have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW
      nlinarith
    have hell : 1 ≤ RBM.Path.ellT L u := RBM.Path.one_le_ellT (by omega) hu (lt_of_le_of_lt huv hv)
    have hell2 : (1 : ℝ) ≤ RBM.Path.ellT L u ^ 2 := by nlinarith
    have hprod : (1 : ℝ) ≤ (W : ℝ) ^ 2 * RBM.Path.ellT L u ^ 2 := by nlinarith
    calc RBM.Path.etaT E v ≤ RBM.Path.etaT E u := hηle
      _ ≤ (W : ℝ) ^ 2 * RBM.Path.ellT L u ^ 2 * RBM.Path.etaT E u :=
        le_mul_of_one_le_left (hηv.le.trans hηle) hprod
  have hinv : (KLoop.Mt L W E u)⁻¹ ≤ (RBM.Path.etaT E v)⁻¹ := inv_anti₀ hηv hMt
  have hinv0 : 0 ≤ (KLoop.Mt L W E u)⁻¹ := inv_nonneg.2 (hηv.le.trans hMt)
  have hone : 1 ≤ (RBM.Path.etaT E v)⁻¹ := (one_le_inv₀ hηv).2 hη1
  calc ‖KLoop.Kcal L W E u J‖ ≤ (N : ℝ) ^ τ * (KLoop.Mt L W E u)⁻¹ ^ (J.length - 1) := hx'
    _ ≤ (N : ℝ) ^ τ * ((RBM.Path.etaT E v)⁻¹) ^ m := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        calc (KLoop.Mt L W E u)⁻¹ ^ (J.length - 1) ≤ ((RBM.Path.etaT E v)⁻¹) ^ (J.length - 1) :=
              pow_le_pow_left₀ hinv0 hinv _
          _ ≤ ((RBM.Path.etaT E v)⁻¹) ^ m := pow_le_pow_right₀ hone (by omega)

end Envelope

end RBM.Ind
