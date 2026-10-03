/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltBudgetTerms
import RBM2D.Induction.AltProxyQ
import RBM2D.Induction.GridGoodEvent
import RBM2D.Induction.NonAltEnd
import RBM2D.Induction.AltGridQ
import RBM2D.Induction.AltDriftQ

/-!
# The alternating endpoint, part 1: vocabulary, the kernel-start shift and the compositions

Part of the alternating endpoint `AltGridEnd`.  This file holds:

* Section 1: the level vocabulary of the alternating `𝒬`-process (`altQ0Level`, `altQLevel`,
  `altE0Level`, `altELevel`, `altEDecay`, `altQvA`, `altQvB`, `cQVAlt`, `altC4`, `altC4e`,
  `altShiftTerm`, `assembledRHSAlt`, `AltELevelsAt`);
* Section 2: the deterministic kernel-start shift `𝒰_{u,w} X` versus `𝒰_{u',w} X`;
* Section 3: the compositions of results from other files (the envelope `gridDriftQN_envelope`, the shifted
  kernel `altQ_hker_shift`, `altQvShift_eventually`, the sub-Gaussian stopping `subGaussStop_alt`,
  `altEnd_identity`, `altCrude_grid`, `altEnd_driftQ_sum`, `cQVAlt_sum_pos`, `altEnd_yMomentsMax`).

The assembly, the four hypotheses and `altGridEnd_of_pins` are in `RBM2D.Induction.AltEnd`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Level vocabulary -/

/-- The level of the `ℚ`-part initial tensor `𝒬_s B_0` at the time `s` (`AltLevelsQ`, part (a)):
`W^{2(k-1)τ'} M_s^{-k} + W^{-D_b}`. -/
def altQ0Level (L W : ℕ) (E s : ℝ) (k : ℕ) (τ' Db : ℝ) : ℝ :=
  (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (scaleM L W E s ^ k)⁻¹ + (W : ℝ) ^ (-Db)

/-- The per-time level of `𝒬_u B_m`, `m = 1..5` (`AltLevelsQ`, part (b)):
`Φ W^{2(k-1)τ'} M_u^{-k} η_u^{-1} + W^{-D_b}`. -/
def altQLevel (L W : ℕ) (E : ℝ) (k : ℕ) (τ' Db Φ u : ℝ) : ℝ :=
  Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) +
    (W : ℝ) ^ (-Db)

/-- The deterministic level of the initial `𝔼` tensor `𝒬_s 𝔼 B_0` (`AltLevelsE`):
`N^{ε_E}` times the `ℚ` level (`≺ ⇒ 𝔼`). -/
def altE0Level (n : ℕ) (E s : ℕ → ℝ) (k : ℕ) (τ' Db εE : ℝ) : ℝ :=
  ((d.size n : ℕ) : ℝ) ^ εE * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db

/-- The deterministic level of the `𝔼` drift `Σ_{m=1}^4 𝒬_u 𝔼 B_m - 𝒬_u 𝔼 B_5` at the time `u`. -/
def altELevel (n : ℕ) (E : ℕ → ℝ) (k : ℕ) (τ' Db εE Φ u : ℝ) : ℝ :=
  5 * (((d.size n : ℕ) : ℝ) ^ εE * altQLevel (d.L n) (d.W n) (E n) k τ' Db Φ u)

/-- The decay level (far labels) of the `𝔼` tensors. -/
def altEDecay (n : ℕ) (Db εE : ℝ) : ℝ := ((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db)

/-- The constant `A` of the quadratic-variation shape of the `𝒬` process
(`qvFormQN_bound_le_qvShape`). -/
def altQvA (L W k : ℕ) (𝔠 τ' : ℝ) : ℝ :=
  cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) *
    (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ'))

/-- The constant `B` of the quadratic-variation shape of the `𝒬` process. -/
def altQvB (L k : ℕ) (Mmax : ℝ) : ℝ :=
  cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * (2 + Mmax)

/-- The sub-Gaussian proxy of the `j`-th propagated increment of the `𝒬` process towards the
target `u_m`: `Δ · k · NonAltBudget_qvShape(u_{j+1}, u_m)`. -/
def cQVAlt (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (𝔠 τ' Dq C' G Mmax : ℝ) (m : ℕ)
    (_a : Fin k → Z2 (d.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * NonAltBudget_qvShape (d.L n) (d.W n) (E n) k
    (altQvA (d.L n) (d.W n) k 𝔠 τ') (altQvB (d.L n) k Mmax) G
    ((d.W n : ℝ) ^ (-Dq + C')) (gridTime s v K n (j + 1)) (gridTime s v K n m))).toNNReal


/-- The Case 4 constant `C₄ = c_4(k) (1 + log L)^{k+1} K_w^{2k}` with `K_w = W^{τ'}` (`kapQ4`). -/
def altC4 (L W k : ℕ) (τ' : ℝ) : ℝ :=
  cCase4 k * (1 + Real.log L) ^ (k + 1) * ((W : ℝ) ^ τ') ^ (2 * k)

/-- The second Case 4 constant `c_4(k) ((1 + log L) L²)^k` (`epsQ4`). -/
def altC4e (L k : ℕ) : ℝ := cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k

/-- The kernel-start shift budget per step (`AltEndCompose_ugen_shift_le` with `‖X_j‖ ≤ 10 N^{4k+7}`,
`((1-u_{j+1})/(1-u_K))^k ≤ N^k`, `(u_{j+1}-u_j)/(1-u_{j+1}) ≤ Δ N`):
`(K Δ) · N^k ((1 + Δ N)^k - 1) · 10 N^{4k+7}`. -/
def altShiftTerm (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Nn : ℝ) : ℝ :=
  ((K n : ℝ) * gridStep s v K n) *
    (Nn ^ k * ((1 + gridStep s v K n * Nn) ^ k - 1) * (10 * Nn ^ (4 * k + 7)))

/-- **The right side of the assembled bound of the `𝒬` process at `m = K n`** (the analogue of
`assembledRHSNonAlt`), the sum of eight terms:

1. the `ℚ` initial term (`altQPartGridT`, first conclusion, level `Λ₀` at `s` only);
2. the `ℚ` drift terms (`altQPartGridT`, second conclusion, per-time level `5 Λq(u_j)`, with the
   Duhamel factor `Δ`);
3. the kernel-start shift `altShiftTerm` (`𝒰_{u_{j+1},u_K}` versus `𝒰_{u_j,u_K}`);
4. the `𝔼` initial term of the modified process (Case 4 weights `kapQ4`, `epsQ4` at `(u_0,u_K)`);
5. the `𝔼` drift terms (the index-shifted weights `kapQ4 (u_{i-1}) (u_m)`, `epsQ4 (u_{i-1}) (u_m)`);
6. the martingale term `N^ε (Σ_j c_j)^{1/2}` with the proxy `cQVAlt`;
7. the `Y` term `N^{-D_Y}`;
8. the remainder `Σ_j (1 + (1-u_K)^{-1})^k qErrQN_j` at the envelope `B_k = N^{τ_K} η_{u_{j+1}}^{-k}`.

Parameters: `(𝔠, τ')` bandwidth exponent and window exponent, `(Dq, C')` quantifiers of the variance
form, `D_b` the decay exponent of the levels and of the `ℚ` events, `(ε_q, ε_E, ε)` the losses of
the `ℚ` events, of `≺ ⇒ 𝔼` and of Azuma, `D_Y` the `Y` decay, `G, M_max` the variance levels. -/
def assembledRHSAlt (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k]
    (𝔠 τ' Dq C' Db εq εE ε D_Y τK : ℝ) (Φ : ℕ → ℝ) (G Mmax : ℝ) (a : Fin k → Z2 (d.L n)) : ℝ :=
  (((d.size n : ℕ) : ℝ) ^ εq * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db *
      ratioR (d.L n) (E n) (s n) (gridTime s v K n (K n)) ^ k + (d.W n : ℝ) ^ (-Db)) +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (((d.size n : ℕ) : ℝ) ^ εq *
          (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (gridTime s v K n j)) *
        ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
        (d.W n : ℝ) ^ (-Db)) +
    altShiftTerm s v K n k ((d.size n : ℕ) : ℝ) +
    (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n 0) (gridTime s v K n (K n)) *
        altE0Level d n E s k τ' Db εE +
      epsQ4 (d.L n) k (gridTime s v K n 0) (gridTime s v K n (K n)) * altEDecay d n Db εE) +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n j) (gridTime s v K n (K n)) *
          altELevel d n E k τ' Db εE (Φ n) (gridTime s v K n j) +
        epsQ4 (d.L n) k (gridTime s v K n j) (gridTime s v K n (K n)) * altEDecay d n Db εE) +
    ((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax (K n) a j : ℝ)) +
    ((d.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      qErrQN d E s v K n k (((d.size n : ℕ) : ℝ) ^ τK *
        (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) j

/-- The deterministic `𝔼`-level data at one size `n` and one alternating `σ` (the conclusion of
`AltLevelsE`): sup bound and window decay of `e_0 = 𝒬_s 𝔼 B_0` at `u = s_n`, and of the
`𝔼` drift `Σ_{m=1}^4 𝒬_u 𝔼 B_m - 𝒬_u 𝔼 B_5` at every `u ∈ [s_n, v_n]`. -/
def AltELevelsAt (n : ℕ) (E s v : ℕ → ℝ) (k : ℕ) [NeZero k] (σ : Fin k → Bool)
    (τ' Db εE Φn : ℝ) : Prop :=
  (∀ b, ‖expAltQB d E n (s n) σ 0 b‖ ≤ altE0Level d n E s k τ' Db εE) ∧
    DecayWin (d.L n) (ellT (d.L n) (s n) * (d.W n : ℝ) ^ τ') (altEDecay d n Db εE)
      (expAltQB d E n (s n) σ 0) ∧
    ∀ u : ℝ, s n ≤ u → u ≤ v n →
      (∀ b, ‖expDriftQN d E n u σ b‖ ≤ altELevel d n E k τ' Db εE Φn u) ∧
      DecayWin (d.L n) (ellT (d.L n) u * (d.W n : ℝ) ^ τ') (altEDecay d n Db εE)
        (expDriftQN d E n u σ)

/-! ## 2. The deterministic kernel-start shift `𝒰_{u,w} X` versus `𝒰_{u',w} X`

Elementary row-sum and tensor bounds (prefix `AltEndCompose_`) and `xiRowBound` give the shift
estimate `AltEndCompose_ugen_shift_le`. -/

section Shift

variable {L : ℕ} [NeZero L]

private def AltEndCompose_Tens {k : ℕ} (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin k → Z2 L) → ℂ)
    (x : Fin k → Z2 L) : ℂ :=
  ∑ y : Fin k → Z2 L, (∏ i, U i (x i) (y i)) * A y

private theorem AltEndCompose_Tens_zero (U : Fin 0 → Matrix (Z2 L) (Z2 L) ℂ) (A : (Fin 0 → Z2 L) → ℂ)
    (x : Fin 0 → Z2 L) : AltEndCompose_Tens U A x = A x := by
  unfold AltEndCompose_Tens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem AltEndCompose_Tens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Z2 L) (Z2 L) ℂ)
    (A : (Fin (k + 1) → Z2 L) → ℂ) (x : Fin (k + 1) → Z2 L) :
    AltEndCompose_Tens U A x = ∑ y0 : Z2 L, U 0 (x 0) y0 *
      AltEndCompose_Tens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold AltEndCompose_Tens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Z2 L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem AltEndCompose_row_mul {P : Matrix (Z2 L) (Z2 L) ℂ} {r m : ℝ}
    (hP : ∀ x : Z2 L, ∑ c : Z2 L, ‖P x c‖ ≤ r) (x : Z2 L) {f : Z2 L → ℂ}
    (hf : ∀ c, ‖f c‖ ≤ m) : ‖∑ c : Z2 L, P x c * f c‖ ≤ r * m := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hf x)
  calc ‖∑ c : Z2 L, P x c * f c‖ ≤ ∑ c : Z2 L, ‖P x c * f c‖ := norm_sum_le _ _
    _ = ∑ c : Z2 L, ‖P x c‖ * ‖f c‖ := by simp only [norm_mul]
    _ ≤ ∑ c : Z2 L, ‖P x c‖ * m :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _)
    _ = (∑ c : Z2 L, ‖P x c‖) * m := (Finset.sum_mul _ _ _).symm
    _ ≤ r * m := mul_le_mul_of_nonneg_right (hP x) hm

private theorem AltEndCompose_row_one_add {e : Matrix (Z2 L) (Z2 L) ℂ} {a : ℝ}
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

private theorem AltEndCompose_one_add_mul (e : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) (f : Z2 L → ℂ) :
    ∑ c : Z2 L, (1 + e) x c * f c = f x + ∑ c : Z2 L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

private theorem AltEndCompose_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Z2 L) (Z2 L) ℂ),
      (∀ i x, ∑ c : Z2 L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Z2 L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖AltEndCompose_Tens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [AltEndCompose_Tens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Z2 L) (Z2 L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Z2 L, ∑ c : Z2 L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact AltEndCompose_row_one_add (fun x'' => hU 0 x'') x'
      set T : Z2 L → ℂ := fun y0 => AltEndCompose_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Z2 L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : AltEndCompose_Tens U A x - A x =
          ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, e (x 0) c * Y c := by
        rw [AltEndCompose_Tens_succ, hAx]
        have h1 : ∑ c : Z2 L, U 0 (x 0) c * T c =
            ∑ c : Z2 L, U 0 (x 0) c * (T c - Y c) + ∑ c : Z2 L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Z2 L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Z2 L, e (x 0) c * Y c := by
          rw [hU0]; exact AltEndCompose_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        AltEndCompose_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Z2 L, e (x 0) c * Y c‖ ≤ a * M :=
        AltEndCompose_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Z2 L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Z2 L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

private theorem AltEndCompose_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (b : Bool) : ‖KLoop.mSig E b‖ = 1 := by
  cases b <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

/-- Row sums of `𝒰_{v,w} - 1` (one slot): `≤ (w - v)/(1 - w)` (`ukerMat = xiMat + 1`,
`xiRowBound`). -/
private theorem AltEndCompose_row_U_sub_one (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hw : w < 1) (a : Z2 L) :
    ∑ c : Z2 L, ‖(ukerMat L ξ v w - 1) a c‖ ≤ (w - v) / (1 - w) := by
  have h := xiRowBound L hL ξ hξ v w hv hvw hw a
  have e : ∀ c, (ukerMat L ξ v w - 1) a c = xiMat L ξ v w a c := fun c => by
    rw [Matrix.sub_apply, KernelExpand_ukerMat_apply]; ring
  simp_rw [e]
  exact h

/-- **One step of `𝒰` is a first-order perturbation of the identity**:
`‖𝒰_{u,u'} A - A‖_∞ ≤ ((1 + (u'-u)/(1-u'))^k - 1) ‖A‖_∞`. -/
theorem AltEndCompose_ugen_sub_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {u u' : ℝ} (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' < 1)
    {A : (Fin k → Z2 L) → ℂ} {M : ℝ} (hA : ∀ b, ‖A b‖ ≤ M) (x : Fin k → Z2 L) :
    ‖Ugen L E σ u u' A x - A x‖ ≤ ((1 + (u' - u) / (1 - u')) ^ k - 1) * M := by
  have ha : 0 ≤ (u' - u) / (1 - u') := div_nonneg (by linarith) (by linarith)
  have key := AltEndCompose_tens_sub_le (L := L) ha k
    (fun i : Fin k => ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u u')
    (fun i x' => AltEndCompose_row_U_sub_one hL (by
      rw [norm_mul, AltEndCompose_norm_mSig hE, AltEndCompose_norm_mSig hE]; norm_num) hu huu hu' x') A M hA x
  exact key

/-- **The kernel-start shift** (the kernel start moves from `u_j` to `u_{j+1}`): for `0 ≤ u ≤ u' ≤ w < 1`,
`|(𝒰_{u',w} X)_a - (𝒰_{u,w} X)_a| ≤ ((1-u')/(1-w))^k ((1 + (u'-u)/(1-u'))^k - 1) ‖X‖_∞`. -/
theorem AltEndCompose_ugen_shift_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) {u u' w : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu'w : u' ≤ w) (hw : w < 1)
    {X : (Fin k → Z2 L) → ℂ} {M : ℝ} (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Z2 L) :
    ‖Ugen L E σ u' w X a - Ugen L E σ u w X a‖ ≤
      ((1 - u') / (1 - w)) ^ k * (((1 + (u' - u) / (1 - u')) ^ k - 1) * M) := by
  have hu'0 : 0 ≤ u' := hu.trans huu'
  have hu'1 : u' < 1 := hu'w.trans_lt hw
  have hw0 : 0 ≤ w := hu'0.trans hu'w
  have hcomp := GridDuhamelN_Ugen_comp L hL hE σ (u := u) hu'0 hu'1 hw0 hw X
  have e : Ugen L E σ u' w X a - Ugen L E σ u w X a =
      Ugen L E σ u' w (fun b => X b - Ugen L E σ u u' X b) a := by
    rw [AltDriftQ_Ugen_sub, ← hcomp]
  rw [e]
  exact AltDriftQ_Ugen_norm_le hL hE σ hu'0 hu'w hw (M := ((1 + (u' - u) / (1 - u')) ^ k - 1) * M)
    (fun b => by
      rw [norm_sub_rev]
      exact AltEndCompose_ugen_sub_le hL hE σ hu huu' hu'1 hX b) a

end Shift

/-! ## 3. Compositions of results from other files -/

section Compositions

variable {d}

/-- **The envelope of the `𝒬`-remainder** (the `𝒬`-analogue of
`gridDriftN_envelope`): `exists_norm_Kcal_le_win` supplies
`B_k = N^{τ_K} η_{u_{j+1}}^{-k}` in `gridDriftQN`, so `‖rGridQN_j‖ ≤ qErrQN_j` a.e., for every grid
step `j < K n` and every label at once. -/
theorem gridDriftQN_envelope (κ : ℝ) (hκ : 0 < κ) (k : ℕ) [NeZero k] (hk : 2 ≤ k) (τK : ℝ)
    (hτK : 0 < τK) {E s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : SizeTendsto d)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP d), ∀ j, j < K n → ∀ a : Fin k → Z2 (d.L n),
      ‖rGridQN d E s t K n σ j ω a‖ ≤
        qErrQN d E s t K n k (((d.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) j := by
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  filter_upwards [hsizeN.eventually (exists_norm_Kcal_le_win κ hκ k τK hτK)] with n hn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hK1 : gridTime s t K n (j + 1) ≤ t n := by
      have h := GoodEvent_gridTime_mono (K := K) (hst n) (show j + 1 ≤ K n by omega)
      rwa [gridTime_last s t K n (hK0 n)] at h
    have hv1 : gridTime s t K n (j + 1) < 1 := hK1.trans_lt (ht1 n)
    have hη : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos (hE2 n) hv1
    have hBk : 0 ≤ ((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _)
    have hN : d.W n ^ 2 * d.L n ^ 2 = d.size n := by
      rw [Sizes.size_eq]
    have h := gridDriftQN d E s t K hE2 hs0 hst ht1 hK0 n j hj k hk σ _ hBk (by
      intro w hw J hJ h2 hJk
      exact hn (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) hN (E n) (hE n) w
        (gridTime s t K n (j + 1)) hw.1 hw.2 hv1 J hJ h2 hJk)
    exact h.mono fun ω hω _ a => hω a
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- `ρ_{s,t} = R_{s,t}` (the factor `Im m` cancels), as the private
`AltBudgetTerms_ratioR_eq_rhoR`. -/
theorem AltEndCompose_ratioR_eq_rhoR {L : ℕ} {E s t : ℝ} (hE : |E| < 2) : ratioR L E s t = rhoR L s t := by
  have hI : (RBM.Gauss.spectralM E).im ≠ 0 := (RBM.Gauss.spectralM_im_pos hE).ne'
  unfold ratioR rhoR etaT
  rw [← mul_assoc, ← mul_assoc]
  exact mul_div_mul_right _ _ hI

/-- **`ρ_{s,t}` is nonincreasing in `s`** (`M` is antitone, `scaleM_anti_ratio`): the comparison
`κ(i,m) := kapQ4(u_{i-1},u_m) ≥ kapQ4(u_i,u_m)` for the index shift of the `𝔼`-part drift budget. -/
theorem AltEndCompose_rhoR_anti {L W : ℕ} [NeZero L] [NeZero W] {E s s' t : ℝ} (hE : |E| < 2)
    (hss' : s ≤ s') (hs't : s' ≤ t) (ht : t < 1) : rhoR L s' t ≤ rhoR L s t := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hs'1 : s' < 1 := hs't.trans_lt ht
  have hMt := scaleM_pos hLp hWp hE ht
  have hle := (scaleM_anti_ratio (L := L) (W := W) hLp hE hss' hs'1).1
  rw [← AltEndCompose_ratioR_eq_rhoR hE, ← AltEndCompose_ratioR_eq_rhoR hE,
    MLExpVocab_ratioR_eq (Nat.pos_of_ne_zero (NeZero.ne W)) E s' t,
    MLExpVocab_ratioR_eq (Nat.pos_of_ne_zero (NeZero.ne W)) E s t]
  exact div_le_div_of_nonneg_right hle hMt.le

theorem AltEndCompose_rhoR_nonneg {L : ℕ} [NeZero L] {s t : ℝ} (hs : s < 1) (ht : t < 1) :
    0 ≤ rhoR L s t := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hls := (ellT_pos_le hLp hs).1
  have hlt := (ellT_pos_le hLp ht).1
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold rhoR
  positivity

/-- **The field `hker` for alternating `σ` with the index shift** `κ(i,m) :=
kapQ4(u_{i-1},u_m)`, `ε(i,m) := epsQ4(u_{i-1},u_m)`: `altQ_hker` and the comparison `kapQ4(u_i,u_m) ≤ kapQ4(u_{i-1},u_m)`. -/
theorem altQ_hker_shift {k : ℕ} [NeZero k] (hk : 2 ≤ k) {L W : ℕ} [NeZero L] [NeZero W]
    (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {σ : Fin k → Bool} (hσ : Alternating σ) {K : ℕ}
    {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m)
    (hu1 : ∀ i ≤ K, u i < 1) {Kw : ℝ} (hKw : 1 ≤ Kw) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Z2 L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → AltCase4Cls L u Kw i δ X → ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ (u i) (u m) X a‖ ≤
        kapQ4 L k Kw (u (i - 1)) (u m) * M + epsQ4 L k (u (i - 1)) (u m) * δ := by
  intro i m him hmK X M δ hM hδ hX hcls a
  have h := altQ_hker hk hL hE.le hσ hu0 hmono hu1 hKw i m him hmK X M δ hM hδ hX hcls a
  refine h.trans ?_
  have him1 : i - 1 ≤ i := Nat.sub_le i 1
  have hi1 : i - 1 ≤ K := him1.trans (him.trans hmK)
  have hmo : u (i - 1) ≤ u i := hmono _ _ him1 (him.trans hmK)
  have hC4 : 0 ≤ cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) := by
    have h1 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
    have h2 : 0 ≤ Kw ^ (2 * k) := by rw [pow_mul]; positivity
    have h3 : 0 ≤ cCase4 k := by unfold cCase4 cProp5; positivity
    positivity
  have hrho := AltEndCompose_rhoR_anti (L := L) (W := W) hE hmo (hmono i m him hmK) (hu1 m hmK)
  have hrho0 : 0 ≤ rhoR L (u i) (u m) := AltEndCompose_rhoR_nonneg (hu1 i (him.trans hmK)) (hu1 m hmK)
  have hk1 : kapQ4 L k Kw (u i) (u m) ≤ kapQ4 L k Kw (u (i - 1)) (u m) := by
    unfold kapQ4
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho0 hrho k) hC4
  have hk2 : epsQ4 L k (u i) (u m) ≤ epsQ4 L k (u (i - 1)) (u m) := by
    unfold epsQ4
    have h1m : 0 < 1 - u m := by linarith [hu1 m hmK]
    have h1i : 0 < 1 - u i := by linarith [hu1 i (him.trans hmK)]
    have hq : (1 - u i) / (1 - u m) ≤ (1 - u (i - 1)) / (1 - u m) :=
      div_le_div_of_nonneg_right (by linarith) h1m.le
    have hq0 : 0 ≤ (1 - u i) / (1 - u m) := by positivity
    have h3 : 0 ≤ cCase4 k := by unfold cCase4 cProp5; positivity
    have h4 : 0 ≤ cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k := by
      have h1 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq k) h4
  have hM0 := hM
  gcongr

/-- **The variance form of the `𝒬` process after the spectral-time shift**, at one size `N`:
for `M ∈ GoodSetN(u)` and `0 ≤ u ≤ u' ≤ w < 1`, if `W^{-D'} + eeShiftErr(u,u') ≤ W^{-D_q}`, then
`qvFormQN_{u',w}(M) ≤ NonAltBudget_qvShape(A, B, G, W^{-D_q+C'}; u', w)` (the `𝒬` analogue of
`qvFormN_le_of_goodSet_shiftN`; the entrywise level of `𝔼 ⊗ 𝔼` at
`u'` is `Mee = Γ²Λ M_u^{-2k}η_u^{-1} + W^{-D_q}`, absorbed by the caller's `G`, `Mmax`). -/
def AltQvShiftAt (k : ℕ) [NeZero k] (𝔠 τ' Dq C' : ℝ) (N : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N → (N : ℝ) ^ 𝔠 ≤ W →
    ∀ (E u u' w Γ Λ Φ D' G Mmax : ℝ), |E| < 2 → 0 ≤ u → u ≤ u' → u' ≤ w → w < 1 →
    ∀ σ : Fin k → Bool, (∀ i : Fin k, σ i ≠ σ (i + 1)) → 0 ≤ Γ → 0 ≤ Λ → 0 ≤ G →
    (W : ℝ) ^ (-D') + eeShiftErr L W E k u u' ≤ (W : ℝ) ^ (-Dq) →
    Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-Dq) ≤
      G * ((scaleM L W E u' ^ (2 * k))⁻¹ * (etaT E u')⁻¹) →
    Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-Dq) ≤ Mmax →
    ∀ M ∈ GoodSetN L W E u k Γ Λ Φ τ' D', ∀ a : Fin k → Z2 L,
      qvFormQN L W E u' w σ M a ≤
        NonAltBudget_qvShape L W E k (altQvA L W k 𝔠 τ') (altQvB L k Mmax) G
          ((W : ℝ) ^ (-Dq + C')) u' w

theorem altQvShift_eventually (𝔠 : ℝ) (h𝔠 : 0 < 𝔠) (k : ℕ) [NeZero k] (hk : 2 ≤ k) (τ' : ℝ)
    (hτ' : 0 < τ') :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ Dq : ℝ, C' < Dq → ∀ᶠ N : ℕ in atTop, AltQvShiftAt k 𝔠 τ' Dq C' N := by
  obtain ⟨C', hC', hbd⟩ := qvFormQN_le_of_bounds 𝔠 h𝔠 k hk τ' hτ'
  refine ⟨C', hC', fun Dq hDq => ?_⟩
  filter_upwards [hbd Dq hDq] with N hN
  intro L W _ _ hL hNLW hNc E u u' w Γ Λ Φ D' G Mmax hE hu0 huu' hu'w hw1 σ hσ hΓ hΛ hG hδ
    hMeeG hMeeM M hM a
  have hMh : M.IsHermitian := hM.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hLp : 1 ≤ L := by omega
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWp
  have hu1 : u < 1 := (huu'.trans hu'w).trans_lt hw1
  have hu'1 : u' < 1 := hu'w.trans_lt hw1
  have hu'0 : 0 ≤ u' := hu0.trans huu'
  have hshift := fun b b' => (norm_eeN_shiftN_le hL hE hMh huu' hu'1 σ b b')
  have hLK : ellT L u ≤ ellT L u' := (ellT_mono_ratio hLp hu0 huu' hu'1).1
  have hWτ : 0 ≤ (W : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hMee0 : 0 ≤ Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) +
      (W : ℝ) ^ (-Dq) := by
    have hMu := scaleM_pos hLp hWp hE hu1
    have hηu := etaT_pos hE hu1
    have hWD : 0 ≤ (W : ℝ) ^ (-Dq) := Real.rpow_nonneg hW0.le _
    have hG0 : 0 ≤ Γ * (Γ * Λ) := mul_nonneg hΓ (mul_nonneg hΓ hΛ)
    positivity
  have hent : ∀ b b' : Fin k → Z2 L, ‖eeN L W E u' M σ b b'‖ ≤
      Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-Dq) := by
    intro b b'
    have h1 := hD4 σ b b'
    have h2 := hshift b b'
    have h3 : ‖eeN L W E u' M σ b b'‖ ≤ ‖eeN L W E u M σ b b'‖ +
        ‖eeN L W E u' M σ b b' - eeN L W E u M σ b b'‖ := by
      have := norm_add_le (eeN L W E u M σ b b') (eeN L W E u' M σ b b' - eeN L W E u M σ b b')
      rwa [add_sub_cancel] at this
    linarith
  have hdec : HasDecay2 L W u' τ' Dq (eeN L W E u' M σ) := by
    intro b b' hfar
    have hfar' : ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L (Fin.append b b') : ℝ) :=
      (mul_le_mul_of_nonneg_right hLK hWτ).trans hfar
    have h1 := hVb σ b b' hfar'
    have h2 := hshift b b'
    have h3 : ‖eeN L W E u' M σ b b'‖ ≤ ‖eeN L W E u M σ b b'‖ +
        ‖eeN L W E u' M σ b b' - eeN L W E u M σ b b'‖ := by
      have := norm_add_le (eeN L W E u M σ b b') (eeN L W E u' M σ b b' - eeN L W E u M σ b b')
      rwa [add_sub_cancel] at this
    linarith
  have hq := hN L W hL hNLW hNc E u' w hE hu'0 hu'w hw1 σ hσ M _ hMee0 hent hdec a
  refine hq.trans ?_
  exact qvFormQN_bound_le_qvShape L W k 𝔠 τ' Dq C' E u' w G _ Mmax h𝔠 hτ'.le hG hMee0 hMeeG hMeeM
    hu'0 hu'w hw1

/-- `η_{u'} ≤ η_u` for `u ≤ u'` (the private `NonAltGood_etaT_anti`). -/
theorem AltEndCompose_etaT_anti {E : ℝ} (hE : |E| < 2) {u u' : ℝ} (hu : u ≤ u') :
    etaT E u' ≤ etaT E u := by
  unfold etaT
  have := (spectralM_im_pos hE).le
  nlinarith

/-- The level `M_u^{-p} η_u^{-1}` is nondecreasing in `u`. -/
theorem AltEndCompose_lvl_mono {L W : ℕ} [NeZero L] [NeZero W] {E u u' : ℝ} (hE : |E| < 2)
    (hu : u ≤ u') (hu' : u' < 1) (p : ℕ) :
    (scaleM L W E u ^ p)⁻¹ * (etaT E u)⁻¹ ≤ (scaleM L W E u' ^ p)⁻¹ * (etaT E u')⁻¹ := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hu1 : u < 1 := hu.trans_lt hu'
  have hMu := scaleM_pos hLp hWp hE hu1
  have hMu' := scaleM_pos hLp hWp hE hu'
  have hηu := etaT_pos hE hu1
  have hηu' := etaT_pos hE hu'
  have hMle : scaleM L W E u' ≤ scaleM L W E u := (scaleM_anti_ratio hLp hE hu hu').1
  have hpow : (scaleM L W E u ^ p)⁻¹ ≤ (scaleM L W E u' ^ p)⁻¹ :=
    inv_anti₀ (pow_pos hMu' _) (pow_le_pow_left₀ hMu'.le hMle _)
  have hinv : (etaT E u)⁻¹ ≤ (etaT E u')⁻¹ := inv_anti₀ hηu' (AltEndCompose_etaT_anti hE hu)
  exact mul_le_mul hpow hinv (inv_nonneg.2 hηu.le) (inv_nonneg.2 (pow_pos hMu' _).le)

/-- **The majorant `hQ`** for the sub-Gaussian input of the `𝒬` process: for `M ∈ GoodSetN(u_j)` Hermitian,
`Δ · (k · qvFormQN_{u_{j+1},u_m}(M)) ≤ cQVAlt` under the size-`n` case of `AltQvShiftAt`, the
shift hypothesis `hδ` and the two level comparisons. -/
theorem hQ_alt {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) [NeZero k] {σ : Fin k → Bool} (hσ : Alternating σ) (Γ Λ Φ : ℕ → ℝ)
    (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (𝔠 τ' D' Dq C' G Mmax : ℝ) (hG : 0 ≤ G) (m : ℕ)
    (hm : m ≤ K n) (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m)
    (hN : AltQvShiftAt k 𝔠 τ' Dq C' (d.size n)) (hNc : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ d.W n)
    (hδ : (d.W n : ℝ) ^ (-D') + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-Dq))
    (hMeeG : Γ n * (Γ n * Λ n) * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤
      G * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n (j + 1)))⁻¹))
    (hMeeM : Γ n * (Γ n * Λ n) * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤ Mmax) :
    ∀ M ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormQN (d.L n) (d.W n) (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤
        (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax m a j : ℝ) := by
  intro M hM _
  have hΔ : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hu0 : 0 ≤ gridTime s v K n j := GoodEvent_gridTime_nonneg (hs0 n) (hsv n) j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    GoodEvent_gridTime_mono (hsv n) (by omega)
  have hj1m : gridTime s v K n (j + 1) ≤ gridTime s v K n m :=
    GoodEvent_gridTime_mono (hsv n) (by omega)
  have hw1 : gridTime s v K n m < 1 := (GoodEvent_gridTime_le (K := K) (hsv n) hm).trans_lt (hv1 n)
  have hσ' : ∀ i : Fin k, σ i ≠ σ (i + 1) := fun i => by rw [hσ i]; cases σ i <;> simp
  have hNLW : (d.W n) ^ 2 * (d.L n) ^ 2 = d.size n := by rw [Sizes.size_eq]
  have hq := hN (d.L n) (d.W n) (d.three_le_L n) hNLW hNc (E n) _ _ _ (Γ n) (Λ n) (Φ n) D' G Mmax
    (hE n) hu0 hjj hj1m hw1 σ hσ' hΓ hΛ hG hδ hMeeG hMeeM M hM a
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **The `SubGaussStopN` input of `AssembledN` for the `𝒬` process**:
`azumaSubGQ_goodExit` with the proxy `cQVAlt` and the majorant `hQ_alt`. -/
theorem subGaussStop_alt {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) {σ : Fin k → Bool} (hσ : Alternating σ) (Γ Λ Φ : ℕ → ℝ)
    (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (𝔠 τ' D' Dq C' G Mmax : ℝ) (hG : 0 ≤ G) (m : ℕ)
    (hm : m ≤ K n) (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m)
    (hN : AltQvShiftAt k 𝔠 τ' Dq C' (d.size n)) (hNc : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ d.W n)
    (hδ : (d.W n : ℝ) ^ (-D') + eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ (d.W n : ℝ) ^ (-Dq))
    (hMeeG : Γ n * (Γ n * Λ n) * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤
      G * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n (j + 1)))⁻¹))
    (hMeeM : Γ n * (Γ n * Λ n) * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤ Mmax) :
    SubGaussStopN d (E n) σ (gridTime s v K n) (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
      (fun j ω => zVecQN d E s v K n j σ ω) m a j (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax m a j) :=
  azumaSubGQ_goodExit d hE hs0 hsv hv1 n k hk σ Γ Λ Φ τ' D' m hm a j hj _
    (hQ_alt hE hs0 hsv hv1 n k hσ Γ Λ Φ hΓ hΛ 𝔠 τ' D' Dq C' G Mmax hG m hm a j hj hN hNc hδ hMeeG
      hMeeM)

/-- **The pathwise decomposition of the `𝒬` process at the grid end** (the "modified
process"): from `stoppedDuhamelQN` with the constant stopping index `τ ≡ K n` and `m = K n`, and
`martIncQN_j = zVecQN_j + yVecQN_j`,
`A^Q_K = 𝒰_{u_0,u_K}(A^Q_0 - e_0) + Σ_j 𝒰_{u_{j+1},u_K}(Δ (dGridQN_j - e^D_j)) + Ã_K`,
`Ã_K = 𝒰_{u_0,u_K} e_0 + Σ_j 𝒰_{u_{j+1},u_K}(Δ e^D_j + Z_j + Y_j + R_j)`
(`e_0 = expAltQB(s,0)`, `e^D_j = expDriftQN(u_j)`). -/
theorem altEnd_identity {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (ω : PathΩ d)
    (hmart : ∀ j < K n, ∀ a, martIncQN d E s v K n σ j ω a =
      zVecQN d E s v K n j σ ω a + yVecQN d E s v K n j σ ω a) (a : Fin k → Z2 (d.L n)) :
    aTrueQN d E s v K n σ (K n) ω a =
      Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
          (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a +
        ∑ j ∈ Finset.range (K n), Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
          (gridTime s v K n (K n))
          (fun b => (gridStep s v K n : ℂ) * (dGridQN d E s v K n σ j ω b -
            expDriftQN d E n (gridTime s v K n j) σ b)) a +
        (Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
            (expAltQB d E n (s n) σ 0) a +
          ∑ j ∈ Finset.range (K n), Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
            (gridTime s v K n (K n))
            ((gridStep s v K n : ℂ) • expDriftQN d E n (gridTime s v K n j) σ +
              zVecQN d E s v K n j σ ω + yVecQN d E s v K n j σ ω +
              rGridQN d E s v K n σ j ω) a) := by
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hΔ0 := GoodEvent_gridStep_nonneg (K := K) (hsv n)
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => GoodEvent_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) (hsv n) hi).trans_lt (hv1 n)
  have hD := stoppedDuhamelQN d E s v K hE hs0 hsv hv1 hK0 n k σ (fun _ => K n) (K n) ω le_rfl
  have hfroz : aFrozQN d E s v K n σ (fun _ => K n) (K n) ω = aTrueQN d E s v K n σ (K n) ω := by
    unfold aFrozQN
    simp only [min_self]
    exact GridDuhamelN_Ugen_self (d.L n) hL3 (hE n).le σ (hu0 _) (hu1 _ le_rfl) _
  rw [hfroz] at hD
  rw [congrFun hD a]
  simp only [min_self, Pi.add_apply, Finset.sum_apply]
  have h0 : Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
      (aTrueQN d E s v K n σ 0 ω) a =
      Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
        (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a +
      Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
        (expAltQB d E n (s n) σ 0) a := by
    have hfun : aTrueQN d E s v K n σ 0 ω =
        (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) +
          expAltQB d E n (s n) σ 0 := by
      funext b; simp
    conv_lhs => rw [hfun]
    rw [GridDuhamelN_Ugen_add]
    rfl
  have hj : ∀ j ∈ Finset.range (K n),
      Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n))
        ((gridStep s v K n : ℂ) • dGridQN d E s v K n σ j ω + martIncQN d E s v K n σ j ω +
          rGridQN d E s v K n σ j ω) a =
      Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n))
        (fun b => (gridStep s v K n : ℂ) * (dGridQN d E s v K n σ j ω b -
          expDriftQN d E n (gridTime s v K n j) σ b)) a +
      Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n))
        ((gridStep s v K n : ℂ) • expDriftQN d E n (gridTime s v K n j) σ +
          zVecQN d E s v K n j σ ω + yVecQN d E s v K n j σ ω + rGridQN d E s v K n σ j ω) a := by
    intro j hjK
    have hjK' := Finset.mem_range.1 hjK
    have hfun : ((gridStep s v K n : ℂ) • dGridQN d E s v K n σ j ω +
          martIncQN d E s v K n σ j ω + rGridQN d E s v K n σ j ω) =
        (fun b => (gridStep s v K n : ℂ) * (dGridQN d E s v K n σ j ω b -
          expDriftQN d E n (gridTime s v K n j) σ b)) +
        ((gridStep s v K n : ℂ) • expDriftQN d E n (gridTime s v K n j) σ +
          zVecQN d E s v K n j σ ω + yVecQN d E s v K n j σ ω + rGridQN d E s v K n σ j ω) := by
      funext b
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hmart j hjK' b]
      ring
    rw [hfun, GridDuhamelN_Ugen_add]
    rfl
  rw [h0, Finset.sum_congr rfl hj, Finset.sum_add_distrib]
  ring

/-- `𝒰` commutes with a scalar factor. -/
theorem AltEndCompose_Ugen_smul (L : ℕ) [NeZero L] (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (v w : ℝ) (c : ℂ) (X : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Ugen L E σ v w (fun b => c * X b) a = c * Ugen L E σ v w X a := by
  unfold Ugen
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `(1-v)⁻¹ ≤ N` from `η_v⁻¹ ≤ N` (`Im m ≤ 1`; the private `NonAltBudget_inv_one_sub_le`). -/
theorem AltEndCompose_inv_one_sub_le {E v Nn : ℝ} (hE : |E| < 2) (hv1 : v < 1)
    (hη : (etaT E v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn := by
  have hη0 := etaT_pos hE hv1
  have him := MLExpVocab_im_le_one E
  have h1v : 0 < 1 - v := by linarith
  have hle : etaT E v ≤ 1 - v := by
    unfold etaT
    calc (1 - v) * (spectralM E).im ≤ (1 - v) * 1 :=
          mul_le_mul_of_nonneg_left him h1v.le
      _ = 1 - v := mul_one _
  exact (inv_anti₀ hη0 hle).trans hη

/-- **`KeyAt` at every time `u ∈ [0, v_n]`**, eventually: the deterministic facts of
`LocalFormCuts.KeyAt` at `Nr = N`, `kmax = k + 1` (`exists_norm_Kcal_le_win` with `τ_K = 1`). -/
theorem AltEndCompose_keyAt {κ : ℝ} (hκ : 0 < κ) (k : ℕ) {E v : ℕ → ℝ} (hsize : SizeTendsto d)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hv1 : ∀ n, v n < 1)
    (hη : ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      LocalFormCuts.KeyAt (d.L n) (d.W n) (E n) u ((d.size n : ℕ) : ℝ) (k + 1) := by
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  filter_upwards [hsizeN.eventually (exists_norm_Kcal_le_win κ hκ (k + 1) 1 one_pos), hη] with
    n hK hηn
  intro u hu0 huv
  have hu1 : u < 1 := huv.trans_lt (hv1 n)
  have hE2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hN : d.W n ^ 2 * d.L n ^ 2 = d.size n := by rw [Sizes.size_eq]
  have hNr : ((d.size n : ℕ) : ℝ) = ((d.W n : ℕ) : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 := by
    rw [← hN]; push_cast; ring
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  refine ⟨d.three_le_L n, d.W_pos n, GoodEvent_one_le_size n, ?_, ?_, ?_, hE2, hu0, hu1, ?_⟩
  · rw [hNr]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hW1)
  · rw [← hN]
    push_cast
    nlinarith [sq_nonneg ((d.W n : ℝ) * (d.L n : ℝ))]
  · exact (inv_anti₀ (etaT_pos hE2 (hv1 n)) (AltEndCompose_etaT_anti hE2 huv)).trans hηn
  · intro J hJ h2 hJk
    have h := hK (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) hN (E n) (hE n) u u hu0 le_rfl hu1 J
      hJ h2 hJk
    rwa [Real.rpow_one] at h

/-- **Crude pathwise bound of the `ℚ` drift tensor and of the `𝔼` drift** at every grid time:
`‖dGridQN_j‖, ‖expDriftQN(u_j)‖ ≤ 5 N^{4k+7}` (`dGridQN_eq_dFlowQ`,
`AltDriftQ_norm_altQB_le`, `AltDriftQ_integral_altQB`). -/
theorem altCrude_grid {κ : ℝ} (hκ : 0 < κ) (k : ℕ) [NeZero k] (hk : 2 ≤ k) {E s v : ℕ → ℝ}
    {K : ℕ → ℕ} (hsize : SizeTendsto d) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hη : ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → ∀ j < K n,
      (∀ (ω : PathΩ d) (b : Fin k → Z2 (d.L n)),
        ‖dGridQN d E s v K n σ j ω b‖ ≤ 5 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7)) ∧
      (∀ b : Fin k → Z2 (d.L n),
        ‖expDriftQN d E n (gridTime s v K n j) σ b‖ ≤ 5 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7)) := by
  filter_upwards [AltEndCompose_keyAt hκ k hsize hE hv1 hη,
    hsize.eventually_ge_atTop (8 * (k : ℝ) ^ 3 * LocalFormCalc.C5 ^ k)] with n hkey hNr
  intro σ hσ j hj
  have hE2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hu0 : 0 ≤ gridTime s v K n j := GoodEvent_gridTime_nonneg (hs0 n) (hsv n) j
  have hjK : j ≤ K n := hj.le
  have huv : gridTime s v K n j ≤ v n := GoodEvent_gridTime_le (K := K) (hsv n) hjK
  have hu1 : gridTime s v K n j < 1 := huv.trans_lt (hv1 n)
  have hkey' := hkey _ hu0 huv
  have hq : ∀ (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), M.IsHermitian →
      ∀ (m : Fin 6) (b : Fin k → Z2 (d.L n)), ‖altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) M σ m b‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := fun M hM m b =>
    AltDriftQ_norm_altQB_le hk hkey' hNr hM hσ m b
  have hsum5 : ∀ (f : Fin 6 → ℂ), (∀ m, ‖f m‖ ≤ ((d.size n : ℕ) : ℝ) ^ (4 * k + 7)) →
      ‖f 1 + f 2 + f 3 + f 4 - f 5‖ ≤ 5 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := by
    intro f hf
    calc ‖f 1 + f 2 + f 3 + f 4 - f 5‖ ≤ ‖f 1‖ + ‖f 2‖ + ‖f 3‖ + ‖f 4‖ + ‖f 5‖ := by
          calc _ ≤ ‖f 1 + f 2 + f 3 + f 4‖ + ‖f 5‖ := norm_sub_le _ _
            _ ≤ ‖f 1 + f 2 + f 3‖ + ‖f 4‖ + ‖f 5‖ := by gcongr; exact norm_add_le _ _
            _ ≤ ‖f 1 + f 2‖ + ‖f 3‖ + ‖f 4‖ + ‖f 5‖ := by gcongr; exact norm_add_le _ _
            _ ≤ ‖f 1‖ + ‖f 2‖ + ‖f 3‖ + ‖f 4‖ + ‖f 5‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 5 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := by
          have := hf 1; have := hf 2; have := hf 3; have := hf 4; have := hf 5
          linarith
  refine ⟨fun ω b => ?_, fun b => ?_⟩
  · rw [dGridQN_eq_dFlowQ d E s v K n k σ j ω hk hE2 hu0 hu1]
    exact hsum5 (fun m => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ m b)
      (fun m => hq _ (pathH_isHermitian d s v K n j ω) m b)
  · have hint : ∀ m : Fin 6, ‖expAltQB d E n (gridTime s v K n j) σ m b‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := by
      intro m
      rw [← AltDriftQ_integral_altQB hk hkey' hNr hσ m b]
      have h := norm_integral_le_of_norm_le_const (μ := Sizes.seqP d)
        (f := fun ω => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j)
          (Sizes.seqHflow d n (gridTime s v K n j) ω) σ m b)
        (C := ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))
        (Filter.Eventually.of_forall fun ω =>
          hq _ (Sizes.seqHflow_isHermitian d n _ ω) m b)
      simpa using h
    exact hsum5 (fun m => expAltQB d E n (gridTime s v K n j) σ m b) hint

/-- **The `ℚ` drift sum with the kernel-start shift**: the Duhamel sum
`Σ_j 𝒰_{u_{j+1},u_K}(Δ X_j)` with `X_j = dGridQN_j - e^D_j` is bounded by `Δ Σ_j (q_j + shift)`,
where `q_j ≥ |(𝒰_{u_j,u_K} X_j)_a|` (the second conclusion of `altQPartGridT`) and
`shift = N^k ((1 + Δ N)^k - 1) · 10 N^{4k+7}` (`AltEndCompose_ugen_shift_le`, the crude bound
`‖X_j‖ ≤ 10 N^{4k+7}` of `altCrude_grid`). -/
theorem altEnd_driftQ_sum {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK0 : K n ≠ 0)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ)) (ω : PathΩ d) (a : Fin k → Z2 (d.L n))
    (X : ℕ → (Fin k → Z2 (d.L n)) → ℂ)
    (hX : ∀ j < K n, ∀ b, ‖X j b‖ ≤ 10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))
    (q : ℕ → ℝ)
    (hq : ∀ j < K n, ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a‖ ≤
      q j) :
    ‖∑ j ∈ Finset.range (K n), Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
        (gridTime s v K n (K n)) (fun b => (gridStep s v K n : ℂ) * X j b) a‖ ≤
      gridStep s v K n * ∑ j ∈ Finset.range (K n), (q j +
        ((d.size n : ℕ) : ℝ) ^ k * ((1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1) *
          (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))) := by
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => GoodEvent_gridTime_nonneg hs0 hsv i
  have hlast : gridTime s v K n (K n) = v n := gridTime_last s v K n hK0
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hv : (1 - v n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) := AltEndCompose_inv_one_sub_le hE hv1 hη
  have h1v : 0 < 1 - v n := by linarith
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK := Finset.mem_range.1 hj
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := GoodEvent_gridTime_mono hsv (by omega)
  have hj1K : gridTime s v K n (j + 1) ≤ gridTime s v K n (K n) :=
    GoodEvent_gridTime_mono hsv (by omega)
  have hw1 : gridTime s v K n (K n) < 1 := by rw [hlast]; exact hv1
  have hu'1 : gridTime s v K n (j + 1) < 1 := hj1K.trans_lt hw1
  have hsmul := AltEndCompose_Ugen_smul (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n))
    (gridStep s v K n : ℂ) (X j) a
  rw [hsmul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
  refine mul_le_mul_of_nonneg_left ?_ hΔ0
  have hMX : ∀ b, ‖X j b‖ ≤ 10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := hX j hjK
  have hshift := AltEndCompose_ugen_shift_le (L := d.L n) hL3 hE.le σ (hu0 j) hjj hj1K hw1 hMX a
  -- the shift bound
  have hA1 : (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n (K n)) ≤
      ((d.size n : ℕ) : ℝ) := by
    rw [hlast]
    have h1 : 1 - gridTime s v K n (j + 1) ≤ 1 := by linarith [hu0 (j + 1)]
    calc (1 - gridTime s v K n (j + 1)) / (1 - v n) ≤ 1 / (1 - v n) :=
          div_le_div_of_nonneg_right h1 h1v.le
      _ = (1 - v n)⁻¹ := one_div _
      _ ≤ _ := hv
  have hA0 : 0 ≤ (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n (K n)) :=
    div_nonneg (by linarith) (by linarith)
  have hB1 : (gridTime s v K n (j + 1) - gridTime s v K n j) / (1 - gridTime s v K n (j + 1)) ≤
      gridStep s v K n * ((d.size n : ℕ) : ℝ) := by
    have hdiff : gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
      unfold gridTime; push_cast; ring
    rw [hdiff]
    have h1 : 0 < 1 - gridTime s v K n (j + 1) := by linarith
    have h2 : (1 - gridTime s v K n (j + 1))⁻¹ ≤ ((d.size n : ℕ) : ℝ) := by
      refine le_trans (inv_anti₀ h1v ?_) hv
      rw [hlast] at hj1K
      linarith
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h2 hΔ0
  have hB0 : 0 ≤ (gridTime s v K n (j + 1) - gridTime s v K n j) /
      (1 - gridTime s v K n (j + 1)) := div_nonneg (by linarith) (by linarith)
  have hM0 : 0 ≤ 10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := by positivity
  have hpow1 : ((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n (K n))) ^ k ≤
      ((d.size n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hA0 hA1 k
  have hpow2 : (1 + (gridTime s v K n (j + 1) - gridTime s v K n j) /
      (1 - gridTime s v K n (j + 1))) ^ k - 1 ≤
      (1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + (gridTime s v K n (j + 1) -
      gridTime s v K n j) / (1 - gridTime s v K n (j + 1))) (by linarith : 1 + (gridTime s v K n (j + 1) -
      gridTime s v K n j) / (1 - gridTime s v K n (j + 1)) ≤ 1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) k
    linarith
  have hpow0 : 0 ≤ (1 + (gridTime s v K n (j + 1) - gridTime s v K n j) /
      (1 - gridTime s v K n (j + 1))) ^ k - 1 := by
    have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + (gridTime s v K n (j + 1) -
      gridTime s v K n j) / (1 - gridTime s v K n (j + 1))) (n := k)
    linarith
  have hshift' : ‖Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) (X j) a -
      Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a‖ ≤
      ((d.size n : ℕ) : ℝ) ^ k * ((1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1) *
        (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7)) := by
    refine hshift.trans ?_
    calc ((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n (K n))) ^ k *
          (((1 + (gridTime s v K n (j + 1) - gridTime s v K n j) /
            (1 - gridTime s v K n (j + 1))) ^ k - 1) * (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7)))
        ≤ ((d.size n : ℕ) : ℝ) ^ k * (((1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1) *
            (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))) := by
          refine mul_le_mul hpow1 (mul_le_mul_of_nonneg_right hpow2 hM0) (mul_nonneg hpow0 hM0)
            (by positivity)
      _ = _ := by ring
  have htri : ‖Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) (X j) a‖ ≤
      ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a‖ +
        ‖Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) (X j) a -
          Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a‖ := by
    have := norm_add_le (Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a)
      (Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n (K n)) (X j) a -
        Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n)) (X j) a)
    rwa [add_sub_cancel] at this
  have := hq j hjK
  linarith

/-- `0 ≤ uStepC` (the private `AltGridQ_uStepC_nonneg`). -/
theorem AltEndCompose_uStepC_nonneg (k : ℕ) {Δ v : ℝ} (hΔ0 : 0 ≤ Δ) (hv1 : 0 < 1 - v) :
    0 ≤ uStepC k Δ v := by
  unfold uStepC
  have hβ0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 hv1.le
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 hβ0
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - v)⁻¹ by linarith) k
  have e1 : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
  linarith [hb, e1]

/-- `0 ≤ qStepErrN` for nonnegative data (`hstepErr0` of the bundle). -/
theorem AltEndCompose_qStepErrN_nonneg (L k : ℕ) (hk : 1 ≤ k) {u Δ Mk Dm S : ℝ} (hΔ : 0 ≤ Δ)
    (hu : u + Δ < 1) (hMk : 0 ≤ Mk) (hDm : 0 ≤ Dm) (hS : 0 ≤ S) :
    0 ≤ qStepErrN L k u Δ Mk Dm S := by
  have hU := AltEndCompose_uStepC_nonneg k hΔ (v := u + Δ) (by linarith)
  have hβ : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.2 (by linarith)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold qStepErrN
  generalize uStepC k Δ (u + Δ) = U at hU ⊢
  generalize (1 - (u + Δ))⁻¹ = β at hβ ⊢
  generalize (k : ℝ) - 1 = k1 at hk1 ⊢
  have hL : 0 ≤ ((L : ℝ) ^ 2) ^ (k - 1) := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  positivity

/-- `0 ≤ qErrQN` at the envelope `B_k ≥ 0` (`hstepErr0` of the bundle). -/
theorem AltEndCompose_qErrQN_nonneg {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (hk : 1 ≤ k)
    (hE : |E n| < 2) (hΔ0 : 0 ≤ gridStep s v K n) {j : ℕ} (hu1 : gridTime s v K n j < 1)
    (hu1' : gridTime s v K n (j + 1) < 1) {Bk : ℝ} (hBk : 0 ≤ Bk) :
    0 ≤ qErrQN d E s v K n k Bk j := by
  have hstep : gridTime s v K n j + gridStep s v K n = gridTime s v K n (j + 1) := by
    unfold gridTime; push_cast; ring
  have hη : 0 < etaT (E n) (gridTime s v K n j) := etaT_pos hE hu1
  have hS : 0 ≤ stepErrN (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
      (gridStep s v K n) Bk := NonAltEnd_stepErrN_nonneg hE hu1 hu1' hΔ0 hBk
  have hMk : 0 ≤ lkEnvN (d.W n) (E n) k (gridTime s v K n j) Bk := by
    unfold lkEnvN
    have : 0 ≤ (etaT (E n) (gridTime s v K n j))⁻¹ := inv_nonneg.2 hη.le
    positivity
  have hDm : 0 ≤ driftEnvN (d.L n) (d.W n) (E n) k (gridTime s v K n j) Bk := by
    unfold driftEnvN
    have : 0 ≤ (etaT (E n) (gridTime s v K n j))⁻¹ := inv_nonneg.2 hη.le
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    positivity
  unfold qErrQN
  exact AltEndCompose_qStepErrN_nonneg (d.L n) k hk hΔ0 (by rw [hstep]; exact hu1') hMk hDm hS

/-- `Σ_{j<m} c_j > 0` for the proxies `cQVAlt` (the field `hc_pos`, strict window `s_n < v_n`). -/
theorem cQVAlt_sum_pos {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) [NeZero k] (hE : |E n| < 2)
    (hk : 1 ≤ k) (hsv : s n < v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (𝔠 τ' Dq C' G Mmax : ℝ) (hG : 0 ≤ G) (hMmax : 0 ≤ Mmax) :
    ∀ m, 1 ≤ m → m ≤ K n → ∀ a : Fin k → Z2 (d.L n),
      0 < ∑ j ∈ Finset.range m, (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax m a j : ℝ) := by
  intro m hm1 hmK a
  have hΔ : 0 < gridStep s v K n :=
    div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hK)
  have hterm : ∀ j ∈ Finset.range m, 0 ≤ (cQVAlt d E s v K n k 𝔠 τ' Dq C' G Mmax m a j : ℝ) :=
    fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  have h1m : gridTime s v K n (0 + 1) ≤ gridTime s v K n m :=
    GoodEvent_gridTime_mono (le_of_lt hsv) (by omega)
  have hw1 : gridTime s v K n m < 1 :=
    (GoodEvent_gridTime_le (K := K) (le_of_lt hsv) hmK).trans_lt hv1
  have hu1 : gridTime s v K n (0 + 1) < 1 := h1m.trans_lt hw1
  have hLp : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWp : 1 ≤ d.W n := d.W_pos n
  have hMu := scaleM_pos hLp hWp hE hu1
  have hηu := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast hWp
  have hWd : 0 < (d.W n : ℝ) ^ (-Dq + C') := Real.rpow_pos_of_pos hW0 _
  have hlog : 0 ≤ Real.log (d.L n : ℝ) := Real.log_natCast_nonneg _
  have hc5 : 0 < cCase5 k := by unfold cCase5 cProp5; positivity
  have h1u : 0 < 1 - gridTime s v K n (0 + 1) := by linarith
  have h1w : 0 < 1 - gridTime s v K n m := by linarith
  have hLpos : (0 : ℝ) < (d.L n : ℝ) := by exact_mod_cast hLp
  have hB : 0 < altQvB (d.L n) k Mmax := by
    unfold altQvB
    have : 0 < (1 + Real.log (d.L n : ℝ)) * (d.L n : ℝ) ^ 2 := by positivity
    positivity
  have hA : 0 ≤ altQvA (d.L n) (d.W n) k 𝔠 τ' := by
    unfold altQvA
    positivity
  have hq : 0 < NonAltBudget_qvShape (d.L n) (d.W n) (E n) k (altQvA (d.L n) (d.W n) k 𝔠 τ')
      (altQvB (d.L n) k Mmax) G ((d.W n : ℝ) ^ (-Dq + C')) (gridTime s v K n (0 + 1))
      (gridTime s v K n m) := by
    unfold NonAltBudget_qvShape
    have hρ : 0 ≤ rhoR (d.L n) (gridTime s v K n (0 + 1)) (gridTime s v K n m) :=
      AltEndCompose_rhoR_nonneg hu1 hw1
    have hlvl : 0 ≤ G * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (0 + 1)) ^ (2 * k))⁻¹ *
        (etaT (E n) (gridTime s v K n (0 + 1)))⁻¹) := by positivity
    have h1 : 0 ≤ altQvA (d.L n) (d.W n) k 𝔠 τ' * rhoR (d.L n) (gridTime s v K n (0 + 1))
        (gridTime s v K n m) ^ (2 * k) *
        (G * ((scaleM (d.L n) (d.W n) (E n) (gridTime s v K n (0 + 1)) ^ (2 * k))⁻¹ *
          (etaT (E n) (gridTime s v K n (0 + 1)))⁻¹) + (d.W n : ℝ) ^ (-Dq + C')) := by
      positivity
    have h2 : 0 < altQvB (d.L n) k Mmax *
        ((1 - gridTime s v K n (0 + 1)) / (1 - gridTime s v K n m)) ^ (2 * k) *
        (d.W n : ℝ) ^ (-Dq + C') := by positivity
    linarith
  unfold cQVAlt
  rw [Real.coe_toNNReal _ (mul_nonneg hΔ.le (mul_nonneg (Nat.cast_nonneg k) hq.le))]
  exact mul_pos hΔ (mul_pos (by exact_mod_cast hk) hq)

/-- **The uniform `Y` moments of the `𝒬` increment for all signs with one `C_P`** (chosen before the
grid `K`): the maximum over the `2^k` sign vectors of the constants of `yMomentsQUnifN`
(`NonAltEnd_yMomentsMax` for the `𝒬` increment). -/
theorem altEnd_yMomentsMax {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : SizeTendsto d) (hrange : RangeCond d τR v) (k : ℕ) [NeZero k] :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin k → Bool,
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
          YMomentBoundsN d (E n) σ (gridTime s v K n) τ (K n)
            (fun j ω => yVecQN d E s v K n j σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  classical
  choose CP hCP0 hCPev using fun σ : Fin k → Bool =>
    yMomentsQUnifN d κ τR E s v hκ hE hs0 hsv hv1 hsize hrange k σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (GoodEvent_one_le_size n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

/-- `(W²L²)^{-p} ≤ M_u^{-p} η_u^{-1}` (the level is at least `N^{-p}`): `M_u ≤ W² ≤ N`, `η_u ≤ 1`. -/
theorem AltEndCompose_lvl_ge {L W : ℕ} [NeZero L] [NeZero W] {E u Nn : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hWN : (W : ℝ) ^ 2 ≤ Nn) (p : ℕ) :
    (Nn ^ p)⁻¹ ≤ (scaleM L W E u ^ p)⁻¹ * (etaT E u)⁻¹ := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hu1
  have hη := etaT_pos hE hu1
  have hMN : scaleM L W E u ≤ Nn := (MLExpVocab_scaleM_le_W2 hLp hu1).trans hWN
  have him := MLExpVocab_im_le_one E
  have hη1 : etaT E u ≤ 1 := by
    unfold etaT
    calc (1 - u) * (spectralM E).im ≤ 1 * 1 :=
          mul_le_mul (by linarith) him (spectralM_im_pos hE).le (by norm_num)
      _ = 1 := one_mul _
  have h1 : (Nn ^ p)⁻¹ ≤ (scaleM L W E u ^ p)⁻¹ :=
    inv_anti₀ (pow_pos hM p) (pow_le_pow_left₀ hM.le hMN p)
  have h2 : 1 ≤ (etaT E u)⁻¹ := one_le_inv₀ hη |>.2 hη1
  calc (Nn ^ p)⁻¹ = (Nn ^ p)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (scaleM L W E u ^ p)⁻¹ * (etaT E u)⁻¹ :=
        mul_le_mul h1 h2 zero_le_one (inv_nonneg.2 (pow_pos hM p).le)

/-- `M_u^{-p} η_u^{-1} ≤ η_u^{-1}` when `1 ≤ M_u` (the level is at most `η_u⁻¹`). -/
theorem AltEndCompose_lvl_le {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    (hM1 : 1 ≤ scaleM L W E u) (p : ℕ) :
    (scaleM L W E u ^ p)⁻¹ * (etaT E u)⁻¹ ≤ (etaT E u)⁻¹ := by
  have hη := etaT_pos hE hu1
  have h1 : (scaleM L W E u ^ p)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hM1)
  calc (scaleM L W E u ^ p)⁻¹ * (etaT E u)⁻¹ ≤ 1 * (etaT E u)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hη.le)
    _ = (etaT E u)⁻¹ := one_mul _

/-- `zVecQN` is `F_{j+1}`-strongly measurable (`𝒬_{u_{j+1}}` is a continuous linear map; the
private `AltProxyQ_stronglyMeasurable_yVecQN` for `ZvecN`). -/
theorem AltEndCompose_stronglyMeasurable_zVecQN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    [NeZero k] (σ : Fin k → Bool) :
    StronglyMeasurable[filt d (j + 1)] (fun ω => zVecQN d E s t K n j σ ω) := by
  have hcont : Continuous (fun A : (Fin k → Z2 (d.L n)) → ℂ =>
      Qop (d.L n) (gridTime s t K n (j + 1)) A) := by
    refine continuous_pi fun a => ?_
    unfold Qop Psum
    exact (continuous_apply a).sub
      ((continuous_finsetSum _ fun c _ => continuous_apply c).mul continuous_const)
  exact hcont.comp_stronglyMeasurable (stronglyMeasurable_ZvecN d E s t K n j σ)

theorem AltEndCompose_kapQ4_nonneg (L k : ℕ) [NeZero L] (Kw : ℝ) {s t : ℝ} (hs : s < 1) (ht : t < 1) :
    0 ≤ kapQ4 L k Kw s t := by
  have h1 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have h2 : 0 ≤ Kw ^ (2 * k) := by rw [pow_mul]; positivity
  have h3 : 0 ≤ cCase4 k := by unfold cCase4 cProp5; positivity
  have h4 := AltEndCompose_rhoR_nonneg (L := L) hs ht
  unfold kapQ4
  positivity

theorem AltEndCompose_epsQ4_nonneg (L k : ℕ) [NeZero L] {s t : ℝ} (hs : s < 1) (ht : t < 1) :
    0 ≤ epsQ4 L k s t := by
  have h1 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have h3 : 0 ≤ cCase4 k := by unfold cCase4 cProp5; positivity
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold epsQ4
  positivity

theorem AltEndCompose_altQLevel_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) (k : ℕ) (τ' Db Φ : ℝ) (hΦ : 0 ≤ Φ) : 0 ≤ altQLevel L W E k τ' Db Φ u := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hu1
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWp
  unfold altQLevel
  positivity

theorem AltEndCompose_altQ0Level_nonneg {L W : ℕ} [NeZero L] [NeZero W] {E s : ℝ} (hE : |E| < 2)
    (hs1 : s < 1) (k : ℕ) (τ' Db : ℝ) : 0 ≤ altQ0Level L W E s k τ' Db := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hs1
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWp
  unfold altQ0Level
  positivity

end Compositions

end RBM.Ind
