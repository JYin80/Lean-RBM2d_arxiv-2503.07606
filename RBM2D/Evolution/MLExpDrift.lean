/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpVocab
import RBM2D.Induction.BcalEDecay
import RBM2D.Induction.KcalDecay
import RBM2D.Path.ScalesBridge
import RBM2D.Gauss.LoopSampleCont

/-!
# The expected drift terms of `ML:exp`

Paper: Section 1 (`ML:exp`, `eq:step6main`) and Sections 5-6 (`eq:LKLKstep6`, `eq:wtGstep6`).
Namespace `RBM.Evol`, `variable (d : Sizes)`.

**Statement** `expDriftBound d κ c τ E t : ExpDriftBound d κ c τ E t` (the statement of
`Evolution/MLExpVocab.lean`): under `MLExpHyps` the drift
`D_u = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ}` (`expDriftT`) has `(u,τ',D)` decay and
`‖D_u‖_max ≤ N^ε η_u^{-1} M_u^{-3}` for every `u ∈ [0,t_n]` and every `σ`, eventually.

## Argument

1. At `n = 2` the two terms are explicit window sums (`MLExpDrift_elklkN_two`,
   `MLExpDrift_egtN_two`): `𝓔^{LK×LK}` has the single cut `(1,2)` (two 2-loops); `𝓔^{(G̃)}` has the
   cuts `k = 1,2`, a 1-loop times a 3-loop; `𝓛 = (𝓛 - 𝒦) + 𝒦` splits it into
   `(𝓛-𝒦)_1 × (𝓛-𝒦)_3` (`MLExpDrift_EL`) and `avgErr × 𝒦_3` (`MLExpDrift_MP`).
2. The good event `S_{n,u}` (`MLExpDrift_core`): `P(S) ≤ N^{-D_p}`, a union bound over all loops of
   length `≤ 3` of one `Step4PT` event (`𝓛 - 𝒦 ≺ M_u^{-m}`) and one `DecayLoopPT` event (far
   entries `≺ W^{-D''}`).  Parameters: `τ_4 = ε/4`, `τ_1 = min(τ'/2, ε/4)`, `τ_d = 1`,
   `D_p = 9 + D`, `D'' = D + 8 + (4 + ε/4)/c`.
3. Off `S` the window `(2R+1)^2`, `R = ℓ_u W^{τ_1}` (`norm_sum_SB_le_left/right`) gives
   `W^2 (2R+1)^2 N^{2τ_4} M_u^{-4} ≤ 9 N^{2τ_4 + τ_1} η_u^{-1} M_u^{-3}`, because
   `W^2 ℓ_u^2 M_u^{-4} = η_u^{-1} M_u^{-3}` (`MLExpDrift_num_window`); the far entries give the
   `W^{-D''}` tails (`MLExpDrift_A_bulk`, `MLExpDrift_far`).
4. The expectation of the random part: `𝔼‖f‖ ≤ c + Env · P(S)` (`MLExpDrift_first_moment`)
   with the polynomial envelope `N^5` (`MLExpDrift_env_X`,
   from `norm_gloop_le_opNorm`, `KboundConcl`, `η_u^{-1} ≤ N`).
5. `𝔼[avgErr · 𝒦_3] = (𝔼 avgErr) 𝒦_3` (`MLExpDrift_expDriftT_eq`), deterministic:
   `|𝔼 avgErr| ≺ M_u^{-2}` is `Step61Concl` (uniform in `u` by `step61_unif`; `σ = (-)` by complex
   conjugation, `MLExpDrift_norm_mu`), `|𝒦_3| ≺ M_u^{-2}` is `KboundConcl` at `n = 3`, and the far
   entries are `kcalDecay` (`MLExpDrift_MP_bound`).
6. Arithmetic: `MLExpDrift_bulk_num` (bulk, `N^ε = A^4`, `A = N^{ε/4} ≥ 48`) and
   `MLExpDrift_far_num` (decay).

The window argument of `bcalEPT'` (`Induction/BcalEDecay.lean`, `bcalEDecay_core`) is copied, not
called: `bcalEPT'` needs `MainIndHyp` and `Step2LocalPT`.  Compared with `bcalEPT'`,
the moment bridge is replaced by the first-moment lemma of item 4 (no second moments, no
lower floor of the control), `far_cutGlueL_or_far_cutGlueR` by the triangle inequality on the
explicit `n = 2` sums, `scaleM_etaT_of_range` by `η_u^{-1} ≤ N` (`MLExpDrift_eta_inv`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. The window sum and the explicit forms at `n = 2` -/

section Alg

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Σ_{x,y} A_x S^{(B)}_{xy} B_y`. -/
private def MLExpDrift_sbSum (A B : Z2 L → ℂ) : ℂ := ∑ x : Z2 L, ∑ y : Z2 L, A x * SB L x y * B y

private theorem MLExpDrift_elklkN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    elklkN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u M (loopOf σ ![a 0, y])) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold elklkN MLExpDrift_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : Finset.Ioc 1 2 = {2} := by decide
  have h3 : Finset.Ioc 2 2 = ∅ := by decide
  rw [h1, Finset.sum_pair (by norm_num), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  rfl

private theorem MLExpDrift_egtN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    egtN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * (MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold egtN MLExpDrift_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num)]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rfl

end Alg

/-! ## 2. Window bounds for `Σ_{x,y} A_x S_{xy} B_y` -/

section Window

variable {L : ℕ} [NeZero L]

private theorem MLExpDrift_sbSum_add_right (A B C : Z2 L → ℂ) :
    MLExpDrift_sbSum A (fun y => B y + C y) = MLExpDrift_sbSum A B + MLExpDrift_sbSum A C := by
  unfold MLExpDrift_sbSum
  simp only [mul_add, Finset.sum_add_distrib]

private theorem MLExpDrift_zdist2_sub_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
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

/-- `‖Σ A S B‖ ≤ L² b` if the product of the norms is `≤ b` on the support of `S^{(B)}`. -/
private theorem MLExpDrift_norm_sbSum_le (hL : 3 ≤ L) {A B : Z2 L → ℂ} {b : ℝ}
    (h : ∀ x y, zdist2 L (x - y) ≤ 1 → ‖A x‖ * ‖B y‖ ≤ b) :
    ‖MLExpDrift_sbSum A B‖ ≤ (L : ℝ) ^ 2 * b := by
  have hb : 0 ≤ b := by
    have := h 0 0 (by simp)
    exact le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) this
  calc ‖MLExpDrift_sbSum A B‖ ≤ ∑ x : Z2 L, ∑ y : Z2 L, ‖SB L x y‖ * b := by
        unfold MLExpDrift_sbSum
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => ?_))
        by_cases hxy : zdist2 L (x - y) ≤ 1
        · rw [norm_mul, norm_mul]
          calc ‖A x‖ * ‖SB L x y‖ * ‖B y‖ = ‖SB L x y‖ * (‖A x‖ * ‖B y‖) := by ring
            _ ≤ ‖SB L x y‖ * b := mul_le_mul_of_nonneg_left (h x y hxy) (norm_nonneg _)
        · rw [SB_apply_eq_zero L hL (by omega)]; simp
    _ = (L : ℝ) ^ 2 * b := by
        simp only [← Finset.sum_mul, BcalEDecay_sum_sum_norm_SB L hL]

/-- The window bound with decay in the first variable (anchor `c`). -/
private theorem MLExpDrift_norm_sbSum_left (hL : 3 ≤ L) {R MA MB δA : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δA) (c : Z2 L) {A B : Z2 L → ℂ} (hA : ∀ x, ‖A x‖ ≤ MA) (hB : ∀ y, ‖B y‖ ≤ MB)
    (hAd : ∀ x, R ≤ (zdist2 L (x - c) : ℝ) → ‖A x‖ ≤ δA) :
    ‖MLExpDrift_sbSum A B‖ ≤ (2 * R + 1) ^ 2 * (MA * MB) + (L : ℝ) ^ 2 * (δA * MB) := by
  have hMB : 0 ≤ MB := (norm_nonneg _).trans (hB 0)
  have h := norm_sum_SB_le_left L hL (M := MA * MB) (δ := δA * MB) hR (mul_nonneg hδ hMB) c
    (fun x y => A x * B y)
    (fun x y => by
      show ‖A x * B y‖ ≤ MA * MB
      rw [norm_mul]; exact mul_le_mul (hA x) (hB y) (norm_nonneg _)
        ((norm_nonneg _).trans (hA 0)))
    (fun x y hx => by
      show ‖A x * B y‖ ≤ δA * MB
      rw [norm_mul]; exact mul_le_mul (hAd x hx) (hB y) (norm_nonneg _) hδ)
  have e : MLExpDrift_sbSum A B = ∑ x : Z2 L, ∑ y : Z2 L, SB L x y * (A x * B y) := by
    unfold MLExpDrift_sbSum
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  exact h

/-- The window bound with decay in the second variable (anchor `c`). -/
private theorem MLExpDrift_norm_sbSum_right (hL : 3 ≤ L) {R MA MB δB : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δB) (c : Z2 L) {A B : Z2 L → ℂ} (hA : ∀ x, ‖A x‖ ≤ MA) (hB : ∀ y, ‖B y‖ ≤ MB)
    (hBd : ∀ y, R ≤ (zdist2 L (y - c) : ℝ) → ‖B y‖ ≤ δB) :
    ‖MLExpDrift_sbSum A B‖ ≤ (2 * R + 1) ^ 2 * (MA * MB) + (L : ℝ) ^ 2 * (MA * δB) := by
  have hMA : 0 ≤ MA := (norm_nonneg _).trans (hA 0)
  have h := norm_sum_SB_le_right L hL (M := MA * MB) (δ := MA * δB) hR (mul_nonneg hMA hδ) c
    (fun x y => A x * B y)
    (fun x y => by
      show ‖A x * B y‖ ≤ MA * MB
      rw [norm_mul]; exact mul_le_mul (hA x) (hB y) (norm_nonneg _) hMA)
    (fun x y hy => by
      show ‖A x * B y‖ ≤ MA * δB
      rw [norm_mul]; exact mul_le_mul (hA x) (hBd y hy) (norm_nonneg _) hMA)
  have e : MLExpDrift_sbSum A B = ∑ x : Z2 L, ∑ y : Z2 L, SB L x y * (A x * B y) := by
    unfold MLExpDrift_sbSum
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  exact h

/-- `|a_i - a_j|_L ≤ max_{p,q} |a_p - a_q|_L`. -/
private theorem MLExpDrift_zdist2_le_maxDist {k : ℕ} (a : Fin k → Z2 L) (i j : Fin k) :
    (zdist2 L (a i - a j) : ℝ) ≤ (KLoop.maxDist L a : ℝ) := by
  unfold KLoop.maxDist
  exact_mod_cast Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (a p.1 - a p.2))
    (Finset.mem_univ (i, j))

end Window

/-! ## 3. Deterministic estimates at `n = 2` -/

section Det

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The `𝓛 - 𝒦` half of `𝓔^{(G̃)}` at `n = 2`: `(𝓛 - 𝒦)_1 × (𝓛 - 𝒦)_3`. -/
private def MLExpDrift_EL (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * (MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
      (fun y => LKf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
    MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
      (fun y => LKf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))

/-- The `𝒦` half of `𝓔^{(G̃)}` at `n = 2`: `avgErr × 𝒦_3` (its expectation is `(𝔼 avgErr) 𝒦_3`). -/
private def MLExpDrift_MP (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * (MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
      (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
    MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
      (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))

/-- `𝓔^{(G̃)} = (𝓛-𝒦)_1×(𝓛-𝒦)_3 + avgErr×𝒦_3` (`𝓛 = (𝓛-𝒦) + 𝒦` in the 3-loop). -/
private theorem MLExpDrift_egtN_split (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    egtN L W E u M (loopOf σ a) = MLExpDrift_EL E u M σ a + MLExpDrift_MP E u M σ a := by
  have hLL : ∀ J, LLf L W E u M J = LKf L W E u M J + KLoop.Kcal L W E u J := by
    intro J; unfold LKf; ring
  rw [MLExpDrift_egtN_two]
  unfold MLExpDrift_EL MLExpDrift_MP
  simp only [hLL, MLExpDrift_sbSum_add_right]
  ring

/-- `‖(W:ℂ)^2‖ = W^2`. -/
private theorem MLExpDrift_norm_W2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp

/-- **The bulk bound of `𝓔^{LK×LK} + (𝓛-𝒦)_1×(𝓛-𝒦)_3`** on a good sample: the `(2R+1)^2` window. -/
private theorem MLExpDrift_A_bulk (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) {R T₁ T₂ T₃ δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (h1 : ∀ (s : Bool) (x : Z2 L), ‖avgErr L W E u M s x‖ ≤ T₁)
    (h2 : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Z2 L), ‖LKf L W E u M (loopOf σ' a')‖ ≤ T₂)
    (h3 : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L), ‖LKf L W E u M (loopOf σ' a')‖ ≤ T₃)
    (hd2 : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Z2 L), R ≤ (KLoop.maxDist L a' : ℝ) →
      ‖LKf L W E u M (loopOf σ' a')‖ ≤ δ)
    (hd3 : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L), R ≤ (KLoop.maxDist L a' : ℝ) →
      ‖LKf L W E u M (loopOf σ' a')‖ ≤ δ) :
    ‖elklkN L W E u M (loopOf σ a) + MLExpDrift_EL E u M σ a‖ ≤
      (W : ℝ) ^ 2 * ((2 * R + 1) ^ 2 * (T₂ * T₂ + 2 * (T₁ * T₃)) +
        (L : ℝ) ^ 2 * (δ * T₂ + 2 * (T₁ * δ))) := by
  have hT₂ : 0 ≤ T₂ := (norm_nonneg _).trans (h2 σ a)
  have hT₁ : 0 ≤ T₁ := (norm_nonneg _).trans (h1 true 0)
  have hT₃ : 0 ≤ T₃ := (norm_nonneg _).trans (h3 ![true, true, true] ![0, 0, 0])
  -- the first-order pieces
  have e1 : ‖MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u M (loopOf σ ![a 0, y]))‖ ≤
      (2 * R + 1) ^ 2 * (T₂ * T₂) + (L : ℝ) ^ 2 * (δ * T₂) :=
    MLExpDrift_norm_sbSum_left hL hR hδ (a 1) (fun x => h2 σ _) (fun y => h2 σ _)
      (fun x hx => hd2 σ _ (hx.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![x, a 1] : Fin 2 → Z2 L) 0 1
        simpa using this)))
  have e2 : ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
        (fun y => LKf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ ≤
      (2 * R + 1) ^ 2 * (T₁ * T₃) + (L : ℝ) ^ 2 * (T₁ * δ) :=
    MLExpDrift_norm_sbSum_right hL hR hδ (a 0) (fun x => h1 _ _) (fun y => h3 _ _)
      (fun y hy => hd3 _ _ (hy.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![y, a 0, a 1] : Fin 3 → Z2 L) 0 1
        simpa using this)))
  have e3 : ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
        (fun y => LKf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖ ≤
      (2 * R + 1) ^ 2 * (T₁ * T₃) + (L : ℝ) ^ 2 * (T₁ * δ) :=
    MLExpDrift_norm_sbSum_right hL hR hδ (a 0) (fun x => h1 _ _) (fun y => h3 _ _)
      (fun y hy => hd3 _ _ (hy.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![a 0, y, a 1] : Fin 3 → Z2 L) 0 1
        rw [MLExpDrift_zdist2_sub_comm]
        simpa using this)))
  rw [MLExpDrift_elklkN_two]
  unfold MLExpDrift_EL
  calc ‖(W : ℂ) ^ 2 * MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
          (fun y => LKf L W E u M (loopOf σ ![a 0, y])) +
        (W : ℂ) ^ 2 * (MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))‖
      = (W : ℝ) ^ 2 * ‖MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
          (fun y => LKf L W E u M (loopOf σ ![a 0, y])) +
        (MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))‖ := by
        rw [← mul_add, norm_mul, MLExpDrift_norm_W2]
    _ ≤ (W : ℝ) ^ 2 * (‖MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
          (fun y => LKf L W E u M (loopOf σ ![a 0, y]))‖ +
        (‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ +
        ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LKf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ (W : ℝ) ^ 2 * ((2 * R + 1) ^ 2 * (T₂ * T₂) + (L : ℝ) ^ 2 * (δ * T₂) +
        ((2 * R + 1) ^ 2 * (T₁ * T₃) + (L : ℝ) ^ 2 * (T₁ * δ) +
        ((2 * R + 1) ^ 2 * (T₁ * T₃) + (L : ℝ) ^ 2 * (T₁ * δ)))) := by
        gcongr
    _ = _ := by ring

/-- The deterministic mean of `avgErr × 𝒦_3`: `μ_s(x) = 𝔼 avgErr_s(x)` in place of `avgErr`. -/
private def MLExpDrift_MPmean (W : ℕ) [NeZero W] (E u : ℝ) (μ : Bool → Z2 L → ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * (MLExpDrift_sbSum (μ (σ 0))
      (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
    MLExpDrift_sbSum (μ (σ 1))
      (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))

/-- **The bound of the mean part**, deterministic: `(𝔼 avgErr) 𝒦_3` with the window `(2R+1)^2`. -/
private theorem MLExpDrift_MP_bound (hL : 3 ≤ L) (E u : ℝ) (μ : Bool → Z2 L → ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) {R Tμ TK δK : ℝ} (hR : 0 ≤ R) (hδK : 0 ≤ δK)
    (hμ : ∀ (s : Bool) (x : Z2 L), ‖μ s x‖ ≤ Tμ)
    (hK : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L), ‖KLoop.Kcal L W E u (loopOf σ' a')‖ ≤ TK)
    (hKd : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L), R ≤ (KLoop.maxDist L a' : ℝ) →
      ‖KLoop.Kcal L W E u (loopOf σ' a')‖ ≤ δK) :
    ‖MLExpDrift_MPmean W E u μ σ a‖ ≤
      (W : ℝ) ^ 2 * (2 * ((2 * R + 1) ^ 2 * (Tμ * TK) + (L : ℝ) ^ 2 * (Tμ * δK))) := by
  have e2 : ‖MLExpDrift_sbSum (μ (σ 0))
        (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ ≤
      (2 * R + 1) ^ 2 * (Tμ * TK) + (L : ℝ) ^ 2 * (Tμ * δK) :=
    MLExpDrift_norm_sbSum_right hL hR hδK (a 0) (fun x => hμ _ _) (fun y => hK _ _)
      (fun y hy => hKd _ _ (hy.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![y, a 0, a 1] : Fin 3 → Z2 L) 0 1
        simpa using this)))
  have e3 : ‖MLExpDrift_sbSum (μ (σ 1))
        (fun y => KLoop.Kcal L W E u (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖ ≤
      (2 * R + 1) ^ 2 * (Tμ * TK) + (L : ℝ) ^ 2 * (Tμ * δK) :=
    MLExpDrift_norm_sbSum_right hL hR hδK (a 0) (fun x => hμ _ _) (fun y => hK _ _)
      (fun y hy => hKd _ _ (hy.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![a 0, y, a 1] : Fin 3 → Z2 L) 0 1
        rw [MLExpDrift_zdist2_sub_comm]
        simpa using this)))
  unfold MLExpDrift_MPmean
  rw [norm_mul, MLExpDrift_norm_W2]
  gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add e2 e3
    _ = _ := by ring

/-- **The far bound** of `𝓔^{LK×LK}` and `𝓔^{(G̃)}` when `|a_0 - a_1|_L ≥ 2R+1`: every summand has
a factor with a far label. -/
private theorem MLExpDrift_far (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) {R B₁ B₂ δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hfar : 2 * R + 1 ≤ (zdist2 L (a 0 - a 1) : ℝ))
    (h1 : ∀ (s : Bool) (x : Z2 L), ‖avgErr L W E u M s x‖ ≤ B₁)
    (h2 : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Z2 L), ‖LKf L W E u M (loopOf σ' a')‖ ≤ B₂)
    (hd2 : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Z2 L), R ≤ (KLoop.maxDist L a' : ℝ) →
      ‖LKf L W E u M (loopOf σ' a')‖ ≤ δ)
    (hd3 : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L), R ≤ (KLoop.maxDist L a' : ℝ) →
      ‖LLf L W E u M (loopOf σ' a')‖ ≤ δ) :
    ‖elklkN L W E u M (loopOf σ a)‖ + ‖egtN L W E u M (loopOf σ a)‖ ≤
      (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * (B₂ * δ + 2 * (B₁ * δ)) := by
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans (h2 σ a)
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (h1 true 0)
  -- `elklkN`
  have hel : ‖MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u M (loopOf σ ![a 0, y]))‖ ≤ (L : ℝ) ^ 2 * (B₂ * δ) := by
    refine MLExpDrift_norm_sbSum_le hL fun x y hxy => ?_
    have hx0 : (zdist2 L (a 0 - y) : ℝ) + zdist2 L (y - x) + zdist2 L (x - a 1) ≥
        (zdist2 L (a 0 - a 1) : ℝ) := by
      have t1 := zdist2_add_le L (a 0 - y) (y - x)
      have t2 := zdist2_add_le L (a 0 - y + (y - x)) (x - a 1)
      have e : a 0 - y + (y - x) + (x - a 1) = a 0 - a 1 := by abel
      rw [e] at t2
      exact_mod_cast t2.trans (Nat.add_le_add_right t1 _)
    have hyx : (zdist2 L (y - x) : ℝ) ≤ 1 := by
      rw [MLExpDrift_zdist2_sub_comm]; exact_mod_cast hxy
    have hcase : R ≤ (zdist2 L (a 0 - y) : ℝ) ∨ R ≤ (zdist2 L (x - a 1) : ℝ) := by
      by_contra hcon
      push Not at hcon
      linarith [hcon.1, hcon.2]
    rcases hcase with hc | hc
    · have hL₂ : ‖LKf L W E u M (loopOf σ ![a 0, y])‖ ≤ δ := hd2 σ _ (hc.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![a 0, y] : Fin 2 → Z2 L) 0 1
        simpa using this))
      have := mul_le_mul (h2 σ ![x, a 1]) hL₂ (norm_nonneg _) hB₂
      exact this
    · have hL₁ : ‖LKf L W E u M (loopOf σ ![x, a 1])‖ ≤ δ := hd2 σ _ (hc.trans (by
        have := MLExpDrift_zdist2_le_maxDist (![x, a 1] : Fin 2 → Z2 L) 0 1
        simpa using this))
      have := mul_le_mul hL₁ (h2 σ ![a 0, y]) (norm_nonneg _) hδ
      calc _ ≤ δ * B₂ := this
        _ = B₂ * δ := mul_comm _ _
  -- `egtN`
  have hd3' : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 L) (i j : Fin 3),
      (zdist2 L (a 0 - a 1) : ℝ) ≤ (zdist2 L (a' i - a' j) : ℝ) →
        ‖LLf L W E u M (loopOf σ' a')‖ ≤ δ := fun σ' a' i j h =>
    hd3 σ' a' ((by linarith : R ≤ (zdist2 L (a 0 - a 1) : ℝ)).trans
      (h.trans (MLExpDrift_zdist2_le_maxDist a' i j)))
  have hg1 : ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
        (fun y => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ ≤
      (L : ℝ) ^ 2 * (B₁ * δ) :=
    MLExpDrift_norm_sbSum_le hL fun x y _ =>
      mul_le_mul (h1 _ _) (hd3' _ _ 1 2 (by simp)) (norm_nonneg _) hB₁
  have hg2 : ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
        (fun y => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖ ≤
      (L : ℝ) ^ 2 * (B₁ * δ) :=
    MLExpDrift_norm_sbSum_le hL fun x y _ =>
      mul_le_mul (h1 _ _) (hd3' _ _ 0 2 (by simp)) (norm_nonneg _) hB₁
  rw [MLExpDrift_elklkN_two, MLExpDrift_egtN_two, norm_mul, norm_mul, MLExpDrift_norm_W2]
  calc (W : ℝ) ^ 2 * ‖MLExpDrift_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
          (fun y => LKf L W E u M (loopOf σ ![a 0, y]))‖ +
        (W : ℝ) ^ 2 * ‖MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpDrift_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖
      ≤ (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (B₂ * δ)) +
        (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (B₁ * δ) + (L : ℝ) ^ 2 * (B₁ * δ)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hg1 hg2)
    _ = _ := by ring

end Det

/-! ## 4. The sample-level facts at one `(n, u)`: measurability, envelope, means -/

section Sample

variable (d : Sizes)

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = (𝓛 - 𝒦)_{u,(σ),(a)}` (as the private `bcalEDecay_avgErr_eq`). -/
private theorem MLExpDrift_avgErr_eq {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (a : Z2 L) :
    avgErr L W E u M s a = LKf L W E u M (loopOf ![s] ![a]) := by
  have hI : loopOf ![s] ![a] = (⟨[s], [a]⟩ : LoopIdx (Z2 L)) := by
    simp [loopOf, List.ofFn_succ]
  rw [hI]
  unfold LKf LLf avgErr
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]

private theorem MLExpDrift_WF_loopOf {L n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem MLExpDrift_length_loopOf {L n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    (loopOf σ a).length = n := by
  simp [loopOf, LoopIdx.length]

private theorem MLExpDrift_spectralZ_im_ne {E u : ℝ} (hE : |E| < 2) (hu : u < 1) :
    (spectralZ E u).im ≠ 0 := by
  rw [spectralZ_im]
  exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'

/-- The loop is a measurable function of the sample. -/
private theorem MLExpDrift_measurable_LLf (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) :
    Measurable fun ω : Sizes.SeqΩ d => LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J :=
  (measurable_gloop_HflowBlock_sample (d.L n) (d.W n) u (MLExpDrift_spectralZ_im_ne hE hu) J
    hJ).comp (Sizes.measurable_slice d n)

private theorem MLExpDrift_measurable_LKf (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) :
    Measurable fun ω : Sizes.SeqΩ d => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J :=
  (MLExpDrift_measurable_LLf d n hE hu hJ).sub measurable_const

private theorem MLExpDrift_measurable_avgErr (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (s : Bool) (x : Z2 (d.L n)) :
    Measurable fun ω : Sizes.SeqΩ d => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) s x := by
  simp only [MLExpDrift_avgErr_eq]
  exact MLExpDrift_measurable_LKf d n hE hu (MLExpDrift_WF_loopOf _ _)

/-- **The envelope**: `‖𝓛_u(J)‖ ≤ N^{|J|}` on every sample when `η_u^{-1} ≤ N`. -/
private theorem MLExpDrift_LLf_env (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
    (hη : ((1 - u) * (spectralM E).im)⁻¹ ≤ N) (hN : 1 ≤ N) (ω : Sizes.SeqΩ d)
    {J : LoopIdx (Z2 (d.L n))} (hJ : J.WF) (h1 : 1 ≤ J.length) :
    ‖LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) J‖ ≤ N ^ J.length := by
  have hH : (blockMat (Sizes.seqHflow d n u ω)).IsHermitian :=
    (Sizes.seqHflow_isHermitian d n u ω).submatrix _
  have hz := MLExpDrift_spectralZ_im_ne hE hu
  have hη0 : 0 < (1 - u) * (spectralM E).im := mul_pos (by linarith) (spectralM_im_pos hE)
  have hg := norm_gloop_le_opNorm (W := d.W n) hH hz J hJ h1
  have habs : |(spectralZ E u).im|⁻¹ ≤ N := by
    rw [spectralZ_im, abs_of_pos hη0]; exact hη
  have hW1 : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWinv : (((d.W n : ℝ))⁻¹ ^ 2) ^ (J.a.length - 1) ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  unfold LLf
  calc ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n u ω)) (spectralZ E u) J‖
      ≤ |(spectralZ E u).im|⁻¹ ^ J.a.length * (((d.W n : ℝ))⁻¹ ^ 2) ^ (J.a.length - 1) := hg
    _ ≤ N ^ J.a.length * 1 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) habs _) hWinv (by positivity)
          (by positivity)
    _ = N ^ J.length := by rw [mul_one]; rfl

/-- The `σ = (-)` one-loop is the complex conjugate of the `σ = (+)` one-loop. -/
private theorem MLExpDrift_LLf_false {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (x : Z2 L) :
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

/-- `μ_s(x) = 𝔼 avgErr_s(x)`. -/
private def MLExpDrift_mu (n : ℕ) (E u : ℝ) (s : Bool) (x : Z2 (d.L n)) : ℂ :=
  ∫ ω, avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) s x ∂(Sizes.seqP d)

/-- **The mean of `avgErr`** is `oneLoopExpErr` (`σ = +`) or its conjugate (`σ = -`). -/
private theorem MLExpDrift_norm_mu (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
    (hη : ((1 - u) * (spectralM E).im)⁻¹ ≤ N) (hN : 1 ≤ N) (s : Bool) (x : Z2 (d.L n)) :
    ‖MLExpDrift_mu d n E u s x‖ = ‖oneLoopExpErr d n E u x‖ := by
  have hint : Integrable (fun ω : Sizes.SeqΩ d =>
      LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩) (Sizes.seqP d) :=
    Integrable.of_bound (MLExpDrift_measurable_LLf d n hE hu (J := ⟨[true], [x]⟩)
      (by simp [LoopIdx.WF])).aestronglyMeasurable (N ^ 1)
      (Eventually.of_forall fun ω => by
        have := MLExpDrift_LLf_env d n hE hu hη hN ω (J := ⟨[true], [x]⟩) (by simp [LoopIdx.WF])
          (by simp [LoopIdx.length])
        simpa [LoopIdx.length] using this)
  have hplus : ∫ ω, LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩
      ∂(Sizes.seqP d) - spectralM E = oneLoopExpErr d n E u x := rfl
  have hmean : ∀ s : Bool, MLExpDrift_mu d n E u s x =
      ∫ ω, LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[s], [x]⟩ ∂(Sizes.seqP d) -
        KLoop.mSig E s := by
    intro s
    unfold MLExpDrift_mu
    have hs : ∀ ω : Sizes.SeqΩ d, avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) s x =
        LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[s], [x]⟩ - KLoop.mSig E s := by
      intro ω
      rw [MLExpDrift_avgErr_eq]
      unfold LKf
      have h2 : KLoop.Kcal (d.L n) (d.W n) E u ⟨[s], [x]⟩ = KLoop.mSig E s := by
        simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
      have : loopOf ![s] ![x] = (⟨[s], [x]⟩ : LoopIdx (Z2 (d.L n))) := by
        simp [loopOf, List.ofFn_succ]
      rw [this, h2]
    simp only [hs]
    cases s
    · have hf : ∀ ω : Sizes.SeqΩ d,
          LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[false], [x]⟩ =
            (starRingEnd ℂ) (LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩) :=
        fun ω => MLExpDrift_LLf_false E u (Sizes.seqHflow_isHermitian d n u ω) x
      simp only [hf]
      have hintc : Integrable (fun ω : Sizes.SeqΩ d => (starRingEnd ℂ)
          (LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩)) (Sizes.seqP d) :=
        Integrable.mono' hint.norm (Complex.continuous_conj.comp_aestronglyMeasurable hint.1)
          (Eventually.of_forall fun ω => (Complex.norm_conj _).le)
      rw [integral_sub hintc (integrable_const _), integral_conj, integral_const]
      simp
    · rw [integral_sub hint (integrable_const _), integral_const]
      simp
  rcases s with _ | _
  · rw [hmean false, ← hplus]
    have hf : ∀ ω : Sizes.SeqΩ d,
        LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[false], [x]⟩ =
          (starRingEnd ℂ) (LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) ⟨[true], [x]⟩) :=
      fun ω => MLExpDrift_LLf_false E u (Sizes.seqHflow_isHermitian d n u ω) x
    simp only [hf]
    rw [integral_conj]
    have : KLoop.mSig E false = (starRingEnd ℂ) (spectralM E) := rfl
    rw [this, ← map_sub, Complex.norm_conj]
  · rw [hmean true, ← hplus]
    rfl

/-- Measurability of the window sum. -/
private theorem MLExpDrift_measurable_sbSum {L : ℕ} [NeZero L] {Ω : Type*} [MeasurableSpace Ω]
    {A B : Z2 L → Ω → ℂ} (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    Measurable fun ω => MLExpDrift_sbSum (fun x => A x ω) (fun y => B y ω) := by
  unfold MLExpDrift_sbSum
  exact Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
    ((hA x).mul_const _).mul (hB y)

/-- The envelope of `𝓛 - 𝒦` for loops of length `m ∈ {1,2,3}`. -/
private theorem MLExpDrift_env_LKf (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
    (hη : ((1 - u) * (spectralM E).im)⁻¹ ≤ N) (hN : 1 ≤ N)
    (hK : ∀ m ∈ Finset.Icc 1 3, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a)‖ ≤ N ^ m)
    (ω : Sizes.SeqΩ d) {m : ℕ} (hm : m ∈ Finset.Icc 1 3) (σ : Fin m → Bool)
    (a : Fin m → Z2 (d.L n)) :
    ‖LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤ 2 * N ^ m := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
  have h1 := MLExpDrift_LLf_env d n hE hu hη hN ω (MLExpDrift_WF_loopOf σ a)
    (by rw [MLExpDrift_length_loopOf]; exact hm1)
  rw [MLExpDrift_length_loopOf] at h1
  unfold LKf
  calc _ ≤ ‖LLf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ +
        ‖KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a)‖ := norm_sub_le _ _
    _ ≤ N ^ m + N ^ m := add_le_add h1 (hK m hm σ a)
    _ = 2 * N ^ m := by ring

/-- The envelope of `X_ω = 𝓔^{LK×LK} + (𝓛-𝒦)_1×(𝓛-𝒦)_3` and of `MP_ω`: `≤ 12 N^5`, `≤ 4 N^5`. -/
private theorem MLExpDrift_env_X (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
    (hη : ((1 - u) * (spectralM E).im)⁻¹ ≤ N) (hN : 1 ≤ N)
    (hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N)
    (hK : ∀ m ∈ Finset.Icc 1 3, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a)‖ ≤ N ^ m)
    (ω : Sizes.SeqΩ d) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)) :
    ‖elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        MLExpDrift_EL E u (Sizes.seqHflow d n u ω) σ a‖ ≤ 12 * N ^ 5 ∧
      ‖MLExpDrift_MP E u (Sizes.seqHflow d n u ω) σ a‖ ≤ 4 * N ^ 5 := by
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hLK : ∀ (m : ℕ) (hm : m ∈ Finset.Icc 1 3) (σ' : Fin m → Bool) (a' : Fin m → Z2 (d.L n)),
      ‖LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ' a')‖ ≤ 2 * N ^ m :=
    fun m hm σ' a' => MLExpDrift_env_LKf d n hE hu hη hN hK ω hm σ' a'
  have hav : ∀ (s : Bool) (x : Z2 (d.L n)),
      ‖avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) s x‖ ≤ 2 * N ^ 1 := by
    intro s x
    rw [MLExpDrift_avgErr_eq]
    exact hLK 1 (by simp) _ _
  have hN0 : 0 ≤ N := by linarith
  -- crude bounds of the window sums
  have b1 : ‖MLExpDrift_sbSum (fun x => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω)
        (loopOf σ ![x, a 1]))
      (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ ![a 0, y]))‖ ≤
      (d.L n : ℝ) ^ 2 * ((2 * N ^ 2) * (2 * N ^ 2)) :=
    MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hLK 2 (by simp) _ _) (hLK 2 (by simp) _ _) (norm_nonneg _) (by positivity)
  have b2 : ∀ (F : Bool → LoopIdx (Z2 (d.L n)) → ℂ) (τ : Bool) (Y : Z2 (d.L n) → LoopIdx (Z2 (d.L n))),
      (∀ y, ‖F τ (Y y)‖ ≤ N ^ 3) →
      ‖MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) τ x)
        (fun y => F τ (Y y))‖ ≤ (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * N ^ 3) := by
    intro F τ Y hY
    exact MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hav _ _) (hY y) (norm_nonneg _) (by positivity)
  have b3 : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 (d.L n)),
      ‖LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ' a')‖ ≤ 2 * N ^ 3 :=
    fun σ' a' => hLK 3 (by simp) _ _
  have b4 : ∀ (σ' : Fin 3 → Bool) (a' : Fin 3 → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ' a')‖ ≤ N ^ 3 :=
    fun σ' a' => hK 3 (by simp) _ _
  have hEL1 : ‖MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (σ 0) x)
        (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω)
          (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ ≤
      (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * (2 * N ^ 3)) :=
    MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hav _ _) (b3 _ _) (norm_nonneg _) (by positivity)
  have hEL2 : ‖MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (σ 1) x)
        (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω)
          (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖ ≤
      (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * (2 * N ^ 3)) :=
    MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hav _ _) (b3 _ _) (norm_nonneg _) (by positivity)
  have hMP1 : ‖MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (σ 0) x)
        (fun y => KLoop.Kcal (d.L n) (d.W n) E u (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1]))‖ ≤
      (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * N ^ 3) :=
    MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hav _ _) (b4 _ _) (norm_nonneg _) (by positivity)
  have hMP2 : ‖MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (σ 1) x)
        (fun y => KLoop.Kcal (d.L n) (d.W n) E u (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))‖ ≤
      (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * N ^ 3) :=
    MLExpDrift_norm_sbSum_le hL3 fun x y _ =>
      mul_le_mul (hav _ _) (b4 _ _) (norm_nonneg _) (by positivity)
  have hWLc : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N := hWL
  have e5 : N * N ^ 4 = N ^ 5 := by ring
  constructor
  · rw [MLExpDrift_elklkN_two]
    unfold MLExpDrift_EL
    calc _ ≤ ‖(d.W n : ℂ) ^ 2 * MLExpDrift_sbSum (fun x => LKf (d.L n) (d.W n) E u
            (Sizes.seqHflow d n u ω) (loopOf σ ![x, a 1]))
          (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ ![a 0, y]))‖ +
        ‖(d.W n : ℂ) ^ 2 * (MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u
            (Sizes.seqHflow d n u ω) (σ 0) x)
          (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω)
            (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpDrift_sbSum (fun x => avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (σ 1) x)
          (fun y => LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω)
            (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])))‖ := norm_add_le _ _
      _ ≤ (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * ((2 * N ^ 2) * (2 * N ^ 2))) +
          (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * (2 * N ^ 3)) +
            (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * (2 * N ^ 3))) := by
          rw [norm_mul, norm_mul, MLExpDrift_norm_W2]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hEL1 hEL2)
      _ = 12 * N ^ 5 := by
          have : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N := hWLc
          calc _ = ((d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2) * (4 * N ^ 4 + 8 * N ^ 4) := by ring
            _ = 12 * N ^ 5 := by rw [this]; ring
  · unfold MLExpDrift_MP
    rw [norm_mul, MLExpDrift_norm_W2]
    calc (d.W n : ℝ) ^ 2 * _ ≤ (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * N ^ 3) +
          (d.L n : ℝ) ^ 2 * ((2 * N ^ 1) * N ^ 3)) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hMP1 hMP2)
      _ = 4 * N ^ 5 := by
          calc _ = ((d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2) * (4 * N ^ 4) := by ring
            _ = 4 * N ^ 5 := by rw [hWLc]; ring

end Sample

/-! ## 5. The first moment outside a small event -/

section Moment

/-- **The first moment outside a small event**: `‖f‖ ≤ c` off `S` and `‖f‖ ≤ B` everywhere give
`𝔼‖f‖ ≤ c + B P(S)`.  Stated for the bad set `S` and, since only the
integrability of the right side is used (`integral_mono_of_nonneg`), without measurability
hypotheses on `f` or `S`. -/
private theorem MLExpDrift_first_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℂ} {S : Set Ω} {c B : ℝ} (hc : 0 ≤ c) (hB0 : 0 ≤ B)
    (hB : ∀ ω, ‖f ω‖ ≤ B) (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ c) :
    ∫ ω, ‖f ω‖ ∂P ≤ c + B * (P S).toReal := by
  classical
  set S' : Set Ω := toMeasurable P S with hS'
  have hmeas : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS : P S' = P S := measure_toMeasurable S
  have hpt : ∀ ω, ‖f ω‖ ≤ c + B * S'.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω]
      have := hB ω
      linarith
    · rw [Set.indicator_of_notMem hω]
      have := hin ω (fun h => hω (subset_toMeasurable P S h))
      linarith
  have hint : Integrable (fun ω => c + B * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const c).add (Integrable.const_mul ((integrable_const (1 : ℝ)).indicator hmeas) B)
  calc ∫ ω, ‖f ω‖ ∂P ≤ ∫ ω, (c + B * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = c + B * (P S).toReal := by
        rw [integral_add (integrable_const c) (Integrable.const_mul
          ((integrable_const (1 : ℝ)).indicator hmeas) B), integral_const,
          integral_const_mul, integral_indicator_const _ hmeas]
        simp [measureReal_def, hPS]

end Moment

/-! ## 6. The expected drift as `𝔼 X + mean part` -/

section Decomp

variable (d : Sizes)

private theorem MLExpDrift_integrable_sbSum {L : ℕ} [NeZero L] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Z2 L → Ω → ℂ} (K : Z2 L → ℂ) (hF : ∀ x, Integrable (F x) P) :
    Integrable (fun ω => MLExpDrift_sbSum (fun x => F x ω) K) P := by
  unfold MLExpDrift_sbSum
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    ((hF x).mul_const _).mul_const _

private theorem MLExpDrift_integral_sbSum {L : ℕ} [NeZero L] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Z2 L → Ω → ℂ} (K : Z2 L → ℂ) (hF : ∀ x, Integrable (F x) P) :
    ∫ ω, MLExpDrift_sbSum (fun x => F x ω) K ∂P =
      MLExpDrift_sbSum (fun x => ∫ ω, F x ω ∂P) K := by
  unfold MLExpDrift_sbSum
  have hi : ∀ x y, Integrable (fun ω => F x ω * SB L x y * K y) P := fun x y =>
    ((hF x).mul_const _).mul_const _
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hi x y]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun y _ => hi x y]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_mul_const, integral_mul_const]

/-- **The decomposition of the expected drift**:
`𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)}) = 𝔼 X + W² Σ (𝔼 avgErr) S 𝒦_3`, `X = 𝓔^{LK×LK} + (𝓛-𝒦)_1×(𝓛-𝒦)_3`. -/
private theorem MLExpDrift_expDriftT_eq (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
    (hη : ((1 - u) * (spectralM E).im)⁻¹ ≤ N) (hN : 1 ≤ N)
    (hWL : (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 = N)
    (hK : ∀ m ∈ Finset.Icc 1 3, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a)‖ ≤ N ^ m)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)) :
    expDriftT d n E u σ a =
      (∫ ω, (elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
          MLExpDrift_EL E u (Sizes.seqHflow d n u ω) σ a) ∂(Sizes.seqP d)) +
        MLExpDrift_MPmean (d.W n) E u (MLExpDrift_mu d n E u) σ a := by
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hLKm : ∀ {m : ℕ} (σ' : Fin m → Bool) (a' : Fin m → Z2 (d.L n)),
      Measurable fun ω : Sizes.SeqΩ d =>
        LKf (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ' a') := fun σ' a' =>
    MLExpDrift_measurable_LKf d n hE hu (MLExpDrift_WF_loopOf σ' a')
  have havm := MLExpDrift_measurable_avgErr d n hE hu
  have hav_int : ∀ (s : Bool) (x : Z2 (d.L n)), Integrable (fun ω : Sizes.SeqΩ d =>
      avgErr (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) s x) (Sizes.seqP d) := by
    intro s x
    refine Integrable.of_bound (havm s x).aestronglyMeasurable (2 * N ^ 1)
      (Eventually.of_forall fun ω => ?_)
    rw [MLExpDrift_avgErr_eq]
    exact MLExpDrift_env_LKf d n hE hu hη hN hK ω (m := 1) (by simp) _ _
  -- measurability of `X` and `MP`
  have hXm : Measurable fun ω : Sizes.SeqΩ d =>
      elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        MLExpDrift_EL E u (Sizes.seqHflow d n u ω) σ a := by
    simp only [MLExpDrift_elklkN_two, MLExpDrift_EL]
    refine (measurable_const.mul (MLExpDrift_measurable_sbSum (fun x => hLKm _ _)
      (fun y => hLKm _ _))).add (measurable_const.mul
      ((MLExpDrift_measurable_sbSum (fun x => havm _ _) (fun y => hLKm _ _)).add
        (MLExpDrift_measurable_sbSum (fun x => havm _ _) (fun y => hLKm _ _))))
  have hMPm : Measurable fun ω : Sizes.SeqΩ d =>
      MLExpDrift_MP E u (Sizes.seqHflow d n u ω) σ a := by
    simp only [MLExpDrift_MP]
    exact measurable_const.mul ((MLExpDrift_measurable_sbSum (fun x => havm _ _)
        (fun y => measurable_const)).add
      (MLExpDrift_measurable_sbSum (fun x => havm _ _) (fun y => measurable_const)))
  have hXint : Integrable (fun ω : Sizes.SeqΩ d =>
      elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        MLExpDrift_EL E u (Sizes.seqHflow d n u ω) σ a) (Sizes.seqP d) :=
    Integrable.of_bound hXm.aestronglyMeasurable (12 * N ^ 5) (Eventually.of_forall fun ω =>
      (MLExpDrift_env_X d n hE hu hη hN hWL hK ω σ a).1)
  have hMPint : Integrable (fun ω : Sizes.SeqΩ d =>
      MLExpDrift_MP E u (Sizes.seqHflow d n u ω) σ a) (Sizes.seqP d) :=
    Integrable.of_bound hMPm.aestronglyMeasurable (4 * N ^ 5) (Eventually.of_forall fun ω =>
      (MLExpDrift_env_X d n hE hu hη hN hWL hK ω σ a).2)
  -- the mean part
  have hmean : ∫ ω, MLExpDrift_MP E u (Sizes.seqHflow d n u ω) σ a ∂(Sizes.seqP d) =
      MLExpDrift_MPmean (d.W n) E u (MLExpDrift_mu d n E u) σ a := by
    simp only [MLExpDrift_MP, MLExpDrift_MPmean]
    rw [integral_const_mul, integral_add (MLExpDrift_integrable_sbSum _ (fun x => hav_int _ _))
      (MLExpDrift_integrable_sbSum _ (fun x => hav_int _ _)),
      MLExpDrift_integral_sbSum _ (fun x => hav_int _ _),
      MLExpDrift_integral_sbSum _ (fun x => hav_int _ _)]
    rfl
  unfold expDriftT
  have hsplit : ∀ ω : Sizes.SeqΩ d,
      elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        egtN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) =
      (elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        MLExpDrift_EL E u (Sizes.seqHflow d n u ω) σ a) +
        MLExpDrift_MP E u (Sizes.seqHflow d n u ω) σ a := by
    intro ω
    rw [MLExpDrift_egtN_split, add_assoc]
  simp only [hsplit]
  rw [integral_add hXint hMPint, hmean]

end Decomp

/-! ## 7. The good event (per size and time) -/

section Core

variable (d : Sizes)

/-- The union bound over a finite family of finite index sets (as the private
`bcalEDecay_union`, `Induction/BcalEDecay.lean`). -/
private theorem MLExpDrift_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Finset ℕ)
    {I : ℕ → Type*} [∀ m, Fintype (I m)] (A : ∀ m, I m → Set Ω) {ε C : ℝ} (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hcard : ∀ m ∈ T, (Fintype.card (I m) : ℝ) ≤ C)
    (hA : ∀ m ∈ T, ∀ q, P (A m q) ≤ ENNReal.ofReal ε) :
    P (⋃ m ∈ T, ⋃ q, A m q) ≤ ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
  calc P (⋃ m ∈ T, ⋃ q, A m q) ≤ ∑ m ∈ T, P (⋃ q, A m q) := measure_biUnion_finset_le T _
    _ ≤ ∑ m ∈ T, ∑ q, P (A m q) := Finset.sum_le_sum fun m _ => measure_iUnion_fintype_le P _
    _ ≤ ∑ m ∈ T, ∑ _q : I m, ENNReal.ofReal ε :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun q _ => hA m hm q
    _ = ∑ m ∈ T, ENNReal.ofReal ((Fintype.card (I m) : ℝ) * ε) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ m ∈ T, ENNReal.ofReal (C * ε) := Finset.sum_le_sum fun m hm =>
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcard m hm) hε)
    _ = ENNReal.ofReal ((T.card : ℝ) * C * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc,
          ENNReal.ofReal_mul (p := (T.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The index set of an `m`-loop has at most `N^{2K}` elements for `m ≤ K`, `N ≥ 2` (as the
private `bcalEDecay_card_le`, `Induction/BcalEDecay.lean`). -/
private theorem MLExpDrift_card_le (n m K : ℕ) (hm : m ≤ K) (hN : 2 ≤ d.size n) :
    (Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (2 * K) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) =
      2 ^ m * (d.L n * d.L n) ^ m := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card ((Fin m → Bool) × (Fin m → Z2 (d.L n))) ≤ d.size n ^ (2 * K) := by
    rw [hcard]
    calc 2 ^ m * (d.L n * d.L n) ^ m ≤ d.size n ^ m * d.size n ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hN m) (Nat.pow_le_pow_left hLL m)
      _ = d.size n ^ (2 * m) := by ring
      _ ≤ d.size n ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  exact_mod_cast hnat

/-- `6 N^6 N^{-(D_p+7)} ≤ N^{-D_p}` for `N ≥ 6`. -/
private theorem MLExpDrift_prob_num {N Dp : ℝ} (hN : 6 ≤ N) :
    (3 : ℝ) * N ^ (2 * 3) * (2 * N ^ (-(Dp + 7))) ≤ N ^ (-Dp) := by
  have hN0 : 0 < N := by linarith
  have e : N ^ (2 * 3) * N ^ (-(Dp + 7)) = N ^ (-Dp) * N⁻¹ := by
    rw [show (N ^ (2 * 3) : ℝ) = N ^ ((6 : ℕ) : ℝ) by norm_num, ← Real.rpow_add hN0,
      ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have h1 : (6 : ℝ) * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have h2 : 0 ≤ N ^ (-Dp) := Real.rpow_nonneg hN0.le _
  calc (3 : ℝ) * N ^ (2 * 3) * (2 * N ^ (-(Dp + 7))) = 6 * (N ^ (2 * 3) * N ^ (-(Dp + 7))) := by ring
    _ = N ^ (-Dp) * (6 * N⁻¹) := by rw [e]; ring
    _ ≤ N ^ (-Dp) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = N ^ (-Dp) := mul_one _

/-- **The good event.**  Eventually in `n`, for every `u ∈ [0,t_n]` there is an event `S` of
probability `≤ N^{-D_p}` off which every loop of length `m ≤ 3` has `‖𝓛 - 𝒦‖ ≤ N^{τ_4} M_u^{-m}`
(`Step4PT`) and, when its labels have spread `≥ ℓ_u W^{τ_1}`, `‖𝓛‖ + ‖𝓛 - 𝒦‖ ≤ N^{τ_d} W^{-D''}`
(`DecayLoopPT`).  A union bound over `≤ 3 N^6` loops, two events each. -/
private theorem MLExpDrift_core {E t : ℕ → ℝ} (hsz : Tendsto d.size atTop atTop)
    (h4 : Step4PT d E (fun _ => 0) t) (hDL : DecayLoopPT d E (fun _ => 0) t)
    {τ₄ τ₁ τd D'' Dp : ℝ} (hτ₄ : 0 < τ₄) (hτ₁ : 0 < τ₁) (hτd : 0 < τd) (hD'' : 0 < D'')
    (hDp : 0 < Dp) :
    ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (t n), ∃ S : Set (Sizes.SeqΩ d),
        Sizes.seqP d S ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dp)) ∧
        ∀ ω ∉ S, ∀ m ∈ Finset.Icc 1 3, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
          ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤
            ((d.size n : ℕ) : ℝ) ^ τ₄ * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ m ∧
          (ellT (d.L n) u * (d.W n : ℝ) ^ τ₁ ≤ (KLoop.maxDist (d.L n) a : ℝ) →
            ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤
                ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D'') ∧
              ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ ≤
                ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D'')) := by
  set D₁ : ℝ := Dp + 7 with hD₁
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  have e4 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 3,
      ∀ p : TimeIcc (fun _ => (0 : ℝ)) t n × (Fin m → Bool) × (Fin m → Z2 (d.L n)),
        Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ τ₄ * (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ m <
          lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
    rw [eventually_all_finset]
    intro m hm
    exact h4 m (Finset.mem_Icc.1 hm).1 τ₄ hτ₄ D₁ hD₁pos
  have e8 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 3,
      ∀ p : TimeIcc (fun _ => (0 : ℝ)) t n × (Fin m → Bool) × (Fin m → Z2 (d.L n)),
        Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 +
            lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2) *
          (if ellT (d.L n) p.1 * (d.W n : ℝ) ^ τ₁ ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ)
            then 1 else 0)} ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
    rw [eventually_all_finset]
    intro m hm
    exact hDL m (Finset.mem_Icc.1 hm).1 τ₁ hτ₁ D'' hD'' τd hτd D₁ hD₁pos
  filter_upwards [e4, e8, hsz.eventually_ge_atTop 6] with n h4n h8n hN6'
  have hN6 : (6 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN6'
  refine ⟨hN6, fun u hu => ?_⟩
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : 2 ≤ d.size n := by
    have : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  set S : Set (Sizes.SeqΩ d) := ⋃ m ∈ Finset.Icc 1 3,
    ⋃ q : (Fin m → Bool) × (Fin m → Z2 (d.L n)),
      ({ω | N ^ τ₄ * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ m <
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2} ∪
        {ω | N ^ τd * (d.W n : ℝ) ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
            lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
          (if ellT (d.L n) u * (d.W n : ℝ) ^ τ₁ ≤ (KLoop.maxDist (d.L n) q.2 : ℝ)
            then 1 else 0)}) with hS
  refine ⟨S, ?_, fun ω hω m hm σ a => ?_⟩
  · have hU := MLExpDrift_union (Sizes.seqP d) (Finset.Icc 1 3)
      (I := fun m => (Fin m → Bool) × (Fin m → Z2 (d.L n)))
      (fun m q => {ω | N ^ τ₄ * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ m <
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2} ∪
        {ω | N ^ τd * (d.W n : ℝ) ^ (-D'') <
          (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2 +
            lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) q.1 q.2) *
          (if ellT (d.L n) u * (d.W n : ℝ) ^ τ₁ ≤ (KLoop.maxDist (d.L n) q.2 : ℝ)
            then 1 else 0)})
      (ε := 2 * N ^ (-D₁)) (C := N ^ (2 * 3)) (by positivity) (by positivity)
      (fun m hm => MLExpDrift_card_le d n m 3 (Finset.mem_Icc.1 hm).2 hN2)
      (fun m hm q => by
        refine (measure_union_le _ _).trans ?_
        have h1 := h4n m hm (⟨u, hu⟩, q.1, q.2)
        have h2 := h8n m hm (⟨u, hu⟩, q.1, q.2)
        calc _ ≤ ENNReal.ofReal (N ^ (-D₁)) + ENNReal.ofReal (N ^ (-D₁)) := add_le_add h1 h2
          _ = ENNReal.ofReal (2 * N ^ (-D₁)) := by
              rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
              ring_nf)
    refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Nat.card_Icc]
    have := MLExpDrift_prob_num (Dp := Dp) hN6
    simpa [hD₁] using this
  · simp only [hS, Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or,
      not_lt] at hω
    have h1 := (hω m hm (σ, a)).1
    have h2 := (hω m hm (σ, a)).2
    refine ⟨?_, fun hfar => ?_⟩
    · exact h1
    · simp only [hfar, ↓reduceIte, mul_one] at h2
      have hLL : loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ a =
          ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ := rfl
      have hLK : lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ a =
          ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)‖ := rfl
      rw [hLL, hLK] at h2
      exact ⟨by linarith [norm_nonneg (LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω)
          (loopOf σ a))], by linarith [norm_nonneg (LLf (d.L n) (d.W n) (E n) u
          (Sizes.seqHflow d n u ω) (loopOf σ a))]⟩

end Core

/-! ## 8. Numerical helpers (as the private helpers of `Induction/BcalEDecay.lean`, and window
arithmetic) -/

section Num

/-- `W^{-(D' + e/c)} N^e ≤ W^{-D'}` from `N^c ≤ W` (as the private `bcalEDecay_WD`). -/
private theorem MLExpDrift_WD {N W c D' e : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (he : 0 ≤ e) (hNW : N ^ c ≤ W) : W ^ (-(D' + e / c)) * N ^ e ≤ W ^ (-D') := by
  have h1 : N ^ e ≤ W ^ (e / c) := by
    calc N ^ e = (N ^ c) ^ (e / c) := by
          rw [← Real.rpow_mul hN]; congr 1; field_simp
      _ ≤ W ^ (e / c) := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hNW (div_nonneg he hc.le)
  have h2 : W ^ (-(D' + e / c)) = W ^ (-D') * (W ^ (e / c))⁻¹ := by
    rw [show -(D' + e / c) = -D' + -(e / c) by ring, Real.rpow_add hW, Real.rpow_neg hW.le (e / c)]
  rw [h2]
  have h3 : 0 < W ^ (e / c) := Real.rpow_pos_of_pos hW _
  have h4 : 0 ≤ W ^ (-D') * (W ^ (e / c))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hW.le _) (inv_nonneg.2 h3.le)
  calc W ^ (-D') * (W ^ (e / c))⁻¹ * N ^ e ≤ W ^ (-D') * (W ^ (e / c))⁻¹ * W ^ (e / c) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = W ^ (-D') := by field_simp

/-- `((1-u) Im m)^{-1} ≤ N` from `N^{-1+τ} ≤ 1-u`, `μ ≤ Im m`, `1 ≤ μ N^τ` (as the private
`bcalEDecay_eta_inv`). -/
private theorem MLExpDrift_eta_inv {N x μ m τ : ℝ} (hN : 0 < N) (hx : N ^ (-1 + τ) ≤ x)
    (hμ : 0 < μ) (hm : μ ≤ m) (hμN : 1 ≤ μ * N ^ τ) : (x * m)⁻¹ ≤ N := by
  have e : N * N ^ (-1 + τ) = N ^ τ := by
    rw [Real.rpow_add hN, Real.rpow_neg_one]; field_simp
  have hp : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN _
  have hx0 : 0 < x := lt_of_lt_of_le hp hx
  have hxm : 0 < x * m := mul_pos hx0 (lt_of_lt_of_le hμ hm)
  have key : 1 ≤ N * (x * m) := by
    rw [← e] at hμN
    have : μ * (N * N ^ (-1 + τ)) ≤ m * (N * x) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left hx hN.le) (by positivity) (by linarith)
    nlinarith
  calc (x * m)⁻¹ = (x * m)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (x * m)⁻¹ * (N * (x * m)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hxm.le)
    _ = N := by rw [mul_comm N, ← mul_assoc, inv_mul_cancel₀ hxm.ne', one_mul]

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ` (copy of the private
`bcalEDecay_im_bounds`). -/
private theorem MLExpDrift_im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hκ : 0 < κ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ (spectralM (E n)).im ∧ (spectralM (E n)).im ≤ 1 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun n => ⟨?_, ?_⟩⟩
  · have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  · rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith
  · exact MLExpVocab_im_le_one (E n)

/-- **The window arithmetic**: `W² (2ℓQ+1)² P² M^{-4} ≤ 9 P² Q² η^{-1} M^{-3}` for `M = W² ℓ² η`,
`ℓ, Q ≥ 1` (`W² ℓ² M^{-4} = η^{-1} M^{-3}`). -/
private theorem MLExpDrift_num_window {Wr ℓ η Q P : ℝ} (hW : 0 < Wr) (hℓ : 1 ≤ ℓ) (hη : 0 < η)
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) :
    Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (P ^ 2 * ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4)) ≤
      9 * P ^ 2 * Q ^ 2 * (η⁻¹ * ((Wr ^ 2 * ℓ ^ 2 * η) ^ 3)⁻¹) := by
  have hR : 1 ≤ ℓ * Q := one_le_mul_of_one_le_of_one_le hℓ hQ
  have hM : 0 < Wr ^ 2 * ℓ ^ 2 * η := by positivity
  have h9 : (2 * (ℓ * Q) + 1) ^ 2 ≤ 9 * (ℓ * Q) ^ 2 := by nlinarith
  have hX : Wr ^ 2 * ℓ ^ 2 * ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4 = η⁻¹ * ((Wr ^ 2 * ℓ ^ 2 * η) ^ 3)⁻¹ := by
    field_simp
  have hMi : 0 ≤ ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4 := by positivity
  calc Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (P ^ 2 * ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4))
      ≤ Wr ^ 2 * (9 * (ℓ * Q) ^ 2 * (P ^ 2 * ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4)) := by
        gcongr
    _ = 9 * P ^ 2 * Q ^ 2 * (Wr ^ 2 * ℓ ^ 2 * ((Wr ^ 2 * ℓ ^ 2 * η)⁻¹) ^ 4) := by ring
    _ = _ := by rw [hX]

/-- `N^5 N^{-(9+D)} ≤ N^{-4}` for `N ≥ 1`, `D ≥ 0`. -/
private theorem MLExpDrift_env_num {N D : ℝ} (hN : 1 ≤ N) (hD : 0 ≤ D) :
    N ^ 5 * N ^ (-(9 + D)) ≤ (N ^ 4)⁻¹ := by
  have hN0 : 0 < N := by linarith
  rw [show (N ^ 5 : ℝ) = N ^ ((5 : ℕ) : ℝ) by norm_num, ← Real.rpow_add hN0,
    show (N ^ 4 : ℝ) = N ^ ((4 : ℕ) : ℝ) by norm_num, ← Real.rpow_neg hN0.le]
  exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)

/-- **The bulk arithmetic**: the sum of the window bounds of `X`, of the mean part and of the
envelope term is `≤ N^ε η^{-1} M^{-3}` (`A = N^{ε/4} ≥ 48`, `Q^2 ≤ A`, `N^ε = A^4`). -/
private theorem MLExpDrift_bulk_num {N Wr Lr ℓ η Mu A Q Ne Dp D D'' : ℝ}
    (hN : 32 ≤ N) (hWr : 3 ≤ Wr) (hWL : Wr ^ 2 * Lr ^ 2 = N) (hWN : Wr ^ 2 ≤ N) (hℓ : 1 ≤ ℓ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hMu : Mu = Wr ^ 2 * ℓ ^ 2 * η) (hMuW : Mu ≤ Wr ^ 2)
    (hQ : 1 ≤ Q) (hQA : Q ^ 2 ≤ A) (hA : 48 ≤ A) (hMi : Mu⁻¹ ≤ N) (hNe : Ne = N ^ 4 * A)
    (hWD : Wr ^ (-D'') * Ne ≤ Wr ^ (-(D + 8))) (hD : 0 < D) (hDp : Dp = 9 + D) :
    Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * ((A * Mu⁻¹ ^ 2) * (A * Mu⁻¹ ^ 2) +
          2 * ((A * Mu⁻¹ ^ 1) * (A * Mu⁻¹ ^ 3))) +
        Lr ^ 2 * ((N * Wr ^ (-D'')) * (A * Mu⁻¹ ^ 2) + 2 * ((A * Mu⁻¹ ^ 1) * (N * Wr ^ (-D''))))) +
      12 * N ^ 5 * N ^ (-Dp) +
      Wr ^ 2 * (2 * ((2 * (ℓ * Q) + 1) ^ 2 * ((A * (Mu ^ 2)⁻¹) * (A * Mu⁻¹ ^ 2)) +
        Lr ^ 2 * ((A * (Mu ^ 2)⁻¹) * Wr ^ (-D'')))) ≤
      A ^ 4 * (η⁻¹ * (Mu ^ 3)⁻¹) := by
  have hW0 : 0 < Wr := by linarith
  have hN0 : 0 < N := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hMu0 : 0 < Mu := by rw [hMu]; positivity
  have hMi0 : 0 ≤ Mu⁻¹ := inv_nonneg.2 hMu0.le
  set X : ℝ := η⁻¹ * (Mu ^ 3)⁻¹ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hwin := MLExpDrift_num_window hW0 hℓ hη hQ hA0
  rw [← hMu] at hwin
  -- `(Mu⁻¹)^4` forms
  have hwin' : Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (A ^ 2 * (Mu⁻¹) ^ 4)) ≤ 9 * A ^ 3 * X := by
    refine hwin.trans ?_
    have : 9 * A ^ 2 * Q ^ 2 * X ≤ 9 * A ^ 2 * A * X := by gcongr
    calc _ ≤ 9 * A ^ 2 * A * X := this
      _ = 9 * A ^ 3 * X := by ring
  -- the main terms
  have m1 : Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * ((A * Mu⁻¹ ^ 2) * (A * Mu⁻¹ ^ 2) +
          2 * ((A * Mu⁻¹ ^ 1) * (A * Mu⁻¹ ^ 3)))) ≤ 27 * A ^ 3 * X := by
    have e : (A * Mu⁻¹ ^ 2) * (A * Mu⁻¹ ^ 2) + 2 * ((A * Mu⁻¹ ^ 1) * (A * Mu⁻¹ ^ 3)) =
        3 * (A ^ 2 * (Mu⁻¹) ^ 4) := by ring
    rw [e]
    calc Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (3 * (A ^ 2 * (Mu⁻¹) ^ 4)))
        = 3 * (Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (A ^ 2 * (Mu⁻¹) ^ 4))) := by ring
      _ ≤ 3 * (9 * A ^ 3 * X) := by gcongr
      _ = 27 * A ^ 3 * X := by ring
  have m2 : Wr ^ 2 * (2 * ((2 * (ℓ * Q) + 1) ^ 2 * ((A * (Mu ^ 2)⁻¹) * (A * Mu⁻¹ ^ 2)))) ≤
      18 * A ^ 3 * X := by
    have e : (A * (Mu ^ 2)⁻¹) * (A * Mu⁻¹ ^ 2) = A ^ 2 * (Mu⁻¹) ^ 4 := by
      rw [inv_pow]; ring
    rw [e]
    calc Wr ^ 2 * (2 * ((2 * (ℓ * Q) + 1) ^ 2 * (A ^ 2 * (Mu⁻¹) ^ 4)))
        = 2 * (Wr ^ 2 * ((2 * (ℓ * Q) + 1) ^ 2 * (A ^ 2 * (Mu⁻¹) ^ 4))) := by ring
      _ ≤ 2 * (9 * A ^ 3 * X) := by gcongr
      _ = 18 * A ^ 3 * X := by ring
  -- the tails
  have hWDN : 0 ≤ Wr ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hMi2 : (Mu⁻¹) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hMi0 hMi 2
  have hMiN : Mu⁻¹ ≤ N ^ 2 := by
    have : (1 : ℝ) ≤ N := by linarith
    calc Mu⁻¹ ≤ N := hMi
      _ ≤ N ^ 2 := by nlinarith
  have t1 : Wr ^ 2 * (Lr ^ 2 * ((N * Wr ^ (-D'')) * (A * Mu⁻¹ ^ 2) +
      2 * ((A * Mu⁻¹ ^ 1) * (N * Wr ^ (-D''))))) ≤ 3 * (Ne * Wr ^ (-D'')) := by
    have e : Wr ^ 2 * (Lr ^ 2 * ((N * Wr ^ (-D'')) * (A * Mu⁻¹ ^ 2) +
        2 * ((A * Mu⁻¹ ^ 1) * (N * Wr ^ (-D''))))) =
        N * (N * Wr ^ (-D'') * A * ((Mu⁻¹) ^ 2 + 2 * Mu⁻¹)) := by
      rw [← hWL]; ring
    rw [e, hNe]
    have h3 : (Mu⁻¹) ^ 2 + 2 * Mu⁻¹ ≤ 3 * N ^ 2 := by nlinarith
    calc N * (N * Wr ^ (-D'') * A * ((Mu⁻¹) ^ 2 + 2 * Mu⁻¹))
        ≤ N * (N * Wr ^ (-D'') * A * (3 * N ^ 2)) := by gcongr
      _ = 3 * (N ^ 4 * A * Wr ^ (-D'')) := by ring
  have t2 : Wr ^ 2 * (2 * (Lr ^ 2 * ((A * (Mu ^ 2)⁻¹) * Wr ^ (-D'')))) ≤ 2 * (Ne * Wr ^ (-D'')) := by
    have e : Wr ^ 2 * (2 * (Lr ^ 2 * ((A * (Mu ^ 2)⁻¹) * Wr ^ (-D'')))) =
        2 * (N * (A * (Mu⁻¹) ^ 2 * Wr ^ (-D''))) := by
      rw [← hWL, inv_pow]; ring
    rw [e, hNe]
    have hN1 : (1 : ℝ) ≤ N := by linarith
    calc 2 * (N * (A * (Mu⁻¹) ^ 2 * Wr ^ (-D''))) ≤ 2 * (N * (A * N ^ 2 * Wr ^ (-D''))) := by
          gcongr
      _ = 2 * (N ^ 3 * A * Wr ^ (-D'')) := by ring
      _ ≤ 2 * (N ^ 4 * A * Wr ^ (-D'')) := by
          have : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
          gcongr
  -- the lower bound `X ≥ W^{-6}`
  have hWr1 : (1 : ℝ) ≤ Wr := by linarith
  have hW6 : (Wr ^ 6)⁻¹ ≤ X := by
    have h1 : 1 ≤ η⁻¹ := one_le_inv_iff₀.2 ⟨hη, hη1⟩
    have h3 : Mu ^ 3 ≤ Wr ^ 6 := by
      calc Mu ^ 3 ≤ (Wr ^ 2) ^ 3 := pow_le_pow_left₀ hMu0.le hMuW 3
        _ = Wr ^ 6 := by ring
    have h4 : (Wr ^ 6)⁻¹ ≤ (Mu ^ 3)⁻¹ := inv_anti₀ (by positivity) h3
    calc (Wr ^ 6)⁻¹ ≤ (Mu ^ 3)⁻¹ := h4
      _ = 1 * (Mu ^ 3)⁻¹ := (one_mul _).symm
      _ ≤ η⁻¹ * (Mu ^ 3)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the tail: `5 Ne W^{-D''} ≤ 5 W^{-(D+8)} ≤ W^{-6}`
  have hW8 : 5 * Wr ^ (-(D + 8)) ≤ (Wr ^ 6)⁻¹ := by
    have h1 : Wr ^ (-(D + 8)) ≤ Wr ^ (-(8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hWr1 (by linarith only [hD])
    have h2 : Wr ^ (-(8 : ℝ)) = (Wr ^ 8)⁻¹ := by
      rw [Real.rpow_neg hW0.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 5 * (Wr ^ 8)⁻¹ ≤ (Wr ^ 6)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      rw [show (Wr ^ 6)⁻¹ * Wr ^ 8 = Wr ^ 2 by field_simp]
      nlinarith only [hWr]
    calc 5 * Wr ^ (-(D + 8)) ≤ 5 * (Wr ^ 8)⁻¹ := by rw [← h2]; gcongr
      _ ≤ (Wr ^ 6)⁻¹ := h3
  -- the envelope term
  have henv : 12 * N ^ 5 * N ^ (-Dp) ≤ (Wr ^ 6)⁻¹ := by
    have h1 : N ^ 5 * N ^ (-Dp) ≤ (N ^ 4)⁻¹ := by
      rw [hDp]; exact MLExpDrift_env_num (by linarith) hD.le
    have h2 : 12 * (N ^ 4)⁻¹ ≤ (N ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      rw [show (N ^ 3)⁻¹ * N ^ 4 = N by field_simp]
      linarith
    have h3 : (N ^ 3)⁻¹ ≤ (Wr ^ 6)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      calc Wr ^ 6 = (Wr ^ 2) ^ 3 := by ring
        _ ≤ N ^ 3 := pow_le_pow_left₀ (by positivity) hWN 3
    calc 12 * N ^ 5 * N ^ (-Dp) = 12 * (N ^ 5 * N ^ (-Dp)) := by ring
      _ ≤ 12 * (N ^ 4)⁻¹ := by gcongr
      _ ≤ (N ^ 3)⁻¹ := h2
      _ ≤ (Wr ^ 6)⁻¹ := h3
  -- the sum
  have hNe' : Ne * Wr ^ (-D'') ≤ Wr ^ (-(D + 8)) := by rw [mul_comm]; exact hWD
  have hA3 : 0 ≤ A ^ 3 * X := by positivity
  calc _ ≤ 27 * A ^ 3 * X + 3 * (Ne * Wr ^ (-D'')) + (12 * N ^ 5 * N ^ (-Dp)) +
        (18 * A ^ 3 * X + 2 * (Ne * Wr ^ (-D''))) := by
        have := add_le_add (add_le_add (add_le_add m1 t1) (le_refl (12 * N ^ 5 * N ^ (-Dp))))
          (add_le_add m2 t2)
        refine le_trans (le_of_eq ?_) this
        ring
    _ ≤ 27 * A ^ 3 * X + 3 * Wr ^ (-(D + 8)) + (Wr ^ 6)⁻¹ +
        (18 * A ^ 3 * X + 2 * Wr ^ (-(D + 8))) := by gcongr
    _ = 45 * (A ^ 3 * X) + 5 * Wr ^ (-(D + 8)) + (Wr ^ 6)⁻¹ := by ring
    _ ≤ 45 * (A ^ 3 * X) + (Wr ^ 6)⁻¹ + (Wr ^ 6)⁻¹ := by gcongr
    _ ≤ 45 * (A ^ 3 * X) + X + X := by gcongr
    _ ≤ 47 * (A ^ 3 * X) := by
        have hA31 : (1 : ℝ) ≤ A ^ 3 := one_le_pow₀ (by linarith only [hA])
        have : X ≤ A ^ 3 * X := le_mul_of_one_le_left hX0 hA31
        linarith only [this]
    _ ≤ 48 * (A ^ 3 * X) := by linarith only [hA3]
    _ ≤ A * (A ^ 3 * X) := mul_le_mul_of_nonneg_right hA hA3
    _ = A ^ 4 * X := by ring

/-- **The decay arithmetic**: the far bound plus the envelope term is `≤ W^{-D}`. -/
private theorem MLExpDrift_far_num {N Wr Lr A Ne Dp D D'' : ℝ}
    (hN : 32 ≤ N) (hWr : 3 ≤ Wr) (hWL : Wr ^ 2 * Lr ^ 2 = N) (hWN : Wr ^ 2 ≤ N) (hA : 1 ≤ A)
    (hNe : Ne = N ^ 4 * A) (hWD : Wr ^ (-D'') * Ne ≤ Wr ^ (-(D + 8))) (hD : 0 < D)
    (hDp : Dp = 9 + D) :
    Wr ^ 2 * Lr ^ 2 * ((2 * N ^ 2) * (N * Wr ^ (-D'')) + 2 * ((2 * N ^ 1) * (N * Wr ^ (-D'')))) +
      16 * N ^ 5 * N ^ (-Dp) ≤ Wr ^ (-D) := by
  have hW0 : 0 < Wr := by linarith only [hWr]
  have hN0 : 0 < N := by linarith only [hN]
  have hN1 : (1 : ℝ) ≤ N := by linarith only [hN]
  have hWr1 : (1 : ℝ) ≤ Wr := by linarith only [hWr]
  have hWDN : 0 ≤ Wr ^ (-D'') := Real.rpow_nonneg hW0.le _
  -- the far term
  have f1 : Wr ^ 2 * Lr ^ 2 * ((2 * N ^ 2) * (N * Wr ^ (-D'')) +
      2 * ((2 * N ^ 1) * (N * Wr ^ (-D'')))) ≤ 6 * (Ne * Wr ^ (-D'')) := by
    rw [hWL, hNe]
    have h1 : N ^ 1 ≤ N ^ 2 := pow_le_pow_right₀ hN1 (by norm_num)
    calc N * ((2 * N ^ 2) * (N * Wr ^ (-D'')) + 2 * ((2 * N ^ 1) * (N * Wr ^ (-D''))))
        ≤ N * ((2 * N ^ 2) * (N * Wr ^ (-D'')) + 2 * ((2 * N ^ 2) * (N * Wr ^ (-D'')))) := by
          gcongr
      _ = 6 * (N ^ 4 * Wr ^ (-D'')) := by ring
      _ ≤ 6 * (N ^ 4 * A * Wr ^ (-D'')) := by
          have : N ^ 4 * 1 ≤ N ^ 4 * A := mul_le_mul_of_nonneg_left hA (by positivity)
          have h2 : N ^ 4 * Wr ^ (-D'') ≤ N ^ 4 * A * Wr ^ (-D'') := by
            rw [mul_one] at this
            exact mul_le_mul_of_nonneg_right this hWDN
          linarith only [h2]
  have hNe' : Ne * Wr ^ (-D'') ≤ Wr ^ (-(D + 8)) := by rw [mul_comm]; exact hWD
  have hWD8 : 6 * Wr ^ (-(D + 8)) ≤ (1 / 2) * Wr ^ (-D) := by
    have e : Wr ^ (-(D + 8)) = Wr ^ (-D) * (Wr ^ 8)⁻¹ := by
      rw [show -(D + 8) = -D + -(8 : ℝ) by ring, Real.rpow_add hW0, Real.rpow_neg hW0.le 8,
        show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h8 : (12 : ℝ) ≤ Wr ^ 8 := by
      have : (3 : ℝ) ^ 8 ≤ Wr ^ 8 := pow_le_pow_left₀ (by norm_num) hWr 8
      linarith only [this]
    have h9 : 0 ≤ Wr ^ (-D) := Real.rpow_nonneg hW0.le _
    have h10 : (Wr ^ 8)⁻¹ ≤ (12 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h8
    rw [e]
    calc 6 * (Wr ^ (-D) * (Wr ^ 8)⁻¹) ≤ 6 * (Wr ^ (-D) * (12 : ℝ)⁻¹) := by gcongr
      _ = (1 / 2) * Wr ^ (-D) := by ring
  -- the envelope term
  have e1 : N ^ 5 * N ^ (-Dp) ≤ (N ^ 4)⁻¹ * N ^ (-(D / 2)) := by
    rw [hDp, show (N ^ 5 : ℝ) = N ^ ((5 : ℕ) : ℝ) by norm_num, ← Real.rpow_add hN0,
      show ((N ^ 4 : ℝ))⁻¹ = N ^ (-((4 : ℕ) : ℝ)) by
        rw [Real.rpow_neg hN0.le, Real.rpow_natCast], ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith only [hD])
  have e2 : N ^ (-(D / 2)) ≤ Wr ^ (-D) := by
    have h1 : Wr ^ D ≤ N ^ (D / 2) := by
      have := MLExpVocab_rpow_le (x := D) hWr1 hWN
      rwa [abs_of_pos hD] at this
    rw [Real.rpow_neg hN0.le, Real.rpow_neg hW0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) h1
  have e3 : 16 * (N ^ 4)⁻¹ ≤ 1 / 2 := by
    have h : (32 : ℝ) ≤ N ^ 4 := by
      calc (32 : ℝ) ≤ N := hN
        _ = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith only [h]
  have f2 : 16 * N ^ 5 * N ^ (-Dp) ≤ (1 / 2) * Wr ^ (-D) := by
    have hp : 0 ≤ N ^ (-(D / 2)) := Real.rpow_nonneg hN0.le _
    calc 16 * N ^ 5 * N ^ (-Dp) = 16 * (N ^ 5 * N ^ (-Dp)) := by ring
      _ ≤ 16 * ((N ^ 4)⁻¹ * N ^ (-(D / 2))) := by gcongr
      _ = (16 * (N ^ 4)⁻¹) * N ^ (-(D / 2)) := by ring
      _ ≤ (1 / 2) * N ^ (-(D / 2)) := mul_le_mul_of_nonneg_right e3 hp
      _ ≤ (1 / 2) * Wr ^ (-D) := by gcongr
  calc _ ≤ 6 * (Ne * Wr ^ (-D'')) + (1 / 2) * Wr ^ (-D) := add_le_add f1 f2
    _ ≤ 6 * Wr ^ (-(D + 8)) + (1 / 2) * Wr ^ (-D) := by gcongr
    _ ≤ (1 / 2) * Wr ^ (-D) + (1 / 2) * Wr ^ (-D) := by gcongr
    _ = Wr ^ (-D) := by ring

end Num

/-! ## 9. The main theorem -/

section Main

variable (d : Sizes)

/-- `max_{p,q} |a_p - a_q|_L = |a_0 - a_1|_L` for a pair of labels. -/
private theorem MLExpDrift_maxDist_two {L : ℕ} [NeZero L] (a : Fin 2 → Z2 L) :
    (KLoop.maxDist L a : ℝ) ≤ (zdist2 L (a 0 - a 1) : ℝ) := by
  have h : KLoop.maxDist L a ≤ zdist2 L (a 0 - a 1) := by
    unfold KLoop.maxDist
    refine Finset.sup_le fun p _ => ?_
    have h01 : zdist2 L (a 1 - a 0) = zdist2 L (a 0 - a 1) := MLExpDrift_zdist2_sub_comm _ _
    fin_cases p <;> simp [h01]
  exact_mod_cast h

private theorem MLExpDrift_tmax_le {L k : ℕ} [NeZero L] {A : (Fin k → Z2 L) → ℂ} {X : ℝ}
    (h : ∀ a, ‖A a‖ ≤ X) : tmax L A ≤ X :=
  Finset.sup'_le _ _ fun a _ => h a

/-- **`ExpDriftBound`** (the expected drift terms).  Under `MLExpHyps`, for every
`ε, τ', D > 0`, eventually in `n`, for every `u ∈ [0,t_n]` and every `σ ∈ {±}²`, the drift
`𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ}` (`expDriftT`) has `(u,τ',D)` decay and
`‖·‖_max ≤ N^ε η_u^{-1} M_u^{-3}`.
Argument: the window argument of `Induction/BcalEDecay.lean` (copied), `Step4PT`, `DecayLoopPT`,
`KboundConcl`, `Step61Concl` (uniform by `step61_unif`), `kcalDecay`; module docstring. -/
theorem expDriftBound (κ c τ : ℝ) (E t : ℕ → ℝ) : ExpDriftBound d κ c τ E t := by
  intro hH ε hε τ' hτ' D hD
  obtain ⟨hκ, hc, hτ, hE, ht0, ht1, hsz, hbw, hrc, hK, h4, hDL, h61⟩ := hH
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hKd : KcalDecay κ := kcalDecay κ
  -- the parameters
  set τ₁ : ℝ := min (τ' / 2) (ε / 4) with hτ₁
  have hτ₁pos : 0 < τ₁ := lt_min (by positivity) (by positivity)
  have hτ₁le : τ₁ ≤ ε / 4 := min_le_right _ _
  have hτ₁le' : τ₁ ≤ τ' / 2 := min_le_left _ _
  set e : ℝ := 4 + ε / 4 with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  set D'' : ℝ := D + 8 + e / c with hD''
  have hD''pos : 0 < D'' := by rw [hD'']; positivity
  set Dp : ℝ := 9 + D with hDp
  have hDppos : 0 < Dp := by rw [hDp]; positivity
  obtain ⟨μ, hμ, hμb⟩ := MLExpDrift_im_bounds hE hκ
  -- the good event
  have core := MLExpDrift_core d hsize h4 hDL (τ₄ := ε / 4) (τ₁ := τ₁) (τd := 1) (D'' := D'')
    (Dp := Dp) (by positivity) hτ₁pos one_pos hD''pos hDppos
  -- the eventual facts
  have f48 : ∀ᶠ n : ℕ in atTop, (48 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 4) :=
    hsize.eventually (eventually_le_rpow 48 (by positivity))
  have f3τ : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (c * (τ' / 2)) :=
    hsize.eventually (eventually_le_rpow 3 (by positivity))
  have f32 : ∀ᶠ n : ℕ in atTop, (32 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hsz.eventually_ge_atTop 32
  have f3c : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ c :=
    hsize.eventually (eventually_le_rpow 3 hc)
  have fμ : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hsz).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have fK1 : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 3, ∀ u ∈ Set.Icc (0 : ℝ) (t n),
      ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := by
    rw [eventually_all_finset]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    filter_upwards [hsize.eventually (hK m hm1 1 one_pos)] with n hn u hu σ a
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
    have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
      u, hu0, hu1⟩, σ, a⟩
    have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * (KLoop.Mt (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) := h
    rwa [kloop_Mt_eq hu1.le] at h'
  have fK3 : ∀ᶠ n : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (t n),
      ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Z2 (d.L n)),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (ε / 4) * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ 2 := by
    filter_upwards [hsize.eventually (hK 3 (by norm_num) (ε / 4) (by positivity))] with n hn u hu σ a
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
    have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
      u, hu0, hu1⟩, σ, a⟩
    have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 4) * (KLoop.Mt (d.L n) (d.W n) (E n) u)⁻¹ ^ (3 - 1) := h
    rwa [kloop_Mt_eq hu1.le] at h'
  have fKd : ∀ᶠ n : ℕ in atTop,
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = d.size n →
        ((d.size n : ℕ) : ℝ) ^ c ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
        ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Z2 L),
          ellT L u * (W : ℝ) ^ τ₁ ≤ (KLoop.maxDist L a : ℝ) →
            ‖KLoop.Kcal L W E u (loopOf σ a)‖ ≤ (W : ℝ) ^ (-D'') :=
    hsize.eventually (hKd hκ c hc 3 (by norm_num) τ₁ D'' hτ₁pos hD''pos)
  have f61 := step61_unif d ht0 h61 (ε / 4) (by positivity)
  filter_upwards [core, f48, f3τ, f3c, f32, hbw, hrc, fμ, fK1, fK3, fKd, f61] with n hcore h48 h3τ
    h3c h32 hbwn hrcn hμn hK1n hK3n hKdn h61n u hu σ
  obtain ⟨hN6, hcoreu⟩ := hcore
  obtain ⟨S, hS, hgood⟩ := hcoreu u hu
  have hK1u := fun m hm => hK1n m hm u hu
  have hK3u := hK3n u hu
  have h61u := h61n u hu
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 n)
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hWpos : 0 < d.W n := d.W_pos n
  have hEn' : |E n| ≤ 2 - κ := hE n
  have hEn : |E n| < 2 := by linarith [hE n]
  have hWLnat : d.W n ^ 2 * d.L n ^ 2 = d.size n := (Sizes.size_eq d n).symm
  have hℓ : 1 ≤ ellT (d.L n) u := one_le_ellT hL1 hu0 hu1
  have hMuW : scaleM (d.L n) (d.W n) (E n) u ≤ ((d.W n : ℕ) : ℝ) ^ 2 :=
    MLExpVocab_scaleM_le_W2 hL1 hu1
  have hη0 : 0 < etaT (E n) u := etaT_pos hEn hu1
  have hMupos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hL1 hWpos hEn hu1
  have hIm : (spectralM (E n)).im ≤ 1 := (hμb n).2
  have hη1 : etaT (E n) u ≤ 1 := by
    unfold etaT
    have h1 : 1 - u ≤ 1 := by linarith
    have h2 : 0 < (spectralM (E n)).im := spectralM_im_pos hEn
    nlinarith
  -- abbreviations
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Wr : ℝ := ((d.W n : ℕ) : ℝ) with hWrdef
  set Lr : ℝ := ((d.L n : ℕ) : ℝ) with hLrdef
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hW1 : 1 ≤ Wr := by rw [hWrdef]; exact_mod_cast hWpos
  have hW0 : 0 < Wr := by linarith
  have hW3 : 3 ≤ Wr := h3c.trans hbwn
  have hL1r : 1 ≤ Lr := by rw [hLrdef]; exact_mod_cast hL1
  have hWL : Wr ^ 2 * Lr ^ 2 = N := by
    rw [hWrdef, hLrdef, hNdef]; exact_mod_cast hWLnat
  have hWN : Wr ^ 2 ≤ N := by
    rw [← hWL]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hL1r)
  have hx : N ^ (-1 + τ) ≤ 1 - u := hrcn.trans (by linarith [hu.2])
  have hη : ((1 - u) * (spectralM (E n)).im)⁻¹ ≤ N :=
    MLExpDrift_eta_inv hN0 hx hμ (hμb n).1 hμn
  have hMuη : etaT (E n) u ≤ scaleM (d.L n) (d.W n) (E n) u := by
    unfold scaleM
    have h1 : (1 : ℝ) ≤ Wr ^ 2 * ellT (d.L n) u ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ hℓ)
    nlinarith
  have hMi : (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ≤ N := (inv_anti₀ hη0 hMuη).trans hη
  have hMi0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) u)⁻¹ := inv_nonneg.2 hMupos.le
  have hKenv : ∀ m ∈ Finset.Icc 1 3, ∀ (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) (E n) u (loopOf σ a)‖ ≤ N ^ m := by
    intro m hm σ a
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have h := hK1u m hm σ a
    rw [Real.rpow_one] at h
    refine h.trans ?_
    calc N * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (m - 1) ≤ N * N ^ (m - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMi0 hMi _) hN0.le
      _ = N ^ m := by rw [← pow_succ']; congr 1; omega
  have hSreal : (Sizes.seqP d S).toReal ≤ N ^ (-Dp) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hS
  -- the window radius and the decay of the good sample
  set A : ℝ := N ^ (ε / 4) with hAdef
  have hA0 : 0 ≤ A := Real.rpow_nonneg hN0.le _
  have hQ1 : 1 ≤ Wr ^ τ₁ := Real.one_le_rpow hW1 hτ₁pos.le
  have hQA : (Wr ^ τ₁) ^ 2 ≤ A := by
    have h1 : (Wr ^ τ₁) ^ 2 = Wr ^ (2 * τ₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have h2 : Wr ^ (2 * τ₁) ≤ N ^ (|2 * τ₁| / 2) := MLExpVocab_rpow_le hW1 hWN
    have h3 : |2 * τ₁| / 2 = τ₁ := by rw [abs_of_pos (by linarith)]; ring
    rw [h3] at h2
    exact h1 ▸ h2.trans (Real.rpow_le_rpow_of_exponent_le hN1 hτ₁le)
  have hG2 : ∀ ω ∉ S, ∀ m ∈ Finset.Icc 1 3, ∀ (σ' : Fin m → Bool) (a' : Fin m → Z2 (d.L n)),
      ellT (d.L n) u * Wr ^ τ₁ ≤ (KLoop.maxDist (d.L n) a' : ℝ) →
        ‖LLf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ' a')‖ ≤
            N * Wr ^ (-D'') ∧
          ‖LKf (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ' a')‖ ≤
            N * Wr ^ (-D'') := by
    intro ω hω m hm σ' a' hfar
    have := (hgood ω hω m hm σ' a').2 hfar
    rwa [Real.rpow_one] at this
  have hR0 : 0 ≤ ellT (d.L n) u * Wr ^ τ₁ := by positivity
  have hδ0 : 0 ≤ N * Wr ^ (-D'') := by positivity
  have hWD : Wr ^ (-D'') * (N ^ 4 * A) ≤ Wr ^ (-(D + 8)) := by
    have h := MLExpDrift_WD (N := N) (W := Wr) (c := c) (D' := D + 8) (e := e) hN0.le hW0 hc he0
      hbwn
    have e1 : N ^ e = N ^ 4 * A := by
      have h4 : N ^ (4 : ℝ) = N ^ 4 := by
        have := Real.rpow_natCast N 4
        simp only [Nat.cast_ofNat] at this
        exact this
      rw [he, Real.rpow_add hN0, h4]
    rwa [e1] at h
  -- the bulk bound
  have hNε : N ^ ε = A ^ 4 := by
    rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hbulk : ∀ a : Fin 2 → Z2 (d.L n), ‖expDriftT d n (E n) u σ a‖ ≤
      N ^ ε * ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) := by
    intro a
    rw [MLExpDrift_expDriftT_eq d n hEn hu1 hη hN1 hWL hKenv σ a]
    set Mu : ℝ := scaleM (d.L n) (d.W n) (E n) u with hMudef
    have hX : ‖∫ ω, (elklkN (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a) +
          MLExpDrift_EL (E n) u (Sizes.seqHflow d n u ω) σ a) ∂(Sizes.seqP d)‖ ≤
        Wr ^ 2 * ((2 * (ellT (d.L n) u * Wr ^ τ₁) + 1) ^ 2 *
            ((A * Mu⁻¹ ^ 2) * (A * Mu⁻¹ ^ 2) + 2 * ((A * Mu⁻¹ ^ 1) * (A * Mu⁻¹ ^ 3))) +
          Lr ^ 2 * ((N * Wr ^ (-D'')) * (A * Mu⁻¹ ^ 2) +
            2 * ((A * Mu⁻¹ ^ 1) * (N * Wr ^ (-D''))))) + 12 * N ^ 5 * N ^ (-Dp) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hfm := MLExpDrift_first_moment (P := Sizes.seqP d)
        (f := fun ω => elklkN (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a) +
          MLExpDrift_EL (E n) u (Sizes.seqHflow d n u ω) σ a) (S := S)
        (c := Wr ^ 2 * ((2 * (ellT (d.L n) u * Wr ^ τ₁) + 1) ^ 2 *
            ((A * Mu⁻¹ ^ 2) * (A * Mu⁻¹ ^ 2) + 2 * ((A * Mu⁻¹ ^ 1) * (A * Mu⁻¹ ^ 3))) +
          Lr ^ 2 * ((N * Wr ^ (-D'')) * (A * Mu⁻¹ ^ 2) +
            2 * ((A * Mu⁻¹ ^ 1) * (N * Wr ^ (-D''))))))
        (B := 12 * N ^ 5) (by positivity) (by positivity)
        (fun ω => (MLExpDrift_env_X d n hEn hu1 hη hN1 hWL hKenv ω σ a).1)
        (fun ω hω => by
          have h1 : ∀ (s : Bool) (x : Z2 (d.L n)),
              ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) s x‖ ≤ A * Mu⁻¹ ^ 1 := by
            intro s x
            rw [MLExpDrift_avgErr_eq]
            exact (hgood ω hω 1 (by simp) ![s] ![x]).1
          exact MLExpDrift_A_bulk hL3 (E n) u (Sizes.seqHflow d n u ω) σ a hR0 hδ0 h1
            (fun σ' a' => (hgood ω hω 2 (by simp) σ' a').1)
            (fun σ' a' => (hgood ω hω 3 (by simp) σ' a').1)
            (fun σ' a' hf => (hG2 ω hω 2 (by simp) σ' a' hf).2)
            (fun σ' a' hf => (hG2 ω hω 3 (by simp) σ' a' hf).2))
      calc _ ≤ _ := hfm
        _ ≤ _ := by gcongr
    have hMP : ‖MLExpDrift_MPmean (d.W n) (E n) u (MLExpDrift_mu d n (E n) u) σ a‖ ≤
        Wr ^ 2 * (2 * ((2 * (ellT (d.L n) u * Wr ^ τ₁) + 1) ^ 2 *
            ((A * (Mu ^ 2)⁻¹) * (A * Mu⁻¹ ^ 2)) +
          Lr ^ 2 * ((A * (Mu ^ 2)⁻¹) * Wr ^ (-D'')))) := by
      refine MLExpDrift_MP_bound hL3 (E n) u (MLExpDrift_mu d n (E n) u) σ a hR0
        (by positivity) ?_ ?_ ?_
      · intro s x
        exact (MLExpDrift_norm_mu d n hEn hu1 hη hN1 s x).le.trans (h61u x)
      · intro σ' a'
        exact hK3u σ' a'
      · intro σ' a' hf
        exact hKdn (d.L n) (d.W n) hL3 hWLnat hbwn (E n) hEn' u hu0 hu1 σ' a' hf
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hX hMP
      _ ≤ A ^ 4 * ((etaT (E n) u)⁻¹ * (Mu ^ 3)⁻¹) :=
          MLExpDrift_bulk_num (N := N) (Wr := Wr) (Lr := Lr) (ℓ := ellT (d.L n) u)
            (η := etaT (E n) u) (Mu := Mu) (A := A) (Q := Wr ^ τ₁) (Ne := N ^ 4 * A)
            (Dp := Dp) (D := D) (D'' := D'') h32 hW3 hWL hWN hℓ hη0 hη1 rfl hMuW hQ1 hQA h48 hMi
            rfl hWD hD rfl
      _ = _ := by rw [hNε]
  -- the decay
  have hfar : ∀ a : Fin 2 → Z2 (d.L n),
      ellT (d.L n) u * Wr ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) →
        ‖expDriftT d n (E n) u σ a‖ ≤ Wr ^ (-D) := by
    intro a hfa
    have hdist : ellT (d.L n) u * Wr ^ τ' ≤ (zdist2 (d.L n) (a 0 - a 1) : ℝ) :=
      hfa.trans (MLExpDrift_maxDist_two a)
    have hW3τ : 3 ≤ Wr ^ (τ' / 2) := by
      calc (3 : ℝ) ≤ N ^ (c * (τ' / 2)) := h3τ
        _ = (N ^ c) ^ (τ' / 2) := Real.rpow_mul hN0.le _ _
        _ ≤ Wr ^ (τ' / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwn (by positivity)
    have hQτ : Wr ^ τ₁ ≤ Wr ^ (τ' / 2) := Real.rpow_le_rpow_of_exponent_le hW1 hτ₁le'
    have hshift : 2 * (ellT (d.L n) u * Wr ^ τ₁) + 1 ≤ ellT (d.L n) u * Wr ^ τ' := by
      have hsq : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have hlQ : 1 ≤ ellT (d.L n) u * Wr ^ τ₁ := one_le_mul_of_one_le_of_one_le hℓ hQ1
      have hlQ0 : 0 ≤ ellT (d.L n) u * Wr ^ τ₁ := by linarith
      have hQ'0 : 0 ≤ Wr ^ (τ' / 2) := Real.rpow_nonneg hW0.le _
      rw [hsq]
      calc 2 * (ellT (d.L n) u * Wr ^ τ₁) + 1 ≤ 3 * (ellT (d.L n) u * Wr ^ τ₁) := by linarith
        _ ≤ Wr ^ (τ' / 2) * (ellT (d.L n) u * Wr ^ τ₁) :=
            mul_le_mul_of_nonneg_right hW3τ hlQ0
        _ ≤ Wr ^ (τ' / 2) * (ellT (d.L n) u * Wr ^ (τ' / 2)) := by gcongr
        _ = ellT (d.L n) u * (Wr ^ (τ' / 2) * Wr ^ (τ' / 2)) := by ring
    have hf2R : 2 * (ellT (d.L n) u * Wr ^ τ₁) + 1 ≤ (zdist2 (d.L n) (a 0 - a 1) : ℝ) :=
      hshift.trans hdist
    unfold expDriftT
    refine (norm_integral_le_integral_norm _).trans ?_
    have hfm := MLExpDrift_first_moment (P := Sizes.seqP d)
      (f := fun ω => elklkN (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a) +
        egtN (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (loopOf σ a)) (S := S)
      (c := Wr ^ 2 * Lr ^ 2 * ((2 * N ^ 2) * (N * Wr ^ (-D'')) +
        2 * ((2 * N ^ 1) * (N * Wr ^ (-D''))))) (B := 16 * N ^ 5) (by positivity) (by positivity)
      (fun ω => by
        have h := MLExpDrift_env_X d n hEn hu1 hη hN1 hWL hKenv ω σ a
        rw [MLExpDrift_egtN_split, ← add_assoc]
        refine (norm_add_le _ _).trans ?_
        linarith [h.1, h.2])
      (fun ω hω => by
        refine (norm_add_le _ _).trans ?_
        exact MLExpDrift_far hL3 (E n) u (Sizes.seqHflow d n u ω) σ a hR0 hδ0 hf2R
          (fun s x => by
            rw [MLExpDrift_avgErr_eq]
            exact MLExpDrift_env_LKf d n hEn hu1 hη hN1 hKenv ω (m := 1) (by simp) _ _)
          (fun σ' a' => MLExpDrift_env_LKf d n hEn hu1 hη hN1 hKenv ω (m := 2) (by simp) _ _)
          (fun σ' a' hf => (hG2 ω hω 2 (by simp) σ' a' hf).2)
          (fun σ' a' hf => (hG2 ω hω 3 (by simp) σ' a' hf).1))
    calc _ ≤ _ := hfm
      _ ≤ Wr ^ 2 * Lr ^ 2 * ((2 * N ^ 2) * (N * Wr ^ (-D'')) +
          2 * ((2 * N ^ 1) * (N * Wr ^ (-D'')))) + 16 * N ^ 5 * N ^ (-Dp) := by gcongr
      _ ≤ Wr ^ (-D) :=
          MLExpDrift_far_num (N := N) (Wr := Wr) (Lr := Lr) (A := A) (Ne := N ^ 4 * A) (Dp := Dp)
            (D := D) (D'' := D'') h32 hW3 hWL hWN (by linarith [h48]) rfl hWD hD rfl
  exact ⟨fun a hfa => hfar a hfa, MLExpDrift_tmax_le hbulk⟩

end Main

end RBM.Evol
