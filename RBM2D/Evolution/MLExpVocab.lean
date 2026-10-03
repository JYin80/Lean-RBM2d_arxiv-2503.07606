/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Evolution.Bridge
import RBM2D.Induction.SumZeroQ
import RBM2D.Induction.QopBounds
import RBM2D.Induction.HierarchyN
import RBM2D.Gauss.LoopInitialValueScalar
import RBM2D.Gauss.MomentBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The vocabulary, the statements and the assembly of `ML:exp` (`eq:step6main`)

Paper: `ML:exp`, `eq:step6main` (Section 1) and Step 6 (`subsection:step6`, Sections 5-6).

Contents (namespace `RBM.Evol`, `variable (d : Sizes)`):

* the vocabulary `expErrT`, `expDriftT`, `qDriftT`, `TensorInvariant`, `MLExpHyps`,
  `ExpDriftBoundConcl` and the six statements `ExpHierPin`, `ExpDuhamelPin`, `ExpQDuhamelPin`,
  `ExpDriftBound`, `ExpInvariant`, `ExpQBound`, all `Prop`-valued;
* **the assembly `mlExp_of_pins`**: the five statements `ExpDuhamelPin`, `ExpQDuhamelPin`,
  `ExpDriftBound`, `ExpInvariant`, `ExpQBound` imply `MLExpPin` (no other hypothesis);
* algebra checks `uker_mul_thetaGenMat`, `qop_source`, `hierarchyN_two`,
  `TensorInvariant.symmetric`, and `expErrT_zero` (`f_0 = 0`);
* `step61_unif` (`≺ → 𝔼`, the union over the time outside `P`).

Helpers are prefixed `MLExpVocab_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Vocabulary -/

/-- `f_{u,σ} = 𝔼(𝓛-𝒦)_{u,σ}` as a `2`-tensor (`expLoopErr` of `Evolution/Defs.lean` at every label). -/
def expErrT (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) : (Fin 2 → Z2 (d.L n)) → ℂ :=
  fun a => expLoopErr d n E u σ a

/-- `D_{u,σ} = 𝔼(𝓔^{((𝓛-𝒦)×(𝓛-𝒦))} + 𝓔^{(G̃)})_{u,σ}` (`def_ELKLK`, `def_EwtG`; `elklkN`, `egtN`
at `n = 2`): the drift of the expected hierarchy at `n = 2`. -/
def expDriftT (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) : (Fin 2 → Z2 (d.L n)) → ℂ :=
  fun a => ∫ ω, (elklkN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a) +
      egtN (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) (loopOf σ a)) ∂(Sizes.seqP d)

/-- The source of the `𝒬`-Duhamel formula (`int_K-L+Q2` at `s = 0`, `n = 2`):
`A_u = 𝒬_u D_u + [𝒬_u, ϴ_{u,σ}] f_u - (𝒫 f_u) ϑ̇_u`.  The sign of the last term is `-` (the
derivative of `𝒬_u f_u = f_u - (𝒫 f_u) ϑ_u`); the paper writes `+`.  Only norms enter. -/
def qDriftT (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) : (Fin 2 → Z2 (d.L n)) → ℂ :=
  fun b => Qop (d.L n) u (expDriftT d n E u σ) b +
    (Qop (d.L n) u (thetaSig (d.L n) E σ u (expErrT d n E u σ)) b -
      thetaSig (d.L n) E σ u (Qop (d.L n) u (expErrT d n E u σ)) b) -
    Psum (d.L n) (expErrT d n E u σ) (b 0) * varthetaDot (d.L n) u b

/-- Invariance of a `2`-tensor under translation and negation of both labels (the automorphisms of
`Z_L²` that preserve `S^{(B)}`; the model, `𝒦`, `Θ` are invariant). -/
def TensorInvariant {L : ℕ} [NeZero L] (A : (Fin 2 → Z2 L) → ℂ) : Prop :=
  (∀ (v : Z2 L) (a : Fin 2 → Z2 L), A (fun i => a i + v) = A a) ∧
    (∀ a : Fin 2 → Z2 L, A (fun i => -a i) = A a)

/-- The hypotheses of `MLExpPin` other than `SumDecayDetPrec` (same order, one bundle). -/
def MLExpHyps (κ c τ : ℝ) (E t : ℕ → ℝ) : Prop :=
  0 < κ ∧ 0 < c ∧ 0 < τ ∧ (∀ n, |E n| ≤ 2 - κ) ∧ (∀ n, 0 ≤ t n) ∧ (∀ n, t n < 1) ∧
    SizeTendsto d ∧ Bandwidth d c ∧ RangeCond d τ t ∧ KboundConcl κ ∧
    Step4PT d E (fun _ => 0) t ∧ DecayLoopPT d E (fun _ => 0) t ∧
    (∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → Step61Concl d E u)

/-- The conclusion of `ExpDriftBound`: `𝔼B_2 + 𝔼B_3` has `(u,τ',D)` decay and
`‖·‖_max ≤ N^ε η_u^{-1} M_u^{-3}`, for every `u ∈ [0,t_n]` and every `σ`. -/
def ExpDriftBoundConcl (E t : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ τ' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (t n),
    ∀ σ : Fin 2 → Bool,
      HasDecay (d.L n) (d.W n) u τ' D (expDriftT d n (E n) u σ) ∧
      tmax (d.L n) (expDriftT d n (E n) u σ) ≤
        ((d.size n : ℕ) : ℝ) ^ ε *
          ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹)

/-! ## 2. The statements -/

/-- **`ExpHierPin`** (the expected hierarchy at `n = 2`, all `σ`).  Paper: (`eq_L-Keee`,
`LK_SDE`) at `n = 2` after taking expectations ("the martingale term vanishes because we take
expectation", proof of `lemma:step6-1`); `f_0 = 0` ("no initial data term", proof of
`lemma:step6-1`).  Inputs: `Ind.hierarchyN` (matrix
level, `k = 2`), `Ind.loopGenN`, `KLoop.Kcal_two`, `Gauss.initialLoopValue_two_edges`.  The drift
identity holds on the open window and continuity on
the closed one: `H_u = √u X` is not differentiable at `u = 0`.  Deterministic, finite size, no
`∀ᶠ`. -/
def ExpHierPin : Prop :=
  ∀ (n : ℕ) (E : ℝ), |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)),
    expErrT d n E 0 σ a = 0 ∧
    ContinuousOn (fun u => expErrT d n E u σ a) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => expDriftT d n E u σ a) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => expErrT d n E v σ a)
      (thetaSig (d.L n) E σ u (expErrT d n E u σ) a + expDriftT d n E u σ a) u

/-- **`ExpDuhamelPin`** (Duhamel, no `𝒬`): `f_t = ∫_0^t 𝒰_{u,t,σ} D_u du` (`Eexpint_K-L` without
`𝒬`; used for the repeated-sign vectors, where Case 1 of `lem:sum_decay` needs no sum-zero).
Deterministic. -/
def ExpDuhamelPin : Prop :=
  ∀ (n : ℕ) (E t : ℝ), |E| < 2 → 0 ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)),
    expErrT d n E t σ a = ∫ u in (0 : ℝ)..t, Ugen (d.L n) E σ u t (expDriftT d n E u σ) a

/-- **`ExpQDuhamelPin`** (Duhamel with `𝒬`): `(𝒬_t f_t)(a) = ∫_0^t (𝒰_{u,t,σ} A_u)(a) du` with
`A_u = qDriftT` (`Eexpint_K-L` with the commutator and `ϑ̇` terms; `pqthlk`).  Inputs:
`qopAlgebra`, `SumZeroQ_hasDerivAt_vartheta`. -/
def ExpQDuhamelPin : Prop :=
  ∀ (n : ℕ) (E t : ℝ), |E| < 2 → 0 ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)),
    Qop (d.L n) t (expErrT d n E t σ) a =
      ∫ u in (0 : ℝ)..t, Ugen (d.L n) E σ u t (qDriftT d n E u σ) a

/-- **`ExpDriftBound`** (the expected drift terms): (`eq:LKLKstep6`, `eq:wtGstep6`) for
`u ∈ [0,t_n]`: `𝔼𝓔^{LK×LK}, 𝔼𝓔^{(G̃)} ≺ W²ℓ_u²M_u^{-4} = η_u^{-1}M_u^{-3}`, with `(u,τ',D)` decay
(`lem_decayLoop` inside the sums over `(a,b)`, window `W^{τ'}ℓ_u²`).  Inputs: `Step4PT`
(`k = 1,2,3`),
`DecayLoopPT` (`k = 2,3`), `Step61Concl` (uniform over `[0,t]` by the section argument, `σ = (-)` by
conjugation), `KboundConcl` (`n = 3`), and the `≺ → 𝔼` step (`momentDomAt_of_stochDomAt`, envelope
`‖G_u‖ ≤ η_u^{-1} ≤ N^{1-τ}/Im m` from `RangeCond`). -/
def ExpDriftBound (κ c τ : ℝ) (E t : ℕ → ℝ) : Prop :=
  MLExpHyps d κ c τ E t → ExpDriftBoundConcl d E t

/-- **`ExpInvariant`** (invariance of the expected tensors): `f_u` and `D_u` are invariant under
translation and negation of the labels (the law of `H_u`, `S^{(B)}`, `𝒦_u` are).  This is the
input behind (`eq:case4_B`), which the paper asserts without proof.  `Symmetric` (the hypothesis
of Case 4) is not enough: `ϴ` does not preserve `Symmetric` (for `L = 3`, `u = 0`, there is a
symmetric `A` with `ϴA` not symmetric), it does preserve `TensorInvariant`.  Specific to `d = 2`
(the one-dimensional argument has no Case 4).  Deterministic, finite size. -/
def ExpInvariant : Prop :=
  ∀ (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
    TensorInvariant (expErrT d n E u σ) ∧ TensorInvariant (expDriftT d n E u σ)

/-- **`ExpQBound`** (the `𝒬`-terms, alternating `σ`): `A_u = qDriftT` is sum-zero, symmetric, has
`(u,τ',D)` decay and `‖A_u‖_max ≤ N^ε η_u^{-1}M_u^{-3}` for `u ∈ [0,t_n]`; and
`‖(𝒫 f_t) ϑ_t‖ ≤ N^ε M_t^{-3}`.  Paper: `lem_+Q` (`QopNorm`, `QopDecay`), `jywiiwsoks`,
`eq:thetadot_bound`, `kkuuwsaf`, `kkuuwsaf5`, `eq:step6_improvedexpectation`
(Ward identity `KLoop.WI_calK_two` and `sum_gloop_ward_last_div`, Lemma `lemma:step6-1`),
`eq:p_term_step6`, `commutator_step6`.  Takes the `ExpDriftBound` conclusion and `ExpInvariant` as
hypotheses. -/
def ExpQBound (κ c τ : ℝ) (E t : ℕ → ℝ) : Prop :=
  MLExpHyps d κ c τ E t → ExpDriftBoundConcl d E t → ExpInvariant d →
  ∀ ε > (0 : ℝ), ∀ τ' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (∀ u ∈ Set.Icc (0 : ℝ) (t n), ∀ σ : Fin 2 → Bool, Alternating σ →
      SumZero (d.L n) (qDriftT d n (E n) u σ) ∧ Symmetric (d.L n) (qDriftT d n (E n) u σ) ∧
      HasDecay (d.L n) (d.W n) u τ' D (qDriftT d n (E n) u σ) ∧
      tmax (d.L n) (qDriftT d n (E n) u σ) ≤
        ((d.size n : ℕ) : ℝ) ^ ε *
          ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹)) ∧
    (∀ σ : Fin 2 → Bool, Alternating σ → ∀ a : Fin 2 → Z2 (d.L n),
      ‖Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0) * vartheta (d.L n) (t n) a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹)


/-! ## 3. Convention and algebra checks -/

section Checks

/-- **`𝒰_{v,w} ∘ ϴ_v = ϴ_w` on one slot**: `(1 - vξS)Θ_{wξ} · ξSΘ_{vξ} = ξSΘ_{wξ}`.  This is the
algebra behind `∂_v(𝒰_{v,t} f_v) = 𝒰_{v,t}(f'_v - ϴ_v f_v)`, i.e. the reason `ukerMat`
and `thetaGenMat` (`Path/UBounds.lean`, with the factor `S`) are the right pair for
`ExpDuhamelPin`. -/
theorem uker_mul_thetaGenMat {L : ℕ} [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hv : ‖(v : ℂ) * ξ‖ < 1) (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat L ξ v w * thetaGenMat L ξ v = thetaGenMat L ξ w := by
  have hc : Theta L ((w : ℂ) * ξ) * Theta L ((v : ℂ) * ξ) =
      Theta L ((v : ℂ) * ξ) * Theta L ((w : ℂ) * ξ) := (Theta_commute L hL hw hv).eq
  have hcs : Theta L ((w : ℂ) * ξ) * SB L = SB L * Theta L ((w : ℂ) * ξ) :=
    (Theta_commute_SB L hL hw).eq
  have h1 : (1 - ((v : ℂ) * ξ) • SB L) * Theta L ((v : ℂ) * ξ) = 1 := mul_Theta L hL hv
  have hAS : (1 - ((v : ℂ) * ξ) • SB L) * SB L = SB L * (1 - ((v : ℂ) * ξ) • SB L) := by
    simp [sub_mul, mul_sub]
  unfold ukerMat thetaGenMat
  calc (1 - ((v : ℂ) * ξ) • SB L) * Theta L ((w : ℂ) * ξ) * (ξ • (SB L * Theta L ((v : ℂ) * ξ)))
      = ξ • ((1 - ((v : ℂ) * ξ) • SB L) * (Theta L ((w : ℂ) * ξ) * SB L) *
          Theta L ((v : ℂ) * ξ)) := by
        rw [Matrix.mul_smul]; congr 1; noncomm_ring
    _ = ξ • ((1 - ((v : ℂ) * ξ) • SB L) * (SB L * Theta L ((w : ℂ) * ξ)) *
          Theta L ((v : ℂ) * ξ)) := by rw [hcs]
    _ = ξ • (((1 - ((v : ℂ) * ξ) • SB L) * SB L) *
          (Theta L ((w : ℂ) * ξ) * Theta L ((v : ℂ) * ξ))) := by
        congr 1; noncomm_ring
    _ = ξ • (((1 - ((v : ℂ) * ξ) • SB L) * SB L) *
          (Theta L ((v : ℂ) * ξ) * Theta L ((w : ℂ) * ξ))) := by rw [hc]
    _ = ξ • (SB L * (((1 - ((v : ℂ) * ξ) • SB L) * Theta L ((v : ℂ) * ξ)) *
          Theta L ((w : ℂ) * ξ))) := by
        rw [hAS]; congr 1; noncomm_ring
    _ = ξ • (SB L * Theta L ((w : ℂ) * ξ)) := by rw [h1, one_mul]

theorem MLExpVocab_Psum_add {L : ℕ} [NeZero L] {k : ℕ} [NeZero k] (A B : (Fin k → Z2 L) → ℂ)
    (a₁ : Z2 L) : Psum L (fun b => A b + B b) a₁ = Psum L A a₁ + Psum L B a₁ := by
  simp only [Psum, Finset.sum_add_distrib]

theorem MLExpVocab_Qop_add {L : ℕ} [NeZero L] {k : ℕ} [NeZero k] (t : ℝ)
    (A B : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L t (fun b => A b + B b) a = Qop L t A a + Qop L t B a := by
  simp only [Qop, MLExpVocab_Psum_add]; ring

/-- **The source of the ODE of `𝒬 f`** (bookkeeping of `ExpQDuhamelPin`):
`∂_u(𝒬_u f_u) = 𝒬_u f'_u - (𝒫 f_u) ϑ̇_u`, and with `f' = ϴ f + D` this is `ϴ(𝒬_u f_u)` plus the source
`𝒬_u D_u + [𝒬_u, ϴ_u] f_u - (𝒫 f_u) ϑ̇_u` (the tensor `qDriftT`). -/
theorem qop_source {L : ℕ} [NeZero L] (E u : ℝ) (σ : Fin 2 → Bool)
    (f D : (Fin 2 → Z2 L) → ℂ) (b : Fin 2 → Z2 L) :
    Qop L u (fun c => thetaSig L E σ u f c + D c) b - Psum L f (b 0) * varthetaDot L u b =
      thetaSig L E σ u (Qop L u f) b +
        (Qop L u D b + (Qop L u (thetaSig L E σ u f) b - thetaSig L E σ u (Qop L u f) b) -
          Psum L f (b 0) * varthetaDot L u b) := by
  rw [MLExpVocab_Qop_add]; ring

/-- The matrix-level input of `ExpHierPin` at `k = 2` (the empty sum `Σ_{l=3}^{2}` removed):
`Ind.hierarchyN` (`Induction/HierarchyN.lean`), all `σ`. -/
theorem hierarchyN_two (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ) (hL : 3 ≤ L)
    (hE : |E| < 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    genMat E u M (loopOf σ a) - deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u =
      thetaSig L E σ u (lkTensor L W E u M σ) a + elklkN L W E u M (loopOf σ a) +
        egtN L W E u M (loopOf σ a) := by
  have h := hierarchyN L W E hL hE u hu0 hu1 M hM 2 le_rfl σ a
  simpa using h

/-- `TensorInvariant` gives the hypothesis `Symmetric` of Case 4 (`symmetric_tensor`). -/
theorem TensorInvariant.symmetric {L : ℕ} [NeZero L] {A : (Fin 2 → Z2 L) → ℂ}
    (h : TensorInvariant A) : Symmetric L A := by
  intro c r _
  have h1 : A (fun i => c + r i) = A r := by
    have := h.1 c r
    simpa [add_comm] using this
  have h2 : A (fun i => c - r i) = A r := by
    have h3 := h.1 c (fun i => -r i)
    have h4 := h.2 r
    have e : (fun i => -r i + c) = fun i => c - r i := by funext i; ring
    rw [show (fun i => (fun j => -r j) i + c) = fun i => c - r i from e] at h3
    rw [h3, h4]
  rw [h1, h2]

/-- `σ 0 ≠ σ 1` is `Alternating σ` at `k = 2`. -/
theorem MLExpVocab_alt_of_ne {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) : Alternating σ := by
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, zero_add]
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all
  · simp only [Fin.mk_one, Fin.isValue]
    have : (1 : Fin 2) + 1 = 0 := by decide
    rw [this]
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all

/-- `σ 0 = σ 1` is a repeated sign, the hypothesis of Case 1 (`nonalternating`). -/
theorem MLExpVocab_repeat_of_eq {σ : Fin 2 → Bool} (h : σ 0 = σ 1) :
    ∃ i : Fin 2, σ i = σ (i + 1) := ⟨0, by simpa using h⟩

end Checks

/-! ## 4. `f_0 = 0` -/

section Zero

/-- `initialGreenScalar E σ = m(σ)` (the zero-matrix Green function is the scalar `m`). -/
theorem MLExpVocab_initialGreenScalar {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    initialGreenScalar E σ = KLoop.mSig E σ := by
  have hmul := spectralM_mul hE.le
  have hT : ((-((E : ℂ) + spectralM E))⁻¹ : ℂ) = spectralM E :=
    inv_eq_of_mul_eq_one_right (by linear_combination (-1 : ℂ) * hmul)
  cases σ
  · have h := congrArg (starRingEnd ℂ) hT
    simp only [map_inv₀, map_neg] at h
    simpa [initialGreenScalar, KLoop.mSig] using h
  · simpa [initialGreenScalar, KLoop.mSig] using hT

/-- `Θ_0 = 1`. -/
theorem MLExpVocab_Theta_zero (L : ℕ) [NeZero L] (hL : 3 ≤ L) : Theta L 0 = 1 := by
  have h := mul_Theta L hL (ξ := 0) (by simp)
  simpa using h

/-- **`f_0 = 0`** (proof of `lemma:step6-1`, "there is no initial data term": `𝓛_0 = 𝒦_0`; see `Def_Ktza`): the
tensor `𝔼(𝓛-𝒦)_{0,σ}` vanishes at every label, for every `σ ∈ {±}²` and `|E| < 2`. -/
theorem expErrT_zero (n : ℕ) {E : ℝ} (hE : |E| < 2) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 (d.L n)) : expErrT d n E 0 σ a = 0 := by
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hI : loopOf σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have hint : (∫ ω, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n 0 ω)) (spectralZ E 0)
      (loopOf σ a) ∂(Sizes.seqP d)) = initialLoopValue (d.L n) (d.W n) E (loopOf σ a) := by
    have h0 : ∀ ω : Sizes.SeqΩ d, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n 0 ω))
        (spectralZ E 0) (loopOf σ a) = initialLoopValue (d.L n) (d.W n) E (loopOf σ a) := by
      intro ω
      simp [blockMat, initialLoopValue, spectralZ]
    simp only [h0]
    simp
  unfold expErrT expLoopErr
  rw [hint, hI, initialLoopValue_two_edges (d.L n) (d.W n) hE, KLoop.Kcal_two,
    MLExpVocab_initialGreenScalar hE, MLExpVocab_initialGreenScalar hE]
  simp only [Complex.ofReal_zero, zero_mul, MLExpVocab_Theta_zero (d.L n) hL, Matrix.one_apply]
  split_ifs
  · ring
  · simp

end Zero

/-! ## 5. Real-variable helpers of the assembly -/

section Assembly

/-- **The time integral** ([YY_25] (5.136); dimension-free): if `‖f v‖ ≤ α (1-v)^{-1} + β` on
`(s,u]` then `‖∫_s^u f‖ ≤ α log((1-s)/(1-u)) + β(u-s)`. -/
theorem MLExpVocab_norm_integral_le_log {s u : ℝ} (hsu : s ≤ u) (hu1 : u < 1) {α β : ℝ}
    {f : ℝ → ℂ} (hf : ∀ v ∈ Set.Ioc s u, ‖f v‖ ≤ α * (1 - v)⁻¹ + β) :
    ‖∫ v in s..u, f v‖ ≤ α * Real.log ((1 - s) / (1 - u)) + β * (u - s) := by
  have hcont : ContinuousOn (fun v : ℝ => (1 - v)⁻¹) (Set.uIcc s u) := by
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun v hv => ?_
    rw [Set.uIcc_of_le hsu] at hv
    have := hv.2
    linarith
  have hint : IntervalIntegrable (fun v : ℝ => (1 - v)⁻¹) volume s u := hcont.intervalIntegrable
  have hlog : ∫ v in s..u, (1 - v)⁻¹ = Real.log ((1 - s) / (1 - u)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) 1]
    refine integral_inv fun h0 => ?_
    rw [Set.uIcc_of_le (by linarith)] at h0
    have := h0.1
    linarith
  refine (intervalIntegral.norm_integral_le_of_norm_le hsu
    (Eventually.of_forall fun v hv => hf v hv)
    ((hint.const_mul α).add intervalIntegrable_const)).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hint.const_mul α) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hlog, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- `Im m ≤ 1`. -/
theorem MLExpVocab_im_le_one (E : ℝ) : (spectralM E).im ≤ 1 := by
  rw [spectralM_im]
  have h : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
  linarith

/-- `Im m ≥ √(2κ)/2` for `|E| ≤ 2 - κ`, `κ > 0` (`4 - E² ≥ κ(4-κ) ≥ 2κ`). -/
theorem MLExpVocab_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt (2 * κ) / 2 ≤ (spectralM E).im := by
  rw [spectralM_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h1 : |E| ^ 2 ≤ (2 - κ) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg E) hE 2
    rwa [sq_abs] at h1
  have h : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h
  linarith

/-- `M_u ≤ W²`. -/
theorem MLExpVocab_scaleM_le_W2 {L W : ℕ} (hL : 1 ≤ L) {E u : ℝ} (hu : u < 1) :
    scaleM L W E u ≤ (W : ℝ) ^ 2 := by
  rw [scaleM_eq hL hu]
  have him := MLExpVocab_im_le_one E
  have hW : (0 : ℝ) ≤ (W : ℝ) ^ 2 := sq_nonneg _
  have hmin : min 1 ((L : ℝ) ^ 2 * (1 - u)) ≤ 1 := min_le_left _ _
  by_cases hi : 0 ≤ (spectralM E).im
  · calc (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u))
        ≤ (W : ℝ) ^ 2 * 1 * 1 := by
          have hm0 : 0 ≤ min 1 ((L : ℝ) ^ 2 * (1 - u)) :=
            le_min zero_le_one (mul_nonneg (sq_nonneg _) (by linarith))
          gcongr
      _ = (W : ℝ) ^ 2 := by ring
  · have hneg : (spectralM E).im < 0 := lt_of_not_ge hi
    have hm0 : 0 ≤ min 1 ((L : ℝ) ^ 2 * (1 - u)) :=
      le_min zero_le_one (mul_nonneg (sq_nonneg _) (by linarith))
    have : (W : ℝ) ^ 2 * (spectralM E).im * min 1 ((L : ℝ) ^ 2 * (1 - u)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hW hneg.le) hm0
    linarith

/-- `ratioR = M_u / M_t` (the factor `W²` cancels). -/
theorem MLExpVocab_ratioR_eq {L W : ℕ} (hW : 0 < W) (E s t : ℝ) :
    ratioR L E s t = scaleM L W E s / scaleM L W E t := by
  have hW2 : ((W : ℝ) ^ 2) ≠ 0 := by positivity
  unfold ratioR scaleM
  rw [mul_assoc ((W : ℝ) ^ 2), mul_assoc ((W : ℝ) ^ 2), mul_div_mul_left _ _ hW2]

/-- `W^x ≤ N^{|x|/2}` when `1 ≤ W`, `W² ≤ N`. -/
theorem MLExpVocab_rpow_le {W N x : ℝ} (hW : 1 ≤ W) (hWN : W ^ 2 ≤ N) :
    W ^ x ≤ N ^ (|x| / 2) := by
  have hW0 : 0 ≤ W := by linarith
  calc W ^ x ≤ W ^ |x| := Real.rpow_le_rpow_of_exponent_le hW (le_abs_self x)
    _ = (W ^ 2) ^ (|x| / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; congr 1; push_cast; ring
    _ ≤ N ^ (|x| / 2) := Real.rpow_le_rpow (by positivity) hWN (by positivity)

/-- The range condition gives `log (1/(1-T)) ≤ log N`. -/
theorem MLExpVocab_log_le {N τ T : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hT1 : T < 1)
    (hR : N ^ (-1 + τ) ≤ 1 - T) : Real.log (1 / (1 - T)) ≤ Real.log N := by
  have hN0 : 0 < N := by linarith
  have h1T : 0 < 1 - T := by linarith
  have hpos : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have h1 : 1 / (1 - T) ≤ N ^ (1 - τ) := by
    rw [one_div]
    calc (1 - T)⁻¹ ≤ (N ^ (-1 + τ))⁻¹ := inv_anti₀ hpos hR
      _ = N ^ (1 - τ) := by
          rw [← Real.rpow_neg hN0.le]; congr 1; ring
  have h2 : N ^ (1 - τ) ≤ N := by
    calc N ^ (1 - τ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N := Real.rpow_one N
  exact Real.log_le_log (by positivity) (h1.trans h2)

end Assembly

section Assembly

/-- **The integral of the kernel bound**: the arithmetic of the kernel-ratio bound at `d = 2`,
`n = 2`: if the integrand of the
Duhamel formula is bounded by the kernel bound `N^{ε₁}(W^x Λ_u R_{u,t}² + W^y)` (Case 1 or Case 4 of
`SumDecayDetPrec`) with `Λ_u ≤ N^{ε₂} η_u^{-1} M_u^{-3}` (`ExpDriftBound`, `ExpQBound`), then, using
`M_t ≤ M_u`,
`W^y ≤ M_t^{-3}` and `∫_0^t η_u^{-1} du = (Im m)^{-1} log(1/(1-t)) ≤ (Im m)^{-1} log N`,
`‖∫_0^t F‖ ≤ M_t^{-3} (N^{ε₁+ε₂+|x|/2} (Im m)^{-1} log N + N^{ε₁})`.  Exponents of `M`: `R² M_u^{-3} =
M_t^{-2} M_u^{-1} ≤ M_t^{-3}`, no power of `M` or `N` is lost. -/
theorem MLExpVocab_core {L W : ℕ} [NeZero L] [NeZero W] {E T : ℝ} (hE : |E| < 2) (hT0 : 0 ≤ T)
    (hT1 : T < 1) {N : ℝ} (hN : 1 ≤ N) (hWN : (W : ℝ) ^ 2 ≤ N) (hL : 1 ≤ L)
    (hlogT : Real.log (1 / (1 - T)) ≤ Real.log N)
    {ε₁ ε₂ x y : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hy : (W : ℝ) ^ y ≤ (scaleM L W E T ^ 3)⁻¹)
    {F : ℝ → ℂ} {Λ : ℝ → ℝ}
    (hF : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖F u‖ ≤
      N ^ ε₁ * ((W : ℝ) ^ x * Λ u * ratioR L E u T ^ 2 + (W : ℝ) ^ y))
    (hΛ : ∀ u ∈ Set.Icc (0 : ℝ) T, Λ u ≤
      N ^ ε₂ * ((etaT E u)⁻¹ * (scaleM L W E u ^ 3)⁻¹)) :
    ‖∫ u in (0 : ℝ)..T, F u‖ ≤
      (scaleM L W E T ^ 3)⁻¹ *
        (N ^ (ε₁ + ε₂ + |x| / 2) * (spectralM E).im⁻¹ * Real.log N + N ^ ε₁) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hN0 : 0 < N := by linarith
  have hm : 0 < (spectralM E).im := spectralM_im_pos hE
  set m : ℝ := (spectralM E).im with hmdef
  set MT : ℝ := scaleM L W E T with hMT
  have hMT0 : 0 < MT := scaleM_pos hL hWpos hE hT1
  set X : ℝ := (MT ^ 3) ⁻¹ with hX
  have hX0 : 0 < X := by positivity
  set Kc : ℝ := N ^ (ε₁ + ε₂ + |x| / 2) * m⁻¹ * X with hKc
  set Bc : ℝ := N ^ ε₁ * X with hBc
  have hKc0 : 0 ≤ Kc := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  have hpt : ∀ v ∈ Set.Ioc (0 : ℝ) T, ‖F v‖ ≤ Kc * (1 - v)⁻¹ + Bc := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1.le
    have hvT : v ≤ T := hv.2
    have hv1 : v < 1 := lt_of_le_of_lt hvT hT1
    have h1v : 0 < 1 - v := by linarith
    have hvI : v ∈ Set.Icc (0 : ℝ) T := ⟨hv0, hvT⟩
    set Mu : ℝ := scaleM L W E v with hMu
    have hMuT : MT ≤ Mu := (scaleM_anti_ratio hL hE hvT hT1).1
    have hMu0 : 0 < Mu := lt_of_lt_of_le hMT0 hMuT
    have hηinv : (etaT E v)⁻¹ = (1 - v)⁻¹ * m⁻¹ := by
      unfold etaT; rw [mul_inv]
    have hratio : ratioR L E v T = Mu / MT := MLExpVocab_ratioR_eq hWpos E v T
    have hR2 : 0 ≤ N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X := by positivity
    have hk : ((Mu ^ 3)⁻¹) * (Mu / MT) ^ 2 ≤ X := by
      have e : ((Mu ^ 3)⁻¹) * (Mu / MT) ^ 2 = Mu⁻¹ * (MT ^ 2)⁻¹ := by field_simp
      have e2 : X = MT⁻¹ * (MT ^ 2)⁻¹ := by rw [hX]; field_simp
      rw [e, e2]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hMT0 hMuT) (by positivity)
    have h1 : Λ v * (Mu / MT) ^ 2 ≤ N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X := by
      have h1a := mul_le_mul_of_nonneg_right (hΛ v hvI) (sq_nonneg (Mu / MT))
      have h1b : (N ^ ε₂ * ((etaT E v)⁻¹ * (Mu ^ 3)⁻¹)) * (Mu / MT) ^ 2 ≤
          N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X := by
        rw [hηinv]
        have hnn : 0 ≤ N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) := by positivity
        calc N ^ ε₂ * (((1 - v)⁻¹ * m⁻¹) * (Mu ^ 3)⁻¹) * (Mu / MT) ^ 2
            = N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * (((Mu ^ 3)⁻¹) * (Mu / MT) ^ 2) := by ring
          _ ≤ N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X := mul_le_mul_of_nonneg_left hk hnn
      exact h1a.trans h1b
    have h2 : (W : ℝ) ^ x ≤ N ^ (|x| / 2) := MLExpVocab_rpow_le hW1 hWN
    have hW0 : 0 ≤ (W : ℝ) ^ x := Real.rpow_nonneg (by linarith) _
    have h3 : (W : ℝ) ^ x * Λ v * ratioR L E v T ^ 2 ≤
        N ^ (|x| / 2) * (N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X) := by
      rw [hratio, mul_assoc]
      calc (W : ℝ) ^ x * (Λ v * (Mu / MT) ^ 2)
          ≤ (W : ℝ) ^ x * (N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X) :=
            mul_le_mul_of_nonneg_left h1 hW0
        _ ≤ N ^ (|x| / 2) * (N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X) :=
            mul_le_mul_of_nonneg_right h2 hR2
    have h4 : (W : ℝ) ^ y ≤ X := hy
    calc ‖F v‖ ≤ N ^ ε₁ * ((W : ℝ) ^ x * Λ v * ratioR L E v T ^ 2 + (W : ℝ) ^ y) := hF v hvI
      _ ≤ N ^ ε₁ * (N ^ (|x| / 2) * (N ^ ε₂ * ((1 - v)⁻¹ * m⁻¹) * X) + X) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN0.le _)
          linarith
      _ = Kc * (1 - v)⁻¹ + Bc := by
          rw [hKc, hBc, Real.rpow_add hN0, Real.rpow_add hN0]; ring
  have hint := MLExpVocab_norm_integral_le_log hT0 hT1 hpt
  have hlog' : Real.log ((1 - 0) / (1 - T)) ≤ Real.log N := by
    simpa using hlogT
  calc ‖∫ u in (0 : ℝ)..T, F u‖ ≤ Kc * Real.log ((1 - 0) / (1 - T)) + Bc * (T - 0) := hint
    _ ≤ Kc * Real.log N + Bc * 1 := by
        gcongr
        linarith
    _ = X * (N ^ (ε₁ + ε₂ + |x| / 2) * m⁻¹ * Real.log N + N ^ ε₁) := by
        rw [hKc, hBc]; ring

/-- The final absorption of the constants (`log N ≤ N^δ/δ`, `Im m ≥ m₀`): with `K₀ = 16/(ε m₀) + 2 ≤
N^{3ε/4}` and `|x|/2 ≤ ε/16`, the bound of `MLExpVocab_core` plus one more term `N^{ε/16} X` is at most
`N^ε X`. -/
theorem MLExpVocab_final {N ε x m m₀ X : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hm₀ : 0 < m₀) (hm : m₀ ≤ m)
    (hx : |x| / 2 ≤ ε / 16) (hX : 0 ≤ X) (hK : 16 / (ε * m₀) + 2 ≤ N ^ (3 * ε / 4)) :
    X * (N ^ (ε / 16 + ε / 16 + |x| / 2) * m⁻¹ * Real.log N + N ^ (ε / 16)) +
        N ^ (ε / 16) * X ≤ N ^ ε * X := by
  have hN0 : 0 < N := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le hm₀ hm
  have hlog : Real.log N ≤ N ^ (ε / 16) / (ε / 16) := Real.log_le_rpow_div hN0.le (by positivity)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 : N ^ (ε / 16 + ε / 16 + |x| / 2) ≤ N ^ (ε / 16 + ε / 16 + ε / 16) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hminv : m⁻¹ ≤ m₀⁻¹ := inv_anti₀ hm₀ hm
  have hA : N ^ (ε / 16 + ε / 16 + |x| / 2) * m⁻¹ * Real.log N ≤
      N ^ (ε / 4) * (16 / (ε * m₀)) := by
    calc N ^ (ε / 16 + ε / 16 + |x| / 2) * m⁻¹ * Real.log N
        ≤ N ^ (ε / 16 + ε / 16 + ε / 16) * m₀⁻¹ * (N ^ (ε / 16) / (ε / 16)) := by
          gcongr
      _ = N ^ (ε / 4) * (16 / (ε * m₀)) := by
          have e : N ^ (ε / 16 + ε / 16 + ε / 16) * N ^ (ε / 16) = N ^ (ε / 4) := by
            rw [← Real.rpow_add hN0]; congr 1; ring
          calc N ^ (ε / 16 + ε / 16 + ε / 16) * m₀⁻¹ * (N ^ (ε / 16) / (ε / 16))
              = (N ^ (ε / 16 + ε / 16 + ε / 16) * N ^ (ε / 16)) * (16 / (ε * m₀)) := by
                field_simp
            _ = N ^ (ε / 4) * (16 / (ε * m₀)) := by rw [e]
  have h2 : N ^ (ε / 16) ≤ N ^ (ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h3 : N ^ (ε / 4) * (16 / (ε * m₀) + 2) ≤ N ^ ε := by
    calc N ^ (ε / 4) * (16 / (ε * m₀) + 2) ≤ N ^ (ε / 4) * N ^ (3 * ε / 4) :=
          mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hN0.le _)
      _ = N ^ ε := by rw [← Real.rpow_add hN0]; congr 1; ring
  have h4 : X * (N ^ (ε / 16 + ε / 16 + |x| / 2) * m⁻¹ * Real.log N + N ^ (ε / 16)) +
      N ^ (ε / 16) * X ≤ X * (N ^ (ε / 4) * (16 / (ε * m₀) + 2)) := by
    have : N ^ (ε / 16 + ε / 16 + |x| / 2) * m⁻¹ * Real.log N + N ^ (ε / 16) + N ^ (ε / 16) ≤
        N ^ (ε / 4) * (16 / (ε * m₀) + 2) := by nlinarith
    nlinarith
  calc _ ≤ X * (N ^ (ε / 4) * (16 / (ε * m₀) + 2)) := h4
    _ ≤ X * N ^ ε := mul_le_mul_of_nonneg_left h3 hX
    _ = N ^ ε * X := by ring

end Assembly

/-! ## 6. The assembly `mlExp_of_pins` -/

section Main

/-- **`MLExpPin` from the five statements `ExpDuhamelPin`, `ExpQDuhamelPin`, `ExpDriftBound`,
`ExpInvariant`, `ExpQBound`.**

* `f_t = ∫_0^t 𝒰_{u,t,σ} D_u du` (`ExpDuhamelPin`) for a repeated sign (Case 1 of
  `SumDecayDetPrec`),
  `𝒬_t f_t = ∫_0^t 𝒰_{u,t,σ} A_u du` (`ExpQDuhamelPin`) for an alternating sign (Case 4, hypotheses
  `SumZero`, `Symmetric`, `HasDecay` of `A_u` from `ExpQBound`), at `k = 2`, `s = u`,
  `t' = t_n ≤ 1 - N^{-1+τ}` (`RangeCond`), `W ≥ N^𝔠` (`Bandwidth`), `|E| ≤ 2 - κ`;
* `‖𝒰_{u,t} A_u‖ ≤ N^{ε₁}(W^{C₂τ'} ‖A_u‖ R_{u,t}² + W^{-D+C₂})`, `R_{u,t} = M_u/M_t`, `‖A_u‖ ≤ N^{ε₁}
  η_u^{-1} M_u^{-3}`, `M_t ≤ M_u` (`scaleM_anti_ratio`), so the integrand is `≤ K η_u^{-1} M_t^{-3}` (`core`);
* `∫_0^t η_u^{-1} du = (Im m)^{-1} log(1/(1-t)) ≤ (2/√(2κ)) log N` (`RangeCond`), `log N ≤ N^δ/δ`;
* `f_t = 𝒬_t f_t + (𝒫 f_t) ϑ_t` and the endpoint clause of `ExpQBound`.

The constants are `τ' = ε/(8(|C₂|+1))`, `D = |C₂| + 6`, `ε₁ = ε/16`; the exponent of `N` is `ε/4` before the
absorption of `16/(ε m₀) + 2 ≤ N^{3ε/4}`.  Hypotheses used: `hκ` (`Im m ≥ √(2κ)/2`), `hc` (kernel), `hτ`
(kernel, `log`), `hE` (kernel, `Im m`), `ht0`, `ht1` (Duhamel), `hsz` (all `∀ᶠ`), `hbw`, `hrc` (kernel and
`log`); `hDuh`, `hQDuh` are the two Duhamel formulas, `hDrift` and `hInv` enter through `hQ` (and `hDrift` also
directly, for the repeated-sign vectors); `hK`, `h4`, `hDL`, `h61` enter only through
`ExpDriftBound` and
`ExpQBound`. -/
theorem mlExp_of_pins {κ c τ : ℝ} {C : ℕ → ℝ} {E t : ℕ → ℝ}
    (hDuh : ExpDuhamelPin d) (hQDuh : ExpQDuhamelPin d)
    (hDrift : ExpDriftBound d κ c τ E t) (hInv : ExpInvariant d)
    (hQ : ExpQBound d κ c τ E t) : MLExpPin d κ c τ C E t := by
  intro hκ hc hτ hE ht0 ht1 hsz hbw hrc hK hSD h4 hDL h61 ε hε
  have hH : MLExpHyps d κ c τ E t :=
    ⟨hκ, hc, hτ, hE, ht0, ht1, hsz, hbw, hrc, hK, h4, hDL, h61⟩
  have hDC : ExpDriftBoundConcl d E t := hDrift hH
  have hQC := hQ hH hDC hInv
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hC2a : 0 < |C 2| + 1 := by positivity
  have hτ'0 : 0 < ε / (8 * (|C 2| + 1)) := by positivity
  have hDd0 : 0 < |C 2| + 6 := by positivity
  have hε16 : 0 < ε / 16 := by positivity
  have hm₀0 : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  have hx : |C 2 * (ε / (8 * (|C 2| + 1)))| / 2 ≤ ε / 16 := by
    rw [abs_mul, abs_of_pos hτ'0]
    have : |C 2| * (ε / (8 * (|C 2| + 1))) ≤ ε / 8 := by
      calc |C 2| * (ε / (8 * (|C 2| + 1))) = ε / 8 * (|C 2| / (|C 2| + 1)) := by field_simp
        _ ≤ ε / 8 * 1 := by
          gcongr
          rw [div_le_one hC2a]; linarith
        _ = ε / 8 := by ring
    linarith
  have hker := hsize.eventually
    (hSD hκ hc hτ 2 le_rfl (ε / (8 * (|C 2| + 1))) (|C 2| + 6) hτ'0 hDd0 (ε / 16) hε16)
  have hdr := hDC (ε / 16) hε16 (ε / (8 * (|C 2| + 1))) hτ'0 (|C 2| + 6) hDd0
  have hq := hQC (ε / 16) hε16 (ε / (8 * (|C 2| + 1))) hτ'0 (|C 2| + 6) hDd0
  have habs := hsize.eventually (eventually_le_rpow (16 / (ε * (Real.sqrt (2 * κ) / 2)) + 2)
    (show 0 < 3 * ε / 4 by positivity))
  filter_upwards [hker, hbw, hrc, hdr, hq, habs, hsize.eventually_ge_atTop 1] with
    n hkn hbwn hrcn hdrn hqn habsn hN1 σ a
  -- facts at this size index
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hWpos : 0 < d.W n := d.W_pos n
  have hW1 : (1 : ℝ) ≤ ((d.W n : ℕ) : ℝ) := by exact_mod_cast hWpos
  have hN1r : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hsizeeq : d.W n ^ 2 * d.L n ^ 2 = d.size n := (Sizes.size_eq d n).symm
  have hWN : ((d.W n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
    have h : d.W n ^ 2 ≤ d.size n := by
      rw [Sizes.size_eq]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    exact_mod_cast h
  have hEn' : |E n| ≤ 2 - κ := hE n
  have hEn : |E n| < 2 := by linarith [hE n]
  have hT0 : 0 ≤ t n := ht0 n
  have hT1 : t n < 1 := ht1 n
  have hTle : t n ≤ 1 - ((d.size n : ℕ) : ℝ) ^ (-1 + τ) := by linarith
  have hlogT := MLExpVocab_log_le hN1r hτ hT1 hrcn
  have him := MLExpVocab_im_ge hκ hEn'
  have hMT0 : 0 < scaleM (d.L n) (d.W n) (E n) (t n) := scaleM_pos hL1 hWpos hEn hT1
  have hX0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ := by positivity
  have hy : ((d.W n : ℕ) : ℝ) ^ (-(|C 2| + 6) + C 2) ≤
      (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ := by
    have h1 : ((d.W n : ℕ) : ℝ) ^ (-(|C 2| + 6) + C 2) ≤ ((d.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [le_abs_self (C 2)])
    have h2 : ((d.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) = (((d.W n : ℕ) : ℝ) ^ 6)⁻¹ := by
      rw [Real.rpow_neg (by linarith)]
      norm_cast
    have h3 : scaleM (d.L n) (d.W n) (E n) (t n) ^ 3 ≤ ((d.W n : ℕ) : ℝ) ^ 6 := by
      calc scaleM (d.L n) (d.W n) (E n) (t n) ^ 3 ≤ (((d.W n : ℕ) : ℝ) ^ 2) ^ 3 :=
            pow_le_pow_left₀ hMT0.le (MLExpVocab_scaleM_le_W2 hL1 hT1) 3
        _ = ((d.W n : ℕ) : ℝ) ^ 6 := by ring
    calc _ ≤ (((d.W n : ℕ) : ℝ) ^ 6)⁻¹ := h1.trans h2.le
      _ ≤ _ := inv_anti₀ (by positivity) h3
  by_cases hσ : σ 0 = σ 1
  · -- repeated sign: Duhamel without `𝒬`, Case 1
    have hduh := hDuh n (E n) (t n) hEn hT0 hT1 σ a
    have hF : ∀ u ∈ Set.Icc (0 : ℝ) (t n),
        ‖Ugen (d.L n) (E n) σ u (t n) (expDriftT d n (E n) u σ) a‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (ε / 16) *
            (((d.W n : ℕ) : ℝ) ^ (C 2 * (ε / (8 * (|C 2| + 1)))) *
              tmax (d.L n) (expDriftT d n (E n) u σ) * ratioR (d.L n) (E n) u (t n) ^ 2 +
              ((d.W n : ℕ) : ℝ) ^ (-(|C 2| + 6) + C 2)) := by
      intro u hu
      have hk := hkn (d.L n) (d.W n) hL3 hsizeeq hbwn (E n) hEn' u (t n) hu.1 hu.2 hTle σ
        (expDriftT d n (E n) u σ) (hdrn u hu σ).1 a
      obtain ⟨-, hc1, -⟩ := hk
      exact hc1 (MLExpVocab_repeat_of_eq hσ)
    have hΛ : ∀ u ∈ Set.Icc (0 : ℝ) (t n), tmax (d.L n) (expDriftT d n (E n) u σ) ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 16) *
          ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) :=
      fun u hu => (hdrn u hu σ).2
    have hcore := MLExpVocab_core hEn hT0 hT1 hN1r hWN hL1 hlogT hε16.le hε16.le hy
      (F := fun u => Ugen (d.L n) (E n) σ u (t n) (expDriftT d n (E n) u σ) a)
      (Λ := fun u => tmax (d.L n) (expDriftT d n (E n) u σ)) hF hΛ
    have hfin := MLExpVocab_final hN1r hε hm₀0 him hx hX0 habsn
    change ‖expErrT d n (E n) (t n) σ a‖ ≤ _
    rw [hduh]
    have hnn : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (ε / 16) *
        (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ := by positivity
    linarith
  · -- alternating sign: Duhamel with `𝒬`, Case 4
    have halt : Alternating σ := MLExpVocab_alt_of_ne hσ
    have hduh := hQDuh n (E n) (t n) hEn hT0 hT1 σ a
    have hF : ∀ u ∈ Set.Icc (0 : ℝ) (t n),
        ‖Ugen (d.L n) (E n) σ u (t n) (qDriftT d n (E n) u σ) a‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (ε / 16) *
            (((d.W n : ℕ) : ℝ) ^ (C 2 * (ε / (8 * (|C 2| + 1)))) *
              tmax (d.L n) (qDriftT d n (E n) u σ) * ratioR (d.L n) (E n) u (t n) ^ 2 +
              ((d.W n : ℕ) : ℝ) ^ (-(|C 2| + 6) + C 2)) := by
      intro u hu
      obtain ⟨hsz0, hsym, hdec, -⟩ := hqn.1 u hu σ halt
      have hk := hkn (d.L n) (d.W n) hL3 hsizeeq hbwn (E n) hEn' u (t n) hu.1 hu.2 hTle σ
        (qDriftT d n (E n) u σ) hdec a
      obtain ⟨-, -, hc4⟩ := hk
      exact hc4 hsz0 hsym
    have hΛ : ∀ u ∈ Set.Icc (0 : ℝ) (t n), tmax (d.L n) (qDriftT d n (E n) u σ) ≤
        ((d.size n : ℕ) : ℝ) ^ (ε / 16) *
          ((etaT (E n) u)⁻¹ * (scaleM (d.L n) (d.W n) (E n) u ^ 3)⁻¹) :=
      fun u hu => (hqn.1 u hu σ halt).2.2.2
    have hcore := MLExpVocab_core hEn hT0 hT1 hN1r hWN hL1 hlogT hε16.le hε16.le hy
      (F := fun u => Ugen (d.L n) (E n) σ u (t n) (qDriftT d n (E n) u σ) a)
      (Λ := fun u => tmax (d.L n) (qDriftT d n (E n) u σ)) hF hΛ
    have hfin := MLExpVocab_final hN1r hε hm₀0 him hx hX0 habsn
    have hend := hqn.2 σ halt a
    have hsplit : expErrT d n (E n) (t n) σ a =
        Qop (d.L n) (t n) (expErrT d n (E n) (t n) σ) a +
          Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0) * vartheta (d.L n) (t n) a := by
      simp only [Qop]; ring
    change ‖expErrT d n (E n) (t n) σ a‖ ≤ _
    calc ‖expErrT d n (E n) (t n) σ a‖
        = ‖Qop (d.L n) (t n) (expErrT d n (E n) (t n) σ) a +
            Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0) * vartheta (d.L n) (t n) a‖ := by
          rw [← hsplit]
      _ ≤ ‖Qop (d.L n) (t n) (expErrT d n (E n) (t n) σ) a‖ +
            ‖Psum (d.L n) (expErrT d n (E n) (t n) σ) (a 0) * vartheta (d.L n) (t n) a‖ :=
          norm_add_le _ _
      _ ≤ (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ *
            (((d.size n : ℕ) : ℝ) ^ (ε / 16 + ε / 16 + |C 2 * (ε / (8 * (|C 2| + 1)))| / 2) *
                (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) +
              ((d.size n : ℕ) : ℝ) ^ (ε / 16)) +
            ((d.size n : ℕ) : ℝ) ^ (ε / 16) * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹ :=
          add_le_add (by rw [hduh]; exact hcore) hend
      _ ≤ _ := hfin

end Main

/-! ## 7. Two lemmas for the drift and `𝒬`-term statements -/

section Step61Unif

/-- **`Step61Concl` uniformly in the time** (`ExpDriftBound`, `ExpQBound`): from `Step61Concl d E u`
along every section `0 ≤ u_n ≤ t_n` (the hypothesis of `MLExpPin`) to `∀ᶠ n, ∀ u ∈ [0,t_n]` (a bad
section is selected by choice at every `n` with a bad time; same argument as
`perTimeDomAt_iff_forall_section`, `Path/PerTime.lean`). -/
theorem step61_unif {E t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (h61 : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → Step61Concl d E u) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (t n), ∀ a : Z2 (d.L n),
      ‖oneLoopExpErr d n (E n) u a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ := by
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  classical
  let bad : ∀ n : ℕ, ℝ → Prop := fun n u => ∃ a : Z2 (d.L n),
    ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ <
      ‖oneLoopExpErr d n (E n) u a‖
  let w : ℕ → ℝ := fun n => if h : ∃ u ∈ Set.Icc (0 : ℝ) (t n), bad n u then h.choose else 0
  have hw : ∀ n, (∃ u ∈ Set.Icc (0 : ℝ) (t n), bad n u) →
      w n ∈ Set.Icc (0 : ℝ) (t n) ∧ bad n (w n) := by
    intro n h
    simp only [w, h, dite_true]
    exact h.choose_spec
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    by_cases h : ∃ u ∈ Set.Icc (0 : ℝ) (t n), bad n u
    · exact (hw n h).1.1
    · simp only [w, h, dite_false]
      exact le_rfl
  have hwt : ∀ n, w n ≤ t n := by
    intro n
    by_cases h : ∃ u ∈ Set.Icc (0 : ℝ) (t n), bad n u
    · exact (hw n h).1.2
    · simp only [w, h, dite_false]
      exact ht0 n
  have hstep := h61 w hw0 hwt ε hε
  obtain ⟨n, hn, hgood⟩ := (hcon.and_eventually hstep).exists
  push Not at hn
  obtain ⟨u, hu, a, ha⟩ := hn
  have hex : ∃ u ∈ Set.Icc (0 : ℝ) (t n), bad n u := ⟨u, hu, a, ha⟩
  obtain ⟨-, a', ha'⟩ := hw n hex
  exact absurd (hgood a') (not_le.2 ha')

end Step61Unif

end RBM.Evol
