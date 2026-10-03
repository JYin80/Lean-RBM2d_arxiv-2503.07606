/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridGoodEvent
import RBM2D.Induction.GridAssemblyN
import RBM2D.Induction.LoopC2N
import RBM2D.Induction.QVN
import RBM2D.Induction.B45
import RBM2D.Induction.DecayLoop
import RBM2D.Induction.Step45
import RBM2D.Induction.GridEnvelopeN
import RBM2D.Induction.AzumaProxyN
import RBM2D.Evolution.Bridge
import RBM2D.Evolution.Case3
import RBM2D.Path.Transfer
import RBM2D.Evolution.MLExpVocab

/-!
# Stopped-hierarchy endpoints: vocabulary, endpoint statements and assembly

Namespace `RBM.Ind`, `variable (d : Sizes)`.  Paper: arXiv:2503.07606, Section 5:
`lem:STOeq_NQ`, `lem:STOeq_Qt`.

Sections: 1. vocabulary (`STOeqLevels`, `G4Inputs`, `g4Inputs`, `altB`, `altQB`,
`TensorInvariantK`);
2. the endpoint statements (`GridEndConcl`, `NonAltGridEnd`, `AltLocalForm`, `AltExpSymm`,
`AltGridEnd`);
3. the transfer and assembly (`gridEnd_to_flow`, `stoeqPT_of_gridEnds`,
`stoeqTargetV2_of_pins`, `stoeqTargetV2_of_gridEnds`); 4. compositions with other pieces of the
induction; 5. the variance form of the Azuma step.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Vocabulary -/

/-- The four level hypotheses of `STOeqPT` (module `RBM2D.Induction.Defs`), as one `Prop`: per time
over `u ∈ [s,t]`, `Ξ^{(𝓛)}_{u,2k+2} ≺ Λ`; `Ξ^{(𝓛-𝒦)}_{u,m} ≺ Φ` for `1 ≤ m < k`;
`Ξ^{(𝓛-𝒦)}_{u,m} Ξ^{(𝓛-𝒦)}_{u,k-m+2} M_u^{-1} ≺ Φ` for `2 ≤ m ≤ k`; `Ξ^{(𝓛)}_{u,k+1} ≺ Φ`.
These are the induction hypotheses of Steps 3 and 4 (see `s45_main_ind` in
`RBM2D.Induction.Step45`): lengths `< k` (lower levels), the products, and the levels `k+1`, `2k+2`
above `k`. -/
def STOeqLevels (E s t : ℕ → ℝ) (k : ℕ) (Λ Φ : ℕ → ℝ) : Prop :=
  PT d s t (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (2 * k + 2))
      (fun n _ _ => Λ n) ∧
    (∀ m, 1 ≤ m → m < k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m)
        (fun n _ _ => Φ n)) ∧
    (∀ m, 2 ≤ m → m ≤ k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m *
          xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k - m + 2) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹)
        (fun n _ _ => Φ n)) ∧
    PT d s t (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k + 1))
      (fun n _ _ => Φ n)

/-- **The sub-Gaussian and moment inputs of the endpoints** (`d` fixed): the sub-Gaussian proxy
theorem `AzumaSubGN` (proved as `azumaSubGN`), the uniform `Y` moments `YMomentsUnifN` (with `C_P`
before the grid `K`; proved as `yMomentsUnifN` in `RBM2D.Induction.AzumaProxyN`) and the theorem
`SumWeightedStepErrN_Stmt` (proved as `sum_weighted_stepErrN_le`).  All three are proved
(`g4Inputs`); the bundle stays as a premise of the four endpoint statements. -/
def G4Inputs : Prop :=
  (∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), AzumaSubGN d s t K) ∧
    (∀ (κ τ' : ℝ) (E s t : ℕ → ℝ), YMomentsUnifN d κ τ' E s t) ∧ SumWeightedStepErrN_Stmt

/-- **The G4 inputs hold**: `azumaSubGN`, `yMomentsUnifN` and `sum_weighted_stepErrN_le`. -/
theorem g4Inputs : G4Inputs d :=
  ⟨fun s t K => azumaSubGN d s t K, fun κ τ' E s t => yMomentsUnifN d κ τ' E s t,
    sum_weighted_stepErrN_le⟩

/-- The tensors of `int_K-L+Q2`: `B₀ = (𝓛-𝒦)_{u,σ}`, `B₁ = Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l`,
`B₂ = 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)}`, `B₃ = 𝓔^{(G̃)}`, `B₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)`, `B₅ = 𝒫(𝓛-𝒦) ϑ̇`, as
`k`-tensors at the matrix `M` (built from `lkTensor`, `ksimLK`, `elklkN`, `egtN`, `B4`, `B5`). -/
def altB (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    [NeZero k] (σ : Fin k → Bool) : Fin 6 → (Fin k → Z2 L) → ℂ
  | 0 => lkTensor L W E u M σ
  | 1 => fun a => ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)
  | 2 => fun a => elklkN L W E u M (loopOf σ a)
  | 3 => fun a => egtN L W E u M (loopOf σ a)
  | 4 => fun a => B4 L W E u M σ a
  | 5 => fun a => B5 L W E u M σ a

/-- `𝒬_u ∘ B_m` (`int_K-L+Q2`): the tensor whose local form is given by `AltLocalForm`. -/
def altQB (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    [NeZero k] (σ : Fin k → Bool) (m : Fin 6) : (Fin k → Z2 L) → ℂ :=
  Qop L u (altB L W E u M σ m)

/-- Invariance of a `k`-tensor under translation and negation of all labels (the automorphisms of
`Z_L²` that preserve `S^{(B)}`); the `k`-label form of `MLExpVocab.TensorInvariant`. -/
def TensorInvariantK {L : ℕ} [NeZero L] {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : Prop :=
  (∀ (v : Z2 L) (a : Fin k → Z2 L), A (fun i => a i + v) = A a) ∧
    ∀ a : Fin k → Z2 L, A (fun i => -a i) = A a

/-! ## 2. The endpoint statements -/

/-- **The conclusion shared by the two grid endpoints.**
Fix the target length `k ≥ 2` (the paper's `n`), the level pair `Λ, Φ` (`Λ ≥ 1` eventually; the four
`STOeqPT` levels as hypotheses, `STOeqLevels`), the end time `v ∈ [s,t]`, the loss `ε > 0` and the
failure exponent `D₁ > 0`.  Then there are exponents `ε₁, τ', D'` (the good-set loss `Γ = N^{ε₁}`, the
label window `ℓ_u W^{τ'}` and the decay `W^{-D'}` of `GoodSetN`) and a grid exponent `C_K` such that,
for every grid `K` with `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉` (`Δ ≤ N^{-C_K}`, `KΔ ≤ 1`), eventually in `n` there
is an event `G` of probability `≥ 1 - N^{-D₁}` (the union of the assembly events of `assembledN` over
the signs, labels and grid targets) on which: if the grid walk stays in `GoodSetN` at every grid time
`j ≤ K_n` and the initial state satisfies `(𝓛-𝒦)_{s} ≤ N^{ε₁} M_s^{-k}` (`InitLK`), then for every sign
vector of the class `p` and every label `a` the terminal state satisfies
`(𝓛-𝒦)_{v,σ,a} ≤ N^ε (Λ^{1/2} + Φ) M_v^{-k}`.  (In the one-dimensional proof the exponents are
explicit functions of `(k, ε, D₁)` only, independent of `Λ, Φ, v, K`; the statement here has the
weaker quantifier order that the assembly `gridEnd_to_flow` needs.)  The class `p` is
`¬ Alternating` (`NonAltGridEnd`) or `Alternating` (`AltGridEnd`).  The good
event and the initial event are NOT part of `G`: they are `gridGoodN` and
`InitLK ∈ MainIndHyp`, composed in `gridEnd_to_flow`. -/
def GridEndConcl (p : ∀ (k : ℕ) [NeZero k], (Fin k → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k →
  ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
  STOeqLevels d E s t k Λ Φ →
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
  ∀ ε : ℝ, 0 < ε → ∀ D₁ : ℝ, 0 < D₁ →
  ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
  ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
  (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊) →
  ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ d),
    (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) ∧
    ∀ ω ∈ G,
      (∀ j ≤ K n, pathH d s v K n j ω ∈
        GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (((d.size n : ℕ) : ℝ) ^ ε₁)
          (Λ n) (Φ n) τ' D') →
      (∀ σ : Fin k → Bool, p k σ → ∀ a : Fin k → Z2 (d.L n),
        lkGen (d.L n) (d.W n) (E n) (s n) (pathH d s v K n 0 ω) σ a ≤
          ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k) →
      ∀ σ : Fin k → Bool, p k σ → ∀ a : Fin k → Z2 (d.L n),
        lkGen (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) σ a ≤
          ((d.size n : ℕ) : ℝ) ^ ε * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
            (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k

/-- **The grid endpoint for non-alternating `σ` (`lem:STOeq_NQ`), every length `k ≥ 2`** (the
paper's `n`; `σ_i = σ_{i+1}` for some `i`, cyclic).  Premises: those
of `STOeqTargetV2` (Case 1 of `lem:sum_decay` is `SumDecayDetPrec ∈ UpstreamSteps34Prec`) and the
inputs `G4Inputs`.  A *conditional* statement: its proof consumes
`gridGoodN`-type good sets, `assembledN`, `ugenCase1Explicit`, `ugenPairCase1Explicit`,
`qvPropagatedN` and the `G4Inputs`.  In the one-dimensional formalization this is
`endpoint_nonAlt_all_plainN` and, for `k = 2`, `endpoint_nonAlt_two_ite_plainN`; here one
statement covers all `k ≥ 2`. -/
def NonAltGridEnd (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t → G4Inputs d →
  GridEndConcl d (fun k [NeZero k] σ => ¬ Alternating σ) E s t

/-- **Local forms (`int_K-L+Q2`, `eq:case4_B`, `a-local-form`)
of `𝒬_u ∘ B_m`, `m = 0..5`.**  For every `k ≥ 2`, every window exponent `τ₀ > 0` and decay
exponent `D₀ > 0` there are a degree `K` and a coefficient exponent `C'` such that, for every time
sequence `u ∈ [s,t]` and every alternating sign sequence `σ_n`, there is a family of local forms
`F_n` (polynomials of degree `≤ K` in the entries of `G_{u}`, deterministic coefficients
`≤ N^{C'}`, every entry within `ℓ_u W^{τ₀}` of a label) such that: `F_n(M)` is sum-zero for every
matrix `M` (so it is an admissible input of `SumDecayCase3Prec`, whose hypotheses it also
satisfies: coefficient bound, `Local`, `LabelDecayPT`), and `𝒬_uB_m(H_u) = F_n(H_u) + O_≺(W^{-D₀})`
per time, all labels.  The truncation of the cut sums `Σ_{a ∈ Z_L²}` of `B₁-B₃` to
`|a - b₁| ≤ ℓ_u W^{τ₀}` costs `N^{C}W^{-D}` by `DecayLoopPT` and `KcalDecay`; `𝒬_u` acts on the
coefficients (`Σ_{b₂..b_k} ϑ_{u,b} = 1`).  New in `d = 2`: the `d = 1` argument uses the
sum-zero Case 2 of `lem:sum_decay`; the contract `SumDecayDetPrec` drops Case 2, and the `d = 2`
argument uses Case 3 for the `ℚ` part and Case 4 for the `𝔼` part.  Used by `AltGridEnd`, through
`SumDecayCase3Prec`. -/
def AltLocalForm (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  MainIndHyp d κ c τ E s t → DecayLoopPT d E s t → KcalDecay κ →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (m : Fin 6) (τ₀ D₀ : ℝ), 0 < τ₀ → 0 < D₀ →
  ∃ (K : ℕ) (C' : ℝ), 0 ≤ C' ∧
    ∀ (u : ℕ → ℝ) (σ : ℕ → Fin k → Bool), (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      (∀ n, Alternating (σ n)) →
    ∃ F : ∀ n, LocalForm (d.L n) (d.W n) k K,
      (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') ∧
      (∀ n, (F n).Local τ₀ (u n)) ∧
      (∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)) ∧
      LabelDecayPT d E u F τ₀ D₀ ∧
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
        (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m
            p.2 - (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
        (fun n _ _ => (d.W n : ℝ) ^ (-D₀))

/-- **Invariance of `𝒬_u 𝔼 B_m` (`eq:case4_B`)**: for alternating `σ`
of every length `k ≥ 2` and `m = 0..5`, the deterministic tensor `𝒬_u 𝔼 B_m` is invariant under
translation and negation of the labels (the law of `H_u`, `S^{(B)}`, `𝒦_u`, `Θ` are), which gives
the hypothesis `Symmetric` of Case 4 (`TensorInvariantK.symmetric`); `Symmetric` alone is not
enough (`ϴ` does not preserve it).  The `k = 2` case of `𝔼B₂ + 𝔼B₃` is `ExpInvariant`;
there is no one-dimensional counterpart (the `d = 1` argument has no Case 4).  Deterministic,
finite size.  Used by `AltGridEnd`. -/
def AltExpSymm : Prop :=
  ∀ (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 → ∀ (k : ℕ) [NeZero k], 2 ≤ k →
    ∀ σ : Fin k → Bool, Alternating σ → ∀ m : Fin 6,
      TensorInvariantK (Qop (d.L n) u (fun b =>
        ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d)))

/-- **The grid endpoint for alternating `σ` (`lem:STOeq_Qt`; proof: `int_K-L+Q2`, `int_K-L+QQ`,
`int_K-L+QE`, `juaspuwp`, `juaspuwp234`, `uwyu92osk`, `kolkisaf`), every length `k ≥ 2`.**  The
`𝕼 = 1 - 𝔼` part of the `𝒬`-process has drift `𝒬ℚB_m` (Case 3 through the local forms of
`AltLocalForm`), martingale part `Z` (Azuma, family `𝒬∘𝓛`, Case 5 `SumDecayCase5Prec` for
`𝒬⊗𝒬`) and initial term `𝒬ℚB₀`; the `𝔼` part is deterministic (`𝒬 𝔼 B_m`: Case 4
through `AltExpSymm`, and `≺ → 𝔼` of the levels, which needs `Λ^{1/2} + Φ ≥ 1`).  The last step
`𝓛-𝒦 = 𝒬(𝓛-𝒦) + (𝒫(𝓛-𝒦))ϑ` needs `|(𝒫(𝓛-𝒦))_{a₁}ϑ_{u,a}| ≤ N^{ε} Φ M_u^{-k}` on `GoodSetN`
(`jywiiwsoks`): `b45PT'` proves it for `ϑ̇` (with `η_u^{-1}`), not for `ϑ`.
The one-dimensional counterpart is `endpoint_alt_all_plainN`. -/
def AltGridEnd (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t → G4Inputs d → AltLocalForm d κ c τ E s t → AltExpSymm d →
  GridEndConcl d (fun k [NeZero k] σ => Alternating σ) E s t

/-! ## 3. The transfer and assembly

`gridEnd_to_flow`: a grid endpoint `GridEndConcl p` of a sign class `p`, composed with
`gridGoodN`, `InitLK ∈ MainIndHyp` and the transfer law, is a per-section bound for the
flow at time `v_n` (the union over `q = (σ,a)` is inside `P`).  `stoeqPT_of_gridEnds`: the two
classes `¬ Alternating`, `Alternating` cover every `σ`, `xiLK` is the
max over `(σ,a)`, and `perTimeDomAt_iff_forall_section` replaces the Hölder lift of the
one-dimensional argument. -/

section Assembly

variable {d}

private theorem StoppedEndDefs_measurable_lkGen (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => lkGen L W E u M σ a :=
  ((GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ a)).sub_const _).norm

private theorem StoppedEndDefs_measurable_pathH (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    Measurable (pathH d s v K n j) :=
  Measurable.of_eval_matrix _ fun i j' => measurable_pathH d s v K n j i j'

private theorem StoppedEndDefs_measurable_seqHflow (n : ℕ) (u : ℝ) :
    Measurable (Sizes.seqHflow d n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n u i j

/-- **The grid-to-continuous-time transfer**: the grid state `H_{u_j}` and the flow at
`u_j` have the same law, so a measurable matrix event has the same probability on `pathP` and on
`seqP` (`transferLaw`; the per-time form is `gridTransferPT` of `RBM2D.Path.Transfer`, the
`∃ p` form is `pg_bad_eq_flow` of `RBM2D.Path.Bootstrap`). -/
theorem gridTerminal_transfer {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (j : ℕ) (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (hK : K n ≠ 0)
    {S : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)} (hS : MeasurableSet S) :
    pathP d (pathH d s v K n j ⁻¹' S) =
      Sizes.seqP d (Sizes.seqHflow d n (gridTime s v K n j) ⁻¹' S) := by
  rw [← Measure.map_apply (StoppedEndDefs_measurable_pathH s v K n j) hS,
    ← Measure.map_apply (StoppedEndDefs_measurable_seqHflow n _) hS, transferLaw d s v K n j hs0 hsv hK]

/-- The index set `(σ, a)` of a `k`-loop, times `Unit`, has at most `N^{2k}` elements. -/
private theorem StoppedEndDefs_card_le (k n : ℕ) (hN2 : 2 ≤ d.size n) :
    (Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
      ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) =
      2 ^ k * (d.L n * d.L n) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have hnat : Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) ≤ d.size n ^ (2 * k) := by
    rw [hcard, pow_mul', sq]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hN2 k) (Nat.pow_le_pow_left hLL k)
  rw [Real.rpow_natCast]
  exact_mod_cast hnat

private theorem StoppedEndDefs_three_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 3 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 3 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (3 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN3
    _ = _ := mul_one _

/-- **From a grid endpoint to a flow bound at a fixed section `v`**: the grid `K`
with `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉` is `gridK d 0 (C_K - 80)`, the good event is `gridGoodN`, the
initial event is `InitLK`, the probability is the sum of the three failure bounds, and the bound is
transferred to `seqHflow d n (v n)` by `gridTerminal_transfer`. -/
theorem gridEnd_to_flow {p : ∀ (k : ℕ) [NeZero k], (Fin k → Bool) → Prop} {κ c τ : ℝ}
    {C : ℕ → ℝ} {E s t : ℕ → ℝ} (hU : UpstreamSteps34Prec d κ c τ C)
    (hmain : MainIndHyp d κ c τ E s t) (hloc : Step2LocalPT d E s t)
    (hdec : Step2DecayPT d E s t) (hend : GridEndConcl d p E s t)
    (k : ℕ) [NeZero k] (hk : 2 ≤ k) {Λ Φ : ℕ → ℝ} (hΛ0 : ∀ n, 0 ≤ Λ n) (hΦ0 : ∀ n, 0 ≤ Φ n)
    (hΛ1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) (hlev : STOeqLevels d E s t k Λ Φ)
    (v : ∀ n, TimeIcc s t n) {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, Sizes.seqP d {ω | ∃ q : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
        p k q.1 ∧ ((d.size n : ℕ) : ℝ) ^ ε * (Λ n ^ ((1 : ℝ) / 2) + Φ n) <
          lkGen (d.L n) (d.W n) (E n) (v n : ℝ) (Sizes.seqHflow d n (v n : ℝ) ω) q.1 q.2 *
            scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, hinit, -, -⟩ := hmain'
  obtain ⟨hK, hV, -, -, -⟩ := hU
  have hsize' : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hdl : DecayLoopPT d E s t :=
    decayLoopWindow d κ c τ E s t hmain (kcalDecay κ) hV hloc hdec
  obtain ⟨h1, h2, h3, h4⟩ := hlev
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend'⟩ := hend k hk Λ Φ hΛ0 hΦ0 hΛ1 ⟨h1, h2, h3, h4⟩
    (fun n => (v n : ℝ)) (fun n => (v n).2.1) (fun n => (v n).2.2) ε hε (D + 1) (by linarith)
  -- the grid `Kg = gridK d 0 (C_K - 80)` has exponent exactly `C_K`
  have hCKeq : CK 0 (C_K - 80) = C_K := by unfold CK; ring
  set Kg : ℕ → ℕ := gridK d 0 (C_K - 80) with hKg
  have hK0 : ∀ n, Kg n ≠ 0 := gridK_ne_zero 0 (C_K - 80)
  have hKlow : ∀ n, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (Kg n : ℝ) := fun n => by
    have := rpow_CK_le_gridK (d := d) 0 (C_K - 80) n
    rwa [hCKeq] at this
  have hKup : ∀ n, Kg n ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊ := fun n => by
    have hN1 := GoodEvent_one_le_size (d := d) n
    have hpos : 0 < ((d.size n : ℕ) : ℝ) ^ C_K := Real.rpow_pos_of_pos (by linarith) _
    have hc1 : 1 ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊ := Nat.ceil_pos.2 hpos
    simp only [hKg, gridK, hCKeq]
    exact max_le hc1 le_rfl
  have hcard : ∀ᶠ n : ℕ in atTop,
      ((Kg n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (C_K + 2) := by
    have := gridK_card_le (d := d) (D := 0) (D₁ := C_K - 80) (by rw [hCKeq]; exact hCK)
    rwa [hCKeq] at this
  have hpin := hend' Kg hK0 (Eventually.of_forall hKlow) (Eventually.of_forall hKup)
  have hgood := gridGoodN d κ c τ E s (fun n => (v n : ℝ)) t Kg hmain hK (kcalDecay κ) hV hloc hdec
    hdl (fun n => (v n).2.1) (fun n => (v n).2.2) hK0 k hk Λ Φ hΛ0 hΦ0 hΛ1 h1 h2 h3 h4 (C_K + 2)
    hcard ε₁ hε₁ τ' hτ' D' hD' (D + 1) (by linarith)
  have hcardI : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ (((2 * k : ℕ) : ℝ)) :=
    (hsize'.eventually_ge_atTop 2).mono fun n hn => StoppedEndDefs_card_le k n hn
  have hI := stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (((2 * k : ℕ) : ℝ)))
    (by positivity) hcardI (hinit k (by omega))
  filter_upwards [hpin, hgood, hI ε₁ hε₁ (D + 1) (by linarith), hsize'.eventually (StoppedEndDefs_three_mul_rpow_le D)] with
    n hG hGood hInit hN3
  obtain ⟨G, hGP, hGb⟩ := hG
  have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the two matrix events
  set Sinit : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
    {M | ∃ q : (Fin k → Bool) × (Fin k → Z2 (d.L n)), ((d.size n : ℕ) : ℝ) ^ ε₁ *
      (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k < lkGen (d.L n) (d.W n) (E n) (s n) M q.1 q.2}
    with hSinit_def
  set Sterm : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
    {M | ∃ q : (Fin k → Bool) × (Fin k → Z2 (d.L n)), p k q.1 ∧
      ((d.size n : ℕ) : ℝ) ^ ε * (Λ n ^ ((1 : ℝ) / 2) + Φ n) <
        lkGen (d.L n) (d.W n) (E n) (v n : ℝ) M q.1 q.2 *
          scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k} with hSterm_def
  have hSinit : MeasurableSet Sinit := by
    have heq : Sinit = ⋃ q : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
        {M | ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k <
          lkGen (d.L n) (d.W n) (E n) (s n) M q.1 q.2} := by
      ext M; simp [hSinit_def]
    rw [heq]
    exact MeasurableSet.iUnion fun q =>
      measurableSet_lt measurable_const (StoppedEndDefs_measurable_lkGen _ _ _ _ q.1 q.2)
  have hSterm : MeasurableSet Sterm := by
    have heq : Sterm = ⋃ q : (Fin k → Bool) × (Fin k → Z2 (d.L n)),
        {M | p k q.1 ∧ ((d.size n : ℕ) : ℝ) ^ ε * (Λ n ^ ((1 : ℝ) / 2) + Φ n) <
          lkGen (d.L n) (d.W n) (E n) (v n : ℝ) M q.1 q.2 *
            scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k} := by
      ext M; simp [hSterm_def]
    rw [heq]
    refine MeasurableSet.iUnion fun q => ?_
    by_cases hq : p k q.1
    · simp only [hq, true_and]
      exact measurableSet_lt measurable_const
        ((StoppedEndDefs_measurable_lkGen _ _ _ _ q.1 q.2).mul measurable_const)
    · simp [hq]
  have hgt0 : gridTime s (fun n => (v n : ℝ)) Kg n 0 = s n := by simp [gridTime]
  have hgtK : gridTime s (fun n => (v n : ℝ)) Kg n (Kg n) = (v n : ℝ) :=
    gridTime_last s (fun n => (v n : ℝ)) Kg n (hK0 n)
  have e1 : Sizes.seqP d (Sizes.seqHflow d n (v n : ℝ) ⁻¹' Sterm) =
      pathP d (pathH d s (fun n => (v n : ℝ)) Kg n (Kg n) ⁻¹' Sterm) := by
    have := gridTerminal_transfer (d := d) (s := s) (v := fun n => (v n : ℝ)) (K := Kg) (n := n) (Kg n) (hs0 n)
      (v n).2.1 (hK0 n) hSterm
    rw [hgtK] at this
    exact this.symm
  have e0 : pathP d (pathH d s (fun n => (v n : ℝ)) Kg n 0 ⁻¹' Sinit) =
      Sizes.seqP d (Sizes.seqHflow d n (s n) ⁻¹' Sinit) := by
    have := gridTerminal_transfer (d := d) (s := s) (v := fun n => (v n : ℝ)) (K := Kg) (n := n) 0 (hs0 n) (v n).2.1 (hK0 n) hSinit
    rw [hgt0] at this
    exact this
  set Goodn : Set (PathΩ d) := {ω | ∀ j ≤ Kg n, pathH d s (fun n => (v n : ℝ)) Kg n j ω ∈
      GoodSetN (d.L n) (d.W n) (E n) (gridTime s (fun n => (v n : ℝ)) Kg n j) k
        (((d.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φ n) τ' D'} with hGoodn_def
  have hsub : pathH d s (fun n => (v n : ℝ)) Kg n (Kg n) ⁻¹' Sterm ⊆
      Goodnᶜ ∪ pathH d s (fun n => (v n : ℝ)) Kg n 0 ⁻¹' Sinit ∪ Gᶜ := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, not_or, not_not] at hno
    obtain ⟨⟨hgoodω, hinitω⟩, hGω⟩ := hno
    obtain ⟨q, hpq, hlt⟩ := hω
    have hinit' : ∀ σ : Fin k → Bool, p k σ → ∀ a : Fin k → Z2 (d.L n),
        lkGen (d.L n) (d.W n) (E n) (s n) (pathH d s (fun n => (v n : ℝ)) Kg n 0 ω) σ a ≤
          ((d.size n : ℕ) : ℝ) ^ ε₁ * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k := by
      intro σ _ a
      by_contra hcon
      exact hinitω ⟨(σ, a), not_le.1 hcon⟩
    have hb := hGb ω hGω hgoodω hinit' q.1 hpq q.2
    have hM : 0 < scaleM (d.L n) (d.W n) (E n) (v n : ℝ) :=
      scaleM_pos (by have := d.three_le_L n; omega) (d.W_pos n) (by linarith [hE n, hκ])
        (lt_of_le_of_lt (v n).2.2 (ht1 n))
    have hMk : 0 < scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k := pow_pos hM k
    have hcancel : (scaleM (d.L n) (d.W n) (E n) (v n : ℝ))⁻¹ ^ k *
        scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hM.ne', one_pow]
    have hmul := mul_le_mul_of_nonneg_right hb hMk.le
    beta_reduce at hmul hlt
    have e : ∀ A : ℝ, A * (scaleM (d.L n) (d.W n) (E n) (v n : ℝ))⁻¹ ^ k *
        scaleM (d.L n) (d.W n) (E n) (v n : ℝ) ^ k = A := fun A => by
      rw [mul_assoc, hcancel, mul_one]
    rw [e] at hmul
    exact absurd hlt (not_lt.2 hmul)
  calc Sizes.seqP d (Sizes.seqHflow d n (v n : ℝ) ⁻¹' Sterm)
      = pathP d (pathH d s (fun n => (v n : ℝ)) Kg n (Kg n) ⁻¹' Sterm) := e1
    _ ≤ pathP d (Goodnᶜ ∪ pathH d s (fun n => (v n : ℝ)) Kg n 0 ⁻¹' Sinit ∪ Gᶜ) :=
        measure_mono hsub
    _ ≤ pathP d Goodnᶜ + pathP d (pathH d s (fun n => (v n : ℝ)) Kg n 0 ⁻¹' Sinit) + pathP d Gᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        refine add_le_add (add_le_add hGood ?_) ?_
        · rw [e0]
          refine le_trans (measure_mono ?_) hInit
          intro ω hω
          obtain ⟨q, hq⟩ := hω
          exact ⟨((), q), hq⟩
        · rw [← ofReal_measureReal (measure_ne_top (pathP d) _)]
          exact ENNReal.ofReal_le_ofReal hGP
    _ = ENNReal.ofReal (3 * ((d.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hN3

private theorem StoppedEndDefs_union_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A B S : Set Ω}
    {x y : ℝ} (hx0 : 0 ≤ x) (hA : μ A ≤ ENNReal.ofReal x) (hB : μ B ≤ ENNReal.ofReal x)
    (hS : S ⊆ A ∪ B) (hx : 2 * x ≤ y) : μ S ≤ ENNReal.ofReal y := by
  refine le_trans (measure_mono hS) (le_trans (measure_union_le _ _) ?_)
  refine (add_le_add hA hB).trans ?_
  rw [← ENNReal.ofReal_add hx0 hx0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The σ-exhaustion and the label union**: from the endpoints of the two sign
classes `¬ Alternating`, `Alternating` to `STOeqPT` at every `k ≥ 2`.  `xiLK` is the max over the
`(σ,a)`; its failure event is contained in the union of the two class events; the per-time
statement of `STOeqPT` is the statement at every section (`perTimeDomAt_iff_forall_section`,
replacing the Hölder lift of the one-dimensional argument). -/
theorem stoeqPT_of_gridEnds {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    (hNA : GridEndConcl d (fun k [NeZero k] σ => ¬ Alternating σ) E s t)
    (hA : GridEndConcl d (fun k [NeZero k] σ => Alternating σ) E s t) :
    ∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k := by
  intro k hk Λ Φ hΛ0 hΦ0 hΛ1 h1 h2 h3 h4
  have : NeZero k := ⟨by omega⟩
  have hst : ∀ n, s n ≤ t n := hmain.2.2.2.2.2.1
  refine (perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size
    (fun n => ⟨⟨s n, le_rfl, hst n⟩⟩) _ _).2 ?_
  intro v τd hτd Dd hDd
  have hNA' := gridEnd_to_flow hU hmain hloc hdec hNA k hk hΛ0 hΦ0 hΛ1 ⟨h1, h2, h3, h4⟩ v hτd
    (D := Dd + 1) (by linarith)
  have hA' := gridEnd_to_flow hU hmain hloc hdec hA k hk hΛ0 hΦ0 hΛ1 ⟨h1, h2, h3, h4⟩ v hτd
    (D := Dd + 1) (by linarith)
  have hsize' : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hmain.2.2.2.2.2.2.2.1
  filter_upwards [hNA', hA', hsize'.eventually (eventually_two_mul_rpow_le Dd)] with n hn1 hn2 hn3
  refine StoppedEndDefs_union_le (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn1 hn2 ?_ hn3
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  simp only [xiLK] at hu
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
    (fun p : (Fin k → Bool) × (Fin k → Z2 (d.L n)) =>
      lkGen (d.L n) (d.W n) (E n) (v n : ℝ) (Sizes.seqHflow d n (v n : ℝ) ω) p.1 p.2)
  rw [hq] at hu
  by_cases hq1 : Alternating q.1
  · exact Or.inr ⟨q, hq1, hu⟩
  · exact Or.inl ⟨q, hq1, hu⟩

/-- **The assembly**: the endpoint statements imply `STOeqTargetV2` (module
`RBM2D.Induction.HierVocab`).  Hypotheses: `NonAltGridEnd`, `AltGridEnd` with its two inputs
`AltLocalForm` and `AltExpSymm`, and the inputs `G4Inputs`; no other
hypothesis.  Conditional: each endpoint statement is a hypothesis, not a proved theorem. -/
theorem stoeqTargetV2_of_pins {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ} (hG4 : G4Inputs d)
    (hLF : AltLocalForm d κ c τ E s t) (hSym : AltExpSymm d)
    (hNA : NonAltGridEnd d κ c τ C E s t) (hA : AltGridEnd d κ c τ C E s t) :
    STOeqTargetV2 d κ c τ C E s t := by
  intro hU hmain hloc hdec k hk
  exact stoeqPT_of_gridEnds hU hmain hloc hdec (hNA hU hmain hloc hdec hG4)
    (hA hU hmain hloc hdec hG4 hLF hSym) k hk

/-- **The assembly with the proved inputs**: `stoeqTargetV2_of_pins` at `g4Inputs d`.
Hypotheses: `NonAltGridEnd`, `AltGridEnd` with its two inputs
`AltLocalForm` and `AltExpSymm`; no other hypothesis.  Conditional: each endpoint statement is a
hypothesis, not a proved theorem. -/
theorem stoeqTargetV2_of_gridEnds {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hLF : AltLocalForm d κ c τ E s t) (hSym : AltExpSymm d)
    (hNA : NonAltGridEnd d κ c τ C E s t) (hA : AltGridEnd d κ c τ C E s t) :
    STOeqTargetV2 d κ c τ C E s t :=
  stoeqTargetV2_of_pins (g4Inputs d) hLF hSym hNA hA

end Assembly


/-! ## 4. Compositions with other pieces of the induction

* `hker_of_case1`: the `hker` field of `GridAssemblyHypN` (module `RBM2D.Induction.GridGoodN`) for
  non-alternating `σ`, class `Cls i δ X := DecayWin (ℓ_{u_i} K_w) δ X`, is `ugenCase1Explicit`:
  `κ_{im} = c_1(k,κ)(1+log L)^k K_w^{2(k-1)} ρ_{u_i,u_m}^k`, `ε_{im} = ((1-u_i)/(1-u_m))^k`.
* `driftTensor` (def) is the drift tensor of the good-set clauses.
* `qvFormN_eq_re_UgenPair`: the variance form of `azumaSubG_goodExit` is the real part of the pair
  kernel `𝒰_σ ⊗ 𝒰_σ̄` on `𝓔 ⊗ 𝓔`. -/

section Compositions

variable {d}

/-- `TensorInvariantK` gives the hypothesis `Symmetric` of Case 4 (`symmetric_tensor`): reflect all
labels about `a₁` (translate by `-a₁`, negate, translate back).  The `k`-label form of
`TensorInvariant.symmetric` of `RBM2D.Evolution.MLExpVocab`. -/
theorem TensorInvariantK.symmetric {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]
    {A : (Fin k → Z2 L) → ℂ} (h : TensorInvariantK A) : Symmetric L A := by
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

/-- **The two sign classes**: `¬ Alternating σ` is exactly the paper's
`∃ i, σ_i = σ_{i+1}` (cyclic; label `NALsigm`), the hypothesis of Case 1 of `lem:sum_decay`
(`UgenCase1Explicit`, `ugenPairCase1Explicit`); with `Alternating σ ∨ ¬ Alternating σ` (used in
`stoeqPT_of_gridEnds`) this replaces `sigma_exhaustive_nonAlt` of the one-dimensional argument. -/
theorem not_alternating_iff {k : ℕ} [NeZero k] (σ : Fin k → Bool) :
    ¬ Alternating σ ↔ ∃ i : Fin k, σ i = σ (i + 1) := by
  unfold Alternating
  constructor
  · intro h
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by cases h1 : σ i <;> cases h2 : σ (i + 1) <;> simp_all⟩
  · rintro ⟨i, hi⟩ h
    have h2 := h i
    rw [← hi] at h2
    cases h1 : σ i <;> rw [h1] at h2 <;> simp at h2

/-- The drift of the stopped hierarchy at a grid time (the expression of `GridDriftN` in
`RBM2D.Induction.HierVocab`). -/
def driftTensor (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℂ :=
  ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a) + elklkN L W E u M (loopOf σ a) +
    egtN L W E u M (loopOf σ a)

/-- **The `hker` field for non-alternating `σ` from `ugenCase1Explicit`.** -/
theorem hker_of_case1 {k : ℕ} [NeZero k] (hk : 2 ≤ k) {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {σ : Fin k → Bool}
    (hσ : ∃ i : Fin k, σ i = σ (i + 1)) {K : ℕ} {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i)
    (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m) (hu1 : ∀ i ≤ K, u i < 1) {Kw : ℝ} (hKw : 1 ≤ Kw) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Z2 L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → DecayWin L (ellT L (u i) * Kw) δ X → ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ (u i) (u m) X a‖ ≤
        cCase1 k κ * (1 + Real.log L) ^ k * Kw ^ (2 * (k - 1)) * rhoR L (u i) (u m) ^ k * M +
          ((1 - u i) / (1 - u m)) ^ k * δ :=
  fun i m him hmK X M δ hM hδ hX hcls a =>
    ugenCase1Explicit k hk L hL κ E hκ hE (u i) (u m) (hu0 i (him.trans hmK))
      (hmono i m him hmK) (hu1 m hmK) σ hσ Kw M δ hKw hM hδ X hX hcls a

end Compositions

section QV

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise (as the private `s45_Theta_star` of `RBM2D.Induction.Step45`). -/
private theorem StoppedEndDefs_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L (star ξ) a b = star (Theta L ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hSB : (SB L).map (starRingEnd ℂ) = SB L := by
    ext x y
    simp only [Matrix.map_apply, SB_apply, sbKernel]
    split_ifs <;> simp [map_ofNat]
  have hmul : (Theta L ξ).map (starRingEnd ℂ) * (1 - star ξ • SB L) = 1 := by
    have h := congrArg (fun A : Matrix (Z2 L) (Z2 L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul L hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB L).map (starRingEnd ℂ) = 1 - star ξ • SB L := by
      ext x y
      have := congrFun (congrFun hSB x) y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul] at this ⊢
      rw [this]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul L hL hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm

/-- `conj (𝒰-slot kernel with parameter ξ) = 𝒰-slot kernel with parameter conj ξ` for real `v, w`. -/
private theorem StoppedEndDefs_conj_ukerMat (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ} (hξ : ‖(w : ℂ) * ξ‖ < 1)
    (x y : Z2 L) :
    (starRingEnd ℂ) (ukerMat L ξ v w x y) = ukerMat L ((starRingEnd ℂ) ξ) v w x y := by
  have hSB : ∀ x y : Z2 L, (starRingEnd ℂ) (SB L x y) = SB L x y := fun x y => by
    simp only [SB_apply, sbKernel]
    split_ifs <;> simp [map_ofNat]
  have hT := StoppedEndDefs_Theta_star (L := L) hL hξ
  have hw : star ((w : ℂ) * ξ) = (w : ℂ) * (starRingEnd ℂ) ξ := by
    simp [Complex.conj_ofReal]
  rw [hw] at hT
  unfold ukerMat
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul,
      hSB, Complex.conj_ofReal]
    split_ifs <;> simp
  · exact (hT z y).symm ▸ rfl


private theorem StoppedEndDefs_mSig_not (E : ℝ) (s : Bool) :
    KLoop.mSig E (!s) = (starRingEnd ℂ) (KLoop.mSig E s) := by
  cases s <;> simp [KLoop.mSig]

private theorem StoppedEndDefs_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖KLoop.mSig E s‖ = 1 := by
  cases s
  · simp [KLoop.mSig, norm_spectralM hE]
  · simp [KLoop.mSig, norm_spectralM hE]

/-- **`qvFormN` is the real part of the pair kernel `𝒰_σ ⊗ 𝒰_σ̄` applied to `𝓔 ⊗ 𝓔`**: the conjugate of
the slotwise kernel of `σ` is the slotwise kernel of `σ̄` (`m(σ̄) = conj m(σ)`, `S` real). -/
theorem qvFormN_eq_re_UgenPair (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {v w : ℝ} (hw : |w| < 1)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k → Z2 L) :
    qvFormN L W E v w σ M a = (UgenPair L E σ v w (eeN L W E v M σ) a).re := by
  unfold qvFormN UgenPair
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : (starRingEnd ℂ) (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))
      v w (a i) (b' i)) = ∏ i : Fin k, ukerMat L (KLoop.mSig E (!σ i) * KLoop.mSig E (!σ (i + 1)))
      v w (a i) (b' i) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : ‖(w : ℂ) * (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))‖ < 1 := by
      rw [norm_mul, norm_mul, StoppedEndDefs_norm_mSig hE, StoppedEndDefs_norm_mSig hE, one_mul, mul_one,
        Complex.norm_real]
      simpa using hw
    rw [StoppedEndDefs_conj_ukerMat hL hn, map_mul, ← StoppedEndDefs_mSig_not, ← StoppedEndDefs_mSig_not]
  rw [hconj]

end QV

end RBM.Ind

end
