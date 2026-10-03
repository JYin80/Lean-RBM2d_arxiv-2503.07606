/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

import RBM2D.Path.PerTime
import RBM2D.Path.Walk
import RBM2D.Path.Scales
import RBM2D.Path.Kernel
import RBM2D.Path.Step2Props
import RBM2D.Loop.Kcal
import RBM2D.Gauss.SpectralWindow
import RBM2D.Gauss.Domination
import RBM2D.Propagator.Basic
import RBM2D.Defs.Dist

/-!
# Vocabulary of the induction step: functionals, hypothesis shapes, per-time conclusions

**Definitions only**: every statement is a `Prop`-valued `def`; nothing is proved.  The file
defines the loop-error functionals `lkGen`, `xiL`, `xiLK`, the tensor operators `Ugen`, `UgenPair`
with the decay, sum-zero and symmetry properties of tensors, the local form `LocalForm`, the
hypothesis shapes of Theorem `lem:main_ind` (Step 1, Step 2, the per-time conclusions of Steps 3--5)
and the conclusions of Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`.  It builds on `RBM.Path`
(the scales `ellT`, `scaleM`, `tailT`, the matrices `ukerMat`, `blockMat`, the loop errors
`lkErrMat`, `llErrMat`, `loopAbs`, and the hypothesis shapes `Bandwidth`, `CondStInd`, `RangeCond`,
`InitDecay`, `InitLocal`, `Step1LoopPT`, `Step1WeakLawPT`, `Step2LocalPT`, `Step2DecayPT`,
`Step2Eq53PT`).

Paper: arXiv:2503.07606; statements are cited by the paper's `\label`s (`lem:main_ind`,
`def:XiL`, ...).

Energy: every sequence-level statement takes `E : ℕ → ℝ` with `∀ n, |E n| ≤ 2 - κ`;
matrix-level functionals and scales take one real `E`.

Layout: 1. functionals (`lkGen`, `xiL`, `xiLK`, `Ugen`, `UgenPair`, decay and sum-zero
properties, `LocalForm`); 2. inputs from other results (`KboundConcl`, `Step2TargetN`); 3. Step 1
and the hypotheses of Theorem `lem:main_ind`; 4. Steps 3--5 per-time conclusions; 5. the
conclusions of `lem:main_ind` and of Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`, and the
chain times.

`RBM.KLoop` names are used qualified (`KLoop.Kcal`, `KLoop.Mt`, `KLoop.mSig`, ...) and
`RBM.KLoop` is not opened.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)


/-! ## 1. Functionals -/

/-- The admissible sizes diverge: `N = size n → ∞`. -/
def SizeTendsto : Prop :=
  Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop

section NewFunctionals

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `|(𝓛 - 𝒦)_{u,σ,a}|` for a loop of length `k`, with the primitive loop `𝒦` of `Def_Ktza`
(`RBM.KLoop.Kcal`). -/
def lkGen (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℝ :=
  ‖gloop L W (blockMat M) (spectralZ E u) (loopOf σ a) - KLoop.Kcal L W E u (loopOf σ a)‖

/-- `Ξ^{(𝓛)}_{u,k} = max_{σ,a} |𝓛_{u,σ,a}| M_u^{k-1}` (`def:XiL`). -/
def xiL (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin k → Bool) × (Fin k → Z2 L) => loopAbs L W E u M p.1 p.2) *
    scaleM L W E u ^ (k - 1)

/-- `Ξ^{(𝓛-𝒦)}_{u,k} = max_{σ,a} |(𝓛-𝒦)_{u,σ,a}| M_u^{k}` (`def:XiL`, `def:XIL-K`). -/
def xiLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin k → Bool) × (Fin k → Z2 L) => lkGen L W E u M p.1 p.2) *
    scaleM L W E u ^ k

/-- `(𝒰_{v,w,σ} ∘ 𝒜)_a = Σ_b Π_i ((1 - v m_i m_{i+1} S)/(1 - w m_i m_{i+1} S))_{a_i b_i} 𝒜_b`
for a loop of length `k ≥ 1` (`def_Ustz`), `m_i = m(σ_i)` at the energy `E`. -/
def Ugen (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ :=
  ∑ b : Fin k → Z2 L, (∏ i : Fin k,
      ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) * A b

/-- `‖𝒜‖_max`. -/
def tmax {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => ‖A a‖

/-- **`(u,τ,D)` decay** (`Def_decay`; `deccA0`):
`max_{i,j} |a_i - a_j|_L ≥ ℓ_u W^τ ⟹ |𝒜_a| ≤ W^{-D}`. -/
def HasDecay (u τ D : ℝ) {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ a : Fin k → Z2 L, ellT L u * (W : ℝ) ^ τ ≤ (KLoop.maxDist L a : ℝ) →
    ‖A a‖ ≤ (W : ℝ) ^ (-D)

/-- The sum-zero property `Σ_{a_2,…,a_k} 𝒜_a = 0` for every `a_1` (`sumAzero`). -/
def SumZero {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ a₁ : Z2 L, ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), A a = 0

/-- The symmetry `𝒜_{a, a+s_2, …} = 𝒜_{a, a-s_2, …}` (`symmetric_tensor`; the
operator `ℛ` of `eq:case4_B`). -/
def Symmetric {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ (c : Z2 L) (r : Fin k → Z2 L), r 0 = 0 → A (fun i => c + r i) = A (fun i => c - r i)

/-- `((𝒰_{v,w,σ} ⊗ 𝒰_{v,w,σ̄}) ∘ 𝒜)_{a,a}` for a `2k`-tensor `𝒜` (`eq:double_sum_zero_tensor`;
`σ̄` flips every sign). -/
def UgenPair (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ :=
  ∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
    (∏ i : Fin k,
        ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) *
      (∏ i : Fin k,
        ukerMat L (KLoop.mSig E (!σ i) * KLoop.mSig E (!σ (i + 1))) v w (a i) (b' i)) * A b b'

/-- `‖𝒜‖_max` for a `2k`-tensor. -/
def tmax2 {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : (Fin k → Z2 L) × (Fin k → Z2 L) => ‖A p.1 p.2‖

/-- `(u,τ,D)` decay of a `2k`-tensor, over all `2k` labels. -/
def HasDecay2 (u τ D : ℝ) {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ a a' : Fin k → Z2 L, ellT L u * (W : ℝ) ^ τ ≤ (KLoop.maxDist L (Fin.append a a') : ℝ) →
    ‖A a a'‖ ≤ (W : ℝ) ^ (-D)

/-- The double sum-zero property (`eq:double_sum_zero_tensor`). -/
def DoubleSumZero {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop :=
  (∀ (a₁ : Z2 L) (a' : Fin k → Z2 L),
      ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), A a a' = 0) ∧
    ∀ (a : Fin k → Z2 L) (a₁ : Z2 L),
      ∑ a' ∈ Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a₁), A a a' = 0

/-- `G_s(σ)_{xy}` at the matrix `M` (entries in (`a-local-form`)). -/
def gEntry (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) (x y : Idx L W) : ℂ :=
  (M - (if σ then spectralZ E s else (starRingEnd ℂ) (spectralZ E s)) •
    (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ x y

end NewFunctionals


/-- The deterministic coefficients of the local form (`a-local-form`): a polynomial of
degree `≤ K` in the entries `G_s(σ_i)_{x_i y_i}`; `coef b j q` is the coefficient of the monomial
`∏_{i<j} G_s(q_i.2.2)_{q_i.1, q_i.2.1}`. -/
structure LocalForm (L W k K : ℕ) where
  coef : (Fin k → Z2 L) → (j : Fin (K + 1)) → (Fin j → Idx L W × Idx L W × Bool) → ℂ

namespace LocalForm

variable {L W k K : ℕ} [NeZero L] [NeZero W]

/-- The tensor `𝒜_b` of (`a-local-form`) at the matrix `M`. -/
def eval (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (b : Fin k → Z2 L) : ℂ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
    F.coef b j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1

/-- The locality condition of (`a-local-form`): a non-zero coefficient has every entry
`(x_i, y_i)` within `W^τ ℓ_s` of some label `b_m` (blocks `[x] = (splitEquiv x).1`). -/
def Local (F : LocalForm L W k K) (τ s : ℝ) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i, ∃ m : Fin k,
    ((zdist2 L ((splitEquiv L W (q i).1).1 - b m) +
        zdist2 L ((splitEquiv L W (q i).2.1).1 - b m) : ℕ) : ℝ) < ellT L s * (W : ℝ) ^ τ

end LocalForm


/-! ## 2. Inputs from other results (hypothesis shapes) -/

/-- **Kernel bound input** (`ML:Kbound`, `ML:Kbound+pi`): the conclusion of the kernel bound,
for one `κ`, over the parameter set `KLoop.Par κ N` (which contains the energy). -/
def KboundConcl (κ : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    UnifDetDom (U := fun N => (p : KLoop.Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
      (fun _ u => ‖KLoop.Kcal u.1.L u.1.W u.1.E u.1.t (loopOf u.2.1 u.2.2)‖)
      (fun _ u => (KLoop.Mt u.1.L u.1.W u.1.E u.1.t)⁻¹ ^ (n - 1))

/-- **Step 2 input** (`Gt_bound_flow`, `Eq:Gdecay_w`, (53)), for an energy sequence
`E : ℕ → ℝ`, with `SizeTendsto` among the hypotheses. -/
def Step2TargetN (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → SizeTendsto d →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    InitDecay d E s → InitLocal d E s → Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    Step2LocalPT d E s t ∧ Step2DecayPT d E s t ∧ Step2Eq53PT d E s t

/-! ## 3. Step 1 and the hypotheses of `lem:main_ind` -/

/-- (`Eq:L-KGt+IND`) at the time `s`: for every loop length `k ≥ 1`,
`max_{σ,a} |(𝓛-𝒦)_{s,σ,a}| ≺ M_s^{-k}`. -/
def InitLK (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)
    (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ k)

/-- `max_{i,j} |(G_u)_{ij}|` at the matrix `M` (the event `Ω` of `usuayzoo`). -/
def gMax {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun q : Idx L W × Idx L W =>
    ‖(M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ q.1 q.2‖

/-- (`lRB1`) in the uniform form Step 1 gives (union over `u` inside `P`,
`StochDomAt`; the net argument after `Gopboundu`). -/
def Step1LoopUnif (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → StochDomAt (Sizes.seqP d) d.size
    (U := fun n => Path.TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (ellT (d.L n) p.1 / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
      (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1))

/-- (`Gtmwc`) in the uniform form Step 1 gives (`StochDomAt`). -/
def Step1WeakLawUnif (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDomAt (Sizes.seqP d) d.size
    (U := fun n => Path.TimeIcc s t n × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ ((1 : ℝ) / 4))

/-- The hypotheses of Theorem `lem:main_ind` in sequence form, with the size
divergence, `RangeCond` and `Bandwidth`: fixed `κ, c, τ` first, then
the energy and time sequences. -/
def MainIndHyp (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ ∧ (∀ n, |E n| ≤ 2 - κ) ∧ 0 < c ∧ 0 < τ ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ t n) ∧
    (∀ n, t n < 1) ∧ SizeTendsto d ∧ Bandwidth d c ∧ CondStInd d E s t ∧ RangeCond d τ t ∧
    InitLK d E s ∧ InitDecay d E s ∧ InitLocal d E s

/-! ## 4. Steps 3–5 -/

/-- The per-time family `u ↦ ξ(u)` over `u ∈ [s,t]` with a time-only control. -/
abbrev PT (s t : ℕ → ℝ) (ξ ζ : ∀ n, Path.TimeIcc s t n → Sizes.SeqΩ d → ℝ) : Prop :=
  Path.PerTimeDomAt (Sizes.seqP d) d.size ξ ζ

/-- **The hypothesis shape of `lem:STOeq_NQ` + `lem:STOeq_Qt` (per time)**, in the form
in which Steps 3–4 use (`am;asoi222`) (the stochastic domination is `PerTimeDomAt`): if
`Ξ^{(𝓛)}_{u,2k+2} ≺ Λ` and every term of the first line of (`am;asoi222`) is `≺ Φ`, per time
over `u ∈ [s,t]`, with `Λ ≥ 1`, `Φ ≥ 0` deterministic, then `Ξ^{(𝓛-𝒦)}_{u,k} ≺ Λ^{1/2} + Φ`,
per time over `u ∈ [s,t]`.  The second line of (`am;asoi222`) (the `𝔼`-terms) is dominated by
`Φ` (the paper: "for the sake of stochastic domination, we can drop the second line"). -/
def STOeqPT (E : ℕ → ℝ) (s t : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
    PT d s t (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (2 * k + 2))
      (fun n _ _ => Λ n) →
    (∀ m, 1 ≤ m → m < k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m)
        (fun n _ _ => Φ n)) →
    (∀ m, 2 ≤ m → m ≤ k →
      PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) m *
          xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k - m + 2) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹)
        (fun n _ _ => Φ n)) →
    PT d s t (fun n u ω => xiL (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) (k + 1))
      (fun n _ _ => Φ n) →
    PT d s t (fun n u ω => xiLK (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) k)
      (fun n _ _ => Λ n ^ ((1 : ℝ) / 2) + Φ n)

/-- **The `(+,+)` two-loop input of the Step 3 base case**: per time over
`u ∈ [s,t]`, `Ξ^{(𝓛-𝒦)}_{u,2}` restricted to `σ = (+,+)` is `≺ M_s^{1/2}`.  The paper's base
case cites only (`Eq:Gdecay_w`), which is the `(+,-)` bound. -/
def PPTwoLoopPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  PT d s t (fun n u ω => Finset.univ.sup' Finset.univ_nonempty
      (fun p : Z2 (d.L n) × Z2 (d.L n) =>
        lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) ![true, true] ![p.1, p.2]) *
      scaleM (d.L n) (d.W n) (E n) u ^ 2)
    (fun n _ _ => scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2))

/-- (`Eq:LGxb`), per time: `max_{σ,a} |𝓛_{u,σ,a}| ≺ M_u^{-k+1}`, `u ∈ [s,t]`, every
`k ≥ 1`. -/
def Step3PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Path.TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1))

/-- (`Eq:L-KGt-flow`), per time: `max_{σ,a} |(𝓛-𝒦)_{u,σ,a}| ≺ M_u^{-k}`. -/
def Step4PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Path.TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ k)

/-- (`Eq:Gdecay_flow`), per time: for every `D > 0`,
`|(𝓛-𝒦)_{u,(+,-),(a,b)}| ≺ M_u^{-2} exp(-(|a-b|_L/ℓ_u)^{1/2}) + W^{-D}` (`= 𝒯_{u,D}`). -/
def Step5PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), Path.PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Path.TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => tailT (d.L n) (d.W n) (E n) D p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ))

/-! ## 5. The assembled theorem, the initial data, and the chain -/

/-- The conclusion of Theorem `lem:main_ind`: (`Eq:L-KGt+IND`),
(`Eq:Gdecay+IND`), (`Gt_bound+IND`) at the time `t`. -/
def MainIndConcl (E : ℕ → ℝ) (t : ℕ → ℝ) : Prop :=
  InitLK d E t ∧ InitDecay d E t ∧ InitLocal d E t

/-- The conclusions of Lemmas `ML:GLoop` (`Eq:L-KGt`, `Eq:L-KGt2`),
`ML:GLoop_expec` (`Eq:Gdecay`) and `ML:GtLocal` (`Gt_bound`) at the time `t`,
per sequence. -/
def MLConcl (E : ℕ → ℝ) (t : ℕ → ℝ) : Prop :=
  MainIndConcl d E t ∧
  ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => loopAbs (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)
    (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1))

/-- The chain times of the proof strategy of `lem:main_ind` in sequence form:
`1 - s_k = (1 - t)^{k/n₀}` with `n₀` fixed (the paper's `1 - s_k = W^{-kτ'}` needs an
`N`-dependent `τ'`).
`s_0 = 0`, `s_{n₀} = t`. -/
def chainTime (t : ℕ → ℝ) (n₀ k : ℕ) (n : ℕ) : ℝ :=
  1 - (1 - t n) ^ ((k : ℝ) / n₀)

end RBM.Ind


end
