/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Case3Defs
import RBM2D.Induction.Step3
import RBM2D.Induction.Step45
import RBM2D.Path.Expansion
import RBM2D.Path.DuhamelTail
import RBM2D.Path.QVIdentity

/-!
# The vocabulary of the loop hierarchy and the statements used by the induction

Every declaration is a `Prop`-valued (or auxiliary) definition; no theorem is proved.  The
clause of `lem_+Q` on decay is stated in the corrected form `QopDecay` (far entries of `𝒬_t𝒜` are
`≤ W^{-D}(2 + ‖𝒜‖_max)`); the literal clause of the paper, with the same `(t,τ,D)` decay for
`𝒬_t𝒜` as for `𝒜`, is not used.

Paper: arXiv:2503.07606, Sections 1 and 5 (the labels are cited in the docstrings).

Layout:
1. tensor-level objects of `Def:QtPt` and the operator `ϴ_{u,σ}` (`DefTHUST`, with the factor
   `S^{(B)}`);
2. the deterministic statements `QopAlgebra`, `QopNorm`, `QopDecay`;
3. matrix-level hierarchy terms (`DefKsimLK`, `def_ELKLK`, `def_EwtG`, `def:CALE`) and the drift
   identity `HierarchyN` (`LK_SDE`);
4. the statements `KcalDecay`, `DecayLoopAt` (single time), `DecayLoopWindow`, `DecayLoopFromML`;
5. the terms `ℬ₄`, `ℬ₅` (`B4`, `B5`);
6. the general-`n` grid statements `StoppedDuhamelN`, `GridDriftN`, `QVPropagatedN`;
7. the statements `STOeqTargetV2`, `PPTargetV2`, `MLExpPin`;
8. the general-`n` loop generator `llPairN`, `LoopGenN`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Tensor-level objects -/

section Tensor

variable (L : ℕ) [NeZero L]

/-- `(𝒫𝒜)_{a₁} = Σ_{a₂,…,a_k} 𝒜_a` (`Def:QtPt`); `SumZero L A ↔ ∀ a₁, Psum L A a₁ = 0`. -/
def Psum {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L) : ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), A a

/-- `ϑ_{t,a} = (1-t)^{k-1} Π_{i≥2} (Θ^{(B)}_t)_{a₁ a_i}` (`Def:QtPt`). -/
def vartheta {k : ℕ} [NeZero k] (t : ℝ) (a : Fin k → Z2 L) : ℂ :=
  ((1 - t : ℝ) : ℂ) ^ (k - 1) *
    ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (t : ℂ) (a 0) (a i)

/-- `ϑ̇_{t,a} = d/dt ϑ_{t,a}`. -/
def varthetaDot {k : ℕ} [NeZero k] (t : ℝ) (a : Fin k → Z2 L) : ℂ :=
  deriv (fun v : ℝ => vartheta L v a) t

/-- `(𝒬_t𝒜)_a = 𝒜_a - (𝒫𝒜)_{a₁} ϑ_{t,a}` (`Def:QtPt`). -/
def Qop {k : ℕ} [NeZero k] (t : ℝ) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ :=
  A a - Psum L A (a 0) * vartheta L t a

/-- `(ϴ_{u,σ}𝒜)_a = Σ_i Σ_b (ξ_i S Θ_{uξ_i})_{a_i b} 𝒜_{a^{(i)}}`, `ξ_i = m(σ_i)m(σ_{i+1})`
(`DefTHUST`, with the factor `S`; the generator of `Ugen`; at `k = 2`,
`σ = (+,-)` this is `thetaGen`). -/
def thetaSig (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (u : ℝ)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ :=
  ∑ i : Fin k, ∑ b : Z2 L,
    thetaGenMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u (a i) b *
      A (Function.update a i b)

end Tensor

/-! ## 2. Deterministic statements -/

/-- **`QopAlgebra` (`Def:QtPt`, `pqthlk`)**: `𝒫ϑ_t = 1`, `𝒫∘𝒬_t = 0`,
`𝒬_t = id` on sum-zero tensors, `𝒫ϑ̇_t = 0`, the closed form of `ϑ̇_t` (`∂_tΘ_t = Θ_tSΘ_t`),
`ϴ_{t,σ}` preserves sum-zero, and the commutator formula for `[𝒬_t, ϴ_{t,σ}]`. -/
def QopAlgebra : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ t : ℝ, 0 ≤ t → t < 1 →
    (∀ a₁ : Z2 L, Psum L (vartheta L t (k := k)) a₁ = 1) ∧
    (∀ (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L), Psum L (Qop L t A) a₁ = 0) ∧
    (∀ A : (Fin k → Z2 L) → ℂ, SumZero L A → Qop L t A = A) ∧
    (∀ a₁ : Z2 L, Psum L (varthetaDot L t (k := k)) a₁ = 0) ∧
    (∀ a : Fin k → Z2 L, varthetaDot L t a =
      -((k - 1 : ℕ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ (k - 2) *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (t : ℂ) (a 0) (a i) +
        ((1 - t : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a j) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (t : ℂ) (a 0) (a i)) ∧
    (∀ E : ℝ, |E| < 2 → ∀ (σ : Fin k → Bool) (A : (Fin k → Z2 L) → ℂ),
      SumZero L A → SumZero L (thetaSig L E σ t A)) ∧
    (∀ (E : ℝ) (σ : Fin k → Bool) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L),
      Qop L t (thetaSig L E σ t A) a - thetaSig L E σ t (Qop L t A) a =
        thetaSig L E σ t (fun b => Psum L A (b 0) * vartheta L t b) a -
          Psum L (thetaSig L E σ t A) (a 0) * vartheta L t a)

/-- **`QopNorm` (`normQA`, `lem_+Q`)**, asymptotic form with the constant
`C_k = cPrec 𝔠 k` (`RBM2D.Evolution.Defs`). -/
def QopNorm : Prop :=
  ∀ 𝔠 > (0 : ℝ), ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin k → Z2 L) → ℂ,
      HasDecay L W t τ D A →
      tmax L (Qop L t A) ≤ (W : ℝ) ^ (cPrec 𝔠 k * τ) * tmax L A + (W : ℝ) ^ (-D + cPrec 𝔠 k)

/-- **`QopDecay` (`lem_+Q` decay clause), in the corrected form**: far entries of `𝒬_t𝒜` are
`≤ W^{-D}(2 + ‖𝒜‖_max)`, eventually. -/
def QopDecay : Prop :=
  ∀ 𝔠 > (0 : ℝ), ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin k → Z2 L) → ℂ,
      HasDecay L W t τ D A →
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D) * (2 + tmax L A)) (Qop L t A)

/-! ## 3. Matrix-level hierarchy terms and the drift identity -/

section Hierarchy

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `𝓛_{u,I}(M)` as a function of the loop index. -/
def LLf (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  gloop L W (blockMat M) (spectralZ E u) I

/-- `(𝓛 - 𝒦)_{u,I}(M)`. -/
def LKf (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  LLf L W E u M I - KLoop.Kcal L W E u I

/-- `[𝒦 ∼ (𝓛-𝒦)]^{l}_{u,I}` (`DefKsimLK`): the cut pairs with `𝒦` of length `l`, both
orders. -/
def ksimLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : ℕ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Z2 L, ∑ b : Z2 L,
      ((if (I.cutGlueR k l' b).length = l then
          LKf L W E u M (I.cutGlueL k l' a) * SB L a b * KLoop.Kcal L W E u (I.cutGlueR k l' b)
        else 0) +
       (if (I.cutGlueL k l' a).length = l then
          KLoop.Kcal L W E u (I.cutGlueL k l' a) * SB L a b * LKf L W E u M (I.cutGlueR k l' b)
        else 0))

/-- `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}_{u,I}` (`def_ELKLK`), general length. -/
def elklkN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Z2 L, ∑ b : Z2 L,
      LKf L W E u M (I.cutGlueL k l' a) * SB L a b * LKf L W E u M (I.cutGlueR k l' b)

/-- `𝓔^{(G̃)}_{u,I}` (`def_EwtG`), general length (at length 2 this is `EGt`). -/
def egtN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    avgErr L W E u M (I.σ.getD (k - 1) false) a * SB L a b * LLf L W E u M (I.cutGlue k b)

/-- The `(2n+2)`-loop of (`def_diffakn_k`), cut at edge `k`:
`a^{(k)} = (a_k..a_n, a_1..a_{k-1}, b', a'_{k-1}..a'_1, a'_n..a'_k, b)`,
`σ^{(k)} = (σ_k..σ_n, σ_1..σ_k, σ̄_k..σ̄_1, σ̄_n..σ̄_k)`. -/
def eeLoop (σ : List Bool) (a a' : List (Z2 L)) (k : ℕ) (b b' : Z2 L) : LoopIdx (Z2 L) :=
  ⟨σ.drop (k - 1) ++ σ.take k ++ ((σ.take k).reverse.map not) ++
      ((σ.drop (k - 1)).reverse.map not),
    a.drop (k - 1) ++ a.take (k - 1) ++ [b'] ++ (a'.take (k - 1)).reverse ++
      (a'.drop (k - 1)).reverse ++ [b]⟩

/-- `(𝓔⊗𝓔)_{u,σ,a,a'}` (`def:CALE`), general length. -/
def eeN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {n : ℕ} (σ : Fin n → Bool)
    (a a' : Fin n → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 n, ∑ b : Z2 L, ∑ b' : Z2 L,
    SB L b b' * LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

/-- The `(𝓛-𝒦)` tensor of a fixed sign vector. -/
def lkTensor (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Z2 L) → ℂ :=
  fun b => LKf L W E u M (loopOf σ b)

end Hierarchy

/-- **`HierarchyN` (`LK_SDE`, drift part)**: for Hermitian `M`,
`genMat(𝓛_{σ,a}) - ∂_u𝒦_{σ,a} = (ϴ_{u,σ}(𝓛-𝒦))_a + Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}`.
At `k = 2` this is `HierarchyN2` (`RBM2D.Path.DriftAlgebra`). -/
def HierarchyN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
    ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      genMat E u M (loopOf σ a) - deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u =
        thetaSig L E σ u (lkTensor L W E u M σ) a +
          ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a) +
          elklkN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a)

/-! ## 4. Decay statements -/

section R24

variable (d : Sizes)

/-- **`KcalDecay` (fast decay of `𝒦`, used by `lem_decayLoop` and `lem_BcalE`; source `eq:bcal_k`
with the tree representation)**: deterministic, eventually in `N`. -/
def KcalDecay (κ : ℝ) : Prop :=
  0 < κ → ∀ 𝔠 > (0 : ℝ), ∀ k : ℕ, 1 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ellT L u * (W : ℝ) ^ τ ≤ (KLoop.maxDist L a : ℝ) →
        ‖KLoop.Kcal L W E u (loopOf σ a)‖ ≤ (W : ℝ) ^ (-D)

/-- **`DecayLoopAt` (`lem_decayLoop`, `res_decayLK`), single time**: inputs at
the one time sequence `u` only: the local law (`InitLocal d E u`) and the `(+,-)` decay with a
polynomial prefactor `P`; conclusion the section form of `DecayLoopPT`. -/
def DecayLoopAt (κ c τ C₀ : ℝ) (E u P : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → 0 ≤ C₀ → (∀ n, 0 ≤ u n) → (∀ n, u n < 1) →
  SizeTendsto d → Bandwidth d c → RangeCond d τ u → KcalDecay κ →
  RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
  (∀ n, 1 ≤ P n) → (∀ᶠ n : ℕ in atTop, P n ≤ ((d.size n : ℕ) : ℝ) ^ C₀) →
  InitLocal d E u →
  (∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
    (fun n p _ => P n * (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (u n))) +
      (d.W n : ℝ) ^ (-D))) →
  ∀ k : ℕ, 1 ≤ k → ∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω =>
      (loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2 +
        lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2) *
      (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ) then 1 else 0))
    (fun n _ _ => (d.W n : ℝ) ^ (-D'))

/-- **`DecayLoopWindow` (window corollary of `DecayLoopAt`)**: `DecayLoopPT d E s t` from the
Step 2 outputs on `[s,t]` (sections, `perTimeDomAt_iff_forall_section`; prefactor
`P = (η_s/η_u)^4`). -/
def DecayLoopWindow (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  MainIndHyp d κ c τ E s t → KcalDecay κ → RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
    Step2LocalPT d E s t → Step2DecayPT d E s t → DecayLoopPT d E s t

/-- **`DecayLoopFromML` (`[0,t]` corollary of `DecayLoopAt`)**: from `MLConcl` at every section
`0 ≤ u ≤ t` (`chainTarget`), `DecayLoopPT d E 0 t`. -/
def DecayLoopFromML (κ c τ : ℝ) (E t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) →
  SizeTendsto d → Bandwidth d c → RangeCond d τ t → KcalDecay κ →
  RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
  (∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → MLConcl d E u) →
  DecayLoopPT d E (fun _ => 0) t

/-- The per-time index set `u ∈ [s,t]`, `σ ∈ {±}^k`, `a`. -/
abbrev IdxT (s t : ℕ → ℝ) (k : ℕ) (n : ℕ) : Type :=
  TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n))

/-- The far-label indicator `1(ℓ_u W^{τ'} ≤ max|a_i - a_j|)`. -/
def farInd (n : ℕ) (u τ' : ℝ) {k : ℕ} (a : Fin k → Z2 (d.L n)) : ℝ :=
  if ellT (d.L n) u * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) then 1 else 0

end R24

/-! ## 5. The terms `ℬ₄`, `ℬ₅` -/

section R25

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `ℬ₅ = (𝒫(𝓛-𝒦)_{u,σ})_{a₁} ϑ̇_{u,a}`. -/
def B5 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (a : Fin k → Z2 L) : ℂ :=
  Psum L (lkTensor L W E u M σ) (a 0) * varthetaDot L u a

/-- `ℬ₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)_{u,σ}`. -/
def B4 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (a : Fin k → Z2 L) : ℂ :=
  Qop L u (thetaSig L E σ u (lkTensor L W E u M σ)) a -
    thetaSig L E σ u (Qop L u (lkTensor L W E u M σ)) a

end R25

/-- The alternating sign vectors (cyclic; empty for odd `k`). -/
def Alternating {k : ℕ} [NeZero k] (σ : Fin k → Bool) : Prop := ∀ i : Fin k, σ (i + 1) = !σ i

/-! ## 6. The general-`n` grid statements -/

section R26

variable (d : Sizes)

/-- `A_j = (𝓛 - 𝒦)_{u_j,σ}` along the walk, a `k`-tensor (general-`n` `Avec`). -/
def AvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => gloop (d.L n) (d.W n) (blockMat (pathH d s t K n j ω))
      (spectralZ (E n) (gridTime s t K n j)) (loopOf σ a) -
    KLoop.Kcal (d.L n) (d.W n) (E n) (gridTime s t K n j) (loopOf σ a)

/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]`. -/
def martIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => AvecN d E s t K n (j + 1) σ ω a -
    (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' a | filt d j] ω

/-- `P_j = 𝔼[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A_j`. -/
def predIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' a | filt d j] ω -
    Ugen (d.L n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (AvecN d E s t K n j σ ω) a

/-- **`StoppedDuhamelN` (`int_K-L_ST`, general `n`, all `σ`)**: the stopped grid Duhamel
identity, pathwise.  At `k = 2`, `σ = (+,-)` it is `StoppedDuhamel105`. -/
def StoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) [NeZero k] (σ : Fin k → Bool) (τ : PathΩ d → ℕ) (j : ℕ) (ω : PathΩ d),
      min j (τ ω) ≤ K n →
      AvecN d E s t K n (min j (τ ω)) σ ω =
        Ugen (d.L n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
            (AvecN d E s t K n 0 σ ω) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Ugen (d.L n) (E n) σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
              (predIncN d E s t K n i σ ω + martIncN d E s t K n i σ ω)

/-- The `d = 2` remainder of one step of `𝒦` (`W → W²`, `L → L²` relative to `d = 1`). -/
def kStepC (L W k : ℕ) (Bk : ℝ) : ℝ :=
  2 * (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * Bk *
      ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * Bk ^ 2) +
    (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * Bk ^ 2) ^ 2

/-- The remainder factor of one step of `𝒰` (dimension-free). -/
def uStepC (k : ℕ) (Δ v : ℝ) : ℝ :=
  (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 + ((1 + Δ * (1 - v)⁻¹) ^ k - 1 - (k : ℝ) * Δ * (1 - v)⁻¹)

/-- The explicit one-step error: `envConst Δ^{3/2}` (`condExp_loop_drift`) plus the
`𝒦` and `𝒰` second-order remainders, with `‖A_j‖_max ≤ η_{u_j}^{-k} W^{-2(k-1)} + B_k`. -/
def stepErrN (L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ Bk : ℝ) : ℝ :=
  envConst L W E k v * Δ ^ ((3 : ℝ) / 2) + kStepC L W k Bk * Δ ^ 2 +
    uStepC k Δ v * ((etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk)

/-- **`GridDriftN` (one grid step of `LK_SDE`, general `n`, all `σ`)**: a.e., the predictable
part is `Δ` times the non-linear drift `Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}` at `u_j`, up
to the deterministic `stepErrN`, given a deterministic envelope `B_k` of `𝒦` on `[0,u_{j+1}]`. -/
def GridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n j : ℕ), j < K n → ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Z2 (d.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖KLoop.Kcal (d.L n) (d.W n) (E n) w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(pathP d), ∀ a : Fin k → Z2 (d.L n),
      ‖predIncN d E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (gridTime s t K n j)
              (pathH d s t K n j ω) l (loopOf σ a) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) (loopOf σ a) +
            egtN (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) (loopOf σ a))‖
        ≤ stepErrN (d.L n) (d.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) Bk

end R26

/-- The derivative of `𝓛_{u,σ,b}(M)` along a direction `X`. -/
def loopDerivN (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 L) : ℂ :=
  deriv (fun y : ℝ => gloop L W (blockMat (M + (y : ℂ) • X)) (spectralZ E u) (loopOf σ b)) 0

/-- **`QVPropagatedN` (variance proxy, general `n`)**: `QVPropagated` (factor
`2 = n`) for loops of length `k ≥ 2`, factor `k` (Cauchy–Schwarz over the `k` cuts, per-cut
identity of `def:CALE`). -/
def QVPropagatedN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ (k : ℕ), 2 ≤ k →
    ∀ (σ : Fin k → Bool) (κ : (Fin k → Z2 L) → ℂ),
      ∑ c : Coord L W, (gvar L W c : ℝ) *
          ‖∑ b : Fin k → Z2 L, κ b * loopDerivN L W E u M (coordinateMatrix L W c) σ b‖ ^ 2 ≤
        (k : ℝ) * (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
          κ b * (starRingEnd ℂ) (κ b') * eeN L W E u M σ b b').re

/-! ## 7. The statements of Steps 3--5 and of `ML:exp` -/

section Consumers

variable (d : Sizes)

/-- **`STOeqTargetV2` (`lem:STOeq_NQ` + `lem:STOeq_Qt`)**, against `UpstreamSteps34Prec`
(`RBM2D.Evolution.Case3Defs`).  Used by `Step3Target`, `Step4TargetV3` (hypothesis
`∀ k ≥ 2, STOeqPT`). -/
def STOeqTargetV2 (κ c τ : ℝ) (C : ℕ → ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t →
    Step2LocalPT d E s t → Step2DecayPT d E s t →
    ∀ k : ℕ, 2 ≤ k → STOeqPT d E s t k

/-- **`PPTargetV2` (the `(+,+)` base case of Step 3)**.  Used by `Step3Target`, `Step4TargetV3`
(hypothesis `PPTwoLoopPT`). -/
def PPTargetV2 (κ c τ : ℝ) (C : ℕ → ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t →
    Step1LoopPT d E s t → Step1WeakLawPT d E s t →
    Step2LocalPT d E s t → Step2DecayPT d E s t → PPTwoLoopPT d E s t

/-- **`MLExpPin` (`ML:exp`)**, in terms of `Step61Concl`, `MLExpConcl`, `DecayLoopPT`,
`SumDecayDetPrec`.  `DecayLoopFromML` feeds it. -/
def MLExpPin (κ c τ : ℝ) (C : ℕ → ℝ) (E t : ℕ → ℝ) : Prop :=
  0 < κ → 0 < c → 0 < τ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) →
    SizeTendsto d → Bandwidth d c → RangeCond d τ t → KboundConcl κ → SumDecayDetPrec κ c τ C →
    Step4PT d E (fun _ => 0) t → DecayLoopPT d E (fun _ => 0) t →
    (∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → Step61Concl d E u) →
    MLExpConcl d E t

end Consumers


/-! ## 8. The general-`n` loop generator -/

/-- `W² Σ_{k<l} Σ_{a,b} 𝓛(𝒢^{(a),L}_{k,l}) S_{ab} 𝓛(𝒢^{(b),R}_{k,l})`, the pair-cut term of
(`eq:mainStoflow`), general length (at length 2 this is `LLpair`). -/
def llPairN (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Z2 L, ∑ b : Z2 L,
      LLf L W E u M (I.cutGlueL k l' a) * SB L a b * LLf L W E u M (I.cutGlueR k l' b)

/-- **`LoopGenN` (`eq:mainStoflow`, drift part, general `n`)**: for Hermitian `M`,
`genMat(𝓛_{σ,a}) = W² Σ 𝓛 S 𝓛 + 𝓔^{(G̃)}`.  At `k = 2` this is `LoopGenN2`
(`RBM2D.Path.DriftAlgebra`).  Used by `HierarchyN`. -/
def LoopGenN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
    ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      genMat E u M (loopOf σ a) = llPairN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a)

end RBM.Ind

end
