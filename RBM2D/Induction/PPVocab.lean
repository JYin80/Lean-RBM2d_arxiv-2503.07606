/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AzumaProxyN
import RBM2D.Induction.GridEnvelopeN
import RBM2D.Induction.GridAssemblyN
import RBM2D.Induction.GridGoodEvent
import RBM2D.Induction.LoopC2N
import RBM2D.Induction.DecayLoop
import RBM2D.Induction.KcalDecay
import RBM2D.Induction.QVN
import RBM2D.Induction.Step3
import RBM2D.Green.GbEXP
import RBM2D.Evolution.MLExpVocab

/-!
# The `(+,+)` two-loop base case: vocabulary, statements and the assembly

Namespace `RBM.Ind`, `variable (d : Sizes)`.  Paper: arXiv:2503.07606, Section 5: the base case
of Step 3 (the `(+,+)` two-loop bound, which the paper's argument for `σ = (+,-)` does not
cover), the stopped loop hierarchy (`int_K-L_ST`) and its martingale term (`alu9_STime`).  The
argument parallels the one-dimensional formalization (the discrete Bihari lemma, the good set, the
exit time).

Layout: 1. vocabulary; 2. the statements (`GridGoodPPN`, `PPKernelN`, `PPDriftN`, `PPCondVarN`,
`PPDriftSumN`, `PPQVSumN`, `PPArithN`); 3. `measurableGoodSetPPN`; 4-7. helpers;
8. `ppN_grid_bound`; 9. the assembly `ppTargetV2_of_pins` and `ppTargetV2_of_ppPins` (with the
inputs `azumaSubGN`, `yMomentsUnifN` of `RBM2D.Induction.AzumaProxyN` discharged).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. Vocabulary: the `(+,+)` quantity, its good set, its exit time, the constants -/

section Vocab

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `σ = (+,+)`. -/
def sigPPN : Fin 2 → Bool := ![true, true]

/-- `J_u(M) = M_u² max_{a,b} |(𝓛-𝒦)_{u,(+,+),(a,b)}(M)|`, the quantity of `PPTwoLoopPT`
(`RBM2D.Induction.Defs`). -/
def jPPN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
      (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]) *
    scaleM L W E u ^ 2

/-- **`GoodSetPPN`**: the `(+,+)` good set at the spectral time `u`, with the loss `Γ`
(`= N^ε`), the (2.73) levels `Φ₃ = R^4`, `Φ₆ = R^10` (`R = ℓ_v/ℓ_s`, `Ξ^{(𝓛)}_{u,m} ≺
(ℓ_u/ℓ_s)^{2(m-1)}` in `d = 2`) and the decay exponents `τ' D'`.  The clauses: Hermitian,
(G1) `Ξ^{(𝓛-𝒦)}_{u,1} ≤ Γ`, (G2) `Ξ^{(𝓛)}_{u,3} ≤ ΓΦ₃` and (G3) `Ξ^{(𝓛)}_{u,6} ≤ ΓΦ₆`, (G4)+(G5) the
decay of `𝓛` and `𝓛-𝒦` at every length `≤ 6`, as the one clause of `GoodSetN`. -/
def GoodSetPPN (E u : ℝ) (Γ Φ₃ Φ₆ τ' D' : ℝ) : Set (Matrix (Idx L W) (Idx L W) ℂ) :=
  {M | M.IsHermitian ∧
    xiLK L W E u M 1 ≤ Γ ∧
    xiL L W E u M 3 ≤ Γ * Φ₃ ∧
    xiL L W E u M 6 ≤ Γ * Φ₆ ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) →
        loopAbs L W E u M σ a + lkGen L W E u M σ a ≤ (W : ℝ) ^ (-D'))}

/-- `N = (W L)²` as a real number. -/
def nPPN : ℝ := (((W * L) ^ 2 : ℕ) : ℝ)

/-- **The `(+,+)` drift majorant** (recounted for `d = 2`: near windows `(2 ℓ_u W^{τ'} + 1)² ≤ 9 ℓ_u² W^{2τ'}`, `W² ℓ_u² = M_u/η_u`): with
`J = J_u(M)`, `Γ`, `Φ₃` the levels of `GoodSetPPN`,
`|𝓔^{LK×LK} + 𝓔^{(G̃)}| ≤ C (W^{2τ'} J² M^{-3} η^{-1} + W^{2τ'} Γ² Φ₃ M^{-2} η^{-1}
+ N² W^{-D'} (J + Γ))`. -/
def dBoundPPN (E u Γ Φ₃ τ' D' J : ℝ) : ℝ :=
  1000 * ((W : ℝ) ^ (2 * τ') * J ^ 2 * (scaleM L W E u)⁻¹ ^ 3 * (etaT E u)⁻¹
    + (W : ℝ) ^ (2 * τ') * Γ ^ 2 * Φ₃ * (scaleM L W E u)⁻¹ ^ 2 * (etaT E u)⁻¹
    + nPPN L W ^ 2 * (W : ℝ) ^ (-D') * (J + Γ))

/-- **The `(+,+)` conditional-variance majorant** (recounted for `d = 2`): `|𝓔⊗𝓔| ≤ C (W^{2τ'} ΓΦ₆ M^{-4} η^{-1} + N² W^{-D'})` on `GoodSetPPN`. -/
def eeBdPPN (E v Γ Φ₆ τ' D' : ℝ) : ℝ :=
  1000 * ((W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E v)⁻¹ ^ 4 * (etaT E v)⁻¹
    + nPPN L W ^ 2 * (W : ℝ) ^ (-D'))

/-- The sub-Gaussian proxy of the propagated first-chaos increment of step `j`:
`Δ CU⁴ ee_bd + K⁻¹ N^{-10}` (the last term makes `Σ_j c_j > 0`). -/
def cQPPN (E v Γ Φ₆ τ' D' Δ CU : ℝ) (K : ℕ) : ℝ :=
  Δ * (CU ^ 4 * eeBdPPN L W E v Γ Φ₆ τ' D') + (K : ℝ)⁻¹ * nPPN L W ^ (-(10 : ℝ))

end Vocab

/-- The row-sum constant of one `(+,+)` slot kernel, `1 + A0 (1 + log L)` (property 5 gives the
factor `1 + log L`). -/
def CUN (A0 : ℝ) (L : ℕ) : ℝ := 1 + A0 * (1 + Real.log (L : ℝ))

/-- `Lg = (Im m(E))⁻¹ log N + 1`. -/
def LgPPN (E N : ℝ) : ℝ := (spectralM E).im⁻¹ * Real.log N + 1

/-- `C₀ = 10⁴ (CU² + 1)` (generous constants). -/
def C0PPN (CU : ℝ) : ℝ := 10000 * (CU ^ 2 + 1)

/-- **The Bihari constant** `c' = C₀ Γ³ (1 + R⁴ + R⁵) Lg` (the powers of `R` double relative to `d = 1`, `lRB1`). -/
def cPrimePPN (CU Γ R Lg : ℝ) : ℝ := C0PPN CU * Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg

/-- The quadratic coefficient of the Bihari step, `C_q = 2000 CU² W^{2ε}`. -/
def CqPPN (CU W ε : ℝ) : ℝ := 2000 * CU ^ 2 * W ^ (2 * ε)

section GridVocab

variable (d : Sizes)

/-- `R = ℓ_v/ℓ_s` at the size index `n`. -/
def RPPN (s v : ℕ → ℝ) (n : ℕ) : ℝ := ellT (d.L n) (v n) / ellT (d.L n) (s n)

/-- The `(+,+)` good set at the grid index `j`, levels `Γ = N^ε`, `Φ₃ = R⁴`, `Φ₆ = R^{10}`. -/
def goodSetGridPPN (E s v : ℕ → ℝ) (K : ℕ → ℕ) (ε τ' D' : ℝ) (n j : ℕ) :
    Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  GoodSetPPN (d.L n) (d.W n) (E n) (gridTime s v K n j) (((d.size n : ℕ) : ℝ) ^ ε)
    (RPPN d s v n ^ 4) (RPPN d s v n ^ 10) τ' D'

/-- **The `(+,+)` exit time**: the exit time of the grid walk from `GoodSetPPN`, through the
generic `gridExitTauN`. -/
def ppExitTauN (E s v : ℕ → ℝ) (K : ℕ → ℕ) (ε τ' D' : ℝ) (n : ℕ) : PathΩ d → ℕ :=
  gridExitTauN d s v K n (goodSetGridPPN d E s v K ε τ' D' n)

/-- The good event of the `(+,+)` grid: the walk stays in `GoodSetPPN` at every grid time and the
initial value satisfies `J_s(H_0) ≤ N^ε`. -/
def goodEventPPN (E s v : ℕ → ℝ) (K : ℕ → ℕ) (ε τ' D' : ℝ) (n : ℕ) : Set (PathΩ d) :=
  {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ goodSetGridPPN d E s v K ε τ' D' n j} ∩
    {ω | jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) ≤
      ((d.size n : ℕ) : ℝ) ^ ε}

end GridVocab

/-! ## 2. The statements -/

section Pins

variable (d : Sizes)

/-- **`MeasurableGoodSetPPN`**: `GoodSetPPN` is a measurable set of matrices (proved below,
`measurableGoodSetPPN`). -/
def MeasurableGoodSetPPN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u Γ Φ₃ Φ₆ τ' D' : ℝ),
    MeasurableSet (GoodSetPPN L W E u Γ Φ₃ Φ₆ τ' D')

/-- **`GridGoodPPN`** (the `d = 2` pattern is `gridGoodN`): with high
probability the grid walk on `[s,v] ⊆ [s,t]` stays in `GoodSetPPN` at every grid time and
`J_s(H_0) ≤ N^ε`.  The premises are those of the inputs: `MainIndHyp` (`InitLK`, `RangeCond`,
`Bandwidth`), `KboundConcl`, `GbEXPHypV3` (`GavLDetSeq`, `Ξ₁ ≺ 1`), `Step1LoopPT` ((2.73) at length
3 and 6), `Step2LocalPT`, `Step2DecayPT`, `DecayLoopPT`.  `Step1WeakLawPT` is not used. -/
def GridGoodPPN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  MainIndHyp d κ c τ E s t → KboundConcl κ → RBM.Green.GbEXPHypV3 d (κ / 2) c τ →
  Step1LoopPT d E s t → Step2LocalPT d E s t → Step2DecayPT d E s t → DecayLoopPT d E s t →
  (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → (∀ n, K n ≠ 0) →
  ∀ C : ℝ, (∀ᶠ n : ℕ in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ C) →
  ∀ ε > (0 : ℝ), ∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ),
    HighProbAt (pathP d) d.size (fun n => goodEventPPN d E s v K ε τ' D' n)


/-- **`PPKernelN`** (the `(+,+)` kernel through property 5 at `ξ = v m²`, and `gapK`): every row of the
`(+,+)` slot kernel `𝒰 = (1 - v m² S) Θ_{w m²}` has `ℓ¹` norm `≤ 1 + A0 (1 + log L)`, uniformly in
`L ≥ 3`, `0 ≤ v ≤ w < 1` and the bulk energy `|E| ≤ 2 - κ`.  The constant `A0 = A0(κ)` comes from
`norm_Theta_apply_le_prop5` (`RBM2D.Propagator.Prop5`) with `κ_ξ² = ‖1 - w m²‖ ≥ gapK κ`,
`ℓ̂ ≤ (gapK κ)^{-1/2}`, summed over `Z_L²` (`1 - v ξ S = (1 - w ξ S) + (w - v) ξ S`, so the row sum is
`≤ 1 + rowsum Θ_{wξ}`); the quantifier order is `∃ A0` before `L`.  The truth of the true constant
(`O(1)`, no `log L`) is not claimed: the `1 + log L` is the loss of property 5. -/
def PPKernelN (κ : ℝ) : Prop :=
  0 < κ → ∃ A0 : ℝ, 0 < A0 ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ v w : ℝ, 0 ≤ v → v ≤ w → w < 1 → ∀ x : Z2 L,
      ∑ y : Z2 L, ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w x y‖ ≤ CUN A0 L

/-- **`PPDriftN`**: on `GoodSetPPN` the non-linear drift
`𝓔^{LK×LK} + 𝓔^{(G̃)}` of the `(+,+)` loop (`Σ_{l≥3}` is empty at `k = 2`) is bounded by `dBoundPPN`
in terms of `J`, deterministically. -/
def PPDriftN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    1 ≤ scaleM L W E u → ∀ Γ Φ₃ Φ₆ τ' D' : ℝ, 1 ≤ Γ → 0 ≤ Φ₃ → 0 ≤ Φ₆ → 0 < τ' → 0 < D' →
    ∀ M ∈ GoodSetPPN L W E u Γ Φ₃ Φ₆ τ' D', ∀ a : Fin 2 → Z2 L,
      ‖elklkN L W E u M (loopOf sigPPN a) + egtN L W E u M (loopOf sigPPN a)‖ ≤
        dBoundPPN L W E u Γ Φ₃ τ' D' (jPPN L W E u M)

/-- **`PPCondVarN`** (with the time shift `u₁ → u₂ = u₁ + Δ`): the conditional-variance form
`Δ · 2 · qvFormN` of the propagated first-chaos increment (`qvPropagatedN`) is bounded on
`GoodSetPPN` at the time `u₁` by `Δ CU⁴ ee_bd`, `CU` a row-sum bound of the propagator weights.  The
shift `u₁ → u₂` costs `Δ ≤ N^{-40}` (`η_{u₂}⁻¹ ≤ N` from `1 ≤ M_{u₂}`).  The additive shift
`δ' = 6 N⁹ Δ` of a six-loop needs the tail hypothesis `Δ ≤ N^{-(40 + D' + 2τ')}` to be absorbed by
`N² W^{-D'}`. -/
def PPCondVarN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (E u₁ u₂ w Δ : ℝ), |E| < 2 → 0 ≤ u₁ → u₁ ≤ u₂ →
    u₂ ≤ w → w < 1 → u₂ = u₁ + Δ → Δ ≤ nPPN L W ^ (-(40 : ℝ)) → 1 ≤ scaleM L W E u₂ →
    ∀ Γ Φ₃ Φ₆ τ' D' CU : ℝ, 1 ≤ Γ → 0 ≤ Φ₃ → 0 ≤ Φ₆ → 0 < τ' → 0 < D' →
    Δ ≤ nPPN L W ^ (-(40 + D' + 2 * τ')) →
    (∀ x : Z2 L, ∑ y : Z2 L,
      ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) u₂ w x y‖ ≤ CU) →
    ∀ M ∈ GoodSetPPN L W E u₁ Γ Φ₃ Φ₆ τ' D', M.IsHermitian → ∀ a : Fin 2 → Z2 L,
      Δ * (2 * qvFormN L W E u₂ w sigPPN M a) ≤ Δ * (CU ^ 4 * eeBdPPN L W E u₂ Γ Φ₆ τ' D')

/-- **`PPDriftSumN`**: the
drift sum of the pathwise bound, along the grid `[s,v]`, `K ≥ N^{C_K}`, `C_K ≥ 80`, in terms of any
`J ≥ 0` and any `m ≥ J_j` (`j < k`): `M_k² Δ Σ_{j<k} CU² d_j ≤ c'/4 + C_q m² Lg/M_v`
(`decay radius exponent = ε`, `D' = 6/c`).  Deterministic; uses `sum_gridStep_div_etaT_le`,
`Bandwidth`, `RangeCond`. -/
def PPDriftSumN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  MainIndHyp d κ c τ E s t → (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → (∀ n, K n ≠ 0) →
  ∀ ε > (0 : ℝ), ∀ C_K : ℝ, 80 ≤ C_K →
  (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) → ∀ A0 : ℝ, 0 < A0 →
  ∀ᶠ n : ℕ in atTop, ∀ J : ℕ → ℝ, (∀ j, 0 ≤ J j) → ∀ k ≤ K n, ∀ m : ℝ, 0 ≤ m →
    (∀ j < k, J j ≤ m) →
    scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) ^ 2 *
        (gridStep s v K n * ∑ j ∈ Finset.range k, CUN A0 (d.L n) ^ 2 *
          dBoundPPN (d.L n) (d.W n) (E n) (gridTime s v K n j) (((d.size n : ℕ) : ℝ) ^ ε)
            (RPPN d s v n ^ 4) ε (6 / c) (J j)) ≤
      cPrimePPN (CUN A0 (d.L n)) (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n)
          (LgPPN (E n) ((d.size n : ℕ) : ℝ)) / 4 +
        CqPPN (CUN A0 (d.L n)) (d.W n : ℝ) ε * m ^ 2 * LgPPN (E n) ((d.size n : ℕ) : ℝ) /
          scaleM (d.L n) (d.W n) (E n) (v n)

/-- **`PPQVSumN`**: the Azuma term of the pathwise bound, `M_k² N^ε (Σ_{j<k} c_j)^{1/2} ≤ c'/4` (`c_j = cQPPN` at
`u_{j+1}`, levels `Γ = N^ε`, `Φ₆ = R^{10}`).  Deterministic. -/
def PPQVSumN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  MainIndHyp d κ c τ E s t → (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → (∀ n, K n ≠ 0) →
  ∀ ε > (0 : ℝ), ∀ C_K : ℝ, 80 ≤ C_K →
  (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) → ∀ A0 : ℝ, 0 < A0 →
  ∀ᶠ n : ℕ in atTop, ∀ k ≤ K n,
    scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) ^ 2 *
        (((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range k,
          (Real.toNNReal (cQPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1))
            (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n ^ 10) ε (6 / c) (gridStep s v K n)
            (CUN A0 (d.L n)) (K n)) : ℝ))) ≤
      cPrimePPN (CUN A0 (d.L n)) (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n)
          (LgPPN (E n) ((d.size n : ℕ) : ℝ)) / 4

/-- **`PPArithN`**: the three deterministic eventual inequalities on
the scales along a section `v ∈ [s,t]`: (i) `1 ≤ M_v`; (ii) the forbidden zone
`4 C_q c' Lg ≤ M_v` for `ε ≤ min(2c, τ)/8`; (iii) the output `2 c' ≤ N^{τ'} M_s^{1/2}` for
`8 ε ≤ τ'`. -/
def PPArithN (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  MainIndHyp d κ c τ E s t → ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
  ∀ A0 : ℝ, 0 < A0 →
    (∀ᶠ n : ℕ in atTop, 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n)) ∧
    (∀ ε > (0 : ℝ), ε ≤ min (2 * c) τ / 8 → ∀ᶠ n : ℕ in atTop,
      4 * CqPPN (CUN A0 (d.L n)) (d.W n : ℝ) ε * cPrimePPN (CUN A0 (d.L n))
          (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n) (LgPPN (E n) ((d.size n : ℕ) : ℝ)) *
          LgPPN (E n) ((d.size n : ℕ) : ℝ) ≤ scaleM (d.L n) (d.W n) (E n) (v n)) ∧
    (∀ ε > (0 : ℝ), ∀ τ' : ℝ, 8 * ε ≤ τ' → ∀ᶠ n : ℕ in atTop,
      2 * cPrimePPN (CUN A0 (d.L n)) (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n)
          (LgPPN (E n) ((d.size n : ℕ) : ℝ)) ≤
        ((d.size n : ℕ) : ℝ) ^ τ' * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2))
/-! ## 3. `MeasurableGoodSetPPN` -/

section MeasurableProof

private theorem PPN_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

private theorem PPN_measurableSet_imp {α : Type*} [MeasurableSpace α] {p : Prop}
    {q : α → Prop} (h : p → MeasurableSet {x | q x}) : MeasurableSet {x | p → q x} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem PPN_meas_loopAbs (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => loopAbs L W E u M σ a :=
  (GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ a)).norm

private theorem PPN_meas_lkGen (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => lkGen L W E u M σ a :=
  ((GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ a)).sub_const _).norm

private theorem PPN_meas_xiL (E u : ℝ) (k : ℕ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => xiL L W E u M k := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        loopAbs L W E u M p.1 p.2)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => PPN_meas_loopAbs L W E u p.1 p.2
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => xiL L W E u M k) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          loopAbs L W E u M p.1 p.2)) M * scaleM L W E u ^ (k - 1) := by
    funext M
    simp only [xiL, Finset.sup'_apply]
  rw [heq]
  exact hsup.mul_const _

private theorem PPN_meas_xiLK (E u : ℝ) (k : ℕ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => xiLK L W E u M k := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        lkGen L W E u M p.1 p.2)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => PPN_meas_lkGen L W E u p.1 p.2
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => xiLK L W E u M k) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          lkGen L W E u M p.1 p.2)) M * scaleM L W E u ^ k := by
    funext M
    simp only [xiLK, Finset.sup'_apply]
  rw [heq]
  exact hsup.mul_const _

/-- `jPPN` is a measurable function of the matrix. -/
theorem measurable_jPPN (E u : ℝ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => jPPN L W E u M := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        lkGen L W E u M ![true, true] ![p.1, p.2])) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ =>
      PPN_meas_lkGen L W E u ![true, true] ![p.1, p.2]
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => jPPN L W E u M) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : Z2 L × Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          lkGen L W E u M ![true, true] ![p.1, p.2])) M * scaleM L W E u ^ 2 := by
    funext M
    simp only [jPPN, Finset.sup'_apply]
  rw [heq]
  exact hsup.mul_const _

end MeasurableProof

/-- **`MeasurableGoodSetPPN` proved** (no hypothesis): `GoodSetPPN` is a finite intersection of level
sets of measurable functions of `M` and the closed set `M.IsHermitian` (template:
`measurableGoodSetN`). -/
theorem measurableGoodSetPPN : MeasurableGoodSetPPN := by
  intro L W _ _ E u Γ Φ₃ Φ₆ τ' D'
  have hH : MeasurableSet {M : Matrix (Idx L W) (Idx L W) ℂ | M.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  unfold GoodSetPPN
  simp only [Set.ofPred_and]
  refine hH.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · exact measurableSet_le (PPN_meas_xiLK L W E u 1) measurable_const
  · exact measurableSet_le (PPN_meas_xiL L W E u 3) measurable_const
  · exact measurableSet_le (PPN_meas_xiL L W E u 6) measurable_const
  · exact PPN_measurableSet_forall fun j => PPN_measurableSet_imp fun _ =>
      PPN_measurableSet_imp fun _ => PPN_measurableSet_forall fun σ =>
        PPN_measurableSet_forall fun a => PPN_measurableSet_imp fun _ =>
          measurableSet_le ((PPN_meas_loopAbs L W E u σ a).add (PPN_meas_lkGen L W E u σ a))
            measurable_const

/-- Measurability of `{j < ppExitTauN}` (`gridExitTauN_measurableSet`). -/
theorem ppExitTauN_measurableSet (E s v : ℕ → ℝ) (K : ℕ → ℕ) (ε τ' D' : ℝ) (n j : ℕ) :
    MeasurableSet[filt d j] {ω | j < ppExitTauN d E s v K ε τ' D' n ω} :=
  gridExitTauN_measurableSet (fun j => measurableGoodSetPPN _ _ _ _ _ _ _ _ _) j


/-! ## 4. Compiled helpers of the assembly -/

section Helpers

variable {L W : ℕ} [NeZero L] [NeZero W]

theorem sigPPN_apply (i : Fin 2) : sigPPN i = true := by
  fin_cases i <;> rfl

theorem jPPN_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : 0 ≤ jPPN L W E u M := by
  unfold jPPN
  obtain ⟨p0⟩ := (inferInstance : Nonempty (Z2 L × Z2 L))
  exact mul_nonneg ((norm_nonneg _).trans (Finset.le_sup' (fun p : Z2 L × Z2 L =>
    lkGen L W E u M ![true, true] ![p.1, p.2]) (Finset.mem_univ p0))) (sq_nonneg _)

/-- One `(+,+)` propagator step: the row sums of the slot kernel bound `𝒰_{v,w,(+,+)}` in `ℓ^∞`. -/
theorem ppKer_ugen_le {E v w CU M : ℝ} (hCU : 0 ≤ CU)
    (hrow : ∀ x : Z2 L, ∑ y : Z2 L,
      ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w x y‖ ≤ CU)
    (hM : 0 ≤ M) (X : (Fin 2 → Z2 L) → ℂ) (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin 2 → Z2 L) :
    ‖Ugen L E sigPPN v w X a‖ ≤ CU ^ 2 * M := by
  unfold Ugen
  have hsig : ∀ i : Fin 2, KLoop.mSig E (sigPPN i) * KLoop.mSig E (sigPPN (i + 1)) =
      KLoop.mSig E true * KLoop.mSig E true := fun i => by
    rw [sigPPN_apply i, sigPPN_apply (i + 1)]
  simp only [hsig]
  calc ‖∑ b : Fin 2 → Z2 L, (∏ i : Fin 2,
        ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) (b i)) * X b‖
      ≤ ∑ b : Fin 2 → Z2 L, ‖(∏ i : Fin 2,
        ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) (b i)) * X b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : Fin 2 → Z2 L, (∏ i : Fin 2,
        ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) (b i)‖) * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hX b) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (∏ i : Fin 2, ∑ y : Z2 L,
        ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) y‖) * M := by
        rw [← Finset.sum_mul, Fintype.prod_sum]
    _ ≤ CU ^ 2 * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        calc (∏ i : Fin 2, ∑ y : Z2 L,
              ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) y‖)
            ≤ ∏ _i : Fin 2, CU :=
              Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
                fun i _ => hrow (a i)
          _ = CU ^ 2 := by simp [Finset.prod_const, Finset.card_univ]

/-- The step error of `gridDriftN` is nonnegative. -/
theorem stepErrN_nonneg' {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2) (hu1 : u < 1) (hv1 : v < 1)
    (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) : 0 ≤ stepErrN L W E k u v Δ Bk := by
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hv : 0 < 1 - v := by linarith
  have h1 : 0 ≤ envConst L W E k v * Δ ^ ((3 : ℝ) / 2) := by
    unfold envConst
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hΔ _)
  have h2 : 0 ≤ kStepC L W k Bk * Δ ^ 2 := by
    unfold kStepC; positivity
  have h3 : 0 ≤ uStepC k Δ v := by
    unfold uStepC
    have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
    have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
      have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
      simpa using this
    have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
    nlinarith
  have h4 : 0 ≤ (etaT E u)⁻¹ ^ k * ((W : ℝ)⁻¹ ^ 2) ^ (k - 1) + Bk := by
    have : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  unfold stepErrN
  have := mul_nonneg h3 h4
  linarith

end Helpers


/-! ## 5. The `(+,+)` data of the assembled bound, the discrete Bihari lemma and the real closure -/

section Data

variable (d : Sizes) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `Dr_j(a) = 𝓔^{LK×LK}_{u_j,(+,+),a}(H_j) + 𝓔^{(G̃)}_{u_j,(+,+),a}(H_j)` (the drift of `(𝓛-𝒦)_{(+,+)}`;
`Σ_{l ≥ 3}` is empty at `k = 2`). -/
def ppDr (j : ℕ) (ω : PathΩ d) : (Fin 2 → Z2 (d.L n)) → ℂ := fun a =>
  elklkN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) (loopOf sigPPN a) +
    egtN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) (loopOf sigPPN a)

/-- The remainder `R_j = P_j - Δ Dr_j` of one grid step. -/
def ppR (j : ℕ) (ω : PathΩ d) : (Fin 2 → Z2 (d.L n)) → ℂ := fun a =>
  predIncN d E s v K n j sigPPN ω a - (gridStep s v K n : ℂ) * ppDr d E s v K n j ω a

/-- The stopped, propagated process `A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} (Δ Dr_j + Z_j + Y_j + R_j)`. -/
def ppA (τ : PathΩ d → ℕ) (m : ℕ) (ω : PathΩ d) : (Fin 2 → Z2 (d.L n)) → ℂ :=
  Ugen (d.L n) (E n) sigPPN (gridTime s v K n 0) (gridTime s v K n m)
      (AvecN d E s v K n 0 sigPPN ω) +
    ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) (E n) sigPPN (gridTime s v K n (j + 1))
      (gridTime s v K n m) ((gridStep s v K n : ℂ) • ppDr d E s v K n j ω +
        ZvecN d E s v K n j sigPPN ω + YvecN d E s v K n j sigPPN ω + ppR d E s v K n j ω)

/-- The pathwise drift majorant `d_j(ω) = dBoundPPN(u_j, J_j(ω))`. -/
def ppDDrift (ε τ' D' : ℝ) (j : ℕ) (ω : PathΩ d) : ℝ :=
  dBoundPPN (d.L n) (d.W n) (E n) (gridTime s v K n j) (((d.size n : ℕ) : ℝ) ^ ε)
    (RPPN d s v n ^ 4) τ' D'
    (jPPN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω))

/-- The deterministic step error `stepErrN` with `B_k = N^{τ_K} η_{u_{j+1}}^{-2}`. -/
def ppStepErr (τK : ℝ) (j : ℕ) : ℝ :=
  stepErrN (d.L n) (d.W n) (E n) 2 (gridTime s v K n j) (gridTime s v K n (j + 1))
    (gridStep s v K n) (((d.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ 2)

/-- The sub-Gaussian proxy of step `j` (independent of the target `m` and the label). -/
def ppC (ε τ' D' A0 : ℝ) (j : ℕ) : ℝ≥0 :=
  Real.toNNReal (cQPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1))
    (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n ^ 10) τ' D' (gridStep s v K n)
    (CUN A0 (d.L n)) (K n))

end Data

/-- **The discrete Bihari lemma**: if `4 C c' L_N ≤ A` and, for every `k ≤ K` and every `m ≥ 0`
dominating all previous values,
`f_k ≤ c' + C m² L_N / A`, then `f_k ≤ 2c'` for every `k ≤ K`. -/
theorem discrete_bihariN {K : ℕ} {f : ℕ → ℝ} {c' C LN A : ℝ} (hC : 0 ≤ C) (hLN : 0 ≤ LN)
    (hA : 0 < A) (hc' : 0 ≤ c') (hzone : 4 * C * c' * LN ≤ A) (_h0 : f 0 ≤ c')
    (hstep : ∀ k ≤ K, ∀ m : ℝ, 0 ≤ m → (∀ j < k, f j ≤ m) → f k ≤ c' + C * m ^ 2 * LN / A) :
    ∀ k ≤ K, f k ≤ 2 * c' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hprev : ∀ j < k, f j ≤ 2 * c' := fun j hj => ih j hj (by omega)
    have h1 := hstep k hk (2 * c') (by linarith) hprev
    have h2 : C * (2 * c') ^ 2 * LN / A ≤ c' := by
      rw [div_le_iff₀ hA]
      have : C * (2 * c') ^ 2 * LN = c' * (4 * C * c' * LN) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hzone hc'
    linarith

/-- **The real closure** of the `(+,+)` induction (the constant bookkeeping): from the pathwise bound
`J_k ≤ M_k² (CU² S₀ + D_k + Q_k + P + E_k)` and the four sum bounds (drift `c'/4 + C_q m² Lg/M_v`,
Azuma `c'/4`, `P`, `E ≤ 1`) and the forbidden zone, `J_k ≤ 2c'` for every `k ≤ K`. -/
theorem ppN_closure_real {K : ℕ} {J M Dsum Qsum Esum : ℕ → ℝ} {S0 Pn Γ CU2 Cq Lg Av cP : ℝ}
    (hM0 : ∀ k ≤ K, 0 ≤ M k) (hS0 : 0 ≤ S0) (hinit : M 0 ^ 2 * S0 ≤ Γ)
    (hMmono : ∀ k ≤ K, M k ≤ M 0) (hCU2 : 0 ≤ CU2) (hCq : 0 ≤ Cq) (hLg : 0 ≤ Lg)
    (hAv : 0 < Av) (hcP : CU2 * Γ + 2 ≤ cP / 2) (hzone : 4 * Cq * cP * Lg ≤ Av)
    (hbd : ∀ k ≤ K, J k ≤ M k ^ 2 * (CU2 * S0 + Dsum k + Qsum k + Pn + Esum k))
    (hD : ∀ k ≤ K, ∀ m : ℝ, 0 ≤ m → (∀ j < k, J j ≤ m) →
      M k ^ 2 * Dsum k ≤ cP / 4 + Cq * m ^ 2 * Lg / Av)
    (hQ : ∀ k ≤ K, M k ^ 2 * Qsum k ≤ cP / 4) (hP : ∀ k ≤ K, M k ^ 2 * Pn ≤ 1)
    (hE : ∀ k ≤ K, M k ^ 2 * Esum k ≤ 1) :
    ∀ k ≤ K, J k ≤ 2 * cP := by
  have hcP0 : 0 ≤ cP := by
    have : 0 ≤ CU2 * Γ + 2 := by
      have hΓ : 0 ≤ Γ := by
        have := mul_nonneg (sq_nonneg (M 0)) hS0
        nlinarith [sq_nonneg (M 0)]
      positivity
    linarith
  have hstep : ∀ k ≤ K, ∀ m : ℝ, 0 ≤ m → (∀ j < k, J j ≤ m) → J k ≤ cP + Cq * m ^ 2 * Lg / Av := by
    intro k hk m hm hJm
    have h1 := hbd k hk
    have h2 : M k ^ 2 * S0 ≤ Γ := by
      have : M k ^ 2 ≤ M 0 ^ 2 := pow_le_pow_left₀ (hM0 k hk) (hMmono k hk) 2
      exact (mul_le_mul_of_nonneg_right this hS0).trans hinit
    have h3 := hD k hk m hm hJm
    have h4 := hQ k hk
    have h5 := hP k hk
    have h6 := hE k hk
    have h7 : M k ^ 2 * (CU2 * S0 + Dsum k + Qsum k + Pn + Esum k) =
        CU2 * (M k ^ 2 * S0) + M k ^ 2 * Dsum k + M k ^ 2 * Qsum k + M k ^ 2 * Pn +
          M k ^ 2 * Esum k := by ring
    have h8 : CU2 * (M k ^ 2 * S0) ≤ CU2 * Γ := mul_le_mul_of_nonneg_left h2 hCU2
    linarith
  have h0 : J 0 ≤ cP := by
    have := hstep 0 (Nat.zero_le _) 0 le_rfl (fun j hj => absurd hj (Nat.not_lt_zero _))
    simpa using this
  exact discrete_bihariN hCq hLg hAv hcP0 hzone h0 hstep


/-! ## 6. Nonnegativity and the bundle of the assembled bound -/

section NonNeg

variable {L W : ℕ} [NeZero L] [NeZero W]

theorem nPPN_pos : 0 < nPPN L W := by
  unfold nPPN
  exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))

theorem dBoundPPN_nonneg {E u Γ Φ₃ τ' D' J : ℝ} (hE : |E| < 2) (hu1 : u < 1) (hJ : 0 ≤ J)
    (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ₃) : 0 ≤ dBoundPPN L W E u Γ Φ₃ τ' D' J := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hM : 0 < scaleM L W E u := scaleM_pos (by have := NeZero.pos L; omega)
    (by have := NeZero.pos W; omega) hE hu1
  have hW : (0 : ℝ) < W := by exact_mod_cast NeZero.pos W
  have hN := nPPN_pos (L := L) (W := W)
  unfold dBoundPPN
  positivity

theorem eeBdPPN_nonneg {E v Γ Φ₆ τ' D' : ℝ} (hE : |E| < 2) (hv1 : v < 1) (hΓ : 0 ≤ Γ)
    (hΦ : 0 ≤ Φ₆) : 0 ≤ eeBdPPN L W E v Γ Φ₆ τ' D' := by
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hM : 0 < scaleM L W E v := scaleM_pos (by have := NeZero.pos L; omega)
    (by have := NeZero.pos W; omega) hE hv1
  have hW : (0 : ℝ) < W := by exact_mod_cast NeZero.pos W
  have hN := nPPN_pos (L := L) (W := W)
  unfold eeBdPPN
  positivity

theorem cQPPN_pos {E v Γ Φ₆ τ' D' Δ CU : ℝ} {K : ℕ} (hE : |E| < 2) (hv1 : v < 1) (hΓ : 0 ≤ Γ)
    (hΦ : 0 ≤ Φ₆) (hΔ : 0 ≤ Δ) (hK : K ≠ 0) :
    0 < cQPPN L W E v Γ Φ₆ τ' D' Δ CU K := by
  have h1 := eeBdPPN_nonneg (L := L) (W := W) (τ' := τ') (D' := D') hE hv1 hΓ hΦ
  have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hN := nPPN_pos (L := L) (W := W)
  unfold cQPPN
  have : 0 ≤ Δ * (CU ^ 4 * eeBdPPN L W E v Γ Φ₆ τ' D') := by positivity
  have : 0 < (K : ℝ)⁻¹ * nPPN L W ^ (-(10 : ℝ)) :=
    mul_pos (inv_pos.2 hK') (Real.rpow_pos_of_pos hN _)
  linarith

end NonNeg

section Bundle

variable {d : Sizes} {E s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- **The bundle `GridAssemblyHypN` of the `(+,+)` walk** (`k = 2`, `σ = (+,+)`): every field of
the `AssembledN` bundle is discharged from definitional data
(`ppA`), the kernel row sums (`PPKernelN`), the drift majorant (`PPDriftN`), the moments
(`YMomentsUnifN`) and the a.e. remainder bound of `gridDriftN_envelope`. -/
theorem ppN_bundle {ε τ' D' A0 τK P : ℝ} (τ : PathΩ d → ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK0 : K n ≠ 0)
    (hA0 : 0 < A0)
    (hrow : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 → ∀ x : Z2 (d.L n), ∑ y : Z2 (d.L n),
      ‖ukerMat (d.L n) (KLoop.mSig (E n) true * KLoop.mSig (E n) true) a b x y‖ ≤
        CUN A0 (d.L n))
    (hdrift : ∀ ω j, j < K n → j < τ ω → ∀ b,
      ‖ppDr d E s v K n j ω b‖ ≤ ppDDrift d E s v K n ε τ' D' j ω)
    (hdrift0 : ∀ ω j, j < K n → 0 ≤ ppDDrift d E s v K n ε τ' D' j ω)
    (hcpos : ∀ m, 1 ≤ m → m ≤ K n →
      0 < ∑ j ∈ Finset.range m, (ppC d E s v K n ε τ' D' A0 j : ℝ))
    (hYn : YMomentBoundsN d (E n) sigPPN (gridTime s v K n) τ (K n)
      (fun j ω => YvecN d E s v K n j sigPPN ω) (fun _ => gridStep s v K n ^ 2 * P)
      (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hP0 : 0 ≤ P)
    (herr : ∀ j < K n, 0 ≤ ppStepErr d E s v K n τK j)
    (henv : ∀ᵐ ω ∂(pathP d), ∀ j, j < K n → ∀ a : Fin 2 → Z2 (d.L n),
      ‖predIncN d E s v K n j sigPPN ω a - (gridStep s v K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 2, ksimLK (d.L n) (d.W n) (E n) (gridTime s v K n j)
              (pathH d s v K n j ω) l (loopOf sigPPN a) +
            elklkN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω)
              (loopOf sigPPN a) +
            egtN (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω)
              (loopOf sigPPN a))‖ ≤ ppStepErr d E s v K n τK j) :
    GridAssemblyHypN d (n := n) (k := 2) (E n) sigPPN (gridTime s v K n) τ (gridStep s v K n)
      (K n) (fun _ _ _ => True) (fun ω => AvecN d E s v K n 0 sigPPN ω)
      (fun m ω => ppA d E s v K n τ m ω) (fun j ω => ppDr d E s v K n j ω)
      (fun j ω => ZvecN d E s v K n j sigPPN ω) (fun j ω => YvecN d E s v K n j sigPPN ω)
      (fun j ω => ppR d E s v K n j ω) (fun _ _ => CUN A0 (d.L n) ^ 2) (fun _ _ => 0) 0
      (fun j ω => ppDDrift d E s v K n ε τ' D' j ω) (fun _ _ => 0)
      (fun _ _ j => ppC d E s v K n ε τ' D' A0 j)
      (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2)
      (ppStepErr d E s v K n τK) where
  hE := hE.le.trans (by norm_num)
  hu0 := fun i _ => GoodEvent_gridTime_nonneg hs0 hsv i
  hu1 := fun i hi => (GoodEvent_gridTime_le (K := K) hsv hi).trans_lt hv1
  hΔ0 := GoodEvent_gridStep_nonneg hsv
  hexp := fun m _ => Eventually.of_forall fun ω => rfl
  hκ0 := fun _ _ _ _ => by
    have : 0 ≤ CUN A0 (d.L n) := by
      unfold CUN
      have := Real.log_natCast_nonneg (d.L n)
      have : 0 ≤ A0 * (1 + Real.log (d.L n : ℝ)) := by positivity
      linarith
    positivity
  hε0 := fun _ _ _ _ => le_rfl
  hker := fun i m him hmK X M δ hM hδ hX _ a => by
    have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ => GoodEvent_gridTime_nonneg hs0 hsv i
    have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
      (GoodEvent_gridTime_le (K := K) hsv hi).trans_lt hv1
    have hCU : 0 ≤ CUN A0 (d.L n) := by
      unfold CUN
      have := Real.log_natCast_nonneg (d.L n)
      have : 0 ≤ A0 * (1 + Real.log (d.L n : ℝ)) := by positivity
      linarith
    have := ppKer_ugen_le hCU (hrow (gridTime s v K n i) (gridTime s v K n m) (hu0 i (him.trans hmK))
      (GoodEvent_gridTime_mono hsv him) (hu1 m hmK)) hM X hX a
    simpa using this
  hδ0 := le_rfl
  hA0cls := fun _ _ => trivial
  hdDrift0 := hdrift0
  hδD0 := fun _ _ _ => le_rfl
  hdrift := hdrift
  hDcls := fun _ _ _ _ => trivial
  hc_pos := fun m hm hmK _ => hcpos m hm hmK
  hv0 := fun _ _ => by positivity
  hw0 := fun _ _ => by positivity
  hY := hYn
  hstepErr0 := herr
  hR := by
    filter_upwards [henv] with ω hω j hj _ b
    have h := hω j hj b
    have hIcc : Finset.Icc 3 2 = (∅ : Finset ℕ) := by decide
    rw [hIcc, Finset.sum_empty, zero_add] at h
    simpa [ppR, ppDr] using h

end Bundle


/-! ## 7. Small facts used by the assembly -/

section Facts

theorem rangeCond_mono_v {d : Sizes} {τ : ℝ} {v t : ℕ → ℝ} (h : RangeCond d τ t)
    (hvt : ∀ n, v n ≤ t n) : RangeCond d τ v := by
  filter_upwards [h] with n hn
  linarith [hvt n]

theorem rangeCond_min_one {d : Sizes} {τ : ℝ} {v : ℕ → ℝ} (h : RangeCond d τ v) :
    RangeCond d (min τ 1) v := by
  filter_upwards [h] with n hn
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (GoodEvent_one_le_size n) ?_) hn
  linarith [min_le_left τ 1]

theorem cPrimePPN_ge {CU Γ R Lg : ℝ} (hΓ : 1 ≤ Γ) (hR : 0 ≤ R) (hLg : 1 ≤ Lg) :
    CU ^ 2 * Γ + 2 ≤ cPrimePPN CU Γ R Lg / 2 := by
  unfold cPrimePPN C0PPN
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hR5 : 0 ≤ R ^ 5 := by positivity
  have h1 : 1 ≤ 1 + R ^ 4 + R ^ 5 := by linarith
  have hΓ3 : Γ ≤ Γ ^ 3 := by nlinarith [sq_nonneg Γ, sq_nonneg (Γ - 1)]
  have hP : Γ ≤ Γ ^ 3 * (1 + R ^ 4 + R ^ 5) := by nlinarith
  have hP2 : Γ ≤ Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg := by nlinarith
  have hcu : 0 ≤ CU ^ 2 := sq_nonneg _
  have : 10000 * (CU ^ 2 + 1) * Γ ≤ 10000 * (CU ^ 2 + 1) * (Γ ^ 3 * (1 + R ^ 4 + R ^ 5) * Lg) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  nlinarith

theorem LgPPN_ge_one {E N : ℝ} (hE : |E| < 2) (hN : 1 ≤ N) : 1 ≤ LgPPN E N := by
  unfold LgPPN
  have := mul_nonneg (inv_nonneg.2 (spectralM_im_pos hE).le) (Real.log_nonneg hN)
  linarith

theorem CUN_nonneg {A0 : ℝ} (hA0 : 0 < A0) (L : ℕ) : 0 ≤ CUN A0 L := by
  unfold CUN
  have := Real.log_natCast_nonneg L
  have : 0 ≤ A0 * (1 + Real.log (L : ℝ)) := by positivity
  linarith

/-- For a label `b` of the two-index tensor, the entry of `𝓛-𝒦` is dominated by `jPPN / M²`. -/
theorem lkGen_le_supPPN {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin 2 → Z2 L) :
    lkGen L W E u M sigPPN b ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]) := by
  have hb : b = ![b 0, b 1] := by
    funext i; fin_cases i <;> rfl
  have := Finset.le_sup' (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2])
    (Finset.mem_univ (b 0, b 1))
  calc lkGen L W E u M sigPPN b = lkGen L W E u M ![true, true] ![b 0, b 1] := by
        rw [← hb]; rfl
    _ ≤ _ := this

end Facts


/-! ## 8. The grid endpoint of the `(+,+)` induction (composition of the statements above) -/

section Main

variable {d : Sizes}

/-- **The grid endpoint** (at the last grid point): for a section `v ∈ [s,t]` and `0 < ε ≤ min(2c,τ)/8`, eventually in
`n`, on an event of probability at least `1 - N^{-D}`, `J_v(H_K) ≤ 2 c'`.  The composition: the statements
`GridGoodPPN` (good event), `PPKernelN` (`hrow`), `PPDriftN`, `PPCondVarN`, the moments
`YMomentsUnifN` and the proxies `AzumaSubGN`, `assembledN`, `gridDriftN_envelope`
and `sum_weighted_stepErrN_le`, `stoppedDuhamelN`, and the closure `ppN_closure_real`
with the sum statements `PPDriftSumN`, `PPQVSumN` and the zone statement `PPArithN`. -/
theorem ppN_grid_bound {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hmain : MainIndHyp d κ c τ E s t) (hK : KboundConcl κ)
    (hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (h1 : Step1LoopPT d E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t) (hdl : DecayLoopPT d E s t)
    (hGood : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), GridGoodPPN d κ c τ E s v t K)
    (hDr : PPDriftN) (hQV : PPCondVarN)
    (hDS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPDriftSumN d κ c τ E s v t K)
    (hQS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPQVSumN d κ c τ E s v t K)
    (hArith : PPArithN d κ c τ E s t)
    (hAz : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), AzumaSubGN d s v K)
    (hY : ∀ v : ℕ → ℝ, YMomentsUnifN d κ τ E s v)
    {A0 : ℝ} (hA0 : 0 < A0)
    (hrow : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      b < 1 → ∀ x : Z2 L, ∑ y : Z2 L,
        ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) a b x y‖ ≤ CUN A0 L)
    (v : ℕ → ℝ) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ min (2 * c) τ / 8) {D : ℝ} (hD : 0 < D) :
    ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ d),
      (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D) ∧ ∀ ω ∈ G,
        jPPN (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) ≤
          2 * cPrimePPN (CUN A0 (d.L n)) (((d.size n : ℕ) : ℝ) ^ ε) (RPPN d s v n)
            (LgPPN (E n) ((d.size n : ℕ) : ℝ)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, hilk, hidec, hiloc⟩ := hmain'
  have hvlt : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hE2 : ∀ n, |E n| < 2 := fun n => lt_of_le_of_lt (hE n) (by linarith)
  have hrangev : RangeCond d τ v := rangeCond_mono_v hrange hvt
  have hτ1 : 0 < min τ 1 := lt_min hτ one_pos
  have hrange1 : RangeCond d (min τ 1) v := rangeCond_min_one hrangev
  obtain ⟨C_P, hCP0, hYev⟩ := hY v hκ hE hs0 hsv hvlt hsize hrangev 2 sigPPN
  have hc6 : 0 < 6 / c := by positivity
  set C_K : ℝ := D + 224 + 2 * C_P + 6 / c with hCKdef
  have hCK200 : 200 ≤ C_K := by linarith
  set K : ℕ → ℕ := gridK d 0 (C_K - 80) with hKdef
  have hCKeq : CK 0 (C_K - 80) = C_K := by unfold CK; ring
  have hK0 : ∀ n, K n ≠ 0 := fun n => gridK_ne_zero _ _ n
  refine ⟨K, hK0, ?_⟩
  have hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ) :=
    Eventually.of_forall fun n => by
      have := rpow_CK_le_gridK (d := d) 0 (C_K - 80) n
      rwa [hCKeq] at this
  have hcard : ∀ᶠ n : ℕ in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (C_K + 2) := by
    have := gridK_card_le (d := d) (D := 0) (D₁ := C_K - 80) (by rw [hCKeq]; linarith)
    rwa [hCKeq] at this
  have hgood := hGood v K hmain hK hV h1 hloc hdec hdl hsv hvt hK0 (C_K + 2) hcard ε hε ε hε
    (6 / c) hc6 (D + 2) (by linarith)
  have hasm := assembledN d hsize 2 ε hε 3 (D + 2) C_P C_K (by linarith) (by push_cast; linarith)
  have hsw := sum_weighted_stepErrN_le d (κ := κ) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := 3) (E := E) (s := s) (t := v) (K := K) 2 hκ hτ1 (min_le_right _ _) one_pos
    (by norm_num) le_rfl hsize hE hs0 hsv hvlt hK0 hrange1
    (by push_cast; nlinarith [min_le_right τ 1]) (by push_cast; nlinarith [min_le_right τ 1])
    (by push_cast; nlinarith [min_le_right τ 1]) (by linarith) hKN
  have henv := gridDriftN_envelope (d := d) κ hκ 2 le_rfl 1 one_pos hsize hE hs0 hsv hvlt hK0
    sigPPN
  obtain ⟨hM1, hzone', hout'⟩ := hArith hmain v hsv hvt A0 hA0
  have hzone := hzone' ε hε hεc
  have hds := hDS v K hmain hsv hvt hK0 ε hε C_K (by linarith) hKN A0 hA0
  have hqs := hQS v K hmain hsv hvt hK0 ε hε C_K (by linarith) hKN A0 hA0
  have hYn := hYev K hK0
  filter_upwards [hgood, hasm, hsw, henv, hM1, hzone, hds, hqs, hYn,
    hsize.eventually_ge_atTop 2] with n hgn han hswn henvn hM1n hzonen hdsn hqsn hYnn hN2
  obtain ⟨P, hP0, hPle, hYP⟩ := hYnn
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hL1 : 1 ≤ d.L n := by omega
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hΓ1 : 1 ≤ N ^ ε := Real.one_le_rpow hN1 hε.le
  have hR0 : 0 ≤ RPPN d s v n ^ 4 := by
    unfold RPPN
    have h1 : 0 < ellT (d.L n) (v n) := (ellT_pos_le hL1 (hvlt n)).1
    have h2 : 0 < ellT (d.L n) (s n) := (ellT_pos_le hL1 ((hsv n).trans_lt (hvlt n))).1
    positivity
  have hR10 : 0 ≤ RPPN d s v n ^ 10 := by
    unfold RPPN
    have h1 : 0 < ellT (d.L n) (v n) := (ellT_pos_le hL1 (hvlt n)).1
    have h2 : 0 < ellT (d.L n) (s n) := (ellT_pos_le hL1 ((hsv n).trans_lt (hvlt n))).1
    positivity
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => GoodEvent_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) (hsv n) hi).trans_lt (hvlt n)
  have huv : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi =>
    GoodEvent_gridTime_le (K := K) (hsv n) hi
  have hmono : ∀ i j, i ≤ j → gridTime s v K n i ≤ gridTime s v K n j := fun i j h =>
    GoodEvent_gridTime_mono (hsv n) h
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hM1j : ∀ j ≤ K n, 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) := fun j hj =>
    hM1n.trans (scaleM_anti_ratio (W := d.W n) hL1 (hE2 n) (huv j hj) (hvlt n)).1
  have hΓ0 : 0 ≤ N ^ ε := Real.rpow_nonneg hN0.le _
  have hCU0 := CUN_nonneg hA0 (d.L n)
  set τf := ppExitTauN d E s v K ε ε (6 / c) n with hτf
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τf ω} := fun j =>
    ppExitTauN_measurableSet d E s v K ε ε (6 / c) n j
  have hΔK : gridStep s v K n ≤ N ^ (-C_K) := by
    have := step_gridK_le (d := d) (s := s) (v := v) (D := 0) (D₁ := C_K - 80) (n := n)
      (by linarith [hvlt n, hs0 n])
    rwa [hCKeq] at this
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := by
    unfold gridStep
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (hK0 n))]
    linarith [hvlt n, hs0 n]
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
  have hKle : K n ≤ ⌈N ^ C_K⌉₊ := by
    change gridK d 0 (C_K - 80) n ≤ _
    unfold gridK
    rw [hCKeq]
    exact max_le (Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hN0 _)) le_rfl
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin 2 → Z2 (d.L n)) (j : ℕ), j < m →
      SubGaussStopN d (E n) sigPPN (gridTime s v K n) τf
        (fun j ω => ZvecN d E s v K n j sigPPN ω) m a j
        (ppC d E s v K n ε ε (6 / c) A0 j) := by
    intro m hm a j hj
    have hjK : j + 1 ≤ K n := by omega
    refine azumaSubG_ugen (hAz v K) (hermTestFunLoopN d) hE2 hs0 hsv hvlt n 2 le_rfl sigPPN τf
      (fun j => goodSetGridPPN d E s v K ε ε (6 / c) n j) hτmeas
      (fun ω j hj => mem_of_lt_gridExitTauN hj) m hm a j hj _ ?_
    intro M hM hMH
    have hΔx : ∀ x : ℝ, x ≤ C_K → gridStep s v K n ≤ nPPN (d.L n) (d.W n) ^ (-x) :=
      fun x hx => hΔK.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hx]))
    have hΔ40 : gridStep s v K n ≤ nPPN (d.L n) (d.W n) ^ (-(40 : ℝ)) :=
      hΔx 40 (by linarith only [hCK200])
    -- `τ ≤ 1` (`RangeCond` at a size `≥ 2`), so `2 ε ≤ τ / 4 ≤ 1`: the room of the tail exponent
    have hε2 : 2 * ε ≤ 1 := by
      have hτle1 : τ ≤ 1 := by
        by_contra hτ1'
        push Not at hτ1'
        obtain ⟨n', hn2, hnr⟩ := (hsize.eventually_ge_atTop 2 |>.and hrange).exists
        have ht0 : 0 ≤ t n' := (hs0 n').trans (hst n')
        have h1 : (1 : ℝ) < ((d.size n' : ℕ) : ℝ) ^ (-1 + τ) :=
          Real.one_lt_rpow (by linarith only [hn2]) (by linarith only [hτ1'])
        linarith only [h1, hnr, ht0]
      have := min_le_right (2 * c) τ
      linarith only [this, hεc, hτle1]
    have hΔtail : gridStep s v K n ≤ nPPN (d.L n) (d.W n) ^ (-(40 + 6 / c + 2 * ε)) :=
      hΔx _ (by linarith only [hCKdef, hD, hCP0, hε2])
    have hq := hQV (d.L n) (d.W n) hL3 (E n) (gridTime s v K n j) (gridTime s v K n (j + 1))
      (gridTime s v K n m) (gridStep s v K n) (hE2 n) (hu0 j) (hmono j (j + 1) (Nat.le_succ j))
      (hmono (j + 1) m hj) (hu1 m hm) (by unfold gridTime; push_cast; ring) hΔ40
      (hM1j (j + 1) hjK) (N ^ ε) (RPPN d s v n ^ 4) (RPPN d s v n ^ 10) ε (6 / c)
      (CUN A0 (d.L n)) hΓ1 hR0 hR10 hε hc6 hΔtail
      (fun x => hrow (d.L n) hL3 (E n) (hE n) (gridTime s v K n (j + 1)) (gridTime s v K n m)
        (hu0 _) (hmono (j + 1) m hj) (hu1 m hm) x) M hM hMH a
    have hpos : 0 ≤ gridStep s v K n * (CUN A0 (d.L n) ^ 4 *
        eeBdPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) (N ^ ε) (RPPN d s v n ^ 10) ε
          (6 / c)) :=
      mul_nonneg hΔ0 (mul_nonneg (by positivity) (eeBdPPN_nonneg (hE2 n) (hu1 _ hjK) hΓ0 hR10))
    have hle : gridStep s v K n * (CUN A0 (d.L n) ^ 4 *
        eeBdPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) (N ^ ε) (RPPN d s v n ^ 10) ε
          (6 / c)) ≤ cQPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) (N ^ ε)
            (RPPN d s v n ^ 10) ε (6 / c) (gridStep s v K n) (CUN A0 (d.L n)) (K n) := by
      unfold cQPPN
      have : 0 < (K n : ℝ)⁻¹ * nPPN (d.L n) (d.W n) ^ (-(10 : ℝ)) :=
        mul_pos (inv_pos.2 (by exact_mod_cast hK1)) (Real.rpow_pos_of_pos nPPN_pos _)
      linarith
    calc gridStep s v K n * (((2 : ℕ) : ℝ) * qvFormN (d.L n) (d.W n) (E n)
          (gridTime s v K n (j + 1)) (gridTime s v K n m) sigPPN M a)
        ≤ _ := by simpa using hq
      _ ≤ _ := hle
      _ ≤ _ := Real.le_coe_toNNReal _
  have hcpos : ∀ m, 1 ≤ m → m ≤ K n →
      0 < ∑ j ∈ Finset.range m, (ppC d E s v K n ε ε (6 / c) A0 j : ℝ) := by
    intro m hm hmK
    refine Finset.sum_pos (fun j hj => ?_) ⟨0, Finset.mem_range.2 (by omega)⟩
    have hj' : j < K n := (Finset.mem_range.1 hj).trans_le hmK
    have := cQPPN_pos (L := d.L n) (W := d.W n) (E := E n) (v := gridTime s v K n (j + 1))
      (Γ := N ^ ε) (Φ₆ := RPPN d s v n ^ 10) (τ' := ε) (D' := 6 / c) (Δ := gridStep s v K n)
      (CU := CUN A0 (d.L n)) (K := K n) (hE2 n) (hu1 (j + 1) hj') hΓ0 hR10 hΔ0 (hK0 n)
    unfold ppC
    rw [Real.coe_toNNReal _ this.le]
    exact this
  have hdrift0 : ∀ ω j, j < K n → 0 ≤ ppDDrift d E s v K n ε ε (6 / c) j ω := fun ω j hj =>
    dBoundPPN_nonneg (hE2 n) (hu1 j hj.le) (jPPN_nonneg _ _ _) hΓ0 hR0
  have hdrift : ∀ ω j, j < K n → j < τf ω → ∀ b,
      ‖ppDr d E s v K n j ω b‖ ≤ ppDDrift d E s v K n ε ε (6 / c) j ω := by
    intro ω j hj hjτ b
    have hmem : pathH d s v K n j ω ∈ goodSetGridPPN d E s v K ε ε (6 / c) n j :=
      mem_of_lt_gridExitTauN hjτ
    exact hDr (d.L n) (d.W n) hL3 (E n) (gridTime s v K n j) (hE2 n) (hu0 j) (hu1 j hj.le)
      (hM1j j hj.le) (N ^ ε) (RPPN d s v n ^ 4) (RPPN d s v n ^ 10) ε (6 / c) hΓ1 hR0 hR10 hε
      hc6 _ hmem b
  have herr : ∀ j < K n, 0 ≤ ppStepErr d E s v K n 1 j := fun j hj =>
    stepErrN_nonneg' (hE2 n) (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0 (by positivity)
  have hbundle := ppN_bundle (ε := ε) (τ' := ε) (D' := 6 / c) (A0 := A0) (τK := 1) (P := P) τf
    (hE2 n) (hs0 n) (hsv n) (hvlt n) (hK0 n) hA0
    (fun a b h0 hab hb1 x => hrow (d.L n) hL3 (E n) (hE n) a b h0 hab hb1 x) hdrift hdrift0
    hcpos (hYP τf hτmeas) hP0 herr henvn
  obtain ⟨Ga, hGa, hbd⟩ := han (K n) (E n) sigPPN (gridTime s v K n) τf (gridStep s v K n)
    (fun _ _ _ => True) (fun ω => AvecN d E s v K n 0 sigPPN ω)
    (fun m ω => ppA d E s v K n τf m ω) (fun j ω => ppDr d E s v K n j ω)
    (fun j ω => ZvecN d E s v K n j sigPPN ω) (fun j ω => YvecN d E s v K n j sigPPN ω)
    (fun j ω => ppR d E s v K n j ω) (fun _ _ => CUN A0 (d.L n) ^ 2) (fun _ _ => 0) 0
    (fun j ω => ppDDrift d E s v K n ε ε (6 / c) j ω) (fun _ _ => 0)
    (fun _ _ j => ppC d E s v K n ε ε (6 / c) A0 j)
    (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2)
    (ppStepErr d E s v K n 1) P hK1 hKle hΔK hKΔ hP0 hPle (fun j _ => le_rfl) (fun j _ => le_rfl)
    hτmeas (fun j => stronglyMeasurable_ZvecN d E s v K n j sigPPN) hsubG hbundle
  refine ⟨Ga ∩ goodEventPPN d E s v K ε ε (6 / c) n, ?_, ?_⟩
  · have hGg : (pathP d) (goodEventPPN d E s v K ε ε (6 / c) n)ᶜ ≤
        ENNReal.ofReal (N ^ (-(D + 2))) := hgn
    have h2 : (pathP d).real (goodEventPPN d E s v K ε ε (6 / c) n)ᶜ ≤ N ^ (-(D + 2)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hGg
    have hsum : (pathP d).real (Ga ∩ goodEventPPN d E s v K ε ε (6 / c) n)ᶜ ≤
        N ^ (-(D + 2)) + N ^ (-(D + 2)) := by
      rw [Set.compl_inter]
      exact (measureReal_union_le _ _).trans (add_le_add hGa h2)
    have hpow : N ^ (-(D + 2)) * 2 ≤ N ^ (-D) := by
      have e : N ^ (-(D + 2)) = N ^ (-D) * N ^ (-(2 : ℝ)) := by
        rw [show -(D + 2) = -D + (-(2 : ℝ)) by ring, Real.rpow_add hN0]
      have h4 : N ^ (-(2 : ℝ)) ≤ 1 / 2 := by
        rw [Real.rpow_neg hN0.le, Real.rpow_two, inv_le_comm₀ (by positivity) (by norm_num)]
        nlinarith
      rw [e]
      have : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
      nlinarith
    linarith
  · rintro ω ⟨hωa, hωg, hωinit⟩
    have hτω : τf ω = K n := gridExitTauN_eq_of_forall_mem hωg
    have hτ0 : 0 < τf ω := by rw [hτω]; exact hK1
    have hb := hbd ω hωa hτ0
    have hA : ∀ m ≤ K n, ppA d E s v K n τf m ω = AvecN d E s v K n m sigPPN ω := by
      intro m hm
      have hDuh := stoppedDuhamelN d E s v K hE2 hs0 hsv hvlt hK0 n 2 sigPPN τf m ω
        (by rw [hτω]; exact (min_le_left _ _).trans hm)
      rw [hτω, min_eq_left hm] at hDuh
      rw [hDuh]
      unfold ppA
      rw [hτω, min_eq_left hm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      funext a
      simp only [ppR, ppDr, YvecN, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    -- the real closure along the grid
    set J : ℕ → ℝ := fun k => jPPN (d.L n) (d.W n) (E n) (gridTime s v K n k)
      (pathH d s v K n k ω) with hJdef
    set Mf : ℕ → ℝ := fun k => scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) with hMfdef
    set S0 : ℝ := Finset.univ.sup' Finset.univ_nonempty
      (fun b : Fin 2 → Z2 (d.L n) => ‖AvecN d E s v K n 0 sigPPN ω b‖) with hS0def
    set Dsum : ℕ → ℝ := fun k => gridStep s v K n * ∑ j ∈ Finset.range k,
      CUN A0 (d.L n) ^ 2 * dBoundPPN (d.L n) (d.W n) (E n) (gridTime s v K n j) (N ^ ε)
        (RPPN d s v n ^ 4) ε (6 / c) (J j) with hDsumdef
    set Qsum : ℕ → ℝ := fun k => N ^ ε * Real.sqrt (∑ j ∈ Finset.range k,
      (Real.toNNReal (cQPPN (d.L n) (d.W n) (E n) (gridTime s v K n (j + 1)) (N ^ ε)
        (RPPN d s v n ^ 10) ε (6 / c) (gridStep s v K n) (CUN A0 (d.L n)) (K n)) : ℝ))
      with hQsumdef
    set Pn : ℝ := N ^ (-(3 : ℝ)) with hPndef
    set Esum : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k,
      (1 + (1 - gridTime s v K n k)⁻¹) ^ 2 * ppStepErr d E s v K n 1 j with hEsumdef
    have hbdJ : ∀ k ≤ K n, J k ≤ Mf k ^ 2 *
        (CUN A0 (d.L n) ^ 2 * S0 + Dsum k + Qsum k + Pn + Esum k) := by
      intro k hk
      have hsup : Finset.univ.sup' Finset.univ_nonempty
          (fun p : Z2 (d.L n) × Z2 (d.L n) => lkGen (d.L n) (d.W n) (E n)
            (gridTime s v K n k) (pathH d s v K n k ω) ![true, true] ![p.1, p.2]) ≤
          CUN A0 (d.L n) ^ 2 * S0 + Dsum k + Qsum k + Pn + Esum k := by
        refine Finset.sup'_le _ _ fun p _ => ?_
        have h := hb k hk ![p.1, p.2]
        have e : lkGen (d.L n) (d.W n) (E n) (gridTime s v K n k) (pathH d s v K n k ω)
            ![true, true] ![p.1, p.2] = ‖ppA d E s v K n τf k ω ![p.1, p.2]‖ := by
          rw [hA k hk]; rfl
        rw [e]
        refine h.trans (le_of_eq ?_)
        simp only [mul_zero, add_zero]
        rfl
      change jPPN (d.L n) (d.W n) (E n) (gridTime s v K n k) (pathH d s v K n k ω) ≤
        scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) ^ 2 *
          (CUN A0 (d.L n) ^ 2 * S0 + Dsum k + Qsum k + Pn + Esum k)
      unfold jPPN
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hsup (sq_nonneg _)
    have hMk_pos : ∀ k ≤ K n, 0 < Mf k := fun k hk =>
      scaleM_pos hL1 hW1 (hE2 n) (hu1 k hk)
    have hLg1 : 1 ≤ LgPPN (E n) N := LgPPN_ge_one (hE2 n) hN1
    have hRnn : 0 ≤ RPPN d s v n := by
      unfold RPPN
      have h1 : 0 < ellT (d.L n) (v n) := (ellT_pos_le hL1 (hvlt n)).1
      have h2 : 0 < ellT (d.L n) (s n) := (ellT_pos_le hL1 ((hsv n).trans_lt (hvlt n))).1
      positivity
    have hS0 : 0 ≤ S0 := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin 2 → Z2 (d.L n)))
      exact (norm_nonneg _).trans (Finset.le_sup' (fun b : Fin 2 → Z2 (d.L n) =>
        ‖AvecN d E s v K n 0 sigPPN ω b‖) (Finset.mem_univ b0))
    have hinit : Mf 0 ^ 2 * S0 ≤ N ^ ε := by
      have h1 : S0 ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun p : Z2 (d.L n) × Z2 (d.L n) => lkGen (d.L n) (d.W n) (E n)
            (gridTime s v K n 0) (pathH d s v K n 0 ω) ![true, true] ![p.1, p.2]) :=
        Finset.sup'_le _ _ fun b _ =>
          lkGen_le_supPPN (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) b
      calc Mf 0 ^ 2 * S0 ≤ Mf 0 ^ 2 * Finset.univ.sup' Finset.univ_nonempty
            (fun p : Z2 (d.L n) × Z2 (d.L n) => lkGen (d.L n) (d.W n) (E n)
              (gridTime s v K n 0) (pathH d s v K n 0 ω) ![true, true] ![p.1, p.2]) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) := by
            unfold jPPN; rw [mul_comm]
        _ ≤ N ^ ε := hωinit
    have hWN : ((d.W n : ℕ) : ℝ) ^ 2 ≤ N := by
      have hL1' : (1 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast hL1
      simp only [hNdef, Sizes.size]
      push_cast
      nlinarith [sq_nonneg ((d.W n : ℝ)), sq_nonneg ((d.L n : ℝ)),
        mul_nonneg (sq_nonneg ((d.W n : ℝ))) (sq_nonneg ((d.L n : ℝ) - 1)),
        mul_nonneg (sq_nonneg ((d.W n : ℝ))) (sub_nonneg.2 hL1')]
    have hMN : ∀ k ≤ K n, Mf k ≤ N := fun k hk =>
      (MLExpVocab_scaleM_le_W2 hL1 (hu1 k hk)).trans hWN
    have hPn : ∀ k ≤ K n, Mf k ^ 2 * Pn ≤ 1 := by
      intro k hk
      have h1 : Mf k ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (hMk_pos k hk).le (hMN k hk) 2
      have h3 : N ^ (3 : ℝ) = N ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h2 : Pn = (N ^ 3)⁻¹ := by
        rw [hPndef, Real.rpow_neg hN0.le, h3]
      calc Mf k ^ 2 * Pn ≤ N ^ 2 * (N ^ 3)⁻¹ :=
            mul_le_mul h1 h2.le (by rw [h2]; positivity) (by positivity)
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            exact pow_le_pow_right₀ hN1 (by norm_num)
    have hEs : ∀ k ≤ K n, Mf k ^ 2 * Esum k ≤ 1 := by
      intro k hk
      have h1 : Esum k ≤ Pn := hswn k hk
      exact (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (hPn k hk)
    have hcl := ppN_closure_real (K := K n) (J := J) (M := Mf) (Dsum := Dsum) (Qsum := Qsum)
      (Esum := Esum) (S0 := S0) (Pn := Pn) (Γ := N ^ ε) (CU2 := CUN A0 (d.L n) ^ 2)
      (Cq := CqPPN (CUN A0 (d.L n)) (d.W n : ℝ) ε) (Lg := LgPPN (E n) N)
      (Av := scaleM (d.L n) (d.W n) (E n) (v n))
      (cP := cPrimePPN (CUN A0 (d.L n)) (N ^ ε) (RPPN d s v n) (LgPPN (E n) N))
      (fun k hk => (hMk_pos k hk).le) hS0 hinit
      (fun k hk => (scaleM_anti_ratio (W := d.W n) hL1 (hE2 n) (hmono 0 k (Nat.zero_le k))
        (hu1 k hk)).1)
      (sq_nonneg _)
      (by unfold CqPPN; positivity) (by linarith) (lt_of_lt_of_le one_pos hM1n)
      (cPrimePPN_ge hΓ1 hRnn hLg1) hzonen hbdJ
      (fun k hk m hm hJm => hdsn J (fun j => jPPN_nonneg _ _ _) k hk m hm hJm)
      (fun k hk => hqsn k hk) hPn hEs
    have hfin := hcl (K n) le_rfl
    have hlast := gridTime_last s v K n (hK0 n)
    simp only [hJdef] at hfin
    rw [hlast] at hfin
    exact hfin


/-! ## 9. The assembly `ppTargetV2_of_pins` -/

/-- **`PPTargetV2` from the statements of the `(+,+)` argument** (the Hölder lift of the
one-dimensional argument is replaced by the per-time form of
`PPTwoLoopPT` and `perTimeDomAt_iff_forall_section`).  The statements: `GridGoodPPN` (good event),
`PPKernelN`, `PPDriftN`, `PPCondVarN`, the sum statements `PPDriftSumN`, `PPQVSumN`, the scale
statement `PPArithN`; `AzumaSubGN`, `YMomentsUnifN`; everything else is proved (`assembledN`,
`stoppedDuhamelN`, `gridDriftN_envelope`, `sum_weighted_stepErrN_le`, `azumaSubG_ugen`,
`hermTestFunLoopN`, `stronglyMeasurable_ZvecN`, `decayLoopWindow`, `kcalDecay`, `map_pathH_eq`).
`Step1WeakLawPT` is not used. -/
theorem ppTargetV2_of_pins {κ c τ : ℝ} (C : ℕ → ℝ) (E s t : ℕ → ℝ)
    (hGood : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), GridGoodPPN d κ c τ E s v t K)
    (hKer : PPKernelN κ) (hDr : PPDriftN) (hQV : PPCondVarN)
    (hDS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPDriftSumN d κ c τ E s v t K)
    (hQS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPQVSumN d κ c τ E s v t K)
    (hArith : PPArithN d κ c τ E s t)
    (hAz : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), AzumaSubGN d s v K)
    (hY : ∀ v : ℕ → ℝ, YMomentsUnifN d κ τ E s v) :
    PPTargetV2 d κ c τ C E s t := by
  intro hU hmain h1 hweak hloc hdec
  have hK : KboundConcl κ := hU.1
  have hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ := hU.2.1
  have hdl : DecayLoopPT d E s t := decayLoopWindow d κ c τ E s t hmain (kcalDecay κ) hV hloc hdec
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, hilk, hidec, hiloc⟩ := hmain'
  obtain ⟨A0, hA0, hrow⟩ := hKer hκ
  have hne : ∀ n, Nonempty (TimeIcc s t n) := fun n => ⟨⟨s n, le_rfl, hst n⟩⟩
  unfold PPTwoLoopPT PT
  rw [perTimeDomAt_iff_forall_section (Sizes.seqP d) d.size hne]
  intro sec τ' hτ' D hD
  set v : ℕ → ℝ := fun n => ((sec n : TimeIcc s t n) : ℝ) with hvdef
  have hsv : ∀ n, s n ≤ v n := fun n => (sec n).2.1
  have hvt : ∀ n, v n ≤ t n := fun n => (sec n).2.2
  have hcτ : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  set ε : ℝ := min (τ' / 8) (min (2 * c) τ / 8) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεc : ε ≤ min (2 * c) τ / 8 := min_le_right _ _
  have hε8 : 8 * ε ≤ τ' := by
    have := min_le_left (τ' / 8) (min (2 * c) τ / 8)
    linarith
  obtain ⟨K, hK0, hev⟩ := ppN_grid_bound hmain hK hV h1 hloc hdec hdl hGood hDr hQV hDS hQS hArith
    hAz hY hA0 hrow v hsv hvt hε hεc hD
  obtain ⟨-, -, hout⟩ := hArith hmain v hsv hvt A0 hA0
  filter_upwards [hev, hout ε hε τ' hε8] with n hn hcP
  obtain ⟨G, hG, hbound⟩ := hn
  set S : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
    {M | ((d.size n : ℕ) : ℝ) ^ τ' * scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) <
      jPPN (d.L n) (d.W n) (E n) (v n) M} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_jPPN (d.L n) (d.W n) (E n) (v n))
  have hHmeas : Measurable (pathH d s v K n (K n)) :=
    (pathH_measurable_filt d s v K n (K n)).mono ((filt d).le (K n)) le_rfl
  have hFmeas : Measurable (Sizes.seqHflow d n (v n)) :=
    Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n (v n) i j
  have hlaw : (Sizes.seqP d) ((Sizes.seqHflow d n (v n)) ⁻¹' S) =
      (pathP d) ((pathH d s v K n (K n)) ⁻¹' S) := by
    rw [← Measure.map_apply hHmeas hSmeas, ← Measure.map_apply hFmeas hSmeas,
      map_pathH_eq d s v K n (K n) (hs0 n) (hsv n) (hK0 n), gridTime_last s v K n (hK0 n)]
  have hsub : {ω | ∃ _u : Unit, ((d.size n : ℕ) : ℝ) ^ τ' *
        scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) <
      jPPN (d.L n) (d.W n) (E n) (v n) (Sizes.seqHflow d n (v n) ω)} ⊆
      (Sizes.seqHflow d n (v n)) ⁻¹' S := by
    rintro ω ⟨_, hω⟩
    exact hω
  have hsub2 : (pathH d s v K n (K n)) ⁻¹' S ⊆ Gᶜ := by
    intro ω hω hωG
    exact absurd (hbound ω hωG) (not_le.2 (lt_of_le_of_lt hcP hω))
  change (Sizes.seqP d) {ω | ∃ _u : Unit, ((d.size n : ℕ) : ℝ) ^ τ' *
        scaleM (d.L n) (d.W n) (E n) (s n) ^ ((1 : ℝ) / 2) <
      jPPN (d.L n) (d.W n) (E n) (v n) (Sizes.seqHflow d n (v n) ω)} ≤ _
  calc _ ≤ (Sizes.seqP d) ((Sizes.seqHflow d n (v n)) ⁻¹' S) := measure_mono hsub
    _ = (pathP d) ((pathH d s v K n (K n)) ⁻¹' S) := hlaw
    _ ≤ (pathP d) Gᶜ := measure_mono hsub2
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
        rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        exact hG

/-- **`PPTargetV2` from the seven `(+,+)` statements alone**: `ppTargetV2_of_pins` with the inputs
discharged by `azumaSubGN` and `yMomentsUnifN` (`RBM2D.Induction.AzumaProxyN`). -/
theorem ppTargetV2_of_ppPins {κ c τ : ℝ} (C : ℕ → ℝ) (E s t : ℕ → ℝ)
    (hGood : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), GridGoodPPN d κ c τ E s v t K)
    (hKer : PPKernelN κ) (hDr : PPDriftN) (hQV : PPCondVarN)
    (hDS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPDriftSumN d κ c τ E s v t K)
    (hQS : ∀ (v : ℕ → ℝ) (K : ℕ → ℕ), PPQVSumN d κ c τ E s v t K)
    (hArith : PPArithN d κ c τ E s t) :
    PPTargetV2 d κ c τ C E s t :=
  ppTargetV2_of_pins C E s t hGood hKer hDr hQV hDS hQS hArith
    (fun v K => azumaSubGN d s v K) (fun v => yMomentsUnifN d κ τ E s v)

end Main

end Pins

end RBM.Ind

end
