/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Model
import RBM2D.Delocalization
import RBM2D.Propagator.Basic
import RBM2D.Defs.Semicircle
import RBM2D.Defs.SemicircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support

/-!
# The five endpoint statements of the paper

These are the endpoint statements of the paper, written as closed `def … : Prop` on the
Gaussian model of `RBM2D/Gauss/Model.lean` (`Sizes`, `seqP`, `seqXmat`): `decol` (`MR:decol`),
`locSC` (`MR:locSC`), `QUE` (`MR:QUE`), `QDiff` (`MR:QDiff`) and `BUniv` (`Thm: B_Univ`).

Common shape:
* the paper's "fixed `𝔠`, then `∃ N₀ ∀ N ≥ N₀`" is written for an arbitrary admissible
  size sequence `d : Sizes` (`Admissible 𝔠 d`: `size n → ∞` and eventually `W ≥ N^𝔠`),
  followed by the fixed parameters `κ, τ, D`, followed by `∀ᶠ n`;
* probabilities are `seqP d` of the failure event, bounded by `N^{-D}` with
  `N = d.size n = (W L)²`.
* `N₀` is uniform over the `N`-dependent spectral domain: this is the form the per-sequence
  statements `P7Out` yield.

The "union inside the probability" form of the local law (the bad event for all spectral
parameters at once), needed for the deductions of `MR:decol` and `MR:QUE`, is not part of these
statements.

The semicircle transform `mSC` is the paper's integral; `mSC_eq_msc` identifies it with `msc`
for `0 < Im z`.  The diffusive length `ellz` and the control parameter `Meta` are
`RBM.ellz`, `RBM.Meta`.  `admissible_witnessSizes` shows that the shared hypotheses can be met.
-/

namespace RBM.Endpoints

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes

/-! ### Local objects -/

/-- The semicircle Stieltjes transform, by the paper's integral (Section 2.1):
`m(z) = ∫_{-2}^{2} (2π)⁻¹ √(4-x²) / (x - z) dx`. -/
noncomputable def mSC (z : ℂ) : ℂ :=
  ∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)

/-- `(μ, ψ)` is an orthonormal eigenbasis of `H`: `ψ k` are orthonormal for the
standard inner product and `H ψ_k = μ_k ψ_k`. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

/-- The admissible-sequence hypotheses shared by all five statements: size `N → ∞` and
the bandwidth condition `(Main_DEL_COND)` `W ≥ N^𝔠`, eventually. -/
def Admissible (𝔠 : ℝ) (d : Sizes) : Prop :=
  Tendsto (fun n => d.size n) atTop atTop ∧
    ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)

/-- The Green function of the size-`n` band matrix. -/
noncomputable def Gn (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  green (seqXmat d n ω) z

/-- The spectral domain of `MR:locSC`/`MR:QDiff`:
`z = E + iη`, `|E| ≤ 2 - κ`, `N^{-1+τ} ≤ η ≤ 1`. -/
def locDomain (N : ℕ) (κ τ : ℝ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 1

/-! ### 1. Delocalization `MR:decol` -/

/-- The good event of `MR:decol`: for every orthonormal eigenbasis, every eigenvector
with eigenvalue in `[-2+κ, 2-κ]` has `‖ψ‖²_∞ ≤ N^{-1+τ}`. -/
def decolEvent (d : Sizes) (n : ℕ) (κ τ : ℝ) (ω : SeqΩ d) : Prop :=
  ∀ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ →
      ∀ k, μ k ∈ Set.Icc (-2 + κ) (2 - κ) →
        ∀ x, ‖ψ k x‖ ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ)

/-- **Delocalization `MR:decol`.** -/
def decol : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop,
        seqP d {ω | ¬ decolEvent d n κ τ ω} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-! ### 2. Local semicircle law `MR:locSC` -/

/-- **Local semicircle law `MR:locSC`**, both `(G_bound)` and `(G_bound_ave)`; `N₀` is uniform
over the `N`-dependent spectral domain. -/
def locSC : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z →
        -- (G_bound)
        seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
            ‖Gn d n ω z x y - (if x = y then mSC z else 0)‖ ≤
              (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z)} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        -- (G_bound_ave)
        seqP d {ω | ¬ ∀ a : Z2 (d.L n),
            ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x -
                mSC z‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-! ### 3. Generalized QUE `MR:QUE` -/

/-- The window `𝒥_E = {k : |λ_k - E| ≤ N^{-1-τ} W^{2/3}}` for eigenvalues `μ`. -/
def window {ι : Type*} (N W : ℕ) (τ E : ℝ) (μ : ι → ℝ) (k : ι) : Prop :=
  |μ k - E| ≤ (N : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3)

/-- The failure event of `(Meq:QUE)`: some orthonormal eigenbasis has `k, k' ∈ 𝒥_E` with
`|N ψ_k^*(E_a - N⁻¹) ψ_{k'}|² ≥ N^{-τ/6}`. -/
def queBad (d : Sizes) (n : ℕ) (τ E : ℝ) (a : Z2 (d.L n)) (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k k', window (d.size n) (d.W n) τ E μ k ∧
        window (d.size n) (d.W n) τ E μ k' ∧
        ((d.size n : ℕ) : ℝ) ^ (-τ / 6) ≤
          ‖((d.size n : ℕ) : ℂ) *
              (star (ψ k) ⬝ᵥ ((Epaper (d.L n) (d.W n) a -
                ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *ᵥ ψ k'))‖ ^ 2

/-- The failure event of `(Meq:QUE2)` for a block set `A`. -/
def que2Bad (d : Sizes) (n : ℕ) (τ E : ℝ) (A : Finset (Z2 (d.L n)))
    (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k, window (d.size n) (d.W n) τ E μ k ∧
        (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ) ^ (1 + τ / 6) ≤
          |∑ a ∈ A, ∑ x ∈ Iblk (d.L n) (d.W n) a, ‖ψ k x‖ ^ 2 -
            (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ)|

/-- **Generalized QUE `MR:QUE`**, `(Meq:QUE)` and `(Meq:QUE2)`.  The paper's `D` is unused and
omitted; `(Meq:QUE2)` is stated for nonempty `A`. -/
def QUE : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ τ : ℝ, 0 < τ → τ < 𝔠 / 2 → ∀ κ : ℝ, 0 < κ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| < 2 - κ →
        (∀ a : Z2 (d.L n),
          seqP d {ω | queBad d n τ E a ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6))) ∧
        (∀ A : Finset (Z2 (d.L n)), A.Nonempty →
          seqP d {ω | que2Bad d n τ E A ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6)))

/-! ### 4. Quantum diffusion `MR:QDiff` -/

/-- `tr(G E_a G^σ E_b)` with `G^σ = G†` (`σ = false`) or `G` (`σ = true`). -/
noncomputable def trGEGE (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) (σ : Bool)
    (a b : Z2 (d.L n)) : ℂ :=
  Matrix.trace (Gn d n ω z * Epaper (d.L n) (d.W n) a *
    (if σ then Gn d n ω z else (Gn d n ω z)ᴴ) * Epaper (d.L n) (d.W n) b)

/-- The deterministic profile `W^{-2} (ξ/(1 - ξ S^(B)))_{ab} = W^{-2} ξ (Θ_ξ)_{ab}` with
`ξ = |m|²` (`σ = false`) or `ξ = m²` (`σ = true`), `m = m(z)`. -/
noncomputable def profile (L W : ℕ) [NeZero L] (z : ℂ) (σ : Bool)
    (a b : Z2 L) : ℂ :=
  let ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ)
  ((W : ℂ) ^ 2)⁻¹ * (ξ * Theta L ξ a b)

/-- **Quantum diffusion `MR:QDiff`**: `(Meq:QdW1)`/`(Meq:QdW2)` (`σ = false/true`) with
probability `≥ 1 - N^{-D}`, and `(Meq:QdS1)`/`(Meq:QdS2)` for the expectation. -/
def QDiff : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z → ∀ σ : Bool,
        seqP d {ω | ¬ ∀ a b : Z2 (d.L n),
            ‖trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z ^ 2} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        ∀ a b : Z2 (d.L n),
          ‖(∫ ω, trGEGE d n ω z σ a b ∂(seqP d)) -
              profile (d.L n) (d.W n) z σ a b‖ ≤
            Meta (d.L n) (d.W n) z ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τ

/-! ### 5. Bulk universality `Thm: B_Univ` -/

/-- GUE coordinate variances at dimension `N = (W L)²`: `1/N` on the diagonal and
`1/(2N)` for each real coordinate off the diagonal, so `E|h_ij|² = 1/N`. -/
noncomputable def gueVar (L W : ℕ) (c : Coord L W) : NNReal :=
  if c.1 = c.2.1 then ((((W * L) ^ 2 : ℕ) : NNReal))⁻¹
  else ((2 * ((W * L) ^ 2 : ℕ) : NNReal))⁻¹

/-- The GUE law on the same coordinate space: `Xmat L W` under this measure is an
`N × N` GUE matrix with `E|h_ij|² = 1/N` (the law of `H_∞`, the OU process in the proof of
`Thm: B_Univ`). -/
noncomputable def gueP (L W : ℕ) : Measure (Ω L W) :=
  Measure.infinitePi fun c => ProbabilityTheory.gaussianReal 0 (gueVar L W c)

/-- The symmetric `k`-point functional
`N^k (N-k)!/N! · Σ_{i₁,…,i_k distinct} 𝒪(N(λ_{i₁}-E), …, N(λ_{i_k}-E))`,
which equals `∫ 𝒪(α) ρ^{(k)}(E + α/N) dα` after taking expectation. -/
noncomputable def kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
    ∑ f : Fin k ↪ ι, O (fun j => (Fintype.card ι : ℝ) * (lam (f j) - E))

/-- **Bulk universality `Thm: B_Univ`** (`(eq:universality)`), `𝒪 ∈ C_c^∞(ℝ^k)` with the smoothness
index `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, not the analytic index `ω`. -/
def BUniv : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
          Tendsto (fun n =>
            (∫ ω, kPoint k O E (seqXmat_isHermitian d n ω).eigenvalues ∂(seqP d)) -
            (∫ ω, kPoint k O E (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
              ∂(gueP (d.L n) (d.W n))))
            atTop (𝓝 0)

/-! ### The shared hypotheses are jointly satisfiable

`L n = n + 3`, `W n = (n + 3)²`, `𝔠 = 1/3`: then `N = (n + 3)⁶ → ∞` and `N^{1/3} = W`. -/

/-- A concrete size sequence, `L n = n + 3` and `W n = (n + 3)²`, for which the shared
hypotheses hold (`admissible_witnessSizes`). -/
def witnessSizes : Sizes where
  L := fun n => n + 3
  W := fun n => (n + 3) ^ 2
  three_le_L := fun n => by omega
  W_pos := fun n => by positivity

theorem admissible_witnessSizes : Admissible (1 / 3) witnessSizes := by
  have hsize : ∀ n, witnessSizes.size n = (n + 3) ^ 6 := by
    intro n
    simp only [Sizes.size, witnessSizes]
    ring
  refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
  · simp_rw [hsize]
    refine Filter.tendsto_atTop_mono (fun n => ?_) Filter.tendsto_id
    calc n ≤ n + 3 := by omega
      _ ≤ (n + 3) ^ 6 := Nat.le_self_pow (by norm_num) _
  · rw [hsize]
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 3) := by positivity
    have h6 : (((n + 3) ^ 6 : ℕ) : ℝ) = (((n : ℝ) + 3) ^ (2 : ℕ)) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]
      push_cast
      rw [← Real.rpow_natCast]
      norm_num
    rw [h6, ← Real.rpow_mul (by positivity)]
    simp [witnessSizes]

/-- The paper's integral `mSC` agrees with `msc` for `0 < Im z`. -/
theorem mSC_eq_msc {z : ℂ} (hz : 0 < z.im) : mSC z = msc z :=
  (msc_eq_integral hz).symm

/-- Check at `z = i`. -/
example : mSC Complex.I = msc Complex.I := mSC_eq_msc (by simp)

/-! ### Axiom check -/

#print axioms decol
#print axioms locSC
#print axioms QUE
#print axioms QDiff
#print axioms BUniv
#print axioms admissible_witnessSizes
#print axioms mSC_eq_msc

end RBM.Endpoints
