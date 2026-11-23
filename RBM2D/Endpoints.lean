/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM2D.MainDefs
public import RBM2D.Gauss.Model
public import RBM2D.Delocalization
public import RBM2D.Propagator.Basic
public import RBM2D.Defs.Semicircle
public import RBM2D.Defs.SemicircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

@[expose] public section

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

/-! ### 1. Delocalization `MR:decol` -/

/-! ### 2. Local semicircle law `MR:locSC` -/

/-! ### 3. Generalized QUE `MR:QUE` -/

/-! ### 4. Quantum diffusion `MR:QDiff` -/

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
