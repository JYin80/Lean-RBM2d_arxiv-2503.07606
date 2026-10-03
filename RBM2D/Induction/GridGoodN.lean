/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.GridDuhamelN
import RBM2D.Induction.QVN
import RBM2D.Induction.BcalE
import RBM2D.Path.GoodEventClose
import RBM2D.Path.Bootstrap

/-!
# The vocabulary of the general-`n` grid walk, and its measurability

The definitions of sections 1-4 are `Prop`-valued (or auxiliary): the good set `GoodSetN` and the
exit time of the grid walk, the high-probability grid event `GridGoodN`, the first-chaos part
`ZvecN`, the remainder `YvecN`, the Azuma proxies, the test class `HermTestFunLoopN` (carrying the
constant `k (k + 1)`), the `Y` moments and the assembled bound `AssembledN`.  Nothing in them is a
claim of the paper by itself.

Paper: arXiv:2503.07606, Section 5: `lem:STOeq_NQ`, `lem:STOeq_Qt`, the stopped loop hierarchy
(`int_K-L_ST`), its martingale term (`lem:DIfREP`, `alu9_STime`), `lem_decayLoop`, `lem_BcalE`,
`def:CALE`.

Proved here (all unconditional, no hypothesis on `E s t K n j σ`):
* `measurableGoodSetN : MeasurableGoodSetN` and `goodExitMeasN` (section 5);
* `stronglyMeasurable_ZvecN`, `stronglyMeasurable_YvecN` (section 5).

Section 6 composes these with `stoppedDuhamelN`, `qvPropagatedN`, `bcalEPT'`:
`hexp_at_goodExit`, `qv_at_propagator`, `hΦ_of_hermTestFunLoopN` (for the constant `k (k + 1)` of
`HermTestFunLoopN`), `azumaSubG_ugen`, `azumaSubG_goodExit`.

Layout: 1. the good set and its exit time; 2. the high-probability grid event; 3. the first-chaos
part `Z`, the remainder `Y`, the Azuma proxies, the test class; 4. the `Y` moments and the
assembled bound; 5. the measurability results; 6. compositions.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The good set and its exit time -/

section GoodSet

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **`GoodSetN`**: the general-`n` good set of the grid walk at the spectral time `u`,
for the target loop length `k` (the paper's `n`), levels `Λ Φ`, loss `Γ` (the caller takes
`Γ = N^ε`) and decay exponents `τ' D'`; scales `M_u = scaleM`, `η_u = etaT`, `N = (WL)²`.  Paper:
the stopping time of `lem:STOeq_NQ` and `lem:STOeq_Qt`.  The clauses:
* Hermitian;
* (G1)-(G4): `Ξ^{(𝓛)}_{2k+2} ≤ ΓΛ`; `Ξ^{(𝓛-𝒦)}_m ≤ ΓΦ` (`1 ≤ m < k`); the products
  `Ξ_mΞ_{k-m+2}M^{-1} ≤ ΓΦ`; `Ξ^{(𝓛)}_{k+1} ≤ ΓΦ` (the four `STOeqPT` inputs);
* (Dec) (`decaySet`, `lkDecaySet`): `|𝓛| + |𝓛-𝒦| ≤ W^{-D'}` at labels farther than
  `ℓ_u W^{τ'}`, lengths `≤ 2k+2` (`lem_decayLoop`);
* (D1)-(D4), (V): the four terms of
  `lem_BcalE` (`ksimLK`, `elklkN`, `egtN`, `eeN`) are bounded by `Γ·(k-1)·ΓΦ·M^{-k}η^{-1}`,
  `ΓΓΦ·M^{-k}η^{-1}`, `ΓΓΛ·M^{-2k}η^{-1}` (+`W^{-D'}` for (ii)-(iv)), and decay at far labels
  (`CalEbwXi`; conjuncts (i)-(v) of `BcalEPT'`). -/
def GoodSetN (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) : Set (Matrix (Idx L W) (Idx L W) ℂ) :=
  {M | M.IsHermitian ∧
    xiL L W E u M (2 * k + 2) ≤ Γ * Λ ∧
    (∀ m : ℕ, 1 ≤ m → m < k → xiLK L W E u M m ≤ Γ * Φ) ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ k →
      xiLK L W E u M m * xiLK L W E u M (k - m + 2) * (scaleM L W E u)⁻¹ ≤ Γ * Φ) ∧
    xiL L W E u M (k + 1) ≤ Γ * Φ ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) →
        loopAbs L W E u M σ a + lkGen L W E u M σ a ≤ (W : ℝ) ^ (-D')) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ‖ksimLK L W E u M l (loopOf σ a)‖ ≤
        Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ‖elklkN L W E u M (loopOf σ a)‖ ≤
        Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) +
          (W : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ‖egtN L W E u M (loopOf σ a)‖ ≤
        Γ * (Γ * Φ) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Z2 L),
      ‖eeN L W E u M σ a a'‖ ≤
        Γ * (Γ * Λ) * ((scaleM L W E u ^ (2 * k))⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) →
        ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ +
          ‖elklkN L W E u M (loopOf σ a)‖ + ‖egtN L W E u M (loopOf σ a)‖ ≤ (W : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Z2 L),
      ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L (Fin.append a a') : ℝ) →
        ‖eeN L W E u M σ a a'‖ ≤ (W : ℝ) ^ (-D'))}

end GoodSet

section ExitTime

variable (d : Sizes)

/-- **`gridExitTauN`**: the exit time of an arbitrary good-set family `G` (measurable
matrix sets, one per grid index) from the grid walk: the first `j ≤ K n` with `H_j ∉ G j`, and
`K n` if there is none (`firstHit` of the indicator of the complement at level `1/2`).  The
generic form serves `GoodSetN` and the good set of the `(+,+)` case. -/
def gridExitTauN (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)) : PathΩ d → ℕ :=
  firstHit (fun j (ω : PathΩ d) => (G j)ᶜ.indicator (fun _ => (1 : ℝ)) (pathH d s v K n j ω))
    (1 / 2) (K n)

/-- **`goodExitTauN`**: the exit time of the grid walk from `GoodSetN`. -/
def goodExitTauN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (n : ℕ) : PathΩ d → ℕ :=
  gridExitTauN d s v K n (fun j =>
    GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')

/-- **Matrix-level measurability of `GoodSetN`**: true without hypotheses (finite intersections of
level sets of the measurable maps `M ↦ 𝓛(M)`, `GoodEvent_measurable_gloop`). -/
def MeasurableGoodSetN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ),
    MeasurableSet (GoodSetN L W E u k Γ Λ Φ τ' D')

/-- **Measurability of `{j < goodExitTauN}`** (in the form `StoppedAzumaN` takes); follows from
`MeasurableGoodSetN` (`goodExitMeasN_of_measurable`). -/
def GoodExitMeasN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ),
    MeasurableSet[filt d j] {ω | j < goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω}

variable {d} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
  {G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)}

/-- `gridExitTauN ≤ K n`. -/
theorem gridExitTauN_le (ω : PathΩ d) : gridExitTauN d s v K n G ω ≤ K n :=
  firstHit_le _ _ _ ω

/-- Strictly before the exit, the grid state is in `G`. -/
theorem mem_of_lt_gridExitTauN {ω : PathΩ d} {j : ℕ} (h : j < gridExitTauN d s v K n G ω) :
    pathH d s v K n j ω ∈ G j := by
  have h1 := lt_firstHit_imp _ _ _ h
  by_contra hmem
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h1
  norm_num at h1

/-- If the grid state stays in `G` up to `K n`, the exit time is `K n`. -/
theorem gridExitTauN_eq_of_forall_mem {ω : PathΩ d} (hgood : ∀ j ≤ K n, pathH d s v K n j ω ∈ G j) :
    gridExitTauN d s v K n G ω = K n := by
  refine firstHit_eq_of_below _ _ _ fun j hj => ?_
  have hnot : pathH d s v K n j ω ∉ (G j)ᶜ := fun hc => hc (hgood j hj)
  rw [Set.indicator_of_notMem hnot]
  norm_num

/-- `{j < gridExitTauN}` is `filt d j`-measurable when every `G j` is measurable. -/
theorem gridExitTauN_measurableSet (hG : ∀ j, MeasurableSet (G j)) (j : ℕ) :
    MeasurableSet[filt d j] {ω | j < gridExitTauN d s v K n G ω} :=
  lt_firstHit_grid_measurableSet d s v K n
    (F := fun j M => (G j)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (fun j => measurable_const.indicator (hG j).compl) (1 / 2) (K n) j

/-- The matrix-level measurability gives `GoodExitMeasN`. -/
theorem goodExitMeasN_of_measurable {E : ℕ → ℝ} (hM : MeasurableGoodSetN) :
    GoodExitMeasN d E s v K :=
  fun n k Γ Λ Φ τ' D' j =>
    gridExitTauN_measurableSet (fun j => hM _ _ _ _ _ _ _ _ _ _) j

end ExitTime

/-! ## 2. The high-probability grid event -/

section GridGood

variable (d : Sizes)

/-- **`GridGoodN`**: with high probability the grid walk on `[s,v] ⊆ [s,t]` stays in
`GoodSetN` for every `j ≤ K n`: the union bound over the `K n + 1 ≤ N^C` grid times and the
`≤ 2^k L^{2k} ≤ (2N)^k` labels and clauses, each with failure `N^{-D₂}` for every `D₂`.  The
`d = 2` pattern is `goodEvent_grid` (`RBM2D.Path.GoodEventClose`), whose part (G) is
`GoodEventClose_goodSet_union` (via `map_pathH_eq`).
Inputs and why: the seven premises are those of `BcalEPT'` (`bcalEPT'` gives the drift-term
clauses (D1)-(D4), (V) from `MainIndHyp, KboundConcl, KcalDecay, GbEXPHypV3, Step2LocalPT,
Step2DecayPT, DecayLoopPT`), `DecayLoopPT` also gives (Dec) directly; the four `PT` hypotheses are
those of `STOeqPT` (`RBM2D.Induction.Defs`) and give (G1)-(G4) and the levels of (D1)-(D4).
`Bandwidth` (in `MainIndHyp`) absorbs `N^ε` into `W^{-D'}`. -/
def GridGoodN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  MainIndHyp d κ c τ E s t → KboundConcl κ → KcalDecay κ →
  RBM.Green.GbEXPHypV3 d (κ / 2) c τ → Step2LocalPT d E s t → Step2DecayPT d E s t →
  DecayLoopPT d E s t → (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → (∀ n, K n ≠ 0) →
  ∀ k : ℕ, 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) →
    (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
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
    ∀ C : ℝ, (∀ᶠ n : ℕ in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ C) →
    ∀ ε > (0 : ℝ), ∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ),
      HighProbAt (pathP d) d.size (fun n => {ω | ∀ j ≤ K n,
        pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k
          (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'})

end GridGood

/-! ## 3. The first-chaos part `Z`, the remainder `Y`, and the Azuma proxies -/

section Azuma

variable (d : Sizes)

/-- The directional derivative of an observable `Φ` at `M` along `X` (real parameter):
`d/dy Φ(M + yX)` at `y = 0`; equal to `fderiv ℝ Φ M X` when `Φ` is differentiable at `M`. -/
def dirDerivN {L W : ℕ} [NeZero L] [NeZero W] (Φ : Matrix (Idx L W) (Idx L W) ℂ → ℂ)
    (M X : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  deriv (fun y : ℝ => Φ (M + (y : ℂ) • X)) 0

/-- **`ZfamN`**: the first-chaos part of a family `Φ` of observables on the grid step
`j → j+1`: `Z_b = √Δ · ∂_{X_{j+1}} Φ_b (H_j)` (linear in the Gaussian increment `X_{j+1}`), for an
arbitrary complex family `Φ`; compare `stepZ` of `RBM2D.Path.StepDecomp` (real, `Z2 × Z2`
labels). -/
def ZfamN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ) (ω : PathΩ d) : ι → ℂ :=
  fun b => ((Real.sqrt (gridStep s t K n) : ℝ) : ℂ) *
    dirDerivN (Φ b) (pathH d s t K n j ω) (Sizes.seqXmat d n (ω (j + 1)))

/-- **`ZvecN`**: the first-chaos part of `martIncN` (the step `j → j+1`): `√Δ` times the
directional derivative of `𝓛_{u_{j+1},σ,b}` at `H_j` along the Gaussian increment `X_{j+1}` (linear
in `X_{j+1}`; the k = 2 `(+,-)` case is `Zvec`, `RBM2D.Path.Expansion`). -/
def ZvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun b => ((Real.sqrt (gridStep s t K n) : ℝ) : ℂ) *
    loopDerivN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (pathH d s t K n j ω)
      (Sizes.seqXmat d n (ω (j + 1))) σ b

/-- **`YvecN`**: the quadratic remainder `martIncN - ZvecN`. -/
def YvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun b => martIncN d E s t K n j σ ω b - ZvecN d E s t K n j σ ω b

/-- The stopped, propagated increment `1_{j<τ} (𝒰_{u_{j+1},t'} Y_j)_b`. -/
def stoppedEdgeN {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    (τ : PathΩ d → ℕ) (Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ) (b : Fin k → Z2 (d.L n))
    (j : ℕ) (ω : PathΩ d) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => Ugen (d.L n) E σ (u (j + 1)) t' (Y j ω') b) ω

/-- Conditional sub-Gaussianity (real and imaginary part, common proxy `c`) of the stopped
complex increment `1_{j<τ} F` given `F_j` (a `HasCondSubgaussianMGF` pair). -/
def SubGaussFormN (j : ℕ) (τ : PathΩ d → ℕ) (F : PathΩ d → ℂ) (c : ℝ≥0) : Prop :=
  HasCondSubgaussianMGF (filt d j) ((filt d).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).re) c (pathP d) ∧
  HasCondSubgaussianMGF (filt d j) ((filt d).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).im) c (pathP d)

/-- The `hsubG` hypothesis of the assembled bound: the stopped, propagated increment
`1_{j<τ} (𝒰_{u_{j+1},u_m} Z_j)_a` is conditionally sub-Gaussian with proxy `c`. -/
def SubGaussStopN {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ d → ℕ)
    (Z : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ) (m : ℕ) (a : Fin k → Z2 (d.L n)) (j : ℕ)
    (c : ℝ≥0) : Prop :=
  SubGaussFormN d j τ (fun ω' => Ugen (d.L n) E σ (u (j + 1)) (u m) (Z j ω') a) c

/-- **`StoppedAzumaZN`**: the stopped Azuma bound for the first-chaos part `ZvecN`, in place of
the full martingale increment `martIncN`.  The sharp sub-Gaussian proxy is available only for
`ZvecN` (`QVPropagatedN` gives the gradient at `H_j`, not on the segment `[H_j, H_{j+1}]`), so
the version for `martIncN` cannot be fed by `AzumaSubGN`.  Paper: `alu9_STime` with BDG replaced
by Azuma-Hoeffding. -/
def StoppedAzumaZN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n k : ℕ) [NeZero k] (σ : Fin k → Bool) (τ : PathΩ d → ℕ),
    (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
    ∀ (m : ℕ), m ≤ K n → ∀ (a : Fin k → Z2 (d.L n)) (c : ℕ → ℝ≥0),
      (∀ j < m, SubGaussStopN d (E n) σ (gridTime s t K n) τ
        (fun j ω => ZvecN d E s t K n j σ ω) m a j (c j)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP d).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (ZvecN d E s t K n j σ ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- `Re Σ_{b,b'} κ_b conj(κ_{b'}) (𝓔⊗𝓔)_{b,b'}(M)` for the propagator weights
`κ_b = Π_i (𝒰-slot)(a_i, b_i)` of `𝒰_{v,w,σ}` and `𝓔⊗𝓔` at the spectral time `v`: the right-hand
side of `QVPropagatedN` at `κ = κ_·` (paper `(alu9_STime)`: `((𝒰_σ ⊗ 𝒰_σ̄) ∘ (𝓔⊗𝓔))_{a,a}`). -/
def qvFormN (L W : ℕ) [NeZero L] [NeZero W] (E v w : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k → Z2 L) : ℝ :=
  (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
    (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) *
      (starRingEnd ℂ) (∏ i : Fin k,
        ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b' i)) *
      eeN L W E v M σ b b').re

/-- **`AzumaSubGN` (the Azuma proxies)**: for a finite family `Φ` of observables in the
Hermitian test class, weights `κ`, a stopping family `{j<τ} ∈ F_j` on which the grid state lies in
a set `G j`, and `Q` majorising the conditional-variance form `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²`
on the Hermitian matrices of `G j`: the stopped combination `1_{j<τ} Σ_b κ_b Z_b` of the
first-chaos parts is conditionally sub-Gaussian with proxy `Q` (real and imaginary parts).
It is used with a closed form of `Q` for each of the three cases (non-alternating, alternating,
`(+,+)`).  Proof: `hasCondSubgaussianMGF_linear` (`RBM2D.Path.Markov`) on the directions
`Σ_b κ_b gradMat Φ_b (H_j)` and its `-i` multiple, with
`linTrVar ≤ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b‖²`.  For loops the hypothesis on `Q` is supplied by
`QVPropagatedN` (`qv_at_propagator`) and the `GoodSetN` clauses (D4), (V), (G1); see
`azumaSubG_ugen`, `azumaSubG_goodExit`. -/
def AzumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {ι : Type} [Fintype ι]
    (Φ : ι → Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ),
    (∀ b, HermTestFun d n (Φ b)) → ∀ (κ : ι → ℂ) (τ : PathΩ d → ℕ)
    (G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)),
    (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
    (∀ ω j, j < τ ω → pathH d s t K n j ω ∈ G j) →
    ∀ (j : ℕ) (Q : ℝ≥0),
      (∀ M ∈ G j, M.IsHermitian →
        gridStep s t K n * ∑ c : Coord (d.L n) (d.W n), (gvar (d.L n) (d.W n) c : ℝ) *
          ‖∑ b, κ b * dirDerivN (Φ b) M (coordinateMatrix (d.L n) (d.W n) c)‖ ^ 2 ≤ (Q : ℝ)) →
      SubGaussFormN d j τ (fun ω => ∑ b, κ b * ZfamN d s t K n j Φ ω b) Q

end Azuma

section TestClass

open scoped Matrix.Norms.L2Operator

variable (d : Sizes)

/-- **`HermTestFunLoopN`, with the constant hard-coded**: every `k`-loop observable
`M ↦ 𝓛_{z,σ,b}(M)` (any length `k ≥ 1`, any signs, complex-valued) is in the Hermitian test class and has the Hermitian second-derivative
bound `‖∂²𝓛(M)[y,y]‖ ≤ k(k+1) N η^{-(k+2)} ‖y‖²`, `z = z_u`, `η = η_u` (`∂²` of a product of `k`
resolvents has `2k + k(k−1)` terms).  It is the input `hΦ` of `azumaSubG_ugen` and of the `Y` moments
(`C₂` in `stepDecompCN`).  The case `k = 2`, `σ = (+,-)`, `C = 6 = 2·3` is `hermTestFun_loopPM`
(`RBM2D.Path.StepDecompLoop`).  For the alternating case the family `Q_u ∘ 𝓛` is a
finite linear combination of such observables. -/
def HermTestFunLoopN : Prop :=
  ∀ (k : ℕ) [NeZero k] (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n)),
      HermTestFun d n (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
        gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (loopOf σ b)) ∧
      ∀ M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ, M.IsHermitian →
        y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
            gloop (d.L n) (d.W n) (blockMat M) (spectralZ E u) (loopOf σ b))) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size d n : ℝ) * (etaT E u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2


end TestClass


/-! ## 4. The `Y` moments and the assembled pathwise bound -/

section Assembly

variable (d : Sizes)

/-- The moment inputs of the fourth-moment tail: `Y_j` is `F_{j+1}`-measurable; the stopped, propagated
increment has conditional mean zero, integrable fourth power, conditional second moment `≤ v_j` and
fourth moment `≤ w_j` (real and imaginary parts). -/
def YMomentBoundsN {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ d → ℕ) (K : ℕ) (Y : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
    (v w : ℕ → ℝ) : Prop :=
  (∀ j, StronglyMeasurable[filt d (j + 1)] (Y j)) ∧
  ∀ m ≤ K, ∀ (b : Fin k → Z2 (d.L n)) (j : ℕ), j < m →
    (pathP d)[fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).re | filt d j] =ᵐ[pathP d] 0 ∧
    (pathP d)[fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).im | filt d j] =ᵐ[pathP d] 0 ∧
    Integrable (fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).re ^ 4) (pathP d) ∧
    Integrable (fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).im ^ 4) (pathP d) ∧
    (pathP d)[fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).re ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => v j) ∧
    (pathP d)[fun ω => (stoppedEdgeN d E σ u (u m) τ Y b j ω).im ^ 2 | filt d j]
      ≤ᵐ[pathP d] (fun _ => v j) ∧
    ∫ ω, (stoppedEdgeN d E σ u (u m) τ Y b j ω).re ^ 4 ∂(pathP d) ≤ w j ∧
    ∫ ω, (stoppedEdgeN d E σ u (u m) τ Y b j ω).im ^ 4 ∂(pathP d) ≤ w j

/-- **The analytic hypothesis bundle of the assembly**, step-indexed (`Z j`, `Y j` are the step
`j → j+1`), with an abstract kernel class `Cls`, on the path space.
`hexp` is a.e. (`stoppedDuhamelN`, `hexp_at_goodExit`), `hR` is a.e. (`gridDriftN` is a.e.;
`gridDriftN_envelope`), `hdrift`/`hDcls` are pathwise on `{j < τ}` (from `GoodSetN` clauses),
`hY` is `YMomentsUnifN`, the sub-Gaussian input is `AzumaSubGN`. -/
structure GridAssemblyHypN {n k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ d → ℕ) (Δ : ℝ) (K : ℕ)
    (Cls : ℕ → ℝ → ((Fin k → Z2 (d.L n)) → ℂ) → Prop)
    (A0 : PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
    (A : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
    (Dr Z Y R : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
    (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ d → ℝ)
    (c : ℕ → (Fin k → Z2 (d.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) : Prop where
  hE : |E| ≤ 2
  hu0 : ∀ i ≤ K, 0 ≤ u i
  hu1 : ∀ i ≤ K, u i < 1
  hΔ0 : 0 ≤ Δ
  hexp : ∀ m ≤ K, ∀ᵐ ω ∂(pathP d), A m ω = Ugen (d.L n) E σ (u 0) (u m) (A0 ω) +
    ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) E σ (u (j + 1)) (u m)
      ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)
  hκ0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ κ i m
  hε0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ εK i m
  hker : ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Z2 (d.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
    (∀ b, ‖X b‖ ≤ M) → Cls i δ X →
    ∀ a, ‖Ugen (d.L n) E σ (u i) (u m) X a‖ ≤ κ i m * M + εK i m * δ
  hδ0 : 0 ≤ δ0
  hA0cls : ∀ ω, 0 < τ ω → Cls 0 δ0 (A0 ω)
  hdDrift0 : ∀ ω j, j < K → 0 ≤ dDrift j ω
  hδD0 : ∀ ω j, j < K → 0 ≤ δD j ω
  hdrift : ∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω
  hDcls : ∀ ω j, j < K → j < τ ω → Cls (j + 1) (δD j ω) (Dr j ω)
  hc_pos : ∀ m, 1 ≤ m → m ≤ K → ∀ a, 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ)
  hv0 : ∀ j < K, 0 ≤ v j
  hw0 : ∀ j < K, 0 ≤ w j
  hY : YMomentBoundsN d E σ u τ K Y v w
  hstepErr0 : ∀ j < K, 0 ≤ stepErr j
  hR : ∀ᵐ ω ∂(pathP d), ∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j

/-- **`AssembledN` (the assembled pathwise bound)**, for `Ugen` on `Fin k → Z2 L`
(label count `L^{2k} ≤ N^k`).  Fixed `k, ε, D, D₁, C_P, C_K` with
`D₁ + 4D + k + 2C_P + 8 ≤ C_K`, then `∀ᶠ n`, uniformly over the grid `K ≤ ⌈N^{C_K}⌉`,
`Δ ≤ N^{-C_K}`, `KΔ ≤ 1`, and all data satisfying the bundle: one event `G`,
`P(Gᶜ) ≤ N^{-D₁}`, on which `0 < τ` gives the bound for every target `m ≤ K` and label `a`:
`‖A_m(a)‖ ≤ κ_{0m}‖A_0‖ + ε_{0m}δ₀ + Δ Σ_{j<m}(κ_{j+1,m} d_j + ε_{j+1,m} δD_j)
  + N^ε (Σ_{j<m} c)^{1/2} + N^{-D} + Σ_{j<m}(1 + (1-u_m)⁻¹)^k stepErr_j`.
The premise `SizeTendsto d` is necessary (`W ≡ 1`, `L ≡ 3`): for a bounded size `N` the Azuma tail
`4 exp(-N^{2ε}/4)` is a positive constant while `D₁` is arbitrary. -/
def AssembledN : Prop :=
  SizeTendsto d → ∀ (k : ℕ) [NeZero k] (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
    D₁ + 4 * D + (k : ℝ) + 2 * C_P + 8 ≤ C_K →
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ d → ℕ)
      (Δ : ℝ) (Cls : ℕ → ℝ → ((Fin k → Z2 (d.L n)) → ℂ) → Prop)
      (A0 : PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
      (A : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
      (Dr Z Y R : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ)
      (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ d → ℝ)
      (c : ℕ → (Fin k → Z2 (d.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      1 ≤ K → K ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊ →
      Δ ≤ ((d.size n : ℕ) : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 →
      0 ≤ P → P ≤ ((d.size n : ℕ) : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
      (∀ j, StronglyMeasurable[filt d (j + 1)] (Z j)) →
      (∀ m ≤ K, ∀ (a : Fin k → Z2 (d.L n)) (j : ℕ), j < m →
        SubGaussStopN d E σ u τ Z m a j (c m a j)) →
      GridAssemblyHypN d E σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set (PathΩ d), (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Z2 (d.L n),
          ‖A m ω a‖ ≤
            κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) +
            εK 0 m * δ0 +
            Δ * ∑ j ∈ Finset.range m,
              (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) +
            ((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((d.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j

end Assembly

/-! ## 5. The measurability results

All four theorems are unconditional (no hypothesis on `E s t K n j σ`, on `|E| < 2` or on `u < 1`).
`MeasurableGoodSetN` needs no premise because `GoodSetN` is a finite conjunction, over finitely
many labels, of inequalities between measurable functions of `M` (norms of the `gloop`-built
functionals) and the closed set `M.IsHermitian` (template: `measurableGoodSet` of
`RBM2D.Path.GoodSet`).

`ZvecN` needs care because `loopDerivN` is `deriv` of a line function `y ↦ 𝓛(M + yX)` whose
`Matrix.inv` factors have the junk value `0` at singular matrices (for `|E| ≥ 2` or `u = 1` the
spectral parameter is real, and even for non-real `z` and non-Hermitian `M, X` the determinant can
vanish).  The proof does not assume `Im z ≠ 0`: the determinants along the line are analytic in the
line parameter, hence either vanish identically near `0` or have an isolated zero at `0`
(`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`), so the line function is continuous on a
punctured neighbourhood of `0`; then `deriv · 0` is measurable in the parameters (difference
quotients along the rationals, `StronglyMeasurable.limUnder`). -/

section MeasurableGoodSetNProof

private theorem GridGoodN_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

private theorem GridGoodN_measurableSet_imp {α : Type*} [MeasurableSpace α] {p : Prop}
    {q : α → Prop} (h : p → MeasurableSet {x | q x}) : MeasurableSet {x | p → q x} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem GridGoodN_meas_LLf (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => LLf L W E u M I :=
  GoodEvent_measurable_gloop L W (spectralZ E u) I

private theorem GridGoodN_meas_LKf (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => LKf L W E u M I :=
  (GridGoodN_meas_LLf L W E u I).sub_const _

private theorem GridGoodN_meas_loopAbs (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => loopAbs L W E u M σ a :=
  (GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ a)).norm

private theorem GridGoodN_meas_lkGen (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => lkGen L W E u M σ a :=
  ((GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ a)).sub_const _).norm

private theorem GridGoodN_meas_xiL (E u : ℝ) (k : ℕ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => xiL L W E u M k := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        loopAbs L W E u M p.1 p.2)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => GridGoodN_meas_loopAbs L W E u p.1 p.2
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => xiL L W E u M k) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          loopAbs L W E u M p.1 p.2)) M * scaleM L W E u ^ (k - 1) := by
    funext M
    simp only [xiL, Finset.sup'_apply]
  rw [heq]
  exact hsup.mul_const _

private theorem GridGoodN_meas_xiLK (E u : ℝ) (k : ℕ) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => xiLK L W E u M k := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
        lkGen L W E u M p.1 p.2)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => GridGoodN_meas_lkGen L W E u p.1 p.2
  have heq : (fun M : Matrix (Idx L W) (Idx L W) ℂ => xiLK L W E u M k) =
      fun M => (Finset.univ.sup' Finset.univ_nonempty
        (fun (p : (Fin k → Bool) × (Fin k → Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) =>
          lkGen L W E u M p.1 p.2)) M * scaleM L W E u ^ k := by
    funext M
    simp only [xiLK, Finset.sup'_apply]
  rw [heq]
  exact hsup.mul_const _

private theorem GridGoodN_meas_ksimLK (E u : ℝ) (l : ℕ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => ksimLK L W E u M l I := by
  unfold ksimLK
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((GridGoodN_meas_LKf L W E u _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      (((measurable_const).mul (measurable_const)).mul (GridGoodN_meas_LKf L W E u _))
      measurable_const

private theorem GridGoodN_meas_ksimLK_sum (E u : ℝ) (k : ℕ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l I :=
  Finset.measurable_sum _ fun l _ => GridGoodN_meas_ksimLK L W E u l I

private theorem GridGoodN_meas_elklkN (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => elklkN L W E u M I := by
  unfold elklkN
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((GridGoodN_meas_LKf L W E u _).mul_const _).mul (GridGoodN_meas_LKf L W E u _)

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = 𝓛_{u,(σ),(a)} - m(σ) tr E_a`: the one-edge loop. -/
private theorem GridGoodN_avgErr_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (a : Z2 L) :
    avgErr L W E u M σ a = gloop L W (blockMat M) (spectralZ E u) ⟨[σ], [a]⟩ -
      KLoop.mSig E σ * Matrix.trace (Eblk L W a) := by
  unfold avgErr greenBlk gloop
  rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]
  simp [gloopProd]

private theorem GridGoodN_meas_avgErr (E u : ℝ) (σ : Bool) (a : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => avgErr L W E u M σ a := by
  simp only [GridGoodN_avgErr_eq]
  exact (GoodEvent_measurable_gloop L W (spectralZ E u) ⟨[σ], [a]⟩).sub_const _

private theorem GridGoodN_meas_egtN (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => egtN L W E u M I := by
  unfold egtN
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((GridGoodN_meas_avgErr L W E u _ a).mul_const _).mul (GridGoodN_meas_LLf L W E u _)

private theorem GridGoodN_meas_eeN (E u : ℝ) {n : ℕ} (σ : Fin n → Bool) (a a' : Fin n → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => eeN L W E u M σ a a' := by
  unfold eeN
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun b _ => Finset.measurable_sum _ fun b' _ => ?_)
  exact measurable_const.mul (GridGoodN_meas_LLf L W E u _)

end MeasurableGoodSetNProof

/-- **`measurableGoodSetN`**: `GoodSetN` is a measurable set of matrices, for every
`L W E u k Γ Λ Φ τ' D'` (no hypothesis).  Template: `measurableGoodSet` of
`RBM2D.Path.GoodSet` (`k = 2`). -/
theorem measurableGoodSetN : MeasurableGoodSetN := by
  intro L W _ _ E u k Γ Λ Φ τ' D'
  have hH : MeasurableSet {M : Matrix (Idx L W) (Idx L W) ℂ | M.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  unfold GoodSetN
  simp only [Set.ofPred_and]
  refine hH.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))))))))))
  · exact measurableSet_le (GridGoodN_meas_xiL L W E u _) measurable_const
  · exact GridGoodN_measurableSet_forall fun m => GridGoodN_measurableSet_imp fun _ =>
      GridGoodN_measurableSet_imp fun _ =>
        measurableSet_le (GridGoodN_meas_xiLK L W E u m) measurable_const
  · exact GridGoodN_measurableSet_forall fun m => GridGoodN_measurableSet_imp fun _ =>
      GridGoodN_measurableSet_imp fun _ =>
        measurableSet_le (((GridGoodN_meas_xiLK L W E u m).mul
          (GridGoodN_meas_xiLK L W E u (k - m + 2))).mul_const _) measurable_const
  · exact measurableSet_le (GridGoodN_meas_xiL L W E u _) measurable_const
  · exact GridGoodN_measurableSet_forall fun j => GridGoodN_measurableSet_imp fun _ =>
      GridGoodN_measurableSet_imp fun _ => GridGoodN_measurableSet_forall fun σ =>
        GridGoodN_measurableSet_forall fun a => GridGoodN_measurableSet_imp fun _ =>
          measurableSet_le ((GridGoodN_meas_loopAbs L W E u σ a).add
            (GridGoodN_meas_lkGen L W E u σ a)) measurable_const
  · exact GridGoodN_measurableSet_forall fun l => GridGoodN_measurableSet_imp fun _ =>
      GridGoodN_measurableSet_imp fun _ => GridGoodN_measurableSet_forall fun σ =>
        GridGoodN_measurableSet_forall fun a =>
          measurableSet_le (GridGoodN_meas_ksimLK L W E u l (loopOf σ a)).norm measurable_const
  · exact GridGoodN_measurableSet_forall fun σ => GridGoodN_measurableSet_forall fun a =>
      measurableSet_le (GridGoodN_meas_elklkN L W E u (loopOf σ a)).norm measurable_const
  · exact GridGoodN_measurableSet_forall fun σ => GridGoodN_measurableSet_forall fun a =>
      measurableSet_le (GridGoodN_meas_egtN L W E u (loopOf σ a)).norm measurable_const
  · exact GridGoodN_measurableSet_forall fun σ => GridGoodN_measurableSet_forall fun a =>
      GridGoodN_measurableSet_forall fun a' =>
        measurableSet_le (GridGoodN_meas_eeN L W E u σ a a').norm measurable_const
  · exact GridGoodN_measurableSet_forall fun σ => GridGoodN_measurableSet_forall fun a =>
      GridGoodN_measurableSet_imp fun _ =>
        measurableSet_le (((GridGoodN_meas_ksimLK_sum L W E u k (loopOf σ a)).norm.add
          (GridGoodN_meas_elklkN L W E u (loopOf σ a)).norm).add
            (GridGoodN_meas_egtN L W E u (loopOf σ a)).norm) measurable_const
  · exact GridGoodN_measurableSet_forall fun σ => GridGoodN_measurableSet_forall fun a =>
      GridGoodN_measurableSet_forall fun a' => GridGoodN_measurableSet_imp fun _ =>
        measurableSet_le (GridGoodN_meas_eeN L W E u σ a a').norm measurable_const

section Targets

variable (d : Sizes)

/-- **Target `goodExitMeasN`**: `{j < goodExitTauN}` is `filt d j`-measurable (from
`measurableGoodSetN` and `goodExitMeasN_of_measurable`). -/
theorem goodExitMeasN (E s v : ℕ → ℝ) (K : ℕ → ℕ) : GoodExitMeasN d E s v K :=
  goodExitMeasN_of_measurable measurableGoodSetN

end Targets

section DerivMeasurability

open scoped Topology

/-- A function on `ℝ` that is continuous on a punctured neighbourhood of `0` and whose limit of
difference quotients along the rationals exists has that limit as the limit along the reals (the
rationals are dense and the quotient is continuous near `0`, `0` excluded). -/
private theorem GridGoodN_tendsto_of_rat {g : ℝ → ℂ} {c : ℂ}
    (hg : ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt g y)
    (h : Tendsto (fun r : ℚ => g (r : ℝ)) (𝓝[≠] (0 : ℚ)) (𝓝 c)) :
    Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hg
  obtain ⟨δ₀, hδ₀, hg⟩ := hg
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := h (ε / 2) (half_pos hε)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun {y} hy0 hy => ?_⟩
  have hy0' : y ≠ 0 := hy0
  have hyabs : |y| < min δ₀ δ₁ := by simpa [Real.dist_eq] using hy
  have hcy : ContinuousAt g y := hg (by
    rw [Real.dist_eq, sub_zero]; exact hyabs.trans_le (min_le_left _ _)) hy0'
  obtain ⟨ρ, hρ, hρy⟩ := Metric.continuousAt_iff.1 hcy (ε / 2) (half_pos hε)
  have hypos : 0 < |y| := abs_pos.2 hy0'
  set ρ' := min ρ (min |y| (min δ₀ δ₁ - |y|)) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min hypos (sub_pos.2 hyabs))
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show y - ρ' < y + ρ' by linarith)
  have hrabs : |(r : ℝ) - y| < ρ' := by
    rw [abs_lt]; constructor <;> linarith
  have hr_ne : (r : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hrabs
    exact absurd (hrabs.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (lt_irrefl _)
  have hr_small : |(r : ℝ)| < min δ₀ δ₁ := by
    have h3 : |(r : ℝ)| ≤ |y| + |(r : ℝ) - y| := by
      calc |(r : ℝ)| = |y + ((r : ℝ) - y)| := by ring_nf
        _ ≤ |y| + |(r : ℝ) - y| := abs_add_le _ _
    have h4 : |(r : ℝ) - y| < min δ₀ δ₁ - |y| :=
      hrabs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hcr : dist (g (r : ℝ)) c < ε / 2 := by
    refine h1 (x := r) (by simpa using hr_ne) ?_
    rw [Rat.dist_eq]; simp only [Rat.cast_zero, sub_zero]
    exact hr_small.trans_le (min_le_right _ _)
  have hgy : dist (g (r : ℝ)) (g y) < ε / 2 :=
    hρy (by rw [Real.dist_eq]; exact hrabs.trans_le (min_le_left _ _))
  calc dist (g y) c ≤ dist (g y) (g (r : ℝ)) + dist (g (r : ℝ)) c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm]; exact add_lt_add hgy hcr
    _ = ε := by ring

/-- **Carathéodory-type measurability of the derivative at `0`**: if `a ↦ f a y` is measurable for
each `y` and each `f a` is continuous on a punctured neighbourhood of `0`, then
`a ↦ deriv (f a) 0` is measurable (no continuity in `a`; the derivative is `0` where `f a` is not
differentiable at `0`). -/
private theorem GridGoodN_measurable_deriv_zero {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : ∀ y, Measurable fun a => f a y)
    (hreg : ∀ a, ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (f a) y) :
    Measurable fun a => deriv (f a) 0 := by
  classical
  let q : α → ℚ → ℂ := fun a r => slope (f a) 0 (r : ℝ)
  have hq : ∀ r : ℚ, Measurable fun a => q a r := fun r => by
    simp only [q, slope, vsub_eq_sub, sub_zero]
    exact ((hf r).sub (hf 0)).const_smul _
  have hqs : ∀ r : ℚ, StronglyMeasurable fun a => q a r := fun r => (hq r).stronglyMeasurable
  let T : Set α := {a | ∃ c, Tendsto (fun r : ℚ => q a r) (𝓝[≠] (0 : ℚ)) (𝓝 c)}
  have hT : MeasurableSet T :=
    StronglyMeasurable.measurableSet_exists_tendsto (l := 𝓝[≠] (0 : ℚ)) (f := fun r a => q a r) hqs
  have hΨ : StronglyMeasurable fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r) :=
    StronglyMeasurable.limUnder (l := 𝓝[≠] (0 : ℚ)) (f := fun r a => q a r) hqs
  have hcast : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[≠] (0 : ℚ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (Rat.continuous_coe_real.tendsto (0 : ℚ)).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℚ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact Rat.cast_ne_zero.2 hr
  have hslope_cont : ∀ a, ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (slope (f a) 0) y := by
    intro a
    filter_upwards [hreg a, self_mem_nhdsWithin] with y hy hy0
    have hy0' : y ≠ 0 := hy0
    have hs : slope (f a) 0 = fun x => x⁻¹ • (f a x - f a 0) := by
      funext x; simp [slope]
    rw [hs]
    exact (continuousAt_inv₀ hy0').smul (hy.sub continuousAt_const)
  have hderiv : ∀ a, deriv (f a) 0 =
      T.indicator (fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r)) a := by
    intro a
    by_cases haT : a ∈ T
    · obtain ⟨c, hc⟩ := haT
      have hreal : Tendsto (slope (f a) 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) :=
        GridGoodN_tendsto_of_rat (hslope_cont a) hc
      have hd : HasDerivAt (f a) c 0 := hasDerivAt_iff_tendsto_slope.2 hreal
      rw [Set.indicator_of_mem (show a ∈ T from ⟨c, hc⟩), hd.deriv]
      exact hc.limUnder_eq.symm
    · rw [Set.indicator_of_notMem haT]
      refine deriv_zero_of_not_differentiableAt fun hdiff => haT ?_
      exact ⟨_, (hasDerivAt_iff_tendsto_slope.1 hdiff.hasDerivAt).comp hcast⟩
  have : (fun a => deriv (f a) 0) =
      T.indicator (fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r)) := funext hderiv
  rw [this]
  exact hΨ.measurable.indicator hT

/-- The determinant along a line `y ↦ A + y B` (`y` real) is analytic in `y`. -/
private theorem GridGoodN_det_line_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (y₀ : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => (A + (y : ℂ) • B).det) y₀ := by
  have hent : ∀ i j : ι, AnalyticAt ℝ (fun y : ℝ => (A + (y : ℂ) • B) i j) y₀ := by
    intro i j
    have h1 : AnalyticAt ℝ (fun y : ℝ => (y : ℂ)) y₀ := Complex.ofRealCLM.analyticAt y₀
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact analyticAt_const.add (h1.mul analyticAt_const)
  simp only [Matrix.det_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  have hprod : AnalyticAt ℝ (fun y : ℝ => ∏ i, (A + (y : ℂ) • B) (σ i) i) y₀ :=
    Finset.analyticAt_fun_prod _ fun i _ => hent (σ i) i
  simp only [Units.smul_def, zsmul_eq_mul]
  exact analyticAt_const.mul hprod

/-- **Regularity of the matrix inverse along a line** (junk value `0` at singular matrices
included): `y ↦ (A + y B)⁻¹` is continuous on a punctured neighbourhood of `0`.  Either the
determinant vanishes identically near `0` (then the inverse is `0` there) or it has an isolated
zero at `0`. -/
private theorem GridGoodN_inv_line_regular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (fun y : ℝ => (A + (y : ℂ) • B)⁻¹) y := by
  have hcont : Continuous (fun y : ℝ => A + (y : ℂ) • B) :=
    continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)
  rcases (GridGoodN_det_line_analytic A B 0).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · have h0' : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), ∀ᶠ y' : ℝ in 𝓝 y, (A + (y' : ℂ) • B).det = 0 :=
      h0.eventually_nhds
    filter_upwards [h0'.filter_mono nhdsWithin_le_nhds] with y hy
    have hz : (fun y' : ℝ => (A + (y' : ℂ) • B)⁻¹) =ᶠ[𝓝 y] fun _ => (0 : Matrix ι ι ℂ) := by
      filter_upwards [hy] with y' hy'
      exact Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hy']; exact not_isUnit_zero)
    exact continuousAt_const.congr hz.symm
  · filter_upwards [h1] with y hy
    have hinv : ContinuousAt Ring.inverse (A + (y : ℂ) • B).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hy
    exact ContinuousAt.comp (f := fun y : ℝ => A + (y : ℂ) • B) (x := y)
      (continuousAt_matrix_inv _ hinv) hcont.continuousAt

private theorem GridGoodN_foldr_continuousAt {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (G : Bool → ℝ → Matrix ι ι ℂ) (Ea : α → Matrix ι ι ℂ) (y : ℝ)
    (hG : ∀ b, ContinuousAt (G b) y) (l : List (Bool × α)) :
    ContinuousAt (fun y => l.foldr (fun p Acc => G p.1 y * Ea p.2 * Acc) (1 : Matrix ι ι ℂ)) y := by
  induction l with
  | nil => exact continuousAt_const
  | cons p l ih =>
      simp only [List.foldr_cons]
      exact ((hG p.1).mul continuousAt_const).mul ih

/-- **Regularity of a loop observable along a line**: for every spectral parameter `z` (real or
not), loop `I` and matrices `M, X` (Hermitian or not), `y ↦ 𝓛_{z,I}(M + yX)` is continuous on a
punctured neighbourhood of `0`. -/
private theorem GridGoodN_gloop_line_regular (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ)
    (I : LoopIdx (Z2 L)) (M X : Matrix (Idx L W) (Idx L W) ℂ) :
    ∀ᶠ y in 𝓝[≠] (0 : ℝ),
      ContinuousAt (fun y : ℝ => gloop L W (blockMat (M + (y : ℂ) • X)) z I) y := by
  have hb : ∀ y : ℝ, blockMat (M + (y : ℂ) • X) = blockMat M + (y : ℂ) • blockMat X := by
    intro y
    simp [blockMat, Matrix.submatrix_add, Matrix.submatrix_smul]
  have hinv : ∀ w : ℂ, ∀ᶠ y in 𝓝[≠] (0 : ℝ),
      ContinuousAt (fun y : ℝ => (blockMat (M + (y : ℂ) • X) - w • (1 : Matrix (BlockIndex L W)
        (BlockIndex L W) ℂ))⁻¹) y := by
    intro w
    have h := GridGoodN_inv_line_regular (blockMat M - w • (1 : Matrix (BlockIndex L W)
      (BlockIndex L W) ℂ)) (blockMat X)
    have hfun : (fun y : ℝ => (blockMat (M + (y : ℂ) • X) - w • (1 : Matrix (BlockIndex L W)
        (BlockIndex L W) ℂ))⁻¹) = fun y : ℝ => ((blockMat M - w • (1 : Matrix (BlockIndex L W)
        (BlockIndex L W) ℂ)) + (y : ℂ) • blockMat X)⁻¹ := by
      funext y
      rw [hb y]
      congr 1
      abel
    rw [hfun]
    exact h
  filter_upwards [hinv z, hinv ((starRingEnd ℂ) z)] with y hz hzc
  have hG : ∀ b : Bool, ContinuousAt (fun y : ℝ => Gsig (blockMat (M + (y : ℂ) • X)) z b) y := by
    intro b
    cases b
    · exact hzc
    · exact hz
  have hfold := GridGoodN_foldr_continuousAt
    (fun (b : Bool) (y : ℝ) => Gsig (blockMat (M + (y : ℂ) • X)) z b)
    (fun a : Z2 L => Eblk L W a) y hG (I.σ.zip I.a)
  exact (continuous_id.matrix_trace).continuousAt.comp hfold

/-- `(M, X) ↦ loopDerivN L W E u M X σ b` is measurable on all pairs of matrices. -/
private theorem GridGoodN_measurable_loopDerivN (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    Measurable fun p : Matrix (Idx L W) (Idx L W) ℂ × Matrix (Idx L W) (Idx L W) ℂ =>
      loopDerivN L W E u p.1 p.2 σ b := by
  unfold loopDerivN
  refine GridGoodN_measurable_deriv_zero
    (fun (p : Matrix (Idx L W) (Idx L W) ℂ × Matrix (Idx L W) (Idx L W) ℂ) (y : ℝ) =>
      gloop L W (blockMat (p.1 + (y : ℂ) • p.2)) (spectralZ E u) (loopOf σ b)) (fun y => ?_)
    (fun p => GridGoodN_gloop_line_regular L W (spectralZ E u) (loopOf σ b) p.1 p.2)
  have hlin : Measurable fun p : Matrix (Idx L W) (Idx L W) ℂ × Matrix (Idx L W) (Idx L W) ℂ =>
      p.1 + (y : ℂ) • p.2 :=
    Measurable.of_eval_matrix _ fun i j => by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact measurable_fst.eval_matrix.add (measurable_snd.eval_matrix.const_mul _)
  exact (GoodEvent_measurable_gloop L W (spectralZ E u) (loopOf σ b)).comp hlin

end DerivMeasurability

section ZYMeasurability

variable (d : Sizes)

/-- The draw `ω l` is `filt d k`-measurable for `l ≤ k` (as in `pathH_adapted`). -/
private theorem GridGoodN_measurable_coord {k l : ℕ} (hl : l ≤ k) :
    Measurable[filt d k] (fun ω : PathΩ d => ω l) := by
  have : (fun ω : PathΩ d => ω l)
      = (fun g : Set.Iic k → Sizes.SeqΩ d => g ⟨l, hl⟩)
        ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ d) k))

/-- The pair (grid state at step `j`, Gaussian increment `X_{j+1}`) is `filt d (j+1)`-measurable. -/
private theorem GridGoodN_measurable_pair (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    Measurable[filt d (j + 1)] (fun ω : PathΩ d =>
      (pathH d s t K n j ω, Sizes.seqXmat d n (ω (j + 1)))) := by
  have hH : Measurable[filt d (j + 1)] (fun ω : PathΩ d => pathH d s t K n j ω) :=
    (pathH_measurable_filt d s t K n j).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt d (j + 1)] (fun ω : PathΩ d => Sizes.seqXmat d n (ω (j + 1))) :=
    ((continuous_Xmat (d.L n) (d.W n)).measurable.comp (Sizes.measurable_slice d n)).comp
      (GridGoodN_measurable_coord d le_rfl)
  exact hH.prodMk hX

/-- The `b`-th component of `ZvecN` is `filt d (j + 1)`-measurable. -/
private theorem GridGoodN_measurable_ZvecN_apply (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n)) :
    Measurable[filt d (j + 1)] (fun ω : PathΩ d => ZvecN d E s t K n j σ ω b) := by
  have hΨ := GridGoodN_measurable_loopDerivN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) σ b
  have hpair := GridGoodN_measurable_pair d s t K n j
  exact (hΨ.comp hpair).const_mul _

/-- The `b`-th component of `martIncN` is `filt d (j + 1)`-measurable (`A_{j+1}` minus a
`filt d j`-conditional expectation). -/
private theorem GridGoodN_measurable_martIncN_apply (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 (d.L n)) :
    Measurable[filt d (j + 1)] (fun ω : PathΩ d => martIncN d E s t K n j σ ω b) := by
  have h1 : Measurable[filt d (j + 1)] (fun ω : PathΩ d => AvecN d E s t K n (j + 1) σ ω b) :=
    ((GoodEvent_measurable_gloop (d.L n) (d.W n) (spectralZ (E n) (gridTime s t K n (j + 1)))
      (loopOf σ b)).comp (pathH_measurable_filt d s t K n (j + 1))).sub_const _
  have h2 : Measurable[filt d (j + 1)] (fun ω : PathΩ d =>
      (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' b | filt d j] ω) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  exact h1.sub h2

/-- **Target `stronglyMeasurable_ZvecN`**: `ZvecN` (step `j → j+1`) is `filt d (j + 1)`-strongly
measurable (the `hZmeas` input of `AssembledN`), for every `E s t K n j σ` (no hypothesis). -/
theorem stronglyMeasurable_ZvecN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) :
    StronglyMeasurable[filt d (j + 1)] (fun ω => ZvecN d E s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun b =>
    GridGoodN_measurable_ZvecN_apply d E s t K n j σ b

/-- **Target `stronglyMeasurable_YvecN`**: `YvecN = martIncN - ZvecN` is `filt d (j + 1)`-strongly
measurable (the first field of `YMomentBoundsN`), for every `E s t K n j σ` (no hypothesis). -/
theorem stronglyMeasurable_YvecN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) :
    StronglyMeasurable[filt d (j + 1)] (fun ω => YvecN d E s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun b =>
    (GridGoodN_measurable_martIncN_apply d E s t K n j σ b).sub
      (GridGoodN_measurable_ZvecN_apply d E s t K n j σ b)

end ZYMeasurability

/-! ## 6. Compositions -/

section Compose

variable {d : Sizes}

/-- **(G1 ∘ exit time)**: `stoppedDuhamelN` at the random target `goodExitTauN ≤ K n` is the
stopped expansion that the assembled bound (`hexp`) needs. -/
theorem hexp_at_goodExit {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (n k : ℕ) [NeZero k] (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (ω : PathΩ d) :
    AvecN d E s v K n (goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω) σ ω =
      Ugen (d.L n) (E n) σ (gridTime s v K n 0)
          (gridTime s v K n (goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω))
          (AvecN d E s v K n 0 σ ω) +
        ∑ j ∈ Finset.range (goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω),
          Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
            (gridTime s v K n (goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω))
            (predIncN d E s v K n j σ ω + martIncN d E s v K n j σ ω) := by
  have h := stoppedDuhamelN d E s v K hE hs0 hsv hv1 hK0 n k σ
    (goodExitTauN d E s v K k Γ Λ Φ τ' D' n) (K n) ω (min_le_left _ _)
  have hle : goodExitTauN d E s v K k Γ Λ Φ τ' D' n ω ≤ K n := gridExitTauN_le ω
  rwa [min_eq_right hle] at h

/-- **(B5 ∘ Azuma proxies)**: the variance identity `qvPropagatedN` at the propagator weights is
`Σ_c gvar_c ‖∂_c Σ_b κ_b 𝓛_b‖² ≤ k · qvFormN`, the quantity that `AzumaSubGN` majorises by `Q/Δ`. -/
theorem qv_at_propagator (L W : ℕ) [NeZero L] [NeZero W] (E u w : ℝ) (hL : 3 ≤ L) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    ∑ c : Coord L W, (gvar L W c : ℝ) *
        ‖∑ b : Fin k → Z2 L,
          (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u w (a i) (b i)) *
            loopDerivN L W E u M (coordinateMatrix L W c) σ b‖ ^ 2 ≤
      (k : ℝ) * qvFormN L W E u w σ M a :=
  qvPropagatedN L W E u hL hE hu0 hu1 M hM k hk σ
    (fun b => ∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u w (a i) (b i))

/-- The `hΦ` input of `azumaSubG_ugen` from `HermTestFunLoopN`: for every grid index
`j + 1 ≤ K n` the loop observable at the spectral time `u_{j+1} ∈ [0, 1)` is in the test class. -/
theorem hΦ_of_hermTestFunLoopN (h : HermTestFunLoopN d) {E s t : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) [NeZero k] (σ : Fin k → Bool) (j : ℕ) (hj : j + 1 ≤ K n)
    (b : Fin k → Z2 (d.L n)) :
    HermTestFun d n (fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      gloop (d.L n) (d.W n) (blockMat M) (spectralZ (E n) (gridTime s t K n (j + 1)))
        (loopOf σ b)) := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (GoodEvent_gridTime_le (K := K) (hst n) hj).trans_lt (ht1 n)
  exact (h k n (E n) (gridTime s t K n (j + 1)) (hE n) hu0 hu1 σ b).1

/-- **(`AzumaSubGN` for loops)**: the `Ugen`-form input `SubGaussStopN` of the assembled bound
from the generic statement, for the loop family `Φ_b = 𝓛_{u_{j+1},σ,b}`, the propagator weights
`κ_b = Π_i (𝒰-slot)(a_i, b_i)` and the variance identity `qv_at_propagator`.  The test-class input
is `HermTestFunLoopN` (via `hΦ_of_hermTestFunLoopN`); what remains for a consumer is the
deterministic majorant `hQ` of `Δ · k · qvFormN` on `G j`. -/
theorem azumaSubG_ugen {E s t : ℕ → ℝ} {K : ℕ → ℕ} (h : AzumaSubGN d s t K)
    (hT : HermTestFunLoopN d)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool)
    (τ : PathΩ d → ℕ) (G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → pathH d s t K n j ω ∈ G j) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * ((k : ℝ) * qvFormN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN d (E n) σ (gridTime s t K n) τ (fun j ω => ZvecN d E s t K n j σ ω) m a j Q := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (GoodEvent_gridTime_le (K := K) (hst n) (show j + 1 ≤ K n by omega)).trans_lt (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := GoodEvent_gridStep_nonneg (hst n)
  exact h n (fun b M => gloop (d.L n) (d.W n) (blockMat M)
      (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ b))
    (hΦ_of_hermTestFunLoopN hT hE hs0 hst ht1 n k σ j (by omega))
    (fun b => ∏ i : Fin k, ukerMat (d.L n)
      (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (a i) (b i)) τ G hτ hG j Q
    (fun M hMG hMH => (mul_le_mul_of_nonneg_left
      (qv_at_propagator (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) (gridTime s t K n m)
        (d.three_le_L n) (hE n) hu0 hu1 M hMH k hk σ a) hΔ).trans (hQ M hMG hMH))

/-- **(`AzumaSubGN` ∘ `GoodSetN` ∘ `goodExitTauN`)**: with `G j = GoodSetN …` and
`τ = goodExitTauN`, the membership hypothesis of `azumaSubG_ugen` is `mem_of_lt_gridExitTauN` and
its measurability hypothesis is `GoodExitMeasN`; what remains is the deterministic majorant `hQ`
on `GoodSetN` (supplied by the consumers from the clauses (D4), (V), (G1)). -/
theorem azumaSubG_goodExit {E s v : ℕ → ℝ} {K : ℕ → ℕ} (h : AzumaSubGN d s v K)
    (hT : HermTestFunLoopN d)
    (hM : GoodExitMeasN d E s v K) (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (σ : Fin k → Bool)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormN (d.L n) (d.W n) (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN d (E n) σ (gridTime s v K n)
      (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
      (fun j ω => ZvecN d E s v K n j σ ω) m a j Q :=
  azumaSubG_ugen h hT hE hs0 hsv hv1 n k hk σ (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
    (fun j => GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')
    (hM n k Γ Λ Φ τ' D') (fun ω j hj => mem_of_lt_gridExitTauN hj) m hm a j hj Q hQ

end Compose

end RBM.Ind

end
