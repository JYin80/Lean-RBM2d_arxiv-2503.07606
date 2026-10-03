/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs

/-!
# The contract vocabulary that does not depend on `lem_GbEXP`

Definitions only (namespace `RBM.Evol`): the scales `ratioR`, `rhoR`, the window decays
`DecayWin`, `DecayWin2`, the deterministic contracts `cPrec`, `SumDecayDetPrec`,
`SumDecayCase5Prec`, the label decay `LabelDecayPT`, and the Step 6 conclusions `oneLoopExpErr`,
`expLoopErr`, `Step61Concl`, `DecayLoopPT`, `MLExpConcl`.  The vocabulary of `RBM.Ind` is used,
not re-declared.
-/

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

variable (d : Sizes)

section Scales

variable (L : ℕ)

/-- `R_{s,t} = ℓ_s²η_s / (ℓ_t²η_t)`, the base of (`sum_res_1`). -/
def ratioR (E s t : ℝ) : ℝ := ellT L s ^ 2 * etaT E s / (ellT L t ^ 2 * etaT E t)

/-- `ℓ_s²(1-s) / (ℓ_t²(1-t))`: `R_{s,t}` without the factor `Im m`, which cancels
(`ratioR L E s t = rhoR L s t` for `|E| < 2`). -/
def rhoR (s t : ℝ) : ℝ := ellT L s ^ 2 * (1 - s) / (ellT L t ^ 2 * (1 - t))

variable [NeZero L]
/-- `(ρ, δ_A)` window decay (with `maxDist`): `HasDecay L W s τ D A` is
`DecayWin L (ellT L s * W^τ) (W^{-D}) A`. -/
def DecayWin {k : ℕ} (ρ δA : ℝ) (A : (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ a : Fin k → Z2 L, ρ ≤ (KLoop.maxDist L a : ℝ) → ‖A a‖ ≤ δA

/-- `(ρ, δ_A)` window decay of a `2k`-tensor, over all `2k` labels. -/
def DecayWin2 {k : ℕ} (ρ δA : ℝ) (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop :=
  ∀ a a' : Fin k → Z2 L, ρ ≤ (KLoop.maxDist L (Fin.append a a') : ℝ) → ‖A a a'‖ ≤ δA

end Scales

/-! ## The deterministic contract -/

/-- The contract constant `C_k(𝔠) = 4k + 4 + 4k/𝔠` (every exponent of §3 and every far term
`N^{4k} ≤ W^{4k/𝔠}` fits). -/
def cPrec (𝔠 : ℝ) (k : ℕ) : ℝ := 4 * k + 4 + 4 * k / 𝔠

/-- **The deterministic sum-decay contract**: general bound (`sum_res_1`), Case 1
(`nonalternating`), Case 4 (`symmetric_tensor`); Case 2 is not included.
Asymptotic form: fixed `κ, 𝔠, δ, k, τ, D` (and `C`), then `∀ ε > 0, ∀ᶠ N`, uniformly over
`W²L² = N`, `W ≥ N^𝔠` (`Main_DEL_COND`), `|E| ≤ 2 - κ`, `0 ≤ s ≤ t ≤ 1 - N^{-1+δ}`
(`lem:sum_decay`), `σ`, `A` with `(s,τ,D)` decay, `a`; conclusion `f ≤ N^ε g`
(`UnifDetDom`, unfolded). -/
def SumDecayDetPrec (κ 𝔠 δ : ℝ) (C : ℕ → ℝ) : Prop :=
  0 < κ → 0 < 𝔠 → 0 < δ →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ ε > (0 : ℝ),
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    t ≤ 1 - (N : ℝ) ^ (-1 + δ) → ∀ (σ : Fin k → Bool) (A : (Fin k → Z2 L) → ℂ),
    HasDecay L W s τ D A → ∀ a : Fin k → Z2 L,
      let base := ratioR L E s t ^ k
      let err := (W : ℝ) ^ (-D + C k)
      -- (sum_res_1)
      ‖Ugen L E σ s t A a‖ ≤ (N : ℝ) ^ ε *
          ((W : ℝ) ^ (C k * τ) * tmax L A * (ellT L t / ellT L s) ^ 2 * base + err) ∧
      -- Case 1: a repeated sign
      ((∃ i : Fin k, σ i = σ (i + 1)) →
        ‖Ugen L E σ s t A a‖ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (C k * τ) * tmax L A * base + err)) ∧
      -- Case 4: sum zero and symmetric
      (SumZero L A → Symmetric L A →
        ‖Ugen L E σ s t A a‖ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (C k * τ) * tmax L A * base + err))

/-- **The Case 5 sum-decay contract**: Case 5 (`eq:double_sum_zero_tensor`), same parameter
set. -/
def SumDecayCase5Prec (κ 𝔠 δ : ℝ) (C : ℕ → ℝ) : Prop :=
  0 < κ → 0 < 𝔠 → 0 < δ →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ ε > (0 : ℝ),
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    t ≤ 1 - (N : ℝ) ^ (-1 + δ) → ∀ (σ : Fin k → Bool) (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ),
    HasDecay2 L W s τ D A → DoubleSumZero L A → ∀ a : Fin k → Z2 L,
      ‖UgenPair L E σ s t A a‖ ≤ (N : ℝ) ^ ε *
        ((W : ℝ) ^ (C k * τ) * tmax2 L A * ratioR L E s t ^ (2 * k) + (W : ℝ) ^ (-D + C k))

/-! ## The Case 3 label decay -/

/-- The `(τ,D)` label decay of the random tensor `𝒜 = (F n).eval` at time `u n` (`deccA0`,
stochastic form): `|𝒜_b| 1(max|b_i - b_j| ≥ ℓ_u W^τ) ≺ W^{-D}`, per time. -/
def LabelDecayPT {k K : ℕ} (E u : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (τ D : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
    (fun n p ω => ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖ *
      (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
    (fun n _ _ => (d.W n : ℝ) ^ (-D))

/-! ## Step 6: `lemma:step6-1` and `ML:exp` -/

/-- `𝔼⟨(G_u - m)E_a⟩ = 𝔼𝓛_{u,(+),(a)} - m` at the energy `E` (`lemma:step6-1`). -/
def oneLoopExpErr (n : ℕ) (E u : ℝ) (a : Z2 (d.L n)) : ℂ :=
  (∫ ω, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n u ω)) (spectralZ E u)
      ⟨[true], [a]⟩ ∂(Sizes.seqP d)) - spectralM E

/-- `𝔼𝓛_{t,σ,a} - 𝒦_{t,σ,a}` for a loop of length `k` (the left side of `eq:step6main`, at `k = 2`).
-/
def expLoopErr (n : ℕ) (E t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 (d.L n)) : ℂ :=
  (∫ ω, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n t ω)) (spectralZ E t)
      (loopOf σ a) ∂(Sizes.seqP d)) - KLoop.Kcal (d.L n) (d.W n) E t (loopOf σ a)

/-- The conclusion of `lemma:step6-1` along a time sequence `u`, deterministic `≺`. -/
def Step61Concl (E u : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ a : Z2 (d.L n),
    ‖oneLoopExpErr d n (E n) (u n) a‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹

/-- (`res_decayLK`) (`lem_decayLoop`), per time over `[s,t]`: for every `k ≥ 1`,
`τ', D' > 0`, `(|𝓛| + |𝓛 - 𝒦|)_{u,σ,a} · 1(max|a_i - a_j| ≥ ℓ_u W^{τ'}) ≺ W^{-D'}`. -/
def DecayLoopPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' > (0 : ℝ), ∀ D' > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω =>
      (loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 +
        lkGen (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2) *
      (if ellT (d.L n) p.1 * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ) then 1 else 0))
    (fun n _ _ => (d.W n : ℝ) ^ (-D'))

/-- The conclusion of `ML:exp` (`eq:step6main`) at the time sequence `t`, all
`σ ∈ {+,-}²`, all `a`, deterministic `≺`. -/
def MLExpConcl (E t : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Z2 (d.L n)),
    ‖expLoopErr d n (E n) (t n) σ a‖ ≤
      ((d.size n : ℕ) : ℝ) ^ ε * (scaleM (d.L n) (d.W n) (E n) (t n) ^ 3)⁻¹

end RBM.Evol
