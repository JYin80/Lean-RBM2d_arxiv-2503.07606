/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.Domination
import RBM2D.Gauss.Envelope
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# From stochastic domination to moments

This is the reverse bridge for Definition 2.1(i). A whole-space envelope controls the
exceptional event; for Green functions that envelope is `norm_green_le`. The positive
control has an eventual polynomial lower bound, uniformly over all parameters.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-! ### The reverse bridge: `≺` + deterministic envelope ⟹ moments -/

section Reverse

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- A whole-space pointwise envelope makes every even power integrable. -/
theorem integrable_abs_evenPow_of_envelope {Y : Ω → ℝ} {M : ℝ}
    (hmeas : Measurable Y) (hbound : ∀ ω, |Y ω| ≤ M) (p : ℕ) :
    Integrable (fun ω => |Y ω| ^ (2 * p)) P := by
  have hm : Measurable (fun ω => |Y ω| ^ (2 * p)) := by
    have hma : Measurable fun ω => |Y ω| := by
      simpa [Real.norm_eq_abs] using hmeas.norm
    exact hma.pow_const _
  refine Integrable.mono' (integrable_const (M ^ (2 * p)))
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (Y ω)) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) _

/-- **The reverse bridge.**

Let `Y(N,u)` be dominated by a positive deterministic control `Φ(N,u)` in the sense of
Definition 2.1 (i), `|Y| ≺ Φ`, and assume

* `Φ` is not super-polynomially small: `N^{-B} ≤ Φ(N,u)` eventually, uniformly in `u`;
* `Y` has a **deterministic envelope**: `|Y(N,u,ω)| ≤ Env(N)` for *every* `ω`, with `Env ≥ 0`
  of polynomial growth `Env(N) ≤ N^{Kenv}` eventually.

Then all moments of `Y` are bounded relative to `Φ` in the sense of `RBM.Gauss.MomentDom`, with
the quantifier order of `RBM2D/Gauss/Domination.lean` (`ε` outside `p`).

Together with `RBM.Gauss.stochDom_of_momentDom` this makes the round trip
`≺ → moments → (generator identity, Grönwall) → moments → ≺` available without changing the
shape of any `≺`-valued interface. -/
theorem momentDom_of_stochDom {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), |Y N u ω| ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u)) :
    MomentDom P Y Φ := by
  intro ε hε p
  have hPuniv : (0 : ℝ) ≤ P.real Set.univ := measureReal_nonneg
  refine ⟨P.real Set.univ + 1, by linarith, ?_⟩
  set τ : ℝ := ε / 2 with hτ_def
  have hτ : 0 < τ := half_pos hε
  set D' : ℝ := 2 * p * (Kenv + B) + 1 with hD'_def
  have hD'0 : 0 < D' := by
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hKB : (0 : ℝ) ≤ 2 * (p : ℝ) * (Kenv + B) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hD'_def]; linarith
  filter_upwards [hΦlow, hEnvpoly, hdom τ hτ D' hD'0, eventually_ge_atTop 1] with
    N hΦN hEN hbad hN1
  intro u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the threshold and the exceptional set for this single `u`
  set c : ℝ := (N : ℝ) ^ τ * Φ N u with hc_def
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos hNpos τ) (hΦ N u)
  set S : Set Ω := {ω | c < |Y N u ω|} with hS_def
  have habs : Measurable fun ω => |Y N u ω| := by
    simpa [Real.norm_eq_abs] using (hmeas N u).norm
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const habs
  have hSsub : S ⊆ badSet (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u) τ N := fun ω hω => ⟨u, hω⟩
  have hPS : P.real S ≤ (N : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P S).toReal ≤ (ENNReal.ofReal ((N : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hSsub).trans hbad)
      _ = (N : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)
  -- the pointwise split
  have hEnvpow : (0 : ℝ) ≤ Env N ^ (2 * p) := pow_nonneg (hEnv0 N) _
  have hcpow : (0 : ℝ) ≤ c ^ (2 * p) := pow_nonneg hc0.le _
  have hpt : ∀ ω, |Y N u ω| ^ (2 * p)
      ≤ c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : |Y N u ω| ^ (2 * p) ≤ Env N ^ (2 * p) :=
        pow_le_pow_left₀ (abs_nonneg _) (henv N u ω) _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |Y N u ω| ≤ c := not_lt.1 hω
      have h2 : |Y N u ω| ^ (2 * p) ≤ c ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) h1 _
      linarith
  have hRHSint : Integrable
      (fun ω => c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hSmeas)
  have hint : Integrable (fun ω => |Y N u ω| ^ (2 * p)) P :=
    integrable_abs_evenPow_of_envelope (hmeas N u) (henv N u) p
  have hle := integral_mono hint hRHSint hpt
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hSmeas), integral_const,
    integral_indicator_const _ hSmeas, smul_eq_mul, smul_eq_mul] at hle
  -- the main part is exactly `N^{εp} Φ^{2p}`
  have hmain : c ^ (2 * p) = (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    rw [hc_def, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 2
    rw [hτ_def]
    push_cast
    ring
  -- the exceptional part is negligible
  have hΦpow : (N : ℝ) ^ (-(B * (2 * p))) ≤ Φ N u ^ (2 * p) := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (hΦN u) (2 * p)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-B)) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have htail : P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    have h1 : Env N ^ (2 * p) ≤ ((N : ℝ) ^ Kenv) ^ (2 * p) :=
      pow_le_pow_left₀ (hEnv0 N) hEN _
    have h2 : ((N : ℝ) ^ Kenv) ^ (2 * p) = (N : ℝ) ^ (Kenv * (2 * p)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ Kenv) (2 * p), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    have hStep : P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (-D') * (N : ℝ) ^ (Kenv * (2 * p)) := by
      refine mul_le_mul hPS (h2 ▸ h1) hEnvpow (Real.rpow_nonneg hNpos.le _)
    have hExp : (N : ℝ) ^ (-D') * (N : ℝ) ^ (Kenv * (2 * p))
        = (N : ℝ) ^ (-(B * (2 * p)) + -1) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      rw [hD'_def]
      ring
    have hDrop : (N : ℝ) ^ (-(B * (2 * p)) + -1) ≤ (N : ℝ) ^ (-(B * (2 * p))) := by
      refine Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hNge1 (mul_nonneg hε.le (Nat.cast_nonneg p))
    have hΦ2p : (0 : ℝ) ≤ Φ N u ^ (2 * p) := pow_nonneg (hΦ N u).le _
    calc P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (-(B * (2 * p))) := by
          rw [hExp] at hStep; exact hStep.trans hDrop
      _ ≤ Φ N u ^ (2 * p) := hΦpow
      _ ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by nlinarith
  -- assemble
  have hmainpos : (0 : ℝ) ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (pow_nonneg (hΦ N u).le _)
  calc ∫ ω, |Y N u ω| ^ (2 * p) ∂P
      ≤ P.real Set.univ * c ^ (2 * p) + P.real S * Env N ^ (2 * p) := hle
    _ ≤ P.real Set.univ * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))
        + (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
          rw [hmain]; linarith
    _ = (P.real Set.univ + 1) * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by ring

/-- Reverse bridge along admissible physical dimensions and a common probability measure. -/
theorem momentDomAt_of_stochDomAt (size : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop) {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (size N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), |Y N u ω| ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (size N : ℝ) ^ Kenv)
    (hdom : StochDomAt P size (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u)) :
    MomentDomAt P size Y Φ := by
  intro ε hε p
  have hPuniv : (0 : ℝ) ≤ P.real Set.univ := measureReal_nonneg
  refine ⟨P.real Set.univ + 1, by linarith, ?_⟩
  set τ : ℝ := ε / 2 with hτ_def
  have hτ : 0 < τ := half_pos hε
  set D' : ℝ := 2 * p * (Kenv + B) + 1 with hD'_def
  have hD'0 : 0 < D' := by
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hKB : (0 : ℝ) ≤ 2 * (p : ℝ) * (Kenv + B) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hD'_def]; linarith
  filter_upwards [hΦlow, hEnvpoly, hdom τ hτ D' hD'0, hsize.eventually (eventually_ge_atTop 1)] with
    N hΦN hEN hbad hN1
  intro u
  have hNpos : (0 : ℝ) < size N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
  -- the threshold and the exceptional set for this single `u`
  set c : ℝ := (size N : ℝ) ^ τ * Φ N u with hc_def
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos hNpos τ) (hΦ N u)
  set S : Set Ω := {ω | c < |Y N u ω|} with hS_def
  have habs : Measurable fun ω => |Y N u ω| := by
    simpa [Real.norm_eq_abs] using (hmeas N u).norm
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const habs
  have hSsub : S ⊆ badSetAt size (fun N u ω => |Y N u ω|)
      (fun N u _ => Φ N u) τ N := fun ω hω => ⟨u, hω⟩
  have hPS : P.real S ≤ (size N : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P S).toReal ≤ (ENNReal.ofReal ((size N : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hSsub).trans hbad)
      _ = (size N : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)
  -- the pointwise split
  have hEnvpow : (0 : ℝ) ≤ Env N ^ (2 * p) := pow_nonneg (hEnv0 N) _
  have hcpow : (0 : ℝ) ≤ c ^ (2 * p) := pow_nonneg hc0.le _
  have hpt : ∀ ω, |Y N u ω| ^ (2 * p)
      ≤ c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : |Y N u ω| ^ (2 * p) ≤ Env N ^ (2 * p) :=
        pow_le_pow_left₀ (abs_nonneg _) (henv N u ω) _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |Y N u ω| ≤ c := not_lt.1 hω
      have h2 : |Y N u ω| ^ (2 * p) ≤ c ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) h1 _
      linarith
  have hRHSint : Integrable
      (fun ω => c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hSmeas)
  have hint : Integrable (fun ω => |Y N u ω| ^ (2 * p)) P :=
    integrable_abs_evenPow_of_envelope (hmeas N u) (henv N u) p
  have hle := integral_mono hint hRHSint hpt
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hSmeas), integral_const,
    integral_indicator_const _ hSmeas, smul_eq_mul, smul_eq_mul] at hle
  -- the main part is exactly `N^{εp} Φ^{2p}`
  have hmain : c ^ (2 * p) = (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    rw [hc_def, mul_pow, ← Real.rpow_natCast ((size N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 2
    rw [hτ_def]
    push_cast
    ring
  -- the exceptional part is negligible
  have hΦpow : (size N : ℝ) ^ (-(B * (2 * p))) ≤ Φ N u ^ (2 * p) := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (hΦN u) (2 * p)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast ((size N : ℝ) ^ (-B)) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have htail : P.real S * Env N ^ (2 * p) ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    have h1 : Env N ^ (2 * p) ≤ ((size N : ℝ) ^ Kenv) ^ (2 * p) :=
      pow_le_pow_left₀ (hEnv0 N) hEN _
    have h2 : ((size N : ℝ) ^ Kenv) ^ (2 * p) = (size N : ℝ) ^ (Kenv * (2 * p)) := by
      rw [← Real.rpow_natCast ((size N : ℝ) ^ Kenv) (2 * p), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    have hStep : P.real S * Env N ^ (2 * p) ≤
        (size N : ℝ) ^ (-D') * (size N : ℝ) ^ (Kenv * (2 * p)) := by
      refine mul_le_mul hPS (h2 ▸ h1) hEnvpow (Real.rpow_nonneg hNpos.le _)
    have hExp : (size N : ℝ) ^ (-D') * (size N : ℝ) ^ (Kenv * (2 * p))
        = (size N : ℝ) ^ (-(B * (2 * p)) + -1) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      rw [hD'_def]
      ring
    have hDrop : (size N : ℝ) ^ (-(B * (2 * p)) + -1) ≤ (size N : ℝ) ^ (-(B * (2 * p))) := by
      refine Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hεp : (1 : ℝ) ≤ (size N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hNge1 (mul_nonneg hε.le (Nat.cast_nonneg p))
    have hΦ2p : (0 : ℝ) ≤ Φ N u ^ (2 * p) := pow_nonneg (hΦ N u).le _
    calc P.real S * Env N ^ (2 * p) ≤ (size N : ℝ) ^ (-(B * (2 * p))) := by
          rw [hExp] at hStep; exact hStep.trans hDrop
      _ ≤ Φ N u ^ (2 * p) := hΦpow
      _ ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by nlinarith
  -- assemble
  have hmainpos : (0 : ℝ) ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (pow_nonneg (hΦ N u).le _)
  calc ∫ ω, |Y N u ω| ^ (2 * p) ∂P
      ≤ P.real Set.univ * c ^ (2 * p) + P.real S * Env N ^ (2 * p) := hle
    _ ≤ P.real Set.univ * ((size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))
        + (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
          rw [hmain]; linarith
    _ = (P.real Set.univ + 1) * ((size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by ring

/-- **The reverse bridge for a non-negative family.**  This is the shape in which the hypothesis
actually occurs in the paper's interfaces (`bdg`, `bdgQ`, …): what is dominated is already
non-negative, so `|Y| = Y`. -/
theorem momentDom_of_stochDom_of_nonneg {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hY0 : ∀ N (u : U N) (ω : Ω), 0 ≤ Y N u ω)
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), Y N u ω ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P Y (fun N u _ => Φ N u)) :
    MomentDom P Y Φ := by
  have habs : (fun N (u : U N) (ω : Ω) => |Y N u ω|) = Y := by
    funext N u ω; exact abs_of_nonneg (hY0 N u ω)
  refine momentDom_of_stochDom hmeas hΦ hB hΦlow hEnv0 hKenv ?_ hEnvpoly ?_
  · intro N u ω; rw [abs_of_nonneg (hY0 N u ω)]; exact henv N u ω
  · rw [habs]; exact hdom

/-- **The reverse bridge for `RBM.NormStochDom`** (Definition 2.1 (iii)): `‖A‖ ≺ Φ` plus a
deterministic envelope for `‖A‖` gives moment bounds for `‖A‖`. -/
theorem momentDom_of_normStochDom {U : ℕ → Type*} {V : Type*} [NormedAddCommGroup V]
    {A : ∀ N, U N → Ω → V} {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable fun ω => ‖A N u ω‖)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), ‖A N u ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : NormStochDom P A (fun N u _ => Φ N u)) :
    MomentDom P (fun N u ω => ‖A N u ω‖) Φ :=
  momentDom_of_stochDom_of_nonneg (fun _ _ _ => norm_nonneg _) hmeas hΦ hB hΦlow hEnv0 hKenv
    henv hEnvpoly hdom

open scoped Matrix.Norms.L2Operator

/-- The reverse bridge for Green functions, with the exceptional-event envelope discharged
by the whole-space resolvent bound `norm_green_le`. The lower bound on `η` is kept as an
explicit polynomial hypothesis. -/
theorem momentDom_green_of_stochDom {U : ℕ → Type*} {n : ℕ → Type*}
    [∀ N, Fintype (n N)] [∀ N, DecidableEq (n N)]
    (H : ∀ N, U N → Ω → Matrix (n N) (n N) ℂ)
    (z : ∀ N, U N → ℂ) (η : ℕ → ℝ)
    {Φ : ∀ N, U N → ℝ} {Kenv B : ℝ}
    (hH : ∀ N (u : U N) ω, (H N u ω).IsHermitian)
    (hη : ∀ N, 0 < η N) (hz : ∀ N (u : U N), η N ≤ |(z N u).im|)
    (hmeas : ∀ N (u : U N), Measurable fun ω => ‖green (H N u ω) (z N u)‖)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hKenv : 0 ≤ Kenv)
    (hηpoly : ∀ᶠ N : ℕ in atTop, (η N)⁻¹ ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P (fun N u ω => ‖green (H N u ω) (z N u)‖)
      (fun N u _ => Φ N u)) :
    MomentDom P (fun N u ω => ‖green (H N u ω) (z N u)‖) Φ := by
  apply momentDom_of_stochDom_of_nonneg (fun _ _ _ => norm_nonneg _) hmeas hΦ hB hΦlow
    (fun N => inv_nonneg.mpr (hη N).le) hKenv
    (fun N u ω => norm_green_le (hH N u ω) (hη N) (hz N u)) hηpoly hdom

/-- A positive nonzero family satisfies the reverse bridge hypotheses. -/
theorem momentDom_reverse_positive_example :
    MomentDom (Measure.dirac ()) (U := fun _ => Unit)
      (fun _ _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  apply momentDom_of_stochDom (Env := fun _ => 1) (Kenv := 0) (B := 0)
  · intro N u
    exact measurable_const
  · intro N u
    exact one_pos
  · norm_num
  · exact Eventually.of_forall fun N u => by simp
  · intro N
    norm_num
  · norm_num
  · intro N u ω
    norm_num
  · exact Eventually.of_forall fun N => by simp
  · have hdom : StochDom (Measure.dirac ())
        (fun _ (_ : Unit) (_ : Unit) => (1 : ℝ))
        (fun _ (_ : Unit) (_ : Unit) => (1 : ℝ)) :=
      StochDom.refl (fun _ _ _ => zero_le_one)
    simpa only [abs_one] using hdom

end Reverse

end RBM.Gauss
