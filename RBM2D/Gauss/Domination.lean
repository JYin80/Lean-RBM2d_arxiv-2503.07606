/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.StochDom
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# From moment bounds to stochastic domination, and the time net

The dimension-independent moment-to-domination bridge for Definition 2.1 (i) of the
two-dimensional random band matrix paper, together with the time net used for uniformity in a
continuous time parameter.

The random layer is treated by the moment method: the flow is `H_u := √u • X` and all bounds are
proved for moments, never for paths.  The paper's stochastic domination `≺` is `RBM.StochDomAt`
(`RBM2D/Defs/StochDom.lean`), measured against the physical matrix dimension `size l`.

## Moments ⟹ `≺`

Markov / Chebyshev.  `RBM.Gauss.MomentDomAt P size Y Φ` is the moment input
```
∀ ε > 0, ∀ p : ℕ, ∃ C > 0, eventually in l, ∀ u,   E |Y l u|^{2p} ≤ C size(l)^{εp} Φ(l,u)^{2p}.
```
The order of the quantifiers matters: `ε` is **outside** `p`, so `ε` may be taken arbitrarily
small for each fixed `p`; this is exactly what is needed to beat the `N^τ` of Definition 2.1 (i).
`RBM.Gauss.stochDomAt_of_momentDomAt` turns this, together with a polynomial bound on the
cardinality of the parameter set, into `RBM.StochDomAt P size Y Φ`.

## The time net

For a continuous parameter `u ∈ [0, T]`, Definition 2.1 (i) puts an *uncountable* union inside
the probability.  It is removed by a polynomial net: `⌈N^A⌉₊ + 1` subintervals of `[0, T]`.

## Main definitions and results

* `RBM.Gauss.meas_gt_le_of_moment` — Markov/Chebyshev at a single scale.
* `RBM.Gauss.MomentDomAt` — the moment input.
* `RBM.Gauss.stochDomAt_of_momentDomAt` — moments `⟹ ≺`, along admissible dimensions `size l`.
* `RBM.Gauss.netSize`, `RBM.Gauss.netPt`, `RBM.Gauss.exists_netPt_close`,
  `RBM.Gauss.card_net_le` — the uniform net on `[0, T]`.
* `RBM.Gauss.HighProbAt`, `RBM.Gauss.highProbAt_univ` — high probability along an admissible
  sequence.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Markov's inequality -/

section Markov

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- **Markov / Chebyshev at a single scale.**  A bound `M` on the `2p`-th moment of `Y` gives
`P(Y > t) ≤ M / t^{2p}` for every threshold `t > 0`. -/
theorem meas_gt_le_of_moment {Y : Ω → ℝ} {p : ℕ} {t M : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hM : ∫ ω, |Y ω| ^ (2 * p) ∂P ≤ M) :
    P {ω | t < Y ω} ≤ ENNReal.ofReal (M / t ^ (2 * p)) := by
  have hnn : 0 ≤ᵐ[P] fun ω => |Y ω| ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have htp : (0 : ℝ) < t ^ (2 * p) := by positivity
  -- the failure event sits inside the level set of the `2p`-th power
  have hsub : {ω | t < Y ω} ⊆ {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact pow_le_pow_left₀ ht.le ((le_abs_self (Y ω)).trans' hω.le) _
  -- Markov
  have hmark := mul_meas_ge_le_integral_of_nonneg hnn hint (t ^ (2 * p))
  have hreal : P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} ≤ M / t ^ (2 * p) := by
    rw [le_div_iff₀ htp, mul_comm]
    exact hmark.trans hM
  calc P {ω | t < Y ω} ≤ P {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
    _ ≤ ENNReal.ofReal (M / t ^ (2 * p)) := ENNReal.ofReal_le_ofReal hreal

variable {P}

/-- The moment hypothesis along an admissible sequence with physical matrix dimension
`size l`. The size, not the sequence index `l`, appears in every power. -/
def MomentDomAt (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type*}
    (Y : ∀ l, U l → Ω → ℝ) (Φ : ∀ l, U l → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u,
    ∫ ω, |Y l u ω| ^ (2 * p) ∂P ≤
      C * ((size l : ℝ) ^ (ε * p) * Φ l u ^ (2 * p))

/-- Moments imply stochastic domination along admissible dimensions. Both the parameter
cardinality and the threshold are measured against `size l`; the measure `P` is common to the
whole sequence. -/
theorem stochDomAt_of_momentDomAt {U : ℕ → Type*} [∀ l, Fintype (U l)]
    (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
    {Ccard : ℝ}
    (hcard : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ Ccard)
    {Y : ∀ l, U l → Ω → ℝ} {Φ : ∀ l, U l → ℝ}
    (hΦ : ∀ l u, 0 < Φ l u)
    (hint : ∀ (p l : ℕ) (u : U l), Integrable (fun ω => |Y l u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size Y Φ) :
    StochDomAt P size Y (fun l u _ => Φ l u) := by
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + Ccard + 1) / τ)
  have hDp : D + Ccard + 1 ≤ τ * (p : ℝ) := by
    rw [div_le_iff₀ hτ] at hp
    linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - (D + Ccard) := by linarith
  filter_upwards [hcard, hCN, hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow C hexp)] with l hcardl hNl hsize1 hCle
  have hNpos : (0 : ℝ) < size l := by exact_mod_cast hsize1
  have hNge1 : (1 : ℝ) ≤ size l := by exact_mod_cast hsize1
  have hsingle (u : U l) :
      P {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} ≤
        ENNReal.ofReal ((size l : ℝ) ^ (-(D + Ccard))) := by
    have hΦu := hΦ l u
    have ht : 0 < (size l : ℝ) ^ τ * Φ l u :=
      mul_pos (Real.rpow_pos_of_pos hNpos τ) hΦu
    refine (meas_gt_le_of_moment P ht (hint p l u) (hNl u)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    set a : ℝ := (size l : ℝ) ^ (τ * (p : ℝ)) with ha_def
    have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
    have hb : (0 : ℝ) < Φ l u ^ (2 * p) := by positivity
    have h1 : ((size l : ℝ) ^ τ * Φ l u) ^ (2 * p) =
        a * a * Φ l u ^ (2 * p) := by
      rw [mul_pow, ha_def, ← Real.rpow_natCast ((size l : ℝ) ^ τ) (2 * p),
        ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      push_cast
      ring_nf
    have h2 : C * (a * Φ l u ^ (2 * p)) /
        (a * a * Φ l u ^ (2 * p)) = C * a⁻¹ := by
      field_simp
    have h3 : a⁻¹ = (size l : ℝ) ^ (-(τ * (p : ℝ))) := by
      rw [ha_def, Real.rpow_neg hNpos.le]
    rw [h1, h2]
    calc C * a⁻¹ ≤ (size l : ℝ) ^ (τ * (p : ℝ) - (D + Ccard)) * a⁻¹ :=
          mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
      _ = (size l : ℝ) ^ (-(D + Ccard)) := by
          rw [h3, ← Real.rpow_add hNpos]
          congr 1
          ring
  have hp' : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + Ccard)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hset : badSetAt size Y (fun l u _ => Φ l u) τ l =
      ⋃ u, {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} := by
    ext ω
    simp [badSetAt]
  calc P (badSetAt size Y (fun l u _ => Φ l u) τ l)
      ≤ ∑ u : U l, P {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} := by
        rw [hset]
        exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _u : U l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + Ccard))) :=
        Finset.sum_le_sum fun u _ => hsingle u
    _ = ENNReal.ofReal (Fintype.card (U l) *
          (size l : ℝ) ^ (-(D + Ccard))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ Ccard *
          (size l : ℝ) ^ (-(D + Ccard))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcardl hp')
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring_nf

end Markov

/-! ### The time net -/

section Net

/-- The number of subintervals of the time net on `[0, T]`: `⌈N^A⌉₊ + 1` (the `+1` keeps it
positive for every `N` and every `A`). -/
noncomputable def netSize (A : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) ^ A⌉₊ + 1

theorem netSize_pos (A : ℝ) (N : ℕ) : 0 < netSize A N := Nat.succ_pos _

theorem rpow_le_netSize (A : ℝ) (N : ℕ) : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := by
  have := Nat.le_ceil ((N : ℝ) ^ A)
  have h : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) ≤ (netSize A N : ℝ) := by
    unfold netSize; push_cast; linarith
  linarith

/-- The `k`-th point `k T / m` of the uniform net with `m = netSize A N` subintervals
on `[0, T]`. -/
noncomputable def netPt (T A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  (k : ℝ) * T / (netSize A N : ℝ)

theorem netPt_mem_Icc {T : ℝ} (hT : 0 ≤ T) (A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) :
    netPt T A N k ∈ Set.Icc (0 : ℝ) T := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hk : (k : ℝ) ≤ (netSize A N : ℝ) := by
    have : (k : ℕ) ≤ netSize A N := Nat.lt_succ_iff.1 k.isLt
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  constructor
  · simp only [netPt]
    exact div_nonneg (mul_nonneg hk0 hT) hm.le
  · simp only [netPt]
    rw [div_le_iff₀ hm]
    nlinarith

/-- Every point of `[0, T]` is within `T / netSize A N` of a net point. -/
theorem exists_netPt_close {T : ℝ} (hT : 0 < T) (A : ℝ) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) :
    ∃ k : Fin (netSize A N + 1), |u - netPt T A N k| ≤ T / (netSize A N : ℝ) := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hx0 : 0 ≤ u * (netSize A N : ℝ) / T := div_nonneg (mul_nonneg hu.1 hm.le) hT.le
  have hxm : u * (netSize A N : ℝ) / T ≤ (netSize A N : ℝ) := by
    rw [div_le_iff₀ hT]
    nlinarith [hu.2, hm.le]
  have hkm : ⌊u * (netSize A N : ℝ) / T⌋₊ ≤ netSize A N := Nat.floor_le_of_le hxm
  have hfl : ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) ≤ u * (netSize A N : ℝ) / T :=
    Nat.floor_le hx0
  have hfu : u * (netSize A N : ℝ) / T < ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩, ?_⟩
  have hnet : netPt T A N ⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩
      = ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := rfl
  have hkey : (u * (netSize A N : ℝ) / T - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ))
      * (T / (netSize A N : ℝ))
      = u - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := by
    field_simp
  rw [hnet, ← hkey,
    abs_of_nonneg (mul_nonneg (by linarith) (div_pos hT hm).le)]
  exact mul_le_of_le_one_left (div_pos hT hm).le (by linarith)

theorem card_net_le {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (Fin (netSize A N + 1)) : ℝ) ≤ (N : ℝ) ^ (A + 1) := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ A := Real.one_le_rpow hN1 hA
  have hceil : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) < (N : ℝ) ^ A + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcard : (Fintype.card (Fin (netSize A N + 1)) : ℝ) = (⌈(N : ℝ) ^ A⌉₊ : ℝ) + 2 := by
    rw [Fintype.card_fin, netSize]; push_cast; ring
  have hrpow : (N : ℝ) ^ (A + 1) = (N : ℝ) ^ A * (N : ℝ) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  rw [hcard, hrpow]
  nlinarith

end Net

/-! ### High probability along an admissible sequence -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- High probability measured against the physical dimension along an admissible sequence. -/
def HighProbAt (P : Measure Ω) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω) : Prop :=
  ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (Ξ l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

/-- The whole sample space is a valid good event at every physical dimension. -/
theorem highProbAt_univ (P : Measure Ω) (size : ℕ → ℕ) :
    HighProbAt P size (fun _ => Set.univ) := by
  intro D _
  exact Eventually.of_forall fun _ => by simp

end Uniform

end RBM.Gauss
