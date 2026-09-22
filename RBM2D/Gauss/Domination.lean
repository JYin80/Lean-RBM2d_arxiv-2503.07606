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
two-dimensional random band matrix paper, together with its time-net argument.

This file is the bridge between the **moment route** for the random layer (the flow is
`H_u := √u • X` and all bounds are proved for moments, never for paths) and the paper's
stochastic domination `≺` (`RBM.StochDom`, `RBM2D/Defs/StochDom.lean`).

## The two steps

1. **Moments ⟹ `≺`** (Markov / Chebyshev).  `RBM.Gauss.MomentDom P Y Φ` is the moment input
   ```
   ∀ ε > 0, ∀ p : ℕ, ∃ C > 0, eventually in N, ∀ u,   E |Y(N,u)|^{2p} ≤ C N^{εp} Φ(N,u)^{2p}.
   ```
   The order of the quantifiers matters: `ε` is **outside** `p`, so `ε` may be taken arbitrarily
   small for each fixed `p`; this is exactly what is needed to beat the `N^τ` of Definition
   2.1 (i).  `RBM.Gauss.stochDom_of_momentDom` turns this, together with a polynomial bound on
   `#U(N)`, into `RBM.StochDom P Y Φ`; `RBM.Gauss.stochDom_one_of_momentDom` is the case `Φ = 1`.

2. **`≺` uniformly in a continuous time parameter `u ∈ [0, T]`.**  Definition 2.1 (i) puts an
   *uncountable* union inside the probability.  `RBM.Gauss.stochDom_Icc_of_holder` removes it
   by a polynomial net: `⌈N^A⌉₊ + 1` subintervals of `[0, T]` with `A := (K + B + 1)/γ`,
   where `N^K |u − u'|^γ` is a modulus of continuity on a high-probability event and
   `N^{-B}` a lower bound for the control `Φ(N)`.  On the net one uses step 1 and the union
   bound `RBM.StochDom.of_forall_le`; between net points the modulus moves the failure event by
   at most `N^{τ/2} Φ(N)`, which is absorbed in the `N^τ` of Definition 2.1 (i).

The good-event version is needed for `H_u = √u • X`, since its modulus includes the unbounded
factor `‖X‖`. A deterministic-modulus theorem is also provided as a special case. The exponent
`γ` accommodates the `1/2`-Hölder behavior of `√u` at `u = 0`.

## Main definitions

* `RBM.Gauss.MomentDom P Y Φ` — the moment input of step 1.
* `RBM.Gauss.netSize`, `RBM.Gauss.netPt` — the uniform net on `[0, T]` of step 2.

## Main results

* `RBM.Gauss.meas_gt_le_of_moment` — Markov/Chebyshev at a single scale.
* `RBM.Gauss.stochDom_of_momentDom` — moments `⟹ ≺`, relative to a deterministic control `Φ`.
* `RBM.Gauss.stochDom_one_of_momentDom` — the case `Φ = 1`, i.e. `Y ≺ 1`.
* `RBM.Gauss.stochDom_Icc_of_holder` — `≺` uniformly in `u ∈ [0, T]`, with the uncountable
  union of Definition 2.1 (i) intact; `RBM.Gauss.stochDom_Icc_of_lipschitz` is the case `γ = 1`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Step 1: Markov's inequality -/

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

/-- **The moment input.**  For every `ε > 0` and every `p`, the `2p`-th moment of `Y(N,u)` is
bounded by `C_{ε,p} · N^{εp} · Φ(N,u)^{2p}`, eventually in `N` and uniformly in `u ∈ U(N)`.

`ε` is quantified *outside* `p`, so it may be taken arbitrarily small for each fixed `p`; this is
what makes `RBM.Gauss.stochDom_of_momentDom` work for every `τ > 0`. -/
def MomentDom {U : ℕ → Type*} (Y : ∀ N, U N → Ω → ℝ) (Φ : ∀ N, U N → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u,
    ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))

variable {P}

/-- **Moments imply stochastic domination.**  If all moments of `Y` are bounded relative to a
positive deterministic control `Φ` in the sense of `MomentDom`, and `#U(N)` is polynomially
bounded, then `Y ≺ Φ` in the sense of Definition 2.1 (i). -/
theorem stochDom_of_momentDom {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ} (hΦ : ∀ N u, 0 < Φ N u)
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P Y Φ) :
    StochDom P Y (fun N u _ => Φ N u) := by
  refine StochDom.of_forall_le hcard ?_
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + 1) / τ)
  have hDp : D + 1 ≤ τ * (p : ℝ) := by
    rw [div_le_iff₀ hτ] at hp; linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - D := by linarith
  filter_upwards [hCN, eventually_ge_atTop 1, eventually_le_rpow C hexp] with N hN hN1 hCle u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hΦu := hΦ N u
  have hrp : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have ht : 0 < (N : ℝ) ^ τ * Φ N u := mul_pos hrp hΦu
  refine (meas_gt_le_of_moment P ht (hint p N u) (hN u)).trans (ENNReal.ofReal_le_ofReal ?_)
  set a : ℝ := (N : ℝ) ^ (τ * (p : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hb : (0 : ℝ) < Φ N u ^ (2 * p) := by positivity
  have h1 : ((N : ℝ) ^ τ * Φ N u) ^ (2 * p) = a * a * Φ N u ^ (2 * p) := by
    rw [mul_pow, ha_def, ← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le,
      ← Real.rpow_add hNpos]
    push_cast
    ring_nf
  have h2 : C * (a * Φ N u ^ (2 * p)) / (a * a * Φ N u ^ (2 * p)) = C * a⁻¹ := by
    field_simp
  have h3 : a⁻¹ = (N : ℝ) ^ (-(τ * (p : ℝ))) := by
    rw [ha_def, Real.rpow_neg hNpos.le]
  rw [h1, h2]
  calc C * a⁻¹ ≤ (N : ℝ) ^ (τ * (p : ℝ) - D) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
    _ = (N : ℝ) ^ (-D) := by
        rw [h3, ← Real.rpow_add hNpos]
        congr 1
        ring_nf

/-- **Moments imply `Y ≺ 1`**: the case `Φ = 1` of `stochDom_of_momentDom`. -/
theorem stochDom_one_of_momentDom {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Y : ∀ N, U N → Ω → ℝ}
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u,
      ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * (N : ℝ) ^ (ε * p)) :
    StochDom P Y (fun _ _ _ => (1 : ℝ)) := by
  refine stochDom_of_momentDom hcard (Φ := fun _ _ => (1 : ℝ)) (fun _ _ => one_pos) hint ?_
  intro ε hε p
  obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hCN] with N hN u
  simpa using hN u

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

/-! ### Step 2: the time net -/

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

/-! ### Step 2: `≺` uniformly in a continuous time parameter -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- **Definition 2.1 (i) with the uncountable union intact.**

Let `Y(N, u, ω)` be defined for `u` in the interval `[0, T]`, let `Φ(N) > 0` be a deterministic
control that is not super-polynomially small (`N^{-B} ≤ Φ(N)` eventually), and assume

* a modulus of continuity
  `|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K |u − u'|^γ` on a high-probability event;
* the moment bound `MomentDom` relative to `Φ`, uniformly in `u ∈ [0, T]`.

Then `Y ≺ Φ` in the sense of Definition 2.1 (i), i.e. the *union over all* `u ∈ [0, T]` of the
failure events has probability `≤ N^{-D}`.

The proof uses `⌈N^{(K+B+1)/γ}⌉₊ + 1` subintervals, `stochDom_of_momentDom` plus
the union bound `RBM.StochDom.of_forall_le` on the net, and the modulus of continuity in between.

The Hölder exponent `γ` accommodates `H_u = √u • X` at `u = 0`, once a high-probability
polynomial bound on `‖X‖` supplies the modulus. -/
theorem stochDom_Icc_of_holder_on_good {T : ℝ} (hT : 0 < T)
    {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ (N : ℕ) (ω : Ω), ω ∈ Ξ N →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net
  have hnet : StochDom P (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω => Y N (netPt T A N k) ω)
      (fun N _ _ => Φ N) := by
    refine stochDom_of_momentDom (card_net_le hA) (Φ := fun N _ => Φ N) (fun N _ => hΦ N)
      (fun p N k => hint p N _) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hCN] with N hN k
    exact hN ⟨netPt T A N k, netPt_mem_Icc hT.le A N k⟩
  -- step 2: transfer from the net to the whole interval
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  have hsub : ∀ᶠ N : ℕ in atTop,
      badSet (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω)
        (fun N _ _ => Φ N) τ N ⊆
      badSet (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω => Y N (netPt T A N k) ω)
        (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ := by
    filter_upwards [hΦlow, eventually_ge_atTop 1, eventually_le_rpow 2 hτ2,
      eventually_le_rpow (T ^ γ) one_pos] with N hΦN hN1 hN2 hNT
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hTN : T ^ γ ≤ (N : ℝ) := by rwa [Real.rpow_one] at hNT
    have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
    have hmge : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := rpow_le_netSize A N
    have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
    have hr2 : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    -- the net error is at most `N^{τ/2} Φ(N)`
    have herr : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
      have hstep1 : T / (netSize A N : ℝ) ≤ T / (N : ℝ) ^ A :=
        div_le_div_of_nonneg_left hT.le hNA hmge
      have hstep1' : (T / (netSize A N : ℝ)) ^ γ ≤ (T / (N : ℝ) ^ A) ^ γ :=
        Real.rpow_le_rpow (div_pos hT hm).le hstep1 hγ.le
      have hKpos : (0 : ℝ) < (N : ℝ) ^ K := Real.rpow_pos_of_pos hNpos K
      have hstep2 : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ
          ≤ (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ :=
        mul_le_mul_of_nonneg_left hstep1' hKpos.le
      have hpowA : ((N : ℝ) ^ A) ^ γ = (N : ℝ) ^ (K + B + 1) := by
        rw [← Real.rpow_mul hNpos.le, hAγ]
      have hdiv : (T / (N : ℝ) ^ A) ^ γ = T ^ γ / (N : ℝ) ^ (K + B + 1) := by
        rw [Real.div_rpow hT.le hNA.le, hpowA]
      have hexp : K - (K + B + 1) = -B + -1 := by ring
      have hKA : (N : ℝ) ^ K / (N : ℝ) ^ (K + B + 1) = (N : ℝ) ^ (-B) * (N : ℝ)⁻¹ := by
        rw [← Real.rpow_sub hNpos, ← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hNpos, hexp]
      have hstep3 : (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ
          = T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) := by
        rw [hdiv, ← hKA]; ring
      have hinvn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      have hstep4 : T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) ≤ T ^ γ * (Φ N * (N : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦN hinvn) hTγ.le
      have hstep5 : T ^ γ * (Φ N * (N : ℝ)⁻¹) ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
        have hTinv : T ^ γ * (N : ℝ)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
        have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hNge1 hτ2.le
        have heq : T ^ γ * (Φ N * (N : ℝ)⁻¹) = (T ^ γ * (N : ℝ)⁻¹) * Φ N := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hTinv.trans h1) (hΦ N).le
      linarith
    -- and `N^τ ≥ 2 N^{τ/2}`
    have hdouble : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
      have heq := UnifDetDom.rpow_half_mul_rpow_half N hτ
      nlinarith [hr2.le]
    rintro ω ⟨u, hu⟩
    by_cases hω : ω ∈ Ξ N
    swap
    · exact Or.inr hω
    refine Or.inl ?_
    obtain ⟨k, hk⟩ := exists_netPt_close hT A N u.2
    refine ⟨k, ?_⟩
    have hhol := hHol N ω hω u.1 u.2 (netPt T A N k) (netPt_mem_Icc hT.le A N k)
    have hle : |Y N u.1 ω - Y N (netPt T A N k) ω| ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
      refine hhol.trans (le_trans ?_ herr)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
        (Real.rpow_pos_of_pos hNpos K).le
    have hdiff : Y N u.1 ω - Y N (netPt T A N k) ω ≤ (N : ℝ) ^ (τ / 2) * Φ N :=
      (le_abs_self _).trans hle
    have hmul : 2 * (N : ℝ) ^ (τ / 2) * Φ N ≤ (N : ℝ) ^ τ * Φ N :=
      mul_le_mul_of_nonneg_right hdouble (hΦ N).le
    simp only
    linarith
  filter_upwards [hsub, hnet (τ / 2) hτ2 (D + 1) (by linarith),
    hΞ (D + 1) (by linarith), eventually_two_mul_rpow_le D] with N h1 h2 h3 h4
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (badSet (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
        (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) τ N)
      ≤ P (badSet (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω =>
          Y N (netPt T A N k) ω) (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ) :=
        measure_mono h1
    _ ≤ P (badSet (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω =>
          Y N (netPt T A N k) ω) (fun N _ _ => Φ N) (τ / 2) N) + P (Ξ N)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := add_le_add h2 h3
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h4

/-- High probability measured against the physical dimension along an admissible sequence. -/
def HighProbAt (P : Measure Ω) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω) : Prop :=
  ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (Ξ l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))

/-- The whole sample space is a valid good event at every physical dimension. -/
theorem highProbAt_univ (P : Measure Ω) (size : ℕ → ℕ) :
    HighProbAt P size (fun _ => Set.univ) := by
  intro D _
  exact Eventually.of_forall fun _ => by simp

/-- The time-net bridge along admissible matrix dimensions. On the good event the modulus
is deterministic; its complement has super-polynomially small probability in `size l`. -/
theorem stochDomAt_Icc_of_holder_on_good (size : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop) {T : ℝ} (hT : 0 < T)
    {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (size N : ℝ) ^ (-B) ≤ Φ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ)
    (hHol : ∀ (N : ℕ) (ω : Ω), ω ∈ Ξ N →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (size N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDomAt P size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net
  have hnet : StochDomAt P size
      (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
        Y N (netPt T A (size N) k) ω)
      (fun N _ _ => Φ N) := by
    refine stochDomAt_of_momentDomAt size hsize
      (hsize.eventually (card_net_le hA)) (Φ := fun N _ => Φ N) (fun N _ => hΦ N)
      (fun p N k => hint p N _) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hCN] with N hN k
    exact hN ⟨netPt T A (size N) k, netPt_mem_Icc hT.le A (size N) k⟩
  -- step 2: transfer from the net to the whole interval
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  have hsub : ∀ᶠ N : ℕ in atTop,
      badSetAt size (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω)
        (fun N _ _ => Φ N) τ N ⊆
      badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω)
        (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ := by
    filter_upwards [hΦlow, hsize.eventually (eventually_ge_atTop 1),
      hsize.eventually (eventually_le_rpow 2 hτ2),
      hsize.eventually (eventually_le_rpow (T ^ γ) one_pos)] with N hΦN hN1 hN2 hNT
    have hNpos : (0 : ℝ) < size N := by exact_mod_cast hN1
    have hNge1 : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
    have hTN : T ^ γ ≤ (size N : ℝ) := by rwa [Real.rpow_one] at hNT
    have hm : (0 : ℝ) < (netSize A (size N) : ℝ) := by exact_mod_cast netSize_pos A (size N)
    have hmge : (size N : ℝ) ^ A ≤ (netSize A (size N) : ℝ) := rpow_le_netSize A (size N)
    have hNA : (0 : ℝ) < (size N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
    have hr2 : (0 : ℝ) < (size N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    -- the net error is at most `N^{τ/2} Φ(N)`
    have herr : (size N : ℝ) ^ K * (T / (netSize A (size N) : ℝ)) ^ γ ≤
        (size N : ℝ) ^ (τ / 2) * Φ N := by
      have hstep1 : T / (netSize A (size N) : ℝ) ≤ T / (size N : ℝ) ^ A :=
        div_le_div_of_nonneg_left hT.le hNA hmge
      have hstep1' : (T / (netSize A (size N) : ℝ)) ^ γ ≤ (T / (size N : ℝ) ^ A) ^ γ :=
        Real.rpow_le_rpow (div_pos hT hm).le hstep1 hγ.le
      have hKpos : (0 : ℝ) < (size N : ℝ) ^ K := Real.rpow_pos_of_pos hNpos K
      have hstep2 : (size N : ℝ) ^ K * (T / (netSize A (size N) : ℝ)) ^ γ
          ≤ (size N : ℝ) ^ K * (T / (size N : ℝ) ^ A) ^ γ :=
        mul_le_mul_of_nonneg_left hstep1' hKpos.le
      have hpowA : ((size N : ℝ) ^ A) ^ γ = (size N : ℝ) ^ (K + B + 1) := by
        rw [← Real.rpow_mul hNpos.le, hAγ]
      have hdiv : (T / (size N : ℝ) ^ A) ^ γ = T ^ γ / (size N : ℝ) ^ (K + B + 1) := by
        rw [Real.div_rpow hT.le hNA.le, hpowA]
      have hexp : K - (K + B + 1) = -B + -1 := by ring
      have hKA : (size N : ℝ) ^ K / (size N : ℝ) ^ (K + B + 1) =
          (size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹ := by
        rw [← Real.rpow_sub hNpos, ← Real.rpow_neg_one (size N : ℝ), ← Real.rpow_add hNpos, hexp]
      have hstep3 : (size N : ℝ) ^ K * (T / (size N : ℝ) ^ A) ^ γ
          = T ^ γ * ((size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹) := by
        rw [hdiv, ← hKA]; ring
      have hinvn : (0 : ℝ) ≤ (size N : ℝ)⁻¹ := by positivity
      have hstep4 : T ^ γ * ((size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹) ≤
          T ^ γ * (Φ N * (size N : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦN hinvn) hTγ.le
      have hstep5 : T ^ γ * (Φ N * (size N : ℝ)⁻¹) ≤ (size N : ℝ) ^ (τ / 2) * Φ N := by
        have hTinv : T ^ γ * (size N : ℝ)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
        have h1 : (1 : ℝ) ≤ (size N : ℝ) ^ (τ / 2) := Real.one_le_rpow hNge1 hτ2.le
        have heq : T ^ γ * (Φ N * (size N : ℝ)⁻¹) = (T ^ γ * (size N : ℝ)⁻¹) * Φ N := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hTinv.trans h1) (hΦ N).le
      linarith
    -- and `N^τ ≥ 2 N^{τ/2}`
    have hdouble : 2 * (size N : ℝ) ^ (τ / 2) ≤ (size N : ℝ) ^ τ := by
      have heq := UnifDetDom.rpow_half_mul_rpow_half (size N) hτ
      nlinarith [hr2.le]
    rintro ω ⟨u, hu⟩
    by_cases hω : ω ∈ Ξ N
    swap
    · exact Or.inr hω
    refine Or.inl ?_
    obtain ⟨k, hk⟩ := exists_netPt_close hT A (size N) u.2
    refine ⟨k, ?_⟩
    have hhol := hHol N ω hω u.1 u.2 (netPt T A (size N) k) (netPt_mem_Icc hT.le A (size N) k)
    have hle : |Y N u.1 ω - Y N (netPt T A (size N) k) ω| ≤ (size N : ℝ) ^ (τ / 2) * Φ N := by
      refine hhol.trans (le_trans ?_ herr)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
        (Real.rpow_pos_of_pos hNpos K).le
    have hdiff : Y N u.1 ω - Y N (netPt T A (size N) k) ω ≤ (size N : ℝ) ^ (τ / 2) * Φ N :=
      (le_abs_self _).trans hle
    have hmul : 2 * (size N : ℝ) ^ (τ / 2) * Φ N ≤ (size N : ℝ) ^ τ * Φ N :=
      mul_le_mul_of_nonneg_right hdouble (hΦ N).le
    simp only
    linarith
  filter_upwards [hsub, hnet (τ / 2) hτ2 (D + 1) (by linarith),
    hΞ (D + 1) (by linarith), hsize.eventually (eventually_two_mul_rpow_le D)] with N h1 h2 h3 h4
  have hp : (0 : ℝ) ≤ (size N : ℝ) ^ (-(D + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg (size N)) _
  calc P (badSetAt size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
        (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) τ N)
      ≤ P (badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω) (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ) :=
        measure_mono h1
    _ ≤ P (badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω) (fun N _ _ => Φ N) (τ / 2) N) + P (Ξ N)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size N : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size N : ℝ) ^ (-(D + 1))) := add_le_add h2 h3
    _ = ENNReal.ofReal (2 * (size N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h4

/-- Deterministic-modulus specialization of the good-event time-net theorem. -/
theorem stochDom_Icc_of_holder {T : ℝ} (hT : 0 < T) {K B γ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    (hHol : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T,
      ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  apply stochDom_Icc_of_holder_on_good hT hK hB hγ hΦ hΦlow
    (Ξ := fun _ => Set.univ)
    (HighProb.of_eventually_univ (Eventually.of_forall fun _ _ => Set.mem_univ _))
  · intro N ω _ u hu u' hu'
    exact hHol N ω u hu u' hu'
  · exact hint
  · exact hmom

/-- **Definition 2.1 (i) with the uncountable union intact**, Lipschitz case: `γ = 1` of
`stochDom_Icc_of_holder`. -/
theorem stochDom_Icc_of_lipschitz {T : ℝ} (hT : 0 < T) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    (hLip : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'|)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) :=
  stochDom_Icc_of_holder hT hK hB one_pos hΦ hΦlow
    (fun N ω u hu u' hu' => by simpa [Real.rpow_one] using hLip N ω u hu u' hu') hint hmom

end Uniform

/-- The moment hypothesis is satisfiable with a positive, nonzero observable and control. -/
theorem momentDom_constant_one_example :
    MomentDom (Measure.dirac ()) (U := fun _ => Unit)
      (fun _ _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro ε hε p
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN u
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 ≤ ε * (p : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1 hp
  simpa using hpow

/-- A positive nonzero instance of the admissible-size moment hypothesis. -/
theorem momentDomAt_constant_one_example :
    MomentDomAt (Measure.dirac ()) (fun l => l + 1) (U := fun _ => Unit)
      (fun _ _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro ε hε p
  refine ⟨1, one_pos, ?_⟩
  exact Eventually.of_forall fun l u => by
    have hsize : (1 : ℝ) ≤ (l + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)
    have hp : 0 ≤ ε * (p : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    have hpow : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hsize hp
    simpa using hpow

end RBM.Gauss
