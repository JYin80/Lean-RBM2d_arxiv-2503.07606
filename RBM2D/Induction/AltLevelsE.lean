/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEnd
import RBM2D.Induction.AltDriftQ
import RBM2D.Induction.AltLevelsQ0
import RBM2D.Induction.AltLevelsQ
import RBM2D.Induction.AltBudget
import RBM2D.Induction.AltAbsorb
import RBM2D.Induction.DecayLoop
import RBM2D.Induction.KcalDecay

/-!
# The hypothesis `AltLevelsE`, the packaging of `AltLevelsQ`, `altGridEnd` and `stoeqTargetV2`

Contents:

1. `altLevelsE : AltLevelsE d κ c τ C E s t` (the `𝔼` levels and window decay of the alternating
   `𝒬`-process, `int_K-L+QE`, from the `ℚ` levels `altLevelsQ0`, `altLevelsQm`);
2. `altLevelsQ_of_parts` (the two parts give `AltLevelsQ`);
3. `altGridEnd : AltGridEnd d κ c τ C E s t` (`altGridEnd_of_pins` with the four proved
   hypotheses);
4. `stoeqTargetV2 : STOeqTargetV2 d κ c τ C E s t` (`stoeqTargetV2_of_gridEnds` with `altLocalForm`,
   `altExpSymm`, `nonAltGridEnd`, `altGridEnd`).

Proof of item 1 (`≺ ⇒ 𝔼`, `AltDriftQ_norm_integral_le`).  Write `N = d.size n`, `x = N^{ε_E/2}`.
* Sup bounds: `𝔼 𝒬_u B_m = expAltQB` (`AltDriftQ_integral_altQB`); the `ℚ` level at the exponent
  `ε_E/2` and failure exponent `4k+7+D_b/2` (parts (a), (b) of `AltLevelsQ`), the crude bound
  `N^{4k+7}` (`AltDriftQ_norm_altQB_le`) give `‖𝔼 𝒬_u B_m‖ ≤ x λ + W^{-D_b} ≤ (x+1) λ ≤ N^{ε_E} λ`
  (`λ ≥ W^{-D_b} ≥ N^{-D_b/2}`, `x ≥ 2`); the drift has five terms (factor `5` of `altELevel`).
* Window decay: `altLocalForm` (`LabelDecayPT` of `F_n` and
  `𝒬_u B_m = F_n(H_u) + O_≺(W^{-D_b})` per time, with `τ₀ = τ'`, `D₀ = D_b`) at a far label:
  the event `{2xW^{-D_b} < ‖𝒬_u B_m‖}` lies in the union of two events of probability `N^{-D}`,
  so `‖𝔼 𝒬_u B_m‖ ≤ 3 x W^{-D_b}` (`x ≥ 2`); the
  drift has five terms (`15 x W^{-D_b} ≤ x² W^{-D_b}`, `x ≥ 15`).  The sections `(σ_n, u_n)` of
  `altLocalForm` are uniformized by `AltDriftQ_ev_forall_of_sections`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. Arithmetic of `≺ ⇒ 𝔼` -/

section Arith

/-- `N^{4k+7} · N^{-(4k+7+D_b/2)} = N^{-D_b/2} ≤ W^{-D_b}` for `W ≤ N^{1/2}`. -/
private theorem AltLevelsE_crude_le {N W Db : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hW0 : 0 < W)
    (hWN : W ≤ N ^ ((1 : ℝ) / 2)) (hDb : 0 < Db) :
    N ^ (4 * k + 7) * N ^ (-((4 * (k : ℝ) + 7) + Db / 2)) ≤ W ^ (-Db) := by
  have hN0 : 0 < N := by linarith
  have e1 : N ^ (4 * k + 7) * N ^ (-((4 * (k : ℝ) + 7) + Db / 2)) = N ^ (-(Db / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have e2 : (N ^ ((1 : ℝ) / 2)) ^ (-Db) = N ^ (-(Db / 2)) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  rw [e1, ← e2]
  exact Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)

/-- `N^{ε_E} = x²` for `x = N^{ε_E/2}`. -/
private theorem AltLevelsE_rpow_sq {N : ℝ} (hN0 : 0 < N) (εE : ℝ) :
    N ^ εE = N ^ (εE / 2) * N ^ (εE / 2) := by
  rw [← Real.rpow_add hN0]; congr 1; ring

/-- The arithmetic of the sup bound: `x λ + N^{4k+7} N^{-(4k+7+D_b/2)} ≤ N^{ε_E} λ` for `λ ≥ W^{-D_b}`. -/
private theorem AltLevelsE_arith_sup {N W lam εE Db : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hW0 : 0 < W)
    (hWN : W ≤ N ^ ((1 : ℝ) / 2)) (hDb : 0 < Db) (hlam : W ^ (-Db) ≤ lam)
    (hx : 2 ≤ N ^ (εE / 2)) :
    N ^ (εE / 2) * lam + N ^ (4 * k + 7) * N ^ (-((4 * (k : ℝ) + 7) + Db / 2)) ≤ N ^ εE * lam := by
  have hN0 : 0 < N := by linarith
  have h1 := AltLevelsE_crude_le (k := k) hN1 hW0 hWN hDb
  have hlam0 : 0 ≤ lam := (Real.rpow_nonneg hW0.le _).trans hlam
  rw [AltLevelsE_rpow_sq hN0 εE]
  nlinarith [mul_nonneg hlam0 (sub_nonneg.2 hx), mul_nonneg (mul_nonneg hlam0 (sub_nonneg.2 hx))
    (by linarith : (0 : ℝ) ≤ N ^ (εE / 2))]

/-- The arithmetic of the decay bound: `2 x w + N^{4k+7} · 2 N^{-(4k+7+D_b/2)} ≤ 3 x w`, `w = W^{-D_b}`. -/
private theorem AltLevelsE_arith_dec {N W εE Db : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hW0 : 0 < W)
    (hWN : W ≤ N ^ ((1 : ℝ) / 2)) (hDb : 0 < Db) (hx : 2 ≤ N ^ (εE / 2)) :
    2 * (N ^ (εE / 2) * W ^ (-Db)) + N ^ (4 * k + 7) * (2 * N ^ (-((4 * (k : ℝ) + 7) + Db / 2))) ≤
      3 * (N ^ (εE / 2) * W ^ (-Db)) := by
  have h1 := AltLevelsE_crude_le (k := k) hN1 hW0 hWN hDb
  have hw0 : 0 ≤ W ^ (-Db) := Real.rpow_nonneg hW0.le _
  nlinarith [mul_nonneg hw0 (sub_nonneg.2 hx)]

end Arith

/-! ## 2. The sup bound `≺ ⇒ 𝔼` at one time -/

section Sup

open LocalFormCuts LocalFormCalc

/-- `W^{-D_b} ≤ altQLevel` (the first summand of the level is nonnegative). -/
private theorem AltLevelsE_le_altQLevel {L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) (k : ℕ) (τ' Db Φ : ℝ) (hΦ : 0 ≤ Φ) :
    (W : ℝ) ^ (-Db) ≤ altQLevel L W E k τ' Db Φ u := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hu1
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWp
  unfold altQLevel
  have : 0 ≤ Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) := by
    positivity
  linarith

/-- `W^{-D_b} ≤ altQ0Level`. -/
private theorem AltLevelsE_le_altQ0Level {L W : ℕ} [NeZero L] [NeZero W] {E s : ℝ} (hE : |E| < 2)
    (hs1 : s < 1) (k : ℕ) (τ' Db : ℝ) :
    (W : ℝ) ^ (-Db) ≤ altQ0Level L W E s k τ' Db := by
  have hLp : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWp : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hM := scaleM_pos hLp hWp hE hs1
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWp
  unfold altQ0Level
  have : 0 ≤ (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (scaleM L W E s ^ k)⁻¹ := by positivity
  linarith

/-- **The sup bound `≺ ⇒ 𝔼` for one `(n, u, σ, m, b)`**: if `‖𝒬_u B_m(H_u)_b‖ ≤ N^{ε_E/2} λ` off an
event of probability `≤ N^{-(4k+7+D_b/2)}`, `λ ≥ W^{-D_b}`, then `‖𝒬_u 𝔼 B_m,b‖ ≤ N^{ε_E} λ`
(`AltDriftQ_norm_integral_le` with the crude bound `N^{4k+7}`). -/
private theorem AltLevelsE_sup_core {n : ℕ} {E : ℕ → ℝ} {u : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hKey : KeyAt (d.L n) (d.W n) (E n) u ((d.size n : ℕ) : ℝ) (k + 1))
    (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ ((d.size n : ℕ) : ℝ))
    {σ : Fin k → Bool} (hσ : Alternating σ) (m : Fin 6) (b : Fin k → Z2 (d.L n))
    {lam εE Db : ℝ} (hDb : 0 < Db) (hlam : (d.W n : ℝ) ^ (-Db) ≤ lam)
    (hx : 2 ≤ ((d.size n : ℕ) : ℝ) ^ (εE / 2))
    (hprob : Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ (εE / 2) * lam <
        ‖altQB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-((4 * (k : ℝ) + 7) + Db / 2)))) :
    ‖expAltQB d E n u σ m b‖ ≤ ((d.size n : ℕ) : ℝ) ^ εE * lam := by
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hKey.hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWN := NonAltEnd_W_le_sqrt d n
  have hlam0 : 0 ≤ lam := (Real.rpow_nonneg hW0.le _).trans hlam
  have hXb : ∀ ω, ‖altQB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b‖ ≤
      ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := fun ω =>
    AltDriftQ_norm_altQB_le hk hKey hNr (Sizes.seqHflow_isHermitian d n u ω) hσ m b
  have hXm : Measurable fun ω => altQB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b :=
    (AltDriftQ_meas_altQB (E n) u σ m b).comp (AltDriftQ_measurable_seqHflow d n u)
  have hint := AltDriftQ_integral_altQB (d := d) hk hKey hNr hσ m b
  rw [← hint]
  refine (AltDriftQ_norm_integral_le hXm (mul_nonneg (Real.rpow_nonneg hN0.le _) hlam0)
    (by positivity) (Real.rpow_nonneg hN0.le _) hXb hprob).trans ?_
  exact AltLevelsE_arith_sup hN1 hW0 hWN hDb hlam hx

/-- **Uniform `KeyAt`**: eventually in `n`, `KeyAt` (at the size `N`, rank `kmax`) holds at every
`u ∈ [s_n, v_n]` (the sections `gd_eventually`). -/
private theorem AltLevelsE_keyAt_ev {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n) (kmax : ℕ) (Nm : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ v n →
      KeyAt (d.L n) (d.W n) (E n) u ((d.size n : ℕ) : ℝ) kmax ∧ Nm ≤ ((d.size n : ℕ) : ℝ) := by
  have key := AltDriftQ_ev_forall_of_sections (U := fun n => {u : ℝ // s n ≤ u ∧ u ≤ v n})
    (fun n => ⟨⟨s n, le_rfl, hsv n⟩⟩)
    (p := fun n x => KeyAt (d.L n) (d.W n) (E n) x.1 ((d.size n : ℕ) : ℝ) kmax ∧
      Nm ≤ ((d.size n : ℕ) : ℝ)) ?_
  · filter_upwards [key] with n hn u h1 h2
    exact hn ⟨u, h1, h2⟩
  · intro sec
    filter_upwards [gd_eventually d hmain kmax Nm one_pos (u := fun n => (sec n).1)
      (fun n => (sec n).2.1) (fun n => (sec n).2.2.trans (hvt n))] with n hn
    exact ⟨hn.1, hn.2.1⟩

/-- **The sup bound for `m ≠ 0`, uniformly in `u ∈ [s_n, v_n]`, `σ`, `b`**: from the per-time `ℚ` level
(part (b) of `AltLevelsQ`) at the exponent `ε_E/2` and the failure exponent `4k+7+D_b/2`. -/
private theorem AltLevelsE_sup_ev {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {Φ : ℕ → ℝ} (hΦ0 : ∀ n, 0 ≤ Φ n)
    {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n) {τ' Db εE : ℝ} (hDb : 0 < Db)
    (hεE : 0 < εE) (m : Fin 6)
    (hlev : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖)
      (fun n p _ => altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (p.1 : ℝ))) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → ∀ u : ℝ, s n ≤ u → u ≤ v n →
      ∀ b : Fin k → Z2 (d.L n), ‖expAltQB d E n u σ m b‖ ≤
        ((d.size n : ℕ) : ℝ) ^ εE * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) u := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hG := AltLevelsE_keyAt_ev d hmain hsv hvt (k + 1) (8 * (k : ℝ) ^ 3 * C5 ^ k)
  have hp := hlev (εE / 2) (half_pos hεE) ((4 * (k : ℝ) + 7) + Db / 2) (by positivity)
  have hx := ((tendsto_rpow_atTop (half_pos hεE)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hG, hp, hx] with n hGn hpn hxn σ hσ u hu1 hu2 b
  obtain ⟨hKey, hNr⟩ := hGn u hu1 hu2
  have hEn : |E n| < 2 := hKey.hE
  refine AltLevelsE_sup_core d hk hKey hNr hσ m b hDb
    (AltLevelsE_le_altQLevel hEn hKey.hu1 k τ' Db (Φ n) (hΦ0 n)) hxn ?_
  exact hpn (⟨u, hu1, hu2⟩, ⟨σ, hσ⟩, b)

/-- **The sup bound for `m = 0` at the time `s_n`**, uniformly in `σ`, `b`: from part (a) of
`AltLevelsQ`. -/
private theorem AltLevelsE_sup0_ev {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {τ' Db εE : ℝ} (hDb : 0 < Db) (hεE : 0 < εE)
    (hlev : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1.1 0 p.2.2‖)
      (fun n _ _ => altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db)) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → ∀ b : Fin k → Z2 (d.L n),
      ‖expAltQB d E n (s n) σ 0 b‖ ≤
        ((d.size n : ℕ) : ℝ) ^ εE * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hG := AltLevelsE_keyAt_ev d hmain (v := s) (fun n => le_rfl) hst (k + 1)
    (8 * (k : ℝ) ^ 3 * C5 ^ k)
  have hp := hlev (εE / 2) (half_pos hεE) ((4 * (k : ℝ) + 7) + Db / 2) (by positivity)
  have hx := ((tendsto_rpow_atTop (half_pos hεE)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hG, hp, hx] with n hGn hpn hxn σ hσ b
  obtain ⟨hKey, hNr⟩ := hGn (s n) le_rfl le_rfl
  have hEn : |E n| < 2 := hKey.hE
  refine AltLevelsE_sup_core d hk hKey hNr hσ 0 b hDb
    (AltLevelsE_le_altQ0Level hEn hKey.hu1 k τ' Db) hxn ?_
  exact hpn ((), ⟨σ, hσ⟩, b)

end Sup

/-! ## 3. The window decay `≺ ⇒ 𝔼` at one section -/

section Decay

open LocalFormCuts LocalFormCalc

/-- **The decay of `𝒬_u 𝔼 B_m` at one section `(u_n, σ_n)`** (the local form `altLocalForm` at
`τ₀ = τ'`, `D₀ = D_b`): eventually in `n`, at every far label `a` (`ℓ_u W^{τ'} ≤ maxDist a`),
`‖𝒬_u 𝔼 B_m,a‖ ≤ 3 N^{ε_E/2} W^{-D_b}`.  The event `{2 x W^{-D_b} < ‖𝒬_u B_m(H_u)_a‖}` lies in
`{x W^{-D_b} < ‖F_a‖ 1_far} ∪ {x W^{-D_b} < ‖𝒬_u B_m - F‖_a}` (probability `N^{-D}` each,
`D = 4k+7+D_b/2`), and the crude bound `N^{4k+7}` handles the rest. -/
private theorem AltLevelsE_decay_section {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {τ' Db εE : ℝ} (hτ' : 0 < τ') (hDb : 0 < Db) (hεE : 0 < εE)
    (m : Fin 6) (u : ℕ → ℝ) (σ : ℕ → Fin k → Bool) (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (hσ : ∀ n, Alternating (σ n)) :
    ∀ᶠ n : ℕ in atTop, ∀ a : Fin k → Z2 (d.L n),
      ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) →
      ‖expAltQB d E n (u n) (σ n) m a‖ ≤
        3 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) := by
  classical
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hdl : DecayLoopPT d E s t :=
    decayLoopWindow d κ c τ E s t hmain (kcalDecay κ) hU.2.1 hloc hdec
  obtain ⟨Kd, C', hC', hF⟩ := altLocalForm d κ c τ E s t hmain hdl (kcalDecay κ) k hk m τ' Db
    hτ' hDb
  obtain ⟨F, hcoef, hloc', hsz, hld, herr⟩ := hF u σ hu hut hσ
  have hG := gd_eventually d hmain (k + 1) (8 * (k : ℝ) ^ 3 * C5 ^ k) one_pos hu hut
  have hD0 : 0 < (4 * (k : ℝ) + 7) + Db / 2 := by positivity
  have h1 := hld (εE / 2) (half_pos hεE) _ hD0
  have h2 := herr (εE / 2) (half_pos hεE) _ hD0
  have hx := ((tendsto_rpow_atTop (half_pos hεE)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hG, h1, h2, hx] with n hGn h1n h2n hxn a hfar
  have hKey : KeyAt (d.L n) (d.W n) (E n) (u n) ((d.size n : ℕ) : ℝ) (k + 1) := hGn.1
  have hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ ((d.size n : ℕ) : ℝ) := hGn.2.1
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hKey.hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWN := NonAltEnd_W_le_sqrt d n
  have hXb : ∀ ω, ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a‖ ≤
      ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := fun ω =>
    AltDriftQ_norm_altQB_le hk hKey hNr (Sizes.seqHflow_isHermitian d n (u n) ω) (hσ n) m a
  have hXm : Measurable fun ω => altQB (d.L n) (d.W n) (E n) (u n)
      (Sizes.seqHflow d n (u n) ω) (σ n) m a :=
    (AltDriftQ_meas_altQB (E n) (u n) (σ n) m a).comp (AltDriftQ_measurable_seqHflow d n (u n))
  have hint := AltDriftQ_integral_altQB (d := d) hk hKey hNr (hσ n) m a
  rw [← hint]
  have hq : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-((4 * (k : ℝ) + 7) + Db / 2)) :=
    Real.rpow_nonneg hN0.le _
  have hθ : 0 ≤ 2 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hW0.le _))
  have hinc : {ω | 2 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) <
        ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a‖} ⊆
      {ω | ((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db) <
        ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a‖ *
          (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) then 1 else 0)} ∪
      {ω | ((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db) <
        ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a -
          (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon hω
    obtain ⟨hc1, hc2⟩ := hcon
    simp only [hfar, ↓reduceIte, mul_one] at hc1
    have hle : ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a‖ ≤
        ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a‖ +
        ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a -
          (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a‖ := by
      calc _ = ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a +
              (altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a -
                (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) a)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hp : Sizes.seqP d {ω | 2 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) <
        ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a‖} ≤
      ENNReal.ofReal (2 * ((d.size n : ℕ) : ℝ) ^ (-((4 * (k : ℝ) + 7) + Db / 2))) := by
    refine (measure_mono hinc).trans ((measure_union_le _ _).trans ?_)
    have e1 := h1n ((), a)
    have e2 := h2n ((), a)
    calc _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-((4 * (k : ℝ) + 7) + Db / 2))) +
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-((4 * (k : ℝ) + 7) + Db / 2))) :=
          add_le_add e1 e2
      _ = _ := by rw [← ENNReal.ofReal_add hq hq]; congr 1; ring
  refine (AltDriftQ_norm_integral_le hXm hθ (by positivity) (mul_nonneg (by norm_num) hq) hXb
    hp).trans ?_
  exact AltLevelsE_arith_dec hN1 hW0 hWN hDb hxn

/-- **The decay of `𝒬_u 𝔼 B_m`, uniformly in the alternating `σ` and `u ∈ [s_n, v_n]`**: the sections
`(σ_n, u_n)` of `AltLevelsE_decay_section` uniformized by `AltDriftQ_ev_forall_of_sections`. -/
private theorem AltLevelsE_decay_ev {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    {τ' Db εE : ℝ} (hτ' : 0 < τ') (hDb : 0 < Db) (hεE : 0 < εE) (m : Fin 6) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → ∀ u : ℝ, s n ≤ u → u ≤ v n →
      ∀ a : Fin k → Z2 (d.L n),
        ellT (d.L n) u * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) →
        ‖expAltQB d E n u σ m a‖ ≤
          3 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) := by
  classical
  by_cases hex : ∃ σ₀ : Fin k → Bool, Alternating σ₀
  swap
  · exact Eventually.of_forall fun n σ hσ => absurd ⟨σ, hσ⟩ hex
  obtain ⟨σ₀, hσ₀⟩ := hex
  have key := AltDriftQ_ev_forall_of_sections
    (U := fun n => {σ : Fin k → Bool // Alternating σ} × {u : ℝ // s n ≤ u ∧ u ≤ v n})
    (fun n => ⟨⟨σ₀, hσ₀⟩, ⟨s n, le_rfl, hsv n⟩⟩)
    (p := fun n x => ∀ a : Fin k → Z2 (d.L n),
      ellT (d.L n) x.2.1 * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ) →
        ‖expAltQB d E n x.2.1 x.1.1 m a‖ ≤
          3 * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db))) ?_
  · filter_upwards [key] with n hn σ hσ u h1 h2
    exact hn ⟨⟨σ, hσ⟩, ⟨u, h1, h2⟩⟩
  · intro sec
    exact AltLevelsE_decay_section d hU hmain hloc hdec hk hτ' hDb hεE m (fun n => (sec n).2.1)
      (fun n => (sec n).1.1) (fun n => (sec n).2.2.1) (fun n => (sec n).2.2.2.trans (hvt n))
      (fun n => (sec n).1.2)

end Decay

/-! ## 4. The hypothesis `altLevelsE` -/

section Main

/-- The five-term triangle inequality for the `𝔼` drift. -/
private theorem AltLevelsE_norm_drift_le {n : ℕ} {E : ℕ → ℝ} {u : ℝ} {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (a : Fin k → Z2 (d.L n)) {B : ℝ}
    (h1 : ‖expAltQB d E n u σ 1 a‖ ≤ B) (h2 : ‖expAltQB d E n u σ 2 a‖ ≤ B)
    (h3 : ‖expAltQB d E n u σ 3 a‖ ≤ B) (h4 : ‖expAltQB d E n u σ 4 a‖ ≤ B)
    (h5 : ‖expAltQB d E n u σ 5 a‖ ≤ B) : ‖expDriftQN d E n u σ a‖ ≤ 5 * B := by
  unfold expDriftQN
  have e1 := norm_sub_le (expAltQB d E n u σ 1 a + expAltQB d E n u σ 2 a +
    expAltQB d E n u σ 3 a + expAltQB d E n u σ 4 a) (expAltQB d E n u σ 5 a)
  have e2 := norm_add_le (expAltQB d E n u σ 1 a + expAltQB d E n u σ 2 a +
    expAltQB d E n u σ 3 a) (expAltQB d E n u σ 4 a)
  have e3 := norm_add_le (expAltQB d E n u σ 1 a + expAltQB d E n u σ 2 a)
    (expAltQB d E n u σ 3 a)
  have e4 := norm_add_le (expAltQB d E n u σ 1 a) (expAltQB d E n u σ 2 a)
  linarith

/-- **The hypothesis `AltLevelsE`**: the deterministic `𝔼`
levels (sup bound and window decay) of `e_0 = 𝒬_s 𝔼 B_0` and of the `𝔼` drift at every
`u ∈ [s_n, v_n]`, for every alternating `σ`, eventually in `n`.  Sup bounds: `≺ ⇒ 𝔼`
(`AltDriftQ_norm_integral_le`) from the two parts of `AltLevelsQ` (`altLevelsQ0`, `altLevelsQm`) and the
crude bound `N^{4k+7}`; window decay: `≺ ⇒ 𝔼` from the local forms `altLocalForm`
(`LabelDecayPT` of `F_n` and `𝒬_u B_m = F_n(H_u) + O_≺(W^{-D_b})`). -/
theorem altLevelsE (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : AltLevelsE d κ c τ C E s t := by
  intro hU hmain hloc hdec k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt τ' Db εE hτ' hDb hεE
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hQ0 := altLevelsQ0 d κ c τ C E s t hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev τ' Db hτ' hDb
  have hQm := altLevelsQm d κ c τ C E s t hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt
    τ' Db hτ' hDb
  have S0 := AltLevelsE_sup0_ev d hmain hk hDb hεE hQ0
  have S1 := AltLevelsE_sup_ev d hmain hk hΦ0 hsv hvt hDb hεE 1 (hQm 1 (by decide))
  have S2 := AltLevelsE_sup_ev d hmain hk hΦ0 hsv hvt hDb hεE 2 (hQm 2 (by decide))
  have S3 := AltLevelsE_sup_ev d hmain hk hΦ0 hsv hvt hDb hεE 3 (hQm 3 (by decide))
  have S4 := AltLevelsE_sup_ev d hmain hk hΦ0 hsv hvt hDb hεE 4 (hQm 4 (by decide))
  have S5 := AltLevelsE_sup_ev d hmain hk hΦ0 hsv hvt hDb hεE 5 (hQm 5 (by decide))
  have D0 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 0
  have D1 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 1
  have D2 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 2
  have D3 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 3
  have D4 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 4
  have D5 := AltLevelsE_decay_ev d hU hmain hloc hdec hk hsv hvt hτ' hDb hεE 5
  have hx := ((tendsto_rpow_atTop (half_pos hεE)).comp hsize).eventually_ge_atTop 15
  have hN1 := hsize.eventually_ge_atTop 1
  filter_upwards [S0, S1, S2, S3, S4, S5, D0, D1, D2, D3, D4, D5, hx, hN1] with n s0 s1 s2 s3 s4 s5
    d0 d1 d2 d3 d4 d5 hxn hN1n σ hσ
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hw0 : 0 ≤ (d.W n : ℝ) ^ (-Db) := Real.rpow_nonneg hW0.le _
  have hsq := AltLevelsE_rpow_sq hN0 εE
  have hx0 : (15 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (εE / 2) := hxn
  -- the decay arithmetic: `c₀ x w ≤ x² w` for `c₀ ≤ 15`
  have hdecar : ∀ c₀ : ℝ, 0 ≤ c₀ → c₀ ≤ 15 →
      c₀ * (((d.size n : ℕ) : ℝ) ^ (εE / 2) * (d.W n : ℝ) ^ (-Db)) ≤ altEDecay d n Db εE := by
    intro c₀ hc0 hc15
    unfold altEDecay
    rw [hsq]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (εE / 2)) hw0)
      (by linarith : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (εE / 2) - c₀)]
  refine ⟨fun b => s0 σ hσ b, fun a ha => ?_, fun u hu1 hu2 => ⟨fun b => ?_, fun a ha => ?_⟩⟩
  · exact (d0 σ hσ (s n) le_rfl (hsv n) a ha).trans (hdecar 3 (by norm_num) (by norm_num))
  · exact (AltLevelsE_norm_drift_le d σ b (s1 σ hσ u hu1 hu2 b) (s2 σ hσ u hu1 hu2 b)
      (s3 σ hσ u hu1 hu2 b) (s4 σ hσ u hu1 hu2 b) (s5 σ hσ u hu1 hu2 b)).trans_eq rfl
  · have := AltLevelsE_norm_drift_le d σ a (d1 σ hσ u hu1 hu2 a ha) (d2 σ hσ u hu1 hu2 a ha)
      (d3 σ hσ u hu1 hu2 a ha) (d4 σ hσ u hu1 hu2 a ha) (d5 σ hσ u hu1 hu2 a ha)
    refine this.trans ?_
    have h15 := hdecar 15 (by norm_num) le_rfl
    linarith

end Main

/-! ## 5. `altLevelsQ_of_parts`, `altGridEnd`, `stoeqTargetV2` -/

/-- **`altLevelsQ_of_parts`**: the two parts `AltLevelsQ0` (the level of `𝒬_s B_0` at `s`) and
`AltLevelsQm` (the levels of `𝒬_u B_m`, `m = 1..5`) give `AltLevelsQ` (the two conjuncts of
`AltLevelsQConcl`). -/
theorem altLevelsQ_of_parts (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) :
    AltLevelsQ0 d κ c τ C E s t → AltLevelsQm d κ c τ C E s t → AltLevelsQ d κ c τ C E s t := by
  intro h0 hm hU hmain hloc hdec k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt τ' Db hτ' hDb
  exact ⟨h0 hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev τ' Db hτ' hDb,
    hm hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt τ' Db hτ' hDb⟩

/-- **The alternating grid endpoint** (`lem:STOeq_Qt`, the statement `AltGridEnd`),
proved: `altGridEnd_of_pins` with the four proved hypotheses `AltLevelsQ` (`altLevelsQ_of_parts`
`altLevelsQ0` `altLevelsQm`), `AltLevelsE` (`altLevelsE`), `BudgetAlt` (`budgetAlt`) and
`AltAbsorb` (`altAbsorb`).  No hypothesis is added. -/
theorem altGridEnd (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : AltGridEnd d κ c τ C E s t :=
  altGridEnd_of_pins d κ c τ C E s t
    (altLevelsQ_of_parts d κ c τ C E s t (altLevelsQ0 d κ c τ C E s t) (altLevelsQm d κ c τ C E s t))
    (altLevelsE d κ c τ C E s t) (budgetAlt d) (altAbsorb d)

/-- **The statement `STOeqTargetV2`** (`lem:STOeq_NQ` + `lem:STOeq_Qt`), proved: `stoeqTargetV2_of_gridEnds` with `altLocalForm`, `altExpSymm`, `nonAltGridEnd` and
`altGridEnd`.  No hypothesis is added: the inputs from other results (`UpstreamSteps34Prec`,
`Step2LocalPT`, `Step2DecayPT`) are the premises of `STOeqTargetV2` itself. -/
theorem stoeqTargetV2 (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : STOeqTargetV2 d κ c τ C E s t :=
  stoeqTargetV2_of_gridEnds (altLocalForm d κ c τ E s t) (altExpSymm d)
    (nonAltGridEnd d κ c τ C E s t) (altGridEnd d κ c τ C E s t)

end RBM.Ind

end
