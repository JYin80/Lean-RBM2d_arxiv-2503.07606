/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEndCompose

/-!
# The alternating endpoint, part 2: the assembly, the four hypotheses and `altGridEnd_of_pins`

Part of the alternating endpoint `AltGridEnd`.  This file holds the assembly (`altEnd_assembly`),
the four hypotheses `AltLevelsQ`, `AltLevelsE`, `BudgetAlt`, `AltAbsorb` (statements only; they are
proved in `RBM2D.Induction.AltLevelsQ0`, `AltLevelsQ`, `AltLevelsE`, `AltBudget`, `AltAbsorb`), the
last step `altLastStep_of_goodSet` and `altGridEnd_of_pins`.  The vocabulary and the compositions
are in `RBM2D.Induction.AltEndCompose`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

section Compositions

variable {d}

/-- **The assembly of the `𝒬` process at the exit time** (the analogue of `NonAltEnd_assembly`).
For each alternating `σ` on a strict window `s_n < v_n`, eventually in `n`: on an event
`G` of probability `≥ 1 - N^{-D₁}` (`assembledN` applied to the *modified process*
`Ã = 𝒰 e_0 + Σ 𝒰 (Δ e^D_j + Z_j + Y_j + R_j)` with the Case 4 class `AltCase4Cls`), if the grid walk
stays in `GoodSetN` and the `ℚ` bounds of `altQPartGridT` hold (`hQinit`, `hQdrift`), then
`|A^Q_K(a)| ≤ assembledRHSAlt`.  The inputs given as hypotheses: the `𝔼` levels `hLE`
(`AltLevelsE`) and the eventual numerical facts `hGs`, `hδ` (the shift), `hη`, `hM1`. -/
theorem altEnd_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hsize : SizeTendsto d)
    (Γ Λ Φ : ℕ → ℝ) (hΓ1 : ∀ n, 1 ≤ Γ n) (hΛ0 : ∀ n, 0 ≤ Λ n) (hΦ0 : ∀ n, 0 ≤ Φ n)
    {𝔠 τ' Dq C' D_Y τK εq εE ε Db D₁ C_P C_K : ℝ}
    (hτ' : 0 ≤ τ') (hτK : 0 < τK) (hε : 0 < ε) (hDq : 0 ≤ Dq)
    (hCK0 : 0 ≤ C_K) (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
        YMomentBoundsN d (E n) σ (gridTime s v K n) τ (K n)
          (fun j ω => yVecQN d E s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hQV : ∀ᶠ n : ℕ in atTop, AltQvShiftAt k 𝔠 τ' Dq C' (d.size n))
    (hNc : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, (d.W n : ℝ) ^ (-(Dq + 1)) +
      eeShiftErr (d.L n) (d.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        (d.W n : ℝ) ^ (-Dq))
    (hGs : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-Dq) ≤
      Γ n * (Γ n * Λ n))
    (hη : ∀ᶠ n : ℕ in atTop, (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ))
    (hM1 : ∀ᶠ n : ℕ in atTop, 1 ≤ scaleM (d.L n) (d.W n) (E n) (v n))
    (hLE : ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ →
      AltELevelsAt d n E s v k σ τ' Db εE (Φ n)) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → s n < v n →
      ∃ G : Set (PathΩ d), (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n)
            (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' (Dq + 1)) →
          (∀ a : Fin k → Z2 (d.L n),
            ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
                (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a‖ ≤
              ((d.size n : ℕ) : ℝ) ^ εq * altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db *
                  ratioR (d.L n) (E n) (s n) (gridTime s v K n (K n)) ^ k +
                (d.W n : ℝ) ^ (-Db)) →
          (∀ j < K n, ∀ a : Fin k → Z2 (d.L n),
            ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n))
                (fun b => dGridQN d E s v K n σ j ω b -
                  expDriftQN d E n (gridTime s v K n j) σ b) a‖ ≤
              ((d.size n : ℕ) : ℝ) ^ εq * (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n)
                  (gridTime s v K n j)) *
                ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-Db)) →
          ∀ a : Fin k → Z2 (d.L n),
            ‖aTrueQN d E s v K n σ (K n) ω a‖ ≤
              assembledRHSAlt d E s v K n k 𝔠 τ' Dq C' Db εq εE ε D_Y τK Φ
                (2 * (Γ n * (Γ n * Λ n))) (Γ n * (Γ n * Λ n) * ((d.size n : ℕ) : ℝ) + 1) a := by
  classical
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hAn := assembledN d hsize k ε hε D_Y D₁ C_P C_K hCK0 hCK
  have hEnv : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP d), ∀ j, j < K n →
      ∀ a : Fin k → Z2 (d.L n), ‖rGridQN d E s v K n σ j ω a‖ ≤
        qErrQN d E s v K n k (((d.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) j :=
    fun σ => gridDriftQN_envelope κ hκ k hk τK hτK hsize hE hs0 hsv hv1 hK0 σ
  have hCr := altCrude_grid hκ k hk (K := K) hsize hE hs0 hsv hv1 hη
  filter_upwards [hAn, hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hQV,
    hNc, hδ, hGs, hη, hM1, hLE, hCr] with n hAnn hKNn hKUn hYn hEnvn hQVn hNcn hδn hGsn hηn hM1n
    hLEn hCrn
  intro σ hσ hsvn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  obtain ⟨hX0, hdec0, hdr⟩ := hLEn σ hσ
  have hEn2 : |E n| < 2 := hE2 n
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-C_K) := NonAltEnd_step_le d hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := NonAltEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ =>
    GoodEvent_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (GoodEvent_gridTime_le (K := K) (hsv n) hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m :=
    fun i m him _ => GoodEvent_gridTime_mono (hsv n) him
  have hLp : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hW1r : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hKw : (1 : ℝ) ≤ (d.W n : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := GoodEvent_one_le_size n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hτmeas : ∀ j, MeasurableSet[filt d j]
      {ω | j < goodExitTauN d E s v K k Γ Λ Φ τ' (Dq + 1) n ω} :=
    goodExitMeasN d E s v K n k Γ Λ Φ τ' (Dq + 1)
  have hmem : ∀ (ω : PathΩ d) (j : ℕ), j < goodExitTauN d E s v K k Γ Λ Φ τ' (Dq + 1) n ω →
      pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n)
        (Φ n) τ' (Dq + 1) := fun ω j hj => mem_of_lt_gridExitTauN hj
  -- the data of the modified process
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ d → ℕ := goodExitTauN d E s v K k Γ Λ Φ τ' (Dq + 1) n with hτdef
  set Kw : ℝ := (d.W n : ℝ) ^ τ' with hKwdef
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNndef
  set Y0 : ℝ := Γ n * (Γ n * Λ n) with hY0def
  set Gq : ℝ := 2 * Y0 with hGqdef
  set Mmx : ℝ := Y0 * Nn + 1 with hMmxdef
  have hY00 : 0 ≤ Y0 := by
    have := hΓ1 n
    have := hΛ0 n
    rw [hY0def]; positivity
  set A0 : PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun _ => expAltQB d E n (s n) σ 0 with hA0
  set Dr : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ :=
    fun j _ => expDriftQN d E n (u j) σ with hDr
  set Z : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω => zVecQN d E s v K n j σ ω with hZ
  set Yv : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω => yVecQN d E s v K n j σ ω with hYv
  set R : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun j ω => rGridQN d E s v K n σ j ω with hR
  set Af : ℕ → PathΩ d → (Fin k → Z2 (d.L n)) → ℂ := fun m ω =>
    Ugen (d.L n) (E n) σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Ugen (d.L n) (E n) σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Yv j ω + R j ω) with hAf
  set κ' : ℕ → ℕ → ℝ := fun i m => kapQ4 (d.L n) k Kw (u (i - 1)) (u m) with hκ'
  set εK : ℕ → ℕ → ℝ := fun i m => epsQ4 (d.L n) k (u (i - 1)) (u m) with hεK
  set δ0 : ℝ := altEDecay d n Db εE with hδ0
  set dDrift : ℕ → PathΩ d → ℝ := fun j _ => altELevel d n E k τ' Db εE (Φ n) (u j) with hdDrift
  set δD : ℕ → PathΩ d → ℝ := fun _ _ => altEDecay d n Db εE with hδD
  set cc : ℕ → (Fin k → Z2 (d.L n)) → ℕ → ℝ≥0 := fun m a j =>
    cQVAlt d E s v K n k 𝔠 τ' Dq C' Gq Mmx m a j with hcc
  set stepE : ℕ → ℝ := fun j => qErrQN d E s v K n k
    (Nn ^ τK * (etaT (E n) (u (j + 1)))⁻¹ ^ k) j with hstepE
  have hη0 : ∀ i ≤ K n, 0 < etaT (E n) (u i) := fun i hi => etaT_pos hEn2 (hu1 i hi)
  have hWN : (d.W n : ℝ) ^ 2 ≤ Nn := by
    have h1 : (1 : ℝ) ≤ (d.L n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hLp)
    have hNr : Nn = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
      rw [hNndef, Sizes.size_eq]; push_cast; ring
    rw [hNr]
    exact le_mul_of_one_le_right (by positivity) h1
  -- the quadratic-variation levels
  have hlvl2 : ∀ j, j + 1 ≤ K n → Y0 * ((scaleM (d.L n) (d.W n) (E n) (u j) ^ (2 * k))⁻¹ *
        (etaT (E n) (u j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤
      Gq * ((scaleM (d.L n) (d.W n) (E n) (u (j + 1)) ^ (2 * k))⁻¹ *
        (etaT (E n) (u (j + 1)))⁻¹) := by
    intro j hj
    have hmo := AltEndCompose_lvl_mono (L := d.L n) (W := d.W n) hEn2 (hmono j (j + 1) (by omega) hj)
      (hu1 (j + 1) hj) (2 * k)
    have hge := AltEndCompose_lvl_ge (L := d.L n) (W := d.W n) hEn2 (hu0 (j + 1) hj) (hu1 (j + 1) hj) hWN
      (2 * k)
    have hWD : (d.W n : ℝ) ^ (-Dq) ≤ Y0 * ((scaleM (d.L n) (d.W n) (E n) (u (j + 1)) ^ (2 * k))⁻¹ *
        (etaT (E n) (u (j + 1)))⁻¹) := by
      have hNk : 0 < Nn ^ (2 * k) := pow_pos hN0 _
      have h1 : (d.W n : ℝ) ^ (-Dq) ≤ Y0 * (Nn ^ (2 * k))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hNk]
        calc (d.W n : ℝ) ^ (-Dq) * Nn ^ (2 * k) = Nn ^ (2 * k) * (d.W n : ℝ) ^ (-Dq) := mul_comm _ _
          _ ≤ Y0 := hGsn
      exact h1.trans (mul_le_mul_of_nonneg_left hge hY00)
    calc Y0 * ((scaleM (d.L n) (d.W n) (E n) (u j) ^ (2 * k))⁻¹ * (etaT (E n) (u j))⁻¹) +
          (d.W n : ℝ) ^ (-Dq) ≤ Y0 * ((scaleM (d.L n) (d.W n) (E n) (u (j + 1)) ^ (2 * k))⁻¹ *
            (etaT (E n) (u (j + 1)))⁻¹) + Y0 * ((scaleM (d.L n) (d.W n) (E n) (u (j + 1)) ^ (2 * k))⁻¹ *
            (etaT (E n) (u (j + 1)))⁻¹) := add_le_add (mul_le_mul_of_nonneg_left hmo hY00) hWD
      _ = Gq * _ := by rw [hGqdef]; ring
  have hlvlM : ∀ j, j ≤ K n → Y0 * ((scaleM (d.L n) (d.W n) (E n) (u j) ^ (2 * k))⁻¹ *
        (etaT (E n) (u j))⁻¹) + (d.W n : ℝ) ^ (-Dq) ≤ Mmx := by
    intro j hj
    have h1 := AltEndCompose_lvl_le (L := d.L n) (W := d.W n) hEn2 (hu1 j hj)
      ((hM1n.trans (by
        rw [show u j = gridTime s v K n j from rfl]
        exact (scaleM_anti_ratio hLp hEn2 ((hmono j (K n) hj le_rfl).trans (le_of_eq
          (gridTime_last s v K n hKn))) (hv1 n)).1))) (2 * k)
    have hηle : (etaT (E n) (u j))⁻¹ ≤ Nn := by
      refine le_trans (inv_anti₀ (etaT_pos hEn2 (hv1 n)) ?_) hηn
      exact AltEndCompose_etaT_anti hEn2 ((hmono j (K n) hj le_rfl).trans (le_of_eq
        (gridTime_last s v K n hKn)))
    have hWD1 : (d.W n : ℝ) ^ (-Dq) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
    calc Y0 * ((scaleM (d.L n) (d.W n) (E n) (u j) ^ (2 * k))⁻¹ * (etaT (E n) (u j))⁻¹) +
          (d.W n : ℝ) ^ (-Dq) ≤ Y0 * Nn + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (h1.trans hηle) hY00) hWD1
      _ = Mmx := rfl
  have hs1 : s n < 1 := (hsv n).trans_lt (hv1 n)
  have hsu : ∀ j ≤ K n, s n ≤ u j := fun j _ => by
    have := GoodEvent_gridTime_mono (K := K) (hsv n) (Nat.zero_le j)
    rwa [GoodEvent_gridTime_zero] at this
  have huv : ∀ j ≤ K n, u j ≤ v n := fun j hj => GoodEvent_gridTime_le (K := K) (hsv n) hj
  have hu00 : u 0 = s n := GoodEvent_gridTime_zero
  have hqpos : (0 : ℝ) ≤ Gq := by rw [hGqdef]; positivity
  have hMpos : (0 : ℝ) ≤ Mmx := by rw [hMmxdef]; positivity
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Z2 (d.L n)) (j : ℕ), j < m →
      SubGaussStopN d (E n) σ u τ Z m a j (cc m a j) := fun m hm a j hj =>
    subGaussStop_alt hE2 hs0 hsv hv1 n k hk hσ Γ Λ Φ (by linarith [hΓ1 n]) (hΛ0 n) 𝔠 τ'
      (Dq + 1) Dq C' Gq Mmx hqpos m hm a j hj hQVn hNcn (hδn j (by omega))
      (hlvl2 j (by omega)) (hlvlM j (by omega))
  have hZmeas : ∀ j, StronglyMeasurable[filt d (j + 1)] (Z j) := fun j =>
    AltEndCompose_stronglyMeasurable_zVecQN E s v K n j σ
  have hbundle : GridAssemblyHypN d (n := n) (k := k) (E n) σ u τ Δ (K n)
      (AltCase4Cls (d.L n) u Kw) A0 Af Dr Z Yv R κ' εK δ0 dDrift δD cc
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE := {
    hE := hEn2.le
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Filter.Eventually.of_forall fun ω => rfl
    hκ0 := fun i m him hmK => AltEndCompose_kapQ4_nonneg _ _ _ (hu1 (i - 1) (by omega)) (hu1 m hmK)
    hε0 := fun i m him hmK => AltEndCompose_epsQ4_nonneg _ _ (hu1 (i - 1) (by omega)) (hu1 m hmK)
    hker := altQ_hker_shift (W := d.W n) hk (d.three_le_L n) hEn2 hσ hu0 hmono hu1 hKw
    hδ0 := by rw [hδ0]; unfold altEDecay; positivity
    hA0cls := fun ω _ => by
      have hcls := (expAltQB_cls d E n (s n) k σ hk hEn2 (hs0 n) hs1 hσ).1 0
      refine ⟨hcls.1, hcls.2, ?_⟩
      rw [hu00]
      exact hdec0
    hdDrift0 := fun ω j hj => by
      show 0 ≤ altELevel d n E k τ' Db εE (Φ n) (u j)
      unfold altELevel
      have := AltEndCompose_altQLevel_nonneg (L := d.L n) (W := d.W n) hEn2 (hu1 j hj.le) k τ' Db (Φ n)
        (hΦ0 n)
      positivity
    hδD0 := fun ω j hj => by
      show 0 ≤ altEDecay d n Db εE
      unfold altEDecay; positivity
    hdrift := fun ω j hj _ b => (hdr (u j) (hsu j hj.le) (huv j hj.le)).1 b
    hDcls := fun ω j hj _ => by
      obtain ⟨hz, hs⟩ := (expAltQB_cls d E n (u j) k σ hk hEn2 (hu0 j hj.le) (hu1 j hj.le) hσ).2
      refine ⟨hz, hs, ?_⟩
      have hD := (hdr (u j) (hsu j hj.le) (huv j hj.le)).2
      intro a ha
      have hrad : ellT (d.L n) (u j) ≤ ellT (d.L n) (u (j + 1)) :=
        (ellT_mono_ratio hLp (hu0 j hj.le) (hmono j (j + 1) (by omega) hj) (hu1 (j + 1) hj)).1
      exact hD a (le_trans (mul_le_mul_of_nonneg_right hrad (by positivity)) ha)
    hc_pos := cQVAlt_sum_pos n k hEn2 (by omega) hsvn (hv1 n) hKn 𝔠 τ' Dq C' Gq Mmx hqpos hMpos
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => AltEndCompose_qErrQN_nonneg (by omega) hEn2 hΔ0 (hu1 j hj.le) (hu1 (j + 1) hj)
      (by have := hη0 (j + 1) hj; positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => hω j hj b }
  obtain ⟨G, hG, hGb⟩ := hAnn (K n) (E n) σ u τ Δ (AltCase4Cls (d.L n) u Kw) A0 Af Dr Z Yv R κ' εK
    δ0 dDrift δD cc (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE P hK1 hKUn hΔ hKΔ hP0 hPle
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  -- the full-measure set where `martIncQN = zVecQN + yVecQN`
  have hmartAE : ∀ᵐ ω ∂(pathP d), ∀ j, j < K n → ∀ b : Fin k → Z2 (d.L n),
      martIncQN d E s v K n σ j ω b = zVecQN d E s v K n j σ ω b + yVecQN d E s v K n j σ ω b := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : j < K n
    · have hj1 : gridTime s v K n (j + 1) < 1 := hu1 (j + 1) hj
      have h := ae_all_iff.2 fun b : Fin k → Z2 (d.L n) =>
        martIncQN_ae_eq d E s v K n j hEn2 hj1 σ b
      filter_upwards [h] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hj
  set S : Set (PathΩ d) := {ω | ∀ j, j < K n → ∀ b : Fin k → Z2 (d.L n),
      martIncQN d E s v K n σ j ω b = zVecQN d E s v K n j σ ω b + yVecQN d E s v K n j σ ω b}
    with hS
  have hSc : (pathP d).real Sᶜ = 0 := by
    have h0 : (pathP d) Sᶜ = 0 := ae_iff.1 hmartAE
    simp [measureReal_def, h0]
  refine ⟨G ∩ S, ?_, ?_⟩
  · calc (pathP d).real (G ∩ S)ᶜ = (pathP d).real (Gᶜ ∪ Sᶜ) := by rw [Set.compl_inter]
      _ ≤ (pathP d).real Gᶜ + (pathP d).real Sᶜ := measureReal_union_le _ _
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) := by rw [hSc]; linarith
  · intro ω hωGS hgood hQinit hQdrift a
    obtain ⟨hωG, hωS⟩ := hωGS
    have hτeq : τ ω = K n := gridExitTauN_eq_of_forall_mem hgood
    have hτpos : 0 < τ ω := by rw [hτeq]; omega
    have hb := hGb ω hωG hτpos (K n) le_rfl a
    have hid := altEnd_identity (d := d) σ hE2 hs0 hsv hv1 hK0 ω hωS a
    -- the `Ã` term
    have hAfK : Af (K n) ω a = Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
            (expAltQB d E n (s n) σ 0) a +
          ∑ j ∈ Finset.range (K n), Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
            (gridTime s v K n (K n))
            ((gridStep s v K n : ℂ) • expDriftQN d E n (gridTime s v K n j) σ +
              zVecQN d E s v K n j σ ω + yVecQN d E s v K n j σ ω +
              rGridQN d E s v K n σ j ω) a := by
      simp only [hAf, hτeq, min_self, Pi.add_apply, Finset.sum_apply]
      rfl
    -- the `ℚ` initial term
    have hT1 := hQinit a
    -- the `ℚ` drift terms with the kernel shift
    have hCrω := hCrn σ hσ
    have hT2 := altEnd_driftQ_sum (d := d) (k := k) σ hEn2 (hs0 n) (hsv n) (hv1 n) hKn hηn ω a
      (fun j b => dGridQN d E s v K n σ j ω b - expDriftQN d E n (gridTime s v K n j) σ b)
      (fun j hj b => by
        have h1 := (hCrω j hj).1 ω b
        have h2 := (hCrω j hj).2 b
        calc ‖dGridQN d E s v K n σ j ω b - expDriftQN d E n (gridTime s v K n j) σ b‖
            ≤ ‖dGridQN d E s v K n σ j ω b‖ + ‖expDriftQN d E n (gridTime s v K n j) σ b‖ :=
              norm_sub_le _ _
          _ ≤ 10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7) := by linarith)
      (fun j => ((d.size n : ℕ) : ℝ) ^ εq * (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n)
                  (gridTime s v K n j)) *
                ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-Db))
      (fun j hj => hQdrift j hj a)
    -- the sup of the initial `𝔼` tensor
    have hsup : Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) ≤
        altE0Level d n E s k τ' Db εE :=
      Finset.sup'_le _ _ fun b _ => hX0 b
    have hk0 : 0 ≤ κ' 0 (K n) := AltEndCompose_kapQ4_nonneg _ _ _ (hu1 _ (by omega)) (hu1 _ le_rfl)
    -- assemble
    have hnorm : ‖aTrueQN d E s v K n σ (K n) ω a‖ ≤
        ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
          (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a‖ +
        ‖∑ j ∈ Finset.range (K n), Ugen (d.L n) (E n) σ (gridTime s v K n (j + 1))
          (gridTime s v K n (K n)) (fun b => (gridStep s v K n : ℂ) * (dGridQN d E s v K n σ j ω b -
            expDriftQN d E n (gridTime s v K n j) σ b)) a‖ + ‖Af (K n) ω a‖ := by
      rw [hid, ← hAfK]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hsumsplit : ∑ j ∈ Finset.range (K n),
        (((d.size n : ℕ) : ℝ) ^ εq * (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n)
                  (gridTime s v K n j)) *
                ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-Db) +
          ((d.size n : ℕ) : ℝ) ^ k * ((1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1) *
            (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))) =
        ∑ j ∈ Finset.range (K n),
        (((d.size n : ℕ) : ℝ) ^ εq * (5 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n)
                  (gridTime s v K n j)) *
                ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-Db)) +
        (K n : ℝ) * (((d.size n : ℕ) : ℝ) ^ k * ((1 + gridStep s v K n * ((d.size n : ℕ) : ℝ)) ^ k - 1) *
            (10 * ((d.size n : ℕ) : ℝ) ^ (4 * k + 7))) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold assembledRHSAlt altShiftTerm
    simp only [κ', εK, δ0, dDrift, δD, cc, stepE, u, Δ, Nn, Gq, Mmx, Y0, Kw] at hb
    simp only [Nat.zero_sub, Nat.add_sub_cancel] at hb
    rw [hsumsplit, mul_add] at hT2
    have hb' : ‖Af (K n) ω a‖ ≤ kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n 0)
          (gridTime s v K n (K n)) * altE0Level d n E s k τ' Db εE +
        epsQ4 (d.L n) k (gridTime s v K n 0) (gridTime s v K n (K n)) * altEDecay d n Db εE +
        gridStep s v K n * ∑ j ∈ Finset.range (K n),
          (kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n j) (gridTime s v K n (K n)) *
              altELevel d n E k τ' Db εE (Φ n) (gridTime s v K n j) +
            epsQ4 (d.L n) k (gridTime s v K n j) (gridTime s v K n (K n)) * altEDecay d n Db εE) +
        ((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVAlt d E s v K n k 𝔠 τ' Dq C' (2 * (Γ n * (Γ n * Λ n)))
            (Γ n * (Γ n * Λ n) * ((d.size n : ℕ) : ℝ) + 1) (K n) a j : ℝ)) +
        ((d.size n : ℕ) : ℝ) ^ (-D_Y) +
        ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          qErrQN d E s v K n k (((d.size n : ℕ) : ℝ) ^ τK *
            (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) j := by
      refine hb.trans ?_
      have h1 : kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n 0) (gridTime s v K n (K n)) *
          Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) ≤
          kapQ4 (d.L n) k ((d.W n : ℝ) ^ τ') (gridTime s v K n 0) (gridTime s v K n (K n)) *
            altE0Level d n E s k τ' Db εE := mul_le_mul_of_nonneg_left hsup hk0
      linarith
    linarith [hnorm, hT1, hT2, hb']


end Compositions

/-! ## 4. The hypotheses of the alternating endpoint -/

section Pins

/-- The conclusion of `AltLevelsQ` (the two level hypotheses of `altQPartGridT`). -/
def AltLevelsQConcl (E s v : ℕ → ℝ) (k : ℕ) [NeZero k] (Φ : ℕ → ℝ) (τ' Db : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1.1 0 p.2.2‖)
      (fun n _ _ => altQ0Level (d.L n) (d.W n) (E n) (s n) k τ' Db) ∧
  ∀ m : Fin 6, m ≠ 0 → PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖)
      (fun n p _ => altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (p.1 : ℝ))

/-- **The hypothesis `AltLevelsQ`**: the per-time stochastic levels of the `ℚ` tensors, i.e.
the two level hypotheses of `altQPartGridT`: `‖𝒬_s B_0‖ ≺ altQ0Level` at the time `s` only
(`InitLK` of ranks `k` and `k-1`, `InitDecay`, `B45_P_vartheta_le`), and `‖𝒬_u B_m‖ ≺ altQLevel`
for `m = 1..5`, `u ∈ [s,v]` (the clauses (D1)-(D3), (V), (Dec) of `GoodSetN` through
`driftTensor_norm_le_of_goodSet`-type lemmas, `B45_core_det_pub` for `m = 4, 5`, `qopNorm`,
`qopDecay`; the good set holds per time with probability `1 - N^{-D}`).  The levels carry
`Φ n` (the `STOeqPT` level of the lower ranks), not `Λ`. -/
def AltLevelsQ (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) → STOeqLevels d E s t k Λ Φ →
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ τ' Db : ℝ, 0 < τ' → 0 < Db →
  AltLevelsQConcl d E s v k Φ τ' Db

/-- **The hypothesis `AltLevelsE`**: the deterministic `𝔼` levels (sup bound and window decay) of
`e_0 = 𝒬_s 𝔼 B_0` and of the `𝔼` drift at every `u ∈ [s_n, v_n]`, for every alternating `σ`
(`≺ ⇒ 𝔼`: `AltDriftQ_norm_integral_le` with the crude bound `N^{4k+7}` of
`AltDriftQ_norm_altQB_le`, from the levels of `AltLevelsQ` and their far-label analogue). -/
def AltLevelsE (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) → STOeqLevels d E s t k Λ Φ →
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ τ' Db εE : ℝ, 0 < τ' → 0 < Db → 0 < εE →
  ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, Alternating σ → AltELevelsAt d n E s v k σ τ' Db εE (Φ n)

end Pins

/-! ## 5. The last step `𝓛-𝒦 = 𝒬(𝓛-𝒦) + 𝒫(𝓛-𝒦) ϑ` on the good set (`kolkisaf`)

The elementary lemmas `AltEnd_loopOf_eq`, `AltEnd_lk_le_xiLK` convert a loop index into the data of
`lkGen` and bound `‖LKf‖` by `xiLK`; `AltEnd_far_list` transfers a bound at far labels to loop
indices with two far labels; then `B45_P_vartheta_le` is applied with `hX`, `hBf` read off the
clauses (G2) and (Dec) of `GoodSetN`. -/

section LastStep

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem AltEnd_loopOf_eq (J : LoopIdx (Z2 L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

private theorem AltEnd_lk_le_xiLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {m : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m) :
    ‖LKf L W E u M J‖ ≤ xiLK L W E u M m * (scaleM L W E u)⁻¹ ^ m := by
  subst hlen
  have hJeq := AltEnd_loopOf_eq J hJ
  have h1 : ‖LKf L W E u M J‖ = lkGen L W E u M
      (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) := by
    unfold lkGen LKf LLf; rw [hJeq]
  have h2 := Finset.le_sup'
    (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) => lkGen L W E u M p.1 p.2)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))
  have hM : scaleM L W E u ^ J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow]
  calc ‖LKf L W E u M J‖ = _ := h1
    _ ≤ _ := h2
    _ = Finset.univ.sup' Finset.univ_nonempty
          (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Z2 L) =>
            lkGen L W E u M p.1 p.2) *
        (scaleM L W E u ^ J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length) := by
          rw [hM, mul_one]
    _ = xiLK L W E u M J.a.length * (scaleM L W E u)⁻¹ ^ J.a.length := by
          unfold xiLK; ring

private theorem AltEnd_far_list {m : ℕ} {R Bf : ℝ} (F : LoopIdx (Z2 L) → ℂ)
    (h : ∀ (σ' : Fin m → Bool) (a' : Fin m → Z2 L),
      R ≤ (KLoop.maxDist L a' : ℝ) → ‖F (loopOf σ' a')‖ ≤ Bf)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m)
    (hfar : ∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) : ‖F J‖ ≤ Bf := by
  subst hlen
  have hJeq := AltEnd_loopOf_eq J hJ
  rw [← hJeq]
  refine h _ _ ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := hfar
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  refine le_trans hxy ?_
  exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
    zdist2 L (J.a[q.1.1] - J.a[q.2.1])) (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length)))

/-- **The last-step level** (`jywiiwsoks`, `kolkisaf`): the right side of
`B45_P_vartheta_le` at `R = ℓ_u W^{τ'}`, `X = Γ Φ M_u^{-(k-1)}` (the level of `Ξ_{k-1}`, clause (G2) of
`GoodSetN`), `B_f = W^{-D'}` (clause (Dec)). -/
def altLastLevel (L W : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ τ' D' : ℝ) : ℝ :=
  ((W : ℝ) ^ 2 * etaT E u)⁻¹ *
    (((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2) ^ (k - 2) *
        (Γ * Φ * (scaleM L W E u)⁻¹ ^ (k - 1)) + ((L : ℝ) ^ 2) ^ (k - 2) * (W : ℝ) ^ (-D')) *
    ((180 * 40002 ^ 2) * (1 + Real.log L) * (ellT L u ^ 2)⁻¹) ^ (k - 1)

/-- **The last step on the good set**: for `M ∈ GoodSetN(u)` and alternating `σ`,
`|(𝒫(𝓛-𝒦)_{u,σ})_{a₁} ϑ_{u,a}| ≤ altLastLevel` (`B45_P_vartheta_le`). -/
theorem altLastStep_of_goodSet (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {k : ℕ} [NeZero k] (hk : 2 ≤ k) {Γ Λ Φ τ' D' : ℝ}
    (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (hτ' : 0 ≤ τ') {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τ' D') {σ : Fin k → Bool} (hσ : Alternating σ)
    (a : Fin k → Z2 L) :
    ‖Psum L (lkTensor L W E u M σ) (a 0) * vartheta L u a‖ ≤ altLastLevel L W E u k Γ Φ τ' D' := by
  have hMh : M.IsHermitian := hM.1
  have hLp : 1 ≤ L := by omega
  have hMpos := scaleM_pos hLp hW hE hu1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hR0 : 0 ≤ ellT L u * (W : ℝ) ^ τ' := by
    have := (ellT_pos_le hLp hu1).1
    positivity
  have hX0 : 0 ≤ Γ * Φ * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hMpos.le
    positivity
  have hBf0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  obtain ⟨-, -, hG2, -, -, hDec, -⟩ := hM
  have hxi : xiLK L W E u M (k - 1) ≤ Γ * Φ := hG2 (k - 1) (by omega) (by omega)
  have hXl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      ‖LKf L W E u M J‖ ≤ Γ * Φ * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    intro J hJ hlen
    have h := AltEnd_lk_le_xiLK E u M hMpos J hJ hlen
    exact h.trans (mul_le_mul_of_nonneg_right hxi (by
      have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hMpos.le
      positivity))
  have hBl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, ellT L u * (W : ℝ) ^ τ' ≤ (zdist2 L (x - y) : ℝ)) →
      ‖LKf L W E u M J‖ ≤ (W : ℝ) ^ (-D') := by
    intro J hJ hlen hfar
    refine AltEnd_far_list (m := k - 1) (LKf L W E u M) (fun σ' a' hfa => ?_) J hJ hlen hfar
    have h := hDec (k - 1) (by omega) (by omega) σ' a' hfa
    have h0 : 0 ≤ loopAbs L W E u M σ' a' := norm_nonneg _
    have : ‖LKf L W E u M (loopOf σ' a')‖ = lkGen L W E u M σ' a' := rfl
    rw [this]; linarith
  have h := B45_P_vartheta_le hL hW hE hu0 hu1 hMh hk hσ hR0 hX0 hBf0 hXl hBl a
  exact h

end LastStep

/-! ## 6. The budget and absorption hypotheses -/

section Budget

/-- **The numerical absorptions of the budget** at one size `n` (the analogue of the hypotheses
`ha1`-`ha3`, `he1`-`he5` of `budgetNonAlt`): five main terms against
`N^{ε₀}/10` and eight far terms (multiplied by `N^k ≥ M_v^{k}`, the inverse of the level) against
`N^{ε₀}/20`.  Notation: `x = 2(k-1)τ'`, `L_s = (Im m)^{-1} log N`, `C₄ = altC4`, `C₄e = altC4e`,
`A = altQvA`, `B = altQvB`, `W_d = W^{-D_q+C'}`. -/
structure AltBudgetHyp (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k]
    (𝔠 τ' Dq C' Db εq εE ε ε₀ D_Y D_t : ℝ) (Γ Λ : ℕ → ℝ) : Prop where
  ha1 : ((d.size n : ℕ) : ℝ) ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 10
  ha2 : 5 * (((d.size n : ℕ) : ℝ) ^ εq * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 10
  ha3 : altC4 (d.L n) (d.W n) k τ' *
      (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 10
  ha4 : 5 * altC4 (d.L n) (d.W n) k τ' *
      (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (2 * ((k : ℝ) - 1) * τ')) *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 10
  ha5 : ((d.size n : ℕ) : ℝ) ^ ε * (Γ n * Real.sqrt (2 * (k : ℝ) * altQvA (d.L n) (d.W n) k 𝔠 τ' *
      ((spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) + 1))) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 10
  he1 : ((d.size n : ℕ) : ℝ) ^ k * ((((d.size n : ℕ) : ℝ) ^ εq * ((d.size n : ℕ) : ℝ) ^ k + 1) *
      (d.W n : ℝ) ^ (-Db)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he2 : ((d.size n : ℕ) : ℝ) ^ k * ((5 * (((d.size n : ℕ) : ℝ) ^ εq * ((d.size n : ℕ) : ℝ) ^ k) + 1) *
      (d.W n : ℝ) ^ (-Db)) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he3 : ((d.size n : ℕ) : ℝ) ^ k * altShiftTerm s v K n k ((d.size n : ℕ) : ℝ) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he4 : ((d.size n : ℕ) : ℝ) ^ k * ((altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he5 : ((d.size n : ℕ) : ℝ) ^ k * ((5 * altC4 (d.L n) (d.W n) k τ' + altC4e (d.L n) k) *
      ((d.size n : ℕ) : ℝ) ^ k * (((d.size n : ℕ) : ℝ) ^ εE * (d.W n : ℝ) ^ (-Db))) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he6 : ((d.size n : ℕ) : ℝ) ^ ε * (((d.size n : ℕ) : ℝ) ^ k * Real.sqrt ((k : ℝ) *
      ((altQvA (d.L n) (d.W n) k 𝔠 τ' + altQvB (d.L n) k (Γ n * (Γ n * Λ n) * ((d.size n : ℕ) : ℝ) + 1)) *
        ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-Dq + C')))) ≤
    ((d.size n : ℕ) : ℝ) ^ ε₀ / 20 * Λ n ^ ((1 : ℝ) / 2)
  he7 : ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20
  he8 : ((d.size n : ℕ) : ℝ) ^ k * ((d.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((d.size n : ℕ) : ℝ) ^ ε₀ / 20

/-- **The hypothesis `BudgetAlt` (the analogue of `budgetNonAlt`)**: at a fixed size index `n`,
`assembledRHSAlt ≤ (9/10) N^{ε₀} (Λ^{1/2} + Φ) M_v^{-k}` under the regime facts (`|E| < 2`, the
window, `K ≥ 1`, `M_v ≥ 1`, `η_v^{-1} ≤ N`, `ΔN ≤ 1`), the levels (`Λ ≥ 1`, `Φ ≥ 0`, `Γ ≥ 0`), the
two inputs `hlog` (`sum_gridStep_div_etaT_le`), `hR` (`sum_weighted_qErrQN_le` at
`m = K n`) and the absorptions `AltBudgetHyp`.  Proof (in `RBM2D.Induction.AltBudget`):
`tbInitQPart`, `tbDriftQPart`, the `𝔼`-part drift budget, `tbQv` (via `NonAltBudget_qvShape`), the
`sqrt` split of `budgetNonAlt` `T4`. -/
def BudgetAlt : Prop :=
  ∀ (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k], 2 ≤ k →
  ∀ (𝔠 τ' Dq C' Db εq εE ε ε₀ D_Y D_t τK : ℝ) (Γ Λ Φ : ℕ → ℝ) (a : Fin k → Z2 (d.L n)),
    |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → 1 ≤ K n →
    1 ≤ scaleM (d.L n) (d.W n) (E n) (v n) →
    (etaT (E n) (v n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) →
    gridStep s v K n * ((d.size n : ℕ) : ℝ) ≤ 1 →
    1 ≤ Λ n → 0 ≤ Φ n → 0 ≤ Γ n →
    ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (spectralM (E n)).im⁻¹ * Real.log ((d.size n : ℕ) : ℝ) →
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
      qErrQN d E s v K n k (((d.size n : ℕ) : ℝ) ^ τK *
        (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) j ≤ ((d.size n : ℕ) : ℝ) ^ (-D_t) →
    AltBudgetHyp d E s v K n k 𝔠 τ' Dq C' Db εq εE ε ε₀ D_Y D_t Γ Λ →
    assembledRHSAlt d E s v K n k 𝔠 τ' Dq C' Db εq εE ε D_Y τK Φ (2 * (Γ n * (Γ n * Λ n)))
        (Γ n * (Γ n * Λ n) * ((d.size n : ℕ) : ℝ) + 1) a ≤
      9 / 10 * (((d.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
        (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k)

end Budget

/-! ## 7. The exponents chosen by the assembly and the absorption hypothesis -/

section Absorb

/-- The unit loss `δ = ε/100`: `ε_q = ε_E = ε_{Az} = ε₁ = δ` (the losses of the `ℚ` events, of
`≺ ⇒ 𝔼`, of Azuma and of the good set `Γ = N^{ε₁}`). -/
def altDelta (ε : ℝ) : ℝ := ε / 100

/-- The window exponent `τ' = δ/(4k + C_k(𝔠) + 1)` (`C_k(𝔠) = cPrec 𝔠 k = 4k + 4 + 4k/𝔠`): the
quadratic-variation constant `A` carries `W^{(4k + 2 C_k)τ'}`. -/
def altTau (c : ℝ) (k : ℕ) (ε : ℝ) : ℝ := altDelta ε / (4 * k + cPrec c k + 1)

/-- The decay exponent of the levels and of the `ℚ` events, `c D_b = 4k + 8`. -/
def altDb (c : ℝ) (k : ℕ) : ℝ := (4 * k + 8) / c

/-- The decay exponent of the variance form, `D_q = C' + (8k + 10)/c`. -/
def altDq (c : ℝ) (k : ℕ) (C' : ℝ) : ℝ := C' + (8 * k + 10) / c

/-- The grid exponent `C_K` (the lower bounds required by the absorptions). -/
def altCK (c : ℝ) (k : ℕ) (D₁ C_P C' : ℝ) : ℝ :=
  D₁ + 2 * C_P + 10 * k + 40 + C' + (4 * k + 5) / c

/-- The conclusion of `AltAbsorb` at one size index. -/
def AltAbsorbConcl (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k] (c ε C' : ℝ)
    (Λ Φ : ℕ → ℝ) : Prop :=
  AltBudgetHyp d E s v K n k c (altTau c k ε) (altDq c k C') C' (altDb c k) (altDelta ε)
        (altDelta ε) (altDelta ε) ε ((k : ℝ) + 1) ((k : ℝ) + 1)
        (fun n => ((d.size n : ℕ) : ℝ) ^ (altDelta ε)) Λ ∧
      altLastLevel (d.L n) (d.W n) (E n) (v n) k (((d.size n : ℕ) : ℝ) ^ (altDelta ε)) (Φ n)
          (altTau c k ε) (altDq c k C' + 1) ≤
        ((d.size n : ℕ) : ℝ) ^ ε / 10 * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
          (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k

/-- **The hypothesis `AltAbsorb` (the analogue of the lemmas `NonAltEnd_ev_ha1`-`NonAltEnd_ev_he5`)**:
at the exponents of `altDelta`, `altTau`, `altDb`, `altDq`, `altCK`, eventually in `n`, the
numerical absorptions of `BudgetAlt` hold (with `ε₀ = ε`, `Γ = N^δ`, `D_Y = D_t = k+1`, `τ_K = 1`),
together with the absorption of the last-step level `altLastLevel` against `(N^ε/10) (Λ^{1/2} + Φ)
M_v^{-k}`.  Premises: the size, bandwidth and range hypotheses of `MainIndHyp`, `Λ ≥ 1`, `D₁, C_P, C' ≥ 0`. -/
def AltAbsorb : Prop :=
  ∀ (κ c τR : ℝ) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) [NeZero k], 2 ≤ k → 0 < κ → 0 < c → 0 < τR →
  (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) →
  (∀ n, K n ≠ 0) → SizeTendsto d → Bandwidth d c → RangeCond d τR v →
  ∀ (Λ Φ : ℕ → ℝ), (∀ n, 0 ≤ Φ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
  ∀ (ε D₁ C_P C' : ℝ), 0 < ε → 0 ≤ D₁ → 0 ≤ C_P → 0 ≤ C' →
  (∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (altCK c k D₁ C_P C') ≤ (K n : ℝ)) →
  ∀ᶠ n : ℕ in atTop, AltAbsorbConcl d E s v K n k c ε C' Λ Φ

end Absorb

/-! ## 8. The assembly `altGridEnd_of_pins` -/

section Main

/-- The union bound over the `≤ 2^k` alternating sign vectors and the `ℚ` event:
`(2^k + 1) N^{-(D+1)} ≤ N^{-D}` eventually. -/
theorem AltEnd_ev_union (hsize : SizeTendsto d) (k : ℕ) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ k + 1) * ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤
      ((d.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [hsize.eventually_ge_atTop ((2 : ℝ) ^ k + 1), hsize.eventually_ge_atTop 1] with
    n hn hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  rw [show (-(D + 1)) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc ((2 : ℝ) ^ k + 1) * (((d.size n : ℕ) : ℝ) ^ (-D) * ((d.size n : ℕ) : ℝ)⁻¹)
      = ((d.size n : ℕ) : ℝ) ^ (-D) * (((2 : ℝ) ^ k + 1) / ((d.size n : ℕ) : ℝ)) := by ring
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ h
        rw [div_le_one hN0]; exact hn
    _ = _ := mul_one _

/-- **`altGridEnd_of_pins`: the four hypotheses imply `AltGridEnd`** (the pattern of
`nonAltGridEnd`).  Hypotheses: `AltLevelsQ`, `AltLevelsE`, `BudgetAlt`, `AltAbsorb`; proved in this
file: the last step (`altLastStep_of_goodSet`), the assembly (`altEnd_assembly`), the kernel shift,
the variance form after the shift, the envelope of the remainder, the `Y` moments for all signs;
used from other files: `altQPartGridT`, `assembledN`, `stoppedDuhamelQN`, `azumaSubGQ_goodExit`,
`yMomentsQUnifN`, `sum_weighted_qErrQN_le`, `sum_gridStep_div_etaT_le`, `NonAltEnd_ev_hδ`.  Paper:
`lem:STOeq_Qt`, `int_K-L+Q2`, `int_K-L+QQ`, `int_K-L+QE`, `eq:case4_B`. -/
theorem altGridEnd_of_pins (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ)
    (hP1 : AltLevelsQ d κ c τ C E s t) (hP2 : AltLevelsE d κ c τ C E s t)
    (hBud : BudgetAlt d) (hAbs : AltAbsorb d) : AltGridEnd d κ c τ C E s t := by
  intro hU hmain hloc hdec hG4 hLF hSym k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt ε hε D₁ hD₁
  classical
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, hinit, -, -⟩ := hmain'
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : RangeCond d (min τ 1) v := NonAltEnd_rangeCond_mono d (min_le_left _ _) hvt hrange
  -- the constants `C_P` (before the grid) and `C'` (variance form)
  obtain ⟨Cmax, hCmax0, hYmax⟩ := altEnd_yMomentsMax (d := d) hκ hE hs0 hsv hv1 hsize hrangeV k
  have hδ0 : 0 < altDelta ε := by unfold altDelta; linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcP : 0 ≤ cPrec c k := by unfold cPrec; positivity
  have hτ'0 : 0 < altTau c k ε := by unfold altTau; positivity
  obtain ⟨C', hC'0, hQVev⟩ := altQvShift_eventually c hc k hk (altTau c k ε) hτ'0
  have hDb0 : 0 < altDb c k := by unfold altDb; positivity
  have hDq0 : 0 ≤ altDq c k C' := by unfold altDq; positivity
  have hDqC : C' < altDq c k C' := by unfold altDq; have : 0 < (8 * (k : ℝ) + 10) / c := by positivity
                                      linarith
  have hCK0 : 0 ≤ altCK c k D₁ Cmax C' := by unfold altCK; positivity
  refine ⟨altDelta ε, altTau c k ε, altDq c k C' + 1, altCK c k D₁ Cmax C', hδ0, hτ'0,
    by linarith, hCK0, ?_⟩
  intro K hK0 hKN hKU
  have hs1 : ∀ n, s n < 1 := fun n => (hsv n).trans_lt (hv1 n)
  have hu1 : ∀ n (u : ℝ), u ≤ v n → u < 1 := fun n u hu => hu.trans_lt (hv1 n)
  -- the `ℚ` levels (`AltLevelsQ`) and the event of `altQPartGridT`
  obtain ⟨hlev0, hlevq⟩ := hP1 hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt
    (altTau c k ε) (altDb c k) hτ'0 hDb0
  have hlevq' : ∀ m : Fin 6, m ≠ 0 → PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖)
      (fun n p _ => (fun (_ : Fin 6) (n : ℕ) (u : ℝ) => max 0 (altQLevel (d.L n) (d.W n) (E n) k
        (altTau c k ε) (altDb c k) (Φ n) u)) m n (p.1 : ℝ)) := by
    intro m hm
    have h := hlevq m hm
    have hfun : (fun (n : ℕ) (p : TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} ×
          (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) => (fun (_ : Fin 6) (n : ℕ) (u : ℝ) =>
            max 0 (altQLevel (d.L n) (d.W n) (E n) k (altTau c k ε) (altDb c k) (Φ n) u)) m n
            (p.1 : ℝ)) =
        fun n p _ => altQLevel (d.L n) (d.W n) (E n) k (altTau c k ε) (altDb c k) (Φ n)
          (p.1 : ℝ) := by
      funext n p ω
      exact max_eq_right (AltEndCompose_altQLevel_nonneg (hE2 n) (hu1 n _ p.1.2.2) k _ _ _ (hΦ0 n))
    rw [hfun]
    exact h
  have hQ := altQPartGridT d κ c τ C E s t hU hmain hloc hdec k hk v hsv hvt
    (fun n => altQ0Level (d.L n) (d.W n) (E n) (s n) k (altTau c k ε) (altDb c k))
    (fun n => AltEndCompose_altQ0Level_nonneg (hE2 n) (hs1 n) k _ _) hlev0
    (fun (_ : Fin 6) (n : ℕ) (u : ℝ) => max 0 (altQLevel (d.L n) (d.W n) (E n) k
      (altTau c k ε) (altDb c k) (Φ n) u)) (fun _ _ _ => le_max_left _ _) hlevq'
    (altDelta ε) hδ0 (altDb c k) (D₁ + 1) (altCK c k D₁ Cmax C') hDb0 (by linarith) hCK0 K hK0 hKU
  -- the numerical absorptions
  have hθ0 : 0 ≤ 1 - min τ 1 := by linarith
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  have hcpos : 0 < (4 * (k : ℝ) + 5) / c := by positivity
  have hrow1 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * (((k : ℝ) + 1) + k) <
      altCK c k D₁ Cmax C' := by
    have h := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 4 * (k : ℝ) + 8) hθ1
    unfold altCK; nlinarith
  have hrow2 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + (((k : ℝ) + 1) + k) <
      altCK c k D₁ Cmax C' := by
    have h := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 5 * (k : ℝ)) hθ1
    unfold altCK; nlinarith
  have hrow3 : 2 * (1 - min τ 1) + (1 : ℝ) + 2 * (k : ℝ) * (1 - min τ 1) + (((k : ℝ) + 1) + k) <
      altCK c k D₁ Cmax C' := by
    have h := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)) hθ1
    unfold altCK; nlinarith
  have hrow4 : 1 - min τ 1 < altCK c k D₁ Cmax C' := by
    unfold altCK; nlinarith
  have hrowδ : 1 + (2 * (k : ℝ) + 3) * (1 - min τ 1) + altDq c k C' / 2 < altCK c k D₁ Cmax C' := by
    have h := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) + 3) hθ1
    have hDq2 : altDq c k C' / 2 = C' / 2 + (4 * (k : ℝ) + 5) / c := by
      unfold altDq; ring
    rw [hDq2]; unfold altCK; nlinarith
  have hCKA : (D₁ + 1) + 4 * ((k : ℝ) + 1) + (k : ℝ) + 2 * Cmax + 8 ≤ altCK c k D₁ Cmax C' := by
    unfold altCK; nlinarith
  have hC1 : 1 ≤ altCK c k D₁ Cmax C' := by unfold altCK; nlinarith
  -- the eventual facts
  have hΓ1 : ∀ n, 1 ≤ ((d.size n : ℕ) : ℝ) ^ (altDelta ε) := fun n =>
    Real.one_le_rpow (GoodEvent_one_le_size n) hδ0.le
  have hLE := hP2 hU hmain hloc hdec k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt (altTau c k ε)
    (altDb c k) (altDelta ε) hτ'0 hDb0 hδ0
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hQVn := hsizeN.eventually (hQVev (altDq c k C') hDqC)
  have hηev := NonAltEnd_ev_hη d hsize hκ hE hτR hrangeV
  have hM1ev := NonAltEnd_ev_hM1 d hsize hκ hE hc hτR hv1 hband hrangeV
  have hδev := NonAltEnd_ev_hδ d hsize (c := c) (τR := min τ 1) (C_K := altCK c k D₁ Cmax C')
    (D'' := altDq c k C') k hκ (E := E) (s := s) (v := v) (K := K) hE hc hs0 hsv hv1 hband
    hrangeV hDq0 hrowδ hKN
  have hGsev : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-altDq c k C') ≤
      ((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n) := by
    filter_upwards [hband, hΛ1, hsize.eventually_ge_atTop 1] with n hW hΛn hN1
    have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have hWn := NonAltEnd_Wneg_le hN0 hW hDq0
    have hcD : (2 * (k : ℝ)) ≤ c * altDq c k C' := by
      unfold altDq
      have : c * ((8 * (k : ℝ) + 10) / c) = 8 * k + 10 := by field_simp
      nlinarith [mul_nonneg hc.le hC'0]
    have h1 : ((d.size n : ℕ) : ℝ) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (-(c * altDq c k C')) ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by push_cast; linarith)
    have hΓΛ : 1 ≤ ((d.size n : ℕ) : ℝ) ^ (altDelta ε) *
        (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n) := by
      have h1' := hΓ1 n
      exact one_le_mul_of_one_le_of_one_le h1' (one_le_mul_of_one_le_of_one_le h1' hΛn)
    calc ((d.size n : ℕ) : ℝ) ^ (2 * k) * (d.W n : ℝ) ^ (-altDq c k C') ≤
          ((d.size n : ℕ) : ℝ) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (-(c * altDq c k C')) :=
          mul_le_mul_of_nonneg_left hWn (by positivity)
      _ ≤ 1 := h1
      _ ≤ _ := hΓΛ
  have hAsm := altEnd_assembly (d := d) k hk hκ hE hs0 hsv hv1 hK0 hsize
    (fun n => ((d.size n : ℕ) : ℝ) ^ (altDelta ε)) Λ Φ hΓ1 hΛ0 hΦ0 (𝔠 := c)
    (τ' := altTau c k ε) (Dq := altDq c k C') (C' := C') (D_Y := (k : ℝ) + 1) (τK := 1)
    (εq := altDelta ε) (εE := altDelta ε) (ε := altDelta ε) (Db := altDb c k) (D₁ := D₁ + 1)
    (C_P := Cmax) (C_K := altCK c k D₁ Cmax C') hτ'0.le one_pos hδ0 hDq0 hCK0 hCKA hKN hKU
    (fun σ => hYmax K hK0 σ) hQVn hband hδev hGsev hηev hM1ev hLE
  have hlogev := sum_gridStep_div_etaT_le hτR hE2 hs0 hsv hv1 hK0 hrangeV
  have hRev := sum_weighted_qErrQN_le d (E := E) (s := s) (t := v) (K := K) k hκ hτR hτR1
    one_pos (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hk hsize hE hs0 hsv hv1 hK0 hrangeV hrow1
    hrow2 hrow3 hrow4 hKN
  have hAbsEv := hAbs κ c (min τ 1) (E := E) (s := s) (v := v) (K := K) k hk hκ hc hτR hE hs0
    hsv hv1 hK0 hsize hband hrangeV Λ Φ hΦ0 hΛ1 ε D₁ Cmax C' hε hD₁.le hCmax0 hC'0 hKN
  have hunion := AltEnd_ev_union d hsize k D₁
  filter_upwards [hAsm, hQ, hAbsEv, hunion, hlogev, hRev, hηev, hM1ev, hKN, hΛ1,
    hsize.eventually_ge_atTop 1] with n hAsmn hQn hAbsn hunn hlogn hRn hηn hM1n hKNn hΛ1n hN1
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact NonAltEnd_collapse d (hE2 n) (hv1 n) hsvn (by unfold altDelta; linarith) hΛ1n (hΦ0 n)
        ω σ a (hinit' σ hσ a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
    have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
    have hΔN := NonAltEnd_hΔN d hC1 hKNn hvs
    -- the events, one per alternating sign vector
    have hAsmσ : ∀ σ : {σ : Fin k → Bool // Alternating σ}, ∃ G : Set (PathΩ d),
        (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) ∧ ∀ ω ∈ G,
          (∀ j ≤ K n, pathH d s v K n j ω ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k
            (((d.size n : ℕ) : ℝ) ^ (altDelta ε)) (Λ n) (Φ n) (altTau c k ε) (altDq c k C' + 1)) →
          (∀ a : Fin k → Z2 (d.L n),
            ‖Ugen (d.L n) (E n) σ.1 (gridTime s v K n 0) (gridTime s v K n (K n))
                (fun b => aTrueQN d E s v K n σ.1 0 ω b - expAltQB d E n (s n) σ.1 0 b) a‖ ≤
              ((d.size n : ℕ) : ℝ) ^ (altDelta ε) *
                  altQ0Level (d.L n) (d.W n) (E n) (s n) k (altTau c k ε) (altDb c k) *
                  ratioR (d.L n) (E n) (s n) (gridTime s v K n (K n)) ^ k +
                (d.W n : ℝ) ^ (-altDb c k)) →
          (∀ j < K n, ∀ a : Fin k → Z2 (d.L n),
            ‖Ugen (d.L n) (E n) σ.1 (gridTime s v K n j) (gridTime s v K n (K n))
                (fun b => dGridQN d E s v K n σ.1 j ω b -
                  expDriftQN d E n (gridTime s v K n j) σ.1 b) a‖ ≤
              ((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (5 * altQLevel (d.L n) (d.W n) (E n) k
                  (altTau c k ε) (altDb c k) (Φ n) (gridTime s v K n j)) *
                ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-altDb c k)) →
          ∀ a : Fin k → Z2 (d.L n), ‖aTrueQN d E s v K n σ.1 (K n) ω a‖ ≤
            assembledRHSAlt d E s v K n k c (altTau c k ε) (altDq c k C') C' (altDb c k)
              (altDelta ε) (altDelta ε) (altDelta ε) ((k : ℝ) + 1) 1 Φ
              (2 * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n)))
              (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n) *
                ((d.size n : ℕ) : ℝ) + 1) a :=
      fun σ => hAsmn σ.1 σ.2 hlt
    choose Gs hGsP hGsb using hAsmσ
    obtain ⟨GQ, hGQP, hGQb⟩ := hQn
    refine ⟨GQ ∩ ⋂ σ, Gs σ, ?_, ?_⟩
    · -- the union bound over the `≤ 2^k` alternating sign vectors and the `ℚ` event
      have hcompl : (GQ ∩ ⋂ σ, Gs σ)ᶜ = GQᶜ ∪ ⋃ σ, (Gs σ)ᶜ := by
        rw [Set.compl_inter, Set.compl_iInter]
      rw [hcompl]
      have hcard : (Fintype.card {σ : Fin k → Bool // Alternating σ} : ℝ) ≤ (2 : ℝ) ^ k := by
        have h1 := Fintype.card_subtype_le (fun σ : Fin k → Bool => Alternating σ)
        have h2 : Fintype.card (Fin k → Bool) = 2 ^ k := by simp
        rw [h2] at h1
        exact_mod_cast h1
      calc (pathP d).real (GQᶜ ∪ ⋃ σ, (Gs σ)ᶜ)
          ≤ (pathP d).real GQᶜ + (pathP d).real (⋃ σ, (Gs σ)ᶜ) := measureReal_union_le _ _
        _ ≤ ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) +
              ∑ σ : {σ : Fin k → Bool // Alternating σ}, (pathP d).real (Gs σ)ᶜ :=
            add_le_add hGQP (measureReal_iUnion_fintype_le _)
        _ ≤ ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) +
              ∑ _σ : {σ : Fin k → Bool // Alternating σ}, ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) :=
            add_le_add le_rfl (Finset.sum_le_sum fun σ _ => hGsP σ)
        _ = (1 + (Fintype.card {σ : Fin k → Bool // Alternating σ} : ℝ)) *
              ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp; ring
        _ ≤ ((2 : ℝ) ^ k + 1) * ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
            linarith
        _ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ hσ a
      have hωQ : ω ∈ GQ := hω.1
      have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω.2 ⟨σ, hσ⟩
      have hQi : ∀ a' : Fin k → Z2 (d.L n),
          ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n (K n))
              (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a'‖ ≤
            ((d.size n : ℕ) : ℝ) ^ (altDelta ε) *
                altQ0Level (d.L n) (d.W n) (E n) (s n) k (altTau c k ε) (altDb c k) *
                ratioR (d.L n) (E n) (s n) (gridTime s v K n (K n)) ^ k +
              (d.W n : ℝ) ^ (-altDb c k) :=
        fun a' => (hGQb ω hωQ σ hσ (K n) le_rfl a').1
      have hnn : ∀ j < K n, 0 ≤ altQLevel (d.L n) (d.W n) (E n) k (altTau c k ε) (altDb c k)
          (Φ n) (gridTime s v K n j) := fun j hj =>
        AltEndCompose_altQLevel_nonneg (hE2 n) ((GoodEvent_gridTime_le (K := K) (hsv n) hj.le).trans_lt
          (hv1 n)) k _ _ _ (hΦ0 n)
      have hQd : ∀ j < K n, ∀ a' : Fin k → Z2 (d.L n),
          ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n (K n))
              (fun b => dGridQN d E s v K n σ j ω b -
                expDriftQN d E n (gridTime s v K n j) σ b) a'‖ ≤
            ((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (5 * altQLevel (d.L n) (d.W n) (E n) k
                (altTau c k ε) (altDb c k) (Φ n) (gridTime s v K n j)) *
              ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n (K n)) ^ k +
            (d.W n : ℝ) ^ (-altDb c k) := by
        intro j hj a'
        have h := (hGQb ω hωQ σ hσ (K n) le_rfl a').2 j hj
        beta_reduce at h
        simp only [max_eq_right (hnn j hj)] at h
        calc _ ≤ _ := h
          _ = _ := by ring
      have hb0 := hGsb ⟨σ, hσ⟩ ω hωσ hgood hQi hQd a
      have hb : ‖aTrueQN d E s v K n σ (K n) ω a‖ ≤
          assembledRHSAlt d E s v K n k c (altTau c k ε) (altDq c k C') C' (altDb c k)
            (altDelta ε) (altDelta ε) (altDelta ε) ((k : ℝ) + 1) 1 Φ
            (2 * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n)))
            (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * (((d.size n : ℕ) : ℝ) ^ (altDelta ε) * Λ n) *
              ((d.size n : ℕ) : ℝ) + 1) a := hb0
      obtain ⟨hAbH, hlastH⟩ := hAbsn
      have hbud := hBud E s v K n k hk c (altTau c k ε) (altDq c k C') C' (altDb c k)
        (altDelta ε) (altDelta ε) (altDelta ε) ε ((k : ℝ) + 1) ((k : ℝ) + 1) 1
        (fun n => ((d.size n : ℕ) : ℝ) ^ (altDelta ε)) Λ Φ a (hE2 n) (hs0 n) (hsv n) (hv1 n) hK1
        hM1n hηn hΔN hΛ1n (hΦ0 n) (Real.rpow_nonneg hN0.le _) hlogn (hRn (K n) le_rfl) hAbH
      beta_reduce at hbud
      -- the last step
      have hKlast : gridTime s v K n (K n) = v n := gridTime_last s v K n (hK0 n)
      have hMK := hgood (K n) le_rfl
      have hlast := altLastStep_of_goodSet (L := d.L n) (W := d.W n) (d.three_le_L n)
        (d.W_pos n) (hE2 n) (GoodEvent_gridTime_nonneg (hs0 n) (hsv n) (K n))
        ((GoodEvent_gridTime_le (K := K) (hsv n) le_rfl).trans_lt (hv1 n)) hk
        (Real.rpow_nonneg hN0.le _) (hΦ0 n) hτ'0.le hMK hσ a
      have hAeq : AvecN d E s v K n (K n) σ ω a = aTrueQN d E s v K n σ (K n) ω a +
          Psum (d.L n) (lkTensor (d.L n) (d.W n) (E n) (gridTime s v K n (K n))
            (pathH d s v K n (K n) ω) σ) (a 0) * vartheta (d.L n) (gridTime s v K n (K n)) a := by
        have e : lkTensor (d.L n) (d.W n) (E n) (gridTime s v K n (K n))
            (pathH d s v K n (K n) ω) σ = AvecN d E s v K n (K n) σ ω := rfl
        rw [e]
        simp only [aTrueQN, Qop]
        ring
      have hlk : lkGen (d.L n) (d.W n) (E n) (v n) (pathH d s v K n (K n) ω) σ a =
          ‖AvecN d E s v K n (K n) σ ω a‖ := by
        simp only [AvecN, lkGen, hKlast]
      have hlastv : altLastLevel (d.L n) (d.W n) (E n) (gridTime s v K n (K n)) k
          (((d.size n : ℕ) : ℝ) ^ (altDelta ε)) (Φ n) (altTau c k ε) (altDq c k C' + 1) ≤
          ((d.size n : ℕ) : ℝ) ^ ε / 10 * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
            (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k := by
        rw [hKlast]; exact hlastH
      rw [hlk, hAeq]
      calc ‖aTrueQN d E s v K n σ (K n) ω a + Psum (d.L n) (lkTensor (d.L n) (d.W n) (E n)
              (gridTime s v K n (K n)) (pathH d s v K n (K n) ω) σ) (a 0) *
              vartheta (d.L n) (gridTime s v K n (K n)) a‖
          ≤ ‖aTrueQN d E s v K n σ (K n) ω a‖ + ‖Psum (d.L n) (lkTensor (d.L n) (d.W n) (E n)
              (gridTime s v K n (K n)) (pathH d s v K n (K n) ω) σ) (a 0) *
              vartheta (d.L n) (gridTime s v K n (K n)) a‖ := norm_add_le _ _
        _ ≤ 9 / 10 * (((d.size n : ℕ) : ℝ) ^ ε * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
              (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k) +
            ((d.size n : ℕ) : ℝ) ^ ε / 10 * (Λ n ^ ((1 : ℝ) / 2) + Φ n) *
              (scaleM (d.L n) (d.W n) (E n) (v n))⁻¹ ^ k := by
            refine add_le_add (hb.trans hbud) ?_
            exact hlast.trans hlastv
        _ = _ := by ring

end Main

end RBM.Ind
