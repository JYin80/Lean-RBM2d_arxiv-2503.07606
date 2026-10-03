/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltAbsorb
import RBM2D.Induction.MainInd
import RBM2D.Induction.PPClosure
import RBM2D.Induction.PPKernel
import RBM2D.Induction.PPDrift
import RBM2D.Induction.PPCondVar
import RBM2D.Induction.PPGoodEvent
import RBM2D.Evolution.Step61
import RBM2D.Evolution.MLExpDuhamel
import RBM2D.Universality.UnivMain

/-!
# `P7Out`, `P7ExpOut` from the stopped-evolution estimate

`PPTargetV2` holds for all data, from the seven `(+,+)` theorems; `P7Out` and `P7ExpOut` follow
from the universally closed estimate `STOAll` (`Ind.STOeqTargetV2` at all data), with the
`t`-modification (`t' < 1` everywhere versus the eventual range).  Namespace `RBM.Endpoints`.
Paper: arXiv:2503.07606, Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`, `ML:exp`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## Congruence of `PerTimeDomAt` -/

section Generic

/-- Congruence of `PerTimeDomAt` along an eventual pointwise identification. -/
theorem P7FromSTO_perTimeDomAt_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} {ξ ζ ξ' ζ' : ∀ l, U l → Ω → ℝ}
    (hξ : ∀ᶠ l in atTop, ∀ u ω, ξ l u ω = ξ' l u ω)
    (hζ : ∀ᶠ l in atTop, ∀ u ω, ζ l u ω = ζ' l u ω)
    (h : PerTimeDomAt P size ξ ζ) : PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hξ, hζ] with l hl hξl hζl u
  have : {ω | (size l : ℝ) ^ τ * ζ' l u ω < ξ' l u ω} =
      {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξl u ω, hζl u ω]
  rw [this]
  exact hl u


end Generic

/-! ## `PPTargetV2` unconditional, `P7Out` and `P7ExpOut` from `STOeqTargetV2` -/

section P7

/-- The universally closed form of `Ind.STOeqTargetV2`; the hypothesis of the endpoint
conversions of `EndpointsFromSTO`. -/
def STOAll : Prop :=
  ∀ (d : Sizes) (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ), Ind.STOeqTargetV2 d κ c τ C E s t

/-- `PPTargetV2` holds for all data, from the seven `(+,+)` theorems. -/
theorem ppTargetV2_all (d : Sizes) (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) :
    Ind.PPTargetV2 d κ c τ C E s t :=
  Ind.ppTargetV2_of_ppPins C E s t (fun v K => Ind.gridGoodPPN d κ c τ E s v t K)
    (Ind.ppKernelN κ) Ind.ppDriftN Ind.ppCondVarN
    (fun v K => Ind.ppDriftSumN d κ c τ E s v t K) (fun v K => Ind.ppQVSumN d κ c τ E s v t K)
    (Ind.ppArithN d κ c τ E s t)

theorem P7FromSTO_sizeTendsto {𝔠 : ℝ} {d : Sizes} (h : Admissible 𝔠 d) : Ind.SizeTendsto d :=
  tendsto_natCast_atTop_atTop.comp h.1

theorem P7FromSTO_bandwidth {𝔠 : ℝ} {d : Sizes} (h : Admissible 𝔠 d) : Bandwidth d 𝔠 := h.2

theorem P7FromSTO_size_pos (d : Sizes) (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 := d.W_pos n
  have h2 := d.three_le_L n
  have : 0 < d.size n := by
    unfold Sizes.size
    exact pow_pos (Nat.mul_pos h1 (by omega)) 2
  exact_mod_cast this

/-- The `t`-modification: a time sequence in range only eventually is replaced by `0` where the
range condition fails; `t' < 1` everywhere, `t' = t` eventually. -/
def P7FromSTO_tmod (d : Sizes) (τ : ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n then t n else 0

theorem P7FromSTO_tmod_props (d : Sizes) {τ : ℝ} {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (hR : RangeCond d τ t) :
    (∀ n, 0 ≤ P7FromSTO_tmod d τ t n) ∧ (∀ n, P7FromSTO_tmod d τ t n < 1) ∧
      (∀ᶠ n in atTop, t n = P7FromSTO_tmod d τ t n) ∧ RangeCond d τ (P7FromSTO_tmod d τ t) := by
  classical
  have hpos := fun n => Real.rpow_pos_of_pos (P7FromSTO_size_pos d n) (-1 + τ)
  refine ⟨fun n => ?_, fun n => ?_, hR.mono fun n hn => ?_, hR.mono fun n hn => ?_⟩
  · unfold P7FromSTO_tmod; split_ifs <;> [exact ht0 n; exact le_rfl]
  · unfold P7FromSTO_tmod
    split_ifs with h
    · have := hpos n; linarith
    · exact one_pos
  · simp [P7FromSTO_tmod, hn]
  · simp [P7FromSTO_tmod, hn]

/-- Congruence of `MLConcl` in the time sequence along an eventual identification. -/
theorem P7FromSTO_mlConcl_congr (d : Sizes) (E : ℕ → ℝ) {t t' : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, t n = t' n) (hML : Ind.MLConcl d E t') : Ind.MLConcl d E t := by
  obtain ⟨⟨hLK, hDec, hLoc⟩, hLoop⟩ := hML
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro k hk
    refine P7FromSTO_perTimeDomAt_congr ?_ ?_ (hLK k hk)
    · filter_upwards [h] with n hn u ω; rw [hn]
    · filter_upwards [h] with n hn u ω; rw [hn]
  · intro D hD
    refine P7FromSTO_perTimeDomAt_congr ?_ ?_ (hDec D hD)
    · filter_upwards [h] with n hn u ω; rw [hn]
    · filter_upwards [h] with n hn u ω; rw [hn]
  · refine P7FromSTO_perTimeDomAt_congr ?_ ?_ hLoc
    · filter_upwards [h] with n hn u ω; rw [hn]
    · filter_upwards [h] with n hn u ω; rw [hn]
  · intro k hk
    refine P7FromSTO_perTimeDomAt_congr ?_ ?_ (hLoop k hk)
    · filter_upwards [h] with n hn u ω; rw [hn]
    · filter_upwards [h] with n hn u ω; rw [hn]

/-- Congruence of `MLExpConcl` in the time sequence along an eventual identification. -/
theorem P7FromSTO_mlExpConcl_congr (d : Sizes) (E : ℕ → ℝ) {t t' : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, t n = t' n) (hML : Evol.MLExpConcl d E t') : Evol.MLExpConcl d E t := by
  intro ε hε
  filter_upwards [hML ε hε, h] with n hn htn σ a
  rw [htn]
  exact hn σ a

/-- **`P7Out`** from `STOAll`: `mlConcl_of_R3` at the modified time sequence, then the tail
congruence. -/
theorem p7Out_of_STOAll (hSTO : STOAll) : Univ.P7Out := by
  intro 𝔠 h𝔠 d hAdm κ hκ E hE τ hτ t ht0 hR
  obtain ⟨ht'0, ht'1, hev, hR'⟩ := P7FromSTO_tmod_props d ht0 hR
  exact P7FromSTO_mlConcl_congr d E hev
    (Ind.mlConcl_of_R3 d hκ h𝔠 hτ (P7FromSTO_sizeTendsto hAdm) (P7FromSTO_bandwidth hAdm)
      (fun E s t => hSTO d κ 𝔠 τ _ E s t) (fun E s t => ppTargetV2_all d κ 𝔠 τ _ E s t) E _ hE
      ht'0 ht'1 hR')

/-- **`P7ExpOut`** from `STOAll`: `mlExp` at the modified time sequence; its premises `Step4PT`
(`perTime_timeIcc_of_forall_seq` + `InitLK` of `MLConcl` at every section time),
`DecayLoopPT` (`decayLoopFromML`), `Step61Concl` (`step61` + `InitLK`) all come from `MLConcl`
at the sections `u ≤ t'` (`mlConcl_of_R3`), and `KboundConcl`, `SumDecayDetPrec` from
`upstreamSteps34Prec`. -/
theorem p7ExpOut_of_STOAll (hSTO : STOAll) : Univ.P7ExpOut := by
  intro 𝔠 h𝔠 d hAdm κ hκ E hE τ hτ t ht0 hR
  obtain ⟨ht'0, ht'1, hev, hR'⟩ := P7FromSTO_tmod_props d ht0 hR
  have hsz := P7FromSTO_sizeTendsto hAdm
  have hbw := P7FromSTO_bandwidth hAdm
  have hU := Ind.upstreamSteps34Prec d hκ h𝔠 hτ
  set t' := P7FromSTO_tmod d τ t with ht'
  have hML : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t' n) → Ind.MLConcl d E u :=
    fun u hu0 hut =>
      Ind.mlConcl_of_R3 d hκ h𝔠 hτ hsz hbw (fun E s t => hSTO d κ 𝔠 τ _ E s t)
        (fun E s t => ppTargetV2_all d κ 𝔠 τ _ E s t) E u hE hu0
        (fun n => (hut n).trans_lt (ht'1 n)) (Green.rangeCond_mono d hR' hut)
  have h4 : Ind.Step4PT d E (fun _ => 0) t' := by
    intro k hk
    exact Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size (s := fun _ => 0) (t := t')
      (fun n => ht'0 n) (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
      (fun n u v ω => Ind.lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2)
      (fun n u v _ => (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ k)
      (fun u hu => (hML u (fun n => (hu n).1) (fun n => (hu n).2)).1.1 k hk)
  have hDL : Evol.DecayLoopPT d E (fun _ => 0) t' :=
    Ind.decayLoopFromML d κ 𝔠 τ E t' hκ hE h𝔠 hτ ht'0 ht'1 hsz hbw hR' (Ind.kcalDecay κ) hU.2.1 hML
  have h61 : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t' n) → Evol.Step61Concl d E u :=
    fun u hu0 hut =>
      Evol.step61 d κ τ E u hκ hτ hE hu0 (fun n => (hut n).trans_lt (ht'1 n)) hsz
        (Green.rangeCond_mono d hR' hut) (hML u hu0 hut).1.1
  exact P7FromSTO_mlExpConcl_congr d E hev
    (Ind.mlExp d κ 𝔠 τ (Evol.cCase3 𝔠 4) E t' hκ h𝔠 hτ hE ht'0 ht'1 hsz hbw hR' hU.1 hU.2.2.1 h4
      hDL h61)

end P7
end RBM.Endpoints
