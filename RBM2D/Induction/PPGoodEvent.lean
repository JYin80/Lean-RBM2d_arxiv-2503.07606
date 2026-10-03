/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.PPVocab

/-!
# The high-probability `(+,+)` grid good event `gridGoodPPN`

The result is the statement `GridGoodPPN` (`RBM2D.Induction.PPVocab`), proved verbatim, with no
hypothesis added:

`theorem gridGoodPPN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : GridGoodPPN d κ c τ E s v t K`.

Paper: arXiv:2503.07606, Section 5: the base case of Step 3 (the `(+,+)` two-loop bound),
`lem_decayLoop`; Section 3: `lem_GbEXP`, `GavLGEX`.  The argument parallels the one-dimensional
formalization; the `d = 2` template is `gridGoodN` (`RBM2D.Induction.GridGoodEvent`).

Layout: 1. the one-loop control `‖⟨(G_u - m) E_a⟩‖ ≺ M_u⁻¹` per time over `[s,t]` (the (G1)
input; it repeats the private chain `bcalE_one_loop` of `RBM2D.Induction.BcalE`, because `bcalEPT'`
has no `Ξ₁` clause and `Step1LoopPT` at `k = 2` only gives `(ℓ_u/ℓ_s)² M_u⁻¹`); 2. the
deterministic steps of each clause of `GoodSetPPN`; 3. the per-time union bound; 4. the grid union
and the initial value `J_s(H_0)`; 5. the endpoint.

Clause to input: Hermitian: deterministic; (G1) `Ξ^{(𝓛-𝒦)}_{u,1} ≤ N^ε` from the (`GavLGEX`)
clause of `GbEXPHypV3` (section 1); (G2), (G3) `Ξ^{(𝓛)}_{u,3} ≤ N^ε R⁴`,
`Ξ^{(𝓛)}_{u,6} ≤ N^ε R^{10}` from `Step1LoopPT` at lengths 3 and 6 (`ℓ_u ≤ ℓ_v` for `u ≤ v`);
(Dec) from `DecayLoopPT` at lengths `1..6` with `N^ε W^{-(D'+ε/c)} ≤ W^{-D'}` (`Bandwidth`);
`J_s(H_0) ≤ N^ε` from `InitLK` at `k = 2`.
The failure budget: per grid time at most `4 · 6 (2N)^6 N^{-D₂}` (four groups, each of at most
`6 (2N)^6` atomic events; `2^j (L²)^j ≤ (2N)^j`), plus one time for `J_0`, over `K + 1 ≤ N^C` grid
times, with `D₂ = D + max C 0 + 7`; the total is `≤ N^{-D}` once `N ≥ 4224`
(`GridGoodEvent_arith`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The one-loop control `‖⟨(G_u - m) E_a⟩‖ ≺ M_u⁻¹` per time over `[s,t]`

The lemmas `ppg_im_bounds`, `ppg_pt_transfer`, `ppg_pt_of_det`, `ppg_lower`, `ppg_scale_pos`,
`ppg_time_facts`, `ppg_Kbound_pt`, `ppg_loopOf_two`, `ppg_avgErr_false`, `ppg_Kpm_eq`,
`ppg_loopDet`, `ppg_one_loop` repeat the private chain `bcalE_*` of `RBM2D.Induction.BcalE`
under the prefix `ppg_` (they are private there). -/

section ImB

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ`. -/
private theorem ppg_im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hκ : 0 < κ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ (spectralM (E n)).im ∧ (spectralM (E n)).im ≤ 1 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun n => ⟨?_, ?_⟩⟩
  · have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  · rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith
  · rw [spectralM_im]
    have : Real.sqrt (4 - E n ^ 2) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [sq_nonneg (E n)]⟩
    linarith


end ImB

/-! ### Helpers (`PerTimeDomAt` bookkeeping, scales, charges, `loopDet`, `one_loop`) -/

section PTHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}

/-- Reindexing plus pointwise rewriting of both sides. -/
private theorem ppg_pt_transfer {U U' : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {ξ' ζ' : ∀ l, U' l → Ω → ℝ} (f : ∀ l, U' l → U l)
    (hξ : ∀ l u ω, ξ' l u ω = ξ l (f l u) ω) (hζ : ∀ l u ω, ζ' l u ω = ζ l (f l u) ω)
    (h : PerTimeDomAt P size ξ ζ) : PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  have hset : {ω | (size l : ℝ) ^ τ * ζ' l u ω < ξ' l u ω} =
      {ω | (size l : ℝ) ^ τ * ζ l (f l u) ω < ξ l (f l u) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, hζ]
  rw [hset]
  exact hl (f l u)

/-- A bound that holds deterministically (up to `N^δ` for every `δ > 0`) gives `≺`. -/
private theorem ppg_pt_of_det {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ δ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ δ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ] with l hl u
  have hE : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [hE, measure_empty]
  exact zero_le

end PTHelpers

section ScalesAvg

variable (d : Sizes)

private theorem ppg_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

private theorem ppg_one_le_W (n : ℕ) : 1 ≤ d.W n := d.W_pos n

private theorem ppg_hsize (h : SizeTendsto d) : Tendsto d.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

private theorem ppg_size_ge_W_sq (n : ℕ) : (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have h : d.W n ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]
    exact Nat.le_mul_of_pos_right _ (by have := ppg_one_le_L d n; positivity)
  exact_mod_cast h

/-- `M_u ≥ μ N^{c₀}` for all `u ≤ t n`, eventually. -/
private theorem ppg_lower {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) :
    ∃ μ c₀ : ℝ, 0 < μ ∧ 0 < c₀ ∧ (∀ n, μ ≤ (spectralM (E n)).im) ∧
      (∀ n, (spectralM (E n)).im ≤ 1) ∧
      ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
        μ * ((d.size n : ℕ) : ℝ) ^ c₀ ≤ scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, hc, hτ, -, -, -, -, hB, -, hR, -, -, -⟩ := hmain
  obtain ⟨μ, hμ, hμb⟩ := ppg_im_bounds hE hκ
  refine ⟨μ, min (2 * c) τ, hμ, lt_min (by linarith) hτ, fun n => (hμb n).1, fun n => (hμb n).2, ?_⟩
  filter_upwards [scaleFacts_R1 d κ c τ E t hE hκ hc hτ hB hR] with n hn u hu
  refine le_trans ?_ (hn u hu)
  exact mul_le_mul_of_nonneg_right (hμb n).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Positivity of the scale on `(-∞, t n]`. -/
private theorem ppg_scale_pos {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) {u : ℝ} (hu : u ≤ t n) : 0 < scaleM (d.L n) (d.W n) (E n) u := by
  obtain ⟨hκ, hE, -, -, -, -, ht1, -⟩ := hmain
  exact scaleM_pos (ppg_one_le_L d n) (ppg_one_le_W d n) (by linarith [hE n])
    (lt_of_le_of_lt hu (ht1 n))

/-- The elementary time facts on `[s n, t n]`. -/
private theorem ppg_time_facts {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (n : ℕ) (u : TimeIcc s t n) : |E n| < 2 ∧ 0 ≤ (u : ℝ) ∧ (u : ℝ) < 1 := by
  obtain ⟨hκ, hE, -, -, hs0, -, ht1, -⟩ := hmain
  exact ⟨by linarith [hE n], le_trans (hs0 n) u.2.1, lt_of_le_of_lt u.2.2 (ht1 n)⟩

/-- (`KboundConcl`) `‖𝒦_{u,σ,a}‖ ≺ M_u^{-(k-1)}` per time, deterministically. -/
private theorem ppg_Kbound_pt {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KboundConcl κ) (k : ℕ) (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p _ => ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := ppg_hsize d hN
  refine ppg_pt_of_det fun δ hδ => ?_
  filter_upwards [hsize.eventually (hK k hk δ hδ)] with n hn p ω
  obtain ⟨hE2, hu0, hu1⟩ := ppg_time_facts d hmain' n p.1
  have h := hn ⟨⟨d.L n, d.W n, d.three_le_L n, d.W_pos n, (Sizes.size_eq d n).symm, E n, hE n,
    p.1, hu0, hu1⟩, p.2.1, p.2.2⟩
  have h' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) p.1 (loopOf p.2.1 p.2.2)‖ ≤
      ((d.size n : ℕ) : ℝ) ^ δ * (KLoop.Mt (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1) := h
  rw [kloop_Mt_eq hu1.le] at h'
  exact h'

end ScalesAvg

section ChargeAvg

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem ppg_loopOf_two (s₁ s₂ : Bool) (a b : Z2 L) :
    loopOf (![s₁, s₂] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) = ⟨[s₁, s₂], [a, b]⟩ := by
  simp [loopOf, List.ofFn_succ]

/-- Conjugating the `+` one-loop gives the `-` one-loop. -/
private theorem ppg_avgErr_false (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (a : Z2 L) :
    avgErr L W E u M false a = star (avgErr L W E u M true a) := by
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hG : (greenBlk L W E u M true)ᴴ = greenBlk L W E u M false :=
    Gsig_conjTranspose hH (spectralZ E u) true
  have hm : star (KLoop.mSig E true) = KLoop.mSig E false := by
    simp [KLoop.mSig]
  unfold avgErr
  rw [← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hG, hm]

/-- `𝒦` at `(+,-)` is `Kpm`. -/
private theorem ppg_Kpm_eq (E u : ℝ) (a b : Z2 L) :
    Kpm L W E u a b = KLoop.Kcal L W E u ⟨[true, false], [a, b]⟩ := by
  rw [KLoop.Kcal_two]
  unfold Kpm
  have : KLoop.mSig E true * KLoop.mSig E false = (Complex.normSq (spectralM E) : ℂ) := by
    simp [KLoop.mSig, Complex.mul_conj]
  rw [this, inv_pow]

end ChargeAvg

section OneLoop

variable (d : Sizes)

/-- **`max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ M_u^{-1}`** per time over `[s,t]`, from `KboundConcl`
(`n = 2`) and `Step2DecayPT` at `D = 2` (`(η_s/η_u)^4 ≤ M_u` by `scaleM_ge_pow29`, `W^{-2} ≤ M_u^{-1}`
by `M_u ≤ W²`). -/
private theorem ppg_loopDet {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hdec : Step2DecayPT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := ppg_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := ppg_hsize d hN
  have hpos : ∀ n (u : TimeIcc s t n), 0 < scaleM (d.L n) (d.W n) (E n) u :=
    fun n u => ppg_scale_pos d hmain' n u.2.2
  -- (1) `‖Kpm‖ ≺ M⁻¹`
  have h1 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => ‖Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
    refine ppg_pt_transfer (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Z2 (d.L n)))
      (fun n p => (p.1, ((![true, false] : Fin 2 → Bool),
        (![p.2.1, p.2.2] : Fin 2 → Z2 (d.L n))))) ?_ ?_ (ppg_Kbound_pt d hmain' hKb 2 (by norm_num))
    · intro n p ω
      simp only []
      rw [ppg_loopOf_two, ppg_Kpm_eq]
    · intro n p ω
      simp
  -- (2) `lkErrMat ≺ M⁻¹`
  have h2 : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize
      (fun n p _ => inv_nonneg.2 (hpos n p.1).le) 2 ?_ (hdec 2 (by norm_num))
    filter_upwards [hC] with n hCn p ω
    obtain ⟨u, a, b⟩ := p
    obtain ⟨hE2, hu0, hu1⟩ := ppg_time_facts d hmain' n u
    have hM := hpos n u
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hut : (u : ℝ) ≤ t n := u.2.2
    have hx29 := scaleM_ge_pow29 (ppg_one_le_L d n) (ppg_one_le_W d n) hE2 (hs0 n) hsu hut
      (ht1 n) hCn
    have hxu : 0 < 1 - (u : ℝ) := by linarith
    have hx1 : 1 ≤ (1 - s n) / (1 - (u : ℝ)) := by
      rw [le_div_iff₀ hxu]; linarith
    have hx4 : ((1 - s n) / (1 - (u : ℝ))) ^ 4 ≤ scaleM (d.L n) (d.W n) (E n) u :=
      (pow_le_pow_right₀ hx1 (by norm_num)).trans hx29
    have hMW : scaleM (d.L n) (d.W n) (E n) u ≤ (d.W n : ℝ) ^ 2 := by
      rw [scaleM_eq (ppg_one_le_L d n) hu1]
      have him0 : 0 ≤ (spectralM (E n)).im := (spectralM_im_pos hE2).le
      have hW2 : (0 : ℝ) ≤ (d.W n : ℝ) ^ 2 := by positivity
      have hmin : min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) ≤ 1 := min_le_left _ _
      have hmin0 : 0 ≤ min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ))) :=
        le_min zero_le_one (mul_nonneg (by positivity) hxu.le)
      calc (d.W n : ℝ) ^ 2 * (spectralM (E n)).im *
            min 1 (((d.L n : ℕ) : ℝ) ^ 2 * (1 - (u : ℝ)))
          ≤ (d.W n : ℝ) ^ 2 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (him1 n) hW2) hmin hmin0 (by positivity)
        _ = (d.W n : ℝ) ^ 2 := by ring
    rw [etaT_div_etaT hE2 (by linarith) hu1]
    set Q := (scaleM (d.L n) (d.W n) (E n) u)⁻¹ with hQ
    have hQ0 : 0 < Q := inv_pos.2 hM
    have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast ppg_one_le_W d n
    have he1 : Real.exp (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) / ellT (d.L n) u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
    have he0 := (Real.exp_pos (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) /
      ellT (d.L n) u))).le
    have hw : (d.W n : ℝ) ^ (-(2 : ℝ)) ≤ Q := by
      rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hQ]
      exact inv_anti₀ hM hMW
    have hr : ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ ≤ Q := by
      calc ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹
          ≤ scaleM (d.L n) (d.W n) (E n) u * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hx4 (inv_nonneg.2 (sq_nonneg _))
        _ = Q := by rw [hQ]; field_simp
    have hr0 : 0 ≤ ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ :=
      mul_nonneg (pow_nonneg (by linarith [hx1]) _) (inv_nonneg.2 (sq_nonneg _))
    calc ((1 - s n) / (1 - (u : ℝ))) ^ 4 * (scaleM (d.L n) (d.W n) (E n) u ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (a - b) : ℝ) / ellT (d.L n) u)) +
          (d.W n : ℝ) ^ (-(2 : ℝ))
        ≤ Q * 1 + Q := add_le_add (mul_le_mul hr he1 he0 hQ0.le) hw
      _ = 2 * Q := by ring
  -- (3) assemble
  have h3 := PerTimeCalc.PerTime.perTimeCalc_add hsize h1 h2
  have h4 := PerTimeCalc.PerTime.stochDom_of_le_left_eventually
    (ξ := fun n (p : TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n)) ω =>
      ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖)
    (Eventually.of_forall fun n p ω => by
      have hx : loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2 =
          (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n p.1 ω)) (spectralZ (E n) p.1)
            (pmLoop p.2.1 p.2.2) - Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2) +
            Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2 := by
        unfold loopPM; ring
      change ‖loopPM (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2‖ ≤
        ‖Kpm (d.L n) (d.W n) (E n) p.1 p.2.1 p.2.2‖ +
          lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2
      rw [hx]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      unfold lkErrMat; ring) h3
  exact PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n p _ => inv_nonneg.2 (hpos n p.1).le) 2
    (Eventually.of_forall fun n p ω => by linarith) h4

/-- **The one-loop control (`n = 1`)**: `‖⟨(G_u - m) E_a⟩‖ ≺ M_u⁻¹` per time over `[s,t]`, from the (`GavLGEX`)
clause of `GbEXPHypV3 d (κ/2) c τ` at every time sequence `u ∈ [s,t]`, with the deterministic
control `Ψ² = M_u⁻¹` (`LoopDetSeq` from `ppg_loopDet`) and (`asGMc`) from `Step2LocalPT`; the
proof is that of `bcalE_one_loop` (itself `s45_one_loop` with `Step3PT` at `k = 2` replaced by
`bcalE_loopDet`). -/
private theorem ppg_one_loop {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hV3 : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (hmain : MainIndHyp d κ c τ E s t)
    (hKb : KboundConcl κ) (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => TimeIcc s t n × Z2 (d.L n))
      (fun n p ω => ‖avgErr (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) true p.2‖)
      (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹) := by
  have hmain' := hmain
  obtain ⟨μ, c₀, hμ, hc₀, hμb, him1, hlow⟩ := ppg_lower d hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hN, hB, hC, hR, -, -, -⟩ := hmain
  have hsize := ppg_hsize d hN
  refine RBM.Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst
    (V := fun n => Z2 (d.L n)) (fun n => ⟨0⟩)
    (fun n v q ω => ‖avgErr (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) true q‖)
    (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹) ?_
  intro u hu
  obtain ⟨hN', hB', hE', hu0, hu1, hRu⟩ := RBM.Green.v3_premises_of_mainIndHyp d hmain' u hu
  have hMpos : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (u n) :=
    fun n => ppg_scale_pos d hmain' n (hu n).2
  -- (asGMc) at the exponent `c₀`, from `Step2LocalPT`
  have hAs : RBM.Green.AsGMcSeq d E u c₀ := by
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ ((1 : ℝ) / 2)) hloc u hu
    unfold RBM.Green.AsGMcSeq
    refine PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n p _ => Real.rpow_nonneg
      (Nat.cast_nonneg _) _) (Real.sqrt μ⁻¹) ?_ h1
    filter_upwards [hlow] with n hn q ω
    have hW0 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast ppg_one_le_W d n
    have hy : 0 < (d.W n : ℝ) ^ c₀ := Real.rpow_pos_of_pos hW0 _
    have hpow : ((d.W n : ℝ) ^ c₀) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ c₀ := by
      calc ((d.W n : ℝ) ^ c₀) ^ 2 = ((d.W n : ℝ) ^ 2) ^ c₀ := by
            rw [sq, sq, Real.mul_rpow hW0.le hW0.le]
        _ ≤ ((d.size n : ℕ) : ℝ) ^ c₀ :=
            Real.rpow_le_rpow (by positivity) (ppg_size_ge_W_sq d n) hc₀.le
    have hM : μ * ((d.W n : ℝ) ^ c₀) ^ 2 ≤ scaleM (d.L n) (d.W n) (E n) (u n) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hμ.le) (hn (u n) (hu n).2)
    have hinv : (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤
        μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by
      calc (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ ≤ (μ * ((d.W n : ℝ) ^ c₀) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) hM
        _ = μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2 := by rw [mul_inv, inv_pow]
    rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹
        ≤ Real.sqrt (μ⁻¹ * (((d.W n : ℝ) ^ c₀)⁻¹) ^ 2) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt μ⁻¹ * ((d.W n : ℝ) ^ c₀)⁻¹ := by
          rw [Real.sqrt_mul (inv_nonneg.2 hμ.le), Real.sqrt_sq (inv_nonneg.2 hy.le)]
  -- the deterministic control `Ψ² = M_u⁻¹`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n,
      Ψ n = Real.sqrt (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := ⟨_, fun _ => rfl⟩
  have hΨsq : ∀ n, Ψ n ^ 2 = (scaleM (d.L n) (d.W n) (E n) (u n))⁻¹ := fun n => by
    rw [hΨ, Real.sq_sqrt (inv_nonneg.2 (hMpos n).le)]
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => by rw [hΨ]; exact Real.sqrt_nonneg _
  have hΨev : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4)) := by
    filter_upwards [hlow, ((tendsto_rpow_atTop (half_pos hc₀)).comp hN).eventually_ge_atTop μ⁻¹]
      with n hn hgrow
    have hgrow' : μ⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := hgrow
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNpos : 0 < ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) :=
      lt_of_lt_of_le (inv_pos.2 hμ) hgrow'
    have h1 : 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      calc (1 : ℝ) = μ * μ⁻¹ := (mul_inv_cancel₀ hμ.ne').symm
        _ ≤ μ * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := mul_le_mul_of_nonneg_left hgrow' hμ.le
    have hsplit : ((d.size n : ℕ) : ℝ) ^ c₀ =
        ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      rw [← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
    have hM : ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) ≤ scaleM (d.L n) (d.W n) (E n) (u n) := by
      refine le_trans ?_ (hn (u n) (hu n).2)
      rw [hsplit]
      nlinarith
    rw [hΨ, Real.sqrt_le_iff]
    refine ⟨Real.rpow_nonneg hN0 _, ?_⟩
    have hsq : (((d.size n : ℕ) : ℝ) ^ (-(c₀ / 4))) ^ 2 =
        (((d.size n : ℕ) : ℝ) ^ (c₀ / 2))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_neg hN0]
      congr 1; push_cast; ring
    rw [hsq]
    exact inv_anti₀ hNpos hM
  -- the loop control `LoopDetSeq` from `ppg_loopDet`
  have hLoop : RBM.Green.LoopDetSeq d E u Ψ := by
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Z2 (d.L n) × Z2 (d.L n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => ‖loopPM (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2‖)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹) (ppg_loopDet d hmain' hKb hdec) u hu
    unfold RBM.Green.LoopDetSeq
    exact ppg_pt_transfer (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n)) (fun n p => p)
      (fun _ _ _ => rfl) (fun n p ω => hΨsq n) h1
  have hGav : RBM.Green.GavLDetSeq d E u Ψ :=
    ((hV3 hN' hB' E u hE' hu0 hu1 hRu c₀ hc₀).2.2 hAs).2.2 Ψ (c₀ / 4) (by positivity) hΨ0 hΨev
      hLoop
  unfold RBM.Green.GavLDetSeq at hGav
  exact ppg_pt_transfer (U := fun n => Unit × Z2 (d.L n)) (fun n p => p) (fun _ _ _ => rfl)
    (fun n p ω => (hΨsq n).symm) hGav

end OneLoop


/-! ## 2. The deterministic steps: from the absence of the atomic failures to the clauses of
`GoodSetPPN` -/

section Det

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem ppg_loopOf_one (s : Bool) (a : Z2 L) :
    loopOf (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = ⟨[s], [a]⟩ := by
  rfl

/-- `lkGen` at length `1` is the norm of `⟨(G - m) E_a⟩`. -/
private theorem ppg_lkGen_one (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (a : Z2 L) :
    lkGen L W E u M (![s] : Fin 1 → Bool) (![a] : Fin 1 → Z2 L) = ‖avgErr L W E u M s a‖ := by
  unfold lkGen avgErr
  rw [ppg_loopOf_one]
  have h1 : gloop L W (blockMat M) (spectralZ E u) ⟨[s], [a]⟩ =
      Matrix.trace (greenBlk L W E u M s * Eblk L W a) := by
    simp [gloop, gloopProd_cons, greenBlk]
  have h2 : KLoop.Kcal L W E u ⟨[s], [a]⟩ = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  rw [h1, h2, sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]

/-- At length `1` the loop `𝓛-𝒦` is `⟨(G - m) E_a⟩` for the `+` sign, whichever the sign. -/
private theorem ppg_lkGen_one_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (σ : Fin 1 → Bool) (a : Fin 1 → Z2 L) :
    lkGen L W E u M σ a = ‖avgErr L W E u M true (a 0)‖ := by
  obtain ⟨x, rfl⟩ : ∃ x, σ = ![x] := ⟨σ 0, by funext i; fin_cases i; rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = ![b] := ⟨a 0, by funext i; fin_cases i; rfl⟩
  rw [ppg_lkGen_one]
  cases x
  · rw [ppg_avgErr_false E u M hM, norm_star]
    rfl
  · rfl

/-- (G1): `Ξ^{(𝓛-𝒦)}_{u,1} ≤ Γ` from `‖⟨(G - m) E_a⟩‖ ≤ Γ M_u⁻¹` at every label. -/
private theorem ppg_xiLK_one_le {E u Γ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (hMpos : 0 < scaleM L W E u)
    (h : ∀ q : Z2 L, ‖avgErr L W E u M true q‖ ≤ Γ * (scaleM L W E u)⁻¹) :
    xiLK L W E u M 1 ≤ Γ := by
  unfold xiLK
  have hsup : Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin 1 → Bool) × (Fin 1 → Z2 L) => lkGen L W E u M p.1 p.2) ≤
        Γ * (scaleM L W E u)⁻¹ := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    rw [ppg_lkGen_one_eq E u M hM p.1 p.2]
    exact h _
  calc _ ≤ Γ * (scaleM L W E u)⁻¹ * scaleM L W E u ^ 1 :=
        mul_le_mul_of_nonneg_right hsup (by positivity)
    _ = Γ := by field_simp

/-- (G2), (G3): `Ξ^{(𝓛)}_{u,k} ≤ Γ Φ` from `|𝓛_{u,σ,a}| ≤ Γ r^{2(k-1)} M_u^{-(k-1)}` at every
`(σ, a)`, `r^{2(k-1)} ≤ Φ`, `Γ ≥ 0`. -/
private theorem ppg_xiL_le {E u Γ r Φ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} (k : ℕ)
    (hMpos : 0 < scaleM L W E u) (hΓ : 0 ≤ Γ) (hrΦ : r ^ (2 * (k - 1)) ≤ Φ)
    (h : ∀ p : (Fin k → Bool) × (Fin k → Z2 L),
      loopAbs L W E u M p.1 p.2 ≤ Γ * (r ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1))) :
    xiL L W E u M k ≤ Γ * Φ := by
  unfold xiL
  have hsup : Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin k → Bool) × (Fin k → Z2 L) => loopAbs L W E u M p.1 p.2) ≤
        Γ * (r ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) :=
    Finset.sup'_le _ _ fun p _ => h p
  calc _ ≤ Γ * (r ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) * scaleM L W E u ^ (k - 1) :=
        mul_le_mul_of_nonneg_right hsup (by positivity)
    _ = Γ * r ^ (2 * (k - 1)) := by
        have hinv : (scaleM L W E u)⁻¹ ^ (k - 1) * scaleM L W E u ^ (k - 1) = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hMpos.ne', one_pow]
        calc Γ * (r ^ (2 * (k - 1)) * (scaleM L W E u)⁻¹ ^ (k - 1)) * scaleM L W E u ^ (k - 1)
            = Γ * r ^ (2 * (k - 1)) * ((scaleM L W E u)⁻¹ ^ (k - 1) * scaleM L W E u ^ (k - 1)) := by
              ring
          _ = Γ * r ^ (2 * (k - 1)) := by rw [hinv, mul_one]
    _ ≤ Γ * Φ := mul_le_mul_of_nonneg_left hrΦ hΓ

/-- `J_u(M) ≤ Γ` from `|(𝓛-𝒦)_{u,(+,+),(a,b)}| ≤ Γ M_u^{-2}` at every `(a, b)`. -/
private theorem ppg_jPPN_le {E u Γ : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hMpos : 0 < scaleM L W E u)
    (h : ∀ p : Z2 L × Z2 L,
      lkGen L W E u M ![true, true] ![p.1, p.2] ≤ Γ * (scaleM L W E u)⁻¹ ^ 2) :
    jPPN L W E u M ≤ Γ := by
  unfold jPPN
  have hsup : Finset.univ.sup' Finset.univ_nonempty
      (fun p : Z2 L × Z2 L => lkGen L W E u M ![true, true] ![p.1, p.2]) ≤
        Γ * (scaleM L W E u)⁻¹ ^ 2 := Finset.sup'_le _ _ fun p _ => h p
  calc _ ≤ Γ * (scaleM L W E u)⁻¹ ^ 2 * scaleM L W E u ^ 2 :=
        mul_le_mul_of_nonneg_right hsup (by positivity)
    _ = Γ := by field_simp

/-- **The deterministic step**: if none of the per-time failure events occurs at the Hermitian
matrix `M`, then `M ∈ GoodSetPPN` (with `Γ W^{-D''} ≤ W^{-D'}`, the absorption of `Bandwidth`,
and `r^4 ≤ Φ₃`, `r^{10} ≤ Φ₆` for `r = ℓ_u/ℓ_s ≤ ℓ_v/ℓ_s`). -/
private theorem ppg_mem_goodSetPPN {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    {Γ Φ₃ Φ₆ r τ' D' D'' : ℝ}
    (hM : M.IsHermitian) (hΓ : 0 ≤ Γ) (hMpos : 0 < scaleM L W E u)
    (hr3 : r ^ (2 * (3 - 1)) ≤ Φ₃) (hr6 : r ^ (2 * (6 - 1)) ≤ Φ₆)
    (hab : Γ * (W : ℝ) ^ (-D'') ≤ (W : ℝ) ^ (-D'))
    (g1 : ∀ q : Z2 L, ¬ (Γ * (scaleM L W E u)⁻¹ < ‖avgErr L W E u M true q‖))
    (g2 : ∀ p : (Fin 3 → Bool) × (Fin 3 → Z2 L),
      ¬ (Γ * (r ^ (2 * (3 - 1)) * (scaleM L W E u)⁻¹ ^ (3 - 1)) < loopAbs L W E u M p.1 p.2))
    (g3 : ∀ p : (Fin 6 → Bool) × (Fin 6 → Z2 L),
      ¬ (Γ * (r ^ (2 * (6 - 1)) * (scaleM L W E u)⁻¹ ^ (6 - 1)) < loopAbs L W E u M p.1 p.2))
    (gd : ∀ j ∈ Finset.Icc 1 6, ∀ (σ : Fin j → Bool) (a : Fin j → Z2 L),
      ¬ (Γ * (W : ℝ) ^ (-D'') < (loopAbs L W E u M σ a + lkGen L W E u M σ a) *
        (if ellT L u * (W : ℝ) ^ τ' ≤ (KLoop.maxDist L a : ℝ) then 1 else 0))) :
    M ∈ GoodSetPPN L W E u Γ Φ₃ Φ₆ τ' D' := by
  refine ⟨hM, ppg_xiLK_one_le hM hMpos fun q => not_lt.1 (g1 q),
    ppg_xiL_le 3 hMpos hΓ hr3 fun p => not_lt.1 (g2 p),
    ppg_xiL_le 6 hMpos hΓ hr6 fun p => not_lt.1 (g3 p), ?_⟩
  intro j hj1 hj2 σ a hfar
  have h := not_lt.1 (gd j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) σ a)
  simp only [hfar, ↓reduceIte, mul_one] at h
  exact h.trans hab

end Det

/-! ## 3. The per-time union bound -/

section PerTime

/-- The union of four sets, each of probability `≤ y`. -/
private theorem ppg_union4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A₁ A₂ A₃ A₄ G : Set Ω} {y : ℝ}
    (h₁ : P A₁ ≤ ENNReal.ofReal y) (h₂ : P A₂ ≤ ENNReal.ofReal y)
    (h₃ : P A₃ ≤ ENNReal.ofReal y) (h₄ : P A₄ ≤ ENNReal.ofReal y)
    (hsub : G ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄) : P G ≤ ENNReal.ofReal (4 * y) := by
  have step : ∀ (A B : Set Ω) (a b : ℝ≥0∞), P A ≤ a → P B ≤ b → P (A ∪ B) ≤ a + b :=
    fun A B a b ha hb => (measure_union_le A B).trans (add_le_add ha hb)
  have h := (measure_mono (μ := P) hsub).trans
    (step _ _ _ _ (step _ _ _ _ (step _ _ _ _ h₁ h₂) h₃) h₄)
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : ENNReal.ofReal (4 : ℝ) = 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  rw [h4]; ring

/-- The atomic failure bound `6 (2N)^6 N^{-D₂}` of one group of at most `6 (2N)^6` events. -/
private def ppgY (N D₂ : ℝ) : ℝ := 6 * (2 * N) ^ 6 * N ^ (-D₂)

variable (d : Sizes)

/-- **The per-time union bound.**  At every time `u ∈ [s n, v n]`, eventually in `n`, the probability
that `Sizes.seqHflow d n u ω` leaves `GoodSetPPN` at the levels `Γ = N^ε`, `Φ₃ = R⁴`, `Φ₆ = R^{10}`
is at most `4 · 6 (2N)^6 N^{-D₂}` for every `D₂ > 0`: four groups (G1: `L² ≤ N` labels, G2: `≤ (2N)³`
labels, G3: `≤ (2N)^6` labels, Dec: lengths `1..6`, `≤ 6 (2N)^6` labels), each of at most
`6 (2N)^6` events of probability `≤ N^{-D₂}` (`L² ≤ N`), and outside their union
`ppg_mem_goodSetPPN` applies. -/
private theorem ppg_perTime (κ c τ : ℝ) (E s v t : ℕ → ℝ)
    (hmain : MainIndHyp d κ c τ E s t) (hK : KboundConcl κ)
    (hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (h1 : Step1LoopPT d E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t) (hdl : DecayLoopPT d E s t)
    (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ε : ℝ) (hε : 0 < ε) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') (D₂ : ℝ)
    (hD₂ : 0 < D₂) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ v n →
      Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
          GoodSetPPN (d.L n) (d.W n) (E n) u (((d.size n : ℕ) : ℝ) ^ ε)
            (RPPN d s v n ^ 4) (RPPN d s v n ^ 10) τ' D'} ≤
        ENNReal.ofReal (4 * ppgY ((d.size n : ℕ) : ℝ) D₂) := by
  have hmain' := hmain
  have hav := ppg_one_loop d hV hmain' hK hloc hdec
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain
  have hD''0 : 0 < D' + ε / c := by positivity
  have eG1 := hav ε hε D₂ hD₂
  have eG2 := h1 3 (by norm_num) ε hε D₂ hD₂
  have eG3 := h1 6 (by norm_num) ε hε D₂ hD₂
  have eDec := (Filter.eventually_all_finset (Finset.Icc 1 6)).2 (fun j hj =>
    hdl j (Finset.mem_Icc.1 hj).1 τ' hτ' (D' + ε / c) hD''0 ε hε D₂ hD₂)
  filter_upwards [eG1, eG2, eG3, eDec, hband] with n e1 e2 e3 ed hbn u hsu hvu
  -- sizes and scales
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  have hN1 : (1 : ℝ) ≤ Nn := GoodEvent_one_le_size (d := d) n
  have hN0 : 0 < Nn := by linarith
  have hx : 0 ≤ Nn ^ (-D₂) := Real.rpow_nonneg hN0.le _
  have hLN : (d.L n) ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]; exact Nat.le_mul_of_pos_left _ (pow_pos (d.W_pos n) 2)
  have hNn1 : 1 ≤ d.size n := Nat.one_le_cast.1 hN1
  have hB1 : (1 : ℝ) ≤ (2 * Nn) ^ 6 := one_le_pow₀ (by linarith)
  have hB0 : (0 : ℝ) ≤ (2 * Nn) ^ 6 := by linarith
  have hcard1 : ∀ j, j ≤ 6 →
      (Fintype.card ((Fin j → Bool) × (Fin j → Z2 (d.L n))) : ℝ) ≤ (2 * Nn) ^ 6 := by
    intro j hj
    have h1 := (GridGoodEvent_card_lab (d.L n) j hLN).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2 * d.size n) hj)
    have h2 : (Fintype.card ((Fin j → Bool) × (Fin j → Z2 (d.L n))) : ℝ) ≤
        (((2 * d.size n) ^ 6 : ℕ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  have hcard0 : (Fintype.card (Z2 (d.L n)) : ℝ) ≤ (2 * Nn) ^ 6 := by
    have h1 : Fintype.card (Z2 (d.L n)) ≤ (2 * d.size n) ^ 6 := by
      rw [GridGoodEvent_card_Z2]
      calc (d.L n) ^ 2 ≤ d.size n := hLN
        _ ≤ 2 * d.size n := by omega
        _ ≤ (2 * d.size n) ^ 6 :=
          Nat.le_self_pow (by norm_num) _
    have h2 : (Fintype.card (Z2 (d.L n)) : ℝ) ≤ (((2 * d.size n) ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast h1
    simpa using h2
  have hE2 : |E n| < 2 := by have := hE n; linarith
  have hv1 : v n < 1 := (hvt n).trans_lt (ht1 n)
  have hu1 : u < 1 := hvu.trans_lt hv1
  have hu0 : 0 ≤ u := (hs0 n).trans hsu
  have hLn : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) u := scaleM_pos hLn (d.W_pos n) hE2 hu1
  have hab : Nn ^ ε * (d.W n : ℝ) ^ (-(D' + ε / c)) ≤ (d.W n : ℝ) ^ (-D') :=
    GridGoodEvent_absorb hN0.le (by exact_mod_cast d.W_pos n) hc hε hbn
  have hΓ : 0 ≤ Nn ^ ε := Real.rpow_nonneg hN0.le _
  -- the levels `Φ₃ = R⁴`, `Φ₆ = R^{10}`: `r = ℓ_u/ℓ_s ≤ ℓ_v/ℓ_s = R`
  have hℓs : 0 < ellT (d.L n) (s n) := (ellT_pos_le hLn ((hsv n).trans_lt hv1)).1
  have hℓu : 0 < ellT (d.L n) u := (ellT_pos_le hLn hu1).1
  have hr0 : 0 ≤ ellT (d.L n) u / ellT (d.L n) (s n) := div_nonneg hℓu.le hℓs.le
  have hrR : ellT (d.L n) u / ellT (d.L n) (s n) ≤ RPPN d s v n :=
    div_le_div_of_nonneg_right (ellT_mono_ratio hLn hu0 hvu hv1).1 hℓs.le
  have hr3 : (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (3 - 1)) ≤ RPPN d s v n ^ 4 :=
    pow_le_pow_left₀ hr0 hrR 4
  have hr6 : (ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (6 - 1)) ≤ RPPN d s v n ^ 10 :=
    pow_le_pow_left₀ hr0 hrR 10
  -- the common bound `y`
  set y : ℝ := ppgY Nn D₂ with hy
  have hy' : y = 6 * ((2 * Nn) ^ 6 * Nn ^ (-D₂)) := by rw [hy]; unfold ppgY; ring
  have hfib : ∀ c' : ℝ, c' ≤ (2 * Nn) ^ 6 → c' * Nn ^ (-D₂) ≤ y := by
    intro c' hc'
    have h0 : 0 ≤ (2 * Nn) ^ 6 * Nn ^ (-D₂) := mul_nonneg hB0 hx
    rw [hy']
    nlinarith [mul_le_mul_of_nonneg_right hc' hx]
  have hcBx : ∀ c' : ℝ, c' ≤ 6 → c' * ((2 * Nn) ^ 6 * Nn ^ (-D₂)) ≤ y := by
    intro c' hc'
    rw [hy']
    exact mul_le_mul_of_nonneg_right hc' (mul_nonneg hB0 hx)
  -- the time as an element of `[s n, t n]`
  set u' : TimeIcc s t n := ⟨u, hsu, hvu.trans (hvt n)⟩ with hu'
  -- the four groups
  have b1 : Sizes.seqP d {ω | ¬ ∀ q : Z2 (d.L n),
      ¬ (Nn ^ ε * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ <
        ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) true q‖)} ≤ ENNReal.ofReal y :=
    (GridGoodEvent_exists_le (P := Sizes.seqP d)
      (fun (q : Z2 (d.L n)) ω => Nn ^ ε * (scaleM (d.L n) (d.W n) (E n) u)⁻¹ <
        ‖avgErr (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) true q‖)
      (x := Nn ^ (-D₂)) (fun q => e1 (u', q))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ hcard0))
  have b2 : Sizes.seqP d {ω | ¬ ∀ p : (Fin 3 → Bool) × (Fin 3 → Z2 (d.L n)),
      ¬ (Nn ^ ε * ((ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (3 - 1)) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (3 - 1)) <
        loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) p.1 p.2)} ≤
      ENNReal.ofReal y :=
    (GridGoodEvent_exists_le (P := Sizes.seqP d)
      (fun (p : (Fin 3 → Bool) × (Fin 3 → Z2 (d.L n))) ω =>
        Nn ^ ε * ((ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (3 - 1)) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (3 - 1)) <
        loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) p.1 p.2)
      (x := Nn ^ (-D₂)) (fun p => e2 (u', p))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ (hcard1 3 (by norm_num))))
  have b3 : Sizes.seqP d {ω | ¬ ∀ p : (Fin 6 → Bool) × (Fin 6 → Z2 (d.L n)),
      ¬ (Nn ^ ε * ((ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (6 - 1)) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (6 - 1)) <
        loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) p.1 p.2)} ≤
      ENNReal.ofReal y :=
    (GridGoodEvent_exists_le (P := Sizes.seqP d)
      (fun (p : (Fin 6 → Bool) × (Fin 6 → Z2 (d.L n))) ω =>
        Nn ^ ε * ((ellT (d.L n) u / ellT (d.L n) (s n)) ^ (2 * (6 - 1)) *
          (scaleM (d.L n) (d.W n) (E n) u)⁻¹ ^ (6 - 1)) <
        loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) p.1 p.2)
      (x := Nn ^ (-D₂)) (fun p => e3 (u', p))).trans
      (ENNReal.ofReal_le_ofReal (hfib _ (hcard1 6 le_rfl)))
  have bd : Sizes.seqP d {ω | ¬ ∀ j ∈ Finset.Icc 1 6,
      ∀ v : (Fin j → Bool) × (Fin j → Z2 (d.L n)),
      ¬ (Nn ^ ε * (d.W n : ℝ) ^ (-(D' + ε / c)) <
        (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2 +
          lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2) *
        (if ellT (d.L n) u * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) v.2 : ℝ)
          then 1 else 0))} ≤ ENNReal.ofReal y := by
    refine (GridGoodEvent_forall_le (P := Sizes.seqP d) (Finset.Icc 1 6)
      (fun j ω => ∀ v : (Fin j → Bool) × (Fin j → Z2 (d.L n)),
        ¬ (Nn ^ ε * (d.W n : ℝ) ^ (-(D' + ε / c)) <
          (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2 +
            lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2) *
          (if ellT (d.L n) u * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) v.2 : ℝ)
            then 1 else 0)))
      (y := (2 * Nn) ^ 6 * Nn ^ (-D₂)) (fun j hj => ?_)).trans
      (ENNReal.ofReal_le_ofReal (hcBx _ ?_))
    · refine (GridGoodEvent_exists_le (P := Sizes.seqP d)
        (fun (v : (Fin j → Bool) × (Fin j → Z2 (d.L n))) ω =>
          Nn ^ ε * (d.W n : ℝ) ^ (-(D' + ε / c)) <
            (loopAbs (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2 +
              lkGen (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) v.1 v.2) *
            (if ellT (d.L n) u * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) v.2 : ℝ)
              then 1 else 0)) (x := Nn ^ (-D₂)) (fun v => ed j hj (u', v))).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (hcard1 j (Finset.mem_Icc.1 hj).2) hx
    · rw [Nat.card_Icc]
      norm_num
  refine ppg_union4 (P := Sizes.seqP d) b1 b2 b3 bd ?_
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
  obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, hd'⟩ := hcon
  simp only [Set.mem_ofPred_eq] at hω
  exact hω (ppg_mem_goodSetPPN (Sizes.seqHflow_isHermitian d n u ω) hΓ hMpos hr3 hr6 hab h1'
    (fun p => h2' p) (fun p => h3' p) (fun j hj σ a => hd' j hj (σ, a)))

end PerTime

/-! ## 4. The grid union and the initial value `J_s(H_0)` -/

section Grid

variable (d : Sizes)

private theorem ppgY_ge {N D₂ c' : ℝ} (hN : 0 < N) (hc' : c' ≤ (2 * N) ^ 6) :
    c' * N ^ (-D₂) ≤ ppgY N D₂ := by
  unfold ppgY
  have hx : 0 ≤ N ^ (-D₂) := Real.rpow_nonneg hN.le _
  have h0 : 0 ≤ (2 * N) ^ 6 * N ^ (-D₂) := mul_nonneg (by positivity) hx
  nlinarith [mul_le_mul_of_nonneg_right hc' hx]

/-- **The grid union** (generic in the measurable good-set family `G`; the template is the private
`gge_grid_union` of `RBM2D.Induction.GridGoodEvent`, which is stated for `GoodSetN`): if the flow leaves `G j`
with probability `≤ a` at every grid time `u_j`, the grid walk leaves some `G j`, `j ≤ K n`, with
probability `≤ (K n + 1) a`, through the transfer law `map_pathH_eq`. -/
private theorem ppg_grid_union {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {a : ℝ}
    (G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
    (hG : ∀ j, MeasurableSet (G j)) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hK0 : K n ≠ 0)
    (h : ∀ j ≤ K n, Sizes.seqP d {ω | Sizes.seqHflow d n (gridTime s v K n j) ω ∉ G j} ≤
      ENNReal.ofReal a) :
    pathP d {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ G j}ᶜ ≤
      ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * a) := by
  have hsub : {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ G j}ᶜ ⊆
      ⋃ j ∈ Finset.range (K n + 1), {ω | pathH d s v K n j ω ∉ G j} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨j, hj, hjG⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) hjG
  have hone : ∀ j ∈ Finset.range (K n + 1),
      pathP d {ω | pathH d s v K n j ω ∉ G j} ≤ ENNReal.ofReal a := by
    intro j hj
    have hmeas : MeasurableSet (G j)ᶜ := (hG j).compl
    have hH : Measurable (pathH d s v K n j) :=
      Measurable.of_eval_matrix _ fun i j' => measurable_pathH d s v K n j i j'
    have hF : Measurable (Sizes.seqHflow d n (gridTime s v K n j)) :=
      Measurable.of_eval_matrix _ fun i j' => Sizes.measurable_seqHflow_entry d n _ i j'
    have h1 : pathP d {ω | pathH d s v K n j ω ∉ G j} =
        Sizes.seqP d {ω | Sizes.seqHflow d n (gridTime s v K n j) ω ∉ G j} := by
      have e1 := Measure.map_apply (μ := pathP d) hH hmeas
      have e2 := Measure.map_apply (μ := Sizes.seqP d) hF hmeas
      rw [map_pathH_eq d s v K n j hs0 hsv hK0] at e1
      exact e1.symm.trans e2
    rw [h1]
    exact h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  calc pathP d {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ G j}ᶜ
      ≤ pathP d (⋃ j ∈ Finset.range (K n + 1), {ω | pathH d s v K n j ω ∉ G j}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (K n + 1), pathP d {ω | pathH d s v K n j ω ∉ G j} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (K n + 1), ENNReal.ofReal a := Finset.sum_le_sum hone
    _ = ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * a) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **The initial value**: `J_s(H_0) ≤ N^ε` fails with probability at most `6 (2N)^6 N^{-D₂}`,
eventually in `n`: the walk at index `0` has the law of the flow at time `s n` (`map_pathH_eq`),
and `InitLK` at `k = 2` bounds every `|(𝓛-𝒦)_{s,(+,+),(a,b)}|` by `N^ε M_s^{-2}`, off an event of
probability `≤ N^{-D₂}` each, over `L⁴ ≤ N² ≤ (2N)^6` labels (`ppg_jPPN_le`). -/
private theorem ppg_init (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ)
    (hmain : MainIndHyp d κ c τ E s t) (hsv : ∀ n, s n ≤ v n) (hK0 : ∀ n, K n ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (D₂ : ℝ) (hD₂ : 0 < D₂) :
    ∀ᶠ n : ℕ in atTop,
      pathP d {ω | jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) ≤
        ((d.size n : ℕ) : ℝ) ^ ε}ᶜ ≤ ENNReal.ofReal (ppgY ((d.size n : ℕ) : ℝ) D₂) := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, hinit, -, -⟩ := hmain
  filter_upwards [hinit 2 (by norm_num) ε hε D₂ hD₂] with n e0
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn
  have hN1 : (1 : ℝ) ≤ Nn := GoodEvent_one_le_size (d := d) n
  have hN0 : 0 < Nn := by linarith
  have hLN : (d.L n) ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]; exact Nat.le_mul_of_pos_left _ (pow_pos (d.W_pos n) 2)
  have hLn : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hE2 : |E n| < 2 := by have := hE n; linarith
  have hs1 : s n < 1 := (hst n).trans_lt (ht1 n)
  have hMpos : 0 < scaleM (d.L n) (d.W n) (E n) (s n) := scaleM_pos hLn (d.W_pos n) hE2 hs1
  have hcard : (Fintype.card (Z2 (d.L n) × Z2 (d.L n)) : ℝ) ≤ (2 * Nn) ^ 6 := by
    rw [Fintype.card_prod, GridGoodEvent_card_Z2]
    have h1 : d.L n ^ 2 * d.L n ^ 2 ≤ (2 * d.size n) ^ 6 := by
      have hNn1 : 1 ≤ d.size n := Nat.one_le_cast.1 hN1
      calc d.L n ^ 2 * d.L n ^ 2 ≤ d.size n * d.size n := Nat.mul_le_mul hLN hLN
        _ ≤ (2 * d.size n) ^ 2 := by nlinarith
        _ ≤ (2 * d.size n) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : ((d.L n ^ 2 * d.L n ^ 2 : ℕ) : ℝ) ≤ (((2 * d.size n) ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast h1
    simpa using h2
  have hmeasS : MeasurableSet {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ |
      jPPN (d.L n) (d.W n) (E n) (s n) M ≤ Nn ^ ε} :=
    measurableSet_le (measurable_jPPN (d.L n) (d.W n) (E n) (s n)) measurable_const
  have hH : Measurable (pathH d s v K n 0) :=
    Measurable.of_eval_matrix _ fun i j' => measurable_pathH d s v K n 0 i j'
  have hF : Measurable (Sizes.seqHflow d n (s n)) :=
    Measurable.of_eval_matrix _ fun i j' => Sizes.measurable_seqHflow_entry d n _ i j'
  have htr : pathP d {ω | jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) ≤
        Nn ^ ε}ᶜ =
      Sizes.seqP d {ω | Sizes.seqHflow d n (s n) ω ∉
        {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ |
          jPPN (d.L n) (d.W n) (E n) (s n) M ≤ Nn ^ ε}} := by
    rw [GoodEvent_gridTime_zero]
    have e1 := Measure.map_apply (μ := pathP d) hH hmeasS.compl
    have e2 := Measure.map_apply (μ := Sizes.seqP d) hF hmeasS.compl
    rw [map_pathH_eq d s v K n 0 (hs0 n) (hsv n) (hK0 n), GoodEvent_gridTime_zero] at e1
    exact e1.symm.trans e2
  rw [htr]
  have hsub : {ω | Sizes.seqHflow d n (s n) ω ∉
        {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ |
          jPPN (d.L n) (d.W n) (E n) (s n) M ≤ Nn ^ ε}} ⊆
      {ω | ¬ ∀ p : Z2 (d.L n) × Z2 (d.L n),
        ¬ (Nn ^ ε * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ 2 <
          lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) ![true, true]
            ![p.1, p.2])} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro hall
    exact hω (ppg_jPPN_le hMpos fun p => not_lt.1 (hall p))
  exact (measure_mono hsub).trans
    ((GridGoodEvent_exists_le (P := Sizes.seqP d)
      (fun (p : Z2 (d.L n) × Z2 (d.L n)) ω => Nn ^ ε * (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ 2 <
        lkGen (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) ![true, true] ![p.1, p.2])
      (x := Nn ^ (-D₂))
      (fun p => e0 ((), ![true, true], ![p.1, p.2]))).trans
      (ENNReal.ofReal_le_ofReal (ppgY_ge hN0 hcard)))

end Grid

/-! ## 5. The endpoint -/

section Endpoint

variable (d : Sizes)

/-- **The high-probability `(+,+)` grid good event** (`d = 2` pattern `gridGoodN`):
the statement `GridGoodPPN`, with no added hypothesis.  With
`D₂ = D + max C 0 + 7` (chosen after `D, C`), the per-time bound of `ppg_perTime` at every grid time
`u_j ∈ [s n, v n] ⊆ [s n, t n]`, the factor `K n + 1 ≤ N^C` of `ppg_grid_union`, the initial value
of `ppg_init` (one time, at most `6 (2N)^6 N^{-D₂}`) and `11 · 6 · 2^6 = 4224 ≤ N`
(`SizeTendsto`, a conjunct of `MainIndHyp`) give the failure probability `≤ N^{-D}`
(`GridGoodEvent_arith` at `k = 2`). -/
theorem gridGoodPPN (κ c τ : ℝ) (E s v t : ℕ → ℝ) (K : ℕ → ℕ) : GridGoodPPN d κ c τ E s v t K := by
  intro hmain hK hV h1 hloc hdec hdl hsv hvt hK0 C hC ε hε τ' hτ' D' hD' D hD
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  have hD₂ : 0 < D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1 := by
    have h1 := le_max_right C 0
    have h2 : (0 : ℝ) ≤ ((2 * 2 + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  filter_upwards [ppg_perTime d κ c τ E s v t hmain hK hV h1 hloc hdec hdl hsv hvt ε hε τ' hτ'
    D' hD' _ hD₂, ppg_init d κ c τ E s v t K hmain hsv hK0 ε hε _ hD₂, hC,
    hsize.eventually_ge_atTop 4224] with n hn hi hCn hNn
  set Nn : ℝ := ((d.size n : ℕ) : ℝ) with hNn'
  have hN1 : (1 : ℝ) ≤ Nn := GoodEvent_one_le_size (d := d) n
  have hN0 : 0 < Nn := by linarith
  -- the grid part
  have hgrid := ppg_grid_union d (goodSetGridPPN d E s v K ε τ' D' n)
    (fun j => measurableGoodSetPPN _ _ _ _ _ _ _ _ _) (hs0 n) (hsv n) (hK0 n)
    (a := 4 * ppgY Nn (D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1)) (fun j hj => by
      have hjv : gridTime s v K n j ≤ v n := GoodEvent_gridTime_le (hsv n) hj
      have hsj : s n ≤ gridTime s v K n j := by
        have h := GoodEvent_gridTime_mono (K := K) (hsv n) (Nat.zero_le j)
        rwa [GoodEvent_gridTime_zero] at h
      exact hn _ hsj hjv)
  -- the arithmetic
  have hcn : 11 * (2 * ((2 : ℕ) : ℝ) + 2) * 2 ^ (2 * 2 + 2) ≤ Nn := by
    norm_num; linarith
  have harith := GridGoodEvent_arith (N := Nn) (Kp := ((K n + 1 : ℕ) : ℝ)) (C := C) (D := D)
    (k := 2) hN1 hCn hcn
  have e : (2 * ((2 : ℕ) : ℝ) + 2) * (2 * Nn) ^ (2 * 2 + 2) *
      Nn ^ (-(D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1)) =
      ppgY Nn (D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1) := by
    unfold ppgY; norm_num
  rw [e] at harith
  set y : ℝ := ppgY Nn (D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]; unfold ppgY
    have : 0 ≤ Nn ^ (-(D + max C 0 + ((2 * 2 + 2 : ℕ) : ℝ) + 1)) := Real.rpow_nonneg hN0.le _
    positivity
  have hKp1 : (1 : ℝ) ≤ ((K n + 1 : ℕ) : ℝ) := by
    have : 1 ≤ K n + 1 := Nat.le_add_left 1 (K n)
    exact_mod_cast this
  have hsum : ((K n + 1 : ℕ) : ℝ) * (4 * y) + y ≤ ((K n + 1 : ℕ) : ℝ) * (11 * y) := by
    nlinarith [mul_le_mul_of_nonneg_right hKp1 hy0]
  -- the union
  unfold goodEventPPN
  rw [Set.compl_inter]
  calc pathP d ({ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ goodSetGridPPN d E s v K ε τ' D' n j}ᶜ ∪
        {ω | jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) ≤
          ((d.size n : ℕ) : ℝ) ^ ε}ᶜ)
      ≤ pathP d {ω | ∀ j ≤ K n, pathH d s v K n j ω ∈ goodSetGridPPN d E s v K ε τ' D' n j}ᶜ +
        pathP d {ω | jPPN (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) ≤
          ((d.size n : ℕ) : ℝ) ^ ε}ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * (4 * y)) + ENNReal.ofReal y :=
        add_le_add hgrid hi
    _ = ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * (4 * y) + y) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by linarith) (by linarith)) hy0]
    _ ≤ ENNReal.ofReal (Nn ^ (-D)) := ENNReal.ofReal_le_ofReal (hsum.trans harith)

end Endpoint

end RBM.Ind

end
