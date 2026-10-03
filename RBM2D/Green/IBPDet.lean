/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucAvgDet
import RBM2D.Green.IBPRem

/-!
# The integration-by-parts display at a deterministic entry scale: `ibpDetThm`

The statement `IBPDetThm` of `Green/AvgPins.lean`, proved outright.  The proof follows the
one-dimensional formalization (the weighted conditional expectation of the diagonal, the floor and
ceiling of `Ψ²`), with the good-event input from the local law.
The paper does not state this as a lemma: (`GavLGEX`) is proved as in [YY_25] (the proof of
`lem_GbEXP`, "that of Lemma 4.2 in [YY_25]").

## Method

* The identity `condExpDiag_eq_sum_Sblk` (`IBP.lean`, with `gaussIBP`) writes
  `E_i(G_ii - m) = t m² Σ_k S_ik (G_kk - m) + t m Σ_k S_ik ibpRem(i,k)`;
  `norm_condExpDiag_sub_le_offdiag` (`CondDom.lean`) bounds the remainder by `A + S_ii A_diag`.
* `perTimeDomAt_ibpRem` (`IBPRem.lean`) gives `ibpRem (i,k) ≺ Ψ²` for `k ≠ i`
  and `ibpRem (i,i) ≺ 1`, under the good event of `highProbAt_detFlucDelta_of_localLaw` and
  the local law.
* `IBPDet_weighted_of_rem`: the union over the `size` sites `k` (spending `D + 2` on `D`),
  `A = a Ψ²`, `A_diag = a` with `a = size^{τ/2}`, and `S_ii = (5 W²)⁻¹ ≤ W⁻² ≤ Ψ²` give
  `2 a Ψ² ≤ size^τ Ψ²`.
* The same bridge `splitEquiv` / `Sblk2_eq_svar` (`FlucAvgDet.lean`) to `BlockIndex`.

## Differences from `d = 1`

* The hypothesis `hWΨ : W⁻¹ ≤ Ψ²` becomes `(W⁻¹)² ≤ Ψ²` (the entry scale is `S ≤ W⁻²/5`),
  which follows from the floor `W⁻¹ ≤ Ψ`.
* The premise `η ≥ N^{-K}` is derived from `RangeCond` (`eta_lower_of_rangeCond`, `K = 1`): the
  envelope is `hEnv` with `K_env = 3` (`(η⁻¹ + 1)² ≤ (size + 1)² ≤ size³`).
* The polynomial floor of `Ψ²` is `size^{-1} = (W L)^{-2} ≤ W⁻² ≤ Ψ²` (`B = 1`); the ceiling is
  `Ψ² ≤ 1`, from `Ψ ≤ size^{-a} ≤ 1`.
* The good-event input `hΩ` is at `θ = detFlucTheta a 1`, and `δ ≤ 1/4 ≤ 1/2`.

## Statement

`ibpDetThm : IBPDetThm` is the statement of `AvgPins.lean`, with no added hypothesis.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Green
open scoped NNReal ENNReal

/-! ## 1. The weighted reduction of the remainder -/

/-- The actual conditional IBP residual, with the diagonal coefficient kept: with
`‖ibpRem (i,k)‖ ≤ A Φ` for
`k ≠ i`, `‖ibpRem (i,i)‖ ≤ A` and `(W⁻¹)² ≤ Φ`, the residual is `≤ 2 A Φ`.  In d = 2 the diagonal
coefficient is `S_ii = (5 W²)⁻¹ ≤ (W⁻¹)²`. -/
theorem IBPDet_norm_condExpDiag_sub_le_two_phi {d : Sizes} {n : ℕ} {E t : ℝ} (hE : |E| < 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) {A Φ : ℝ}
    (hA0 : 0 ≤ A) (hΦ0 : 0 ≤ Φ) (hWΦ : ((d.W n : ℝ))⁻¹ ^ 2 ≤ Φ)
    (hoff : ∀ k : Idx (d.L n) (d.W n), k ≠ i → ‖ibpRem d n E t (i, k) ω‖ ≤ A * Φ)
    (hdiag : ‖ibpRem d n E t (i, i) ω‖ ≤ A) :
    ‖condExpDiag d n t (spectralZ E t) (spectralM E) i ω
        - (t : ℂ) * spectralM E ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E)‖ ≤ 2 * A * Φ := by
  have hS : svar (d.L n) (d.W n) i i ≤ ((d.W n : ℝ))⁻¹ ^ 2 := by
    rw [svar_diag]
    have h0 : (0 : ℝ) ≤ ((d.W n : ℝ))⁻¹ ^ 2 := by positivity
    linarith
  calc _ ≤ A * Φ + svar (d.L n) (d.W n) i i * A :=
      norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE ht0 ht i ω (mul_nonneg hA0 hΦ0) hoff hdiag
    _ ≤ A * Φ + Φ * A :=
      add_le_add_right (mul_le_mul_of_nonneg_right (hS.trans hWΦ) hA0) _
    _ = 2 * A * Φ := by ring

/-- **The weighted IBP display from the remainder bound**: from
`ibpRem (i,k) ≺ Ψ²` off the diagonal and `≺ 1` on it (`hrem`), and `(W⁻¹)² ≤ Ψ²`,
`|E_i(G_ii - m) - t m² Σ_k S_ik (G_kk - m)| ≺ Ψ²`, per time.  The union is over the `size` sites
`k` of the row (spending `D + 2` on `D`); `i` stays outside the probability. -/
theorem IBPDet_weighted_of_rem {d : Sizes} (hsz : SizeTendsto d) {E t Ψ : ℕ → ℝ}
    (hE : ∀ n, |E n| < 2) (h0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hWΨ : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ^ 2 ≤ Ψ n * Ψ n)
    (hrem : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
      (fun n q ω => ‖ibpRem d n (E n) (t n) q ω‖)
      (fun n q _ => if q.1 = q.2 then (1 : ℝ) else Ψ n * Ψ n)) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Idx (d.L n) (d.W n))
      (fun n i ω =>
        ‖condExpDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) i ω
          - (t n : ℂ) * spectralM (E n) ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
            * (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)) k k
              - spectralM (E n))‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  classical
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [hrem (τ / 2) hτ2 (D + 2) (by linarith), hWΨ,
    (tendsto_natCast_atTop_iff.mp hsz).eventually (eventually_le_rpow 2 hτ2)] with
    n hremN hWΨn h2N i
  have hNge1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := AvgPins_one_le_size d n
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set a : ℝ := ((d.size n : ℕ) : ℝ) ^ (τ / 2) with hadef
  have ha0 : 0 ≤ a := (Real.rpow_pos_of_pos hNpos _).le
  have ha2 : a * a = ((d.size n : ℕ) : ℝ) ^ τ := by
    rw [hadef, ← Real.rpow_add hNpos]
    congr 1
    ring
  set T : Idx (d.L n) (d.W n) → Set (Sizes.SeqΩ d) := fun k =>
    {ω | a * (if i = k then (1 : ℝ) else Ψ n * Ψ n) <
      ‖ibpRem d n (E n) (t n) (i, k) ω‖} with hTdef
  have hTk : ∀ k : Idx (d.L n) (d.W n), (Sizes.seqP d) (T k) ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) := fun k => hremN (i, k)
  have hunion : (Sizes.seqP d) (⋃ k, T k) ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
    have hpow : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
    have hcard' : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
      rw [flucAvg_card_Idx_eq_size]
    calc (Sizes.seqP d) (⋃ k, T k)
        ≤ ∑ k : Idx (d.L n) (d.W n), (Sizes.seqP d) (T k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Idx (d.L n) (d.W n),
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(D + 2))) :=
          Finset.sum_le_sum fun k _ => hTk k
      _ = ENNReal.ofReal ((Fintype.card (Idx (d.L n) (d.W n)) : ℝ) *
          ((d.size n : ℕ) : ℝ) ^ (-(D + 2))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) *
              ((d.size n : ℕ) : ℝ) ^ (-(D + 2)) ≤
              ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(D + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hpow
          have h2 : ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-(D + 2)) =
              ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
            have hsplit := Real.rpow_add hNpos 1 (-(D + 2))
            rw [Real.rpow_one] at hsplit
            rw [← hsplit]
            congr 1
            ring
          have h3 : ((d.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤ ((d.size n : ℕ) : ℝ) ^ (-D) :=
            Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
          linarith
  have hsub : {ω | ((d.size n : ℕ) : ℝ) ^ τ * (Ψ n * Ψ n) <
      ‖condExpDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) i ω
        - (t n : ℂ) * spectralM (E n) ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)) k k
            - spectralM (E n))‖} ⊆ ⋃ k, T k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hTle : ∀ k : Idx (d.L n) (d.W n), ‖ibpRem d n (E n) (t n) (i, k) ω‖ ≤
        a * (if i = k then (1 : ℝ) else Ψ n * Ψ n) := by
      intro k
      have := hcon k
      rw [hTdef] at this
      simpa only [Set.mem_ofPred_eq, not_lt] using this
    have hΦ0 : 0 ≤ Ψ n * Ψ n := mul_nonneg (hΨ0 n) (hΨ0 n)
    have hbound := IBPDet_norm_condExpDiag_sub_le_two_phi (hE n) (h0 n) (ht1 n) i ω ha0 hΦ0
      hWΨn (fun k hk => by simpa [Ne.symm hk] using hTle k) (by simpa using hTle i)
    have h2a : 2 * a ≤ a * a := by
      have ha : 2 ≤ a := h2N
      nlinarith
    have hfin : ‖condExpDiag d n (t n) (spectralZ (E n) (t n)) (spectralM (E n)) i ω
        - (t n : ℂ) * spectralM (E n) ^ 2 * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * (green (Sizes.seqHflow d n (t n) ω) (spectralZ (E n) (t n)) k k
            - spectralM (E n))‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ * (Ψ n * Ψ n) := by
      calc _ ≤ 2 * a * (Ψ n * Ψ n) := hbound
        _ ≤ (a * a) * (Ψ n * Ψ n) := mul_le_mul_of_nonneg_right h2a hΦ0
        _ = _ := by rw [ha2]
    exact (not_le.2 hω) hfin
  exact (measure_mono hsub).trans hunion

/-! ## 2. The eventual inputs of `perTimeDomAt_ibpRem` -/

/-- The envelope input `hEnv` at `K_env = 3` from `size^{-1} ≤ η_t` (`K_η = 1`): `η⁻¹ ≤ size`, so
`(η⁻¹ + 1)² ≤ (size + 1)² ≤ size³` once `size ≥ 4`. -/
theorem IBPDet_hEnv (d : Sizes) (hsz : SizeTendsto d) {E t : ℕ → ℝ}
    (hη : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n)) :
    ∀ᶠ n : ℕ in atTop,
      ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
  filter_upwards [hη, flucThreshold_etaInv_le_rpow_of_lower d hη, hsz.eventually_ge_atTop 4]
    with n hn hinv hs4
  rw [Real.rpow_one] at hinv
  have h3 : ((d.size n : ℕ) : ℝ) ^ (3 : ℝ) = ((d.size n : ℕ) : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have hpos : 0 < etaT (E n) (t n) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hn
  have hinv0 : 0 ≤ (etaT (E n) (t n))⁻¹ := inv_nonneg.2 hpos.le
  set s : ℝ := ((d.size n : ℕ) : ℝ) with hs
  have h1 : ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (s + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (s + 1) ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s]
  exact h1.trans h2

/-- The polynomial floor of `Ψ²` at `B = 1`: `size^{-1} = (W L)^{-2} ≤ W⁻² ≤ Ψ²`. -/
theorem IBPDet_hΨlow (d : Sizes) {Ψ : ℕ → ℝ} (hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ Ψ n * Ψ n := by
  filter_upwards [hΨlo] with n hn
  have hw : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hs : d.W n ^ 2 ≤ d.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) 2
  have hsR : ((d.W n : ℝ)) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast hs
  rw [Real.rpow_neg_one]
  calc ((d.size n : ℕ) : ℝ)⁻¹ ≤ (((d.W n : ℝ)) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsR
    _ = ((d.W n : ℝ))⁻¹ ^ 2 := by rw [inv_pow]
    _ ≤ Ψ n ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hw.le) hn 2
    _ = Ψ n * Ψ n := sq _

/-- The ceiling `Ψ² ≤ 1` from `Ψ ≤ size^{-a}`. -/
theorem IBPDet_hΨ1 (d : Sizes) {Ψ : ℕ → ℝ} {a : ℝ} (ha : 0 < a) (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1 := by
  filter_upwards [hΨhi] with n hn
  have h1 : Ψ n ≤ 1 :=
    hn.trans (Real.rpow_le_one_of_one_le_of_nonpos (AvgPins_one_le_size d n) (by linarith))
  nlinarith [hΨ0 n]

/-! ## 3. The endpoint: `ibpDetThm` -/

section Endpoint

/-- **The endpoint `ibpDetThm`.**  The remainder `ibpRem ≺ 1` (diagonal), `≺ Ψ²` (off the
diagonal) from `perTimeDomAt_ibpRem` (`Kenv = 3`, `B = 1`, the good event at
`θ = detFlucTheta a 1`), then the weighted reduction `IBPDet_weighted_of_rem`, then the bridge
to `BlockIndex` (`splitEquiv`, `Sblk2_eq_svar`).  The statement is `IBPDetThm`
(`AvgPins.lean`), with no added hypothesis. -/
theorem ibpDetThm : IBPDetThm := by
  intro d κ 𝔠 δ hκ h𝔠 hδ hsz hbw E t hE h0 h1 hR Ψ a ha hΨ0 hΨ hll
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hη : ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n) :=
    (eta_lower_of_rangeCond d hκ hδ hsz hE hR).mono fun n h => by
      rw [spectralZ_im] at h
      exact h
  have hΨlo : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ≤ Ψ n := hΨ.mono fun n hn => hn.1
  have hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((d.size n : ℕ) : ℝ) ^ (-a) := hΨ.mono fun n hn => hn.2
  obtain ⟨hθ0, hθa, -, hθ1⟩ := detFlucTheta_specs ha one_pos
  have hΩ := highProbAt_detFlucDelta_of_localLaw d hsz ha hθ0 hθa.le hθ1 hΨhi hll
  have hrem := perTimeDomAt_ibpRem (d := d) (E := E) (t := t) (Ψ := Ψ)
    (δ := detFlucDelta d Ψ (detFlucTheta a 1)) (Kenv := 3) (B := 1)
    (tendsto_natCast_atTop_iff.mp hsz) hE2 h1 hΨ0 (by norm_num) zero_le_one
    (IBPDet_hEnv d hsz hη) (by simpa using IBPDet_hΨlow d hΨlo) (IBPDet_hΨ1 d ha hΨ0 hΨhi)
    (Eventually.of_forall fun n => (detFlucDelta_le_quarter d Ψ _ n).trans (by norm_num)) hΩ hll
  have hWΨ : ∀ᶠ n : ℕ in atTop, ((d.W n : ℝ))⁻¹ ^ 2 ≤ Ψ n * Ψ n :=
    hΨlo.mono fun n hn => by
      have hw : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
      calc ((d.W n : ℝ))⁻¹ ^ 2 ≤ Ψ n ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hw.le) hn 2
        _ = Ψ n * Ψ n := sq _
  have hidx := IBPDet_weighted_of_rem hsz hE2 h0 h1 hΨ0 hWΨ hrem
  exact FlucAvgDet_perTime_reindex (fun n i => (splitEquiv (d.L n) (d.W n)).symm i)
    (fun n i ω => by rw [FlucAvgDet_condDiagBlk_eq, FlucAvgDet_ibp_sum_eq])
    (fun n _ _ => sq (Ψ n)) hidx

end Endpoint

end RBM.Green
