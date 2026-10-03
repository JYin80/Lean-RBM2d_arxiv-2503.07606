/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltEnd
import RBM2D.Induction.QopBounds
import RBM2D.Induction.GridGoodEvent
import RBM2D.Induction.KcalDecay
import RBM2D.Induction.DecayLoop

/-!
# The per-time levels of `𝒬_u B_m`, `m = 1..5` (part (b) of `AltLevelsQ`)

Namespace `RBM.Ind`, `variable (d : Sizes)`.
Paper (Section 5): `lem:STOeq_Qt`, `int_K-L+Q2`, `lem_BcalE` (`CalEbwXi`), `STOeq_Qt_assume_0`,
`jywiiwsoks`, `eq:thetadot_bound`, `kkuuwsaf`, `kkuuwsaf5`, `lem_+Q`, `normQA`.

Public declarations (every other declaration is `private` with the prefix `AltLevelsQ_`):
* `AltLevelsQm`: the second conjunct of `AltLevelsQConcl` under the premises of `AltLevelsQ`;
* `altLevelsQm : AltLevelsQm d κ c τ C E s t`, with no added hypothesis.

## Proof

1. `AltLevelsQ_goodSet`: at every time `u ∈ [s_n, v_n]` the matrix `H_u` lies in
   `GoodSetN (Γ = N^{τ₀/4}, Λ, Φ, τ_g, D_g)` off an event of probability `≤ N^{-D}`:
   `gridGoodN` with the one-step grid `K ≡ 1` (grid time `u_1 = u`), the transfer law
   `map_pathH_eq`, and the uniformization over time sections.  The window
   `τ_g = 2(k-1)τ'/(cPrec + 2(k-2))` and the decay `D_g` are free parameters of `GoodSetN`.
2. `m = 1, 2, 3` (`B₁ = Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l`, `B₂ = 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)}`, `B₃ = 𝓔^{(G̃)}`): the clauses
   (D1)-(D3), (V) of `GoodSetN` give `‖B_m‖_max ≤ k²Γ²Φ M_u^{-k}η_u^{-1} + W^{-D_g}` and the
   `(u, τ_g, D_g)` decay (`AltLevelsQ_B123`); then `qopNorm` (`𝒬_u`: loss
   `W^{cPrec τ_g}`, additive `W^{-D_g+cPrec}`) and the arithmetic of `AltLevelsQ_final123`.
3. `m = 4, 5`: `𝒫B₄ = 𝒫B₅ = 0`, so `𝒬_u B_m = B_m` (`AltLevelsQ_altQB_four_five`, the two facts used
   in `dGridQN_eq_dFlowQ`); then `B45_core_det_pub` with `R = ℓ_u W^{τ_g}`,
   `X = ΓΦ M_u^{-(k-1)}` (clause (G2)), `B_f = W^{-D_g}` (clause (Dec)) (`AltLevelsQ_B45`), and the
   arithmetic `AltLevelsQ_arith45`.  The far part `B_f` goes to the additive term `W^{-D_b}` of
   `altQLevel`, so no `Φ ≥ 1` is used (`b45PT'` needs `1 ≤ Λ`).

The argument parallels the one-dimensional formalization on the good set.  Some elementary lemmas
used in the proof (loop indices, far labels, arithmetic of the levels) are private here and carry
the prefix `AltLevelsQ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **`AltLevelsQm`**: part (b) of
`AltLevelsQ` (in `RBM2D.Induction.AltEnd`), i.e. the second conjunct of `AltLevelsQConcl` under the
premises of `AltLevelsQ`: for `m = 1..5`, every time `u ∈ [s_n, v_n]`, every alternating `σ` and label,
`‖𝒬_u B_m(H_u)‖ ≺ altQLevel = Φ W^{2(k-1)τ'} M_u^{-k} η_u^{-1} + W^{-D_b}`, per time. -/
def AltLevelsQm (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ n, 0 ≤ Φ n) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) → STOeqLevels d E s t k Λ Φ →
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ τ' Db : ℝ, 0 < τ' → 0 < Db →
  ∀ m : Fin 6, m ≠ 0 → PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖)
      (fun n p _ => altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (p.1 : ℝ))

/-! ## 1. The good set holds per time (from `gridGoodN`) -/

section Good

variable {d}

/-- **The good set at one time section** (`gridGoodN` with the one-step grid `K ≡ 1`,
`v := u`, and the transfer law `map_pathH_eq`): for a time sequence `s ≤ u ≤ t`, eventually in `n`,
`Sizes.seqHflow d n (u n)` leaves `GoodSetN` at level `Γ = N^ε` with probability `≤ N^{-D}`. -/
private theorem AltLevelsQ_goodSet_seq {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hmain : MainIndHyp d κ c τ E s t) (hK : KboundConcl κ) (hKd : KcalDecay κ)
    (hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (hloc : Step2LocalPT d E s t)
    (hdec : Step2DecayPT d E s t) (hdl : DecayLoopPT d E s t)
    {k : ℕ} (hk : 2 ≤ k) {Λ Φ : ℕ → ℝ} (hΛ0 : ∀ n, 0 ≤ Λ n) (hΦ0 : ∀ n, 0 ≤ Φ n)
    (hΛ1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) (hlev : STOeqLevels d E s t k Λ Φ)
    {ε : ℝ} (hε : 0 < ε) {τg : ℝ} (hτg : 0 < τg) {Dg : ℝ} (hDg : 0 < Dg) {D : ℝ} (hD : 0 < D)
    {u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∀ᶠ n : ℕ in atTop, Sizes.seqP d {ω | Sizes.seqHflow d n (u n) ω ∉
        GoodSetN (d.L n) (d.W n) (E n) (u n) k (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τg Dg} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -⟩ := hmain'
  obtain ⟨hlev1, hlev2, hlev3, hlev4⟩ := hlev
  have hgg := gridGoodN d κ c τ E s u t (fun _ => 1) hmain hK hKd hV hloc hdec hdl hsu hut
    (fun _ => one_ne_zero) k hk Λ Φ hΛ0 hΦ0 hΛ1 hlev1 hlev2 hlev3 hlev4 1
    ((hsize.eventually_ge_atTop 2).mono fun n hn => by
      rw [Real.rpow_one]; push_cast; linarith) ε hε τg hτg Dg hDg D hD
  filter_upwards [hgg] with n hn
  set G : Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
    GoodSetN (d.L n) (d.W n) (E n) (u n) k (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τg Dg with hG
  have hgt : gridTime s u (fun _ => 1) n 1 = u n := by
    unfold gridTime gridStep; simp
  have hH : Measurable (pathH d s u (fun _ => 1) n 1) :=
    Measurable.of_eval_matrix _ fun i j' => measurable_pathH d s u (fun _ => 1) n 1 i j'
  have hF : Measurable (Sizes.seqHflow d n (gridTime s u (fun _ => 1) n 1)) :=
    Measurable.of_eval_matrix _ fun i j' => Sizes.measurable_seqHflow_entry d n _ i j'
  have hmeas : MeasurableSet Gᶜ := (measurableGoodSetN _ _ _ _ _ _ _ _ _ _).compl
  have e1 := Measure.map_apply (μ := pathP d) hH hmeas
  have e2 := Measure.map_apply (μ := Sizes.seqP d) hF hmeas
  rw [map_pathH_eq d s u (fun _ => 1) n 1 (hs0 n) (hsu n) one_ne_zero] at e1
  have h1 : Sizes.seqP d {ω | Sizes.seqHflow d n (u n) ω ∉ G} =
      pathP d {ω | pathH d s u (fun _ => 1) n 1 ω ∉ G} := by
    rw [hgt] at e1 e2
    exact e2.symm.trans e1
  rw [h1]
  refine le_trans (measure_mono ?_) hn
  intro ω hω hcon
  have h1 := hcon 1 le_rfl
  rw [hgt] at h1
  exact hω h1

/-- **The good set holds at every time `u ∈ [s_n, v_n]`, eventually in `n`** (the sections lemma
`AltDriftQ_ev_forall_of_sections` applied to `AltLevelsQ_goodSet_seq`). -/
private theorem AltLevelsQ_goodSet {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (hmain : MainIndHyp d κ c τ E s t) (hK : KboundConcl κ) (hKd : KcalDecay κ)
    (hV : RBM.Green.GbEXPHypV3 d (κ / 2) c τ) (hloc : Step2LocalPT d E s t)
    (hdec : Step2DecayPT d E s t) (hdl : DecayLoopPT d E s t)
    {k : ℕ} (hk : 2 ≤ k) {Λ Φ : ℕ → ℝ} (hΛ0 : ∀ n, 0 ≤ Λ n) (hΦ0 : ∀ n, 0 ≤ Φ n)
    (hΛ1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) (hlev : STOeqLevels d E s t k Λ Φ)
    {ε : ℝ} (hε : 0 < ε) {τg : ℝ} (hτg : 0 < τg) {Dg : ℝ} (hDg : 0 < Dg) {D : ℝ} (hD : 0 < D)
    {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n) :
    ∀ᶠ n : ℕ in atTop, ∀ u : TimeIcc s v n, Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
        GoodSetN (d.L n) (d.W n) (E n) u k (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τg Dg} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) := by
  refine AltDriftQ_ev_forall_of_sections (U := fun n => TimeIcc s v n)
    (fun n => ⟨⟨s n, le_rfl, hsv n⟩⟩)
    (p := fun n u => Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
        GoodSetN (d.L n) (d.W n) (E n) u k (((d.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τg Dg} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))) fun sec => ?_
  exact AltLevelsQ_goodSet_seq hmain hK hKd hV hloc hdec hdl hk hΛ0 hΦ0 hΛ1 hlev hε hτg hDg hD
    (u := fun n => ((sec n : TimeIcc s v n) : ℝ)) (fun n => (sec n).2.1)
    (fun n => (sec n).2.2.trans (hvt n))

end Good

/-! ## 2. The tensors `B₁, B₂, B₃` on the good set -/

section Det123

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **`B₁, B₂, B₃` on the good set**: the clauses (D1)-(D3) and (V) of `GoodSetN` give, for every
`σ` and label `a`, `‖B_m(a)‖ ≤ k² Γ² Φ M_u^{-k} η_u^{-1} + W^{-D'}` and, at far labels,
`‖B_m(a)‖ ≤ W^{-D'}` (`driftTensor_norm_le_of_goodSet` for the individual terms). -/
private theorem AltLevelsQ_B123 {E u Γ Λ Φ τg Dg : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (hX0 : 0 ≤ (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τg Dg)
    (σ : Fin k → Bool) (m : Fin 6) (hm : m = 1 ∨ m = 2 ∨ m = 3) (a : Fin k → Z2 L) :
    ‖altB L W E u M σ m a‖ ≤
      (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) + (W : ℝ) ^ (-Dg) ∧
    (ellT L u * (W : ℝ) ^ τg ≤ (KLoop.maxDist L a : ℝ) →
      ‖altB L W E u M σ m a‖ ≤ (W : ℝ) ^ (-Dg)) := by
  obtain ⟨-, -, -, -, -, -, hD1, hD2, hD3, -, hV, -⟩ := hM
  set X0 : ℝ := (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ with hX0def
  have hQ0 : 0 ≤ Γ * (Γ * Φ) * X0 := by positivity
  have hWD0 : 0 ≤ (W : ℝ) ^ (-Dg) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hcard : ((Finset.Icc 3 k).card : ℝ) = (k : ℝ) - 2 ∨ k = 2 := by
    by_cases h2 : k = 2
    · exact Or.inr h2
    · left
      rw [Nat.card_Icc]
      have : k + 1 - 3 = k - 2 := by omega
      rw [this, Nat.cast_sub (by omega)]; simp
  rcases hm with rfl | rfl | rfl
  · -- `B₁ = Σ_{l = 3}^k [𝒦 ∼ (𝓛-𝒦)]^l`
    have hsum : ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ ≤
        (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by
      refine (norm_sum_le _ _).trans ?_
      have hle : ∀ l ∈ Finset.Icc 3 k, ‖ksimLK L W E u M l (loopOf σ a)‖ ≤
          Γ * (((k - 1 : ℕ) : ℝ) * (Γ * Φ)) * X0 := fun l hl =>
        hD1 l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2 σ a
      refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
      rw [nsmul_eq_mul, hk1]
      rcases hcard with hc | hc
      · rw [hc]
        have : ((k : ℝ) - 2) * (Γ * (((k : ℝ) - 1) * (Γ * Φ)) * X0) =
            ((k : ℝ) - 2) * ((k : ℝ) - 1) * (Γ * (Γ * Φ) * X0) := by ring
        rw [this]
        have h1 : ((k : ℝ) - 2) * ((k : ℝ) - 1) ≤ (k : ℝ) ^ 2 := by nlinarith
        calc ((k : ℝ) - 2) * ((k : ℝ) - 1) * (Γ * (Γ * Φ) * X0) ≤
            (k : ℝ) ^ 2 * (Γ * (Γ * Φ) * X0) := mul_le_mul_of_nonneg_right h1 hQ0
          _ = (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by ring
      · subst hc
        have h0 : ((Finset.Icc 3 2).card : ℝ) = 0 := by simp
        rw [h0, zero_mul]
        positivity
    refine ⟨?_, fun hfar => ?_⟩
    · change ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ ≤ _
      linarith
    · change ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)‖ ≤ _
      have := hV σ a hfar
      linarith [norm_nonneg (elklkN L W E u M (loopOf σ a)), norm_nonneg (egtN L W E u M (loopOf σ a))]
  · -- `B₂ = 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)}`
    have h2 := hD2 σ a
    refine ⟨?_, fun hfar => ?_⟩
    · change ‖elklkN L W E u M (loopOf σ a)‖ ≤ _
      refine h2.trans ?_
      rw [hk1]
      have : Γ * (((k : ℝ) - 1) * (Γ * Φ)) * X0 = ((k : ℝ) - 1) * (Γ * (Γ * Φ) * X0) := by ring
      rw [this]
      have h1 : ((k : ℝ) - 1) ≤ (k : ℝ) ^ 2 := by nlinarith
      have : ((k : ℝ) - 1) * (Γ * (Γ * Φ) * X0) ≤ (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by
        calc ((k : ℝ) - 1) * (Γ * (Γ * Φ) * X0) ≤ (k : ℝ) ^ 2 * (Γ * (Γ * Φ) * X0) :=
              mul_le_mul_of_nonneg_right h1 hQ0
          _ = (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by ring
      linarith
    · change ‖elklkN L W E u M (loopOf σ a)‖ ≤ _
      have := hV σ a hfar
      linarith [norm_nonneg (∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)),
        norm_nonneg (egtN L W E u M (loopOf σ a))]
  · -- `B₃ = 𝓔^{(G̃)}`
    have h3 := hD3 σ a
    refine ⟨?_, fun hfar => ?_⟩
    · change ‖egtN L W E u M (loopOf σ a)‖ ≤ _
      refine h3.trans ?_
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have : Γ * (Γ * Φ) * X0 ≤ (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by
        calc Γ * (Γ * Φ) * X0 = 1 * (Γ * (Γ * Φ) * X0) := (one_mul _).symm
          _ ≤ (k : ℝ) ^ 2 * (Γ * (Γ * Φ) * X0) := mul_le_mul_of_nonneg_right h1 hQ0
          _ = (k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 := by ring
      linarith
    · change ‖egtN L W E u M (loopOf σ a)‖ ≤ _
      have := hV σ a hfar
      linarith [norm_nonneg (∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)),
        norm_nonneg (elklkN L W E u M (loopOf σ a))]

end Det123

/-! ## 3. The tensors `B₄, B₅` on the good set -/

section Det45

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A loop index is `loopOf` of its sign and label vectors. -/
private theorem AltLevelsQ_loopOf_eq (J : LoopIdx (Z2 L)) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- `‖LKf‖` is at most `xiLK` times the inverse scale to the power of the loop length. -/
private theorem AltLevelsQ_lk_le_xiLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hpos : 0 < scaleM L W E u) {m : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m) :
    ‖LKf L W E u M J‖ ≤ xiLK L W E u M m * (scaleM L W E u)⁻¹ ^ m := by
  subst hlen
  have hJeq := AltLevelsQ_loopOf_eq J hJ
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

/-- A bound at far labels transfers to loop indices with two far labels. -/
private theorem AltLevelsQ_far_list {m : ℕ} {R Bf : ℝ} (F : LoopIdx (Z2 L) → ℂ)
    (h : ∀ (σ' : Fin m → Bool) (a' : Fin m → Z2 L),
      R ≤ (KLoop.maxDist L a' : ℝ) → ‖F (loopOf σ' a')‖ ≤ Bf)
    (J : LoopIdx (Z2 L)) (hJ : J.WF) (hlen : J.a.length = m)
    (hfar : ∃ x ∈ J.a, ∃ y ∈ J.a, R ≤ (zdist2 L (x - y) : ℝ)) : ‖F J‖ ≤ Bf := by
  subst hlen
  have hJeq := AltLevelsQ_loopOf_eq J hJ
  rw [← hJeq]
  refine h _ _ ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := hfar
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  refine le_trans hxy ?_
  exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
    zdist2 L (J.a[q.1.1] - J.a[q.2.1])) (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length)))

/-- **`B₄, B₅` on the good set** (`jywiiwsoks`, `kkuuwsaf`, `kkuuwsaf5`):
`B45_core_det_pub` with `R = ℓ_u W^{τ_g}`, `X = Γ Φ M_u^{-(k-1)}` (clause (G2), rank `k-1`) and
`B_f = W^{-D_g}` (clause (Dec)); the same reading of `GoodSetN` as in `altLastStep_of_goodSet`. -/
private theorem AltLevelsQ_B45 (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {k : ℕ} [NeZero k] (hk : 2 ≤ k) {Γ Λ Φ τg Dg : ℝ}
    (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (hτg : 0 ≤ τg) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τg Dg) {σ : Fin k → Bool} (hσ : Alternating σ)
    (a : Fin k → Z2 L) :
    ‖B5 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ * altLastLevel L W E u k Γ Φ τg Dg) ∧
    ‖B4 L W E u M σ a‖ ≤ 2 * (k : ℝ) * ((1 - u)⁻¹ * altLastLevel L W E u k Γ Φ τg Dg) := by
  have hMh : M.IsHermitian := hM.1
  have hLp : 1 ≤ L := by omega
  have hMpos := scaleM_pos hLp hW hE hu1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hR0 : 0 ≤ ellT L u * (W : ℝ) ^ τg := by
    have := (ellT_pos_le hLp hu1).1
    positivity
  have hX0 : 0 ≤ Γ * Φ * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hMpos.le
    positivity
  have hBf0 : 0 ≤ (W : ℝ) ^ (-Dg) := Real.rpow_nonneg hW0.le _
  obtain ⟨-, -, hG2, -, -, hDec, -⟩ := hM
  have hxi : xiLK L W E u M (k - 1) ≤ Γ * Φ := hG2 (k - 1) (by omega) (by omega)
  have hXl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      ‖LKf L W E u M J‖ ≤ Γ * Φ * (scaleM L W E u)⁻¹ ^ (k - 1) := by
    intro J hJ hlen
    have h := AltLevelsQ_lk_le_xiLK E u M hMpos J hJ hlen
    exact h.trans (mul_le_mul_of_nonneg_right hxi (by
      have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 hMpos.le
      positivity))
  have hBl : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      (∃ x ∈ J.a, ∃ y ∈ J.a, ellT L u * (W : ℝ) ^ τg ≤ (zdist2 L (x - y) : ℝ)) →
      ‖LKf L W E u M J‖ ≤ (W : ℝ) ^ (-Dg) := by
    intro J hJ hlen hfar
    refine AltLevelsQ_far_list (m := k - 1) (LKf L W E u M) (fun σ' a' hfa => ?_) J hJ hlen hfar
    have h := hDec (k - 1) (by omega) (by omega) σ' a' hfa
    have h0 : 0 ≤ loopAbs L W E u M σ' a' := norm_nonneg _
    have : ‖LKf L W E u M (loopOf σ' a')‖ = lkGen L W E u M σ' a' := rfl
    rw [this]; linarith
  have h := B45_core_det_pub hL hW hE hu0 hu1 hMh hk hσ hR0 hX0 hBf0 hXl hBl a
  exact h

end Det45

/-! ## 4. Arithmetic of the levels of `B₄, B₅` -/

section Arith45

/-- The near part of the arithmetic of `B45_core_det_pub`:
`(W²η)⁻¹ ((2R+1)²)^m X c^{m+1} ≤ 9^m C^{m+1} (w²)^m Y (M⁻¹)^{m+2}` for `R = ℓ w`,
`X = Y (M⁻¹)^{m+1}`, `c = C ℓ⁻²`, `M = W²ℓ²η` (the exponents of `ℓ` cancel exactly). -/
private theorem AltLevelsQ_arith_near {m : ℕ} {Wr ℓ η M Y Cc w : ℝ} (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ)
    (hη : 0 < η) (hw : 1 ≤ w) (hY : 0 ≤ Y) (hCc : 0 ≤ Cc) (hM : M = Wr ^ 2 * ℓ ^ 2 * η) :
    (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Y * (M⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2) := by
  have hW0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hR1 : 1 ≤ ℓ * w := by nlinarith
  have h9 : (2 * (ℓ * w) + 1) ^ 2 ≤ 9 * ℓ ^ 2 * w ^ 2 := by nlinarith
  have hpow : ((2 * (ℓ * w) + 1) ^ 2) ^ m ≤ (9 * ℓ ^ 2 * w ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) h9 m
  have hinv : (Wr ^ 2 * η)⁻¹ = ℓ ^ 2 * M⁻¹ := by rw [hM]; field_simp
  have hq : ℓ ^ 2 * (ℓ ^ 2) ^ m * ((ℓ ^ 2)⁻¹) ^ (m + 1) = 1 := by
    rw [← pow_succ', ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  have hnn : 0 ≤ (Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
  calc (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Y * (M⁻¹) ^ (m + 1))) *
        (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)
      = ((2 * (ℓ * w) + 1) ^ 2) ^ m *
        ((Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) := by ring
    _ ≤ (9 * ℓ ^ 2 * w ^ 2) ^ m *
        ((Wr ^ 2 * η)⁻¹ * (Y * (M⁻¹) ^ (m + 1)) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = (ℓ ^ 2 * (ℓ ^ 2) ^ m * ((ℓ ^ 2)⁻¹) ^ (m + 1)) *
        (9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2)) := by
        rw [hinv]; ring
    _ = 9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * Y * (M⁻¹) ^ (m + 2) := by rw [hq, one_mul]

/-- **The level of `B₄, B₅`** (all quantities real): with `R = ℓ w`, `X = Γ Φ M⁻ᵏ⁺¹`, `c = C ℓ⁻²`,
`M = W²ℓ²η`, `(1-u)⁻¹ ≤ η⁻¹ ≤ N`, `L² ≤ N`:
`2k (1-u)⁻¹ (W²η)⁻¹ (((2R+1)²)^{k-2} X + (L²)^{k-2} B_f) c^{k-1}
  ≤ (2k 9^{k-2} C^{k-1} Γ (w²)^{k-2}) · Φ M^{-k} η⁻¹ + 2k C^{k-1} N^k B_f`.
The coefficient of the main term does not involve `Φ ≥ 1`: the far part `B_f` is not absorbed into it. -/
private theorem AltLevelsQ_arith45 {k : ℕ} (hk : 2 ≤ k)
    {Nr Wr Lr ℓ η u Mm Γ Φ w Cc Bf : ℝ} (hW : 1 ≤ Wr) (hℓ : 1 ≤ ℓ) (hη : 0 < η)
    (hηle : η ≤ 1 - u) (hMdef : Mm = Wr ^ 2 * ℓ ^ 2 * η) (hN1 : 1 ≤ Nr)
    (hLN : Lr ^ 2 ≤ Nr) (hηN : η⁻¹ ≤ Nr) (hCc0 : 0 ≤ Cc) (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ)
    (hw : 1 ≤ w) (hBf0 : 0 ≤ Bf) :
    2 * (k : ℝ) * ((1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ *
        (((2 * (ℓ * w) + 1) ^ 2) ^ (k - 2) * (Γ * Φ * (Mm⁻¹) ^ (k - 1)) +
          (Lr ^ 2) ^ (k - 2) * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (k - 1))) ≤
      (2 * (k : ℝ) * 9 ^ (k - 2) * Cc ^ (k - 1) * Γ * (w ^ 2) ^ (k - 2)) *
          (Φ * ((Mm ^ k)⁻¹ * η⁻¹)) + 2 * (k : ℝ) * Cc ^ (k - 1) * Nr ^ k * Bf := by
  obtain ⟨m, hkm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hk2 : k - 2 = m := by omega
  have hk1 : k - 1 = m + 1 := by omega
  rw [hk2, hk1, hkm]
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hMm0 : 0 < Mm := by rw [hMdef]; positivity
  have hnear := AltLevelsQ_arith_near (m := m) (Wr := Wr) (ℓ := ℓ) (η := η) (M := Mm)
    (Y := Γ * Φ) (Cc := Cc) (w := w) hW hℓ hη hw (by positivity) hCc0 hMdef
  have hinv1 : (1 - u)⁻¹ ≤ η⁻¹ := inv_anti₀ hη hηle
  have h1 : (Wr ^ 2 * η)⁻¹ ≤ Nr := by
    refine le_trans ?_ hηN
    refine inv_anti₀ hη ?_
    have : 1 ≤ Wr ^ 2 := one_le_pow₀ hW
    nlinarith
  have h2 : (Lr ^ 2) ^ m ≤ Nr ^ m := pow_le_pow_left₀ (by positivity) hLN m
  have h3 : (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤ Cc ^ (m + 1) := by
    have : (ℓ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ)
    have h4 : Cc * (ℓ ^ 2)⁻¹ ≤ Cc := mul_le_of_le_one_right hCc0 this
    exact pow_le_pow_left₀ (by positivity) h4 _
  have hfar : (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) ≤
      Nr * (Nr ^ m * Bf) * Cc ^ (m + 1) := by
    have hc0 : 0 ≤ (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
    gcongr
  have hsplit : (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Γ * Φ * (Mm⁻¹) ^ (m + 1)) +
        (Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) =
      (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Γ * Φ * (Mm⁻¹) ^ (m + 1))) *
          (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) +
        (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by ring
  have hP0 : 0 ≤ (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Γ * Φ * (Mm⁻¹) ^ (m + 1)) +
        (Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
  have hkk : (0 : ℝ) ≤ 2 * ((m + 2 : ℕ) : ℝ) := by positivity
  have hnear' : (1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m *
        (Γ * Φ * (Mm⁻¹) ^ (m + 1))) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) ≤
      η⁻¹ * (9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * (Γ * Φ) * (Mm⁻¹) ^ (m + 2)) := by
    have hn0 : 0 ≤ (Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m *
        (Γ * Φ * (Mm⁻¹) ^ (m + 1))) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by positivity
    calc _ ≤ η⁻¹ * ((Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m *
        (Γ * Φ * (Mm⁻¹) ^ (m + 1))) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_right hinv1 hn0
      _ ≤ _ := mul_le_mul_of_nonneg_left hnear (inv_nonneg.2 hη.le)
  have hfar' : (1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) ≤
      Nr * (Nr * (Nr ^ m * Bf) * Cc ^ (m + 1)) := by
    have hf0 : 0 ≤ (Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1) := by
      positivity
    calc _ ≤ η⁻¹ * ((Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_right hinv1 hf0
      _ ≤ Nr * ((Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_right hηN hf0
      _ ≤ _ := mul_le_mul_of_nonneg_left hfar hN0.le
  calc 2 * ((m + 2 : ℕ) : ℝ) * ((1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ *
        (((2 * (ℓ * w) + 1) ^ 2) ^ m * (Γ * Φ * (Mm⁻¹) ^ (m + 1)) +
          (Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)))
      = 2 * ((m + 2 : ℕ) : ℝ) * ((1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ * (((2 * (ℓ * w) + 1) ^ 2) ^ m *
        (Γ * Φ * (Mm⁻¹) ^ (m + 1))) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1)) +
        (1 - u)⁻¹ * ((Wr ^ 2 * η)⁻¹ * ((Lr ^ 2) ^ m * Bf) * (Cc * (ℓ ^ 2)⁻¹) ^ (m + 1))) := by
        rw [hsplit]; ring
    _ ≤ 2 * ((m + 2 : ℕ) : ℝ) * (η⁻¹ * (9 ^ m * Cc ^ (m + 1) * (w ^ 2) ^ m * (Γ * Φ) *
          (Mm⁻¹) ^ (m + 2)) + Nr * (Nr * (Nr ^ m * Bf) * Cc ^ (m + 1))) :=
        mul_le_mul_of_nonneg_left (add_le_add hnear' hfar') hkk
    _ = (2 * ((m + 2 : ℕ) : ℝ) * 9 ^ m * Cc ^ (m + 1) * Γ * (w ^ 2) ^ m) *
          (Φ * ((Mm ^ (m + 2))⁻¹ * η⁻¹)) +
        2 * ((m + 2 : ℕ) : ℝ) * Cc ^ (m + 1) * Nr ^ (m + 2) * Bf := by
        rw [inv_pow]; ring

end Arith45

/-! ## 5. `𝒬_u` of the tensors, and the deterministic level bound on the good set -/

section Final

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `‖(𝒬_u A)_a‖ ≤ W^{cτ} T + W^{-D+c}` from `qopNorm` (`QopNorm` instance `hq`), if `A`
has `(u,τ,D)` decay and `‖A‖_max ≤ T`. -/
private theorem AltLevelsQ_Qop_le {k : ℕ} [NeZero k] {u τg Dg cp : ℝ}
    (hq : ∀ A : (Fin k → Z2 L) → ℂ, HasDecay L W u τg Dg A →
      tmax L (Qop L u A) ≤ (W : ℝ) ^ (cp * τg) * tmax L A + (W : ℝ) ^ (-Dg + cp))
    {A : (Fin k → Z2 L) → ℂ} (hdec : HasDecay L W u τg Dg A) {T : ℝ} (hT : ∀ a, ‖A a‖ ≤ T)
    (a : Fin k → Z2 L) :
    ‖Qop L u A a‖ ≤ (W : ℝ) ^ (cp * τg) * T + (W : ℝ) ^ (-Dg + cp) := by
  have h1 := hq A hdec
  have h2 : ‖Qop L u A a‖ ≤ tmax L (Qop L u A) :=
    Finset.le_sup' (fun a => ‖Qop L u A a‖) (Finset.mem_univ a)
  have h3 : tmax L A ≤ T := Finset.sup'_le _ _ (fun a _ => hT a)
  have hP : 0 ≤ (W : ℝ) ^ (cp * τg) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ‖Qop L u A a‖ ≤ (W : ℝ) ^ (cp * τg) * tmax L A + (W : ℝ) ^ (-Dg + cp) := h2.trans h1
    _ ≤ (W : ℝ) ^ (cp * τg) * T + (W : ℝ) ^ (-Dg + cp) := by
        have := mul_le_mul_of_nonneg_left h3 hP
        linarith

/-- **The level bound for `m = 1, 2, 3`** on the good set: `‖(𝒬_u B_m)_a‖ ≤ N_t · altQLevel`, `N_t = N^{τ₀}`
(`N_t ≥ 2`, `k²Γ² ≤ N_t`; `cp = cPrec 𝔠 k`, `hq` the `qopNorm` at `(𝔠, k, τ_g, D_g)`). -/
private theorem AltLevelsQ_final123 {E u : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hW : 1 ≤ W)
    {Γ Λ Φ τg Dg Nt τ' Db cp : ℝ} (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ)
    (hMpos : 0 < scaleM L W E u) (hη : 0 < etaT E u)
    (hq : ∀ A : (Fin k → Z2 L) → ℂ, HasDecay L W u τg Dg A →
      tmax L (Qop L u A) ≤ (W : ℝ) ^ (cp * τg) * tmax L A + (W : ℝ) ^ (-Dg + cp))
    (hcp : 0 ≤ cp) (hτg0 : 0 ≤ τg)
    (hτg : (cp + 2 * ((k : ℝ) - 2)) * τg ≤ 2 * ((k : ℝ) - 1) * τ')
    (hDg1 : Db + cp * τg ≤ Dg) (hDg2 : Db + cp ≤ Dg) (hNt : 2 ≤ Nt)
    (hΓ2 : (k : ℝ) ^ 2 * (Γ * Γ) ≤ Nt)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τg Dg)
    (σ : Fin k → Bool) (m : Fin 6) (hm : m = 1 ∨ m = 2 ∨ m = 3) (a : Fin k → Z2 L) :
    ‖altQB L W E u M σ m a‖ ≤ Nt * altQLevel L W E k τ' Db Φ u := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set X0 : ℝ := (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ with hX0def
  have hX0 : 0 ≤ X0 := by positivity
  have hB := fun a' => AltLevelsQ_B123 (L := L) (W := W) (E := E) (u := u) hk hΓ hΦ hX0 hM σ m hm a'
  have hdec : HasDecay L W u τg Dg (altB L W E u M σ m) := fun a' hfar => (hB a').2 hfar
  have hQ := AltLevelsQ_Qop_le (u := u) hq hdec (fun a' => (hB a').1) a
  have hQ' : ‖altQB L W E u M σ m a‖ ≤ (W : ℝ) ^ (cp * τg) *
      ((k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 + (W : ℝ) ^ (-Dg)) + (W : ℝ) ^ (-Dg + cp) := hQ
  have hP : (W : ℝ) ^ (cp * τg) ≤ (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') := by
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have e2 : (cp + 2 * ((k : ℝ) - 2)) * τg = cp * τg + 2 * ((k : ℝ) - 2) * τg := by ring
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * ((k : ℝ) - 2)) hτg0
    linarith
  have hexp1 : (W : ℝ) ^ (cp * τg) * (W : ℝ) ^ (-Dg) ≤ (W : ℝ) ^ (-Db) := by
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hexp2 : (W : ℝ) ^ (-Dg + cp) ≤ (W : ℝ) ^ (-Db) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hWb0 : 0 ≤ (W : ℝ) ^ (-Db) := Real.rpow_nonneg hW0.le _
  have hΦX : 0 ≤ Φ * X0 := mul_nonneg hΦ hX0
  have hmain : (W : ℝ) ^ (cp * τg) * ((k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0) ≤
      Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * X0)) := by
    have e : (W : ℝ) ^ (cp * τg) * ((k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0) =
        ((k : ℝ) ^ 2 * (Γ * Γ)) * ((W : ℝ) ^ (cp * τg) * (Φ * X0)) := by ring
    rw [e]
    have hp0 : 0 ≤ (W : ℝ) ^ (cp * τg) := Real.rpow_nonneg hW0.le _
    have h1 : (W : ℝ) ^ (cp * τg) * (Φ * X0) ≤ (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * X0) :=
      mul_le_mul_of_nonneg_right hP hΦX
    have h2 : 0 ≤ (W : ℝ) ^ (cp * τg) * (Φ * X0) := mul_nonneg hp0 hΦX
    calc ((k : ℝ) ^ 2 * (Γ * Γ)) * ((W : ℝ) ^ (cp * τg) * (Φ * X0))
        ≤ Nt * ((W : ℝ) ^ (cp * τg) * (Φ * X0)) := mul_le_mul_of_nonneg_right hΓ2 h2
      _ ≤ Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * X0)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
  unfold altQLevel
  calc ‖altQB L W E u M σ m a‖
      ≤ (W : ℝ) ^ (cp * τg) * ((k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0 + (W : ℝ) ^ (-Dg)) +
          (W : ℝ) ^ (-Dg + cp) := hQ'
    _ = (W : ℝ) ^ (cp * τg) * ((k : ℝ) ^ 2 * (Γ * (Γ * Φ)) * X0) +
          (W : ℝ) ^ (cp * τg) * (W : ℝ) ^ (-Dg) + (W : ℝ) ^ (-Dg + cp) := by ring
    _ ≤ Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * X0)) + (W : ℝ) ^ (-Db) +
          (W : ℝ) ^ (-Db) := by linarith
    _ ≤ Nt * (Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * X0 + (W : ℝ) ^ (-Db)) := by
        have : Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * X0)) =
            Nt * (Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * X0) := by ring
        rw [this, mul_add]
        linarith [mul_le_mul_of_nonneg_right hNt hWb0]

private theorem AltLevelsQ_Psum_sub (A B : (Fin k → Z2 L) → ℂ) (x : Z2 L) [NeZero k] :
    Psum L (fun b => A b - B b) x = Psum L A x - Psum L B x := by
  simp only [Psum, Finset.sum_sub_distrib]

/-- `N^a ≤ W^{a/c}` from `N^c ≤ W` (for real `N, W`). -/
private theorem AltLevelsQ_N_pow_le {N Wr c a : ℝ} (hN : 0 ≤ N) (hc : 0 < c) (ha : 0 ≤ a)
    (hb : N ^ c ≤ Wr) : N ^ a ≤ Wr ^ (a / c) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hN c) hb (div_nonneg ha hc.le)
  rwa [← Real.rpow_mul hN, mul_div_cancel₀ _ hc.ne'] at h

/-- **`𝒬_u ℬ_m = ℬ_m` for `m = 4, 5`**: `𝒫ℬ₄ = 0` (`𝒫𝒬_u = 0` and `ϴ` preserves sum zero) and
`𝒫ℬ₅ = (𝒫(𝓛-𝒦))_{a₁} 𝒫ϑ̇ = 0` (as in the proof of `dGridQN_eq_dFlowQ`).  So no `qopNorm` is
needed for `m = 4, 5`. -/
private theorem AltLevelsQ_altQB_four_five (hL : 3 ≤ L) {E u : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin k → Bool) (m : Fin 6) (hm : m = 4 ∨ m = 5) (a : Fin k → Z2 L) :
    altQB L W E u M σ m a = altB L W E u M σ m a := by
  have hu : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
  rcases hm with rfl | rfl
  · -- `ℬ₄`
    have hB4 : SumZero L (fun b => B4 L W E u M σ b) := by
      intro a₁
      change Psum L (fun b => B4 L W E u M σ b) a₁ = 0
      have e : (fun b => B4 L W E u M σ b) =
          fun b => Qop L u (thetaSig L E σ u (lkTensor L W E u M σ)) b -
            thetaSig L E σ u (Qop L u (lkTensor L W E u M σ)) b := rfl
      rw [e, AltLevelsQ_Psum_sub, SumZeroQ_Psum_Qop hL hu]
      have hs : SumZero L (thetaSig L E σ u (Qop L u (lkTensor L W E u M σ))) :=
        SumZeroQ_SumZero_thetaSig hL hE σ hu0 hu1 (fun a₁ => SumZeroQ_Psum_Qop hL hu _ a₁)
      have := hs a₁
      change Psum L (thetaSig L E σ u (Qop L u (lkTensor L W E u M σ))) a₁ = 0 at this
      rw [this]; ring
    exact congrFun (SumZeroQ_Qop_of_sumZero u hB4) a
  · -- `ℬ₅`
    have hB5 : SumZero L (fun b => B5 L W E u M σ b) := by
      intro a₁
      have hd := SumZeroQ_Psum_varthetaDot hL hk hu a₁
      unfold B5
      have : ∀ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          Psum L (lkTensor L W E u M σ) (a 0) * varthetaDot L u a =
            Psum L (lkTensor L W E u M σ) a₁ * varthetaDot L u a := by
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      have hd' : ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁),
          varthetaDot L u a = 0 := hd
      rw [hd', mul_zero]
    exact congrFun (SumZeroQ_Qop_of_sumZero u hB5) a

/-- **The level bound for `m = 4, 5`** on the good set: `‖(𝒬_u B_m)_a‖ = ‖B_m(a)‖ ≤ N_t · altQLevel`,
from `AltLevelsQ_B45` (`B45_core_det_pub`) and `AltLevelsQ_arith45`; the far part of
rank `k-1` goes to the additive term `W^{-D_b}`, so `Φ ≥ 1` is not used. -/
private theorem AltLevelsQ_final45 (hL : 3 ≤ L) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {k : ℕ} [NeZero k] (hk : 2 ≤ k) {c N : ℝ} (hc : 0 < c)
    (hN : N = (W : ℝ) ^ 2 * (L : ℝ) ^ 2) (hNW : N ^ c ≤ (W : ℝ)) (hηN : (etaT E u)⁻¹ ≤ N)
    {Γ Λ Φ τg Dg Nt τ' Db cp : ℝ} (hΓ : 0 ≤ Γ) (hΦ : 0 ≤ Φ) (hτg0 : 0 ≤ τg) (hcp : 0 ≤ cp)
    (hτg : (cp + 2 * ((k : ℝ) - 2)) * τg ≤ 2 * ((k : ℝ) - 1) * τ')
    (hDg : Db + ((k : ℝ) + 1) / c ≤ Dg) (hNt : 1 ≤ Nt)
    (hcoef : 2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log L)) ^ (k - 1) * Γ ≤ Nt)
    (hpoly : 2 * (k : ℝ) * (180 * 40002 ^ 2 * (1 + Real.log L)) ^ (k - 1) ≤ N)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetN L W E u k Γ Λ Φ τg Dg)
    {σ : Fin k → Bool} (hσ : Alternating σ) (m : Fin 6) (hm : m = 4 ∨ m = 5) (a : Fin k → Z2 L) :
    ‖altQB L W E u M σ m a‖ ≤ Nt * altQLevel L W E k τ' Db Φ u := by
  have hLp : 1 ≤ L := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hLp
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hηle : etaT E u ≤ 1 - u := by
    unfold etaT
    have h1 : (spectralM E).im ≤ 1 := by
      rw [spectralM_im]
      have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
      linarith
    have h2 : 0 ≤ 1 - u := by linarith
    calc (1 - u) * (spectralM E).im ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = 1 - u := mul_one _
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT hLp hu0 hu1
  have hMpos : 0 < scaleM L W E u := scaleM_pos hLp hW hE hu1
  have hN1 : 1 ≤ N := by
    rw [hN]
    have h1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hW1
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hLp)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hN0 : 0 < N := by linarith
  have hLN : (L : ℝ) ^ 2 ≤ N := by
    rw [hN]
    have h1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hW1
    exact le_mul_of_one_le_left (by positivity) h1
  have hlog0 : 0 ≤ 1 + Real.log (L : ℝ) := by
    have := Real.log_natCast_nonneg L
    linarith
  have hCc0 : 0 ≤ 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ)) := by positivity
  have hw1 : 1 ≤ (W : ℝ) ^ τg := Real.one_le_rpow hW1 hτg0
  have hBf0 : 0 ≤ (W : ℝ) ^ (-Dg) := Real.rpow_nonneg hW0.le _
  have hB := AltLevelsQ_B45 hL hW hE hu0 hu1 hk hΓ hΦ hτg0 hM hσ a
  have hbound : ‖altQB L W E u M σ m a‖ ≤
      2 * (k : ℝ) * ((1 - u)⁻¹ * altLastLevel L W E u k Γ Φ τg Dg) := by
    rw [AltLevelsQ_altQB_four_five hL hk hE hu0 hu1 M σ m hm a]
    rcases hm with rfl | rfl
    · exact hB.2
    · exact hB.1
  refine hbound.trans ?_
  unfold altLastLevel
  have hA := AltLevelsQ_arith45 (k := k) hk (Nr := N) (Wr := (W : ℝ)) (Lr := (L : ℝ))
    (ℓ := ellT L u) (η := etaT E u) (u := u) (Mm := scaleM L W E u) (Γ := Γ) (Φ := Φ)
    (w := (W : ℝ) ^ τg) (Cc := 180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) (Bf := (W : ℝ) ^ (-Dg))
    hW1 hℓ1 hη hηle rfl hN1 hLN hηN hCc0 hΓ hΦ hw1 hBf0
  refine hA.trans ?_
  -- the near coefficient
  have hwpow : ((((W : ℝ) ^ τg) ^ 2) ^ (k - 2)) ≤ (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') := by
    have e : ((((W : ℝ) ^ τg) ^ 2) ^ (k - 2)) = (W : ℝ) ^ (2 * ((k : ℝ) - 2) * τg) := by
      rw [← Real.rpow_natCast ((W : ℝ) ^ τg) 2, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hW0.le]
      congr 1
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [e]
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have e2 : (cp + 2 * ((k : ℝ) - 2)) * τg = cp * τg + 2 * ((k : ℝ) - 2) * τg := by ring
    have := mul_nonneg hcp hτg0
    linarith
  have hX0 : 0 ≤ (scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹ := by positivity
  have hnear : (2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) ^ (k - 1) *
        Γ * (((W : ℝ) ^ τg) ^ 2) ^ (k - 2)) *
      (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) ≤
      Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) := by
    have hq0 : 0 ≤ Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) := mul_nonneg hΦ hX0
    have hwp0 : 0 ≤ (((W : ℝ) ^ τg) ^ 2) ^ (k - 2) := by positivity
    calc (2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) ^ (k - 1) *
          Γ * (((W : ℝ) ^ τg) ^ 2) ^ (k - 2)) *
        (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))
        = (2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) ^ (k - 1) * Γ) *
          ((((W : ℝ) ^ τg) ^ 2) ^ (k - 2) *
            (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) := by ring
      _ ≤ Nt * ((((W : ℝ) ^ τg) ^ 2) ^ (k - 2) *
            (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hwp0 hq0)
      _ ≤ Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') *
            (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact mul_le_mul_of_nonneg_right hwpow hq0
  -- the far part
  have hfar : 2 * (k : ℝ) * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) ^ (k - 1) * N ^ k *
      (W : ℝ) ^ (-Dg) ≤ (W : ℝ) ^ (-Db) := by
    have hNk : N ^ (k + 1) ≤ (W : ℝ) ^ (((k : ℝ) + 1) / c) := by
      have h := AltLevelsQ_N_pow_le hN0.le hc (a := ((k : ℝ) + 1)) (by positivity) hNW
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
      simpa using h
    have hD0 : 0 ≤ (W : ℝ) ^ (-Dg) := hBf0
    calc 2 * (k : ℝ) * (180 * 40002 ^ 2 * (1 + Real.log (L : ℝ))) ^ (k - 1) * N ^ k *
          (W : ℝ) ^ (-Dg)
        ≤ N * N ^ k * (W : ℝ) ^ (-Dg) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (by positivity)) hD0
      _ = N ^ (k + 1) * (W : ℝ) ^ (-Dg) := by ring
      _ ≤ (W : ℝ) ^ (((k : ℝ) + 1) / c) * (W : ℝ) ^ (-Dg) :=
          mul_le_mul_of_nonneg_right hNk hD0
      _ = (W : ℝ) ^ (((k : ℝ) + 1) / c + -Dg) := by rw [Real.rpow_add hW0]
      _ ≤ (W : ℝ) ^ (-Db) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  unfold altQLevel
  have hWb0 : 0 ≤ (W : ℝ) ^ (-Db) := Real.rpow_nonneg hW0.le _
  calc _ ≤ Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) +
        (W : ℝ) ^ (-Db) := add_le_add hnear hfar
    _ ≤ Nt * (Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹) +
        (W : ℝ) ^ (-Db)) := by
        rw [mul_add]
        have : Nt * ((W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') *
            (Φ * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹))) =
            Nt * (Φ * (W : ℝ) ^ (2 * ((k : ℝ) - 1) * τ') * ((scaleM L W E u ^ k)⁻¹ * (etaT E u)⁻¹)) := by
          ring
        rw [this]
        have := le_mul_of_one_le_left hWb0 hNt
        linarith

end Final

/-! ## 6. The eventual numerical facts and the theorem -/

section Main

variable {d}

/-- `K (1 + log N)^j ≤ N^ε` eventually (`1 + log N ≺ 1`, `one_add_log_detDom_one`). -/
private theorem AltLevelsQ_eventually_log_pow (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ N : ℕ in atTop, K * (1 + Real.log N) ^ j ≤ (N : ℝ) ^ ε := by
  have hε' : 0 < ε / (2 * ((j : ℝ) + 1)) := by positivity
  have h1 := detDom_iff.mp one_add_log_detDom_one (ε / (2 * ((j : ℝ) + 1))) hε'
  have h2 : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN3
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hlog0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  have hb : 1 + Real.log N ≤ (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1))) := by simpa using hN1
  have h3 : (1 + Real.log N) ^ j ≤ (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) := by
    calc (1 + Real.log N) ^ j ≤ ((N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)))) ^ j :=
          pow_le_pow_left₀ hlog0 hb j
      _ = (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have h4 : ε / (2 * ((j : ℝ) + 1)) * j ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [hε]
  calc K * (1 + Real.log N) ^ j ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / (2 * ((j : ℝ) + 1)) * j) :=
        mul_le_mul hN2 h3 (by positivity) (by positivity)
    _ = (N : ℝ) ^ (ε / 2 + ε / (2 * ((j : ℝ) + 1)) * j) := by rw [← Real.rpow_add hN0]
    _ ≤ (N : ℝ) ^ ε := by
        refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
        linarith

/-- `η_u⁻¹ ≤ η_t⁻¹` for `u ≤ t < 1`. -/
private theorem AltLevelsQ_etaT_inv_anti {E u t : ℝ} (hE : |E| < 2) (hut : u ≤ t) (ht1 : t < 1) :
    (etaT E u)⁻¹ ≤ (etaT E t)⁻¹ := by
  refine inv_anti₀ (etaT_pos hE ht1) ?_
  unfold etaT
  exact mul_le_mul_of_nonneg_right (by linarith) (spectralM_im_pos hE).le

/-- **The eventual numerical facts** (polylogarithmic absorptions): for `τ₀ > 0`, eventually in `n`,
with `N = size n`, `Γ = N^{τ₀/4}`, `C_L = 180·40002²(1 + log L)`:
`2 ≤ N^{τ₀}`, `k² Γ² ≤ N^{τ₀}`, `2k 9^{k-2} C_L^{k-1} Γ ≤ N^{τ₀}`, `2k C_L^{k-1} ≤ N`. -/
private theorem AltLevelsQ_ev_nums (hsize : SizeTendsto d) (k : ℕ) {τ0 : ℝ} (hτ0 : 0 < τ0) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ0 ∧
      (k : ℝ) ^ 2 * (((d.size n : ℕ) : ℝ) ^ (τ0 / 4) * ((d.size n : ℕ) : ℝ) ^ (τ0 / 4)) ≤
        ((d.size n : ℕ) : ℝ) ^ τ0 ∧
      2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1) *
          ((d.size n : ℕ) : ℝ) ^ (τ0 / 4) ≤ ((d.size n : ℕ) : ℝ) ^ τ0 ∧
      2 * (k : ℝ) * (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1) ≤
        ((d.size n : ℕ) : ℝ) := by
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hK1 : 0 ≤ 2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2) ^ (k - 1) := by positivity
  have hK2 : 0 ≤ 2 * (k : ℝ) * (180 * 40002 ^ 2) ^ (k - 1) := by positivity
  have e1 := ((tendsto_rpow_atTop hτ0).comp hsize).eventually_ge_atTop 2
  have e2 := ((tendsto_rpow_atTop (half_pos hτ0)).comp hsize).eventually_ge_atTop ((k : ℝ) ^ 2)
  have e3 := hsizeN.eventually (AltLevelsQ_eventually_log_pow _ (τ0 / 2) hK1 (half_pos hτ0) (k - 1))
  have e4 := hsizeN.eventually (AltLevelsQ_eventually_log_pow _ 1 hK2 one_pos (k - 1))
  filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
  simp only [Function.comp] at h1 h2
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := GoodEvent_one_le_size (d := d) n
  have hN0 : 0 < N := by linarith
  have hL0 : (0 : ℝ) < d.L n := by exact_mod_cast (d.three_le_L n).trans_lt' (by norm_num)
  have hlogle : Real.log (d.L n : ℝ) ≤ Real.log N :=
    Real.log_le_log hL0 (NonAltEnd_L_le_size d n)
  have hlog0 : 0 ≤ 1 + Real.log (d.L n : ℝ) := by
    have := Real.log_natCast_nonneg (d.L n)
    linarith
  have hCle : (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1) ≤
      (180 * 40002 ^ 2) ^ (k - 1) * (1 + Real.log N) ^ (k - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) _
  have hG : N ^ (τ0 / 4) * N ^ (τ0 / 4) = N ^ (τ0 / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [hG]
    have : N ^ (τ0 / 2) * N ^ (τ0 / 2) = N ^ τ0 := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    calc (k : ℝ) ^ 2 * N ^ (τ0 / 2) ≤ N ^ (τ0 / 2) * N ^ (τ0 / 2) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN0.le _)
      _ = N ^ τ0 := this
  · have h5 : 2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1) ≤
        N ^ (τ0 / 2) := by
      refine le_trans ?_ h3
      calc 2 * (k : ℝ) * 9 ^ (k - 2) * (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1)
          ≤ 2 * (k : ℝ) * 9 ^ (k - 2) * ((180 * 40002 ^ 2) ^ (k - 1) * (1 + Real.log N) ^ (k - 1)) :=
            mul_le_mul_of_nonneg_left hCle (by positivity)
        _ = _ := by ring
    have h6 : N ^ (τ0 / 2) * N ^ (τ0 / 4) ≤ N ^ τ0 := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc _ ≤ N ^ (τ0 / 2) * N ^ (τ0 / 4) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hN0.le _)
      _ ≤ N ^ τ0 := h6
  · rw [Real.rpow_one] at h4
    refine le_trans ?_ h4
    calc 2 * (k : ℝ) * (180 * 40002 ^ 2 * (1 + Real.log (d.L n : ℝ))) ^ (k - 1)
        ≤ 2 * (k : ℝ) * ((180 * 40002 ^ 2) ^ (k - 1) * (1 + Real.log N) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hCle (by positivity)
      _ = _ := by ring

end Main

/-! ## 7. The theorem -/

section Pin

variable (d : Sizes)

/-- **Theorem `altLevelsQm`: part (b) of `AltLevelsQ`** — the
per-time levels of `𝒬_u B_m`, `m = 1..5`, `u ∈ [s_n, v_n]`, for alternating `σ` and every label:
`‖𝒬_u B_m(H_u)‖ ≺ Φ W^{2(k-1)τ'} M_u^{-k} η_u^{-1} + W^{-D_b}`.

Proof.  The good set `GoodSetN` (levels `Γ = N^{τ₀/4}`, window `τ_g = 2(k-1)τ'/(cPrec + 2(k-2))`,
decay `D_g`) holds at every time with probability `1 - N^{-D}` (`AltLevelsQ_goodSet`, via
`gridGoodN` with the one-step grid).  On it: `m = 1, 2, 3` by the clauses (D1)-(D3), (V) and
`qopNorm` (`AltLevelsQ_final123`); `m = 4, 5` by `𝒬_u B_m = B_m` (sum zero) and
`B45_core_det_pub` (`AltLevelsQ_final45`).  No hypothesis is added to `AltLevelsQm`. -/
theorem altLevelsQm (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : AltLevelsQm d κ c τ C E s t := by
  intro hU hmain hloc hdec k _ hk Λ Φ hΛ0 hΦ0 hΛ1 hlev v hsv hvt τ' Db hτ' hDb m hm
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, hcond, hrange, -⟩ := hmain'
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have hKd : KcalDecay κ := kcalDecay κ
  have hdl : DecayLoopPT d E s t := decayLoopWindow d κ c τ E s t hmain hKd hU.2.1 hloc hdec
  have hm' : (m = 1 ∨ m = 2 ∨ m = 3) ∨ (m = 4 ∨ m = 5) := by revert hm; revert m; decide
  intro τ0 hτ0 D0 hD0
  -- the parameters
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨cp, hcpdef⟩ : ∃ cp : ℝ, cp = cPrec c k := ⟨_, rfl⟩
  have hcp : 0 < cp := by rw [hcpdef]; unfold cPrec; positivity
  obtain ⟨den, hden⟩ : ∃ den : ℝ, den = cp + 2 * ((k : ℝ) - 2) := ⟨_, rfl⟩
  have hden0 : 0 < den := by rw [hden]; linarith
  obtain ⟨τg, hτgdef⟩ : ∃ τg : ℝ, τg = 2 * ((k : ℝ) - 1) * τ' / den := ⟨_, rfl⟩
  have hτg0 : 0 < τg := by rw [hτgdef]; apply div_pos _ hden0; nlinarith
  have hτg : (cp + 2 * ((k : ℝ) - 2)) * τg ≤ 2 * ((k : ℝ) - 1) * τ' := by
    rw [← hden, hτgdef]; field_simp; exact le_rfl
  obtain ⟨Dg, hDgdef⟩ : ∃ Dg : ℝ, Dg = Db + cp + cp * τg + ((k : ℝ) + 2) / c := ⟨_, rfl⟩
  have hcτ : 0 ≤ cp * τg := mul_nonneg hcp.le hτg0.le
  have hk2c : 0 ≤ ((k : ℝ) + 1) / c := by positivity
  have hDg0 : 0 < Dg := by rw [hDgdef]; positivity
  have hDg1 : Db + cp * τg ≤ Dg := by
    rw [hDgdef]; have : 0 ≤ ((k : ℝ) + 2) / c := by positivity
    linarith
  have hDg2 : Db + cp ≤ Dg := by
    rw [hDgdef]; have : 0 ≤ ((k : ℝ) + 2) / c := by positivity
    linarith
  have hDg3 : Db + ((k : ℝ) + 1) / c ≤ Dg := by
    rw [hDgdef]
    have : ((k : ℝ) + 1) / c ≤ ((k : ℝ) + 2) / c := by
      apply div_le_div_of_nonneg_right _ hc.le; linarith
    linarith
  -- the eventual facts
  have hgood := AltLevelsQ_goodSet hmain hU.1 hKd hU.2.1 hloc hdec hdl hk hΛ0 hΦ0 hΛ1 hlev
    (ε := τ0 / 4) (by positivity) hτg0 hDg0 hD0 hsv hvt
  have hqop := hsizeN.eventually (qopNorm c hc k hk τg Dg hτg0 hDg0)
  have hηt := NonAltEnd_ev_hη d hsize hκ hE hτ hrange
  have hnums := AltLevelsQ_ev_nums hsize k hτ0
  filter_upwards [hgood, hqop, hband, hηt, hnums] with n hg hq hb hηn hnm
  obtain ⟨hNt2, hΓ2, hcoef, hpoly⟩ := hnm
  intro p
  refine le_trans (measure_mono ?_) (hg p.1)
  intro ω hω
  by_contra hmem
  have hM : Sizes.seqHflow d n p.1 ω ∈ GoodSetN (d.L n) (d.W n) (E n) p.1 k
      (((d.size n : ℕ) : ℝ) ^ (τ0 / 4)) (Λ n) (Φ n) τg Dg := not_not.1 hmem
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hut : (p.1 : ℝ) ≤ t n := p.1.2.2.trans (hvt n)
  have hu1 : (p.1 : ℝ) < 1 := hut.trans_lt (ht1 n)
  have hEn : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  have hLn : 3 ≤ d.L n := d.three_le_L n
  have hWn : 1 ≤ d.W n := d.W_pos n
  have hNt1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ0 := by linarith
  have hΓ0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (τ0 / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbound : ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖ ≤
      ((d.size n : ℕ) : ℝ) ^ τ0 * altQLevel (d.L n) (d.W n) (E n) k τ' Db (Φ n) (p.1 : ℝ) := by
    rcases hm' with h123 | h45
    · refine AltLevelsQ_final123 (L := d.L n) (W := d.W n) hk hWn hΓ0 (hΦ0 n)
        (scaleM_pos (by omega) hWn hEn hu1) (etaT_pos hEn hu1) ?_ hcp.le hτg0.le
        hτg hDg1 hDg2 hNt2 hΓ2 hM p.2.1.1 m h123 p.2.2
      intro A hA
      have := hq (d.L n) (d.W n) hLn (Sizes.size_eq d n).symm hb (p.1 : ℝ) hu0 hu1 A hA
      rw [← hcpdef] at this
      exact this
    · exact AltLevelsQ_final45 (L := d.L n) (W := d.W n) hLn hWn hEn hu0 hu1 hk hc
        (NonAltEnd_size_eq d n) hb ((AltLevelsQ_etaT_inv_anti hEn hut (ht1 n)).trans hηn)
        hΓ0 (hΦ0 n) hτg0.le hcp.le hτg hDg3 hNt1 hcoef hpoly hM p.2.1.2 m h45 p.2.2
  exact absurd hω (not_lt.2 hbound)

end Pin

end RBM.Ind
