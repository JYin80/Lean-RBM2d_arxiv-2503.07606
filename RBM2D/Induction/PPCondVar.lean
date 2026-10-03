/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.PPVocab
import RBM2D.Induction.PPKernel
import RBM2D.Induction.NonAltGood
import RBM2D.Induction.BcalEDecay

/-!
# The `(+,+)` conditional-variance bound `ppCondVarN`

The result is the statement `PPCondVarN` (`RBM2D.Induction.PPVocab`, with the tail hypothesis
`Δ ≤ N^{-(40 + D' + 2τ')}`), proved verbatim:

`theorem ppCondVarN : PPCondVarN`.

Paper: arXiv:2503.07606, Section 5: `def:CALE`, `alu9_STime`.  The argument parallels the
one-dimensional formalization (the good set at `u₁` controls the loops at `u₂ = u₁ + Δ`, with an
explicit tail hypothesis).  The argument is: (1) at the time
`u₁` the pair form `𝓔⊗𝓔` is a `W²`-weighted sum over the two cuts `k ∈ {1, 2}` of the
`S^{(B)}`-window sum of a length-`6` loop; the window bound `norm_sum_SB_le_left` splits it
into the near window `(2R + 1)²` (`R = ℓ_{u₁} W^{τ'}`, `Ξ^{(𝓛)}_{u₁,6} ≤ ΓΦ₆`) and the far rest
(decay clause of `GoodSetPPN`, `W^{-D'}`); (2) `norm_eeN_shiftN_le` moves `𝓔⊗𝓔` from
`u₁` to `u₂` at the cost `12 N⁸ Δ` (`η_{u₂}⁻¹ ≤ N` from `1 ≤ M_{u₂}`), absorbed by `N^{-D'}` through
the tail hypothesis; (3) the row sums of the slot kernel give `(Σ_b |κ_b|)² ≤ CU⁴`.

Layout: 1. the loop clauses of `GoodSetPPN`; 2. `𝓔⊗𝓔` at the time `u₁`; 3. the form
`qvFormN ≤ CU⁴ B`; 4. the theorem `ppCondVarN`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open Matrix Filter RBM RBM.Gauss RBM.Path

/-! ## 1. The loop clauses of `GoodSetPPN` for a length-`6` loop -/

section Clauses

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- A well-formed loop of length `6` is `loopOf` of its entries. -/
private theorem PPCondVar_exists_loopOf {I : LoopIdx (Z2 L)} (hI : I.WF) (hl : I.a.length = 6) :
    ∃ (σ : Fin 6 → Bool) (a : Fin 6 → Z2 L), loopOf σ a = I := by
  obtain ⟨σ, a⟩ := I
  simp only [LoopIdx.WF] at hI
  simp only at hl
  refine ⟨fun i => σ[i.1]'(by rw [hI, hl]; exact i.2), fun i => a[i.1]'(by rw [hl]; exact i.2), ?_⟩
  simp only [loopOf, LoopIdx.mk.injEq]
  constructor
  · exact List.ext_getElem (by simp [hI, hl]) (fun i h1 h2 => by rw [List.getElem_ofFn])
  · exact List.ext_getElem (by simp [hl]) (fun i h1 h2 => by rw [List.getElem_ofFn])

/-- **The two loop clauses of `GoodSetPPN` at length `6`** (clause (G3) and the decay clause): for a
well-formed loop `I` of length `6`, `|𝓛_I| M_u⁵ ≤ ΓΦ₆`, and `|𝓛_I| ≤ W^{-D'}` as soon as two labels
of `I` are at distance `≥ ℓ_u W^{τ'}`. -/
private theorem PPCondVar_loop_good {E u Γ Φ₃ Φ₆ τ' D' : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M ∈ GoodSetPPN L W E u Γ Φ₃ Φ₆ τ' D') (hs : 0 ≤ scaleM L W E u)
    {I : LoopIdx (Z2 L)} (hI : I.WF) (hl : I.a.length = 6) :
    ‖LLf L W E u M I‖ * scaleM L W E u ^ 5 ≤ Γ * Φ₆ ∧
    ∀ x ∈ I.a, ∀ y ∈ I.a, ellT L u * (W : ℝ) ^ τ' ≤ (zdist2 L (x - y) : ℝ) →
      ‖LLf L W E u M I‖ ≤ (W : ℝ) ^ (-D') := by
  obtain ⟨σ, a, rfl⟩ := PPCondVar_exists_loopOf hI hl
  obtain ⟨-, -, -, hxi6, hdec⟩ := hM
  have hLL : ‖LLf L W E u M (loopOf σ a)‖ = loopAbs L W E u M σ a := rfl
  refine ⟨?_, ?_⟩
  · rw [hLL]
    have h1 : loopAbs L W E u M σ a ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin 6 → Bool) × (Fin 6 → Z2 L) => loopAbs L W E u M p.1 p.2) :=
      Finset.le_sup' (fun p : (Fin 6 → Bool) × (Fin 6 → Z2 L) => loopAbs L W E u M p.1 p.2)
        (Finset.mem_univ (σ, a))
    calc loopAbs L W E u M σ a * scaleM L W E u ^ 5
        ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun p : (Fin 6 → Bool) × (Fin 6 → Z2 L) => loopAbs L W E u M p.1 p.2) *
          scaleM L W E u ^ (6 - 1) := mul_le_mul_of_nonneg_right h1 (pow_nonneg hs _)
      _ = xiL L W E u M 6 := rfl
      _ ≤ Γ * Φ₆ := hxi6
  · intro x hx y hy hfar
    rw [hLL]
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    have hmax : ((zdist2 L (a i - a j) : ℕ) : ℝ) ≤ (KLoop.maxDist L a : ℝ) := by
      exact_mod_cast Finset.le_sup (f := fun q : Fin 6 × Fin 6 => zdist2 L (a q.1 - a q.2))
        (Finset.mem_univ (i, j))
    have h := hdec 6 (by norm_num) le_rfl σ a (hfar.trans hmax)
    have hlk : 0 ≤ lkGen L W E u M σ a := norm_nonneg _
    linarith

end Clauses

/-! ## 2. `𝓔⊗𝓔` at the time `u₁` on `GoodSetPPN` -/

section EE

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **`𝓔⊗𝓔` at the time of the good set** (`n = 2`): for `M ∈ GoodSetPPN(u)`,
`|(𝓔⊗𝓔)_{σ,a,a'}| ≤ 2 W² ((2R + 1)² ΓΦ₆ M_u^{-5} + L² W^{-D'})`, `R = ℓ_u W^{τ'}`. -/
private theorem PPCondVar_eeN_le (hL : 3 ≤ L) {E u Γ Φ₃ Φ₆ τ' D' : ℝ}
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M ∈ GoodSetPPN L W E u Γ Φ₃ Φ₆ τ' D')
    (hs : 0 < scaleM L W E u) (hR : 0 ≤ ellT L u * (W : ℝ) ^ τ') (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Z2 L) :
    ‖eeN L W E u M σ a a'‖ ≤ (W : ℝ) ^ 2 * (2 * ((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 *
      (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹) + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D'))) := by
  have hW2 : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  have hδ : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold eeN
  rw [norm_mul, hW2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k ∈ Finset.Icc 1 2, ‖∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
      LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 * (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹) +
        (L : ℝ) ^ 2 * (W : ℝ) ^ (-D') := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hwf : ∀ b b' : Z2 L,
        (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').WF := fun b b' =>
      eeLoop_WF (L := L) (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk.1 (by simpa using hk.2)
        (by simp) (by simp) b b'
    have hlen : ∀ b b' : Z2 L,
        (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a.length = 6 :=
      fun b b' => by
        have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k)
          (by simp; omega) (by simp) b b'
        simpa [LoopIdx.length] using this
    have hmemb : ∀ b b' : Z2 L,
        b ∈ (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a := fun b b' => by
      simp [eeLoop]
    have hmemc : ∀ b b' : Z2 L,
        a 0 ∈ (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a := fun b b' =>
      mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨0, rfl⟩)
    refine norm_sum_SB_le_left L hL hR hδ (a 0)
      (fun b b' => LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))
      (fun b b' => ?_) (fun b b' hfar => ?_)
    · have h := (PPCondVar_loop_good hM hs.le (hwf b b') (hlen b b')).1
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hs 5)]
      exact h
    · exact (PPCondVar_loop_good hM hs.le (hwf b b') (hlen b b')).2 b (hmemb b b') (a 0)
        (hmemc b b') hfar
  calc ∑ k ∈ Finset.Icc 1 2, ‖∑ b : Z2 L, ∑ b' : Z2 L, SB L b b' *
        LLf L W E u M (eeLoop L (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖
      ≤ ∑ k ∈ Finset.Icc 1 2, ((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 *
          (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹) + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D')) :=
        Finset.sum_le_sum hk
    _ = 2 * ((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 * (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹) +
          (L : ℝ) ^ 2 * (W : ℝ) ^ (-D')) := by
        simp [Finset.sum_const, Nat.card_Icc]
        ring

end EE

/-! ## 3. The form `qvFormN` from a uniform bound on `𝓔⊗𝓔` -/

section Form

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Minkowski bound of a bilinear form: `Re Σ_{b,b'} κ_b conj(κ_{b'}) e_{bb'} ≤ S² B` when
`Σ_b |κ_b| ≤ S` and `|e_{bb'}| ≤ B`. -/
private theorem PPCondVar_form_le {ι : Type*} [Fintype ι] {κ : ι → ℂ} {S B : ℝ}
    (hS : ∑ b, ‖κ b‖ ≤ S) (hB : 0 ≤ B) (ee : ι → ι → ℂ) (hee : ∀ b b', ‖ee b b'‖ ≤ B) :
    (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * ee b b').re ≤ S ^ 2 * B := by
  have hS0 : 0 ≤ ∑ b, ‖κ b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * ee b b').re
      ≤ ‖∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * ee b b'‖ := Complex.re_le_norm _
    _ ≤ ∑ b, ∑ b', ‖κ b * (starRingEnd ℂ) (κ b') * ee b b'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
    _ ≤ ∑ b, ∑ b', ‖κ b‖ * ‖κ b'‖ * B :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => by
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hee b b') (by positivity)
    _ = (∑ b, ‖κ b‖) * (∑ b, ‖κ b‖) * B := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
    _ ≤ S * S * B := by
        have hS0' : 0 ≤ S := hS0.trans hS
        gcongr
    _ = S ^ 2 * B := by ring

/-- **`qvFormN` at `(+,+)`**: if the row sums of the slot kernel are `≤ CU` and
`|(𝓔⊗𝓔)_{b,b'}| ≤ B` uniformly, then `qvFormN ≤ CU⁴ B`. -/
private theorem PPCondVar_qv_le {E v w CU B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ x : Z2 L, ∑ y : Z2 L,
      ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w x y‖ ≤ CU)
    (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hee : ∀ b b' : Fin 2 → Z2 L, ‖eeN L W E v M sigPPN b b'‖ ≤ B) (a : Fin 2 → Z2 L) :
    qvFormN L W E v w sigPPN M a ≤ CU ^ 4 * B := by
  have hCU : 0 ≤ CU := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hrow 0)
  have hsig : ∀ i : Fin 2, KLoop.mSig E (sigPPN i) * KLoop.mSig E (sigPPN (i + 1)) =
      KLoop.mSig E true * KLoop.mSig E true := fun i => by
    rw [sigPPN_apply i, sigPPN_apply (i + 1)]
  unfold qvFormN
  simp only [hsig]
  have hS : ∑ b : Fin 2 → Z2 L, ‖∏ i : Fin 2,
      ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) (b i)‖ ≤ CU ^ 2 := by
    simp only [norm_prod]
    calc ∑ b : Fin 2 → Z2 L, ∏ i : Fin 2,
          ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) (b i)‖
        = ∏ i : Fin 2, ∑ y : Z2 L,
          ‖ukerMat L (KLoop.mSig E true * KLoop.mSig E true) v w (a i) y‖ := by
          rw [Fintype.prod_sum]
      _ ≤ ∏ _i : Fin 2, CU :=
          Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            fun i _ => hrow (a i)
      _ = CU ^ 2 := by simp [Finset.prod_const, Finset.card_univ]
  have := PPCondVar_form_le hS hB (eeN L W E v M sigPPN) hee
  calc _ ≤ (CU ^ 2) ^ 2 * B := this
    _ = CU ^ 4 * B := by ring

end Form

/-! ## 4. The theorem `ppCondVarN` -/

section Main

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The shift error of `𝓔⊗𝓔` at `n = 2`: `eeShiftErr ≤ 12 N⁸ Δ` for `η_{u'}⁻¹ ≤ N`,
`N = W² L²` (six edges: `W² · 2 · L² · 6 η⁻⁷ (W⁻²)⁵ Δ`). -/
private theorem PPCondVar_shiftErr_le {E u u' Δ N : ℝ} (hΔ : u' - u = Δ) (hΔ0 : 0 ≤ Δ)
    (hη : 0 < etaT E u') (hiη : (etaT E u')⁻¹ ≤ N) (hNWL : N = (W : ℝ) ^ 2 * (L : ℝ) ^ 2)
    (hW1r : (1 : ℝ) ≤ W) : eeShiftErr L W E 2 u u' ≤ 12 * (N ^ 8 * Δ) := by
  unfold eeShiftErr loopShiftErr
  rw [hΔ]
  norm_num
  have h1 : (((W : ℝ) ^ 2) ^ 5)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ hW1r))
  have h2 : ((etaT E u') ^ 7)⁻¹ ≤ N ^ 7 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hη.le) hiη 7
  have h3 : 0 ≤ ((etaT E u') ^ 7)⁻¹ := by positivity
  have h4 : 0 ≤ (((W : ℝ) ^ 2) ^ 5)⁻¹ := by positivity
  have hN0 : 0 ≤ N := by rw [hNWL]; positivity
  calc (W : ℝ) ^ 2 * (2 * ((L : ℝ) ^ 2 * (6 * (((etaT E u') ^ 7)⁻¹ * (((W : ℝ) ^ 2) ^ 5)⁻¹ * Δ))))
      = 12 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (((etaT E u') ^ 7)⁻¹ * (((W : ℝ) ^ 2) ^ 5)⁻¹ * Δ) := by
        ring
    _ ≤ 12 * N * (N ^ 7 * 1 * Δ) := by
        rw [← hNWL]
        gcongr
    _ = 12 * (N ^ 8 * Δ) := by ring

/-- The near window: `2 W² (2R + 1)² ΓΦ₆ M_u⁻⁵ ≤ 18 W^{2τ'} ΓΦ₆ M_u⁻⁴ η_u⁻¹`
(`R = ℓ_u W^{τ'} ≥ 1`, `W² ℓ_u² = M_u / η_u`). -/
private theorem PPCondVar_near_le {E u τ' Γ Φ₆ : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hτ' : 0 ≤ τ') (hΓΦ : 0 ≤ Γ * Φ₆) :
    (W : ℝ) ^ 2 * (2 * ((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 *
        (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹))) ≤
      18 * ((W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E u)⁻¹ ^ 4 * (etaT E u)⁻¹) := by
  have hL1 : 1 ≤ L := NeZero.pos L
  have hW1 : 1 ≤ W := NeZero.pos W
  have hs := scaleM_pos (W := W) hL1 hW1 hE hu1
  have hη := etaT_pos hE hu1
  have hℓ := one_le_ellT hL1 hu0 hu1
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hp : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hWr hτ'
  have hR : 1 ≤ ellT L u * (W : ℝ) ^ τ' := one_le_mul_of_one_le_of_one_le hℓ hp
  have hp2 : ((W : ℝ) ^ τ') ^ 2 = (W : ℝ) ^ (2 * τ') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  have h9 : (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 ≤
      9 * (ellT L u ^ 2 * (W : ℝ) ^ (2 * τ')) := by
    have h : (2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 ≤ 9 * (ellT L u * (W : ℝ) ^ τ') ^ 2 := by
      nlinarith
    rwa [mul_pow, hp2] at h
  have hW2ℓ : (W : ℝ) ^ 2 * ellT L u ^ 2 = scaleM L W E u * (etaT E u)⁻¹ := by
    unfold scaleM
    field_simp
  have hG : 0 ≤ Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹ :=
    mul_nonneg hΓΦ (inv_nonneg.2 (pow_nonneg hs.le 5))
  calc (W : ℝ) ^ 2 * (2 * ((2 * (ellT L u * (W : ℝ) ^ τ') + 1) ^ 2 *
          (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹)))
      ≤ (W : ℝ) ^ 2 * (2 * (9 * (ellT L u ^ 2 * (W : ℝ) ^ (2 * τ')) *
          (Γ * Φ₆ * (scaleM L W E u ^ 5)⁻¹))) := by gcongr
    _ = 18 * ((W : ℝ) ^ (2 * τ') * ((W : ℝ) ^ 2 * ellT L u ^ 2) * (Γ * Φ₆) *
          (scaleM L W E u ^ 5)⁻¹) := by ring
    _ = 18 * ((W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E u)⁻¹ ^ 4 * (etaT E u)⁻¹) := by
        rw [hW2ℓ]
        field_simp

/-- **`ppCondVarN`** (the statement `PPCondVarN`): the conditional-variance form
`Δ · 2 · qvFormN` of the propagated first-chaos
increment at `u₂ = u₁ + Δ` is `≤ Δ CU⁴ ee_bd` on `GoodSetPPN` at `u₁`.  The statement carries the
tail hypothesis `Δ ≤ N^{-(40 + D' + 2τ')}`, which the paper does not need. -/
theorem ppCondVarN : PPCondVarN := by
  intro L W _ _ hL E u₁ u₂ w Δ hE hu₁0 hu₁₂ hu₂w hw1 hu₂ hΔ40 hM₂ Γ Φ₃ Φ₆ τ' D' CU hΓ hΦ₃ hΦ₆
    hτ' hD' hΔtail hrow M hM hMh a
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hu2 : u₂ < 1 := hu₂w.trans_lt hw1
  have hu1 : u₁ < 1 := hu₁₂.trans_lt hu2
  have hΔ0 : 0 ≤ Δ := by linarith
  have hη2 := etaT_pos hE hu2
  have hη1 := etaT_pos hE hu1
  have hs2 := scaleM_pos (W := W) hL1 hW1 hE hu2
  have hs1 := scaleM_pos (W := W) hL1 hW1 hE hu1
  have hsle : scaleM L W E u₂ ≤ scaleM L W E u₁ := (scaleM_anti_ratio hL1 hE hu₁₂ hu2).1
  have hηle : etaT E u₂ ≤ etaT E u₁ := by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (spectralM_im_pos hE).le
  -- `N = W² L²`, `η_{u₂}⁻¹ ≤ N` from `1 ≤ M_{u₂}`
  have hNWL : nPPN L W = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    unfold nPPN
    push_cast
    ring
  have hN1 : 1 ≤ nPPN L W := by
    rw [hNWL]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hWr) (one_le_pow₀ hLr)
  have hNpos : 0 < nPPN L W := lt_of_lt_of_le one_pos hN1
  have hWN : (W : ℝ) ≤ nPPN L W := by
    rw [hNWL]
    exact (le_self_pow₀ hWr two_ne_zero).trans
      (le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hLr))
  have hiη : (etaT E u₂)⁻¹ ≤ nPPN L W := by
    have hℓ := ellT_pos_le hL1 hu2
    have h1 : 1 ≤ (W : ℝ) ^ 2 * ellT L u₂ ^ 2 * etaT E u₂ := hM₂
    calc (etaT E u₂)⁻¹ = (etaT E u₂)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (etaT E u₂)⁻¹ * ((W : ℝ) ^ 2 * ellT L u₂ ^ 2 * etaT E u₂) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hη2.le)
      _ = (W : ℝ) ^ 2 * ellT L u₂ ^ 2 := by field_simp
      _ ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ.1.le hℓ.2 2) (sq_nonneg _)
      _ = nPPN L W := hNWL.symm
  -- the shift `u₁ → u₂` of `𝓔⊗𝓔` and its absorption by the tail hypothesis
  have hshift : ∀ b b' : Fin 2 → Z2 L,
      ‖eeN L W E u₂ M sigPPN b b' - eeN L W E u₁ M sigPPN b b'‖ ≤ 12 * (nPPN L W ^ 8 * Δ) :=
    fun b b' => (norm_eeN_shiftN_le hL hE hMh hu₁₂ hu2 sigPPN b b').trans
      (PPCondVar_shiftErr_le (by linarith) hΔ0 hη2 hiη hNWL hWr)
  have hδ0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNΔ : nPPN L W ^ 8 * Δ ≤ (W : ℝ) ^ (-D') := by
    have h8 : nPPN L W ^ 8 = nPPN L W ^ (8 : ℝ) := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : nPPN L W ^ 8 * Δ ≤ nPPN L W ^ (8 : ℝ) * nPPN L W ^ (-(40 + D' + 2 * τ')) := by
      rw [h8]
      exact mul_le_mul_of_nonneg_left hΔtail (Real.rpow_nonneg hNpos.le _)
    have h2 : nPPN L W ^ (8 : ℝ) * nPPN L W ^ (-(40 + D' + 2 * τ')) ≤ nPPN L W ^ (-D') := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h3 : nPPN L W ^ (-D') ≤ (W : ℝ) ^ (-D') :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hWN (by linarith)
    linarith
  -- the pair form at `u₂`
  have hΓΦ : 0 ≤ Γ * Φ₆ := mul_nonneg (by linarith) hΦ₆
  have hWτ0 : 0 ≤ (W : ℝ) ^ (2 * τ') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set X₂ : ℝ := (W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E u₂)⁻¹ ^ 4 * (etaT E u₂)⁻¹ with hX₂
  have hX₂0 : 0 ≤ X₂ := by
    have := inv_nonneg.2 hs2.le
    have := inv_nonneg.2 hη2.le
    positivity
  have hinv : (scaleM L W E u₁)⁻¹ ^ 4 * (etaT E u₁)⁻¹ ≤
      (scaleM L W E u₂)⁻¹ ^ 4 * (etaT E u₂)⁻¹ :=
    mul_le_mul (pow_le_pow_left₀ (inv_nonneg.2 hs1.le) (inv_anti₀ hs2 hsle) 4)
      (inv_anti₀ hη2 hηle) (inv_nonneg.2 hη1.le) (pow_nonneg (inv_nonneg.2 hs2.le) 4)
  have hX : (W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E u₁)⁻¹ ^ 4 * (etaT E u₁)⁻¹ ≤ X₂ := by
    calc (W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * (scaleM L W E u₁)⁻¹ ^ 4 * (etaT E u₁)⁻¹
        = (W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * ((scaleM L W E u₁)⁻¹ ^ 4 * (etaT E u₁)⁻¹) := by ring
      _ ≤ (W : ℝ) ^ (2 * τ') * (Γ * Φ₆) * ((scaleM L W E u₂)⁻¹ ^ 4 * (etaT E u₂)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg hWτ0 hΓΦ)
      _ = X₂ := by rw [hX₂]; ring
  have hℓ1 : 1 ≤ ellT L u₁ := one_le_ellT hL1 hu₁0 hu1
  have hR0 : 0 ≤ ellT L u₁ * (W : ℝ) ^ τ' :=
    (one_le_mul_of_one_le_of_one_le hℓ1 (Real.one_le_rpow hWr hτ'.le)).trans' zero_le_one
  have hee : ∀ b b' : Fin 2 → Z2 L,
      ‖eeN L W E u₂ M sigPPN b b'‖ ≤ 18 * X₂ + (2 * nPPN L W + 12) * (W : ℝ) ^ (-D') := by
    intro b b'
    have h1 := PPCondVar_eeN_le hL hM hs1 hR0 sigPPN b b'
    have h2 := PPCondVar_near_le (L := L) (W := W) hE hu₁0 hu1 hτ'.le hΓΦ
    have h3 := hshift b b'
    have h4 := norm_sub_norm_le (eeN L W E u₂ M sigPPN b b') (eeN L W E u₁ M sigPPN b b')
    have e1 : (W : ℝ) ^ 2 * (2 * ((2 * (ellT L u₁ * (W : ℝ) ^ τ') + 1) ^ 2 *
        (Γ * Φ₆ * (scaleM L W E u₁ ^ 5)⁻¹) + (L : ℝ) ^ 2 * (W : ℝ) ^ (-D'))) =
        (W : ℝ) ^ 2 * (2 * ((2 * (ellT L u₁ * (W : ℝ) ^ τ') + 1) ^ 2 *
          (Γ * Φ₆ * (scaleM L W E u₁ ^ 5)⁻¹))) + 2 * nPPN L W * (W : ℝ) ^ (-D') := by
      rw [hNWL]
      ring
    rw [e1] at h1
    linarith
  have hBee0 : 0 ≤ 18 * X₂ + (2 * nPPN L W + 12) * (W : ℝ) ^ (-D') := by positivity
  have hqv := PPCondVar_qv_le (E := E) (v := u₂) (w := w) hBee0 hrow M hee a
  refine mul_le_mul_of_nonneg_left ?_ hΔ0
  have hN2 : 4 * nPPN L W + 24 ≤ 1000 * nPPN L W ^ 2 := by nlinarith
  have hkey := mul_le_mul_of_nonneg_right hN2 hδ0
  have hee2 : 2 * (18 * X₂ + (2 * nPPN L W + 12) * (W : ℝ) ^ (-D')) ≤
      eeBdPPN L W E u₂ Γ Φ₆ τ' D' := by
    unfold eeBdPPN
    nlinarith [hkey, hX₂0]
  calc 2 * qvFormN L W E u₂ w sigPPN M a
      ≤ 2 * (CU ^ 4 * (18 * X₂ + (2 * nPPN L W + 12) * (W : ℝ) ^ (-D'))) := by linarith
    _ = CU ^ 4 * (2 * (18 * X₂ + (2 * nPPN L W + 12) * (W : ℝ) ^ (-D'))) := by ring
    _ ≤ CU ^ 4 * eeBdPPN L W E u₂ Γ Φ₆ τ' D' :=
        mul_le_mul_of_nonneg_left hee2 (by positivity)

end Main

end RBM.Ind
