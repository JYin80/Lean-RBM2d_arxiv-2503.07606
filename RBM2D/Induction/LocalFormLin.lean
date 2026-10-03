/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.LocalFormCalc

/-!
# `AltLocalFormAt` at `m = 0` and `m = 5`

Paper: arXiv:2503.07606, Section 5 (`int_K-L+Q2`, `Def:QtPt`) and Section 7 (`a-local-form`).

Results (namespace `RBM.Ind`, `variable (d : Sizes)`):
1. `altLocalFormAt_zero`: `𝒬_u B₀ = 𝒬_u(𝓛-𝒦)`, the kernel `𝔎_{a,c} = 1(c = a)`.
2. `altLocalFormAt_five`: `𝒬_u B₅ = 𝒬_u(𝒫(𝓛-𝒦) ϑ̇_u)`, the kernel `pvdKer` (`sum_pvdKer`).

Both are linear in `X = 𝓛-𝒦` with a deterministic kernel, so both are the same assembly as
`altLocalFormAt_four` (in `LocalFormCalc`): the private `localFormLin_core` proves
`AltLocalFormAt` for any kernel family
`𝔎` with `K1` (`|𝔎| ≤ 2k(1-u)⁻¹`), `K2'`, `K3'` (`|𝔎| ≤ P_δ dec(ρ/2)` off the window) and the
identity `altQB m = 𝒬_u(𝔎 X)`; the two results supply the kernel.  Exponents as for `m = 4`:
`C' = 3k+3`, kernel bound `N²`, `δ = P_δ dec(ρ/2)`, `D_tr = D₀ + (k+3)/c`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

section LinDet

open LocalFormCalc

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} [NeZero k]

/-- The coefficient bound of the assembled form for a kernel `|𝔎| ≤ 2kN`: `≤ N^{3k+3}`
(as `LocalFormCalc.four_coef`, with the kernel a hypothesis). -/
private theorem localFormLin_coef (hL : 3 ≤ L) (hW : 1 ≤ W) {E u Nr : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (ρ : ℝ) (𝔎 : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (h𝔎 : ∀ a c, ‖𝔎 a c‖ ≤ 2 * (k : ℝ) * Nr)
    (σ : Fin k → Bool) (hN1 : 1 ≤ Nr) (hLN : (L : ℝ) ^ 2 ≤ Nr)
    (hη : (etaT E u)⁻¹ ≤ Nr) (hηpos : 0 < etaT E u)
    (hKc : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr * (etaT E u)⁻¹ ^ k)
    (hc1 : 8 * (k : ℝ) ≤ Nr) (a : Fin k → Z2 L) (j : Fin (k + 1)) (q : Fin j → Mono L W) :
    ‖(asmF u ρ 𝔎 (lkF σ E u : LocalForm L W k k)).coef a j q‖ ≤ Nr ^ (3 * k + 3) := by
  have hN0 : 0 < Nr := by linarith
  have hpow : (etaT E u)⁻¹ ^ k ≤ Nr ^ k := pow_le_pow_left₀ (inv_nonneg.2 hηpos.le) hη k
  have hKb : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr ^ (k + 1) := fun b =>
    (hKc b).trans (by
      calc Nr * (etaT E u)⁻¹ ^ k ≤ Nr * Nr ^ k := mul_le_mul_of_nonneg_left hpow hN0.le
        _ = Nr ^ (k + 1) := by ring)
  have hN1k : (1 : ℝ) ≤ Nr ^ (k + 1) := one_le_pow₀ hN1
  have hlk := coef_lkF_le hW σ E u (B := Nr ^ (k + 1)) (by positivity) hKb
  have hBK : (0 : ℝ) ≤ 2 * (k : ℝ) * Nr := by positivity
  have h := coef_asmF_le hL hu0 hu1 ρ 𝔎 (lkF σ E u : LocalForm L W k k)
    (B := 1 + Nr ^ (k + 1)) (B_K := 2 * (k : ℝ) * Nr) (by positivity) hBK hlk h𝔎 a j q
  refine h.trans ?_
  have hc := card_le_pow (L := L) (k := k) hLN
  have h2 := one_add_card_le (L := L) (k := k) hN1 hLN
  have h3 : 1 + Nr ^ (k + 1) ≤ 2 * Nr ^ (k + 1) := by linarith
  calc (1 + ((L : ℝ) ^ 2) ^ k) * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (1 + Nr ^ (k + 1)))
      ≤ (2 * Nr ^ k) * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) := by
        gcongr
    _ = (8 * (k : ℝ)) * Nr ^ (3 * k + 2) := by ring
    _ ≤ Nr * Nr ^ (3 * k + 2) := mul_le_mul_of_nonneg_right hc1 (by positivity)
    _ = Nr ^ (3 * k + 3) := by ring

/-- Locality of the assembled form for any kernel: `Loc0 (4ρ)`. -/
private theorem localFormLin_loc (u ρ : ℝ) (𝔎 : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (σ : Fin k → Bool) (E : ℝ) :
    Loc0 (4 * ρ) (asmF u ρ 𝔎 (lkF σ E u : LocalForm L W k k)) := by
  have h := loc0_asmF u ρ 𝔎 (lkF σ E u : LocalForm L W k k)
    (loc0_trunc_lkF (L := L) (W := W) σ E u ρ)
  have e : 2 * ρ + 2 * ρ = 4 * ρ := by ring
  rwa [e] at h

/-- Far labels of the assembled form are deterministically tiny for any kernel `|𝔎| ≤ 2kN`
(as `LocalFormCalc.four_far`, with the kernel a hypothesis). -/
private theorem localFormLin_far (hL : 3 ≤ L) (hW : 1 ≤ W) {E u Nr ρ Tgt : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hρ : 0 < ρ) (𝔎 : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (h𝔎 : ∀ a c, ‖𝔎 a c‖ ≤ 2 * (k : ℝ) * Nr) (σ : Fin k → Bool) (hN1 : 1 ≤ Nr)
    (hLN : (L : ℝ) ^ 2 ≤ Nr) (hNLW : (((L * W) ^ 2 : ℕ) : ℝ) ≤ Nr) (hη : (etaT E u)⁻¹ ≤ Nr)
    (hKc : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr * (etaT E u)⁻¹ ^ k)
    (hc3 : 4 * (k : ℝ) * C5 ≤ Nr) (htail : Nr ^ (3 * k + 6) * dec L u (ρ / 2) ≤ Tgt)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (b : Fin k → Z2 L)
    (hb : ρ ≤ (KLoop.maxDist L b : ℝ)) :
    ‖(asmF u ρ 𝔎 (lkF σ E u : LocalForm L W k k)).eval E u M b‖ ≤ Tgt := by
  have hN0 : 0 < Nr := by linarith
  have hηpos : 0 < etaT E u := etaT_pos hE hu1
  have hA : ∀ c, ‖lkTensor L W E u M σ c‖ ≤ 2 * Nr ^ (k + 1) := fun c =>
    norm_lkTensor_le hW hE hu1 hM σ c hη hNLW hN1 (hKc c)
  have hBK : (0 : ℝ) ≤ 2 * (k : ℝ) * Nr := by positivity
  have h := norm_eval_asmF_le_far hL hu0 hu1 ρ 𝔎 (lkF σ E u : LocalForm L W k k) E u M
    (lkTensor L W E u M σ) (fun c => eval_lkF σ E u M c) (B_K := 2 * (k : ℝ) * Nr)
    (B_X := 2 * Nr ^ (k + 1)) hBK (by positivity) h𝔎 hA b hb
  refine h.trans ?_
  obtain ⟨j₀, hj₀S, hj⟩ := exists_far hρ hb
  have hj0 : j₀ ≠ 0 := (Finset.mem_erase.mp hj₀S).1
  have hϑ := norm_vartheta_le_decay hL hu0 hu1 b hj0 (r := ρ / 2) hj
  have hcL := cL_le hL hu0 hu1 hLN
  have hε := (dec_pos L u (ρ / 2)).le
  have hC0 := cL_nonneg L u
  have hϑ2 : ‖vartheta L u b‖ ≤ C5 * Nr * dec L u (ρ / 2) :=
    hϑ.trans (mul_le_mul_of_nonneg_right hcL hε)
  have hc := card_le_pow (L := L) (k := k) hLN
  have hpref : ((L : ℝ) ^ 2) ^ k * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) ≤
      Nr ^ k * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) := by gcongr
  have hC5 := C5_pos
  calc (((L : ℝ) ^ 2) ^ k * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1)))) *
        ‖vartheta L u b‖
      ≤ (Nr ^ k * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1)))) * (C5 * Nr * dec L u (ρ / 2)) :=
        mul_le_mul hpref hϑ2 (norm_nonneg _) (by positivity)
    _ = (4 * (k : ℝ) * C5) * Nr ^ (3 * k + 3) * dec L u (ρ / 2) := by ring
    _ ≤ Nr * Nr ^ (3 * k + 3) * dec L u (ρ / 2) := by
        gcongr
    _ = Nr ^ (3 * k + 4) * dec L u (ρ / 2) := by ring
    _ ≤ Nr ^ (3 * k + 6) * dec L u (ρ / 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by omega)) hε
    _ ≤ Tgt := htail

end LinDet

section LinCore

variable (d : Sizes)

/-- **The common assembly for a kernel that is linear in `X = 𝓛 - 𝒦`.**  If `𝒬_u B_m = 𝒬_u(𝔎 X)`
for a deterministic kernel `𝔎` with `K1` (`|𝔎| ≤ 2k(1-u)⁻¹`) and `K2'`, `K3'` (`|𝔎| ≤ P_δ dec(ρ/2)`
off the window), then `𝒬_u B_m` has a local form up to `O_≺(W^{-D₀})` (the body of `AltLocalFormAt`
after the introductions).  Proof: that of `altLocalFormAt_four`. -/
private theorem localFormLin_core {κ c τ : ℝ} {E s t : ℕ → ℝ} (m : Fin 6)
    (hmain : MainIndHyp d κ c τ E s t) (hdl : DecayLoopPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {τ₀ D₀ : ℝ} (hτ₀ : 0 < τ₀) (hD₀ : 0 < D₀)
    (𝔎 : ∀ (L : ℕ) [NeZero L], ℝ → (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (hid : ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
      (σ : Fin k → Bool) (a : Fin k → Z2 L),
      altQB L W E u M σ m a = Qop L u (fun a' => ∑ c, 𝔎 L u a' c * lkTensor L W E u M σ c) a)
    (hK1 : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ a c,
      ‖𝔎 L u a c‖ ≤ 2 * (k : ℝ) * (1 - u)⁻¹)
    (hK2 : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ ρ : ℝ, 0 < ρ →
      ∀ a c, ρ ≤ (zdist2 L (c 0 - a 0) : ℝ) → (KLoop.maxDist L c : ℝ) < ρ →
        ‖𝔎 L u a c‖ ≤ LocalFormCalc.pdelta L k u * LocalFormCalc.dec L u (ρ / 2))
    (hK3 : ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ ρ : ℝ, 0 < ρ →
      ∀ a c, ρ ≤ (KLoop.maxDist L a : ℝ) → (KLoop.maxDist L c : ℝ) < ρ →
        ‖𝔎 L u a c‖ ≤ LocalFormCalc.pdelta L k u * LocalFormCalc.dec L u (ρ / 2)) :
    ∃ (K : ℕ) (C' : ℝ), 0 ≤ C' ∧
      ∀ (u : ℕ → ℝ) (σ : ℕ → Fin k → Bool), (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      ∃ F : ∀ n, LocalForm (d.L n) (d.W n) k K,
        (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') ∧
        (∀ n, (F n).Local τ₀ (u n)) ∧
        (∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)) ∧
        LabelDecayPT d E u F τ₀ D₀ ∧
        PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
          (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m
              p.2 - (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
          (fun n _ _ => (d.W n : ℝ) ^ (-D₀)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  refine ⟨k, ((3 * k + 3 : ℕ) : ℝ), by positivity, fun u σ hu hut => ?_⟩
  -- the constants
  set Dtr : ℝ := D₀ + ((k + 2 + 1 : ℕ) : ℝ) / c with hDtr
  have hkc : 0 < ((k + 2 + 1 : ℕ) : ℝ) / c := by positivity
  have hDtr0 : 0 < Dtr := by rw [hDtr]; linarith
  have hl1 := LocalFormCalc.lkTruncErr d hmain hdl (k := k) (by omega) hτ₀ hDtr0 u σ hu hut
  -- eventual facts
  obtain ⟨μ, hμ, hμb⟩ := LocalFormCalc.im_bounds hE hκ
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have e1 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hsize).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have e2 : ∀ᶠ n : ℕ in atTop, 1 ≤ ((d.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 1
  have e3 : ∀ᶠ n : ℕ in atTop, 8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
      8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
      4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ) := by
    filter_upwards [hsize.eventually_ge_atTop (8 * (k : ℝ)),
      hsize.eventually_ge_atTop (8 * LocalFormCalc.Qc k),
      hsize.eventually_ge_atTop (4 * (k : ℝ) * LocalFormCalc.C5)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have e4 : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (((3 * k + 7 : ℕ) : ℝ)) *
      Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) ≤ (d.W n : ℝ) ^ (-D₀) :=
    LocalFormCalc.tail_eventually d hc (Nat.cast_nonneg _) (by norm_num) hτ₀ hband hsize
  have e5 : ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = N →
      ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u' v : ℝ, 0 ≤ u' → u' ≤ v → v < 1 →
        ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
          ‖KLoop.Kcal L W E' u' J‖ ≤ (N : ℝ) ^ (1 : ℝ) * ((RBM.Path.etaT E' v)⁻¹) ^ k :=
    exists_norm_Kcal_le_win κ hκ k 1 one_pos
  have e6 := hsizeN.eventually e5
  -- the bundle of eventual facts
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ ((d.size n : ℕ) : ℝ) ∧
      ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n ∧ 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ ∧
      (8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
        4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ)) ∧
      ((d.size n : ℕ) : ℝ) ^ (((3 * k + 7 : ℕ) : ℝ)) * Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) ≤
        (d.W n : ℝ) ^ (-D₀) ∧
      (∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = d.size n →
        ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u' v : ℝ, 0 ≤ u' → u' ≤ v → v < 1 →
          ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
            ‖KLoop.Kcal L W E' u' J‖ ≤ ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((RBM.Path.etaT E' v)⁻¹) ^ k) := by
    filter_upwards [e2, hrange, e1, e3, e4, e6] with n h2 h3 h1 h4 h5 h6
    exact ⟨h2, h3, h1, h4, h5, h6⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  -- the radius and the assembled form
  set ρ : ℕ → ℝ := fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8 with hρdef
  set Fg : ∀ n, LocalForm (d.L n) (d.W n) k k := fun n =>
    LocalFormCalc.asmF (u n) (ρ n) (𝔎 (d.L n) (u n))
      (LocalFormCalc.lkF (σ n) (E n) (u n)) with hFg
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs0 n).trans (hu n)
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hℓ : ∀ n, 0 < ellT (d.L n) (u n) := fun n =>
    (ellT_pos_le (by have := d.three_le_L n; omega) (hu1 n)).1
  have hWpos : ∀ n, 0 < (d.W n : ℝ) := fun n => by exact_mod_cast d.W_pos n
  have hρpos : ∀ n, 0 < ρ n := fun n => by
    simp only [hρdef]
    have := hℓ n
    have := Real.rpow_pos_of_pos (hWpos n) τ₀
    positivity
  have hηpos : ∀ n, 0 < etaT (E n) (u n) := fun n =>
    etaT_pos (by linarith [hE n]) (hu1 n)
  -- the deterministic facts at every `n ≥ n₀`
  have key : ∀ n, n₀ ≤ n →
      1 ≤ ((d.size n : ℕ) : ℝ) ∧ ((d.L n : ℝ)) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧
      (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
      (1 - u n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ∧ (etaT (E n) (u n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ∧
      (∀ b : Fin k → Z2 (d.L n), ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) b)‖ ≤
        ((d.size n : ℕ) : ℝ) * (etaT (E n) (u n))⁻¹ ^ k) ∧
      8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
      4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ) ∧
      ((d.size n : ℕ) : ℝ) ^ (3 * k + 7) * LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) ≤
        (d.W n : ℝ) ^ (-D₀) := by
    intro n hn
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn₀ n hn
    have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hx : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - u n := h2.trans (by linarith [hut n])
    refine ⟨h1, LocalFormCalc.L_sq_le_size d n, ?_, LocalFormCalc.inv_one_sub_le h1 hτ hx, ?_, ?_,
      h4.1, h4.2.1, h4.2.2, ?_⟩
    · have : ((d.L n * d.W n) ^ 2 : ℕ) = d.size n := by rw [Sizes.size_eq]; ring
      rw [this]
    · exact LocalFormCalc.eta_inv hN0 hx hμ (hμb n) h3
    · intro b
      have hwf : (loopOf (σ n) b).WF := by simp [loopOf, LoopIdx.WF]
      have hlen : (loopOf (σ n) b).length = k := by simp [loopOf, LoopIdx.length]
      have := h6 (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) (Sizes.size_eq d n).symm (E n)
        (hE n) (u n) (u n) (hu0 n) le_rfl (hu1 n) (loopOf (σ n) b) hwf (by omega) (by omega)
      rwa [Real.rpow_one] at this
    · have := h5
      rw [Real.rpow_natCast] at this
      have hd : LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) =
          Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) := LocalFormCalc.dec_rho (hℓ n)
      rw [hd]
      exact this
  -- the kernel bound `|𝔎| ≤ 2kN`
  have hKN : ∀ n, n₀ ≤ n → ∀ a c' : Fin k → Z2 (d.L n),
      ‖𝔎 (d.L n) (u n) a c'‖ ≤ 2 * (k : ℝ) * ((d.size n : ℕ) : ℝ) := by
    intro n hn a c'
    obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
    refine (hK1 (d.L n) (d.three_le_L n) (u n) (hu0 n) (hu1 n) a c').trans ?_
    exact mul_le_mul_of_nonneg_left hτu (by positivity)
  refine ⟨fun n => if n₀ ≤ n then Fg n else LocalFormCalc.zeroF, ?_, ?_, ?_, ?_, ?_⟩
  · -- the coefficient bound
    intro n b j q
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      have := localFormLin_coef (d.three_le_L n) (d.W_pos n) (hu0 n) (hu1 n) (ρ n)
        (𝔎 (d.L n) (u n)) (hKN n hn) (σ n) hN1 hLN hη (hηpos n) hKc hc1 b j q
      rwa [← Real.rpow_natCast] at this
    · simp only [hn, ↓reduceIte, LocalFormCalc.zeroF, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- locality
    intro n
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      refine (localFormLin_loc (u n) (ρ n) (𝔎 (d.L n) (u n)) (σ n) (E n)).local τ₀ (u n) ?_
      have := hℓ n
      have := Real.rpow_pos_of_pos (hWpos n) τ₀
      simp only [hρdef]
      nlinarith [mul_pos (hℓ n) this]
    · simp only [hn, ↓reduceIte]
      intro b j q hq
      exact absurd rfl hq
  · -- sum-zero
    intro n M
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      exact LocalFormCalc.sumZero_asmF (d.three_le_L n) hk (hu0 n) (hu1 n) (ρ n) _ _ _ _ M
    · simp only [hn, ↓reduceIte]
      intro a₁
      simp [LocalFormCalc.eval_zeroF]
  · -- label decay (deterministic)
    unfold LabelDecayPT
    refine LocalFormCalc.perTimeDomAt_of_le d (fun n p ω => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
    simp only [hn, ↓reduceIte, hFg]
    by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
    · simp only [hfar, ↓reduceIte, mul_one]
      have hρle : ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) := by
        refine le_trans ?_ hfar
        simp only [hρdef]
        have := mul_pos (hℓ n) (Real.rpow_pos_of_pos (hWpos n) τ₀)
        linarith
      exact localFormLin_far (d.three_le_L n) (d.W_pos n) (by linarith [hE n]) (hu0 n)
        (hu1 n) (hρpos n) (𝔎 (d.L n) (u n)) (hKN n hn) (σ n) hN1 hLN hNLW hη hKc hc3
        (le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by omega))
          (LocalFormCalc.dec_pos _ _ _).le) htail)
        (Sizes.seqHflow_isHermitian d n (u n) ω) p.2 hρle
    · simp only [hfar, ↓reduceIte, mul_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- the error: the stochastic kernel assembly `kernelAssembly_PT` with the kernel `𝔎`, `X = 𝓛 - 𝒦`
    have hδ0 : ∀ n, 0 ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
        LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := fun n =>
      mul_nonneg (LocalFormCalc.pdelta_nonneg _ _ (hu1 n)) (LocalFormCalc.dec_pos _ _ _).le
    have hK1' : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ‖𝔎 (d.L n) (u n) a c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ 2 := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c'
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      refine (hKN n hn a c').trans ?_
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hK2' : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ρ n ≤ (zdist2 (d.L n) (c' 0 - a 0) : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖𝔎 (d.L n) (u n) a c'‖ ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
            LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c' h1 h2
      exact hK2 (d.L n) (d.three_le_L n) (u n) (hu0 n) (hu1 n) (ρ n) (hρpos n) a c' h1 h2
    have hK3' : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ρ n ≤ (KLoop.maxDist (d.L n) a : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖𝔎 (d.L n) (u n) a c'‖ ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
            LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c' h1 h2
      exact hK3 (d.L n) (d.three_le_L n) (u n) (hu0 n) (hu1 n) (ρ n) (hρpos n) a c' h1 h2
    have hX : ∀ᶠ n : ℕ in atTop, ∀ (ω : Sizes.SeqΩ d) (c' : Fin k → Z2 (d.L n)),
        ‖lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c'‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (k + 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn ω c'
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      have h2 := LocalFormCalc.norm_lkTensor_le (d.W_pos n) (by linarith [hE n]) (hu1 n)
        (Sizes.seqHflow_isHermitian d n (u n) ω) (σ n) c' hη hNLW hN1 (hKc c')
      refine h2.trans ?_
      have hk2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ 8 * (k : ℝ) := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        linarith
      calc 2 * ((d.size n : ℕ) : ℝ) ^ (k + 1) ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hk2 (by positivity)
        _ = ((d.size n : ℕ) : ℝ) ^ (k + 2) := by ring
    have hδ : ∀ᶠ n : ℕ in atTop, (1 + ((d.size n : ℕ) : ℝ) ^ k) *
        (((d.size n : ℕ) : ℝ) ^ k * (LocalFormCalc.pdelta (d.L n) k (u n) *
          LocalFormCalc.dec (d.L n) (u n) (ρ n / 2)) * ((d.size n : ℕ) : ℝ) ^ (k + 2)) ≤
        (d.W n : ℝ) ^ (-D₀) / 2 := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      exact LocalFormCalc.four_tail (d.three_le_L n) (hu0 n) (hu1 n) hN1 hLN hτu hc2 htail
    have hFXeq : ∀ n (ω : Sizes.SeqΩ d) (c' : Fin k → Z2 (d.L n)),
        (LocalFormCalc.lkF (σ n) (E n) (u n)).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) c' =
          lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c' :=
      fun n ω c' => LocalFormCalc.eval_lkF _ _ _ _ c'
    have h := LocalFormCalc.kernelAssembly_PT d (D₀ := D₀) hc hband hsize (aK := 2) (aX := k + 2)
      (K := k) (E := E) (u := u) (ρ := ρ)
      (δ := fun n => LocalFormCalc.pdelta (d.L n) k (u n) * LocalFormCalc.dec (d.L n) (u n) (ρ n / 2))
      (fun n => 𝔎 (d.L n) (u n))
      (fun n => LocalFormCalc.lkF (σ n) (E n) (u n))
      (fun n ω => lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n))
      hFXeq hu0 hu1 hδ0 hK1' hK2' hK3' hX hδ hl1
    refine LocalFormCalc.perTimeDomAt_congr_left d ?_ h
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    simp only [hn, ↓reduceIte, hFg]
    rw [hid (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) p.2]

end LinCore

section LinKernels

open LocalFormCalc

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- The `m = 5` tail coefficient `(k-1)(1-u)⁻¹(2c_L + 3L²c_L²)` of `pvdKer_hyps` is at most `P_δ`. -/
private theorem localFormLin_pvd_coef_le {u : ℝ} (hu1 : u < 1) :
    ((k : ℝ) - 1) * (1 - u)⁻¹ * (2 * cL L u + 3 * (L : ℝ) ^ 2 * cL L u ^ 2) ≤ pdelta L k u := by
  have h1u : 0 < 1 - u := by linarith
  have hC := cL_nonneg L u
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold pdelta
  have e : 6 * (1 - u)⁻¹ * cL L u + (k : ℝ) * (1 - u)⁻¹ *
        ((L : ℝ) ^ 2 * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u) -
      ((k : ℝ) - 1) * (1 - u)⁻¹ * (2 * cL L u + 3 * (L : ℝ) ^ 2 * cL L u ^ 2) =
      6 * (1 - u)⁻¹ * cL L u + (1 - u)⁻¹ * (3 * (L : ℝ) ^ 2 * cL L u ^ 2 + 2 * cL L u) +
        (k : ℝ) * (1 - u)⁻¹ * (L : ℝ) ^ 2 * cL L u := by ring
  have hpos : 0 ≤ 6 * (1 - u)⁻¹ * cL L u + (1 - u)⁻¹ * (3 * (L : ℝ) ^ 2 * cL L u ^ 2 + 2 * cL L u) +
      (k : ℝ) * (1 - u)⁻¹ * (L : ℝ) ^ 2 * cL L u := by positivity
  linarith

/-- `1 ≤ 2k(1-u)⁻¹` for `k ≥ 2`, `0 ≤ u < 1`. -/
private theorem localFormLin_one_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hk : 2 ≤ k) :
    (1 : ℝ) ≤ 2 * (k : ℝ) * (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have h1 : (1 : ℝ) ≤ (1 - u)⁻¹ := (one_le_inv₀ h1u).2 (by linarith)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

end LinKernels

section LinTargets

variable (d : Sizes)

/-- **The case `m = 0` (`𝒬_u B₀ = 𝒬_u(𝓛-𝒦)`, `int_K-L+Q2`)**: `AltLocalFormAt` at `m = 0`.
The kernel is the identity `𝔎_{a,c} = 1(c = a)`, which vanishes off the window (`c ≠ a` when
`|c₀ - a₀| ≥ ρ > maxDist c` or `maxDist a ≥ ρ > maxDist c`), so `K2'`, `K3'` hold with `δ = 0 ≤ P_δ dec`
and the assembly of `altLocalFormAt_four` applies (`localFormLin_core`).  Not the general
`AltLocalForm`: only `m = 0`. -/
theorem altLocalFormAt_zero {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 0 := by
  intro hmain hdl _hK k _ hk τ₀ D₀ hτ₀ hD₀
  refine (localFormLin_core d (κ := κ) (c := c) (τ := τ) (E := E) (s := s) (t := t) 0 hmain hdl
    hk hτ₀ hD₀ (fun L _ u a c => if c = a then (1 : ℂ) else 0) ?_ ?_ ?_ ?_).elim
    fun K h => h.elim fun C' h => ⟨K, C', h.1, fun u σ hu hut _ => h.2 u σ hu hut⟩
  · intro L W _ _ E u M σ a
    have h : altB L W E u M σ 0 =
        fun a' => ∑ c, (if c = a' then (1 : ℂ) else 0) * lkTensor L W E u M σ c := by
      funext a'
      simp [altB]
    unfold altQB
    rw [h]
  · intro L _ hL u hu0 hu1 a c
    by_cases hca : c = a
    · simp only [hca, ↓reduceIte, norm_one]
      exact localFormLin_one_le hu0 hu1 hk
    · simp only [hca, ↓reduceIte, norm_zero]
      have := localFormLin_one_le hu0 hu1 hk
      linarith
  · intro L _ hL u hu0 hu1 ρ hρ a c h1 h2
    have hca : c ≠ a := by
      intro h
      rw [h, sub_self, zdist2_zero] at h1
      simp at h1
      linarith
    simp only [hca, ↓reduceIte, norm_zero]
    exact mul_nonneg (LocalFormCalc.pdelta_nonneg L k hu1) (LocalFormCalc.dec_pos _ _ _).le
  · intro L _ hL u hu0 hu1 ρ hρ a c h1 h2
    have hca : c ≠ a := by
      intro h
      rw [h] at h2
      exact absurd h1 (not_le.mpr h2)
    simp only [hca, ↓reduceIte, norm_zero]
    exact mul_nonneg (LocalFormCalc.pdelta_nonneg L k hu1) (LocalFormCalc.dec_pos _ _ _).le

/-- **The case `m = 5` (`𝒬_u B₅`, `B₅ = 𝒫(𝓛-𝒦) ϑ̇_u`, `int_K-L+Q2`)**: `AltLocalFormAt`
at `m = 5`.  `B₅ = Σ_c pvdKer_{a,c} (𝓛-𝒦)_c` (`sum_pvdKer`); the kernel is `|ϑ̇| ≤ 2(k-1)(1-u)⁻¹`
(`K1`), supported on `c₀ = a₀` (`K2'`, bound `0`) and `≤ (k-1)(1-u)⁻¹(2c_L + 3L²c_L²) dec(ρ/2) ≤ P_δ dec(ρ/2)`
for `maxDist a ≥ ρ` (`K3'`, `pvdKer_hyps`), so the assembly of `altLocalFormAt_four` applies
(`localFormLin_core`).  Not the general `AltLocalForm`: only `m = 5`. -/
theorem altLocalFormAt_five {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 5 := by
  intro hmain hdl _hK k _ hk τ₀ D₀ hτ₀ hD₀
  refine (localFormLin_core d (κ := κ) (c := c) (τ := τ) (E := E) (s := s) (t := t) 5 hmain hdl
    hk hτ₀ hD₀ (fun L _ u => LocalFormCalc.pvdKer u) ?_ ?_ ?_ ?_).elim
    fun K h => h.elim fun C' h => ⟨K, C', h.1, fun u σ hu hut _ => h.2 u σ hu hut⟩
  · intro L W _ _ E u M σ a
    have h : altB L W E u M σ 5 =
        fun a' => ∑ c, LocalFormCalc.pvdKer u a' c * lkTensor L W E u M σ c := by
      funext a'
      rw [LocalFormCalc.sum_pvdKer]
      rfl
    unfold altQB
    rw [h]
  · intro L _ hL u hu0 hu1 a c
    refine ((LocalFormCalc.pvdKer_hyps hL hk hu0 hu1 (ρ := 1) one_pos).1 a c).trans ?_
    have h1u : 0 < 1 - u := by linarith
    have hτ0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  · intro L _ hL u hu0 hu1 ρ hρ a c h1 h2
    refine ((LocalFormCalc.pvdKer_hyps hL hk hu0 hu1 hρ).2.1 a c h1).trans ?_
    exact mul_nonneg (LocalFormCalc.pdelta_nonneg L k hu1) (LocalFormCalc.dec_pos _ _ _).le
  · intro L _ hL u hu0 hu1 ρ hρ a c h1 h2
    refine ((LocalFormCalc.pvdKer_hyps hL hk hu0 hu1 hρ).2.2 a c h1).trans ?_
    exact mul_le_mul_of_nonneg_right (localFormLin_pvd_coef_le hu1) (LocalFormCalc.dec_pos _ _ _).le

end LinTargets

end RBM.Ind
