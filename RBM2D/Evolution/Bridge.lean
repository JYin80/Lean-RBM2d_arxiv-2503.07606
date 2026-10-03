/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Case5

/-!
# The bridges from the explicit forms to the asymptotic contracts

Paper: arXiv:2503.07606, Section 7: `sum_res_1`, `nonalternating`, `symmetric_tensor`,
`eq:double_sum_zero_tensor`.

Statements (namespace `RBM.Evol`): the `Prop`s `BridgeDet`, `BridgeCase5`, `PrecMono`.  Proved
here: `bridgeDet`, `bridgeCase5`, `precMono`, and the two unconditional corollaries
`sumDecayDetPrec`, `sumDecayCase5Prec` (constant `cPrec 𝔠`).

Argument.  Fix `κ, 𝔠, δ > 0`, `k ≥ 2`, `τ, D > 0`, `ε > 0`.  Each explicit bound is `near + far`.
* `HasDecay L W s τ D A` is `DecayWin L (ℓ_s W^τ) (W^{-D}) A` (definitional), `K = W^τ ≥ 1`,
  `δ_A = W^{-D}`, `M = tmax A`; `ratioR = rhoR` for `|E| < 2` (`Im m` cancels).
* Near: `|c| (1 + log L)^m ≤ (1 + log N)^m |c| ≤ N^ε` for `N ≥ N₀` (only place where `N₀` is used),
  `K^n = W^{nτ} ≤ W^{C_k τ}` for `n ≤ 4k ≤ C_k`.
* Far: `L² ≤ N`, `(1 - s)/(1 - t) ≤ 1/(1 - t) ≤ N` (`1 - t ≥ N^{-1+δ} ≥ N^{-1}`), and `N ≤ W^{1/𝔠}`
  (`W ≥ N^𝔠`) give `P ≤ N^m ≤ W^{m/𝔠} ≤ W^{C_k}` for `m ≤ 4k`.
* A repeated sign is Case 1; for Case 4 with an alternating `σ` `ugenCase4AltExplicit` is used; for
  Case 5 with an alternating `σ` `ugenPairCase5AltExplicit`.
`precMono` is the monotonicity of `W^{Cτ} M B + W^{-D+C}` in `C` for `W ≥ 1`.  The argument
follows the one-dimensional kernel-decay bridge, which has fixed constants.
-/

noncomputable section

namespace RBM.Evol

open Filter RBM.Path RBM.Ind

/-! ## The statements -/

/-- **Bridge to the deterministic contract**: the explicit forms `ugenGenExplicit`,
`ugenCase1Explicit`, `ugenCase4AltExplicit` give
`SumDecayDetPrec` with `C = cPrec 𝔠`, for any constants (they are absorbed by `N^ε`). -/
def BridgeDet : Prop :=
  ∀ (cG : ℕ → ℝ) (c1 : ℕ → ℝ → ℝ) (c4 : ℕ → ℝ),
    UgenGenExplicit cG → UgenCase1Explicit c1 → UgenCase4AltExplicit c4 →
    ∀ κ 𝔠 δ : ℝ, SumDecayDetPrec κ 𝔠 δ (cPrec 𝔠)

/-- **Bridge to Case 5**: `ugenPairCase1Explicit` and `ugenPairCase5AltExplicit` give
`SumDecayCase5Prec` with `C = cPrec 𝔠`. -/
def BridgeCase5 : Prop :=
  ∀ (c1 : ℕ → ℝ → ℝ) (c5 : ℕ → ℝ),
    UgenPairCase1Explicit c1 → UgenPairCase5AltExplicit c5 →
    ∀ κ 𝔠 δ : ℝ, SumDecayCase5Prec κ 𝔠 δ (cPrec 𝔠)

/-- **Monotonicity**: a larger contract constant gives a weaker statement
(`1 ≤ W`), so a consumer may take any `C ≥ cPrec 𝔠`. -/
def PrecMono : Prop :=
  ∀ (κ 𝔠 δ : ℝ) (C C' : ℕ → ℝ), (∀ k, C k ≤ C' k) →
    (SumDecayDetPrec κ 𝔠 δ C → SumDecayDetPrec κ 𝔠 δ C') ∧
    (SumDecayCase5Prec κ 𝔠 δ C → SumDecayCase5Prec κ 𝔠 δ C')

/-! ## Helpers -/

/-- Polylog absorption, at a real variable `N`: `|c| (1 + log N)^m ≤ N^ε` eventually. -/
private theorem bridge_polylog_real (c : ℝ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |c| * (1 + Real.log N) ^ m ≤ (N : ℝ) ^ ε := by
  have hc : 0 < (2 ^ m * (|c| + 1))⁻¹ := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hε).def hc
  have h2 : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
  have h3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (h1.and h2)
  filter_upwards [h3] with N hN
  obtain ⟨hN1, hN2⟩ := hN
  set x : ℝ := (N : ℝ) with hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hN2
  have hlog1 : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_natCast,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hN1
  have hpow : (1 + Real.log x) ^ m ≤ 2 ^ m * Real.log x ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) m
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
  calc |c| * (1 + Real.log x) ^ m ≤ |c| * (2 ^ m * Real.log x ^ m) := by gcongr
    _ ≤ |c| * (2 ^ m * ((2 ^ m * (|c| + 1))⁻¹ * x ^ ε)) := by gcongr
    _ = |c| / (|c| + 1) * x ^ ε := by field_simp
    _ ≤ 1 * x ^ ε := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = x ^ ε := one_mul _

/-- Uniform polylog absorption: for `L ≤ N`, `|c| (1 + log L)^a ≤ N^ε` for all `a ≤ m`,
eventually in `N`. -/
private theorem bridge_polylog (c : ℝ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (L a : ℕ), 1 ≤ L → L ≤ N → a ≤ m →
      |c| * (1 + Real.log L) ^ a ≤ (N : ℝ) ^ ε := by
  filter_upwards [bridge_polylog_real c m hε] with N hN L a hL hLN ha
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hlogN : Real.log L ≤ Real.log N :=
    Real.log_le_log hL0 (by exact_mod_cast hLN)
  calc |c| * (1 + Real.log L) ^ a ≤ |c| * (1 + Real.log L) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) ha) (abs_nonneg c)
    _ ≤ |c| * (1 + Real.log N) ^ m := by gcongr
    _ ≤ (N : ℝ) ^ ε := hN

/-- `N^m ≤ W^{m/𝔠}` from `N^𝔠 ≤ W`. -/
private theorem bridge_pow_le {N W 𝔠 : ℝ} (hN : 0 ≤ N) (h𝔠 : 0 < 𝔠) (hW : N ^ 𝔠 ≤ W) (m : ℕ) :
    N ^ m ≤ W ^ ((m : ℝ) / 𝔠) := by
  have h1 : N ^ m = (N ^ 𝔠) ^ ((m : ℝ) / 𝔠) := by
    rw [← Real.rpow_mul hN, mul_div_cancel₀ _ h𝔠.ne', Real.rpow_natCast]
  rw [h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hN _) hW (by positivity)

/-- `(W^τ)^n ≤ W^{C τ}` for `W ≥ 1`, `n ≤ C`. -/
private theorem bridge_K_pow {W τ C : ℝ} {n : ℕ} (hW : 1 ≤ W) (hτ : 0 ≤ τ) (hn : (n : ℝ) ≤ C) :
    (W ^ τ) ^ n ≤ W ^ (C * τ) := by
  rw [← Real.rpow_mul_natCast (by linarith) τ n]
  exact Real.rpow_le_rpow_of_exponent_le hW (by nlinarith)

/-- The contract constant covers every `n ≤ 4k`. -/
private theorem bridge_cPrec_ge {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {k n : ℕ} (hn : n ≤ 4 * k) :
    (n : ℝ) ≤ cPrec 𝔠 k ∧ (n : ℝ) / 𝔠 ≤ cPrec 𝔠 k := by
  have h1 : (n : ℝ) ≤ 4 * k := by exact_mod_cast hn
  have h2 : (n : ℝ) / 𝔠 ≤ 4 * k / 𝔠 := div_le_div_of_nonneg_right h1 h𝔠.le
  have h3 : (0 : ℝ) ≤ 4 * k / 𝔠 := by positivity
  have h4 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold cPrec
  constructor <;> linarith

/-- `c · lam^a · Z ≤ N^ε · Z'` from `|c| lam^a ≤ N^ε`, `0 ≤ lam` and `0 ≤ Z ≤ Z'`. -/
private theorem bridge_absorb {c lam Z Z' Nε : ℝ} {a : ℕ} (hc : |c| * lam ^ a ≤ Nε)
    (hlam : 0 ≤ lam) (hZ : 0 ≤ Z) (hZZ : Z ≤ Z') : c * lam ^ a * Z ≤ Nε * Z' := by
  have h0 : 0 ≤ Nε := le_trans (mul_nonneg (abs_nonneg c) (pow_nonneg hlam a)) hc
  have h1 : c * lam ^ a ≤ Nε :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg hlam a)) hc
  calc c * lam ^ a * Z ≤ Nε * Z := mul_le_mul_of_nonneg_right h1 hZ
    _ ≤ Nε * Z' := mul_le_mul_of_nonneg_left hZZ h0

/-- Near term: `c lam^a (K^n Y) ≤ N^ε (W^{Cτ} Y)`, `K = W^τ`, `n ≤ C`. -/
private theorem bridge_near {W τ C lam Nε c : ℝ} {a n : ℕ} (Y : ℝ) (hW : 1 ≤ W) (hτ : 0 ≤ τ)
    (hn : (n : ℝ) ≤ C) (hlam : 0 ≤ lam) (hc : |c| * lam ^ a ≤ Nε) (hY : 0 ≤ Y) :
    c * lam ^ a * ((W ^ τ) ^ n * Y) ≤ Nε * (W ^ (C * τ) * Y) :=
  bridge_absorb hc hlam
    (mul_nonneg (pow_nonneg (Real.rpow_nonneg (by linarith) _) _) hY)
    (mul_le_mul_of_nonneg_right (bridge_K_pow hW hτ hn) hY)

/-- Far term: `c lam^a (P W^{-D}) ≤ N^ε W^{-D + C}` when `0 ≤ P ≤ N^m ≤ W^{m/𝔠} ≤ W^C`. -/
private theorem bridge_far {W D C lam Nε c N 𝔠 P : ℝ} {a m : ℕ} (hW : 1 ≤ W) (hlam : 0 ≤ lam)
    (hc : |c| * lam ^ a ≤ Nε) (hm : N ^ m ≤ W ^ ((m : ℝ) / 𝔠)) (hmC : (m : ℝ) / 𝔠 ≤ C)
    (hP0 : 0 ≤ P) (hP : P ≤ N ^ m) :
    c * lam ^ a * (P * W ^ (-D)) ≤ Nε * W ^ (-D + C) := by
  have hW0 : 0 < W := by linarith
  have hPW : P ≤ W ^ C := hP.trans (hm.trans (Real.rpow_le_rpow_of_exponent_le hW hmC))
  apply bridge_absorb hc hlam (mul_nonneg hP0 (Real.rpow_nonneg hW0.le _))
  rw [Real.rpow_add hW0, mul_comm (W ^ (-D))]
  exact mul_le_mul_of_nonneg_right hPW (Real.rpow_nonneg hW0.le _)

/-- `X^j x^j ≤ N^{j+j}` for `0 ≤ X ≤ N`, `0 ≤ x ≤ N`. -/
private theorem bridge_pair_le {N X x : ℝ} (j : ℕ) (hX0 : 0 ≤ X) (hXN : X ≤ N) (hx0 : 0 ≤ x)
    (hxN : x ≤ N) : X ^ j * x ^ j ≤ N ^ (j + j) := by
  rw [pow_add]
  exact mul_le_mul (pow_le_pow_left₀ hX0 hXN j) (pow_le_pow_left₀ hx0 hxN j)
    (pow_nonneg hx0 j) (pow_nonneg (hX0.trans hXN) j)

/-- `ratioR = rhoR` for `|E| < 2`: the factor `Im m` cancels. -/
private theorem bridge_ratioR_eq {L : ℕ} {E s t : ℝ} (hE : |E| < 2) :
    ratioR L E s t = rhoR L s t := by
  have hI : (RBM.Gauss.spectralM E).im ≠ 0 := (RBM.Gauss.spectralM_im_pos hE).ne'
  unfold ratioR rhoR etaT
  rw [← mul_assoc, ← mul_assoc]
  exact mul_div_mul_right _ _ hI

/-- The scale, time and bandwidth facts shared by the bridges. -/
private theorem bridge_facts {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (hδ : 0 < δ)
    {N L W : ℕ} [NeZero W] (hL : 3 ≤ L) (hNW : W ^ 2 * L ^ 2 = N)
    (hW : (N : ℝ) ^ 𝔠 ≤ W) {E : ℝ} (hE : |E| ≤ 2 - κ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1 - (N : ℝ) ^ (-1 + δ)) :
    t < 1 ∧ ratioR L E s t = rhoR L s t ∧ 1 ≤ rhoR L s t ∧ 0 ≤ (1 - s) / (1 - t) ∧
      (1 - s) / (1 - t) ≤ N ∧ (L : ℝ) ^ 2 ≤ N ∧ (1 : ℝ) ≤ W ∧ (1 : ℝ) ≤ N ∧ L ≤ N ∧
      ∀ m : ℕ, (N : ℝ) ^ m ≤ (W : ℝ) ^ ((m : ℝ) / 𝔠) := by
  have hLpos : 0 < L := by omega
  have hWpos : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hNpos : 0 < N := hNW ▸ Nat.mul_pos (pow_pos hWpos 2) (pow_pos hLpos 2)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNr : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hpos : 0 < (N : ℝ) ^ (-1 + δ) := Real.rpow_pos_of_pos hNr _
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hE2 : |E| < 2 := by linarith
  have hNinv : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + δ) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hx : (1 - s) / (1 - t) ≤ N := by
    rw [div_le_iff₀ h1t]
    have h2 : 1 ≤ (N : ℝ) * (1 - t) :=
      calc (1 : ℝ) = N * (N : ℝ)⁻¹ := (mul_inv_cancel₀ hNr.ne').symm
        _ ≤ N * (1 - t) := mul_le_mul_of_nonneg_left (by linarith) hNr.le
    linarith
  have hNW' : (N : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by rw [← hNW]; push_cast; ring
  have hL2 : (L : ℝ) ^ 2 ≤ N := by
    rw [hNW']
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hW1)
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := le_trans (by nlinarith) hL2
    exact_mod_cast this
  exact ⟨ht1, bridge_ratioR_eq hE2, KernelExpand_one_le_rhoR hL hst ht1,
    div_nonneg (by linarith) h1t.le, hx, hL2, hW1, hN1, hLN,
    bridge_pow_le hNr.le h𝔠 hW⟩

/-! ## The bridges -/

/-- **Bridge to the deterministic contract**: the explicit forms `ugenGenExplicit`,
`ugenCase1Explicit`, `ugenCase4AltExplicit` give
`SumDecayDetPrec` with `C = cPrec 𝔠`, for any constants. -/
theorem bridgeDet : BridgeDet := by
  intro cG c1 c4 hG h1 h4 κ 𝔠 δ hκ h𝔠 hδ k _ hk τ D hτ hD ε hε
  filter_upwards [bridge_polylog (cG k) (k + 1) hε, bridge_polylog (c1 k κ) (k + 1) hε,
    bridge_polylog (c4 k) (k + 1) hε] with N hp0 hp1 hp4
  intro L W _ _ hL hNW hW E hE s t hs hst ht σ A hA a
  obtain ⟨ht1, hrho, hρ1, hx0, hxN, hL2, hW1, hN1, hLN, hNpow⟩ :=
    bridge_facts hκ h𝔠 hδ hL hNW hW hE hs hst ht
  have hL1 : 1 ≤ L := by omega
  have hE2 : |E| ≤ 2 := by linarith
  have hlam : 0 ≤ 1 + Real.log L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast hL1); linarith
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hK1 : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hAM : ∀ b, ‖A b‖ ≤ tmax L A := fun b =>
    Finset.le_sup' (fun a => ‖A a‖) (Finset.mem_univ b)
  have hM0 : 0 ≤ tmax L A := (norm_nonneg _).trans (hAM (Classical.arbitrary _))
  have hδA : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
  have hdec : DecayWin L (ellT L s * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D)) A := hA
  have hρ0 : 0 ≤ rhoR L s t := by linarith
  have hX0 : 0 ≤ (ellT L t / ellT L s) ^ 2 := sq_nonneg _
  have hxk : ((1 - s) / (1 - t)) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ hx0 hxN k
  dsimp only
  rw [hrho]
  -- Case 1
  have hC1 : (∃ i : Fin k, σ i = σ (i + 1)) →
      ‖Ugen L E σ s t A a‖ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) * tmax L A *
        rhoR L s t ^ k + (W : ℝ) ^ (-D + cPrec 𝔠 k)) := by
    intro hrep
    have hc := h1 k hk L hL κ E hκ hE s t hs hst ht1 σ hrep ((W : ℝ) ^ τ) (tmax L A)
      ((W : ℝ) ^ (-D)) hK1 hM0 hδA A hAM hdec a
    have n1 := bridge_near (n := 2 * (k - 1)) (rhoR L s t ^ k * tmax L A) hW1 hτ.le
      (bridge_cPrec_ge h𝔠 (by omega : 2 * (k - 1) ≤ 4 * k)).1 hlam
      (hp1 L k hL1 hLN (by omega)) (mul_nonneg (pow_nonneg hρ0 _) hM0)
    have f1 := bridge_far (D := D) (a := 0) (P := ((1 - s) / (1 - t)) ^ k) (c := 1)
      (lam := 1 + Real.log L) (Nε := (N : ℝ) ^ ε) hW1 hlam (by simpa using hNε) (hNpow k)
      (bridge_cPrec_ge h𝔠 (by omega : k ≤ 4 * k)).2 (pow_nonneg hx0 _) hxk
    calc ‖Ugen L E σ s t A a‖ ≤ _ := hc
      _ = c1 k κ * (1 + Real.log L) ^ k * (((W : ℝ) ^ τ) ^ (2 * (k - 1)) *
            (rhoR L s t ^ k * tmax L A)) +
          1 * (1 + Real.log L) ^ 0 * (((1 - s) / (1 - t)) ^ k * (W : ℝ) ^ (-D)) := by ring
      _ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) * (rhoR L s t ^ k * tmax L A)) +
          (N : ℝ) ^ ε * (W : ℝ) ^ (-D + cPrec 𝔠 k) := add_le_add n1 f1
      _ = _ := by ring
  refine ⟨?_, hC1, ?_⟩
  · -- general bound
    have hc := hG k hk L hL E hE2 s t hs hst ht1 σ ((W : ℝ) ^ τ) (tmax L A)
      ((W : ℝ) ^ (-D)) hK1 hM0 hδA A hAM hdec a
    have n1 := bridge_near (n := 2 * (k - 1))
      ((ellT L t / ellT L s) ^ 2 * rhoR L s t ^ k * tmax L A) hW1 hτ.le
      (bridge_cPrec_ge h𝔠 (by omega : 2 * (k - 1) ≤ 4 * k)).1 hlam
      (hp0 L (k - 1) hL1 hLN (by omega))
      (mul_nonneg (mul_nonneg hX0 (pow_nonneg hρ0 _)) hM0)
    have f1 := bridge_far (D := D) (a := 0) (P := ((1 - s) / (1 - t)) ^ k) (c := 1)
      (lam := 1 + Real.log L) (Nε := (N : ℝ) ^ ε) hW1 hlam (by simpa using hNε) (hNpow k)
      (bridge_cPrec_ge h𝔠 (by omega : k ≤ 4 * k)).2 (pow_nonneg hx0 _) hxk
    calc ‖Ugen L E σ s t A a‖ ≤ _ := hc
      _ = cG k * (1 + Real.log L) ^ (k - 1) * (((W : ℝ) ^ τ) ^ (2 * (k - 1)) *
            ((ellT L t / ellT L s) ^ 2 * rhoR L s t ^ k * tmax L A)) +
          1 * (1 + Real.log L) ^ 0 * (((1 - s) / (1 - t)) ^ k * (W : ℝ) ^ (-D)) := by ring
      _ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) *
            ((ellT L t / ellT L s) ^ 2 * rhoR L s t ^ k * tmax L A)) +
          (N : ℝ) ^ ε * (W : ℝ) ^ (-D + cPrec 𝔠 k) := add_le_add n1 f1
      _ = _ := by ring
  · -- Case 4
    intro hsz hsym
    by_cases hrep : ∃ i : Fin k, σ i = σ (i + 1)
    · exact hC1 hrep
    · push Not at hrep
      have hc := h4 k hk L hL E hE2 s t hs hst ht1 σ hrep ((W : ℝ) ^ τ) (tmax L A)
        ((W : ℝ) ^ (-D)) hK1 hM0 hδA A hAM hdec hsz hsym a
      rw [mul_pow] at hc
      have n1 := bridge_near (n := 2 * k) (rhoR L s t ^ k * tmax L A) hW1 hτ.le
        (bridge_cPrec_ge h𝔠 (by omega : 2 * k ≤ 4 * k)).1 hlam
        (hp4 L (k + 1) hL1 hLN le_rfl) (mul_nonneg (pow_nonneg hρ0 _) hM0)
      have f1 := bridge_far (D := D) (a := k) (m := k + k) (c := c4 k)
        (P := ((L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k)
        (lam := 1 + Real.log L) (Nε := (N : ℝ) ^ ε) hW1 hlam
        (hp4 L k hL1 hLN (by omega)) (hNpow (k + k))
        (bridge_cPrec_ge h𝔠 (by omega : k + k ≤ 4 * k)).2
        (mul_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg hx0 _))
        (bridge_pair_le k (sq_nonneg _) hL2 hx0 hxN)
      calc ‖Ugen L E σ s t A a‖ ≤ _ := hc
        _ = c4 k * (1 + Real.log L) ^ (k + 1) * (((W : ℝ) ^ τ) ^ (2 * k) *
              (rhoR L s t ^ k * tmax L A)) +
            c4 k * (1 + Real.log L) ^ k *
              (((L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k * (W : ℝ) ^ (-D)) := by ring
        _ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) * (rhoR L s t ^ k * tmax L A)) +
            (N : ℝ) ^ ε * (W : ℝ) ^ (-D + cPrec 𝔠 k) := add_le_add n1 f1
        _ = _ := by ring

/-- **Bridge to Case 5**: `ugenPairCase1Explicit` and `ugenPairCase5AltExplicit` give
`SumDecayCase5Prec` with `C = cPrec 𝔠`. -/
theorem bridgeCase5 : BridgeCase5 := by
  intro c1 c5 h1 h5 κ 𝔠 δ hκ h𝔠 hδ k _ hk τ D hτ hD ε hε
  filter_upwards [bridge_polylog (c1 k κ) (2 * k + 1) hε,
    bridge_polylog (c5 k) (2 * k + 1) hε] with N hp1 hp5
  intro L W _ _ hL hNW hW E hE s t hs hst ht σ A hA hdsz a
  obtain ⟨ht1, hrho, hρ1, hx0, hxN, hL2, hW1, hN1, hLN, hNpow⟩ :=
    bridge_facts hκ h𝔠 hδ hL hNW hW hE hs hst ht
  have hL1 : 1 ≤ L := by omega
  have hE2 : |E| ≤ 2 := by linarith
  have hlam : 0 ≤ 1 + Real.log L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast hL1); linarith
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hK1 : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hAM : ∀ b b', ‖A b b'‖ ≤ tmax2 L A := fun b b' =>
    Finset.le_sup' (fun p : (Fin k → Z2 L) × (Fin k → Z2 L) => ‖A p.1 p.2‖)
      (Finset.mem_univ (b, b'))
  have hM0 : 0 ≤ tmax2 L A :=
    (norm_nonneg _).trans (hAM (Classical.arbitrary _) (Classical.arbitrary _))
  have hδA : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (by linarith) _
  have hdec : DecayWin2 L (ellT L s * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D)) A := hA
  have hρ0 : 0 ≤ rhoR L s t := by linarith
  have hxk : ((1 - s) / (1 - t)) ^ (2 * k) ≤ (N : ℝ) ^ (2 * k) := pow_le_pow_left₀ hx0 hxN _
  rw [hrho]
  by_cases hrep : ∃ i : Fin k, σ i = σ (i + 1)
  · -- repeated sign (`ugenPairCase1Explicit`)
    have hc := h1 k hk L hL κ E hκ hE s t hs hst ht1 σ hrep ((W : ℝ) ^ τ) (tmax2 L A)
      ((W : ℝ) ^ (-D)) hK1 hM0 hδA A hAM hdec a
    have n1 := bridge_near (n := 2 * (2 * k - 1)) (rhoR L s t ^ (2 * k) * tmax2 L A) hW1 hτ.le
      (bridge_cPrec_ge h𝔠 (by omega : 2 * (2 * k - 1) ≤ 4 * k)).1 hlam
      (hp1 L (2 * k) hL1 hLN (by omega)) (mul_nonneg (pow_nonneg hρ0 _) hM0)
    have f1 := bridge_far (D := D) (a := 0) (P := ((1 - s) / (1 - t)) ^ (2 * k)) (c := 1)
      (lam := 1 + Real.log L) (Nε := (N : ℝ) ^ ε) hW1 hlam (by simpa using hNε) (hNpow (2 * k))
      (bridge_cPrec_ge h𝔠 (by omega : 2 * k ≤ 4 * k)).2 (pow_nonneg hx0 _) hxk
    calc ‖UgenPair L E σ s t A a‖ ≤ _ := hc
      _ = c1 k κ * (1 + Real.log L) ^ (2 * k) * (((W : ℝ) ^ τ) ^ (2 * (2 * k - 1)) *
            (rhoR L s t ^ (2 * k) * tmax2 L A)) +
          1 * (1 + Real.log L) ^ 0 * (((1 - s) / (1 - t)) ^ (2 * k) * (W : ℝ) ^ (-D)) := by ring
      _ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) * (rhoR L s t ^ (2 * k) * tmax2 L A)) +
          (N : ℝ) ^ ε * (W : ℝ) ^ (-D + cPrec 𝔠 k) := add_le_add n1 f1
      _ = _ := by ring
  · -- alternating sign (`ugenPairCase5AltExplicit`)
    push Not at hrep
    have hc := h5 k hk L hL E hE2 s t hs hst ht1 σ hrep ((W : ℝ) ^ τ) (tmax2 L A)
      ((W : ℝ) ^ (-D)) hK1 hM0 hδA A hAM hdec hdsz a
    rw [mul_pow] at hc
    have n1 := bridge_near (n := 4 * k) (rhoR L s t ^ (2 * k) * tmax2 L A) hW1 hτ.le
      (bridge_cPrec_ge h𝔠 (le_refl (4 * k))).1 hlam
      (hp5 L (2 * k + 1) hL1 hLN le_rfl) (mul_nonneg (pow_nonneg hρ0 _) hM0)
    have f1 := bridge_far (D := D) (a := 2 * k) (m := 2 * k + 2 * k) (c := c5 k)
      (P := ((L : ℝ) ^ 2) ^ (2 * k) * ((1 - s) / (1 - t)) ^ (2 * k))
      (lam := 1 + Real.log L) (Nε := (N : ℝ) ^ ε) hW1 hlam
      (hp5 L (2 * k) hL1 hLN (by omega)) (hNpow (2 * k + 2 * k))
      (bridge_cPrec_ge h𝔠 (by omega : 2 * k + 2 * k ≤ 4 * k)).2
      (mul_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg hx0 _))
      (bridge_pair_le (2 * k) (sq_nonneg _) hL2 hx0 hxN)
    calc ‖UgenPair L E σ s t A a‖ ≤ _ := hc
      _ = c5 k * (1 + Real.log L) ^ (2 * k + 1) * (((W : ℝ) ^ τ) ^ (4 * k) *
            (rhoR L s t ^ (2 * k) * tmax2 L A)) +
          c5 k * (1 + Real.log L) ^ (2 * k) *
            (((L : ℝ) ^ 2) ^ (2 * k) * ((1 - s) / (1 - t)) ^ (2 * k) * (W : ℝ) ^ (-D)) := by ring
      _ ≤ (N : ℝ) ^ ε * ((W : ℝ) ^ (cPrec 𝔠 k * τ) * (rhoR L s t ^ (2 * k) * tmax2 L A)) +
          (N : ℝ) ^ ε * (W : ℝ) ^ (-D + cPrec 𝔠 k) := add_le_add n1 f1
      _ = _ := by ring

/-- **Monotonicity**: a larger contract constant gives a weaker statement. -/
theorem precMono : PrecMono := by
  intro κ 𝔠 δ C C' hCC'
  constructor
  · intro h hκ h𝔠 hδ k _ hk τ D hτ hD ε hε
    filter_upwards [h hκ h𝔠 hδ k hk τ D hτ hD ε hε] with N hN
    intro L W _ _ hL hNW hW E hE s t hs hst ht σ A hA a
    obtain ⟨ht1, hrho, hρ1, hx0, hxN, hL2, hW1, hN1, hLN, hNpow⟩ :=
      bridge_facts hκ h𝔠 hδ hL hNW hW hE hs hst ht
    have h0 := hN L W hL hNW hW E hE s t hs hst ht σ A hA a
    have hAM : ∀ b, ‖A b‖ ≤ tmax L A := fun b =>
      Finset.le_sup' (fun a => ‖A a‖) (Finset.mem_univ b)
    have hM0 : 0 ≤ tmax L A := (norm_nonneg _).trans (hAM (Classical.arbitrary _))
    have e1 : (W : ℝ) ^ (C k * τ) ≤ (W : ℝ) ^ (C' k * τ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (mul_le_mul_of_nonneg_right (hCC' k) hτ.le)
    have e2 : (W : ℝ) ^ (-D + C k) ≤ (W : ℝ) ^ (-D + C' k) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [hCC' k])
    have hNε : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hR0 : 0 ≤ ratioR L E s t := by rw [hrho]; linarith
    have hX0 : 0 ≤ (ellT L t / ellT L s) ^ 2 := sq_nonneg _
    dsimp only at h0 ⊢
    obtain ⟨g0, g1, g4⟩ := h0
    refine ⟨g0.trans ?_, fun hr => (g1 hr).trans ?_, fun hz hy => (g4 hz hy).trans ?_⟩ <;> gcongr
  · intro h hκ h𝔠 hδ k _ hk τ D hτ hD ε hε
    filter_upwards [h hκ h𝔠 hδ k hk τ D hτ hD ε hε] with N hN
    intro L W _ _ hL hNW hW E hE s t hs hst ht σ A hA hdsz a
    obtain ⟨ht1, hrho, hρ1, hx0, hxN, hL2, hW1, hN1, hLN, hNpow⟩ :=
      bridge_facts hκ h𝔠 hδ hL hNW hW hE hs hst ht
    have h0 := hN L W hL hNW hW E hE s t hs hst ht σ A hA hdsz a
    have hAM : ∀ b b', ‖A b b'‖ ≤ tmax2 L A := fun b b' =>
      Finset.le_sup' (fun p : (Fin k → Z2 L) × (Fin k → Z2 L) => ‖A p.1 p.2‖)
        (Finset.mem_univ (b, b'))
    have hM0 : 0 ≤ tmax2 L A :=
      (norm_nonneg _).trans (hAM (Classical.arbitrary _) (Classical.arbitrary _))
    have e1 : (W : ℝ) ^ (C k * τ) ≤ (W : ℝ) ^ (C' k * τ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (mul_le_mul_of_nonneg_right (hCC' k) hτ.le)
    have e2 : (W : ℝ) ^ (-D + C k) ≤ (W : ℝ) ^ (-D + C' k) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [hCC' k])
    have hNε : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hR0 : 0 ≤ ratioR L E s t := by rw [hrho]; linarith
    exact h0.trans (by gcongr)

/-- **Corollary**: the contract `SumDecayDetPrec` with `C = cPrec 𝔠`, unconditionally
(explicit forms `ugenGenExplicit`, `ugenCase1Explicit`, `ugenCase4AltExplicit` with the constants
`cGen`, `cCase1`, `cCase4`). -/
theorem sumDecayDetPrec (κ 𝔠 δ : ℝ) : SumDecayDetPrec κ 𝔠 δ (cPrec 𝔠) :=
  bridgeDet cGen cCase1 cCase4 ugenGenExplicit ugenCase1Explicit ugenCase4AltExplicit κ 𝔠 δ

/-- **Corollary**: the contract `SumDecayCase5Prec` with `C = cPrec 𝔠`, unconditionally
(explicit forms `ugenPairCase1Explicit`, `ugenPairCase5AltExplicit` with the constants `cPair1`,
`cCase5`). -/
theorem sumDecayCase5Prec (κ 𝔠 δ : ℝ) : SumDecayCase5Prec κ 𝔠 δ (cPrec 𝔠) :=
  bridgeCase5 cPair1 cCase5 ugenPairCase1Explicit ugenPairCase5AltExplicit κ 𝔠 δ

end RBM.Evol

end
