/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.Pins
import RBM2D.Universality.OU
import RBM2D.Universality.OUHessian
import RBM2D.Propagator.FiniteDiff
import RBM2D.Induction.Split

/-!
# The zero-mode profile `S̃ = (1 - ζ) S + ζ N⁻¹ J` and the §7.2 layer interface

Paper: arXiv:2503.07606, the OU flow `𝐇_t` of the proof of `Thm: B_Univ` and its two claims (the
resolvent estimates after `417`, "details identical to Section 7.2 of [YY_25]").

Contents.
* the profile `S̃` on `Idx L W` (row sums, `S̃ = S̃^(B) ⊗ S_W`, the OU variance family
  `ouVar t` is the coordinate family of `S̃` at `ζ = 1 - e^{-t}`);
* `S̃^(B)` and `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` on `Z_L²`: `Θ̃ = Θ_T + α J` and the `ζ`-free oscillation
  bound `norm_ThetaTilde_sub_le`;
* the `τ_U` constraint of the layer (`ouTauMax`, `ouTauMax_slack`);
* the statements of the interface of the layer: `OULL`, `OUEq747` (the outputs of the random
  layer), `G1Row`, `G2bRow`;
* `ouDiag_of_ouLL` (`OUDiag` from `OULL`: Markov and a union bound inside `ouP`);
* the assembly `ouRow_of_pins` of `OURow` of `Universality/Pins.lean`;
* extreme inputs `ζ = 0` and `ζ = 1`.

Helpers are `private` or carry the prefix `ZeroModeProfile_`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal ENNReal


/-! ## The profile `S̃ = (1 - ζ) S + ζ N⁻¹ J` on `Idx L W` -/

/-- The OU time change `ζ(t) = 1 - e^{-t}`. -/
def ouZeta (t : ℝ) : ℝ := 1 - Real.exp (-t)

section Profile

theorem ZeroModeProfile_ouZeta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ouZeta t := by
  unfold ouZeta
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 ht)
  linarith

theorem ZeroModeProfile_ouZeta_le_one (t : ℝ) : ouZeta t ≤ 1 := by
  unfold ouZeta
  have := (Real.exp_pos (-t)).le
  linarith

/-- `ζ(t) ≤ t`. -/
theorem ZeroModeProfile_ouZeta_le (t : ℝ) : ouZeta t ≤ t := by
  unfold ouZeta
  have := Real.add_one_le_exp (-t)
  linarith

end Profile


/-! ## The zero-mode profile on `Z_L²` and `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` -/

section ThetaTilde

variable (L : ℕ) [NeZero L]

/-- The all-ones matrix `J` on `Z_L²`. -/
def Jmat : Matrix (Z2 L) (Z2 L) ℂ := Matrix.of fun _ _ => 1

/-- The block-level zero-mode profile `S̃^(B) = (1 - ζ) S^(B) + (ζ/L²) J`. -/
def SBtilde (ζ : ℝ) : Matrix (Z2 L) (Z2 L) ℂ :=
  (((1 - ζ : ℝ) : ℂ)) • SB L + ((ζ : ℂ) / (L : ℂ) ^ 2) • Jmat L

/-- `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹`, written with `Ring.inverse` as the `Theta`. -/
def ThetaTilde (ζ : ℝ) (ξ : ℂ) : Matrix (Z2 L) (Z2 L) ℂ :=
  Ring.inverse (1 - ξ • SBtilde L ζ)

theorem ZeroModeProfile_SB_mul_Jmat (hL : 3 ≤ L) : SB L * Jmat L = Jmat L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, mul_one]
  exact sum_SB_row L hL a

theorem ZeroModeProfile_Jmat_mul_SB (hL : 3 ≤ L) : Jmat L * SB L = Jmat L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, one_mul]
  rw [← sum_SB_row L hL b]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := congrFun (congrFun (SB_transpose L) b) k
  simpa [Matrix.transpose_apply] using this

theorem ZeroModeProfile_Jmat_mul_Jmat : Jmat L * Jmat L = ((L : ℂ) ^ 2) • Jmat L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, mul_one, Finset.sum_const,
    Finset.card_univ, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [show Fintype.card (Z2 L) = L * L by simp [Z2, ZMod.card]]
  push_cast
  ring

/-- Left inverses are two-sided and unique for `Ring.inverse` (finite matrices). -/
private theorem ringInverse_eq_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : B * A = 1) : Ring.inverse A = B := by
  have h2 : A * B = 1 := mul_eq_one_comm.mp h
  have hu : IsUnit A := ⟨⟨A, B, h2, h⟩, rfl⟩
  calc Ring.inverse A = (B * A) * Ring.inverse A := by rw [h, one_mul]
    _ = B * (A * Ring.inverse A) := by rw [mul_assoc]
    _ = B := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

theorem ZeroModeProfile_one_sub_smul_SB_mul_Jmat (hL : 3 ≤ L) (T : ℂ) :
    (1 - T • SB L) * Jmat L = (1 - T) • Jmat L := by
  rw [sub_mul, one_mul, Matrix.smul_mul, ZeroModeProfile_SB_mul_Jmat L hL, sub_smul, one_smul]

theorem ZeroModeProfile_Jmat_mul_one_sub_smul_SB (hL : 3 ≤ L) (T : ℂ) :
    Jmat L * (1 - T • SB L) = (1 - T) • Jmat L := by
  rw [mul_sub, mul_one, Matrix.mul_smul, ZeroModeProfile_Jmat_mul_SB L hL, sub_smul, one_smul]

/-- `Θ_T J = J Θ_T = (1 - T)⁻¹ J`: the constant vector is the zero mode of `Θ_T`. -/
theorem ZeroModeProfile_Theta_mul_Jmat (hL : 3 ≤ L) {T : ℂ} (hT : ‖T‖ < 1) :
    Theta L T * Jmat L = (1 - T)⁻¹ • Jmat L := by
  have h1T : (1 : ℂ) - T ≠ 0 := one_sub_ne_zero hT
  have h : Theta L T * ((1 - T • SB L) * Jmat L) = Theta L T * ((1 - T) • Jmat L) := by
    rw [ZeroModeProfile_one_sub_smul_SB_mul_Jmat L hL]
  rw [← mul_assoc, Theta_mul L hL hT, one_mul, Matrix.mul_smul] at h
  calc Theta L T * Jmat L = (1 - T)⁻¹ • ((1 - T) • (Theta L T * Jmat L)) := by
        rw [smul_smul, inv_mul_cancel₀ h1T, one_smul]
    _ = (1 - T)⁻¹ • Jmat L := by rw [← h]

/-- **The zero-mode identity**: for `T = ξ (1 - ζ)`,
`Θ̃_ξ = Θ_T + α J`, `α = ξ ζ / (L² (1 - T)(1 - ξ))`.  Everything about `Θ̃` that the loop-estimate
argument could use is therefore `Θ` at the shifted parameter `T` (`‖T‖ < 1`) plus a constant
matrix. -/
theorem ThetaTilde_eq (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) :
    ThetaTilde L ζ ξ = Theta L (ξ * (1 - (ζ : ℂ))) +
      (ξ * ζ / ((L : ℂ) ^ 2 * (1 - ξ * (1 - (ζ : ℂ))) * (1 - ξ))) • Jmat L := by
  have hTn : ‖ξ * (1 - (ζ : ℂ))‖ < 1 := by
    have hz : ‖(1 - (ζ : ℂ))‖ ≤ 1 := by
      have : (1 - (ζ : ℂ)) = ((1 - ζ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    calc ‖ξ * (1 - (ζ : ℂ))‖ = ‖ξ‖ * ‖(1 - (ζ : ℂ))‖ := norm_mul _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ < 1 := by linarith
  generalize hT : ξ * (1 - (ζ : ℂ)) = T at hTn ⊢
  have h1T : (1 : ℂ) - T ≠ 0 := one_sub_ne_zero hTn
  have h1ξ : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
  have hL2 : ((L : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hX : 1 - ξ • SBtilde L ζ =
      (1 - T • SB L) - (ξ * ((ζ : ℂ) / (L : ℂ) ^ 2)) • Jmat L := by
    unfold SBtilde
    rw [smul_add, smul_smul, smul_smul]
    have e1 : ξ * (((1 - ζ : ℝ) : ℂ)) = T := by rw [← hT]; push_cast; ring
    rw [e1]
    abel
  have hs : ((ξ * ζ / ((L : ℂ) ^ 2 * (1 - T) * (1 - ξ)))) * (1 - T)
      - (ξ * ((ζ : ℂ) / (L : ℂ) ^ 2)) * (1 - T)⁻¹
      - (ξ * ζ / ((L : ℂ) ^ 2 * (1 - T) * (1 - ξ))) * (ξ * ((ζ : ℂ) / (L : ℂ) ^ 2)) *
        (L : ℂ) ^ 2 = 0 := by
    rw [← hT]
    have h1T' : (1 : ℂ) - ξ * (1 - (ζ : ℂ)) ≠ 0 := by rw [hT]; exact h1T
    field_simp
    ring
  have key : (Theta L T + (ξ * ζ / ((L : ℂ) ^ 2 * (1 - T) * (1 - ξ))) • Jmat L) *
      (1 - ξ • SBtilde L ζ) = 1 := by
    rw [hX]
    set α : ℂ := ξ * ζ / ((L : ℂ) ^ 2 * (1 - T) * (1 - ξ)) with hα
    set c : ℂ := ξ * ((ζ : ℂ) / (L : ℂ) ^ 2) with hc
    have hΘA := Theta_mul L hL hTn
    have hΘJ := ZeroModeProfile_Theta_mul_Jmat L hL hTn
    have hJA := ZeroModeProfile_Jmat_mul_one_sub_smul_SB L hL T
    have hJJ := ZeroModeProfile_Jmat_mul_Jmat L
    generalize (1 - T • SB L) = A at hΘA hJA ⊢
    calc (Theta L T + α • Jmat L) * (A - c • Jmat L)
        = Theta L T * A - c • (Theta L T * Jmat L)
          + α • (Jmat L * A) - (α * c) • (Jmat L * Jmat L) := by
          simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          module
      _ = 1 - c • ((1 - T)⁻¹ • Jmat L) + α • ((1 - T) • Jmat L)
          - (α * c) • (((L : ℂ) ^ 2) • Jmat L) := by
          rw [hΘA, hΘJ, hJA, hJJ]
      _ = 1 + (α * (1 - T) - c * (1 - T)⁻¹ - α * c * (L : ℂ) ^ 2) • Jmat L := by
          module
      _ = 1 := by rw [hs, zero_smul, add_zero]
  exact (ringInverse_eq_of_mul_eq_one key)

/-- **`Θ̃` has the oscillation bound of `Θ`, uniformly in `ζ` and `ξ`** (d = 2): the constant
matrix `α J` of `ThetaTilde_eq` cancels in differences, and the Fourier estimate
`norm_Theta_sub_le_log` applies at the shifted parameter `T = ξ (1 - ζ)`.  No comparability
`ζ ≲ |1 - ξ|` and no further Fourier estimate is needed. -/
theorem norm_ThetaTilde_sub_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {ζ : ℝ} (h0 : 0 ≤ ζ)
    (h1 : ζ ≤ 1) (u v : Z2 L) :
    ‖ThetaTilde L ζ ξ u v - ThetaTilde L ζ ξ 0 0‖ ≤ 90 * (1 + Real.log L) := by
  have hTn : ‖ξ * (1 - (ζ : ℂ))‖ < 1 := by
    have hz : ‖(1 - (ζ : ℂ))‖ ≤ 1 := by
      have : (1 - (ζ : ℂ)) = ((1 - ζ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    calc ‖ξ * (1 - (ζ : ℂ))‖ = ‖ξ‖ * ‖(1 - (ζ : ℂ))‖ := norm_mul _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [ThetaTilde_eq L hL hξ h0 h1]
  simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply, smul_eq_mul, mul_one]
  have hshift : Theta L (ξ * (1 - (ζ : ℂ))) u v = Theta L (ξ * (1 - (ζ : ℂ))) (u - v) 0 := by
    have h := Theta_apply_add_right L hL hTn (u - v) 0 v
    simp only [sub_add_cancel, zero_add] at h
    exact h
  rw [hshift]
  have := norm_Theta_sub_le_log L hL hTn (u - v) 0
  convert this using 2
  ring

end ThetaTilde

/-! ## The `τ_U` constraint of the layer -/

/-- **The `τ_U` bound of the layer**: `τ₀(𝔠) = min (𝔠/12) (1/100)`.  The binding inequalities of
the size-level conditions in d = 2 (`N = (W L)²`, `L² ≤ N^{1-2𝔠}`, `W ≥ N^𝔠`) are `τ_U < 𝔠` at the
scale `η = N^{-1+2τ_U}` and `3τ_U/2 < 2𝔠/3` at the scale `η_Q = W^{2/3}/N`; the value has slack
factor `12` (LL scale) and `16/3` (Q scale). -/
def ouTauMax (𝔠 : ℝ) : ℝ := min (𝔠 / 12) (1 / 100)

theorem ZeroModeProfile_ouTauMax_pos {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) : 0 < ouTauMax 𝔠 := by
  unfold ouTauMax
  exact lt_min (by linarith) (by norm_num)

/-- The scale of `OUDiag`/`OULL`: `η = N^{-1+2τ_U}` (the resolvent estimates after `417`). -/
def ouEtaLL (d : Sizes) (τU : ℝ) (n : ℕ) : ℝ := ((d.size n : ℕ) : ℝ) ^ (-1 + 2 * τU)

/-- The scale of the weak QUE (`QUE_of_QDiff`, `Main/QUEFromQDiff.lean`): `η_Q = W^{2/3}/N`. -/
def ouEtaQ (d : Sizes) (n : ℕ) : ℝ := (d.W n : ℝ) ^ ((2 : ℝ) / 3) / ((d.size n : ℕ) : ℝ)

/-! ## The statements of the interface -/

/-- `tr(G E_a G^σ E_b)` for an arbitrary matrix (the `trGEGE` is the case `seqXmat`). -/
def trGEGEmat (L W : ℕ) [NeZero L] [NeZero W] (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ)
    (σ : Bool) (a b : Z2 L) : ℂ :=
  Matrix.trace (green M z * Epaper L W a * (if σ then green M z else (green M z)ᴴ) * Epaper L W b)

/-- The profile of the `QDiff` with `Θ` replaced by `Θ̃` (the (7.47) main term). -/
def profileTilde (L W : ℕ) [NeZero L] (ζ : ℝ) (z : ℂ) (σ : Bool) (a b : Z2 L) : ℂ :=
  let ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ)
  ((W : ℂ) ^ 2)⁻¹ * (ξ * ThetaTilde L ζ ξ a b)

/-- **`OULL`: the weak local law (2.26) for `𝐇_t` in moment form,** per sequence: the (7.28)
endpoint `GUEPathBounds.localLaw` transferred to `ouMat` by the one-time law (7.26).  Energies and
times are sequences with `0 ≤ t_n ≤ t*_n` (including `t = 0`, where `ζ = 0`), the moment is `2p`,
the loss `N^δ`, `η = N^{-1+2τ_U}` (the resolvent estimates after `417`).  Used in
`ouDiag_of_ouLL`. -/
def OULL (d : Sizes) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ,
      ∀ᶠ n in atTop, ∀ x : Idx (d.L n) (d.W n),
        ∫ ω, ‖green (ouMat (d.L n) (d.W n) (t n) ω)
            ((E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖ ^ (2 * p)
          ∂(ouP (d.L n) (d.W n)) ≤ ((d.size n : ℕ) : ℝ) ^ δ

/-- **`OUEq747`: (7.47) for `𝐇_t`,** per sequence, at the QUE scale
`z = E + i η_Q`: `E tr G E_a G^{(*)} E_b = W^{-2} ξ Θ̃_ξ(a,b) + O(W^δ Meta^{-3})`,
`ξ = |m|², m²`, `Θ̃ = (1 - ξ S̃^(B))⁻¹` with `ζ = ζ(t_n)`.  Integrability of the loops is automatic
(bounded, measurable) and is not a field.  Used for `OUQUE`, with `norm_ThetaTilde_sub_le`. -/
def OUEq747 (d : Sizes) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ (σ : Bool) (a b : Z2 (d.L n)),
        ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω)
              ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b ∂(ouP (d.L n) (d.W n))) -
            profileTilde (d.L n) (d.W n) (ouZeta (t n))
              ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b‖ ≤
          (d.W n : ℝ) ^ δ * (Meta (d.L n) (d.W n)
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3

/-- **`G1Row`** (the §7.2 GUE-phase layer): `P7Out` and `P7ExpOut` at the band time
`t₁ = (1 - ζ) t₀` give `OULL` and `OUEq747` for `𝐇_t` for all `τ_U ≤ τ₀(𝔠)` (`P7ExpOut` carries
the expectation bound (2.71)). -/
def G1Row : Prop :=
  P7Out → P7ExpOut → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 → OULL d τU ∧ OUEq747 d τU

/-- **`G2bRow`**: the weak QUE (2.27) for `𝐇_t`, `τ = 𝔠/3`, from (7.47) and the zero-mode
removal. -/
def G2bRow : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 →
    OUEq747 d τU → OUQUE 𝔠 d τU

/-! ## Sequence uniformization and `ouDiag_of_ouLL` -/

/-- Uniformization over admissible parameter sequences. -/
theorem ZeroModeProfile_eventually_forall_mem_of_forall_seq' {α : Type*} {T : ℕ → Set α}
    (hT : ∀ n, (T n).Nonempty) {P : ℕ → α → Prop}
    (h : ∀ s : ℕ → α, (∀ n, s n ∈ T n) → ∀ᶠ n in atTop, P n (s n)) :
    ∀ᶠ n in atTop, ∀ a ∈ T n, P n a := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∃ a, a ∈ T n ∧ ¬ P n a := by
    refine hcon.mono ?_
    intro n hn
    push Not at hn
    exact hn
  set g : ℕ → α := fun n =>
    if hn : ∃ a, a ∈ T n ∧ ¬ P n a then hn.choose else (hT n).choose with hg
  have hgmem : ∀ n, g n ∈ T n := by
    intro n
    by_cases hn : ∃ a, a ∈ T n ∧ ¬ P n a
    · simp only [hg, hn, dite_true]
      exact hn.choose_spec.1
    · simp only [hg, hn, dite_false]
      exact (hT n).choose_spec
  have hbad : ∀ n, (∃ a, a ∈ T n ∧ ¬ P n a) → ¬ P n (g n) := by
    intro n hn
    have hgn : g n = hn.choose := by simp only [hg, hn, dite_true]
    rw [hgn]
    exact hn.choose_spec.2
  have heven : ∀ᶠ n in atTop, P n (g n) := h g hgmem
  obtain ⟨n, hn1, hn2⟩ := (hcon'.and_eventually heven).exists
  exact hbad n hn1 hn2

section DiagMarkov

variable (L W : ℕ) [NeZero L] [NeZero W]

private theorem ouLL_continuous_ouMat (t : ℝ) : Continuous (ouMat L W t) := by
  unfold ouMat
  exact (((continuous_Xmat L W).comp continuous_fst).const_smul (Real.exp (-t / 2))).add
    (((continuous_Xmat L W).comp continuous_snd).const_smul (Real.sqrt (1 - Real.exp (-t))))

private theorem ouLL_continuous_entry (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) (x y : Idx L W) :
    Continuous fun ω : Ω L W × Ω L W => green (ouMat L W t ω) z x y :=
  (continuous_green_of_isHermitian (ouLL_continuous_ouMat L W t)
    (fun ω => ouMat_isHermitian L W t ω) hz).matrix_elem x y

open scoped Matrix.Norms.L2Operator in
private theorem ouLL_norm_entry_le (t : ℝ) (ω : Ω L W × Ω L W) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (x y : Idx L W) : ‖green (ouMat L W t ω) z x y‖ ≤ η⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (norm_green_le (ouMat_isHermitian L W t ω) hη hz)

/-- Markov for one diagonal entry: if `E ‖G_{xx}‖^{2p} ≤ N^δ` then
`P(‖G_{xx}‖ > N^ε) ≤ N^{δ - 2pε}`. -/
private theorem ouLL_markov (t : ℝ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : z.im = η) (x : Idx L W)
    (p : ℕ) {N ε δ : ℝ} (hN : 1 ≤ N)
    (hmom : ∫ ω, ‖green (ouMat L W t ω) z x x‖ ^ (2 * p) ∂(ouP L W) ≤ N ^ δ) :
    ouP L W {ω | N ^ ε < ‖green (ouMat L W t ω) z x x‖} ≤
      ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := by
  have hN0 : 0 < N := by linarith
  set μ := ouP L W with hμ
  set f : Ω L W × Ω L W → ℝ := fun ω => ‖green (ouMat L W t ω) z x x‖ ^ (2 * p) with hf
  have hzim : z.im ≠ 0 := by rw [hz]; exact hη.ne'
  have hfm : Measurable f :=
    ((ouLL_continuous_entry L W t hzim x x).norm.pow (2 * p)).measurable
  have hfi : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((η⁻¹) ^ (2 * p)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (ouLL_norm_entry_le L W t ω hη (by rw [hz]; exact le_abs_self _) x x) _
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (ae_of_all _ fun ω => by positivity) hfi (N ^ (2 * p * ε))
  have hsub : {ω | N ^ ε < ‖green (ouMat L W t ω) z x x‖} ⊆ {ω | N ^ (2 * p * ε) ≤ f ω} := by
    intro ω hω
    have h1 : (N ^ ε) ^ (2 * p) ≤ ‖green (ouMat L W t ω) z x x‖ ^ (2 * p) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) (le_of_lt hω) _
    have h2 : (N ^ ε) ^ (2 * p) = N ^ (2 * p * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    change N ^ (2 * p * ε) ≤ ‖green (ouMat L W t ω) z x x‖ ^ (2 * p)
    rw [← h2]
    exact h1
  have hreal : μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ (δ - 2 * p * ε) := by
    have hpos : 0 < N ^ (2 * p * ε) := Real.rpow_pos_of_pos hN0 _
    have h3 : N ^ (2 * p * ε) * μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ δ := hM.trans hmom
    rw [Real.rpow_sub hN0, le_div_iff₀ hpos]
    linarith
  calc μ {ω | N ^ ε < ‖green (ouMat L W t ω) z x x‖}
      ≤ μ {ω | N ^ (2 * p * ε) ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | N ^ (2 * p * ε) ≤ f ω}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := ENNReal.ofReal_le_ofReal hreal

end DiagMarkov

/-- **`OUDiag` from the per-sequence moment bound `OULL`.**  Uniformization over
`(t, E)` (`ZeroModeProfile_eventually_forall_mem_of_forall_seq'`), Markov for
`E ‖G_{xx}‖^{2p} ≤ N^ε` with
`2pε ≥ 1 + ε + D`, and the union bound over the `N` indices `x` inside `ouP`. -/
theorem ouDiag_of_ouLL {d : Sizes} {τU : ℝ} (h : OULL d τU) : OUDiag d τU := by
  intro κ ε D hκ hε hD
  by_cases hκ2 : 2 ≤ κ
  · refine Eventually.of_forall fun n t _ _ E hE => ?_
    exfalso
    have := abs_nonneg E
    linarith
  push Not at hκ2
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 1 + ε + D ≤ 2 * (p : ℝ) * ε := by
    refine ⟨⌈(1 + ε + D) / (2 * ε)⌉₊, ?_⟩
    have := Nat.le_ceil ((1 + ε + D) / (2 * ε))
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hT : ∀ n, ({a : ℝ × ℝ | 0 ≤ a.1 ∧ a.1 ≤ ouTStar d τU n ∧ |a.2| ≤ 2 - κ}).Nonempty := by
    intro n
    refine ⟨(0, 0), le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    simp only [abs_zero]
    linarith
  have key := ZeroModeProfile_eventually_forall_mem_of_forall_seq'
    (P := fun n (a : ℝ × ℝ) => ∀ x : Idx (d.L n) (d.W n),
      ∫ ω, ‖green (ouMat (d.L n) (d.W n) a.1 ω)
          ((a.2 : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖ ^ (2 * p)
        ∂(ouP (d.L n) (d.W n)) ≤ ((d.size n : ℕ) : ℝ) ^ ε) hT
    (fun s hs => h κ hκ (fun n => (s n).2) (fun n => (hs n).2.2) (fun n => (s n).1)
      (fun n => ⟨(hs n).1, (hs n).2.1⟩) ε hε p)
  filter_upwards [key] with n hn t ht0 ht E hE
  have hsz : 1 ≤ ((d.size n : ℕ) : ℝ) := by
    have : 1 ≤ d.size n := by
      have h1 := d.three_le_L n
      have h2 := d.W_pos n
      simp only [Sizes.size]
      exact Nat.one_le_pow _ _ (Nat.mul_pos h2 (by omega))
    exact_mod_cast this
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hη : 0 < ouEtaLL d τU n := Real.rpow_pos_of_pos hN0 _
  have hmom := hn (t, E) ⟨ht0, ht, hE.le⟩
  have hbd : ∀ x : Idx (d.L n) (d.W n),
      ouP (d.L n) (d.W n) {ω | N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
        ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖} ≤
      ENNReal.ofReal (N ^ (ε - 2 * p * ε)) := fun x =>
    ouLL_markov (d.L n) (d.W n) t hη (by simp) x p hsz (hmom x)
  have hset : {ω | ∃ x : Idx (d.L n) (d.W n), N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
      ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖} =
      ⋃ x : Idx (d.L n) (d.W n), {ω | N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
        ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖} := by
    ext ω; simp
  have hcard : (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = N := by
    rw [card_Idx_eq]; simp [hN, Sizes.size]
  change ouP (d.L n) (d.W n) {ω | ∃ x : Idx (d.L n) (d.W n), N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
      ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖} ≤ ENNReal.ofReal (N ^ (-D))
  rw [hset]
  calc ouP (d.L n) (d.W n) (⋃ x : Idx (d.L n) (d.W n), {ω | N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
        ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖})
      ≤ ∑ x : Idx (d.L n) (d.W n), ouP (d.L n) (d.W n) {ω | N ^ ε < ‖green (ouMat (d.L n) (d.W n) t ω)
        ((E : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _x : Idx (d.L n) (d.W n), ENNReal.ofReal (N ^ (ε - 2 * p * ε)) :=
        Finset.sum_le_sum fun x _ => hbd x
    _ = ENNReal.ofReal (N * N ^ (ε - 2 * p * ε)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hN0.le]
        congr 1
        rw [← hcard]
        exact (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        calc N * N ^ (ε - 2 * p * ε) = N ^ (1 + (ε - 2 * p * ε)) := by
              rw [Real.rpow_add hN0, Real.rpow_one]
          _ ≤ N ^ (-D) := Real.rpow_le_rpow_of_exponent_le hsz (by linarith)

/-- The slack of the value `ouTauMax`: `12 τ_U ≤ 𝔠` and `(3/2) τ_U ≤ 𝔠/8 < 2𝔠/3`. -/
theorem ouTauMax_slack {𝔠 τU : ℝ} (h𝔠 : 0 < 𝔠) (h : τU ≤ ouTauMax 𝔠) :
    12 * τU ≤ 𝔠 ∧ τU < 𝔠 ∧ 3 * τU / 2 < 2 * 𝔠 / 3 := by
  have h1 : τU ≤ 𝔠 / 12 := h.trans (min_le_left _ _)
  refine ⟨by linarith, by linarith, by linarith⟩


/-! ## The assembly -/


/-- **The assembly**: `G1Row` and `G2bRow` give `OURow` of `Universality/Pins.lean` (with the
input `P7ExpOut`); the `OUDiag` half is `ouDiag_of_ouLL`.  `locSC` and `QUE` are not used by this
assembly: `OULL` and `OUEq747` already include `t = 0`, where `ζ = 0`. -/
theorem ouRow_of_pins (r1 : G1Row) (r2b : G2bRow) : OURow := by
  intro h7 h7e _ _ 𝔠 h𝔠 d hd
  refine ⟨ouTauMax 𝔠, ZeroModeProfile_ouTauMax_pos h𝔠, fun τU hτ hle => ?_⟩
  have h1 := r1 h7 h7e 𝔠 h𝔠 d hd τU hτ hle
  exact ⟨r2b 𝔠 h𝔠 d hd τU hτ hle h1.2, ouDiag_of_ouLL h1.1⟩


/-! ## The cases `ζ = 0` and `ζ = 1` -/

section Extreme

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Entries of `A⁻¹` are measurable in `A` (a private copy of `measurable_matrix_inv_apply` of
`Green/RowIndep.lean`). -/
theorem ZeroModeProfile_measurable_inv_entry {n : Type*} [Fintype n] [DecidableEq n] (i j : n) :
    Measurable fun A : Matrix n n ℂ => A⁻¹ i j := by
  have h : (fun A : Matrix n n ℂ => A⁻¹ i j) = fun A => Ring.inverse A.det * A.adjugate i j := by
    funext A; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp (continuous_id.matrix_det).measurable
  · have hadj : Measurable fun A : Matrix n n ℂ => A.adjugate :=
      (continuous_id.matrix_adjugate).measurable
    exact hadj.eval_matrix

/-- `M ↦ tr(G E_a G^σ E_b)` is measurable on matrices (entrywise, no product measurability). -/
theorem ZeroModeProfile_measurable_trGEGEmat (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (σ : Bool) (a b : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => trGEGEmat L W M z σ a b := by
  have hG : ∀ x y : Idx L W, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => green M z x y :=
    fun x y => (ZeroModeProfile_measurable_inv_entry x y).comp (continuous_id.sub continuous_const).measurable
  have hmulE : ∀ f g : Matrix (Idx L W) (Idx L W) ℂ → Matrix (Idx L W) (Idx L W) ℂ,
      (∀ i j, Measurable fun M => f M i j) → (∀ i j, Measurable fun M => g M i j) →
        ∀ i j, Measurable fun M => (f M * g M) i j := by
    intro f g hf hg i j
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => (hf i k).mul (hg k j)
  have hGσ : ∀ x y : Idx L W, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      (if σ then green M z else (green M z)ᴴ) x y := by
    intro x y
    cases σ
    · simp only [Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply]
      exact (continuous_star.measurable).comp (hG y x)
    · simpa using hG x y
  have h1 : ∀ i j, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      (green M z * Epaper L W a) i j :=
    hmulE (fun M => green M z) (fun _ => Epaper L W a) hG fun _ _ => measurable_const
  have h2 : ∀ i j, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      (green M z * Epaper L W a * (if σ then green M z else (green M z)ᴴ)) i j :=
    hmulE (fun M => green M z * Epaper L W a) (fun M => if σ then green M z else (green M z)ᴴ)
      h1 hGσ
  have h3 : ∀ i j, Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ =>
      (green M z * Epaper L W a * (if σ then green M z else (green M z)ᴴ) * Epaper L W b) i j :=
    hmulE (fun M => green M z * Epaper L W a * (if σ then green M z else (green M z)ᴴ))
      (fun _ => Epaper L W b) h2 fun _ _ => measurable_const
  have hfun : (fun M : Matrix (Idx L W) (Idx L W) ℂ => trGEGEmat L W M z σ a b) = fun M =>
      ∑ i, (green M z * Epaper L W a * (if σ then green M z else (green M z)ᴴ) *
        Epaper L W b) i i := by
    funext M; rfl
  rw [hfun]
  exact Finset.measurable_sum _ fun i _ => h3 i i

end Extreme

end RBM.Univ

