/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab

/-!
# The algebra behind the general-`n` hierarchy

Everything here is finite-size algebra on the loop indices `LoopIdx (Z2 L)`; there
is no `∀ᶠ N` and no asymptotic parameter.  Paper: arXiv:2503.07606, `pro_dyncalK`,
`DefKsimLK`, `def_ELKLK`, `DefTHUST` (the displayed formula of the paper omits the factor
`S^{(B)}` in `m_i m_{i+1}/(1 - t m_i m_{i+1} S^{(B)})`, which is included here, as in `def_Ustz`
and `Kn2sol`), `LK_SDE`.

* `primBil`, `primRhs_sub` : the polarization of `primRhs` and `primRhs L - primRhs K` (`eq_L-Keee`).
* `primBilLen`, `primBilLenR`, `couplingLen` : the graded couplings `[𝒦 ∼ (𝓛-𝒦)]^{l}`.
* `couplingLen_eq_zero_outside`, `primRhs_split` : the split of `primRhs (K + D) - primRhs K`.
* `couplingLen_two_Kval_eq_thetaOp` : the `l = 2` coupling of `𝒦_u` is `ϴ_{u,σ}` (`thetaSig`).
* `loopDrift_sub_K_deriv_n` : the matrix-level drift-minus-`∂_u𝒦` identity.
* `norm_primBil_le` : the `d = 2` bound `W² n² L² B_F B_G`.

The argument parallels the one-dimensional formalization, with `W → W²`, `ZMod L → Z2 L`,
`L → L²` in the bound.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Finset Matrix RBM RBM.Path

/-! ## 1. The polarization of `primRhs` -/

section Bilinear

variable (L : ℕ) [NeZero L]

/-- The polarization of `primRhs`: the same sum with independent left and right factors. -/
def primBil (W : ℕ) (K K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)

@[simp] theorem primBil_self (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBil L W K K I = KLoop.primRhs L W K I := rfl

theorem primBil_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBil L W (K₁ + K₂) K' I = primBil L W K₁ K' I + primBil L W K₂ K' I := by
  simp only [primBil, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBil_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBil L W K (K₁ + K₂) I = primBil L W K K₁ I + primBil L W K K₂ I := by
  simp only [primBil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem primBil_add_add (W : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBil L W (K + D) (K + D) I
      = primBil L W K K I + primBil L W K D I + primBil L W D K I + primBil L W D D I := by
  rw [primBil_add_left, primBil_add_right, primBil_add_right]
  ring

/-- The loop hierarchy and the primitive equation (`pro_dyncalK`) share their quadratic
term `primRhs`, so their difference (`eq_L-Keee`) has exactly three summands: the two
couplings `[𝒦 ∼ (𝓛-𝒦)]` (`DefKsimLK`) and `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` (`def_ELKLK`). -/
theorem primRhs_sub (W : ℕ) (Lf K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    KLoop.primRhs L W Lf I - KLoop.primRhs L W K I
      = primBil L W K (Lf - K) I + primBil L W (Lf - K) K I
        + primBil L W (Lf - K) (Lf - K) I := by
  set D : LoopIdx (Z2 L) → ℂ := Lf - K with hD
  have hLf : Lf = K + D := by
    rw [hD]
    funext x
    simp
  have h1 : KLoop.primRhs L W Lf I = primBil L W (K + D) (K + D) I := by
    rw [← primBil_self, hLf]
  rw [h1, primBil_add_add, ← primBil_self L W K I]
  ring

/-- The part of the coupling in which the *left* factor is a loop of length `lK`. -/
def primBilLen (W : ℕ) (lK : ℕ) (K K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    (if (I.cutGlueL k l a).length = lK then
      K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b) else 0)

/-- The coupling `primBil F G` graded by the length of the **right** factor. -/
def primBilLenR (W : ℕ) (lK : ℕ) (F G : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    (if (I.cutGlueR k l b).length = lK then
      F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0)

/-- `[𝒦 ∼ (𝓛-𝒦)]^{l_K}` (`DefKsimLK`) with `D = 𝓛 - 𝒦`: both orientations, graded by
the length `l_K` of the `𝒦` loop. -/
def couplingLen (W : ℕ) (lK : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  primBilLen L W lK K D I + primBilLenR L W lK D K I

private theorem HierAlgebra_two_le_length_cutGlueL (I : LoopIdx (Z2 L)) (a : Z2 L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : 2 ≤ (I.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem HierAlgebra_two_le_length_cutGlueR (I : LoopIdx (Z2 L)) (b : Z2 L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : 2 ≤ (I.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

private theorem HierAlgebra_length_cutGlueL_le (I : LoopIdx (Z2 L)) (a : Z2 L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : (I.cutGlueL k l a).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem HierAlgebra_length_cutGlueR_le (I : LoopIdx (Z2 L)) (b : Z2 L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : (I.cutGlueR k l b).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

/-- Every `K`-loop occurring in the coupling has length at most `I.length`. -/
private theorem HierAlgebra_length_cutGlueL_lt (I : LoopIdx (Z2 L)) {k l : ℕ} (hk : k ∈ Icc 1 I.length)
    (hl : l ∈ Ioc k I.length) (a : Z2 L) :
    (I.cutGlueL k l a).length < I.length + 2 := by
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]
  omega

/-- Summing the graded pieces over every possible `l_K` recovers the whole coupling. -/
theorem sum_primBilLen (W : ℕ) (K K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLen L W lK K K' I = primBil L W K K' I := by
  simp only [primBilLen, primBil, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueL k l a).length)
    (fun _ => K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr (lt_of_lt_of_le (HierAlgebra_length_cutGlueL_lt L I hk hl a) hN))]

theorem sum_primBilLenR (W : ℕ) (F G : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLenR L W lK F G I = primBil L W F G I := by
  simp only [primBilLenR, primBil, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hlen : (I.cutGlueR k l b).length < N := by
    rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueR k l b).length)
    (fun _ => F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr hlen)]

/-- Summing over every `l_K` gives the whole coupling:
`∑_{l_K} [𝒦 ∼ (𝓛-𝒦)]^{l_K} = primBil K D + primBil D K`. -/
theorem sum_couplingLen (W : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, couplingLen L W lK K D I = primBil L W K D I + primBil L W D K I := by
  simp only [couplingLen, Finset.sum_add_distrib]
  rw [sum_primBilLen L W K D I hN, sum_primBilLenR L W D K I hN]

/-- Both graded couplings vanish outside `2 ≤ lK ≤ I.length`. -/
theorem couplingLen_eq_zero_outside (W : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    {lK : ℕ} (hlK : lK < 2 ∨ I.length < lK) :
    couplingLen L W lK K D I = 0 := by
  have hzeroL : primBilLen L W lK K D I = 0 := by
    unfold primBilLen
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]
    intro hcontra
    rcases hlK with h | h
    · have := HierAlgebra_two_le_length_cutGlueL L I a hk.1 hl.1 hl.2
      omega
    · have := HierAlgebra_length_cutGlueL_le L I a hk.1 hl.1 hl.2
      omega
  have hzeroR : primBilLenR L W lK D K I = 0 := by
    unfold primBilLenR
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]
    intro hcontra
    rcases hlK with h | h
    · have := HierAlgebra_two_le_length_cutGlueR L I b hk.1 hl.1 hl.2
      omega
    · have := HierAlgebra_length_cutGlueR_le L I b hk.1 hl.1 hl.2
      omega
  rw [couplingLen, hzeroL, hzeroR, add_zero]

/-- The split of `primRhs (K + D) - primRhs K` into the `l_K = 2` coupling, the `l_K ≥ 3`
couplings and the quadratic term `primBil D D` (`eq_L-Keee`, `DefKsimLK`,
`def_ELKLK`); the only hypothesis is `2 ≤ n`. -/
theorem primRhs_split (W : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    (hn : 2 ≤ I.length) :
    KLoop.primRhs L W (K + D) I - KLoop.primRhs L W K I
      = couplingLen L W 2 K D I
        + (∑ lK ∈ Finset.Icc 3 I.length, couplingLen L W lK K D I)
        + primBil L W D D I := by
  have hDeq : (K + D) - K = D := by funext x; simp
  have hps := primRhs_sub L W (K + D) K I
  rw [hDeq] at hps
  have hN : I.length + 2 ≤ I.length + 2 := le_rfl
  have hsum := sum_couplingLen L W K D I hN
  have h2mem : (2 : ℕ) ∈ Finset.range (I.length + 2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h2mem] at hsum
  have hsub : Finset.Icc 3 I.length ⊆ (Finset.range (I.length + 2)).erase 2 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hsum2 : ∑ lK ∈ (Finset.range (I.length + 2)).erase 2, couplingLen L W lK K D I
      = ∑ lK ∈ Finset.Icc 3 I.length, couplingLen L W lK K D I := by
    symm
    refine Finset.sum_subset hsub (fun x hx hnx => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    exact couplingLen_eq_zero_outside L W K D I (by omega)
  rw [hsum2] at hsum
  rw [hps, ← hsum]

/-- Row sums of `‖S‖`: `∑_b ‖S_{ab}‖ = 1` (from the `NNReal` statement `sum_nnnorm_SB_row`). -/
private theorem HierAlgebra_sum_norm_SB_row (hL : 3 ≤ L) (a : Z2 L) :
    ∑ b : Z2 L, ‖SB L a b‖ = 1 := by
  have h := sum_nnnorm_SB_row L hL a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simpa using h'

/-- **`norm_primBil_le`, `d = 2` form** (`W → W²`, `L → L²` relative to `d = 1`):
`primBil F G I` is bounded by the product of separate envelopes `BF, BG` on `F, G` at the cut
sub-loop lengths `2 … I.length`, with the constant `W² n² L² B_F B_G`. -/
theorem norm_primBil_le (hL : 3 ≤ L) (W : ℕ) (F G : LoopIdx (Z2 L) → ℂ)
    (I : LoopIdx (Z2 L)) (hI : I.WF) {BF BG : ℝ} (hBF0 : 0 ≤ BF) (hBG0 : 0 ≤ BG)
    (hBF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ BF)
    (hBG : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ BG) :
    ‖primBil L W F G I‖ ≤ (W : ℝ) ^ 2 * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * BG := by
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖∑ a : Z2 L, ∑ b : Z2 L,
          F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ ≤ (L : ℝ) ^ 2 * BF * BG := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hBFl : ∀ a : Z2 L, ‖F (I.cutGlueL k l a)‖ ≤ BF := fun a =>
      hBF _ (LoopIdx.WF.cutGlueL hI a hk.1 hl.1 hl.2)
        (HierAlgebra_two_le_length_cutGlueL L I a hk.1 hl.1 hl.2)
        (HierAlgebra_length_cutGlueL_le L I a hk.1 hl.1 hl.2)
    have hBGr : ∀ b : Z2 L, ‖G (I.cutGlueR k l b)‖ ≤ BG := fun b =>
      hBG _ (LoopIdx.WF.cutGlueR hI b hk.1 hl.1 hl.2)
        (HierAlgebra_two_le_length_cutGlueR L I b hk.1 hl.1 hl.2)
        (HierAlgebra_length_cutGlueR_le L I b hk.1 hl.1 hl.2)
    calc ‖∑ a : Z2 L, ∑ b : Z2 L,
            F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖
        ≤ ∑ a : Z2 L, ∑ b : Z2 L,
            ‖F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Z2 L, ∑ b : Z2 L, BF * BG * ‖SB L a b‖ := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul]
          calc ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖
              ≤ BF * ‖SB L a b‖ * BG :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hBFl a) (norm_nonneg _)) (hBGr b)
                  (norm_nonneg _) (by positivity)
            _ = BF * BG * ‖SB L a b‖ := by ring
      _ = ∑ _a : Z2 L, BF * BG := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, HierAlgebra_sum_norm_SB_row L hL a, mul_one]
      _ = (L : ℝ) ^ 2 * BF * BG := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
            nsmul_eq_mul]
          push_cast
          ring
  calc ‖primBil L W F G I‖
      ≤ (W : ℝ) ^ 2 * ∑ _k ∈ Icc 1 I.length, ∑ _l ∈ Ioc _k I.length, (L : ℝ) ^ 2 * BF * BG := by
        rw [primBil, norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) ^ 2 * ∑ _k ∈ Icc 1 I.length, (I.length : ℝ) * ((L : ℝ) ^ 2 * BF * BG) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have hle : ((I.length - k : ℕ) : ℝ) ≤ (I.length : ℝ) := by
          exact_mod_cast Nat.sub_le I.length k
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (W : ℝ) ^ 2 * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * BG := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

end Bilinear

/-! ## 2. The `l = 2` coupling is the generator `ϴ_{u,σ}` (`DefTHUST`) -/

section Coupling2

variable {L : ℕ} [NeZero L]

private theorem take_one_drop {α : Type*} (l : List α) (d : α) {m : ℕ} (h : m < l.length) :
    (l.drop m).take 1 = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
  rfl

private theorem take_two_drop {α : Type*} (l : List α) (d : α) {m m' : ℕ} (hm : m + 1 = m')
    (h : m' < l.length) : (l.drop m).take 2 = [l.getD m d, l.getD m' d] := by
  subst hm
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h]
  rfl

private theorem drop_last {α : Type*} (l : List α) (d : α) {m : ℕ} (h : m + 1 = l.length) :
    l.drop m = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega),
    List.getD_eq_getElem _ _ (by omega)]

omit [NeZero L] in
private theorem cutGlueL_succ_eq (I : LoopIdx (Z2 L)) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k + 1 ≤ I.length) (a : Z2 L) :
    I.cutGlueL k (k + 1) a = ⟨I.σ, I.a.set (k - 1) a⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hkm : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change I.σ.take k ++ I.σ.drop (k + 1 - 1) = I.σ
    simp
  · change I.a.take (k - 1) ++ a :: I.a.drop (k + 1 - 1) = I.a.set (k - 1) a
    rw [List.set_eq_take_cons_drop a hkm, show k + 1 - 1 = k - 1 + 1 by omega]

omit [NeZero L] in
private theorem cutGlueR_succ_eq (I : LoopIdx (Z2 L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k + 1 ≤ I.length) (b : Z2 L) :
    I.cutGlueR k (k + 1) b
      = ⟨[I.σ.getD (k - 1) true, I.σ.getD k true], [I.a.getD (k - 1) 0, b]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h2 : k < I.σ.length := by rw [hσ]; omega
  have h1' : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change (I.σ.drop (k - 1)).take (k + 1 - k + 1) = _
    rw [show k + 1 - k + 1 = 2 by omega, take_two_drop I.σ true (by omega : k - 1 + 1 = k) h2]
  · change (I.a.drop (k - 1)).take (k + 1 - k) ++ [b] = _
    rw [show k + 1 - k = 1 by omega, take_one_drop I.a 0 h1']
    rfl

omit [NeZero L] in
private theorem cutGlueL_one_eq (I : LoopIdx (Z2 L)) (hwf : I.WF) (hn : 2 ≤ I.length) (a : Z2 L) :
    I.cutGlueL 1 I.length a
      = ⟨[I.σ.getD 0 true, I.σ.getD (I.length - 1) true], [a, I.a.getD (I.length - 1) 0]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h0 : 0 < I.σ.length := by rw [hσ]; omega
  have hm : I.length - 1 + 1 = I.σ.length := by rw [hσ]; omega
  have hm' : I.length - 1 + 1 = I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change I.σ.take 1 ++ I.σ.drop (I.length - 1) = _
    rw [drop_last I.σ true hm, show I.σ.take 1 = (I.σ.drop 0).take 1 by simp,
      take_one_drop I.σ true h0]
    rfl
  · change I.a.take 0 ++ a :: I.a.drop (I.length - 1) = _
    rw [drop_last I.a 0 hm']
    rfl

omit [NeZero L] in
private theorem cutGlueR_one_eq (I : LoopIdx (Z2 L)) (hwf : I.WF) (hn : 2 ≤ I.length) (b : Z2 L) :
    I.cutGlueR 1 I.length b = ⟨I.σ, I.a.set (I.length - 1) b⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have hm' : I.length - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change (I.σ.drop 0).take (I.length - 1 + 1) = I.σ
    rw [List.drop_zero, show I.length - 1 + 1 = I.length by omega,
      List.take_of_length_le (by rw [hσ])]
  · change (I.a.drop 0).take (I.length - 1) ++ [b] = _
    rw [List.drop_zero, List.set_eq_take_cons_drop b hm',
      show I.length - 1 + 1 = I.length by omega,
      List.drop_eq_nil_of_le (by rw [hlen])]

/-- Only the wrap-around cut `(k,l) = (1,n)` has a left chain of length 2. -/
private theorem primBilLen_two_eq (W : ℕ) (K D : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    (hn : 2 ≤ I.length) :
    primBilLen L W 2 K D I
      = (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
          K (I.cutGlueL 1 I.length a) * SB L a b * D (I.cutGlueR 1 I.length b) := by
  have hlenL : ∀ (k l : ℕ) (a : Z2 L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueL k l a).length = k + I.length - l + 1 :=
    fun k l a h1 h2 h3 => LoopIdx.length_cutGlueL I a h1 h2 h3
  rw [primBilLen]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (by simp [Finset.mem_Icc]; omega)]
  · rw [Finset.sum_eq_single_of_mem I.length (by simp [Finset.mem_Ioc]; omega)]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ite_eq_left (by rw [hlenL 1 I.length a le_rfl (by omega) le_rfl]; omega)]
    · intro l hl hne
      rw [Finset.mem_Ioc] at hl
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (by rw [hlenL 1 l a le_rfl hl.1 hl.2]; omega)]
  · intro k hk hne
    rw [Finset.mem_Icc] at hk
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (by rw [hlenL k l a hk.1 hl.1 hl.2]; omega)]

/-- Only the adjacent cuts `(k, k+1)` have a right chain of length 2. -/
private theorem primBilLenR_two_eq (W : ℕ) (F G : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    (hn : 2 ≤ I.length) :
    primBilLenR L W 2 F G I
      = (W : ℂ) ^ 2 * ∑ k ∈ Finset.Icc 1 (I.length - 1), ∑ a : Z2 L, ∑ b : Z2 L,
          F (I.cutGlueL k (k + 1) a) * SB L a b * G (I.cutGlueR k (k + 1) b) := by
  have hlenR : ∀ (k l : ℕ) (b : Z2 L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueR k l b).length = l - k + 1 :=
    fun k l b h1 h2 h3 => LoopIdx.length_cutGlueR I b h1 h2 h3
  rw [primBilLenR]
  congr 1
  have key : ∀ k ∈ Finset.Icc 1 I.length,
      (∑ l ∈ Finset.Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
        (if (I.cutGlueR k l b).length = 2 then
          F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0))
      = if k ∈ Finset.Icc 1 (I.length - 1) then
          (∑ a : Z2 L, ∑ b : Z2 L,
            F (I.cutGlueL k (k + 1) a) * SB L a b * G (I.cutGlueR k (k + 1) b)) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hlt : k < I.length
    · rw [ite_eq_left (by rw [Finset.mem_Icc]; omega)]
      rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [Finset.mem_Ioc]; omega)]
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [ite_eq_left (by rw [hlenR k (k + 1) b hk.1 (by omega) (by omega)]; omega)]
      · intro l hl hne
        rw [Finset.mem_Ioc] at hl
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right (by rw [hlenR k l b hk.1 hl.1 hl.2]; omega)]
    · have hkn : k = I.length := by omega
      subst hkn
      rw [ite_eq_right (by rw [Finset.mem_Icc]; omega), Finset.Ioc_self, Finset.sum_empty]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; rw [Finset.mem_Icc] at *; omega)]

/-- Reindex `∑_{k=1}^{n}` as `∑_{k=0}^{n-1}`. -/
private theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- The cyclic edge weight `ξ_i = m(σ_i) m(σ_{i+1 mod n})` of a loop index. -/
private def xiLoop (m : Bool → ℂ) (I : LoopIdx (Z2 L)) (i : ℕ) : ℂ :=
  m (I.σ.getD i true) * m (I.σ.getD ((i + 1) % I.length) true)

section
variable (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ) (K D : LoopIdx (Z2 L) → ℂ)

private theorem thetaR_term
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = KLoop.kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ I.length) :
    (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        D (I.cutGlueL k (k + 1) a) * SB L a b * K (I.cutGlueR k (k + 1) b)
      = ∑ c : Z2 L,
          xiLoop m I (k - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (k - 1)) * SB L) (I.a.getD (k - 1) 0) c
            * D ⟨I.σ, I.a.set (k - 1) c⟩ := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hW : (W : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hW'
  have hxi : xiLoop m I (k - 1) = m (I.σ.getD (k - 1) true) * m (I.σ.getD k true) := by
    rw [xiLoop, show (k - 1 + 1) % I.length = k by
      rw [show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt (by omega)]]
  have hinner : ∀ b : Z2 L, K (I.cutGlueR k (k + 1) b)
      = ((W : ℂ) ^ 2)⁻¹ * xiLoop m I (k - 1)
          * Theta L ((t : ℂ) * xiLoop m I (k - 1)) (I.a.getD (k - 1) 0) b := by
    intro b
    rw [cutGlueR_succ_eq I hwf hk hk', hK, KLoop.kTwo, hxi]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cutGlueL_succ_eq I hk hk', Finset.mul_sum]
  calc ∑ b : Z2 L, (W : ℂ) ^ 2 * (D ⟨I.σ, I.a.set (k - 1) a⟩ * SB L a b
          * K (I.cutGlueR k (k + 1) b))
      = ∑ b : Z2 L, (Theta L ((t : ℂ) * xiLoop m I (k - 1)) (I.a.getD (k - 1) 0) b
            * SB L b a) * (xiLoop m I (k - 1) * D ⟨I.σ, I.a.set (k - 1) a⟩) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hinner b, show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
        field_simp
    _ = xiLoop m I (k - 1)
          * (Theta L ((t : ℂ) * xiLoop m I (k - 1)) * SB L) (I.a.getD (k - 1) 0) a
          * D ⟨I.σ, I.a.set (k - 1) a⟩ := by
        rw [← Finset.sum_mul, Matrix.mul_apply]
        ring

private theorem thetaL_term (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = KLoop.kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * xiLoop m I (I.length - 1)‖ < 1) :
    (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        K (I.cutGlueL 1 I.length a) * SB L a b * D (I.cutGlueR 1 I.length b)
      = ∑ c : Z2 L,
          xiLoop m I (I.length - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) * SB L)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hW : (W : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hW'
  have hxi : m (I.σ.getD 0 true) * m (I.σ.getD (I.length - 1) true)
      = xiLoop m I (I.length - 1) := by
    rw [xiLoop, show (I.length - 1 + 1) % I.length = 0 by
      rw [show I.length - 1 + 1 = I.length by omega, Nat.mod_self]]
    ring
  have hsym : ∀ p q : Z2 L, Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) p q
      = Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) q p := fun p q =>
    congrFun (congrFun (Theta_transpose L hL hξ) q) p
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cutGlueR_one_eq I hwf hn]
  have step : ∀ a : Z2 L,
      (W : ℂ) ^ 2 * (K (I.cutGlueL 1 I.length a) * SB L a b * D ⟨I.σ, I.a.set (I.length - 1) b⟩)
        = (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) (I.a.getD (I.length - 1) 0) a
            * SB L a b) * (xiLoop m I (I.length - 1) * D ⟨I.σ, I.a.set (I.length - 1) b⟩) := by
    intro a
    rw [cutGlueL_one_eq I hwf hn, hK, KLoop.kTwo, hxi, hsym a (I.a.getD (I.length - 1) 0)]
    field_simp
  rw [Finset.sum_congr rfl fun a _ => step a, ← Finset.sum_mul, Matrix.mul_apply]
  ring

private theorem couplingLen_two_eq_sum (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = KLoop.kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * xiLoop m I (I.length - 1)‖ < 1) :
    couplingLen L W 2 K D I
      = ∑ i ∈ Finset.range I.length, ∑ c : Z2 L,
          xiLoop m I i * (Theta L ((t : ℂ) * xiLoop m I i) * SB L) (I.a.getD i 0) c
            * D ⟨I.σ, I.a.set i c⟩ := by
  have hR : primBilLenR L W 2 D K I
      = ∑ i ∈ Finset.range (I.length - 1), ∑ c : Z2 L,
          xiLoop m I i * (Theta L ((t : ℂ) * xiLoop m I i) * SB L) (I.a.getD i 0) c
            * D ⟨I.σ, I.a.set i c⟩ := by
    rw [primBilLenR_two_eq W D K I hn, Finset.mul_sum,
      sum_Icc_one_eq_range (I.length - 1)
        (fun k => (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
          D (I.cutGlueL k (k + 1) a) * SB L a b * K (I.cutGlueR k (k + 1) b))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [thetaR_term W m t K D hK I hwf (by omega : 1 ≤ i + 1) (by omega)]
    simp
  have hL2 : primBilLen L W 2 K D I
      = ∑ c : Z2 L,
          xiLoop m I (I.length - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) * SB L)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
    rw [primBilLen_two_eq W K D I hn, thetaL_term W m t K D hL hK I hwf hn hξ]
  rw [couplingLen, hR, hL2,
    show I.length = (I.length - 1) + 1 by omega, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  exact add_comm _ _

end

/-- `List.set` on a `List.ofFn` is `Function.update`. -/
private theorem set_ofFn_eq_ofFn_update {α : Type*} {n : ℕ} (a : Fin n → α) (i : Fin n) (c : α) :
    (List.ofFn a).set (i : ℕ) c = List.ofFn (Function.update a i c) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.length_set, List.length_ofFn] at h1
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases hij : (i : ℕ) = j
  · subst hij
    simp [Function.update_self]
  · rw [ite_eq_right hij, Function.update_apply,
      ite_eq_right (by simp only [Fin.ext_iff]; omega)]

end Coupling2

private theorem HierAlgebra_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

private theorem HierAlgebra_norm_xi {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (s s' : Bool) : ‖(u : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ < 1 := by
  rw [norm_mul, norm_mul, HierAlgebra_norm_mSig hE, HierAlgebra_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg hu0, mul_one, mul_one]
  exact hu1

/-- **The `l_K = 2` coupling of `𝒦_u` against any `D`, at every loop length `k ≥ 2` and every sign
vector, is `ϴ_{u,σ}D`** (`thetaSig`, `DefTHUST` with the factor `S`; the general-`k`
form of the sentence after `def_Ustz_2`).  The only hypotheses are `3 ≤ L`, `|E| ≤ 2`,
`0 ≤ u < 1`, `NeZero W`, `2 ≤ k`. -/
theorem couplingLen_two_Kval_eq_thetaOp (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (E : ℝ)
    (hE : |E| ≤ 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (D : LoopIdx (Z2 L) → ℂ)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    couplingLen L W 2 (KLoop.Kcal L W E u) D (loopOf σ a)
      = thetaSig L E σ u (fun v => D (loopOf σ v)) a := by
  have hwf : (loopOf σ a).WF := by
    change (List.ofFn σ).length = (List.ofFn a).length
    simp
  have hlen : (loopOf σ a).length = k := by
    change (List.ofFn a).length = k
    simp
  have hK : ∀ s₁ s₂ (x y : Z2 L), KLoop.Kcal L W E u ⟨[s₁, s₂], [x, y]⟩
      = KLoop.kTwo L W (KLoop.mSig E) u s₁ s₂ x y := by
    intro s₁ s₂ x y
    simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]
  have hxi : ∀ i : Fin k, xiLoop (KLoop.mSig E) (loopOf σ a) (i : ℕ)
      = KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) := by
    intro i
    have hmod : ((i : ℕ) + 1) % k < k := Nat.mod_lt _ (by omega)
    have h1 : (List.ofFn σ).getD (i : ℕ) true = σ i := by
      rw [List.getD_eq_getElem (List.ofFn σ) true (by rw [List.length_ofFn]; exact i.isLt),
        List.getElem_ofFn]
    have h2 : (List.ofFn σ).getD (((i : ℕ) + 1) % k) true = σ (i + 1) := by
      rw [List.getD_eq_getElem (List.ofFn σ) true (by rw [List.length_ofFn]; exact hmod),
        List.getElem_ofFn]
      congr 1
      rw [Fin.ext_iff, Fin.val_add, Fin.val_one' k, Nat.mod_eq_of_lt (show 1 < k by omega)]
    change KLoop.mSig E ((List.ofFn σ).getD (i : ℕ) true)
        * KLoop.mSig E ((List.ofFn σ).getD (((i : ℕ) + 1) % (loopOf σ a).length) true) = _
    rw [hlen, h1, h2]
  have hξ : ‖(u : ℂ) * xiLoop (KLoop.mSig E) (loopOf σ a) ((loopOf σ a).length - 1)‖ < 1 := by
    unfold xiLoop
    exact HierAlgebra_norm_xi hE hu0 hu1 _ _
  rw [couplingLen_two_eq_sum W (KLoop.mSig E) u (KLoop.Kcal L W E u) D hL hK (loopOf σ a) hwf
    (by rw [hlen]; exact hk) hξ, hlen]
  refine (Finset.sum_range _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  have hcomm := (Theta_commute_SB L hL (HierAlgebra_norm_xi hE hu0 hu1 (σ i) (σ (i + 1)))).eq
  have hget : (List.ofFn a).getD (i : ℕ) 0 = a i := by
    rw [List.getD_eq_getElem (List.ofFn a) 0 (by simp), List.getElem_ofFn]
  simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul]
  rw [hxi i, hcomm]
  change _ * (SB L * Theta L _) ((List.ofFn a).getD (i : ℕ) 0) c
      * D ⟨List.ofFn σ, (List.ofFn a).set (i : ℕ) c⟩ = _
  rw [hget, set_ofFn_eq_ofFn_update]
  rfl

/-! ## 3. The drift-minus-`∂_u𝒦` identity at matrix level -/

private theorem HierAlgebra_couplingLen_eq_ksimLK (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ) (l : ℕ) (I : LoopIdx (Z2 L)) :
    couplingLen L W l (KLoop.Kcal L W E u) (LKf L W E u M) I = ksimLK L W E u M l I := by
  simp only [couplingLen, primBilLen, primBilLenR, ksimLK, Finset.sum_add_distrib, mul_add]
  ring

/-- **The general-`k` drift-minus-`∂_u𝒦` identity at matrix level** (in the shape `HierarchyN`
needs).  With `𝓛 = LLf`, `𝒦 = Kcal`,
`𝓛 - 𝒦 = LKf`, for an arbitrary matrix `M` (no `genMat` and no Hermitian hypothesis: the identity
is algebra on the values `𝓛_M(J)`):
`(llPairN + egtN)(I) - ∂_u𝒦_u(I) = ϴ_{u,σ}(𝓛-𝒦) + Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}`
at `I = loopOf σ a`.  With `genMat(𝓛_I) = llPairN + egtN` (`LoopGenN`) this is `HierarchyN`. -/
theorem loopDrift_sub_K_deriv_n (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ) (hL : 3 ≤ L)
    (hE : |E| < 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Gauss.Idx L W) (Gauss.Idx L W) ℂ)
    (k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    (llPairN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a))
        - deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u
      = thetaSig L E σ u (lkTensor L W E u M σ) a
          + ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a)
          + elklkN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a) := by
  have hwf : (loopOf σ a).WF := by
    change (List.ofFn σ).length = (List.ofFn a).length
    simp
  have hlen : (loopOf σ a).length = k := by
    change (List.ofFn a).length = k
    simp
  have hW1 : 1 ≤ W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hprim := (KLoop.isPrimitive_Kcal L W hL hW1 E hE).1 u ⟨hu0, hu1⟩ (loopOf σ a) hwf
    (by rw [hlen]; exact hk)
  have hderiv : deriv (fun v : ℝ => KLoop.Kcal L W E v (loopOf σ a)) u
      = KLoop.primRhs L W (KLoop.Kcal L W E u) (loopOf σ a) := hprim.deriv
  have hLL : llPairN L W E u M (loopOf σ a)
      = KLoop.primRhs L W (LLf L W E u M) (loopOf σ a) := rfl
  have hKD : KLoop.Kcal L W E u + LKf L W E u M = LLf L W E u M := by
    funext x
    simp [LKf]
  have hsplit := primRhs_split L W (KLoop.Kcal L W E u) (LKf L W E u M) (loopOf σ a)
    (by rw [hlen]; exact hk)
  rw [hKD, hlen,
    couplingLen_two_Kval_eq_thetaOp L W hL E hE.le u hu0 hu1 (LKf L W E u M) hk σ a] at hsplit
  have hsum : ∑ l ∈ Finset.Icc 3 k, couplingLen L W l (KLoop.Kcal L W E u) (LKf L W E u M)
        (loopOf σ a) = ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a) :=
    Finset.sum_congr rfl fun l _ => HierAlgebra_couplingLen_eq_ksimLK L W E u M l _
  have hEl : primBil L W (LKf L W E u M) (LKf L W E u M) (loopOf σ a)
      = elklkN L W E u M (loopOf σ a) := rfl
  have hθ : thetaSig L E σ u (lkTensor L W E u M σ) a
      = thetaSig L E σ u (fun v => LKf L W E u M (loopOf σ v)) a := rfl
  rw [hsum, hEl] at hsplit
  rw [hderiv, hLL, hθ]
  linear_combination hsplit

end RBM.Ind
