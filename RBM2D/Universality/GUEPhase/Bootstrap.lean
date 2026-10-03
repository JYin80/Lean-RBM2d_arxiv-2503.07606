/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.OperationsPair
import RBM2D.Defs.StochDom
import RBM2D.Defs.Domination
import RBM2D.Path.PerTime
import RBM2D.Path.Scales
import Mathlib.Data.Set.Finite.List

/-!
# The abstract bootstraps of the GUE phase (§7.2 of [YY_25], `d = 2`)

The real-analysis and `≺`-bookkeeping part of the GUE phase.  There is no carrier and no matrix
model; the random layer enters only through hypotheses of the `≺` form.

* `SBgue` (`S^{(B)}_{GUE} = 1/L²` on `Z_L²`), `primBilGUE`, `primRhsGUE` (the primitive equation
  (7.33) with `S^{(B)} → S^{(B)}_{GUE}`, prefactor `W²`), `norm_primBilGUE_le`,
  `norm_primRhsGUE_le` (the power counting (7.34): the double sum over `a, b ∈ Z_L²` with
  `S_GUE = 1/L²` costs `L²`, times `W²`: `N = (W L)²`).
* `continuity_argument`, `K_bootstrap` (abstract ODE bootstrap (7.35) ⟹ (7.36)), `eq736`.
* `supOn` and its lemmas, `rhs745G`, `rhs746G` (the right sides of (7.45)G and (7.46)G).

`ellT_eq_L` states `ℓ_t = L` for the path scale `RBM.Path.ellT` once `L² (1 - t) ≤ 1`; it needs
`t < 1`, since at `t ≥ 1` Lean's `1/√(1-t)` is `0`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open Matrix Finset Filter

/-! ### (7.25): the variance profile -/

section Variance

variable (L : ℕ) [NeZero L]

/-- `S^{(B)}_{GUE}`: `(S^{(B)}_{GUE})_{ab} = 1/L²` on `Z_L²`. -/
def SBgue : Matrix (Z2 L) (Z2 L) ℂ := Matrix.of fun _ _ => ((L : ℂ) ^ 2)⁻¹

@[simp] theorem SBgue_apply (a b : Z2 L) : SBgue L a b = ((L : ℂ) ^ 2)⁻¹ := rfl

end Variance

/-! ### The continuity argument -/

section Continuity

open Set

/-- **The continuity argument** used for (7.36) and (7.27), (7.28): finitely many continuous
quantities `f i` start strictly below the continuous thresholds `g i` at `t₁`, and whenever all
of them are below their thresholds on `[t₁, t]`, they are strictly below at `t` (the bootstrap
improvement).  Then they stay strictly below on all of `[t₁, t₀]`. -/
theorem continuity_argument {ι : Type*} {S : Set ι} (hS : S.Finite) {f g : ι → ℝ → ℝ}
    {t1 t0 : ℝ} (hf : ∀ i ∈ S, ContinuousOn (f i) (Icc t1 t0))
    (hg : ∀ i ∈ S, ContinuousOn (g i) (Icc t1 t0)) (h0 : ∀ i ∈ S, f i t1 < g i t1)
    (hstep : ∀ t ∈ Icc t1 t0, (∀ u ∈ Icc t1 t, ∀ i ∈ S, f i u ≤ g i u) →
      ∀ i ∈ S, f i t < g i t) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, f i t < g i t := by
  by_contra hno
  push Not at hno
  set F : Set ℝ := {t | t ∈ Icc t1 t0 ∧ ∃ i ∈ S, g i t ≤ f i t} with hFdef
  have hFeq : F = ⋃ i ∈ S, {t | t ∈ Icc t1 t0 ∧ g i t ≤ f i t} := by
    ext t
    simp only [hFdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨ht, i, hi, h⟩; exact ⟨i, hi, ht, h⟩
    · rintro ⟨i, hi, ht, h⟩; exact ⟨ht, i, hi, h⟩
  have hFc : IsClosed F := by
    rw [hFeq]
    exact hS.isClosed_biUnion fun i hi => isClosed_Icc.isClosed_le (hg i hi) (hf i hi)
  obtain ⟨t, ht, i, hi, hti⟩ := hno
  have hFne : F.Nonempty := ⟨t, ht, i, hi, hti⟩
  have hFbdd : BddBelow F := ⟨t1, fun x hx => hx.1.1⟩
  set T := sInf F with hT
  have hTF : T ∈ F := hFc.csInf_mem hFne hFbdd
  have hT1 : t1 ≤ T := hTF.1.1
  have hTne : T ≠ t1 := by
    intro h
    obtain ⟨-, j, hj, hle⟩ := hTF
    rw [h] at hle
    exact absurd (h0 j hj) (not_lt.2 hle)
  have hT1' : t1 < T := lt_of_le_of_ne hT1 (Ne.symm hTne)
  have hbelow : ∀ u ∈ Ico t1 T, ∀ j ∈ S, f j u < g j u := by
    intro u hu j hj
    by_contra hle
    push Not at hle
    have huF : u ∈ F := ⟨⟨hu.1, (hu.2.le.trans hTF.1.2)⟩, j, hj, hle⟩
    exact absurd (csInf_le hFbdd huF) (not_le.2 hu.2)
  have hsub : Ico t1 T ⊆ Icc t1 t0 := fun u hu => ⟨hu.1, hu.2.le.trans hTF.1.2⟩
  have hcl : T ∈ closure (Ico t1 T) := by
    rw [closure_Ico hTne.symm]
    exact ⟨hT1, le_rfl⟩
  have hTle : ∀ j ∈ S, f j T ≤ g j T := by
    intro j hj
    exact ContinuousWithinAt.closure_le hcl (((hf j hj) T hTF.1).mono hsub)
      (((hg j hj) T hTF.1).mono hsub) fun y hy => (hbelow y hy j hj).le
  have hall : ∀ u ∈ Icc t1 T, ∀ j ∈ S, f j u ≤ g j u := by
    intro u hu j hj
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hTle j hj
    · exact (hbelow u ⟨hu.1, h⟩ j hj).le
  obtain ⟨hTI, j, hj, hle⟩ := hTF
  exact absurd (hstep T hTI hall j hj) (not_lt.2 hle)

end Continuity

/-! ### (7.30): the scales of the GUE phase -/

section Scales

/-- **(7.30) ⟹ `ℓ_{t₁} = L`**: `ℓ_t = L` (`RBM.Path.ellT`) as soon as `L² (1 - t) ≤ 1`
(and `t < 1`: at `t ≥ 1` Lean gives `1/√(1-t) = 0`). -/
theorem ellT_eq_L {L : ℕ} {t : ℝ} (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ 1) :
    Path.ellT L t = L := by
  unfold Path.ellT
  rw [min_eq_right]
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  have h1 : ((L : ℝ) * Real.sqrt (1 - t)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; exact h
  nlinarith [Real.sqrt_nonneg (1 - t), (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

end Scales

/-! ### (7.33), (7.34), (7.39), (7.40): the hierarchy with `S^{(B)} → S^{(B)}_{GUE}` -/

section Hierarchy

variable (L : ℕ) [NeZero L]

/-- The polarized right side of the primitive equation of the GUE phase ((7.33) with independent
left and right factors): `W² ∑_{1≤k<l≤n} ∑_{a,b} K(G^{(a),L}_{k,l}) (S^{(B)}_{GUE})_{ab}
K'(G^{(b),R}_{k,l})`, `(S^{(B)}_{GUE})_{ab} = 1/L²`. -/
def primBilGUE (W : ℕ) (K K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)

/-- **(7.33)**: the right side of the primitive equation of the GUE phase. -/
def primRhsGUE (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  primBilGUE L W K K I

theorem primBilGUE_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBilGUE L W (K₁ + K₂) K' I = primBilGUE L W K₁ K' I + primBilGUE L W K₂ K' I := by
  simp only [primBilGUE, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBilGUE_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primBilGUE L W K (K₁ + K₂) I = primBilGUE L W K K₁ I + primBilGUE L W K K₂ I := by
  simp only [primBilGUE, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **The GUE-phase version of (5.12)/(5.13)**. -/
theorem primRhsGUE_sub (W : ℕ) (Lf K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) :
    primRhsGUE L W Lf I - primRhsGUE L W K I
      = primBilGUE L W K (Lf - K) I + primBilGUE L W (Lf - K) K I
        + primBilGUE L W (Lf - K) (Lf - K) I := by
  have hLf : Lf = K + (Lf - K) := by funext x; simp
  have h1 : primRhsGUE L W Lf I = primBilGUE L W (K + (Lf - K)) (K + (Lf - K)) I := by
    rw [primRhsGUE, ← hLf]
  rw [h1, primBilGUE_add_left, primBilGUE_add_right, primBilGUE_add_right, primRhsGUE]
  ring

private theorem GUEPhaseBootstrap_two_le_length_cutGlueL (I : LoopIdx (Z2 L)) (a : Z2 L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem GUEPhaseBootstrap_two_le_length_cutGlueR (I : LoopIdx (Z2 L)) (b : Z2 L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

private theorem GUEPhaseBootstrap_length_cutGlueL_le (I : LoopIdx (Z2 L)) (a : Z2 L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l a).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem GUEPhaseBootstrap_length_cutGlueR_le (I : LoopIdx (Z2 L)) (b : Z2 L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueR k l b).length ≤ I.length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

/-- **The power counting behind (7.34), (7.39), (7.40)** (`d = 2`): if `|K J| ≤ B(|J|)` and
`|K' J| ≤ B'(|J|)` for all well-formed loops `J` of length `2 ≤ |J| ≤ n = |I|`, then
`|W² ∑_{k<l} ∑_{a,b} K(G^{L}) (S_{GUE})_{ab} K'(G^{R})| ≤ n² N ∑_{2≤j≤n} B(n-j+2) B'(j)`,
`N = (W L)²`.  Since `S^{(B)}_{GUE}` is the constant `1/L²`, the double sum over `a, b ∈ Z_L²`
costs exactly a factor `L⁴ · L⁻² = L²`; with the prefactor `W²` this is `N = (W L)²`. -/
theorem norm_primBilGUE_le (W : ℕ) (K K' : LoopIdx (Z2 L) → ℂ) (B B' : ℕ → ℝ)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length)
    (hB' : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K' J‖ ≤ B' J.length)
    (hB0 : ∀ j, 0 ≤ B j) (hB0' : ∀ j, 0 ≤ B' j) :
    ‖primBilGUE L W K K' I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ 2 : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B' j := by
  set n := I.length with hn
  set Sm := ∑ j ∈ Icc 2 n, B (n - j + 2) * B' j with hSm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0' _)
  -- one pair `(k, l)`
  have hpair : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n,
      ‖∑ a : Z2 L, ∑ b : Z2 L, K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)‖
        ≤ (L : ℝ) ^ 2 * Sm := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL : ∀ a : Z2 L, (I.cutGlueL k l a).length = n - (l - k + 1) + 2 := by
      intro a; rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega
    have hlenR : ∀ b : Z2 L, (I.cutGlueR k l b).length = l - k + 1 := by
      intro b; rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]
    have hBL : ∀ a : Z2 L, ‖K (I.cutGlueL k l a)‖ ≤ B (n - (l - k + 1) + 2) := by
      intro a
      rw [← hlenL a]
      exact hB _ (LoopIdx.WF.cutGlueL hI a hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_two_le_length_cutGlueL L I a hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_length_cutGlueL_le L I a hk.1 hl.1 hl.2)
    have hBR : ∀ b : Z2 L, ‖K' (I.cutGlueR k l b)‖ ≤ B' (l - k + 1) := by
      intro b
      rw [← hlenR b]
      exact hB' _ (LoopIdx.WF.cutGlueR hI b hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_two_le_length_cutGlueR L I b hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_length_cutGlueR_le L I b hk.1 hl.1 hl.2)
    have hj : l - k + 1 ∈ Icc 2 n := by rw [Finset.mem_Icc]; omega
    have hterm : B (n - (l - k + 1) + 2) * B' (l - k + 1) ≤ Sm :=
      Finset.single_le_sum (f := fun j => B (n - j + 2) * B' j)
        (fun j _ => mul_nonneg (hB0 _) (hB0' _)) hj
    have hSB : ‖((L : ℂ) ^ 2)⁻¹‖ = ((L : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]
    calc _ ≤ ∑ a : Z2 L, ∑ b : Z2 L,
          ‖K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : Z2 L, ∑ _b : Z2 L,
          B (n - (l - k + 1) + 2) * ((L : ℝ) ^ 2)⁻¹ * B' (l - k + 1) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul, SBgue_apply, hSB]
          have hLi : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := inv_nonneg.2 hL2.le
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hBL a) hLi) (hBR b) (norm_nonneg _)
            (mul_nonneg (hB0 _) hLi)
      _ = (L : ℝ) ^ 2 * (B (n - (l - k + 1) + 2) * B' (l - k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
            nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ (L : ℝ) ^ 2 * Sm := mul_le_mul_of_nonneg_left hterm hL2.le
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  calc ‖primBilGUE L W K K' I‖
      ≤ (W : ℝ) ^ 2 * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, (L : ℝ) ^ 2 * Sm := by
        rw [primBilGUE, norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) ^ 2 * ∑ _k ∈ Icc 1 n, (n : ℝ) * ((L : ℝ) ^ 2 * Sm) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
        exact mul_le_mul_of_nonneg_right this (mul_nonneg hL2.le hSm0)
    _ = (n : ℝ) ^ 2 * (((W * L) ^ 2 : ℕ) : ℝ) * Sm := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

/-- **(7.34)**: `|d/dt K_{t,σ,a}| ≤ n² N ∑_{2≤k≤n} max K^{(k)} · max K^{(n-k+2)}`, with the maxima
written as bounds `B` (`N = (W L)²`). -/
theorem norm_primRhsGUE_le (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (B : ℕ → ℝ)
    (I : LoopIdx (Z2 L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length)
    (hB0 : ∀ j, 0 ≤ B j) :
    ‖primRhsGUE L W K I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ 2 : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B j :=
  norm_primBilGUE_le L W K K B B I hI hB hB hB0 hB0

end Hierarchy

/-! ### (7.35), (7.36): the continuity bootstrap for `K` -/

section KBootstrap

open Set

/-- `∑_{2≤j≤m} (c x^{m-j+1}) (c x^{j-1}) = (m-1) c² x^m`. -/
theorem sum_pow_mul_pow (c x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 2 m, (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = ((m - 1 : ℕ) : ℝ) * c ^ 2 * x ^ m := by
  have hterm : ∀ j ∈ Finset.Icc 2 m,
      (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1)) = c ^ 2 * x ^ m := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have he : m - j + 2 - 1 + (j - 1) = m := by omega
    rw [show (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = c ^ 2 * (x ^ (m - j + 2 - 1) * x ^ (j - 1)) by ring, ← pow_add, he]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : m + 1 - 2 = m - 1 := by omega
  rw [this]; ring

/-- **(7.35) ⟹ (7.36), deterministic core.**  Let `k_i(t)` (`i ∈ S`, finitely many; `i` stands
for `(σ, a)` of a loop of length `|i| ∈ [2, n]`) solve `d/dt k_i = d_i` on `[t₁, t₀]`, where the
drift obeys the power counting (7.34): whenever `|k_j(t)| ≤ B(|j|)` for all `j`,
`|d_i(t)| ≤ C N ∑_{2≤j≤|i|} B(|i|-j+2) B(j)`.  Let `λ_t = N η_t` be positive, continuous and
non-increasing, and let (7.30) hold in the form `N (t - t₁) ≤ ε λ_t`.  If initially
`|k_i(t₁)| ≤ A λ_{t₁}^{-|i|+1}` ((7.32)) and `4 C n A ε < 1`, then
`|k_i(t)| < 2 A λ_t^{-|i|+1}` on `[t₁, t₀]` ((7.36)).  The integration of (7.34) to (7.35) is
the mean value inequality; the continuity argument is `continuity_argument`. -/
theorem K_bootstrap {ι : Type*} {S : Set ι} (hS : S.Finite) (len : ι → ℕ) {n : ℕ}
    (hlen : ∀ i ∈ S, 2 ≤ len i ∧ len i ≤ n) (k d : ℝ → ι → ℂ) {t1 t0 C N A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hderiv : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, HasDerivWithinAt (fun s => k s i) (d t i) (Icc t1 t0) t)
    (hd : ∀ t ∈ Icc t1 t0, ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → (∀ j ∈ S, ‖k t j‖ ≤ B (len j)) →
      ∀ i ∈ S, ‖d t i‖ ≤ C * N * ∑ j ∈ Finset.Icc 2 (len i), B (len i - j + 2) * B j)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hA : 0 < A)
    (hinit : ∀ i ∈ S, ‖k t1 i‖ ≤ A * (lam t1)⁻¹ ^ (len i - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, N * (t - t1) ≤ ε * lam t) (hε : 4 * C * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1) := by
  have ht1' : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
  have hkc : ∀ i ∈ S, ContinuousOn (fun t => ‖k t i‖) (Icc t1 t0) := fun i hi =>
    ContinuousOn.norm (f := fun s => k s i) fun t ht => (hderiv t ht i hi).continuousWithinAt
  have hgc : ∀ i ∈ S, ContinuousOn (fun t => 2 * A * (lam t)⁻¹ ^ (len i - 1)) (Icc t1 t0) :=
    fun i _ => continuousOn_const.mul
      ((hlamc.inv₀ fun t ht => (hlam t ht).ne').pow _)
  refine continuity_argument hS hkc hgc (fun i hi => ?_) (fun t ht hprev i hi => ?_)
  · have hpos : 0 < A * (lam t1)⁻¹ ^ (len i - 1) :=
      mul_pos hA (pow_pos (inv_pos.2 (hlam t1 ht1')) _)
    have := hinit i hi
    change ‖k t1 i‖ < 2 * A * (lam t1)⁻¹ ^ (len i - 1)
    linarith
  -- the improvement step at time `t`
  show ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1)
  have hlt := hlam t ht
  set x := (lam t)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hlt
  set m := len i with hm
  obtain ⟨hm2, hmn⟩ := hlen i hi
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  -- bounds on `[t₁, t]` in terms of `λ_t`
  set Bt : ℕ → ℝ := fun j => 2 * A * x ^ (j - 1) with hBt
  have hBt0 : ∀ j, 0 ≤ Bt j := fun j => by positivity
  have hkB : ∀ u ∈ Icc t1 t, ∀ j ∈ S, ‖k u j‖ ≤ Bt (len j) := by
    intro u hu j hj
    have hu0 := hsub hu
    have h1 : ‖k u j‖ ≤ 2 * A * (lam u)⁻¹ ^ (len j - 1) := hprev u hu j hj
    have hxu : (lam u)⁻¹ ≤ x := inv_anti₀ hlt (hanti u hu0 t ht hu.2)
    refine h1.trans ?_
    simp only [hBt]
    gcongr
    exact (inv_pos.2 (hlam u hu0)).le
  -- the drift bound on `[t₁, t]`
  have hdB : ∀ u ∈ Ico t1 t, ‖d u i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) := by
    intro u hu
    have hu' : u ∈ Icc t1 t := Ico_subset_Icc_self hu
    have h := hd u (hsub hu') Bt hBt0 (fun j hj => hkB u hu' j hj) i hi
    rw [← sum_pow_mul_pow]
    exact h
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => k s i) (fun u hu => (hderiv u (hsub hu) i hi).mono hsub) hdB t ⟨ht1t, le_rfl⟩
  -- `λ_{t₁}^{-1} ≤ λ_t^{-1}`
  have hx1 : (lam t1)⁻¹ ≤ x := inv_anti₀ hlt (hanti t1 ht1' t ht ht1t)
  have hinit' : ‖k t1 i‖ ≤ A * x ^ (m - 1) := by
    refine (hinit i hi).trans ?_
    gcongr
    exact (inv_pos.2 (hlam t1 ht1')).le
  -- `C N (m-1)(2A)² x^m (t - t₁) ≤ 4 C n A² ε x^{m-1}`
  have hxm : x ^ m * lam t = x ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    rw [this, pow_succ, Nat.add_sub_cancel, mul_assoc, hx, inv_mul_cancel₀ hlt.ne', mul_one]
  have hkey : C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
      ≤ 4 * C * n * A * ε * (A * x ^ (m - 1)) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le m 1).trans hmn
    have hsm := hsmall t ht
    have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN (by linarith)
    calc C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
        = C * ((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m * (N * (t - t1)) := by ring
      _ ≤ C * n * (2 * A) ^ 2 * x ^ m * (ε * lam t) := by gcongr
      _ = 4 * C * n * A * ε * (A * (x ^ m * lam t)) := by ring
      _ = 4 * C * n * A * ε * (A * x ^ (m - 1)) := by rw [hxm]
  have hmvt' :
      ‖k t i‖ ≤ ‖k t1 i‖ + C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) := by
    have := norm_sub_norm_le (k t i) (k t1 i)
    have h2 : ‖k t i - k t1 i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) :=
      hmvt
    linarith
  have hpos : 0 < A * x ^ (m - 1) := mul_pos hA (pow_pos hx0 _)
  nlinarith

/-- Well-formed loop indices of bounded length form a finite set. -/
theorem finite_loopIdx (L : ℕ) [NeZero L] (n : ℕ) :
    {I : LoopIdx (Z2 L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}.Finite := by
  refine (((List.finite_length_le Bool n).prod (List.finite_length_le (Z2 L) n)).image
    (fun p : List Bool × List (Z2 L) => (⟨p.1, p.2⟩ : LoopIdx (Z2 L)))).subset ?_
  rintro ⟨σ, a⟩ ⟨hWF, -, hn⟩
  simp only [LoopIdx.WF, LoopIdx.length] at hWF hn
  exact ⟨(σ, a), ⟨show σ.length ≤ n by omega, show a.length ≤ n from hn⟩, rfl⟩

/-- **(7.36)** for the primitive loops of the GUE phase (`d = 2`): if `K_t` solves the GUE-phase
primitive equation (7.33) (`primRhsGUE`) on `[t₁, t₀]` for all loops of length `2 ≤ |I| ≤ n`,
`|K_{t₁, I}| ≤ A (N η_{t₁})^{-|I|+1}` ((7.32)), and (7.30) holds as `N (t - t₁) ≤ ε N η_t`
(`N = (W L)²`), with `4 n³ A ε < 1`, then `|K_{t, I}| < 2 A (N η_t)^{-|I|+1}` on `[t₁, t₀]`. -/
theorem eq736 (L W : ℕ) [NeZero L] (Kt : ℝ → LoopIdx (Z2 L) → ℂ) {n : ℕ} {t1 t0 A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hK : ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length → I.length ≤ n →
      HasDerivWithinAt (fun s => Kt s I) (primRhsGUE L W (Kt t) I) (Icc t1 t0) t)
    (hA : 0 < A)
    (hinit : ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t1 I‖ ≤ A * (lam t1)⁻¹ ^ (I.length - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, (((W * L) ^ 2 : ℕ) : ℝ) * (t - t1) ≤ ε * lam t)
    (hε : 4 * ((n : ℝ) ^ 2) * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t I‖ < 2 * A * (lam t)⁻¹ ^ (I.length - 1) := by
  set S := {I : LoopIdx (Z2 L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n} with hSdef
  have hS : S.Finite := finite_loopIdx L n
  have key := K_bootstrap (S := S) hS LoopIdx.length (n := n)
    (fun I hI => ⟨hI.2.1, hI.2.2⟩) Kt (fun t I => primRhsGUE L W (Kt t) I)
    (C := (n : ℝ) ^ 2) (N := (((W * L) ^ 2 : ℕ) : ℝ)) ht10 lam hlam hanti hlamc
    (fun t ht I hI => hK t ht I hI.1 hI.2.1 hI.2.2) ?_ (by positivity) (by positivity) hA
    (fun I hI => hinit I hI.1 hI.2.1 hI.2.2) hsmall hε
  · intro t ht I hWF h2 hn
    exact key t ht I ⟨hWF, h2, hn⟩
  · intro t _ B hB0 hB I hI
    have h := norm_primRhsGUE_le L W (Kt t) B I hI.1
      (fun J hJ h2 hJI => hB J ⟨hJ, h2, hJI.trans hI.2.2⟩) hB0
    refine h.trans ?_
    have hsum : 0 ≤ ∑ j ∈ Finset.Icc 2 I.length, B (I.length - j + 2) * B j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0 _)
    have hlen : (I.length : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (I.length : ℝ) ≤ n := by exact_mod_cast hI.2.2
      gcongr
    gcongr

/-- Well-formed loop indices of length `2 ≤ |I| ≤ n` (the `(σ, a)` of the maxima in (7.27),
(7.28), (7.36)). -/
abbrev LoopSet (L : ℕ) (n : ℕ) : Type :=
  {I : LoopIdx (Z2 L) // I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}

/-- `4 n³ N^{τ'} N^{-τ_U} < 1` for large `N`, if `τ' < τ_U`. -/
theorem eventually_small {n : ℕ} {τ' τU : ℝ} (h : τ' < τU) :
    ∀ᶠ N : ℕ in atTop, 4 * ((n : ℝ) ^ 2) * n * (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) < 1 := by
  filter_upwards [eventually_le_rpow (8 * (n : ℝ) ^ 3 + 1) (sub_pos.2 h),
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (τU - τ') := Real.rpow_pos_of_pos hN0 _
  have he : (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) = ((N : ℝ) ^ (τU - τ'))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; ring_nf
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  rw [mul_assoc, he, show 4 * (n : ℝ) ^ 2 * n = 4 * (n : ℝ) ^ 3 by ring, ← div_eq_mul_inv,
    div_lt_one hpos]
  linarith

end KBootstrap

/-! ### (7.45) ⟹ (7.27) and (7.46) ⟹ (7.28): the pathwise bootstrap for `L` -/

section LBootstrap

open Set

/-- `sup_{u ∈ [a, b]} g(u)` (a conditionally complete supremum; only upper bounds are used). -/
def supOn (g : ℝ → ℝ) (a b : ℝ) : ℝ := ⨆ u : Icc a b, g u

theorem supOn_le {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (h : ∀ u ∈ Icc a b, g u ≤ c) :
    supOn g a b ≤ c := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  exact ciSup_le fun u => h u u.2

/-- (7.45) with the E^{(G)} term `N L₂ L_n` (from (4.3) + (5.117), no fluctuation averaging). -/
def rhs745G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Lm 2 u * Lm n u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t

/-- (7.46) with the E^{(G)} term `N D₁ L_{n+1}` (the `1`-loop tracked in the bootstrap). -/
def rhs746G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Dm 1 u * Lm (n + 1) u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) *
        Real.sqrt (Lm (2 * n) u)) t1 t

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- The first line of (7.45)/(7.46) under bounds `D_j(u) ≤ c x^{j-1+e}` (`x = (Nη_t)^{-1} ≤ 1`,
`e ∈ {0, 1}`): `sup_u ∑_k ((Nη_u)^{-k+1} + D_k) D_{n-k+2} ≤ n (1 + c) c x^{n+e}`. -/
theorem supOn_line1_le {Dm : ℕ → ℝ → ℝ} {n : ℕ} {t c x : ℝ} (e : ℕ) (he : e ≤ 1)
    (ht1t : t1 ≤ t) (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x)
    (hD : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n → 0 ≤ Dm j u ∧ Dm j u ≤ c * x ^ (j - 1 + e)) :
    supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
      ≤ n * ((1 + c) * c * x ^ (n + e)) := by
  refine supOn_le ht1t fun u hu => ?_
  have hterm : ∀ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
      ≤ (1 + c) * c * x ^ (n + e) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hDk0, hDk⟩ := hD u hu k hk.1 hk.2
    obtain ⟨hDn0, hDn⟩ := hD u hu (n - k + 2) (by omega) (by omega)
    have h1 : (N * η u)⁻¹ ^ (k - 1) ≤ x ^ (k - 1) := pow_le_pow_left₀ (hxu u hu).1 (hxu u hu).2 _
    have h2 : x ^ (k - 1 + e) ≤ x ^ (k - 1) := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h3 : (N * η u)⁻¹ ^ (k - 1) + Dm k u ≤ (1 + c) * x ^ (k - 1) := by nlinarith
    have hexp : k - 1 + (n - k + 2 - 1 + e) = n + e := by omega
    calc ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
        ≤ ((1 + c) * x ^ (k - 1)) * (c * x ^ (n - k + 2 - 1 + e)) :=
          mul_le_mul h3 hDn hDn0 (by positivity)
      _ = (1 + c) * c * x ^ (n + e) := by rw [← hexp, pow_add]; ring
  calc _ ≤ ∑ _k ∈ Finset.Icc 2 n, (1 + c) * c * x ^ (n + e) := Finset.sum_le_sum hterm
    _ = ((n + 1 - 2 : ℕ) : ℝ) * ((1 + c) * c * x ^ (n + e)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ n * ((1 + c) * c * x ^ (n + e)) := by
        gcongr
        exact_mod_cast (by omega : n + 1 - 2 ≤ n)

/-- `N(t - t₁) · y ≤ ε x^{-1} y` from (7.30) in the form `t - t₁ ≤ ε η_t`, `x = (Nη_t)^{-1}`. -/
theorem mul_le_of_eq730 {t ε y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) (hsm : t - t1 ≤ ε * η t) :
    N * (t - t1) * y ≤ ε * ((N * η t)⁻¹)⁻¹ * y := by
  rw [inv_inv]
  have : N * (t - t1) ≤ ε * (N * η t) := by nlinarith
  exact mul_le_mul_of_nonneg_right this hy

/-- The martingale line: `|t - t₁|^{1/2} (N^{-1} η_t^{-2})^{1/2} = (ε (Nη_t)^{-1})^{1/2}` at most,
under (7.30) `t - t₁ ≤ ε η_t`. -/
theorem sqrt_mul_sqrt_le {t ε : ℝ} (hN : 0 < N) (hηt : 0 < η t) (ht1t : t1 ≤ t)
    (hsm : t - t1 ≤ ε * η t) :
    Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) ≤ Real.sqrt (ε * (N * η t)⁻¹) := by
  rw [← Real.sqrt_mul (by linarith)]
  refine Real.sqrt_le_sqrt ?_
  have h0 : 0 ≤ N⁻¹ * (η t)⁻¹ ^ 2 := by positivity
  calc (t - t1) * (N⁻¹ * (η t)⁻¹ ^ 2) ≤ ε * η t * (N⁻¹ * (η t)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hsm h0
    _ = ε * (N * η t)⁻¹ := by field_simp

/-- `sup_{[a,b]} g ≥ 0` for `g ≥ 0` on `[a, b]`. -/
theorem supOn_nonneg {g : ℝ → ℝ} {a b : ℝ} (h : ∀ u ∈ Icc a b, 0 ≤ g u) : 0 ≤ supOn g a b :=
  Real.iSup_nonneg fun u => h u u.2

/-- `x^{-1} x^n = x^{n-1}` for `n ≥ 1`. -/
theorem inv_mul_pow {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

end LBootstrap

/-! ### (7.27), (7.28) as `≺` statements: helpers -/

section Domination

open Set MeasureTheory

/-- `N^a ≤ ρ` for large `N`, if `a < 0`, `ρ > 0`. -/
theorem eventually_rpow_le_of_neg {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ρ := by
  filter_upwards [eventually_le_rpow ρ⁻¹ (neg_pos.2 ha), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hN0 _
  have e : (N : ℝ) ^ a = ((N : ℝ) ^ (-a))⁻¹ := by
    rw [← Real.rpow_neg hN0.le, neg_neg]
  rw [e]
  calc ((N : ℝ) ^ (-a))⁻¹ ≤ (ρ⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hρ) hN
    _ = ρ := inv_inv ρ

end Domination

end RBM.Univ.GUEPhase
