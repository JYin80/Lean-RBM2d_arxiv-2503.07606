/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.TreeRep
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Fintype.Vector

/-!
# Uniqueness for `(pro_dyncalK)` on `[0, 1)` (`Def_Ktza`, "unique")

Every family `K` satisfying `IsPrimitive L W (mSig E) (Set.Ico 0 1)` equals `Kcal L W E` on
loops of length `≥ 1` (`isPrimitive_eq_Kcal`).

The argument follows the one-dimensional formalization, with `ZMod L → Z2 L` and `W → W²` in
`primRhs` (so `C = W² ∑ ... `), and sums over `Z_L²`: the structure lemmas
`Unique_cutGlueR_length_eq_two`/`Unique_cutGlueL_length_eq_two`, `Unique_norm_SB_apply_le`,
`Unique_norm_mul_mul_sub_le`, `Unique_eq_on_level` and `Unique_isPrimitive_unique`.  The bound on
the `2`-loops
(a hypothesis in the one-dimensional case) is obtained here from the continuity given by
`HasDerivAt` on the compact interval `[0, t] ⊆ [0, 1)`.  Finally the family
`fun t => Kcal L W E t` is primitive by `isPrimitive_Kcal`.
-/

namespace RBM.KLoop

open Finset

/-! ## Structure of the cut operators -/

private theorem Unique_two_le_length_cutGlueL {α : Type*} (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

private theorem Unique_two_le_length_cutGlueR {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

private theorem Unique_length_cutGlueL_le {α : Type*} (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : (x.cutGlueL k l a).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

private theorem Unique_length_cutGlueR_le {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : (x.cutGlueR k l b).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

/-- If the left chain has the full length `n`, the right chain is a `2`-loop. -/
private theorem Unique_cutGlueR_length_eq_two {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueL k l a).length = x.length) : (x.cutGlueR k l b).length = 2 := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl] at h
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

/-- If the right chain has the full length `n`, the left chain is a `2`-loop. -/
private theorem Unique_cutGlueL_length_eq_two {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueR k l b).length = x.length) : (x.cutGlueL k l a).length = 2 := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl] at h
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

/-! ## Loops of length `n` as a finite type -/

/-- Loops of length `n`, as a finite type. -/
private abbrev Unique_LoopVec (L n : ℕ) := List.Vector Bool n × List.Vector (Z2 L) n

/-- The loop with given charges and labels. -/
private def Unique_toLoop (L : ℕ) {n : ℕ} (p : Unique_LoopVec L n) : LoopIdx (Z2 L) :=
  ⟨p.1.1, p.2.1⟩

private theorem Unique_toLoop_wf (L : ℕ) {n : ℕ} (p : Unique_LoopVec L n) :
    (Unique_toLoop L p).WF := by
  change p.1.1.length = p.2.1.length
  rw [p.1.2, p.2.2]

private theorem Unique_toLoop_length (L : ℕ) {n : ℕ} (p : Unique_LoopVec L n) :
    (Unique_toLoop L p).length = n := p.2.2

private theorem Unique_exists_toLoop (L : ℕ) {n : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF)
    (hJn : J.length = n) : ∃ p : Unique_LoopVec L n, Unique_toLoop L p = J :=
  ⟨(⟨J.σ, hJ.trans hJn⟩, ⟨J.a, hJn⟩), rfl⟩

private theorem Unique_norm_SB_apply_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) (a b : Z2 L) :
    ‖SB L a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB L a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row L hL a] at h
  exact_mod_cast h

/-- The difference of one term of `(pro_dyncalK)`:
`X s Y - X' s Y' = (X - X') s Y + X' s (Y - Y')`. -/
private theorem Unique_norm_mul_mul_sub_le {X X' Y Y' s : ℂ} {R d : ℝ} (hs : ‖s‖ ≤ 1)
    (h1 : ‖X - X'‖ * ‖Y‖ ≤ R * d) (h2 : ‖X'‖ * ‖Y - Y'‖ ≤ R * d) :
    ‖X * s * Y - X' * s * Y'‖ ≤ 2 * (R * d) := by
  have e : X * s * Y - X' * s * Y' = (X - X') * s * Y + X' * s * (Y - Y') := by ring
  have e1 : ‖(X - X') * s * Y‖ ≤ R * d := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg (X - X')) (norm_nonneg Y))
    nlinarith
  have e2 : ‖X' * s * (Y - Y')‖ ≤ R * d := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg X') (norm_nonneg (Y - Y')))
    nlinarith
  rw [e]
  linarith [norm_add_le ((X - X') * s * Y) (X' * s * (Y - Y'))]

/-! ## One step of the induction and two-family uniqueness -/

/-- One step of the induction: two families satisfying `(pro_dyncalK)` on loops of length `n`
on `[0, T₀]`, whose `2`-loops are bounded by `R`, which agree on all loops of length `< n`
and at `t = 0` on loops of length `n`, agree on loops of length `n`. -/
private theorem Unique_eq_on_level (L : ℕ) [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    (K K' : ℝ → LoopIdx (Z2 L) → ℂ) (T₀ R : ℝ)
    (n : ℕ) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = n →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t)
    (hK' : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = n →
      HasDerivAt (fun s => K' s I) (primRhs L W (K' t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      I.length < n → K t I = K' t I)
    (h0 : ∀ I : LoopIdx (Z2 L), I.WF → I.length = n → K 0 I = K' 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = n → K t I = K' t I := by
  let D : ℝ → Unique_LoopVec L n → ℂ := fun t p =>
    K t (Unique_toLoop L p) - K' t (Unique_toLoop L p)
  let D' : ℝ → Unique_LoopVec L n → ℂ := fun t p =>
    primRhs L W (K t) (Unique_toLoop L p) - primRhs L W (K' t) (Unique_toLoop L p)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ (Unique_toLoop_wf L p) (Unique_toLoop_length L p)).sub
        (hK' t ht _ (Unique_toLoop_wf L p) (Unique_toLoop_length L p))
  let C : ℝ := (W : ℝ) ^ 2 *
    ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * R
  have hC : 0 ≤ C := by
    refine mul_nonneg (pow_nonneg (Nat.cast_nonneg W) 2) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
        positivity)
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have hdiff : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t J - K' t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := Unique_exists_toLoop L J hJ heq
        exact norm_le_pi_norm (D t) p
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    set I := Unique_toLoop L p with hIdef
    have hI : I.WF := Unique_toLoop_wf L p
    have hIn : I.length = n := Unique_toLoop_length L p
    have hterm : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n, ∀ a b : Z2 L,
        ‖K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      have hk1 : 1 ≤ k := hk.1
      have hkl : k < l := hl.1
      have hlI : l ≤ I.length := hIn ▸ hl.2
      have hWL : (I.cutGlueL k l a).WF := LoopIdx.WF.cutGlueL hI a hk1 hkl hlI
      have hWR : (I.cutGlueR k l b).WF := LoopIdx.WF.cutGlueR hI b hk1 hkl hlI
      have h2L := Unique_two_le_length_cutGlueL I a hk1 hkl hlI
      have h2R := Unique_two_le_length_cutGlueR I b hk1 hkl hlI
      have hLle : (I.cutGlueL k l a).length ≤ n :=
        hIn ▸ Unique_length_cutGlueL_le I a hk1 hkl hlI
      have hRle : (I.cutGlueR k l b).length ≤ n :=
        hIn ▸ Unique_length_cutGlueR_le I b hk1 hkl hlI
      have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
      refine Unique_norm_mul_mul_sub_le (Unique_norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have h2 := Unique_cutGlueR_length_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hY := (hR t ht' _ hWR h2).1
          have hX := hdiff _ hWL h2L hLle
          rw [mul_comm R]
          exact mul_le_mul hX hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have h2 := Unique_cutGlueL_length_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hX := (hR t ht' _ hWL h2).2
          have hY := hdiff _ hWR h2R hRle
          exact mul_le_mul hX hY (norm_nonneg _) hR0
    have e : D' t p = (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ a : Z2 L, ∑ b : Z2 L,
        (K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b)) := by
      simp only [D', primRhs, ← hIdef, hIn, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [e, norm_mul, norm_pow, Complex.norm_natCast]
    have hsum : ‖∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ a : Z2 L, ∑ b : Z2 L,
        (K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b))‖
        ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * (R * ‖D t‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact hterm k hk l hl a b
    calc (W : ℝ) ^ 2 * ‖_‖ ≤ (W : ℝ) ^ 2 * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : Z2 L,
          ∑ _b : Z2 L, 2 * (R * ‖D t‖) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg W) 2)
      _ = C * ‖D t‖ := by
        simp only [C, Finset.sum_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2
      (h0 _ (Unique_toLoop_wf L p) (Unique_toLoop_length L p))) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := Unique_exists_toLoop L I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- Uniqueness for two primitive families on `[0, T₀]` whose `2`-loops stay bounded: they agree
on every loop of length `≥ 2`. -/
private theorem Unique_isPrimitive_unique (L : ℕ) [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    (m : Bool → ℂ) {T : Set ℝ}
    {K K' : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W m T K)
    (hK' : IsPrimitive L W m T K') {T₀ R : ℝ} (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length → K t I = K' t I := by
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      I.length = n → K t I = K' t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine Unique_eq_on_level L hL W K K' T₀ R n hR0
        (fun s hs J hJ hJn => hK.1 s (hT hs) J hJ (hJn ▸ hn))
        (fun s hs J hJ hJn => hK'.1 s (hT hs) J hJ (hJn ▸ hn)) hR ?_ ?_ t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 J hJ (hJn ▸ hn), hK'.2.1 J hJ (hJn ▸ hn)]
  exact fun t ht I hI h2 => main _ t ht I hI h2 rfl

/-! ## The bound on `2`-loops from continuity -/

/-- A primitive family has bounded `2`-loops on any `[0, T₀] ⊆ T`: each coordinate is
differentiable, hence continuous, on the compact interval, and there are finitely many
`2`-loops. -/
private theorem Unique_two_loop_bound (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ C := by
  let f : ℝ → Unique_LoopVec L 2 → ℂ := fun s p => K s (Unique_toLoop L p)
  have hf : ContinuousOn f (Set.Icc 0 T₀) := by
    refine continuousOn_pi.2 fun p s hs => ?_
    have := hK.1 s (hT hs) (Unique_toLoop L p) (Unique_toLoop_wf L p)
      (by rw [Unique_toLoop_length L p])
    exact this.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨C, fun t ht I hI hI2 => ?_⟩
  obtain ⟨p, rfl⟩ := Unique_exists_toLoop L I hI hI2
  exact (norm_le_pi_norm (f t) p).trans (hC t ht)

/-! ## The uniqueness statement -/

/-- Every primitive family on `[0, 1)` equals `Kcal` on well-formed loops
of length `≥ 1`.  The length-`1` case is the third clause of `IsPrimitive` (for `K` and, by
`isPrimitive_Kcal`, for `Kcal`); the length-`≥ 2` case is the two-family uniqueness with the
`2`-loops bounded on `[0, t]` by continuity. -/
theorem isPrimitive_eq_Kcal :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 →
    ∀ K : ℝ → LoopIdx (Z2 L) → ℂ, IsPrimitive L W (mSig E) (Set.Ico 0 1) K →
      ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Z2 L), I.WF → 1 ≤ I.length →
        K t I = Kcal L W E t I := by
  intro L W _ hL hW E hE K hK t ht I hI hI1
  have hKc := isPrimitive_Kcal L W hL hW E hE
  rcases hI1.lt_or_eq with h2 | h1
  · have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    obtain ⟨C, hC⟩ := Unique_two_loop_bound L W (mSig E) hK hT
    obtain ⟨C', hC'⟩ := Unique_two_loop_bound L W (mSig E) hKc hT
    refine Unique_isPrimitive_unique L hL W (mSig E) hK hKc hT
      (R := max 0 (max C C')) (le_max_left _ _) (fun s hs J hJ hJ2 => ?_) t
      ⟨ht.1, le_rfl⟩ I hI h2
    exact ⟨(hC s hs J hJ hJ2).trans ((le_max_left C C').trans (le_max_right _ _)),
      (hC' s hs J hJ hJ2).trans ((le_max_right C C').trans (le_max_right _ _))⟩
  · obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := by simpa [LoopIdx.length] using h1.symm
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    rw [hK.2.2 t ht s x]
    exact (hKc.2.2 t ht s x).symm

end RBM.KLoop
