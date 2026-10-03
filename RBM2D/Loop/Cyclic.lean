/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Unique

/-!
# Rotation and translation invariance of `𝒦`

The theorems `Kcal_rotate` and `Kcal_translate`.  The proof follows the one-dimensional
formalization: `Cyclic_primRhs_split`, `Cyclic_primRhs_rot`, `Cyclic_primInit_rot`,
`Cyclic_rot_eq_on_level`, `Cyclic_isPrimitive_rot`, the cut lemmas `Cyclic_cutGlueL_rot_of_lt`,
`Cyclic_cutGlueR_rot_of_lt`, `Cyclic_cutGlueL_rot_last`, `Cyclic_cutGlueR_rot_last`,
`Cyclic_primRhs_shift` and `Cyclic_primInit_shift`, with `ZMod L → Z2 L`, `W → W²` in `primRhs`
(so `C = W² ∑ ⋯`), and sums over `Z_L²`.

* Rotation: the rotated family does not satisfy `(pro_dyncalK)` termwise, so uniqueness is
  not used; instead Grönwall on `K ∘ rot - K` by strong induction on the length (as in
  `Unique.lean`, whose private helpers are re-proved here with the prefix `Cyclic_`).
* Translation: the shifted family is again primitive, hence equals `Kcal` by
  `isPrimitive_eq_Kcal`.
-/

namespace RBM.KLoop

open Finset

/-! ## Structure of the cut operators -/

private theorem Cyclic_two_le_length_cutGlueL {α : Type*} (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

private theorem Cyclic_two_le_length_cutGlueR {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

private theorem Cyclic_length_cutGlueL_le {α : Type*} (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : (x.cutGlueL k l a).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

private theorem Cyclic_length_cutGlueR_le {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : (x.cutGlueR k l b).length ≤ x.length := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

private theorem Cyclic_cutGlueR_length_eq_two {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueL k l a).length = x.length) : (x.cutGlueR k l b).length = 2 := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl] at h
  rw [LoopIdx.length_cutGlueR x b hk hkl hl]
  omega

private theorem Cyclic_cutGlueL_length_eq_two {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueR k l b).length = x.length) : (x.cutGlueL k l a).length = 2 := by
  rw [LoopIdx.length_cutGlueR x b hk hkl hl] at h
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

/-! ## Loops of length `n` as a finite type -/

private abbrev Cyclic_LoopVec (L n : ℕ) := List.Vector Bool n × List.Vector (Z2 L) n

private def Cyclic_toLoop (L : ℕ) {n : ℕ} (p : Cyclic_LoopVec L n) : LoopIdx (Z2 L) :=
  ⟨p.1.1, p.2.1⟩

private theorem Cyclic_toLoop_wf (L : ℕ) {n : ℕ} (p : Cyclic_LoopVec L n) :
    (Cyclic_toLoop L p).WF := by
  change p.1.1.length = p.2.1.length
  rw [p.1.2, p.2.2]

private theorem Cyclic_toLoop_length (L : ℕ) {n : ℕ} (p : Cyclic_LoopVec L n) :
    (Cyclic_toLoop L p).length = n := p.2.2

private theorem Cyclic_exists_toLoop (L : ℕ) {n : ℕ} (J : LoopIdx (Z2 L)) (hJ : J.WF)
    (hJn : J.length = n) : ∃ p : Cyclic_LoopVec L n, Cyclic_toLoop L p = J :=
  ⟨(⟨J.σ, hJ.trans hJn⟩, ⟨J.a, hJn⟩), rfl⟩

private theorem Cyclic_norm_SB_apply_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) (a b : Z2 L) :
    ‖SB L a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB L a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row L hL a] at h
  exact_mod_cast h

private theorem Cyclic_norm_mul_mul_sub_le {X X' Y Y' s : ℂ} {R d : ℝ} (hs : ‖s‖ ≤ 1)
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

/-- A primitive family has bounded `2`-loops on any `[0, T₀] ⊆ T`. -/
private theorem Cyclic_two_loop_bound (L : ℕ) [NeZero L] (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ C := by
  let f : ℝ → Cyclic_LoopVec L 2 → ℂ := fun s p => K s (Cyclic_toLoop L p)
  have hf : ContinuousOn f (Set.Icc 0 T₀) := by
    refine continuousOn_pi.2 fun p s hs => ?_
    have := hK.1 s (hT hs) (Cyclic_toLoop L p) (Cyclic_toLoop_wf L p)
      (by rw [Cyclic_toLoop_length L p])
    exact this.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨C, fun t ht I hI hI2 => ?_⟩
  obtain ⟨p, rfl⟩ := Cyclic_exists_toLoop L I hI hI2
  exact (norm_le_pi_norm (f t) p).trans (hC t ht)

/-! ## Rotation: combinatorics of the cuts -/

/-- Move the first edge to the end. -/
private def Cyclic_rot {α : Type*} (x : LoopIdx α) : LoopIdx α := ⟨x.σ.rotate 1, x.a.rotate 1⟩

private theorem Cyclic_rot_mk_cons {α : Type*} (s : Bool) (ss : List Bool) (c : α)
    (cs : List α) :
    Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α) = ⟨ss ++ [s], cs ++ [c]⟩ := by
  simp [Cyclic_rot, List.rotate_cons_succ]

private theorem Cyclic_length_rot {α : Type*} (x : LoopIdx α) :
    (Cyclic_rot x).length = x.length := by
  simp [Cyclic_rot, LoopIdx.length, List.length_rotate]

private theorem Cyclic_WF_rot {α : Type*} {x : LoopIdx α} (hx : x.WF) : (Cyclic_rot x).WF := by
  simpa [LoopIdx.WF, Cyclic_rot, List.length_rotate] using hx

section RotCuts

variable {α : Type*} (s : Bool) (ss : List Bool) (c : α) (cs : List α) (b : α) {k l : ℕ}

private theorem Cyclic_cutGlueL_rot_of_lt (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ cs.length) :
    (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueL k l b
      = Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueL (k + 1) (l + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [Cyclic_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, Nat.add_sub_cancel, List.take_succ_cons, List.drop_succ_cons,
    List.cons_append]
  rw [Cyclic_rot_mk_cons]
  congr 1
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.append_assoc]
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    simp

private theorem Cyclic_cutGlueR_rot_of_lt (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ cs.length) :
    (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueR k l b
      = (⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueR (k + 1) (l + 1) b := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Cyclic_rot_mk_cons]
  simp only [LoopIdx.cutGlueR, Nat.add_sub_cancel, List.drop_succ_cons]
  rw [show l + 1 - (k + 1 + 1) = l - (k + 1) by omega,
    List.drop_append_of_le_length (by omega : k ≤ ss.length),
    List.drop_append_of_le_length (by omega : k ≤ cs.length),
    List.take_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega)]

private theorem Cyclic_cutGlueL_rot_last (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkn : k ≤ cs.length) :
    (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueL k (cs.length + 1) b
      = Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueR 1 (k + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Cyclic_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, LoopIdx.cutGlueR, Nat.add_sub_cancel, Nat.sub_self,
    List.drop_zero, List.take_succ_cons, List.cons_append]
  rw [Cyclic_rot_mk_cons,
    List.take_append_of_le_length (by omega : k + 1 ≤ ss.length),
    List.take_append_of_le_length (by omega : k ≤ cs.length),
    List.drop_append_of_le_length (by omega : cs.length ≤ ss.length),
    List.drop_eq_nil_of_le (by omega : ss.length ≤ cs.length), List.drop_left]
  simp

private theorem Cyclic_cutGlueR_rot_last (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkn : k ≤ cs.length) :
    (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueR k (cs.length + 1) b
      = Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueL 1 (k + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Cyclic_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, LoopIdx.cutGlueR, Nat.add_sub_cancel, Nat.sub_self,
    List.take_zero, List.drop_succ_cons, List.nil_append, List.take_succ_cons, List.take_zero,
    List.singleton_append]
  rw [Cyclic_rot_mk_cons,
    List.drop_append_of_le_length (by omega : k ≤ ss.length),
    List.drop_append_of_le_length (by omega : k ≤ cs.length),
    List.take_of_length_le (by simp; omega),
    List.take_append_of_le_length (by simp),
    List.take_of_length_le (by simp)]

end RotCuts

/-! ## Rotation: the equation at a rotated loop -/

section RotEq

variable (L : ℕ) [NeZero L]

private theorem Cyclic_primRhs_split (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L))
    (hn : 1 ≤ I.length) :
    primRhs L W K I = (W : ℂ) ^ 2 *
      (∑ l ∈ Ioc 1 I.length, ∑ a : Z2 L, ∑ b : Z2 L,
          K (I.cutGlueL 1 l a) * SB L a b * K (I.cutGlueR 1 l b)
        + ∑ k ∈ Icc 2 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
          K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)) := by
  have h : Icc 1 I.length = insert 1 (Icc 2 I.length) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [primRhs, h, sum_insert (by simp)]

/-- `(pro_dyncalK)`'s right-hand side at the rotated loop of `(s :: ss, c :: cs)`, in terms of
the cuts of the original loop. -/
private theorem Cyclic_primRhs_rot (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (s : Bool)
    (ss : List Bool) (c : Z2 L) (cs : List (Z2 L)) (hss : ss.length = cs.length) :
    primRhs L W K (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L))) = (W : ℂ) ^ 2 *
      (∑ l ∈ Ioc 1 (cs.length + 1), ∑ a : Z2 L, ∑ b : Z2 L,
          K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueL 1 l a)) * SB L a b *
            K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueR 1 l b))
        + ∑ k ∈ Icc 2 (cs.length + 1), ∑ l ∈ Ioc k (cs.length + 1), ∑ a : Z2 L, ∑ b : Z2 L,
          K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueL k l a)) * SB L a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueR k l b)) := by
  have hrlen : (Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L))).length = cs.length + 1 := by
    rw [Cyclic_length_rot]
    simp [LoopIdx.length]
  rw [primRhs, hrlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero]
  have hsplit : ∀ k ∈ Icc 1 cs.length, ∑ l ∈ Ioc k (cs.length + 1), ∑ a : Z2 L, ∑ b : Z2 L,
      K ((Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L))).cutGlueL k l a) * SB L a b *
        K ((Cyclic_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L))).cutGlueR k l b)
      = ∑ l ∈ Ioc k cs.length, ∑ a : Z2 L, ∑ b : Z2 L,
          K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueL (k + 1) (l + 1) a)) *
            SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueR (k + 1) (l + 1) b)
        + ∑ a : Z2 L, ∑ b : Z2 L,
          K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueL 1 (k + 1) a)) *
            SB L a b *
            K (Cyclic_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Z2 L)).cutGlueR 1 (k + 1) b)) := by
    intro k hk
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [Cyclic_cutGlueL_rot_of_lt s ss c cs a hss hk.1 hl.1 hl.2,
        Cyclic_cutGlueR_rot_of_lt s ss c cs b hss hk.1 hl.1 hl.2]
    · rw [sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [Cyclic_cutGlueL_rot_last s ss c cs b hss hk.1 hk.2,
        Cyclic_cutGlueR_rot_last s ss c cs a hss hk.1 hk.2,
        show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
      ring
  rw [sum_congr rfl hsplit, sum_add_distrib, add_comm]
  refine congrArg _ (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Ioc] at hx
      omega
    · intro x _
      rfl
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Icc] at hx
      omega
    · intro x _
      refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y _
        simp
      · intro y hy
        simp only [mem_Ioc] at hy
        omega
      · intro y _
        rfl

/-- The initial value of `Def_Ktza` is invariant under rotation. -/
private theorem Cyclic_primInit_rot (W : ℕ) (m : Bool → ℂ) (I : LoopIdx (Z2 L)) :
    primInit L W m (Cyclic_rot I) = primInit L W m I := by
  simp only [primInit, Cyclic_length_rot]
  congr 2
  · simp only [Cyclic_rot, List.map_rotate]
    exact (List.rotate_perm _ 1).prod_eq
  · simp only [Cyclic_rot, List.mem_rotate]

/-- One level of the induction for rotation. -/
private theorem Cyclic_rot_eq_on_level (hL : 3 ≤ L) (W : ℕ) (K : ℝ → LoopIdx (Z2 L) → ℂ)
    (T₀ R : ℝ) (n : ℕ) (hn : 2 ≤ n) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      I.length < n → K t (Cyclic_rot I) = K t I)
    (h0 : ∀ I : LoopIdx (Z2 L), I.WF → I.length = n → K 0 (Cyclic_rot I) = K 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = n →
      K t (Cyclic_rot I) = K t I := by
  let D : ℝ → Cyclic_LoopVec L n → ℂ := fun t p =>
    K t (Cyclic_rot (Cyclic_toLoop L p)) - K t (Cyclic_toLoop L p)
  let D' : ℝ → Cyclic_LoopVec L n → ℂ := fun t p =>
    primRhs L W (K t) (Cyclic_rot (Cyclic_toLoop L p)) - primRhs L W (K t) (Cyclic_toLoop L p)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ (Cyclic_WF_rot (Cyclic_toLoop_wf L p))
          (by rw [Cyclic_length_rot, Cyclic_toLoop_length L p]; exact hn)).sub
        (hK t ht _ (Cyclic_toLoop_wf L p) ((Cyclic_toLoop_length L p).symm ▸ hn))
  let C : ℝ := (W : ℝ) ^ 2 * ((∑ _l ∈ Ioc 1 n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * R)
    + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * R)
  have hC : 0 ≤ C := by
    refine mul_nonneg (pow_nonneg (Nat.cast_nonneg W) 2) (add_nonneg ?_ ?_)
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => by positivity
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have hdiff : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t (Cyclic_rot J) - K t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := Cyclic_exists_toLoop L J hJ heq
        exact norm_le_pi_norm (D t) p
    have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    have hI : (Cyclic_toLoop L p).WF := Cyclic_toLoop_wf L p
    have hIn : (Cyclic_toLoop L p).length = n := Cyclic_toLoop_length L p
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_length_pos
      (show 0 < (Cyclic_toLoop L p).a.length from by rw [← LoopIdx.length, hIn]; omega)
    obtain ⟨s, ss, hss'⟩ := List.exists_cons_of_length_pos
      (show 0 < (Cyclic_toLoop L p).σ.length from by rw [hI, ← LoopIdx.length, hIn]; omega)
    have hIeq : Cyclic_toLoop L p = ⟨s :: ss, c :: cs⟩ := LoopIdx.ext hss' hcs
    have hss : ss.length = cs.length := by
      have := hI
      rw [hIeq] at this
      simpa [LoopIdx.WF] using this
    have hn' : cs.length + 1 = n := by
      rw [← hIn, hIeq]
      simp [LoopIdx.length]
    set I : LoopIdx (Z2 L) := ⟨s :: ss, c :: cs⟩ with hIdef
    have hIWF : I.WF := hIeq ▸ hI
    have hIlen : I.length = n := hIeq ▸ hIn
    have hcut : ∀ k l, 1 ≤ k → k < l → l ≤ n → ∀ a b : Z2 L,
        (I.cutGlueL k l a).WF ∧ (I.cutGlueR k l b).WF ∧
        2 ≤ (I.cutGlueL k l a).length ∧ 2 ≤ (I.cutGlueR k l b).length ∧
        (I.cutGlueL k l a).length ≤ n ∧ (I.cutGlueR k l b).length ≤ n ∧
        ((I.cutGlueL k l a).length = n → (I.cutGlueR k l b).length = 2) ∧
        ((I.cutGlueR k l b).length = n → (I.cutGlueL k l a).length = 2) := by
      intro k l hk hkl hl a b
      have hlI : l ≤ I.length := hIlen ▸ hl
      refine ⟨LoopIdx.WF.cutGlueL hIWF a hk hkl hlI, LoopIdx.WF.cutGlueR hIWF b hk hkl hlI,
        Cyclic_two_le_length_cutGlueL I a hk hkl hlI,
        Cyclic_two_le_length_cutGlueR I b hk hkl hlI,
        hIlen ▸ Cyclic_length_cutGlueL_le I a hk hkl hlI,
        hIlen ▸ Cyclic_length_cutGlueR_le I b hk hkl hlI, fun h => ?_, fun h => ?_⟩
      · exact Cyclic_cutGlueR_length_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
      · exact Cyclic_cutGlueL_length_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
    have hA : ∀ l ∈ Ioc 1 n, ∀ a b : Z2 L,
        ‖K t (Cyclic_rot (I.cutGlueL 1 l a)) * SB L a b * K t (Cyclic_rot (I.cutGlueR 1 l b))
          - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro l hl a b
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ := hcut 1 l le_rfl hl.1 hl.2 a b
      refine Cyclic_norm_mul_mul_sub_le (Cyclic_norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ (Cyclic_WF_rot hWR)
            (by rw [Cyclic_length_rot]; exact hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have hX := hR t ht' _ hWL (hRL heq)
          exact mul_le_mul hX (hdiff _ hWR h2R hRn) (norm_nonneg _) hR0
    have hB : ∀ k ∈ Icc 2 n, ∀ l ∈ Ioc k n, ∀ a b : Z2 L,
        ‖K t (Cyclic_rot (I.cutGlueL k l a)) * SB L a b * K t (I.cutGlueR k l b)
          - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [mem_Icc] at hk
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ :=
        hcut k l (by omega) hl.1 hl.2 a b
      refine Cyclic_norm_mul_mul_sub_le (Cyclic_norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ hWR (hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rw [sub_self, norm_zero, mul_zero]
        exact hRD
    have e : D' t p = (W : ℂ) ^ 2 *
        ((∑ l ∈ Ioc 1 n, ∑ a : Z2 L, ∑ b : Z2 L,
          (K t (Cyclic_rot (I.cutGlueL 1 l a)) * SB L a b * K t (Cyclic_rot (I.cutGlueR 1 l b))
            - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : Z2 L, ∑ b : Z2 L,
          (K t (Cyclic_rot (I.cutGlueL k l a)) * SB L a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b))) := by
      simp only [D']
      rw [hIeq, Cyclic_primRhs_rot L W (K t) s ss c cs hss,
        Cyclic_primRhs_split L W (K t) _ (by rw [hIlen]; omega)]
      simp only [← hIdef]
      rw [hIlen, hn']
      simp only [Finset.sum_sub_distrib]
      ring
    rw [e, norm_mul, norm_pow, Complex.norm_natCast]
    have hsum : ‖(∑ l ∈ Ioc 1 n, ∑ a : Z2 L, ∑ b : Z2 L,
          (K t (Cyclic_rot (I.cutGlueL 1 l a)) * SB L a b * K t (Cyclic_rot (I.cutGlueR 1 l b))
            - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : Z2 L, ∑ b : Z2 L,
          (K t (Cyclic_rot (I.cutGlueL k l a)) * SB L a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b))‖
        ≤ (∑ _l ∈ Ioc 1 n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * (R * ‖D t‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hA l hl a b
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hB k hk l hl a b
    calc (W : ℝ) ^ 2 * ‖_‖ ≤ (W : ℝ) ^ 2 *
          ((∑ _l ∈ Ioc 1 n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Z2 L, ∑ _b : Z2 L, 2 * (R * ‖D t‖)) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg W) 2)
      _ = C * ‖D t‖ := by simp only [C, Finset.sum_mul, add_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2
      (h0 _ (Cyclic_toLoop_wf L p) (Cyclic_toLoop_length L p))) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := Cyclic_exists_toLoop L I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- Cyclic invariance of a primitive family with bounded `2`-loops. -/
private theorem Cyclic_isPrimitive_rot (hL : 3 ≤ L) (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (Z2 L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ R : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      K t (Cyclic_rot I) = K t I := by
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      I.length = n → K t (Cyclic_rot I) = K t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine Cyclic_rot_eq_on_level L hL W K T₀ R n hn hR0 (fun s hs => hK.1 s (hT hs)) hR ?_ ?_
        t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 _ (Cyclic_WF_rot hJ) (by rw [Cyclic_length_rot, hJn]; exact hn),
          hK.2.1 _ hJ (hJn ▸ hn), Cyclic_primInit_rot]
  intro t ht I hI h2
  exact main _ t ht I hI h2 rfl

end RotEq

/-! ## Translation -/

section Translation

variable (L : ℕ) [NeZero L]

/-- Shift every block label by `c`. -/
private def Cyclic_shift (c : Z2 L) (I : LoopIdx (Z2 L)) : LoopIdx (Z2 L) :=
  ⟨I.σ, I.a.map (· + c)⟩

omit [NeZero L] in
private theorem Cyclic_shift_WF {c : Z2 L} {I : LoopIdx (Z2 L)} (hI : I.WF) :
    (Cyclic_shift L c I).WF := by
  simpa [LoopIdx.WF, Cyclic_shift] using hI

omit [NeZero L] in
private theorem Cyclic_length_shift (c : Z2 L) (I : LoopIdx (Z2 L)) :
    (Cyclic_shift L c I).length = I.length := by
  simp [LoopIdx.length, Cyclic_shift]

omit [NeZero L] in
private theorem Cyclic_cutGlueL_shift (c : Z2 L) (I : LoopIdx (Z2 L)) (k l : ℕ) (b : Z2 L) :
    (Cyclic_shift L c I).cutGlueL k l b = Cyclic_shift L c (I.cutGlueL k l (b - c)) := by
  simp [Cyclic_shift, LoopIdx.cutGlueL, List.map_take, List.map_drop]

omit [NeZero L] in
private theorem Cyclic_cutGlueR_shift (c : Z2 L) (I : LoopIdx (Z2 L)) (k l : ℕ) (b : Z2 L) :
    (Cyclic_shift L c I).cutGlueR k l b = Cyclic_shift L c (I.cutGlueR k l (b - c)) := by
  simp [Cyclic_shift, LoopIdx.cutGlueR, List.map_take, List.map_drop]

private theorem Cyclic_primRhs_shift (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (c : Z2 L)
    (I : LoopIdx (Z2 L)) :
    primRhs L W K (Cyclic_shift L c I) = primRhs L W (fun J => K (Cyclic_shift L c J)) I := by
  rw [primRhs, primRhs, Cyclic_length_shift]
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  simp only [Cyclic_cutGlueL_shift, Cyclic_cutGlueR_shift]
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, SB_apply_add_right]

private theorem Cyclic_primInit_shift (W : ℕ) (m : Bool → ℂ) (c : Z2 L) (I : LoopIdx (Z2 L)) :
    primInit L W m (Cyclic_shift L c I) = primInit L W m I := by
  simp only [primInit, Cyclic_length_shift]
  congr 2
  simp only [Cyclic_shift, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, add_left_inj]

end Translation

/-! ## The invariance statements -/

/-- **Rotation.**  `𝒦` is invariant under moving the first edge to the end.
The length-`1` case is a syntactic equality; for length `≥ 2` see `Cyclic_isPrimitive_rot`
with the `2`-loop bound from continuity on `[0, t] ⊆ [0, 1)`. -/
theorem Kcal_rotate :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (s : Bool) (b : Z2 L) (σ : List Bool) (a : List (Z2 L)), σ.length = a.length →
      Kcal L W E t ⟨s :: σ, b :: a⟩ = Kcal L W E t ⟨σ ++ [s], a ++ [b]⟩ := by
  intro L W _ hL hW E hE t ht s b σ a hσa
  rcases a with _ | ⟨a₀, a'⟩
  · have : σ = [] := List.length_eq_zero_iff.1 (by simpa using hσa)
    subst this
    rfl
  · have hKc := isPrimitive_Kcal L W hL hW E hE
    have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    obtain ⟨C, hC⟩ := Cyclic_two_loop_bound L W (mSig E) hKc hT
    have hwf : (⟨s :: σ, b :: a₀ :: a'⟩ : LoopIdx (Z2 L)).WF := by
      simpa [LoopIdx.WF] using hσa
    have h2 : 2 ≤ (⟨s :: σ, b :: a₀ :: a'⟩ : LoopIdx (Z2 L)).length := by
      simp [LoopIdx.length]
    have := Cyclic_isPrimitive_rot L hL W (mSig E) hKc hT (le_max_left 0 C)
      (fun r hr J hJ hJ2 => (hC r hr J hJ hJ2).trans (le_max_right 0 C)) t
      ⟨ht.1, le_rfl⟩ _ hwf h2
    rw [Cyclic_rot_mk_cons] at this
    exact this.symm

/-- **Translation.**  Shifting all block labels by `c : Z_L²` leaves `𝒦`
unchanged: the shifted family is again primitive (`Cyclic_primRhs_shift`,
`Cyclic_primInit_shift`), so it equals `Kcal` by `isPrimitive_eq_Kcal`. -/
theorem Kcal_translate :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (c : Z2 L) (I : LoopIdx (Z2 L)), I.WF →
      Kcal L W E t ⟨I.σ, I.a.map (· + c)⟩ = Kcal L W E t I := by
  intro L W _ hL hW E hE t ht c I hI
  have hKc := isPrimitive_Kcal L W hL hW E hE
  by_cases h0 : I.length = 0
  · have ha : I.a = [] := List.length_eq_zero_iff.1 h0
    have hσ : I.σ = [] := List.length_eq_zero_iff.1 (hI.trans h0)
    obtain ⟨σ, a⟩ := I
    simp only at ha hσ
    subst ha hσ
    rfl
  · have hK' : IsPrimitive L W (mSig E) (Set.Ico 0 1)
        (fun r J => Kcal L W E r (Cyclic_shift L c J)) := by
      refine ⟨fun r hr J hJ h2 => ?_, fun J hJ h2 => ?_, fun r hr s a => ?_⟩
      · have := hKc.1 r hr (Cyclic_shift L c J) (Cyclic_shift_WF L hJ)
          (by rw [Cyclic_length_shift]; exact h2)
        rwa [Cyclic_primRhs_shift] at this
      · change Kcal L W E 0 (Cyclic_shift L c J) = primInit L W (mSig E) J
        exact (hKc.2.1 (Cyclic_shift L c J) (Cyclic_shift_WF L hJ)
          (by rw [Cyclic_length_shift]; exact h2)).trans (Cyclic_primInit_shift L W (mSig E) c J)
      · exact hKc.2.2 r hr s (a + c)
    exact isPrimitive_eq_Kcal L W hL hW E hE _ hK' t ht I hI (by omega)

end RBM.KLoop
