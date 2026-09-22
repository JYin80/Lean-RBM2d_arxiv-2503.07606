/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Hierarchy.LoopHierarchyInitialAverageBound

/-!
# Removing block-label dependence from the crude hierarchy envelope

The two loop lengths in a pair cut sum to `n+2`. Since each loop envelope is
a pure power of the same spectral-gap factor, their product is exactly the
same for every pair position. Thus the entire crude envelope depends only on
the number of edges, not on the sign or block-label values.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The two crude pair-cut envelopes multiply to the same `n+2` power at
every enumerated pair split. This is an exact power identity, not a
monotonicity estimate. -/
theorem pair_cut_envelopes_eq_total_length
    (I : LoopIdx (Z2 L)) (hwf : I.WF)
    (p : PairSplit (Bool × Z2 L))
    (hp : p ∈ pairSplits (I.σ.zip I.a)) (η : ℝ) :
    cutResolventEnvelope L W η
        (p.before.length + p.after.length + 2) *
      cutResolventEnvelope L W η (p.middle.length + 2) =
    cutResolventEnvelope L W η (I.length + 2) *
      cutResolventEnvelope L W η 0 := by
  have hrec := pairSplits_reconstruct (I.σ.zip I.a) p hp
  have hlen := congrArg List.length hrec
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.WF, LoopIdx.length] at hwf ⊢
    omega
  rw [hzip] at hlen
  simp only [List.length_append, List.length_cons] at hlen
  have hsum : (p.before.length + p.after.length + 2) +
      (p.middle.length + 2) = I.length + 2 := by omega
  let N : ℝ := Fintype.card (BlockIndex L W)
  let R : ℝ := η⁻¹ * ((W : ℝ)⁻¹ ^ 2)
  change (N * R ^ (p.before.length + p.after.length + 2)) *
      (N * R ^ (p.middle.length + 2)) =
    (N * R ^ (I.length + 2)) * (N * R ^ 0)
  calc
    _ = N ^ 2 * R ^ ((p.before.length + p.after.length + 2) +
          (p.middle.length + 2)) := by rw [pow_add]; ring
    _ = N ^ 2 * R ^ (I.length + 2) := by rw [hsum]
    _ = _ := by simp; ring

/-- A length-only form of the explicit finite hierarchy envelope. The
pair-cut count is exactly `Nat.choose n 2`. -/
noncomputable def loopHierarchyLengthEnvelope (η : ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  (W : ℝ) ^ 2 *
    ((n : ℝ) *
      ((Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η (n + 1) *
          cutResolventEnvelope L W η 1))) +
  (W : ℝ) ^ 2 *
    ((n.choose 2 : ℝ) *
      ((Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η (n + 2) *
          cutResolventEnvelope L W η 0))) +
  (n : ℝ) *
    (‖spectralM E‖ * (W : ℝ) ^ 2 *
      ((Fintype.card (Z2 L) : ℝ) *
        cutResolventEnvelope L W η (n + 1)))

private theorem list_sum_map_const {α : Type*} (l : List α) (C : ℝ) :
    (l.map fun _ => C).sum = (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      rw [ih]
      ring

omit [NeZero W] in
/-- The crude uniform envelope is independent of all sign and block-label
values once the loop is well formed and its length is fixed. -/
theorem loopHierarchyUniformEnvelope_eq_lengthEnvelope
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (η E : ℝ) :
    loopHierarchyUniformEnvelope L W η E I =
      loopHierarchyLengthEnvelope L W η E I.length := by
  let ps := pairSplits (I.σ.zip I.a)
  let C : ℝ := (Fintype.card (Z2 L) : ℝ) *
    (cutResolventEnvelope L W η (I.length + 2) *
      cutResolventEnvelope L W η 0)
  have hmap : (ps.map fun p =>
      (Fintype.card (Z2 L) : ℝ) *
        (cutResolventEnvelope L W η
          (p.before.length + p.after.length + 2) *
          cutResolventEnvelope L W η (p.middle.length + 2))).sum =
      (ps.length : ℝ) * C := by
    have heq : (ps.map fun p =>
        (Fintype.card (Z2 L) : ℝ) *
          (cutResolventEnvelope L W η
            (p.before.length + p.after.length + 2) *
            cutResolventEnvelope L W η (p.middle.length + 2))) =
        ps.map (fun _ => C) := by
      apply List.map_congr_left
      intro p hp
      dsimp [C]
      rw [pair_cut_envelopes_eq_total_length L W I hwf p hp η]
    rw [heq]
    exact list_sum_map_const ps C
  have hzip : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.WF, LoopIdx.length] at hwf ⊢
    omega
  have hcount : ps.length = I.length.choose 2 := by
    rw [show ps = pairSplits (I.σ.zip I.a) from rfl,
      length_pairSplits, hzip]
  unfold loopHierarchyUniformEnvelope loopHierarchyLengthEnvelope
  rw [show pairSplits (I.σ.zip I.a) = ps from rfl, hmap, hcount]

omit [NeZero W] in
/-- Summing the label-independent envelope over every assignment simply
multiplies it by `card(Z2 L)^n`. -/
theorem sum_loopHierarchyUniformEnvelope_ofFn
    {n : ℕ} (σ : List Bool) (hσ : σ.length = n) (η E : ℝ) :
    (∑ f : Fin n → Z2 L,
      loopHierarchyUniformEnvelope L W η E ⟨σ, List.ofFn f⟩) =
      ((Fintype.card (Z2 L) : ℝ) ^ n) *
        loopHierarchyLengthEnvelope L W η E n := by
  have hwf (f : Fin n → Z2 L) :
      (⟨σ, List.ofFn f⟩ : LoopIdx (Z2 L)).WF := by
    simp [LoopIdx.WF, hσ]
  calc
    _ = ∑ _f : Fin n → Z2 L,
          loopHierarchyLengthEnvelope L W η E n := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [loopHierarchyUniformEnvelope_eq_lengthEnvelope L W
              ⟨σ, List.ofFn f⟩ (hwf f)]
            simp [LoopIdx.length]
    _ = ((Fintype.card (Z2 L) : ℝ) ^ n) *
          loopHierarchyLengthEnvelope L W η E n := by
            simp [Finset.sum_const, nsmul_eq_mul]

/-- Label-summed finite-time bound with the error envelope evaluated exactly
as a cardinality power times one length-only expression. -/
theorem sum_norm_expected_gloop_ofFn_le_lengthEnvelope
    (hL : 3 ≤ L) {n : ℕ} (hn : 0 < n)
    (σ : List Bool) (hσ : σ.length = n)
    {E u η : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < η)
    (hz : ∀ v ∈ Set.Icc 0 u, η ≤ |(spectralZ E v).im|) :
    (∑ f : Fin n → Z2 L,
      ‖∫ ω : Ω L W,
        gloop L W (HflowBlock L W u ω) (spectralZ E u)
          ⟨σ, List.ofFn f⟩ ∂(P L W)‖) ≤
      (L ^ 2 : ℕ) * ((W : ℝ)⁻¹) ^ (2 * (n - 1)) +
      (((Fintype.card (Z2 L) : ℝ) ^ n) *
        loopHierarchyLengthEnvelope L W η E n) * u := by
  have h := sum_norm_expected_gloop_ofFn_le_initial_add_envelopes
    L W hL hn σ hσ hE hu0 hu1 hη hz
  rw [sum_loopHierarchyUniformEnvelope_ofFn L W σ hσ η E] at h
  exact h

end RBM.Gauss
