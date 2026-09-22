/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffLowGrid

/-!
# Cardinality of low-grid cutoff support

The cyclic distance ball of radius eight has a uniformly bounded number of
points. A two-step cutoff second difference can start only within one of
three translates of the corresponding two-dimensional box.
-/

namespace RBM

/-- The one-dimensional cyclic distance ball with distance strictly below
eight. -/
def lowGridBall (L : ℕ) [NeZero L] : Finset (ZMod L) :=
  Finset.univ.filter (fun u => zdist L u < 8)

/-- The cyclic distance ball has at most 16 points, uniformly in `L`. -/
theorem card_lowGridBall_le (L : ℕ) [NeZero L] :
    (lowGridBall L).card ≤ 16 := by
  classical
  let s := lowGridBall L
  have hinj : Function.Injective (fun u : ZMod L => u.val) :=
    ZMod.val_injective L
  have hcard : s.card = (s.image fun u : ZMod L => u.val).card :=
    (Finset.card_image_of_injective s hinj).symm
  have hsubset : (s.image fun u : ZMod L => u.val) ⊆
      Finset.range 8 ∪ Finset.Icc (L - 7) L := by
    intro n hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    have hball : zdist L u < 8 := (Finset.mem_filter.mp hu).2
    have hval : u.val < L := ZMod.val_lt u
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
    simp only [zdist] at hball
    omega
  have hIcc : (Finset.Icc (L - 7) L).card ≤ 8 := by
    rw [Nat.card_Icc]
    omega
  calc
    s.card = (s.image fun u : ZMod L => u.val).card := hcard
    _ ≤ (Finset.range 8 ∪ Finset.Icc (L - 7) L).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.range 8).card + (Finset.Icc (L - 7) L).card :=
      Finset.card_union_le _ _
    _ ≤ 16 := by simp only [Finset.card_range]; omega

/-- The two-dimensional low-grid support box. -/
def lowGridBox (L : ℕ) [NeZero L] : Finset (Z2 L) :=
  Finset.univ.filter (fun p => zdist L p.1 < 8 ∧ zdist L p.2 < 8)

theorem mem_lowGridBox_iff (L : ℕ) [NeZero L] (p : Z2 L) :
    p ∈ lowGridBox L ↔ zdist L p.1 < 8 ∧ zdist L p.2 < 8 := by
  simp [lowGridBox]

/-- At most `16²=256` lattice points lie in the low-grid box. -/
theorem card_lowGridBox_le (L : ℕ) [NeZero L] :
    (lowGridBox L).card ≤ 256 := by
  classical
  have hbox : lowGridBox L = lowGridBall L ×ˢ lowGridBall L := by
    ext p
    simp [lowGridBox, lowGridBall]
  rw [hbox, Finset.card_product]
  have h := card_lowGridBall_le L
  calc
    (lowGridBall L).card * (lowGridBall L).card ≤ 16 * 16 := by gcongr
    _ = 256 := by norm_num

/-- Starting points with a nonzero two-step cutoff second difference along
an arbitrary lattice displacement. -/
noncomputable def lowGridTwoStepStarts (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L) :
    Finset (Z2 L) :=
  Finset.univ.filter (fun p =>
    normalizedDyadicCutoff L j (p + e + e) -
      2 * normalizedDyadicCutoff L j (p + e) +
      normalizedDyadicCutoff L j p ≠ 0)

/-- Low-grid second-difference starts lie in three translates of the fixed
box and hence number at most `3·256=768`, independently of `L` and `j`. -/
theorem card_lowGridTwoStepStarts_le
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L)
    (hlow : dyad (j + 1) < 2 / (L : ℝ)) :
    (lowGridTwoStepStarts L j e).card ≤ 768 := by
  classical
  let B := lowGridBox L
  let B₁ := B.image (fun x : Z2 L => x - e)
  let B₂ := B.image (fun x : Z2 L => x - e - e)
  have hsubset : lowGridTwoStepStarts L j e ⊆ B ∪ B₁ ∪ B₂ := by
    intro p hp
    have hsecond : normalizedDyadicCutoff L j (p + e + e) -
        2 * normalizedDyadicCutoff L j (p + e) +
        normalizedDyadicCutoff L j p ≠ 0 :=
      (Finset.mem_filter.mp hp).2
    rcases cutoff_second_diff_low_grid_has_near_origin_support
        L j p (p + e) (p + e + e) hlow hsecond with h₀ | h₁ | h₂
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl ((mem_lowGridBox_iff L p).2 h₀))))
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨p + e, (mem_lowGridBox_iff L (p + e)).2 h₁, ?_⟩
      simp
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨p + e + e, (mem_lowGridBox_iff L (p + e + e)).2 h₂, ?_⟩
      simp
  have hB : B.card ≤ 256 := card_lowGridBox_le L
  have hB₁ : B₁.card ≤ B.card := Finset.card_image_le
  have hB₂ : B₂.card ≤ B.card := Finset.card_image_le
  calc
    (lowGridTwoStepStarts L j e).card ≤ (B ∪ B₁ ∪ B₂).card :=
      Finset.card_le_card hsubset
    _ ≤ B.card + B₁.card + B₂.card := by
      calc
        _ ≤ (B ∪ B₁).card + B₂.card := Finset.card_union_le _ _
        _ ≤ B.card + B₁.card + B₂.card := by
          have h := Finset.card_union_le B B₁
          omega
    _ ≤ 768 := by omega

/-- A concrete low-grid box point and the corresponding uniform count. -/
example : ((2, 0) : Z2 16) ∈ lowGridBox 16 ∧
    (lowGridTwoStepStarts 16 3 ((1, 0) : Z2 16)).card ≤ 768 := by
  constructor
  · rw [mem_lowGridBox_iff]
    constructor <;> decide
  · apply card_lowGridTwoStepStarts_le
    norm_num [dyad]

end RBM

#print axioms RBM.card_lowGridBall_le
#print axioms RBM.card_lowGridBox_le
#print axioms RBM.card_lowGridTwoStepStarts_le
