/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffShellSplitSum

/-!
# Support of the periodic-distance fold defect

A two-step cyclic-distance defect is confined to a few representatives near
the antipode or the wrap point. The two-dimensional strip has `O(L)` points:
an unweighted sum over it is therefore not uniformly supported on `O(1)`
points without further cutoff localization.
-/

namespace RBM

/-- A safe finite candidate set for the two-step fold defect. -/
noncomputable def foldCandidateSet (L : ℕ) [NeZero L] : Finset (ZMod L) := by
  classical
  exact Finset.univ.filter (fun u => ¬ noFoldTwo L u)

theorem mem_foldCandidateSet_iff (L : ℕ) [NeZero L]
    (u : ZMod L) :
    u ∈ foldCandidateSet L ↔ ¬ noFoldTwo L u := by
  classical
  simp [foldCandidateSet]

/-- Every nonzero fold defect lies either within two representatives of the
antipode or within two representatives of the wrap point. The candidate
set is a safe superset; zero defects may also lie in it. -/
theorem foldCandidateSet_val_localized (L : ℕ) [NeZero L]
    (u : ZMod L) (hu : u ∈ foldCandidateSet L) :
    u.val ∈ Finset.Icc (L / 2 - 2) (L / 2) ∪
      Finset.Icc (L - 2) L := by
  have hno : ¬ noFoldTwo L u := (mem_foldCandidateSet_iff L u).1 hu
  change ¬(2 * (u.val + 2) ≤ L ∨
    (L ≤ 2 * u.val ∧ u.val + 2 < L)) at hno
  have hval : u.val < L := ZMod.val_lt u
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

theorem pstarFoldDefect_ne_zero_mem_foldCandidateSet
    (L : ℕ) [NeZero L] (u : ZMod L)
    (hdef : pstarFoldDefect L u ≠ 0) :
    u ∈ foldCandidateSet L :=
  (mem_foldCandidateSet_iff L u).2
    (not_noFoldTwo_of_pstarFoldDefect_ne_zero L u hdef)

/-- At most six cyclic representatives can carry a two-step fold defect. -/
theorem card_foldCandidateSet_le_six (L : ℕ) [NeZero L] :
    (foldCandidateSet L).card ≤ 6 := by
  classical
  let S := foldCandidateSet L
  have hinj : Function.Injective (fun u : ZMod L => u.val) :=
    ZMod.val_injective L
  have hcard : S.card = (S.image fun u : ZMod L => u.val).card :=
    (Finset.card_image_of_injective S hinj).symm
  have hsubset : (S.image fun u : ZMod L => u.val) ⊆
      Finset.Icc (L / 2 - 2) (L / 2) ∪
        Finset.Icc (L - 2) L := by
    intro n hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    exact foldCandidateSet_val_localized L u hu
  have hmid : (Finset.Icc (L / 2 - 2) (L / 2)).card ≤ 3 := by
    rw [Nat.card_Icc]
    omega
  have hwrap : (Finset.Icc (L - 2) L).card ≤ 3 := by
    rw [Nat.card_Icc]
    omega
  calc
    S.card = (S.image fun u : ZMod L => u.val).card := hcard
    _ ≤ (Finset.Icc (L / 2 - 2) (L / 2) ∪
        Finset.Icc (L - 2) L).card := Finset.card_le_card hsubset
    _ ≤ (Finset.Icc (L / 2 - 2) (L / 2)).card +
        (Finset.Icc (L - 2) L).card := Finset.card_union_le _ _
    _ ≤ 6 := by omega

/-- Starting points where the first-coordinate fold defect is nonzero. -/
noncomputable def foldStripE1 (L : ℕ) [NeZero L] : Finset (Z2 L) :=
  Finset.univ.filter (fun p => pstarFoldDefect L p.1 ≠ 0)

/-- The raw two-dimensional first-coordinate fold strip has at most `6L`
points; the other coordinate remains unrestricted. -/
theorem card_foldStripE1_le (L : ℕ) [NeZero L] :
    (foldStripE1 L).card ≤ 6 * L := by
  classical
  have hsubset : foldStripE1 L ⊆
      foldCandidateSet L ×ˢ (Finset.univ : Finset (ZMod L)) := by
    intro p hp
    have hdef : pstarFoldDefect L p.1 ≠ 0 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr
      ⟨pstarFoldDefect_ne_zero_mem_foldCandidateSet L p.1 hdef,
        Finset.mem_univ _⟩
  calc
    (foldStripE1 L).card ≤
        (foldCandidateSet L ×ˢ (Finset.univ : Finset (ZMod L))).card :=
      Finset.card_le_card hsubset
    _ = (foldCandidateSet L).card * L := by
      simp [Finset.card_product, ZMod.card]
    _ ≤ 6 * L := Nat.mul_le_mul_right L (card_foldCandidateSet_le_six L)

/-- The second-coordinate fold strip satisfies the same count. -/
noncomputable def foldStripE2 (L : ℕ) [NeZero L] : Finset (Z2 L) :=
  Finset.univ.filter (fun p => pstarFoldDefect L p.2 ≠ 0)

theorem card_foldStripE2_le (L : ℕ) [NeZero L] :
    (foldStripE2 L).card ≤ 6 * L := by
  classical
  have hsubset : foldStripE2 L ⊆
      (Finset.univ : Finset (ZMod L)) ×ˢ foldCandidateSet L := by
    intro p hp
    have hdef : pstarFoldDefect L p.2 ≠ 0 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_univ _,
        pstarFoldDefect_ne_zero_mem_foldCandidateSet L p.2 hdef⟩
  calc
    (foldStripE2 L).card ≤
        ((Finset.univ : Finset (ZMod L)) ×ˢ foldCandidateSet L).card :=
      Finset.card_le_card hsubset
    _ = L * (foldCandidateSet L).card := by
      simp [Finset.card_product, ZMod.card]
    _ ≤ 6 * L := by
      have h := card_foldCandidateSet_le_six L
      nlinarith

/-- The raw sum of first-coordinate fold defects over the torus is at most
`24π`. Its nonzero set still has size proportional to `L`. -/
theorem sum_abs_pstarFoldDefect_e1_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ p : Z2 L, |pstarFoldDefect L p.1|) ≤ 24 * Real.pi := by
  classical
  let S := foldStripE1 L
  have hsum : (∑ p : Z2 L, |pstarFoldDefect L p.1|) =
      ∑ p ∈ S, |pstarFoldDefect L p.1| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    have hzero : pstarFoldDefect L p.1 = 0 := by
      by_contra hn
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hn⟩)
    simp [hzero]
  have hpoint (p : Z2 L) :
      |pstarFoldDefect L p.1| ≤ 2 * symbolGridStep L :=
    abs_pstarFoldDefect_le L hL p.1
  have hbound : (∑ p ∈ S, |pstarFoldDefect L p.1|) ≤
      ∑ _p ∈ S, 2 * symbolGridStep L := by
    apply Finset.sum_le_sum
    intro p _
    exact hpoint p
  have hcard : (S.card : ℝ) ≤ 6 * (L : ℝ) := by
    exact_mod_cast card_foldStripE1_le L
  have hg : 0 ≤ 2 * symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hidentity : (6 * (L : ℝ)) * (2 * symbolGridStep L) =
      24 * Real.pi := by
    unfold symbolGridStep
    field_simp [ne_of_gt (cast_L_pos L)]
    ring
  rw [hsum]
  calc
    (∑ p ∈ S, |pstarFoldDefect L p.1|) ≤
        ∑ _p ∈ S, 2 * symbolGridStep L := hbound
    _ = (S.card : ℝ) * (2 * symbolGridStep L) := by simp
    _ ≤ (6 * (L : ℝ)) * (2 * symbolGridStep L) :=
      mul_le_mul_of_nonneg_right hcard hg
    _ = 24 * Real.pi := hidentity

/-- The same raw bound for the second-coordinate fold defect. -/
theorem sum_abs_pstarFoldDefect_e2_le
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (∑ p : Z2 L, |pstarFoldDefect L p.2|) ≤ 24 * Real.pi := by
  classical
  let S := foldStripE2 L
  have hsum : (∑ p : Z2 L, |pstarFoldDefect L p.2|) =
      ∑ p ∈ S, |pstarFoldDefect L p.2| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    have hzero : pstarFoldDefect L p.2 = 0 := by
      by_contra hn
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hn⟩)
    simp [hzero]
  have hpoint (p : Z2 L) :
      |pstarFoldDefect L p.2| ≤ 2 * symbolGridStep L :=
    abs_pstarFoldDefect_le L hL p.2
  have hbound : (∑ p ∈ S, |pstarFoldDefect L p.2|) ≤
      ∑ _p ∈ S, 2 * symbolGridStep L := by
    apply Finset.sum_le_sum
    intro p _
    exact hpoint p
  have hcard : (S.card : ℝ) ≤ 6 * (L : ℝ) := by
    exact_mod_cast card_foldStripE2_le L
  have hg : 0 ≤ 2 * symbolGridStep L := by
    unfold symbolGridStep
    positivity
  have hidentity : (6 * (L : ℝ)) * (2 * symbolGridStep L) =
      24 * Real.pi := by
    unfold symbolGridStep
    field_simp [ne_of_gt (cast_L_pos L)]
    ring
  rw [hsum]
  calc
    (∑ p ∈ S, |pstarFoldDefect L p.2|) ≤
        ∑ _p ∈ S, 2 * symbolGridStep L := hbound
    _ = (S.card : ℝ) * (2 * symbolGridStep L) := by simp
    _ ≤ (6 * (L : ℝ)) * (2 * symbolGridStep L) :=
      mul_le_mul_of_nonneg_right hcard hg
    _ = 24 * Real.pi := hidentity

/-- A genuine antipodal crossing is contained in the candidate set. -/
example : (3 : ZMod 8) ∈ foldCandidateSet 8 ∧
    (foldStripE1 8).card ≤ 48 := by
  constructor
  · exact pstarFoldDefect_ne_zero_mem_foldCandidateSet 8 3
      pstarFoldDefect_antipodal_nonzero
  · simpa using card_foldStripE1_le 8

end RBM

#print axioms RBM.foldCandidateSet_val_localized
#print axioms RBM.pstarFoldDefect_ne_zero_mem_foldCandidateSet
#print axioms RBM.card_foldCandidateSet_le_six
#print axioms RBM.card_foldStripE1_le
#print axioms RBM.card_foldStripE2_le
#print axioms RBM.sum_abs_pstarFoldDefect_e1_le
#print axioms RBM.sum_abs_pstarFoldDefect_e2_le
