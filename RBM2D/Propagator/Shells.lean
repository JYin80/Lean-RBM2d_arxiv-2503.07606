/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Dist

/-!
# Shell counting on the discrete torus

Work order T15.  The lattice sum of Section 8.2,

  `Σ_{p ∈ Z_L^2 \ {0}} |p|_*^{-2} ≤ C L^2 log L`,

is proved by grouping the momenta into `max`-shells and summing over shells.
The inequality part of that argument is analytic and belongs to T3
(`Propagator/LatticeSum.lean`); the bookkeeping part is pure counting, and it is
all collected here.  **Not a single real number occurs in this file**, which is
why T15 can be, and was, done in parallel with everything else.

## The shell decomposition

The shell index is the `ℓ^∞` radius

  `shellIndex p = max (zdist p.1) (zdist p.2)`,

*not* the `ℓ^1` radius `zdist2` used for the band structure of `S^(B)`.  The
`ℓ^∞` shells are the ones whose cardinality is linear in the radius with an
elementary proof: a point of shell `k` has one coordinate at distance exactly
`k` (at most `2` choices) and the other at distance at most `k` (at most
`2k + 1` choices).

## Main results

* `RBM.card_filter_zdist_eq_le` : `#{u : zdist u = k} ≤ 2`
* `RBM.card_filter_zdist_le_le` : `#{u : zdist u ≤ k} ≤ 2k + 1`
* `RBM.card_shell_le`           : `#{p : shellIndex p = k} ≤ 12k + 4`
* `RBM.sum_erase_zero_eq_sum_shells` : the fibrewise rewriting T3 consumes

The constant in `card_shell_le` is deliberately loose.  The honest bound from
the proof is `8k + 4`; `12k + 4` is stated because it is what lets T3 relax to
`16k` for `k ≥ 1` in one step, and no downstream estimate looks at the constant.
-/

namespace RBM

section OneDim

variable (L : ℕ) [NeZero L]

/-- `ZMod L` is recovered from its representative.  Stated once so that the
counting arguments below never touch `ZMod.val` lore again. -/
theorem natCast_val_self (u : ZMod L) : ((u.val : ℕ) : ZMod L) = u := by
  rw [ZMod.natCast_val, ZMod.cast_id]

/-- The complement of a representative is the negative. -/
theorem natCast_sub_val (u : ZMod L) : ((L - u.val : ℕ) : ZMod L) = -u := by
  have hle : u.val ≤ L := le_of_lt (ZMod.val_lt u)
  have hsum : ((L - u.val : ℕ) : ZMod L) + ((u.val : ℕ) : ZMod L) = ((L : ℕ) : ZMod L) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hle]
  rw [natCast_val_self, ZMod.natCast_self] at hsum
  linear_combination hsum

/-- `zdist` is a `min`, so it is one of its two arguments.  Having this as a
disjunction of plain naturals is what lets `omega` finish every count below. -/
theorem zdist_eq_val_or (u : ZMod L) : zdist L u = u.val ∨ zdist L u = L - u.val :=
  min_choice _ _

theorem zdist_le_val (u : ZMod L) : zdist L u ≤ u.val :=
  min_le_left _ _

/-- A one-dimensional sphere has at most two points: `u.val` is pinned to `k` or
to `L - k`. -/
theorem card_filter_zdist_eq_le (k : ℕ) :
    (Finset.univ.filter (fun u : ZMod L => zdist L u = k)).card ≤ 2 := by
  have hsub : (Finset.univ.filter (fun u : ZMod L => zdist L u = k)) ⊆
      ({((k : ℕ) : ZMod L), (((L - k : ℕ)) : ZMod L)} : Finset (ZMod L)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hval : u.val < L := ZMod.val_lt u
    have hchoice := zdist_eq_val_or L u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (by omega : u.val = k ∨ u.val = L - k) with h | h
    · exact Or.inl (by rw [← natCast_val_self L u, h])
    · exact Or.inr (by rw [← natCast_val_self L u, h])
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

/-- A one-dimensional ball has at most `2k + 1` points: the representatives
`0, …, k` together with the representatives `-1, …, -k`. -/
theorem card_filter_zdist_le_le (k : ℕ) :
    (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)).card ≤ 2 * k + 1 := by
  classical
  have hsub : (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)) ⊆
      (Finset.range (k + 1)).image (fun j : ℕ => (j : ZMod L)) ∪
        (Finset.Icc 1 k).image (fun j : ℕ => -((j : ℕ) : ZMod L)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hval : u.val < L := ZMod.val_lt u
    have hchoice := zdist_eq_val_or L u
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    rcases (by omega : u.val ≤ k ∨ (1 ≤ L - u.val ∧ L - u.val ≤ k)) with h | h
    · exact Or.inl ⟨u.val, by omega, natCast_val_self L u⟩
    · refine Or.inr ⟨L - u.val, ⟨h.1, h.2⟩, ?_⟩
      show -(((L - u.val : ℕ)) : ZMod L) = u
      rw [natCast_sub_val, neg_neg]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : ((Finset.range (k + 1)).image (fun j : ℕ => (j : ZMod L))).card ≤ k + 1 :=
    le_trans (Finset.card_image_le) (by simp)
  have h2 : ((Finset.Icc 1 k).image (fun j : ℕ => -((j : ℕ) : ZMod L))).card ≤ k :=
    le_trans (Finset.card_image_le) (by simp)
  omega

end OneDim

section TwoDim

variable (L : ℕ) [NeZero L]

/-- The `ℓ^∞` radius on `Z_L^2`.  Shells of this radius, not of `zdist2`, are
what the lattice sum of Section 8.2 is grouped by. -/
def shellIndex (p : Z2 L) : ℕ := max (zdist L p.1) (zdist L p.2)

@[simp] theorem shellIndex_zero : shellIndex L (0 : Z2 L) = 0 := by
  simp [shellIndex]

theorem shellIndex_eq_zero_iff {p : Z2 L} : shellIndex L p = 0 ↔ p = 0 := by
  constructor
  · intro h
    simp only [shellIndex] at h
    have h1 : zdist L p.1 = 0 := by omega
    have h2 : zdist L p.2 = 0 := by omega
    exact Prod.ext_iff.mpr ⟨(zdist_eq_zero_iff L).mp h1, (zdist_eq_zero_iff L).mp h2⟩
  · rintro rfl
    simp

/-- Every shell index is at most `L`; this is what makes `Finset.Icc 1 L` the
right index set for the shell decomposition. -/
theorem shellIndex_le (p : Z2 L) : shellIndex L p ≤ L := by
  have h1 : (p.1).val < L := ZMod.val_lt p.1
  have h2 : (p.2).val < L := ZMod.val_lt p.2
  have k1 := zdist_le_val L p.1
  have k2 := zdist_le_val L p.2
  simp only [shellIndex]
  omega

/-- **Shell counting.**  A point of shell `k` has one coordinate at distance
exactly `k` and the other at distance at most `k`, so the shell is covered by
two products of a sphere with a ball. -/
theorem card_shell_le (k : ℕ) :
    (Finset.univ.filter (fun p : Z2 L => shellIndex L p = k)).card ≤ 12 * k + 4 := by
  classical
  have hsub : (Finset.univ.filter (fun p : Z2 L => shellIndex L p = k)) ⊆
      ((Finset.univ.filter (fun u : ZMod L => zdist L u = k)) ×ˢ
          (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k))) ∪
        ((Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)) ×ˢ
          (Finset.univ.filter (fun u : ZMod L => zdist L u = k))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, shellIndex] at hp
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rcases (by omega : (zdist L p.1 = k ∧ zdist L p.2 ≤ k) ∨
        (zdist L p.2 = k ∧ zdist L p.1 ≤ k)) with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.2, h.1⟩
  have heq := card_filter_zdist_eq_le L k
  have hle := card_filter_zdist_le_le L k
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_product, Finset.card_product]
  have hmul1 :
      (Finset.univ.filter (fun u : ZMod L => zdist L u = k)).card *
        (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)).card ≤ 2 * (2 * k + 1) :=
    Nat.mul_le_mul heq hle
  have hmul2 :
      (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)).card *
        (Finset.univ.filter (fun u : ZMod L => zdist L u = k)).card ≤ (2 * k + 1) * 2 :=
    Nat.mul_le_mul hle heq
  omega

/-- **The interface T3 consumes.**  A sum over the punctured torus is a sum over
shells `1, …, L`.  Note the inner filter is over all of `Finset.univ`, not over
the punctured torus: a shell of index `k ≥ 1` never contains `0`. -/
theorem sum_erase_zero_eq_sum_shells (f : Z2 L → ℝ) :
    ∑ p ∈ Finset.univ.erase (0 : Z2 L), f p
      = ∑ k ∈ Finset.Icc 1 L,
          ∑ p ∈ Finset.univ.filter (fun p : Z2 L => shellIndex L p = k), f p := by
  classical
  have hmaps : ∀ p ∈ Finset.univ.erase (0 : Z2 L), shellIndex L p ∈ Finset.Icc 1 L := by
    intro p hp
    rw [Finset.mem_erase] at hp
    have hne : shellIndex L p ≠ 0 := fun h => hp.1 ((shellIndex_eq_zero_iff L).mp h)
    have hle := shellIndex_le L p
    simp only [Finset.mem_Icc]
    omega
  have hfilter : ∀ k ∈ Finset.Icc 1 L,
      ∑ p ∈ (Finset.univ.erase (0 : Z2 L)).filter (fun p : Z2 L => shellIndex L p = k), f p
        = ∑ p ∈ Finset.univ.filter (fun p : Z2 L => shellIndex L p = k), f p := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · refine fun h => ⟨?_, h⟩
      intro hp0
      rw [hp0, shellIndex_zero] at h
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  exact Finset.sum_congr rfl hfilter

end TwoDim

end RBM
