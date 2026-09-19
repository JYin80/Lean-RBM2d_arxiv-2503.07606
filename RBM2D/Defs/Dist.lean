/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Defs.Block

/-!
# The periodic distance on `Z_L^2`

Section 8 of the paper writes `|x|_L = min_{n ∈ Z^2} |x + nL|` for the periodic
Euclidean norm on `Z_L^2`, and notes that the periodic `L^1` and `L^2` distances
differ by at most a factor `√2`; since every estimate of `lem_propTH` is stated
up to constants in the exponent and up to `≺`, the two are used interchangeably.

We therefore formalize the periodic **`L^1`** norm
`zdist2 x = zdist x.1 + zdist x.2`, where `zdist` is the graph distance on the
cycle `ZMod L`.  This is the choice that makes the band structure of `S^(B)`
literally true: `S^(B)_{ab} ≠ 0` iff `zdist2 (a - b) ≤ 1`.  See
`docs/paper-deltas.md`.
-/

namespace RBM

section OneDim

variable (L : ℕ) [NeZero L]

/-- Graph distance from `u` to `0` on the cycle `ZMod L`. -/
def zdist (u : ZMod L) : ℕ := min u.val (L - u.val)

@[simp] theorem zdist_zero : zdist L 0 = 0 := by
  simp [zdist]

theorem zdist_eq_zero_iff {u : ZMod L} : zdist L u = 0 ↔ u = 0 := by
  have hu : u.val < L := ZMod.val_lt u
  constructor
  · intro h
    have hval : u.val = 0 := by
      simp only [zdist] at h
      omega
    have hz : ((u.val : ℕ) : ZMod L) = 0 := by rw [hval]; simp
    rwa [ZMod.natCast_val, ZMod.cast_id] at hz
  · rintro rfl
    simp

theorem ne_zero_of_zdist_ne_zero {u : ZMod L} (h : zdist L u ≠ 0) : u ≠ 0 := by
  intro hu
  rw [hu, zdist_zero] at h
  exact h rfl

theorem zdist_add_le (u v : ZMod L) : zdist L (u + v) ≤ zdist L u + zdist L v := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hu : u.val < L := ZMod.val_lt u
  have hv : v.val < L := ZMod.val_lt v
  have hadd : (u + v).val = (u.val + v.val) % L := ZMod.val_add u v
  rcases lt_or_ge (u.val + v.val) L with h | h
  · rw [Nat.mod_eq_of_lt h] at hadd
    simp only [zdist, hadd]
    omega
  · have hmod : (u.val + v.val) % L = u.val + v.val - L := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hadd
    simp only [zdist, hadd]
    omega

theorem zdist_one_le (hL : 3 ≤ L) : zdist L (1 : ZMod L) ≤ 1 := by
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  simp only [zdist, hval]
  omega

theorem zdist_neg_one_le (hL : 3 ≤ L) : zdist L (-1 : ZMod L) ≤ 1 := by
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have hval : (1 : ZMod L).val = 1 := by
    have : ((1 : ℕ) : ZMod L).val = 1 := ZMod.val_cast_of_lt (by omega)
    simpa using this
  have hneg : (-1 : ZMod L).val = L - 1 := by
    rw [ZMod.neg_val, if_neg h1, hval]
  simp only [zdist, hneg]
  omega

end OneDim

section TwoDim

variable (L : ℕ) [NeZero L]

/-- The periodic `L^1` norm on `Z_L^2`, written `|x|_L` in Section 8. -/
def zdist2 (u : Z2 L) : ℕ := zdist L u.1 + zdist L u.2

@[simp] theorem zdist2_zero : zdist2 L (0 : Z2 L) = 0 := by
  simp [zdist2]

theorem zdist2_eq_zero_iff {u : Z2 L} : zdist2 L u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h1 : zdist L u.1 = 0 := by simp only [zdist2] at h; omega
    have h2 : zdist L u.2 = 0 := by simp only [zdist2] at h; omega
    exact Prod.ext_iff.mpr ⟨(zdist_eq_zero_iff L).mp h1, (zdist_eq_zero_iff L).mp h2⟩
  · rintro rfl
    simp

theorem zdist2_add_le (u v : Z2 L) : zdist2 L (u + v) ≤ zdist2 L u + zdist2 L v := by
  simp only [zdist2, Prod.fst_add, Prod.snd_add]
  have h1 := zdist_add_le L u.1 v.1
  have h2 := zdist_add_le L u.2 v.2
  omega

/-- `S^(B)` is supported on the nearest-neighbour band of `Z_L^2`. -/
theorem zdist2_le_one_of_mem_sbSupport (hL : 3 ≤ L) {u : Z2 L} (h : u ∈ sbSupport L) :
    zdist2 L u ≤ 1 := by
  have h1 := zdist_one_le L hL
  have hm1 := zdist_neg_one_le L hL
  simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h
  · rw [h]; show zdist L 0 + zdist L 0 ≤ 1; simp only [zdist_zero]; omega
  · rw [h]; show zdist L 1 + zdist L 0 ≤ 1; simp only [zdist_zero]; omega
  · rw [h]; show zdist L (-1) + zdist L 0 ≤ 1; simp only [zdist_zero]; omega
  · rw [h]; show zdist L 0 + zdist L 1 ≤ 1; simp only [zdist_zero]; omega
  · rw [h]; show zdist L 0 + zdist L (-1) ≤ 1; simp only [zdist_zero]; omega

theorem sbKernel_eq_zero (hL : 3 ≤ L) {u : Z2 L} (h : 1 < zdist2 L u) : sbKernel L u = 0 := by
  rw [sbKernel, if_neg]
  intro hmem
  exact absurd (zdist2_le_one_of_mem_sbSupport L hL hmem) (by omega)

theorem SB_apply_eq_zero (hL : 3 ≤ L) {x y : Z2 L} (h : 1 < zdist2 L (x - y)) :
    SB L x y = 0 := by
  rw [SB_apply]
  exact sbKernel_eq_zero L hL h

end TwoDim

end RBM
