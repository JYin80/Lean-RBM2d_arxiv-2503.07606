/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import RBM2D.Defs.Dist
import RBM2D.Propagator.Elliptic

/-!
# `(eq_qcomp)`: the comparison `q(p) ∼ |p|_*²`

Formalization of the identity `(eq_qcomp)` of Section 8.1 of the paper, which
compares the symbol defect

  `q(p) = 1 - Ŝ(p) = (2/5)[(1 - cos p₁) + (1 - cos p₂)]`   `(eq_qdef)`

with the quantity the paper writes

  `|p|_*² = dist(p₁, 2πZ)² + dist(p₂, 2πZ)²`.

## The one simplification that makes this cheap

On the lattice `T_L^2` the frequency in coordinate `i` is `p_i = 2π p_i.val / L`,
and there

  `dist(2π p.val / L, 2πZ) = 2π · zdist L p / L`

*exactly*, where `zdist` is the graph distance on the cycle `ZMod L` from
`Defs/Dist.lean`.  So we never formalize `dist(·, 2πZ)` at all: we **define**
`RBM.pstar` to be the right-hand side and record the one fact that makes this
legitimate, `RBM.cos_eq_cos_pstar`.  All the periodicity of the problem is
compressed into that single cosine identity.  See `docs/paper-deltas.md`.

## The analytic input

Two Mathlib lemmas give the two-sided elementary bound outright, with no
half-angle rewriting and no direct appeal to Jordan's inequality:

* `Real.one_sub_sq_div_two_le_cos  : 1 - x²/2 ≤ cos x`              (all `x`)
* `Real.cos_le_one_sub_mul_cos_sq  : |x| ≤ π → cos x ≤ 1 - (2/π²)x²`

that is, `(2/π²) θ² ≤ 1 - cos θ ≤ θ²/2` on `|θ| ≤ π`.  The hypothesis `|θ| ≤ π`
is supplied by `RBM.pstar_le_pi`, which is where `zdist ≤ L/2` is used.

## Main results

* `RBM.qsym_le_pstar2`  : `q(p) ≤ (1/5) |p|_*²`
* `RBM.pstar2_le_qsym`  : `(4/(5π²)) |p|_*² ≤ q(p)`

and the restatement of `(eq_elliptic)` in the paper's own form
`|1 - ξ Ŝ(p)| ∼ κ² + |p|_*²`:

* `RBM.norm_one_sub_mul_Shat_le_pstar` : `≤ κ² + |p|_*²`
* `RBM.norm_one_sub_mul_Shat_ge_pstar` : `≥ (4/(45π²)) (κ² + |p|_*²)`

`RBM.pstar2_pos_of_ne_zero` is the positivity fact the lattice sum of T3 needs
in order to divide by `|p|_*²` away from the zero mode.

## Imports

`Trigonometric.Bounds` and `Real.Pi.Bounds` are imported **explicitly**: the two
cosine bounds and `Real.pi_gt_three` exist in Mathlib but are *not* in the
import closure of `Defs.Dist` + `Propagator.Elliptic`, so the first CI round
failed with `Unknown constant` on all three.  Grepping the Mathlib source proves
a name exists; it does not prove it is in scope.

## Names checked against the pinned Mathlib (v4.34.0)

`Real.one_sub_sq_div_two_le_cos`, `Real.cos_le_one_sub_mul_cos_sq` (both in
`Analysis/SpecialFunctions/Trigonometric/Bounds.lean`, implicit `{x : ℝ}`),
`Real.cos_two_pi_sub`, `Real.pi_gt_three`, `Real.pi_pos`, `div_nonneg`,
`div_pos`, `div_le_one`, `mul_le_mul_of_nonneg_right`.
-/

namespace RBM

section OneDim

variable (L : ℕ) [NeZero L]

/-- One coordinate of `|p|_*`: the paper's `dist(2π p.val/L, 2πZ)`, written
directly in terms of the cycle distance `zdist`. -/
noncomputable def pstar (p : ZMod L) : ℝ := 2 * Real.pi * (zdist L p : ℝ) / (L : ℝ)

theorem cast_L_pos : (0 : ℝ) < (L : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem pstar_nonneg (p : ZMod L) : 0 ≤ pstar L p := by
  have h : (0 : ℝ) ≤ 2 * Real.pi * (zdist L p : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)
  simp only [pstar]
  exact div_nonneg h (le_of_lt (cast_L_pos L))

/-- `zdist` never exceeds half the circumference.  This is what puts `pstar`
inside `[0, π]`, where the cosine bounds apply. -/
theorem two_mul_zdist_le (p : ZMod L) : 2 * zdist L p ≤ L := by
  have h : p.val < L := ZMod.val_lt p
  simp only [zdist]
  omega

theorem pstar_le_pi (p : ZMod L) : pstar L p ≤ Real.pi := by
  have hLR := cast_L_pos L
  have hR : 2 * (zdist L p : ℝ) ≤ (L : ℝ) := by exact_mod_cast two_mul_zdist_le L p
  have hrw : pstar L p = Real.pi * (2 * (zdist L p : ℝ) / (L : ℝ)) := by
    simp only [pstar]; ring
  have h1 : 2 * (zdist L p : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hLR).mpr hR
  have h0 : (0 : ℝ) ≤ 2 * (zdist L p : ℝ) / (L : ℝ) :=
    div_nonneg (by positivity) (le_of_lt hLR)
  rw [hrw]
  nlinarith [Real.pi_pos]

theorem abs_pstar_le_pi (p : ZMod L) : |pstar L p| ≤ Real.pi := by
  rw [abs_of_nonneg (pstar_nonneg L p)]
  exact pstar_le_pi L p

/-- **The pivot of this file.**  Replacing the frequency `2π p.val/L` by its
distance to `2πZ` does not change the cosine.  If `p.val ≤ L - p.val` the two
are equal on the nose; otherwise they differ by `2π`. -/
theorem cos_eq_cos_pstar (p : ZMod L) :
    Real.cos (2 * Real.pi * (p.val : ℝ) / (L : ℝ)) = Real.cos (pstar L p) := by
  have hlt : p.val < L := ZMod.val_lt p
  have hLne : ((L : ℝ)) ≠ 0 := ne_of_gt (cast_L_pos L)
  rcases le_or_gt p.val (L - p.val) with h | h
  · have hz : zdist L p = p.val := by simp only [zdist]; omega
    simp only [pstar, hz]
  · have hz : zdist L p = L - p.val := by simp only [zdist]; omega
    have hcast : ((L - p.val : ℕ) : ℝ) = (L : ℝ) - (p.val : ℝ) :=
      Nat.cast_sub (le_of_lt hlt)
    have hval : pstar L p = 2 * Real.pi - 2 * Real.pi * (p.val : ℝ) / (L : ℝ) := by
      simp only [pstar, hz, hcast]
      field_simp [hLne]
    rw [hval, Real.cos_two_pi_sub]

theorem pstar_pos_of_ne_zero {u : ZMod L} (hu : u ≠ 0) : 0 < pstar L u := by
  have hz : zdist L u ≠ 0 := fun h => hu ((zdist_eq_zero_iff L).mp h)
  have hzR : (0 : ℝ) < (zdist L u : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  simp only [pstar]
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hzR) (cast_L_pos L)

end OneDim

section Elementary

/-- `1 - cos θ ≤ θ²/2`, valid for every real `θ`. -/
theorem one_sub_cos_le_sq (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

/-- `(2/π²) θ² ≤ 1 - cos θ` on `|θ| ≤ π`.  This is the half of the comparison
that Jordan's inequality is normally invoked for; Mathlib already packages it. -/
theorem sq_le_one_sub_cos {θ : ℝ} (h : |θ| ≤ Real.pi) :
    2 / Real.pi ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by
  have hc := Real.cos_le_one_sub_mul_cos_sq h
  linarith

end Elementary

section TwoDim

variable (L : ℕ) [NeZero L]

/-- `|p|_*²`, the paper's `dist(p₁,2πZ)² + dist(p₂,2πZ)²`. -/
noncomputable def pstar2 (p : Z2 L) : ℝ := (pstar L p.1) ^ 2 + (pstar L p.2) ^ 2

omit [NeZero L] in
theorem pstar2_nonneg (p : Z2 L) : 0 ≤ pstar2 L p := by
  simp only [pstar2]
  positivity

/-- Away from the zero mode `|p|_*² > 0`; this is what lets T3 divide by it. -/
theorem pstar2_pos_of_ne_zero {p : Z2 L} (hp : p ≠ 0) : 0 < pstar2 L p := by
  have hcoord : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    rcases eq_or_ne p.1 0 with h1 | h1
    · rcases eq_or_ne p.2 0 with h2 | h2
      · exact absurd (Prod.ext_iff.mpr ⟨h1, h2⟩) hp
      · exact Or.inr h2
    · exact Or.inl h1
  have h1 := pstar_nonneg L p.1
  have h2 := pstar_nonneg L p.2
  simp only [pstar2]
  rcases hcoord with h | h
  · have hpos := pstar_pos_of_ne_zero L h
    linarith [pow_pos hpos 2, sq_nonneg (pstar L p.2)]
  · have hpos := pstar_pos_of_ne_zero L h
    linarith [pow_pos hpos 2, sq_nonneg (pstar L p.1)]

theorem one_sub_cos_le_pstar_sq (p : ZMod L) :
    1 - Real.cos (2 * Real.pi * (p.val : ℝ) / (L : ℝ)) ≤ (pstar L p) ^ 2 / 2 := by
  rw [cos_eq_cos_pstar L p]
  exact one_sub_cos_le_sq _

theorem pstar_sq_le_one_sub_cos (p : ZMod L) :
    2 / Real.pi ^ 2 * (pstar L p) ^ 2
      ≤ 1 - Real.cos (2 * Real.pi * (p.val : ℝ) / (L : ℝ)) := by
  rw [cos_eq_cos_pstar L p]
  exact sq_le_one_sub_cos (abs_pstar_le_pi L p)

/-- The upper half of `(eq_qcomp)`: `q(p) ≤ (1/5)|p|_*²`. -/
theorem qsym_le_pstar2 (p : Z2 L) : qsym L p ≤ (1 / 5 : ℝ) * pstar2 L p := by
  have h1 := one_sub_cos_le_pstar_sq L p.1
  have h2 := one_sub_cos_le_pstar_sq L p.2
  simp only [qsym, pstar2]
  linarith

/-- The lower half of `(eq_qcomp)`: `(4/(5π²))|p|_*² ≤ q(p)`.  The constant is
not optimal and is not meant to be. -/
theorem pstar2_le_qsym (p : Z2 L) :
    4 / (5 * Real.pi ^ 2) * pstar2 L p ≤ qsym L p := by
  have h1 := pstar_sq_le_one_sub_cos L p.1
  have h2 := pstar_sq_le_one_sub_cos L p.2
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  -- Rewrite the left-hand side so that `2/π² * (pstar ·)^2` appears as a unit:
  -- `linarith` treats `π` as an atom, so it must see the hypotheses' left-hand
  -- sides literally rather than having to divide by `π²` itself.
  have key : 4 / (5 * Real.pi ^ 2) * pstar2 L p
      = 2 / 5 * (2 / Real.pi ^ 2 * (pstar L p.1) ^ 2
          + 2 / Real.pi ^ 2 * (pstar L p.2) ^ 2) := by
    simp only [pstar2]
    field_simp [hpi]
    ring
  rw [key]
  simp only [qsym]
  linarith

end TwoDim

section EllipticPstar

variable (L : ℕ) [NeZero L]

/-- `4/(45π²) ≤ 1/9`, the only numeric fact needed to merge `(eq_qcomp)` into
`(eq_elliptic)`.  It holds because `π > 3`. -/
theorem four_div_le_one_div_nine : 4 / (45 * Real.pi ^ 2) ≤ (1 / 9 : ℝ) := by
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  have heq : (1 / 9 : ℝ) - 4 / (45 * Real.pi ^ 2)
      = (5 * Real.pi ^ 2 - 4) / (45 * Real.pi ^ 2) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp [hpi]
    ring
  have hnn : (0 : ℝ) ≤ (1 / 9 : ℝ) - 4 / (45 * Real.pi ^ 2) := by
    rw [heq]
    apply div_nonneg
    · nlinarith
    · positivity
  linarith

/-- `(eq_elliptic)` in the paper's own form, upper half:
`|1 - ξ Ŝ(p)| ≤ κ² + |p|_*²`. -/
theorem norm_one_sub_mul_Shat_le_pstar {ξ : ℂ} (p : Z2 L) :
    ‖1 - ξ * Shat L p‖ ≤ (kappa ξ) ^ 2 + pstar2 L p := by
  have h := norm_one_sub_mul_Shat_le L (ξ := ξ) p
  have hq := qsym_le_pstar2 L p
  have hp := pstar2_nonneg L p
  rw [kappa_sq ξ]
  linarith

/-- `(eq_elliptic)` in the paper's own form, lower half:
`(4/(45π²))(κ² + |p|_*²) ≤ |1 - ξ Ŝ(p)|`.  This is the shape Section 8.2 and
Section 8.3 actually consume. -/
theorem norm_one_sub_mul_Shat_ge_pstar {ξ : ℂ} (hξ : ‖ξ‖ < 1) (p : Z2 L) :
    4 / (45 * Real.pi ^ 2) * ((kappa ξ) ^ 2 + pstar2 L p) ≤ ‖1 - ξ * Shat L p‖ := by
  have h := norm_one_sub_mul_Shat_ge_kappa L hξ p
  have hq := pstar2_le_qsym L p
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hconst := four_div_le_one_div_nine
  have hkap : (0 : ℝ) ≤ (kappa ξ) ^ 2 := sq_nonneg _
  have hsplit : 4 / (45 * Real.pi ^ 2) * ((kappa ξ) ^ 2 + pstar2 L p)
      = 4 / (45 * Real.pi ^ 2) * (kappa ξ) ^ 2
        + 1 / 9 * (4 / (5 * Real.pi ^ 2) * pstar2 L p) := by
    field_simp [hpi]
    ring
  have hc1 : 4 / (45 * Real.pi ^ 2) * (kappa ξ) ^ 2 ≤ 1 / 9 * (kappa ξ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hconst hkap
    linarith
  rw [hsplit]
  linarith

end EllipticPstar

end RBM
