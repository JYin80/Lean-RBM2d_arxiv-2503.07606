/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Cutoff
import RBM2D.Propagator.Elliptic
import RBM2D.Propagator.Momentum
import RBM2D.Propagator.Shells
import RBM2D.Propagator.SymbolReciprocalDiff
import RBM2D.Propagator.SymbolShiftAnnulus

/-!
# The dyadic shell cutoff in the smooth periodic variable

The cutoff is a function of `t(p) = (5/8) q(p) = (2 - cos θ₁ - cos θ₂)/4`, a
trigonometric polynomial, not of the folded radius `|p|_*`.  The shell cutoff
`χ_j(p) = lowPass(4^j t(p)) - lowPass(4^{j+1} t(p))` is a partition of unity over
`j = 0, …, ⌈log₂ L⌉` on `p ≠ 0`; on its support `√2 r < |p|_* < 2π r` with
`r = 2^{-j}`.  Section 8.3 of the paper only asks for a smooth dyadic
decomposition `L⁻¹ ≲ r ≲ 1`; the concrete formula is a choice.
-/

namespace RBM

open Finset

/-- The radial variable `t(p) = (5/8) q(p) ∈ [0, 1]`. -/
noncomputable def shellRadial (L : ℕ) [NeZero L] (p : Z2 L) : ℝ :=
  5 / 8 * qsym L p

/-- The shell cutoff `χ_j(p) = lowPass(4^j t(p)) - lowPass(4^{j+1} t(p))`. -/
noncomputable def shellCutoff (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L) : ℝ :=
  lowPass ((dyad j)⁻¹ ^ 2 * shellRadial L p) -
    lowPass ((dyad (j + 1))⁻¹ ^ 2 * shellRadial L p)

/-- The number of shells: the least `J` with `L ≤ 2 ^ J`. -/
def shellCount (L : ℕ) : ℕ := Nat.clog 2 L

/-- The shell kernel `K_r(u) = L⁻² ∑_p χ_j(p) (1 - ξ Ŝ(p))⁻¹ e_p(u)`. -/
noncomputable def shellKernel (L : ℕ) [NeZero L] (ξ : ℂ) (j : ℕ) (u : Z2 L) : ℂ :=
  ((L : ℂ) ^ 2)⁻¹ *
    ∑ p : Z2 L, (shellCutoff L j p : ℂ) * invSymbolMultiplier L ξ p * chr L p u

/-! ## Private helpers -/

private theorem shellCutoff_inv_dyad_sq_mul (j : ℕ) :
    ((dyad j)⁻¹) ^ 2 * dyad j ^ 2 = 1 := by
  have h : dyad j ≠ 0 := (dyad_pos j).ne'
  field_simp

private theorem shellCutoff_inv_dyad_succ (j : ℕ) :
    ((dyad (j + 1))⁻¹) ^ 2 = 4 * ((dyad j)⁻¹) ^ 2 := by
  have h : dyad j ≠ 0 := (dyad_pos j).ne'
  have : dyad (j + 1) = dyad j / 2 := by
    unfold dyad
    rw [pow_succ]
    ring
  rw [this]
  field_simp
  ring

private theorem shellCutoff_inv_dyad_sq_pos (j : ℕ) : 0 < ((dyad j)⁻¹) ^ 2 := by
  have := dyad_pos j
  positivity

private theorem shellRadial_nonneg (L : ℕ) [NeZero L] (p : Z2 L) :
    0 ≤ shellRadial L p := by
  unfold shellRadial
  have := qsym_nonneg L p
  positivity

private theorem shellRadial_le_one (L : ℕ) [NeZero L] (p : Z2 L) :
    shellRadial L p ≤ 1 := by
  unfold shellRadial
  have := qsym_le L p
  linarith

private theorem shellRadial_ge (L : ℕ) [NeZero L] (p : Z2 L) :
    pstar2 L p / (2 * Real.pi ^ 2) ≤ shellRadial L p := by
  unfold shellRadial
  have h := pstar2_le_qsym L p
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : pstar2 L p / (2 * Real.pi ^ 2)
      = 5 / 8 * (4 / (5 * Real.pi ^ 2) * pstar2 L p) := by
    field_simp
    ring
  rw [key]
  linarith

private theorem shellRadial_le (L : ℕ) [NeZero L] (p : Z2 L) :
    shellRadial L p ≤ pstar2 L p / 8 := by
  unfold shellRadial
  have h := qsym_le_pstar2 L p
  linarith

/-- On the support, `r² / 4 < t < 2 r²`. -/
private theorem shellCutoff_radial_bounds (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (h : shellCutoff L j p ≠ 0) :
    dyad j ^ 2 / 4 < shellRadial L p ∧ shellRadial L p < 2 * dyad j ^ 2 := by
  set t := shellRadial L p with ht
  have ht0 : 0 ≤ t := shellRadial_nonneg L p
  have hc := shellCutoff_inv_dyad_sq_mul j
  have hcp := shellCutoff_inv_dyad_sq_pos j
  have hr : 0 < dyad j ^ 2 := by have := dyad_pos j; positivity
  have hsucc := shellCutoff_inv_dyad_succ j
  unfold shellCutoff at h
  rw [hsucc, ← ht] at h
  constructor
  · by_contra hcon
    push Not at hcon
    apply h
    have h1 : 4 * ((dyad j)⁻¹ ^ 2) * t ≤ 1 := by
      have : 4 * ((dyad j)⁻¹ ^ 2) * t = ((dyad j)⁻¹ ^ 2 * dyad j ^ 2) * (4 * t / dyad j ^ 2) := by
        field_simp
      rw [this, hc, one_mul, div_le_one hr]
      linarith
    have h2 : (dyad j)⁻¹ ^ 2 * t ≤ 1 := by nlinarith
    rw [lowPass_eq_one_of_le_one h1, lowPass_eq_one_of_le_one h2]
    ring
  · by_contra hcon
    push Not at hcon
    apply h
    have h1 : 2 ≤ (dyad j)⁻¹ ^ 2 * t := by
      have : (dyad j)⁻¹ ^ 2 * t = ((dyad j)⁻¹ ^ 2 * dyad j ^ 2) * (t / dyad j ^ 2) := by
        field_simp
      rw [this, hc, one_mul, le_div_iff₀ hr]
      linarith
    have h2 : 2 ≤ 4 * (dyad j)⁻¹ ^ 2 * t := by nlinarith
    rw [lowPass_eq_zero_of_two_le h1, lowPass_eq_zero_of_two_le h2]
    ring

/-- For `p ≠ 0`, `pstar2 ≥ 4π²/L²`. -/
private theorem shellCutoff_pstar2_ge (L : ℕ) [NeZero L] (p : Z2 L) (hp : p ≠ 0) :
    4 * Real.pi ^ 2 / (L : ℝ) ^ 2 ≤ pstar2 L p := by
  have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hone : ∀ u : ZMod L, u ≠ 0 → 2 * Real.pi / (L : ℝ) ≤ pstar L u := by
    intro u hu
    have hz : 1 ≤ zdist L u := Nat.one_le_iff_ne_zero.mpr (fun h => hu ((zdist_eq_zero_iff L).mp h))
    have hz' : (1 : ℝ) ≤ (zdist L u : ℝ) := by exact_mod_cast hz
    unfold pstar
    rw [div_le_div_iff_of_pos_right hLpos]
    nlinarith
  have hsq : 4 * Real.pi ^ 2 / (L : ℝ) ^ 2 = (2 * Real.pi / (L : ℝ)) ^ 2 := by
    field_simp
    ring
  rw [hsq]
  have h1 := pstar_nonneg L p.1
  have h2 := pstar_nonneg L p.2
  have hpos : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  unfold pstar2
  by_cases h : p.1 = 0
  · have h' : p.2 ≠ 0 := by
      intro h'
      exact hp (Prod.ext h h')
    have := hone _ h'
    nlinarith [sq_nonneg (pstar L p.1)]
  · have := hone _ h
    nlinarith [sq_nonneg (pstar L p.2)]

/-- `pstar2 ≥ 4π²/L²` turns into `2 / L² ≤ t`. -/
private theorem shellRadial_ge_two_div (L : ℕ) [NeZero L] (p : Z2 L) (hp : p ≠ 0) :
    2 / (L : ℝ) ^ 2 ≤ shellRadial L p := by
  have h1 := shellRadial_ge L p
  have h2 := shellCutoff_pstar2_ge L p hp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 : 4 * Real.pi ^ 2 / (L : ℝ) ^ 2 / (2 * Real.pi ^ 2) ≤
      pstar2 L p / (2 * Real.pi ^ 2) := by
    apply div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : 4 * Real.pi ^ 2 / (L : ℝ) ^ 2 / (2 * Real.pi ^ 2) = 2 / (L : ℝ) ^ 2 := by
    have := cast_L_pos L
    field_simp
    ring
  linarith

/-! ## The theorems -/

theorem shellCutoff_mem_Icc :
  ∀ (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L),
    0 ≤ shellCutoff L j p ∧ shellCutoff L j p ≤ 1 := by
  intro L _ j p
  have ht0 := shellRadial_nonneg L p
  have hcp := shellCutoff_inv_dyad_sq_pos j
  have hsucc := shellCutoff_inv_dyad_succ j
  unfold shellCutoff
  rw [hsucc]
  have hanti : lowPass (4 * (dyad j)⁻¹ ^ 2 * shellRadial L p) ≤
      lowPass ((dyad j)⁻¹ ^ 2 * shellRadial L p) := by
    apply lowPass_antitone
    nlinarith [mul_nonneg hcp.le ht0]
  have h1 := lowPass_le_one ((dyad j)⁻¹ ^ 2 * shellRadial L p)
  have h2 := lowPass_nonneg (4 * (dyad j)⁻¹ ^ 2 * shellRadial L p)
  constructor <;> linarith

theorem shellCutoff_support :
  ∀ (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L), shellCutoff L j p ≠ 0 →
    2 * dyad j ^ 2 < pstar2 L p ∧ pstar2 L p < 4 * Real.pi ^ 2 * dyad j ^ 2 := by
  intro L _ j p h
  obtain ⟨h1, h2⟩ := shellCutoff_radial_bounds L j p h
  have hlow := shellRadial_le L p
  have hup := shellRadial_ge L p
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · linarith
  · have h3 : pstar2 L p ≤ 2 * Real.pi ^ 2 * shellRadial L p := by
      rw [div_le_iff₀ (by positivity)] at hup
      linarith
    have h4 : 2 * Real.pi ^ 2 * shellRadial L p < 2 * Real.pi ^ 2 * (2 * dyad j ^ 2) := by
      apply mul_lt_mul_of_pos_left h2 (by positivity)
    linarith

theorem shellCutoff_partition :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L →
    (∀ j : ℕ, shellCutoff L j 0 = 0) ∧
    ∀ p : Z2 L, p ≠ 0 →
      ∑ j ∈ Finset.range (shellCount L + 1), shellCutoff L j p = 1 := by
  intro L _ _
  constructor
  · intro j
    have hq : qsym L 0 = 0 := by
      simp [qsym]
    have hr : shellRadial L 0 = 0 := by
      simp [shellRadial, hq]
    simp [shellCutoff, hr]
  · intro p hp
    set f : ℕ → ℝ := fun j => lowPass ((dyad j)⁻¹ ^ 2 * shellRadial L p) with hf
    have hterm : ∀ j, shellCutoff L j p = f j - f (j + 1) := fun j => rfl
    simp_rw [hterm]
    rw [Finset.sum_range_sub']
    have h0 : f 0 = 1 := by
      simp only [hf, dyad_zero, inv_one, one_pow, one_mul]
      exact lowPass_eq_one_of_le_one (shellRadial_le_one L p)
    have hJ : f (shellCount L + 1) = 0 := by
      simp only [hf]
      apply lowPass_eq_zero_of_two_le
      have hLJ : L ≤ 2 ^ shellCount L := Nat.le_pow_clog (by norm_num) L
      have hLJ' : (L : ℝ) ≤ 2 ^ shellCount L := by exact_mod_cast hLJ
      have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
      have ht := shellRadial_ge_two_div L p hp
      have hsucc := shellCutoff_inv_dyad_succ (shellCount L)
      rw [hsucc]
      have hinv : ((dyad (shellCount L))⁻¹) ^ 2 = 4 ^ shellCount L := by
        unfold dyad
        simp only [inv_pow, inv_inv]
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [hinv]
      have h4 : (L : ℝ) ^ 2 ≤ 4 ^ shellCount L := by
        have : ((4 : ℝ) ^ shellCount L) = ((2 : ℝ) ^ shellCount L) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [this]
        exact pow_le_pow_left₀ hLpos.le hLJ' 2
      have h5 : 2 ≤ (L : ℝ) ^ 2 * shellRadial L p := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) ^ 2)).mp
          (by rw [div_le_iff₀ (by positivity)] at ht; rw [div_le_iff₀ (by positivity)]; linarith :
            2 / (L : ℝ) ^ 2 ≤ shellRadial L p)
        linarith
      have h6 : 0 ≤ shellRadial L p := shellRadial_nonneg L p
      nlinarith [mul_le_mul_of_nonneg_right h4 h6]
    rw [h0, hJ]
    ring

theorem shellCutoff_count :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ j : ℕ,
    (((Finset.univ.filter (fun p : Z2 L => shellCutoff L j p ≠ 0)).card : ℕ) : ℝ)
        ≤ (2 * dyad j * L + 1) ^ 2
      ∧ ∀ p : Z2 L, shellCutoff L j p ≠ 0 → 1 < dyad j * L := by
  intro L _ hL j
  have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
  have hr := dyad_pos j
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpstar : ∀ u : ZMod L, ∀ p : Z2 L, shellCutoff L j p ≠ 0 →
      (pstar L u) ^ 2 ≤ pstar2 L p → (zdist L u : ℝ) < dyad j * L := by
    intro u p hp hle
    have hs := (shellCutoff_support L j p hp).2
    have hlt : (pstar L u) ^ 2 < (2 * Real.pi * dyad j) ^ 2 := by nlinarith
    have hu0 := pstar_nonneg L u
    have hlt' : pstar L u < 2 * Real.pi * dyad j := by
      by_contra hcon
      rw [not_lt] at hcon
      have := pow_le_pow_left₀ (by positivity) hcon 2
      linarith
    unfold pstar at hlt'
    rw [div_lt_iff₀ hLpos] at hlt'
    have : 2 * Real.pi * (zdist L u : ℝ) < 2 * Real.pi * (dyad j * L) := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  constructor
  · set k : ℕ := ⌊dyad j * (L : ℝ)⌋₊ with hk
    have hsub : (Finset.univ.filter (fun p : Z2 L => shellCutoff L j p ≠ 0)) ⊆
        (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)) ×ˢ
          (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ k)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : (pstar L p.1) ^ 2 ≤ pstar2 L p := by
        unfold pstar2; nlinarith [sq_nonneg (pstar L p.2)]
      have h2 : (pstar L p.2) ^ 2 ≤ pstar2 L p := by
        unfold pstar2; nlinarith [sq_nonneg (pstar L p.1)]
      constructor
      · exact Nat.le_floor (hpstar _ p hp h1).le
      · exact Nat.le_floor (hpstar _ p hp h2).le
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product] at hcard
    have hb := card_filter_zdist_le_le L k
    have hcard' : (Finset.univ.filter (fun p : Z2 L => shellCutoff L j p ≠ 0)).card ≤
        (2 * k + 1) * (2 * k + 1) := le_trans hcard (Nat.mul_le_mul hb hb)
    have hcast : (((Finset.univ.filter (fun p : Z2 L => shellCutoff L j p ≠ 0)).card : ℕ) : ℝ)
        ≤ ((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hcard'
    have hkle : (k : ℝ) ≤ dyad j * L := Nat.floor_le (by positivity)
    have : ((2 * k + 1 : ℕ) : ℝ) ≤ 2 * dyad j * L + 1 := by
      push_cast; linarith
    have h0 : (0 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by positivity
    calc _ ≤ ((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := hcast
      _ ≤ (2 * dyad j * L + 1) * (2 * dyad j * L + 1) := mul_le_mul this this h0 (by linarith)
      _ = _ := by ring
  · intro p hp
    have hp0 : p ≠ 0 := by
      intro h0
      apply hp
      subst h0
      have hq : qsym L 0 = 0 := by simp [qsym]
      have hr : shellRadial L 0 = 0 := by simp [shellRadial, hq]
      simp [shellCutoff, hr]
    have h1 := shellCutoff_pstar2_ge L p hp0
    have h2 := (shellCutoff_support L j p hp).2
    have h3 : 4 * Real.pi ^ 2 / (L : ℝ) ^ 2 < 4 * Real.pi ^ 2 * dyad j ^ 2 := lt_of_le_of_lt h1 h2
    rw [div_lt_iff₀ (by positivity)] at h3
    have h4 : 4 * Real.pi ^ 2 * 1 < 4 * Real.pi ^ 2 * ((dyad j * L) ^ 2) := by
      nlinarith
    have h5 : 1 < (dyad j * L) ^ 2 := lt_of_mul_lt_mul_left h4 (by positivity)
    by_contra hcon
    push Not at hcon
    have : 0 ≤ dyad j * (L : ℝ) := by positivity
    nlinarith

/-! ### Stencil helpers -/

private theorem shellCutoff_zdist_natCast_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) (k : ℕ) :
    zdist L (k : ZMod L) ≤ k := by
  induction k with
  | zero => simp [(zdist_eq_zero_iff L).mpr rfl]
  | succ n ih =>
    have := zdist_add_le L (n : ZMod L) 1
    have h1 := zdist_one_le L hL
    push_cast
    omega

private theorem shellCutoff_zdist_neg_natCast_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) (k : ℕ) :
    zdist L (-(k : ZMod L)) ≤ k := by
  induction k with
  | zero => simp [(zdist_eq_zero_iff L).mpr rfl]
  | succ n ih =>
    have := zdist_add_le L (-(n : ZMod L)) (-1)
    have h1 := zdist_neg_one_le L hL
    have e : -((n + 1 : ℕ) : ZMod L) = -(n : ZMod L) + -1 := by push_cast; ring
    rw [e]
    omega

private theorem shellCutoff_pstar_shift (L : ℕ) [NeZero L] (hL : 3 ≤ L) (c : ZMod L)
    (l l' : ℕ) (hl : l ≤ 3) (hl' : l' ≤ 3) :
    pstar L (c + (l' : ZMod L)) ≤ pstar L (c + (l : ZMod L)) + 6 * Real.pi / (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hadd : ∀ u v : ZMod L, pstar L (u + v) ≤ pstar L u + pstar L v := by
    intro u v
    have hz := zdist_add_le L u v
    have hz' : (zdist L (u + v) : ℝ) ≤ (zdist L u : ℝ) + (zdist L v : ℝ) := by
      exact_mod_cast hz
    unfold pstar
    rw [← add_div, div_le_div_iff_of_pos_right hLpos]
    nlinarith
  have hbound : ∀ v : ZMod L, zdist L v ≤ 3 → pstar L v ≤ 6 * Real.pi / (L : ℝ) := by
    intro v hv
    have hv' : (zdist L v : ℝ) ≤ 3 := by exact_mod_cast hv
    unfold pstar
    rw [div_le_div_iff_of_pos_right hLpos]
    nlinarith
  rcases le_total l l' with h | h
  · have e : c + (l' : ZMod L) = (c + (l : ZMod L)) + ((l' - l : ℕ) : ZMod L) := by
      push_cast [Nat.cast_sub h]; ring
    rw [e]
    have := hadd (c + (l : ZMod L)) ((l' - l : ℕ) : ZMod L)
    have h2 : zdist L ((l' - l : ℕ) : ZMod L) ≤ 3 :=
      le_trans (shellCutoff_zdist_natCast_le L hL _) (by omega)
    have := hbound _ h2
    linarith
  · have e : c + (l' : ZMod L) = (c + (l : ZMod L)) + (-((l - l' : ℕ) : ZMod L)) := by
      push_cast [Nat.cast_sub h]; ring
    rw [e]
    have := hadd (c + (l : ZMod L)) (-((l - l' : ℕ) : ZMod L))
    have h2 : zdist L (-((l - l' : ℕ) : ZMod L)) ≤ 3 :=
      le_trans (shellCutoff_zdist_neg_natCast_le L hL _) (by omega)
    have := hbound _ h2
    linarith

private theorem shellCutoff_sqrt_step (a a' b δ : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hδ : 0 ≤ δ)
    (h : a' ≤ a + δ) :
    Real.sqrt (a' ^ 2 + b ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) + δ := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)
  nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2), mul_nonneg hδ (Real.sqrt_nonneg (a ^ 2 + b ^ 2))]

/-- The real-variable core of the stencil claim. -/
private theorem shellCutoff_stencil_core (a a' b r δ : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hr : 0 < r) (hδ : 0 ≤ δ) (hδr : δ ≤ 19 / 64 * r)
    (h1 : 2 * r ^ 2 < a ^ 2 + b ^ 2) (h2 : a ^ 2 + b ^ 2 ≤ (63 / 10 * r) ^ 2)
    (hup : a' ≤ a + δ) (hdown : a ≤ a' + δ) :
    r ^ 2 ≤ a' ^ 2 + b ^ 2 ∧ a' ^ 2 + b ^ 2 ≤ (33 / 5 * r) ^ 2 := by
  have hS := shellCutoff_sqrt_step a a' b δ ha ha' hδ hup
  have hS' := shellCutoff_sqrt_step a' a b δ ha' ha hδ hdown
  set S := Real.sqrt (a ^ 2 + b ^ 2) with hSdef
  set S' := Real.sqrt (a' ^ 2 + b ^ 2) with hS'def
  have hSsq : S ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hS'sq : S' ^ 2 = a' ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS'0 : 0 ≤ S' := Real.sqrt_nonneg _
  have hSlow : 7 / 5 * r ≤ S := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hSup : S ≤ 63 / 10 * r := by
    by_contra hcon
    push Not at hcon
    nlinarith
  rw [← hSsq] at *
  rw [← hS'sq]
  constructor
  · have : r ≤ S' := by linarith
    nlinarith
  · have : S' ≤ 33 / 5 * r := by linarith
    nlinarith

theorem shellCutoff_stencil :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ j : ℕ, 64 < dyad j * L →
    10 * symbolGridStep L ≤ dyad j ∧
    ∀ e : Z2 L, (e = (1, 0) ∨ e = (0, 1)) → ∀ (p : Z2 L) (l l' : ℕ),
      l ≤ 3 → l' ≤ 3 → shellCutoff L j (p + l • e) ≠ 0 →
        dyad j ^ 2 ≤ pstar2 L (p + l' • e) ∧
          pstar2 L (p + l' • e) ≤ (33 / 5 * dyad j) ^ 2 := by
  intro L _ hL j hj
  have hLpos : (0 : ℝ) < (L : ℝ) := cast_L_pos L
  have hr := dyad_pos j
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hδ : 6 * Real.pi / (L : ℝ) ≤ 19 / 64 * dyad j := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold symbolGridStep
    have : 10 * (2 * Real.pi / (L : ℝ)) = 20 * Real.pi / (L : ℝ) := by ring
    rw [this, div_le_iff₀ hLpos]
    nlinarith
  · intro e he p l l' hl hl' hne
    obtain ⟨hs1, hs2⟩ := shellCutoff_support L j _ hne
    have hs2' : pstar2 L (p + l • e) ≤ (63 / 10 * dyad j) ^ 2 := by
      have h1 : 2 * Real.pi < 63 / 10 := by linarith
      have h3 : (2 * Real.pi * dyad j) ^ 2 ≤ (63 / 10 * dyad j) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      nlinarith [h3]
    have hδ0 : 0 ≤ 6 * Real.pi / (L : ℝ) := by positivity
    rcases he with rfl | rfl
    · have e1 : ∀ n : ℕ, (p + n • ((1 : ZMod L), (0 : ZMod L))).1 = p.1 + (n : ZMod L) := by
        intro n; simp
      have e2 : ∀ n : ℕ, (p + n • ((1 : ZMod L), (0 : ZMod L))).2 = p.2 := by
        intro n; simp
      have hx := shellCutoff_pstar_shift L hL p.1 l l' hl hl'
      have hy := shellCutoff_pstar_shift L hL p.1 l' l hl' hl
      unfold pstar2 at hs1 hs2' ⊢
      rw [e1, e2] at hs1 hs2' ⊢
      exact shellCutoff_stencil_core _ _ _ _ _ (pstar_nonneg L _) (pstar_nonneg L _) hr hδ0 hδ
        hs1 hs2' (by linarith) (by linarith)
    · have e1 : ∀ n : ℕ, (p + n • ((0 : ZMod L), (1 : ZMod L))).1 = p.1 := by
        intro n; simp
      have e2 : ∀ n : ℕ, (p + n • ((0 : ZMod L), (1 : ZMod L))).2 = p.2 + (n : ZMod L) := by
        intro n; simp
      have hx := shellCutoff_pstar_shift L hL p.2 l l' hl hl'
      have hy := shellCutoff_pstar_shift L hL p.2 l' l hl' hl
      unfold pstar2 at hs1 hs2' ⊢
      rw [e1, e2] at hs1 hs2' ⊢
      have := shellCutoff_stencil_core (pstar L (p.2 + (l : ZMod L)))
        (pstar L (p.2 + (l' : ZMod L))) (pstar L p.1) _ _
        (pstar_nonneg L _) (pstar_nonneg L _) hr hδ0 hδ
        (by linarith) (by linarith) (by linarith) (by linarith)
      constructor <;> nlinarith [this.1, this.2]

end RBM
