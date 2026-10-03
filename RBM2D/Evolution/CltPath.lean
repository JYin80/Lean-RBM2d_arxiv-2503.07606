/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.CltResolvent

/-!
# The pointwise path bound of the replacement step

Paper: Section 7, the proof of `clt-lemmafar`.  The definitions `cltYo`, `cltCoefSum`,
`cltGoodAt`, `CltPathBound` are stated below.

* `cltPath_bound : CltPathBound L W`: along the segment that moves one coordinate `c`
  (whose two blocks are adjacent and far from the label `b`) from `ω₀ c` to `s`, the local form
  `cltYo F E u · b` changes by at most `|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}` on the good set
  `cltGoodAt`.

The proof is the mean-value inequality on the segment.  At every point of the segment the matrix is
`Hflow u ω₀ + t • A`, `A = √u • coordinateMatrix c`, `|t| ≤ 2 W^{-1/2}`: all entries of the
perturbed resolvent are `≤ 4` (`cltPert_max_le`), the entries `G_t(σ)_{x a₀}`, `G_t(σ)_{x b₀}` for
the left index `x` of a monomial local to `b` are `≤ 2 W^{-D'}` (`cltFarGeomNear`, `cltGoodAt`,
`cltPert_sub_le`), and `cltDeriv_eval_le` bounds the derivative of `cltY` along the path.  The
statement has no hypothesis `3 ≤ L`; the support and modulus of `coordinateMatrix c` are the two
last conjuncts of `cltCoord_adj`, re-proved privately here (`cltpath_coordEntry`) because
`cltCoord_adj` itself carries `3 ≤ L`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## The statements -/

section Step

variable {L W K : ℕ} [NeZero L] [NeZero W]

/-- `Y_b(ω)` on the finite model (`clt-yform`). -/
def cltYo (F : LocalForm L W 1 K) (E u : ℝ) (ω : Ω L W) (b : Z2 L) : ℂ :=
  cltY F E u (Hflow L W u ω) b

/-- The coefficient weight `Σ_{j,q} |coef(b,j,q)| · j · 4^j` of the first-order bound `CltDerivEval`
at `g = 4`. -/
def cltCoefSum (F : LocalForm L W 1 K) (b : Z2 L) : ℝ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
    ‖F.coef (fun _ => b) j q‖ * (j : ℝ) * 4 ^ (j : ℕ)

/-- The deterministic good set at one sample point: all entries of `G_u(±)` are `≤ 2`, and the
entries whose blocks are at distance `≥ ρ` are `≤ W^{-D'}` (the events of `CltGmaxWhp`,
`CltFarEntryWhp`). -/
def cltGoodAt (E u ρ D' : ℝ) (ω : Ω L W) : Prop :=
  (∀ σ x y, ‖gEntry L W E u (Hflow L W u ω) σ x y‖ ≤ 2) ∧
    ∀ σ x y, ρ ≤ (zdist2 L ((splitEquiv L W x).1 - (splitEquiv L W y).1) : ℝ) →
      ‖gEntry L W E u (Hflow L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')

end Step

/-- **The pointwise path bound** (deterministic; `clt-ibp-decay`, `clt-ibp-bound1`
/ `clt-ibp-bound3` at first order, with the perturbation bounds `clt-gij-bound`,
`clt-gij-decay`).  At a good sample point `ω₀` (threshold `ρ = ℓ_u W^τ`), for a coordinate
`c` whose two blocks are adjacent and whose first block is at distance `≥ W^{2τ} ℓ_u / 2` from the
label `b`, moving the coordinate `c` from `ω₀ c` to `s` (`|s - ω₀ c| ≤ 2W^{-1/2}`) changes `Y_b` by
at most `|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}`.  It is used twice in `CltStep`: case A with
`ω₀ = T_k`, `s = ω' c` (`cltHyb_succ`), case B with `ω₀ = ω`, `s = 0`, label `b_m`, `m ≠ i`.
Inputs: `CltPertMaxLe`, `CltPertSubLe`, `CltDerivEval`, `CltFarGeomNear`, `CltCoordAdj`,
`Xmat_update`. -/
def CltPathBound (L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm L W 1 K) (E u τ D' : ℝ) (b : Z2 L) (c : Coord L W) (ω₀ : Ω L W)
    (s : ℝ),
    0 ≤ u → u < 1 → (spectralZ E u).im ≠ 0 → F.Local τ u →
    6 ≤ (W : ℝ) ^ τ → 1 ≤ ellT L u → 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 →
    zdist2 L ((splitEquiv L W c.1).1 - (splitEquiv L W c.2.1).1) ≤ 1 →
    ((W : ℝ) ^ τ) ^ 2 * ellT L u / 2 ≤ (zdist2 L ((splitEquiv L W c.1).1 - b) : ℝ) →
    cltGoodAt E u (ellT L u * (W : ℝ) ^ τ) D' ω₀ →
    |s - ω₀ c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) →
    ‖cltYo F E u (Function.update ω₀ c s) b - cltYo F E u ω₀ b‖ ≤
      |s - ω₀ c| * 4 * cltCoefSum F b * (W : ℝ) ^ (-D')

/-! ## Private helpers -/

section Helpers

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem cltpath_single_val (c d : Coord L W) :
    ((Pi.single c (1 : ℝ) : Coord L W → ℝ) d : ℝ) = if d = c then 1 else 0 := by
  by_cases h : d = c
  · subst h; simp
  · simp [h]

/-- Entries of `coordinateMatrix c`: modulus `≤ 1`, supported on `{(x,y),(y,x)}` (a copy of the
private `cltres_coordEntry` of `RBM2D/Evolution/CltResolvent.lean`; no `3 ≤ L` is needed). -/
private theorem cltpath_coordEntry (c : Coord L W) (i j : Idx L W) :
    ‖coordinateMatrix L W c i j‖ ≤ 1 ∧
      (coordinateMatrix L W c i j ≠ 0 →
        (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) := by
  obtain ⟨x, y, β⟩ := c
  rw [coordinateMatrix_apply]
  unfold Xentry
  simp only [cltpath_single_val]
  split_ifs <;> simp_all

/-- `√u • coordinateMatrix c` is a `cltCoordDir` for `0 ≤ u ≤ 1`. -/
private theorem cltpath_coordDir {u : ℝ} (hu1 : u ≤ 1) (c : Coord L W) :
    cltCoordDir ((Real.sqrt u : ℂ) • coordinateMatrix L W c) c.1 c.2.1 := by
  have hs0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hs1 : Real.sqrt u ≤ 1 := Real.sqrt_le_one.2 hu1
  refine ⟨?_, fun a b => ?_, fun a b hab => ?_⟩
  · have h := isHermitian_add_realSmul Matrix.isHermitian_zero
      (coordinateMatrix_isHermitian L W c) (Real.sqrt u)
    rwa [zero_add] at h
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
    calc Real.sqrt u * ‖coordinateMatrix L W c a b‖ ≤ 1 * 1 :=
          mul_le_mul hs1 (cltpath_coordEntry c a b).1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine (cltpath_coordEntry c a b).2 fun h0 => hab ?_
    rw [Matrix.smul_apply, smul_eq_mul, h0, mul_zero]

/-- The spectral parameter of the `σ`-resolvent in `gEntry`. -/
private def cltpath_zs (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then spectralZ E u else (starRingEnd ℂ) (spectralZ E u)

private theorem cltpath_zs_im {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool) :
    (cltpath_zs E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltpath_zs] using hz

private theorem cltpath_gEntry (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (x y : Idx L W) : gEntry L W E u M σ x y = green M (cltpath_zs E u σ) x y := rfl

/-- The private copy of `zdist_neg` used in `CltResolvent.lean`. -/
private theorem cltpath_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

/-- The private copy of `zdist2_neg` used in `CltResolvent.lean`. -/
private theorem cltpath_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, cltpath_zdist_neg]

/-- Moving the coordinate `c` of `ω₀` to `x` moves `Hflow` by `(x - ω₀ c) • A`,
`A = √u • coordinateMatrix c`. -/
private theorem cltpath_Hflow_update (u : ℝ) (ω₀ : Ω L W) (c : Coord L W) (x : ℝ) :
    Hflow L W u (Function.update ω₀ c x) =
      Hflow L W u ω₀ + (((x - ω₀ c : ℝ)) : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix L W c) := by
  rw [Hflow, Xmat_update, smul_add, ← Complex.coe_smul, smul_comm, Hflow]

/-- The mean-value inequality on `[-R, R]` for a function with a derivative bounded by `C` at each
point of the interval. -/
private theorem cltpath_mvt (h : ℝ → ℂ) (R C v : ℝ)
    (hD : ∀ t : ℝ, |t| ≤ R → ∃ D : ℂ, HasDerivAt h D t ∧ ‖D‖ ≤ C) (hv : |v| ≤ R) :
    ‖h v - h 0‖ ≤ C * |v| := by
  have hR : 0 ≤ R := (abs_nonneg v).trans hv
  have hmem : ∀ t : ℝ, t ∈ Set.Icc (-R) R ↔ |t| ≤ R := fun t => by
    rw [Set.mem_Icc, abs_le]
  have hf : ∀ t ∈ Set.Icc (-R) R, DifferentiableAt ℝ h t := fun t ht =>
    let ⟨_, hD1, _⟩ := hD t ((hmem t).1 ht)
    hD1.differentiableAt
  have hb : ∀ t ∈ Set.Icc (-R) R, ‖deriv h t‖ ≤ C := fun t ht =>
    let ⟨D, hD1, hD2⟩ := hD t ((hmem t).1 ht)
    hD1.deriv ▸ hD2
  have := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc (-R) R)
    ((hmem 0).2 (by simpa using hR)) ((hmem v).2 hv)
  simpa using this

/-- One point of the path: at `t` with `|t| ≤ 2 W^{-1/2}` the local form `cltY` along the line
`M₀ + s A` has a derivative of norm at most `4 W^{-D'} cltCoefSum F b`. -/
private theorem cltpath_deriv (K : ℕ) (F : LocalForm L W 1 K) (E u τ D' : ℝ) (b : Z2 L)
    (c : Coord L W) (ω₀ : Ω L W) (hu1 : u < 1) (hz : (spectralZ E u).im ≠ 0)
    (hloc : F.Local τ u) (hw : 6 ≤ (W : ℝ) ^ τ) (hℓ : 1 ≤ ellT L u)
    (hθ : 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1)
    (hadj : zdist2 L ((splitEquiv L W c.1).1 - (splitEquiv L W c.2.1).1) ≤ 1)
    (hfar : ((W : ℝ) ^ τ) ^ 2 * ellT L u / 2 ≤ (zdist2 L ((splitEquiv L W c.1).1 - b) : ℝ))
    (hgood : cltGoodAt E u (ellT L u * (W : ℝ) ^ τ) D' ω₀)
    (t : ℝ) (ht : |t| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => cltY F E u (Hflow L W u ω₀ +
        (s : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix L W c)) b) D t ∧
      ‖D‖ ≤ 4 * (W : ℝ) ^ (-D') * cltCoefSum F b := by
  set A : Matrix (Idx L W) (Idx L W) ℂ := (Real.sqrt u : ℂ) • coordinateMatrix L W c with hA
  set M₀ : Matrix (Idx L W) (Idx L W) ℂ := Hflow L W u ω₀ with hM₀
  set γ : ℝ := (W : ℝ) ^ (-D') with hγdef
  have hγ0 : 0 ≤ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hherm : M₀.IsHermitian := Hflow_isHermitian L W u ω₀
  have hdir : cltCoordDir A c.1 c.2.1 := cltpath_coordDir hu1.le c
  have h8 : 8 * |t| ≤ 1 := by linarith
  have hzσ : ∀ σ, (cltpath_zs E u σ).im ≠ 0 := cltpath_zs_im hz
  have hG0 : ∀ σ x y, ‖green M₀ (cltpath_zs E u σ) x y‖ ≤ 2 := fun σ x y => hgood.1 σ x y
  have hGt : ∀ σ x y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) x y‖ ≤ 4 := fun σ x y => by
    have h := cltPert_max_le (Idx L W) M₀ A c.1 c.2.1 (cltpath_zs E u σ) t 2 hherm hdir (hzσ σ)
      (hG0 σ) (by linarith) x y
    linarith
  have hnear : ∀ (j : Fin (K + 1)) (q : Fin j → Idx L W × Idx L W × Bool),
      F.coef (fun _ => b) j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntry L W E u (M₀ + (t : ℂ) • A) σ (q i).1 c.1‖ ≤ 2 * γ ∧
          ‖gEntry L W E u (M₀ + (t : ℂ) • A) σ (q i).1 c.2.1‖ ≤ 2 * γ := by
    intro j q hq i σ
    obtain ⟨m, hm⟩ := hloc (fun _ => b) j q hq i
    have hm' : (zdist2 L ((splitEquiv L W (q i).1).1 - b) : ℝ) < ellT L u * (W : ℝ) ^ τ := by
      have h0 : (0 : ℝ) ≤ (zdist2 L ((splitEquiv L W (q i).2.1).1 - b) : ℝ) := Nat.cast_nonneg _
      push_cast at hm
      linarith
    have hadj' : zdist2 L ((splitEquiv L W c.2.1).1 - (splitEquiv L W c.1).1) ≤ 1 := by
      have h := cltpath_zdist2_neg ((splitEquiv L W c.1).1 - (splitEquiv L W c.2.1).1)
      rw [neg_sub] at h
      rw [h]
      exact hadj
    obtain ⟨h1, h2⟩ := cltFarGeomNear L ((W : ℝ) ^ τ) (ellT L u) (splitEquiv L W c.1).1
      (splitEquiv L W c.2.1).1 b (splitEquiv L W (q i).1).1 hw hℓ hfar hadj' hm'
    have ha := hgood.2 σ (q i).1 c.1 h1
    have hb := hgood.2 σ (q i).1 c.2.1 h2
    have hmax : max ‖green M₀ (cltpath_zs E u σ) (q i).1 c.1‖
        ‖green M₀ (cltpath_zs E u σ) (q i).1 c.2.1‖ ≤ γ := max_le ha hb
    have hsub := (cltPert_sub_le (Idx L W) M₀ A c.1 c.2.1 (cltpath_zs E u σ) t 4 hherm hdir
      (hzσ σ) (hGt σ) (q i).1)
    have key : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y -
        green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ ∧ ‖green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ →
        ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y‖ ≤ 2 * γ := fun y hy => by
      have := norm_sub_norm_le (green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y)
        (green M₀ (cltpath_zs E u σ) (q i).1 y)
      linarith [hy.1, hy.2]
    have hstep : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y -
        green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ := fun y => by
      calc _ ≤ 2 * |t| * 4 * max ‖green M₀ (cltpath_zs E u σ) (q i).1 c.1‖
              ‖green M₀ (cltpath_zs E u σ) (q i).1 c.2.1‖ := (hsub y).1
        _ ≤ 2 * |t| * 4 * γ := by gcongr
        _ ≤ γ := by nlinarith [mul_le_mul_of_nonneg_right h8 hγ0]
    refine ⟨?_, ?_⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, ha⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, hb⟩
  obtain ⟨D, hD, hDb⟩ := cltDeriv_eval_le L W K F E u M₀ A c.1 c.2.1 t 4 (2 * γ) b hherm hdir hz
    (fun σ x y => by rw [cltpath_gEntry]; exact hGt σ x y) hnear
  refine ⟨D, hD, hDb.trans (le_of_eq ?_)⟩
  unfold cltCoefSum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end Helpers

/-! ## The path bound -/

/-- **`CltPathBound`**: the mean-value inequality along the segment that moves the coordinate
`c` from `ω₀ c` to `s`, with no hypothesis `3 ≤ L`. -/
theorem cltPath_bound (L W : ℕ) [NeZero L] [NeZero W] : CltPathBound L W := by
  intro K F E u τ D' b c ω₀ s hu0 hu1 hz hloc hw hℓ hθ hadj hfar hgood hs
  set h : ℝ → ℂ := fun t => cltY F E u (Hflow L W u ω₀ +
    (t : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix L W c)) b with hh
  have hpath : ∀ x : ℝ, cltYo F E u (Function.update ω₀ c x) b = h (x - ω₀ c) := by
    intro x
    rw [cltYo, cltpath_Hflow_update]
  have h0 : cltYo F E u ω₀ b = h 0 := by
    have := hpath (ω₀ c)
    rwa [Function.update_eq_self, sub_self] at this
  have hmvt := cltpath_mvt h (2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (W : ℝ) ^ (-D') * cltCoefSum F b)
    (s - ω₀ c)
    (fun t ht => cltpath_deriv K F E u τ D' b c ω₀ hu1 hz hloc hw hℓ hθ hadj hfar hgood t ht) hs
  rw [hpath s, h0]
  calc _ ≤ _ := hmvt
    _ = _ := by ring

end RBM.Evol
