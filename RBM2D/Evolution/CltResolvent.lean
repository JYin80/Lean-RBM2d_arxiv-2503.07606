/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Case3Defs
import RBM2D.Gauss.Envelope
import RBM2D.Gauss.LoopEnvelope

/-!
# Deterministic resolvent bounds for the replacement step

Paper: Section 7, the proof of `clt-lemmafar` (statement, closing sentence).  The statements are
stated below.

* `cltCoordDir`: a one-coordinate direction; `cltCoord_adj` says `coordinateMatrix c` is one;
* `cltPert_max_le`, `cltPert_sub_le`: the perturbation `G_t` of `G` in one direction;
* `cltDeriv_entry`, `cltDeriv_eval_le`: the derivative of an entry and of the local form `cltY`;
* `cltEta_lower`, `cltEval_det_le`: the lower bound on `Im z_u` and the deterministic bound of
  `cltY` in powers of `N = (WL)²`;
* `cltFarGeomHalf`, `cltFarGeomNear`: the far/near geometry of `Z_L²`.

The private helpers `cltres_*` re-prove the private `cltm_cltY_le`, `cltm_ck*` of
`RBM2D/Evolution/CltMoments.lean`.  Everything here is deterministic.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open Matrix RBM RBM.Gauss RBM.Ind

/-! ## The statements -/

section Det

/-- A one-coordinate direction with support `{(a₀,b₀),(b₀,a₀)}` and entries of modulus `≤ 1`.
`√u • coordinateMatrix L W c` is one for `0 ≤ u ≤ 1` (by `CltCoordAdj`, `c = (a₀, b₀, β)`). -/
def cltCoordDir {ι : Type*} (A : Matrix ι ι ℂ) (a₀ b₀ : ι) : Prop :=
  A.IsHermitian ∧ (∀ a b, ‖A a b‖ ≤ 1) ∧
    ∀ a b, A a b ≠ 0 → (a = a₀ ∧ b = b₀) ∨ (a = b₀ ∧ b = a₀)

/-- **Perturbation, maximum bound** (`clt-gij-bound`, deterministic part).  If `|G_{xy}| ≤ g` for
all entries
and `4|t| g ≤ 1`, then `|(G_t)_{xy}| ≤ 2g`, where `G_t = green (M + tA) z`. -/
def CltPertMaxLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t g : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green M z x y‖ ≤ g) → 4 * |t| * g ≤ 1 →
    ∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ 2 * g

/-- **Perturbation, difference bound** (`clt-gij-decay`; replaces the expansion `clt-resolvent`, and
the
pigeonhole after it).  `G_t - G = -t G A G_t = -t G_t A G` bounded entrywise. -/
def CltPertSubLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t gt : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ gt) →
    ∀ x y,
      ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z x a₀‖ ‖green M z x b₀‖ ∧
        ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z a₀ y‖ ‖green M z b₀ y‖

/-- **Derivative of an entry** (first-order case of `clt-f-total`; "`∂_{H_ij}(G_s)_{xy} =
-(G_s)_{xi}(G_s)_{jy}`", proof of `clt-lemma`).  The derivative of `s ↦ (G_s)_{xy}` along the
direction `A`, and its entrywise bounds.  Applied with `z` and with `conj z` (the two values of
`σ` in `gEntry`).  Input: `hasDerivAt_lineInverse`. -/
def CltDerivEntry (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → ∀ x y,
      HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z x y)
        (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y) t ∧
      ∀ g : ℝ, (∀ x' y', ‖green (M + (t : ℂ) • A) z x' y'‖ ≤ g) →
        ‖(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y‖ ≤
            2 * g * max ‖green (M + (t : ℂ) • A) z x a₀‖ ‖green (M + (t : ℂ) • A) z x b₀‖ ∧
          ‖(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y‖ ≤
            2 * g * max ‖green (M + (t : ℂ) • A) z a₀ y‖ ‖green (M + (t : ℂ) • A) z b₀ y‖

/-- **Derivative of the local form** (`clt-f-total-bound-1`, at first order; `clt-ibp-decay`,
`clt-ibp-bound1`, `clt-ibp-bound3`, first order).  The derivative of the local form
`cltY F E u (M + sA) b` in `s` exists and is bounded by
`2 Σ_{j,q} |coef| · j · g^j · φ`, where `g` bounds all entries of `G_t(±)` and `φ` bounds the
entries `G_t(σ)_{x a₀}`, `G_t(σ)_{x b₀}` for every left index `x` of a monomial with non-zero
coefficient. -/
def CltDerivEval (L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm L W 1 K) (E u : ℝ) (M A : Matrix (Idx L W) (Idx L W) ℂ)
    (a₀ b₀ : Idx L W) (t g φ : ℝ) (b : Z2 L),
    M.IsHermitian → cltCoordDir A a₀ b₀ → (spectralZ E u).im ≠ 0 →
    (∀ σ x y, ‖gEntry L W E u (M + (t : ℂ) • A) σ x y‖ ≤ g) →
    (∀ (j : Fin (K + 1)) (q : Fin j → Idx L W × Idx L W × Bool),
      F.coef (fun _ => b) j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntry L W E u (M + (t : ℂ) • A) σ (q i).1 a₀‖ ≤ φ ∧
          ‖gEntry L W E u (M + (t : ℂ) • A) σ (q i).1 b₀‖ ≤ φ) →
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => cltY F E u (M + (s : ℂ) • A) b) D t ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
        ‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ

/-- `c_κ = √(κ(4-κ))/2`, the lower bound of `Im m(E)` for `|E| ≤ 2 - κ` (the private
`cltm_ck` of `CltMoments.lean`). -/
def cltCk (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ)) / 2

/-- **Lower bound on `Im z_u`** (the spectral-parameter lower bound behind `clt-f-total-bound-2`,
and
`clt-ibp-bound2`/`clt-ibp-bound4`): `c_κ / N ≤ Im z_u`.  With
`norm_green_le` this gives `‖G_u(±)‖ ≤ N / c_κ` for every Hermitian matrix. -/
def CltEtaLower (L W : ℕ) : Prop :=
  ∀ (κ δ E u : ℝ), 0 < κ → 0 < δ → |E| ≤ 2 - κ →
    ((((W * L) ^ 2 : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    cltCk κ / (((W * L) ^ 2 : ℕ) : ℝ) ≤ (spectralZ E u).im

/-- **Deterministic bound of the local form** (`clt-f-total-bound-2`; `clt-ibp-bound2`,
`clt-ibp-bound4`,
`clt-ibp-other-factor-bound`), in powers of `N = (WL)²` (the paper's
`O(W^C)` form needs `Bandwidth`).  For every Hermitian `M`:
`‖cltY F E u M b‖ ≤ (K+1) N^{C'} (2N³/c_κ)^K`.  This is the bound of the private
`cltm_Y_bound` (`CltMoments.lean`), stated for any Hermitian matrix (its proof, through the
private `cltm_cltY_le`, uses only Hermitian-ness). -/
def CltEvalDetLe (L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (κ δ E u : ℝ) (K : ℕ) (F : LocalForm L W 1 K) (C' : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Z2 L),
    0 < κ → 0 < δ → |E| ≤ 2 - κ →
    ((((W * L) ^ 2 : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    (∀ b' j q, ‖F.coef b' j q‖ ≤ ((((W * L) ^ 2 : ℕ) : ℝ)) ^ C') → M.IsHermitian →
    ‖cltY F E u M b‖ ≤ ((K : ℝ) + 1) * ((((W * L) ^ 2 : ℕ) : ℝ)) ^ C' *
      (2 * ((((W * L) ^ 2 : ℕ) : ℝ)) ^ 3 / cltCk κ) ^ K

private theorem zdist_neg_aux (L : ℕ) [NeZero L] (x : ZMod L) :
    zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem zdist2_neg_aux (L : ℕ) [NeZero L] (u : Z2 L) :
    zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, zdist_neg_aux]

/-- **Far/near dichotomy** (the dichotomy in the proof of `clt-lemma`, half-separation form; no
condition on
`W`).  If `R ≤ |b_i - b_k|_L` for all `k ≠ i`, then every block `a` has `R/2 ≤ |a - b_i|_L` or
`R/2 ≤ |a - b_k|_L` for all `k ≠ i`.  Proved: `cltFarGeomHalf`. -/
def CltFarGeomHalf : Prop :=
  ∀ (L : ℕ) [NeZero L] (m : ℕ) (b : Fin m → Z2 L) (i : Fin m) (R : ℝ) (a : Z2 L),
    (∀ k, k ≠ i → R ≤ (zdist2 L (b i - b k) : ℝ)) →
    R / 2 ≤ (zdist2 L (a - b i) : ℝ) ∨ ∀ k, k ≠ i → R / 2 ≤ (zdist2 L (a - b k) : ℝ)

theorem cltFarGeomHalf : CltFarGeomHalf := by
  intro L _ m b i R a hsep
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, k, hki, h2⟩ := hcon
  have htri := zdist2_add_le L (b i - a) (a - b k)
  rw [show b i - a + (a - b k) = b i - b k by abel] at htri
  have hs : zdist2 L (b i - a) = zdist2 L (a - b i) := by
    rw [← neg_sub, zdist2_neg_aux]
  rw [hs] at htri
  have h3 := hsep k hki
  have h4 : (zdist2 L (b i - b k) : ℝ) ≤ (zdist2 L (a - b i) : ℝ) + (zdist2 L (a - b k) : ℝ) := by
    exact_mod_cast htri
  linarith

/-- **Near-block distances** (the distances used in the proof of `clt-lemma`, `clt-ibp-bound3`).
With
`w = W^τ ≥ 6`, `ℓ ≥ 1`: if
the block `a` is at distance `≥ w²ℓ/2` from the label `b`, `a'` is adjacent to `a`, and
`|x - b|_L < ℓw` (a block of a monomial local to `b`), then `x` is at distance `≥ ℓw` from `a`
and from `a'` (the far threshold of `FarEntryDecayPT` at `τ' = τ`).  Without `6 ≤ w` it is false.
Proved: `cltFarGeomNear`. -/
def CltFarGeomNear : Prop :=
  ∀ (L : ℕ) [NeZero L] (w ℓ : ℝ) (a a' b x : Z2 L), 6 ≤ w → 1 ≤ ℓ →
    w ^ 2 * ℓ / 2 ≤ (zdist2 L (a - b) : ℝ) → zdist2 L (a' - a) ≤ 1 →
    (zdist2 L (x - b) : ℝ) < ℓ * w →
    ℓ * w ≤ (zdist2 L (x - a) : ℝ) ∧ ℓ * w ≤ (zdist2 L (x - a') : ℝ)

theorem cltFarGeomNear : CltFarGeomNear := by
  intro L _ w ℓ a a' b x hw hℓ hab ha' hxb
  have t1 := zdist2_add_le L (a - x) (x - b)
  rw [show a - x + (x - b) = a - b by abel] at t1
  have s1 : zdist2 L (a - x) = zdist2 L (x - a) := by
    rw [← neg_sub, zdist2_neg_aux]
  rw [s1] at t1
  have t2 := zdist2_add_le L (x - a') (a' - a)
  rw [show x - a' + (a' - a) = x - a by abel] at t2
  have t1' : (zdist2 L (a - b) : ℝ) ≤ (zdist2 L (x - a) : ℝ) + (zdist2 L (x - b) : ℝ) := by
    exact_mod_cast t1
  have t2' : (zdist2 L (x - a) : ℝ) ≤ (zdist2 L (x - a') : ℝ) + (zdist2 L (a' - a) : ℝ) := by
    exact_mod_cast t2
  have ha'' : (zdist2 L (a' - a) : ℝ) ≤ 1 := by exact_mod_cast ha'
  have hℓ0 : (0 : ℝ) ≤ ℓ := by linarith
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have key : ℓ * w + 1 ≤ w ^ 2 * ℓ / 2 - ℓ * w := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hw) hℓ0) hw0,
      mul_nonneg (sub_nonneg.2 hℓ) hw0]
  constructor <;> linarith

/-- **Adjacency of the blocks of a coordinate** (the restriction to `S_ij ≠ 0`, proof of
`clt-lemma`).  For `L ≥ 3`
and a coordinate `c = (x, y, β)`: if `gvar c ≠ 0` the blocks of `x` and `y` are adjacent
(`|[x] - [y]|_L ≤ 1`, five-point `sbSupport`); `coordinateMatrix c` is supported on
`{(x,y),(y,x)}` with entries of modulus `≤ 1`. -/
def CltCoordAdj : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ c : Coord L W,
    (gvar L W c ≠ 0 →
      zdist2 L ((splitEquiv L W c.1).1 - (splitEquiv L W c.2.1).1) ≤ 1) ∧
    (∀ i j, coordinateMatrix L W c i j ≠ 0 → (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) ∧
    (∀ i j, ‖coordinateMatrix L W c i j‖ ≤ 1)

end Det

/-! ## Proofs: perturbation of `G` in one direction -/

section Perturb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(R1)`: `G - G_t = t G A G_t` for `G = green M z`, `G_t = green (M + tA) z`. -/
private theorem cltres_R1 {M A : Matrix ι ι ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian)
    (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    green M z - green (M + (t : ℂ) • A) z =
      (t : ℂ) • (green M z * A * green (M + (t : ℂ) • A) z) := by
  have hX : IsUnit (M - z • (1 : Matrix ι ι ℂ)) :=
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hM hz
  have hY : IsUnit (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) :=
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA t) hz
  have h := Matrix.inv_sub_inv (A := M - z • (1 : Matrix ι ι ℂ))
    (B := M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) ⟨fun _ => hY, fun _ => hX⟩
  have hd : (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) - (M - z • (1 : Matrix ι ι ℂ))
      = (t : ℂ) • A := by abel
  rw [hd] at h
  unfold green
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- `(R2)`: `G_t - G = -t G_t A G`. -/
private theorem cltres_R2 {M A : Matrix ι ι ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian)
    (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    green (M + (t : ℂ) • A) z - green M z =
      -((t : ℂ) • (green (M + (t : ℂ) • A) z * A * green M z)) := by
  have hX : IsUnit (M - z • (1 : Matrix ι ι ℂ)) :=
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero hM hz
  have hY : IsUnit (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) :=
    RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA t) hz
  have h := Matrix.inv_sub_inv (A := M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ))
    (B := M - z • (1 : Matrix ι ι ℂ)) ⟨fun _ => hX, fun _ => hY⟩
  have hd : (M - z • (1 : Matrix ι ι ℂ)) - (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ))
      = -((t : ℂ) • A) := by abel
  rw [hd] at h
  unfold green
  rw [h, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]

set_option linter.unusedDecidableInType false in
/-- The support fact (S): `|(P A Q)_{xy}| ≤ |P_{x a₀}||Q_{b₀ y}| + |P_{x b₀}||Q_{a₀ y}|`. -/
private theorem cltres_PAQ_le {A : Matrix ι ι ℂ} {a₀ b₀ : ι} (hA : cltCoordDir A a₀ b₀)
    (P Q : Matrix ι ι ℂ) (x y : ι) :
    ‖(P * A * Q) x y‖ ≤ ‖P x a₀‖ * ‖Q b₀ y‖ + ‖P x b₀‖ * ‖Q a₀ y‖ := by
  obtain ⟨-, hA1, hAs⟩ := hA
  have hterm : ∀ a k : ι, ‖P x a * A a k * Q k y‖ ≤
      (if a = a₀ ∧ k = b₀ then ‖P x a₀‖ * ‖Q b₀ y‖ else 0) +
      (if a = b₀ ∧ k = a₀ then ‖P x b₀‖ * ‖Q a₀ y‖ else 0) := by
    intro a k
    by_cases h0 : A a k = 0
    · rw [h0]
      simp only [mul_zero, zero_mul, norm_zero]
      split_ifs <;> positivity
    · rcases hAs a k h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc : a = a₀ ∧ k = b₀ := ⟨h1, h2⟩
        rw [ite_eq_left hc]
        refine le_add_of_le_of_nonneg ?_ (by split_ifs <;> positivity)
        rw [h1, h2, norm_mul, norm_mul]
        calc ‖P x a₀‖ * ‖A a₀ b₀‖ * ‖Q b₀ y‖ ≤ ‖P x a₀‖ * 1 * ‖Q b₀ y‖ := by
              gcongr; exact hA1 _ _
          _ = _ := by ring
      · have hc : a = b₀ ∧ k = a₀ := ⟨h1, h2⟩
        rw [ite_eq_left hc]
        refine le_add_of_nonneg_of_le (by split_ifs <;> positivity) ?_
        rw [h1, h2, norm_mul, norm_mul]
        calc ‖P x b₀‖ * ‖A b₀ a₀‖ * ‖Q a₀ y‖ ≤ ‖P x b₀‖ * 1 * ‖Q a₀ y‖ := by
              gcongr; exact hA1 _ _
          _ = _ := by ring
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k _ => hterm a k)).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, ite_and]
  simp

end Perturb

section PerturbThms

/-- **Perturbation, maximum bound** (`clt-gij-bound`, deterministic part), the statement
`CltPertMaxLe`. -/
theorem cltPert_max_le (ι : Type*) [Fintype ι] [DecidableEq ι] : CltPertMaxLe ι := by
  intro M A a₀ b₀ z t g hM hA hz hg ht x y
  set Gt := green (M + (t : ℂ) • A) z with hGt
  set G := green M z with hG
  have hR1 : ∀ x y, Gt x y = G x y - (t : ℂ) * (G * A * Gt) x y := by
    intro x y
    have h := congrFun (congrFun (cltres_R1 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [← h]; ring
  have hne : Nonempty (ι × ι) := ⟨(x, y)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : ι × ι => ‖Gt p.1 p.2‖)
  have hm0 : 0 ≤ ‖Gt p.1 p.2‖ := norm_nonneg _
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg p.1 p.2)
  have hpm := hR1 p.1 p.2
  have hS := cltres_PAQ_le hA G Gt p.1 p.2
  have h1 : ‖G p.1 a₀‖ * ‖Gt b₀ p.2‖ ≤ g * ‖Gt p.1 p.2‖ :=
    mul_le_mul (hg _ _) (hp (b₀, p.2)) (norm_nonneg _) hg0
  have h2 : ‖G p.1 b₀‖ * ‖Gt a₀ p.2‖ ≤ g * ‖Gt p.1 p.2‖ :=
    mul_le_mul (hg _ _) (hp (a₀, p.2)) (norm_nonneg _) hg0
  have hbound : ‖Gt p.1 p.2‖ ≤ g + |t| * (g * ‖Gt p.1 p.2‖ + g * ‖Gt p.1 p.2‖) := by
    calc ‖Gt p.1 p.2‖ = ‖G p.1 p.2 - (t : ℂ) * (G * A * Gt) p.1 p.2‖ := by rw [← hpm]
      _ ≤ ‖G p.1 p.2‖ + ‖(t : ℂ) * (G * A * Gt) p.1 p.2‖ := norm_sub_le _ _
      _ = ‖G p.1 p.2‖ + |t| * ‖(G * A * Gt) p.1 p.2‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ g + |t| * (g * ‖Gt p.1 p.2‖ + g * ‖Gt p.1 p.2‖) := by
          gcongr
          · exact hg _ _
          · exact hS.trans (add_le_add h1 h2)
  have hkey : ‖Gt p.1 p.2‖ ≤ 2 * g := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht) hm0]
  exact (hp (x, y)).trans hkey

/-- **Perturbation, difference bound** (`clt-gij-decay`), the statement `CltPertSubLe`. -/
theorem cltPert_sub_le (ι : Type*) [Fintype ι] [DecidableEq ι] : CltPertSubLe ι := by
  intro M A a₀ b₀ z t gt hM hA hz hgt x y
  set Gt := green (M + (t : ℂ) • A) z with hGt
  set G := green M z with hG
  have hgt0 : 0 ≤ gt := (norm_nonneg _).trans (hgt x y)
  constructor
  · have h := congrFun (congrFun (cltres_R1 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have hS := cltres_PAQ_le hA G Gt x y
    set mx := max ‖G x a₀‖ ‖G x b₀‖ with hmx
    have hmx0 : 0 ≤ mx := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖G x a₀‖ * ‖Gt b₀ y‖ ≤ mx * gt :=
      mul_le_mul (le_max_left _ _) (hgt _ _) (norm_nonneg _) hmx0
    have h2 : ‖G x b₀‖ * ‖Gt a₀ y‖ ≤ mx * gt :=
      mul_le_mul (le_max_right _ _) (hgt _ _) (norm_nonneg _) hmx0
    have hd : Gt x y - G x y = -((t : ℂ) * (G * A * Gt) x y) := by rw [← h]; ring
    rw [hd, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖(G * A * Gt) x y‖ ≤ |t| * (mx * gt + mx * gt) := by
          gcongr; exact hS.trans (add_le_add h1 h2)
      _ = 2 * |t| * gt * mx := by ring
  · have h := congrFun (congrFun (cltres_R2 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at h
    have hS := cltres_PAQ_le hA Gt G x y
    set my := max ‖G a₀ y‖ ‖G b₀ y‖ with hmy
    have hmy0 : 0 ≤ my := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖G b₀ y‖ ≤ gt * my :=
      mul_le_mul (hgt _ _) (le_max_right _ _) (norm_nonneg _) hgt0
    have h2 : ‖Gt x b₀‖ * ‖G a₀ y‖ ≤ gt * my :=
      mul_le_mul (hgt _ _) (le_max_left _ _) (norm_nonneg _) hgt0
    rw [h, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖(Gt * A * G) x y‖ ≤ |t| * (gt * my + gt * my) := by
          gcongr; exact hS.trans (add_le_add h1 h2)
      _ = 2 * |t| * gt * my := by ring

end PerturbThms

section Deriv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
/-- The resolvent along a Hermitian line has derivative `-G A G` (matrix-valued; the ambient norm
is the `L²` operator norm of `RBM.Gauss.hasDerivAt_lineInverse`). -/
private theorem cltres_hasDerivAt_green {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z)
      (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z)) t := by
  have hgr : ∀ s : ℝ, green (M + (s : ℂ) • A) z
      = Ring.inverse (M - z • (1 : Matrix ι ι ℂ) + (s : ℂ) • A) := by
    intro s
    change (M + (s : ℂ) • A - z • (1 : Matrix ι ι ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (M - z • (1 : Matrix ι ι ℂ) + (s : ℂ) • A) := by
    intro s
    have he : M - z • (1 : Matrix ι ι ℂ) + (s : ℂ) • A
        = (M + (s : ℂ) • A) - z • (1 : Matrix ι ι ℂ) := by abel
    rw [he]
    exact RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA s) hz
  have h := hasDerivAt_lineInverse hU t
  simp only [← hgr] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- The entry `(x, y)` of the resolvent along a Hermitian line has derivative
`-(G A G)_{xy}`. -/
private theorem cltres_hasDerivAt_entry {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) (x y : ι) :
    HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z x y)
      (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y) t := by
  have h := cltres_hasDerivAt_green hM hA hz t
  have hl := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℂ x y : Matrix ι ι ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using hl

/-- **Derivative of an entry** (first-order case of `clt-f-total`, proof of `clt-lemma`), the
statement
`CltDerivEntry`. -/
theorem cltDeriv_entry (ι : Type*) [Fintype ι] [DecidableEq ι] : CltDerivEntry ι := by
  intro M A a₀ b₀ z t hM hA hz x y
  refine ⟨cltres_hasDerivAt_entry hM hA.1 hz t x y, fun g hg => ?_⟩
  set Gt := green (M + (t : ℂ) • A) z with hGt
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg x y)
  have hS := cltres_PAQ_le hA Gt Gt x y
  constructor
  · set mx := max ‖Gt x a₀‖ ‖Gt x b₀‖ with hmx
    have hmx0 : 0 ≤ mx := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖Gt b₀ y‖ ≤ mx * g :=
      mul_le_mul (le_max_left _ _) (hg _ _) (norm_nonneg _) hmx0
    have h2 : ‖Gt x b₀‖ * ‖Gt a₀ y‖ ≤ mx * g :=
      mul_le_mul (le_max_right _ _) (hg _ _) (norm_nonneg _) hmx0
    calc ‖(Gt * A * Gt) x y‖ ≤ mx * g + mx * g := hS.trans (add_le_add h1 h2)
      _ = 2 * g * mx := by ring
  · set my := max ‖Gt a₀ y‖ ‖Gt b₀ y‖ with hmy
    have hmy0 : 0 ≤ my := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖Gt b₀ y‖ ≤ g * my :=
      mul_le_mul (hg _ _) (le_max_right _ _) (norm_nonneg _) hg0
    have h2 : ‖Gt x b₀‖ * ‖Gt a₀ y‖ ≤ g * my :=
      mul_le_mul (hg _ _) (le_max_left _ _) (norm_nonneg _) hg0
    calc ‖(Gt * A * Gt) x y‖ ≤ g * my + g * my := hS.trans (add_le_add h1 h2)
      _ = 2 * g * my := by ring

end Deriv

section EvalDeriv

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The spectral parameter of the `σ`-resolvent in `gEntry`. -/
private def cltres_zs (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then spectralZ E u else (starRingEnd ℂ) (spectralZ E u)

private theorem cltres_zs_im {E u : ℝ} (hz : (spectralZ E u).im ≠ 0) (σ : Bool) :
    (cltres_zs E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltres_zs] using hz

/-- **Derivative of the local form** (`clt-f-total-bound-1`, at first order; `clt-ibp-decay`,
`clt-ibp-bound1`, `clt-ibp-bound3`), the statement `CltDerivEval`. -/
theorem cltDeriv_eval_le (L W : ℕ) [NeZero L] [NeZero W] : CltDerivEval L W := by
  intro K F E u M A a₀ b₀ t g φ b hM hA hz hg hφ
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg true 0 0)
  set Gs : Bool → Matrix (Idx L W) (Idx L W) ℂ := fun σ =>
    green (M + (t : ℂ) • A) (cltres_zs E u σ) with hGs
  let Dm : ∀ (j : Fin (K + 1)) (_ : Fin j → Idx L W × Idx L W × Bool), ℂ := fun j q =>
    F.coef (fun _ => b) j q * ∑ i : Fin j,
      (∏ k ∈ Finset.univ.erase i,
        gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
        (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)
  refine ⟨∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool, Dm j q, ?_, ?_⟩
  · unfold cltY LocalForm.eval
    refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun q _ => ?_
    have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin j)))
      (f := fun (i : Fin j) (s : ℝ) =>
        gEntry L W E u (M + (s : ℂ) • A) (q i).2.2 (q i).1 (q i).2.1)
      (f' := fun i => -(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1) (x := t)
      (fun i _ => cltres_hasDerivAt_entry hM hA.1 (cltres_zs_im hz (q i).2.2) t _ _)
    exact hprod.const_mul (F.coef (fun _ => b) j q)
  · have hterm : ∀ (j : Fin (K + 1)) (q : Fin j → Idx L W × Idx L W × Bool),
        ‖Dm j q‖ ≤ 2 * (‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) := by
      intro j q
      by_cases hc : F.coef (fun _ => b) j q = 0
      · simp [Dm, hc]
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
      · have hE : IsEmpty (Fin (j : ℕ)) := ⟨fun i => by have := i.2; omega⟩
        simp [Dm, h0]
      · have hφ' := hφ j q hc
        have hφ0 : 0 ≤ φ := (norm_nonneg _).trans (hφ' ⟨0, hpos⟩ true).1
        have hpow : g ^ (j : ℕ) = g ^ ((j : ℕ) - 1) * g := by
          rw [← pow_succ]; congr 1; omega
        have hi : ∀ i : Fin j,
            ‖(∏ k ∈ Finset.univ.erase i,
              gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
              ≤ g ^ ((j : ℕ) - 1) * (2 * g * φ) := by
          intro i
          rw [smul_eq_mul, norm_mul, norm_neg]
          have hprod : ‖∏ k ∈ Finset.univ.erase i,
              gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
              ≤ g ^ ((j : ℕ) - 1) := by
            rw [norm_prod]
            calc ∏ k ∈ Finset.univ.erase i,
                  ‖gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
                ≤ ∏ _k ∈ Finset.univ.erase i, g :=
                  Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hg _ _ _
              _ = g ^ ((j : ℕ) - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                    Finset.card_univ, Fintype.card_fin]
          have hentry : ‖(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1‖ ≤ 2 * g * φ := by
            have h := ((cltDeriv_entry (Idx L W)) M A a₀ b₀ (cltres_zs E u (q i).2.2) t hM hA
              (cltres_zs_im hz (q i).2.2) (q i).1 (q i).2.1).2 g
              (fun x' y' => hg (q i).2.2 x' y') |>.1
            refine h.trans ?_
            have hm : max ‖Gs (q i).2.2 (q i).1 a₀‖ ‖Gs (q i).2.2 (q i).1 b₀‖ ≤ φ :=
              max_le (hφ' i (q i).2.2).1 (hφ' i (q i).2.2).2
            have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * g)
            exact this
          exact mul_le_mul hprod hentry (norm_nonneg _) (by positivity)
        have hsum : ‖∑ i : Fin j,
            (∏ k ∈ Finset.univ.erase i,
              gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
            ≤ (j : ℝ) * (g ^ ((j : ℕ) - 1) * (2 * g * φ)) := by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc ‖Dm j q‖ = ‖F.coef (fun _ => b) j q‖ * ‖∑ i : Fin j,
              (∏ k ∈ Finset.univ.erase i,
                gEntry L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
                (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖ := norm_mul _ _
          _ ≤ ‖F.coef (fun _ => b) j q‖ * ((j : ℝ) * (g ^ ((j : ℕ) - 1) * (2 * g * φ))) :=
              mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
          _ = 2 * (‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) := by
              rw [hpow]; ring
    calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool, Dm j q‖
        ≤ ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool, ‖Dm j q‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
            2 * (‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun q _ => hterm j q
      _ = 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
            ‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

end EvalDeriv

section EtaEval

private theorem cltres_ck_le_im {κ E : ℝ} (hE : |E| ≤ 2 - κ) : cltCk κ ≤ (spectralM E).im := by
  rw [spectralM_im, cltCk]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private theorem cltres_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltCk κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltCk
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

private theorem cltres_ck_le_one {κ : ℝ} : cltCk κ ≤ 1 := by
  unfold cltCk
  have h : κ * (4 - κ) ≤ 2 ^ 2 := by nlinarith [sq_nonneg (κ - 2)]
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by norm_num)] at this
  linarith

/-- **Lower bound on `Im z_u`** (the spectral-parameter lower bound behind `clt-f-total-bound-2`,
and
`clt-ibp-bound2`/`clt-ibp-bound4`), the statement `CltEtaLower`. -/
theorem cltEta_lower (L W : ℕ) : CltEtaLower L W := by
  intro κ δ E u hκ hδ hE hR
  set N : ℝ := ((((W * L) ^ 2 : ℕ) : ℝ)) with hN
  have hRe : cltCk κ ≤ (spectralM E).im := cltres_ck_le_im hE
  have hck : 0 < cltCk κ := cltres_ck_pos hκ hE
  rw [spectralZ_im]
  rcases Nat.eq_zero_or_pos ((W * L) ^ 2) with h0 | hpos
  · have hN0 : N = 0 := by rw [hN, h0]; simp
    have h1u : 0 ≤ 1 - u := by
      have := Real.rpow_nonneg (le_refl (0 : ℝ)) (-1 + δ)
      rw [hN0] at hR
      linarith
    rw [hN0, div_zero]
    exact mul_nonneg h1u (hck.le.trans hRe)
  · have hN1 : 1 ≤ N := by
      rw [hN]; exact_mod_cast hpos
    have hN0 : 0 < N := by linarith
    have h1 : N⁻¹ ≤ 1 - u := by
      have h2 : N ^ (-1 : ℝ) ≤ N ^ (-1 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
    calc cltCk κ / N = N⁻¹ * cltCk κ := by ring
      _ ≤ (1 - u) * (spectralM E).im := mul_le_mul h1 hRe hck.le (by have := inv_pos.2 hN0; linarith)

variable {L W : ℕ} [NeZero L] [NeZero W]

open scoped Matrix.Norms.L2Operator in
private theorem cltres_gEntry_le (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hH : M.IsHermitian) (σ : Bool) (x y : Idx L W) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E s).im|) : ‖gEntry L W E s M σ x y‖ ≤ η⁻¹ := by
  have hz' : η ≤ |(if σ then spectralZ E s else (starRingEnd ℂ) (spectralZ E s)).im| := by
    cases σ
    · simpa using hz
    · simpa using hz
  have h1 := norm_green_le hH hη hz'
  have h2 := norm_matrix_entry_le_opNorm (green M (if σ then spectralZ E s
    else (starRingEnd ℂ) (spectralZ E s))) x y
  exact h2.trans h1

/-- Private copy of the private `cltm_cltY_le` of `CltMoments.lean`: the
deterministic bound of `cltY` for any Hermitian matrix. -/
private theorem cltres_cltY_le {K : ℕ} (F : LocalForm L W 1 K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hH : M.IsHermitian) {η C : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E s).im|) (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C)
    (hΘ : 1 ≤ 2 * (Fintype.card (Idx L W) : ℝ) ^ 2 * η⁻¹) (b : Z2 L) :
    ‖cltY F E s M b‖ ≤ (K + 1) * C * (2 * (Fintype.card (Idx L W) : ℝ) ^ 2 * η⁻¹) ^ K := by
  set N : ℝ := (Fintype.card (Idx L W) : ℝ) with hN
  set Θ : ℝ := 2 * N ^ 2 * η⁻¹ with hΘdef
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => b) 0 (fun i => i.elim0))
  have hterm : ∀ j : Fin (K + 1), ‖∑ q : Fin j → Idx L W × Idx L W × Bool,
      F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ C * Θ ^ (j : ℕ) := by
    intro j
    calc ‖∑ q : Fin j → Idx L W × Idx L W × Bool,
          F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
        ≤ ∑ q : Fin j → Idx L W × Idx L W × Bool, C * (η⁻¹) ^ (j : ℕ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
          rw [norm_mul, norm_prod]
          refine mul_le_mul (hC _ _ _) ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _) hC0
          calc ∏ i : Fin j, ‖gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
              ≤ ∏ _i : Fin j, η⁻¹ :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
                  cltres_gEntry_le E s M hH _ _ _ hη hz
            _ = (η⁻¹) ^ (j : ℕ) := by simp
      _ = (Fintype.card (Fin j → Idx L W × Idx L W × Bool) : ℝ) * (C * (η⁻¹) ^ (j : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = C * Θ ^ (j : ℕ) := by
          have hcard : (Fintype.card (Fin j → Idx L W × Idx L W × Bool) : ℝ)
              = (2 * N ^ 2) ^ (j : ℕ) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Idx L W) (Idx L W × Bool),
              Fintype.card_prod (Idx L W) Bool, Fintype.card_bool]
            push_cast
            rw [hN]; ring
          rw [hcard, hΘdef, mul_pow]; ring
  unfold cltY LocalForm.eval
  calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
        F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ ∑ j : Fin (K + 1), C * Θ ^ (j : ℕ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ ∑ _j : Fin (K + 1), C * Θ ^ K :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hΘ (by have := j.2; omega)) hC0
    _ = (K + 1) * C * Θ ^ K := by simp; ring

private theorem cltres_card_idx :
    (Fintype.card (Idx L W) : ℝ) = ((((W * L) ^ 2 : ℕ)) : ℝ) := by
  have : Fintype.card (Idx L W) = (W * L) ^ 2 := by
    simp [Idx, Z2, ZMod.card, sq]
  rw [this]

/-- **Deterministic bound of the local form** (`clt-f-total-bound-2`; `clt-ibp-bound2`,
`clt-ibp-bound4`,
`clt-ibp-other-factor-bound`), the statement `CltEvalDetLe`. -/
theorem cltEval_det_le (L W : ℕ) [NeZero L] [NeZero W] : CltEvalDetLe L W := by
  intro κ δ E u K F C' M b hκ hδ hE hR hcoef hH
  set N : ℝ := ((((W * L) ^ 2 : ℕ) : ℝ)) with hN
  have hN1 : 1 ≤ N := by
    have : 0 < (W * L) ^ 2 := pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) 2
    rw [hN]; exact_mod_cast this
  have hN0 : 0 < N := by linarith
  have hck := cltres_ck_pos hκ hE
  have hck1 : cltCk κ ≤ 1 := cltres_ck_le_one
  set η : ℝ := cltCk κ / N with hη
  have hη0 : 0 < η := by positivity
  have hlow : η ≤ (spectralZ E u).im := cltEta_lower L W κ δ E u hκ hδ hE hR
  have him : η ≤ |(spectralZ E u).im| := hlow.trans (le_abs_self _)
  have hΘ : 1 ≤ 2 * (Fintype.card (Idx L W) : ℝ) ^ 2 * η⁻¹ := by
    rw [cltres_card_idx, ← hN, hη, inv_div]
    have : 1 ≤ N / cltCk κ := by rw [le_div_iff₀ hck]; linarith
    nlinarith [sq_nonneg N]
  have := cltres_cltY_le F E u M hH hη0 him (C := N ^ C') hcoef hΘ b
  rw [cltres_card_idx, ← hN, hη, inv_div] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  ring

end EtaEval

section Adj

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem cltres_single_val (c d : Coord L W) :
    ((Pi.single c (1 : ℝ) : Coord L W → ℝ) d : ℝ) = if d = c then 1 else 0 := by
  by_cases h : d = c
  · subst h; simp
  · simp [h]

/-- Entries of `coordinateMatrix c`: modulus `≤ 1`, supported on `{(x,y),(y,x)}`. -/
private theorem cltres_coordEntry (c : Coord L W) (i j : Idx L W) :
    ‖coordinateMatrix L W c i j‖ ≤ 1 ∧
      (coordinateMatrix L W c i j ≠ 0 →
        (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) := by
  obtain ⟨x, y, β⟩ := c
  rw [coordinateMatrix_apply]
  unfold Xentry
  simp only [cltres_single_val]
  split_ifs <;> simp_all

/-- **Adjacency of the blocks of a coordinate** (the restriction to `S_ij ≠ 0`, proof of
`clt-lemma`), the statement `CltCoordAdj`. -/
theorem cltCoord_adj : CltCoordAdj := by
  intro L W _ _ hL c
  refine ⟨fun hg => ?_, fun i j h => (cltres_coordEntry c i j).2 h,
    fun i j => (cltres_coordEntry c i j).1⟩
  have hsv : svar L W c.1 c.2.1 ≠ 0 := by
    intro h0
    apply hg
    apply NNReal.eq
    simp only [gvar, NNReal.coe_zero]
    split_ifs <;> simp [h0] <;> rfl
  unfold svar at hsv
  split_ifs at hsv with hmem
  · exact zdist2_le_one_of_mem_sbSupport L hL hmem
  · exact absurd rfl hsv

end Adj

end RBM.Evol
