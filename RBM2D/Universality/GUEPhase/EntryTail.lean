/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.AuxCarrier
import RBM2D.Universality.GUEPhase.EntryDet
import RBM2D.Green.EntryDom

/-!
# The probabilistic half of Lemma 4.1 at the mixture profile

The mixture matrix `mixMat a b = √a X_band + √b X_GUE` on the OU carrier `ouP = P ⊗ gueP`
(the OU marginal is the mixture at `(e^{-t}, 1 - e^{-t})`), and the statement `GUEEntryMix`
(Lemma 4.1 (4.2)+(4.3) of [YY_25] at the profile `S_u = a S + b N⁻¹`, one-time-law form on `ouP`,
size scale), which is proved as `gueEntryMix`.

Proof of `gueEntryMix` (that of `gueGrid_entry_bound` at the mixture profile):
* `mixSample`, `mixSample_law`: under `ouP` the coordinates `√a ω₁ + √b ω₂` are independent
  centred Gaussians of variance `mixVar a b` for all `a, b ≥ 0` (`ouSample_law` is the case
  `a > 0`, `a + b = 1`).
* the entry variances `sigRow (mixVar a b) i k = Smix a b i k` (`k ≠ i`), the diagonal
  variance, tag-freeness, and the profile hypothesis `MixProfOK`.
* the minor resolvent is `greenMinor` and the measurability of the statistics.
* the four large-deviation tails under `gaussLaw v` through the auxiliary carrier of
  `AuxCarrier.lean`: the row and column sums are the rank-one chaos `auxLinChaos`, the quadratic
  form is `gaussLaw_quad_tail`, the diagonal entry is one Gaussian coordinate (Chernoff bound).
* the deterministic step on the fine lattice, `mixEntry_det`: the LDE inputs stated on `Idx` (the
  form of the tails) are transported to the `BlockIndex` form of `mix_det` through `splitEquiv`.
* the union `mixBad` of the four failure events and its probability, the inclusion of the event of
  the statement in the pull-back of `mixBad` by `mixSample`, and the union over the grid `k ≤ K`
  at one size `n` (the per-`n` form of the `of_det` engine of `Green/EntryDom.lean`:
  `ouP (L n) (W n)` varies with `n`).
* the size scale: `δ_n ≤ N^{-c₀}` against `mixDelta κ L_n` and `mixCdet κ L_n ≲ log² L_n` against
  `N^{τ/2}`, the arithmetic of the union bound.
* `gueEntryMix`: `Φ = N^{τ'}`, `τ' = min (τ/4) c₀`, `q` with `τ'(q+1) ≥ D + n0 + 3`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

/-! ## The mixture matrix and the statement of Lemma 4.1 at the mixture profile -/

section PinEntry

open MeasureTheory RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints RBM.Path

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The mixture matrix `√a X_band + √b X_GUE` on the OU carrier `ouP = P ⊗ gueP`: its entry
variance profile is `a S + b N⁻¹` (`Smix`).  With `(a, b) = (t₁, u - t₁)` it is the one-time law of
the GUE-phase grid path `gueH` ((7.25)/(7.26)); with
`(a, b) = (e^{-t}, 1 - e^{-t})` it is the OU marginal `ouMat t`. -/
def mixMat (a b : ℝ) (ω : Ω L W × Ω L W) : Matrix (Idx L W) (Idx L W) ℂ :=
  Real.sqrt a • Xmat L W ω.1 + Real.sqrt b • Xmat L W ω.2

/-- **`GUEEntryMix`**.  Lemma 4.1 (4.2)+(4.3) of [YY_25] for the profile
`S_u = a S + b N⁻¹`, `u = a + b < 1`, at a polynomially large family of mixture parameters
`(a_{n,k}, b_{n,k})`, `k ≤ K_n ≤ N^{n0}`, in the one-time-law form on `ouP` (the union over the
grid is inside the probability; the coupling across `k` is irrelevant for a union bound):
on the a priori event `‖G - m‖_max ≤ δ_n`, `δ_n ≤ N^{-c₀}`,
`|G_ij - m δ_ij|² ≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W⁻²`, at the energy `E_n` and the spectral
parameter `z_u^{(E)}` with `u = a + b`.
`b = 0` is the band statement (`gbEXPV3`), `a = 0` the flat GUE.  Paper: `lem_GbEXP` ("the proof
... follows Lemma 4.2 of [YY_25]"), the resolvent estimates after `417` ("identical to Section 7.2
of [YY_25]"). -/
def GUEEntryMix : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
  ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ n0 : ℕ, ∀ K : ℕ → ℕ,
  (∀ n, K n ≤ (d.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((d.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    ouP (d.L n) (d.W n) {ω | ∃ (k : Fin (K n + 1)) (i j : Idx (d.L n) (d.W n)),
      ((d.size n : ℕ) : ℝ) ^ τ *
          (maxLoopPM (d.L n) (d.W n) (E n) (a n k + b n k)
              (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat (d.L n) (d.W n) (E n) (a n k + b n k)
              (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) x y ≤ δ n
          then llErrMat (d.L n) (d.W n) (E n) (a n k + b n k)
                (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) i j ^ 2
          else 0)} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

end PinEntry

/-! ## Part 2.1 The coordinates of the mixture matrix and their law -/

section MixSample

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The real coordinates `√a ω₁ + √b ω₂` of the mixture matrix `mixMat a b` on the OU carrier
`ouP` (see the docstring of `mixMat`: with `(a, b) = (t₁, u - t₁)` they are the one-time
coordinates of the GUE-phase grid path). -/
def mixSample (a b : ℝ) (ω : Ω L W × Ω L W) : Ω L W :=
  fun c => Real.sqrt a * ω.1 c + Real.sqrt b * ω.2 c

theorem measurable_mixSample (a b : ℝ) : Measurable (mixSample L W a b) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : Ω L W × Ω L W => ω.1 c :=
    (measurable_pi_apply c).comp measurable_fst
  have h2 : Measurable fun ω : Ω L W × Ω L W => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

/-- `mixMat a b = Xmat (√a ω₁ + √b ω₂)` (as `ouMat_eq_Xmat_ouSample`, by `Xmat_add`, `Xmat_smul`). -/
theorem mixMat_eq_Xmat_mixSample (a b : ℝ) (ω : Ω L W × Ω L W) :
    mixMat L W a b ω = Xmat L W (mixSample L W a b ω) := by
  have h : mixSample L W a b ω = Real.sqrt a • ω.1 + Real.sqrt b • ω.2 := by
    funext c
    simp [mixSample]
  rw [h, Xmat_add, Xmat_smul, Xmat_smul]
  rfl

theorem measurable_mixMat (a b : ℝ) : Measurable (mixMat L W a b) := by
  have hX : Measurable (Xmat L W) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry L W i j
  have h : mixMat L W a b = Xmat L W ∘ mixSample L W a b := by
    funext ω
    exact mixMat_eq_Xmat_mixSample L W a b ω
  rw [h]
  exact hX.comp (measurable_mixSample L W a b)

end MixSample

/-- The law of `α X + β Y` for independent centred Gaussians `X`, `Y`. -/
private theorem mixEntry_pair_map (a b : ℝ) (v₁ v₂ : ℝ≥0) :
    ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      gaussianReal 0
        (NNReal.mk (a ^ 2) (sq_nonneg a) * v₁ + NNReal.mk (b ^ 2) (sq_nonneg b) * v₂) := by
  have h : (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun x : ℝ => a * x) (fun y : ℝ => b * y) := by
    funext p
    rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  have := gaussianReal_conv_gaussianReal (m₁ := a * 0) (m₂ := b * 0)
    (v₁ := NNReal.mk (a ^ 2) (sq_nonneg a) * v₁) (v₂ := NNReal.mk (b ^ 2) (sq_nonneg b) * v₂)
  rw [mul_zero] at this
  simpa [Measure.conv] using this

section MixSampleLaw

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The one-time Gaussian law of the mixture, for every `a, b ≥ 0`**: under `ouP` the
coordinates `√a ω₁ + √b ω₂` are independent centred Gaussians of variance
`a gvar_c + b gueVar_c = mixVar a b c`.  (`ouSample_law` is the case
`(a, b) = (e^{-t}, 1 - e^{-t})`, `a > 0`, `a + b = 1`, and does not contain `a = 0` or `a + b < 1`.)
Proof: that of `ouSample_law`. -/
theorem mixSample_law {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ouP L W).map (mixSample L W a b) = gaussLaw L W (mixVar L W a b) := by
  have hA : NNReal.mk (Real.sqrt a ^ 2) (sq_nonneg _) = a.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ ha]
    exact Real.sq_sqrt ha
  have hB : NNReal.mk (Real.sqrt b ^ 2) (sq_nonneg _) = b.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ hb]
    exact Real.sq_sqrt hb
  refine IsProjectiveLimit.unique ?_
    (Measure.isProjectiveLimit_infinitePi (fun c => gaussianReal 0 (mixVar L W a b c)))
  intro I
  set α : ℝ := Real.sqrt a with hα
  set β : ℝ := Real.sqrt b with hβ
  let f : ℝ × ℝ → ℝ := fun p => α * p.1 + β * p.2
  have hf : Measurable f := by fun_prop
  let R : (Ω L W × Ω L W) → (I → ℝ) × (I → ℝ) := Prod.map I.restrict I.restrict
  let g : (I → ℝ) × (I → ℝ) → (I → ℝ) := fun q i => α * q.1 i + β * q.2 i
  have hR : Measurable R := (Finset.measurable_restrict I).prodMap (Finset.measurable_restrict I)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun i => ?_
    have h1 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    have h2 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (h1.const_mul _).add (h2.const_mul _)
  have hcomp : (fun ω : Ω L W => I.restrict ω) ∘ mixSample L W a b = g ∘ R := by
    funext ω
    rfl
  have hR_map : (ouP L W).map R =
      (Measure.pi fun i : I => gaussianReal 0 (gvar L W i)).prod
        (Measure.pi fun i : I => gaussianReal 0 (Endpoints.gueVar L W i)) := by
    have h1 : (P L W).map I.restrict = Measure.pi fun i : I => gaussianReal 0 (gvar L W i) :=
      Measure.infinitePi_map_restrict _
    have h2 : (Endpoints.gueP L W).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (Endpoints.gueVar L W i) :=
      Measure.infinitePi_map_restrict _
    rw [← h1, ← h2, Measure.map_prod_map _ _ (Finset.measurable_restrict I)
      (Finset.measurable_restrict I)]
    rfl
  have he_map := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i : I => gaussianReal 0 (gvar L W i))
    (fun i : I => gaussianReal 0 (Endpoints.gueVar L W i))).map_eq
  have hge : g ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) = fun x i => f (x i) := by
    funext x i
    rfl
  have : ∀ i : I, SigmaFinite
      (((gaussianReal 0 (gvar L W i)).prod (gaussianReal 0 (Endpoints.gueVar L W i))).map f) :=
    fun i => by
    rw [mixEntry_pair_map]
    infer_instance
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_mixSample L W a b), hcomp,
    ← Measure.map_map hg hR, hR_map, ← he_map, Measure.map_map hg
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).measurable, hge,
    Measure.pi_map_pi (fun i => hf.aemeasurable)]
  congr 1
  funext i
  rw [mixEntry_pair_map, hA, hB]
  rfl

/-- The transfer of a tail bound from `gaussLaw (mixVar a b)` to the carrier `ouP`: for a
measurable event `A` of the coordinates, `ouP (mixSample⁻¹ A) = gaussLaw (mixVar a b) A`. -/
theorem ouP_mixSample_preimage {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {A : Set (Ω L W)}
    (hA : MeasurableSet A) :
    ouP L W (mixSample L W a b ⁻¹' A) = gaussLaw L W (mixVar L W a b) A := by
  rw [← mixSample_law L W ha hb, Measure.map_apply (measurable_mixSample L W a b) hA]

end MixSampleLaw

/-! ## Part 2.2 The entry variances of the mixture (the profile `Smix`) -/

section MixVarId

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `mixVar a b` is tag-free (`gvar` and `gueVar` read only `(c.1, c.2.1)`). -/
theorem mixEntry_mixVar_tagFree (a b : ℝ) : TagFree L W (mixVar L W a b) := fun _ _ => rfl

theorem mixEntry_mixVar_coe {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : Coord L W) :
    (mixVar L W a b c : ℝ) = a * (gvar L W c : ℝ) + b * (Endpoints.gueVar L W c : ℝ) := by
  simp [mixVar, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]

/-- `sigRow gvar i k = S_{ik}` for `k ≠ i` (two real coordinates of variance `S_{ik}/2`). -/
theorem mixEntry_sigRow_gvar {i k : Idx L W} (hik : k ≠ i) :
    sigRow L W (gvar L W) i k = svar L W i k := by
  unfold sigRow rowCoordF
  split_ifs with h
  · rw [gvar_offDiag L W i k true (Ne.symm hik)]
    ring
  · rw [gvar_offDiag L W k i true hik, svar_comm L W k i]
    ring

/-- **The entry variance of the mixture**:
`E|H_{ik}|² = 2 (a gvar_c + b gueVar_c) = a S_{ik} + b N⁻¹ = Smix a b i k` for `k ≠ i`. -/
theorem mixEntry_sigRow_mixVar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {i k : Idx L W} (hik : k ≠ i) :
    sigRow L W (mixVar L W a b) i k = Smix L W a b i k := by
  have h : sigRow L W (mixVar L W a b) i k = a * sigRow L W (gvar L W) i k
      + b * sigRow L W (Endpoints.gueVar L W) i k := by
    unfold sigRow
    rw [mixEntry_mixVar_coe L W ha hb]
    ring
  rw [h, mixEntry_sigRow_gvar L W hik, sigRow_gueVar hik]
  unfold Smix
  rw [div_eq_mul_inv]

/-- The diagonal variance of the mixture: `E (X_{ii})² = a S_{ii} + b N⁻¹ = Smix a b i i`. -/
theorem mixEntry_mixVar_diag {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Idx L W) :
    (mixVar L W a b (i, i, true) : ℝ) = Smix L W a b i i := by
  rw [mixEntry_mixVar_coe L W ha hb, gvar_diag]
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold Smix
  simp only [Endpoints.gueVar, ite_true]
  push_cast
  rw [div_eq_mul_inv]

theorem mixEntry_Smix_diag_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (i : Idx L W) :
    0 < Smix L W a b i i := by
  have hs := svar_diag_pos L W i
  have hN : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold Smix
  rcases ha.eq_or_lt with h0 | h0
  · have hb' : 0 < b := by linarith
    rw [← h0]
    have := div_pos hb' hN
    linarith
  · have := mul_pos h0 hs
    have := div_nonneg hb hN.le
    linarith

end MixVarId

/-! ## Part 2.3 The profile hypothesis, the minor identity, measurability of the statistics -/

section MixBridge

open RBM.Green

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The profile hypothesis**: `S` is symmetric, `E|H_{xy}|² = sigRow v x y = S x y` off the
diagonal
and the diagonal coordinate has variance `S x x`. -/
structure MixProfOK (v : Coord L W → ℝ≥0) (S : Idx L W → Idx L W → ℝ) : Prop where
  symm : ∀ x y, S x y = S y x
  off : ∀ x y, x ≠ y → sigRow L W v x y = S x y
  diag : ∀ x, (v (x, x, true) : ℝ) = S x x

/-- The mixture variances and the profile `Smix` satisfy the profile hypothesis. -/
theorem mixProfOK {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MixProfOK (mixVar L W a b) (Smix L W a b) :=
  ⟨Smix_symm L W a b, fun _ _ hxy => mixEntry_sigRow_mixVar L W ha hb hxy.symm, mixEntry_mixVar_diag L W ha hb⟩

/-- **The minor resolvent is `greenMinor`**: for Hermitian `H` and
`Im z ≠ 0`, `(H^{(i)} - z)⁻¹_{kl} = G_{kl} - G_{ki} G_{il} / G_{ii}`, i.e. (4.9) via the
`inv_minor_resolvent`. -/
theorem mixEntry_minor_eq {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) (k l : {a : ν // a ≠ i}) :
    green (H.submatrix Subtype.val Subtype.val) z k l = greenMinor (green H z) i k.1 l.1 := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_sub_smul_one_of_im_ne_zero hH hz)
  have h := inv_minor_resolvent hdet i (green_diag_ne_zero hH hz i)
  change ((H.submatrix Subtype.val Subtype.val -
    z • (1 : Matrix {a : ν // a ≠ i} {a : ν // a ≠ i} ℂ))⁻¹ : Matrix {a : ν // a ≠ i}
      {a : ν // a ≠ i} ℂ) k l = _
  rw [h]
  rfl

theorem mixEntry_meas_Xmat (k l : Idx L W) : Measurable fun s : Ω L W => Xmat L W s k l :=
  measurable_Xentry L W k l

theorem mixEntry_meas_green {z : ℂ} (hz : z.im ≠ 0) (k l : Idx L W) :
    Measurable fun s : Ω L W => green (Xmat L W s) z k l :=
  ((continuous_green_of_isHermitian (continuous_Xmat L W) (Xmat_isHermitian L W) hz).matrix_elem
    k l).measurable

theorem mixEntry_meas_greenMinor {z : ℂ} (hz : z.im ≠ 0) (i k l : Idx L W) :
    Measurable fun s : Ω L W => greenMinor (green (Xmat L W s) z) i k l := by
  unfold greenMinor
  exact (mixEntry_meas_green hz k l).sub
    (((mixEntry_meas_green hz k i).mul (mixEntry_meas_green hz i l)).div
      (mixEntry_meas_green hz i i))

theorem mixEntry_meas_ldeRowLHS {z : ℂ} (hz : z.im ≠ 0) (i j : Idx L W) :
    Measurable fun s : Ω L W => ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) i j := by
  unfold ldeRowLHS
  exact (Finset.measurable_sum _ fun k _ =>
    (mixEntry_meas_Xmat i k).mul (mixEntry_meas_greenMinor hz i k j)).norm.pow_const 2

theorem mixEntry_meas_ldeRowRHS (S : Idx L W → Idx L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i j : Idx L W) :
    Measurable fun s : Ω L W => ldeRowRHS S (green (Xmat L W s) z) i j := by
  unfold ldeRowRHS
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((mixEntry_meas_greenMinor hz i k j).norm.pow_const 2)

theorem mixEntry_meas_ldeColLHS {z : ℂ} (hz : z.im ≠ 0) (k j : Idx L W) :
    Measurable fun s : Ω L W => ldeColLHS (Xmat L W s) (green (Xmat L W s) z) k j := by
  unfold ldeColLHS
  exact (Finset.measurable_sum _ fun l _ =>
    (mixEntry_meas_greenMinor hz j k l).mul (mixEntry_meas_Xmat l j)).norm.pow_const 2

theorem mixEntry_meas_ldeColRHS (S : Idx L W → Idx L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (k j : Idx L W) :
    Measurable fun s : Ω L W => ldeColRHS S (green (Xmat L W s) z) k j := by
  unfold ldeColRHS
  exact Finset.measurable_sum _ fun l _ =>
    ((mixEntry_meas_greenMinor hz j k l).norm.pow_const 2).mul measurable_const

theorem mixEntry_meas_ldeQuadLHS (S : Idx L W → Idx L W → ℝ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) :
    Measurable fun s : Ω L W => ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) S t i := by
  unfold ldeQuadLHS
  refine ((Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    ((mixEntry_meas_Xmat i k).mul (mixEntry_meas_greenMinor hz i k l)).mul
      (mixEntry_meas_Xmat l i)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (mixEntry_meas_greenMinor hz i k k)))).norm.pow_const 2

theorem mixEntry_meas_ldeQuadRHS (S : Idx L W → Idx L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) :
    Measurable fun s : Ω L W => ldeQuadRHS S (green (Xmat L W s) z) i := by
  unfold ldeQuadRHS
  exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    (measurable_const.mul ((mixEntry_meas_greenMinor hz i k l).norm.pow_const 2)).mul
      measurable_const

theorem mixEntry_meas_diag (i : Idx L W) :
    Measurable fun s : Ω L W => ‖Xmat L W s i i‖ ^ 2 :=
  (mixEntry_meas_Xmat i i).norm.pow_const 2

end MixBridge

/-! ## The four large-deviation tails under `gaussLaw v`

The tails are transferred to the auxiliary carrier of `AuxCarrier.lean`: the event is a function
of `Xmat s` only, `gaussLaw v` is the push-forward of `seqP auxSizes` by the rescaled sample
`auxT v` (`auxT_law`), and the tails are `aux_lin_tail` (row, column) and `gaussLaw_quad_tail`
(quadratic form). -/

section MixTails

open RBM.Green

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Quadratic LDE (4.7) for the resolvent `G` of `Xmat s`**:
`P(λ ∑_{k,l≠i} S_{ik} |G^{(i)}_{kl}|² S_{li} < |Q_i - ∑_k S_{ik} G^{(i)}_{kk}|²) ≤ A_q / λ^{q+1}`.
-/
theorem mixEntry_quad_tail {v : Coord L W → ℝ≥0} {S : Idx L W → Idx L W → ℝ}
    (hv : TagFree L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W) {lam : ℝ}
    (hlam : 0 < lam) (q : ℕ) :
    gaussLaw L W v {s | lam * ldeQuadRHS S (green (Xmat L W s) z) i <
        ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) S 1 i}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gaussLaw_quad_tail hv hz i hlam q
  have hset : {s : Ω L W | lam * ldeQuadRHS S (green (Xmat L W s) z) i <
        ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) S 1 i}
      = {s : Ω L W | lam * quadVqS v z i s < ‖quadQS v z i s‖ ^ 2} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    have hVq : ldeQuadRHS S (green (Xmat L W s) z) i = quadVqS v z i s := by
      unfold ldeQuadRHS quadVqS
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mixEntry_minor_eq (Xmat_isHermitian L W s) hz i k l, ← hS.off i k.1 (Ne.symm k.2),
        hS.symm l.1 i, ← hS.off i l.1 (Ne.symm l.2)]
    have hQ : ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) S 1 i = ‖quadQS v z i s‖ ^ 2 := by
      unfold ldeQuadLHS quadQS
      congr 2
      rw [RowChaos.sum_erase_eq (i := i)]
      · congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [RowChaos.sum_erase_eq (i := i)]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mixEntry_minor_eq (Xmat_isHermitian L W s) hz i k l]
        · rw [RowChaos.sum_erase_eq (i := i), Complex.ofReal_one, one_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← mixEntry_minor_eq (Xmat_isHermitian L W s) hz i k k, ← hS.off i k.1 (Ne.symm k.2)]
    rw [hVq, hQ]
  rw [hset]
  exact h

end MixTails

section MixLinTails

open RBM.Green

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Row LDE (4.8) for the resolvent `G` of `Xmat s`**:
`P(Λ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}|² < |∑_{k≠i} H_{ik} G^{(i)}_{kj}|²) ≤ A_q / ((Λ-1)²)^{q+1}` for
`i ≠ j`, `Λ > 1`: the rank-one chaos `auxLinChaos` of `AuxCarrier.lean` with the coefficient vector
`c_k = G^{(i)}_{kj}` (which does not read the row `i`). -/
theorem mixEntry_row_tail {v : Coord L W → ℝ≥0} {S : Idx L W → Idx L W → ℝ}
    (hv : TagFree L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {i j : Idx L W}
    (hij : i ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw L W v {s | Λ * ldeRowRHS S (green (Xmat L W s) z) i j <
        ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) i j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨j', rfl⟩ : ∃ j' : {a : Idx L W // a ≠ i}, j'.1 = j := ⟨⟨j, Ne.symm hij⟩, rfl⟩
  set c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ :=
    fun ω k => auxMinorRes L W v z i ω k j' with hc_def
  have hc : ∀ k, Continuous fun ω => c ω k := fun k => continuous_auxMinorRes L W v hz i k j'
  have hCb : ∀ ω k, ‖c ω k‖ ≤ |z.im|⁻¹ := fun ω k => norm_auxMinorRes_le L W v hz i ω k j'
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext k
    simp only [c]
    rw [auxMinorRes_congr L W v z i h]
  have hY : ∀ ω, ldeRowLHS (Xmat L W (auxT L W v ω)) (green (Xmat L W (auxT L W v ω)) z) i j'.1
      = ‖∑ k : {a : Idx L W // a ≠ i}, auxHG L W v ω i k.1 * c ω k‖ ^ 2 := by
    intro ω
    change ldeRowLHS (auxHG L W v ω) (green (auxHG L W v ω) z) i j'.1 = _
    unfold ldeRowLHS
    rw [RowChaos.sum_erase_eq (i := i)]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm := mixEntry_minor_eq (auxHG_isHermitian L W v ω) hz i k j'
    exact congrArg (fun x => auxHG L W v ω i k.1 * x) hm.symm
  have hR : ∀ ω, ldeRowRHS S (green (Xmat L W (auxT L W v ω)) z) i j'.1
      = ∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    change ldeRowRHS S (green (auxHG L W v ω) z) i j'.1 = _
    unfold ldeRowRHS
    rw [RowChaos.sum_erase_eq (i := i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm := mixEntry_minor_eq (auxHG_isHermitian L W v ω) hz i k j'
    rw [← hS.off i k.1 (Ne.symm k.2)]
    exact congrArg (fun x => sigRow L W v i k.1 * ‖x‖ ^ 2) hm.symm
  have hR0 : ∀ ω, 0 ≤ ∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos L W v i c hc _ hCb hcf)
    (fun ω => ‖∑ k : {a : Idx L W // a ≠ i}, auxHG L W v ω i k.1 * c ω k‖ ^ 2)
    (fun ω => ∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv i c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq i c hc _ hCb hcf ω) hΛ q
  have hA : MeasurableSet {s : Ω L W | Λ * ldeRowRHS S (green (Xmat L W s) z) i j'.1 <
      ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) i j'.1} :=
    measurableSet_lt ((mixEntry_meas_ldeRowRHS S hz i j'.1).const_mul Λ)
      (mixEntry_meas_ldeRowLHS hz i j'.1)
  have hmap : gaussLaw L W v = (Sizes.seqP auxSizes).map (auxT L W v) := (auxT_law L W v).symm
  rw [hmap, Measure.map_apply (auxT_measurable L W v) hA]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

/-- **Column LDE (4.8) for the resolvent `G` of `Xmat s`**:
for `k ≠ j`, the row `j` of `H` against the conjugated minor row `conj G^{(j)}_{k·}`. -/
theorem mixEntry_col_tail {v : Coord L W → ℝ≥0} {S : Idx L W → Idx L W → ℝ}
    (hv : TagFree L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {k j : Idx L W}
    (hkj : k ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw L W v {s | Λ * ldeColRHS S (green (Xmat L W s) z) k j <
        ldeColLHS (Xmat L W s) (green (Xmat L W s) z) k j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k' : {a : Idx L W // a ≠ j}, k'.1 = k := ⟨⟨k, hkj⟩, rfl⟩
  set c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ j} → ℂ :=
    fun ω l => (starRingEnd ℂ) (auxMinorRes L W v z j ω k' l) with hc_def
  have hc : ∀ l, Continuous fun ω => c ω l := fun l =>
    Complex.continuous_conj.comp (continuous_auxMinorRes L W v hz j k' l)
  have hCb : ∀ ω l, ‖c ω l‖ ≤ |z.im|⁻¹ := fun ω l => by
    simp only [c, Complex.norm_conj]
    exact norm_auxMinorRes_le L W v hz j ω k' l
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W j, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext l
    simp only [c]
    rw [auxMinorRes_congr L W v z j h]
  have hY : ∀ ω, ldeColLHS (Xmat L W (auxT L W v ω)) (green (Xmat L W (auxT L W v ω)) z) k'.1 j
      = ‖∑ l : {a : Idx L W // a ≠ j}, auxHG L W v ω j l.1 * c ω l‖ ^ 2 := by
    intro ω
    change ldeColLHS (auxHG L W v ω) (green (auxHG L W v ω) z) k'.1 j = _
    unfold ldeColLHS
    rw [RowChaos.sum_erase_eq (i := j)]
    have e : ∑ l : {a : Idx L W // a ≠ j}, greenMinor (green (auxHG L W v ω) z) j k'.1 l.1 *
          auxHG L W v ω l.1 j
        = (starRingEnd ℂ) (∑ l : {a : Idx L W // a ≠ j}, auxHG L W v ω j l.1 * c ω l) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hm := mixEntry_minor_eq (auxHG_isHermitian L W v ω) hz j k' l
      have hH : (starRingEnd ℂ) (auxHG L W v ω j l.1) = auxHG L W v ω l.1 j :=
        (auxHG_isHermitian L W v ω).apply l.1 j
      have hc' : c ω l = (starRingEnd ℂ) (greenMinor (green (auxHG L W v ω) z) j k'.1 l.1) := by
        simp only [c]
        exact congrArg (starRingEnd ℂ) hm
      rw [hc', map_mul, Complex.conj_conj, hH]
      ring
    rw [e, Complex.norm_conj]
  have hR : ∀ ω, ldeColRHS S (green (Xmat L W (auxT L W v ω)) z) k'.1 j
      = ∑ l : {a : Idx L W // a ≠ j}, sigRow L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    change ldeColRHS S (green (auxHG L W v ω) z) k'.1 j = _
    unfold ldeColRHS
    rw [RowChaos.sum_erase_eq (i := j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hm := mixEntry_minor_eq (auxHG_isHermitian L W v ω) hz j k' l
    have hc' : ‖c ω l‖ = ‖greenMinor (green (auxHG L W v ω) z) j k'.1 l.1‖ := by
      simp only [c, Complex.norm_conj]
      exact congrArg norm hm
    rw [hc', hS.symm l.1 j, hS.off j l.1 (Ne.symm l.2)]
    ring
  have hR0 : ∀ ω, 0 ≤ ∑ l : {a : Idx L W // a ≠ j}, sigRow L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos L W v j c hc _ hCb hcf)
    (fun ω => ‖∑ l : {a : Idx L W // a ≠ j}, auxHG L W v ω j l.1 * c ω l‖ ^ 2)
    (fun ω => ∑ l : {a : Idx L W // a ≠ j}, sigRow L W v j l.1 * ‖c ω l‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv j c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq j c hc _ hCb hcf ω) hΛ q
  have hA : MeasurableSet {s : Ω L W | Λ * ldeColRHS S (green (Xmat L W s) z) k'.1 j <
      ldeColLHS (Xmat L W s) (green (Xmat L W s) z) k'.1 j} :=
    measurableSet_lt ((mixEntry_meas_ldeColRHS S hz k'.1 j).const_mul Λ)
      (mixEntry_meas_ldeColLHS hz k'.1 j)
  have hmap : gaussLaw L W v = (Sizes.seqP auxSizes).map (auxT L W v) := (auxT_law L W v).symm
  rw [hmap, Measure.map_apply (auxT_measurable L W v) hA]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

end MixLinTails

section MixDiagTail

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Chernoff bound, upper tail, for a centred real Gaussian. -/
private theorem mixEntry_gaussianReal_ge_le {v : ℝ≥0} {t s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- Chernoff bound, lower tail, for a centred real Gaussian. -/
private theorem mixEntry_gaussianReal_le_le {v : ℝ≥0} {t s : ℝ} (hs : s ≤ 0) :
    (gaussianReal 0 v).real {x : ℝ | x ≤ t} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- The two-sided Gaussian tail `P(|g| > t) ≤ 2 exp(-t²/(2v))`. -/
private theorem mixEntry_gaussianReal_tail {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    gaussianReal 0 v {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hsub : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    rcases lt_abs.1 (show t < |x| from hx) with h | h
    · exact Or.inl (show t ≤ x from h.le)
    · exact Or.inr (show x ≤ -t by linarith)
  have h1 : gaussianReal 0 v {x : ℝ | t ≤ x} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((mixEntry_gaussianReal_ge_le (t := t) (s := t / v)
      (by positivity)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  have h2 : gaussianReal 0 v {x : ℝ | x ≤ -t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((mixEntry_gaussianReal_le_le (t := -t) (s := -(t / v))
      (by have : 0 ≤ t / v := by positivity
          linarith)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  calc gaussianReal 0 v {x : ℝ | t < |x|}
      ≤ gaussianReal 0 v ({x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t}) := measure_mono hsub
    _ ≤ gaussianReal 0 v {x : ℝ | t ≤ x} + gaussianReal 0 v {x : ℝ | x ≤ -t} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) +
          ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- **The diagonal entry under `gaussLaw v`**: `X_{ii}` is the
real coordinate `s (i,i,true)`, a centred Gaussian of variance `S_{ii} > 0`, so
`P(Λ S_{ii} < |X_{ii}|²) ≤ 2 exp(-Λ/2)` (Chernoff bound; the two-sided Gaussian tail is that of
`GUELocalSchur.lean`). -/
theorem mixEntry_diag_tail {v : Coord L W → ℝ≥0} {S : Idx L W → Idx L W → ℝ}
    (hS : MixProfOK v S) (i : Idx L W) (hpos : 0 < S i i) {Λ : ℝ} (hΛ : 0 < Λ) :
    gaussLaw L W v {s | Λ * S i i < ‖Xmat L W s i i‖ ^ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-Λ / 2)) := by
  have hXd : ∀ s : Ω L W, Xmat L W s i i = ((s (i, i, true) : ℝ) : ℂ) := fun s => by
    simp [Xmat, Xentry]
  have hvd : (v (i, i, true) : ℝ) = S i i := hS.diag i
  have hvne : v (i, i, true) ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hvd
    linarith
  have ht : 0 < Real.sqrt (Λ * S i i) := Real.sqrt_pos.2 (mul_pos hΛ hpos)
  have hmeas : MeasurableSet {x : ℝ | Real.sqrt (Λ * S i i) < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hiff : ∀ x : ℝ, (Real.sqrt (Λ * S i i) < |x|) ↔ Λ * S i i < x ^ 2 := by
    intro x
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt_sqrt_iff (mul_pos hΛ hpos).le]
  have hset : {s : Ω L W | Λ * S i i < ‖Xmat L W s i i‖ ^ 2} =
      (fun s : Ω L W => s (i, i, true)) ⁻¹' {x : ℝ | Real.sqrt (Λ * S i i) < |x|} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hXd, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    rw [hiff]
  have hmeasf : Measurable (fun s : Ω L W => s (i, i, true)) := measurable_pi_apply _
  have hmap : (gaussLaw L W v).map (fun s : Ω L W => s (i, i, true)) =
      gaussianReal 0 (v (i, i, true)) := Measure.infinitePi_map_eval _ _
  rw [hset, ← Measure.map_apply hmeasf hmeas, hmap]
  refine (mixEntry_gaussianReal_tail hvne ht).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  congr 2
  rw [Real.sq_sqrt (mul_pos hΛ hpos).le, hvd]
  field_simp

end MixDiagTail

/-! ## Part 2.5 From the fine-lattice inputs to `mix_det` (block relabelling, `splitEquiv`)

The four large-deviation inputs of `mix_det` are stated on `BlockIndex` for `blockMat M` and
`greenBlk L W E u M true`; the tails above are stated on `Idx` for `M` and `green M z`.  The two
are related by the relabelling `(splitEquiv L W).symm : BlockIndex L W ≃ Idx L W`. -/

section MixRelabel

open RBM.Green

variable {ν μ : Type*} [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] (f : ν ≃ μ)

private theorem mixEntry_erase_iff (x k : ν) :
    k ∈ (Finset.univ : Finset ν).erase x ↔ f k ∈ (Finset.univ : Finset μ).erase (f x) := by
  simp [Finset.mem_erase, f.injective.eq_iff]

theorem mixEntry_relabel_ldeRowLHS (H G : Matrix μ μ ℂ) (x y : ν) :
    ldeRowLHS (H.submatrix f f) (G.submatrix f f) x y = ldeRowLHS H G (f x) (f y) := by
  unfold ldeRowLHS
  congr 2
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeRowRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x y : ν) :
    ldeRowRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x y = ldeRowRHS S G (f x) (f y) := by
  unfold ldeRowRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeColLHS (H G : Matrix μ μ ℂ) (x y : ν) :
    ldeColLHS (H.submatrix f f) (G.submatrix f f) x y = ldeColLHS H G (f x) (f y) := by
  unfold ldeColLHS
  congr 2
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f y k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeColRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x y : ν) :
    ldeColRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x y = ldeColRHS S G (f x) (f y) := by
  unfold ldeColRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f y k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeQuadLHS (H G : Matrix μ μ ℂ) (S : μ → μ → ℝ) (t : ℝ) (x : ν) :
    ldeQuadLHS (H.submatrix f f) (G.submatrix f f) (fun a b => S (f a) (f b)) t x
      = ldeQuadLHS H G S t (f x) := by
  unfold ldeQuadLHS
  have h1 : ∑ k ∈ Finset.univ.erase x, ∑ l ∈ Finset.univ.erase x,
        (H.submatrix f f) x k * greenMinor (G.submatrix f f) x k l * (H.submatrix f f) l x
      = ∑ k ∈ Finset.univ.erase (f x), ∑ l ∈ Finset.univ.erase (f x),
        H (f x) k * greenMinor G (f x) k l * H l (f x) :=
    Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ =>
      Finset.sum_equiv f (fun l => mixEntry_erase_iff f x l) (fun l _ => rfl))
  have h2 : ∑ k ∈ Finset.univ.erase x, (S (f x) (f k) : ℂ) * greenMinor (G.submatrix f f) x k k
      = ∑ k ∈ Finset.univ.erase (f x), (S (f x) k : ℂ) * greenMinor G (f x) k k :=
    Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)
  rw [h1, h2]

theorem mixEntry_relabel_ldeQuadRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x : ν) :
    ldeQuadRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x = ldeQuadRHS S G (f x) := by
  unfold ldeQuadRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ =>
    Finset.sum_equiv f (fun l => mixEntry_erase_iff f x l) (fun l _ => rfl))

end MixRelabel

section MixDetBridge

open RBM.Green RBM.Path

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `greenBlk L W E u M true` is the fine-lattice resolvent relabelled by `splitEquiv` (the
identity inside the proof of `entryDom_goodEvent_of_llErr`). -/
theorem mixEntry_greenBlk_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    greenBlk L W E u M true
      = (green M (spectralZ E u)).submatrix (splitEquiv L W).symm (splitEquiv L W).symm := by
  rw [greenBlk, Gsig_true, green, blockMat]
  have h1 : M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm -
      spectralZ E u • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix
        (splitEquiv L W).symm (splitEquiv L W).symm := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have : (splitEquiv L W).symm i ≠ (splitEquiv L W).symm j :=
        fun h => hij ((splitEquiv L W).symm.injective h)
      simp [hij, this]
  rw [h1, Matrix.inv_submatrix_equiv]
  rfl

/-- **The deterministic step on the fine lattice**: the four large-deviation inputs of
`mix_det` for `M`, `G = (M - z)⁻¹`, `z = z_{a+b}^{(E)}`, stated on `Idx` (the form of the tails
`mixEntry_*_tail`), give `|(G - m)_{ij}|² ≤ mixCdet κ L Φ² maxLoopPM` for `llErrMat` on the a priori
event `‖G - m‖_max ≤ δ ≤ mixDelta κ L`. -/
theorem mixEntry_det (hL : 3 ≤ L) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {κ E a b : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (hu1 : a + b < 1) {δ Φ : ℝ} (hllErr : ∀ x y, llErrMat L W E (a + b) M x y ≤ δ)
    (hδ : δ ≤ mixDelta κ L) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS M (green M (spectralZ E (a + b))) i j ≤
      Φ * ldeRowRHS (Smix L W a b) (green M (spectralZ E (a + b))) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS M (green M (spectralZ E (a + b))) k j ≤
      Φ * ldeColRHS (Smix L W a b) (green M (spectralZ E (a + b))) k j)
    (hquad : ∀ i, ldeQuadLHS M (green M (spectralZ E (a + b))) (Smix L W a b) 1 i ≤
      Φ * ldeQuadRHS (Smix L W a b) (green M (spectralZ E (a + b))) i)
    (hdiag : ∀ i, ‖M i i‖ ^ 2 ≤ Φ * Smix L W a b i i) (i j : Idx L W) :
    llErrMat L W E (a + b) M i j ^ 2 ≤ mixCdet κ L * Φ ^ 2 * maxLoopPM L W E (a + b) M := by
  have hG := mixEntry_greenBlk_eq (L := L) (W := W) E (a + b) M
  have hΩ := entryDom_goodEvent_of_llErr L W E (a + b) δ M hllErr
  have key := mix_det hL hM hκ hE ha hb hu hu1 hΩ hδ hΦ1 hΦδ
    (fun x y hxy => by
      rw [hG]
      change ldeRowLHS (M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm) _ x y ≤ _
      rw [mixEntry_relabel_ldeRowLHS, mixEntry_relabel_ldeRowRHS (splitEquiv L W).symm
        (Smix L W a b) (green M (spectralZ E (a + b))) x y]
      exact hrow _ _ (fun h => hxy ((splitEquiv L W).symm.injective h)))
    (fun x y hxy => by
      rw [hG]
      change ldeColLHS (M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm) _ x y ≤ _
      rw [mixEntry_relabel_ldeColLHS, mixEntry_relabel_ldeColRHS (splitEquiv L W).symm
        (Smix L W a b) (green M (spectralZ E (a + b))) x y]
      exact hcol _ _ (fun h => hxy ((splitEquiv L W).symm.injective h)))
    (fun x => by
      rw [hG]
      change ldeQuadLHS (M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm) _ _ 1 x ≤ _
      rw [mixEntry_relabel_ldeQuadLHS, mixEntry_relabel_ldeQuadRHS (splitEquiv L W).symm
        (Smix L W a b) (green M (spectralZ E (a + b))) x]
      exact hquad _)
    (fun x => hdiag _) ((splitEquiv L W) i) ((splitEquiv L W) j)
  have hent : ‖(greenBlk L W E (a + b) M true - spectralM E •
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) ((splitEquiv L W) i) ((splitEquiv L W) j)‖ ^ 2
      = llErrMat L W E (a + b) M i j ^ 2 := by
    congr 1
    rw [hG]
    unfold llErrMat
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Equiv.symm_apply_apply, (splitEquiv L W).injective.eq_iff, mul_ite, mul_one,
      mul_zero]
    rfl
  rw [← hent]
  exact key

end MixDetBridge

/-! ## Part 2.6 The union of the four failure events and its probability -/

section MixBad

open RBM.Green

/-- The constant of the common polynomial bound of the three tails: for `Λ ≥ 2`, each of
`A_q / ((Λ-1)²)^{q+1}`, `A_q / Λ^{q+1}`, `2 exp(-Λ/2)` is at most `mixCq q / Λ^{q+1}`. -/
def mixCq (q : ℕ) : ℝ := 4 ^ (q + 1) * hwConst q + 2 ^ (q + 2) * ((q + 1).factorial : ℝ)

theorem mixCq_pos (q : ℕ) : 0 < mixCq q := by
  unfold mixCq
  have := hwConst_pos q
  positivity

theorem mixEntry_tail_row_le {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    hwConst q / ((Λ - 1) ^ 2) ^ (q + 1) ≤ mixCq q / Λ ^ (q + 1) := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : Λ / 4 ≤ (Λ - 1) ^ 2 := by nlinarith
  have h2 : (Λ / 4) ^ (q + 1) ≤ ((Λ - 1) ^ 2) ^ (q + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : hwConst q / ((Λ - 1) ^ 2) ^ (q + 1) ≤ hwConst q / (Λ / 4) ^ (q + 1) :=
    div_le_div_of_nonneg_left (hwConst_pos q).le (by positivity) h2
  have h4 : hwConst q / (Λ / 4) ^ (q + 1) = 4 ^ (q + 1) * hwConst q / Λ ^ (q + 1) := by
    rw [div_pow]
    field_simp
  have h5 : 4 ^ (q + 1) * hwConst q ≤ mixCq q := by
    unfold mixCq
    have : 0 ≤ 2 ^ (q + 2) * ((q + 1).factorial : ℝ) := by positivity
    linarith
  rw [h4] at h3
  exact h3.trans (div_le_div_of_nonneg_right h5 (by positivity))

theorem mixEntry_tail_quad_le {Λ : ℝ} (hΛ : 0 < Λ) (q : ℕ) :
    hwConst q / Λ ^ (q + 1) ≤ mixCq q / Λ ^ (q + 1) := by
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold mixCq
  have h1 : (1 : ℝ) ≤ 4 ^ (q + 1) := one_le_pow₀ (by norm_num)
  have h2 := hwConst_pos q
  have : 0 ≤ 2 ^ (q + 2) * ((q + 1).factorial : ℝ) := by positivity
  nlinarith

theorem mixEntry_tail_diag_le {Λ : ℝ} (hΛ : 0 < Λ) (q : ℕ) :
    2 * Real.exp (-Λ / 2) ≤ mixCq q / Λ ^ (q + 1) := by
  have hfac : (0 : ℝ) < ((q + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h1 := Real.pow_div_factorial_le_exp (x := Λ / 2) (by positivity) (q + 1)
  have hexp : Real.exp (-Λ / 2) = (Real.exp (Λ / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpos : 0 < (Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ) := by positivity
  have h3 : (Real.exp (Λ / 2))⁻¹ ≤ ((Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ))⁻¹ :=
    inv_anti₀ hpos h1
  have h4 : ((Λ / 2) ^ (q + 1) / ((q + 1).factorial : ℝ))⁻¹
      = 2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1) := by
    rw [inv_div, div_pow]
    field_simp
  rw [hexp]
  have h5 : 2 * (Real.exp (Λ / 2))⁻¹ ≤ 2 * (2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1)) :=
    mul_le_mul_of_nonneg_left (h3.trans_eq h4) (by norm_num)
  refine h5.trans ?_
  have h6 : 2 * (2 ^ (q + 1) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1))
      = 2 ^ (q + 2) * ((q + 1).factorial : ℝ) / Λ ^ (q + 1) := by
    rw [pow_succ 2 (q + 1)]
    ring
  rw [h6]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold mixCq
  have := hwConst_pos q
  have h7 : (0 : ℝ) ≤ 4 ^ (q + 1) * hwConst q := by positivity
  linarith

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The union of the four large-deviation failure events** at the mixture `(a, b)`, the spectral
parameter `z` and the factor `Λ`: some row sum (4.8), some column sum (4.8), some quadratic form
(4.7), or some diagonal entry exceeds its proxy by the factor `Λ`.  On the complement, `mix_det`
applies. -/
def mixBad (a b : ℝ) (z : ℂ) (Λ : ℝ) : Set (Ω L W) :=
  (⋃ p : Idx L W × Idx L W, {s | p.1 ≠ p.2 ∧
      Λ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) ∪
  (⋃ p : Idx L W × Idx L W, {s | p.1 ≠ p.2 ∧
      Λ * ldeColRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeColLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) ∪
  (⋃ i : Idx L W, {s | Λ * ldeQuadRHS (Smix L W a b) (green (Xmat L W s) z) i <
      ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) (Smix L W a b) 1 i}) ∪
  (⋃ i : Idx L W, {s | Λ * Smix L W a b i i < ‖Xmat L W s i i‖ ^ 2})

private theorem mixEntry_measurableSet_and {α : Type*} [MeasurableSpace α] {P : Prop}
    {A : Set α} (hA : P → MeasurableSet A) : MeasurableSet {s | P ∧ s ∈ A} := by
  by_cases hP : P
  · have : {s | P ∧ s ∈ A} = A := by ext s; simp [hP]
    rw [this]
    exact hA hP
  · have : {s | P ∧ s ∈ A} = ∅ := by ext s; simp [hP]
    rw [this]
    exact MeasurableSet.empty

private theorem mixEntry_measure_and_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {P : Prop} {A : Set α} {B : ℝ≥0∞} (hA : P → μ A ≤ B) : μ {s | P ∧ s ∈ A} ≤ B := by
  by_cases hP : P
  · have : {s | P ∧ s ∈ A} = A := by ext s; simp [hP]
    rw [this]
    exact hA hP
  · have : {s | P ∧ s ∈ A} = ∅ := by ext s; simp [hP]
    rw [this, measure_empty]
    exact zero_le

theorem mixEntry_measurableSet_mixBad (a b : ℝ) {z : ℂ} (hz : z.im ≠ 0) (Λ : ℝ) :
    MeasurableSet (mixBad (L := L) (W := W) a b z Λ) := by
  unfold mixBad
  refine ((MeasurableSet.union (MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_) ?_))
  · exact MeasurableSet.iUnion fun p => mixEntry_measurableSet_and (A :=
      {s : Ω L W | Λ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) fun _ =>
      measurableSet_lt ((mixEntry_meas_ldeRowRHS _ hz p.1 p.2).const_mul Λ)
        (mixEntry_meas_ldeRowLHS hz p.1 p.2)
  · exact MeasurableSet.iUnion fun p => mixEntry_measurableSet_and (A :=
      {s : Ω L W | Λ * ldeColRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeColLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) fun _ =>
      measurableSet_lt ((mixEntry_meas_ldeColRHS _ hz p.1 p.2).const_mul Λ)
        (mixEntry_meas_ldeColLHS hz p.1 p.2)
  · exact MeasurableSet.iUnion fun i =>
      measurableSet_lt ((mixEntry_meas_ldeQuadRHS _ hz i).const_mul Λ)
        (mixEntry_meas_ldeQuadLHS _ 1 hz i)
  · exact MeasurableSet.iUnion fun i =>
      measurableSet_lt (measurable_const.mul measurable_const) (mixEntry_meas_diag i)

/-- **The probability of the union of the failure events**: for `Λ ≥ 2`, `N = (W L)²` and
`ε = mixCq q / Λ^{q+1}`,
`gaussLaw (mixVar a b) (mixBad a b z Λ) ≤ 4 N² ε`. -/
theorem mixBad_tail {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) {z : ℂ}
    (hz : z.im ≠ 0) {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    gaussLaw L W (mixVar L W a b) (mixBad a b z Λ)
      ≤ ENNReal.ofReal (4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (mixCq q / Λ ^ (q + 1))) := by
  have hv := mixEntry_mixVar_tagFree L W a b
  have hS := mixProfOK (L := L) (W := W) ha hb
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 < Λ := by linarith
  set ε : ℝ := mixCq q / Λ ^ (q + 1) with hε
  have hε0 : 0 ≤ ε := by
    have := mixCq_pos q
    positivity
  set Nn : ℕ := (W * L) ^ 2 with hNn
  have hNn1 : (1 : ℝ) ≤ (Nn : ℝ) := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    exact_mod_cast Nat.one_le_pow _ _ this
  have hcardI : Fintype.card (Idx L W) = Nn := card_Idx L W
  have hcardP : Fintype.card (Idx L W × Idx L W) = Nn * Nn := by
    rw [Fintype.card_prod, hcardI]
  -- the four sums
  have hrow : gaussLaw L W (mixVar L W a b) (⋃ p : Idx L W × Idx L W, {s : Ω L W | p.1 ≠ p.2 ∧
      Λ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) ≤
      ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ p : Idx L W × Idx L W, gaussLaw L W (mixVar L W a b) {s : Ω L W | p.1 ≠ p.2 ∧
        Λ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε := fun p =>
      mixEntry_measure_and_le (A := {s : Ω L W |
        Λ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) _ fun hpp =>
        (mixEntry_row_tail hv hS hz hpp hΛ1 q).trans
          (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardP, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hcol : gaussLaw L W (mixVar L W a b) (⋃ p : Idx L W × Idx L W, {s : Ω L W | p.1 ≠ p.2 ∧
      Λ * ldeColRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
        ldeColLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) ≤
      ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ p : Idx L W × Idx L W, gaussLaw L W (mixVar L W a b) {s : Ω L W | p.1 ≠ p.2 ∧
        Λ * ldeColRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
          ldeColLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε := fun p =>
      mixEntry_measure_and_le (A := {s : Ω L W |
        Λ * ldeColRHS (Smix L W a b) (green (Xmat L W s) z) p.1 p.2 <
          ldeColLHS (Xmat L W s) (green (Xmat L W s) z) p.1 p.2}) _ fun hpp =>
        (mixEntry_col_tail hv hS hz hpp hΛ1 q).trans
          (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardP, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hquad : gaussLaw L W (mixVar L W a b) (⋃ i : Idx L W, {s : Ω L W |
      Λ * ldeQuadRHS (Smix L W a b) (green (Xmat L W s) z) i <
        ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) (Smix L W a b) 1 i}) ≤
      ENNReal.ofReal ((Nn : ℝ) * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ i : Idx L W, gaussLaw L W (mixVar L W a b) {s : Ω L W |
        Λ * ldeQuadRHS (Smix L W a b) (green (Xmat L W s) z) i <
          ldeQuadLHS (Xmat L W s) (green (Xmat L W s) z) (Smix L W a b) 1 i} ≤
        ENNReal.ofReal ε := fun i =>
      (mixEntry_quad_tail hv hS hz i hΛ0 q).trans
        (ENNReal.ofReal_le_ofReal (mixEntry_tail_quad_le hΛ0 q))
    refine (Finset.sum_le_sum fun i _ => hp i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hdiag : gaussLaw L W (mixVar L W a b) (⋃ i : Idx L W, {s : Ω L W |
      Λ * Smix L W a b i i < ‖Xmat L W s i i‖ ^ 2}) ≤ ENNReal.ofReal ((Nn : ℝ) * ε) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hp : ∀ i : Idx L W, gaussLaw L W (mixVar L W a b) {s : Ω L W |
        Λ * Smix L W a b i i < ‖Xmat L W s i i‖ ^ 2} ≤ ENNReal.ofReal ε := fun i =>
      (mixEntry_diag_tail hS i (mixEntry_Smix_diag_pos L W ha hb hu i) hΛ0).trans
        (ENNReal.ofReal_le_ofReal (by
          have := mixEntry_tail_diag_le hΛ0 q
          rw [hε]
          exact this))
    refine (Finset.sum_le_sum fun i _ => hp i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  -- assemble
  unfold mixBad
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add hrow hcol)) hquad)) hdiag).trans ?_
  have hN0 : 0 ≤ (Nn : ℝ) := Nat.cast_nonneg _
  have e1 : ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) + ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε) +
      ENNReal.ofReal ((Nn : ℝ) * ε) + ENNReal.ofReal ((Nn : ℝ) * ε)
      = ENNReal.ofReal ((Nn : ℝ) ^ 2 * ε + (Nn : ℝ) ^ 2 * ε + (Nn : ℝ) * ε + (Nn : ℝ) * ε) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [e1]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (Nn : ℝ) ≤ (Nn : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hε0]

end MixBad

/-! ## The event of the statement is inside the failure events; the union over the grid -/

section MixEvent

open RBM.Green RBM.Path

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The event of the statement (one mixture, one pair) is contained in the failure events**:
outside `mixBad`, the four large-deviation inputs
hold with the factor `Φ`, and `mixEntry_det` (i.e. `mix_det`) gives
`|(G - m)_{ij}|² ≤ mixCdet κ L Φ² maxLoopPM ≤ T maxLoopPM ≤ T (maxLoopPM + W⁻²)` on the a priori
event, which contradicts the strict inequality of the statement. -/
theorem mixEntry_event_subset (hL : 3 ≤ L) {κ E a b δ Φ T : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1)
    (hδ : δ ≤ mixDelta κ L) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hT : mixCdet κ L * Φ ^ 2 ≤ T) :
    {ω : Ω L W × Ω L W | ∃ i j : Idx L W,
      T * (maxLoopPM L W E (a + b) (mixMat L W a b ω) + (((W : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat L W E (a + b) (mixMat L W a b ω) x y ≤ δ
          then llErrMat L W E (a + b) (mixMat L W a b ω) i j ^ 2 else 0)}
      ⊆ mixSample L W a b ⁻¹' mixBad a b (spectralZ E (a + b)) Φ := by
  rintro ω ⟨i, j, hij⟩
  by_contra hnot
  rw [mixMat_eq_Xmat_mixSample] at hij
  set s := mixSample L W a b ω with hs
  have hnot' : s ∉ mixBad a b (spectralZ E (a + b)) Φ := hnot
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (mixCdet_nonneg hκ L) (sq_nonneg Φ)) hT
  have hmL : 0 ≤ maxLoopPM L W E (a + b) (Xmat L W s) := maxLoopPM_nonneg E (a + b) _
  have hW0 : 0 ≤ (((W : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  by_cases hall : ∀ x y, llErrMat L W E (a + b) (Xmat L W s) x y ≤ δ
  · simp only [hall, implies_true, ↓reduceIte] at hij
    have hrow : ∀ i j, i ≠ j → ldeRowLHS (Xmat L W s) (green (Xmat L W s) (spectralZ E (a + b)))
        i j ≤ Φ * ldeRowRHS (Smix L W a b) (green (Xmat L W s) (spectralZ E (a + b))) i j := by
      intro i j hij'
      by_contra h
      have h := not_le.1 h
      apply hnot'
      refine Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨(i, j), hij', h⟩)))
    have hcol : ∀ k j, k ≠ j → ldeColLHS (Xmat L W s) (green (Xmat L W s) (spectralZ E (a + b)))
        k j ≤ Φ * ldeColRHS (Smix L W a b) (green (Xmat L W s) (spectralZ E (a + b))) k j := by
      intro k j hkj
      by_contra h
      have h := not_le.1 h
      apply hnot'
      refine Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨(k, j), hkj, h⟩)))
    have hquad : ∀ i, ldeQuadLHS (Xmat L W s) (green (Xmat L W s) (spectralZ E (a + b)))
        (Smix L W a b) 1 i ≤
        Φ * ldeQuadRHS (Smix L W a b) (green (Xmat L W s) (spectralZ E (a + b))) i := by
      intro i
      by_contra h
      have h := not_le.1 h
      apply hnot'
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, h⟩))
    have hdiag : ∀ i, ‖Xmat L W s i i‖ ^ 2 ≤ Φ * Smix L W a b i i := by
      intro i
      by_contra h
      have h := not_le.1 h
      apply hnot'
      exact Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)
    have hdet := mixEntry_det hL (Xmat_isHermitian L W s) hκ hE ha hb hu hu1 hall hδ hΦ1 hΦδ
      hrow hcol hquad hdiag i j
    have h1 : mixCdet κ L * Φ ^ 2 * maxLoopPM L W E (a + b) (Xmat L W s)
        ≤ T * maxLoopPM L W E (a + b) (Xmat L W s) := mul_le_mul_of_nonneg_right hT hmL
    have h2 : T * maxLoopPM L W E (a + b) (Xmat L W s) ≤
        T * (maxLoopPM L W E (a + b) (Xmat L W s) + (((W : ℕ) : ℝ) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hW0) hT0
    linarith
  · simp only [hall, ↓reduceIte] at hij
    have : 0 ≤ T * (maxLoopPM L W E (a + b) (Xmat L W s) + (((W : ℕ) : ℝ) ^ 2)⁻¹) :=
      mul_nonneg hT0 (add_nonneg hmL hW0)
    linarith

/-- **The union over the grid `k ≤ K` at one size**: the event of the statement has
`ouP`-probability at most
`(K + 1) · 4 N² · mixCq q / Φ^{q+1}`, `N = (W L)²`, for every `q`, whenever the scalar side
conditions hold. -/
theorem mixEntry_union (hL : 3 ≤ L) {κ E δ Φ T : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {K : ℕ}
    {a b : Fin (K + 1) → ℝ} (hab : ∀ k, 0 ≤ a k ∧ 0 ≤ b k ∧ 0 < a k + b k ∧ a k + b k < 1)
    (hδ : δ ≤ mixDelta κ L) (hΦ2 : 2 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hT : mixCdet κ L * Φ ^ 2 ≤ T) (q : ℕ) :
    ouP L W {ω | ∃ (k : Fin (K + 1)) (i j : Idx L W),
      T * (maxLoopPM L W E (a k + b k) (mixMat L W (a k) (b k) ω) +
          (((W : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat L W E (a k + b k) (mixMat L W (a k) (b k) ω) x y ≤ δ
          then llErrMat L W E (a k + b k) (mixMat L W (a k) (b k) ω) i j ^ 2 else 0)}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) *
          (4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)))) := by
  have hΦ1 : 1 ≤ Φ := by linarith
  have hsub : {ω | ∃ (k : Fin (K + 1)) (i j : Idx L W),
      T * (maxLoopPM L W E (a k + b k) (mixMat L W (a k) (b k) ω) +
          (((W : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat L W E (a k + b k) (mixMat L W (a k) (b k) ω) x y ≤ δ
          then llErrMat L W E (a k + b k) (mixMat L W (a k) (b k) ω) i j ^ 2 else 0)}
      ⊆ ⋃ k : Fin (K + 1), mixSample L W (a k) (b k) ⁻¹'
          mixBad (a k) (b k) (spectralZ E (a k + b k)) Φ := by
    rintro ω ⟨k, i, j, hω⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    exact mixEntry_event_subset hL hκ hE ha hb hu hu1 hδ hΦ1 hΦδ hT ⟨i, j, hω⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hk : ∀ k : Fin (K + 1), ouP L W (mixSample L W (a k) (b k) ⁻¹'
      mixBad (a k) (b k) (spectralZ E (a k + b k)) Φ) ≤
      ENNReal.ofReal (4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1))) := by
    intro k
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    rw [ouP_mixSample_preimage L W ha hb (mixEntry_measurableSet_mixBad (a k) (b k)
      (zt_im_ne_zero hκ hE hu1) Φ)]
    exact mixBad_tail ha hb hu (zt_im_ne_zero hκ hE hu1) hΦ2 q
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)) := by
    have := mixCq_pos q
    have : 0 < Φ := by linarith
    positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

end MixEvent

/-! ## Part 2.8 Size-scale bookkeeping: the thresholds, the absorption of the constants

`δ_n ≤ N^{-c₀}` against `mixDelta κ L_n ≳ 1/log L_n`, `mixCdet κ L_n ≲ log² L_n` against `N^{τ/2}`,
and the arithmetic of the union bound. -/

section MixAsymp

open RBM.Green RBM.Path

variable (d : Sizes)

private theorem mixEntry_W_le_size (n : ℕ) : d.W n ≤ d.size n := by
  have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have h1 : d.W n ≤ d.W n * d.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : d.W n * d.L n ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact h1.trans h2

/-- `Kstab2 κ L_n ≤ (size n)^ε` eventually, for every `ε > 0` (the argument of the private
`eventually_Kstab2_le_rpow` of `Green/EntryDom.lean`, from the public
`eventually_Kstab2_mul_rpow_le` and `W ≤ size`). -/
private theorem mixEntry_eventually_Kstab2_le {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Kstab2 κ (d.L n) ≤ ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [eventually_Kstab2_mul_rpow_le d hκ h𝔠 hε hsz hbw] with n hn
  have hW : 0 < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hWε : 0 < (d.W n : ℝ) ^ ε := Real.rpow_pos_of_pos hW ε
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, div_le_iff₀ hWε] at hn
  have hWN : (d.W n : ℝ) ^ ε ≤ ((d.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow hW.le (by exact_mod_cast mixEntry_W_le_size d n) hε.le
  have hpos : 0 ≤ (d.W n : ℝ) ^ ε := hWε.le
  linarith

/-- `mixK κ L_n ≤ (1 + 1/gapK κ) (size n)^ε` eventually. -/
private theorem mixEntry_eventually_mixK_le {κ 𝔠 : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠)
    (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, mixK κ (d.L n) ≤
      (1 + 1 / RBM.KLoop.gapK κ) * ((d.size n : ℕ) : ℝ) ^ ε := by
  filter_upwards [mixEntry_eventually_Kstab2_le d hκ h𝔠 hsz hbw hε] with n hn
  have hg : 0 ≤ 1 + 1 / RBM.KLoop.gapK κ := by
    have : 0 ≤ RBM.KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    positivity
  unfold mixK
  calc Kstab2 κ (d.L n) * (1 + 1 / RBM.KLoop.gapK κ)
      ≤ ((d.size n : ℕ) : ℝ) ^ ε * (1 + 1 / RBM.KLoop.gapK κ) :=
        mul_le_mul_of_nonneg_right hn hg
    _ = _ := mul_comm _ _

/-- `N^{-c₀} ≤ mixDelta κ L_n` eventually: `mixDelta` is `min (1/2) (1/(2 mixK), mixC/2)` and
`mixK ≲ log L_n ≤ N^{c₀/2}`. -/
private theorem mixEntry_eventually_rpow_le_mixDelta {κ 𝔠 c₀ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (h𝔠 : 0 < 𝔠) (hc₀ : 0 < c₀) (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) :
    ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-c₀) ≤ mixDelta κ (d.L n) := by
  have hsz0 : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hc2 : 0 < c₀ / 2 := half_pos hc₀
  have hC := mixC_pos hκ
  have hg : 0 < 1 + 1 / RBM.KLoop.gapK κ := by
    have : 0 < RBM.KLoop.gapK κ := by
      unfold RBM.KLoop.gapK
      refine lt_min one_pos (Real.sqrt_pos.2 ?_)
      nlinarith
    positivity
  filter_upwards [mixEntry_eventually_mixK_le d hκ h𝔠 hsz hbw hc2,
    hsz0.eventually (eventually_le_rpow 2 hc₀),
    hsz0.eventually (eventually_le_rpow (2 / mixC κ) hc₀),
    hsz0.eventually (eventually_le_rpow (2 * (1 + 1 / RBM.KLoop.gapK κ)) hc2),
    hsz.eventually_gt_atTop 0] with n hK h2 h2C h2g hN0
  have hNp : 0 < ((d.size n : ℕ) : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN0 _
  have hneg : ((d.size n : ℕ) : ℝ) ^ (-c₀) = (((d.size n : ℕ) : ℝ) ^ c₀)⁻¹ :=
    Real.rpow_neg hN0.le c₀
  have hK1 := mixK_one_le hκ hκ2 (d.L n)
  unfold mixDelta
  refine le_min ?_ (le_min ?_ ?_)
  · rw [hneg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  · rw [hneg, one_div]
    refine inv_anti₀ (by positivity) ?_
    have hsq : ((d.size n : ℕ) : ℝ) ^ c₀ =
        ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc 2 * mixK κ (d.L n)
        ≤ 2 * ((1 + 1 / RBM.KLoop.gapK κ) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2)) :=
          mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = (2 * (1 + 1 / RBM.KLoop.gapK κ)) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) := by ring
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) * ((d.size n : ℕ) : ℝ) ^ (c₀ / 2) :=
          mul_le_mul_of_nonneg_right h2g (Real.rpow_nonneg hN0.le _)
      _ = _ := hsq.symm
  · rw [hneg]
    calc (((d.size n : ℕ) : ℝ) ^ c₀)⁻¹ ≤ (2 / mixC κ)⁻¹ := inv_anti₀ (by positivity) h2C
      _ = mixC κ / 2 := inv_div _ _

end MixAsymp

section MixAsymp2

open RBM.Green RBM.Path

variable (d : Sizes)

/-- `mixCdet κ L_n ≤ N^{τ/2}` eventually (`mixCdet ≲ mixK² ≲ log² L_n`). -/
private theorem mixEntry_eventually_mixCdet_le {κ 𝔠 τ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (hsz : RBM.Ind.SizeTendsto d) (hbw : Bandwidth d 𝔠) :
    ∀ᶠ n in atTop, mixCdet κ (d.L n) ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2) := by
  have hsz0 : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hτ8 : 0 < τ / 8 := by positivity
  have hτ4 : 0 < τ / 4 := by positivity
  have hC := mixC_pos hκ
  set g : ℝ := 1 + 1 / RBM.KLoop.gapK κ with hgdef
  have hg0 : 0 ≤ g := by
    have : 0 ≤ RBM.KLoop.gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    positivity
  set C0 : ℝ := (2160 * g ^ 2 + 162) * (1 + 3 / mixC κ) with hC0
  filter_upwards [mixEntry_eventually_mixK_le d hκ h𝔠 hsz hbw hτ8,
    hsz0.eventually (eventually_le_rpow C0 hτ4), hsz.eventually_gt_atTop 0] with n hK hC0n hN0
  have hK1 := mixK_one_le hκ hκ2 (d.L n)
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : 1 ≤ d.size n := by exact_mod_cast hN0
    exact_mod_cast this
  have hX1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 4) := Real.one_le_rpow hN1 hτ4.le
  have hsq : (((d.size n : ℕ) : ℝ) ^ (τ / 8)) ^ 2 = ((d.size n : ℕ) : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hK2 : mixK κ (d.L n) ^ 2 ≤ g ^ 2 * ((d.size n : ℕ) : ℝ) ^ (τ / 4) := by
    have h0 : 0 ≤ mixK κ (d.L n) := by linarith
    calc mixK κ (d.L n) ^ 2 ≤ (g * ((d.size n : ℕ) : ℝ) ^ (τ / 8)) ^ 2 :=
          pow_le_pow_left₀ h0 hK 2
      _ = g ^ 2 * (((d.size n : ℕ) : ℝ) ^ (τ / 8)) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have hpoly : 2160 * mixK κ (d.L n) ^ 2 + 162 ≤
      (2160 * g ^ 2 + 162) * ((d.size n : ℕ) : ℝ) ^ (τ / 4) := by nlinarith
  have hhalf : ((d.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((d.size n : ℕ) : ℝ) ^ (τ / 4) * ((d.size n : ℕ) : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have h1C : 0 ≤ 1 + 3 / mixC κ := by positivity
  unfold mixCdet
  calc (2160 * mixK κ (d.L n) ^ 2 + 162) * (1 + 3 / mixC κ)
      ≤ ((2160 * g ^ 2 + 162) * ((d.size n : ℕ) : ℝ) ^ (τ / 4)) * (1 + 3 / mixC κ) :=
        mul_le_mul_of_nonneg_right hpoly h1C
    _ = C0 * ((d.size n : ℕ) : ℝ) ^ (τ / 4) := by rw [hC0]; ring
    _ ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 4) * ((d.size n : ℕ) : ℝ) ^ (τ / 4) :=
        mul_le_mul_of_nonneg_right hC0n (by linarith)
    _ = _ := hhalf.symm

end MixAsymp2

/-- **The arithmetic of the union bound.**  With `N ≥ 1`, `Kn ≤ N^{n0}`, `τ'(q+1) ≥ D + n0 + 3` and
`8 C_q ≤ N`: `(Kn + 1) · 4 N² · C_q / (N^{τ'})^{q+1} ≤ N^{-D}`. -/
private theorem mixEntry_final_arith {N Cq τ' D : ℝ} {Kn n0 q : ℕ} (hN1 : 1 ≤ N)
    (hK : (Kn : ℝ) ≤ N ^ n0) (hq : D + n0 + 3 ≤ τ' * (q + 1)) (hCq0 : 0 ≤ Cq)
    (hCq : 8 * Cq ≤ N) :
    ((Kn : ℝ) + 1) * (4 * N ^ 2 * (Cq / (N ^ τ') ^ (q + 1))) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hpow : (N ^ τ') ^ (q + 1) = N ^ (τ' * (q + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hexp : N ^ (D + n0 + 3) ≤ N ^ (τ' * (q + 1)) := Real.rpow_le_rpow_of_exponent_le hN1 hq
  have hsplit : N ^ (D + n0 + 3) = N ^ D * N ^ n0 * N ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
    norm_num
  have hXD : 0 < N ^ D := Real.rpow_pos_of_pos hN0 D
  have hY1 : 1 ≤ N ^ n0 := one_le_pow₀ hN1
  have hYp : 0 < N ^ n0 := by linarith
  have hneg : N ^ (-D) = (N ^ D)⁻¹ := Real.rpow_neg hN0.le D
  have hden : 0 < N ^ D * N ^ n0 * N ^ 3 := by positivity
  rw [hpow, hneg]
  have h1 : Cq / N ^ (τ' * (q + 1)) ≤ Cq / (N ^ D * N ^ n0 * N ^ 3) := by
    rw [← hsplit]
    exact div_le_div_of_nonneg_left hCq0 (by positivity) hexp
  have h2 : ((Kn : ℝ) + 1) ≤ 2 * N ^ n0 := by linarith
  calc ((Kn : ℝ) + 1) * (4 * N ^ 2 * (Cq / N ^ (τ' * (q + 1))))
      ≤ (2 * N ^ n0) * (4 * N ^ 2 * (Cq / (N ^ D * N ^ n0 * N ^ 3))) := by
        refine mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 (by positivity)) ?_ (by positivity)
        have : 0 ≤ Cq / N ^ (τ' * (q + 1)) := by
          have := Real.rpow_pos_of_pos hN0 (τ' * (q + 1))
          positivity
        positivity
    _ = 8 * Cq / (N ^ D * N) := by
        field_simp
        ring
    _ ≤ N / (N ^ D * N) := by
        refine div_le_div_of_nonneg_right hCq (by positivity)
    _ = (N ^ D)⁻¹ := by
        field_simp

/-- The scalar conditions of `of_det` (`Green/EntryDom.lean`): `δ ≤ N^{-c₀}`, `τ' ≤ c₀`,
`36 ≤ N^{c₀}` give `36 N^{τ'} δ² ≤ 1`. -/
private theorem mixEntry_scalar_36 {N δ c₀ τ' : ℝ} (hN1 : 1 ≤ N) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ N ^ (-c₀)) (hτ'c : τ' ≤ c₀) (hτ'0 : 0 < τ') (h36 : 36 ≤ N ^ c₀) :
    36 * N ^ τ' * δ ^ 2 ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : 0 < N ^ c₀ := Real.rpow_pos_of_pos hN0 c₀
  have hNneg : N ^ (-c₀) = (N ^ c₀)⁻¹ := Real.rpow_neg hN0.le c₀
  have hΦc : N ^ τ' ≤ N ^ c₀ := Real.rpow_le_rpow_of_exponent_le hN1 hτ'c
  have hΦ1 : 1 ≤ N ^ τ' := Real.one_le_rpow hN1 hτ'0.le
  have h1 : δ ^ 2 ≤ (N ^ (-c₀)) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have h2 : N ^ τ' * (N ^ (-c₀)) ^ 2 ≤ N ^ (-c₀) := by
    rw [hNneg]
    have h3 : N ^ τ' * (N ^ c₀)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hNc, one_mul]
      exact hΦc
    calc N ^ τ' * ((N ^ c₀)⁻¹) ^ 2 = (N ^ τ' * (N ^ c₀)⁻¹) * (N ^ c₀)⁻¹ := by ring
      _ ≤ 1 * (N ^ c₀)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (N ^ c₀)⁻¹ := one_mul _
  have h4 : 36 * N ^ (-c₀) ≤ 1 := by
    rw [hNneg, ← div_eq_mul_inv, div_le_one hNc]
    exact h36
  have h5 : 0 ≤ N ^ τ' := by linarith
  calc 36 * N ^ τ' * δ ^ 2 ≤ 36 * (N ^ τ' * (N ^ (-c₀)) ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1 h5
        linarith
    _ ≤ 36 * N ^ (-c₀) := by linarith
    _ ≤ 1 := h4

/-! ## Part 2.9 The theorem `gueEntryMix` -/

section MixMain

open RBM.Green RBM.Path

/-- **`GUEEntryMix` (Lemma 4.1 (4.2)+(4.3) of [YY_25] for the profile `S_u = a S + b N⁻¹`,
one-time-law form on `ouP`, size scale) is proved.**  The deterministic `mix_det` applies outside
the four failure events `mixBad`, whose probabilities are the Gaussian large-deviation
tails of the auxiliary carrier pulled back to `ouP` by `mixSample`
(`mixBad_tail`, `mixSample_law`), with the per-`n` form of the `of_det` engine
(`Green/EntryDom.lean`): `Φ = N^{τ'}`, `τ' = min (τ/4) c₀`, the constants `mixCdet κ L_n`
(`≲ log² L_n`) absorbed by `N^{τ/2}`, and the union bound over `k ≤ K_n ≤ N^{n0}`, `i, j`. -/
theorem gueEntryMix : GUEEntryMix := by
  intro 𝔠 h𝔠 d hAdm κ hκ E hE n0 K hK a b hab c₀ δ hc₀ hδ0 hδ τ D hτ hD
  obtain ⟨hsz0, hbw⟩ := hAdm
  have hsz : RBM.Ind.SizeTendsto d := tendsto_natCast_atTop_iff.mpr hsz0
  have hκ2 : κ ≤ 2 := by
    have := hE 0
    linarith [abs_nonneg (E 0)]
  set τ' : ℝ := min (τ / 4) c₀ with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) hc₀
  have hτ'c : τ' ≤ c₀ := min_le_right _ _
  have hτ'τ : τ' ≤ τ / 4 := min_le_left _ _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, D + n0 + 3 ≤ τ' * (q + 1) := by
    refine ⟨⌈(D + n0 + 3) / τ'⌉₊, ?_⟩
    have h1 := Nat.le_ceil ((D + n0 + 3) / τ')
    rw [div_le_iff₀ hτ'0] at h1
    nlinarith [hτ'0]
  filter_upwards [hsz.eventually_ge_atTop 1, hδ, hsz0.eventually (eventually_le_rpow 36 hc₀),
    hsz0.eventually (eventually_le_rpow 2 hτ'0),
    mixEntry_eventually_rpow_le_mixDelta d hκ hκ2 h𝔠 hc₀ hsz hbw,
    mixEntry_eventually_mixCdet_le d hκ hκ2 h𝔠 hτ hsz hbw,
    hsz.eventually_ge_atTop (8 * mixCq q)] with n hN1 hδn h36 hΦ2 hdelta hcdet hCq
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hδ' : δ n ≤ mixDelta κ (d.L n) := hδn.trans hdelta
  have hΦ1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'0.le
  have hΦδ : 36 * ((d.size n : ℕ) : ℝ) ^ τ' * δ n ^ 2 ≤ 1 :=
    mixEntry_scalar_36 hN1 (hδ0 n) hδn hτ'c hτ'0 h36
  have hΦsq : (((d.size n : ℕ) : ℝ) ^ τ') ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    push_cast
    nlinarith
  have hT : mixCdet κ (d.L n) * (((d.size n : ℕ) : ℝ) ^ τ') ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ τ := by
    calc mixCdet κ (d.L n) * (((d.size n : ℕ) : ℝ) ^ τ') ^ 2
        ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2) * ((d.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul hcdet hΦsq (sq_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = ((d.size n : ℕ) : ℝ) ^ τ := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  have hmain : ouP (d.L n) (d.W n) {ω | ∃ (k : Fin (K n + 1)) (i j : Idx (d.L n) (d.W n)),
      ((d.size n : ℕ) : ℝ) ^ τ *
          (maxLoopPM (d.L n) (d.W n) (E n) (a n k + b n k)
              (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) + (((d.W n : ℕ) : ℝ) ^ 2)⁻¹) <
        (if ∀ x y, llErrMat (d.L n) (d.W n) (E n) (a n k + b n k)
              (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) x y ≤ δ n
          then llErrMat (d.L n) (d.W n) (E n) (a n k + b n k)
                (mixMat (d.L n) (d.W n) (a n k) (b n k) ω) i j ^ 2
          else 0)} ≤
      ENNReal.ofReal (((K n : ℝ) + 1) * (4 * ((d.size n : ℕ) : ℝ) ^ 2 *
        (mixCq q / (((d.size n : ℕ) : ℝ) ^ τ') ^ (q + 1)))) :=
    mixEntry_union (d.three_le_L n) hκ (hE n) (hab n) hδ' hΦ2 hΦδ hT q
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK' : (K n : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ n0 := by exact_mod_cast hK n
  exact mixEntry_final_arith hN1 hK' hq (mixCq_pos q).le hCq

end MixMain

end RBM.Univ

end
