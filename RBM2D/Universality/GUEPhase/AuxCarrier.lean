/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.LDEQuadInst
import RBM2D.Green.IBP
import RBM2D.Universality.OU
import RBM2D.Induction.Split
import RBM2D.Gauss.Domination
import RBM2D.Gauss.GreenTimeCont
import RBM2D.Gauss.Envelope

/-!
# The auxiliary carrier and the row-chaos (LDE) layer of the GUE phase

* The auxiliary carrier `auxSizes` (`L' ≡ 3`, `W' s = max 1 (s / 3)`), the embedding of the fine
  lattice `Idx L W` into its first block, positivity of the auxiliary variance on the image
  (`svar_aux_pos`; it fails on the whole auxiliary lattice because `sbSupport 3` has 5 of 9
  points), and the realisation of an arbitrary variance family `v` by the rescaled auxiliary
  sample (`auxT_law`).
* The law `gaussLaw v` of independent centred Gaussian coordinates, the mixture variance
  `mixVar a b` and its row-sum profile `Smix`.
* The Hanson-Wright tail `chaos_tail` for an arbitrary `RowChaos`.
* The quadratic row chaos `auxQuadChaos` of the auxiliary matrix at row `i`, its identification
  with the centred quadratic form of (4.7) (`auxQuadChaos_chaos`, `auxQuadChaos_Vq`), the tails
  `gaussLaw_quad_tail` (any tag-free variance family) and `gue_quad_tail` (the GUE rows).
* The rank-one row chaos `auxLinChaos` (`|∑_k H_{ik} c_k|² - ∑_k σ_{ik} |c_k|²`, control
  `(∑_k σ_{ik} |c_k|²)²`) and its tail `aux_lin_tail`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

/-! ## The auxiliary carrier, positive on the image of the embedding -/

section Aux

/-- The auxiliary sizes: `L ≡ 3`, `W s = max 1 (s / 3)`.  Only the four fields of `Sizes`
(no bandwidth). -/
def auxSizes : Sizes where
  L _ := 3
  W s := max 1 (s / 3)
  three_le_L _ := le_rfl
  W_pos _ := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- The slot of the auxiliary model used for a fixed size `(L, W)`: `3 · (W L)`, so that the
auxiliary block width is `auxSizes.W slot = W L`. -/
def auxSlot (L W : ℕ) : ℕ := 3 * (W * L)

theorem auxW_slot (L W : ℕ) [NeZero L] [NeZero W] : auxSizes.W (auxSlot L W) = W * L := by
  have hpos : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
  change max 1 (3 * (W * L) / 3) = W * L
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  omega

theorem auxL (_s : ℕ) : auxSizes.L _s = 3 := rfl

/-- The auxiliary lattice points: the fine lattice `Z_{WL}` sits in the first block of
`Z_{3 (W L)}` (block width `W L`). -/
def auxEmb1 (L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    ZMod (auxSizes.W (auxSlot L W) * auxSizes.L (auxSlot L W)) :=
  ((a.val : ℕ) : ZMod (auxSizes.W (auxSlot L W) * auxSizes.L (auxSlot L W)))

theorem auxEmb1_val (L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    (auxEmb1 L W a).val = a.val := by
  unfold auxEmb1
  apply ZMod.val_natCast_of_lt
  have h1 := ZMod.val_lt a
  rw [auxW_slot, auxL]
  nlinarith

theorem auxEmb1_injective (L W : ℕ) [NeZero L] [NeZero W] : Function.Injective (auxEmb1 L W) := by
  intro a b h
  have := congrArg ZMod.val h
  rw [auxEmb1_val, auxEmb1_val] at this
  exact ZMod.val_injective _ this

theorem blk_auxEmb1 (L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    blk (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W)) (auxEmb1 L W a) = 0 := by
  unfold blk
  rw [auxEmb1_val, auxW_slot]
  have h1 := ZMod.val_lt a
  rw [Nat.div_eq_of_lt h1]
  simp

/-- The embedding of the fine lattice `Idx L W` into the first block of the auxiliary lattice. -/
def auxEmb (L W : ℕ) [NeZero L] [NeZero W] (i : Idx L W) :
    Idx (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W)) :=
  (auxEmb1 L W i.1, auxEmb1 L W i.2)

theorem auxEmb_injective (L W : ℕ) [NeZero L] [NeZero W] : Function.Injective (auxEmb L W) := by
  intro i j h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (auxEmb1_injective L W h1) (auxEmb1_injective L W h2)

/-- The coordinate injection `ρ : Coord L W ↪ SeqCoord auxSizes`, at one fixed size. -/
def auxRho (L W : ℕ) [NeZero L] [NeZero W] (c : Coord L W) : auxSizes.SeqCoord :=
  ⟨auxSlot L W, (auxEmb L W c.1, auxEmb L W c.2.1, c.2.2)⟩

theorem auxRho_injective (L W : ℕ) [NeZero L] [NeZero W] : Function.Injective (auxRho L W) := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
  have h2 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  simp only [Prod.mk.injEq] at h2
  obtain ⟨hi, hj, hb⟩ := h2
  rw [auxEmb_injective L W hi, auxEmb_injective L W hj, hb]

/-- **The auxiliary variance is positive on the image of the fine lattice** (both indices lie in
block `(0,0)`, whose difference `0` is in `sbSupport 3`); it is not positive at every coordinate
of the auxiliary model. -/
theorem svar_aux_pos (L W : ℕ) [NeZero L] [NeZero W] (i j : Idx L W) :
    0 < svar (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W)) (auxEmb L W i) (auxEmb L W j) := by
  have hW : (0 : ℝ) < auxSizes.W (auxSlot L W) := Nat.cast_pos.2 (auxSizes.W_pos _)
  have h0 : (0 : Z2 (auxSizes.L (auxSlot L W))) ∈ sbSupport (auxSizes.L (auxSlot L W)) := by
    change ((0 : ZMod (auxSizes.L (auxSlot L W))), (0 : ZMod (auxSizes.L (auxSlot L W)))) ∈
      sbSupport (auxSizes.L (auxSlot L W))
    simp [sbSupport]
  unfold svar
  have hb : ∀ i : Idx L W, (blk (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W))
      (auxEmb L W i).1, blk (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W))
      (auxEmb L W i).2) = (0 : Z2 (auxSizes.L (auxSlot L W))) := fun i =>
    Prod.ext (blk_auxEmb1 L W i.1) (blk_auxEmb1 L W i.2)
  rw [hb i, hb j, sub_self]
  simp only [h0, ↓reduceIte]
  positivity

theorem seqGvar_aux_rho_pos (L W : ℕ) [NeZero L] [NeZero W] (c : Coord L W) :
    0 < (Sizes.seqGvar auxSizes (auxRho L W c) : ℝ) := by
  have h := svar_aux_pos L W c.1 c.2.1
  change 0 < ((if auxEmb L W c.1 = auxEmb L W c.2.1 then
    svar (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W)) (auxEmb L W c.1) (auxEmb L W c.2.1)
    else svar (auxSizes.L (auxSlot L W)) (auxSizes.W (auxSlot L W)) (auxEmb L W c.1)
      (auxEmb L W c.2.1) / 2 : ℝ))
  split_ifs <;> positivity

/-- Reindexing a product Gaussian measure along an injection. -/
theorem aux_infinitePi_map_comp {ι α : Type*} [Nonempty α] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {ρ : α → ι} (hρ : Function.Injective ρ) :
    (Measure.infinitePi μ).map (fun ω : ι → ℝ => fun a => ω (ρ a))
      = Measure.infinitePi (fun a => μ (ρ a)) := by
  classical
  have hmeas : Measurable (fun ω : ι → ℝ => fun a => ω (ρ a)) :=
    measurable_pi_iff.2 fun a => measurable_pi_apply (ρ a)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun a _ => ht a)]
  have hpre : (fun ω : ι → ℝ => fun a => ω (ρ a)) ⁻¹' ((s : Set α).pi t)
      = ((s.map ⟨ρ, hρ⟩ : Finset ι) : Set ι).pi (fun i => t (Function.invFun ρ i)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_image]
    constructor
    · rintro h i ⟨a, ha, rfl⟩
      rw [Function.leftInverse_invFun hρ a]
      exact h a ha
    · intro h a ha
      have := h (ρ a) ⟨a, ha, rfl⟩
      rwa [Function.leftInverse_invFun hρ a] at this
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk, Function.leftInverse_invFun hρ a]

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The scale turning the auxiliary coordinate `ρ c` into a coordinate of variance `v c`. -/
def auxScale (v : Coord L W → ℝ≥0) (c : Coord L W) : ℝ :=
  Real.sqrt ((v c : ℝ) / (Sizes.seqGvar auxSizes (auxRho L W c) : ℝ))

/-- The coordinate map `(T ω) c = s_c · ω (ρ c)`. -/
def auxT (v : Coord L W → ℝ≥0) (ω : Sizes.SeqΩ auxSizes) : Ω L W :=
  fun c => auxScale L W v c * ω (auxRho L W c)

theorem auxT_measurable (v : Coord L W → ℝ≥0) : Measurable (auxT L W v) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _

theorem auxScale_sq (v : Coord L W → ℝ≥0) (c : Coord L W) :
    auxScale L W v c ^ 2 * (Sizes.seqGvar auxSizes (auxRho L W c) : ℝ) = v c := by
  have hg := seqGvar_aux_rho_pos L W c
  unfold auxScale
  rw [Real.sq_sqrt (div_nonneg (v c).coe_nonneg hg.le)]
  field_simp

/-- **Realisation of an arbitrary variance family**: the auxiliary Gaussian sample, rescaled
coordinatewise, has the law of independent centred Gaussians with the prescribed variances `v c`
(zero allowed). -/
theorem auxT_law (v : Coord L W → ℝ≥0) :
    (Sizes.seqP auxSizes).map (auxT L W v)
      = Measure.infinitePi (fun c : Coord L W => gaussianReal 0 (v c)) := by
  have hre : auxT L W v = (fun y : Coord L W → ℝ => fun c => auxScale L W v c * y c) ∘
      (fun ω : Sizes.SeqΩ auxSizes => fun c => ω (auxRho L W c)) := rfl
  have hm1 : Measurable (fun ω : Sizes.SeqΩ auxSizes => fun c => ω (auxRho L W c)) :=
    measurable_pi_iff.2 fun c => measurable_pi_apply _
  have hm2 : ∀ c : Coord L W, Measurable (fun x : ℝ => auxScale L W v c * x) :=
    fun c => measurable_const.mul measurable_id
  rw [hre, ← Measure.map_map (measurable_pi_iff.2 fun c => (measurable_pi_apply c).const_mul _)
    hm1, Sizes.seqP, aux_infinitePi_map_comp _ (auxRho_injective L W)]
  refine (Measure.infinitePi_map_pi
    (μ := fun c : Coord L W => gaussianReal 0 (Sizes.seqGvar auxSizes (auxRho L W c)))
    (f := fun c (x : ℝ) => auxScale L W v c * x) hm2).trans ?_
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  have h := auxScale_sq L W v c
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [← h]

/-- The auxiliary matrix `H = X(T ω)` on the auxiliary carrier. -/
def auxHG (v : Coord L W → ℝ≥0) (ω : Sizes.SeqΩ auxSizes) : Matrix (Idx L W) (Idx L W) ℂ :=
  Xmat L W (auxT L W v ω)

end Aux

/-! ## The variance families and profiles of the GUE phase and of the OU marginal -/

section Mix

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The law of independent centred Gaussian coordinates with variances `v`. -/
def gaussLaw (v : Coord L W → ℝ≥0) : Measure (Ω L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (v c)

/-- `gueP` is `gaussLaw` of the GUE variances; `P` is `gaussLaw` of the band variances. -/
theorem gueP_eq_gaussLaw : Endpoints.gueP L W = gaussLaw L W (Endpoints.gueVar L W) := rfl

/-- The coordinate variance family of `√a X_band + √b X_GUE` (independent): `a gvar + b gueVar`.
It is the family of the GUE-phase grid path at time `u = t₁ + b` (`a = t₁`) and, with
`(a, b) = (e^{-t}, 1 - e^{-t})`, the family `ouVar`. -/
def mixVar (a b : ℝ) (c : Coord L W) : ℝ≥0 :=
  a.toNNReal * gvar L W c + b.toNNReal * Endpoints.gueVar L W c

/-- The entry-variance profile `S_{ij} = a S^{band}_{ij} + b N⁻¹` of `mixVar a b`
(`ζ = b / (a + b)`: `(a + b) · S̃`). -/
def Smix (a b : ℝ) (i j : Idx L W) : ℝ :=
  a * svar L W i j + b / (((W * L) ^ 2 : ℕ) : ℝ)

theorem Smix_symm (a b : ℝ) (i j : Idx L W) : Smix L W a b i j = Smix L W a b j i := by
  simp [Smix, svar_comm L W i j]

theorem Smix_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : Idx L W) :
    0 ≤ Smix L W a b i j := by
  unfold Smix
  have := svar_nonneg L W i j
  positivity

theorem card_Idx : Fintype.card (Idx L W) = (W * L) ^ 2 := by
  simp [Idx, Z2, ZMod.card, sq]

/-- Row sums: `∑_j Smix a b i j = a + b` (`S1 = 1`, `N · N⁻¹ = 1`). -/
theorem sum_Smix_row (hL : 3 ≤ L) (a b : ℝ) (i : Idx L W) :
    ∑ j, Smix L W a b i j = a + b := by
  unfold Smix
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Green.IBP_sum_svar_row hL, Finset.sum_const,
    Finset.card_univ, card_Idx, nsmul_eq_mul]
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  field_simp

theorem sum_Smix_col (hL : 3 ≤ L) (a b : ℝ) (j : Idx L W) :
    ∑ i, Smix L W a b i j = a + b := by
  simp_rw [Smix_symm L W a b _ j]
  exact sum_Smix_row L W hL a b j

end Mix

/-! ## The Hanson–Wright tail for an arbitrary row chaos (generic form of the moment bound) -/

section GenericTail

open RBM.Green

variable {d : Sizes} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem RowChaos_continuous_Vq (C : RowChaos d κ) : Continuous C.Vq := by
  unfold RowChaos.Vq
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact (continuous_const.mul ((C.B_cont k l).norm.pow 2)).mul continuous_const

theorem RowChaos_Vq_congr (C : RowChaos d κ) {ω ω' : Sizes.SeqΩ d}
    (h : ∀ c ∈ C.Ifree, ω c = ω' c) : C.Vq ω = C.Vq ω' := by
  unfold RowChaos.Vq
  rw [C.B_free ω ω' h]

/-- **The `ε`-normalised row chaos, for an arbitrary row chaos** (generic version of
`modelChaosEps`): the matrix divided by `(V_q + ε)^{1/2}`. -/
def chaosEps (C : RowChaos d κ) (ε : ℝ) (hε : 0 < ε) : RowChaos d κ :=
  { C with
    B := fun ω k l => C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (C.B_cont k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp ((RowChaos_continuous_Vq C).add continuous_const).sqrt
      · intro ω
        have : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
        exact_mod_cast this.ne'
    Bbd := C.Bbd / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
      have hge : Real.sqrt ε ≤ Real.sqrt (C.Vq ω + ε) :=
        Real.sqrt_le_sqrt (by linarith [C.Vq_nonneg ω])
      have hεp : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact div_le_div₀ (by
        have := C.B_bdd ω k l
        have h0 : 0 ≤ ‖C.B ω k l‖ := norm_nonneg _
        linarith) (C.B_bdd ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : Real.sqrt (C.Vq ω + ε) = Real.sqrt (C.Vq ω' + ε) := by
        rw [RowChaos_Vq_congr C h]
      funext k l
      rw [C.B_free ω ω' h, hs] }


theorem chaosEps_chaos (C : RowChaos d κ) {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ d) :
    (chaosEps C ε hε).chaos ω = C.chaos ω / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ) := by
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    change C.h ω k * (C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)) * (starRingEnd ℂ) (C.h ω l)
      = C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ((C.sg k : ℝ) : ℂ) * (C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ))
      = ((C.sg k : ℝ) : ℂ) * C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring

theorem chaosEps_Vq (C : RowChaos d κ) {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ d) :
    (chaosEps C ε hε).Vq ω = C.Vq ω / (C.Vq ω + ε) := by
  have hpos : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
  have hsq : Real.sqrt (C.Vq ω + ε) ^ 2 = C.Vq ω + ε :=
    Real.sq_sqrt (by linarith [C.Vq_nonneg ω])
  have hpt : ∀ k l : κ, (chaosEps C ε hε).sg k * ‖(chaosEps C ε hε).B ω k l‖ ^ 2 *
        (chaosEps C ε hε).sg l = (C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) / (C.Vq ω + ε) := by
    intro k l
    change C.sg k * ‖C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)‖ ^ 2 * C.sg l = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
    ring
  have hd : ∀ (A : κ → κ → ℝ) (c : ℝ), (∑ k, ∑ l, A k l / c) = (∑ k, ∑ l, A k l) / c := by
    intro A c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_div _ _ _).symm
  unfold RowChaos.Vq
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l,
    hd (fun k l => C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) (C.Vq ω + ε)]
  rfl

theorem chaosEps_Vq_le_one (C : RowChaos d κ) {ε : ℝ} (hε : 0 < ε)
    (ω : Sizes.SeqΩ d) : (chaosEps C ε hε).Vq ω ≤ 1 := by
  rw [chaosEps_Vq C hε ω]
  have h0 := C.Vq_nonneg ω
  rw [div_le_one (by linarith)]
  linarith

/-- **`E[(|Q|²/(V_q+ε))^{q+1}] ≤ A_{q+1}` for an arbitrary row chaos**, uniformly in `ε`. -/
theorem chaosEps_mom_le (C : RowChaos d κ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (chaosEps C ε hε).mom (q + 1) ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) := by
  have h := (chaosEps C ε hε).mom_le_momVpow (gaussIBP d) q
  have hV : (chaosEps C ε hε).momVpow (q + 1) ≤ 1 := by
    change (∫ ω, (chaosEps C ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP d)) ≤ 1
    calc ∫ ω, (chaosEps C ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP d)
        ≤ ∫ _ω : Sizes.SeqΩ d, (1 : ℝ) ∂(Sizes.seqP d) :=
          MeasureTheory.integral_mono
            ((chaosEps C ε hε).integrable_Vq_pow (gaussIBP d) (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω) (chaosEps_Vq_le_one C hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) := by positivity
  refine h.trans ?_
  calc ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * (chaosEps C ε hε).momVpow (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * 1 :=
        mul_le_mul_of_nonneg_left hV hc
    _ = _ := mul_one _


/-- **Markov at fixed `ε`** for an arbitrary row chaos. -/
theorem chaos_tail_eps (C : RowChaos d κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    (Sizes.seqP d) {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := chaosEps C ε hε with hC'
  set Y : Sizes.SeqΩ d → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (Sizes.seqP d) := by
    simpa only [habs] using C'.integrable_norm_pow (gaussIBP d) (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(Sizes.seqP d)) ≤ hwConst q :=
    chaosEps_mom_le C hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(Sizes.seqP d) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := Sizes.seqP d) (Y := Y) ht hint hmom
  have hset : {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2} = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (C.Vq ω + ε) := ⟨_, rfl⟩
    have hs : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
    have hsq : s ^ 2 = C.Vq ω + ε := by
      rw [hsdef]; exact Real.sq_sqrt (by linarith [C.Vq_nonneg ω])
    have hYv : Y ω = ‖C.chaos ω‖ / s := by
      show ‖C'.chaos ω‖ = _
      rw [hC', chaosEps_chaos C hε ω, norm_div, Complex.norm_real, Real.norm_eq_abs, ← hsdef,
        abs_of_nonneg hs.le]
    have hc : (0 : ℝ) ≤ ‖C.chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs, ← hsq]
    constructor
    · intro h
      nlinarith [h, hs, hc, hsl, hsln, sq_nonneg (Real.sqrt lam * s - ‖C.chaos ω‖),
        sq_nonneg (Real.sqrt lam * s + ‖C.chaos ω‖)]
    · intro h
      have hms := mul_self_lt_mul_self (mul_nonneg hsln hs.le) h
      nlinarith [hms, hsl, hs]
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

/-- **Hanson–Wright tail for an arbitrary row chaos with its random control**:
`P(λ V_q < |Q|²) ≤ A_q / λ^{q+1}`, the `ε → 0` limit of `chaos_tail_eps` by continuity of the
measure from below.  Generic: `meas_lt_normSq_chaos_le` proves this for the band instance
`modelChaos` only. -/
theorem chaos_tail (C : RowChaos d κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (Sizes.seqP d) {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set S : ℕ → Set (Sizes.SeqΩ d) := fun m =>
    {ω | lam * (C.Vq ω + 1 / ((m : ℝ) + 1)) < ‖C.chaos ω‖ ^ 2} with hS
  have hmono : Monotone S := by
    intro m m' hmm ω hω
    simp only [hS, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmm' : ((m : ℝ) + 1) ≤ ((m' : ℝ) + 1) := by
        have : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm
        linarith
      exact one_div_le_one_div_of_le hm hmm'
    nlinarith [hω, h1, hlam]
  have hunion : (⋃ m, S m) = {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      nlinarith [hm, hlam, hpos]
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (‖C.chaos ω‖ ^ 2 - lam * C.Vq ω) / lam by
          apply div_pos _ hlam; linarith)
      refine ⟨m, ?_⟩
      rw [lt_div_iff₀ hlam] at hm
      nlinarith [hm]
  rw [← hunion]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := Sizes.seqP d) hmono)
    (Filter.Eventually.of_forall fun m => ?_)
  exact chaos_tail_eps C hlam q (by positivity)

end GenericTail

/-! ## The row chaos on the auxiliary carrier

The Gaussian row `(H_{ik})_{k ≠ i}` of the rescaled auxiliary matrix `auxHG v ω` is
`H_{ik} = λ_{ik} (ω_{ρ c_re} + ε_{ik} i ω_{ρ c_im})`: a `RowChaos auxSizes` with `r = 1` and the
matrix `B_{kl} = λ_k G^{(i)}_{kl} λ_l` (the scales `λ_{ik} = s_c` of the auxiliary carrier are
absorbed into `B`), so that the moment bound applies to the quadratic form of (4.7) *for any
variance family `v`*, in particular `v = mixVar a b` and `v = gueVar` (the GUE local law). -/

section AuxRowChaos

open RBM.Green

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The coordinate carrying the real (`true`) or imaginary (`false`) part of `X_{ik}`. -/
def rowCoordF (i k : Idx L W) (b : Bool) : Coord L W :=
  if idxKey L W i < idxKey L W k then (i, k, b) else (k, i, b)

/-- The sign with which the imaginary coordinate enters `X_{ik}`. -/
def rowSignF (i k : Idx L W) : ℝ := if idxKey L W i < idxKey L W k then 1 else -1

theorem Xentry_eq_rowCoordF {i k : Idx L W} (hik : i ≠ k) (s : Ω L W) :
    Xentry L W s i k = (s (rowCoordF L W i k true) : ℂ)
      + (rowSignF L W i k : ℂ) * Complex.I * (s (rowCoordF L W i k false) : ℂ) := by
  have hkey : idxKey L W i ≠ idxKey L W k := fun h => hik (idxKey_injective L W h)
  unfold Xentry rowCoordF rowSignF
  rcases lt_or_gt_of_ne hkey with h | h
  · simp only [h, ↓reduceIte]
    push_cast
    ring
  · have h' : ¬ idxKey L W i < idxKey L W k := by omega
    simp only [h', ↓reduceIte, h]
    push_cast
    ring

theorem rowCoordF_injOn {i k l : Idx L W} {b c : Bool} (hk : k ≠ i) (hl : l ≠ i)
    (h : rowCoordF L W i k b = rowCoordF L W i l c) : k = l ∧ b = c := by
  unfold rowCoordF at h
  split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq] at h
  · exact ⟨h.2.1, h.2.2⟩
  · exact absurd h.1.symm hl
  · exact absurd h.1 hk
  · exact ⟨h.1, h.2.2⟩

/-- Tag-free variance family: the real and imaginary coordinates of an entry have the same
variance (true for `mixVar` and `gueVar`). -/
def TagFree (v : Coord L W → ℝ≥0) : Prop := ∀ i j : Idx L W, v (i, j, true) = v (i, j, false)

theorem seqGvar_auxRho_tag (i j : Idx L W) :
    Sizes.seqGvar auxSizes (auxRho L W (i, j, true))
      = Sizes.seqGvar auxSizes (auxRho L W (i, j, false)) := rfl

theorem auxScale_tag {v : Coord L W → ℝ≥0} (hv : TagFree L W v) (i j : Idx L W) :
    auxScale L W v (i, j, false) = auxScale L W v (i, j, true) := by
  unfold auxScale
  rw [seqGvar_auxRho_tag, hv i j]

/-- **The entry `H_{ik}` of the auxiliary matrix** in terms of the two row coordinates of the
auxiliary carrier: `λ_{ik} (ω_{ρ c_re} + ε i ω_{ρ c_im})`. -/
theorem auxHG_apply {v : Coord L W → ℝ≥0} (hv : TagFree L W v) {i k : Idx L W} (hik : i ≠ k)
    (ω : Sizes.SeqΩ auxSizes) :
    auxHG L W v ω i k = (auxScale L W v (rowCoordF L W i k true) : ℂ) *
      ((ω (auxRho L W (rowCoordF L W i k true)) : ℂ) + (rowSignF L W i k : ℂ) * Complex.I *
        (ω (auxRho L W (rowCoordF L W i k false)) : ℂ)) := by
  unfold auxHG
  rw [Xmat_apply, Xentry_eq_rowCoordF L W hik]
  have h : auxScale L W v (rowCoordF L W i k false) = auxScale L W v (rowCoordF L W i k true) := by
    unfold rowCoordF; split_ifs <;> exact auxScale_tag L W hv _ _
  simp only [auxT, h]
  push_cast
  ring

/-- The `i`-th row scale `λ_{ik}` of the auxiliary matrix. -/
def lamRow (v : Coord L W → ℝ≥0) (i k : Idx L W) : ℝ := auxScale L W v (rowCoordF L W i k true)

theorem lamRow_nonneg (v : Coord L W → ℝ≥0) (i k : Idx L W) : 0 ≤ lamRow L W v i k :=
  Real.sqrt_nonneg _

theorem continuous_auxT (v : Coord L W → ℝ≥0) : Continuous (auxT L W v) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem continuous_auxHG (v : Coord L W → ℝ≥0) : Continuous (auxHG L W v) :=
  (continuous_Xmat L W).comp (continuous_auxT L W v)

theorem auxHG_isHermitian (v : Coord L W → ℝ≥0) (ω : Sizes.SeqΩ auxSizes) :
    (auxHG L W v ω).IsHermitian :=
  Xmat_isHermitian L W _

/-- The minor resolvent `(H^{(i)} - z)⁻¹` of the auxiliary matrix. -/
def auxMinorRes (v : Coord L W → ℝ≥0) (z : ℂ) (i : Idx L W) (ω : Sizes.SeqΩ auxSizes) :
    Matrix {a : Idx L W // a ≠ i} {a : Idx L W // a ≠ i} ℂ :=
  green ((auxHG L W v ω).submatrix Subtype.val Subtype.val) z

section MinorBounds

open scoped Matrix.Norms.L2Operator

theorem norm_auxMinorRes_le (v : Coord L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W)
    (ω : Sizes.SeqΩ auxSizes) (k l : {a : Idx L W // a ≠ i}) :
    ‖auxMinorRes L W v z i ω k l‖ ≤ |z.im|⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ k l).trans
    (RBM.Gauss.norm_green_le ((auxHG_isHermitian L W v ω).submatrix _) (abs_pos.2 hz) le_rfl)

end MinorBounds

theorem continuous_auxMinorRes (v : Coord L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W)
    (k l : {a : Idx L W // a ≠ i}) : Continuous fun ω => auxMinorRes L W v z i ω k l := by
  have h := RBM.Gauss.continuous_green_of_isHermitian
    (f := fun ω : Sizes.SeqΩ auxSizes => (auxHG L W v ω).submatrix Subtype.val Subtype.val)
    ((continuous_auxHG L W v).matrix_submatrix (Subtype.val : {a : Idx L W // a ≠ i} → Idx L W)
      (Subtype.val : {a : Idx L W // a ≠ i} → Idx L W))
    (fun ω => (auxHG_isHermitian L W v ω).submatrix _) hz
  exact h.matrix_elem k l

open Classical in
/-- The coordinates of the auxiliary carrier that the minor `H^{(i)}` can read. -/
def auxOffRow (i : Idx L W) : Finset (Sizes.SeqCoord auxSizes) :=
  ((Finset.univ : Finset (Coord L W)).filter (fun c => c.1 ≠ i ∧ c.2.1 ≠ i)).image (auxRho L W)

theorem Xentry_congr_offRow {i k l : Idx L W} (hk : k ≠ i) (hl : l ≠ i) {s s' : Ω L W}
    (h : ∀ c : Coord L W, c.1 ≠ i → c.2.1 ≠ i → s c = s' c) :
    Xentry L W s k l = Xentry L W s' k l := by
  unfold Xentry
  split_ifs
  · simp [h (k, l, true) hk hl, h (k, l, false) hk hl]
  · simp [h (l, k, true) hl hk, h (l, k, false) hl hk]
  · simp [h (k, l, true) hk hl]

theorem auxMinorRes_congr (v : Coord L W → ℝ≥0) (z : ℂ) (i : Idx L W)
    {ω ω' : Sizes.SeqΩ auxSizes} (h : ∀ c ∈ auxOffRow L W i, ω c = ω' c) :
    auxMinorRes L W v z i ω = auxMinorRes L W v z i ω' := by
  unfold auxMinorRes
  congr 1
  ext k l
  simp only [Matrix.submatrix_apply, auxHG, Xmat_apply]
  apply Xentry_congr_offRow L W k.2 l.2
  intro c hc1 hc2
  simp only [auxT]
  have hmem : auxRho L W c ∈ auxOffRow L W i := by
    classical
    unfold auxOffRow
    exact Finset.mem_image.2 ⟨c, by simp [hc1, hc2], rfl⟩
  rw [h _ hmem]

/-- **The quadratic row chaos of the auxiliary matrix at row `i`**: coordinates
`ρ (rowCoordF i k b)`, signs
`rowSignF`, scale `r = 1`, matrix `B_{kl} = λ_k G^{(i)}_{kl} λ_l` (continuous, bounded, off-row). -/
noncomputable def auxQuadChaos (v : Coord L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W) :
    RowChaos auxSizes {a : Idx L W // a ≠ i} where
  co k b := auxRho L W (rowCoordF L W i k.1 b)
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoordF_injOn L W hk hl (auxRho_injective L W h)
    subst h1; subst h2; rfl
  gvar_tag k := by
    unfold rowCoordF
    split_ifs <;> exact_mod_cast (seqGvar_auxRho_tag L W _ _).symm
  eps k := rowSignF L W i k.1
  eps_sq k := by unfold rowSignF; split_ifs <;> norm_num
  r := 1
  B ω k l := (lamRow L W v i k.1 : ℂ) * auxMinorRes L W v z i ω k l * (lamRow L W v i l.1 : ℂ)
  B_cont k l := (continuous_const.mul (continuous_auxMinorRes L W v hz i k l)).mul continuous_const
  Bbd := (∑ k : {a : Idx L W // a ≠ i}, lamRow L W v i k.1) ^ 2 * |z.im|⁻¹
  B_bdd ω k l := by
    have hk : lamRow L W v i k.1 ≤ ∑ j : {a : Idx L W // a ≠ i}, lamRow L W v i j.1 :=
      Finset.single_le_sum (f := fun j : {a : Idx L W // a ≠ i} => lamRow L W v i j.1)
        (fun j _ => lamRow_nonneg L W v i j.1) (Finset.mem_univ k)
    have hl : lamRow L W v i l.1 ≤ ∑ j : {a : Idx L W // a ≠ i}, lamRow L W v i j.1 :=
      Finset.single_le_sum (f := fun j : {a : Idx L W // a ≠ i} => lamRow L W v i j.1)
        (fun j _ => lamRow_nonneg L W v i j.1) (Finset.mem_univ l)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg L W v i k.1),
      abs_of_nonneg (lamRow_nonneg L W v i l.1)]
    have hG := norm_auxMinorRes_le L W v hz i ω k l
    have h0 := lamRow_nonneg L W v i k.1
    have h1 := lamRow_nonneg L W v i l.1
    calc lamRow L W v i k.1 * ‖auxMinorRes L W v z i ω k l‖ * lamRow L W v i l.1
        ≤ (∑ j : {a : Idx L W // a ≠ i}, lamRow L W v i j.1) * |z.im|⁻¹ *
          (∑ j : {a : Idx L W // a ≠ i}, lamRow L W v i j.1) := by
          apply mul_le_mul _ hl h1
            (mul_nonneg (Finset.sum_nonneg fun j _ => lamRow_nonneg L W v i j.1) (by positivity))
          exact mul_le_mul hk hG (norm_nonneg _) (h0.trans hk)
      _ = _ := by ring
  Ifree := auxOffRow L W i
  Ifree_free k b := by
    classical
    unfold auxOffRow
    intro hmem
    obtain ⟨c, hc, hc'⟩ := Finset.mem_image.1 hmem
    have hc2 : c = rowCoordF L W i k.1 b := auxRho_injective L W hc'
    have hc3 := (Finset.mem_filter.1 hc).2
    rw [hc2] at hc3
    unfold rowCoordF at hc3
    split_ifs at hc3 with h
    · exact hc3.1 rfl
    · exact hc3.2 rfl
  B_free ω ω' h := by
    funext k l
    rw [auxMinorRes_congr L W v z i h]

/-- The variance `E|H_{ik}|² = 2 v_{(i,k)}` of the entry `(i, k)` (two real coordinates). -/
def sigRow (v : Coord L W → ℝ≥0) (i k : Idx L W) : ℝ := 2 * (v (rowCoordF L W i k true) : ℝ)

variable {L W}

theorem auxQuadChaos_sg {v : Coord L W → ℝ≥0} {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W)
    (k : {a : Idx L W // a ≠ i}) :
    (auxQuadChaos L W v hz i).sg k * lamRow L W v i k.1 ^ 2 = sigRow L W v i k.1 := by
  have h := auxScale_sq L W v (rowCoordF L W i k.1 true)
  change 2 * (1 : ℝ) ^ 2 * (Sizes.seqGvar auxSizes (auxRho L W (rowCoordF L W i k.1 true)) : ℝ) *
      auxScale L W v (rowCoordF L W i k.1 true) ^ 2 = 2 * (v (rowCoordF L W i k.1 true) : ℝ)
  rw [← h]
  ring

/-- **The row of the chaos is the `i`-th row of the auxiliary matrix**, up to the scale `λ_{ik}`. -/
theorem auxQuadChaos_h {v : Coord L W → ℝ≥0} (hv : TagFree L W v) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) (ω : Sizes.SeqΩ auxSizes) (k : {a : Idx L W // a ≠ i}) :
    auxHG L W v ω i k.1 = (lamRow L W v i k.1 : ℂ) * (auxQuadChaos L W v hz i).h ω k := by
  rw [auxHG_apply L W hv (Ne.symm k.2)]
  change _ = (lamRow L W v i k.1 : ℂ) * (((1 : ℝ) : ℂ) *
    ((ω (auxRho L W (rowCoordF L W i k.1 true)) : ℂ) + ((rowSignF L W i k.1 : ℝ) : ℂ) * Complex.I *
      (ω (auxRho L W (rowCoordF L W i k.1 false)) : ℂ)))
  unfold lamRow
  push_cast
  ring

theorem auxHG_swap (v : Coord L W → ℝ≥0) (ω : Sizes.SeqΩ auxSizes) (k l : Idx L W) :
    auxHG L W v ω l k = (starRingEnd ℂ) (auxHG L W v ω k l) :=
  Xentry_swap L W _ k l

/-- **The chaos is the quadratic form of (4.7), centred**: for the auxiliary matrix `H`,
`Q_i - ∑_k E|H_{ik}|² G^{(i)}_{kk}` with `Q_i = ∑_{k,l ≠ i} H_{ik} G^{(i)}_{kl} H_{li}`. -/
theorem auxQuadChaos_chaos {v : Coord L W → ℝ≥0} (hv : TagFree L W v) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) (ω : Sizes.SeqΩ auxSizes) :
    (auxQuadChaos L W v hz i).chaos ω =
      (∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
          auxHG L W v ω i k.1 * auxMinorRes L W v z i ω k l * auxHG L W v ω l.1 i)
        - ∑ k : {a : Idx L W // a ≠ i}, (sigRow L W v i k.1 : ℂ) * auxMinorRes L W v z i ω k k := by
  unfold RowChaos.chaos RowChaos.cen
  congr 1
  · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [auxQuadChaos_h hv hz i ω k, auxHG_swap, auxQuadChaos_h hv hz i ω l]
    simp only [map_mul, Complex.conj_ofReal]
    change (auxQuadChaos L W v hz i).h ω k *
        ((lamRow L W v i k.1 : ℂ) * auxMinorRes L W v z i ω k l * (lamRow L W v i l.1 : ℂ)) *
        (starRingEnd ℂ) ((auxQuadChaos L W v hz i).h ω l) = _
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hs := auxQuadChaos_sg (v := v) hz i k
    change (((auxQuadChaos L W v hz i).sg k : ℝ) : ℂ) *
        ((lamRow L W v i k.1 : ℂ) * auxMinorRes L W v z i ω k k * (lamRow L W v i k.1 : ℂ)) = _
    rw [← hs]
    push_cast
    ring

/-- **The control of the chaos is the Hanson–Wright proxy** `∑_{k,l} σ_{ik} |G^{(i)}_{kl}|² σ_{il}`. -/
theorem auxQuadChaos_Vq {v : Coord L W → ℝ≥0} {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W)
    (ω : Sizes.SeqΩ auxSizes) :
    (auxQuadChaos L W v hz i).Vq ω =
      ∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
        sigRow L W v i k.1 * ‖auxMinorRes L W v z i ω k l‖ ^ 2 * sigRow L W v i l.1 := by
  unfold RowChaos.Vq
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hk := auxQuadChaos_sg (v := v) hz i k
  have hl := auxQuadChaos_sg (v := v) hz i l
  change (auxQuadChaos L W v hz i).sg k *
      ‖(lamRow L W v i k.1 : ℂ) * auxMinorRes L W v z i ω k l * (lamRow L W v i l.1 : ℂ)‖ ^ 2 *
      (auxQuadChaos L W v hz i).sg l = _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (lamRow_nonneg L W v i k.1), abs_of_nonneg (lamRow_nonneg L W v i l.1),
    ← hk, ← hl]
  ring

/-- The Hanson–Wright proxy `∑_{k,l} σ_{ik} |G^{(i)}_{kl}|² σ_{il}` of the minor of `Xmat s`. -/
def quadVqS (v : Coord L W → ℝ≥0) (z : ℂ) (i : Idx L W) (s : Ω L W) : ℝ :=
  ∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
    sigRow L W v i k.1 *
      ‖green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2 * sigRow L W v i l.1

/-- The centred quadratic form of (4.7) of `Xmat s` at row `i`:
`∑_{k,l ≠ i} H_{ik} G^{(i)}_{kl} H_{li} - ∑_{k ≠ i} σ_{ik} G^{(i)}_{kk}`. -/
def quadQS (v : Coord L W → ℝ≥0) (z : ℂ) (i : Idx L W) (s : Ω L W) : ℂ :=
  (∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
      Xmat L W s i k.1 * green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l *
        Xmat L W s l.1 i)
    - ∑ k : {a : Idx L W // a ≠ i}, (sigRow L W v i k.1 : ℂ) *
        green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k k

theorem continuous_green_minorS {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W)
    (k l : {a : Idx L W // a ≠ i}) :
    Continuous fun s : Ω L W => green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l := by
  have h := RBM.Gauss.continuous_green_of_isHermitian
    (f := fun s : Ω L W => (Xmat L W s).submatrix Subtype.val Subtype.val)
    ((continuous_Xmat L W).matrix_submatrix (Subtype.val : {a : Idx L W // a ≠ i} → Idx L W)
      (Subtype.val : {a : Idx L W // a ≠ i} → Idx L W))
    (fun s => (Xmat_isHermitian L W s).submatrix _) hz
  exact h.matrix_elem k l

theorem continuous_Xmat_apply (i j : Idx L W) : Continuous fun s : Ω L W => Xmat L W s i j :=
  (continuous_Xmat L W).matrix_elem i j

theorem continuous_quadVqS (v : Coord L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W) :
    Continuous (quadVqS v z i) := by
  unfold quadVqS
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact (continuous_const.mul ((continuous_green_minorS hz i k l).norm.pow 2)).mul continuous_const

theorem continuous_quadQS (v : Coord L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W) :
    Continuous (quadQS v z i) := by
  unfold quadQS
  refine Continuous.sub ?_ ?_
  · refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_Xmat_apply i k.1).mul (continuous_green_minorS hz i k l)).mul
      (continuous_Xmat_apply l.1 i)
  · exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_green_minorS hz i k k)

/-- The chaos and its control are the functions `quadQS`, `quadVqS` of the rescaled sample. -/
theorem auxQuadChaos_eq {v : Coord L W → ℝ≥0} (hv : TagFree L W v) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) (ω : Sizes.SeqΩ auxSizes) :
    (auxQuadChaos L W v hz i).chaos ω = quadQS v z i (auxT L W v ω) ∧
      (auxQuadChaos L W v hz i).Vq ω = quadVqS v z i (auxT L W v ω) :=
  ⟨auxQuadChaos_chaos hv hz i ω, auxQuadChaos_Vq hz i ω⟩

/-- **The quadratic large deviation estimate (4.7) for any tag-free variance family**, on the
original coordinate space, through the auxiliary carrier: for `Q_i = ∑_{k,l ≠ i} H_{ik} G^{(i)}_{kl} H_{li}`
and `V = ∑ σ_{ik} |G^{(i)}_{kl}|² σ_{il}`,
`P(λ V < |Q_i - ∑_k σ_{ik} G^{(i)}_{kk}|²) ≤ A_q / λ^{q+1}` under `gaussLaw v`.  The auxiliary
carrier is a proof device: the event is a function of `Xmat s` only. -/
theorem gaussLaw_quad_tail {v : Coord L W → ℝ≥0} (hv : TagFree L W v) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw L W v {s | lam * quadVqS v z i s < ‖quadQS v z i s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have hA : MeasurableSet {s : Ω L W | lam * quadVqS v z i s < ‖quadQS v z i s‖ ^ 2} :=
    measurableSet_lt ((continuous_quadVqS v hz i).measurable.const_mul lam)
      ((continuous_quadQS v hz i).norm.pow 2).measurable
  have hmap : gaussLaw L W v = (Sizes.seqP auxSizes).map (auxT L W v) := (auxT_law L W v).symm
  rw [hmap, Measure.map_apply (continuous_auxT L W v).measurable hA]
  have := chaos_tail (auxQuadChaos L W v hz i) hlam q
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (auxQuadChaos_eq hv hz i ω).1,
    (auxQuadChaos_eq hv hz i ω).2]

theorem gueVar_tagFree : TagFree L W (Endpoints.gueVar L W) := fun _ _ => rfl

/-- The entry variance of the GUE off the diagonal: `E|H_{ik}|² = N⁻¹`, `N = (W L)²`. -/
theorem sigRow_gueVar {i k : Idx L W} (hik : k ≠ i) :
    sigRow L W (Endpoints.gueVar L W) i k = ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold sigRow rowCoordF
  split_ifs with h
  · have : i ≠ k := Ne.symm hik
    simp only [Endpoints.gueVar, this, ↓reduceIte]
    push_cast
    field_simp
  · simp only [Endpoints.gueVar, hik, ↓reduceIte]
    push_cast
    field_simp

/-- **The Gaussian quadratic-form LDE for the GUE rows (the probabilistic core of the Schur tail)**:
with `G^{(i)}` the resolvent of the minor, `Q_i = ∑_{k,l ≠ i} H_{ik} G^{(i)}_{kl} H_{li}` and
`N = (W L)²`,
`P_{GUE}(λ N⁻² ∑_{kl} |G^{(i)}_{kl}|² < |Q_i - N⁻¹ tr G^{(i)}|²) ≤ A_q / λ^{q+1}` for every `λ > 0`,
`q`, `i` and `Im z ≠ 0`.  This is `gaussLaw_quad_tail` at `v = gueVar`, i.e. the auxiliary carrier
supplies the GUE row chaos although no band profile is flat. -/
theorem gue_quad_tail {z : ℂ} (hz : z.im ≠ 0) (i : Idx L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    Endpoints.gueP L W {s | lam * ((((((W * L) ^ 2 : ℕ) : ℝ))⁻¹) ^ 2 *
        ∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
          ‖green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2) <
      ‖(∑ k : {a : Idx L W // a ≠ i}, ∑ l : {a : Idx L W // a ≠ i},
          Xmat L W s i k.1 * green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k l *
            Xmat L W s l.1 i) -
        ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ * ∑ k : {a : Idx L W // a ≠ i},
          green ((Xmat L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gaussLaw_quad_tail (gueVar_tagFree (L := L) (W := W)) hz i hlam q
  rw [← gueP_eq_gaussLaw] at h
  convert h using 3
  ext s
  simp only [quadVqS, quadQS]
  have e1 : ∀ k : {a : Idx L W // a ≠ i}, sigRow L W (Endpoints.gueVar L W) i k.1
      = ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := fun k => sigRow_gueVar k.2
  simp only [e1, ← Finset.mul_sum, ← Finset.sum_mul]
  constructor <;> intro hh <;> convert hh using 2 <;> ring

end AuxRowChaos

/-! ## The rank-one row chaos on the auxiliary carrier

The row `(H_{ik})_{k ≠ i}` with a coefficient vector `c` that does not read the row gives
`Q = |∑_k H_{ik} c_k|² - ∑_k σ_{ik} |c_k|²` and `V_q = (∑_k σ_{ik} |c_k|²)²`, where
`σ_{ik} = sigRow v i k = E|H_{ik}|²` for a tag-free family (`TagFree`); no resolvent enters `B`,
so the hypothesis `z.im ≠ 0` is not needed. -/

section AuxLin

open RBM.Green

/-- **The rank-one row chaos** at row `i` with coefficient vector `c`:
`B_{kl} = (λ_k c_k) conj(λ_l c_l)`; its chaos is `|∑_k H_{ik} c_k|² - ∑_k σ_{ik} |c_k|²`. -/
noncomputable def auxLinChaos (L W : ℕ) [NeZero L] [NeZero W] (v : Coord L W → ℝ≥0) (i : Idx L W)
    (c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω') :
    RowChaos auxSizes {a : Idx L W // a ≠ i} where
  co k b := auxRho L W (rowCoordF L W i k.1 b)
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoordF_injOn L W hk hl (auxRho_injective L W h)
    subst h1; subst h2; rfl
  gvar_tag k := by
    unfold rowCoordF
    split_ifs <;> exact_mod_cast (seqGvar_auxRho_tag L W _ _).symm
  eps k := rowSignF L W i k.1
  eps_sq k := by unfold rowSignF; split_ifs <;> norm_num
  r := 1
  B ω k l := ((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k *
    (starRingEnd ℂ) (((lamRow L W v i l.1 : ℝ) : ℂ) * c ω l)
  B_cont k l := (continuous_const.mul (hc k)).mul
    (Complex.continuous_conj.comp (continuous_const.mul (hc l)))
  Bbd := ((∑ k : {a : Idx L W // a ≠ i}, lamRow L W v i k.1) * Cb) ^ 2
  B_bdd ω k l := by
    have hsum : ∀ k : {a : Idx L W // a ≠ i},
        lamRow L W v i k.1 ≤ ∑ k : {a : Idx L W // a ≠ i}, lamRow L W v i k.1 :=
      fun k => Finset.single_le_sum
        (f := fun k : {a : Idx L W // a ≠ i} => lamRow L W v i k.1)
        (fun k _ => lamRow_nonneg L W v i k.1) (Finset.mem_univ k)
    have hb : ∀ k : {a : Idx L W // a ≠ i}, ‖((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k‖
        ≤ (∑ k : {a : Idx L W // a ≠ i}, lamRow L W v i k.1) * Cb := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (lamRow_nonneg L W v i k.1)]
      exact mul_le_mul (hsum k) (hCb ω k) (norm_nonneg _)
        ((lamRow_nonneg L W v i k.1).trans (hsum k))
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul (hb k) (hb l) (norm_nonneg _) ((norm_nonneg _).trans (hb k))
  Ifree := auxOffRow L W i
  Ifree_free k b := by
    classical
    unfold auxOffRow
    intro hmem
    obtain ⟨c, hc, hc'⟩ := Finset.mem_image.1 hmem
    have hc2 : c = rowCoordF L W i k.1 b := auxRho_injective L W hc'
    have hc3 := (Finset.mem_filter.1 hc).2
    rw [hc2] at hc3
    unfold rowCoordF at hc3
    split_ifs at hc3 with h
    · exact hc3.1 rfl
    · exact hc3.2 rfl
  B_free ω ω' h := by
    funext k l
    rw [hcf ω ω' h]

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem auxLin_sg_lam {v : Coord L W → ℝ≥0} (i : Idx L W)
    (c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω')
    (k : {a : Idx L W // a ≠ i}) :
    (auxLinChaos L W v i c hc Cb hCb hcf).sg k * lamRow L W v i k.1 ^ 2 = sigRow L W v i k.1 := by
  have h := auxScale_sq L W v (rowCoordF L W i k.1 true)
  change 2 * (1 : ℝ) ^ 2 * (Sizes.seqGvar auxSizes (auxRho L W (rowCoordF L W i k.1 true)) : ℝ) *
      auxScale L W v (rowCoordF L W i k.1 true) ^ 2 = 2 * (v (rowCoordF L W i k.1 true) : ℝ)
  rw [← h]
  ring

private theorem auxLin_h_lam {v : Coord L W → ℝ≥0} (hv : TagFree L W v) (i : Idx L W)
    (c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ auxSizes) (k : {a : Idx L W // a ≠ i}) :
    (lamRow L W v i k.1 : ℂ) * (auxLinChaos L W v i c hc Cb hCb hcf).h ω k
      = auxHG L W v ω i k.1 := by
  rw [auxHG_apply L W hv (Ne.symm k.2)]
  change _ * (((1 : ℝ) : ℂ) *
    ((ω (auxRho L W (rowCoordF L W i k.1 true)) : ℂ) + ((rowSignF L W i k.1 : ℝ) : ℂ) * Complex.I *
      (ω (auxRho L W (rowCoordF L W i k.1 false)) : ℂ))) = _
  unfold lamRow
  push_cast
  ring

/-- **The rank-one chaos is `|∑ H_{ik} c_k|² - ∑ σ_{ik} |c_k|²`** (`sigRow` for the variance of
an entry; no `z`). -/
theorem auxLin_chaos {v : Coord L W → ℝ≥0} (hv : TagFree L W v) (i : Idx L W)
    (c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ auxSizes) :
    (auxLinChaos L W v i c hc Cb hCb hcf).chaos ω
      = ((‖∑ k : {a : Idx L W // a ≠ i}, auxHG L W v ω i k.1 * c ω k‖ ^ 2
          - ∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
  have hY : ∀ k : {a : Idx L W // a ≠ i},
      (auxLinChaos L W v i c hc Cb hCb hcf).h ω k * ((lamRow L W v i k.1 : ℂ) * c ω k)
        = auxHG L W v ω i k.1 * c ω k := by
    intro k
    rw [← auxLin_h_lam hv i c hc Cb hCb hcf ω k]; ring
  unfold RowChaos.chaos RowChaos.cen
  have e1 : ∑ k, ∑ l, (auxLinChaos L W v i c hc Cb hCb hcf).h ω k *
        (auxLinChaos L W v i c hc Cb hCb hcf).B ω k l *
        (starRingEnd ℂ) ((auxLinChaos L W v i c hc Cb hCb hcf).h ω l)
      = (∑ k, auxHG L W v ω i k.1 * c ω k) *
        (starRingEnd ℂ) (∑ k, auxHG L W v ω i k.1 * c ω k) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hY k, ← hY l]
    change (auxLinChaos L W v i c hc Cb hCb hcf).h ω k *
      (((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k *
      (starRingEnd ℂ) (((lamRow L W v i l.1 : ℝ) : ℂ) * c ω l)) *
        (starRingEnd ℂ) ((auxLinChaos L W v i c hc Cb hCb hcf).h ω l) = _
    rw [map_mul (starRingEnd ℂ) ((auxLinChaos L W v i c hc Cb hCb hcf).h ω l)]
    ring
  have e2 : ∑ k, (((auxLinChaos L W v i c hc Cb hCb hcf).sg k : ℝ) : ℂ) *
        (auxLinChaos L W v i c hc Cb hCb hcf).B ω k k
      = ((∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← auxLin_sg_lam i c hc Cb hCb hcf k]
    change (((auxLinChaos L W v i c hc Cb hCb hcf).sg k : ℝ) : ℂ) *
      (((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k)) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg L W v i k.1)]
    push_cast
    ring
  rw [e1, e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The control of the rank-one chaos is `(∑ σ_{ik} |c_k|²)²`.** -/
theorem auxLin_Vq {v : Coord L W → ℝ≥0} (i : Idx L W)
    (c : Sizes.SeqΩ auxSizes → {a : Idx L W // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ auxSizes) :
    (auxLinChaos L W v i c hc Cb hCb hcf).Vq ω
      = (∑ k : {a : Idx L W // a ≠ i}, sigRow L W v i k.1 * ‖c ω k‖ ^ 2) ^ 2 := by
  have hpt : ∀ k l : {a : Idx L W // a ≠ i},
      (auxLinChaos L W v i c hc Cb hCb hcf).sg k *
        ‖(auxLinChaos L W v i c hc Cb hCb hcf).B ω k l‖ ^ 2 *
        (auxLinChaos L W v i c hc Cb hCb hcf).sg l
      = (sigRow L W v i k.1 * ‖c ω k‖ ^ 2) * (sigRow L W v i l.1 * ‖c ω l‖ ^ 2) := by
    intro k l
    rw [← auxLin_sg_lam (v := v) i c hc Cb hCb hcf k, ← auxLin_sg_lam (v := v) i c hc Cb hCb hcf l]
    change (auxLinChaos L W v i c hc Cb hCb hcf).sg k *
      ‖((lamRow L W v i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((lamRow L W v i l.1 : ℝ) : ℂ) * c ω l)‖ ^ 2 *
      (auxLinChaos L W v i c hc Cb hCb hcf).sg l = _
    rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg L W v i k.1),
      abs_of_nonneg (lamRow_nonneg L W v i l.1)]
    ring
  change ∑ k, ∑ l, (auxLinChaos L W v i c hc Cb hCb hcf).sg k *
      ‖(auxLinChaos L W v i c hc Cb hCb hcf).B ω k l‖ ^ 2 *
      (auxLinChaos L W v i c hc Cb hCb hcf).sg l = _
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l

/-- **A rank-one chaos `Q = Y - R`, `V_q = R²`**: `P(Λ R < Y) ≤ A_q / ((Λ - 1)²)^{q+1}` for
`Λ > 1`. -/
theorem aux_lin_tail {d : Sizes} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : RowChaos d κ) (Y R : Sizes.SeqΩ d → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hchaos : ∀ ω, C.chaos ω = ((Y ω - R ω : ℝ) : ℂ)) (hV : ∀ ω, C.Vq ω = R ω ^ 2)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (Sizes.seqP d) {ω | Λ * R ω < Y ω}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  have hlam : 0 < (Λ - 1) ^ 2 := by
    have : 0 < Λ - 1 := by linarith
    positivity
  refine (measure_mono ?_).trans (chaos_tail C hlam q)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hV, hchaos, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h0 := hR0 ω
  have h1 : (Λ - 1) * R ω < Y ω - R ω := by linarith
  have h2 : 0 ≤ (Λ - 1) * R ω := mul_nonneg (by linarith) h0
  have h3 := pow_lt_pow_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)
  nlinarith [h3]

end AuxLin

end RBM.Univ
