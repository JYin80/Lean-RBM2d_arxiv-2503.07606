/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Endpoints
import RBM2D.Universality.ZeroModeProfile
import RBM2D.Gauss.GreenTimeCont
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Loop.Kcal
import RBM2D.Path.Scales

/-!
# The deterministic transfer `z ↦ (E, u)`

The six statements `ZRange`, `ZGreen`, `ZMeta`, `ZAve`, `ZTrace`, `ZProfile` (`def … : Prop`)
and their proofs: the deterministic transfer from the spectral parameter `z` to the flow data
`(E, u) = (lemE z, lemT z)`.  Namespace `RBM.Endpoints`.  Paper: arXiv:2503.07606, Theorems
`MR:locSC`, `MR:QDiff` and the reparametrisation `zztE`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## The statements (deterministic transfer from `z` to the flow `(E, u)`) -/

section Pins

/-- The constant of `ZMeta`: `cMeta κ = 32/√(κ(4-κ)) = 16/m_κ` with `m_κ = √(κ(4-κ))/2`; it
bounds `4 (m_κ^{-1/2} + 1)²` from above (`(t+1)² ≤ 4t²` for `t ≥ 1`); meaningful for `0 < κ ≤ 2`. -/
def cMeta (κ : ℝ) : ℝ := 32 / Real.sqrt (κ * (4 - κ))

/-- The sign pattern of the `QDiff` index `σ : Bool`: `σ = false` (`G, G†`) is the loop `(+,-)`,
`σ = true` (`G, G`) is the loop `(+,+)`. -/
def qdSign (σ : Bool) : Fin 2 → Bool := ![true, σ]

/-- The spectral domain of `locSC`/`QDiff` at size index `n`, as a type. -/
abbrev ZDom (d : Sizes) (κ τ : ℝ) (n : ℕ) : Type := {z : ℂ // locDomain (d.size n) κ τ z}

/-- **`ZRange`** (`zztE`, `eq:zztE2`): for `0 < Im z ≤ 1`,
`|Re z| ≤ 2 - κ`, the flow data `(E, u) = (lemE z, lemT z)` is a bulk energy, `0 < u < 1`, and
`1 - u ≥ Im z / 4`.  Ingredients: `zztE_quant` (`|E| ≤ 2-κ`, `u ≥ 1/16`), `norm_msc_lt_one`
(`u < 1`), and `1 - u ≥ √u Im z` (from `Im z = Im m (1-u)/u`, `Im m ≤ |m| = √u`).
Proved below: `zRange`. -/
def ZRange : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
    |lemE z| ≤ 2 - κ ∧ 0 < lemT z ∧ lemT z < 1 ∧ (1 / 4 : ℝ) * z.im ≤ 1 - lemT z

/-- **`ZGreen`** (`eq:zztE`; `Sizes.seqHflow_eq_smul`): for `Im z > 0`,
`G_X(z) = √u · (H_u - z_u)^{-1}` with `H_u = √u X`, `z_u = z_u^{(E)}`, `(E, u) = (lemE z, lemT z)`
(from `z_u = √u z`, `eq_inv_sqrt_mul_spectralZ`, and `(c X - c z)^{-1} = c^{-1} (X - z)^{-1}`).
It is an exact identity.  Proved below: `zGreen`. -/
def ZGreen : Prop :=
  ∀ (d : Sizes) (n : ℕ) (ω : d.SeqΩ) (z : ℂ), 0 < z.im →
    Gn d n ω z = (Real.sqrt (lemT z) : ℂ) •
      green (Sizes.seqHflow d n (lemT z) ω) (spectralZ (lemE z) (lemT z))

/-- **`ZMeta`** (`def_meta`; `eq:zztE2`): `M_η ≤ c_κ M_u` for
`(E, u) = (lemE z, lemT z)`, `Meta = W² ℓ(z)² η`, `ℓ(z) = min(η^{-1/2}, L) + 1`,
`M_u = W² ℓ_u² η_u`.  Proof: `η_u = √u η`, `1 - u = η_u / Im m^{(E)}`, `Im m^{(E)} ≥ m_κ`.
Proved below: `zMeta`. -/
def ZMeta : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ L W : ℕ, 1 ≤ L → 1 ≤ W → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → Meta L W z ≤ cMeta κ * scaleM L W (lemE z) (lemT z)

/-- **`ZAve`** (`(G_bound_ave)`): the block average of the diagonal of `G_X(z)` is
`√u · 𝓛_{u,(+),(a)}` (one-loop, `E_a` of weight `W^{-2}`; `Epaper`/`Eblk` reindexing
`Epaper_eq`, `blockMat`).  Proved below: `zAve`. -/
def ZAve : Prop :=
  ∀ (d : Sizes) (n : ℕ) (ω : d.SeqΩ) (z : ℂ), 0 < z.im → ∀ a : Z2 (d.L n),
    ((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x =
      (Real.sqrt (lemT z) : ℂ) *
        gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (lemT z) ω))
          (spectralZ (lemE z) (lemT z)) (loopOf ![true] ![a])

/-- **`ZTrace`** (`(Meq:QdW1)`, `(Meq:QdW2)`): `tr(G E_a G^σ E_b) =
u · 𝓛_{u,(+,σ),(a,b)}` at `H_u, z_u` (`G_X(z) = √u G_u`, `G_X(z)† = √u G_u(z̄_u)`, `Epaper` to
`Eblk`).  Proved below: `zTrace`. -/
def ZTrace : Prop :=
  ∀ (d : Sizes) (n : ℕ) (ω : d.SeqΩ) (z : ℂ), 0 < z.im → ∀ (σ : Bool) (a b : Z2 (d.L n)),
    trGEGE d n ω z σ a b = (lemT z : ℂ) *
      gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (lemT z) ω))
        (spectralZ (lemE z) (lemT z)) (loopOf (qdSign σ) ![a, b])

/-- **`ZProfile`** (`Kn2sol`): `profile = u · 𝒦_{u,(+,σ),(a,b)}` at `(E, u) = (lemE z,
lemT z)`, using `mSC z = √u m^{(E)}` and `|m^{(E)}| = 1`.  Proved below: `zProfile`. -/
def ZProfile : Prop :=
  ∀ (L W : ℕ) [NeZero L] (z : ℂ), 0 < z.im → ∀ (σ : Bool) (a b : Z2 L),
    profile L W z σ a b = (lemT z : ℂ) *
      KLoop.Kcal L W (lemE z) (lemT z) (loopOf (qdSign σ) ![a, b])

end Pins

/-! ### Statements proved here: `ZRange`, `ZGreen`, `ZProfile`

These three are proved here from `zztE_quant`, `norm_msc_lt_one`, `msc_mul`,
`eq_inv_sqrt_mul_spectralZ`, `msc_eq_sqrt_mul_spectralM`, `Sizes.seqHflow_eq_smul`. -/

section ProvedPins

theorem ZRescale_msc_ne_zero {z : ℂ} (hz : 0 < z.im) : msc z ≠ 0 := fun h0 => by
  have := msc_im_pos hz
  rw [h0] at this
  simp at this

theorem ZRescale_lemT_pos {z : ℂ} (hz : 0 < z.im) : 0 < lemT z := by
  unfold lemT
  have := norm_pos_iff.2 (ZRescale_msc_ne_zero hz)
  positivity

/-- `mSC z = √u m^{(E)}` for `(E, u) = (lemE z, lemT z)`. -/
theorem ZRescale_msc_eq {z : ℂ} (hz : 0 < z.im) :
    mSC z = (Real.sqrt (lemT z) : ℂ) * spectralM (lemE z) := by
  rw [mSC_eq_msc hz]
  exact msc_eq_sqrt_mul_spectralM hz

/-- `G(cH, cz) = c⁻¹ G(H, z)` for `c ≠ 0` (no invertibility assumption). -/
theorem ZRescale_green_smul_mul {n : Type*} [Fintype n] [DecidableEq n] {c : ℂ} (hc : c ≠ 0)
    (H : Matrix n n ℂ) (z : ℂ) : green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  have hinv : ∀ A : Matrix n n ℂ, (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
    intro A
    by_cases h : IsUnit A.det
    · have : Invertible c := invertibleOfNonzero hc
      rw [Matrix.inv_smul A c h, invOf_eq_inv c]
    · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
      have h2 : ¬ IsUnit (c • A).det := by
        rw [Matrix.det_smul, hdet, mul_zero]
        simp
      rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
        smul_zero]
  unfold green
  rw [hsub, hinv]

theorem zGreen : ZGreen := by
  intro d n ω z hz
  have hu := ZRescale_lemT_pos hz
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have h1 : spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
    have h := eq_inv_sqrt_mul_spectralZ hz
    calc spectralZ (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) *
            ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]
  rw [Sizes.seqHflow_eq_smul, h1, ZRescale_green_smul_mul hs, smul_smul, mul_inv_cancel₀ hs,
    one_smul]
  rfl

/-- The key identity behind `ZRange`: `Im z · |m|² = Im m (1 - |m|²)`, from `m (m + z) = -1`. -/
theorem ZRescale_im_identity {z : ℂ} (hz : 0 < z.im) :
    z.im * ‖msc z‖ ^ 2 = (msc z).im * (1 - ‖msc z‖ ^ 2) := by
  have hm0 := ZRescale_msc_ne_zero hz
  have h := msc_mul z
  have hz' : z = -(msc z)⁻¹ - msc z := by
    field_simp
    linear_combination h
  have him := congrArg Complex.im hz'
  have hN : Complex.normSq (msc z) = ‖msc z‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hN0 : 0 < Complex.normSq (msc z) := Complex.normSq_pos.2 hm0
  rw [Complex.sub_im, Complex.neg_im, Complex.inv_im, hN] at him
  rw [hN] at hN0
  field_simp at him ⊢
  linarith

theorem zRange : ZRange := by
  intro κ hκ z hz hz1 hre
  obtain ⟨hE, hu16, -, -⟩ := zztE_quant hκ hz hz1 hre
  have hr0 : 0 < ‖msc z‖ := norm_pos_iff.2 (ZRescale_msc_ne_zero hz)
  have hr1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hu : lemT z = ‖msc z‖ ^ 2 := rfl
  refine ⟨hE, ZRescale_lemT_pos hz, by rw [hu]; nlinarith, ?_⟩
  have hid := ZRescale_im_identity hz
  have him : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have h4 : (1 / 4 : ℝ) ≤ ‖msc z‖ := by
    rw [hu] at hu16
    nlinarith
  rw [hu]
  have h1r : 0 ≤ 1 - ‖msc z‖ ^ 2 := by nlinarith
  have hkey : ‖msc z‖ * z.im ≤ 1 - ‖msc z‖ ^ 2 := by
    have : z.im * ‖msc z‖ ^ 2 ≤ ‖msc z‖ * (1 - ‖msc z‖ ^ 2) := by
      rw [hid]; exact mul_le_mul_of_nonneg_right him h1r
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hr0 hr0]
  nlinarith [mul_le_mul_of_nonneg_right h4 hz.le]

theorem ZRescale_Kcal_two (L W : ℕ) [NeZero L] (E u : ℝ) (s : Bool) (a b : Z2 L) :
    KLoop.Kcal L W E u (loopOf ![true, s] ![a, b]) =
      KLoop.kTwo L W (KLoop.mSig E) u true s a b := by
  simp [KLoop.Kcal, KLoop.Kgen, loopOf, LoopIdx.length]

theorem zProfile : ZProfile := by
  intro L W _ z hz σ a b
  have hu := ZRescale_lemT_pos hz
  have hm := ZRescale_msc_eq hz
  have hE : |lemE z| ≤ 2 := by
    unfold lemE
    have hr : 0 < ‖msc z‖ := norm_pos_iff.2 (ZRescale_msc_ne_zero hz)
    rw [abs_div, abs_mul, abs_of_pos hr, div_le_iff₀ hr]
    have := Complex.abs_re_le_norm (msc z)
    norm_num
    linarith
  have hn : ‖spectralM (lemE z)‖ = 1 := norm_spectralM hE
  have hconj : spectralM (lemE z) * (starRingEnd ℂ) (spectralM (lemE z)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hsq : (Real.sqrt (lemT z) : ℂ) ^ 2 = (lemT z : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hu.le]
  have hnorm2 : ((‖mSC z‖ ^ 2 : ℝ) : ℂ) = (lemT z : ℂ) := by
    rw [hm, norm_mul, Complex.norm_real, hn, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hu.le]
  unfold profile
  rw [qdSign, ZRescale_Kcal_two]
  unfold KLoop.kTwo KLoop.mSig
  cases σ
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [hconj, hnorm2]
    ring_nf
  · simp only [ite_true]
    rw [hm, mul_pow, hsq]
    ring_nf

end ProvedPins

/-! ### Statements proved here: `ZAve`, `ZTrace` (reindexing `Idx ≃ BlockIndex`) and `ZMeta` -/

section ProvedBlock

variable {L W : ℕ} [NeZero L] [NeZero W]

theorem ZRescale_blockMat_eq (M : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat M = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv L W) M := by
  simp [blockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem ZRescale_blockMat_mul (A B : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (A * B) = blockMat A * blockMat B := by
  rw [ZRescale_blockMat_eq, ZRescale_blockMat_eq, ZRescale_blockMat_eq, map_mul]

theorem ZRescale_blockMat_sub (A B : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (A - B) = blockMat A - blockMat B := by
  rw [ZRescale_blockMat_eq, ZRescale_blockMat_eq, ZRescale_blockMat_eq, map_sub]

theorem ZRescale_blockMat_smul_one (c : ℂ) :
    blockMat (c • (1 : Matrix (Idx L W) (Idx L W) ℂ)) = c • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) := by
  rw [ZRescale_blockMat_eq, map_smul, map_one]

theorem ZRescale_green_block (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) :
    green (blockMat H) z = blockMat (green H z) := by
  unfold green
  rw [← ZRescale_blockMat_smul_one, ← ZRescale_blockMat_sub, ZRescale_blockMat_eq, ZRescale_blockMat_eq,
    Matrix.coe_reindexAlgEquiv, Matrix.inv_reindex]

theorem ZRescale_gsig_block (H : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) (s : Bool) :
    Gsig (blockMat H) z s = blockMat (Gsig H z s) := by
  cases s <;> simp [Gsig, ZRescale_green_block]

theorem ZRescale_blockMat_Epaper (a : Z2 L) : blockMat (Epaper L W a) = Eblk L W a := by
  rw [Epaper_eq_submatrix]
  ext p q
  simp only [blockMat, Matrix.submatrix_apply]
  have h : ∀ p, split L W ((splitEquiv L W).symm p) = p := fun p =>
    (splitEquiv L W).apply_symm_apply p
  rw [h, h]

theorem ZRescale_trace_block (A : Matrix (Idx L W) (Idx L W) ℂ) :
    Matrix.trace (blockMat A) = Matrix.trace A := by
  unfold Matrix.trace Matrix.diag blockMat
  simp only [Matrix.submatrix_apply]
  exact Equiv.sum_comp (splitEquiv L W).symm (fun x => A x x)


omit [NeZero W] in
theorem ZRescale_gloop_one (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (b : Z2 L) :
    gloop L W H z ⟨[true], [b]⟩ = Matrix.trace (green H z * Eblk L W b) := by
  simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true]

theorem ZRescale_trace_mul_Epaper (G : Matrix (Idx L W) (Idx L W) ℂ) (a : Z2 L) :
    Matrix.trace (G * Epaper L W a) = ((W : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk L W a, G x x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Epaper, Matrix.of_apply]
  have h : ∀ i : Idx L W, ∑ j : Idx L W, G i j *
      (if j = i then (W : ℂ)⁻¹ ^ 2 * (if j ∈ Iblk L W a then 1 else 0) else 0) =
      if i ∈ Iblk L W a then ((W : ℂ) ^ 2)⁻¹ * G i i else 0 := by
    intro i
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, inv_pow]
    split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]


theorem zAve : ZAve := by
  intro d n ω z hz a
  have hl : (loopOf ![true] ![a] : LoopIdx (Z2 (d.L n))) = ⟨[true], [a]⟩ := by simp [loopOf]
  rw [hl, ZRescale_gloop_one, ZRescale_green_block, ← ZRescale_blockMat_Epaper a, ← ZRescale_blockMat_mul,
    ZRescale_trace_block, ZRescale_trace_mul_Epaper, zGreen d n ω z hz]
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring


theorem zTrace : ZTrace := by
  intro d n ω z hz σ a b
  set H := Sizes.seqHflow d n (lemT z) ω with hH
  have hHerm : H.IsHermitian := Sizes.seqHflow_isHermitian d n _ ω
  have hu := ZRescale_lemT_pos hz
  have hG : Gn d n ω z = (Real.sqrt (lemT z) : ℂ) • Gsig H (spectralZ (lemE z) (lemT z)) true :=
    zGreen d n ω z hz
  have hGσ : (if σ then Gn d n ω z else (Gn d n ω z)ᴴ) =
      (Real.sqrt (lemT z) : ℂ) • Gsig H (spectralZ (lemE z) (lemT z)) σ := by
    cases σ
    · simp only [Bool.false_eq_true, ite_false]
      rw [hG, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        Gsig_conjTranspose hHerm]
      rfl
    · simpa using hG
  have hl : (loopOf (qdSign σ) ![a, b] : LoopIdx (Z2 (d.L n))) = ⟨[true, σ], [a, b]⟩ := by
    simp [loopOf, qdSign, List.ofFn_succ]
  rw [hl, gloop_two, ZRescale_gsig_block, ZRescale_gsig_block, ← ZRescale_blockMat_Epaper a,
    ← ZRescale_blockMat_Epaper b, ← ZRescale_blockMat_mul, ← ZRescale_blockMat_mul,
    ← ZRescale_blockMat_mul, ZRescale_trace_block]
  unfold trGEGE
  rw [hGσ, hG]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]


end ProvedBlock

section ProvedMeta

theorem ZRescale_rpow_neg_half {η : ℝ} (hη : 0 ≤ η) : η ^ (-(1 / 2 : ℝ)) = (Real.sqrt η)⁻¹ := by
  rw [Real.rpow_neg hη, Real.sqrt_eq_rpow]

/-- The real core of `ZMeta` (no complex numbers, no `msc`). -/
theorem ZRescale_meta_real {L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {η u mE mk : ℝ} (hη : 0 < η)
    (hu0 : 0 < u) (hu1 : u < 1) (hu16 : 1 / 16 ≤ u) (hmk : 0 < mk) (hmk1 : mk ≤ 1)
    (hmkE : mk ≤ mE) (hid : (1 - u) * mE = Real.sqrt u * η) :
    (W : ℝ) ^ 2 * (min (η ^ (-(1 / 2 : ℝ))) (L : ℝ) + 1) ^ 2 * η ≤
      (16 / mk) * ((W : ℝ) ^ 2 * (min (1 / Real.sqrt (1 - u)) (L : ℝ)) ^ 2 * ((1 - u) * mE)) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hx : 0 < 1 - u := by linarith
  have hsx : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [ZRescale_rpow_neg_half hη.le]
  set a := min (Real.sqrt η)⁻¹ (L : ℝ) with ha
  set b := min (1 / Real.sqrt (1 - u)) (L : ℝ) with hb
  have hb1 : 1 ≤ b := by
    have hsq1 : Real.sqrt (1 - u) ≤ 1 := by
      calc Real.sqrt (1 - u) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    exact le_min (one_le_one_div hsx hsq1) hL'
  have ha0 : 0 ≤ a := le_min (inv_nonneg.2 hsη.le) (by linarith)
  set ρ := Real.sqrt mk with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hmk
  have hρ1 : ρ ≤ 1 := by
    calc ρ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hmk1
      _ = 1 := Real.sqrt_one
  have hρ2 : ρ * ρ = mk := Real.mul_self_sqrt hmk.le
  -- the key comparison `ρ a ≤ b`
  have hmkη : mk * (1 - u) ≤ η := by
    have h1 : mk * (1 - u) ≤ mE * (1 - u) := mul_le_mul_of_nonneg_right hmkE hx.le
    have h2 : Real.sqrt u * η ≤ η := by
      have : Real.sqrt u ≤ 1 := Real.sqrt_le_one.2 hu1.le
      nlinarith
    nlinarith
  have hkey : ρ * a ≤ b := by
    refine le_min ?_ ?_
    · have h1 : ρ * a ≤ ρ * (Real.sqrt η)⁻¹ := mul_le_mul_of_nonneg_left (min_le_left _ _) hρ0.le
      refine h1.trans ?_
      have h2 : ρ * Real.sqrt (1 - u) ≤ Real.sqrt η := by
        rw [hρ, ← Real.sqrt_mul hmk.le]
        exact Real.sqrt_le_sqrt hmkη
      rw [← div_eq_mul_inv, div_le_iff₀ hsη, one_div]
      calc ρ = ρ * Real.sqrt (1 - u) * (Real.sqrt (1 - u))⁻¹ := by field_simp
        _ ≤ Real.sqrt η * (Real.sqrt (1 - u))⁻¹ := by gcongr
        _ = (Real.sqrt (1 - u))⁻¹ * Real.sqrt η := mul_comm _ _
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hρ0.le).trans
        (by nlinarith)
  have ha_le : a ≤ b / ρ := by
    rw [le_div_iff₀ hρ0]; linarith
  have hb_le : b ≤ b / ρ := by
    rw [le_div_iff₀ hρ0]; nlinarith
  have hℓ : a + 1 ≤ 2 * (b / ρ) := by linarith
  have hℓ2 : (a + 1) ^ 2 ≤ 4 * b ^ 2 / mk := by
    calc (a + 1) ^ 2 ≤ (2 * (b / ρ)) ^ 2 := pow_le_pow_left₀ (by linarith) hℓ 2
      _ = 4 * b ^ 2 / (ρ * ρ) := by field_simp; norm_num
      _ = 4 * b ^ 2 / mk := by rw [hρ2]
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt u := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu16
  rw [hid]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := sq_nonneg _
  have hX : 0 ≤ (W : ℝ) ^ 2 * b ^ 2 * η / mk := by positivity
  calc (W : ℝ) ^ 2 * (a + 1) ^ 2 * η ≤ (W : ℝ) ^ 2 * (4 * b ^ 2 / mk) * η := by gcongr
    _ = ((W : ℝ) ^ 2 * b ^ 2 * η / mk) * 4 := by ring
    _ ≤ ((W : ℝ) ^ 2 * b ^ 2 * η / mk) * (16 * Real.sqrt u) := by
        apply mul_le_mul_of_nonneg_left _ hX; linarith
    _ = (16 / mk) * ((W : ℝ) ^ 2 * b ^ 2 * (Real.sqrt u * η)) := by field_simp

theorem zMeta : ZMeta := by
  intro κ hκ L W hL hW z hz hz1 hre
  obtain ⟨hE, hu16, -, -⟩ := zztE_quant hκ hz hz1 hre
  obtain ⟨-, hu0, hu1, -⟩ := zRange κ hκ z hz hz1 hre
  have hκ2 : κ ≤ 2 := by have := abs_nonneg z.re; linarith
  have hkpos : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  set mk : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hmk
  have hmk0 : 0 < mk := by positivity
  have hmk1 : mk ≤ 1 := by
    have h4 : κ * (4 - κ) ≤ 2 ^ 2 := by nlinarith [sq_nonneg (κ - 2)]
    have := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_sq (by norm_num)] at this
    rw [hmk]; linarith
  have hmkE : mk ≤ (spectralM (lemE z)).im := by
    rw [spectralM_im, hmk]
    have h1 := abs_le.1 hE
    have : κ * (4 - κ) ≤ 4 - lemE z ^ 2 := by nlinarith [h1.1, h1.2]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt this) (by norm_num)
  have hs : 0 < Real.sqrt (lemT z) := Real.sqrt_pos.2 (ZRescale_lemT_pos hz)
  have hzu : spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
    have h := eq_inv_sqrt_mul_spectralZ hz
    have hs' : (Real.sqrt (lemT z) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    calc spectralZ (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) *
            ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs', one_mul]
      _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]
  have hid : (1 - lemT z) * (spectralM (lemE z)).im = Real.sqrt (lemT z) * z.im := by
    have h := spectralZ_im (lemE z) (lemT z)
    rw [hzu, Complex.im_ofReal_mul] at h
    exact h.symm
  have hcm : cMeta κ = 16 / mk := by
    rw [cMeta, hmk]
    have : Real.sqrt (κ * (4 - κ)) ≠ 0 := (Real.sqrt_pos.2 hkpos).ne'
    field_simp
    norm_num
  have h := ZRescale_meta_real (L := L) (W := W) hL hW hz hu0 hu1 hu16 hmk0 hmk1 hmkE hid
  rw [hcm]
  unfold Meta ellz scaleM ellT etaT
  exact h


end ProvedMeta
end RBM.Endpoints
