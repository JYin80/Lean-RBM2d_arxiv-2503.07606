/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Drift
import RBM2D.Path.GoodEvent

/-!
# (7.29) at `t₀` on the GUE-phase grid, first half (`d = 2`)

The 2-loop algebra, Duhamel in expectation, one grid step of `K̃` on 2-loops, and one step of the
recursion for `e_k = E L_{u_k} - K̃_{u_k}`.  The second half (Grönwall, the inputs, the arithmetic
and `gueGrid_eq729`) is in `Eq729B.lean`.

## What is proved

* `eq729F`, `eq729e`: the loop `L_{u_k}` of the GUE-phase grid path at step `k` and
  `e_k(I) = E L_{u_k}(I) - K̃_{u_k}(I)`.
* `eq729_duhamel`: Duhamel in expectation for one grid step,
  `‖E L_{k+1} - E L_k - Δ E genMatGUE_k‖ ≤ envConst · Δ^{3/2}` (the martingale part has mean `0`),
  from `condExp_loop_drift_gue`.
* `eq729_primBil2`, `eq729_eG2`, `eq729_norm_primBil2_le`, `eq729_norm_primRhs2_le`,
  `eq729_primRhs_one`: the algebra of 2-loops (`W²·∑_{a,b}` with `SBgue = 1/L²`; the cut `(1,2)`
  is the only one; `primRhsGUE` of a 1-loop is `0`).
* `eq729_Kdisc`: one grid step of the primitive 2-loop, `‖K̃_u + Δ ∂_t K̃_u - K̃_{u+Δ}‖ ≤ 3 N² Δ²`.
* `eq729c`, `eq729_one_step`: one step of the recursion for `e_k` on 2-loops,
  `‖e_{k+1}‖ ≤ (1 + 2 N ρ Λ Δ) ‖e_k‖_max + eq729c`.
* the grid-time facts `eq729_step_nonneg`, `eq729_KΔ`, `eq729_time_mem`, `eq729_eta_pos`,
  `eq729_eta_le`, `eq729_zt_im` used in `Eq729B.lean`.

## Conventions (`d = 2`)

The sizes are `Sizes`, the grid path lives in `PathΩ d` with `gridTime/gridStep`, the spectral
parameter is `spectralZ`, and `gloop (d.L n) (d.W n) (blockMat M) z ⟨σ, a⟩` has labels in
`Z2 (d.L n)`.  The drift `genMatGUE` is `primRhsGUE (LLf …) + egtNGUE` on loops of length `≥ 2`
(`loopGenGUE`); the envelope is `envConst`.  The counts are `N = (W L)²` rows, `L²` labels,
weight `W²` in `primRhsGUE`, `SBgue = 1/L²`, so every double sum over `a, b ∈ Z_L²` costs
`L⁴ · L⁻² = L²`, and with `W²` this is `N`; the remainder constant of `eq729c` is
`envConst … 2 = 16·5⁴·N⁴ (1+η⁻¹)⁶ = 10000 N⁴ (1+η⁻¹)⁶` (`η_v⁻¹ ≤ N`).  The `1`-loop input `hX`
stays a hypothesis of `eq729_one_step` (it comes from `gueGrid_expect_oneLoop`).

Helpers are `private` or carry the prefix `Eq729A_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ### Algebra of 2-loops -/

section Algebra

/-- The primitive bilinear form on a 2-loop: only the cut `(k, l) = (1, 2)` contributes. -/
theorem eq729_primBil2 (L W : ℕ) [NeZero L] (K K' : LoopIdx (Z2 L) → ℂ)
    (s1 s2 : Bool) (a1 a2 : Z2 L) :
    primBilGUE L W K K' ⟨[s1, s2], [a1, a2]⟩ =
      (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        K ⟨[s1, s2], [a, a2]⟩ * SBgue L a b * K' ⟨[s1, s2], [a1, b]⟩ := by
  unfold primBilGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L))) = {1, 2} := by
    rfl
  have h2 : ∀ k, Finset.Ioc k (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L)))
      = Finset.Ioc k 2 := fun k => rfl
  rw [h1]
  simp only [h2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    show Finset.Ioc 1 2 = {2} from rfl, show Finset.Ioc 2 2 = ∅ from rfl, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  rfl

/-- `avgErr` of a 1-loop: `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)`. -/
private theorem Eq729A_avgErr_eq (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) (a : Z2 L) :
    avgErr L W E u M σ a = gloop L W (blockMat M) (spectralZ E u) ⟨[σ], [a]⟩ - KLoop.mSig E σ := by
  unfold avgErr greenBlk
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk_eq_one, smul_eq_mul, mul_one]
  simp [gloop, gloopProd]

/-- The `𝓔^{(G̃)}` term on a 2-loop, written with 1-loops and 3-loops. -/
theorem eq729_eG2 (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (s1 s2 : Bool) (a1 a2 : Z2 L) :
    egtNGUE L W E u M ⟨[s1, s2], [a1, a2]⟩ =
      (W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L,
        ((gloop L W (blockMat M) (spectralZ E u) ⟨[s1], [a]⟩ - KLoop.mSig E s1) * SBgue L a b *
            gloop L W (blockMat M) (spectralZ E u) ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (gloop L W (blockMat M) (spectralZ E u) ⟨[s2], [a]⟩ - KLoop.mSig E s2) * SBgue L a b *
            gloop L W (blockMat M) (spectralZ E u) ⟨[s1, s2, s2], [a1, b, a2]⟩) := by
  unfold egtNGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L))) = {1, 2} := by
    rfl
  rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L)).σ.getD (1 - 1) false = s1 := rfl
  have e2 : (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L)).σ.getD (2 - 1) false = s2 := rfl
  have c1 : ∀ b : Z2 L, (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L)).cutGlue 1 b
      = ⟨[s1, s1, s2], [b, a1, a2]⟩ := fun b => rfl
  have c2 : ∀ b : Z2 L, (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (Z2 L)).cutGlue 2 b
      = ⟨[s1, s2, s2], [a1, b, a2]⟩ := fun b => rfl
  simp only [e1, e2, c1, c2, Eq729A_avgErr_eq]
  rw [← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  rfl

/-- `‖W² ∑_{a,b} A_a (1/L²) B_b‖ ≤ N α β`, `N = (W L)²`. -/
private theorem Eq729A_norm_WsumSB_le (L W : ℕ) [NeZero L] (A B : Z2 L → ℂ) {α β : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ α) (hB : ∀ y, ‖B y‖ ≤ β) :
    ‖(W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L, A a * SBgue L a b * B b‖
      ≤ (((W * L) ^ 2 : ℕ) : ℝ) * α * β := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA 0)
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hB 0)
  have hterm : ∀ a b : Z2 L, ‖A a * SBgue L a b * B b‖ ≤ α * ((L : ℝ) ^ 2)⁻¹ * β := by
    intro a b
    rw [norm_mul, norm_mul, SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hA a) (by positivity)) (hB b) (norm_nonneg _)
      (by positivity)
  calc ‖(W : ℂ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L, A a * SBgue L a b * B b‖
      ≤ (W : ℝ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L, ‖A a * SBgue L a b * B b‖ := by
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ (W : ℝ) ^ 2 * ∑ _a : Z2 L, ∑ _b : Z2 L, α * ((L : ℝ) ^ 2)⁻¹ * β := by
        gcongr with a _ b _
        exact hterm a b
    _ = (((W * L) ^ 2 : ℕ) : ℝ) * α * β := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
        push_cast
        field_simp

/-- The norm of `primBilGUE` on a 2-loop: `≤ N α β`. -/
theorem eq729_norm_primBil2_le (L W : ℕ) [NeZero L] (K K' : LoopIdx (Z2 L) → ℂ)
    (s1 s2 : Bool) (a1 a2 : Z2 L) {α β : ℝ} (hA : ∀ x, ‖K ⟨[s1, s2], [x, a2]⟩‖ ≤ α)
    (hB : ∀ y, ‖K' ⟨[s1, s2], [a1, y]⟩‖ ≤ β) :
    ‖primBilGUE L W K K' ⟨[s1, s2], [a1, a2]⟩‖ ≤ (((W * L) ^ 2 : ℕ) : ℝ) * α * β := by
  rw [eq729_primBil2]
  exact Eq729A_norm_WsumSB_le L W (fun x => K ⟨[s1, s2], [x, a2]⟩)
    (fun y => K' ⟨[s1, s2], [a1, y]⟩) hA hB

/-- `primRhsGUE` of a 1-loop is an empty sum. -/
theorem eq729_primRhs_one (L W : ℕ) [NeZero L] (K : LoopIdx (Z2 L) → ℂ) (s : Bool)
    (a : Z2 L) : primRhsGUE L W K ⟨[s], [a]⟩ = 0 := by
  unfold primRhsGUE primBilGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s], [a]⟩ : LoopIdx (Z2 L))) = {1} := rfl
  have h2 : Finset.Ioc 1 (LoopIdx.length (⟨[s], [a]⟩ : LoopIdx (Z2 L))) = ∅ := rfl
  rw [h1, Finset.sum_singleton, h2, Finset.sum_empty, mul_zero]

/-- The `-` 1-loop is the conjugate of the `+` 1-loop (Hermitian `H`). -/
private theorem Eq729A_gloop_one_false {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (a : Z2 L) :
    gloop L W H z ⟨[false], [a]⟩ = (starRingEnd ℂ) (gloop L W H z ⟨[true], [a]⟩) := by
  simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]
  rw [show Gsig H z false = (Gsig H z true).conjTranspose from
    (Gsig_conjTranspose hH z true).symm]
  change Matrix.trace ((Gsig H z true).conjTranspose * Eblk L W a)
    = star (Matrix.trace (Gsig H z true * Eblk L W a))
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Eblk_conjTranspose,
    Matrix.trace_mul_comm]

end Algebra

/-! ### Bounded measurable functions and expectations on a good event -/

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bounded and a.e.-strongly measurable. -/
private def Eq729A_BM (μ : Measure Ω) (f : Ω → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C, ∀ ω, ‖f ω‖ ≤ C

private theorem Eq729A_BM_const (c : ℂ) : Eq729A_BM μ (fun _ => c) :=
  ⟨aestronglyMeasurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem Eq729A_BM.add {f g : Ω → ℂ} (hf : Eq729A_BM μ f) (hg : Eq729A_BM μ g) :
    Eq729A_BM μ (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem Eq729A_BM.sub {f g : Ω → ℂ} (hf : Eq729A_BM μ f) (hg : Eq729A_BM μ g) :
    Eq729A_BM μ (fun ω => f ω - g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem Eq729A_BM.mul {f g : Ω → ℂ} (hf : Eq729A_BM μ f) (hg : Eq729A_BM μ g) :
    Eq729A_BM μ (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

private theorem Eq729A_BM.sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℂ}
    (hf : ∀ i ∈ s, Eq729A_BM μ (f i)) : Eq729A_BM μ (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Eq729A_BM_const (μ := μ) 0
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

private theorem Eq729A_BM.integrable [IsFiniteMeasure μ] {f : Ω → ℂ} (hf : Eq729A_BM μ f) :
    Integrable f μ := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact Integrable.of_bound hfm C (Eventually.of_forall hC)

/-- **Expectation on a good event**: `‖E f‖ ≤ g + C p` if `‖f‖ ≤ g` off `B`, `‖f‖ ≤ C`
everywhere, and `μ B ≤ p`. -/
private theorem Eq729A_norm_integral_le [IsProbabilityMeasure μ] {f : Ω → ℂ}
    (hf : Integrable f μ)
    {B : Set Ω} {g C p : ℝ} (hg : 0 ≤ g) (hC : 0 ≤ C) (hp : μ B ≤ ENNReal.ofReal p)
    (hp0 : 0 ≤ p) (hgood : ∀ ω ∉ B, ‖f ω‖ ≤ g) (hall : ∀ ω, ‖f ω‖ ≤ C) :
    ‖∫ ω, f ω ∂μ‖ ≤ g + C * p := by
  set T := toMeasurable μ B with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable μ B
  have hpt : ∀ ω, ‖f ω‖ ≤ g + T.indicator (fun _ => C) ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω]; linarith [hall ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact hgood ω fun h => hω (subset_toMeasurable μ B h)
  have hint : Integrable (fun ω => g + T.indicator (fun _ => C) ω) μ :=
    (integrable_const g).add ((integrable_const C).indicator hTm)
  have hμT : μ.real T ≤ p := by
    rw [Measure.real, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hp0 hp
  calc ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (g + T.indicator (fun _ => C) ω) ∂μ := integral_mono hf.norm hint hpt
    _ = g + μ.real T * C := by
        rw [integral_add (integrable_const g) ((integrable_const C).indicator hTm),
          integral_const, integral_indicator_const C hTm]
        simp
    _ ≤ g + C * p := by nlinarith

/-- `‖∫ W² ∑_{a,b} f_{ab}‖ ≤ W² ∑_{a,b} ‖∫ f_{ab}‖`. -/
private theorem Eq729A_norm_integral_Wsum_le {ι : Type*} [Fintype ι] (W : ℕ)
    (f : ι → ι → Ω → ℂ) (hf : ∀ a b, Integrable (f a b) μ) :
    ‖∫ ω, (W : ℂ) ^ 2 * ∑ a, ∑ b, f a b ω ∂μ‖ ≤ (W : ℝ) ^ 2 * ∑ a, ∑ b, ‖∫ ω, f a b ω ∂μ‖ := by
  rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hf a b]
  simp_rw [integral_finsetSum _ fun b _ => hf _ b]
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  exact Finset.sum_le_sum fun a _ => norm_sum_le _ _

end Measure

/-! ### The GUE-phase grid at a fixed size parameter -/

section GridFacts

variable (d : Sizes)

/-- The loop `L_{u_k}` of the GUE-phase grid path at grid step `k`. -/
def eq729F (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (n k : ℕ) (ω : PathΩ d)
    (I : LoopIdx (Z2 (d.L n))) : ℂ :=
  gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω))
    (spectralZ (E n) (gridTime t1 t0 K n k)) I

variable {d}

/-- `0 ≤ Δ`. -/
theorem eq729_step_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n) :
    0 ≤ gridStep t1 t0 K n :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- `u_{k+1} = u_k + Δ`. -/
private theorem Eq729A_time_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + gridStep t1 t0 K n := by
  unfold gridTime; push_cast; ring

/-- `K Δ = t₀ - t₁`. -/
theorem eq729_KΔ {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n := by
  unfold gridStep
  have : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  field_simp

/-- The grid times lie in `[t₁, t₀]`. -/
theorem eq729_time_mem {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (ht10 : t1 n ≤ t0 n)
    (hK : K n ≠ 0) (hk : k ≤ K n) :
    gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) := by
  have hΔ := eq729_step_nonneg (K := K) ht10
  have hkK : (k : ℝ) ≤ K n := by exact_mod_cast hk
  have h1 : (k : ℝ) * gridStep t1 t0 K n ≤ K n * gridStep t1 t0 K n :=
    mul_le_mul_of_nonneg_right hkK hΔ
  rw [eq729_KΔ hK] at h1
  constructor
  · unfold gridTime; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · unfold gridTime; linarith

/-- `0 < η_u`. -/
theorem eq729_eta_pos {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) : 0 < etaT E u :=
  etaT_pos hE hu

/-- `η_t ≤ η_u` for `u ≤ t`. -/
theorem eq729_eta_le {E : ℝ} (hE : |E| < 2) {u t : ℝ} (hut : u ≤ t) :
    etaT E t ≤ etaT E u := by
  unfold etaT; exact mul_le_mul_of_nonneg_right (by linarith) (spectralM_im_pos hE).le

/-- `Im z_u = η_u`. -/
theorem eq729_zt_im (E u : ℝ) : (spectralZ E u).im = etaT E u := spectralZ_im E u

/-- The loop at step `k` is a.e. strongly measurable (a measurable function of `gueH`). -/
private theorem Eq729A_loop_aesm {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (z : ℂ)
    (I : LoopIdx (Z2 (d.L n))) :
    AEStronglyMeasurable
      (fun ω => gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω)) z I) (Pgue d) :=
  ((GoodEvent_measurable_gloop (d.L n) (d.W n) z I).comp
    (gueH_measurable d t1 t0 K n k)).aestronglyMeasurable

/-- The crude bound on a well-formed loop of any length (for integrability only). -/
private theorem Eq729A_loop_bound_crude {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ}
    (hz : z.im ≠ 0) {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF) (ω : PathΩ d) :
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω)) z I‖ ≤
      (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) * (|z.im|⁻¹ * ((d.W n : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
  norm_gloop_le_crude (d.L n) (d.W n) ((gueH_isHermitian d t1 t0 K n k ω).submatrix _)
    (abs_pos.2 hz) le_rfl I hwf

/-- `‖𝓛_I‖ ≤ |Im z|^{-ℓ}` for a loop of length `ℓ ≥ 1`. -/
private theorem Eq729A_loop_bound {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ}
    (hz : z.im ≠ 0) {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (ω : PathΩ d) :
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω)) z I‖ ≤
      (|z.im|)⁻¹ ^ I.a.length := by
  have hH : (blockMat (gueH d t1 t0 K n k ω)).IsHermitian :=
    (gueH_isHermitian d t1 t0 K n k ω).submatrix _
  have h := RBM.Ind.norm_gloop_le_of_le_abs_im (L := d.L n) (W := d.W n) hH (abs_pos.2 hz)
    le_rfl I hwf hn
  refine h.trans ?_
  have hW : ((d.W n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast d.W_pos n)
  have hW0 : 0 ≤ ((d.W n : ℝ))⁻¹ := by positivity
  calc |z.im|⁻¹ ^ I.a.length * (((d.W n : ℝ))⁻¹ ^ 2) ^ (I.a.length - 1)
      ≤ |z.im|⁻¹ ^ I.a.length * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) (pow_le_one₀ hW0 hW)) (by positivity)
    _ = _ := mul_one _

/-- The loop at step `k` is bounded and measurable (any well-formed loop). -/
private theorem Eq729A_loop_BM {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF) :
    Eq729A_BM (Pgue d) (fun ω => gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n k ω)) z I) :=
  ⟨Eq729A_loop_aesm z I, _, Eq729A_loop_bound_crude hz hwf⟩

end GridFacts

/-! ### One step of the Duhamel formula in expectation -/

section Duhamel

/-- **Duhamel in expectation** (`condExp_loop_drift_gue` integrated): the martingale part has mean
`0`.
The loops are deterministically bounded, so every term is integrable. -/
theorem eq729_duhamel (d : Sizes) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ}
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) {k : ℕ}
    (hk : k < K n) {J : LoopIdx (Z2 (d.L n))} (hwf : J.WF)
    (hdrift : Integrable (fun ω => genMatGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k)
      (gueH d t1 t0 K n k ω) J) (Pgue d)) :
    ‖(∫ ω, eq729F d t1 t0 K E n (k + 1) ω J ∂(Pgue d)) -
        (∫ ω, eq729F d t1 t0 K E n k ω J ∂(Pgue d)) -
        (gridStep t1 t0 K n : ℂ) * ∫ ω, genMatGUE (d.L n) (d.W n) (E n)
          (gridTime t1 t0 K n k) (gueH d t1 t0 K n k ω) J ∂(Pgue d)‖
      ≤ envConst (d.L n) (d.W n) (E n) J.length (gridTime t1 t0 K n (k + 1)) *
          gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  have hKn : K n ≠ 0 := by omega
  have hu : ∀ j, j ≤ K n → gridTime t1 t0 K n j < 1 := fun j hj =>
    lt_of_le_of_lt (eq729_time_mem ht10 hKn hj).2 ht0
  have hz : ∀ j, j ≤ K n → (spectralZ (E n) (gridTime t1 t0 K n j)).im ≠ 0 := fun j hj => by
    rw [eq729_zt_im]; exact (eq729_eta_pos hE (hu j hj)).ne'
  have h := condExp_loop_drift_gue d t1 t0 K n k (E n) hE hwf ht1 ht10 hKn hk (hu (k + 1) hk)
  set f' : PathΩ d → ℂ := fun ω' => eq729F d t1 t0 K E n (k + 1) ω' J with hf'
  set f : PathΩ d → ℂ := fun ω' => eq729F d t1 t0 K E n k ω' J with hf
  have hf'i : Integrable f' (Pgue d) := (Eq729A_loop_BM (hz (k + 1) hk) hwf).integrable
  have hfi : Integrable f (Pgue d) := (Eq729A_loop_BM (hz k hk.le) hwf).integrable
  have hbound := norm_integral_le_of_norm_le_const h
  rw [probReal_univ, mul_one] at hbound
  set ce : PathΩ d → ℂ := (Pgue d)[f' | filt d k] with hce_def
  have hce : Integrable ce (Pgue d) := integrable_condExp
  have hid : (∫ x, (ce x - f x - (gridStep t1 t0 K n : ℂ) *
        genMatGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k) (gueH d t1 t0 K n k x) J)
        ∂(Pgue d))
      = (∫ x, f' x ∂(Pgue d)) - (∫ x, f x ∂(Pgue d)) - (gridStep t1 t0 K n : ℂ) *
        ∫ ω, genMatGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k)
          (gueH d t1 t0 K n k ω) J ∂(Pgue d) := by
    rw [integral_sub, integral_sub, integral_const_mul, hce_def,
      integral_condExp ((filt d).le k)]
    · exact hce
    · exact hfi
    · exact hce.sub hfi
    · exact hdrift.const_mul _
  refine (le_of_eq ?_).trans hbound
  exact congrArg norm hid.symm

end Duhamel

/-! ### Abstract expectation bounds for the drift terms on 2-loops -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {L : ℕ} [NeZero L] (W : ℕ)

private theorem Eq729A_sum_const (γ : ℝ) :
    (W : ℝ) ^ 2 * ∑ _a : Z2 L, ∑ _b : Z2 L, γ * ((L : ℝ) ^ 2)⁻¹ = (((W * L) ^ 2 : ℕ) : ℝ) * γ := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
  push_cast
  field_simp

omit [IsProbabilityMeasure μ] in
/-- `‖∫ W² ∑_{a,b} f_{ab}‖ ≤ N γ` if every `‖∫ f_{ab}‖ ≤ γ/L²`. -/
private theorem Eq729A_norm_integral_Wsum_le' (f : Z2 L → Z2 L → Ω → ℂ)
    (hf : ∀ a b, Integrable (f a b) μ) {γ : ℝ}
    (hγ : ∀ a b, ‖∫ ω, f a b ω ∂μ‖ ≤ γ * ((L : ℝ) ^ 2)⁻¹) :
    ‖∫ ω, (W : ℂ) ^ 2 * ∑ a, ∑ b, f a b ω ∂μ‖ ≤ (((W * L) ^ 2 : ℕ) : ℝ) * γ := by
  refine (Eq729A_norm_integral_Wsum_le W f hf).trans ?_
  rw [← Eq729A_sum_const W γ]
  gcongr with a _ b _
  exact hγ a b

omit [IsProbabilityMeasure μ] in
/-- The expectation passes through the deterministic left factor. -/
private theorem Eq729A_integral_primBil_left (K : LoopIdx (Z2 L) → ℂ)
    (G : Ω → LoopIdx (Z2 L) → ℂ) (e : LoopIdx (Z2 L) → ℂ) (s1 s2 : Bool) (a1 a2 : Z2 L)
    (hG : ∀ y, Integrable (fun ω => G ω ⟨[s1, s2], [a1, y]⟩) μ)
    (he : ∀ y, ∫ ω, G ω ⟨[s1, s2], [a1, y]⟩ ∂μ = e ⟨[s1, s2], [a1, y]⟩) :
    ∫ ω, primBilGUE L W K (G ω) ⟨[s1, s2], [a1, a2]⟩ ∂μ
      = primBilGUE L W K e ⟨[s1, s2], [a1, a2]⟩ := by
  simp_rw [eq729_primBil2]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hG b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, he]

omit [IsProbabilityMeasure μ] in
/-- The expectation passes through the deterministic right factor. -/
private theorem Eq729A_integral_primBil_right (K : LoopIdx (Z2 L) → ℂ)
    (G : Ω → LoopIdx (Z2 L) → ℂ) (e : LoopIdx (Z2 L) → ℂ) (s1 s2 : Bool) (a1 a2 : Z2 L)
    (hG : ∀ x, Integrable (fun ω => G ω ⟨[s1, s2], [x, a2]⟩) μ)
    (he : ∀ x, ∫ ω, G ω ⟨[s1, s2], [x, a2]⟩ ∂μ = e ⟨[s1, s2], [x, a2]⟩) :
    ∫ ω, primBilGUE L W (G ω) K ⟨[s1, s2], [a1, a2]⟩ ∂μ
      = primBilGUE L W e K ⟨[s1, s2], [a1, a2]⟩ := by
  simp_rw [eq729_primBil2]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((hG a).mul_const (SBgue L a b)).mul_const (K ⟨[s1, s2], [a1, b]⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ =>
    ((hG a).mul_const (SBgue L a b)).mul_const (K ⟨[s1, s2], [a1, b]⟩)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_mul_const, he]

/-- **The quadratic term** `E[(L-K) ∼ (L-K)]` on a 2-loop. -/
private theorem Eq729A_quad (D : Ω → LoopIdx (Z2 L) → ℂ) (s1 s2 : Bool) (a1 a2 : Z2 L)
    (hD : ∀ x y, Eq729A_BM μ (fun ω => D ω ⟨[s1, s2], [x, y]⟩)) {B : Set Ω} {g C p : ℝ}
    (hg : 0 ≤ g) (hC : 0 ≤ C) (hp : μ B ≤ ENNReal.ofReal p) (hp0 : 0 ≤ p)
    (hgood : ∀ ω ∉ B, ∀ x y, ‖D ω ⟨[s1, s2], [x, y]⟩‖ ≤ g)
    (hall : ∀ ω x y, ‖D ω ⟨[s1, s2], [x, y]⟩‖ ≤ C) :
    ‖∫ ω, primBilGUE L W (D ω) (D ω) ⟨[s1, s2], [a1, a2]⟩ ∂μ‖
      ≤ (((W * L) ^ 2 : ℕ) : ℝ) * (g * g + C * C * p) := by
  simp_rw [eq729_primBil2]
  refine Eq729A_norm_integral_Wsum_le' W _ (fun a b =>
    (((hD a a2).mul (Eq729A_BM_const _)).mul (hD a1 b)).integrable) fun a b => ?_
  have hL : (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ := by positivity
  have hSB : ‖SBgue L a b‖ = ((L : ℝ) ^ 2)⁻¹ := by
    rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
  have key := Eq729A_norm_integral_le (μ := μ)
    ((((hD a a2).mul (Eq729A_BM_const (SBgue L a b))).mul (hD a1 b)).integrable)
    (g := g * g * ((L : ℝ) ^ 2)⁻¹) (C := C * C * ((L : ℝ) ^ 2)⁻¹) (by positivity)
    (by positivity) hp hp0
    (fun ω hω => by
      rw [norm_mul, norm_mul, hSB]
      have h1 := hgood ω hω a a2
      have h2 := hgood ω hω a1 b
      calc ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ((L : ℝ) ^ 2)⁻¹ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖
          = ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖ * ((L : ℝ) ^ 2)⁻¹ := by ring
        _ ≤ g * g * ((L : ℝ) ^ 2)⁻¹ := by gcongr)
    (fun ω => by
      rw [norm_mul, norm_mul, hSB]
      have h1 := hall ω a a2
      have h2 := hall ω a1 b
      calc ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ((L : ℝ) ^ 2)⁻¹ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖
          = ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖ * ((L : ℝ) ^ 2)⁻¹ := by ring
        _ ≤ C * C * ((L : ℝ) ^ 2)⁻¹ := by gcongr)
  refine key.trans (le_of_eq ?_)
  ring

/-- One `E^{(G)}` pair: `‖E[X (1/L²) T]‖ ≤ (αβ + g₁g₃ + C₁C₃ p)/L²`, from `E T = κ + E(T - κ)`. -/
private theorem Eq729A_pair (X T : Ω → ℂ) (κ c : ℂ) (hX : Eq729A_BM μ X) (hT : Eq729A_BM μ T)
    {B : Set Ω} {α β g1 g3 C1 C3 p : ℝ} (hα : ‖∫ ω, X ω ∂μ‖ ≤ α) (hκ : ‖κ‖ ≤ β)
    (hg1 : 0 ≤ g1) (hg3 : 0 ≤ g3) (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3) (hc : 0 ≤ ‖c‖)
    (hp : μ B ≤ ENNReal.ofReal p) (hp0 : 0 ≤ p)
    (hgood : ∀ ω ∉ B, ‖X ω‖ ≤ g1 ∧ ‖T ω - κ‖ ≤ g3)
    (hall : ∀ ω, ‖X ω‖ ≤ C1 ∧ ‖T ω - κ‖ ≤ C3) :
    ‖∫ ω, X ω * c * T ω ∂μ‖ ≤ (α * β + (g1 * g3 + C1 * C3 * p)) * ‖c‖ := by
  have hα0 : 0 ≤ α := (norm_nonneg _).trans hα
  have hXi := hX.integrable
  have hTκ : Eq729A_BM μ (fun ω => T ω - κ) := hT.sub (Eq729A_BM_const κ)
  have hsplit : (fun ω => X ω * c * T ω) = fun ω => c * (X ω * κ + X ω * (T ω - κ)) := by
    funext ω; ring
  have hint2 : Integrable (fun ω => X ω * (T ω - κ)) μ := (hX.mul hTκ).integrable
  rw [hsplit, integral_const_mul, integral_add (hXi.mul_const κ) hint2, integral_mul_const,
    norm_mul]
  have h2 := Eq729A_norm_integral_le (μ := μ) hint2 (g := g1 * g3) (C := C1 * C3)
    (by positivity) (by positivity) hp hp0
    (fun ω hω => by
      rw [norm_mul]; exact mul_le_mul (hgood ω hω).1 (hgood ω hω).2 (norm_nonneg _) hg1)
    (fun ω => by rw [norm_mul]; exact mul_le_mul (hall ω).1 (hall ω).2 (norm_nonneg _) hC1)
  have h1 : ‖(∫ ω, X ω ∂μ) * κ‖ ≤ α * β := by
    rw [norm_mul]; exact mul_le_mul hα hκ (norm_nonneg _) hα0
  calc ‖c‖ * ‖(∫ ω, X ω ∂μ) * κ + ∫ ω, X ω * (T ω - κ) ∂μ‖
      ≤ ‖c‖ * (α * β + (g1 * g3 + C1 * C3 * p)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) hc
    _ = _ := by ring

end Abstract

/-! ### One grid step of `K̃` on 2-loops -/

section KDisc

variable {L W : ℕ} [NeZero L]

/-- `primRhsGUE` on a 2-loop is bounded by `N b²`, `N = (W L)²`. -/
theorem eq729_norm_primRhs2_le (K : LoopIdx (Z2 L) → ℂ) {b : ℝ}
    (hb : ∀ s1 s2 x y, ‖K ⟨[s1, s2], [x, y]⟩‖ ≤ b) (s1 s2 : Bool) (a1 a2 : Z2 L) :
    ‖primRhsGUE L W K ⟨[s1, s2], [a1, a2]⟩‖ ≤ (((W * L) ^ 2 : ℕ) : ℝ) * b * b :=
  eq729_norm_primBil2_le L W K K s1 s2 a1 a2 (fun x => hb s1 s2 x a2) (fun y => hb s1 s2 a1 y)

/-- **One grid step of the primitive 2-loop**: `‖K̃_u + Δ·(d/dt K̃)_u - K̃_{u+Δ}‖ ≤ 3 N² Δ²`,
`N = (W L)²`. -/
theorem eq729_Kdisc (Kf : ℝ → LoopIdx (Z2 L) → ℂ) {t1 t0 u Δ b2 : ℝ}
    (hu : u ∈ Set.Icc t1 t0) (hu' : u + Δ ∈ Set.Icc t1 t0) (hΔ : 0 ≤ Δ) (hb2 : b2 ≤ 1)
    (hMΔ : (((W * L) ^ 2 : ℕ) : ℝ) * Δ ≤ 1)
    (hKb : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖Kf s ⟨[s1, s2], [x, y]⟩‖ ≤ b2)
    (hKd : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kf s ⟨[s1, s2], [x, y]⟩)
      (primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩) (Set.Icc t1 t0) s)
    (s1 s2 : Bool) (a1 a2 : Z2 L) :
    ‖Kf u ⟨[s1, s2], [a1, a2]⟩ + (Δ : ℂ) * primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩
        - Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤ 3 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 * Δ ^ 2 := by
  set M : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hb20 : 0 ≤ b2 := (norm_nonneg _).trans (hKb u hu true true 0 0)
  set S : Set ℝ := Set.Icc u (u + Δ) with hS
  have hSsub : S ⊆ Set.Icc t1 t0 := fun s hs => ⟨hu.1.trans hs.1, hs.2.trans hu'.2⟩
  have hSconv : Convex ℝ S := convex_Icc _ _
  have huS : u ∈ S := ⟨le_rfl, by linarith⟩
  have hu'S : u + Δ ∈ S := ⟨by linarith, le_rfl⟩
  -- (a) the derivative is bounded by `M`
  have hder : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y,
      ‖primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩‖ ≤ M := by
    intro s hs s1 s2 x y
    refine (eq729_norm_primRhs2_le (W := W) (Kf s) (hKb s hs) s1 s2 x y).trans ?_
    calc M * b2 * b2 ≤ M * 1 * 1 := by gcongr
      _ = M := by ring
  -- (b) `‖K̃_s - K̃_u‖ ≤ M Δ` on `[u, u + Δ]`
  have hmove : ∀ s ∈ S, ∀ s1 s2 x y,
      ‖Kf s ⟨[s1, s2], [x, y]⟩ - Kf u ⟨[s1, s2], [x, y]⟩‖ ≤ M * Δ := by
    intro s hs s1 s2 x y
    have h := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => Kf s ⟨[s1, s2], [x, y]⟩)
      (f' := fun s => primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩)
      (fun r hr => (hKd r (hSsub hr) s1 s2 x y).mono hSsub)
      (fun r hr => hder r (hSsub hr) s1 s2 x y) huS hs
    refine h.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM0
  have hδ1 : M * Δ ≤ 1 := hMΔ
  have hδ0 : 0 ≤ M * Δ := mul_nonneg hM0 hΔ
  -- (c) the derivative moves by at most `3 M² Δ`
  have hgmove : ∀ s ∈ S, ‖primRhsGUE L W (Kf s) ⟨[s1, s2], [a1, a2]⟩
      - primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩‖ ≤ 3 * M ^ 2 * Δ := by
    intro s hs
    rw [primRhsGUE_sub]
    have hdiff : ∀ s1 s2 x y, ‖(Kf s - Kf u) ⟨[s1, s2], [x, y]⟩‖ ≤ M * Δ := fun s1 s2 x y => by
      rw [Pi.sub_apply]; exact hmove s hs s1 s2 x y
    have e1 := eq729_norm_primBil2_le L W (Kf u) (Kf s - Kf u) s1 s2 a1 a2
      (fun x => hKb u hu s1 s2 x a2) (fun y => hdiff s1 s2 a1 y)
    have e2 := eq729_norm_primBil2_le L W (Kf s - Kf u) (Kf u) s1 s2 a1 a2
      (fun x => hdiff s1 s2 x a2) (fun y => hKb u hu s1 s2 a1 y)
    have e3 := eq729_norm_primBil2_le L W (Kf s - Kf u) (Kf s - Kf u) s1 s2 a1 a2
      (fun x => hdiff s1 s2 x a2) (fun y => hdiff s1 s2 a1 y)
    have h1 : M * b2 * (M * Δ) ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_right hb2 hδ0; nlinarith
    have h2 : M * (M * Δ) * b2 ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_right hb2 hδ0; nlinarith
    have h3 : M * (M * Δ) * (M * Δ) ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_left hδ1 hδ0; nlinarith
    calc _ ≤ ‖primBilGUE L W (Kf u) (Kf s - Kf u) ⟨[s1, s2], [a1, a2]⟩‖
          + ‖primBilGUE L W (Kf s - Kf u) (Kf u) ⟨[s1, s2], [a1, a2]⟩‖
          + ‖primBilGUE L W (Kf s - Kf u) (Kf s - Kf u) ⟨[s1, s2], [a1, a2]⟩‖ :=
          norm_add₃_le
      _ ≤ M * (M * Δ) + M * (M * Δ) + M * (M * Δ) := by linarith
      _ = 3 * M ^ 2 * Δ := by ring
  -- (d) the mean value inequality for `φ(s) = K̃_s - (s - u) (d/dt K̃)_u`
  set c : ℂ := primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩ with hc
  have hφ : ∀ r ∈ S, HasDerivWithinAt
      (fun s => Kf s ⟨[s1, s2], [a1, a2]⟩ - ((s - u : ℝ) : ℂ) * c)
      (primRhsGUE L W (Kf r) ⟨[s1, s2], [a1, a2]⟩ - ((1 : ℝ) : ℂ) * c) S r := by
    intro r hr
    have h1 := (hKd r (hSsub hr) s1 s2 a1 a2).mono hSsub
    have h2 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ) * c) (((1 : ℝ) : ℂ) * c) r :=
      (((hasDerivAt_id r).sub_const u).ofReal_comp).mul_const c
    exact h1.sub h2.hasDerivWithinAt
  have hmvt := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le hφ
    (fun r hr => by
      rw [Complex.ofReal_one, one_mul]; exact hgmove r hr) huS hu'S
  have heq : Kf u ⟨[s1, s2], [a1, a2]⟩ + (Δ : ℂ) * c - Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩
      = -((Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩ - ((u + Δ - u : ℝ) : ℂ) * c)
          - (Kf u ⟨[s1, s2], [a1, a2]⟩ - ((u - u : ℝ) : ℂ) * c)) := by
    push_cast; ring
  rw [heq, norm_neg]
  refine hmvt.trans (le_of_eq ?_)
  rw [show u + Δ - u = Δ by ring, Real.norm_eq_abs, abs_of_nonneg hΔ]
  ring

end KDisc

/-! ### The drift of a 2-loop along the grid path -/

section DriftTwo

/-- The generator on a 2-loop (`loopGenGUE` at `k = 2`, in list form). -/
private theorem Eq729A_genMat_two (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (s1 s2 : Bool) (a1 a2 : Z2 L) :
    genMatGUE L W E u M ⟨[s1, s2], [a1, a2]⟩ =
      primRhsGUE L W (RBM.Ind.LLf L W E u M) ⟨[s1, s2], [a1, a2]⟩ +
        egtNGUE L W E u M ⟨[s1, s2], [a1, a2]⟩ :=
  loopGenGUE L W E hL hE u hu0 hu1 M hM 2 le_rfl ![s1, s2] ![a1, a2]

variable (d : Sizes)

/-- The `𝓔^{(G̃)}` part of the drift of a 2-loop is bounded and measurable. -/
private theorem Eq729A_BM_eG {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n k : ℕ}
    (hz : (spectralZ (E n) (gridTime t1 t0 K n k)).im ≠ 0) (s1 s2 : Bool)
    (a1 a2 : Z2 (d.L n)) :
    Eq729A_BM (Pgue d) (fun ω => egtNGUE (d.L n) (d.W n) (E n) (gridTime t1 t0 K n k)
      (gueH d t1 t0 K n k ω) ⟨[s1, s2], [a1, a2]⟩) := by
  have hFBM : ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω I) := fun I h => Eq729A_loop_BM hz h
  simp_rw [eq729_eG2]
  refine (Eq729A_BM_const _).mul (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ => ?_)
  exact ((((hFBM ⟨[s1], [a]⟩ rfl).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
    (hFBM ⟨[s1, s1, s2], [b, a1, a2]⟩ rfl)).add
    ((((hFBM ⟨[s2], [a]⟩ rfl).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
      (hFBM ⟨[s1, s2, s2], [a1, b, a2]⟩ rfl))

/-- The `primRhsGUE` part of the drift of a 2-loop is bounded and measurable. -/
private theorem Eq729A_BM_prim {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n k : ℕ}
    (hz : (spectralZ (E n) (gridTime t1 t0 K n k)).im ≠ 0) (s1 s2 : Bool)
    (a1 a2 : Z2 (d.L n)) :
    Eq729A_BM (Pgue d) (fun ω => primRhsGUE (d.L n) (d.W n) (eq729F d t1 t0 K E n k ω)
      ⟨[s1, s2], [a1, a2]⟩) := by
  have hFBM : ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω I) := fun I h => Eq729A_loop_BM hz h
  simp_rw [primRhsGUE, eq729_primBil2]
  exact (Eq729A_BM_const _).mul (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
    ((hFBM ⟨[s1, s2], [a, a2]⟩ rfl).mul (Eq729A_BM_const _)).mul
      (hFBM ⟨[s1, s2], [a1, b]⟩ rfl))

end DriftTwo

/-! ### One step of the recursion for `e_k = E L_{u_k} - K̃_{u_k}` on 2-loops -/

section OneStep

/-- `e_k(I) = E L_{u_k}(I) - K̃_{u_k}(I)`. -/
def eq729e (d : Sizes) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n k : ℕ) (I : LoopIdx (Z2 (d.L n))) : ℂ :=
  (∫ ω, eq729F d t1 t0 K E n k ω I ∂(Pgue d)) - Kt n (gridTime t1 t0 K n k) I

/-- The additive error of one step; `N = (W L)²` rows.  The last-but-one term is
the envelope `envConst … 2 = 16·5⁴·N⁴ (1+η⁻¹)⁶ = 10000 N⁴ (1+η⁻¹)⁶` with `η⁻¹ ≤ N`. -/
def eq729c (N ρ Λ p Δ : ℝ) : ℝ :=
  Δ * (N * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * N ^ 2) * (2 * N ^ 2) * p)
      + N * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p))))
    + 10000 * N ^ 4 * (1 + N) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * N ^ 2 * Δ ^ 2

/-- **One step** of the recursion (at a single grid step).  `N = d.size n = (W L)²`.  The
hypotheses `hX`, `hB`, `hg1`–`hg3`, `hBk` are the stochastic inputs of the second half
(`gueGrid_expect_oneLoop`, the `lk` field of `GUEPathBounds`). -/
theorem eq729_one_step (d : Sizes) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ}
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {Λ ρ p Bk : ℝ}
    (hΛ : Λ = (((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((d.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE (d.L n) (d.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 n) (t0 n)) s)
    {k : ℕ} (hk : k < K n)
    (hX : ∀ a, ‖(∫ ω, eq729F d t1 t0 K E n k ω ⟨[true], [a]⟩ ∂(Pgue d)) - spectralM (E n)‖
      ≤ ρ * Λ ^ 2)
    {B : Set (PathΩ d)} (hB : Pgue d B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ σ a, ‖eq729F d t1 t0 K E n k ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ s1 s2 x y, ‖eq729F d t1 t0 K E n k ω ⟨[s1, s2], [x, y]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ s1 s2 s3 x y w, ‖eq729F d t1 t0 K E n k ω ⟨[s1, s2, s3], [x, y, w]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hBk : ∀ s1 s2 x y, ‖eq729e d t1 t0 K E Kt n k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk)
    (s1 s2 : Bool) (a1 a2 : Z2 (d.L n)) :
    ‖eq729e d t1 t0 K E Kt n (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      (1 + gridStep t1 t0 K n * (2 * ((d.size n : ℕ) : ℝ) * (ρ * Λ))) * Bk
        + eq729c ((d.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n) := by
  classical
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set Δ : ℝ := gridStep t1 t0 K n with hΔ
  set u : ℝ := gridTime t1 t0 K n k with hu_def
  set z : ℂ := spectralZ (E n) u with hz_def
  set J : LoopIdx (Z2 (d.L n)) := ⟨[s1, s2], [a1, a2]⟩ with hJ
  have hKN : K n ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := eq729_step_nonneg ht10
  have hu : u ∈ Set.Icc (t1 n) (t0 n) := eq729_time_mem ht10 hKN hk.le
  have hu' : u + Δ ∈ Set.Icc (t1 n) (t0 n) := by
    rw [hu_def, hΔ, ← Eq729A_time_succ]; exact eq729_time_mem ht10 hKN hk
  have hM1 : 1 ≤ N := by
    have hpos : 0 < d.size n := by
      unfold Sizes.size
      exact pow_pos (Nat.mul_pos (d.W_pos n) (by have := d.three_le_L n; omega)) 2
    rw [hN]; exact_mod_cast hpos
  have hM0 : 0 ≤ N := by linarith
  -- the scale: `η_u⁻¹ ≤ N` on `[t₁, t₀]`
  have hη0 : 0 < etaT (E n) (t0 n) := eq729_eta_pos hE ht0
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have hΛ0 : 0 ≤ Λ := hΛpos.le
  have hηM : ∀ r ∈ Set.Icc (t1 n) (t0 n), |(spectralZ (E n) r).im|⁻¹ ≤ N := by
    intro r hr
    rw [eq729_zt_im]
    have hr1 : etaT (E n) (t0 n) ≤ etaT (E n) r := eq729_eta_le hE hr.2
    rw [abs_of_pos (hη0.trans_le hr1)]
    have hMη : 1 ≤ N * etaT (E n) (t0 n) := by
      have : (N * etaT (E n) (t0 n))⁻¹ ≤ 1 := by rw [← hΛ]; exact hΛ1
      have hpos : 0 < N * etaT (E n) (t0 n) := by positivity
      rwa [inv_le_one₀ hpos] at this
    rw [inv_le_iff_one_le_mul₀ (hη0.trans_le hr1)]
    nlinarith
  have hzne : z.im ≠ 0 := by
    rw [hz_def, eq729_zt_im]; exact (eq729_eta_pos hE (lt_of_le_of_lt hu.2 ht0)).ne'
  have hηz : |z.im|⁻¹ ≤ N := hηM u hu
  -- loops at step `k`: bounded and measurable
  have hFBM : ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω I) := fun I h1 =>
    Eq729A_loop_BM hzne h1
  have hFb : ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.a.length → ∀ ω,
      ‖eq729F d t1 t0 K E n k ω I‖ ≤ N ^ I.a.length := fun I h1 h2 ω =>
    (Eq729A_loop_bound hzne h1 h2 ω).trans (pow_le_pow_left₀ (by positivity) hηz _)
  have hFBM1 : ∀ σ a, Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω ⟨[σ], [a]⟩) :=
    fun σ a => hFBM _ rfl
  have hFBM2 : ∀ σ₁ σ₂ x y,
      Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω ⟨[σ₁, σ₂], [x, y]⟩) :=
    fun σ₁ σ₂ x y => hFBM _ rfl
  have hFBM3 : ∀ σ₁ σ₂ σ₃ x y w,
      Eq729A_BM (Pgue d) (fun ω => eq729F d t1 t0 K E n k ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩) :=
    fun σ₁ σ₂ σ₃ x y w => hFBM _ rfl
  set Kk : LoopIdx (Z2 (d.L n)) → ℂ := Kt n u with hKk
  set F : PathΩ d → LoopIdx (Z2 (d.L n)) → ℂ := fun ω I => eq729F d t1 t0 K E n k ω I with hF
  set e : LoopIdx (Z2 (d.L n)) → ℂ := eq729e d t1 t0 K E Kt n k with he
  -- the drift, pointwise
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht0
  have hu0 : 0 ≤ u := ht1.trans hu.1
  have hdrift_eq : ∀ ω, genMatGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J
      = primRhsGUE (d.L n) (d.W n) (F ω) J
        + egtNGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J := fun ω =>
    Eq729A_genMat_two (d.L n) (d.W n) (d.three_le_L n) hE hu0 hu1
      (gueH_isHermitian d t1 t0 K n k ω) s1 s2 a1 a2
  have heG_eq : ∀ ω, egtNGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J
      = (d.W n : ℂ) ^ 2 * ∑ a : Z2 (d.L n), ∑ b : Z2 (d.L n),
        ((F ω ⟨[s1], [a]⟩ - KLoop.mSig (E n) s1) * SBgue (d.L n) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - KLoop.mSig (E n) s2) * SBgue (d.L n) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) := fun ω =>
    eq729_eG2 (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) s1 s2 a1 a2
  have hBMeG : Eq729A_BM (Pgue d)
      (fun ω => egtNGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J) :=
    Eq729A_BM_eG d K hzne s1 s2 a1 a2
  have hBMprim : Eq729A_BM (Pgue d) (fun ω => primRhsGUE (d.L n) (d.W n) (F ω) J) :=
    Eq729A_BM_prim d K hzne s1 s2 a1 a2
  have hdrift_int : Integrable (fun ω => genMatGUE (d.L n) (d.W n) (E n) u
      (gueH d t1 t0 K n k ω) J) (Pgue d) := by
    simp_rw [hdrift_eq]; exact (hBMprim.add hBMeG).integrable
  -- (R1) Duhamel in expectation
  have hR1 := eq729_duhamel d K hE ht1 ht10 ht0 hk (J := J) rfl hdrift_int
  -- (R2) the primitive side
  have hR2 := eq729_Kdisc (L := d.L n) (W := d.W n) (Kt n) hu hu' hΔ0 hρΛ hMΔ hK2b hKd
    s1 s2 a1 a2
  have htime : gridTime t1 t0 K n (k + 1) = u + Δ := Eq729A_time_succ t1 t0 K n k
  -- split of the drift in expectation
  set D : PathΩ d → LoopIdx (Z2 (d.L n)) → ℂ := fun ω => F ω - Kk with hD
  have hDBM2 : ∀ x y, Eq729A_BM (Pgue d) (fun ω => D ω ⟨[s1, s2], [x, y]⟩) := fun x y =>
    (hFBM2 s1 s2 x y).sub (Eq729A_BM_const _)
  have hDint : ∀ x y, ∫ ω, D ω ⟨[s1, s2], [x, y]⟩ ∂(Pgue d) = e ⟨[s1, s2], [x, y]⟩ := by
    intro x y
    simp only [hD, Pi.sub_apply]
    rw [integral_sub (hFBM2 s1 s2 x y).integrable (integrable_const _), integral_const,
      probReal_univ, one_smul]
    rfl
  have hprim_split : ∀ ω, primRhsGUE (d.L n) (d.W n) (F ω) J
      = primRhsGUE (d.L n) (d.W n) Kk J
        + primBilGUE (d.L n) (d.W n) Kk (D ω) J
        + primBilGUE (d.L n) (d.W n) (D ω) Kk J
        + primBilGUE (d.L n) (d.W n) (D ω) (D ω) J := by
    intro ω
    have := primRhsGUE_sub (d.L n) (d.W n) (F ω) Kk J
    simp only [hD]
    linear_combination this
  have hBMbilL : Eq729A_BM (Pgue d) (fun ω => primBilGUE (d.L n) (d.W n) Kk (D ω) J) := by
    simp_rw [hJ, eq729_primBil2]
    exact (Eq729A_BM_const _).mul (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      ((Eq729A_BM_const _).mul (Eq729A_BM_const _)).mul (hDBM2 a1 b))
  have hBMbilR : Eq729A_BM (Pgue d) (fun ω => primBilGUE (d.L n) (d.W n) (D ω) Kk J) := by
    simp_rw [hJ, eq729_primBil2]
    exact (Eq729A_BM_const _).mul (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      ((hDBM2 a a2).mul (Eq729A_BM_const _)).mul (Eq729A_BM_const _))
  have hBMbilQ : Eq729A_BM (Pgue d) (fun ω => primBilGUE (d.L n) (d.W n) (D ω) (D ω) J) := by
    simp_rw [hJ, eq729_primBil2]
    exact (Eq729A_BM_const _).mul (Eq729A_BM.sum _ fun a _ => Eq729A_BM.sum _ fun b _ =>
      ((hDBM2 a a2).mul (Eq729A_BM_const _)).mul (hDBM2 a1 b))
  have hprim_int : ∫ ω, primRhsGUE (d.L n) (d.W n) (F ω) J ∂(Pgue d)
      = primRhsGUE (d.L n) (d.W n) Kk J
        + primBilGUE (d.L n) (d.W n) Kk e J
        + primBilGUE (d.L n) (d.W n) e Kk J
        + ∫ ω, primBilGUE (d.L n) (d.W n) (D ω) (D ω) J ∂(Pgue d) := by
    simp_rw [hprim_split]
    have i1 : Integrable (fun ω => primRhsGUE (d.L n) (d.W n) Kk J
        + primBilGUE (d.L n) (d.W n) Kk (D ω) J) (Pgue d) :=
      (integrable_const _).add hBMbilL.integrable
    have i2 : Integrable (fun ω => primRhsGUE (d.L n) (d.W n) Kk J
        + primBilGUE (d.L n) (d.W n) Kk (D ω) J
        + primBilGUE (d.L n) (d.W n) (D ω) Kk J) (Pgue d) :=
      i1.add hBMbilR.integrable
    rw [integral_add i2 hBMbilQ.integrable, integral_add i1 hBMbilR.integrable,
      integral_add (integrable_const _) hBMbilL.integrable, integral_const, probReal_univ,
      one_smul,
      Eq729A_integral_primBil_left (d.W n) Kk D e s1 s2 a1 a2
        (fun y => (hDBM2 a1 y).integrable) (fun y => hDint a1 y),
      Eq729A_integral_primBil_right (d.W n) Kk D e s1 s2 a1 a2
        (fun x => (hDBM2 x a2).integrable) (fun x => hDint x a2)]
  have hdrift_int_eq : ∫ ω, genMatGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J ∂(Pgue d)
      = (∫ ω, primRhsGUE (d.L n) (d.W n) (F ω) J ∂(Pgue d))
        + ∫ ω, egtNGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J ∂(Pgue d) := by
    simp_rw [hdrift_eq]
    exact integral_add hBMprim.integrable hBMeG.integrable
  -- the exact identity
  set R1 : ℂ := (∫ ω, eq729F d t1 t0 K E n (k + 1) ω J ∂(Pgue d))
      - (∫ ω, eq729F d t1 t0 K E n k ω J ∂(Pgue d))
      - (Δ : ℂ) * ∫ ω, genMatGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J ∂(Pgue d)
    with hR1def
  set R2 : ℂ := Kk J + (Δ : ℂ) * primRhsGUE (d.L n) (d.W n) Kk J - Kt n (u + Δ) J
    with hR2def
  set IeG : ℂ := ∫ ω, egtNGUE (d.L n) (d.W n) (E n) u (gueH d t1 t0 K n k ω) J ∂(Pgue d)
    with hIeG
  set IQ : ℂ := ∫ ω, primBilGUE (d.L n) (d.W n) (D ω) (D ω) J ∂(Pgue d) with hIQ
  set lin : ℂ := primBilGUE (d.L n) (d.W n) Kk e J
    + primBilGUE (d.L n) (d.W n) e Kk J with hlin
  have hident : eq729e d t1 t0 K E Kt n (k + 1) J
      = (e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2 := by
    have h1 : eq729e d t1 t0 K E Kt n (k + 1) J
        = (∫ ω, eq729F d t1 t0 K E n (k + 1) ω J ∂(Pgue d)) - Kt n (u + Δ) J := by
      rw [eq729e, htime]
    have h2 : e J = (∫ ω, eq729F d t1 t0 K E n k ω J ∂(Pgue d)) - Kk J := rfl
    rw [h1, h2, hR1def, hR2def, hdrift_int_eq, hprim_int]
    ring
  -- bounds
  have hΔn : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ0]
  have hlinb : ‖lin‖ ≤ 2 * N * (ρ * Λ) * Bk := by
    have e1 := eq729_norm_primBil2_le (d.L n) (d.W n) Kk e s1 s2 a1 a2
      (fun x => hK2b u hu s1 s2 x a2) (fun y => hBk s1 s2 a1 y)
    have e2 := eq729_norm_primBil2_le (d.L n) (d.W n) e Kk s1 s2 a1 a2
      (fun x => hBk s1 s2 x a2) (fun y => hK2b u hu s1 s2 a1 y)
    calc ‖lin‖ ≤ _ + _ := norm_add_le _ _
      _ ≤ N * (ρ * Λ) * Bk + N * Bk * (ρ * Λ) := add_le_add e1 e2
      _ = 2 * N * (ρ * Λ) * Bk := by ring
  have hBk0 : 0 ≤ Bk := (norm_nonneg _).trans (hBk s1 s2 a1 a2)
  have hlead : ‖e J + (Δ : ℂ) * lin‖ ≤ (1 + Δ * (2 * N * (ρ * Λ))) * Bk := by
    calc ‖e J + (Δ : ℂ) * lin‖ ≤ ‖e J‖ + Δ * ‖lin‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, hΔn]
      _ ≤ Bk + Δ * (2 * N * (ρ * Λ) * Bk) :=
          add_le_add (hBk s1 s2 a1 a2) (mul_le_mul_of_nonneg_left hlinb hΔ0)
      _ = (1 + Δ * (2 * N * (ρ * Λ))) * Bk := by ring
  -- the quadratic term
  have hρΛ2 : ρ * Λ ^ 2 ≤ 1 := by
    calc ρ * Λ ^ 2 = (ρ * Λ) * Λ := by ring
      _ ≤ 1 * 1 := mul_le_mul hρΛ hΛ1 hΛ0 zero_le_one
      _ = 1 := by ring
  have hQ : ‖IQ‖ ≤ N * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * N ^ 2) * (2 * N ^ 2) * p) := by
    have := Eq729A_quad (μ := Pgue d) (d.W n) D s1 s2 a1 a2 hDBM2 (g := ρ * Λ ^ 2)
      (C := 2 * N ^ 2) (by positivity) (by positivity) hB hp0
      (fun ω hω x y => hg2 ω hω s1 s2 x y)
      (fun ω x y => by
        simp only [hD, Pi.sub_apply]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖F ω ⟨[s1, s2], [x, y]⟩‖ ≤ N ^ 2 := hFb ⟨[s1, s2], [x, y]⟩ rfl (by simp) ω
        have h2 : ‖Kk ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := hK2b u hu s1 s2 x y
        have : N ^ 2 ≥ 1 := one_le_pow₀ hM1
        nlinarith)
    exact this
  -- the 1-loop input
  have hXall : ∀ σ a, ‖∫ ω, (F ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ) ∂(Pgue d)‖ ≤ ρ * Λ ^ 2 := by
    intro σ a
    have htrue : ∫ ω, (F ω ⟨[true], [a]⟩ - KLoop.mSig (E n) true) ∂(Pgue d)
        = (∫ ω, eq729F d t1 t0 K E n k ω ⟨[true], [a]⟩ ∂(Pgue d)) - spectralM (E n) := by
      rw [integral_sub (hFBM1 true a).integrable (integrable_const _), integral_const,
        probReal_univ, one_smul]
      rfl
    cases σ with
    | true => rw [htrue]; exact hX a
    | false =>
      have hconj : (fun ω => F ω ⟨[false], [a]⟩ - KLoop.mSig (E n) false)
          = fun ω => (starRingEnd ℂ) (F ω ⟨[true], [a]⟩ - KLoop.mSig (E n) true) := by
        funext ω
        simp only [hF, eq729F, KLoop.mSig, map_sub, ite_true, Bool.false_eq_true, ite_false]
        have hH : (blockMat (gueH d t1 t0 K n k ω)).IsHermitian :=
          (gueH_isHermitian d t1 t0 K n k ω).submatrix _
        rw [Eq729A_gloop_one_false hH]
      rw [hconj, integral_conj, RCLike.norm_conj, htrue]
      exact hX a
  have hSBn : ∀ a b : Z2 (d.L n), ‖SBgue (d.L n) a b‖ = ((d.L n : ℝ) ^ 2)⁻¹ := by
    intro a b; rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
  have hXb : ∀ σ a ω, ‖F ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ‖ ≤ 2 * N := by
    intro σ a ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ], [a]⟩‖ ≤ N ^ 1 := hFb ⟨[σ], [a]⟩ rfl (by simp) ω
    rw [pow_one] at h1
    have h2 : ‖KLoop.mSig (E n) σ‖ = 1 := by
      cases σ <;> simp [KLoop.mSig, norm_spectralM hE.le]
    rw [h2]
    linarith
  have hTb : ∀ σ₁ σ₂ σ₃ x y w ω, ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ - Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖
      ≤ 2 * N ^ 3 := by
    intro σ₁ σ₂ σ₃ x y w ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ N ^ 3 :=
      hFb ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ rfl (by simp) ω
    have h2 : ‖Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := hK3b u hu σ₁ σ₂ σ₃ x y w
    have : N ^ 3 ≥ 1 := one_le_pow₀ hM1
    nlinarith
  have hpair : ∀ (σ : Bool) (a : Z2 (d.L n)) (T : PathΩ d → ℂ) (κ : ℂ) (c : ℂ),
      Eq729A_BM (Pgue d) T → ‖κ‖ ≤ ρ * Λ ^ 2 → ‖c‖ = ((d.L n : ℝ) ^ 2)⁻¹ →
      (∀ ω ∉ B, ‖T ω - κ‖ ≤ ρ * Λ ^ 3) → (∀ ω, ‖T ω - κ‖ ≤ 2 * N ^ 3) →
      ‖∫ ω, (F ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ) * c * T ω ∂(Pgue d)‖
        ≤ ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p))
          * ((d.L n : ℝ) ^ 2)⁻¹ := by
    intro σ a T κ c hT hκ hc hTg hTa
    have := Eq729A_pair (μ := Pgue d) (fun ω => F ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ) T κ c
      ((hFBM1 σ a).sub (Eq729A_BM_const _)) hT (hXall σ a) hκ (by positivity) (by positivity)
      (by positivity) (by positivity) (norm_nonneg _) hB hp0
      (fun ω hω => ⟨hg1 ω hω σ a, hTg ω hω⟩) (fun ω => ⟨hXb σ a ω, hTa ω⟩)
    rwa [hc] at this
  have heG : ‖IeG‖ ≤ N * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p))) := by
    rw [hIeG]
    simp_rw [heG_eq]
    have hint : ∀ a b, Integrable (fun ω =>
        (F ω ⟨[s1], [a]⟩ - KLoop.mSig (E n) s1) * SBgue (d.L n) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - KLoop.mSig (E n) s2) * SBgue (d.L n) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue d) := fun a b =>
      (((((hFBM1 s1 a).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
        (hFBM3 s1 s1 s2 b a1 a2)).add
        ((((hFBM1 s2 a).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
          (hFBM3 s1 s2 s2 a1 b a2))).integrable
    refine Eq729A_norm_integral_Wsum_le' (d.W n) _ hint fun a b => ?_
    have hi1 : Integrable (fun ω => (F ω ⟨[s1], [a]⟩ - KLoop.mSig (E n) s1) *
        SBgue (d.L n) a b * F ω ⟨[s1, s1, s2], [b, a1, a2]⟩) (Pgue d) :=
      ((((hFBM1 s1 a).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
        (hFBM3 s1 s1 s2 b a1 a2)).integrable
    have hi2 : Integrable (fun ω => (F ω ⟨[s2], [a]⟩ - KLoop.mSig (E n) s2) *
        SBgue (d.L n) a b * F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue d) :=
      ((((hFBM1 s2 a).sub (Eq729A_BM_const _)).mul (Eq729A_BM_const _)).mul
        (hFBM3 s1 s2 s2 a1 b a2)).integrable
    rw [integral_add hi1 hi2]
    have p1 := hpair s1 a (fun ω => F ω ⟨[s1, s1, s2], [b, a1, a2]⟩)
      (Kk ⟨[s1, s1, s2], [b, a1, a2]⟩) (SBgue (d.L n) a b) (hFBM3 s1 s1 s2 b a1 a2)
      (hK3b u hu s1 s1 s2 b a1 a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s1 s2 b a1 a2)
      (fun ω => hTb s1 s1 s2 b a1 a2 ω)
    have p2 := hpair s2 a (fun ω => F ω ⟨[s1, s2, s2], [a1, b, a2]⟩)
      (Kk ⟨[s1, s2, s2], [a1, b, a2]⟩) (SBgue (d.L n) a b) (hFBM3 s1 s2 s2 a1 b a2)
      (hK3b u hu s1 s2 s2 a1 b a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s2 s2 a1 b a2)
      (fun ω => hTb s1 s2 s2 a1 b a2 ω)
    refine (norm_add_le _ _).trans ?_
    linarith
  -- assembly
  have hR1b : ‖R1‖ ≤ 10000 * N ^ 4 * (1 + N) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by
    refine hR1.trans ?_
    have hlen : J.length = 2 := rfl
    rw [hlen, htime]
    have hu2 : u + Δ ∈ Set.Icc (t1 n) (t0 n) := hu'
    have hηk1 : (etaT (E n) (u + Δ))⁻¹ ≤ N := by
      have := hηM _ hu2
      rwa [eq729_zt_im, abs_of_pos (eq729_eta_pos hE (lt_of_le_of_lt hu2.2 ht0))] at this
    have hpos : 0 ≤ (etaT (E n) (u + Δ))⁻¹ :=
      (inv_pos.2 (eq729_eta_pos hE (lt_of_le_of_lt hu2.2 ht0))).le
    have hΔr : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have h6 : (1 + (etaT (E n) (u + Δ))⁻¹) ^ (2 + 4) ≤ (1 + N) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hEnv : envConst (d.L n) (d.W n) (E n) 2 (u + Δ)
        = 10000 * N ^ 4 * (1 + (etaT (E n) (u + Δ))⁻¹) ^ (2 + 4) := by
      have hNeq : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = N := rfl
      unfold envConst
      rw [hNeq]
      norm_num
    rw [hEnv]
    gcongr
  have hR2b : ‖R2‖ ≤ 3 * N ^ 2 * Δ ^ 2 := hR2
  rw [hident]
  have hQn : ‖(Δ : ℂ) * IQ‖
      ≤ Δ * (N * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * N ^ 2) * (2 * N ^ 2) * p)) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left hQ hΔ0
  have hGn : ‖(Δ : ℂ) * IeG‖ ≤ Δ * (N * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * N) * (2 * N ^ 3) * p)))) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left heG hΔ0
  have htri : ‖(e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2‖
      ≤ ‖e J + (Δ : ℂ) * lin‖ + ‖(Δ : ℂ) * IQ‖ + ‖(Δ : ℂ) * IeG‖ + ‖R1‖ + ‖R2‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  refine htri.trans ?_
  unfold eq729c
  linarith

end OneStep

end RBM.Univ.GUEPhase

end
