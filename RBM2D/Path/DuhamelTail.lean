/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Expansion
import RBM2D.Path.Azuma
import RBM2D.Path.Kernel
import RBM2D.Path.Stop
import RBM2D.Path.UBounds
import RBM2D.Path.StepDecompLoop

/-!
# Tail bounds for the stopped Duhamel martingale (`d = 2`)

Paper: arXiv:2503.07606, (108) = `alu9_STime`, with the BDG inequality replaced by
Azuma-Hoeffding.

The kernel is the two-index `Uop L ξ` on `Z2 L × Z2 L` with a single `ξ : ℂ` and real times;
the back-kernel constant is `4` (`uopBack`), and the label count is `L ^ 4`.

## Main declarations

* `stoppedEdge`, the stopped kernel image of an increment at one label;
* `stopped_duhamel_azuma_tail_fixed`, the label-weighted Azuma tail for a fixed target grid
  index `k` and label `a`;
* `stopped_duhamel_azuma_union`, the union over `1 ≤ k ≤ K` and all labels;
* `stopped_duhamel_cheb_tail`, the Chebyshev tail through the backward kernel.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. Generic algebra of the kernel `Uop` -/

section Setup

/-- Prepend a dummy zero term to a family `f : ℕ → M`. -/
private def DuhamelTail_prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

private theorem DuhamelTail_sum_range_succ_prependZero {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), DuhamelTail_prependZero f i = ∑ j ∈ Finset.range K, f j := by
  rw [Finset.sum_range_succ' (DuhamelTail_prependZero f) K]
  simp [DuhamelTail_prependZero]

/-- A finite sum of `MemLp _ 2 μ` real-valued functions is `MemLp _ 2 μ`. -/
private theorem DuhamelTail_memLp_finset_sum {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} {s : Finset ι} (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) : MemLp (fun x => ∑ i ∈ s, f i x) 2 μ := by
  have h := Finset.sum_induction f (fun g : α → ℝ => MemLp g 2 μ)
    (fun _ _ ha hb => ha.add hb) (memLp_const (0 : ℝ)) hf
  have heq : (∑ x ∈ s, f x) = fun x => ∑ i ∈ s, f i x := by
    funext x; rw [Finset.sum_apply]
  rwa [← heq]

/-- `‖(r : ℂ) * ζ‖ < 1` once `0 ≤ r ≤ t < 1` and `‖ζ‖ ≤ 1`. -/
private theorem DuhamelTail_norm_real_mul_lt_one {r t' : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t')
    (ht1 : t' < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : ‖(r : ℂ) * ζ‖ < 1 := by
  have heq : ‖(r : ℂ) * ζ‖ = r * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  rw [heq]
  calc r * ‖ζ‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hζ hr0
    _ = r := mul_one r
    _ ≤ t' := hrt
    _ < 1 := ht1

/-- The backward factorisation: for any real `s` and `0 ≤ r ≤ t < 1`,
`𝒰_{s,r} = 𝒰_{t,r} ∘ 𝒰_{s,t}` (from `Uop_comp`). -/
private theorem DuhamelTail_back_factor_apply (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {s t r : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (A : Z2 L × Z2 L → ℂ) :
    Uop L ξ s r A = Uop L ξ t r (Uop L ξ s t A) := by
  have ht' : ‖(t : ℂ) * ξ‖ < 1 := DuhamelTail_norm_real_mul_lt_one ht0 le_rfl ht1 hξ
  have hr' : ‖(r : ℂ) * ξ‖ < 1 := DuhamelTail_norm_real_mul_lt_one hr0 hrt ht1 hξ
  exact (Uop_comp L hL ht' hr' A).symm

/-- The backward factorisation applied to a finite sum: for `0 ≤ u 0 ≤ u 1 ≤ …`, `u K = t < 1`,
`k ≤ K` and any family `F`,
`Σ_{j<k} 𝒰_{u_{j+1},u_k} (F j) = 𝒰_{t,u_k} (Σ_{j<k} 𝒰_{u_{j+1},t} (F j))`. -/
private theorem DuhamelTail_back_factor_sum_apply (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {k : ℕ} (hkK : k ≤ K)
    (F : ℕ → Z2 L × Z2 L → ℂ) (a : Z2 L × Z2 L) :
    (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) (u k) (F j)) a
      = Uop L ξ t (u k) (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) t (F j)) a := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have h0t : 0 ≤ t := hut ▸ h0m K
  have hle_t : ∀ m, m ≤ K → u m ≤ t := fun m hm => hut ▸ hmono hm
  have hstep : ∀ j < k, Uop L ξ (u (j + 1)) (u k) (F j)
      = Uop L ξ t (u k) (Uop L ξ (u (j + 1)) t (F j)) :=
    fun j _ => DuhamelTail_back_factor_apply L hL hξ h0t ht1 (h0m k) (hle_t k hkK) (F j)
  have hsum_eq : (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) (u k) (F j))
      = Uop L ξ t (u k) (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) t (F j)) := by
    calc (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) (u k) (F j))
        = ∑ j ∈ Finset.range k, Uop L ξ t (u k) (Uop L ξ (u (j + 1)) t (F j)) :=
          Finset.sum_congr rfl (fun j hj => hstep j (Finset.mem_range.mp hj))
      _ = ∑ j ∈ Finset.range k, UopHom L ξ t (u k) (Uop L ξ (u (j + 1)) t (F j)) := by
          simp [UopHom_apply]
      _ = UopHom L ξ t (u k) (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) t (F j)) :=
          (map_sum (UopHom L ξ t (u k)) _ _).symm
      _ = Uop L ξ t (u k) (∑ j ∈ Finset.range k, Uop L ξ (u (j + 1)) t (F j)) := by
          rw [UopHom_apply]
  exact congrFun hsum_eq a

/-- Given the back-kernel bound `‖𝒰_{t,r} V a‖ ≤ 4 ‖V‖_max` (`uopBack`) and a label `a`
where the threshold `4 x` is met, some label `b` meets the threshold `x` for `V`. -/
private theorem DuhamelTail_exists_label_of_back_bound (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {t r : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t) (ht1 : t < 1)
    (V : Z2 L × Z2 L → ℂ) {x : ℝ} {a : Z2 L × Z2 L}
    (ha : 4 * x ≤ ‖Uop L ξ t r V a‖) :
    ∃ b, x ≤ ‖V b‖ := by
  have : Nonempty (Z2 L × Z2 L) := ⟨((0 : ZMod L), (0 : ZMod L)), ((0 : ZMod L), (0 : ZMod L))⟩
  have hA : ∀ b, ‖V b‖ ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    fun b => Finset.le_sup' (fun b => ‖V b‖) (Finset.mem_univ b)
  have hbound : ‖Uop L ξ t r V a‖
      ≤ 4 * Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    uopBack L hL ξ hξ r t hr0 hrt ht1 V _ hA a
  have hxM : x ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) := by
    linarith [ha, hbound]
  obtain ⟨b, -, hb⟩ := (Finset.le_sup'_iff (H := Finset.univ_nonempty)).mp hxM
  exact ⟨b, hb⟩

/-- The number of labels is `L ^ 4` (`n = 2` slots of two indices each). -/
private theorem DuhamelTail_card_label (L : ℕ) [NeZero L] :
    Fintype.card (Z2 L × Z2 L) = L ^ 4 := by
  rw [Fintype.card_prod, Fintype.card_prod, ZMod.card]
  ring

end Setup

/-! ### 2. The stopped edge -/

section StoppedEdge

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ℱ : Filtration ℕ mΩ'}

/-- The stopped, evaluated-at-one-label kernel image of an increment,
`{j < τ}.indicator (fun ω' => (𝒰_{u_{j+1},t'} Z_{j+1} ω') b)`, with target time `t'`
(`t' = u k` for the fixed-target tails, `t' = t = u K` for the Chebyshev tail). -/
noncomputable def stoppedEdge (L : ℕ) [NeZero L] (ξ : ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → Z2 L × Z2 L → ℂ) (b : Z2 L × Z2 L) (j : ℕ) :
    Ω' → ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => Uop L ξ (u (j + 1)) t' (Z (j + 1) ω') b)

/-- `A ↦ (𝒰_{s,t} A) b` is continuous, so it preserves strong measurability. -/
private theorem DuhamelTail_stronglyMeasurable_Uop_apply (L : ℕ) [NeZero L] (ξ : ℂ) (s t : ℝ)
    {i : ℕ} {W : Ω' → Z2 L × Z2 L → ℂ} (hW : StronglyMeasurable[ℱ i] W) (b : Z2 L × Z2 L) :
    StronglyMeasurable[ℱ i] (fun ω => Uop L ξ s t (W ω) b) := by
  have hcont : Continuous (fun A : Z2 L × Z2 L → ℂ => Uop L ξ s t A b) := by
    have heq : (fun A : Z2 L × Z2 L → ℂ => Uop L ξ s t A b)
        = fun A => ∑ c : Z2 L × Z2 L,
            (ukerMat L ξ s t b.1 c.1 * ukerMat L ξ s t b.2 c.2) * A c := by
      funext A; rfl
    rw [heq]
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `stoppedEdge` is `ℱ (j+1)`-strongly measurable once `Z (j+1)` is. -/
private theorem DuhamelTail_stronglyMeasurable_stoppedEdge (L : ℕ) [NeZero L] (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Z2 L × Z2 L) :
    StronglyMeasurable[ℱ (j + 1)] (stoppedEdge L ξ u t' τ Z b j) := by
  have hset : MeasurableSet[ℱ (j + 1)] {ω | j < τ ω} := (ℱ.mono (Nat.le_succ j)) _ (hτmeas j)
  have hW : StronglyMeasurable[ℱ (j + 1)]
      (fun ω => Uop L ξ (u (j + 1)) t' (Z (j + 1) ω) b) :=
    DuhamelTail_stronglyMeasurable_Uop_apply L ξ _ _ hZ b
  exact hW.indicator hset

private theorem DuhamelTail_stronglyMeasurable_stoppedEdge_re (L : ℕ) [NeZero L] (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Z2 L × Z2 L) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).re) :=
  Complex.continuous_re.comp_stronglyMeasurable
    (DuhamelTail_stronglyMeasurable_stoppedEdge L ξ u t' hZ hτmeas b)

private theorem DuhamelTail_stronglyMeasurable_stoppedEdge_im (L : ℕ) [NeZero L] (ξ : ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} {j : ℕ}
    (hZ : StronglyMeasurable[ℱ (j + 1)] (Z (j + 1)))
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) (b : Z2 L × Z2 L) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).im) :=
  Complex.continuous_im.comp_stronglyMeasurable
    (DuhamelTail_stronglyMeasurable_stoppedEdge L ξ u t' hZ hτmeas b)

/-- `sum_stopped` at one label: the sum up to `min k (τ ω)` is the `k`-horizon sum of
`stoppedEdge`. -/
private theorem DuhamelTail_stopped_sum_apply_eq (L : ℕ) [NeZero L] (ξ : ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → Z2 L × Z2 L → ℂ) (k : ℕ) (ω : Ω')
    (b : Z2 L × Z2 L) :
    (∑ j ∈ Finset.range (min k (τ ω)), Uop L ξ (u (j + 1)) t' (Z (j + 1) ω)) b
      = ∑ j ∈ Finset.range k, stoppedEdge L ξ u t' τ Z b j ω := by
  rw [Finset.sum_apply]
  exact sum_stopped (Ω' := Ω') (M := ℂ)
    (fun j ω => Uop L ξ (u j) t' (Z j ω) b) τ k ω

/-- The `τ ≤ K` form of `DuhamelTail_stopped_sum_apply_eq`. -/
private theorem DuhamelTail_inner_sum_apply_eq (L : ℕ) [NeZero L] (ξ : ℂ) (u : ℕ → ℝ) (t : ℝ)
    {K : ℕ} {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K) (Z : ℕ → Ω' → Z2 L × Z2 L → ℂ) (ω : Ω')
    (b : Z2 L × Z2 L) :
    (∑ j ∈ Finset.range (τ ω), Uop L ξ (u (j + 1)) t (Z (j + 1) ω)) b
      = ∑ j ∈ Finset.range K, stoppedEdge L ξ u t τ Z b j ω := by
  have h := DuhamelTail_stopped_sum_apply_eq L ξ u t τ Z K ω b
  rwa [min_eq_right (hτK ω)] at h

end StoppedEdge

/-! ### 3. The Azuma tails -/

section Azuma

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- The common Azuma step: for a fixed label `b`, target time `t'` and horizon `k`, conditional
sub-Gaussian stopped increments give the complex Azuma tail for their `k`-horizon sum.  The
measurability hypothesis is only needed for `i ≤ k`; the process is truncated to `0` beyond `k`
to feed `azuma_complex`, which asks for adaptedness at every index. -/
private theorem DuhamelTail_azuma_stoppedEdge (L : ℕ) [NeZero L] (ξ : ℂ) (u : ℕ → ℝ) (t' : ℝ)
    {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} {k : ℕ}
    (hZ : ∀ i ≤ k, StronglyMeasurable[ℱ i] (Z i))
    (b : Z2 L × Z2 L) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge L ξ u t' τ Z b j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := fun i =>
    if i ≤ k then DuhamelTail_prependZero (fun j => stoppedEdge L ξ u t' τ Z b j) i
    else 0 with hYdef
  set cc : ℕ → ℝ≥0 := DuhamelTail_prependZero c with hccdef
  have hYsucc : ∀ j, j + 1 ≤ k → Y (j + 1) = stoppedEdge L ξ u t' τ Z b j := by
    intro j hj
    simp only [hYdef, hj, ↓reduceIte, DuhamelTail_prependZero]
  have hYzero : Y 0 = 0 := by
    simp [hYdef, DuhamelTail_prependZero]
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ k
      · have := DuhamelTail_stronglyMeasurable_stoppedEdge_re L ξ u t' (hZ (j + 1) hj) hτmeas b
        simpa [hYsucc j hj] using this
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ k
      · have := DuhamelTail_stronglyMeasurable_stoppedEdge_im L ξ u t' (hZ (j + 1) hj) hτmeas b
        simpa [hYsucc j hj] using this
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYzero, hccdef, DuhamelTail_prependZero]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYzero, hccdef, DuhamelTail_prependZero]
  have hCR : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    have h1 := (hsubG i hi).1
    rw [hYsucc i hi]
    simpa [hccdef, DuhamelTail_prependZero] using h1
  have hCI : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    have h1 := (hsubG i hi).2
    rw [hYsucc i hi]
    simpa [hccdef, DuhamelTail_prependZero] using h1
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (k + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ Finset.range k, stoppedEdge L ξ u t' τ Z b j ω
      = ∑ i ∈ Finset.range (k + 1), Y i ω := by
    intro ω
    have h3 := congrFun
      (DuhamelTail_sum_range_succ_prependZero (fun j => stoppedEdge L ξ u t' τ Z b j) k) ω
    simp only [Finset.sum_apply] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hYdef, hik, ↓reduceIte]
  have hsumeq : ∑ i ∈ Finset.range (k + 1), (cc i : ℝ) = ∑ j ∈ Finset.range k, (c j : ℝ) := by
    have := DuhamelTail_sum_range_succ_prependZero (M := ℝ≥0) c k
    have hcast : ((∑ i ∈ Finset.range (k + 1), DuhamelTail_prependZero c i : ℝ≥0) : ℝ)
        = ((∑ j ∈ Finset.range k, c j : ℝ≥0) : ℝ) := by exact_mod_cast this
    simpa [hccdef] using hcast
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge L ξ u t' τ Z b j ω‖}
      = {ω | x ≤ ‖∑ i ∈ Finset.range (k + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

/-- **`stopped_duhamel_azuma_tail_fixed`**: the label-weighted Azuma tail for a fixed target
grid index `k` and a fixed label `a`, with deterministic constants `c k a j`.
Proof: `sum_stopped` rewrites `(Σ_{j<min k τ} 𝒰_{u_{j+1},u_k} Z_{j+1}) a` as
`Σ_{j<k} {j<τ}·(𝒰_{u_{j+1},u_k} Z_{j+1}) a`, and `azuma_complex` is applied to that sum.

No hypothesis on `u`, `ξ` or `k` is needed: `Uop` is a total function of its real times.  The
measurability hypothesis is `∀ i ≤ k`. -/
theorem stopped_duhamel_azuma_tail_fixed (L : ℕ) [NeZero L] {ξ : ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} (k : ℕ) (hZ : ∀ i ≤ k, StronglyMeasurable[ℱ i] (Z i))
    (a : Z2 L × Z2 L) {c : ℕ → Z2 L × Z2 L → ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
  have hset : {ω | x ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range k, stoppedEdge L ξ u (u k) τ Z a j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      DuhamelTail_stopped_sum_apply_eq L ξ u (u k) τ Z k ω a]
  rw [hset]
  exact DuhamelTail_azuma_stoppedEdge L ξ u (u k) hτmeas hZ a (c := c k a) hsubG hx

/-- **`stopped_duhamel_azuma_union`**: the union of the events of
`stopped_duhamel_azuma_tail_fixed` over all target grid indices `k ≤ K` and all labels `a`,
with a threshold `x k a` for each `(k, a)`.  On `{τ = k}` the `k`-th sum is the linear term of
the stopped Duhamel expansion at `u_τ`.

**The `k = 0` summand.**  For `k = 0` the inner constant sum is empty, so under Lean's `a / 0 = 0`
that summand would equal `4 * exp 0 = 4`, and the form summed over `k ≤ K` would be trivially
true.  In the paper's convention the `k = 0` summand is `0` (for `x 0 a > 0`), and the `k = 0`
event `{x 0 a ≤ ‖0‖}` is empty.  So the event is over all `k ≤ K`, `hx0 : ∀ a, 0 < x 0 a` is
assumed, and the right-hand side is summed over `k ∈ Icc 1 K` only.  This right-hand side is at
most the literal one, so this statement implies the literal form.  The measurability hypothesis is
`∀ i ≤ K`. -/
theorem stopped_duhamel_azuma_union (L : ℕ) [NeZero L] {ξ : ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → Z2 L × Z2 L → ℂ} (K : ℕ) (hZ : ∀ i ≤ K, StronglyMeasurable[ℱ i] (Z i))
    {c : ℕ → Z2 L × Z2 L → ℕ → ℝ≥0}
    (hsubG : ∀ k ≤ K, ∀ a : Z2 L × Z2 L, ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℕ → Z2 L × Z2 L → ℝ} (hx : ∀ k ≤ K, ∀ a, 0 ≤ x k a) (hx0 : ∀ a, 0 < x 0 a) :
    μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ a : Z2 L × Z2 L,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
  set E : ℕ → Z2 L × Z2 L → Set Ω' := fun k a => {ω | x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖} with hEdef
  have hincl : {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      ⊆ ⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a := by
    rintro ω ⟨k, hk, a, ha⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have h0 : (∑ j ∈ Finset.range (min 0 (τ ω)),
          Uop L ξ (u (j + 1)) (u 0) (Z (j + 1) ω)) a = 0 := by simp
      rw [h0, norm_zero] at ha
      exact absurd ha (not_le.mpr (hx0 a))
    · simp only [Set.mem_iUnion]
      exact ⟨k, Finset.mem_Icc.mpr ⟨hkpos, hk⟩, a, ha⟩
  calc μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Uop L ξ (u (j + 1)) (u k) (Z (j + 1) ω)) a‖}
      ≤ μ.real (⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.Icc 1 K, μ.real (⋃ a, E k a) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : Z2 L × Z2 L, μ.real (E k a) :=
        Finset.sum_le_sum fun k _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : Z2 L × Z2 L,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ Finset.range k, (c k a j : ℝ))) := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => ?_
        have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
        exact stopped_duhamel_azuma_tail_fixed L hτmeas k (fun i hi => hZ i (hi.trans hkK)) a
          (hsubG k hkK a) (hx k hkK a)

end Azuma

/-! ### 4. The Chebyshev tail -/

section Cheb

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

/-- **`stopped_duhamel_cheb_tail`**: the discrete Chebyshev tail bound for the stopped Duhamel
martingale-difference remainder (sup-norm, via the backward kernel).  Proof: backward
factorisation (`Uop_comp`, `uopBack` with constant `4`), then per label the real/imaginary
partial sums are martingales (`martingale_of_condExp_sub_eq_zero_nat`), `martingale_sq_eq_sum`,
and Markov's inequality.  The number of labels is `L ^ 4`.  `0 < x` is needed: at `x = 0` the
right side is `0` under `a / 0 = 0`.  The measurability hypothesis is `∀ i ≤ K`. -/
theorem stopped_duhamel_cheb_tail (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) {Y : ℕ → Ω' → Z2 L × Z2 L → ℂ}
    (hY : ∀ i ≤ K, StronglyMeasurable[ℱ i] (Y i)) {e : ℕ → ℝ}
    (hYmeanRe : ∀ b : Z2 L × Z2 L, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re | ℱ j] =ᵐ[μ] 0)
    (hYmeanIm : ∀ b : Z2 L × Z2 L, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im | ℱ j] =ᵐ[μ] 0)
    (hYmemLpRe : ∀ b : Z2 L × Z2 L, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re) 2 μ)
    (hYmemLpIm : ∀ b : Z2 L × Z2 L, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im) 2 μ)
    (hYbound : ∀ b : Z2 L × Z2 L, ∀ j < K,
      ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).re ^ 2 ∂μ
        + ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uop L ξ (u (j + 1)) t (Y (j + 1) ω') b) ω).im ^ 2 ∂μ ≤ e j)
    {x : ℝ} (hx : 0 < x) :
    μ.real {ω | ∃ a, 4 * x ≤
        ‖(∑ j ∈ Finset.range (τ ω), Uop L ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖} ≤
      (L : ℝ) ^ 4 * (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
  set vector : Ω' → Z2 L × Z2 L → ℂ :=
    fun ω => ∑ j ∈ Finset.range (τ ω), Uop L ξ (u (j + 1)) t (Y (j + 1) ω) with hvecdef
  have hincl : {ω | ∃ a, 4 * x ≤
      ‖(∑ j ∈ Finset.range (τ ω), Uop L ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖}
      ⊆ ⋃ b : Z2 L × Z2 L, {ω | x ≤ ‖vector ω b‖} := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    have hfact := DuhamelTail_back_factor_sum_apply L hL hξ hu0 hu_succ hut ht1 (hτK ω)
      (fun j => Y (j + 1) ω) a
    rw [hfact] at ha
    have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
    have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
    have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
    obtain ⟨b, hb⟩ := DuhamelTail_exists_label_of_back_bound L hL hξ (h0m (τ ω)) hle_t ht1
      (vector ω) ha
    exact Set.mem_iUnion.mpr ⟨b, hb⟩
  calc μ.real {ω | ∃ a, 4 * x ≤
        ‖(∑ j ∈ Finset.range (τ ω), Uop L ξ (u (j + 1)) (u (τ ω)) (Y (j + 1) ω)) a‖}
      ≤ μ.real (⋃ b : Z2 L × Z2 L, {ω | x ≤ ‖vector ω b‖}) := measureReal_mono hincl
    _ ≤ ∑ b : Z2 L × Z2 L, μ.real {ω | x ≤ ‖vector ω b‖} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _b : Z2 L × Z2 L, (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        set W : ℕ → Ω' → ℂ := stoppedEdge L ξ u t τ Y b with hWdef
        set Mre : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ Finset.range (min i K), (W j ω).re
          with hMredef
        set Mim : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ Finset.range (min i K), (W j ω).im
          with hMimdef
        have hWadaptRe : ∀ j, j + 1 ≤ K → StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).re) :=
          fun j hj => DuhamelTail_stronglyMeasurable_stoppedEdge_re L ξ u t (hY (j + 1) hj)
            hτmeas b
        have hWadaptIm : ∀ j, j + 1 ≤ K → StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).im) :=
          fun j hj => DuhamelTail_stronglyMeasurable_stoppedEdge_im L ξ u t (hY (j + 1) hj)
            hτmeas b
        have hadpRe : StronglyAdapted ℱ Mre := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (Finset.range (min i K))
            (fun j hj => ?_)
          have hj' : j + 1 ≤ min i K := by
            simp only [Finset.mem_range] at hj
            omega
          exact (hWadaptRe j (hj'.trans (min_le_right i K))).mono
            (ℱ.mono (hj'.trans (min_le_left i K)))
        have hadpIm : StronglyAdapted ℱ Mim := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (Finset.range (min i K))
            (fun j hj => ?_)
          have hj' : j + 1 ≤ min i K := by
            simp only [Finset.mem_range] at hj
            omega
          exact (hWadaptIm j (hj'.trans (min_le_right i K))).mono
            (ℱ.mono (hj'.trans (min_le_left i K)))
        have hMemLpRe : ∀ i, MemLp (Mre i) 2 μ := fun i =>
          DuhamelTail_memLp_finset_sum (fun j ω => (W j ω).re)
            (fun j hj => hYmemLpRe b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hMemLpIm : ∀ i, MemLp (Mim i) 2 μ := fun i =>
          DuhamelTail_memLp_finset_sum (fun j ω => (W j ω).im)
            (fun j hj => hYmemLpIm b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hintRe : ∀ i, Integrable (Mre i) μ := fun i => (hMemLpRe i).integrable (by norm_num)
        have hintIm : ∀ i, Integrable (Mim i) μ := fun i => (hMemLpIm i).integrable (by norm_num)
        have hM0Re : Mre 0 = 0 := by funext ω; simp [hMredef]
        have hM0Im : Mim 0 = 0 := by funext ω; simp [hMimdef]
        have hstepRe : ∀ i, μ[Mre (i + 1) - Mre i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mre (i + 1) - Mre i = fun ω => (W i ω).re := by
              funext ω
              simp only [hMredef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanRe b i hiK
          · have heq : Mre (i + 1) - Mre i = 0 := by
              funext ω
              simp only [hMredef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hstepIm : ∀ i, μ[Mim (i + 1) - Mim i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mim (i + 1) - Mim i = fun ω => (W i ω).im := by
              funext ω
              simp only [hMimdef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanIm b i hiK
          · have heq : Mim (i + 1) - Mim i = 0 := by
              funext ω
              simp only [hMimdef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hMartRe : Martingale Mre ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpRe hintRe hstepRe
        have hMartIm : Martingale Mim ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpIm hintIm hstepIm
        have hsqRe := martingale_sq_eq_sum hMartRe hM0Re hMemLpRe K
        have hsqIm := martingale_sq_eq_sum hMartIm hM0Im hMemLpIm K
        have hMreK : Mre K = fun ω => ∑ j ∈ Finset.range K, (W j ω).re := by
          simp [hMredef, min_self]
        have hMimK : Mim K = fun ω => ∑ j ∈ Finset.range K, (W j ω).im := by
          simp [hMimdef, min_self]
        have hΔRe : ∀ j < K, ∀ ω, Mre (j + 1) ω - Mre j ω = (W j ω).re := by
          intro j hj ω
          simp only [hMredef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hΔIm : ∀ j < K, ∀ ω, Mim (j + 1) ω - Mim j ω = (W j ω).im := by
          intro j hj ω
          simp only [hMimdef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hsumRe : ∫ ω, (Mre K ω) ^ 2 ∂μ = ∑ j ∈ Finset.range K, ∫ ω, (W j ω).re ^ 2 ∂μ := by
          rw [hsqRe]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔRe j (Finset.mem_range.mp hj) ω]
        have hsumIm : ∫ ω, (Mim K ω) ^ 2 ∂μ = ∑ j ∈ Finset.range K, ∫ ω, (W j ω).im ^ 2 ∂μ := by
          rw [hsqIm]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔIm j (Finset.mem_range.mp hj) ω]
        have hboundtot :
            ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ ≤ ∑ j ∈ Finset.range K, e j := by
          rw [hsumRe, hsumIm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun j hj => hYbound b j (Finset.mem_range.mp hj))
        have hveceq : ∀ ω, ‖vector ω b‖ ^ 2 = (Mre K ω) ^ 2 + (Mim K ω) ^ 2 := by
          intro ω
          have hv : vector ω b = ∑ j ∈ Finset.range K, W j ω := by
            rw [hvecdef]; exact DuhamelTail_inner_sum_apply_eq L ξ u t hτK Y ω b
          have hre : (vector ω b).re = Mre K ω := by rw [hv, hMreK]; simp [Complex.re_sum]
          have him : (vector ω b).im = Mim K ω := by rw [hv, hMimK]; simp [Complex.im_sum]
          have hns : ‖vector ω b‖ ^ 2 = (vector ω b).re ^ 2 + (vector ω b).im ^ 2 := by
            rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
          rw [hns, hre, him]
        have hintf : Integrable (fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2) μ :=
          ((hMemLpRe K).integrable_sq).add ((hMemLpIm K).integrable_sq)
        have hnn : 0 ≤ᵐ[μ] fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2 :=
          ae_of_all _ fun ω => by positivity
        have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn hintf (x ^ 2)
        have hsetEq :
            {ω | x ≤ ‖vector ω b‖} = {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by
          ext ω
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hveceq ω]
          constructor
          · intro h; exact pow_le_pow_left₀ hx.le h 2
          · intro h
            exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) two_ne_zero).mp h
        rw [hsetEq]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2)]
        calc μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} * x ^ 2
            = x ^ 2 * μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by ring
          _ ≤ ∫ ω, (Mre K ω) ^ 2 + (Mim K ω) ^ 2 ∂μ := hmarkov
          _ = ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ :=
            integral_add (hMemLpRe K).integrable_sq (hMemLpIm K).integrable_sq
          _ ≤ ∑ j ∈ Finset.range K, e j := hboundtot
    _ = (L : ℝ) ^ 4 * (∑ j ∈ Finset.range K, e j) / x ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, DuhamelTail_card_label, nsmul_eq_mul]
        push_cast
        ring

end Cheb

end RBM.Path
