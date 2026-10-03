/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Ward
import RBM2D.Loop.SumZero

/-!
# `lem_sumAinK`, `(sumallAinK)` with an explicit constant

The theorem `Kcal_sumAll_le`, from `lem_sumAinK` and `(sumallAinK)` of the paper.

Method.  Total sums `T_n(σ) = ∑_a 𝒦_{t,σ,a}`.
* translation (`Kcal_translate`) gives `T_n(σ) = L² ∑_{a : a₁ fixed} 𝒦`;
* rotation (`Kcal_rotate`) gives `T_n(σ) = T_n(σ ∘ (· + j))`;
* pure `σ`: `n = 1`, `n = 2` (`Kcal_two`, `sum_Theta_row`) and `n ≥ 3` (`Kcal_eq_sum_Kpi`,
  `sum_Kpi_closed`) are bounded directly;
* non-pure `σ`: rotate to `σ₁ = +`, `σₙ = −` and apply `Kcal_ward`, by induction on `n`
  with the claim for all sign vectors.

In contrast to the one-dimensional argument, the
pure loops are computed exactly in `d = 2` (`sum_Kpi_closed`), and the induction runs over
all sign vectors.  The private helpers of `SumZero.lean` (`norm_mSig'`, `norm_xi'`, `gapK_pos`,
`gapK_le_one`, `gapK_sq_le`, `norm_one_sub_sq`, `gapK_le_norm`, `norm_edge_le`,
`card_le_of_mem_TSP` with its `goodPt` chain, `card_TSPlong_le`) are re-proved here with the
prefix `SumAll_`.  All helpers are `private`.
-/

namespace RBM.KLoop

open Finset

/-! ## 1. Private helpers (as in `SumZero.lean`) -/

section Helpers

variable {n : ℕ}


private theorem SumAll_isDiag_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : IsDiag n d.1 d.2 := by
  have h1 := mem_powerset.1 (mem_filter.1 hF).1 hd
  simpa [diagonals] using h1


private theorem SumAll_crossingFree_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    CrossingFree F :=
  (mem_filter.1 hF).2


/-- `‖m(s)‖ = 1` in the bulk. -/
private theorem SumAll_norm_mSig' {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖t m(s) m(s')‖ = t` for `t ≥ 0`. -/
private theorem SumAll_norm_xi' {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (mSig E s * mSig E s')‖ = t := by
  rw [norm_mul, norm_mul, SumAll_norm_mSig' hE, SumAll_norm_mSig' hE, Complex.norm_real,
    Real.norm_of_nonneg ht, mul_one, mul_one]

private theorem SumAll_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem SumAll_gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem SumAll_gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ gapK κ := (SumAll_gapK_pos hκ hκ2).le
  have h1 : gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem SumAll_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 =
      (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him := Gauss.spectralM_im E
  have hs := Gauss.spectralM_sqrt_sq hE
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- **The bulk gap**: `c_κ ≤ |1 - t m(s)²|` for `t ≥ 0` (in particular `t ∈ [0,1]`)
and `|E| ≤ 2 - κ`. -/
private theorem SumAll_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (s : Bool) :
    gapK κ ≤ ‖1 - (t : ℂ) * (mSig E s * mSig E s)‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 := by
    rw [SumAll_norm_one_sub_sq hE2]
    have hg1 : gapK κ ^ 2 ≤ 1 := by
      have := SumAll_gapK_le_one κ
      have := (SumAll_gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := SumAll_gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have hle : gapK κ ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ := by
    have := (SumAll_gapK_pos hκ hκ2).le
    have := norm_nonneg (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E))
    nlinarith
  cases s
  · have hc : (1 : ℂ) - (t : ℂ) * (mSig E false * mSig E false) =
        (starRingEnd ℂ) (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)) := by
      simp [mSig, map_sub, map_mul, Complex.conj_ofReal]
    rw [hc, Complex.norm_conj]
    exact hle
  · simpa [mSig] using hle

/-- The factor `f(t) = (1 - tμ)⁻¹ - 1` is bounded by `c⁻¹`. -/
private theorem SumAll_norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
    ‖(1 - (t : ℂ) * μ)⁻¹ - 1‖ ≤ c⁻¹ := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have h : (1 - (t : ℂ) * μ)⁻¹ - 1 = ((t : ℂ) * μ) * (1 - (t : ℂ) * μ)⁻¹ := by
    field_simp
    ring
  rw [h, norm_mul, norm_mul, hμ, Complex.norm_real, Real.norm_of_nonneg ht0, norm_inv, mul_one]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hc1 : 0 ≤ ‖1 - (t : ℂ) * μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  nlinarith [ht1]

/-- A vertex `v` strictly inside the arc of `d` and not strictly inside the arc of any other
diagonal of `F` below `d`. -/
private def SumAll_goodPt {n : ℕ} (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) (v : Fin n) :
    Prop :=
  d.1 < v ∧ v < d.2 ∧ ∀ e ∈ F, e ≠ d → ArcLe e d → ¬(e.1 < v ∧ v < e.2)

private theorem SumAll_exists_goodPt {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : ∃ v, SumAll_goodPt F d v := by
  have hdD := SumAll_isDiag_of_mem_TSP hF hd
  have hcf := SumAll_crossingFree_of_mem_TSP hF
  obtain ⟨hd12, hdadj, -⟩ := hdD
  rw [Fin.lt_def] at hd12
  set S := F.filter (fun e => e.1 = d.1 ∧ e.2 < d.2) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hlt : d.1.val + 1 < n := by have := d.2.isLt; omega
    refine ⟨⟨d.1.val + 1, hlt⟩, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; simp
    · rw [Fin.lt_def]; simp only; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      simp only at h1 h2
      have he1 : e.1 = d.1 := Fin.ext (by omega)
      have he2 : e.2 < d.2 := by
        rw [Fin.lt_def]
        rcases Nat.lt_or_ge e.2.val d.2.val with h | h
        · exact h
        · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
      have : e ∈ S := mem_filter.2 ⟨he, he1, he2⟩
      rw [hS] at this
      exact absurd this (notMem_empty e)
  · obtain ⟨e₀, he₀, hmax⟩ := S.exists_max_image (fun e => e.2.val) hS
    obtain ⟨he₀F, he₀1, he₀2⟩ := mem_filter.1 he₀
    have he₀D := (SumAll_isDiag_of_mem_TSP hF he₀F).1
    rw [Fin.lt_def] at he₀D he₀2
    have he₀1' : e₀.1.val = d.1.val := congrArg Fin.val he₀1
    refine ⟨e₀.2, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [Fin.lt_def]; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      rcases Nat.lt_or_ge d.1.val e.1.val with h | h
      · apply hcf e₀ he₀F e he
        left
        refine ⟨?_, ?_, ?_⟩ <;> rw [Fin.lt_def] <;> omega
      · have he1 : e.1 = d.1 := Fin.ext (by omega)
        have he2 : e.2 < d.2 := by
          rw [Fin.lt_def]
          rcases Nat.lt_or_ge e.2.val d.2.val with h' | h'
          · exact h'
          · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
        have : e.2.val ≤ e₀.2.val := hmax e (mem_filter.2 ⟨he, he1, he2⟩)
        omega

private theorem SumAll_goodPt_inj {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d d' : Fin n × Fin n} (hd : d ∈ F) (hd' : d' ∈ F) {v : Fin n}
    (hv : SumAll_goodPt F d v) (hv' : SumAll_goodPt F d' v) : d = d' := by
  by_contra hne
  have hcf := SumAll_crossingFree_of_mem_TSP hF
  obtain ⟨a1, a2, a3⟩ := hv
  obtain ⟨b1, b2, b3⟩ := hv'
  by_cases h1 : ArcLe d' d
  · exact a3 d' hd' (Ne.symm hne) h1 ⟨b1, b2⟩
  by_cases h2 : ArcLe d d'
  · exact b3 d hd hne h2 ⟨a1, a2⟩
  simp only [ArcLe, Fin.le_def, not_and_or, not_le] at h1 h2
  rw [Fin.lt_def] at a1 a2 b1 b2
  have hc1 := hcf d hd d' hd'
  have hc2 := hcf d' hd' d hd
  simp only [Crossing, Fin.lt_def, not_or, not_and_or, not_lt] at hc1 hc2
  omega

/-- A crossing-free set of diagonals of the `n`-gon has at most `n - 2` elements. -/
private theorem SumAll_card_le_of_mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    F.card ≤ n - 2 := by
  classical
  let g : Fin n × Fin n → Fin n := fun d =>
    if h : ∃ v, SumAll_goodPt F d v then Classical.choose h else d.1
  have hg : ∀ d ∈ F, SumAll_goodPt F d (g d) := by
    intro d hd
    have h := SumAll_exists_goodPt hF hd
    simp only [g, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hcard : (Finset.Ioo 0 (n - 1)).card = n - 2 := by
    rw [Nat.card_Ioo]; omega
  rw [← hcard]
  refine card_le_card_of_injOn (fun d => (g d).val) (fun d hd => ?_) (fun d hd d' hd' h => ?_)
  · obtain ⟨h1, h2, -⟩ := hg d hd
    rw [Fin.lt_def] at h1 h2
    have := d.2.isLt
    simp only [coe_Ioo, Set.mem_Ioo]
    omega
  · have hv : g d = g d' := Fin.ext h
    have g' := hg d' hd'
    rw [← hv] at g'
    exact SumAll_goodPt_inj hF hd hd' (hg d hd) g'

/-- The number of trees: `#T_SP(σ,π) ≤ #T_SP(n) ≤ 2^{n²}`. -/
private theorem SumAll_card_TSPlong_le (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    (TSPlong n σ π).card ≤ 2 ^ (n ^ 2) := by
  calc (TSPlong n σ π).card ≤ (TSP n).card := card_filter_le _ _
    _ ≤ (diagonals n).powerset.card := card_filter_le _ _
    _ = 2 ^ (diagonals n).card := card_powerset _
    _ ≤ 2 ^ (n ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
          _ = n ^ 2 := by simp [sq]

end Helpers


/-! ## 2. Scalar facts on `η_t` -/

section Scalars

private theorem SumAll_etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem SumAll_etaT_pos {E t : ℝ} (hE : |E| < 2) (ht : t < 1) : 0 < etaT E t := by
  rw [SumAll_etaT_eq]
  exact mul_pos (by linarith) (Gauss.spectralM_im_pos hE)

private theorem SumAll_etaT_le_one (E : ℝ) {t : ℝ} (ht0 : 0 ≤ t) : etaT E t ≤ 1 := by
  rw [SumAll_etaT_eq]
  have h0 : 0 ≤ (Gauss.spectralM E).im := by
    rw [Gauss.spectralM_im]; positivity
  have h1 : (Gauss.spectralM E).im ≤ 1 := by
    rw [Gauss.spectralM_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
    linarith
  nlinarith

end Scalars

/-! ## 3. Total sums, translation and rotation -/

section Total

variable {L : ℕ} [NeZero L]

/-- The total sum `T_n(σ) = ∑_a 𝒦_{t,σ,a}`. -/
private noncomputable def SumAll_T (L W : ℕ) [NeZero L] (E t : ℝ) {n : ℕ} (σ : Fin n → Bool) :
    ℂ :=
  ∑ a : Fin n → Z2 L, Kcal L W E t (loopOf L σ a)

/-- Splitting off the last coordinate. -/
private theorem SumAll_sum_snoc {α M : Type*} [Fintype α] [AddCommMonoid M] (m : ℕ)
    (f : (Fin (m + 1) → α) → M) :
    ∑ a, f a = ∑ a' : Fin m → α, ∑ x : α, f (Fin.snoc (α := fun _ => α) a' x) := by
  rw [← Fintype.sum_prod_type', ← (Fin.snocEquiv (fun _ : Fin (m + 1) => α)).sum_comp]
  rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
  rfl

private theorem SumAll_ofFn_rot {α : Type*} {k : ℕ} (f : Fin (k + 1) → α) :
    List.ofFn (fun i : Fin (k + 1) => f (i + 1))
      = List.ofFn (fun i : Fin k => f i.succ) ++ [f 0] := by
  rw [List.ofFn_succ']
  simp [Fin.coeSucc_eq_succ, Fin.last_add_one]

private theorem SumAll_T_rot (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool) :
    SumAll_T L W E t σ = SumAll_T L W E t (fun i => σ (i + 1)) := by
  unfold SumAll_T
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.subRight (1 : Fin (k + 1))) (Equiv.refl (Z2 L))) _ _ (fun a => ?_)
  have hea : (Equiv.arrowCongr (Equiv.subRight (1 : Fin (k + 1))) (Equiv.refl (Z2 L))) a
      = fun i => a (i + 1) := by
    funext i; simp [Equiv.arrowCongr]
  rw [hea]
  have h1 : loopOf L σ a = ⟨σ 0 :: List.ofFn (fun i : Fin k => σ i.succ),
      a 0 :: List.ofFn (fun i : Fin k => a i.succ)⟩ := by
    simp only [loopOf]; rw [List.ofFn_succ, List.ofFn_succ]
  have h2 : loopOf L (fun i => σ (i + 1)) (fun i => a (i + 1)) =
      ⟨List.ofFn (fun i : Fin k => σ i.succ) ++ [σ 0],
        List.ofFn (fun i : Fin k => a i.succ) ++ [a 0]⟩ := by
    simp only [loopOf]; rw [SumAll_ofFn_rot, SumAll_ofFn_rot]
  rw [h1, h2]
  exact Kcal_rotate L W hL hW E hE t ht (σ 0) (a 0) _ _ (by simp)

open Fin.NatCast in
private theorem SumAll_T_rot_iter (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool) (j : ℕ) :
    SumAll_T L W E t σ = SumAll_T L W E t (fun i => σ (i + (j : Fin (k + 1)))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, SumAll_T_rot hL hW hE ht]
    congr 1
    funext i
    congr 1
    push_cast
    rw [add_assoc, add_comm (1 : Fin (k + 1))]

open Fin.NatCast in
private theorem SumAll_exists_false_true {k : ℕ} (σ : Fin (k + 1) → Bool)
    (h : ¬ ∀ i, σ i = σ 0) : ∃ i, σ i = false ∧ σ (i + 1) = true := by
  by_contra hne0
  have hne : ∀ i, σ i = false → σ (i + 1) = false := fun i hi => by
    by_contra hc
    exact hne0 ⟨i, hi, by simpa using hc⟩
  obtain ⟨j0, hj0⟩ : ∃ j0, σ j0 = false := by
    obtain ⟨i, hi⟩ := not_forall.1 h
    cases h0 : σ 0
    · exact ⟨0, h0⟩
    · exact ⟨i, by simpa [h0] using hi⟩
  have hall : ∀ m : ℕ, σ (j0 + (m : Fin (k + 1))) = false := by
    intro m
    induction m with
    | zero => simpa using hj0
    | succ m ih =>
      have := hne _ ih
      simpa [Nat.cast_succ, ← add_assoc] using this
  have hall' : ∀ i, σ i = false := by
    intro i
    have := hall (i - j0).val
    simpa using this
  exact h fun i => by rw [hall' i, hall' 0]

private theorem SumAll_card_Z2 : Fintype.card (Z2 L) = L ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

/-- Translation invariance of the fibre sums (`Kcal_translate`). -/
private theorem SumAll_fiber_const (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool) (y y' : Z2 L) :
    ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Z2 L => a 0 = y), Kcal L W E t (loopOf L σ a)
      = ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Z2 L => a 0 = y'),
          Kcal L W E t (loopOf L σ a) := by
  refine Finset.sum_nbij' (fun a i => a i + (y' - y)) (fun a i => a i - (y' - y))
    (fun a ha => ?_) (fun a ha => ?_) (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_)
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [ha]; abel
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [ha]; abel
  · funext i; simp
  · funext i; simp
  · have h := Kcal_translate L W hL hW E hE t ht (y' - y) (loopOf L σ a)
      (by simp [LoopIdx.WF, loopOf])
    rw [← h]
    congr 1
    simp only [loopOf, List.map_ofFn]
    rfl

/-- `T_n(σ) = L² ∑_{a : a₀ = a₁} 𝒦_{t,σ,a}`. -/
private theorem SumAll_T_eq_fiber (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool) (a₁ : Z2 L) :
    SumAll_T L W E t σ = (L : ℂ) ^ 2 *
      ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Z2 L => a 0 = a₁), Kcal L W E t (loopOf L σ a) := by
  unfold SumAll_T
  rw [← Finset.sum_fiberwise univ (fun a : Fin (k + 1) → Z2 L => a 0)]
  rw [Finset.sum_congr rfl (fun y _ => SumAll_fiber_const hL hW hE ht σ y a₁)]
  rw [Finset.sum_const, Finset.card_univ, SumAll_card_Z2]
  simp

omit [NeZero L] in
/-- The list form of `loopOf σ (snoc a' x)` for `σ₀ = +`, `σ_{last} = −`. -/
private theorem SumAll_loopOf_snoc {k : ℕ} (σ : Fin (k + 2) → Bool) (h0 : σ 0 = true)
    (hl : σ (Fin.last (k + 1)) = false) (a' : Fin (k + 1) → Z2 L) (x : Z2 L) :
    loopOf L σ (Fin.snoc (α := fun _ => Z2 L) a' x) =
      ⟨true :: List.ofFn (fun i : Fin k => σ i.succ.castSucc) ++ [false],
        List.ofFn a' ++ [x]⟩ := by
  simp only [loopOf]
  rw [List.ofFn_succ' σ, List.ofFn_succ' (Fin.snoc (α := fun _ => Z2 L) a' x)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hl, List.concat_eq_append]
  rw [List.ofFn_succ (f := fun i : Fin (k + 1) => σ i.castSucc)]
  simp [h0]

omit [NeZero L] in
private theorem SumAll_loopOf_cons {k : ℕ} (σ : Fin (k + 2) → Bool) (b : Bool)
    (a' : Fin (k + 1) → Z2 L) :
    loopOf L (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 b) a' =
      ⟨b :: List.ofFn (fun i : Fin k => σ i.succ.castSucc), List.ofFn a'⟩ := by
  simp only [loopOf]
  rw [List.ofFn_succ]
  simp [Function.update_of_ne, Fin.succ_ne_zero]

/-- The Ward step on total sums (`Kcal_ward`). -/
private theorem SumAll_T_ward (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 2) → Bool) (h0 : σ 0 = true)
    (hl : σ (Fin.last (k + 1)) = false) :
    SumAll_T L W E t σ = (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹ *
      (SumAll_T L W E t (fun i : Fin (k + 1) => σ i.castSucc)
        - SumAll_T L W E t (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 false)) := by
  have hg : (fun i : Fin (k + 1) => σ i.castSucc)
      = Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 true := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [h0]
    · simp [Function.update_of_ne hi]
  have hw : ∀ a' : Fin (k + 1) → Z2 L,
      ∑ x : Z2 L, Kcal L W E t (loopOf L σ (Fin.snoc (α := fun _ => Z2 L) a' x))
        = (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹ *
          (Kcal L W E t (loopOf L (fun i : Fin (k + 1) => σ i.castSucc) a')
            - Kcal L W E t
              (loopOf L (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 false) a')) := by
    intro a'
    rw [Finset.sum_congr rfl (fun x _ => by rw [SumAll_loopOf_snoc σ h0 hl a' x])]
    rw [Kcal_ward L W hL hW E hE t ht (List.ofFn (fun i : Fin k => σ i.succ.castSucc))
      (List.ofFn a') (by simp)]
    have hgl := SumAll_loopOf_cons σ true a'
    rw [← hg] at hgl
    rw [hgl, SumAll_loopOf_cons σ false a']
  unfold SumAll_T
  rw [SumAll_sum_snoc (k + 1), Finset.sum_congr rfl (fun a' _ => hw a'), ← Finset.mul_sum,
    Finset.sum_sub_distrib]

end Total

/-! ## 4. Pure sign vectors -/

section Pure

variable {L : ℕ} [NeZero L]

private theorem SumAll_norm_inv_one_sub_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) (s : Bool) :
    ‖(1 - (t : ℂ) * (mSig E s * mSig E s))⁻¹‖ ≤ (gapK κ)⁻¹ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  rw [norm_inv]
  exact inv_anti₀ (SumAll_gapK_pos hκ hκ2) (SumAll_gapK_le_norm hκ hE ht0 s)

/-- `n = 1`. -/
private theorem SumAll_pure_one {W : ℕ} {E t : ℝ} (hE : |E| ≤ 2) (σ : Fin 1 → Bool) :
    ‖SumAll_T L W E t σ‖ ≤ (L : ℝ) ^ 2 := by
  have hK : ∀ a : Fin 1 → Z2 L, Kcal L W E t (loopOf L σ a) = mSig E (σ 0) := by
    intro a
    simp [loopOf, List.ofFn_succ, Kcal, Kgen, LoopIdx.length]
  unfold SumAll_T
  rw [Finset.sum_congr rfl (fun a _ => hK a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, SumAll_card_Z2]
  simp [SumAll_norm_mSig' hE]

/-- `n = 2`, pure. -/
private theorem SumAll_pure_two (hL : 3 ≤ L) {W : ℕ} {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) :
    ‖SumAll_T L W E t (fun _ : Fin 2 => s)‖
      ≤ (L : ℝ) ^ 2 * (((W : ℝ) ^ 2)⁻¹ * (gapK κ)⁻¹) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hK : ∀ a : Fin 2 → Z2 L, Kcal L W E t (loopOf L (fun _ : Fin 2 => s) a)
      = ((W : ℂ) ^ 2)⁻¹ * (mSig E s * mSig E s) *
        Theta L ((t : ℂ) * (mSig E s * mSig E s)) (a 0) (a 1) := by
    intro a
    have : loopOf L (fun _ : Fin 2 => s) a = ⟨[s, s], [a 0, a 1]⟩ := by
      simp [loopOf, List.ofFn_succ]
    rw [this, Kcal_two]
  have hξ : ‖(t : ℂ) * (mSig E s * mSig E s)‖ < 1 := by
    rw [SumAll_norm_xi' hE2 ht.1]; exact ht.2
  unfold SumAll_T
  rw [Finset.sum_congr rfl (fun a _ => hK a)]
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Z2 L)) _
    (fun p : Z2 L × Z2 L => ((W : ℂ) ^ 2)⁻¹ * (mSig E s * mSig E s) *
        Theta L ((t : ℂ) * (mSig E s * mSig E s)) p.1 p.2) (fun a => by simp [finTwoArrowEquiv])]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_Theta_row L hL hξ]
  rw [Finset.sum_const, Finset.card_univ, SumAll_card_Z2]
  have h2 : ‖((W : ℂ) ^ 2)⁻¹‖ = ((W : ℝ) ^ 2)⁻¹ := by simp
  have h3 : ‖mSig E s * mSig E s‖ = 1 := by
    rw [norm_mul, SumAll_norm_mSig' hE2]; norm_num
  have hC := SumAll_norm_inv_one_sub_le hκ hE ht.1 s
  have hAB : ‖((W : ℂ) ^ 2)⁻¹ * (mSig E s * mSig E s)‖ = ((W : ℝ) ^ 2)⁻¹ := by
    rw [norm_mul, h2, h3, mul_one]
  have hn : ‖((L ^ 2 : ℕ)) • (1 - (t : ℂ) * (mSig E s * mSig E s))⁻¹‖
      ≤ (L : ℝ) ^ 2 * (gapK κ)⁻¹ := by
    refine le_trans (norm_nsmul_le (E := ℂ)) ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hC (by positivity)
  calc _ ≤ ‖((W : ℂ) ^ 2)⁻¹ * (mSig E s * mSig E s)‖ *
        ‖((L ^ 2 : ℕ)) • (1 - (t : ℂ) * (mSig E s * mSig E s))⁻¹‖ := norm_mul_le _ _
    _ ≤ ((W : ℝ) ^ 2)⁻¹ * ((L : ℝ) ^ 2 * (gapK κ)⁻¹) := by rw [hAB]; gcongr
    _ = (L : ℝ) ^ 2 * (((W : ℝ) ^ 2)⁻¹ * (gapK κ)⁻¹) := by ring

/-- `n = k + 3 ≥ 3`, pure: only `π = ∅` survives; `(3.41)`, `sum_Kpi_closed`. -/
private theorem SumAll_pure_ge3 (hL : 3 ≤ L) {W : ℕ} {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (k : ℕ) :
    ‖SumAll_T L W E t (fun _ : Fin (k + 3) => s)‖
      ≤ (L : ℝ) ^ 2 * (((W : ℝ) ^ 2)⁻¹) ^ (k + 2) *
          (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * k + 4)) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := SumAll_gapK_pos hκ hκ2
  have hct := SumAll_gapK_le_norm hκ hE ht.1 s
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (SumAll_gapK_le_one κ)
  set σ : Fin (k + 3) → Bool := fun _ => s with hσ
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 := fun s s' => by
    rw [SumAll_norm_xi' hE2 ht.1]; exact ht.2
  have hzero : ∀ π ∈ (diagonals (k + 3)).powerset, π ≠ ∅ →
      (L : ℂ) ^ 2 * Alayer (mSig E) t σ π = 0 := by
    intro π _ hπ
    have hT : TSPlong (k + 3) σ π = ∅ := by
      unfold TSPlong
      refine Finset.filter_eq_empty_iff.2 fun F _ hF => hπ ?_
      rw [← hF]
      simp [Flong, hσ]
    simp [Alayer, Qlayer, hT]
  have hT : SumAll_T L W E t σ = ((W : ℂ) ^ 2)⁻¹ ^ (k + 3 - 1) * (∏ i, mSig E (σ i)) *
      ((L : ℂ) ^ 2 * Alayer (mSig E) t σ ∅) := by
    unfold SumAll_T
    rw [Finset.sum_congr rfl (fun a _ => Kcal_eq_sum_Kpi L W E t (k + 3) (by omega) σ a),
      ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl (fun π _ => sum_Kpi_closed (mSig E) hm hL σ π)]
    exact Finset.sum_eq_single_of_mem ∅ (by simp) hzero
  -- the bound on `Alayer`
  have hQ : ‖Qlayer (mSig E) t σ ∅‖ ≤ 2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1) := by
    unfold Qlayer
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ F ∈ TSPlong (k + 3) σ ∅,
        ‖∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2)‖ ≤ (gapK κ)⁻¹ ^ (k + 1) := by
      intro F hF
      have hFT : F ∈ TSP (k + 3) := (mem_filter.1 hF).1
      rw [norm_prod]
      calc ∏ e ∈ F, ‖edgeR (mSig E) t (σ e.1) (σ e.2)‖
          ≤ ∏ _e ∈ F, (gapK κ)⁻¹ := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => ?_
            have hμ : ‖mSig E s * mSig E s‖ = 1 := by
              rw [norm_mul, SumAll_norm_mSig' hE2]; norm_num
            exact SumAll_norm_edge_le hμ ht.1 ht.2.le hc hct
        _ = (gapK κ)⁻¹ ^ F.card := Finset.prod_const _
        _ ≤ (gapK κ)⁻¹ ^ (k + 1) :=
            pow_le_pow_right₀ hD1 (by have := SumAll_card_le_of_mem_TSP hFT; omega)
    calc ∑ F ∈ TSPlong (k + 3) σ ∅, ‖∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2)‖
        ≤ ∑ _F ∈ TSPlong (k + 3) σ ∅, (gapK κ)⁻¹ ^ (k + 1) := Finset.sum_le_sum hterm
      _ = (TSPlong (k + 3) σ ∅).card * (gapK κ)⁻¹ ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1) := by
          gcongr
          exact_mod_cast SumAll_card_TSPlong_le (k + 3) σ ∅
  have hA : ‖Alayer (mSig E) t σ ∅‖ ≤
      (gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)) := by
    unfold Alayer
    rw [norm_mul, norm_prod]
    have hP : ∏ v : Fin (k + 3), ‖(1 - (t : ℂ) * (mSig E (σ v) * mSig E (σ (v + 1))))⁻¹‖
        ≤ (gapK κ)⁻¹ ^ (k + 3) := by
      calc _ ≤ ∏ _v : Fin (k + 3), (gapK κ)⁻¹ :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ =>
              SumAll_norm_inv_one_sub_le hκ hE ht.1 s
        _ = _ := by simp
    exact mul_le_mul hP hQ (norm_nonneg _) (by positivity)
  rw [hT, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖((W : ℂ) ^ 2)⁻¹‖ = ((W : ℝ) ^ 2)⁻¹ := by simp
  have h2 : ‖∏ i, mSig E (σ i)‖ = 1 := by
    rw [norm_prod]; simp [hσ, SumAll_norm_mSig' hE2]
  have h3 : ‖(L : ℂ)‖ = L := by simp
  rw [h1, h2, h3, mul_one]
  have hk : k + 3 - 1 = k + 2 := by omega
  rw [hk]
  have hpos : (0 : ℝ) ≤ ((W : ℝ) ^ 2)⁻¹ ^ (k + 2) := by positivity
  calc _ ≤ ((W : ℝ) ^ 2)⁻¹ ^ (k + 2) * ((L : ℝ) ^ 2 *
        ((gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)))) := by gcongr
    _ = _ := by ring

/-- The bound `B_n = 2^{n²} c_κ^{-2n} (W² η_t)^{-(n-1)}`. -/
private noncomputable def SumAll_B (κ : ℝ) (W : ℕ) (E t : ℝ) (n : ℕ) : ℝ :=
  2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ 2 * etaT E t)⁻¹) ^ (n - 1)

/-- Pure sign vectors: `‖T_n(s,…,s)‖ ≤ L² B_n`. -/
private theorem SumAll_pure_bound (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (k : ℕ) :
    ‖SumAll_T L W E t (fun _ : Fin (k + 1) => s)‖ ≤ (L : ℝ) ^ 2 * SumAll_B κ W E t (k + 1) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hE' : |E| < 2 := by linarith
  have hc := SumAll_gapK_pos hκ hκ2
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (SumAll_gapK_le_one κ)
  have hη := SumAll_etaT_pos hE' ht.2
  have hη1 := SumAll_etaT_le_one E ht.1
  have hW0 : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  have hwu : ((W : ℝ) ^ 2)⁻¹ ≤ ((W : ℝ) ^ 2 * etaT E t)⁻¹ :=
    inv_anti₀ (mul_pos hW0 hη) (by nlinarith)
  have hw0 : (0 : ℝ) ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  unfold SumAll_B
  match k with
  | 0 =>
    refine (SumAll_pure_one hE2 _).trans ?_
    simp only [zero_add, Nat.sub_self, pow_zero, mul_one]
    refine le_mul_of_one_le_right hL0 ?_
    calc (1 : ℝ) ≤ 1 * 1 := by norm_num
      _ ≤ 2 ^ (1 ^ 2) * (gapK κ)⁻¹ ^ (2 * 1) := by
        gcongr
        · norm_num
        · exact one_le_pow₀ hD1
  | 1 =>
    refine (SumAll_pure_two hL hκ hE ht s).trans ?_
    simp only [Nat.add_sub_cancel, pow_one]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have h1 : (gapK κ)⁻¹ ≤ (gapK κ)⁻¹ ^ (2 * (1 + 1)) := by
      calc (gapK κ)⁻¹ = (gapK κ)⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hD1 (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ ((1 + 1) ^ 2) := one_le_pow₀ (by norm_num)
    calc ((W : ℝ) ^ 2)⁻¹ * (gapK κ)⁻¹
        ≤ ((W : ℝ) ^ 2 * etaT E t)⁻¹ * (gapK κ)⁻¹ ^ (2 * (1 + 1)) := by gcongr
      _ = 1 * (gapK κ)⁻¹ ^ (2 * (1 + 1)) * ((W : ℝ) ^ 2 * etaT E t)⁻¹ := by ring
      _ ≤ 2 ^ ((1 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (1 + 1)) * ((W : ℝ) ^ 2 * etaT E t)⁻¹ := by
        gcongr
  | k + 2 =>
    refine (SumAll_pure_ge3 hL hκ hE ht s k).trans ?_
    have hk : k + 2 + 1 - 1 = k + 2 := by omega
    rw [hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have h1 : ((W : ℝ) ^ 2)⁻¹ ^ (k + 2) ≤ ((W : ℝ) ^ 2 * etaT E t)⁻¹ ^ (k + 2) :=
      pow_le_pow_left₀ hw0 hwu _
    have h2 : (gapK κ)⁻¹ ^ (2 * k + 4) ≤ (gapK κ)⁻¹ ^ (2 * (k + 2 + 1)) :=
      pow_le_pow_right₀ hD1 (by omega)
    have h3 : (0 : ℝ) ≤ 2 ^ ((k + 3) ^ 2) := by positivity
    calc ((W : ℝ) ^ 2)⁻¹ ^ (k + 2) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * k + 4))
        ≤ ((W : ℝ) ^ 2 * etaT E t)⁻¹ ^ (k + 2) *
            (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 2 + 1))) := by gcongr
      _ = 2 ^ ((k + 2 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 2 + 1)) *
            ((W : ℝ) ^ 2 * etaT E t)⁻¹ ^ (k + 2) := by ring

end Pure

/-! ## 5. The induction over all sign vectors -/

section Induction

variable {L : ℕ} [NeZero L]

open Fin.NatCast in
/-- The claim `P(n)` for every sign vector: `‖T_n(σ)‖ ≤ L² B_n`. -/
private theorem SumAll_main (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    ∀ σ : Fin (k + 1) → Bool,
      ‖SumAll_T L W E t σ‖ ≤ (L : ℝ) ^ 2 * SumAll_B κ W E t (k + 1) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hE' : |E| < 2 := by linarith
  have hc := SumAll_gapK_pos hκ hκ2
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (SumAll_gapK_le_one κ)
  have hη := SumAll_etaT_pos hE' ht.2
  have hW0 : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  have hu : (0 : ℝ) < ((W : ℝ) ^ 2 * etaT E t)⁻¹ := inv_pos.2 (mul_pos hW0 hη)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  induction k with
  | zero =>
    intro σ
    have h := SumAll_pure_bound hL hW hκ hE ht (σ 0) 0
    have hσ : σ = fun _ => σ 0 := by
      funext i; rw [Fin.ext (show i.val = (0 : Fin (0 + 1)).val by have := i.isLt; simp)]
    rw [hσ]
    exact h
  | succ k ih =>
    intro σ
    by_cases hp : ∀ i, σ i = σ 0
    · have hσ : σ = fun _ => σ 0 := funext hp
      rw [hσ]
      exact SumAll_pure_bound hL hW hκ hE ht (σ 0) (k + 1)
    · obtain ⟨i0, hi0f, hi0t⟩ := SumAll_exists_false_true σ hp
      set σ' : Fin (k + 2) → Bool :=
        fun i => σ (i + (((i0 + 1 : Fin (k + 2)).val : ℕ) : Fin (k + 2))) with hσ'
      have hrot := SumAll_T_rot_iter hL hW hE' ht σ ((i0 + 1 : Fin (k + 2)).val)
      have h0 : σ' 0 = true := by simpa [hσ'] using hi0t
      have hl : σ' (Fin.last (k + 1)) = false := by
        have : Fin.last (k + 1) + (((i0 + 1 : Fin (k + 2)).val : ℕ) : Fin (k + 2)) = i0 := by
          rw [Fin.cast_val_eq_self, add_comm i0 1, ← add_assoc, Fin.last_add_one, zero_add]
        change σ (Fin.last (k + 1) + _) = false
        rw [this]; exact hi0f
      rw [hrot]
      change ‖SumAll_T L W E t σ'‖ ≤ _
      rw [SumAll_T_ward hL hW hE' ht σ' h0 hl, norm_mul]
      have hκn : ‖(2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹‖
          = (2 * (((W : ℝ) ^ 2 * etaT E t)))⁻¹ := by
        rw [norm_inv]
        congr 1
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_I, Complex.norm_natCast,
          Complex.norm_real, Real.norm_of_nonneg hη.le, mul_one]
        ring
      rw [hκn]
      have h1 := ih (fun i : Fin (k + 1) => σ' i.castSucc)
      have h2 := ih (Function.update (fun i : Fin (k + 1) => σ' i.castSucc) 0 false)
      have h3 : ‖SumAll_T L W E t (fun i : Fin (k + 1) => σ' i.castSucc)
          - SumAll_T L W E t (Function.update (fun i : Fin (k + 1) => σ' i.castSucc) 0 false)‖
          ≤ 2 * ((L : ℝ) ^ 2 * SumAll_B κ W E t (k + 1)) := by
        refine (norm_sub_le _ _).trans ?_
        linarith
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
      set u := ((W : ℝ) ^ 2 * etaT E t)⁻¹ with hudef
      have hinv : (2 * ((W : ℝ) ^ 2 * etaT E t))⁻¹ = 2⁻¹ * u := by
        rw [hudef, mul_inv]
      rw [hinv]
      unfold SumAll_B
      have h4 : (2 : ℝ) ^ ((k + 1) ^ 2) ≤ 2 ^ ((k + 1 + 1) ^ 2) :=
        pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
      have h5 : (gapK κ)⁻¹ ^ (2 * (k + 1)) ≤ (gapK κ)⁻¹ ^ (2 * (k + 1 + 1)) :=
        pow_le_pow_right₀ hD1 (by omega)
      have hk1 : k + 1 - 1 = k := by omega
      have hk2 : k + 1 + 1 - 1 = k + 1 := by omega
      rw [hk1, hk2]
      calc 2⁻¹ * u * (2 * ((L : ℝ) ^ 2 * (2 ^ ((k + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1)) * u ^ k)))
          = (L : ℝ) ^ 2 * ((2 ^ ((k + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1))) * u ^ (k + 1)) := by
            ring
        _ ≤ (L : ℝ) ^ 2 * ((2 ^ ((k + 1 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1 + 1))) *
              u ^ (k + 1)) := by gcongr
        _ = _ := by ring

end Induction

/-! ## 6. The theorem -/

/-- **`lem_sumAinK`, `(sumallAinK)`**, with the explicit constant
`2^{n²} c_κ^{-2n}`:
`|∑_{a₂,…,aₙ} 𝒦_{t,σ,a}| ≤ C_{n,κ} (W² η_t)^{-n+1}`. -/
theorem Kcal_sumAll_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) (hn : 2 ≤ n) (σ : Fin n → Bool),
      σ ⟨0, by omega⟩ = true → σ ⟨n - 1, by omega⟩ = false → ∀ a₁ : Z2 L,
        ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Z2 L => a ⟨0, by omega⟩ = a₁),
            Kcal L W E t (loopOf L σ a)‖
          ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ 2 * etaT E t)⁻¹) ^ (n - 1) := by
  intro κ hκ L W _ hL hW E hE t ht n hn σ _ _ a₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have hE' : |E| < 2 := by linarith
  have hmain := SumAll_main hL hW hκ hE ht (k + 1) σ
  have hfib := SumAll_T_eq_fiber hL hW hE' ht σ a₁
  have hz : ((⟨0, by omega⟩ : Fin (k + 1 + 1))) = 0 := rfl
  simp only [hz]
  rw [hfib, norm_mul, norm_pow, Complex.norm_natCast] at hmain
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    positivity
  exact le_of_mul_le_mul_left hmain hL2

end RBM.KLoop
