/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.Defs
import RBM2D.Induction.ScaleFacts
import RBM2D.Induction.PerTimeCalc
import RBM2D.Path.ScalesBridge
import RBM2D.Loop.TreeRep
import RBM2D.Gauss.LoopInitialValueSupport
import RBM2D.Gauss.SpectralAlgebra

/-!
# The initial data at `s ≡ 0` and the induction chain

The statements `InitAtZero` and `ChainTarget`; the hypothesis `0 < κ →` is the first hypothesis
of `InitAtZero`.

Results:
1. `initAtZero`: at `s ≡ 0` the three hypotheses `InitLK`, `InitDecay`, `InitLocal` of Theorem
   `lem:main_ind` hold exactly (`H_0 = 0`, `G_0 = m`, `𝓛_0 = 𝒦_0`; `ini)bigasya`);
2. `chainTarget`: from Theorem `lem:main_ind` (as a hypothesis), `InitAtZero`, `ChainStepCond`
   and the kernel bound `KboundConcl`, the conclusions of Lemmas `ML:GLoop`, `ML:GLoop_expec`,
   `ML:GtLocal` at every bulk energy sequence and every time sequence in range (the proof of
   these lemmas from `lem:main_ind` in the paper).

Paper: arXiv:2503.07606, Section 2 (strategy of the proofs of the main lemmas).

The argument parallels the one-dimensional formalization.  For `d = 2` the index is `Z2 L`, the
block normalization is `W⁻²` per edge, and the chain times are `chainTime`
(`1 - s_k = (1 - t)^{k/n₀}`, `n₀` fixed) with `chainStepCond` in place of the `d = 1` grid.

`RBM.KLoop` is not opened (its `loopOf` would clash with `RBM.Path.loopOf`).
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. The statements -/

/-- **The initial data (`ini)bigasya`)**: at `s ≡ 0` the three hypotheses of
Theorem `lem:main_ind` hold (exactly: `H_0 = 0`, `G_0 = m`, `𝓛_0 = 𝒦_0`), for every bulk
energy sequence.  Inputs: `seqHflow_zero`, `m² + E m + 1 = 0`, and the initial value of `𝒦`. -/
def InitAtZero (κ : ℝ) : Prop :=
  0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → SizeTendsto d →
    MainIndConcl d E (fun _ => 0)

/-- **The chain (Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`)**: from
Theorem `lem:main_ind` (all sequences), the initial data and the `𝒦` bound, the conclusions
hold at every bulk energy sequence and every time sequence `0 ≤ t ≤ 1 - N^{-1+τ}`. -/
def ChainTarget (κ c τ : ℝ) : Prop :=
  0 < κ → 0 < c → 0 < τ → SizeTendsto d → Bandwidth d c → KboundConcl κ →
  InitAtZero d κ → ChainStepCond d κ c τ →
  (∀ (E s t : ℕ → ℝ), MainIndHyp d κ c τ E s t → MainIndConcl d E t) →
  ∀ (E t : ℕ → ℝ), (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) →
    RangeCond d τ t → MLConcl d E t

/-! ## 2. Elementary facts -/

section Elementary

/-- A deterministic pointwise bound `ξ ≤ size^τ ζ` (for every `τ > 0`, eventually) gives
`ξ ≺ ζ` per time: the failure event is empty. -/
private theorem chain_pt_of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D _
  filter_upwards [h τ hτ] with l hl u
  have : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [this, measure_empty]
  exact zero_le

/-- A vanishing left side is dominated by any non-negative right side. -/
private theorem chain_pt_of_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hξ : ∀ l u ω, ξ l u ω = 0) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    PerTimeDomAt P size ξ ζ :=
  chain_pt_of_le fun τ _ => Eventually.of_forall fun l u ω => by
    rw [hξ l u ω]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ l u ω)

/-- Bulk energy: `|E| < 2` and `√(2κ)/2 ≤ Im m` for `|E| ≤ 2 - κ`. -/
private theorem chain_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    |E| < 2 ∧ Real.sqrt (2 * κ) / 2 ≤ (spectralM E).im := by
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hκ2 : κ ≤ 2 := by linarith
  refine ⟨by linarith, ?_⟩
  rw [spectralM_im]
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ hE0 hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

private theorem chain_one_le_L (n : ℕ) : 1 ≤ d.L n := by
  have := d.three_le_L n; omega

end Elementary

/-! ## 3. The initial data at `s ≡ 0` -/

section Initial

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `G_0 = (0 - z_0)^{-1} = m I` on the fine lattice `Idx L W`. -/
private theorem chain_green_zero {E : ℝ} (hE : |E| ≤ 2) :
    ((0 : Matrix (Idx L W) (Idx L W) ℂ) - spectralZ E 0 • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ =
      spectralM E • (1 : Matrix (Idx L W) (Idx L W) ℂ) := by
  have hm := spectralM_mul hE
  have hz : -spectralZ E 0 * spectralM E = 1 := by
    simp only [spectralZ, Complex.ofReal_zero, sub_zero, one_mul]
    linear_combination -hm
  refine Matrix.inv_eq_right_inv ?_
  rw [zero_sub, ← neg_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul, hz, one_smul]

/-- `‖G_0 - m‖_max = 0` entrywise. -/
private theorem chain_llErrMat_zero {E : ℝ} (hE : |E| ≤ 2) (i j : Idx L W) :
    llErrMat L W E 0 0 i j = 0 := by
  unfold llErrMat
  rw [chain_green_zero hE]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The scalar of a signed Green factor at `z_0` is `m(σ)`. -/
private theorem chain_initialGreenScalar {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    initialGreenScalar E s = KLoop.mSig E s := by
  have hm := spectralM_mul hE
  have h1 : -((E : ℂ) + spectralM E) * spectralM E = 1 := by linear_combination -hm
  cases s
  · have h2 : -((starRingEnd ℂ) ((E : ℂ) + spectralM E)) * (starRingEnd ℂ) (spectralM E) = 1 := by
      have := congrArg (starRingEnd ℂ) h1
      simpa [map_mul, map_neg] using this
    simp only [initialGreenScalar, KLoop.mSig, Bool.false_eq_true, ite_false]
    exact inv_eq_of_mul_eq_one_right h2
  · simp only [initialGreenScalar, KLoop.mSig, ite_true]
    exact inv_eq_of_mul_eq_one_right h1

omit [NeZero L] in
/-- A label word that is not constant has an unequal adjacent pair. -/
private theorem chain_adjacentMismatch (a : Z2 L) (as : List (Z2 L))
    (h : ¬ ∀ b ∈ as, b = a) : AdjacentMismatch L (a :: as) := by
  induction as generalizing a with
  | nil => simp at h
  | cons b bs ih =>
      change a ≠ b ∨ AdjacentMismatch L (b :: bs)
      by_cases hab : a = b
      · subst hab
        right
        refine ih a fun hall => h ?_
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact hall c hc
      · exact Or.inl hab

omit [NeZero W] in
/-- `adjacentBlockWeight` in the form of `primInit`: `(W^{-2})^{n-1} 1(a₁ = ⋯ = aₙ)`. -/
private theorem chain_adjacentBlockWeight (a : Z2 L) (as : List (Z2 L)) :
    adjacentBlockWeight L W (a :: as) =
      ((W : ℂ) ^ 2)⁻¹ ^ as.length *
        (if ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y then 1 else 0) := by
  by_cases hsame : ∀ b ∈ as, b = a
  · have hc : ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y := by
      intro x hx y hy
      have hx' : x = a := by
        rcases List.mem_cons.1 hx with rfl | hx
        · rfl
        · exact hsame x hx
      have hy' : y = a := by
        rcases List.mem_cons.1 hy with rfl | hy
        · rfl
        · exact hsame y hy
      rw [hx', hy']
    rw [adjacentBlockWeight_all_same L W a as hsame, ite_eq_left_of_eq_true _ _ (eq_true hc),
      mul_one, inv_pow]
  · have hc : ¬ ∀ x ∈ a :: as, ∀ y ∈ a :: as, x = y := fun hall =>
      hsame fun b hb => hall b (List.mem_cons_of_mem a hb) a List.mem_cons_self
    rw [adjacentBlockWeight_zero_of_mismatch L W (a :: as) (chain_adjacentMismatch a as hsame),
      ite_eq_right_of_eq_false _ _ (eq_false hc), mul_zero]

/-- **`𝓛_0 = 𝒦_0`**: at `H_0 = 0` and `z_0 = E + m`, every well-formed loop of length
`≥ 1` equals the primitive loop `KLoop.Kcal` at `t = 0` (via its initial data,
`isPrimitive_Kcal`). -/
private theorem chain_gloop_zero (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) (I : LoopIdx (Z2 L))
    (hI : I.WF) (h1 : 1 ≤ I.length) :
    gloop L W (blockMat (0 : Matrix (Idx L W) (Idx L W) ℂ)) (spectralZ E 0) I =
      KLoop.Kcal L W E 0 I := by
  have hb : blockMat (0 : Matrix (Idx L W) (Idx L W) ℂ) = 0 := by
    simp [blockMat]
  have hg : gloop L W 0 (spectralZ E 0) I = initialLoopValue L W E I := by
    simp [initialLoopValue, spectralZ]
  have hP := KLoop.isPrimitive_Kcal L W hL (NeZero.pos W) E hE
  obtain ⟨σ, as0⟩ := I
  cases as0 with
  | nil => simp [LoopIdx.length] at h1
  | cons a as =>
    rw [hb, hg, initialLoopValue_nonempty L W hE ⟨σ, a :: as⟩ hI a as rfl]
    have hK : KLoop.Kcal L W E 0 ⟨σ, a :: as⟩ = KLoop.primInit L W (KLoop.mSig E) ⟨σ, a :: as⟩ := by
      by_cases h2 : 2 ≤ LoopIdx.length ⟨σ, a :: as⟩
      · exact hP.2.1 _ hI h2
      · have has : as = [] := by
          simp only [LoopIdx.length, List.length_cons] at h2
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst has
        have hσ : σ.length = 1 := by simpa [LoopIdx.WF] using hI
        obtain ⟨s, rfl⟩ : ∃ s, σ = [s] := List.length_eq_one_iff.1 hσ
        refine (hP.2.2 0 ⟨le_rfl, zero_lt_one⟩ s a).trans ?_
        simp [KLoop.primInit, LoopIdx.length]
    rw [hK]
    have hσ : σ.length = (a :: as).length := hI
    have hmap : (σ.zip (a :: as)).map (fun p => initialGreenScalar E p.1) =
        σ.map (KLoop.mSig E) := by
      have hfun : (fun p : Bool × Z2 L => initialGreenScalar E p.1) =
          KLoop.mSig E ∘ Prod.fst := funext fun p => chain_initialGreenScalar hE.le p.1
      rw [hfun, ← List.map_map, List.map_fst_zip hσ.le]
    simp only [KLoop.primInit, LoopIdx.length, List.length_cons, Nat.add_sub_cancel]
    rw [hmap, chain_adjacentBlockWeight]
    ring

/-- `|(𝓛 - 𝒦)_{0,(+,-),(a,b)}| = 0` with `𝒦 = Kpm` (`Kn2sol` at `t = 0`: `Θ_0 = 1`). -/
private theorem chain_lkErrMat_zero {E : ℝ} (hE : |E| < 2) (a b : Z2 L) :
    lkErrMat L W E 0 0 a b = 0 := by
  have hb : blockMat (0 : Matrix (Idx L W) (Idx L W) ℂ) = 0 := by
    simp [blockMat]
  have hg : gloop L W 0 (spectralZ E 0) (pmLoop a b) = initialLoopValue L W E (pmLoop a b) := by
    simp [initialLoopValue, spectralZ]
  unfold lkErrMat
  rw [hb, hg]
  unfold pmLoop
  rw [initialLoopValue_two_edges L W hE, chain_initialGreenScalar hE.le,
    chain_initialGreenScalar hE.le]
  have hT : Theta L (((0 : ℝ) : ℂ) * (Complex.normSq (spectralM E) : ℂ)) = 1 := by
    simp [Theta]
  unfold Kpm
  rw [hT]
  simp only [KLoop.mSig, ite_true, Bool.false_eq_true, ite_false, Complex.mul_conj]
  by_cases hab : a = b
  · subst hab; simp; ring
  · simp [hab]

/-- `|(𝓛 - 𝒦)_{0,σ,a}| = 0` for every loop of length `k ≥ 1`. -/
private theorem chain_lkGen_zero (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    lkGen L W E 0 0 σ a = 0 := by
  unfold lkGen
  rw [chain_gloop_zero hL hE (loopOf σ a) (by simp [loopOf, LoopIdx.WF])
    (by simpa [loopOf, LoopIdx.length] using hk), sub_self, norm_zero]

end Initial

/-- **`InitAtZero` holds**: at `s ≡ 0`, `H_0 = 0`, so `G_0 = m`, `𝓛_0 = 𝒦_0`, and
the three error functionals vanish identically. -/
theorem initAtZero (κ : ℝ) : InitAtZero d κ := by
  intro hκ E hE _hS
  have hE2 : ∀ n, |E n| < 2 := fun n => (chain_bulk hκ (hE n)).1
  have hM : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) 0 := fun n =>
    scaleM_pos (chain_one_le_L d n) (d.W_pos n) (hE2 n) zero_lt_one
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    refine chain_pt_of_zero (fun n p ω => ?_) (fun n _ _ => ?_)
    · simp only [Sizes.seqHflow_zero]
      exact chain_lkGen_zero (d.three_le_L n) (hE2 n) hk _ _
    · exact pow_nonneg (inv_nonneg.2 (hM n).le) _
  · intro D _
    refine chain_pt_of_zero (fun n p ω => ?_) (fun n _ _ => ?_)
    · simp only [Sizes.seqHflow_zero]
      exact chain_lkErrMat_zero (hE2 n) _ _
    · have := hM n
      positivity
  · refine chain_pt_of_zero (fun n p ω => ?_) (fun n _ _ => ?_)
    · simp only [Sizes.seqHflow_zero]
      exact chain_llErrMat_zero (hE2 n).le _ _
    · exact Real.rpow_nonneg (inv_nonneg.2 (hM n).le) _

/-! ## 4. The chain -/

section Chain

variable {d}

/-- `KboundConcl κ` along the sequence `(L n, W n, E n, t n)`: `|𝒦_{t,σ,a}| ≺ M_t^{-(k-1)}`
per time (`ML:Kbound`, via `kloop_Mt_eq`).  The two `loopOf` (`RBM.Path`, `RBM.KLoop`) have the same body. -/
private theorem chain_Kbound_seq {κ : ℝ} {E t : ℕ → ℝ} (hK : KboundConcl κ)
    (hS : SizeTendsto d) (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p _ => ‖KLoop.Kcal (d.L n) (d.W n) (E n) (t n) (loopOf p.2.1 p.2.2)‖)
      (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1)) := by
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hS
  refine chain_pt_of_le fun τ' hτ' => ?_
  filter_upwards [hsize.eventually (hK k hk τ' hτ')] with n hn p ω
  let par : KLoop.Par κ (d.size n) :=
    { L := d.L n, W := d.W n, hL := d.three_le_L n, hW := d.W_pos n,
      hN := (Sizes.size_eq d n).symm, E := E n, hE := hE n, t := t n,
      ht0 := ht0 n, ht1 := ht1 n }
  have h1 := hn ⟨par, p.2.1, p.2.2⟩
  simp only [] at h1
  rw [kloop_Mt_eq (ht1 n).le] at h1
  exact h1

/-- `M_t ≥ 1` eventually (`scaleFacts_R1` at `u = t n`: `M_t ≥ Im m · N^{min(2c,τ)} → ∞`). -/
private theorem chain_one_le_Mt {κ c τ : ℝ} {E t : ℕ → ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hτ : 0 < τ) (hS : SizeTendsto d) (hB : Bandwidth d c) (hE : ∀ n, |E n| ≤ 2 - κ)
    (hR : RangeCond d τ t) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scaleM (d.L n) (d.W n) (E n) (t n) := by
  have hc0 : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  have hc1 : 0 < Real.sqrt (2 * κ) / 2 := by
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith
  have hS' : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop := hS
  have h1 : Tendsto (fun n => Real.sqrt (2 * κ) / 2 * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ))
      atTop atTop := ((tendsto_rpow_atTop hc0).comp hS').const_mul_atTop hc1
  filter_upwards [scaleFacts_R1 d κ c τ E t hE hκ hc hτ hB hR, h1.eventually_ge_atTop 1]
    with n hn h1n
  refine h1n.trans ((mul_le_mul_of_nonneg_right (chain_bulk hκ (hE n)).2
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (hn (t n) le_rfl))

/-- Monotonicity and range of the chain times: for `0 ≤ t n < 1`, `k ≤ k'`,
`0 ≤ s_k ≤ s_{k'} < 1`. -/
private theorem chain_chainTime_facts {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1)
    (n₀ k : ℕ) (n : ℕ) :
    0 ≤ chainTime t n₀ k n ∧ chainTime t n₀ k n ≤ chainTime t n₀ (k + 1) n ∧
      chainTime t n₀ (k + 1) n < 1 := by
  have hb0 : 0 < 1 - t n := by linarith [ht1 n]
  have hb1 : 1 - t n ≤ 1 := by linarith [ht0 n]
  have hn₀ : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  unfold chainTime
  refine ⟨?_, ?_, ?_⟩
  · have := Real.rpow_le_one hb0.le hb1 (div_nonneg (Nat.cast_nonneg k) hn₀)
    linarith
  · have hkk : ((k : ℕ) : ℝ) / n₀ ≤ ((k + 1 : ℕ) : ℝ) / n₀ :=
      div_le_div_of_nonneg_right (by push_cast; linarith) hn₀
    have := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hkk
    linarith
  · have := Real.rpow_pos_of_pos hb0 (((k + 1 : ℕ) : ℝ) / n₀)
    linarith

end Chain

/-- **`ChainTarget` holds** (the proof of Lemmas `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` from
Theorem `lem:main_ind`).  Fix `n₀ > 30/min(2c,τ)`; by induction over `k ≤ n₀`,
`MainIndConcl` holds at `s_k = chainTime t n₀ k` (`k = 0`: `InitAtZero`; the step: the
`lem:main_ind` hypothesis on `[s_k, s_{k+1}]` with `ChainStepCond`); `s_{n₀} = t`.  Then
(`Eq:L-KGt2`): `|𝓛| ≤ |𝓛 - 𝒦| + |𝒦| ≺ M_t^{-k} + M_t^{-(k-1)} ≤ 2 M_t^{-(k-1)}` from `InitLK`
at `t` and `KboundConcl`. -/
theorem chainTarget (κ c τ : ℝ) : ChainTarget d κ c τ := by
  intro hκ hc hτ hS hB hK hInit hStep hMain E t hE ht0 ht1 hR
  have hc0 : 0 < min (2 * c) τ := lt_min (by linarith) hτ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (30 / min (2 * c) τ)
  have hn₀pos : (0 : ℝ) < n₀ := lt_trans (div_pos (by norm_num) hc0) hn₀
  -- the induction over the chain
  have key : ∀ k : ℕ, k ≤ n₀ → MainIndConcl d E (chainTime t n₀ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : chainTime t n₀ 0 = fun _ => 0 := by
        funext n; simp [chainTime]
      rw [h0]
      exact hInit hκ E hE hS
    | succ k ih =>
      intro hk
      have hk' : k < n₀ := by omega
      obtain ⟨hCond, hRk⟩ := hStep E t n₀ hE hκ hc hτ hn₀ ht0 hS hB hR k hk'
      have hf := chain_chainTime_facts ht0 ht1 n₀ k
      have ihk := ih hk'.le
      exact hMain E (chainTime t n₀ k) (chainTime t n₀ (k + 1))
        ⟨hκ, hE, hc, hτ, fun n => (hf n).1, fun n => (hf n).2.1, fun n => (hf n).2.2, hS, hB,
          hCond, hRk, ihk.1, ihk.2.1, ihk.2.2⟩
  have hend : chainTime t n₀ n₀ = t := by
    funext n
    simp [chainTime, div_self hn₀pos.ne']
  have hMC : MainIndConcl d E t := hend ▸ key n₀ le_rfl
  refine ⟨hMC, fun k hk => ?_⟩
  -- (`Eq:L-KGt2`) at `t`
  have hsize : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hS
  have hMpos : ∀ n, 0 < scaleM (d.L n) (d.W n) (E n) (t n) := fun n =>
    scaleM_pos (chain_one_le_L d n) (d.W_pos n) (chain_bulk hκ (hE n)).1 (ht1 n)
  have hsum := PerTimeCalc.PerTime.perTimeCalc_add hsize (hMC.1 k hk)
    (chain_Kbound_seq hK hS hE ht0 ht1 hk)
  have h₁ := PerTimeCalc.PerTime.perTimeCalc_mono hsize (P := Sizes.seqP d) (size := d.size)
    (ζ' := fun n (_ : Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n))) (_ : Sizes.SeqΩ d) =>
      (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1))
    (fun n _ _ => pow_nonneg (inv_nonneg.2 (hMpos n).le) _) 2 ?_ hsum
  swap
  · filter_upwards [chain_one_le_Mt hκ hc hτ hS hB hE hR] with n hn p ω
    have h1 : (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
    have h2 : (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ k ≤
        (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1) :=
      pow_le_pow_of_le_one (inv_nonneg.2 (hMpos n).le) h1 (Nat.sub_le k 1)
    change (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ k +
        (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1) ≤
      2 * (scaleM (d.L n) (d.W n) (E n) (t n))⁻¹ ^ (k - 1)
    linarith
  refine PerTimeCalc.PerTime.stochDom_of_le_left_eventually
    (Eventually.of_forall fun n p ω => ?_) h₁
  unfold loopAbs lkGen
  exact norm_le_norm_sub_add _ _

end RBM.Ind

/-! ## Checks -/
