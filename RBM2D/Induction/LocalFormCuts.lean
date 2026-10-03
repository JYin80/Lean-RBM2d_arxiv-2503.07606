/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.LocalFormCalc

/-!
# Local forms of the three cut-sum tensors `B₁, B₂, B₃`

Paper: arXiv:2503.07606, Section 5 (`int_K-L+Q2`, `lem_BcalE`) and Section 7 (`a-local-form`).
Namespace `RBM.Ind`, `variable (d : Sizes)`.

Results: `altLocalFormAt_one`, `altLocalFormAt_two`, `altLocalFormAt_three` are `AltLocalFormAt`
(`RBM2D.Induction.LocalFormCalc`) at `m = 1, 2, 3`.

1. **Cut-glue as loops** (`cutGlueL_loopOf`, `cutGlueR_loopOf`, `cutGlue_loopOf`): for
   `z = (c₀, …, c_{n-1}, a', b')` the loops `𝒢^{L}_{k',l'}(a')`, `𝒢^{R}_{k',l'}(b')`,
   `𝒢_{k'}(b')` of `loopOf σ c` are `loopOf` of an explicit sign vector and label positions
   in `z`.
2. **Form algebra**: `liftF`, `sumF`, `tsmulF`; the predicate `BlkLab` (entries in blocks that are
   labels) with its closure lemmas; `Fac`, a tensor with a local form (`mul`, `lift`, `tsmul`,
   `sum`, `add`) and the pieces `Fac.lk`, `Fac.kcal`, `Fac.loop`.
3. **Far part of a product** (`farPT_prod`): if `|a' - b'| ≤ 1` and `maxDist z ≥ ρ`, one of the two
   pieces has `maxDist ≥ (ρ-1)/2`; the far part of each piece is `DecayLoopPT` (`lk`, `loop`) or
   `KcalDecay` (`kcal`); the sum over the cuts.
4. **The assembly** (`cutAssembly`): `𝒬_u(𝔎^{tr}X^{tr})` with `𝔎 = W² cutKer S^{(B)}` through
   `kernelAssembly_PT`; the three cases only supply the tensor `X` and its local form.

Locality: the tensors are `1(|a'-b'| ≤ 1)` times products of pieces whose entries lie in the
blocks of the labels `z_i`; after truncation to `maxDist z < ρ` the form is `Loc0 (2ρ)`, the cut
kernel adds `2ρ`, so `Loc0 (4ρ)`, `4ρ = ℓ_u W^{τ₀}/2 < ℓ_u W^{τ₀}` (`ρ = ℓ_u W^{τ₀}/8`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

namespace LocalFormCuts

open LocalFormCalc

/-! ## 1. Cut-glue as loops -/

section CutGlue

variable {L : ℕ} [NeZero L] {n : ℕ}

/-- The sign vector `σ` extended by `false` to all of `ℕ`. -/
def sx (σ : Fin n → Bool) (j : ℕ) : Bool := if h : j < n then σ ⟨j, h⟩ else false

/-- The positions in `z = (c₀, …, c_{n-1}, a', b')` of the labels of the left piece
`𝒢^{L}_{k',l'}(a')`: `c₀ … c_{k'-2}, a', c_{l'-1} … c_{n-1}`. -/
def fL (n k' l' : ℕ) (i : Fin (k' + n - l' + 1)) : Fin (n + 2) :=
  ⟨min (if i.val < k' - 1 then i.val else if i.val = k' - 1 then n else l' - k' + i.val - 1) (n + 1),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The signs of the left piece: `σ₀ … σ_{k'-1}, σ_{l'-1} … σ_{n-1}`. -/
def sL (σ : Fin n → Bool) (k' l' : ℕ) (i : Fin (k' + n - l' + 1)) : Bool :=
  sx σ (if i.val < k' then i.val else l' - k' + i.val - 1)

set_option linter.flexible false in
/-- **Cut-glue as loops (left)**: `𝒢^{L}_{k',l'}(a')(loopOf σ c) = loopOf (sL σ k' l') (z ∘ fL)` for
`z = (c, a', b')`, `1 ≤ k' < l' ≤ n`. -/
theorem cutGlueL_loopOf (σ : Fin n → Bool) (z : Fin (n + 2) → Z2 L) {k' l' : ℕ} (hk : 1 ≤ k')
    (hkl : k' < l') (hl : l' ≤ n) :
    (loopOf σ (fun i : Fin n => z (Fin.castAdd 2 i))).cutGlueL k' l' (z (Fin.natAdd n 0)) =
      loopOf (sL σ k' l') (fun i => z (fL n k' l' i)) := by
  unfold loopOf
  refine LoopIdx.ext ?_ ?_
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlueL]; omega
    · intro i h1 h2
      have hi : i < k' + n - l' + 1 := by simpa using h2
      simp only [LoopIdx.cutGlueL, List.getElem_append, List.getElem_take, List.getElem_drop,
        List.getElem_ofFn, List.length_take, List.length_ofFn, sL, sx]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlueL]; omega
    · intro i h1 h2
      have hi : i < k' + n - l' + 1 := by simpa using h2
      simp only [LoopIdx.cutGlueL, List.getElem_append, List.getElem_take, List.getElem_drop,
        List.getElem_ofFn, List.length_take, List.length_ofFn, List.getElem_cons, fL]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)

/-- The positions in `z = (c, a', b')` of the labels of the right piece `𝒢^{R}_{k',l'}(b')`:
`c_{k'-1} … c_{l'-2}, b'`. -/
def fR (n k' l' : ℕ) (i : Fin (l' - k' + 1)) : Fin (n + 2) :=
  ⟨min (if i.val < l' - k' then k' - 1 + i.val else n + 1) (n + 1),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The signs of the right piece: `σ_{k'-1} … σ_{l'-1}`. -/
def sR (σ : Fin n → Bool) (k' l' : ℕ) (i : Fin (l' - k' + 1)) : Bool := sx σ (k' - 1 + i.val)

set_option linter.flexible false in
/-- **Cut-glue as loops (right)**: `𝒢^{R}_{k',l'}(b')(loopOf σ c) = loopOf (sR σ k' l') (z ∘ fR)`. -/
theorem cutGlueR_loopOf (σ : Fin n → Bool) (z : Fin (n + 2) → Z2 L) {k' l' : ℕ} (hk : 1 ≤ k')
    (hkl : k' < l') (hl : l' ≤ n) :
    (loopOf σ (fun i : Fin n => z (Fin.castAdd 2 i))).cutGlueR k' l' (z (Fin.natAdd n 1)) =
      loopOf (sR σ k' l') (fun i => z (fR n k' l' i)) := by
  unfold loopOf
  refine LoopIdx.ext ?_ ?_
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlueR]; omega
    · intro i h1 h2
      have hi : i < l' - k' + 1 := by simpa using h2
      simp only [LoopIdx.cutGlueR, List.getElem_take, List.getElem_drop, List.getElem_ofFn, sR, sx]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlueR]; omega
    · intro i h1 h2
      have hi : i < l' - k' + 1 := by simpa using h2
      simp only [LoopIdx.cutGlueR, List.getElem_append, List.getElem_take, List.getElem_drop,
        List.getElem_ofFn, List.length_take, List.length_drop, List.length_ofFn, List.getElem_cons,
        fR]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)

/-- The positions in `z = (c, a', b')` of the labels of the single-cut loop `𝒢_{k'}^{(b')}`:
`c₀ … c_{k'-2}, b', c_{k'-1} … c_{n-1}`. -/
def f3 (n k' : ℕ) (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨min (if i.val < k' - 1 then i.val else if i.val = k' - 1 then n + 1 else i.val - 1) (n + 1),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The signs of the single-cut loop: `σ₀ … σ_{k'-1}, σ_{k'-1} … σ_{n-1}`. -/
def s3 (σ : Fin n → Bool) (k' : ℕ) (i : Fin (n + 1)) : Bool :=
  sx σ (if i.val < k' then i.val else i.val - 1)

set_option linter.flexible false in
/-- **Cut-glue as loops (single edge)**: `𝒢_{k'}^{(b')}(loopOf σ c) = loopOf (s3 σ k') (z ∘ f3)`. -/
theorem cutGlue_loopOf (σ : Fin n → Bool) (z : Fin (n + 2) → Z2 L) {k' : ℕ} (hk : 1 ≤ k')
    (hkn : k' ≤ n) :
    (loopOf σ (fun i : Fin n => z (Fin.castAdd 2 i))).cutGlue k' (z (Fin.natAdd n 1)) =
      loopOf (s3 σ k') (fun i => z (f3 n k' i)) := by
  unfold loopOf
  refine LoopIdx.ext ?_ ?_
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlue]; omega
    · intro i h1 h2
      have hi : i < n + 1 := by simpa using h2
      simp only [LoopIdx.cutGlue, List.getElem_append, List.getElem_take, List.getElem_drop,
        List.getElem_ofFn, List.length_take, List.length_ofFn, s3, sx]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)
  · apply List.ext_getElem
    · simp [LoopIdx.cutGlue]; omega
    · intro i h1 h2
      have hi : i < n + 1 := by simpa using h2
      simp only [LoopIdx.cutGlue, List.getElem_append, List.getElem_take, List.getElem_drop,
        List.getElem_ofFn, List.length_take, List.length_ofFn, List.getElem_cons, f3]
      split_ifs <;> (try (exfalso; omega)) <;> (try congr 1) <;> (try ext) <;> (try simp) <;>
        (try omega)

end CutGlue

/-! ## 2. Form algebra: lifting, finite sums, tensor scalars, blocks that are labels -/

section Algebra

variable {L W : ℕ} [NeZero L] [NeZero W] {k K K₁ K₂ : ℕ}

/-- Lifting a form to a larger degree bound (coefficients of degree `> K₁` are `0`). -/
def liftF (K₂ : ℕ) (F : LocalForm L W k K₁) : LocalForm L W k K₂ :=
  ⟨fun b j q => if h : j.val < K₁ + 1 then F.coef b ⟨j.val, h⟩ q else 0⟩

/-- Lifting does not change the evaluation. -/
theorem eval_liftF (h : K₁ ≤ K₂) (F : LocalForm L W k K₁) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (liftF K₂ F).eval E s M b = F.eval E s M b := by
  simp only [eval_eq]
  have hK : K₁ + 1 ≤ K₂ + 1 := by omega
  rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin (K₁ + 1))).map (Fin.castLEEmb hK))
    (Finset.subset_univ _)]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    have hj : ((Fin.castLEEmb hK) j).val < K₁ + 1 := j.isLt
    simp only [liftF, hj, ↓reduceDIte]
    rfl
  · intro j _ hj
    have hn : ¬ j.val < K₁ + 1 := by
      intro hlt
      apply hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact ⟨⟨j.val, hlt⟩, by ext; simp⟩
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [liftF, hn, ↓reduceDIte, zero_mul]

/-- Lifting keeps a coefficient bound. -/
theorem coef_liftF_le (F : LocalForm L W k K₁) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B) (b : Fin k → Z2 L) (j : Fin (K₂ + 1))
    (q : Fin j → Mono L W) : ‖(liftF K₂ F).coef b j q‖ ≤ B := by
  simp only [liftF]
  split_ifs with h
  · exact hF b ⟨j.val, h⟩ q
  · simpa using hB

/-- A finite sum of forms of the same degree. -/
def sumF {ι : Type*} (s : Finset ι) (F : ι → LocalForm L W k K) : LocalForm L W k K :=
  ⟨fun b j q => ∑ i ∈ s, (F i).coef b j q⟩

/-- The evaluation of a finite sum of forms is the sum of the evaluations. -/
theorem eval_sumF {ι : Type*} (s : Finset ι) (F : ι → LocalForm L W k K) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (sumF s F).eval E u M b = ∑ i ∈ s, (F i).eval E u M b := by
  simp only [eval_eq, sumF, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- The coefficients of a finite sum are bounded by `|s| B`. -/
theorem coef_sumF_le {ι : Type*} (s : Finset ι) (F : ι → LocalForm L W k K) {B : ℝ}
    (hF : ∀ i ∈ s, ∀ c j q, ‖(F i).coef c j q‖ ≤ B) (b : Fin k → Z2 L) (j : Fin (K + 1))
    (q : Fin j → Mono L W) : ‖(sumF s F).coef b j q‖ ≤ (s.card : ℝ) * B := by
  simp only [sumF]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ s, ‖(F i).coef b j q‖ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum fun i hi => hF i hi b j q
    _ = (s.card : ℝ) * B := by simp

/-- Multiplication by a deterministic scalar tensor `v_b`: `(v F)_b = v_b F_b`. -/
def tsmulF (v : (Fin k → Z2 L) → ℂ) (F : LocalForm L W k K) : LocalForm L W k K :=
  ⟨fun b j q => v b * F.coef b j q⟩

/-- The evaluation of `tsmulF v F` is `v_b F_b`. -/
theorem eval_tsmulF (v : (Fin k → Z2 L) → ℂ) (F : LocalForm L W k K) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (tsmulF v F).eval E u M b = v b * F.eval E u M b := by
  simp only [eval_eq, tsmulF, Finset.mul_sum, mul_assoc]

/-- The coefficients of `tsmulF v F` are bounded by `B_v B`. -/
theorem coef_tsmulF_le (v : (Fin k → Z2 L) → ℂ) (F : LocalForm L W k K) {B Bv : ℝ}
    (hv : ∀ b, ‖v b‖ ≤ Bv) (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B) (b : Fin k → Z2 L)
    (j : Fin (K + 1)) (q : Fin j → Mono L W) : ‖(tsmulF v F).coef b j q‖ ≤ Bv * B := by
  simp only [tsmulF, norm_mul]
  exact mul_le_mul (hv b) (hF b j q) (norm_nonneg _) ((norm_nonneg _).trans (hv b))

/-- **Blocks are labels**: every entry `(x, y)` of a monomial with non-zero coefficient has the blocks of
`x` and of `y` among the labels `b_m`. -/
def BlkLab (F : LocalForm L W k K) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i,
    (∃ m : Fin k, (splitEquiv L W (q i).1).1 = b m) ∧
      ∃ m : Fin k, (splitEquiv L W (q i).2.1).1 = b m

/-- The zero form has its entries in the blocks of the labels. -/
theorem blkLab_zero : BlkLab (zeroF : LocalForm L W k K) := fun b j q hq => absurd rfl hq

/-- `BlkLab` is stable under sums. -/
theorem blkLab_add {F G : LocalForm L W k K} (hF : BlkLab F) (hG : BlkLab G) :
    BlkLab (addF F G) := by
  intro b j q hq i
  by_cases h : F.coef b j q = 0
  · have : G.coef b j q ≠ 0 := by
      intro h'
      apply hq
      simp [addF, h, h']
    exact hG b j q this i
  · exact hF b j q h i

/-- `BlkLab` is stable under scalar multiples. -/
theorem blkLab_smul {F : LocalForm L W k K} (r : ℂ) (hF : BlkLab F) : BlkLab (smulF r F) := by
  intro b j q hq i
  refine hF b j q (fun h => hq ?_) i
  simp [smulF, h]

/-- `BlkLab` is stable under tensor scalars. -/
theorem blkLab_tsmul {F : LocalForm L W k K} (v : (Fin k → Z2 L) → ℂ) (hF : BlkLab F) :
    BlkLab (tsmulF v F) := by
  intro b j q hq i
  refine hF b j q (fun h => hq ?_) i
  simp [tsmulF, h]

/-- `BlkLab` is stable under finite sums. -/
theorem blkLab_sum {ι : Type*} (s : Finset ι) {F : ι → LocalForm L W k K}
    (hF : ∀ i ∈ s, BlkLab (F i)) : BlkLab (sumF s F) := by
  intro b j q hq i
  simp only [sumF] at hq
  obtain ⟨i₀, hi₀, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  exact hF i₀ hi₀ b j q hne i

/-- `BlkLab` is stable under lifting. -/
theorem blkLab_lift {F : LocalForm L W k K₁} (hF : BlkLab F) : BlkLab (liftF K₂ F) := by
  intro b j q hq i
  simp only [liftF] at hq
  split_ifs at hq with h
  · exact hF b ⟨j.val, h⟩ q hq i
  · exact absurd rfl hq

/-- `BlkLab` is stable under relabelling (the labels of `b ∘ f` are labels of `b`). -/
theorem blkLab_comap {k' : ℕ} (f : Fin k → Fin k') {F : LocalForm L W k K} (hF : BlkLab F) :
    BlkLab (comapF f F) := by
  intro b j q hq i
  obtain ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hF (fun m => b (f m)) j q hq i
  exact ⟨⟨f m₁, h₁⟩, ⟨f m₂, h₂⟩⟩

/-- A constant (degree `0`) form has no entries. -/
theorem blkLab_const {k' K' : ℕ} (v : (Fin k' → Z2 L) → ℂ) :
    BlkLab (constF (K := K') v : LocalForm L W k' K') := by
  intro b j q hq i
  have hj : j.val = 0 := by
    by_contra hne
    have hj' : j ≠ 0 := fun h => hne (by rw [h]; rfl)
    apply hq
    simp [constF, homF, hj']
  exact absurd i.isLt (by omega)

/-- `BlkLab` is stable under products. -/
theorem blkLab_mul {K₁ K₂ : ℕ} {F : LocalForm L W k K₁} {G : LocalForm L W k K₂}
    (hF : BlkLab F) (hG : BlkLab G) : BlkLab (mulF F G) := by
  intro b j q hq i
  simp only [mulF] at hq
  obtain ⟨j₁, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  obtain ⟨j₂, -, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases h : j₁.val + j₂.val = j.val
  · simp only [h, dite_true] at h2
    have hF0 : F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) ≠ 0 := left_ne_zero_of_mul h2
    have hG0 : G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩) ≠ 0 := right_ne_zero_of_mul h2
    by_cases hi : i.val < j₁.val
    · exact hF b j₁ _ hF0 ⟨i.val, hi⟩
    · have hi2 : i.val - j₁.val < j₂.val := by have := i.isLt; omega
      have e : (⟨j₁.val + (i.val - j₁.val), by omega⟩ : Fin j.val) = i := Fin.ext (by
        simp only; omega)
      have := hG b j₂ _ hG0 ⟨i.val - j₁.val, hi2⟩
      simp only [e] at this
      exact this
  · simp [h] at h2

/-- The loop form has its entries in the blocks of its labels (`(p_{i-1}, p_i)` sits in `(c_{i-1}, c_i)`); as in the proof of `loc0_trunc_lkF`. -/
theorem blkLab_loopF {k : ℕ} [NeZero k] (σ : Fin k → Bool) :
    BlkLab (loopF σ : LocalForm L W k k) := by
  intro b j q hq i
  have hj0 : j.val ≠ 0 := fun h0 => absurd i.isLt (by omega)
  have hjk : j.val = k := by
    by_contra hjk
    apply hq
    unfold loopF homF
    simp [hjk]
  unfold loopF homF at hq
  simp only at hq
  split_ifs at hq
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hqp : (fun i : Fin k => q (Fin.cast hjk.symm i)) = qOf σ p := by
    by_contra hne
    exact hp (by simp [hne])
  have hp' : loopW b p ≠ 0 := by
    intro h0
    exact hp (by simp [h0])
  have hblock : ∀ i' : Fin k, (splitEquiv L W (p i')).1 = b i' := by
    intro i'
    unfold loopW at hp'
    have := (Finset.prod_ne_zero_iff.mp hp') i' (Finset.mem_univ _)
    rw [Eblk_apply] at this
    by_contra hne
    apply this
    simp [hne]
  set i' : Fin k := Fin.cast hjk i with hi'
  have hqi : q i = qOf σ p i' := by
    have := congrFun hqp i'
    simpa [hi'] using this
  refine ⟨⟨prvK k i', ?_⟩, ⟨i', ?_⟩⟩
  · rw [hqi]; exact hblock _
  · rw [hqi]; exact hblock _

/-- The form `𝓛 - 𝒦` has its entries in the blocks of its labels. -/
theorem blkLab_lkF {k : ℕ} [NeZero k] (σ : Fin k → Bool) (E u : ℝ) :
    BlkLab (lkF σ E u : LocalForm L W k k) :=
  blkLab_add (blkLab_loopF σ) (blkLab_smul _ (blkLab_const _))

/-- After truncation to `maxDist b < ρ`, a form whose entries lie in blocks that are labels is local
around the first label with radius `2ρ`. -/
theorem loc0_truncF_of_blk [NeZero k] {ρ : ℝ} {F : LocalForm L W k K} (hF : BlkLab F) :
    Loc0 (2 * ρ) (truncF ρ F) := by
  intro b j q hq i
  simp only [truncF] at hq
  by_cases hb : (KLoop.maxDist L b : ℝ) < ρ
  · simp only [hb, ↓reduceIte] at hq
    obtain ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hF b j q hq i
    have m1 := zdist2_le_maxDist b m₁ 0
    have m2 := zdist2_le_maxDist b m₂ 0
    have m1' : (zdist2 L (b m₁ - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by exact_mod_cast m1
    have m2' : (zdist2 L (b m₂ - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by exact_mod_cast m2
    rw [h₁, h₂]
    push_cast
    linarith
  · simp only [hb, ↓reduceIte] at hq
    exact absurd rfl hq

end Algebra

/-! ## 3. Tensors with a local form (`Fac`) and their pieces -/

section FacSec

variable (d : Sizes)

/-- A random `kk`-tensor `T_n(ω)` together with a deterministic local form `F_n` that evaluates to it
at the flow matrix `H_{u_n}(ω)` (`eval_eq`), whose entries lie in the blocks of the labels (`blk`). -/
structure Fac (E u : ℕ → ℝ) (kk K : ℕ) where
  F : ∀ n, LocalForm (d.L n) (d.W n) kk K
  T : ∀ n, Sizes.SeqΩ d → (Fin kk → Z2 (d.L n)) → ℂ
  eval_eq : ∀ n ω z, (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) z = T n ω z
  blk : ∀ n, BlkLab (F n)

namespace Fac

variable {d} {E u : ℕ → ℝ} {kk : ℕ}

/-- The product of two tensors (degrees add). -/
def mul {K₁ K₂ : ℕ} (x : Fac d E u kk K₁) (y : Fac d E u kk K₂) : Fac d E u kk (K₁ + K₂) where
  F n := mulF (x.F n) (y.F n)
  T n ω z := x.T n ω z * y.T n ω z
  eval_eq n ω z := by rw [eval_mulF, x.eval_eq, y.eval_eq]
  blk n := blkLab_mul (x.blk n) (y.blk n)

/-- Multiplication by a deterministic scalar tensor. -/
def tsmul {K : ℕ} (v : ∀ n, (Fin kk → Z2 (d.L n)) → ℂ) (x : Fac d E u kk K) : Fac d E u kk K where
  F n := tsmulF (v n) (x.F n)
  T n ω z := v n z * x.T n ω z
  eval_eq n ω z := by rw [eval_tsmulF, x.eval_eq]
  blk n := blkLab_tsmul (v n) (x.blk n)

/-- A finite sum of tensors of the same degree. -/
def sum {ι : Type*} {K : ℕ} (s : Finset ι) (x : ι → Fac d E u kk K) : Fac d E u kk K where
  F n := sumF s (fun i => (x i).F n)
  T n ω z := ∑ i ∈ s, (x i).T n ω z
  eval_eq n ω z := by
    rw [eval_sumF]
    exact Finset.sum_congr rfl fun i _ => (x i).eval_eq n ω z
  blk n := blkLab_sum s (fun i _ => (x i).blk n)

/-- The sum of two tensors of the same degree. -/
def add {K : ℕ} (x y : Fac d E u kk K) : Fac d E u kk K where
  F n := addF (x.F n) (y.F n)
  T n ω z := x.T n ω z + y.T n ω z
  eval_eq n ω z := by rw [eval_addF, x.eval_eq, y.eval_eq]
  blk n := blkLab_add (x.blk n) (y.blk n)

/-- The piece `𝓛 - 𝒦` (`lkTensor`) of length `m + 1` on the labels `z ∘ f`. -/
def lk {m K : ℕ} (hm : m + 1 ≤ K) (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) :
    Fac d E u kk K where
  F n := liftF K (comapF f (lkF (σ n) (E n) (u n)))
  T n ω z := lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n)
    (fun i => z (f i))
  eval_eq n ω z := by rw [eval_liftF hm, eval_comapF, eval_lkF]
  blk n := blkLab_lift (blkLab_comap f (blkLab_lkF _ _ _))

/-- The piece `𝒦` (the primitive loop, a constant form) of length `m + 1` on the labels `z ∘ f`. -/
def kcal {m K : ℕ} (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) : Fac d E u kk K where
  F n := constF (fun z => KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => z (f i))))
  T n _ z := KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => z (f i)))
  eval_eq n ω z := eval_constF _ _ _ _ _
  blk n := blkLab_const _

/-- The piece `𝓛` (`LLf`, the loop trace) of length `m + 1` on the labels `z ∘ f`. -/
def loop {m K : ℕ} (hm : m + 1 ≤ K) (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) :
    Fac d E u kk K where
  F n := liftF K (comapF f (loopF (σ n)))
  T n ω z := LLf (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (loopOf (σ n) (fun i => z (f i)))
  eval_eq n ω z := by rw [eval_liftF hm, eval_comapF, eval_loopF]; rfl
  blk n := blkLab_lift (blkLab_comap f (blkLab_loopF _))

end Fac

end FacSec

/-! ## 4. Deterministic size bounds -/

section Key

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The deterministic facts at one size `n`, with `Nr = N`, for tensors of length `≤ kmax`. -/
structure KeyAt (L W : ℕ) [NeZero L] [NeZero W] (E u Nr : ℝ) (kmax : ℕ) : Prop where
  hL : 3 ≤ L
  hW : 1 ≤ W
  hN1 : 1 ≤ Nr
  hLN : (L : ℝ) ^ 2 ≤ Nr
  hNLW : (((L * W) ^ 2 : ℕ) : ℝ) ≤ Nr
  hη : (etaT E u)⁻¹ ≤ Nr
  hE : |E| < 2
  hu0 : 0 ≤ u
  hu1 : u < 1
  hKc : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ kmax →
    ‖KLoop.Kcal L W E u J‖ ≤ Nr * (etaT E u)⁻¹ ^ kmax

private theorem norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

namespace KeyAt

variable {E u Nr : ℝ} {kmax : ℕ}

theorem eta_pos (h : KeyAt L W E u Nr kmax) : 0 < etaT E u := etaT_pos h.hE h.hu1

theorem N_pos (h : KeyAt L W E u Nr kmax) : 0 < Nr := lt_of_lt_of_le one_pos h.hN1

/-- `|𝒦_J| ≤ N^{kmax+1}` for loops of length `1 ≤ |J| ≤ kmax`. -/
theorem norm_kcal_le (h : KeyAt L W E u Nr kmax) (J : LoopIdx (Z2 L)) (h1 : 1 ≤ J.length)
    (hkm : J.length ≤ kmax) (hwf : J.WF) : ‖KLoop.Kcal L W E u J‖ ≤ Nr ^ (kmax + 1) := by
  by_cases h1' : J.length = 1
  · have e : KLoop.Kcal L W E u J = KLoop.mSig E (J.σ.getD 0 false) := by
      simp [KLoop.Kcal, KLoop.Kgen, h1']
    rw [e, norm_mSig (by have := h.hE; rw [abs_lt] at this; rw [abs_le]; constructor <;> linarith)]
    exact one_le_pow₀ h.hN1
  · have h2 : 2 ≤ J.length := by omega
    refine (h.hKc J hwf h2 hkm).trans ?_
    have hpow : (etaT E u)⁻¹ ^ kmax ≤ Nr ^ kmax :=
      pow_le_pow_left₀ (inv_nonneg.2 h.eta_pos.le) h.hη kmax
    calc Nr * (etaT E u)⁻¹ ^ kmax ≤ Nr * Nr ^ kmax :=
          mul_le_mul_of_nonneg_left hpow h.N_pos.le
      _ = Nr ^ (kmax + 1) := by ring

/-- `|𝓛_{σ,c}| ≤ N^{kmax+1}` for a Hermitian `M` and `len ≤ kmax`; compare `norm_lkTensor_le` in `LocalFormCalc`. -/
theorem norm_loop_le (h : KeyAt L W E u Nr kmax) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {len : ℕ} (σ : Fin len → Bool) (c : Fin len → Z2 L)
    (hlen : len ≤ kmax) : ‖LLf L W E u M (loopOf σ c)‖ ≤ Nr ^ (kmax + 1) := by
  have hηpos := h.eta_pos
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_nonneg]
    · rfl
    · exact hηpos.le
  have hHerm : (blockMat M).IsHermitian := hM.submatrix _
  have hwf : (loopOf σ c).WF := by simp [loopOf, LoopIdx.WF]
  have hg := norm_gloop_le_crude L W hHerm hηpos hz (loopOf σ c) hwf
  have hl : (loopOf σ c).a.length = len := by simp [loopOf]
  rw [hl] at hg
  have hW1 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ W := by exact_mod_cast h.hW
    have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith
  have hpow : (etaT E u)⁻¹ ^ len ≤ Nr ^ kmax :=
    (pow_le_pow_left₀ (inv_nonneg.2 hηpos.le) h.hη len).trans (pow_le_pow_right₀ h.hN1 hlen)
  unfold LLf
  refine hg.trans ?_
  have h1 : (etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2 ≤ (etaT E u)⁻¹ :=
    mul_le_of_le_one_right (inv_nonneg.2 hηpos.le) hW1
  have h2 : ((etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2) ^ len ≤ ((etaT E u)⁻¹) ^ len :=
    pow_le_pow_left₀ (by positivity) h1 len
  calc _ ≤ Nr * ((etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2) ^ len :=
        mul_le_mul_of_nonneg_right h.hNLW (by positivity)
    _ ≤ Nr * Nr ^ kmax := mul_le_mul_of_nonneg_left (h2.trans hpow) h.N_pos.le
    _ = Nr ^ (kmax + 1) := by ring

/-- `|(𝓛-𝒦)_{σ,c}| ≤ 2 N^{kmax+1}` for a Hermitian `M` and `1 ≤ len ≤ kmax`. -/
theorem norm_lk_le (h : KeyAt L W E u Nr kmax) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) {len : ℕ} (σ : Fin len → Bool) (c : Fin len → Z2 L) (h1 : 1 ≤ len)
    (hlen : len ≤ kmax) : ‖lkTensor L W E u M σ c‖ ≤ 2 * Nr ^ (kmax + 1) := by
  have hwf : (loopOf σ c).WF := by simp [loopOf, LoopIdx.WF]
  have hl : (loopOf σ c).length = len := by simp [loopOf, LoopIdx.length]
  have hk := h.norm_kcal_le (loopOf σ c) (by omega) (by omega) hwf
  have hg := h.norm_loop_le hM σ c hlen
  unfold lkTensor LKf
  refine (norm_sub_le _ _).trans ?_
  linarith

end KeyAt

end Key

/-! ## 5. The tensor `𝓛-𝒦` at one label, and the geometry of a cut -/

section Avg

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `tr E_a = 1` (a block has `W²` sites of weight `W⁻²`). -/
theorem trace_Eblk (a : Z2 L) : Matrix.trace (Eblk L W a) = 1 := by
  have h := Green.sum_blkCoef2 (L := L) (W := W) a
  have h' : ((∑ k, Green.blkCoef2 L W a k : ℝ) : ℂ) = 1 := by rw [h]; simp
  rw [Complex.ofReal_sum] at h'
  rw [← h', Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Eblk, Matrix.diagonal_apply_eq, Green.blkCoef2]
  split_ifs <;> simp

/-- **`avgErr` is a one-loop `𝓛-𝒦`**: `⟨(G_σ - m(σ)) E_a⟩ = (𝓛-𝒦)_{u,(σ),(a)}` (`𝒦` of a loop of
length `1` is `m(σ)`), so the factor `avgErr` of `𝓔^{(G̃)}` is a local form of degree `≤ 1`. -/
theorem avgErr_eq_lk (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (a : Z2 L) :
    avgErr L W E u M s a = lkTensor L W E u M (fun _ : Fin 1 => s) (fun _ => a) := by
  have hK : KLoop.Kcal L W E u (loopOf (fun _ : Fin 1 => s) (fun _ => a)) = KLoop.mSig E s := by
    simp [KLoop.Kcal, KLoop.Kgen, loopOf, LoopIdx.length]
  have hg : gloop L W (blockMat M) (spectralZ E u) (loopOf (fun _ : Fin 1 => s) (fun _ => a)) =
      Matrix.trace (Gsig (blockMat M) (spectralZ E u) s * Eblk L W a) := by
    simp [gloop, loopOf]
  unfold avgErr lkTensor LKf LLf greenBlk
  rw [hK, hg, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_Eblk, smul_eq_mul, mul_one]

end Avg

section Geometry

variable {L : ℕ} [NeZero L]

/-- Two groups of labels covering all labels, joined by a pair of labels at distance `≤ 1` (one in each
group): `maxDist z ≤ maxDist zA + maxDist zB + 1`. -/
theorem maxDist_le_add {kk la lb : ℕ} (z : Fin kk → Z2 L) (fA : Fin la → Fin kk)
    (fB : Fin lb → Fin kk) {ia ib : Fin kk} (hia : ∃ i, fA i = ia) (hib : ∃ i, fB i = ib)
    (hadj : zdist2 L (z ia - z ib) ≤ 1)
    (hcov : ∀ j : Fin kk, (∃ i, fA i = j) ∨ (∃ i, fB i = j)) :
    KLoop.maxDist L z ≤
      KLoop.maxDist L (fun i => z (fA i)) + KLoop.maxDist L (fun i => z (fB i)) + 1 := by
  obtain ⟨ia', rfl⟩ := hia
  obtain ⟨ib', rfl⟩ := hib
  have hA : ∀ a b : Fin la, zdist2 L (z (fA a) - z (fA b)) ≤ KLoop.maxDist L (fun i => z (fA i)) :=
    fun a b => zdist2_le_maxDist (fun i => z (fA i)) a b
  have hB : ∀ a b : Fin lb, zdist2 L (z (fB a) - z (fB b)) ≤ KLoop.maxDist L (fun i => z (fB i)) :=
    fun a b => zdist2_le_maxDist (fun i => z (fB i)) a b
  have cross : ∀ (a : Fin la) (b : Fin lb), zdist2 L (z (fA a) - z (fB b)) ≤
      KLoop.maxDist L (fun i => z (fA i)) + KLoop.maxDist L (fun i => z (fB i)) + 1 := by
    intro a b
    have t1 := zdist2_sub_le L (z (fA a)) (z (fA ia')) (z (fB b))
    have t2 := zdist2_sub_le L (z (fA ia')) (z (fB ib')) (z (fB b))
    have h1 := hA a ia'
    have h2 := hB ib' b
    omega
  have key : ∀ i j : Fin kk, zdist2 L (z i - z j) ≤
      KLoop.maxDist L (fun i => z (fA i)) + KLoop.maxDist L (fun i => z (fB i)) + 1 := by
    intro i j
    rcases hcov i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;> rcases hcov j with ⟨a', rfl⟩ | ⟨b', rfl⟩
    · have := hA a a'
      omega
    · exact cross a b'
    · rw [zdist2_symm]
      exact cross a' b
    · have := hB b b'
      omega
  exact Finset.sup_le fun p _ => key p.1 p.2

/-- One of the two groups has `maxDist ≥ r` if `maxDist z ≥ ρ`, `r ≤ ρ/4`, `ρ ≥ 2`. -/
theorem far_of_sum {ρ r : ℝ} {mA mB mz : ℕ} (hρ : 2 ≤ ρ) (hr : r ≤ ρ / 4) (hfar : ρ ≤ (mz : ℝ))
    (hb : mz ≤ mA + mB + 1) : r ≤ (mA : ℝ) ∨ r ≤ (mB : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hb' : (mz : ℝ) ≤ (mA : ℝ) + (mB : ℝ) + 1 := by exact_mod_cast hb
  linarith [hcon.1, hcon.2]

/-- The label positions of `𝒢^{L}` and `𝒢^{R}` cover all labels of `z = (c, a', b')`. -/
theorem cover_LR {n k' l' : ℕ} (hk : 1 ≤ k') (hkl : k' < l') (hl : l' ≤ n) (j : Fin (n + 2)) :
    (∃ i, fL n k' l' i = j) ∨ (∃ i, fR n k' l' i = j) := by
  have hj := j.isLt
  by_cases h1 : j.val < k' - 1
  · left
    refine ⟨⟨j.val, by omega⟩, Fin.ext ?_⟩
    simp only [fL]
    split_ifs <;> omega
  by_cases h2 : j.val = n
  · left
    refine ⟨⟨k' - 1, by omega⟩, Fin.ext ?_⟩
    simp only [fL]
    split_ifs <;> omega
  by_cases h3 : j.val = n + 1
  · right
    refine ⟨⟨l' - k', by omega⟩, Fin.ext ?_⟩
    simp only [fR]
    split_ifs <;> omega
  by_cases h4 : j.val < l' - 1
  · right
    refine ⟨⟨j.val - (k' - 1), by omega⟩, Fin.ext ?_⟩
    simp only [fR]
    split_ifs <;> omega
  · left
    refine ⟨⟨k' + (j.val - (l' - 1)), by omega⟩, Fin.ext ?_⟩
    simp only [fL]
    split_ifs <;> omega

/-- The label `a' = z_n` is a label of the left piece. -/
theorem exists_fL_a {n k' l' : ℕ} (hk : 1 ≤ k') (hkl : k' < l') (hl : l' ≤ n) :
    ∃ i, fL n k' l' i = Fin.natAdd n 0 := by
  refine ⟨⟨k' - 1, by omega⟩, Fin.ext ?_⟩
  simp only [fL]
  split_ifs <;> simp <;> omega

/-- The label `b' = z_{n+1}` is a label of the right piece. -/
theorem exists_fR_b {n k' l' : ℕ} (hk : 1 ≤ k') (hkl : k' < l') (hl : l' ≤ n) :
    ∃ i, fR n k' l' i = Fin.natAdd n 1 := by
  refine ⟨⟨l' - k', by omega⟩, Fin.ext ?_⟩
  simp only [fR]
  split_ifs <;> simp <;> omega

/-- The single position `a' = z_n`. -/
def fA (n : ℕ) : Fin 1 → Fin (n + 2) := fun _ => Fin.natAdd n 0

/-- The label positions of `fA` and of `f3` cover all labels of `z = (c, a', b')`. -/
theorem cover_A3 {n k' : ℕ} (hk : 1 ≤ k') (hkn : k' ≤ n) (j : Fin (n + 2)) :
    (∃ i, fA n i = j) ∨ (∃ i, f3 n k' i = j) := by
  have hj := j.isLt
  by_cases h2 : j.val = n
  · left
    refine ⟨0, Fin.ext ?_⟩
    simp [fA, h2]
  by_cases h1 : j.val < k' - 1
  · right
    refine ⟨⟨j.val, by omega⟩, Fin.ext ?_⟩
    simp only [f3]
    split_ifs <;> omega
  by_cases h3 : j.val = n + 1
  · right
    refine ⟨⟨k' - 1, by omega⟩, Fin.ext ?_⟩
    simp only [f3]
    split_ifs <;> omega
  · right
    refine ⟨⟨j.val + 1, by omega⟩, Fin.ext ?_⟩
    simp only [f3]
    split_ifs <;> omega

/-- The label `a' = z_n` is the label of `fA`. -/
theorem exists_fA_a {n : ℕ} : ∃ i, fA n i = Fin.natAdd n 0 := ⟨0, rfl⟩

/-- The label `b' = z_{n+1}` is a label of the single-cut loop. -/
theorem exists_f3_b {n k' : ℕ} (hk : 1 ≤ k') (hkn : k' ≤ n) : ∃ i, f3 n k' i = Fin.natAdd n 1 := by
  refine ⟨⟨k' - 1, by omega⟩, Fin.ext ?_⟩
  simp only [f3]
  split_ifs <;> simp <;> omega

end Geometry

/-! ## 6. The far part of the tensors (`≺`-calculus) -/

section Stoch

variable (d : Sizes)

/-- `≺` is stable under a finite sum of dominated quantities (the number of terms is absorbed by
`size^{τ-τ'}`). -/
theorem perTimeDomAt_sum_le {U : ℕ → Type*} {ι : Type*} (hsize : SizeTendsto d) (s : Finset ι)
    {ξ : ι → ∀ n, U n → Sizes.SeqΩ d → ℝ} {Ξ : ∀ n, U n → Sizes.SeqΩ d → ℝ} {D : ℝ}
    (h : ∀ i ∈ s, PerTimeDomAt (Sizes.seqP d) d.size (ξ i) (fun n _ _ => (d.W n : ℝ) ^ (-D)))
    (hle : ∀ᶠ n : ℕ in atTop, ∀ p ω, Ξ n p ω ≤ ∑ i ∈ s, ξ i n p ω) :
    PerTimeDomAt (Sizes.seqP d) d.size Ξ (fun n _ _ => (d.W n : ℝ) ^ (-D)) := by
  have hsize' : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have h1 := PerTimeCalc.PerTime.finset_sum_of hsize' s
    (ζ := fun (_ : ι) n (_ : U n) (_ : Sizes.SeqΩ d) => (d.W n : ℝ) ^ (-D)) h
  have h2 := PerTimeCalc.PerTime.perTimeCalc_mono hsize'
    (ζ' := fun n (_ : U n) (_ : Sizes.SeqΩ d) => (d.W n : ℝ) ^ (-D))
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (s.card : ℝ)
    (Filter.Eventually.of_forall fun n u ω => by simp) h1
  exact PerTimeCalc.PerTime.stochDom_of_le_left_eventually hle h2

/-- `‖X_z‖ 1(ρ ≤ maxDist z) ≺ W^{-D}`, per time and label `z`. -/
def FarPT {kk : ℕ} (X : ∀ n, Sizes.SeqΩ d → (Fin kk → Z2 (d.L n)) → ℂ) (ρ : ℕ → ℝ) (D : ℝ) :
    Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin kk → Z2 (d.L n)))
    (fun n p ω => ‖X n ω p.2‖ * (if ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
    (fun n _ _ => (d.W n : ℝ) ^ (-D))

/-- `‖X_z‖ 1(r ≤ maxDist (z ∘ f)) ≺ W^{-D}`: the far part of a piece on the labels `z ∘ f`. -/
def FarPieceAt {kk lx : ℕ} (X : ∀ n, Sizes.SeqΩ d → (Fin kk → Z2 (d.L n)) → ℂ) (r : ℕ → ℝ)
    (f : Fin lx → Fin kk) (D : ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin kk → Z2 (d.L n)))
    (fun n p ω => ‖X n ω p.2‖ *
      (if r n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (f i)) : ℝ) then 1 else 0))
    (fun n _ _ => (d.W n : ℝ) ^ (-D))

/-- `≺` is stable under a sum of two dominated quantities. -/
theorem perTimeDomAt_add_le {U : ℕ → Type*} (hsize : SizeTendsto d)
    {ξ₁ ξ₂ Ξ : ∀ n, U n → Sizes.SeqΩ d → ℝ} {D : ℝ}
    (h₁ : PerTimeDomAt (Sizes.seqP d) d.size ξ₁ (fun n _ _ => (d.W n : ℝ) ^ (-D)))
    (h₂ : PerTimeDomAt (Sizes.seqP d) d.size ξ₂ (fun n _ _ => (d.W n : ℝ) ^ (-D)))
    (hle : ∀ᶠ n : ℕ in atTop, ∀ p ω, Ξ n p ω ≤ ξ₁ n p ω + ξ₂ n p ω) :
    PerTimeDomAt (Sizes.seqP d) d.size Ξ (fun n _ _ => (d.W n : ℝ) ^ (-D)) := by
  have hsize' : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have h1 := PerTimeCalc.PerTime.perTimeCalc_add hsize' h₁ h₂
  have h2 := PerTimeCalc.PerTime.perTimeCalc_mono hsize'
    (ζ' := fun n (_ : U n) (_ : Sizes.SeqΩ d) => (d.W n : ℝ) ^ (-D))
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) 2
    (Filter.Eventually.of_forall fun n u ω => by beta_reduce; linarith) h1
  exact PerTimeCalc.PerTime.stochDom_of_le_left_eventually hle h2

/-- The far part of a finite sum of tensors. -/
theorem farPT_sum {ι : Type*} (hsize : SizeTendsto d) (s : Finset ι) {kk K : ℕ} {E u : ℕ → ℝ}
    (x : ι → Fac d E u kk K) (ρ : ℕ → ℝ) {D : ℝ} (h : ∀ i ∈ s, FarPT d (x i).T ρ D) :
    FarPT d (Fac.sum s x).T ρ D := by
  refine perTimeDomAt_sum_le d hsize s (U := fun n => Unit × (Fin kk → Z2 (d.L n)))
    (ξ := fun i n p ω => ‖(x i).T n ω p.2‖ * (if ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
    h (Filter.Eventually.of_forall fun n p ω => ?_)
  simp only [Fac.sum, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by split_ifs <;> norm_num)

/-- The far part of a sum of two tensors. -/
theorem farPT_add (hsize : SizeTendsto d) {kk K : ℕ} {E u : ℕ → ℝ} (x y : Fac d E u kk K)
    (ρ : ℕ → ℝ) {D : ℝ} (hx : FarPT d x.T ρ D) (hy : FarPT d y.T ρ D) :
    FarPT d (Fac.add x y).T ρ D := by
  refine perTimeDomAt_add_le d hsize (U := fun n => Unit × (Fin kk → Z2 (d.L n))) hx hy
    (Filter.Eventually.of_forall fun n p ω => ?_)
  simp only [Fac.add]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by split_ifs <;> norm_num)

/-- **The far part of a product `1(|a'-b'| ≤ 1) x y`** (`x, y` bounded by `N^a`).  If the geometry
forces one factor to be far on its own labels (`hgeo`), then `‖adj x y‖ 1(ρ ≤ maxDist z) ≺ W^{-(D - a/c)}`
(`errTransport` with `η = ‖x‖ 1(far_x) + ‖y‖ 1(far_y)`, `γ = 0`). -/
theorem farPT_prod {c a D : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hband : Bandwidth d c)
    (hsize : SizeTendsto d) {kk K₁ K₂ lx ly : ℕ} {E u : ℕ → ℝ} (x : Fac d E u kk K₁)
    (y : Fac d E u kk K₂) (adj : ∀ n, (Fin kk → Z2 (d.L n)) → ℂ) (ρ rx ry : ℕ → ℝ)
    (fx : Fin lx → Fin kk) (fy : Fin ly → Fin kk) (G : ℕ → Prop) (hG : ∀ᶠ n : ℕ in atTop, G n)
    (hgeo : ∀ n, G n → ∀ z : Fin kk → Z2 (d.L n), adj n z ≠ 0 →
      ρ n ≤ (KLoop.maxDist (d.L n) z : ℝ) →
      rx n ≤ (KLoop.maxDist (d.L n) (fun i => z (fx i)) : ℝ) ∨
      ry n ≤ (KLoop.maxDist (d.L n) (fun i => z (fy i)) : ℝ))
    (hadj : ∀ n z, ‖adj n z‖ ≤ 1)
    (hsx : ∀ n, G n → ∀ ω z, ‖x.T n ω z‖ ≤ ((d.size n : ℕ) : ℝ) ^ a)
    (hsy : ∀ n, G n → ∀ ω z, ‖y.T n ω z‖ ≤ ((d.size n : ℕ) : ℝ) ^ a)
    (hx : FarPieceAt d x.T rx fx D) (hy : FarPieceAt d y.T ry fy D) :
    FarPT d (Fac.tsmul adj (Fac.mul x y)).T ρ (D - a / c) := by
  have hη : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin kk → Z2 (d.L n)))
      (fun n p ω => ‖x.T n ω p.2‖ *
          (if rx n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fx i)) : ℝ) then 1 else 0) +
        ‖y.T n ω p.2‖ *
          (if ry n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fy i)) : ℝ) then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-D)) :=
    perTimeDomAt_add_le d hsize hx hy (Filter.Eventually.of_forall fun n p ω => le_rfl)
  refine errTransport d (C := a) (D := D) hc ha hband hsize (γ := fun _ => 0)
    (fun n p ω => by positivity) hη
    (Filter.Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [hG] with n hn p ω
  have hN0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxn := hsx n hn ω p.2
  have hyn := hsy n hn ω p.2
  have hα := hadj n p.2
  have hx0 := norm_nonneg (x.T n ω p.2)
  have hy0 := norm_nonneg (y.T n ω p.2)
  have hα0 := norm_nonneg (adj n p.2)
  simp only [Fac.tsmul, Fac.mul, norm_mul, zero_add]
  by_cases hfar : ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
  · simp only [hfar, ↓reduceIte, mul_one]
    by_cases hadjz : adj n p.2 = 0
    · simp only [hadjz, norm_zero, zero_mul]
      positivity
    · rcases hgeo n hn p.2 hadjz hfar with h | h
      · simp only [h, ↓reduceIte, mul_one]
        have hyi : 0 ≤ ‖y.T n ω p.2‖ * (if ry n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fy i)) : ℝ)
            then 1 else 0) := by positivity
        calc ‖adj n p.2‖ * (‖x.T n ω p.2‖ * ‖y.T n ω p.2‖)
            ≤ 1 * (‖x.T n ω p.2‖ * ((d.size n : ℕ) : ℝ) ^ a) := by
              refine mul_le_mul hα (mul_le_mul_of_nonneg_left hyn hx0) (by positivity) zero_le_one
          _ ≤ ((d.size n : ℕ) : ℝ) ^ a * (‖x.T n ω p.2‖ +
                ‖y.T n ω p.2‖ * (if ry n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fy i)) : ℝ)
                  then 1 else 0)) := by nlinarith
      · simp only [h, ↓reduceIte, mul_one]
        have hxi : 0 ≤ ‖x.T n ω p.2‖ * (if rx n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fx i)) : ℝ)
            then 1 else 0) := by positivity
        calc ‖adj n p.2‖ * (‖x.T n ω p.2‖ * ‖y.T n ω p.2‖)
            ≤ 1 * (((d.size n : ℕ) : ℝ) ^ a * ‖y.T n ω p.2‖) := by
              refine mul_le_mul hα (mul_le_mul_of_nonneg_right hxn hy0) (by positivity) zero_le_one
          _ ≤ ((d.size n : ℕ) : ℝ) ^ a * (‖x.T n ω p.2‖ *
                (if rx n ≤ (KLoop.maxDist (d.L n) (fun i => p.2 (fx i)) : ℝ) then 1 else 0) +
                ‖y.T n ω p.2‖) := by nlinarith
  · simp only [hfar, ↓reduceIte, mul_zero]
    positivity

/-- **`DecayLoopPT` for the piece `𝓛-𝒦` on the labels `z ∘ f`** (`res_decayLK`): the piece is
`≺ W^{-D}` where its own labels are `ℓ_u W^{τ'}` apart. -/
theorem farPiece_lk {E s t : ℕ → ℝ} (hdl : DecayLoopPT d E s t) {u : ℕ → ℝ}
    (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) {kk m K : ℕ} (hm : m + 1 ≤ K)
    (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    FarPieceAt d (Fac.lk (d := d) (E := E) (u := u) hm σ f).T
      (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ') f D := by
  intro τ'' hτ'' D₁ hD₁
  have h1 := hdl (m + 1) (by omega) τ' hτ' D hD τ'' hτ'' D₁ hD₁
  filter_upwards [h1] with n h1n p
  refine le_trans (measure_mono ?_) (h1n (⟨u n, ⟨hu n, hut n⟩⟩, σ n, fun i => p.2 (f i)))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤
      (KLoop.maxDist (d.L n) (fun i => p.2 (f i)) : ℝ)
  · simp only [Fac.lk, hfar, ↓reduceIte, mul_one]
    have : ‖lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n)
        (fun i => p.2 (f i))‖ =
        lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n)
          (fun i => p.2 (f i)) := rfl
    rw [this]
    have := norm_nonneg (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω))
      (spectralZ (E n) (u n)) (loopOf (σ n) (fun i => p.2 (f i))))
    unfold loopAbs
    linarith
  · simp [hfar]

/-- **`DecayLoopPT` for the piece `𝓛` (the loop) on the labels `z ∘ f`** (`loopAbs` part). -/
theorem farPiece_loop {E s t : ℕ → ℝ} (hdl : DecayLoopPT d E s t) {u : ℕ → ℝ}
    (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) {kk m K : ℕ} (hm : m + 1 ≤ K)
    (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    FarPieceAt d (Fac.loop (d := d) (E := E) (u := u) hm σ f).T
      (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ') f D := by
  intro τ'' hτ'' D₁ hD₁
  have h1 := hdl (m + 1) (by omega) τ' hτ' D hD τ'' hτ'' D₁ hD₁
  filter_upwards [h1] with n h1n p
  refine le_trans (measure_mono ?_) (h1n (⟨u n, ⟨hu n, hut n⟩⟩, σ n, fun i => p.2 (f i)))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤
      (KLoop.maxDist (d.L n) (fun i => p.2 (f i)) : ℝ)
  · simp only [Fac.loop, hfar, ↓reduceIte, mul_one]
    have : ‖LLf (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
        (loopOf (σ n) (fun i => p.2 (f i)))‖ =
        loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n)
          (fun i => p.2 (f i)) := rfl
    rw [this]
    have := norm_nonneg (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω))
      (spectralZ (E n) (u n)) (loopOf (σ n) (fun i => p.2 (f i)) : LoopIdx (Z2 (d.L n))) -
      KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => p.2 (f i))))
    unfold lkGen
    linarith
  · simp [hfar]

/-- **`KcalDecay` for the piece `𝒦` on the labels `z ∘ f`**: deterministic, `≤ W^{-D}` eventually
where its own labels are `ℓ_u W^{τ'}` apart. -/
theorem farPiece_kcal {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KcalDecay κ) {u : ℕ → ℝ} (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) {kk m K : ℕ}
    (σ : ∀ n : ℕ, Fin (m + 1) → Bool) (f : Fin (m + 1) → Fin kk) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    FarPieceAt d (Fac.kcal (d := d) (E := E) (u := u) (K := K) σ f).T
      (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ') f D := by
  have h := kcalTruncErr d hmain hK (k := m + 1) (by omega) hτ' hD u σ hu hut
  refine perTimeDomAt_of_le d (fun n p ω => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
  filter_upwards [h] with n hn p ω
  by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤
      (KLoop.maxDist (d.L n) (fun i => p.2 (f i)) : ℝ)
  · simp only [Fac.kcal, hfar, ↓reduceIte, mul_one]
    exact hn _ hfar
  · simp only [hfar, ↓reduceIte, mul_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end Stoch

/-! ## 7. The cut kernel and the deterministic part of the assembly -/

section Kernel

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ}

/-- The kernel of the cut sums: `𝔎_{a,z} = W² cutKer S^{(B)}_{a,z}` (`z = (a, a', b')`). -/
def cutKerW (L W : ℕ) {k : ℕ} (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L) : ℂ :=
  (W : ℂ) ^ 2 * cutKer (fun a b => SB L a b) a z

/-- The entries of `S^{(B)}` are `≤ 1`. -/
theorem norm_SB_le_one (hL : 3 ≤ L) (a b : Z2 L) : ‖SB L a b‖ ≤ 1 :=
  (Finset.single_le_sum (f := fun b => ‖SB L a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans (sum_norm_SB_row_real hL a).le

/-- **The cut sum as a kernel**: `Σ_z 𝔎_{c,z} Z_z = W² Σ_{a',b'} S_{a'b'} Z(c, a', b')`. -/
theorem sum_cutKerW [NeZero k] (Z : (Fin (k + 2) → Z2 L) → ℂ) (c : Fin k → Z2 L) :
    ∑ z, cutKerW L W c z * Z z = (W : ℂ) ^ 2 * ∑ a, ∑ b, SB L a b * Z (Fin.append c ![a, b]) := by
  have h := sum_cutKer (L := L) (k := k) (fun a b => SB L a b) Z c
  unfold cutKerW
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h]

/-- The hypotheses of the assembly for the kernel `𝔎 = W² cutKer S^{(B)}`: `K1` (`≤ W²`), `K2'` and `K3'`
with `δ = 0`. -/
theorem cutKerW_hyps [NeZero k] (hL : 3 ≤ L) {Nr ρ : ℝ} (hWN : (W : ℝ) ^ 2 ≤ Nr) (hρ : 0 < ρ) :
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ‖cutKerW L W a z‖ ≤ Nr) ∧
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ρ ≤ (zdist2 L (z 0 - a 0) : ℝ) →
      (KLoop.maxDist L z : ℝ) < ρ → ‖cutKerW L W a z‖ ≤ 0) ∧
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ρ ≤ (KLoop.maxDist L a : ℝ) →
      (KLoop.maxDist L z : ℝ) < ρ → ‖cutKerW L W a z‖ ≤ 0) := by
  obtain ⟨h1, h2, h3⟩ := cutKer_hyps (k := k) (fun a b => SB L a b) (B_S := 1) (ρ := ρ) (norm_SB_le_one hL)
    zero_le_one hρ
  have hn : ∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L),
      ‖cutKerW L W a z‖ = (W : ℝ) ^ 2 * ‖cutKer (fun a b => SB L a b) a z‖ := by
    intro a z
    unfold cutKerW
    rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine ⟨fun a z => ?_, fun a z h h' => ?_, fun a z h h' => ?_⟩
  · rw [hn]
    calc (W : ℝ) ^ 2 * ‖cutKer (fun a b => SB L a b) a z‖ ≤ (W : ℝ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (h1 a z) (by positivity)
      _ ≤ Nr := by linarith
  · rw [hn]
    have := h2 a z h h'
    have h0 : ‖cutKer (fun a b => SB L a b) a z‖ = 0 := le_antisymm this (norm_nonneg _)
    rw [h0]; simp
  · rw [hn]
    have := h3 a z h h'
    have h0 : ‖cutKer (fun a b => SB L a b) a z‖ = 0 := le_antisymm this (norm_nonneg _)
    rw [h0]; simp

end Kernel

/-! ## 8. The eventual facts (`Gd`) -/

section GoodSizes

variable (d : Sizes)

/-- The size threshold of the arithmetic of the assembly. -/
def Nmin (k : ℕ) : ℝ := 8 * ((k : ℝ) + 2) ^ 4 + C5

/-- The deterministic facts at the size `n` used by the assembly: `KeyAt` for tensors of length `≤ kmax`,
the size threshold `Nm ≤ N`, and `W^{τ₀/2} ≥ 32` (so that `ρ/4 ≥ ℓ_u W^{τ₀/2}`). -/
def Gd (E u : ℕ → ℝ) (kmax : ℕ) (Nm τ₀ : ℝ) (n : ℕ) : Prop :=
  KeyAt (d.L n) (d.W n) (E n) (u n) ((d.size n : ℕ) : ℝ) kmax ∧ Nm ≤ ((d.size n : ℕ) : ℝ) ∧
    32 ≤ (d.W n : ℝ) ^ (τ₀ / 2)

/-- `Gd` holds eventually (`MainIndHyp`: `Bandwidth`, `SizeTendsto`, `RangeCond`, `|E n| ≤ 2 - κ`,
and the envelope `exists_norm_Kcal_le_win` of `𝒦`); compare `altLocalFormAt_four` in `LocalFormCalc`. -/
theorem gd_eventually {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) (kmax : ℕ)
    (Nm : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) {u : ℕ → ℝ} (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∀ᶠ n : ℕ in atTop, Gd d E u kmax Nm τ₀ n := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain
  obtain ⟨μ, hμ, hμb⟩ := im_bounds hE hκ
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have e1 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hsize).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have e2 : ∀ᶠ n : ℕ in atTop, 1 ≤ ((d.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 1
  have e3 : ∀ᶠ n : ℕ in atTop, Nm ≤ ((d.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop Nm
  have e4 : ∀ᶠ n : ℕ in atTop, 32 ≤ (d.W n : ℝ) ^ (τ₀ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ₀)).comp
      (tendsto_W_atTop d hc hband hsize)).eventually_ge_atTop 32
  have e5 : ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = N →
      ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u' v : ℝ, 0 ≤ u' → u' ≤ v → v < 1 →
        ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ kmax →
          ‖KLoop.Kcal L W E' u' J‖ ≤ (N : ℝ) ^ (1 : ℝ) * ((RBM.Path.etaT E' v)⁻¹) ^ kmax :=
    exists_norm_Kcal_le_win κ hκ kmax 1 one_pos
  have e6 := hsizeN.eventually e5
  filter_upwards [e1, e2, e3, e4, hrange, e6] with n h1 h2 h3 h4 h5 h6
  have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
  have hu0 : 0 ≤ u n := (hs0 n).trans (hu n)
  have hu1 : u n < 1 := lt_of_le_of_lt (hut n) (ht1 n)
  have hx : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - u n := h5.trans (by linarith [hut n])
  have hEn : |E n| < 2 := by linarith [hE n, abs_nonneg (E n)]
  refine ⟨⟨d.three_le_L n, d.W_pos n, h2, L_sq_le_size d n, ?_, eta_inv hN0 hx hμ (hμb n) h1, hEn,
    hu0, hu1, ?_⟩, h3, h4⟩
  · have : ((d.L n * d.W n) ^ 2 : ℕ) = d.size n := by rw [Sizes.size_eq]; ring
    rw [this]
  · intro J hwf hJ2 hJk
    have := h6 (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) (Sizes.size_eq d n).symm (E n) (hE n)
      (u n) (u n) hu0 le_rfl hu1 J hwf hJ2 hJk
    rwa [Real.rpow_one] at this

end GoodSizes

/-! ## 9. The deterministic bounds of the assembled cut form -/

section CutDet

variable {L W : ℕ} [NeZero L] [NeZero W] {k K : ℕ} [NeZero k]

/-- `W² ≤ N`. -/
theorem KeyAt.W_sq_le {E u Nr : ℝ} {kmax : ℕ} (h : KeyAt L W E u Nr kmax) : (W : ℝ) ^ 2 ≤ Nr := by
  have h1 := h.hNLW
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  have : (W : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 * (W : ℝ) ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hL1)
  refine this.trans ?_
  calc (L : ℝ) ^ 2 * (W : ℝ) ^ 2 = (((L * W) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ Nr := h1

/-- **The coefficient bound of the assembled cut form**: `|coef| ≤ N^{4k+9}` if `|coef FX| ≤ N^{2k+5}` (compare `four_coef` in `LocalFormCalc`). -/
theorem cut_coef {E u Nr ρ : ℝ} {kmax : ℕ} (hK : KeyAt L W E u Nr kmax) (hN2 : 2 ≤ Nr)
    (FX : LocalForm L W (k + 2) K) (hFX : ∀ c j q, ‖FX.coef c j q‖ ≤ Nr ^ (2 * k + 5))
    (a : Fin k → Z2 L) (j : Fin (K + 1)) (q : Fin j → Mono L W) :
    ‖(asmF u ρ (cutKerW L W) FX).coef a j q‖ ≤ Nr ^ (4 * k + 9) := by
  have hN0 := hK.N_pos
  have hK1 := (cutKerW_hyps (k := k) hK.hL hK.W_sq_le (ρ := 1) one_pos).1
  have h := coef_asmF_le hK.hL hK.hu0 hK.hu1 ρ (cutKerW L W) FX (B := Nr ^ (2 * k + 5))
    (B_K := Nr) (by positivity) hN0.le hFX hK1 a j q
  refine h.trans ?_
  have hc1 := one_add_card_le (L := L) (k := k) hK.hN1 hK.hLN
  have hc2 := card_le_pow (L := L) (k := k + 2) hK.hLN
  calc (1 + ((L : ℝ) ^ 2) ^ k) * (((L : ℝ) ^ 2) ^ (k + 2) * Nr * Nr ^ (2 * k + 5))
      ≤ (2 * Nr ^ k) * (Nr ^ (k + 2) * Nr * Nr ^ (2 * k + 5)) := by gcongr
    _ = 2 * Nr ^ (4 * k + 8) := by ring
    _ ≤ Nr * Nr ^ (4 * k + 8) := by gcongr
    _ = Nr ^ (4 * k + 9) := by ring

/-- **Far labels of the assembled cut form are deterministically tiny**: at a Hermitian `M` and
`maxDist b ≥ ρ`, `|F_b| ≤ N^{4k+10} dec(ρ/2)` (compare `four_far` in `LocalFormCalc`). -/
theorem cut_far {E u Nr ρ Tgt : ℝ} {kmax : ℕ} (hK : KeyAt L W E u Nr kmax) (hC5 : C5 ≤ Nr)
    (hρ : 0 < ρ) (FX : LocalForm L W (k + 2) K) {M : Matrix (Idx L W) (Idx L W) ℂ}
    (X : (Fin (k + 2) → Z2 L) → ℂ) (hFX : ∀ c, FX.eval E u M c = X c)
    (hX : ∀ c, ‖X c‖ ≤ Nr ^ (2 * k + 5))
    (htail : Nr ^ (4 * k + 10) * dec L u (ρ / 2) ≤ Tgt) (b : Fin k → Z2 L)
    (hb : ρ ≤ (KLoop.maxDist L b : ℝ)) :
    ‖(asmF u ρ (cutKerW L W) FX).eval E u M b‖ ≤ Tgt := by
  have hN0 := hK.N_pos
  have hK1 := (cutKerW_hyps (k := k) hK.hL hK.W_sq_le hρ).1
  have h := norm_eval_asmF_le_far hK.hL hK.hu0 hK.hu1 ρ (cutKerW L W) FX E u M X hFX
    (B_K := Nr) (B_X := Nr ^ (2 * k + 5)) hN0.le (by positivity) hK1 hX b hb
  refine h.trans ?_
  obtain ⟨j₀, hj₀S, hj⟩ := exists_far hρ hb
  have hj0 : j₀ ≠ 0 := (Finset.mem_erase.mp hj₀S).1
  have hϑ := norm_vartheta_le_decay hK.hL hK.hu0 hK.hu1 b hj0 (r := ρ / 2) hj
  have hcL := cL_le hK.hL hK.hu0 hK.hu1 hK.hLN
  have hε := (dec_pos L u (ρ / 2)).le
  have hC0 := cL_nonneg L u
  have hϑ2 : ‖vartheta L u b‖ ≤ Nr * Nr * dec L u (ρ / 2) := by
    refine hϑ.trans ?_
    calc cL L u * dec L u (ρ / 2) ≤ (C5 * Nr) * dec L u (ρ / 2) :=
          mul_le_mul_of_nonneg_right hcL hε
      _ ≤ (Nr * Nr) * dec L u (ρ / 2) := by gcongr
  have hc := card_le_pow (L := L) (k := k) hK.hLN
  have hc' := card_le_pow (L := L) (k := k + 2) hK.hLN
  calc (((L : ℝ) ^ 2) ^ k * (((L : ℝ) ^ 2) ^ (k + 2) * Nr * Nr ^ (2 * k + 5))) * ‖vartheta L u b‖
      ≤ (Nr ^ k * (Nr ^ (k + 2) * Nr * Nr ^ (2 * k + 5))) * (Nr * Nr * dec L u (ρ / 2)) := by
        gcongr
    _ = Nr ^ (4 * k + 10) * dec L u (ρ / 2) := by ring
    _ ≤ Tgt := htail

end CutDet

/-! ## 10. The assembly: `𝒬_u(𝔎^{tr} X^{tr})` with `𝔎 = W² cutKer S^{(B)}` -/

section Assembly

variable (d : Sizes)

/-- **The assembly of a cut-sum tensor.**  Let `X_n(ω) = Σ_z ...` be a `(k+2)`-tensor with a local form
`X.F` (entries in the blocks of the labels), such that the tensor `B_m = Σ_z 𝔎_{·,z} X_z` with the cut
kernel `𝔎 = W² cutKer S^{(B)}` (`hid`), `|X| ≤ N^{2k+5}`, `|coef X.F| ≤ N^{2k+5}` (`hsup`, `hcoef`, at the
sizes where `Gd` holds), and whose far part is small (`hfar`).  Then `𝒬_u B_m` is a local form
`F = 𝒬_u(𝔎^{tr}(X.F)^{tr})` (`ρ = ℓ_u W^{τ₀}/8`; degree `2k+2`, coefficients `≤ N^{4k+9}`, `Loc0 (4ρ)`,
sum-zero, `LabelDecayPT`) up to `O_≺(W^{-D₀})`; the proof is that of `altLocalFormAt_four` (in `LocalFormCalc`) with the kernel `W² cutKer S^{(B)}`. -/
theorem cutAssembly {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) {k : ℕ}
    [NeZero k] (hk : 2 ≤ k) {τ₀ D₀ : ℝ} (hτ₀ : 0 < τ₀) (hD₀ : 0 < D₀) {u : ℕ → ℝ}
    (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) (m : Fin 6) (σ : ℕ → Fin k → Bool)
    (X : Fac d E u (k + 2) ((k + 1) + (k + 1)))
    (hid : ∀ n (ω : Sizes.SeqΩ d) (a : Fin k → Z2 (d.L n)),
      altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m a =
        ∑ z, cutKerW (d.L n) (d.W n) a z * X.T n ω z)
    (hsup : ∀ n, Gd d E u (k + 1) (Nmin k) τ₀ n → ∀ ω z,
      ‖X.T n ω z‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 5))
    (hcoef : ∀ n, Gd d E u (k + 1) (Nmin k) τ₀ n → ∀ c j q,
      ‖(X.F n).coef c j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 5))
    (hfar : FarPT d X.T (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8)
      (D₀ + ((k + 1 + 1 : ℕ) : ℝ) / c + ((k + 2 : ℕ) : ℝ) / c)) :
    ∃ F : ∀ n, LocalForm (d.L n) (d.W n) k ((k + 1) + (k + 1)),
      (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ (((4 * k + 9 : ℕ) : ℝ))) ∧
      (∀ n, (F n).Local τ₀ (u n)) ∧
      (∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)) ∧
      LabelDecayPT d E u F τ₀ D₀ ∧
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
        (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m p.2 -
            (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
        (fun n _ _ => (d.W n : ℝ) ^ (-D₀)) := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hG := gd_eventually d hmain (k + 1) (Nmin k) hτ₀ hu hut
  have htail : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (((4 * k + 10 : ℕ) : ℝ)) *
      Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) ≤ (d.W n : ℝ) ^ (-D₀) :=
    tail_eventually d hc (Nat.cast_nonneg _) (by norm_num) hτ₀ hband hsize
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hG.and htail)
  set ρ : ℕ → ℝ := fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8 with hρdef
  set Fg : ∀ n, LocalForm (d.L n) (d.W n) k ((k + 1) + (k + 1)) := fun n =>
    asmF (u n) (ρ n) (cutKerW (d.L n) (d.W n)) (X.F n) with hFg
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs0 n).trans (hu n)
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hℓ : ∀ n, 0 < ellT (d.L n) (u n) := fun n =>
    (ellT_pos_le (by have := d.three_le_L n; omega) (hu1 n)).1
  have hWpos : ∀ n, 0 < (d.W n : ℝ) := fun n => by exact_mod_cast d.W_pos n
  have hρpos : ∀ n, 0 < ρ n := fun n => by
    simp only [hρdef]
    have := hℓ n
    have := Real.rpow_pos_of_pos (hWpos n) τ₀
    positivity
  have hC5 : ∀ n, n₀ ≤ n → C5 ≤ ((d.size n : ℕ) : ℝ) := fun n hn => by
    have := (hn₀ n hn).1.2.1
    unfold Nmin at this
    have h4 : (0 : ℝ) ≤ 8 * ((k : ℝ) + 2) ^ 4 := by positivity
    linarith
  have hN2 : ∀ n, n₀ ≤ n → 2 ≤ ((d.size n : ℕ) : ℝ) := fun n hn => by
    have := (hn₀ n hn).1.2.1
    unfold Nmin at this
    have h2k : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h4 : (2 : ℝ) ^ 4 ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) h2k 4
    have h5 := C5_pos
    norm_num at h4
    linarith
  refine ⟨fun n => if n₀ ≤ n then Fg n else zeroF, ?_, ?_, ?_, ?_, ?_⟩
  · -- the coefficient bound
    intro n b j q
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      have := cut_coef (ρ := ρ n) (hn₀ n hn).1.1 (hN2 n hn) (X.F n) (hcoef n (hn₀ n hn).1) b j q
      rwa [← Real.rpow_natCast] at this
    · simp only [hn, ↓reduceIte, zeroF, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- locality
    intro n
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      have h := loc0_asmF (k' := k) (u n) (ρ n) (cutKerW (d.L n) (d.W n)) (X.F n)
        (loc0_truncF_of_blk (ρ := ρ n) (X.blk n))
      refine h.local τ₀ (u n) ?_
      have h1 := hℓ n
      have h2 := Real.rpow_pos_of_pos (hWpos n) τ₀
      simp only [hρdef]
      nlinarith [mul_pos h1 h2]
    · simp only [hn, ↓reduceIte]
      intro b j q hq
      exact absurd rfl hq
  · -- sum-zero
    intro n M
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      exact sumZero_asmF (d.three_le_L n) hk (hu0 n) (hu1 n) (ρ n) _ _ _ _ M
    · simp only [hn, ↓reduceIte]
      intro a₁
      simp [eval_zeroF]
  · -- label decay (deterministic)
    unfold LabelDecayPT
    refine perTimeDomAt_of_le d (fun n p ω => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    obtain ⟨hGn, htn⟩ := hn₀ n hn
    simp only [hn, ↓reduceIte, hFg]
    by_cases hfar' : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
    · simp only [hfar', ↓reduceIte, mul_one]
      have hρle : ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) := by
        refine le_trans ?_ hfar'
        simp only [hρdef]
        have := mul_pos (hℓ n) (Real.rpow_pos_of_pos (hWpos n) τ₀)
        linarith
      have hd : dec (d.L n) (u n) (ρ n / 2) = Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) :=
        dec_rho (hℓ n)
      refine cut_far hGn.1 (hC5 n hn) (hρpos n) (X.F n) (X.T n ω) (fun c => X.eval_eq n ω c)
        (hsup n hGn ω) ?_ p.2 hρle
      rw [hd, ← Real.rpow_natCast]
      exact htn
    · simp only [hfar', ↓reduceIte, mul_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- the error: the stochastic kernel assembly `kernelAssembly_PT` with `𝔎 = W² cutKer S`
    have hδ0 : ∀ n, 0 ≤ (fun _ : ℕ => (0 : ℝ)) n := fun n => le_rfl
    have hK1 : ∀ᶠ n : ℕ in atTop, ∀ (a : Fin k → Z2 (d.L n)) (c' : Fin (k + 2) → Z2 (d.L n)),
        ‖cutKerW (d.L n) (d.W n) a c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ 1 := by
      filter_upwards [hG] with n hGn a c'
      have := (cutKerW_hyps (k := k) hGn.1.hL hGn.1.W_sq_le (ρ := 1) one_pos).1 a c'
      simpa using this
    have hK2 : ∀ᶠ n : ℕ in atTop, ∀ (a : Fin k → Z2 (d.L n)) (c' : Fin (k + 2) → Z2 (d.L n)),
        ρ n ≤ (zdist2 (d.L n) (c' 0 - a 0) : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖cutKerW (d.L n) (d.W n) a c'‖ ≤ (fun _ : ℕ => (0 : ℝ)) n := by
      filter_upwards [hG] with n hGn a c' h1 h2
      exact (cutKerW_hyps (k := k) hGn.1.hL hGn.1.W_sq_le (hρpos n)).2.1 a c' h1 h2
    have hK3 : ∀ᶠ n : ℕ in atTop, ∀ (a : Fin k → Z2 (d.L n)) (c' : Fin (k + 2) → Z2 (d.L n)),
        ρ n ≤ (KLoop.maxDist (d.L n) a : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖cutKerW (d.L n) (d.W n) a c'‖ ≤ (fun _ : ℕ => (0 : ℝ)) n := by
      filter_upwards [hG] with n hGn a c' h1 h2
      exact (cutKerW_hyps (k := k) hGn.1.hL hGn.1.W_sq_le (hρpos n)).2.2 a c' h1 h2
    have hX : ∀ᶠ n : ℕ in atTop, ∀ (ω : Sizes.SeqΩ d) (c' : Fin (k + 2) → Z2 (d.L n)),
        ‖X.T n ω c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 5) := by
      filter_upwards [hG] with n hGn ω c'
      exact hsup n hGn ω c'
    have hδ : ∀ᶠ n : ℕ in atTop, (1 + ((d.size n : ℕ) : ℝ) ^ k) *
        (((d.size n : ℕ) : ℝ) ^ (k + 2) * (fun _ : ℕ => (0 : ℝ)) n *
          ((d.size n : ℕ) : ℝ) ^ (2 * k + 5)) ≤ (d.W n : ℝ) ^ (-D₀) / 2 :=
      Filter.Eventually.of_forall fun n => by
        simp only [mul_zero, zero_mul]
        positivity
    have hl1 := l1far_PT d hc hband (k := k + 2) (D := D₀ + ((k + 1 + 1 : ℕ) : ℝ) / c)
      (X := X.T) (ρ := ρ) hfar
    have h := kernelAssembly_PT d (D₀ := D₀) hc hband hsize (aK := 1) (aX := 2 * k + 5)
      (K := (k + 1) + (k + 1)) (E := E) (u := u) (ρ := ρ) (δ := fun _ => 0)
      (fun n => cutKerW (d.L n) (d.W n)) X.F X.T (fun n ω c' => X.eval_eq n ω c') hu0 hu1 hδ0 hK1
      hK2 hK3 hX hδ hl1
    refine perTimeDomAt_congr_left d ?_ h
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    simp only [hn, ↓reduceIte, hFg]
    have hB : altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m =
        fun a' => ∑ c', cutKerW (d.L n) (d.W n) a' c' * X.T n ω c' := funext (hid n ω)
    change ‖Qop (d.L n) (u n) (fun a' => ∑ c', cutKerW (d.L n) (d.W n) a' c' * X.T n ω c') p.2 -
        (asmF (u n) (ρ n) (cutKerW (d.L n) (d.W n)) (X.F n)).eval (E n) (u n)
          (Sizes.seqHflow d n (u n) ω) p.2‖ =
      ‖Qop (d.L n) (u n) (altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m)
          p.2 - (asmF (u n) (ρ n) (cutKerW (d.L n) (d.W n)) (X.F n)).eval (E n) (u n)
          (Sizes.seqHflow d n (u n) ω) p.2‖
    rw [hB]

end Assembly

/-! ## 11. The terms of the cut sums: bounds of the pieces -/

section Terms

variable (d : Sizes)

/-- The zero tensor. -/
def Fac.zero {E u : ℕ → ℝ} {kk K : ℕ} : Fac d E u kk K where
  F _ := zeroF
  T _ _ _ := 0
  eval_eq n ω z := eval_zeroF _ _ _ _
  blk _ := blkLab_zero

/-- The adjacency indicator `1(|a' - b'| ≤ 1)` of the last two labels of `z = (c, a', b')`. -/
def adjI (L k : ℕ) [NeZero L] (z : Fin (k + 2) → Z2 L) : ℂ :=
  if zdist2 L (z (Fin.natAdd k 0) - z (Fin.natAdd k 1)) ≤ 1 then 1 else 0

theorem norm_adjI_le (L k : ℕ) [NeZero L] (z : Fin (k + 2) → Z2 L) : ‖adjI L k z‖ ≤ 1 := by
  unfold adjI
  split_ifs <;> simp

theorem adjI_ne_zero {L k : ℕ} [NeZero L] {z : Fin (k + 2) → Z2 L} (h : adjI L k z ≠ 0) :
    zdist2 L (z (Fin.natAdd k 0) - z (Fin.natAdd k 1)) ≤ 1 := by
  by_contra hc
  apply h
  simp [adjI, hc]

/-- The adjacency indicator as a tensor in the labels of size `n`. -/
def adjT (k : ℕ) (n : ℕ) (z : Fin (k + 2) → Z2 (d.L n)) : ℂ := adjI (d.L n) k z

/-- `S^{(B)}_{a'b'} 1(|a' - b'| ≤ 1) = S^{(B)}_{a'b'}`. -/
theorem SB_mul_adj {L : ℕ} [NeZero L] (hL : 3 ≤ L) (a b : Z2 L) :
    SB L a b * (if zdist2 L (a - b) ≤ 1 then (1 : ℂ) else 0) = SB L a b := by
  by_cases h : zdist2 L (a - b) ≤ 1
  · simp [h]
  · simp [h, SB_apply_eq_zero L hL (by omega : 1 < zdist2 L (a - b))]

variable {d}

/-! ### Sup and coefficient bounds of the pieces -/

section Good

variable {E u : ℕ → ℝ} {k : ℕ} (Nm τ₀ : ℝ)

/-- A tensor is *good* if its entries and the coefficients of its form are `≤ 2N^{k+2}` at the sizes where
`Gd` holds. -/
def GoodFac (x : Fac d E u (k + 2) (k + 1)) : Prop :=
  (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ ω z, ‖x.T n ω z‖ ≤ 2 * ((d.size n : ℕ) : ℝ) ^ (k + 2)) ∧
    (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ c j q,
      ‖(x.F n).coef c j q‖ ≤ 2 * ((d.size n : ℕ) : ℝ) ^ (k + 2))

variable {Nm τ₀}

theorem goodFac_lk {m : ℕ} (hm : m + 1 ≤ k + 1) (σ : ∀ n : ℕ, Fin (m + 1) → Bool)
    (f : Fin (m + 1) → Fin (k + 2)) :
    GoodFac Nm τ₀ (Fac.lk (d := d) (E := E) (u := u) hm σ f) := by
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · exact hn.1.norm_lk_le (Sizes.seqHflow_isHermitian d n (u n) ω) (σ n) _ (by omega) hm
  · have hK := hn.1
    have hN1 := hK.hN1
    have hKb : ∀ b : Fin (m + 1) → Z2 (d.L n),
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) b)‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (k + 2) := fun b => by
      have hwf : (loopOf (σ n) b).WF := by simp [loopOf, LoopIdx.WF]
      have hl : (loopOf (σ n) b).length = m + 1 := by simp [loopOf, LoopIdx.length]
      exact hK.norm_kcal_le _ (by omega) (by omega) hwf
    have hlk := coef_lkF_le (L := d.L n) (W := d.W n) hK.hW (σ n) (E n) (u n)
      (B := ((d.size n : ℕ) : ℝ) ^ (k + 2)) (by positivity) hKb
    have h1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k + 2) := one_le_pow₀ hN1
    refine coef_liftF_le (comapF f (lkF (σ n) (E n) (u n))) (by positivity)
      (fun c' j' q' => ?_) c j q
    refine (hlk (fun i => c' (f i)) j' q').trans ?_
    linarith

theorem goodFac_kcal {m : ℕ} (hm : m + 1 ≤ k + 1) (σ : ∀ n : ℕ, Fin (m + 1) → Bool)
    (f : Fin (m + 1) → Fin (k + 2)) :
    GoodFac Nm τ₀ (Fac.kcal (d := d) (E := E) (u := u) (K := k + 1) σ f) := by
  have hb : ∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ (z : Fin (k + 2) → Z2 (d.L n)),
      ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => z (f i)))‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (k + 2) := fun n hn z => by
    have hwf : (loopOf (σ n) (fun i => z (f i))).WF := by simp [loopOf, LoopIdx.WF]
    have hl : (loopOf (σ n) (fun i => z (f i))).length = m + 1 := by
      simp [loopOf, LoopIdx.length]
    exact hn.1.norm_kcal_le _ (by omega) (by omega) hwf
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · have := hb n hn z
    have h1 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k + 2) := by have := hn.1.hN1; positivity
    change ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => z (f i)))‖ ≤ _
    linarith
  · have h1 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k + 2) := by have := hn.1.hN1; positivity
    have := coef_constF_le (L := d.L n) (W := d.W n) (K := k + 1)
      (fun z => KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) (fun i => z (f i))))
      (B := ((d.size n : ℕ) : ℝ) ^ (k + 2)) h1 (hb n hn) c j q
    change ‖(constF (fun z => KLoop.Kcal (d.L n) (d.W n) (E n) (u n)
      (loopOf (σ n) (fun i => z (f i)))) : LocalForm (d.L n) (d.W n) (k + 2) (k + 1)).coef c j q‖ ≤ _
    linarith

theorem goodFac_loop {m : ℕ} (hm : m + 1 ≤ k + 1) (σ : ∀ n : ℕ, Fin (m + 1) → Bool)
    (f : Fin (m + 1) → Fin (k + 2)) :
    GoodFac Nm τ₀ (Fac.loop (d := d) (E := E) (u := u) hm σ f) := by
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · have h1 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k + 2) := by have := hn.1.hN1; positivity
    have := hn.1.norm_loop_le (Sizes.seqHflow_isHermitian d n (u n) ω) (σ n) (fun i => z (f i)) hm
    change ‖LLf (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
      (loopOf (σ n) (fun i => z (f i)))‖ ≤ _
    linarith
  · have hK := hn.1
    have h1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k + 2) := one_le_pow₀ hK.hN1
    refine coef_liftF_le (comapF f (loopF (σ n))) (by positivity) (fun c' j' q' => ?_) c j q
    refine (coef_loopF_le hK.hW (σ n) (fun i => c' (f i)) j' q').trans ?_
    linarith

end Good

end Terms

/-! ## 12. The tensors as cut sums: the identities `B_m = Σ_z 𝔎 X` -/

section Identities

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} [NeZero k]

/-- The cut pairs `1 ≤ k' < l' ≤ k`. -/
def pairsK (k : ℕ) : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc 1 k).sigma (fun k' => Finset.Ioc k' k)

theorem mem_pairsK {p : Σ _ : ℕ, ℕ} : p ∈ pairsK k ↔ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k := by
  simp only [pairsK, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem card_pairsK_le : (pairsK k).card ≤ k * k := by
  unfold pairsK
  rw [Finset.card_sigma]
  calc ∑ k' ∈ Finset.Icc 1 k, (Finset.Ioc k' k).card ≤ ∑ _k' ∈ Finset.Icc 1 k, k :=
        Finset.sum_le_sum fun k' _ => by simp
    _ = k * k := by simp

/-- `Fin.append c ![a', b']` at the first `k` labels. -/
theorem append_castAdd (c : Fin k → Z2 L) (a' b' : Z2 L) (i : Fin k) :
    (Fin.append c ![a', b'] : Fin (k + 2) → Z2 L) (Fin.castAdd 2 i) = c i := Fin.append_left _ _ _

theorem append_natAdd0 (c : Fin k → Z2 L) (a' b' : Z2 L) :
    (Fin.append c ![a', b'] : Fin (k + 2) → Z2 L) (Fin.natAdd k 0) = a' := by
  rw [Fin.append_right]; rfl

theorem append_natAdd1 (c : Fin k → Z2 L) (a' b' : Z2 L) :
    (Fin.append c ![a', b'] : Fin (k + 2) → Z2 L) (Fin.natAdd k 1) = b' := by
  rw [Fin.append_right]; rfl

theorem adjI_append (c : Fin k → Z2 L) (a' b' : Z2 L) :
    adjI L k (Fin.append c ![a', b']) = if zdist2 L (a' - b') ≤ 1 then 1 else 0 := by
  simp only [adjI, append_natAdd0, append_natAdd1]

/-- The length of `loopOf σ a` is `k`. -/
theorem length_loopOf (σ : Fin k → Bool) (a : Fin k → Z2 L) : (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- Reordering a triple sum `Σ_x Σ_y Σ_{i∈s} = Σ_{i∈s} Σ_x Σ_y`. -/
theorem sum_swap3 {ι : Type*} (f : Z2 L → Z2 L → ι → ℂ) (s : Finset ι) :
    ∑ x, ∑ y, ∑ i ∈ s, f x y i = ∑ i ∈ s, ∑ x, ∑ y, f x y i := by
  calc ∑ x, ∑ y, ∑ i ∈ s, f x y i = ∑ x, ∑ i ∈ s, ∑ y, f x y i :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ x, ∑ y, f x y i := Finset.sum_comm

/-- **`𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` as a cut sum** (`B₂`): `Σ_z 𝔎_{c,z} X_z` with the pieces `𝒢^L`, `𝒢^R`. -/
theorem elklkN_eq (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin k → Bool)
    (a : Fin k → Z2 L) :
    elklkN L W E u M (loopOf σ a) =
      ∑ z, cutKerW L W a z * ∑ p ∈ pairsK k, adjI L k z *
        (lkTensor L W E u M (sL σ p.1 p.2) (fun i => z (fL k p.1 p.2 i)) *
          lkTensor L W E u M (sR σ p.1 p.2) (fun i => z (fR k p.1 p.2 i))) := by
  rw [sum_cutKerW]
  unfold elklkN
  rw [length_loopOf]
  congr 1
  simp only [pairsK]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Eq.trans ?_ (sum_swap3 _ _).symm
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hp2, hp3⟩ := mem_pairsK.mp (by simpa [pairsK] using hp)
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hL' := cutGlueL_loopOf σ (Fin.append a ![x, y]) hp1 hp2 hp3
  have hR' := cutGlueR_loopOf σ (Fin.append a ![x, y]) hp1 hp2 hp3
  simp only [append_castAdd, append_natAdd0, append_natAdd1] at hL' hR'
  rw [adjI_append, hL', hR']
  have h := SB_mul_adj hL x y
  calc LKf L W E u M (loopOf (sL σ p.1 p.2) fun i => Fin.append a ![x, y] (fL k p.1 p.2 i)) *
        SB L x y * LKf L W E u M (loopOf (sR σ p.1 p.2) fun i => Fin.append a ![x, y] (fR k p.1 p.2 i))
      = SB L x y * (LKf L W E u M (loopOf (sL σ p.1 p.2) fun i => Fin.append a ![x, y] (fL k p.1 p.2 i)) *
          LKf L W E u M (loopOf (sR σ p.1 p.2) fun i => Fin.append a ![x, y] (fR k p.1 p.2 i))) := by
        ring
    _ = (SB L x y * (if zdist2 L (x - y) ≤ 1 then (1 : ℂ) else 0)) *
          (LKf L W E u M (loopOf (sL σ p.1 p.2) fun i => Fin.append a ![x, y] (fL k p.1 p.2 i)) *
          LKf L W E u M (loopOf (sR σ p.1 p.2) fun i => Fin.append a ![x, y] (fR k p.1 p.2 i))) := by
        rw [h]
    _ = _ := by simp only [lkTensor]; ring

/-- The sign of the `j`-th edge of `loopOf σ a` (extended by `false`). -/
theorem getD_loopOf (σ : Fin k → Bool) (a : Fin k → Z2 L) (j : ℕ) :
    (loopOf σ a).σ.getD j false = sx σ j := by
  unfold loopOf sx
  by_cases h : j < k
  · simp [h]
  · simp [h]

/-- **`𝓔^{(G̃)}` as a cut sum** (`B₃`): `avgErr` is a one-loop `𝓛-𝒦` at the label `a'`, the loop is the
single-cut loop `𝒢_{k'}^{(b')}`. -/
theorem egtN_eq (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin k → Bool)
    (a : Fin k → Z2 L) :
    egtN L W E u M (loopOf σ a) =
      ∑ z, cutKerW L W a z * ∑ k' ∈ Finset.Icc 1 k, adjI L k z *
        (lkTensor L W E u M (fun _ : Fin 1 => sx σ (k' - 1)) (fun i => z (fA k i)) *
          LLf L W E u M (loopOf (s3 σ k') (fun i => z (f3 k k' i)))) := by
  rw [sum_cutKerW]
  unfold egtN
  rw [length_loopOf]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Eq.trans ?_ (sum_swap3 _ _).symm
  refine Finset.sum_congr rfl fun k' hk' => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk'
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hG' := cutGlue_loopOf σ (Fin.append a ![x, y]) hk1 hk2
  simp only [append_castAdd, append_natAdd1] at hG'
  have h := SB_mul_adj hL x y
  rw [adjI_append, hG', getD_loopOf, avgErr_eq_lk]
  simp only [fA, append_natAdd0]
  calc lkTensor L W E u M (fun _ : Fin 1 => sx σ (k' - 1)) (fun _ => x) * SB L x y *
        LLf L W E u M (loopOf (s3 σ k') fun i => Fin.append a ![x, y] (f3 k k' i))
      = SB L x y * (lkTensor L W E u M (fun _ : Fin 1 => sx σ (k' - 1)) (fun _ => x) *
        LLf L W E u M (loopOf (s3 σ k') fun i => Fin.append a ![x, y] (f3 k k' i))) := by ring
    _ = (SB L x y * (if zdist2 L (x - y) ≤ 1 then (1 : ℂ) else 0)) *
        (lkTensor L W E u M (fun _ : Fin 1 => sx σ (k' - 1)) (fun _ => x) *
        LLf L W E u M (loopOf (s3 σ k') fun i => Fin.append a ![x, y] (f3 k k' i))) := by
        rw [h]
    _ = _ := by ring

/-- Moving the outermost sum `Σ_l` innermost in a five-fold sum. -/
theorem sum_swap5 (s₀ s₁ : Finset ℕ) (s₂ : ℕ → Finset ℕ) (g : ℕ → ℕ → ℕ → Z2 L → Z2 L → ℂ) :
    ∑ l ∈ s₀, ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ x, ∑ y, g l k' l' x y =
      ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ x, ∑ y, ∑ l ∈ s₀, g l k' l' x y := by
  calc ∑ l ∈ s₀, ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ x, ∑ y, g l k' l' x y
      = ∑ k' ∈ s₁, ∑ l ∈ s₀, ∑ l' ∈ s₂ k', ∑ x, ∑ y, g l k' l' x y := Finset.sum_comm
    _ = ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ l ∈ s₀, ∑ x, ∑ y, g l k' l' x y :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_comm
    _ = ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ x, ∑ l ∈ s₀, ∑ y, g l k' l' x y :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ => Finset.sum_comm
    _ = ∑ k' ∈ s₁, ∑ l' ∈ s₂ k', ∑ x, ∑ y, ∑ l ∈ s₀, g l k' l' x y :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
          Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- **`Σ_{l ≥ 3} [𝒦 ∼ (𝓛-𝒦)]^l` as a cut sum** (`B₁`): the pairs with `𝒦` of length `≥ 3` on one side. -/
theorem ksimLK_eq (hL : 3 ≤ L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Fin k → Bool)
    (a : Fin k → Z2 L) :
    ∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ a) =
      ∑ z, cutKerW L W a z *
        ((∑ p ∈ (pairsK k).filter (fun p => 3 ≤ p.2 - p.1 + 1), adjI L k z *
          (lkTensor L W E u M (sL σ p.1 p.2) (fun i => z (fL k p.1 p.2 i)) *
            KLoop.Kcal L W E u (loopOf (sR σ p.1 p.2) (fun i => z (fR k p.1 p.2 i))))) +
        ∑ p ∈ (pairsK k).filter (fun p => 3 ≤ p.1 + k - p.2 + 1), adjI L k z *
          (KLoop.Kcal L W E u (loopOf (sL σ p.1 p.2) (fun i => z (fL k p.1 p.2 i))) *
            lkTensor L W E u M (sR σ p.1 p.2) (fun i => z (fR k p.1 p.2 i)))) := by
  rw [sum_cutKerW]
  unfold ksimLK
  simp only [length_loopOf]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_swap5]
  simp only [Finset.sum_filter]
  simp_rw [← Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Eq.trans ?_ (sum_swap3 _ _).symm
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hp2, hp3⟩ := mem_pairsK.mp (by simpa [pairsK] using hp)
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hL' := cutGlueL_loopOf σ (Fin.append a ![x, y]) hp1 hp2 hp3
  have hR' := cutGlueR_loopOf σ (Fin.append a ![x, y]) hp1 hp2 hp3
  simp only [append_castAdd, append_natAdd0, append_natAdd1] at hL' hR'
  have hlR : (LoopIdx.cutGlueR p.1 p.2 y (loopOf σ a)).length = p.2 - p.1 + 1 :=
    LoopIdx.length_cutGlueR _ y hp1 hp2 (by rw [length_loopOf]; exact hp3)
  have hlL : (LoopIdx.cutGlueL p.1 p.2 x (loopOf σ a)).length = p.1 + k - p.2 + 1 := by
    rw [LoopIdx.length_cutGlueL _ x hp1 hp2 (by rw [length_loopOf]; exact hp3), length_loopOf]
  simp only [hlR, hlL, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_Icc]
  have hRk : p.2 - p.1 + 1 ≤ k := by omega
  have hLk : p.1 + k - p.2 + 1 ≤ k := by omega
  simp only [hRk, hLk, and_true]
  rw [adjI_append, hL', hR']
  have h := SB_mul_adj hL x y
  have key : ∀ A B : ℂ, A * SB L x y * B =
      SB L x y * ((if zdist2 L (x - y) ≤ 1 then (1 : ℂ) else 0) * (A * B)) := by
    intro A B
    linear_combination (-(A * B)) * h
  simp only [lkTensor, key]
  split_ifs <;> ring

end Identities

/-! ## 13. The three cases: terms, bounds, far part -/

section Cases

variable {d : Sizes} {E u : ℕ → ℝ} {k : ℕ} [NeZero k]

/-- The product `1(|a'-b'| ≤ 1) x y` of two pieces (a tensor of degree `2(k+1)`). -/
def prodTerm (x y : Fac d E u (k + 2) (k + 1)) : Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  Fac.tsmul (adjT d k) (Fac.mul x y)

theorem prodTerm_T (x y : Fac d E u (k + 2) (k + 1)) (n : ℕ) (ω : Sizes.SeqΩ d)
    (z : Fin (k + 2) → Z2 (d.L n)) :
    (prodTerm x y).T n ω z = adjI (d.L n) k z * (x.T n ω z * y.T n ω z) := rfl

/-- The bounds of a tensor that is a sum of `c₀` products of good pieces: entries `≤ c₀ · 4N^{2k+4}`,
coefficients `≤ c₀ (k+2)² 4N^{2k+4}`. -/
def TermBd (Nm τ₀ c₀ : ℝ) (t : Fac d E u (k + 2) ((k + 1) + (k + 1))) : Prop :=
  (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ ω z,
      ‖t.T n ω z‖ ≤ c₀ * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))) ∧
    (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ c j q,
      ‖(t.F n).coef c j q‖ ≤ c₀ * (((k : ℝ) + 2) ^ 2 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))))

variable {Nm τ₀ : ℝ}

theorem termBd_prod {x y : Fac d E u (k + 2) (k + 1)} (hx : GoodFac Nm τ₀ x)
    (hy : GoodFac Nm τ₀ y) : TermBd Nm τ₀ 1 (prodTerm x y) := by
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · have h1 := hx.1 n hn ω z
    have h2 := hy.1 n hn ω z
    have h3 := norm_adjI_le (d.L n) k z
    have h4 := norm_nonneg (x.T n ω z)
    have h5 := norm_nonneg (y.T n ω z)
    rw [prodTerm_T, norm_mul, norm_mul]
    calc ‖adjI (d.L n) k z‖ * (‖x.T n ω z‖ * ‖y.T n ω z‖) ≤ 1 * ((2 * ((d.size n : ℕ) : ℝ) ^ (k + 2)) *
          (2 * ((d.size n : ℕ) : ℝ) ^ (k + 2))) :=
          mul_le_mul h3 (mul_le_mul h1 h2 h5 (by have := hn.1.hN1; positivity)) (by positivity)
            zero_le_one
      _ = 1 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4)) := by ring
  · have hN := hn.1.hN1
    have hB : (0 : ℝ) ≤ 2 * ((d.size n : ℕ) : ℝ) ^ (k + 2) := by positivity
    have h1 := coef_mulF_le (x.F n) (y.F n) hB hB (hx.2 n hn) (hy.2 n hn)
    have h2 := coef_tsmulF_le (adjT d k n) (mulF (x.F n) (y.F n)) (Bv := 1)
      (fun b => norm_adjI_le (d.L n) k b) (fun c' j' q' => h1 c' j' q') c j q
    refine h2.trans ?_
    push_cast
    exact le_of_eq (by ring)

theorem termBd_mono {c₀ c₁ : ℝ} (hc : c₀ ≤ c₁) {t : Fac d E u (k + 2) ((k + 1) + (k + 1))}
    (h : TermBd Nm τ₀ c₀ t) : TermBd Nm τ₀ c₁ t := by
  refine ⟨fun n hn ω z => (h.1 n hn ω z).trans ?_, fun n hn c j q => (h.2 n hn c j q).trans ?_⟩
  · have := hn.1.hN1
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  · have := hn.1.hN1
    exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem termBd_sum {ι : Type*} (s : Finset ι) (t : ι → Fac d E u (k + 2) ((k + 1) + (k + 1)))
    (h : ∀ p ∈ s, TermBd Nm τ₀ 1 (t p)) : TermBd Nm τ₀ (s.card) (Fac.sum s t) := by
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · calc ‖(Fac.sum s t).T n ω z‖ ≤ ∑ p ∈ s, ‖(t p).T n ω z‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ s, 1 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4)) :=
          Finset.sum_le_sum fun p hp => (h p hp).1 n hn ω z
      _ = (s.card : ℝ) * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4)) := by simp
  · have := coef_sumF_le s (fun p => (t p).F n) (B := ((k : ℝ) + 2) ^ 2 *
      (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))) (fun p hp c' j' q' => by
        have := (h p hp).2 n hn c' j' q'
        simpa using this) c j q
    exact this

theorem termBd_add {c₁ c₂ : ℝ} {x y : Fac d E u (k + 2) ((k + 1) + (k + 1))}
    (hx : TermBd Nm τ₀ c₁ x) (hy : TermBd Nm τ₀ c₂ y) : TermBd Nm τ₀ (c₁ + c₂) (Fac.add x y) := by
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · calc ‖(Fac.add x y).T n ω z‖ ≤ ‖x.T n ω z‖ + ‖y.T n ω z‖ := norm_add_le _ _
      _ ≤ _ := by have := hx.1 n hn ω z; have := hy.1 n hn ω z; linarith
  · calc ‖((Fac.add x y).F n).coef c j q‖ ≤ ‖(x.F n).coef c j q‖ + ‖(y.F n).coef c j q‖ :=
          norm_add_le _ _
      _ ≤ _ := by have := hx.2 n hn c j q; have := hy.2 n hn c j q; linarith

/-- From `TermBd c₀` to the bounds `N^{2k+5}` of the assembly, if `4 c₀ (k+2)² ≤ N_min`. -/
theorem termBd_final {c₀ : ℝ} (hc : 0 ≤ c₀) (hcN : c₀ * (4 * ((k : ℝ) + 2) ^ 2) ≤ Nmin k)
    (hNm : Nm = Nmin k) {t : Fac d E u (k + 2) ((k + 1) + (k + 1))} (h : TermBd Nm τ₀ c₀ t) :
    (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ ω z,
      ‖t.T n ω z‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 5)) ∧
    (∀ n, Gd d E u (k + 1) Nm τ₀ n → ∀ c j q,
      ‖(t.F n).coef c j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k + 5)) := by
  have key : ∀ n, Gd d E u (k + 1) Nm τ₀ n →
      c₀ * (((k : ℝ) + 2) ^ 2 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))) ≤
        ((d.size n : ℕ) : ℝ) ^ (2 * k + 5) := fun n hn => by
    have hN1 := hn.1.hN1
    have hNm' := hn.2.1
    rw [hNm] at hNm'
    calc c₀ * (((k : ℝ) + 2) ^ 2 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4)))
        = (c₀ * (4 * ((k : ℝ) + 2) ^ 2)) * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4) := by ring
      _ ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4) :=
          mul_le_mul_of_nonneg_right (hcN.trans hNm') (by positivity)
      _ = ((d.size n : ℕ) : ℝ) ^ (2 * k + 5) := by ring
  refine ⟨fun n hn ω z => ?_, fun n hn c j q => ?_⟩
  · refine (h.1 n hn ω z).trans ?_
    refine le_trans ?_ (key n hn)
    have hN1 := hn.1.hN1
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by
      have : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact one_le_pow₀ this
    calc c₀ * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))
        = c₀ * (1 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))) := by ring
      _ ≤ c₀ * (((k : ℝ) + 2) ^ 2 * (4 * ((d.size n : ℕ) : ℝ) ^ (2 * k + 4))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) hc
  · exact (h.2 n hn c j q).trans (key n hn)

/-- `ρ = ℓ_u W^{τ₀}/8 ≥ 2` and `ℓ_u W^{τ₀/2} ≤ ρ/4` if `ℓ_u ≥ 1` and `W^{τ₀/2} ≥ 32`. -/
theorem rho_facts {ℓ Wr τ₀ : ℝ} (hℓ : 1 ≤ ℓ) (hW0 : 0 < Wr) (hW : 32 ≤ Wr ^ (τ₀ / 2)) :
    2 ≤ ℓ * Wr ^ τ₀ / 8 ∧ ℓ * Wr ^ (τ₀ / 2) ≤ (ℓ * Wr ^ τ₀ / 8) / 4 := by
  have hpow : Wr ^ τ₀ = Wr ^ (τ₀ / 2) * Wr ^ (τ₀ / 2) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  rw [hpow]
  set T : ℝ := Wr ^ (τ₀ / 2) with hT
  have hℓ0 : 0 ≤ ℓ := by linarith
  refine ⟨?_, ?_⟩
  · have h1 : 32 * 32 ≤ T * T := mul_le_mul hW hW (by norm_num) (by linarith)
    nlinarith
  · have h1 : ℓ * T * 32 ≤ ℓ * T * T :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hℓ0 (by linarith))
    nlinarith

/-- **The geometry of a cut**: if the two groups of labels `fA`, `fB` cover `z = (c, a', b')`, contain
`a'`, `b'` respectively, `|a' - b'| ≤ 1` and `maxDist z ≥ ρ`, one of the groups has `maxDist ≥ ℓ_u W^{τ₀/2}`. -/
theorem geo_pieces {la lb L : ℕ} [NeZero L] {ℓ Wr τ₀ : ℝ}
    (hℓ : 1 ≤ ℓ) (hW0 : 0 < Wr) (hW : 32 ≤ Wr ^ (τ₀ / 2)) (fA : Fin la → Fin (k + 2))
    (fB : Fin lb → Fin (k + 2)) (hia : ∃ i, fA i = Fin.natAdd k 0) (hib : ∃ i, fB i = Fin.natAdd k 1)
    (hcov : ∀ j, (∃ i, fA i = j) ∨ (∃ i, fB i = j)) (z : Fin (k + 2) → Z2 L)
    (hadj : adjI L k z ≠ 0) (hfar : ℓ * Wr ^ τ₀ / 8 ≤ (KLoop.maxDist L z : ℝ)) :
    ℓ * Wr ^ (τ₀ / 2) ≤ (KLoop.maxDist L (fun i => z (fA i)) : ℝ) ∨
      ℓ * Wr ^ (τ₀ / 2) ≤ (KLoop.maxDist L (fun i => z (fB i)) : ℝ) := by
  obtain ⟨h2, h4⟩ := rho_facts hℓ hW0 hW
  have hb := maxDist_le_add z fA fB hia hib (adjI_ne_zero hadj) hcov
  exact far_of_sum h2 h4 hfar hb

/-- **The far part of a product term**: `‖1(|a'-b'| ≤ 1) x y‖ 1(ρ ≤ maxDist z) ≺ W^{-(D - (k+3)/c)}` if
each piece is `≺ W^{-D}` where its own labels are `ℓ_u W^{τ₀/2}` apart. -/
theorem farPT_term {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t) {u : ℕ → ℝ}
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) {Nm : ℝ}
    (hNm : 2 ≤ Nm) {x y : Fac d E u (k + 2) (k + 1)} (hxg : GoodFac Nm τ₀ x)
    (hyg : GoodFac Nm τ₀ y) {la lb : ℕ} (fx : Fin la → Fin (k + 2)) (fy : Fin lb → Fin (k + 2))
    (hia : ∃ i, fx i = Fin.natAdd k 0) (hib : ∃ i, fy i = Fin.natAdd k 1)
    (hcov : ∀ j, (∃ i, fx i = j) ∨ (∃ i, fy i = j)) {D : ℝ}
    (hx : FarPieceAt d x.T (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2)) fx D)
    (hy : FarPieceAt d y.T (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2)) fy D) :
    FarPT d (prodTerm x y).T (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8)
      (D - ((k + 3 : ℕ) : ℝ) / c) := by
  have hG := gd_eventually d hmain (k + 1) Nm hτ₀ hu hut
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain
  have hsxy : ∀ (w : Fac d E u (k + 2) (k + 1)), GoodFac Nm τ₀ w → ∀ n,
      Gd d E u (k + 1) Nm τ₀ n → ∀ ω z,
        ‖w.T n ω z‖ ≤ ((d.size n : ℕ) : ℝ) ^ (((k + 3 : ℕ) : ℝ)) := fun w hw n hn ω z => by
    have h1 := hw.1 n hn ω z
    have hN2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hNm.trans hn.2.1
    rw [Real.rpow_natCast]
    refine h1.trans ?_
    calc 2 * ((d.size n : ℕ) : ℝ) ^ (k + 2) ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (k + 2) :=
          mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = ((d.size n : ℕ) : ℝ) ^ (k + 3) := by ring
  exact farPT_prod d hc (Nat.cast_nonneg _) hband hsize x y (adjT d k)
    (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8)
    (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2))
    (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2)) fx fy (Gd d E u (k + 1) Nm τ₀) hG
    (fun n hn z hadj hfar =>
      geo_pieces (one_le_ellT (by have := hn.1.hL; omega) hn.1.hu0 hn.1.hu1)
        (by exact_mod_cast d.W_pos n) hn.2.2 fx fy hia hib hcov z hadj hfar)
    (fun n z => norm_adjI_le (d.L n) k z) (hsxy x hxg) (hsxy y hyg) hx hy

/-- The numeric threshold: `c₀ ≤ 2k²` gives `4 c₀ (k+2)² ≤ N_min`. -/
theorem nmin_ge {c₀ : ℝ} (hc : c₀ ≤ 2 * ((k : ℝ) * k)) : c₀ * (4 * ((k : ℝ) + 2) ^ 2) ≤ Nmin k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (k : ℝ) * k ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) ≤ 4 * ((k : ℝ) + 2) ^ 2 := by positivity
  have h3 : 2 * ((k : ℝ) * k) * (4 * ((k : ℝ) + 2) ^ 2) ≤ 8 * ((k : ℝ) + 2) ^ 4 := by
    have : 2 * ((k : ℝ) * k) ≤ 2 * ((k : ℝ) + 2) ^ 2 := by linarith
    calc 2 * ((k : ℝ) * k) * (4 * ((k : ℝ) + 2) ^ 2) ≤ 2 * ((k : ℝ) + 2) ^ 2 * (4 * ((k : ℝ) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_right this h2
      _ = 8 * ((k : ℝ) + 2) ^ 4 := by ring
  unfold Nmin
  have := C5_pos
  calc c₀ * (4 * ((k : ℝ) + 2) ^ 2) ≤ 2 * ((k : ℝ) * k) * (4 * ((k : ℝ) + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hc h2
    _ ≤ 8 * ((k : ℝ) + 2) ^ 4 := h3
    _ ≤ 8 * ((k : ℝ) + 2) ^ 4 + C5 := by linarith

theorem two_le_nmin : (2 : ℝ) ≤ Nmin k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2k : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have h4 : (2 : ℝ) ^ 4 ≤ ((k : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) h2k 4
  have h5 := C5_pos
  unfold Nmin
  norm_num at h4
  linarith

/-! ### `m = 2`: `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` -/

/-- The term of `B₂` at the cut `p = (k', l')`: `1(|a'-b'| ≤ 1) (𝓛-𝒦)(𝒢^L) (𝓛-𝒦)(𝒢^R)`. -/
def termTwo (σ : ∀ n : ℕ, Fin k → Bool) (p : Σ _ : ℕ, ℕ) :
    Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  if h : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k then
    prodTerm (Fac.lk (m := p.1 + k - p.2) (by omega) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
      (Fac.lk (m := p.2 - p.1) (by omega) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2))
  else Fac.zero d

/-- The tensor `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` as a sum of the terms at all cuts. -/
def xTwo (σ : ∀ n : ℕ, Fin k → Bool) : Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  Fac.sum (pairsK k) (termTwo σ)

theorem termTwo_eq {σ : ∀ n : ℕ, Fin k → Bool} {p : Σ _ : ℕ, ℕ}
    (hp : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k) :
    termTwo (d := d) (E := E) (u := u) σ p =
      prodTerm (Fac.lk (m := p.1 + k - p.2) (by omega) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
        (Fac.lk (m := p.2 - p.1) (by omega) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2)) := by
  unfold termTwo
  simp [hp]

theorem xTwo_T (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d) (z : Fin (k + 2) → Z2 (d.L n)) :
    (xTwo (E := E) (u := u) σ).T n ω z = ∑ p ∈ pairsK k, adjI (d.L n) k z *
      (lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (sL (σ n) p.1 p.2)
          (fun i => z (fL k p.1 p.2 i)) *
        lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (sR (σ n) p.1 p.2)
          (fun i => z (fR k p.1 p.2 i))) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [termTwo_eq (mem_pairsK.mp hp)]
  rfl

theorem hid_two (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d) (a : Fin k → Z2 (d.L n)) :
    altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) 2 a =
      ∑ z, cutKerW (d.L n) (d.W n) a z * (xTwo (E := E) (u := u) σ).T n ω z := by
  change elklkN (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (loopOf (σ n) a) = _
  rw [elklkN_eq (d.three_le_L n)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [xTwo_T]

theorem termBd_two (σ : ∀ n : ℕ, Fin k → Bool) :
    TermBd Nm τ₀ ((k : ℝ) * k) (xTwo (d := d) (E := E) (u := u) σ) := by
  have hcard : ((pairsK k).card : ℝ) ≤ (k : ℝ) * k := by exact_mod_cast card_pairsK_le
  refine termBd_mono hcard (termBd_sum (pairsK k) (termTwo σ) ?_)
  intro p hp
  have hp' := mem_pairsK.mp hp
  rw [termTwo_eq hp']
  exact termBd_prod (goodFac_lk _ _ _) (goodFac_lk _ _ _)

theorem farPT_two {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hdl : DecayLoopPT d E s t) {u : ℕ → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hu : ∀ n, s n ≤ u n)
    (hut : ∀ n, u n ≤ t n) {D : ℝ} (hD : 0 < D) (σ : ∀ n : ℕ, Fin k → Bool) :
    FarPT d (xTwo (E := E) (u := u) σ).T (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8) D := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  refine farPT_sum d hsize (pairsK k) (termTwo σ) _ (fun p hp => ?_)
  have hp' := mem_pairsK.mp hp
  rw [termTwo_eq hp']
  have hD'' : 0 < D + ((k + 3 : ℕ) : ℝ) / c := by positivity
  have hxf := farPiece_lk d hdl hu hut (m := p.1 + k - p.2) (K := k + 1) (by omega)
    (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
  have hyf := farPiece_lk d hdl hu hut (m := p.2 - p.1) (K := k + 1) (by omega)
    (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
  have h := farPT_term hmain hτ₀ hu hut (Nm := Nmin k) two_le_nmin (goodFac_lk _ _ _)
    (goodFac_lk _ _ _) (fL k p.1 p.2) (fR k p.1 p.2) (exists_fL_a hp'.1 hp'.2.1 hp'.2.2)
    (exists_fR_b hp'.1 hp'.2.1 hp'.2.2) (cover_LR hp'.1 hp'.2.1 hp'.2.2) hxf hyf
  rwa [add_sub_cancel_right] at h

/-! ### `m = 3`: `𝓔^{(G̃)}` -/

/-- The term of `B₃` at the cut edge `k'`: `1(|a'-b'| ≤ 1) avgErr(σ_{k'-1}, a') 𝓛(𝒢_{k'}^{(b')})`. -/
def term3 (σ : ∀ n : ℕ, Fin k → Bool) (k' : ℕ) : Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  if h : 1 ≤ k' ∧ k' ≤ k then
    prodTerm (Fac.lk (m := 0) (by omega) (fun n => fun _ => sx (σ n) (k' - 1)) (fA k))
      (Fac.loop (m := k) (by omega) (fun n => s3 (σ n) k') (f3 k k'))
  else Fac.zero d

/-- The tensor `𝓔^{(G̃)}` as a sum of the terms at all cut edges. -/
def xThree (σ : ∀ n : ℕ, Fin k → Bool) : Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  Fac.sum (Finset.Icc 1 k) (term3 σ)

theorem term3_eq {σ : ∀ n : ℕ, Fin k → Bool} {k' : ℕ} (hp : 1 ≤ k' ∧ k' ≤ k) :
    term3 (d := d) (E := E) (u := u) σ k' =
      prodTerm (Fac.lk (m := 0) (by omega) (fun n => fun _ => sx (σ n) (k' - 1)) (fA k))
        (Fac.loop (m := k) (by omega) (fun n => s3 (σ n) k') (f3 k k')) := by
  unfold term3
  simp [hp]

theorem xThree_T (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d)
    (z : Fin (k + 2) → Z2 (d.L n)) :
    (xThree (E := E) (u := u) σ).T n ω z = ∑ k' ∈ Finset.Icc 1 k, adjI (d.L n) k z *
      (lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
          (fun _ : Fin 1 => sx (σ n) (k' - 1)) (fun i => z (fA k i)) *
        LLf (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
          (loopOf (s3 (σ n) k') (fun i => z (f3 k k' i)))) := by
  change ∑ k' ∈ Finset.Icc 1 k, (term3 (d := d) (E := E) (u := u) σ k').T n ω z = _
  refine Finset.sum_congr rfl fun k' hk' => ?_
  rw [term3_eq (Finset.mem_Icc.mp hk')]
  rfl

theorem hid_three (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d) (a : Fin k → Z2 (d.L n)) :
    altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) 3 a =
      ∑ z, cutKerW (d.L n) (d.W n) a z * (xThree (E := E) (u := u) σ).T n ω z := by
  change egtN (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (loopOf (σ n) a) = _
  rw [egtN_eq (d.three_le_L n)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [xThree_T]

theorem termBd_three (hk1 : 1 ≤ k) (σ : ∀ n : ℕ, Fin k → Bool) :
    TermBd Nm τ₀ (k : ℝ) (xThree (d := d) (E := E) (u := u) σ) := by
  have hcard : ((Finset.Icc 1 k).card : ℝ) ≤ (k : ℝ) := by simp
  refine termBd_mono hcard (termBd_sum (Finset.Icc 1 k) (term3 σ) ?_)
  intro p hp
  have hp' := Finset.mem_Icc.mp hp
  rw [term3_eq hp']
  exact termBd_prod (goodFac_lk _ _ _) (goodFac_loop _ _ _)

theorem farPT_three {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hdl : DecayLoopPT d E s t) {u : ℕ → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hu : ∀ n, s n ≤ u n)
    (hut : ∀ n, u n ≤ t n) {D : ℝ} (hD : 0 < D) (σ : ∀ n : ℕ, Fin k → Bool) :
    FarPT d (xThree (E := E) (u := u) σ).T
      (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8) D := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  refine farPT_sum d hsize (Finset.Icc 1 k) (term3 σ) _ (fun p hp => ?_)
  have hp' := Finset.mem_Icc.mp hp
  rw [term3_eq hp']
  have hD'' : 0 < D + ((k + 3 : ℕ) : ℝ) / c := by positivity
  have hxf := farPiece_lk d hdl hu hut (m := 0) (K := k + 1) (by omega)
    (fun n => fun _ => sx (σ n) (p - 1)) (fA k) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
  have hyf := farPiece_loop d hdl hu hut (m := k) (K := k + 1) (by omega)
    (fun n => s3 (σ n) p) (f3 k p) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
  have h := farPT_term hmain hτ₀ hu hut (Nm := Nmin k) two_le_nmin (goodFac_lk _ _ _)
    (goodFac_loop _ _ _) (fA k) (f3 k p) exists_fA_a (exists_f3_b hp'.1 hp'.2)
    (cover_A3 hp'.1 hp'.2) hxf hyf
  rwa [add_sub_cancel_right] at h

/-! ### `m = 1`: `Σ_{l ≥ 3} [𝒦 ∼ (𝓛-𝒦)]^l` -/

/-- The term of `B₁` at the cut `p = (k', l')`, `𝒦` on the right: `1(|a'-b'| ≤ 1) (𝓛-𝒦)(𝒢^L) 𝒦(𝒢^R)`. -/
def termOneA (σ : ∀ n : ℕ, Fin k → Bool) (p : Σ _ : ℕ, ℕ) :
    Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  if h : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k then
    prodTerm (Fac.lk (m := p.1 + k - p.2) (by omega) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
      (Fac.kcal (m := p.2 - p.1) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2))
  else Fac.zero d

/-- The term of `B₁` at the cut `p = (k', l')`, `𝒦` on the left: `1(|a'-b'| ≤ 1) 𝒦(𝒢^L) (𝓛-𝒦)(𝒢^R)`. -/
def termOneB (σ : ∀ n : ℕ, Fin k → Bool) (p : Σ _ : ℕ, ℕ) :
    Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  if h : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k then
    prodTerm (Fac.kcal (m := p.1 + k - p.2) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
      (Fac.lk (m := p.2 - p.1) (by omega) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2))
  else Fac.zero d

/-- The cuts with `𝒦` of length `≥ 3` on the right. -/
def pairsA (k : ℕ) : Finset (Σ _ : ℕ, ℕ) := (pairsK k).filter (fun p => 3 ≤ p.2 - p.1 + 1)

/-- The cuts with `𝒦` of length `≥ 3` on the left. -/
def pairsB (k : ℕ) : Finset (Σ _ : ℕ, ℕ) := (pairsK k).filter (fun p => 3 ≤ p.1 + k - p.2 + 1)

/-- The tensor `Σ_{l ≥ 3}[𝒦 ∼ (𝓛-𝒦)]^l` as a sum of the terms of both orders. -/
def xOne (σ : ∀ n : ℕ, Fin k → Bool) : Fac d E u (k + 2) ((k + 1) + (k + 1)) :=
  Fac.add (Fac.sum (pairsA k) (termOneA σ)) (Fac.sum (pairsB k) (termOneB σ))

theorem termOneA_eq {σ : ∀ n : ℕ, Fin k → Bool} {p : Σ _ : ℕ, ℕ}
    (hp : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k) :
    termOneA (d := d) (E := E) (u := u) σ p =
      prodTerm (Fac.lk (m := p.1 + k - p.2) (by omega) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
        (Fac.kcal (m := p.2 - p.1) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2)) := by
  unfold termOneA
  simp [hp]

theorem termOneB_eq {σ : ∀ n : ℕ, Fin k → Bool} {p : Σ _ : ℕ, ℕ}
    (hp : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k) :
    termOneB (d := d) (E := E) (u := u) σ p =
      prodTerm (Fac.kcal (m := p.1 + k - p.2) (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2))
        (Fac.lk (m := p.2 - p.1) (by omega) (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2)) := by
  unfold termOneB
  simp [hp]

theorem mem_pairsA {p : Σ _ : ℕ, ℕ} (hp : p ∈ pairsA k) : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k :=
  mem_pairsK.mp (Finset.mem_filter.mp hp).1

theorem mem_pairsB {p : Σ _ : ℕ, ℕ} (hp : p ∈ pairsB k) : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k :=
  mem_pairsK.mp (Finset.mem_filter.mp hp).1

theorem xOne_T (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d) (z : Fin (k + 2) → Z2 (d.L n)) :
    (xOne (E := E) (u := u) σ).T n ω z =
      (∑ p ∈ (pairsK k).filter (fun p => 3 ≤ p.2 - p.1 + 1), adjI (d.L n) k z *
        (lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (sL (σ n) p.1 p.2)
            (fun i => z (fL k p.1 p.2 i)) *
          KLoop.Kcal (d.L n) (d.W n) (E n) (u n)
            (loopOf (sR (σ n) p.1 p.2) (fun i => z (fR k p.1 p.2 i))))) +
      ∑ p ∈ (pairsK k).filter (fun p => 3 ≤ p.1 + k - p.2 + 1), adjI (d.L n) k z *
        (KLoop.Kcal (d.L n) (d.W n) (E n) (u n)
            (loopOf (sL (σ n) p.1 p.2) (fun i => z (fL k p.1 p.2 i))) *
          lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (sR (σ n) p.1 p.2)
            (fun i => z (fR k p.1 p.2 i))) := by
  change (∑ p ∈ pairsA k, (termOneA (d := d) (E := E) (u := u) σ p).T n ω z) +
    ∑ p ∈ pairsB k, (termOneB (d := d) (E := E) (u := u) σ p).T n ω z = _
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [termOneA_eq (mem_pairsA hp)]
    rfl
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [termOneB_eq (mem_pairsB hp)]
    rfl

theorem hid_one (σ : ∀ n : ℕ, Fin k → Bool) (n : ℕ) (ω : Sizes.SeqΩ d) (a : Fin k → Z2 (d.L n)) :
    altB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) 1 a =
      ∑ z, cutKerW (d.L n) (d.W n) a z * (xOne (E := E) (u := u) σ).T n ω z := by
  change ∑ l ∈ Finset.Icc 3 k, ksimLK (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) l
    (loopOf (σ n) a) = _
  rw [ksimLK_eq (d.three_le_L n)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [xOne_T]

theorem termBd_one (σ : ∀ n : ℕ, Fin k → Bool) :
    TermBd Nm τ₀ (2 * ((k : ℝ) * k)) (xOne (d := d) (E := E) (u := u) σ) := by
  have hcard : ∀ s : Finset (Σ _ : ℕ, ℕ), s ⊆ pairsK k → (s.card : ℝ) ≤ (k : ℝ) * k := fun s hs => by
    have := (Finset.card_le_card hs).trans card_pairsK_le
    exact_mod_cast this
  have hA : TermBd Nm τ₀ (k * k : ℝ) (Fac.sum (pairsA k) (termOneA (d := d) (E := E) (u := u) σ)) := by
    refine termBd_mono (hcard _ (Finset.filter_subset _ _)) (termBd_sum (pairsA k) _ ?_)
    intro p hp
    have hp' := mem_pairsA hp
    rw [termOneA_eq hp']
    exact termBd_prod (goodFac_lk _ _ _) (goodFac_kcal (by omega) _ _)
  have hB : TermBd Nm τ₀ (k * k : ℝ) (Fac.sum (pairsB k) (termOneB (d := d) (E := E) (u := u) σ)) := by
    refine termBd_mono (hcard _ (Finset.filter_subset _ _)) (termBd_sum (pairsB k) _ ?_)
    intro p hp
    have hp' := mem_pairsB hp
    rw [termOneB_eq hp']
    exact termBd_prod (goodFac_kcal (by omega) _ _) (goodFac_lk _ _ _)
  have := termBd_add hA hB
  rwa [show ((k : ℝ) * k + (k : ℝ) * k) = 2 * ((k : ℝ) * k) by ring] at this

theorem farPT_one {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hdl : DecayLoopPT d E s t) (hK : KcalDecay κ) {u : ℕ → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) {D : ℝ} (hD : 0 < D)
    (σ : ∀ n : ℕ, Fin k → Bool) :
    FarPT d (xOne (E := E) (u := u) σ).T
      (fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8) D := by
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  have hD'' : 0 < D + ((k + 3 : ℕ) : ℝ) / c := by positivity
  refine farPT_add d hsize _ _ _ (farPT_sum d hsize (pairsA k) (termOneA σ) _ (fun p hp => ?_))
    (farPT_sum d hsize (pairsB k) (termOneB σ) _ (fun p hp => ?_))
  · have hp' := mem_pairsA hp
    rw [termOneA_eq hp']
    have hxf := farPiece_lk d hdl hu hut (m := p.1 + k - p.2) (K := k + 1) (by omega)
      (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
    have hyf := farPiece_kcal d hmain hK hu hut (m := p.2 - p.1) (K := k + 1)
      (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
    have h := farPT_term hmain hτ₀ hu hut (Nm := Nmin k) two_le_nmin (goodFac_lk _ _ _)
      (goodFac_kcal (by omega) _ _) (fL k p.1 p.2) (fR k p.1 p.2)
      (exists_fL_a hp'.1 hp'.2.1 hp'.2.2) (exists_fR_b hp'.1 hp'.2.1 hp'.2.2)
      (cover_LR hp'.1 hp'.2.1 hp'.2.2) hxf hyf
    rwa [add_sub_cancel_right] at h
  · have hp' := mem_pairsB hp
    rw [termOneB_eq hp']
    have hxf := farPiece_kcal d hmain hK hu hut (m := p.1 + k - p.2) (K := k + 1)
      (fun n => sL (σ n) p.1 p.2) (fL k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
    have hyf := farPiece_lk d hdl hu hut (m := p.2 - p.1) (K := k + 1) (by omega)
      (fun n => sR (σ n) p.1 p.2) (fR k p.1 p.2) (τ' := τ₀ / 2) (half_pos hτ₀) hD''
    have h := farPT_term hmain hτ₀ hu hut (Nm := Nmin k) two_le_nmin (goodFac_kcal (by omega) _ _)
      (goodFac_lk _ _ _) (fL k p.1 p.2) (fR k p.1 p.2)
      (exists_fL_a hp'.1 hp'.2.1 hp'.2.2) (exists_fR_b hp'.1 hp'.2.1 hp'.2.2)
      (cover_LR hp'.1 hp'.2.1 hp'.2.2) hxf hyf
    rwa [add_sub_cancel_right] at h

end Cases

end LocalFormCuts

variable (d : Sizes)

/-- **`AltLocalFormAt` at `m = 1`**: a local form of `𝒬_u Σ_{l ≥ 3}[𝒦 ∼ (𝓛-𝒦)]^l` (`B₁`, `ksimLK`): the tensor is a sum over the
cuts `1 ≤ k' < l' ≤ k` (with `𝒦` of length `≥ 3` on one side) of `1(|a'-b'| ≤ 1)` times the product of a piece
`𝓛-𝒦` and a piece `𝒦`, contracted with `W² S^{(B)}`; the far part of `𝒦` is `KcalDecay`. -/
theorem altLocalFormAt_one {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 1 := by
  intro hmain hdl hK k _ hk τ₀ D₀ hτ₀ hD₀
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  refine ⟨(k + 1) + (k + 1), ((4 * k + 9 : ℕ) : ℝ), by positivity, fun u σ hu hut hσ => ?_⟩
  have hb := LocalFormCuts.termBd_final (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) (E := E) (u := u)
    (d := d) (c₀ := 2 * ((k : ℝ) * k)) (by positivity) (LocalFormCuts.nmin_ge le_rfl) rfl
    (LocalFormCuts.termBd_one (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) σ)
  exact LocalFormCuts.cutAssembly d hmain hk hτ₀ hD₀ hu hut 1 σ (LocalFormCuts.xOne σ)
    (LocalFormCuts.hid_one σ) hb.1 hb.2
    (LocalFormCuts.farPT_one hmain hdl hK hτ₀ hu hut (by positivity) σ)


/-- **`AltLocalFormAt` at `m = 2`**: a local form of `𝒬_u 𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` (`B₂`, `elklkN`): the tensor is a sum over the
cuts `1 ≤ k' < l' ≤ k` of `1(|a'-b'| ≤ 1)(𝓛-𝒦)(𝒢^L)(𝓛-𝒦)(𝒢^R)`, contracted with `W² S^{(B)}`. -/
theorem altLocalFormAt_two {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 2 := by
  intro hmain hdl hK k _ hk τ₀ D₀ hτ₀ hD₀
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  refine ⟨(k + 1) + (k + 1), ((4 * k + 9 : ℕ) : ℝ), by positivity, fun u σ hu hut hσ => ?_⟩
  have hkk : (0 : ℝ) ≤ (k : ℝ) * k := by positivity
  have hb := LocalFormCuts.termBd_final (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) (E := E) (u := u)
    (d := d) (c₀ := (k : ℝ) * k) hkk (LocalFormCuts.nmin_ge (by linarith)) rfl
    (LocalFormCuts.termBd_two (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) σ)
  exact LocalFormCuts.cutAssembly d hmain hk hτ₀ hD₀ hu hut 2 σ (LocalFormCuts.xTwo σ)
    (LocalFormCuts.hid_two σ) hb.1 hb.2
    (LocalFormCuts.farPT_two hmain hdl hτ₀ hu hut (by positivity) σ)


/-- **`AltLocalFormAt` at `m = 3`**: a local form of `𝒬_u 𝓔^{(G̃)}` (`B₃`, `egtN`): the tensor is a sum over the cut edges
`k' ∈ [1,k]` of `1(|a'-b'| ≤ 1) avgErr_{σ_{k'-1}}(a') 𝓛(𝒢_{k'}^{(b')})`, contracted with `W² S^{(B)}`. -/
theorem altLocalFormAt_three {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 3 := by
  intro hmain hdl hK k _ hk τ₀ D₀ hτ₀ hD₀
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain'
  refine ⟨(k + 1) + (k + 1), ((4 * k + 9 : ℕ) : ℝ), by positivity, fun u σ hu hut hσ => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hb := LocalFormCuts.termBd_final (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) (E := E) (u := u)
    (d := d) (c₀ := (k : ℝ)) hkk (LocalFormCuts.nmin_ge (by nlinarith))
    rfl (LocalFormCuts.termBd_three (Nm := LocalFormCuts.Nmin k) (τ₀ := τ₀) (by omega) σ)
  exact LocalFormCuts.cutAssembly d hmain hk hτ₀ hD₀ hu hut 3 σ (LocalFormCuts.xThree σ)
    (LocalFormCuts.hid_three σ) hb.1 hb.2
    (LocalFormCuts.farPT_three hmain hdl hτ₀ hu hut (by positivity) σ)


end RBM.Ind

end
