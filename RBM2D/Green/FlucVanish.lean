/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.CondRow
import RBM2D.Green.EntryBlock

/-!
# Fluctuation averaging, base layer: the vanishing lemma and the uniform weights

The paper (arXiv:2503.07606) does not state these lemmas: the estimates on `G_t` "follow that of
Lemma 4.2 in [YY_25]" (Section "Estimates for entries of `G`"), and the fluctuation averaging
behind (`GavLGEX`) is proved internally.

Everything lives at one slice `n` of a size sequence `d : Sizes`, on the fine index
`Idx (d.L n) (d.W n) = Z2 (W L)`, with `E_k = condRow d n k` and the variance `svar`.

* `sub_smul_one_apply` : `(A - m • 1)_{ij} = A_{ij} - [i = j] m`.
* `finDepOffRow_const`, `FinDepOffRow.mul`, `FinDepOffRow.sub`, `finDepOffRow_prod`,
  `finDepOffRow_condRow` : closure properties of `FinDepOffRow`.
* `integral_mul_prod_eq_zero` : **the vanishing lemma** — if every factor but one is
  independent of row `κ` and `E_κ` kills the remaining one, the expectation is `0`.
* `greenDiagCentered`, `flucDiag`, `greenMinorDiagCentered`, `flucDiagMinor` :
  `Z_k = (1 - E_k)(G_{kk} - m)` and its `G^{(κ)}` replacement, with the bounds
  `norm_flucDiag_sub_flucDiagMinor_le`, `norm_sub_condRow_le`, `norm_flucDiag_le`,
  `norm_flucDiagMinor_le`.
* `UniformWeight`, `epsHom`, `prod_epsHom`, `prod_epsHom_sum_eq`, `flucAvg` : the counting
  interface.
* `uniformWeight_svar`, `uniformWeight_blockAvg2` : the two d = 2 weight families, the row
  `j ↦ S_{ij}` (weight `(5W²)⁻¹` on the five neighbouring blocks) and the block average
  `k ↦ W⁻² 1(k ∈ 𝓘_a)` (weight `W⁻²` on the `W²` sites of block `a`).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

/-! ### `(A - m • 1)_{ij}` -/

section Det

variable {n : Type*} [DecidableEq n]

/-- Entries of `G - m` are `G_{ij} - m δ_{ij}`. -/
theorem sub_smul_one_apply (A : Matrix n n ℂ) (m : ℂ) (i j : n) :
    (A - m • (1 : Matrix n n ℂ)) i j = A i j - (if i = j then m else 0) := by
  by_cases h : i = j
  · subst h
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, h]

end Det

variable {d : Sizes} {n : ℕ}

/-! ### Closure properties of `FinDepOffRow` -/

theorem finDepOffRow_const (k : Idx (d.L n) (d.W n)) {V : Type*} (v : V) :
    FinDepOffRow d n k (fun _ : Sizes.SeqΩ d => v) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem FinDepOffRow.mul {k : Idx (d.L n) (d.W n)} {X Y : Sizes.SeqΩ d → ℂ}
    (hX : FinDepOffRow d n k X)
    (hY : FinDepOffRow d n k Y) : FinDepOffRow d n k fun ω => X ω * Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · change X ω * Y ω = X ω' * Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

theorem FinDepOffRow.sub {k : Idx (d.L n) (d.W n)} {X Y : Sizes.SeqΩ d → ℂ}
    (hX : FinDepOffRow d n k X)
    (hY : FinDepOffRow d n k Y) : FinDepOffRow d n k fun ω => X ω - Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · change X ω - Y ω = X ω' - Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

/-- **A finite product of factors independent of row `k` is independent of row `k`.** -/
theorem finDepOffRow_prod {k : Idx (d.L n) (d.W n)} {ι : Type*} (s : Finset ι)
    {f : ι → Sizes.SeqΩ d → ℂ}
    (hf : ∀ i ∈ s, FinDepOffRow d n k (f i)) :
    FinDepOffRow d n k fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simpa using finDepOffRow_const k (1 : ℂ)
  | cons j t hj ih =>
      have hjf : FinDepOffRow d n k (f j) := hf j (Finset.mem_cons_self _ _)
      have ht : FinDepOffRow d n k fun ω => ∏ i ∈ t, f i ω :=
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      have := hjf.mul ht
      simpa only [Finset.prod_cons] using this

/-- **`E_{k'}` preserves independence of row `k`.** -/
theorem finDepOffRow_condRow {k k' : Idx (d.L n) (d.W n)} {X : Sizes.SeqΩ d → ℂ}
    (h : FinDepOffRow d n k X) :
    FinDepOffRow d n k (condRow d n k' X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord d n k' c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d n k' c
  · rw [rowSplit_apply_of_isRowCoord k' ω ω'' hcr, rowSplit_apply_of_isRowCoord k' ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k' ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k' ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

/-! ### Integrability from measurability and a uniform bound -/

/-- A bounded measurable function on the Gaussian product space is integrable. -/
theorem integrable_P_of_measurable_of_bound {f : Sizes.SeqΩ d → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (Sizes.seqP d) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-! ### The vanishing lemma, abstract form -/

section Vanish

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The vanishing itself.**  If every factor other than the distinguished one is strictly
independent of row `κ`, and the distinguished factor is killed by `E_κ`, then the expectation
of the product is exactly `0`. -/
theorem integral_mul_prod_eq_zero {κ : Idx (d.L n) (d.W n)} {i₀ : ι}
    {Z Y : ι → Sizes.SeqΩ d → ℂ}
    (hZ0 : condRow d n κ (Z i₀) = 0)
    (hY : ∀ i ∈ Finset.univ.erase i₀, FinDepOffRow d n κ (Y i))
    (hint : Integrable (fun ω => Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω) (Sizes.seqP d)) :
    ∫ ω, Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω ∂(Sizes.seqP d) = 0 := by
  have hprod : FinDepOffRow d n κ fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω :=
    finDepOffRow_prod _ hY
  have hpull := condRow_mul_of_finDepOffRow' (X := Z i₀)
    (Y := fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω) hprod
  rw [← integral_condRow κ hint, hpull]
  simp [hZ0]

end Vanish

/-! ### The concrete fluctuation `Z_k = (1 - E_k)(G_{kk} - m)` -/

/-- The centred diagonal Green function entry, `G_{kk} - m`. -/
noncomputable def greenDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) : Sizes.SeqΩ d → ℂ :=
  fun ω => green (Sizes.seqHflow d n u ω) z k k - m

/-- **`Z_k := (1 - E_k)(G_{kk} - m)`**, the fluctuation. -/
noncomputable def flucDiag (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx (d.L n) (d.W n)) :
    Sizes.SeqΩ d → ℂ :=
  fun ω => greenDiagCentered d n u z m k ω - condRow d n k (greenDiagCentered d n u z m k) ω

/-- The centred diagonal entry of the **minor** resolvent, `G^{(κ)}_{kk} - m`. -/
noncomputable def greenMinorDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx (d.L n) (d.W n)) (k : {a : Idx (d.L n) (d.W n) // a ≠ κ}) : Sizes.SeqΩ d → ℂ :=
  fun ω => greenMinorMat d n u z κ ω k k - m

/-- **`Z^{(κ)}_k := (1 - E_k)(G^{(κ)}_{kk} - m)`**, the replaced fluctuation. -/
noncomputable def flucDiagMinor (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx (d.L n) (d.W n)) (k : {a : Idx (d.L n) (d.W n) // a ≠ κ}) : Sizes.SeqΩ d → ℂ :=
  fun ω => greenMinorDiagCentered d n u z m κ k ω
    - condRow d n k.1 (greenMinorDiagCentered d n u z m κ k) ω

/-- **The replacement error of a factor**, in terms of the replacement error of the Green
function entry; the factor `2` is the price of the `(1 - E_k)`. -/
theorem norm_flucDiag_sub_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : Idx (d.L n) (d.W n)}
    {k : {a : Idx (d.L n) (d.W n) // a ≠ κ}} {e : ℝ}
    (hrow : RowIntegrable d n k.1 (greenDiagCentered d n u z m k.1))
    (hrow' : RowIntegrable d n k.1 (greenMinorDiagCentered d n u z m κ k))
    (he : ∀ ω, ‖green (Sizes.seqHflow d n u ω) z k.1 k.1 - greenMinorMat d n u z κ ω k k‖ ≤ e)
    (ω : Sizes.SeqΩ d) :
    ‖flucDiag d n u z m k.1 ω - flucDiagMinor d n u z m κ k ω‖ ≤ 2 * e := by
  have hD : ∀ ω' : Sizes.SeqΩ d, greenDiagCentered d n u z m k.1 ω'
      - greenMinorDiagCentered d n u z m κ k ω'
      = green (Sizes.seqHflow d n u ω') z k.1 k.1 - greenMinorMat d n u z κ ω' k k := by
    intro ω'
    simp only [greenDiagCentered, greenMinorDiagCentered]
    ring
  have hcond := condRow_sub k.1 hrow hrow'
  have hcondpt : condRow d n k.1 (greenDiagCentered d n u z m k.1) ω
      - condRow d n k.1 (greenMinorDiagCentered d n u z m κ k) ω
      = condRow d n k.1 (fun ω' => green (Sizes.seqHflow d n u ω') z k.1 k.1
          - greenMinorMat d n u z κ ω' k k) ω := by
    have := congrFun hcond ω
    rw [← this]
    simp only [condRow_apply, hD]
  have hbound : ‖condRow d n k.1 (fun ω' => green (Sizes.seqHflow d n u ω') z k.1 k.1
      - greenMinorMat d n u z κ ω' k k) ω‖ ≤ e := by
    rw [condRow_apply]
    have := norm_integral_le_of_norm_le_const (μ := Sizes.seqP d)
      (f := fun ω' => green (Sizes.seqHflow d n u (rowSplit d n k.1 ω ω')) z k.1 k.1
        - greenMinorMat d n u z κ (rowSplit d n k.1 ω ω') k k)
      (C := e) (Filter.Eventually.of_forall fun ω' => he _)
    simpa using this
  have hsplit : flucDiag d n u z m k.1 ω - flucDiagMinor d n u z m κ k ω
      = (green (Sizes.seqHflow d n u ω) z k.1 k.1 - greenMinorMat d n u z κ ω k k)
        - condRow d n k.1 (fun ω' => green (Sizes.seqHflow d n u ω') z k.1 k.1
            - greenMinorMat d n u z κ ω' k k) ω := by
    rw [← hcondpt, ← hD ω]
    simp only [flucDiag, flucDiagMinor]
    ring
  rw [hsplit]
  calc ‖(green (Sizes.seqHflow d n u ω) z k.1 k.1 - greenMinorMat d n u z κ ω k k)
        - condRow d n k.1 (fun ω' => green (Sizes.seqHflow d n u ω') z k.1 k.1
            - greenMinorMat d n u z κ ω' k k) ω‖
      ≤ ‖green (Sizes.seqHflow d n u ω) z k.1 k.1 - greenMinorMat d n u z κ ω k k‖
        + ‖condRow d n k.1 (fun ω' => green (Sizes.seqHflow d n u ω') z k.1 k.1
            - greenMinorMat d n u z κ ω' k k) ω‖ := norm_sub_le _ _
    _ ≤ e + e := add_le_add (he ω) hbound
    _ = 2 * e := by ring

/-- **A uniform bound survives `(1 - E_k)`, at the cost of a factor `2`.** -/
theorem norm_sub_condRow_le {k : Idx (d.L n) (d.W n)} {X : Sizes.SeqΩ d → ℂ} {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b)
    (ω : Sizes.SeqΩ d) : ‖X ω - condRow d n k X ω‖ ≤ 2 * b := by
  have h1 : ‖condRow d n k X ω‖ ≤ b := by
    rw [condRow_apply]
    simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP d)
      (f := fun ω' => X (rowSplit d n k ω ω')) (C := b)
      (Filter.Eventually.of_forall fun ω' => hX _)
  calc ‖X ω - condRow d n k X ω‖ ≤ ‖X ω‖ + ‖condRow d n k X ω‖ := norm_sub_le _ _
    _ ≤ b + b := add_le_add (hX ω) h1
    _ = 2 * b := by ring

/-- `‖Z_k‖ ≤ 2 b` as soon as `‖G_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiag_le {u : ℝ} {z m : ℂ} {k : Idx (d.L n) (d.W n)} {b : ℝ}
    (hb : ∀ ω, ‖greenDiagCentered d n u z m k ω‖ ≤ b) (ω : Sizes.SeqΩ d) :
    ‖flucDiag d n u z m k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

/-- `‖Z^{(κ)}_k‖ ≤ 2 b` as soon as `‖G^{(κ)}_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : Idx (d.L n) (d.W n)}
    {k : {a : Idx (d.L n) (d.W n) // a ≠ κ}}
    {b : ℝ} (hb : ∀ ω, ‖greenMinorDiagCentered d n u z m κ k ω‖ ≤ b) (ω : Sizes.SeqΩ d) :
    ‖flucDiagMinor d n u z m κ k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

/-! ### Uniform weights -/

section Counting

variable {κ : Type*}

/-- **A uniform weight**: `t_k = c` on a set `A` and `0` off it, with total mass `c · #A ≤ 1`.
Both coefficient families of the fluctuation averaging are of this shape. -/
structure UniformWeight (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where
  /-- The common value is nonnegative. -/
  nonneg : 0 ≤ c
  /-- `t` is `c` on `A` … -/
  mem : ∀ k ∈ A, t k = c
  /-- … and `0` off it. -/
  not_mem : ∀ k ∉ A, t k = 0
  /-- Total mass at most one, the normalization `∑_k |t_k| ≤ 1`. -/
  mass : c * A.card ≤ 1

end Counting

/-! ### The conjugation pattern -/

section Eps

/-- The ring homomorphism attached to the slot `i`: the identity on the left summand, complex
conjugation on the right. -/
def epsHom (p : ℕ) : (Fin p ⊕ Fin p) → (ℂ →+* ℂ) :=
  Sum.elim (fun _ => RingHom.id ℂ) fun _ => starRingEnd ℂ

@[simp] theorem norm_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) (w : ℂ) : ‖epsHom p i w‖ = ‖w‖ := by
  cases i <;> simp [epsHom]

@[simp] theorem epsHom_ofReal (p : ℕ) (i : Fin p ⊕ Fin p) (r : ℝ) :
    epsHom p i (r : ℂ) = (r : ℂ) := by
  cases i <;> simp [epsHom]

theorem measurable_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) : Measurable (epsHom p i) := by
  cases i with
  | inl _ => exact measurable_id
  | inr _ => exact Complex.continuous_conj.measurable

/-- **`|w|^{2p}` as a product of `2p` factors**, `p` of them conjugated. -/
theorem prod_epsHom (p : ℕ) (w : ℂ) : ∏ i, epsHom p i w = ((‖w‖ ^ (2 * p) : ℝ) : ℂ) := by
  rw [Fintype.prod_sum_type]
  simp only [epsHom, Sum.elim_inl, Sum.elim_inr, RingHom.id_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj', ← pow_mul]
  push_cast
  ring

/-- **The multi-index expansion** of `|∑_k t_k Z_k|^{2p}`. -/
theorem prod_epsHom_sum_eq (p : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (Z : κ → ℂ) :
    ((‖∑ k, (t k : ℂ) * Z k‖ ^ (2 * p) : ℝ) : ℂ)
      = ∑ v : (Fin p ⊕ Fin p) → κ,
          (∏ i, (t (v i) : ℂ)) * ∏ i, epsHom p i (Z (v i)) := by
  classical
  rw [← prod_epsHom]
  have h1 : ∀ i : Fin p ⊕ Fin p, epsHom p i (∑ k, (t k : ℂ) * Z k)
      = ∑ k, (t k : ℂ) * epsHom p i (Z k) := by
    intro i
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, epsHom_ofReal]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ : Fin p ⊕ Fin p => (univ : Finset κ))
      fun (i : Fin p ⊕ Fin p) (k : κ) => (t k : ℂ) * epsHom p i (Z k),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun v _ => Finset.prod_mul_distrib

end Eps

/-! ### The weighted fluctuation average -/

/-- `∑_k t_k Z_k` with `Z_k = (1 - E_k)(G_{kk} - m)`, for real weights `t`. -/
noncomputable def flucAvg (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (t : Idx (d.L n) (d.W n) → ℝ) : Sizes.SeqΩ d → ℂ :=
  fun ω => ∑ k, (t k : ℂ) * flucDiag d n u z m k ω

/-! ### The two d = 2 coefficient families

The block of a site `k ∈ Z2 (W L)` is `(blk k.1, blk k.2) ∈ Z2 L`, the first component of
`splitEquiv`.  The row family is `j ↦ svar i j` (the paper's `S_{ij}`), the block family is
`k ↦ W⁻² 1(k ∈ 𝓘_a)` (the diagonal of `E_a`, `Def_matE`). -/

section Families

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- For a set `T` of blocks, the sites whose block lies in `T` number `#T · W²`. -/
theorem flucVanish_card_filter_blk2_mem (T : Finset (Z2 L)) :
    ((univ : Finset (Idx L W)).filter fun k => (blk L W k.1, blk L W k.2) ∈ T).card
      = T.card * W ^ 2 := by
  classical
  have h : ((univ : Finset (Idx L W)).filter
      fun k => (blk L W k.1, blk L W k.2) ∈ T).map (splitEquiv L W).toEmbedding
      = T ×ˢ (univ : Finset (Fin W × Fin W)) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding, Finset.mem_product, and_true]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hp
      refine ⟨(splitEquiv L W).symm p, ?_, (splitEquiv L W).apply_symm_apply p⟩
      have : (blk L W ((splitEquiv L W).symm p).1, blk L W ((splitEquiv L W).symm p).2) = p.1 :=
        congrArg Prod.fst ((splitEquiv L W).apply_symm_apply p)
      rw [this]
      exact hp
  rw [← Finset.card_map, h, Finset.card_product, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, sq]

omit [NeZero W] in
/-- The blocks `b` with `a - b ∈ sbSupport L` are as many as the points of `sbSupport L`. -/
theorem flucVanish_card_filter_sub_mem_sbSupport (a : Z2 L) :
    ((univ : Finset (Z2 L)).filter fun b => a - b ∈ sbSupport L).card = (sbSupport L).card := by
  classical
  have hset : ((univ : Finset (Z2 L)).filter fun b => a - b ∈ sbSupport L)
      = (sbSupport L).image fun s => a - s := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun h => ⟨a - b, h, by abel⟩, ?_⟩
    rintro ⟨s, hs, rfl⟩
    simpa using hs
  rw [hset, Finset.card_image_of_injective _ fun x y h => sub_right_inj.1 h]

omit [NeZero L] [NeZero W] in
/-- `sbSupport L` has at most five points, for every `L`. -/
theorem flucVanish_card_sbSupport_le : (sbSupport L).card ≤ 5 := by
  classical
  unfold sbSupport
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  simp

/-- The support of the row `j ↦ svar i j` has `#(sbSupport L) · W²` sites. -/
theorem flucVanish_card_svarSupport (i : Idx L W) :
    ((univ : Finset (Idx L W)).filter fun j =>
        (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L).card
      = (sbSupport L).card * W ^ 2 := by
  classical
  have hset : ((univ : Finset (Idx L W)).filter fun j =>
        (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L)
      = (univ : Finset (Idx L W)).filter fun j => (blk L W j.1, blk L W j.2) ∈
          (univ : Finset (Z2 L)).filter fun b => (blk L W i.1, blk L W i.2) - b ∈ sbSupport L := by
    ext j
    simp
  rw [hset, flucVanish_card_filter_blk2_mem, flucVanish_card_filter_sub_mem_sbSupport]

/-- For `3 ≤ L` the row `j ↦ svar i j` is supported on exactly `5 W²` sites. -/
theorem flucVanish_card_svarSupport_eq (hL : 3 ≤ L) (i : Idx L W) :
    ((univ : Finset (Idx L W)).filter fun j =>
        (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L).card
      = 5 * W ^ 2 := by
  rw [flucVanish_card_svarSupport, card_sbSupport L hL]

/-- A block has exactly `W²` sites. -/
theorem flucVanish_card_blockSupport (a : Z2 L) :
    ((univ : Finset (Idx L W)).filter fun k => (blk L W k.1, blk L W k.2) = a).card
      = W ^ 2 := by
  classical
  have := flucVanish_card_filter_blk2_mem L W {a}
  simpa using this

/-- **The variance-profile row `t_j = S_{ij} = svar i j`** is a uniform weight: it is
`(5 W²)⁻¹` on the sites of the five blocks neighbouring the block of `i`, and `0` elsewhere. -/
theorem uniformWeight_svar (i : Idx L W) :
    UniformWeight (fun j : Idx L W => svar L W i j) ((5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2)
      ((univ : Finset (Idx L W)).filter fun j =>
        (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L) := by
  classical
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  refine ⟨by positivity, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    unfold svar
    split_ifs
    rfl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    unfold svar
    split_ifs
    rfl
  · rw [flucVanish_card_svarSupport]
    have h5 : ((sbSupport L).card : ℝ) ≤ 5 := by exact_mod_cast flucVanish_card_sbSupport_le L
    push_cast
    have hW2 : (W : ℝ)⁻¹ ^ 2 * (W : ℝ) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hW, one_pow]
    calc (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 * ((sbSupport L).card * (W : ℝ) ^ 2)
        = (5 : ℝ)⁻¹ * ((sbSupport L).card : ℝ) * ((W : ℝ)⁻¹ ^ 2 * (W : ℝ) ^ 2) := by ring
      _ = (5 : ℝ)⁻¹ * ((sbSupport L).card : ℝ) := by rw [hW2, mul_one]
      _ ≤ (5 : ℝ)⁻¹ * 5 := by gcongr
      _ = 1 := by norm_num

/-- **The block average `t_k = W⁻² · 1(k ∈ 𝓘_a)`** is a uniform weight, with weight `W⁻²` on
the `W²` sites of block `a`. -/
theorem uniformWeight_blockAvg2 (a : Z2 L) :
    UniformWeight
      (fun k : Idx L W => if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0)
      ((W : ℝ)⁻¹ ^ 2)
      ((univ : Finset (Idx L W)).filter fun k => (blk L W k.1, blk L W k.2) = a) := by
  classical
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  refine ⟨by positivity, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · simp [(Finset.mem_filter.1 hk).2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [hk]
  · rw [flucVanish_card_blockSupport]
    push_cast
    rw [← mul_pow, inv_mul_cancel₀ hW, one_pow]

/-- The block-average weight is `blkCoef2` read through `splitEquiv`. -/
theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Z2 L) (k : Idx L W) :
    (if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0)
      = blkCoef2 L W a (splitEquiv L W k) := by
  rfl

end Families

end RBM.Green
