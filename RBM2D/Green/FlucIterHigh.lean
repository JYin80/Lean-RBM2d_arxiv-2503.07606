/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucIter
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Topology.Instances.Matrix

/-!
# The higher-order minor expansion: the annihilation identity and `MinorDiffGainUpTo'`

The paper (arXiv:2503.07606) states no
higher-order minor expansion: it defers the estimates on `G_t` to "Lemma 4.2 in [YY_25], which is
dimension-independent" (Section "Estimates for entries of `G`"), and the fluctuation averaging
behind `GavLGEX` is proved internally.

`RBM2D/Green/FlucIter.lean` reduces the moment bound for `flucAvg` to one hypothesis, the
gain interface `FlucGainUpTo'`: `q ≤ M` conditional fluctuations `Q_{κ_1} ⋯ Q_{κ_q}` (distinct
rows, all different from `k`) applied to `Z_k = (1 - E_k)(G_{kk} - m)` gain a factor `ρ^q`, for at
most `K` slots.  This file turns that hypothesis into a statement about the `q`-fold **minor
difference** alone.

## The annihilation identity

`applyOps_eq_applyOps_minorDiff` :
`applyOps L (Y ∅) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Y)`, where `κ_1, …, κ_m` are the rows carrying
a `Q` in the word `L` (`qList L`), `Y` is a family of minor versions indexed by `Finset`s of rows
and `Δ_κ Y^{(S)} := Y^{(S)} - Y^{(S ∪ {κ})}`.  It is an **exact identity**, not an estimate: the
proof peels the outermost letter; a `P` letter passes through; for a `Q_κ` letter it replaces `Y`
by `S ↦ Y S - Y (insert κ S)`, and the subtracted term `Y {κ}` is killed outright by `Q_κ`,
because it is strictly independent of row `κ` (`FinDepOffRow`) and a word preserves that.  No
truncation and no indicator is used.

## What is in the file

1. **`Finset`-indexed minors.**  `AgreeOffRows`, `FinDepOffRows`, `offRowsCoords`,
   `finDepOffRows_of_minorSet` (the master independence lemma: anything read off the minor matrix
   `H_u^{(S)}` is strictly independent of every row of `S`), `greenSetMat` (`G^{(S)}`, total in
   `ω`), `gEnt` (`G^{(S)}_{ab}` extended by `0` to the levels that removed `a` or `b`),
   `greenSetMat_empty_apply` (`S = ∅` is the full resolvent), `greenSetMat_insert_apply` ((4.9)
   between `G^{(S)}` and `G^{(S ∪ {κ})}`).
2. **The identity** `applyOps_eq_applyOps_minorDiff`, with `minorDiff`, `qList`, `applyOps_sub`,
   `qRow_sub`, `finDepOffRow_applyOps`, and the concrete family `greenSetDiagCentered`,
   `flucDiagSet` (`Z^{(S)}_k`; `flucDiagSet_empty : S = ∅` is `flucDiag`).
3. **Crude bounds**: `norm_minorDiff_le` (each difference at most doubles a uniform bound) and the
   deterministic envelope of the family (`norm_greenSetMat_apply_le_etaT`,
   `norm_greenSetDiagCentered_le_env`, `bddMeas_flucDiagSet`, `norm_flucDiagSet_le_env`).
4. **The interface** `MinorDiffGainUpTo'`, the gain interface with both budgets (`M` on the word
   length, `K` on `#ι`) for the reduced quantity, and `flucGainUpTo'_of_minorDiffGainUpTo'`:
   `MinorDiffGainUpTo'` at `(B, ρ, M, K)` gives `FlucGainUpTo'` at the same `(B, ρ, M, K)`.  The
   identity touches neither the words nor the index type, so both budgets and `ρ^{∑ numQ}` pass
   through unchanged.

## d = 2

These statements depend on the dimension only through the index type `Idx (d.L n) (d.W n) =
Z2 (W L)` (its `Fintype` and `DecidableEq` structure): no exponent or cardinality of the index
set occurs, and `L`, `W` occur only in the types `Idx`, `Coord`, `Xentry` of slice `n`.  The
constants are `2` per `Q` (`norm_applyOps_le`) and `2` per difference
(`norm_minorDiff_le`).  `MinorDiffGainUpTo'` is a **hypothesis** of the endpoint, not a theorem:
the size of the iterated minor differences is the consumers' obligation.  It is not vacuous: it
holds gain-free (`ρ` compensated by `B`), by the crude bounds `norm_applyOps_le` and
`norm_minorDiff_le`.

## Notation

* The objects are `Sizes`, `Idx (d.L n) (d.W n)`, `Sizes.SeqΩ d`, `Sizes.seqP d`,
  `Sizes.SeqCoord d`, `Sizes.seqHflow d n u ω`,
  `Xentry (d.L n) (d.W n) (Sizes.slice d n ω)`, `spectralZ E t`, `spectralM E`; the slice is `n`
  and the budget of `MinorDiffGainUpTo'` is `K`.
* The envelope is written with `η_t = (spectralZ E t).im`, as in `RBM2D/Green/FlucAvg.lean`.
  The private lemmas `flucIterHigh_spectralZ_im_pos`,
  `flucIterHigh_norm_green_spectralZ_le` and `flucIterHigh_measurable_matrix_inv_apply` restate
  private lemmas of `FlucAvg.lean` and `RowIndep.lean`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

variable {d : Sizes} {n : ℕ}

/-! ### Private helpers -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A` (the private lemma of `FlucAvg.lean`, restated). -/
private theorem flucIterHigh_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ}
    (hM : Measurable M) (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

end MatrixMeasurable

/-! ### Sample points that agree off a `Finset` of rows -/

/-- Two sample points **agree off the rows in `S`**: every coordinate at size `n` whose index
pair avoids `S` carries the same value.  The `S = {i}` case is `RBM.Green.AgreeOffRow`. -/
def AgreeOffRows (d : Sizes) (n : ℕ) (S : Finset (Idx (d.L n) (d.W n))) (ω ω' : Sizes.SeqΩ d) :
    Prop :=
  ∀ (k l : Idx (d.L n) (d.W n)) (b : Bool), k ∉ S → l ∉ S → ω ⟨n, k, l, b⟩ = ω' ⟨n, k, l, b⟩

/-- The entries of `X` away from the rows and columns in `S` read only coordinates that
avoid `S`. -/
theorem Xentry_congr_of_not_mem {S : Finset (Idx (d.L n) (d.W n))} {ω ω' : Sizes.SeqΩ d}
    (h : AgreeOffRows d n S ω ω') {k l : Idx (d.L n) (d.W n)} (hk : k ∉ S) (hl : l ∉ S) :
    Xentry (d.L n) (d.W n) (Sizes.slice d n ω) k l
      = Xentry (d.L n) (d.W n) (Sizes.slice d n ω') k l := by
  unfold Xentry
  simp only [Sizes.slice]
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` on `{a ∉ S}` reads only coordinates that avoid `S`. -/
theorem Hflow_submatrix_set_congr (u : ℝ) {S : Finset (Idx (d.L n) (d.W n))}
    {ω ω' : Sizes.SeqΩ d} (h : AgreeOffRows d n S ω ω') :
    (Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
      = (Sizes.seqHflow d n u ω').submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n)) := by
  ext k l
  simp only [Matrix.submatrix_apply]
  exact congrArg (fun x : ℂ => (Real.sqrt u : ℂ) * x) (Xentry_congr_of_not_mem h k.2 l.2)

/-! ### `FinDepOffRows`: strict independence of a whole `Finset` of rows -/

/-- **`g` is strictly independent of every row in `S`**: it reads finitely many Gaussian
coordinates, none of which is a row-`κ` coordinate for any `κ ∈ S`.  This is
`RBM.Green.FinDepOffRow` with the witness set constrained to avoid all of `S` at once. -/
def FinDepOffRows (d : Sizes) (n : ℕ) (S : Finset (Idx (d.L n) (d.W n))) {V : Type*}
    (g : Sizes.SeqΩ d → V) : Prop :=
  ∃ I : Finset (Sizes.SeqCoord d), (∀ c ∈ I, ∀ κ ∈ S, ¬ IsRowCoord d n κ c) ∧
    ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

/-- **The annihilation half, in one line**: `FinDepOffRows S` gives `FinDepOffRow κ` for every
`κ ∈ S`, hence `E_κ` fixes `g` and `Q_κ g = 0`. -/
theorem FinDepOffRows.finDepOffRow {S : Finset (Idx (d.L n) (d.W n))} {V : Type*}
    {g : Sizes.SeqΩ d → V} (h : FinDepOffRows d n S g) {κ : Idx (d.L n) (d.W n)} (hκ : κ ∈ S) :
    FinDepOffRow d n κ g :=
  let ⟨I, hI, hg⟩ := h; ⟨I, fun c hc => hI c hc κ hκ, hg⟩

theorem FinDepOffRows.comp {S : Finset (Idx (d.L n) (d.W n))} {V W : Type*}
    {g : Sizes.SeqΩ d → V} (h : FinDepOffRows d n S g) (F : V → W) :
    FinDepOffRows d n S fun ω => F (g ω) :=
  let ⟨I, hI, hg⟩ := h
  ⟨I, hI, fun ω ω' hω => show F (g ω) = F (g ω') by rw [hg ω ω' hω]⟩

theorem FinDepOffRows.sub {S : Finset (Idx (d.L n) (d.W n))} {X Y : Sizes.SeqΩ d → ℂ}
    (hX : FinDepOffRows d n S X) (hY : FinDepOffRows d n S Y) :
    FinDepOffRows d n S fun ω => X ω - Y ω := by
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

/-- **`E_{k}` preserves independence of every row in `S`** — the `Finset` version of
`RBM.Green.finDepOffRow_condRow`.  It is what keeps the `(1 - E_k)` in `Z^{(S)}_k` harmless. -/
theorem finDepOffRows_condRow {S : Finset (Idx (d.L n) (d.W n))} {k : Idx (d.L n) (d.W n)}
    {X : Sizes.SeqΩ d → ℂ} (h : FinDepOffRows d n S X) :
    FinDepOffRows d n S (condRow d n k X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord d n k c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d n k c
  · rw [rowSplit_apply_of_isRowCoord k ω ω'' hcr, rowSplit_apply_of_isRowCoord k ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

theorem finDepOffRows_qRow {S : Finset (Idx (d.L n) (d.W n))} {k : Idx (d.L n) (d.W n)}
    {X : Sizes.SeqΩ d → ℂ} (h : FinDepOffRows d n S X) :
    FinDepOffRows d n S (qRow d n k X) :=
  h.sub (finDepOffRows_condRow h)

/-- The witness set: every coordinate at size `n` whose index pair avoids `S`. -/
def offRowsCoords (d : Sizes) (n : ℕ) (S : Finset (Idx (d.L n) (d.W n))) :
    Finset (Sizes.SeqCoord d) :=
  (Finset.univ.image fun p : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n) × Bool =>
      (⟨n, p⟩ : Sizes.SeqCoord d)).filter
    fun c => ∀ κ ∈ S, ¬ IsRowCoord d n κ c

theorem forall_not_isRowCoord_of_mem_offRowsCoords {S : Finset (Idx (d.L n) (d.W n))}
    {c : Sizes.SeqCoord d} (hc : c ∈ offRowsCoords d n S) : ∀ κ ∈ S, ¬ IsRowCoord d n κ c :=
  (Finset.mem_filter.1 hc).2

theorem mem_offRowsCoords {S : Finset (Idx (d.L n) (d.W n))} {i j : Idx (d.L n) (d.W n)}
    {b : Bool} (hi : i ∉ S) (hj : j ∉ S) :
    (⟨n, i, j, b⟩ : Sizes.SeqCoord d) ∈ offRowsCoords d n S := by
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(i, j, b), Finset.mem_univ _, rfl⟩, ?_⟩
  intro κ hκ
  simp only [isRowCoord_mk]
  rintro (h | h)
  · exact hi (h ▸ hκ)
  · exact hj (h ▸ hκ)

/-- **The master row-independence lemma for a `Finset` of rows.**  Anything read off the minor
matrix `H_u^{(S)}` is strictly independent of every row in `S`. -/
theorem finDepOffRows_of_minorSet (d : Sizes) (n : ℕ) (u : ℝ) (S : Finset (Idx (d.L n) (d.W n)))
    {V : Type*}
    (F : Matrix {a : Idx (d.L n) (d.W n) // a ∉ S} {a : Idx (d.L n) (d.W n) // a ∉ S} ℂ → V) :
    FinDepOffRows d n S fun ω =>
      F ((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))) := by
  refine ⟨offRowsCoords d n S, fun c hc => forall_not_isRowCoord_of_mem_offRowsCoords hc,
    fun ω ω' hω => ?_⟩
  have hagree : AgreeOffRows d n S ω ω' := fun i j b hi hj => hω _ (mem_offRowsCoords hi hj)
  change F _ = F _
  rw [Hflow_submatrix_set_congr u hagree]

/-! ### The iterated minor resolvent `G^{(S)}` -/

/-- **`G^{(S)} = (H_u^{(S)} - z)⁻¹`**, the resolvent on `{a ∉ S}`, as a *total* function of `ω`
(`Matrix.inv` is total, so no invertibility hypothesis is carried).  For `S = ∅` it is the full
resolvent (`greenSetMat_empty_apply`); for `S = {κ}` it is `RBM.Green.greenMinorMat` on the
index set `{a // a ∉ {κ}}` in place of `{a // a ≠ κ}` (this identification is not proved here). -/
noncomputable def greenSetMat (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d) :
    Matrix {a : Idx (d.L n) (d.W n) // a ∉ S} {a : Idx (d.L n) (d.W n) // a ∉ S} ℂ :=
  ((Sizes.seqHflow d n u ω).submatrix
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ∉ S} {a : Idx (d.L n) (d.W n) // a ∉ S}
        ℂ))⁻¹

theorem greenSetMat_eq_green_submatrix (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d) :
    greenSetMat d n u z S ω
      = green ((Sizes.seqHflow d n u ω).submatrix
          (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
          (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))) z := rfl

theorem finDepOffRows_greenSetMat (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) :
    FinDepOffRows d n S (greenSetMat d n u z S) :=
  finDepOffRows_of_minorSet d n u S fun M => (M - z • 1)⁻¹

theorem finDepOffRows_greenSetMat_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) (a b : {a : Idx (d.L n) (d.W n) // a ∉ S}) :
    FinDepOffRows d n S fun ω => greenSetMat d n u z S ω a b :=
  (finDepOffRows_greenSetMat d n u z S).comp fun M => M a b

theorem measurable_greenSetMat_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) (a b : {a : Idx (d.L n) (d.W n) // a ∉ S}) :
    Measurable fun ω => greenSetMat d n u z S ω a b := by
  refine flucIterHigh_measurable_matrix_inv_apply (M := fun ω : Sizes.SeqΩ d =>
    (Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
      (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ∉ S}
        {a : Idx (d.L n) (d.W n) // a ∉ S} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Sizes.SeqΩ d =>
      ((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ∉ S} → Idx (d.L n) (d.W n))
        - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ∉ S}
          {a : Idx (d.L n) (d.W n) // a ∉ S} ℂ)) p q)
      = fun ω => Sizes.seqHflow d n u ω p.1 q.1
          - z * (1 : Matrix {a : Idx (d.L n) (d.W n) // a ∉ S}
            {a : Idx (d.L n) (d.W n) // a ∉ S} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry d n u p.1 q.1).sub measurable_const

/-! ### The entries of the iterated minor, extended by `0`

`greenSetMat` lives on the subtype `{a // a ∉ S}`, so its entries carry a proof that the index
has not been removed.  `gEnt` erases that proof by extending the entry by `0` to the levels that
*have* removed `a` or `b`.  This is what makes the difference calculus total: no side condition
travels with the recursion.  It is stated here so that `RBM2D/Green/MinorGoodLe.lean`, which needs
`gEnt` to phrase the level-budgeted good event, does not have to import the minor-difference
calculus, which consumes that event. -/

section GEnt

variable {u : ℝ} {z : ℂ} {ω : Sizes.SeqΩ d} {a b : Idx (d.L n) (d.W n)}
  {S : Finset (Idx (d.L n) (d.W n))}

/-- `G^{(S)}_{ab}`, extended by `0` to the levels that have removed `a` or `b`.  The extension is
what makes the difference calculus total: no side condition is carried along the recursion. -/
noncomputable def gEnt (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ d)
    (a b : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) : ℂ :=
  if ha : a ∉ S then (if hb : b ∉ S then greenSetMat d n u z S ω ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0

theorem gEnt_apply (ha : a ∉ S) (hb : b ∉ S) :
    gEnt d n u z ω a b S = greenSetMat d n u z S ω ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [gEnt, dite_eq_left ha, dite_eq_left hb]

theorem gEnt_eq_zero_left (h : a ∈ S) : gEnt d n u z ω a b S = 0 := by
  rw [gEnt, dite_eq_right (not_not_intro h)]

theorem gEnt_eq_zero_right (h : b ∈ S) : gEnt d n u z ω a b S = 0 := by
  rw [gEnt]
  by_cases ha : a ∉ S
  · rw [dite_eq_left ha, dite_eq_right (not_not_intro h)]
  · rw [dite_eq_right ha]

end GEnt

/-! ### The `m`-fold minor difference

The gain comes from the *iterated* difference operator `Δ_{κ_1} ⋯ Δ_{κ_m}`, where
`Δ_κ X^{(S)} := X^{(S)} - X^{(S ∪ {κ})}`.  It is presented as a recursion on the list of rows,
acting on a whole *family* `Y : Finset (Idx) → Ω → ℂ` of minor versions; unfolded, it is the
inclusion–exclusion sum `∑_{T ⊆ {κ_1,…,κ_m}} (-1)^{#T} Y T`. -/

/-- `minorDiff d n [κ_1, …, κ_m] Y = Δ_{κ_1} ⋯ Δ_{κ_m} Y`, the `m`-fold minor difference of
the family `Y`. -/
noncomputable def minorDiff (d : Sizes) (n : ℕ) :
    List (Idx (d.L n) (d.W n)) → (Finset (Idx (d.L n) (d.W n)) → Sizes.SeqΩ d → ℂ) →
      (Sizes.SeqΩ d → ℂ)
  | [], Y => Y ∅
  | κ :: l, Y => minorDiff d n l fun S ω => Y S ω - Y (insert κ S) ω

@[simp] theorem minorDiff_cons (d : Sizes) (n : ℕ) (κ : Idx (d.L n) (d.W n))
    (l : List (Idx (d.L n) (d.W n)))
    (Y : Finset (Idx (d.L n) (d.W n)) → Sizes.SeqΩ d → ℂ) :
    minorDiff d n (κ :: l) Y = minorDiff d n l fun S ω => Y S ω - Y (insert κ S) ω := rfl

/-- The rows carrying a `Q` in a word, in order.  These are exactly the rows along which the
minor difference is taken. -/
def qList (L : List (Bool × Idx (d.L n) (d.W n))) : List (Idx (d.L n) (d.W n)) :=
  (L.filter (·.1)).map Prod.snd

@[simp] theorem qList_cons_true (κ : Idx (d.L n) (d.W n))
    (l : List (Bool × Idx (d.L n) (d.W n))) :
    qList ((true, κ) :: l) = κ :: qList l := rfl

@[simp] theorem qList_cons_false (κ : Idx (d.L n) (d.W n))
    (l : List (Bool × Idx (d.L n) (d.W n))) :
    qList ((false, κ) :: l) = qList l := rfl

theorem length_qList (L : List (Bool × Idx (d.L n) (d.W n))) : (qList L).length = numQ L := by
  simp [qList, numQ, List.countP_eq_length_filter]

/-! ### Linearity of the words, and their independence -/

theorem qRow_sub (k : Idx (d.L n) (d.W n)) {X Y : Sizes.SeqΩ d → ℂ} (hX : BddMeas d X)
    (hY : BddMeas d Y) :
    qRow d n k (fun ω => X ω - Y ω) = fun ω => qRow d n k X ω - qRow d n k Y ω := by
  funext ω
  change X ω - Y ω - condRow d n k (fun ω' => X ω' - Y ω') ω
    = (X ω - condRow d n k X ω) - (Y ω - condRow d n k Y ω)
  rw [condRow_sub k (hX.rowIntegrable k) (hY.rowIntegrable k)]
  ring

/-- **The words are linear.** -/
theorem applyOps_sub (l : List (Bool × Idx (d.L n) (d.W n))) {X Y : Sizes.SeqΩ d → ℂ}
    (hX : BddMeas d X) (hY : BddMeas d Y) :
    applyOps d n l (fun ω => X ω - Y ω)
      = fun ω => applyOps d n l X ω - applyOps d n l Y ω := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [applyOps_cons_false, ih]
        exact condRow_sub κ ((hX.applyOps l).rowIntegrable κ)
          ((hY.applyOps l).rowIntegrable κ)
      · rw [applyOps_cons_true, ih]
        exact qRow_sub κ (hX.applyOps l) (hY.applyOps l)

/-- **A word preserves strict independence of row `κ`.** -/
theorem finDepOffRow_applyOps {κ : Idx (d.L n) (d.W n)}
    (l : List (Bool × Idx (d.L n) (d.W n))) {X : Sizes.SeqΩ d → ℂ}
    (h : FinDepOffRow d n κ X) : FinDepOffRow d n κ (applyOps d n l X) := by
  induction l with
  | nil => simpa [applyOps] using h
  | cons x l ih =>
      obtain ⟨b, ν⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using finDepOffRow_condRow (k' := ν) ih
      · rw [applyOps_cons_true]
        exact ih.sub (finDepOffRow_condRow (k' := ν) ih)

/-! ### The annihilation identity

This is the whole content of the higher-order expansion on the probabilistic side, and it is an
**exact identity**, not an estimate: a word may be applied to the `m`-fold minor difference
instead of to the function itself, where `m` is the number of `Q`'s in the word. -/

/-- **`applyOps L (Y ∅) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Y)`**, where `κ_1, …, κ_m` are the rows
carrying a `Q` in `L`.

The proof peels the outermost letter.  A `P` letter passes through by the inductive hypothesis.
For a `Q_κ` letter, replace the family `Y` by `Z S := Y S - Y (S ∪ {κ})`: by linearity of the
word, `applyOps l (Z ∅) = applyOps l (Y ∅) - applyOps l (Y {κ})`, and the subtracted term is
killed outright by `Q_κ`, because `Y {κ}` is strictly independent of row `κ` and a word
preserves that.  No estimate, no truncation, no indicator. -/
theorem applyOps_eq_applyOps_minorDiff (L : List (Bool × Idx (d.L n) (d.W n)))
    (Y : Finset (Idx (d.L n) (d.W n)) → Sizes.SeqΩ d → ℂ) (hbdd : ∀ S, BddMeas d (Y S))
    (hind : ∀ (S : Finset (Idx (d.L n) (d.W n))), ∀ κ ∈ S, FinDepOffRow d n κ (Y S)) :
    applyOps d n L (Y ∅) = applyOps d n L (minorDiff d n (qList L) Y) := by
  induction L generalizing Y with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [qList_cons_false, applyOps_cons_false, applyOps_cons_false, ih Y hbdd hind]
      · set Z : Finset (Idx (d.L n) (d.W n)) → Sizes.SeqΩ d → ℂ :=
          fun S ω => Y S ω - Y (insert κ S) ω with hZ
        have hbddZ : ∀ S, BddMeas d (Z S) := fun S => (hbdd S).sub (hbdd _)
        have hindZ : ∀ (S : Finset (Idx (d.L n) (d.W n))), ∀ ν ∈ S, FinDepOffRow d n ν (Z S) :=
          fun S ν hν => (hind S ν hν).sub (hind _ ν (Finset.mem_insert_of_mem hν))
        have hkey : applyOps d n l (Z ∅)
            = fun ω => applyOps d n l (Y ∅) ω - applyOps d n l (Y {κ}) ω := by
          have hins : insert κ (∅ : Finset (Idx (d.L n) (d.W n))) = {κ} := rfl
          rw [hZ]
          simpa only [hins] using applyOps_sub l (hbdd ∅) (hbdd {κ})
        have hann : qRow d n κ (applyOps d n l (Y {κ})) = 0 := by
          funext ω
          have hf : FinDepOffRow d n κ (applyOps d n l (Y {κ})) :=
            finDepOffRow_applyOps l (hind {κ} κ (Finset.mem_singleton_self κ))
          change applyOps d n l (Y {κ}) ω - condRow d n κ (applyOps d n l (Y {κ})) ω = 0
          rw [congrFun (condRow_of_finDepOffRow hf) ω, sub_self]
        rw [qList_cons_true, minorDiff_cons, applyOps_cons_true, applyOps_cons_true,
          ← hZ, ← ih Z hbddZ hindZ, hkey,
          qRow_sub κ ((hbdd ∅).applyOps l) ((hbdd {κ}).applyOps l), hann]
        funext ω
        simp

/-! ### The concrete family of iterated minors of `Z_k` -/

/-- `G^{(S)}_{kk} - m`, extended by `0` to the (never used) subsets containing `k`. -/
noncomputable def greenSetDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) : Sizes.SeqΩ d → ℂ :=
  fun ω => if h : k ∉ S then greenSetMat d n u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0

/-- **`Z^{(S)}_k := (1 - E_k)(G^{(S)}_{kk} - m)`**, the `S`-minor version of the fluctuation.
`S = ∅` is `RBM.Green.flucDiag` (`flucDiagSet_empty`). -/
noncomputable def flucDiagSet (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx (d.L n) (d.W n))
    (S : Finset (Idx (d.L n) (d.W n))) : Sizes.SeqΩ d → ℂ :=
  qRow d n k (greenSetDiagCentered d n u z m k S)

theorem finDepOffRows_greenSetDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) :
    FinDepOffRows d n S (greenSetDiagCentered d n u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (finDepOffRows_greenSetMat_apply d n u z S ⟨k, h⟩ ⟨k, h⟩).comp fun c => c - m
  · simp only [dite_eq_right h]
    exact ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem finDepOffRows_flucDiagSet (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) :
    FinDepOffRows d n S (flucDiagSet d n u z m k S) :=
  finDepOffRows_qRow (finDepOffRows_greenSetDiagCentered d n u z m k S)

/-- The hypothesis `hind` of `applyOps_eq_applyOps_minorDiff`, for the concrete family. -/
theorem finDepOffRow_flucDiagSet (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) {κ : Idx (d.L n) (d.W n)}
    (hκ : κ ∈ S) : FinDepOffRow d n κ (flucDiagSet d n u z m k S) :=
  (finDepOffRows_flucDiagSet d n u z m k S).finDepOffRow hκ

/-! #### `S = ∅` is the full resolvent -/

theorem greenSetMat_empty_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ d)
    (a b : {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))}) :
    greenSetMat d n u z ∅ ω a b = green (Sizes.seqHflow d n u ω) z a.1 b.1 := by
  classical
  set e : {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))}
      ≃ Idx (d.L n) (d.W n) :=
    Equiv.subtypeUnivEquiv fun x => Finset.notMem_empty x with he
  have hone : ∀ i j : {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))},
      (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))}
        {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))} ℂ) i j
        = (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) i.1 j.1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']
  have hsub : (Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))} →
          Idx (d.L n) (d.W n)) Subtype.val
        - z • (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))}
          {x : Idx (d.L n) (d.W n) // x ∉ (∅ : Finset (Idx (d.L n) (d.W n)))} ℂ)
      = (Sizes.seqHflow d n u ω
          - z • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)).submatrix ⇑e ⇑e := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, he,
      Equiv.subtypeUnivEquiv_apply]
    rw [hone i j]
  change (_ : Matrix _ _ ℂ)⁻¹ a b = _
  rw [hsub, Matrix.inv_submatrix_equiv]
  simp [green, he]

theorem flucDiagSet_empty (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx (d.L n) (d.W n)) :
    flucDiagSet d n u z m k ∅ = flucDiag d n u z m k := by
  have hg : greenSetDiagCentered d n u z m k ∅ = greenDiagCentered d n u z m k := by
    funext ω
    have hk : k ∉ (∅ : Finset (Idx (d.L n) (d.W n))) := Finset.notMem_empty k
    change (if h : k ∉ (∅ : Finset (Idx (d.L n) (d.W n))) then
        greenSetMat d n u z ∅ ω ⟨k, h⟩ ⟨k, h⟩ - m else 0) = _
    rw [dite_eq_left hk, greenSetMat_empty_apply]
    rfl
  rw [flucDiagSet, hg, flucDiag_eq_qRow]

/-! ### One step of (4.9) between consecutive iterated minors

`RBM2D/Green/Minor.lean` proves (4.9) for an arbitrary `Fintype` index, so it iterates:
removing one more row `κ` from `G^{(S)}` gives `G^{(S ∪ {κ})}`, and the two differ by the rank-one
term `G^{(S)}_{aκ} G^{(S)}_{κb} / G^{(S)}_{κκ}`.  The only work is the index bookkeeping. -/

/-- Removing `κ` from `{a ∉ S}` is passing to `{a ∉ insert κ S}`. -/
def insertRowEquiv (d : Sizes) (n : ℕ) {S : Finset (Idx (d.L n) (d.W n))}
    {κ : Idx (d.L n) (d.W n)} (hκ : κ ∉ S) :
    {y : {x : Idx (d.L n) (d.W n) // x ∉ S} // y ≠ ⟨κ, hκ⟩}
      ≃ {x : Idx (d.L n) (d.W n) // x ∉ insert κ S} where
  toFun y := ⟨y.1.1, by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  invFun x := ⟨⟨x.1, fun h => x.2 (Finset.mem_insert_of_mem h)⟩, by
    intro h
    exact x.2 (by rw [show x.1 = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- **(4.9) between `G^{(S)}` and `G^{(S ∪ {κ})}`.**  The hypotheses are the ones (4.9) itself
needs: the `S`-minor is invertible and its `κκ` entry does not vanish — on the event (4.1) the
latter is `≥ 1/2` (`RBM.Green.GoodEvent.half_le_norm_diag`). -/
theorem greenSetMat_insert_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d) {κ : Idx (d.L n) (d.W n)}
    (hκ : κ ∉ S)
    (hdet : IsUnit ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ S} → Idx (d.L n) (d.W n)) Subtype.val
        - z • (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ S}
          {x : Idx (d.L n) (d.W n) // x ∉ S} ℂ)).det)
    (hGκκ : greenSetMat d n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0)
    {a b : Idx (d.L n) (d.W n)} (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    greenSetMat d n u z (insert κ S) ω ⟨a, ha⟩ ⟨b, hb⟩
      = greenSetMat d n u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩
            ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
        - greenSetMat d n u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ ⟨κ, hκ⟩
            * greenSetMat d n u z S ω ⟨κ, hκ⟩
              ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
            / greenSetMat d n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ := by
  classical
  set ν := {x : Idx (d.L n) (d.W n) // x ∉ S}
  set M : Matrix ν ν ℂ := (Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : ν → Idx (d.L n) (d.W n)) Subtype.val - z • (1 : Matrix ν ν ℂ) with hM
  set G : Matrix ν ν ℂ := greenSetMat d n u z S ω with hG
  have hGM : G * M = 1 := Matrix.nonsing_inv_mul M hdet
  set i : ν := ⟨κ, hκ⟩ with hi
  set e := insertRowEquiv d n hκ with he
  set A : Matrix {x : Idx (d.L n) (d.W n) // x ∉ insert κ S}
      {x : Idx (d.L n) (d.W n) // x ∉ insert κ S} ℂ :=
    (Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ insert κ S} → Idx (d.L n) (d.W n))
      Subtype.val - z • 1 with hA
  have hminor : minorMat M i = A.submatrix ⇑e ⇑e := by
    ext y w
    have hone : (1 : Matrix ν ν ℂ) y.1 w.1
        = (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ insert κ S}
            {x : Idx (d.L n) (d.W n) // x ∉ insert κ S} ℂ)
            (e y) (e w) := by
      by_cases h : y.1.1 = w.1.1
      · have h1 : y.1 = w.1 := Subtype.ext h
        have h2 : e y = e w := Subtype.ext h
        rw [h1, h2, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h1 : y.1 ≠ w.1 := fun hh => h (congrArg Subtype.val hh)
        have h2 : e y ≠ e w := fun hh =>
          h (congrArg (fun x : {x : Idx (d.L n) (d.W n) // x ∉ insert κ S} => x.1) hh)
        rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]
    simp only [minorMat, hM, hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, smul_eq_mul]
    rw [hone]
    rfl
  have hinv : minorGreen G i = (greenSetMat d n u z (insert κ S) ω).submatrix ⇑e ⇑e := by
    rw [← inv_minorMat hGM i hGκκ, hminor, Matrix.inv_submatrix_equiv]
    rfl
  have hane : (⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ : ν) ≠ i := by
    intro h
    exact ha (by rw [show a = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have hbne : (⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩ : ν) ≠ i := by
    intro h
    exact hb (by rw [show b = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have := congrFun (congrFun hinv ⟨_, hane⟩) ⟨_, hbne⟩
  simp only [minorGreen, Matrix.of_apply, Matrix.submatrix_apply] at this
  rw [show (e ⟨_, hane⟩ : {x : Idx (d.L n) (d.W n) // x ∉ insert κ S}) = ⟨a, ha⟩
      from Subtype.ext rfl,
    show (e ⟨_, hbne⟩ : {x : Idx (d.L n) (d.W n) // x ∉ insert κ S}) = ⟨b, hb⟩
      from Subtype.ext rfl] at this
  exact this.symm

/-! ### Crude bounds on the difference, and the deterministic envelope -/

/-- Each difference at most doubles a uniform bound. -/
theorem norm_minorDiff_le (l : List (Idx (d.L n) (d.W n)))
    (Y : Finset (Idx (d.L n) (d.W n)) → Sizes.SeqΩ d → ℂ) {b : ℝ}
    (hb : ∀ S ω, ‖Y S ω‖ ≤ b) (ω : Sizes.SeqΩ d) :
    ‖minorDiff d n l Y ω‖ ≤ 2 ^ l.length * b := by
  induction l generalizing Y b with
  | nil => simpa [minorDiff] using hb ∅ ω
  | cons κ l ih =>
      have hb' : ∀ (S : Finset (Idx (d.L n) (d.W n))) (ω' : Sizes.SeqΩ d),
          ‖(fun S ω => Y S ω - Y (insert κ S) ω) S ω'‖ ≤ 2 * b := fun S ω' =>
        le_trans (norm_sub_le _ _) (by linarith [hb S ω', hb (insert κ S) ω'])
      have := ih (fun S ω => Y S ω - Y (insert κ S) ω) hb'
      rw [minorDiff_cons]
      calc ‖minorDiff d n l (fun S ω => Y S ω - Y (insert κ S) ω) ω‖
          ≤ 2 ^ l.length * (2 * b) := this
        _ = 2 ^ (κ :: l).length * b := by rw [List.length_cons, pow_succ]; ring

section Env

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- For `|E| < 2` and `t < 1`, `η_t = Im z_t > 0` (the private lemma of `FlucAvg.lean`,
restated). -/
private theorem flucIterHigh_spectralZ_im_pos (hE : |E| < 2) (ht : t < 1) :
    0 < (spectralZ E t).im := by
  rw [spectralZ_im]
  exact mul_pos (by linarith) (spectralM_im_pos hE)

/-- The Green function of a Hermitian matrix at `z_t` has operator norm at most `η_t⁻¹` (the
private lemma of `FlucAvg.lean`, restated). -/
private theorem flucIterHigh_norm_green_spectralZ_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hE : |E| < 2) (ht : t < 1) :
    ‖green H (spectralZ E t)‖ ≤ ((spectralZ E t).im)⁻¹ := by
  have hη := flucIterHigh_spectralZ_im_pos hE ht
  exact norm_green_le hH hη (le_of_eq (abs_of_pos hη).symm)

/-- `|G^{(S)}_{ab}| ≤ η_t⁻¹` for every `ω`: `H^{(S)}` is a minor of a Hermitian matrix. -/
theorem norm_greenSetMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {S : Finset (Idx (d.L n) (d.W n))} (a b : {x : Idx (d.L n) (d.W n) // x ∉ S})
    (ω : Sizes.SeqΩ d) :
    ‖greenSetMat d n u (spectralZ E t) S ω a b‖ ≤ ((spectralZ E t).im)⁻¹ := by
  rw [greenSetMat_eq_green_submatrix]
  exact le_trans (RBM.Ind.norm_apply_le_l2_opNorm _ a b)
    (flucIterHigh_norm_green_spectralZ_le
      ((Sizes.seqHflow_isHermitian d n u ω).submatrix _) hE ht)

theorem measurable_greenSetDiagCentered (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) :
    Measurable (greenSetDiagCentered d n u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (measurable_greenSetMat_apply d n u z S ⟨k, h⟩ ⟨k, h⟩).sub measurable_const
  · simp only [dite_eq_right h]
    exact measurable_const

theorem norm_greenSetDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d) :
    ‖greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k S ω‖
      ≤ ((spectralZ E t).im)⁻¹ + 1 := by
  have hη : 0 < (spectralZ E t).im := flucIterHigh_spectralZ_im_pos hE ht
  change ‖if h : k ∉ S then greenSetMat d n u (spectralZ E t) S ω ⟨k, h⟩ ⟨k, h⟩ - spectralM E
    else 0‖ ≤ _
  by_cases h : k ∉ S
  · rw [dite_eq_left h]
    refine le_trans (norm_sub_le _ _)
      (add_le_add (norm_greenSetMat_apply_le_etaT hE ht u ⟨k, h⟩ ⟨k, h⟩ ω) ?_)
    exact le_of_eq (norm_spectralM hE.le)
  · rw [dite_eq_right h, norm_zero]
    positivity

theorem bddMeas_greenSetDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx (d.L n) (d.W n)) (S : Finset (Idx (d.L n) (d.W n))) :
    BddMeas d (greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k S) :=
  ⟨measurable_greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k S,
    ((spectralZ E t).im)⁻¹ + 1, norm_greenSetDiagCentered_le_env hE ht u k S⟩

theorem bddMeas_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx (d.L n) (d.W n))
    (S : Finset (Idx (d.L n) (d.W n))) :
    BddMeas d (flucDiagSet d n u (spectralZ E t) (spectralM E) k S) :=
  (bddMeas_greenSetDiagCentered hE ht u k S).qRow k

theorem norm_flucDiagSet_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx (d.L n) (d.W n))
    (S : Finset (Idx (d.L n) (d.W n))) (ω : Sizes.SeqΩ d) :
    ‖flucDiagSet d n u (spectralZ E t) (spectralM E) k S ω‖
      ≤ 2 * (((spectralZ E t).im)⁻¹ + 1) := by
  have h := norm_sub_condRow_le (k := k)
    (X := greenSetDiagCentered d n u (spectralZ E t) (spectralM E) k S)
    (b := ((spectralZ E t).im)⁻¹ + 1) (norm_greenSetDiagCentered_le_env hE ht u k S) ω
  exact h

/-! ### The interface, reduced to the iterated minors

`applyOps_eq_applyOps_minorDiff` turns `FlucGainUpTo'` — a statement about the effect of `q`
conditional fluctuations — into a statement about the `q`-fold minor difference alone.  The
conditional expectations survive only as the outer word, which costs at most `2^q` and does not
have to *produce* anything.

The budget `K` on `#ι` is that of `FlucGainUpTo'`: without it, `ι = Fin j` with empty
words would give `∫ ‖Z_k‖^j ≤ B^j` for every `j`, i.e. an `L^∞` bound. -/

/-- **`FlucGainUpTo'` for the reduced quantity `applyOps L (Δ_{κ_1} ⋯ Δ_{κ_q} Z^{(·)}_k)`**, with
both budgets: `M` on the word length and `K` on the number of slots `#ι`. -/
def MinorDiffGainUpTo' (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → Idx (d.L n) (d.W n))
      (L : ι → List (Bool × Idx (d.L n) (d.W n))),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
      ∫ ω, ∏ i, ‖applyOps d n (L i)
          (minorDiff d n (qList (L i)) (flucDiagSet d n u z m (k i))) ω‖ ∂(Sizes.seqP d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- **`FlucGainUpTo'` from `MinorDiffGainUpTo'`**: the rewriting step is the exact identity
`applyOps_eq_applyOps_minorDiff`, which touches neither the words nor the index type, so both
budgets and the gain `ρ^{∑ numQ}` are handed on unchanged. -/
theorem flucGainUpTo'_of_minorDiffGainUpTo' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    {M K : ℕ} (h : MinorDiffGainUpTo' d n u (spectralZ E t) (spectralM E) B ρ M K) :
    FlucGainUpTo' d n u (spectralZ E t) (spectralM E) B ρ M K := by
  refine ⟨h.1, h.2.1, fun ι _ k L h1 h2 h3 h4 => ?_⟩
  have hrw : ∀ i : ι, applyOps d n (L i) (flucDiag d n u (spectralZ E t) (spectralM E) (k i))
      = applyOps d n (L i)
        (minorDiff d n (qList (L i)) (flucDiagSet d n u (spectralZ E t) (spectralM E) (k i))) := by
    intro i
    rw [← flucDiagSet_empty d n u (spectralZ E t) (spectralM E) (k i)]
    exact applyOps_eq_applyOps_minorDiff (L i) _
      (fun S => bddMeas_flucDiagSet hE ht u (k i) S)
      (fun S κ hκ => finDepOffRow_flucDiagSet d n u (spectralZ E t) (spectralM E) (k i) S hκ)
  simp only [hrw]
  exact h.2.2 ι k L h1 h2 h3 h4

end Env

end RBM.Green
