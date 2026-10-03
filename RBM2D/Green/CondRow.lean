/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Probability.ProductMeasure
import RBM2D.Delocalization
import RBM2D.Gauss.Model
import RBM2D.Green.Minor
import RBM2D.Green.RowIndep

/-!
# `E_x` = integration over the row-`x` coordinates of slice `n`

The paper (arXiv:2503.07606) does not state this file as a lemma: it
says that the estimates on `G_t` "follow that of Lemma 4.2 in [YY_25], which is
dimension-independent" (Section "Estimates for entries of `G`"), and the mathematics is that of
[YY_25]: `E_x = E[· | H^{(x)}]`, with `G^{(x)}` a function of the entries outside row and column
`x`.

The model interface is that of `RBM2D/Gauss/Model.lean` and `RBM2D/Green/RowIndep.lean`:
everything is stated on the common sample space `Sizes.SeqΩ d = Sizes.SeqCoord d → ℝ` with the
product measure `Sizes.seqP d`, at slice `n` (the lattice index type is
`Idx (d.L n) (d.W n)`; the flow is `Sizes.seqHflow d n u`).  So `E_x` is not an abstract
`MeasureTheory.condExp`: it is the integral over the row-`x` coordinates of slice `n`, with the
others fixed,

  `E_x[X](ω) = ∫ X (rowSplit d n x ω ω') dP(ω')`,

where `rowSplit d n x ω ω'` takes the coordinates of `rowSet d n x` from `ω'` and all the others
from `ω`.  No `condExp` is used, and every identity below is pointwise in `ω`.

* `IsRowCoord`, `rowSplit`, `measurePreserving_rowSplit` : `(ω, ω') ↦ rowSplit d n x ω ω'`
  pushes `P ⊗ P` to `P`.
* `condRow`, `condRow_condRow`, `condRow_sub_condRow`, `integral_condRow` : `E_x`, `E_x ∘ E_x =
  E_x`, `E_x ∘ (1 - E_x) = 0`, the tower property `E[E_x X] = E[X]`.
* `FinDepOffRow`, `condRow_of_finDepOffRow`, `condRow_mul_of_finDepOffRow'` : a function that
  reads only finitely many coordinates, none of them in row `x`, is `E_x`-constant and its
  factor comes out of `E_x`.
* `finDepOffRow_of_minor`, `greenMinorMat`, `finDepOffRow_greenMinorMat`,
  `finDepOffRow_greenMinorMat_apply`, `greenMinorMat_eq_minorGreen` : anything read off the minor
  matrix `H_u^{(x)}` (in particular the minor resolvent) is `FinDepOffRow`.

`IsRowCoord d n x c` is defined as `c ∈ rowSet d n x` (`RBM2D/Green/RowIndep.lean`), and
the off-row coordinates are `offRowCoord` of `RowIndep.lean`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory RBM.Gauss

variable {d : Sizes} {n : ℕ}

/-! ### The row-`k` coordinates -/

/-- The coordinate `c` belongs to **row `k` at slice `n`**: it is `⟨n, k, j, b⟩` or `⟨n, j, k, b⟩`
for some `j` and some tag `b`, i.e. it lies in `rowSet d n k`.  These are exactly the coordinates
that the entries `H_{k·}` and `H_{·k}` read, and exactly the ones `E_k` integrates out. -/
def IsRowCoord (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) (c : Sizes.SeqCoord d) : Prop :=
  c ∈ rowSet d n k

instance decidableIsRowCoord (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) :
    DecidablePred (IsRowCoord d n k) := fun c => by
  unfold IsRowCoord; infer_instance

/-- Membership of row `k`, read off the index triple: `⟨n, i, j, b⟩` is a row-`k` coordinate
iff `i = k` or `j = k`. -/
@[simp] theorem isRowCoord_mk (d : Sizes) (n : ℕ) (k i j : Idx (d.L n) (d.W n)) (b : Bool) :
    IsRowCoord d n k (⟨n, i, j, b⟩ : Sizes.SeqCoord d) ↔ (i = k ∨ j = k) :=
  mem_rowSet

/-! ### Splitting a sample point along row `k` -/

/-- `rowSplit d n k ω ω'` takes the row-`k` coordinates from `ω'` and every other coordinate
from `ω`.  Integrating in `ω'` is exactly `E_k`. -/
noncomputable def rowSplit (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (ω ω' : Sizes.SeqΩ d) : Sizes.SeqΩ d :=
  fun c => if IsRowCoord d n k c then ω' c else ω c

theorem rowSplit_apply_of_isRowCoord (k : Idx (d.L n) (d.W n)) (ω ω' : Sizes.SeqΩ d)
    {c : Sizes.SeqCoord d}
    (hc : IsRowCoord d n k c) : rowSplit d n k ω ω' c = ω' c :=
  ite_eq_left hc

theorem rowSplit_apply_of_not_isRowCoord (k : Idx (d.L n) (d.W n)) (ω ω' : Sizes.SeqΩ d)
    {c : Sizes.SeqCoord d}
    (hc : ¬ IsRowCoord d n k c) : rowSplit d n k ω ω' c = ω c :=
  ite_eq_right hc

/-- **The splitting is idempotent in its first argument**: the second split overwrites exactly
the coordinates the first one wrote.  This single identity is what makes `E_k` a projection. -/
@[simp] theorem rowSplit_rowSplit (k : Idx (d.L n) (d.W n)) (ω ω' ω'' : Sizes.SeqΩ d) :
    rowSplit d n k (rowSplit d n k ω ω') ω'' = rowSplit d n k ω ω'' := by
  funext c
  unfold rowSplit
  split_ifs <;> rfl

theorem measurable_rowSplit (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) :
    Measurable fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : IsRowCoord d n k c
  · have h : (fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2 c)
        = fun p => p.2 c := by
      funext p; exact rowSplit_apply_of_isRowCoord k p.1 p.2 hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2 c)
        = fun p => p.1 c := by
      funext p; exact rowSplit_apply_of_not_isRowCoord k p.1 p.2 hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

/-! ### `(ω, ω') ↦ rowSplit k ω ω'` pushes `P ⊗ P` to `P`

This is the only measure-theoretic input of the file.  It is proved by testing on measurable
boxes: the preimage of a box splits as a product of the box restricted to the non-row
coordinates and the box restricted to the row coordinates, and `Measure.eq_infinitePi`
identifies the pushforward. -/

theorem preimage_rowSplit_pi (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (s : Finset (Sizes.SeqCoord d))
    (t : Sizes.SeqCoord d → Set ℝ) :
    (fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) ⁻¹'
        ((s : Set (Sizes.SeqCoord d)).pi t)
      = ((↑(s.filter fun c => ¬ IsRowCoord d n k c) : Set (Sizes.SeqCoord d)).pi t)
        ×ˢ ((↑(s.filter fun c => IsRowCoord d n k c) : Set (Sizes.SeqCoord d)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      rwa [rowSplit_apply_of_not_isRowCoord k ω ω' hc.2] at this
    · have := h c hc.1
      rwa [rowSplit_apply_of_isRowCoord k ω ω' hc.2] at this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcr : IsRowCoord d n k c
    · rw [rowSplit_apply_of_isRowCoord k ω ω' hcr]; exact h2 c ⟨hc, hcr⟩
    · rw [rowSplit_apply_of_not_isRowCoord k ω ω' hcr]; exact h1 c ⟨hc, hcr⟩

/-- **The Fubini statement behind `E_k`.**  Taking the row-`k` coordinates from one independent
copy and the rest from another reproduces the law `Sizes.seqP d`. -/
theorem measurePreserving_rowSplit (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) :
    MeasurePreserving (fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2)
      ((Sizes.seqP d).prod (Sizes.seqP d)) (Sizes.seqP d) := by
  refine ⟨measurable_rowSplit d n k, ?_⟩
  have hmeas := measurable_rowSplit d n k
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    preimage_rowSplit_pi d n k s t, Measure.prod_prod]
  show Sizes.seqP d _ * Sizes.seqP d _ = _
  rw [Sizes.seqP, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun i _ => ht i,
    mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s (IsRowCoord d n k) _

/-! ### The conditional expectation -/

/-- **`E_k[X] = E[X | H^{(k)}]`**, realized as the integral over the row-`k` coordinates with
all the other coordinates fixed.  This is an exact Fubini in the product model, *not* an
abstract `MeasureTheory.condExp`; in particular every identity below is pointwise in `ω`. -/
noncomputable def condRow (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (X : Sizes.SeqΩ d → ℂ) : Sizes.SeqΩ d → ℂ :=
  fun ω => ∫ ω', X (rowSplit d n k ω ω') ∂(Sizes.seqP d)

theorem condRow_apply (k : Idx (d.L n) (d.W n)) (X : Sizes.SeqΩ d → ℂ) (ω : Sizes.SeqΩ d) :
    condRow d n k X ω = ∫ ω', X (rowSplit d n k ω ω') ∂(Sizes.seqP d) := rfl

/-- `ω' ↦ X (rowSplit k ω ω')` is integrable for **every** fixed `ω`.  This is the (mild)
hypothesis under which `E_k` is additive. -/
def RowIntegrable (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (X : Sizes.SeqΩ d → ℂ) : Prop :=
  ∀ ω : Sizes.SeqΩ d, Integrable (fun ω' => X (rowSplit d n k ω ω')) (Sizes.seqP d)

theorem measurable_rowSplit_right (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) :
    Measurable fun ω' : Sizes.SeqΩ d => rowSplit d n k ω ω' :=
  (measurable_rowSplit d n k).comp (measurable_const.prodMk measurable_id)

theorem rowIntegrable_of_measurable_of_bound {k : Idx (d.L n) (d.W n)}
    {X : Sizes.SeqΩ d → ℂ} (hX : Measurable X)
    {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) : RowIntegrable d n k X := fun ω =>
  Integrable.mono' (integrable_const C)
    ((hX.comp (measurable_rowSplit_right d n k ω)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => hC _)

/-! #### Idempotence and the projection identity -/

/-- `E_k` applied to a function that does not depend on `ω` at all. -/
@[simp] theorem condRow_const (k : Idx (d.L n) (d.W n)) (c : ℂ) :
    condRow d n k (fun _ => c) = fun _ => c := by
  funext ω
  simp [condRow]

/-- **`E_k ∘ E_k = E_k`.**  No hypothesis: `E_k X` is already constant along row `k`, so the
second integral is the integral of a constant over a probability measure. -/
@[simp] theorem condRow_condRow (k : Idx (d.L n) (d.W n)) (X : Sizes.SeqΩ d → ℂ) :
    condRow d n k (condRow d n k X) = condRow d n k X := by
  funext ω
  have h : ∀ ω' : Sizes.SeqΩ d, condRow d n k X (rowSplit d n k ω ω') = condRow d n k X ω := by
    intro ω'
    simp only [condRow, rowSplit_rowSplit]
  simp only [condRow_apply (X := condRow d n k X), h]
  simp

/-- `E_k X` does not read row `k`: it is unchanged by the splitting. -/
theorem rowSplit_condRow (k : Idx (d.L n) (d.W n)) (X : Sizes.SeqΩ d → ℂ)
    (ω ω' : Sizes.SeqΩ d) :
    condRow d n k X (rowSplit d n k ω ω') = condRow d n k X ω := by
  simp only [condRow, rowSplit_rowSplit]

theorem condRow_sub (k : Idx (d.L n) (d.W n)) {X Y : Sizes.SeqΩ d → ℂ}
    (hX : RowIntegrable d n k X)
    (hY : RowIntegrable d n k Y) :
    condRow d n k (fun ω => X ω - Y ω) = fun ω => condRow d n k X ω - condRow d n k Y ω := by
  funext ω
  exact integral_sub (hX ω) (hY ω)

/-- **`E_k ∘ (1 - E_k) = 0`** -- the identity the vanishing lemma runs on.  Only the
integrability of `X` along row `k` is needed. -/
theorem condRow_sub_condRow (k : Idx (d.L n) (d.W n)) {X : Sizes.SeqΩ d → ℂ}
    (hX : RowIntegrable d n k X) :
    condRow d n k (fun ω => X ω - condRow d n k X ω) = 0 := by
  have hcond : RowIntegrable d n k (condRow d n k X) := by
    intro ω
    have : (fun ω' => condRow d n k X (rowSplit d n k ω ω')) = fun _ => condRow d n k X ω := by
      funext ω'; exact rowSplit_condRow k X ω ω'
    rw [this]
    exact integrable_const _
  funext ω
  rw [condRow_sub k hX hcond]
  have := congrFun (condRow_condRow k X) ω
  simp only [Pi.zero_apply, this, sub_self]

/-! #### Pulling out a factor that does not read row `k` -/

/-- **`g` is strictly independent of row `k`**: it reads only finitely many Gaussian
coordinates, and none of those is a row-`k` coordinate.

This is the shared hypothesis of the fluctuation-averaging argument: it is used for the
large-deviation estimates in the entries of row `k`, and to push `E_{k}` through a
product.  It is `FinDep` (a function of finitely many coordinates) with the witness set
constrained to avoid row `k`. -/
def FinDepOffRow (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n)) {V : Type*}
    (g : Sizes.SeqΩ d → V) : Prop :=
  ∃ I : Finset (Sizes.SeqCoord d), (∀ c ∈ I, ¬ IsRowCoord d n k c) ∧
    ∀ ω ω' : Sizes.SeqΩ d, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

/-- The defining consequence: a function strictly independent of row `k` does not see the
splitting. -/
theorem FinDepOffRow.rowSplit_eq {k : Idx (d.L n) (d.W n)} {V : Type*}
    {g : Sizes.SeqΩ d → V}
    (h : FinDepOffRow d n k g) (ω ω' : Sizes.SeqΩ d) : g (rowSplit d n k ω ω') = g ω := by
  obtain ⟨I, hI, hg⟩ := h
  exact (hg ω _ fun c hc => (rowSplit_apply_of_not_isRowCoord k ω ω' (hI c hc)).symm).symm

theorem FinDepOffRow.comp {k : Idx (d.L n) (d.W n)} {V W : Type*}
    {g : Sizes.SeqΩ d → V}
    (h : FinDepOffRow d n k g) (F : V → W) : FinDepOffRow d n k fun ω => F (g ω) :=
  let ⟨I, hI, hg⟩ := h
  ⟨I, hI, fun ω ω' hω => show F (g ω) = F (g ω') by rw [hg ω ω' hω]⟩

/-- A function strictly independent of row `k` is its own `E_k`. -/
theorem condRow_of_finDepOffRow {k : Idx (d.L n) (d.W n)} {X : Sizes.SeqΩ d → ℂ}
    (h : FinDepOffRow d n k X) :
    condRow d n k X = X := by
  funext ω
  have : (fun ω' => X (rowSplit d n k ω ω')) = fun _ => X ω := by
    funext ω'; exact h.rowSplit_eq ω ω'
  simp [condRow, this]

/-- The mirror image, with the independent factor on the right.  No integrability hypothesis:
`∫ f • c = (∫ f) • c` is unconditional. -/
theorem condRow_mul_of_finDepOffRow' {k : Idx (d.L n) (d.W n)}
    {X Y : Sizes.SeqΩ d → ℂ}
    (hY : FinDepOffRow d n k Y) :
    condRow d n k (fun ω => X ω * Y ω) = fun ω => condRow d n k X ω * Y ω := by
  funext ω
  have hY' : ∀ ω', Y (rowSplit d n k ω ω') = Y ω := hY.rowSplit_eq ω
  simp only [condRow_apply, hY']
  exact integral_mul_const (Y ω) _

/-! #### The tower property `E[E_k X] = E[X]` -/

/-- **`E[E_k X] = E[X]`.**  This is the one statement that really uses Fubini, through
`measurePreserving_rowSplit`. -/
theorem integral_condRow (k : Idx (d.L n) (d.W n)) {X : Sizes.SeqΩ d → ℂ}
    (hX : Integrable X (Sizes.seqP d)) :
    ∫ ω, condRow d n k X ω ∂(Sizes.seqP d) = ∫ ω, X ω ∂(Sizes.seqP d) := by
  have hmp := measurePreserving_rowSplit d n k
  have hmap : ((Sizes.seqP d).prod (Sizes.seqP d)).map
      (fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) = Sizes.seqP d :=
    hmp.map_eq
  have hXmeas : AEStronglyMeasurable X
      (((Sizes.seqP d).prod (Sizes.seqP d)).map
        fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) := by
    rw [hmap]; exact hX.aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun ω ω' => X (rowSplit d n k ω ω'))
      ((Sizes.seqP d).prod (Sizes.seqP d)) := by
    refine (integrable_map_measure hXmeas (measurable_rowSplit d n k).aemeasurable).1 ?_
    rw [hmap]; exact hX
  have hpush := integral_map (μ := (Sizes.seqP d).prod (Sizes.seqP d))
    (φ := fun p : Sizes.SeqΩ d × Sizes.SeqΩ d => rowSplit d n k p.1 p.2) (f := X)
    (measurable_rowSplit d n k).aemeasurable hXmeas
  rw [hmap] at hpush
  simp only [condRow_apply]
  rw [integral_integral hint]
  exact hpush.symm

/-! ### Strict independence of the minor resolvent `G^{(k)}`

Everything read off the minor matrix `H_u^{(k)}` is `FinDepOffRow`. -/

/-- **The master row-independence lemma.**  Anything read off the minor matrix
`H_u^{(k)} = (H_u).submatrix (· ≠ k) (· ≠ k)` is strictly independent of row `k`.  Every
"`G^{(k)}` does not see row `k`" statement is an instance of this. -/
theorem finDepOffRow_of_minor (d : Sizes) (n : ℕ) (u : ℝ) (k : Idx (d.L n) (d.W n)) {V : Type*}
    (F : Matrix {a : Idx (d.L n) (d.W n) // a ≠ k} {a : Idx (d.L n) (d.W n) // a ≠ k} ℂ → V) :
    FinDepOffRow d n k fun ω =>
      F ((Sizes.seqHflow d n u ω).submatrix
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ k} → Idx (d.L n) (d.W n))
        (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ k} → Idx (d.L n) (d.W n))) := by
  refine ⟨offRowCoord d n k, fun c hc => (Finset.mem_sdiff.1 hc).2, fun ω ω' hω => ?_⟩
  change F _ = F _
  rw [Hflow_submatrix_congr_offRowCoord u hω]

/-- The **minor resolvent** `G^{(k)} = (H_u^{(k)} - z)⁻¹`, as a *total* function of `ω`
(`Matrix.inv` is total, so no invertibility hypothesis is carried). -/
noncomputable def greenMinorMat (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (k : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) :
    Matrix {a : Idx (d.L n) (d.W n) // a ≠ k} {a : Idx (d.L n) (d.W n) // a ≠ k} ℂ :=
  ((Sizes.seqHflow d n u ω).submatrix
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ k} → Idx (d.L n) (d.W n))
    (Subtype.val : {a : Idx (d.L n) (d.W n) // a ≠ k} → Idx (d.L n) (d.W n))
      - z • (1 : Matrix {a : Idx (d.L n) (d.W n) // a ≠ k} {a : Idx (d.L n) (d.W n) // a ≠ k}
        ℂ))⁻¹

/-- **`G^{(k)}` is strictly independent of row `k`.** -/
theorem finDepOffRow_greenMinorMat (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx (d.L n) (d.W n)) :
    FinDepOffRow d n k (greenMinorMat d n u z k) :=
  finDepOffRow_of_minor d n u k fun M => (M - z • 1)⁻¹

/-- Entrywise form of `finDepOffRow_greenMinorMat`: each entry `G^{(k)}_{ab}` is a scalar
function of `ω` that reads no row-`k` coordinate. -/
theorem finDepOffRow_greenMinorMat_apply (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx (d.L n) (d.W n))
    (a b : {a : Idx (d.L n) (d.W n) // a ≠ k}) :
    FinDepOffRow d n k fun ω => greenMinorMat d n u z k ω a b :=
  (finDepOffRow_greenMinorMat d n u z k).comp fun M => M a b

/-- `greenMinorMat` is the paper's `G^{(k)}`: where the full resolvent exists and
`G_{kk} ≠ 0`, it is the explicit minor formula (4.9) of `RBM2D/Green/Minor.lean`. -/
theorem greenMinorMat_eq_minorGreen (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d)
    (hdet : IsUnit (Sizes.seqHflow d n u ω
      - z • (1 : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)).det)
    (hGkk : green (Sizes.seqHflow d n u ω) z k k ≠ 0) :
    greenMinorMat d n u z k ω = minorGreen (green (Sizes.seqHflow d n u ω) z) k :=
  inv_minor_resolvent hdet k hGkk

end RBM.Green
