/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.SumAll
import RBM2D.Loop.KBoundCut

/-!
# The sum-zero identity `R_n(1) = 0` and the bound `SigmaPi_alt_sumZero_le`

Paper: `(SZjadljsk)`, "which follows from the proof of Lemma 3.10 in [YY_25]"; here that proof
is redone in `d = 2`.

The proof follows the one-dimensional formalization, with private helpers `prod_cut`,
`Qlayer_cut`, `fin_congr`, `prod_cyc`, `prod_leaves_cut`, `Alayer_cut`,
`SumZeroWard_mSig_mul_of_ne`, `SumZeroWard_Alayer_eq_zero_of_empty`,
`SumZeroWard_norm_sum_Alayer_le`, `SumZeroWard_norm_Alayer_le`; the step (3.51) of [YY_25]
is inside the proof of `Qlayer_alt_one_eq_zero`.  The laminar API, the cut maps `FIn`/`FOut`
and the cut bijection `sum_cut` (with `Flong_FOut`, `Flong_FIn`, `Flong_eq_iff_cut`) are
private in `RBM2D/Loop/KBoundCut.lean` and are repeated here (sections 1–4 below).  `wIn`,
`sigmaIn`, `sigmaOut`, `unCol`, `col`, `shiftOut`, `exists_innermost`,
`Flong_subset_diagonals` are the public declarations of `KBoundCut.lean` and are not
redefined.

Changes for `d = 2`:
* the base bound (3.49) (`SumZeroWard_norm_sum_Alayer_le`) uses the Ward bound
  `Kcal_sumAll_le` at `L = 3`, `W = 1` with `Kcal_eq_sum_Kpi` (3.41) and
  `sum_Kpi_closed` (`|Z_3²| = 9`), in place of the one-dimensional bulk bound;
* `Kcal_sumAll_le` is stated only for `σ₀ = +`, `σ_{n-1} = -`.  The induction (3.50) is
  therefore run on the class `σ₀ ≠ σ_{n-1}`, which is closed under the cut (the inside polygon
  has end charges `σ_i ≠ σ_j` for a long edge `J = (i, j)`, the outside polygon keeps `σ₀`
  and `σ_{n-1}`), and `σ₀ = -` is reduced to `σ₀ = +` by complex conjugation
  (`mSig E (!s) = conj (mSig E s)`);
* the limit `t → 1` uses the Lipschitz bound of the edge factors on `[0, 1]` (bulk gap
  `gapK κ`).
-/

namespace RBM.KLoop

open Finset

/-! ## 1. Crossing-free families and the laminar API -/

private theorem not_crossing_self {n : ℕ} (e : Fin n × Fin n) : ¬Crossing e e := by
  unfold Crossing; omega

private theorem mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} :
    F ∈ TSP n ↔ F ⊆ diagonals n ∧ CrossingFree F := by
  simp [TSP]

section Laminar

variable {n : ℕ} [NeZero n]

/-! ### Laminarity -/

/-- `F` is a family of diagonals with no crossing pair: an element of `T_SP(n)`. -/
private def IsTSP (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ F, IsDiag n d.1 d.2) ∧ CrossingFree F

omit [NeZero n] in
private theorem isTSP_of_mem_TSP {F : Finset (Fin n × Fin n)} (h : F ∈ TSP n) : IsTSP F := by
  rw [mem_TSP] at h
  refine ⟨fun d hd => ?_, h.2⟩
  have := h.1 hd
  simp only [diagonals, mem_filter, mem_univ, true_and] at this
  exact this

private theorem arcLe_wholeP (d : Fin n × Fin n) : ArcLe d (wholeP n) := by
  refine ⟨Fin.zero_le _, ?_⟩
  simp only [wholeP, Fin.le_def]
  have := d.2.isLt
  omega

private theorem lt_of_mem_nodes {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ nodes F) : d.1 < d.2 := by
  rcases mem_insert.1 hd with rfl | hd
  · simp only [wholeP, Fin.lt_def, Fin.val_zero]; omega
  · exact (hF.1 d hd).1

/-- **Laminarity**: two nodes are nested or have disjoint arcs. -/
private theorem nodes_laminar {F : Finset (Fin n × Fin n)} (hF : IsTSP F) {d e : Fin n × Fin n}
    (hd : d ∈ nodes F) (he : e ∈ nodes F) :
    ArcLe d e ∨ ArcLe e d ∨ d.2 ≤ e.1 ∨ e.2 ≤ d.1 := by
  rcases mem_insert.1 he with rfl | he'
  · exact Or.inl (arcLe_wholeP d)
  rcases mem_insert.1 hd with rfl | hd'
  · exact Or.inr (Or.inl (arcLe_wholeP e))
  have h1 := hF.2 d hd' e he'
  have hd2 := (hF.1 d hd').1
  have he2 := (hF.1 e he').1
  simp only [Crossing, not_or, not_and, not_lt] at h1
  simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 hd2 he2 ⊢
  omega

end Laminar

/-! ## 2. The inside and outside families of a cut
(without the tree-value lemmas `gval_in_eq`, `gval_out_eq`) -/

section CutIn

variable {n : ℕ} [NeZero n]

/-- Shift a region pair inside `J` to the inside polygon: `(x₁, x₂) ↦ (x₁ - i, x₂ - i)`. -/
private def shiftIn (J : Fin n × Fin n) (d : Fin n × Fin n) : Fin (wIn J + 1) × Fin (wIn J + 1) :=
  (⟨min (d.1.val - J.1.val) (wIn J), by omega⟩, ⟨min (d.2.val - J.1.val) (wIn J), by omega⟩)

/-- The family of the inside polygon: the edges strictly inside `J`, shifted. -/
private def FIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) :=
  (F.filter fun d => ArcLe d J ∧ d ≠ J).image (shiftIn J)

variable {J : Fin n × Fin n}

omit [NeZero n] in
private theorem shiftIn_val {d : Fin n × Fin n} (h : ArcLe d J) (h12 : d.1 ≤ d.2) :
    (shiftIn J d).1.val = d.1.val - J.1.val ∧ (shiftIn J d).2.val = d.2.val - J.1.val := by
  simp only [ArcLe, Fin.le_def] at h h12
  simp only [shiftIn, wIn]
  constructor <;> omega

omit [NeZero n] in
private theorem shiftIn_injOn {d e : Fin n × Fin n} (hd : ArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : ArcLe e J) (he12 : e.1 ≤ e.2) (h : shiftIn J d = shiftIn J e) : d = e := by
  have h1 := shiftIn_val hd hd12
  have h2 := shiftIn_val he he12
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  simp only [ArcLe, Fin.le_def] at hd he hd12 he12
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

end CutIn

section CutOut

variable {n : ℕ} [NeZero n]

/-- The family of the outside polygon: the edges not inside `J`, collapsed. -/
private def FOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) :=
  (F.filter fun d => ¬ArcLe d J).image (shiftOut J)

variable {J : Fin n × Fin n}

/-- The endpoint condition of an outside node: no endpoint strictly inside `J`. -/
private def OutEnds (J : Fin n × Fin n) (x : Fin n × Fin n) : Prop :=
  (x.1.val ≤ J.1.val ∨ J.2.val ≤ x.1.val) ∧ (x.2.val ≤ J.1.val ∨ J.2.val ≤ x.2.val) ∧
    x.1.val < x.2.val

omit [NeZero n] in
private theorem col_val {r : ℕ} (hr' : r < n) (hJ2 : J.1.val < J.2.val) :
    min (col J r) (n - wIn J) = col J r := by
  have := J.2.isLt
  simp only [col, wIn] at *
  split_ifs <;> omega

omit [NeZero n] in
private theorem shiftOut_val (x : Fin n × Fin n) (hJ2 : J.1.val < J.2.val) :
    (shiftOut J x).1.val = col J x.1.val ∧ (shiftOut J x).2.val = col J x.2.val :=
  ⟨col_val x.1.isLt hJ2, col_val x.2.isLt hJ2⟩

omit [NeZero n] in
/-- `col` is strictly monotone on points outside the open arc of `J`. -/
private theorem col_le_iff {r s : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hs : s ≤ J.1.val ∨ J.2.val ≤ s)
    (hJ : J.1.val + 2 ≤ J.2.val) : col J r ≤ col J s ↔ r ≤ s := by
  simp only [col, wIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem shiftOut_injOn {d e : Fin n × Fin n} (hd : OutEnds J d) (he : OutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) (h : shiftOut J d = shiftOut J e) : d = e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have h2 := shiftOut_val e hJ2
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  have a1 := (col_le_iff hd.1 he.1 hJ).1 (by omega)
  have a2 := (col_le_iff he.1 hd.1 hJ).1 (by omega)
  have a3 := (col_le_iff hd.2.1 he.2.1 hJ).1 (by omega)
  have a4 := (col_le_iff he.2.1 hd.2.1 hJ).1 (by omega)
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hJ

omit [NeZero n] in
private theorem diag_width : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hF.1 J hJ
  rw [Fin.lt_def] at h1
  omega

include hn in
private theorem outEnds_of {x : Fin n × Fin n} (hx : x ∈ nodes F)
    (hxJ : ¬ArcLe x J) : OutEnds J x := by
  have hlt := lt_of_mem_nodes hF hn hx
  have hJw := diag_width hF hJ
  rcases nodes_laminar hF hx (mem_nodes_of_mem hJ) with h | h | h | h
  · exact absurd h hxJ
  all_goals simp only [ArcLe, Fin.le_def, Fin.lt_def] at h hlt ⊢
  all_goals exact ⟨by omega, by omega, hlt⟩

end CutOut

/-! ## 3. The cut bijection `sum_cut` -/

section CutBij

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- Lift a region pair of the inside polygon back: `(i', j') ↦ (i' + J.1, j' + J.1)`. -/
private def unShift (J : Fin n × Fin n) (h : Fin (wIn J + 1) × Fin (wIn J + 1)) : Fin n × Fin n :=
  (⟨min (h.1.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (h.2.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩)

/-- Lift a region pair of the outside polygon back. -/
private def unColP (J : Fin n × Fin n) (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) :
    Fin n × Fin n :=
  (⟨min (unCol J g.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (unCol J g.2.val) (n - 1), by have := NeZero.pos n; omega⟩)

private theorem unShift_val (h : Fin (wIn J + 1) × Fin (wIn J + 1)) :
    (unShift J h).1.val = h.1.val + J.1.val ∧ (unShift J h).2.val = h.2.val + J.1.val := by
  have h1 := h.1.isLt; have h2 := h.2.isLt; have := J.2.isLt
  simp only [unShift, wIn] at *
  constructor <;> omega

omit [NeZero n] in
private theorem unCol_lt {r : ℕ} (hr : r < n - wIn J + 1)
    (hJ : J.1.val < J.2.val) : unCol J r < n := by
  have := J.2.isLt
  simp only [unCol, wIn] at *
  split_ifs <;> omega

private theorem unColP_val (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1))
    (hJ : J.1.val < J.2.val) :
    (unColP J g).1.val = unCol J g.1.val ∧ (unColP J g).2.val = unCol J g.2.val := by
  have h1 := unCol_lt g.1.isLt hJ; have h2 := unCol_lt g.2.isLt hJ
  simp only [unColP]
  constructor <;> omega

omit [NeZero n] in
private theorem unCol_of_le {r : ℕ} (h : r ≤ J.1.val) : unCol J r = r := by simp [unCol, h]

omit [NeZero n] in
private theorem unCol_of_gt {r : ℕ} (h : J.1.val < r) : unCol J r = r + (wIn J - 1) := by
  simp [unCol, not_le.2 h]

omit [NeZero n] in
private theorem col_unCol {r : ℕ} : col J (unCol J r) = r := by
  simp only [col, unCol, wIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem unCol_col {r : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hJ : J.1.val + 2 ≤ J.2.val) :
    unCol J (col J r) = r := by
  simp only [col, unCol, wIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem unCol_ends {r : ℕ} (hJ : J.1.val + 2 ≤ J.2.val) :
    unCol J r ≤ J.1.val ∨ J.2.val ≤ unCol J r := by
  simp only [unCol, wIn]
  split_ifs <;> omega

private theorem shiftIn_unShift (h : Fin (wIn J + 1) × Fin (wIn J + 1)) :
    shiftIn J (unShift J h) = h := by
  have hv := unShift_val h
  have h1 := h.1.isLt; have h2 := h.2.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [shiftIn, hv] <;> omega

private theorem unShift_shiftIn {d : Fin n × Fin n} (hd : ArcLe d J) (h12 : d.1 ≤ d.2) :
    unShift J (shiftIn J d) = d := by
  have hv := shiftIn_val hd h12
  simp only [ArcLe, Fin.le_def] at hd h12
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [unShift, hv] <;>
    have := d.2.isLt <;> omega

private theorem shiftOut_unColP (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1))
    (hJ : J.1.val + 2 ≤ J.2.val) : shiftOut J (unColP J g) = g := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := unColP_val g hJ2
  have h1 := shiftOut_val (unColP J g) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [h1.1, hv.1, col_unCol]
  · rw [h1.2, hv.2, col_unCol]

private theorem unColP_shiftOut {d : Fin n × Fin n} (hd : OutEnds J d)
    (hJ : J.1.val + 2 ≤ J.2.val) :
    unColP J (shiftOut J d) = d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have hv := unColP_val (shiftOut J d) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [hv.1, h1.1, unCol_col hd.1 hJ]
  · rw [hv.2, h1.2, unCol_col hd.2.1 hJ]

/-- A lifted outside pair has no endpoint strictly inside `J`. -/
private theorem outEnds_unColP (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) (hg : g.1 < g.2)
    (hJ : J.1.val + 2 ≤ J.2.val) : OutEnds J (unColP J g) := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := unColP_val g hJ2
  rw [Fin.lt_def] at hg
  refine ⟨hv.1 ▸ unCol_ends hJ, hv.2 ▸ unCol_ends hJ, ?_⟩
  rw [hv.1, hv.2]
  simp only [unCol, wIn]; split_ifs <;> omega

/-- Glue an outside and an inside family back along `J`. -/
private def glueF (J : Fin n × Fin n) (G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)))
    (H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))) : Finset (Fin n × Fin n) :=
  insert J (G.image (unColP J) ∪ H.image (unShift J))

private theorem mem_diagonals_iff {m : ℕ}
    {d : Fin m × Fin m} : d ∈ diagonals m ↔ IsDiag m d.1 d.2 := by
  simp [diagonals]

variable (hJd : IsDiag n J.1 J.2)
include hJd

omit [NeZero n] in
private theorem width_of_isDiag : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hJd; rw [Fin.lt_def] at h1; omega

omit [NeZero n] hJd in
/-- The inside family is a crossing-free family of diagonals. -/
private theorem FIn_mem_TSP {F : Finset (Fin n × Fin n)} (hF : IsTSP F) :
    FIn F J ∈ TSP (wIn J + 1) := by
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ, hne⟩ := mem_filter.1 hd
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := shiftIn_val hdJ (le_of_lt d1)
    rw [mem_diagonals_iff]
    have hJ' := hdJ
    simp only [ArcLe, Fin.le_def] at hJ'
    have hne' : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    rw [Fin.lt_def] at d1
    refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
    rw [hv.1, hv.2]; simp only [wIn]; omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
    have hd1 := (hF.1 d hdF).1
    have he1 := (hF.1 e heF).1
    have hv := shiftIn_val hdJ (le_of_lt hd1)
    have hw := shiftIn_val heJ (le_of_lt he1)
    apply hF.2 d hdF e heF
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [ArcLe, Fin.le_def] at hdJ heJ
    omega

/-- The outside family is a crossing-free family of diagonals. -/
private theorem FOut_mem_TSP {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    FOut F J ∈ TSP (n - wIn J + 1) := by
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    have hE := outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := shiftOut_val d hJ2
    have hne : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hdJ (by simp only [ArcLe, Fin.le_def]; omega)
    have hn2 := J.2.isLt
    have hd2 := d.2.isLt
    rw [mem_diagonals_iff]
    obtain ⟨e1, e2, e3⟩ := hE
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.lt_def, hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ⟩ := mem_filter.1 he
    have hdE := outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ
    have heE := outEnds_of hF hn hJ (mem_nodes_of_mem heF) heJ
    have hv := shiftOut_val d hJ2
    have hw := shiftOut_val e hJ2
    apply hF.2 d hdF e heF
    obtain ⟨a1, a2, a3⟩ := hdE
    obtain ⟨b1, b2, b3⟩ := heE
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [col, wIn] at hc
    split_ifs at hc <;> omega

private theorem arcLe_unShift (h : Fin (wIn J + 1) × Fin (wIn J + 1)) : ArcLe (unShift J h) J := by
  have hv := unShift_val h
  have hJw := width_of_isDiag hJd
  have h2 := h.2.isLt
  have hw : wIn J = J.2.val - J.1.val := rfl
  constructor
  · rw [Fin.le_def, hv.1]; omega
  · rw [Fin.le_def, hv.2]; omega

omit hJd in
private theorem unShift_ne {h : Fin (wIn J + 1) × Fin (wIn J + 1)}
    (hh : IsDiag (wIn J + 1) h.1 h.2) :
    unShift J h ≠ J := by
  intro he
  have hv := unShift_val h
  obtain ⟨-, -, h3⟩ := hh
  apply h3
  have e1 := congrArg (fun x => x.1.val) he
  have e2 := congrArg (fun x => x.2.val) he
  simp only [hv.1, hv.2] at e1 e2
  simp only [wIn]; omega

private theorem not_arcLe_unColP {g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)}
    (hg : IsDiag (n - wIn J + 1) g.1 g.2) : ¬ArcLe (unColP J g) J := by
  have hJw := width_of_isDiag hJd
  have hv := unColP_val g (by omega)
  obtain ⟨g1, g2, -⟩ := hg
  rw [Fin.lt_def] at g1
  simp only [ArcLe, Fin.le_def, hv.1, hv.2, unCol, wIn]
  split_ifs <;> omega

/-- The glued family is a crossing-free family of diagonals. -/
private theorem glueF_mem_TSP {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1))
    (hH : H ∈ TSP (wIn J + 1)) : glueF J G H ∈ TSP n := by
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP] at hG hH ⊢
  have hGd : ∀ g ∈ G, IsDiag _ g.1 g.2 := fun g hg => mem_diagonals_iff.1 (hG.1 hg)
  have hHd : ∀ h ∈ H, IsDiag _ h.1 h.2 := fun h hh => mem_diagonals_iff.1 (hH.1 hh)
  have hn2 := J.2.isLt
  -- the three kinds of elements
  have kinds : ∀ x ∈ glueF J G H, x = J ∨ (∃ g ∈ G, unColP J g = x) ∨
      (∃ h ∈ H, unShift J h = x) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact Or.inl rfl
    rcases mem_union.1 hx with hx | hx
    · exact Or.inr (Or.inl (mem_image.1 hx))
    · exact Or.inr (Or.inr (mem_image.1 hx))
  constructor
  · intro x hx
    rw [mem_diagonals_iff]
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩
    · exact hJd
    · have hv := unColP_val g hJ2
      obtain ⟨g1, g2, g3⟩ := hGd g hg
      rw [Fin.lt_def] at g1
      refine ⟨?_, ?_, ?_⟩
      · rw [Fin.lt_def, hv.1, hv.2]; simp only [unCol, wIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [unCol, wIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [unCol, wIn] at g3 ⊢; split_ifs <;> omega
    · have hv := unShift_val h
      obtain ⟨h1, h2, h3⟩ := hHd h hh
      rw [Fin.lt_def] at h1
      have hb := h.2.isLt
      refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
      rw [hv.1, hv.2]; simp only [wIn] at h3 hb ⊢; omega
  · -- crossing-freeness
    have outE : ∀ g ∈ G, OutEnds J (unColP J g) := fun g hg =>
      outEnds_unColP g (hGd g hg).1 hJw
    have crossJ : ∀ x, OutEnds J x → ¬Crossing J x ∧ ¬Crossing x J := by
      intro x ⟨a1, a2, a3⟩
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossIn : ∀ h, ¬Crossing J (unShift J h) ∧ ¬Crossing (unShift J h) J := by
      intro h
      have := arcLe_unShift hJd h
      simp only [ArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGH : ∀ g h, OutEnds J (unColP J g) →
        ¬Crossing (unColP J g) (unShift J h) ∧ ¬Crossing (unShift J h) (unColP J g) := by
      intro g h ⟨a1, a2, a3⟩
      have := arcLe_unShift hJd h
      simp only [ArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGG : ∀ g ∈ G, ∀ g' ∈ G, ¬Crossing (unColP J g) (unColP J g') := by
      intro g hg g' hg' hc
      apply hG.2 g hg g' hg'
      have hv := unColP_val g hJ2
      have hw := unColP_val g' hJ2
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2, unCol, wIn] at hc ⊢
      split_ifs at hc <;> omega
    have crossHH : ∀ h ∈ H, ∀ h' ∈ H, ¬Crossing (unShift J h) (unShift J h') := by
      intro h hh h' hh' hc
      apply hH.2 h hh h' hh'
      have hv := unShift_val h
      have hw := unShift_val h'
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
      omega
    intro x hx y hy
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩ <;>
      rcases kinds y hy with rfl | ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
    · exact not_crossing_self _
    · exact (crossJ _ (outE g' hg')).1
    · exact (crossIn h').1
    · exact (crossJ _ (outE g hg)).2
    · exact crossGG g hg g' hg'
    · exact (crossGH g h' (outE g hg)).1
    · exact (crossIn h).2
    · exact (crossGH g' h (outE g' hg')).2
    · exact crossHH h hh h' hh'

private theorem FIn_glueF {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1))
    (hH : H ∈ TSP (wIn J + 1)) : FIn (glueF J G H) J = H := by
  rw [mem_TSP] at hG hH
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ, hne⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd rfl hne
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      exact absurd hxJ (not_arcLe_unColP hJd (mem_diagonals_iff.1 (hG.1 hg)))
    · obtain ⟨h, hh, rfl⟩ := mem_image.1 hxg
      rw [shiftIn_unShift]; exact hh
  · intro hy
    refine mem_image.2 ⟨unShift J y, mem_filter.2 ⟨?_, arcLe_unShift hJd y,
      unShift_ne (mem_diagonals_iff.1 (hH.1 hy))⟩, shiftIn_unShift y⟩
    exact mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ hy))

private theorem FOut_glueF {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1)) :
    FOut (glueF J G H) J = G := by
  have hJw := width_of_isDiag hJd
  rw [mem_TSP] at hG
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd ⟨le_refl _, le_refl _⟩ hxJ
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      rw [shiftOut_unColP g hJw]; exact hg
    · obtain ⟨h, -, rfl⟩ := mem_image.1 hxg
      exact absurd (arcLe_unShift hJd h) hxJ
  · intro hy
    refine mem_image.2 ⟨unColP J y, mem_filter.2 ⟨?_,
      not_arcLe_unColP hJd (mem_diagonals_iff.1 (hG.1 hy))⟩, shiftOut_unColP y hJw⟩
    exact mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ hy))

private theorem glueF_cut {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    glueF J (FOut F J) (FIn F J) = F := by
  have hJw := width_of_isDiag hJd
  ext x
  constructor
  · intro hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hJ
    rcases mem_union.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      rw [unColP_shiftOut (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw]
      exact hdF
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      rw [unShift_shiftIn hdJ (le_of_lt (hF.1 d hdF).1)]
      exact hdF
  · intro hx
    by_cases h1 : x = J
    · rw [h1]; exact mem_insert_self _ _
    refine mem_insert_of_mem ?_
    by_cases h2 : ArcLe x J
    · refine mem_union_right _ (mem_image.2 ⟨shiftIn J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2, h1⟩), unShift_shiftIn h2 (le_of_lt (hF.1 x hx).1)⟩)
    · refine mem_union_left _ (mem_image.2 ⟨shiftOut J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2⟩), unColP_shiftOut
          (outEnds_of hF hn hJ (mem_nodes_of_mem hx) h2) hJw⟩)

/-- **The cut bijection**: `{F ∈ T_SP(n) : J ∈ F} ≃ T_SP(outside) × T_SP(inside)`. -/
private theorem sum_cut (hn : 2 ≤ n)
    (f : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) →
      Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) → ℂ) :
    ∑ F ∈ (TSP n).filter (fun F => J ∈ F), f (FOut F J) (FIn F J)
      = ∑ G ∈ TSP (n - wIn J + 1), ∑ H ∈ TSP (wIn J + 1), f G H := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun F => (FOut F J, FIn F J)) (fun p => glueF J p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := isTSP_of_mem_TSP hFT
    exact mem_product.2 ⟨FOut_mem_TSP hJd hF' hn hJF, FIn_mem_TSP hF'⟩
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact mem_filter.2 ⟨glueF_mem_TSP hJd hG hH, mem_insert_self _ _⟩
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    exact glueF_cut hJd (isTSP_of_mem_TSP hFT) hn hJF
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact Prod.ext (FOut_glueF hJd hG) (FIn_glueF hJd hG hH)
  · intro F _
    rfl

end CutBij


/-! ## 4. The layer condition across the cut -/

section LayerFacts

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

omit [NeZero n] in
private theorem mem_Flong {F : Finset (Fin n × Fin n)} {σ : Fin n → Bool} {d : Fin n × Fin n} :
    d ∈ Flong F σ ↔ d ∈ F ∧ σ d.1 ≠ σ d.2 := mem_filter

omit [NeZero n] in
private theorem Flong_subset (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) :
    Flong F σ ⊆ F :=
  filter_subset _ _

omit [NeZero n] in
private theorem arcLe_le {d : Fin n × Fin n} (h : ArcLe d J) (h12 : d.1 ≤ d.2) :
    J.1.val ≤ d.1.val ∧ d.2.val ≤ J.2.val ∧ d.1.val ≤ d.2.val := by
  simp only [ArcLe, Fin.le_def] at h h12
  exact ⟨h.1, h.2, h12⟩

private theorem sigmaIn_shiftIn (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : ArcLe d J)
    (h12 : d.1 ≤ d.2) :
    sigmaIn σ J (shiftIn J d).1 = σ d.1 ∧ sigmaIn σ J (shiftIn J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := shiftIn_val hd h12
  obtain ⟨a1, a2, a3⟩ := arcLe_le hd h12
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  constructor <;> (unfold sigmaIn; congr 1; ext; simp only [h1, h2]; omega)

private theorem sigmaOut_shiftOut (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : OutEnds J d)
    (hJ : J.1.val + 2 ≤ J.2.val) :
    sigmaOut σ J (shiftOut J d).1 = σ d.1 ∧ sigmaOut σ J (shiftOut J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := shiftOut_val d (by omega : J.1.val < J.2.val)
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  have e1 := unCol_col hd.1 hJ
  have e2 := unCol_col hd.2.1 hJ
  constructor <;> (unfold sigmaOut; congr 1; ext; simp only [h1, h2, e1, e2]; omega)

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hn hJ

/-- The long edges of the outside family are the outside long edges of `F`. -/
private theorem Flong_FOut (σ : Fin n → Bool) :
    Flong (FOut F J) (sigmaOut σ J) =
      ((Flong F σ).filter fun d => ¬ArcLe d J).image (shiftOut J) := by
  have hJw := diag_width hF hJ
  unfold Flong FOut
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, hdJ⟩, by rwa [e1, e2]⟩

omit hn hJ in
/-- The long edges of the inside family are the long edges of `F` strictly inside `J`. -/
private theorem Flong_FIn (σ : Fin n → Bool) :
    Flong (FIn F J) (sigmaIn σ J) =
      ((Flong F σ).filter fun d => ArcLe d J ∧ d ≠ J).image (shiftIn J) := by
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  unfold Flong FIn
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ, hne⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ, hne⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ, hne⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, hdJ, hne⟩, by rwa [e1, e2]⟩

/-- **The layer condition across the cut.**  Let `π = F_long(F₀, σ)` for some tree `F₀` and let
`J ∈ π` be innermost.  Then a tree `F ∋ J` lies in the layer `π` iff its inside family has no
long edges and the long edges of its outside family are `π ∖ {J}`, collapsed. -/
private theorem Flong_eq_iff_cut (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}
    (hF₀ : IsTSP F₀)
    {π : Finset (Fin n × Fin n)} (hπ : Flong F₀ σ = π) (hJπ : J ∈ π)
    (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Flong F σ = π ↔ Flong (FOut F J) (sigmaOut σ J) = (π.erase J).image (shiftOut J) ∧
      Flong (FIn F J) (sigmaIn σ J) = ∅ := by
  have hJw := diag_width hF hJ
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJπ)).2
  have hπout : ∀ e ∈ π.erase J, OutEnds J e ∧ ¬ArcLe e J := by
    intro e he
    obtain ⟨hne, heπ⟩ := mem_erase.1 he
    have hnot : ¬ArcLe e J := fun h => hne (hinner e heπ h)
    exact ⟨outEnds_of hF₀ hn hJF₀ (mem_nodes_of_mem (Flong_subset F₀ σ (hπ ▸ heπ))) hnot, hnot⟩
  have hπerase : π.filter (fun d => ¬ArcLe d J) = π.erase J := by
    ext e
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨heπ, hnot⟩
      exact ⟨fun h => hnot (h ▸ ⟨le_rfl, le_rfl⟩), heπ⟩
    · rintro ⟨hne, heπ⟩
      exact ⟨heπ, fun h => hne (hinner e heπ h)⟩
  have hπin : π.filter (fun d => ArcLe d J ∧ d ≠ J) = ∅ := by
    refine filter_eq_empty_iff.2 fun e heπ h => h.2 (hinner e heπ h.1)
  rw [Flong_FOut hF hn hJ, Flong_FIn hF σ]
  constructor
  · intro h
    rw [h, hπerase, hπin, image_empty]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hout, hin⟩
    have hin' : (Flong F σ).filter (fun d => ArcLe d J ∧ d ≠ J) = ∅ := image_eq_empty.1 hin
    have hout' : (Flong F σ).filter (fun d => ¬ArcLe d J) = π.erase J := by
      ext e
      constructor
      · intro he
        obtain ⟨heF, heJ⟩ := mem_filter.1 he
        have heO := outEnds_of hF hn hJ (mem_nodes_of_mem (Flong_subset F σ heF)) heJ
        have : shiftOut J e ∈ (π.erase J).image (shiftOut J) := hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        rwa [← shiftOut_injOn (hπout e' he').1 heO hJw hee']
      · intro he
        have : shiftOut J e ∈ ((Flong F σ).filter fun d => ¬ArcLe d J).image (shiftOut J) :=
          hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        obtain ⟨he'F, he'J⟩ := mem_filter.1 he'
        have he'O := outEnds_of hF hn hJ (mem_nodes_of_mem (Flong_subset F σ he'F)) he'J
        rwa [← shiftOut_injOn he'O (hπout e he).1 hJw hee']
    ext e
    constructor
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ hJπ
      by_cases hin : ArcLe e J
      · have : e ∈ (Flong F σ).filter (fun d => ArcLe d J ∧ d ≠ J) := mem_filter.2 ⟨he, hin, heJ⟩
        rw [hin'] at this
        exact absurd this (notMem_empty e)
      · have : e ∈ (Flong F σ).filter (fun d => ¬ArcLe d J) := mem_filter.2 ⟨he, hin⟩
        rw [hout'] at this
        exact (mem_erase.1 this).2
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ mem_Flong.2 ⟨hJ, hJlong⟩
      · have : e ∈ π.erase J := mem_erase.2 ⟨heJ, he⟩
        rw [← hout'] at this
        exact (mem_filter.1 this).1

end LayerFacts

/-! ## 5. The molecule factorization at an innermost long edge -/

section MoleculeCut

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **A product over the edges of `F ∋ J` splits over the cut**: the edge `J`, the outside
family and the inside family, each with its own charges. -/
private theorem prod_cut {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (σ : Fin n → Bool) (w : Bool → Bool → ℂ) :
    ∏ e ∈ F, w (σ e.1) (σ e.2) =
      w (σ J.1) (σ J.2) * (∏ g ∈ FOut F J, w (sigmaOut σ J g.1) (sigmaOut σ J g.2)) *
        ∏ h ∈ FIn F J, w (sigmaIn σ J h.1) (sigmaIn σ J h.2) := by
  have hJw := diag_width hF hJ
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  rw [← mul_prod_erase F _ hJ, mul_assoc]
  congr 1
  rw [← prod_filter_mul_prod_filter_not (F.erase J) (fun d => ArcLe d J), mul_comm]
  have hout : (F.erase J).filter (fun d => ¬ArcLe d J) = F.filter (fun d => ¬ArcLe d J) := by
    ext d
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨fun hdJ => h.2 (hdJ ▸ ⟨le_rfl, le_rfl⟩), h.1⟩, h.2⟩
  have hin : (F.erase J).filter (fun d => ArcLe d J) = F.filter (fun d => ArcLe d J ∧ d ≠ J) := by
    ext d
    simp only [mem_filter, mem_erase]
    tauto
  rw [hout, hin]
  congr 1
  · unfold FOut
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ⟩ := mem_filter.1 he
      exact shiftOut_injOn (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ)
        (outEnds_of hF hn hJ (mem_nodes_of_mem heF) heJ) hJw h
  · unfold FIn
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
      exact shiftIn_injOn hdJ (h12 d hdF) heJ (h12 e heF) h

/-- **The molecule factorization (3.53)–(3.58), closed form.**  If `J` is an innermost long
edge of the layer `π = F_long(F₀, σ)`, then `Q(σ, π) = r_J · Q(σ_out, π ∖ {J}) · Q(σ_in, ∅)`. -/
private theorem Qlayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : Flong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Qlayer m t σ π = edgeR m t (σ J.1) (σ J.2) *
      Qlayer m t (sigmaOut σ J) ((π.erase J).image (shiftOut J)) *
        Qlayer m t (sigmaIn σ J) ∅ := by
  have hF₀' := isTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  set π' := (π.erase J).image (shiftOut J)
  set f : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) →
      Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) → ℂ := fun G H =>
    (if Flong G (sigmaOut σ J) = π' then
      ∏ g ∈ G, edgeR m t (sigmaOut σ J g.1) (sigmaOut σ J g.2) else 0) *
    (if Flong H (sigmaIn σ J) = ∅ then
      ∏ h ∈ H, edgeR m t (sigmaIn σ J h.1) (sigmaIn σ J h.2) else 0)
  have hlayer : TSPlong n σ π = ((TSP n).filter fun F => J ∈ F).filter fun F => Flong F σ = π := by
    ext F
    simp only [TSPlong, mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if Flong F σ = π then ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2) else 0)
        = edgeR m t (σ J.1) (σ J.2) * f (FOut F J) (FIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := isTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn hJF σ hF₀' hπ hJπ hinner
    by_cases h : Flong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : Flong (FOut F J) (sigmaOut σ J) = π' := h1
      simp only [f, h, h1', h2, ↓reduceIte, prod_cut hF' hn hJF σ]
      ring
    · simp only [f, h, ↓reduceIte]
      by_cases h1 : Flong (FOut F J) (sigmaOut σ J) = π'
      · have h2 : ¬Flong (FIn F J) (sigmaIn σ J) = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [h2]
      · simp [h1]
  unfold Qlayer
  rw [hlayer, sum_filter, sum_congr rfl hpt, ← mul_sum, sum_cut hJd hn f]
  simp only [f, ← sum_mul_sum, ← sum_filter]
  rw [mul_assoc]
  rfl

end MoleculeCut

section Leaves

private theorem fin_congr {N : ℕ} {α : Type*} (σ : Fin N → α) {a b : ℕ} (ha : a < N)
    (hb : b < N) (h : a = b) : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := by
  subst h; rfl

/-- A cyclic product over consecutive pairs, written over `range`. -/
private theorem prod_cyc {k : ℕ} (τ : Fin (k + 1) → Bool) (g : Bool → Bool → ℂ) :
    ∏ v : Fin (k + 1), g (τ v) (τ (v + 1)) =
      (∏ v ∈ range k, g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) *
        g (τ (Fin.last k)) (τ 0) := by
  rw [Fin.prod_univ_castSucc, Fin.last_add_one]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← Fin.prod_univ_eq_prod_range
    (fun v => g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) k]
  refine prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have h1 : Fin.castSucc i = ⟨min i k, by omega⟩ :=
    Fin.ext (by rw [Fin.val_castSucc]; exact (min_eq_left hi.le).symm)
  have h2 : Fin.castSucc i + 1 = ⟨min (i + 1) k, by omega⟩ := by
    ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc]
    exact (min_eq_left hi).symm
  rw [h2, h1]

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The boundary edges across the cut**:
`∏_v g(σ_v, σ_{v+1}) · g(σ_j, σ_i) g(σ_i, σ_j) = ∏_{in} · ∏_{out}`. -/
private theorem prod_leaves_cut (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool)
    (g : Bool → Bool → ℂ) :
    (∏ v : Fin n, g (σ v) (σ (v + 1))) * (g (σ J.2) (σ J.1) * g (σ J.1) (σ J.2)) =
      (∏ k : Fin (wIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1))) *
        ∏ k : Fin (n - wIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  obtain ⟨hlt, hne1, hnot⟩ := hJd
  rw [Fin.lt_def] at hlt
  have hjn : J.2.val ≤ n' := by have := J.2.isLt; omega
  have hw : wIn J = J.2.val - J.1.val := rfl
  have hunc : ∀ v, v ≤ J.1.val → unCol J v = v := fun v hv => unCol_of_le hv
  have hunc' : ∀ v, J.1.val < v → unCol J v = v + (wIn J - 1) := fun v hv => unCol_of_gt hv
  set σ' : ℕ → Bool := fun r => σ ⟨min r n', by omega⟩ with hσ'
  set G : ℕ → ℂ := fun r => g (σ' r) (σ' (r + 1)) with hG
  have hJ1 : σ J.1 = σ' J.1.val := fin_congr σ J.1.isLt (by omega) (by omega)
  have hJ2 : σ J.2 = σ' J.2.val := fin_congr σ J.2.isLt (by omega) (by omega)
  have horig : ∏ v : Fin (n' + 1), g (σ v) (σ (v + 1)) =
      (∏ v ∈ range n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc σ g]
    refine congrArg₂ (· * ·) rfl (congrArg₂ g ?_ ?_) <;>
      exact fin_congr σ _ _ (by simp)
  have hin : ∏ k : Fin (wIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1)) =
      (∏ v ∈ Ico J.1.val J.2.val, G v) * g (σ' J.2.val) (σ' J.1.val) := by
    rw [prod_cyc (sigmaIn σ J) g, prod_Ico_eq_prod_range]
    refine congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) (congrArg₂ g ?_ ?_)
    · rw [mem_range] at hv
      exact congrArg₂ g (fin_congr σ _ _ (by simp; omega)) (fin_congr σ _ _ (by simp; omega))
    · exact fin_congr σ _ _ (by simp; omega)
    · exact fin_congr σ _ _ (by simp)
  have hout : ∏ k : Fin (n' + 1 - wIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) =
      (∏ v ∈ range J.1.val, G v) * g (σ' J.1.val) (σ' J.2.val) *
        (∏ v ∈ Ico J.2.val n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc (sigmaOut σ J) g]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ g ?_ ?_)
    · rw [← prod_range_mul_prod_Ico _ (show J.1.val ≤ n' + 1 - wIn J by omega),
        prod_eq_prod_Ico_succ_bot (show J.1.val < n' + 1 - wIn J by omega), ← mul_assoc]
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) ?_) ?_
      · rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show v ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ (by omega)]; omega
        · simp only [min_eq_left (show v + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ (by omega)]; omega
      · refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ le_rfl]; omega
        · simp only [min_eq_left (show J.1.val + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
      · rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range,
          show n' + 1 - wIn J - (J.1.val + 1) = n' - J.2.val by omega]
        refine prod_congr rfl fun v hv => ?_
        rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val + 1 + v ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
        · simp only [min_eq_left (show J.1.val + 1 + v + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_last, min_self]
      rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_zero, Nat.zero_min]
      rw [hunc _ (Nat.zero_le _)]; omega
  rw [horig, hin, hout, hJ1, hJ2]
  rw [← prod_range_mul_prod_Ico G (show J.1.val ≤ n' by omega),
    ← prod_Ico_consecutive G (show J.1.val ≤ J.2.val by omega) hjn]
  ring

end Leaves

section MoleculeA

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **(3.60)–(3.64) in closed form.**  At an innermost long edge `J` of the layer `π`,
`A(σ, π) = ξ_J (1 - ξ_J) · A(σ_in, ∅) · A(σ_out, π ∖ {J})`. -/
private theorem Alayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) {t : ℝ}
    (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : Flong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Alayer m t σ π = (t * (m (σ J.1) * m (σ J.2))) * (1 - t * (m (σ J.1) * m (σ J.2))) *
      Alayer m t (sigmaIn σ J) ∅ *
        Alayer m t (sigmaOut σ J) ((π.erase J).image (shiftOut J)) := by
  have hJd : IsDiag n J.1 J.2 :=
    (isTSP_of_mem_TSP hF₀).1 J (Flong_subset F₀ σ (hπ ▸ hJπ))
  set g : Bool → Bool → ℂ := fun s s' => (1 - (t : ℂ) * (m s * m s'))⁻¹ with hg
  have hP := prod_leaves_cut hJd σ g
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  have hx : 1 - ξ ≠ 0 := by
    intro h
    have : ‖ξ‖ = 1 := by rw [show ξ = 1 by linear_combination -h, norm_one]
    exact absurd (hm (σ J.1) (σ J.2)) (by rw [this]; exact lt_irrefl 1)
  have hgJ : g (σ J.2) (σ J.1) = (1 - ξ)⁻¹ := by simp only [g, ξ, mul_comm (m (σ J.2))]
  have hgJ' : g (σ J.1) (σ J.2) = (1 - ξ)⁻¹ := rfl
  rw [hgJ, hgJ'] at hP
  unfold Alayer
  rw [Qlayer_cut hn m t σ hF₀ hπ hJπ hinner]
  unfold edgeR
  simp only [g] at hP
  rw [← hξ]
  have hP' : ∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹ =
      (∏ k : Fin (wIn J + 1), (1 - (t : ℂ) * (m (sigmaIn σ J k) * m (sigmaIn σ J (k + 1))))⁻¹) *
        (∏ k : Fin (n - wIn J + 1),
          (1 - (t : ℂ) * (m (sigmaOut σ J k) * m (sigmaOut σ J (k + 1))))⁻¹) * (1 - ξ) ^ 2 := by
    rw [← hP]
    field_simp
  rw [hP']
  field_simp
  ring

end MoleculeA

/-! ## 6. Elementary facts on `m(±)` -/

section Spectral

/-- `‖m(s)‖ = 1` for `|E| ≤ 2`. -/
private theorem SumZeroWard_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖t m(s) m(s')‖ < 1` for `t ∈ [0,1)` and `|E| ≤ 2`. -/
private theorem SumZeroWard_hm {E t : ℝ} (hE : |E| ≤ 2) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ∀ s s' : Bool, ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 := by
  intro s s'
  rw [norm_mul, norm_mul, SumZeroWard_norm_mSig hE, SumZeroWard_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg ht.1, mul_one, mul_one]
  exact ht.2

/-- A long edge has `m(s) m(s') = m m̄ = |m|² = 1`. -/
private theorem SumZeroWard_mSig_mul_of_ne {E : ℝ} (hE : |E| ≤ 2) {s s' : Bool} (h : s ≠ s') :
    mSig E s * mSig E s' = 1 := by
  have h1 : Gauss.spectralM E * (starRingEnd ℂ) (Gauss.spectralM E) = 1 := by
    rw [Complex.mul_conj', Gauss.norm_spectralM hE]; simp
  cases s <;> cases s' <;> simp_all [mSig, mul_comm]

/-- Flipping every charge conjugates `m`: `m(!s) = conj m(s)`. -/
private theorem SumZeroWard_mSig_not (E : ℝ) (s : Bool) :
    mSig E (!s) = (starRingEnd ℂ) (mSig E s) := by
  cases s <;> simp [mSig]

/-- `η_t = (1 - t) Im m`. -/
private theorem SumZeroWard_etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

end Spectral

/-! ## 7. Flipping all charges -/

section Flip

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem SumZeroWard_Flong_not (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) :
    Flong F (fun v => !σ v) = Flong F σ := by
  unfold Flong
  refine filter_congr fun d _ => ?_
  change (!σ d.1) ≠ (!σ d.2) ↔ σ d.1 ≠ σ d.2
  cases σ d.1 <;> cases σ d.2 <;> simp

/-- `A(!σ, π) = conj A(σ, π)` for real `t`. -/
private theorem SumZeroWard_Alayer_not (E t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    Alayer (mSig E) t (fun v => !σ v) π = (starRingEnd ℂ) (Alayer (mSig E) t σ π) := by
  have hT : TSPlong n (fun v => !σ v) π = TSPlong n σ π := by
    unfold TSPlong
    refine filter_congr fun F _ => ?_
    rw [SumZeroWard_Flong_not]
  unfold Alayer Qlayer edgeR
  rw [hT]
  simp only [SumZeroWard_mSig_not, map_mul, map_prod, map_sum, map_inv₀, map_sub, map_one,
    Complex.conj_ofReal]

end Flip

/-! ## 8. The base bound (3.49) from the RBM2D Ward bound `Kcal_sumAll_le` -/

section Bound349

/-- `|Z_3²| = 9`. -/
private theorem SumZeroWard_card_Z2_three : Fintype.card (Z2 3) = 9 := by
  simp [Z2, Fintype.card_prod, ZMod.card]

/-- **(3.49)** for `σ₀ = +`, `σ_{n-1} = -`, in closed form: `|∑_π A(σ, π)| ≤ 2^{n²} c_κ^{-2n}
η_t^{-(n-1)}`.  From `Kcal_sumAll_le` at `L = 3`, `W = 1`, with `Kcal_eq_sum_Kpi`
(3.41) and the closed form `∑_a K^(π) = 9 A(σ, π)` (`sum_Kpi_closed`). -/
private theorem SumZeroWard_norm_sum_Alayer_le_pm {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : |E| ≤ 2 - κ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (h0 : σ ⟨0, by omega⟩ = true) (h1 : σ ⟨n - 1, by omega⟩ = false) :
    ‖∑ π ∈ (diagonals n).powerset, Alayer (mSig E) t σ π‖ ≤
      2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (etaT E t)⁻¹ ^ (n - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hm := SumZeroWard_hm hE2 ht
  have hprod : ‖∏ i, mSig E (σ i)‖ = 1 := by
    rw [norm_prod]; exact prod_eq_one fun i _ => SumZeroWard_norm_mSig hE2 (σ i)
  have hprod0 : ∏ i, mSig E (σ i) ≠ 0 := by
    intro h; rw [h, norm_zero] at hprod; exact zero_ne_one hprod
  -- `∑_π A = 9⁻¹ ∑_a ∑_π K^(π)`
  have e1 : ∑ π ∈ (diagonals n).powerset, Alayer (mSig E) t σ π
      = (9 : ℂ)⁻¹ * ∑ a : Fin n → Z2 3,
          ∑ π ∈ (diagonals n).powerset, Kpi 3 (mSig E) t σ a π := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun π _ => ?_
    rw [sum_Kpi_closed (mSig E) hm (L := 3) (by norm_num)]
    push_cast
    field_simp
    norm_num
  -- `∑_π K^(π) = m_σ⁻¹ K` (3.41), with `W = 1`
  have e2 : ∀ a : Fin n → Z2 3, ∑ π ∈ (diagonals n).powerset, Kpi 3 (mSig E) t σ a π
      = (∏ i, mSig E (σ i))⁻¹ * Kcal 3 1 E t (loopOf 3 σ a) := by
    intro a
    rw [Kcal_eq_sum_Kpi 3 1 E t n hn σ a]
    simp only [Nat.cast_one, one_pow, inv_one, one_mul]
    field_simp
  -- the fibres `a₀ = a₁`
  have e3 : ∑ a : Fin n → Z2 3, Kcal 3 1 E t (loopOf 3 σ a)
      = ∑ a₁ : Z2 3, ∑ a ∈ Finset.univ.filter (fun a : Fin n → Z2 3 => a ⟨0, by omega⟩ = a₁),
          Kcal 3 1 E t (loopOf 3 σ a) :=
    (sum_fiberwise univ (fun a : Fin n → Z2 3 => a ⟨0, by omega⟩) _).symm
  have hB : ∀ a₁ : Z2 3,
      ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Z2 3 => a ⟨0, by omega⟩ = a₁),
          Kcal 3 1 E t (loopOf 3 σ a)‖
        ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (etaT E t)⁻¹ ^ (n - 1) := by
    intro a₁
    have h := Kcal_sumAll_le κ hκ 3 1 (by norm_num) le_rfl E hE t ht n (by omega) σ h0 h1 a₁
    simpa using h
  simp_rw [e2] at e1
  rw [e1, ← mul_sum, e3, norm_mul, norm_mul, norm_inv, norm_inv, hprod, inv_one, one_mul]
  have hsum := (norm_sum_le _ _).trans
    (sum_le_sum fun a₁ (_ : a₁ ∈ (univ : Finset (Z2 3))) => hB a₁)
  rw [sum_const, card_univ, SumZeroWard_card_Z2_three, nsmul_eq_mul] at hsum
  have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
  rw [h9]
  have h9' : (9 : ℝ)⁻¹ * ((9 : ℕ) : ℝ) = 1 := by norm_num
  calc (9 : ℝ)⁻¹ * ‖∑ a₁ : Z2 3,
        ∑ a ∈ Finset.univ.filter (fun a : Fin n → Z2 3 => a ⟨0, by omega⟩ = a₁),
          Kcal 3 1 E t (loopOf 3 σ a)‖
      ≤ (9 : ℝ)⁻¹ * (((9 : ℕ) : ℝ) *
          (2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (etaT E t)⁻¹ ^ (n - 1))) := by
        gcongr
    _ = 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (etaT E t)⁻¹ ^ (n - 1) := by
        rw [← mul_assoc, h9', one_mul]

/-- **(3.49)** for every `σ` with `σ₀ ≠ σ_{n-1}`: the case `σ₀ = -` is the conjugate of the
case `σ₀ = +` (`SumZeroWard_Alayer_not`). -/
private theorem SumZeroWard_norm_sum_Alayer_le {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : |E| ≤ 2 - κ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (hσ : σ ⟨0, by omega⟩ ≠ σ ⟨n - 1, by omega⟩) :
    ‖∑ π ∈ (diagonals n).powerset, Alayer (mSig E) t σ π‖ ≤
      2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (etaT E t)⁻¹ ^ (n - 1) := by
  cases h0 : σ ⟨0, by omega⟩
  · have h1 : σ ⟨n - 1, by omega⟩ = true := by
      rw [h0] at hσ; cases h : σ ⟨n - 1, by omega⟩ <;> simp_all
    set σ' : Fin n → Bool := fun v => !σ v with hσ'
    have hσσ : σ = fun v => !σ' v := by funext v; simp [σ']
    have hsum : ∑ π ∈ (diagonals n).powerset, Alayer (mSig E) t σ π
        = (starRingEnd ℂ) (∑ π ∈ (diagonals n).powerset, Alayer (mSig E) t σ' π) := by
      rw [map_sum]
      refine sum_congr rfl fun π _ => ?_
      rw [hσσ, SumZeroWard_Alayer_not]
    rw [hsum, Complex.norm_conj]
    exact SumZeroWard_norm_sum_Alayer_le_pm hκ hE ht hn σ'
      (by simp only [σ']; rw [h0]; rfl) (by simp only [σ']; rw [h1]; rfl)
  · have h1 : σ ⟨n - 1, by omega⟩ = false := by
      rw [h0] at hσ; cases h : σ ⟨n - 1, by omega⟩ <;> simp_all
    exact SumZeroWard_norm_sum_Alayer_le_pm hκ hE ht hn σ h0 h1

end Bound349

/-! ## 9. The induction (3.50) on the class `σ₀ ≠ σ_{n-1}` -/

section Induction350

variable {E : ℝ}

private theorem SumZeroWard_Alayer_eq_zero_of_empty {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ)
    {σ : Fin n → Bool} {π : Finset (Fin n × Fin n)} (h : TSPlong n σ π = ∅) :
    Alayer m t σ π = 0 := by
  simp [Alayer, Qlayer, h]

/-- The end charges of the inner polygon of the cut at `J = (i, j)` are `σ_i` and `σ_j`. -/
private theorem SumZeroWard_sigmaIn_ends {n : ℕ} [NeZero n] {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) :
    sigmaIn σ J ⟨0, by omega⟩ = σ J.1 ∧
      sigmaIn σ J ⟨wIn J + 1 - 1, by omega⟩ = σ J.2 := by
  have hJ1 := J.1.isLt
  have hJ2 := J.2.isLt
  have h12 := hJd.1
  rw [Fin.lt_def] at h12
  constructor <;> (simp only [sigmaIn]; congr 1; ext; simp only [wIn]; omega)

/-- The end charges of the outer polygon of the cut at `J` are `σ₀` and `σ_{n-1}`. -/
private theorem SumZeroWard_sigmaOut_ends {n : ℕ} [NeZero n] {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) :
    sigmaOut σ J ⟨0, by omega⟩ = σ ⟨0, NeZero.pos n⟩ ∧
      sigmaOut σ J ⟨n - wIn J + 1 - 1, by omega⟩ =
        σ ⟨n - 1, by have := NeZero.pos n; omega⟩ := by
  have hJ2 := J.2.isLt
  have hJw := width_of_isDiag hJd
  have hw : wIn J = J.2.val - J.1.val := rfl
  constructor
  · simp only [sigmaOut]
    congr 1
  · simp only [sigmaOut]
    congr 1
    ext
    change min (unCol J (n - wIn J + 1 - 1)) (n - 1) = n - 1
    rw [unCol_of_gt (J := J) (by omega)]
    omega

/-- **(3.50)**: `|A(σ, π)| ≤ C η_t^{-(n-1)}` for every `σ` with `σ₀ ≠ σ_{n-1}` and every `π`,
in the bulk, by induction on `n`.  For `π ≠ ∅` cut at an
innermost long edge (`Alayer_cut`); for `π = ∅` subtract the other layers from (3.49).  The
class `σ₀ ≠ σ_{n-1}` is closed under the cut (`SumZeroWard_sigmaIn_ends`,
`SumZeroWard_sigmaOut_ends`). -/
private theorem SumZeroWard_norm_Alayer_le {κ : ℝ} (hκ : 0 < κ) (hEk : |E| ≤ 2 - κ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (hn3 : 3 ≤ n), n ≤ N →
      ∀ σ : Fin n → Bool, σ ⟨0, by omega⟩ ≠ σ ⟨n - 1, by omega⟩ →
      ∀ (π : Finset (Fin n × Fin n)) (t : ℝ), t ∈ Set.Ico (0 : ℝ) 1 →
        ‖Alayer (mSig E) t σ π‖ ≤ C * (etaT E t)⁻¹ ^ (n - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set ι := (Gauss.spectralM E).im with hι
  have hι0 : 0 < ι := Gauss.spectralM_im_pos hE
  have hc0 : 0 < gapK κ := by
    unfold gapK
    refine lt_min one_pos (Real.sqrt_pos.2 ?_)
    nlinarith
  induction N with
  | zero => exact ⟨0, le_rfl, fun n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih
  set B : ℝ := 2 ^ ((N + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (N + 1)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨C + B + (2 ^ ((N + 1) * (N + 1)) + 1) * (C * C * ι⁻¹),
    by positivity, fun n _ h3 hN σ hσ π t ht => ?_⟩
  have ht0 := ht.1
  have ht1 := ht.2
  have hη : 0 < etaT E t := by
    rw [SumZeroWard_etaT_eq]; exact mul_pos (by linarith) hι0
  set η := etaT E t with hηdef
  have hη' : η = (1 - t) * ι := SumZeroWard_etaT_eq E t
  have hpow0 : 0 ≤ η⁻¹ ^ (n - 1) := by positivity
  have hCC : 0 ≤ C * C * ι⁻¹ := by positivity
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC n h3 (by omega) σ hσ π t ht).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) + 1) hCC
    linarith
  have hn : n = N + 1 := by omega
  -- the layers with a long edge
  have hne_bound : ∀ π : Finset (Fin n × Fin n), π.Nonempty →
      ‖Alayer (mSig E) t σ π‖ ≤ C * C * ι⁻¹ * η⁻¹ ^ (n - 1) := by
    intro π hπne
    rcases (TSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
    · rw [SumZeroWard_Alayer_eq_zero_of_empty _ _ hemp, norm_zero]; positivity
    obtain ⟨hF₀T, hπ⟩ := mem_filter.1 hF₀
    have hF₀' := isTSP_of_mem_TSP hF₀T
    obtain ⟨J, hJ, hinner⟩ := exists_innermost (hπ ▸ Flong_subset_diagonals hF₀T σ) hπne
    have hm := SumZeroWard_hm hE2 ht
    have hJd : IsDiag n J.1 J.2 := hF₀'.1 J (Flong_subset F₀ σ (hπ ▸ hJ))
    have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJ)).2
    rw [Alayer_cut (by omega) (mSig E) hm σ hF₀T hπ hJ hinner,
      SumZeroWard_mSig_mul_of_ne hE2 hJlong, mul_one]
    have hw := width_of_isDiag hJd
    have hw' : wIn J + 1 < n := by
      obtain ⟨-, -, hnot⟩ := hJd
      have := J.2.isLt
      simp only [wIn]
      omega
    have hwv : wIn J = J.2.val - J.1.val := rfl
    obtain ⟨hi0, hi1⟩ := SumZeroWard_sigmaIn_ends hJd σ
    obtain ⟨ho0, ho1⟩ := SumZeroWard_sigmaOut_ends hJd σ
    have hin := hC (wIn J + 1) (by omega) (by omega) (sigmaIn σ J)
      (by rw [hi0, hi1]; exact hJlong) ∅ t ht
    have hout := hC (n - wIn J + 1) (by omega) (by omega) (sigmaOut σ J)
      (by rw [ho0, ho1]; exact hσ) ((π.erase J).image (shiftOut J)) t ht
    simp only [Nat.add_sub_cancel] at hin hout
    have htn : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht0
    have h1t : ‖(1 : ℂ) - t‖ = 1 - t := by
      rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by linarith)
    rw [norm_mul, norm_mul, norm_mul, htn, h1t]
    have hkey : (1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J)) = ι⁻¹ * η⁻¹ ^ (n - 1) := by
      have h1t0 : 1 - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
      have hι0' : ι ≠ 0 := hι0.ne'
      rw [← pow_add, show wIn J + (n - wIn J) = n - 1 + 1 by omega, pow_succ, hη']
      field_simp
    calc t * (1 - t) * ‖Alayer (mSig E) t (sigmaIn σ J) ∅‖ *
          ‖Alayer (mSig E) t (sigmaOut σ J) ((π.erase J).image (shiftOut J))‖
        ≤ (1 - t) * (C * η⁻¹ ^ wIn J) * (C * η⁻¹ ^ (n - wIn J)) := by
          gcongr
          all_goals nlinarith
        _ = C * C * ((1 - t) * (η⁻¹ ^ wIn J * η⁻¹ ^ (n - wIn J))) := by ring
        _ = C * C * ι⁻¹ * η⁻¹ ^ (n - 1) := by rw [hkey]; ring
  rcases π.eq_empty_or_nonempty with rfl | hπne
  · -- the layer without long edges: (3.49) minus the others
    have hsum := SumZeroWard_norm_sum_Alayer_le hκ hEk ht h3 σ hσ
    have hmem : (∅ : Finset (Fin n × Fin n)) ∈ (diagonals n).powerset := empty_mem_powerset _
    rw [← add_sum_erase _ _ hmem] at hsum
    have hrest : ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSig E) t σ π‖
        ≤ 2 ^ ((N + 1) * (N + 1)) * (C * C * ι⁻¹ * η⁻¹ ^ (n - 1)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (sum_le_sum fun π hπ => hne_bound π
        (nonempty_iff_ne_empty.2 (mem_erase.1 hπ).1)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      gcongr
      have hc : ((diagonals n).powerset.erase ∅).card ≤ 2 ^ (n * n) := by
        refine (card_erase_le).trans ?_
        rw [card_powerset]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have := card_le_univ (diagonals n)
        simpa using this
      rw [← hn]
      exact_mod_cast hc
    have htri : ‖Alayer (mSig E) t σ ∅‖ ≤
        ‖Alayer (mSig E) t σ ∅ +
            ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSig E) t σ π‖ +
          ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSig E) t σ π‖ := by
      have := norm_sub_le (Alayer (mSig E) t σ ∅ +
        ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSig E) t σ π)
        (∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSig E) t σ π)
      rwa [add_sub_cancel_right] at this
    have hBn : 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) = B := by rw [hn]
    rw [hBn] at hsum
    calc ‖Alayer (mSig E) t σ ∅‖
        ≤ B * η⁻¹ ^ (n - 1) +
            2 ^ ((N + 1) * (N + 1)) * (C * C * ι⁻¹ * η⁻¹ ^ (n - 1)) := by
          linarith
      _ ≤ _ := by
          have h2 : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) := by positivity
          nlinarith [mul_nonneg hC0 hpow0, mul_nonneg hCC hpow0]
  · refine (hne_bound π hπne).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1))) hCC
    linarith

end Induction350

/-! ## 10. The Lipschitz step `t → 1` (the estimates of `RBM2D/Loop/SumZero.lean`, section
`Estimates`, which are private there) -/

section Lipschitz

private theorem SumZeroWard_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem SumZeroWard_gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem SumZeroWard_gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ gapK κ := (SumZeroWard_gapK_pos hκ hκ2).le
  have h1 : gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem SumZeroWard_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
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

/-- **The bulk gap**: `c_κ ≤ |1 - t m(s)²|` for `t ≥ 0` and `|E| ≤ 2 - κ`. -/
private theorem SumZeroWard_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) (s : Bool) :
    gapK κ ≤ ‖1 - (t : ℂ) * (mSig E s * mSig E s)‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 := by
    rw [SumZeroWard_norm_one_sub_sq hE2]
    have hg1 : gapK κ ^ 2 ≤ 1 := by
      have := SumZeroWard_gapK_le_one κ
      have := (SumZeroWard_gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := SumZeroWard_gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have hle : gapK κ ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ := by
    have := (SumZeroWard_gapK_pos hκ hκ2).le
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
private theorem SumZeroWard_norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
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

/-- The Lipschitz bound `|f(t) - f(1)| ≤ (1 - t) c⁻²`. -/
private theorem SumZeroWard_norm_edge_sub_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) (hc1 : c ≤ ‖1 - μ‖) :
    ‖((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1)‖ ≤ (1 - t) * c⁻¹ ^ 2 := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have hne1 : (1 : ℂ) - μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc1; linarith
  have h : ((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1) =
      (((t - 1 : ℝ) : ℂ) * μ) * ((1 - (t : ℂ) * μ)⁻¹ * (1 - μ)⁻¹) := by
    field_simp
    push_cast
    ring
  rw [h, norm_mul, norm_mul, norm_mul, hμ, Complex.norm_real, norm_inv, norm_inv, mul_one,
    Real.norm_of_nonpos (by linarith), neg_sub]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hinv1 : ‖1 - μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hc1
  have h01 : 0 ≤ ‖1 - μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hprod : ‖1 - (t : ℂ) * μ‖⁻¹ * ‖1 - μ‖⁻¹ ≤ c⁻¹ ^ 2 := by
    rw [sq]; exact mul_le_mul hinv hinv1 h01 (inv_nonneg.2 hc.le)
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- Telescoping bound for finite products:
`‖∏ a - ∏ b‖ ≤ |s| M^{|s|} δ` if `‖a_i‖, ‖b_i‖ ≤ M`, `‖a_i - b_i‖ ≤ δ`, `M ≥ 1`. -/
private theorem SumZeroWard_norm_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℂ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ M) (hb : ∀ i ∈ s, ‖b i‖ ≤ M) (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ δ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ s.card * M ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ M := fun i hi => ha i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ M := fun i hi => hb i (mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, ‖a i - b i‖ ≤ δ := fun i hi => hab i (mem_insert_of_mem hi)
    have hI := ih ha' hb' hab'
    have hax := ha x (mem_insert_self x s)
    have habx := hab x (mem_insert_self x s)
    have hQ : ‖∏ i ∈ s, b i‖ ≤ M ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, M :=
            prod_le_prod₀ (fun i _ => norm_nonneg _) hb'
        _ = M ^ s.card := prod_const M
    rw [prod_insert hx, prod_insert hx, card_insert_of_notMem hx]
    have hsplit : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    have hMk : M ^ s.card ≤ M ^ s.card * M := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hM (Nat.le_succ _)
    have hM0 : 0 ≤ M := by linarith
    have hMk0 : 0 ≤ M ^ s.card := pow_nonneg hM0 _
    have hk0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    calc ‖a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i‖
        ≤ ‖a x‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ + ‖a x - b x‖ * ‖∏ i ∈ s, b i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M * (s.card * M ^ s.card * δ) + δ * M ^ s.card := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * M ^ (s.card + 1) * δ := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left hMk hδ]

/-- **The Lipschitz step**: `‖Q(σ, ∅)(t) - Q(σ, ∅)(1)‖ ≤ 2^{n²} n² c_κ^{-(n²+2)} (1 - t)` on
`[0, 1)`, in the bulk (every edge of a tree of the layer `∅` joins equal charges, so its factor
is `(1 - t m(s)²)⁻¹ - 1`, with `|1 - t m(s)²| ≥ c_κ` on `[0, 1]`). -/
private theorem SumZeroWard_norm_Qlayer_sub_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} (σ : Fin n → Bool) :
    ‖Qlayer (mSig E) t σ ∅ - Qlayer (mSig E) 1 σ ∅‖ ≤
      2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * (gapK κ)⁻¹ ^ (n ^ 2) * (gapK κ)⁻¹ ^ 2) * (1 - t) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := SumZeroWard_gapK_pos hκ hκ2
  set c := gapK κ with hcdef
  have hc1 : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 (SumZeroWard_gapK_le_one κ)
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hμ : ∀ s : Bool, ‖mSig E s * mSig E s‖ = 1 := fun s => by
    rw [norm_mul, SumZeroWard_norm_mSig hE2]; norm_num
  -- one tree
  have hF : ∀ F ∈ TSPlong n σ ∅,
      ‖∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSig E) 1 (σ e.1) (σ e.2)‖
        ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by
    intro F hFm
    obtain ⟨-, hFl⟩ := mem_filter.1 hFm
    have hsame : ∀ e ∈ F, σ e.2 = σ e.1 := by
      intro e he
      by_contra h
      have : e ∈ Flong F σ := mem_filter.2 ⟨he, Ne.symm h⟩
      rw [hFl] at this
      exact notMem_empty e this
    have htel := SumZeroWard_norm_prod_sub_prod_le F
      (fun e => edgeR (mSig E) t (σ e.1) (σ e.2))
      (fun e => edgeR (mSig E) 1 (σ e.1) (σ e.2)) hc1
      (by positivity : 0 ≤ (1 - t) * c⁻¹ ^ 2)
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact SumZeroWard_norm_edge_le (hμ _) ht.1 ht.2.le hc
          (SumZeroWard_gapK_le_norm hκ hE ht.1 _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact SumZeroWard_norm_edge_le (hμ _) zero_le_one le_rfl hc
          (SumZeroWard_gapK_le_norm hκ hE zero_le_one _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        have h1 := SumZeroWard_gapK_le_norm hκ hE zero_le_one (σ e.1)
        rw [Complex.ofReal_one, one_mul] at h1 ⊢
        exact SumZeroWard_norm_edge_sub_le (hμ _) ht.2.le hc
          (SumZeroWard_gapK_le_norm hκ hE ht.1 _) h1)
    refine htel.trans ?_
    have hkn' : F.card ≤ n ^ 2 := by
      have := card_le_univ F
      simpa [sq] using this
    have hkn : (F.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hkn'
    have hpow : c⁻¹ ^ F.card ≤ c⁻¹ ^ (n ^ 2) := pow_le_pow_right₀ hc1 hkn'
    calc (F.card : ℝ) * c⁻¹ ^ F.card * ((1 - t) * c⁻¹ ^ 2)
        = (F.card : ℝ) * c⁻¹ ^ F.card * c⁻¹ ^ 2 * (1 - t) := by ring
      _ ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by gcongr
  have hdiff : Qlayer (mSig E) t σ ∅ - Qlayer (mSig E) 1 σ ∅ = ∑ F ∈ TSPlong n σ ∅,
      (∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2) -
        ∏ e ∈ F, edgeR (mSig E) 1 (σ e.1) (σ e.2)) := by
    rw [sum_sub_distrib]
    rfl
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum hF).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((TSPlong n σ ∅).card : ℝ) ≤ 2 ^ (n ^ 2) := by
    have h : (TSPlong n σ ∅).card ≤ 2 ^ (n ^ 2) := by
      calc (TSPlong n σ ∅).card ≤ (TSP n).card := card_filter_le _ _
        _ ≤ (diagonals n).powerset.card := card_filter_le _ _
        _ = 2 ^ (diagonals n).card := card_powerset _
        _ ≤ 2 ^ (n ^ 2) := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
              _ = n ^ 2 := by simp [sq]
    exact_mod_cast h
  have h0 : 0 ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by positivity
  calc ((TSPlong n σ ∅).card : ℝ) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t))
      ≤ 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t)) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ = 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2) * (1 - t) := by ring

end Lipschitz

/-! ## 11. The identity `R_n(1) = 0` -/

section Target1

/-- `σ^{(alt)}` has `σ₀ = +` and, for even `n`, `σ_{n-1} = -`. -/
private theorem SumZeroWard_sigAlt_ends {n : ℕ} (hn : 2 ≤ n) (hev : Even n) :
    sigAlt n ⟨0, by omega⟩ = true ∧ sigAlt n ⟨n - 1, by omega⟩ = false := by
  obtain ⟨k, hk⟩ := hev
  have h : (n - 1) % 2 = 1 := by omega
  simp [sigAlt, h]

/-- For even `n`, `σ^{(alt)}` alternates cyclically: `σ_v ≠ σ_{v+1}` for every `v : Fin n`. -/
private theorem SumZeroWard_sigAlt_alt {n : ℕ} [NeZero n] (hev : Even n) (v : Fin n) :
    sigAlt n v ≠ sigAlt n (v + 1) := by
  obtain ⟨k, hk⟩ := hev
  have hv := v.isLt
  have hval : (v + 1 : Fin n).val = (v.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [sigAlt, hval]
  by_cases h : v.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    rcases Nat.mod_two_eq_zero_or_one v.val with h2 | h2
    · have h3 : (v.val + 1) % 2 = 1 := by omega
      simp [h2, h3]
    · have h3 : (v.val + 1) % 2 = 0 := by omega
      simp [h2, h3]
  · rw [show v.val + 1 = n by omega, Nat.mod_self]
    have h2 : v.val % 2 = 1 := by omega
    simp [h2]

/-- **`[YY_25]` Lemma 3.10 (2) in closed form (`R_n(1) = 0`)**: for every even `n ≥ 4`
and every `|E| < 2`, the single-molecule layer of the alternating loop vanishes at `t = 1`:
`Q(σ^{(alt)}, ∅)|_{t=1} = ∑_{F ∈ T_SP(σ^{(alt)}, ∅)} ∏_{e ∈ F} ((1 - m_e²)⁻¹ - 1) = 0`.
Proof: (3.51) `Q(t) = (1 - t)^n A(σ^{(alt)}, ∅)(t)`, (3.50) `|A| ≤ C η_t^{-(n-1)}`, so
`|Q(t)| ≤ C (Im m)^{-(n-1)} (1 - t)`; with the Lipschitz step, `|Q(1)| ≤ K (1 - t)` for all
`t ∈ [0, 1)`. -/
theorem Qlayer_alt_one_eq_zero :
    ∀ E : ℝ, |E| < 2 → ∀ (n : ℕ) [NeZero n], 4 ≤ n → Even n →
      Qlayer (mSig E) 1 (sigAlt n) ∅ = 0 := by
  intro E hE n _ hn hev
  set κ : ℝ := 2 - |E| with hκdef
  have hκ : 0 < κ := by linarith
  have hEk : |E| ≤ 2 - κ := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set ι := (Gauss.spectralM E).im with hι
  have hι0 : 0 < ι := Gauss.spectralM_im_pos hE
  obtain ⟨C, hC0, hC⟩ := SumZeroWard_norm_Alayer_le hκ hEk n
  obtain ⟨he0, he1⟩ := SumZeroWard_sigAlt_ends (by omega : 2 ≤ n) hev
  have hends : sigAlt n ⟨0, by omega⟩ ≠ sigAlt n ⟨n - 1, by omega⟩ := by
    rw [he0, he1]; decide
  -- (3.51) and (3.50): `|Q(t)| ≤ C ι^{-(n-1)} (1 - t)`
  have hQt : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖Qlayer (mSig E) t (sigAlt n) ∅‖ ≤ C * ι⁻¹ ^ (n - 1) * (1 - t) := by
    intro t ht
    have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
    have hξ : ∀ v : Fin n, (1 : ℂ) - t * (mSig E (sigAlt n v) * mSig E (sigAlt n (v + 1)))
        = ((1 - t : ℝ) : ℂ) := by
      intro v
      rw [SumZeroWard_mSig_mul_of_ne hE2 (SumZeroWard_sigAlt_alt hev v)]
      push_cast; ring
    have hQ : Qlayer (mSig E) t (sigAlt n) ∅ =
        ((1 - t : ℝ) : ℂ) ^ n * Alayer (mSig E) t (sigAlt n) ∅ := by
      unfold Alayer
      simp_rw [hξ]
      rw [prod_const, card_univ, Fintype.card_fin, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ (by exact_mod_cast h1t.ne'), one_pow, one_mul]
    have hA := hC n (by omega) le_rfl (sigAlt n) hends ∅ t ht
    rw [hQ, norm_mul, norm_pow, Complex.norm_of_nonneg h1t.le]
    have hη : etaT E t = (1 - t) * ι := SumZeroWard_etaT_eq E t
    rw [hη] at hA
    calc (1 - t) ^ n * ‖Alayer (mSig E) t (sigAlt n) ∅‖
        ≤ (1 - t) ^ n * (C * ((1 - t) * ι)⁻¹ ^ (n - 1)) := by gcongr
      _ = C * ι⁻¹ ^ (n - 1) * (1 - t) := by
          obtain ⟨p, hp⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
          rw [hp, Nat.add_sub_cancel, mul_inv, mul_pow, inv_pow, pow_succ]
          have h1 : (1 - t) ^ p ≠ 0 := pow_ne_zero _ h1t.ne'
          field_simp
  -- the limit `t → 1`
  set K : ℝ := 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * (gapK κ)⁻¹ ^ (n ^ 2) * (gapK κ)⁻¹ ^ 2)
    with hKdef
  set M : ℝ := C * ι⁻¹ ^ (n - 1) + K with hMdef
  have hK0 : 0 ≤ K := by
    have := SumZeroWard_gapK_pos hκ (by linarith [abs_nonneg E])
    positivity
  have hM0 : 0 ≤ M := by positivity
  have hQ1 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Qlayer (mSig E) 1 (sigAlt n) ∅‖ ≤ M * (1 - t) := by
    intro t ht
    have h1 := hQt t ht
    have h2 := SumZeroWard_norm_Qlayer_sub_le hκ hEk ht (sigAlt n)
    have h3 := norm_sub_le (Qlayer (mSig E) t (sigAlt n) ∅)
      (Qlayer (mSig E) t (sigAlt n) ∅ - Qlayer (mSig E) 1 (sigAlt n) ∅)
    rw [sub_sub_cancel] at h3
    calc ‖Qlayer (mSig E) 1 (sigAlt n) ∅‖
        ≤ C * ι⁻¹ ^ (n - 1) * (1 - t) + K * (1 - t) := by linarith
      _ = M * (1 - t) := by ring
  by_contra hne
  have hx : 0 < ‖Qlayer (mSig E) 1 (sigAlt n) ∅‖ := norm_pos_iff.2 hne
  set x := ‖Qlayer (mSig E) 1 (sigAlt n) ∅‖ with hxdef
  set δ : ℝ := min 1 (x / (2 * (M + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδx : δ ≤ x / (2 * (M + 1)) := min_le_right _ _
  have h := hQ1 (1 - δ) ⟨by linarith, by linarith⟩
  rw [sub_sub_cancel] at h
  have hMδ : M * δ ≤ M * (x / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hδx hM0
  have hlt : M * (x / (2 * (M + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end Target1

/-! ## 12. The bound `SigmaPi_alt_sumZero_le` -/

/-- **The sum-zero property `(SZjadljsk)`**: the bound
`SigmaPi_alt_sumZero_le_of_Qlayer_one` with its hypothesis discharged by
`Qlayer_alt_one_eq_zero`. -/
theorem SigmaPi_alt_sumZero_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Z2 L,
      ‖∑ d ∈ Finset.univ.filter (fun d : Fin n → Z2 L => d ⟨0, by omega⟩ = d₁),
          SigmaPi L (mSig E) t (sigAlt n) ∅ d‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
  intro κ hκ L _ hL E hE t ht n _ hn hev d₁
  have hE2 : |E| < 2 := by linarith
  exact SigmaPi_alt_sumZero_le_of_Qlayer_one κ hκ L hL E hE t ht n hn hev
    (Qlayer_alt_one_eq_zero E hE2 n hn hev) d₁

end RBM.KLoop
