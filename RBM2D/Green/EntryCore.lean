/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.Minor

/-!
# Entry estimates for the Green's function: the dimension-free core

The dimension-free core of Lemma 4.1 of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices* [YY_25] (Lemma 4.2 in the numbering
of the 2D paper, arXiv:2503.07606).  The 2D paper does not restate this lemma: it says
"the proof of these estimates follows that of Lemma 4.2 in [YY_25], which is
dimension-independent" (Section "Estimates for entries of `G`").

Everything here is a finite algebraic statement over an arbitrary finite index type `n` with
`[Fintype n] [DecidableEq n]` and an arbitrary variance profile `S : n → n → ℝ`; no lattice,
block, bandwidth or dimension appears.  The probabilistic inputs (the large deviation bound)
enter as the explicit `Prop`s `LDERow`, `LDECol`, `LDEQuad` with a factor `Φ` in place of `≺`.

* `greenMinor`: the right-hand side of (4.9) on the full index set, related to
  `RBM.Green.minorGreen` (subtype index set) by `minorGreen_eq_greenMinor`.
* `GoodEvent`: the event `‖G - m‖_max ≤ δ` of (4.1), and its consequences.
* `LDERow`, `LDECol`, `LDEQuad` and the `lde*LHS`/`lde*RHS` definitions.
* `absorb_le`, `sum_mul_sq_le_of_le_add`: the absorption and weighted-square steps.
* `norm_sq_green_le_row`, `norm_sq_green_le_col`: (4.10) and its column form.
* `norm_sq_green_le_two_sided`, `norm_sq_green_offdiag_le`: (4.11).
* `ldeQuadRHS_le`, `norm_sq_selfEnergy_err_le`: the self-consistent equation from (4.7).
* `Stable`, `norm_sq_green_diag_sub_le`: (4.3).
* `norm_condExp_le`, `norm_sum_coef_green_sub_le`: the algebra behind (4.5).

The block specialization (`Sblk`, the `_blk` forms) and the `≺` layer depend on the dimension and
are in other files.
-/

namespace RBM.Green

open Matrix Finset

section Core

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries `G^(i)_{kl}` of the Green's function of the minor, written through the
right-hand side of (4.9) on the full index set.  For `k, l ≠ i` this is
`minorGreen G i k l`. -/
noncomputable def greenMinor (G : Matrix n n ℂ) (i k l : n) : ℂ :=
  G k l - G k i * G i l / G i i

omit [Fintype n] [DecidableEq n] in
theorem minorGreen_eq_greenMinor (G : Matrix n n ℂ) (i : n) (k l : {a : n // a ≠ i}) :
    minorGreen G i k l = greenMinor G i k.1 l.1 := rfl

omit [Fintype n] [DecidableEq n] in
theorem greenMinor_sub (G : Matrix n n ℂ) (i k l : n) :
    greenMinor G i k l - G k l = -(G k i * G i l / G i i) := by
  rw [greenMinor]; ring

variable {M G : Matrix n n ℂ}

/-- Row identity from `M G = 1`, with the `i`-th term removed. -/
private theorem sum_erase_mul_green (hMG : M * G = 1) (i a b : n) :
    ∑ k ∈ univ.erase i, M a k * G k b = (if a = b then (1 : ℂ) else 0) - M a i * G i b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hMG
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- Column identity from `G M = 1`, with the `j`-th term removed. -/
private theorem sum_erase_green_mul (hGM : G * M = 1) (j a b : n) :
    ∑ l ∈ univ.erase j, G a l * M l b = (if a = b then (1 : ℂ) else 0) - G a j * M j b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hGM
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- The row sum in **(4.8)**, on the full index set. -/
private theorem sum_erase_mul_greenMinor (hMG : M * G = 1) {i j : n}
    (hGii : G i i ≠ 0) (hij : i ≠ j) :
    ∑ k ∈ univ.erase i, M i k * greenMinor G i k j = -(G i j / G i i) := by
  have hsplit : ∑ k ∈ univ.erase i, M i k * greenMinor G i k j
      = (∑ k ∈ univ.erase i, M i k * G k j)
        - (G i j / G i i) * ∑ k ∈ univ.erase i, M i k * G k i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_mul_green hMG, sum_erase_mul_green hMG, ite_eq_right hij, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8)** on the full index set (with our sign):
`G_{ij} = -G_{ii} ∑_{k ≠ i} M_{ik} G^(i)_{kj}`. -/
private theorem green_eq_neg_mul_sum_row (hMG : M * G = 1) {i j : n}
    (hGii : G i i ≠ 0) (hij : i ≠ j) :
    G i j = -G i i * ∑ k ∈ univ.erase i, M i k * greenMinor G i k j := by
  rw [sum_erase_mul_greenMinor hMG hGii hij]
  field_simp

/-- The column analogue of the sum in (4.8). -/
private theorem sum_erase_greenMinor_mul (hGM : G * M = 1) {k j : n}
    (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * M l j = -(G k j / G j j) := by
  have hsplit : ∑ l ∈ univ.erase j, greenMinor G j k l * M l j
      = (∑ l ∈ univ.erase j, G k l * M l j)
        - (G k j / G j j) * ∑ l ∈ univ.erase j, G j l * M l j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_green_mul hGM, sum_erase_green_mul hGM, ite_eq_right hkj, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8), column form**: `G_{kj} = -G_{jj} ∑_{l ≠ j} G^(j)_{kl} M_{lj}`. -/
private theorem green_eq_neg_mul_sum_col (hGM : G * M = 1) {k j : n}
    (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    G k j = -G j j * ∑ l ∈ univ.erase j, greenMinor G j k l * M l j := by
  rw [sum_erase_greenMinor_mul hGM hGjj hkj]
  field_simp

/-- **(4.7)** on the full index set:
`G_{ii}⁻¹ = M_{ii} - ∑_{k, l ≠ i} M_{ik} G^(i)_{kl} M_{li}`. -/
private theorem inv_green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) {i : n} (hGii : G i i ≠ 0) :
    (G i i)⁻¹ = M i i - ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
      M i k * greenMinor G i k l * M l i := by
  have hinner : ∀ k ∈ univ.erase i, ∑ l ∈ univ.erase i, M i k * greenMinor G i k l * M l i
      = M i k * -(G k i / G i i) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [← sum_erase_greenMinor_mul hGM hGii hki, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl hinner]
  have hcol : ∑ k ∈ univ.erase i, M i k * G k i = 1 - M i i * G i i := by
    rw [sum_erase_mul_green hMG, ite_eq_left rfl]
  have houter : ∑ k ∈ univ.erase i, M i k * -(G k i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [houter]
  field_simp
  ring

/-- Off-diagonal entries of `H - z` are those of `H`: the row sum in (4.8). -/
private theorem sum_erase_sub_smul_row (H G : Matrix n n ℂ) (z : ℂ) (i j : n) :
    ∑ k ∈ univ.erase i, (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k j
      = ∑ k ∈ univ.erase i, H i k * greenMinor G i k j := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm]

/-- Off-diagonal entries of `H - z` are those of `H`: the column sum in (4.8). -/
private theorem sum_erase_sub_smul_col (H G : Matrix n n ℂ) (z : ℂ) (k j : n) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * (H - z • (1 : Matrix n n ℂ)) l j
      = ∑ l ∈ univ.erase j, greenMinor G j k l * H l j := by
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

/-- Off-diagonal entries of `H - z` are those of `H`: the quadratic form in (4.7). -/
private theorem sum_erase_sub_smul_quad (H G : Matrix n n ℂ) (z : ℂ) (i : n) :
    ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
        (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k l * (H - z • (1 : Matrix n n ℂ)) l i
      = ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i := by
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm,
    sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

end Core

section Event

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The event `Ω(t,c)` of (4.1), for one fixed matrix: `‖G - m‖_max ≤ δ`.  The paper takes
`δ = W^{-c}`. -/
def GoodEvent (G : Matrix n n ℂ) (m : ℂ) (δ : ℝ) : Prop :=
  ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ

variable {G : Matrix n n ℂ} {m : ℂ} {δ : ℝ}

omit [Fintype n] in
theorem GoodEvent.norm_offdiag_le (h : GoodEvent G m δ) {x y : n} (hxy : x ≠ y) :
    ‖G x y‖ ≤ δ := by
  simpa [hxy] using h x y

omit [Fintype n] in
theorem GoodEvent.norm_diag_sub_le (h : GoodEvent G m δ) (x : n) : ‖G x x - m‖ ≤ δ := by
  simpa using h x x

omit [Fintype n] in
theorem GoodEvent.norm_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    ‖G x x‖ ≤ 1 + δ := by
  calc ‖G x x‖ = ‖m + (G x x - m)‖ := by rw [add_sub_cancel]
    _ ≤ ‖m‖ + ‖G x x - m‖ := norm_add_le _ _
    _ ≤ 1 + δ := by rw [hm]; linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.one_sub_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    1 - δ ≤ ‖G x x‖ := by
  have h1 : ‖m‖ ≤ ‖G x x‖ + ‖m - G x x‖ := by
    calc ‖m‖ = ‖G x x + (m - G x x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G x x‖ + ‖m - G x x‖ := norm_add_le _ _
  rw [norm_sub_rev, hm] at h1
  linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.half_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : 1 / 2 ≤ ‖G x x‖ := by
  linarith [h.one_sub_le_norm_diag hm x]

omit [Fintype n] in
theorem GoodEvent.diag_ne_zero (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : G x x ≠ 0 := by
  intro h0
  have := h.half_le_norm_diag hm hδ x
  rw [h0, norm_zero] at this
  norm_num at this

omit [Fintype n] in
theorem GoodEvent.norm_sq_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : ‖G x x‖ ^ 2 ≤ 9 / 4 := by
  have h1 := h.norm_diag_le hm x
  have h0 := norm_nonneg (G x x)
  nlinarith

omit [Fintype n] in
/-- On the event, removing the `(i)` superscript costs `2 |G_{ki}| |G_{il}|`: this is (4.9). -/
theorem GoodEvent.norm_greenMinor_sub_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1)
    (hδ : δ ≤ 1 / 2) (i k l : n) :
    ‖greenMinor G i k l - G k l‖ ≤ 2 * (‖G k i‖ * ‖G i l‖) := by
  rw [greenMinor_sub, norm_neg, norm_div, norm_mul]
  have h1 := h.half_le_norm_diag hm hδ i
  rw [div_le_iff₀ (by linarith)]
  have h2 : 0 ≤ ‖G k i‖ * ‖G i l‖ := by positivity
  nlinarith

end Event

section Absorb

/-- The absorption step at the end of (4.10). -/
theorem absorb_le {x Y Φ δ : ℝ} (hx : 0 ≤ x) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (h : x ≤ 9 / 4 * (Φ * (2 * Y + 8 * δ ^ 2 * x))) : x ≤ 9 * Φ * Y := by
  have h1 : 36 * Φ * δ ^ 2 * x ≤ x := by nlinarith
  nlinarith

variable {n : Type*} [Fintype n]

/-- A weighted sum of squares of perturbed quantities. -/
theorem sum_mul_sq_le_of_le_add (s : Finset n) {w a b : n → ℝ} {ε : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k ≤ 1) (ha : ∀ k, 0 ≤ a k) (hab : ∀ k ∈ s, a k ≤ b k + ε) :
    ∑ k ∈ s, w k * a k ^ 2 ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
  have hpt : ∀ k ∈ s, w k * a k ^ 2 ≤ w k * (2 * b k ^ 2 + 2 * ε ^ 2) := by
    intro k hk
    have h1 := hab k hk
    have h2 : a k ^ 2 ≤ 2 * b k ^ 2 + 2 * ε ^ 2 := by nlinarith [ha k, sq_nonneg (b k - ε)]
    exact mul_le_mul_of_nonneg_left h2 (hw k)
  calc ∑ k ∈ s, w k * a k ^ 2 ≤ ∑ k ∈ s, w k * (2 * b k ^ 2 + 2 * ε ^ 2) := sum_le_sum hpt
    _ ≤ ∑ k, w k * (2 * b k ^ 2 + 2 * ε ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          fun k _ _ => mul_nonneg (hw k) (by positivity)
    _ = 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 * ∑ k, w k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
        have : 2 * ε ^ 2 * ∑ k, w k ≤ 2 * ε ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hw1 (by positivity)
        linarith

end Absorb

section EntryBound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The large deviation input

We do not formalize the large deviation bound; we take its *conclusion*, for the vectors
where the paper applies it, as a hypothesis with an explicit factor `Φ` (in the stochastic
domination layer `Φ = N^τ`).  All three are stated for squared moduli, i.e.
`|∑ H X|² ≤ Φ ∑ S |X|²` is the paper's `|∑ H X| ≺ (∑ S |X|²)^{1/2}`. -/

/-- Left-hand side of the LDE for the row sum in (4.8): `|∑_{k≠i} H_{ik} G^(i)_{kj}|²`. -/
noncomputable def ldeRowLHS (H G : Matrix n n ℂ) (i j : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, H i k * greenMinor G i k j‖ ^ 2

/-- Right-hand side of the LDE for the row sum in (4.8): `∑_{k≠i} S_{ik} |G^(i)_{kj}|²`. -/
noncomputable def ldeRowRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) : ℝ :=
  ∑ k ∈ univ.erase i, S i k * ‖greenMinor G i k j‖ ^ 2

/-- Left-hand side of the LDE for the column sum: `|∑_{l≠j} G^(j)_{kl} H_{lj}|²`. -/
noncomputable def ldeColLHS (H G : Matrix n n ℂ) (k j : n) : ℝ :=
  ‖∑ l ∈ univ.erase j, greenMinor G j k l * H l j‖ ^ 2

/-- Right-hand side of the LDE for the column sum: `∑_{l≠j} |G^(j)_{kl}|² S_{lj}`. -/
noncomputable def ldeColRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (k j : n) : ℝ :=
  ∑ l ∈ univ.erase j, ‖greenMinor G j k l‖ ^ 2 * S l j

/-- Left-hand side of the LDE for the quadratic form in (4.7):
`|∑_{k,l≠i} H_{ik} G^(i)_{kl} H_{li} - t ∑_{k≠i} S_{ik} G^(i)_{kk}|²`. -/
noncomputable def ldeQuadLHS (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ) (i : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i
    - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k‖ ^ 2

/-- Right-hand side of the LDE for the quadratic form in (4.7):
`∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li}`. -/
noncomputable def ldeQuadRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) : ℝ :=
  ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i

/-- The row LDE, with factor `Φ`, for all `i ≠ j`. -/
def LDERow (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ldeRowLHS H G i j ≤ Φ * ldeRowRHS S G i j

/-- The column LDE, with factor `Φ`, for all `k ≠ j`. -/
def LDECol (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ k j, k ≠ j → ldeColLHS H G k j ≤ Φ * ldeColRHS S G k j

/-- The quadratic LDE, with factor `Φ`, for all `i`. -/
def LDEQuad (H G : Matrix n n ℂ) (S : n → n → ℝ) (t Φ : ℝ) : Prop :=
  ∀ i, ldeQuadLHS H G S t i ≤ Φ * ldeQuadRHS S G i

variable {H G : Matrix n n ℂ} {z m : ℂ} {δ Φ : ℝ} {S : n → n → ℝ}

/-- **(4.10)**: on the event `Ω`, `|G_{ij}|² ≤ 9 Φ ∑_k S_{ik} |G_{kj}|²` for `i ≠ j`. -/
theorem norm_sq_green_le_row (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDERow H G S Φ) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := by
  have hGii := hΩ.diag_ne_zero hm hδ i
  have h48 := green_eq_neg_mul_sum_row hMG hGii hij
  rw [sum_erase_sub_smul_row] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := by
    rw [hnorm, ldeRowLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ i) (sq_nonneg _)
  have hrhs : ldeRowRHS S G i j ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2 := by
    refine sum_mul_sq_le_of_le_add _ (hS0 i) (hS1 i) (fun _ => norm_nonneg _) ?_
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k j
    have h2 := hΩ.norm_offdiag_le hki
    have h3 : ‖greenMinor G i k j‖ ≤ ‖G k j‖ + ‖greenMinor G i k j - G k j‖ := by
      calc ‖greenMinor G i k j‖ = ‖G k j + (greenMinor G i k j - G k j)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i j‖ ≤ δ * ‖G i j‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  have hlde := hLDE i j hij
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := hsq
    _ ≤ 9 / 4 * (Φ * ldeRowRHS S G i j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 8 * δ ^ 2 * ‖G i j‖ ^ 2)) := by ring

/-- **(4.10), column form**: on the event `Ω`, `|G_{kj}|² ≤ 9 Φ ∑_l |G_{kl}|² S_{lj}` for
`k ≠ j`.  The paper uses this (the same estimate, expanded along the column) in the
iteration leading to (4.11). -/
theorem norm_sq_green_le_col (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ j, ∑ l, S l j ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDECol H G S Φ) {k j : n} (hkj : k ≠ j) :
    ‖G k j‖ ^ 2 ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 := by
  have hGjj := hΩ.diag_ne_zero hm hδ j
  have h48 := green_eq_neg_mul_sum_col hGM hGjj hkj
  rw [sum_erase_sub_smul_col] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := by
    rw [hnorm, ldeColLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ j) (sq_nonneg _)
  have hrhs : ldeColRHS S G k j ≤ 2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2 := by
    have hre : ldeColRHS S G k j = ∑ l ∈ univ.erase j, S l j * ‖greenMinor G j k l‖ ^ 2 := by
      rw [ldeColRHS]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hre]
    refine sum_mul_sq_le_of_le_add _ (fun l => hS0 l j) (hS1 j) (fun _ => norm_nonneg _) ?_
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ j k l
    have h2 := hΩ.norm_offdiag_le hlj.symm
    have h3 : ‖greenMinor G j k l‖ ≤ ‖G k l‖ + ‖greenMinor G j k l - G k l‖ := by
      calc ‖greenMinor G j k l‖ = ‖G k l + (greenMinor G j k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k j‖ * ‖G j l‖ ≤ ‖G k j‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    linarith
  have hlde := hLDE k j hkj
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := hsq
    _ ≤ 9 / 4 * (Φ * ldeColRHS S G k j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k j‖ ^ 2)) := by ring

/-- **(4.11)**: iterating (4.10) once along the row and once along the column,
`|G_{ij}|² ≤ 81 Φ² (∑_{k,l} S_{ik} |G_{kl}|² S_{lj} + S_{ij})` for `i ≠ j`.
The term `S_{ij}` is the contribution `k = j` of the paper, where `|G_{jj}|² = O(1)`. -/
theorem norm_sq_green_le_two_sided (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
  have hΦ : 0 ≤ Φ := by linarith
  have h1 := norm_sq_green_le_row hMG hm hΩ hδ hS0 hSrow hΦ hΦδ hLrow hij
  have hk : ∀ k, ‖G k j‖ ^ 2
      ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl]
      have h2 := hΩ.norm_sq_diag_le hm hδ k
      have h3 : 0 ≤ 9 * Φ * ∑ l, S l k * ‖G k l‖ ^ 2 :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun l _ =>
          mul_nonneg (hS0 l k) (sq_nonneg _))
      linarith
    · rw [ite_eq_right hkj, add_zero]
      exact norm_sq_green_le_col hGM hm hΩ hδ hS0 hScol hΦ hΦδ hLcol hkj
  have hsum : ∑ k, S i k * ‖G k j‖ ^ 2
      ≤ 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
    calc ∑ k, S i k * ‖G k j‖ ^ 2
        ≤ ∑ k, S i k * (9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hS0 i k)
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j)
            + ∑ k, S i k * (if k = j then 9 / 4 else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
          congr 1
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  have hX : 0 ≤ ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hS0 i k) (sq_nonneg _)) (hS0 l j)
  have hSij := hS0 i j
  have hΦ2 : Φ ≤ Φ ^ 2 := by nlinarith
  calc ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := h1
    _ ≤ 9 * Φ * (9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
        nlinarith [mul_le_mul_of_nonneg_right hΦ2 hSij]

/-- (4.11) in the form used below: with `Λ` bounding both terms on the right,
`|G_{ij}|² ≤ 162 Φ² Λ` for `i ≠ j`. -/
theorem norm_sq_green_offdiag_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ := by
  have h := norm_sq_green_le_two_sided hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hij
  have h2 : ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j ≤ 2 * Λ := by
    linarith [hΛ1 i j, hΛ2 i j]
  have hΦ2 : 0 ≤ 81 * Φ ^ 2 := by positivity
  calc ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := h
    _ ≤ 81 * Φ ^ 2 * (2 * Λ) := mul_le_mul_of_nonneg_left h2 hΦ2
    _ = 162 * Φ ^ 2 * Λ := by ring

omit [DecidableEq n] in
/-- A double sum over a subset is bounded by the full double sum, for non-negative terms. -/
private theorem sum_sum_le_sum_sum (s : Finset n) {f : n → n → ℝ} (hf : ∀ k l, 0 ≤ f k l) :
    ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k, ∑ l, f k l := by
  calc ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k ∈ s, ∑ l, f k l :=
        Finset.sum_le_sum fun k _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun l _ _ => hf k l
    _ ≤ ∑ k, ∑ l, f k l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun k _ _ =>
          Finset.sum_nonneg fun l _ => hf k l

/-- The right-hand side of the quadratic LDE, after removing the `(i)` superscript with
(4.9) and using (4.11): `∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li} ≤ 38 Φ Λ`. -/
theorem ldeQuadRHS_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ldeQuadRHS S G i ≤ 38 * Φ * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hpt : ∀ k ∈ univ.erase i, ∀ l ∈ univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
        ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k hk l hl
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k l
    have h2 := hΩ.norm_offdiag_le hli.symm
    have h3 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + ‖greenMinor G i k l - G k l‖ := by
      calc ‖greenMinor G i k l‖ = ‖G k l + (greenMinor G i k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i l‖ ≤ ‖G k i‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h5 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + 2 * δ * ‖G k i‖ := by linarith
    have h6 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
      hΛ1 hΛ2 hki
    have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
    have h7 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k i‖ ^ 2 := by
      have := norm_nonneg (greenMinor G i k l)
      nlinarith [sq_nonneg (‖G k l‖ - 2 * δ * ‖G k i‖), norm_nonneg (G k i),
        norm_nonneg (G k l)]
    have h8 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 36 * Φ * Λ := by
      have h9 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h10 : 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h11 : 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) ≤ 36 * 1 * (Φ * Λ) := by
        have : 0 ≤ Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
      linarith
    have h12 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 (hS0 i k)) (hS0 l i)
  have hnn : ∀ k l, 0 ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k l
    have : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
    exact mul_nonneg (mul_nonneg (hS0 i k) (by positivity)) (hS0 l i)
  calc ldeQuadRHS S G i
      ≤ ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
          S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hpt k hk l hl
    _ ≤ ∑ k, ∑ l, S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        sum_sum_le_sum_sum _ hnn
    _ = 2 * ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l i
          + 36 * Φ * Λ * ((∑ k, S i k) * ∑ l, S l i) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 2 * Λ + 36 * Φ * Λ * (1 * 1) := by
        have h1 := hΛ1 i i
        have h2 : (∑ k, S i k) * ∑ l, S l i ≤ 1 * 1 :=
          mul_le_mul (hSrow i) (hScol i) (Finset.sum_nonneg fun l _ => hS0 l i) zero_le_one
        have h3 : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
    _ ≤ 38 * Φ * Λ := by nlinarith

/-- **The self-consistent equation behind (4.3).**  On the event, (4.7), the quadratic LDE,
(4.9) and (4.11) give
`G_{ii}⁻¹ = -z - t ∑_k S_{ik} G_{kk} + e_i` with `|e_i|² ≤ 240 Φ² Λ`. -/
theorem norm_sq_selfEnergy_err_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    (hLquad : LDEQuad H G S t Φ) (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ‖(G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k‖ ^ 2 ≤ 240 * Φ ^ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hΦ : 0 ≤ Φ := by linarith
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
  have hGii := hΩ.diag_ne_zero hm hδ i
  have hinv := inv_green_diag_eq hGM hMG hGii
  rw [sum_erase_sub_smul_quad, sub_smul_one_apply_self] at hinv
  set Q := ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i with hQ
  set A2 := Q - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k with hA2
  set A3 := (t : ℂ) * ((S i i : ℂ) * G i i) with hA3
  set A4 := (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) with hA4
  have hsplit : ∑ k, (S i k : ℂ) * G k k
      = (S i i : ℂ) * G i i + ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k
        + ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have heq : (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k = H i i - A2 + A3 + A4 := by
    rw [hinv, hsplit, hA2, hA3, hA4]
    ring
  rw [heq]
  -- the four pieces
  have hb1 : ‖H i i‖ ^ 2 ≤ Φ * Λ :=
    (hLdiag i).trans (mul_le_mul_of_nonneg_left (hΛ2 i i) hΦ)
  have hb2 : ‖A2‖ ^ 2 ≤ 38 * Φ ^ 2 * Λ := by
    have h1 := hLquad i
    have h2 := ldeQuadRHS_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hΛ1 hΛ2 i
    have h3 : ‖A2‖ ^ 2 = ldeQuadLHS H G S t i := rfl
    calc ‖A2‖ ^ 2 ≤ Φ * ldeQuadRHS S G i := h3 ▸ h1
      _ ≤ Φ * (38 * Φ * Λ) := mul_le_mul_of_nonneg_left h2 hΦ
      _ = 38 * Φ ^ 2 * Λ := by ring
  have hSii1 : S i i ≤ 1 :=
    le_trans (Finset.single_le_sum (fun k _ => hS0 i k) (Finset.mem_univ i)) (hSrow i)
  have hb3 : ‖A3‖ ^ 2 ≤ 9 / 4 * Λ := by
    have hn : ‖A3‖ = t * (S i i * ‖G i i‖) := by
      rw [hA3, norm_mul, norm_mul, Complex.norm_of_nonneg ht0, Complex.norm_of_nonneg (hS0 i i)]
    have h1 := hΩ.norm_sq_diag_le hm hδ i
    have h2 : ‖A3‖ ^ 2 ≤ S i i ^ 2 * ‖G i i‖ ^ 2 := by
      have h0 : 0 ≤ S i i * ‖G i i‖ := mul_nonneg (hS0 i i) (norm_nonneg _)
      have h5 : t * (S i i * ‖G i i‖) ≤ S i i * ‖G i i‖ := by nlinarith
      calc ‖A3‖ ^ 2 = (t * (S i i * ‖G i i‖)) ^ 2 := by rw [hn]
        _ ≤ (S i i * ‖G i i‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 h0) h5 2
        _ = S i i ^ 2 * ‖G i i‖ ^ 2 := by ring
    have h3 : S i i ^ 2 ≤ Λ := by nlinarith [hS0 i i, hΛ2 i i]
    have h4 : S i i ^ 2 * ‖G i i‖ ^ 2 ≤ Λ * (9 / 4) :=
      mul_le_mul h3 h1 (sq_nonneg _) hΛ0
    linarith
  have hb4 : ‖A4‖ ^ 2 ≤ 18 * Φ * Λ := by
    have hpt : ∀ k ∈ univ.erase i,
        ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ ≤ S i k * (2 * δ * ‖G i k‖) := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      rw [norm_mul, Complex.norm_of_nonneg (hS0 i k), norm_sub_rev]
      refine mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k k
      have h2 := hΩ.norm_offdiag_le hki
      have h3 : ‖G k i‖ * ‖G i k‖ ≤ δ * ‖G i k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      linarith
    have hA4le : ‖A4‖ ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) := by
      rw [hA4, norm_mul, Complex.norm_of_nonneg ht0]
      calc t * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖
          ≤ 1 * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ ∑ k ∈ univ.erase i, ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ := by
            rw [one_mul]; exact norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum hpt
    have hCS : (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2
        ≤ (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => hS0 i k)
        (fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)) fun k _ => le_of_eq (by ring)
    have hE1 : ∑ k ∈ univ.erase i, S i k ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
        fun k _ _ => hS0 i k) (hSrow i)
    have hE2 : ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ)) := by
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have hki : i ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h1 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
        hΛ1 hΛ2 hki
      calc (2 * δ * ‖G i k‖) ^ 2 = 4 * δ ^ 2 * ‖G i k‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hE3 : ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ))
        ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by
      rw [← Finset.sum_mul]
      have : 0 ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by positivity
      nlinarith
    have hE4 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) ≤ 18 * Φ * Λ := by
      have h1 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 18 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h2 : 0 ≤ Φ * Λ := mul_nonneg hΦ hΛ0
      nlinarith
    have hS : 0 ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)
    have hA4sq : ‖A4‖ ^ 2 ≤ (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA4le 2
    have hE5 : (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ 1 * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hE1 hS
    linarith
  -- assemble
  have htri : ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by
    calc ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i - A2 + A3‖ + ‖A4‖ := norm_add_le _ _
      _ ≤ ‖H i i - A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_add_le (H i i - A2) A3]
      _ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_sub_le (H i i) A2]
  have hsq : ‖H i i - A2 + A3 + A4‖ ^ 2
      ≤ 4 * (‖H i i‖ ^ 2 + ‖A2‖ ^ 2 + ‖A3‖ ^ 2 + ‖A4‖ ^ 2) := by
    have h0 := norm_nonneg (H i i - A2 + A3 + A4)
    have h1 : ‖H i i - A2 + A3 + A4‖ ^ 2 ≤ (‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖) ^ 2 :=
      pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖H i i‖ - ‖A2‖), sq_nonneg (‖H i i‖ - ‖A3‖),
      sq_nonneg (‖H i i‖ - ‖A4‖), sq_nonneg (‖A2‖ - ‖A3‖), sq_nonneg (‖A2‖ - ‖A4‖),
      sq_nonneg (‖A3‖ - ‖A4‖)]
  have hΦΛ : Φ * Λ ≤ Φ ^ 2 * Λ := by
    have : Φ ≤ Φ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  have hΛΦ : Λ ≤ Φ ^ 2 * Λ := by
    have : 1 ≤ Φ ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- **Stability of `1 - ξ S` in `max → max` norm**, with constant `K`: whenever
`|v_i - ξ (S v)_i| ≤ B` for all `i`, then `|v_i| ≤ K B` for all `i`.  This is the paper's
`‖(1 - t m² S)⁻¹‖_{max→max} = O(1)`, stated without forming the inverse. -/
def Stable (S : n → n → ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
  ∀ (v : n → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B

/-- **(4.3)**, deterministic form.  On the event `Ω`, given the three LDE inputs, the bound
`|H_{ii}|² ≤ Φ S_{ii}` and stability of `1 - t m² S` with constant `K`,
`|G_{ii} - m|² ≤ 2160 K² Φ² Λ`, where `Λ` bounds `∑_{k,l} S_{ik}|G_{kl}|²S_{lj}` and `S_{ij}`
(in the block model `Λ = 2 max_{a,b} L_{(+,-),(a,b)}`). -/
theorem norm_sq_green_diag_sub_le [Nonempty n] (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ}
    (hmz : m * ((t : ℂ) * m + z) = -1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k) (hSrow : ∀ i, ∑ k, S i k = 1)
    (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) (hLquad : LDEQuad H G S t Φ)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {K : ℝ} (hKδ : K * δ ≤ 1 / 2) (hStab : Stable S ((t : ℂ) * m ^ 2) K)
    (i : n) :
    ‖G i i - m‖ ^ 2 ≤ 2160 * K ^ 2 * Φ ^ 2 * Λ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i₀ i₀) (hΛ2 i₀ i₀)
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i₀ i₀)
  have hSrow' : ∀ i, ∑ k, S i k ≤ 1 := fun i => (hSrow i).le
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  set ε := Real.sqrt (240 * Φ ^ 2 * Λ) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  set e : n → ℂ := fun i => (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k with he
  have heb : ∀ i, ‖e i‖ ≤ ε := by
    intro i
    rw [hε, Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact norm_sq_selfEnergy_err_le hGM hMG hm ht0 ht1 hΩ hδ hS0 hSrow' hScol hΦ1 hΦδ hLrow
      hLcol hLquad hLdiag hΛ1 hΛ2 i
  set v : n → ℂ := fun k => G k k - m with hv
  have hvδ : ∀ k, ‖v k‖ ≤ δ := fun k => hΩ.norm_diag_sub_le k
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => ‖v k‖
  set V := ‖v k₀‖ with hV
  -- the exact identity `v_i - t m² (S v)_i = -m² e_i + m v_i x_i`
  have hident : ∀ i, v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k
      = -(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
    intro i
    have hGii := hΩ.diag_ne_zero hm hδ i
    have hSv : ∑ k, (S i k : ℂ) * G k k = ∑ k, (S i k : ℂ) * v k + m := by
      have h1 : ∑ k, (S i k : ℂ) * v k = ∑ k, (S i k : ℂ) * G k k - m := by
        have h2 : ∑ k, (S i k : ℂ) = 1 := by exact_mod_cast hSrow i
        rw [hv]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2, one_mul]
      rw [h1]; ring
    have hinv : (G i i)⁻¹ = m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
      have hz : z = -m⁻¹ - (t : ℂ) * m := by
        field_simp
        linear_combination hmz
      simp only [he, hSv, hz]
      ring
    have h1 : G i i * (m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hGii
    have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
    simp only [hv]
    linear_combination m * h1 - G i i * hmm
  -- bound on the right-hand side
  have hSvb : ∀ i, ‖∑ k, (S i k : ℂ) * v k‖ ≤ V := by
    intro i
    calc ‖∑ k, (S i k : ℂ) * v k‖ ≤ ∑ k, ‖(S i k : ℂ) * v k‖ := norm_sum_le _ _
      _ ≤ ∑ k, S i k * V := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_of_nonneg (hS0 i k)]
          exact mul_le_mul_of_nonneg_left (hk₀ k) (hS0 i k)
      _ = V := by rw [← Finset.sum_mul, hSrow i, one_mul]
  have hBi : ∀ i, ‖v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k‖ ≤ 3 / 2 * ε + δ * V := by
    intro i
    rw [hident i]
    have hx : ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ ≤ V + ε := by
      calc ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖
          ≤ ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k‖ + ‖e i‖ := norm_sub_le _ _
        _ ≤ V + ε := by
          rw [norm_mul, Complex.norm_of_nonneg ht0]
          have h1 := hSvb i
          have h2 : t * ‖∑ k, (S i k : ℂ) * v k‖ ≤ 1 * V :=
            mul_le_mul ht1 h1 (norm_nonneg _) zero_le_one
          linarith [heb i]
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖-(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖
        ≤ ‖-(m ^ 2 * e i)‖ + ‖m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖ :=
          norm_add_le _ _
      _ = ‖e i‖ + ‖v i‖ * ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ := by
          rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, hm]; ring
      _ ≤ ε + δ * (V + ε) := by
          have := mul_le_mul (hvδ i) hx (norm_nonneg _) hδ0
          linarith [heb i]
      _ ≤ 3 / 2 * ε + δ * V := by nlinarith
  have hst := hStab v (3 / 2 * ε + δ * V) hBi
  have hVb : V ≤ 3 * K * ε := by
    have h1 := hst k₀
    have h2 : K * (δ * V) ≤ 1 / 2 * V := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKδ (norm_nonneg _)
    rw [← hV] at h1
    nlinarith
  have hvi : ‖v i‖ ≤ 3 * K * ε := (hk₀ i).trans hVb
  have hsq : ‖v i‖ ^ 2 ≤ (3 * K * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvi 2
  have hε2 : ε ^ 2 = 240 * Φ ^ 2 * Λ := Real.sq_sqrt (by positivity)
  calc ‖G i i - m‖ ^ 2 = ‖v i‖ ^ 2 := rfl
    _ ≤ (3 * K * ε) ^ 2 := hsq
    _ = 9 * K ^ 2 * ε ^ 2 := by ring
    _ = 2160 * K ^ 2 * Φ ^ 2 * Λ := by rw [hε2]; ring

end EntryBound

section Averaged

variable {n : Type*} [Fintype n]

/-- **The self-consistent step of (4.5).**  Let `x_i` stand for `E_i(G_{ii} - m)`.  If
`x_i = ξ ∑_k S_{ik}(G_{kk} - m) + O(A)` (the Gaussian integration by parts display on p. 50)
and `∑_k S_{ik}(1 - E_k)(G_{kk} - m) = O(B)` (the fluctuation averaging (4.12) with
`t_k = S_{ik}`), then stability of `1 - ξS` gives `|x_i| ≤ K (A + B)`. -/
theorem norm_condExp_le {S : n → n → ℝ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ} (x : n → ℂ) {A B : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B) (i : n) :
    ‖x i‖ ≤ K * (A + B) := by
  refine hStab x (A + B) (fun j => ?_) i
  have hsplit : x j - ξ * ∑ k, (S j k : ℂ) * x k
      = (x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc ‖(x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖
      ≤ ‖x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m)‖
        + ‖ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖ := norm_add_le _ _
    _ ≤ A + 1 * B := by
        rw [norm_mul]
        have := mul_le_mul hξ (hFA j) (norm_nonneg _) zero_le_one
        linarith [hIBP j]
    _ = A + B := by ring

/-- **(4.5)**, deterministic form: for coefficients with `∑_k |c_k| ≤ 1`, if
`∑_k c_k (1 - E_k)(G_{kk} - m) = O(B')` (fluctuation averaging (4.12)) then
`|∑_k c_k (G_{kk} - m)| ≤ B' + K (A + B)`. -/
theorem norm_sum_coef_green_sub_le [Nonempty n] {S : n → n → ℝ}
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ}
    (x : n → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B)
    {c : n → ℝ} (hc : ∑ k, |c k| ≤ 1)
    (hFA' : ‖∑ k, (c k : ℂ) * ((G k k - m) - x k)‖ ≤ B') :
    ‖∑ k, (c k : ℂ) * (G k k - m)‖ ≤ B' + K * (A + B) := by
  have hx := norm_condExp_le hξ hStab x hIBP hFA
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hX0 : 0 ≤ K * (A + B) := le_trans (norm_nonneg _) (hx i₀)
  have hsplit : ∑ k, (c k : ℂ) * (G k k - m)
      = ∑ k, (c k : ℂ) * ((G k k - m) - x k) + ∑ k, (c k : ℂ) * x k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  have hcx : ‖∑ k, (c k : ℂ) * x k‖ ≤ K * (A + B) := by
    calc ‖∑ k, (c k : ℂ) * x k‖ ≤ ∑ k, ‖(c k : ℂ) * x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, |c k| * (K * (A + B)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
      _ = (∑ k, |c k|) * (K * (A + B)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (K * (A + B)) := mul_le_mul_of_nonneg_right hc hX0
      _ = K * (A + B) := one_mul _
  linarith [norm_add_le (∑ k, (c k : ℂ) * ((G k k - m) - x k)) (∑ k, (c k : ℂ) * x k)]

end Averaged

end RBM.Green
