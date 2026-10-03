/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import RBM2D.Gauss.Model

/-!
# The Hanson–Wright layer, first half: polynomial weights, tame functions, the row chaos

The setting is the two-dimensional sequence model of `RBM2D/Gauss/Model.lean`.  The paper
(arXiv:2503.07606) does not state this file as a lemma: it is abstract Gaussian calculus on
independent centred coordinates, and involves neither `Z_L²` nor the variance profile `S`.

## The model

The objects are `Sizes`, `Sizes.SeqΩ d`, `Sizes.SeqCoord d`, `Sizes.seqGvar d`, `Sizes.seqP d`
(the sequence model of `RBM2D/Gauss/Model.lean`), in the namespace `RBM.Green`.  The row chaos
itself is dimension-free.

## The abstract setting: `RBM.Green.RowChaos`

Everything is done for an abstract *row chaos* (`RowChaos d κ`), which is exactly the data the
quadratic form at a fixed row `i` presents:

* an index type `κ` (in the application `{k // k ≠ i}`);
* two Gaussian coordinates `co k true`, `co k false` per index, all distinct, with equal
  variance `w k` — the real and imaginary parts of `H_{ik}`;
* a sign `eps k = ±1` and a scale `r` (in the application `r = √t`, since `H_t = √t X`), giving
  the row entry `h_k = r (ω_{co k tt} + ε_k i ω_{co k ff})`, hence `E|h_k|² = σ_k := 2 r² w_k`;
* a matrix `B`, continuous, **globally bounded**, and **not reading any coordinate `co k b`**.

The last field, `B_free` (together with `Ifree_free`), is the row independence hypothesis:
"`B` is `FinDep` with a witness set containing no row-`i` coordinate", the property
`FinDepOffRow` of `RBM2D/Green/CondRow.lean`.

The chaos, its control and the two error terms are

* `chaos ω = ∑_{k,l} h_k B_{kl} \bar h_l − ∑_k σ_k B_{kk}`  (`Q`);
* `U_k = ∑_l B_{kl} \bar h_l`, `V_k = ∑_m h_m B_{mk}`;
* `Tq = ∑_k σ_k (‖U_k‖² + ‖V_k‖²)`  (`T`), `Rq = ∑_k σ_k U_k V_k`  (`R`), with `‖R‖ ≤ T/2`.

## Main results

* `RBM.Green.FinDep` — "reads only finitely many coordinates".
* `RBM.Green.polyW`, `RBM.Green.young_pow`, `RBM.Green.Tame` and its closure lemmas.
* `RBM.Green.GaussIBP`, `RBM.Green.Tame.integrable`.
* `RBM.Green.RowChaos.hasDerivAt_chaos_true` / `_false` — `∂_{a_k}Q = dA_k`, `∂_{b_k}Q = dB_k`.
* `RBM.Green.RowChaos.sum_coord_mul_deriv` — **Euler's identity**
  `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})`.

## Hypotheses carried

`RBM.Green.GaussIBP d` is a structure with two fields, both properties of the product measure
`Sizes.seqP d` alone:

* `stein` — `E[ω_c g] = v_c E[∂_c g]` for `Tame` `g` (continuous, finitely dependent,
  **polynomially** bounded);
* `polyInt` — all polynomial moments of `Sizes.seqP d` are finite.

It is a structure carried by the lemmas that integrate; it is proved for the model in
`RBM2D/Green/IBPPoly.lean`.
Only `Tame.integrable` in this file takes it as a hypothesis.

## Not in this file

The master integration-by-parts identity, the moment recursion and the variance interface are
in `RBM2D/Green/LDEQuadMom.lean`, and the positive chaos moment bound in
`RBM2D/Green/LDEQuadT.lean`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Finset RBM.Gauss
open scoped NNReal

/-! ### Finite dependence -/

/-- `g : Sizes.SeqΩ d → V` reads only finitely many Gaussian coordinates.  Every function we feed
to Stein's identity has this property, which lets the identity on the infinite product
`Sizes.seqP d` be reduced to one on a finite `MeasureTheory.Measure.pi`.

`FinDepOffRow d n k g` (`RBM2D/Green/CondRow.lean`) is `FinDep d g` with a witness set that
contains no coordinate of row `k` of slice `n`; dropping that conjunct gives
`FinDepOffRow d n k g → FinDep d g` (the same witness set). -/
def FinDep (d : Sizes) {V : Type*} (g : Sizes.SeqΩ d → V) : Prop :=
  ∃ I : Finset (Sizes.SeqCoord d), ∀ ω ω' : Sizes.SeqΩ d, (∀ e ∈ I, ω e = ω' e) → g ω = g ω'

variable {d : Sizes}

/-! ### Polynomial weights -/

/-- `polyW I ω = 1 + ∑_{c ∈ I} |ω c|`, the polynomial weight used to dominate every integrand
of this file. -/
noncomputable def polyW (I : Finset (Sizes.SeqCoord d)) (ω : Sizes.SeqΩ d) : ℝ := 1 + ∑ c ∈ I, |ω c|

theorem one_le_polyW (I : Finset (Sizes.SeqCoord d)) (ω : Sizes.SeqΩ d) : 1 ≤ polyW I ω := by
  have : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold polyW; linarith

theorem polyW_pos (I : Finset (Sizes.SeqCoord d)) (ω : Sizes.SeqΩ d) : 0 < polyW I ω :=
  lt_of_lt_of_le zero_lt_one (one_le_polyW I ω)

theorem polyW_nonneg (I : Finset (Sizes.SeqCoord d)) (ω : Sizes.SeqΩ d) : 0 ≤ polyW I ω :=
  le_trans zero_le_one (one_le_polyW I ω)

theorem polyW_mono {I J : Finset (Sizes.SeqCoord d)} (h : I ⊆ J) (ω : Sizes.SeqΩ d) :
    polyW I ω ≤ polyW J ω := by
  have : ∑ c ∈ I, |ω c| ≤ ∑ c ∈ J, |ω c| :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => abs_nonneg _
  unfold polyW; linarith

theorem polyW_pow_le {I J : Finset (Sizes.SeqCoord d)} (hIJ : I ⊆ J) {n m : ℕ} (hnm : n ≤ m)
    (ω : Sizes.SeqΩ d) :
    polyW I ω ^ n ≤ polyW J ω ^ m :=
  le_trans (pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_mono hIJ ω) n)
    (pow_le_pow_right₀ (one_le_polyW J ω) hnm)

/-! ### An elementary Young inequality with natural exponents

`(q+1) a b^q ≤ a^{q+1} + q b^{q+1}` for `a, b ≥ 0`: the arithmetic–geometric mean inequality for
the `q+1` numbers `a, b, …, b`, proved from `a^n - b^n = (a-b)∑ a^i b^{n-1-i}`.  Only natural
powers occur, which is what lets the moment recursion be closed without any `rpow`. -/
theorem young_pow (q : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((q : ℝ) + 1) * (a * b ^ q) ≤ a ^ (q + 1) + (q : ℝ) * b ^ (q + 1) := by
  have hgs : (∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i)) * (a - b)
      = a ^ (q + 1) - b ^ (q + 1) := geom_sum₂_mul a b (q + 1)
  set Sm := ∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i) with hS
  have hconst : ∑ _i ∈ Finset.range (q + 1), b ^ q = ((q : ℝ) + 1) * b ^ q := by
    rw [Finset.sum_const, Finset.card_range]
    ring
  have key : ((q : ℝ) + 1) * b ^ q * (a - b) ≤ a ^ (q + 1) - b ^ (q + 1) := by
    rcases le_total b a with hab | hab
    · have hge : ((q : ℝ) + 1) * b ^ q ≤ Sm := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hab i) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hge (sub_nonneg.mpr hab)
      rw [hgs] at hmul
      exact hmul
    · have hle : Sm ≤ ((q : ℝ) + 1) * b ^ q := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab i) (by positivity)
      have hmul := mul_le_mul_of_nonpos_right hle (sub_nonpos.mpr hab)
      rw [hgs] at hmul
      exact hmul
  have expand : ((q : ℝ) + 1) * b ^ q * (a - b)
      = ((q : ℝ) + 1) * (a * b ^ q) - ((q : ℝ) + 1) * b ^ (q + 1) := by
    rw [pow_succ]; ring
  rw [expand] at key
  linarith

/-! ### Tame functions: continuous, finitely dependent, polynomially bounded

Every integrand of this file is a polynomial in finitely many Gaussian coordinates with
coefficients read off a *bounded* matrix.  `Tame` is exactly that class; it is closed under the
ring operations and under complex conjugation, and (given `GaussIBP`) every `Tame` function is
integrable. -/

/-- `f` is **tame**: continuous, reading only finitely many coordinates, and dominated by a
polynomial in finitely many coordinates. -/
structure Tame (d : Sizes) (f : Sizes.SeqΩ d → ℂ) : Prop where
  /-- `f` is continuous. -/
  cont : Continuous f
  /-- `f` reads only finitely many coordinates. -/
  findep : FinDep d f
  /-- `f` is dominated by a polynomial in finitely many coordinates. -/
  poly : ∃ (I : Finset (Sizes.SeqCoord d)) (n : ℕ) (C : ℝ), ∀ ω, ‖f ω‖ ≤ C * polyW I ω ^ n

namespace Tame

variable {f g : Sizes.SeqΩ d → ℂ}

theorem const (z : ℂ) : Tame d (fun _ => z) :=
  ⟨continuous_const, ⟨∅, fun _ _ _ => rfl⟩, ⟨∅, 0, ‖z‖, fun ω => by simp⟩⟩

theorem coord (c : Sizes.SeqCoord d) : Tame d (fun ω : Sizes.SeqΩ d => (ω c : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_apply c),
    ⟨{c}, fun ω ω' h => by
      show ((ω c : ℂ)) = ((ω' c : ℂ))
      rw [h c (Finset.mem_singleton_self c)]⟩, ⟨{c}, 1, 1, fun ω => ?_⟩⟩
  have : |ω c| ≤ polyW ({c} : Finset (Sizes.SeqCoord d)) ω := by
    unfold polyW; simp
  simpa [Complex.norm_real] using this

theorem add (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω + g ω) := by
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.add hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, max n₁ n₂, C₁ + C₂, fun ω => ?_⟩⟩
  · show f ω + g ω = f ω' + g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : C₁ * polyW I₁ ω ^ n₁ ≤ C₁ * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_left (le_max_left _ _) ω) hC₁
    have e₂ : C₂ * polyW I₂ ω ^ n₂ ≤ C₂ * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_right (le_max_right _ _) ω) hC₂
    calc ‖f ω + g ω‖ ≤ ‖f ω‖ + ‖g ω‖ := norm_add_le _ _
      _ ≤ C₁ * polyW I₁ ω ^ n₁ + C₂ * polyW I₂ ω ^ n₂ := add_le_add (h₁ ω) (h₂ ω)
      _ ≤ (C₁ + C₂) * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ := by linarith

theorem mul (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω * g ω) := by
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.mul hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, n₁ + n₂, C₁ * C₂, fun ω => ?_⟩⟩
  · show f ω * g ω = f ω' * g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : polyW I₁ ω ^ n₁ ≤ polyW (I₁ ∪ I₂) ω ^ n₁ :=
      polyW_pow_le Finset.subset_union_left le_rfl ω
    have e₂ : polyW I₂ ω ^ n₂ ≤ polyW (I₁ ∪ I₂) ω ^ n₂ :=
      polyW_pow_le Finset.subset_union_right le_rfl ω
    have hp₁ : (0 : ℝ) ≤ polyW (I₁ ∪ I₂) ω ^ n₁ := le_of_lt (pow_pos (polyW_pos _ _) _)
    have hp₂ : (0 : ℝ) ≤ polyW (I₁ ∪ I₂) ω ^ n₂ := le_of_lt (pow_pos (polyW_pos _ _) _)
    calc ‖f ω * g ω‖ = ‖f ω‖ * ‖g ω‖ := norm_mul _ _
      _ ≤ (C₁ * polyW I₁ ω ^ n₁) * (C₂ * polyW I₂ ω ^ n₂) :=
          mul_le_mul (h₁ ω) (h₂ ω) (norm_nonneg _)
            (mul_nonneg hC₁ (le_of_lt (pow_pos (polyW_pos _ _) _)))
      _ ≤ (C₁ * C₂) * polyW (I₁ ∪ I₂) ω ^ (n₁ + n₂) := by
          rw [pow_add]
          have hkey := mul_le_mul e₁ e₂ (le_of_lt (pow_pos (polyW_pos _ _) _)) hp₁
          calc C₁ * polyW I₁ ω ^ n₁ * (C₂ * polyW I₂ ω ^ n₂)
              = C₁ * C₂ * (polyW I₁ ω ^ n₁ * polyW I₂ ω ^ n₂) := by ring
            _ ≤ C₁ * C₂ * (polyW (I₁ ∪ I₂) ω ^ n₁ * polyW (I₁ ∪ I₂) ω ^ n₂) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg hC₁ hC₂)

theorem neg (hf : Tame d f) : Tame d (fun ω => -f ω) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨hf.cont.neg, ⟨J, fun ω ω' hh => by show -f ω = -f ω'; rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem sub (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem conj (hf : Tame d f) : Tame d (fun ω => (starRingEnd ℂ) (f ω)) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨Complex.continuous_conj.comp hf.cont,
    ⟨J, fun ω ω' hh => by
      show (starRingEnd ℂ) (f ω) = (starRingEnd ℂ) (f ω'); rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem pow (hf : Tame d f) (n : ℕ) : Tame d (fun ω => f ω ^ n) := by
  induction n with
  | zero => simpa using Tame.const (d := d) 1
  | succ n ih => simpa [_root_.pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Sizes.SeqΩ d → ℂ} (h : ∀ i ∈ s, Tame d (F i)) :
    Tame d (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Tame.const (d := d) 0
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hi₀] using h₀.add hs

/-- A continuous, finitely dependent, globally bounded function is tame. -/
theorem ofBdd {C : ℝ} (hc : Continuous f) (hd : FinDep d f) (hb : ∀ ω, ‖f ω‖ ≤ C) :
    Tame d f :=
  ⟨hc, hd, ∅, 0, C, fun ω => by simpa using hb ω⟩

end Tame

/-! ### The two facts about `Sizes.seqP d` that are consumed here -/

/-- **The Gaussian calculus on `Sizes.seqP d`**, in the form this file uses.

* `stein` is the Stein identity `E[ω_c g] = v_c E[∂_c g]` for `Tame` `g` (continuous, finitely
  dependent, **polynomially** bounded).  Polynomial growth, and not global boundedness, is what
  is needed here: the integrands of a second order chaos are genuine polynomials in the
  Gaussian coordinates, so they are never globally bounded.  It is the one-dimensional
  integration by parts (`RBM.integral_mul_gaussianReal`) pushed through
  the finite-dimensional marginals of `Sizes.seqP d`.
* `polyInt` is the statement that all polynomial moments of `Sizes.seqP d` are finite.

Both are properties of the product measure alone.  They are **carried in this structure**, and
nothing else is assumed. -/
structure GaussIBP (d : Sizes) : Prop where
  /-- `E[ω_c · g] = gvar_c · E[∂_c g]` for tame `g`. -/
  stein : ∀ (c : Sizes.SeqCoord d) (g g' : Sizes.SeqΩ d → ℂ), Tame d g → Tame d g' →
    (∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c)) →
    ∫ ω, (ω c : ℂ) * g ω ∂(Sizes.seqP d) = (Sizes.seqGvar d c : ℝ) * ∫ ω, g' ω ∂(Sizes.seqP d)
  /-- All polynomial moments of `Sizes.seqP d` are finite. -/
  polyInt : ∀ (I : Finset (Sizes.SeqCoord d)) (n : ℕ),
    Integrable (fun ω => polyW I ω ^ n) (Sizes.seqP d)

/-- Every tame function is integrable. -/
theorem Tame.integrable (hG : GaussIBP d) {f : Sizes.SeqΩ d → ℂ} (hf : Tame d f) :
    Integrable f (Sizes.seqP d) := by
  obtain ⟨I, n, C, hb⟩ := hf.poly
  have hC : 0 ≤ C := by
    have hp : (0 : ℝ) < polyW I (fun _ => 0) ^ n := pow_pos (polyW_pos _ _) _
    nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
  refine Integrable.mono ((hG.polyInt I n).const_mul C) hf.cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hp : (0 : ℝ) ≤ C * polyW I ω ^ n := mul_nonneg hC (le_of_lt (pow_pos (polyW_pos _ _) _))
  have : ‖C * polyW I ω ^ n‖ = C * polyW I ω ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
  rw [this]
  exact hb ω

/-! ### The row chaos

The data below is exactly what a quadratic form in the entries of one row presents at a fixed
row `i`: an index set `κ` (in the application `{k // k ≠ i}`), two Gaussian coordinates
`co k true`, `co k false` per index (the real and imaginary parts of `H_{ik}`), a sign
`eps k = ±1` (which of `X_{ik}`, `X_{ki}` carries the coordinates), a scale `r` (`= √t`, since
`H_t = √t X`), and a matrix `B` (`= G^{(i)}`) which is **bounded** and **does not read any of
the coordinates `co k b`**.  That last property is `B_free` below, and is the row independence
that `FinDepOffRow` (`RBM2D/Green/CondRow.lean`) supplies. -/

/-- The data of a *row chaos*: the Gaussian row `h_k = r(ω_{co k tt} + ε_k i ω_{co k ff})` and a
bounded matrix `B` that does not read the coordinates of the row. -/
structure RowChaos (d : Sizes) (κ : Type*) [Fintype κ] [DecidableEq κ] where
  /-- The two coordinates carrying the real and imaginary part of the row entry `h_k`. -/
  co : κ → Bool → Sizes.SeqCoord d
  /-- Distinct indices and tags use distinct coordinates. -/
  co_inj : Function.Injective fun p : κ × Bool => co p.1 p.2
  /-- Both tags of `k` carry the same variance. -/
  gvar_tag : ∀ k, (Sizes.seqGvar d (co k false) : ℝ) = (Sizes.seqGvar d (co k true) : ℝ)
  /-- The sign `±1` fixing the orientation of the imaginary part. -/
  eps : κ → ℝ
  /-- `eps k = ±1`. -/
  eps_sq : ∀ k, eps k ^ 2 = 1
  /-- The global scale of the row (`√t` for the flow `H_t = √t X`). -/
  r : ℝ
  /-- The matrix of the quadratic form. -/
  B : Sizes.SeqΩ d → κ → κ → ℂ
  /-- `B` is continuous entrywise. -/
  B_cont : ∀ k l, Continuous fun ω => B ω k l
  /-- A global bound for `B`. -/
  Bbd : ℝ
  /-- `B` is globally bounded (in the application, by `η⁻¹`, via `norm_green_le` and
  `norm_apply_le_l2_opNorm`). -/
  B_bdd : ∀ ω k l, ‖B ω k l‖ ≤ Bbd
  /-- The witness set of coordinates `B` reads. -/
  Ifree : Finset (Sizes.SeqCoord d)
  /-- **Row independence**: the witness set contains no coordinate of the row. -/
  Ifree_free : ∀ k b, co k b ∉ Ifree
  /-- `B` is determined by the coordinates in `Ifree`. -/
  B_free : ∀ ω ω', (∀ c ∈ Ifree, ω c = ω' c) → B ω = B ω'

namespace RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos d κ)

/-- The variance of each of the two coordinates of the index `k`. -/
noncomputable def w (k : κ) : ℝ := (Sizes.seqGvar d (C.co k true) : ℝ)

/-- `σ_k = E|h_k|² = 2 r² w_k`; in the application `σ_k = t S_{ik}`. -/
noncomputable def sg (k : κ) : ℝ := 2 * C.r ^ 2 * C.w k

theorem w_nonneg (k : κ) : 0 ≤ C.w k := (Sizes.seqGvar d (C.co k true)).coe_nonneg

theorem sg_nonneg (k : κ) : 0 ≤ C.sg k := by
  have := C.w_nonneg k; unfold sg; positivity

/-- The row entry `h_k = r (ω_{co k tt} + ε_k i ω_{co k ff})`. -/
noncomputable def h (ω : Sizes.SeqΩ d) (k : κ) : ℂ :=
  (C.r : ℂ) * ((ω (C.co k true) : ℂ) + ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ))

/-- `U_k = ∑_l B_{kl} conj(h_l)`. -/
noncomputable def U (ω : Sizes.SeqΩ d) (k : κ) : ℂ := ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)

/-- `V_k = ∑_m h_m B_{mk}`. -/
noncomputable def V (ω : Sizes.SeqΩ d) (k : κ) : ℂ := ∑ m, C.h ω m * C.B ω m k

/-- The centring constant `∑_k σ_k B_{kk}` (random, but not reading the row). -/
noncomputable def cen (ω : Sizes.SeqΩ d) : ℂ := ∑ k, (C.sg k : ℂ) * C.B ω k k

/-- **The chaos** `Q = ∑_{k,l} h_k B_{kl} conj(h_l) − ∑_k σ_k B_{kk}`. -/
noncomputable def chaos (ω : Sizes.SeqΩ d) : ℂ :=
  (∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l)) - C.cen ω

/-- `∂ Q / ∂ ω_{co k tt}`. -/
noncomputable def dA (ω : Sizes.SeqΩ d) (k : κ) : ℂ := (C.r : ℂ) * (C.U ω k + C.V ω k)

/-- `∂ Q / ∂ ω_{co k ff}`. -/
noncomputable def dB (ω : Sizes.SeqΩ d) (k : κ) : ℂ :=
  ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)

/-- `T = ∑_k σ_k (‖U_k‖² + ‖V_k‖²)`, the random control of the recursion. -/
noncomputable def Tq (ω : Sizes.SeqΩ d) : ℝ := ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)

/-- `R = ∑_k σ_k U_k V_k`, the off-diagonal term of the recursion; `‖R‖ ≤ T/2`. -/
noncomputable def Rq (ω : Sizes.SeqΩ d) : ℂ := ∑ k, (C.sg k : ℂ) * C.U ω k * C.V ω k

theorem Tq_nonneg (ω : Sizes.SeqΩ d) : 0 ≤ C.Tq ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Rq_le (ω : Sizes.SeqΩ d) : ‖C.Rq ω‖ ≤ C.Tq ω / 2 := by
  have hterm : ∀ k : κ, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
      ≤ C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
    intro k
    have h2 : ‖C.U ω k‖ * ‖C.V ω k‖ ≤ (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖C.U ω k‖ - ‖C.V ω k‖)]
    have := mul_le_mul_of_nonneg_left h2 (C.sg_nonneg k)
    calc ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
        = C.sg k * (‖C.U ω k‖ * ‖C.V ω k‖) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (C.sg_nonneg k), mul_assoc]
      _ ≤ C.sg k * ((‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2) := this
      _ = C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by ring
  calc ‖C.Rq ω‖ ≤ ∑ k, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖ := norm_sum_le _ _
    _ ≤ ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = C.Tq ω / 2 := by rw [← Finset.sum_div]; rfl

/-! #### Elementary consequences of the data -/

theorem co_ne_of_index_ne {k m : κ} (hm : m ≠ k) (b b' : Bool) : C.co m b' ≠ C.co k b :=
  fun hh => hm (congrArg Prod.fst (C.co_inj (a₁ := (m, b')) (a₂ := (k, b)) hh))

theorem co_false_ne_co_true (k m : κ) : C.co m false ≠ C.co k true := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, false)) (a₂ := (k, true)) hh)

theorem co_true_ne_co_false (k m : κ) : C.co m true ≠ C.co k false := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, true)) (a₂ := (k, false)) hh)

/-- **Row independence in the form used**: moving a coordinate of the row does not move `B`. -/
theorem B_update (ω : Sizes.SeqΩ d) (k : κ) (b : Bool) (t : ℝ) :
    C.B (Function.update ω (C.co k b) t) = C.B ω := by
  refine C.B_free _ _ fun c hc => ?_
  have hne : c ≠ C.co k b := by
    rintro rfl
    exact C.Ifree_free k b hc
  exact Function.update_of_ne hne _ _

theorem tameB (k l : κ) : Tame d (fun ω => C.B ω k l) :=
  Tame.ofBdd (C.B_cont k l)
    ⟨C.Ifree, fun ω ω' h => congrFun (congrFun (C.B_free ω ω' h) k) l⟩
    (fun ω => C.B_bdd ω k l)

theorem tameh (k : κ) : Tame d (fun ω => C.h ω k) :=
  (Tame.const (d := d) (C.r : ℂ)).mul
    ((Tame.coord (C.co k true)).add
      ((Tame.const (d := d) ((C.eps k : ℂ) * Complex.I)).mul (Tame.coord (C.co k false))))

theorem tameU (k : κ) : Tame d (fun ω => C.U ω k) :=
  Tame.sum _ fun l _ => (C.tameB k l).mul (C.tameh l).conj

theorem tameV (k : κ) : Tame d (fun ω => C.V ω k) :=
  Tame.sum _ fun m _ => (C.tameh m).mul (C.tameB m k)

theorem tamecen : Tame d C.cen :=
  Tame.sum _ fun k _ => (Tame.const (d := d) (C.sg k : ℂ)).mul (C.tameB k k)

theorem tamechaos : Tame d C.chaos :=
  (Tame.sum _ fun k _ => Tame.sum _ fun l _ =>
    ((C.tameh k).mul (C.tameB k l)).mul (C.tameh l).conj).sub C.tamecen

theorem tamedA (k : κ) : Tame d (fun ω => C.dA ω k) :=
  (Tame.const (d := d) (C.r : ℂ)).mul ((C.tameU k).add (C.tameV k))

theorem tamedB (k : κ) : Tame d (fun ω => C.dB ω k) :=
  (Tame.const (d := d) ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)).mul
    ((C.tameU k).sub (C.tameV k))

/-! #### The coordinate derivatives -/

/-- `∂ h_m / ∂ ω_{co k tt}`. -/
noncomputable def delA (k m : κ) : ℂ := if m = k then (C.r : ℂ) else 0

/-- `∂ h_m / ∂ ω_{co k ff}`. -/
noncomputable def delB (k m : κ) : ℂ :=
  if m = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0

theorem conj_delA (k m : κ) : (starRingEnd ℂ) (C.delA k m) = C.delA k m := by
  unfold delA; split_ifs <;> simp

theorem conj_delB (k m : κ) : (starRingEnd ℂ) (C.delB k m) = -C.delB k m := by
  unfold delB; split_ifs <;> simp

theorem hasDerivAt_conj' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) f') t :=
  (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

theorem hasDerivAt_ofReal_id (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

theorem hasDerivAt_h_true (k m : κ) (ω : Sizes.SeqΩ d) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m) (C.delA k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m true) s) m
        = (C.r : ℂ) * ((s : ℂ) + ((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_false_ne_co_true m m)]
    simp only [e]
    have h1 := (hasDerivAt_ofReal_id s₀).add_const
      (((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ))
    simpa [delA] using HasDerivAt.const_mul (C.r : ℂ) h1
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k true) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delA, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem hasDerivAt_h_false (k m : κ) (ω : Sizes.SeqΩ d) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m) (C.delB k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m false) s) m
        = (C.r : ℂ) * ((ω (C.co m true) : ℂ) + ((C.eps m : ℂ) * Complex.I) * (s : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_true_ne_co_false m m)]
    simp only [e]
    have h1 := HasDerivAt.const_mul ((C.eps m : ℂ) * Complex.I) (hasDerivAt_ofReal_id s₀)
    have h2 := h1.const_add ((ω (C.co m true) : ℂ))
    have := HasDerivAt.const_mul (C.r : ℂ) h2
    simpa [delB, mul_assoc] using this
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k false) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delB, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem cen_update (ω : Sizes.SeqΩ d) (k : κ) (b : Bool) (t : ℝ) :
    C.cen (Function.update ω (C.co k b) t) = C.cen ω := by
  unfold cen
  exact Finset.sum_congr rfl fun m _ => by rw [C.B_update ω k b t]

theorem sum_ite_mul_left {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ m, (if m = k then a else 0) * F m = a * F k := by
  have e : ∀ m : κ, (if m = k then a else 0) * F m = if m = k then a * F m else 0 := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun m _ => e m,
    Finset.sum_ite_eq' Finset.univ k fun m => a * F m]
  simp

theorem sum_mul_ite_right {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ l, F l * (if l = k then a else 0) = F k * a := by
  have e : ∀ l : κ, F l * (if l = k then a else 0) = if l = k then F l * a else 0 := by
    intro l; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => e l,
    Finset.sum_ite_eq' Finset.univ k fun l => F l * a]
  simp

omit [DecidableEq κ] in
theorem sum_mul_const (F : κ → ℂ) (a : ℂ) : ∑ m, F m * a = (∑ m, F m) * a :=
  (Finset.sum_mul _ _ _).symm

/-- The value of the derivative of the chaos along the real tag of the row index `k`. -/
theorem sum_delA_eq (k : κ) (ω : Sizes.SeqΩ d) :
    (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l))) = C.dA ω k := by
  have e1 : ∀ m : κ, ∑ l, C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delA k m * C.U ω m := by
    intro m
    show _ = C.delA k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
      = (C.h ω m * C.B ω m k) * (C.r : ℂ) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = (C.h ω m * C.B ω m l) * (if l = k then (C.r : ℂ) else 0) := fun l => by
      rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delA k m * C.U ω m = (C.r : ℂ) * C.U ω k := by
    have e : ∀ m : κ, C.delA k m * C.U ω m = (if m = k then (C.r : ℂ) else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (C.r : ℂ) = (C.r : ℂ) * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (C.r : ℂ) = _
    ring
  calc (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
      = ∑ m, (C.delA k m * C.U ω m + (C.h ω m * C.B ω m k) * (C.r : ℂ)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = (C.r : ℂ) * C.U ω k + (C.r : ℂ) * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dA ω k := by unfold dA; ring

/-- The value of the derivative of the chaos along the imaginary tag of the row index `k`. -/
theorem sum_delB_eq (k : κ) (ω : Sizes.SeqΩ d) :
    (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l))) = C.dB ω k := by
  set a : ℂ := (C.r : ℂ) * (C.eps k : ℂ) * Complex.I with ha
  have e1 : ∀ m : κ, ∑ l, C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delB k m * C.U ω m := by
    intro m
    show _ = C.delB k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = (C.h ω m * C.B ω m k) * (-a) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = (C.h ω m * C.B ω m l) * (if l = k then -a else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp [ha]
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delB k m * C.U ω m = a * C.U ω k := by
    have e : ∀ m : κ, C.delB k m * C.U ω m = (if m = k then a else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (-a) = -a * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (-a) = _
    ring
  calc (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
      = ∑ m, (C.delB k m * C.U ω m + (C.h ω m * C.B ω m k) * (-a)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = a * C.U ω k + -a * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dB ω k := by unfold dB; rw [ha]; ring

/-- **`∂ Q / ∂ ω_{co k tt} = dA`.** -/
theorem hasDerivAt_chaos_true (k : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k true) s))
      (C.dA ω k) (ω (C.co k true)) := by
  have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m *
          C.B (Function.update ω (C.co k true) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro m l
    have h1 := C.hasDerivAt_h_true k m ω (ω (C.co k true))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l) 0
        (ω (C.co k true)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k true s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k true) s) m *
        C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
    (A' := fun m => ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) 0
      (ω (C.co k true)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k true s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delA_eq k ω] at this
  exact this

/-- **`∂ Q / ∂ ω_{co k ff} = dB`.** -/
theorem hasDerivAt_chaos_false (k : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k false) s))
      (C.dB ω k) (ω (C.co k false)) := by
  have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m *
          C.B (Function.update ω (C.co k false) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro m l
    have h1 := C.hasDerivAt_h_false k m ω (ω (C.co k false))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l) 0
        (ω (C.co k false)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k false s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k false) s) m *
        C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
    (A' := fun m => ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) 0
      (ω (C.co k false)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k false s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delB_eq k ω] at this
  exact this

/-! #### The derivatives of `U`, `V`, `dA`, `dB` -/

theorem hasDerivAt_B_const (k : κ) (b : Bool) (m l : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) 0 (ω (C.co k b)) := by
  have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) = fun _ => C.B ω m l := by
    funext s; rw [C.B_update ω k b s]
  rw [hfun]; exact hasDerivAt_const _ _

theorem hasDerivAt_U_true (k m : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k true) s) m)
      (C.B ω m k * (C.r : ℂ)) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k true m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delA k l) = C.B ω m k * (C.r : ℂ) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = C.B ω m l * (if l = k then (C.r : ℂ) else 0) := fun l => by rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_true (k m : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k true) s) m)
      ((C.r : ℂ) * C.B ω k m) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) j *
        C.B (Function.update ω (C.co k true) s) j m)
      (C.delA k j * C.B ω j m) (ω (C.co k true)) := by
    intro j
    have h1 := C.hasDerivAt_h_true k j ω (ω (C.co k true))
    have h2 := C.hasDerivAt_B_const k true j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delA k j * C.B ω j m = (C.r : ℂ) * C.B ω k m := by
    have e : ∀ j : κ, C.delA k j * C.B ω j m = (if j = k then (C.r : ℂ) else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_U_false (k m : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k false) s) m)
      (C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k false m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = C.B ω m l * (if l = k then -((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_false (k m : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k false) s) m)
      (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) j *
        C.B (Function.update ω (C.co k false) s) j m)
      (C.delB k j * C.B ω j m) (ω (C.co k false)) := by
    intro j
    have h1 := C.hasDerivAt_h_false k j ω (ω (C.co k false))
    have h2 := C.hasDerivAt_B_const k false j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delB k j * C.B ω j m
      = ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m := by
    have e : ∀ j : κ, C.delB k j * C.B ω j m
        = (if j = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_dA_true (k : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.dA (Function.update ω (C.co k true) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k true)) := by
  have hU := C.hasDerivAt_U_true k k ω
  have hV := C.hasDerivAt_V_true k k ω
  have := HasDerivAt.const_mul (C.r : ℂ) (hU.add hV)
  have he : (C.r : ℂ) * (C.B ω k k * (C.r : ℂ) + (C.r : ℂ) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by ring
  rw [he] at this
  exact this

theorem hasDerivAt_dB_false (k : κ) (ω : Sizes.SeqΩ d) :
    HasDerivAt (fun s : ℝ => C.dB (Function.update ω (C.co k false) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k false)) := by
  have hU := C.hasDerivAt_U_false k k ω
  have hV := C.hasDerivAt_V_false k k ω
  have hd := HasDerivAt.const_mul ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) (hU.sub hV)
  have hes : ((C.eps k : ℂ)) ^ 2 = 1 := by
    have := C.eps_sq k
    have : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [this]
    push_cast at this
    exact this
  have he : ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) *
      (C.B ω k k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))
        - ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-2 * (C.r : ℂ) ^ 2 * C.B ω k k * (C.eps k : ℂ) ^ 2) * hI
      + (2 * (C.r : ℂ) ^ 2 * C.B ω k k) * hes
  rw [he] at hd
  exact hd

/-! #### The Euler identity -/

theorem conj_h (ω : Sizes.SeqΩ d) (k : κ) : (starRingEnd ℂ) (C.h ω k)
    = (C.r : ℂ) * ((ω (C.co k true) : ℂ)
      - ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * _) = _
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem coord_mul_dA_add_dB (ω : Sizes.SeqΩ d) (k : κ) :
    (ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k
      = C.h ω k * C.U ω k + (starRingEnd ℂ) (C.h ω k) * C.V ω k := by
  rw [C.conj_h ω k]
  show _ = ((C.r : ℂ) * _) * _ + _
  unfold dA dB
  ring

/-- **Euler's identity for the chaos**: `∑_α ω_α ∂_α Q = 2 (Q + ∑_k σ_k B_{kk})`. -/
theorem sum_coord_mul_deriv (ω : Sizes.SeqΩ d) :
    ∑ k, ((ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k)
      = 2 * (C.chaos ω + C.cen ω) := by
  have hD : C.chaos ω + C.cen ω
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    unfold chaos; ring
  have e1 : ∑ k, C.h ω k * C.U ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) :=
    Finset.sum_congr rfl fun k _ => by
      show C.h ω k * (∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  have e2 : ∑ k, (starRingEnd ℂ) (C.h ω k) * C.V ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    have step : ∀ k : κ, (starRingEnd ℂ) (C.h ω k) * C.V ω k
        = ∑ m, C.h ω m * C.B ω m k * (starRingEnd ℂ) (C.h ω k) := by
      intro k
      show (starRingEnd ℂ) (C.h ω k) * (∑ m, C.h ω m * C.B ω m k) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun k _ => step k]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun k _ => C.coord_mul_dA_add_dB ω k, Finset.sum_add_distrib, e1, e2,
    hD]
  ring

end RowChaos

end RBM.Green
