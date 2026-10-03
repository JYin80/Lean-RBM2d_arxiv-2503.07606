/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Molecule
import RBM2D.Loop.PureLoop
import RBM2D.Loop.SumZeroWard
import RBM2D.Loop.PropHyp

/-!
# `ML:Kbound+pi` at `π = ∅`: `(spwow3)` and `(eq:bcal_k_pi)`

Paper: Lemma `ML:Kbound+pi`, `(eq:bcal_k_pi)` and `(spwow3)`, for `π = ∅`.

Theorems (namespace `RBM.KLoop`):

* `Kpi_empty_spwow3At_prec` : `(spwow3)` at a general erased index `p` with `σ'_p ≠ σ'_{p+1}`;
* `Kpi_empty_prec` : `(eq:bcal_k_pi)` at `π = ∅` (the special case `π = ∅` only).

Both are conditional on `Prop5Hyp κ c` and `Prop6Hyp κ` (properties 5–6 of
`lem_propTH`).  Method: the proof of `(spwow3)` of the paper, redone in `d = 2` at a general
index.  Case (i), a short boundary edge `j ≠ p`: its decay and the short range of
`Σ^{(∅)}` (`SigmaPi_empty_shortRange_prec`).  Case (ii), all edges long: the sum over the fibre
`{d_p = u}` is symmetrised by the reflection `d ↦ 2u - d` (`SigmaPi_empty_symm` plus
translation invariance), which removes the odd first-order terms; the zeroth-order term is the
slice sum (`SumZero_sum_slice`, `SigmaPi_alt_sumZero_le`, conjugation for `-σ^{(alt)}`);
second-order terms use `(prop:BD1)`, `(prop:BD2)`.  No rotation covariance of `Σ^{(∅)}` is
used.  The case analysis is written directly for `Z_L²` (sums over `Z_L²`, `sum_exp_le`,
`sum_inv_sq_le`), and no `d = 1` bound of `f₁`, `f₂` is used; instead of expanding every
factor in the three-term split `f = f₀ + f₁ + f₂` of the paper (proof of `(spwow3)`), the
symmetrised product is expanded binomially around the `V = ∅` term.  Several helpers are
private copies of private `RBM2D` lemmas: section 3 is the section `Gap` of
`RBM2D/Loop/PureLoop.lean`; `zdist_neg`, `zdist2_neg` follow `PureLoop.lean`; the scale
facts of section 4 follow the private lemmas of `RBM2D/Loop/Molecule.lean`;
`mSig_mul_ne` follows `RBM2D/Loop/Kcal.lean`.
Every helper is `private`.
-/

namespace RBM.KLoop

open Finset

/-! ## 1. Distances and lattice sums -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, zdist_neg]

private theorem le_maxDist {n : ℕ} (d : Fin n → Z2 L) (i j : Fin n) :
    zdist2 L (d i - d j) ≤ maxDist L d :=
  Finset.le_sup (f := fun q : Fin n × Fin n => zdist2 L (d q.1 - d q.2)) (mem_univ (i, j))

end Dist

section Elementary

/-- `1 + D ≤ (1 + μ⁻¹) e^{μ D}`. -/
private theorem one_add_le_exp {μ D : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D) :
    1 + D ≤ (1 + μ⁻¹) * Real.exp (μ * D) := by
  have h := Real.add_one_le_exp (μ * D)
  have h1 : 0 ≤ 1 + μ⁻¹ := by positivity
  have h2 : (1 + μ⁻¹) * (μ * D + 1) = μ * D + 1 + D + μ⁻¹ := by
    field_simp
    ring
  have h3 : 0 ≤ μ * D := by positivity
  have h4 : 0 ≤ μ⁻¹ := by positivity
  calc 1 + D ≤ (1 + μ⁻¹) * (μ * D + 1) := by rw [h2]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left h h1

/-- `e^{-μ x} ≤ (1 + 4/μ²) (x² + 1)⁻¹` for `x ≥ 0`. -/
private theorem exp_le_inv_sq {μ x : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) :
    Real.exp (-(μ * x)) ≤ (1 + 4 / μ ^ 2) * (x ^ 2 + 1)⁻¹ := by
  have h1 := Real.add_one_le_exp (μ * x / 2)
  have hy : 0 ≤ μ * x / 2 := by positivity
  have hsq : Real.exp (μ * x) = Real.exp (μ * x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h2 : 1 + (μ * x / 2) ^ 2 ≤ Real.exp (μ * x) := by
    rw [hsq]
    nlinarith [sq_nonneg (μ * x / 2)]
  have h3 : x ^ 2 + 1 ≤ (1 + 4 / μ ^ 2) * (1 + (μ * x / 2) ^ 2) := by
    have : (1 + 4 / μ ^ 2) * (1 + (μ * x / 2) ^ 2) = 1 + x ^ 2 + 4 / μ ^ 2 + μ ^ 2 * x ^ 2 / 4 := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ 4 / μ ^ 2 := by positivity
    nlinarith [sq_nonneg (μ * x)]
  have hx1 : 0 < x ^ 2 + 1 := by positivity
  have hC : 0 ≤ 1 + 4 / μ ^ 2 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hx1, ← div_eq_inv_mul,
    div_le_iff₀ (Real.exp_pos _)]
  calc x ^ 2 + 1 ≤ (1 + 4 / μ ^ 2) * (1 + (μ * x / 2) ^ 2) := h3
    _ ≤ (1 + 4 / μ ^ 2) * Real.exp (μ * x) := mul_le_mul_of_nonneg_left h2 hC

/-- `((x+1)⁻¹ + Y)((x'+1)⁻¹ + Y) ≤ (x²+1)⁻¹ + (x'²+1)⁻¹ + 2Y²`. -/
private theorem pair_le {x x' Y : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    ((x + 1)⁻¹ + Y) * ((x' + 1)⁻¹ + Y) ≤ (x ^ 2 + 1)⁻¹ + (x' ^ 2 + 1)⁻¹ + 2 * Y ^ 2 := by
  have ha : (x + 1)⁻¹ ^ 2 ≤ (x ^ 2 + 1)⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hb : (x' + 1)⁻¹ ^ 2 ≤ (x' ^ 2 + 1)⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith)
  nlinarith [sq_nonneg ((x + 1)⁻¹ - (x' + 1)⁻¹), sq_nonneg ((x + 1)⁻¹ - Y),
    sq_nonneg ((x' + 1)⁻¹ - Y)]

/-- `∏_{i ∈ s} ‖f i‖ ≤ M^{#s}`. -/
private theorem prod_norm_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ) {M : ℝ}
    (h : ∀ i ∈ s, ‖f i‖ ≤ M) : ∏ i ∈ s, ‖f i‖ ≤ M ^ s.card := by
  calc ∏ i ∈ s, ‖f i‖ ≤ ∏ _i ∈ s, M := prod_le_prod₀ (fun _ _ => norm_nonneg _) h
    _ = M ^ s.card := prod_const M

end Elementary

/-! ## 2. Sums over the fibre `{d : d_p = u}` with exponential weights -/

section Fiber

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `Σ_{d : d_p = u} e^{-λ maxDist(d)} ≤ ((1 + 2k/λ)²)^k`: `maxDist d ≥ |d_i - u|` for each `i`. -/
private theorem fiber_exp_le (p : Fin k) (u : Z2 L) {lam : ℝ} (hlam : 0 < lam) :
    ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Real.exp (-(lam * (maxDist L d : ℝ)))
      ≤ ((1 + 2 / (lam / k)) ^ 2) ^ k := by
  have hk : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  set g : Z2 L → ℝ := fun x => Real.exp (-(lam / k * (zdist2 L (u - x) : ℝ))) with hg
  have hpt : ∀ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
      Real.exp (-(lam * (maxDist L d : ℝ))) ≤ ∏ i, g (d i) := by
    intro d hd
    have hdp : d p = u := (mem_filter.1 hd).2
    simp only [hg]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hle : ∀ i, (zdist2 L (u - d i) : ℝ) ≤ maxDist L d := by
      intro i; rw [← hdp]; exact_mod_cast le_maxDist d p i
    have hsum : ∑ i, (lam / k * (zdist2 L (u - d i) : ℝ)) ≤ lam * maxDist L d := by
      calc ∑ i, (lam / k * (zdist2 L (u - d i) : ℝ))
          ≤ ∑ _i : Fin k, (lam / k * (maxDist L d : ℝ)) :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (by positivity)
        _ = lam * maxDist L d := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    rw [sum_neg_distrib]
    linarith
  have hg0 : ∀ x, 0 ≤ g x := fun x => (Real.exp_pos _).le
  calc _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u), ∏ i, g (d i) :=
        sum_le_sum hpt
    _ ≤ ∑ d : Fin k → Z2 L, ∏ i, g (d i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => prod_nonneg fun _ _ => hg0 _)
    _ = (∑ x, g x) ^ k := by
        have h := Finset.prod_univ_sum (fun _ : Fin k => (univ : Finset (Z2 L)))
          (fun _ x => g x)
        rw [Fintype.piFinset_univ] at h
        rw [← h, prod_const, card_univ, Fintype.card_fin]
    _ ≤ ((1 + 2 / (lam / k)) ^ 2) ^ k := by
        refine pow_le_pow_left₀ (sum_nonneg fun _ _ => hg0 _) ?_ k
        have := sum_exp_le L (lam / k) (by positivity) u
        simpa [hg] using this

/-- The fibre sum with a polynomial weight `(1 + maxDist d)^m`. -/
private theorem fiber_exp_pow_le (p : Fin k) (u : Z2 L) {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Real.exp (-(lam * (maxDist L d : ℝ))) * (1 + (maxDist L d : ℝ)) ^ m
      ≤ (1 + (lam / (2 * (m + 1)))⁻¹) ^ m * ((1 + 2 / (lam / 2 / k)) ^ 2) ^ k := by
  set μ := lam / (2 * (m + 1)) with hμ
  have hμ0 : 0 < μ := by positivity
  have hC : 0 ≤ (1 + μ⁻¹) ^ m := by positivity
  have hpt : ∀ d : Fin k → Z2 L,
      Real.exp (-(lam * (maxDist L d : ℝ))) * (1 + (maxDist L d : ℝ)) ^ m
        ≤ (1 + μ⁻¹) ^ m * Real.exp (-(lam / 2 * (maxDist L d : ℝ))) := by
    intro d
    set D : ℝ := (maxDist L d : ℝ)
    have hD : 0 ≤ D := Nat.cast_nonneg _
    have h1 : (1 + D) ^ m ≤ ((1 + μ⁻¹) * Real.exp (μ * D)) ^ m :=
      pow_le_pow_left₀ (by positivity) (one_add_le_exp hμ0 hD) m
    have h2 : ((1 + μ⁻¹) * Real.exp (μ * D)) ^ m = (1 + μ⁻¹) ^ m * Real.exp (m * μ * D) := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (-(lam * D)) * Real.exp (m * μ * D) ≤ Real.exp (-(lam / 2 * D)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hmμ : (m : ℝ) * μ ≤ lam / 2 := by
        rw [hμ]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        rw [show (m : ℝ) * (lam / (2 * (m + 1))) = lam / 2 * (m / (m + 1)) by field_simp]
        have : (m : ℝ) / (m + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith
      nlinarith
    calc Real.exp (-(lam * D)) * (1 + D) ^ m
        ≤ Real.exp (-(lam * D)) * ((1 + μ⁻¹) ^ m * Real.exp (m * μ * D)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = (1 + μ⁻¹) ^ m * (Real.exp (-(lam * D)) * Real.exp (m * μ * D)) := by ring
      _ ≤ (1 + μ⁻¹) ^ m * Real.exp (-(lam / 2 * D)) := mul_le_mul_of_nonneg_left h3 hC
  calc _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        (1 + μ⁻¹) ^ m * Real.exp (-(lam / 2 * (maxDist L d : ℝ))) := sum_le_sum fun d _ => hpt d
    _ = (1 + μ⁻¹) ^ m * ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Real.exp (-(lam / 2 * (maxDist L d : ℝ))) := by rw [mul_sum]
    _ ≤ (1 + μ⁻¹) ^ m * ((1 + 2 / (lam / 2 / k)) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left (fiber_exp_le p u (by positivity)) hC

end Fiber

/-! ## 3. The bulk gap and the short-edge bound

These lemmas are also proved (privately) in the section `Gap` of
`RBM2D/Loop/PureLoop.lean`. -/

section Gap

private theorem gapK_nonneg (κ : ℝ) : 0 ≤ gapK κ :=
  le_min zero_le_one (Real.sqrt_nonneg _)

private theorem gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ :=
  lt_min one_pos (Real.sqrt_pos.2 (by nlinarith))

private theorem gapK_sq_le {κ : ℝ} (hκ2 : κ ≤ 2) (hκ : 0 < κ) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ κ * (4 - κ) / 2 := by nlinarith
  calc gapK κ ^ 2 ≤ (Real.sqrt (κ * (4 - κ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (gapK_nonneg κ) (min_le_right _ _) 2
    _ = κ * (4 - κ) / 2 := Real.sq_sqrt h0

/-- The bulk gap: `c_κ ≤ |1 - t m²|` for `t ≥ 0`, `|E| ≤ 2 - κ` (`m = m^{(E)}`). -/
private theorem gap_le_norm {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ) (ht : 0 ≤ t) :
    gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ := by
  have hE2 : |E| ≤ 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set s := Real.sqrt (4 - E ^ 2) with hs_def
  have hs : s ^ 2 = 4 - E ^ 2 := Gauss.spectralM_sqrt_sq hE2
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him : (Gauss.spectralM E).im = s / 2 := Gauss.spectralM_im E
  have hzre : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).re
      = 1 - t * ((-E / 2) ^ 2 - (s / 2) ^ 2) := by
    simp [pow_two, Complex.mul_re, hre, him]
  have hzim : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).im
      = -(t * (2 * (-E / 2) * (s / 2))) := by
    simp only [pow_two, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub, hre, him]
    ring
  have hsq : ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ ^ 2
      = 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    linear_combination (t / 2 + t ^ 2 * (8 + (s ^ 2 - (4 - E ^ 2))) / 16) * hs
  have hg0 := gapK_nonneg κ
  have hg1 : gapK κ ^ 2 ≤ 1 := pow_le_one₀ hg0 (gapK_le_one κ)
  have hg2 := gapK_sq_le hκ2 hκ
  have hmain : gapK κ ^ 2 ≤ 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    by_cases hc : E ^ 2 ≤ 2
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hc), sq_nonneg t]
    · have hc := not_le.1 hc
      have hy : E ^ 2 ≤ (2 - κ) ^ 2 := by
        rw [← sq_abs E]
        exact pow_le_pow_left₀ (abs_nonneg E) hE 2
      have hk4 : 0 ≤ 4 - (2 - κ) ^ 2 := by nlinarith
      have h1 : κ * (4 - κ) / 2 ≤ E ^ 2 * (4 - E ^ 2) / 4 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hy) (show 0 ≤ E ^ 2 + (2 - κ) ^ 2 - 4 by nlinarith),
          mul_nonneg hk4 (show 0 ≤ (2 - κ) ^ 2 - 2 by nlinarith)]
      nlinarith [sq_nonneg (t - (E ^ 2 / 2 - 1))]
  by_contra hlt
  have hlt := not_le.1 hlt
  have := norm_nonneg ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2)
  nlinarith

private theorem gap_le_norm_mSig {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ)
    (ht : 0 ≤ t) (s : Bool) : gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * mSig E s ^ 2‖ := by
  cases s
  · have h := gap_le_norm hκ hE ht
    have : (1 : ℂ) - (t : ℂ) * mSig E false ^ 2
        = (starRingEnd ℂ) ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2) := by
      simp [mSig]
    rw [this, Complex.norm_conj]
    exact h
  · simpa [mSig] using gap_le_norm hκ hE ht

/-- The right side of `Prop5Hyp` is at most `c_κ⁻¹ e^{-c √c_κ |x-y|}`:
`ℓ̂ ≤ c_κ^{-1/2}` and `|1-ξ| ℓ̂² ≥ c_κ`. -/
private theorem edge_rhs_le {L : ℕ} [NeZero L] {ξ : ℂ} {g c d : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hgξ : g ≤ ‖(1 : ℂ) - ξ‖) (hc : 0 < c) (hd : 0 ≤ d) (hL : 3 ≤ L) :
    Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2)
      ≤ g⁻¹ * Real.exp (-(c * Real.sqrt g * d)) := by
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hκξ : Real.sqrt g ≤ kappa ξ := Real.sqrt_le_sqrt hgξ
  have hκpos : 0 < kappa ξ := lt_of_lt_of_le hsg hκξ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hℓpos : 0 < ellhat L ξ := lt_min (inv_pos.2 hκpos) (by linarith)
  have hℓle : ellhat L ξ ≤ (Real.sqrt g)⁻¹ := (min_le_left _ _).trans (inv_anti₀ hsg hκξ)
  have hinv : Real.sqrt g * ellhat L ξ ≤ 1 := by
    calc Real.sqrt g * ellhat L ξ ≤ Real.sqrt g * (Real.sqrt g)⁻¹ :=
          mul_le_mul_of_nonneg_left hℓle hsg.le
      _ = 1 := mul_inv_cancel₀ hsg.ne'
  have hexp : c * Real.sqrt g * d ≤ c * d / ellhat L ξ := by
    rw [le_div_iff₀ hℓpos]
    have : 0 ≤ c * d := by positivity
    nlinarith
  have hkl : Real.sqrt g ≤ kappa ξ * ellhat L ξ := by
    rcases le_total (kappa ξ)⁻¹ (L : ℝ) with h | h
    · have : ellhat L ξ = (kappa ξ)⁻¹ := min_eq_left h
      rw [this, mul_inv_cancel₀ hκpos.ne']
      exact Real.sqrt_le_one.2 hg1 |>.trans_eq rfl
    · have : ellhat L ξ = L := min_eq_right h
      rw [this]
      nlinarith
  have hden : g ≤ ‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2 := by
    rw [← kappa_sq, ← mul_pow]
    calc g = Real.sqrt g ^ 2 := (Real.sq_sqrt hg.le).symm
      _ ≤ _ := pow_le_pow_left₀ hsg.le hkl 2
  have hden' : 0 < ‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2 := lt_of_lt_of_le hg hden
  calc Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2)
      ≤ Real.exp (-(c * Real.sqrt g * d)) / g := by
        refine div_le_div₀ (Real.exp_pos _).le ?_ hg hden
        apply Real.exp_le_exp.2
        rw [neg_div]
        linarith
    _ = g⁻¹ * Real.exp (-(c * Real.sqrt g * d)) := by rw [div_eq_inv_mul]

/-- **The edge bound from `Prop5Hyp`**: for every `τ > 0`, eventually in `N`, all entries of the
edge matrices `Θ_{t m(s)²}` (`s = ±`) are at most `N^τ c_κ⁻¹ e^{-c √c_κ |x-y|_L}`. -/
private theorem prop5_edge {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hP : Prop5Hyp κ c) {τ : ℝ}
    (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p : Par κ N) (s : Bool) (x y : Z2 p.L),
      ‖Theta p.L ((p.t : ℂ) * (mSig p.E s * mSig p.E s)) x y‖ ≤
        (N : ℝ) ^ τ * ((gapK κ)⁻¹ *
          Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ)))) := by
  filter_upwards [hP τ hτ] with N hN p s x y
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg p.E, p.hE]
  have hg := gapK_pos hκ hκ2
  have hgξ := gap_le_norm_mSig hκ p.hE p.ht0 s
  have h := hN ⟨p, if s then 0 else 1, x, y⟩
  have hξ : xiSet p.E p.t (if s then 0 else 1) = (p.t : ℂ) * mSig p.E s ^ 2 := by
    cases s <;> simp [xiSet]
  simp only [hξ] at h
  rw [← sq] at *
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) τ)
  exact edge_rhs_le hg (gapK_le_one κ) hgξ hc (Nat.cast_nonneg _) p.hL

end Gap

/-! ## 4. The scales `η_t`, `ℓ_t`, `X_t` -/

section Scales

variable {L : ℕ} [NeZero L]

private theorem etaT_eq' (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem im_nonneg' (E : ℝ) : 0 ≤ (Gauss.spectralM E).im := by
  rw [Gauss.spectralM_im]; positivity

private theorem im_le_one' (E : ℝ) : (Gauss.spectralM E).im ≤ 1 := by
  rw [Gauss.spectralM_im]
  have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
  linarith

private theorem etaT_pos' {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) : 0 < etaT E t := by
  rw [etaT_eq']
  have := Gauss.spectralM_im_pos hE
  have : 0 < 1 - t := by linarith
  positivity

private theorem etaT_le' {E t : ℝ} (ht1 : t < 1) : etaT E t ≤ 1 - t := by
  rw [etaT_eq']
  have h1 := im_le_one' E
  have h0 := im_nonneg' E
  have : 0 ≤ 1 - t := by linarith
  nlinarith

private theorem norm_one_sub_ofReal' {t : ℝ} (ht1 : t < 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

private theorem one_le_ellT' (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ ellT L t := by
  rw [ellT, ellhat, kappa, norm_one_sub_ofReal' ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine le_min ((one_le_inv₀ hs0).2 hs1) ?_
  have : (3 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

/-- `X_t η_t = ℓ_t⁻²`. -/
private theorem Xt_mul_etaT {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) :
    Xt L E t * etaT E t = (ellT L t ^ 2)⁻¹ := by
  rw [Xt, mul_inv, mul_assoc, inv_mul_cancel₀ (etaT_pos' hE ht1).ne', mul_one]

/-- The right side of property 5 at `ξ = t` is at most `X_t`. -/
private theorem long_rhs_le (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    Real.exp (-(c * x) / ellhat L (t : ℂ)) / (‖(1 : ℂ) - (t : ℂ)‖ * ellhat L (t : ℂ) ^ 2)
      ≤ Xt L E t := by
  have hℓ : 1 ≤ ellhat L (t : ℂ) := one_le_ellT' hL ht0 ht1
  rw [norm_one_sub_ofReal' ht1]
  have h1t : 0 < 1 - t := by linarith
  have hη := etaT_pos' hE ht1
  have hden : 0 < (1 - t) * ellhat L (t : ℂ) ^ 2 := by positivity
  have hexp : Real.exp (-(c * x) / ellhat L (t : ℂ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
    have : 0 ≤ c * x := mul_nonneg hc hx
    linarith
  calc Real.exp (-(c * x) / ellhat L (t : ℂ)) / ((1 - t) * ellhat L (t : ℂ) ^ 2)
      ≤ 1 / ((1 - t) * ellhat L (t : ℂ) ^ 2) := div_le_div_of_nonneg_right hexp hden.le
    _ ≤ 1 / (etaT E t * ellhat L (t : ℂ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right (etaT_le' ht1) (sq_nonneg _))
    _ = Xt L E t := by rw [Xt, ellT, one_div, mul_comm]

/-- `Y := (ℓ_t² √(1-t))⁻¹ ≤ X_t`. -/
private theorem Y_le_Xt (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (ellT L t ^ 2 * Real.sqrt (1 - t))⁻¹ ≤ Xt L E t := by
  have hℓ := one_le_ellT' hL ht0 ht1
  have hη := etaT_pos' hE ht1
  have h1t : 0 ≤ 1 - t := by linarith
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hs : 1 - t ≤ Real.sqrt (1 - t) := by
    have := Real.mul_self_sqrt h1t
    nlinarith [Real.sqrt_nonneg (1 - t)]
  rw [Xt]
  refine inv_anti₀ (by positivity) ?_
  exact mul_le_mul_of_nonneg_left ((etaT_le' ht1).trans hs) (by positivity)

/-- `Y² ≤ η_t X_t²`. -/
private theorem Y_sq_le (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((ellT L t ^ 2 * Real.sqrt (1 - t))⁻¹) ^ 2 ≤ etaT E t * Xt L E t ^ 2 := by
  have hℓ := one_le_ellT' hL ht0 ht1
  have hη := etaT_pos' hE ht1
  have h1t : 0 < 1 - t := by linarith
  have e1 : ((ellT L t ^ 2 * Real.sqrt (1 - t))⁻¹) ^ 2 = ((ellT L t ^ 2) ^ 2 * (1 - t))⁻¹ := by
    rw [inv_pow, mul_pow, Real.sq_sqrt h1t.le]
  have e2 : etaT E t * Xt L E t ^ 2 = ((ellT L t ^ 2) ^ 2 * etaT E t)⁻¹ := by
    rw [Xt]
    field_simp
  rw [e1, e2]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (etaT_le' ht1) (by positivity))

end Scales

/-! ## 5. The inputs at one parameter point -/

/-- `m(s) m(s') = 1` for `s ≠ s'` (`|m| = 1`). -/
private theorem mSig_mul_ne {E : ℝ} (hE : |E| ≤ 2) {s s' : Bool} (h : s ≠ s') :
    mSig E s * mSig E s' = 1 := by
  have hm : Gauss.spectralM E * (starRingEnd ℂ) (Gauss.spectralM E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
    simp
  cases s <;> cases s' <;> simp_all [mSig, mul_comm]

/-- A long edge is `Θ_t`. -/
private theorem thetaEdge_long {L : ℕ} [NeZero L] {E t : ℝ} (hE : |E| ≤ 2) {s s' : Bool}
    (h : s ≠ s') : thetaEdge L (mSig E) t s s' = Theta L (t : ℂ) := by
  rw [thetaEdge, mSig_mul_ne hE h, mul_one]

/-- The five input bounds at the parameter point `p`, with the factor `B` (`= N^τ'`). -/
private structure Good {κ : ℝ} {N : ℕ} (p : Par κ N) (k : ℕ) [NeZero k] (B c₁ κe G : ℝ) :
    Prop where
  sig : ∀ (σ : Fin k → Bool) (d : Fin k → Z2 p.L),
    ‖SigmaPi p.L (mSig p.E) p.t σ ∅ d‖ ≤ B * Real.exp (-(c₁ * (maxDist p.L d : ℝ)))
  short : ∀ (s : Bool) (x y : Z2 p.L),
    ‖thetaEdge p.L (mSig p.E) p.t s s x y‖ ≤
      B * G * Real.exp (-(κe * (zdist2 p.L (x - y) : ℝ)))
  long : ∀ x y : Z2 p.L, ‖Theta p.L (p.t : ℂ) x y‖ ≤ B * Xt p.L p.E p.t
  bd1 : ∀ a b s : Z2 p.L,
    ‖Theta p.L (p.t : ℂ) a b - Theta p.L (p.t : ℂ) a (b + s)‖ ≤
      B * ((zdist2 p.L s : ℝ) * (((zdist2 p.L (a - b) : ℝ) + 1)⁻¹ +
        (ellT p.L p.t ^ 2 * Real.sqrt (1 - p.t))⁻¹))
  bd2 : ∀ a b s : Z2 p.L,
    ‖2 * Theta p.L (p.t : ℂ) a b - Theta p.L (p.t : ℂ) a (b + s)
        - Theta p.L (p.t : ℂ) a (b - s)‖ ≤
      B * ((zdist2 p.L s : ℝ) ^ 2 * (((zdist2 p.L (a - b) : ℝ) ^ 2 + 1)⁻¹ +
        Xt p.L p.E p.t * etaT p.E p.t))

private theorem absE_lt {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (p : Par κ N) : |p.E| < 2 := by
  have := p.hE; linarith

/-- The inputs hold eventually, with `B = N^τ`. -/
private theorem good_eventually {k : ℕ} [NeZero k] (hk : 3 ≤ k) {κ c : ℝ} (hκ : 0 < κ)
    (hc : 0 < c) (h5 : Prop5Hyp κ c) (h6 : Prop6Hyp κ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p : Par κ N,
      Good p k ((N : ℝ) ^ τ) (c * Real.sqrt (gapK κ) / 2) (c * Real.sqrt (gapK κ))
        (gapK κ)⁻¹ := by
  filter_upwards [SigmaPi_empty_shortRange_prec k hk κ c hκ hc h5 τ hτ,
    prop5_edge hκ hc h5 hτ, h5 τ hτ, h6.1 τ hτ, h6.2 τ hτ] with N h1 h2 h3 h4 h5' p
  have hE := absE_lt hκ p
  have hξ : xiSet p.E p.t 2 = (p.t : ℂ) := by simp [xiSet]
  have hNτ : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
  have hn1 : ‖(1 : ℂ) - (p.t : ℂ)‖ = 1 - p.t := norm_one_sub_ofReal' p.ht1
  refine ⟨fun σ d => h1 ⟨p, σ, d⟩, fun s x y => ?_, fun x y => ?_, fun a b s => ?_,
    fun a b s => ?_⟩
  · refine (h2 p s x y).trans (le_of_eq ?_)
    ring
  · have h := h3 ⟨p, 2, x, y⟩
    simp only [hξ] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (long_rhs_le p.hL hE p.ht0 p.ht1 hc.le (Nat.cast_nonneg _)) hNτ)
  · have h := h4 ⟨p, 2, a, b, s⟩
    simp only [hξ, hn1] at h
    refine h.trans (le_of_eq ?_)
    simp only [ellT, div_eq_mul_inv]
    ring
  · have h := h5' ⟨p, 2, a, b, s⟩
    simp only [hξ] at h
    refine h.trans (le_of_eq ?_)
    rw [Xt_mul_etaT hE p.ht1]
    simp only [ellT, div_eq_mul_inv]
    ring

/-! ## 6. The deterministic bounds of the inner molecule -/

section Core

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- **Case (i)** (proof of `(spwow3)`): a boundary edge `j ≠ p` is short.  Its
decay and the short range of `Σ^{(∅)}` give `e^{-(c₁/2)|a_j - u|}`; every other edge is
`≤ B G X`. -/
private theorem core_short (hk : 3 ≤ k) (p j : Fin k) (hj : j ≠ p) (u : Z2 L)
    (a : Fin k → Z2 L) (Sg : (Fin k → Z2 L) → ℂ) (M : Fin k → Z2 L → Z2 L → ℂ)
    {B G X c₁ κe : ℝ} (hB : 1 ≤ B) (hG : 1 ≤ G) (hX : 1 ≤ X) (hc₁ : 0 < c₁) (hκe : c₁ ≤ κe)
    (hSg : ∀ d, ‖Sg d‖ ≤ B * Real.exp (-(c₁ * (maxDist L d : ℝ))))
    (hMj : ∀ x y, ‖M j x y‖ ≤ B * G * Real.exp (-(κe * (zdist2 L (x - y) : ℝ))))
    (hM : ∀ i x y, ‖M i x y‖ ≤ B * G * X) :
    ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖
      ≤ (1 + 4 / (c₁ / 2) ^ 2) * ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k * (B * G) ^ k *
          X ^ (k - 2) * ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ := by
  have hjS : j ∈ univ.erase p := mem_erase.2 ⟨hj, mem_univ _⟩
  have hcard : ((univ.erase p).erase j).card = k - 2 := by
    rw [card_erase_of_mem hjS, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  set x : ℝ := (zdist2 L (a j - u) : ℝ) with hxdef
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hBG : 0 ≤ B * G := mul_nonneg hB0 hG0
  have hpowBG : (B * G) ^ k = (B * G) ^ (k - 2) * (B * G) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpt : ∀ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
      ‖Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖ ≤
        (B * G) ^ k * X ^ (k - 2) *
          (Real.exp (-(c₁ / 2 * x)) * Real.exp (-(c₁ / 2 * (maxDist L d : ℝ)))) := by
    intro d hd
    have hdp : d p = u := (mem_filter.1 hd).2
    rw [norm_mul, norm_prod, ← mul_prod_erase (univ.erase p) _ hjS]
    have hrest : ∏ i ∈ (univ.erase p).erase j, ‖M i (a i) (d i)‖ ≤ (B * G * X) ^ (k - 2) := by
      rw [← hcard]; exact prod_norm_le_pow _ _ fun i _ => hM i _ _
    set D : ℝ := (maxDist L d : ℝ)
    have hD0 : 0 ≤ D := Nat.cast_nonneg _
    have hDj : (zdist2 L (d j - u) : ℝ) ≤ D := by
      change ((zdist2 L (d j - u) : ℕ) : ℝ) ≤ ((maxDist L d : ℕ) : ℝ)
      rw [← hdp]; exact_mod_cast le_maxDist d j p
    have htri : x ≤ (zdist2 L (a j - d j) : ℝ) + zdist2 L (d j - u) := by
      have := zdist2_add_le L (a j - d j) (d j - u)
      rw [sub_add_sub_cancel] at this
      change ((zdist2 L (a j - u) : ℕ) : ℝ) ≤ _
      exact_mod_cast this
    have hexp : Real.exp (-(c₁ * D)) * Real.exp (-(κe * (zdist2 L (a j - d j) : ℝ))) ≤
        Real.exp (-(c₁ / 2 * x)) * Real.exp (-(c₁ / 2 * D)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h0 : (0 : ℝ) ≤ zdist2 L (a j - d j) := Nat.cast_nonneg _
      have h1 : c₁ * (zdist2 L (a j - d j) : ℝ) ≤ κe * (zdist2 L (a j - d j) : ℝ) :=
        mul_le_mul_of_nonneg_right hκe h0
      nlinarith
    have hE0 : 0 ≤ Real.exp (-(c₁ / 2 * x)) * Real.exp (-(c₁ / 2 * D)) := by positivity
    calc ‖Sg d‖ * (‖M j (a j) (d j)‖ * ∏ i ∈ (univ.erase p).erase j, ‖M i (a i) (d i)‖)
        ≤ (B * Real.exp (-(c₁ * D))) *
            ((B * G * Real.exp (-(κe * (zdist2 L (a j - d j) : ℝ)))) * (B * G * X) ^ (k - 2)) := by
          gcongr
          · exact hSg d
          · exact hMj _ _
      _ = (B * (B * G) * (B * G * X) ^ (k - 2)) *
            (Real.exp (-(c₁ * D)) * Real.exp (-(κe * (zdist2 L (a j - d j) : ℝ)))) := by ring
      _ ≤ ((B * G) ^ k * X ^ (k - 2)) *
            (Real.exp (-(c₁ / 2 * x)) * Real.exp (-(c₁ / 2 * D))) := by
          have hsc : B * (B * G) * (B * G * X) ^ (k - 2) ≤ (B * G) ^ k * X ^ (k - 2) := by
            rw [hpowBG, mul_pow]
            have h1 : B * (B * G) ≤ (B * G) ^ 2 := by nlinarith
            calc B * (B * G) * ((B * G) ^ (k - 2) * X ^ (k - 2))
                ≤ (B * G) ^ 2 * ((B * G) ^ (k - 2) * X ^ (k - 2)) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = (B * G) ^ (k - 2) * (B * G) ^ 2 * X ^ (k - 2) := by ring
          exact mul_le_mul hsc hexp (by positivity) (by positivity)
  have hK : 0 ≤ (B * G) ^ k * X ^ (k - 2) := by positivity
  calc _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        ‖Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u), (B * G) ^ k * X ^ (k - 2) *
          (Real.exp (-(c₁ / 2 * x)) * Real.exp (-(c₁ / 2 * (maxDist L d : ℝ)))) :=
        sum_le_sum hpt
    _ = (B * G) ^ k * X ^ (k - 2) * Real.exp (-(c₁ / 2 * x)) *
          ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
            Real.exp (-(c₁ / 2 * (maxDist L d : ℝ))) := by
        rw [mul_sum]; refine sum_congr rfl fun d _ => ?_; ring
    _ ≤ (B * G) ^ k * X ^ (k - 2) * ((1 + 4 / (c₁ / 2) ^ 2) * (x ^ 2 + 1)⁻¹) *
          ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k := by
        gcongr
        · exact exp_le_inv_sq (by positivity) hx0
        · exact fiber_exp_le p u (by positivity)
    _ = _ := by ring

omit [NeZero k] in
/-- A product over `V ∋ j, l` (`j ≠ l`) times a product over `S \ V`: two factors of `V` are
kept, the other `#S - 2` are bounded by `M`. -/
private theorem norm_prod_pair_le {S V : Finset (Fin k)} (hV : V ⊆ S) {j l : Fin k}
    (hj : j ∈ V) (hl : l ∈ V) (hjl : j ≠ l) (f g : Fin k → ℂ) {M : ℝ} (hf : ∀ i, ‖f i‖ ≤ M)
    (hg : ∀ i, ‖g i‖ ≤ M) :
    ‖(∏ i ∈ V, f i) * ∏ i ∈ S \ V, g i‖ ≤ ‖f j‖ * ‖f l‖ * M ^ (S.card - 2) := by
  have hl' : l ∈ V.erase j := mem_erase.2 ⟨hjl.symm, hl⟩
  have h2V : 1 < V.card := Finset.one_lt_card.2 ⟨j, hj, l, hl, hjl⟩
  have hVS : V.card ≤ S.card := card_le_card hV
  have h1 : ∏ i ∈ (V.erase j).erase l, ‖f i‖ ≤ M ^ (V.card - 2) := by
    have := prod_norm_le_pow ((V.erase j).erase l) f (fun i _ => hf i)
    rwa [card_erase_of_mem hl', card_erase_of_mem hj, Nat.sub_sub] at this
  have h2 : ∏ i ∈ S \ V, ‖g i‖ ≤ M ^ (S.card - V.card) := by
    have := prod_norm_le_pow (S \ V) g (fun i _ => hg i)
    rwa [card_sdiff_of_subset hV] at this
  have hpow : M ^ (V.card - 2) * M ^ (S.card - V.card) = M ^ (S.card - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [norm_mul, norm_prod, norm_prod, ← mul_prod_erase V _ hj,
    ← mul_prod_erase (V.erase j) _ hl']
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf j)
  have hA : 0 ≤ ‖f j‖ * (‖f l‖ * M ^ (V.card - 2)) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg hM _))
  calc ‖f j‖ * (‖f l‖ * ∏ i ∈ (V.erase j).erase l, ‖f i‖) * ∏ i ∈ S \ V, ‖g i‖
      ≤ ‖f j‖ * (‖f l‖ * M ^ (V.card - 2)) * M ^ (S.card - V.card) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          (norm_nonneg _)) h2 (prod_nonneg fun _ _ => norm_nonneg _) hA
    _ = ‖f j‖ * ‖f l‖ * (M ^ (V.card - 2) * M ^ (S.card - V.card)) := by ring
    _ = _ := by rw [hpow]

omit [NeZero k] in
/-- The binomial expansion of `∏_S (D + F) + ∏_S (D̄ + F)` around the term `V = ∅`. -/
private theorem expand_two (S : Finset (Fin k)) (F Dd Db : Fin k → ℂ) :
    ∏ i ∈ S, (Dd i + F i) + ∏ i ∈ S, (Db i + F i) =
      2 * ∏ i ∈ S, F i + ∑ V ∈ S.powerset.erase ∅,
        ((∏ i ∈ V, Dd i) + ∏ i ∈ V, Db i) * ∏ i ∈ S \ V, F i := by
  rw [prod_add, prod_add, ← sum_add_distrib,
    ← add_sum_erase (S.powerset) _ (empty_mem_powerset S)]
  simp only [prod_empty, sdiff_empty, one_mul]
  congr 1
  · ring
  · exact sum_congr rfl fun V _ => by ring

/-- **The bound of one term `V ≠ ∅` of the expansion** (in the
symmetrised form): `V = {j}` uses `(prop:BD2)` (the `f₂` bound), `#V ≥ 2` uses `(prop:BD1)`
twice (the `f₁ f₁` cross term). -/
private theorem term_bound {S V : Finset (Fin k)} (hk : 3 ≤ k) (hSc : S.card = k - 1)
    (hV : V ∈ S.powerset.erase ∅) (F Dd Db : Fin k → ℂ) (x s : Fin k → ℝ) {B X η Y Dm : ℝ}
    (hB : 1 ≤ B) (hX : 1 ≤ X) (hη : 0 ≤ η) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (hY2 : Y ^ 2 ≤ η * X ^ 2) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, 0 ≤ s i) (hsD : ∀ i, s i ≤ Dm)
    (hF : ∀ i, ‖F i‖ ≤ B * X)
    (hD : ∀ i, ‖Dd i‖ ≤ B * (s i * ((x i + 1)⁻¹ + Y)))
    (hDb : ∀ i, ‖Db i‖ ≤ B * (s i * ((x i + 1)⁻¹ + Y)))
    (h2 : ∀ i, ‖Dd i + Db i‖ ≤ B * (s i ^ 2 * ((x i ^ 2 + 1)⁻¹ + X * η))) :
    ‖((∏ i ∈ V, Dd i) + ∏ i ∈ V, Db i) * ∏ i ∈ S \ V, F i‖ ≤
      2 ^ k * B ^ (k - 1) * (1 + Dm) ^ k *
        (X ^ (k - 2) * ∑ j ∈ S, (x j ^ 2 + 1)⁻¹ + X ^ (k - 1) * η) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  rw [show n + 3 - 1 = n + 2 by omega] at hSc ⊢
  rw [show n + 3 - 2 = n + 1 by omega]
  obtain ⟨hV0, hVS⟩ := mem_erase.1 hV
  rw [mem_powerset] at hVS
  set Sx := ∑ j ∈ S, (x j ^ 2 + 1)⁻¹ with hSx
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hDm : 0 ≤ Dm := (hs 0).trans (hsD 0)
  have hD1 : 1 ≤ 1 + Dm := by linarith
  have hSx0 : 0 ≤ Sx := sum_nonneg fun i _ => by have := hx i; positivity
  have hinv_le : ∀ j ∈ S, (x j ^ 2 + 1)⁻¹ ≤ Sx := fun j hj =>
    single_le_sum (f := fun j => (x j ^ 2 + 1)⁻¹) (fun i _ => by have := hx i; positivity) hj
  have hVne : V.Nonempty := nonempty_iff_ne_empty.2 hV0
  rcases Nat.lt_or_ge 1 V.card with hc | hc
  · -- two or more factors of `D`
    obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.1 hc
    set M := 2 * B * X * (1 + Dm) with hM
    have hfM : ∀ f : Fin (n + 3) → ℂ, (∀ i, ‖f i‖ ≤ B * (s i * ((x i + 1)⁻¹ + Y))) →
        ∀ i, ‖f i‖ ≤ M := by
      intro f hf i
      have hxi : (x i + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hx i])
      have h1 : s i * ((x i + 1)⁻¹ + Y) ≤ (1 + Dm) * (2 * X) := by
        have := hs i
        have := hsD i
        have hxi0 : 0 ≤ (x i + 1)⁻¹ := by have := hx i; positivity
        nlinarith
      calc ‖f i‖ ≤ B * (s i * ((x i + 1)⁻¹ + Y)) := hf i
        _ ≤ B * ((1 + Dm) * (2 * X)) := mul_le_mul_of_nonneg_left h1 hB0
        _ = M := by rw [hM]; ring
    have hFM : ∀ i, ‖F i‖ ≤ M := fun i => (hF i).trans (by
      rw [hM]; nlinarith [mul_nonneg hB0 hX0])
    have hjS : j ∈ S := hVS hj
    have hlS : l ∈ S := hVS hl
    have hpair : (x j ^ 2 + 1)⁻¹ + (x l ^ 2 + 1)⁻¹ ≤ Sx := by
      have h := sum_le_sum_of_subset_of_nonneg (f := fun j => (x j ^ 2 + 1)⁻¹)
        (show ({j, l} : Finset (Fin (n + 3))) ⊆ S by
          intro i hi; rcases mem_insert.1 hi with rfl | hi
          · exact hjS
          · rw [mem_singleton.1 hi]; exact hlS)
        (fun i _ _ => by have := hx i; positivity)
      rwa [sum_pair hjl] at h
    have key : ∀ f : Fin (n + 3) → ℂ, (∀ i, ‖f i‖ ≤ B * (s i * ((x i + 1)⁻¹ + Y))) →
        ‖(∏ i ∈ V, f i) * ∏ i ∈ S \ V, F i‖ ≤
          2 ^ n * B ^ (n + 2) * (1 + Dm) ^ (n + 2) * X ^ n * (Sx + 2 * (η * X ^ 2)) := by
      intro f hf
      have h0 := norm_prod_pair_le hVS hj hl hjl f F (hfM f hf) hFM
      rw [hSc, show n + 2 - 2 = n by omega] at h0
      have hsj := hs j
      have hsl := hs l
      have hss : s j * s l ≤ (1 + Dm) ^ 2 := by
        have := hsD j; have := hsD l; nlinarith
      have hcross : ((x j + 1)⁻¹ + Y) * ((x l + 1)⁻¹ + Y) ≤ Sx + 2 * (η * X ^ 2) := by
        have := pair_le (Y := Y) (hx j) (hx l)
        linarith
      have hA0 : 0 ≤ (x j + 1)⁻¹ + Y := by have := hx j; positivity
      have hB0' : 0 ≤ (x l + 1)⁻¹ + Y := by have := hx l; positivity
      have hM0 : 0 ≤ M := by rw [hM]; positivity
      calc ‖(∏ i ∈ V, f i) * ∏ i ∈ S \ V, F i‖
          ≤ ‖f j‖ * ‖f l‖ * M ^ n := h0
        _ ≤ (B * (s j * ((x j + 1)⁻¹ + Y))) * (B * (s l * ((x l + 1)⁻¹ + Y))) * M ^ n := by
            gcongr
            · exact hf j
            · exact hf l
        _ = B ^ 2 * (s j * s l) * (((x j + 1)⁻¹ + Y) * ((x l + 1)⁻¹ + Y)) * M ^ n := by ring
        _ ≤ B ^ 2 * (1 + Dm) ^ 2 * (Sx + 2 * (η * X ^ 2)) * M ^ n := by
            gcongr
        _ = 2 ^ n * B ^ (n + 2) * (1 + Dm) ^ (n + 2) * X ^ n * (Sx + 2 * (η * X ^ 2)) := by
            rw [hM, mul_pow, mul_pow, mul_pow]; ring
    have hk1 := key Dd hD
    have hk2 := key Db hDb
    have hsum : ‖((∏ i ∈ V, Dd i) + ∏ i ∈ V, Db i) * ∏ i ∈ S \ V, F i‖ ≤
        2 * (2 ^ n * B ^ (n + 2) * (1 + Dm) ^ (n + 2) * X ^ n * (Sx + 2 * (η * X ^ 2))) := by
      rw [add_mul]
      exact (norm_add_le _ _).trans (by linarith)
    refine hsum.trans ?_
    have hXn : X ^ n ≤ X ^ (n + 1) := pow_le_pow_right₀ hX (by omega)
    have hDn : (1 + Dm) ^ (n + 2) ≤ (1 + Dm) ^ (n + 3) := pow_le_pow_right₀ hD1 (by omega)
    have hinner : X ^ n * (Sx + 2 * (η * X ^ 2)) ≤ 2 * (X ^ (n + 1) * Sx + X ^ (n + 2) * η) := by
      have : X ^ n * Sx ≤ X ^ (n + 1) * Sx := mul_le_mul_of_nonneg_right hXn hSx0
      have e : X ^ n * (2 * (η * X ^ 2)) = 2 * (X ^ (n + 2) * η) := by ring
      have h0 : 0 ≤ X ^ (n + 1) * Sx := by positivity
      rw [mul_add, e]
      linarith
    have hT0 : 0 ≤ X ^ (n + 1) * Sx + X ^ (n + 2) * η := by positivity
    calc 2 * (2 ^ n * B ^ (n + 2) * (1 + Dm) ^ (n + 2) * X ^ n * (Sx + 2 * (η * X ^ 2)))
        = 2 ^ (n + 1) * B ^ (n + 2) * (1 + Dm) ^ (n + 2) *
            (X ^ n * (Sx + 2 * (η * X ^ 2))) := by ring
      _ ≤ 2 ^ (n + 1) * B ^ (n + 2) * (1 + Dm) ^ (n + 3) *
            (2 * (X ^ (n + 1) * Sx + X ^ (n + 2) * η)) := by gcongr
      _ ≤ 2 ^ (n + 3) * B ^ (n + 2) * (1 + Dm) ^ (n + 3) *
            (X ^ (n + 1) * Sx + X ^ (n + 2) * η) := by
          have : (2 : ℝ) ^ (n + 1) * 2 ≤ 2 ^ (n + 3) := by
            rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
          have h0 : 0 ≤ B ^ (n + 2) * (1 + Dm) ^ (n + 3) * (X ^ (n + 1) * Sx + X ^ (n + 2) * η) :=
            by positivity
          nlinarith
  · -- exactly one factor: `V = {j}`
    have hc1 : V.card = 1 := le_antisymm hc (card_pos.2 hVne)
    obtain ⟨j, rfl⟩ := card_eq_one.1 hc1
    have hjS : j ∈ S := hVS (mem_singleton_self j)
    simp only [prod_singleton]
    have hcard : (S \ {j}).card = n + 1 := by
      rw [card_sdiff_of_subset hVS, hSc, card_singleton]
      omega
    have hprodF : ‖∏ i ∈ S \ {j}, F i‖ ≤ (B * X) ^ (n + 1) := by
      rw [norm_prod, ← hcard]; exact prod_norm_le_pow _ _ fun i _ => hF i
    have hsj := hs j
    have hs2 : s j ^ 2 ≤ (1 + Dm) ^ (n + 3) := by
      have : s j ≤ 1 + Dm := by linarith [hsD j]
      calc s j ^ 2 ≤ (1 + Dm) ^ 2 := pow_le_pow_left₀ hsj this 2
        _ ≤ (1 + Dm) ^ (n + 3) := pow_le_pow_right₀ hD1 (by omega)
    have hxj : (x j ^ 2 + 1)⁻¹ ≤ Sx := hinv_le j hjS
    have hq0 : 0 ≤ (x j ^ 2 + 1)⁻¹ := by have := hx j; positivity
    calc ‖(Dd j + Db j) * ∏ i ∈ S \ {j}, F i‖
        = ‖Dd j + Db j‖ * ‖∏ i ∈ S \ {j}, F i‖ := norm_mul _ _
      _ ≤ (B * (s j ^ 2 * ((x j ^ 2 + 1)⁻¹ + X * η))) * (B * X) ^ (n + 1) :=
          mul_le_mul (h2 j) hprodF (norm_nonneg _) (by positivity)
      _ = B ^ (n + 2) * s j ^ 2 * (X ^ (n + 1) * (x j ^ 2 + 1)⁻¹ + X ^ (n + 2) * η) := by ring
      _ ≤ B ^ (n + 2) * (1 + Dm) ^ (n + 3) * (X ^ (n + 1) * Sx + X ^ (n + 2) * η) := by
          gcongr
      _ ≤ 2 ^ (n + 3) * B ^ (n + 2) * (1 + Dm) ^ (n + 3) *
            (X ^ (n + 1) * Sx + X ^ (n + 2) * η) := by
          have h0 : 0 ≤ B ^ (n + 2) * (1 + Dm) ^ (n + 3) * (X ^ (n + 1) * Sx + X ^ (n + 2) * η) :=
            by positivity
          have : (1 : ℝ) ≤ 2 ^ (n + 3) := one_le_pow₀ (by norm_num)
          nlinarith

/-- **Case (ii)** (proof of `(spwow3)`): every boundary edge is the long edge `T`,
the self-energy is symmetric under the reflection `d ↦ 2u - d` about the fixed label `u`, and
its fibre sum is `O(η)` (sum zero).  Symmetrising and expanding `T(a, d_i) = F_i + D_i` around
`F_i = T(a, u)`: the `V = ∅` term is `(∏ F) Σ_d Sg(d)` (sum zero), the first-order terms cancel
(in the symmetrised sum they become `(prop:BD2)` terms), and the rest has two `(prop:BD1)`
factors. -/
private theorem core_alt (hk : 3 ≤ k) (p : Fin k) (u : Z2 L) (a : Fin k → Z2 L)
    (Sg : (Fin k → Z2 L) → ℂ) (T : Z2 L → Z2 L → ℂ) {B X η Y c₁ Cq : ℝ}
    (hB : 1 ≤ B) (hX : 1 ≤ X) (hη : 0 ≤ η) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (hY2 : Y ^ 2 ≤ η * X ^ 2) (hc₁ : 0 < c₁) (hCq : 0 ≤ Cq)
    (hsym : ∀ d, Sg (fun i => u + u - d i) = Sg d)
    (hSg : ∀ d, ‖Sg d‖ ≤ B * Real.exp (-(c₁ * (maxDist L d : ℝ))))
    (hQ : ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u), Sg d‖ ≤ Cq * η)
    (hF : ∀ x, ‖T x u‖ ≤ B * X)
    (hD1 : ∀ x y, ‖T x u - T x y‖ ≤
      B * ((zdist2 L (y - u) : ℝ) * (((zdist2 L (x - u) : ℝ) + 1)⁻¹ + Y)))
    (hD2 : ∀ x y, ‖2 * T x u - T x y - T x (u + u - y)‖ ≤
      B * ((zdist2 L (y - u) : ℝ) ^ 2 * (((zdist2 L (x - u) : ℝ) ^ 2 + 1)⁻¹ + X * η))) :
    ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Sg d * ∏ i ∈ univ.erase p, T (a i) (d i)‖
      ≤ (Cq + 4 ^ k * ((1 + (c₁ / (2 * ((k : ℝ) + 1)))⁻¹) ^ k *
          ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k)) * B ^ k *
        (X ^ (k - 2) * ∑ j ∈ univ.erase p, ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ +
          X ^ (k - 1) * η) := by
  set fib := univ.filter (fun d : Fin k → Z2 L => d p = u) with hfib
  set S := univ.erase p with hS
  set Sx := ∑ j ∈ S, ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ with hSx
  set Tg := X ^ (k - 2) * Sx + X ^ (k - 1) * η with hTg
  set Cw := (1 + (c₁ / (2 * ((k : ℝ) + 1)))⁻¹) ^ k * ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k with hCw
  have hSc : S.card = k - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hSx0 : 0 ≤ Sx := sum_nonneg fun _ _ => by positivity
  have hTg0 : 0 ≤ Tg := by positivity
  have hCw0 : 0 ≤ Cw := by positivity
  set F : Fin k → ℂ := fun i => T (a i) u with hFdef
  set w : (Fin k → Z2 L) → Finset (Fin k) → ℂ := fun d V =>
    ((∏ i ∈ V, (T (a i) (d i) - F i)) + ∏ i ∈ V, (T (a i) (u + u - d i) - F i)) *
      ∏ i ∈ S \ V, F i with hw
  -- the reflection `d ↦ 2u - d` of the fibre
  have hrefl : ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i) =
      ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (u + u - d i) := by
    refine sum_nbij' (fun d i => u + u - d i) (fun d i => u + u - d i) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [hfib, mem_filter, mem_univ, true_and] at hd ⊢
      rw [hd]; abel
    · intro d hd
      simp only [hfib, mem_filter, mem_univ, true_and] at hd ⊢
      rw [hd]; abel
    · intro d _; funext i; exact sub_sub_cancel _ _
    · intro d _; funext i; exact sub_sub_cancel _ _
    · intro d _
      simp only [hsym, sub_sub_cancel]
  -- the expansion
  have hexp : ∀ d, ∏ i ∈ S, T (a i) (d i) + ∏ i ∈ S, T (a i) (u + u - d i) =
      2 * ∏ i ∈ S, F i + ∑ V ∈ S.powerset.erase ∅, w d V := by
    intro d
    have e1 : ∏ i ∈ S, T (a i) (d i) = ∏ i ∈ S, ((T (a i) (d i) - F i) + F i) :=
      prod_congr rfl fun i _ => by ring
    have e2 : ∏ i ∈ S, T (a i) (u + u - d i) =
        ∏ i ∈ S, ((T (a i) (u + u - d i) - F i) + F i) :=
      prod_congr rfl fun i _ => by ring
    rw [e1, e2]
    exact expand_two S F _ _
  have h2 : 2 * ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i) =
      2 * ((∏ i ∈ S, F i) * ∑ d ∈ fib, Sg d) +
        ∑ d ∈ fib, Sg d * ∑ V ∈ S.powerset.erase ∅, w d V := by
    calc 2 * ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i)
        = ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i) +
            ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (u + u - d i) := by
          rw [two_mul]; congr 1
      _ = ∑ d ∈ fib, Sg d * (∏ i ∈ S, T (a i) (d i) + ∏ i ∈ S, T (a i) (u + u - d i)) := by
          rw [← sum_add_distrib]; exact sum_congr rfl fun d _ => by ring
      _ = ∑ d ∈ fib, Sg d * (2 * ∏ i ∈ S, F i + ∑ V ∈ S.powerset.erase ∅, w d V) :=
          sum_congr rfl fun d _ => by rw [hexp d]
      _ = _ := by
          simp only [mul_add, sum_add_distrib]
          congr 1
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun d _ => by ring
  -- the bound of each term `V ≠ ∅`
  have hW : ∀ d ∈ fib, ∀ V ∈ S.powerset.erase ∅, ‖w d V‖ ≤
      2 ^ k * B ^ (k - 1) * (1 + (maxDist L d : ℝ)) ^ k * Tg := by
    intro d hd V hV
    have hdp : d p = u := (mem_filter.1 hd).2
    refine term_bound hk hSc hV F (fun i => T (a i) (d i) - F i)
      (fun i => T (a i) (u + u - d i) - F i) (fun i => (zdist2 L (a i - u) : ℝ))
      (fun i => (zdist2 L (d i - u) : ℝ)) hB hX hη hY hYX hY2 (fun _ => Nat.cast_nonneg _)
      (fun _ => Nat.cast_nonneg _) (fun i => ?_) (fun i => hF (a i)) (fun i => ?_)
      (fun i => ?_) (fun i => ?_)
    · rw [← hdp]; exact_mod_cast le_maxDist d i p
    · rw [norm_sub_rev]; exact hD1 (a i) (d i)
    · rw [norm_sub_rev]
      have h := hD1 (a i) (u + u - d i)
      have e : u + u - d i - u = -(d i - u) := by abel
      rwa [e, zdist2_neg] at h
    · have e : T (a i) (d i) - F i + (T (a i) (u + u - d i) - F i) =
          -(2 * T (a i) u - T (a i) (d i) - T (a i) (u + u - d i)) := by
        simp only [hFdef]; ring
      rw [e, norm_neg]
      exact hD2 (a i) (d i)
  have hcardE : ((S.powerset.erase ∅).card : ℝ) ≤ 2 ^ k := by
    have h1 : (S.powerset.erase ∅).card ≤ 2 ^ k := by
      calc (S.powerset.erase ∅).card ≤ S.powerset.card := card_erase_le
        _ = 2 ^ S.card := card_powerset S
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h1
  have hrest : ‖∑ d ∈ fib, Sg d * ∑ V ∈ S.powerset.erase ∅, w d V‖ ≤
      4 ^ k * B ^ k * Tg * Cw := by
    have hpt : ∀ d ∈ fib, ‖Sg d * ∑ V ∈ S.powerset.erase ∅, w d V‖ ≤
        4 ^ k * B ^ k * Tg * (Real.exp (-(c₁ * (maxDist L d : ℝ))) *
          (1 + (maxDist L d : ℝ)) ^ k) := by
      intro d hd
      have hs : ‖∑ V ∈ S.powerset.erase ∅, w d V‖ ≤
          2 ^ k * (2 ^ k * B ^ (k - 1) * (1 + (maxDist L d : ℝ)) ^ k * Tg) := by
        refine (norm_sum_le _ _).trans ?_
        refine (sum_le_sum (hW d hd)).trans ?_
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcardE (by positivity)
      have hBk : B * B ^ (k - 1) = B ^ k := by
        rw [← pow_succ']; congr 1; omega
      rw [norm_mul]
      calc ‖Sg d‖ * ‖∑ V ∈ S.powerset.erase ∅, w d V‖
          ≤ (B * Real.exp (-(c₁ * (maxDist L d : ℝ)))) *
              (2 ^ k * (2 ^ k * B ^ (k - 1) * (1 + (maxDist L d : ℝ)) ^ k * Tg)) :=
            mul_le_mul (hSg d) hs (norm_nonneg _) (by positivity)
        _ = (2 ^ k * 2 ^ k) * (B * B ^ (k - 1)) * Tg *
              (Real.exp (-(c₁ * (maxDist L d : ℝ))) * (1 + (maxDist L d : ℝ)) ^ k) := by ring
        _ = 4 ^ k * B ^ k * Tg *
              (Real.exp (-(c₁ * (maxDist L d : ℝ))) * (1 + (maxDist L d : ℝ)) ^ k) := by
            rw [hBk, ← mul_pow]; norm_num
    calc _ ≤ ∑ d ∈ fib, ‖Sg d * ∑ V ∈ S.powerset.erase ∅, w d V‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ fib, 4 ^ k * B ^ k * Tg * (Real.exp (-(c₁ * (maxDist L d : ℝ))) *
            (1 + (maxDist L d : ℝ)) ^ k) := sum_le_sum hpt
      _ = 4 ^ k * B ^ k * Tg * ∑ d ∈ fib, Real.exp (-(c₁ * (maxDist L d : ℝ))) *
            (1 + (maxDist L d : ℝ)) ^ k := by rw [mul_sum]
      _ ≤ 4 ^ k * B ^ k * Tg * Cw :=
          mul_le_mul_of_nonneg_left (fiber_exp_pow_le p u hc₁ k) (by positivity)
  have hprodF : ‖∏ i ∈ S, F i‖ ≤ B ^ k * X ^ (k - 1) := by
    rw [norm_prod]
    calc ∏ i ∈ S, ‖F i‖ ≤ (B * X) ^ S.card := prod_norm_le_pow _ _ fun i _ => hF (a i)
      _ = B ^ (k - 1) * X ^ (k - 1) := by rw [hSc, mul_pow]
      _ ≤ B ^ k * X ^ (k - 1) := by
          gcongr
          omega
  have hmain : ‖(∏ i ∈ S, F i) * ∑ d ∈ fib, Sg d‖ ≤ Cq * B ^ k * Tg := by
    rw [norm_mul]
    calc ‖∏ i ∈ S, F i‖ * ‖∑ d ∈ fib, Sg d‖ ≤ (B ^ k * X ^ (k - 1)) * (Cq * η) :=
          mul_le_mul hprodF hQ (norm_nonneg _) (by positivity)
      _ = Cq * B ^ k * (X ^ (k - 1) * η) := by ring
      _ ≤ Cq * B ^ k * Tg := by
          gcongr
          rw [hTg]
          have : 0 ≤ X ^ (k - 2) * Sx := by positivity
          linarith
  have h2n : ‖(2 : ℂ) * ∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i)‖ ≤
      2 * (Cq * B ^ k * Tg) + 4 ^ k * B ^ k * Tg * Cw := by
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h2n
  have hfinal : ‖∑ d ∈ fib, Sg d * ∏ i ∈ S, T (a i) (d i)‖ ≤
      Cq * B ^ k * Tg + 4 ^ k * B ^ k * Tg * Cw := by
    have : 0 ≤ 4 ^ k * B ^ k * Tg * Cw := by positivity
    linarith
  refine hfinal.trans (le_of_eq ?_)
  ring

end Core

/-! ## 7. Symmetry, conjugation and sum zero for `Σ^{(∅)}` -/

section SumZeroInputs

private theorem norm_mSig'' {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

private theorem norm_xi_lt {E t : ℝ} (hE : |E| ≤ 2) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (s s' : Bool) : ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 := by
  rw [norm_mul, norm_mul, norm_mSig'' hE, norm_mSig'' hE, Complex.norm_real,
    Real.norm_of_nonneg ht.1, mul_one, mul_one]
  exact ht.2

/-- **Reflection about any point** (`g(s) = g(-s)` about the fixed label `d_p`, for every
`p`): `Σ^{(∅)}(t, σ, x - d) = Σ^{(∅)}(t, σ, d)`.  From `SigmaPi_empty_symm` (centre `d₀`) and
translation invariance `SumZero_SigmaPi_add_const`. -/
private theorem SigmaPi_reflect {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (σ : Fin n → Bool) (x : Z2 L)
    (d : Fin n → Z2 L) :
    SigmaPi L (mSig E) t σ ∅ (fun i => x - d i) = SigmaPi L (mSig E) t σ ∅ d := by
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 :=
    norm_xi_lt hE.le ht
  have h1 := SigmaPi_empty_symm L hL E hE t ht n σ (d 0) (fun i => d i - d 0) (by simp)
  have e1 : (fun i => d 0 + (d i - d 0)) = d := funext fun i => by abel
  rw [e1] at h1
  have h2 := SumZero_SigmaPi_add_const (mSig E) hm hL σ ∅ (fun i => d 0 - (d i - d 0))
    (x - (d 0 + d 0))
  have e2 : (fun v => d 0 - (d v - d 0) + (x - (d 0 + d 0))) = fun i => x - d i :=
    funext fun i => by abel
  rw [e2] at h2
  rw [h2, h1]

private theorem mSig_not (E : ℝ) (s : Bool) : mSig E (!s) = (starRingEnd ℂ) (mSig E s) := by
  cases s <;> simp [mSig]

/-- **The pattern `(-,+,-,…)` by complex conjugation**: `Q(!σ, ∅) = conj Q(σ, ∅)`. -/
private theorem Qlayer_not (E t : ℝ) {n : ℕ} [NeZero n] (σ : Fin n → Bool) :
    Qlayer (mSig E) t (fun v => !σ v) ∅ = (starRingEnd ℂ) (Qlayer (mSig E) t σ ∅) := by
  have hF : ∀ F : Finset (Fin n × Fin n), Flong F (fun v => !σ v) = Flong F σ := fun F => by
    unfold Flong
    exact filter_congr fun d _ => by simp
  have hT : TSPlong n (fun v => !σ v) ∅ = TSPlong n σ ∅ := by
    unfold TSPlong
    simp only [hF]
  rw [Qlayer, Qlayer, hT, map_sum]
  refine sum_congr rfl fun F _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun e _ => ?_
  simp only [edgeR, mSig_not, map_sub, map_inv₀, map_mul, map_one, Complex.conj_ofReal]

/-- If every edge of the cycle is long, `k` is even and `σ = ±σ^{(alt)}`. -/
private theorem alt_of_all_ne {k : ℕ} [NeZero k] (hk : 3 ≤ k) (σ : Fin k → Bool)
    (h : ∀ v : Fin k, σ v ≠ σ (v + 1)) :
    Even k ∧ (σ = sigAlt k ∨ σ = fun v => !sigAlt k v) := by
  have hone : ((1 : Fin k) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hstep : ∀ v : ℕ, ∀ hv : v + 1 < k, σ ⟨v + 1, hv⟩ = !σ ⟨v, by omega⟩ := by
    intro v hv
    have e : (⟨v, by omega⟩ : Fin k) + 1 = ⟨v + 1, hv⟩ := by
      ext
      rw [Fin.val_add, hone, Nat.mod_eq_of_lt hv]
    have := h ⟨v, by omega⟩
    rw [e] at this
    revert this
    cases σ ⟨v + 1, hv⟩ <;> cases σ ⟨v, by omega⟩ <;> simp
  have hform : ∀ v : ℕ, ∀ hv : v < k,
      σ ⟨v, hv⟩ = if v % 2 = 0 then σ 0 else !σ 0 := by
    intro v
    induction v with
    | zero => intro hv; simp
    | succ v ih =>
      intro hv
      rw [hstep v hv, ih (by omega)]
      by_cases hv2 : v % 2 = 0
      · have : (v + 1) % 2 ≠ 0 := by omega
        simp [hv2, this]
      · have : (v + 1) % 2 = 0 := by omega
        simp [hv2, this]
  have hlast : (⟨k - 1, by omega⟩ : Fin k) + 1 = 0 := by
    ext
    rw [Fin.val_add, hone, show k - 1 + 1 = k by omega, Nat.mod_self]
    rfl
  have hev : k % 2 = 0 := by
    by_contra hodd
    have h1 := h ⟨k - 1, by omega⟩
    rw [hlast, hform (k - 1) (by omega)] at h1
    have : (k - 1) % 2 = 0 := by omega
    simp [this] at h1
  refine ⟨Nat.even_iff.2 hev, ?_⟩
  cases h0 : σ 0
  · right
    funext v
    rw [show v = ⟨v.val, v.isLt⟩ from rfl, hform v.val v.isLt, h0]
    by_cases hv2 : v.val % 2 = 0 <;> simp [sigAlt, hv2]
  · left
    funext v
    rw [show v = ⟨v.val, v.isLt⟩ from rfl, hform v.val v.isLt, h0]
    by_cases hv2 : v.val % 2 = 0 <;> simp [sigAlt, hv2]

/-- **Sum zero at every index** (`(SZjadljsk)`): for a cycle of long edges, the fibre sum
`Σ_{d : d_p = u} Σ^{(∅)}(t, σ, d) = Q(σ, ∅)` (translation invariance, `SumZero_sum_slice`) is
`O(η_t)`, by `SigmaPi_alt_sumZero_le` for `σ^{(alt)}` and by conjugation for `-σ^{(alt)}`. -/
private theorem norm_slice_alt_le {κ : ℝ} (hκ : 0 < κ) {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    {E t : ℝ} (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (σ : Fin k → Bool) (h : ∀ v : Fin k, σ v ≠ σ (v + 1)) (p : Fin k) (u : Z2 L) :
    ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u), SigmaPi L (mSig E) t σ ∅ d‖ ≤
      2 ^ (k ^ 2) * k * (gapK κ)⁻¹ ^ k * (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
  have hE2 : |E| ≤ 2 := by linarith
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 := norm_xi_lt hE2 ht
  obtain ⟨hev, hσ⟩ := alt_of_all_ne hk σ h
  have hk4 : 4 ≤ k := by
    rcases hev with ⟨r, hr⟩; omega
  rw [SumZero_sum_slice (mSig E) hm hL σ ∅ p u]
  have hA : ‖Qlayer (mSig E) t (sigAlt k) ∅‖ ≤
      2 ^ (k ^ 2) * k * (gapK κ)⁻¹ ^ k * (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
    have h1 := SumZero_sum_slice (mSig E) hm hL (sigAlt k) ∅ ⟨0, by omega⟩ (0 : Z2 L)
    have h2 := SigmaPi_alt_sumZero_le κ hκ L hL E hE t ht k hk4 hev 0
    rw [← h1]
    exact h2
  rcases hσ with rfl | rfl
  · exact hA
  · rw [Qlayer_not, Complex.norm_conj]
    exact hA

end SumZeroInputs

/-! ## 8. The inner molecule at one parameter point -/

section Inner

/-- The constant of case (i). -/
private noncomputable def Cshort (c₁ : ℝ) (k : ℕ) : ℝ :=
  (1 + 4 / (c₁ / 2) ^ 2) * ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k

/-- The constant of case (ii). -/
private noncomputable def Calt (κ c₁ : ℝ) (k : ℕ) : ℝ :=
  2 ^ (k ^ 2) * k * (gapK κ)⁻¹ ^ k * (2 / Real.sqrt (κ * (4 - κ))) +
    4 ^ k * ((1 + (c₁ / (2 * ((k : ℝ) + 1)))⁻¹) ^ k * ((1 + 2 / (c₁ / 2 / k)) ^ 2) ^ k)

/-- The constant of the inner-molecule bound. -/
private noncomputable def KA (κ c : ℝ) (k : ℕ) : ℝ :=
  Cshort (c * Real.sqrt (gapK κ) / 2) k * (gapK κ)⁻¹ ^ k +
    Calt κ (c * Real.sqrt (gapK κ) / 2) k

private theorem Cshort_nonneg {c₁ : ℝ} (hc₁ : 0 < c₁) (k : ℕ) : 0 ≤ Cshort c₁ k := by
  unfold Cshort; positivity

private theorem Calt_nonneg (κ : ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁) (k : ℕ) :
    0 ≤ Calt κ c₁ k := by
  have := gapK_nonneg κ
  unfold Calt; positivity

private theorem KA_nonneg {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hκ2 : κ ≤ 2) (k : ℕ) :
    0 ≤ KA κ c k := by
  have hg := gapK_pos hκ hκ2
  have hc₁ : 0 < c * Real.sqrt (gapK κ) / 2 := by
    have := Real.sqrt_pos.2 hg; positivity
  unfold KA
  have := Cshort_nonneg hc₁ k
  have := Calt_nonneg κ hc₁ k
  positivity

/-- Every boundary edge is `≤ B c_κ⁻¹ X_t`. -/
private theorem edge_le {κ c₁ κe : ℝ} (hκ : 0 < κ) {N : ℕ} (p : Par κ N) {k : ℕ} [NeZero k]
    {B : ℝ} (hB : 1 ≤ B) (hG : Good p k B c₁ κe (gapK κ)⁻¹) (hκe : 0 ≤ κe) (s s' : Bool)
    (x y : Z2 p.L) :
    ‖thetaEdge p.L (mSig p.E) p.t s s' x y‖ ≤ B * (gapK κ)⁻¹ * Xt p.L p.E p.t := by
  have hE : |p.E| < 2 := absE_lt hκ p
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg p.E, p.hE]
  have hg := gapK_pos hκ hκ2
  have hG1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hg).2 (gapK_le_one κ)
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hB0 : 0 ≤ B := by linarith
  by_cases h : s = s'
  · subst h
    refine (hG.short s x y).trans ?_
    have he : Real.exp (-(κe * (zdist2 p.L (x - y) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κe * (zdist2 p.L (x - y) : ℝ) := mul_nonneg hκe (Nat.cast_nonneg _)
      linarith
    have hBG : 0 ≤ B * (gapK κ)⁻¹ := by positivity
    calc B * (gapK κ)⁻¹ * Real.exp (-(κe * (zdist2 p.L (x - y) : ℝ)))
        ≤ B * (gapK κ)⁻¹ * 1 := mul_le_mul_of_nonneg_left he hBG
      _ ≤ B * (gapK κ)⁻¹ * Xt p.L p.E p.t := mul_le_mul_of_nonneg_left hX hBG
  · rw [thetaEdge_long hE.le h]
    refine (hG.long x y).trans ?_
    have hX0 : 0 ≤ Xt p.L p.E p.t := by linarith
    calc B * Xt p.L p.E p.t = B * 1 * Xt p.L p.E p.t := by ring
      _ ≤ B * (gapK κ)⁻¹ * Xt p.L p.E p.t := by gcongr

/-- **`(spwow3)` at the erased index `q`, deterministic form**: the inner molecule
`A(u) = Σ_{d : d_q = u} Σ^{(∅)}(σ', d) ∏_{v ≠ q} Θ_v(a'_v, d_v)` with `σ'_q ≠ σ'_{q+1}` is at most
`K B^k (X^{k-2} Σ_{j ≠ q} (|a'_j - u|² + 1)⁻¹ + X^{k-1} η)`. -/
private theorem inner_bound {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) {N : ℕ} (p : Par κ N)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {B : ℝ} (hB : 1 ≤ B)
    (hG : Good p k B (c * Real.sqrt (gapK κ) / 2) (c * Real.sqrt (gapK κ)) (gapK κ)⁻¹)
    (σ' : Fin k → Bool) (q : Fin k) (hq : σ' q ≠ σ' (q + 1)) (a' : Fin k → Z2 p.L)
    (u : Z2 p.L) :
    ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 p.L => d q = u),
        SigmaPi p.L (mSig p.E) p.t σ' ∅ d *
          ∏ v ∈ univ.erase q, thetaEdge p.L (mSig p.E) p.t (σ' v) (σ' (v + 1)) (a' v) (d v)‖
      ≤ KA κ c k * B ^ k *
        (Xt p.L p.E p.t ^ (k - 2) *
            ∑ j ∈ univ.erase q, ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ +
          Xt p.L p.E p.t ^ (k - 1) * etaT p.E p.t) := by
  have hE : |p.E| < 2 := absE_lt hκ p
  have hE2 : |p.E| ≤ 2 := hE.le
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg p.E, p.hE]
  have hg := gapK_pos hκ hκ2
  have hG1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hg).2 (gapK_le_one κ)
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hsg : 0 < Real.sqrt (gapK κ) := Real.sqrt_pos.2 hg
  have hc₁0 : 0 < c * Real.sqrt (gapK κ) / 2 := by positivity
  have hκe : c * Real.sqrt (gapK κ) / 2 ≤ c * Real.sqrt (gapK κ) := by
    have := mul_pos hc hsg; linarith
  have hη := etaT_pos' hE p.ht1
  have hB0 : 0 ≤ B := by linarith
  set X := Xt p.L p.E p.t with hXdef
  set η := etaT p.E p.t with hηdef
  set Sx := ∑ j ∈ univ.erase q, ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ with hSx
  have hSx0 : 0 ≤ Sx := sum_nonneg fun _ _ => by positivity
  have hX0 : 0 ≤ X := by linarith
  have hTg0 : 0 ≤ X ^ (k - 2) * Sx + X ^ (k - 1) * η := by positivity
  have hCs := Cshort_nonneg hc₁0 k
  have hCa := Calt_nonneg κ hc₁0 k
  have hBk : 0 ≤ B ^ k := by positivity
  by_cases hsh : ∃ j, j ≠ q ∧ σ' j = σ' (j + 1)
  · -- case (i): a short boundary edge `j ≠ q`
    obtain ⟨j, hjq, hj⟩ := hsh
    have h := core_short hk q j hjq u a' (SigmaPi p.L (mSig p.E) p.t σ' ∅)
      (fun i => thetaEdge p.L (mSig p.E) p.t (σ' i) (σ' (i + 1))) hB hG1 hX hc₁0 hκe
      (hG.sig σ') (fun x y => by
        show ‖thetaEdge p.L (mSig p.E) p.t (σ' j) (σ' (j + 1)) x y‖ ≤ _
        rw [← hj]; exact hG.short _ x y)
      (fun i x y => edge_le hκ p hB hG (by positivity) _ _ x y)
    refine h.trans ?_
    have hjS : j ∈ univ.erase q := mem_erase.2 ⟨hjq, mem_univ _⟩
    have hxj : ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ ≤ Sx :=
      single_le_sum (f := fun j => ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹)
        (fun _ _ => by positivity) hjS
    have hA : Cshort (c * Real.sqrt (gapK κ) / 2) k * (gapK κ)⁻¹ ^ k ≤ KA κ c k := by
      unfold KA; linarith
    calc (1 + 4 / (c * Real.sqrt (gapK κ) / 2 / 2) ^ 2) *
            ((1 + 2 / (c * Real.sqrt (gapK κ) / 2 / 2 / k)) ^ 2) ^ k *
            (B * (gapK κ)⁻¹) ^ k * X ^ (k - 2) *
            ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹
        = Cshort (c * Real.sqrt (gapK κ) / 2) k * (gapK κ)⁻¹ ^ k * B ^ k *
            (X ^ (k - 2) * ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹) := by
          unfold Cshort; rw [mul_pow]; ring
      _ ≤ KA κ c k * B ^ k * (X ^ (k - 2) * Sx + X ^ (k - 1) * η) := by
          have h1 : 0 ≤ X ^ (k - 1) * η := by positivity
          have h2 : X ^ (k - 2) * ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ ≤ X ^ (k - 2) * Sx :=
            mul_le_mul_of_nonneg_left hxj (by positivity)
          have hmain : X ^ (k - 2) * ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ ≤
              X ^ (k - 2) * Sx + X ^ (k - 1) * η := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_right hA hBk) hmain (by positivity)
            (mul_nonneg (le_trans (by positivity) hA) hBk)
  · -- case (ii): every boundary edge is long
    simp only [not_exists, not_and] at hsh
    have hall : ∀ v : Fin k, σ' v ≠ σ' (v + 1) := fun v => by
      by_cases hv : v = q
      · rw [hv]; exact hq
      · exact hsh v hv
    have hsum : ∑ d ∈ univ.filter (fun d : Fin k → Z2 p.L => d q = u),
        SigmaPi p.L (mSig p.E) p.t σ' ∅ d *
          ∏ v ∈ univ.erase q, thetaEdge p.L (mSig p.E) p.t (σ' v) (σ' (v + 1)) (a' v) (d v) =
        ∑ d ∈ univ.filter (fun d : Fin k → Z2 p.L => d q = u),
          SigmaPi p.L (mSig p.E) p.t σ' ∅ d *
            ∏ v ∈ univ.erase q, Theta p.L (p.t : ℂ) (a' v) (d v) :=
      sum_congr rfl fun d _ => by
        congr 1
        exact prod_congr rfl fun v _ => by rw [thetaEdge_long hE2 (hall v)]
    rw [hsum]
    set Y := (ellT p.L p.t ^ 2 * Real.sqrt (1 - p.t))⁻¹ with hYdef
    have hY0 : 0 ≤ Y := by positivity
    have hYX : Y ≤ X := Y_le_Xt p.hL hE p.ht0 p.ht1
    have hY2 : Y ^ 2 ≤ η * X ^ 2 := Y_sq_le p.hL hE p.ht0 p.ht1
    have hCq : 0 ≤ 2 ^ (k ^ 2) * k * (gapK κ)⁻¹ ^ k * (2 / Real.sqrt (κ * (4 - κ))) := by
      have := gapK_nonneg κ; positivity
    have h := core_alt hk q u a' (SigmaPi p.L (mSig p.E) p.t σ' ∅) (Theta p.L (p.t : ℂ))
      hB hX hη.le hY0 hYX hY2 hc₁0 hCq
      (fun d => SigmaPi_reflect p.hL hE ⟨p.ht0, p.ht1⟩ σ' (u + u) d)
      (hG.sig σ')
      (norm_slice_alt_le hκ p.hL p.hE ⟨p.ht0, p.ht1⟩ hk σ' hall q u)
      (fun x => hG.long x u)
      (fun x y => by
        have h := hG.bd1 x u (y - u)
        have e : u + (y - u) = y := by abel
        rwa [e] at h)
      (fun x y => by
        have h := hG.bd2 x u (y - u)
        have e : u + (y - u) = y := by abel
        have e' : u - (y - u) = u + u - y := by abel
        rwa [e, e'] at h)
    refine h.trans ?_
    have hA : Calt κ (c * Real.sqrt (gapK κ) / 2) k ≤ KA κ c k := by
      unfold KA
      have : 0 ≤ Cshort (c * Real.sqrt (gapK κ) / 2) k * (gapK κ)⁻¹ ^ k := by positivity
      linarith
    calc _ = Calt κ (c * Real.sqrt (gapK κ) / 2) k * B ^ k *
            (X ^ (k - 2) * Sx + X ^ (k - 1) * η) := by unfold Calt; ring
      _ ≤ KA κ c k * B ^ k * (X ^ (k - 2) * Sx + X ^ (k - 1) * η) := by gcongr

end Inner

/-! ## 9. Absorbing the constants, and the split of `K^{(∅)}` at one vertex -/

section Assembly

/-- `C (N^{τ/(2m)})^m ≤ N^τ` eventually. -/
private theorem absorb_pow (m : ℕ) (hm : 0 < m) (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, C * ((N : ℝ) ^ (τ / (2 * m))) ^ m ≤ (N : ℝ) ^ τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  filter_upwards [eventually_le_rpow C (half_pos hτ)] with N hC
  have h3 : ((N : ℝ) ^ (τ / (2 * m))) ^ m = (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  rw [h3]
  calc C * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half N hτ

/-- Splitting the vertex `q`: `Σ_d Σ(d) ∏_v M_v(a_v, d_v) = Σ_w M_q(a_q, w) A_q(w)`. -/
private theorem sum_split {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (q : Fin n)
    (Sg : (Fin n → Z2 L) → ℂ) (M : Fin n → Z2 L → Z2 L → ℂ) (a : Fin n → Z2 L) :
    ∑ d : Fin n → Z2 L, Sg d * ∏ v, M v (a v) (d v) =
      ∑ w : Z2 L, M q (a q) w *
        ∑ d ∈ univ.filter (fun d : Fin n → Z2 L => d q = w),
          Sg d * ∏ v ∈ univ.erase q, M v (a v) (d v) := by
  rw [← sum_fiberwise univ (fun d : Fin n → Z2 L => d q)]
  refine sum_congr rfl fun w _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hdq : d q = w := (mem_filter.1 hd).2
  rw [← mul_prod_erase univ (fun v => M v (a v) (d v)) (mem_univ q), hdq]
  ring

end Assembly

/-! ## 10. The theorems -/

section Statements

/-- **`(spwow3)` at a general erased index**:
for `σ'_p ≠ σ'_{p+1}`,
`|A(u)| ≺ X_t^{k-2} Σ_{j ≠ p} (|a'_j - u|² + 1)⁻¹ + X_t^{k-1} η_t`, `A = innerId`.  The
paper's `min_j` is replaced by `Σ_j`.  Conditional on `Prop5Hyp κ c` and
`Prop6Hyp κ` (properties 5–6 of `lem_propTH`). -/
theorem Kpi_empty_spwow3At_prec :
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
        (Fin k → Z2 p.L) × Z2 p.L)
      (fun _ u => ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2.1 u.2.1.1.2 u.2.2.2‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 2) *
          ∑ j ∈ Finset.univ.erase u.2.1.1.2,
            ((zdist2 u.1.L (u.2.2.1 j - u.2.2.2) : ℝ) ^ 2 + 1)⁻¹
        + Xt u.1.L u.1.E u.1.t ^ (k - 1) * etaT u.1.E u.1.t) := by
  intro k _ hk κ c hκ hc h5 h6 τ hτ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine Filter.Eventually.of_forall fun N u => ?_
    exfalso
    have h1 := u.1.hE
    have h2 := abs_nonneg u.1.E
    have h3 := not_le.1 hκ2
    linarith
  have hk0 : 0 < k := by omega
  have hτ' : 0 < τ / (2 * (k : ℝ)) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk0
    positivity
  filter_upwards [good_eventually hk hκ hc h5 h6 hτ', Filter.eventually_ge_atTop 1,
    absorb_pow k hk0 (KA κ c k) hτ] with N hgood hN1 habs u
  rcases u with ⟨p, ⟨⟨σ', q⟩, hq⟩, a', u⟩
  dsimp only
  rw [innerId_eq_sum]
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hB : 1 ≤ (N : ℝ) ^ (τ / (2 * (k : ℝ))) := Real.one_le_rpow hN1' hτ'.le
  refine (inner_bound hκ hc p hk hB (hgood p) σ' q hq a' u).trans ?_
  have hE : |p.E| < 2 := absE_lt hκ p
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hη := etaT_pos' hE p.ht1
  have hT0 : 0 ≤ Xt p.L p.E p.t ^ (k - 2) *
        ∑ j ∈ univ.erase q, ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ +
      Xt p.L p.E p.t ^ (k - 1) * etaT p.E p.t := by
    have : 0 ≤ ∑ j ∈ univ.erase q, ((zdist2 p.L (a' j - u) : ℝ) ^ 2 + 1)⁻¹ :=
      sum_nonneg fun _ _ => by positivity
    have : (0 : ℝ) ≤ Xt p.L p.E p.t := by linarith
    positivity
  exact mul_le_mul_of_nonneg_right habs hT0

/-- **`(eq:bcal_k_pi)` at `π = ∅`**: `|K^{(∅)}_{t,σ,a}| ≺ (ℓ_t² η_t)^{-(n-1)}` for every `σ`.
Non-constant `σ`: split at a
long edge `q` and use `(spwow3)` at `q`, `Σ_u (|u|² + 1)⁻¹ ≤ 5 + 4 log L` and the row sum of
`Θ_t`; constant `σ`: case (i) at `q = 0`.  This is the special case `π = ∅` of
`(eq:bcal_k_pi)` (the general `π` is `Kpi_bound_prec`).  Conditional on `Prop5Hyp κ c` and
`Prop6Hyp κ`. -/
theorem Kpi_empty_prec :
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
      (fun _ u => ‖Kpi u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2 ∅‖)
      (fun _ u => (ellT u.1.L u.1.t ^ 2 * etaT u.1.E u.1.t)⁻¹ ^ (n - 1)) := by
  intro n _ hn κ c hκ hc h5 h6 τ hτ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine Filter.Eventually.of_forall fun N u => ?_
    exfalso
    have h1 := u.1.hE
    have h2 := abs_nonneg u.1.E
    have h3 := not_le.1 hκ2
    linarith
  have hg := gapK_pos hκ hκ2
  have hG1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hg).2 (gapK_le_one κ)
  have hsg : 0 < Real.sqrt (gapK κ) := Real.sqrt_pos.2 hg
  have hc₁0 : 0 < c * Real.sqrt (gapK κ) / 2 := by positivity
  have hκe0 : 0 < c * Real.sqrt (gapK κ) := by positivity
  have hκe : c * Real.sqrt (gapK κ) / 2 ≤ c * Real.sqrt (gapK κ) := by linarith
  have hm : 0 < n + 2 := by omega
  have hτ' : 0 < τ / (2 * ((n + 2 : ℕ) : ℝ)) := by positivity
  set τ' := τ / (2 * ((n + 2 : ℕ) : ℝ)) with hτ'def
  have hKA := KA_nonneg hκ hc hκ2 n
  have hCs := Cshort_nonneg hc₁0 n
  set K3 := KA κ c n * (1 + ((n - 1 : ℕ) : ℝ) * (5 + 4 / τ')) +
    Cshort (c * Real.sqrt (gapK κ) / 2) n * (gapK κ)⁻¹ ^ (n + 1) *
      (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 with hK3
  filter_upwards [good_eventually hn hκ hc h5 h6 hτ', Filter.eventually_ge_atTop 1,
    absorb_pow (n + 2) hm K3 hτ] with N hgood hN1 habs u
  rcases u with ⟨p, σ, a⟩
  dsimp only
  have hE : |p.E| < 2 := absE_lt hκ p
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hX0 : 0 ≤ Xt p.L p.E p.t := by linarith
  have hη := etaT_pos' hE p.ht1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set B := (N : ℝ) ^ τ' with hBdef
  have hB : 1 ≤ B := Real.one_le_rpow hN1' hτ'.le
  have hB0 : 0 ≤ B := by linarith
  have hG := hgood p
  set X := Xt p.L p.E p.t with hXdef
  set η := etaT p.E p.t with hηdef
  set Sg := SigmaPi p.L (mSig p.E) p.t σ ∅ with hSg
  set M : Fin n → Z2 p.L → Z2 p.L → ℂ := fun v => thetaEdge p.L (mSig p.E) p.t (σ v) (σ (v + 1))
    with hMdef
  have hK : Kpi p.L (mSig p.E) p.t σ a ∅ = ∑ d : Fin n → Z2 p.L, Sg d * ∏ v, M v (a v) (d v) :=
    Kpi_eq_sum_SigmaPi p.L p.E p.t n σ a ∅
  have hBpow : B ^ (n + 1) ≤ B ^ (n + 2) := pow_le_pow_right₀ hB (by omega)
  have hXpow : X ^ (n - 2) * X = X ^ (n - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hBound : ‖Kpi p.L (mSig p.E) p.t σ a ∅‖ ≤ K3 * B ^ (n + 2) * X ^ (n - 1) := by
    rw [hK]
    by_cases hnc : ∃ q, σ q ≠ σ (q + 1)
    · -- a long edge `q`: `(spwow3)` at `q`
      obtain ⟨q, hq⟩ := hnc
      rw [sum_split q Sg M a]
      have hMq : ∀ w, M q (a q) w = Theta p.L (p.t : ℂ) (a q) w := fun w => by
        simp only [hMdef]; rw [thetaEdge_long hE.le hq]
      set Sx : Z2 p.L → ℝ := fun w =>
        ∑ j ∈ univ.erase q, ((zdist2 p.L (a j - w) : ℝ) ^ 2 + 1)⁻¹ with hSxdef
      have hSx0 : ∀ w, 0 ≤ Sx w := fun w => sum_nonneg fun _ _ => by positivity
      have hA : ∀ w, ‖∑ d ∈ univ.filter (fun d : Fin n → Z2 p.L => d q = w),
          Sg d * ∏ v ∈ univ.erase q, M v (a v) (d v)‖ ≤
            KA κ c n * B ^ n * (X ^ (n - 2) * Sx w + X ^ (n - 1) * η) := fun w =>
        inner_bound hκ hc p hn hB hG σ q hq a w
      have hrow : ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ ≤ (1 - p.t)⁻¹ := by
        have hξ : ‖(p.t : ℂ)‖ < 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg p.ht0]; exact p.ht1
        have := sum_norm_Theta_row_le p.L p.hL hξ (a q)
        rwa [Complex.norm_real, Real.norm_of_nonneg p.ht0] at this
      have hLN : (p.L : ℝ) ≤ N := by
        have h1 : p.L ≤ N := by
          have := p.hN
          have hW := p.hW
          have : p.L ≤ p.W ^ 2 * p.L ^ 2 := by
            have : 1 ≤ p.W ^ 2 := Nat.one_le_pow _ _ (by omega)
            nlinarith
          omega
        exact_mod_cast h1
      have hlog : ∀ j, ∑ w : Z2 p.L, ((zdist2 p.L (a j - w) : ℝ) ^ 2 + 1)⁻¹ ≤
          (5 + 4 / τ') * B := fun j => by
        refine (sum_inv_sq_le p.L p.hL (a j)).trans ?_
        have h1 : Real.log p.L ≤ (p.L : ℝ) ^ τ' / τ' :=
          Real.log_le_rpow_div (Nat.cast_nonneg _) hτ'
        have h2 : (p.L : ℝ) ^ τ' ≤ B :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hLN hτ'.le
        have h3 : (p.L : ℝ) ^ τ' / τ' ≤ B / τ' := div_le_div_of_nonneg_right h2 hτ'.le
        have h4 : B / τ' = 1 / τ' * B := by ring
        have h5' : (5 : ℝ) ≤ 5 * B := by linarith
        have h6' : 4 / τ' * B = 4 * (1 / τ' * B) := by ring
        nlinarith
      have hsumSx : ∑ w : Z2 p.L, Sx w ≤ ((n - 1 : ℕ) : ℝ) * ((5 + 4 / τ') * B) := by
        simp only [hSxdef]
        rw [sum_comm]
        calc ∑ j ∈ univ.erase q, ∑ w : Z2 p.L, ((zdist2 p.L (a j - w) : ℝ) ^ 2 + 1)⁻¹
            ≤ ∑ _j ∈ univ.erase q, (5 + 4 / τ') * B := sum_le_sum fun j _ => hlog j
          _ = ((n - 1 : ℕ) : ℝ) * ((5 + 4 / τ') * B) := by
            rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
              nsmul_eq_mul]
      have hη1 : η * (1 - p.t)⁻¹ ≤ 1 := by
        have h1t : 0 < 1 - p.t := by linarith [p.ht1]
        rw [← div_eq_mul_inv, div_le_one h1t]
        exact etaT_le' p.ht1
      have hθ0 : ∀ w, 0 ≤ ‖Theta p.L (p.t : ℂ) (a q) w‖ := fun w => norm_nonneg _
      calc ‖∑ w : Z2 p.L, M q (a q) w *
            ∑ d ∈ univ.filter (fun d : Fin n → Z2 p.L => d q = w),
              Sg d * ∏ v ∈ univ.erase q, M v (a v) (d v)‖
          ≤ ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ *
              (KA κ c n * B ^ n * (X ^ (n - 2) * Sx w + X ^ (n - 1) * η)) := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun w _ => ?_)
            rw [norm_mul, hMq]
            exact mul_le_mul_of_nonneg_left (hA w) (norm_nonneg _)
        _ = KA κ c n * B ^ n * (X ^ (n - 2) *
              ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ * Sx w +
            X ^ (n - 1) * (η * ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖)) := by
            rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
            exact sum_congr rfl fun w _ => by ring
        _ ≤ KA κ c n * B ^ n * (X ^ (n - 2) * (B * X * (((n - 1 : ℕ) : ℝ) *
              ((5 + 4 / τ') * B))) + X ^ (n - 1) * 1) := by
            have h1 : ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ * Sx w ≤
                B * X * (((n - 1 : ℕ) : ℝ) * ((5 + 4 / τ') * B)) := by
              calc ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ * Sx w
                  ≤ ∑ w : Z2 p.L, B * X * Sx w :=
                    sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hG.long _ _) (hSx0 w)
                _ = B * X * ∑ w : Z2 p.L, Sx w := by rw [mul_sum]
                _ ≤ _ := mul_le_mul_of_nonneg_left hsumSx (by positivity)
            have h2 : η * ∑ w : Z2 p.L, ‖Theta p.L (p.t : ℂ) (a q) w‖ ≤ 1 :=
              (mul_le_mul_of_nonneg_left hrow hη.le).trans hη1
            gcongr
        _ = KA κ c n * (((n - 1 : ℕ) : ℝ) * (5 + 4 / τ') * B ^ (n + 2) + B ^ n) *
              X ^ (n - 1) := by
            rw [← hXpow]; ring
        _ ≤ K3 * B ^ (n + 2) * X ^ (n - 1) := by
            have hBn : B ^ n ≤ B ^ (n + 2) := pow_le_pow_right₀ hB (by omega)
            have hC2 : 0 ≤ Cshort (c * Real.sqrt (gapK κ) / 2) n * (gapK κ)⁻¹ ^ (n + 1) *
                (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 := by positivity
            have hin : KA κ c n * (((n - 1 : ℕ) : ℝ) * (5 + 4 / τ') * B ^ (n + 2) + B ^ n) ≤
                K3 * B ^ (n + 2) := by
              rw [hK3]
              have : 0 ≤ ((n - 1 : ℕ) : ℝ) * (5 + 4 / τ') := by positivity
              nlinarith [mul_nonneg hKA (sub_nonneg.2 hBn),
                mul_nonneg hC2 (show (0 : ℝ) ≤ B ^ (n + 2) by positivity)]
            exact mul_le_mul_of_nonneg_right hin (by positivity)
    · -- constant `σ`: case (i) at `q = 0` with the short edge `1`
      simp only [not_exists, not_not] at hnc
      have hn1 : (1 : Fin n) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega), Fin.val_zero] at this
        omega
      rw [sum_split 0 Sg M a]
      have hA : ∀ w, ‖∑ d ∈ univ.filter (fun d : Fin n → Z2 p.L => d 0 = w),
          Sg d * ∏ v ∈ univ.erase 0, M v (a v) (d v)‖ ≤
            Cshort (c * Real.sqrt (gapK κ) / 2) n * (B * (gapK κ)⁻¹) ^ n * X ^ (n - 2) := by
        intro w
        have h := core_short hn 0 1 hn1 w a Sg M hB hG1 hX hc₁0 hκe (hG.sig σ)
          (fun x y => by
            simp only [hMdef]
            rw [← hnc 1]; exact hG.short _ x y)
          (fun i x y => edge_le hκ p hB hG hκe0.le _ _ x y)
        refine h.trans ?_
        have hx1 : ((zdist2 p.L (a 1 - w) : ℝ) ^ 2 + 1)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by have := sq_nonneg (zdist2 p.L (a 1 - w) : ℝ); linarith)
        have h0 : 0 ≤ Cshort (c * Real.sqrt (gapK κ) / 2) n * (B * (gapK κ)⁻¹) ^ n *
            X ^ (n - 2) := by positivity
        calc _ = Cshort (c * Real.sqrt (gapK κ) / 2) n * (B * (gapK κ)⁻¹) ^ n * X ^ (n - 2) *
              ((zdist2 p.L (a 1 - w) : ℝ) ^ 2 + 1)⁻¹ := by unfold Cshort; ring
          _ ≤ Cshort (c * Real.sqrt (gapK κ) / 2) n * (B * (gapK κ)⁻¹) ^ n * X ^ (n - 2) * 1 :=
              mul_le_mul_of_nonneg_left hx1 h0
          _ = _ := mul_one _
      have hM0 : ∀ w, ‖M 0 (a 0) w‖ ≤
          B * (gapK κ)⁻¹ * Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (a 0 - w) : ℝ))) :=
        fun w => by
          simp only [hMdef]
          rw [← hnc 0]; exact hG.short _ _ _
      have hexp := sum_exp_le p.L (c * Real.sqrt (gapK κ)) hκe0 (a 0)
      set C0 := Cshort (c * Real.sqrt (gapK κ) / 2) n * (B * (gapK κ)⁻¹) ^ n * X ^ (n - 2)
        with hC0
      have hC00 : 0 ≤ C0 := by positivity
      calc ‖∑ w : Z2 p.L, M 0 (a 0) w *
            ∑ d ∈ univ.filter (fun d : Fin n → Z2 p.L => d 0 = w),
              Sg d * ∏ v ∈ univ.erase 0, M v (a v) (d v)‖
          ≤ ∑ w : Z2 p.L, (B * (gapK κ)⁻¹ *
              Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (a 0 - w) : ℝ)))) * C0 := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun w _ => ?_)
            rw [norm_mul]
            exact mul_le_mul (hM0 w) (hA w) (norm_nonneg _) (by positivity)
        _ = B * (gapK κ)⁻¹ * C0 * ∑ w : Z2 p.L,
              Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (a 0 - w) : ℝ))) := by
            rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
        _ ≤ B * (gapK κ)⁻¹ * C0 * (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Cshort (c * Real.sqrt (gapK κ) / 2) n * (gapK κ)⁻¹ ^ (n + 1) *
              (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 * B ^ (n + 1) * X ^ (n - 2) := by
            rw [hC0, mul_pow]; ring
        _ ≤ K3 * B ^ (n + 2) * X ^ (n - 1) := by
            have hXn : X ^ (n - 2) ≤ X ^ (n - 1) := pow_le_pow_right₀ hX (by omega)
            have hC2 : 0 ≤ Cshort (c * Real.sqrt (gapK κ) / 2) n * (gapK κ)⁻¹ ^ (n + 1) *
                (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 := by positivity
            have hK3' : Cshort (c * Real.sqrt (gapK κ) / 2) n * (gapK κ)⁻¹ ^ (n + 1) *
                (1 + 2 / (c * Real.sqrt (gapK κ))) ^ 2 ≤ K3 := by
              rw [hK3]
              have : 0 ≤ KA κ c n * (1 + ((n - 1 : ℕ) : ℝ) * (5 + 4 / τ')) := by positivity
              linarith
            gcongr
  calc ‖Kpi p.L (mSig p.E) p.t σ a ∅‖ ≤ K3 * B ^ (n + 2) * X ^ (n - 1) := hBound
    _ ≤ (N : ℝ) ^ τ * X ^ (n - 1) := mul_le_mul_of_nonneg_right habs (by positivity)
    _ = (N : ℝ) ^ τ * (ellT p.L p.t ^ 2 * etaT p.E p.t)⁻¹ ^ (n - 1) := rfl

end Statements

end RBM.KLoop
