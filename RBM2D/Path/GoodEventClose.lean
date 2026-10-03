/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.GoodEventGrid

/-!
# The deterministic consequence of the Azuma event and the Step 2 good event

The multiplier `azumaMm` with `azumaMm_nonneg`, `azumaMm_le`; the deterministic consequence
`xZ_le_azumaMm` of the Azuma event; the good event `goodEventGrid` with `goodEvent_grid` and
`goodEvent_grid_imp`.

For `d = 2` the multiplier is built on the loss of `cZ` (`lossE2 · e^{2 (log W)^{3/4}}`), and
`azumaMm ≤ N^{δ/8 + 3ε}`; the control of `xZ_le_azumaMm` has the four terms
`r^{5/2}·1(|a| ≤ 5ℓ*) + N^δ r^{19/4} M^{-1/4} + N^{3δ/2} r^6 M^{-1/2} + 1`
(`r = η_s/η_{u_k}`, `M = M_{u_k}`), from three separate time sums; the far-kernel and
shift remainders of `cZ` are absorbed into `𝒯²`; the good event uses `gridTauFull`, the
good set and the initial event of `highProb_init_grid`.

## Main declarations

* `azumaMm`, `azumaMm_nonneg`, `azumaMm_le`: the multiplier.
* `xZ_le_azumaMm`: the deterministic consequence of the Azuma event.
* `goodEventGrid`, `goodEvent_grid`, `goodEvent_grid_imp`: the good event, its probability and
  its deterministic consequences.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## Real-arithmetic helpers -/

/-- `c_κ = √(κ(4-κ))/2` is positive and bounds `Im m(E_n)` from below under
`|E_n| ≤ 2 - κ`. -/
private theorem GoodEventClose_im_ge {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (n : ℕ) :
    0 < Real.sqrt (κ * (4 - κ)) / 2 ∧ Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg (E n); have := hE n; linarith
  have hpos : 0 < κ * (4 - κ) := by nlinarith
  refine ⟨by positivity, ?_⟩
  rw [spectralM_im]
  have hE2 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hE n) 2
  have : κ * (4 - κ) ≤ 4 - E n ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- `(a^{1/4})^m = a^{m/4}`. -/
private theorem GoodEventClose_qpow {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (a ^ ((1 : ℝ) / 4)) ^ m = a ^ ((m : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; ring_nf

/-- `(a^{b/2})^m = a^{m b/2}`. -/
private theorem GoodEventClose_hpow {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (m : ℕ) :
    (a ^ (b / 2)) ^ m = a ^ ((m : ℝ) * b / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; ring_nf

/-- `10 z^{3/4} ≤ η z + 10 (10/η)³` for `z ≥ 0`, `η > 0`. -/
private theorem GoodEventClose_pow34_le {z η : ℝ} (hz : 0 ≤ z) (hη : 0 < η) :
    10 * z ^ ((3 : ℝ) / 4) ≤ η * z + 10 * (10 / η) ^ 3 := by
  have hb : 0 < 10 / η := by positivity
  rcases le_total z ((10 / η) ^ 4) with h | h
  · have h1 : z ^ ((3 : ℝ) / 4) ≤ ((10 / η) ^ 4) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hz h (by norm_num)
    have h2 : ((10 / η) ^ 4) ^ ((3 : ℝ) / 4) = (10 / η) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le, ← Real.rpow_natCast]; norm_num
    have : 0 ≤ η * z := by positivity
    linarith
  · have h1 : (10 / η) ≤ z ^ ((1 : ℝ) / 4) := by
      have := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hb.le, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by
        norm_num, Real.rpow_one] at this
    have hz0 : 0 < z := lt_of_lt_of_le (by positivity) h
    have hsplit : z = z ^ ((3 : ℝ) / 4) * z ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hz0]; norm_num
    have h34 : 0 ≤ z ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hz _
    have : 10 * z ^ ((3 : ℝ) / 4) ≤ η * z := by
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hη.le h34)
      have e : η * z ^ ((3 : ℝ) / 4) * (10 / η) = 10 * z ^ ((3 : ℝ) / 4) := by
        field_simp
      calc 10 * z ^ ((3 : ℝ) / 4) = η * z ^ ((3 : ℝ) / 4) * (10 / η) := e.symm
        _ ≤ η * z ^ ((3 : ℝ) / 4) * z ^ ((1 : ℝ) / 4) := h2
        _ = η * z := by rw [mul_assoc, ← hsplit]
    have : 0 ≤ 10 * (10 / η) ^ 3 := by positivity
    linarith

/-- `1 + log x ≤ (1 + 1/η) x^η` for `x ≥ 1`, `η > 0`. -/
private theorem GoodEventClose_one_add_log_le {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) (c : ℝ)
    (hc : 0 ≤ c) :
    1 + c * Real.log x ≤ (1 + c / η) * x ^ η := by
  have h1 : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div (by linarith) hη
  have h2 : 1 ≤ x ^ η := Real.one_le_rpow hx hη.le
  have : c * Real.log x ≤ c * (x ^ η / η) := mul_le_mul_of_nonneg_left h1 hc
  have e : (1 + c / η) * x ^ η = x ^ η + c * (x ^ η / η) := by ring
  rw [e]; linarith

/-- For a size sequence tending to infinity, `C ≤ N^b` eventually (`b > 0`). -/
private theorem GoodEventClose_eventually_const_le {b : ℝ} (hb : 0 < b)
    (hsize : RBM.Ind.SizeTendsto d) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ ((d.size n : ℕ) : ℝ) ^ b :=
  ((tendsto_rpow_atTop hb).comp hsize).eventually (eventually_ge_atTop C)

variable {d}

/-- Facts on the sizes: `1 ≤ L`, `1 ≤ W`, `L² ≤ N`, `W² ≤ N`, `1 ≤ N`. -/
private theorem GoodEventClose_sizes (n : ℕ) :
    (1 : ℝ) ≤ (d.L n : ℝ) ∧ (1 : ℝ) ≤ (d.W n : ℝ) ∧ (d.L n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧
      (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧ (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have hL : (1 : ℝ) ≤ (d.L n : ℝ) := by
    exact_mod_cast (by have := d.three_le_L n; omega : 1 ≤ d.L n)
  have hW : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  have hN : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
    rw [Sizes.size_eq]; push_cast; ring
  have hL2 : (1 : ℝ) ≤ (d.L n : ℝ) ^ 2 := one_le_pow₀ hL
  have hW2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW
  refine ⟨hL, hW, ?_, ?_, ?_⟩ <;> rw [hN] <;> nlinarith

/-! ## The multiplier `azumaMm` -/

variable (d) in
/-- **The Azuma multiplier**:
`azumaMm(n) = N^{δ/16} (√(8 · lossE2(L, W, N^ε, K₀) · e^{2 (log W)^{3/4}} / Im m(E_n)) + 1)`,
with `K₀ = 180·40002²(1 + log L)`, the loss factor of `cZ`. -/
def azumaMm (E : ℕ → ℝ) (δ ε : ℝ) (n : ℕ) : ℝ :=
  ((d.size n : ℕ) : ℝ) ^ (δ / 16) *
    (Real.sqrt (8 * (lossE2 (d.L n) (d.W n) (((d.size n : ℕ) : ℝ) ^ ε)
          (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) *
        Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4))) / (spectralM (E n)).im) + 1)

/-- **`azumaMm ≥ 0`**. -/
theorem azumaMm_nonneg (E : ℕ → ℝ) (δ ε : ℝ) (n : ℕ) : 0 ≤ azumaMm d E δ ε n := by
  unfold azumaMm
  positivity

/-- **`azumaMm ≤ N^{δ/8 + 3ε}` eventually**.  The loss is
`N^{6ε}` times a factor `N^{o(1)}` (logarithms of `L, W ≤ N` and `e^{10 (log W)^{3/4}}`),
which is at most `N^{δ/8}/4` eventually. -/
theorem azumaMm_le {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (hsize : RBM.Ind.SizeTendsto d) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) :
    ∀ᶠ n : ℕ in atTop, azumaMm d E δ ε n ≤ ((d.size n : ℕ) : ℝ) ^ (δ / 8 + 3 * ε) := by
  set η : ℝ := δ / 160 with hηdef
  have hη : 0 < η := by positivity
  set cκ : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hcκ
  have hcκ0 : 0 < cκ := (GoodEventClose_im_ge hκ hE 0).1
  set Cη : ℝ := 10 * (10 / η) ^ 3 with hCη
  set c1 : ℝ := 1 + 1 / η with hc1
  set c7 : ℝ := 1 + 7 / η with hc7
  set Cst : ℝ := 8 * 10 ^ 12 * (180 * 40002 ^ 2 * c1) ^ 2 * c7 ^ 4 * c1 ^ 3 * Real.exp Cη / cκ
    with hCst
  have hc1p : 0 < c1 := by positivity
  have hc7p : 0 < c7 := by positivity
  have hCst0 : 0 ≤ Cst := by positivity
  filter_upwards [GoodEventClose_eventually_const_le d (by positivity : (0 : ℝ) < δ / 16) hsize
    (4 * Cst + 2)] with n hbig
  obtain ⟨hL1, hW1, hLN, hWN, hN1⟩ := GoodEventClose_sizes (d := d) n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set L : ℝ := (d.L n : ℝ) with hLdef
  set W : ℝ := (d.W n : ℝ) with hWdef
  have hN0 : 0 < N := by linarith
  have hm := (GoodEventClose_im_ge hκ hE n).2
  set m : ℝ := (spectralM (E n)).im with hmdef
  have hm0 : 0 < m := lt_of_lt_of_le hcκ0 hm
  set q : ℝ := N ^ η with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1 hη.le
  have hq10 : N ^ (δ / 16) = q ^ 10 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hηdef]; push_cast; ring
  have hLleN : L ≤ N := by nlinarith
  have hWleN : W ≤ N := by nlinarith
  -- logarithmic factors
  have hlogL : 1 + Real.log L ≤ c1 * q := by
    have h := GoodEventClose_one_add_log_le hN1 hη 1 zero_le_one
    have : Real.log L ≤ Real.log N := Real.log_le_log (by linarith) hLleN
    rw [one_mul] at h; rw [hc1]; linarith
  have hlogW : 1 + Real.log W ≤ c1 * q := by
    have h := GoodEventClose_one_add_log_le hN1 hη 1 zero_le_one
    have : Real.log W ≤ Real.log N := Real.log_le_log (by linarith) hWleN
    rw [one_mul] at h; rw [hc1]; linarith
  have hlog12 : 1 + Real.log (L ^ 2 * W ^ 12) ≤ c7 * q := by
    have h := GoodEventClose_one_add_log_le hN1 hη 7 (by norm_num)
    have hLW : L ^ 2 * W ^ 12 ≤ N ^ 7 := by
      have h6 : W ^ 12 ≤ N ^ 6 := by
        rw [show W ^ 12 = (W ^ 2) ^ 6 by ring]
        exact pow_le_pow_left₀ (by positivity) hWN 6
      calc L ^ 2 * W ^ 12 ≤ N * N ^ 6 := mul_le_mul hLN h6 (by positivity) hN0.le
        _ = N ^ 7 := by ring
    have hpos : 0 < L ^ 2 * W ^ 12 := by positivity
    have : Real.log (L ^ 2 * W ^ 12) ≤ 7 * Real.log N := by
      have h7 := Real.log_le_log hpos hLW
      rw [Real.log_pow] at h7; push_cast at h7; exact h7
    rw [hc7]; linarith
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlog120 : 0 ≤ Real.log (L ^ 2 * W ^ 12) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1))
  -- the exponential factor
  have hexp : Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) *
      Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) ≤ Real.exp Cη * q := by
    rw [← Real.exp_add]
    have h := GoodEventClose_pow34_le hlogW0 hη
    have hWq : Real.exp (η * Real.log W) ≤ q := by
      rw [hq, Real.rpow_def_of_pos hN0, mul_comm η]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
        (Real.log_le_log (by linarith) hWleN) hη.le)
    calc Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4) + 2 * Real.log W ^ ((3 : ℝ) / 4))
        ≤ Real.exp (Cη + η * Real.log W) := Real.exp_le_exp.2 (by rw [hCη]; linarith)
      _ = Real.exp Cη * Real.exp (η * Real.log W) := Real.exp_add _ _
      _ ≤ Real.exp Cη * q := mul_le_mul_of_nonneg_left hWq (Real.exp_pos _).le
  -- the bound on the radicand
  set e3 : ℝ := N ^ (3 * ε) with he3
  have he31 : 1 ≤ e3 := Real.one_le_rpow hN1 (by positivity)
  have hΛ6 : (N ^ ε) ^ 6 = e3 ^ 2 := by
    rw [he3, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  set A : ℝ := 8 * (lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log L)) *
      Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) / m with hA
  have hAle : A ≤ Cst * e3 ^ 2 * q ^ 10 := by
    have hK0 : 180 * 40002 ^ 2 * (1 + Real.log L) ≤ 180 * 40002 ^ 2 * c1 * q := by
      nlinarith
    have hK00 : 0 ≤ 180 * 40002 ^ 2 * (1 + Real.log L) := by positivity
    have hinv : m⁻¹ ≤ cκ⁻¹ := inv_anti₀ hcκ0 hm
    have hloss : lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log L)) *
        Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) ≤
        10 ^ 12 * (180 * 40002 ^ 2 * c1 * q) ^ 2 * e3 ^ 2 * (c7 * q) ^ 4 * (c1 * q) ^ 3 *
          (Real.exp Cη * q) := by
      unfold lossE2
      rw [hΛ6, ← hLdef, ← hWdef]
      have e : 10 ^ 12 * (180 * 40002 ^ 2 * (1 + Real.log L)) ^ 2 * e3 ^ 2 *
            (1 + Real.log (L ^ 2 * W ^ 12)) ^ 4 * (1 + Real.log W) ^ 3 *
            Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) *
            Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) =
          10 ^ 12 * (180 * 40002 ^ 2 * (1 + Real.log L)) ^ 2 * e3 ^ 2 *
            (1 + Real.log (L ^ 2 * W ^ 12)) ^ 4 * (1 + Real.log W) ^ 3 *
            (Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) *
              Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) := by ring
      rw [e]
      gcongr
    have hL0 : 0 ≤ lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log L)) *
        Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) := by
      unfold lossE2; positivity
    calc A = 8 * (lossE2 (d.L n) (d.W n) (N ^ ε) (180 * 40002 ^ 2 * (1 + Real.log L)) *
          Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) * m⁻¹ := by rw [hA, div_eq_mul_inv]
      _ ≤ 8 * (10 ^ 12 * (180 * 40002 ^ 2 * c1 * q) ^ 2 * e3 ^ 2 * (c7 * q) ^ 4 *
            (c1 * q) ^ 3 * (Real.exp Cη * q)) * cκ⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hloss (by norm_num)) hinv
            (inv_nonneg.2 hm0.le) (by positivity)
      _ = Cst * e3 ^ 2 * q ^ 10 := by rw [hCst]; ring
  have hq10' : 4 * Cst + 2 ≤ q ^ 10 := by rw [← hq10]; exact hbig
  have hsqA : Real.sqrt A ≤ e3 * q ^ 10 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    calc A ≤ Cst * e3 ^ 2 * q ^ 10 := hAle
      _ ≤ (q ^ 10 / 4) * e3 ^ 2 * q ^ 10 := by gcongr; linarith
      _ = (e3 * q ^ 10 / 2) ^ 2 := by ring
  have hone : 1 ≤ e3 * q ^ 10 / 2 := by
    have : q ^ 10 ≤ e3 * q ^ 10 := le_mul_of_one_le_left (by positivity) he31
    linarith
  have hfin : N ^ (δ / 8 + 3 * ε) = q ^ 10 * (e3 * q ^ 10) := by
    rw [← hq10, he3, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  unfold azumaMm
  rw [← hN, ← hmdef, ← hLdef, ← hWdef, ← hA, hq10, hfin]
  gcongr
  linarith

/-! ## The time sums -/

/-- `(a^{1/4})^{4m} = a^m`. -/
private theorem GoodEventClose_qpow4 {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (a ^ ((1 : ℝ) / 4)) ^ (4 * m) = a ^ m := by
  have h4 : (a ^ ((1 : ℝ) / 4)) ^ 4 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  rw [pow_mul, h4]

/-- Telescoping: if `x_{j+1} = x_j - Δ` with `Δ ≥ 0` and `x_k > 0`, then
`Σ_{j<k} Δ/x_j² ≤ 1/x_k - 1/x_0`. -/
private theorem GoodEventClose_telescope {x : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hx : ∀ j, x (j + 1) = x j - Δ) :
    ∀ k, 0 < x k → ∑ j ∈ Finset.range k, Δ / x j ^ 2 ≤ 1 / x k - 1 / x 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hxk : 0 < x k := by have := hx k; linarith
    rw [Finset.sum_range_succ]
    have h1 := ih hxk
    have h2 : Δ / x k ^ 2 ≤ 1 / x (k + 1) - 1 / x k := by
      rw [hx k] at hk ⊢
      rw [div_sub_div _ _ hk.ne' hxk.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hΔ hΔ) hxk.le]
    linarith

/-- The per-index bound behind the three time sums: with `w⁴ = x_s/x_j`, `p⁴ = x_s/x_k`,
`R w⁴ ≤ p⁴`, `ρ ≤ w²`, `η_j⁻¹ = w⁴ c₀`, `η_k⁻¹ = p⁴ c₀`, `Θ = ν² w^{16}`,
`M_j^{-1/2} ≤ α²`, `M_k⁻¹ = α⁴`, the summand of the three time sums is `≤ c₀ w⁸ (…)`. -/
private theorem GoodEventClose_row {R ρ w p I μj μk α ν c0 ei ek Θ : ℝ} (hR0 : 0 ≤ R)
    (hRw : R * w ^ 4 ≤ p ^ 4) (hw : 1 ≤ w) (hwp : w ≤ p) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ w ^ 2)
    (hI0 : 0 ≤ I) (hμ0 : 0 ≤ μj) (hμ : μj ≤ α ^ 2) (hc0 : 0 ≤ c0)
    (hei : ei = w ^ 4 * c0) (hek : ek = p ^ 4 * c0) (hΘ : Θ = ν ^ 2 * w ^ 16)
    (hμk : μk = α ^ 4) :
    R ^ 4 * (ei * ρ ^ 10 * I + ei * ρ ^ 3 * μj * Θ ^ 2 + ek * μk * Θ ^ 3) ≤
      c0 * w ^ 8 * (I * p ^ 16 + ν ^ 4 * α ^ 2 * p ^ 34 + ν ^ 6 * α ^ 4 * p ^ 44) := by
  subst hei hek hΘ hμk
  have hw0 : 0 ≤ w := by linarith
  have hR16 : R ^ 4 * w ^ 16 ≤ p ^ 16 := by
    have := pow_le_pow_left₀ (mul_nonneg hR0 (pow_nonneg hw0 4)) hRw 4
    calc R ^ 4 * w ^ 16 = (R * w ^ 4) ^ 4 := by ring
      _ ≤ (p ^ 4) ^ 4 := this
      _ = p ^ 16 := by ring
  have hρ10 : ρ ^ 10 ≤ (w ^ 2) ^ 10 := pow_le_pow_left₀ hρ0 hρ 10
  have hρ3 : ρ ^ 3 ≤ (w ^ 2) ^ 3 := pow_le_pow_left₀ hρ0 hρ 3
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have h1 : R ^ 4 * (w ^ 4 * c0 * ρ ^ 10 * I) ≤ c0 * w ^ 8 * (I * p ^ 16) := by
    have hA : 0 ≤ R ^ 4 * (w ^ 4 * c0) * I := by positivity
    calc R ^ 4 * (w ^ 4 * c0 * ρ ^ 10 * I) = R ^ 4 * (w ^ 4 * c0) * I * ρ ^ 10 := by ring
      _ ≤ R ^ 4 * (w ^ 4 * c0) * I * (w ^ 2) ^ 10 := mul_le_mul_of_nonneg_left hρ10 hA
      _ = c0 * I * w ^ 8 * (R ^ 4 * w ^ 16) := by ring
      _ ≤ c0 * I * w ^ 8 * p ^ 16 := mul_le_mul_of_nonneg_left hR16 (by positivity)
      _ = _ := by ring
  have h2 : R ^ 4 * (w ^ 4 * c0 * ρ ^ 3 * μj * (ν ^ 2 * w ^ 16) ^ 2) ≤
      c0 * w ^ 8 * (ν ^ 4 * α ^ 2 * p ^ 34) := by
    have hw18 : w ^ 18 ≤ p ^ 18 := pow_le_pow_left₀ hw0 hwp 18
    have hA : 0 ≤ R ^ 4 * (w ^ 4 * c0) * (ν ^ 2 * w ^ 16) ^ 2 := by positivity
    have hρμ : ρ ^ 3 * μj ≤ (w ^ 2) ^ 3 * α ^ 2 :=
      mul_le_mul hρ3 hμ hμ0 (by positivity)
    calc R ^ 4 * (w ^ 4 * c0 * ρ ^ 3 * μj * (ν ^ 2 * w ^ 16) ^ 2)
        = R ^ 4 * (w ^ 4 * c0) * (ν ^ 2 * w ^ 16) ^ 2 * (ρ ^ 3 * μj) := by ring
      _ ≤ R ^ 4 * (w ^ 4 * c0) * (ν ^ 2 * w ^ 16) ^ 2 * ((w ^ 2) ^ 3 * α ^ 2) :=
          mul_le_mul_of_nonneg_left hρμ hA
      _ = c0 * ν ^ 4 * α ^ 2 * w ^ 8 * w ^ 18 * (R ^ 4 * w ^ 16) := by ring
      _ ≤ c0 * ν ^ 4 * α ^ 2 * w ^ 8 * p ^ 18 * p ^ 16 := by
          have h0 : 0 ≤ c0 * ν ^ 4 * α ^ 2 * w ^ 8 := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hw18 h0) hR16 (by positivity)
            (by positivity)
      _ = _ := by ring
  have h3 : R ^ 4 * (p ^ 4 * c0 * α ^ 4 * (ν ^ 2 * w ^ 16) ^ 3) ≤
      c0 * w ^ 8 * (ν ^ 6 * α ^ 4 * p ^ 44) := by
    have hw24 : w ^ 24 ≤ p ^ 24 := pow_le_pow_left₀ hw0 hwp 24
    have h0 : 0 ≤ c0 * ν ^ 6 * α ^ 4 * p ^ 4 * w ^ 8 := by positivity
    calc R ^ 4 * (p ^ 4 * c0 * α ^ 4 * (ν ^ 2 * w ^ 16) ^ 3)
        = c0 * ν ^ 6 * α ^ 4 * p ^ 4 * w ^ 8 * w ^ 24 * (R ^ 4 * w ^ 16) := by ring
      _ ≤ c0 * ν ^ 6 * α ^ 4 * p ^ 4 * w ^ 8 * p ^ 24 * p ^ 16 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw24 h0) hR16 (by positivity) (by positivity)
      _ = _ := by ring
  calc R ^ 4 * (w ^ 4 * c0 * ρ ^ 10 * I + w ^ 4 * c0 * ρ ^ 3 * μj * (ν ^ 2 * w ^ 16) ^ 2 +
        p ^ 4 * c0 * α ^ 4 * (ν ^ 2 * w ^ 16) ^ 3)
      = R ^ 4 * (w ^ 4 * c0 * ρ ^ 10 * I) +
          R ^ 4 * (w ^ 4 * c0 * ρ ^ 3 * μj * (ν ^ 2 * w ^ 16) ^ 2) +
          R ^ 4 * (p ^ 4 * c0 * α ^ 4 * (ν ^ 2 * w ^ 16) ^ 3) := by ring
    _ ≤ c0 * w ^ 8 * (I * p ^ 16) + c0 * w ^ 8 * (ν ^ 4 * α ^ 2 * p ^ 34) +
          c0 * w ^ 8 * (ν ^ 6 * α ^ 4 * p ^ 44) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- **The three time sums** (summed with their right sides kept separate): with
`R_{jk} = x_{u_{j+1}}/x_{u_k}`, `ρ_j = ℓ_{u_j}/ℓ_{s_n}`, `r = η_{s_n}/η_{u_k}`,
`Θ = thr`, `I ≥ 0`,
`Σ_{j<k} Δ R⁴ (η_j⁻¹ ρ^{10} I + η_j⁻¹ ρ³ (M_j⁻¹)^{1/2} Θ_j² + η_k⁻¹ M_k⁻¹ Θ_j³)
  ≤ (Im m)⁻¹ (r⁵ I + N^{2δ} r^{19/2} (M_k⁻¹)^{1/2} + N^{3δ} r^{12} M_k⁻¹)`. -/
private theorem GoodEventClose_timeSums {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {δ : ℝ} {n k : ℕ}
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hk : k ≤ K n)
    {I : ℝ} (hI0 : 0 ≤ I) :
    ∑ j ∈ Finset.range k, gridStep s v K n *
        (((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)) ^ 4 *
          ((etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 10 * I +
            (etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 3 *
              (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ ((1 : ℝ) / 2) *
              thr d E s δ n (gridTime s v K n j) ^ 2 +
            (etaT (E n) (gridTime s v K n k))⁻¹ *
              (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ *
              thr d E s δ n (gridTime s v K n j) ^ 3)) ≤
      ((spectralM (E n)).im)⁻¹ *
        ((etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 5 * I +
          ((d.size n : ℕ) : ℝ) ^ (2 * δ) *
            (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((19 : ℝ) / 2) *
            (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 2) +
          ((d.size n : ℕ) : ℝ) ^ (3 * δ) *
            (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 12 *
            (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹) := by
  have hLn : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWn : 1 ≤ d.W n := d.W_pos n
  have hN1 := (GoodEventClose_sizes (d := d) n).2.2.2.2
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hm0 : 0 < (spectralM (E n)).im := spectralM_im_pos hE
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hs1 : s n < 1 := hsv.trans_lt hv1
  have hS0 : 0 < 1 - s n := by linarith
  have hsle : ∀ i, s n ≤ gridTime s v K n i := fun i => by
    have h := GoodEvent_gridTime_mono (K := K) hsv (Nat.zero_le i)
    rwa [GoodEvent_gridTime_zero] at h
  have hsucc : ∀ j, gridTime s v K n (j + 1) = gridTime s v K n j + gridStep s v K n := by
    intro j; unfold gridTime; push_cast; ring
  have hukv : gridTime s v K n k ≤ v n := GoodEvent_gridTime_le hsv hk
  have huk1 : gridTime s v K n k < 1 := hukv.trans_lt hv1
  have hxk : 0 < 1 - gridTime s v K n k := by linarith
  -- the scales
  set m : ℝ := (spectralM (E n)).im with hmdef
  set S : ℝ := 1 - s n with hSdef
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set Δ : ℝ := gridStep s v K n with hΔdef
  set uk : ℝ := gridTime s v K n k with hukdef
  set Mk : ℝ := scaleM (d.L n) (d.W n) (E n) uk with hMkdef
  have hMk0 : 0 < Mk := scaleM_pos hLn hWn hE huk1
  set c0 : ℝ := (S * m)⁻¹ with hc0def
  have hc00 : 0 ≤ c0 := by positivity
  set a : ℝ := S / (1 - uk) with hadef
  have ha0 : 0 ≤ a := by positivity
  set p : ℝ := a ^ ((1 : ℝ) / 4) with hpdef
  set ν : ℝ := N ^ (δ / 2) with hνdef
  set α : ℝ := Mk⁻¹ ^ ((1 : ℝ) / 4) with hαdef
  have hMki0 : 0 ≤ Mk⁻¹ := inv_nonneg.2 hMk0.le
  have hp4 : p ^ 4 = a := by
    have h := GoodEventClose_qpow4 ha0 1; rw [mul_one, pow_one] at h; exact h
  have hα2 : α ^ 2 = Mk⁻¹ ^ ((1 : ℝ) / 2) := by
    rw [hαdef, GoodEventClose_qpow hMki0]; norm_num
  have hα4 : α ^ 4 = Mk⁻¹ := by
    have h := GoodEventClose_qpow4 hMki0 1; rw [mul_one, pow_one] at h; exact h
  have hν2 : ν ^ 2 = N ^ δ := by
    rw [hνdef, GoodEventClose_hpow hN0.le]; congr 1; push_cast; ring
  set Q : ℝ := I * p ^ 16 + ν ^ 4 * α ^ 2 * p ^ 34 + ν ^ 6 * α ^ 4 * p ^ 44 with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  -- the per-index bound
  have hper : ∀ j ∈ Finset.range k, Δ *
        (((1 - gridTime s v K n (j + 1)) / (1 - uk)) ^ 4 *
          ((etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 10 * I +
            (etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 3 *
              (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ ((1 : ℝ) / 2) *
              thr d E s δ n (gridTime s v K n j) ^ 2 +
            (etaT (E n) uk)⁻¹ * Mk⁻¹ * thr d E s δ n (gridTime s v K n j) ^ 3)) ≤
        (c0 * Q * S ^ 2) * (Δ / (1 - gridTime s v K n j) ^ 2) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set uj : ℝ := gridTime s v K n j with hujdef
    have hujk : uj ≤ uk := GoodEvent_gridTime_mono hsv hjk.le
    have hj1k : gridTime s v K n (j + 1) ≤ uk := GoodEvent_gridTime_mono hsv hjk
    have huj1 : uj < 1 := hujk.trans_lt huk1
    have hxj : 0 < 1 - uj := by linarith
    have hsuj : s n ≤ uj := hsle j
    have hj1 : uj ≤ gridTime s v K n (j + 1) := by rw [hsucc]; linarith
    set aj : ℝ := S / (1 - uj) with hajdef
    have haj0 : 0 ≤ aj := by positivity
    set w : ℝ := aj ^ ((1 : ℝ) / 4) with hwdef
    have hw4 : w ^ 4 = aj := by
      have h := GoodEventClose_qpow4 haj0 1; rw [mul_one, pow_one] at h; exact h
    have hw8 : w ^ 8 = aj ^ 2 := GoodEventClose_qpow4 haj0 2
    have hw16 : w ^ 16 = aj ^ 4 := GoodEventClose_qpow4 haj0 4
    have hw2 : w ^ 2 = aj ^ ((1 : ℝ) / 2) := by
      rw [hwdef, GoodEventClose_qpow haj0]; norm_num
    have haj1 : 1 ≤ aj := by rw [hajdef, one_le_div hxj]; linarith
    have hajle : aj ≤ a := div_le_div_of_nonneg_left hS0.le hxk (by linarith)
    have hw1 : 1 ≤ w := Real.one_le_rpow haj1 (by norm_num)
    have hwp : w ≤ p := Real.rpow_le_rpow haj0 hajle (by norm_num)
    have hR0 : 0 ≤ (1 - gridTime s v K n (j + 1)) / (1 - uk) :=
      div_nonneg (by linarith) hxk.le
    have hRw : (1 - gridTime s v K n (j + 1)) / (1 - uk) * w ^ 4 ≤ p ^ 4 := by
      rw [hw4, hp4, hajdef, hadef, div_mul_div_comm, div_le_div_iff₀ (by positivity) hxk]
      have h1 : 1 - gridTime s v K n (j + 1) ≤ 1 - uj := by linarith
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ S * (1 - uk))
      nlinarith
    have hℓ := ellT_mono_ratio hLn hs0 hsuj huj1
    have hℓs : 0 < ellT (d.L n) (s n) := (ellT_pos_le hLn hs1).1
    have hℓj : 0 < ellT (d.L n) uj := (ellT_pos_le hLn huj1).1
    have hρ0 : 0 ≤ ellT (d.L n) uj / ellT (d.L n) (s n) := by positivity
    have hρ : ellT (d.L n) uj / ellT (d.L n) (s n) ≤ w ^ 2 := by rw [hw2]; exact hℓ.2
    have hMj0 : 0 < scaleM (d.L n) (d.W n) (E n) uj := scaleM_pos hLn hWn hE huj1
    have hMkj : Mk ≤ scaleM (d.L n) (d.W n) (E n) uj := (scaleM_anti_ratio hLn hE hujk huk1).1
    have hμ0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (inv_nonneg.2 hMj0.le) _
    have hμ : (scaleM (d.L n) (d.W n) (E n) uj)⁻¹ ^ ((1 : ℝ) / 2) ≤ α ^ 2 := by
      rw [hα2]
      exact Real.rpow_le_rpow (inv_nonneg.2 hMj0.le) (inv_anti₀ hMk0 hMkj) (by norm_num)
    have hei : (etaT (E n) uj)⁻¹ = w ^ 4 * c0 := by
      rw [hw4, hajdef, hc0def]; unfold etaT; rw [← hmdef]
      field_simp
    have hek : (etaT (E n) uk)⁻¹ = p ^ 4 * c0 := by
      rw [hp4, hadef, hc0def]; unfold etaT; rw [← hmdef]
      field_simp
    have hΘ : thr d E s δ n uj = ν ^ 2 * w ^ 16 := by
      unfold thr
      rw [etaT_div_etaT hE hs1 huj1, hν2, hw16]
    have hrow := GoodEventClose_row hR0 hRw hw1 hwp hρ0 hρ hI0 hμ0 hμ hc00 hei hek hΘ hα4.symm
    have hw8' : w ^ 8 = S ^ 2 / (1 - uj) ^ 2 := by rw [hw8, hajdef, div_pow]
    calc _ ≤ Δ * (c0 * w ^ 8 * Q) := mul_le_mul_of_nonneg_left hrow hΔ0
      _ = (c0 * Q * S ^ 2) * (Δ / (1 - uj) ^ 2) := by rw [hw8']; ring
  -- summing
  have htel := GoodEventClose_telescope (x := fun i => 1 - gridTime s v K n i) hΔ0
    (fun j => by
      show 1 - gridTime s v K n (j + 1) = 1 - gridTime s v K n j - Δ
      rw [hsucc]; ring) k hxk
  have hx0 : 0 < 1 - gridTime s v K n 0 := by rw [GoodEvent_gridTime_zero]; exact hS0
  have htel' : ∑ j ∈ Finset.range k, Δ / (1 - gridTime s v K n j) ^ 2 ≤ 1 / (1 - uk) := by
    have : 0 ≤ 1 / (1 - gridTime s v K n 0) := by positivity
    linarith
  have hCQ : 0 ≤ c0 * Q * S ^ 2 := by positivity
  have hr : etaT (E n) (s n) / etaT (E n) uk = p ^ 4 := by
    rw [etaT_div_etaT hE hs1 huk1, hp4]
  have hr5 : (p ^ 4) ^ 5 = p ^ 20 := by ring
  have hr12 : (p ^ 4) ^ 12 = p ^ 48 := by ring
  have hr19 : (p ^ 4) ^ ((19 : ℝ) / 2) = p ^ 38 := by
    rw [hp4, hpdef, GoodEventClose_qpow ha0]; norm_num
  have hN2 : N ^ (2 * δ) = ν ^ 4 := by
    rw [hνdef, GoodEventClose_hpow hN0.le]; congr 1; push_cast; ring
  have hN3 : N ^ (3 * δ) = ν ^ 6 := by
    rw [hνdef, GoodEventClose_hpow hN0.le]; congr 1; push_cast; ring
  calc _ ≤ ∑ j ∈ Finset.range k, (c0 * Q * S ^ 2) * (Δ / (1 - gridTime s v K n j) ^ 2) :=
        Finset.sum_le_sum hper
    _ = (c0 * Q * S ^ 2) * ∑ j ∈ Finset.range k, Δ / (1 - gridTime s v K n j) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (c0 * Q * S ^ 2) * (1 / (1 - uk)) := mul_le_mul_of_nonneg_left htel' hCQ
    _ = m⁻¹ * (p ^ 4 * Q) := by
        rw [hp4, hadef, hc0def]; field_simp
    _ = _ := by
        rw [hr, hr5, hr12, hr19, hN2, hN3, ← hα2, ← hα4, hQdef]; ring

/-! ## The deterministic consequence `xZ ≤ azumaMm · Ctrl · 𝒯` -/

/-- The algebra of one summand of `4 Σ cZ`: the main part, the far-kernel part (`8F ≤ W_D/4`),
the shift part (`8 Sh ≤ N_D/4`) and the floor. -/
private theorem GoodEventClose_cZ_alg {Δ R L0 Aj T Fj Shj NCc Wd ND : ℝ} (hΔ : 0 ≤ Δ)
    (hF : 8 * Fj ≤ Wd / 4) (hSh : 8 * Shj ≤ ND / 4) :
    4 * (2 * Δ * (R ^ 4 * (L0 * Aj * T ^ 2) + Fj + Shj) + Δ * NCc) ≤
      8 * L0 * T ^ 2 * (Δ * (R ^ 4 * Aj)) + Δ * (Wd / 4 + ND / 4 + 4 * NCc) := by
  have h2 := mul_le_mul_of_nonneg_left hF hΔ
  have h3 := mul_le_mul_of_nonneg_left hSh hΔ
  linarith

/-- The shift remainder: `8·16 R⁴ N² η⁻⁷ Δ ≤ Y/4` from `R⁴ ≤ √N`, `η⁻¹ ≤ N C`,
`Δ ≤ Y N^{-10}` and `512 C⁷ ≤ √N` (written with `sN = √N`, `N = sN²`). -/
private theorem GoodEventClose_shift_le {R4 N2 ei Δ sN C Y : ℝ} (hR4le : R4 ≤ sN)
    (hsN : 0 < sN) (hN2 : N2 = sN ^ 4) (hei0 : 0 ≤ ei) (hei : ei ≤ sN ^ 2 * C) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ Y * (sN ^ 20)⁻¹) (hY : 0 ≤ Y) (hC : 0 ≤ C) (hbig : 512 * C ^ 7 ≤ sN) :
    8 * (16 * R4 * N2 * ei ^ 7 * Δ) ≤ Y / 4 := by
  subst hN2
  have hei7 : ei ^ 7 ≤ (sN ^ 2 * C) ^ 7 := pow_le_pow_left₀ hei0 hei 7
  calc 8 * (16 * R4 * sN ^ 4 * ei ^ 7 * Δ)
      ≤ 8 * (16 * sN * sN ^ 4 * (sN ^ 2 * C) ^ 7 * (Y * (sN ^ 20)⁻¹)) := by
        gcongr
    _ = (128 * C ^ 7 / sN) * Y := by field_simp; ring
    _ ≤ (1 / 4) * Y := by
        refine mul_le_mul_of_nonneg_right ?_ hY
        rw [div_le_iff₀ hsN]; linarith
    _ = Y / 4 := by ring

/-- The far-kernel remainder: `8·8 L⁴ W^{2-D'} N^ε ρ^{10} μ R³ ≤ (W^{-D})²/4` from `ρ ≤ L`,
`μ ≤ 1`, `R³ ≤ W^{1/5}`, `L^{14} N^ε ≤ W^e`, `e + 3 + 2D ≤ D'` and `256 ≤ W^{4/5}`. -/
private theorem GoodEventClose_far_le {L W Ne ρ μ5 R3 D D' e : ℝ} (hW1 : 1 ≤ W)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ L) (hμ0 : 0 ≤ μ5) (hμ : μ5 ≤ 1) (hR0 : 0 ≤ R3)
    (hR : R3 ≤ W ^ ((1 : ℝ) / 5)) (hNe0 : 0 ≤ Ne) (hLN : L ^ 14 * Ne ≤ W ^ e)
    (hD' : e + 3 + 2 * D ≤ D') (hW256 : 256 ≤ W ^ ((4 : ℝ) / 5)) :
    8 * (8 * L ^ 4 * W ^ (2 - D') * Ne * ρ ^ 10 * μ5 * R3) ≤ (W ^ (-D)) ^ 2 / 4 := by
  have hW0 : 0 < W := by linarith
  have hρ10 : ρ ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ hρ0 hρ 10
  have hWD' : 0 ≤ W ^ (2 - D') := Real.rpow_nonneg hW0.le _
  calc 8 * (8 * L ^ 4 * W ^ (2 - D') * Ne * ρ ^ 10 * μ5 * R3)
      ≤ 8 * (8 * L ^ 4 * W ^ (2 - D') * Ne * L ^ 10 * 1 * W ^ ((1 : ℝ) / 5)) := by
        gcongr
    _ = 64 * (L ^ 14 * Ne) * (W ^ (2 - D') * W ^ ((1 : ℝ) / 5)) := by ring
    _ ≤ 64 * W ^ e * (W ^ (2 - D') * W ^ ((1 : ℝ) / 5)) := by gcongr
    _ = 64 * W ^ (e + (2 - D') + 1 / 5) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0]; ring
    _ ≤ 64 * W ^ (-D + -D + -((4 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
          (by norm_num)
    _ = 64 * (W ^ (-D)) ^ 2 * (W ^ ((4 : ℝ) / 5))⁻¹ := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_neg hW0.le ((4 : ℝ) / 5)]; ring
    _ ≤ 64 * (W ^ (-D)) ^ 2 * (1 / 256) := by
        gcongr
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hW256
    _ = (W ^ (-D)) ^ 2 / 4 := by ring

/-- `(x^b)² = x^{2b}`. -/
private theorem GoodEventClose_sq_rpow {x : ℝ} (hx : 0 ≤ x) (b : ℝ) :
    (x ^ b) ^ 2 = x ^ (2 * b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num; ring_nf

/-- The final square-root step: if `X ≤ T²(A P + 1)`, `P ≤ C₁²`, then
`√X ≤ (√A + 1)(C₁ + 1) T`. -/
private theorem GoodEventClose_sqrt_step {X T A P C1 : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hC1 : 0 ≤ C1) (hX : X ≤ T ^ 2 * (A * P + 1)) (hPC : P ≤ C1 ^ 2) :
    Real.sqrt X ≤ (Real.sqrt A + 1) * (C1 + 1) * T := by
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  rw [Real.sqrt_le_left (by positivity)]
  have hsA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have h1 : A * P + 1 ≤ (Real.sqrt A + 1) ^ 2 * (C1 + 1) ^ 2 := by
    have e1 : A + 1 ≤ (Real.sqrt A + 1) ^ 2 := by nlinarith
    have e2 : C1 ^ 2 + 1 ≤ (C1 + 1) ^ 2 := by nlinarith
    have e3 : A * P + 1 ≤ (A + 1) * (C1 ^ 2 + 1) := by nlinarith
    calc A * P + 1 ≤ (A + 1) * (C1 ^ 2 + 1) := e3
      _ ≤ (Real.sqrt A + 1) ^ 2 * (C1 + 1) ^ 2 := mul_le_mul e1 e2 (by positivity) (by positivity)
  calc X ≤ T ^ 2 * (A * P + 1) := hX
    _ ≤ T ^ 2 * ((Real.sqrt A + 1) ^ 2 * (C1 + 1) ^ 2) := by gcongr
    _ = ((Real.sqrt A + 1) * (C1 + 1) * T) ^ 2 := by ring

/-- `xZ ≤ azumaMm · Ctrl · 𝒯` at one size index `n`, with the eventual inputs of
`xZ_le_azumaMm` evaluated at `n`. -/
private theorem GoodEventClose_xZ_le_at {E : ℕ → ℝ} {s v t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {c cκ τ' δ D ε D' Cc Cx : ℝ} (hcκ : 0 < cκ) (hm : cκ ≤ (spectralM (E n)).im)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hvt : v n ≤ t n) (ht1 : t n < 1)
    (hc : 0 < c) (hτ' : 0 ≤ τ') (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hD' : 2 * D + 3 + (7 + ε) / c ≤ D') (hCc : D + 1 ≤ Cc) (hCx : D + 1 ≤ Cx)
    (hstep : (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ ((1 - t n) / (1 - s n)) ^ 30)
    (hband : ((d.size n : ℕ) : ℝ) ^ c ≤ (d.W n : ℝ))
    (hrange : ((d.size n : ℕ) : ℝ) ^ (-1 + τ') ≤ 1 - t n)
    (hmesh : gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-(D + 10)))
    (hW256 : 256 ≤ (d.W n : ℝ) ^ ((4 : ℝ) / 5))
    (hN512 : 512 * cκ⁻¹ ^ 7 ≤ ((d.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 2))
    (hN10 : 10 ≤ ((d.size n : ℕ) : ℝ)) {k : ℕ} (hk : k ≤ K n) (a : Z2 (d.L n) × Z2 (d.L n)) :
    xZ d E s v K δ D ε D' Cc Cx n k a ≤ azumaMm d E δ ε n *
      ((etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((5 : ℝ) / 2) *
          (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
              5 * ellStar (d.L n) (d.W n) (gridTime s v K n k) then 1 else 0) +
        ((d.size n : ℕ) : ℝ) ^ δ *
          (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((19 : ℝ) / 4) *
          (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 4) +
        ((d.size n : ℕ) : ℝ) ^ (3 * δ / 2) *
          (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 6 *
          (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 2) + 1) *
      tailT (d.L n) (d.W n) (E n) D (gridTime s v K n k) (zdist2 (d.L n) (a.1 - a.2) : ℝ) := by
  -- sizes and scales
  have hLn : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hWn : 1 ≤ d.W n := d.W_pos n
  obtain ⟨hL1, hW1, hLN, hWN, hN1⟩ := GoodEventClose_sizes (d := d) n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hm0 : 0 < (spectralM (E n)).im := spectralM_im_pos hE
  have hΔ0 : 0 ≤ gridStep s v K n := GoodEvent_gridStep_nonneg hsv
  have hs1 : s n < 1 := (hsv.trans hvt).trans_lt ht1
  have hS0 : 0 < 1 - s n := by linarith
  have hxt : 0 < 1 - t n := by linarith
  have hsle : ∀ i, s n ≤ gridTime s v K n i := fun i => by
    have h := GoodEvent_gridTime_mono (K := K) hsv (Nat.zero_le i)
    rwa [GoodEvent_gridTime_zero] at h
  have hukv : gridTime s v K n k ≤ v n := GoodEvent_gridTime_le hsv hk
  have huk1 : gridTime s v K n k < 1 := (hukv.trans hvt).trans_lt ht1
  have hxk : 0 < 1 - gridTime s v K n k := by linarith
  have hkΔ : (k : ℝ) * gridStep s v K n ≤ 1 := by
    have : gridTime s v K n k = s n + k * gridStep s v K n := rfl
    linarith
  -- `√N`
  set sN : ℝ := ((d.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) with hsNdef
  have hsN0 : 0 < sN := Real.rpow_pos_of_pos hN0 _
  have hsN2 : sN ^ 2 = ((d.size n : ℕ) : ℝ) := by
    rw [hsNdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hWsN : (d.W n : ℝ) ≤ sN := by
    have h := Real.rpow_le_rpow (by positivity) hWN (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_two, ← Real.rpow_mul hW0.le, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      Real.rpow_one] at h
  -- the window ratio `r_t = x_s/x_t`: `r_t^{30} ≤ M_s ≤ W²`
  have hMs := LemDecCalE_scaleM_le_sq (L := d.L n) (W := d.W n) (E := E n) hLn hE hs1
  have hMs0 : 0 < scaleM (d.L n) (d.W n) (E n) (s n) := scaleM_pos hLn hWn hE hs1
  have hrt30 : ((1 - s n) / (1 - t n)) ^ 30 ≤ (d.W n : ℝ) ^ 2 := by
    have hpos : 0 < ((1 - s n) / (1 - t n)) ^ 30 := by positivity
    have e : ((1 - t n) / (1 - s n)) ^ 30 = (((1 - s n) / (1 - t n)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [e] at hstep
    exact ((inv_le_inv₀ hMs0 hpos).1 hstep).trans hMs
  -- `L^{14} N^ε ≤ W^{(7+ε)/c}`
  have hLN14 : (d.L n : ℝ) ^ 14 * ((d.size n : ℕ) : ℝ) ^ ε ≤
      (d.W n : ℝ) ^ ((7 + ε) / c) := by
    have h1 : (d.L n : ℝ) ^ 14 ≤ ((d.size n : ℕ) : ℝ) ^ 7 := by
      rw [show (d.L n : ℝ) ^ 14 = ((d.L n : ℝ) ^ 2) ^ 7 by ring]
      exact pow_le_pow_left₀ (by positivity) hLN 7
    have h2 : ((d.size n : ℕ) : ℝ) ^ 7 * ((d.size n : ℕ) : ℝ) ^ ε =
        (((d.size n : ℕ) : ℝ) ^ c) ^ ((7 + ε) / c) := by
      rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hc.ne', Real.rpow_add hN0,
        show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (d.L n : ℝ) ^ 14 * ((d.size n : ℕ) : ℝ) ^ ε
        ≤ ((d.size n : ℕ) : ℝ) ^ 7 * ((d.size n : ℕ) : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
      _ = _ := h2
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hband
          (div_nonneg (by linarith) hc.le)
  -- the mesh in the form `Δ ≤ N^{-D} (√N)^{-20}`
  have hΔY : gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-D) * (sN ^ 20)⁻¹ := by
    have e : ((d.size n : ℕ) : ℝ) ^ (-(D + 10)) = ((d.size n : ℕ) : ℝ) ^ (-D) * (sN ^ 20)⁻¹ := by
      rw [show -(D + 10) = -D + -10 by ring, Real.rpow_add hN0, Real.rpow_neg hN0.le 10,
        show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← hsN2, ← pow_mul]
    rw [← e]; exact hmesh
  -- the tail
  set T : ℝ := tailT (d.L n) (d.W n) (E n) D (gridTime s v K n k)
    (zdist2 (d.L n) (a.1 - a.2) : ℝ) with hTdef
  have hTW : (d.W n : ℝ) ^ (-D) ≤ T := by
    rw [hTdef]; unfold tailT
    have : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) (a.1 - a.2) : ℝ) /
          ellT (d.L n) (gridTime s v K n k))) := by positivity
    linarith
  have hWD0 : 0 ≤ (d.W n : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hT0 : 0 ≤ T := hWD0.trans hTW
  have hT2W : ((d.W n : ℝ) ^ (-D)) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hWD0 hTW 2
  have hND : ((d.size n : ℕ) : ℝ) ^ (-D) ≤ ((d.W n : ℝ) ^ (-D)) ^ 2 := by
    rw [GoodEventClose_sq_rpow hW0.le, Real.rpow_mul hW0.le, Real.rpow_two]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hWN (by linarith)
  have hNfloor : ∀ C' : ℝ, D + 1 ≤ C' →
      ((d.size n : ℕ) : ℝ) ^ (-C') ≤ ((d.size n : ℕ) : ℝ) ^ (-D) / 10 := by
    intro C' hC'
    have h1 : ((d.size n : ℕ) : ℝ) ^ (-C') ≤ ((d.size n : ℕ) : ℝ) ^ (-D + -1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_add hN0, Real.rpow_neg_one] at h1
    have h2 : ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 10 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN10
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le (-D))
    linarith
  have hNCc := hNfloor Cc hCc
  have hNCx := hNfloor Cx hCx
  have hNCc0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-Cc) := Real.rpow_nonneg hN0.le _
  have hND0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
  -- the loss `L0` and the indicator `I`
  set L0 : ℝ := lossE2 (d.L n) (d.W n) (((d.size n : ℕ) : ℝ) ^ ε)
      (180 * 40002 ^ 2 * (1 + Real.log (d.L n))) *
    Real.exp (2 * Real.log (d.W n) ^ ((3 : ℝ) / 4)) with hL0def
  have hL00 : 0 ≤ L0 := by
    have : 0 ≤ Real.log (d.W n : ℝ) := Real.log_nonneg hW1
    rw [hL0def]; unfold lossE2; positivity
  set I : ℝ := if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
      5 * ellStar (d.L n) (d.W n) (gridTime s v K n k) then 1 else 0 with hIdef
  have hI0 : 0 ≤ I := by rw [hIdef]; split_ifs <;> norm_num
  have hI2 : I ^ 2 = I := by rw [hIdef]; split_ifs <;> norm_num
  set Frem : ℝ := ((d.W n : ℝ) ^ (-D)) ^ 2 / 4 + ((d.size n : ℕ) : ℝ) ^ (-D) / 4 +
    4 * ((d.size n : ℕ) : ℝ) ^ (-Cc) with hFremdef
  have hFrem0 : 0 ≤ Frem := by positivity
  -- per-index bounds on `4 cZ`
  have hper : ∀ j ∈ Finset.range k, 4 * cZ d E s v K δ D ε D' Cc n k a j ≤
      8 * L0 * T ^ 2 * (gridStep s v K n *
        (((1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)) ^ 4 *
          ((etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 10 * I +
            (etaT (E n) (gridTime s v K n j))⁻¹ *
              (ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n)) ^ 3 *
              (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ ((1 : ℝ) / 2) *
              thr d E s δ n (gridTime s v K n j) ^ 2 +
            (etaT (E n) (gridTime s v K n k))⁻¹ *
              (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ *
              thr d E s δ n (gridTime s v K n j) ^ 3))) +
        gridStep s v K n * Frem := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    have hj1k : gridTime s v K n (j + 1) ≤ gridTime s v K n k :=
      GoodEvent_gridTime_mono hsv hjk
    have hujk : gridTime s v K n j ≤ gridTime s v K n k :=
      GoodEvent_gridTime_mono hsv hjk.le
    have huj1 : gridTime s v K n j < 1 := hujk.trans_lt huk1
    have hujt : gridTime s v K n j ≤ t n := (hujk.trans hukv).trans hvt
    have hsuj := hsle j
    have hsuj1 := hsle (j + 1)
    -- `R = x_{j+1}/x_k`
    have hR0 : 0 ≤ (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k) :=
      div_nonneg (by linarith) hxk.le
    have hRrt : (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k) ≤
        (1 - s n) / (1 - t n) :=
      calc (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k)
          ≤ (1 - s n) / (1 - gridTime s v K n k) :=
            div_le_div_of_nonneg_right (by linarith) hxk.le
        _ ≤ (1 - s n) / (1 - t n) :=
            div_le_div_of_nonneg_left hS0.le hxt (by linarith)
    set R : ℝ := (1 - gridTime s v K n (j + 1)) / (1 - gridTime s v K n k) with hRdef
    have hR30 : R ^ 30 ≤ (d.W n : ℝ) ^ 2 := (pow_le_pow_left₀ hR0 hRrt 30).trans hrt30
    have hR3 : R ^ 3 ≤ (d.W n : ℝ) ^ ((1 : ℝ) / 5) := by
      refine le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (Real.rpow_nonneg hW0.le _) ?_
      have e : ((d.W n : ℝ) ^ ((1 : ℝ) / 5)) ^ 10 = (d.W n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_two]; norm_num
      rw [e, ← pow_mul]; exact hR30
    have hR4 : R ^ 4 ≤ (d.W n : ℝ) := by
      by_cases hR1 : R ≤ 1
      · exact (pow_le_one₀ hR0 hR1).trans hW1
      · replace hR1 := lt_of_not_ge hR1
        refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hW0.le ?_
        calc (R ^ 4) ^ 2 = R ^ 8 := by ring
          _ ≤ R ^ 30 := pow_le_pow_right₀ hR1.le (by norm_num)
          _ ≤ _ := hR30
    -- far-kernel part
    have hρ0 : 0 ≤ ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n) :=
      div_nonneg (ellT_pos_le hLn huj1).1.le (ellT_pos_le hLn hs1).1.le
    have hρL : ellT (d.L n) (gridTime s v K n j) / ellT (d.L n) (s n) ≤ (d.L n : ℝ) :=
      (div_le_self (ellT_pos_le hLn huj1).1.le (one_le_ellT hLn hs0 hs1)).trans
        (ellT_pos_le hLn huj1).2
    have hMj1 : 1 ≤ scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j) := by
      have h29 := scaleM_ge_pow29 hLn hWn hE hs0 hsuj hujt ht1 hstep
      have h1 : 1 ≤ (1 - s n) / (1 - gridTime s v K n j) := by
        rw [one_le_div (by linarith)]; linarith
      exact (one_le_pow₀ h1).trans h29
    have hμ0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ 5 := by
      have := zero_lt_one.trans_le hMj1; positivity
    have hμ1 : (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n j))⁻¹ ^ 5 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 (zero_le_one.trans hMj1)) (inv_le_one_of_one_le₀ hMj1)
    have hD'' : (7 + ε) / c + 3 + 2 * D ≤ D' := by linarith
    have hF := GoodEventClose_far_le (D := D) (e := (7 + ε) / c) hW1 hρ0 hρL
      hμ0 hμ1 (pow_nonneg hR0 3) hR3 (Real.rpow_nonneg hN0.le ε) hLN14 hD'' hW256
    -- shift part
    have hηj1 : ((d.size n : ℕ) : ℝ)⁻¹ * cκ ≤ etaT (E n) (gridTime s v K n (j + 1)) := by
      have h1 : ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 - gridTime s v K n (j + 1) := by
        have h2 : ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ') :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        rw [Real.rpow_neg_one] at h2
        linarith
      unfold etaT
      exact mul_le_mul h1 hm hcκ.le (by linarith)
    have hei0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ :=
      inv_nonneg.2 (etaT_pos hE (hj1k.trans_lt huk1)).le
    have hei : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ sN ^ 2 * cκ⁻¹ := by
      have h := inv_anti₀ (by positivity) hηj1
      rwa [mul_inv, inv_inv, ← hsN2] at h
    have hSh := GoodEventClose_shift_le (R4 := R ^ 4) (N2 := ((d.size n : ℕ) : ℝ) ^ 2)
      (hR4.trans hWsN) hsN0 (by rw [← hsN2]; ring) hei0 hei hΔ0 hΔY hND0
      (inv_nonneg.2 hcκ.le) hN512
    unfold cZ
    exact GoodEventClose_cZ_alg hΔ0 hF hSh
  -- summing
  have hTS := GoodEventClose_timeSums (d := d) (E := E) (δ := δ) hE hs0 hsv
    (hvt.trans_lt ht1) hk hI0
  set P : ℝ := (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 5 * I +
      ((d.size n : ℕ) : ℝ) ^ (2 * δ) *
        (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((19 : ℝ) / 2) *
        (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 2) +
      ((d.size n : ℕ) : ℝ) ^ (3 * δ) *
        (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 12 *
        (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ with hPdef
  set A : ℝ := 8 * L0 / (spectralM (E n)).im with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hr0 : 0 ≤ etaT (E n) (s n) / etaT (E n) (gridTime s v K n k) :=
    div_nonneg (etaT_pos hE hs1).le (etaT_pos hE huk1).le
  have hMk0 : 0 < scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k) :=
    scaleM_pos hLn hWn hE huk1
  have hμk0 : 0 ≤ (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ :=
    inv_nonneg.2 hMk0.le
  have hP0 : 0 ≤ P := by positivity
  set X : ℝ := 4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j +
    ((d.size n : ℕ) : ℝ) ^ (-Cx) with hXdef
  have hX : X ≤ T ^ 2 * (A * P + 1) := by
    have hsum : 4 * ∑ j ∈ Finset.range k, cZ d E s v K δ D ε D' Cc n k a j ≤
        8 * L0 * T ^ 2 * (((spectralM (E n)).im)⁻¹ * P) + Frem := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum hper).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left hTS (by positivity : 0 ≤ 8 * L0 * T ^ 2)
      have h2 : (k : ℝ) * (gridStep s v K n * Frem) ≤ Frem := by
        rw [← mul_assoc]; exact mul_le_of_le_one_left hFrem0 hkΔ
      linarith
    have hrem : Frem + ((d.size n : ℕ) : ℝ) ^ (-Cx) ≤ T ^ 2 := by
      rw [hFremdef]; linarith
    have e : 8 * L0 * T ^ 2 * (((spectralM (E n)).im)⁻¹ * P) = T ^ 2 * (A * P) := by
      rw [hAdef]; ring
    have hX1 : X ≤ T ^ 2 * (A * P) + (Frem + ((d.size n : ℕ) : ℝ) ^ (-Cx)) := by
      rw [hXdef, ← e]; linarith
    calc X ≤ T ^ 2 * (A * P) + (Frem + ((d.size n : ℕ) : ℝ) ^ (-Cx)) := hX1
      _ ≤ T ^ 2 * (A * P) + T ^ 2 := by linarith
      _ = T ^ 2 * (A * P + 1) := by ring
  -- the control
  set r : ℝ := etaT (E n) (s n) / etaT (E n) (gridTime s v K n k) with hrdef
  set μ : ℝ := (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ with hμdef
  set a1 : ℝ := r ^ ((5 : ℝ) / 2) with ha1def
  set b1 : ℝ := ((d.size n : ℕ) : ℝ) ^ δ * r ^ ((19 : ℝ) / 4) * μ ^ ((1 : ℝ) / 4) with hb1def
  set c1 : ℝ := ((d.size n : ℕ) : ℝ) ^ (3 * δ / 2) * r ^ 6 * μ ^ ((1 : ℝ) / 2) with hc1def
  have ha10 : 0 ≤ a1 := Real.rpow_nonneg hr0 _
  have hb10 : 0 ≤ b1 := by positivity
  have hc10 : 0 ≤ c1 := by positivity
  have ha1 : a1 ^ 2 = r ^ 5 := by
    rw [ha1def, GoodEventClose_sq_rpow hr0, show (2 : ℝ) * (5 / 2) = ((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hb1 : b1 ^ 2 = ((d.size n : ℕ) : ℝ) ^ (2 * δ) * r ^ ((19 : ℝ) / 2) *
      μ ^ ((1 : ℝ) / 2) := by
    rw [hb1def, mul_pow, mul_pow, GoodEventClose_sq_rpow hN0.le, GoodEventClose_sq_rpow hr0,
      GoodEventClose_sq_rpow hμk0]
    norm_num
  have hc1 : c1 ^ 2 = ((d.size n : ℕ) : ℝ) ^ (3 * δ) * r ^ 12 * μ := by
    rw [hc1def, mul_pow, mul_pow, GoodEventClose_sq_rpow hN0.le, GoodEventClose_sq_rpow hμk0,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, show 2 * (3 * δ / 2) = 3 * δ by ring,
      ← pow_mul]
  have hPC : P ≤ (a1 * I + b1 + c1) ^ 2 := by
    have eP : P = a1 ^ 2 * I + b1 ^ 2 + c1 ^ 2 := by rw [ha1, hb1, hc1]
    have h0 : 0 ≤ a1 * I * b1 + a1 * I * c1 + b1 * c1 :=
      add_nonneg (add_nonneg (mul_nonneg (mul_nonneg ha10 hI0) hb10)
        (mul_nonneg (mul_nonneg ha10 hI0) hc10)) (mul_nonneg hb10 hc10)
    calc P = a1 ^ 2 * I + b1 ^ 2 + c1 ^ 2 := eP
      _ ≤ a1 ^ 2 * I + b1 ^ 2 + c1 ^ 2 + 2 * (a1 * I * b1 + a1 * I * c1 + b1 * c1) := by
          linarith
      _ = a1 ^ 2 * I ^ 2 + b1 ^ 2 + c1 ^ 2 + 2 * (a1 * I * b1 + a1 * I * c1 + b1 * c1) := by
          rw [hI2]
      _ = (a1 * I + b1 + c1) ^ 2 := by ring
  have hC10 : 0 ≤ a1 * I + b1 + c1 := by positivity
  have hsq := GoodEventClose_sqrt_step hT0 hA0 hC10 hX hPC
  have hNd : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (δ / 16) := Real.rpow_nonneg hN0.le _
  unfold xZ azumaMm
  rw [← hL0def, ← hXdef]
  calc ((d.size n : ℕ) : ℝ) ^ (δ / 16) * Real.sqrt X
      ≤ ((d.size n : ℕ) : ℝ) ^ (δ / 16) * ((Real.sqrt A + 1) * (a1 * I + b1 + c1 + 1) * T) :=
        mul_le_mul_of_nonneg_left hsq hNd
    _ = _ := by rw [hAdef]; ring

/-- **The deterministic consequence of the Azuma event**: eventually in `n`, for
every `k ≤ K_n` and every label `a`,
`xZ(n, k, a) ≤ azumaMm(n) · Ctrl_k(a) · 𝒯_{u_k}(|a|)` with
`Ctrl_k(a) = r^{5/2}·1(|a| ≤ 5ℓ*_{u_k}) + N^δ r^{19/4} (M_{u_k}^{-1})^{1/4}
  + N^{3δ/2} r^6 (M_{u_k}^{-1})^{1/2} + 1`, `r = η_{s_n}/η_{u_k}`.
The eventual set does not depend on `k` or `a`. -/
theorem xZ_le_azumaMm {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    {s v t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c) (hband : Bandwidth d c) {τ' : ℝ} (hτ' : 0 ≤ τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    (δ : ℝ) {D ε D' Cc Cx : ℝ} (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hD' : 2 * D + 3 + (7 + ε) / c ≤ D') (hCc : D + 1 ≤ Cc) (hCx : D + 1 ≤ Cx) (K : ℕ → ℕ)
    (hmesh : ∀ᶠ n : ℕ in atTop, gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-(D + 10))) :
    ∀ᶠ n : ℕ in atTop, ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n),
      xZ d E s v K δ D ε D' Cc Cx n k a ≤ azumaMm d E δ ε n *
        ((etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((5 : ℝ) / 2) *
            (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
                5 * ellStar (d.L n) (d.W n) (gridTime s v K n k) then 1 else 0) +
          ((d.size n : ℕ) : ℝ) ^ δ *
            (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ ((19 : ℝ) / 4) *
            (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 4) +
          ((d.size n : ℕ) : ℝ) ^ (3 * δ / 2) *
            (etaT (E n) (s n) / etaT (E n) (gridTime s v K n k)) ^ 6 *
            (scaleM (d.L n) (d.W n) (E n) (gridTime s v K n k))⁻¹ ^ ((1 : ℝ) / 2) + 1) *
        tailT (d.L n) (d.W n) (E n) D (gridTime s v K n k)
          (zdist2 (d.L n) (a.1 - a.2) : ℝ) := by
  have hcκ := (GoodEventClose_im_ge hκ hE 0).1
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hW256 : ∀ᶠ n : ℕ in atTop, (256 : ℝ) ≤ (d.W n : ℝ) ^ ((4 : ℝ) / 5) := by
    filter_upwards [hband, GoodEventClose_eventually_const_le d
      (by positivity : (0 : ℝ) < c * (4 / 5)) hsize 256] with n hb h256
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (256 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (c * (4 / 5)) := h256
      _ = (((d.size n : ℕ) : ℝ) ^ c) ^ ((4 : ℝ) / 5) := by rw [Real.rpow_mul hN0]
      _ ≤ (d.W n : ℝ) ^ ((4 : ℝ) / 5) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hb (by norm_num)
  filter_upwards [hstep, hband, hrange, hmesh, hW256,
    GoodEventClose_eventually_const_le d (by norm_num : (0 : ℝ) < 1 / 2) hsize
      (512 * (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ ^ 7),
    hsize.eventually (eventually_ge_atTop 10)] with n h1 h2 h3 h4 h5 h6 h7 k hk a
  exact GoodEventClose_xZ_le_at hcκ (GoodEventClose_im_ge hκ hE n).2 (hE2 n) (hs0 n) (hsv n)
    (hvt n) (ht1 n) hc hτ' hD hε hD' hCc hCx h1 h2 h3 h4 h5 h6 h7 hk a

/-! ## The good event on the grid -/

variable (d) in
/-- **The Step 2 good event on the grid**, with
`τ = gridTauFull`:
(Z) the Azuma event of `highProb_azuma_grid'` for every `k ≤ K_n`;
(Y) the complement of the Chebyshev event of `cheb_grid_at_tau` at `k = τ`;
(G) `H_k ∈ G(u_k)` for every `k ≤ K_n`;
(I) the initial event of `highProb_init_grid`. -/
def goodEventGrid (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (δ D ε D' Cc Cx : ℝ) (n : ℕ) :
    Set (PathΩ d) :=
  {ω | ∀ k ≤ K n, ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(∑ j ∈ Finset.range (min k (gridTauFull d E s v K δ D ε n ω)),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n k) (Zvec d (E n) s v K n (j + 1) ω)) a‖
        < xZ d E s v K δ D ε D' Cc Cx n k a}
  ∩ {ω | ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (Yvec d (E n) s v K n (j + 1) ω)) a‖
        < tailT (d.L n) (d.W n) (E n) D (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (zdist2 (d.L n) (a.1 - a.2) : ℝ)}
  ∩ {ω | ∀ k ≤ K n, pathH d s v K n k ω ∈
      goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s v K n k) (((d.size n : ℕ) : ℝ) ^ ε)}
  ∩ {ω | (∀ a : Z2 (d.L n) × Z2 (d.L n), ‖Avec d (E n) s v K n 0 ω a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ (δ / 16) *
          tailT (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (zdist2 (d.L n) (a.1 - a.2) : ℝ))
      ∧ jStarMat (d.L n) (d.W n) (E n) D (gridTime s v K n 0) (pathH d s v K n 0 ω)
        < thr d E s δ n (gridTime s v K n 0)}

/-- Part (G) of the good event: `P(∃ k ≤ K_n, H_k ∉ G(u_k)) ≤ (K_n + 1) N^{-D₃}` from the
per-time bound of `goodSetPT` at the grid times, through the transfer law `map_pathH_eq`. -/
private theorem GoodEventClose_goodSet_union {E : ℕ → ℝ} {s v t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {ε D₃ : ℝ} (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hvt : v n ≤ t n)
    (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hG : ∀ u : TimeIcc s t n, Sizes.seqP d {ω | Sizes.seqHflow d n u ω ∉
        goodSet (d.L n) (d.W n) (E n) (s n) u (((d.size n : ℕ) : ℝ) ^ ε)} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₃))) :
    pathP d {ω | ∀ k ≤ K n, pathH d s v K n k ω ∈
        goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s v K n k) (((d.size n : ℕ) : ℝ) ^ ε)}ᶜ ≤
      ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-D₃)) := by
  set G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) := fun k =>
    goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s v K n k) (((d.size n : ℕ) : ℝ) ^ ε)
    with hGdef
  have hsub : {ω | ∀ k ≤ K n, pathH d s v K n k ω ∈ G k}ᶜ ⊆
      ⋃ k ∈ Finset.range (K n + 1), {ω | pathH d s v K n k ω ∉ G k} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨k, hk, hkG⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hkG
  have hone : ∀ k ∈ Finset.range (K n + 1), pathP d {ω | pathH d s v K n k ω ∉ G k} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₃)) := by
    intro k hk
    have hkK : k ≤ K n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have huk : gridTime s v K n k ≤ t n := (GoodEvent_gridTime_le hsv hkK).trans hvt
    have hsuk : s n ≤ gridTime s v K n k := by
      have h := GoodEvent_gridTime_mono (K := K) hsv (Nat.zero_le k)
      rwa [GoodEvent_gridTime_zero] at h
    have hmeas : MeasurableSet (G k)ᶜ :=
      (measurableGoodSet (d.L n) (d.W n) (E n) (s n) _ _ hE (huk.trans_lt ht1)).compl
    have hH : Measurable (pathH d s v K n k) :=
      Measurable.of_eval_matrix _ fun i j => measurable_pathH d s v K n k i j
    have hF : Measurable (Sizes.seqHflow d n (gridTime s v K n k)) :=
      Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n _ i j
    have h1 : pathP d {ω | pathH d s v K n k ω ∉ G k} =
        Sizes.seqP d {ω | Sizes.seqHflow d n (gridTime s v K n k) ω ∉ G k} := by
      have e1 := Measure.map_apply (μ := pathP d) hH hmeas
      have e2 := Measure.map_apply (μ := Sizes.seqP d) hF hmeas
      rw [map_pathH_eq d s v K n k hs0 hsv hK0] at e1
      exact e1.symm.trans e2
    rw [h1]
    exact hG ⟨gridTime s v K n k, hsuk, huk⟩
  calc pathP d {ω | ∀ k ≤ K n, pathH d s v K n k ω ∈ G k}ᶜ
      ≤ pathP d (⋃ k ∈ Finset.range (K n + 1), {ω | pathH d s v K n k ω ∉ G k}) :=
        measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (K n + 1), pathP d {ω | pathH d s v K n k ω ∉ G k} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (K n + 1), ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₃)) :=
        Finset.sum_le_sum hone
    _ = ENNReal.ofReal (((K n + 1 : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-D₃)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **The good event has high probability**: for every `D₁ > 0`,
on the grid `K = gridK d D (D₁ + 1)`, eventually `P(goodEventGridᶜ) ≤ N^{-D₁}`.  The four
parts are each `≤ N^{-(D₁+1)}`: (Z) `highProb_azuma_grid'`, (Y) `cheb_grid_at_tau`,
(G) `goodSetPT` through `map_pathH_eq` with a union over `K_n + 1 ≤ N^{CK+2}` grid times,
(I) `highProb_init_grid`. -/
theorem goodEvent_grid {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| < 2 - κ)
    {s v t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c) (hband : Bandwidth d c) {τ' : ℝ} (hτ' : 0 < τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    (hV3 : RBM.Green.GbEXPHypV3 d κ c τ') (hloop : Step1LoopPT d E s t)
    (hweak : Step1WeakLawPT d E s t) (hInit : InitDecay d E s)
    {δ D ε : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 200) (hD : 20 + 2 / c ≤ D) (hε : 0 < ε)
    (D' Cc Cx : ℝ) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      pathP d (goodEventGrid d E s v (gridK d D (D₁ + 1)) δ D ε D' Cc Cx n)ᶜ ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  have hD0 : 0 < D := by
    have : 0 < 2 / c := by positivity
    linarith
  set K : ℕ → ℕ := gridK d D (D₁ + 1) with hKdef
  have hK0 : ∀ n, K n ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hCK : 0 ≤ CK D (D₁ + 1) := by unfold CK; linarith
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hEle : ∀ n, |E n| ≤ 2 - κ := fun n => (hE n).le
  have hst : ∀ n, s n ≤ t n := fun n => (hsv n).trans (hvt n)
  have HZ := highProb_azuma_grid' hE2 hs0 hsv hvt ht1 hc hband hτ' hrange hstep hsize hδ0 hδc hD
    hε.le D' Cc Cx K (gridK_card_le hCK)
  have HI := highProb_init_grid hInit hE2 hs0 hsv (fun n => (hvt n).trans_lt (ht1 n)) hK0 hδ0
    hD0 hsize
  have HY := cheb_grid_at_tau hκ hEle hs0 hsv hvt ht1 hτ'.le hrange hsize hD0.le δ ε (D₁ + 1)
    (by linarith)
  set D₃ : ℝ := CK D (D₁ + 1) + 2 + (D₁ + 1) with hD₃
  have HG := goodSetPT d κ c τ' E s t hκ hc hτ' hV3 hsize hband hrange hstep hE hs0 hst ht1
    hloop hweak ε hε D₃ (by linarith)
  filter_upwards [HZ (D₁ + 1) (by linarith), HI (D₁ + 1) (by linarith), HY, HG,
    gridK_card_le (d := d) hCK] with n hZ hI hY hG hcard
  have hN1 := GoodEvent_one_le_size (d := d) n
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hN9 : (4 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    obtain ⟨hL1, hW1, -, -, -⟩ := GoodEventClose_sizes (d := d) n
    have h3 : (3 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast d.three_le_L n
    have hN : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
      rw [Sizes.size_eq]; push_cast; ring
    have hL2 : (9 : ℝ) ≤ (d.L n : ℝ) ^ 2 := by nlinarith
    have hW2 : (1 : ℝ) ≤ (d.W n : ℝ) ^ 2 := one_le_pow₀ hW1
    rw [hN]; nlinarith
  set x : ℝ := ((d.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  -- part (G)
  have hGpart := GoodEventClose_goodSet_union (hE2 n) (hs0 n) (hsv n) (hvt n) (ht1 n) (hK0 n) hG
  have hGx : ((K n + 1 : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (-D₃) ≤ x := by
    have e : ((d.size n : ℕ) : ℝ) ^ (CK D (D₁ + 1) + 2) * ((d.size n : ℕ) : ℝ) ^ (-D₃) = x := by
      rw [← Real.rpow_add hN0, hxdef, hD₃]; congr 1; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
  -- part (Y)
  have hYsub : {ω | ∀ a : Z2 (d.L n) × Z2 (d.L n),
      ‖(∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
          Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ) (gridTime s v K n (j + 1))
            (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (Yvec d (E n) s v K n (j + 1) ω)) a‖
        < tailT (d.L n) (d.W n) (E n) D (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (zdist2 (d.L n) (a.1 - a.2) : ℝ)}ᶜ ⊆
      {ω | ∃ a : Z2 (d.L n) × Z2 (d.L n),
        tailT (d.L n) (d.W n) (E n) D (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
            (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
          ‖(∑ j ∈ Finset.range (gridTauFull d E s v K δ D ε n ω),
              Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
                (gridTime s v K n (j + 1))
                (gridTime s v K n (gridTauFull d E s v K δ D ε n ω))
                (Yvec d (E n) s v K n (j + 1) ω)) a‖} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
    exact hω
  have hYp := (measure_mono (μ := pathP d) hYsub).trans hY
  -- the sum of the four parts
  unfold goodEventGrid
  rw [Set.compl_inter, Set.compl_inter, Set.compl_inter]
  calc pathP d (((_ᶜ ∪ _ᶜ) ∪ _ᶜ) ∪ _ᶜ)
      ≤ pathP d ((_ᶜ ∪ _ᶜ) ∪ _ᶜ) + pathP d _ := measure_union_le _ _
    _ ≤ (pathP d (_ᶜ ∪ _ᶜ) + pathP d _) + pathP d _ := by gcongr; exact measure_union_le _ _
    _ ≤ ((pathP d _ + pathP d _) + pathP d _) + pathP d _ := by
        gcongr; exact measure_union_le _ _
    _ ≤ ((ENNReal.ofReal x + ENNReal.ofReal x) + ENNReal.ofReal x) + ENNReal.ofReal x :=
        add_le_add (add_le_add (add_le_add hZ hYp) (hGpart.trans (ENNReal.ofReal_le_ofReal hGx)))
          hI
    _ = ENNReal.ofReal (4 * x) := by
        rw [← ENNReal.ofReal_add hx0 hx0, ← ENNReal.ofReal_add (by positivity) hx0,
          ← ENNReal.ofReal_add (by positivity) hx0]
        ring_nf
    _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hxdef, show -(D₁ + 1) = -D₁ + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
        have : 4 * ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hN9
        nlinarith

/-- **The deterministic consequences on the good event**:
for every `D₁ > 0`, with `K = gridK d D (D₁ + 1)`, eventually in `n`:
`1 ≤ K_n`, `Δ ≤ N^{-CK(D, D₁+1)}`, `0 ≤ azumaMm ≤ N^{δ/8 + 3ε}`; and for every `ω` in the
good event, with `τ = gridTauFull(ω) ≤ K_n`:
1. the initial event (I);
2. `‖(Σ_{j<τ} 𝒰_{u_{j+1}, u_τ} Zvec_{j+1})(a)‖ ≤ azumaMm · Ctrl_τ(a) · 𝒯_{u_τ}(|a|)`;
3. `‖(Σ_{j<τ} 𝒰_{u_{j+1}, u_τ} Yvec_{j+1})(a)‖ ≤ 𝒯_{u_τ}(|a|)`;
4. `J*_{u_j}(H_j) < Θ(u_j)` and `H_j ∈ G(u_j)` for `j < τ`;
5. `H_k ∈ G(u_k)` for every `k ≤ K_n`. -/
theorem goodEvent_grid_imp {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    {s v t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c) (hband : Bandwidth d c) {τ' : ℝ} (hτ' : 0 ≤ τ')
    (hrange : RangeCond d τ' t) (hstep : CondStInd d E s t) (hsize : RBM.Ind.SizeTendsto d)
    {δ D ε D' Cc Cx : ℝ} (hδ0 : 0 < δ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hD' : 2 * D + 3 + (7 + ε) / c ≤ D') (hCc : D + 1 ≤ Cc) (hCx : D + 1 ≤ Cx) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 ≤ gridK d D (D₁ + 1) n ∧
        gridStep s v (gridK d D (D₁ + 1)) n ≤ ((d.size n : ℕ) : ℝ) ^ (-CK D (D₁ + 1)) ∧
        0 ≤ azumaMm d E δ ε n ∧ azumaMm d E δ ε n ≤ ((d.size n : ℕ) : ℝ) ^ (δ / 8 + 3 * ε)) ∧
      ∀ ω ∈ goodEventGrid d E s v (gridK d D (D₁ + 1)) δ D ε D' Cc Cx n,
        ((∀ a : Z2 (d.L n) × Z2 (d.L n), ‖Avec d (E n) s v (gridK d D (D₁ + 1)) n 0 ω a‖ ≤
            ((d.size n : ℕ) : ℝ) ^ (δ / 16) *
              tailT (d.L n) (d.W n) (E n) D (gridTime s v (gridK d D (D₁ + 1)) n 0)
                (zdist2 (d.L n) (a.1 - a.2) : ℝ)) ∧
          jStarMat (d.L n) (d.W n) (E n) D (gridTime s v (gridK d D (D₁ + 1)) n 0)
              (pathH d s v (gridK d D (D₁ + 1)) n 0 ω)
            < thr d E s δ n (gridTime s v (gridK d D (D₁ + 1)) n 0)) ∧
        (∀ a : Z2 (d.L n) × Z2 (d.L n),
          ‖(∑ j ∈ Finset.range (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω),
              Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
                (gridTime s v (gridK d D (D₁ + 1)) n (j + 1))
                (gridTime s v (gridK d D (D₁ + 1)) n
                  (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))
                (Zvec d (E n) s v (gridK d D (D₁ + 1)) n (j + 1) ω)) a‖ ≤
            azumaMm d E δ ε n *
              ((etaT (E n) (s n) / etaT (E n) (gridTime s v (gridK d D (D₁ + 1)) n
                    (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))) ^ ((5 : ℝ) / 2) *
                  (if (zdist2 (d.L n) (a.1 - a.2) : ℝ) ≤
                      5 * ellStar (d.L n) (d.W n) (gridTime s v (gridK d D (D₁ + 1)) n
                        (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω)) then 1 else 0) +
                ((d.size n : ℕ) : ℝ) ^ δ *
                  (etaT (E n) (s n) / etaT (E n) (gridTime s v (gridK d D (D₁ + 1)) n
                    (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))) ^ ((19 : ℝ) / 4) *
                  (scaleM (d.L n) (d.W n) (E n) (gridTime s v (gridK d D (D₁ + 1)) n
                    (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω)))⁻¹ ^ ((1 : ℝ) / 4) +
                ((d.size n : ℕ) : ℝ) ^ (3 * δ / 2) *
                  (etaT (E n) (s n) / etaT (E n) (gridTime s v (gridK d D (D₁ + 1)) n
                    (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))) ^ 6 *
                  (scaleM (d.L n) (d.W n) (E n) (gridTime s v (gridK d D (D₁ + 1)) n
                    (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω)))⁻¹ ^ ((1 : ℝ) / 2) +
                1) *
              tailT (d.L n) (d.W n) (E n) D (gridTime s v (gridK d D (D₁ + 1)) n
                  (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))
                (zdist2 (d.L n) (a.1 - a.2) : ℝ)) ∧
        (∀ a : Z2 (d.L n) × Z2 (d.L n),
          ‖(∑ j ∈ Finset.range (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω),
              Uop (d.L n) ((Complex.normSq (spectralM (E n)) : ℝ) : ℂ)
                (gridTime s v (gridK d D (D₁ + 1)) n (j + 1))
                (gridTime s v (gridK d D (D₁ + 1)) n
                  (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))
                (Yvec d (E n) s v (gridK d D (D₁ + 1)) n (j + 1) ω)) a‖ ≤
            tailT (d.L n) (d.W n) (E n) D (gridTime s v (gridK d D (D₁ + 1)) n
                (gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω))
              (zdist2 (d.L n) (a.1 - a.2) : ℝ)) ∧
        (∀ j < gridTauFull d E s v (gridK d D (D₁ + 1)) δ D ε n ω,
          jStarMat (d.L n) (d.W n) (E n) D (gridTime s v (gridK d D (D₁ + 1)) n j)
              (pathH d s v (gridK d D (D₁ + 1)) n j ω) <
            thr d E s δ n (gridTime s v (gridK d D (D₁ + 1)) n j) ∧
          pathH d s v (gridK d D (D₁ + 1)) n j ω ∈ goodSet (d.L n) (d.W n) (E n) (s n)
            (gridTime s v (gridK d D (D₁ + 1)) n j) (((d.size n : ℕ) : ℝ) ^ ε)) ∧
        (∀ k ≤ gridK d D (D₁ + 1) n, pathH d s v (gridK d D (D₁ + 1)) n k ω ∈
          goodSet (d.L n) (d.W n) (E n) (s n) (gridTime s v (gridK d D (D₁ + 1)) n k)
            (((d.size n : ℕ) : ℝ) ^ ε)) := by
  intro D₁ hD₁
  set K : ℕ → ℕ := gridK d D (D₁ + 1) with hKdef
  have hK0 : ∀ n, K n ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hstepCK : ∀ n, gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-CK D (D₁ + 1)) := fun n =>
    step_gridK_le (by linarith [hs0 n, hvt n, ht1 n])
  have hmesh : ∀ᶠ n : ℕ in atTop, gridStep s v K n ≤ ((d.size n : ℕ) : ℝ) ^ (-(D + 10)) :=
    Eventually.of_forall fun n => (hstepCK n).trans
      (Real.rpow_le_rpow_of_exponent_le (GoodEvent_one_le_size n) (by unfold CK; linarith))
  filter_upwards [xZ_le_azumaMm hκ hE hs0 hsv hvt ht1 hc hband hτ' hrange hstep hsize δ hD hε
      hD' hCc hCx K hmesh, azumaMm_le hκ hE hsize hδ0 hε] with n hxZ hMm
  refine ⟨⟨Nat.one_le_iff_ne_zero.2 (hK0 n), hstepCK n, azumaMm_nonneg E δ ε n, hMm⟩, ?_⟩
  intro ω hω
  obtain ⟨⟨⟨hZ, hY⟩, hG⟩, hI⟩ := hω
  have hτK : gridTauFull d E s v K δ D ε n ω ≤ K n := gridTauFull_le E s v K δ D ε n ω
  refine ⟨hI, fun a => ?_, fun a => (hY a).le, fun j hj => lt_gridTauFull_imp hj, hG⟩
  have h1 := hZ _ hτK a
  rw [min_self] at h1
  exact h1.le.trans (hxZ _ hτK a)

end RBM.Path
