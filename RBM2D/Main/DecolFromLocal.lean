/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Endpoints

/-!
# `MR:decol` from `MR:locSC`

`decol_of_locSC : locSC → decol`: the deduction of delocalization from the local semicircle law
(the endpoint statements of `RBM2D/Endpoints.lean`).

Proof: apply `locSC` at `τ'' = min(τ, 𝔠, 1)/2` and `D' = D + 2`; take the energy net
`E_j = min(2 - κ, -2 + κ + j/N)`, `j ≤ 4N`, at `η = N^{-1+τ''}`; for any orthonormal
eigenbasis, `|ψ_k(x)|² ≤ 2η Im G_xx(E_j + iη)` when `|μ_k - E_j| ≤ η`; the local law bounds
`Im G_xx ≤ |mSC| + 1 ≤ 2`; a union bound over the `4N + 1` net points.
-/

namespace RBM.Endpoints

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes

/-! ### Spectral identity for any orthonormal eigenbasis -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- `G_xx(z) = ∑_l |ψ_l(x)|² / (μ_l - z)` for any orthonormal eigenbasis `(μ, ψ)`. -/
private theorem DecolFromLocal_green_apply_self (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) (x : ι) :
    green H z x x = ∑ l, (Complex.normSq (ψ l x) : ℂ) / ((μ l : ℂ) - z) := by
  set U : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y with hU
  have hUU : star U * U = 1 := by
    ext k k'
    have h := hψ.1 k k'
    simp only [dotProduct, Pi.star_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, hU, Matrix.of_apply, Matrix.one_apply]
    exact h
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - z • 1) * U = U * diagonal (fun l => (μ l : ℂ) - z) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hinv : green H z = U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    calc (H - z • 1) * (U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U)
        = ((H - z • 1) * U) * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun l => (μ l : ℂ) - z)
            * diagonal (fun l => ((μ l : ℂ) - z)⁻¹)) * star U := by
          rw [hsub]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          have hd : (fun l => ((μ l : ℂ) - z) * ((μ l : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
            funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
          rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']
  rw [hinv, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, star_apply, Complex.normSq_eq_conj_mul_self]
  simp only [hU, Matrix.of_apply, RCLike.star_def]
  ring

/-- `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((μ_l - E)² + η²)` for any orthonormal
eigenbasis `(μ, ψ)`. -/
private theorem DecolFromLocal_im_green_apply_self (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ)
    {η : ℝ} (hη : η ≠ 0) (x : ι) :
    (green H (E + η * Complex.I) x x).im
      = ∑ l, η * Complex.normSq (ψ l x) / ((μ l - E) ^ 2 + η ^ 2) := by
  have hz : ∀ l, (μ l : ℂ) ≠ E + η * Complex.I := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hη this.symm
  rw [DecolFromLocal_green_apply_self hψ hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : Complex.normSq ((μ l : ℂ) - (E + η * Complex.I)) = (μ l - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have him : ((μ l : ℂ) - (E + η * Complex.I)).im = -η := by simp
  have hpos : 0 < (μ l - E) ^ 2 + η ^ 2 := by positivity
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him]
  field_simp

/-- If `|μ_k - E| ≤ η`, then `|ψ_k(x)|² ≤ 2η Im G_xx(E + iη)`. -/
private theorem DecolFromLocal_sq_le_two_mul_im_green (hψ : IsOrthoEigenbasis H μ ψ)
    {E η : ℝ} (hη : 0 < η) {k : ι} (hk : |μ k - E| ≤ η) (x : ι) :
    ‖ψ k x‖ ^ 2 ≤ 2 * η * (green H (E + η * Complex.I) x x).im := by
  rw [DecolFromLocal_im_green_apply_self hψ E hη.ne' x, Finset.mul_sum]
  have hterm : ∀ l ∈ Finset.univ,
      0 ≤ 2 * η * (η * Complex.normSq (ψ l x) / ((μ l - E) ^ 2 + η ^ 2)) := by
    intro l _
    have := Complex.normSq_nonneg (ψ l x)
    positivity
  refine le_trans ?_ (Finset.single_le_sum hterm (Finset.mem_univ k))
  have hden : 0 < (μ k - E) ^ 2 + η ^ 2 := by positivity
  have hsq : (μ k - E) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  rw [Complex.normSq_eq_norm_sq, mul_div_assoc', le_div_iff₀ hden]
  have h0 : 0 ≤ ‖ψ k x‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq h0]

end Spectral

/-! ### The energy net -/

/-- The net point `E_j = min(2 - κ, -2 + κ + j/N)`. -/
private noncomputable def DecolFromLocal_net (κ : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  min (2 - κ) (-2 + κ + (j : ℝ) / N)

private theorem DecolFromLocal_abs_net_le {κ : ℝ} (hκ2 : κ ≤ 2) (N j : ℕ) :
    |DecolFromLocal_net κ N j| ≤ 2 - κ := by
  unfold DecolFromLocal_net
  have hj : 0 ≤ (j : ℝ) / N := by positivity
  rw [abs_le]
  constructor
  · rw [le_min_iff]; constructor <;> linarith
  · exact min_le_left _ _

private theorem DecolFromLocal_exists_net_close {κ : ℝ} (hκ0 : 0 ≤ κ) {N : ℕ} (hN : 0 < N)
    {E : ℝ} (hE : E ∈ Set.Icc (-2 + κ) (2 - κ)) :
    ∃ j : Fin (4 * N + 1), |E - DecolFromLocal_net κ N j| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ (E + 2 - κ) * N := by
    have := hE.1
    have : 0 ≤ E + 2 - κ := by linarith
    positivity
  set j := ⌊(E + 2 - κ) * N⌋₊ with hj
  have hjle : (j : ℝ) ≤ (E + 2 - κ) * N := Nat.floor_le ha
  have hjlt : (E + 2 - κ) * N < j + 1 := Nat.lt_floor_add_one _
  have hj4 : j < 4 * N + 1 := by
    have h1 : (j : ℝ) ≤ 4 * N := by
      have := hE.2
      nlinarith
    have h2 : (j : ℝ) < 4 * N + 1 := by linarith
    exact_mod_cast h2
  refine ⟨⟨j, hj4⟩, ?_⟩
  have hdiv : (j : ℝ) / N ≤ E + 2 - κ := by rwa [div_le_iff₀ hNr]
  have hdiv' : E + 2 - κ < ((j : ℝ) + 1) / N := by rwa [lt_div_iff₀ hNr]
  have hnet : DecolFromLocal_net κ N j = -2 + κ + (j : ℝ) / N := by
    unfold DecolFromLocal_net
    apply min_eq_right
    have := hE.2
    linarith
  simp only [hnet]
  have hNinv : 0 < 1 / (N : ℝ) := by positivity
  rw [abs_le]
  constructor
  · linarith
  · rw [add_div] at hdiv'
    linarith

/-! ### The local-law error at `η = N^{-1+τ''}` is at most `1` -/

private theorem DecolFromLocal_err_le_one (L W : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (z : ℂ)
    (hz : z.im = (((W * L) ^ 2 : ℕ) : ℝ) ^ (-1 + θ)) :
    (W : ℝ) ^ θ / Real.sqrt (Meta L W z) ≤ 1 := by
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNeq : N = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    rw [hNdef]; push_cast; ring
  have hNpos : 0 < N := by rw [hNeq]; positivity
  set η := z.im with hηdef
  have hηpos : 0 < η := by rw [hz]; exact Real.rpow_pos_of_pos hNpos _
  have hWθ : 0 < (W : ℝ) ^ θ := Real.rpow_pos_of_pos (by linarith) _
  -- it suffices that `W^{2θ} ≤ M_η`
  suffices hM : ((W : ℝ) ^ θ) ^ 2 ≤ Meta L W z by
    have hs : (W : ℝ) ^ θ ≤ Real.sqrt (Meta L W z) := (Real.le_sqrt' hWθ).mpr hM
    have hspos : 0 < Real.sqrt (Meta L W z) := lt_of_lt_of_le hWθ hs
    rw [div_le_one hspos]
    exact hs
  have hW2θ : ((W : ℝ) ^ θ) ^ 2 = ((W : ℝ) ^ 2) ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast (W : ℝ) 2,
      ← Real.rpow_mul (by linarith), mul_comm]
  unfold Meta ellz
  rw [← hηdef]
  set m := min (η ^ (-(1 / 2 : ℝ))) (L : ℝ) with hm
  have hm0 : 0 ≤ m := le_min (Real.rpow_nonneg hηpos.le _) (by linarith)
  rcases min_choice (η ^ (-(1 / 2 : ℝ))) (L : ℝ) with hmin | hmin
  · -- `ℓ²η ≥ 1`
    have hmeq : m = η ^ (-(1 / 2 : ℝ)) := hm.trans hmin
    have hℓ : (η ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (m + 1) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hηpos.le _) (by rw [hmeq]; linarith) 2
    have hsq : (η ^ (-(1 / 2 : ℝ))) ^ 2 * η = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hηpos.le]
      norm_num
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hηpos.ne']
    have h1 : 1 ≤ (m + 1) ^ 2 * η :=
      calc (1 : ℝ) = (η ^ (-(1 / 2 : ℝ))) ^ 2 * η := hsq.symm
        _ ≤ (m + 1) ^ 2 * η := mul_le_mul_of_nonneg_right hℓ hηpos.le
    have h2 : ((W : ℝ) ^ θ) ^ 2 ≤ (W : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast (W : ℝ) 2]
      apply Real.rpow_le_rpow_of_exponent_le hWr
      push_cast
      linarith
    calc ((W : ℝ) ^ θ) ^ 2 ≤ (W : ℝ) ^ 2 * 1 := by rw [mul_one]; exact h2
      _ ≤ (W : ℝ) ^ 2 * ((m + 1) ^ 2 * η) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (W : ℝ) ^ 2 * (m + 1) ^ 2 * η := by ring
  · -- `M_η ≥ W² L² η = N^θ`
    have hmeq : m = (L : ℝ) := hm.trans hmin
    have hℓ : (L : ℝ) ^ 2 ≤ (m + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by rw [hmeq]; linarith) 2
    have hNη : N * η = N ^ θ := by
      have hsplit : N ^ θ = N ^ (1 : ℝ) * N ^ (-1 + θ) := by
        rw [← Real.rpow_add hNpos]; ring_nf
      rw [hsplit, Real.rpow_one, hz]
    have h2 : ((W : ℝ) ^ 2) ^ θ ≤ N ^ θ := by
      apply Real.rpow_le_rpow (by positivity) _ hθ0
      rw [hNeq]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLr)
    calc ((W : ℝ) ^ θ) ^ 2 = ((W : ℝ) ^ 2) ^ θ := hW2θ
      _ ≤ N ^ θ := h2
      _ = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * η := by rw [← hNη, hNeq]
      _ ≤ (W : ℝ) ^ 2 * (m + 1) ^ 2 * η := by
          apply mul_le_mul_of_nonneg_right _ hηpos.le
          exact mul_le_mul_of_nonneg_left hℓ (by positivity)


/-! ### The deduction -/

/-- **`MR:decol` from `MR:locSC`** (Theorem `MR:decol`; the paper deduces it from `MR:locSC` in
the paragraph following Theorem `MR:QDiff`, without details). -/
theorem decol_of_locSC : locSC → decol := by
  intro hloc 𝔠 h𝔠 d hAdm κ τ D hκ hτ hD
  -- Step 0: `κ > 2`, empty bulk
  by_cases hκ2 : 2 < κ
  · refine Filter.Eventually.of_forall fun n => ?_
    have hempty : {ω | ¬ decolEvent d n κ τ ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro μ ψ _ k hk
      exact absurd (hk.1.trans hk.2) (by linarith)
    rw [hempty, measure_empty]
    exact zero_le
  push Not at hκ2
  -- the exponent `τ'' = min(τ, 𝔠, 1)/2`
  set θ : ℝ := min τ (min 𝔠 1) / 2 with hθdef
  have hθpos : 0 < θ := div_pos (lt_min hτ (lt_min h𝔠 one_pos)) two_pos
  have hθ1 : θ ≤ 1 / 2 := by
    have : min τ (min 𝔠 1) ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    rw [hθdef]; linarith
  have hθτ : θ ≤ τ / 2 := by
    have : min τ (min 𝔠 1) ≤ τ := min_le_left _ _
    rw [hθdef]; linarith
  -- Step 1: apply `locSC` at `(𝔠, d, κ, τ'', D + 2)`
  have hloc' := hloc 𝔠 h𝔠 d hAdm κ θ (D + 2) hκ hθpos (by linarith)
  have hNt : Tendsto (fun n => ((d.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hAdm.1
  have h5 : ∀ᶠ n in atTop, (5 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := hNt.eventually_ge_atTop 5
  have h4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (τ - θ) :=
    ((tendsto_rpow_atTop (by linarith)).comp hNt).eventually_ge_atTop 4
  filter_upwards [hloc', h5, h4] with n hn hN5 hN4
  set N : ℕ := d.size n with hNdef
  have hNr : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNr
  set η : ℝ := (N : ℝ) ^ (-1 + θ) with hηdef
  have hηpos : 0 < η := Real.rpow_pos_of_pos hNr _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hinvη : 1 / (N : ℝ) ≤ η := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  -- Step 2: the net points lie in the spectral domain
  let z : Fin (4 * N + 1) → ℂ := fun j => (DecolFromLocal_net κ N j : ℂ) + η * Complex.I
  have hzre : ∀ j, (z j).re = DecolFromLocal_net κ N j := fun j => by simp [z]
  have hzim : ∀ j, (z j).im = η := fun j => by simp [z]
  have hzdom : ∀ j, locDomain N κ θ (z j) := by
    intro j
    refine ⟨?_, ?_, ?_⟩
    · rw [hzre]; exact DecolFromLocal_abs_net_le hκ2 N j
    · rw [hzim]
    · rw [hzim]; exact hη1
  let B : Fin (4 * N + 1) → Set (SeqΩ d) := fun j =>
    {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
      ‖Gn d n ω (z j) x y - (if x = y then mSC (z j) else 0)‖ ≤
        (d.W n : ℝ) ^ θ / Real.sqrt (Meta (d.L n) (d.W n) (z j))}
  have hB : ∀ j, seqP d (B j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
    fun j => (hn (z j) (hzdom j)).1
  -- Steps 3–4: off `⋃ B j`, `decolEvent` holds
  have hsub : {ω | ¬ decolEvent d n κ τ ω} ⊆ ⋃ j, B j := by
    intro ω hω
    by_contra hnot
    apply hω
    simp only [Set.mem_iUnion, not_exists, B, Set.mem_ofPred_eq, not_not] at hnot
    intro μ ψ hψ k hk x
    obtain ⟨j, hj⟩ := DecolFromLocal_exists_net_close hκ.le hNpos hk
    have hG := hnot j x x
    simp only [eq_self, ite_true] at hG
    have herr : (d.W n : ℝ) ^ θ / Real.sqrt (Meta (d.L n) (d.W n) (z j)) ≤ 1 :=
      DecolFromLocal_err_le_one (d.L n) (d.W n) (by have := d.three_le_L n; omega)
        (d.W_pos n) hθpos.le hθ1 (z j) (by rw [hzim, hηdef]; rfl)
    have hzpos : 0 < (z j).im := by rw [hzim]; exact hηpos
    have hm : ‖mSC (z j)‖ < 1 := by
      rw [mSC_eq_msc hzpos]; exact norm_msc_lt_one hzpos
    have hGn : ‖Gn d n ω (z j) x x‖ ≤ 2 := by
      have := norm_sub_norm_le (Gn d n ω (z j) x x) (mSC (z j))
      linarith
    have hsq := DecolFromLocal_sq_le_two_mul_im_green hψ hηpos
      (E := DecolFromLocal_net κ N j) (k := k) (hj.trans hinvη) x
    have him : (green (seqXmat d n ω) (z j) x x).im ≤ 2 := (Complex.im_le_norm _).trans hGn
    calc ‖ψ k x‖ ^ 2
        ≤ 2 * η * (green (seqXmat d n ω) (z j) x x).im := hsq
      _ ≤ 2 * η * 2 := by gcongr
      _ = η * 4 := by ring
      _ ≤ η * (N : ℝ) ^ (τ - θ) := by gcongr
      _ = (N : ℝ) ^ (-1 + τ) := by
          rw [hηdef, ← Real.rpow_add hNr]; ring_nf
  -- Step 5: union bound
  have hreal : ((4 * N + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-D) := by
    rw [show -D = -(D + 2) + 2 by ring, Real.rpow_add hNr, Real.rpow_two, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNr.le _)
    push_cast
    nlinarith
  calc seqP d {ω | ¬ decolEvent d n κ τ ω}
      ≤ seqP d (⋃ j, B j) := measure_mono hsub
    _ ≤ ∑ j, seqP d (B j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin (4 * N + 1), ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
        Finset.sum_le_sum fun j _ => hB j
    _ = ENNReal.ofReal (((4 * N + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(D + 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

end RBM.Endpoints
