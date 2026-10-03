/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.AuxCarrier
import RBM2D.Green.EntryBlock

/-!
# The deterministic entry layer of the GUE phase at the mixture profile

The mixture profile is `S_u = a S + b N⁻¹` (`Smix`, in `AuxCarrier.lean`), `S' = S_u / u`,
`u = a + b`.

* stability of `1 - u m² S'` (`stable_mix`);
* the profile `Snorm = Smix / (a + b)` and the deterministic core of Lemma 4.1 (4.2), (4.3) at
  the mixture profile (`mix_det`);
* the `J`-part: Ward in column form (`ward_col`) and `Im m / (2 N η) ≤ maxLoopPM`
  (`inv_N_le_maxLoopPM`);
* Ward in row form, the diagonal bound, and the two-sided sum bound
  `∑_{k,l} S'_{ik} |G_{kl}|² S'_{lj} ≤ (1 + 3 / Im m) maxLoopPM` (`ward_row`, `im_diag_le`,
  `sum_Snorm_le`);
* the constants (`mixC`, `mixK`, `mixDelta`, `mixCdet`) and the deterministic bound `mix_det`:
  `|(G - m)_{pq}|² ≤ mixCdet κ L Φ² maxLoopPM`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

/-! ## Stability of `1 - ξ S̃` -/

section Stab

open RBM.Green

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem norm_one_sub_sq' {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * spectralM E ^ 2‖ ^ 2 = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (spectralM E).re = -E / 2 := by simp [spectralM]
  have him := spectralM_im E
  have hs := spectralM_sqrt_sq hE
  rw [pow_two (spectralM E), Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

private theorem gapK_pos' {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < RBM.KLoop.gapK κ := by
  unfold RBM.KLoop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

/-- The bulk gap `c_κ ≤ |1 - t m²|`. -/
theorem gapK_le_norm' {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) :
    RBM.KLoop.gapK κ ≤ ‖1 - (t : ℂ) * spectralM E ^ 2‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : RBM.KLoop.gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * spectralM E ^ 2‖ ^ 2 := by
    rw [norm_one_sub_sq' hE2]
    have hg0 := (gapK_pos' hκ hκ2).le
    have hg1 : RBM.KLoop.gapK κ ^ 2 ≤ 1 := by
      have := min_le_left 1 (Real.sqrt (κ * (4 - κ) / 2))
      have h1 : RBM.KLoop.gapK κ ≤ 1 := this
      nlinarith
    have hg2 : RBM.KLoop.gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
      have h1 : RBM.KLoop.gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
      have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
        Real.sq_sqrt (by nlinarith)
      nlinarith
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have := (gapK_pos' hκ hκ2).le
  have := norm_nonneg (1 - (t : ℂ) * spectralM E ^ 2)
  nlinarith

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Stability of `1 - u m² S'`, `S' = S_u / u = (a S + b N⁻¹) / (a + b)`**, uniformly in
`a, b ≥ 0`, `0 < a + b < 1`, `|E| ≤ 2 - κ`: the `J`-part is removed by averaging
(`|1 - u m²| ≥ c_κ`) and the band part is the `stable_svar_bulk` at `t = a`.  The stability
constant is `Kstab2 κ L` and the gap is `gapK κ`. -/
theorem stable_mix (hL : 3 ≤ L) {κ E a b : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) :
    Stable (fun x y : Idx L W => Smix L W a b x y / (a + b)) (((a + b : ℝ) : ℂ) * spectralM E ^ 2)
      (Kstab2 κ L * (1 + 1 / RBM.KLoop.gapK κ)) := by
  intro v B hB i
  set m := spectralM E with hm
  set u : ℝ := a + b with hudef
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    rw [hNdef]; positivity
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hgap0 := gapK_pos' hκ hκ2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i)
  have hm1 : ‖m‖ = 1 := norm_spectralM hE2
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  set V : ℂ := ∑ k, v k with hV
  have hgapn : RBM.KLoop.gapK κ ≤ ‖1 - (u : ℂ) * m ^ 2‖ := gapK_le_norm' hκ hE hu.le
  have hcard : (Fintype.card (Idx L W) : ℝ) = N := by
    rw [hNdef, card_Idx]
  -- the key identity
  have hkey : ∀ j, (u : ℂ) * m ^ 2 * ∑ k, ((Smix L W a b j k / u : ℝ) : ℂ) * v k
      = (a : ℂ) * m ^ 2 * ∑ k, (svar L W j k : ℂ) * v k + (b : ℂ) * m ^ 2 * (V / N) := by
    intro j
    have : ∀ k, (u : ℂ) * (((Smix L W a b j k / u : ℝ) : ℂ) * v k)
        = (a : ℂ) * ((svar L W j k : ℂ) * v k) + (b : ℂ) * (v k / N) := by
      intro k
      simp only [Smix, ← hNdef]
      push_cast
      field_simp
    calc (u : ℂ) * m ^ 2 * ∑ k, ((Smix L W a b j k / u : ℝ) : ℂ) * v k
        = m ^ 2 * ∑ k, (u : ℂ) * (((Smix L W a b j k / u : ℝ) : ℂ) * v k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = m ^ 2 * ∑ k, ((a : ℂ) * ((svar L W j k : ℂ) * v k) + (b : ℂ) * (v k / N)) := by
          simp only [this]
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, hV]
          ring
  set r : Idx L W → ℂ := fun j =>
    v j - (u : ℂ) * m ^ 2 * ∑ k, ((Smix L W a b j k / u : ℝ) : ℂ) * v k with hr
  have hrB : ∀ j, ‖r j‖ ≤ B := hB
  have hSV : ∑ j, ∑ k, (svar L W j k : ℂ) * v k = V := by
    rw [Finset.sum_comm, hV]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ j, (svar L W j k : ℂ) = 1 := by
      have h := Green.IBP_sum_svar_row hL (W := W) k
      simp_rw [svar_comm L W _ k]
      exact_mod_cast h
    rw [this, one_mul]
  have hsumr : ∑ j, r j = (1 - (u : ℂ) * m ^ 2) * V := by
    simp only [hr, hkey, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hSV,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hV]
    have hc : ((Fintype.card (Idx L W) : ℕ) : ℂ) = (N : ℂ) := by exact_mod_cast hcard
    rw [hc, hudef]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  have hnorm_sumr : ‖∑ j, r j‖ ≤ N * B := by
    calc ‖∑ j, r j‖ ≤ ∑ j, ‖r j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Idx L W, B := Finset.sum_le_sum fun j _ => hrB j
      _ = N * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hVle : ‖V‖ ≤ N * B / RBM.KLoop.gapK κ := by
    rw [le_div_iff₀ hgap0]
    calc ‖V‖ * RBM.KLoop.gapK κ ≤ ‖V‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hgapn (norm_nonneg _)
      _ = ‖∑ j, r j‖ := by rw [hsumr, norm_mul, mul_comm]
      _ ≤ N * B := hnorm_sumr
  have hr' : ∀ j, ‖v j - (a : ℂ) * m ^ 2 * ∑ k, (svar L W j k : ℂ) * v k‖
      ≤ B + B / RBM.KLoop.gapK κ := by
    intro j
    have hj : v j - (a : ℂ) * m ^ 2 * ∑ k, (svar L W j k : ℂ) * v k
        = r j + (b : ℂ) * m ^ 2 * (V / N) := by
      simp only [hr, hkey]; ring
    rw [hj]
    have hbn : ‖(b : ℂ) * m ^ 2 * (V / N)‖ = b * (‖V‖ / N) := by
      rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hb, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hNpos]
    have hVN : ‖V‖ / N ≤ B / RBM.KLoop.gapK κ := by
      rw [div_le_iff₀ hNpos]
      calc ‖V‖ ≤ N * B / RBM.KLoop.gapK κ := hVle
        _ = B / RBM.KLoop.gapK κ * N := by ring
    calc ‖r j + (b : ℂ) * m ^ 2 * (V / N)‖ ≤ ‖r j‖ + ‖(b : ℂ) * m ^ 2 * (V / N)‖ := norm_add_le _ _
      _ ≤ B + b * (B / RBM.KLoop.gapK κ) := by
          rw [hbn]
          exact add_le_add (hrB j) (mul_le_mul_of_nonneg_left hVN hb)
      _ ≤ B + B / RBM.KLoop.gapK κ := by
          have hb1 : b ≤ 1 := by linarith
          have h0 : 0 ≤ B / RBM.KLoop.gapK κ := div_nonneg hB0 hgap0.le
          nlinarith
  have ha1 : a < 1 := by linarith
  have hst := stable_svar_bulk (W := W) hL hκ hE ha ha1 v (B + B / RBM.KLoop.gapK κ) hr' i
  calc ‖v i‖ ≤ Kstab2 κ L * (B + B / RBM.KLoop.gapK κ) := hst
    _ = Kstab2 κ L * (1 + 1 / RBM.KLoop.gapK κ) * B := by ring

end Stab

/-! ## The deterministic core of Lemma 4.1 at the mixture profile (`EntryCore`) -/

section Core

open RBM.Green

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The normalised profile `S' = S_u / u`, `S_u = a S + b N⁻¹`, `u = a + b` (the profile of the
GUE phase at time `u`, and `S̃` for `b = ζ`, `a = 1 - ζ`). -/
def Snorm (L W : ℕ) (a b : ℝ) (x y : Idx L W) : ℝ := Smix L W a b x y / (a + b)

theorem Snorm_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Idx L W) :
    0 ≤ Snorm L W a b x y :=
  div_nonneg (Smix_nonneg L W ha hb x y) (add_nonneg ha hb)

theorem sum_Snorm_row (hL : 3 ≤ L) {a b : ℝ} (hu : 0 < a + b) (x : Idx L W) :
    ∑ y, Snorm L W a b x y = 1 := by
  unfold Snorm
  rw [← Finset.sum_div, sum_Smix_row L W hL a b x, div_self hu.ne']

theorem sum_Snorm_col (hL : 3 ≤ L) {a b : ℝ} (hu : 0 < a + b) (y : Idx L W) :
    ∑ x, Snorm L W a b x y = 1 := by
  unfold Snorm
  rw [← Finset.sum_div, sum_Smix_col L W hL a b y, div_self hu.ne']

/-- The entry bound `S'_{xy} ≤ W⁻²` (`N⁻¹ ≤ W⁻²`, `S ≤ W⁻²/5`): the hypothesis `S_xy ≤ C W⁻²` of the
profile-generic part. -/
theorem svar_le (x y : Idx L W) : svar L W x y ≤ (5 : ℝ)⁻¹ * ((W : ℝ)⁻¹) ^ 2 := by
  unfold svar; split_ifs
  · exact le_rfl
  · positivity

theorem Snorm_le (hL : 3 ≤ L) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (x y : Idx L W) : Snorm L W a b x y ≤ ((W : ℝ)⁻¹) ^ 2 := by
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hN : (W : ℝ) ^ 2 ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : W ≤ W * L := Nat.le_mul_of_pos_right W (by omega)
    have h2 : W ^ 2 ≤ (W * L) ^ 2 := Nat.pow_le_pow_left this 2
    exact_mod_cast h2
  have h1 : 1 / (((W * L) ^ 2 : ℕ) : ℝ) ≤ ((W : ℝ)⁻¹) ^ 2 := by
    rw [inv_pow, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hN
  have h2 : svar L W x y ≤ ((W : ℝ)⁻¹) ^ 2 := by
    refine (svar_le x y).trans ?_
    have : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
    nlinarith
  unfold Snorm Smix
  rw [div_le_iff₀ hu]
  have h3 : b / (((W * L) ^ 2 : ℕ) : ℝ) ≤ b * ((W : ℝ)⁻¹) ^ 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h1 hb
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

end Core

/-! ## The `J`-part lemma: `(N η)⁻¹ Im m ≲ max |𝓛|`

The flat part `b N⁻¹` of the profile is controlled through the Ward identity, since
`∑_{a,b} |𝓛_{(+,-),(a,b)}| = W⁻⁴ ∑_{x,y} |G_{xy}|²` (`norm_loopPM_eq`) and
`∑_x |G_{xy}|² = Im G_{yy} / η`. -/

section JPart

open RBM.Green RBM.Path

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Ward, column form**: `∑_x |G_{xi}|² = Im G_{ii} / Im z`. -/
theorem ward_col {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : ν) :
    ∑ x, ‖green H z x i‖ ^ 2 = (green H z i i).im / z.im := by
  have h := im_green_diag hH hz i
  have hdot : (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re
      = ∑ x, ‖green H z x i‖ ^ 2 := by
    have hv : ∀ x, (green H z *ᵥ Pi.single i 1) x = green H z x i := by
      intro x; simp
    simp only [dotProduct, Pi.star_apply, hv]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [RCLike.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [hdot] at h
  rw [h]
  field_simp

/-- **The lower bound `m / (2 N η) ≤ max_{a,b} |𝓛_{(+,-),(a,b)}|`** on the good event
`‖G - m‖_max ≤ δ ≤ Im m / 2`, `N = (W L)²`, `η = Im z_u^{(E)}`: Ward over one block column. -/
theorem inv_N_le_maxLoopPM {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (hz : 0 < (spectralZ E u).im) {m : ℂ} {δ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E u M true) m δ) (hδ : δ ≤ m.im / 2) :
    m.im / (2 * ((((W * L) ^ 2 : ℕ) : ℝ) * (spectralZ E u).im)) ≤ maxLoopPM L W E u M := by
  set z := spectralZ E u with hzdef
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (NeZero.pos L)
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  have hG : greenBlk L W E u M true = green (blockMat M) z := by rw [hzdef]; simp [greenBlk]
  have hdiag : ∀ x, m.im / 2 ≤ (greenBlk L W E u M true x x).im := by
    intro x
    have h1 := hΩ.norm_diag_sub_le x
    have h2 : |((greenBlk L W E u M true) x x - m).im| ≤ ‖(greenBlk L W E u M true) x x - m‖ :=
      Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have := neg_abs_le ((greenBlk L W E u M true x x).im - m.im)
    linarith
  set a0 : Z2 L := 0 with ha0
  have hsum : ∑ b : Z2 L, ‖loopPM L W E u M a0 b‖
      = ((W : ℝ)⁻¹ ^ 2) ^ 2 * ∑ α : Fin W × Fin W, (greenBlk L W E u M true (a0, α) (a0, α)).im / z.im := by
    simp only [norm_loopPM_eq M hM a0, ← Finset.mul_sum]
    congr 1
    calc ∑ b : Z2 L, ∑ β : Fin W × Fin W, ∑ α : Fin W × Fin W,
          ‖greenBlk L W E u M true (b, β) (a0, α)‖ ^ 2
        = ∑ b : Z2 L, ∑ α : Fin W × Fin W, ∑ β : Fin W × Fin W,
          ‖greenBlk L W E u M true (b, β) (a0, α)‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ α : Fin W × Fin W, ∑ b : Z2 L, ∑ β : Fin W × Fin W,
          ‖greenBlk L W E u M true (b, β) (a0, α)‖ ^ 2 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hG, ← ward_col hH hz.ne' (a0, α)]
          exact (Fintype.sum_prod_type (α₁ := Z2 L) (α₂ := Fin W × Fin W)
            (fun x : BlockIndex L W => ‖green (blockMat M) z x (a0, α)‖ ^ 2)).symm
  have hlow : (W : ℝ) ^ 2 * (m.im / 2 / z.im)
      ≤ ∑ α : Fin W × Fin W, (greenBlk L W E u M true (a0, α) (a0, α)).im / z.im := by
    calc (W : ℝ) ^ 2 * (m.im / 2 / z.im) = ∑ _α : Fin W × Fin W, m.im / 2 / z.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
      _ ≤ _ := Finset.sum_le_sum fun α _ => div_le_div_of_nonneg_right (hdiag _) hz.le
  have hup : ∑ b : Z2 L, ‖loopPM L W E u M a0 b‖ ≤ (L : ℝ) ^ 2 * maxLoopPM L W E u M := by
    calc ∑ b : Z2 L, ‖loopPM L W E u M a0 b‖ ≤ ∑ _b : Z2 L, maxLoopPM L W E u M :=
          Finset.sum_le_sum fun b _ =>
            Finset.le_sup' (fun p : Z2 L × Z2 L => ‖loopPM L W E u M p.1 p.2‖)
              (Finset.mem_univ (a0, b))
      _ = (L : ℝ) ^ 2 * maxLoopPM L W E u M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
          push_cast; ring
  have key : ((W : ℝ)⁻¹ ^ 2) ^ 2 * ((W : ℝ) ^ 2 * (m.im / 2 / z.im)) ≤
      (L : ℝ) ^ 2 * maxLoopPM L W E u M :=
    calc ((W : ℝ)⁻¹ ^ 2) ^ 2 * ((W : ℝ) ^ 2 * (m.im / 2 / z.im))
        ≤ ((W : ℝ)⁻¹ ^ 2) ^ 2 * ∑ α : Fin W × Fin W,
            (greenBlk L W E u M true (a0, α) (a0, α)).im / z.im :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = ∑ b : Z2 L, ‖loopPM L W E u M a0 b‖ := hsum.symm
      _ ≤ _ := hup
  have hN : (((W * L) ^ 2 : ℕ) : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by push_cast; ring
  rw [hN]
  have e : m.im / (2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * z.im))
      = (1 / (L : ℝ) ^ 2) * (((W : ℝ)⁻¹ ^ 2) ^ 2 * ((W : ℝ) ^ 2 * (m.im / 2 / z.im))) := by
    field_simp
  rw [e, one_div, inv_mul_le_iff₀ (by positivity)]
  exact key

end JPart

/-! ## Ward in row form, the diagonal bound, and the two-sided sum bound at the mixture profile -/

section Ward

open RBM.Green RBM.Path

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- `(green H z)ᵀ = green Hᵀ z`. -/
theorem green_transpose {H : Matrix ν ν ℂ} (z : ℂ) : (green H z)ᵀ = green Hᵀ z := by
  unfold green
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- **Ward, row form**: `∑_l |G_{kl}|² = Im G_{kk} / Im z`. -/
theorem ward_row {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (k : ν) :
    ∑ l, ‖green H z k l‖ ^ 2 = (green H z k k).im / z.im := by
  have hHt : (Hᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose, Matrix.transpose_transpose]
    have := hH.eq
    rw [Matrix.conjTranspose] at this
    ext a b
    have h2 := congrArg (fun M => M b a) this
    simp only [Matrix.map_apply, Matrix.transpose_apply] at h2 ⊢
    exact h2
  have h := ward_col hHt hz k
  have ht : ∀ a b, green Hᵀ z a b = green H z b a := by
    intro a b
    rw [← green_transpose]; rfl
  simp only [ht] at h
  exact h

omit [Fintype ν] in
/-- On the good event, `Im G_{xx} ≤ 3/2`. -/
theorem im_diag_le {G : Matrix ν ν ℂ} {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (x : ν) : (G x x).im ≤ 3 / 2 := by
  have h1 := hΩ.norm_diag_le hm x
  have h2 : |(G x x).im| ≤ ‖G x x‖ := Complex.abs_im_le_norm _
  have := le_abs_self (G x x).im
  linarith

end Ward

section SumBound

open RBM.Green RBM.Path

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem card_blockIndex_real (L W : ℕ) [NeZero L] [NeZero W] :
    (Fintype.card (BlockIndex L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
  have h := Fintype.card_congr (splitEquiv L W)
  have h2 : Fintype.card (BlockIndex L W) = (W * L) ^ 2 := by
    rw [← h]; exact card_Idx L W
  exact_mod_cast h2

/-- **The two-sided sum with the normalised mixture profile** is `≤ (1 + 3 / Im m) max |𝓛_{(+,-)}|`
on the good event (the profile `S' = (a S + b N⁻¹) / (a + b)` read on `BlockIndex` through
`splitEquiv`).  The band part is `sum_sum_Sblk2_le_maxLoopPM`, the `J`-part goes through Ward
(`ward_row`, `ward_col`, `im_diag_le`) and `inv_N_le_maxLoopPM`.  The profile is `a S + b N⁻¹` with
`u = a + b`; the spectral time `s` is independent of `a, b`. -/
theorem sum_Snorm_le (hL : 3 ≤ L) {E s : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hM : M.IsHermitian) (hz : 0 < (spectralZ E s).im) {m : ℂ} (hm : ‖m‖ = 1) (him : 0 < m.im)
    {δ : ℝ} (hΩ : GoodEvent (greenBlk L W E s M true) m δ) (hδ12 : δ ≤ 1 / 2)
    (hδm : δ ≤ m.im / 2) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (p q : BlockIndex L W) :
    ∑ k, ∑ l, Snorm L W a b ((splitEquiv L W).symm p) ((splitEquiv L W).symm k) *
        ‖greenBlk L W E s M true k l‖ ^ 2 *
        Snorm L W a b ((splitEquiv L W).symm l) ((splitEquiv L W).symm q)
      ≤ (1 + 3 / m.im) * maxLoopPM L W E s M := by
  set G := greenBlk L W E s M true with hG
  set N : ℝ := (((W * L) ^ 2 : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    rw [hNdef]; positivity
  set α : ℝ := a / (a + b) with hα
  set β : ℝ := b / (a + b) with hβ
  have hαβ : α + β = 1 := by
    rw [hα, hβ, ← add_div, div_self hu.ne']
  have hα0 : 0 ≤ α := div_nonneg ha hu.le
  have hβ0 : 0 ≤ β := div_nonneg hb hu.le
  have hune : a + b ≠ 0 := hu.ne'
  have hGgreen : G = green (blockMat M) (spectralZ E s) := by simp [hG, greenBlk]
  have hH : (blockMat M).IsHermitian := hM.submatrix _
  set η : ℝ := (spectralZ E s).im with hη
  set Y : ℝ := 3 / 2 / η with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hR : ∀ k, ∑ l, ‖G k l‖ ^ 2 ≤ Y := by
    intro k
    rw [hGgreen, ward_row hH hz.ne' k, ← hGgreen]
    exact div_le_div_of_nonneg_right (im_diag_le hm hΩ hδ12 k) hz.le
  have hC : ∀ l, ∑ k, ‖G k l‖ ^ 2 ≤ Y := by
    intro l
    rw [hGgreen, ward_col hH hz.ne' l, ← hGgreen]
    exact div_le_div_of_nonneg_right (im_diag_le hm hΩ hδ12 l) hz.le
  have hLm := maxLoopPM_nonneg (L := L) (W := W) E s M
  set mL := maxLoopPM L W E s M with hmL
  have hYN : Y / N ≤ 3 / m.im * mL := by
    have h := inv_N_le_maxLoopPM (W := W) (L := L) hM hz hΩ hδm
    have e : Y / N = 3 / m.im * (m.im / (2 * (N * η))) := by
      rw [hY]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hSn : ∀ x y : BlockIndex L W,
      Snorm L W a b ((splitEquiv L W).symm x) ((splitEquiv L W).symm y)
        = α * Sblk2 L W x y + β / N := by
    intro x y
    rw [Sblk2_eq_svar]
    unfold Snorm Smix
    rw [hα, hβ, ← hNdef]
    field_simp
  have hpt : ∀ k l : BlockIndex L W,
      (α * Sblk2 L W p k + β / N) * ‖G k l‖ ^ 2 * (α * Sblk2 L W l q + β / N)
        = α ^ 2 * (Sblk2 L W p k * ‖G k l‖ ^ 2 * Sblk2 L W l q)
          + α * β / N * (Sblk2 L W p k * ‖G k l‖ ^ 2)
          + α * β / N * (‖G k l‖ ^ 2 * Sblk2 L W l q)
          + β ^ 2 / N ^ 2 * ‖G k l‖ ^ 2 := by
    intro k l; field_simp; ring
  have hT1 : ∑ k, ∑ l, Sblk2 L W p k * ‖G k l‖ ^ 2 * Sblk2 L W l q ≤ mL :=
    sum_sum_Sblk2_le_maxLoopPM (E := E) (u := s) hL hM p q
  have hT2 : ∑ k, ∑ l, Sblk2 L W p k * ‖G k l‖ ^ 2 ≤ Y := by
    calc ∑ k, ∑ l, Sblk2 L W p k * ‖G k l‖ ^ 2 = ∑ k, Sblk2 L W p k * ∑ l, ‖G k l‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ k, Sblk2 L W p k * Y :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hR k) (Sblk2_nonneg _ _)
      _ = Y := by rw [← Finset.sum_mul, sum_Sblk2_row hL, one_mul]
  have hT3 : ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk2 L W l q ≤ Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk2 L W l q = ∑ l, (∑ k, ‖G k l‖ ^ 2) * Sblk2 L W l q := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ ∑ l, Y * Sblk2 L W l q :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hC l) (Sblk2_nonneg _ _)
      _ = Y := by rw [← Finset.mul_sum, sum_Sblk2_col hL, mul_one]
  have hT4 : ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ N * Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ ∑ _k : BlockIndex L W, Y := Finset.sum_le_sum fun k _ => hR k
      _ = N * Y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_blockIndex_real]
  simp only [hSn, hpt]
  have hsplit : ∑ k, ∑ l, (α ^ 2 * (Sblk2 L W p k * ‖G k l‖ ^ 2 * Sblk2 L W l q)
          + α * β / N * (Sblk2 L W p k * ‖G k l‖ ^ 2)
          + α * β / N * (‖G k l‖ ^ 2 * Sblk2 L W l q)
          + β ^ 2 / N ^ 2 * ‖G k l‖ ^ 2)
      = α ^ 2 * ∑ k, ∑ l, Sblk2 L W p k * ‖G k l‖ ^ 2 * Sblk2 L W l q
        + α * β / N * ∑ k, ∑ l, Sblk2 L W p k * ‖G k l‖ ^ 2
        + α * β / N * ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk2 L W l q
        + β ^ 2 / N ^ 2 * ∑ k, ∑ l, ‖G k l‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have e1 := mul_le_mul_of_nonneg_left hT1 (sq_nonneg α)
  have e2 := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ α * β / N)
  have e3 := mul_le_mul_of_nonneg_left hT3 (by positivity : 0 ≤ α * β / N)
  have e4 := mul_le_mul_of_nonneg_left hT4 (by positivity : 0 ≤ β ^ 2 / N ^ 2)
  have hα1 : α ^ 2 ≤ 1 := by nlinarith
  have hc : α * β / N * Y + α * β / N * Y + β ^ 2 / N ^ 2 * (N * Y) = (1 - α ^ 2) * (Y / N) := by
    have hβ' : β = 1 - α := by linarith
    rw [hβ']
    field_simp
    ring
  have hf : (1 - α ^ 2) * (Y / N) ≤ (1 - α ^ 2) * (3 / m.im * mL) :=
    mul_le_mul_of_nonneg_left hYN (by linarith)
  have h3m : 0 ≤ 3 / m.im * mL := by positivity
  have hα2mL : α ^ 2 * mL ≤ mL := by nlinarith
  have hg : (1 - α ^ 2) * (3 / m.im * mL) ≤ 3 / m.im * mL := by nlinarith
  have : (1 + 3 / m.im) * mL = mL + 3 / m.im * mL := by ring
  rw [this]
  linarith

end SumBound

/-! ## The constants and the deterministic bound `mix_det`

The constants are `mixC`, `mixK`, `mixDelta`, `mixCdet`; the stability constant is `Kstab2 κ L`
and `gapK κ` replaces `√κ`; the hypothesis `κ ≤ 1` is not needed (`κ ≤ 2` follows from `hE`), and
the conclusion has no `+ W⁻²` term (it is absorbed by `inv_W2_le_maxLoopPM`). -/

section MixConst

open RBM.Green

/-- `c_κ = √(2κ)/2 ≤ Im m(E)`. -/
def mixC (κ : ℝ) : ℝ := Real.sqrt (2 * κ) / 2

/-- The stability constant `Kstab2 κ L · (1 + 1 / gapK κ)` of `stable_mix`. -/
def mixK (κ : ℝ) (L : ℕ) : ℝ := Kstab2 κ L * (1 + 1 / RBM.KLoop.gapK κ)

/-- The smallness threshold for `δ`. -/
def mixDelta (κ : ℝ) (L : ℕ) : ℝ := min (1 / 2) (min (1 / (2 * mixK κ L)) (mixC κ / 2))

/-- The constant of the deterministic bound. -/
def mixCdet (κ : ℝ) (L : ℕ) : ℝ := (2160 * mixK κ L ^ 2 + 162) * (1 + 3 / mixC κ)

theorem mixC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < mixC κ := by
  unfold mixC
  have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  positivity

theorem mixK_one_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (L : ℕ) : 1 ≤ mixK κ L := by
  unfold mixK Kstab2
  have hg := gapK_pos' hκ hκ2
  have hlog : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  have h1 : 0 ≤ 2 * (180 * 40002 ^ 2) / RBM.KLoop.gapK κ *
      (1 + 40000 / Real.sqrt (RBM.KLoop.gapK κ)) ^ 2 * (1 + Real.log L) := by positivity
  have h2 : (1 : ℝ) ≤ 1 + 2 * (180 * 40002 ^ 2) / RBM.KLoop.gapK κ *
      (1 + 40000 / Real.sqrt (RBM.KLoop.gapK κ)) ^ 2 * (1 + Real.log L) := by linarith
  have h3 : (1 : ℝ) ≤ 1 + 1 / RBM.KLoop.gapK κ := by
    have : 0 ≤ 1 / RBM.KLoop.gapK κ := by positivity
    linarith
  nlinarith

theorem mixCdet_nonneg {κ : ℝ} (hκ : 0 < κ) (L : ℕ) : 0 ≤ mixCdet κ L := by
  unfold mixCdet
  have hc := mixC_pos hκ
  positivity

/-- `c_κ ≤ Im m(E)` for `|E| ≤ 2 - κ`. -/
private theorem mixC_le_spectralM_im {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    mixC κ ≤ (spectralM E).im := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  rw [spectralM_im]
  unfold mixC
  have := Real.sqrt_le_sqrt h2
  linarith

end MixConst

section MixDet

open RBM.Green RBM.Path

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scaling of the row right side by `u`, any index type. -/
theorem ldeRowRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeRowRHS (fun x y => u * S x y) G i j = u * ldeRowRHS S G i j := by
  unfold ldeRowRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- Scaling of the column right side by `u`, any index type. -/
theorem ldeColRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeColRHS (fun x y => u * S x y) G i j = u * ldeColRHS S G i j := by
  unfold ldeColRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- Scaling of the quadratic right side by `u²`, any index type. -/
theorem ldeQuadRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) :
    ldeQuadRHS (fun x y => u * S x y) G i = u ^ 2 * ldeQuadRHS S G i := by
  unfold ldeQuadRHS; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring

/-- Pulling the scale `u` out of the profile in `ldeQuadLHS`:
`ldeQuadLHS H G (u S) 1 i = ldeQuadLHS H G S u i`, any index type. -/
theorem ldeQuadLHS_smul (u : ℝ) (S : n → n → ℝ) (H G : Matrix n n ℂ) (i : n) :
    ldeQuadLHS H G (fun x y => u * S x y) 1 i = ldeQuadLHS H G S u i := by
  unfold ldeQuadLHS
  congr 2
  push_cast
  rw [one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

end MixDet

section MixDetThm

open RBM.Green RBM.Path

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Lemma 4.1 (4.2)+(4.3) at the mixture profile, deterministic form.**  On the good event of
`G = greenBlk L W E (a+b) M true` (`‖G - m‖_max ≤ δ ≤ mixDelta κ L`), given the four large-deviation
inputs with the profile `S_u = a S + b N⁻¹` (`Smix`, read on `BlockIndex` through `splitEquiv`) and
factor `Φ`, every entry satisfies
`|(G - m)_{pq}|² ≤ mixCdet κ L · Φ² · max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`.  The stability input is
`stable_mix` and the two-sided sum is `sum_Snorm_le`. -/
theorem mix_det (hL : 3 ≤ L) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {κ E a b : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (hu1 : a + b < 1) {δ Φ : ℝ}
    (hΩ : GoodEvent (greenBlk L W E (a + b) M true) (spectralM E) δ)
    (hδ : δ ≤ mixDelta κ L) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow (blockMat M) (greenBlk L W E (a + b) M true)
      (fun x y => Smix L W a b ((splitEquiv L W).symm x) ((splitEquiv L W).symm y)) Φ)
    (hLcol : LDECol (blockMat M) (greenBlk L W E (a + b) M true)
      (fun x y => Smix L W a b ((splitEquiv L W).symm x) ((splitEquiv L W).symm y)) Φ)
    (hLquad : LDEQuad (blockMat M) (greenBlk L W E (a + b) M true)
      (fun x y => Smix L W a b ((splitEquiv L W).symm x) ((splitEquiv L W).symm y)) 1 Φ)
    (hLdiag : ∀ i, ‖blockMat M i i‖ ^ 2 ≤
      Φ * Smix L W a b ((splitEquiv L W).symm i) ((splitEquiv L W).symm i))
    (p q : BlockIndex L W) :
    ‖(greenBlk L W E (a + b) M true - spectralM E •
        (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) p q‖ ^ 2
      ≤ mixCdet κ L * Φ ^ 2 * maxLoopPM L W E (a + b) M := by
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set e := splitEquiv L W with he
  set u : ℝ := a + b with hudef
  set m := spectralM E with hmdef
  set z := spectralZ E u with hzdef
  set G := greenBlk L W E u M true with hGdef
  set H := blockMat M with hHdef
  set S' : BlockIndex L W → BlockIndex L W → ℝ :=
    fun x y => Snorm L W a b (e.symm x) (e.symm y) with hS'def
  set Sb : BlockIndex L W → BlockIndex L W → ℝ :=
    fun x y => Smix L W a b (e.symm x) (e.symm y) with hSbdef
  have hm : ‖m‖ = 1 := norm_spectralM hE2
  have hmim : mixC κ ≤ m.im := mixC_le_spectralM_im hκ hE
  have hc := mixC_pos hκ
  have him : 0 < m.im := lt_of_lt_of_le hc hmim
  have hzpos : 0 < z.im := by
    rw [hzdef, spectralZ_im]; exact mul_pos (by linarith) him
  have hz : z.im ≠ 0 := hzpos.ne'
  have hGgreen : G = green H z := by simp [hGdef, hHdef, hzdef, greenBlk]
  have hHerm : H.IsHermitian := hM.submatrix _
  have hGM : G * (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) = 1 := by
    rw [hGgreen]; exact green_mul_sub_of_im hHerm hz
  have hMG : (H - z • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) * G = 1 := by
    rw [hGgreen]; exact sub_mul_green_of_im hHerm hz
  have hK1 := mixK_one_le hκ hκ2 L
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ p p)
  have hδ12 : δ ≤ 1 / 2 := hδ.trans (min_le_left _ _)
  have hδK : mixK κ L * δ ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * mixK κ L) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ mixK κ L)
    rwa [show mixK κ L * (1 / (2 * mixK κ L)) = 1 / 2 by field_simp] at h2
  have hδc : δ ≤ m.im / 2 := by
    have h1 : δ ≤ mixC κ / 2 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hSbfun : Sb = fun x y => u * S' x y := by
    funext x y
    simp only [hSbdef, hS'def]
    unfold Snorm
    rw [hudef]
    have hune : a + b ≠ 0 := hu.ne'
    field_simp
  have hS0 : ∀ x y, 0 ≤ S' x y := fun x y => Snorm_nonneg ha hb _ _
  have hSrow : ∀ x, ∑ y, S' x y = 1 := by
    intro x
    simp only [hS'def]
    rw [Equiv.sum_comp e.symm (fun y' => Snorm L W a b (e.symm x) y')]
    exact sum_Snorm_row hL hu _
  have hScol : ∀ y, ∑ x, S' x y ≤ 1 := by
    intro y
    simp only [hS'def]
    rw [Equiv.sum_comp e.symm (fun x' => Snorm L W a b x' (e.symm y))]
    exact (sum_Snorm_col hL hu _).le
  have hS'W : ∀ x y, S' x y ≤ ((W : ℝ)⁻¹) ^ 2 := fun x y => Snorm_le hL ha hb hu _ _
  have hu1' : u ≤ 1 := hu1.le
  -- the four inputs in the normalised form
  have hLr : LDERow H G S' Φ := by
    intro i j hij
    have h : ldeRowLHS H G i j ≤ Φ * ldeRowRHS (fun x y => u * S' x y) G i j := by
      rw [← hSbfun]; exact hLrow i j hij
    rw [ldeRowRHS_smul] at h
    have hR : 0 ≤ ldeRowRHS S' G i j :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 _ _) (sq_nonneg _)
    have : Φ * (u * ldeRowRHS S' G i j) ≤ Φ * ldeRowRHS S' G i j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLc : LDECol H G S' Φ := by
    intro k j hkj
    have h : ldeColLHS H G k j ≤ Φ * ldeColRHS (fun x y => u * S' x y) G k j := by
      rw [← hSbfun]; exact hLcol k j hkj
    rw [ldeColRHS_smul] at h
    have hR : 0 ≤ ldeColRHS S' G k j :=
      Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) (hS0 _ _)
    have : Φ * (u * ldeColRHS S' G k j) ≤ Φ * ldeColRHS S' G k j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLq : LDEQuad H G S' u Φ := by
    intro i
    have h : ldeQuadLHS H G (fun x y => u * S' x y) 1 i
        ≤ Φ * ldeQuadRHS (fun x y => u * S' x y) G i := by
      rw [← hSbfun]; exact hLquad i
    rw [ldeQuadLHS_smul, ldeQuadRHS_smul] at h
    have hR : 0 ≤ ldeQuadRHS S' G i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (hS0 _ _) (sq_nonneg _)) (hS0 _ _)
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have : Φ * (u ^ 2 * ldeQuadRHS S' G i) ≤ Φ * ldeQuadRHS S' G i :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLd : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S' i i := by
    intro i
    have h : ‖H i i‖ ^ 2 ≤ Φ * (u * S' i i) := by
      have := hLdiag i
      have e1 : Smix L W a b (e.symm i) (e.symm i) = Sb i i := rfl
      rw [e1, hSbfun] at this
      exact this
    have : Φ * (u * S' i i) ≤ Φ * S' i i :=
      mul_le_mul_of_nonneg_left (by nlinarith [hS0 i i]) (by linarith)
    linarith
  -- `Λ`
  have hLm0 : 0 ≤ maxLoopPM L W E u M := maxLoopPM_nonneg (L := L) (W := W) E u M
  set mL := maxLoopPM L W E u M with hmL
  set Λ : ℝ := (1 + 3 / mixC κ) * mL with hΛdef
  have h3c : 3 / m.im ≤ 3 / mixC κ := div_le_div_of_nonneg_left (by norm_num) hc hmim
  have hΛ1 : ∀ i j, ∑ k, ∑ l, S' i k * ‖G k l‖ ^ 2 * S' l j ≤ Λ := by
    intro i j
    have h := sum_Snorm_le hL hM hzpos hm him hΩ hδ12 hδc ha hb hu i j
    have h2 : (1 + 3 / m.im) * mL ≤ (1 + 3 / mixC κ) * mL :=
      mul_le_mul_of_nonneg_right (by linarith) hLm0
    exact h.trans h2
  have hΛ2 : ∀ i j, S' i j ≤ Λ := by
    intro i j
    have hW2 := inv_W2_le_maxLoopPM (L := L) (W := W) (E := E) (u := u) hM hE2 hΩ hδ12
    have hc1 : mixC κ ≤ 1 := by
      have : m.im ≤ ‖m‖ := Complex.im_le_norm _
      linarith
    have h4 : 4 ≤ 1 + 3 / mixC κ := by
      have : 3 ≤ 3 / mixC κ := by rw [le_div_iff₀ hc]; linarith
      linarith
    calc S' i j ≤ ((W : ℝ)⁻¹) ^ 2 := hS'W i j
      _ ≤ 4 * mL := hW2
      _ ≤ (1 + 3 / mixC κ) * mL := mul_le_mul_of_nonneg_right h4 hLm0
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΦ2 : 0 ≤ Φ ^ 2 := sq_nonneg Φ
  have hfinal : ∀ X : ℝ, X ≤ (2160 * mixK κ L ^ 2 + 162) * Φ ^ 2 * Λ →
      X ≤ mixCdet κ L * Φ ^ 2 * mL := by
    intro X hX
    refine hX.trans (le_of_eq ?_)
    unfold mixCdet
    rw [hΛdef]
    ring
  by_cases hij : p = q
  · subst hij
    have hentry : (G - m • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) p p = G p p - m := by
      simp
    rw [hentry]
    have hStab : Stable S' ((u : ℂ) * m ^ 2) (mixK κ L) :=
      stable_relabel e (stable_mix hL hκ hE ha hb hu hu1)
    have h := norm_sq_green_diag_sub_le hGM hMG hm (mE_mul_add_zt hE2 u) (by linarith) hu1' hΩ
      hδ12 hS0 hSrow hScol hΦ1 hΦδ hLr hLc hLq hLd hΛ1 hΛ2 hδK hStab p
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ := mul_nonneg hΦ2 hΛ0
    calc 2160 * mixK κ L ^ 2 * Φ ^ 2 * Λ = 2160 * mixK κ L ^ 2 * (Φ ^ 2 * Λ) := by ring
      _ ≤ (2160 * mixK κ L ^ 2 + 162) * (Φ ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * mixK κ L ^ 2 + 162) * Φ ^ 2 * Λ := by ring
  · have hentry : (G - m • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)) p q = G p q := by
      simp [hij]
    rw [hentry]
    have h := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ12 hS0 (fun x => (hSrow x).le) hScol
      hΦ1 hΦδ hLr hLc hΛ1 hΛ2 hij
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ := mul_nonneg hΦ2 hΛ0
    have hK2 : 0 ≤ 2160 * mixK κ L ^ 2 := by positivity
    calc 162 * Φ ^ 2 * Λ = 162 * (Φ ^ 2 * Λ) := by ring
      _ ≤ (2160 * mixK κ L ^ 2 + 162) * (Φ ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * mixK κ L ^ 2 + 162) * Φ ^ 2 * Λ := by ring

end MixDetThm

end RBM.Univ
