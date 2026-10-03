/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.LemDecCalE

/-!
# `lem_dec_calE`, second part: the `𝓔^{(G̃)}` bound

Result (namespace `RBM.Path`): `lemDecCalE_wG : LemDecCalE_wG`, the bound `res_deccalE_wG` with
the deterministic control (e9) of `⟨G̃ E_a⟩` (clause 6 of `goodSet`), from the shared facts
(e1)–(e10) of `RBM2D/Path/LemDecCalE.lean` and the tail sums `convSqrtTailT`, `tellStar` of
`RBM2D/Path/TailSums.lean`.

Proof outline:
* prefactor: `|𝓔^{(G̃)}| ≤ W² · Λρ²M_u⁻¹ · Σ_b (|𝓛¹_b| + |𝓛²_b|)` (the column sums of `|S|`
  are `1`);
* every three-loop is bounded by the triangle sum `tri` of the entry bounds `fG` (symmetric in
  the two blocks, `G(−)_{pq} = conj G(+)_{qp}`);
* near (`|a₁-a₂|_L ≤ ℓ*_u`): split `b` at `4 (log(L²W¹²))² ℓ_u`; close `b` by (`lRB1`) at `k = 3`,
  far `b` by (e7) and the floor; normalise `M_u⁻² ≤ e^{(log W)^{3/4}} 𝒯_u(|a₁-a₂|_L)` (`tellStar`);
* far (`|a₁-a₂|_L > ℓ*_u`): `b` within `ℓ*_u/2` of `a₁` or of `a₂` by (e7), (e8), (e6) and AM–GM;
  the rest by (e7) on all three edges and `convSqrtTailT`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

/-- **The `𝓔^{(G̃)}` bound (`res_deccalE_wG`, proof exponents)**, with (`GavLGEX`) in the
deterministic-control form of `goodSet` (fact (e9): `|⟨G̃E_a⟩| ≤ Λ ρ² M_u^{-1}`, `ρ = ℓ_u/ℓ_s`):
near `η_u^{-1} ρ⁶ 1(|a₁-a₂| ≤ ℓ*_u)`, far `η_u^{-1} ρ² M_u^{-1/2} (J*)²`. -/
def LemDecCalE_wG : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E s u v D Λ K₀ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ),
    E2Hyp L W E s u v D Λ K₀ M → ∀ a₁ a₂ : Z2 L,
      ‖EGt L W E u M a₁ a₂‖ ≤ lossE2 L W Λ K₀ * ((etaT E u)⁻¹ *
        ((ellT L u / ellT L s) ^ 6 *
            (if (zdist2 L (a₁ - a₂) : ℝ) ≤ ellStar L W u then 1 else 0) +
          (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2)) *
        tailT L W E D v (zdist2 L (a₁ - a₂) : ℝ)

/-! ## 1. Distances -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem zdist_neg_eq' (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem zdist2_comm (a b : Z2 L) : zdist2 L (a - b) = zdist2 L (b - a) := by
  rw [← neg_sub b a]
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, zdist_neg_eq']

private theorem zdist2_tri (a b c : Z2 L) :
    (zdist2 L (a - c) : ℝ) ≤ (zdist2 L (a - b) : ℝ) + (zdist2 L (b - c) : ℝ) := by
  have := zdist2_add_le L (a - b) (b - c)
  rw [sub_add_sub_cancel] at this
  exact_mod_cast this

end Dist

/-! ## 2. Entry bounds and the triangle sum -/

section Tri

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The symmetric entry bound `max(|G(+)_{pq}|, |G(+)_{qp}|)`. -/
private def fG (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p q : BlockIndex L W) : ℝ :=
  max ‖greenBlk L W E u M true p q‖ ‖greenBlk L W E u M true q p‖

private theorem fG_comm (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p q : BlockIndex L W) :
    fG E u M p q = fG E u M q p := max_comm _ _

private theorem fG_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (p q : BlockIndex L W) :
    0 ≤ fG E u M p q := le_max_of_le_left (norm_nonneg _)

private theorem fG_sq_le {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} {p q : BlockIndex L W}
    {c : ℝ} (h1 : ‖greenBlk L W E u M true p q‖ ^ 2 ≤ c)
    (h2 : ‖greenBlk L W E u M true q p‖ ^ 2 ≤ c) : fG E u M p q ^ 2 ≤ c := by
  unfold fG
  rcases le_total ‖greenBlk L W E u M true p q‖ ‖greenBlk L W E u M true q p‖ with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- `|G(σ)_{pq}| ≤ fG p q` for both signs (`G(−) = G(+)ᴴ` for Hermitian `M`). -/
private theorem norm_greenBlk_le_fG {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : M.IsHermitian) (σ : Bool) (p q : BlockIndex L W) :
    ‖greenBlk L W E u M σ p q‖ ≤ fG E u M p q := by
  cases σ
  · have hHb : (blockMat M).IsHermitian := hH.submatrix _
    have hG := Gsig_conjTranspose hHb (spectralZ E u) true
    have hfalse : greenBlk L W E u M false p q = star (greenBlk L W E u M true q p) := by
      have := congrFun (congrFun hG p) q
      simpa [Matrix.conjTranspose_apply, greenBlk] using this.symm
    rw [hfalse, norm_star]
    exact le_max_right _ _
  · exact le_max_left _ _

/-- The block weight `|E_c|_{pp} = W⁻² 1(p.1 = c)`. -/
private def wt (c : Z2 L) (p : BlockIndex L W) : ℝ := if p.1 = c then ((W : ℝ) ^ 2)⁻¹ else 0

omit [NeZero L] [NeZero W] in
private theorem wt_nonneg (c : Z2 L) (p : BlockIndex L W) : 0 ≤ (wt c p : ℝ) := by
  unfold wt; split_ifs <;> positivity

omit [NeZero L] [NeZero W] in
private theorem wt_le (c : Z2 L) (p : BlockIndex L W) : (wt c p : ℝ) ≤ ((W : ℝ) ^ 2)⁻¹ := by
  unfold wt; split_ifs <;> first | exact le_rfl | positivity

private theorem sum_wt (c : Z2 L) : ∑ p : BlockIndex L W, (wt c p : ℝ) = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  unfold wt
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  · intro x _ hx
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- The triangle sum `Σ_{p ∈ c₃, q ∈ c₁, r ∈ c₂} W⁻⁶ fG(p,q) fG(q,r) fG(r,p)`. -/
private def tri (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (c₁ c₂ c₃ : Z2 L) : ℝ :=
  ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ∑ r : BlockIndex L W,
    wt c₃ p * wt c₁ q * wt c₂ r * (fG E u M p q * fG E u M q r * fG E u M r p)

/-- A three-loop as a triple sum of entries. -/
private theorem loop3_expand (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s₁ s₂ s₃ : Bool)
    (c₁ c₂ c₃ : Z2 L) :
    loop3 L W E u M ![s₁, s₂, s₃] ![c₁, c₂, c₃] =
      Matrix.trace (greenBlk L W E u M s₁ * Eblk L W c₁ * greenBlk L W E u M s₂ * Eblk L W c₂ *
        greenBlk L W E u M s₃ * Eblk L W c₃) := by
  simp [loop3, greenBlk, gloop, gloopProd, loopOf, List.ofFn_succ, Matrix.mul_assoc]

/-- Every three-loop is bounded by the triangle sum. -/
private theorem norm_loop3_le_tri {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ}
    (hH : M.IsHermitian) (s₁ s₂ s₃ : Bool) (c₁ c₂ c₃ : Z2 L) :
    ‖loop3 L W E u M ![s₁, s₂, s₃] ![c₁, c₂, c₃]‖ ≤ tri E u M c₁ c₂ c₃ := by
  rw [loop3_expand]
  simp only [Eblk, Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hw : ‖((W : ℂ)⁻¹ ^ 2 : ℂ)‖ = ((W : ℝ) ^ 2)⁻¹ := by simp
  have hw0 : (0 : ℝ) ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  calc _ ≤ ∑ p : BlockIndex L W, ∑ r : BlockIndex L W, ∑ q : BlockIndex L W,
        wt c₃ p * wt c₁ q * wt c₂ r * (fG E u M p q * fG E u M q r * fG E u M r p) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        split_ifs with hp
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          split_ifs with hr
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
            split_ifs with hq
            · have h1 := norm_greenBlk_le_fG (E := E) (u := u) hH s₁ p q
              have h2 := norm_greenBlk_le_fG (E := E) (u := u) hH s₂ q r
              have h3 := norm_greenBlk_le_fG (E := E) (u := u) hH s₃ r p
              have hf1 := fG_nonneg E u M p q
              have hf2 := fG_nonneg E u M q r
              simp only [wt, hp, hq, hr, ite_true, norm_mul, hw]
              calc ‖greenBlk L W E u M s₁ p q‖ * ((W : ℝ) ^ 2)⁻¹ * ‖greenBlk L W E u M s₂ q r‖ *
                    ((W : ℝ) ^ 2)⁻¹ * ‖greenBlk L W E u M s₃ r p‖ * ((W : ℝ) ^ 2)⁻¹
                  = (((W : ℝ) ^ 2)⁻¹ * ((W : ℝ) ^ 2)⁻¹ * ((W : ℝ) ^ 2)⁻¹) *
                      (‖greenBlk L W E u M s₁ p q‖ * ‖greenBlk L W E u M s₂ q r‖ *
                        ‖greenBlk L W E u M s₃ r p‖) := by ring
                _ ≤ (((W : ℝ) ^ 2)⁻¹ * ((W : ℝ) ^ 2)⁻¹ * ((W : ℝ) ^ 2)⁻¹) *
                      (fG E u M p q * fG E u M q r * fG E u M r p) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hf1) h3 (norm_nonneg _)
                        (mul_nonneg hf1 hf2)) (by positivity)
            · simp [wt, hq]
          · simp [wt, hr]
        · simp [wt, hp]
    _ = tri E u M c₁ c₂ c₃ := by
        unfold tri
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- The triangle sum is symmetric in its first two blocks. -/
private theorem tri_swap (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (c₁ c₂ c₃ : Z2 L) :
    tri E u M c₂ c₁ c₃ = tri E u M c₁ c₂ c₃ := by
  unfold tri
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  rw [fG_comm E u M p r, fG_comm E u M r q, fG_comm E u M q p]
  ring

/-- Pointwise bound on the three edges. -/
private theorem tri_le_of_pt {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} {c₁ c₂ c₃ : Z2 L}
    {B : ℝ} (h : ∀ p q r : BlockIndex L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ →
      fG E u M p q * fG E u M q r * fG E u M r p ≤ B) :
    tri E u M c₁ c₂ c₃ ≤ B := by
  calc tri E u M c₁ c₂ c₃
      ≤ ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ∑ r : BlockIndex L W,
          wt c₃ p * (wt c₁ q * (wt c₂ r * B)) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have := mul_le_mul_of_nonneg_left (h p q r hp hq hr)
                (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q)) (wt_nonneg c₂ r))
              linarith
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- The average of `fG` over two blocks. -/
private def avg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (c c' : Z2 L) : ℝ :=
  ∑ q : BlockIndex L W, ∑ r : BlockIndex L W, wt c q * (wt c' r * fG E u M q r)

/-- Two long edges bounded pointwise, the edge `c₁`–`c₂` averaged. -/
private theorem tri_le_avg12 {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} {c₁ c₂ c₃ : Z2 L}
    {B : ℝ} (h : ∀ p q r : BlockIndex L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ →
      fG E u M p q * fG E u M r p ≤ B) :
    tri E u M c₁ c₂ c₃ ≤ B * avg E u M c₁ c₂ := by
  calc tri E u M c₁ c₂ c₃
      ≤ ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ∑ r : BlockIndex L W,
          wt c₃ p * (B * (wt c₁ q * (wt c₂ r * fG E u M q r))) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have hX : 0 ≤ wt c₃ p * wt c₁ q * wt c₂ r * fG E u M q r :=
                mul_nonneg (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q))
                  (wt_nonneg c₂ r)) (fG_nonneg E u M q r)
              have := mul_le_mul_of_nonneg_left (h p q r hp hq hr) hX
              calc wt c₃ p * wt c₁ q * wt c₂ r * (fG E u M p q * fG E u M q r * fG E u M r p)
                  = wt c₃ p * wt c₁ q * wt c₂ r * fG E u M q r *
                      (fG E u M p q * fG E u M r p) := by ring
                _ ≤ wt c₃ p * wt c₁ q * wt c₂ r * fG E u M q r * B := this
                _ = wt c₃ p * (B * (wt c₁ q * (wt c₂ r * fG E u M q r))) := by ring
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B * avg E u M c₁ c₂ := by
        unfold avg
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- Two long edges bounded pointwise, the edge `c₂`–`c₃` averaged. -/
private theorem tri_le_avg23 {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} {c₁ c₂ c₃ : Z2 L}
    {B : ℝ} (h : ∀ p q r : BlockIndex L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ →
      fG E u M p q * fG E u M q r ≤ B) :
    tri E u M c₁ c₂ c₃ ≤ B * avg E u M c₃ c₂ := by
  calc tri E u M c₁ c₂ c₃
      ≤ ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ∑ r : BlockIndex L W,
          wt c₁ q * (B * (wt c₃ p * (wt c₂ r * fG E u M p r))) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have hX : 0 ≤ wt c₃ p * wt c₁ q * wt c₂ r * fG E u M p r :=
                mul_nonneg (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q))
                  (wt_nonneg c₂ r)) (fG_nonneg E u M p r)
              have := mul_le_mul_of_nonneg_left (h p q r hp hq hr) hX
              rw [fG_comm E u M r p]
              calc wt c₃ p * wt c₁ q * wt c₂ r * (fG E u M p q * fG E u M q r * fG E u M p r)
                  = wt c₃ p * wt c₁ q * wt c₂ r * fG E u M p r *
                      (fG E u M p q * fG E u M q r) := by ring
                _ ≤ wt c₃ p * wt c₁ q * wt c₂ r * fG E u M p r * B := this
                _ = wt c₁ q * (B * (wt c₃ p * (wt c₂ r * fG E u M p r))) := by ring
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B * avg E u M c₃ c₂ := by
        unfold avg
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- The average over two blocks: the diagonal `q = r` costs `2Λ W⁻²`, the rest `A`. -/
private theorem avg_le {E u : ℝ} {M : Matrix (Idx L W) (Idx L W) ℂ} {Λ A : ℝ}
    (h6 : ∀ q r : BlockIndex L W, fG E u M q r ≤ 2 * Λ)
    (h8 : ∀ q r : BlockIndex L W, q ≠ r → fG E u M q r ≤ A) (hA : 0 ≤ A) (c c' : Z2 L) :
    avg E u M c c' ≤ 2 * Λ * ((W : ℝ) ^ 2)⁻¹ + A := by
  have hin : ∀ q : BlockIndex L W, ∑ r : BlockIndex L W, wt c' r * fG E u M q r ≤
      2 * Λ * ((W : ℝ) ^ 2)⁻¹ + A := by
    intro q
    have hΛ : 0 ≤ 2 * Λ := (fG_nonneg E u M q q).trans (h6 q q)
    calc ∑ r : BlockIndex L W, wt c' r * fG E u M q r
        ≤ ∑ r : BlockIndex L W, ((if r = q then wt c' r * (2 * Λ) else 0) + wt c' r * A) := by
          refine Finset.sum_le_sum fun r _ => ?_
          by_cases hr : r = q
          · subst hr
            simp only [ite_true]
            have := mul_le_mul_of_nonneg_left (h6 r r) (wt_nonneg c' r)
            have := mul_nonneg (wt_nonneg c' r) hA
            linarith
          · simp only [hr, ite_false, zero_add]
            exact mul_le_mul_of_nonneg_left (h8 q r (Ne.symm hr)) (wt_nonneg c' r)
      _ = wt c' q * (2 * Λ) + A := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_mul, sum_wt, one_mul]
          simp
      _ ≤ 2 * Λ * ((W : ℝ) ^ 2)⁻¹ + A := by
          have := mul_le_mul_of_nonneg_right (wt_le c' q) hΛ
          linarith
  calc avg E u M c c' ≤ ∑ q : BlockIndex L W, wt c q * (2 * Λ * ((W : ℝ) ^ 2)⁻¹ + A) := by
        unfold avg
        refine Finset.sum_le_sum fun q _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hin q) (wt_nonneg c q)
    _ = 2 * Λ * ((W : ℝ) ^ 2)⁻¹ + A := by
        rw [← Finset.sum_mul, sum_wt, one_mul]

end Tri

/-! ## 3. The entry bounds (e6)–(e8) for `fG`, and the prefactor (e9) -/

section Entries

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem fG_e6 (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) :
    fG E u M p q ≤ 2 * Λ :=
  max_le (LemDecCalE_e6_of_hyp h true p q) (LemDecCalE_e6_of_hyp h true q p)

private theorem fG_e7 (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W)
    (hd : ellStar L W u / 8 + 2 ≤ (zdist2 L (p.1 - q.1) : ℝ)) :
    fG E u M p q ^ 2 ≤ 25 * Λ * ((W : ℝ) ^ (-D) + jStarMat L W E D u M *
      tailT L W E D u ((zdist2 L (p.1 - q.1) : ℝ) - 2)) := by
  have hc := zdist2_comm p.1 q.1
  refine fG_sq_le ?_ (LemDecCalE_e7 h q p hd)
  have := LemDecCalE_e7 h p q (by rw [← hc]; exact hd)
  rwa [← hc] at this

private theorem fG_e8 (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) (hpq : p ≠ q) :
    fG E u M p q ^ 2 ≤
      50 * Λ * K₀ * (scaleM L W E u)⁻¹ * (1 + jStarMat L W E D u M / scaleM L W E u) :=
  fG_sq_le (LemDecCalE_e8 h p q hpq).2 (LemDecCalE_e8 h q p (Ne.symm hpq)).2

/-- Prefactor (e9): `|𝓔^{(G̃)}| ≤ W² Λρ²M_u⁻¹ Σ_b (|𝓛¹_b| + |𝓛²_b|)`. -/
private theorem EGt_le_pref (h : E2Hyp L W E s u v D Λ K₀ M) (a₁ a₂ : Z2 L) :
    ‖EGt L W E u M a₁ a₂‖ ≤ (W : ℝ) ^ 2 *
      (Λ * (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹) *
      ∑ b : Z2 L, (‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
        ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖) := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  set A : ℝ := Λ * (ellT L u / ellT L s) ^ 2 * (scaleM L W E u)⁻¹ with hAdef
  have hA : ∀ σ a, ‖avgErr L W E u M σ a‖ ≤ A := fun σ a => LemDecCalE_e9 hgood σ a
  have hSB : ∀ b : Z2 L, ∑ a : Z2 L, ‖SB L a b‖ = 1 := by
    intro b
    rw [← KLoop.sum_norm_SB_row L hL3 b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
  set F : Z2 L → ℝ := fun b => ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
    ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖ with hF
  unfold EGt
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  calc (W : ℝ) ^ 2 * ‖∑ a : Z2 L, ∑ b : Z2 L,
        (avgErr L W E u M true a * SB L a b * loop3 L W E u M ![true, true, false] ![b, a₁, a₂] +
          avgErr L W E u M false a * SB L a b *
            loop3 L W E u M ![true, false, false] ![a₁, b, a₂])‖
      ≤ (W : ℝ) ^ 2 * ∑ a : Z2 L, ∑ b : Z2 L, A * (‖SB L a b‖ * F b) := by
        refine mul_le_mul_of_nonneg_left ?_ hW2
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hF]
        have h1 := hA true a
        have h2 := hA false a
        have hs := norm_nonneg (SB L a b)
        have hl1 := norm_nonneg (loop3 L W E u M ![true, true, false] ![b, a₁, a₂])
        have hl2 := norm_nonneg (loop3 L W E u M ![true, false, false] ![a₁, b, a₂])
        have e1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hs hl1)
        have e2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hs hl2)
        calc ‖avgErr L W E u M true a‖ * ‖SB L a b‖ *
              ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
            ‖avgErr L W E u M false a‖ * ‖SB L a b‖ *
              ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖
            = ‖avgErr L W E u M true a‖ * (‖SB L a b‖ *
                ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖) +
              ‖avgErr L W E u M false a‖ * (‖SB L a b‖ *
                ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖) := by ring
          _ ≤ A * (‖SB L a b‖ * ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖) +
              A * (‖SB L a b‖ * ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖) :=
            add_le_add e1 e2
          _ = A * (‖SB L a b‖ * (‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
              ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖)) := by ring
    _ = (W : ℝ) ^ 2 * A * ∑ b : Z2 L, F b := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul, hSB, one_mul]
        ring

/-- Both three-loops of `𝓔^{(G̃)}` are bounded by the triangle sum at `(a₁, b, a₂)`. -/
private theorem loops_le_tri (hH : M.IsHermitian) (a₁ a₂ b : Z2 L) :
    ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
        ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖ ≤ 2 * tri E u M a₁ b a₂ := by
  have h1 := norm_loop3_le_tri (E := E) (u := u) hH true true false b a₁ a₂
  have h2 := norm_loop3_le_tri (E := E) (u := u) hH true false false a₁ b a₂
  rw [tri_swap] at h1
  linarith

end Entries

/-! ## 4. Scale facts under `E2Hyp` -/

section Facts

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem one_le_L' : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)

private theorem one_le_W' : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)

/-- The scale facts used below: `1 < W`, `1 ≤ M_u ≤ W²`, `ℓ_u ≥ 1`, `ρ ≥ 1`, `1 ≤ J ≤ W`,
`log W ≥ 4`, `ℓ*_u ≥ 8`, `W^{-D} ≤ (L²W¹²)⁻²`. -/
private theorem facts (h : E2Hyp L W E s u v D Λ K₀ M) :
    (1 : ℝ) < W ∧ 1 ≤ scaleM L W E u ∧ scaleM L W E u ≤ (W : ℝ) ^ 2 ∧ 1 ≤ ellT L u ∧
      1 ≤ ellT L u / ellT L s ∧ 1 ≤ jStarMat L W E D u M ∧ jStarMat L W E D u M ≤ W ∧
      4 ≤ Real.log W ∧ 8 ≤ ellStar L W u ∧
      (W : ℝ) ^ (-D) ≤ (((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹) ^ 2 := by
  obtain ⟨hW1, -, -, -⟩ := LemDecCalE_floor h
  have h2 := LemDecCalE_e2 h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ1 : 1 ≤ ellT L u := one_le_ellT one_le_L' hu0 hu1
  have hℓs := (ellT_pos_le (L := L) one_le_L' (hsu.trans_lt hu1)).1
  have hρ : 1 ≤ ellT L u / ellT L s := by
    rw [one_le_div hℓs]
    exact (ellT_mono_ratio one_le_L' hs0 hsu hu1).1
  have h48 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpow : (4 : ℝ) ^ ((3 : ℝ) / 2) ≤ Real.log (W : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
  have hstar : 8 ≤ ellStar L W u := by
    unfold ellStar
    have h0 : 0 ≤ Real.log (W : ℝ) ^ ((3 : ℝ) / 2) := by linarith
    nlinarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hWD : (W : ℝ) ^ (-D) ≤ (((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹) ^ 2 := by
    have hsplit : (W : ℝ) ^ (-D) = ((W : ℝ) ^ (D / 2) * (W : ℝ) ^ (D / 2))⁻¹ := by
      rw [← Real.rpow_add hW0, Real.rpow_neg hW0.le]
      congr 2; ring
    rw [hsplit, inv_pow, sq]
    have hp : (0 : ℝ) < (L : ℝ) ^ 2 * (W : ℝ) ^ 12 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    exact inv_anti₀ (mul_pos hp hp) (mul_le_mul hfloor hfloor hp.le (hp.le.trans hfloor))
  exact ⟨hW1, hMv.trans h2.2.1, h2.2.2, hℓ1, hρ, one_le_jStarMat L W one_le_W' E D u M, hJ, hlog,
    hstar, hWD⟩

end Facts

/-! ## 5. The near bound: `Σ_b (|𝓛¹_b| + |𝓛²_b|) ≤ 1162 Λ³ (log(L²W¹²))⁴ ℓ_u² ρ⁴ M_u⁻²` -/

section Near

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- The far edge of the near case: beyond `R = 4 (log(L²W¹²))² ℓ_u`,
`fG ≤ 125 Λ J (L²W¹²)⁻¹` ((e7), the floor, `√((R-2)/ℓ_u) ≥ 2 log(L²W¹²) - 1`). -/
private theorem fG_near_far (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W)
    (hd : 4 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2 * ellT L u <
      (zdist2 L (p.1 - q.1) : ℝ)) :
    fG E u M p q ≤ 125 * Λ * jStarMat L W E D u M * ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹ := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have h7 := fG_e7 h p q
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Z : ℝ := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hZ
  have hZ0 : 0 < Z := by positivity
  set Lg : ℝ := Real.log Z with hLg
  set ℓ := ellT L u with hℓ
  set J := jStarMat L W E D u M with hJdef
  set X : ℝ := Z⁻¹ with hX
  have hX0 : 0 < X := inv_pos.2 hZ0
  set x : ℝ := (zdist2 L (p.1 - q.1) : ℝ) with hx
  -- `Lg ≥ 12 log W ≥ 48`
  have hLg48 : 48 ≤ Lg := by
    have h1 : Real.log ((W : ℝ) ^ 12) ≤ Lg := by
      rw [hLg]
      apply Real.log_le_log (by positivity)
      have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast one_le_L')
      nlinarith [pow_pos hW0 12]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlgLg : Real.log W ≤ Lg := by
    have h1 : Real.log ((W : ℝ) ^ 12) ≤ Lg := by
      rw [hLg]
      apply Real.log_le_log (by positivity)
      have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast one_le_L')
      nlinarith [pow_pos hW0 12]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  -- `ℓ*/8 + 2 ≤ 4 Lg² ℓ`
  have hstarR : ellStar L W u / 8 + 2 ≤ 4 * Lg ^ 2 * ℓ := by
    have h1 : Real.log (W : ℝ) ^ ((3 : ℝ) / 2) ≤ Real.log (W : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_two] at h1
    have h2 : Real.log (W : ℝ) ^ 2 ≤ Lg ^ 2 := pow_le_pow_left₀ (by linarith) hlgLg 2
    have h3 : ellStar L W u ≤ Lg ^ 2 * ℓ := by
      unfold ellStar
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (by linarith)
    have h4 : Lg ^ 2 ≤ Lg ^ 2 * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
    have h5 : 48 * 48 ≤ Lg ^ 2 := by
      rw [sq]; exact mul_le_mul hLg48 hLg48 (by norm_num) (by linarith)
    linarith
  have hd' : ellStar L W u / 8 + 2 ≤ x := by linarith
  have h7' := h7 hd'
  -- the tail at `x - 2`
  have hT1 : tailT L W E D u (x - 2) ≤ tailT L W E D u (4 * Lg ^ 2 * ℓ - 2) :=
    LemDecCalE_tailT_anti one_le_L' hu1 (by linarith)
  have hsq : 2 * Lg - 1 ≤ Real.sqrt ((4 * Lg ^ 2 * ℓ - 2) / ℓ) := by
    have hℓ0 : 0 < ℓ := by linarith
    have h4 : 191 * 1 ≤ (4 * Lg - 1) * ℓ := mul_le_mul (by linarith) hℓ1 zero_le_one (by linarith)
    have h5 : Lg ^ 2 ≤ Lg ^ 2 * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
    have h6 : 0 ≤ Lg ^ 2 := by positivity
    rw [Real.le_sqrt (by linarith) (div_nonneg (by linarith) hℓ0.le), le_div_iff₀ hℓ0]
    have e : (2 * Lg - 1) ^ 2 * ℓ = 4 * Lg ^ 2 * ℓ - (4 * Lg - 1) * ℓ := by ring
    rw [e]
    linarith
  have hexpZ : Real.exp (-Lg) = X := by
    rw [Real.exp_neg, hLg, Real.exp_log hZ0]
  have hexp : Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ℓ - 2) / ℓ)) ≤ Real.exp 1 * X ^ 2 := by
    calc Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ℓ - 2) / ℓ)) ≤ Real.exp (1 + -Lg + -Lg) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 * X ^ 2 := by rw [Real.exp_add, Real.exp_add, hexpZ]; ring
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have hMinv : (scaleM L W E u ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hM1)
  have hT2 : tailT L W E D u (4 * Lg ^ 2 * ℓ - 2) ≤ 4 * X ^ 2 := by
    unfold tailT
    have h0 : 0 ≤ Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ℓ - 2) / ℓ)) := (Real.exp_pos _).le
    have h1 : (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ℓ - 2) / ℓ)) ≤
        1 * (Real.exp 1 * X ^ 2) := mul_le_mul hMinv hexp h0 zero_le_one
    have : Real.exp 1 * X ^ 2 ≤ 3 * X ^ 2 := mul_le_mul_of_nonneg_right he3 (by positivity)
    linarith
  have hsq2 : fG E u M p q ^ 2 ≤ 125 * Λ * J * X ^ 2 := by
    have hJ0 : 0 ≤ J := by linarith
    have e1 := mul_le_mul_of_nonneg_left (hT1.trans hT2) hJ0
    have e2 : X ^ 2 ≤ J * X ^ 2 := le_mul_of_one_le_left (by positivity) hJ1
    have hΛ0 : 0 ≤ Λ := by linarith
    have e3 := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 25 * Λ)
    calc fG E u M p q ^ 2 ≤ 25 * Λ * ((W : ℝ) ^ (-D) + J * tailT L W E D u (x - 2)) := h7'
      _ ≤ 25 * Λ * (X ^ 2 + J * (4 * X ^ 2)) := by gcongr
      _ = 25 * Λ * X ^ 2 + 100 * Λ * (J * X ^ 2) := by ring
      _ ≤ 25 * Λ * (J * X ^ 2) + 100 * Λ * (J * X ^ 2) := by linarith
      _ = 125 * Λ * J * X ^ 2 := by ring
  have hb : 0 ≤ 125 * Λ * J * X := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    positivity
  rw [← pow_le_pow_iff_left₀ (fG_nonneg E u M p q) hb (two_ne_zero)]
  refine hsq2.trans ?_
  have h1 : 1 ≤ 125 * Λ * J := by
    have := mul_le_mul hΛ hJ1 zero_le_one (by linarith)
    linarith
  have : 125 * Λ * J * X ^ 2 ≤ (125 * Λ * J) ^ 2 * X ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 125 * Λ * J)
    rw [sq]; linarith
  calc 125 * Λ * J * X ^ 2 ≤ (125 * Λ * J) ^ 2 * X ^ 2 := this
    _ = (125 * Λ * J * X) ^ 2 := by ring

/-- A three-loop is at most `Λ ρ⁴ M_u⁻²` (clause 2 of `goodSet` at `k = 3`). -/
private theorem loop3_le_good (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Fin 3 → Bool)
    (a : Fin 3 → Z2 L) :
    ‖loop3 L W E u M σ a‖ ≤
      Λ * (ellT L u / ellT L s) ^ 4 * ((scaleM L W E u)⁻¹) ^ 2 := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have := hgood.2.1 3 (by simp) σ a
  exact this

/-- **Near sum**: `Σ_b (|𝓛¹_b| + |𝓛²_b|) ≤ 1162 Λ³ (log(L²W¹²))⁴ ℓ_u² ρ⁴ M_u⁻²` (for all
`a₁, a₂`). -/
private theorem near_sum (h : E2Hyp L W E s u v D Λ K₀ M) (a₁ a₂ : Z2 L) :
    ∑ b : Z2 L, (‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
        ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖) ≤
      1162 * Λ ^ 3 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 4 * ellT L u ^ 2 *
        (ellT L u / ellT L s) ^ 4 * ((scaleM L W E u)⁻¹) ^ 2 := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have hfar := fG_near_far h
  have h6 := fG_e6 h
  have hclose := loop3_le_good h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hH := hgood.1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Z : ℝ := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hZ
  have hZ0 : 0 < Z := by positivity
  set Lg : ℝ := Real.log Z with hLg
  set ℓ := ellT L u with hℓ
  set ρ := ellT L u / ellT L s with hρdef
  set J := jStarMat L W E D u M with hJdef
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  set X : ℝ := Z⁻¹ with hX
  set R : ℝ := 4 * Lg ^ 2 * ℓ with hR
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hX0 : 0 ≤ X := (inv_pos.2 hZ0).le
  have hm0 : 0 ≤ m := by positivity
  have hLg48 : 48 ≤ Lg := by
    have h1 : Real.log ((W : ℝ) ^ 12) ≤ Lg := by
      rw [hLg]
      apply Real.log_le_log (by positivity)
      have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast one_le_L')
      nlinarith [pow_pos hW0 12]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  set F : Z2 L → ℝ := fun b => ‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
    ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖ with hF
  set c : ℝ := 500 * Λ ^ 3 * J * X with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ b : Z2 L, F b ≤
      (if (zdist2 L (a₁ - b) : ℝ) ≤ R then 2 * (Λ * ρ ^ 4 * m ^ 2) else 0) + 2 * c := by
    intro b
    by_cases hb : (zdist2 L (a₁ - b) : ℝ) ≤ R
    · simp only [hb, ↓reduceIte]
      have e1 := hclose ![true, true, false] ![b, a₁, a₂]
      have e2 := hclose ![true, false, false] ![a₁, b, a₂]
      simp only [hF]
      linarith
    · simp only [hb, ↓reduceIte, zero_add]
      refine (loops_le_tri hH a₁ a₂ b).trans ?_
      have ht : tri E u M a₁ b a₂ ≤ c := by
        refine tri_le_of_pt fun p q r hp hq hr => ?_
        have f1 := h6 p q
        have f3 := h6 r p
        have f2 : fG E u M q r ≤ 125 * Λ * J * X := by
          apply hfar q r
          rw [hq, hr]
          exact not_le.1 hb
        have n1 := fG_nonneg E u M p q
        have n2 := fG_nonneg E u M q r
        have n3 := fG_nonneg E u M r p
        calc fG E u M p q * fG E u M q r * fG E u M r p
            ≤ (2 * Λ) * (125 * Λ * J * X) * (2 * Λ) :=
              mul_le_mul (mul_le_mul f1 f2 n2 (by linarith)) f3 n3
                (mul_nonneg (by linarith) (by positivity))
          _ = c := by rw [hc]; ring
      linarith
  have hsum : ∑ b : Z2 L, F b ≤
      ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₁ - b) : ℝ) ≤ R).card : ℝ) *
          (2 * (Λ * ρ ^ 4 * m ^ 2)) + ((L : ℝ) * L) * (2 * c) := by
    refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp [Finset.card_univ, ZMod.card]
  -- the count
  have hcard := LemDecCalE_e10a a₁ R (by positivity)
  have hLg2ℓ : 1 ≤ Lg ^ 2 * ℓ := by
    have h5 : 48 * 48 ≤ Lg ^ 2 := by
      rw [sq]; exact mul_le_mul hLg48 hLg48 (by norm_num) (by linarith)
    have h4 : Lg ^ 2 ≤ Lg ^ 2 * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
    linarith
  have hR9 : (2 * R + 1) ^ 2 ≤ 81 * Lg ^ 4 * ℓ ^ 2 := by
    have h1 : 2 * R + 1 ≤ 9 * (Lg ^ 2 * ℓ) := by rw [hR]; linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    calc (2 * R + 1) ^ 2 ≤ (9 * (Lg ^ 2 * ℓ)) ^ 2 := h2
      _ = 81 * Lg ^ 4 * ℓ ^ 2 := by ring
  -- the far part: `L² J X ≤ M_u⁻²`
  have hMpos : 0 < scaleM L W E u := by linarith
  have hWm : ((W : ℝ) ^ 2)⁻¹ ≤ m := inv_anti₀ hMpos hMW
  have hfarpart : (L : ℝ) * L * (J * X) ≤ m ^ 2 := by
    have e1 : (L : ℝ) * L * (J * X) = J * ((W : ℝ) ^ 12)⁻¹ := by
      rw [hX, hZ]; field_simp
    have e2 : J * ((W : ℝ) ^ 12)⁻¹ ≤ (W : ℝ) * ((W : ℝ) ^ 12)⁻¹ :=
      mul_le_mul_of_nonneg_right hJW (by positivity)
    have e3 : (W : ℝ) * ((W : ℝ) ^ 12)⁻¹ = ((W : ℝ) ^ 11)⁻¹ := by
      field_simp
    have e4 : ((W : ℝ) ^ 11)⁻¹ ≤ (((W : ℝ) ^ 2) ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      rw [← pow_mul]
      exact pow_le_pow_right₀ hW1.le (by norm_num)
    have e5 : (((W : ℝ) ^ 2) ^ 2)⁻¹ ≤ m ^ 2 := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) hWm 2
    rw [e1]
    linarith
  -- assemble
  have hP : 1 ≤ Lg ^ 4 * ℓ ^ 2 * ρ ^ 4 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hℓ1))
      (one_le_pow₀ hρ)
  have hΛ3 : Λ ≤ Λ ^ 3 := le_self_pow₀ hΛ (by norm_num)
  have hcardP : ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₁ - b) : ℝ) ≤ R).card : ℝ) *
      (2 * (Λ * ρ ^ 4 * m ^ 2)) ≤ 162 * Λ ^ 3 * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_right (hcard.trans hR9)
      (by positivity : (0 : ℝ) ≤ 2 * (Λ * ρ ^ 4 * m ^ 2))
    have e2 : 81 * Lg ^ 4 * ℓ ^ 2 * (2 * (Λ * ρ ^ 4 * m ^ 2)) =
        162 * Λ * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := by ring
    have e3 : 162 * Λ * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 ≤
        162 * Λ ^ 3 * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := by
      have : 0 ≤ (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := by positivity
      nlinarith
    linarith
  have hfarP : (L : ℝ) * L * (2 * c) ≤ 1000 * Λ ^ 3 * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := by
    have e1 : (L : ℝ) * L * (2 * c) = 1000 * Λ ^ 3 * ((L : ℝ) * L * (J * X)) := by
      rw [hc]; ring
    have hΛ30 : 0 ≤ 1000 * Λ ^ 3 := by positivity
    have e2 := mul_le_mul_of_nonneg_left hfarpart hΛ30
    have e3 : m ^ 2 ≤ (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 :=
      le_mul_of_one_le_left (by positivity) hP
    have e4 := mul_le_mul_of_nonneg_left e3 hΛ30
    rw [e1]
    linarith
  calc ∑ b : Z2 L, F b ≤ _ := hsum
    _ ≤ 162 * Λ ^ 3 * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 +
        1000 * Λ ^ 3 * (Lg ^ 4 * ℓ ^ 2 * ρ ^ 4) * m ^ 2 := add_le_add hcardP hfarP
    _ = 1162 * Λ ^ 3 * Lg ^ 4 * ℓ ^ 2 * ρ ^ 4 * m ^ 2 := by ring

end Near

/-! ## 6. The far bound: `Σ_b tri ≤ 2·10⁹ (1 + log W)³ K₀ e^{Y} Λ² J² ℓ_u² M_u^{-1/2} 𝒯_u(d)` -/

section Far

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

omit [NeZero L] [NeZero W] in
/-- `W^{-D} ≤ 𝒯_{u,D}(x)`. -/
private theorem WD_le_tailT (E D u x : ℝ) : (W : ℝ) ^ (-D) ≤ tailT L W E D u x := by
  unfold tailT
  have : 0 ≤ (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt (x / ellT L u)) := by positivity
  linarith

/-- `𝒯_u(x) ≤ e^{(log W)^{3/4}} 𝒯_u(d)` for `x ≥ d - ℓ*_u` (`tellStar` with `C = 1`). -/
private theorem tail_le_Y {E D u : ℝ} (hu : u < 1) {d x : ℝ} (hx : d - ellStar L W u ≤ x) :
    tailT L W E D u x ≤ Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D u d := by
  have h1 := LemDecCalE_tailT_anti (W := W) (E := E) (D := D) (one_le_L' (L := L)) hu hx
  have h2 := tellStar L W E D u 1 d hu zero_le_one
  simp only [Real.sqrt_one, one_mul] at h2
  exact h1.trans h2

/-- A long edge of the far case: `fG² ≤ 50 Λ J e^{Y} 𝒯_u(d)` if its length `x` has
`x ≥ ℓ*/8 + 2` and `x - 2 ≥ d - ℓ*` ((e7), `tellStar`). -/
private theorem fG_long (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) {d x : ℝ}
    (hx : (zdist2 L (p.1 - q.1) : ℝ) = x) (h1 : ellStar L W u / 8 + 2 ≤ x)
    (h2 : d - ellStar L W u ≤ x - 2) :
    fG E u M p q ^ 2 ≤ 50 * Λ * jStarMat L W E D u M *
      Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D u d := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have h7 := fG_e7 h p q (by rw [hx]; exact h1)
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu1 : u < 1 := huv.trans_lt hv1
  rw [hx] at h7
  set J := jStarMat L W E D u M
  set eY := Real.exp (Real.log W ^ ((3 : ℝ) / 4))
  set T := tailT L W E D u d
  have hT0 : 0 ≤ T := (tailT_pos one_le_W' L E D u d).le
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hTY := tail_le_Y (L := L) (W := W) (E := E) (D := D) hu1 h2
  have hWT := WD_le_tailT (L := L) (W := W) E D u d
  have hJY : 1 ≤ J * eY := one_le_mul_of_one_le_of_one_le hJ1 heY
  have e1 : T ≤ J * eY * T := le_mul_of_one_le_left hT0 hJY
  have e2 : J * tailT L W E D u (x - 2) ≤ J * (eY * T) :=
    mul_le_mul_of_nonneg_left hTY (by linarith)
  have hΛ0 : 0 ≤ 25 * Λ := by linarith
  calc fG E u M p q ^ 2 ≤ 25 * Λ * ((W : ℝ) ^ (-D) + J * tailT L W E D u (x - 2)) := h7
    _ ≤ 25 * Λ * (J * eY * T + J * eY * T) := by
        apply mul_le_mul_of_nonneg_left _ hΛ0
        have : J * (eY * T) = J * eY * T := by ring
        linarith
    _ = 50 * Λ * J * eY * T := by ring

/-- An edge of length `x ≥ ℓ*/8 + 2`: `fG ≤ √(225 Λ J) √𝒯_u(x)` ((e7), shift by `2`). -/
private theorem fG_sqrt (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) {x : ℝ}
    (hx : (zdist2 L (p.1 - q.1) : ℝ) = x) (h1 : ellStar L W u / 8 + 2 ≤ x) :
    fG E u M p q ≤ Real.sqrt (225 * Λ * jStarMat L W E D u M) *
      Real.sqrt (tailT L W E D u x) := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have h7 := fG_e7 h p q (by rw [hx]; exact h1)
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  rw [hx] at h7
  set J := jStarMat L W E D u M
  set T := tailT L W E D u x
  have hT0 : 0 ≤ T := (tailT_pos one_le_W' L E D u x).le
  have hsh := LemDecCalE_tailT_shift (L := L) (W := W) (E := E) (D := D) one_le_L' hu0 hu1
    (c := 2) (by norm_num) x
  have he8 : Real.exp (Real.sqrt 2) ≤ 8 := by
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]; norm_num
    have h1' : Real.exp (Real.sqrt 2) ≤ Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have h2' := Real.exp_one_lt_d9
    have h3' : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hsh8 : tailT L W E D u (x - 2) ≤ 8 * T :=
    hsh.trans (mul_le_mul_of_nonneg_right he8 hT0)
  have hWT := WD_le_tailT (L := L) (W := W) E D u x
  have hJT : T ≤ J * T := le_mul_of_one_le_left hT0 hJ1
  have hsq : fG E u M p q ^ 2 ≤ 225 * Λ * J * T := by
    have e2 : J * tailT L W E D u (x - 2) ≤ J * (8 * T) :=
      mul_le_mul_of_nonneg_left hsh8 (by linarith)
    have hΛ0 : 0 ≤ 25 * Λ := by linarith
    calc fG E u M p q ^ 2 ≤ 25 * Λ * ((W : ℝ) ^ (-D) + J * tailT L W E D u (x - 2)) := h7
      _ ≤ 25 * Λ * (J * T + J * (8 * T)) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          linarith
      _ = 225 * Λ * J * T := by ring
  have hc0 : 0 ≤ 225 * Λ * J := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    positivity
  rw [← Real.sqrt_mul hc0, ← Real.sqrt_sq (fG_nonneg E u M p q)]
  exact Real.sqrt_le_sqrt hsq

/-- An off-diagonal entry: `fG ≤ 10 Λ K₀ J √(M_u⁻¹)` ((e8)). -/
private theorem fG_off (h : E2Hyp L W E s u v D Λ K₀ M) (p q : BlockIndex L W) (hpq : p ≠ q) :
    fG E u M p q ≤ 10 * Λ * K₀ * jStarMat L W E D u M * Real.sqrt ((scaleM L W E u)⁻¹) := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have h8 := fG_e8 h p q hpq
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  set J := jStarMat L W E D u M
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  have hMpos : 0 < scaleM L W E u := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hJM : J / scaleM L W E u = J * m := by rw [hm, div_eq_mul_inv]
  rw [hJM] at h8
  have hJm : 1 + J * m ≤ 2 * J := by
    have : J * m ≤ J * 1 := mul_le_mul_of_nonneg_left hm1 (by linarith)
    linarith
  have hΛK : 1 ≤ Λ * K₀ * J :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hΛ hK) hJ1
  have hsq : fG E u M p q ^ 2 ≤ (10 * Λ * K₀ * J * Real.sqrt m) ^ 2 := by
    have e0 : 0 ≤ 50 * Λ * K₀ * m := by
      have : 0 ≤ Λ := by linarith
      have : 0 ≤ K₀ := by linarith
      positivity
    have e1 := mul_le_mul_of_nonneg_left hJm e0
    have e2 : (10 * Λ * K₀ * J * Real.sqrt m) ^ 2 = 100 * (Λ * K₀ * J) ^ 2 * m := by
      rw [mul_pow, Real.sq_sqrt hm0]; ring
    have e3 : Λ * K₀ * J ≤ (Λ * K₀ * J) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by linarith) hΛK
    have e4 := mul_le_mul_of_nonneg_right e3 (by positivity : (0 : ℝ) ≤ 100 * m)
    rw [e2]
    calc fG E u M p q ^ 2 ≤ 50 * Λ * K₀ * m * (1 + J * m) := h8
      _ ≤ 50 * Λ * K₀ * m * (2 * J) := e1
      _ = Λ * K₀ * J * (100 * m) := by ring
      _ ≤ (Λ * K₀ * J) ^ 2 * (100 * m) := e4
      _ = 100 * (Λ * K₀ * J) ^ 2 * m := by ring
  have hb : 0 ≤ 10 * Λ * K₀ * J * Real.sqrt m := by
    have : 0 ≤ Λ * K₀ * J := by linarith
    have : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
    nlinarith
  exact (pow_le_pow_iff_left₀ (fG_nonneg E u M p q) hb two_ne_zero).1 hsq

/-- The block average: `avg ≤ 12 Λ K₀ J √(M_u⁻¹)`. -/
private theorem avg_le_hyp (h : E2Hyp L W E s u v D Λ K₀ M) (c c' : Z2 L) :
    avg E u M c c' ≤ 12 * Λ * K₀ * jStarMat L W E D u M * Real.sqrt ((scaleM L W E u)⁻¹) := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have h6 := fG_e6 h
  have hoff := fG_off h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  set J := jStarMat L W E D u M
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  have hMpos : 0 < scaleM L W E u := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hΛK : 1 ≤ K₀ * J := one_le_mul_of_one_le_of_one_le hK hJ1
  have hsm : m ≤ Real.sqrt m := by
    rw [Real.le_sqrt hm0 hm0, sq]
    exact mul_le_of_le_one_left hm0 hm1
  have hWm : ((W : ℝ) ^ 2)⁻¹ ≤ Real.sqrt m := (inv_anti₀ hMpos hMW).trans hsm
  have hA0 : 0 ≤ 10 * Λ * K₀ * J * Real.sqrt m := by
    have : 0 ≤ Λ * K₀ * J := by
      have := one_le_mul_of_one_le_of_one_le hΛ hΛK
      linarith [mul_assoc Λ K₀ J]
    have : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
    nlinarith
  have hav := avg_le (E := E) (u := u) (M := M) (Λ := Λ) h6 hoff hA0 c c'
  have hs0' : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have e1 : 2 * Λ * ((W : ℝ) ^ 2)⁻¹ ≤ 2 * Λ * Real.sqrt m :=
    mul_le_mul_of_nonneg_left hWm (by linarith)
  have e2 : 2 * Λ * Real.sqrt m ≤ 2 * Λ * (K₀ * J) * Real.sqrt m := by
    have : 0 ≤ 2 * Λ * Real.sqrt m := by
      have : 0 ≤ Λ := by linarith
      positivity
    nlinarith
  calc avg E u M c c' ≤ 2 * Λ * ((W : ℝ) ^ 2)⁻¹ + 10 * Λ * K₀ * J * Real.sqrt m := hav
    _ ≤ 2 * Λ * (K₀ * J) * Real.sqrt m + 10 * Λ * K₀ * J * Real.sqrt m := by linarith
    _ = 12 * Λ * K₀ * J * Real.sqrt m := by ring

/-- AM–GM: `x² ≤ B`, `y² ≤ B` give `x y ≤ B`. -/
private theorem mul_le_of_sq_le {x y B : ℝ} (h1 : x ^ 2 ≤ B) (h2 : y ^ 2 ≤ B) : x * y ≤ B := by
  nlinarith [sq_nonneg (x - y)]

/-- The far case, one `b`: `b` within `ℓ*_u/2` of `a₁` (edge `a₁`–`b` averaged), within `ℓ*_u/2`
of `a₂` (edge `b`–`a₂` averaged), or far from both (three long edges). -/
private theorem far_pt (h : E2Hyp L W E s u v D Λ K₀ M) (a₁ a₂ b : Z2 L)
    (hd : ellStar L W u < (zdist2 L (a₁ - a₂) : ℝ)) :
    tri E u M a₁ b a₂ ≤
      (if (zdist2 L (a₁ - b) : ℝ) ≤ ellStar L W u / 2 then
          50 * Λ * jStarMat L W E D u M * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) *
            tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) *
              (12 * Λ * K₀ * jStarMat L W E D u M * Real.sqrt ((scaleM L W E u)⁻¹)) else 0) +
        (if (zdist2 L (a₂ - b) : ℝ) ≤ ellStar L W u / 2 then
          50 * Λ * jStarMat L W E D u M * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) *
            tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) *
              (12 * Λ * K₀ * jStarMat L W E D u M * Real.sqrt ((scaleM L W E u)⁻¹)) else 0) +
          Real.sqrt (225 * Λ * jStarMat L W E D u M) ^ 3 *
            (Real.sqrt (tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ)) *
              (Real.sqrt (tailT L W E D u (zdist2 L (a₁ - b) : ℝ)) *
                Real.sqrt (tailT L W E D u (zdist2 L (b - a₂) : ℝ)))) := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  obtain ⟨-, -, -, hfl2⟩ := LemDecCalE_floor h
  have hlong := fG_long h
  have hsqrt := fG_sqrt h
  have havg := avg_le_hyp h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  set ls := ellStar L W u with hls
  set d : ℝ := (zdist2 L (a₁ - a₂) : ℝ) with hddef
  set J := jStarMat L W E D u M with hJdef
  set ℓ := ellT L u with hℓ
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  set eY := Real.exp (Real.log W ^ ((3 : ℝ) / 4)) with heYdef
  set T : ℝ → ℝ := fun x => tailT L W E D u x with hT
  have hT0 : ∀ x, 0 ≤ T x := fun x => (tailT_pos one_le_W' L E D u x).le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hMpos : 0 < scaleM L W E u := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  set B1 : ℝ := 50 * Λ * J * eY * T d with hB1
  have hB10 : 0 ≤ B1 := by
    have := hT0 d
    have : 0 ≤ eY := by linarith
    positivity
  set X1 : ℝ := B1 * (12 * Λ * K₀ * J * Real.sqrt m) with hX1
  have hX10 : 0 ≤ X1 := by
    have : 0 ≤ 12 * Λ * K₀ * J * Real.sqrt m := by positivity
    positivity
  set k : ℝ := Real.sqrt (225 * Λ * J) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  set sT : Z2 L → ℝ := fun b => Real.sqrt (T (zdist2 L (a₁ - b) : ℝ)) *
    Real.sqrt (T (zdist2 L (b - a₂) : ℝ)) with hsT
  have hsT0 : ∀ b, 0 ≤ sT b := fun b => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the edge `a₂ – a₁` of length `d`
  have hda : ∀ p q : BlockIndex L W, p.1 = a₂ → q.1 = a₁ →
      (zdist2 L (p.1 - q.1) : ℝ) = d := by
    intro p q hp hq
    rw [hp, hq, zdist2_comm]
  have hd1 : ls / 8 + 2 ≤ d := by linarith
  have htri := zdist2_tri a₁ b a₂
  have hc2 : 0 ≤ k ^ 3 * (Real.sqrt (T d) * sT b) :=
    mul_nonneg (pow_nonneg hk0 3) (mul_nonneg (Real.sqrt_nonneg _) (hsT0 b))
  have hi1 : 0 ≤ (if (zdist2 L (a₁ - b) : ℝ) ≤ ls / 2 then X1 else 0) := by
    split_ifs <;> first | exact hX10 | exact le_rfl
  have hi2 : 0 ≤ (if (zdist2 L (a₂ - b) : ℝ) ≤ ls / 2 then X1 else 0) := by
    split_ifs <;> first | exact hX10 | exact le_rfl
  by_cases hA : (zdist2 L (a₁ - b) : ℝ) ≤ ls / 2
  · -- `b` near `a₁`: the edge `a₁ – b` is averaged
    have ht : tri E u M a₁ b a₂ ≤ B1 * avg E u M a₁ b := by
      refine tri_le_avg12 fun p q r hp hq hr => ?_
      have e1 := hlong p q (d := d) (hda p q hp hq) hd1 (by linarith)
      have hx : (zdist2 L (r.1 - p.1) : ℝ) = (zdist2 L (b - a₂) : ℝ) := by rw [hr, hp]
      have e2 := hlong r p (d := d) hx (by linarith) (by linarith)
      exact mul_le_of_sq_le e1 e2
    have ha := mul_le_mul_of_nonneg_left (havg a₁ b) hB10
    simp only [hA, ↓reduceIte]
    linarith
  · by_cases hB : (zdist2 L (a₂ - b) : ℝ) ≤ ls / 2
    · -- `b` near `a₂`: the edge `b – a₂` is averaged
      have hB' : (zdist2 L (b - a₂) : ℝ) ≤ ls / 2 := by rw [zdist2_comm]; exact hB
      have ht : tri E u M a₁ b a₂ ≤ B1 * avg E u M a₂ b := by
        refine tri_le_avg23 fun p q r hp hq hr => ?_
        have e1 := hlong p q (d := d) (hda p q hp hq) hd1 (by linarith)
        have hx : (zdist2 L (q.1 - r.1) : ℝ) = (zdist2 L (a₁ - b) : ℝ) := by rw [hq, hr]
        have e2 := hlong q r (d := d) hx (by linarith) (by linarith)
        exact mul_le_of_sq_le e1 e2
      have ha := mul_le_mul_of_nonneg_left (havg a₂ b) hB10
      simp only [hA, hB, ↓reduceIte, zero_add]
      linarith
    · -- `b` far from both: three long edges and `convSqrtTailT`
      have hA' : ls / 2 < (zdist2 L (a₁ - b) : ℝ) := not_le.1 hA
      have hB' : ls / 2 < (zdist2 L (b - a₂) : ℝ) := by rw [zdist2_comm]; exact not_le.1 hB
      have ht : tri E u M a₁ b a₂ ≤ k ^ 3 * (Real.sqrt (T d) * sT b) := by
        refine tri_le_of_pt fun p q r hp hq hr => ?_
        have e1 := hsqrt p q (hda p q hp hq) hd1
        have hx2 : (zdist2 L (q.1 - r.1) : ℝ) = (zdist2 L (a₁ - b) : ℝ) := by rw [hq, hr]
        have e2 := hsqrt q r hx2 (by linarith)
        have hx3 : (zdist2 L (r.1 - p.1) : ℝ) = (zdist2 L (b - a₂) : ℝ) := by rw [hr, hp]
        have e3 := hsqrt r p hx3 (by linarith)
        have n1 := fG_nonneg E u M p q
        have n2 := fG_nonneg E u M q r
        have n3 := fG_nonneg E u M r p
        have s1 := Real.sqrt_nonneg (T d)
        have s2 := Real.sqrt_nonneg (T (zdist2 L (a₁ - b) : ℝ))
        have s3 := Real.sqrt_nonneg (T (zdist2 L (b - a₂) : ℝ))
        calc fG E u M p q * fG E u M q r * fG E u M r p
            ≤ (k * Real.sqrt (T d)) * (k * Real.sqrt (T (zdist2 L (a₁ - b) : ℝ))) *
                (k * Real.sqrt (T (zdist2 L (b - a₂) : ℝ))) :=
              mul_le_mul (mul_le_mul e1 e2 n2 (mul_nonneg hk0 s1)) e3 n3
                (mul_nonneg (mul_nonneg hk0 s1) (mul_nonneg hk0 s2))
          _ = k ^ 3 * (Real.sqrt (T d) * sT b) := by rw [hsT]; ring
      simp only [hA, hB, ↓reduceIte, zero_add]
      exact ht

/-- **Far sum**: for `|a₁ - a₂|_L > ℓ*_u`,
`Σ_b tri(a₁,b,a₂) ≤ 2·10⁹ (1 + log W)³ K₀ e^{(log W)^{3/4}} Λ² J² ℓ_u² √(M_u⁻¹) 𝒯_u(d)`. -/
private theorem far_sum (h : E2Hyp L W E s u v D Λ K₀ M) (a₁ a₂ : Z2 L)
    (hd : ellStar L W u < (zdist2 L (a₁ - a₂) : ℝ)) :
    ∑ b : Z2 L, tri E u M a₁ b a₂ ≤
      2 * 10 ^ 9 * (1 + Real.log W) ^ 3 * K₀ * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) *
        Λ ^ 2 * jStarMat L W E D u M ^ 2 * ellT L u ^ 2 * Real.sqrt ((scaleM L W E u)⁻¹) *
          tailT L W E D u (zdist2 L (a₁ - a₂) : ℝ) := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  obtain ⟨-, -, -, hfl2⟩ := LemDecCalE_floor h
  have hptE := fun b => far_pt h a₁ a₂ b hd
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  set ls := ellStar L W u with hls
  set d : ℝ := (zdist2 L (a₁ - a₂) : ℝ) with hddef
  set J := jStarMat L W E D u M with hJdef
  set ℓ := ellT L u with hℓ
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  set eY := Real.exp (Real.log W ^ ((3 : ℝ) / 4)) with heYdef
  set T : ℝ → ℝ := fun x => tailT L W E D u x with hT
  have hT0 : ∀ x, 0 ≤ T x := fun x => (tailT_pos one_le_W' L E D u x).le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hMpos : 0 < scaleM L W E u := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  set B1 : ℝ := 50 * Λ * J * eY * T d with hB1
  have hB10 : 0 ≤ B1 := by
    have := hT0 d
    have : 0 ≤ eY := by linarith
    positivity
  set X1 : ℝ := B1 * (12 * Λ * K₀ * J * Real.sqrt m) with hX1
  have hX10 : 0 ≤ X1 := by
    have : 0 ≤ 12 * Λ * K₀ * J * Real.sqrt m := by positivity
    positivity
  set k : ℝ := Real.sqrt (225 * Λ * J) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  set sT : Z2 L → ℝ := fun b => Real.sqrt (T (zdist2 L (a₁ - b) : ℝ)) *
    Real.sqrt (T (zdist2 L (b - a₂) : ℝ)) with hsT
  have hsT0 : ∀ b, 0 ≤ sT b := fun b => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpt : ∀ b : Z2 L, tri E u M a₁ b a₂ ≤
      (if (zdist2 L (a₁ - b) : ℝ) ≤ ls / 2 then X1 else 0) +
        (if (zdist2 L (a₂ - b) : ℝ) ≤ ls / 2 then X1 else 0) +
          k ^ 3 * (Real.sqrt (T d) * sT b) := hptE
  -- summation
  have hconv := convSqrtTailT L W E D u hE hu0 hu1 hfl2 a₁ a₂
  have hsum : ∑ b : Z2 L, tri E u M a₁ b a₂ ≤
      ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₁ - b) : ℝ) ≤ ls / 2).card : ℝ) * X1 +
        ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₂ - b) : ℝ) ≤ ls / 2).card : ℝ) * X1 +
          k ^ 3 * (Real.sqrt (T d) * ∑ b : Z2 L, sT b) := by
    refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    exact le_rfl
  have hc1 := LemDecCalE_e10a a₁ (ls / 2) (by linarith)
  have hc2 := LemDecCalE_e10a a₂ (ls / 2) (by linarith)
  have hconv' : ∑ b : Z2 L, sT b ≤ 30000 * ℓ ^ 2 * m * Real.sqrt (T d) := hconv
  -- constants
  have hls2 : (2 * (ls / 2) + 1) ^ 2 ≤ 2 * (Real.log W ^ 3 * ℓ ^ 2) := by
    have e0 : (Real.log (W : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = Real.log W ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have e1 : ls ^ 2 = Real.log W ^ 3 * ℓ ^ 2 := by
      rw [hls]
      unfold ellStar
      rw [mul_pow, e0]
    rw [← e1]
    have : 2 * (ls / 2) + 1 = ls + 1 := by ring
    rw [this]
    nlinarith
  have hk3 : k ^ 3 ≤ (225 * Λ * J) ^ 2 := by
    have hc0 : 0 ≤ 225 * Λ * J := by positivity
    have hk2 : k ^ 2 = 225 * Λ * J := Real.sq_sqrt hc0
    have hk1 : 1 ≤ k := by
      rw [hk, Real.le_sqrt zero_le_one hc0]
      have := mul_le_mul hΛ hJ1 zero_le_one hΛ0
      linarith
    have : k ≤ k ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hk0 hk1
    calc k ^ 3 = k * k ^ 2 := by ring
      _ ≤ k ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = (225 * Λ * J) ^ 2 := by rw [hk2]; ring
  have hsTd : Real.sqrt (T d) * Real.sqrt (T d) = T d := Real.mul_self_sqrt (hT0 d)
  have hsm : m ≤ Real.sqrt m := by
    rw [Real.le_sqrt hm0 hm0, sq]
    exact mul_le_of_le_one_left hm0 (inv_le_one_of_one_le₀ hM1)
  set Q : ℝ := K₀ * eY * Λ ^ 2 * J ^ 2 * ℓ ^ 2 * Real.sqrt m * T d with hQ
  have hQ0 : 0 ≤ Q := by
    have := hT0 d
    have : 0 ≤ eY := by linarith
    positivity
  have hpart1 : ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₁ - b) : ℝ) ≤ ls / 2).card : ℝ) *
        X1 + ((Finset.univ.filter fun b : Z2 L => (zdist2 L (a₂ - b) : ℝ) ≤ ls / 2).card : ℝ) *
        X1 ≤ 2400 * Real.log W ^ 3 * Q := by
    have e1 := mul_le_mul_of_nonneg_right (hc1.trans hls2) hX10
    have e2 := mul_le_mul_of_nonneg_right (hc2.trans hls2) hX10
    have e3 : 2 * (Real.log W ^ 3 * ℓ ^ 2) * X1 = 1200 * Real.log W ^ 3 * Q := by
      rw [hX1, hB1, hQ]; ring
    calc _ ≤ 2 * (Real.log W ^ 3 * ℓ ^ 2) * X1 + 2 * (Real.log W ^ 3 * ℓ ^ 2) * X1 :=
          add_le_add e1 e2
      _ = 2400 * Real.log W ^ 3 * Q := by rw [e3]; ring
  have hpart2 : k ^ 3 * (Real.sqrt (T d) * ∑ b : Z2 L, sT b) ≤ 1518750000 * Q := by
    have e1 : Real.sqrt (T d) * ∑ b : Z2 L, sT b ≤
        Real.sqrt (T d) * (30000 * ℓ ^ 2 * m * Real.sqrt (T d)) :=
      mul_le_mul_of_nonneg_left hconv' (Real.sqrt_nonneg _)
    have e2 : Real.sqrt (T d) * (30000 * ℓ ^ 2 * m * Real.sqrt (T d)) =
        30000 * ℓ ^ 2 * m * T d := by
      calc Real.sqrt (T d) * (30000 * ℓ ^ 2 * m * Real.sqrt (T d))
          = 30000 * ℓ ^ 2 * m * (Real.sqrt (T d) * Real.sqrt (T d)) := by ring
        _ = 30000 * ℓ ^ 2 * m * T d := by rw [hsTd]
    have e3 : 0 ≤ Real.sqrt (T d) * ∑ b : Z2 L, sT b :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun b _ => hsT0 b)
    have e4 := mul_le_mul hk3 e1 e3 (by positivity)
    rw [e2] at e4
    have e5 : (225 * Λ * J) ^ 2 * (30000 * ℓ ^ 2 * m * T d) =
        1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * m := by ring
    have e6 : 1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * m ≤
        1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * Real.sqrt m :=
      mul_le_mul_of_nonneg_left hsm (by have := hT0 d; positivity)
    have hKY : 1 ≤ K₀ * eY := one_le_mul_of_one_le_of_one_le hK heY
    have e7 : 1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * Real.sqrt m ≤ 1518750000 * Q := by
      have eQ : Q = (K₀ * eY) * (1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * Real.sqrt m) /
          1518750000 := by rw [hQ]; ring
      have : 0 ≤ 1518750000 * (Λ ^ 2 * J ^ 2 * ℓ ^ 2 * T d) * Real.sqrt m := by
        have := hT0 d; positivity
      have e8 := le_mul_of_one_le_left this hKY
      rw [eQ]
      linarith
    linarith
  have hlg3 : Real.log W ^ 3 ≤ (1 + Real.log W) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hlg1 : 1 ≤ (1 + Real.log W) ^ 3 := one_le_pow₀ (by linarith)
  have e1 : 2400 * Q * Real.log W ^ 3 ≤ 2400 * Q * (1 + Real.log W) ^ 3 :=
    mul_le_mul_of_nonneg_left hlg3 (mul_nonneg (by norm_num) hQ0)
  have e2 : 1518750000 * Q * 1 ≤ 1518750000 * Q * (1 + Real.log W) ^ 3 :=
    mul_le_mul_of_nonneg_left hlg1 (mul_nonneg (by norm_num) hQ0)
  have e3 : 0 ≤ Q * (1 + Real.log W) ^ 3 := mul_nonneg hQ0 (by linarith)
  calc ∑ b : Z2 L, tri E u M a₁ b a₂ ≤ _ := hsum
    _ ≤ 2400 * Real.log W ^ 3 * Q + 1518750000 * Q := add_le_add hpart1 hpart2
    _ ≤ 2 * 10 ^ 9 * (1 + Real.log W) ^ 3 * Q := by linarith
    _ = _ := by rw [hQ]; ring

end Far

/-! ## 7. The loss, the normalisation, and `lemDecCalE_wG` -/

section Main

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- Both constants are below `lossE2 = 10¹² K₀² Λ⁶ (1+log(L²W¹²))⁴ (1+log W)³ e^{8(log W)^{3/4}}`:
near `1162 Λ⁴ (log(L²W¹²))⁴ e^{(log W)^{3/4}}`, far `4·10⁹ (1+log W)³ K₀ e^{(log W)^{3/4}} Λ³`. -/
private theorem loss_ge (h : E2Hyp L W E s u v D Λ K₀ M) :
    1162 * Λ ^ 4 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 4 *
        Real.exp (Real.log W ^ ((3 : ℝ) / 4)) ≤ lossE2 L W Λ K₀ ∧
      4 * 10 ^ 9 * (1 + Real.log W) ^ 3 * K₀ * Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * Λ ^ 3 ≤
        lossE2 L W Λ K₀ := by
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hW0 : (0 : ℝ) < W := by linarith
  set Lg : ℝ := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) with hLg
  set lg : ℝ := Real.log W with hlgdef
  set Y : ℝ := lg ^ ((3 : ℝ) / 4) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hLg0 : 0 ≤ Lg := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast one_le_L')
    have h2 : (1 : ℝ) ≤ (W : ℝ) ^ 12 := one_le_pow₀ hW1.le
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hc1 : 1 ≤ Real.exp Y := Real.one_le_exp hY0
  have hcC : Real.exp Y ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have hA1 : 1 ≤ (1 + Lg) ^ 4 := one_le_pow₀ (by linarith)
  have hB1 : 1 ≤ (1 + lg) ^ 3 := one_le_pow₀ (by linarith)
  have hK2 : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK
  have hK2' : K₀ ≤ K₀ ^ 2 := le_self_pow₀ hK (by norm_num)
  have hb46 : Λ ^ 4 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hb34 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hLgA : Lg ^ 4 ≤ (1 + Lg) ^ 4 := pow_le_pow_left₀ hLg0 (by linarith) 4
  have hloss : lossE2 L W Λ K₀ =
      10 ^ 12 * (K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y)) := by
    unfold lossE2; ring
  have hΛ6 : 0 ≤ Λ ^ 6 := by positivity
  have hP1 : 1 ≤ K₀ ^ 2 * (1 + lg) ^ 3 := one_le_mul_of_one_le_of_one_le hK2 hB1
  have hQ0 : 0 ≤ Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y) := by positivity
  constructor
  · have e1 : Λ ^ 4 * Lg ^ 4 * Real.exp Y ≤ Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y) :=
      mul_le_mul (mul_le_mul hb46 hLgA (by positivity) hΛ6) hcC (by positivity)
        (by positivity)
    have e2 : Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y) ≤
        (K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y)) :=
      le_mul_of_one_le_left hQ0 hP1
    rw [hloss]
    calc 1162 * Λ ^ 4 * Lg ^ 4 * Real.exp Y = 1162 * (Λ ^ 4 * Lg ^ 4 * Real.exp Y) := by ring
      _ ≤ 1162 * ((K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y))) := by
          linarith
      _ ≤ 10 ^ 12 * ((K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y))) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by positivity) hQ0)
      _ = 10 ^ 12 * (K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y)) := by
          ring
  · have hB0 : 0 ≤ (1 + lg) ^ 3 := by positivity
    have e1 : K₀ * (1 + lg) ^ 3 ≤ K₀ ^ 2 * (1 + lg) ^ 3 := mul_le_mul_of_nonneg_right hK2' hB0
    have e2 : Real.exp Y * Λ ^ 3 ≤ Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y) := by
      have : Λ ^ 3 ≤ Λ ^ 6 * (1 + Lg) ^ 4 := hb34.trans (le_mul_of_one_le_right hΛ6 hA1)
      calc Real.exp Y * Λ ^ 3 ≤ Real.exp (8 * Y) * (Λ ^ 6 * (1 + Lg) ^ 4) :=
            mul_le_mul hcC this (by positivity) (by positivity)
        _ = Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y) := by ring
    have e3 := mul_le_mul e1 e2 (by positivity) (by positivity)
    rw [hloss]
    calc 4 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * Real.exp Y * Λ ^ 3 =
        4 * 10 ^ 9 * ((K₀ * (1 + lg) ^ 3) * (Real.exp Y * Λ ^ 3)) := by ring
      _ ≤ 4 * 10 ^ 9 * ((K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y))) := by
          linarith
      _ ≤ 10 ^ 12 * ((K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y))) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by positivity) hQ0)
      _ = 10 ^ 12 * (K₀ ^ 2 * (1 + lg) ^ 3) * (Λ ^ 6 * (1 + Lg) ^ 4 * Real.exp (8 * Y)) := by
          ring

/-- The near normalisation: for `|a₁-a₂|_L ≤ ℓ*_u`, `M_u⁻² ≤ e^{(log W)^{3/4}} 𝒯_u(|a₁-a₂|_L)`
(`tellStar` with `C = 1`; `𝒯_u(d - ℓ*_u) ≥ M_u⁻²` as `√` of a non-positive number is `0`). -/
private theorem near_norm {E D u : ℝ} (hu : u < 1) {d : ℝ} (hd : d ≤ ellStar L W u) :
    ((scaleM L W E u)⁻¹) ^ 2 ≤
      Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D u d := by
  have h2 := tellStar L W E D u 1 d hu zero_le_one
  simp only [Real.sqrt_one, one_mul] at h2
  refine le_trans ?_ h2
  have hℓ := (ellT_pos_le (L := L) one_le_L' hu).1
  have hneg : (d - ellStar L W u) / ellT L u ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le
  unfold tailT
  rw [Real.sqrt_eq_zero_of_nonpos hneg, neg_zero, Real.exp_zero, mul_one, inv_pow]
  have : (0 : ℝ) ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  linarith

/-- **`lemDecCalE_wG`** (`res_deccalE_wG`).
Proof: the prefactor (e9) `|𝓔^{(G̃)}| ≤ W² Λρ²M_u⁻¹ Σ_b (|𝓛¹_b| + |𝓛²_b|)` (`EGt_le_pref`);
near `|a₁-a₂|_L ≤ ℓ*_u`: `near_sum` and `near_norm` give
`≤ 1162 Λ⁴ (log(L²W¹²))⁴ e^{(log W)^{3/4}} · η_u⁻¹ ρ⁶ 𝒯_v`; far: `loops_le_tri` and `far_sum` give
`≤ 4·10⁹ (1+log W)³ K₀ e^{(log W)^{3/4}} Λ³ · η_u⁻¹ ρ² M_u^{-1/2} J² 𝒯_v`; both constants are at
most `lossE2` (`loss_ge`), and `W² ℓ_u² M_u⁻¹ = η_u⁻¹` ((e1)), `𝒯_u ≤ 𝒯_v` ((e3)). -/
theorem lemDecCalE_wG : LemDecCalE_wG := by
  intro L W _ _ E s u v D Λ K₀ M h a₁ a₂
  obtain ⟨hW1, hM1, hMW, hℓ1, hρ, hJ1, hJW, hlg, hstar, hWD⟩ := facts h
  have hpref := EGt_le_pref h a₁ a₂
  have hnear := near_sum h a₁ a₂
  have hfar := far_sum h a₁ a₂
  obtain ⟨hlossN, hlossF⟩ := loss_ge h
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, hfloor, hMv, hgood, hJ, hK14, hK15⟩ := h
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hMpos : 0 < scaleM L W E u := by linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  set d : ℝ := (zdist2 L (a₁ - a₂) : ℝ) with hddef
  have hmono : tailT L W E D u d ≤ tailT L W E D v d :=
    LemDecCalE_tailT_mono_scale one_le_L' one_le_W' hE hu0 huv hv1 (Nat.cast_nonneg _)
  have hTu0 : 0 ≤ tailT L W E D u d := (tailT_pos one_le_W' L E D u d).le
  have hTv0 : 0 ≤ tailT L W E D v d := (tailT_pos one_le_W' L E D v d).le
  have he1 : (W : ℝ) ^ 2 * ellT L u ^ 2 * (scaleM L W E u)⁻¹ = (etaT E u)⁻¹ := by
    rw [LemDecCalE_e1 (L := L) (W := W) hE hu1]
    field_simp
  have hsqrt : (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) = Real.sqrt ((scaleM L W E u)⁻¹) :=
    (Real.sqrt_eq_rpow _).symm
  rw [hsqrt]
  set Φ := lossE2 L W Λ K₀ with hΦ
  set η := etaT E u with hηdef
  set ℓ := ellT L u with hℓ
  set ρ := ellT L u / ellT L s with hρdef
  set J := jStarMat L W E D u M with hJdef
  set m : ℝ := (scaleM L W E u)⁻¹ with hm
  set lg : ℝ := Real.log W with hlgdef
  set Lg : ℝ := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) with hLg
  set eY : ℝ := Real.exp (lg ^ ((3 : ℝ) / 4)) with heY
  set S : ℝ := ∑ b : Z2 L, (‖loop3 L W E u M ![true, true, false] ![b, a₁, a₂]‖ +
        ‖loop3 L W E u M ![true, false, false] ![a₁, b, a₂]‖) with hS
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hηi : 0 ≤ η⁻¹ := (inv_pos.2 hη).le
  have hρ0 : 0 ≤ ρ := by linarith
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have heY1 : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  have hpre0 : 0 ≤ (W : ℝ) ^ 2 * (Λ * ρ ^ 2 * m) := by positivity
  by_cases hd : d ≤ ellStar L W u
  · -- near
    have hnorm := near_norm (L := L) (W := W) (E := E) (D := D) hu1 hd
    simp only [hd, ↓reduceIte]
    have e1 : ‖EGt L W E u M a₁ a₂‖ ≤ (W : ℝ) ^ 2 * (Λ * ρ ^ 2 * m) *
        (1162 * Λ ^ 3 * Lg ^ 4 * ℓ ^ 2 * ρ ^ 4 * m ^ 2) :=
      hpref.trans (mul_le_mul_of_nonneg_left hnear hpre0)
    have e2 : (W : ℝ) ^ 2 * (Λ * ρ ^ 2 * m) * (1162 * Λ ^ 3 * Lg ^ 4 * ℓ ^ 2 * ρ ^ 4 * m ^ 2) =
        (1162 * Λ ^ 4 * Lg ^ 4) * (η⁻¹ * ρ ^ 6) * m ^ 2 := by
      rw [← he1]; ring
    have hC0 : 0 ≤ (1162 * Λ ^ 4 * Lg ^ 4) * (η⁻¹ * ρ ^ 6) := by positivity
    have e3 : (1162 * Λ ^ 4 * Lg ^ 4) * (η⁻¹ * ρ ^ 6) * m ^ 2 ≤
        (1162 * Λ ^ 4 * Lg ^ 4) * (η⁻¹ * ρ ^ 6) * (eY * tailT L W E D v d) :=
      mul_le_mul_of_nonneg_left (hnorm.trans (mul_le_mul_of_nonneg_left hmono (by linarith))) hC0
    have e4 : (1162 * Λ ^ 4 * Lg ^ 4) * (η⁻¹ * ρ ^ 6) * (eY * tailT L W E D v d) =
        (1162 * Λ ^ 4 * Lg ^ 4 * eY) * (η⁻¹ * ρ ^ 6 * tailT L W E D v d) := by ring
    have hX0 : 0 ≤ η⁻¹ * ρ ^ 6 * tailT L W E D v d := by positivity
    have e5 := mul_le_mul_of_nonneg_right hlossN hX0
    have e6 : Φ * (η⁻¹ * ρ ^ 6 * tailT L W E D v d) ≤
        Φ * (η⁻¹ * (ρ ^ 6 * 1 + ρ ^ 2 * Real.sqrt m * J ^ 2)) * tailT L W E D v d := by
      have hΦ0 : 0 ≤ Φ := le_trans (by positivity) hlossN
      have : η⁻¹ * ρ ^ 6 ≤ η⁻¹ * (ρ ^ 6 * 1 + ρ ^ 2 * Real.sqrt m * J ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hηi
        have : 0 ≤ ρ ^ 2 * Real.sqrt m * J ^ 2 := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right this hTv0
      have := mul_le_mul_of_nonneg_left this hΦ0
      linarith
    linarith
  · -- far
    have hd' : ellStar L W u < d := not_le.1 hd
    simp only [hd, ↓reduceIte]
    have hS2 : S ≤ 2 * ∑ b : Z2 L, tri E u M a₁ b a₂ := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => loops_le_tri hgood.1 a₁ a₂ b
    have hfar' := hfar hd'
    set C : ℝ := 2 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * eY * Λ ^ 2 * J ^ 2 * ℓ ^ 2 * Real.sqrt m *
      tailT L W E D u d with hC
    have e1 : ‖EGt L W E u M a₁ a₂‖ ≤ (W : ℝ) ^ 2 * (Λ * ρ ^ 2 * m) * (2 * C) :=
      hpref.trans (mul_le_mul_of_nonneg_left (by linarith) hpre0)
    have e2 : (W : ℝ) ^ 2 * (Λ * ρ ^ 2 * m) * (2 * C) =
        (4 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * eY * Λ ^ 3) *
          (η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2)) * tailT L W E D u d := by
      rw [hC, ← he1]; ring
    have hC0 : 0 ≤ (4 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * eY * Λ ^ 3) *
        (η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2)) := by
      have : 0 ≤ eY := by linarith
      have : 0 ≤ 1 + lg := by linarith
      positivity
    have e3 := mul_le_mul_of_nonneg_left hmono hC0
    have hX0 : 0 ≤ η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2) * tailT L W E D v d := by positivity
    have e4 := mul_le_mul_of_nonneg_right hlossF hX0
    have e5 : Φ * (η⁻¹ * (ρ ^ 6 * 0 + ρ ^ 2 * Real.sqrt m * J ^ 2)) * tailT L W E D v d =
        Φ * (η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2) * tailT L W E D v d) := by ring
    rw [e5]
    have e6 : (4 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * eY * Λ ^ 3) *
        (η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2)) * tailT L W E D v d =
        (4 * 10 ^ 9 * (1 + lg) ^ 3 * K₀ * eY * Λ ^ 3) *
          (η⁻¹ * (ρ ^ 2 * Real.sqrt m * J ^ 2) * tailT L W E D v d) := by ring
    linarith

end Main

end RBM.Path
