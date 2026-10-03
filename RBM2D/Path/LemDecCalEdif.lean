/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.LemDecCalE
import RBM2D.Path.Step2Vocab

/-!
# `lem_dec_calE`, third part: the `𝓔 ⊗ 𝓔` bound under (57)

The statement `LemDecCalE_dif` refers to `EE` (`RBM2D/Path/Step2Vocab.lean`), `lossE2`, `E2Hyp`
(`RBM2D/Path/LemDecCalE.lean`) and the good set `goodSet`.

Result: `lemDecCalE_dif : LemDecCalE_dif` (`res_deccalE_dif`).

Proof outline (all deterministic, under `E2Hyp` and (57) at the endpoint `v`):
* the two cuts of `EE` are alternating six-loops `tr(A E₁ B E₂ A E₃ B E₄ A E₅ B E₆)` with
  `A = G_u(σ)`, `B = G_u(-σ) = Aᴴ` (`loopAB`);
* near (`|a₁ - a₂|_L ≤ 4ℓ*_v`): split `b` at `ℓ** = 4 (log(L²W¹²))² ℓ_u`; inside, (`lRB1`)
  at `k = 6` from `goodSet`; outside, the edge `b → a₁` is long and (e7) makes it
  `≤ 200ΛJ(L²W¹²)⁻¹`;
* far: (`L6G6X`) with the glue `X = B E_b A` at `b` if `|a₁ - b|_L ≤ |b - a₂|_L`, and at `b'` (the
  rotated loop) otherwise; Cauchy–Schwarz with the four-loop (`lRB1` at `k = 4`) when `b` is within
  `ℓ*_u + 1` of a label, pointwise (e7) bounds otherwise; the sum over `b` by `convTailT` at `v`;
* every (e7) edge is compared with `𝒯_v` through `e² e^{2Y}`, `Y = (log W)^{3/4}`
  (`LemDecCalE_tailT_shift`, `tellStar`), and the constants are absorbed by `lossE2`.

Paper: arXiv:2503.07606, `res_deccalE_dif` and its proof, (`defEOTE`), (`alkkj3`), (`L6G6X`),
(`GGTLJ4G`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Path

open Matrix RBM RBM.Gauss

/-! ## 0. The statement -/

/-- **The `𝓔 ⊗ 𝓔` bound (`res_deccalE_dif`, proof exponents)** under (57) at the endpoint `v`:
near `η_u^{-1}(ℓ_u/ℓ_s)^{10} 1(|a₁-a₂| ≤ 4ℓ*_v)`, far
`η_u^{-1}(ℓ_u/ℓ_s)³ M_u^{-1/2}(J*)² + η_v^{-1} M_v^{-1}(J*)³` (paper: `η_t^{-1}M_u^{-1/2}(J*)³`). -/
def LemDecCalE_dif : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E s u v D Λ K₀ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ),
    E2Hyp L W E s u v D Λ K₀ M → ∀ a a' : Z2 L × Z2 L,
      (zdist2 L (a.1 - a'.1) : ℝ) ≤ ellStar L W v → (zdist2 L (a.2 - a'.2) : ℝ) ≤ ellStar L W v →
      ‖EE L W E u M a a'‖ ≤ lossE2 L W Λ K₀ *
        ((etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 *
            (if (zdist2 L (a.1 - a.2) : ℝ) ≤ 4 * ellStar L W v then 1 else 0) +
          (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
            jStarMat L W E D u M ^ 2 +
          (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ * jStarMat L W E D u M ^ 3) *
        tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) ^ 2


section Generic

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The weight of `E_c` at `p`: `W⁻²` on the block `c`, `0` elsewhere. -/
private def wt (c : Z2 L) (p : BlockIndex L W) : ℝ := if p.1 = c then ((W : ℝ) ^ 2)⁻¹ else 0

private theorem wt_nonneg (c : Z2 L) (p : BlockIndex L W) : 0 ≤ wt c p := by
  unfold wt; split_ifs <;> positivity

private theorem Eblk_eq_diag (c : Z2 L) :
    Eblk L W c = diagonal (fun p : BlockIndex L W => ((wt c p : ℝ) : ℂ)) := by
  unfold Eblk
  congr 1
  funext p
  unfold wt
  split_ifs <;> simp

private theorem sum_wt (c : Z2 L) : ∑ p : BlockIndex L W, wt c p = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [wt, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · intro b _ hb
    simp [wt, hb]
  · simp

private theorem path2 (P H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (c : Z2 L)
    (p q : BlockIndex L W) {t β : ℝ} (ht : 0 ≤ t)
    (h : ∀ y : BlockIndex L W, y.1 = c → ‖P p y‖ * ‖H y q‖ * t ≤ β) :
    ‖(P * Eblk L W c * H) p q‖ * t ≤ β := by
  rw [Eblk_eq_diag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  have h1 : ‖∑ y, P p y * ((wt c y : ℝ) : ℂ) * H y q‖ ≤ ∑ y, wt c y * (‖P p y‖ * ‖H y q‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg c y)]
    nlinarith [norm_nonneg (P p y), norm_nonneg (H y q), wt_nonneg c y]
  calc ‖∑ y, P p y * ((wt c y : ℝ) : ℂ) * H y q‖ * t
      ≤ (∑ y, wt c y * (‖P p y‖ * ‖H y q‖)) * t := mul_le_mul_of_nonneg_right h1 ht
    _ = ∑ y, wt c y * (‖P p y‖ * ‖H y q‖ * t) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ y, wt c y * β := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hy : y.1 = c
        · exact mul_le_mul_of_nonneg_left (h y hy) (wt_nonneg c y)
        · simp [wt, hy]
    _ = β := by rw [← Finset.sum_mul, sum_wt, one_mul]

/-- The alternating six-loop `tr(A E₁ B E₂ A E₃ B E₄ A E₅ B E₆)` (the `gloopProd` bracketing). -/
private def loopAB (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Z2 L) : ℂ :=
  trace (A * Eblk L W c1 * (B * Eblk L W c2 * (A * Eblk L W c3 * (B * Eblk L W c4 *
    (A * Eblk L W c5 * (B * Eblk L W c6 * 1))))))

/-- The alternating four-loop `tr(A E₁ B E₆ A E₅ B E₆)`. -/
private def loop4AB (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (c1 c6 c5 : Z2 L) : ℂ :=
  trace (A * Eblk L W c1 * (B * Eblk L W c6 * (A * Eblk L W c5 * (B * Eblk L W c6 * 1))))

/-- Cyclic rotation of the six-loop by three steps. -/
private theorem loopAB_rot (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Z2 L) :
    loopAB A B c1 c2 c3 c4 c5 c6 = loopAB B A c4 c5 c6 c1 c2 c3 := by
  unfold loopAB
  simp only [Matrix.mul_one]
  rw [show A * Eblk L W c1 * (B * Eblk L W c2 * (A * Eblk L W c3 * (B * Eblk L W c4 *
      (A * Eblk L W c5 * (B * Eblk L W c6))))) =
      (A * Eblk L W c1 * B * Eblk L W c2 * A * Eblk L W c3) *
        (B * Eblk L W c4 * A * Eblk L W c5 * B * Eblk L W c6) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The middle factor `B E₂ A E₃ B E₄ A` (edges `c₁ → c₂ → c₃ → c₄ → c₅`). -/
private def midAB (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (c2 c3 c4 : Z2 L) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  B * Eblk L W c2 * A * Eblk L W c3 * B * Eblk L W c4 * A

/-- The glue `X = B E₆ A` (edges `c₅ → c₆ → c₁`). -/
private def glueAB (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (c6 : Z2 L) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  B * Eblk L W c6 * A

private theorem loopAB_eq_sum (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Z2 L) :
    loopAB A B c1 c2 c3 c4 c5 c6 = ∑ p, ∑ q, ((wt c1 p : ℝ) : ℂ) * midAB A B c2 c3 c4 p q *
      ((wt c5 q : ℝ) : ℂ) * glueAB A B c6 q p := by
  have h : loopAB A B c1 c2 c3 c4 c5 c6 =
      trace ((Eblk L W c1 * midAB A B c2 c3 c4 * Eblk L W c5) * glueAB A B c6) := by
    unfold loopAB midAB glueAB
    simp only [Matrix.mul_one]
    rw [show A * Eblk L W c1 * (B * Eblk L W c2 * (A * Eblk L W c3 * (B * Eblk L W c4 *
        (A * Eblk L W c5 * (B * Eblk L W c6))))) =
        A * (Eblk L W c1 * B * Eblk L W c2 * A * Eblk L W c3 * B * Eblk L W c4 * A *
          Eblk L W c5 * B * Eblk L W c6) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Eblk_eq_diag, Eblk_eq_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem loop4AB_eq_sum (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c6 c5 : Z2 L) :
    loop4AB A B c1 c6 c5 = ∑ p, ∑ q, ((wt c1 p : ℝ) : ℂ) * glueAB A B c6 p q *
      ((wt c5 q : ℝ) : ℂ) * glueAB A B c6 q p := by
  have h : loop4AB A B c1 c6 c5 =
      trace ((Eblk L W c1 * glueAB A B c6 * Eblk L W c5) * glueAB A B c6) := by
    unfold loop4AB glueAB
    simp only [Matrix.mul_one]
    rw [show A * Eblk L W c1 * (B * Eblk L W c6 * (A * Eblk L W c5 * (B * Eblk L W c6))) =
        A * (Eblk L W c1 * B * Eblk L W c6 * A * Eblk L W c5 * B * Eblk L W c6) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Eblk_eq_diag, Eblk_eq_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Path bound for the middle factor. -/
private theorem midAB_le (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 : Z2 L) {α : ℝ}
    (h : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖B x1 x2‖ * ‖A x2 x3‖ * ‖B x3 x4‖ * ‖A x4 x5‖ ≤ α)
    (p q : BlockIndex L W) (hp : p.1 = c1) (hq : q.1 = c5) :
    ‖midAB A B c2 c3 c4 p q‖ ≤ α := by
  have h3 : ∀ y3 y4 : BlockIndex L W, y3.1 = c3 → y4.1 = c4 →
      ‖(B * Eblk L W c2 * A) p y3‖ * (‖B y3 y4‖ * ‖A y4 q‖) ≤ α := fun y3 y4 hy3 hy4 =>
    path2 B A c2 p y3 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun y2 hy2 => by
      have := h p y2 y3 y4 q hp hy2 hy3 hy4 hq
      calc ‖B p y2‖ * ‖A y2 y3‖ * (‖B y3 y4‖ * ‖A y4 q‖)
          = ‖B p y2‖ * ‖A y2 y3‖ * ‖B y3 y4‖ * ‖A y4 q‖ := by ring
        _ ≤ α := this)
  have h4 : ∀ y4 : BlockIndex L W, y4.1 = c4 →
      ‖(B * Eblk L W c2 * A * Eblk L W c3 * B) p y4‖ * ‖A y4 q‖ ≤ α := fun y4 hy4 =>
    path2 (B * Eblk L W c2 * A) B c3 p y4 (norm_nonneg _) (fun y3 hy3 => by
      have := h3 y3 y4 hy3 hy4
      calc ‖(B * Eblk L W c2 * A) p y3‖ * ‖B y3 y4‖ * ‖A y4 q‖
          = ‖(B * Eblk L W c2 * A) p y3‖ * (‖B y3 y4‖ * ‖A y4 q‖) := by ring
        _ ≤ α := this)
  have := path2 (B * Eblk L W c2 * A * Eblk L W c3 * B) A c4 p q (t := 1) zero_le_one
    (fun y4 hy4 => by rw [mul_one]; exact h4 y4 hy4)
  simpa [midAB] using this

/-- Pointwise bound for the glue. -/
private theorem glueAB_le (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c5 c6 c1 : Z2 L) {β : ℝ}
    (h : ∀ x5 x6 x1 : BlockIndex L W, x5.1 = c5 → x6.1 = c6 → x1.1 = c1 →
      ‖B x5 x6‖ * ‖A x6 x1‖ ≤ β)
    (q p : BlockIndex L W) (hq : q.1 = c5) (hp : p.1 = c1) :
    ‖glueAB A B c6 q p‖ ≤ β := by
  have := path2 B A c6 q p (t := 1) zero_le_one (fun y hy => by
    rw [mul_one]; exact h q y p hq hy hp)
  simpa [glueAB] using this

/-- The first reduction: `‖loop‖ ≤ α Σ_{p,q} w₁(p) w₅(q) ‖X_{qp}‖`. -/
private theorem loopAB_le_glue (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Z2 L) {α : ℝ}
    (h : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖B x1 x2‖ * ‖A x2 x3‖ * ‖B x3 x4‖ * ‖A x4 x5‖ ≤ α) :
    ‖loopAB A B c1 c2 c3 c4 c5 c6‖ ≤
      α * ∑ p, ∑ q, wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖ := by
  rw [loopAB_eq_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (wt_nonneg c1 p), Real.norm_of_nonneg (wt_nonneg c5 q)]
  have hw1 := wt_nonneg (W := W) c1 p
  have hw5 := wt_nonneg (W := W) c5 q
  have hX := norm_nonneg (glueAB A B c6 q p)
  by_cases hp : p.1 = c1
  · by_cases hq : q.1 = c5
    · have hm := midAB_le A B c1 c2 c3 c4 c5 h p q hp hq
      have : wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖ * ‖midAB A B c2 c3 c4 p q‖ ≤
          wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖ * α :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      nlinarith
    · simp [wt, hq]
  · simp [wt, hp]

/-- Weighted Cauchy–Schwarz: `(Σ w f)² ≤ Σ w f²` for weights `w ≥ 0` of total mass `1`. -/
private theorem wcs {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * f i ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)
  have e1 : ∀ i, Real.sqrt (w i) * (Real.sqrt (w i) * f i) = w i * f i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  have e3 : ∀ i, (Real.sqrt (w i) * f i) ^ 2 = w i * f i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [e1, e2, e3, h1, one_mul] at this
  exact this

/-- Total mass of the product weight. -/
private theorem sum_wt_wt (c1 c5 : Z2 L) :
    ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, wt c1 p * wt c5 q = 1 := by
  simp only [← Finset.mul_sum, sum_wt, mul_one]

/-- The glue of a Hermitian pair is Hermitian. -/
private theorem glueAB_herm (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (hAB : Aᴴ = B)
    (c6 : Z2 L) (p q : BlockIndex L W) :
    glueAB A B c6 p q = star (glueAB A B c6 q p) := by
  have hBA : Bᴴ = A := by rw [← hAB, Matrix.conjTranspose_conjTranspose]
  have hE : (Eblk L W c6)ᴴ = Eblk L W c6 := by
    rw [Eblk_eq_diag, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    simp
  have hX : (glueAB A B c6)ᴴ = glueAB A B c6 := by
    unfold glueAB
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hE, hAB, hBA, Matrix.mul_assoc]
  have := congrFun (congrFun hX p) q
  rw [Matrix.conjTranspose_apply] at this
  exact this.symm

/-- The four-loop is the weighted `ℓ²` mass of the glue. -/
private theorem loop4AB_eq (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (hAB : Aᴴ = B)
    (c1 c6 c5 : Z2 L) :
    loop4AB A B c1 c6 c5 =
      ((∑ p, ∑ q, wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖ ^ 2 : ℝ) : ℂ) := by
  rw [loop4AB_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [glueAB_herm A B hAB c6 p q]
  have : star (glueAB A B c6 q p) * glueAB A B c6 q p = ((‖glueAB A B c6 q p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  calc ((wt c1 p : ℝ) : ℂ) * star (glueAB A B c6 q p) * ((wt c5 q : ℝ) : ℂ) * glueAB A B c6 q p
      = ((wt c1 p : ℝ) : ℂ) * ((wt c5 q : ℝ) : ℂ) *
          (star (glueAB A B c6 q p) * glueAB A B c6 q p) := by ring
    _ = _ := by rw [this]; push_cast; ring

/-- **Glue at `c₆` with Cauchy–Schwarz** (`L6G6X`): for `Aᴴ = B`,
`‖loop‖ ≤ α √‖tr(A E₁ B E₆ A E₅ B E₆)‖`. -/
private theorem loopAB_le_cs (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (hAB : Aᴴ = B)
    (c1 c2 c3 c4 c5 c6 : Z2 L) {α : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖B x1 x2‖ * ‖A x2 x3‖ * ‖B x3 x4‖ * ‖A x4 x5‖ ≤ α) :
    ‖loopAB A B c1 c2 c3 c4 c5 c6‖ ≤ α * Real.sqrt ‖loop4AB A B c1 c6 c5‖ := by
  refine (loopAB_le_glue A B c1 c2 c3 c4 c5 c6 h).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hα0
  set S2 : ℝ := ∑ p, ∑ q, wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖ ^ 2 with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (wt_nonneg c1 p) (wt_nonneg c5 q)) (sq_nonneg _)
  have h4 : ‖loop4AB A B c1 c6 c5‖ = S2 := by
    rw [loop4AB_eq A B hAB, Complex.norm_real, Real.norm_of_nonneg hS20]
  rw [h4]
  have hcs := wcs (ι := BlockIndex L W × BlockIndex L W) (fun x => wt c1 x.1 * wt c5 x.2)
    (fun x => ‖glueAB A B c6 x.2 x.1‖)
    (fun x => mul_nonneg (wt_nonneg c1 x.1) (wt_nonneg c5 x.2))
    (by rw [Fintype.sum_prod_type]; exact sum_wt_wt c1 c5)
  rw [Fintype.sum_prod_type (fun x : BlockIndex L W × BlockIndex L W =>
      wt c1 x.1 * wt c5 x.2 * ‖glueAB A B c6 x.2 x.1‖),
    Fintype.sum_prod_type (fun x : BlockIndex L W × BlockIndex L W =>
      wt c1 x.1 * wt c5 x.2 * ‖glueAB A B c6 x.2 x.1‖ ^ 2)] at hcs
  apply Real.le_sqrt_of_sq_le
  rw [hS2]
  exact hcs

/-- **Pointwise glue**: `‖loop‖ ≤ α β`. -/
private theorem loopAB_le_pt (A B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Z2 L) {α β : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖B x1 x2‖ * ‖A x2 x3‖ * ‖B x3 x4‖ * ‖A x4 x5‖ ≤ α)
    (hβ : ∀ x5 x6 x1 : BlockIndex L W, x5.1 = c5 → x6.1 = c6 → x1.1 = c1 →
      ‖B x5 x6‖ * ‖A x6 x1‖ ≤ β) :
    ‖loopAB A B c1 c2 c3 c4 c5 c6‖ ≤ α * β := by
  refine (loopAB_le_glue A B c1 c2 c3 c4 c5 c6 h).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hα0
  calc ∑ p, ∑ q, wt c1 p * wt c5 q * ‖glueAB A B c6 q p‖
      ≤ ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, wt c1 p * wt c5 q * β := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        by_cases hp : p.1 = c1
        · by_cases hq : q.1 = c5
          · exact mul_le_mul_of_nonneg_left (glueAB_le A B c5 c6 c1 hβ q p hq hp)
              (mul_nonneg (wt_nonneg c1 p) (wt_nonneg c5 q))
          · simp [wt, hq]
        · simp [wt, hp]
    _ = β := by simp only [← Finset.sum_mul, sum_wt_wt, one_mul]

end Generic

/-! ## 2. Distances, tails, edges -/

section Facts

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem dif_oneL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)

private theorem dif_oneW : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (NeZero.ne W)

private theorem dif_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem zd_comm (a b : Z2 L) : zdist2 L (a - b) = zdist2 L (b - a) := by
  rw [← neg_sub b a]
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, dif_zdist_neg]

private theorem zd_tri (a b c : Z2 L) :
    (zdist2 L (a - c) : ℝ) ≤ (zdist2 L (a - b) : ℝ) + (zdist2 L (b - c) : ℝ) := by
  have := zdist2_add_le L (a - b) (b - c)
  rw [sub_add_sub_cancel] at this
  exact_mod_cast this

private theorem tail_at_nonpos {L W : ℕ} {E D u x : ℝ} (hL : 1 ≤ L) (hu : u < 1) (hx : x ≤ 0) :
    tailT L W E D u x = tailT L W E D u 0 := by
  have hℓ := (ellT_pos_le (L := L) hL hu).1
  unfold tailT
  rw [Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg hx hℓ.le), zero_div, Real.sqrt_zero]

private theorem hyp_basic (h : E2Hyp L W E s u v D Λ K₀ M) :
    3 ≤ L ∧ |E| < 2 ∧ 0 ≤ u ∧ 0 ≤ v ∧ u < 1 ∧ v < 1 ∧ u ≤ v ∧ 1 ≤ Λ ∧ 4 ≤ Real.log W := by
  obtain ⟨hL3, hE, hs0, hsu, huv, hv1, hΛ, hK, hlog, -⟩ := h
  exact ⟨hL3, hE, hs0.trans hsu, (hs0.trans hsu).trans huv, huv.trans_lt hv1, hv1, huv, hΛ, hlog⟩

/-- `𝒯_u ≤ 𝒯_v` at every real argument. -/
private theorem tail_uv (h : E2Hyp L W E s u v D Λ K₀ M) (x : ℝ) :
    tailT L W E D u x ≤ tailT L W E D v x := by
  obtain ⟨-, hE, hu0, -, hu1, hv1, huv, -⟩ := hyp_basic h
  rcases le_total x 0 with hx | hx
  · rw [tail_at_nonpos dif_oneL hu1 hx, tail_at_nonpos dif_oneL hv1 hx]
    exact LemDecCalE_tailT_mono_scale dif_oneL dif_oneW hE hu0 huv hv1 le_rfl
  · exact LemDecCalE_tailT_mono_scale dif_oneL dif_oneW hE hu0 huv hv1 hx

private theorem ellStar_ge (h : E2Hyp L W E s u v D Λ K₀ M) : 4 ≤ ellStar L W u := by
  obtain ⟨-, -, hu0, -, hu1, -, -, -, hlog⟩ := hyp_basic h
  have hℓ := one_le_ellT (L := L) dif_oneL hu0 hu1
  have h1 : Real.log W ^ (1 : ℝ) ≤ Real.log W ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_one] at h1
  unfold ellStar
  nlinarith

private theorem ellStar_le (h : E2Hyp L W E s u v D Λ K₀ M) : ellStar L W u ≤ ellStar L W v := by
  obtain ⟨-, -, hu0, -, hu1, hv1, huv, -, hlog⟩ := hyp_basic h
  have hℓ := (ellT_mono_ratio (L := L) dif_oneL hu0 huv hv1).1
  unfold ellStar
  exact mul_le_mul_of_nonneg_left hℓ (Real.rpow_nonneg (by linarith) _)

private theorem greenBlk_false_eq (hH : M.IsHermitian) (p q : BlockIndex L W) :
    greenBlk L W E u M false p q = star (greenBlk L W E u M true q p) := by
  have hHb : (blockMat M).IsHermitian := hH.submatrix _
  have hG := Gsig_conjTranspose hHb (spectralZ E u) true
  have := congrFun (congrFun hG p) q
  simpa [Matrix.conjTranspose_apply, greenBlk] using this.symm

private theorem greenBlk_herm (hH : M.IsHermitian) (σ : Bool) :
    (greenBlk L W E u M σ)ᴴ = greenBlk L W E u M (!σ) :=
  Gsig_conjTranspose (hH.submatrix _) (spectralZ E u) σ

/-- The (e7) bound for either sign, with the distance written `|p.1 - q.1|_L`, and the additive
`W^{-D}` folded (`W^{-D} ≤ 𝒯_u`, `J ≥ 1`). -/
private theorem edge_u (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Bool) (p q : BlockIndex L W)
    (hd : ellStar L W u / 8 + 2 ≤ (zdist2 L (p.1 - q.1) : ℝ)) :
    ‖greenBlk L W E u M σ p q‖ ^ 2 ≤
      50 * Λ * jStarMat L W E D u M * tailT L W E D u ((zdist2 L (p.1 - q.1) : ℝ) - 2) := by
  have hJ1 := one_le_jStarMat L W dif_oneW E D u M
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hH : M.IsHermitian := h.2.2.2.2.2.2.2.2.2.2.2.1.1
  set J := jStarMat L W E D u M
  set T := tailT L W E D u ((zdist2 L (p.1 - q.1) : ℝ) - 2)
  have hT : (W : ℝ) ^ (-D) ≤ T := by
    have := (mul_nonneg (inv_nonneg.2 (sq_nonneg (scaleM L W E u)))
      (Real.exp_pos (-Real.sqrt ((((zdist2 L (p.1 - q.1) : ℕ) : ℝ) - 2) / ellT L u))).le)
    simp only [T, tailT]
    linarith
  have hT0 : 0 ≤ T := le_trans (Real.rpow_nonneg (Nat.cast_nonneg W) _) hT
  have key : ∀ x : ℝ, x ≤ 25 * Λ * ((W : ℝ) ^ (-D) + J * T) → x ≤ 50 * Λ * J * T := by
    intro x hx
    have : (W : ℝ) ^ (-D) ≤ J * T := hT.trans (le_mul_of_one_le_left hT0 hJ1)
    nlinarith
  cases σ
  · rw [greenBlk_false_eq hH, norm_star]
    exact key _ (LemDecCalE_e7 h q p hd)
  · apply key
    have hd' : ellStar L W u / 8 + 2 ≤ (zdist2 L (q.1 - p.1) : ℝ) := by rwa [zd_comm]
    have := LemDecCalE_e7 h p q hd'
    rwa [zd_comm q.1 p.1] at this

/-- The combined shift: `𝒯_v(y) ≤ e² e^{2Y} 𝒯_v(x)` for `y ≥ x - 4 - 4ℓ*_v`. -/
private theorem shiftS (h : E2Hyp L W E s u v D Λ K₀ M) {x y : ℝ}
    (hy : x - 4 - 4 * ellStar L W v ≤ y) :
    tailT L W E D v y ≤ Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
      tailT L W E D v x := by
  obtain ⟨-, -, -, hv0, -, hv1, -⟩ := hyp_basic h
  have h1 : tailT L W E D v y ≤ tailT L W E D v ((x - 4 * ellStar L W v) - 4) :=
    LemDecCalE_tailT_anti dif_oneL hv1 (by linarith)
  have h2 := LemDecCalE_tailT_shift (L := L) (W := W) (E := E) (D := D) dif_oneL hv0 hv1
    (c := 4) (by norm_num) (x - 4 * ellStar L W v)
  have h3 := LemDecCalE_e4c (L := L) (W := W) (E := E) (D := D) hv1 (C := 4) (by norm_num) x
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4] at h2 h3
  have he : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
  calc tailT L W E D v y ≤ Real.exp 2 * tailT L W E D v (x - 4 * ellStar L W v) := h1.trans h2
    _ ≤ Real.exp 2 * (Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D v x) :=
        mul_le_mul_of_nonneg_left h3 he
    _ = _ := by ring

/-- (e7) at the scale `v` with slack `2 + 4ℓ*_v` in the distance. -/
private theorem edge_v (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Bool) (p q : BlockIndex L W)
    (x : ℝ) (hd : ellStar L W u / 8 + 2 ≤ (zdist2 L (p.1 - q.1) : ℝ))
    (hx : x - 2 - 4 * ellStar L W v ≤ (zdist2 L (p.1 - q.1) : ℝ)) :
    ‖greenBlk L W E u M σ p q‖ ^ 2 ≤
      50 * Λ * jStarMat L W E D u M * (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) *
        tailT L W E D v x := by
  have hJ1 := one_le_jStarMat L W dif_oneW E D u M
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have h1 := edge_u h σ p q hd
  have h2 := tail_uv h ((zdist2 L (p.1 - q.1) : ℝ) - 2)
  have h3 := shiftS h (x := x) (y := (zdist2 L (p.1 - q.1) : ℝ) - 2) (by linarith)
  have hc : 0 ≤ 50 * Λ * jStarMat L W E D u M := by positivity
  calc ‖greenBlk L W E u M σ p q‖ ^ 2
      ≤ 50 * Λ * jStarMat L W E D u M * tailT L W E D u ((zdist2 L (p.1 - q.1) : ℝ) - 2) := h1
    _ ≤ 50 * Λ * jStarMat L W E D u M * tailT L W E D v ((zdist2 L (p.1 - q.1) : ℝ) - 2) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ ≤ 50 * Λ * jStarMat L W E D u M * (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) *
        tailT L W E D v x) := mul_le_mul_of_nonneg_left h3 hc
    _ = _ := by ring

/-- AM–GM for two norms with a common squared bound. -/
private theorem pair_le {a b K : ℝ} (ha : a ^ 2 ≤ K) (hb : b ^ 2 ≤ K) :
    a * b ≤ K := by
  nlinarith [sq_nonneg (a - b)]

end Facts

/-! ## 3. The six- and four-loops of `EE` as `loopAB`, `loop4AB` -/

section Loops

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem gloop6_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (c1 c2 c3 c4 c5 c6 : Z2 L) :
    gloop L W (blockMat M) (spectralZ E u) (loopOf ![σ, !σ, σ, !σ, σ, !σ] ![c1, c2, c3, c4, c5, c6]) =
      loopAB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) c1 c2 c3 c4 c5 c6 := by
  simp [gloop, loopOf, loopAB, greenBlk, List.ofFn_succ]

private theorem gloop4_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (c1 c6 c5 : Z2 L) :
    gloop L W (blockMat M) (spectralZ E u) (loopOf ![σ, !σ, σ, !σ] ![c1, c6, c5, c6]) =
      loop4AB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) c1 c6 c5 := by
  simp [gloop, loopOf, loop4AB, greenBlk, List.ofFn_succ]

end Loops

/-! ## 4. The near part: the split radius `ℓ** = 4 (log(L²W¹²))² ℓ_u` -/

section Near

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem goodSet_of_hyp (h : E2Hyp L W E s u v D Λ K₀ M) : M ∈ goodSet L W E s u Λ :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- `log(L² W¹²) ≥ 12 log W`. -/
private theorem logP_ge :
    12 * Real.log W ≤ Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (dif_oneL (L := L))
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have := Real.log_nonneg hL1
  push_cast
  linarith

/-- `W^{-D} ≤ (L² W¹²)⁻²` from the floor condition. -/
private theorem wD_le (h : E2Hyp L W E s u v D Λ K₀ M) :
    (W : ℝ) ^ (-D) ≤ (((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2)⁻¹ := by
  have hfloor := h.2.2.2.2.2.2.2.2.2.1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hP0 : (0 : ℝ) < (L : ℝ) ^ 2 * (W : ℝ) ^ 12 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h2 : ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2 ≤ (W : ℝ) ^ D := by
    have := pow_le_pow_left₀ hP0.le hfloor 2
    rwa [← Real.rpow_natCast ((W : ℝ) ^ (D / 2)) 2, ← Real.rpow_mul hW0.le,
      show D / 2 * ((2 : ℕ) : ℝ) = D by push_cast; ring] at this
  rw [Real.rpow_neg hW0.le]
  exact inv_anti₀ (by positivity) h2

/-- The tail at the split radius: `𝒯_u(ℓ** - 2) ≤ 4 (L²W¹²)⁻²`, and `ℓ** ≥ ℓ*_u/8 + 2`. -/
private theorem tail_Rss (h : E2Hyp L W E s u v D Λ K₀ M) :
    tailT L W E D u (4 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2 * ellT L u - 2) ≤
        4 * (((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2)⁻¹ ∧
      ellStar L W u / 8 + 2 ≤ 4 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2 * ellT L u := by
  obtain ⟨-, hE, hu0, -, hu1, -, -, -, hlog⟩ := hyp_basic h
  have h2 := LemDecCalE_e2 h
  have hlp := logP_ge (L := L) (W := W)
  set P : ℝ := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hPdef
  set Lg : ℝ := Real.log P with hLg
  have hP0 : 0 < P := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hLg1 : 1 ≤ Lg := by linarith
  have hℓ := one_le_ellT (L := L) dif_oneL hu0 hu1
  have hℓ0 : 0 < ellT L u := by linarith
  refine ⟨?_, ?_⟩
  · have hq : (2 * Lg - 1) ^ 2 ≤ (4 * Lg ^ 2 * ellT L u - 2) / ellT L u := by
      rw [le_div_iff₀ hℓ0]
      nlinarith
    have hs : 2 * Lg - 1 ≤ Real.sqrt ((4 * Lg ^ 2 * ellT L u - 2) / ellT L u) :=
      Real.le_sqrt_of_sq_le hq
    have he : Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ellT L u - 2) / ellT L u)) ≤
        Real.exp 1 * (P ^ 2)⁻¹ := by
      have hP2 : P ^ 2 = Real.exp (2 * Lg) := by
        rw [show 2 * Lg = Lg + Lg by ring, Real.exp_add, hLg, Real.exp_log hP0]; ring
      rw [hP2, ← Real.exp_neg, ← Real.exp_add, Real.exp_le_exp]
      linarith
    have hM : (scaleM L W E u ^ 2)⁻¹ ≤ 1 := by
      have : 1 ≤ scaleM L W E u := h2.1.trans h2.2.1
      exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
    have hWD := wD_le h
    have he3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hPi : 0 ≤ (P ^ 2)⁻¹ := by positivity
    unfold tailT
    have hexp0 := (Real.exp_pos (-Real.sqrt ((4 * Lg ^ 2 * ellT L u - 2) / ellT L u))).le
    calc (scaleM L W E u ^ 2)⁻¹ * Real.exp (-Real.sqrt ((4 * Lg ^ 2 * ellT L u - 2) / ellT L u)) +
          (W : ℝ) ^ (-D)
        ≤ 1 * (Real.exp 1 * (P ^ 2)⁻¹) + (P ^ 2)⁻¹ := by
          gcongr
      _ ≤ 4 * (P ^ 2)⁻¹ := by nlinarith
  · have h32 : Real.log W ^ ((3 : ℝ) / 2) ≤ Real.log W ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Real.log W) (by linarith)
        (show (3 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) by norm_num)
      rwa [Real.rpow_natCast] at this
    have hLg2 : Real.log W ^ 2 ≤ Lg ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    unfold ellStar
    have : Real.log W ^ ((3 : ℝ) / 2) * ellT L u ≤ Lg ^ 2 * ellT L u :=
      mul_le_mul_of_nonneg_right (h32.trans hLg2) hℓ0.le
    nlinarith

/-- **Near cut bound.** For the cut pattern `(A₁, A₂, B', A₂', A₁', B)`: if `|A₁ - B|_L ≤ ℓ**`, the
six-loop is `≤ Λ ρ^{10} M_u⁻⁵` (`lRB1`, `k = 6`); otherwise the edge `B → A₁` is long and
`‖loop‖ ≤ (2Λ)⁵ · 200 Λ J (L²W¹²)⁻¹`. -/
private theorem cut_near (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Bool) (A1 A2 A1' A2' B B' : Z2 L) :
    ‖loopAB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) A1 A2 B' A2' A1' B‖ ≤
      Λ * (ellT L u / ellT L s) ^ 10 * (scaleM L W E u)⁻¹ ^ 5 *
          (if (zdist2 L (A1 - B) : ℝ) ≤
              4 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 2 * ellT L u then 1 else 0) +
        32 * Λ ^ 5 * (200 * Λ * jStarMat L W E D u M * ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹) := by
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hJ1 := one_le_jStarMat L W dif_oneW E D u M
  have hu1 := (hyp_basic h).2.2.2.2.1
  obtain ⟨hT, hR⟩ := tail_Rss h
  set P : ℝ := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hPdef
  have hP0 : 0 < P := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  clear_value P
  set J := jStarMat L W E D u M with hJdef
  have hsecond : 0 ≤ 32 * Λ ^ 5 * (200 * Λ * J * P⁻¹) := by positivity
  have hρ0 : 0 ≤ ellT L u / ellT L s := by
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    positivity
  split_ifs with hn
  · have hk := (goodSet_of_hyp h).2.1 6 (by simp) ![σ, !σ, σ, !σ, σ, !σ] ![A1, A2, B', A2', A1', B]
    unfold loopAbs at hk
    rw [gloop6_eq] at hk
    norm_num at hk
    rw [← inv_pow] at hk
    linarith
  · have hlong : ∀ x6 x1 : BlockIndex L W, x6.1 = B → x1.1 = A1 →
        ‖greenBlk L W E u M σ x6 x1‖ ≤ 200 * Λ * J * P⁻¹ := by
      intro x6 x1 h6 h1
      have hd : (4 * Real.log P ^ 2 * ellT L u) < (zdist2 L (x6.1 - x1.1) : ℝ) := by
        rw [h6, h1, zd_comm]; exact lt_of_not_ge hn
      have he := edge_u (D := D) h σ x6 x1 (by linarith)
      have ht := LemDecCalE_tailT_anti (L := L) (W := W) (E := E) (D := D) dif_oneL hu1
        (x := 4 * Real.log P ^ 2 * ellT L u - 2)
        (y := (zdist2 L (x6.1 - x1.1) : ℝ) - 2) (by linarith)
      have hc : 0 ≤ 50 * Λ * J := by positivity
      have hsq : ‖greenBlk L W E u M σ x6 x1‖ ^ 2 ≤ (200 * Λ * J * P⁻¹) ^ 2 := by
        calc ‖greenBlk L W E u M σ x6 x1‖ ^ 2
            ≤ 50 * Λ * J * (4 * (P ^ 2)⁻¹) :=
              he.trans (mul_le_mul_of_nonneg_left (ht.trans hT) hc)
          _ ≤ (200 * Λ * J * P⁻¹) ^ 2 := by
              have h1' : 1 ≤ 200 * Λ * J := by nlinarith
              have hPi : 0 ≤ (P ^ 2)⁻¹ := by positivity
              have e : (200 * Λ * J * P⁻¹) ^ 2 = (200 * Λ * J) ^ 2 * (P ^ 2)⁻¹ := by
                rw [mul_pow, inv_pow]
              rw [e]
              nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have hle : ∀ (τ : Bool) (x y : BlockIndex L W), ‖greenBlk L W E u M τ x y‖ ≤ 2 * Λ :=
      fun τ x y => LemDecCalE_e6_of_hyp h τ x y
    have hα : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = A1 → x2.1 = A2 → x3.1 = B' →
        x4.1 = A2' → x5.1 = A1' →
        ‖greenBlk L W E u M (!σ) x1 x2‖ * ‖greenBlk L W E u M σ x2 x3‖ *
          ‖greenBlk L W E u M (!σ) x3 x4‖ * ‖greenBlk L W E u M σ x4 x5‖ ≤ (2 * Λ) ^ 4 := by
      intro x1 x2 x3 x4 x5 _ _ _ _ _
      have h1 := hle (!σ) x1 x2
      have h2 := hle σ x2 x3
      have h3 := hle (!σ) x3 x4
      have h4 := hle σ x4 x5
      calc ‖greenBlk L W E u M (!σ) x1 x2‖ * ‖greenBlk L W E u M σ x2 x3‖ *
            ‖greenBlk L W E u M (!σ) x3 x4‖ * ‖greenBlk L W E u M σ x4 x5‖
          ≤ (2 * Λ) * (2 * Λ) * (2 * Λ) * (2 * Λ) := by gcongr
        _ = (2 * Λ) ^ 4 := by ring
    have hβ : ∀ x5 x6 x1 : BlockIndex L W, x5.1 = A1' → x6.1 = B → x1.1 = A1 →
        ‖greenBlk L W E u M (!σ) x5 x6‖ * ‖greenBlk L W E u M σ x6 x1‖ ≤
          2 * Λ * (200 * Λ * J * P⁻¹) := by
      intro x5 x6 x1 _ h6 h1
      exact mul_le_mul (hle _ _ _) (hlong x6 x1 h6 h1) (norm_nonneg _) (by positivity)
    have := loopAB_le_pt _ _ A1 A2 B' A2' A1' B (by positivity) hα hβ
    calc _ ≤ (2 * Λ) ^ 4 * (2 * Λ * (200 * Λ * J * P⁻¹)) := this
      _ = 32 * Λ ^ 5 * (200 * Λ * J * P⁻¹) := by ring
      _ ≤ _ := by linarith

end Near

/-! ## 5. The far part: (`L6G6X`) with the glue at `b` or at `b'` -/

section Far

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- The four-loop of (`L6G6X`): `√‖𝓛_{(τ,-τ,τ,-τ)}‖ ≤ Λ ρ³ M_u⁻¹ M_u^{-1/2}` (`lRB1`, `k = 4`). -/
private theorem sqrt_loop4_le (h : E2Hyp L W E s u v D Λ K₀ M) (τ : Bool) (c1 c6 c5 : Z2 L) :
    Real.sqrt ‖loop4AB (greenBlk L W E u M τ) (greenBlk L W E u M (!τ)) c1 c6 c5‖ ≤
      Λ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ *
        (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) := by
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hu1 := (hyp_basic h).2.2.2.2.1
  have hk := (goodSet_of_hyp h).2.1 4 (by simp) ![τ, !τ, τ, !τ] ![c1, c6, c5, c6]
  unfold loopAbs at hk
  rw [gloop4_eq] at hk
  norm_num at hk
  rw [← inv_pow] at hk
  have hρ0 : 0 ≤ ellT L u / ellT L s := by
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    positivity
  set ρ := ellT L u / ellT L s
  set m := (scaleM L W E u)⁻¹
  have hm0 : 0 ≤ m := by
    have h2 := LemDecCalE_e2 h
    exact inv_nonneg.2 (by linarith [h2.1, h2.2.1])
  have hsq : (m ^ ((1 : ℝ) / 2)) ^ 2 = m := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hm0]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ‖loop4AB (greenBlk L W E u M τ) (greenBlk L W E u M (!τ)) c1 c6 c5‖
      ≤ Λ * ρ ^ 6 * m ^ 3 := hk
    _ ≤ Λ ^ 2 * ρ ^ 6 * m ^ 3 := by
        have : Λ ≤ Λ ^ 2 := by nlinarith
        have h0 : 0 ≤ ρ ^ 6 * m ^ 3 := by positivity
        nlinarith
    _ = (Λ * ρ ^ 3 * m * m ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [mul_pow, hsq]; ring

private theorem quad_le {a b c e P1 P2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (h25 : a * e ≤ P1) (h34 : b * c ≤ P2) : a * b * c * e ≤ P1 * P2 := by
  have h1 : a * b * c * e = (a * e) * (b * c) := by ring
  rw [h1]
  exact mul_le_mul h25 h34 (by positivity) ((mul_nonneg ha he).trans h25)

/-- **Far cut bound** (`L6G6X`, `GGTLJ4G`), for the cut pattern
`(A₁, A₂, B', A₂', A₁', B)` with signs `(σ, -σ, …)`, under (57) at `v` and `|A₁ - A₂|_L > 4ℓ*_v`.
Case (1) `|A₁ - B| ≤ |B - A₂|`: glue at `B`; case (2): glue at `B'` (the rotated loop). In (1a)/(2a)
(`B` within `ℓ*_u + 1` of a label) Cauchy–Schwarz with the four-loop; otherwise pointwise. -/
private theorem cut_far (h : E2Hyp L W E s u v D Λ K₀ M) (σ : Bool) (A1 A2 A1' A2' B B' : Z2 L)
    (h1 : (zdist2 L (A1 - A1') : ℝ) ≤ ellStar L W v)
    (h2 : (zdist2 L (A2 - A2') : ℝ) ≤ ellStar L W v)
    (hB : (zdist2 L (B - B') : ℝ) ≤ 1)
    (hd : 4 * ellStar L W v < (zdist2 L (A1 - A2) : ℝ)) :
    ‖loopAB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) A1 A2 B' A2' A1' B‖ ≤
      (50 * Λ * jStarMat L W E D u M) ^ 2 *
          (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 *
          tailT L W E D v (zdist2 L (A1 - A2) : ℝ) ^ 2 *
          (Λ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ *
            (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2)) *
          ((if (zdist2 L (A1 - B) : ℝ) ≤ ellStar L W u + 1 then 1 else 0) +
            (if (zdist2 L (A1' - B) : ℝ) ≤ ellStar L W u + 1 then 1 else 0) +
            (if (zdist2 L (A2 - B) : ℝ) ≤ ellStar L W u + 1 then 1 else 0) +
            (if (zdist2 L (A2' - B) : ℝ) ≤ ellStar L W u + 1 then 1 else 0)) +
        (50 * Λ * jStarMat L W E D u M) ^ 3 *
          (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 *
          tailT L W E D v (zdist2 L (A1 - A2) : ℝ) * tailT L W E D v (zdist2 L (A1 - B) : ℝ) *
          tailT L W E D v (zdist2 L (B - A2) : ℝ) := by
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hJ1 := one_le_jStarMat L W dif_oneW E D u M
  have hls := ellStar_ge h
  have hlv := ellStar_le h
  have hH : M.IsHermitian := (goodSet_of_hyp h).1
  -- abbreviations
  set lam := ellStar L W v with hlam
  set ls := ellStar L W u with hls_def
  set S := Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) with hS
  set κ := 50 * Λ * jStarMat L W E D u M with hκ
  set R4 := Λ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ *
    (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) with hR4
  have hS1 : 1 ≤ S := by
    have a := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 2 * Real.log W ^ ((3 : ℝ) / 4) by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log W by linarith [(hyp_basic h).2.2.2.2.2.2.2.2])
        ((3 : ℝ) / 4)
      linarith)
    nlinarith
  have hκ0 : 0 ≤ κ := by positivity
  have hR40 : 0 ≤ R4 := by
    have hu1 := (hyp_basic h).2.2.2.2.1
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    have h2 := LemDecCalE_e2 h
    have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 (by linarith [h2.1, h2.2.1])
    positivity
  have hT0 : ∀ x : ℝ, 0 ≤ tailT L W E D v x := fun x => (tailT_pos dif_oneW L E D v x).le
  -- the edge bound
  have edge : ∀ (τ : Bool) (p q : BlockIndex L W) (x : ℝ),
      ls / 8 + 2 ≤ (zdist2 L (p.1 - q.1) : ℝ) → x - 2 - 4 * lam ≤ (zdist2 L (p.1 - q.1) : ℝ) →
      ‖greenBlk L W E u M τ p q‖ ^ 2 ≤ κ * S * tailT L W E D v x :=
    fun τ p q x ha hb => edge_v h τ p q x ha hb
  have shift : ∀ x y : ℝ, x - 4 - 4 * lam ≤ y → tailT L W E D v y ≤ S * tailT L W E D v x :=
    fun x y hxy => shiftS h hxy
  -- distances
  set d := (zdist2 L (A1 - A2) : ℝ) with hd_def
  set bA1 := (zdist2 L (A1 - B) : ℝ) with hbA1
  set bA2 := (zdist2 L (B - A2) : ℝ) with hbA2
  have c1 : (zdist2 L (B - A1) : ℝ) = bA1 := by rw [hbA1, zd_comm]
  have c2 : (zdist2 L (A2 - B) : ℝ) = bA2 := by rw [hbA2, zd_comm]
  have c3 : (zdist2 L (A1' - A2') : ℝ) = (zdist2 L (A2' - A1') : ℝ) := by rw [zd_comm]
  have c4 : (zdist2 L (A2' - A2) : ℝ) = (zdist2 L (A2 - A2') : ℝ) := by rw [zd_comm]
  have c5 : (zdist2 L (B' - A2) : ℝ) = (zdist2 L (A2 - B') : ℝ) := by rw [zd_comm]
  have c6 : (zdist2 L (B' - B) : ℝ) = (zdist2 L (B - B') : ℝ) := by rw [zd_comm]
  have c7 : (zdist2 L (A2' - B') : ℝ) = (zdist2 L (B' - A2') : ℝ) := by rw [zd_comm]
  have c8 : (zdist2 L (B - A2') : ℝ) = (zdist2 L (A2' - B) : ℝ) := by rw [zd_comm]
  have t1 := zd_tri A1 A1' A2
  have t2 := zd_tri A1' A2' A2
  have t3 := zd_tri B B' A2
  have t4 := zd_tri B' A2' A2
  have t5 := zd_tri A1 A1' B
  have t6 := zd_tri A1 B A2
  have t7 := zd_tri A2 A2' B
  have t8 := zd_tri A2 B' B
  have t9 := zd_tri A2' B' B
  have t10 := zd_tri B B' A2'
  have hd5 : d - 2 * lam ≤ (zdist2 L (A2' - A1') : ℝ) := by linarith
  -- the pair of long edges `A₁ → A₂`, `A₂' → A₁'` (both signs)
  have pair25 : ∀ (τ : Bool) (x1 x2 x4 x5 : BlockIndex L W), x1.1 = A1 → x2.1 = A2 →
      x4.1 = A2' → x5.1 = A1' →
      ‖greenBlk L W E u M τ x1 x2‖ * ‖greenBlk L W E u M (!τ) x4 x5‖ ≤
        κ * S * tailT L W E D v d := by
    intro τ x1 x2 x4 x5 e1 e2 e4 e5
    refine pair_le (edge τ x1 x2 d (by rw [e1, e2]; linarith) (by rw [e1, e2]; linarith))
      (edge (!τ) x4 x5 d (by rw [e4, e5]; linarith) (by rw [e4, e5]; linarith))
  by_cases hcase : bA1 ≤ bA2
  · -- case (1): glue at `B`
    have hb2 : d / 2 ≤ bA2 := by linarith
    have pair34 : ∀ x2 x3 x4 : BlockIndex L W, x2.1 = A2 → x3.1 = B' → x4.1 = A2' →
        ‖greenBlk L W E u M σ x2 x3‖ * ‖greenBlk L W E u M (!σ) x3 x4‖ ≤
          κ * S * tailT L W E D v bA2 := by
      intro x2 x3 x4 e2 e3 e4
      refine pair_le (edge σ x2 x3 bA2 (by rw [e2, e3]; linarith) (by rw [e2, e3]; linarith))
        (edge (!σ) x3 x4 bA2 (by rw [e3, e4]; linarith) (by rw [e3, e4]; linarith))
    have hα : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = A1 → x2.1 = A2 → x3.1 = B' →
        x4.1 = A2' → x5.1 = A1' →
        ‖greenBlk L W E u M (!σ) x1 x2‖ * ‖greenBlk L W E u M σ x2 x3‖ *
          ‖greenBlk L W E u M (!σ) x3 x4‖ * ‖greenBlk L W E u M σ x4 x5‖ ≤
          (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA2) := by
      intro x1 x2 x3 x4 x5 e1 e2 e3 e4 e5
      have p25 := pair25 (!σ) x1 x2 x4 x5 e1 e2 e4 e5
      rw [Bool.not_not] at p25
      exact quad_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) p25
        (pair34 x2 x3 x4 e2 e3 e4)
    have hα0 : 0 ≤ (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA2) := by
      have := hT0 d; have := hT0 bA2; positivity
    by_cases hA : bA1 ≤ ls + 1 ∨ (zdist2 L (A1' - B) : ℝ) ≤ ls + 1
    · -- (1a)
      have hbA2' : d - 4 - 4 * lam ≤ bA2 := by rcases hA with hA | hA <;> linarith
      have hsh := shift d bA2 hbA2'
      have hcs := loopAB_le_cs _ _ (greenBlk_herm hH σ) A1 A2 B' A2' A1' B hα0 hα
      have h4 := sqrt_loop4_le h σ A1 B A1'
      have hind : 1 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
          (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
        rcases hA with hA | hA
        · simp only [hA, ite_true]; split_ifs <;> norm_num
        · simp only [hA, ite_true]; split_ifs <;> norm_num
      have hsec : 0 ≤ κ ^ 3 * S ^ 3 * tailT L W E D v d * tailT L W E D v bA1 *
          tailT L W E D v bA2 := by
        have := hT0 d; have := hT0 bA1; have := hT0 bA2; positivity
      have hTd := hT0 d
      calc ‖loopAB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) A1 A2 B' A2' A1' B‖
          ≤ (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA2) *
              Real.sqrt ‖loop4AB (greenBlk L W E u M σ) (greenBlk L W E u M (!σ)) A1 B A1'‖ := hcs
        _ ≤ (κ * S * tailT L W E D v d) * (κ * S * (S * tailT L W E D v d)) * R4 := by
            apply mul_le_mul _ h4 (Real.sqrt_nonneg _) (by positivity)
            gcongr
        _ = κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 * 1 := by ring
        _ ≤ κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 *
            ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
              (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hind (by positivity)
        _ ≤ _ := by
            have : κ ^ 3 * S ^ 3 * tailT L W E D v d * tailT L W E D v bA1 * tailT L W E D v bA2 =
                κ ^ 3 * S ^ 3 * tailT L W E D v d * tailT L W E D v bA1 *
                  tailT L W E D v bA2 := rfl
            linarith
    · -- (1b)
      push Not at hA
      obtain ⟨hA1, hA1'⟩ := hA
      have hβ : ∀ x5 x6 x1 : BlockIndex L W, x5.1 = A1' → x6.1 = B → x1.1 = A1 →
          ‖greenBlk L W E u M (!σ) x5 x6‖ * ‖greenBlk L W E u M σ x6 x1‖ ≤
            κ * S * tailT L W E D v bA1 := by
        intro x5 x6 x1 e5 e6 e1
        refine pair_le (edge (!σ) x5 x6 bA1 (by rw [e5, e6]; linarith) (by rw [e5, e6]; linarith))
          (edge σ x6 x1 bA1 (by rw [e6, e1]; linarith) (by rw [e6, e1]; linarith))
      have hpt := loopAB_le_pt _ _ A1 A2 B' A2' A1' B hα0 hα hβ
      have hfirst : 0 ≤ κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 *
          ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0)) := by
        have := hT0 d
        have hi : 0 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
          split_ifs <;> norm_num
        positivity
      have heq : (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA2) *
          (κ * S * tailT L W E D v bA1) = κ ^ 3 * S ^ 3 * tailT L W E D v d *
            tailT L W E D v bA1 * tailT L W E D v bA2 := by ring
      linarith
  · -- case (2): glue at `B'`, on the rotated loop
    push Not at hcase
    have hb1 : d / 2 < bA1 := by linarith
    rw [loopAB_rot]
    have pair34' : ∀ x2 x3 x4 : BlockIndex L W, x2.1 = A1' → x3.1 = B → x4.1 = A1 →
        ‖greenBlk L W E u M (!σ) x2 x3‖ * ‖greenBlk L W E u M σ x3 x4‖ ≤
          κ * S * tailT L W E D v bA1 := by
      intro x2 x3 x4 e2 e3 e4
      refine pair_le (edge (!σ) x2 x3 bA1 (by rw [e2, e3]; linarith) (by rw [e2, e3]; linarith))
        (edge σ x3 x4 bA1 (by rw [e3, e4]; linarith) (by rw [e3, e4]; linarith))
    have hα : ∀ x1 x2 x3 x4 x5 : BlockIndex L W, x1.1 = A2' → x2.1 = A1' → x3.1 = B →
        x4.1 = A1 → x5.1 = A2 →
        ‖greenBlk L W E u M σ x1 x2‖ * ‖greenBlk L W E u M (!σ) x2 x3‖ *
          ‖greenBlk L W E u M σ x3 x4‖ * ‖greenBlk L W E u M (!σ) x4 x5‖ ≤
          (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA1) := by
      intro x1 x2 x3 x4 x5 e1 e2 e3 e4 e5
      have p25 := pair25 (!σ) x4 x5 x1 x2 e4 e5 e1 e2
      rw [Bool.not_not] at p25
      have p25' : ‖greenBlk L W E u M σ x1 x2‖ * ‖greenBlk L W E u M (!σ) x4 x5‖ ≤
          κ * S * tailT L W E D v d := by rw [mul_comm]; exact p25
      exact quad_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) p25'
        (pair34' x2 x3 x4 e2 e3 e4)
    have hα0 : 0 ≤ (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA1) := by
      have := hT0 d; have := hT0 bA1; positivity
    by_cases hA : bA2 ≤ ls + 1 ∨ (zdist2 L (A2' - B) : ℝ) ≤ ls + 1
    · -- (2a)
      have hbA1' : d - 4 - 4 * lam ≤ bA1 := by rcases hA with hA | hA <;> linarith
      have hsh := shift d bA1 hbA1'
      have hherm : (greenBlk L W E u M (!σ))ᴴ = greenBlk L W E u M σ := by
        rw [greenBlk_herm hH, Bool.not_not]
      have hcs := loopAB_le_cs _ _ hherm A2' A1' B A1 A2 B' hα0 hα
      have h4 := sqrt_loop4_le h (!σ) A2' B' A2
      rw [Bool.not_not] at h4
      have hind : 1 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
          (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
        rcases hA with hA | hA
        · have : (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 := by linarith
          simp only [this, ite_true]; split_ifs <;> norm_num
        · simp only [hA, ite_true]; split_ifs <;> norm_num
      have hsec : 0 ≤ κ ^ 3 * S ^ 3 * tailT L W E D v d * tailT L W E D v bA1 *
          tailT L W E D v bA2 := by
        have := hT0 d; have := hT0 bA1; have := hT0 bA2; positivity
      have hTd := hT0 d
      calc ‖loopAB (greenBlk L W E u M (!σ)) (greenBlk L W E u M σ) A2' A1' B A1 A2 B'‖
          ≤ (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA1) *
              Real.sqrt ‖loop4AB (greenBlk L W E u M (!σ)) (greenBlk L W E u M σ) A2' B' A2‖ := hcs
        _ ≤ (κ * S * tailT L W E D v d) * (κ * S * (S * tailT L W E D v d)) * R4 := by
            apply mul_le_mul _ h4 (Real.sqrt_nonneg _) (by positivity)
            gcongr
        _ = κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 * 1 := by ring
        _ ≤ κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 *
            ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
              (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hind (by positivity)
        _ ≤ _ := by linarith
    · -- (2b)
      push Not at hA
      obtain ⟨hA2, hA2'⟩ := hA
      have hβ : ∀ x5 x6 x1 : BlockIndex L W, x5.1 = A2 → x6.1 = B' → x1.1 = A2' →
          ‖greenBlk L W E u M σ x5 x6‖ * ‖greenBlk L W E u M (!σ) x6 x1‖ ≤
            κ * S * tailT L W E D v bA2 := by
        intro x5 x6 x1 e5 e6 e1
        refine pair_le (edge σ x5 x6 bA2 (by rw [e5, e6]; linarith) (by rw [e5, e6]; linarith))
          (edge (!σ) x6 x1 bA2 (by rw [e6, e1]; linarith) (by rw [e6, e1]; linarith))
      have hpt := loopAB_le_pt _ _ A2' A1' B A1 A2 B' hα0 hα hβ
      have hfirst : 0 ≤ κ ^ 2 * S ^ 3 * tailT L W E D v d ^ 2 * R4 *
          ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0)) := by
        have := hT0 d
        have hi : 0 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdist2 L (A1' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2 - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdist2 L (A2' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
          split_ifs <;> norm_num
        positivity
      have heq : (κ * S * tailT L W E D v d) * (κ * S * tailT L W E D v bA1) *
          (κ * S * tailT L W E D v bA2) = κ ^ 3 * S ^ 3 * tailT L W E D v d *
            tailT L W E D v bA1 * tailT L W E D v bA2 := by ring
      linarith

end Far

/-! ## 6. Summation over `b, b'` -/

section Sum

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- `‖EE‖ ≤ W² Σ_{b,b'} |S_{bb'}| (‖𝓛^{(1)}‖ + ‖𝓛^{(2)}‖)`, the two cuts written as `loopAB`. -/
private theorem EE_le (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a a' : Z2 L × Z2 L) :
    ‖EE L W E u M a a'‖ ≤ (W : ℝ) ^ 2 * ∑ b : Z2 L, ∑ b' : Z2 L, ‖SB L b b'‖ *
      (‖loopAB (greenBlk L W E u M true) (greenBlk L W E u M false) a.1 a.2 b' a'.2 a'.1 b‖ +
        ‖loopAB (greenBlk L W E u M false) (greenBlk L W E u M true) a.2 a.1 b' a'.1 a'.2 b‖) := by
  have e1 : ∀ b b' : Z2 L, loop6 L W E u M ![true, false, true, false, true, false]
      ![a.1, a.2, b', a'.2, a'.1, b] =
      loopAB (greenBlk L W E u M true) (greenBlk L W E u M false) a.1 a.2 b' a'.2 a'.1 b :=
    fun b b' => gloop6_eq E u M true a.1 a.2 b' a'.2 a'.1 b
  have e2 : ∀ b b' : Z2 L, loop6 L W E u M ![false, true, false, true, false, true]
      ![a.2, a.1, b', a'.1, a'.2, b] =
      loopAB (greenBlk L W E u M false) (greenBlk L W E u M true) a.2 a.1 b' a'.1 a'.2 b :=
    fun b b' => gloop6_eq E u M false a.2 a.1 b' a'.1 a'.2 b
  unfold EE
  rw [norm_mul]
  have hw : ‖(W : ℂ) ^ 2‖ = (W : ℝ) ^ 2 := by simp
  rw [hw]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
  rw [norm_mul, e1, e2]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

/-- The `S^{(B)}` average: `Σ_{b'} |S_{bb'}| X(b') ≤ F` if `X(b') ≤ F` for `|b - b'|_L ≤ 1`. -/
private theorem sum_SB_le (hL : 3 ≤ L) (b : Z2 L) (X : Z2 L → ℝ) (F : ℝ)
    (hX : ∀ b' : Z2 L, (zdist2 L (b - b') : ℝ) ≤ 1 → X b' ≤ F) :
    ∑ b' : Z2 L, ‖SB L b b'‖ * X b' ≤ F := by
  calc ∑ b' : Z2 L, ‖SB L b b'‖ * X b' ≤ ∑ b' : Z2 L, ‖SB L b b'‖ * F := by
        refine Finset.sum_le_sum fun b' _ => ?_
        by_cases hb : (zdist2 L (b - b') : ℝ) ≤ 1
        · exact mul_le_mul_of_nonneg_left (hX b' hb) (norm_nonneg _)
        · have h1 : 1 < zdist2 L (b - b') := by
            have : (1 : ℝ) < (zdist2 L (b - b') : ℝ) := lt_of_not_ge hb
            exact_mod_cast this
          rw [SB_apply_eq_zero L hL h1]
          simp
    _ = F := by rw [← Finset.sum_mul, KLoop.sum_norm_SB_row L hL b, one_mul]

/-- Ball count with indicators: `Σ_b 1(|c - b|_L ≤ R) ≤ (2R + 1)²`. -/
private theorem count_le (c : Z2 L) (R : ℝ) (hR : 0 ≤ R) :
    ∑ b : Z2 L, (if (zdist2 L (c - b) : ℝ) ≤ R then (1 : ℝ) else 0) ≤ (2 * R + 1) ^ 2 := by
  rw [Finset.sum_boole]
  exact LemDecCalE_e10a c R hR

private theorem card_Z2 : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
  rw [Fintype.card_prod, ZMod.card]
  push_cast
  ring

end Sum

/-! ## 7. Scalar facts for the final comparison -/

section Scalar

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

private theorem Y_nonneg (h : E2Hyp L W E s u v D Λ K₀ M) :
    0 ≤ Real.log W ^ ((3 : ℝ) / 4) :=
  Real.rpow_nonneg (by linarith [(hyp_basic h).2.2.2.2.2.2.2.2]) _

/-- `(e² e^{2Y})³ ≤ 404 e^{6Y}`. -/
private theorem S3_le (Y : ℝ) :
    (Real.exp 2 * Real.exp (2 * Y)) ^ 3 ≤ 404 * Real.exp (6 * Y) := by
  have e1 : (Real.exp 2 * Real.exp (2 * Y)) ^ 3 = Real.exp 1 ^ 6 * Real.exp (6 * Y) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [e1]
  have h1 := Real.exp_one_lt_d9
  have h6 : Real.exp 1 ^ 6 ≤ 404 := by
    calc Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 6
      _ ≤ 404 := by norm_num
  exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le

/-- The `lossE2` lower bound used throughout this file. -/
private theorem loss_ge (h : E2Hyp L W E s u v D Λ K₀ M) :
    10 ^ 12 * Λ ^ 6 * (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 * (1 + Real.log W) ^ 3 *
      Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) ≤ lossE2 L W Λ K₀ := by
  have hK : 1 ≤ K₀ := h.2.2.2.2.2.2.2.1
  have hlog := (hyp_basic h).2.2.2.2.2.2.2.2
  have hlp := logP_ge (L := L) (W := W)
  unfold lossE2
  have hK2 : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK
  have h0 : 0 ≤ 10 ^ 12 * Λ ^ 6 * (1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)) ^ 4 *
      (1 + Real.log W) ^ 3 * Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4)) := by
    have : 0 ≤ 1 + Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) := by linarith
    have : 0 ≤ 1 + Real.log W := by linarith
    have : 0 ≤ Λ := by linarith [(hyp_basic h).2.2.2.2.2.2.2.1]
    positivity
  nlinarith

/-- `η_u⁻¹ ≥ 1` and `ρ = ℓ_u/ℓ_s ≥ 1`. -/
private theorem eta_rho_ge (h : E2Hyp L W E s u v D Λ K₀ M) :
    1 ≤ (etaT E u)⁻¹ ∧ 1 ≤ ellT L u / ellT L s := by
  obtain ⟨-, hE, hu0, -, hu1, -, -, -, -⟩ := hyp_basic h
  have hs0 : 0 ≤ s := h.2.2.1
  have hsu : s ≤ u := h.2.2.2.1
  refine ⟨?_, ?_⟩
  · have hη := etaT_pos hE hu1
    have him : (spectralM E).im ≤ 1 := by
      rw [spectralM_im, div_le_one (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    have him0 := spectralM_im_pos hE
    have hη1 : etaT E u ≤ 1 := by
      unfold etaT
      have : 1 - u ≤ 1 := by linarith
      nlinarith
    exact one_le_inv₀ hη |>.2 hη1
  · have hℓs := (ellT_pos_le (L := L) dif_oneL (hsu.trans_lt hu1)).1
    rw [one_le_div hℓs]
    exact (ellT_mono_ratio (L := L) dif_oneL hs0 hsu hu1).1

/-- Near lower bound for the tail: `M_v⁻⁴ ≤ e^{4Y} 𝒯_v(x)²` for `0 ≤ x ≤ 4ℓ*_v`. -/
private theorem tail_lower (h : E2Hyp L W E s u v D Λ K₀ M) {x : ℝ}
    (hx : x ≤ 4 * ellStar L W v) :
    (scaleM L W E v ^ 4)⁻¹ ≤
      Real.exp (4 * Real.log W ^ ((3 : ℝ) / 4)) * tailT L W E D v x ^ 2 := by
  obtain ⟨-, hE, -, hv0, -, hv1, -, -, hlog⟩ := hyp_basic h
  have h2 := LemDecCalE_e2 h
  have hℓ := one_le_ellT (L := L) dif_oneL hv0 hv1
  have hℓ0 : 0 < ellT L v := by linarith
  set Y := Real.log W ^ ((3 : ℝ) / 4) with hY
  have hY0 : 0 ≤ Y := Y_nonneg h
  have hY2 : Y ^ 2 = Real.log W ^ ((3 : ℝ) / 2) := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hs : Real.sqrt (x / ellT L v) ≤ 2 * Y := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hℓ0]
    have : x ≤ 4 * (Real.log W ^ ((3 : ℝ) / 2) * ellT L v) := hx
    nlinarith
  have hMv : 0 < scaleM L W E v := by linarith [h2.1]
  have hT : (scaleM L W E v ^ 2)⁻¹ * Real.exp (-(2 * Y)) ≤ tailT L W E D v x := by
    unfold tailT
    have : Real.exp (-(2 * Y)) ≤ Real.exp (-Real.sqrt (x / ellT L v)) :=
      Real.exp_le_exp.2 (by linarith)
    have hW : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg W) _
    have := mul_le_mul_of_nonneg_left this (inv_nonneg.2 (sq_nonneg (scaleM L W E v)))
    linarith
  have hT' : (scaleM L W E v ^ 2)⁻¹ ≤ Real.exp (2 * Y) * tailT L W E D v x := by
    have e : (scaleM L W E v ^ 2)⁻¹ =
        Real.exp (2 * Y) * ((scaleM L W E v ^ 2)⁻¹ * Real.exp (-(2 * Y))) := by
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
  have h0 : 0 ≤ (scaleM L W E v ^ 2)⁻¹ := by positivity
  calc (scaleM L W E v ^ 4)⁻¹ = ((scaleM L W E v ^ 2)⁻¹) ^ 2 := by rw [← inv_pow]; ring
    _ ≤ (Real.exp (2 * Y) * tailT L W E D v x) ^ 2 := pow_le_pow_left₀ h0 hT' 2
    _ = Real.exp (4 * Y) * tailT L W E D v x ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- `W² L² J (L²W¹²)⁻¹ ≤ M_v⁻⁴` (`J ≤ W`, `M_v ≤ W²`). -/
private theorem near_far_small (h : E2Hyp L W E s u v D Λ K₀ M) :
    (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * (jStarMat L W E D u M * ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹) ≤
      (scaleM L W E v ^ 4)⁻¹ := by
  have hJ : jStarMat L W E D u M ≤ W := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 := LemDecCalE_e2 h
  have hW1 := (LemDecCalE_floor h).1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hMv : 0 < scaleM L W E v := by linarith [h2.1]
  have hJ0 : 0 ≤ jStarMat L W E D u M := by
    linarith [one_le_jStarMat L W dif_oneW E D u M]
  have hMvW : scaleM L W E v ^ 4 ≤ (W : ℝ) ^ 8 := by
    have := pow_le_pow_left₀ hMv.le (h2.2.1.trans h2.2.2) 4
    calc scaleM L W E v ^ 4 ≤ ((W : ℝ) ^ 2) ^ 4 := this
      _ = (W : ℝ) ^ 8 := by ring
  calc (W : ℝ) ^ 2 * (L : ℝ) ^ 2 * (jStarMat L W E D u M * ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹)
      = jStarMat L W E D u M * ((W : ℝ) ^ 10)⁻¹ := by field_simp
    _ ≤ (W : ℝ) * ((W : ℝ) ^ 10)⁻¹ := mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = ((W : ℝ) ^ 9)⁻¹ := by field_simp
    _ ≤ ((W : ℝ) ^ 8)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hW1.le (by norm_num))
    _ ≤ (scaleM L W E v ^ 4)⁻¹ := inv_anti₀ (by positivity) hMvW

end Scalar

/-! ## 8. The two cases of `lemDecCalE_dif` -/

section Cases

variable {L W : ℕ} [NeZero L] [NeZero W] {E s u v D Λ K₀ : ℝ}
  {M : Matrix (Idx L W) (Idx L W) ℂ}

/-- Near case, the sum over `b, b'`:
`‖EE‖ ≤ W² (Λ ρ^{10} M_u⁻⁵ · 2 · 81 Lg⁴ ℓ_u² + L² · 2 · 32 Λ⁵ · 200 Λ J (L²W¹²)⁻¹)`. -/
private theorem near_sum (h : E2Hyp L W E s u v D Λ K₀ M) (a a' : Z2 L × Z2 L) :
    ‖EE L W E u M a a'‖ ≤ (W : ℝ) ^ 2 *
      (Λ * (ellT L u / ellT L s) ^ 10 * (scaleM L W E u)⁻¹ ^ 5 *
          (2 * (81 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 4 * ellT L u ^ 2)) +
        (L : ℝ) ^ 2 * (2 * (32 * Λ ^ 5 * (200 * Λ * jStarMat L W E D u M *
          ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)⁻¹)))) := by
  obtain ⟨hL3, hE, hu0, hv0, hu1, hv1, huv, hΛ, hlog⟩ := hyp_basic h
  have h2 := LemDecCalE_e2 h
  have hlp := logP_ge (L := L) (W := W)
  obtain ⟨-, hρ1⟩ := eta_rho_ge h
  have hℓ := one_le_ellT (L := L) dif_oneL hu0 hu1
  set Lg := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) with hLg
  set P := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hP
  set Rss := 4 * Lg ^ 2 * ellT L u with hRss
  set J := jStarMat L W E D u M with hJ
  set ρ := ellT L u / ellT L s with hρ
  set m := (scaleM L W E u)⁻¹ with hm
  have hm0 : 0 ≤ m := inv_nonneg.2 (by linarith [h2.1, h2.2.1])
  have hρ0 : 0 ≤ ρ := by linarith
  set Fn : Z2 L → ℝ := fun b => Λ * ρ ^ 10 * m ^ 5 *
      ((if (zdist2 L (a.1 - b) : ℝ) ≤ Rss then 1 else 0) +
        (if (zdist2 L (a.2 - b) : ℝ) ≤ Rss then 1 else 0)) +
      2 * (32 * Λ ^ 5 * (200 * Λ * J * P⁻¹)) with hFn
  have hper : ∀ b b' : Z2 L,
      ‖loopAB (greenBlk L W E u M true) (greenBlk L W E u M false) a.1 a.2 b' a'.2 a'.1 b‖ +
        ‖loopAB (greenBlk L W E u M false) (greenBlk L W E u M true) a.2 a.1 b' a'.1 a'.2 b‖ ≤
        Fn b := by
    intro b b'
    have c1 := cut_near h true a.1 a.2 a'.1 a'.2 b b'
    have c2 := cut_near h false a.2 a.1 a'.2 a'.1 b b'
    simp only [Bool.not_true, Bool.not_false] at c1 c2
    simp only [hFn]
    linarith
  have hsum : ‖EE L W E u M a a'‖ ≤ (W : ℝ) ^ 2 * ∑ b : Z2 L, Fn b := by
    refine (EE_le E u M a a').trans ?_
    gcongr with b
    exact sum_SB_le hL3 b _ (Fn b) (fun b' _ => hper b b')
  have hR0 : 0 ≤ Rss := by positivity
  have hcnt : ∀ c : Z2 L, ∑ b : Z2 L, (if (zdist2 L (c - b) : ℝ) ≤ Rss then (1 : ℝ) else 0) ≤
      81 * Lg ^ 4 * ellT L u ^ 2 := by
    intro c
    refine (count_le c Rss hR0).trans ?_
    have h1 : 1 ≤ Lg ^ 2 * ellT L u := by
      have : 1 ≤ Lg ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    have h2' : 2 * Rss + 1 ≤ 9 * (Lg ^ 2 * ellT L u) := by rw [hRss]; nlinarith
    calc (2 * Rss + 1) ^ 2 ≤ (9 * (Lg ^ 2 * ellT L u)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2' 2
      _ = 81 * Lg ^ 4 * ellT L u ^ 2 := by ring
  have hsplit : ∑ b : Z2 L, Fn b = Λ * ρ ^ 10 * m ^ 5 *
      (∑ b : Z2 L, (if (zdist2 L (a.1 - b) : ℝ) ≤ Rss then (1 : ℝ) else 0) +
        ∑ b : Z2 L, (if (zdist2 L (a.2 - b) : ℝ) ≤ Rss then (1 : ℝ) else 0)) +
      (L : ℝ) ^ 2 * (2 * (32 * Λ ^ 5 * (200 * Λ * J * P⁻¹))) := by
    simp only [hFn, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, card_Z2]
    ring
  have e1 := hcnt a.1
  have e2 := hcnt a.2
  have hc : 0 ≤ Λ * ρ ^ 10 * m ^ 5 := by
    have : 0 ≤ Λ := by linarith
    positivity
  have hsc : ∑ b : Z2 L, (if (zdist2 L (a.1 - b) : ℝ) ≤ Rss then (1 : ℝ) else 0) +
      ∑ b : Z2 L, (if (zdist2 L (a.2 - b) : ℝ) ≤ Rss then (1 : ℝ) else 0) ≤
      2 * (81 * Lg ^ 4 * ellT L u ^ 2) := by linarith
  have hsumF : ∑ b : Z2 L, Fn b ≤ Λ * ρ ^ 10 * m ^ 5 * (2 * (81 * Lg ^ 4 * ellT L u ^ 2)) +
      (L : ℝ) ^ 2 * (2 * (32 * Λ ^ 5 * (200 * Λ * J * P⁻¹))) := by
    rw [hsplit]
    exact add_le_add (mul_le_mul_of_nonneg_left hsc hc) le_rfl
  exact hsum.trans (mul_le_mul_of_nonneg_left hsumF (by positivity))

/-- The near constant: `(162 Lg⁴ Λ + 12800 Λ⁶) e^{4Y} ≤ lossE2`. -/
private theorem near_const (h : E2Hyp L W E s u v D Λ K₀ M) :
    (162 * Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) ^ 4 * Λ + 12800 * Λ ^ 6) *
      Real.exp (4 * Real.log W ^ ((3 : ℝ) / 4)) ≤ lossE2 L W Λ K₀ := by
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hlog := (hyp_basic h).2.2.2.2.2.2.2.2
  have hlp := logP_ge (L := L) (W := W)
  have hloss := loss_ge h
  have hY0 := Y_nonneg h
  set Lg := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)
  set Y := Real.log W ^ ((3 : ℝ) / 4)
  have hΛ6 : Λ ≤ Λ ^ 6 := by
    have := pow_le_pow_right₀ hΛ (show 1 ≤ 6 by norm_num); simpa using this
  have hexp : Real.exp (4 * Y) ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have hLg0 : 0 ≤ Lg := by linarith
  have hA1 : Lg ^ 4 ≤ (1 + Lg) ^ 4 := pow_le_pow_left₀ hLg0 (by linarith) 4
  have hA2 : 1 ≤ (1 + Lg) ^ 4 := one_le_pow₀ (by linarith)
  have hB : 1 ≤ (1 + Real.log W) ^ 3 := one_le_pow₀ (by linarith)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛ60 : 0 ≤ Λ ^ 6 := by positivity
  set X := Λ ^ 6 * (1 + Lg) ^ 4 with hX
  have hX0 : 0 ≤ X := by positivity
  have ha : Lg ^ 4 * Λ ≤ X := by
    rw [hX, mul_comm (Λ ^ 6)]
    exact mul_le_mul hA1 hΛ6 hΛ0 (by positivity)
  have hb : Λ ^ 6 ≤ X := le_mul_of_one_le_right hΛ60 hA2
  have hc : X ≤ X * (1 + Real.log W) ^ 3 := le_mul_of_one_le_right hX0 hB
  have hpos : 0 ≤ 162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6 := by positivity
  have hc1 : 162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6 ≤ 10 ^ 12 * (X * (1 + Real.log W) ^ 3) := by
    linarith
  have e : 10 ^ 12 * Λ ^ 6 * (1 + Lg) ^ 4 * (1 + Real.log W) ^ 3 * Real.exp (8 * Y) =
      10 ^ 12 * (X * (1 + Real.log W) ^ 3) * Real.exp (8 * Y) := by rw [hX]; ring
  rw [e] at hloss
  calc (162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * Real.exp (4 * Y)
      ≤ 10 ^ 12 * (X * (1 + Real.log W) ^ 3) * Real.exp (8 * Y) :=
        mul_le_mul hc1 hexp (Real.exp_pos _).le (le_trans hpos hc1)
    _ ≤ lossE2 L W Λ K₀ := hloss

/-- **Near case** `|a₁ - a₂|_L ≤ 4ℓ*_v`: `‖EE‖ ≤ lossE2 · η_u⁻¹ ρ^{10} 𝒯_v(|a₁ - a₂|)²`. -/
private theorem near_case (h : E2Hyp L W E s u v D Λ K₀ M) (a a' : Z2 L × Z2 L)
    (hn : (zdist2 L (a.1 - a.2) : ℝ) ≤ 4 * ellStar L W v) :
    ‖EE L W E u M a a'‖ ≤ lossE2 L W Λ K₀ * ((etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10) *
      tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := by
  obtain ⟨hL3, hE, hu0, hv0, hu1, hv1, huv, hΛ, hlog⟩ := hyp_basic h
  have h2 := LemDecCalE_e2 h
  obtain ⟨hη1, hρ1⟩ := eta_rho_ge h
  have hlow := tail_lower (D := D) h hn
  have hsmall := near_far_small (D := D) h
  have hsum := near_sum (D := D) h a a'
  have hconst := near_const h
  have hlp := logP_ge (L := L) (W := W)
  set Lg := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12) with hLg
  set P := (L : ℝ) ^ 2 * (W : ℝ) ^ 12 with hP
  set J := jStarMat L W E D u M with hJ
  set ρ := ellT L u / ellT L s with hρ
  set m := (scaleM L W E u)⁻¹ with hm
  set Y := Real.log W ^ ((3 : ℝ) / 4) with hY
  set Td := tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) with hTd
  set V := (scaleM L W E v ^ 4)⁻¹ with hV
  have hMv4 : 0 ≤ V := by positivity
  have hρ10 : 1 ≤ ρ ^ 10 := one_le_pow₀ hρ1
  have hN1 : 1 ≤ (etaT E u)⁻¹ * ρ ^ 10 := one_le_mul_of_one_le_of_one_le hη1 hρ10
  set N := (etaT E u)⁻¹ * ρ ^ 10 with hN
  have hA : (W : ℝ) ^ 2 * ellT L u ^ 2 * m ^ 5 ≤ (etaT E u)⁻¹ * V := by
    have he1 := LemDecCalE_e1 (L := L) (W := W) hE hu1 (u := u)
    have hη := etaT_pos hE hu1
    have hMu : 0 < scaleM L W E u := by linarith [h2.1, h2.2.1]
    rw [he1]
    have hm4 : m ^ 4 ≤ V := by
      rw [hm, hV, inv_pow]
      exact inv_anti₀ (pow_pos (by linarith [h2.1]) 4) (pow_le_pow_left₀ (by linarith [h2.1]) h2.2.1 4)
    calc scaleM L W E u / etaT E u * m ^ 5 = (etaT E u)⁻¹ * m ^ 4 := by
          rw [hm]; field_simp
      _ ≤ (etaT E u)⁻¹ * V := mul_le_mul_of_nonneg_left hm4 (inv_nonneg.2 hη.le)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hLg0 : 0 ≤ Lg := by linarith
  have hk1 : (W : ℝ) ^ 2 * (Λ * ρ ^ 10 * m ^ 5 * (2 * (81 * Lg ^ 4 * ellT L u ^ 2))) ≤
      162 * Lg ^ 4 * Λ * (N * V) := by
    have e : (W : ℝ) ^ 2 * (Λ * ρ ^ 10 * m ^ 5 * (2 * (81 * Lg ^ 4 * ellT L u ^ 2))) =
        162 * Lg ^ 4 * Λ * ρ ^ 10 * ((W : ℝ) ^ 2 * ellT L u ^ 2 * m ^ 5) := by ring
    rw [e]
    calc 162 * Lg ^ 4 * Λ * ρ ^ 10 * ((W : ℝ) ^ 2 * ellT L u ^ 2 * m ^ 5)
        ≤ 162 * Lg ^ 4 * Λ * ρ ^ 10 * ((etaT E u)⁻¹ * V) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 162 * Lg ^ 4 * Λ * (N * V) := by rw [hN]; ring
  have hk2 : (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * (32 * Λ ^ 5 * (200 * Λ * J * P⁻¹)))) ≤
      12800 * Λ ^ 6 * (N * V) := by
    have e : (W : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * (32 * Λ ^ 5 * (200 * Λ * J * P⁻¹)))) =
        12800 * Λ ^ 6 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2 * (J * P⁻¹)) := by ring
    rw [e]
    have : V ≤ N * V := le_mul_of_one_le_left hMv4 hN1
    exact mul_le_mul_of_nonneg_left (hsmall.trans this) (by positivity)
  have step : ‖EE L W E u M a a'‖ ≤ (162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * (N * V) := by
    rw [mul_add] at hsum
    have e : (162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * (N * V) =
        162 * Lg ^ 4 * Λ * (N * V) + 12800 * Λ ^ 6 * (N * V) := by ring
    rw [e]
    exact hsum.trans (add_le_add hk1 hk2)
  have hN0 : 0 ≤ N := by linarith
  have hpos : 0 ≤ 162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6 := by positivity
  calc ‖EE L W E u M a a'‖ ≤ (162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * (N * V) := step
    _ ≤ (162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * (N * (Real.exp (4 * Y) * Td ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow hN0) hpos
    _ = ((162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * Real.exp (4 * Y)) * N * Td ^ 2 := by ring
    _ ≤ lossE2 L W Λ K₀ * N * Td ^ 2 := by
        have : 0 ≤ N * Td ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_right hconst this
        linarith [mul_assoc ((162 * Lg ^ 4 * Λ + 12800 * Λ ^ 6) * Real.exp (4 * Y)) N (Td ^ 2),
          mul_assoc (lossE2 L W Λ K₀) N (Td ^ 2)]

/-- Far case, the sum over `b, b'`. -/
private theorem far_sum (h : E2Hyp L W E s u v D Λ K₀ M) (a a' : Z2 L × Z2 L)
    (h1 : (zdist2 L (a.1 - a'.1) : ℝ) ≤ ellStar L W v)
    (h2 : (zdist2 L (a.2 - a'.2) : ℝ) ≤ ellStar L W v)
    (hd : 4 * ellStar L W v < (zdist2 L (a.1 - a.2) : ℝ)) :
    ‖EE L W E u M a a'‖ ≤ (W : ℝ) ^ 2 *
      (2 * ((50 * Λ * jStarMat L W E D u M) ^ 2 *
          (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 *
          tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) ^ 2 *
          (Λ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ *
            (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2))) * (4 * (9 * ellStar L W u ^ 2)) +
        2 * ((50 * Λ * jStarMat L W E D u M) ^ 3 *
          (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 *
          tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ)) *
          (2500 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹ *
            tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ))) := by
  obtain ⟨hL3, hE, hu0, hv0, hu1, hv1, huv, hΛ, hlog⟩ := hyp_basic h
  have hls := ellStar_ge h
  have hfloorC := (LemDecCalE_floor h).2.2.1
  set κ := 50 * Λ * jStarMat L W E D u M with hκ
  set S := Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) with hS
  set Td := tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) with hTd
  set R4 := Λ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ *
    (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) with hR4
  set ls := ellStar L W u with hls_def
  set Q := κ ^ 2 * S ^ 3 * Td ^ 2 * R4 with hQ
  set ind : Z2 L → Z2 L → ℝ := fun c b => if (zdist2 L (c - b) : ℝ) ≤ ls + 1 then 1 else 0
    with hind
  set Ff : Z2 L → ℝ := fun b => 2 * (Q * (ind a.1 b + ind a'.1 b + ind a.2 b + ind a'.2 b)) +
      2 * (κ ^ 3 * S ^ 3 * Td * tailT L W E D v (zdist2 L (a.1 - b) : ℝ) *
        tailT L W E D v (zdist2 L (b - a.2) : ℝ)) with hFf
  have hper : ∀ b b' : Z2 L, (zdist2 L (b - b') : ℝ) ≤ 1 →
      ‖loopAB (greenBlk L W E u M true) (greenBlk L W E u M false) a.1 a.2 b' a'.2 a'.1 b‖ +
        ‖loopAB (greenBlk L W E u M false) (greenBlk L W E u M true) a.2 a.1 b' a'.1 a'.2 b‖ ≤
        Ff b := by
    intro b b' hb
    have c1 := cut_far (D := D) h true a.1 a.2 a'.1 a'.2 b b' h1 h2 hb hd
    have hd' : 4 * ellStar L W v < (zdist2 L (a.2 - a.1) : ℝ) := by rw [zd_comm]; exact hd
    have c2 := cut_far (D := D) h false a.2 a.1 a'.2 a'.1 b b' h2 h1 hb hd'
    simp only [Bool.not_true, Bool.not_false] at c1 c2
    have c2' : ‖loopAB (greenBlk L W E u M false) (greenBlk L W E u M true) a.2 a.1 b' a'.1 a'.2 b‖ ≤
        Q * (ind a.1 b + ind a'.1 b + ind a.2 b + ind a'.2 b) +
          κ ^ 3 * S ^ 3 * Td * tailT L W E D v (zdist2 L (a.1 - b) : ℝ) *
            tailT L W E D v (zdist2 L (b - a.2) : ℝ) := by
      refine c2.trans (le_of_eq ?_)
      simp only [hQ, hTd, hind]
      rw [zd_comm a.2 a.1, zd_comm a.2 b, zd_comm b a.1, zd_comm a'.2 b]
      simp only [zd_comm b a.2, zd_comm b a'.2]
      ring
    have c1' : ‖loopAB (greenBlk L W E u M true) (greenBlk L W E u M false) a.1 a.2 b' a'.2 a'.1 b‖ ≤
        Q * (ind a.1 b + ind a'.1 b + ind a.2 b + ind a'.2 b) +
          κ ^ 3 * S ^ 3 * Td * tailT L W E D v (zdist2 L (a.1 - b) : ℝ) *
            tailT L W E D v (zdist2 L (b - a.2) : ℝ) := c1
    simp only [hFf]
    linarith
  have hsum : ‖EE L W E u M a a'‖ ≤ (W : ℝ) ^ 2 * ∑ b : Z2 L, Ff b := by
    refine (EE_le E u M a a').trans ?_
    gcongr with b
    exact sum_SB_le hL3 b _ (Ff b) (fun b' hb => hper b b' hb)
  have hcnt : ∀ c : Z2 L, ∑ b : Z2 L, ind c b ≤ 9 * ls ^ 2 := by
    intro c
    refine (count_le c (ls + 1) (by linarith)).trans ?_
    nlinarith
  have hconv := convTailT L W E D v hE hv0 hv1 hfloorC a.1 a.2
  have hsplit : ∑ b : Z2 L, Ff b = 2 * (Q * (∑ b : Z2 L, ind a.1 b + ∑ b : Z2 L, ind a'.1 b +
      ∑ b : Z2 L, ind a.2 b + ∑ b : Z2 L, ind a'.2 b)) +
      2 * (κ ^ 3 * S ^ 3 * Td) * ∑ b : Z2 L, tailT L W E D v (zdist2 L (a.1 - b) : ℝ) *
        tailT L W E D v (zdist2 L (b - a.2) : ℝ) := by
    simp only [hFf, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun b _ => by ring)
  have hQ0 : 0 ≤ Q := by
    have hu1' := hu1
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    have h2e := LemDecCalE_e2 h
    have : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 (by linarith [h2e.1, h2e.2.1])
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ jStarMat L W E D u M := by linarith [one_le_jStarMat L W dif_oneW E D u M]
    positivity
  have hk0 : 0 ≤ 2 * (κ ^ 3 * S ^ 3 * Td) := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ jStarMat L W E D u M := by linarith [one_le_jStarMat L W dif_oneW E D u M]
    have : 0 ≤ Td := (tailT_pos dif_oneW L E D v _).le
    positivity
  have hsumF : ∑ b : Z2 L, Ff b ≤ 2 * Q * (4 * (9 * ls ^ 2)) +
      2 * (κ ^ 3 * S ^ 3 * Td) * (2500 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹ * Td) := by
    rw [hsplit]
    have e1 := hcnt a.1
    have e2 := hcnt a'.1
    have e3 := hcnt a.2
    have e4 := hcnt a'.2
    have hs4 : ∑ b : Z2 L, ind a.1 b + ∑ b : Z2 L, ind a'.1 b + ∑ b : Z2 L, ind a.2 b +
        ∑ b : Z2 L, ind a'.2 b ≤ 4 * (9 * ls ^ 2) := by linarith
    have := mul_le_mul_of_nonneg_left hs4 hQ0
    have := mul_le_mul_of_nonneg_left hconv hk0
    nlinarith
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine hsumF.trans (le_of_eq ?_)
  ring


/-- The far constants: `180000 (log W)³ Λ³ S³ ≤ lossE2` and `6.25·10⁸ Λ³ S³ ≤ lossE2`,
`S = e² e^{2Y}`. -/
private theorem far_const (h : E2Hyp L W E s u v D Λ K₀ M) :
    180000 * Real.log W ^ 3 * Λ ^ 3 *
        (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 ≤ lossE2 L W Λ K₀ ∧
      625000000 * Λ ^ 3 *
        (Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))) ^ 3 ≤ lossE2 L W Λ K₀ := by
  have hΛ := (hyp_basic h).2.2.2.2.2.2.2.1
  have hlog := (hyp_basic h).2.2.2.2.2.2.2.2
  have hlp := logP_ge (L := L) (W := W)
  have hloss := loss_ge h
  have hY0 := Y_nonneg h
  set Lg := Real.log ((L : ℝ) ^ 2 * (W : ℝ) ^ 12)
  set Y := Real.log W ^ ((3 : ℝ) / 4)
  have hS3 := S3_le Y
  set S := Real.exp 2 * Real.exp (2 * Y)
  have hexp : Real.exp (6 * Y) ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have hS3' : S ^ 3 ≤ 404 * Real.exp (8 * Y) := hS3.trans (by linarith)
  have hS30 : 0 ≤ S ^ 3 := by positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hA2 : 1 ≤ (1 + Lg) ^ 4 := one_le_pow₀ (by linarith)
  have hB : 1 ≤ (1 + Real.log W) ^ 3 := one_le_pow₀ (by linarith)
  have hB' : Real.log W ^ 3 ≤ (1 + Real.log W) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hΛ60 : 0 ≤ Λ ^ 6 := by positivity
  set Z := Λ ^ 6 * (1 + Lg) ^ 4 * (1 + Real.log W) ^ 3 with hZ
  have hZ1 : Real.log W ^ 3 * Λ ^ 3 ≤ Z := by
    have : Λ ^ 6 ≤ Λ ^ 6 * (1 + Lg) ^ 4 := le_mul_of_one_le_right hΛ60 hA2
    rw [hZ, mul_comm (Real.log W ^ 3)]
    exact mul_le_mul (hΛ3.trans this) hB' (by positivity) (by positivity)
  have hZ2 : Λ ^ 3 ≤ Z := by
    have : Λ ^ 6 ≤ Λ ^ 6 * (1 + Lg) ^ 4 := le_mul_of_one_le_right hΛ60 hA2
    have h' : Λ ^ 6 * (1 + Lg) ^ 4 ≤ Z := le_mul_of_one_le_right (by positivity) hB
    linarith
  have hZ0 : 0 ≤ Z := le_trans (by positivity) hZ2
  have e : 10 ^ 12 * Λ ^ 6 * (1 + Lg) ^ 4 * (1 + Real.log W) ^ 3 * Real.exp (8 * Y) =
      10 ^ 12 * Z * Real.exp (8 * Y) := by rw [hZ]; ring
  rw [e] at hloss
  have hE8 : 0 ≤ Real.exp (8 * Y) := (Real.exp_pos _).le
  have hlw3 : 0 ≤ Real.log W ^ 3 := by positivity
  constructor
  · calc 180000 * Real.log W ^ 3 * Λ ^ 3 * S ^ 3
        ≤ 180000 * Real.log W ^ 3 * Λ ^ 3 * (404 * Real.exp (8 * Y)) :=
          mul_le_mul_of_nonneg_left hS3' (by positivity)
      _ = 72720000 * (Real.log W ^ 3 * Λ ^ 3) * Real.exp (8 * Y) := by ring
      _ ≤ 72720000 * Z * Real.exp (8 * Y) := by gcongr
      _ ≤ 10 ^ 12 * Z * Real.exp (8 * Y) := by gcongr; norm_num
      _ ≤ lossE2 L W Λ K₀ := hloss
  · calc 625000000 * Λ ^ 3 * S ^ 3 ≤ 625000000 * Λ ^ 3 * (404 * Real.exp (8 * Y)) :=
          mul_le_mul_of_nonneg_left hS3' (by positivity)
      _ = 252500000000 * Λ ^ 3 * Real.exp (8 * Y) := by ring
      _ ≤ 252500000000 * Z * Real.exp (8 * Y) := by gcongr
      _ ≤ 10 ^ 12 * Z * Real.exp (8 * Y) := by gcongr; norm_num
      _ ≤ lossE2 L W Λ K₀ := hloss

/-- **Far case** `|a₁ - a₂|_L > 4ℓ*_v`:
`‖EE‖ ≤ lossE2 · (η_u⁻¹ ρ³ M_u^{-1/2} J² + η_v⁻¹ M_v⁻¹ J³) · 𝒯_v(|a₁ - a₂|)²`. -/
private theorem far_case (h : E2Hyp L W E s u v D Λ K₀ M) (a a' : Z2 L × Z2 L)
    (h1 : (zdist2 L (a.1 - a'.1) : ℝ) ≤ ellStar L W v)
    (h2 : (zdist2 L (a.2 - a'.2) : ℝ) ≤ ellStar L W v)
    (hd : 4 * ellStar L W v < (zdist2 L (a.1 - a.2) : ℝ)) :
    ‖EE L W E u M a a'‖ ≤ lossE2 L W Λ K₀ *
      ((etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
          jStarMat L W E D u M ^ 2 +
        (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ * jStarMat L W E D u M ^ 3) *
      tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := by
  obtain ⟨hL3, hE, hu0, hv0, hu1, hv1, huv, hΛ, hlog⟩ := hyp_basic h
  have h2e := LemDecCalE_e2 h
  have hsum := far_sum (D := D) h a a' h1 h2 hd
  obtain ⟨hC1, hC2⟩ := far_const (D := D) h
  have he1u := LemDecCalE_e1 (L := L) (W := W) hE hu1 (u := u)
  have he1v := LemDecCalE_e1 (L := L) (W := W) hE hv1 (u := v)
  have hηu := etaT_pos hE hu1
  have hηv := etaT_pos hE hv1
  have hMu : 0 < scaleM L W E u := by linarith [h2e.1, h2e.2.1]
  have hMv : 0 < scaleM L W E v := by linarith [h2e.1]
  have hlogW0 : 0 ≤ Real.log W := by linarith
  set J := jStarMat L W E D u M with hJ
  set Y := Real.log W ^ ((3 : ℝ) / 4) with hY
  set S := Real.exp 2 * Real.exp (2 * Y) with hS
  set Td := tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) with hTd
  set ρ := ellT L u / ellT L s with hρ
  set m := (scaleM L W E u)⁻¹ with hm
  set h12 := m ^ ((1 : ℝ) / 2) with hh12
  set T1 := (etaT E u)⁻¹ * ρ ^ 3 * h12 * J ^ 2 with hT1
  set T2 := (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ * J ^ 3 with hT2
  -- `ℓ*_u² = (log W)³ ℓ_u²`
  have hls2 : ellStar L W u ^ 2 = Real.log W ^ 3 * ellT L u ^ 2 := by
    unfold ellStar
    rw [mul_pow, ← Real.rpow_natCast (Real.log W ^ ((3 : ℝ) / 2)), ← Real.rpow_mul hlogW0]
    norm_num
  have hA : (W : ℝ) ^ 2 * (2 * ((50 * Λ * J) ^ 2 * S ^ 3 * Td ^ 2 *
      (Λ * ρ ^ 3 * m * h12)) * (4 * (9 * ellStar L W u ^ 2))) =
      (180000 * Real.log W ^ 3 * Λ ^ 3 * S ^ 3) * T1 * Td ^ 2 := by
    rw [hls2, hT1]
    have e : (W : ℝ) ^ 2 * ellT L u ^ 2 * m = (etaT E u)⁻¹ := by
      rw [he1u, hm]; field_simp
    calc (W : ℝ) ^ 2 * (2 * ((50 * Λ * J) ^ 2 * S ^ 3 * Td ^ 2 * (Λ * ρ ^ 3 * m * h12)) *
          (4 * (9 * (Real.log W ^ 3 * ellT L u ^ 2))))
        = 180000 * Real.log W ^ 3 * Λ ^ 3 * S ^ 3 * ρ ^ 3 * h12 * J ^ 2 * Td ^ 2 *
            ((W : ℝ) ^ 2 * ellT L u ^ 2 * m) := by ring
      _ = _ := by rw [e]; ring
  have hB : (W : ℝ) ^ 2 * (2 * ((50 * Λ * J) ^ 3 * S ^ 3 * Td) *
      (2500 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹ * Td)) =
      (625000000 * Λ ^ 3 * S ^ 3) * T2 * Td ^ 2 := by
    rw [hT2]
    have e : (W : ℝ) ^ 2 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹ =
        (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ := by
      rw [he1v]; field_simp
    calc (W : ℝ) ^ 2 * (2 * ((50 * Λ * J) ^ 3 * S ^ 3 * Td) *
          (2500 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹ * Td))
        = 625000000 * Λ ^ 3 * S ^ 3 * J ^ 3 * Td ^ 2 *
            ((W : ℝ) ^ 2 * ellT L v ^ 2 * (scaleM L W E v ^ 2)⁻¹) := by ring
      _ = _ := by rw [e]; ring
  rw [mul_add, hA, hB] at hsum
  have hJ0 : 0 ≤ J := by linarith [one_le_jStarMat L W dif_oneW E D u M]
  have hρ0 : 0 ≤ ρ := by
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    positivity
  have hm0 : 0 ≤ m := inv_nonneg.2 hMu.le
  have hT10 : 0 ≤ T1 := by
    have : 0 ≤ h12 := Real.rpow_nonneg hm0 _
    have : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu.le
    positivity
  have hT20 : 0 ≤ T2 := by
    have : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hηv.le
    have : 0 ≤ (scaleM L W E v)⁻¹ := inv_nonneg.2 hMv.le
    positivity
  have hTd2 : 0 ≤ Td ^ 2 := sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_right hC1 (mul_nonneg hT10 hTd2)
  have k2 := mul_le_mul_of_nonneg_right hC2 (mul_nonneg hT20 hTd2)
  have e3 : lossE2 L W Λ K₀ * (T1 + T2) * Td ^ 2 =
      lossE2 L W Λ K₀ * (T1 * Td ^ 2) + lossE2 L W Λ K₀ * (T2 * Td ^ 2) := by ring
  rw [e3]
  have e4 : (180000 * Real.log W ^ 3 * Λ ^ 3 * S ^ 3) * T1 * Td ^ 2 =
      (180000 * Real.log W ^ 3 * Λ ^ 3 * S ^ 3) * (T1 * Td ^ 2) := by ring
  have e5 : (625000000 * Λ ^ 3 * S ^ 3) * T2 * Td ^ 2 =
      (625000000 * Λ ^ 3 * S ^ 3) * (T2 * Td ^ 2) := by ring
  rw [e4, e5] at hsum
  exact hsum.trans (add_le_add k1 k2)


end Cases

/-! ## 9. The theorem -/

/-- **`lemDecCalE_dif`** (`res_deccalE_dif`), under (57) at
the endpoint `v`: near case by `near_case` (the indicator is `1`), far case by `far_case` (the
indicator is `0`). -/
theorem lemDecCalE_dif : LemDecCalE_dif := by
  intro L W _ _ E s u v D Λ K₀ M h a a' h1 h2
  have hloss : 0 ≤ lossE2 L W Λ K₀ := by linarith [LemDecCalE_six_thousand_le_lossE2 h]
  obtain ⟨-, hE, hu0, hv0, hu1, hv1, -, -, -⟩ := hyp_basic h
  have h2e := LemDecCalE_e2 h
  have hJ0 : 0 ≤ jStarMat L W E D u M := by linarith [one_le_jStarMat L W dif_oneW E D u M]
  have hηu := (etaT_pos hE hu1).le
  have hηv := (etaT_pos hE hv1).le
  have hρ0 : 0 ≤ ellT L u / ellT L s := by
    have := (ellT_pos_le (L := L) dif_oneL hu1).1
    have hs1 : s < 1 := (h.2.2.2.1).trans_lt hu1
    have := (ellT_pos_le (L := L) dif_oneL hs1).1
    positivity
  have hm0 : 0 ≤ (scaleM L W E u)⁻¹ := inv_nonneg.2 (by linarith [h2e.1, h2e.2.1])
  have hmv0 : 0 ≤ (scaleM L W E v)⁻¹ := inv_nonneg.2 (by linarith [h2e.1])
  have hT1 : 0 ≤ (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 3 * (scaleM L W E u)⁻¹ ^ ((1 : ℝ) / 2) *
      jStarMat L W E D u M ^ 2 := by
    have := Real.rpow_nonneg hm0 ((1 : ℝ) / 2)
    positivity
  have hT2 : 0 ≤ (etaT E v)⁻¹ * (scaleM L W E v)⁻¹ * jStarMat L W E D u M ^ 3 := by positivity
  have hN : 0 ≤ (etaT E u)⁻¹ * (ellT L u / ellT L s) ^ 10 := by positivity
  have hTd : 0 ≤ tailT L W E D v (zdist2 L (a.1 - a.2) : ℝ) ^ 2 := sq_nonneg _
  by_cases hn : (zdist2 L (a.1 - a.2) : ℝ) ≤ 4 * ellStar L W v
  · simp only [hn, ↓reduceIte, mul_one]
    refine (near_case h a a' hn).trans ?_
    apply mul_le_mul_of_nonneg_right _ hTd
    apply mul_le_mul_of_nonneg_left _ hloss
    linarith
  · simp only [hn, ↓reduceIte, mul_zero, zero_add]
    refine (far_case h a a' h1 h2 (lt_of_not_ge hn)).trans (le_of_eq ?_)
    ring

end RBM.Path
