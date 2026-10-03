/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.DriftLip
import RBM2D.Gauss.SteinMatrix
import RBM2D.Gauss.LoopSampleCont
import RBM2D.Gauss.LoopEnvelope
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Gauss.LoopDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The one-step expansion with its envelope (`d = 2`)

The definitions `genMat` (the generator of one Gaussian increment for a loop functional),
`envConst` (the explicit envelope constant) and `OneStepEnvelope` (the one-step expansion with
envelope), and the theorem `oneStepEnvelope : OneStepEnvelope`.

## Proof outline

The error is split as `T₂ + T₁` with `τ = √Δ`, `X = Xmat ω`, `f_v(A) = 𝓛(blockMat A, z_v, I)`:

* **space step** at fixed time `u` (`OneStep_space_step`).  With `F(x) = E f_u(M + x X)`,
  `F'(x) = x Σ_c gvar_c E ∂²_c f_u(M + x X)` by differentiation under the integral sign
  (`OneStep_hasDerivAt_F`) and the coordinatewise Stein identity `GaussianProduct.stein`
  (`OneStep_stein_coord`); the fencing lemma `image_norm_le_of_norm_deriv_right_le_deriv_boundary`
  then gives `‖F(τ) - f_u(M) - τ² g_u(M)‖ ≤ (Λ'/3) τ³`.  The resolvent is unbounded off the
  Hermitian set, so only Hermitian samples are used and no global `ContDiff` or bound is
  asserted for loops.
* **time step** at fixed sample `A` (`OneStep_time_step`): the second-order Taylor expansion of
  `v ↦ f_v(A)`.
* The derivatives of the loop functional are the jets `w1`, `w2` of a word of resolvent factors
  (`R' = -R D R`, section 1) with `D = B` (a Hermitian direction) for the space variable and
  `D = m_σ` for the spectral variable; their norms and their Lipschitz constants in the matrix are
  proved by induction on the word (sections 1--3), with `N = (LW)²` and `‖E_a‖ ≤ 1` (`d = 2`).
* Counts (section 4): `Σ_c gvar_c ≤ 2 N` from the row sums of `S^{(B)}` for every `L`
  (`SB L a` has at most five entries `1/5`), and `‖X‖ ≤ 2 Σ_c |ω_c|`, `E‖X‖ ≤ 4 N²`.

The Lipschitz constant of the space generator is computed directly from the third-derivative
structure of the word; of `Path/DriftLip.lean` only `norm_green_sub_le_of_herm` is used.  The
constant closed by `OneStep_closure` is
`(32/3) N⁴ k(k+1)(k+2) η^{-(k+3)} + N k(k+1) η^{-(k+2)} (½ + 4N²) ≤ 16 (k+3)⁴ N⁴ (1+η⁻¹)^{k+4}`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- The generator of one Gaussian increment for the loop functional `Φ_u(M) = 𝓛_{u,I}(M)`:
`½ Σ_c gvar(c) ∂²_c Φ_u(M) + ∂_u Φ_u(M)`, with one-variable derivatives along the coordinate
matrices `coordinateMatrix c` and along the spectral path. -/
def genMat {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        gloop L W (blockMat (M + (y : ℂ) • coordinateMatrix L W c)) (spectralZ E u) I)) 0 +
    deriv (fun v : ℝ => gloop L W (blockMat M) (spectralZ E v) I) u

/-- The explicit envelope constant of the one-step expansion:
`16 (k+3)^4 N^4 (1 + η_v^{-1})^{k+4}` for a loop of length `k`, `N = (WL)²`, `v` the later time. -/
def envConst (L W : ℕ) (E : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  16 * ((k : ℝ) + 3) ^ 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 4 * (1 + (etaT E v)⁻¹) ^ (k + 4)

/-- **The one-step expansion with envelope** (the `N^C Δ^{3/2}` control): for Hermitian `M`,
`0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a well-formed loop of length `k`,
`‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · gen_u(M)‖ ≤ envConst · Δ^{3/2}`. -/
def OneStepEnvelope : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : LoopIdx (Z2 L)), I.WF →
    ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
      ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
        ‖(∫ ω', gloop L W (blockMat (M + (Real.sqrt Δ : ℂ) • Xmat L W ω'))
              (spectralZ E (u + Δ)) I ∂(P L W)) -
            gloop L W (blockMat M) (spectralZ E u) I - (Δ : ℂ) * genMat E u M I‖ ≤
          envConst L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2)

/-! ## 1. Generic jets of a word of resolvent factors

A word `∏ᵢ R_{σᵢ} E_{aᵢ}` whose resolvent factors have the jets `R`, `r1 = -R D R`,
`r2 = 2 R D R D R` along a line has the jets `w0`, `w1`, `w2` below (Leibniz recursion). -/

section Jets

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- The word `∏ R_{σᵢ} E_{aᵢ}` (as in `gloopProd`). -/
private def OneStep_w0 (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : Matrix n n ℂ :=
  l.foldr (fun p M => R p.1 * Ei p.2 * M) 1

/-- First jet of a resolvent factor. -/
private def OneStep_r1 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  -(R σ * D σ * R σ)

/-- Second jet of a resolvent factor. -/
private def OneStep_r2 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ

/-- First derivative of the word. -/
private def OneStep_w1 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (OneStep_r1 R D p.1 * Ei p.2) * OneStep_w0 R Ei l
      + (R p.1 * Ei p.2) * OneStep_w1 R D Ei l

/-- Second derivative of the word. -/
private def OneStep_w2 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (OneStep_r2 R D p.1 * Ei p.2) * OneStep_w0 R Ei l
      + ((OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l
          + (OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l)
      + (R p.1 * Ei p.2) * OneStep_w2 R D Ei l

private theorem OneStep_w0_cons (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) (p : Bool × ι)
    (l : List (Bool × ι)) :
    OneStep_w0 R Ei (p :: l) = R p.1 * Ei p.2 * OneStep_w0 R Ei l := rfl

private theorem OneStep_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

private theorem OneStep_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem OneStep_norm_sub_mul_le {A₁ A₂ B₁ B₂ : Matrix n n ℂ} {a₂ b₁ da db : ℝ}
    (hA₂ : ‖A₂‖ ≤ a₂) (hB₁ : ‖B₁‖ ≤ b₁) (hdA : ‖A₁ - A₂‖ ≤ da) (hdB : ‖B₁ - B₂‖ ≤ db) :
    ‖A₁ * B₁ - A₂ * B₂‖ ≤ da * b₁ + a₂ * db := by
  have h : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by noncomm_ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (OneStep_nmul hdA hB₁) (OneStep_nmul hA₂ hdB))

private theorem OneStep_norm_add3 (X Y Z : Matrix n n ℂ) :
    ‖X + (Y + Y) + Z‖ ≤ ‖X‖ + 2 * ‖Y‖ + ‖Z‖ := by
  have h1 := norm_add_le (X + (Y + Y)) Z
  have h2 := norm_add_le X (Y + Y)
  have h3 := norm_add_le Y Y
  linarith

/-- The hypotheses of the norm bounds on the jets of a word. -/
private structure OneStep_Data (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b : ℝ) : Prop where
  hK : 0 ≤ K
  hb : 0 ≤ b
  hR : ∀ σ, ‖R σ‖ ≤ K
  hD : ∀ σ, ‖D σ‖ ≤ b
  hE : ∀ a, ‖Ei a‖ ≤ 1

/-- The hypotheses of the Lipschitz bounds: a second factor family at distance `K² δ`. -/
private structure OneStep_Diff (R₁ R₂ D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b δ : ℝ) : Prop where
  d₁ : OneStep_Data R₁ D Ei K b
  hR₂ : ∀ σ, ‖R₂ σ‖ ≤ K
  hδ : 0 ≤ δ
  hdiff : ∀ σ, ‖R₁ σ - R₂ σ‖ ≤ K ^ 2 * δ

section Bounds

variable {R D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b : ℝ}

private theorem OneStep_norm_r1_le (h : OneStep_Data R D Ei K b) (σ : Bool) :
    ‖OneStep_r1 R D σ‖ ≤ K * b * K := by
  rw [OneStep_r1, norm_neg]
  exact OneStep_nmul (OneStep_nmul (h.hR σ) (h.hD σ)) (h.hR σ)

private theorem OneStep_norm_r2_le (h : OneStep_Data R D Ei K b) (σ : Bool) :
    ‖OneStep_r2 R D σ‖ ≤ 2 * (K * b * K * b * K) := by
  rw [OneStep_r2]
  have h5 := OneStep_nmul (OneStep_nmul (OneStep_nmul (OneStep_nmul (h.hR σ) (h.hD σ))
    (h.hR σ)) (h.hD σ)) (h.hR σ)
  calc ‖R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ‖
      ≤ ‖R σ * D σ * R σ * D σ * R σ‖ + ‖R σ * D σ * R σ * D σ * R σ‖ := norm_add_le _ _
    _ ≤ K * b * K * b * K + K * b * K * b * K := add_le_add h5 h5
    _ = 2 * (K * b * K * b * K) := by ring

private theorem OneStep_norm_w0_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w0 R Ei l‖ ≤ K ^ l.length := by
  induction l with
  | nil => simpa [OneStep_w0] using OneStep_norm_one_le
  | cons p l ih =>
      rw [OneStep_w0_cons, List.length_cons, pow_succ]
      calc ‖R p.1 * Ei p.2 * OneStep_w0 R Ei l‖ ≤ (K * 1) * K ^ l.length :=
            OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
        _ = K ^ l.length * K := by ring

private theorem OneStep_norm_w1_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w1 R D Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * b := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, List.length_cons]
      have h1 : ‖(OneStep_r1 R D p.1 * Ei p.2) * OneStep_w0 R Ei l‖
          ≤ (K * b * K * 1) * K ^ l.length :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r1_le h p.1) (h.hE p.2))
          (OneStep_norm_w0_le h l)
      have h2 : ‖(R p.1 * Ei p.2) * OneStep_w1 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
      push_cast
      ring

private theorem OneStep_norm_w2_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w2 R D Ei l‖ ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2 := by
  induction l with
  | nil => simp [OneStep_w2]
  | cons p l ih =>
      rw [OneStep_w2, List.length_cons]
      have h1 : ‖(OneStep_r2 R D p.1 * Ei p.2) * OneStep_w0 R Ei l‖
          ≤ (2 * (K * b * K * b * K) * 1) * K ^ l.length :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r2_le h p.1) (h.hE p.2))
          (OneStep_norm_w0_le h l)
      have h2 : ‖(OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l‖
          ≤ (K * b * K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r1_le h p.1) (h.hE p.2))
          (OneStep_norm_w1_le h l)
      have h3 : ‖(R p.1 * Ei p.2) * OneStep_w2 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2) :=
        OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (OneStep_norm_add3 _ _ _).trans ((add_le_add (add_le_add h1
        (mul_le_mul_of_nonneg_left h2 zero_le_two)) h3).trans (le_of_eq ?_))
      push_cast
      ring

end Bounds

end Jets

section DiffBounds

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R₁ R₂ D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b δ : ℝ}

private theorem OneStep_norm_r1_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖OneStep_r1 R₁ D σ - OneStep_r1 R₂ D σ‖ ≤ 2 * (K ^ 3 * b * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul (h.hdiff σ) (h.d₁.hD σ)
  have := OneStep_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have e : OneStep_r1 R₁ D σ - OneStep_r1 R₂ D σ
      = -(R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ) := by
    simp only [OneStep_r1]; abel
  rw [e, norm_neg]
  refine this.trans (le_of_eq ?_)
  ring

private theorem OneStep_norm_r2_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖OneStep_r2 R₁ D σ - OneStep_r2 R₂ D σ‖ ≤ 6 * (K ^ 4 * b ^ 2 * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hδ := h.hδ
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul (h.hdiff σ) (h.d₁.hD σ)
  -- `R D R`
  have h3 := OneStep_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have h3' : ‖R₂ σ * D σ * R₂ σ‖ ≤ K * b * K :=
    OneStep_nmul (OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)) (h.hR₂ σ)
  -- `R D R D`
  have h4 : ‖(R₁ σ * D σ * R₁ σ) * D σ - (R₂ σ * D σ * R₂ σ) * D σ‖
      ≤ (K ^ 2 * δ * b * K + K * b * (K ^ 2 * δ)) * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul h3 (h.d₁.hD σ)
  have h4' : ‖R₂ σ * D σ * R₂ σ * D σ‖ ≤ K * b * K * b :=
    OneStep_nmul h3' (h.d₁.hD σ)
  -- `R D R D R`
  have h5 := OneStep_norm_sub_mul_le h4' (h.d₁.hR σ) h4 (h.hdiff σ)
  have e : OneStep_r2 R₁ D σ - OneStep_r2 R₂ D σ
      = (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ)
        + (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ) := by
    simp only [OneStep_r2]; abel
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add h5 h5).trans (le_of_eq ?_))
  ring

private theorem OneStep_norm_w0_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w0 R₁ Ei l - OneStep_w0 R₂ Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * δ := by
  induction l with
  | nil => simp [OneStep_w0]
  | cons p l ih =>
      rw [OneStep_w0_cons, OneStep_w0_cons, List.length_cons]
      have hA₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) (h.d₁.hE p.2)
      have hdA : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) (h.d₁.hE p.2)
      have := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA ih
      refine this.trans (le_of_eq ?_)
      push_cast
      ring

private theorem OneStep_norm_w1_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w1 R₁ D Ei l - OneStep_w1 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b * δ := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, List.length_cons]
      have hE := h.d₁.hE p.2
      -- the `r1` part
      have hA₂ : ‖OneStep_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        OneStep_nmul (OneStep_norm_r1_le ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩ p.1) hE
      have hdA : ‖OneStep_r1 R₁ D p.1 * Ei p.2 - OneStep_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r1_sub_le h p.1) hE
      have hα := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA
        (OneStep_norm_w0_sub_le h l)
      -- the `R` part
      have hB₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) hE
      have hdB : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) hE
      have hβ := OneStep_norm_sub_mul_le hB₂ (OneStep_norm_w1_le h.d₁ l) hdB ih
      rw [add_sub_add_comm]
      refine (norm_add_le _ _).trans ((add_le_add hα hβ).trans (le_of_eq ?_))
      push_cast
      ring

private theorem OneStep_norm_w2_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w2 R₁ D Ei l - OneStep_w2 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * (l.length + 2) * K ^ (l.length + 3) * b ^ 2 * δ := by
  induction l with
  | nil => simp [OneStep_w2]
  | cons p l ih =>
      rw [OneStep_w2, OneStep_w2, List.length_cons]
      have hE := h.d₁.hE p.2
      have h₂ : OneStep_Data R₂ D Ei K b := ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩
      -- the `r2` part
      have hA₂ : ‖OneStep_r2 R₂ D p.1 * Ei p.2‖ ≤ 2 * (K * b * K * b * K) * 1 :=
        OneStep_nmul (OneStep_norm_r2_le h₂ p.1) hE
      have hdA : ‖OneStep_r2 R₁ D p.1 * Ei p.2 - OneStep_r2 R₂ D p.1 * Ei p.2‖
          ≤ 6 * (K ^ 4 * b ^ 2 * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r2_sub_le h p.1) hE
      have hα := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA
        (OneStep_norm_w0_sub_le h l)
      -- the `r1` part
      have hB₂ : ‖OneStep_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        OneStep_nmul (OneStep_norm_r1_le h₂ p.1) hE
      have hdB : ‖OneStep_r1 R₁ D p.1 * Ei p.2 - OneStep_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r1_sub_le h p.1) hE
      have hβ := OneStep_norm_sub_mul_le hB₂ (OneStep_norm_w1_le h.d₁ l) hdB
        (OneStep_norm_w1_sub_le h l)
      -- the `R` part
      have hC₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) hE
      have hdC : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) hE
      have hγ := OneStep_norm_sub_mul_le hC₂ (OneStep_norm_w2_le h.d₁ l) hdC ih
      have e : ∀ a₁ a₂ c₁ c₂ d₁ d₂ : Matrix n n ℂ,
          (a₁ + (c₁ + c₁) + d₁) - (a₂ + (c₂ + c₂) + d₂)
            = (a₁ - a₂) + ((c₁ - c₂) + (c₁ - c₂)) + (d₁ - d₂) := fun _ _ _ _ _ _ => by abel
      rw [e]
      refine (OneStep_norm_add3 _ _ _).trans ((add_le_add (add_le_add hα
        (mul_le_mul_of_nonneg_left hβ zero_le_two)) hγ).trans (le_of_eq ?_))
      push_cast
      ring

end DiffBounds

section Deriv

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {Rt : ℝ → Bool → Matrix n n ℂ} {D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {t : ℝ}

/-- Jets of a word along a family of resolvent factors with `R' = -R D R`. -/
private theorem OneStep_hasDerivAt_w0
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => OneStep_w0 (Rt s) Ei l) (OneStep_w1 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [OneStep_w0, OneStep_w1] using hasDerivAt_const t (1 : Matrix n n ℂ)
  | cons p l ih =>
      have h : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * OneStep_w0 (Rt s) Ei l)
          ((-(Rt t p.1 * D p.1 * Rt t p.1)) * Ei p.2 * OneStep_w0 (Rt t) Ei l
            + Rt t p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      simpa only [OneStep_w0_cons, OneStep_w1, OneStep_r1] using h

private theorem OneStep_hasDerivAt_w1
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => OneStep_w1 (Rt s) D Ei l) (OneStep_w2 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [OneStep_w1, OneStep_w2] using hasDerivAt_const t (0 : Matrix n n ℂ)
  | cons p l ih =>
      have hr1 : HasDerivAt (fun s => OneStep_r1 (Rt s) D p.1)
          (OneStep_r2 (Rt t) D p.1) t := by
        have h : HasDerivAt (fun s => -(Rt s p.1 * D p.1 * Rt s p.1))
            (-(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1))) t :=
          (((hR p.1).mul_const (D p.1)).mul (hR p.1)).neg
        have e : OneStep_r2 (Rt t) D p.1 = -(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1)) := by
          simp only [OneStep_r2]
          noncomm_ring
        rw [e]
        exact h
      have h0 := OneStep_hasDerivAt_w0 (Ei := Ei) hR l
      have h1 : HasDerivAt (fun s => OneStep_r1 (Rt s) D p.1 * Ei p.2 * OneStep_w0 (Rt s) Ei l)
          (OneStep_r2 (Rt t) D p.1 * Ei p.2 * OneStep_w0 (Rt t) Ei l
            + OneStep_r1 (Rt t) D p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l) t :=
        (hr1.mul_const (Ei p.2)).mul h0
      have h2 : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * OneStep_w1 (Rt s) D Ei l)
          (OneStep_r1 (Rt t) D p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l
            + Rt t p.1 * Ei p.2 * OneStep_w2 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      have h3 := h1.add h2
      refine h3.congr_deriv ?_
      simp only [OneStep_w2]
      abel

end Deriv

section LinCont

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ}

private theorem OneStep_w1_add (D₁ D₂ : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    OneStep_w1 R (D₁ + D₂) Ei l = OneStep_w1 R D₁ Ei l + OneStep_w1 R D₂ Ei l := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, OneStep_w1, ih]
      simp only [OneStep_r1, Pi.add_apply]
      noncomm_ring

private theorem OneStep_w1_smul (c : ℝ) (D : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    OneStep_w1 R (c • D) Ei l = c • OneStep_w1 R D Ei l := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, ih]
      simp only [OneStep_r1, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, smul_add, Matrix.neg_mul,
        smul_neg]

/-- `D ↦ w1 R D` is real-linear. -/
private def OneStep_w1Lin (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : (Bool → Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ where
  toFun D := OneStep_w1 R D Ei l
  map_add' D₁ D₂ := OneStep_w1_add D₁ D₂ l
  map_smul' c D := OneStep_w1_smul c D l

variable {X : Type*} [TopologicalSpace X] {Rt : X → Bool → Matrix n n ℂ}
  {D : Bool → Matrix n n ℂ}

private theorem OneStep_continuous_w0 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w0 (Rt x) Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih => exact (((h p.1).mul continuous_const).mul ih)

private theorem OneStep_continuous_w1 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w1 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      exact ((hr1.mul continuous_const).mul (OneStep_continuous_w0 h l)).add
        (((h p.1).mul continuous_const).mul ih)

private theorem OneStep_continuous_w2 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w2 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      have hr2 : Continuous fun x => OneStep_r2 (Rt x) D p.1 := by
        have h5 : Continuous fun x => Rt x p.1 * D p.1 * Rt x p.1 * D p.1 * Rt x p.1 :=
          (((((h p.1).mul continuous_const).mul (h p.1)).mul continuous_const).mul (h p.1))
        exact h5.add h5
      have h1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 * Ei p.2 * OneStep_w1 (Rt x) D Ei l :=
        (hr1.mul continuous_const).mul (OneStep_continuous_w1 (Ei := Ei) (D := D) h l)
      exact (((hr2.mul continuous_const).mul (OneStep_continuous_w0 h l)).add (h1.add h1)).add
        (((h p.1).mul continuous_const).mul ih)

end LinCont

/-! ## 2. The loop functional along a line and along the spectral path -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem OneStep_hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- The derivative of a signed resolvent along a moving Hermitian matrix and spectral parameter. -/
private theorem OneStep_hasDerivAt_Gsig {H : ℝ → Matrix n n ℂ} {zf : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {t : ℝ}
    (hH : HasDerivAt H H' t) (hz : HasDerivAt zf z' t) (hherm : (H t).IsHermitian)
    (him : (zf t).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s => Gsig (H s) (zf s) σ)
      (-(Gsig (H t) (zf t) σ *
        (H' - (if σ then z' else (starRingEnd ℂ) z') • (1 : Matrix n n ℂ)) *
        Gsig (H t) (zf t) σ)) t := by
  cases σ with
  | true => exact hasDerivAt_green_moving hH hz hherm him
  | false =>
      have hz' : HasDerivAt (fun s => (starRingEnd ℂ) (zf s)) ((starRingEnd ℂ) z') t := hz.star
      have him' : ((starRingEnd ℂ) (zf t)).im ≠ 0 := by simpa using him
      exact hasDerivAt_green_moving hH hz' hherm him'

/-- Both spectral signs satisfy the same resolvent-difference bound. -/
private theorem OneStep_norm_Gsig_sub_le {M₁ M₂ : Matrix n n ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    ‖Gsig M₁ z σ - Gsig M₂ z σ‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by
  cases σ
  · have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    have := norm_green_sub_le_of_herm hM₁ hM₂ hz'
    simpa using this
  · exact norm_green_sub_le_of_herm hM₁ hM₂ hz

end Resolvent

section Loop

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The first jet `tr w1` of the loop functional with resolvent data `Gsig H z` and directions
`D`. -/
private def OneStep_J1 (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  Matrix.trace (OneStep_w1 (fun σ => Gsig H z σ) D (Eblk L W) (I.σ.zip I.a))

/-- The second jet `tr w2` of the loop functional. -/
private def OneStep_J2 (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  Matrix.trace (OneStep_w2 (fun σ => Gsig H z σ) D (Eblk L W) (I.σ.zip I.a))

/-- The spectral direction of the factor `G(σ)`: `m_σ · 1`. -/
private def OneStep_Dsp (L W : ℕ) (E : ℝ) :
    Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  fun σ => spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)

section LineDeriv

variable {H B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

private theorem OneStep_hasDerivAt_lineR (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (y : ℝ) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gsig (H + (s : ℂ) • B) z σ)
      (-(Gsig (H + (y : ℂ) • B) z σ * B * Gsig (H + (y : ℂ) • B) z σ)) y := by
  have := OneStep_hasDerivAt_Gsig (hasDerivAt_line H B y) (hasDerivAt_const y z)
    (isHermitian_add_realSmul hH hB y) hz σ
  simpa using this

/-- First derivative of the loop functional along a Hermitian line. -/
private theorem OneStep_hasDerivAt_line0 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => gloop L W (H + (s : ℂ) • B) z I)
      (OneStep_J1 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gsig (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk L W) (OneStep_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

/-- Second derivative of the loop functional along a Hermitian line. -/
private theorem OneStep_hasDerivAt_line1 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => OneStep_J1 (H + (s : ℂ) • B) z (fun _ => B) I)
      (OneStep_J2 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gsig (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk L W) (OneStep_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

end LineDeriv

section SpecDeriv

variable {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

private theorem OneStep_hasDerivAt_specR (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gsig H (spectralZ E s) σ)
      (-(Gsig H (spectralZ E v) σ * OneStep_Dsp L W E σ * Gsig H (spectralZ E v) σ)) v := by
  have := OneStep_hasDerivAt_Gsig (hasDerivAt_const v H) (hasDerivAt_spectralZ E v) hH hv σ
  refine this.congr_deriv ?_
  cases σ <;> simp [OneStep_Dsp, spectralMSign]

private theorem OneStep_hasDerivAt_spec0 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (I : LoopIdx (Z2 L)) :
    HasDerivAt (fun s : ℝ => gloop L W H (spectralZ E s) I)
      (OneStep_J1 H (spectralZ E v) (OneStep_Dsp L W E) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gsig H (spectralZ E s) σ)
      (D := OneStep_Dsp L W E) (Ei := Eblk L W) (OneStep_hasDerivAt_specR hH hv) (I.σ.zip I.a))

private theorem OneStep_hasDerivAt_spec1 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (I : LoopIdx (Z2 L)) :
    HasDerivAt (fun s : ℝ => OneStep_J1 H (spectralZ E s) (OneStep_Dsp L W E) I)
      (OneStep_J2 H (spectralZ E v) (OneStep_Dsp L W E) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gsig H (spectralZ E s) σ)
      (D := OneStep_Dsp L W E) (Ei := Eblk L W) (OneStep_hasDerivAt_specR hH hv) (I.σ.zip I.a))

end SpecDeriv

end Loop

/-! ## 3. Norm and Lipschitz bounds for the jets of the loop functional -/

section LoopBounds

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem OneStep_norm_Eblk_le_one (a : Z2 L) : ‖Eblk L W a‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq L W a).trans ?_
  by_cases hW : W = 0
  · subst hW; simp
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hW
  have h1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  calc (W : ℝ)⁻¹ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 1 := one_pow 2

omit [NeZero W] in
private theorem OneStep_zip_length {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    (I.σ.zip I.a).length = I.length := by
  rw [List.length_zip]
  simp only [LoopIdx.WF] at hwf
  rw [hwf, min_self]
  rfl

private theorem OneStep_data {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    OneStep_Data (fun σ => Gsig H z σ) D (Eblk L W) η⁻¹ b :=
  ⟨by positivity, hb, fun σ => norm_Gsig_le_inv_eta L W hH hη hz σ, hD,
    fun a => OneStep_norm_Eblk_le_one a⟩

/-- `‖J1‖ ≤ N k K^{k+1} b`. -/
private theorem OneStep_norm_J1_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖OneStep_J1 H z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * η⁻¹ ^ (I.length + 1) * b) := by
  have h := OneStep_norm_w1_le (OneStep_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2‖ ≤ N k (k+1) K^{k+2} b²`. -/
private theorem OneStep_norm_J2_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖OneStep_J2 H z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b ^ 2) := by
  have h := OneStep_norm_w2_le (OneStep_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

private theorem OneStep_diff {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    OneStep_Diff (fun σ => Gsig H₁ z σ) (fun σ => Gsig H₂ z σ) D (Eblk L W) η⁻¹ b ‖H₁ - H₂‖ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  refine ⟨OneStep_data hH₁ hη hz hb hD, fun σ => norm_Gsig_le_inv_eta L W hH₂ hη hz σ,
    norm_nonneg _, fun σ => ?_⟩
  refine (OneStep_norm_Gsig_sub_le hH₁ hH₂ hzim σ).trans ?_
  have h1 : |z.im|⁻¹ ≤ η⁻¹ := inv_anti₀ hη hz
  have h2 : |z.im|⁻¹ ^ 2 ≤ η⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `‖J1(H₁) - J1(H₂)‖ ≤ N k (k+1) K^{k+2} b ‖H₁ - H₂‖`. -/
private theorem OneStep_norm_J1_sub_le {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖OneStep_J1 H₁ z D I - OneStep_J1 H₂ z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b * ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w1_sub_le (OneStep_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (OneStep_w1 (fun σ => Gsig H₁ z σ) D (Eblk L W) (I.σ.zip I.a)
      - OneStep_w1 (fun σ => Gsig H₂ z σ) D (Eblk L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2(H₁) - J2(H₂)‖ ≤ N k (k+1) (k+2) K^{k+3} b² ‖H₁ - H₂‖`. -/
private theorem OneStep_norm_J2_sub_le {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖OneStep_J2 H₁ z D I - OneStep_J2 H₂ z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3) * b ^ 2 *
          ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w2_sub_le (OneStep_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (OneStep_w2 (fun σ => Gsig H₁ z σ) D (Eblk L W) (I.σ.zip I.a)
      - OneStep_w2 (fun σ => Gsig H₂ z σ) D (Eblk L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

end LoopBounds

/-! ## 4. Counts: `Σ_c gvar_c ≤ 2N`, and `‖X‖ ≤ 2 Σ_c |ω_c|` -/

section Counts

private theorem OneStep_norm_single_le {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
    (a : ℂ) : ‖(Matrix.single i j a : Matrix n n ℂ)‖ ≤ ‖a‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => ?_
  have h : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.single i j a) v
      = EuclideanSpace.single i (a * v j) := by
    ext k
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.single_mulVec, Function.update_apply]
  rw [h, EuclideanSpace.single, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- The `ℓ²` operator norm is at most the sum of the moduli of the entries. -/
private theorem OneStep_norm_le_sum_entries {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => OneStep_norm_single_le i j _))

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OneStep_norm_Xentry_le (ω : Ω L W) (i j : Idx L W) :
    ‖Xentry L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

private theorem OneStep_sum_coord (f : Coord L W → ℝ) :
    ∑ c : Coord L W, f c = ∑ i : Idx L W, ∑ j : Idx L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|`, in block coordinates. -/
private theorem OneStep_norm_blockMat_Xmat_le (ω : Ω L W) :
    ‖blockMat (Xmat L W ω)‖ ≤ 2 * ∑ c : Coord L W, |ω c| := by
  refine (OneStep_norm_le_sum_entries _).trans ?_
  have hent : ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ‖blockMat (Xmat L W ω) p q‖
      = ∑ i : Idx L W, ∑ j : Idx L W, ‖Xentry L W ω i j‖ := by
    rw [← Equiv.sum_comp (splitEquiv L W).symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp (splitEquiv L W).symm]
    rfl
  rw [hent, OneStep_sum_coord]
  have hswap : ∑ i : Idx L W, ∑ j : Idx L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx L W, ∑ j : Idx L W, ‖Xentry L W ω i j‖
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => OneStep_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

private theorem OneStep_svar_le_one (i j : Idx L W) : svar L W i j ≤ 1 := by
  unfold svar
  split_ifs
  · have hW : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    have h1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
    have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    have h2 : (W : ℝ)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    linarith
  · exact zero_le_one

private theorem OneStep_gvar_le_svar (c : Coord L W) :
    (gvar L W c : ℝ) ≤ svar L W c.1 c.2.1 := by
  change (if c.1 = c.2.1 then svar L W c.1 c.2.1 else svar L W c.1 c.2.1 / 2) ≤ _
  have := svar_nonneg L W c.1 c.2.1
  split_ifs <;> linarith

private theorem OneStep_gvar_le_one (c : Coord L W) : (gvar L W c : ℝ) ≤ 1 :=
  (OneStep_gvar_le_svar c).trans (OneStep_svar_le_one _ _)

/-- The absolute row sums of `S^{(B)}` are at most `1` (valid for every `L`). -/
private theorem OneStep_sum_norm_SB_row (a : Z2 L) : ∑ b : Z2 L, ‖SB L a b‖ ≤ 1 := by
  have h : ∀ b : Z2 L, ‖SB L a b‖ = if a - b ∈ sbSupport L then (5 : ℝ)⁻¹ else 0 := by
    intro b
    rw [SB_apply, sbKernel]
    split_ifs <;> simp
  simp_rw [h]
  rw [show (∑ x : Z2 L, if a - x ∈ sbSupport L then (5 : ℝ)⁻¹ else 0)
      = ∑ c : Z2 L, if c ∈ sbSupport L then (5 : ℝ)⁻¹ else 0 from
    Equiv.sum_comp (Equiv.subLeft a) (fun c : Z2 L => if c ∈ sbSupport L then (5 : ℝ)⁻¹ else 0)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((sbSupport L).card : ℝ) ≤ 5 := by
    have h5 : (sbSupport L).card ≤ 5 := by
      unfold sbSupport
      exact Finset.card_le_five
    exact_mod_cast h5
  calc ((sbSupport L).card : ℝ) * (5 : ℝ)⁻¹ ≤ 5 * (5 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by norm_num

/-- The row sums of `svar` are at most `1`, for every `L`, `W ≥ 1`. -/
private theorem OneStep_sum_svar_row (i : Idx L W) : ∑ j : Idx L W, svar L W i j ≤ 1 := by
  have h1 : ∀ j : Idx L W,
      svar L W i j = ‖Svar L W (split L W i) (splitEquiv L W j)‖ := by
    intro j
    have h := svar_cast_eq_Spaper L W i j
    rw [Spaper_eq] at h
    have h' : (svar L W i j : ℂ) = Svar L W (split L W i) (splitEquiv L W j) := h
    rw [← h', Complex.norm_real, Real.norm_of_nonneg (svar_nonneg L W i j)]
  simp_rw [h1]
  rw [Fintype.sum_equiv (splitEquiv L W) _ (fun k => ‖Svar L W (split L W i) k‖)
    (fun _ => rfl)]
  generalize split L W i = s
  obtain ⟨a, α⟩ := s
  rw [Fintype.sum_prod_type]
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have h2 : ∀ b : Z2 L, ∑ β : Fin W × Fin W, ‖Svar L W (a, α) (b, β)‖ = ‖SB L a b‖ := by
    intro b
    simp only [Svar_apply, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  simp_rw [h2]
  exact OneStep_sum_norm_SB_row a

/-- `Σ_c gvar_c ≤ 2 N`, `N = |Idx|`. -/
private theorem OneStep_sum_gvar_le :
    ∑ c : Coord L W, (gvar L W c : ℝ) ≤ 2 * (Fintype.card (Idx L W) : ℝ) := by
  rw [OneStep_sum_coord]
  calc ∑ i : Idx L W, ∑ j : Idx L W, ((gvar L W (i, j, true) : ℝ) + (gvar L W (i, j, false) : ℝ))
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, 2 * svar L W i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h1 := OneStep_gvar_le_svar (L := L) (W := W) (i, j, true)
          have h2 := OneStep_gvar_le_svar (L := L) (W := W) (i, j, false)
          simp only at h1 h2
          linarith
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, svar L W i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ _i : Idx L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => OneStep_sum_svar_row i)
          zero_le_two
    _ = 2 * (Fintype.card (Idx L W) : ℝ) := by simp

/-- `|Idx| = (W L)²`. -/
private theorem OneStep_card_Idx : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
  simp [Idx, Z2, pow_two]

/-! ### First absolute moments of the Gaussian coordinates -/

private theorem OneStep_integrable_abs_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => |ω c|) (P L W) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (integrable_sq_coord L W c))
    (continuous_abs.comp (continuous_apply c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]

private theorem OneStep_integral_abs_coord_le (c : Coord L W) :
    ∫ ω : Ω L W, |ω c| ∂(P L W) ≤ 1 := by
  have hint : Integrable (fun ω : Ω L W => (1 + (ω c) ^ 2) / 2) (P L W) :=
    ((integrable_const (1 : ℝ)).add (integrable_sq_coord L W c)).div_const 2
  have hmono : ∫ ω : Ω L W, |ω c| ∂(P L W) ≤ ∫ ω : Ω L W, (1 + (ω c) ^ 2) / 2 ∂(P L W) := by
    refine integral_mono (OneStep_integrable_abs_coord c) hint fun ω => ?_
    nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]
  refine hmono.trans ?_
  rw [integral_div, integral_add (integrable_const _) (integrable_sq_coord L W c),
    integral_sq_coord]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := OneStep_gvar_le_one (L := L) (W := W) c
  linarith

private theorem OneStep_continuous_blockMat :
    Continuous (blockMat : Matrix (Idx L W) (Idx L W) ℂ →
      Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :=
  continuous_id.matrix_submatrix _ _

private theorem OneStep_integrable_sum_abs :
    Integrable (fun ω : Ω L W => 2 * ∑ c : Coord L W, |ω c|) (P L W) :=
  (integrable_finsetSum _ fun c _ => OneStep_integrable_abs_coord c).const_mul 2

private theorem OneStep_integrable_normX :
    Integrable (fun ω : Ω L W => ‖blockMat (Xmat L W ω)‖) (P L W) := by
  refine Integrable.mono' OneStep_integrable_sum_abs ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (continuous_norm.comp
      (OneStep_continuous_blockMat.comp (continuous_Xmat L W))).aestronglyMeasurable
  · rw [norm_norm]
    exact OneStep_norm_blockMat_Xmat_le ω

/-- `E ‖X‖ ≤ 4 N²` (in block coordinates), `N = (W L)²`. -/
private theorem OneStep_integral_normX_le :
    ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(P L W) ≤ 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by
  calc ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(P L W)
      ≤ ∫ ω : Ω L W, 2 * ∑ c : Coord L W, |ω c| ∂(P L W) :=
        integral_mono OneStep_integrable_normX OneStep_integrable_sum_abs
          fun ω => OneStep_norm_blockMat_Xmat_le ω
    _ = 2 * ∑ c : Coord L W, ∫ ω : Ω L W, |ω c| ∂(P L W) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => OneStep_integrable_abs_coord c]
    _ ≤ 2 * ∑ _c : Coord L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => OneStep_integral_abs_coord_le c)
          zero_le_two
    _ = 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have : Fintype.card (Coord L W) = 2 * (Fintype.card (Idx L W)) ^ 2 := by
          simp [Coord, Fintype.card_prod, Fintype.card_bool]
          ring
        rw [this]
        push_cast
        rw [OneStep_card_Idx]
        push_cast
        ring

end Counts

/-! ## 5. The derivative of `x ↦ E f(M + x X)` by Stein's identity -/

section Fine

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OneStep_blockMat_add_smul (A C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (A + y • C) = blockMat A + y • blockMat C := by
  ext p q
  simp [blockMat]

/-- The reindexed sample matrix `M + x X_ω`. -/
private def OneStep_Hs (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) (ω : Ω L W) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  blockMat (M + (x : ℂ) • Xmat L W ω)

private theorem OneStep_Hs_eq (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) (ω : Ω L W) :
    OneStep_Hs M x ω = blockMat M + (x : ℂ) • blockMat (Xmat L W ω) :=
  OneStep_blockMat_add_smul _ _ _

private theorem OneStep_Hs_herm {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (x : ℝ)
    (ω : Ω L W) : (OneStep_Hs M x ω).IsHermitian :=
  (isHermitian_add_realSmul hM (Xmat_isHermitian L W ω) x).submatrix _

private theorem OneStep_continuous_Hs (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) :
    Continuous (OneStep_Hs M x) :=
  OneStep_continuous_blockMat.comp
    (continuous_const.add ((continuous_Xmat L W).const_smul (x : ℂ)))

private theorem OneStep_Hs_update {M : Matrix (Idx L W) (Idx L W) ℂ} (x : ℝ) (ω : Ω L W)
    (c : Coord L W) (t : ℝ) :
    OneStep_Hs M x (Function.update ω c t) = OneStep_Hs M x ω
      + ((x * (t - ω c) : ℝ) : ℂ) • blockMat (coordinateMatrix L W c) := by
  rw [OneStep_Hs, OneStep_Hs, Xmat_update]
  ext p q
  simp only [blockMat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private theorem OneStep_continuous_Gsig {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hf : Continuous f)
    (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun v => Gsig (f v) z σ := by
  cases σ
  · exact continuous_green_of_isHermitian hf hh (by simpa using hz)
  · exact continuous_green_of_isHermitian hf hh hz

section Cont

variable {V : Type*} [TopologicalSpace V] {f : V → Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
  (hf : Continuous f) (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  (I : LoopIdx (Z2 L)) (D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
include hf hh hz

private theorem OneStep_continuous_gloop : Continuous fun v => gloop L W (f v) z I :=
  (continuous_matrixTrace L W).comp
    (OneStep_continuous_w0 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

private theorem OneStep_continuous_J1 : Continuous fun v => OneStep_J1 (f v) z D I :=
  (continuous_matrixTrace L W).comp
    (OneStep_continuous_w1 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

private theorem OneStep_continuous_J2 : Continuous fun v => OneStep_J2 (f v) z D I :=
  (continuous_matrixTrace L W).comp
    (OneStep_continuous_w2 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

end Cont

/-- Linearity of the first jet in the direction: `X = Σ_c ω_c C_c`. -/
private theorem OneStep_J1_Xmat (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) (ω : Ω L W) :
    OneStep_J1 H z (fun _ => blockMat (Xmat L W ω)) I
      = ∑ c : Coord L W, (ω c : ℂ) *
          OneStep_J1 H z (fun _ => blockMat (coordinateMatrix L W c)) I := by
  have hX : (fun _ : Bool => blockMat (Xmat L W ω))
      = ∑ c : Coord L W, (ω c) • (fun _ : Bool => blockMat (coordinateMatrix L W c)) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply]
    ext p q
    rw [Xmat_eq_sum_coordinates]
    simp [blockMat, Matrix.sum_apply]
  have hlin := map_sum (OneStep_w1Lin (fun σ => Gsig H z σ) (Eblk L W) (I.σ.zip I.a))
    (fun c : Coord L W => (ω c) • (fun _ : Bool => blockMat (coordinateMatrix L W c)))
    Finset.univ
  simp only [map_smul] at hlin
  unfold OneStep_J1
  rw [hX]
  change Matrix.trace ((OneStep_w1Lin (fun σ => Gsig H z σ) (Eblk L W) (I.σ.zip I.a)) _) = _
  rw [hlin, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul]
  rfl

/-- A Gaussian coordinate times a bounded continuous observable is integrable. -/
private theorem OneStep_integrable_coord_mul (c : Coord L W) {g : Ω L W → ℂ}
    (hg : Continuous g) {C : ℝ} (hb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω L W => (ω c : ℂ) * g ω) (P L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (P L W) := (measurable_pi_apply c).aemeasurable
  have hg' : Integrable (fun x : ℝ => x) ((P L W).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gvar L W c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (P L W) :=
    (integrable_map_measure hg'.aestronglyMeasurable hf).1 hg'
  have h := hcoord.ofReal.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa [Complex.real_smul, mul_comm] using h

section SteinStep

variable {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  {I : LoopIdx (Z2 L)} (hwf : I.WF)
include hM hz hwf

/-- The coordinate Stein identity, for the first jet along the coordinate direction. -/
private theorem OneStep_stein_coord (x : ℝ) (c : Coord L W) :
    ∫ ω : Ω L W, (ω c : ℂ) *
        OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)
      = ((gvar L W c : ℝ) : ℂ) * ((x : ℂ) * ∫ ω : Ω L W,
        OneStep_J2 (OneStep_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
    := by
  set Cb := blockMat (coordinateMatrix L W c) with hCb
  have hCh : Cb.IsHermitian := (coordinateMatrix_isHermitian L W c).submatrix _
  set g : Ω L W → ℂ := fun ω => OneStep_J1 (OneStep_Hs M x ω) z (fun _ => Cb) I with hg
  set g' : Ω L W → ℂ := fun ω => (x : ℂ) * OneStep_J2 (OneStep_Hs M x ω) z (fun _ => Cb) I
    with hg'
  have hgc : Continuous g :=
    OneStep_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _
  have hg'c : Continuous g' :=
    continuous_const.mul
      (OneStep_continuous_J2 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _)
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C := ⟨_, fun ω =>
    OneStep_norm_J1_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl) hwf⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C := ⟨|x| * _, fun ω => by
    rw [hg', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (OneStep_norm_J2_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb)
        (fun _ => le_rfl) hwf) (abs_nonneg _)⟩
  have hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    have hAh := OneStep_Hs_herm hM x ω
    have hφ := OneStep_hasDerivAt_line1 hAh hCh hz I (x * (ω c - ω c))
    have hh : HasDerivAt (fun t : ℝ => x * (t - ω c)) x (ω c) := by
      simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul x
    have hcomp := hφ.scomp (ω c) hh
    have hfun : (fun t : ℝ => g (Function.update ω c t)) =
        ((fun s : ℝ => OneStep_J1 (OneStep_Hs M x ω + (s : ℂ) • Cb) z (fun _ => Cb) I) ∘
          fun t : ℝ => x * (t - ω c)) := by
      funext t
      simp only [Function.comp, hg, OneStep_Hs_update, hCb]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    simp [hg']
  have h := GaussianProduct.stein (gvar L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : P L W = GaussianProduct.law (gvar L W) := rfl
  rw [← hlaw] at h
  simp only [Complex.real_smul] at h
  rw [h, hg', integral_const_mul]

/-- **The derivative of `x ↦ E f(M + x X)`**: `x Σ_c gvar_c E ∂²_c f(M + x X)`, by Stein. -/
private theorem OneStep_hasDerivAt_F (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ω : Ω L W, gloop L W (OneStep_Hs M y ω) z I ∂(P L W))
      ((x : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M x ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)) x := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hcontgl : ∀ y : ℝ, Continuous fun ω : Ω L W => gloop L W (OneStep_Hs M y ω) z I :=
    fun y => OneStep_continuous_gloop (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz I
  have hint : ∀ y : ℝ, Integrable (fun ω : Ω L W => gloop L W (OneStep_Hs M y ω) z I) (P L W) :=
    fun y => Integrable.of_bound (hcontgl y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude L W (OneStep_Hs_herm hM y ω) hη le_rfl I hwf)
  have hJc : ∀ c : Coord L W, Continuous fun ω : Ω L W =>
      OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I :=
    fun c => OneStep_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _
  have hF'cont : Continuous fun ω : Ω L W =>
      OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat (Xmat L W ω)) I := by
    simp only [OneStep_J1_Xmat]
    exact continuous_finsetSum _ fun c _ =>
      (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc c)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P L W)
    (s := Set.univ) (x₀ := x)
    (F := fun y ω => gloop L W (OneStep_Hs M y ω) z I)
    (F' := fun y ω => OneStep_J1 (OneStep_Hs M y ω) z (fun _ => blockMat (Xmat L W ω)) I)
    (bound := fun ω => ((Fintype.card (BlockIndex L W) : ℝ) *
      ((I.length : ℝ) * |z.im|⁻¹ ^ (I.length + 1))) * ‖blockMat (Xmat L W ω)‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hcontgl y).aestronglyMeasurable)
    (hint x) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω y _ =>
      (OneStep_norm_J1_le (OneStep_Hs_herm hM y ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl)
        hwf).trans (le_of_eq (by ring)))
    (OneStep_integrable_normX.const_mul _)
    (Filter.Eventually.of_forall fun ω y _ => by
      have hXb : (blockMat (Xmat L W ω)).IsHermitian := (Xmat_isHermitian L W ω).submatrix _
      have := OneStep_hasDerivAt_line0 hMb hXb hz I y
      simpa only [OneStep_Hs_eq] using this)
  refine hD.congr_deriv ?_
  simp only [OneStep_J1_Xmat]
  rw [integral_finsetSum _ fun c _ => OneStep_integrable_coord_mul c (hJc c)
    (fun ω => OneStep_norm_J1_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg _)
      (fun _ => le_rfl) hwf)]
  simp_rw [OneStep_stein_coord hM hz hwf x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end SteinStep

end Fine

/-! ## 6. The space step: `E f(M + τ X) - f(M) - τ² g(M)` -/

section SpaceStep

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OneStep_card_Block :
    (Fintype.card (BlockIndex L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
  rw [card_BlockIndex, mul_comm]

/-- The coordinate directions have norm at most `2` (in block coordinates). -/
private theorem OneStep_norm_Cb_le (c : Coord L W) : ‖blockMat (coordinateMatrix L W c)‖ ≤ 2 := by
  have h := OneStep_norm_blockMat_Xmat_le (L := L) (W := W) (Pi.single c (1 : ℝ))
  have h1 : ∑ c' : Coord L W, |(Pi.single c (1 : ℝ) : Coord L W → ℝ) c'| = 1 := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [h1] at h
  simpa [coordinateMatrix] using h

/-- The `g`-part: `g_u(M) = ½ Σ_c gvar_c ∂²_c f(M)`. -/
private def OneStep_g (z : ℂ) (I : LoopIdx (Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
    OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I

variable {M : Matrix (Idx L W) (Idx L W) ℂ} {z : ℂ} {I : LoopIdx (Z2 L)}

/-- The Lipschitz estimate of one coordinate second jet along the Gaussian sample. -/
private theorem OneStep_coord_sub_le (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) (c : Coord L W) (y : ℝ) (ω : Ω L W) :
    ‖OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I‖
      ≤ (((Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4) * |y|) * ‖blockMat (Xmat L W ω)‖ := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have h := OneStep_norm_J2_sub_le (OneStep_Hs_herm hM y ω) hMb hη hz (D := fun _ =>
    blockMat (coordinateMatrix L W c)) (b := 2) zero_le_two (fun _ => OneStep_norm_Cb_le c) hwf
  have hd : ‖OneStep_Hs M y ω - blockMat M‖ = |y| * ‖blockMat (Xmat L W ω)‖ := by
    rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hd] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- The key size estimate: the derivative of `ψ(y) = F(y) - F(0) - y² g(M)` is `O(y²)`. -/
private theorem OneStep_psi_deriv_le (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {y : ℝ} (hy : 0 ≤ y) :
    ‖(y : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)
      - ((2 * y : ℝ) : ℂ) * OneStep_g z I M‖
      ≤ (32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) * y ^ 2 := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  set C₃ : ℝ := (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hcont : ∀ c : Coord L W, Continuous fun ω : Ω L W =>
      OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I :=
    fun c => OneStep_continuous_J2 (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz' I _
  have hint : ∀ c : Coord L W, Integrable (fun ω : Ω L W =>
      OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I) (P L W) :=
    fun c => Integrable.of_bound (hcont c).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        OneStep_norm_J2_le (OneStep_Hs_herm hM y ω) hη hz (norm_nonneg _) (fun _ => le_rfl) hwf)
  -- one coordinate
  have hone : ∀ c : Coord L W,
      ‖(∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I‖
      ≤ (C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
    intro c
    have hsub : (∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I
        = ∫ ω : Ω L W, (OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I
          - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) ∂(P L W) := by
      rw [integral_sub (hint c) (integrable_const _)]
      simp
    rw [hsub]
    refine (norm_integral_le_of_norm_le ((OneStep_integrable_normX.const_mul (C₃ * |y|)))
      (Filter.Eventually.of_forall fun ω =>
        OneStep_coord_sub_le hM hη hz hwf c y ω)).trans ?_
    rw [integral_const_mul, abs_of_nonneg hy]
    have := OneStep_integral_normX_le (L := L) (W := W)
    rw [← OneStep_card_Idx] at this
    calc C₃ * y * ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(P L W)
        ≤ C₃ * y * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hsum : ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) * ∫ ω : Ω L W, OneStep_J2
        (OneStep_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)
      - 2 * OneStep_g z I M
      = ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) := by
    simp only [OneStep_g, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmain : (y : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) * ∫ ω : Ω L W, OneStep_J2
        (OneStep_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)
      - ((2 * y : ℝ) : ℂ) * OneStep_g z I M
      = (y : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) := by
    rw [← hsum]
    push_cast
    ring
  rw [hmain, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  have hsn : ‖∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
      ≤ (2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Coord L W, ‖((gvar L W c : ℝ) : ℂ) *
          ((∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
            (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
          - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
        ≤ ∑ c : Coord L W, (gvar L W c : ℝ) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gvar L W c).coe_nonneg]
            exact mul_le_mul_of_nonneg_left (hone c) (gvar L W c).coe_nonneg
      _ = (∑ c : Coord L W, (gvar L W c : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right OneStep_sum_gvar_le (by positivity)
  calc y * ‖∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W))
        - OneStep_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
      ≤ y * ((2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsn hy
    _ = _ := by rw [hC₃]; ring

/-- **The space step** (by Stein's identity): `‖E f(M + τ X) - f(M) - τ² g(M)‖ ≤ (Λ'/3) τ³`. -/
private theorem OneStep_space_step (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) z I ∂(P L W)) - gloop L W (blockMat M) z I
        - ((τ ^ 2 : ℝ) : ℂ) * OneStep_g z I M‖
      ≤ ((32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) / 3)
        * τ ^ 3 := by
  set Λ : ℝ := 32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
    ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3)) with hΛ
  set F : ℝ → ℂ := fun y => ∫ ω : Ω L W, gloop L W (OneStep_Hs M y ω) z I ∂(P L W) with hF
  have hF0 : F 0 = gloop L W (blockMat M) z I := by
    simp [hF, OneStep_Hs]
  set ψ : ℝ → ℂ := fun y => F y - F 0 - ((y ^ 2 : ℝ) : ℂ) * OneStep_g z I M with hψ
  set ψ' : ℝ → ℂ := fun y => (y : ℂ) * ∑ c : Coord L W, ((gvar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(P L W)
      - ((2 * y : ℝ) : ℂ) * OneStep_g z I M with hψ'
  have hd : ∀ y : ℝ, HasDerivAt ψ (ψ' y) y := by
    intro y
    have h1 := ((OneStep_hasDerivAt_F hM hz' hwf y).sub_const (F 0)).sub
      ((((hasDerivAt_pow 2 y).ofReal_comp)).mul_const (OneStep_g z I M))
    refine h1.congr_deriv ?_
    simp only [hψ']
    push_cast
    ring
  have hcont : ContinuousOn ψ (Set.Icc 0 τ) := fun y _ => (hd y).continuousAt.continuousWithinAt
  have hB : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Λ / 3 * y ^ 3) (Λ * y ^ 2) y := by
    intro y
    refine ((hasDerivAt_pow 3 y).const_mul (Λ / 3)).congr_deriv ?_
    push_cast
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (f' := ψ') (a := 0)
    (b := τ) hcont (fun y _ => (hd y).hasDerivWithinAt)
    (by simp [hψ]) hB
    (fun y hy => OneStep_psi_deriv_le hM hz' hη hz hwf hy.1)
  have := key (x := τ) ⟨hτ, le_rfl⟩
  simp only [hψ] at this
  rw [hF0] at this
  exact this

end SpaceStep

/-! ## 7. The time step, the closure of the constant, and the theorem -/

section TimeStep

/-- Second-order Taylor bound (the fencing lemma twice). -/
private theorem OneStep_taylor2 {f f₁ f₂ : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
    (h1 : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (h2 : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x) (hB : ∀ x ∈ Set.Icc a b, ‖f₂ x‖ ≤ B) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f₁ a‖ ≤ B * (b - a) ^ 2 / 2 := by
  have hc1 : ContinuousOn f₁ (Set.Icc a b) := fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have hs1 := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f₁) (f' := f₂) (C := B) hc1
    (fun x hx => (h2 x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (fun x hx => hB x ⟨hx.1, hx.2.le⟩)
  set ψ : ℝ → ℂ := fun x => f x - f a - ((x - a : ℝ) : ℂ) * f₁ a with hψ
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt ψ (f₁ x - f₁ a) x := by
    intro x hx
    have h := ((h1 x hx).sub_const (f a)).sub
      ((((hasDerivAt_id x).sub_const a).ofReal_comp).mul_const (f₁ a))
    refine h.congr_deriv ?_
    simp
  have hB' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => B * (x - a) ^ 2 / 2) (B * (x - a)) x := by
    intro x
    refine ((((hasDerivAt_id x).sub_const a).pow 2).const_mul B |>.div_const 2).congr_deriv ?_
    simp
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ)
    (f' := fun x => f₁ x - f₁ a) (a := a) (b := b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (by simp [hψ]) hB'
    (fun x hx => by simpa [mul_comm] using hs1 x ⟨hx.1, hx.2.le⟩)
  exact key ⟨hab, le_rfl⟩

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem OneStep_norm_Dsp_le {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    ‖OneStep_Dsp L W E σ‖ ≤ 1 := by
  have hm : ‖spectralMSign E σ‖ = 1 := by
    cases σ <;> simp [spectralMSign, norm_spectralM hE.le]
  unfold OneStep_Dsp
  rw [norm_smul, hm, one_mul]
  exact OneStep_norm_one_le

private theorem OneStep_eta_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (spectralM_im_pos hE)

/-- **The time step**: Taylor expansion of `v ↦ f_v(A)` at fixed `A`. -/
private theorem OneStep_time_step {A : Matrix (Idx L W) (Idx L W) ℂ} (hA : A.IsHermitian)
    {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖gloop L W (blockMat A) (spectralZ E (u + Δ)) I - gloop L W (blockMat A) (spectralZ E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat A) (spectralZ E u) (OneStep_Dsp L W E) I‖
      ≤ ((Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat A).IsHermitian := hA.submatrix _
  have hη := OneStep_eta_pos hE hu1
  have hv : ∀ v ∈ Set.Icc u (u + Δ), (spectralZ E v).im ≠ 0 := fun v hv => by
    rw [spectralZ_im]
    exact (mul_pos (by linarith [hv.2]) (spectralM_im_pos hE)).ne'
  have hvη : ∀ v ∈ Set.Icc u (u + Δ), etaT E (u + Δ) ≤ |(spectralZ E v).im| :=
    fun v hv => spectralZ_im_gap hE hu1 hv
  have h := OneStep_taylor2 (f := fun v => gloop L W (blockMat A) (spectralZ E v) I)
    (f₁ := fun v => OneStep_J1 (blockMat A) (spectralZ E v) (OneStep_Dsp L W E) I)
    (f₂ := fun v => OneStep_J2 (blockMat A) (spectralZ E v) (OneStep_Dsp L W E) I)
    (a := u) (b := u + Δ)
    (B := (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
      (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) (by linarith)
    (fun v hv' => OneStep_hasDerivAt_spec0 hAb (hv v hv') I)
    (fun v hv' => OneStep_hasDerivAt_spec1 hAb (hv v hv') I)
    (fun v hv' => by
      have := OneStep_norm_J2_le hAb hη (hvη v hv') zero_le_one (D := OneStep_Dsp L W E)
        (OneStep_norm_Dsp_le hE) hwf
      simpa using this)
  simpa using h

end TimeStep

section Assembly

/-- The closure of the constant: `⅔·16·… ≤ 16 (k+3)⁴ N⁴ (1 + q)^{k+4}` with `q = η⁻¹`. -/
private theorem OneStep_closure (k : ℕ) {N q : ℝ} (hN : 1 ≤ N) (hq : 0 ≤ q) :
    32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      + (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
    ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK : (1 : ℝ) ≤ 1 + q := by linarith
  have hq3 : q ^ (k + 3) ≤ (1 + q) ^ (k + 3) := pow_le_pow_left₀ hq (by linarith) _
  have hq2 : q ^ (k + 2) ≤ (1 + q) ^ (k + 3) :=
    (pow_le_pow_left₀ hq (by linarith) _).trans (pow_le_pow_right₀ hK (by omega))
  have h4 : (1 + q) ^ (k + 3) ≤ (1 + q) ^ (k + 4) := pow_le_pow_right₀ hK (by omega)
  have ha3 : (k : ℝ) * (k + 1) * (k + 2) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have ha2 : (k : ℝ) * (k + 1) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have hN4 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hN1 : N ≤ N ^ 4 := by nlinarith [pow_le_pow_right₀ hN (show 1 ≤ 4 by norm_num)]
  have hP : 0 ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3) := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hq0 : 0 ≤ q ^ (k + 3) := by positivity
  have e1 : 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      ≤ (32 / 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have : (k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha3 hq3 hq0 (by positivity)
    calc 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
        = (32 / 3) * N ^ 4 * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) := by ring
      _ ≤ (32 / 3) * N ^ 4 * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) := by gcongr
      _ = _ := by ring
  have e2 : (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
      ≤ (9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have h5 : (k : ℝ) * (k + 1) * q ^ (k + 2) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha2 hq2 (by positivity) (by positivity)
    have h6 : N * (1 / 2 + 4 * N ^ 2) ≤ (9 / 2) * N ^ 4 := by nlinarith
    calc (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
        = (N * (1 / 2 + 4 * N ^ 2)) * ((k : ℝ) * (k + 1) * q ^ (k + 2)) := by ring
      _ ≤ ((9 / 2) * N ^ 4) * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) :=
          mul_le_mul h6 h5 (by positivity) (by positivity)
      _ = _ := by ring
  have e3 : (32 / 3 + 9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3))
      ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
    have h7 : ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)
        ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4) := by gcongr
    have h8 : 3 * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4))
        ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h7, h8]
  linarith

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The mixed second derivative along a coordinate line, as the second jet. -/
private theorem OneStep_deriv_deriv {M C : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (hC : C.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    deriv (deriv (fun y : ℝ => gloop L W (blockMat (M + (y : ℂ) • C)) z I)) 0
      = OneStep_J2 (blockMat M) z (fun _ => blockMat C) I := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hCb : (blockMat C).IsHermitian := hC.submatrix _
  simp only [OneStep_blockMat_add_smul]
  have h1 : deriv (fun y : ℝ => gloop L W (blockMat M + (y : ℂ) • blockMat C) z I)
      = fun y : ℝ => OneStep_J1 (blockMat M + (y : ℂ) • blockMat C) z (fun _ => blockMat C) I := by
    funext y
    exact (OneStep_hasDerivAt_line0 hMb hCb hz I y).deriv
  rw [h1]
  simpa using (OneStep_hasDerivAt_line1 hMb hCb hz I 0).deriv

/-- **The one-step expansion with its envelope** (`OneStepEnvelope`).  The proof
splits the error into the space step at fixed time `u` (`OneStep_space_step`, by Stein) and the time
step at fixed sample (`OneStep_time_step`, by Taylor), and closes the constant with
`OneStep_closure`. -/
theorem oneStepEnvelope : OneStepEnvelope := by
  intro L W _ _ E hE I hwf u Δ hu hΔ hu1 M hM
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaT E (u + Δ) := OneStep_eta_pos hE hu1
  have hzu : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  have hηu : etaT E (u + Δ) ≤ |(spectralZ E u).im| :=
    spectralZ_im_gap hE hu1 ⟨le_rfl, by linarith⟩
  have hηv : etaT E (u + Δ) ≤ |(spectralZ E (u + Δ)).im| :=
    spectralZ_im_gap (s := u) hE hu1 ⟨by linarith, le_rfl⟩
  have hzv : (spectralZ E (u + Δ)).im ≠ 0 := fun h => absurd hηv (by rw [h]; simpa using hη)
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  set c₁ : ℝ := (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (etaT E (u + Δ))⁻¹ ^ (I.length + 2)) with hc₁
  -- the generator, in the jets
  have hgen : genMat E u M I = OneStep_g (spectralZ E u) I M
      + OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I := by
    unfold genMat OneStep_g
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [OneStep_deriv_deriv hM (coordinateMatrix_isHermitian L W c) hzu I]
    · exact (OneStep_hasDerivAt_spec0 hMb hzu I).deriv
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (spectralZ E v).im ≠ 0 → Integrable
      (fun ω : Ω L W => gloop L W (OneStep_Hs M τ ω) (spectralZ E v) I) (P L W) := fun v hv => by
    have hv' : 0 < |(spectralZ E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (OneStep_continuous_gloop (OneStep_continuous_Hs M τ)
      (OneStep_Hs_herm hM τ) hv I).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude L W (OneStep_Hs_herm hM τ ω) hv' le_rfl I hwf)
  -- the space step
  have hT2 := OneStep_space_step hM hzu hη hηu hwf hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(P L W))
      - (∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I ∂(P L W))
      - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω L W, ‖gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I
        - gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat (Xmat L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat L W ω).IsHermitian :=
        isHermitian_add_realSmul hM (Xmat_isHermitian L W ω) τ
      have h1 := OneStep_time_step hA hE hΔ hu1 hwf
      have h2 := OneStep_norm_J1_sub_le (OneStep_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := OneStep_Dsp L W E) (OneStep_norm_Dsp_le hE) hwf
      have hd : ‖OneStep_Hs M τ ω - blockMat M‖ = τ * ‖blockMat (Xmat L W ω)‖ := by
        rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I
          = (gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E (u + Δ)) I
            - gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u)
              (OneStep_Dsp L W E) I)
            + (Δ : ℂ) * (OneStep_J1 (OneStep_Hs M τ ω) (spectralZ E u) (OneStep_Dsp L W E) I
              - OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I) := by
        simp only [OneStep_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (OneStep_J1 (OneStep_Hs M τ ω) (spectralZ E u) (OneStep_Dsp L W E) I
          - OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I)‖
          ≤ Δ * (c₁ * (τ * ‖blockMat (Xmat L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E (u + Δ)) I
            - gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u)
              (OneStep_Dsp L W E) I‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat (Xmat L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(P L W))
        - (∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I ∂(P L W))
        - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I
        = ∫ ω : Ω L W, (gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I)
            ∂(P L W) := by
      have i12 : Integrable (fun ω : Ω L W => gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I) (P L W) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat (Xmat L W ω)‖) (P L W) :=
      (integrable_const _).add (OneStep_integrable_normX.const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) (OneStep_integrable_normX.const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := OneStep_integral_normX_le (L := L) (W := W)
    rw [← OneStep_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(P L W)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω L W, gloop L W (blockMat (M + (Real.sqrt Δ : ℂ) • Xmat L W ω))
        (spectralZ E (u + Δ)) I ∂(P L W)) - gloop L W (blockMat M) (spectralZ E u) I
        - (Δ : ℂ) * genMat E u M I
      = ((∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I ∂(P L W))
          - gloop L W (blockMat M) (spectralZ E u) I
          - ((τ ^ 2 : ℝ) : ℂ) * OneStep_g (spectralZ E u) I M)
        + ((∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(P L W))
          - (∫ ω : Ω L W, gloop L W (OneStep_Hs M τ ω) (spectralZ E u) I ∂(P L W))
          - (Δ : ℂ) * OneStep_J1 (blockMat M) (spectralZ E u) (OneStep_Dsp L W E) I) := by
    rw [hgen, hτ2]
    simp only [OneStep_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, OneStep_card_Idx, OneStep_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ 2 :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := OneStep_closure I.length hN (inv_nonneg.mpr hη.le)
  unfold envConst
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, OneStep_card_Block]
  calc _ = (32 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 3 * (((W * L) ^ 2 : ℕ) : ℝ) *
            ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * (etaT E (u + Δ))⁻¹ ^ (I.length + 3))
            / 3
          + ((((W * L) ^ 2 : ℕ) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
            (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * (1 / 2 + 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Assembly

end RBM.Path
