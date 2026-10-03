/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.OneStep
import RBM2D.Universality.GUEPhase.Generator
import RBM2D.Universality.GUEPhase.Markov
import RBM2D.Endpoints

/-!
# The one-step drift of the GUE-phase grid (`d = 2`)

The GUE analogue of the band statements `oneStepEnvelope` (`Path/OneStep.lean`) and
`condExp_loop_drift` (`Path/LoopStep.lean`).

## What is proved

* `oneStepEnvelopeGUE`: for Hermitian `M`, one GUE increment `√Δ X` with `X ~ gueP L W` satisfies
  `‖E 𝓛_{u+Δ}(M + √Δ X) - 𝓛_u(M) - Δ · genMatGUE‖ ≤ envConst · Δ^{3/2}`, with the envelope
  constant `envConst` of the band case.
* `gueH_succ`: the one-step recursion `gueH (k+1) = gueH k + √(Δ/N) · seqXmat (ω (k+1))`.
* `condExp_loop_step_gue`: the GUE analogue of `condExp_loop_step`; given `filt d k`, the
  conditional expectation of the loop observable at step `k + 1` is its integral over one GUE
  increment `√Δ Xmat`, `Xmat ~ gueP`, added to the `gueH k ω`.
* `condExp_loop_drift_gue`: the conditional drift of the loop observable along `gueH`, under
  `Pgue d`, given `filt d k`.

## Proof (`d = 2`)

The proof is the direct band argument with the coordinate law `P L W ↦ gueP L W` and
`gvar ↦ gueVar`: the space step by Stein's identity for the product law
`GaussianProduct.law (gueVar L W) = gueP L W` and the fencing lemma, the time step by Taylor, the
jets of a word of resolvent factors.  Every count of `Path/OneStep.lean` holds for `gueVar`
with the same constants (`gueVar_c ≤ N⁻¹ ≤ 1`, `Σ_c gueVar_c = N + 1 ≤ 2 N`, `E‖X‖ ≤ 4 N²`), so
the band envelope constant `envConst` is kept and no larger envelope is needed.  The generator of
the space step is `½ Σ_c gueVar_c ∂²_c`, i.e. `genMatGUE` (`Universality/GUEPhase/Generator.lean`).

The conditional step is the band argument of `condExp_loop_step` (`Path/LoopStep.lean`) with
`pathP ↦ Pgue d`, `pathH ↦ gueH`, `condExp_freeze ↦ gueCondExp_freeze` and the law of the unit
slice transferred to `gueP`: under `gueUnit d` the matrix `(1/√N) · slice d n x` has the law
`gueP`, and `√(Δ/N) · seqXmat d n x = √Δ · Xmat ((1/√N) • slice d n x)`.

The private helpers copy those of `OneStep.lean` and `LoopStep.lean` under the prefix `Drift_`,
with `P L W ↦ gueP L W`, `gvar ↦ gueVar`, `genMat ↦ genMatGUE`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal Matrix.Norms.L2Operator
open RBM.Endpoints (gueP gueVar)

/-! ## 1. Generic jets of a word of resolvent factors

A word `∏ᵢ R_{σᵢ} E_{aᵢ}` whose resolvent factors have the jets `R`, `r1 = -R D R`,
`r2 = 2 R D R D R` along a line has the jets `w0`, `w1`, `w2` below (Leibniz recursion). -/

section Jets

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- The word `∏ R_{σᵢ} E_{aᵢ}` (as in `gloopProd`). -/
private def Drift_w0 (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : Matrix n n ℂ :=
  l.foldr (fun p M => R p.1 * Ei p.2 * M) 1

/-- First jet of a resolvent factor. -/
private def Drift_r1 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  -(R σ * D σ * R σ)

/-- Second jet of a resolvent factor. -/
private def Drift_r2 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ

/-- First derivative of the word. -/
private def Drift_w1 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (Drift_r1 R D p.1 * Ei p.2) * Drift_w0 R Ei l
      + (R p.1 * Ei p.2) * Drift_w1 R D Ei l

/-- Second derivative of the word. -/
private def Drift_w2 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (Drift_r2 R D p.1 * Ei p.2) * Drift_w0 R Ei l
      + ((Drift_r1 R D p.1 * Ei p.2) * Drift_w1 R D Ei l
          + (Drift_r1 R D p.1 * Ei p.2) * Drift_w1 R D Ei l)
      + (R p.1 * Ei p.2) * Drift_w2 R D Ei l

private theorem Drift_w0_cons (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) (p : Bool × ι)
    (l : List (Bool × ι)) :
    Drift_w0 R Ei (p :: l) = R p.1 * Ei p.2 * Drift_w0 R Ei l := rfl

private theorem Drift_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

private theorem Drift_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem Drift_norm_sub_mul_le {A₁ A₂ B₁ B₂ : Matrix n n ℂ} {a₂ b₁ da db : ℝ}
    (hA₂ : ‖A₂‖ ≤ a₂) (hB₁ : ‖B₁‖ ≤ b₁) (hdA : ‖A₁ - A₂‖ ≤ da) (hdB : ‖B₁ - B₂‖ ≤ db) :
    ‖A₁ * B₁ - A₂ * B₂‖ ≤ da * b₁ + a₂ * db := by
  have h : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by noncomm_ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (Drift_nmul hdA hB₁) (Drift_nmul hA₂ hdB))

private theorem Drift_norm_add3 (X Y Z : Matrix n n ℂ) :
    ‖X + (Y + Y) + Z‖ ≤ ‖X‖ + 2 * ‖Y‖ + ‖Z‖ := by
  have h1 := norm_add_le (X + (Y + Y)) Z
  have h2 := norm_add_le X (Y + Y)
  have h3 := norm_add_le Y Y
  linarith

/-- The hypotheses of the norm bounds on the jets of a word. -/
private structure Drift_Data (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b : ℝ) : Prop where
  hK : 0 ≤ K
  hb : 0 ≤ b
  hR : ∀ σ, ‖R σ‖ ≤ K
  hD : ∀ σ, ‖D σ‖ ≤ b
  hE : ∀ a, ‖Ei a‖ ≤ 1

/-- The hypotheses of the Lipschitz bounds: a second factor family at distance `K² δ`. -/
private structure Drift_Diff (R₁ R₂ D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b δ : ℝ) : Prop where
  d₁ : Drift_Data R₁ D Ei K b
  hR₂ : ∀ σ, ‖R₂ σ‖ ≤ K
  hδ : 0 ≤ δ
  hdiff : ∀ σ, ‖R₁ σ - R₂ σ‖ ≤ K ^ 2 * δ

section Bounds

variable {R D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b : ℝ}

private theorem Drift_norm_r1_le (h : Drift_Data R D Ei K b) (σ : Bool) :
    ‖Drift_r1 R D σ‖ ≤ K * b * K := by
  rw [Drift_r1, norm_neg]
  exact Drift_nmul (Drift_nmul (h.hR σ) (h.hD σ)) (h.hR σ)

private theorem Drift_norm_r2_le (h : Drift_Data R D Ei K b) (σ : Bool) :
    ‖Drift_r2 R D σ‖ ≤ 2 * (K * b * K * b * K) := by
  rw [Drift_r2]
  have h5 := Drift_nmul (Drift_nmul (Drift_nmul (Drift_nmul (h.hR σ) (h.hD σ))
    (h.hR σ)) (h.hD σ)) (h.hR σ)
  calc ‖R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ‖
      ≤ ‖R σ * D σ * R σ * D σ * R σ‖ + ‖R σ * D σ * R σ * D σ * R σ‖ := norm_add_le _ _
    _ ≤ K * b * K * b * K + K * b * K * b * K := add_le_add h5 h5
    _ = 2 * (K * b * K * b * K) := by ring

private theorem Drift_norm_w0_le (h : Drift_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖Drift_w0 R Ei l‖ ≤ K ^ l.length := by
  induction l with
  | nil => simpa [Drift_w0] using Drift_norm_one_le
  | cons p l ih =>
      rw [Drift_w0_cons, List.length_cons, pow_succ]
      calc ‖R p.1 * Ei p.2 * Drift_w0 R Ei l‖ ≤ (K * 1) * K ^ l.length :=
            Drift_nmul (Drift_nmul (h.hR p.1) (h.hE p.2)) ih
        _ = K ^ l.length * K := by ring

private theorem Drift_norm_w1_le (h : Drift_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖Drift_w1 R D Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * b := by
  induction l with
  | nil => simp [Drift_w1]
  | cons p l ih =>
      rw [Drift_w1, List.length_cons]
      have h1 : ‖(Drift_r1 R D p.1 * Ei p.2) * Drift_w0 R Ei l‖
          ≤ (K * b * K * 1) * K ^ l.length :=
        Drift_nmul (Drift_nmul (Drift_norm_r1_le h p.1) (h.hE p.2))
          (Drift_norm_w0_le h l)
      have h2 : ‖(R p.1 * Ei p.2) * Drift_w1 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        Drift_nmul (Drift_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
      push_cast
      ring

private theorem Drift_norm_w2_le (h : Drift_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖Drift_w2 R D Ei l‖ ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2 := by
  induction l with
  | nil => simp [Drift_w2]
  | cons p l ih =>
      rw [Drift_w2, List.length_cons]
      have h1 : ‖(Drift_r2 R D p.1 * Ei p.2) * Drift_w0 R Ei l‖
          ≤ (2 * (K * b * K * b * K) * 1) * K ^ l.length :=
        Drift_nmul (Drift_nmul (Drift_norm_r2_le h p.1) (h.hE p.2))
          (Drift_norm_w0_le h l)
      have h2 : ‖(Drift_r1 R D p.1 * Ei p.2) * Drift_w1 R D Ei l‖
          ≤ (K * b * K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        Drift_nmul (Drift_nmul (Drift_norm_r1_le h p.1) (h.hE p.2))
          (Drift_norm_w1_le h l)
      have h3 : ‖(R p.1 * Ei p.2) * Drift_w2 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2) :=
        Drift_nmul (Drift_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (Drift_norm_add3 _ _ _).trans ((add_le_add (add_le_add h1
        (mul_le_mul_of_nonneg_left h2 zero_le_two)) h3).trans (le_of_eq ?_))
      push_cast
      ring

end Bounds

end Jets

section DiffBounds

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R₁ R₂ D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b δ : ℝ}

private theorem Drift_norm_r1_sub_le (h : Drift_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖Drift_r1 R₁ D σ - Drift_r1 R₂ D σ‖ ≤ 2 * (K ^ 3 * b * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := Drift_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact Drift_nmul (h.hdiff σ) (h.d₁.hD σ)
  have := Drift_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have e : Drift_r1 R₁ D σ - Drift_r1 R₂ D σ
      = -(R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ) := by
    simp only [Drift_r1]; abel
  rw [e, norm_neg]
  refine this.trans (le_of_eq ?_)
  ring

private theorem Drift_norm_r2_sub_le (h : Drift_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖Drift_r2 R₁ D σ - Drift_r2 R₂ D σ‖ ≤ 6 * (K ^ 4 * b ^ 2 * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hδ := h.hδ
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := Drift_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact Drift_nmul (h.hdiff σ) (h.d₁.hD σ)
  -- `R D R`
  have h3 := Drift_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have h3' : ‖R₂ σ * D σ * R₂ σ‖ ≤ K * b * K :=
    Drift_nmul (Drift_nmul (h.hR₂ σ) (h.d₁.hD σ)) (h.hR₂ σ)
  -- `R D R D`
  have h4 : ‖(R₁ σ * D σ * R₁ σ) * D σ - (R₂ σ * D σ * R₂ σ) * D σ‖
      ≤ (K ^ 2 * δ * b * K + K * b * (K ^ 2 * δ)) * b := by
    rw [← Matrix.sub_mul]
    exact Drift_nmul h3 (h.d₁.hD σ)
  have h4' : ‖R₂ σ * D σ * R₂ σ * D σ‖ ≤ K * b * K * b :=
    Drift_nmul h3' (h.d₁.hD σ)
  -- `R D R D R`
  have h5 := Drift_norm_sub_mul_le h4' (h.d₁.hR σ) h4 (h.hdiff σ)
  have e : Drift_r2 R₁ D σ - Drift_r2 R₂ D σ
      = (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ)
        + (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ) := by
    simp only [Drift_r2]; abel
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add h5 h5).trans (le_of_eq ?_))
  ring

private theorem Drift_norm_w0_sub_le (h : Drift_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖Drift_w0 R₁ Ei l - Drift_w0 R₂ Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * δ := by
  induction l with
  | nil => simp [Drift_w0]
  | cons p l ih =>
      rw [Drift_w0_cons, Drift_w0_cons, List.length_cons]
      have hA₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := Drift_nmul (h.hR₂ p.1) (h.d₁.hE p.2)
      have hdA : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (h.hdiff p.1) (h.d₁.hE p.2)
      have := Drift_norm_sub_mul_le hA₂ (Drift_norm_w0_le h.d₁ l) hdA ih
      refine this.trans (le_of_eq ?_)
      push_cast
      ring

private theorem Drift_norm_w1_sub_le (h : Drift_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖Drift_w1 R₁ D Ei l - Drift_w1 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b * δ := by
  induction l with
  | nil => simp [Drift_w1]
  | cons p l ih =>
      rw [Drift_w1, Drift_w1, List.length_cons]
      have hE := h.d₁.hE p.2
      -- the `r1` part
      have hA₂ : ‖Drift_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        Drift_nmul (Drift_norm_r1_le ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩ p.1) hE
      have hdA : ‖Drift_r1 R₁ D p.1 * Ei p.2 - Drift_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (Drift_norm_r1_sub_le h p.1) hE
      have hα := Drift_norm_sub_mul_le hA₂ (Drift_norm_w0_le h.d₁ l) hdA
        (Drift_norm_w0_sub_le h l)
      -- the `R` part
      have hB₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := Drift_nmul (h.hR₂ p.1) hE
      have hdB : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (h.hdiff p.1) hE
      have hβ := Drift_norm_sub_mul_le hB₂ (Drift_norm_w1_le h.d₁ l) hdB ih
      rw [add_sub_add_comm]
      refine (norm_add_le _ _).trans ((add_le_add hα hβ).trans (le_of_eq ?_))
      push_cast
      ring

private theorem Drift_norm_w2_sub_le (h : Drift_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖Drift_w2 R₁ D Ei l - Drift_w2 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * (l.length + 2) * K ^ (l.length + 3) * b ^ 2 * δ := by
  induction l with
  | nil => simp [Drift_w2]
  | cons p l ih =>
      rw [Drift_w2, Drift_w2, List.length_cons]
      have hE := h.d₁.hE p.2
      have h₂ : Drift_Data R₂ D Ei K b := ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩
      -- the `r2` part
      have hA₂ : ‖Drift_r2 R₂ D p.1 * Ei p.2‖ ≤ 2 * (K * b * K * b * K) * 1 :=
        Drift_nmul (Drift_norm_r2_le h₂ p.1) hE
      have hdA : ‖Drift_r2 R₁ D p.1 * Ei p.2 - Drift_r2 R₂ D p.1 * Ei p.2‖
          ≤ 6 * (K ^ 4 * b ^ 2 * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (Drift_norm_r2_sub_le h p.1) hE
      have hα := Drift_norm_sub_mul_le hA₂ (Drift_norm_w0_le h.d₁ l) hdA
        (Drift_norm_w0_sub_le h l)
      -- the `r1` part
      have hB₂ : ‖Drift_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        Drift_nmul (Drift_norm_r1_le h₂ p.1) hE
      have hdB : ‖Drift_r1 R₁ D p.1 * Ei p.2 - Drift_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (Drift_norm_r1_sub_le h p.1) hE
      have hβ := Drift_norm_sub_mul_le hB₂ (Drift_norm_w1_le h.d₁ l) hdB
        (Drift_norm_w1_sub_le h l)
      -- the `R` part
      have hC₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := Drift_nmul (h.hR₂ p.1) hE
      have hdC : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact Drift_nmul (h.hdiff p.1) hE
      have hγ := Drift_norm_sub_mul_le hC₂ (Drift_norm_w2_le h.d₁ l) hdC ih
      have e : ∀ a₁ a₂ c₁ c₂ d₁ d₂ : Matrix n n ℂ,
          (a₁ + (c₁ + c₁) + d₁) - (a₂ + (c₂ + c₂) + d₂)
            = (a₁ - a₂) + ((c₁ - c₂) + (c₁ - c₂)) + (d₁ - d₂) := fun _ _ _ _ _ _ => by abel
      rw [e]
      refine (Drift_norm_add3 _ _ _).trans ((add_le_add (add_le_add hα
        (mul_le_mul_of_nonneg_left hβ zero_le_two)) hγ).trans (le_of_eq ?_))
      push_cast
      ring

end DiffBounds

section Deriv

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {Rt : ℝ → Bool → Matrix n n ℂ} {D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {t : ℝ}

/-- Jets of a word along a family of resolvent factors with `R' = -R D R`. -/
private theorem Drift_hasDerivAt_w0
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => Drift_w0 (Rt s) Ei l) (Drift_w1 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [Drift_w0, Drift_w1] using hasDerivAt_const t (1 : Matrix n n ℂ)
  | cons p l ih =>
      have h : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * Drift_w0 (Rt s) Ei l)
          ((-(Rt t p.1 * D p.1 * Rt t p.1)) * Ei p.2 * Drift_w0 (Rt t) Ei l
            + Rt t p.1 * Ei p.2 * Drift_w1 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      simpa only [Drift_w0_cons, Drift_w1, Drift_r1] using h

private theorem Drift_hasDerivAt_w1
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => Drift_w1 (Rt s) D Ei l) (Drift_w2 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [Drift_w1, Drift_w2] using hasDerivAt_const t (0 : Matrix n n ℂ)
  | cons p l ih =>
      have hr1 : HasDerivAt (fun s => Drift_r1 (Rt s) D p.1)
          (Drift_r2 (Rt t) D p.1) t := by
        have h : HasDerivAt (fun s => -(Rt s p.1 * D p.1 * Rt s p.1))
            (-(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1))) t :=
          (((hR p.1).mul_const (D p.1)).mul (hR p.1)).neg
        have e : Drift_r2 (Rt t) D p.1 = -(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1)) := by
          simp only [Drift_r2]
          noncomm_ring
        rw [e]
        exact h
      have h0 := Drift_hasDerivAt_w0 (Ei := Ei) hR l
      have h1 : HasDerivAt (fun s => Drift_r1 (Rt s) D p.1 * Ei p.2 * Drift_w0 (Rt s) Ei l)
          (Drift_r2 (Rt t) D p.1 * Ei p.2 * Drift_w0 (Rt t) Ei l
            + Drift_r1 (Rt t) D p.1 * Ei p.2 * Drift_w1 (Rt t) D Ei l) t :=
        (hr1.mul_const (Ei p.2)).mul h0
      have h2 : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * Drift_w1 (Rt s) D Ei l)
          (Drift_r1 (Rt t) D p.1 * Ei p.2 * Drift_w1 (Rt t) D Ei l
            + Rt t p.1 * Ei p.2 * Drift_w2 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      have h3 := h1.add h2
      refine h3.congr_deriv ?_
      simp only [Drift_w2]
      abel

end Deriv

section LinCont

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ}

private theorem Drift_w1_add (D₁ D₂ : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    Drift_w1 R (D₁ + D₂) Ei l = Drift_w1 R D₁ Ei l + Drift_w1 R D₂ Ei l := by
  induction l with
  | nil => simp [Drift_w1]
  | cons p l ih =>
      rw [Drift_w1, Drift_w1, Drift_w1, ih]
      simp only [Drift_r1, Pi.add_apply]
      noncomm_ring

private theorem Drift_w1_smul (c : ℝ) (D : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    Drift_w1 R (c • D) Ei l = c • Drift_w1 R D Ei l := by
  induction l with
  | nil => simp [Drift_w1]
  | cons p l ih =>
      rw [Drift_w1, Drift_w1, ih]
      simp only [Drift_r1, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, smul_add, Matrix.neg_mul,
        smul_neg]

/-- `D ↦ w1 R D` is real-linear. -/
private def Drift_w1Lin (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : (Bool → Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ where
  toFun D := Drift_w1 R D Ei l
  map_add' D₁ D₂ := Drift_w1_add D₁ D₂ l
  map_smul' c D := Drift_w1_smul c D l

variable {X : Type*} [TopologicalSpace X] {Rt : X → Bool → Matrix n n ℂ}
  {D : Bool → Matrix n n ℂ}

private theorem Drift_continuous_w0 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => Drift_w0 (Rt x) Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih => exact (((h p.1).mul continuous_const).mul ih)

private theorem Drift_continuous_w1 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => Drift_w1 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => Drift_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      exact ((hr1.mul continuous_const).mul (Drift_continuous_w0 h l)).add
        (((h p.1).mul continuous_const).mul ih)

private theorem Drift_continuous_w2 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => Drift_w2 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => Drift_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      have hr2 : Continuous fun x => Drift_r2 (Rt x) D p.1 := by
        have h5 : Continuous fun x => Rt x p.1 * D p.1 * Rt x p.1 * D p.1 * Rt x p.1 :=
          (((((h p.1).mul continuous_const).mul (h p.1)).mul continuous_const).mul (h p.1))
        exact h5.add h5
      have h1 : Continuous fun x => Drift_r1 (Rt x) D p.1 * Ei p.2 * Drift_w1 (Rt x) D Ei l :=
        (hr1.mul continuous_const).mul (Drift_continuous_w1 (Ei := Ei) (D := D) h l)
      exact (((hr2.mul continuous_const).mul (Drift_continuous_w0 h l)).add (h1.add h1)).add
        (((h p.1).mul continuous_const).mul ih)

end LinCont

/-! ## 2. The loop functional along a line and along the spectral path -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem Drift_hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- The derivative of a signed resolvent along a moving Hermitian matrix and spectral parameter. -/
private theorem Drift_hasDerivAt_Gsig {H : ℝ → Matrix n n ℂ} {zf : ℝ → ℂ}
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
private theorem Drift_norm_Gsig_sub_le {M₁ M₂ : Matrix n n ℂ}
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
private def Drift_J1 (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  Matrix.trace (Drift_w1 (fun σ => Gsig H z σ) D (Eblk L W) (I.σ.zip I.a))

/-- The second jet `tr w2` of the loop functional. -/
private def Drift_J2 (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  Matrix.trace (Drift_w2 (fun σ => Gsig H z σ) D (Eblk L W) (I.σ.zip I.a))

/-- The spectral direction of the factor `G(σ)`: `m_σ · 1`. -/
private def Drift_Dsp (L W : ℕ) (E : ℝ) :
    Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  fun σ => spectralMSign E σ • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)

section LineDeriv

variable {H B : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

private theorem Drift_hasDerivAt_lineR (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (y : ℝ) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gsig (H + (s : ℂ) • B) z σ)
      (-(Gsig (H + (y : ℂ) • B) z σ * B * Gsig (H + (y : ℂ) • B) z σ)) y := by
  have := Drift_hasDerivAt_Gsig (hasDerivAt_line H B y) (hasDerivAt_const y z)
    (isHermitian_add_realSmul hH hB y) hz σ
  simpa using this

/-- First derivative of the loop functional along a Hermitian line. -/
private theorem Drift_hasDerivAt_line0 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => gloop L W (H + (s : ℂ) • B) z I)
      (Drift_J1 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  Drift_hasDerivAt_trace
    (Drift_hasDerivAt_w0 (Rt := fun s σ => Gsig (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk L W) (Drift_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

/-- Second derivative of the loop functional along a Hermitian line. -/
private theorem Drift_hasDerivAt_line1 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => Drift_J1 (H + (s : ℂ) • B) z (fun _ => B) I)
      (Drift_J2 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  Drift_hasDerivAt_trace
    (Drift_hasDerivAt_w1 (Rt := fun s σ => Gsig (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk L W) (Drift_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

end LineDeriv

section SpecDeriv

variable {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}

private theorem Drift_hasDerivAt_specR (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gsig H (spectralZ E s) σ)
      (-(Gsig H (spectralZ E v) σ * Drift_Dsp L W E σ * Gsig H (spectralZ E v) σ)) v := by
  have := Drift_hasDerivAt_Gsig (hasDerivAt_const v H) (hasDerivAt_spectralZ E v) hH hv σ
  refine this.congr_deriv ?_
  cases σ <;> simp [Drift_Dsp, spectralMSign]

private theorem Drift_hasDerivAt_spec0 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (I : LoopIdx (Z2 L)) :
    HasDerivAt (fun s : ℝ => gloop L W H (spectralZ E s) I)
      (Drift_J1 H (spectralZ E v) (Drift_Dsp L W E) I) v :=
  Drift_hasDerivAt_trace
    (Drift_hasDerivAt_w0 (Rt := fun s σ => Gsig H (spectralZ E s) σ)
      (D := Drift_Dsp L W E) (Ei := Eblk L W) (Drift_hasDerivAt_specR hH hv) (I.σ.zip I.a))

private theorem Drift_hasDerivAt_spec1 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (spectralZ E v).im ≠ 0) (I : LoopIdx (Z2 L)) :
    HasDerivAt (fun s : ℝ => Drift_J1 H (spectralZ E s) (Drift_Dsp L W E) I)
      (Drift_J2 H (spectralZ E v) (Drift_Dsp L W E) I) v :=
  Drift_hasDerivAt_trace
    (Drift_hasDerivAt_w1 (Rt := fun s σ => Gsig H (spectralZ E s) σ)
      (D := Drift_Dsp L W E) (Ei := Eblk L W) (Drift_hasDerivAt_specR hH hv) (I.σ.zip I.a))

end SpecDeriv

end Loop

/-! ## 3. Norm and Lipschitz bounds for the jets of the loop functional -/

section LoopBounds

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem Drift_norm_Eblk_le_one (a : Z2 L) : ‖Eblk L W a‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq L W a).trans ?_
  by_cases hW : W = 0
  · subst hW; simp
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hW
  have h1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  calc (W : ℝ)⁻¹ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 1 := one_pow 2

omit [NeZero W] in
private theorem Drift_zip_length {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    (I.σ.zip I.a).length = I.length := by
  rw [List.length_zip]
  simp only [LoopIdx.WF] at hwf
  rw [hwf, min_self]
  rfl

private theorem Drift_data {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    Drift_Data (fun σ => Gsig H z σ) D (Eblk L W) η⁻¹ b :=
  ⟨by positivity, hb, fun σ => norm_Gsig_le_inv_eta L W hH hη hz σ, hD,
    fun a => Drift_norm_Eblk_le_one a⟩

/-- `‖J1‖ ≤ N k K^{k+1} b`. -/
private theorem Drift_norm_J1_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖Drift_J1 H z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * η⁻¹ ^ (I.length + 1) * b) := by
  have h := Drift_norm_w1_le (Drift_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [Drift_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2‖ ≤ N k (k+1) K^{k+2} b²`. -/
private theorem Drift_norm_J2_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖Drift_J2 H z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b ^ 2) := by
  have h := Drift_norm_w2_le (Drift_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [Drift_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

private theorem Drift_diff {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    Drift_Diff (fun σ => Gsig H₁ z σ) (fun σ => Gsig H₂ z σ) D (Eblk L W) η⁻¹ b ‖H₁ - H₂‖ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  refine ⟨Drift_data hH₁ hη hz hb hD, fun σ => norm_Gsig_le_inv_eta L W hH₂ hη hz σ,
    norm_nonneg _, fun σ => ?_⟩
  refine (Drift_norm_Gsig_sub_le hH₁ hH₂ hzim σ).trans ?_
  have h1 : |z.im|⁻¹ ≤ η⁻¹ := inv_anti₀ hη hz
  have h2 : |z.im|⁻¹ ^ 2 ≤ η⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `‖J1(H₁) - J1(H₂)‖ ≤ N k (k+1) K^{k+2} b ‖H₁ - H₂‖`. -/
private theorem Drift_norm_J1_sub_le {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖Drift_J1 H₁ z D I - Drift_J1 H₂ z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b * ‖H₁ - H₂‖) := by
  have h := Drift_norm_w1_sub_le (Drift_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [Drift_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (Drift_w1 (fun σ => Gsig H₁ z σ) D (Eblk L W) (I.σ.zip I.a)
      - Drift_w1 (fun σ => Gsig H₂ z σ) D (Eblk L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2(H₁) - J2(H₂)‖ ≤ N k (k+1) (k+2) K^{k+3} b² ‖H₁ - H₂‖`. -/
private theorem Drift_norm_J2_sub_le {H₁ H₂ : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖Drift_J2 H₁ z D I - Drift_J2 H₂ z D I‖ ≤
      (Fintype.card (BlockIndex L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3) * b ^ 2 *
          ‖H₁ - H₂‖) := by
  have h := Drift_norm_w2_sub_le (Drift_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [Drift_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (Drift_w2 (fun σ => Gsig H₁ z σ) D (Eblk L W) (I.σ.zip I.a)
      - Drift_w2 (fun σ => Gsig H₂ z σ) D (Eblk L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

end LoopBounds

/-! ## 4. Counts: `Σ_c gueVar_c ≤ 2N`, and `‖X‖ ≤ 2 Σ_c |ω_c|` -/

section Counts

private theorem Drift_norm_single_le {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
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
private theorem Drift_norm_le_sum_entries {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => Drift_norm_single_le i j _))

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_norm_Xentry_le (ω : Ω L W) (i j : Idx L W) :
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

private theorem Drift_sum_coord (f : Coord L W → ℝ) :
    ∑ c : Coord L W, f c = ∑ i : Idx L W, ∑ j : Idx L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|`, in block coordinates. -/
private theorem Drift_norm_blockMat_Xmat_le (ω : Ω L W) :
    ‖blockMat (Xmat L W ω)‖ ≤ 2 * ∑ c : Coord L W, |ω c| := by
  refine (Drift_norm_le_sum_entries _).trans ?_
  have hent : ∑ p : BlockIndex L W, ∑ q : BlockIndex L W, ‖blockMat (Xmat L W ω) p q‖
      = ∑ i : Idx L W, ∑ j : Idx L W, ‖Xentry L W ω i j‖ := by
    rw [← Equiv.sum_comp (splitEquiv L W).symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp (splitEquiv L W).symm]
    rfl
  rw [hent, Drift_sum_coord]
  have hswap : ∑ i : Idx L W, ∑ j : Idx L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx L W, ∑ j : Idx L W, ‖Xentry L W ω i j‖
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Drift_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx L W, ∑ j : Idx L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

/-- `|Idx| = (W L)²`. -/
private theorem Drift_card_Idx : (Fintype.card (Idx L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
  simp [Idx, Z2, pow_two]

/-- `N = (W L)² ≥ 1`. -/
private theorem Drift_one_le_N : (1 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
  have : 1 ≤ (W * L) ^ 2 :=
    Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L)))
  exact_mod_cast this

/-! ### The GUE coordinate variances: `gueVar_c ≤ N⁻¹ ≤ 1` and `Σ_c gueVar_c ≤ 2 N`

(These replace the band counts through the row sums of `S^{(B)}`.) -/

/-- A diagonal GUE coordinate has variance `N⁻¹`, `N = (W L)²`. -/
private theorem Drift_gueVar_diag (i : Idx L W) (b : Bool) :
    ((gueVar L W (i, i, b) : NNReal) : ℝ) = ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Endpoints.gueVar]

/-- An off-diagonal GUE coordinate has variance `(2N)⁻¹`. -/
private theorem Drift_gueVar_offDiag {i j : Idx L W} (b : Bool) (hij : i ≠ j) :
    ((gueVar L W (i, j, b) : NNReal) : ℝ) = (2 * (((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Endpoints.gueVar, hij]

/-- Every GUE coordinate has variance at most `N⁻¹`. -/
private theorem Drift_gueVar_le_inv (c : Coord L W) :
    (gueVar L W c : ℝ) ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by
  obtain ⟨i, j, b⟩ := c
  by_cases hij : i = j
  · subst hij
    rw [Drift_gueVar_diag]
  · rw [Drift_gueVar_offDiag b hij, mul_inv]
    have h0 : (0 : ℝ) ≤ ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ := by positivity
    linarith

/-- Every GUE coordinate has variance at most `1`. -/
private theorem Drift_gueVar_le_one (c : Coord L W) : (gueVar L W c : ℝ) ≤ 1 :=
  (Drift_gueVar_le_inv c).trans (inv_le_one_of_one_le₀ Drift_one_le_N)

/-- `Σ_c gueVar_c ≤ 2 N`, `N = |Idx|` (the exact value is `N + 1`: the unused coordinates
`(i, i, false)` and the lower triangle carry variance but a zero direction). -/
private theorem Drift_sum_gueVar_le :
    ∑ c : Coord L W, (gueVar L W c : ℝ) ≤ 2 * (Fintype.card (Idx L W) : ℝ) := by
  rw [Drift_sum_coord]
  have hN0 : (0 : ℝ) < (((W * L) ^ 2 : ℕ) : ℝ) := lt_of_lt_of_le one_pos Drift_one_le_N
  calc ∑ i : Idx L W, ∑ j : Idx L W,
        ((gueVar L W (i, j, true) : ℝ) + (gueVar L W (i, j, false) : ℝ))
      ≤ ∑ i : Idx L W, ∑ j : Idx L W, 2 * ((((W * L) ^ 2 : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h1 := Drift_gueVar_le_inv (L := L) (W := W) (i, j, true)
          have h2 := Drift_gueVar_le_inv (L := L) (W := W) (i, j, false)
          linarith
    _ = 2 * (Fintype.card (Idx L W) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Drift_card_Idx]
        field_simp

/-! ### The coordinate law `gueP`: marginals and second moments -/

private theorem Drift_gueP_map_eval (c : Coord L W) :
    (gueP L W).map (fun ω => ω c) = gaussianReal 0 (gueVar L W c) :=
  Measure.infinitePi_map_eval _ c

private theorem Drift_integrable_sq_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => (ω c) ^ 2) (gueP L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (gueP L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((gueP L W).map fun ω => ω c) := by
    rw [Drift_gueP_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gueVar L W c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem Drift_integral_sq_coord (c : Coord L W) :
    ∫ ω, (ω c) ^ 2 ∂(gueP L W) = (gueVar L W c : ℝ) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (gueP L W) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((gueP L W).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, Drift_gueP_map_eval]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := gueVar L W c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-! ### First absolute moments of the Gaussian coordinates -/

private theorem Drift_integrable_abs_coord (c : Coord L W) :
    Integrable (fun ω : Ω L W => |ω c|) (gueP L W) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (Drift_integrable_sq_coord c))
    (continuous_abs.comp (continuous_apply c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]

private theorem Drift_integral_abs_coord_le (c : Coord L W) :
    ∫ ω : Ω L W, |ω c| ∂(gueP L W) ≤ 1 := by
  have hint : Integrable (fun ω : Ω L W => (1 + (ω c) ^ 2) / 2) (gueP L W) :=
    ((integrable_const (1 : ℝ)).add (Drift_integrable_sq_coord c)).div_const 2
  have hmono : ∫ ω : Ω L W, |ω c| ∂(gueP L W) ≤ ∫ ω : Ω L W, (1 + (ω c) ^ 2) / 2 ∂(gueP L W) := by
    refine integral_mono (Drift_integrable_abs_coord c) hint fun ω => ?_
    nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]
  refine hmono.trans ?_
  rw [integral_div, integral_add (integrable_const _) (Drift_integrable_sq_coord c),
    Drift_integral_sq_coord]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := Drift_gueVar_le_one (L := L) (W := W) c
  linarith

private theorem Drift_continuous_blockMat :
    Continuous (blockMat : Matrix (Idx L W) (Idx L W) ℂ →
      Matrix (BlockIndex L W) (BlockIndex L W) ℂ) :=
  continuous_id.matrix_submatrix _ _

private theorem Drift_integrable_sum_abs :
    Integrable (fun ω : Ω L W => 2 * ∑ c : Coord L W, |ω c|) (gueP L W) :=
  (integrable_finsetSum _ fun c _ => Drift_integrable_abs_coord c).const_mul 2

private theorem Drift_integrable_normX :
    Integrable (fun ω : Ω L W => ‖blockMat (Xmat L W ω)‖) (gueP L W) := by
  refine Integrable.mono' Drift_integrable_sum_abs ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (continuous_norm.comp
      (Drift_continuous_blockMat.comp (continuous_Xmat L W))).aestronglyMeasurable
  · rw [norm_norm]
    exact Drift_norm_blockMat_Xmat_le ω

/-- `E ‖X‖ ≤ 4 N²` (in block coordinates), `N = (W L)²`. -/
private theorem Drift_integral_normX_le :
    ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(gueP L W) ≤ 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by
  calc ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(gueP L W)
      ≤ ∫ ω : Ω L W, 2 * ∑ c : Coord L W, |ω c| ∂(gueP L W) :=
        integral_mono Drift_integrable_normX Drift_integrable_sum_abs
          fun ω => Drift_norm_blockMat_Xmat_le ω
    _ = 2 * ∑ c : Coord L W, ∫ ω : Ω L W, |ω c| ∂(gueP L W) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => Drift_integrable_abs_coord c]
    _ ≤ 2 * ∑ _c : Coord L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => Drift_integral_abs_coord_le c)
          zero_le_two
    _ = 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have : Fintype.card (Coord L W) = 2 * (Fintype.card (Idx L W)) ^ 2 := by
          simp [Coord, Fintype.card_prod, Fintype.card_bool]
          ring
        rw [this]
        push_cast
        rw [Drift_card_Idx]
        push_cast
        ring

end Counts

/-! ## 5. The derivative of `x ↦ E f(M + x X)` by Stein's identity -/

section Fine

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_blockMat_add_smul (A C : Matrix (Idx L W) (Idx L W) ℂ) (y : ℂ) :
    blockMat (A + y • C) = blockMat A + y • blockMat C := by
  ext p q
  simp [blockMat]

/-- The reindexed sample matrix `M + x X_ω`. -/
private def Drift_Hs (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) (ω : Ω L W) :
    Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  blockMat (M + (x : ℂ) • Xmat L W ω)

private theorem Drift_Hs_eq (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) (ω : Ω L W) :
    Drift_Hs M x ω = blockMat M + (x : ℂ) • blockMat (Xmat L W ω) :=
  Drift_blockMat_add_smul _ _ _

private theorem Drift_Hs_herm {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (x : ℝ)
    (ω : Ω L W) : (Drift_Hs M x ω).IsHermitian :=
  (isHermitian_add_realSmul hM (Xmat_isHermitian L W ω) x).submatrix _

private theorem Drift_continuous_Hs (M : Matrix (Idx L W) (Idx L W) ℂ) (x : ℝ) :
    Continuous (Drift_Hs M x) :=
  Drift_continuous_blockMat.comp
    (continuous_const.add ((continuous_Xmat L W).const_smul (x : ℂ)))

private theorem Drift_Hs_update {M : Matrix (Idx L W) (Idx L W) ℂ} (x : ℝ) (ω : Ω L W)
    (c : Coord L W) (t : ℝ) :
    Drift_Hs M x (Function.update ω c t) = Drift_Hs M x ω
      + ((x * (t - ω c) : ℝ) : ℂ) • blockMat (coordinateMatrix L W c) := by
  rw [Drift_Hs, Drift_Hs, Xmat_update]
  ext p q
  simp only [blockMat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private theorem Drift_continuous_Gsig {V : Type*} [TopologicalSpace V]
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

private theorem Drift_continuous_gloop : Continuous fun v => gloop L W (f v) z I :=
  (continuous_matrixTrace L W).comp
    (Drift_continuous_w0 (fun σ => Drift_continuous_Gsig hf hh hz σ) _)

private theorem Drift_continuous_J1 : Continuous fun v => Drift_J1 (f v) z D I :=
  (continuous_matrixTrace L W).comp
    (Drift_continuous_w1 (fun σ => Drift_continuous_Gsig hf hh hz σ) _)

private theorem Drift_continuous_J2 : Continuous fun v => Drift_J2 (f v) z D I :=
  (continuous_matrixTrace L W).comp
    (Drift_continuous_w2 (fun σ => Drift_continuous_Gsig hf hh hz σ) _)

end Cont

/-- Linearity of the first jet in the direction: `X = Σ_c ω_c C_c`. -/
private theorem Drift_J1_Xmat (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (I : LoopIdx (Z2 L)) (ω : Ω L W) :
    Drift_J1 H z (fun _ => blockMat (Xmat L W ω)) I
      = ∑ c : Coord L W, (ω c : ℂ) *
          Drift_J1 H z (fun _ => blockMat (coordinateMatrix L W c)) I := by
  have hX : (fun _ : Bool => blockMat (Xmat L W ω))
      = ∑ c : Coord L W, (ω c) • (fun _ : Bool => blockMat (coordinateMatrix L W c)) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply]
    ext p q
    rw [Xmat_eq_sum_coordinates]
    simp [blockMat, Matrix.sum_apply]
  have hlin := map_sum (Drift_w1Lin (fun σ => Gsig H z σ) (Eblk L W) (I.σ.zip I.a))
    (fun c : Coord L W => (ω c) • (fun _ : Bool => blockMat (coordinateMatrix L W c)))
    Finset.univ
  simp only [map_smul] at hlin
  unfold Drift_J1
  rw [hX]
  change Matrix.trace ((Drift_w1Lin (fun σ => Gsig H z σ) (Eblk L W) (I.σ.zip I.a)) _) = _
  rw [hlin, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul]
  rfl

/-- A Gaussian coordinate times a bounded continuous observable is integrable. -/
private theorem Drift_integrable_coord_mul (c : Coord L W) {g : Ω L W → ℂ}
    (hg : Continuous g) {C : ℝ} (hb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω L W => (ω c : ℂ) * g ω) (gueP L W) := by
  have hf : AEMeasurable (fun ω : Ω L W => ω c) (gueP L W) := (measurable_pi_apply c).aemeasurable
  have hg' : Integrable (fun x : ℝ => x) ((gueP L W).map fun ω => ω c) := by
    rw [Drift_gueP_map_eval]
    exact RBM.integrable_id_gaussianReal (var := gueVar L W c)
  have hcoord : Integrable (fun ω : Ω L W => ω c) (gueP L W) :=
    (integrable_map_measure hg'.aestronglyMeasurable hf).1 hg'
  have h := hcoord.ofReal.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa [Complex.real_smul, mul_comm] using h

section SteinStep

variable {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  {I : LoopIdx (Z2 L)} (hwf : I.WF)
include hM hz hwf

/-- The coordinate Stein identity, for the first jet along the coordinate direction. -/
private theorem Drift_stein_coord (x : ℝ) (c : Coord L W) :
    ∫ ω : Ω L W, (ω c : ℂ) *
        Drift_J1 (Drift_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)
      = ((gueVar L W c : ℝ) : ℂ) * ((x : ℂ) * ∫ ω : Ω L W,
        Drift_J2 (Drift_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
    := by
  set Cb := blockMat (coordinateMatrix L W c) with hCb
  have hCh : Cb.IsHermitian := (coordinateMatrix_isHermitian L W c).submatrix _
  set g : Ω L W → ℂ := fun ω => Drift_J1 (Drift_Hs M x ω) z (fun _ => Cb) I with hg
  set g' : Ω L W → ℂ := fun ω => (x : ℂ) * Drift_J2 (Drift_Hs M x ω) z (fun _ => Cb) I
    with hg'
  have hgc : Continuous g :=
    Drift_continuous_J1 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _
  have hg'c : Continuous g' :=
    continuous_const.mul
      (Drift_continuous_J2 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _)
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C := ⟨_, fun ω =>
    Drift_norm_J1_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl) hwf⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C := ⟨|x| * _, fun ω => by
    rw [hg', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (Drift_norm_J2_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb)
        (fun _ => le_rfl) hwf) (abs_nonneg _)⟩
  have hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    have hAh := Drift_Hs_herm hM x ω
    have hφ := Drift_hasDerivAt_line1 hAh hCh hz I (x * (ω c - ω c))
    have hh : HasDerivAt (fun t : ℝ => x * (t - ω c)) x (ω c) := by
      simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul x
    have hcomp := hφ.scomp (ω c) hh
    have hfun : (fun t : ℝ => g (Function.update ω c t)) =
        ((fun s : ℝ => Drift_J1 (Drift_Hs M x ω + (s : ℂ) • Cb) z (fun _ => Cb) I) ∘
          fun t : ℝ => x * (t - ω c)) := by
      funext t
      simp only [Function.comp, hg, Drift_Hs_update, hCb]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    simp [hg']
  have h := GaussianProduct.stein (gueVar L W) c g g' hgc hg'c hderiv hgb hg'b
  have hlaw : gueP L W = GaussianProduct.law (gueVar L W) := rfl
  rw [← hlaw] at h
  simp only [Complex.real_smul] at h
  rw [h, hg', integral_const_mul]

/-- **The derivative of `x ↦ E f(M + x X)`**: `x Σ_c gueVar_c E ∂²_c f(M + x X)`, by Stein. -/
private theorem Drift_hasDerivAt_F (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ω : Ω L W, gloop L W (Drift_Hs M y ω) z I ∂(gueP L W))
      ((x : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, Drift_J2 (Drift_Hs M x ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)) x := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hcontgl : ∀ y : ℝ, Continuous fun ω : Ω L W => gloop L W (Drift_Hs M y ω) z I :=
    fun y => Drift_continuous_gloop (Drift_continuous_Hs M y) (Drift_Hs_herm hM y) hz I
  have hint : ∀ y : ℝ, Integrable (fun ω : Ω L W => gloop L W (Drift_Hs M y ω) z I) (gueP L W) :=
    fun y => Integrable.of_bound (hcontgl y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude L W (Drift_Hs_herm hM y ω) hη le_rfl I hwf)
  have hJc : ∀ c : Coord L W, Continuous fun ω : Ω L W =>
      Drift_J1 (Drift_Hs M x ω) z (fun _ => blockMat (coordinateMatrix L W c)) I :=
    fun c => Drift_continuous_J1 (Drift_continuous_Hs M x) (Drift_Hs_herm hM x) hz I _
  have hF'cont : Continuous fun ω : Ω L W =>
      Drift_J1 (Drift_Hs M x ω) z (fun _ => blockMat (Xmat L W ω)) I := by
    simp only [Drift_J1_Xmat]
    exact continuous_finsetSum _ fun c _ =>
      (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc c)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gueP L W)
    (s := Set.univ) (x₀ := x)
    (F := fun y ω => gloop L W (Drift_Hs M y ω) z I)
    (F' := fun y ω => Drift_J1 (Drift_Hs M y ω) z (fun _ => blockMat (Xmat L W ω)) I)
    (bound := fun ω => ((Fintype.card (BlockIndex L W) : ℝ) *
      ((I.length : ℝ) * |z.im|⁻¹ ^ (I.length + 1))) * ‖blockMat (Xmat L W ω)‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hcontgl y).aestronglyMeasurable)
    (hint x) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω y _ =>
      (Drift_norm_J1_le (Drift_Hs_herm hM y ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl)
        hwf).trans (le_of_eq (by ring)))
    (Drift_integrable_normX.const_mul _)
    (Filter.Eventually.of_forall fun ω y _ => by
      have hXb : (blockMat (Xmat L W ω)).IsHermitian := (Xmat_isHermitian L W ω).submatrix _
      have := Drift_hasDerivAt_line0 hMb hXb hz I y
      simpa only [Drift_Hs_eq] using this)
  refine hD.congr_deriv ?_
  simp only [Drift_J1_Xmat]
  rw [integral_finsetSum _ fun c _ => Drift_integrable_coord_mul c (hJc c)
    (fun ω => Drift_norm_J1_le (Drift_Hs_herm hM x ω) hη le_rfl (norm_nonneg _)
      (fun _ => le_rfl) hwf)]
  simp_rw [Drift_stein_coord hM hz hwf x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end SteinStep

end Fine

/-! ## 6. The space step: `E f(M + τ X) - f(M) - τ² g(M)` -/

section SpaceStep

variable {L W : ℕ} [NeZero L] [NeZero W]

private theorem Drift_card_Block :
    (Fintype.card (BlockIndex L W) : ℝ) = (((W * L) ^ 2 : ℕ) : ℝ) := by
  rw [card_BlockIndex, mul_comm]

/-- The coordinate directions have norm at most `2` (in block coordinates). -/
private theorem Drift_norm_Cb_le (c : Coord L W) : ‖blockMat (coordinateMatrix L W c)‖ ≤ 2 := by
  have h := Drift_norm_blockMat_Xmat_le (L := L) (W := W) (Pi.single c (1 : ℝ))
  have h1 : ∑ c' : Coord L W, |(Pi.single c (1 : ℝ) : Coord L W → ℝ) c'| = 1 := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [h1] at h
  simpa [coordinateMatrix] using h

/-- The `g`-part: `g_u(M) = ½ Σ_c gueVar_c ∂²_c f(M)`. -/
private def Drift_g (z : ℂ) (I : LoopIdx (Z2 L)) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
    Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I

variable {M : Matrix (Idx L W) (Idx L W) ℂ} {z : ℂ} {I : LoopIdx (Z2 L)}

/-- The Lipschitz estimate of one coordinate second jet along the Gaussian sample. -/
private theorem Drift_coord_sub_le (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) (c : Coord L W) (y : ℝ) (ω : Ω L W) :
    ‖Drift_J2 (Drift_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I‖
      ≤ (((Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4) * |y|) * ‖blockMat (Xmat L W ω)‖ := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have h := Drift_norm_J2_sub_le (Drift_Hs_herm hM y ω) hMb hη hz (D := fun _ =>
    blockMat (coordinateMatrix L W c)) (b := 2) zero_le_two (fun _ => Drift_norm_Cb_le c) hwf
  have hd : ‖Drift_Hs M y ω - blockMat M‖ = |y| * ‖blockMat (Xmat L W ω)‖ := by
    rw [Drift_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hd] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- The key size estimate: the derivative of `ψ(y) = F(y) - F(0) - y² g(M)` is `O(y²)`. -/
private theorem Drift_psi_deriv_le (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {y : ℝ} (hy : 0 ≤ y) :
    ‖(y : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M‖
      ≤ (32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) * y ^ 2 := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  set C₃ : ℝ := (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hcont : ∀ c : Coord L W, Continuous fun ω : Ω L W =>
      Drift_J2 (Drift_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I :=
    fun c => Drift_continuous_J2 (Drift_continuous_Hs M y) (Drift_Hs_herm hM y) hz' I _
  have hint : ∀ c : Coord L W, Integrable (fun ω : Ω L W =>
      Drift_J2 (Drift_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I) (gueP L W) :=
    fun c => Integrable.of_bound (hcont c).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        Drift_norm_J2_le (Drift_Hs_herm hM y ω) hη hz (norm_nonneg _) (fun _ => le_rfl) hwf)
  -- one coordinate
  have hone : ∀ c : Coord L W,
      ‖(∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I‖
      ≤ (C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
    intro c
    have hsub : (∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I
        = ∫ ω : Ω L W, (Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I
          - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) ∂(gueP L W) := by
      rw [integral_sub (hint c) (integrable_const _)]
      simp
    rw [hsub]
    refine (norm_integral_le_of_norm_le ((Drift_integrable_normX.const_mul (C₃ * |y|)))
      (Filter.Eventually.of_forall fun ω =>
        Drift_coord_sub_le hM hη hz hwf c y ω)).trans ?_
    rw [integral_const_mul, abs_of_nonneg hy]
    have := Drift_integral_normX_le (L := L) (W := W)
    rw [← Drift_card_Idx] at this
    calc C₃ * y * ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(gueP L W)
        ≤ C₃ * y * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hsum : ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) * ∫ ω : Ω L W, Drift_J2
        (Drift_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)
      - 2 * Drift_g z I M
      = ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) := by
    simp only [Drift_g, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmain : (y : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) * ∫ ω : Ω L W, Drift_J2
        (Drift_Hs M y ω) z (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M
      = (y : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I) := by
    rw [← hsum]
    push_cast
    ring
  rw [hmain, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  have hsn : ‖∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
      ≤ (2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Coord L W, ‖((gueVar L W c : ℝ) : ℂ) *
          ((∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
            (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
          - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
        ≤ ∑ c : Coord L W, (gueVar L W c : ℝ) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gueVar L W c).coe_nonneg]
            exact mul_le_mul_of_nonneg_left (hone c) (gueVar L W c).coe_nonneg
      _ = (∑ c : Coord L W, (gueVar L W c : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right Drift_sum_gueVar_le (by positivity)
  calc y * ‖∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ((∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W))
        - Drift_J2 (blockMat M) z (fun _ => blockMat (coordinateMatrix L W c)) I)‖
      ≤ y * ((2 * (Fintype.card (Idx L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsn hy
    _ = _ := by rw [hC₃]; ring

/-- **The space step** for the law `gueP`: `‖E f(M + τ X) - f(M) - τ² g(M)‖ ≤ (Λ'/3) τ³`. -/
private theorem Drift_space_step (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) z I ∂(gueP L W)) - gloop L W (blockMat M) z I
        - ((τ ^ 2 : ℝ) : ℂ) * Drift_g z I M‖
      ≤ ((32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) / 3)
        * τ ^ 3 := by
  set Λ : ℝ := 32 * (Fintype.card (Idx L W) : ℝ) ^ 3 * (Fintype.card (BlockIndex L W) : ℝ) *
    ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3)) with hΛ
  set F : ℝ → ℂ := fun y => ∫ ω : Ω L W, gloop L W (Drift_Hs M y ω) z I ∂(gueP L W) with hF
  have hF0 : F 0 = gloop L W (blockMat M) z I := by
    simp [hF, Drift_Hs]
  set ψ : ℝ → ℂ := fun y => F y - F 0 - ((y ^ 2 : ℝ) : ℂ) * Drift_g z I M with hψ
  set ψ' : ℝ → ℂ := fun y => (y : ℂ) * ∑ c : Coord L W, ((gueVar L W c : ℝ) : ℂ) *
        ∫ ω : Ω L W, Drift_J2 (Drift_Hs M y ω) z
          (fun _ => blockMat (coordinateMatrix L W c)) I ∂(gueP L W)
      - ((2 * y : ℝ) : ℂ) * Drift_g z I M with hψ'
  have hd : ∀ y : ℝ, HasDerivAt ψ (ψ' y) y := by
    intro y
    have h1 := ((Drift_hasDerivAt_F hM hz' hwf y).sub_const (F 0)).sub
      ((((hasDerivAt_pow 2 y).ofReal_comp)).mul_const (Drift_g z I M))
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
    (fun y hy => Drift_psi_deriv_le hM hz' hη hz hwf hy.1)
  have := key (x := τ) ⟨hτ, le_rfl⟩
  simp only [hψ] at this
  rw [hF0] at this
  exact this

end SpaceStep

/-! ## 7. The time step, the closure of the constant, and the envelope -/

section TimeStep

/-- Second-order Taylor bound (the fencing lemma twice). -/
private theorem Drift_taylor2 {f f₁ f₂ : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
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

private theorem Drift_norm_Dsp_le {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    ‖Drift_Dsp L W E σ‖ ≤ 1 := by
  have hm : ‖spectralMSign E σ‖ = 1 := by
    cases σ <;> simp [spectralMSign, norm_spectralM hE.le]
  unfold Drift_Dsp
  rw [norm_smul, hm, one_mul]
  exact Drift_norm_one_le

private theorem Drift_eta_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (spectralM_im_pos hE)

/-- **The time step**: Taylor expansion of `v ↦ f_v(A)` at fixed `A`. -/
private theorem Drift_time_step {A : Matrix (Idx L W) (Idx L W) ℂ} (hA : A.IsHermitian)
    {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) {I : LoopIdx (Z2 L)} (hwf : I.WF) :
    ‖gloop L W (blockMat A) (spectralZ E (u + Δ)) I - gloop L W (blockMat A) (spectralZ E u) I
        - (Δ : ℂ) * Drift_J1 (blockMat A) (spectralZ E u) (Drift_Dsp L W E) I‖
      ≤ ((Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat A).IsHermitian := hA.submatrix _
  have hη := Drift_eta_pos hE hu1
  have hv : ∀ v ∈ Set.Icc u (u + Δ), (spectralZ E v).im ≠ 0 := fun v hv => by
    rw [spectralZ_im]
    exact (mul_pos (by linarith [hv.2]) (spectralM_im_pos hE)).ne'
  have hvη : ∀ v ∈ Set.Icc u (u + Δ), etaT E (u + Δ) ≤ |(spectralZ E v).im| :=
    fun v hv => spectralZ_im_gap hE hu1 hv
  have h := Drift_taylor2 (f := fun v => gloop L W (blockMat A) (spectralZ E v) I)
    (f₁ := fun v => Drift_J1 (blockMat A) (spectralZ E v) (Drift_Dsp L W E) I)
    (f₂ := fun v => Drift_J2 (blockMat A) (spectralZ E v) (Drift_Dsp L W E) I)
    (a := u) (b := u + Δ)
    (B := (Fintype.card (BlockIndex L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
      (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) (by linarith)
    (fun v hv' => Drift_hasDerivAt_spec0 hAb (hv v hv') I)
    (fun v hv' => Drift_hasDerivAt_spec1 hAb (hv v hv') I)
    (fun v hv' => by
      have := Drift_norm_J2_le hAb hη (hvη v hv') zero_le_one (D := Drift_Dsp L W E)
        (Drift_norm_Dsp_le hE) hwf
      simpa using this)
  simpa using h

end TimeStep

section Assembly

/-- The closure of the constant: `⅔·16·… ≤ 16 (k+3)⁴ N⁴ (1 + q)^{k+4}` with `q = η⁻¹`. -/
private theorem Drift_closure (k : ℕ) {N q : ℝ} (hN : 1 ≤ N) (hq : 0 ≤ q) :
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
private theorem Drift_deriv_deriv {M C : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (hC : C.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    deriv (deriv (fun y : ℝ => gloop L W (blockMat (M + (y : ℂ) • C)) z I)) 0
      = Drift_J2 (blockMat M) z (fun _ => blockMat C) I := by
  have hMb : (blockMat M).IsHermitian := hM.submatrix _
  have hCb : (blockMat C).IsHermitian := hC.submatrix _
  simp only [Drift_blockMat_add_smul]
  have h1 : deriv (fun y : ℝ => gloop L W (blockMat M + (y : ℂ) • blockMat C) z I)
      = fun y : ℝ => Drift_J1 (blockMat M + (y : ℂ) • blockMat C) z (fun _ => blockMat C) I := by
    funext y
    exact (Drift_hasDerivAt_line0 hMb hCb hz I y).deriv
  rw [h1]
  simpa using (Drift_hasDerivAt_line1 hMb hCb hz I 0).deriv

/-- **The one-step expansion with its envelope for one GUE increment** (the GUE analogue of
`oneStepEnvelope` of `Path/OneStep.lean`): for Hermitian `M`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a
well-formed loop of length `k`,
`‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · genMatGUE_u(M)‖ ≤ envConst · Δ^{3/2}` with `X ~ gueP L W`
and the band envelope `envConst`.  The proof splits the error into the space step at fixed time
`u` (`Drift_space_step`, by Stein for the product law `gueP`) and the time step at fixed sample
(`Drift_time_step`, by Taylor), and closes the constant with `Drift_closure`. -/
theorem oneStepEnvelopeGUE :
    ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : LoopIdx (Z2 L)), I.WF →
      ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
        ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
          ‖(∫ ω', gloop L W (blockMat (M + (Real.sqrt Δ : ℂ) • Xmat L W ω'))
                (spectralZ E (u + Δ)) I ∂(RBM.Endpoints.gueP L W)) -
              gloop L W (blockMat M) (spectralZ E u) I -
              (Δ : ℂ) * RBM.Univ.GUEPhase.genMatGUE L W E u M I‖ ≤
            envConst L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2) := by
  intro L W _ _ E hE I hwf u Δ hu hΔ hu1 M hM
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaT E (u + Δ) := Drift_eta_pos hE hu1
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
  have hgen : genMatGUE L W E u M I = Drift_g (spectralZ E u) I M
      + Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I := by
    unfold genMatGUE Drift_g
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Drift_deriv_deriv hM (coordinateMatrix_isHermitian L W c) hzu I]
    · exact (Drift_hasDerivAt_spec0 hMb hzu I).deriv
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (spectralZ E v).im ≠ 0 → Integrable
      (fun ω : Ω L W => gloop L W (Drift_Hs M τ ω) (spectralZ E v) I) (gueP L W) := fun v hv => by
    have hv' : 0 < |(spectralZ E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (Drift_continuous_gloop (Drift_continuous_Hs M τ)
      (Drift_Hs_herm hM τ) hv I).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude L W (Drift_Hs_herm hM τ ω) hv' le_rfl I hwf)
  -- the space step
  have hT2 := Drift_space_step hM hzu hη hηu hwf hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(gueP L W))
      - (∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E u) I ∂(gueP L W))
      - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω L W, ‖gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I
        - gloop L W (Drift_Hs M τ ω) (spectralZ E u) I
        - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat (Xmat L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat L W ω).IsHermitian :=
        isHermitian_add_realSmul hM (Xmat_isHermitian L W ω) τ
      have h1 := Drift_time_step hA hE hΔ hu1 hwf
      have h2 := Drift_norm_J1_sub_le (Drift_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := Drift_Dsp L W E) (Drift_norm_Dsp_le hE) hwf
      have hd : ‖Drift_Hs M τ ω - blockMat M‖ = τ * ‖blockMat (Xmat L W ω)‖ := by
        rw [Drift_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (Drift_Hs M τ ω) (spectralZ E u) I
          - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I
          = (gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E (u + Δ)) I
            - gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u) I
            - (Δ : ℂ) * Drift_J1 (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u)
              (Drift_Dsp L W E) I)
            + (Δ : ℂ) * (Drift_J1 (Drift_Hs M τ ω) (spectralZ E u) (Drift_Dsp L W E) I
              - Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I) := by
        simp only [Drift_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (Drift_J1 (Drift_Hs M τ ω) (spectralZ E u) (Drift_Dsp L W E) I
          - Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I)‖
          ≤ Δ * (c₁ * (τ * ‖blockMat (Xmat L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E (u + Δ)) I
            - gloop L W (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u) I
            - (Δ : ℂ) * Drift_J1 (blockMat (M + (τ : ℂ) • Xmat L W ω)) (spectralZ E u)
              (Drift_Dsp L W E) I‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat (Xmat L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(gueP L W))
        - (∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E u) I ∂(gueP L W))
        - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I
        = ∫ ω : Ω L W, (gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (Drift_Hs M τ ω) (spectralZ E u) I
          - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I)
            ∂(gueP L W) := by
      have i12 : Integrable (fun ω : Ω L W => gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I
          - gloop L W (Drift_Hs M τ ω) (spectralZ E u) I) (gueP L W) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat (Xmat L W ω)‖) (gueP L W) :=
      (integrable_const _).add (Drift_integrable_normX.const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) (Drift_integrable_normX.const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := Drift_integral_normX_le (L := L) (W := W)
    rw [← Drift_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω L W, ‖blockMat (Xmat L W ω)‖ ∂(gueP L W)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω L W, gloop L W (blockMat (M + (Real.sqrt Δ : ℂ) • Xmat L W ω))
        (spectralZ E (u + Δ)) I ∂(gueP L W)) - gloop L W (blockMat M) (spectralZ E u) I
        - (Δ : ℂ) * genMatGUE L W E u M I
      = ((∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E u) I ∂(gueP L W))
          - gloop L W (blockMat M) (spectralZ E u) I
          - ((τ ^ 2 : ℝ) : ℂ) * Drift_g (spectralZ E u) I M)
        + ((∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E (u + Δ)) I ∂(gueP L W))
          - (∫ ω : Ω L W, gloop L W (Drift_Hs M τ ω) (spectralZ E u) I ∂(gueP L W))
          - (Δ : ℂ) * Drift_J1 (blockMat M) (spectralZ E u) (Drift_Dsp L W E) I) := by
    rw [hgen, hτ2]
    simp only [Drift_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, Drift_card_Idx, Drift_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ 2 :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := Drift_closure I.length hN (inv_nonneg.mpr hη.le)
  unfold envConst
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, Drift_card_Block]
  calc _ = (32 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 3 * (((W * L) ^ 2 : ℕ) : ℝ) *
            ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * (etaT E (u + Δ))⁻¹ ^ (I.length + 3))
            / 3
          + ((((W * L) ^ 2 : ℕ) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
            (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * (1 / 2 + 4 * (((W * L) ^ 2 : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Assembly

/-! ## 8. The one-step recursion of the GUE-phase grid path -/

section Step

variable (d : Sizes)

/-- **The GUE-phase grid one-step recursion** `H_{k+1} = H_k + √(Δ/N) X_{k+1}`, `N = d.size n`. -/
theorem gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    gueH d t1 t0 K n (k + 1) ω
      = gueH d t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ) •
          Sizes.seqXmat d n (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold gueH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

end Step

/-! ## 9. The complex-valued freezing lemma for `Pgue d` -/

section FreezeC

variable {d : Sizes}

/-- The complex-valued freezing lemma for `Pgue d`.  `gueCondExp_freeze` is real-valued; the
complex case
is its real and imaginary parts, glued with `ContinuousLinearMap.comp_condExp_comm`. -/
private theorem Drift_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ d → β} (hY : Measurable[filt d k] Y)
    {F : β → Sizes.SeqΩ d → ℂ} (hF : Measurable (fun p : β × Sizes.SeqΩ d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (gueUnit d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set f : PathΩ d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Sizes.SeqΩ d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Sizes.SeqΩ d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Sizes.SeqΩ d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pgue d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pgue d) := hInt.im
  have hfreezeRe := gueCondExp_freeze d k hY hFre hIntRe
  have hfreezeIm := gueCondExp_freeze d k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fre (Y ω) x ∂(gueUnit d) := by
    have hRe' : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fre (Y ω) (ω (k + 1)) | filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fim (Y ω) x ∂(gueUnit d) := by
    have hIm' : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fim (Y ω) (ω (k + 1)) | filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(gueUnit d) = RCLike.re (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(gueUnit d) = RCLike.im (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pgue d)[f | filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωre, hreEq]
  · change RCLike.im ((Pgue d)[f | filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωim, himEq]

end FreezeC

/-! ## 10. The observable of the Hermitian part: continuity and a global bound

(Copies of the private `LoopStep_herm`, `LoopStep_Phi` of `Path/LoopStep.lean`.) -/

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)`. -/
private def Drift_herm (A : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (Idx L W) (Idx L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem Drift_herm_isHermitian (A : Matrix (Idx L W) (Idx L W) ℂ) :
    (Drift_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem Drift_herm_of_isHermitian {A : Matrix (Idx L W) (Idx L W) ℂ}
    (hA : A.IsHermitian) : Drift_herm A = A := by
  unfold Drift_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem Drift_continuous_herm :
    Continuous (Drift_herm : Matrix (Idx L W) (Idx L W) ℂ → _) := by
  unfold Drift_herm
  have h1 : Continuous fun A : Matrix (Idx L W) (Idx L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix. -/
private def Drift_Phi (L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : LoopIdx (Z2 L))
    (A : Matrix (Idx L W) (Idx L W) ℂ) : ℂ :=
  gloop L W (blockMat (Drift_herm A)) z I

private theorem Drift_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Z2 L)) :
    Continuous (Drift_Phi L W z I) := by
  unfold Drift_Phi
  exact Drift_continuous_gloop (f := fun A => blockMat (Drift_herm A))
    ((Drift_continuous_herm (L := L) (W := W)).matrix_submatrix _ _)
    (fun A => (Drift_herm_isHermitian A).submatrix _) hz I

private theorem Drift_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Z2 L)} (hwf : I.WF)
    (A : Matrix (Idx L W) (Idx L W) ℂ) :
    ‖Drift_Phi L W z I A‖ ≤
      (((L * W) ^ 2 : ℕ) : ℝ) * (|z.im|⁻¹ * ((W : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
  norm_gloop_le_crude L W ((Drift_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl I hwf

private theorem Drift_isHermitian_add_smul {p X : Matrix (Idx L W) (Idx L W) ℂ}
    (hp : p.IsHermitian) (hX : X.IsHermitian) (r : ℝ) :
    (p + (r : ℂ) • X).IsHermitian :=
  hp.add (hX.smul (by simp [IsSelfAdjoint]))

end Observable

/-! ## 11. The law of the unit slice, rescaled to `gueP`

Under `gueUnit d` the matrix `N^{-1/2} · slice d n x` has the law `gueP (d.L n) (d.W n)`.  Copies
of the private lemmas `GUEPhaseGrid_map_slice_infinitePi`, `GUEPhaseGrid_map_smul_infinitePi` of
`Grid.lean` and of the variance step `hunit` of `map_gueH_last`. -/

section LawTransfer

variable {d : Sizes}

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord d`. -/
private lemma Drift_map_slice_infinitePi (w : Sizes.SeqCoord d → ℝ≥0) (n : ℕ) :
    (Measure.infinitePi fun c => gaussianReal 0 (w c)).map (Sizes.slice d n)
      = Measure.infinitePi fun c : Coord (d.L n) (d.W n) => gaussianReal 0 (w ⟨n, c⟩) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : Coord (d.L n) (d.W n) → Sizes.SeqCoord d := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : Sizes.SeqCoord d → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : Sizes.slice d n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, Sizes.slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, Sizes.slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (Sizes.measurable_slice d n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e]

/-- Scaling every coordinate of an independent centred Gaussian family by `s` multiplies the
variances by `s²`. -/
private lemma Drift_map_smul_infinitePi {ι : Type*} (s : ℝ) (v : ι → ℝ≥0) :
    (Measure.infinitePi fun c => gaussianReal 0 (v c)).map (fun x : ι → ℝ => s • x)
      = Measure.infinitePi (fun c => gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s) * v c)) := by
  have hfmeas : ∀ c : ι, Measurable (s * ·) := fun c => by fun_prop
  have h1 : (Measure.infinitePi fun c => gaussianReal 0 (v c)).map
        (fun x : ι → ℝ => fun c => s * x c)
      = Measure.infinitePi (fun c => (gaussianReal 0 (v c)).map (s * ·)) :=
    Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (v c)) (f := fun _ => (s * ·)) hfmeas
  have heq : (fun x : ι → ℝ => s • x) = (fun x : ι → ℝ => fun c => s * x c) := by
    funext x c; simp [smul_eq_mul]
  rw [heq, h1]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]

/-- The rescaled slice `x ↦ N^{-1/2} · slice d n x`, `N = d.size n`. -/
private def Drift_scaledSlice (d : Sizes) (n : ℕ) (x : Sizes.SeqΩ d) : Ω (d.L n) (d.W n) :=
  (Real.sqrt ((d.size n : ℕ) : ℝ))⁻¹ • Sizes.slice d n x

private lemma Drift_measurable_scaledSlice (n : ℕ) : Measurable (Drift_scaledSlice d n) := by
  unfold Drift_scaledSlice
  exact (Sizes.measurable_slice d n).const_smul ((Real.sqrt ((d.size n : ℕ) : ℝ))⁻¹)

private lemma Drift_size_pos (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.W n := d.W_pos n
  have h2 : 0 < d.L n := by have := d.three_le_L n; omega
  have : 0 < d.size n := by
    rw [Sizes.size_eq]; positivity
  exact_mod_cast this

/-- The unit variance `1` (diagonal) or `1/2` (off the diagonal), divided by `N`, is `gueVar`. -/
private lemma Drift_unitVar_div (n : ℕ) (c : Coord (d.L n) (d.W n)) :
    ((gueUnitVar d ⟨n, c⟩ : ℝ≥0) : ℝ) / ((d.size n : ℕ) : ℝ)
      = (gueVar (d.L n) (d.W n) c : ℝ) := by
  have hsz : ((d.size n : ℕ) : ℝ) = (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) := rfl
  unfold gueUnitVar RBM.Endpoints.gueVar
  by_cases hc : c.1 = c.2.1
  · simp only [hc, ite_true, hsz]
    push_cast
    simp
  · simp only [hc, ite_false, hsz]
    push_cast
    field_simp

/-- **The law of the rescaled unit slice**: `(gueUnit d).map (N^{-1/2} · slice d n) = gueP`. -/
private lemma Drift_map_scaledSlice (n : ℕ) :
    (gueUnit d).map (Drift_scaledSlice d n) = gueP (d.L n) (d.W n) := by
  have hN := Drift_size_pos (d := d) n
  have hsm : Measurable (fun x : Ω (d.L n) (d.W n) => (Real.sqrt ((d.size n : ℕ) : ℝ))⁻¹ • x) :=
    by fun_prop
  have hcomp : Drift_scaledSlice d n =
      (fun x : Ω (d.L n) (d.W n) => (Real.sqrt ((d.size n : ℕ) : ℝ))⁻¹ • x) ∘
        Sizes.slice d n := rfl
  rw [hcomp, ← Measure.map_map hsm (Sizes.measurable_slice d n)]
  unfold gueUnit
  rw [Drift_map_slice_infinitePi (gueUnitVar d) n, Drift_map_smul_infinitePi]
  unfold gueP
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_mk, ← Drift_unitVar_div n c]
  have h2 : ((Real.sqrt ((d.size n : ℕ) : ℝ))⁻¹) ^ 2 = (((d.size n : ℕ) : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hN.le]
  rw [h2]
  ring

/-- Pointwise: `√(Δ/N) · seqXmat d n x = √Δ · Xmat (N^{-1/2} · slice d n x)`. -/
private lemma Drift_seqXmat_scaled (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (x : Sizes.SeqΩ d) :
    (Real.sqrt (gridStep t1 t0 K n / ((d.size n : ℕ) : ℝ)) : ℂ) • Sizes.seqXmat d n x
      = (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
        Xmat (d.L n) (d.W n) (Drift_scaledSlice d n x) := by
  have hN := Drift_size_pos (d := d) n
  unfold Drift_scaledSlice
  rw [Xmat_smul]
  have hreal : ∀ (r : ℝ) (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ),
      r • M = (r : ℂ) • M := fun r M => by
    ext i j
    simp [Complex.real_smul]
  rw [hreal, smul_smul, Real.sqrt_div' _ hN.le, div_eq_mul_inv, Complex.ofReal_mul]
  rfl

private lemma Drift_gueH_succ' (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ d) :
    gueH d t1 t0 K n (k + 1) ω
      = gueH d t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat (d.L n) (d.W n) (Drift_scaledSlice d n (ω (k + 1))) := by
  rw [gueH_succ, Drift_seqXmat_scaled]

end LawTransfer

/-! ## 12. The one-step conditional expectation -/

section LoopStepGUE

variable (d : Sizes)

/-- A private copy of the (private) `StandardBorelSpace` instance of `Markov.lean`. -/
private instance Drift_instStandardBorelSpaceMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ))

/-- The grid path is `filt d k`-measurable as a matrix-valued map (entrywise from
`gueH_adapted`). -/
private theorem Drift_measurable_gueH_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt d k] (gueH d t1 t0 K n k) :=
  @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt d k) _ _ |>.mpr fun j =>
      (gueH_adapted d t1 t0 K n k i j).measurable

/-- **The GUE analogue of `condExp_loop_step`** (`Path/LoopStep.lean`): the freezing lemma
applied to the one-step recursion `gueH_succ`, for the loop observable
`Φ_{u_{k+1}} = 𝓛(blockMat ·, z_{u_{k+1}}, I)`.  The conditional expectation given `filt d k` is the
integral of the observable over one GUE increment `√Δ X`, `X ~ gueP (d.L n) (d.W n)`, added to the
`gueH k ω`.  Under `gueUnit d` the matrix `√(Δ/N) seqXmat d n x` has the law of `√Δ Xmat` under
`gueP`, because `gueVar = gueUnitVar / N`. -/
theorem condExp_loop_step_gue (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ)
    (hE : |E| < 2) {I : LoopIdx (Z2 (d.L n))} (hwf : I.WF)
    (hu1 : gridTime t1 t0 K n (k + 1) < 1) :
    (Pgue d)[fun ω : PathΩ d =>
        gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n (k + 1) ω))
          (spectralZ E (gridTime t1 t0 K n (k + 1))) I | filt d k]
      =ᵐ[Pgue d] fun ω =>
        ∫ x, gloop (d.L n) (d.W n)
          (blockMat (gueH d t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat (d.L n) (d.W n) x))
          (spectralZ E (gridTime t1 t0 K n (k + 1))) I ∂(gueP (d.L n) (d.W n)) := by
  classical
  have hz : (spectralZ E (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (sub_pos.2 hu1) (spectralM_im_pos hE)).ne'
  set z : ℂ := spectralZ E (gridTime t1 t0 K n (k + 1)) with hzdef
  set Φ : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ :=
    Drift_Phi (d.L n) (d.W n) z I with hΦdef
  have hΦcont : Continuous Φ := Drift_continuous_Phi hz I
  set F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → Sizes.SeqΩ d → ℂ :=
    fun p x => Φ (p + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
      Xmat (d.L n) (d.W n) (Drift_scaledSlice d n x)) with hFdef
  have hXmeas : Measurable (fun x : Sizes.SeqΩ d =>
      Xmat (d.L n) (d.W n) (Drift_scaledSlice d n x)) :=
    (continuous_Xmat (d.L n) (d.W n)).measurable.comp (Drift_measurable_scaledSlice n)
  have hFmeas : Measurable (fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
      Sizes.SeqΩ d => F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ d =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat (d.L n) (d.W n) (Drift_scaledSlice d n x) :=
      hXmeas.const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    have h3 : Measurable fun p : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ ×
        Sizes.SeqΩ d => p.1 + (Real.sqrt (gridStep t1 t0 K n) : ℂ) •
          Xmat (d.L n) (d.W n) (Drift_scaledSlice d n p.2) :=
      measurable_fst.add (h2.comp measurable_snd)
    have h4 := hΦcont.measurable.comp h3
    exact h4
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) *
      (|z.im|⁻¹ * (((d.W n : ℕ) : ℝ)⁻¹ ^ 2)) ^ I.a.length :=
    fun p x => Drift_norm_Phi_le hz hwf _
  have hYmeas : Measurable[filt d k] (gueH d t1 t0 K n k) :=
    Drift_measurable_gueH_filt d t1 t0 K n k
  have hYmeas' : Measurable (gueH d t1 t0 K n k) := hYmeas.mono ((filt d).le k) le_rfl
  have hFInt : ∀ p, Integrable (F p) (gueUnit d) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ d => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm : Measurable (fun x : Sizes.SeqΩ d => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ d => F (gueH d t1 t0 K n k ω) (ω (k + 1)))
      (Pgue d) := by
    have hm : Measurable (fun ω : PathΩ d => F (gueH d t1 t0 K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω : PathΩ d =>
      gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n (k + 1) ω)) z I)
      = fun ω => F (gueH d t1 t0 K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (gueH d t1 t0 K n (k + 1) ω).IsHermitian :=
      gueH_isHermitian d t1 t0 K n (k + 1) ω
    change _ = Drift_Phi (d.L n) (d.W n) z I _
    rw [← Drift_gueH_succ' (d := d) t1 t0 K n k ω]
    unfold Drift_Phi
    rw [Drift_herm_of_isHermitian hH]
  rw [hEq]
  filter_upwards [Drift_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget] with ω hω
  rw [hω]
  have hp : (gueH d t1 t0 K n k ω).IsHermitian := gueH_isHermitian d t1 t0 K n k ω
  set f : Ω (d.L n) (d.W n) → ℂ := fun y =>
    gloop (d.L n) (d.W n)
      (blockMat (gueH d t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat (d.L n) (d.W n) y)) z I with hfdef
  have hfeq : f = fun y => Φ (gueH d t1 t0 K n k ω
      + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat (d.L n) (d.W n) y) := by
    funext y
    have hh := Drift_isHermitian_add_smul hp (Xmat_isHermitian (d.L n) (d.W n) y)
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω (d.L n) (d.W n) =>
        (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat (d.L n) (d.W n) y :=
      (continuous_Xmat (d.L n) (d.W n)).const_smul (Real.sqrt (gridStep t1 t0 K n) : ℂ)
    exact hΦcont.comp (continuous_const.add h2)
  have hFf : ∀ x, F (gueH d t1 t0 K n k ω) x = f (Drift_scaledSlice d n x) := by
    intro x
    have hh := Drift_isHermitian_add_smul hp
      (Xmat_isHermitian (d.L n) (d.W n) (Drift_scaledSlice d n x))
      (Real.sqrt (gridStep t1 t0 K n))
    simp only [hFdef, hΦdef, Drift_Phi, Drift_herm_of_isHermitian hh, hfdef]
  calc ∫ x, F (gueH d t1 t0 K n k ω) x ∂(gueUnit d)
      = ∫ x, f (Drift_scaledSlice d n x) ∂(gueUnit d) := by simp only [hFf]
    _ = ∫ y, f y ∂((gueUnit d).map (Drift_scaledSlice d n)) :=
        (integral_map (Drift_measurable_scaledSlice n).aemeasurable
          hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(gueP (d.L n) (d.W n)) := by rw [Drift_map_scaledSlice]

end LoopStepGUE

/-! ## 13. The conditional drift along the GUE-phase grid -/

/-- **The conditional drift of the loop observable along the GUE-phase grid path**, bounded by the
one-step envelope (`oneStepEnvelopeGUE`) applied pointwise at `M = gueH k ω` (Hermitian); the form
of `condExp_loop_drift` (`Path/LoopStep.lean`) with `pathP ↦ Pgue`, `pathH ↦ gueH`,
`genMat ↦ genMatGUE`.  The hypotheses `K n ≠ 0`, `k < K n` are not used by the proof. -/
theorem condExp_loop_drift_gue :
    ∀ (d : Sizes) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ), |E| < 2 →
    ∀ {I : LoopIdx (Z2 (d.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
    gridTime t1 t0 K n (k + 1) < 1 →
    ∀ᵐ ω ∂(RBM.Univ.GUEPhase.Pgue d),
      ‖(RBM.Univ.GUEPhase.Pgue d)[fun ω' : PathΩ d =>
            gloop (d.L n) (d.W n) (blockMat (RBM.Univ.GUEPhase.gueH d t1 t0 K n (k + 1) ω'))
              (spectralZ E (gridTime t1 t0 K n (k + 1))) I | filt d k] ω
          - gloop (d.L n) (d.W n) (blockMat (RBM.Univ.GUEPhase.gueH d t1 t0 K n k ω))
              (spectralZ E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * RBM.Univ.GUEPhase.genMatGUE (d.L n) (d.W n) E
              (gridTime t1 t0 K n k) (RBM.Univ.GUEPhase.gueH d t1 t0 K n k ω) I‖
        ≤ envConst (d.L n) (d.W n) E I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
  intro d t1 t0 K n k E hE I hwf ht1 ht10 _hK _hk hu1
  filter_upwards [condExp_loop_step_gue d t1 t0 K n k E hE hwf hu1] with ω hω
  rw [hω]
  have hΔ : 0 ≤ gridStep t1 t0 K n := div_nonneg (sub_nonneg.2 ht10) (Nat.cast_nonneg _)
  have hu : gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + gridStep t1 t0 K n := by
    unfold gridTime
    push_cast
    ring
  have hu0 : 0 ≤ gridTime t1 t0 K n k := by
    unfold gridTime
    positivity
  have key := oneStepEnvelopeGUE (d.L n) (d.W n) E hE I hwf (gridTime t1 t0 K n k)
    (gridStep t1 t0 K n) hu0 hΔ (hu ▸ hu1) (gueH d t1 t0 K n k ω)
    (gueH_isHermitian d t1 t0 K n k ω)
  rw [← hu] at key
  exact key

end RBM.Univ.GUEPhase

end
