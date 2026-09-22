/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Dyadic
import RBM2D.Propagator.FiniteDiff

/-!
# Both cases of Property 6

This file combines the small-step dyadic estimate of T18 with the large-step
Fourier estimate of T5. The dyadic decomposition and its scale-independent
constant still have to be constructed in T22. Accordingly, every analytic
estimate below names the actual `DyadicDecomp` hypothesis and the domination
statement names an explicit uniform upper bound on its constant.

The paper uses the periodic Euclidean norm, while `zdist2` is the equivalent
periodic `L¹` norm; this recorded translation is in `docs/paper-deltas.md`.
-/

namespace RBM

open Filter

variable {L : ℕ} [NeZero L] {ξ : ℂ}

/-- The first right-hand side of `(prop:BD1)`, without the domination factor. -/
noncomputable def fd1Scale (L : ℕ) [NeZero L] (ξ : ℂ) (u s : Z2 L) : ℝ :=
  (zdist2 L s : ℝ) * ((zdist2 L u : ℝ) + 1)⁻¹ +
    (zdist2 L s : ℝ) * (kappa ξ * (ellhat L ξ) ^ 2)⁻¹

/-- The second right-hand side of `(prop:BD2)`, without the domination factor. -/
noncomputable def fd2Scale (L : ℕ) [NeZero L] (ξ : ℂ) (u s : Z2 L) : ℝ :=
  (zdist2 L s : ℝ) ^ 2 * ((zdist2 L u : ℝ) ^ 2 + 1)⁻¹ +
    (zdist2 L s : ℝ) ^ 2 * ((ellhat L ξ) ^ 2)⁻¹

/-- Both paper scales are nonnegative. The first uses `κ > 0`, which follows
from `‖ξ‖ < 1`; no lower bound on `ℓ̂` is needed for nonnegativity. -/
theorem fd1Scale_nonneg (hξ : ‖ξ‖ < 1) (u s : Z2 L) :
    0 ≤ fd1Scale L ξ u s := by
  have hk : 0 ≤ kappa ξ := (kappa_pos hξ).le
  unfold fd1Scale
  exact add_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (mul_nonneg hk (sq_nonneg _))))

theorem fd2Scale_nonneg (u s : Z2 L) : 0 ≤ fd2Scale L ξ u s := by
  unfold fd2Scale
  positivity

/-- One common coefficient dominates the constants of both cases. -/
noncomputable def derivativePrefactor (C : ℝ) (L : ℕ) : ℝ :=
  8 * C + 720 * (1 + Real.log L)

/-- T18 Case 1 and T5 Case 2 cover all displacements. This is Property 6 in
the paper's exact two-term scale, conditional on T22's dyadic decomposition. -/
theorem norm_Theta_fd_all_le (H : DyadicDecomp L ξ) (hL : 3 ≤ L)
    (hξ : ‖ξ‖ < 1) (u s : Z2 L) :
    ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
        ≤ derivativePrefactor H.C L * fd1Scale L ξ u s
      ∧
    ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
        ≤ derivativePrefactor H.C L * fd2Scale L ξ u s := by
  have hlog : 0 ≤ 1 + Real.log L := one_add_log_nonneg L
  have hA : 0 ≤ fd1Scale L ξ u s := fd1Scale_nonneg hξ u s
  have hB : 0 ≤ fd2Scale L ξ u s := fd2Scale_nonneg u s
  rcases le_or_gt (2 * zdist2 L s) (zdist2 L u) with hsmall | hlarge
  · have hfirst := norm_Theta_fd1_le_paper H hL hξ hsmall
    have hsecond := norm_Theta_fd2_le_paper H hsmall
    change ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
      ≤ 8 * H.C * fd1Scale L ξ u s at hfirst
    change ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ 8 * H.C * fd2Scale L ξ u s at hsecond
    have hc : 8 * H.C ≤ derivativePrefactor H.C L := by
      unfold derivativePrefactor
      linarith
    exact ⟨hfirst.trans (mul_le_mul_of_nonneg_right hc hA),
      hsecond.trans (mul_le_mul_of_nonneg_right hc hB)⟩
  · have hcase := norm_Theta_fd_case2_le_paper L hL hξ u s hlarge
    have hfirst := hcase.1
    have hsecond := hcase.2
    change ‖Theta L ξ u 0 - Theta L ξ (u - s) 0‖
      ≤ 720 * (1 + Real.log L) * fd1Scale L ξ u s at hfirst
    change ‖2 * Theta L ξ u 0 - Theta L ξ (u - s) 0 - Theta L ξ (u + s) 0‖
      ≤ 720 * (1 + Real.log L) * fd2Scale L ξ u s at hsecond
    have hc : 720 * (1 + Real.log L) ≤ derivativePrefactor H.C L := by
      unfold derivativePrefactor
      nlinarith [H.C_nonneg]
    exact ⟨hfirst.trans (mul_le_mul_of_nonneg_right hc hA),
      hsecond.trans (mul_le_mul_of_nonneg_right hc hB)⟩

/-- Translation invariance converts the general matrix entry to the pinned
second index used by T18 and T5. -/
theorem Theta_apply_eq_sub_zero (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    (a b : Z2 L) : Theta L ξ a b = Theta L ξ (a - b) 0 := by
  have h := Theta_apply_add_right L hL hξ (a - b) 0 b
  simpa using h

/-- Property 6 for arbitrary matrix indices, retaining the paper's two
right-hand sides. T22 still has to produce `H`. -/
theorem norm_Theta_fd_all_le_matrix (H : DyadicDecomp L ξ)
    (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (a b s : Z2 L) :
    ‖Theta L ξ a b - Theta L ξ a (b + s)‖
        ≤ derivativePrefactor H.C L * fd1Scale L ξ (a - b) s
      ∧
    ‖2 * Theta L ξ a b - Theta L ξ a (b + s) - Theta L ξ a (b - s)‖
        ≤ derivativePrefactor H.C L * fd2Scale L ξ (a - b) s := by
  have hminus : a - (b + s) = (a - b) - s := by abel
  have hplus : a - (b - s) = (a - b) + s := by abel
  rw [Theta_apply_eq_sub_zero hL hξ a b,
    Theta_apply_eq_sub_zero hL hξ a (b + s),
    Theta_apply_eq_sub_zero hL hξ a (b - s), hminus, hplus]
  exact norm_Theta_fd_all_le H hL hξ (a - b) s

/-- A uniform absolute bound on T22's dyadic constant turns the local
coefficient into a function of `L` alone. -/
theorem norm_Theta_fd_all_le_uniform (H : DyadicDecomp L ξ)
    (C₀ : ℝ) (hC : H.C ≤ C₀) (hL : 3 ≤ L)
    (hξ : ‖ξ‖ < 1) (a b s : Z2 L) :
    ‖Theta L ξ a b - Theta L ξ a (b + s)‖
        ≤ derivativePrefactor C₀ L * fd1Scale L ξ (a - b) s
      ∧
    ‖2 * Theta L ξ a b - Theta L ξ a (b + s) - Theta L ξ a (b - s)‖
        ≤ derivativePrefactor C₀ L * fd2Scale L ξ (a - b) s := by
  have hfactor : derivativePrefactor H.C L ≤ derivativePrefactor C₀ L := by
    unfold derivativePrefactor
    linarith
  have hA : 0 ≤ fd1Scale L ξ (a - b) s := fd1Scale_nonneg hξ _ _
  have hB : 0 ≤ fd2Scale L ξ (a - b) s := fd2Scale_nonneg _ _
  have h := norm_Theta_fd_all_le_matrix H hL hξ a b s
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hfactor hA),
    h.2.trans (mul_le_mul_of_nonneg_right hfactor hB)⟩

/-- For a fixed absolute dyadic constant, the common Property 6 prefactor is
`≺ 1` in the block-side length `L`. It is uniform in `ξ,a,b,s` because it has
no dependence on them. -/
theorem derivativePrefactor_detDom_one (C₀ : ℝ) (hC : 0 ≤ C₀) :
    (fun L : ℕ => derivativePrefactor C₀ L) ≺ (fun _ => (1 : ℝ)) := by
  have hone : (fun _ : ℕ => (1 : ℝ)) ≺ (fun _ => (1 : ℝ)) :=
    DetDom.refl (fun _ => by norm_num)
  have hconst : (fun _ : ℕ => 8 * C₀) ≺ (fun _ => (1 : ℝ)) := by
    simpa using DetDom.const_mul_left (c := 8 * C₀) (by positivity)
      (fun _ => by norm_num) hone
  have hlog : (fun L : ℕ => 720 * (1 + Real.log L)) ≺
      (fun _ => (1 : ℝ)) := case2_log_prefactor_detDom_one
  have h := DetDom.add_left (fun _ => by norm_num) hconst hlog
  change (fun L : ℕ => derivativePrefactor C₀ L) ≺ (fun _ => (1 : ℝ)) at h
  exact h

/-- The `≺` result gives one threshold in `L`, independent of `ξ,a,b,s` and
of which of the two inequalities is requested. -/
theorem derivativePrefactor_eventually_le_rpow (C₀ : ℝ) (hC : 0 ≤ C₀)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℕ in atTop, derivativePrefactor C₀ L ≤ (L : ℝ) ^ τ := by
  simpa using (detDom_iff.mp (derivativePrefactor_detDom_one C₀ hC)) τ hτ

/-- The matrix estimate written with the two explicit expressions of the
paper. The hypothesis `H.C ≤ C₀` is the scale-uniformity owed by T22. -/
theorem norm_Theta_fd_all_le_paper (H : DyadicDecomp L ξ)
    (C₀ : ℝ) (hC : H.C ≤ C₀) (hL : 3 ≤ L)
    (hξ : ‖ξ‖ < 1) (a b s : Z2 L) :
    ‖Theta L ξ a b - Theta L ξ a (b + s)‖
        ≤ derivativePrefactor C₀ L *
          ((zdist2 L s : ℝ) * ((zdist2 L (a - b) : ℝ) + 1)⁻¹ +
            (zdist2 L s : ℝ) * (kappa ξ * (ellhat L ξ) ^ 2)⁻¹)
      ∧
    ‖2 * Theta L ξ a b - Theta L ξ a (b + s) - Theta L ξ a (b - s)‖
        ≤ derivativePrefactor C₀ L *
          ((zdist2 L s : ℝ) ^ 2 * ((zdist2 L (a - b) : ℝ) ^ 2 + 1)⁻¹ +
            (zdist2 L s : ℝ) ^ 2 * ((ellhat L ξ) ^ 2)⁻¹) := by
  simpa only [fd1Scale, fd2Scale] using
    norm_Theta_fd_all_le_uniform H C₀ hC hL hξ a b s

/-- The full uniform-in-parameters inequality after a chosen `L` has passed
the `≺` threshold. T22 must supply `H` with `H.C ≤ C₀`; the threshold is the
one from `derivativePrefactor_eventually_le_rpow`. -/
theorem norm_Theta_fd_all_le_rpow (H : DyadicDecomp L ξ)
    (C₀ : ℝ) (hC : H.C ≤ C₀) (hL : 3 ≤ L)
    (hξ : ‖ξ‖ < 1) (a b s : Z2 L) (τ : ℝ)
    (hthreshold : derivativePrefactor C₀ L ≤ (L : ℝ) ^ τ) :
    ‖Theta L ξ a b - Theta L ξ a (b + s)‖
        ≤ (L : ℝ) ^ τ * fd1Scale L ξ (a - b) s
      ∧
    ‖2 * Theta L ξ a b - Theta L ξ a (b + s) - Theta L ξ a (b - s)‖
        ≤ (L : ℝ) ^ τ * fd2Scale L ξ (a - b) s := by
  have hA : 0 ≤ fd1Scale L ξ (a - b) s := fd1Scale_nonneg hξ _ _
  have hB : 0 ≤ fd2Scale L ξ (a - b) s := fd2Scale_nonneg _ _
  have h := norm_Theta_fd_all_le_uniform H C₀ hC hL hξ a b s
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hthreshold hA),
    h.2.trans (mul_le_mul_of_nonneg_right hthreshold hB)⟩

/-- Both geometric cases really occur on a finite torus, with an admissible
spectral parameter. This does not assert existence of `DyadicDecomp`, which is
the mathematical construction assigned to T22. -/
example : 3 ≤ (3 : ℕ) ∧ ‖(0 : ℂ)‖ < 1 ∧
    2 * zdist2 3 ((1, 0) : Z2 3) ≤ zdist2 3 ((1, 1) : Z2 3) ∧
    zdist2 3 (0 : Z2 3) < 2 * zdist2 3 ((1, 0) : Z2 3) := by
  constructor
  · omega
  constructor
  · norm_num
  constructor <;> decide

end RBM
