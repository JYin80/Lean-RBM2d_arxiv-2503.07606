/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Path.Scales
import RBM2D.Path.PerTime
import RBM2D.Hierarchy.Loops
import RBM2D.Propagator.Basic
import RBM2D.Defs.Dist
import RBM2D.Gauss.Model
import RBM2D.Gauss.LoopTimeCont

/-!
# The Step 2 vocabulary: threshold, matrix-level functionals, step conditions

The threshold `thr`, the matrix-level functionals (`blockMat`, `pmLoop`, `loopOf`, `Kpm`,
`lkErrMat`, `jStarMat`, `llErrMat`, `loopAbs`), the conditions `Bandwidth`, `CondStInd`,
`RangeCond`, and the hypotheses and conclusions of Step 2 in per-time form (`InitDecay`,
`InitLocal`, `Step1LoopPT`, `Step1WeakLawPT`, `Step2LocalPT`, `Step2DecayPT`, `Step2Eq53PT`).
In `thr`, `CondStInd`, `InitDecay`, `InitLocal`, `Step1LoopPT`, `Step1WeakLawPT`, `Step2LocalPT`,
`Step2DecayPT`, `Step2Eq53PT` the energy is a sequence `E : ℕ → ℝ` and each occurrence of `E` in
the body is `E n` (`n` the size index in scope).  `Bandwidth`, `RangeCond` and section
`Functionals` take one real `E`.  Paper: arXiv:2503.07606.

Differences from the paper: `thr` carries the factor `N^δ`; `Step2Eq53PT` has the near-diagonal
exponent `5/2` (the paper has `2`); `RangeCond` is an additional hypothesis (the application
range); the statements are in the per-time form of `PerTimeDomAt`.

Results:
1. `lkErrMat_nonneg`, `llErrMat_nonneg`, `loopAbs_nonneg`: the three error functionals are `≥ 0`;
2. `one_le_jStarMat`: `1 ≤ J*` for `1 ≤ W`;
3. `lkErrMat_le_jStarMat_mul_tailT`: `|(𝓛-𝒦)_{ab}| ≤ J* · 𝒯(|a-b|_L)` for `1 ≤ W`.

For `d = 2` the index is `Z2 L`, the distance `zdist2`, and `tailT` carries `M_u^{-2}` with
`M_u = W² ℓ_u² η_u`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal

set_option linter.style.longLine false

variable (d : Sizes)

/-- **The Step 2 threshold.**  `Θ(u) = N^δ (η_s/η_u)^4` with `N = size n = W_n² L_n²`.  The
paper's threshold (the stopping time `T` before (`51`)) is `(η_s/η_t)^4`, fixed in `u` and
without `N^δ`.  Evaluated at the energy `E n`. -/
def thr (E : ℕ → ℝ) (s : ℕ → ℝ) (δ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ((d.size n : ℕ) : ℝ) ^ δ * (etaT (E n) (s n) / etaT (E n) u) ^ 4

/-! ## Matrix-level functionals -/

section Functionals

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The fine-lattice matrix reindexed by block and within-block coordinates
(as `HflowBlock` in `Gauss/LoopTimeCont.lean`). -/
def blockMat (M : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ :=
  M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm

/-- The `σ = (+,-)` two-loop index `(a, b)`. -/
def pmLoop (a b : Z2 L) : LoopIdx (Z2 L) := ⟨[true, false], [a, b]⟩

/-- A loop of length `k` with signs `σ` and labels `a`. -/
def loopOf {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) : LoopIdx (Z2 L) :=
  ⟨List.ofFn σ, List.ofFn a⟩

variable (L W)

/-- The primitive two-loop at `σ = (+,-)` by (`Kn2sol`):
`𝒦_{u,(+,-),(a,b)} = W^{-2} m m̄ (Θ^{(B)}_{u m m̄})_{ab}`. -/
def Kpm (E u : ℝ) (a b : Z2 L) : ℂ :=
  ((W : ℂ)⁻¹) ^ 2 * (Complex.normSq (spectralM E) : ℂ) *
    Theta L ((u : ℂ) * (Complex.normSq (spectralM E) : ℂ)) a b

/-- `|(𝓛 - 𝒦)_{u,(+,-),(a,b)}|` at the matrix `M`, spectral parameter `z_u^{(E)}`. -/
def lkErrMat (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) : ℝ :=
  ‖gloop L W (blockMat M) (spectralZ E u) (pmLoop a b) - Kpm L W E u a b‖

/-- `J*_{u,D}` at the matrix `M` (`def_Ju`; `shoellJJ`).  Because both tail functions are
non-increasing in `ℓ`, the maximum over `ℓ` is attained at `ℓ = |a - b|_L` for each pair. -/
def jStarMat (E D u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : Z2 L × Z2 L =>
      lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ)) + 1

/-- `|(G_u - m)_{ij}|` at the matrix `M` (the entries of `‖G_u - m‖_max`). -/
def llErrMat (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) : ℝ :=
  ‖(M - spectralZ E u • (1 : Matrix (Idx L W) (Idx L W) ℂ))⁻¹ i j -
      (if i = j then spectralM E else 0)‖

/-- `|𝓛_{u,σ,a}|` for a loop of length `k` at the matrix `M`. -/
def loopAbs (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℝ :=
  ‖gloop L W (blockMat M) (spectralZ E u) (loopOf σ a)‖

end Functionals

/-! ## Inputs of Step 2: time-`s` hypotheses, Step 1 outputs, step conditions -/

/-- (`Main_DEL_COND`): `W ≥ N^𝔠`, eventually. -/
def Bandwidth (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ c ≤ (d.W n : ℝ)

/-- (`con_st_ind`): `M_s^{-1} ≤ ((1-t)/(1-s))^{30}`, eventually. Evaluated at the energy `E n`. -/
def CondStInd (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ≤ ((1 - t n) / (1 - s n)) ^ 30

/-- The application range `1 - t ≥ N^{-1+τ}`, eventually.  This is not a hypothesis of
Theorem `lem:main_ind` in the paper. -/
def RangeCond (τ : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n

/-- (`Eq:Gdecay+IND`) at the time `s`, for every `D > 0`. Evaluated at the energy `E n`. -/
def InitDecay (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) (s n) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (s n))) +
      (d.W n : ℝ) ^ (-D))

/-- (`Gt_bound+IND`) at the time `s`. Evaluated at the energy `E n`. -/
def InitLocal (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => Unit × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)
    (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (s n))⁻¹ ^ ((1 : ℝ) / 2))

/-- (`lRB1`), per time: for every loop length `k ≥ 1`,
`|𝓛_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{2(k-1)} M_u^{-k+1}`, uniformly in `u ∈ [s,t]`, `σ`, `a`. Evaluated at the energy `E n`. -/
def Step1LoopPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n p ω => loopAbs (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (ellT (d.L n) p.1 / ellT (d.L n) (s n)) ^ (2 * (k - 1)) *
      (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ (k - 1))

/-- (`Gtmwc`), per time: `‖G_u - m‖_max ≺ M_u^{-1/4}`, uniformly in `u ∈ [s,t]`. Evaluated at the
energy `E n`. -/
def Step1WeakLawPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ ((1 : ℝ) / 4))

/-! ## Outputs of Step 2, per time -/

/-- (`Gt_bound_flow`), per time: `‖G_u - m‖_max ≺ M_u^{-1/2}`, `u ∈ [s,t]`. Evaluated at the energy
`E n`. -/
def Step2LocalPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ ((1 : ℝ) / 2))

/-- (`Eq:Gdecay_w`), per time: for every `D > 0`,
`|(𝓛-𝒦)_{u,(+,-),(a,b)}| ≺ (η_s/η_u)^4 M_u^{-2} exp(-(|a-b|_L/ℓ_u)^{1/2}) + W^{-D}`. Evaluated at the energy `E n`. -/
def Step2DecayPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (etaT (E n) (s n) / etaT (E n) p.1) ^ 4 * (scaleM (d.L n) (d.W n) (E n) p.1 ^ 2)⁻¹ *
        Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) p.1)) +
      (d.W n : ℝ) ^ (-D))

/-- (53), per time and at every endpoint `u ∈ [s,t]`, with the near-diagonal exponent
`5/2` that the Step 2 argument gives (paper: `2`):
`|(𝓛-𝒦)_{u,(+,-),(a,b)}| ≺ [(η_s/η_u)^{5/2} 1(|a-b|_L ≤ 6ℓ*_u) + 1] 𝒯_{u,D}(|a-b|_L)`.
Evaluated at the energy `E n`. -/
def Step2Eq53PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Z2 (d.L n) × Z2 (d.L n))
    (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ =>
      ((etaT (E n) (s n) / etaT (E n) p.1) ^ ((5 : ℝ) / 2) *
          (if (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) p.1
            then 1 else 0) + 1) *
        tailT (d.L n) (d.W n) (E n) D p.1 (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ))

/-! ## Elementary facts -/

section Elementary

variable (L W : ℕ) [NeZero L] [NeZero W]

theorem lkErrMat_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    0 ≤ lkErrMat L W E u M a b :=
  norm_nonneg _

theorem llErrMat_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (i j : Idx L W) :
    0 ≤ llErrMat L W E u M i j :=
  norm_nonneg _

theorem loopAbs_nonneg (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    0 ≤ loopAbs L W E u M σ a :=
  norm_nonneg _

/-- `J*_{u,D} ≥ 1` (`def_Ju`). -/
theorem one_le_jStarMat (hW : 1 ≤ W) (E D u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    1 ≤ jStarMat L W E D u M := by
  unfold jStarMat
  have h : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun p : Z2 L × Z2 L =>
        lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ)) :=
    Finset.le_sup'_of_le _ (Finset.mem_univ ((0 : Z2 L), (0 : Z2 L)))
      (div_nonneg (lkErrMat_nonneg L W E u M _ _) (tailT_pos hW L E D u _).le)
  linarith

/-- The `J*` bound: `|(𝓛-𝒦)_{ab}| ≤ J*_{u,D} 𝒯_{u,D}(|a-b|_L)` (`shoellJJ`). -/
theorem lkErrMat_le_jStarMat_mul_tailT (hW : 1 ≤ W) (E D u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a b : Z2 L) :
    lkErrMat L W E u M a b ≤
      jStarMat L W E D u M * tailT L W E D u (zdist2 L (a - b) : ℝ) := by
  have hT : 0 < tailT L W E D u (zdist2 L (a - b) : ℝ) := tailT_pos hW L E D u _
  have h1 : lkErrMat L W E u M a b / tailT L W E D u (zdist2 L (a - b) : ℝ) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Z2 L × Z2 L =>
          lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ)) :=
    Finset.le_sup' (fun p : Z2 L × Z2 L =>
      lkErrMat L W E u M p.1 p.2 / tailT L W E D u (zdist2 L (p.1 - p.2) : ℝ))
      (Finset.mem_univ (a, b))
  have h2 := (div_le_iff₀ hT).1 h1
  unfold jStarMat
  nlinarith

end Elementary

end RBM.Path
