module

public import Mathlib

@[expose] public section

/-!
# Delocalization of two-dimensional random band matrices

Statements of Theorems 2.2–2.5 of S. Dubova, K. Yang, H.-T. Yau and J. Yin, *Delocalization of
two-dimensional random band matrices*, arXiv:2503.07606, with the definitions they use. This file
imports Mathlib and nothing else; the proofs are in the library `RBM2D`, and `Solution.lean`
connects each statement to the theorem of the library that proves it.

The model is the complex Gaussian block band matrix of the paper's §2.1 on the torus `Z_L²`
(`RBM.Gauss`): `L²` blocks of size `W × W`, `N = W²L²`, band width `W ≥ N^𝔠`. The four statements
are the closed propositions `RBM.Endpoints.decol`, `locSC`, `QUE` and `QDiff`, made along any
admissible sequence of sizes; they have no hypotheses other than their parameters.
`docs/PAPER-VS-LEAN.md` lists every difference from the printed statements. Theorem 2.6 (bulk
universality), which the library proves from one external input, is not stated here.
-/

section
namespace RBM
open Finset Matrix
/-- The index set of the paper: the discrete torus `Z_L^2`. -/
abbrev Z2 (L : ℕ) := ZMod L × ZMod L
section Defs
variable (L : ℕ)
/-- The nearest-neighbour support `{(0,0), (1,0), (-1,0), (0,1), (0,-1)} ⊆ Z_L^2`. -/
def sbSupport : Finset (Z2 L) := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The generating kernel of `S^(B)`: the value `1/5` on the five-point
nearest-neighbour support, zero elsewhere. -/
noncomputable def sbKernel : Z2 L → ℂ :=
  fun u => if u ∈ sbSupport L then (5 : ℂ)⁻¹ else 0

/-- The block covariance matrix `S^(B)` of Section 2.1, on `Z_L^2`. -/
noncomputable def SB : Matrix (Z2 L) (Z2 L) ℂ := circulant (sbKernel L)
end Defs
end RBM
end
section
namespace RBM
open Matrix Finset
open scoped Kronecker
section Paper
variable (L W : ℕ) [NeZero L] [NeZero W]
/-- The block containing a one-dimensional coordinate. -/
def blk (i : ZMod (W * L)) : ZMod L := ((i.val / W : ℕ) : ZMod L)

/-- A zero-based version of the paper's interval `I_a`. -/
def I₁ (a : ZMod L) : Finset (ZMod (W * L)) :=
  (Finset.range W).image fun α => ((a.val * W + α : ℕ) : ZMod (W * L))

/-- The paper's two-dimensional block `I_a^(2) = I_(a₁) × I_(a₂)`. -/
def Iblk (a : Z2 L) : Finset (Z2 (W * L)) := (I₁ L W a.1).product (I₁ L W a.2)

/-- The matrix `E_a` in `Def_matE` at literal paper indices. -/
noncomputable def Epaper (a : Z2 L) :
    Matrix (Z2 (W * L)) (Z2 (W * L)) ℂ :=
  Matrix.of fun i j => if i = j then (W : ℂ)⁻¹ ^ 2 * (if i ∈ Iblk L W a then 1 else 0) else 0
end Paper
end RBM
end
section
namespace RBM
open Matrix
open scoped NNReal Matrix.Norms.Operator
section Defs
variable (L : ℕ) [NeZero L]
/-- The propagator `Θ^(B)_ξ = (1 - ξ S^(B))⁻¹` on `Z_L^2`. -/
noncomputable def Theta (ξ : ℂ) : Matrix (Z2 L) (Z2 L) ℂ :=
  Ring.inverse (1 - ξ • SB L)
end Defs
end RBM
end
section
namespace RBM
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹
end RBM
end
section
namespace RBM.Gauss
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
variable (L W : ℕ) [NeZero L] [NeZero W]
/-- The exact fine-lattice index set of Section 2.1. -/
abbrev Idx := Z2 (W * L)

/-- The real form of the paper's variance profile. -/
noncomputable def svar (i j : Idx L W) : ℝ :=
  if (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L
  then (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 else 0

omit [NeZero L] [NeZero W] in
theorem svar_nonneg (i j : Idx L W) : 0 ≤ svar L W i j := by
  unfold svar
  split_ifs <;> positivity

/-- A finite injective key, used only to orient independent off-diagonal entries. -/
noncomputable def idxKey (i : Idx L W) : ℕ := (Fintype.equivFin (Idx L W) i).val

/-- Two real coordinates per oriented pair.  The lower-triangular and imaginary diagonal
coordinates are unused independent noise; this choice makes the product index simple. -/
abbrev Coord := Idx L W × Idx L W × Bool

/-- The finite product sample space. -/
abbrev Ω := Coord L W → ℝ

/-- Diagonal coordinate variance `S_ii`; off-diagonal coordinate variance `S_ij/2`. -/
noncomputable def gvar (c : Coord L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svar L W c.1 c.2.1 else svar L W c.1 c.2.1 / 2, by
    split_ifs
    · exact svar_nonneg L W _ _
    · exact div_nonneg (svar_nonneg L W _ _) (by norm_num)⟩

/-- An entry of the Hermitian matrix, oriented by `idxKey`. -/
noncomputable def Xentry (ω : Ω L W) (i j : Idx L W) : ℂ :=
  if idxKey L W i < idxKey L W j then
    (ω (i, j, true) : ℂ) + Complex.I * (ω (i, j, false) : ℂ)
  else if idxKey L W j < idxKey L W i then
    (ω (j, i, true) : ℂ) - Complex.I * (ω (j, i, false) : ℂ)
  else (ω (i, j, true) : ℂ)

/-- The fixed one-time Gaussian matrix. -/
noncomputable def Xmat (ω : Ω L W) : Matrix (Idx L W) (Idx L W) ℂ :=
  Matrix.of fun i j => Xentry L W ω i j

/-- Only the size data needed by the Gaussian construction.  Quantitative bandwidth
hypotheses belong to the later asymptotic estimates. -/
structure Sizes where
  L : ℕ → ℕ
  W : ℕ → ℕ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n
namespace Sizes
variable (d : Sizes)
instance neZeroL (n : ℕ) : NeZero (d.L n) :=
  ⟨(Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (d.three_le_L n)).ne'⟩
instance neZeroW (n : ℕ) : NeZero (d.W n) := ⟨(d.W_pos n).ne'⟩

/-- The full matrix dimension along this admissible sequence. -/
def size (n : ℕ) : ℕ := (d.W n * d.L n) ^ 2

/-- A coordinate records its size parameter as well as the entry and real/imaginary tag. -/
abbrev SeqCoord := Σ n : ℕ, Coord (d.L n) (d.W n)

/-- One common sample space for all sizes. -/
abbrev SeqΩ := SeqCoord d → ℝ

noncomputable def seqGvar (c : SeqCoord d) : ℝ≥0 :=
  gvar (d.L c.1) (d.W c.1) c.2

/-- Independent Gaussian coordinates for every size in one countable product. -/
noncomputable def seqP : Measure (SeqΩ d) :=
  Measure.infinitePi fun c => gaussianReal 0 (seqGvar d c)

/-- The coordinate vector at one size, extracted from the common product. -/
def slice (n : ℕ) (ω : SeqΩ d) : Ω (d.L n) (d.W n) := fun c => ω ⟨n, c⟩

/-- The size-`n` matrix on the common probability space. -/
noncomputable def seqXmat (n : ℕ) (ω : SeqΩ d) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  Xmat (d.L n) (d.W n) (slice d n ω)
end Sizes
end RBM.Gauss
end
section
namespace RBM
open Complex RBM.Gauss
/-- `ℓ(z) = min(η^{-1/2}, L) + 1`, `η = Im z` (`def_ellz`). -/
noncomputable def ellz (L : ℕ) (z : ℂ) : ℝ :=
  min (z.im ^ (-(1 / 2 : ℝ))) (L : ℝ) + 1

/-- `M_η = W² ℓ(z)² η` (`def_meta`, `d = 2`). -/
noncomputable def Meta (L W : ℕ) (z : ℂ) : ℝ :=
  (W : ℝ) ^ 2 * ellz L z ^ 2 * z.im
end RBM
end
section
namespace RBM.Endpoints
open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes
/-- The semicircle Stieltjes transform, by the paper's integral (Section 2.1):
`m(z) = ∫_{-2}^{2} (2π)⁻¹ √(4-x²) / (x - z) dx`. -/
noncomputable def mSC (z : ℂ) : ℂ :=
  ∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)

/-- `(μ, ψ)` is an orthonormal eigenbasis of `H`: `ψ k` are orthonormal for the
standard inner product and `H ψ_k = μ_k ψ_k`. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

/-- The admissible-sequence hypotheses shared by all five statements: size `N → ∞` and
the bandwidth condition `(Main_DEL_COND)` `W ≥ N^𝔠`, eventually. -/
def Admissible (𝔠 : ℝ) (d : Sizes) : Prop :=
  Tendsto (fun n => d.size n) atTop atTop ∧
    ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)

/-- The Green function of the size-`n` band matrix. -/
noncomputable def Gn (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) :
    Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ :=
  green (seqXmat d n ω) z

/-- The spectral domain of `MR:locSC`/`MR:QDiff`:
`z = E + iη`, `|E| ≤ 2 - κ`, `N^{-1+τ} ≤ η ≤ 1`. -/
def locDomain (N : ℕ) (κ τ : ℝ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 1

/-- The good event of `MR:decol`: for every orthonormal eigenbasis, every eigenvector
with eigenvalue in `[-2+κ, 2-κ]` has `‖ψ‖²_∞ ≤ N^{-1+τ}`. -/
def decolEvent (d : Sizes) (n : ℕ) (κ τ : ℝ) (ω : SeqΩ d) : Prop :=
  ∀ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ →
      ∀ k, μ k ∈ Set.Icc (-2 + κ) (2 - κ) →
        ∀ x, ‖ψ k x‖ ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ)

/-- **Delocalization `MR:decol`.** -/
def decol : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop,
        seqP d {ω | ¬ decolEvent d n κ τ ω} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **Local semicircle law `MR:locSC`**, both `(G_bound)` and `(G_bound_ave)`; `N₀` is uniform
over the `N`-dependent spectral domain. -/
def locSC : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z →
        -- (G_bound)
        seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
            ‖Gn d n ω z x y - (if x = y then mSC z else 0)‖ ≤
              (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z)} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        -- (G_bound_ave)
        seqP d {ω | ¬ ∀ a : Z2 (d.L n),
            ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x -
                mSC z‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- The window `𝒥_E = {k : |λ_k - E| ≤ N^{-1-τ} W^{2/3}}` for eigenvalues `μ`. -/
def window {ι : Type*} (N W : ℕ) (τ E : ℝ) (μ : ι → ℝ) (k : ι) : Prop :=
  |μ k - E| ≤ (N : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3)

/-- The failure event of `(Meq:QUE)`: some orthonormal eigenbasis has `k, k' ∈ 𝒥_E` with
`|N ψ_k^*(E_a - N⁻¹) ψ_{k'}|² ≥ N^{-τ/6}`. -/
def queBad (d : Sizes) (n : ℕ) (τ E : ℝ) (a : Z2 (d.L n)) (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k k', window (d.size n) (d.W n) τ E μ k ∧
        window (d.size n) (d.W n) τ E μ k' ∧
        ((d.size n : ℕ) : ℝ) ^ (-τ / 6) ≤
          ‖((d.size n : ℕ) : ℂ) *
              (star (ψ k) ⬝ᵥ ((Epaper (d.L n) (d.W n) a -
                ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *ᵥ ψ k'))‖ ^ 2

/-- The failure event of `(Meq:QUE2)` for a block set `A`. -/
def que2Bad (d : Sizes) (n : ℕ) (τ E : ℝ) (A : Finset (Z2 (d.L n)))
    (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k, window (d.size n) (d.W n) τ E μ k ∧
        (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ) ^ (1 + τ / 6) ≤
          |∑ a ∈ A, ∑ x ∈ Iblk (d.L n) (d.W n) a, ‖ψ k x‖ ^ 2 -
            (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ)|

/-- **Generalized QUE `MR:QUE`**, `(Meq:QUE)` and `(Meq:QUE2)`.  The paper's `D` is unused and
omitted; `(Meq:QUE2)` is stated for nonempty `A`. -/
def QUE : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ τ : ℝ, 0 < τ → τ < 𝔠 / 2 → ∀ κ : ℝ, 0 < κ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| < 2 - κ →
        (∀ a : Z2 (d.L n),
          seqP d {ω | queBad d n τ E a ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6))) ∧
        (∀ A : Finset (Z2 (d.L n)), A.Nonempty →
          seqP d {ω | que2Bad d n τ E A ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6)))

/-- `tr(G E_a G^σ E_b)` with `G^σ = G†` (`σ = false`) or `G` (`σ = true`). -/
noncomputable def trGEGE (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) (σ : Bool)
    (a b : Z2 (d.L n)) : ℂ :=
  Matrix.trace (Gn d n ω z * Epaper (d.L n) (d.W n) a *
    (if σ then Gn d n ω z else (Gn d n ω z)ᴴ) * Epaper (d.L n) (d.W n) b)

/-- The deterministic profile `W^{-2} (ξ/(1 - ξ S^(B)))_{ab} = W^{-2} ξ (Θ_ξ)_{ab}` with
`ξ = |m|²` (`σ = false`) or `ξ = m²` (`σ = true`), `m = m(z)`. -/
noncomputable def profile (L W : ℕ) [NeZero L] (z : ℂ) (σ : Bool)
    (a b : Z2 L) : ℂ :=
  let ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ)
  ((W : ℂ) ^ 2)⁻¹ * (ξ * Theta L ξ a b)

/-- **Quantum diffusion `MR:QDiff`**: `(Meq:QdW1)`/`(Meq:QdW2)` (`σ = false/true`) with
probability `≥ 1 - N^{-D}`, and `(Meq:QdS1)`/`(Meq:QdS2)` for the expectation. -/
def QDiff : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z → ∀ σ : Bool,
        seqP d {ω | ¬ ∀ a b : Z2 (d.L n),
            ‖trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z ^ 2} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        ∀ a b : Z2 (d.L n),
          ‖(∫ ω, trGEGE d n ω z σ a b ∂(seqP d)) -
              profile (d.L n) (d.W n) z σ a b‖ ≤
            Meta (d.L n) (d.W n) z ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τ
end RBM.Endpoints
end

/-! ## The statements -/

section
namespace RBM.Endpoints

/-- Theorem 2.2: delocalization of the bulk eigenvectors; the statement is `RBM.Endpoints.decol`. -/
theorem theorem_2_2 : decol := by
  sorry

/-- Theorem 2.3: the local semicircle law, (4) and (5); the statement is `RBM.Endpoints.locSC`. -/
theorem theorem_2_3 : locSC := by
  sorry

/-- Theorem 2.4: generalized quantum unique ergodicity, (8) and (9); the statement is `RBM.Endpoints.QUE`. -/
theorem theorem_2_4 : QUE := by
  sorry

/-- Theorem 2.5: quantum diffusion, (10)–(13); the statement is `RBM.Endpoints.QDiff`. -/
theorem theorem_2_5 : QDiff := by
  sorry

end RBM.Endpoints
end
