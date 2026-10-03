/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Endpoints
import RBM2D.Evolution.Defs
import RBM2D.Main.DecolFromLocal
import RBM2D.Main.QUEFromQDiff
import Mathlib.Probability.Moments.SubGaussian

/-!
# The reduction of `BUniv` to its inputs

Paper: arXiv:2503.07606, `Thm: B_Univ` (`eq:universality`) and its proof.

Every statement here is a `Prop`-valued `def`.  Its docstring names the paper label and its uses
(by declaration name; the users are the other statements of this file, `RBM.Endpoints.BUniv`,
and the reduction statements `Infty1Row`, `UnivMainRow`, `ClaimRow`, `EMCTE2Row`, `JakUywRow`,
`OURow`).

Layout.
* Vocabulary: the OU carrier `ouP`, the OU marginal `ouMat`, `stieltjesN`, `queBadMat`, the
  functionals `L1t`, `L2t`, the OU time `ouTStar`.
* The external input `L32` ([32] Thm 2.2, complex Hermitian, unit density).
* The internal inputs: `GUELocal`, the OU claims `OUQUE`, `OUDiag` (the resolvent estimates after
  `417`), `P7Out`, `P7ExpOut`.
* The Claim `(417)` and its reduction: `Claim417`, `EMCTE2`, `Jak`, `Uyw`.
* The Green-to-correlation comparison `GreenCorr` with the a priori bound `AprioriImM`.
* The two limits `Infty1` (`1infyuniv`), `UnivMain` (`univ-main`), and `bUniv_of_steps`.
* The reduction statements and the conditional theorem `BUnivOfInputs`.
* Namespace `RBM.Univ.PinsCheck`: a degenerate-case check.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints

/-! ## Vocabulary -/

section Vocab

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The OU carrier: the band coordinates under `P L W` and independent GUE coordinates under
`gueP L W` (the OU process in the proof of `Thm: B_Univ`, with `𝐇_0 = H`). -/
def ouP : Measure (Ω L W × Ω L W) := (P L W).prod (gueP L W)

/-- The one-time law of the matrix OU process in the proof of `Thm: B_Univ`,
`𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'` with `H'` an independent GUE (`E|h'_ij|² = 1/N`).
Used in `OUQUE`, `OUDiag`, `Claim417`, `EMCTE2`, `Jak`, `Uyw`, `AprioriImM`, `GreenCorr`,
`Infty1`, `UnivMain`. -/
def ouMat (t : ℝ) (ω : Ω L W × Ω L W) : Matrix (Idx L W) (Idx L W) ℂ :=
  Real.exp (-t / 2) • Xmat L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω.2

theorem ouMat_isHermitian (t : ℝ) (ω : Ω L W × Ω L W) : (ouMat L W t ω).IsHermitian :=
  ((Xmat_isHermitian L W ω.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian L W ω.2).smul (IsSelfAdjoint.all _))

/-- `𝐇_0 = H`. -/
theorem ouMat_zero (ω : Ω L W × Ω L W) : ouMat L W 0 ω = Xmat L W ω.1 := by
  simp [ouMat]

/-- `m(z) = N⁻¹ tr (M - z)⁻¹` (`m_t` in the proof of `Thm: B_Univ`, after `417`).  Used in
`Claim417`, `EMCTE2`, `AprioriImM`, `GUELocal`. -/
def stieltjesN {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * (green M z).trace

/-- The failure event of `(Meq:QUE)` for an arbitrary matrix `M` of size `N`: some
orthonormal eigenbasis has `k, k' ∈ 𝒥_E` with `|N ψ_k^*(E_a - N⁻¹) ψ_{k'}|² ≥ N^{-τ/6}`.
Definitionally the body of `RBM.Endpoints.queBad`.  Used in `OUQUE`. -/
def queBadMat (N : ℕ) (τ E : ℝ) (a : Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=
  ∃ (μ : Idx L W → ℝ) (ψ : Idx L W → Idx L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧
      ∃ k k', window N W τ E μ k ∧ window N W τ E μ k' ∧
        (N : ℝ) ^ (-τ / 6) ≤
          ‖(N : ℂ) * (star (ψ k) ⬝ᵥ ((Epaper L W a - (N : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *ᵥ ψ k'))‖ ^ 2

/-- `S°_{xy} = S_{xy} - N⁻¹` (the definition of `S°` in the proof of `Thm: B_Univ`).  Used in
`L1t`, `L2t`, `Jak`, `Uyw`. -/
def Scirc (x y : Idx L W) : ℂ := Spaper L W x y - (((W * L) ^ 2 : ℕ) : ℂ)⁻¹

/-- `G ∈ {R, R^*}`: `b = true` is `R = (M - z)⁻¹`, `b = false` is `R^*`. -/
def gSel (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) (b : Bool) : Matrix (Idx L W) (Idx L W) ℂ :=
  if b then green M z else (green M z)ᴴ

/-- `L_{1,t}(z)` of the proof of `Thm: B_Univ` at the matrix `M = 𝐇_t`.  Used in `EMCTE2`. -/
def L1t (M : Matrix (Idx L W) (Idx L W) ℂ) (z : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖(((W * L) ^ 2 : ℕ) : ℂ)⁻¹ * ∑ a, ∑ b,
      (gSel L W M z b₁ * gSel L W M z b₁) a a * Scirc L W a b * gSel L W M z b₂ b b‖

/-- `L_{2,t}(z₁, z₂)` of the proof of `Thm: B_Univ` at the matrix `M = 𝐇_t`.  Used in `EMCTE2`. -/
def L2t (M : Matrix (Idx L W) (Idx L W) ℂ) (z₁ z₂ : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖((((W * L) ^ 2 : ℕ) : ℂ)⁻¹) ^ 2 * ∑ a, ∑ b,
      (gSel L W M z₁ b₁ * gSel L W M z₁ b₁) a b * Scirc L W a b *
        (gSel L W M z₂ b₂ * gSel L W M z₂ b₂) b a‖

end Vocab

/-- The OU time `t* = N^{-1+τ_U}` (the choice of `t*` in the proof of `Thm: B_Univ`) at size
index `n`. -/
def ouTStar (d : Sizes) (τU : ℝ) (n : ℕ) : ℝ := ((d.size n : ℕ) : ℝ) ^ (-1 + τU)

/-! ## The external input: [32] Theorem 2.2 -/

/-- `m_V(z) = N⁻¹ ∑_i (v_i - z)⁻¹` ([32] (2.2)). -/
def mV {ι : Type*} [Fintype ι] (v : ι → ℝ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹

/-- [32] Definition 2.1: `V = diag v` is `(g, G)`-regular, (2.2) and (2.3). -/
def IsRegular32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (mV v ⟨E, η⟩).im ∧ (mV v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card ι : ℝ) ^ CV

/-- [32] (2.5): `m` solves the free-convolution equation on the upper half plane, `Im m > 0`. -/
def IsFreeConv32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹

/-- [32] (2.1) with GOE → GUE: `V + √t H'`, `H' = Xmat` under `gueP` (`E|h'_ij|² = 1/N`). -/
def dbmMat (L W : ℕ) [NeZero L] [NeZero W] (v : Idx L W → ℝ) (t : ℝ) (ω : Ω L W) :
    Matrix (Idx L W) (Idx L W) ℂ :=
  Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Xmat L W ω

theorem dbmMat_isHermitian (L W : ℕ) [NeZero L] [NeZero W] (v : Idx L W → ℝ) (t : ℝ)
    (ω : Ω L W) : (dbmMat L W v t ω).IsHermitian :=
  (Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).add
    ((Xmat_isHermitian L W ω).smul (IsSelfAdjoint.all _))

/-- The semicircle density `ρ_sc(E) = (2π)⁻¹ √(4 - E²)` (`Real.sqrt` is `0` off `[-2, 2]`). -/
def rhoSC (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / (2 * Real.pi)

/-- **`L32`: [32] (`LANDON20191137`) Theorem 2.2, complex Hermitian (GUE) version, unit
density**, as stated in arXiv:1609.09011v4 (30 Sep 2026): its (2.9) carries the factors
`ρ_fc^{-k}`, `ρ_sc^{-k}` that earlier versions omitted, and the Remark after its Theorem 2.2
states that the results hold also for the complex Hermitian case.  Used at `(1infyuniv)`, as
cited in the paragraph after `univ-main`.
* Premises: [32] Definition 2.1 ((2.2), (2.3)), (2.5)–(2.6), (2.8), `|E| ≤ qG`, required
  eventually along a size sequence with `size n → ∞`; the matrix is `diag v + √t · GUE_N` with
  `N = (W L)²`.
* Conclusion: (2.9) of v4 (with the factors `ρ_fc^{-k}`, `ρ_sc^{-k}`), written
  by the change of variables `α = ρβ` as the test function dilated by each side's own density,
  in the eigenvalue-sum form `kPoint`; the rate `C N^{-κ}` weakened to `→ 0`.
* `size n → ∞` is a hypothesis: for a constant size sequence the conclusion would force an
  equality of two finite-`N` quantities.

Used in `Infty1Row` (`(1infyuniv)` from `L32`, `locSC`, `GUELocal`) and in `BUnivOfInputs`.
This is the only external input. -/
def L32 : Prop :=
  ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ n, Idx (d.L n) (d.W n) → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ n in atTop,
      ((d.size n : ℕ) : ℝ) ^ δ / ((d.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((d.size n : ℕ) : ℝ) ^ (-δ) ∧ G n ≤ ((d.size n : ℕ) : ℝ) ^ (-δ) ∧
      g n * ((d.size n : ℕ) : ℝ) ^ σ ≤ t n ∧ t n ≤ ((d.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |E n| ≤ q * G n ∧
      IsRegular32 (v n) (g n) (G n) c C CV ∧ IsFreeConv32 (v n) (t n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨E n, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
        Tendsto (fun n =>
          (∫ ω, kPoint k (fun α => O (ρ n • α)) (E n)
              (dbmMat_isHermitian (d.L n) (d.W n) (v n) (t n) ω).eigenvalues
              ∂(gueP (d.L n) (d.W n))) -
          (∫ ω, kPoint k (fun α => O (rhoSC (E n) • α)) (E n)
              (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues ∂(gueP (d.L n) (d.W n))))
          atTop (𝓝 0)

/-! ## Internal inputs: the GUE local law, the OU claims, the loop estimates -/

/-- **`GUELocal`**: a weak averaged bulk local law of the `N × N` GUE, `N = (W L)²`:
`|m_N(z) - m(z)| ≤ N^τ (N Im z)^{-1/2}` for `Im z ≥ N^{-1+τ}` up to `Im z ≤ 10` ([32] Def 2.1's
range), with the union over `z` inside the probability.  The precision `(Nη)^{-1/2}` (not the
optimal `(Nη)^{-1}`) is what the uses need: the bounds `c ≤ Im m_V ≤ C` of [32] (2.2) on
`η ≥ N^{-1+δ}` and a polynomial rate for `ρ_fc → ρ_sc`.
Not stated in the paper: the paragraph after `univ-main` cites only `MR:locSC` and [32]; it is
needed to move the GUE statistics from energy `0` (where [32] compares) to `E` (the GUE
translation).  In d = 2 no admissible band profile is flat (`card_sbSupport = 5 < L²`), so the
GUE local law cannot be obtained from the band local law.  Used in `Infty1Row` and
`BUnivOfInputs`. -/
def GUELocal : Prop :=
  ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
  ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      gueP (d.L n) (d.W n) {ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧
          ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
          ((d.size n : ℕ) : ℝ) ^ τ / Real.sqrt (((d.size n : ℕ) : ℝ) * z.im) <
            ‖stieltjesN (Xmat (d.L n) (d.W n) ω) z - msc z‖} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- **`OUQUE`: the first `𝐇_t` claim of the resolvent estimates after `417`** — `(Meq:QUE)` holds
for `𝐇_t` with `τ = 𝔠/3`, uniformly in `t ∈ [0, t*]`, `t* = N^{-1+τ_U}` (the paper: "details
identical to Section 7.2 of [YY_25]").  Only the `(Meq:QUE)` half is stated: `(Meq:QUE2)` for
`𝐇_t` has no use in the proof of `Thm: B_Univ`.  At `t = 0` it contains the `(Meq:QUE)` half of
`QUE` at `τ = 𝔠/3` (law transfer `ouMat_zero`).  Used in `JakUywRow` (the bad event in the proof
of `uywy7723r3rf`, with the threshold `N^{-𝔠/36}`). -/
def OUQUE (𝔠 : ℝ) (d : Sizes) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
    ∀ E : ℝ, |E| < 2 - κ → ∀ a : Z2 (d.L n),
      ouP (d.L n) (d.W n)
          {ω | queBadMat (d.L n) (d.W n) (d.size n) (𝔠 / 3) E a (ouMat (d.L n) (d.W n) t ω)} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(𝔠 / 3) / 6))

/-- **`OUDiag`: the second `𝐇_t` claim of the resolvent estimates after `417`** — for
`t ∈ [0, t*]`, `|E| < 2 - κ`, `η = N^{-1+2τ_U}`: `max_x |(𝐑_t(E + iη))_{xx}| ≺ 1`, union over `x`
inside `P`.  Used in `JakUywRow` (with it, the weights `∏ Im m_t(z_j)` of `Jak`, `Uyw` are
`≤ N^{Cτ_U}` off an event of probability `≤ N^{-D}`, by monotonicity of `η ↦ η Im m(E + iη)`;
and `decol` and the eigenvalue counting for `𝐇_t` follow: `|ψ_α(x)|² ≤ η Im 𝐑_xx`). -/
def OUDiag (d : Sizes) (τU : ℝ) : Prop :=
  ∀ κ ε D : ℝ, 0 < κ → 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
    ∀ E : ℝ, |E| < 2 - κ →
      ouP (d.L n) (d.W n) {ω | ∃ x : Idx (d.L n) (d.W n),
          ((d.size n : ℕ) : ℝ) ^ ε <
            ‖green (ouMat (d.L n) (d.W n) t ω)
                ((E : ℂ) + ((((d.size n : ℕ) : ℝ) ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) x x‖} ≤
        ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

/-- The two `𝐇_t` claims for all small `τ_U` (the resolvent estimates after `417`: "for
`τ_U > 0` sufficiently small").  Used in `JakUywRow`; obtained from `OURow`. -/
def OUClaims : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → OUQUE 𝔠 d τU ∧ OUDiag d τU

/-- **`P7Out`**: the loop estimates (`RBM.Ind.MLConcl`: the conclusions of `ML:GLoop`,
`ML:GLoop_expec`, `ML:GtLocal`) for every bulk energy sequence and every time sequence with
`1 - t ≥ N^{-1+τ}`.  Used in `OURow`. -/
def P7Out : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ τ : ℝ, 0 < τ → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
      (∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n) → RBM.Ind.MLConcl d E t

/-- **`P7ExpOut`**: the improved expectation bound `RBM.Evol.MLExpConcl` (`ML:exp`,
`Evolution/Defs.lean`) for every bulk energy sequence and every time sequence with
`1 - t ≥ N^{-1+τ}`, in the shape of `P7Out`.  It is the initial term of (7.29) and is not
contained in `P7Out := ∀ …, MLConcl d E t`.  Used in `OURow`; it follows from the loop estimates
by `RBM.Ind.mlExp`. -/
def P7ExpOut : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ τ : ℝ, 0 < τ → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
      (∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n) → RBM.Evol.MLExpConcl d E t

/-! ## The Claim `(417)` and its reduction -/

/-- The spectral window of the Claim before `(417)`: `|E_j - E| ≤ C₀/N` (the paper's `O(N^{-1})`
with an explicit `C₀`), `N^{-1-τ_U} ≤ η_j ≤ N^{-1+τ_U}`. -/
def InWindow (d : Sizes) (E C₀ τU : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re - E| ≤ C₀ / ((d.size n : ℕ) : ℝ) ∧ ((d.size n : ℕ) : ℝ) ^ (-1 - τU) ≤ z.im ∧
    z.im ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τU)

/-- **`Claim417`: the Claim, `(417)`**: for `n_f` factors,
`sup_{0≤t≤t*} |E ∏ Im m_t(z_i) - E ∏ Im m_{t*}(z_i)| ≤ N^{-c' + C_n τ_U}`, eventually,
for every `C₀`.  `c'`, `C_n` are parameters; the chosen value is `c' = 𝔠/36`.
Used in `GreenCorr` (hypothesis) and `ClaimRow` (conclusion). -/
def Claim417 (d : Sizes) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ, (∀ i, InWindow d E C₀ τU n (z i)) →
    ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
      |(∫ ω, ∏ i, (stieltjesN (ouMat (d.L n) (d.W n) t ω) (z i)).im ∂(ouP (d.L n) (d.W n))) -
        ∫ ω, ∏ i, (stieltjesN (ouMat (d.L n) (d.W n) (ouTStar d τU n) ω) (z i)).im
          ∂(ouP (d.L n) (d.W n))| ≤
        ((d.size n : ℕ) : ℝ) ^ (-c' + Cn * τU)

/-- **`EMCTE2`** (`EMCTE2` in the proof of `Thm: B_Univ`: "argue as in Step 3 of the proof of
Theorem 2.6 in [YY_25]", `(2.28)` there), in the **weighted** form: the left side of `(417)` is
`≺ N^{-1+C_nτ_U}` times a bound `B` on `E[(∏_{j≠u} Im m_s(z_j)) L_{1,s}(z_u)]` (all `u`) and on
`E[(∏_{k∉{u,v}} Im m_s(z_k)) L_{2,s}(z_u, z_v)]` (`u ≠ v`), `s ∈ [0, t*]`.  The weights are
the factors that the OU generator leaves on the undifferentiated `Im m`; the paper's display
drops them.  With the weights the bound is multiplicative in `B` with no additive tail (the
generator identity is exact).  The paper's `max_{u≠v} E[L_1(z_u) + L_2(z_u,z_v)]` is read as a
bound on each term (for `n_f = 1` the set `u ≠ v` is empty).  `≺` of a deterministic quantity is
written with an explicit `N^ε`.  `0 ≤ B` is needed: at `n_f = 0` both families of hypotheses on
`B` are empty and the left side is `0`.  Used in `ClaimRow`. -/
def EMCTE2 (d : Sizes) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow d E C₀ τU n (z i)) → ∀ B : ℝ, 0 ≤ B →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar d τU n → ∀ u : Fin nf,
        ∫ ω, (∏ j ∈ Finset.univ.erase u,
            (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z j)).im) *
          L1t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z u) ∂(ouP (d.L n) (d.W n)) ≤ B) →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar d τU n → ∀ u v : Fin nf, u ≠ v →
        ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v,
            (stieltjesN (ouMat (d.L n) (d.W n) s ω) (z k)).im) *
          L2t (d.L n) (d.W n) (ouMat (d.L n) (d.W n) s ω) (z u) (z v)
          ∂(ouP (d.L n) (d.W n)) ≤ B) →
      ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
        |(∫ ω, ∏ i, (stieltjesN (ouMat (d.L n) (d.W n) t ω) (z i)).im ∂(ouP (d.L n) (d.W n))) -
          ∫ ω, ∏ i, (stieltjesN (ouMat (d.L n) (d.W n) (ouTStar d τU n) ω) (z i)).im
            ∂(ouP (d.L n) (d.W n))| ≤
          ((d.size n : ℕ) : ℝ) ^ ε * ((d.size n : ℕ) : ℝ) ^ (-1 + Cn * τU) * B

/-- **`Jak`: `(jaklsdufowe)`**, with the exponent `c'` (chosen value `𝔠/36`; the paper writes
`𝔠/18`), `≺`-slack `N^ε`, and a weight `∏_{j∈s} Im m_t(z_j)` for every `s`, to match the
weighted `EMCTE2`:
`max_i max_y E[(∏_{j∈s} Im m_t(z_j)) |∑_x (G₁²(z_i))_{xx} S°_{xy} (G₂(z_i))_{yy}|] ≤ N^{1-c'+Cτ_U}`,
for `t ∈ [0,t*]`.  At `s = ∅` this is the paper's display.
Used in `ClaimRow`; obtained from `JakUywRow`. -/
def Jak (d : Sizes) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow d E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
      ∀ (s : Finset (Fin nf)) (i : Fin nf) (y : Idx (d.L n) (d.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ j ∈ s, (stieltjesN (ouMat (d.L n) (d.W n) t ω) (z j)).im) *
          ‖∑ x, (gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z i) b₁ *
              gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z i) b₁) x x *
            Scirc (d.L n) (d.W n) x y *
              gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z i) b₂ y y‖
          ∂(ouP (d.L n) (d.W n)) ≤
          ((d.size n : ℕ) : ℝ) ^ ε * ((d.size n : ℕ) : ℝ) ^ (1 - c' + C * τU)

/-- **`Uyw`: `(uywy7723r3rf)`**, exponent `c'` (chosen value `𝔠/36`), with a
weight `∏_{k∈s} Im m_t(z_k)` for every `s`, to match the weighted `EMCTE2`:
`max_{i≠j} max_y E[(∏_{k∈s} Im m_t(z_k)) |∑_x (G₁²(z_i))_{xy} S°_{xy} (G₂²(z_j))_{yx}|]`
`≺ N^{2-c'+Cτ_U}`, `t ∈ [0,t*]`.  At `s = ∅` this is the paper's display.
Used in `ClaimRow`; obtained from `JakUywRow`. -/
def Uyw (d : Sizes) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow d E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar d τU n →
      ∀ (s : Finset (Fin nf)) (i j : Fin nf), i ≠ j → ∀ (y : Idx (d.L n) (d.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ k ∈ s, (stieltjesN (ouMat (d.L n) (d.W n) t ω) (z k)).im) *
          ‖∑ x, (gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z i) b₁ *
              gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z i) b₁) x y *
            Scirc (d.L n) (d.W n) x y *
              (gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z j) b₂ *
                gSel (d.L n) (d.W n) (ouMat (d.L n) (d.W n) t ω) (z j) b₂) y x‖
          ∂(ouP (d.L n) (d.W n)) ≤
          ((d.size n : ℕ) : ℝ) ^ ε * ((d.size n : ℕ) : ℝ) ^ (2 - c' + C * τU)

/-! ## The Green-to-correlation comparison -/

/-- The a priori bound at the level spacing:
`E (Im m_0(E + i/N))^p ≤ N^ε` eventually.  Used in `GreenCorr`; obtained from `AprioriRow`. -/
def AprioriImM (d : Sizes) (E : ℝ) : Prop :=
  ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∫ ω, (stieltjesN (ouMat (d.L n) (d.W n) 0 ω)
        ((E : ℂ) + ((((d.size n : ℕ) : ℝ))⁻¹ : ℂ) * Complex.I)).im ^ p ∂(ouP (d.L n) (d.W n)) ≤
      ((d.size n : ℕ) : ℝ) ^ ε

/-- **`GreenCorr`: the Green-function-to-correlation comparison** (the paragraph after
`univ-main`: "Theorem 15.3 in [25], Proposition 4.17 in [45], and (2.23) in [YY_25]").
If `(417)` holds for all `n_f ≤ k` at a small enough `τ_U` and the a priori bound holds, the
`k`-point functionals of `𝐇_0` and `𝐇_{t*}` have the same limit.  `τ₀` may depend on
`k, c', C`.  Used in `UnivMainRow`, `BUnivOfInputs`. -/
def GreenCorr (d : Sizes) : Prop :=
  ∀ (E : ℝ) (k : ℕ) (c' : ℝ), 0 < c' → ∀ Cn : ℕ → ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → (∀ nf ≤ k, Claim417 d E nf τU c' (Cn nf)) →
      AprioriImM d E →
      ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
        Tendsto (fun n =>
          (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) 0 ω).eigenvalues
              ∂(ouP (d.L n) (d.W n))) -
          (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) (ouTStar d τU n) ω).eigenvalues
              ∂(ouP (d.L n) (d.W n))))
          atTop (𝓝 0)

/-! ## The two limits and the final combination -/

/-- **`(1infyuniv)`** at `τ_U`: the `𝐇_{t*}` functional against the GUE
(`𝐇_∞`, law `gueP`).  Used in `bUniv_of_steps`; obtained from `Infty1Row`. -/
def Infty1 (d : Sizes) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) (ouTStar d τU n) ω).eigenvalues
        ∂(ouP (d.L n) (d.W n))) -
    (∫ ω, kPoint k O E (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
        ∂(gueP (d.L n) (d.W n))))
    atTop (𝓝 0)

/-- **`(univ-main)`** at `τ_U`: the band matrix `H = 𝐇_0` (on the carrier `seqP d`, exactly as in
`BUniv`) against `𝐇_{t*}`.  Used in `bUniv_of_steps`; obtained from `UnivMainRow`. -/
def UnivMain (d : Sizes) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k O E (seqXmat_isHermitian d n ω).eigenvalues ∂(seqP d)) -
    (∫ ω, kPoint k O E (ouMat_isHermitian (d.L n) (d.W n) (ouTStar d τU n) ω).eigenvalues
        ∂(ouP (d.L n) (d.W n))))
    atTop (𝓝 0)

/-- The hypothesis of the final combination: for the fixed parameters of `BUniv` there is a
`τ_U > 0` at which both limits hold (the choice of `t*` in the proof of `Thm: B_Univ`:
"`t* = N^{-1+τ_U}` with a fixed (small) `τ_U`"). -/
def StepsAt : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
          ∃ τU : ℝ, 0 < τU ∧ Infty1 d k O E τU ∧ UnivMain d k O E τU

/-- **The final combination**: `(univ-main)` and `(1infyuniv)` at the same `t*` give
`(eq:universality)`, i.e. `BUniv`. -/
theorem bUniv_of_steps (h : StepsAt) : BUniv := by
  intro 𝔠 h𝔠 d hd k hk κ hκ E hE O hO hOc
  obtain ⟨τU, -, h1, h2⟩ := h 𝔠 h𝔠 d hd k hk κ hκ E hE O hO hOc
  have h3 := h2.add h1
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-! ## The reduction statements and the conditional theorem -/

/-- `Claim417` for all `n_f` at `c' = 𝔠/36`, with `C_n` and a `τ₀` for every bulk `E`. -/
def ClaimAll : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ nf : ℕ, ∃ Cn : ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → Claim417 d E nf τU (𝔠 / 36) Cn

/-- `GreenCorr` for every size sequence with `size n → ∞`. -/
def GreenCorrAll : Prop :=
  ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop → GreenCorr d

/-- **The conditional theorem**: its hypotheses are exactly the external `L32`, the endpoint
`locSC`, the internal `GUELocal`, the Claim `(417)` family and the Green-to-correlation
comparison. -/
def BUnivOfInputs : Prop :=
  L32 → locSC → GUELocal → ClaimAll → GreenCorrAll → BUniv

/-- Reduction statement: `(1infyuniv)` for every `τ_U ∈ (0, τ₁]` with some `τ₁ > 0` depending on
`𝔠, d, k, κ, E, O`, from `L32`, `locSC`, `GUELocal`
(conditioning on `H`, GUE unitary invariance, regularity of `V = e^{-t*/2}λ(H) - E` from
`(G_bound_ave)`, dilation by `ρ_fc → ρ_sc(E)`, and the GUE translation).  In d = 2 the
regularity of `V` (`step1Good_highProb`) holds only for `τ_U ≤ 𝔠`, so the range of `τ_U` is
`(0, τ₁]`. -/
def Infty1Row : Prop :=
  L32 → locSC → GUELocal →
    ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
        ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
          ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → Infty1 d k O E τU

/-- Reduction statement: the a priori bound from `locSC` (law transfer `ouMat_zero`, then
`(G_bound)` at `η = N^{-1+τ}` and monotonicity of `η ↦ η Im m(E + iη)`). -/
def AprioriRow : Prop :=
  locSC → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → AprioriImM d E

/-- Reduction statement: `(univ-main)` from the Claim family, `AprioriImM` (via `AprioriRow`) and
`GreenCorr`, plus the law transfer from `seqP d` to `ouP` at `t = 0` (`seqP_map_slice`,
`ouMat_zero`, measurability of `kPoint ∘ eigenvalues`). -/
def UnivMainRow : Prop :=
  ClaimAll → locSC → GreenCorrAll →
    ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∃ τ₀ : ℝ, 0 < τ₀ ∧
        ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
          ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
            UnivMain d k O E τU

/-- Reduction statement (arithmetic): `(EMCTE2)` with `(jaklsdufowe)`, `(uywy7723r3rf)`, all three
weighted, give `(417)` at `c' = 𝔠/36`, with `C_n' = C_n + C + 1` (`Jak` at
`s = univ.erase u` bounds the `L₁` term of `EMCTE2`, `Uyw` at `s = (univ.erase u).erase v` the
`L₂` term). -/
def ClaimRow : Prop :=
  (∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ nf : ℕ, ∃ Cn C : ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      EMCTE2 d E nf τU Cn ∧ Jak d E nf τU C (𝔠 / 36) ∧ Uyw d E nf τU C (𝔠 / 36)) →
  ClaimAll

/-- Reduction statement: the weighted `(EMCTE2)` from the OU generator identity alone (whose only
hypothesis on the spectral parameters is `0 < Im z`); no `𝐇_t` claim is used. -/
def EMCTE2Row : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn : ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → EMCTE2 d E nf τU Cn

/-- Reduction statement: the weighted `(jaklsdufowe)`, `(uywy7723r3rf)` at `c' = 𝔠/36` from
`locSC` and the `𝐇_t` claims (`OUDiag` bounds the weights off a small event). -/
def JakUywRow : Prop :=
  locSC → OUClaims → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C : ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → Jak d E nf τU C (𝔠 / 36) ∧ Uyw d E nf τU C (𝔠 / 36)

/-- Reduction statement: the `𝐇_t` claims from the loop estimates `P7Out`, `P7ExpOut` (and `QUE`,
`locSC` at `t = 0`).  The input `P7ExpOut` is needed because the random-layer argument uses the
expectation bound (2.71), which `P7Out` does not contain. -/
def OURow : Prop := P7Out → P7ExpOut → locSC → QUE → OUClaims

/-- **The reduction statements compose (1)**: `Infty1Row` and `UnivMainRow` give `BUnivOfInputs`
(`τ_U := min τ₀ τ₁`). -/
theorem bUnivOfInputs_of_rows (h1 : Infty1Row) (h2 : UnivMainRow) : BUnivOfInputs := by
  intro h32 hLL hGLL hCl hGC
  apply bUniv_of_steps
  intro 𝔠 h𝔠 d hd k _ κ hκ E hE O hO hOc
  obtain ⟨τ₀, hτ₀, hU⟩ := h2 hCl hLL hGC 𝔠 h𝔠 d hd k κ hκ E hE
  obtain ⟨τ₁, hτ₁, hI⟩ := h1 h32 hLL hGLL 𝔠 h𝔠 d hd k κ hκ E hE O hO hOc
  have hpos : 0 < min τ₀ τ₁ := lt_min hτ₀ hτ₁
  exact ⟨min τ₀ τ₁, hpos, hI _ hpos (min_le_right _ _),
    hU _ hpos (min_le_left _ _) O hO hOc⟩

/-- **The reduction statements compose (2)**: `OURow`, `EMCTE2Row`, `JakUywRow`, `ClaimRow` give
`ClaimAll` from `P7Out`, `P7ExpOut`, `locSC` and `QUE`: `OURow` yields `OUClaims`, which
`EMCTE2Row` and `JakUywRow` combine (with `τ_U := min τ₁ τ₂`) into the hypothesis of
`ClaimRow`. -/
theorem claimAll_of_rows (rC : ClaimRow) (rE : EMCTE2Row) (rJ : JakUywRow) (rO : OURow)
    (h7 : P7Out) (h7e : P7ExpOut) (hLL : locSC) (hQ : QUE) : ClaimAll := by
  have hOU := rO h7 h7e hLL hQ
  apply rC
  intro 𝔠 h𝔠 d hd κ hκ E hE nf
  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := rE 𝔠 h𝔠 d hd κ hκ E hE nf
  obtain ⟨C, τ₂, hτ₂, h2⟩ := rJ hLL hOU 𝔠 h𝔠 d hd κ hκ E hE nf
  refine ⟨Cn, C, min τ₁ τ₂, lt_min hτ₁ hτ₂, fun τU h0 hle => ?_⟩
  have hJU := h2 τU h0 (hle.trans (min_le_right _ _))
  exact ⟨h1 τU h0 (hle.trans (min_le_left _ _)), hJU.1, hJU.2⟩

/-- **The reduction closes**: from the six reduction statements `Infty1Row`, `UnivMainRow`,
`ClaimRow`, `EMCTE2Row`, `JakUywRow`, `OURow`, `BUniv` follows from the external `L32`, the
inputs `P7Out`, `P7ExpOut`, `locSC`, `QDiff` (`QUE` via `QUE_of_QDiff`), and the internal
statements `GUELocal`, `GreenCorrAll`.  Every input other than `L32` is proved: see
`Main/BUniv.lean` (`bUniv_of_g1Row`) and `Main/BUnivHolds.lean` (`bUniv_holds`). -/
theorem bUniv_of_rows (hI : Infty1Row) (hU : UnivMainRow) (hC : ClaimRow) (hE : EMCTE2Row)
    (hJ : JakUywRow) (hO : OURow) :
    L32 → P7Out → P7ExpOut → locSC → QDiff → GUELocal → GreenCorrAll → BUniv :=
  fun h32 h7 h7e hLL hQD hGLL hGC =>
    bUnivOfInputs_of_rows hI hU h32 hLL hGLL
      (claimAll_of_rows hC hE hJ hO h7 h7e hLL (QUE_of_QDiff hQD)) hGC

end RBM.Univ

namespace RBM.Univ.PinsCheck

open MeasureTheory Matrix Filter Topology
open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints

/-! ## A degenerate case -/

/-- Degenerate case: `EMCTE2` at `n_f = 0` holds (both products are `1`); without the
hypothesis `0 ≤ B` it would claim `0 ≤ N^ε N^{…} B` for every `B`, which is false. -/
theorem emcte2_zero (d : Sizes) (E τU Cn : ℝ) : EMCTE2 d E 0 τU Cn := by
  intro C₀ ε _ _
  refine Eventually.of_forall fun n z _ B hB _ _ t _ _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
  positivity

end RBM.Univ.PinsCheck
