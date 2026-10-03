/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltGridQ
import RBM2D.Induction.QopBounds
import RBM2D.Induction.AzumaProxyN
import RBM2D.Induction.QVN
import RBM2D.Induction.SumZeroQ
import RBM2D.Evolution.Case5
import RBM2D.Induction.NonAltGood

/-!
# The martingale part of the `𝒬`-process

Namespace `RBM.Ind`.  Paper: arXiv:2503.07606, Section 5: `Def:QtPt`, `lem_+Q` (`normQA`),
`int_K-L+Q2`, the double sum-zero tensor `(𝒬 ⊗ 𝒬)(𝓔 ⊗ 𝓔)`; and Section 7, Case 5
(`eq:double_sum_zero_tensor`).

## Contents

1. **Vocabulary**: `qqTensorN` (`(𝒬_t ⊗ \bar 𝒬_t) 𝒜`), `qvFormQN` (`qvFormN` with
   `𝓔 ⊗ 𝓔` replaced by `(𝒬_v ⊗ \bar 𝒬_v)(𝓔 ⊗ 𝓔)`), `zVecQN = 𝒬_{u_{j+1}} ZvecN`,
   `yVecQN = 𝒬_{u_{j+1}} YvecN`.
2. `martIncQN_ae_eq`: a.e. `martIncQN_j = zVecQN_j + yVecQN_j`.
3. `qv_at_propagatorQ`: `qvPropagatedN` at the weights
   `κ'_c = Σ_b κ_b Qmat_u(b,c)` (`AltProxyQ_wts`, `AltProxyQ_sum_Qop`, `AltProxyQ_sum_qq`).
4. `doubleSumZero_qqTensorN`: `𝒫 ∘ 𝒬_t = 0` (`qopAlgebra`) in each copy.
5. `QQTensorBoundsN`, `qqTensorBoundsN`: the two-copy form of `normQA` / `lem_+Q` (the paper
   states only the one-copy form).  `qopNorm` and `qopDecay` are applied slice by slice.  Inner copy: every
   slice `c' ↦ conj 𝒜(c,c')` has `HasDecay(t,τ,D)` (`maxDist c' ≤ maxDist (c,c')`).  Outer copy:
   `c ↦ conj (𝒬 S_c)(b')` has `HasDecay(t,τ,D₁)`, `D₁ = D - a - 1`, `a = (k-1)/𝔠`, because a
   spread `c` makes the whole slice `S_c` decay and `𝒬` costs `1 + (L²)^{k-1} ≤ W^{a+1}`.  The
   window is `3ρ`, `ρ = ℓ_t W^τ`: if both blocks have spread `< ρ` and the concatenation has
   spread `≥ 3ρ`, the anchors `b₀`, `b'₀` are `≥ ρ` apart, and the four terms of `𝒬 ⊗ \bar 𝒬`
   (kernel `Qmat_t(b,c) = δ_{bc} - ϑ_t(b) 1[c₀ = b₀]`) only use entries of `𝒜` with anchors
   `≥ ρ` apart.  `AltProxyQ_core` is the algebra for abstract exponents; `qqTensorBoundsN`
   instantiates it with `C' = C + Cτ + 2a + 2`, `C = cPrec 𝔠 k`.
6. `qvFormQN_le_of_bounds`: the explicit Case 5 bound from items 4, 5,
   `qvFormQN = Re UgenPair (𝒬 ⊗ \bar 𝒬)(𝓔 ⊗ 𝓔)` (`AltProxyQ_qvFormQN_eq_re`, as
   `qvFormN_eq_re_UgenPair`) and `ugenPairCase5AltExplicit` with `K = 3 W^{τ'}`.
7. `azumaSubGQ_ugen`, `azumaSubGQ_goodExit`: `azumaSubG_ugen`, `azumaSubG_goodExit` for `zVecQN`,
   `qvFormQN`, with `azumaSubGN`, `hermTestFunLoopN`, `goodExitMeasN` in place of the hypotheses.
8. `YMomentsQUnifN`, `yMomentsQUnifN`: the `𝒬`-analogue of `YMomentsUnifN`.  The
   stopped increment `1_{j<τ} (𝒰 𝒬 Y)_b` is `1_{j<τ} Σ_c κ'_c Y_c`; the weights `κ'` have `ℓ¹`
   norm at most `(1 + (L²)^{k-1}) (1 + (1-u_m)⁻¹)^k`.  The eight moment fields for an arbitrary
   weight vector are the theorem `AzumaProxyN_YfieldsW` of `RBM2D.Induction.AzumaProxyN`.

The argument parallels the one-dimensional formalization.  The `d = 2` changes: labels in `Z2 L`
(`𝒫` has `(L²)^{k-1}` terms), `‖ϑ_t‖ ≤ 1` from the entries `|Θ_t(x,y)| ≤ (1-t)⁻¹` (no polynomial
loss, no decay input), `W → W²`, `N = W²L²`; the joint `Q ⊗ Q` contraction is replaced by the
Case 5 estimate `ugenPairCase5AltExplicit`.

Private helpers carry the prefix `AltProxyQ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The vocabulary -/

/-- `(𝒬_t ⊗ \bar 𝒬_t) 𝒜`, i.e. `Σ_{c,c'} Qmat_t(b,c) conj (Qmat_t(b',c')) 𝒜(c,c')`. -/
def qqTensorN (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (t : ℝ)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (b b' : Fin k → Z2 L) : ℂ :=
  Qop L t (fun c => starRingEnd ℂ (Qop L t (fun c' => starRingEnd ℂ (A c c')) b')) b

/-- `qvFormN` with `𝓔⊗𝓔` replaced by `(𝒬_v ⊗ \bar 𝒬_v)(𝓔⊗𝓔)`. -/
def qvFormQN (L W : ℕ) [NeZero L] [NeZero W] (E v w : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k → Z2 L) : ℝ :=
  (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
    (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b i)) *
      (starRingEnd ℂ) (∏ i : Fin k,
        ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) (b' i)) *
      qqTensorN L v (eeN L W E v M σ) b b').re

/-- The first-chaos part of the `𝒬`-martingale increment: `𝒬_{u_{j+1}} ZvecN`. -/
def zVecQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  Qop (d.L n) (gridTime s t K n (j + 1)) (ZvecN d E s t K n j σ ω)

/-- The second-order part: `𝒬_{u_{j+1}} YvecN`. -/
def yVecQN (d : Sizes) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ :=
  Qop (d.L n) (gridTime s t K n (j + 1)) (YvecN d E s t K n j σ ω)

/-! ## 2. Linearity of `𝒬_t` and the transposed weights -/

section QopAlg

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem AltProxyQ_Qop_finset_sum {ι : Type*} (t : ℝ) (s : Finset ι)
    (F : ι → (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L t (fun c => ∑ i ∈ s, F i c) a = ∑ i ∈ s, Qop L t (F i) a := by
  unfold Qop Psum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_comm]

private theorem AltProxyQ_Qop_sub (t : ℝ) (A B : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L t (fun c => A c - B c) a = Qop L t A a - Qop L t B a := by
  unfold Qop Psum
  rw [Finset.sum_sub_distrib]
  ring

private theorem AltProxyQ_Qop_add (t : ℝ) (A B : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L t (fun c => A c + B c) a = Qop L t A a + Qop L t B a := by
  unfold Qop Psum
  rw [Finset.sum_add_distrib]
  ring

private theorem AltProxyQ_Qop_zero (t : ℝ) (a : Fin k → Z2 L) :
    Qop L t (fun _ => (0 : ℂ)) a = 0 := by
  simp [Qop, Psum]

/-- The transposed weights: `Σ_b κ_b (𝒬_t F)_b = Σ_c κ'_c F_c` with
`κ'_c = κ_c - Σ_{b : b₀ = c₀} κ_b ϑ_{t,b}` (i.e. `κ'_c = Σ_b κ_b Qmat_t(b, c)`). -/
private def AltProxyQ_wts (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (t : ℝ)
    (κ : (Fin k → Z2 L) → ℂ) (c : Fin k → Z2 L) : ℂ :=
  κ c - ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), κ b * vartheta L t b

private theorem AltProxyQ_sum_Qop (t : ℝ) (κ F : (Fin k → Z2 L) → ℂ) :
    ∑ b, κ b * Qop L t F b = ∑ c, AltProxyQ_wts L t κ c * F c := by
  have key : ∑ b : Fin k → Z2 L, κ b * (Psum L F (b 0) * vartheta L t b) =
      ∑ c : Fin k → Z2 L, (∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0),
        κ b * vartheta L t b) * F c := by
    have h1 : ∀ b : Fin k → Z2 L, κ b * (Psum L F (b 0) * vartheta L t b) =
        ∑ c : Fin k → Z2 L, if c 0 = b 0 then κ b * vartheta L t b * F c else 0 := by
      intro b
      unfold Psum
      rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> ring
    have h2 : ∀ c : Fin k → Z2 L, (∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0),
        κ b * vartheta L t b) * F c =
        ∑ b : Fin k → Z2 L, if c 0 = b 0 then κ b * vartheta L t b * F c else 0 := by
      intro c
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    simp only [h1, h2]
    exact Finset.sum_comm
  unfold Qop AltProxyQ_wts
  simp only [mul_sub, Finset.sum_sub_distrib, sub_mul]
  rw [key]

/-- The double form: `Σ_{b,b'} κ_b conj(κ_{b'}) (𝒬⊗\bar 𝒬 𝒜)_{b,b'} =
Σ_{c,c'} κ'_c conj(κ'_{c'}) 𝒜_{c,c'}`. -/
private theorem AltProxyQ_sum_qq (t : ℝ) (κ : (Fin k → Z2 L) → ℂ)
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) :
    ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * qqTensorN L t A b b' =
      ∑ c, ∑ c', AltProxyQ_wts L t κ c * starRingEnd ℂ (AltProxyQ_wts L t κ c') * A c c' := by
  -- sum over `b` first
  have h1 : ∀ b' : Fin k → Z2 L, ∑ b, κ b * qqTensorN L t A b b' =
      ∑ c, AltProxyQ_wts L t κ c *
        starRingEnd ℂ (Qop L t (fun c' => starRingEnd ℂ (A c c')) b') := fun b' =>
    AltProxyQ_sum_Qop t κ _
  have h2 : ∀ c : Fin k → Z2 L, ∑ b', κ b' * Qop L t (fun c' => starRingEnd ℂ (A c c')) b' =
      ∑ c', AltProxyQ_wts L t κ c' * starRingEnd ℂ (A c c') := fun c =>
    AltProxyQ_sum_Qop t κ _
  calc ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * qqTensorN L t A b b'
      = ∑ b', starRingEnd ℂ (κ b') * ∑ b, κ b * qqTensorN L t A b b' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b', starRingEnd ℂ (κ b') * ∑ c, AltProxyQ_wts L t κ c *
          starRingEnd ℂ (Qop L t (fun c' => starRingEnd ℂ (A c c')) b') := by
        simp only [h1]
    _ = ∑ c, AltProxyQ_wts L t κ c * starRingEnd ℂ
          (∑ b', κ b' * Qop L t (fun c' => starRingEnd ℂ (A c c')) b') := by
        simp only [Finset.mul_sum, map_sum, map_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b' _ => ?_
        ring
    _ = ∑ c, ∑ c', AltProxyQ_wts L t κ c * starRingEnd ℂ (AltProxyQ_wts L t κ c') * A c c' := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [h2 c, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, Complex.conj_conj]
        ring

end QopAlg

/-! ## 3. `martIncQN = zVecQN + yVecQN` -/

section MartInc

variable (d : Sizes)

/-- **`martIncQN_ae_eq`**: a.e., the martingale increment of the
`𝒬`-process is `𝒬_{u_{j+1}}` of the first-chaos part plus `𝒬_{u_{j+1}}` of the remainder,
`martIncQN_j = zVecQN_j + yVecQN_j`.  Proof: `AltGridQ_condExp_aTrueQN` (`𝔼[·|F_j]` commutes with
`𝒬_{u_{j+1}}`), linearity of `Qop`, and `YvecN = martIncN - ZvecN`. -/
theorem martIncQN_ae_eq (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hj1 : gridTime s t K n (j + 1) < 1) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (a : Fin k → Z2 (d.L n)) :
    ∀ᵐ ω ∂(pathP d), martIncQN d E s t K n σ j ω a =
      zVecQN d E s t K n j σ ω a + yVecQN d E s t K n j σ ω a := by
  filter_upwards [AltGridQ_condExp_aTrueQN d E s t K n j hE hj1 σ a] with ω h
  have h1 : (fun c => ZvecN d E s t K n j σ ω c + YvecN d E s t K n j σ ω c) =
      fun c => AvecN d E s t K n (j + 1) σ ω c -
        (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' c | filt d j] ω := by
    funext c
    simp only [YvecN, martIncN]
    ring
  have h2 := AltProxyQ_Qop_add (gridTime s t K n (j + 1)) (ZvecN d E s t K n j σ ω)
    (YvecN d E s t K n j σ ω) a
  have h3 := AltProxyQ_Qop_sub (gridTime s t K n (j + 1)) (AvecN d E s t K n (j + 1) σ ω)
    (fun c => (pathP d)[fun ω' => AvecN d E s t K n (j + 1) σ ω' c | filt d j] ω) a
  unfold zVecQN yVecQN
  rw [← h2, h1, h3]
  unfold martIncQN
  rw [h]
  rfl

end MartInc

/-! ## 4. The variance identity of the propagated `𝒬`-family -/

section QVQ

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The variance identity for an arbitrary weight vector `κ`. -/
private theorem AltProxyQ_qv_aux (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (hL : 3 ≤ L)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hM : M.IsHermitian) (k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool)
    (κ : (Fin k → Z2 L) → ℂ) :
    ∑ c : Coord L W, (gvar L W c : ℝ) *
        ‖∑ b : Fin k → Z2 L, κ b *
          Qop L u (fun b'' => loopDerivN L W E u M (coordinateMatrix L W c) σ b'') b‖ ^ 2 ≤
      (k : ℝ) * (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
        κ b * (starRingEnd ℂ) (κ b') * qqTensorN L u (eeN L W E u M σ) b b').re := by
  have h := qvPropagatedN L W E u hL hE hu0 hu1 M hM k hk σ (AltProxyQ_wts L u κ)
  have hLHS : ∀ c : Coord L W, ∑ b : Fin k → Z2 L, κ b *
      Qop L u (fun b'' => loopDerivN L W E u M (coordinateMatrix L W c) σ b'') b =
      ∑ b : Fin k → Z2 L, AltProxyQ_wts L u κ b *
        loopDerivN L W E u M (coordinateMatrix L W c) σ b := fun c =>
    AltProxyQ_sum_Qop u κ _
  rw [AltProxyQ_sum_qq]
  simp only [hLHS]
  exact h

/-- **`qv_at_propagatorQ`**: `qvPropagatedN` at the weights
`κ'_c = Σ_b κ_b Qmat_u(b, c)` of the transposed `𝒬_u`: `Σ_c gvar_c ‖Σ_b κ_b (𝒬_u ∂_c 𝓛)_b‖² ≤
k · qvFormQN`.  The two finite-sum rearrangements are `AltProxyQ_sum_Qop` and `AltProxyQ_sum_qq`. -/
theorem qv_at_propagatorQ (L W : ℕ) [NeZero L] [NeZero W] (E u w : ℝ) (hL : 3 ≤ L) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian)
    (k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    ∑ c : Coord L W, (gvar L W c : ℝ) *
        ‖∑ b : Fin k → Z2 L,
          (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u w (a i) (b i)) *
            Qop L u (fun b'' => loopDerivN L W E u M (coordinateMatrix L W c) σ b'') b‖ ^ 2 ≤
      (k : ℝ) * qvFormQN L W E u w σ M a :=
  AltProxyQ_qv_aux L W E u hL hE hu0 hu1 M hM k hk σ
    (fun b => ∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) u w (a i) (b i))

end QVQ

/-! ## 5. `(𝒬 ⊗ \bar 𝒬) 𝒜` has the double sum-zero property -/

section DSZ

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- **`doubleSumZero_qqTensorN`**: `(𝒬_t ⊗ \bar 𝒬_t) 𝒜` has the double sum-zero property
(`eq:double_sum_zero_tensor`) for every `𝒜`: `𝒫 ∘ 𝒬_t = 0` (`qopAlgebra` (ii)) in each copy, with linearity of `Qop` and
of complex conjugation for the second half. -/
theorem doubleSumZero_qqTensorN (L : ℕ) [NeZero L] (hL : 3 ≤ L) {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) :
    DoubleSumZero L (qqTensorN L t A) := by
  have hPQ := (qopAlgebra L hL k hk t ht0 ht1).2.1
  refine ⟨fun a₁ a' => ?_, fun a a₁ => ?_⟩
  · exact hPQ (fun c => starRingEnd ℂ (Qop L t (fun c' => starRingEnd ℂ (A c c')) a')) a₁
  · set F : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ := fun a' c =>
      starRingEnd ℂ (Qop L t (fun c' => starRingEnd ℂ (A c c')) a') with hF
    have h0 : ∀ c : Fin k → Z2 L, ∑ a' ∈ Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a₁),
        F a' c = 0 := by
      intro c
      simp only [hF]
      rw [← map_sum]
      have h := hPQ (fun c' => starRingEnd ℂ (A c c')) a₁
      unfold Psum at h
      rw [h, map_zero]
    have h1 := AltProxyQ_Qop_finset_sum t
      (Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a₁)) F a
    have h2 : (fun c => ∑ a' ∈ Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a₁), F a' c) =
        fun _ => (0 : ℂ) := funext h0
    rw [h2, AltProxyQ_Qop_zero] at h1
    exact h1.symm

end DSZ

/-! ## 6. Helpers: `‖ϑ‖ ≤ 1`, the slot bound of `𝒬`, distances under `Fin.append` -/

section Helpers

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `‖ϑ_{t,a}‖ ≤ 1` for `0 ≤ t < 1` (every entry of `Θ_t` is at most `(1-t)⁻¹`). -/
private theorem AltProxyQ_norm_vartheta_le_one (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin k → Z2 L) : ‖vartheta L t a‖ ≤ 1 := by
  have hn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hξ : ‖(t : ℂ)‖ < 1 := by rw [hn]; exact ht1
  have h1t : 0 < 1 - t := by linarith
  unfold vartheta
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h1t.le, norm_prod]
  have hprod : ∏ i ∈ Finset.univ.erase (0 : Fin k), ‖Theta L (t : ℂ) (a 0) (a i)‖ ≤
      ∏ _i ∈ Finset.univ.erase (0 : Fin k), (1 - t)⁻¹ :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
      have h := norm_Theta_apply_le L hL hξ (a 0) (a i)
      rwa [hn] at h)
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at hprod
  calc (1 - t) ^ (k - 1) * ∏ i ∈ Finset.univ.erase (0 : Fin k), ‖Theta L (t : ℂ) (a 0) (a i)‖
      ≤ (1 - t) ^ (k - 1) * ((1 - t)⁻¹) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ h1t.ne', one_pow]

/-- **The slot bound of `𝒬_t`**: if `‖F c‖ ≤ M` whenever `c₀ = y`, then `‖(𝒬_t F)_b‖ ≤ (1 + (L²)^{k-1}) M`
for every `b` with `b₀ = y` (`𝒫F` sums the `(L²)^{k-1}` entries with `c₀ = b₀ = y`). -/
private theorem AltProxyQ_norm_Qop_le_slot (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (F : (Fin k → Z2 L) → ℂ) {M : ℝ} (y : Z2 L) (hF : ∀ c : Fin k → Z2 L, c 0 = y → ‖F c‖ ≤ M)
    (b : Fin k → Z2 L) (hb : b 0 = y) :
    ‖Qop L t F b‖ ≤ (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF b hb)
  have hP : ‖Psum L F (b 0)‖ ≤ ((L : ℝ) ^ 2) ^ (k - 1) * M := by
    unfold Psum
    calc ‖∑ c ∈ Finset.univ.filter (fun c : Fin k → Z2 L => c 0 = b 0), F c‖
        ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin k → Z2 L => c 0 = b 0), ‖F c‖ := norm_sum_le _ _
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin k → Z2 L => c 0 = b 0), M :=
          Finset.sum_le_sum fun c hc => hF c (by rw [(Finset.mem_filter.mp hc).2, hb])
      _ = ((L : ℝ) ^ 2) ^ (k - 1) * M := by
          rw [Finset.sum_const, nsmul_eq_mul, SumZeroQ_card_filter]
  have hϑ := AltProxyQ_norm_vartheta_le_one hL ht0 ht1 b
  unfold Qop
  calc ‖F b - Psum L F (b 0) * vartheta L t b‖ ≤ ‖F b‖ + ‖Psum L F (b 0) * vartheta L t b‖ :=
        norm_sub_le _ _
    _ ≤ M + ((L : ℝ) ^ 2) ^ (k - 1) * M * 1 := by
        refine add_le_add (hF b hb) ?_
        rw [norm_mul]
        exact mul_le_mul hP hϑ (norm_nonneg _) (by positivity)
    _ = (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * M := by ring

/-- The unrestricted form of `AltProxyQ_norm_Qop_le_slot`. -/
private theorem AltProxyQ_norm_Qop_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (F : (Fin k → Z2 L) → ℂ) {M : ℝ} (hF : ∀ c : Fin k → Z2 L, ‖F c‖ ≤ M)
    (b : Fin k → Z2 L) : ‖Qop L t F b‖ ≤ (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * M :=
  AltProxyQ_norm_Qop_le_slot hL ht0 ht1 F (b 0) (fun c _ => hF c) b rfl

private theorem AltProxyQ_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem AltProxyQ_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, AltProxyQ_zdist_neg]

private theorem AltProxyQ_zdist2_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← neg_sub y x, AltProxyQ_zdist2_neg]

/-- `maxDist` of the first block is at most `maxDist` of the concatenation. -/
private theorem AltProxyQ_maxDist_le_append_left (a a' : Fin k → Z2 L) :
    KLoop.maxDist L a ≤ KLoop.maxDist L (Fin.append a a') := by
  unfold KLoop.maxDist
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdist2 L (Fin.append a a' q.1 - Fin.append a a' q.2))
    (Finset.mem_univ (Fin.castAdd k p.1, Fin.castAdd k p.2))
  simpa only [Fin.append_left] using h

/-- `maxDist` of the second block is at most `maxDist` of the concatenation. -/
private theorem AltProxyQ_maxDist_le_append_right (a a' : Fin k → Z2 L) :
    KLoop.maxDist L a' ≤ KLoop.maxDist L (Fin.append a a') := by
  unfold KLoop.maxDist
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdist2 L (Fin.append a a' q.1 - Fin.append a a' q.2))
    (Finset.mem_univ (Fin.natAdd k p.1, Fin.natAdd k p.2))
  simpa only [Fin.append_right] using h

/-- `zdist2 (x - y) ≤ maxDist` for two labels of the same tuple. -/
private theorem AltProxyQ_zdist2_le_maxDist {n : ℕ} (a : Fin n → Z2 L) (i j : Fin n) :
    zdist2 L (a i - a j) ≤ KLoop.maxDist L a :=
  Finset.le_sup (f := fun p : Fin n × Fin n => zdist2 L (a p.1 - a p.2)) (Finset.mem_univ (i, j))

/-- **The cross case of the window `3ρ`**: if both blocks have spread `< ρ` and the concatenation has
spread `≥ 3ρ`, then the anchors `b₀`, `b'₀` are at distance `≥ ρ`. -/
private theorem AltProxyQ_cross {ρ : ℝ} (hρ : 0 < ρ) (b b' : Fin k → Z2 L)
    (hb : (KLoop.maxDist L b : ℝ) < ρ) (hb' : (KLoop.maxDist L b' : ℝ) < ρ)
    (h : 3 * ρ ≤ (KLoop.maxDist L (Fin.append b b') : ℝ)) :
    ρ ≤ (zdist2 L (b 0 - b' 0) : ℝ) := by
  obtain ⟨⟨p1, p2⟩, -, hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin (k + k) × Fin (k + k))) Finset.univ_nonempty
    (fun q : Fin (k + k) × Fin (k + k) => zdist2 L (Fin.append b b' q.1 - Fin.append b b' q.2))
  have hmax : KLoop.maxDist L (Fin.append b b') =
      zdist2 L (Fin.append b b' p1 - Fin.append b b' p2) := hp
  have hij : 3 * ρ ≤ (zdist2 L (Fin.append b b' p1 - Fin.append b b' p2) : ℝ) := by
    rw [← hmax]; exact h
  have hbd : ∀ i : Fin k, (zdist2 L (b i - b 0) : ℝ) < ρ := fun i =>
    lt_of_le_of_lt (by exact_mod_cast AltProxyQ_zdist2_le_maxDist b i 0) hb
  have hbd' : ∀ i : Fin k, (zdist2 L (b' 0 - b' i) : ℝ) < ρ := fun i =>
    lt_of_le_of_lt (by exact_mod_cast AltProxyQ_zdist2_le_maxDist b' 0 i) hb'
  -- the mixed case
  have mixed : ∀ i j : Fin k, 3 * ρ ≤ (zdist2 L (b i - b' j) : ℝ) →
      ρ ≤ (zdist2 L (b 0 - b' 0) : ℝ) := by
    intro i j hij'
    have htri : zdist2 L (b i - b' j) ≤
        zdist2 L (b i - b 0) + zdist2 L (b 0 - b' 0) + zdist2 L (b' 0 - b' j) := by
      have h1 := zdist2_add_le L (b i - b 0 + (b 0 - b' 0)) (b' 0 - b' j)
      have h2 := zdist2_add_le L (b i - b 0) (b 0 - b' 0)
      have e : b i - b 0 + (b 0 - b' 0) + (b' 0 - b' j) = b i - b' j := by abel
      rw [e] at h1
      omega
    have htri' : (zdist2 L (b i - b' j) : ℝ) ≤
        (zdist2 L (b i - b 0) : ℝ) + (zdist2 L (b 0 - b' 0) : ℝ) +
          (zdist2 L (b' 0 - b' j) : ℝ) := by
      exact_mod_cast htri
    have := hbd i
    have := hbd' j
    linarith
  have hcases : ∀ q : Fin (k + k), (∃ i : Fin k, q = Fin.castAdd k i) ∨
      (∃ i : Fin k, q = Fin.natAdd k i) := fun q =>
    Fin.addCases (motive := fun q => (∃ i : Fin k, q = Fin.castAdd k i) ∨
      (∃ i : Fin k, q = Fin.natAdd k i)) (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) q
  rcases hcases p1 with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hcases p2 with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- both in the first block
    simp only [Fin.append_left] at hij
    have h1 : (zdist2 L (b i - b j) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by
      exact_mod_cast AltProxyQ_zdist2_le_maxDist b i j
    linarith
  · -- first block, second block
    simp only [Fin.append_left, Fin.append_right] at hij
    exact mixed i j hij
  · -- second block, first block
    simp only [Fin.append_left, Fin.append_right] at hij
    rw [AltProxyQ_zdist2_comm] at hij
    exact mixed j i hij
  · -- both in the second block
    simp only [Fin.append_right] at hij
    have h1 : (zdist2 L (b' i - b' j) : ℝ) ≤ (KLoop.maxDist L b' : ℝ) := by
      exact_mod_cast AltProxyQ_zdist2_le_maxDist b' i j
    linarith

end Helpers

/-! ## 7. The core: the two-copy bounds for abstract exponents

The analytic inputs are the four one-copy statements (`qopNorm`, `qopDecay` at the decay exponents
`D` and `D₁ = D - a - 1`), written for the abstract quantities `ρ` (window), `Wd = W^{-D}`,
`Wd1 = W^{-D₁} = Wd · Z · W`, `X = W^{C τ}`, `Y = W^{C}`, `Z = W^{a} ≥ (L²)^{k-1}`. -/

section Core

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem AltProxyQ_tmax_le {F : (Fin k → Z2 L) → ℂ} {B : ℝ} (h : ∀ a, ‖F a‖ ≤ B) :
    tmax L F ≤ B :=
  Finset.sup'_le _ _ fun a _ => h a

private theorem AltProxyQ_le_tmax (F : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ‖F a‖ ≤ tmax L F :=
  Finset.le_sup' (fun a => ‖F a‖) (Finset.mem_univ a)

private theorem AltProxyQ_tmax2_le {A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ} {B : ℝ}
    (h : ∀ a a', ‖A a a'‖ ≤ B) : tmax2 L A ≤ B :=
  Finset.sup'_le _ _ fun p _ => h p.1 p.2

private theorem AltProxyQ_le_tmax2 (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ)
    (a a' : Fin k → Z2 L) : ‖A a a'‖ ≤ tmax2 L A :=
  Finset.le_sup' (fun p : (Fin k → Z2 L) × (Fin k → Z2 L) => ‖A p.1 p.2‖) (Finset.mem_univ (a, a'))

private theorem AltProxyQ_tmax2_nonneg (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) :
    0 ≤ tmax2 L A :=
  (norm_nonneg _).trans (AltProxyQ_le_tmax2 A 0 0)

/-- **The two-copy bounds for abstract exponents** (both conjuncts of `QQTensorBoundsN`). -/
private theorem AltProxyQ_core (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ρ : ℝ}
    (hρ : 0 < ρ) {Wr X Y Z Wd Wd1 : ℝ} (hWr : 2 ≤ Wr) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (hWd : 0 ≤ Wd) (hWd1 : Wd1 = Wd * Z * Wr) (hWdY : Wd * Y ≤ 1)
    (hLp : ((L : ℝ) ^ 2) ^ (k - 1) ≤ Z)
    (hN1 : ∀ F : (Fin k → Z2 L) → ℂ, DecayWin L ρ Wd F →
      tmax L (Qop L t F) ≤ X * tmax L F + Wd * Y)
    (hD1 : ∀ F : (Fin k → Z2 L) → ℂ, DecayWin L ρ Wd F →
      DecayWin L ρ (Wd * (2 + tmax L F)) (Qop L t F))
    (hN2 : ∀ F : (Fin k → Z2 L) → ℂ, DecayWin L ρ Wd1 F →
      tmax L (Qop L t F) ≤ X * tmax L F + Wd1 * Y)
    (hD2 : ∀ F : (Fin k → Z2 L) → ℂ, DecayWin L ρ Wd1 F →
      DecayWin L ρ (Wd1 * (2 + tmax L F)) (Qop L t F))
    (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (hA : DecayWin2 L ρ Wd A) :
    tmax2 L (qqTensorN L t A) ≤ X * X * tmax2 L A + Wd * (Y * X * Z * Z * Wr * Wr) ∧
      DecayWin2 L (3 * ρ) (Wd * (Y * X * Z * Z * Wr * Wr) * (2 + tmax2 L A))
        (qqTensorN L t A) := by
  set m := tmax2 L A with hm
  have hm0 : 0 ≤ m := AltProxyQ_tmax2_nonneg A
  set Lp : ℝ := ((L : ℝ) ^ 2) ^ (k - 1) with hLpdef
  have hLp0 : 0 ≤ Lp := by positivity
  have hX0 : 0 ≤ X := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hQ : 2 ≤ Z * Wr := by nlinarith
  have hLpW : 1 + Lp ≤ Z * Wr := by nlinarith
  -- the slices
  set S : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ := fun c c' => starRingEnd ℂ (A c c') with hS
  set B : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ := fun c b' =>
    starRingEnd ℂ (Qop L t (S c) b') with hB
  have hqq : ∀ b b', qqTensorN L t A b b' = Qop L t (fun c => B c b') b := fun b b' => rfl
  have hnB : ∀ c b', ‖B c b'‖ = ‖Qop L t (S c) b'‖ := fun c b' => by simp [hB]
  have hnS : ∀ c c', ‖S c c'‖ = ‖A c c'‖ := fun c c' => by simp [hS]
  -- inner copy: every slice `S c` decays
  have hS1 : ∀ c, DecayWin L ρ Wd (S c) := by
    intro c c' hc'
    rw [hnS]
    exact hA c c' (le_trans hc' (by exact_mod_cast AltProxyQ_maxDist_le_append_right c c'))
  have hSm : ∀ c, tmax L (S c) ≤ m := fun c =>
    AltProxyQ_tmax_le fun c' => by rw [hnS]; exact AltProxyQ_le_tmax2 A c c'
  have hBI : ∀ c b', ‖B c b'‖ ≤ X * m + Wd * Y := by
    intro c b'
    rw [hnB]
    calc ‖Qop L t (S c) b'‖ ≤ tmax L (Qop L t (S c)) := AltProxyQ_le_tmax _ _
      _ ≤ X * tmax L (S c) + Wd * Y := hN1 _ (hS1 c)
      _ ≤ X * m + Wd * Y := by gcongr; exact hSm c
  have hBII : ∀ c b', ρ ≤ (KLoop.maxDist L b' : ℝ) → ‖B c b'‖ ≤ Wd * (2 + m) := by
    intro c b' hb'
    rw [hnB]
    calc ‖Qop L t (S c) b'‖ ≤ Wd * (2 + tmax L (S c)) := hD1 _ (hS1 c) b' hb'
      _ ≤ Wd * (2 + m) := by gcongr; exact hSm c
  -- outer copy: the slices `c ↦ B c b'` decay with `Wd1`
  have hT1 : ∀ b', DecayWin L ρ Wd1 (fun c => B c b') := by
    intro b' c hc
    have hall : ∀ c', ‖S c c'‖ ≤ Wd := fun c' => by
      rw [hnS]
      exact hA c c' (le_trans hc (by exact_mod_cast AltProxyQ_maxDist_le_append_left c c'))
    calc ‖B c b'‖ = ‖Qop L t (S c) b'‖ := hnB c b'
      _ ≤ (1 + Lp) * Wd := AltProxyQ_norm_Qop_le hL ht0 ht1 (S c) hall b'
      _ ≤ Z * Wr * Wd := by gcongr
      _ = Wd1 := by rw [hWd1]; ring
  have hTm : ∀ b', tmax L (fun c => B c b') ≤ X * m + Wd * Y := fun b' =>
    AltProxyQ_tmax_le fun c => hBI c b'
  -- the numerical inequalities
  have hP1 : Y * X + Z * Wr * Y ≤ Y * X * Z * Z * Wr * Wr := by
    have h1 : X + Z * Wr ≤ X * (Z * Wr) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 (show (1 : ℝ) ≤ (Z * Wr) ^ 2 by nlinarith)),
        mul_nonneg (sub_nonneg.2 hQ) (by linarith : (0 : ℝ) ≤ Z * Wr + 1)]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Y)
    nlinarith [h2]
  refine ⟨?_, ?_⟩
  · -- the sup bound
    refine AltProxyQ_tmax2_le fun b b' => ?_
    rw [hqq]
    calc ‖Qop L t (fun c => B c b') b‖ ≤ tmax L (Qop L t (fun c => B c b')) :=
          AltProxyQ_le_tmax _ _
      _ ≤ X * tmax L (fun c => B c b') + Wd1 * Y := hN2 _ (hT1 b')
      _ ≤ X * (X * m + Wd * Y) + Wd1 * Y := by gcongr; exact hTm b'
      _ ≤ X * X * m + Wd * (Y * X * Z * Z * Wr * Wr) := by
          rw [hWd1]
          nlinarith [mul_le_mul_of_nonneg_left hP1 hWd]
  · -- the decay of the window `3ρ`
    intro b b' hfar
    rw [hqq]
    have hP : Z * Wr ≤ Y * X * Z * Z * Wr * Wr := by
      have h1 : 1 ≤ Y * X := one_le_mul_of_one_le_of_one_le hY hX
      have h2 : 1 ≤ Y * X * (Z * Wr) := by nlinarith
      nlinarith
    by_cases h1 : ρ ≤ (KLoop.maxDist L b : ℝ)
    · -- (1) the first block spreads: `Wd1`-decay of the outer copy
      have hc := hD2 _ (hT1 b') b h1
      refine hc.trans ?_
      have hb1 : Wd * Y ≤ 1 := hWdY
      have h3 : 2 + tmax L (fun c => B c b') ≤ 2 * X * (2 + m) := by
        have := hTm b'
        nlinarith
      calc Wd1 * (2 + tmax L (fun c => B c b')) ≤ Wd1 * (2 * X * (2 + m)) :=
            mul_le_mul_of_nonneg_left h3 (by rw [hWd1]; positivity)
        _ ≤ Wd * (Y * X * Z * Z * Wr * Wr) * (2 + m) := by
            rw [hWd1]
            have hh : 0 ≤ Wd * Z * Wr * X * (2 + m) := by positivity
            have hYZ : 1 ≤ Y * Z := one_le_mul_of_one_le_of_one_le hY hZ
            have hh2 : 0 ≤ Wd * Z * Wr * X * (2 + m) * Wr * (Y * Z - 1) := by
              have : 0 ≤ Y * Z - 1 := sub_nonneg.2 hYZ
              positivity
            nlinarith [mul_le_mul_of_nonneg_left hWr hh, hh2]
    by_cases h2 : ρ ≤ (KLoop.maxDist L b' : ℝ)
    · -- (2) the second block spreads: every entry of the outer slice is small
      calc ‖Qop L t (fun c => B c b') b‖ ≤ (1 + Lp) * (Wd * (2 + m)) :=
            AltProxyQ_norm_Qop_le hL ht0 ht1 _ (fun c => hBII c b' h2) b
        _ ≤ Z * Wr * (Wd * (2 + m)) := by gcongr
        _ ≤ Y * X * Z * Z * Wr * Wr * (Wd * (2 + m)) := by gcongr
        _ = Wd * (Y * X * Z * Z * Wr * Wr) * (2 + m) := by ring
    · -- (3) both blocks are close, the anchors are far: all entries of `A` in the four terms decay
      have hcross := AltProxyQ_cross hρ b b' (not_le.1 h1) (not_le.1 h2) hfar
      have hAfar : ∀ c c' : Fin k → Z2 L, c 0 = b 0 → c' 0 = b' 0 → ‖A c c'‖ ≤ Wd := by
        intro c c' hc hc'
        refine hA c c' (le_trans hcross ?_)
        have h4 := AltProxyQ_zdist2_le_maxDist (Fin.append c c') (Fin.castAdd k 0) (Fin.natAdd k 0)
        simp only [Fin.append_left, Fin.append_right] at h4
        rw [hc, hc'] at h4
        exact_mod_cast h4
      have hBfar : ∀ c : Fin k → Z2 L, c 0 = b 0 → ‖B c b'‖ ≤ (1 + Lp) * Wd := by
        intro c hc
        rw [hnB]
        exact AltProxyQ_norm_Qop_le_slot hL ht0 ht1 (S c) (b' 0)
          (fun c' hc' => by rw [hnS]; exact hAfar c c' hc hc') b' rfl
      calc ‖Qop L t (fun c => B c b') b‖ ≤ (1 + Lp) * ((1 + Lp) * Wd) :=
            AltProxyQ_norm_Qop_le_slot hL ht0 ht1 _ (b 0) (fun c hc => hBfar c hc) b rfl
        _ ≤ (Z * Wr) * ((Z * Wr) * Wd) := by gcongr
        _ ≤ Wd * (Y * X * Z * Z * Wr * Wr) * (2 + m) := by
            have h1 : 1 ≤ Y * X := one_le_mul_of_one_le_of_one_le hY hX
            have h5 : (Z * Wr) * (Z * Wr) ≤ Y * X * Z * Z * Wr * Wr * (2 + m) := by
              have : (Z * Wr) * (Z * Wr) * 1 ≤ (Z * Wr) * (Z * Wr) * (Y * X * (2 + m)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                nlinarith
              nlinarith
            nlinarith [mul_le_mul_of_nonneg_right h5 hWd]

end Core

/-! ## 8. The statement `QQTensorBoundsN` and its proof -/

section QQBounds

/-- **`QQTensorBoundsN` (the two-copy form of `normQA` / `lem_+Q`)**:
`(𝒬_t ⊗ \bar 𝒬_t)` loses at most `W^{2 C_k τ}` in `‖·‖_max` (up to `W^{-D+C'}`) and keeps the decay
of the concatenated `2k` labels at the window `3 ℓ_t W^τ`, with the weight `(2 + ‖𝒜‖_max)` of the
one-copy `QopDecay`.  The constant `C'` depends on `𝔠, k, τ` only and comes
before `D`. -/
def QQTensorBoundsN : Prop :=
  ∀ 𝔠 > (0 : ℝ), ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ τ : ℝ, 0 < τ →
  ∃ C' : ℝ, 0 ≤ C' ∧ ∀ D : ℝ, C' < D →
  ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
    (N : ℝ) ^ 𝔠 ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 →
    ∀ A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ, HasDecay2 L W t τ D A →
      tmax2 L (qqTensorN L t A) ≤
          (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ)) * tmax2 L A + (W : ℝ) ^ (-D + C') ∧
        DecayWin2 L (3 * (RBM.Path.ellT L t * (W : ℝ) ^ τ))
          ((W : ℝ) ^ (-D + C') * (2 + tmax2 L A)) (qqTensorN L t A)

/-- `L² ≤ N ≤ W^{1/𝔠}` from `W²L² = N` and `N^𝔠 ≤ W`. -/
private theorem AltProxyQ_sizes {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {L W N : ℕ} [NeZero W]
    (hNLW : W ^ 2 * L ^ 2 = N) (hNc : (N : ℝ) ^ 𝔠 ≤ W) : (L : ℝ) ^ 2 ≤ (W : ℝ) ^ 𝔠⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNW' : (N : ℝ) ≤ (W : ℝ) ^ 𝔠⁻¹ := by
    calc (N : ℝ) = ((N : ℝ) ^ 𝔠) ^ 𝔠⁻¹ := by
          rw [← Real.rpow_mul h0, mul_inv_cancel₀ h𝔠.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ 𝔠⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hNc (inv_nonneg.mpr h𝔠.le)
  have hNeq : (N : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    rw [← hNLW]
    push_cast
    ring
  have hL2N : (L : ℝ) ^ 2 ≤ N := by
    rw [hNeq]
    nlinarith [sq_nonneg (L : ℝ), sq_nonneg ((W : ℝ) - 1)]
  exact hL2N.trans hNW'

/-- The exponent identity `W^{-D + (C + Cτ + a + a + 1 + 1)} = W^{-D} (W^C W^{Cτ} W^a W^a W W)`. -/
private theorem AltProxyQ_rpow_C' {Wr : ℝ} (hW0 : 0 < Wr) (D C Cτ a : ℝ) :
    Wr ^ (-D + (C + Cτ + a + a + 1 + 1)) =
      Wr ^ (-D) * (Wr ^ C * Wr ^ Cτ * Wr ^ a * Wr ^ a * Wr * Wr) := by
  have e : -D + (C + Cτ + a + a + 1 + 1) = -D + C + Cτ + a + a + 1 + 1 := by ring
  rw [e, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_add hW0,
    Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
  ring

/-- **`qqTensorBoundsN`**: `QQTensorBoundsN`, with the explicit constant
`C' = C + C τ + 2 a + 2`, `C = cPrec 𝔠 k`, `a = (k-1)/𝔠`.  (The paper has only the
one-copy `lem_+Q`.)  The inner copy `c' ↦ conj 𝒜(c, c')` has `HasDecay(t, τ, D)` for
every `c` (`maxDist c' ≤ maxDist (c, c')`), so `qopNorm`, `qopDecay` apply slice by slice; the outer
copy `c ↦ conj (𝒬 S_c)(b')` has `HasDecay(t, τ, D₁)`, `D₁ = D - a - 1`, because a spread `c` makes the
whole slice `S_c` decay and `𝒬` costs `1 + (L²)^{k-1} ≤ W^{a+1}`; the cross case of the window `3ρ`
(both blocks of spread `< ρ`, anchors `≥ ρ` apart) expands `𝒬 ⊗ \bar 𝒬` into the four terms of the
kernel `Qmat_t(b,c) = δ_{bc} - ϑ_t(b) 1[c₀ = b₀]`, all with anchors `≥ ρ` apart. -/
theorem qqTensorBoundsN : QQTensorBoundsN := by
  intro 𝔠 h𝔠 k _ hk τ hτ
  set C : ℝ := cPrec 𝔠 k with hC
  set a : ℝ := 𝔠⁻¹ * ((k - 1 : ℕ) : ℝ) with ha
  have hC0 : 0 < C := by rw [hC]; unfold cPrec; positivity
  have ha0 : 0 ≤ a := by positivity
  have hCτ0 : 0 ≤ C * τ := by positivity
  refine ⟨C + C * τ + a + a + 1 + 1, by positivity, fun D hD => ?_⟩
  have hD0 : 0 < D := lt_of_le_of_lt (by positivity) hD
  have hD1 : 0 < D - a - 1 := by linarith
  have hE5 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ 𝔠 :=
    ((tendsto_rpow_atTop h𝔠).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [qopNorm 𝔠 h𝔠 k hk τ D hτ hD0, qopDecay 𝔠 h𝔠 k hk τ D hτ hD0,
    qopNorm 𝔠 h𝔠 k hk τ (D - a - 1) hτ hD1, qopDecay 𝔠 h𝔠 k hk τ (D - a - 1) hτ hD1, hE5]
    with N hN1 hD1' hN2 hD2' h5
  intro L W _ _ hL hNLW hNc t ht0 ht1 A hA
  have hW2 : (2 : ℝ) ≤ W := h5.trans hNc
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hL2 := AltProxyQ_sizes h𝔠 hNLW hNc
  have hLp : ((L : ℝ) ^ 2) ^ (k - 1) ≤ (W : ℝ) ^ a := by
    calc ((L : ℝ) ^ 2) ^ (k - 1) ≤ ((W : ℝ) ^ 𝔠⁻¹) ^ (k - 1) :=
          pow_le_pow_left₀ (by positivity) hL2 _
      _ = (W : ℝ) ^ a := by rw [ha]; exact (Real.rpow_mul_natCast hW0.le 𝔠⁻¹ (k - 1)).symm
  have hρ : 0 < ellT L t * (W : ℝ) ^ τ := by
    have h1 := one_le_ellT (by omega : 1 ≤ L) ht0 ht1
    have h2 : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
    positivity
  have hX : 1 ≤ (W : ℝ) ^ (C * τ) := Real.one_le_rpow hW1 hCτ0
  have hY : 1 ≤ (W : ℝ) ^ C := Real.one_le_rpow hW1 hC0.le
  have hZ : 1 ≤ (W : ℝ) ^ a := Real.one_le_rpow hW1 ha0
  have hWd : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hWd1 : (W : ℝ) ^ (-(D - a - 1)) = (W : ℝ) ^ (-D) * (W : ℝ) ^ a * (W : ℝ) := by
    rw [show -(D - a - 1) = -D + a + 1 by ring, Real.rpow_add hW0, Real.rpow_add hW0,
      Real.rpow_one]
  have hDY : (W : ℝ) ^ (-D) * (W : ℝ) ^ C = (W : ℝ) ^ (-D + C) := (Real.rpow_add hW0 _ _).symm
  have hDY1 : (W : ℝ) ^ (-(D - a - 1)) * (W : ℝ) ^ C = (W : ℝ) ^ (-(D - a - 1) + C) :=
    (Real.rpow_add hW0 _ _).symm
  have hWdY : (W : ℝ) ^ (-D) * (W : ℝ) ^ C ≤ 1 := by
    rw [hDY]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hN1' : ∀ F : (Fin k → Z2 L) → ℂ, DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D)) F →
      tmax L (Qop L t F) ≤ (W : ℝ) ^ (C * τ) * tmax L F + (W : ℝ) ^ (-D) * (W : ℝ) ^ C := by
    intro F hF
    rw [hDY]
    exact hN1 L W hL hNLW hNc t ht0 ht1 F hF
  have hD1'' : ∀ F : (Fin k → Z2 L) → ℂ,
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D)) F →
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-D) * (2 + tmax L F)) (Qop L t F) := fun F hF =>
    hD1' L W hL hNLW hNc t ht0 ht1 F hF
  have hN2' : ∀ F : (Fin k → Z2 L) → ℂ,
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-(D - a - 1))) F →
      tmax L (Qop L t F) ≤ (W : ℝ) ^ (C * τ) * tmax L F +
        (W : ℝ) ^ (-(D - a - 1)) * (W : ℝ) ^ C := by
    intro F hF
    rw [hDY1]
    exact hN2 L W hL hNLW hNc t ht0 ht1 F hF
  have hD2'' : ∀ F : (Fin k → Z2 L) → ℂ,
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-(D - a - 1))) F →
      DecayWin L (ellT L t * (W : ℝ) ^ τ) ((W : ℝ) ^ (-(D - a - 1)) * (2 + tmax L F))
        (Qop L t F) := fun F hF => hD2' L W hL hNLW hNc t ht0 ht1 F hF
  have hcore := AltProxyQ_core hL ht0 ht1 hρ hW2 hX hY hZ hWd hWd1 hWdY hLp hN1' hD1'' hN2' hD2''
    A hA
  have hX2 : (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ)) = (W : ℝ) ^ (C * τ) * (W : ℝ) ^ (C * τ) := by
    rw [← Real.rpow_add hW0]
    congr 1
    rw [hC]
    ring
  rw [hX2, AltProxyQ_rpow_C' hW0]
  exact hcore

end QQBounds

/-! ## 9. The variance form on the good set (Case 5) -/

section QVPair

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise. -/
private theorem AltProxyQ_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L (star ξ) a b = star (Theta L ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hSB : (SB L).map (starRingEnd ℂ) = SB L := by
    ext x y
    simp only [Matrix.map_apply, SB_apply, sbKernel]
    split_ifs <;> simp [map_ofNat]
  have hmul : (Theta L ξ).map (starRingEnd ℂ) * (1 - star ξ • SB L) = 1 := by
    have h := congrArg (fun A : Matrix (Z2 L) (Z2 L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul L hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB L).map (starRingEnd ℂ) = 1 - star ξ • SB L := by
      ext x y
      have := congrFun (congrFun hSB x) y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul] at this ⊢
      rw [this]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul L hL hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm

/-- `conj (𝒰-slot kernel with parameter ξ) = 𝒰-slot kernel with parameter conj ξ` for real `v, w`. -/
private theorem AltProxyQ_conj_ukerMat (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hξ : ‖(w : ℂ) * ξ‖ < 1) (x y : Z2 L) :
    (starRingEnd ℂ) (ukerMat L ξ v w x y) = ukerMat L ((starRingEnd ℂ) ξ) v w x y := by
  have hSB : ∀ x y : Z2 L, (starRingEnd ℂ) (SB L x y) = SB L x y := fun x y => by
    simp only [SB_apply, sbKernel]
    split_ifs <;> simp [map_ofNat]
  have hT := AltProxyQ_Theta_star (L := L) hL hξ
  have hw : star ((w : ℂ) * ξ) = (w : ℂ) * (starRingEnd ℂ) ξ := by
    simp [Complex.conj_ofReal]
  rw [hw] at hT
  unfold ukerMat
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
      map_mul, hSB, Complex.conj_ofReal]
    split_ifs <;> simp
  · exact (hT z y).symm ▸ rfl

private theorem AltProxyQ_mSig_not (E : ℝ) (s : Bool) :
    KLoop.mSig E (!s) = (starRingEnd ℂ) (KLoop.mSig E s) := by
  cases s <;> simp [KLoop.mSig]

private theorem AltProxyQ_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    ‖KLoop.mSig E s‖ = 1 := by
  cases s
  · simp [KLoop.mSig, norm_spectralM hE]
  · simp [KLoop.mSig, norm_spectralM hE]

/-- **`qvFormQN` is the real part of the pair kernel `𝒰_σ ⊗ 𝒰_σ̄` applied to
`(𝒬 ⊗ \bar 𝒬)(𝓔 ⊗ 𝓔)`** (as `qvFormN_eq_re_UgenPair`, with `𝓔 ⊗ 𝓔` replaced by any
`2k`-tensor). -/
private theorem AltProxyQ_qvFormQN_eq_re (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {v w : ℝ}
    (hw : |w| < 1) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (a : Fin k → Z2 L) :
    qvFormQN L W E v w σ M a =
      (UgenPair L E σ v w (qqTensorN L v (eeN L W E v M σ)) a).re := by
  unfold qvFormQN UgenPair
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : (starRingEnd ℂ) (∏ i : Fin k, ukerMat L (KLoop.mSig E (σ i) *
      KLoop.mSig E (σ (i + 1))) v w (a i) (b' i)) =
      ∏ i : Fin k, ukerMat L (KLoop.mSig E (!σ i) * KLoop.mSig E (!σ (i + 1))) v w (a i) (b' i) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : ‖(w : ℂ) * (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))‖ < 1 := by
      rw [norm_mul, norm_mul, AltProxyQ_norm_mSig hE, AltProxyQ_norm_mSig hE, one_mul, mul_one,
        Complex.norm_real]
      simpa using hw
    rw [AltProxyQ_conj_ukerMat hL hn, map_mul, ← AltProxyQ_mSig_not, ← AltProxyQ_mSig_not]
  rw [hconj]

end QVPair

section GoodSet

/-- **`qvFormQN_le_of_bounds`**: the explicit Case 5 bound for the variance form of
the `𝒬`-process from the two raw inputs at the time `u`: an entrywise bound `Mee` of `𝓔 ⊗ 𝓔` and its
decay `HasDecay2 L W u τ' D'`, for alternating `σ`, eventually in `N`.  The constant `C'` is that of
`qqTensorBoundsN` at `(𝔠, k, τ')`.  Proof: `qvFormQN = Re UgenPair (𝒬 ⊗ \bar 𝒬)(𝓔 ⊗ 𝓔)`
(`AltProxyQ_qvFormQN_eq_re`), `qqTensorBoundsN` (max-norm and decay at the window `3 ℓ_u W^{τ'}`),
`doubleSumZero_qqTensorN` and `ugenPairCase5AltExplicit` with `K = 3 W^{τ'}`,
`M = W^{2 C_k τ'} Mee + W^{-D'+C'}`, `δA = W^{-D'+C'} (2 + Mee)`. -/
theorem qvFormQN_le_of_bounds (𝔠 : ℝ) (h𝔠 : 0 < 𝔠) (k : ℕ) [NeZero k] (hk : 2 ≤ k) (τ' : ℝ)
    (hτ' : 0 < τ') :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ D' : ℝ, C' < D' →
    ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → W ^ 2 * L ^ 2 = N →
      (N : ℝ) ^ 𝔠 ≤ W → ∀ E u w : ℝ, |E| < 2 → 0 ≤ u → u ≤ w → w < 1 →
      ∀ σ : Fin k → Bool, (∀ i : Fin k, σ i ≠ σ (i + 1)) →
      ∀ (M : Matrix (Idx L W) (Idx L W) ℂ) (Mee : ℝ), 0 ≤ Mee →
      (∀ b b' : Fin k → Z2 L, ‖eeN L W E u M σ b b'‖ ≤ Mee) →
      HasDecay2 L W u τ' D' (eeN L W E u M σ) → ∀ a : Fin k → Z2 L,
        qvFormQN L W E u w σ M a ≤
          cCase5 k * (1 + Real.log L) ^ (2 * k + 1) * (3 * (W : ℝ) ^ τ') ^ (4 * k) *
              rhoR L u w ^ (2 * k) *
              ((W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) * Mee + (W : ℝ) ^ (-D' + C')) +
            cCase5 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ (2 * k) * ((1 - u) / (1 - w)) ^ (2 * k) *
              ((W : ℝ) ^ (-D' + C') * (2 + Mee)) := by
  obtain ⟨C', hC', hbd⟩ := qqTensorBoundsN 𝔠 h𝔠 k hk τ' hτ'
  refine ⟨C', hC', fun D' hD' => ?_⟩
  filter_upwards [hbd D' hD'] with N hN
  intro L W _ _ hL hNLW hNc E u w hE hu0 huw hw1 σ hσ M Mee hMee hentry hdecay a
  have hu1 : u < 1 := huw.trans_lt hw1
  obtain ⟨h1, h2⟩ := hN L W hL hNLW hNc u hu0 hu1 (eeN L W E u M σ) hdecay
  have hm : tmax2 L (eeN L W E u M σ) ≤ Mee := AltProxyQ_tmax2_le hentry
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hWD : 0 ≤ (W : ℝ) ^ (-D' + C') := Real.rpow_nonneg hW0.le _
  have hX : 0 ≤ (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) := Real.rpow_nonneg hW0.le _
  have hbound : ∀ b b' : Fin k → Z2 L, ‖qqTensorN L u (eeN L W E u M σ) b b'‖ ≤
      (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) * Mee + (W : ℝ) ^ (-D' + C') := fun b b' =>
    (AltProxyQ_le_tmax2 _ b b').trans (h1.trans (by gcongr))
  have hwin : DecayWin2 L (ellT L u * (3 * (W : ℝ) ^ τ')) ((W : ℝ) ^ (-D' + C') * (2 + Mee))
      (qqTensorN L u (eeN L W E u M σ)) := by
    intro b b' hfar
    have e : 3 * (ellT L u * (W : ℝ) ^ τ') = ellT L u * (3 * (W : ℝ) ^ τ') := by ring
    refine (h2 b b' (by rw [e]; exact hfar)).trans ?_
    gcongr
  have hdsz := doubleSumZero_qqTensorN L hL hk hu0 hu1 (eeN L W E u M σ)
  have hK : 1 ≤ 3 * (W : ℝ) ^ τ' := by
    have := Real.one_le_rpow hW1 hτ'.le
    linarith
  have hM0 : 0 ≤ (W : ℝ) ^ (2 * (cPrec 𝔠 k * τ')) * Mee + (W : ℝ) ^ (-D' + C') := by positivity
  have hδ0 : 0 ≤ (W : ℝ) ^ (-D' + C') * (2 + Mee) := by positivity
  have hcase := ugenPairCase5AltExplicit k hk L hL E hE.le u w hu0 huw hw1 σ hσ (3 * (W : ℝ) ^ τ')
    _ _ hK hM0 hδ0 (qqTensorN L u (eeN L W E u M σ)) hbound hwin hdsz a
  rw [AltProxyQ_qvFormQN_eq_re hL hE.le (abs_lt.2 ⟨by linarith, hw1⟩) σ M a]
  exact (Complex.re_le_norm _).trans hcase

end GoodSet

/-! ## 10. The sub-Gaussian input for the first-chaos part of the `𝒬`-increment -/

section AzumaQ

/-- **`azumaSubGQ_ugen`**: `azumaSubG_ugen` with `zVecQN` and `qvFormQN` in
place of `ZvecN` and `qvFormN`, and no `AzumaSubGN` / `HermTestFunLoopN` hypothesis (the
theorems `azumaSubGN`, `hermTestFunLoopN` are used).  The propagated `𝒬 Z` is
`Σ_c κ'_c ZfamN(loop family)_c` pointwise (`AltProxyQ_sum_Qop`), then `azumaSubGN` at the weights
`κ'` and the variance identity `qv_at_propagatorQ`.  What remains for a consumer is the deterministic
majorant `hQ` of `Δ · k · qvFormQN` on `G j`. -/
theorem azumaSubGQ_ugen (d : Sizes) {E s t : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool)
    (τ : PathΩ d → ℕ) (G : ℕ → Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → pathH d s t K n j ω ∈ G j) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * ((k : ℝ) * qvFormQN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN d (E n) σ (gridTime s t K n) τ (fun j ω => zVecQN d E s t K n j σ ω) m a j Q := by
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (GoodEvent_gridTime_le (K := K) (hst n) (show j + 1 ≤ K n by omega)).trans_lt (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := GoodEvent_gridStep_nonneg (hst n)
  set κ : (Fin k → Z2 (d.L n)) → ℂ := fun b => ∏ i : Fin k, ukerMat (d.L n)
    (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
    (gridTime s t K n m) (a i) (b i) with hκ
  set Φ : (Fin k → Z2 (d.L n)) →
      Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ := fun b M =>
    gloop (d.L n) (d.W n) (blockMat M) (spectralZ (E n) (gridTime s t K n (j + 1))) (loopOf σ b)
    with hΦdef
  have hΦ : ∀ b, HermTestFun d n (Φ b) := fun b =>
    hΦ_of_hermTestFunLoopN (hermTestFunLoopN d) hE hs0 hst ht1 n k σ j (by omega) b
  have hcomb : ∀ ω' : PathΩ d,
      Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
        (zVecQN d E s t K n j σ ω') a =
      ∑ c, AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κ c * ZfamN d s t K n j Φ ω' c := by
    intro ω'
    exact AltProxyQ_sum_Qop (gridTime s t K n (j + 1)) κ (ZvecN d E s t K n j σ ω')
  have hz := azumaSubGN d s t K n Φ hΦ
    (AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κ) τ G hτ hG j Q (fun M hMG hMH => by
      have h3 := qv_at_propagatorQ (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n m) (d.three_le_L n) (hE n) hu0 hu1 M hMH k hk σ a
      have h4 : ∀ c : Coord (d.L n) (d.W n),
          ∑ b, AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κ b *
              dirDerivN (Φ b) M (coordinateMatrix (d.L n) (d.W n) c) =
            ∑ b : Fin k → Z2 (d.L n), κ b * Qop (d.L n) (gridTime s t K n (j + 1))
              (fun b'' => loopDerivN (d.L n) (d.W n) (E n) (gridTime s t K n (j + 1)) M
                (coordinateMatrix (d.L n) (d.W n) c) σ b'') b := fun c =>
        (AltProxyQ_sum_Qop (gridTime s t K n (j + 1)) κ _).symm
      simp only [h4]
      exact (mul_le_mul_of_nonneg_left h3 hΔ).trans (hQ M hMG hMH))
  have hfun : (fun ω' : PathΩ d => Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1))
      (gridTime s t K n m) (zVecQN d E s t K n j σ ω') a) =
      fun ω => ∑ b, AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κ b *
        ZfamN d s t K n j Φ ω b := funext hcomb
  unfold SubGaussStopN
  rw [hfun]
  exact hz

/-- **`azumaSubGQ_goodExit`**: `azumaSubGQ_ugen` at `G j = GoodSetN …` and
`τ = goodExitTauN` (the membership hypothesis is `mem_of_lt_gridExitTauN`, the measurability
hypothesis is `goodExitMeasN`); what remains is the deterministic majorant `hQ` of
`Δ · k · qvFormQN` on `GoodSetN` at the shifted time. -/
theorem azumaSubGQ_goodExit (d : Sizes) {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n k : ℕ) [NeZero k] (hk : 2 ≤ k) (σ : Fin k → Bool)
    (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ K n)
    (a : Fin k → Z2 (d.L n)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D',
      M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormQN (d.L n) (d.W n) (E n)
        (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN d (E n) σ (gridTime s v K n) (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
      (fun j ω => zVecQN d E s v K n j σ ω) m a j Q :=
  azumaSubGQ_ugen d hE hs0 hsv hv1 n k hk σ (goodExitTauN d E s v K k Γ Λ Φ τ' D' n)
    (fun j => GoodSetN (d.L n) (d.W n) (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')
    (goodExitMeasN d E s v K n k Γ Λ Φ τ' D') (fun ω j hj => mem_of_lt_gridExitTauN hj) m hm a j hj
    Q hQ

end AzumaQ

/-! ## 11. The `Y` moments of the `𝒬`-increment -/

section YQ

variable (d : Sizes)

/-- The transposed weights have `ℓ¹` norm at most `(1 + (L²)^{k-1})` times that of `κ`
(`|ϑ| ≤ 1`, and every `b` lies in the `(L²)^{k-1}` fibres `{c : c₀ = b₀}`): the kernel row sum of
`𝒬_u`. -/
private theorem AltProxyQ_sum_norm_wts_le {L : ℕ} [NeZero L] {k : ℕ} [NeZero k] (hL : 3 ≤ L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (κ : (Fin k → Z2 L) → ℂ) :
    ∑ c, ‖AltProxyQ_wts L t κ c‖ ≤ (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * ∑ b, ‖κ b‖ := by
  have h1 : ∀ c : Fin k → Z2 L, ‖AltProxyQ_wts L t κ c‖ ≤
      ‖κ c‖ + ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), ‖κ b‖ := by
    intro c
    unfold AltProxyQ_wts
    calc ‖κ c - ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0),
          κ b * vartheta L t b‖ ≤ ‖κ c‖ + ‖∑ b ∈ Finset.univ.filter
          (fun b : Fin k → Z2 L => b 0 = c 0), κ b * vartheta L t b‖ := norm_sub_le _ _
      _ ≤ ‖κ c‖ + ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), ‖κ b‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          calc ‖κ b‖ * ‖vartheta L t b‖ ≤ ‖κ b‖ * 1 :=
                mul_le_mul_of_nonneg_left (AltProxyQ_norm_vartheta_le_one hL ht0 ht1 b)
                  (norm_nonneg _)
            _ = ‖κ b‖ := mul_one _
  have h2 : ∑ c : Fin k → Z2 L, ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), ‖κ b‖ =
      ((L : ℝ) ^ 2) ^ (k - 1) * ∑ b, ‖κ b‖ := by
    have h3 : ∀ c : Fin k → Z2 L, ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0),
        ‖κ b‖ = ∑ b : Fin k → Z2 L, if c 0 = b 0 then ‖κ b‖ else 0 := by
      intro c
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl
    simp only [h3]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h4 : ∀ c : Fin k → Z2 L, (if c 0 = b 0 then ‖κ b‖ else 0) =
        if c 0 = b 0 then ‖κ b‖ else 0 := fun c => rfl
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, SumZeroQ_card_filter]
  calc ∑ c, ‖AltProxyQ_wts L t κ c‖ ≤ ∑ c : Fin k → Z2 L, (‖κ c‖ +
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), ‖κ b‖) :=
        Finset.sum_le_sum fun c _ => h1 c
    _ = ∑ c, ‖κ c‖ + ∑ c : Fin k → Z2 L,
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Z2 L => b 0 = c 0), ‖κ b‖ := Finset.sum_add_distrib
    _ = (1 + ((L : ℝ) ^ 2) ^ (k - 1)) * ∑ b, ‖κ b‖ := by rw [h2]; ring

/-- `𝒬_u` of a strongly measurable family is strongly measurable (`𝒬_u` is a continuous linear
map of the finite-dimensional space of tensors). -/
private theorem AltProxyQ_stronglyMeasurable_yVecQN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) :
    StronglyMeasurable[filt d (j + 1)] (fun ω => yVecQN d E s t K n j σ ω) := by
  have hcont : Continuous (fun A : (Fin k → Z2 (d.L n)) → ℂ =>
      Qop (d.L n) (gridTime s t K n (j + 1)) A) := by
    refine continuous_pi fun a => ?_
    unfold Qop Psum
    exact (continuous_apply a).sub
      ((continuous_finsetSum _ fun c _ => continuous_apply c).mul continuous_const)
  exact hcont.comp_stronglyMeasurable (stronglyMeasurable_YvecN d E s t K n j σ)

/-- **`YMomentsQUnifN`**: the `𝒬`-analogue of `YMomentsUnifN`: the
`Y` moment inputs of the assembled bound for `yVecQN = 𝒬_{u_{j+1}} YvecN`, with `v_j = Δ² P`,
`w_j = Δ⁴ P²`, `P ≤ N^{C_P}` for a constant `C_P = C_P(k, τ')` chosen before the grid `K`. -/
def YMomentsQUnifN (d : Sizes) (κ τ' : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  SizeTendsto d → RangeCond d τ' t →
  ∀ (k : ℕ) [NeZero k] (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
        YMomentBoundsN d (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => yVecQN d E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- `YMomentsQUnifN` with a strictly positive level `P` (the explicit level of
`yMomentsQUnifN` is `2000 (S' C₂)² N⁸ > 0`). -/
private def AltProxyQ_YMomentsQPos (d : Sizes) (κ τ' : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  SizeTendsto d → RangeCond d τ' t →
  ∀ (k : ℕ) [NeZero k] (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 < P ∧ P ≤ ((d.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ d → ℕ, (∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) →
        YMomentBoundsN d (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => yVecQN d E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **`YMomentsQUnifN` with an explicit positive level**: `YMomentsQUnifN` with `0 < P`.  **Explicit witness**
`C_P = 11 + (4 k + 4) · max 0 (1 - τ') + 2 k` (the constant of `yMomentsUnifN` plus `2k`
for the kernel row-sum factor `1 + (L²)^{k-1} ≤ 2 N^{k-1}` of `𝒬_u`, squared in `P`), chosen before the
grid `K`; for `N = size n ≥ max 2 (2000 (2^k k (k + 1) c₀^{-(k+2)})²)` and the range condition,
`P = 2000 (S' C₂)² N⁸` with `S' = 2 N^{k-1} (2 Θ)^k`, `C₂ = k (k + 1) N (Θ / c₀)^{k+2}`,
`Θ = N^{max 0 (1-τ')}`.  Proof: the stopped propagated increment `1_{j<τ} (𝒰 𝒬_{u_{j+1}} Y_j)_b` is
`1_{j<τ} Σ_c κ'_c (Y_j)_c` with the transposed weights `κ'` (`AltProxyQ_sum_Qop`), whose `ℓ¹` norm is at
most `(1 + (L²)^{k-1}) (1 + (1-u_m)⁻¹)^k`; then the weighted fields `AzumaProxyN_YfieldsW`. -/
private theorem AltProxyQ_yMomentsQPos (κ τ' : ℝ) (E s t : ℕ → ℝ) :
    AltProxyQ_YMomentsQPos d κ τ' E s t := by
  intro hκ hE hs0 hst ht1 hsize hrange k _ σ
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0def
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  refine ⟨11 + (4 * k + 4) * θ + 2 * k, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max 2 (2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hbig' : 2000 * (2 ^ k * ((k * (k + 1) : ℕ) : ℝ) * (c0⁻¹) ^ (k + 2)) ^ 2 ≤
      ((d.size n : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hΘ1 : 1 ≤ ((d.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((d.size n : ℕ) : ℝ) ^ θ) ^ k with hSmax
  set C2 : ℝ := ((k * (k + 1) : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ)
    * (((d.size n : ℕ) : ℝ) ^ θ / c0) ^ (k + 2) with hC2def
  have hk0 : (0 : ℝ) < ((k * (k + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hk1 (by omega)
  have hS0 : 0 < Smax := by positivity
  have hC20 : 0 < C2 := by positivity
  set Smax' : ℝ := 2 * ((d.size n : ℕ) : ℝ) ^ (k - 1) * Smax with hSmax'
  have hS0' : 0 < Smax' := by positivity
  have hLN : ((d.L n : ℕ) : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
    have hW1 : (1 : ℝ) ≤ ((d.W n : ℕ) : ℝ) := by exact_mod_cast d.W_pos n
    have hsz : ((d.size n : ℕ) : ℝ) = ((d.W n : ℕ) : ℝ) ^ 2 * ((d.L n : ℕ) : ℝ) ^ 2 := by
      rw [Sizes.size_eq]
      push_cast
      ring
    rw [hsz]
    nlinarith [sq_nonneg ((d.L n : ℕ) : ℝ), sq_nonneg (((d.W n : ℕ) : ℝ) - 1)]
  refine ⟨2000 * (Smax' * C2) ^ 2 * ((d.size n : ℕ) : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · -- `P ≤ N^{C_P + 2k}`
    have hP0 := AzumaProxyN_P_le_pub k hc0 hθ0 hN1 hbig'
    have hpow : 4 * ((d.size n : ℕ) : ℝ) ^ (2 * (k - 1)) ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k) := by
      have h2k : 2 * k = 2 * (k - 1) + 2 := by omega
      rw [h2k, pow_add]
      have h4 : (4 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ 2 := by nlinarith
      have h5 : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (2 * (k - 1)) := by positivity
      nlinarith
    calc 2000 * (Smax' * C2) ^ 2 * ((d.size n : ℕ) : ℝ) ^ 8
        = 4 * ((d.size n : ℕ) : ℝ) ^ (2 * (k - 1)) *
            (2000 * (Smax * C2) ^ 2 * ((d.size n : ℕ) : ℝ) ^ 8) := by
          rw [hSmax']; ring
      _ ≤ ((d.size n : ℕ) : ℝ) ^ (2 * k) * ((d.size n : ℕ) : ℝ) ^ (11 + (4 * k + 4) * θ) :=
          mul_le_mul hpow hP0 (by positivity) (by positivity)
      _ = ((d.size n : ℕ) : ℝ) ^ (11 + (4 * k + 4) * θ + 2 * k) := by
          rw [← Real.rpow_natCast ((d.size n : ℕ) : ℝ) (2 * k), ← Real.rpow_add hN0]
          congr 1
          push_cast
          ring
  · intro τ hτ
    refine ⟨fun j => AltProxyQ_stronglyMeasurable_yVecQN d E s t K n j σ, ?_⟩
    intro m hm b j hjm
    have hj : j + 1 ≤ K n := by omega
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := GoodEvent_gridTime_nonneg (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := GoodEvent_gridTime_le (K := K) (hst n) hj
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n m := GoodEvent_gridTime_nonneg (hs0 n) (hst n) m
    have hwt : gridTime s t K n m ≤ t n := GoodEvent_gridTime_le (K := K) (hst n) hm
    have hw1 : gridTime s t K n m < 1 := hwt.trans_lt (ht1 n)
    set κb : (Fin k → Z2 (d.L n)) → ℂ := fun b' => ∏ i : Fin k, ukerMat (d.L n)
      (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
      (gridTime s t K n m) (b i) (b' i) with hκb
    have hUrow : ∑ b', ‖κb b'‖ ≤ Smax := by
      refine (AzumaProxyN_rowsum_Ugen_pub (d.L n) (d.three_le_L n) hEn.le σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n m)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τ') :=
        AzumaProxyN_inv_one_sub_le_pub hwt hN0 hR
      have h2 : ((d.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((d.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have hrow : ∑ c, ‖AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κb c‖ ≤ Smax' := by
      refine (AltProxyQ_sum_norm_wts_le (d.three_le_L n) hv0 hv1 κb).trans ?_
      have hLp : ((d.L n : ℕ) : ℝ) ^ 2 ^ 1 = ((d.L n : ℕ) : ℝ) ^ 2 := by norm_num
      have hLp' : (((d.L n : ℕ) : ℝ) ^ 2) ^ (k - 1) ≤ ((d.size n : ℕ) : ℝ) ^ (k - 1) :=
        pow_le_pow_left₀ (by positivity) hLN _
      have hN1' : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k - 1) := one_le_pow₀ hN1
      rw [hSmax']
      exact mul_le_mul (by linarith) hUrow (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (by positivity)
    have hC2' : ∀ (a : Fin k → Z2 (d.L n))
        (M y : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ), M.IsHermitian →
        y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN d E s t K n j σ a)) M y y‖ ≤
          C2 * ‖y‖ ^ 2 := by
      intro a M y hM hy
      have hη := AzumaProxyN_etaT_inv_le_pub (κ := κ) (E := E n)
        (u := gridTime s t K n (j + 1)) (t := t n) (τ' := τ') (N := ((d.size n : ℕ) : ℝ)) hκ
        (hE n) hvt hN0 hR
      have hη' : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹
          ≤ ((d.size n : ℕ) : ℝ) ^ θ / c0 :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (hermTestFunLoopN d k n (E n) (gridTime s t K n (j + 1)) hEn hv0 hv1 σ a).2 M y hM hy
      refine h.trans ?_
      have hle : ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size d n : ℝ)
          * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (k + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ := by
          have := etaT_pos hEn hv1
          positivity
        have := pow_le_pow_left₀ hη0 hη' (k + 2)
        have hpos : 0 ≤ ((k * (k + 1) : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hcomb : ∀ ω' : PathΩ d,
        Ugen (d.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (yVecQN d E s t K n j σ ω') b =
        ∑ c, AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κb c *
          YvecN d E s t K n j σ ω' c := fun ω' =>
      AltProxyQ_sum_Qop (gridTime s t K n (j + 1)) κb (YvecN d E s t K n j σ ω')
    have hpt : ∀ ω, stoppedEdgeN d (E n) σ (gridTime s t K n) (gridTime s t K n m) τ
        (fun j ω => yVecQN d E s t K n j σ ω) b j ω =
        AzumaProxyN_stopW d E s t K n j σ
          (AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κb) τ ω := by
      intro ω
      unfold stoppedEdgeN AzumaProxyN_stopW
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        exact hcomb ω
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    have h8 := AzumaProxyN_YfieldsW d E s t K n j hEn (hs0 n) (hst n) (ht1 n) hj σ
      (AltProxyQ_wts (d.L n) (gridTime s t K n (j + 1)) κb) hS0'.le hC20.le hrow hC2' le_rfl τ hτ
    simp only [hpt]
    exact h8


/-- **`yMomentsQUnifN`**: `YMomentsQUnifN`, from the strictly positive explicit level
of `AltProxyQ_yMomentsQPos`. -/
theorem yMomentsQUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsQUnifN d κ τ' E s t := by
  intro hκ hE hs0 hst ht1 hsize hrange k _ σ
  obtain ⟨C_P, hC, h⟩ := AltProxyQ_yMomentsQPos d κ τ' E s t hκ hE hs0 hst ht1 hsize hrange k σ
  refine ⟨C_P, hC, fun K hK => ?_⟩
  filter_upwards [h K hK] with n ⟨P, hP, hPN, hτ⟩
  exact ⟨P, hP.le, hPN, hτ⟩

end YQ

end RBM.Ind


end
