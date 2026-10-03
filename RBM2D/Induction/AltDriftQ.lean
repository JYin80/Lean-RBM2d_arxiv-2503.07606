/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.AltGridQ
import RBM2D.Induction.AltSymm
import RBM2D.Induction.LocalFormCalc
import RBM2D.Induction.LocalFormLin
import RBM2D.Induction.LocalFormCuts
import RBM2D.Induction.NonAltEnd
import RBM2D.Induction.B45
import RBM2D.Induction.StoppedEndDefs
import RBM2D.Evolution.Case4
import RBM2D.Evolution.Case3

/-!
# The `ℚ`/`𝔼` split of the drift and of the initial term of the `𝒬`-process

Paper (Section 5): `int_K-L+Q2`, `int_K-L+QQ`, `int_K-L+QE`, `juaspuwp`, `juaspuwp234`,
`eq:case4_B`, `jywiiwsoks`, `kolkisaf`.  Namespace `RBM.Ind`.

## Contents

1. `altLocalForm`: the hypothesis `AltLocalForm` (`RBM2D.Induction.StoppedEndDefs`) for every
   `d κ c τ E s t`, from the six `altLocalFormAt_zero … five` (`altLocalForm_of_at`).
2. `dFlowQ`, `dGridQN_eq_dFlowQ`: the drift `dGridQN` of the `𝒬`-grid equals
   `Σ_{m=1}^4 𝒬_uB_m - 𝒬_uB_5`: `𝒬_u` is linear and `𝒫ℬ₄ = 𝒫ℬ₅ = 0`.
3. The `𝔼` part (Case 4): `kapQ4`, `epsQ4`, `AltCase4Cls`, `altQ_hker` (the `hker` field of
   `GridAssemblyHypN` for alternating `σ`, from `ugenCase4AltExplicit`); `expAltQB`, `expDriftQN`,
   `expAltQB_cls` (sum zero and symmetric, from `qopAlgebra` and `altExpSymm`).
4. The `ℚ` part on the grid (Case 3) with per-time levels: `AltQPartGridT`, `altQPartGridT`.
   Ingredients: general lemmas (uniformization over indices by sections, the centred
   decomposition, `≺ ⇒ 𝔼`); measurability of `altB`, `altQB`; the crude envelopes of `altB` and of
   the local forms; integrability and `𝔼 𝒬_uℬ_m = 𝒬_u 𝔼 ℬ_m`; the numerical absorption
   `AltDriftQ_arith`; the section lemma `AltDriftQ_sectionT`; its uniformization `AltDriftQ_termT`,
   `AltDriftQ_termT0`; the union bound over `(m', j, m, σ, a)` in `altQPartGridT`.

Some private lemmas of other files (measurability of the loop quantities, the cut-sum envelopes,
the row sum of `𝒰`) are repeated here with the prefix `AltDriftQ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-! ## 1. The local form: `altLocalForm` -/

/-- **The hypothesis `AltLocalForm`, proved**: `altLocalForm_of_at` with the six
`altLocalFormAt_zero … altLocalFormAt_five` (`m = 0` loop, `1` cut sums with `𝒦`, `2` product of
two loops, `3` `𝓔^{(G̃)}`, `4` `ℬ₄`, `5` `ℬ₅`). -/
theorem altLocalForm (κ c τ : ℝ) (E s t : ℕ → ℝ) : AltLocalForm d κ c τ E s t :=
  altLocalForm_of_at d fun m => by
    fin_cases m
    · exact altLocalFormAt_zero d
    · exact altLocalFormAt_one d
    · exact altLocalFormAt_two d
    · exact altLocalFormAt_three d
    · exact altLocalFormAt_four d
    · exact altLocalFormAt_five d

/-! ## 2. The drift of `int_K-L+Q2` as the five `𝒬_u ℬ_m` -/

/-- **The drift of `int_K-L+Q2` at a matrix**: `Σ_{m=1}^4 𝒬_uℬ_m - 𝒬_uℬ_5`
(the sign of `ℬ₅` is the one that comes from differentiating `𝒬_u f_u`; the paper writes `+`, a
misprint that is harmless since only norms enter). -/
def dFlowQ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ}
    [NeZero k] (σ : Fin k → Bool) : (Fin k → Z2 L) → ℂ :=
  fun a => altQB L W E u M σ 1 a + altQB L W E u M σ 2 a + altQB L W E u M σ 3 a +
    altQB L W E u M σ 4 a - altQB L W E u M σ 5 a

section Lin

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

private theorem AltDriftQ_Psum_add (A B : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    Psum L (fun b => A b + B b) x = Psum L A x + Psum L B x := by
  simp only [Psum, Finset.sum_add_distrib]

private theorem AltDriftQ_Psum_sub (A B : (Fin k → Z2 L) → ℂ) (x : Z2 L) :
    Psum L (fun b => A b - B b) x = Psum L A x - Psum L B x := by
  simp only [Psum, Finset.sum_sub_distrib]

/-- `𝒬_t` is additive (pointwise). -/
theorem AltDriftQ_Qop_add (t : ℝ) (A B : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L t (fun b => A b + B b) a = Qop L t A a + Qop L t B a := by
  simp only [Qop, AltDriftQ_Psum_add]; ring

end Lin

/-- **The drift of the `𝒬`-grid as the five `𝒬_uℬ_m`**: the drift `dGridQN` of the `𝒬`-grid, which
is `𝒬_u` of `Σ_{l≥3} [𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}` plus `ℬ₄` minus `ℬ₅`, is
`Σ_{m=1}^4 𝒬_uℬ_m - 𝒬_uℬ_5`: `𝒬_u` is linear, and
`𝒫ℬ₄ = 0` (`𝒫𝒬_u = 0` and `ϴ` preserves sum zero, `qopAlgebra`) and `𝒫ℬ₅ = (𝒫𝒜)_{a₁}𝒫ϑ̇ = 0`
(`SumZeroQ_Psum_varthetaDot`) give `𝒬_uℬ₄ = ℬ₄`, `𝒬_uℬ₅ = ℬ₅`. -/
theorem dGridQN_eq_dFlowQ (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) [NeZero k]
    (σ : Fin k → Bool) (j : ℕ) (ω : PathΩ d) (hk : 2 ≤ k) (hE : |E n| < 2)
    (h0 : 0 ≤ gridTime s t K n j) (h1 : gridTime s t K n j < 1) :
    dGridQN d E s t K n σ j ω =
      dFlowQ (d.L n) (d.W n) (E n) (gridTime s t K n j) (pathH d s t K n j ω) σ := by
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hu : |gridTime s t K n j| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
  set u := gridTime s t K n j with hu_def
  set M := pathH d s t K n j ω with hM_def
  -- `𝒫ℬ₄ = 0`
  have hB4 : SumZero (d.L n) (fun b => B4 (d.L n) (d.W n) (E n) u M σ b) := by
    intro a₁
    change Psum (d.L n) (fun b => B4 (d.L n) (d.W n) (E n) u M σ b) a₁ = 0
    have e : (fun b => B4 (d.L n) (d.W n) (E n) u M σ b) =
        fun b => Qop (d.L n) u (thetaSig (d.L n) (E n) σ u
            (lkTensor (d.L n) (d.W n) (E n) u M σ)) b -
          thetaSig (d.L n) (E n) σ u (Qop (d.L n) u (lkTensor (d.L n) (d.W n) (E n) u M σ)) b :=
      rfl
    rw [e, AltDriftQ_Psum_sub, SumZeroQ_Psum_Qop hL hu]
    have hs : SumZero (d.L n) (thetaSig (d.L n) (E n) σ u
        (Qop (d.L n) u (lkTensor (d.L n) (d.W n) (E n) u M σ))) :=
      SumZeroQ_SumZero_thetaSig hL hE σ h0 h1 (fun a₁ => SumZeroQ_Psum_Qop hL hu _ a₁)
    have := hs a₁
    change Psum (d.L n) (thetaSig (d.L n) (E n) σ u
      (Qop (d.L n) u (lkTensor (d.L n) (d.W n) (E n) u M σ))) a₁ = 0 at this
    rw [this]; ring
  -- `𝒫ℬ₅ = 0`
  have hB5 : SumZero (d.L n) (fun b => B5 (d.L n) (d.W n) (E n) u M σ b) := by
    intro a₁
    have hd := SumZeroQ_Psum_varthetaDot hL hk hu a₁
    unfold B5
    have : ∀ a ∈ Finset.univ.filter (fun a : Fin k → Z2 (d.L n) => a 0 = a₁),
        Psum (d.L n) (lkTensor (d.L n) (d.W n) (E n) u M σ) (a 0) * varthetaDot (d.L n) u a =
          Psum (d.L n) (lkTensor (d.L n) (d.W n) (E n) u M σ) a₁ * varthetaDot (d.L n) u a := by
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have hd' : ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 (d.L n) => a 0 = a₁),
        varthetaDot (d.L n) u a = 0 := hd
    rw [hd', mul_zero]
  funext a
  have q4 := SumZeroQ_Qop_of_sumZero u hB4
  have q5 := SumZeroQ_Qop_of_sumZero u hB5
  unfold dGridQN dFlowQ altQB
  have h4 : Qop (d.L n) u (altB (d.L n) (d.W n) (E n) u M σ 4) a =
      B4 (d.L n) (d.W n) (E n) u M σ a := congrFun q4 a
  have h5 : Qop (d.L n) u (altB (d.L n) (d.W n) (E n) u M σ 5) a =
      B5 (d.L n) (d.W n) (E n) u M σ a := congrFun q5 a
  rw [h4, h5]
  have h123 : Qop (d.L n) u (fun b => ∑ l ∈ Finset.Icc 3 k,
        ksimLK (d.L n) (d.W n) (E n) u M l (loopOf σ b) +
            elklkN (d.L n) (d.W n) (E n) u M (loopOf σ b) +
            egtN (d.L n) (d.W n) (E n) u M (loopOf σ b)) a =
      Qop (d.L n) u (altB (d.L n) (d.W n) (E n) u M σ 1) a +
        Qop (d.L n) u (altB (d.L n) (d.W n) (E n) u M σ 2) a +
        Qop (d.L n) u (altB (d.L n) (d.W n) (E n) u M σ 3) a := by
    rw [AltDriftQ_Qop_add, AltDriftQ_Qop_add]
    rfl
  rw [h123]

/-! ## 3. The bounds of `𝒫(𝓛-𝒦)` and `𝒫(𝓛-𝒦)ϑ`

`B45_psum_le_pub` and `B45_P_vartheta_le` are in `RBM2D.Induction.B45`;
`B45_norm_vartheta_le_pub` and `B45_core_det_pub` serve the envelopes of Section 5. -/

/-! ## 4. The `𝔼` part (Case 4) -/

/-- The first coefficient of Case 4 (`ugenCase4AltExplicit`): `c_4(k) (1 + log L)^{k+1} K_w^{2k} R_{s,t}^k`. -/
def kapQ4 (L k : ℕ) (Kw s t : ℝ) : ℝ :=
  cCase4 k * (1 + Real.log L) ^ (k + 1) * Kw ^ (2 * k) * rhoR L s t ^ k

/-- The second coefficient of Case 4: `c_4(k) ((1 + log L) L²)^k ((1-s)/(1-t))^k`. -/
def epsQ4 (L k : ℕ) (s t : ℝ) : ℝ :=
  cCase4 k * ((1 + Real.log L) * (L : ℝ) ^ 2) ^ k * ((1 - s) / (1 - t)) ^ k

/-- The kernel class of Case 4 at the grid index `i`: sum zero, `Symmetric`, `DecayWin` at the
scale `ℓ_{u_i} K_w` (`symmetric_tensor`). -/
def AltCase4Cls (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (u : ℕ → ℝ) (Kw : ℝ) (i : ℕ) (δ : ℝ)
    (X : (Fin k → Z2 L) → ℂ) : Prop :=
  SumZero L X ∧ Symmetric L X ∧ DecayWin L (RBM.Path.ellT L (u i) * Kw) δ X

/-- **The `hker` field of `GridAssemblyHypN` for alternating `σ`** (the pattern of
`hker_of_case1`): `ugenCase4AltExplicit` (`Alternating σ` gives `σ i ≠ σ (i+1)`). -/
theorem altQ_hker {k : ℕ} [NeZero k] (hk : 2 ≤ k) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {σ : Fin k → Bool} (hσ : Alternating σ) {K : ℕ} {u : ℕ → ℝ}
    (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m)
    (hu1 : ∀ i ≤ K, u i < 1) {Kw : ℝ} (hKw : 1 ≤ Kw) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Z2 L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → AltCase4Cls L u Kw i δ X → ∀ a : Fin k → Z2 L,
      ‖Ugen L E σ (u i) (u m) X a‖ ≤ kapQ4 L k Kw (u i) (u m) * M + epsQ4 L k (u i) (u m) * δ :=
  fun i m him hmK X M δ hM hδ hX hcls a => by
    obtain ⟨hsz, hsym, hdec⟩ := hcls
    have hσ' : ∀ i : Fin k, σ i ≠ σ (i + 1) := fun i => by
      rw [hσ i]; cases σ i <;> simp
    exact ugenCase4AltExplicit k hk L hL E hE (u i) (u m) (hu0 i (him.trans hmK))
      (hmono i m him hmK) (hu1 m hmK) σ hσ' Kw M δ hKw hM hδ X hX hdec hsz hsym a

/-- **The deterministic `𝔼` parts of `int_K-L+QE`**: `𝒬_u 𝔼 ℬ_m`, `m = 0..5`, as the
tensor `Qop` of the Gaussian mean of `altB` (the tensor of `AltExpSymm`). -/
def expAltQB (d : Sizes) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool)
    (m : Fin 6) : (Fin k → Z2 (d.L n)) → ℂ :=
  Qop (d.L n) u (fun b => ∫ ω, altB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b
    ∂(Sizes.seqP d))

/-- The deterministic drift `Σ_{m=1}^4 𝒬_u𝔼ℬ_m - 𝒬_u𝔼ℬ_5` (the `𝔼` part of the drift of
`int_K-L+Q2`; the drift of the modified process). -/
def expDriftQN (d : Sizes) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) {k : ℕ} [NeZero k]
    (σ : Fin k → Bool) : (Fin k → Z2 (d.L n)) → ℂ :=
  fun a => expAltQB d E n u σ 1 a + expAltQB d E n u σ 2 a + expAltQB d E n u σ 3 a +
    expAltQB d E n u σ 4 a - expAltQB d E n u σ 5 a

/-- **Sum zero and symmetry (`eq:case4_B`) of the `𝔼` parts**: every
`𝒬_u𝔼ℬ_m` and the drift `expDriftQN` is sum zero (`𝒫𝒬_u = 0`) and `Symmetric`
(`altExpSymm` and `TensorInvariantK.symmetric`).  The sup and decay levels are not here. -/
theorem expAltQB_cls (E : ℕ → ℝ) (n : ℕ) (u : ℝ) (k : ℕ) [NeZero k] (σ : Fin k → Bool)
    (hk : 2 ≤ k) (hE : |E n| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hσ : Alternating σ) :
    (∀ m : Fin 6, SumZero (d.L n) (expAltQB d E n u σ m) ∧
      Symmetric (d.L n) (expAltQB d E n u σ m)) ∧
    SumZero (d.L n) (expDriftQN d E n u σ) ∧ Symmetric (d.L n) (expDriftQN d E n u σ) := by
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hu : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
  have hsz : ∀ m : Fin 6, SumZero (d.L n) (expAltQB d E n u σ m) := fun m a₁ =>
    SumZeroQ_Psum_Qop hL hu _ a₁
  have hsy : ∀ m : Fin 6, Symmetric (d.L n) (expAltQB d E n u σ m) := fun m =>
    (altExpSymm d n (E n) u hE hu0 hu1 k hk σ hσ m).symmetric
  refine ⟨fun m => ⟨hsz m, hsy m⟩, ?_, ?_⟩
  · intro a₁
    have h1 := hsz 1 a₁
    have h2 := hsz 2 a₁
    have h3 := hsz 3 a₁
    have h4 := hsz 4 a₁
    have h5 := hsz 5 a₁
    unfold expDriftQN
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, h1, h2, h3, h4, h5]
    ring
  · intro c r hr
    unfold expDriftQN
    rw [hsy 1 c r hr, hsy 2 c r hr, hsy 3 c r hr, hsy 4 c r hr, hsy 5 c r hr]

/-! ## 5. The `ℚ` part on the grid (Case 3)

### 5.0 General lemmas -/

section General

/-- **Uniformization over a finite index by sections** (the contrapositive-choice argument of
`perTimeDomAt_iff_forall_section` for a fixed statement `p`):
if the statement holds eventually along every section `n ↦ sec n`, it holds eventually for all
indices at once. -/
theorem AltDriftQ_ev_forall_of_sections {U : ℕ → Type*} (hU : ∀ n, Nonempty (U n))
    {p : ∀ n, U n → Prop} (h : ∀ sec : ∀ n, U n, ∀ᶠ n in atTop, p n (sec n)) :
    ∀ᶠ n in atTop, ∀ x : U n, p n x := by
  by_contra hne
  rw [Filter.not_eventually] at hne
  classical
  let sec : ∀ n, U n := fun n =>
    if hb : ∃ x, ¬ p n x then hb.choose else Classical.choice (hU n)
  have hfreq : ∃ᶠ n in atTop, ¬ p n (sec n) := by
    refine hne.mono fun n hn => ?_
    have hb : ∃ x, ¬ p n x := by
      by_contra hb
      exact hn fun x => by_contra fun hx => hb ⟨x, hx⟩
    simp only [sec, hb, dite_true]
    exact hb.choose_spec
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (h sec)).exists
  exact hn1 hn2

section UgenLin

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

theorem AltDriftQ_Ugen_add (E : ℝ) (σ : Fin k → Bool) (v w : ℝ) (A B : (Fin k → Z2 L) → ℂ)
    (a : Fin k → Z2 L) :
    Ugen L E σ v w (fun b => A b + B b) a = Ugen L E σ v w A a + Ugen L E σ v w B a := by
  simp only [Ugen, mul_add, Finset.sum_add_distrib]

theorem AltDriftQ_Ugen_sub (E : ℝ) (σ : Fin k → Bool) (v w : ℝ) (A B : (Fin k → Z2 L) → ℂ)
    (a : Fin k → Z2 L) :
    Ugen L E σ v w (fun b => A b - B b) a = Ugen L E σ v w A a - Ugen L E σ v w B a := by
  simp only [Ugen, mul_sub, Finset.sum_sub_distrib]

/-- `‖m(σ)‖ = 1` for `|E| ≤ 2`. -/
private theorem AltDriftQ_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) :
    ‖KLoop.mSig E σ‖ = 1 := by
  cases σ <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

/-- The row `ℓ¹` norm of `𝒰`: `Σ_c |ψ_{ac}| ≤ (1-v)/(1-w)` for `‖ξ‖ ≤ 1`. -/
private theorem AltDriftQ_row_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hw : w < 1) (a : Z2 L) :
    ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖ ≤ (1 - v) / (1 - w) := by
  have h1w : 0 < 1 - w := by linarith
  have h := xiRowBound L hL ξ hξ v w hv hvw hw a
  calc ∑ c : Z2 L, ‖ukerMat L ξ v w a c‖
      ≤ ∑ c : Z2 L, (‖xiMat L ξ v w a c‖ + ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖) :=
        Finset.sum_le_sum fun c _ => by
          rw [KernelExpand_ukerMat_apply]; exact norm_add_le _ _
    _ = ∑ c : Z2 L, ‖xiMat L ξ v w a c‖ + ∑ c : Z2 L, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) a c‖ :=
        Finset.sum_add_distrib
    _ ≤ (w - v) / (1 - w) + 1 := by rw [KernelExpand_sum_norm_one_row]; linarith
    _ = (1 - v) / (1 - w) := by field_simp; ring

/-- **The crude norm of `𝒰`**: `|(𝒰_{v,w,σ}A)_a| ≤ ((1-v)/(1-w))^k ‖A‖_max` (`|E| ≤ 2`, `0 ≤ v ≤ w < 1`). -/
theorem AltDriftQ_Ugen_norm_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) {A : (Fin k → Z2 L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Z2 L) :
    ‖Ugen L E σ v w A a‖ ≤ ((1 - v) / (1 - w)) ^ k * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hA 0)
  set ψ : Fin k → Z2 L → ℝ := fun i c =>
    ‖ukerMat L (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1))) v w (a i) c‖ with hψ
  have hψ0 : ∀ i c, 0 ≤ ψ i c := fun i c => norm_nonneg _
  have hrow : ∀ i, ∑ c : Z2 L, ψ i c ≤ (1 - v) / (1 - w) := fun i =>
    AltDriftQ_row_le hL (by rw [norm_mul, AltDriftQ_norm_mSig hE, AltDriftQ_norm_mSig hE]; norm_num)
      hv hvw hw (a i)
  calc ‖Ugen L E σ v w A a‖ ≤ ∑ b : Fin k → Z2 L, (∏ i, ψ i (b i)) * ‖A b‖ := by
        unfold Ugen
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_prod]
    _ ≤ ∑ b : Fin k → Z2 L, (∏ i, ψ i (b i)) * M :=
        Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hA b) (Finset.prod_nonneg fun i _ => hψ0 i _)
    _ = (∏ i, ∑ c : Z2 L, ψ i c) * M := by
        rw [← Finset.sum_mul, KernelExpand_sum_prod_pi ψ]
    _ ≤ ((1 - v) / (1 - w)) ^ k * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM0
        calc ∏ i, ∑ c : Z2 L, ψ i c ≤ ∏ _i : Fin k, (1 - v) / (1 - w) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => hψ0 i c)
                (fun i _ => hrow i)
          _ = ((1 - v) / (1 - w)) ^ k := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The decomposition of the centred tensor** `X - X_m = (F - F_m) + ((X - F) - (X_m - F_m))`:
`|𝒰(X - X_m)| ≤ |𝒰(F - F_m)| + ((1-v)/(1-w))^k (θ + θ')` if `‖X - F‖_max ≤ θ`,
`‖X_m - F_m‖_max ≤ θ'`. -/
theorem AltDriftQ_decomp (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) (σ : Fin k → Bool) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) (X F Xm Fm : (Fin k → Z2 L) → ℂ) {θ θ' : ℝ}
    (he : ∀ b, ‖X b - F b‖ ≤ θ) (hem : ∀ b, ‖Xm b - Fm b‖ ≤ θ') (a : Fin k → Z2 L) :
    ‖Ugen L E σ v w (fun b => X b - Xm b) a‖ ≤
      ‖Ugen L E σ v w (fun b => F b - Fm b) a‖ + ((1 - v) / (1 - w)) ^ k * (θ + θ') := by
  have e : (fun b => X b - Xm b) =
      fun b => (F b - Fm b) + ((X b - F b) - (Xm b - Fm b)) := by
    funext b; ring
  rw [e, AltDriftQ_Ugen_add]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact AltDriftQ_Ugen_norm_le hL hE σ hv hvw hw (M := θ + θ')
    (fun b => (norm_sub_le _ _).trans (add_le_add (he b) (hem b))) a

end UgenLin

/-- **`≺ ⇒ 𝔼`**: for a measurable `f` with `‖f‖ ≤ B` everywhere and
`μ{θ < ‖f‖} ≤ p`, `‖𝔼 f‖ ≤ θ + B p`. -/
theorem AltDriftQ_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (hf : Measurable f) {θ B p : ℝ} (hθ : 0 ≤ θ)
    (hB0 : 0 ≤ B) (hp0 : 0 ≤ p) (hB : ∀ ω, ‖f ω‖ ≤ B)
    (hp : μ {ω | θ < ‖f ω‖} ≤ ENNReal.ofReal p) :
    ‖∫ ω, f ω ∂μ‖ ≤ θ + B * p := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set A : Set Ω := {ω | θ < ‖f ω‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hf.norm
  have hpt : ∀ ω, ‖f ω‖ ≤ θ + A.indicator (fun _ => B) ω := by
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h]; linarith [hB ω]
    · rw [Set.indicator_of_notMem h]
      have : ‖f ω‖ ≤ θ := not_lt.mp h
      linarith
  have hμA : μ.real A ≤ p := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rwa [ENNReal.toReal_ofReal hp0] at this
  calc ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (θ + A.indicator (fun _ => B) ω) ∂μ := by
        refine integral_mono hfi.norm ?_ hpt
        exact (integrable_const θ).add ((integrable_const B).indicator hAm)
    _ = θ + B * μ.real A := by
        rw [integral_add (integrable_const θ) ((integrable_const B).indicator hAm), integral_const,
          integral_indicator_const _ hAm]
        simp [smul_eq_mul, mul_comm]
    _ ≤ θ + B * p := by
        have := mul_le_mul_of_nonneg_left hμA hB0
        linarith

end General

/-! ### 5.1 Measurability of `altB`, `altQB`, `𝒰` as functions of the matrix -/

section Meas

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- Measurability of the loop quantities. -/
private theorem AltDriftQ_meas_LLf (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => LLf L W E u M I :=
  GoodEvent_measurable_gloop L W (spectralZ E u) I

private theorem AltDriftQ_meas_LKf (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => LKf L W E u M I :=
  (AltDriftQ_meas_LLf L W E u I).sub_const _

private theorem AltDriftQ_meas_ksimLK (E u : ℝ) (l : ℕ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => ksimLK L W E u M l I := by
  unfold ksimLK
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((AltDriftQ_meas_LKf L W E u _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      (((measurable_const).mul (measurable_const)).mul (AltDriftQ_meas_LKf L W E u _))
      measurable_const

private theorem AltDriftQ_meas_elklkN (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => elklkN L W E u M I := by
  unfold elklkN
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((AltDriftQ_meas_LKf L W E u _).mul_const _).mul (AltDriftQ_meas_LKf L W E u _)

private theorem AltDriftQ_avgErr_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool)
    (a : Z2 L) :
    avgErr L W E u M σ a = gloop L W (blockMat M) (spectralZ E u) ⟨[σ], [a]⟩ -
      KLoop.mSig E σ * Matrix.trace (Eblk L W a) := by
  unfold avgErr greenBlk gloop
  rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]
  simp [gloopProd]

private theorem AltDriftQ_meas_avgErr (E u : ℝ) (σ : Bool) (a : Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => avgErr L W E u M σ a := by
  simp only [AltDriftQ_avgErr_eq]
  exact (GoodEvent_measurable_gloop L W (spectralZ E u) ⟨[σ], [a]⟩).sub_const _

private theorem AltDriftQ_meas_egtN (E u : ℝ) (I : LoopIdx (Z2 L)) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => egtN L W E u M I := by
  unfold egtN
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((AltDriftQ_meas_avgErr L W E u _ a).mul_const _).mul (AltDriftQ_meas_LLf L W E u _)

variable {L W}

section Tens

variable {k : ℕ} [NeZero k]

private theorem AltDriftQ_meas_Psum {A : Matrix (Idx L W) (Idx L W) ℂ → (Fin k → Z2 L) → ℂ}
    (hA : ∀ b, Measurable fun M => A M b) (x : Z2 L) :
    Measurable fun M => Psum L (A M) x :=
  Finset.measurable_sum _ fun b _ => hA b

private theorem AltDriftQ_meas_Qop {A : Matrix (Idx L W) (Idx L W) ℂ → (Fin k → Z2 L) → ℂ}
    (hA : ∀ b, Measurable fun M => A M b) (t : ℝ) (a : Fin k → Z2 L) :
    Measurable fun M => Qop L t (A M) a :=
  (hA a).sub ((AltDriftQ_meas_Psum hA (a 0)).mul_const _)

private theorem AltDriftQ_meas_thetaSig {A : Matrix (Idx L W) (Idx L W) ℂ → (Fin k → Z2 L) → ℂ}
    (hA : ∀ b, Measurable fun M => A M b) (E : ℝ) (σ : Fin k → Bool) (u : ℝ) (a : Fin k → Z2 L) :
    Measurable fun M => thetaSig L E σ u (A M) a :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
    measurable_const.mul (hA _)

private theorem AltDriftQ_meas_lkTensor (E u : ℝ) (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => lkTensor L W E u M σ b :=
  AltDriftQ_meas_LKf L W E u _

/-- **`M ↦ (altB_m)_b(M)` is measurable**, `m = 0..5`. -/
theorem AltDriftQ_meas_altB (E u : ℝ) (σ : Fin k → Bool) (m : Fin 6) (b : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => altB L W E u M σ m b := by
  fin_cases m
  · exact AltDriftQ_meas_lkTensor E u σ b
  · exact Finset.measurable_sum _ fun l _ => AltDriftQ_meas_ksimLK L W E u l _
  · exact AltDriftQ_meas_elklkN L W E u _
  · exact AltDriftQ_meas_egtN L W E u _
  · exact (AltDriftQ_meas_Qop (fun b' => AltDriftQ_meas_thetaSig
        (fun b'' => AltDriftQ_meas_lkTensor E u σ b'') E σ u b') u b).sub
      (AltDriftQ_meas_thetaSig (fun b' => AltDriftQ_meas_Qop
        (fun b'' => AltDriftQ_meas_lkTensor E u σ b'') u b') E σ u b)
  · exact (AltDriftQ_meas_Psum (fun b' => AltDriftQ_meas_lkTensor E u σ b') (b 0)).mul_const _

/-- **`M ↦ (altQB_m)_b(M)` is measurable**. -/
theorem AltDriftQ_meas_altQB (E u : ℝ) (σ : Fin k → Bool) (m : Fin 6) (b : Fin k → Z2 L) :
    Measurable fun M : Matrix (Idx L W) (Idx L W) ℂ => altQB L W E u M σ m b :=
  AltDriftQ_meas_Qop (fun b' => AltDriftQ_meas_altB E u σ m b') u b

/-- `M ↦ (𝒰 A(M))_a` is measurable if the entries of `A` are. -/
theorem AltDriftQ_meas_Ugen {A : Matrix (Idx L W) (Idx L W) ℂ → (Fin k → Z2 L) → ℂ}
    (hA : ∀ b, Measurable fun M => A M b) (E : ℝ) (σ : Fin k → Bool) (v w : ℝ)
    (a : Fin k → Z2 L) : Measurable fun M => Ugen L E σ v w (A M) a :=
  Finset.measurable_sum _ fun b _ => measurable_const.mul (hA b)

end Tens

end Meas

/-! ### 5.2 The crude envelopes of `altB`, `altQB` on Hermitian matrices (`KeyAt` of `RBM2D.Induction.LocalFormCuts`) -/

section Crude

open LocalFormCuts LocalFormCalc

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Σ_b |S_{ab}| = 1`. -/
private theorem AltDriftQ_sum_norm_SB_row (hL : 3 ≤ L) (a : Z2 L) :
    ∑ b : Z2 L, ‖SB L a b‖ = 1 := by
  have h := sum_nnnorm_SB_row L hL a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simpa using h'

private theorem AltDriftQ_norm_ite_le (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

/-- The graded cut coupling as two `primBil`s. -/
private theorem AltDriftQ_ksimLK_eq (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : ℕ)
    (I : LoopIdx (Z2 L)) :
    ksimLK L W E u M l I =
      primBil L W (LKf L W E u M)
          (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) I +
        primBil L W (fun J => if J.length = l then KLoop.Kcal L W E u J else 0)
          (LKf L W E u M) I := by
  unfold ksimLK primBil
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]

/-- The envelope of one graded cut coupling. -/
private theorem AltDriftQ_norm_ksimLK_le (hL : 3 ≤ L) {E u : ℝ}
    (M : Matrix (Idx L W) (Idx L W) ℂ) {I : LoopIdx (Z2 L)} (hI : I.WF) (l : ℕ) {BF Bk : ℝ}
    (hBF0 : 0 ≤ BF) (hBk0 : 0 ≤ Bk)
    (hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖LKf L W E u M J‖ ≤ BF)
    (hK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖KLoop.Kcal L W E u J‖ ≤ Bk) :
    ‖ksimLK L W E u M l I‖ ≤ 2 * ((W : ℝ) ^ 2 * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * BF * Bk) := by
  rw [AltDriftQ_ksimLK_eq]
  refine (norm_add_le _ _).trans ?_
  have hKl : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖(if J.length = l then KLoop.Kcal L W E u J else 0)‖ ≤ Bk :=
    fun J h1 h2 h3 => (AltDriftQ_norm_ite_le _ _).trans (hK J h1 h2 h3)
  have h1 := norm_primBil_le L hL W (LKf L W E u M)
    (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) I hI hBF0 hBk0 hF hKl
  have h2 := norm_primBil_le L hL W
    (fun J => if J.length = l then KLoop.Kcal L W E u J else 0) (LKf L W E u M) I hI hBk0 hBF0
    hKl hF
  linarith [h1, h2]

/-- `|(𝓛-𝒦)_J| ≤ 2N^{k+2}` for the well-formed loops of length `1 ≤ ℓ ≤ k+1` and Hermitian `M`
(`norm_lk_envN` with the `𝒦` envelope of `KeyAt`). -/
private theorem AltDriftQ_norm_LKf_le {E u Nr : ℝ} {k : ℕ} (h : KeyAt L W E u Nr (k + 1))
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {J : LoopIdx (Z2 L)} (hJ : J.WF)
    (h1 : 1 ≤ J.length) (hk : J.length ≤ k + 1) : ‖LKf L W E u M J‖ ≤ 2 * Nr ^ (k + 2) := by
  have h1' : ‖LKf L W E u M J‖ ≤ (etaT E u)⁻¹ ^ (k + 1) + Nr ^ (k + 2) :=
    norm_lk_envN h.hE hM h.hu0 h.hu1 (n := k + 1) (MK := Nr ^ (k + 2))
      (fun J hJ h1 hkm => h.norm_kcal_le J h1 hkm hJ) J hJ h1 hk
  have hη : (etaT E u)⁻¹ ^ (k + 1) ≤ Nr ^ (k + 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 h.eta_pos.le) h.hη _
  have hN : Nr ^ (k + 1) ≤ Nr ^ (k + 2) := pow_le_pow_right₀ h.hN1 (by omega)
  linarith

/-- `W² L² ≤ N`. -/
private theorem AltDriftQ_WL_le {E u Nr : ℝ} {kmax : ℕ} (h : KeyAt L W E u Nr kmax) :
    (W : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ Nr := by
  have h1 : (((L * W) ^ 2 : ℕ) : ℝ) ≤ Nr := h.hNLW
  have e : (((L * W) ^ 2 : ℕ) : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by push_cast; ring
  rwa [e] at h1

/-- The size threshold `8 k³ C₅^k ≤ N` gives all the numerical absorptions of the crude bounds. -/
private theorem AltDriftQ_thr {k : ℕ} {Nr : ℝ} (hk : 2 ≤ k)
    (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr) :
    2 ≤ Nr ∧ 4 * (k : ℝ) ^ 3 ≤ Nr ∧ 2 * (k : ℝ) ≤ Nr ∧ 4 * C5 ^ k ≤ Nr := by
  have hC1 : (1 : ℝ) ≤ C5 := by unfold C5; norm_num
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (8 : ℝ) ≤ (k : ℝ) ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hk2 3
  have hp1 : (1 : ℝ) ≤ C5 ^ k := one_le_pow₀ hC1
  have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    calc (k : ℝ) = k * 1 := (mul_one _).symm
      _ ≤ k * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = (k : ℝ) ^ 3 := by ring
  have h1 : 8 * (k : ℝ) ^ 3 ≤ 8 * (k : ℝ) ^ 3 * C5 ^ k := le_mul_of_one_le_right (by positivity) hp1
  have h2 : 8 * C5 ^ k ≤ 8 * (k : ℝ) ^ 3 * C5 ^ k := by
    have : (1 : ℝ) ≤ (k : ℝ) ^ 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * C5 ^ k)]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `(1-u)⁻¹ ≤ η_u⁻¹` (`Im m ≤ 1`). -/
private theorem AltDriftQ_inv_one_sub_le {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) :
    (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hsq : Real.sqrt (4 - E ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have him : (spectralM E).im ≤ 1 := by rw [spectralM_im]; linarith
  have hIm : 0 ≤ (spectralM E).im := (spectralM_im_pos hE).le
  have : etaT E u ≤ 1 - u := by
    calc etaT E u = (1 - u) * (spectralM E).im := rfl
      _ ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left him (by linarith)
      _ = 1 - u := mul_one _
  exact inv_anti₀ hη this

/-- **`m = 0`**: `|𝓛-𝒦| ≤ 2N^{k+2}`. -/
private theorem AltDriftQ_altB_zero_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin k → Bool) (b : Fin k → Z2 L) : ‖altB L W E u M σ 0 b‖ ≤ 2 * Nr ^ (k + 2) :=
  h.norm_lk_le hM σ b (by omega) (by omega)

/-- **`m = 1`** (the cut sums with `𝒦`): `≤ 4k³ N^{2k+5}`. -/
private theorem AltDriftQ_altB_one_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    ‖altB L W E u M σ 1 b‖ ≤ 4 * (k : ℝ) ^ 3 * Nr ^ (2 * k + 5) := by
  have hI : (loopOf σ b).WF := by simp [loopOf, LoopIdx.WF]
  have hlen : (loopOf σ b).length = k := by simp [loopOf, LoopIdx.length]
  have hN0 : 0 < Nr := h.N_pos
  have hBF0 : 0 ≤ 2 * Nr ^ (k + 2) := by positivity
  have hBk0 : 0 ≤ Nr ^ (k + 2) := by positivity
  have hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ b).length →
      ‖LKf L W E u M J‖ ≤ 2 * Nr ^ (k + 2) := fun J hJ h2 hJk =>
    AltDriftQ_norm_LKf_le h hM hJ (by omega) (by omega)
  have hK : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ b).length →
      ‖KLoop.Kcal L W E u J‖ ≤ Nr ^ (k + 2) := fun J hJ h2 hJk =>
    h.norm_kcal_le J (by omega) (by omega) hJ
  have hsum : ‖∑ l ∈ Finset.Icc 3 k, ksimLK L W E u M l (loopOf σ b)‖ ≤
      (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2)) *
        Nr ^ (k + 2))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l ∈ Finset.Icc 3 k, ‖ksimLK L W E u M l (loopOf σ b)‖
        ≤ ∑ _l ∈ Finset.Icc 3 k, (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 *
            (2 * Nr ^ (k + 2)) * Nr ^ (k + 2))) :=
          Finset.sum_le_sum fun l _ => by
            have := AltDriftQ_norm_ksimLK_le h.hL M hI l hBF0 hBk0 hF hK
            rwa [hlen] at this
      _ = ((Finset.Icc 3 k).card : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 *
            (2 * Nr ^ (k + 2)) * Nr ^ (k + 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 *
            (2 * Nr ^ (k + 2)) * Nr ^ (k + 2))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : k + 1 - 3 ≤ k)
  refine hsum.trans ?_
  have hWL := AltDriftQ_WL_le h
  have key : (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2)) * Nr ^ (k + 2) ≤
      (k : ℝ) ^ 2 * Nr * (2 * Nr ^ (k + 2)) * Nr ^ (k + 2) := by
    have e : (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 = (k : ℝ) ^ 2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
      ring
    rw [e]
    gcongr
  calc (k : ℝ) * (2 * ((W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2)) *
        Nr ^ (k + 2))) ≤ (k : ℝ) * (2 * ((k : ℝ) ^ 2 * Nr * (2 * Nr ^ (k + 2)) * Nr ^ (k + 2))) := by
        gcongr
    _ = 4 * (k : ℝ) ^ 3 * Nr ^ (2 * k + 5) := by ring

/-- **`m = 2`** (the product of two loops): `≤ 4k² N^{2k+5}`. -/
private theorem AltDriftQ_altB_two_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    ‖altB L W E u M σ 2 b‖ ≤ 4 * (k : ℝ) ^ 2 * Nr ^ (2 * k + 5) := by
  have hI : (loopOf σ b).WF := by simp [loopOf, LoopIdx.WF]
  have hlen : (loopOf σ b).length = k := by simp [loopOf, LoopIdx.length]
  have hN0 : 0 < Nr := h.N_pos
  have hBF0 : 0 ≤ 2 * Nr ^ (k + 2) := by positivity
  have hF : ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ b).length →
      ‖LKf L W E u M J‖ ≤ 2 * Nr ^ (k + 2) := fun J hJ h2 hJk =>
    AltDriftQ_norm_LKf_le h hM hJ (by omega) (by omega)
  have h1 : ‖altB L W E u M σ 2 b‖ ≤
      (W : ℝ) ^ 2 * ((loopOf σ b).length : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2)) *
        (2 * Nr ^ (k + 2)) :=
    norm_primBil_le L h.hL W (LKf L W E u M) (LKf L W E u M) (loopOf σ b) hI hBF0 hBF0 hF hF
  rw [hlen] at h1
  refine h1.trans ?_
  have hWL := AltDriftQ_WL_le h
  have e : (W : ℝ) ^ 2 * (k : ℝ) ^ 2 * (L : ℝ) ^ 2 = (k : ℝ) ^ 2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
    ring
  rw [e]
  calc (k : ℝ) ^ 2 * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (2 * Nr ^ (k + 2)) * (2 * Nr ^ (k + 2))
      ≤ (k : ℝ) ^ 2 * Nr * (2 * Nr ^ (k + 2)) * (2 * Nr ^ (k + 2)) := by gcongr
    _ = 4 * (k : ℝ) ^ 2 * Nr ^ (2 * k + 5) := by ring

/-- **`m = 3`** (`𝓔^{(G̃)}`): `≤ 2k N^{2k+4}`. -/
private theorem AltDriftQ_altB_three_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    ‖altB L W E u M σ 3 b‖ ≤ 2 * (k : ℝ) * Nr ^ (2 * k + 4) := by
  have hI : (loopOf σ b).WF := by simp [loopOf, LoopIdx.WF]
  have hlen : (loopOf σ b).length = k := by simp [loopOf, LoopIdx.length]
  have hN0 : 0 < Nr := h.N_pos
  have hL := h.hL
  change ‖egtN L W E u M (loopOf σ b)‖ ≤ _
  unfold egtN
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hone : ∀ k' ∈ Finset.Icc 1 (loopOf σ b).length,
      ‖∑ a : Z2 L, ∑ b' : Z2 L, avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a *
          SB L a b' * LLf L W E u M ((loopOf σ b).cutGlue k' b')‖ ≤
        (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by
    intro k' hk'
    rw [Finset.mem_Icc] at hk'
    have hBG : ∀ b' : Z2 L, ‖LLf L W E u M ((loopOf σ b).cutGlue k' b')‖ ≤ Nr ^ (k + 1) := by
      intro b'
      have hJ := LoopIdx.WF.cutGlue hI b' hk'.1 hk'.2
      have hlen' := LoopIdx.length_cutGlue (loopOf σ b) b' hk'.2
      have hJl : 1 ≤ ((loopOf σ b).cutGlue k' b').a.length := by
        simp only [LoopIdx.length] at hlen'; omega
      have := norm_gloop_crudeN h.hE hM h.hu1 _ hJ hJl
      have hJk : ((loopOf σ b).cutGlue k' b').a.length = k + 1 := by
        simp only [LoopIdx.length] at hlen' hlen; omega
      rw [hJk] at this
      exact this.trans (pow_le_pow_left₀ (inv_nonneg.2 h.eta_pos.le) h.hη _)
    have hAv : ∀ a : Z2 L, ‖avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a‖ ≤
        2 * Nr ^ (k + 2) := by
      intro a
      rw [avgErr_eq_lk]
      exact h.norm_lk_le hM (fun _ : Fin 1 => (loopOf σ b).σ.getD (k' - 1) false) (fun _ => a)
        le_rfl (by omega)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Z2 L, ‖∑ b' : Z2 L, avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a *
            SB L a b' * LLf L W E u M ((loopOf σ b).cutGlue k' b')‖
        ≤ ∑ _a : Z2 L, (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b' : Z2 L, ‖avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a *
                SB L a b' * LLf L W E u M ((loopOf σ b).cutGlue k' b')‖
              ≤ ∑ b' : Z2 L, (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) * ‖SB L a b'‖ := by
                refine Finset.sum_le_sum fun b' _ => ?_
                rw [norm_mul, norm_mul]
                calc ‖avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a‖ * ‖SB L a b'‖ *
                      ‖LLf L W E u M ((loopOf σ b).cutGlue k' b')‖
                    ≤ (2 * Nr ^ (k + 2)) * ‖SB L a b'‖ * Nr ^ (k + 1) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right (hAv a) (norm_nonneg _)) (hBG b')
                        (norm_nonneg _) (by positivity)
                  _ = (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) * ‖SB L a b'‖ := by ring
            _ = (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by
                rw [← Finset.mul_sum, AltDriftQ_sum_norm_SB_row hL a, mul_one]
      _ = (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
            nsmul_eq_mul]
          push_cast
          ring
  have hsum : ‖∑ k' ∈ Finset.Icc 1 (loopOf σ b).length, ∑ a : Z2 L, ∑ b' : Z2 L,
        avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a * SB L a b' *
          LLf L W E u M ((loopOf σ b).cutGlue k' b')‖ ≤
      (k : ℝ) * ((L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k' ∈ Finset.Icc 1 (loopOf σ b).length, ‖∑ a : Z2 L, ∑ b' : Z2 L,
          avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a * SB L a b' *
            LLf L W E u M ((loopOf σ b).cutGlue k' b')‖
        ≤ ∑ _k' ∈ Finset.Icc 1 (loopOf σ b).length,
            (L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := Finset.sum_le_sum hone
      _ = (k : ℝ) * ((L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1))) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hlen]
          simp
  have hWL := AltDriftQ_WL_le h
  calc (W : ℝ) ^ 2 * ‖∑ k' ∈ Finset.Icc 1 (loopOf σ b).length, ∑ a : Z2 L, ∑ b' : Z2 L,
        avgErr L W E u M ((loopOf σ b).σ.getD (k' - 1) false) a * SB L a b' *
          LLf L W E u M ((loopOf σ b).cutGlue k' b')‖
      ≤ (W : ℝ) ^ 2 * ((k : ℝ) * ((L : ℝ) ^ 2 * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (k : ℝ) * ((W : ℝ) ^ 2 * (L : ℝ) ^ 2) * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by ring
    _ ≤ (k : ℝ) * Nr * (2 * Nr ^ (k + 2) * Nr ^ (k + 1)) := by gcongr
    _ = 2 * (k : ℝ) * Nr ^ (2 * k + 4) := by ring

/-- **`m = 4, 5`** (`ℬ₄`, `ℬ₅` for alternating `σ`): `B45_core_det_pub` with `R = 0`,
`X = B_f = 2N^{k+2}`, `≤ N^{3k+6}`. -/
private theorem AltDriftQ_altB_fourfive_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian)
    {σ : Fin k → Bool} (hσ : Alternating σ) (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr)
    (a : Fin k → Z2 L) :
    ‖B5 L W E u M σ a‖ ≤ Nr ^ (3 * k + 6) ∧ ‖B4 L W E u M σ a‖ ≤ Nr ^ (3 * k + 6) := by
  obtain ⟨h2, hk3, hk2, hC⟩ := AltDriftQ_thr hk hNr
  have hN0 : 0 < Nr := h.N_pos
  have hN1 := h.hN1
  have hX : ∀ J : LoopIdx (Z2 L), J.WF → J.length = k - 1 →
      ‖LKf L W E u M J‖ ≤ 2 * Nr ^ (k + 2) := fun J hJ hl =>
    AltDriftQ_norm_LKf_le h hM hJ (by omega) (by omega)
  have hcore := B45_core_det_pub h.hL h.hW h.hE h.hu0 h.hu1 hM hk hσ (R := 0)
    (X := 2 * Nr ^ (k + 2)) (Bf := 2 * Nr ^ (k + 2)) le_rfl (by positivity) (by positivity) hX
    (fun J hJ hl _ => hX J hJ hl) a
  have hC1 : (1 : ℝ) ≤ C5 := by unfold C5; norm_num
  have hcL0 : 0 ≤ cL L u := cL_nonneg L u
  have hcL1 : cL L u ≤ C5 * Nr := cL_le h.hL h.hu0 h.hu1 h.hLN
  have A1 : (1 - u)⁻¹ ≤ Nr := (AltDriftQ_inv_one_sub_le h.hE h.hu1).trans h.hη
  have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast h.hW
    nlinarith
  have A2 : ((W : ℝ) ^ 2 * etaT E u)⁻¹ ≤ Nr := by
    rw [mul_inv]
    calc ((W : ℝ) ^ 2)⁻¹ * (etaT E u)⁻¹ ≤ 1 * (etaT E u)⁻¹ :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hW1) (inv_nonneg.2 h.eta_pos.le)
      _ ≤ Nr := by rw [one_mul]; exact h.hη
  have hLk : ((L : ℝ) ^ 2) ^ (k - 2) ≤ Nr ^ k :=
    (pow_le_pow_left₀ (by positivity) h.hLN (k - 2)).trans (pow_le_pow_right₀ hN1 (by omega))
  have A3 : ((2 * (0 : ℝ) + 1) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) +
      ((L : ℝ) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) ≤ 4 * Nr ^ (2 * k + 2) := by
    have e0 : ((2 * (0 : ℝ) + 1) ^ 2) ^ (k - 2) = 1 := by simp
    rw [e0, one_mul]
    have h1 : 2 * Nr ^ (k + 2) ≤ 2 * Nr ^ (2 * k + 2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (by omega)) (by norm_num)
    have h2' : ((L : ℝ) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) ≤ Nr ^ k * (2 * Nr ^ (k + 2)) :=
      mul_le_mul_of_nonneg_right hLk (by positivity)
    have h3 : Nr ^ k * (2 * Nr ^ (k + 2)) = 2 * Nr ^ (2 * k + 2) := by ring
    linarith
  have A4 : cL L u ^ (k - 1) ≤ C5 ^ k * Nr ^ k := by
    calc cL L u ^ (k - 1) ≤ (C5 * Nr) ^ (k - 1) := pow_le_pow_left₀ hcL0 hcL1 _
      _ ≤ (C5 * Nr) ^ k := pow_le_pow_right₀ (by nlinarith) (by omega)
      _ = C5 ^ k * Nr ^ k := mul_pow _ _ _
  have e1 : ((180 * 40002 ^ 2 : ℝ) * (1 + Real.log L) * (RBM.Path.ellT L u ^ 2)⁻¹) = cL L u := rfl
  have hbound : 2 * (k : ℝ) * ((1 - u)⁻¹ *
      ((((W : ℝ) ^ 2 * etaT E u)⁻¹ *
        (((2 * (0 : ℝ) + 1) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) +
          ((L : ℝ) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)))) *
        ((180 * 40002 ^ 2 : ℝ) * (1 + Real.log L) * (RBM.Path.ellT L u ^ 2)⁻¹) ^ (k - 1))) ≤
      Nr ^ (3 * k + 6) := by
    rw [e1]
    have hA2' : 0 ≤ ((W : ℝ) ^ 2 * etaT E u)⁻¹ := by
      have := h.eta_pos
      positivity
    calc 2 * (k : ℝ) * ((1 - u)⁻¹ *
        ((((W : ℝ) ^ 2 * etaT E u)⁻¹ *
          (((2 * (0 : ℝ) + 1) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) +
            ((L : ℝ) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)))) * cL L u ^ (k - 1)))
        ≤ 2 * (k : ℝ) * (Nr * ((Nr * (4 * Nr ^ (2 * k + 2))) * (C5 ^ k * Nr ^ k))) := by
          have hP3 : 0 ≤ ((2 * (0 : ℝ) + 1) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) +
              ((L : ℝ) ^ 2) ^ (k - 2) * (2 * Nr ^ (k + 2)) := by positivity
          have hA1' : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith [h.hu1])
          gcongr
      _ = (2 * (k : ℝ)) * (4 * C5 ^ k) * Nr ^ (3 * k + 4) := by ring
      _ ≤ Nr * Nr * Nr ^ (3 * k + 4) := by
          have : (0 : ℝ) ≤ 4 * C5 ^ k := by positivity
          have h5 := mul_le_mul hk2 hC this (by positivity)
          gcongr
      _ = Nr ^ (3 * k + 6) := by ring
  exact ⟨hcore.1.trans hbound, hcore.2.trans hbound⟩

/-- **The crude envelope of `altB`** (`m = 0..5`, alternating `σ`, Hermitian `M`): at a size `N`
with the deterministic facts `KeyAt` and `8k³C₅^k ≤ N`, `|(altB_m)_b| ≤ N^{3k+6}`. -/
theorem AltDriftQ_norm_altB_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {σ : Fin k → Bool}
    (hσ : Alternating σ) (m : Fin 6) (b : Fin k → Z2 L) :
    ‖altB L W E u M σ m b‖ ≤ Nr ^ (3 * k + 6) := by
  obtain ⟨h2, hk3, hk2, hC⟩ := AltDriftQ_thr hk hNr
  have hN0 : 0 < Nr := h.N_pos
  have hN1 := h.hN1
  fin_cases m
  · have h0 := AltDriftQ_altB_zero_le hk h hM σ b
    calc ‖altB L W E u M σ 0 b‖ ≤ 2 * Nr ^ (k + 2) := h0
      _ ≤ Nr * Nr ^ (k + 2) := by gcongr
      _ = Nr ^ (k + 3) := by ring
      _ ≤ Nr ^ (3 * k + 6) := pow_le_pow_right₀ hN1 (by omega)
  · have h0 := AltDriftQ_altB_one_le hk h hM σ b
    calc ‖altB L W E u M σ 1 b‖ ≤ 4 * (k : ℝ) ^ 3 * Nr ^ (2 * k + 5) := h0
      _ ≤ Nr * Nr ^ (2 * k + 5) := by gcongr
      _ = Nr ^ (2 * k + 6) := by ring
      _ ≤ Nr ^ (3 * k + 6) := pow_le_pow_right₀ hN1 (by omega)
  · have h0 := AltDriftQ_altB_two_le hk h hM σ b
    have hk23 : 4 * (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 3 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith [sq_nonneg (k : ℝ)]
    calc ‖altB L W E u M σ 2 b‖ ≤ 4 * (k : ℝ) ^ 2 * Nr ^ (2 * k + 5) := h0
      _ ≤ Nr * Nr ^ (2 * k + 5) := by
          have : 4 * (k : ℝ) ^ 2 ≤ Nr := hk23.trans hk3
          gcongr
      _ = Nr ^ (2 * k + 6) := by ring
      _ ≤ Nr ^ (3 * k + 6) := pow_le_pow_right₀ hN1 (by omega)
  · have h0 := AltDriftQ_altB_three_le hk h hM σ b
    calc ‖altB L W E u M σ 3 b‖ ≤ 2 * (k : ℝ) * Nr ^ (2 * k + 4) := h0
      _ ≤ Nr * Nr ^ (2 * k + 4) := by gcongr
      _ = Nr ^ (2 * k + 5) := by ring
      _ ≤ Nr ^ (3 * k + 6) := pow_le_pow_right₀ hN1 (by omega)
  · exact (AltDriftQ_altB_fourfive_le hk h hM hσ hNr b).2
  · exact (AltDriftQ_altB_fourfive_le hk h hM hσ hNr b).1

/-- The crude envelope of `𝒬_t` on a tensor bounded by `B`: `|𝒬_tA| ≤ B + (L²)^{k-1} B`
(`|ϑ| ≤ 1`, `norm_vartheta_le_one`). -/
theorem AltDriftQ_norm_Qop_le (hL : 3 ≤ L) {k : ℕ} [NeZero k] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {A : (Fin k → Z2 L) → ℂ} {B : ℝ} (hA : ∀ b, ‖A b‖ ≤ B) (a : Fin k → Z2 L) :
    ‖Qop L t A a‖ ≤ B + ((L : ℝ) ^ 2) ^ (k - 1) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hA 0)
  unfold Qop
  refine (norm_sub_le _ _).trans (add_le_add (hA a) ?_)
  rw [norm_mul]
  have h1 : ‖Psum L A (a 0)‖ ≤ ((L : ℝ) ^ 2) ^ (k - 1) * B := by
    unfold Psum
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a 0), ‖A b‖
        ≤ ∑ _b ∈ Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a 0), B :=
          Finset.sum_le_sum fun b _ => hA b
      _ = ((Finset.univ.filter (fun a' : Fin k → Z2 L => a' 0 = a 0)).card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((L : ℝ) ^ 2) ^ (k - 1) * B := by rw [SumZeroQ_card_filter]
  have h2 := norm_vartheta_le_one hL ht0 ht1 a
  calc ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ ≤ (((L : ℝ) ^ 2) ^ (k - 1) * B) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ((L : ℝ) ^ 2) ^ (k - 1) * B := mul_one _

/-- **The crude envelope of `altQB`**: `|(𝒬_uℬ_m)_b| ≤ N^{4k+7}`. -/
theorem AltDriftQ_norm_altQB_le {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt L W E u Nr (k + 1)) (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) {σ : Fin k → Bool}
    (hσ : Alternating σ) (m : Fin 6) (b : Fin k → Z2 L) :
    ‖altQB L W E u M σ m b‖ ≤ Nr ^ (4 * k + 7) := by
  obtain ⟨h2, hk3, hk2, hC⟩ := AltDriftQ_thr hk hNr
  have hN0 : 0 < Nr := h.N_pos
  have hN1 := h.hN1
  have hB := fun b' => AltDriftQ_norm_altB_le hk h hNr hM hσ m b'
  have hQ := AltDriftQ_norm_Qop_le h.hL h.hu0 h.hu1 hB b
  refine hQ.trans ?_
  have hLk : ((L : ℝ) ^ 2) ^ (k - 1) ≤ Nr ^ k :=
    (pow_le_pow_left₀ (by positivity) h.hLN (k - 1)).trans (pow_le_pow_right₀ hN1 (by omega))
  have hk1 : (1 : ℝ) ≤ Nr ^ k := one_le_pow₀ hN1
  calc Nr ^ (3 * k + 6) + ((L : ℝ) ^ 2) ^ (k - 1) * Nr ^ (3 * k + 6)
      ≤ Nr ^ (3 * k + 6) + Nr ^ k * Nr ^ (3 * k + 6) := by gcongr
    _ = (1 + Nr ^ k) * Nr ^ (3 * k + 6) := by ring
    _ ≤ (Nr * Nr ^ k) * Nr ^ (3 * k + 6) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = Nr ^ (4 * k + 7) := by ring

end Crude

/-! ### 5.3 Integrability along the flow and the crude envelope of a local form -/

section Integ

open LocalFormCuts LocalFormCalc

variable (d : Sizes)

/-- `seqHflow d n u` is measurable. -/
theorem AltDriftQ_measurable_seqHflow (n : ℕ) (u : ℝ) : Measurable (Sizes.seqHflow d n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry d n u i j

variable {d}

/-- Every coordinate of `altB` along the flow is integrable (bounded by `N^{3k+6}`, measurable). -/
theorem AltDriftQ_integrable_altB {n : ℕ} {E u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt (d.L n) (d.W n) E u Nr (k + 1)) (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr)
    {σ : Fin k → Bool} (hσ : Alternating σ) (m : Fin 6) (b : Fin k → Z2 (d.L n)) :
    Integrable (fun ω => altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b) (Sizes.seqP d) :=
  Integrable.of_bound
    ((AltDriftQ_meas_altB E u σ m b).comp (AltDriftQ_measurable_seqHflow d n u)).aestronglyMeasurable
    (Nr ^ (3 * k + 6))
    (Filter.Eventually.of_forall fun ω =>
      AltDriftQ_norm_altB_le hk h hNr (Sizes.seqHflow_isHermitian d n u ω) hσ m b)

/-- **`𝔼 𝒬_uℬ_m = 𝒬_u 𝔼 ℬ_m`**: the Gaussian mean of `altQB` along the flow is `expAltQB`
(`𝒬_u` is a finite linear combination, and `altB` is integrable). -/
theorem AltDriftQ_integral_altQB {n : ℕ} {E : ℕ → ℝ} {u Nr : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (h : KeyAt (d.L n) (d.W n) (E n) u Nr (k + 1)) (hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ Nr)
    {σ : Fin k → Bool} (hσ : Alternating σ) (m : Fin 6) (b : Fin k → Z2 (d.L n)) :
    ∫ ω, altQB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d) =
      expAltQB d E n u σ m b := by
  have hint : ∀ b', Integrable (fun ω => altB (d.L n) (d.W n) (E n) u (Sizes.seqHflow d n u ω) σ m b')
      (Sizes.seqP d) := fun b' => AltDriftQ_integrable_altB hk h hNr hσ m b'
  unfold expAltQB altQB Qop Psum
  rw [integral_sub (hint b) ((integrable_finsetSum _ fun a _ => hint a).mul_const _),
    integral_mul_const, integral_finsetSum _ fun a _ => hint a]

/-- The one-label form with the coefficients of `F` at the fixed label tuple `b`. -/
def AltDriftQ_one {L W k K : ℕ} (F : LocalForm L W k K) (b : Fin k → Z2 L) : LocalForm L W 1 K :=
  ⟨fun _ j q => F.coef b j q⟩

theorem AltDriftQ_one_eval {L W k K : ℕ} [NeZero L] [NeZero W] (F : LocalForm L W k K)
    (b : Fin k → Z2 L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (x : Z2 L) :
    cltY (AltDriftQ_one F b) E u M x = F.eval E u M b := rfl

/-- **The crude bound of a local form** (`𝒜 = O(N^{C'+2K} η^{-K})` for a Hermitian matrix `M`):
`‖F_b(M)‖ ≤ (K+1) N^{C'} (2N³/c_κ)^K`. -/
theorem AltDriftQ_eval_det_le {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {k K : ℕ} [NeZero k] {n : ℕ}
    (F : LocalForm (d.L n) (d.W n) k K) {E u C' : ℝ} (hE : |E| ≤ 2 - κ)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u)
    (hcoef : ∀ b j q, ‖F.coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C')
    {M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ} (hM : M.IsHermitian)
    (b : Fin k → Z2 (d.L n)) :
    ‖F.eval E u M b‖ ≤ ((K : ℝ) + 1) * ((d.size n : ℕ) : ℝ) ^ C' *
      (2 * ((d.size n : ℕ) : ℝ) ^ 3 / cltCk κ) ^ K := by
  have h := cltEval_det_le (d.L n) (d.W n) κ δ E u K (AltDriftQ_one F b) C' M (b 0) hκ hδ hE hR
    (fun b' j q => hcoef b j q) hM
  rw [AltDriftQ_one_eval] at h
  exact h

/-- Measurability of the local form along the flow. -/
theorem AltDriftQ_meas_eval {k K : ℕ} (F : LocalForm (d.L n) (d.W n) k K) (E u : ℝ)
    (b : Fin k → Z2 (d.L n)) :
    Measurable fun ω => F.eval E u (Sizes.seqHflow d n u ω) b := by
  unfold LocalForm.eval
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun q _ => ?_
  refine measurable_const.mul (Finset.measurable_prod _ fun i _ => ?_)
  exact RBM.Green.measurable_green_apply d n u _ _ _

end Integ

/-! ### 5.4 The numerical absorption of the `ℚ` budget -/

section Arith

/-- `W^x ≤ N^{ε/2}` for `x ≤ ε`, `1 ≤ W ≤ N^{1/2}` (the loss `W^{C_kτ₀}` of Case 3 is absorbed). -/
theorem AltDriftQ_W_pow_le {N W x ε : ℝ} (hN1 : 1 ≤ N) (hW1 : 1 ≤ W) (hWN : W ≤ N ^ ((1 : ℝ) / 2))
    (hε : 0 ≤ ε) (hx : x ≤ ε) : W ^ x ≤ N ^ (ε / 2) := by
  have hN0 : 0 < N := by linarith
  by_cases hx0 : x ≤ 0
  · calc W ^ x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 hx0
      _ ≤ N ^ (ε / 2) := Real.one_le_rpow hN1 (by linarith)
  · have hx0' : 0 < x := not_le.mp hx0
    calc W ^ x ≤ (N ^ ((1 : ℝ) / 2)) ^ x := Real.rpow_le_rpow (by linarith) hWN hx0'.le
      _ = N ^ ((1 : ℝ) / 2 * x) := (Real.rpow_mul hN0.le _ _).symm
      _ ≤ N ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- **The numerical absorption of the `ℚ`-part budget** (pure real arithmetic).  With
`ν = N^{ε/2}`, `w = W^{-D₀}`, `D₀ = D + 1 + (ε+k)/c + |C_k|`, `N^c ≤ W ≤ N^{1/2}`, `W ≥ 40`,
`N ≥ 10`, `R, R_w ≤ N`, `B ≤ N^Γ`, `D₄ ≥ k + Γ + D/2 + 1`:
`ν (W^{C_kτ₀}(Λ + w)R^k + W^{-D₀+C_k}) + R_w^k(ν w + (ν w + B N^{-D₄})) ≤ N^ε Λ R^k + W^{-D}/5`. -/
theorem AltDriftQ_arith {N W Λ R Rw B Ck τ₀ ε D c Γ D₀ D₄ : ℝ} {k : ℕ}
    (hN : 10 ≤ N) (hW : 40 ≤ W) (hWN : W ≤ N ^ ((1 : ℝ) / 2)) (hc : 0 < c) (hband : N ^ c ≤ W)
    (hε : 0 < ε) (hD : 0 < D) (hΛ : 0 ≤ Λ) (hR0 : 0 ≤ R) (hR : R ≤ N) (hRw0 : 0 ≤ Rw)
    (hRw : Rw ≤ N) (hCτ : Ck * τ₀ ≤ ε) (hD₀ : D₀ = D + 1 + (ε + k) / c + |Ck|) (hB0 : 0 ≤ B)
    (hB : B ≤ N ^ Γ) (hD₄ : (k : ℝ) + Γ + D / 2 + 1 ≤ D₄) :
    N ^ (ε / 2) * (W ^ (Ck * τ₀) * (Λ + W ^ (-D₀)) * R ^ k + W ^ (-D₀ + Ck)) +
        Rw ^ k * (N ^ (ε / 2) * W ^ (-D₀) + (N ^ (ε / 2) * W ^ (-D₀) + B * N ^ (-D₄))) ≤
      N ^ ε * Λ * R ^ k + W ^ (-D) / 5 := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  set ν : ℝ := N ^ (ε / 2) with hν
  set w : ℝ := W ^ (-D₀) with hw
  have hν1 : 1 ≤ ν := Real.one_le_rpow hN1 (by linarith)
  have hν0 : 0 < ν := by linarith
  have hw0 : 0 < w := Real.rpow_pos_of_pos hW0 _
  have hνν : ν * ν = N ^ ε := by
    rw [hν, ← Real.rpow_add hN0]; congr 1; ring
  have hWCk : W ^ (Ck * τ₀) ≤ ν := AltDriftQ_W_pow_le hN1 hW1 hWN hε.le hCτ
  have hWCk0 : 0 ≤ W ^ (Ck * τ₀) := Real.rpow_nonneg hW0.le _
  -- the powers
  have hNk1 : 1 ≤ N ^ k := one_le_pow₀ hN1
  have hRk : R ^ k ≤ N ^ k := pow_le_pow_left₀ hR0 hR k
  have hRwk : Rw ^ k ≤ N ^ k := pow_le_pow_left₀ hRw0 hRw k
  have hRk0 : 0 ≤ R ^ k := pow_nonneg hR0 k
  have hRwk0 : 0 ≤ Rw ^ k := pow_nonneg hRw0 k
  -- `N^a ≤ W^{a/c}`
  have hNW : N ^ (ε + k) ≤ W ^ ((ε + k) / c) := by
    have hnn : 0 ≤ (ε + (k : ℝ)) / c := by positivity
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le c) hband hnn
    rwa [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hc.ne'] at h
  have hNeps : N ^ (ε + k) = N ^ ε * N ^ k := by
    rw [Real.rpow_add hN0, Real.rpow_natCast]
  have hWCkabs : W ^ Ck ≤ W ^ |Ck| := Real.rpow_le_rpow_of_exponent_le hW1 (le_abs_self _)
  -- step 1: the `w`-terms
  have e1 : ν * (W ^ (Ck * τ₀) * (Λ + w) * R ^ k) ≤ N ^ ε * Λ * R ^ k + N ^ ε * w * N ^ k := by
    calc ν * (W ^ (Ck * τ₀) * (Λ + w) * R ^ k) = (ν * W ^ (Ck * τ₀)) * (Λ + w) * R ^ k := by ring
      _ ≤ (ν * ν) * (Λ + w) * R ^ k := by gcongr
      _ = N ^ ε * Λ * R ^ k + N ^ ε * w * R ^ k := by rw [hνν]; ring
      _ ≤ N ^ ε * Λ * R ^ k + N ^ ε * w * N ^ k := by gcongr
  have e2 : ν * W ^ (-D₀ + Ck) ≤ N ^ ε * w * W ^ |Ck| := by
    have : W ^ (-D₀ + Ck) = w * W ^ Ck := by rw [hw, Real.rpow_add hW0]
    rw [this]
    calc ν * (w * W ^ Ck) ≤ N ^ ε * (w * W ^ |Ck|) := by
          have hνN : ν ≤ N ^ ε := by
            rw [← hνν]; exact le_mul_of_one_le_right hν0.le hν1
          gcongr
      _ = N ^ ε * w * W ^ |Ck| := by ring
  have e3 : Rw ^ k * (ν * w + (ν * w + B * N ^ (-D₄))) ≤ 2 * N ^ k * (N ^ ε * w) +
      N ^ k * (B * N ^ (-D₄)) := by
    have hνN : ν ≤ N ^ ε := by rw [← hνν]; exact le_mul_of_one_le_right hν0.le hν1
    have hBp : 0 ≤ B * N ^ (-D₄) := mul_nonneg hB0 (Real.rpow_nonneg hN0.le _)
    calc Rw ^ k * (ν * w + (ν * w + B * N ^ (-D₄)))
        = Rw ^ k * (2 * (ν * w)) + Rw ^ k * (B * N ^ (-D₄)) := by ring
      _ ≤ N ^ k * (2 * (N ^ ε * w)) + N ^ k * (B * N ^ (-D₄)) := by gcongr
      _ = 2 * N ^ k * (N ^ ε * w) + N ^ k * (B * N ^ (-D₄)) := by ring
  -- step 2: the sum of the `w`-terms is `≤ 4 w N^{ε+k} W^{|C_k|}`
  have hWabs1 : 1 ≤ W ^ |Ck| := Real.one_le_rpow hW1 (abs_nonneg _)
  have e4 : N ^ ε * w * N ^ k + N ^ ε * w * W ^ |Ck| + 2 * N ^ k * (N ^ ε * w) ≤
      4 * (w * (N ^ ε * N ^ k) * W ^ |Ck|) := by
    have hq : 0 ≤ w * (N ^ ε * N ^ k) * W ^ |Ck| := by positivity
    have a1 : N ^ ε * w * N ^ k ≤ w * (N ^ ε * N ^ k) * W ^ |Ck| := by
      calc N ^ ε * w * N ^ k = w * (N ^ ε * N ^ k) * 1 := by ring
        _ ≤ w * (N ^ ε * N ^ k) * W ^ |Ck| := by gcongr
    have a2 : N ^ ε * w * W ^ |Ck| ≤ w * (N ^ ε * N ^ k) * W ^ |Ck| := by
      calc N ^ ε * w * W ^ |Ck| = w * (N ^ ε * 1) * W ^ |Ck| := by ring
        _ ≤ w * (N ^ ε * N ^ k) * W ^ |Ck| := by gcongr
    have a3 : 2 * N ^ k * (N ^ ε * w) ≤ 2 * (w * (N ^ ε * N ^ k) * W ^ |Ck|) := by
      calc 2 * N ^ k * (N ^ ε * w) = 2 * (w * (N ^ ε * N ^ k) * 1) := by ring
        _ ≤ 2 * (w * (N ^ ε * N ^ k) * W ^ |Ck|) := by gcongr
    linarith
  -- step 3: `w N^{ε+k} W^{|C_k|} ≤ W^{-D-1}`
  have e5 : w * (N ^ ε * N ^ k) * W ^ |Ck| ≤ W ^ (-D - 1) := by
    calc w * (N ^ ε * N ^ k) * W ^ |Ck| = w * N ^ (ε + k) * W ^ |Ck| := by rw [hNeps]
      _ ≤ w * W ^ ((ε + k) / c) * W ^ |Ck| := by gcongr
      _ = W ^ (-D₀ + (ε + k) / c + |Ck|) := by
          rw [hw, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      _ = W ^ (-D - 1) := by congr 1; rw [hD₀]; ring
  have e6 : 4 * W ^ (-D - 1) ≤ W ^ (-D) / 10 := by
    have : W ^ (-D - 1) = W ^ (-D) * W⁻¹ := by
      rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_neg_one]
    rw [this]
    have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    have : 4 * W⁻¹ ≤ 1 / 10 := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hW0 (by norm_num)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hWD]
  -- step 4: the mean term
  have e7 : N ^ k * (B * N ^ (-D₄)) ≤ W ^ (-D) / 10 := by
    have h1 : N ^ k * (B * N ^ (-D₄)) ≤ N ^ k * (N ^ Γ * N ^ (-D₄)) := by
      gcongr
    have h2 : N ^ k * (N ^ Γ * N ^ (-D₄)) = N ^ ((k : ℝ) + Γ - D₄) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    have h3 : N ^ ((k : ℝ) + Γ - D₄) ≤ N ^ (-(D / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h4 : N ^ (-(D / 2) - 1) = N ^ (-(D / 2)) * N⁻¹ := by
      rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_neg_one]
    have h5 : N ^ (-(D / 2)) ≤ W ^ (-D) := by
      calc N ^ (-(D / 2)) = (N ^ ((1 : ℝ) / 2)) ^ (-D) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
        _ ≤ W ^ (-D) := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    have h6 : N⁻¹ ≤ 1 / 10 := by
      rw [← one_div, div_le_div_iff₀ hN0 (by norm_num)]; linarith
    have hN2 : 0 ≤ N ^ (-(D / 2)) := Real.rpow_nonneg hN0.le _
    calc N ^ k * (B * N ^ (-D₄)) ≤ N ^ (-(D / 2)) * N⁻¹ := by rw [← h4]; exact h1.trans (h2 ▸ h3)
      _ ≤ W ^ (-D) * (1 / 10) := mul_le_mul h5 h6 (by positivity) (Real.rpow_nonneg hW0.le _)
      _ = W ^ (-D) / 10 := by ring
  -- assemble
  have hsum : N ^ ε * w * N ^ k + N ^ ε * w * W ^ |Ck| + 2 * N ^ k * (N ^ ε * w) +
      N ^ k * (B * N ^ (-D₄)) ≤ W ^ (-D) / 5 := by
    have := e4.trans (mul_le_mul_of_nonneg_left e5 (by norm_num : (0 : ℝ) ≤ 4))
    have hh : 4 * W ^ (-D - 1) ≤ W ^ (-D) / 10 := e6
    linarith
  calc ν * (W ^ (Ck * τ₀) * (Λ + w) * R ^ k + W ^ (-D₀ + Ck)) +
        Rw ^ k * (ν * w + (ν * w + B * N ^ (-D₄)))
      = ν * (W ^ (Ck * τ₀) * (Λ + w) * R ^ k) + ν * W ^ (-D₀ + Ck) +
        Rw ^ k * (ν * w + (ν * w + B * N ^ (-D₄))) := by ring
    _ ≤ (N ^ ε * Λ * R ^ k + N ^ ε * w * N ^ k) + N ^ ε * w * W ^ |Ck| +
        (2 * N ^ k * (N ^ ε * w) + N ^ k * (B * N ^ (-D₄))) := by
          have := add_le_add (add_le_add e1 e2) e3
          linarith
    _ ≤ N ^ ε * Λ * R ^ k + W ^ (-D) / 5 := by linarith

end Arith

/-! ### 5.5 The section lemma (Case 3, the local form, the mean of the error) and its uniformization -/

section TermHelpers

open LocalFormCuts LocalFormCalc

/-- The crude local-form bound is polynomial: `(K+1) N^{C'} (2N³/c_0)^K ≤ N^{1+|C'|+4K}`. -/
theorem AltDriftQ_Fcrude_le {N c0 C' : ℝ} {K : ℕ} (hN1 : 1 ≤ N) (hc0 : 0 < c0)
    (hc : 2 / c0 ≤ N) (hK : (K : ℝ) + 1 ≤ N) :
    ((K : ℝ) + 1) * N ^ C' * (2 * N ^ 3 / c0) ^ K ≤ N ^ (1 + |C'| + 4 * (K : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ C' ≤ N ^ |C'| := Real.rpow_le_rpow_of_exponent_le hN1 (le_abs_self _)
  have h2 : 2 * N ^ 3 / c0 ≤ N ^ 4 := by
    have e : 2 * N ^ 3 / c0 = N ^ 3 * (2 / c0) := by ring
    rw [e]
    calc N ^ 3 * (2 / c0) ≤ N ^ 3 * N := by gcongr
      _ = N ^ 4 := by ring
  have h3 : (2 * N ^ 3 / c0) ^ K ≤ (N ^ 4) ^ K := pow_le_pow_left₀ (by positivity) h2 K
  have hC0 : 0 ≤ N ^ C' := Real.rpow_nonneg hN0.le _
  calc ((K : ℝ) + 1) * N ^ C' * (2 * N ^ 3 / c0) ^ K ≤ N * N ^ |C'| * (N ^ 4) ^ K := by
        gcongr
    _ = N ^ (1 + |C'| + 4 * (K : ℝ)) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
        have : N ^ (4 * (K : ℝ)) = (N ^ 4) ^ K := by
          rw [← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
        rw [this]

/-- The number of labels: `|Unit × (Z_L²)^k| = (L L)^k ≤ N^k`. -/
theorem AltDriftQ_card_le (d : Sizes) (k n : ℕ) :
    (Fintype.card (Unit × (Fin k → Z2 (d.L n))) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (k : ℝ) := by
  have hLL : d.L n * d.L n ≤ d.size n := by
    rw [Sizes.size_eq]
    have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
    calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  have hcard : Fintype.card (Unit × (Fin k → Z2 (d.L n))) = (d.L n * d.L n) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard, Real.rpow_natCast]
  exact_mod_cast Nat.pow_le_pow_left hLL k

/-- `R_{u,t} ≤ η_t⁻¹` for `u ≤ t < 1`, `|E| < 2`, `0 ≤ u`. -/
theorem AltDriftQ_ratioR_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E u t : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hut : u ≤ t) (ht1 : t < 1) : ratioR L E u t ≤ (etaT E t)⁻¹ := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have hηt : 0 < etaT E t := etaT_pos hE ht1
  have hℓt : 1 ≤ ellT L t := one_le_ellT (by omega) (hu0.trans hut) ht1
  have hIm1 : (spectralM E).im ≤ 1 := by
    have hsq : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    rw [spectralM_im]; linarith
  have hIm0 : 0 ≤ (spectralM E).im := (spectralM_im_pos hE).le
  have hnum : ellT L u ^ 2 * etaT E u ≤ 1 := by
    have h1 := KernelExpand_ellT_sq_mul (L := L) hu1
    have e : ellT L u ^ 2 * etaT E u = (ellT L u ^ 2 * (1 - u)) * (spectralM E).im := by
      unfold etaT; ring
    rw [e, h1]
    calc min 1 ((L : ℝ) ^ 2 * (1 - u)) * (spectralM E).im ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hIm1 hIm0 zero_le_one
      _ = 1 := one_mul 1
  unfold ratioR
  have hden : 0 < ellT L t ^ 2 * etaT E t := by positivity
  rw [div_le_iff₀ hden]
  have h1t : (1 : ℝ) ≤ ellT L t ^ 2 := one_le_pow₀ hℓt
  calc ellT L u ^ 2 * etaT E u ≤ 1 := hnum
    _ ≤ ellT L t ^ 2 := h1t
    _ = (etaT E t)⁻¹ * (ellT L t ^ 2 * etaT E t) := by field_simp

/-- `(1-u)/(1-t) ≤ η_t⁻¹` for `0 ≤ u`, `t < 1`, `|E| < 2`. -/
theorem AltDriftQ_rowRatio_le {E u t : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (ht1 : t < 1) :
    (1 - u) / (1 - t) ≤ (etaT E t)⁻¹ := by
  have h1t : 0 < 1 - t := by linarith
  have h := AltDriftQ_inv_one_sub_le hE ht1
  calc (1 - u) / (1 - t) ≤ 1 / (1 - t) := by
        gcongr; linarith
    _ = (1 - t)⁻¹ := one_div _
    _ ≤ (etaT E t)⁻¹ := h

end TermHelpers

/-! ### 5.6 A linear identity for `𝒰` -/

section Final

open LocalFormCuts LocalFormCalc

/-- The five-term linear combination `Y₁ + Y₂ + Y₃ + Y₄ - Y₅` commutes with `𝒰`. -/
theorem AltDriftQ_Ugen_five {L : ℕ} [NeZero L] {k : ℕ} [NeZero k] (E : ℝ) (σ : Fin k → Bool)
    (v w : ℝ) (Y : Fin 6 → (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Ugen L E σ v w (fun b => Y 1 b + Y 2 b + Y 3 b + Y 4 b - Y 5 b) a =
      Ugen L E σ v w (Y 1) a + Ugen L E σ v w (Y 2) a + Ugen L E σ v w (Y 3) a +
        Ugen L E σ v w (Y 4) a - Ugen L E σ v w (Y 5) a := by
  simp only [Ugen, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

end Final

end RBM.Ind

end

/-! ## 6. The `ℚ` parts on the grid with per-time levels

`AltQPartGridT` reads the levels at each section: the initial term (`m = 0`) has its level `Λ0 n`
at the time `s` only (index type `Unit × …`), the drift levels `Λq m n u` (`m ≠ 0`) are functions
of the time, and the second conclusion uses `Λq m' n (u_j)` at the tensor's own grid time.

Contents:
1. `AltDriftQ_sectionT`: the section lemma with the level hypothesis at the section `(u_n, σ_n)`
   (a `Unit × labels`-indexed `PerTimeDomAt`).
2. `AltDriftQ_termT` (`m ≠ 0`, level `Λi n (u_j)` at the section `u = u_j`) and `AltDriftQ_termT0`
   (`m = 0`, level `Λ0 n` at `u = s`, `j = 0` only): the uniformization over the grid indices.
3. `AltQPartGridT`, `altQPartGridT`: the union over `(m', j, m, σ, a)`; the indices `(0, j, …)` with
   `j ≠ 0` are dropped, so the count is at most `6 (K+1)² 2^k (L²)^k`. -/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

variable (d : Sizes)

/-- **The `ℚ` parts of the `𝒬`-process on the grid with per-time levels** (`int_K-L+QQ`,
`juaspuwp`).  The initial level `Λ0 n` is a hypothesis at the time `s` only (`Unit`-indexed
`PerTimeDomAt`), the drift levels `Λq m n u` (`m ≠ 0`) are functions of the time `u`, and the drift
bound uses `Λq m' n (u_j)` at the grid time `u_j` of the tensor. -/
def AltQPartGridT (d : Sizes) (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : Prop :=
  UpstreamSteps34Prec d κ c τ C → MainIndHyp d κ c τ E s t → Step2LocalPT d E s t →
  Step2DecayPT d E s t →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k →
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
  ∀ Λ0 : ℕ → ℝ, (∀ n, 0 ≤ Λ0 n) →
  PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1.1 0 p.2.2‖)
      (fun n _ _ => Λ0 n) →
  ∀ Λq : Fin 6 → ℕ → ℝ → ℝ, (∀ m n u, 0 ≤ Λq m n u) →
  (∀ m : Fin 6, m ≠ 0 → PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 m p.2.2‖)
      (fun n p _ => Λq m n (p.1 : ℝ))) →
  ∀ ε : ℝ, 0 < ε → ∀ D D₁ C_K : ℝ, 0 < D → 0 < D₁ → 0 ≤ C_K →
  ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((d.size n : ℕ) : ℝ) ^ C_K⌉₊) →
  ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ d),
    (pathP d).real Gᶜ ≤ ((d.size n : ℕ) : ℝ) ^ (-D₁) ∧
    ∀ ω ∈ G, ∀ σ : Fin k → Bool, Alternating σ → ∀ m ≤ K n, ∀ a : Fin k → Z2 (d.L n),
      ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n m)
          (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (s n) σ 0 b) a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε * Λ0 n *
            ratioR (d.L n) (E n) (s n) (gridTime s v K n m) ^ k + (d.W n : ℝ) ^ (-D) ∧
      ∀ j < m, ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n m)
          (fun b => dGridQN d E s v K n σ j ω b - expDriftQN d E n (gridTime s v K n j) σ b) a‖ ≤
        ((d.size n : ℕ) : ℝ) ^ ε *
            (Λq 1 n (gridTime s v K n j) + Λq 2 n (gridTime s v K n j) +
              Λq 3 n (gridTime s v K n j) + Λq 4 n (gridTime s v K n j) +
              Λq 5 n (gridTime s v K n j)) *
            ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n m) ^ k +
          (d.W n : ℝ) ^ (-D)

/-! ### 6.1 The section lemma with the level read at the section -/

section SectionT

open LocalFormCuts LocalFormCalc

/-- **The section lemma, sectionwise level** (the level hypothesis is read at the
section): for a section with `s ≤ u ≤ t' ≤ v ≤ t` and alternating `σ_n`, if the section satisfies
`‖𝒬_uℬ_i(H_u)‖ ≺ Λi` (a `Unit × labels`-indexed `PerTimeDomAt` at `(u_n, σ_n)`), the centred tensor
`𝒬_uℬ_i(H_u) - 𝔼` satisfies, with probability `≥ 1 - N^{-D₂}`, the bound
`|𝒰_{u,t',σ}(𝒬_uℬ_i(H_u) - 𝒬_u𝔼ℬ_i)_a| ≤ N^ε Λi R_{u,t'}^k + W^{-D}/5`.  The proof takes
`τ₀ = ε/(|C_k|+1)`, `D₀ = D + 1 + (ε+k)/c + |C_k|`, the level `Λi + W^{-D₀}` of the local form `F`,
Case 3 for `F - 𝔼F`, and `≺ ⇒ 𝔼` for the error; `hlev` is used at the section only. -/
theorem AltDriftQ_sectionT {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    (i : Fin 6) {Λi : ℕ → ℝ} (hΛ0 : ∀ n, 0 ≤ Λi n)
    {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) {D₂ : ℝ} (hD₂ : 0 ≤ D₂)
    (u t' : ℕ → ℝ) (σ : ℕ → Fin k → Bool) (a : ∀ n, Fin k → Z2 (d.L n))
    (hu : ∀ n, s n ≤ u n) (huv : ∀ n, u n ≤ v n) (hut' : ∀ n, u n ≤ t' n)
    (ht'v : ∀ n, t' n ≤ v n) (hσ : ∀ n, Alternating (σ n))
    (hlev : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2‖)
      (fun n _ _ => Λi n)) :
    ∀ᶠ n : ℕ in atTop,
      Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λi n *
          ratioR (d.L n) (E n) (u n) (t' n) ^ k + (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) (σ n) (u n) (t' n)
          (fun b => altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b -
            expAltQB d E n (u n) (σ n) i b) (a n)‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂)) := by
  classical
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  have hdl : DecayLoopPT d E s t :=
    decayLoopWindow d κ c τ E s t hmain (kcalDecay κ) hU.2.1 hloc hdec
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs0 n).trans (hu n)
  have hut : ∀ n, u n ≤ t n := fun n => (huv n).trans (hvt n)
  have ht't : ∀ n, t' n ≤ t n := fun n => (ht'v n).trans (hvt n)
  have ht'1 : ∀ n, t' n < 1 := fun n => (ht't n).trans_lt (ht1 n)
  have hRt' : RangeCond d τ t' := NonAltEnd_rangeCond_mono d le_rfl ht't hrange
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  -- the parameters of the local form
  obtain ⟨τ₀, hτ₀def⟩ : ∃ τ₀ : ℝ, τ₀ = ε / (|C k| + 1) := ⟨_, rfl⟩
  have hCk1 : 0 < |C k| + 1 := by positivity
  have hτ₀ : 0 < τ₀ := by rw [hτ₀def]; positivity
  have hCτ : C k * τ₀ ≤ ε := by
    calc C k * τ₀ ≤ |C k| * τ₀ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ₀.le
      _ = ε * (|C k| / (|C k| + 1)) := by rw [hτ₀def]; ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) hCk1.le) hε.le
      _ = ε := mul_one _
  obtain ⟨D₀, hD₀def⟩ : ∃ D₀ : ℝ, D₀ = D + 1 + (ε + k) / c + |C k| := ⟨_, rfl⟩
  have hD₀ : 0 < D₀ := by rw [hD₀def]; positivity
  obtain ⟨Kd, C', hC', hF⟩ := altLocalForm d κ c τ E s t hmain hdl (kcalDecay κ) k hk i τ₀ D₀
    hτ₀ hD₀
  obtain ⟨F, hcoef, hloc', hsz, hld, herr⟩ := hF u σ hu hut hσ
  -- the level of `F`
  have hΛ' : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => Λi n + (d.W n : ℝ) ^ (-D₀)) := by
    intro τd hτd Dd hDd
    filter_upwards [hlev τd hτd (Dd + 1) (by linarith), herr τd hτd (Dd + 1) (by linarith),
      NonAltEnd_ev_union d hsize 1 Dd] with n h1 h2 h3 p
    have hsub : {ω | ((d.size n : ℕ) : ℝ) ^ τd * (Λi n + (d.W n : ℝ) ^ (-D₀)) <
          ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖} ⊆
        {ω | ((d.size n : ℕ) : ℝ) ^ τd * Λi n <
          ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2‖} ∪
        {ω | ((d.size n : ℕ) : ℝ) ^ τd * (d.W n : ℝ) ^ (-D₀) <
          ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
            (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon hω
      have hF : ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖ ≤
          ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2‖ +
          ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
            (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖ := by
        have e : (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2 =
            altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
              (altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
                (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2) := by ring
        calc _ = ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
              (altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
                (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2)‖ := by rw [← e]
          _ ≤ _ := norm_sub_le _ _
      have := mul_add (((d.size n : ℕ) : ℝ) ^ τd) (Λi n) ((d.W n : ℝ) ^ (-D₀))
      linarith [hcon.1, hcon.2]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have e1 := h1 p
    have e2 := h2 p
    have hq : 0 ≤ ((d.size n : ℕ) : ℝ) ^ (-(Dd + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(Dd + 1))) +
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-(Dd + 1))) := add_le_add e1 e2
      _ = ENNReal.ofReal (2 * ((d.size n : ℕ) : ℝ) ^ (-(Dd + 1))) := by
          rw [← ENNReal.ofReal_add hq hq]; congr 1; ring
      _ ≤ ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-Dd)) :=
          ENNReal.ofReal_le_ofReal (by simpa using h3)
  -- Case 3 for the mean-zero part `F - 𝔼F`
  have hcase3 := hU.2.2.2.2 hκ hc hτ k Kd hk C' τ₀ D₀ hC' hτ₀ hD₀ E s t u t'
    (fun n => Λi n + (d.W n : ℝ) ^ (-D₀)) F σ hE hs0 hu hut hut' ht'1 hsize hband hRt' hloc hdec
    hU.2.1 hcoef hloc' hsz hld hΛ'
  -- the local-form error is `≺ W^{-D₀}`, uniformly in the labels
  have hSD2 : StochDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
        (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => (d.W n : ℝ) ^ (-D₀)) :=
    stochDomAt_of_perTimeDomAt (Sizes.seqP d) d.size (C := (k : ℝ)) (Nat.cast_nonneg _)
      (Eventually.of_forall fun n => AltDriftQ_card_le d k n) herr
  -- the exponents and the eventual facts
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = 4 * k + 8 + |C'| + 4 * Kd := ⟨_, rfl⟩
  obtain ⟨D₄, hD₄def⟩ : ∃ D₄ : ℝ, D₄ = max (D₂ + 1) ((k : ℝ) + Γ + D / 2 + 1) := ⟨_, rfl⟩
  have hD₄1 : D₂ + 1 ≤ D₄ := by rw [hD₄def]; exact le_max_left _ _
  have hD₄2 : (k : ℝ) + Γ + D / 2 + 1 ≤ D₄ := by rw [hD₄def]; exact le_max_right _ _
  have hD₄0 : 0 < D₄ := by linarith
  have hB1 := hcase3 (ε / 2) (half_pos hε) (D₂ + 1) (by linarith)
  have hB2 := hSD2 (ε / 2) (half_pos hε) D₄ hD₄0
  have hGd := gd_eventually d hmain (k + 1) (8 * (k : ℝ) ^ 3 * C5 ^ k) one_pos hu hut
  have hW40 := (tendsto_W_atTop d hc hband hsize).eventually_ge_atTop 40
  have hN10 := hsize.eventually_ge_atTop 10
  have hηt' := NonAltEnd_ev_hη d hsize hκ hE hτ hRt'
  have hc0 : 0 < cltCk κ := AzumaProxyN_c0_pos_pub hκ (hE 0)
  have hcK := hsize.eventually_ge_atTop (2 / cltCk κ)
  have hKd := hsize.eventually_ge_atTop ((Kd : ℝ) + 1)
  have hUnion := NonAltEnd_ev_union d hsize 1 D₂
  filter_upwards [hB1, hB2, hGd, hW40, hN10, hηt', hcK, hKd, hUnion, hband, hrange] with n hB1n
    hB2n hGdn hW40n hN10n hηt'n hcKn hKdn hUnionn hbandn hrangen
  -- the size index `n`
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hNr : 8 * (k : ℝ) ^ 3 * C5 ^ k ≤ N := hGdn.2.1
  have hKey : KeyAt (d.L n) (d.W n) (E n) (u n) N (k + 1) := hGdn.1
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hEn : |E n| ≤ 2 - κ := hE n
  have hEn2 : |E n| < 2 := by linarith [abs_nonneg (E n)]
  have hHerm : ∀ ω, (Sizes.seqHflow d n (u n) ω).IsHermitian := fun ω =>
    Sizes.seqHflow_isHermitian d n (u n) ω
  have hu1 : u n < 1 := lt_of_le_of_lt (hut n) (ht1 n)
  have hRn : N ^ (-1 + τ) ≤ 1 - u n := hrangen.trans (by linarith [hut n])
  -- crude envelopes
  have hXb : ∀ ω b, ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b‖ ≤
      N ^ (4 * k + 7) := fun ω b =>
    AltDriftQ_norm_altQB_le hk hKey hNr (hHerm ω) (hσ n) i b
  have hFb : ∀ ω b, ‖(F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b‖ ≤
      N ^ (1 + |C'| + 4 * (Kd : ℝ)) := fun ω b =>
    (AltDriftQ_eval_det_le hκ hτ (F n) hEn hRn (hcoef n) (hHerm ω) b).trans
      (AltDriftQ_Fcrude_le hN1 hc0 hcKn hKdn)
  have hEb : ∀ ω b, ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b -
      (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b‖ ≤ N ^ Γ := by
    intro ω b
    refine (norm_sub_le _ _).trans ?_
    have hKd0 : (0 : ℝ) ≤ Kd := Nat.cast_nonneg _
    have h1 : N ^ (4 * k + 7) ≤ N ^ (Γ - 1) := by
      rw [← Real.rpow_natCast]
      push_cast
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hΓdef]; linarith [abs_nonneg C'])
    have h2 : N ^ (1 + |C'| + 4 * (Kd : ℝ)) ≤ N ^ (Γ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hΓdef]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have h3 : N ^ Γ = N * N ^ (Γ - 1) := by
      have := Real.rpow_add hN0 1 (Γ - 1)
      rw [Real.rpow_one] at this
      rw [← this]; congr 1; ring
    have h4 : 0 ≤ N ^ (Γ - 1) := Real.rpow_nonneg hN0.le _
    have := hXb ω b
    have := hFb ω b
    nlinarith
  -- the mean of the local-form error
  have hθ0 : 0 ≤ N ^ (ε / 2) * (d.W n : ℝ) ^ (-D₀) :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmean : ∀ b, ‖expAltQB d E n (u n) (σ n) i b -
      ∫ ω', (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d)‖ ≤
      N ^ (ε / 2) * (d.W n : ℝ) ^ (-D₀) + N ^ Γ * N ^ (-D₄) := by
    intro b
    have hXm : Measurable fun ω => altQB (d.L n) (d.W n) (E n) (u n)
        (Sizes.seqHflow d n (u n) ω) (σ n) i b :=
      (AltDriftQ_meas_altQB (E n) (u n) (σ n) i b).comp (AltDriftQ_measurable_seqHflow d n (u n))
    have hFm : Measurable fun ω => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b :=
      AltDriftQ_meas_eval (F n) (E n) (u n) b
    have hXint : Integrable (fun ω => altQB (d.L n) (d.W n) (E n) (u n)
        (Sizes.seqHflow d n (u n) ω) (σ n) i b) (Sizes.seqP d) :=
      Integrable.of_bound hXm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω => hXb ω b)
    have hFint : Integrable (fun ω => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b)
        (Sizes.seqP d) :=
      Integrable.of_bound hFm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω => hFb ω b)
    have hEq : ∫ ω, (altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b -
          (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b) ∂(Sizes.seqP d) =
        expAltQB d E n (u n) (σ n) i b -
          ∫ ω', (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d) := by
      rw [integral_sub hXint hFint, AltDriftQ_integral_altQB hk hKey hNr (hσ n) i b]
    rw [← hEq]
    refine AltDriftQ_norm_integral_le (hXm.sub hFm) hθ0 (Real.rpow_nonneg hN0.le _)
      (Real.rpow_nonneg hN0.le _) (fun ω => hEb ω b) ?_
    refine (measure_mono ?_).trans hB2n
    intro ω hω
    exact ⟨((), b), hω⟩
  -- the bounds on the ratios
  have hR0 : 0 ≤ ratioR (d.L n) (E n) (u n) (t' n) := by
    have h1 := etaT_pos hEn2 hu1
    have h2 := etaT_pos hEn2 (ht'1 n)
    unfold ratioR; positivity
  have hRN : ratioR (d.L n) (E n) (u n) (t' n) ≤ N :=
    (AltDriftQ_ratioR_le (d.three_le_L n) hEn2 (hu0 n) (hut' n) (ht'1 n)).trans hηt'n
  have hRw0 : 0 ≤ (1 - u n) / (1 - t' n) :=
    div_nonneg (by linarith) (by linarith [ht'1 n])
  have hRwN : (1 - u n) / (1 - t' n) ≤ N :=
    (AltDriftQ_rowRatio_le hEn2 (hu0 n) (ht'1 n)).trans hηt'n
  have hWN := NonAltEnd_W_le_sqrt d n
  -- the inclusion of the bad events
  have hinc : {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λi n * ratioR (d.L n) (E n) (u n) (t' n) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) (σ n) (u n) (t' n)
          (fun b => altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b -
            expAltQB d E n (u n) (σ n) i b) (a n)‖} ⊆
      {ω | N ^ (ε / 2) * ((d.W n : ℝ) ^ (C k * τ₀) * (Λi n + (d.W n : ℝ) ^ (-D₀)) *
          ratioR (d.L n) (E n) (u n) (t' n) ^ k + (d.W n : ℝ) ^ (-D₀ + C k)) <
        ‖Ugen (d.L n) (E n) (σ n) (u n) (t' n)
          (fun b => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
            ∫ ω', (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))
          (a n)‖} ∪
      {ω | ∃ p : Unit × (Fin k → Z2 (d.L n)), N ^ (ε / 2) * (d.W n : ℝ) ^ (-D₀) <
        ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i p.2 -
          (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_exists] at hcon hω
    obtain ⟨h1, h2⟩ := hcon
    have hdec := AltDriftQ_decomp (d.three_le_L n) (by linarith : |E n| ≤ 2) (σ n) (hu0 n)
      (hut' n) (ht'1 n)
      (fun b => altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) i b)
      (fun b => (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) b)
      (fun b => expAltQB d E n (u n) (σ n) i b)
      (fun b => ∫ ω', (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))
      (θ := N ^ (ε / 2) * (d.W n : ℝ) ^ (-D₀))
      (θ' := N ^ (ε / 2) * (d.W n : ℝ) ^ (-D₀) + N ^ Γ * N ^ (-D₄))
      (fun b => h2 ((), b)) hmean (a n)
    have harith := AltDriftQ_arith (N := N) (W := (d.W n : ℝ)) (Λ := Λi n)
      (R := ratioR (d.L n) (E n) (u n) (t' n)) (Rw := (1 - u n) / (1 - t' n)) (B := N ^ Γ)
      (Ck := C k) (τ₀ := τ₀) (ε := ε) (D := D) (c := c) (Γ := Γ) (D₀ := D₀) (D₄ := D₄) (k := k)
      hN10n hW40n hWN hc hbandn hε hD (hΛ0 n) hR0 hRN hRw0 hRwN hCτ hD₀def
      (Real.rpow_nonneg hN0.le _) le_rfl hD₄2
    linarith
  -- the probability
  have hq : 0 ≤ N ^ (-(D₂ + 1)) := Real.rpow_nonneg hN0.le _
  have hq4 : N ^ (-D₄) ≤ N ^ (-(D₂ + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine (measure_mono hinc).trans ((measure_union_le _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (N ^ (-(D₂ + 1))) + ENNReal.ofReal (N ^ (-(D₂ + 1))) :=
        add_le_add (hB1n ((), a n))
          ((hB2n).trans (ENNReal.ofReal_le_ofReal hq4))
    _ = ENNReal.ofReal (2 * N ^ (-(D₂ + 1))) := by
        rw [← ENNReal.ofReal_add hq hq]; congr 1; ring
    _ ≤ ENNReal.ofReal (N ^ (-D₂)) := ENNReal.ofReal_le_ofReal (by simpa using hUnionn)

end SectionT

/-! ### 6.2 The uniformization over the grid indices -/

section TermT

open LocalFormCuts LocalFormCalc

/-- **The `ℚ` part for one `m ≠ 0`, per-time level, all grid indices at once**: the sectionwise lemma
`AltDriftQ_sectionT` at the section `(u_j, u_m, σ, a)` with the level `Λi n (u_j n)` (the
`TimeIcc`-indexed hypothesis `hlev` restricted to the section), uniformized by
`AltDriftQ_ev_forall_of_sections`: eventually in `n`, for every grid pair `j ≤ m ≤ K_n`, every
alternating `σ` and label `a`, the probability that
`|𝒰_{u_j,u_m,σ}(𝒬_{u_j}ℬ_i(H_{u_j}) - 𝒬_{u_j}𝔼ℬ_i)_a| > N^ε Λ_i(u_j) R_{u_j,u_m}^k + W^{-D}/5`
is `≤ N^{-D₂}`. -/
theorem AltDriftQ_termT {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (i : Fin 6) {Λi : ℕ → ℝ → ℝ} (hΛ0 : ∀ n u, 0 ≤ Λi n u)
    (hlev : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => TimeIcc s v n × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1.1 i p.2.2‖)
      (fun n p _ => Λi n (p.1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) {D₂ : ℝ} (hD₂ : 0 ≤ D₂) (K : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (j m : ℕ), j ≤ m → m ≤ K n → ∀ σ : Fin k → Bool, Alternating σ →
      ∀ a : Fin k → Z2 (d.L n),
      Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λi n (gridTime s v K n j) *
          ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n m) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n m)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j)
            (Sizes.seqHflow d n (gridTime s v K n j) ω) σ i b -
            expAltQB d E n (gridTime s v K n j) σ i b) a‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂)) := by
  classical
  by_cases hex : ∃ σ₀ : Fin k → Bool, Alternating σ₀
  swap
  · exact Eventually.of_forall fun n j m _ _ σ hσ => absurd ⟨σ, hσ⟩ hex
  obtain ⟨σ₀, hσ₀⟩ := hex
  have hU' : ∀ n, Nonempty ({p : ℕ × ℕ // p.1 ≤ p.2 ∧ p.2 ≤ K n} ×
      {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n))) := fun n =>
    ⟨⟨(0, 0), le_rfl, Nat.zero_le _⟩, ⟨σ₀, hσ₀⟩, fun _ => 0⟩
  have key := AltDriftQ_ev_forall_of_sections (U := fun n => {p : ℕ × ℕ // p.1 ≤ p.2 ∧ p.2 ≤ K n} ×
      {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n))) hU'
    (p := fun n x => Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λi n (gridTime s v K n x.1.1.1) *
          ratioR (d.L n) (E n) (gridTime s v K n x.1.1.1) (gridTime s v K n x.1.1.2) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) x.2.1.1 (gridTime s v K n x.1.1.1) (gridTime s v K n x.1.1.2)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n x.1.1.1)
            (Sizes.seqHflow d n (gridTime s v K n x.1.1.1) ω) x.2.1.1 i b -
            expAltQB d E n (gridTime s v K n x.1.1.1) x.2.1.1 i b) x.2.2‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂))) ?_
  · filter_upwards [key] with n hn j m hjm hmK σ hσ a
    exact hn ⟨⟨(j, m), hjm, hmK⟩, ⟨σ, hσ⟩, a⟩
  · intro sec
    have hsu : ∀ n, s n ≤ gridTime s v K n (sec n).1.1.1 := fun n => by
      have := GoodEvent_gridTime_mono (K := K) (hsv n) (Nat.zero_le (sec n).1.1.1)
      rwa [GoodEvent_gridTime_zero] at this
    have huv : ∀ n, gridTime s v K n (sec n).1.1.1 ≤ v n := fun n =>
      GoodEvent_gridTime_le (K := K) (hsv n) ((sec n).1.2.1.trans (sec n).1.2.2)
    refine AltDriftQ_sectionT d hU hmain hloc hdec hk hvt i
      (Λi := fun n => Λi n (gridTime s v K n (sec n).1.1.1)) (fun n => hΛ0 n _) hε hD hD₂
      (fun n => gridTime s v K n (sec n).1.1.1) (fun n => gridTime s v K n (sec n).1.1.2)
      (fun n => (sec n).2.1.1) (fun n => (sec n).2.2) hsu huv ?_ ?_ (fun n => (sec n).2.1.2) ?_
    · intro n
      exact GoodEvent_gridTime_mono (K := K) (hsv n) (sec n).1.2.1
    · intro n
      exact GoodEvent_gridTime_le (K := K) (hsv n) (sec n).1.2.2
    · intro τd hτd Dd hDd
      filter_upwards [hlev τd hτd Dd hDd] with n hn p
      exact hn (⟨gridTime s v K n (sec n).1.1.1, hsu n, huv n⟩, ⟨(sec n).2.1.1, (sec n).2.1.2⟩, p.2)

/-- **The initial `ℚ` term (`m = 0`), level at the time `s` only**: the sectionwise lemma at the
section `(s_n, u_m, σ, a)` with the level `Λ0 n` (the `Unit`-indexed hypothesis `hlev` restricted to
the section), uniformized over `m ≤ K_n`, alternating `σ` and labels `a`; the start time is
`u_0 = s_n` (`GoodEvent_gridTime_zero`). -/
theorem AltDriftQ_termT0 {κ c τ : ℝ} {C : ℕ → ℝ} {E s t : ℕ → ℝ}
    (hU : UpstreamSteps34Prec d κ c τ C) (hmain : MainIndHyp d κ c τ E s t)
    (hloc : Step2LocalPT d E s t) (hdec : Step2DecayPT d E s t)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) {v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    {Λ0 : ℕ → ℝ} (hΛ0 : ∀ n, 0 ≤ Λ0 n)
    (hlev : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (s n) (Sizes.seqHflow d n (s n) ω) p.2.1.1 0 p.2.2‖)
      (fun n _ _ => Λ0 n))
    {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) {D₂ : ℝ} (hD₂ : 0 ≤ D₂) (K : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ K n → ∀ σ : Fin k → Bool, Alternating σ →
      ∀ a : Fin k → Z2 (d.L n),
      Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λ0 n *
          ratioR (d.L n) (E n) (gridTime s v K n 0) (gridTime s v K n m) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n m)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n 0)
            (Sizes.seqHflow d n (gridTime s v K n 0) ω) σ 0 b -
            expAltQB d E n (gridTime s v K n 0) σ 0 b) a‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂)) := by
  classical
  by_cases hex : ∃ σ₀ : Fin k → Bool, Alternating σ₀
  swap
  · exact Eventually.of_forall fun n m _ σ hσ => absurd ⟨σ, hσ⟩ hex
  obtain ⟨σ₀, hσ₀⟩ := hex
  have hU' : ∀ n, Nonempty ({m : ℕ // m ≤ K n} ×
      {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n))) := fun n =>
    ⟨⟨0, Nat.zero_le _⟩, ⟨σ₀, hσ₀⟩, fun _ => 0⟩
  have key := AltDriftQ_ev_forall_of_sections (U := fun n => {m : ℕ // m ≤ K n} ×
      {σ : Fin k → Bool // Alternating σ} × (Fin k → Z2 (d.L n))) hU'
    (p := fun n x => Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Λ0 n *
          ratioR (d.L n) (E n) (gridTime s v K n 0) (gridTime s v K n x.1.1) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) x.2.1.1 (gridTime s v K n 0) (gridTime s v K n x.1.1)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n 0)
            (Sizes.seqHflow d n (gridTime s v K n 0) ω) x.2.1.1 0 b -
            expAltQB d E n (gridTime s v K n 0) x.2.1.1 0 b) x.2.2‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂))) ?_
  · filter_upwards [key] with n hn m hmK σ hσ a
    exact hn ⟨⟨m, hmK⟩, ⟨σ, hσ⟩, a⟩
  · intro sec
    have e0 : ∀ n, gridTime s v K n 0 = s n := fun n => GoodEvent_gridTime_zero
    simp only [e0]
    refine AltDriftQ_sectionT d hU hmain hloc hdec hk hvt 0 (Λi := Λ0) hΛ0 hε hD hD₂
      s (fun n => gridTime s v K n (sec n).1.1) (fun n => (sec n).2.1.1) (fun n => (sec n).2.2)
      (fun n => le_rfl) hsv ?_ ?_ (fun n => (sec n).2.1.2) ?_
    · intro n
      have := GoodEvent_gridTime_mono (K := K) (hsv n) (Nat.zero_le (sec n).1.1)
      rwa [GoodEvent_gridTime_zero] at this
    · intro n
      exact GoodEvent_gridTime_le (K := K) (hsv n) (sec n).1.2
    · intro τd hτd Dd hDd
      filter_upwards [hlev τd hτd Dd hDd] with n hn p
      exact hn (p.1, ⟨(sec n).2.1.1, (sec n).2.1.2⟩, p.2)

end TermT

/-! ### 6.3 The theorem `altQPartGridT` -/

section FinalT

open LocalFormCuts LocalFormCalc

/-- **`AltQPartGridT`, proved.**  The levels are read at each section: for each `m' ≠ 0` the term lemma `AltDriftQ_termT` (Case 3 and `altLocalForm`,
`τ₀ = ε/(|C_k|+1)`, `D₀ = D + 1 + (ε+k)/c + |C_k|`, level `Λq m' n (u_j)` at the section `u = u_j`,
kernel end `u_m`) and for `m' = 0` the term lemma `AltDriftQ_termT0` (level `Λ0 n` at `u = s`, `j = 0`
only) bound the bad event by `N^{-D₂}`, `D₂ = D₁ + 2C_K + k + 4`; the transfer from `Hflow` at `u_j` to
the grid walk is `gridTerminal_transfer`; the union bound over the `≤ 6 (K+1)² 2^k N^k ≤ 54·2^k N^{2C_K+k}`
indices `(m', j, m, σ, a)` (the indices `(0, j, …)`, `j ≠ 0`, are dropped, so the count does not grow)
gives `P(Gᶜ) ≤ N^{-D₁}` once `54·2^k ≤ N`; the drift bullet is the five-term sum
(`dGridQN_eq_dFlowQ`). -/
theorem altQPartGridT (κ c τ : ℝ) (C : ℕ → ℝ) (E s t : ℕ → ℝ) : AltQPartGridT d κ c τ C E s t := by
  intro hU hmain hloc hdec k _ hk v hsv hvt Λ0 hΛ00 hlev0 Λq hΛq0 hlev ε hε D D₁ C_K hD hD₁ hCK K
    hK0 hKup
  classical
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  obtain ⟨D₂, hD₂def⟩ : ∃ D₂ : ℝ, D₂ = D₁ + 2 * C_K + k + 4 := ⟨_, rfl⟩
  have hD₂ : 0 ≤ D₂ := by rw [hD₂def]; positivity
  -- the level read at the start index: `Λ0` for `m = 0` (at `u = s`), `Λq m` for `m ≠ 0`
  obtain ⟨Lam, hLam0, hLamq⟩ : ∃ Lam : Fin 6 → ℕ → ℝ → ℝ, (∀ n u, Lam 0 n u = Λ0 n) ∧
      ∀ i : Fin 6, i ≠ 0 → ∀ n u, Lam i n u = Λq i n u :=
    ⟨fun i n u => if i = 0 then Λ0 n else Λq i n u, fun n u => by simp,
      fun i hi n u => by simp [hi]⟩
  have hT : ∀ i : Fin 6, ∀ᶠ n : ℕ in atTop, ∀ (j m : ℕ), j ≤ m → m ≤ K n → (i = 0 → j = 0) →
      ∀ σ : Fin k → Bool, Alternating σ → ∀ a : Fin k → Z2 (d.L n),
      Sizes.seqP d {ω | ((d.size n : ℕ) : ℝ) ^ ε * Lam i n (gridTime s v K n j) *
          ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n m) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 <
        ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n m)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j)
            (Sizes.seqHflow d n (gridTime s v K n j) ω) σ i b -
            expAltQB d E n (gridTime s v K n j) σ i b) a‖} ≤
      ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D₂)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      filter_upwards [AltDriftQ_termT0 d hU hmain hloc hdec hk hsv hvt hΛ00 hlev0 hε hD hD₂ K] with
        n hn j m hjm hmK hj σ hσ a
      have hj0 : j = 0 := hj rfl
      subst hj0
      simp only [hLam0]
      exact hn m hmK σ hσ a
    · filter_upwards [AltDriftQ_termT d hU hmain hloc hdec hk hsv hvt i (Λi := Λq i)
        (fun n u => hΛq0 i n u) (hlev i hi) hε hD hD₂ K] with n hn j m hjm hmK _ σ hσ a
      simp only [hLamq i hi]
      exact hn j m hjm hmK σ hσ a
  have hTall := Filter.eventually_all.2 hT
  have hcount := hsize.eventually_ge_atTop (54 * (2 : ℝ) ^ k)
  filter_upwards [hTall, hKup, hcount] with n hTn hKn hcn
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := GoodEvent_one_le_size n
  have hN0 : 0 < N := by linarith
  have hEn2 : |E n| < 2 := by have := hE n; linarith [abs_nonneg (E n)]
  -- the index type and the bad matrix sets
  let I : Type := Fin 6 × Fin (K n + 1) × Fin (K n + 1) × (Fin k → Bool) × (Fin k → Z2 (d.L n))
  let bs : Fin 6 → ℕ → ℕ → (Fin k → Bool) → (Fin k → Z2 (d.L n)) →
      Set (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) := fun i j m σ a =>
    {M | N ^ ε * Lam i n (gridTime s v K n j) *
        ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n m) ^ k +
        (d.W n : ℝ) ^ (-D) / 5 <
      ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n m)
        (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) M σ i b -
          expAltQB d E n (gridTime s v K n j) σ i b) a‖}
  have hbs_meas : ∀ i j m σ a, MeasurableSet (bs i j m σ a) := fun i j m σ a =>
    measurableSet_lt measurable_const
      (Measurable.norm (AltDriftQ_meas_Ugen (fun b => (AltDriftQ_meas_altQB _ _ σ i b).sub
        measurable_const) _ σ _ _ a))
  let Bad : I → Set (PathΩ d) := fun idx =>
    {ω | ((idx.2.1 : ℕ) ≤ (idx.2.2.1 : ℕ) ∧ Alternating idx.2.2.2.1 ∧
        (idx.1 = 0 → (idx.2.1 : ℕ) = 0)) ∧
      pathH d s v K n idx.2.1 ω ∈ bs idx.1 idx.2.1 idx.2.2.1 idx.2.2.2.1 idx.2.2.2.2}
  have hBad : ∀ idx : I, pathP d (Bad idx) ≤ ENNReal.ofReal (N ^ (-D₂)) := by
    rintro ⟨i, j, m, σ, a⟩
    by_cases hc : (j : ℕ) ≤ m ∧ Alternating σ ∧ (i = 0 → (j : ℕ) = 0)
    · have hset : Bad (i, j, m, σ, a) = pathH d s v K n j ⁻¹' bs i j m σ a :=
        Set.ext fun ω => ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
      rw [hset, gridTerminal_transfer (d := d) (j : ℕ) (hs0 n) (hsv n) (hK0 n) (hbs_meas i j m σ a)]
      exact hTn i j m hc.1 (Nat.lt_succ_iff.mp m.2) hc.2.2 σ hc.2.1 a
    · have hset : Bad (i, j, m, σ, a) = ∅ :=
        Set.ext fun ω => ⟨fun h => absurd h.1 hc, fun h => h.elim⟩
      rw [hset, measure_empty]
      exact bot_le
  -- the counting of the indices
  have hKN : ((K n + 1 : ℕ) : ℝ) ≤ 3 * N ^ C_K := by
    have h1 : (K n : ℝ) ≤ (⌈N ^ C_K⌉₊ : ℝ) := by exact_mod_cast hKn
    have h2 : (⌈N ^ C_K⌉₊ : ℝ) < N ^ C_K + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le _)
    have h3 : 1 ≤ N ^ C_K := Real.one_le_rpow hN1 hCK
    push_cast
    linarith
  have hLL : ((d.L n * d.L n : ℕ) : ℝ) ^ k ≤ N ^ k := by
    have h : d.L n * d.L n ≤ d.size n := by
      rw [Sizes.size_eq]
      have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
      calc d.L n * d.L n = 1 * d.L n ^ 2 := by ring
        _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
    have h' : ((d.L n * d.L n : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast h
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h' k
  have hcard : (Fintype.card I : ℝ) ≤ 54 * 2 ^ k * N ^ (2 * C_K + k) := by
    have hI : Fintype.card I = 6 * ((K n + 1) * ((K n + 1) * (2 ^ k * (d.L n * d.L n) ^ k))) := by
      simp [I, Fintype.card_prod, ZMod.card]
    rw [hI]
    push_cast
    have hKK : ((K n + 1 : ℕ) : ℝ) * ((K n + 1 : ℕ) : ℝ) ≤ (3 * N ^ C_K) * (3 * N ^ C_K) :=
      mul_le_mul hKN hKN (by positivity) (by positivity)
    have hNe : N ^ (2 * C_K + k) = N ^ C_K * N ^ C_K * N ^ k := by
      rw [show 2 * C_K + (k : ℝ) = C_K + C_K + k by ring, Real.rpow_add hN0, Real.rpow_add hN0,
        Real.rpow_natCast]
    rw [hNe]
    push_cast at hKK hLL
    calc 6 * (((K n : ℝ) + 1) * (((K n : ℝ) + 1) * (2 ^ k * ((d.L n : ℝ) * (d.L n : ℝ)) ^ k)))
        = 6 * ((((K n : ℝ) + 1) * ((K n : ℝ) + 1)) * (2 ^ k * ((d.L n : ℝ) * (d.L n : ℝ)) ^ k)) := by
          ring
      _ ≤ 6 * (((3 * N ^ C_K) * (3 * N ^ C_K)) * (2 ^ k * N ^ k)) := by
          gcongr
      _ = 54 * 2 ^ k * (N ^ C_K * N ^ C_K * N ^ k) := by ring
  have hsum : (pathP d).real (⋃ idx, Bad idx) ≤ N ^ (-D₁) := by
    calc (pathP d).real (⋃ idx, Bad idx) ≤ ∑ idx, (pathP d).real (Bad idx) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ _idx : I, N ^ (-D₂) := Finset.sum_le_sum fun idx _ => by
          have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBad idx)
          rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)] at h
          exact h
      _ = (Fintype.card I : ℝ) * N ^ (-D₂) := by simp
      _ ≤ 54 * 2 ^ k * N ^ (2 * C_K + k) * N ^ (-D₂) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
      _ = 54 * 2 ^ k * N ^ (-D₁ - 4) := by
          rw [mul_assoc, ← Real.rpow_add hN0]
          congr 2
          rw [hD₂def]; ring
      _ ≤ N * N ^ (-D₁ - 4) := mul_le_mul_of_nonneg_right hcn (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-D₁ - 3) := by
          have := Real.rpow_add hN0 1 (-D₁ - 4)
          rw [Real.rpow_one] at this
          rw [← this]; congr 1; ring
      _ ≤ N ^ (-D₁) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine ⟨(⋃ idx, Bad idx)ᶜ, by rw [compl_compl]; exact hsum, ?_⟩
  intro ω hω σ hσ m hm a
  have hωB : ∀ idx, ω ∉ Bad idx := fun idx h => hω (Set.mem_iUnion.2 ⟨idx, h⟩)
  have hmK : m < K n + 1 := Nat.lt_succ_of_le hm
  have hW5 : 0 ≤ (d.W n : ℝ) ^ (-D) / 5 :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
  -- the single-term bounds along the grid walk (the start index `j = 0` for `m' = 0`)
  have good : ∀ (i : Fin 6) (j : ℕ) (hj : j < K n + 1), j ≤ m → (i = 0 → j = 0) →
      ‖Ugen (d.L n) (E n) σ (gridTime s v K n j) (gridTime s v K n m)
        (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ i b -
          expAltQB d E n (gridTime s v K n j) σ i b) a‖ ≤
        N ^ ε * Lam i n (gridTime s v K n j) *
            ratioR (d.L n) (E n) (gridTime s v K n j) (gridTime s v K n m) ^ k +
          (d.W n : ℝ) ^ (-D) / 5 := by
    intro i j hj hjm hij
    by_contra hcon
    exact hωB (i, ⟨j, hj⟩, ⟨m, hmK⟩, σ, a) ⟨⟨hjm, hσ, hij⟩, not_le.mp hcon⟩
  have hWD : 0 ≤ (d.W n : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨?_, fun j hjm => ?_⟩
  · -- the initial term `i = 0`, `j = 0`
    have h0 := good 0 0 (Nat.succ_pos _) (Nat.zero_le _) (fun _ => rfl)
    rw [hLam0] at h0
    have e0 : s n = gridTime s v K n 0 := (GoodEvent_gridTime_zero (K := K)).symm
    rw [e0]
    calc ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n m)
          (fun b => aTrueQN d E s v K n σ 0 ω b - expAltQB d E n (gridTime s v K n 0) σ 0 b) a‖
        = ‖Ugen (d.L n) (E n) σ (gridTime s v K n 0) (gridTime s v K n m)
          (fun b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n 0) (pathH d s v K n 0 ω) σ 0 b -
            expAltQB d E n (gridTime s v K n 0) σ 0 b) a‖ := rfl
      _ ≤ _ := h0
      _ ≤ _ := by linarith
  · -- the drift `i = 1, …, 5`, each at its own level `Λq i n (u_j)`
    have hjK : j < K n + 1 := by omega
    have hjm' : j ≤ m := hjm.le
    have g1 := good 1 j hjK hjm' (fun h => absurd h (by decide))
    have g2 := good 2 j hjK hjm' (fun h => absurd h (by decide))
    have g3 := good 3 j hjK hjm' (fun h => absurd h (by decide))
    have g4 := good 4 j hjK hjm' (fun h => absurd h (by decide))
    have g5 := good 5 j hjK hjm' (fun h => absurd h (by decide))
    rw [hLamq 1 (by decide)] at g1
    rw [hLamq 2 (by decide)] at g2
    rw [hLamq 3 (by decide)] at g3
    rw [hLamq 4 (by decide)] at g4
    rw [hLamq 5 (by decide)] at g5
    have h0j : 0 ≤ gridTime s v K n j := GoodEvent_gridTime_nonneg (hs0 n) (hsv n) j
    have h1j : gridTime s v K n j < 1 :=
      lt_of_le_of_lt ((GoodEvent_gridTime_le (K := K) (hsv n) (by omega : j ≤ K n)).trans (hvt n))
        (ht1 n)
    have hbr := dGridQN_eq_dFlowQ d E s v K n k σ j ω hk hEn2 h0j h1j
    have e : (fun b => dGridQN d E s v K n σ j ω b - expDriftQN d E n (gridTime s v K n j) σ b) =
        fun b => (altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ 1 b -
              expAltQB d E n (gridTime s v K n j) σ 1 b) +
            (altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ 2 b -
              expAltQB d E n (gridTime s v K n j) σ 2 b) +
            (altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ 3 b -
              expAltQB d E n (gridTime s v K n j) σ 3 b) +
            (altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ 4 b -
              expAltQB d E n (gridTime s v K n j) σ 4 b) -
            (altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ 5 b -
              expAltQB d E n (gridTime s v K n j) σ 5 b) := by
      funext b
      rw [hbr]
      unfold dFlowQ expDriftQN
      ring
    rw [e, AltDriftQ_Ugen_five (E n) σ (gridTime s v K n j) (gridTime s v K n m)
      (fun i b => altQB (d.L n) (d.W n) (E n) (gridTime s v K n j) (pathH d s v K n j ω) σ i b -
        expAltQB d E n (gridTime s v K n j) σ i b) a]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add g1 g2) g3) g4) g5).trans (le_of_eq ?_)
    ring

end FinalT

end RBM.Ind

end
