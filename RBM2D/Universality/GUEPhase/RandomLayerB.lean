/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.RandomLayerA
import RBM2D.Universality.GUEPhase.LLTransfer
import RBM2D.Universality.GUEPhase.PathBounds
import RBM2D.Universality.GUEPhase.Eq729B
import RBM2D.Universality.GUEPhase.KPrim
import RBM2D.Universality.ZeroModeProfile
import RBM2D.Main.Endpoints

/-!
# The §7.2 random layer, assembly: `g1Row : G1Row` (`d = 2`)

`g1Row : G1Row` (no hypothesis): for `P7Out`, `P7ExpOut`, `𝔠 > 0`, `d` with `Admissible 𝔠 d` and
`0 < τ_U ≤ ouTauMax 𝔠`, the two statements `OULL d τ_U` and `OUEq747 d τ_U` hold.  Both are per
sequence `(κ, E, t, δ, p)`, so the proof is the assembly of one sequence, with the energy margin
`κ/2` of the size-level conditions and the exponent `τ_D = τ_U/2`:

* `OULL`, at `z_n = E_n + i η_LL`, `η_LL = ouEtaLL d τ_U n = N^{-1+2τ_U}`:
  `RandomLayer_rowsLL` and `RandomLayer_rows` (`τ = τ_U`) give `|E'| ≤ 2 - κ/2`,
  `0 ≤ t₁ ≤ t₀ < 1`, `h730`, `hscale`, `hell` and the range `N^{-1+τ_U} ≤ 1 - t₁`
  (`E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`); `P7Out` at
  `(𝔠, d, κ/2, E', τ_U, t₁)` gives `MLConcl d E' t₁`; `gueK_exists` (loops of length
  `≤ 8 = 4 n₀`, `n₀ = 2`) gives `K̃` at each `n`; `gueGrid_pathBounds` (`n₀ = 2`, `τ_U/2`, `κ/2`)
  gives `GUEPathBounds`; `oull_of_pathBounds` gives the moment bound.
* `OUEq747`, at `z_n = E_n + i η_Q`, `η_Q = ouEtaQ d n = W^{2/3}/N`: `RandomLayer_rowsQ` and
  `RandomLayer_rows` (`τ = 𝔠/3`) give the same eight facts; `P7Out` and `P7ExpOut` give
  `MLConcl d E' t₁` and `MLExpConcl d E' t₁`; `gueK_exists` (length `≤ 12 = 4 n₀`, `n₀ = 3`);
  `gueGrid_pathBounds` (`n₀ = 3`) gives `GUEPathBounds`; `Eq729B_eq747_of_inputs`
  (`n₀ = 3`, margin `κ`) gives the bound.  (`GUEPathBounds` does not depend on the margin, so the
  margin `κ/2` of the size-level conditions and the margin `κ` of `Eq729B_eq747_of_inputs` meet at
  the same `GUEPathBounds d E' t₁ t₀ (gueGridK d 3) 3 Kt`.)

Conventions (`d = 2`): `P7Out` / `P7ExpOut` are instantiated at
`(𝔠, d, κ/2, E', τ, t₁, range condition)`; the statements `OULL`/`OUEq747` are per sequence, on
`ouMat`/`ouP`; the hypotheses are `Admissible 𝔠 d` and `τU ≤ ouTauMax 𝔠`; the size scale is
`N = (W L)²`.  No case split on `κ` is needed: the hypothesis `|E n| ≤ 2 - κ` is used only
through `|E n| ≤ 2 - κ/2`, which holds for every `κ > 0`.

Helpers are `private` and carry the prefix `RandomLayerB_`; the only public declaration is
`g1Row`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path

/-- **One sequence `(κ, E, t, δ, p)`**: the moment bound of `OULL`.  Margin `κ/2` and exponent
`τ_D = τ_U/2` in the size-level conditions, `n₀ = 2`. -/
private theorem RandomLayerB_oull_seq (h7 : P7Out) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (d : Sizes)
    (hd : RBM.Endpoints.Admissible 𝔠 d) {τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠)
    {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) {δ : ℝ} (hδ : 0 < δ) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x : Idx (d.L n) (d.W n),
      ∫ ω, ‖green (ouMat (d.L n) (d.W n) (t n) ω)
          ((E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) x x‖ ^ (2 * p)
        ∂(ouP (d.L n) (d.W n)) ≤ ((d.size n : ℕ) : ℝ) ^ δ := by
  have hk : 0 < κ / 2 := by positivity
  have hτU1 : τU ≤ 1 / 100 := hτUm.trans (min_le_right _ _)
  have he' : ∀ n, |E n| ≤ 2 - κ / 2 := fun n => by linarith [hE n]
  have hη0 : ∀ n, 0 < ouEtaLL d τU n := RandomLayer_etaLL_pos d τU
  have hη1 : ∀ n, ouEtaLL d τU n ≤ 1 := RandomLayer_etaLL_le_one d (by linarith)
  obtain ⟨r1, r2, r3, r5⟩ := RandomLayer_rowsLL d (𝔠 := 𝔠) (κ := κ / 2) (τU := τU) h𝔠 hd hk hτU
    hτUm (t := t) (fun n => (ht n).1) (fun n => (ht n).2)
  obtain ⟨hE', ht1, ht10, ht0, h730, hscale, hell, hrange⟩ :=
    RandomLayer_rows d (k := κ / 2) (τD := τU / 2) (τ := τU) hk (by positivity)
      (e := E) (η := ouEtaLL d τU) (t := t)
      (fun n => (E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I) (fun n => rfl) he' hη0 hη1
      (fun n => (ht n).1) r1 r2 r3 r5
  have hB : RBM.Ind.MLConcl d
      (fun n => lemE ((E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (t n)) *
        lemT ((E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I)) :=
    h7 𝔠 h𝔠 d hd (κ / 2) hk _ hE' τU hτU _ ht1 hrange
  have hE'2 : ∀ n, |lemE ((E n : ℂ) + ((ouEtaLL d τU n : ℝ) : ℂ) * Complex.I)| < 2 :=
    fun n => by have := hE' n; linarith
  choose Kt hKinit hK hK2 using fun n =>
    gueK_exists (d.L n) (d.W n) (d.three_le_L n) (hE'2 n) (ht1 n) (ht10 n) (ht0 n) (4 * 2)
  have hP := gueGrid_pathBounds d (𝔠 := 𝔠) (κ := κ / 2) (τU := τU / 2) h𝔠 hd hk (by positivity)
    2 le_rfl hE' ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB
  exact oull_of_pathBounds d hκ hτU (by linarith) 2 (by norm_num) hd.1 hE (fun n => (ht n).1)
    Kt hP δ hδ p

/-- **(7.47) along one sequence** `(κ, E, t, δ)`: the bound of `OUEq747`.  Margin `κ/2` and
exponent `τ_D = τ_U/2` in
the rows, range exponent `τ = 𝔠/3`, `n₀ = 3` in both `gueGrid_pathBounds` and
`Eq729B_eq747_of_inputs`. -/
private theorem RandomLayerB_eq747_seq (h7 : P7Out) (h7e : P7ExpOut) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (d : Sizes) (hd : RBM.Endpoints.Admissible 𝔠 d) {τU : ℝ} (hτU : 0 < τU)
    (hτUm : τU ≤ ouTauMax 𝔠) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω)
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b ∂(ouP (d.L n) (d.W n))) -
          profileTilde (d.L n) (d.W n) (ouZeta (t n))
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b‖ ≤
        (d.W n : ℝ) ^ δ * (Meta (d.L n) (d.W n)
          ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3 := by
  have hk : 0 < κ / 2 := by positivity
  have he' : ∀ n, |E n| ≤ 2 - κ / 2 := fun n => by linarith [hE n]
  obtain ⟨r1, r2, r3, r5⟩ := RandomLayer_rowsQ d (𝔠 := 𝔠) (κ := κ / 2) (τU := τU) h𝔠 hd hk hτU
    hτUm (t := t) (fun n => (ht n).1) (fun n => (ht n).2)
  obtain ⟨hE', ht1, ht10, ht0, h730, hscale, hell, hrange⟩ :=
    RandomLayer_rows d (k := κ / 2) (τD := τU / 2) (τ := 𝔠 / 3) hk (by positivity)
      (e := E) (η := ouEtaQ d) (t := t)
      (fun n => (E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) (fun n => rfl) he'
      (RandomLayer_etaQ_pos d) (RandomLayer_etaQ_le_one d) (fun n => (ht n).1) r1 r2 r3 r5
  have hB : RBM.Ind.MLConcl d
      (fun n => lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (t n)) *
        lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I)) :=
    h7 𝔠 h𝔠 d hd (κ / 2) hk _ hE' (𝔠 / 3) (by positivity) _ ht1 hrange
  have hBe : RBM.Evol.MLExpConcl d
      (fun n => lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (t n)) *
        lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I)) :=
    h7e 𝔠 h𝔠 d hd (κ / 2) hk _ hE' (𝔠 / 3) (by positivity) _ ht1 hrange
  have hE'2 : ∀ n, |lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I)| < 2 :=
    fun n => by have := hE' n; linarith
  choose Kt hKinit hK hK2 using fun n =>
    gueK_exists (d.L n) (d.W n) (d.three_le_L n) (hE'2 n) (ht1 n) (ht10 n) (ht0 n) (4 * 3)
  have hP := gueGrid_pathBounds d (𝔠 := 𝔠) (κ := κ / 2) (τU := τU / 2) h𝔠 hd hk (by positivity)
    3 (by norm_num) hE' ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB
  exact Eq729B_eq747_of_inputs d h𝔠 hd hκ hτU hτUm 3 le_rfl hE ht
    (E' := fun n => lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (t0 := fun n => lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (t1 := fun n => (1 - ouZeta (t n)) * lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) Kt hKinit hK hK2 hBe hP δ hδ

/-- **`g1Row`, proved**: `P7Out` and `P7ExpOut` at the band time `t₁ = (1 - ζ(t_n)) t₀` give the
two statements `OULL d τ_U` and `OUEq747 d τ_U` for `𝐇_t`, for every `𝔠 > 0`, every `d` with
`Admissible 𝔠 d` and every `0 < τ_U ≤ ouTauMax 𝔠`.  The hypotheses `P7Out`, `P7ExpOut` are those of
`G1Row` itself; `g1Row` has no other hypothesis. -/
theorem g1Row : RBM.Univ.G1Row := by
  intro h7 h7e 𝔠 h𝔠 d hd τU hτU hτUm
  refine ⟨?_, ?_⟩
  · intro κ hκ E hE t ht δ hδ p
    exact RandomLayerB_oull_seq h7 h𝔠 d hd hτU hτUm hκ hE ht hδ p
  · intro κ hκ E hE t ht δ hδ
    exact RandomLayerB_eq747_seq h7 h7e h𝔠 d hd hτU hτUm hκ hE ht hδ

end RBM.Univ.GUEPhase

end
