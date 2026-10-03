/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.ContinuumSymbol

/-!
# Swap symmetry of the infinite-volume kernel

`K_{ξ,∞}(x₂,x₁) = K_{ξ,∞}(x₁,x₂)`, from the symmetry of the symbol `Ŝ` in `(p₁,p₂)`
(equation `(eq_symbol)`) and the exchange of the two coordinates in the square integral
`(eq_Kinf)`.
-/

namespace RBM

open Real MeasureTheory

private theorem KinfSwap_integrand (ξ : ℂ) (x : ℤ × ℤ) (p : ℝ × ℝ) :
    KinfIntegrand ξ (x.2, x.1) p = KinfIntegrand ξ x p.swap := by
  have hS : ScontReal p.swap = ScontReal p := by
    unfold ScontReal
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have hph : continuumPhase (x.2, x.1) p = continuumPhase x p.swap := by
    unfold continuumPhase
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  unfold KinfIntegrand continuumNumerator Dcont Scont
  rw [hph, hS]

theorem Kinf_swap :
    ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ x : ℤ × ℤ, Kinf ξ (x.2, x.1) = Kinf ξ x := by
  intro ξ hξ x
  rw [Kinf_eq_square_integral ξ hξ (x.2, x.1), Kinf_eq_square_integral ξ hξ x]
  congr 1
  simp_rw [KinfSwap_integrand ξ x]
  exact setIntegral_prod_swap (μ := volume) (ν := volume)
    (Set.Icc (-Real.pi) Real.pi) (Set.Icc (-Real.pi) Real.pi) (KinfIntegrand ξ x)

end RBM
