/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RBM2D.Green.EntryCore
import RBM2D.Green.LDEQuad

/-!
# The Hanson–Wright layer, second half: master identity, moment recursion, moment bound

The setting is the two-dimensional sequence model of `RBM2D/Gauss/Model.lean`, on top of the
first half `RBM2D/Green/LDEQuad.lean`.
The paper (arXiv:2503.07606) does not state this file as a lemma: it is abstract Gaussian
calculus on independent centred coordinates.  A reference `(4.7)` in a docstring below is the
quadratic large deviation estimate of the one-dimensional paper (arXiv:2501.01718), which the
declarations `norm_chaos_sq_eq_ldeQuadLHS` and `Vq_eq_ldeQuadRHS` connect to
`RBM.Green.ldeQuadLHS`, `RBM.Green.ldeQuadRHS` (`RBM2D/Green/EntryCore.lean`).

## The model

The objects are `Sizes.SeqΩ d`, `Sizes.seqP d`, `Sizes.seqGvar d`, in the namespace `RBM.Green`.
The row chaos is dimension-free, and so are the constants `2p − 1` and `2q + 1` below.  All
declarations live in `RBM.Green.RowChaos`.

## Main results (all in `RBM.Green.RowChaos`)

* `integral_chaos_mul` — **the master integration-by-parts identity**:
  `2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q ∂_{a_k}F + ∂_{b_k}Q ∂_{b_k}F)` for every tame `F`.
* `moment_recursion` — with `F = Q^q \bar Q^{q+1}`,
  `2 E|Q|^{2(q+1)} = 2q E[R Q^{q−1}\bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`.
* `two_mul_mom_succ_le` — **the Hanson–Wright recursion**,
  `2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`.
* `mom_succ_le` — **the moment bound** `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, `p ≥ 1`: the recursion
  closed by the pointwise Young inequality `RBM.Green.young_pow` with the rational parameter
  `K = 2p−1` (no `rpow`, no Hölder inequality).
* `norm_chaos_sq_eq_ldeQuadLHS`, `Vq_eq_ldeQuadRHS` — the two sides are literally
  `RBM.Green.ldeQuadLHS` and `t²·RBM.Green.ldeQuadRHS` (pure reindexing).

## Hypotheses carried

`RBM.Green.GaussIBP d` (first half) is a hypothesis `hG` of exactly the declarations that
integrate: `integral_chaos_mul`, `moment_recursion`, `integrable_of_tame_ofReal`,
`integrable_norm_pow`, `integrable_Tq_mul`, `norm_integral_Rq_le`, `two_mul_mom_succ_le`,
`integrable_Tq_pow` and `mom_succ_le`.  Nothing here is an `axiom` or a `sorry`.

## Not in this file

1. The row isometry `E[\bar h_l h_{l'} Z] = δ_{l l'} σ_l E[Z]`, the exact variance
   `E|Q|² = E[Vq]` and the identity `E[T] = 2 E[Vq]`.
2. The positive-chaos bound `E[T^p] ≤ C_p E[Vq^p]` (in `RBM2D/Green/LDEQuadT.lean`).
   `mom_succ_le` gives `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, and `T` must still be traded for the
   paper's `Vq = ∑_{k,l}σ_k‖B_{kl}‖²σ_l`.
3. `GaussIBP` for the model (in `RBM2D/Green/IBPPoly.lean`), and the instance of `RowChaos` for
   the model.

## Deviations from the paper and the one-dimensional text

* The interface lemma `Vq_eq_ldeQuadRHS` carries a factor `t²` (`Vq = t² · ldeQuadRHS`) and the
  hypothesis `σ_k = t S_{ki}` as well as `σ_k = t S_{ik}`, because
  `E|H_{ik}|² = t S_{ik}` for the flow `H_t = √t X` while `ldeQuadRHS` is written with `S`.
* The centring constant is `∑_k σ_k B_{kk}` with `σ_k = E|h_k|²`; the paper writes
  `t ∑_k S_{ik} B_{kk}`.  They agree in the model (`σ_k = t S_{ik}`), and the agreement is a
  hypothesis of `norm_chaos_sq_eq_ldeQuadLHS`, not an assumption of the theory.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Finset RBM.Gauss
open scoped NNReal

variable {d : Sizes}

namespace RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos d κ)

/-! #### The master integration-by-parts identity -/

section IBP

variable (hG : GaussIBP d)
include hG

/-- **The master identity.**  For any tame `F` whose derivatives along the two coordinates of
each row index are `FA k`, `FB k`,

`2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q · ∂_{a_k}F + ∂_{b_k}Q · ∂_{b_k}F)`.

This is Gaussian integration by parts applied once to each of the `2|κ|` coordinates of the row,
using Euler's identity `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})` to produce `Q` on the left and
`∂_α ∂_α Q = 2 r² B_{kk}` to cancel the centring constant. -/
theorem integral_chaos_mul {F : Sizes.SeqΩ d → ℂ} {FA FB : κ → Sizes.SeqΩ d → ℂ}
    (hF : Tame d F) (hFA : ∀ k, Tame d (FA k)) (hFB : ∀ k, Tame d (FB k))
    (hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)))
    (hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false))) :
    2 * ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP d)
      = ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d) := by
  classical
  have htB : ∀ k : κ, Tame d fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω := fun k =>
    ((Tame.const (d := d) (2 * (C.r : ℂ) ^ 2)).mul (C.tameB k k)).mul hF
  have htsg : ∀ k : κ, Tame d fun ω => (C.sg k : ℂ) * C.B ω k k * F ω := fun k =>
    ((Tame.const (d := d) ((C.sg k : ℂ))).mul (C.tameB k k)).mul hF
  have hcast : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2) = ((C.sg k : ℝ) : ℂ) := by
    intro k
    have : C.sg k = 2 * C.r ^ 2 * C.w k := rfl
    rw [this]; push_cast; ring
  -- the two Stein identities at the row index `k`
  have hIA : ∀ k : κ, ∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(Sizes.seqP d)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP d) := by
    intro k
    have hst := hG.stein (C.co k true) (fun ω => C.dA ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dA ω k * FA k ω)
      ((C.tamedA k).mul hF) ((htB k).add ((C.tamedA k).mul (hFA k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedA k).mul (hFA k)).integrable hG), mul_add]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dA_true k ω).fun_mul (hdFA k ω)
      simp only [hself] at hmul
      exact hmul
  have hIB : ∀ k : κ, ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(Sizes.seqP d)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP d) := by
    intro k
    have hst := hG.stein (C.co k false) (fun ω => C.dB ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dB ω k * FB k ω)
      ((C.tamedB k).mul hF) ((htB k).add ((C.tamedB k).mul (hFB k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG), mul_add]
      have hgv : ((Sizes.seqGvar d (C.co k false) : ℝ) : ℂ) = ((C.w k : ℝ) : ℂ) := by
        rw [C.gvar_tag k]; rfl
      rw [hgv]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dB_false k ω).fun_mul (hdFB k ω)
      simp only [hself] at hmul
      exact hmul
  -- the left-hand side, by Euler's identity
  have hEuler : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP d)
      = ∑ k, (∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(Sizes.seqP d)
        + ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(Sizes.seqP d)) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
          + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) := by
      intro ω
      rw [← C.sum_coord_mul_deriv ω, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hti : ∀ k : κ, Tame d fun ω => (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) :=
      fun k => (Tame.coord (C.co k true)).mul ((C.tamedA k).mul hF)
    have hti' : ∀ k : κ, Tame d fun ω => (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) :=
      fun k => (Tame.coord (C.co k false)).mul ((C.tamedB k).mul hF)
    calc ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP d)
        = ∫ ω, ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(Sizes.seqP d) := by
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = ∑ k, ∫ ω, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(Sizes.seqP d) :=
          MeasureTheory.integral_finsetSum _ fun k _ => ((hti k).add (hti' k)).integrable hG
      _ = _ := Finset.sum_congr rfl fun k _ =>
          MeasureTheory.integral_add ((hti k).integrable hG) ((hti' k).integrable hG)
  -- the left-hand side, expanded
  have hsplit : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP d)
      = 2 * ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP d) + 2 * ∫ ω, C.cen ω * F ω ∂(Sizes.seqP d) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = 2 * (C.chaos ω * F ω) + 2 * (C.cen ω * F ω) := fun ω => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw),
      MeasureTheory.integral_add
        (((Tame.const (d := d) 2).mul (C.tamechaos.mul hF)).integrable hG)
        (((Tame.const (d := d) 2).mul (C.tamecen.mul hF)).integrable hG),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the centring constant
  have hcen : ∑ k, ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
      = ∫ ω, C.cen ω * F ω ∂(Sizes.seqP d) := by
    rw [← MeasureTheory.integral_finsetSum _ fun k _ => (htsg k).integrable hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show _ = (∑ k, (C.sg k : ℂ) * C.B ω k k) * F ω
    rw [Finset.sum_mul]
  -- put everything together
  have hkey := hEuler
  rw [hsplit] at hkey
  rw [Finset.sum_congr rfl fun k _ => by rw [hIA k, hIB k]] at hkey
  have hrearr : ∑ k, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP d))
      + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP d)))
      = 2 * ∫ ω, C.cen ω * F ω ∂(Sizes.seqP d)
        + ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d) := by
    have hstep : ∀ k : κ, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
          + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP d))
        + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
          + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP d)))
        = 2 * ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP d)
          + (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d) := by
      intro k
      rw [MeasureTheory.integral_add (((C.tamedA k).mul (hFA k)).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG)]
      ring
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_add_distrib, ← Finset.mul_sum, hcen]
  rw [hrearr] at hkey
  have := hkey
  linear_combination this

end IBP

/-! #### The two quadratic sums -/

theorem eps_sq_complex (k : κ) : ((C.eps k : ℂ)) ^ 2 = 1 := by
  have h := C.eps_sq k
  have h2 : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

theorem sg_complex (k : κ) : ((C.sg k : ℝ) : ℂ) = 2 * (C.r : ℂ) ^ 2 * ((C.w k : ℝ) : ℂ) := by
  show ((2 * C.r ^ 2 * C.w k : ℝ) : ℂ) = _
  push_cast; ring

theorem conj_dA (ω : Sizes.SeqΩ d) (k : κ) : (starRingEnd ℂ) (C.dA ω k)
    = (C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * (C.U ω k + C.V ω k)) = _
  simp [Complex.conj_ofReal]

theorem conj_dB (ω : Sizes.SeqΩ d) (k : κ) : (starRingEnd ℂ) (C.dB ω k)
    = (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
      ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) = _
  simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `∑_k w_k ((∂_{a_k}Q)² + (∂_{b_k}Q)²) = 2 R`. -/
theorem sum_w_sq (ω : Sizes.SeqΩ d) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2) = 2 * C.Rq ω := by
  have hR : (2 : ℂ) * C.Rq ω = ∑ k, 2 * (((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) := by
    show (2 : ℂ) * (∑ k, ((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) = _
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hes := C.eps_sq_complex k
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [C.sg_complex k]
  show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) ^ 2
      + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) ^ 2) = _
  linear_combination (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2
      * (C.eps k : ℂ) ^ 2) * hI
    - (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2) * hes

/-- `∑_k w_k (|∂_{a_k}Q|² + |∂_{b_k}Q|²) = T`. -/
theorem sum_w_normSq (ω : Sizes.SeqΩ d) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) = ((C.Tq ω : ℝ) : ℂ) := by
  have hstep : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))
      = ((C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    have hU : ((‖C.U ω k‖ ^ 2 : ℝ) : ℂ) = C.U ω k * (starRingEnd ℂ) (C.U ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have hV : ((‖C.V ω k‖ ^ 2 : ℝ) : ℂ) = C.V ω k * (starRingEnd ℂ) (C.V ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    rw [Complex.ofReal_mul, Complex.ofReal_add, hU, hV, C.sg_complex k, C.conj_dA, C.conj_dB]
    have hes := C.eps_sq_complex k
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) *
          ((C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)))
        + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) *
          ((-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
            ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) = _
    linear_combination (-(((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.eps k : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k))))) * hI
      + (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) * hes
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Complex.ofReal_sum]
  rfl

theorem tameRq : Tame d C.Rq :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul (C.tameU k) |>.mul (C.tameV k)

theorem tameTq : Tame d fun ω => ((C.Tq ω : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω : ℝ) : ℂ))
      = fun ω => ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
        + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) := by
    funext ω; rw [C.sum_w_normSq ω]
  rw [hfun]
  exact Tame.sum _ fun k _ => (Tame.const (d := d) ((C.w k : ℝ) : ℂ)).mul
    (((C.tamedA k).mul (C.tamedA k).conj).add ((C.tamedB k).mul (C.tamedB k).conj))

/-! #### The moment recursion -/

section Recursion

variable (hG : GaussIBP d)
include hG

/-- **The moment recursion.**  Integration by parts once in each row coordinate, applied to
`F = Q^q \bar Q^{q+1}`, gives

`2 E[|Q|^{2(q+1)}] = 2q E[R Q^{q-1} \bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`,

with `R = ∑_k σ_k U_k V_k` and `T = ∑_k σ_k (|U_k|² + |V_k|²)`.  Since `‖R‖ ≤ T/2` this is the
Hanson–Wright recursion `E|Q|^{2p} ≤ (2p-1)/2 · E[T |Q|^{2p-2}]`. -/
theorem moment_recursion (q : ℕ) :
    2 * ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(Sizes.seqP d)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP d)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP d) := by
  classical
  set F : Sizes.SeqΩ d → ℂ :=
    fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) with hFdef
  set FA : κ → Sizes.SeqΩ d → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dA ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dA ω k)) with hFAdef
  set FB : κ → Sizes.SeqΩ d → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dB ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dB ω k)) with hFBdef
  have hFt : Tame d F := (C.tamechaos.pow q).mul (C.tamechaos.conj.pow (q + 1))
  have hFAt : ∀ k, Tame d (FA k) := fun k =>
    ((((Tame.const (d := d) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedA k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (d := d) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedA k).conj))
  have hFBt : ∀ k, Tame d (FB k) := fun k =>
    ((((Tame.const (d := d) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedB k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (d := d) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedB k).conj))
  have hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)) := by
    intro k ω
    have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_true k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false)) := by
    intro k ω
    have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_false k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hmain := C.integral_chaos_mul hG hFt hFAt hFBt hdFA hdFB
  -- the left-hand side
  have hL : ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP d)
      = ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(Sizes.seqP d) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show C.chaos ω * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) = _
    ring
  -- the right-hand side, pointwise
  have hptw : ∀ ω : Sizes.SeqΩ d, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
      = 2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
        + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q)) := by
    intro ω
    have hsplit : ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
        = ((q : ℂ) * (C.chaos ω ^ (q - 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2))
          + (((q + 1 : ℕ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
                + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hFAdef, hFBdef]
      ring
    rw [hsplit, C.sum_w_sq ω, C.sum_w_normSq ω]
    push_cast
    ring
  -- assemble
  have htR : Tame d fun ω => C.Rq ω * (C.chaos ω ^ (q - 1)
      * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) :=
    C.tameRq.mul ((C.tamechaos.pow (q - 1)).mul (C.tamechaos.conj.pow (q + 1)))
  have htT : Tame d fun ω => ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
      * (starRingEnd ℂ) (C.chaos ω) ^ q) :=
    C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))
  have htk : ∀ k : κ, Tame d fun ω =>
      ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) := fun k =>
    (Tame.const (d := d) ((C.w k : ℝ) : ℂ)).mul
      (((C.tamedA k).mul (hFAt k)).add ((C.tamedB k).mul (hFBt k)))
  have hR : ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP d)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP d) := by
    calc ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d)
        = ∑ k, ∫ ω, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d) :=
          Finset.sum_congr rfl fun k _ => (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ ω, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP d) :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (htk k).integrable hG).symm
      _ = ∫ ω, (2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
              * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
              * (starRingEnd ℂ) (C.chaos ω) ^ q))) ∂(Sizes.seqP d) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = _ := by
          rw [MeasureTheory.integral_add
            (((Tame.const (d := d) (2 * (q : ℂ))).mul htR).integrable hG)
            (((Tame.const (d := d) ((q : ℕ) + 1 : ℂ)).mul htT).integrable hG),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hL] at hmain
  rw [hmain, hR]

end Recursion

/-! #### The real form of the recursion -/

/-- `E|Q|^{2q}`. -/
noncomputable def mom (q : ℕ) : ℝ := ∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP d)

/-- `E[T |Q|^{2q}]`, the right-hand side of the recursion. -/
noncomputable def momT (q : ℕ) : ℝ := ∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP d)

theorem ofReal_norm_pow (ω : Sizes.SeqΩ d) (q : ℕ) :
    ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) = C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q := by
  have h2 : ((‖C.chaos ω‖ ^ 2 : ℝ) : ℂ) = C.chaos ω * (starRingEnd ℂ) (C.chaos ω) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [pow_mul, Complex.ofReal_pow, h2, mul_pow]

theorem tame_ofReal_norm_pow (q : ℕ) :
    Tame d fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q :=
    funext fun ω => C.ofReal_norm_pow ω q
  rw [hfun]
  exact (C.tamechaos.pow q).mul (C.tamechaos.conj.pow q)

theorem tame_ofReal_Tq_mul (q : ℕ) :
    Tame d fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => ((C.Tq ω : ℝ) : ℂ) *
        (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) := by
    funext ω
    rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]
  rw [hfun]
  exact C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))

omit [DecidableEq κ] in
theorem ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.sq_norm]

theorem mom_nonneg (q : ℕ) : 0 ≤ C.mom q :=
  MeasureTheory.integral_nonneg fun ω => by positivity

theorem momT_nonneg (q : ℕ) : 0 ≤ C.momT q :=
  MeasureTheory.integral_nonneg fun ω => mul_nonneg (C.Tq_nonneg ω) (by positivity)

omit [DecidableEq κ] in
theorem integral_ofReal' (f : Sizes.SeqΩ d → ℝ) :
    ∫ ω, ((f ω : ℝ) : ℂ) ∂(Sizes.seqP d) = ((∫ ω, f ω ∂(Sizes.seqP d) : ℝ) : ℂ) := by
  have h := _root_.integral_ofReal (𝕜 := ℂ) (f := f) (μ := Sizes.seqP d)
  simpa using h

theorem integral_chaos_pow (q : ℕ) :
    ∫ ω, C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q ∂(Sizes.seqP d) = ((C.mom q : ℝ) : ℂ) := by
  show _ = ((∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP d) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => ‖C.chaos ω‖ ^ (2 * q))]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω => (C.ofReal_norm_pow ω q).symm)

theorem integral_Tq_chaos_pow (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP d)
      = ((C.momT q : ℝ) : ℂ) := by
  show _ = ((∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP d) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q)
    = ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]

section Real

variable (hG : GaussIBP d)
include hG

theorem integrable_of_tame_ofReal {f : Sizes.SeqΩ d → ℝ} (hf : Tame d fun ω => ((f ω : ℝ) : ℂ)) :
    Integrable f (Sizes.seqP d) := by
  simpa using (hf.integrable hG).re

theorem integrable_norm_pow (q : ℕ) :
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP d) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_norm_pow q)

theorem integrable_Tq_mul (q : ℕ) :
    Integrable (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP d) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_Tq_mul q)

/-- The cross term of the recursion is dominated by half the control. -/
theorem norm_integral_Rq_le (p : ℕ) :
    ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(Sizes.seqP d)‖
      ≤ C.momT (p + 1) / 2 := by
  have htR : Tame d fun ω => C.Rq ω * (C.chaos ω ^ p
      * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) :=
    C.tameRq.mul ((C.tamechaos.pow p).mul (C.tamechaos.conj.pow (p + 2)))
  have hbnd : ∀ ω : Sizes.SeqΩ d,
      ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖
        ≤ 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) := by
    intro ω
    have hnorm : ‖C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)‖
        = ‖C.chaos ω‖ ^ (2 * (p + 1)) := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
      congr 1
      omega
    rw [norm_mul, hnorm]
    have h1 := C.norm_Rq_le ω
    have h2 : (0 : ℝ) ≤ ‖C.chaos ω‖ ^ (2 * (p + 1)) := by positivity
    nlinarith
  calc ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(Sizes.seqP d)‖
      ≤ ∫ ω, ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖ ∂(Sizes.seqP d) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) ∂(Sizes.seqP d) :=
        MeasureTheory.integral_mono ((htR.integrable hG).norm)
          ((C.integrable_Tq_mul hG (p + 1)).const_mul _) hbnd
    _ = C.momT (p + 1) / 2 := by
        rw [MeasureTheory.integral_const_mul]
        show 1 / 2 * C.momT (p + 1) = _
        ring

/-- **The Hanson–Wright recursion, real form**:
`2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`. -/
theorem two_mul_mom_succ_le (q : ℕ) :
    2 * C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) * C.momT q := by
  have hrec := C.moment_recursion hG q
  rw [C.integral_chaos_pow (q + 1), C.integral_Tq_chaos_pow q] at hrec
  set X : ℂ := ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
    * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP d) with hX
  have hXb : 2 * (q : ℝ) * ‖X‖ ≤ (q : ℝ) * C.momT q := by
    rcases q with _ | p
    · simp
    · have hq : ‖X‖ ≤ C.momT (p + 1) / 2 := by
        rw [hX]
        have hidx : (p + 1 : ℕ) - 1 = p := by omega
        have hidx2 : (p + 1 : ℕ) + 1 = p + 2 := by omega
        rw [hidx, hidx2]
        exact C.norm_integral_Rq_le hG p
      have hm : 0 ≤ C.momT (p + 1) := C.momT_nonneg (p + 1)
      push_cast
      nlinarith [norm_nonneg X]
  have hnorm : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖
      ≤ 2 * (q : ℝ) * ‖X‖ + ((q : ℝ) + 1) * C.momT q := by
    rw [hrec]
    have h1 : ‖2 * (q : ℂ) * X + ((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖
        ≤ ‖2 * (q : ℂ) * X‖ + ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ := norm_add_le _ _
    have h2 : ‖2 * (q : ℂ) * X‖ = 2 * (q : ℝ) * ‖X‖ := by
      rw [norm_mul, norm_mul]
      simp
    have h3 : ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ = ((q : ℝ) + 1) * C.momT q := by
      have hc : ((q : ℕ) + 1 : ℂ) = (((q : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (C.momT_nonneg q),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)]
    linarith
  have hlhs : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖ = 2 * C.mom (q + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (C.mom_nonneg (q + 1))]
    simp
  rw [hlhs] at hnorm
  linarith

/-! #### The paper's right-hand side `Vq`

`Vq ω = ∑_{k,l} σ_k ‖B_{kl}‖² σ_l` is the random control of the paper's quadratic large deviation
estimate.  At `q = 0` the recursion is the identity `2 E|Q|² = E[T]`; the exact variance
`E|Q|² = E[Vq]` needs the row isometry and is not part of this file. -/

/-- The paper's right-hand side `∑_{k,l} σ_k ‖B_{kl}‖² σ_l` (a random quantity, since `B` is). -/
noncomputable def Vq (ω : Sizes.SeqΩ d) : ℝ := ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l

omit hG in
theorem Vq_complex (ω : Sizes.SeqΩ d) : ((C.Vq ω : ℝ) : ℂ)
    = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)) := by
  show ((∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normSq]
  ring

omit hG in
theorem tame_ofReal_Vq : Tame d fun ω => ((C.Vq ω : ℝ) : ℂ) := by
  rw [funext fun ω => C.Vq_complex ω]
  exact Tame.sum _ fun k _ => Tame.sum _ fun l _ =>
    (Tame.const (d := d) (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul
      ((C.tameB k l).mul (C.tameB k l).conj)

omit hG in
theorem Tq_complex (ω : Sizes.SeqΩ d) : ((C.Tq ω : ℝ) : ℂ)
    = ∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.U ω k)
      + C.V ω k * (starRingEnd ℂ) (C.V ω k)) := by
  show ((∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]

/-! #### Closing the recursion: `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` -/

/-- `E[T^q]`, the positive-chaos moment that the recursion reduces everything to. -/
noncomputable def momTpow (q : ℕ) : ℝ := ∫ ω, C.Tq ω ^ q ∂(Sizes.seqP d)

theorem integrable_Tq_pow (q : ℕ) : Integrable (fun ω => C.Tq ω ^ q) (Sizes.seqP d) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω => ((C.Tq ω ^ q : ℝ) : ℂ)) = fun ω => ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tameTq.pow q

omit hG in
theorem momTpow_nonneg (q : ℕ) : 0 ≤ C.momTpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Tq_nonneg ω) q

/-- **Hanson–Wright, the moment bound.**  `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` for `p ≥ 1`.

The recursion `2E|Q|^{2(q+1)} ≤ (2q+1)E[T|Q|^{2q}]` is closed by the pointwise Young inequality
`RBM.Green.young_pow` with the *rational* parameter `K = 2q+1`, which keeps every exponent a
natural number and needs no Hölder inequality.

What remains, to reach the paper's `∑_{k,l}σ_k‖B_{kl}‖²σ_l`, is the positive-chaos bound
`E[T^p] ≤ C_p E[Vq^p]`; see the file header. -/
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := by
  set K : ℝ := 2 * (q : ℝ) + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  -- the pointwise Young inequality
  have hpt : ∀ ω : Sizes.SeqΩ d, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1)) := by
    intro ω
    have hT := C.Tq_nonneg ω
    have hy := young_pow q (mul_nonneg hT hK0.le) (sq_nonneg ‖C.chaos ω‖)
    rw [mul_pow] at hy
    have hg : ∀ j : ℕ, ‖C.chaos ω‖ ^ (2 * j) = (‖C.chaos ω‖ ^ 2) ^ j := fun j => pow_mul _ 2 j
    rw [hg q, hg (q + 1)]
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Tq ω * (‖C.chaos ω‖ ^ 2) ^ q)
        = ((q : ℝ) + 1) * (C.Tq ω * K * (‖C.chaos ω‖ ^ 2) ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * (‖C.chaos ω‖ ^ 2) ^ (q + 1))
        = C.Tq ω ^ (q + 1) * K ^ (q + 1) + (q : ℝ) * (‖C.chaos ω‖ ^ 2) ^ (q + 1) := by
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  -- integrate
  have hi1 := C.integrable_Tq_pow hG (q + 1)
  have hi2 := C.integrable_norm_pow hG (q + 1)
  have hmomT : C.momT q ≤ (K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1) := by
    calc C.momT q ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1))) ∂(Sizes.seqP d) :=
          MeasureTheory.integral_mono (C.integrable_Tq_mul hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  -- close the recursion
  have hrec := C.two_mul_mom_succ_le hG q
  rw [← hKdef] at hrec
  have hm := C.mom_nonneg (q + 1)
  have ht := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    field_simp
    ring
  have hchain : 2 * C.mom (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    refine hrec.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hmomT hK0.le
  have hB : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hq1]; linarith
  have hA : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have h1 : (q : ℝ) / ((q : ℝ) + 1) * C.mom (q + 1) ≤ C.mom (q + 1) := by
    nlinarith [hm, hB]
  have h3 : K ^ (q + 1) / ((q : ℝ) + 1) * C.momTpow (q + 1)
      ≤ K ^ (q + 1) * C.momTpow (q + 1) := mul_le_mul_of_nonneg_right hA ht
  linarith

end Real

/-! #### The shape of `RBM.Green.ldeQuadLHS` and `RBM.Green.ldeQuadRHS`

The chaos and its control are literally the two sides of the quadratic large deviation estimate
`RBM.Green.LDEQuad` (`RBM2D/Green/EntryCore.lean`), once the row chaos is indexed by
`{k // k ≠ i}` with `h_k = H_{ik}` and `σ_k = t S_{ik}`.  These two lemmas are pure reindexing
(`Finset.sum_subtype`) and contain no analysis; they are the interface through which a
concrete instance meets `RBM.Green.LDEQuad`. -/

section LDEShape

variable {n : Type*} [Fintype n] [DecidableEq n] {i : n}

omit [DecidableEq κ] in
theorem sum_erase_eq {M : Type*} [AddCommMonoid M] (f : n → M) :
    ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {k : n // k ≠ i}, f k.1 :=
  Finset.sum_subtype _ (fun x => by simp [Finset.mem_erase]) _

/-- **The chaos is the left-hand side of (4.7).** -/
theorem norm_chaos_sq_eq_ldeQuadLHS (C : RowChaos d {k : n // k ≠ i}) (ω : Sizes.SeqΩ d)
    (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hh : ∀ k : {k : n // k ≠ i}, C.h ω k = H i k.1)
    (hhc : ∀ k : {k : n // k ≠ i}, (starRingEnd ℂ) (C.h ω k) = H k.1 i)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1) :
    ‖C.chaos ω‖ ^ 2 = ldeQuadLHS H G S t i := by
  have e1 : ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
        H i k * greenMinor G i k l * H l i
      = ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
        C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    rw [sum_erase_eq (i := i)
      fun k => ∑ l ∈ Finset.univ.erase i, H i k * greenMinor G i k l * H l i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_erase_eq (i := i) fun l => H i k.1 * greenMinor G i k.1 l * H l i]
    exact Finset.sum_congr rfl fun l _ => by rw [hh k, hB k l, hhc l]
  have e2 : (t : ℂ) * ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor G i k k
      = ∑ k : {k : n // k ≠ i}, ((C.sg k : ℝ) : ℂ) * C.B ω k k := by
    rw [sum_erase_eq (i := i) fun k => (S i k : ℂ) * greenMinor G i k k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB k k, hsg k, Complex.ofReal_mul]
    ring
  show ‖C.chaos ω‖ ^ 2 = ‖_ - _‖ ^ 2
  rw [e1, e2]
  rfl

/-- **`Vq` is the right-hand side of (4.7)**, up to the factor `t²` coming from
`E|H_{ik}|² = t S_{ik}`. -/
theorem Vq_eq_ldeQuadRHS (C : RowChaos d {k : n // k ≠ i}) (ω : Sizes.SeqΩ d)
    (G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    C.Vq ω = t ^ 2 * ldeQuadRHS S G i := by
  show ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
      C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l = _
  rw [show ldeQuadRHS S G i = ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i from rfl,
    sum_erase_eq (i := i) fun k => ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_erase_eq (i := i) fun l => S i k.1 * ‖greenMinor G i k.1 l‖ ^ 2 * S l i,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hB k l, hsg k, hsg' l]
  ring

end LDEShape

end RowChaos

end RBM.Green
