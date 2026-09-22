/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateDerivative

/-!
# Matrix-flow term as a finite sum of coordinate derivatives

The matrix and spectral parts of the fixed-sample loop derivative are separated.
Only the matrix part is identified with the finite coordinate sum.
-/

namespace RBM.Gauss

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

private abbrev BlockMat (L W : ℕ) :=
  Matrix (BlockIndex L W) (BlockIndex L W) ℂ

/-- Linear dependence of one signed resolvent derivative on its matrix direction. -/
noncomputable def gsigDirectionMap (u : ℝ) (ω : Ω L W) (z : ℂ) (σ : Bool) :
    BlockMat L W →ₗ[ℝ] BlockMat L W :=
  let G := Gsig (HflowBlock L W u ω) z σ
  (-(ContinuousLinearMap.mulLeftRight ℝ (BlockMat L W) G G)).toLinearMap

@[simp] theorem gsigDirectionMap_apply (u : ℝ) (ω : Ω L W) (z : ℂ)
    (σ : Bool) (B : BlockMat L W) :
    gsigDirectionMap L W u ω z σ B =
      -(Gsig (HflowBlock L W u ω) z σ * B *
        Gsig (HflowBlock L W u ω) z σ) := by
  simp [gsigDirectionMap, ContinuousLinearMap.mulLeftRight_apply]

/-- The finite-word directional derivative as a real-linear map of the matrix direction. -/
noncomputable def wordDirectionMap (u : ℝ) (ω : Ω L W) (z : ℂ) :
    (l : List (Bool × Z2 L)) → BlockMat L W →ₗ[ℝ] BlockMat L W
  | [] => 0
  | p :: l =>
      let G := Gsig (HflowBlock L W u ω) z p.1
      let E := Eblk L W p.2
      let tail := l.foldr (fun q M =>
        Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1
      { toFun := fun B =>
          (gsigDirectionMap L W u ω z p.1 B * E) * tail +
            (G * E) * wordDirectionMap u ω z l B
        map_add' := by
          intro B C
          simp only [map_add, mul_add, add_mul]
          noncomm_ring
        map_smul' := by
          intro r B
          simp only [map_smul, RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
            smul_add] }

@[simp] theorem wordDirectionMap_nil (u : ℝ) (ω : Ω L W) (z : ℂ)
    (B : BlockMat L W) :
    wordDirectionMap L W u ω z [] B = 0 := rfl

@[simp] theorem wordDirectionMap_cons (u : ℝ) (ω : Ω L W) (z : ℂ)
    (p : Bool × Z2 L) (l : List (Bool × Z2 L)) (B : BlockMat L W) :
    wordDirectionMap L W u ω z (p :: l) B =
      (gsigDirectionMap L W u ω z p.1 B * Eblk L W p.2) *
        l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1 +
      (Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
        wordDirectionMap L W u ω z l B := rfl

/-- Reindexing the finite coordinate expansion of the Gaussian matrix. -/
theorem Xblock_eq_sum_coordinates (ω : Ω L W) :
    (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm =
      ∑ c : Coord L W, (ω c) • coordinateBlock L W c := by
  rw [Xmat_eq_sum_coordinates]
  ext i j
  simp [coordinateBlock, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]

/-- The directional map at one Gaussian coordinate equals its established derivative. -/
theorem wordDirectionMap_coordinate (u : ℝ) (ω : Ω L W)
    (c : Coord L W) (z : ℂ) (l : List (Bool × Z2 L)) :
    wordDirectionMap L W u ω z l (Real.sqrt u • coordinateBlock L W c) =
      coordinateWordDeriv L W u ω c z l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [wordDirectionMap_cons, coordinateWordDeriv, ih,
        gsigDirectionMap_apply, gsigCoordinateDeriv]

/-- The matrix-flow direction is the weighted sum of coordinate directions. -/
theorem time_direction_eq_coordinate_sum (ω : Ω L W) {u : ℝ} (hu : 0 < u) :
    (1 / (2 * Real.sqrt u)) •
        (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm =
      (1 / (2 * u)) • ∑ c : Coord L W,
        (ω c) • (Real.sqrt u • coordinateBlock L W c) := by
  have hsqrt : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hscalar : (1 / (2 * u)) * Real.sqrt u = 1 / (2 * Real.sqrt u) := by
    field_simp
    nlinarith [Real.sq_sqrt hu.le]
  rw [Xblock_eq_sum_coordinates L W ω]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hscalar]
  ring

/-- Matrix-flow contribution to a finite word equals its weighted coordinate sum. -/
theorem wordDirectionMap_time_eq_coordinate_sum (ω : Ω L W) {u : ℝ}
    (hu : 0 < u) (z : ℂ) (l : List (Bool × Z2 L)) :
    wordDirectionMap L W u ω z l
        ((1 / (2 * Real.sqrt u)) •
          (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm) =
      (1 / (2 * u)) • ∑ c : Coord L W,
        (ω c) • coordinateWordDeriv L W u ω c z l := by
  rw [time_direction_eq_coordinate_sum L W ω hu]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [← map_smul, wordDirectionMap_coordinate]

/-- The spectral part of a signed Green derivative, kept separate from matrix motion. -/
noncomputable def gsigSpectralFlowDeriv (ω : Ω L W) (E u : ℝ) (σ : Bool) :
    BlockMat L W :=
  let G := Gsig (HflowBlock L W u ω) (spectralZ E u) σ;
  -(G * (spectralMSign E σ • (1 : BlockMat L W)) * G)

/-- The flow derivative of one factor splits into matrix and spectral terms. -/
theorem gsigFlowDeriv_split (ω : Ω L W) (E u : ℝ) (σ : Bool) :
    gsigFlowDeriv L W ω E u σ =
      gsigDirectionMap L W u ω (spectralZ E u) σ
        ((1 / (2 * Real.sqrt u)) •
          (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm) +
      gsigSpectralFlowDeriv L W ω E u σ := by
  simp only [gsigFlowDeriv, gsigDirectionMap_apply, gsigSpectralFlowDeriv]
  noncomm_ring

/-- Recursive spectral drift of a finite signed word. -/
noncomputable def spectralWordDeriv (ω : Ω L W) (E u : ℝ) :
    List (Bool × Z2 L) → BlockMat L W
  | [] => 0
  | p :: l =>
      (gsigSpectralFlowDeriv L W ω E u p.1 * Eblk L W p.2) *
        l.foldr (fun q M => Gsig (HflowBlock L W u ω) (spectralZ E u) q.1 *
          Eblk L W q.2 * M) 1 +
      (Gsig (HflowBlock L W u ω) (spectralZ E u) p.1 * Eblk L W p.2) *
        spectralWordDeriv ω E u l

/-- The established fixed-sample word derivative splits into matrix and spectral parts. -/
theorem loopWordDeriv_split (ω : Ω L W) (E u : ℝ)
    (l : List (Bool × Z2 L)) :
    loopWordDeriv L W ω E u l =
      wordDirectionMap L W u ω (spectralZ E u) l
        ((1 / (2 * Real.sqrt u)) •
          (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm) +
      spectralWordDeriv L W ω E u l := by
  induction l with
  | nil => simp [loopWordDeriv, spectralWordDeriv]
  | cons p l ih =>
      simp only [loopWordDeriv, wordDirectionMap_cons, spectralWordDeriv,
        gsigFlowDeriv_split, ih]
      noncomm_ring

/-- The matrix-flow part of the loop derivative is the coordinate-weighted sum. -/
theorem trace_wordDirectionMap_time_eq_coordinate_sum (ω : Ω L W)
    {u : ℝ} (hu : 0 < u) (z : ℂ) (I : LoopIdx (Z2 L)) :
    Matrix.trace (wordDirectionMap L W u ω z (I.σ.zip I.a)
      ((1 / (2 * Real.sqrt u)) •
        (Xmat L W ω).submatrix (splitEquiv L W).symm (splitEquiv L W).symm)) =
      (1 / (2 * u)) • ∑ c : Coord L W,
        (ω c) • Matrix.trace
          (coordinateWordDeriv L W u ω c z (I.σ.zip I.a)) := by
  rw [wordDirectionMap_time_eq_coordinate_sum L W ω hu]
  simp only [Matrix.trace_smul, Matrix.trace_sum]

/-- The full fixed-sample loop derivative, with its spectral drift displayed separately. -/
theorem loop_flow_derivative_coordinate_chain (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun v : ℝ =>
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u =
      (1 / (2 * u)) • ∑ c : Coord L W,
        (ω c) • Matrix.trace
          (coordinateWordDeriv L W u ω c (spectralZ E u) (I.σ.zip I.a)) +
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) := by
  rw [(hasDerivAt_gloop_HflowBlock_spectralZ L W ω hE hu hu1 I hwf).deriv]
  rw [loopWordDeriv_split, Matrix.trace_add]
  rw [trace_wordDirectionMap_time_eq_coordinate_sum L W ω hu]

/-- The same identity with each actual Gaussian-coordinate derivative displayed. -/
theorem loop_flow_derivative_actual_coordinate_chain (ω : Ω L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) :
    deriv (fun v : ℝ =>
      gloop L W (HflowBlock L W v ω) (spectralZ E v) I) u =
      (1 / (2 * u)) • ∑ c : Coord L W,
        (ω c) • deriv (fun t : ℝ =>
          gloop L W (HflowBlock L W u (Function.update ω c t))
            (spectralZ E u) I) (ω c) +
      Matrix.trace (spectralWordDeriv L W ω E u (I.σ.zip I.a)) := by
  have hz : (spectralZ E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  have hcoord (c : Coord L W) :
      deriv (fun t : ℝ =>
        gloop L W (HflowBlock L W u (Function.update ω c t))
          (spectralZ E u) I) (ω c) =
        Matrix.trace
          (coordinateWordDeriv L W u ω c (spectralZ E u) (I.σ.zip I.a)) :=
    (hasDerivAt_gloop_update L W u ω c hz I hwf).deriv
  have h := loop_flow_derivative_coordinate_chain L W ω hE hu hu1 I hwf
  simpa only [← hcoord] using h

end RBM.Gauss
