/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Gauss.LoopCoordinateSecondDerivative
import RBM2D.Gauss.LoopEnvelope

/-!
# Sample-uniform bounds for coordinate derivatives of finite loops

The constants depend on the fixed coordinate direction, time, spectral gap,
and word length, but not on the Gaussian sample.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

variable (L W : ℕ) [NeZero L] [NeZero W]

private noncomputable def coordA (η : ℝ) : ℝ :=
  η⁻¹ * ((W : ℝ)⁻¹ ^ 2)

private noncomputable def coordD (u η : ℝ) (c : Coord L W) : ℝ :=
  (η⁻¹ * ‖Real.sqrt u • coordinateBlock L W c‖ * η⁻¹) *
    ((W : ℝ)⁻¹ ^ 2)

private noncomputable def coordS (u η : ℝ) (c : Coord L W) : ℝ :=
  2 * ((η⁻¹ * ‖Real.sqrt u • coordinateBlock L W c‖ * η⁻¹ *
      ‖Real.sqrt u • coordinateBlock L W c‖ * η⁻¹) *
    ((W : ℝ)⁻¹ ^ 2))

/-- Explicit finite-recursion majorant for the first derivative of a word. -/
noncomputable def coordinateFirstWordBound (u η : ℝ) (c : Coord L W) : ℕ → ℝ
  | 0 => 0
  | n + 1 => coordD L W u η c * (coordA W η) ^ n +
      coordA W η * coordinateFirstWordBound u η c n

/-- Explicit finite-recursion majorant for the second derivative of a word. -/
noncomputable def coordinateSecondWordBound (u η : ℝ) (c : Coord L W) : ℕ → ℝ
  | 0 => 0
  | n + 1 => coordS L W u η c * (coordA W η) ^ n +
      2 * coordD L W u η c * coordinateFirstWordBound L W u η c n +
      coordA W η * coordinateSecondWordBound u η c n

omit [NeZero W] in
private theorem coordA_nonneg {η : ℝ} (hη : 0 < η) :
    0 ≤ coordA W η := by unfold coordA; positivity

private theorem coordD_nonneg {η u : ℝ} (hη : 0 < η) (c : Coord L W) :
    0 ≤ coordD L W u η c := by unfold coordD; positivity

private theorem coordS_nonneg {η u : ℝ} (hη : 0 < η) (c : Coord L W) :
    0 ≤ coordS L W u η c := by unfold coordS; positivity

private theorem firstBound_nonneg {η u : ℝ} (hη : 0 < η) (c : Coord L W)
    (n : ℕ) : 0 ≤ coordinateFirstWordBound L W u η c n := by
  induction n with
  | zero => simp [coordinateFirstWordBound]
  | succ n ih =>
      rw [coordinateFirstWordBound]
      exact add_nonneg
        (mul_nonneg (coordD_nonneg L W hη c) (pow_nonneg (coordA_nonneg W hη) _))
        (mul_nonneg (coordA_nonneg W hη) ih)

private theorem secondBound_nonneg {η u : ℝ} (hη : 0 < η) (c : Coord L W)
    (n : ℕ) : 0 ≤ coordinateSecondWordBound L W u η c n := by
  induction n with
  | zero => simp [coordinateSecondWordBound]
  | succ n ih =>
      rw [coordinateSecondWordBound]
      exact add_nonneg
        (add_nonneg
          (mul_nonneg (coordS_nonneg L W hη c) (pow_nonneg (coordA_nonneg W hη) _))
          (mul_nonneg (mul_nonneg (by norm_num) (coordD_nonneg L W hη c))
            (firstBound_nonneg L W hη c n)))
        (mul_nonneg (coordA_nonneg W hη) ih)

private theorem norm_coordinate_head_le {η u : ℝ} (hη : 0 < η)
    (ω : Ω L W) (c : Coord L W) {z : ℂ} (hz : η ≤ |z.im|)
    (p : Bool × Z2 L) :
    ‖Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2‖ ≤ coordA W η ∧
    ‖gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2‖ ≤
      coordD L W u η c ∧
    ‖gsigCoordinateSecondDeriv L W u ω c z p.1 * Eblk L W p.2‖ ≤
      coordS L W u η c := by
  let G := Gsig (HflowBlock L W u ω) z p.1
  let B := Real.sqrt u • coordinateBlock L W c
  let E := Eblk L W p.2
  have hG : ‖G‖ ≤ η⁻¹ :=
    norm_Gsig_le_inv_eta L W (HflowBlock_isHermitian L W u ω) hη hz p.1
  have hE : ‖E‖ ≤ (W : ℝ)⁻¹ ^ 2 := norm_Eblk_le_inv_W_sq L W p.2
  have hq : 0 ≤ η⁻¹ := by positivity
  have he : 0 ≤ (W : ℝ)⁻¹ ^ 2 := by positivity
  constructor
  · calc
      ‖G * E‖ ≤ ‖G‖ * ‖E‖ := norm_mul_le _ _
      _ ≤ η⁻¹ * ((W : ℝ)⁻¹ ^ 2) := by gcongr
      _ = coordA W η := rfl
  constructor
  · change ‖-(G * B * G) * E‖ ≤ coordD L W u η c
    calc
      ‖-(G * B * G) * E‖ ≤ ‖-(G * B * G)‖ * ‖E‖ := norm_mul_le _ _
      _ = ‖G * B * G‖ * ‖E‖ := by rw [norm_neg]
      _ ≤ (‖G‖ * ‖B‖ * ‖G‖) * ‖E‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ (η⁻¹ * ‖B‖ * η⁻¹) * ((W : ℝ)⁻¹ ^ 2) := by gcongr
      _ = coordD L W u η c := rfl
  · change ‖((2 : ℝ) • (G * B * G * B * G)) * E‖ ≤ coordS L W u η c
    calc
      ‖((2 : ℝ) • (G * B * G * B * G)) * E‖
          ≤ ‖(2 : ℝ) • (G * B * G * B * G)‖ * ‖E‖ := norm_mul_le _ _
      _ = 2 * ‖G * B * G * B * G‖ * ‖E‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (‖G‖ * ‖B‖ * ‖G‖ * ‖B‖ * ‖G‖) * ‖E‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by
          gcongr
          exact (norm_mul_le _ _).trans (by
            gcongr
            exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)))
      _ ≤ 2 * (η⁻¹ * ‖B‖ * η⁻¹ * ‖B‖ * η⁻¹) *
            ((W : ℝ)⁻¹ ^ 2) := by gcongr
      _ = coordS L W u η c := by unfold coordS; ring

/-- Uniform first and second derivative bounds for every Gaussian sample. -/
theorem norm_coordinateWordDeriv_le {η u : ℝ} (hη : 0 < η)
    (c : Coord L W) {z : ℂ} (hz : η ≤ |z.im|)
    (l : List (Bool × Z2 L)) (ω : Ω L W) :
    ‖coordinateWordDeriv L W u ω c z l‖ ≤
        coordinateFirstWordBound L W u η c l.length ∧
    ‖coordinateSecondWordDeriv L W u ω c z l‖ ≤
        coordinateSecondWordBound L W u η c l.length := by
  induction l with
  | nil => simp [coordinateWordDeriv, coordinateSecondWordDeriv,
      coordinateFirstWordBound, coordinateSecondWordBound]
  | cons p l ih =>
      obtain ⟨hA, hD, hS⟩ := norm_coordinate_head_le L W (u := u) hη ω c hz p
      obtain ⟨hF, hT⟩ := ih
      have hword := norm_foldr_Gsig_Eblk_le L W
        (HflowBlock_isHermitian L W u ω) hη hz l
      have hword' :
          ‖l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ ≤
            coordA W η ^ l.length := by
        simpa only [coordA] using hword
      have hA0 := coordA_nonneg W hη
      have hD0 := coordD_nonneg L W (u := u) hη c
      have hS0 := coordS_nonneg L W (u := u) hη c
      have hF0 := firstBound_nonneg L W (u := u) hη c l.length
      have hT0 := secondBound_nonneg L W (u := u) hη c l.length
      have hp0 : 0 ≤ (coordA W η) ^ l.length := pow_nonneg hA0 _
      constructor
      · rw [coordinateWordDeriv, List.length_cons, coordinateFirstWordBound]
        calc
          ‖_ + _‖ ≤ ‖gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2 *
              l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ +
              ‖(Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
                coordinateWordDeriv L W u ω c z l‖ := norm_add_le _ _
          _ ≤ ‖gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2‖ *
                ‖l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ +
              ‖Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2‖ *
                ‖coordinateWordDeriv L W u ω c z l‖ :=
                  add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ coordD L W u η c * coordA W η ^ l.length +
              coordA W η * coordinateFirstWordBound L W u η c l.length := by gcongr
      · rw [coordinateSecondWordDeriv, List.length_cons, coordinateSecondWordBound]
        have hSterm :
            ‖gsigCoordinateSecondDeriv L W u ω c z p.1 * Eblk L W p.2 *
                l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ ≤
              coordS L W u η c * coordA W η ^ l.length := by
          calc
            _ ≤ ‖gsigCoordinateSecondDeriv L W u ω c z p.1 * Eblk L W p.2‖ *
                ‖l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ :=
                  norm_mul_le _ _
            _ ≤ _ := by gcongr
        have hDterm :
            ‖(gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
                coordinateWordDeriv L W u ω c z l‖ ≤
              coordD L W u η c * coordinateFirstWordBound L W u η c l.length := by
          calc
            _ ≤ ‖gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2‖ *
                ‖coordinateWordDeriv L W u ω c z l‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr
        have hAterm :
            ‖(Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
                coordinateSecondWordDeriv L W u ω c z l‖ ≤
              coordA W η * coordinateSecondWordBound L W u η c l.length := by
          calc
            _ ≤ ‖Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2‖ *
                ‖coordinateSecondWordDeriv L W u ω c z l‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr
        calc
          ‖(_ + _) + (_ + _)‖ ≤
              (‖gsigCoordinateSecondDeriv L W u ω c z p.1 * Eblk L W p.2 *
                  l.foldr (fun q M => Gsig (HflowBlock L W u ω) z q.1 * Eblk L W q.2 * M) 1‖ +
                ‖(gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
                  coordinateWordDeriv L W u ω c z l‖) +
              (‖(gsigCoordinateDeriv L W u ω c z p.1 * Eblk L W p.2) *
                  coordinateWordDeriv L W u ω c z l‖ +
                ‖(Gsig (HflowBlock L W u ω) z p.1 * Eblk L W p.2) *
                  coordinateSecondWordDeriv L W u ω c z l‖) := by
                    apply (norm_add_le _ _).trans
                    exact add_le_add (norm_add_le _ _) (norm_add_le _ _)
          _ ≤ (coordS L W u η c * coordA W η ^ l.length +
                coordD L W u η c * coordinateFirstWordBound L W u η c l.length) +
              (coordD L W u η c * coordinateFirstWordBound L W u η c l.length +
                coordA W η * coordinateSecondWordBound L W u η c l.length) := by
                  exact add_le_add (add_le_add hSterm hDterm)
                    (add_le_add hDterm hAterm)
          _ = coordS L W u η c * coordA W η ^ l.length +
              2 * coordD L W u η c * coordinateFirstWordBound L W u η c l.length +
              coordA W η * coordinateSecondWordBound L W u η c l.length := by ring

/-- A sample-independent envelope for the two derivatives of a traced loop. -/
theorem norm_gloop_coordinate_derivatives_le {η u : ℝ} (hη : 0 < η)
    (c : Coord L W) {z : ℂ} (hz : η ≤ |z.im|)
    (I : LoopIdx (Z2 L)) (hwf : I.WF) (ω : Ω L W) :
    ‖Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) *
          coordinateFirstWordBound L W u η c I.a.length ∧
    ‖Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ 2 : ℕ) : ℝ) *
          coordinateSecondWordBound L W u η c I.a.length := by
  obtain ⟨hF, hS⟩ := norm_coordinateWordDeriv_le L W hη c hz (I.σ.zip I.a) ω
  have hlen : (I.σ.zip I.a).length = I.a.length := by
    rw [List.length_zip]
    simp only [LoopIdx.WF] at hwf
    rw [hwf, min_self]
  constructor
  · calc
      ‖Matrix.trace (coordinateWordDeriv L W u ω c z (I.σ.zip I.a))‖ ≤
          (Fintype.card (BlockIndex L W) : ℝ) *
            ‖coordinateWordDeriv L W u ω c z (I.σ.zip I.a)‖ :=
              norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          coordinateFirstWordBound L W u η c (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]
  · calc
      ‖Matrix.trace (coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a))‖ ≤
          (Fintype.card (BlockIndex L W) : ℝ) *
            ‖coordinateSecondWordDeriv L W u ω c z (I.σ.zip I.a)‖ :=
              norm_matrix_trace_le_card_mul _
      _ ≤ (Fintype.card (BlockIndex L W) : ℝ) *
          coordinateSecondWordBound L W u η c (I.σ.zip I.a).length := by
            exact mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = _ := by rw [card_BlockIndex, hlen]

end RBM.Gauss
