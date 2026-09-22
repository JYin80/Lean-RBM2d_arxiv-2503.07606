/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.NormalizedCutoffSeparatedShellSum
import RBM2D.Propagator.Shells

/-!
# Support of separated-shell cutoff differences

A nonzero three-point cutoff difference has at least one sample in the
actual physical annulus. Thus its starting point lies in three translates
of that annulus. The same statement is valid in the separated-shell regime;
fold defects are not discarded.
-/

namespace RBM

/-- The closed physical annulus containing the support of the normalized
dyadic cutoff at shell `j`. -/
noncomputable def dyadicPhysicalAnnulus (L : ℕ) [NeZero L]
    (j : ℕ) : Finset (Z2 L) := by
  classical
  exact Finset.univ.filter (fun p =>
    (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
      pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2)

theorem mem_dyadicPhysicalAnnulus_iff (L : ℕ) [NeZero L]
    (j : ℕ) (p : Z2 L) :
    p ∈ dyadicPhysicalAnnulus L j ↔
      (physicalShellRadius (j + 1)) ^ 2 ≤ pstar2 L p ∧
        pstar2 L p ≤ (2 * physicalShellRadius j) ^ 2 := by
  classical
  simp [dyadicPhysicalAnnulus]

/-- A nonzero cutoff weight lies in the actual physical annulus. -/
theorem normalizedDyadicCutoff_mem_dyadicPhysicalAnnulus
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (hcut : normalizedDyadicCutoff L j p ≠ 0) :
    p ∈ dyadicPhysicalAnnulus L j :=
  (mem_dyadicPhysicalAnnulus_iff L j p).2
    (normalizedDyadicCutoff_physical_support_sq L j p hcut)

/-- A nonzero three-point difference has at least one sampled momentum in
the physical annulus. -/
theorem cutoff_second_diff_has_annulus_sample
    (L : ℕ) [NeZero L] (j : ℕ) (p q r : Z2 L)
    (hsecond : normalizedDyadicCutoff L j r -
        2 * normalizedDyadicCutoff L j q +
        normalizedDyadicCutoff L j p ≠ 0) :
    p ∈ dyadicPhysicalAnnulus L j ∨
      q ∈ dyadicPhysicalAnnulus L j ∨
      r ∈ dyadicPhysicalAnnulus L j := by
  by_cases hp : normalizedDyadicCutoff L j p = 0
  · by_cases hq : normalizedDyadicCutoff L j q = 0
    · have hr : normalizedDyadicCutoff L j r ≠ 0 := by
        intro hzero
        simp [hp, hq, hzero] at hsecond
      exact Or.inr (Or.inr
        (normalizedDyadicCutoff_mem_dyadicPhysicalAnnulus L j r hr))
    · exact Or.inr (Or.inl
        (normalizedDyadicCutoff_mem_dyadicPhysicalAnnulus L j q hq))
  · exact Or.inl
      (normalizedDyadicCutoff_mem_dyadicPhysicalAnnulus L j p hp)

/-- Every starting momentum of a nonzero two-step difference lies in one
of three translated physical annuli. -/
theorem lowGridTwoStepStarts_subset_annulus_translates
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L) :
    lowGridTwoStepStarts L j e ⊆
      (dyadicPhysicalAnnulus L j ∪
        (dyadicPhysicalAnnulus L j).image (fun x => x - e)) ∪
          (dyadicPhysicalAnnulus L j).image (fun x => x - e - e) := by
  classical
  intro p hp
  have hsecond : normalizedDyadicCutoff L j (p + e + e) -
      2 * normalizedDyadicCutoff L j (p + e) +
      normalizedDyadicCutoff L j p ≠ 0 :=
    (Finset.mem_filter.mp hp).2
  rcases cutoff_second_diff_has_annulus_sample L j p
      (p + e) (p + e + e) hsecond with h₀ | h₁ | h₂
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl h₀)))
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨p + e, h₁, ?_⟩
    simp
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨p + e + e, h₂, ?_⟩
    simp

/-- The nonzero starting set has at most three times as many points as its
physical annulus. This is a finite count with no artificial lower-radius
assumption. -/
theorem card_lowGridTwoStepStarts_le_three_annulus
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L) :
    (lowGridTwoStepStarts L j e).card ≤
      3 * (dyadicPhysicalAnnulus L j).card := by
  classical
  let B := dyadicPhysicalAnnulus L j
  have hsubset := lowGridTwoStepStarts_subset_annulus_translates L j e
  have h₁ : (B.image (fun x : Z2 L => x - e)).card ≤ B.card :=
    Finset.card_image_le
  have h₂ : (B.image (fun x : Z2 L => x - e - e)).card ≤ B.card :=
    Finset.card_image_le
  calc
    (lowGridTwoStepStarts L j e).card ≤
        ((B ∪ B.image (fun x : Z2 L => x - e)) ∪
          B.image (fun x : Z2 L => x - e - e)).card :=
      Finset.card_le_card hsubset
    _ ≤ B.card + (B.image (fun x : Z2 L => x - e)).card +
        (B.image (fun x : Z2 L => x - e - e)).card := by
      have ha := Finset.card_union_le B (B.image (fun x : Z2 L => x - e))
      have hb := Finset.card_union_le
        (B ∪ B.image (fun x : Z2 L => x - e))
        (B.image (fun x : Z2 L => x - e - e))
      omega
    _ ≤ 3 * B.card := by omega

/-- A natural-number outer radius for the physical shell, measured in cyclic
lattice steps. -/
noncomputable def dyadicOuterGridRadius (L j : ℕ) : ℕ :=
  Nat.ceil (2 * (L : ℝ) * dyad j)

private theorem annulus_normalizedFrequency_le_outer
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (hp : p ∈ dyadicPhysicalAnnulus L j) :
    normalizedFrequency L p ≤ 2 * dyad j := by
  have hsq := ((mem_dyadicPhysicalAnnulus_iff L j p).1 hp).2
  have hr : 0 ≤ 2 * physicalShellRadius j := by
    have := physicalShellRadius_pos j
    positivity
  have hsqrt : Real.sqrt (pstar2 L p) ≤ 2 * physicalShellRadius j := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hr).mp
    simpa only [Real.sq_sqrt (pstar2_nonneg L p)] using hsq
  unfold normalizedFrequency
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  convert hsqrt using 1
  unfold physicalShellRadius
  ring

/-- Both cyclic coordinate distances of an annulus point are bounded by the
explicit ceiling of the physical outer radius in lattice steps. -/
theorem dyadicPhysicalAnnulus_zdist_le_outerGridRadius
    (L : ℕ) [NeZero L] (j : ℕ) (p : Z2 L)
    (hp : p ∈ dyadicPhysicalAnnulus L j) :
    zdist L p.1 ≤ dyadicOuterGridRadius L j ∧
      zdist L p.2 ≤ dyadicOuterGridRadius L j := by
  have hν := annulus_normalizedFrequency_le_outer L j p hp
  have hL : 0 < (L : ℝ) := cast_L_pos L
  have hceil : 2 * (L : ℝ) * dyad j ≤
      (dyadicOuterGridRadius L j : ℝ) := by
    exact Nat.le_ceil _
  constructor
  · have hc := zdist_coord_div_le_normalizedFrequency L p 0
    have hm := (div_le_iff₀ hL).mp (hc.trans hν)
    have hm' : (zdist L p.1 : ℝ) ≤
        2 * (L : ℝ) * dyad j := by
      have hm₁ : (zdist L p.1 : ℝ) ≤
          2 * dyad j * (L : ℝ) := by simpa using hm
      nlinarith
    exact_mod_cast hm'.trans hceil
  · have hc := zdist_coord_div_le_normalizedFrequency L p 1
    have hm := (div_le_iff₀ hL).mp (hc.trans hν)
    have hm' : (zdist L p.2 : ℝ) ≤
        2 * (L : ℝ) * dyad j := by
      have hm₂ : (zdist L p.2 : ℝ) ≤
          2 * dyad j * (L : ℝ) := by simpa using hm
      nlinarith
    exact_mod_cast hm'.trans hceil

/-- Existing cyclic-ball counting gives an explicit finite bound for the
physical annulus, with the natural dyadic outer radius. -/
theorem card_dyadicPhysicalAnnulus_le_outerGridRadius
    (L : ℕ) [NeZero L] (j : ℕ) :
    (dyadicPhysicalAnnulus L j).card ≤
      (2 * dyadicOuterGridRadius L j + 1) ^ 2 := by
  classical
  let R := dyadicOuterGridRadius L j
  let B : Finset (ZMod L) := Finset.univ.filter (fun u => zdist L u ≤ R)
  have hsubset : dyadicPhysicalAnnulus L j ⊆ B ×ˢ B := by
    intro p hp
    obtain ⟨h₁, h₂⟩ :=
      dyadicPhysicalAnnulus_zdist_le_outerGridRadius L j p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h₁⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h₂⟩⟩
  have hB : B.card ≤ 2 * R + 1 := card_filter_zdist_le_le L R
  calc
    (dyadicPhysicalAnnulus L j).card ≤ (B ×ˢ B).card :=
      Finset.card_le_card hsubset
    _ = B.card ^ 2 := by rw [Finset.card_product]; ring
    _ ≤ (2 * R + 1) ^ 2 := by gcongr

/-- The nonzero second-difference starting set has at most three times the
outer lattice-ball count. The bound scales like `(L·2⁻ʲ)²` and is not yet a
sharp Fourier multiplier estimate. -/
theorem card_lowGridTwoStepStarts_le_outerGridRadius
    (L : ℕ) [NeZero L] (j : ℕ) (e : Z2 L) :
    (lowGridTwoStepStarts L j e).card ≤
      3 * (2 * dyadicOuterGridRadius L j + 1) ^ 2 := by
  calc
    _ ≤ 3 * (dyadicPhysicalAnnulus L j).card :=
      card_lowGridTwoStepStarts_le_three_annulus L j e
    _ ≤ 3 * (2 * dyadicOuterGridRadius L j + 1) ^ 2 := by
      exact Nat.mul_le_mul_left 3
        (card_dyadicPhysicalAnnulus_le_outerGridRadius L j)

/-- A small-lattice numerical radius and support-count probe. -/
example : dyadicOuterGridRadius 6 2 = 3 ∧
    (lowGridTwoStepStarts 6 2 ((1, 0) : Z2 6)).card ≤ 147 := by
  have hR : dyadicOuterGridRadius 6 2 = 3 := by
    norm_num [dyadicOuterGridRadius, dyad]
  refine ⟨hR, ?_⟩
  have h := card_lowGridTwoStepStarts_le_outerGridRadius
    6 2 ((1, 0) : Z2 6)
  simpa [hR] using h

end RBM

#print axioms RBM.normalizedDyadicCutoff_mem_dyadicPhysicalAnnulus
#print axioms RBM.cutoff_second_diff_has_annulus_sample
#print axioms RBM.lowGridTwoStepStarts_subset_annulus_translates
#print axioms RBM.card_lowGridTwoStepStarts_le_three_annulus
#print axioms RBM.dyadicPhysicalAnnulus_zdist_le_outerGridRadius
#print axioms RBM.card_dyadicPhysicalAnnulus_le_outerGridRadius
#print axioms RBM.card_lowGridTwoStepStarts_le_outerGridRadius
