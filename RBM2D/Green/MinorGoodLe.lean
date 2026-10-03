/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucIterHigh

/-!
# The level-budgeted minor good event: `MinorGoodLe`

The paper (arXiv:2503.07606) has the event `Ω(t, c) = {‖G_t - m‖_max ≤ W^{-c}}` (`def_asGMc`),
and states the entry estimates for the full matrix `G_t`
only: the TeX has no minor `G^{(S)}`, and the proofs are deferred to "Lemma 4.2 in [YY_25], which
is dimension-independent".  In this file, as in `RBM2D/Green/EntryCore.lean`,
(4.1) is that event, `‖G - m‖_max ≤ Ψ` (`GoodEvent`), and (4.9) is the minor formula of
`RBM2D/Green/Minor.lean` (the numbering of [YY_25]).

## Why this file exists

The full-matrix good event (4.1) is a statement at level `S = ∅`.  The `2p`-th moment expansion
needs the four estimates on the minors `G^{(S)}` at the levels it reaches, which are bounded by
the word length: `|S| ≤ M`.  Iterating (4.9)
degrades the threshold at every level (`Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`, see below), so the bound is
proved with a level budget `M`, and `MinorGoodLe` carries it.

## The logical shape

`minorGoodLe_of_goodEvent` is a **pointwise implication**, not a hypothesis: at one fixed sample
point `ω`, *if* the full-matrix good event (4.1) holds at `ω` with threshold `Ψ`, *then* the
level-budgeted estimates hold at the same `ω` with threshold `2Ψ`.  Nothing is assumed for all
`ω`: the produced event contains the event (4.1) in the sense that (4.1) at `ω` implies it at `ω`.

## What is proved

* `isUnit_det_Hflow_submatrix_sub` — **invertibility of every minor is free**: it is
  `isUnit_sub_smul_one_of_im_ne_zero` applied to the (Hermitian) submatrix of `H_u`; it needs
  neither a good event nor a level restriction.
* `gEnt_insert_of_ne` — (4.9) at a general level, with the two hypotheses it really needs (`hdet`
  at level `S`, and `G^{(S)}_{κκ} ≠ 0`).  At the inductive step the good event is available at
  level `S` only, not at all levels.
* `gEnt_empty` — level `0` is the full resolvent.
* `norm_gEnt_le_of_goodEvent` — the simultaneous induction on the level.
* `MinorGoodLe`, `MinorGoodLe.gEnt_insert`, `minorGoodLe_of_goodEvent`,
  `minorGoodLe_of_goodEvent_flow`.

## The induction, and the constants it needs

Level `0` is exactly (4.1): `GoodEvent.norm_offdiag_le` and `GoodEvent.norm_diag_sub_le` are
`off_le` and `diag_sub_le` at `S = ∅`, via `greenSetMat_empty_apply`.  One level of (4.9),

  `G^{(S ∪ {κ})}_{ab} = G^{(S)}_{ab} - G^{(S)}_{aκ} G^{(S)}_{κb} (G^{(S)}_{κκ})⁻¹`,

costs `2 Ψ_j²` on both the off-diagonal and the centered diagonal entries (the `2` is the bound
on `|G^{(S)}_{κκ}|⁻¹`, which travels with the induction).  So the recursion is
`Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`.  The invariant that closes it is

  `Ψ_j ≤ Ψ + 8 j Ψ²` for `j ≤ M`,

which needs exactly `8 M Ψ ≤ 1` (then `8 j Ψ² ≤ Ψ`, hence `Ψ_j ≤ 2Ψ`, hence the step costs
`2 Ψ_j² ≤ 8 Ψ²`, which is the increment of the invariant).  The separate hypothesis `Ψ ≤ 1/4`
gives `|G^{(S)}_{aa}| ≥ 1 - 2Ψ ≥ 1/2` from `|m| = 1` (used for `diag_ne`, `inv_le` and, inside the
induction, for the bound `2` on the inverse); it follows from `8 M Ψ ≤ 1` as soon as `M ≥ 1`.  In
the use for the `2p`-th moment expansion, `M = K = 2p` is fixed and `Ψ → 0`, so `8 M Ψ ≤ 1`
holds eventually.

## d = 2

The statements depend on the dimension only through the index type `Idx (d.L n) (d.W n)`; the
constants (`2` per `Q`, `2` per difference, the budget `8 M Ψ ≤ 1`, the threshold `2Ψ`) do not
depend on `d`.  The flow is `Sizes.seqHflow d n u ω`, with `spectralZ`, `spectralM`,
`norm_spectralM`, and `GoodEvent` is `RBM.Green.GoodEvent` (`RBM2D/Green/EntryCore.lean`).
The invertibility of the determinant follows from `isUnit_sub_smul_one_of_im_ne_zero` and
`Matrix.isUnit_iff_isUnit_det`.

The iteration to `|S| ≤ M`, the budget `M` and the constants `Ψ ≤ 1/4`, `8 M Ψ ≤ 1`, `Ψ ↦ 2Ψ`
are an addition of the formalization (the paper has only the full-matrix estimates).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

variable {d : Sizes} {n : ℕ} {u : ℝ} {z m : ℂ} {ω : Sizes.SeqΩ d} {Ψ : ℝ} {M : ℕ}
variable {a b κ : Idx (d.L n) (d.W n)} {S : Finset (Idx (d.L n) (d.W n))}

/-! ### Invertibility of the minors is unconditional -/

/-- **Every minor of `H_u - z` is invertible**, for every sample point and every level, as soon
as `z` is off the real axis. -/
theorem isUnit_det_Hflow_submatrix_sub (d : Sizes) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d)
    (hz : z.im ≠ 0) (S : Finset (Idx (d.L n) (d.W n))) :
    IsUnit ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ S} → Idx (d.L n) (d.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ S}
        {x : Idx (d.L n) (d.W n) // x ∉ S} ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_sub_smul_one_of_im_ne_zero ((Sizes.seqHflow_isHermitian d n u ω).submatrix Subtype.val)
      hz)

/-! ### (4.9) with the hypotheses it actually needs -/

/-- **(4.9) for the extended entries**, assuming only what one level of the identity uses: the
`S`-minor is invertible and its `κκ` entry does not vanish.  `MinorGoodLe.gEnt_insert` is the
same identity packaged behind `MinorGoodLe`, which asserts both inside the budget; the induction
of `norm_gEnt_le_of_goodEvent` has them at level `S` only. -/
theorem gEnt_insert_of_ne
    (hdet : IsUnit ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ S} → Idx (d.L n) (d.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ S}
        {x : Idx (d.L n) (d.W n) // x ∉ S} ℂ)).det)
    (hκ : κ ∉ S) (hne : gEnt d n u z ω κ κ S ≠ 0)
    (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt d n u z ω a b (insert κ S)
      = gEnt d n u z ω a b S - gEnt d n u z ω a κ S * gEnt d n u z ω κ b S
          * (gEnt d n u z ω κ κ S)⁻¹ := by
  have ha' : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
  have hb' : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
  have hne' : greenSetMat d n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0 := by
    rwa [gEnt_apply hκ hκ] at hne
  rw [gEnt_apply ha hb, gEnt_apply ha' hb', gEnt_apply ha' hκ, gEnt_apply hκ hb',
    gEnt_apply hκ hκ,
    greenSetMat_insert_apply d n u z S ω hκ hdet hne' ha hb, div_eq_mul_inv, mul_assoc]

/-! ### Level `0` is the full-matrix good event -/

/-- At `S = ∅` the extended entry is the full resolvent entry. -/
theorem gEnt_empty (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ d)
    (a b : Idx (d.L n) (d.W n)) :
    gEnt d n u z ω a b ∅ = green (Sizes.seqHflow d n u ω) z a b := by
  rw [gEnt_apply (Finset.notMem_empty a) (Finset.notMem_empty b),
    greenSetMat_empty_apply d n u z ω ⟨a, Finset.notMem_empty a⟩ ⟨b, Finset.notMem_empty b⟩]

/-! ### The simultaneous induction on the level -/

/-- **The recursion `Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`, solved**: at every level `S` with
`S.card ≤ M`, the off-diagonal entries and the centered diagonal entries of `G^{(S)}` are at
most `Ψ + 8 |S| Ψ²`.

The two estimates cannot be separated, because the step of (4.9) multiplies by
`(G^{(S)}_{κκ})⁻¹`, whose bound comes from the diagonal estimate at level `S`, while the
diagonal estimate at level `S ∪ {κ}` needs the off-diagonal estimate at level `S`. -/
theorem norm_gEnt_le_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow d n u ω) z) m Ψ) :
    ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M →
      (∀ a b : Idx (d.L n) (d.W n), a ≠ b →
        ‖gEnt d n u z ω a b S‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) ∧
      (∀ a : Idx (d.L n) (d.W n), a ∉ S →
        ‖gEnt d n u z ω a a S - m‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨fun a b hab => ?_, fun a _ => ?_⟩
      · rw [gEnt_empty]
        simpa using hG.norm_offdiag_le hab
      · rw [gEnt_empty]
        simpa using hG.norm_diag_sub_le a
  | insert κ s hκs ih =>
      intro hcard
      have hscard : s.card ≤ M := by
        rw [Finset.card_insert_of_notMem hκs] at hcard; omega
      obtain ⟨ihoff, ihdiag⟩ := ih hscard
      -- the bound at level `s`
      set B : ℝ := Ψ + 8 * (s.card : ℝ) * Ψ ^ 2 with hB
      have hjM : (s.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hscard
      have h8j : 8 * (s.card : ℝ) * Ψ ≤ 1 := by nlinarith
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      have hB2 : B ≤ 2 * Ψ := by rw [hB]; nlinarith
      -- `|G^{(s)}_{aa}| ≥ 1/2`, hence the bound `2` on the inverse
      have hhalf : ∀ x : Idx (d.L n) (d.W n), x ∉ s → 1 / 2 ≤ ‖gEnt d n u z ω x x s‖ := by
        intro x hx
        have h1 := ihdiag x hx
        have h2 : ‖m‖ - ‖gEnt d n u z ω x x s‖ ≤ ‖m - gEnt d n u z ω x x s‖ :=
          norm_sub_norm_le _ _
        rw [norm_sub_rev, hm] at h2
        linarith
      have hκ0 : gEnt d n u z ω κ κ s ≠ 0 := by
        intro h0
        have := hhalf κ hκs
        rw [h0, norm_zero] at this
        norm_num at this
      have hinv : ‖(gEnt d n u z ω κ κ s)⁻¹‖ ≤ 2 := by
        have h := hhalf κ hκs
        rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      -- the arithmetic of one step: `B + 2 B² ≤ Ψ + 8 (|s| + 1) Ψ²`
      have hstep : B + B * B * 2 ≤ Ψ + 8 * ((s.card : ℝ) + 1) * Ψ ^ 2 := by
        rw [hB]; nlinarith [hB0, hB2]
      have hcast : ((insert κ s).card : ℝ) = (s.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hκs]; push_cast; ring
      rw [hcast]
      refine ⟨fun a b hab => ?_, fun a ha => ?_⟩
      · by_cases ha : a ∈ insert κ s
        · rw [gEnt_eq_zero_left ha, norm_zero]
          nlinarith
        by_cases hb : b ∈ insert κ s
        · rw [gEnt_eq_zero_right hb, norm_zero]
          nlinarith
        have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have hbκ : b ≠ κ := fun h => hb (by rw [h]; exact Finset.mem_insert_self κ s)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub d n u ω hz s) hκs hκ0 ha hb]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihoff a b hab
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ b (Ne.symm hbκ)
          have n2 := norm_nonneg (gEnt d n u z ω κ b s)
          have n3 := norm_nonneg ((gEnt d n u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)
      · have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have ha' : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub d n u ω hz s) hκs hκ0 ha ha]
        have hre : gEnt d n u z ω a a s
              - gEnt d n u z ω a κ s * gEnt d n u z ω κ a s * (gEnt d n u z ω κ κ s)⁻¹ - m
            = (gEnt d n u z ω a a s - m)
              - gEnt d n u z ω a κ s * gEnt d n u z ω κ a s * (gEnt d n u z ω κ κ s)⁻¹ := by
          ring
        rw [hre]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihdiag a ha'
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ a (Ne.symm haκ)
          have n2 := norm_nonneg (gEnt d n u z ω κ a s)
          have n3 := norm_nonneg ((gEnt d n u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)

/-! ### The level-budgeted good event -/

/-- **The local law on the good event, at every minor level of size at most `M`.**

The budget is what makes it *producible*: `minorGoodLe_of_goodEvent` derives it, at one fixed
sample point, from the full-matrix good event (4.1) alone.

`det` needs neither the budget nor the good event (`isUnit_det_Hflow_submatrix_sub`), so it is
stated at every level. -/
structure MinorGoodLe (d : Sizes) (n : ℕ) (u : ℝ) (z m : ℂ) (ω : Sizes.SeqΩ d) (Ψ : ℝ) (M : ℕ)
    : Prop where
  /-- Every minor of `H_u - z` is invertible -- unconditional, and at *every* level. -/
  det : ∀ S : Finset (Idx (d.L n) (d.W n)), IsUnit ((Sizes.seqHflow d n u ω).submatrix
      (Subtype.val : {x : Idx (d.L n) (d.W n) // x ∉ S} → Idx (d.L n) (d.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx (d.L n) (d.W n) // x ∉ S}
        {x : Idx (d.L n) (d.W n) // x ∉ S} ℂ)).det
  /-- The diagonal entries of the budgeted minors are non-zero. -/
  diag_ne : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a : Idx (d.L n) (d.W n),
    a ∉ S → gEnt d n u z ω a a S ≠ 0
  /-- `|G^{(S)}_{aa}|⁻¹ ≤ 2` for `|S| ≤ M` -- the quantitative form of (4.1). -/
  inv_le : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a : Idx (d.L n) (d.W n),
    ‖(gEnt d n u z ω a a S)⁻¹‖ ≤ 2
  /-- `|G^{(S)}_{ab}| ≤ Ψ` for `a ≠ b` and `|S| ≤ M` -- (4.2). -/
  off_le : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a b : Idx (d.L n) (d.W n),
    a ≠ b → ‖gEnt d n u z ω a b S‖ ≤ Ψ
  /-- `|G^{(S)}_{aa} - m| ≤ Ψ` for `|S| ≤ M` -- (4.3). -/
  diag_sub_le : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a : Idx (d.L n) (d.W n),
    a ∉ S → ‖gEnt d n u z ω a a S - m‖ ≤ Ψ

/-- **(4.9) inside the budget.**  The identity is available at `S ∪ {κ}` as soon as `S` itself
is within the budget; the estimate of the right-hand side then uses the fields at level `S`. -/
theorem MinorGoodLe.gEnt_insert (hg : MinorGoodLe d n u z m ω Ψ M) (hS : S.card ≤ M)
    (hκ : κ ∉ S) (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt d n u z ω a b (insert κ S)
      = gEnt d n u z ω a b S - gEnt d n u z ω a κ S * gEnt d n u z ω κ b S
          * (gEnt d n u z ω κ κ S)⁻¹ :=
  gEnt_insert_of_ne (hg.det S) hκ (hg.diag_ne S hS κ hκ) ha hb

/-- **The level-budgeted good event follows from (4.1) at the same sample point**, with the
threshold degraded from `Ψ` to `2Ψ`.

This is a pointwise implication: `ω` occurs only as the point at which the hypothesis and the
conclusion are both read.  Nothing is assumed for all `ω`. -/
theorem minorGoodLe_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow d n u ω) z) m Ψ) :
    MinorGoodLe d n u z m ω (2 * Ψ) M := by
  classical
  have key := norm_gEnt_le_of_goodEvent hz hm hΨ0 hΨ4 hMΨ hG
  -- the invariant collapses to `2Ψ` inside the budget
  have hle : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M →
      Ψ + 8 * (S.card : ℝ) * Ψ ^ 2 ≤ 2 * Ψ := by
    intro S hS
    have hjM : ((S.card : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hS
    nlinarith
  have hdiag : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a : Idx (d.L n) (d.W n),
      a ∉ S → ‖gEnt d n u z ω a a S - m‖ ≤ 2 * Ψ :=
    fun S hS a ha => le_trans ((key S hS).2 a ha) (hle S hS)
  have hhalf : ∀ S : Finset (Idx (d.L n) (d.W n)), S.card ≤ M → ∀ a : Idx (d.L n) (d.W n),
      a ∉ S → 1 / 2 ≤ ‖gEnt d n u z ω a a S‖ := by
    intro S hS a ha
    have h1 := hdiag S hS a ha
    have h2 : ‖m‖ - ‖gEnt d n u z ω a a S‖ ≤ ‖m - gEnt d n u z ω a a S‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, hm] at h2
    linarith
  refine
    { det := isUnit_det_Hflow_submatrix_sub d n u ω hz
      diag_ne := ?_
      inv_le := ?_
      off_le := fun S hS a b hab => le_trans ((key S hS).1 a b hab) (hle S hS)
      diag_sub_le := hdiag }
  · intro S hS a ha h0
    have := hhalf S hS a ha
    rw [h0, norm_zero] at this
    norm_num at this
  · intro S hS a
    by_cases ha : a ∉ S
    · have h := hhalf S hS a ha
      rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    · rw [gEnt_eq_zero_left (not_not.1 ha), _root_.inv_zero, norm_zero]
      norm_num

/-- The shape in which the flow consumes it: `z = z_u`, `m = m_E`, where `|m_E| = 1` is
`norm_spectralM`. -/
theorem minorGoodLe_of_goodEvent_flow {E : ℝ} (hE : |E| ≤ 2) (hz : (spectralZ E u).im ≠ 0)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow d n u ω) (spectralZ E u)) (spectralM E) Ψ) :
    MinorGoodLe d n u (spectralZ E u) (spectralM E) ω (2 * Ψ) M :=
  minorGoodLe_of_goodEvent hz (norm_spectralM hE) hΨ0 hΨ4 hMΨ hG

end RBM.Green
